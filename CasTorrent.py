
import warnings
warnings.filterwarnings("ignore", category=DeprecationWarning)

import libtorrent as lt
import tkinter as tk
from tkinter import ttk, filedialog, messagebox, scrolledtext
import threading
import time
import os
import json
from datetime import datetime
from pathlib import Path
import webbrowser
import logging
import sys
import requests
from collections import deque
import psutil
import csv
import shutil

logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger("TorrentClient")

def platform_downloads_dir() -> Path:
	home = Path.home()
	downloads = home / "Downloads"
	try:
		downloads.mkdir(parents=True, exist_ok=True)
	except Exception:
		return home
	return downloads

def lt_has(obj, name):
	try:
		return hasattr(obj, name)
	except Exception:
		return False

def session_set_download_rate_limit(session, value):
	try:
		if lt_has(session, 'set_download_rate_limit'):
			session.set_download_rate_limit(int(value))
	except Exception:
		pass

def session_set_upload_rate_limit(session, value):
	try:
		if lt_has(session, 'set_upload_rate_limit'):
			session.set_upload_rate_limit(int(value))
	except Exception:
		pass

def session_set_max_connections(session, value):
	try:
		if lt_has(session, 'set_max_connections'):
			session.set_max_connections(int(value))
	except Exception:
		pass

def session_set_max_uploads(session, value):
	try:
		if lt_has(session, 'set_max_uploads'):
			session.set_max_uploads(int(value))
	except Exception:
		pass

def session_enable_feature(session, feature_name, enable):
	try:
		if feature_name == 'dht':
			if enable and lt_has(session, 'start_dht'):
				session.start_dht()
			elif not enable and lt_has(session, 'stop_dht'):
				session.stop_dht()
	except Exception:
		pass

def session_listen_on(session, start_port, end_port):
	try:
		session.listen_on(int(start_port), int(end_port))
		return True
	except Exception:
		return False

def safe_add_dht_routers(session):
	try:
		if lt_has(session, 'add_dht_router'):
			session.add_dht_router('router.bittorrent.com', 6881)
			session.add_dht_router('dht.transmissionbt.com', 6881)
			session.add_dht_router('dht.libtorrent.org', 6881)
	except Exception:
		pass

def save_session_state_safe(session, path="session_state"):
	try:
		state = session.save_state()
		data = None
		try:
			data = lt.bencode(state)
		except Exception:
			if isinstance(state, (bytes, bytearray)):
				data = bytes(state)
		if data is not None:
			with open(path, "wb") as f:
				f.write(data)
			logger.info("Session state saved")
	except Exception as e:
		logger.warning(f"Error saving session state: {e}")

def load_session_state_safe(session, path="session_state"):
	try:
		p = Path(path)
		if not p.exists():
			return
		raw = p.read_bytes()
		state = None
		try:
			state = lt.bdecode(raw)
		except Exception:
			try:
				state = json.loads(raw.decode("utf-8"))
			except Exception:
				state = None
		if state is not None:
			session.load_state(state)
			logger.info("Loaded previous session state")
	except Exception as e:
		logger.warning(f"Error loading session state: {e}")

def safe_info_hash_str(handle):
	try:
		ihs = handle.info_hashes()  # lt 2.x
		if hasattr(ihs, "v1") and ihs.v1:
			return ihs.v1.to_string()
		if hasattr(ihs, "v2") and ihs.v2:
			return ihs.v2.to_string()
	except Exception:
		pass
	try:
		return handle.info_hash().to_string()  # lt 1.x
	except Exception:
		pass
	try:
		return str(handle.info_hash())
	except Exception:
		return ""

def open_path_in_os(path: Path):
	if sys.platform == 'win32':
		os.startfile(str(path))
	elif sys.platform == 'darwin':
		os.system(f'open "{path}"')
	else:
		os.system(f'xdg-open "{path}"')

FILE_PRIORITY_SKIP = 0
FILE_PRIORITY_LOW = 1
FILE_PRIORITY_TWO = 2
FILE_PRIORITY_THREE = 3
FILE_PRIORITY_FOUR = 4
FILE_PRIORITY_FIVE = 5
FILE_PRIORITY_SIX = 6
FILE_PRIORITY_MAX = 7
FILE_PRIORITY_NORMAL = FILE_PRIORITY_FOUR

class TorrentClient:
	def __init__(self):
		self.config = self.load_config()
		self.session = lt.session()
		self.apply_initial_session_settings()

		self.torrents = {}  # hash -> {'handle','added_time','source','save_path','moved'}
		self.download_history = deque(maxlen=3000)

		self.performance_stats = {
			'download_speeds': deque(maxlen=600),
			'upload_speeds': deque(maxlen=600),
			'memory_usage': deque(maxlen=600),
			'cpu_usage': deque(maxlen=600),
		}

		# Live status rendering (single-line per torrent, refreshed)
		self._last_live_status_render = 0

		self.root = tk.Tk()
		self.setup_gui()

		self.running = True
		self.update_thread = threading.Thread(target=self.update_torrents_loop, daemon=True)
		self.update_thread.start()

	def apply_initial_session_settings(self):
		session_set_max_connections(self.session, self.config.get('max_connections', 500))
		session_set_max_uploads(self.session, self.config.get('max_uploads', 50))
		session_set_download_rate_limit(self.session, self.config.get('global_dl_limit', 0))
		session_set_upload_rate_limit(self.session, self.config.get('global_ul_limit', 0))

		port_range = self.config.get('port_range', [6881, 6891])
		if not session_listen_on(self.session, port_range[0], port_range[1]):
			logger.warning(f"listen_on failed {port_range}, trying defaults 6881-6891")
			session_listen_on(self.session, 6881, 6891)
		else:
			logger.info(f"Listening on {port_range[0]}-{port_range[1]}")

		if self.config.get('enable_dht', True):
			safe_add_dht_routers(self.session)
			session_enable_feature(self.session, 'dht', True)

		load_session_state_safe(self.session)

	def setup_gui(self):
		self.root.title("Advanced BitTorrent Client")
		self.root.geometry("1380x920")
		self.root.protocol("WM_DELETE_WINDOW", self.on_closing)

		self.create_menu()
		self.create_toolbar()
		self.create_torrent_list()
		self.create_details_panel()
		self.create_status_bar()

		try:
			style = ttk.Style()
			style.theme_use('clam')
		except Exception:
			pass

		self.center_window()

	def center_window(self):
		self.root.update_idletasks()
		width = self.root.winfo_width()
		height = self.root.winfo_height()
		x = (self.root.winfo_screenwidth() // 2) - (width // 2)
		y = (self.root.winfo_screenheight() // 2) - (height // 2)
		self.root.geometry(f'{width}x{height}+{x}+{y}')

	def create_menu(self):
		menubar = tk.Menu(self.root)
		self.root.config(menu=menubar)

		file_menu = tk.Menu(menubar, tearoff=0)
		menubar.add_cascade(label="File", menu=file_menu)
		file_menu.add_command(label="Add Torrent File(s)...", command=self.add_torrent_files, accelerator="Ctrl+O")
		file_menu.add_command(label="Add Magnet Link...", command=self.add_magnet_dialog, accelerator="Ctrl+M")
		file_menu.add_command(label="Add Multiple Magnets...", command=self.add_multi_magnets_dialog)
		file_menu.add_command(label="Add from URL...", command=self.add_url_dialog)
		file_menu.add_separator()
		file_menu.add_command(label="Save As (copy/move completed)...", command=self.save_as_selected)
		file_menu.add_separator()
		file_menu.add_command(label="Export Torrent List...", command=self.export_torrent_list)
		file_menu.add_separator()
		file_menu.add_command(label="Exit", command=self.on_closing)

		edit_menu = tk.Menu(menubar, tearoff=0)
		menubar.add_cascade(label="Edit", menu=edit_menu)
		edit_menu.add_command(label="Settings", command=self.show_settings, accelerator="Ctrl+S")
		edit_menu.add_command(label="Speed Limits", command=self.show_speed_limits)

		view_menu = tk.Menu(menubar, tearoff=0)
		menubar.add_cascade(label="View", menu=view_menu)
		self.hide_completed_var = tk.BooleanVar(value=False)
		self.live_status_var = tk.BooleanVar(value=True)  # show single-line live status
		view_menu.add_checkbutton(label="Hide Completed/Seeding", variable=self.hide_completed_var, command=self.refresh_filter_view)
		view_menu.add_checkbutton(label="Show Live Status Panel", variable=self.live_status_var, command=self.toggle_live_status_panel)
		view_menu.add_command(label="Show Performance Graph", command=self.show_performance_graph)
		view_menu.add_command(label="Show Download History", command=self.show_download_history)

		torrent_menu = tk.Menu(menubar, tearoff=0)
		menubar.add_cascade(label="Torrent", menu=torrent_menu)
		torrent_menu.add_command(label="Start", command=self.start_selected)
		torrent_menu.add_command(label="Pause", command=self.pause_selected)
		torrent_menu.add_command(label="Resume", command=self.force_resume_selected)
		torrent_menu.add_command(label="Stop (halt seeding)", command=self.stop_selected)
		torrent_menu.add_separator()
		torrent_menu.add_command(label="Remove", command=self.remove_selected, accelerator="Delete")
		torrent_menu.add_command(label="Remove and Delete Data", command=self.remove_and_delete_selected)
		torrent_menu.add_command(label="Open Folder", command=self.open_folder)
		torrent_menu.add_command(label="Open File Location", command=self.open_file_location)
		torrent_menu.add_separator()
		torrent_menu.add_command(label="Force Recheck", command=self.force_recheck)
		torrent_menu.add_command(label="Force Reannounce", command=self.force_reannounce)
		torrent_menu.add_separator()
		torrent_menu.add_command(label="Copy Magnet Link", command=self.copy_magnet_link)
		torrent_menu.add_command(label="Save As", command=self.save_as_selected)

		help_menu = tk.Menu(menubar, tearoff=0)
		menubar.add_cascade(label="Help", menu=help_menu)
		help_menu.add_command(label="Documentation", command=self.show_documentation)
		help_menu.add_command(label="About", command=self.show_about)

		self.root.bind('<Control-o>', lambda e: self.add_torrent_files())
		self.root.bind('<Control-m>', lambda e: self.add_magnet_dialog())
		self.root.bind('<Control-s>', lambda e: self.show_settings())
		self.root.bind('<Delete>', lambda e: self.remove_selected())
		self.root.bind('<space>', lambda e: self.toggle_pause_selected())

	def create_toolbar(self):
		toolbar = ttk.Frame(self.root)
		toolbar.pack(fill=tk.X, padx=5, pady=(5, 0))

		ttk.Button(toolbar, text="Add Torrent(s)", command=self.add_torrent_files).pack(side=tk.LEFT, padx=(0, 5))
		ttk.Button(toolbar, text="Add Magnet", command=self.add_magnet_dialog).pack(side=tk.LEFT, padx=(0, 5))
		ttk.Button(toolbar, text="Add Multi Magnets", command=self.add_multi_magnets_dialog).pack(side=tk.LEFT, padx=(0, 5))
		ttk.Separator(toolbar, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=5)
		ttk.Button(toolbar, text="Start", command=self.start_selected).pack(side=tk.LEFT, padx=(0, 5))
		ttk.Button(toolbar, text="Pause", command=self.pause_selected).pack(side=tk.LEFT, padx=(0, 5))
		ttk.Button(toolbar, text="Resume", command=self.force_resume_selected).pack(side=tk.LEFT, padx=(0, 5))
		ttk.Button(toolbar, text="Stop", command=self.stop_selected).pack(side=tk.LEFT, padx=(0, 5))
		ttk.Button(toolbar, text="Remove", command=self.remove_selected).pack(side=tk.LEFT, padx=(0, 5))
		ttk.Button(toolbar, text="Remove+Data", command=self.remove_and_delete_selected).pack(side=tk.LEFT, padx=(0, 5))
		ttk.Button(toolbar, text="Open Folder", command=self.open_folder).pack(side=tk.LEFT, padx=(0, 5))
		ttk.Button(toolbar, text="Open File Location", command=self.open_file_location).pack(side=tk.LEFT, padx=(0, 5))
		ttk.Button(toolbar, text="Save As", command=self.save_as_selected).pack(side=tk.LEFT, padx=(0, 5))
		ttk.Separator(toolbar, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=5)

		speed_frame = ttk.Frame(toolbar)
		speed_frame.pack(side=tk.LEFT, padx=(0, 5))
		ttk.Label(speed_frame, text="DL:").pack(side=tk.LEFT)
		self.dl_limit_var = tk.StringVar(value=self.format_speed_limit_display(self.config.get('global_dl_limit', 0)))
		ttk.Entry(speed_frame, textvariable=self.dl_limit_var, width=7).pack(side=tk.LEFT)
		ttk.Label(speed_frame, text="KB/s").pack(side=tk.LEFT)
		ttk.Label(speed_frame, text="UL:").pack(side=tk.LEFT, padx=(5, 0))
		self.ul_limit_var = tk.StringVar(value=self.format_speed_limit_display(self.config.get('global_ul_limit', 0)))
		ttk.Entry(speed_frame, textvariable=self.ul_limit_var, width=7).pack(side=tk.LEFT)
		ttk.Label(speed_frame, text="KB/s").pack(side=tk.LEFT)
		ttk.Button(speed_frame, text="Apply", command=self.apply_speed_limits_toolbar).pack(side=tk.LEFT, padx=(5, 0))

		search_frame = ttk.Frame(toolbar)
		search_frame.pack(side=tk.RIGHT)
		ttk.Label(search_frame, text="Search:").pack(side=tk.LEFT, padx=(0, 5))
		self.search_var = tk.StringVar()
		search_entry = ttk.Entry(search_frame, textvariable=self.search_var, width=26)
		search_entry.pack(side=tk.LEFT)
		search_entry.bind('<KeyRelease>', self.filter_torrents)

	def create_torrent_list(self):
		self.paned = ttk.PanedWindow(self.root, orient=tk.VERTICAL)
		self.paned.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

		list_frame = ttk.Frame(self.paned)
		self.paned.add(list_frame, weight=3)

		tree_frame = ttk.Frame(list_frame)
		tree_frame.pack(fill=tk.BOTH, expand=True)

		columns = ('Name', 'Size', 'Progress', 'Status', 'Seeds', 'Peers', 'Down Speed', 'Up Speed', 'ETA', 'Ratio', 'Added On')
		self.tree = ttk.Treeview(tree_frame, columns=columns, show='headings', height=22)

		column_widths = [400, 120, 90, 120, 80, 80, 120, 120, 90, 80, 170]
		for i, (col, width) in enumerate(zip(columns, column_widths)):
			self.tree.heading(col, text=col, command=lambda c=col: self.sort_treeview(c))
			self.tree.column(col, width=width, anchor='center' if i > 0 else 'w')

		v_scrollbar = ttk.Scrollbar(tree_frame, orient=tk.VERTICAL, command=self.tree.yview)
		h_scrollbar = ttk.Scrollbar(tree_frame, orient=tk.HORIZONTAL, command=self.tree.xview)
		self.tree.configure(yscrollcommand=v_scrollbar.set, xscrollcommand=h_scrollbar.set)

		self.tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
		v_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
		h_scrollbar.pack(side=tk.BOTTOM, fill=tk.X)

		self.tree.bind('<Double-1>', self.on_torrent_double_click)
		self.tree.bind('<Button-3>', self.show_context_menu)
		self.tree.bind('<<TreeviewSelect>>', self.on_torrent_select)

	def create_details_panel(self):
		details_frame = ttk.Frame(self.paned)
		self.paned.add(details_frame, weight=2)

		self.notebook = ttk.Notebook(details_frame)
		self.notebook.pack(fill=tk.BOTH, expand=True)

		self.general_frame = ttk.Frame(self.notebook)
		self.notebook.add(self.general_frame, text="General")
		self.general_text = scrolledtext.ScrolledText(self.general_frame, height=12, wrap=tk.WORD)
		self.general_text.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
		self.general_text.config(state=tk.DISABLED)

		self.files_frame = ttk.Frame(self.notebook)
		self.notebook.add(self.files_frame, text="Files")
		self.create_files_tab()

		self.peers_frame = ttk.Frame(self.notebook)
		self.notebook.add(self.peers_frame, text="Peers")
		self.create_peers_tab()

		self.trackers_frame = ttk.Frame(self.notebook)
		self.notebook.add(self.trackers_frame, text="Trackers")
		self.create_trackers_tab()

		self.log_frame = ttk.Frame(self.notebook)
		self.notebook.add(self.log_frame, text="Log + Live")
		self.create_log_tab()

		self.performance_frame = ttk.Frame(self.notebook)
		self.notebook.add(self.performance_frame, text="Performance")
		self.create_performance_tab()

	def create_files_tab(self):
		file_ops_frame = ttk.Frame(self.files_frame)
		file_ops_frame.pack(fill=tk.X, padx=5, pady=(5, 0))
		ttk.Button(file_ops_frame, text="Set Priority", command=self.set_file_priority).pack(side=tk.LEFT, padx=(0, 5))
		ttk.Button(file_ops_frame, text="Expand All", command=self.expand_all_files).pack(side=tk.LEFT, padx=(0, 5))
		ttk.Button(file_ops_frame, text="Collapse All", command=self.collapse_all_files).pack(side=tk.LEFT)

		files_frame = ttk.Frame(self.files_frame)
		files_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

		files_columns = ('File', 'Size', 'Progress', 'Priority')
		self.files_tree = ttk.Treeview(files_frame, columns=files_columns, show='tree headings')
		for col in files_columns:
			self.files_tree.heading(col, text=col)
			self.files_tree.column(col, width=220 if col == 'File' else 160)

		files_v_scroll = ttk.Scrollbar(files_frame, orient=tk.VERTICAL, command=self.files_tree.yview)
		files_h_scroll = ttk.Scrollbar(files_frame, orient=tk.HORIZONTAL, command=self.files_tree.xview)
		self.files_tree.configure(yscrollcommand=files_v_scroll.set, xscrollcommand=files_h_scroll.set)

		self.files_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
		files_v_scroll.pack(side=tk.RIGHT, fill=tk.Y)
		files_h_scroll.pack(side=tk.BOTTOM, fill=tk.X)

		self.files_tree.bind('<Double-1>', self.on_file_double_click)

	def create_peers_tab(self):
		peers_columns = ('IP', 'Client', 'Progress', 'Down Speed', 'Up Speed', 'Flags')
		self.peers_tree = ttk.Treeview(self.peers_frame, columns=peers_columns, show='headings')
		for col in peers_columns:
			self.peers_tree.heading(col, text=col)
			self.peers_tree.column(col, width=160)
		peers_scroll = ttk.Scrollbar(self.peers_frame, orient=tk.VERTICAL, command=self.peers_tree.yview)
		self.peers_tree.configure(yscrollcommand=peers_scroll.set)
		self.peers_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5, pady=5)
		peers_scroll.pack(side=tk.RIGHT, fill=tk.Y, pady=5)

	def create_trackers_tab(self):
		trackers_columns = ('URL', 'Message')
		self.trackers_tree = ttk.Treeview(self.trackers_frame, columns=trackers_columns, show='headings')
		for col in trackers_columns:
			self.trackers_tree.heading(col, text=col)
			self.trackers_tree.column(col, width=400 if col == 'URL' else 400)
		trackers_scroll = ttk.Scrollbar(self.trackers_frame, orient=tk.VERTICAL, command=self.trackers_tree.yview)
		self.trackers_tree.configure(yscrollcommand=trackers_scroll.set)
		self.trackers_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5, pady=5)
		trackers_scroll.pack(side=tk.RIGHT, fill=tk.Y, pady=5)

	def create_log_tab(self):
		wrap = ttk.Frame(self.log_frame)
		wrap.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

		left = ttk.Frame(wrap)
		left.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
		right = ttk.Frame(wrap)
		right.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(5, 0))

		log_controls = ttk.Frame(left)
		log_controls.pack(fill=tk.X, pady=(0, 5))
		ttk.Button(log_controls, text="Clear Log", command=self.clear_log).pack(side=tk.LEFT)
		ttk.Button(log_controls, text="Save Log", command=self.save_log).pack(side=tk.LEFT, padx=(5, 0))

		self.log_text = scrolledtext.ScrolledText(left, height=14, wrap=tk.WORD)
		self.log_text.pack(fill=tk.BOTH, expand=True)
		self.log_text.config(state=tk.DISABLED)
		self.log("BitTorrent client started")

		live_controls = ttk.Frame(right)
		live_controls.pack(fill=tk.X, pady=(0, 5))
		ttk.Label(live_controls, text="Live Status (one line per torrent)").pack(side=tk.LEFT)
		self.live_status_text = scrolledtext.ScrolledText(right, height=14, wrap=tk.NONE)
		self.live_status_text.pack(fill=tk.BOTH, expand=True)
		self.live_status_text.config(state=tk.DISABLED)

	def toggle_live_status_panel(self):
		visible = self.live_status_var.get()
		try:
			self.live_status_text.configure(state=tk.NORMAL)
			self.live_status_text.delete(1.0, tk.END)
			if visible:
				self.live_status_text.insert(tk.END, "Live status enabled.\n")
			self.live_status_text.configure(state=tk.DISABLED)
		except Exception:
			pass

	def create_performance_tab(self):
		perf_frame = ttk.Frame(self.performance_frame)
		perf_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

		ttk.Label(perf_frame, text="Performance Metrics", font=('Arial', 12, 'bold')).pack(anchor=tk.W, pady=(0, 10))
		metrics_frame = ttk.Frame(perf_frame)
		metrics_frame.pack(fill=tk.X, pady=5)

		ttk.Label(metrics_frame, text="Download:", font=('Arial', 10, 'bold')).grid(row=0, column=0, sticky=tk.W)
		self.dl_stats_label = ttk.Label(metrics_frame, text="Total: 0 MB, Rate: 0 KB/s")
		self.dl_stats_label.grid(row=0, column=1, sticky=tk.W, padx=(10, 0))

		ttk.Label(metrics_frame, text="Upload:", font=('Arial', 10, 'bold')).grid(row=1, column=0, sticky=tk.W, pady=(5, 0))
		self.ul_stats_label = ttk.Label(metrics_frame, text="Total: 0 MB, Rate: 0 KB/s")
		self.ul_stats_label.grid(row=1, column=1, sticky=tk.W, padx=(10, 0), pady=(5, 0))

		ttk.Label(metrics_frame, text="Connections:", font=('Arial', 10, 'bold')).grid(row=2, column=0, sticky=tk.W, pady=(5, 0))
		self.conn_stats_label = ttk.Label(metrics_frame, text="Active: 0")
		self.conn_stats_label.grid(row=2, column=1, sticky=tk.W, padx=(10, 0), pady=(5, 0))

		ttk.Label(metrics_frame, text="Memory:", font=('Arial', 10, 'bold')).grid(row=3, column=0, sticky=tk.W, pady=(5, 0))
		self.mem_stats_label = ttk.Label(metrics_frame, text="Usage: 0 MB")
		self.mem_stats_label.grid(row=3, column=1, sticky=tk.W, padx=(10, 0), pady=(5, 0))

		ttk.Label(metrics_frame, text="CPU Usage:", font=('Arial', 10, 'bold')).grid(row=4, column=0, sticky=tk.W, pady=(5, 0))
		self.cpu_stats_label = ttk.Label(metrics_frame, text="Current: 0%")
		self.cpu_stats_label.grid(row=4, column=1, sticky=tk.W, padx=(10, 0), pady=(5, 0))

		ttk.Separator(perf_frame, orient=tk.HORIZONTAL).pack(fill=tk.X, pady=10)

		ttk.Label(perf_frame, text="Detailed Statistics:", font=('Arial', 10, 'bold')).pack(anchor=tk.W)
		self.perf_text = scrolledtext.ScrolledText(perf_frame, height=12, wrap=tk.WORD)
		self.perf_text.pack(fill=tk.BOTH, expand=True, pady=(5, 0))
		self.perf_text.config(state=tk.DISABLED)

	def create_status_bar(self):
		self.status_bar = ttk.Frame(self.root)
		self.status_bar.pack(fill=tk.X, padx=5, pady=(0, 5))
		self.status_label = ttk.Label(self.status_bar, text="Ready")
		self.status_label.pack(side=tk.LEFT)
		self.progress_bar = ttk.Progressbar(self.status_bar, mode='determinate')
		self.progress_bar.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=5)
		self.connection_label = ttk.Label(self.status_bar, text="DHT: 0 nodes")
		self.connection_label.pack(side=tk.RIGHT, padx=(5, 0))
		self.speed_label = ttk.Label(self.status_bar, text="↓ 0 kB/s ↑ 0 kB/s")
		self.speed_label.pack(side=tk.RIGHT, padx=(5, 0))

	def ask_fast_download_options(self):
		return FastDownloadDialog(self.root, self.config).result

	def add_torrent_files(self):
		paths = filedialog.askopenfilenames(
			title="Select Torrent File(s)",
			initialdir=self.config.get('last_opened_torrent_dir', str(platform_downloads_dir())),
			filetypes=[("Torrent files", "*.torrent"), ("All files", "*.*")]
		)
		if not paths:
			return
		fd = self.ask_fast_download_options()
		default_save = self.config.get('download_path', str(platform_downloads_dir()))
		for file_path in paths:
			try:
				self.add_torrent(file_path, default_save, fast_download=fd)
			except Exception as e:
				self.log(f"Failed adding {file_path}: {e}")
		self.config['last_opened_torrent_dir'] = str(Path(paths[-1]).parent)
		self.save_config()

	def add_magnet_dialog(self):
		dialog = MagnetDialog(self.root, self.config.get('download_path', str(platform_downloads_dir())))
		magnet_uri, save_path = dialog.result if dialog.result else (None, None)
		if magnet_uri and save_path:
			fd = self.ask_fast_download_options()
			self.add_torrent(magnet_uri, save_path, fast_download=fd)

	def add_multi_magnets_dialog(self):
		dialog = MultiMagnetDialog(self.root, self.config.get('download_path', str(platform_downloads_dir())))
		result = dialog.result
		if not result:
			return
		save_path, magnets = result
		fd = self.ask_fast_download_options()
		for m in magnets:
			try:
				self.add_torrent(m, save_path, fast_download=fd)
			except Exception as e:
				self.log(f"Add magnet failed: {e}")

	def add_url_dialog(self):
		dialog = UrlDialog(self.root, self.config.get('download_path', str(platform_downloads_dir())))
		url, save_path = dialog.result if dialog.result else (None, None)
		if url and save_path:
			fd = self.ask_fast_download_options()
			self.download_torrent_from_url(url, save_path, fast_download=fd)

	def download_torrent_from_url(self, url, save_path, fast_download=None):
		try:
			self.log(f"Downloading torrent from URL: {url}")
			r = requests.get(url, timeout=30)
			r.raise_for_status()
			tmp = Path(f"temp_{int(time.time())}.torrent")
			tmp.write_bytes(r.content)
			self.add_torrent(str(tmp), save_path, fast_download=fast_download)
			threading.Timer(5.0, lambda: tmp.exists() and tmp.unlink()).start()
		except Exception as e:
			messagebox.showerror("Error", f"Failed to download/add torrent: {e}")
			self.log(f"URL add error: {e}")

	def apply_fast_download(self, handle, fast_download):
		try:
			if not fast_download or not fast_download.get('enabled', False):
				return
			connections = int(fast_download.get('connections', 5))
			# Approximate multi-connection acceleration:
			# - raise per-torrent peer limit
			# - enable sequential if requested (default True for "fast download")
			if lt_has(handle, 'set_max_connections'):
				handle.set_max_connections(max(20, connections * 50))
			if fast_download.get('sequential', True) and lt_has(handle, 'set_sequential_download'):
				handle.set_sequential_download(True)
			# remove upload-only if present
			if lt_has(handle, 'set_upload_mode'):
				handle.set_upload_mode(False)
		except Exception:
			pass

	def add_torrent(self, torrent_source, save_path=None, fast_download=None):
		if save_path is None:
			save_path = self.config.get('download_path', str(platform_downloads_dir()))
		Path(save_path).mkdir(parents=True, exist_ok=True)

		if str(torrent_source).startswith("magnet:"):
			handle = lt.add_magnet_uri(self.session, torrent_source, {'save_path': save_path})
			source_type = 'magnet'
			name_hint = torrent_source[:64] + "..."
		else:
			info = lt.torrent_info(torrent_source)
			params = {
				'ti': info,
				'save_path': save_path,
				'storage_mode': lt.storage_mode_t.storage_mode_sparse
			}
			handle = self.session.add_torrent(params)
			source_type = 'file'
			name_hint = info.name()

		self.apply_fast_download(handle, fast_download)

		t_hash = safe_info_hash_str(handle)
		if t_hash in self.torrents:
			self.log(f"Skipped duplicate torrent: {name_hint}")
			return

		self.torrents[t_hash] = {
			'handle': handle,
			'added_time': datetime.now(),
			'source': source_type,
			'save_path': save_path,
			'moved': False
		}

		try:
			st = handle.status()
			name = getattr(st, 'name', None) or (handle.name() if lt_has(handle, 'name') else name_hint)
		except Exception:
			name = name_hint

		self.download_history.append({
			'name': name,
			'hash': t_hash,
			'added_time': datetime.now(),
			'source': source_type,
			'save_path': save_path
		})

	def update_torrents_loop(self):
		while self.running:
			try:
				try:
					self.session.post_torrent_updates()
				except Exception:
					pass
				self.root.after(0, self.update_gui_elements)
				time.sleep(1)
			except Exception as e:
				self.log(f"Update loop error: {e}")
				time.sleep(3)

	def update_gui_elements(self):
		try:
			self.update_torrent_list()
			self.update_details()
			self.update_status_bar()
			self.update_performance_stats()
			self.auto_move_completed()
			self.update_live_status()  # single-line per torrent
			if self.hide_completed_var.get():
				self.refresh_filter_view()
		except Exception as e:
			self.log(f"GUI update error: {e}")

	def update_torrent_list(self):
		try:
			handles = self.session.get_torrents()
		except Exception:
			handles = []
		current = set()
		for h in handles:
			try:
				if not h.is_valid():
					continue
			except Exception:
				continue
			t_hash = safe_info_hash_str(h)
			current.add(t_hash)
			if t_hash not in self.torrents:
				self.torrents[t_hash] = {
					'handle': h,
					'added_time': datetime.now(),
					'source': 'unknown',
					'save_path': getattr(h.status(), 'save_path', self.config.get('download_path', str(platform_downloads_dir()))),
					'moved': False
				}
			self.update_tree_item(t_hash, h, h.status())
		for gone in set(self.torrents.keys()) - current:
			self.remove_tree_item(gone)
			self.torrents.pop(gone, None)

	def update_tree_item(self, torrent_hash, handle, status):
		existing_item = None
		for item in self.tree.get_children():
			tags = self.tree.item(item)['tags']
			if tags and tags[0] == torrent_hash:
				existing_item = item
				break

		try:
			name = getattr(status, 'name', None) or (handle.name() if lt_has(handle, "name") else "Loading...")
		except Exception:
			name = "Loading..."

		size = self.format_bytes(getattr(status, "total_wanted", 0))
		progress = f"{getattr(status, 'progress', 0.0) * 100:.1f}%"
		state = self.get_status_text(status)
		seeds = f"{getattr(status, 'num_seeds', 0)} ({getattr(status, 'num_complete', 0)})"
		peers = f"{getattr(status, 'num_peers', 0)} ({getattr(status, 'num_incomplete', 0)})"
		down_speed = self.format_speed(getattr(status, "download_rate", 0))
		up_speed = self.format_speed(getattr(status, "upload_rate", 0))
		eta = self.calculate_eta(status)
		all_up = float(getattr(status, "all_time_upload", getattr(status, "total_upload", 0)))
		all_down = float(getattr(status, "all_time_download", getattr(status, "total_download", 1)))
		ratio = f"{all_up / max(all_down, 1.0):.2f}"
		added_time = self.torrents.get(torrent_hash, {}).get('added_time', datetime.now())
		added_str = added_time.strftime("%Y-%m-%d %H:%M")

		values = (name, size, progress, state, seeds, peers, down_speed, up_speed, eta, ratio, added_str)
		tag = self.get_state_tag(status)

		if existing_item:
			self.tree.item(existing_item, values=values)
			self.tree.item(existing_item, tags=(torrent_hash, tag))
		else:
			self.tree.insert('', tk.END, values=values, tags=(torrent_hash, tag))

		self.tree.tag_configure('seeding', foreground='green')
		self.tree.tag_configure('downloading', foreground='blue')
		self.tree.tag_configure('checking', foreground='orange')
		self.tree.tag_configure('error', foreground='red')
		self.tree.tag_configure('paused', foreground='gray')

	def get_state_tag(self, status):
		try:
			if getattr(status, "paused", False):
				return 'paused'
			st = getattr(status, "state", None)
			if st == lt.torrent_status.seeding:
				return 'seeding'
			if st == lt.torrent_status.downloading:
				return 'downloading'
			if st in (lt.torrent_status.checking_files, lt.torrent_status.checking_resume_data):
				return 'checking'
			if st == lt.torrent_status.error:
				return 'error'
		except Exception:
			return ''
		return ''

	def remove_tree_item(self, torrent_hash):
		for item in self.tree.get_children():
			tags = self.tree.item(item)['tags']
			if tags and tags[0] == torrent_hash:
				self.tree.delete(item)
				break

	def update_details(self):
		selection = self.tree.selection()
		if not selection:
			self.set_general_placeholder()
			return
		item = selection[0]
		tags = self.tree.item(item)['tags']
		if not tags:
			self.set_general_placeholder()
			return
		t_hash = tags[0]
		if t_hash not in self.torrents:
			self.set_general_placeholder()
			return
		handle = self.torrents[t_hash]['handle']
		status = handle.status()
		self.update_general_info(handle, status)
		tab_idx = self.notebook.index(self.notebook.select())
		if tab_idx == 1:
			self.update_files_info(handle)
		elif tab_idx == 2:
			self.update_peers_info(handle)
		elif tab_idx == 3:
			self.update_trackers_info(handle)

	def set_general_placeholder(self):
		self.general_text.config(state=tk.NORMAL)
		self.general_text.delete(1.0, tk.END)
		self.general_text.insert(tk.END, "Select a torrent to view details.")
		self.general_text.config(state=tk.DISABLED)
		for w in (self.files_tree, self.peers_tree, self.trackers_tree):
			for child in w.get_children():
				w.delete(child)

	def update_general_info(self, handle, status):
		torrent_info = None
		try:
			if getattr(status, "has_metadata", False):
				torrent_info = handle.get_torrent_info()
		except Exception:
			torrent_info = None

		creation_date_str = 'Unknown'
		try:
			if torrent_info and hasattr(torrent_info, "creation_date"):
				cd = torrent_info.creation_date()
				if cd and cd > 0:
					creation_date_str = datetime.fromtimestamp(cd).strftime('%Y-%m-%d %H:%M:%S')
		except Exception:
			pass

		def fmt_time(seconds):
			return self.format_time(int(seconds or 0))

		content_name = getattr(status, 'name', '') or (handle.name() if lt_has(handle, "name") else 'N/A')

		info_text = f"""Name: {content_name}
Size: {self.format_bytes(getattr(status, 'total_wanted', 0))}
Progress: {getattr(status, 'progress', 0.0) * 100:.2f}%
Status: {self.get_status_text(status)}
Download Rate: {self.format_speed(getattr(status, 'download_rate', 0))}
Upload Rate: {self.format_speed(getattr(status, 'upload_rate', 0))}
Seeds: {getattr(status, 'num_seeds', 0)} connected, {getattr(status, 'num_complete', 0)}) total
Peers: {getattr(status, 'num_peers', 0)} connected, {getattr(status, 'num_incomplete', 0)} total
Downloaded: {self.format_bytes(getattr(status, 'total_done', 0))}
Uploaded: {self.format_bytes(getattr(status, 'total_upload', 0))}
Ratio: {float(getattr(status, 'total_upload', 0)) / max(float(getattr(status, 'total_done', 0)), 1.0):.3f}
Time Active: {fmt_time(getattr(status, 'active_time', 0))}
Seeding Time: {fmt_time(getattr(status, 'seeding_time', 0))}
Save Path: {getattr(status, 'save_path', '')}
Top-Level Path: {(Path(getattr(status, 'save_path', '')) / content_name) if content_name not in ('N/A','') else ''}
Hash: {safe_info_hash_str(handle)}
Created By: {(torrent_info.creator() if torrent_info and hasattr(torrent_info, 'creator') else 'Unknown')}
Created On: {creation_date_str}
Comment: {(torrent_info.comment() if torrent_info and hasattr(torrent_info, 'comment') else 'Unknown')}
"""
		self.general_text.config(state=tk.NORMAL)
		self.general_text.delete(1.0, tk.END)
		self.general_text.insert(tk.END, info_text)
		self.general_text.config(state=tk.DISABLED)

	def update_files_info(self, handle):
		for item in self.files_tree.get_children():
			self.files_tree.delete(item)
		st = handle.status()
		if not getattr(st, "has_metadata", False):
			self.files_tree.insert('', tk.END, values=("Metadata not available.", "", "", ""))
			return
		try:
			ti = handle.get_torrent_info()
			files = ti.files()
		except Exception:
			self.files_tree.insert('', tk.END, values=("Metadata not available.", "", "", ""))
			return
		try:
			file_progress_bytes = handle.file_progress(0)
		except Exception:
			file_progress_bytes = []

		tree_items = {}
		def insert_recursive(path_parts, current_parent_id, file_index=-1):
			if not path_parts:
				return
			part = path_parts[0]
			current_id = f"{current_parent_id}/{part}" if current_parent_id else part
			if current_id not in tree_items:
				if len(path_parts) == 1 and file_index != -1:
					file_size = files.file_size(file_index)
					progress_pct = ""
					try:
						if file_progress_bytes and file_index < len(file_progress_bytes):
							pb = max(0, min(file_progress_bytes[file_index], file_size))
							progress_pct = f"{(pb / file_size * 100) if file_size > 0 else 0:.1f}%"
					except Exception:
						progress_pct = ""
					file_priority = self.safe_get_file_priority(handle, file_index)
					item_id = self.files_tree.insert(
						current_parent_id,
						tk.END,
						text=part,
						values=(self.format_bytes(file_size), progress_pct, self.get_priority_text(file_priority)),
						tags=(str(file_index), 'file')
					)
					tree_items[current_id] = item_id
				else:
					item_id = self.files_tree.insert(current_parent_id, tk.END, text=part, open=True, values=("", "", ""))
					tree_items[current_id] = item_id
			if len(path_parts) > 1:
				insert_recursive(path_parts[1:], tree_items[current_id], file_index)

		for i in range(ti.num_files()):
			file_path = str(Path(files.file_path(i)))
			insert_recursive(file_path.split(os.sep), '', i)

	def safe_get_file_priority(self, handle, file_index: int) -> int:
		try:
			return int(handle.file_priority(file_index))
		except Exception:
			return FILE_PRIORITY_NORMAL

	def update_peers_info(self, handle):
		for item in self.peers_tree.get_children():
			self.peers_tree.delete(item)
		try:
			peers = handle.get_peer_info()
			for p in peers:
				try:
					ip_obj = getattr(p, "ip", None)
					ip_text = str(ip_obj[0]) if isinstance(ip_obj, tuple) else str(ip_obj)
					client = getattr(p, "client", "")
					prog = f"{getattr(p, 'progress', 0.0) * 100:.1f}%"
					ds = self.format_speed(getattr(p, "down_speed", 0))
					us = self.format_speed(getattr(p, "up_speed", 0))
					flags = self.format_peer_flags(getattr(p, "flags", 0))
					self.peers_tree.insert('', tk.END, values=(ip_text, client, prog, ds, us, flags))
				except Exception:
					continue
		except Exception as e:
			self.log(f"Peer list error: {e}")

	def format_peer_flags(self, flags: int) -> str:
		try:
			out = []
			if flags & lt.peer_info.interesting: out.append("I")
			if flags & lt.peer_info.choked: out.append("C")
			if flags & lt.peer_info.remote_interested: out.append("i")
			if flags & lt.peer_info.remote_choked: out.append("c")
			if flags & lt.peer_info.supports_extensions: out.append("E")
			if flags & lt.peer_info.handshake: out.append("H")
			if flags & lt.peer_info.connecting: out.append("X")
			if flags & lt.peer_info.queued: out.append("Q")
			if hasattr(lt.peer_info, "on_parole") and (flags & lt.peer_info.on_parole): out.append("P")
			if flags & lt.peer_info.seed: out.append("S")
			if flags & lt.peer_info.optimistic_unchoke: out.append("O")
			if flags & lt.peer_info.snubbed: out.append("U")
			if hasattr(lt.peer_info, "upload_only") and (flags & lt.peer_info.upload_only): out.append("D")
			if hasattr(lt.peer_info, "endgame_mode") and (flags & lt.peer_info.endgame_mode): out.append("F")
			if hasattr(lt.peer_info, "holepunched") and (flags & lt.peer_info.holepunched): out.append("L")
			if hasattr(lt.peer_info, "i2p_peer") and (flags & lt.peer_info.i2p_peer): out.append("Z")
			if hasattr(lt.peer_info, "utp_peer") and (flags & lt.peer_info.utp_peer): out.append("T")
			if hasattr(lt.peer_info, "webrtc_peer") and (flags & lt.peer_info.webrtc_peer): out.append("W")
			if flags & lt.peer_info.outgoing: out.append("O")
			return "".join(out) if out else "-"
		except Exception:
			return "-"

	def update_trackers_info(self, handle):
		for item in self.trackers_tree.get_children():
			self.trackers_tree.delete(item)
		try:
			entries = handle.trackers()
			for tr in entries:
				url = getattr(tr, "url", "")
				msg = getattr(tr, "message", "")
				self.trackers_tree.insert('', tk.END, values=(url, msg))
		except Exception as e:
			self.log(f"Trackers error: {e}")

	def update_status_bar(self):
		total_down = 0
		total_up = 0
		try:
			for h in self.session.get_torrents():
				if h.is_valid():
					st = h.status()
					total_down += getattr(st, "download_rate", 0)
					total_up += getattr(st, "upload_rate", 0)
		except Exception:
			pass

		try:
			sst = self.session.status()
			dht_nodes = getattr(sst, "dht_nodes", 0)
		except Exception:
			dht_nodes = 0

		total_wanted_all = 0
		total_done_all = 0
		try:
			for h in self.session.get_torrents():
				if h.is_valid():
					st = h.status()
					total_wanted_all += getattr(st, "total_wanted", 0)
					total_done_all += getattr(st, "total_done", 0)
		except Exception:
			pass

		progress = (total_done_all / total_wanted_all * 100) if total_wanted_all > 0 else 0.0

		self.speed_label.config(text=f"↓ {self.format_speed(total_down)} ↑ {self.format_speed(total_up)}")
		self.connection_label.config(text=f"DHT: {dht_nodes} nodes")
		self.status_label.config(text=f"Torrents: {len(self.torrents)}")
		self.progress_bar['value'] = progress

	def update_performance_stats(self):
		try:
			sst = self.session.status()
			self.performance_stats['download_speeds'].append(getattr(sst, 'download_rate', 0))
			self.performance_stats['upload_speeds'].append(getattr(sst, 'upload_rate', 0))
		except Exception:
			self.performance_stats['download_speeds'].append(0)
			self.performance_stats['upload_speeds'].append(0)

		try:
			process = psutil.Process(os.getpid())
			mem = process.memory_info().rss
			self.performance_stats['memory_usage'].append(mem)
			self.performance_stats['cpu_usage'].append(process.cpu_percent(interval=None))
		except Exception:
			self.performance_stats['memory_usage'].append(0)
			self.performance_stats['cpu_usage'].append(0)

		self.update_performance_tab()

	def update_performance_tab(self):
		try:
			sst = self.session.status()
			self.dl_stats_label.config(text=f"Total: {self.format_bytes(getattr(sst, 'total_download', 0))}, Rate: {self.format_speed(getattr(sst, 'download_rate', 0))}")
			self.ul_stats_label.config(text=f"Total: {self.format_bytes(getattr(sst, 'total_upload', 0))}, Rate: {self.format_speed(getattr(sst, 'upload_rate', 0))}")
			self.conn_stats_label.config(text=f"Active: {getattr(sst, 'num_peers', 0)}")
		except Exception:
			self.dl_stats_label.config(text="Total: 0, Rate: 0")
			self.ul_stats_label.config(text="Total: 0, Rate: 0")
			self.conn_stats_label.config(text="Active: 0")

		try:
			process = psutil.Process(os.getpid())
			m = process.memory_info().rss
			self.mem_stats_label.config(text=f"Usage: {self.format_bytes(m)}")
			cur_cpu = self.performance_stats['cpu_usage'][-1] if self.performance_stats['cpu_usage'] else 0.0
			self.cpu_stats_label.config(text=f"Current: {cur_cpu:.1f}%")
		except Exception:
			self.mem_stats_label.config(text="Usage: N/A")
			self.cpu_stats_label.config(text="Current: N/A")

		try:
			sst = self.session.status()
			stats_text = f"""Session Uptime: {self.format_time(int(getattr(sst, 'uptime', 0)))}
Total Download: {self.format_bytes(getattr(sst, 'total_download', 0))}
Total Upload: {self.format_bytes(getattr(sst, 'total_upload', 0))}
Download Rate: {self.format_speed(getattr(sst, 'download_rate', 0))}
Upload Rate: {self.format_speed(getattr(sst, 'upload_rate', 0))}
Peers: {getattr(sst, 'num_peers', 0)}
Unchoked Peers: {getattr(sst, 'num_unchoked', 0)}
DHT Nodes: {getattr(sst, 'dht_nodes', 0)}
"""
		except Exception:
			stats_text = "No session stats available."

		self.perf_text.config(state=tk.NORMAL)
		self.perf_text.delete(1.0, tk.END)
		self.perf_text.insert(tk.END, stats_text)
		self.perf_text.config(state=tk.DISABLED)

	def update_live_status(self):
		now = time.time()
		if not self.live_status_var.get():
			return
		# throttle to ~2Hz
		if now - self._last_live_status_render < 0.5:
			return
		self._last_live_status_render = now
		lines = []
		for hsh, info in self.torrents.items():
			h = info['handle']
			try:
				st = h.status()
				name = getattr(st, 'name', '') or (h.name() if lt_has(h, 'name') else hsh[:10])
				state = self.get_status_text(st)
				prog = f"{getattr(st, 'progress', 0.0) * 100:.1f}%"
				ds = self.format_speed(getattr(st, 'download_rate', 0))
				us = self.format_speed(getattr(st, 'upload_rate', 0))
				lines.append(f"{name} | {prog} | {state} | ↓ {ds} ↑ {us}")
			except Exception:
				continue
		try:
			self.live_status_text.config(state=tk.NORMAL)
			self.live_status_text.delete(1.0, tk.END)
			self.live_status_text.insert(tk.END, "\n".join(lines) if lines else "No torrents yet.")
			self.live_status_text.config(state=tk.DISABLED)
		except Exception:
			pass

	def auto_move_completed(self):
		completed_root = Path(self.config.get('completed_path', str(platform_downloads_dir() / "Completed")))
		try:
			completed_root.mkdir(parents=True, exist_ok=True)
		except Exception:
			return
		for hsh, info in list(self.torrents.items()):
			handle = info['handle']
			try:
				st = handle.status()
				is_done = getattr(st, 'is_seeding', False) or getattr(st, 'state', None) == lt.torrent_status.seeding or getattr(st, 'progress', 0.0) >= 0.999
				if is_done and not info.get('moved', False):
					src = Path(getattr(st, 'save_path', info['save_path']))
					name = getattr(st, 'name', None) or (handle.name() if lt_has(handle, 'name') else hsh)
					if not name:
						continue
					src_content = src / name
					target = completed_root / name
					try:
						if src_content.exists():
							if src_content.is_dir():
								shutil.move(str(src_content), str(target))
							else:
								target.parent.mkdir(parents=True, exist_ok=True)
								shutil.move(str(src_content), str(target))
						elif src.exists():
							shutil.move(str(src), str(target))
						else:
							continue
						info['moved'] = True
						self.log(f"Auto-moved completed to: {target}")
					except Exception as me:
						self.log(f"Auto-move failed: {me}")
			except Exception:
				continue

	def refresh_filter_view(self):
		hide_completed = self.hide_completed_var.get()
		for item in self.tree.get_children():
			values = self.tree.item(item)['values']
			if not hide_completed:
				self.tree.reattach(item, '', tk.END)
				continue
			status_text = values[3] if len(values) > 3 else ""
			if any(s in str(status_text) for s in ("Finished", "Seeding")):
				self.tree.detach(item)
			else:
				self.tree.reattach(item, '', tk.END)

	def start_selected(self):
		item = self.get_single_selection()
		if not item:
			return
		h = self.get_handle_from_item(item)
		if not h:
			return
		try:
			h.resume()
			if lt_has(h, 'set_upload_mode'):
				h.set_upload_mode(False)
			self.log(f"Started: {h.name() if lt_has(h, 'name') else ''}")
		except Exception as e:
			self.log(f"Start error: {e}")

	def pause_selected(self):
		item = self.get_single_selection()
		if not item:
			return
		h = self.get_handle_from_item(item)
		if not h:
			return
		try:
			h.pause()
			self.log(f"Paused: {h.name() if lt_has(h, 'name') else ''}")
		except Exception as e:
			self.log(f"Pause error: {e}")

	def stop_selected(self):
		item = self.get_single_selection()
		if not item:
			return
		h = self.get_handle_from_item(item)
		if not h:
			return
		try:
			if lt_has(h, 'set_upload_mode'):
				h.set_upload_mode(True)
			h.pause()
			self.log("Stopped (seeding halted)")
		except Exception as e:
			self.log(f"Stop error: {e}")

	def force_resume_selected(self):
		item = self.get_single_selection()
		if not item:
			return
		h = self.get_handle_from_item(item)
		if not h:
			return
		try:
			if lt_has(h, 'set_upload_mode'):
				h.set_upload_mode(False)
			h.resume()
			self.log("Forced resume")
		except Exception as e:
			self.log(f"Force resume error: {e}")

	def toggle_pause_selected(self):
		item = self.get_single_selection()
		if not item:
			return
		h = self.get_handle_from_item(item)
		if not h:
			return
		try:
			st = h.status()
			if getattr(st, "paused", False):
				if lt_has(h, 'set_upload_mode'):
					h.set_upload_mode(False)
				h.resume()
				self.log(f"Resumed: {h.name() if lt_has(h, 'name') else ''}")
			else:
				h.pause()
				self.log(f"Paused: {h.name() if lt_has(h, 'name') else ''}")
		except Exception as e:
			self.log(f"Toggle pause error: {e}")

	def remove_selected(self):
		item = self.get_single_selection()
		if not item:
			return
		if not messagebox.askyesno("Remove Torrent", "Remove torrent from list only? Data will remain on disk."):
			return
		self._remove_common(item, delete_data=False)

	def remove_and_delete_selected(self):
		item = self.get_single_selection()
		if not item:
			return
		if not messagebox.askyesno("Remove & Delete Data", "Remove torrent and delete its downloaded data from disk?"):
			return
		self._remove_common(item, delete_data=True)

	def _remove_common(self, item, delete_data=False):
		h = self.get_handle_from_item(item)
		if not h:
			return
		try:
			if delete_data:
				try:
					flag = getattr(getattr(lt, 'options_t', object()), 'delete_files', 1)
					self.session.remove_torrent(h, flag)
				except Exception:
					self.session.remove_torrent(h)
					try:
						st = h.status()
						name = getattr(st, 'name', '') or (h.name() if lt_has(h, 'name') else '')
						base = Path(getattr(st, 'save_path', ''))
						target = (base / name) if name else base
						if target.exists():
							if target.is_dir():
								shutil.rmtree(target, ignore_errors=True)
							else:
								target.unlink(missing_ok=True)
					except Exception:
						pass
			else:
				self.session.remove_torrent(h)
			t_hash = self.tree.item(item)['tags'][0]
			self.torrents.pop(t_hash, None)
			self.tree.delete(item)
			self.log("Removed torrent" + (" and data" if delete_data else ""))
		except Exception as e:
			self.log(f"Remove error: {e}")

	def save_as_selected(self):
		item = self.get_single_selection()
		if not item:
			return
		h = self.get_handle_from_item(item)
		if not h:
			return
		st = h.status()
		src_path = Path(getattr(st, 'save_path', ''))
		if not src_path.exists():
			messagebox.showinfo("Save As", "Source path not found on disk yet.")
			return
		dest = filedialog.askdirectory(initialdir=str(platform_downloads_dir()))
		if not dest:
			return
		dest_path = Path(dest)
		try:
			name = getattr(st, 'name', None) or (h.name() if lt_has(h, 'name') else safe_info_hash_str(h))
			if not name:
				messagebox.showinfo("Save As", "Cannot resolve content name yet.")
				return
			src_content = src_path / name
			target = dest_path / name
			if src_content.exists():
				if src_content.is_dir():
					shutil.copytree(str(src_content), str(target), dirs_exist_ok=True)
				else:
					target.parent.mkdir(parents=True, exist_ok=True)
					shutil.copy2(str(src_content), str(target))
			else:
				if src_path.is_dir():
					shutil.copytree(str(src_path), str(target), dirs_exist_ok=True)
				elif src_path.exists():
					target.parent.mkdir(parents=True, exist_ok=True)
					shutil.copy2(str(src_path), str(target))
			self.log(f"Saved to: {target}")
			messagebox.showinfo("Save As", f"Saved to: {target}")
		except Exception as e:
			self.log(f"Save As failed: {e}")
			messagebox.showerror("Save As", f"Failed: {e}")

	def force_recheck(self):
		item = self.get_single_selection()
		if not item:
			return
		h = self.get_handle_from_item(item)
		if not h:
			return
		try:
			h.force_recheck()
			self.log("Force recheck")
		except Exception as e:
			self.log(f"Recheck error: {e}")

	def force_reannounce(self):
		item = self.get_single_selection()
		if not item:
			return
		h = self.get_handle_from_item(item)
		if not h:
			return
		try:
			h.force_reannounce()
			self.log("Force reannounce")
		except Exception as e:
			self.log(f"Reannounce error: {e}")

	def open_folder(self):
		item = self.get_single_selection()
		if not item:
			return
		h = self.get_handle_from_item(item)
		if not h:
			return
		st = h.status()
		content_name = getattr(st, "name", "") or (h.name() if lt_has(h, 'name') else "")
		save_path = Path(getattr(st, "save_path", ""))
		target = save_path if not content_name else (save_path / content_name)
		if target.exists():
			try:
				open_path_in_os(target if target.is_dir() else target.parent)
			except Exception as e:
				self.log(str(e))
				messagebox.showerror("Error", str(e))
		else:
			if save_path.exists():
				open_path_in_os(save_path)
			else:
				messagebox.showinfo("Info", "Download path does not exist.")

	def open_file_location(self):
		item = self.get_single_selection()
		if not item:
			return
		h = self.get_handle_from_item(item)
		if not h:
			return
		try:
			st = h.status()
			name = getattr(st, "name", "") or (h.name() if lt_has(h, 'name') else "")
			base = Path(getattr(st, "save_path", ""))
			if name:
				target = base / name
				if target.exists():
					open_path_in_os(target if target.is_dir() else target.parent)
					return
			if base.exists():
				open_path_in_os(base)
			else:
				messagebox.showinfo("Info", "File location not found yet.")
		except Exception as e:
			self.log(f"Open file location error: {e}")
			messagebox.showerror("Error", str(e))

	def copy_magnet_link(self):
		item = self.get_single_selection()
		if not item:
			return
		h = self.get_handle_from_item(item)
		if not h:
			return
		try:
			if getattr(h.status(), "has_metadata", False):
				info = h.get_torrent_info()
				magnet_link = lt.make_magnet_uri(info)
				self.root.clipboard_clear()
				self.root.clipboard_append(magnet_link)
				self.log(f"Magnet copied: {magnet_link[:64]}...")
			else:
				messagebox.showinfo("Info", "Metadata not available yet.")
		except Exception as e:
			self.log(f"Copy magnet error: {e}")

	def get_single_selection(self):
		sel = self.tree.selection()
		if not sel:
			return None
		return sel[0]

	def get_handle_from_item(self, item):
		tags = self.tree.item(item)['tags']
		if not tags:
			return None
		t_hash = tags[0]
		return self.torrents.get(t_hash, {}).get('handle')

	def apply_speed_limits_toolbar(self):
		try:
			dl_limit = self.parse_speed_limit_input(self.dl_limit_var.get())
			ul_limit = self.parse_speed_limit_input(self.ul_limit_var.get())
			session_set_download_rate_limit(self.session, dl_limit)
			session_set_upload_rate_limit(self.session, ul_limit)
			self.config['global_dl_limit'] = dl_limit
			self.config['global_ul_limit'] = ul_limit
			self.save_config()
			self.log(f"Applied speed limits: DL={dl_limit/1024:.0f} KB/s, UL={ul_limit/1024:.0f} KB/s" if (dl_limit or ul_limit) else "Applied speed limits: unlimited")
		except Exception:
			messagebox.showerror("Error", "Enter numeric values or '0'/'inf' for limits.")

	def parse_speed_limit_input(self, input_str):
		s = str(input_str).strip().lower()
		if s in ["0", "inf", "infinity", "∞", "unlimited"]:
			return 0
		return int(float(s) * 1024)

	def format_speed_limit_display(self, bytes_per_second):
		if int(bytes_per_second) == 0:
			return "∞"
		return str(int(bytes_per_second) // 1024)

	def on_file_double_click(self, event):
		selection = self.files_tree.selection()
		if not selection:
			return
		item = selection[0]
		item_tags = self.files_tree.item(item, 'tags')
		if 'file' not in item_tags:
			return
		file_name = self.files_tree.item(item, 'text')
		main_sel = self.tree.selection()
		if not main_sel:
			return
		h = self.get_handle_from_item(main_sel[0])
		if not h:
			return
		save_path = getattr(h.status(), "save_path", "")
		full_path = Path(save_path) / file_name
		if full_path.exists():
			try:
				open_path_in_os(full_path)
			except Exception as e:
				self.log(f"Open file error: {e}")
				messagebox.showerror("Error", str(e))
		else:
			messagebox.showinfo("Info", "File does not exist on disk.")

	def on_torrent_select(self, event):
		self.update_details()

	def show_context_menu(self, event):
		item = self.tree.identify_row(event.y)
		if item:
			self.tree.selection_set(item)
			menu = tk.Menu(self.root, tearoff=0)
			menu.add_command(label="Start", command=self.start_selected)
			menu.add_command(label="Pause", command=self.pause_selected)
			menu.add_command(label="Resume", command=self.force_resume_selected)
			menu.add_command(label="Stop", command=self.stop_selected)
			menu.add_separator()
			menu.add_command(label="Remove", command=self.remove_selected)
			menu.add_command(label="Remove + Data", command=self.remove_and_delete_selected)
			menu.add_command(label="Open Folder", command=self.open_folder)
			menu.add_command(label="Open File Location", command=self.open_file_location)
			menu.add_separator()
			menu.add_command(label="Force Recheck", command=self.force_recheck)
			menu.add_command(label="Force Reannounce", command=self.force_reannounce)
			menu.add_separator()
			menu.add_command(label="Copy Magnet Link", command=self.copy_magnet_link)
			menu.add_command(label="Save As", command=self.save_as_selected)
			menu.tk_popup(event.x_root, event.y_root)

	def on_torrent_double_click(self, event):
		self.open_folder()

	def show_settings(self):
		SettingsDialog(self.root, self.config, self.apply_settings)

	def apply_settings(self, new_config):
		self.config.update(new_config)
		self.save_config()

		session_set_max_connections(self.session, self.config.get('max_connections', 500))
		session_set_max_uploads(self.session, self.config.get('max_uploads', 50))
		session_set_download_rate_limit(self.session, self.config.get('global_dl_limit', 0))
		session_set_upload_rate_limit(self.session, self.config.get('global_ul_limit', 0))

		port_range = self.config.get('port_range', [6881, 6891])
		if session_listen_on(self.session, port_range[0], port_range[1]):
			self.log(f"Listen ports set to {port_range[0]}-{port_range[1]}")
		else:
			self.log("Failed to set listen ports")

		try:
			if self.config.get('enable_dht', True):
				session_enable_feature(self.session, 'dht', True)
			else:
				session_enable_feature(self.session, 'dht', False)
		except Exception:
			pass

		self.log("Settings applied")
		self.dl_limit_var.set(self.format_speed_limit_display(self.config.get('global_dl_limit', 0)))
		self.ul_limit_var.set(self.format_speed_limit_display(self.config.get('global_ul_limit', 0)))

	def show_documentation(self):
		try:
			webbrowser.open("https://www.libtorrent.org/documentation.html")
		except Exception:
			pass

	def show_about(self):
		about_text = f"""Advanced BitTorrent Client

Built with libtorrent: {getattr(lt, 'version', 'unknown')}
Python: {sys.version.split(' ')[0]}
Tkinter: {tk.TkVersion}
"""
		messagebox.showinfo("About", about_text)

	def clear_log(self):
		self.log_text.config(state=tk.NORMAL)
		self.log_text.delete(1.0, tk.END)
		self.log_text.config(state=tk.DISABLED)
		self.log("Log cleared")

	def save_log(self):
		file_path = filedialog.asksaveasfilename(
			defaultextension=".log",
			initialdir=str(platform_downloads_dir()),
			filetypes=[("Log files", "*.log"), ("Text files", "*.txt"), ("All files", "*.*")]
		)
		if file_path:
			try:
				with open(file_path, 'w', encoding='utf-8') as f:
					f.write(self.log_text.get(1.0, tk.END))
				self.log(f"Log saved to: {file_path}")
			except Exception as e:
				messagebox.showerror("Error", f"Failed to save log: {e}")

	def export_torrent_list(self):
		file_path = filedialog.asksaveasfilename(
			defaultextension=".csv",
			initialdir=str(platform_downloads_dir()),
			filetypes=[("CSV files", "*.csv"), ("All files", "*.*")]
		)
		if file_path:
			try:
				with open(file_path, 'w', newline='', encoding='utf-8') as f:
					writer = csv.writer(f)
					writer.writerow(["Name","Size","Progress","Status","Seeds","Peers","Down Speed","Up Speed","ETA","Ratio","Added On"])
					for item in self.tree.get_children():
						values = self.tree.item(item)['values']
						writer.writerow(values)
				self.log(f"Exported CSV: {file_path}")
			except Exception as e:
				messagebox.showerror("Error", f"Failed to export: {e}")

	def filter_torrents(self, event=None):
		search_term = (self.search_var.get() or "").lower()
		for item in self.tree.get_children():
			values = self.tree.item(item)['values']
			tags = self.tree.item(item)['tags']
			match = any(search_term in str(v).lower() for v in values)
			if not match and tags:
				if search_term in tags[0][:16].lower():
					match = True
			if match:
				self.tree.reattach(item, '', tk.END)
			else:
				self.tree.detach(item)

	def sort_treeview(self, col):
		numeric_cols = ['Size', 'Progress', 'Seeds', 'Peers', 'Down Speed', 'Up Speed', 'ETA', 'Ratio']
		rows = [(self.tree.set(k, col), k) for k in self.tree.get_children('')]
		def parse_human(value_str):
			if value_str in ("0 B", "0 B/s"):
				return 0
			try:
				sign = -1 if str(value_str).startswith('-') else 1
				s = str(value_str).lstrip('-').replace('/s', '')
				num_str, unit = s.split(' ')
				num = float(num_str)
				unit_map = {'B':1, 'KB':1024, 'MB':1024**2, 'GB':1024**3, 'TB':1024**4, 'PB':1024**5}
				return sign * num * unit_map.get(unit, 1)
			except Exception:
				return float('inf')
		def parse_eta(eta_str):
			if eta_str == "∞":
				return float('inf')
			total = 0
			for part in str(eta_str).split(' '):
				if part.endswith('d'): total += int(part[:-1]) * 86400
				elif part.endswith('h'): total += int(part[:-1]) * 3600
				elif part.endswith('m'): total += int(part[:-1]) * 60
				elif part.endswith('s'): total += int(part[:-1])
			return total
		try:
			if col in numeric_cols:
				if col in ['Size', 'Down Speed', 'Up Speed']:
					rows.sort(key=lambda t: parse_human(t[0]))
				elif col == 'Progress':
					rows.sort(key=lambda t: float(str(t[0]).rstrip('%') or 0.0))
				elif col == 'ETA':
					rows.sort(key=lambda t: parse_eta(t[0]))
				elif col == 'Ratio':
					rows.sort(key=lambda t: float(t[0] or 0.0))
				elif col in ['Seeds', 'Peers']:
					head = lambda s: (str(s).split(' ') or ['0'])[0]
					rows.sort(key=lambda t: int(head(t[0])) if head(t[0]).isdigit() else -1)
			else:
				rows.sort(key=lambda t: str(t[0]).lower())
		except Exception:
			rows.sort(key=lambda t: str(t[0]).lower())

		if hasattr(self, '_sort_column') and self._sort_column == col:
			if getattr(self, '_sort_reverse', False):
				rows.reverse()
				self._sort_reverse = False
			else:
				self._sort_reverse = True
		else:
			self._sort_column = col
			self._sort_reverse = False

		for idx, (_, k) in enumerate(rows):
			self.tree.move(k, '', idx)

	def load_config(self):
		config_file = "torrent_client_config.json"
		default_downloads = str(platform_downloads_dir())
		default_config = {
			'download_path': default_downloads,
			'completed_path': str(Path(default_downloads) / "Completed"),
			'max_connections': 500,
			'max_uploads': 50,
			'port_range': [6881, 6891],
			'enable_dht': True,
			'enable_lsd': True,
			'enable_upnp': True,
			'enable_natpmp': True,
			'global_dl_limit': 0,
			'global_ul_limit': 0,
			'last_opened_torrent_dir': default_downloads,
			'last_saved_torrent_dir': default_downloads,
			'log_level': 'INFO',
			'fast_download_default_enabled': True,
			'fast_download_default_connections': 5,
			'fast_download_sequential': True
		}
		try:
			if Path(config_file).exists():
				with open(config_file, 'r', encoding='utf-8') as f:
					loaded = json.load(f)
				return {**default_config, **loaded}
		except Exception as e:
			logger.warning(f"Config load error: {e}")
		return default_config

	def save_config(self):
		try:
			with open("torrent_client_config.json", 'w', encoding='utf-8') as f:
				json.dump(self.config, f, indent=2)
		except Exception as e:
			self.log(f"Config save error: {e}")

	def format_bytes(self, bytes_value):
		try:
			v = float(bytes_value)
		except Exception:
			v = 0.0
		if v == 0:
			return "0 B"
		units = ['B', 'KB', 'MB', 'GB', 'TB', 'PB']
		i = 0
		abs_v = abs(v)
		while abs_v >= 1024 and i < len(units) - 1:
			abs_v /= 1024.0
			i += 1
		sign = "-" if v < 0 else ""
		return f"{sign}{abs_v:.1f} {units[i]}"

	def format_speed(self, bytes_per_second):
		return f"{self.format_bytes(bytes_per_second)}/s"

	def format_time(self, seconds):
		s = int(seconds)
		if s <= 0:
			return "0s"
		d, rem = divmod(s, 86400)
		h, rem = divmod(rem, 3600)
		m, s = divmod(rem, 60)
		parts = []
		if d: parts.append(f"{d}d")
		if h: parts.append(f"{h}h")
		if m: parts.append(f"{m}m")
		if s or not parts: parts.append(f"{s}s")
		return " ".join(parts)

	def get_status_text(self, status):
		try:
			if getattr(status, "paused", False):
				return "Paused"
			st = getattr(status, "state", None)
			if st == lt.torrent_status.queued_for_checking:
				return "Queued"
			elif st == lt.torrent_status.checking_files:
				return "Checking"
			elif st == lt.torrent_status.downloading_metadata:
				return "Metadata"
			elif st == lt.torrent_status.downloading:
				return "Downloading"
			elif st == lt.torrent_status.finished:
				return "Finished"
			elif st == lt.torrent_status.seeding:
				return "Seeding"
			elif st == lt.torrent_status.allocating:
				return "Allocating"
			elif st == lt.torrent_status.checking_resume_data:
				return "Checking Resume"
			elif st == lt.torrent_status.error:
				try:
					if getattr(status, "errc", None):
						return f"Error: {status.errc.message()}"
				except Exception:
					pass
				try:
					if getattr(status, "error", None):
						return f"Error: {status.error}"
				except Exception:
					pass
				return "Error"
			else:
				return "Unknown"
		except Exception:
			return "Unknown"

	def on_closing(self):
		if messagebox.askokcancel("Quit", "Quit the client? Active downloads will pause."):
			self.running = False
			save_session_state_safe(self.session)
			self.save_config()
			try:
				for h in self.session.get_torrents():
					if h.is_valid():
						h.pause()
				if lt_has(self.session, 'pause'):
					self.session.pause()
				time.sleep(0.5)
			except Exception:
				pass
			self.session = None
			self.root.destroy()

	# Quick actions and helpers

	def show_speed_limits(self):
		SpeedLimitsDialog(self.root, self.session)

	def show_performance_graph(self):
		PerformanceGraphDialog(self.root, self.performance_stats)

	def show_download_history(self):
		DownloadHistoryDialog(self.root, self.download_history)

	def set_file_priority(self):
		item = self.get_single_selection()
		if not item:
			return
		handle = self.get_handle_from_item(item)
		if not handle:
			return
		try:
			if not getattr(handle.status(), "has_metadata", False):
				messagebox.showinfo("Info", "Metadata not available yet.")
				return
		except Exception:
			messagebox.showinfo("Info", "Metadata not available yet.")
			return
		FilePriorityDialog(self.root, handle)

	def expand_all_files(self):
		for item in self.files_tree.get_children():
			self.files_tree.item(item, open=True)
			self._expand_children(self.files_tree, item, True)

	def collapse_all_files(self):
		for item in self.files_tree.get_children():
			self.files_tree.item(item, open=False)
			self._expand_children(self.files_tree, item, False)

	def _expand_children(self, tree, item, open_state):
		for child in tree.get_children(item):
			tree.item(child, open=open_state)
			self._expand_children(tree, child, open_state)

	@staticmethod
	def get_priority_text(priority: int) -> str:
		mapping = {
			FILE_PRIORITY_SKIP: "Skip",
			FILE_PRIORITY_LOW: "Low",
			FILE_PRIORITY_TWO: "2",
			FILE_PRIORITY_THREE: "3",
			FILE_PRIORITY_FOUR: "Normal",
			FILE_PRIORITY_FIVE: "5",
			FILE_PRIORITY_SIX: "6",
			FILE_PRIORITY_MAX: "Max"
		}
		return mapping.get(int(priority), str(priority))

	def calculate_eta(self, status) -> str:
		try:
			total_wanted = float(getattr(status, 'total_wanted', 0))
			total_done = float(getattr(status, 'total_done', 0))
			remaining = max(0.0, total_wanted - total_done)
			rate = float(getattr(status, 'download_rate', 0))
			if rate <= 0.0 or remaining <= 0.0:
				return "∞"
			seconds = int(remaining / rate)
			return self.format_time(seconds)
		except Exception:
			return "∞"

	def log(self, msg: str):
		try:
			ts = datetime.now().strftime("%H:%M:%S")
			self.log_text.config(state=tk.NORMAL)
			self.log_text.insert(tk.END, f"[{ts}] {msg}\n")
			self.log_text.see(tk.END)
			self.log_text.config(state=tk.DISABLED)
		except Exception:
			logger.info(msg)

class FastDownloadDialog:
	def __init__(self, parent, config):
		self.result = {
			'enabled': config.get('fast_download_default_enabled', True),
			'connections': config.get('fast_download_default_connections', 5),
			'sequential': config.get('fast_download_sequential', True)
		}
		self.dialog = tk.Toplevel(parent)
		self.dialog.title("Fast Download")
		self.dialog.transient(parent)
		self.dialog.grab_set()
		self.dialog.resizable(False, False)
		self.dialog.update_idletasks()
		x = parent.winfo_x() + (parent.winfo_width() // 2) - (self.dialog.winfo_width() // 2)
		y = parent.winfo_y() + (parent.winfo_height() // 2) - (self.dialog.winfo_height() // 2)
		self.dialog.geometry(f"+{x}+{y}")

		main = ttk.Frame(self.dialog, padding="10 10 10 10")
		main.pack(fill=tk.BOTH, expand=True)

		self.enable_var = tk.BooleanVar(value=self.result['enabled'])
		ttk.Checkbutton(main, text="Enable Fast Download (multi-connection per torrent)", variable=self.enable_var).pack(anchor=tk.W, pady=(0, 8))

		row = ttk.Frame(main)
		row.pack(fill=tk.X, pady=(0, 8))
		ttk.Label(row, text="Connections:").pack(side=tk.LEFT)
		self.conn_var = tk.StringVar(value=str(self.result['connections']))
		ttk.Entry(row, textvariable=self.conn_var, width=6).pack(side=tk.LEFT, padx=(6, 0))
		ttk.Label(row, text="(suggest 5–10)").pack(side=tk.LEFT, padx=(6, 0))

		self.seq_var = tk.BooleanVar(value=self.result['sequential'])
		ttk.Checkbutton(main, text="Sequential download (improves playback start, stable speed)", variable=self.seq_var).pack(anchor=tk.W)

		btns = ttk.Frame(main)
		btns.pack(fill=tk.X, pady=(10, 0))
		ttk.Button(btns, text="Cancel", command=self.cancel).pack(side=tk.RIGHT)
		ttk.Button(btns, text="OK", command=self.ok).pack(side=tk.RIGHT, padx=(0, 6))

		self.dialog.bind('<Return>', lambda e: self.ok())
		self.dialog.wait_window()

	def ok(self):
		try:
			conns = max(1, min(50, int(float(self.conn_var.get()))))
		except Exception:
			conns = 5
		self.result = {
			'enabled': bool(self.enable_var.get()),
			'connections': conns,
			'sequential': bool(self.seq_var.get())
		}
		self.dialog.destroy()

	def cancel(self):
		# Keep defaults as "disabled" so it's safe
		self.result = {'enabled': False, 'connections': 5, 'sequential': True}
		self.dialog.destroy()

class MagnetDialog:
	def __init__(self, parent, default_path):
		self.result = None
		self.dialog = tk.Toplevel(parent)
		self.dialog.title("Add Magnet Link")
		self.dialog.transient(parent)
		self.dialog.grab_set()
		self.dialog.update_idletasks()
		x = parent.winfo_x() + (parent.winfo_width() // 2) - (self.dialog.winfo_width() // 2)
		y = parent.winfo_y() + (parent.winfo_height() // 2) - (self.dialog.winfo_height() // 2)
		self.dialog.geometry(f"+{x}+{y}")
		self.dialog.resizable(False, False)

		main = ttk.Frame(self.dialog, padding="10 10 10 10")
		main.pack(fill=tk.BOTH, expand=True)

		ttk.Label(main, text="Magnet URI:").pack(anchor=tk.W, pady=(0, 5))
		self.magnet_var = tk.StringVar()
		entry = ttk.Entry(main, textvariable=self.magnet_var, width=80)
		entry.pack(fill=tk.X, pady=(0, 10))
		entry.focus()

		ttk.Label(main, text="Download Path:").pack(anchor=tk.W, pady=(0, 5))
		path_frame = ttk.Frame(main)
		path_frame.pack(fill=tk.X, pady=(0, 10))
		self.path_var = tk.StringVar(value=default_path)
		ttk.Entry(path_frame, textvariable=self.path_var).pack(side=tk.LEFT, fill=tk.X, expand=True)
		ttk.Button(path_frame, text="Browse...", command=self.browse_path).pack(side=tk.RIGHT, padx=(5, 0))

		btns = ttk.Frame(main)
		btns.pack(fill=tk.X, pady=(10, 0))
		ttk.Button(btns, text="Cancel", command=self.cancel).pack(side=tk.RIGHT)
		ttk.Button(btns, text="Add", command=self.add_magnet).pack(side=tk.RIGHT, padx=(0, 5))

		self.dialog.bind('<Return>', lambda e: self.add_magnet())
		self.dialog.wait_window()

	def browse_path(self):
		path = filedialog.askdirectory(initialdir=self.path_var.get(), parent=self.dialog)
		if path:
			self.path_var.set(path)

	def add_magnet(self):
		magnet_uri = (self.magnet_var.get() or "").strip()
		if magnet_uri.startswith("magnet:"):
			self.result = (magnet_uri, self.path_var.get())
			self.dialog.destroy()
		else:
			messagebox.showerror("Invalid Magnet", "Enter a valid magnet URI.", parent=self.dialog)

	def cancel(self):
		self.dialog.destroy()

class MultiMagnetDialog:
	def __init__(self, parent, default_path):
		self.result = None
		self.dialog = tk.Toplevel(parent)
		self.dialog.title("Add Multiple Magnets")
		self.dialog.transient(parent)
		self.dialog.grab_set()
		self.dialog.geometry("680x400")
		self.dialog.update_idletasks()
		x = parent.winfo_x() + (parent.winfo_width() // 2) - (self.dialog.winfo_width() // 2)
		y = parent.winfo_y() + (parent.winfo_height() // 2) - (self.dialog.winfo_height() // 2)
		self.dialog.geometry(f"+{x}+{y}")
		self.dialog.resizable(True, True)

		main = ttk.Frame(self.dialog, padding="10 10 10 10")
		main.pack(fill=tk.BOTH, expand=True)

		ttk.Label(main, text="Paste one magnet URI per line:").pack(anchor=tk.W, pady=(0, 5))
		self.text = scrolledtext.ScrolledText(main, wrap=tk.WORD, height=12)
		self.text.pack(fill=tk.BOTH, expand=True)

		ttk.Label(main, text="Download Path:").pack(anchor=tk.W, pady=(10, 5))
		path_frame = ttk.Frame(main)
		path_frame.pack(fill=tk.X)
		self.path_var = tk.StringVar(value=default_path)
		ttk.Entry(path_frame, textvariable=self.path_var).pack(side=tk.LEFT, fill=tk.X, expand=True)
		ttk.Button(path_frame, text="Browse...", command=self.browse_path).pack(side=tk.RIGHT, padx=(5, 0))

		btns = ttk.Frame(main, padding="0 10 10 0")
		btns.pack(fill=tk.X, pady=(10, 0))
		ttk.Button(btns, text="Cancel", command=self.cancel).pack(side=tk.RIGHT)
		ttk.Button(btns, text="Add All", command=self.add_all).pack(side=tk.RIGHT, padx=(0, 5))

		self.dialog.wait_window()

	def browse_path(self):
		path = filedialog.askdirectory(initialdir=self.path_var.get(), parent=self.dialog)
		if path:
			self.path_var.set(path)

	def add_all(self):
		raw = self.text.get(1.0, tk.END).strip()
		lines = [ln.strip() for ln in raw.splitlines() if ln.strip()]
		magnets = [ln for ln in lines if ln.startswith("magnet:")]
		if not magnets:
			messagebox.showerror("Invalid Input", "Paste at least one magnet URI.", parent=self.dialog)
			return
		self.result = (self.path_var.get(), magnets)
		self.dialog.destroy()

	def cancel(self):
		self.dialog.destroy()

class UrlDialog:
	def __init__(self, parent, default_path):
		self.result = None
		self.dialog = tk.Toplevel(parent)
		self.dialog.title("Add Torrent from URL")
		self.dialog.transient(parent)
		self.dialog.grab_set()
		self.dialog.update_idletasks()
		x = parent.winfo_x() + (parent.winfo_width() // 2) - (self.dialog.winfo_width() // 2)
		y = parent.winfo_y() + (parent.winfo_height() // 2) - (self.dialog.winfo_height() // 2)
		self.dialog.geometry(f"+{x}+{y}")
		self.dialog.resizable(False, False)

		main = ttk.Frame(self.dialog, padding="10 10 10 10")
		main.pack(fill=tk.BOTH, expand=True)

		ttk.Label(main, text="Torrent URL:").pack(anchor=tk.W, pady=(0, 5))
		self.url_var = tk.StringVar()
		entry = ttk.Entry(main, textvariable=self.url_var, width=80)
		entry.pack(fill=tk.X, pady=(0, 10))
		entry.focus()

		ttk.Label(main, text="Download Path:").pack(anchor=tk.W, pady=(0, 5))
		path_frame = ttk.Frame(main)
		path_frame.pack(fill=tk.X, pady=(0, 10))
		self.path_var = tk.StringVar(value=default_path)
		ttk.Entry(path_frame, textvariable=self.path_var).pack(side=tk.LEFT, fill=tk.X, expand=True)
		ttk.Button(path_frame, text="Browse...", command=self.browse_path).pack(side=tk.RIGHT, padx=(5, 0))

		btns = ttk.Frame(self.dialog, padding="0 10 10 10")
		btns.pack(fill=tk.X)
		ttk.Button(btns, text="Cancel", command=self.cancel).pack(side=tk.RIGHT)
		ttk.Button(btns, text="Add", command=self.add_url).pack(side=tk.RIGHT, padx=(0, 5))

		self.dialog.bind('<Return>', lambda e: self.add_url())
		self.dialog.wait_window()

	def browse_path(self):
		path = filedialog.askdirectory(initialdir=self.path_var.get(), parent=self.dialog)
		if path:
			self.path_var.set(path)

	def add_url(self):
		url = (self.url_var.get() or "").strip().lower()
		if url.startswith("http://") or url.startswith("https://"):
			self.result = (self.url_var.get().strip(), self.path_var.get())
			self.dialog.destroy()
		else:
			messagebox.showerror("Invalid URL", "Enter a valid HTTP or HTTPS URL.", parent=self.dialog)

	def cancel(self):
		self.dialog.destroy()

class SettingsDialog:
	def __init__(self, parent, config, apply_callback):
		self.config = config.copy()
		self.apply_callback = apply_callback

		self.dialog = tk.Toplevel(parent)
		self.dialog.title("Settings")
		self.dialog.transient(parent)
		self.dialog.grab_set()

		self.dialog.update_idletasks()
		x = parent.winfo_x() + (parent.winfo_width() // 2) - (self.dialog.winfo_width() // 2)
		y = parent.winfo_y() + (parent.winfo_height() // 2) - (self.dialog.winfo_height() // 2)
		self.dialog.geometry(f"+{x}+{y}")
		self.dialog.resizable(False, False)

		main = ttk.Frame(self.dialog, padding="10 10 10 10")
		main.pack(fill=tk.BOTH, expand=True)

		notebook = ttk.Notebook(main)
		notebook.pack(fill=tk.BOTH, expand=True)

		general_frame = ttk.Frame(notebook, padding="5 5 5 5")
		notebook.add(general_frame, text="General")
		self.create_general_settings(general_frame)

		connection_frame = ttk.Frame(notebook, padding="5 5 5 5")
		notebook.add(connection_frame, text="Connection")
		self.create_connection_settings(connection_frame)

		speed_limits_frame = ttk.Frame(notebook, padding="5 5 5 5")
		notebook.add(speed_limits_frame, text="Speed Limits")
		self.create_speed_limits_settings(speed_limits_frame)

		button_frame = ttk.Frame(self.dialog, padding="0 10 10 10")
		button_frame.pack(fill=tk.X)
		ttk.Button(button_frame, text="Cancel", command=self.cancel).pack(side=tk.RIGHT)
		ttk.Button(button_frame, text="Apply", command=self.apply).pack(side=tk.RIGHT, padx=(0, 5))

	def create_general_settings(self, parent):
		ttk.Label(parent, text="Default Download Path:").pack(anchor=tk.W, pady=(0, 5))
		path_frame = ttk.Frame(parent)
		path_frame.pack(fill=tk.X, pady=(0, 10))
		self.download_path_var = tk.StringVar(value=self.config.get('download_path', str(platform_downloads_dir())))
		ttk.Entry(path_frame, textvariable=self.download_path_var).pack(side=tk.LEFT, fill=tk.X, expand=True)
		ttk.Button(path_frame, text="Browse...", command=self.browse_download_path).pack(side=tk.RIGHT, padx=(5, 0))

		ttk.Label(parent, text="Completed Path:").pack(anchor=tk.W, pady=(0, 5))
		comp_frame = ttk.Frame(parent)
		comp_frame.pack(fill=tk.X, pady=(0, 10))
		self.completed_path_var = tk.StringVar(value=self.config.get('completed_path', str(platform_downloads_dir() / "Completed")))
		ttk.Entry(comp_frame, textvariable=self.completed_path_var).pack(side=tk.LEFT, fill=tk.X, expand=True)
		ttk.Button(comp_frame, text="Browse...", command=self.browse_completed_path).pack(side=tk.RIGHT, padx=(5, 0))

		ttk.Label(parent, text="Fast Download default:").pack(anchor=tk.W, pady=(0, 5))
		fd_frame = ttk.Frame(parent)
		fd_frame.pack(fill=tk.X, pady=(0, 10))
		self.fd_enabled_var = tk.BooleanVar(value=self.config.get('fast_download_default_enabled', True))
		ttk.Checkbutton(fd_frame, text="Enable by default", variable=self.fd_enabled_var).pack(anchor=tk.W)
		fd2 = ttk.Frame(parent)
		fd2.pack(fill=tk.X, pady=(0, 10))
		ttk.Label(fd2, text="Connections:").pack(side=tk.LEFT)
		self.fd_conn_var = tk.StringVar(value=str(self.config.get('fast_download_default_connections', 5)))
		ttk.Entry(fd2, textvariable=self.fd_conn_var, width=6).pack(side=tk.LEFT, padx=(6, 0))
		self.fd_seq_var = tk.BooleanVar(value=self.config.get('fast_download_sequential', True))
		ttk.Checkbutton(parent, text="Sequential download default", variable=self.fd_seq_var).pack(anchor=tk.W)

	def create_connection_settings(self, parent):
		ttk.Label(parent, text="Maximum Connections:").pack(anchor=tk.W, pady=(0, 5))
		self.max_connections_var = tk.StringVar(value=str(self.config.get('max_connections', 500)))
		ttk.Entry(parent, textvariable=self.max_connections_var).pack(anchor=tk.W, fill=tk.X, pady=(0, 10))

		ttk.Label(parent, text="Maximum Uploads:").pack(anchor=tk.W, pady=(0, 5))
		self.max_uploads_var = tk.StringVar(value=str(self.config.get('max_uploads', 50)))
		ttk.Entry(parent, textvariable=self.max_uploads_var).pack(anchor=tk.W, fill=tk.X, pady=(0, 10))

		ttk.Label(parent, text="Listen Port Range:").pack(anchor=tk.W, pady=(0, 5))
		port_frame = ttk.Frame(parent)
		port_frame.pack(anchor=tk.W, fill=tk.X, pady=(0, 10))
		port_range = self.config.get('port_range', [6881, 6891])
		self.port_start_var = tk.StringVar(value=str(port_range[0]))
		self.port_end_var = tk.StringVar(value=str(port_range[1]))
		ttk.Entry(port_frame, textvariable=self.port_start_var, width=10).pack(side=tk.LEFT)
		ttk.Label(port_frame, text=" to ").pack(side=tk.LEFT)
		ttk.Entry(port_frame, textvariable=self.port_end_var, width=10).pack(side=tk.LEFT)

	def create_speed_limits_settings(self, parent):
		ttk.Label(parent, text="Global Download Limit (KB/s): 0 for unlimited").pack(anchor=tk.W, pady=(0, 5))
		self.global_dl_limit_var = tk.StringVar(value=str(int(self.config.get('global_dl_limit', 0)) // 1024))
		ttk.Entry(parent, textvariable=self.global_dl_limit_var).pack(anchor=tk.W, fill=tk.X, pady=(0, 10))

		ttk.Label(parent, text="Global Upload Limit (KB/s): 0 for unlimited").pack(anchor=tk.W, pady=(0, 5))
		self.global_ul_limit_var = tk.StringVar(value=str(int(self.config.get('global_ul_limit', 0)) // 1024))
		ttk.Entry(parent, textvariable=self.global_ul_limit_var).pack(anchor=tk.W, fill=tk.X, pady=(0, 10))

	def browse_download_path(self):
		path = filedialog.askdirectory(initialdir=self.download_path_var.get(), parent=self.dialog)
		if path:
			self.download_path_var.set(path)

	def browse_completed_path(self):
		path = filedialog.askdirectory(initialdir=self.completed_path_var.get(), parent=self.dialog)
		if path:
			self.completed_path_var.set(path)

	def apply(self):
		try:
			dl_limit_val = int(float(self.global_dl_limit_var.get()) * 1024)
			ul_limit_val = int(float(self.global_ul_limit_var.get()) * 1024)
			port_start = int(self.port_start_var.get())
			port_end = int(self.port_end_var.get())
			if not (1 <= port_start <= 65535 and 1 <= port_end <= 65535 and port_start <= port_end):
				messagebox.showerror("Invalid Input", "Port range must be 1..65535 and start <= end.", parent=self.dialog)
				return
			new_config = {
				'download_path': self.download_path_var.get(),
				'completed_path': self.completed_path_var.get(),
				'max_connections': int(self.max_connections_var.get()),
				'max_uploads': int(self.max_uploads_var.get()),
				'port_range': [port_start, port_end],
				'enable_dht': True,
				'enable_lsd': True,
				'enable_upnp': True,
				'enable_natpmp': True,
				'global_dl_limit': max(0, dl_limit_val),
				'global_ul_limit': max(0, ul_limit_val),
				'fast_download_default_enabled': bool(self.fd_enabled_var.get()),
				'fast_download_default_connections': max(1, min(50, int(float(self.fd_conn_var.get()) if self.fd_conn_var.get() else 5))),
				'fast_download_sequential': bool(self.fd_seq_var.get())
			}
			self.apply_callback(new_config)
			self.dialog.destroy()
		except Exception:
			messagebox.showerror("Invalid Input", "Please enter valid numeric values.", parent=self.dialog)

	def cancel(self):
		self.dialog.destroy()

class FilePriorityDialog:
	def __init__(self, parent, handle):
		self.handle = handle
		self.dialog = tk.Toplevel(parent)
		self.dialog.title(f"Set File Priorities: {handle.name()[:30]}...")
		self.dialog.transient(parent)
		self.dialog.grab_set()
		self.dialog.update_idletasks()
		x = parent.winfo_x() + (parent.winfo_width() // 2) - (self.dialog.winfo_width() // 2)
		y = parent.winfo_y() + (parent.winfo_height() // 2) - (self.dialog.winfo_height() // 2)
		self.dialog.geometry(f"+{x}+{y}")
		self.dialog.resizable(False, False)

		main = ttk.Frame(self.dialog, padding="10 10 10 10")
		main.pack(fill=tk.BOTH, expand=True)

		ttk.Label(main, text="Select files and set their priorities:").pack(anchor=tk.W, pady=(0, 5))

		tree_frame = ttk.Frame(main)
		tree_frame.pack(fill=tk.BOTH, expand=True, pady=(0, 5))

		columns = ('File', 'Size', 'Priority')
		self.tree = ttk.Treeview(tree_frame, columns=columns, show='tree headings', selectmode='extended')
		self.tree.column('#0', width=280, stretch=tk.NO)
		self.tree.heading('#0', text='File')
		for col in columns[1:]:
			self.tree.heading(col, text=col)
			self.tree.column(col, width=120)

		scroll = ttk.Scrollbar(tree_frame, orient=tk.VERTICAL, command=self.tree.yview)
		self.tree.configure(yscrollcommand=scroll.set)
		self.tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
		scroll.pack(side=tk.RIGHT, fill=tk.Y)

		if getattr(self.handle.status(), "has_metadata", False):
			ti = self.handle.get_torrent_info()
			files = ti.files()
			tree_items = {}

			def insert_recursive(path_parts, parent_id, file_index=-1):
				if not path_parts:
					return
				part = path_parts[0]
				current_id = f"{parent_id}/{part}" if parent_id else part
				if current_id not in tree_items:
					if len(path_parts) == 1 and file_index != -1:
						size = files.file_size(file_index)
						priority = self.safe_get_file_priority(self.handle, file_index)
						item_id = self.tree.insert(parent_id, tk.END, text=part, values=(self.format_bytes(size), self.get_priority_text(priority)), tags=(str(file_index), 'file'))
						tree_items[current_id] = item_id
					else:
						item_id = self.tree.insert(parent_id, tk.END, text=part, open=True, values=("", ""))
						tree_items[current_id] = item_id
				if len(path_parts) > 1:
					insert_recursive(path_parts[1:], tree_items[current_id], file_index)

			for i in range(ti.num_files()):
				file_path = str(Path(files.file_path(i)))
				insert_recursive(file_path.split(os.sep), '', i)
		else:
			ttk.Label(tree_frame, text="Torrent metadata not available.").pack(pady=20)

		priority_frame = ttk.Frame(main)
		priority_frame.pack(fill=tk.X, pady=(5, 10))
		ttk.Label(priority_frame, text="Set Priority for Selected:").pack(side=tk.LEFT)

		self.priority_var = tk.IntVar(value=FILE_PRIORITY_NORMAL)
		priority_values = [FILE_PRIORITY_SKIP, FILE_PRIORITY_LOW, FILE_PRIORITY_TWO, FILE_PRIORITY_THREE, FILE_PRIORITY_FOUR, FILE_PRIORITY_FIVE, FILE_PRIORITY_SIX, FILE_PRIORITY_MAX]
		priority_combo = ttk.Combobox(priority_frame, textvariable=self.priority_var, state='readonly', values=priority_values)
		priority_combo.set(FILE_PRIORITY_NORMAL)
		priority_combo.pack(side=tk.LEFT, padx=(5, 0))
		ttk.Button(priority_frame, text="Apply", command=self.apply_priority).pack(side=tk.LEFT, padx=(5, 0))

		btns = ttk.Frame(self.dialog, padding="0 10 10 10")
		btns.pack(fill=tk.X)
		ttk.Button(btns, text="Close", command=self.close).pack(side=tk.RIGHT)

	def safe_get_file_priority(self, handle, file_index):
		try:
			return int(handle.file_priority(file_index))
		except Exception:
			return FILE_PRIORITY_NORMAL

	def format_bytes(self, b):
		if not b:
			return "0 B"
		return TorrentClient.format_bytes(self=None, bytes_value=b)

	def get_priority_text(self, pr):
		return TorrentClient.get_priority_text(self=None, priority=pr)

	def apply_priority(self):
		selection = self.tree.selection()
		if not selection:
			messagebox.showinfo("Info", "Select one or more files.", parent=self.dialog)
			return
		pr = int(self.priority_var.get())
		applied = 0
		for item in selection:
			tags = self.tree.item(item, 'tags')
			if 'file' in tags:
				idx = int(tags[0])
				try:
					self.handle.file_priority(idx, pr)
					self.tree.set(item, 'Priority', self.get_priority_text(pr))
					applied += 1
				except Exception:
					continue
		messagebox.showinfo("File Priorities", f"Applied priority to {applied} files.", parent=self.dialog)

	def close(self):
		self.dialog.destroy()

class PerformanceGraphDialog:
	def __init__(self, parent, performance_stats):
		self.performance_stats = performance_stats
		self.dialog = tk.Toplevel(parent)
		self.dialog.title("Performance Graph")
		self.dialog.geometry("880x620")
		self.dialog.transient(parent)
		self.dialog.grab_set()
		self.dialog.update_idletasks()
		x = parent.winfo_x() + (parent.winfo_width() // 2) - (self.dialog.winfo_width() // 2)
		y = parent.winfo_y() + (parent.winfo_height() // 2) - (self.dialog.winfo_height() // 2)
		self.dialog.geometry(f"+{x}+{y}")

		main = ttk.Frame(self.dialog, padding="10 10 10 10")
		main.pack(fill=tk.BOTH, expand=True)

		self.canvas = tk.Canvas(main, bg="white", highlightbackground="gray", highlightthickness=1)
		self.canvas.pack(fill=tk.BOTH, expand=True)

		summary_frame = ttk.Frame(main)
		summary_frame.pack(fill=tk.X, pady=(10, 0))
		self.summary_label = ttk.Label(summary_frame, text="", font=('Arial', 10))
		self.summary_label.pack(anchor=tk.W)

		btns = ttk.Frame(self.dialog, padding="0 10 10 10")
		btns.pack(fill=tk.X)
		ttk.Button(btns, text="Close", command=self.dialog.destroy).pack(side=tk.RIGHT)

		self.canvas.bind('<Configure>', self.on_canvas_resize)
		self.dialog.after(100, self.draw_placeholder_graph)
		self.dialog.after(100, self.update_summary_label)

	def on_canvas_resize(self, event):
		self.draw_placeholder_graph()

	def draw_placeholder_graph(self):
		self.canvas.delete("all")
		width = self.canvas.winfo_width()
		height = self.canvas.winfo_height()
		if width <= 100 or height <= 100:
			return

		padding = 40
		x_axis_start = padding
		x_axis_end = width - padding
		y_axis_start = height - padding
		y_axis_end = padding

		self.canvas.create_line(x_axis_start, y_axis_start, x_axis_end, y_axis_start, fill="gray", arrow=tk.LAST, width=1)
		self.canvas.create_line(x_axis_start, y_axis_start, y_axis_start, y_axis_end, fill="gray", width=1)

		self.canvas.create_text(width / 2, height - padding / 2, text="Time (most recent on right)", fill="gray")
		self.canvas.create_text(padding / 2, height / 2, text="Value", fill="gray", angle=90)
		self.canvas.create_text(width / 2, padding / 2, text="Performance Over Time", font=('Arial', 12, 'bold'))

		dl_speeds = list(self.performance_stats['download_speeds'])
		ul_speeds = list(self.performance_stats['upload_speeds'])
		mem_usage = list(self.performance_stats['memory_usage'])
		cpu_usage = list(self.performance_stats['cpu_usage'])

		if not dl_speeds and not ul_speeds and not mem_usage and not cpu_usage:
			self.canvas.create_text(width / 2, height / 2, text="No performance data available yet.", fill="black")
			return

		max_speed = max(max(dl_speeds) if dl_speeds else 0, max(ul_speeds) if ul_speeds else 0)
		max_mem = max(mem_usage) if mem_usage else 0
		max_cpu = max(cpu_usage) if cpu_usage else 0

		scale_factor_cpu = 1024 * 1024
		max_y = max(max_speed, max_mem, max_cpu * scale_factor_cpu)
		max_y = max_y if max_y > 0 else 1

		data_len = max(len(dl_speeds), len(ul_speeds), len(mem_usage), len(cpu_usage))
		if data_len == 0:
			self.canvas.create_text(width / 2, height / 2, text="No performance data available yet.", fill="black")
			return

		x_interval = (x_axis_end - x_axis_start) / max(data_len - 1, 1)
		y_scale = (y_axis_start - y_axis_end) / max_y

		def plot_line(data, color, label_text, label_offset):
			if not data:
				return
			points = []
			for i, raw in enumerate(data):
				x = x_axis_start + i * x_interval
				y_raw = raw * (scale_factor_cpu if label_text == "CPU %" else 1)
				y = y_axis_start - (y_raw * y_scale)
				points.extend([x, y])
			if len(points) > 2:
				self.canvas.create_line(points, fill=color, smooth=True, width=2)
				self.canvas.create_text(x_axis_end + 5, y_axis_end + label_offset, text=label_text, fill=color, anchor=tk.W)

		plot_line(dl_speeds, "blue", "DL (B/s)", 0)
		plot_line(ul_speeds, "green", "UL (B/s)", 20)
		plot_line(mem_usage, "red", "RSS (B)", 40)
		plot_line(cpu_usage, "purple", "CPU %", 60)

		if self.dialog.winfo_exists():
			self.dialog.after(3000, self.draw_placeholder_graph)

	def update_summary_label(self):
		if not self.dialog.winfo_exists():
			return

		def avg(arr):
			return sum(arr) / len(arr) if arr else 0.0

		dl_speeds = list(self.performance_stats['download_speeds'])
		ul_speeds = list(self.performance_stats['upload_speeds'])
		mem_usage = list(self.performance_stats['memory_usage'])
		cpu_usage = list(self.performance_stats['cpu_usage'])

		text = "Current Performance Summary:\n"
		if dl_speeds:
			text += f"Avg DL (last {len(dl_speeds)}s): {self.format_speed(avg(dl_speeds))}\n"
		if ul_speeds:
			text += f"Avg UL (last {len(ul_speeds)}s): {self.format_speed(avg(ul_speeds))}\n"
		if mem_usage:
			text += f"Avg RSS (last {len(mem_usage)}s): {self.format_bytes(avg(mem_usage))}\n"
		if cpu_usage:
			text += f"Avg CPU (last {len(cpu_usage)}s): {avg(cpu_usage):.1f}%\n"

		self.summary_label.config(text=text)
		if self.dialog.winfo_exists():
			self.dialog.after(1000, self.update_summary_label)

	def format_speed(self, bps):
		if not bps:
			return "0 B/s"
		units = ['B/s', 'KB/s', 'MB/s', 'GB/s', 'TB/s']
		i = 0
		v = float(bps)
		while v >= 1024.0 and i < len(units) - 1:
			v /= 1024.0
			i += 1
		return f"{v:.1f} {units[i]}"

	def format_bytes(self, b):
		if not b:
			return "0 B"
		units = ['B', 'KB', 'MB', 'GB', 'TB', 'PB']
		i = 0
		v = float(b)
		while v >= 1024.0 and i < len(units) - 1:
			v /= 1024.0
			i += 1
		return f"{v:.1f} {units[i]}"

class DownloadHistoryDialog:
	def __init__(self, parent, download_history):
		self.download_history = download_history
		self.dialog = tk.Toplevel(parent)
		self.dialog.title("Download History")
		self.dialog.geometry("940x440")
		self.dialog.transient(parent)
		self.dialog.grab_set()
		self.dialog.update_idletasks()
		x = parent.winfo_x() + (parent.winfo_width() // 2) - (self.dialog.winfo_width() // 2)
		y = parent.winfo_y() + (parent.winfo_height() // 2) - (self.dialog.winfo_height() // 2)
		self.dialog.geometry(f"+{x}+{y}")

		main = ttk.Frame(self.dialog, padding="10 10 10 10")
		main.pack(fill=tk.BOTH, expand=True)

		tree_frame = ttk.Frame(main)
		tree_frame.pack(fill=tk.BOTH, expand=True)

		columns = ('Name', 'Hash', 'Added On', 'Source', 'Save Path')
		self.tree = ttk.Treeview(tree_frame, columns=columns, show='headings')
		for col in columns:
			self.tree.heading(col, text=col)
			self.tree.column(col, width=180)

		scroll = ttk.Scrollbar(tree_frame, orient=tk.VERTICAL, command=self.tree.yview)
		self.tree.configure(yscrollcommand=scroll.set)
		self.tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
		scroll.pack(side=tk.RIGHT, fill=tk.Y)

		for item in reversed(self.download_history):
			self.tree.insert('', tk.END, values=(
				item.get('name', 'Unknown'),
				(item.get('hash', '')[:10] + "...") if item.get('hash') else "",
				item.get('added_time').strftime("%Y-%m-%d %H:%M") if item.get('added_time') else "",
				item.get('source', 'N/A'),
				item.get('save_path', 'N/A')
			))

		btns = ttk.Frame(self.dialog, padding="0 10 10 10")
		btns.pack(fill=tk.X)
		ttk.Button(btns, text="Close", command=self.dialog.destroy).pack(side=tk.RIGHT)

class SpeedLimitsDialog:
	def __init__(self, parent, session):
		self.session = session
		self.dialog = tk.Toplevel(parent)
		self.dialog.title("Global Speed Limits")
		self.dialog.transient(parent)
		self.dialog.grab_set()
		self.dialog.update_idletasks()
		x = parent.winfo_x() + (parent.winfo_width() // 2) - (self.dialog.winfo_width() // 2)
		y = parent.winfo_y() + (parent.winfo_height() // 2) - (self.dialog.winfo_height() // 2)
		self.dialog.geometry(f"+{x}+{y}")
		self.dialog.resizable(False, False)

		main = ttk.Frame(self.dialog, padding="10 10 10 10")
		main.pack(fill=tk.BOTH, expand=True)

		try:
			cur_dl = self.session.download_rate_limit() // 1024 if lt_has(self.session, 'download_rate_limit') else 0
		except Exception:
			cur_dl = 0
		try:
			cur_ul = self.session.upload_rate_limit() // 1024 if lt_has(self.session, 'upload_rate_limit') else 0
		except Exception:
			cur_ul = 0

		ttk.Label(main, text="Global Download Limit (KB/s, 0=unlimited):").pack(anchor=tk.W, pady=(0, 5))
		self.dl_limit_var = tk.StringVar(value=str(cur_dl))
		ttk.Entry(main, textvariable=self.dl_limit_var).pack(fill=tk.X, pady=(0, 10))

		ttk.Label(main, text="Global Upload Limit (KB/s, 0=unlimited):").pack(anchor=tk.W, pady=(0, 5))
		self.ul_limit_var = tk.StringVar(value=str(cur_ul))
		ttk.Entry(main, textvariable=self.ul_limit_var).pack(fill=tk.X, pady=(0, 10))

		btns = ttk.Frame(self.dialog, padding="0 10 10 10")
		btns.pack(fill=tk.X)
		ttk.Button(btns, text="Cancel", command=self.cancel).pack(side=tk.RIGHT)
		ttk.Button(btns, text="Apply", command=self.apply).pack(side=tk.RIGHT, padx=(0, 5))

	def apply(self):
		try:
			dl_limit = int(float(self.dl_limit_var.get()) * 1024)
			ul_limit = int(float(self.ul_limit_var.get()) * 1024)
			if dl_limit < 0 or ul_limit < 0:
				messagebox.showerror("Error", "Limits cannot be negative.", parent=self.dialog)
				return
			if lt_has(self.session, 'set_download_rate_limit'):
				self.session.set_download_rate_limit(max(0, dl_limit))
			if lt_has(self.session, 'set_upload_rate_limit'):
				self.session.set_upload_rate_limit(max(0, ul_limit))
			self.dialog.destroy()
		except Exception:
			messagebox.showerror("Error", "Please enter valid numeric values.", parent=self.dialog)

	def cancel(self):
		self.dialog.destroy()

def main():
	try:
		app = TorrentClient()
		app.root.mainloop()
	except KeyboardInterrupt:
		print("\nShutting down...")
	except Exception as e:
		print(f"Error starting application: {e}")

if __name__ == "__main__":
	main()
