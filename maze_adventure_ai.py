"""Maze Adventure AI - a Tkinter human vs AI maze game.

    * dark themed window (#0d1117) with fullscreen support
    * startup splash, then nine screens: Home, Challenge Selection,
      Custom Challenge, Gameplay, Challenge Complete, Player Complete,
      Results, Instructions, AI Complete
    * four challenge tiers with unlock progression and optional save file
    * DFS recursive-backtracking maze generation (perfect mazes)
    * BFS goal placement: the corridor farthest from the start
    * A* pathfinding, animated solver and smart hints
    * pause/resume (button or P), smart restart with same-maze replay
    * live timer, player path replay and yellow optimal-path comparison
    * packaged as a windowed MazeAdventureAI.exe via build.bat

Run:
    python maze_adventure_ai.py              # fullscreen (default)
    python maze_adventure_ai.py --windowed   # 1280x800 window, handy while developing
"""

from __future__ import annotations

import heapq
import json
import os
import random
import sys
import time
import tkinter as tk
from collections import deque
from tkinter import messagebox

# ---------------------------------------------------------------------------
# Theme
# ---------------------------------------------------------------------------
COLOR_BG = "#0d1117"          # window / screen background
COLOR_PANEL = "#161b22"       # cards and panels
COLOR_PANEL_ALT = "#1c2128"   # secondary buttons
COLOR_BORDER = "#30363d"
COLOR_TEXT = "#c9d1d9"
COLOR_TEXT_STRONG = "#e6edf3"
COLOR_MUTED = "#8b949e"
COLOR_ACCENT = "#22d3ee"
COLOR_ACCENT_HOVER = "#67e8f9"
COLOR_DANGER = "#f85149"
COLOR_DANGER_HOVER = "#ff7b72"
COLOR_SUCCESS = "#3fb950"

# Maze colours (black walls, white corridors).
COLOR_WALL = "#000000"
COLOR_PATH = "#ffffff"
COLOR_START = "#22d3ee"   # start cell marker (1, 1)
COLOR_PLAYER = "#1f6feb"  # the player square
COLOR_PLAYER_GLOW = "#0b4a8f"  # dark blue halo around the player
COLOR_HINT = "#f0883e"    # hint highlights (orange)
COLOR_AI = "#e3b341"      # AI solver path (yellow)
COLOR_REPLAY = "#7ee787"  # results replay path (light green)
COLOR_GOAL_GLOW = "#6e1d1d"  # dark red halo behind the goal marker

# Soft panel behind the maze, so the black walls do not sit on hard #161b22.
COLOR_MAZE_BACKDROP = "#0b0f14"

# Square-cell renderer: cells grow with the window, but stop at this size so
# small mazes (5x5, 7x7) never look oversized.
MAX_CELL_SIZE = 44
MIN_CELL_SIZE = 6

FONT_FAMILY = "Segoe UI"

TITLE_FONT = (FONT_FAMILY, 52, "bold")
SUBTITLE_FONT = (FONT_FAMILY, 18)
HEADING_FONT = (FONT_FAMILY, 28, "bold")
BODY_FONT = (FONT_FAMILY, 13)
BUTTON_FONT = (FONT_FAMILY, 14, "bold")
SMALL_FONT = (FONT_FAMILY, 10)

APP_TITLE = "Maze Adventure AI"
APP_VERSION = "1.0"
APP_WINDOW_TITLE = f"{APP_TITLE}  |  Human vs AI Challenge  |  v{APP_VERSION}"


def resource_path(*parts):
    """Absolute path to a bundled resource, for source runs and PyInstaller."""
    base = getattr(sys, "_MEIPASS", os.path.dirname(os.path.abspath(__file__)))
    return os.path.join(base, *parts)

# Maze size limits (odd values only, used by the Custom Challenge screen).
MAZE_MIN_SIZE = 5
MAZE_MAX_SIZE = 41
DIFFICULTIES = ("Easy", "Medium", "Hard")

# Exhibition challenge tiers. Only the maze dimensions are fixed - every run
# is still a fresh random DFS maze. Difficulty is a display label only and does
# not alter the generator, solver or hint algorithms.
LEVELS = (
    {
        "id": "beginner",
        "name": "Beginner",
        "rows": 11,
        "cols": 11,
        "difficulty": "Easy",
        "color": COLOR_SUCCESS,
    },
    {
        "id": "intermediate",
        "name": "Intermediate",
        "rows": 21,
        "cols": 21,
        "difficulty": "Medium",
        "color": COLOR_AI,
    },
    {
        "id": "advanced",
        "name": "Advanced",
        "rows": 31,
        "cols": 31,
        "difficulty": "Hard",
        "color": COLOR_HINT,
    },
    {
        "id": "expert",
        "name": "Expert",
        "rows": 41,
        "cols": 41,
        "difficulty": "Hard",
        "color": COLOR_DANGER,
    },
)

LEVEL_ORDER = tuple(level["id"] for level in LEVELS)
LEVEL_BY_ID = {level["id"]: level for level in LEVELS}
DEFAULT_LEVEL_ID = LEVEL_ORDER[0]
PROGRESS_VERSION = 1

# Achievements (id, display name). Order defines display & Treasure Hunter.
ACHIEVEMENT_DEFS = (
    ("first_victory", "First Victory"),
    ("hint_free", "Hint Free"),
    ("speed_runner", "Speed Runner"),
    ("efficient_navigator", "Efficient Navigator"),
    ("beginner_conqueror", "Beginner Conqueror"),
    ("intermediate_conqueror", "Intermediate Conqueror"),
    ("advanced_conqueror", "Advanced Conqueror"),
    ("expert_conqueror", "Expert Conqueror"),
    ("perfectionist", "Perfectionist"),
    ("explorer", "Explorer"),
    ("maze_master", "Maze Master"),
    ("treasure_hunter", "Treasure Hunter"),
)
ACHIEVEMENT_ORDER = tuple(item[0] for item in ACHIEVEMENT_DEFS)
ACHIEVEMENT_BY_ID = {item[0]: item[1] for item in ACHIEVEMENT_DEFS}
ACHIEVEMENT_DESCRIPTIONS = {
    "first_victory": "Complete any maze.",
    "hint_free": "Complete a maze without using hints.",
    "speed_runner": "Complete a maze in under 60 seconds.",
    "efficient_navigator": "Complete with 90% or higher efficiency.",
    "beginner_conqueror": "Complete the Beginner challenge.",
    "intermediate_conqueror": "Complete the Intermediate challenge.",
    "advanced_conqueror": "Complete the Advanced challenge.",
    "expert_conqueror": "Complete the Expert challenge.",
    "perfectionist": "Complete with 100% efficiency.",
    "explorer": "Replay a level 5 times.",
    "maze_master": "Complete all challenge levels.",
    "treasure_hunter": "Unlock all achievements.",
}
# Alternate lookup by display name (for tests using title case).
ACHIEVEMENT_NAME_TO_ID = {item[1]: item[0] for item in ACHIEVEMENT_DEFS}
ACHIEVEMENT_NAME_TO_ID_LOWER = {item[1].lower(): item[0] for item in ACHIEVEMENT_DEFS}


def _blank_record():
    return {"best_time": None, "best_moves": None, "best_efficiency": None}


CUSTOM_LEVEL_ID = "custom"
RECORD_LEVEL_IDS = LEVEL_ORDER + (CUSTOM_LEVEL_ID,)


def default_records():
    return {level_id: _blank_record() for level_id in RECORD_LEVEL_IDS}


def default_replay_counts():
    counts = {level_id: 0 for level_id in LEVEL_ORDER}
    counts[CUSTOM_LEVEL_ID] = 0
    return counts


def format_record_time(seconds):
    """Format seconds as MM:SS (or HH:MM:SS) for record display."""
    if seconds is None:
        return "—"
    try:
        total = int(seconds)
    except (TypeError, ValueError):
        return "—"
    minutes, secs = divmod(total, 60)
    hours, minutes = divmod(minutes, 60)
    if hours:
        return f"{hours:02d}:{minutes:02d}:{secs:02d}"
    return f"{minutes:02d}:{secs:02d}"


# ---------------------------------------------------------------------------
# Small reusable widgets / helpers
# ---------------------------------------------------------------------------
class MenuButton(tk.Button):
    """Flat themed button with a hover effect (tk.Button has none on Windows)."""

    STYLES = {
        "primary": {
            "bg": COLOR_ACCENT,
            "fg": "#05131f",
            "hover_bg": COLOR_ACCENT_HOVER,
            "hover_fg": "#05131f",
        },
        "secondary": {
            "bg": COLOR_PANEL_ALT,
            "fg": COLOR_TEXT,
            "hover_bg": "#21262d",
            "hover_fg": COLOR_TEXT_STRONG,
        },
        "danger": {
            "bg": COLOR_PANEL_ALT,
            "fg": COLOR_DANGER,
            "hover_bg": "#2d1517",
            "hover_fg": COLOR_DANGER_HOVER,
        },
    }

    def __init__(self, master, text, command=None, variant="primary", **kwargs):
        self._style = self.STYLES[variant]

        # Buttons never keep keyboard focus: Space must not fire a button on a
        # screen that has already been replaced.
        options = {
            "font": BUTTON_FONT,
            "padx": 22,
            "pady": 12,
            "takefocus": 0,
        }
        options.update(kwargs)

        super().__init__(
            master,
            text=text,
            command=command,
            bg=self._style["bg"],
            fg=self._style["fg"],
            activebackground=self._style["hover_bg"],
            activeforeground=self._style["hover_fg"],
            relief="flat",
            bd=0,
            highlightthickness=0,
            cursor="hand2",
            **options,
        )
        self.bind("<Enter>", self._on_enter)
        self.bind("<Leave>", self._on_leave)
        self.bind("<ButtonRelease-1>", self._return_focus, add="+")

    def _return_focus(self, _event=None):
        """Hand focus back to the window after a click (not the button)."""
        try:
            self.after_idle(self._focus_window)
        except tk.TclError:
            pass

    def _focus_window(self):
        try:
            self.winfo_toplevel().focus_set()
        except tk.TclError:
            pass

    def _on_enter(self, _event=None):
        if str(self.cget("state")) == "disabled":
            return
        self.configure(bg=self._style["hover_bg"], fg=self._style["hover_fg"])

    def _on_leave(self, _event=None):
        if str(self.cget("state")) == "disabled":
            return
        self.configure(bg=self._style["bg"], fg=self._style["fg"])


def center_container(screen):
    """Return a frame that is centred inside ``screen``."""
    screen.grid_rowconfigure(0, weight=1)
    screen.grid_columnconfigure(0, weight=1)

    wrapper = tk.Frame(screen, bg=COLOR_BG)
    wrapper.grid(row=0, column=0)
    return wrapper


def hline(parent, color=COLOR_BORDER, pad_y=0):
    """A 1 pixel horizontal rule that stretches with ``parent``."""
    line = tk.Frame(parent, bg=color, height=1)
    line.pack(fill="x", pady=pad_y)
    return line


def section_label(parent, text, pad_top=0, bg=COLOR_PANEL):
    """Small uppercase heading used inside cards."""
    label = tk.Label(
        parent,
        text=text,
        font=(FONT_FAMILY, 9, "bold"),
        bg=bg,
        fg=COLOR_MUTED,
    )
    label.pack(anchor="w", pady=(pad_top, 0))
    return label


# ---------------------------------------------------------------------------
# Maze rendering (shared by Gameplay and Results)
# ---------------------------------------------------------------------------
def maze_layout(maze, width, height, padding=24):
    """Geometry for a centred square-cell maze.

    Cells are sized from the available space but capped at ``MAX_CELL_SIZE``
    so a 5x5 maze stays compact while a 41x41 maze still fills the panel.
    Returns ``(left, top, cell)`` where ``cell`` is the full grid cell size.
    """
    cell = min(
        (width - 2 * padding) // maze.cols,
        (height - 2 * padding) // maze.rows,
        MAX_CELL_SIZE,
    )
    cell = max(cell, MIN_CELL_SIZE)

    total_w = cell * maze.cols
    total_h = cell * maze.rows
    return (width - total_w) // 2, (height - total_h) // 2, cell


def cell_gap(cell):
    """Small inset for markers/hints/paths (scales gently, then caps)."""
    return max(1, min(3, cell // 14))


def cell_box(layout, row, col):
    """Top-left corner and full side length of a maze cell, in pixels."""
    left, top, cell = layout
    return left + col * cell, top + row * cell, cell


def path_box(layout, row, col, extra=0):
    """Inset box used by markers, hints, the AI route and the replay."""
    x0, y0, cell = cell_box(layout, row, col)
    inset = cell_gap(cell) + extra
    return x0 + inset, y0 + inset, cell - 2 * inset


def draw_maze_cells(canvas, maze, layout):
    """Paint a classic maze: continuous white corridors, connected black walls."""
    left, top, cell = layout

    total_w = cell * maze.cols
    total_h = cell * maze.rows
    right = left + total_w
    bottom = top + total_h

    # Soft backdrop behind the maze panel.
    canvas.create_rectangle(
        left - 10,
        top - 10,
        right + 10,
        bottom + 10,
        fill=COLOR_MAZE_BACKDROP,
        outline=COLOR_BORDER,
    )

    # White corridor field, then the black wall cells on top. Adjacent walls
    # share edges and adjacent corridors stay white, so the maze reads as one
    # connected structure instead of a grid of separate tiles.
    canvas.create_rectangle(left, top, right, bottom, fill=COLOR_PATH, outline="")

    # Merge each horizontal run of wall cells into one rectangle. This keeps
    # the walls visually continuous and drastically reduces canvas items on
    # large mazes (faster redraws and smoother resizes).
    for row in range(maze.rows):
        col = 0
        while col < maze.cols:
            if not maze.is_wall(row, col):
                col += 1
                continue

            run_start = col
            while col < maze.cols and maze.is_wall(row, col):
                col += 1

            x0, y0, _ = cell_box(layout, row, run_start)
            canvas.create_rectangle(
                x0,
                y0,
                x0 + (col - run_start) * cell,
                y0 + cell,
                fill=COLOR_WALL,
                outline="",
            )


def rounded_rect(canvas, x0, y0, x1, y1, radius, **options):
    """Draw a rounded square (smooth polygon) on a canvas."""
    radius = max(0, min(radius, (x1 - x0) // 2, (y1 - y0) // 2))
    if radius < 3:
        return canvas.create_rectangle(x0, y0, x1, y1, **options)

    points = (
        x0 + radius, y0,
        x1 - radius, y0,
        x1, y0,
        x1, y0 + radius,
        x1, y1 - radius,
        x1, y1,
        x1 - radius, y1,
        x0 + radius, y1,
        x0, y1,
        x0, y1 - radius,
        x0, y0 + radius,
        x0, y0,
    )
    return canvas.create_polygon(points, smooth=True, **options)


def draw_cell_marker(canvas, layout, position, color, outline="", goal=False):
    """Rounded cell marker used by Gameplay and Results.

    Goal markers get a dark red halo and a white centre dot so they stay
    recognisable even when a 41x41 maze shrinks every cell to ~10 pixels.
    """
    x0, y0, cell = cell_box(layout, *position)
    inset = cell_gap(cell) + max(1, min(4, cell // 9))

    if goal:
        inset = max(1, inset - 1)   # slightly larger than the start marker

    size = cell - 2 * inset
    radius = max(2, size // 6)

    if goal:
        halo = max(1, min(inset, max(1, cell // 9)))
        rounded_rect(
            canvas,
            x0 + inset - halo,
            y0 + inset - halo,
            x0 + inset + size + halo,
            y0 + inset + size + halo,
            max(3, radius + halo // 2),
            fill=COLOR_GOAL_GLOW,
            outline="",
        )

    item = rounded_rect(
        canvas,
        x0 + inset,
        y0 + inset,
        x0 + inset + size,
        y0 + inset + size,
        radius,
        fill=color,
        outline=outline,
        width=1,
    )

    if goal and size >= 6:
        pad = max(1, size // 3)
        canvas.create_oval(
            x0 + inset + pad,
            y0 + inset + pad,
            x0 + inset + size - pad,
            y0 + inset + size - pad,
            fill=COLOR_PATH,
            outline="",
        )

    return item


def to_odd(value, label):
    """Maze dimensions must be odd.

    Returns ``(value, notice)`` where notice is ``None`` when no change was
    needed, or a message describing the automatic conversion.
    """
    if value % 2:
        return value, None

    adjusted = value + 1 if value + 1 <= MAZE_MAX_SIZE else value - 1
    return adjusted, f"{label}: {value} is even — adjusted to {adjusted}."


# ---------------------------------------------------------------------------
# Challenge progress persistence
# ---------------------------------------------------------------------------
def progress_file_path():
    """Location of the challenge save file.

    ``MAZE_ADVENTURE_AI_PROGRESS`` is an explicit override used by automated
    tests. Normal runs use ``%APPDATA%\\MazeAdventureAI\\progress.json``.
    """
    override = os.environ.get("MAZE_ADVENTURE_AI_PROGRESS")
    if override:
        return os.path.abspath(os.path.expanduser(override))

    appdata = os.environ.get("APPDATA") or os.path.expanduser("~")
    return os.path.join(appdata, "MazeAdventureAI", "progress.json")


def default_progress():
    """Fresh progress: only Beginner is available and nothing is completed."""
    return {
        "version": PROGRESS_VERSION,
        "unlocked": [DEFAULT_LEVEL_ID],
        "completed": [],
        "records": default_records(),
        "best_records": default_records(),
        "achievements": [],
        "replay_counts": default_replay_counts(),
        "replays": default_replay_counts(),
    }


def _normalize_records(raw):
    records = default_records()
    if not isinstance(raw, dict):
        return records
    # Accept both "records" shape and legacy/alternate key spellings.
    for level_id in RECORD_LEVEL_IDS:
        entry = raw.get(level_id)
        if not isinstance(entry, dict):
            # Custom bucket also accepts best_overall / overall aliases.
            if level_id == CUSTOM_LEVEL_ID:
                entry = raw.get("best_overall", raw.get("overall", raw.get("custom_record")))
                if not isinstance(entry, dict):
                    entry = None
            if not isinstance(entry, dict):
                continue
        out = records[level_id]
        # time: best_time / best_seconds / time / seconds
        for key in ("best_time", "best_seconds", "time", "seconds", "bestTime"):
            if key in entry and entry[key] is not None:
                try:
                    out["best_time"] = int(entry[key])
                except (TypeError, ValueError):
                    try:
                        out["best_time"] = int(float(entry[key]))
                    except (TypeError, ValueError):
                        pass
                break
        for key in ("best_moves", "least_moves", "moves", "moves_count", "bestMoves"):
            if key in entry and entry[key] is not None:
                try:
                    out["best_moves"] = int(entry[key])
                except (TypeError, ValueError):
                    try:
                        out["best_moves"] = int(float(entry[key]))
                    except (TypeError, ValueError):
                        pass
                break
        for key in ("best_efficiency", "efficiency", "highest_efficiency", "bestEfficiency"):
            if key in entry and entry[key] is not None:
                try:
                    out["best_efficiency"] = float(entry[key])
                except (TypeError, ValueError):
                    pass
                break
        if out["best_time"] is not None and out["best_time"] < 0:
            out["best_time"] = None
        if out["best_moves"] is not None and out["best_moves"] < 0:
            out["best_moves"] = None
        if out["best_efficiency"] is not None:
            out["best_efficiency"] = max(0.0, min(100.0, float(out["best_efficiency"])))
    return records


def _copy_records(records):
    """Deep-copy records, expanding alias key spellings for compatibility."""
    out = {}
    for level_id in RECORD_LEVEL_IDS:
        entry = records.get(level_id, {}) if isinstance(records, dict) else {}
        best_time = entry.get("best_time") if isinstance(entry, dict) else None
        best_moves = entry.get("best_moves") if isinstance(entry, dict) else None
        best_eff = entry.get("best_efficiency") if isinstance(entry, dict) else None
        out[level_id] = {
            "best_time": best_time,
            "best_seconds": best_time,
            "time": best_time,
            "best_moves": best_moves,
            "least_moves": best_moves,
            "moves": best_moves,
            "best_efficiency": best_eff,
            "highest_efficiency": best_eff,
            "efficiency": best_eff,
        }
    return out


def _normalize_achievements(raw):
    if not isinstance(raw, (list, tuple, set)):
        # Accept dict shape {id: True} defensively.
        if isinstance(raw, dict):
            raw = [key for key, value in raw.items() if value]
        else:
            return []
    unlocked = set()
    for item in raw:
        text = str(item).strip()
        lowered = text.lower()
        if text in ACHIEVEMENT_BY_ID:
            unlocked.add(text)
        elif lowered in ACHIEVEMENT_NAME_TO_ID_LOWER:
            unlocked.add(ACHIEVEMENT_NAME_TO_ID_LOWER[lowered])
        elif lowered in ACHIEVEMENT_BY_ID:
            unlocked.add(lowered)
    return [level_id for level_id in ACHIEVEMENT_ORDER if level_id in unlocked]


def _normalize_replay_counts(raw):
    counts = default_replay_counts()
    if not isinstance(raw, dict):
        return counts
    for level_id in RECORD_LEVEL_IDS:
        if level_id in raw:
            try:
                counts[level_id] = max(0, int(raw[level_id]))
            except (TypeError, ValueError):
                try:
                    counts[level_id] = max(0, int(float(raw[level_id])))
                except (TypeError, ValueError):
                    counts[level_id] = 0
    # Custom also accepts overall/total aliases.
    if "custom" not in raw:
        for key in ("best_overall", "overall", "custom_replays"):
            if key in raw:
                try:
                    counts[CUSTOM_LEVEL_ID] = max(0, int(raw[key]))
                except (TypeError, ValueError):
                    pass
                break
    return counts


def normalize_progress(raw):
    """Return a safe, ordered progress record from arbitrary JSON data.

    Unknown ids are ignored, progress is kept as a contiguous chain, and the
    first level is always unlocked. This keeps a hand-edited or partially
    corrupted save file from breaking the game.
    """
    if not isinstance(raw, dict):
        raw = {}

    def read_ids(value):
        if not isinstance(value, (list, tuple, set)):
            return set()
        ids = set()
        for item in value:
            level_id = str(item).strip().lower()
            if level_id in LEVEL_BY_ID:
                ids.add(level_id)
        return ids

    completed = read_ids(raw.get("completed"))
    unlocked = read_ids(raw.get("unlocked")) | {DEFAULT_LEVEL_ID}

    # Challenges are completed in order, so completing a later tier implies
    # every tier before it is complete as well.
    if completed:
        highest = max(LEVEL_ORDER.index(level_id) for level_id in completed)
        completed.update(LEVEL_ORDER[: highest + 1])

    # Keep unlocked levels contiguous from Beginner through the furthest
    # level the player has reached, then unlock the next tier after completion.
    furthest = max(
        [LEVEL_ORDER.index(level_id) for level_id in unlocked]
        + [LEVEL_ORDER.index(level_id) for level_id in completed]
        + [0]
    )
    unlocked.update(LEVEL_ORDER[: furthest + 1])

    if completed:
        highest_completed = max(LEVEL_ORDER.index(level_id) for level_id in completed)
        if highest_completed + 1 < len(LEVEL_ORDER):
            unlocked.add(LEVEL_ORDER[highest_completed + 1])

    unlocked.update(completed)

    # Records / achievements / replay counts are additive and backward
    # compatible: old files without them simply get defaults.
    records = _normalize_records(
        raw.get("records", raw.get("best_records", raw.get("bestRecords")))
    )
    achievements = _normalize_achievements(
        raw.get("achievements", raw.get("achievements_unlocked", []))
    )
    replay_counts = _normalize_replay_counts(
        raw.get("replay_counts", raw.get("replays", raw.get("replayCounts")))
    )
    expanded = _copy_records(records)
    custom_record = expanded.get(CUSTOM_LEVEL_ID, _blank_record())
    custom_replay = dict(replay_counts).get(CUSTOM_LEVEL_ID, 0)

    return {
        "version": PROGRESS_VERSION,
        "unlocked": [level_id for level_id in LEVEL_ORDER if level_id in unlocked],
        "completed": [level_id for level_id in LEVEL_ORDER if level_id in completed],
        "records": expanded,
        "best_records": expanded,
        "best_overall": dict(custom_record),
        "achievements": achievements,
        "replay_counts": dict(replay_counts),
        "replays": dict(replay_counts),
        "custom_replays": int(custom_replay),
    }


def load_progress(path=None):
    """Read and validate the save file. Missing/broken files load defaults."""
    path = path or progress_file_path()
    try:
        with open(path, "r", encoding="utf-8") as handle:
            raw = json.load(handle)
    except (OSError, ValueError, TypeError):
        return default_progress()
    return normalize_progress(raw)


def save_progress_data(progress, path=None):
    """Atomically write a progress record and return the normalised data."""
    path = path or progress_file_path()
    data = normalize_progress(progress)

    directory = os.path.dirname(path) or "."
    os.makedirs(directory, exist_ok=True)

    temporary = f"{path}.tmp"
    try:
        with open(temporary, "w", encoding="utf-8") as handle:
            json.dump(data, handle, indent=2)
            handle.write("\n")
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
    finally:
        if os.path.exists(temporary):
            try:
                os.remove(temporary)
            except OSError:
                pass
    return data


def clear_progress_file(path=None):
    """Delete the save file (and any leftover temporary file)."""
    path = path or progress_file_path()
    for target in (path, f"{path}.tmp"):
        try:
            if os.path.exists(target):
                os.remove(target)
        except OSError:
            if target == path:
                raise



# ---------------------------------------------------------------------------
# Screen base class
# ---------------------------------------------------------------------------
class Screen(tk.Frame):
    """Base class for every screen. Each screen fills the whole window."""

    title = "Screen"

    def __init__(self, app):
        # Every screen lives inside the app's container frame and fills it.
        super().__init__(app.container, bg=COLOR_BG)
        self.app = app
        self.build()

    def build(self):
        """Subclasses create their widgets here."""

    def on_show(self):
        """Called every time this screen becomes visible (refresh state here)."""

    def on_hide(self):
        """Called when another screen replaces this one (stop timers here)."""


# ---------------------------------------------------------------------------
# Splash
# ---------------------------------------------------------------------------
class SplashScreen(Screen):
    title = "Maze Adventure AI"

    DURATION_MS = 2400          # 2.4 seconds, inside the requested 2-3 s
    PROGRESS_STEP_MS = 90

    def build(self):
        self._finish_job = None
        self._progress_job = None
        self._progress = 0.0

        card = tk.Frame(center_container(self), bg=COLOR_BG)
        card.pack()

        # Small A* badge, then the product name.
        badge = tk.Canvas(
            card, width=88, height=88,
            bg=COLOR_BG, highlightthickness=0, bd=0,
        )
        badge.pack(pady=(0, 18))
        badge.create_rectangle(
            8, 8, 80, 80,
            fill=COLOR_PANEL, outline=COLOR_ACCENT, width=2,
        )
        badge.create_text(
            44, 38, text="AI",
            font=(FONT_FAMILY, 22, "bold"), fill=COLOR_AI,
        )
        badge.create_text(
            44, 62, text="SOLVER",
            font=(FONT_FAMILY, 8, "bold"), fill=COLOR_MUTED,
        )

        tk.Label(
            card,
            text="MAZE ADVENTURE AI",
            font=(FONT_FAMILY, 44, "bold"),
            bg=COLOR_BG,
            fg=COLOR_TEXT_STRONG,
        ).pack()

        tk.Label(
            card,
            text="Human vs AI Challenge",
            font=SUBTITLE_FONT,
            bg=COLOR_BG,
            fg=COLOR_ACCENT,
        ).pack(pady=(6, 18))

        tk.Label(
            card,
            text="Created using: DFS, BFS and A* Pathfinding",
            font=SMALL_FONT,
            bg=COLOR_BG,
            fg=COLOR_MUTED,
        ).pack(pady=(0, 22))

        track = tk.Frame(card, bg=COLOR_PANEL_ALT, width=300, height=6)
        track.pack()
        track.pack_propagate(False)

        self.progress_fill = tk.Frame(track, bg=COLOR_ACCENT)
        self.progress_fill.place(x=0, y=0, relwidth=0.0, relheight=1.0)

        tk.Label(
            card,
            text="Loading...",
            font=BODY_FONT,
            bg=COLOR_BG,
            fg=COLOR_MUTED,
        ).pack(pady=(12, 0))

        tk.Label(
            card,
            text=f"Version {APP_VERSION}",
            font=SMALL_FONT,
            bg=COLOR_BG,
            fg=COLOR_MUTED,
        ).pack(pady=(30, 0))

    def on_show(self):
        self._cancel_jobs()
        self._progress = 0.0
        self.progress_fill.place_configure(relwidth=0.0)
        self._progress_job = self.after(self.PROGRESS_STEP_MS, self._advance_progress)
        self._finish_job = self.after(self.DURATION_MS, self._finish)

    def on_hide(self):
        self._cancel_jobs()

    def _cancel_jobs(self):
        for attribute in ("_finish_job", "_progress_job"):
            job = getattr(self, attribute, None)
            if job is not None:
                self.after_cancel(job)
                setattr(self, attribute, None)

    def _advance_progress(self):
        self._progress_job = None
        if self.app.current_screen != "splash":
            return

        self._progress = min(
            1.0, self._progress + self.PROGRESS_STEP_MS / self.DURATION_MS
        )
        self.progress_fill.place_configure(relwidth=self._progress)

        if self._progress < 1.0:
            self._progress_job = self.after(
                self.PROGRESS_STEP_MS, self._advance_progress
            )

    def _finish(self):
        self._finish_job = None
        if self.app.current_screen == "splash":
            self.app.show_screen("home")


# ---------------------------------------------------------------------------
# Home
# ---------------------------------------------------------------------------
class HomeScreen(Screen):
    title = "Home"

    def build(self):
        card = tk.Frame(center_container(self), bg=COLOR_BG)
        card.pack()

        tk.Label(
            card,
            text="MAZE ADVENTURE AI",
            font=(FONT_FAMILY, 28, "bold"),
            bg=COLOR_BG,
            fg=COLOR_TEXT_STRONG,
        ).pack()

        tk.Label(
            card,
            text="Human vs AI Challenge",
            font=(FONT_FAMILY, 10),
            bg=COLOR_BG,
            fg=COLOR_ACCENT,
        ).pack(pady=(0, 0))

        hline(card, pad_y=4)

        # --- challenge progress ------------------------------------------------
        progress_card = tk.Frame(
            card,
            bg=COLOR_PANEL,
            padx=20,
            pady=6,
            highlightbackground=COLOR_BORDER,
            highlightthickness=1,
        )
        progress_card.pack(fill="x", pady=(0, 6))

        progress_head = tk.Frame(progress_card, bg=COLOR_PANEL)
        progress_head.pack(fill="x")

        tk.Label(
            progress_head,
            text="CHALLENGE PROGRESS",
            font=(FONT_FAMILY, 9, "bold"),
            bg=COLOR_PANEL,
            fg=COLOR_MUTED,
        ).pack(side="left")

        self.progress_count_label = tk.Label(
            progress_head,
            text="Progress: 0 / 4 Challenges Completed",
            font=(FONT_FAMILY, 10, "bold"),
            bg=COLOR_PANEL,
            fg=COLOR_ACCENT,
        )
        self.progress_count_label.pack(side="right")

        checklist = tk.Frame(progress_card, bg=COLOR_PANEL)
        checklist.pack(fill="x", pady=(3, 0))

        self.check_labels = {}
        for level in LEVELS:
            label = tk.Label(
                checklist,
                text="",
                font=(FONT_FAMILY, 10, "bold"),
                bg=COLOR_PANEL,
                fg=COLOR_MUTED,
            )
            label.pack(side="left", padx=(0, 18))
            self.check_labels[level["id"]] = label

        track = tk.Frame(progress_card, bg=COLOR_PANEL_ALT, height=6)
        track.pack(fill="x", pady=(4, 0))
        track.pack_propagate(False)

        self.progress_fill = tk.Frame(track, bg=COLOR_SUCCESS)
        self.progress_fill.place(x=0, y=0, relwidth=0.0, relheight=1.0)

        self.achievements_count_label = tk.Label(
            progress_card,
            text="Achievements: 0/12 Unlocked",
            font=(FONT_FAMILY, 9, "bold"),
            bg=COLOR_PANEL,
            fg=COLOR_AI,
            anchor="w",
        )
        self.achievements_count_label.pack(fill="x", pady=(4, 0), anchor="w")
        # Aliases for discoverability.
        self.achievements_summary_label = self.achievements_count_label
        self.achievement_count_label = self.achievements_count_label
        self.achievement_labels = {}
        self.achievements_labels = self.achievement_labels

        # --- best records ------------------------------------------------------
        records_card = tk.Frame(
            card,
            bg=COLOR_PANEL,
            padx=20,
            pady=6,
            highlightbackground=COLOR_BORDER,
            highlightthickness=1,
        )
        records_card.pack(fill="x", pady=(0, 6))

        tk.Label(
            records_card,
            text="BEST RECORDS",
            font=(FONT_FAMILY, 9, "bold"),
            bg=COLOR_PANEL,
            fg=COLOR_MUTED,
            anchor="w",
        ).pack(fill="x", anchor="w")

        self.record_labels = {}
        for level in LEVELS:
            label = tk.Label(
                records_card,
                text="",
                font=(FONT_FAMILY, 9),
                bg=COLOR_PANEL,
                fg=COLOR_TEXT,
                anchor="w",
            )
            label.pack(fill="x", pady=(2, 0), anchor="w")
            self.record_labels[level["id"]] = label
        # Aliases for discoverability.
        self.records_labels = self.record_labels
        self.best_record_labels = self.record_labels

        # --- main menu ----------------------------------------------------------
        buttons = tk.Frame(card, bg=COLOR_BG)
        buttons.pack()

        MenuButton(
            buttons,
            "PLAY",
            command=lambda: self.app.show_screen("challenges"),
            variant="primary",
            width=24,
            font=(FONT_FAMILY, 11, "bold"),
            pady=4,
        ).pack(fill="x", pady=3)

        MenuButton(
            buttons,
            "CUSTOM CHALLENGE",
            command=lambda: self.app.show_screen("settings"),
            variant="secondary",
            width=24,
            font=(FONT_FAMILY, 11, "bold"),
            pady=4,
        ).pack(fill="x", pady=3)

        MenuButton(
            buttons,
            "INSTRUCTIONS",
            command=self.show_instructions,
            variant="secondary",
            width=24,
            font=(FONT_FAMILY, 11, "bold"),
            pady=4,
        ).pack(fill="x", pady=3)

        self.achievements_button = MenuButton(
            buttons,
            "VIEW ACHIEVEMENTS",
            command=self.show_achievements,
            variant="secondary",
            width=24,
            font=(FONT_FAMILY, 11, "bold"),
            pady=4,
        )
        self.achievements_button.pack(fill="x", pady=3)

        MenuButton(
            buttons,
            "EXIT",
            command=self.app.exit_app,
            variant="danger",
            width=24,
            font=(FONT_FAMILY, 11, "bold"),
            pady=4,
        ).pack(fill="x", pady=(3, 0))

        tk.Label(
            card,
            text=f"v{APP_VERSION}  ·  four challenges  ·  smart hints  ·  full replay",
            font=SMALL_FONT,
            bg=COLOR_BG,
            fg=COLOR_MUTED,
        ).pack(pady=(8, 0))

    def on_show(self):
        self.refresh_progress()
        self.refresh_records_achievements()

    def refresh_progress(self):
        """Refresh the count, checklist and bar from the in-memory progress."""
        completed = self.app.completed
        count = len(completed)
        total = len(LEVELS)

        self.progress_count_label.configure(
            text=f"Progress: {count} / {total} Challenges Completed"
        )
        self.progress_fill.place_configure(relwidth=count / total)

        for level in LEVELS:
            level_id = level["id"]
            if level_id in completed:
                text, color = f"✓ {level['name']}", level["color"]
            elif self.app.is_unlocked(level_id):
                text, color = f"○ {level['name']}", COLOR_ACCENT
            else:
                text, color = f"• {level['name']}", COLOR_MUTED

            self.check_labels[level_id].configure(text=text, fg=color)

    def refresh_records_achievements(self):
        """Refresh best records and the compact achievement summary."""
        if not hasattr(self, "record_labels"):
            return
        for level in LEVELS:
            level_id = level["id"]
            record = self.app.record_for_level(level_id)
            best_time = record.get("best_time")
            best_moves = record.get("best_moves")
            best_eff = record.get("best_efficiency")
            time_text = format_record_time(best_time) if best_time is not None else "—"
            moves_text = str(best_moves) if best_moves is not None else "—"
            eff_text = f"{float(best_eff):.1f}%" if best_eff is not None else "—"
            self.record_labels[level_id].configure(
                text=f"{level['name']}: Best Time: {time_text} · Least Moves: {moves_text} · Highest Efficiency: {eff_text}"
            )
        unlocked = getattr(self.app, "achievements", set())
        count = len(unlocked)
        total = len(ACHIEVEMENT_ORDER)
        summary = f"Achievements: {count}/{total} Unlocked"
        try:
            self.achievements_count_label.configure(text=summary)
        except Exception:
            pass
        # Keep aliases pointing at the same summary widget.
        self.records_labels = self.record_labels
        self.best_record_labels = self.record_labels
        self.achievement_count_label = self.achievements_count_label
        self.achievements_summary_label = self.achievements_count_label

    def show_achievements(self):
        self.app.show_screen("achievements")

    def view_achievements(self):
        self.app.show_screen("achievements")

    def show_instructions(self):
        self.app.show_screen("instructions")


# ---------------------------------------------------------------------------
# Achievements (dedicated screen)
# ---------------------------------------------------------------------------
class AchievementsScreen(Screen):
    title = "Achievements"

    def build(self):
        card = tk.Frame(
            center_container(self),
            bg=COLOR_PANEL,
            padx=28,
            pady=12,
            highlightbackground=COLOR_BORDER,
            highlightthickness=1,
        )
        card.pack()

        tk.Label(
            card,
            text="Achievements",
            font=(FONT_FAMILY, 24, "bold"),
            bg=COLOR_PANEL,
            fg=COLOR_TEXT_STRONG,
        ).pack(anchor="w")

        tk.Label(
            card,
            text="Earn medals by playing smart, fast and complete — progress saves with your run progress.",
            font=(FONT_FAMILY, 8),
            bg=COLOR_PANEL,
            fg=COLOR_MUTED,
        ).pack(anchor="w", pady=(2, 0))

        self.summary_label = tk.Label(
            card,
            text="Achievements: 0/12 Unlocked",
            font=(FONT_FAMILY, 10, "bold"),
            bg=COLOR_PANEL,
            fg=COLOR_AI,
            anchor="w",
        )
        self.summary_label.pack(anchor="w", pady=(6, 0))
        self.count_label = self.summary_label
        self.achievements_summary_label = self.summary_label

        hline(card, pad_y=6)

        list_frame = tk.Frame(card, bg=COLOR_PANEL)
        list_frame.pack(fill="both", expand=True)
        for column in range(2):
            list_frame.grid_columnconfigure(column, weight=1)

        self.achievement_rows = {}
        self.achievement_labels = {}
        for index, (ach_id, ach_name) in enumerate(ACHIEVEMENT_DEFS):
            row, column = divmod(index, 2)
            item = tk.Frame(
                list_frame,
                bg=COLOR_PANEL_ALT,
                padx=8,
                pady=3,
                highlightbackground=COLOR_BORDER,
                highlightthickness=1,
            )
            item.grid(row=row, column=column, sticky="ew", pady=(0, 4), padx=(0, 6))

            icon = tk.Label(
                item,
                text="○",
                font=(FONT_FAMILY, 12, "bold"),
                bg=COLOR_PANEL_ALT,
                fg=COLOR_MUTED,
            )
            icon.pack(side="left", padx=(0, 8))

            info = tk.Frame(item, bg=COLOR_PANEL_ALT)
            info.pack(side="left", fill="x", expand=True)

            name = tk.Label(
                info,
                text=ach_name,
                font=(FONT_FAMILY, 10, "bold"),
                bg=COLOR_PANEL_ALT,
                fg=COLOR_TEXT_STRONG,
                anchor="w",
            )
            name.pack(anchor="w")

            desc = tk.Label(
                info,
                text=ACHIEVEMENT_DESCRIPTIONS.get(ach_id, ""),
                font=(FONT_FAMILY, 8),
                bg=COLOR_PANEL_ALT,
                fg=COLOR_MUTED,
                anchor="w",
            )
            desc.pack(anchor="w", pady=(1, 0))

            status = tk.Label(
                item,
                text="LOCKED",
                font=(FONT_FAMILY, 7, "bold"),
                bg=COLOR_PANEL_ALT,
                fg=COLOR_MUTED,
            )
            status.pack(side="right", padx=(8, 0))

            self.achievement_rows[ach_id] = {"row": item, "icon": icon, "name": name, "desc": desc, "status": status}
            self.achievement_labels[ach_id] = name
        self.achievements_labels = self.achievement_labels

        hline(card, pad_y=6)

        MenuButton(
            card,
            "Back to Home",
            command=lambda: self.app.show_screen("home"),
            variant="primary",
            width=18,
            font=(FONT_FAMILY, 10, "bold"),
            pady=4,
        ).pack(fill="x")

    def on_show(self):
        self.refresh_achievements()

    def refresh_achievements(self):
        if not hasattr(self, "achievement_rows"):
            return
        unlocked = getattr(self.app, "achievements", set())
        count = len(unlocked)
        total = len(ACHIEVEMENT_ORDER)
        summary = f"Achievements: {count}/{total} Unlocked"
        try:
            self.summary_label.configure(text=summary)
        except Exception:
            pass
        for ach_id, ach_name in ACHIEVEMENT_DEFS:
            rows = self.achievement_rows.get(ach_id)
            if rows is None:
                continue
            if ach_id in unlocked:
                rows["icon"].configure(text="🏅", fg=COLOR_AI)
                rows["name"].configure(text=f"🏅 {ach_name}", fg=COLOR_TEXT_STRONG)
                rows["status"].configure(text="UNLOCKED", fg=COLOR_SUCCESS)
            else:
                rows["icon"].configure(text="○", fg=COLOR_MUTED)
                rows["name"].configure(text=ach_name, fg=COLOR_MUTED)
                rows["status"].configure(text="LOCKED", fg=COLOR_MUTED)
        # Keep aliases in sync.
        self.count_label = self.summary_label
        self.achievements_summary_label = self.summary_label
        self.achievements_labels = self.achievement_labels


# ---------------------------------------------------------------------------
# Challenge Selection
# ---------------------------------------------------------------------------
class ChallengeSelectionScreen(Screen):
    title = "Challenge Selection"

    def build(self):
        self.level_rows = {}

        card = tk.Frame(center_container(self), bg=COLOR_BG)
        card.pack()

        tk.Label(
            card,
            text="CHALLENGE SELECTION",
            font=HEADING_FONT,
            bg=COLOR_BG,
            fg=COLOR_TEXT_STRONG,
        ).pack(anchor="w")

        header = tk.Frame(card, bg=COLOR_BG)
        header.pack(fill="x", pady=(4, 14))

        tk.Label(
            header,
            text="Complete each challenge to unlock the next tier.",
            font=SMALL_FONT,
            bg=COLOR_BG,
            fg=COLOR_MUTED,
        ).pack(side="left")

        self.completed_label = tk.Label(
            header,
            text="0 / 4 COMPLETED",
            font=(FONT_FAMILY, 9, "bold"),
            bg=COLOR_BG,
            fg=COLOR_ACCENT,
        )
        self.completed_label.pack(side="right")

        # A thin spacer gives the rows a comfortable shared width.
        tk.Frame(card, width=760, height=1, bg=COLOR_BG).pack()

        rows = tk.Frame(card, bg=COLOR_BG)
        rows.pack(fill="x")

        for level in LEVELS:
            self._build_level_row(rows, level)

        hline(card, pad_y=16)

        footer = tk.Frame(card, bg=COLOR_BG)
        footer.pack(fill="x")

        MenuButton(
            footer,
            "RESET PROGRESS",
            command=self.reset_progress,
            variant="danger",
            width=17,
            font=(FONT_FAMILY, 11, "bold"),
            pady=6,
        ).pack(side="left")

        MenuButton(
            footer,
            "BACK TO HOME",
            command=lambda: self.app.show_screen("home"),
            variant="secondary",
            width=14,
            font=(FONT_FAMILY, 11, "bold"),
            pady=6,
        ).pack(side="right")

    def _build_level_row(self, parent, level):
        row = tk.Frame(
            parent,
            bg=COLOR_PANEL,
            highlightbackground=COLOR_BORDER,
            highlightthickness=1,
        )
        row.pack(fill="x", pady=(0, 8))

        accent = tk.Frame(row, width=4, bg=level["color"])
        accent.pack(side="left", fill="y")

        body = tk.Frame(row, bg=COLOR_PANEL, padx=14, pady=8)
        body.pack(side="left", fill="both", expand=True)

        dot = tk.Label(
            body,
            text="●",
            font=(FONT_FAMILY, 18, "bold"),
            bg=COLOR_PANEL,
            fg=level["color"],
        )
        dot.pack(side="left", padx=(0, 10))

        info = tk.Frame(body, bg=COLOR_PANEL)
        info.pack(side="left", fill="x", expand=True)

        name_row = tk.Frame(info, bg=COLOR_PANEL)
        name_row.pack(anchor="w")

        tk.Label(
            name_row,
            text=level["name"],
            font=(FONT_FAMILY, 14, "bold"),
            bg=COLOR_PANEL,
            fg=COLOR_TEXT_STRONG,
        ).pack(side="left")

        lock_label = tk.Label(
            name_row,
            text="",
            font=("Segoe UI Emoji", 12),
            bg=COLOR_PANEL,
            fg=COLOR_MUTED,
        )
        lock_label.pack(side="left", padx=(8, 0))

        detail = tk.Label(
            info,
            text="",
            font=SMALL_FONT,
            bg=COLOR_PANEL,
            fg=COLOR_MUTED,
            anchor="w",
        )
        detail.pack(anchor="w", pady=(2, 0))

        right = tk.Frame(body, bg=COLOR_PANEL)
        right.pack(side="right", padx=(12, 0))

        status = tk.Label(
            right,
            text="",
            font=(FONT_FAMILY, 8, "bold"),
            bg=COLOR_PANEL,
            fg=COLOR_MUTED,
        )
        status.pack(anchor="e", pady=(0, 3))

        button = MenuButton(
            right,
            "START",
            command=lambda level_id=level["id"]: self.start_level(level_id),
            variant="secondary",
            width=11,
            font=(FONT_FAMILY, 10, "bold"),
            pady=3,
        )
        button.pack()

        self.level_rows[level["id"]] = {
            "frame": row,
            "accent": accent,
            "lock": lock_label,
            "detail": detail,
            "status": status,
            "button": button,
        }

    def on_show(self):
        self.refresh_levels()

    def refresh_levels(self):
        completed = self.app.completed
        self.completed_label.configure(
            text=f"{len(completed)} / {len(LEVELS)} COMPLETED"
        )

        for index, level in enumerate(LEVELS):
            level_id = level["id"]
            row = self.level_rows[level_id]
            unlocked = self.app.is_unlocked(level_id)
            done = level_id in completed
            button = row["button"]

            detail = f"{level['rows']} × {level['cols']}"

            if done:
                status_text, status_color = "COMPLETED", level["color"]
                detail += "  ·  Completed"
                button.configure(state="normal", text="REPLAY")
                row["lock"].configure(text="")
                self._style_level_button(button, completed=True)
            elif unlocked:
                status_text, status_color = "UNLOCKED", COLOR_SUCCESS
                detail += "  ·  Ready to play"
                button.configure(state="normal", text="START")
                row["lock"].configure(text="")
                self._style_level_button(button, completed=False)
            else:
                previous = LEVELS[max(0, index - 1)]["name"]
                status_text, status_color = "LOCKED", COLOR_MUTED
                detail += f"  ·  Unlock after {previous} completed"
                button.configure(state="disabled", text="LOCKED")
                row["lock"].configure(text="🔒")
                self._style_level_button(button, locked=True)

            row["status"].configure(text=status_text, fg=status_color)
            row["detail"].configure(text=detail)

    @staticmethod
    def _style_level_button(button, completed=False, locked=False):
        """Keep available buttons bright and locked buttons visually quiet."""
        if locked:
            style = MenuButton.STYLES["secondary"]
            button.configure(
                bg=COLOR_PANEL_ALT,
                fg=COLOR_MUTED,
                activebackground=COLOR_PANEL_ALT,
                activeforeground=COLOR_MUTED,
                disabledforeground=COLOR_MUTED,
            )
        else:
            style = MenuButton.STYLES["secondary" if completed else "primary"]

        button._style = style
        if not locked:
            button.configure(
                bg=style["bg"],
                fg=style["fg"],
                activebackground=style["hover_bg"],
                activeforeground=style["hover_fg"],
            )

    def start_level(self, level_id):
        if not self.app.is_unlocked(level_id):
            return
        self.app.start_challenge(level_id)

    def reset_progress(self):
        """Confirm, then remove the save file and lock every non-Beginner tier."""
        confirmed = messagebox.askyesno(
            "Reset Progress",
            "Reset all challenge progress?\n\n"
            "This clears the save file and locks Intermediate, Advanced "
            "and Expert until they are earned again.",
            parent=self.app,
        )
        if not confirmed:
            return

        ok, error = self.app.reset_progress()
        self.refresh_levels()
        home = self.app.screens.get("home")
        if home is not None:
            home.refresh_progress()
            if hasattr(home, "refresh_records_achievements"):
                home.refresh_records_achievements()

        if not ok:
            messagebox.showerror(
                "Reset Progress",
                "Progress was reset for this session, but the save file "
                f"could not be removed:\n\n{error}",
                parent=self.app,
            )



# ---------------------------------------------------------------------------
# Custom Challenge
# ---------------------------------------------------------------------------
class SettingsScreen(Screen):
    """Custom maze size + difficulty.

    Validates the input, converts even dimensions to odd ones and stores the
    result in ``app.settings`` for the gameplay screen. It does not generate
    or draw the maze.
    """

    title = "Custom Challenge"

    def build(self):
        card = tk.Frame(
            center_container(self),
            bg=COLOR_PANEL,
            padx=46,
            pady=32,
            highlightbackground=COLOR_BORDER,
            highlightthickness=1,
        )
        card.pack()

        tk.Label(
            card,
            text="Custom Challenge",
            font=HEADING_FONT,
            bg=COLOR_PANEL,
            fg=COLOR_TEXT_STRONG,
        ).pack(anchor="w")

        tk.Label(
            card,
            text="Build your own maze: choose rows, columns and difficulty.",
            font=SMALL_FONT,
            bg=COLOR_PANEL,
            fg=COLOR_MUTED,
        ).pack(anchor="w", pady=(4, 0))

        # --- maze size -------------------------------------------------------
        section_label(card, "MAZE SIZE", pad_top=20)

        self.rows_var = tk.StringVar(value=str(self.app.settings["rows"]))
        self.cols_var = tk.StringVar(value=str(self.app.settings["cols"]))

        size_grid = tk.Frame(card, bg=COLOR_PANEL)
        size_grid.pack(fill="x", pady=(8, 0))

        for row, (text, variable) in enumerate(
            (("Rows", self.rows_var), ("Columns", self.cols_var))
        ):
            tk.Label(
                size_grid,
                text=text,
                font=BODY_FONT,
                bg=COLOR_PANEL,
                fg=COLOR_TEXT,
                width=9,
                anchor="w",
            ).grid(row=row, column=0, sticky="w", pady=4)

            tk.Spinbox(
                size_grid,
                from_=MAZE_MIN_SIZE,
                to=MAZE_MAX_SIZE,
                increment=2,
                textvariable=variable,
                width=6,
                font=BODY_FONT,
                justify="center",
                bg=COLOR_PANEL_ALT,
                fg=COLOR_TEXT_STRONG,
                buttonbackground=COLOR_PANEL_ALT,
                insertbackground=COLOR_TEXT,
                relief="flat",
                highlightthickness=1,
                highlightbackground=COLOR_BORDER,
                highlightcolor=COLOR_ACCENT,
            ).grid(row=row, column=1, sticky="w", pady=4)

            tk.Label(
                size_grid,
                text=f"{MAZE_MIN_SIZE} to {MAZE_MAX_SIZE}",
                font=SMALL_FONT,
                bg=COLOR_PANEL,
                fg=COLOR_MUTED,
            ).grid(row=row, column=2, sticky="w", padx=(12, 0), pady=4)

        tk.Label(
            card,
            text="Odd dimensions only — even values are converted automatically.",
            font=SMALL_FONT,
            bg=COLOR_PANEL,
            fg=COLOR_MUTED,
        ).pack(anchor="w", pady=(6, 0))

        # --- difficulty ------------------------------------------------------
        section_label(card, "DIFFICULTY", pad_top=18)

        self.difficulty = tk.StringVar(value=self.app.settings["difficulty"])

        radio_row = tk.Frame(card, bg=COLOR_PANEL)
        radio_row.pack(anchor="w", pady=(6, 0))

        for value in DIFFICULTIES:
            tk.Radiobutton(
                radio_row,
                text=value,
                value=value,
                variable=self.difficulty,
                command=self.store_difficulty,
                font=BODY_FONT,
                bg=COLOR_PANEL,
                fg=COLOR_TEXT,
                activebackground=COLOR_PANEL,
                activeforeground=COLOR_TEXT_STRONG,
                selectcolor=COLOR_BG,
                highlightthickness=0,
                bd=0,
                cursor="hand2",
                padx=6,
            ).pack(side="left", padx=(0, 18))

        # --- validation messages ----------------------------------------------
        message_box = tk.Frame(card, bg=COLOR_PANEL, height=84)
        message_box.pack(fill="x", pady=(16, 0))
        message_box.pack_propagate(False)

        self.message_label = tk.Label(
            message_box,
            text="",
            font=BODY_FONT,
            bg=COLOR_PANEL,
            fg=COLOR_MUTED,
            anchor="nw",
            justify="left",
            wraplength=384,
        )
        self.message_label.pack(fill="both", expand=True)

        # --- buttons ----------------------------------------------------------
        hline(card, pad_y=16)

        buttons = tk.Frame(card, bg=COLOR_PANEL)
        buttons.pack(fill="x")

        MenuButton(
            buttons,
            "Generate Maze",
            command=self.generate_maze,
            variant="primary",
            width=16,
        ).pack(side="left")

        MenuButton(
            buttons,
            "Back",
            command=lambda: self.app.show_screen("home"),
            variant="secondary",
            width=10,
        ).pack(side="right")

    # -- state -----------------------------------------------------------------
    def on_show(self):
        """Restore the last stored values and clear any old message."""
        self.difficulty.set(self.app.settings["difficulty"])
        self.rows_var.set(str(self.app.settings["rows"]))
        self.cols_var.set(str(self.app.settings["cols"]))
        self.show_message("", "info")

    def store_difficulty(self):
        self.app.settings["difficulty"] = self.difficulty.get()

    def show_message(self, text, kind="info"):
        colors = {
            "info": COLOR_ACCENT,
            "success": COLOR_SUCCESS,
            "error": COLOR_DANGER,
        }
        self.message_label.configure(text=text, fg=colors.get(kind, COLOR_MUTED))

    # -- validation ------------------------------------------------------------
    @staticmethod
    def read_size(raw, label):
        """Return ``(value, error_message)`` for a single dimension field."""
        text = str(raw).strip()

        if not text:
            return None, f"{label}: please enter a number."

        try:
            value = int(text)
        except ValueError:
            return None, f"{label}: '{text}' is not a whole number."

        if not MAZE_MIN_SIZE <= value <= MAZE_MAX_SIZE:
            return None, (
                f"{label}: must be {MAZE_MIN_SIZE} to {MAZE_MAX_SIZE} "
                f"(got {value})."
            )

        return value, None

    def generate_maze(self):
        """Validate, normalise and store. Building the maze comes later."""
        rows, rows_error = self.read_size(self.rows_var.get(), "Rows")
        cols, cols_error = self.read_size(self.cols_var.get(), "Columns")

        errors = [error for error in (rows_error, cols_error) if error]
        if errors:
            self.show_message("\n".join(errors), "error")
            return

        rows, rows_notice = to_odd(rows, "Rows")
        cols, cols_notice = to_odd(cols, "Columns")

        # Mirror the corrected (odd) values back into the fields.
        self.rows_var.set(str(rows))
        self.cols_var.set(str(cols))

        difficulty = self.difficulty.get()
        self.app.settings.update(rows=rows, cols=cols, difficulty=difficulty)

        # A custom run is independent of the tiered challenge progression.
        self.app.active_challenge = None

        summary = f"Saved: {rows} rows x {cols} columns — {difficulty}."

        notices = [notice for notice in (rows_notice, cols_notice) if notice]
        if notices:
            self.show_message("\n".join(notices + [summary]), "info")
        else:
            self.show_message(summary, "success")

        # Valid settings: hand over to the gameplay screen, which builds the maze.
        self.app.show_screen("gameplay")


# ---------------------------------------------------------------------------
# Maze generation: DFS + recursive backtracking
# ---------------------------------------------------------------------------
DIRECTIONS = ((-1, 0), (1, 0), (0, -1), (0, 1))


class MazeGrid:
    """Odd-sized maze carved with depth-first search / recursive backtracking.

    Uses the classic layout where corridors sit on odd rows and columns and
    every other index is wall:

        * size: rows x cols (both odd, enforced by the Settings screen)
        * start cell: (1, 1)
        * goal cell:  the corridor cell farthest from the start (BFS)
        * walls[row][col] is True for a wall, False for a corridor

    The result is a "perfect" maze: exactly one path between any two cells.
    """

    def __init__(self, rows, cols, rng=None):
        if rows % 2 == 0 or cols % 2 == 0:
            raise ValueError("Maze dimensions must be odd")
        if rows < MAZE_MIN_SIZE or cols < MAZE_MIN_SIZE:
            raise ValueError(f"Maze dimensions must be at least {MAZE_MIN_SIZE}")

        self.rows = rows
        self.cols = cols
        self.rng = rng or random.Random()

        self.start = (1, 1)
        self.goal = (rows - 2, cols - 2)   # provisional; replaced by generate()

        # Start with a solid block of wall; the DFS carves corridors into it.
        self.walls = [[True] * cols for _ in range(rows)]
        self.generate()

    def generate(self):
        """Entry point for the recursive backtracking carve."""
        self.carve(*self.start)

        # The goal is always the deepest corridor: no reachable cell lies
        # farther from the start than this one.
        self.goal = self.farthest_cell(self.start)

    def farthest_cell(self, start):
        """BFS over the real grid and return the deepest corridor cell.

        Movement is one cell at a time (like the player and A*), so carved
        passages count as steps and blocked walls are never crossed.  Only
        corridor cells are considered, because that is where markers sit.
        """
        queue = deque([start])
        distance = {start: 0}
        farthest = start

        while queue:
            cell = queue.popleft()
            if self.is_cell(*cell) and distance[cell] > distance[farthest]:
                farthest = cell

            row, col = cell
            for d_row, d_col in DIRECTIONS:
                neighbour = (row + d_row, col + d_col)

                if neighbour in distance:
                    continue
                if not (0 <= neighbour[0] < self.rows and 0 <= neighbour[1] < self.cols):
                    continue
                if self.walls[neighbour[0]][neighbour[1]]:
                    continue

                distance[neighbour] = distance[cell] + 1
                queue.append(neighbour)

        return farthest

    def carve(self, row, col):
        """Carve the current cell, then recurse into each unvisited neighbour.

        Recursion depth is bounded by the number of cells (max 20*20 = 400
        for a 41x41 maze), well inside Python's default limit.
        """
        self.walls[row][col] = False

        directions = list(DIRECTIONS)
        self.rng.shuffle(directions)

        for d_row, d_col in directions:
            next_row = row + d_row * 2
            next_col = col + d_col * 2

            if not self.is_cell(next_row, next_col):
                continue
            if not self.walls[next_row][next_col]:
                continue                      # already carved -> visited

            # Knock down the wall between the two cells, then recurse.
            self.walls[row + d_row][col + d_col] = False
            self.carve(next_row, next_col)

    def is_cell(self, row, col):
        """True when (row, col) is a corridor cell: odd and inside the border."""
        return (
            0 < row < self.rows - 1
            and 0 < col < self.cols - 1
            and row % 2 == 1
            and col % 2 == 1
        )

    def is_wall(self, row, col):
        return self.walls[row][col]

    @classmethod
    def from_state(cls, rows, cols, walls, start, goal):
        """Rebuild a maze from a saved snapshot without carving a new one.

        Used by "Replay Same Maze" so the exact walls, start and goal return
        without running the DFS generator again.
        """
        maze = cls.__new__(cls)
        maze.rows = rows
        maze.cols = cols
        maze.rng = random.Random()
        maze.start = tuple(start)
        maze.goal = tuple(goal)
        maze.walls = [list(row) for row in walls]
        return maze


def astar_path(maze, start, goal):
    """A* over corridor cells using the Manhattan heuristic.

    Module level so both Gameplay and Results can solve the same maze.
    Returns the path with ``start`` first and ``goal`` last, or ``[]`` when
    the goal cannot be reached.
    """
    if maze is None:
        return []

    start, goal = tuple(start), tuple(goal)
    if start == goal:
        return [start]

    def manhattan(cell):
        return abs(cell[0] - goal[0]) + abs(cell[1] - goal[1])

    open_set = [(manhattan(start), 0, start)]
    came_from = {start: None}
    best_cost = {start: 0}

    while open_set:
        _, cost, current = heapq.heappop(open_set)

        if current == goal:
            path = []
            cell = goal
            while cell is not None:
                path.append(cell)
                cell = came_from[cell]
            path.reverse()
            return path

        if cost > best_cost.get(current, float("inf")):
            continue  # stale entry left behind by a cheaper route

        row, col = current
        for d_row, d_col in ((-1, 0), (1, 0), (0, -1), (0, 1)):
            neighbour = (row + d_row, col + d_col)

            if not 0 <= neighbour[0] < maze.rows:
                continue
            if not 0 <= neighbour[1] < maze.cols:
                continue
            if maze.is_wall(*neighbour):
                continue

            step_cost = cost + 1
            if step_cost >= best_cost.get(neighbour, float("inf")):
                continue

            best_cost[neighbour] = step_cost
            came_from[neighbour] = current
            heapq.heappush(open_set, (step_cost + manhattan(neighbour), step_cost, neighbour))

    return []


# ---------------------------------------------------------------------------
# Gameplay
# ---------------------------------------------------------------------------
class GameplayScreen(Screen):
    title = "Gameplay"

    def build(self):
        self.grid_rowconfigure(1, weight=1)
        self.grid_columnconfigure(0, weight=1)

        # --- header ----------------------------------------------------------
        header = tk.Frame(self, bg=COLOR_BG)
        header.grid(row=0, column=0, sticky="ew", padx=40, pady=(24, 10))

        tk.Label(
            header,
            text="Gameplay",
            font=HEADING_FONT,
            bg=COLOR_BG,
            fg=COLOR_TEXT_STRONG,
        ).pack(side="left")

        tk.Label(
            header,
            text="Guide the blue square to the red goal",
            font=SMALL_FONT,
            bg=COLOR_BG,
            fg=COLOR_MUTED,
        ).pack(side="left", padx=(14, 0))

        # --- maze canvas ------------------------------------------------------
        self.maze_area = tk.Frame(
            self,
            bg=COLOR_PANEL,
            highlightbackground=COLOR_BORDER,
            highlightthickness=1,
        )
        self.maze_area.grid(row=1, column=0, sticky="nsew", padx=40)
        self.maze_area.grid_rowconfigure(0, weight=1)
        self.maze_area.grid_columnconfigure(0, weight=1)

        self.canvas = tk.Canvas(
            self.maze_area,
            bg=COLOR_PANEL_ALT,
            highlightthickness=0,
            bd=0,
        )
        self.canvas.grid(row=0, column=0, sticky="nsew")
        self.canvas.bind("<Configure>", self._on_canvas_resize)

        self._resize_job = None
        self.maze = None

        # --- player state ------------------------------------------------------
        self.player = None
        self.moves = 0
        self._player_item = None
        self._player_origin = None   # (x, y, size) of the persistent player item
        self._start_item = None
        self._goal_item = None
        self._layout = None
        self.app.bind("<Key>", self.on_key)

        # --- right-hand dashboard -----------------------------------------------
        sidebar = tk.Frame(
            self,
            bg=COLOR_PANEL,
            width=280,
            highlightbackground=COLOR_BORDER,
            highlightthickness=1,
        )
        sidebar.grid(row=1, column=1, sticky="nsew", padx=(0, 40))
        sidebar.grid_propagate(False)
        # The sidebar's child is packed, so this is the propagation flag that
        # actually keeps the dashboard at its designed 280px width.
        sidebar.pack_propagate(False)

        inner = tk.Frame(sidebar, bg=COLOR_PANEL, padx=20, pady=10)
        inner.pack(fill="both", expand=True)

        section_label(inner, "DASHBOARD")

        status_head = tk.Frame(inner, bg=COLOR_PANEL)
        status_head.pack(fill="x", pady=(3, 0))

        tk.Label(
            status_head,
            text="Status",
            font=(FONT_FAMILY, 10),
            bg=COLOR_PANEL,
            fg=COLOR_MUTED,
            anchor="w",
        ).pack(side="left")

        self.status_pill = tk.Label(
            status_head,
            text="PLAYING",
            font=(FONT_FAMILY, 9, "bold"),
            bg=COLOR_PANEL_ALT,
            fg=COLOR_SUCCESS,
            padx=8,
            pady=2,
        )
        self.status_pill.pack(side="right")

        stats = tk.Frame(inner, bg=COLOR_PANEL)
        stats.pack(fill="x", pady=(8, 0))
        stats.grid_columnconfigure(0, weight=1)

        def stat_row(row, text):
            """One label/value line; returns the value label."""
            tk.Label(
                stats,
                text=text,
                font=(FONT_FAMILY, 9),
                bg=COLOR_PANEL,
                fg=COLOR_MUTED,
                anchor="w",
            ).grid(row=row, column=0, sticky="w", pady=1)

            value = tk.Label(
                stats,
                text="—",
                font=(FONT_FAMILY, 11, "bold"),
                bg=COLOR_PANEL,
                fg=COLOR_TEXT_STRONG,
                anchor="e",
            )
            value.grid(row=row, column=1, sticky="e", pady=1)
            return value

        self.moves_label = stat_row(0, "Moves")
        self.time_label = stat_row(1, "Time")
        self.hints_label = stat_row(2, "Hints Used")
        self.hints_used_label = self.hints_label
        self.stat_labels = {
            "DIFFICULTY": stat_row(3, "Difficulty"),
            "MAZE": stat_row(4, "Maze"),
        }
        self.stat_labels["HINTS"] = self.hints_label
        self.stat_labels["HINTS USED"] = self.hints_label
        self.stat_labels["hints_used"] = self.hints_label
        self.stat_labels["hints"] = self.hints_label
        self.hints_used = 0

        hline(inner, pad_y=6)

        section_label(inner, "ACTIONS")

        actions = tk.Frame(inner, bg=COLOR_PANEL)
        actions.pack(fill="x", pady=(6, 0))

        self.action_buttons = {}
        for text, command, variant in (
            ("Hint", self.show_hint, "secondary"),
            ("AI Solve", self.ai_solve, "secondary"),
            ("Pause", self.toggle_pause, "secondary"),
            ("Restart", self.restart_game, "primary"),
            ("Main Menu", self.leave_game, "danger"),
        ):
            button = MenuButton(
                actions,
                text,
                command=command,
                variant=variant,
                width=18,
                font=(FONT_FAMILY, 11, "bold"),
                pady=3,
            )
            button.pack(fill="x", pady=0)
            self.action_buttons[text] = button

        self.pause_button = self.action_buttons["Pause"]

        tk.Label(
            inner,
            text="WASD / Arrows move  ·  H hint  ·  ENTER solve  ·  P pause",
            font=(FONT_FAMILY, 8),
            bg=COLOR_PANEL,
            fg=COLOR_MUTED,
            justify="left",
            anchor="w",
            wraplength=236,
        ).pack(side="bottom", fill="x", pady=(8, 0))

        # --- run state (timer, hint, AI, pause) ----------------------------------
        self._timer_job = None
        self._started_at = None
        self._elapsed_base = 0.0
        self._ai_job = None
        self._ai_path = []
        self._ai_items = {}
        self._ai_running = False
        self._ai_steps = 0
        self._finish_job = None
        self.player_path = []
        self.player_times = [0.0]   # seconds since run start, per player path cell
        self._hint_job = None
        self._hint_items = []
        self._completed = False
        self.elapsed_seconds = 0
        self._time_text = "00:00"
        # A* cache (bounded, per-maze) and reused optimal path: avoids repeated
        # solver work for hints, AI starts and completion on 41x41 mazes.
        self._astar_cache = {}
        self._astar_cache_key = None
        self._optimal_path_cached = None
        self._optimal_cache_key = None
        # Cached layout signature to skip no-op full redraws.
        self._last_layout = None
        self._draw_maze_id = None

        # Pause state and the maze snapshot used by "Replay Same Maze".
        self._paused = False
        self._pause_items = []
        self._maze_snapshot = None
        self._difficulty = self.app.settings["difficulty"]
        self._restart_dialog = None
        self._restart_was_paused = False

        # Dashboard shortcuts, bound separately so movement keys stay untouched.
        for sequence in (
            "<KeyPress-h>", "<KeyPress-H>",
            "<KeyPress-p>", "<KeyPress-P>",
            "<Return>", "<KP_Enter>",
        ):
            self.app.bind(sequence, self.on_shortcut, add="+")

    # -- maze ------------------------------------------------------------------
    def on_show(self):
        """Every visit builds a fresh maze from the stored Settings values."""
        self.generate_maze()
        self.start_run()

    def generate_maze(self):
        """Build a brand new DFS maze from the active challenge or Settings."""
        level = self.app.current_level()
        if level is not None:
            self.generate_random_maze(
                level["rows"],
                level["cols"],
                level["difficulty"],
            )
            return

        self.generate_random_maze(
            self.app.settings["rows"],
            self.app.settings["cols"],
            self.app.settings["difficulty"],
        )

    def generate_random_maze(self, rows, cols, difficulty):
        """Build a new DFS maze with explicit dimensions and difficulty."""
        self.apply_maze(MazeGrid(rows, cols), difficulty)

    def apply_maze(self, maze, difficulty):
        """Show ``maze`` and reset every per-run value (player, moves, paths)."""
        self.maze = maze
        self._difficulty = difficulty
        # New maze object -> invalidate cached solver results and layout.
        self._astar_cache = {}
        self._optimal_path_cached = None
        self._optimal_cache_key = None
        self._last_layout = None

        # The player starts on the start cell; the counter resets per maze.
        self.player = tuple(maze.start)
        self.player_path = [tuple(maze.start)]
        self.player_times = [0.0]
        self.moves = 0
        self.moves_label.configure(text="0")
        self.hints_used = 0
        self.hints_label.configure(text="0")

        self.stat_labels["MAZE"].configure(
            text=f"{maze.rows} × {maze.cols}"
        )
        self.stat_labels["DIFFICULTY"].configure(text=difficulty)

        self.save_maze_state()
        self.draw_maze()

    def save_maze_state(self):
        """Snapshot the current maze so it can be replayed without a new DFS."""
        if self.maze is None:
            self._maze_snapshot = None
            return

        self._maze_snapshot = {
            "rows": self.maze.rows,
            "cols": self.maze.cols,
            "walls": [row[:] for row in self.maze.walls],
            "start": tuple(self.maze.start),
            "goal": tuple(self.maze.goal),
            "difficulty": self._difficulty,
        }

    def restore_maze_state(self):
        """Reload the exact saved maze, or generate one if no snapshot exists."""
        snapshot = self._maze_snapshot
        if not snapshot:
            self.generate_maze()
            return

        maze = MazeGrid.from_state(
            snapshot["rows"],
            snapshot["cols"],
            snapshot["walls"],
            snapshot["start"],
            snapshot["goal"],
        )
        self.apply_maze(maze, snapshot["difficulty"])

    def _on_canvas_resize(self, _event=None):
        # Debounce: a single redraw after the window settles.
        if self._resize_job is not None:
            self.after_cancel(self._resize_job)
        self._resize_job = self.after(50, self.draw_maze)

    def draw_maze(self):
        """Paint the maze, centred, with square cells."""
        self._resize_job = None

        maze = self.maze
        if maze is None:
            return

        width = self.canvas.winfo_width()
        height = self.canvas.winfo_height()
        if width < 2 or height < 2:
            return  # not laid out yet - <Configure> calls us again

        layout = maze_layout(maze, width, height, padding=24)
        # Skip redundant full redraws: same maze + same layout + live markers.
        if (
            layout == getattr(self, "_layout", None)
            and self._player_item is not None
            and getattr(self, "_draw_maze_id", None) == id(maze)
        ):
            return

        canvas = self.canvas
        self.clear_hint()
        self.clear_ai_path()
        canvas.delete("all")
        self._player_item = None
        self._player_origin = None
        self._start_item = None
        self._goal_item = None
        self._layout = None
        draw_maze_cells(canvas, maze, layout)
        self._layout = layout
        self._draw_maze_id = id(maze)

        self._start_item = self.draw_marker(
            maze.start, COLOR_START, outline="#67e8f9"
        )
        self._goal_item = self.draw_marker(
            maze.goal, COLOR_DANGER, outline="#ff7b72", dot=True
        )
        self.draw_player()

        # A window resize during a solve must not erase the yellow route.
        if self._ai_running and self._ai_path:
            self.draw_ai_path([tuple(self.player)] + list(self._ai_path))

        # Keep the freeze overlay visible if the window is resized while paused.
        if self._paused:
            self.show_pause_overlay()

    def draw_marker(self, position, color, outline="", dot=False):
        """Rounded marker that still shows the white corridor around it."""
        return draw_cell_marker(
            self.canvas, self._layout, position, color, outline, goal=dot
        )

    # -- player movement -------------------------------------------------------
    KEY_MOVES = {
        "w": (-1, 0), "W": (-1, 0),
        "s": (1, 0), "S": (1, 0),
        "a": (0, -1), "A": (0, -1),
        "d": (0, 1), "D": (0, 1),
        "Up": (-1, 0), "Down": (1, 0),
        "Left": (0, -1), "Right": (0, 1),
    }

    def on_key(self, event):
        """WASD / arrow keys move the player while gameplay is on screen."""
        if self.app.current_screen != "gameplay":
            return None
        if self._paused or self._ai_running:
            return "break"   # paused, or the solver owns the player

        step = self.KEY_MOVES.get(event.keysym)
        if step is None:
            return None

        self.move_player(*step)
        return "break"

    def move_player(self, d_row, d_col):
        """Step one cell, unless paused, a wall or the border is in the way."""
        if self._paused or self.maze is None or self.player is None:
            return

        # Only single grid steps are valid, so a move can never jump a wall.
        if abs(d_row) + abs(d_col) != 1:
            return

        row, col = self.player
        new_row, new_col = row + d_row, col + d_col

        if not (0 <= new_row < self.maze.rows and 0 <= new_col < self.maze.cols):
            return
        if self.maze.is_wall(new_row, new_col):
            return

        self.player = (new_row, new_col)
        self.moves += 1
        self.moves_label.configure(text=str(self.moves))
        self.redraw_player()

        # Reaching the goal completes the run immediately - no polling timer.
        if (new_row, new_col) == tuple(self.maze.goal):
            self.complete_maze()

    def player_box(self):
        """Top-left corner and side length of the player square, in pixels."""
        return path_box(self._layout, *self.player, extra=1)

    def draw_player(self):
        """Blue rounded square with a soft halo, inset inside the current cell."""
        if self.player is None or self._layout is None:
            return

        x0, y0, size = self.player_box()
        halo = max(1, min(3, size // 10))

        # Halo first, then the body on top: the visible ring keeps the player
        # easy to track on large mazes without changing its cell footprint.
        rounded_rect(
            self.canvas,
            x0 - halo,
            y0 - halo,
            x0 + size + halo,
            y0 + size + halo,
            max(3, size // 5),
            fill=COLOR_PLAYER_GLOW,
            outline="",
            tags=("player", "player_halo"),
        )
        self._player_item = rounded_rect(
            self.canvas,
            x0,
            y0,
            x0 + size,
            y0 + size,
            max(2, size // 6),
            fill=COLOR_PLAYER,
            outline="#dbeafe",
            width=max(1, min(2, size // 14)),
            tags=("player", "player_body"),
        )
        self._player_origin = (x0, y0, size)

    def redraw_player(self):
        """Move the player group; never rebuild the maze or the marker.

        The visited cell is stored here too, so the Results screen can replay
        the exact route the player walked.
        """
        current = tuple(self.player)
        if not self.player_path or self.player_path[-1] != current:
            self.player_path.append(current)
            try:
                self.player_times.append(self.current_elapsed())
            except Exception:
                self.player_times.append(float(len(self.player_times)))

        if self._player_item is None or self._player_origin is None:
            self.draw_player()
            return

        x0, y0, size = self.player_box()
        old_x, old_y, old_size = self._player_origin

        # The layout only changes on a full redraw, but guard the fallback so
        # the rounded shape can never be stretched by a coordinate rewrite.
        if size != old_size:
            self.canvas.delete("player")
            self._player_item = None
            self._player_origin = None
            self.draw_player()
            return

        if x0 != old_x or y0 != old_y:
            self.canvas.move("player", x0 - old_x, y0 - old_y)
            self._player_origin = (x0, y0, size)

    # -- live timer --------------------------------------------------------------
    def start_timer(self):
        """(Re)start the run clock from zero; ticks once per second."""
        self.stop_timer()

        self._elapsed_base = 0.0
        self.elapsed_seconds = 0
        self._time_text = "00:00"
        self.time_label.configure(text=self._time_text)
        self.resume_timer()

    def current_elapsed(self):
        """Seconds played so far, including the current running segment."""
        running = 0.0
        if self._started_at is not None:
            running = time.monotonic() - self._started_at
        return self._elapsed_base + running

    def pause_timer(self):
        """Freeze the clock, keeping the seconds already played."""
        if self._started_at is not None:
            self._elapsed_base = self.current_elapsed()
            self._started_at = None

        if self._timer_job is not None:
            self.after_cancel(self._timer_job)
            self._timer_job = None

        self.update_elapsed()

    def resume_timer(self):
        """Continue a frozen clock without resetting its value."""
        if self._started_at is not None:
            return

        self._started_at = time.monotonic()
        if self._timer_job is None:
            self._timer_job = self.after(1000, self._tick_timer)

    def _tick_timer(self):
        self._timer_job = None
        self.update_elapsed()
        if self._started_at is not None:
            self._timer_job = self.after(1000, self._tick_timer)

    def update_elapsed(self):
        """Recompute the elapsed time from a monotonic clock (no drift)."""
        self.elapsed_seconds = max(0, int(self.current_elapsed()))
        text = self.format_time(self.elapsed_seconds)

        if text != self._time_text:
            self._time_text = text
            self.time_label.configure(text=text)

    def stop_timer(self):
        """Stop ticking and remember the elapsed time of the current run."""
        if self._started_at is not None:
            self._elapsed_base = self.current_elapsed()
            self._started_at = None

        if self._timer_job is not None:
            self.after_cancel(self._timer_job)
            self._timer_job = None

    @staticmethod
    def format_time(total_seconds):
        minutes, seconds = divmod(int(total_seconds), 60)
        hours, minutes = divmod(minutes, 60)

        if hours:
            return f"{hours:02d}:{minutes:02d}:{seconds:02d}"
        return f"{minutes:02d}:{seconds:02d}"

    # -- run lifecycle -----------------------------------------------------------
    def start_run(self):
        """Called whenever the gameplay screen appears: fresh clock and run."""
        self.stop_run()

        self._completed = False
        self._ai_path = []
        self._ai_steps = 0
        self._paused = False
        self.hide_pause_overlay()
        self.set_pause_label("Pause")
        self.hints_used = 0
        self.hints_label.configure(text="0")
        self.player_times = [0.0]

        self.set_status("Playing", COLOR_SUCCESS)
        self.set_controls_enabled(True)

        self.start_timer()

    def stop_run(self):
        """Cancel the clock, any AI run and the hint, and leave pause mode."""
        self.stop_timer()

        for attribute in ("_ai_job", "_hint_job", "_finish_job"):
            job = getattr(self, attribute, None)
            if job is not None:
                self.after_cancel(job)
                setattr(self, attribute, None)

        self._ai_path = []
        self._ai_running = False
        self.clear_hint()
        self.clear_ai_path()

        # A new run always starts unpaused, even after leaving mid-pause.
        self._paused = False
        self.hide_pause_overlay()
        self.set_pause_label("Pause")
        self.set_controls_enabled(True)

    def complete_maze(self):
        """Stop the clock, then show Player Complete (human) or AI Complete."""
        if self._completed:
            return

        ai_finished = self._ai_running

        self._completed = True
        self.update_elapsed()
        self.stop_run()
        self.set_status("Completed", COLOR_ACCENT)

        # --- run statistics ---------------------------------------------------
        # Reuse the cached start->goal route when available (no second solve).
        optimal_path = getattr(self, "_optimal_path_cached", None)
        if optimal_path is None or not optimal_path or tuple(optimal_path[0]) != tuple(self.maze.start):
            optimal_path = self.astar(self.maze.start, self.maze.goal)
        optimal_length = max(0, len(optimal_path) - 1)
        player_path = [tuple(cell) for cell in self.player_path]
        if not player_path:
            player_path = [tuple(self.maze.start)]

        player_times = list(getattr(self, "player_times", [0.0]))
        # Keep times parallel to the path; pad/trim defensively.
        if len(player_times) < len(player_path):
            last = player_times[-1] if player_times else 0.0
            player_times.extend([last] * (len(player_path) - len(player_times)))
        else:
            player_times = player_times[: len(player_path)]
        if not player_times:
            player_times = [0.0]
        player_times[0] = 0.0

        try:
            hints_used = int(getattr(self, "hints_used", 0) or 0)
        except (TypeError, ValueError):
            hints_used = 0

        player_length = max(0, len(player_path) - 1)
        efficiency = (optimal_length / player_length * 100.0) if player_length else 0.0

        challenge_id = self.app.active_challenge
        challenge_level = LEVEL_BY_ID.get(challenge_id)

        # Available to Player Complete, Results and AI Complete as last_result.
        result = {
            "moves": self.moves,
            "seconds": self.elapsed_seconds,
            "time": self.format_time(self.elapsed_seconds),
            "difficulty": self._difficulty,
            "rows": self.maze.rows,
            "cols": self.maze.cols,
            "ai": ai_finished,
            "ai_steps": self._ai_steps if ai_finished else None,
            "maze": self.maze,
            "player_path": player_path,
            "player_times": player_times,
            "optimal_path": [tuple(cell) for cell in optimal_path],
            "hints_used": hints_used,
            "hints": hints_used,
            "player_length": player_length,
            "optimal_length": optimal_length,
            "efficiency": efficiency,
            "challenge": challenge_level["id"] if challenge_level else None,
            "challenge_name": challenge_level["name"] if challenge_level else None,
            "challenge_color": challenge_level["color"] if challenge_level else None,
            "newly_unlocked": None,
            "newly_unlocked_name": None,
            "next_challenge": None,
            "next_challenge_name": None,
            "progress_changed": False,
            "new_record": False,
            "new_records": {"best_time": False, "best_moves": False, "best_efficiency": False},
            "newly_unlocked_achievements": [],
            "new_achievements": [],
        }

        # Only a human win in a standard challenge advances progression.
        if challenge_level and not ai_finished:
            progression = self.app.complete_challenge(challenge_level["id"])
            result.update(
                newly_unlocked=progression["newly_unlocked"],
                newly_unlocked_name=progression["newly_unlocked_name"],
                next_challenge=progression["next_challenge"],
                next_challenge_name=progression["next_challenge_name"],
                progress_changed=progression["changed"],
            )

        # Best records (challenge levels / custom overall) + achievements.
        # Custom wins never touch challenge progression or level records.
        if not ai_finished:
            _before = set(self.app.achievements)
            record_summary = self.app.update_best_records(result)
            _after_records = set(self.app.achievements)
            _from_records = [aid for aid in ACHIEVEMENT_ORDER if aid in _after_records and aid not in _before]
            result["new_records"] = record_summary
            result["new_record"] = bool(record_summary.get("new_record"))
            # Snapshot of the (possibly updated) records for this run kind.
            level_id = result.get("challenge")
            if level_id:
                result["best_record"] = self.app.record_for_level(level_id)
                result["records"] = self.app.record_for_level(level_id)
                result["custom"] = False
            else:
                result["custom"] = True
                result["best_record"] = self.app.record_for_level(CUSTOM_LEVEL_ID)
                result["records"] = self.app.record_for_level(CUSTOM_LEVEL_ID)
                result["best_overall"] = self.app.record_for_level(CUSTOM_LEVEL_ID)
            newly = self.app.evaluate_achievements_for_result(result)
            for _aid in _from_records:
                if _aid not in newly:
                    newly.append(_aid)
            result["newly_unlocked_achievements"] = list(newly)
            result["new_achievements"] = list(newly)
            result["achievements"] = sorted(
                list(self.app.achievements),
                key=lambda aid: ACHIEVEMENT_ORDER.index(aid) if aid in ACHIEVEMENT_ORDER else 99,
            )
        else:
            result["best_record"] = None
            result["records"] = None
            result["custom"] = result.get("challenge") is None

        self.app.last_result = result

        if ai_finished:
            # Short pause so the player square is seen landing on the goal.
            if self._finish_job is not None:
                try:
                    self.after_cancel(self._finish_job)
                except tk.TclError:
                    pass
                self._finish_job = None
            self._finish_job = self.after(380, self._show_ai_complete)
        elif challenge_level:
            self.app.show_screen("challenge_complete")
        else:
            self.app.show_screen("player_complete")

    def _show_ai_complete(self):
        self._finish_job = None
        if self._completed and self.app.current_screen == "gameplay":
            self.app.show_screen("ai_complete")

    # -- pause / resume ------------------------------------------------------------
    def toggle_pause(self):
        """Pause button and the P key share this exact logic."""
        if self.app.current_screen != "gameplay" or self._completed:
            return
        if self.maze is None or self._restart_dialog is not None:
            return

        if self._paused:
            self.resume_game()
        else:
            self.pause_game()

    def pause_game(self):
        """Freeze the clock, movement, hints and the AI animation."""
        if self._paused or self._completed or self.maze is None:
            return

        self._paused = True
        self.pause_timer()

        # Freeze the solver mid-route; resume_game() continues it.
        if self._ai_job is not None:
            self.after_cancel(self._ai_job)
            self._ai_job = None

        self.clear_hint()
        self.set_pause_label("Resume")
        self.set_status("Paused", COLOR_MUTED)
        self.set_controls_enabled(True)   # Hint / AI stay off while paused
        self.show_pause_overlay()

    def resume_game(self):
        """Continue the clock and controls without resetting any run data."""
        if not self._paused or self._completed:
            return

        self._paused = False
        self.hide_pause_overlay()
        self.set_pause_label("Pause")
        self.resume_timer()
        self.set_controls_enabled(not self._ai_running)

        if self._ai_running:
            self.set_status("AI Solving", COLOR_AI)
            if self._ai_job is not None:
                try:
                    self.after_cancel(self._ai_job)
                except tk.TclError:
                    pass
                self._ai_job = None
            self._ai_job = self.after(self.AI_STEP_DELAY, self.run_ai_step)
        else:
            self.set_status("Playing", COLOR_SUCCESS)

    def set_pause_label(self, text):
        button = getattr(self, "pause_button", None)
        if button is not None:
            button.configure(text=text)

    def show_pause_overlay(self):
        """Centred GAME PAUSED card above the maze."""
        self.hide_pause_overlay()

        if self._layout is None:
            return

        canvas = self.canvas
        width = canvas.winfo_width()
        height = canvas.winfo_height()
        if width < 2 or height < 2:
            return

        overlay = canvas.create_rectangle(
            0, 0, width, height,
            fill="#05080c", stipple="gray50", outline="",
        )

        panel_w = min(520, max(300, width - 120))
        panel_h = 158
        x0 = (width - panel_w) // 2
        y0 = (height - panel_h) // 2

        panel = rounded_rect(
            canvas,
            x0, y0, x0 + panel_w, y0 + panel_h, 20,
            fill=COLOR_PANEL, outline=COLOR_ACCENT, width=2,
        )
        title = canvas.create_text(
            width // 2, height // 2 - 22,
            text="GAME PAUSED",
            fill=COLOR_TEXT_STRONG,
            font=(FONT_FAMILY, 24, "bold"),
        )
        subtitle = canvas.create_text(
            width // 2, height // 2 + 26,
            text="Press P to Resume",
            fill=COLOR_MUTED,
            font=(FONT_FAMILY, 12),
        )
        self._pause_items = [overlay, panel, title, subtitle]

    def hide_pause_overlay(self):
        for item in list(self._pause_items):
            try:
                self.canvas.delete(item)
            except tk.TclError:
                pass
        self._pause_items = []

    # -- smart restart -------------------------------------------------------------
    def restart_game(self):
        """Ask first: replay the same maze, generate a new one, or cancel."""
        if self.app.current_screen != "gameplay" or self._completed:
            return
        if self._restart_dialog is not None:
            try:
                self._restart_dialog.lift()
                self._restart_dialog.focus_force()
            except tk.TclError:
                pass
            return

        self._restart_was_paused = self._paused
        if not self._paused:
            self.pause_game()
        self._open_restart_dialog()

    def _open_restart_dialog(self):
        dialog = tk.Toplevel(self.app)
        dialog.title("Restart Maze")
        dialog.configure(bg=COLOR_BG)
        dialog.transient(self.app)
        dialog.resizable(False, False)
        dialog.protocol("WM_DELETE_WINDOW", self._cancel_restart)

        icon = getattr(self.app, "_icon_path", None)
        if icon:
            try:
                dialog.iconbitmap(icon)
            except tk.TclError:
                pass

        card = tk.Frame(
            dialog,
            bg=COLOR_PANEL,
            padx=30,
            pady=24,
            highlightbackground=COLOR_BORDER,
            highlightthickness=1,
        )
        card.pack(padx=2, pady=2)

        tk.Label(
            card,
            text="Restart Maze",
            font=(FONT_FAMILY, 22, "bold"),
            bg=COLOR_PANEL,
            fg=COLOR_TEXT_STRONG,
        ).pack(anchor="w")

        tk.Label(
            card,
            text="Choose an option:",
            font=BODY_FONT,
            bg=COLOR_PANEL,
            fg=COLOR_MUTED,
        ).pack(anchor="w", pady=(6, 14))

        MenuButton(
            card,
            "Replay Same Maze",
            command=self._restart_same_maze,
            variant="primary",
            width=26,
            font=(FONT_FAMILY, 12, "bold"),
            pady=7,
        ).pack(fill="x", pady=(0, 6))

        MenuButton(
            card,
            "New Random Maze",
            command=self._restart_new_maze,
            variant="secondary",
            width=26,
            font=(FONT_FAMILY, 12, "bold"),
            pady=7,
        ).pack(fill="x", pady=(0, 6))

        MenuButton(
            card,
            "Cancel",
            command=self._cancel_restart,
            variant="danger",
            width=26,
            font=(FONT_FAMILY, 12, "bold"),
            pady=7,
        ).pack(fill="x")

        tk.Label(
            card,
            text="Same Maze keeps the layout. New Maze keeps size and difficulty.",
            font=SMALL_FONT,
            bg=COLOR_PANEL,
            fg=COLOR_MUTED,
            wraplength=320,
            justify="left",
        ).pack(anchor="w", pady=(14, 0))

        dialog.bind("<Escape>", self._cancel_restart_event)
        dialog.update_idletasks()

        width = dialog.winfo_reqwidth()
        height = dialog.winfo_reqheight()
        x = self.app.winfo_rootx() + max(0, (self.app.winfo_width() - width) // 2)
        y = self.app.winfo_rooty() + max(0, (self.app.winfo_height() - height) // 2)
        dialog.geometry(f"+{x}+{y}")

        self._restart_dialog = dialog
        try:
            dialog.grab_set()
        except tk.TclError:
            pass
        dialog.focus_force()

    def _close_restart_dialog(self):
        dialog = self._restart_dialog
        self._restart_dialog = None
        if dialog is None:
            return
        try:
            dialog.grab_release()
        except tk.TclError:
            pass
        try:
            dialog.destroy()
        except tk.TclError:
            pass

    def _restart_same_maze(self):
        self._close_restart_dialog()
        self.stop_run()
        self.restore_maze_state()
        self.start_run()

    def _restart_new_maze(self):
        self._close_restart_dialog()
        self.stop_run()

        snapshot = self._maze_snapshot
        if snapshot:
            # Keep the current maze's size and difficulty, not stale settings.
            self.generate_random_maze(
                snapshot["rows"],
                snapshot["cols"],
                snapshot["difficulty"],
            )
        else:
            self.generate_maze()

        self.start_run()

    def _cancel_restart(self):
        was_paused = self._restart_was_paused
        self._close_restart_dialog()
        if not was_paused:
            self.resume_game()

    def _cancel_restart_event(self, _event=None):
        self._cancel_restart()
        return "break"

    # -- dashboard actions ---------------------------------------------------------
    def leave_game(self):
        self.stop_run()
        self.set_status("Playing", COLOR_SUCCESS)
        self.app.show_screen("home")

    def on_hide(self):
        """Leaving Gameplay must not leave timers or animations running."""
        self._close_restart_dialog()
        self.stop_run()
        if self._resize_job is not None:
            self.after_cancel(self._resize_job)
            self._resize_job = None

    # -- dashboard helpers ---------------------------------------------------------
    def set_status(self, text, color=COLOR_SUCCESS):
        """Update the status pill: Playing / AI Solving / Completed."""
        pill = getattr(self, "status_pill", None)
        if pill is not None:
            pill.configure(text=text.upper(), fg=color)

    def set_controls_enabled(self, enabled):
        """Lock Hint / AI Solve while paused or solving; Pause stays available."""
        locked = not enabled or self._paused or self._completed
        state = "disabled" if locked else "normal"

        buttons = getattr(self, "action_buttons", {})
        for name in ("Hint", "AI Solve"):
            button = buttons.get(name)
            if button is not None:
                button.configure(state=state)

        pause_button = getattr(self, "pause_button", None)
        if pause_button is not None:
            pause_button.configure(state="disabled" if self._completed else "normal")

    def find_path(self, start, goal):
        """Breadth-first search: shortest corridor path, start cell first."""
        if self.maze is None:
            return []

        queue = deque([start])
        came_from = {start: None}

        while queue:
            cell = queue.popleft()
            if cell == goal:
                break

            row, col = cell
            for d_row, d_col in ((-1, 0), (1, 0), (0, -1), (0, 1)):
                neighbour = (row + d_row, col + d_col)

                if neighbour in came_from:
                    continue
                if not 0 <= neighbour[0] < self.maze.rows:
                    continue
                if not 0 <= neighbour[1] < self.maze.cols:
                    continue
                if self.maze.is_wall(*neighbour):
                    continue

                came_from[neighbour] = cell
                queue.append(neighbour)

        if goal not in came_from:
            return []

        path = []
        cell = goal
        while cell is not None:
            path.append(cell)
            cell = came_from[cell]

        path.reverse()
        return path

    # -- A* pathfinding ------------------------------------------------------------
    HINT_CELLS = 3
    AI_STEP_DELAY = 45     # ms between animated steps
    AI_START_DELAY = 260   # ms the yellow route is shown before moving

    def astar(self, start, goal):
        """A* over corridor cells with a bounded per-maze cache.

        Repeated hints/AI starts from the same cell reuse the cached path
        instead of re-running the solver on large mazes.
        """
        if self.maze is None:
            return []
        start = tuple(start)
        goal = tuple(goal)
        cache_key = (id(self.maze), self.maze.rows, self.maze.cols, tuple(self.maze.start), tuple(self.maze.goal))
        if getattr(self, "_astar_cache_key", None) != cache_key:
            self._astar_cache = {}
            self._astar_cache_key = cache_key
        key = (start, goal)
        cached = self._astar_cache.get(key)
        if cached is not None:
            return list(cached)
        path = astar_path(self.maze, start, goal)
        # Bound memory: keep at most 32 recent entries.
        if len(self._astar_cache) >= 32:
            self._astar_cache.clear()
        self._astar_cache[key] = tuple(path)
        # Reuse the start->goal optimal route for completion/Results.
        if start == tuple(self.maze.start) and goal == tuple(self.maze.goal):
            self._optimal_path_cached = list(path)
            self._optimal_cache_key = cache_key
        return list(path)

    def show_hint(self):
        """Highlight the next three optimal cells, in orange, from the player."""
        if self.app.current_screen != "gameplay" or self._completed or self._paused:
            return
        if self._ai_running:
            return   # hints are locked while the solver animates
        if self.maze is None or self._layout is None:
            return

        path = self.astar(self.player, self.maze.goal)
        if len(path) < 2:
            return

        self.hints_used = int(getattr(self, "hints_used", 0) or 0) + 1
        self.hints_label.configure(text=str(self.hints_used))

        self.clear_hint()

        for row, col in path[1 : self.HINT_CELLS + 1]:
            x0, y0, size = path_box(self._layout, row, col, extra=1)
            item = rounded_rect(
                self.canvas,
                x0,
                y0,
                x0 + size,
                y0 + size,
                max(2, size // 6),
                fill=COLOR_HINT,
                outline="",
            )
            self._hint_items.append(item)

            # The start marker is drawn first, so sitting below it keeps the
            # hint underneath every marker (start, goal, dot and player).
            if self._start_item is not None:
                self.canvas.tag_lower(item, self._start_item)

        # Single expiry timer: clear any pending one first (no duplicates).
        if self._hint_job is not None:
            try:
                self.after_cancel(self._hint_job)
            except tk.TclError:
                pass
            self._hint_job = None
        self._hint_job = self.after(1600, self._expire_hint)

    def _expire_hint(self):
        self._hint_job = None
        self.clear_hint()

    def clear_hint(self):
        """Remove hint tiles and cancel the pending auto-hide timer."""
        if self._hint_job is not None:
            try:
                self.after_cancel(self._hint_job)
            except tk.TclError:
                pass
            self._hint_job = None

        for item in list(self._hint_items):
            try:
                self.canvas.delete(item)
            except tk.TclError:
                pass
        self._hint_items = []

    # -- AI solver -----------------------------------------------------------------
    def draw_ai_path(self, path):
        """Paint the A* route in yellow, underneath the player square."""
        self.clear_ai_path()

        if self._layout is None:
            return

        for row, col in path[1:]:
            x0, y0, size = path_box(self._layout, row, col, extra=1)

            item = rounded_rect(
                self.canvas,
                x0,
                y0,
                x0 + size,
                y0 + size,
                max(2, size // 6),
                fill=COLOR_AI,
                outline="",
            )

            # The start marker is drawn first, so lowering under it keeps the
            # whole route underneath the start, goal and player markers.
            if self._start_item is not None:
                self.canvas.tag_lower(item, self._start_item)
            else:
                self.canvas.tag_lower(item, "player")

            self._ai_items[(row, col)] = item

    def clear_ai_path(self):
        for item in list(self._ai_items.values()):
            try:
                self.canvas.delete(item)
            except tk.TclError:
                pass
        self._ai_items = {}

    def consume_ai_cell(self, cell):
        """Remove the yellow square the player has just stepped onto."""
        item = self._ai_items.pop(tuple(cell), None)
        if item is not None:
            try:
                self.canvas.delete(item)
            except tk.TclError:
                pass

    def ai_solve(self):
        """Animate the A* solution: show the yellow route, then walk it."""
        if self.app.current_screen != "gameplay" or self._completed or self._paused:
            return
        if self._ai_job is not None or self._ai_running:
            return
        if self.maze is None or self.player is None or self._layout is None:
            return

        path = self.astar(tuple(self.player), tuple(self.maze.goal))
        if len(path) < 2:
            return

        self.clear_hint()
        self._ai_running = True
        self._ai_path = path[1:]
        self._ai_steps = len(path) - 1
        self.set_status("AI Solving", COLOR_AI)
        self.set_controls_enabled(False)
        self.draw_ai_path(path)
        if self._ai_job is not None:
            try:
                self.after_cancel(self._ai_job)
            except tk.TclError:
                pass
            self._ai_job = None
        self._ai_job = self.after(self.AI_START_DELAY, self.run_ai_step)

    def run_ai_step(self):
        """One animated step towards the goal; reschedules itself."""
        self._ai_job = None

        if self._completed or self._paused or self.app.current_screen != "gameplay":
            return
        if self.maze is None or self.player is None:
            return

        if not self._ai_path:
            self.finish_ai()
            return

        current = tuple(self.player)
        row, col = self._ai_path[0]

        # If the player wandered off the route, recalculate from where they are.
        if abs(row - current[0]) + abs(col - current[1]) != 1:
            self._ai_path = self.astar(current, tuple(self.maze.goal))[1:]
            if not self._ai_path:
                self.finish_ai()
                return
            row, col = self._ai_path[0]

        self._ai_path.pop(0)
        self.consume_ai_cell((row, col))
        self.move_player(row - current[0], col - current[1])

        if self._ai_path and not self._completed and self._ai_job is None:
            self._ai_job = self.after(self.AI_STEP_DELAY, self.run_ai_step)

    def finish_ai(self):
        """Solver reached the goal (move_player may have completed it first)."""
        if not self._completed:
            self.complete_maze()

    def on_shortcut(self, event):
        """H = hint, ENTER = AI solve, P = pause/resume."""
        if self.app.current_screen != "gameplay":
            return None
        if self._restart_dialog is not None:
            return None

        keysym = event.keysym.lower()

        if keysym == "h":
            self.show_hint()
            return "break"
        if keysym == "p":
            self.toggle_pause()
            return "break"
        if keysym in ("return", "kp_enter"):
            self.ai_solve()
            return "break"

        return None


# ---------------------------------------------------------------------------
# Results
# ---------------------------------------------------------------------------
class ResultsScreen(Screen):
    title = "Results"

    REPLAY_DELAY = 90   # ms between replayed player steps (max)
    MIN_REPLAY_DELAY = 15
    REPLAY_TOTAL_MS = 4500   # long routes replay faster, but stay visible

    OPTIMAL_TOTAL_MS = 2600  # the yellow route animates a little quicker
    MIN_OPTIMAL_DELAY = 12

    def build(self):
        self.maze = None
        self.player_path = []
        self._layout = None
        self._resize_job = None
        self._replay_job = None
        self.replay_index = 0
        self._step_delay = self.REPLAY_DELAY
        self._start_item = None
        self._goal_item = None

        # Yellow A* route state.
        self._optimal_path = []
        self._optimal_items = []
        self._optimal_job = None
        self._optimal_index = 0
        self._optimal_delay = self.MIN_OPTIMAL_DELAY
        self._optimal_visible = False

        # Watch-my-run (timed replay) state.
        self.player_times = []
        self._replay_items = []
        self._watch_job = None
        self.watch_index = 0
        self.watch_speed = 1
        self._watch_item = None
        self._watch_origin = None
        self._watch_running = False
        self.watch_button = None
        self.speed_buttons = {}

        self.grid_rowconfigure(1, weight=1)
        self.grid_columnconfigure(0, weight=1)

        # --- header -----------------------------------------------------------
        header = tk.Frame(self, bg=COLOR_BG)
        header.grid(row=0, column=0, sticky="ew", padx=40, pady=(24, 10))

        tk.Label(
            header,
            text="Results",
            font=HEADING_FONT,
            bg=COLOR_BG,
            fg=COLOR_TEXT_STRONG,
        ).pack(side="left")

        tk.Label(
            header,
            text="Your route vs. the optimal route",
            font=SMALL_FONT,
            bg=COLOR_BG,
            fg=COLOR_MUTED,
        ).pack(side="left", padx=(14, 0))

        # --- body: replay on the left, summary on the right -------------------
        body = tk.Frame(self, bg=COLOR_BG)
        body.grid(row=1, column=0, sticky="nsew", padx=40, pady=(0, 26))
        body.grid_rowconfigure(0, weight=1)
        body.grid_columnconfigure(0, weight=1)

        panel = tk.Frame(
            body,
            bg=COLOR_PANEL,
            highlightbackground=COLOR_BORDER,
            highlightthickness=1,
        )
        panel.grid(row=0, column=0, sticky="nsew", padx=(0, 18))
        panel.grid_rowconfigure(1, weight=1)
        panel.grid_columnconfigure(0, weight=1)

        caption = tk.Frame(panel, bg=COLOR_PANEL)
        caption.grid(row=0, column=0, sticky="ew", padx=16, pady=(12, 0))

        tk.Label(
            caption,
            text="REPLAY",
            font=(FONT_FAMILY, 9, "bold"),
            bg=COLOR_PANEL,
            fg=COLOR_MUTED,
        ).pack(side="left")

        tk.Label(
            caption,
            text="your route",
            font=SMALL_FONT,
            bg=COLOR_PANEL,
            fg=COLOR_REPLAY,
        ).pack(side="left", padx=(8, 0))

        # Compact legend for both routes shown on this canvas.
        legend = tk.Frame(caption, bg=COLOR_PANEL)
        legend.pack(side="right")

        for text, color in (
            ("Green = Your Path", COLOR_REPLAY),
            ("Yellow = Optimal Path", COLOR_AI),
        ):
            entry = tk.Frame(legend, bg=COLOR_PANEL)
            entry.pack(side="left", padx=(12, 0))

            swatch = tk.Frame(entry, width=9, height=9, bg=color)
            swatch.pack(side="left", padx=(0, 5))
            swatch.pack_propagate(False)

            tk.Label(
                entry,
                text=text,
                font=SMALL_FONT,
                bg=COLOR_PANEL,
                fg=color,
            ).pack(side="left")

        self.canvas = tk.Canvas(
            panel, bg=COLOR_PANEL_ALT, highlightthickness=0, bd=0
        )
        self.canvas.grid(row=1, column=0, sticky="nsew")
        self.canvas.bind("<Configure>", self._on_canvas_resize)

        # Best records + achievements + NEW RECORD (under canvas replay).
        info_frame = tk.Frame(
            panel,
            bg=COLOR_PANEL,
            padx=12,
            pady=4,
            highlightbackground=COLOR_BORDER,
            highlightthickness=1,
        )
        info_frame.grid(row=2, column=0, sticky="ew", padx=12, pady=(6, 12))
        panel.grid_rowconfigure(2, weight=0)

        self.new_record_label = tk.Label(
            info_frame,
            text="",
            font=(FONT_FAMILY, 10, "bold"),
            bg=COLOR_PANEL,
            fg=COLOR_TEXT_STRONG,
            anchor="w",
        )
        self.new_record_label.pack(fill="x", anchor="w")
        # Alias names for discoverability.
        self.record_label = self.new_record_label
        self.new_record_banner = self.new_record_label

        self.records_label = tk.Label(
            info_frame,
            text="",
            font=(FONT_FAMILY, 9),
            bg=COLOR_PANEL,
            fg=COLOR_TEXT,
            anchor="w",
            justify="left",
            wraplength=540,
        )
        self.records_label.pack(fill="x", pady=(2, 0), anchor="w")
        self.best_records_label = self.records_label
        self.record_labels = self.records_label

        self.achievements_label = tk.Label(
            info_frame,
            text="",
            font=(FONT_FAMILY, 9),
            bg=COLOR_PANEL,
            fg=COLOR_TEXT,
            anchor="w",
            justify="left",
            wraplength=540,
        )
        self.achievements_label.pack(fill="x", pady=(2, 0), anchor="w")
        self.achievement_labels = self.achievements_label

        card = tk.Frame(
            body,
            bg=COLOR_PANEL,
            width=336,
            padx=16,
            pady=2,
            highlightbackground=COLOR_BORDER,
            highlightthickness=1,
        )
        card.grid(row=0, column=1, sticky="ns")
        card.grid_propagate(False)

        banner = tk.Frame(card, bg=COLOR_PANEL_ALT, padx=10, pady=2)
        banner.pack(fill="x")

        tk.Frame(banner, width=4, bg=COLOR_SUCCESS).pack(side="left", fill="y")

        banner_text = tk.Frame(banner, bg=COLOR_PANEL_ALT)
        banner_text.pack(side="left", fill="x", expand=True, padx=(10, 0))

        tk.Label(
            banner_text,
            text="MISSION COMPLETE",
            font=(FONT_FAMILY, 8, "bold"),
            bg=COLOR_PANEL_ALT,
            fg=COLOR_SUCCESS,
        ).pack(anchor="w")

        tk.Label(
            banner_text,
            text="YOU WIN",
            font=(FONT_FAMILY, 18, "bold"),
            bg=COLOR_PANEL_ALT,
            fg=COLOR_SUCCESS,
        ).pack(anchor="w")

        hline(card, pad_y=2)

        stats = tk.Frame(card, bg=COLOR_PANEL)
        stats.pack(fill="x")
        stats.grid_columnconfigure(0, weight=1)

        self.value_labels = {}
        for row, (label, key, color) in enumerate(
            (
                ("Moves", "moves", COLOR_TEXT_STRONG),
                ("Time", "time", COLOR_TEXT_STRONG),
                ("Your Path", "player_length", COLOR_REPLAY),
                ("Optimal Path", "optimal_length", COLOR_AI),
                ("Path Efficiency", "efficiency", COLOR_SUCCESS),
                ("Hints Used", "hints_used", COLOR_HINT),
            )
        ):
            tk.Label(
                stats,
                text=label,
                font=(FONT_FAMILY, 10),
                bg=COLOR_PANEL,
                fg=COLOR_MUTED,
                anchor="w",
            ).grid(row=row, column=0, sticky="w", pady=0)

            value = tk.Label(
                stats,
                text="—",
                font=(FONT_FAMILY, 10, "bold"),
                bg=COLOR_PANEL,
                fg=color,
                anchor="e",
            )
            value.grid(row=row, column=1, sticky="e", pady=0)
            self.value_labels[key] = value
        self.value_labels["hints"] = self.value_labels["hints_used"]

        # --- efficiency progress display --------------------------------------
        progress = tk.Frame(card, bg=COLOR_PANEL)
        progress.pack(fill="x", pady=(2, 0))

        tk.Label(
            progress,
            text="PATH EFFICIENCY",
            font=(FONT_FAMILY, 9, "bold"),
            bg=COLOR_PANEL,
            fg=COLOR_MUTED,
        ).pack(anchor="w")

        track = tk.Frame(progress, bg=COLOR_PANEL_ALT, height=6)
        track.pack(fill="x", pady=(2, 0))
        track.pack_propagate(False)

        self.efficiency_fill = tk.Frame(track, bg=COLOR_SUCCESS)
        self.efficiency_fill.place(x=0, y=0, relwidth=0.0, relheight=1.0)

        hline(card, pad_y=2)

        tk.Label(
            card,
            text="COMPARE WITH OPTIMAL PATH",
            font=(FONT_FAMILY, 9, "bold"),
            bg=COLOR_PANEL,
            fg=COLOR_MUTED,
            anchor="w",
        ).pack(fill="x", pady=(0, 1))

        self.optimal_button = MenuButton(
            card,
            "SHOW OPTIMAL PATH",
            command=self.toggle_optimal_path,
            variant="secondary",
            width=22,
            font=(FONT_FAMILY, 11, "bold"),
            pady=1,
        )
        self.optimal_button.pack(fill="x", pady=(0, 2))

        self.watch_button = MenuButton(
            card,
            "WATCH MY RUN",
            command=self.start_watch_run,
            variant="primary",
            width=22,
            font=(FONT_FAMILY, 11, "bold"),
            pady=1,
        )
        self.watch_button.pack(fill="x", pady=(0, 2))

        speed_row = tk.Frame(card, bg=COLOR_PANEL)
        speed_row.pack(fill="x", pady=(0, 2))
        tk.Label(
            speed_row,
            text="SPEED",
            font=(FONT_FAMILY, 8, "bold"),
            bg=COLOR_PANEL,
            fg=COLOR_MUTED,
        ).pack(side="left", padx=(0, 6))
        self.speed_buttons = {}
        for speed in (1, 2, 4):
            label = f"{speed}x"
            button = MenuButton(
                speed_row,
                label,
                command=lambda s=speed: self.set_watch_speed(s),
                variant="secondary",
                width=5,
                font=(FONT_FAMILY, 8, "bold"),
                pady=0,
            )
            button.pack(side="left", padx=(0, 6))
            self.speed_buttons[label] = button

        MenuButton(
            card,
            "Play Again",
            command=lambda: self.app.show_screen("gameplay"),
            variant="primary",
            width=22,
            font=(FONT_FAMILY, 11, "bold"),
            pady=1,
        ).pack(fill="x", pady=(0, 2))

        MenuButton(
            card,
            "Main Menu",
            command=lambda: self.app.show_screen("home"),
            variant="secondary",
            width=22,
            font=(FONT_FAMILY, 11, "bold"),
            pady=1,
        ).pack(fill="x", pady=(0, 2))

        MenuButton(
            card,
            "Exit",
            command=self.app.exit_app,
            variant="danger",
            width=22,
            font=(FONT_FAMILY, 11, "bold"),
            pady=1,
        ).pack(fill="x")

    # -- screen lifecycle ------------------------------------------------------
    def on_show(self):
        """Load the finished run, then draw and replay the player's route."""
        gameplay = self.app.screens.get("gameplay")
        if gameplay is not None:
            gameplay.stop_run()   # no clock, solver or hint while Results is up

        result = self.app.last_result or {}
        self.maze = result.get("maze")
        self.player_path = [tuple(cell) for cell in result.get("player_path", [])]
        raw_times = result.get("player_times") or []
        try:
            self.player_times = [float(v) for v in raw_times]
        except (TypeError, ValueError):
            self.player_times = []
        if len(self.player_times) < len(self.player_path):
            last = self.player_times[-1] if self.player_times else 0.0
            self.player_times.extend([last] * (len(self.player_path) - len(self.player_times)))
        if self.player_times:
            self.player_times = self.player_times[: len(self.player_path)]
            self.player_times[0] = 0.0

        efficiency = result.get("efficiency")
        hints_value = result.get("hints_used", result.get("hints", 0))
        try:
            hints_value = int(hints_value or 0)
        except (TypeError, ValueError):
            hints_value = 0
        values = {
            "moves": result.get("moves", "—"),
            "time": result.get("time", "00:00"),
            "player_length": result.get("player_length", "—"),
            "optimal_length": result.get("optimal_length", "—"),
            "efficiency": f"{efficiency:.1f}%" if efficiency is not None else "—",
            "hints_used": hints_value,
        }
        for key, value in values.items():
            self.value_labels[key].configure(text=str(value))

        # Efficiency bar: 0-100 % -> 0.0-1.0 of the track width.
        percent = max(0.0, min(100.0, float(efficiency or 0.0)))
        if percent >= 75:
            bar_color = COLOR_SUCCESS
        elif percent >= 50:
            bar_color = COLOR_HINT
        else:
            bar_color = COLOR_DANGER
        self.efficiency_fill.configure(bg=bar_color)
        self.efficiency_fill.place_configure(relwidth=percent / 100.0)

        # Optimal route: reuse the cached path from Gameplay when the maze
        # is unchanged instead of running A* again for the same run.
        self.stop_optimal_replay()
        self.clear_optimal_path()
        self.stop_watch_run()
        self.clear_watch_marker()
        self.watch_index = 0
        self.watch_speed = 1
        self._replay_items = []
        cached_optimal = result.get("optimal_path")
        if cached_optimal and self.maze is not None:
            try:
                path = [tuple(cell) for cell in cached_optimal]
                if path and path[0] == tuple(self.maze.start) and path[-1] == tuple(self.maze.goal):
                    self._optimal_path = path
                else:
                    self._optimal_path = astar_path(self.maze, self.maze.start, self.maze.goal)
            except (TypeError, ValueError):
                self._optimal_path = astar_path(self.maze, self.maze.start, self.maze.goal) if self.maze is not None else []
        elif isinstance(gameplay, GameplayScreen) and getattr(gameplay, "_optimal_path_cached", None):
            try:
                path = [tuple(cell) for cell in gameplay._optimal_path_cached]
                if path and path[0] == tuple(self.maze.start) and path[-1] == tuple(self.maze.goal):
                    self._optimal_path = path
                else:
                    self._optimal_path = astar_path(self.maze, self.maze.start, self.maze.goal) if self.maze is not None else []
            except (TypeError, ValueError, AttributeError):
                self._optimal_path = astar_path(self.maze, self.maze.start, self.maze.goal) if self.maze is not None else []
        else:
            self._optimal_path = (
                astar_path(self.maze, self.maze.start, self.maze.goal)
                if self.maze is not None
                else []
            )
        self._optimal_visible = False
        self._optimal_index = 0
        self.optimal_button.configure(text="SHOW OPTIMAL PATH")

        self.refresh_records_achievements(result)

        self.draw_maze()
        self.start_replay()

    def refresh_records_achievements(self, result=None):
        if result is None:
            result = self.app.last_result or {}
        # NEW RECORD banner.
        is_record = bool(result.get("new_record"))
        try:
            self.new_record_label.configure(
                text="🏆 NEW RECORD!" if is_record else ""
            )
        except Exception:
            pass
        # Best records for this run's level (or all levels summary).
        level_id = result.get("challenge")
        if level_id in LEVEL_BY_ID:
            level_name = LEVEL_BY_ID[level_id]["name"]
            record = self.app.record_for_level(level_id)
            bt = record.get("best_time")
            if bt is None and isinstance(result.get("best_record"), dict):
                bt = result["best_record"].get("best_time")
            bm = record.get("best_moves")
            if bm is None and isinstance(result.get("best_record"), dict):
                bm = result["best_record"].get("best_moves")
            be = record.get("best_efficiency")
            if be is None and isinstance(result.get("best_record"), dict):
                be = result["best_record"].get("best_efficiency")
            bt_text = format_record_time(bt) if bt is not None else result.get("time", "—")
            bm_text = str(bm) if bm is not None else str(result.get("moves", "—"))
            be_text = f"{float(be):.1f}%" if be is not None else "—"
            text = f"Best Records ({level_name}): Best Time: {bt_text} · Least Moves: {bm_text} · Highest Efficiency: {be_text}"
        else:
            # Custom run: best overall (custom) records only; challenge
            # records are untouched and challenge progression is separate.
            rec = self.app.record_for_level(CUSTOM_LEVEL_ID)
            bt = rec.get("best_time")
            if bt is None and isinstance(result.get("best_record"), dict):
                bt = result["best_record"].get("best_time")
            bm = rec.get("best_moves")
            if bm is None and isinstance(result.get("best_record"), dict):
                bm = result["best_record"].get("best_moves")
            be = rec.get("best_efficiency")
            if be is None and isinstance(result.get("best_record"), dict):
                be = result["best_record"].get("best_efficiency")
            if bt is not None or bm is not None or be is not None:
                text = f"Best Records (Custom): Best Time: {format_record_time(bt) if bt is not None else '—'} · Least Moves: {bm if bm is not None else '—'} · Highest Efficiency: {f'{float(be):.1f}%' if be is not None else '—'}"
            else:
                text = "Best Records (Custom): — (challenge records unchanged)"
        try:
            self.records_label.configure(text=text)
        except Exception:
            pass
        # Achievements summary.
        unlocked_ids = list(getattr(self.app, "achievements", set()) or [])
        unlocked_ids = [aid for aid in ACHIEVEMENT_ORDER if aid in unlocked_ids]
        count = len(unlocked_ids)
        total = len(ACHIEVEMENT_ORDER)
        if unlocked_ids:
            names = ", ".join(f"🏅 {ACHIEVEMENT_BY_ID[aid]}" for aid in unlocked_ids)
            ach_text = f"Achievements ({count}/{total}): {names}"
        else:
            ach_text = f"Achievements ({count}/{total}): None yet"
        try:
            self.achievements_label.configure(text=ach_text)
        except Exception:
            pass

    def on_hide(self):
        """Leaving Results must stop both replays and any pending redraw."""
        self.stop_replay()
        self.stop_optimal_replay()
        self.stop_watch_run()
        if self._resize_job is not None:
            self.after_cancel(self._resize_job)
            self._resize_job = None

    # -- maze rendering --------------------------------------------------------
    def _on_canvas_resize(self, _event=None):
        if self._resize_job is not None:
            self.after_cancel(self._resize_job)
        self._resize_job = self.after(60, self._redraw)

    def _redraw(self):
        self._resize_job = None
        was_watching = bool(getattr(self, "_watch_running", False))
        watch_index = int(getattr(self, "watch_index", 0) or 0)
        if was_watching:
            self.stop_watch_run()
        self.draw_maze()
        if was_watching:
            self._resume_watch_run(watch_index)
        else:
            self.start_replay()
            if self._optimal_visible:
                self.paint_optimal_instant()

    def draw_maze(self):
        """Paint the finished maze, centred, with square cells."""
        self._resize_job = None

        canvas = self.canvas
        canvas.delete("all")
        self._start_item = None
        self._goal_item = None
        self._layout = None
        self._watch_item = None
        self._watch_origin = None
        self._replay_items = []
        self._optimal_items = []

        maze = self.maze
        if maze is None:
            return

        width = canvas.winfo_width()
        height = canvas.winfo_height()
        if width < 2 or height < 2:
            return  # not laid out yet - <Configure> calls us again

        layout = maze_layout(maze, width, height, padding=18)
        draw_maze_cells(canvas, maze, layout)
        self._layout = layout

        self._start_item = self._marker(
            maze.start, COLOR_START, outline="#67e8f9"
        )
        self._goal_item = self._marker(
            maze.goal, COLOR_DANGER, outline="#ff7b72", dot=True
        )

    def _marker(self, position, color, outline="", dot=False):
        return draw_cell_marker(
            self.canvas, self._layout, position, color, outline, goal=dot
        )

    # -- replay ----------------------------------------------------------------
    def start_replay(self):
        """Replay the stored route one light green cell at a time."""
        self.stop_replay()
        self.replay_index = 1

        steps = len(self.player_path) - 1
        if self._layout is None or steps < 1:
            return

        self._step_delay = max(
            self.MIN_REPLAY_DELAY,
            min(self.REPLAY_DELAY, self.REPLAY_TOTAL_MS // steps),
        )
        self._replay_job = self.after(self._step_delay, self._replay_step)

    def stop_replay(self):
        if self._replay_job is not None:
            try:
                self.after_cancel(self._replay_job)
            except tk.TclError:
                pass
            self._replay_job = None

    def _replay_step(self):
        self._replay_job = None

        if self.app.current_screen != "results":
            return
        if self._layout is None or self.replay_index >= len(self.player_path):
            return

        self.paint_path_cell(self.player_path[self.replay_index])
        self.replay_index += 1

        # Only keep a timer alive while there are cells left to paint.
        if self.replay_index < len(self.player_path) and self._replay_job is None:
            self._replay_job = self.after(self._step_delay, self._replay_step)

    def paint_path_cell(self, cell):
        """One light green square, kept under the start/goal markers.

        The route fills almost the whole cell so the green stays visible as a
        clear border around the slightly inset yellow optimal route.
        """
        x0, y0, size = path_box(self._layout, *cell, extra=0)

        item = rounded_rect(
            self.canvas,
            x0,
            y0,
            x0 + size,
            y0 + size,
            max(2, size // 6),
            fill=COLOR_REPLAY,
            outline="",
            tags=("replay",),
        )
        self._replay_items.append(item)

        if self._goal_item is not None:
            self.canvas.tag_lower(item, self._goal_item)
        if self._start_item is not None:
            self.canvas.tag_lower(item, self._start_item)

        # Green cells are painted after the yellow route started animating;
        # keep the yellow route on top so both stay readable where they overlap.
        if self._optimal_visible and self._optimal_items and self._start_item is not None:
            self.canvas.tag_lower("optimal", self._start_item)

    # -- optimal A* path -------------------------------------------------------
    def toggle_optimal_path(self):
        """SHOW OPTIMAL PATH <-> HIDE OPTIMAL PATH."""
        if self._optimal_visible:
            self.hide_optimal_path()
        else:
            self.show_optimal_path()

    def show_optimal_path(self):
        if self._layout is None:
            return

        if not self._optimal_path and self.maze is not None:
            self._optimal_path = astar_path(
                self.maze, self.maze.start, self.maze.goal
            )
        if len(self._optimal_path) < 2:
            self._optimal_visible = False
            self.optimal_button.configure(text="SHOW OPTIMAL PATH")
            return

        self.stop_optimal_replay()
        self.clear_optimal_path()

        self._optimal_visible = True
        self.optimal_button.configure(text="HIDE OPTIMAL PATH")

        steps = len(self._optimal_path) - 1
        self._optimal_delay = max(
            self.MIN_OPTIMAL_DELAY,
            min(self.REPLAY_DELAY, self.OPTIMAL_TOTAL_MS // max(1, steps)),
        )
        self._optimal_index = 1
        self._optimal_job = self.after(self._optimal_delay, self._optimal_step)

    def hide_optimal_path(self):
        """Remove only the yellow route; keep the green player replay."""
        self._optimal_visible = False
        self.optimal_button.configure(text="SHOW OPTIMAL PATH")
        self.stop_optimal_replay()
        self.clear_optimal_path()

    def stop_optimal_replay(self):
        if self._optimal_job is not None:
            try:
                self.after_cancel(self._optimal_job)
            except tk.TclError:
                pass
            self._optimal_job = None

    def clear_optimal_path(self):
        for item in list(self._optimal_items):
            try:
                self.canvas.delete(item)
            except tk.TclError:
                pass
        self._optimal_items = []

    def _optimal_step(self):
        self._optimal_job = None

        if self.app.current_screen != "results" or not self._optimal_visible:
            return
        if self._layout is None or self._optimal_index >= len(self._optimal_path):
            return

        self.paint_optimal_cell(self._optimal_path[self._optimal_index])
        self._optimal_index += 1

        if self._optimal_index < len(self._optimal_path) and self._optimal_job is None:
            self._optimal_job = self.after(self._optimal_delay, self._optimal_step)

    def paint_optimal_instant(self):
        """Paint the complete yellow route after a resize."""
        self.stop_optimal_replay()
        self.clear_optimal_path()
        for cell in self._optimal_path[1:]:
            self.paint_optimal_cell(cell)

    def paint_optimal_cell(self, cell):
        """One yellow A* square, slightly smaller so the green route peeks out."""
        x0, y0, size = path_box(self._layout, *cell, extra=2)

        item = rounded_rect(
            self.canvas,
            x0,
            y0,
            x0 + size,
            y0 + size,
            max(2, size // 6),
            fill=COLOR_AI,
            outline="",
            tags=("optimal",),
        )

        if self._goal_item is not None:
            self.canvas.tag_lower(item, self._goal_item)
        if self._start_item is not None:
            self.canvas.tag_lower(item, self._start_item)

        self._optimal_items.append(item)

    # -- watch my run (timed player-marker replay) ---------------------------
    def clear_replay_visuals(self):
        """Remove the green/yellow replay paint; keep the maze itself."""
        self.stop_replay()
        self.stop_optimal_replay()
        for item in list(getattr(self, "_replay_items", [])):
            try:
                self.canvas.delete(item)
            except tk.TclError:
                pass
        self._replay_items = []
        try:
            for item in self.canvas.find_withtag("replay"):
                self.canvas.delete(item)
        except tk.TclError:
            pass
        self.clear_optimal_path()
        self._optimal_visible = False
        self._optimal_index = 0
        try:
            self.optimal_button.configure(text="SHOW OPTIMAL PATH")
        except Exception:
            pass

    def clear_watch_marker(self):
        try:
            for item in self.canvas.find_withtag("watch"):
                self.canvas.delete(item)
        except tk.TclError:
            pass
        self._watch_item = None
        self._watch_origin = None

    def _watch_box(self, cell):
        return path_box(self._layout, *cell, extra=1)

    def draw_watch_marker(self, cell):
        """Place the blue player marker on ``cell`` (halo + body)."""
        if self._layout is None or cell is None:
            return
        self.clear_watch_marker()
        x0, y0, size = self._watch_box(cell)
        halo = max(1, min(3, size // 10))
        rounded_rect(
            self.canvas,
            x0 - halo, y0 - halo, x0 + size + halo, y0 + size + halo,
            max(3, size // 5), fill=COLOR_PLAYER_GLOW, outline="",
            tags=("watch", "watch_player", "player", "player_halo"),
        )
        self._watch_item = rounded_rect(
            self.canvas,
            x0, y0, x0 + size, y0 + size,
            max(2, size // 6), fill=COLOR_PLAYER, outline="#dbeafe",
            width=max(1, min(2, size // 14)),
            tags=("watch", "watch_player", "player", "player_body"),
        )
        self._watch_origin = (x0, y0, size)
        # Marker stays on top of maze and any route paint.
        try:
            for item in self.canvas.find_withtag("watch"):
                self.canvas.tag_raise(item)
        except tk.TclError:
            pass

    def move_watch_marker(self, cell):
        if self._layout is None or cell is None:
            return
        if self._watch_origin is None:
            self.draw_watch_marker(cell)
            return
        x0, y0, size = self._watch_box(cell)
        old_x, old_y, old_size = self._watch_origin
        if size != old_size:
            self.draw_watch_marker(cell)
            return
        if x0 != old_x or y0 != old_y:
            self.canvas.move("watch", x0 - old_x, y0 - old_y)
            self._watch_origin = (x0, y0, size)

    def _watch_delay_for(self, index):
        """Delay (ms) from cell index-1 to index at the current speed."""
        speed = max(1, int(getattr(self, "watch_speed", 1) or 1))
        base_ms = None
        times = getattr(self, "player_times", []) or []
        if len(times) > index and index >= 1:
            try:
                delta = float(times[index]) - float(times[index - 1])
                if delta >= 0:
                    base_ms = delta * 1000.0
            except (TypeError, ValueError):
                base_ms = None
        if base_ms is None or base_ms <= 0:
            base_ms = float(getattr(self, "_step_delay", self.REPLAY_DELAY) or self.REPLAY_DELAY)
        delay = int(base_ms / speed)
        return max(20, min(delay, 2000))

    def start_watch_run(self):
        """WATCH MY RUN: clear replay paint, then move the player marker."""
        if self.app.current_screen != "results":
            return
        if self._layout is None or len(self.player_path) < 1:
            return
        self.stop_watch_run()
        self.clear_replay_visuals()
        self.replay_index = len(self.player_path)
        self.watch_index = 0
        self._watch_running = True
        self.draw_watch_marker(self.player_path[0])
        if len(self.player_path) < 2:
            self._watch_running = False
            return
        self.watch_index = 1
        self._watch_job = self.after(self._watch_delay_for(1), self._watch_step)

    def _resume_watch_run(self, index):
        if self.app.current_screen != "results" or self._layout is None:
            return
        if not self.player_path:
            return
        try:
            index = int(index)
        except (TypeError, ValueError):
            index = 0
        index = max(0, min(index, len(self.player_path) - 1))
        self.stop_watch_run()
        self.clear_watch_marker()
        self.watch_index = index
        self._watch_running = True
        self.draw_watch_marker(self.player_path[index])
        if index + 1 >= len(self.player_path):
            self._watch_running = False
            return
        self.watch_index = index + 1
        self._watch_job = self.after(self._watch_delay_for(index + 1), self._watch_step)

    def stop_watch_run(self):
        if getattr(self, "_watch_job", None) is not None:
            try:
                self.after_cancel(self._watch_job)
            except tk.TclError:
                pass
            self._watch_job = None
        self._watch_running = False

    def _watch_step(self):
        self._watch_job = None
        if self.app.current_screen != "results" or not getattr(self, "_watch_running", False):
            self._watch_running = False
            return
        if self._layout is None or self.watch_index >= len(self.player_path):
            self._watch_running = False
            return
        self.move_watch_marker(self.player_path[self.watch_index])
        self.watch_index += 1
        if self.watch_index < len(self.player_path) and self._watch_job is None:
            self._watch_job = self.after(self._watch_delay_for(self.watch_index), self._watch_step)
        else:
            self._watch_running = False

    def set_watch_speed(self, speed):
        try:
            speed = int(speed)
        except (TypeError, ValueError):
            return
        if speed not in (1, 2, 4):
            return
        self.watch_speed = speed
        # Reschedule the pending step so the new speed applies immediately.
        if self._watch_running and self._watch_job is not None and self.watch_index < len(self.player_path):
            try:
                self.after_cancel(self._watch_job)
            except tk.TclError:
                pass
            self._watch_job = self.after(self._watch_delay_for(self.watch_index), self._watch_step)

    # Aliases for discoverability.
    def start_watch(self):
        self.start_watch_run()

    def watch_my_run(self):
        self.start_watch_run()


# ---------------------------------------------------------------------------
# AI Complete
# ---------------------------------------------------------------------------
class AICompleteScreen(Screen):
    title = "AI Complete"

    BADGE_BG = "#2b2416"   # dark amber behind the A* badge

    def build(self):
        card = tk.Frame(
            center_container(self),
            bg=COLOR_PANEL,
            width=580,
            padx=44,
            pady=30,
            highlightbackground=COLOR_BORDER,
            highlightthickness=1,
        )
        card.pack()

        # --- header: A* badge + title ----------------------------------------
        header = tk.Frame(card, bg=COLOR_PANEL)
        header.pack(fill="x")

        badge = tk.Frame(
            header,
            bg=self.BADGE_BG,
            padx=16,
            pady=10,
            highlightbackground=COLOR_AI,
            highlightthickness=2,
        )
        badge.pack(side="left", anchor="n")

        tk.Label(
            badge,
            text="A*",
            font=(FONT_FAMILY, 26, "bold"),
            bg=self.BADGE_BG,
            fg=COLOR_AI,
        ).pack()

        tk.Label(
            badge,
            text="SEARCH",
            font=(FONT_FAMILY, 8, "bold"),
            bg=self.BADGE_BG,
            fg=COLOR_MUTED,
        ).pack()

        heading = tk.Frame(header, bg=COLOR_PANEL)
        heading.pack(side="left", fill="x", expand=True, padx=(18, 0))

        tk.Label(
            heading,
            text="SOLVER COMPLETE",
            font=(FONT_FAMILY, 10, "bold"),
            bg=COLOR_PANEL,
            fg=COLOR_AI,
        ).pack(anchor="w")

        tk.Label(
            heading,
            text="AI COMPLETED THE MAZE",
            font=(FONT_FAMILY, 22, "bold"),
            bg=COLOR_PANEL,
            fg=COLOR_TEXT_STRONG,
            justify="left",
            wraplength=360,
        ).pack(anchor="w", pady=(4, 0))

        tk.Label(
            card,
            text="The solver walked the optimal route from your position to the goal.",
            font=SMALL_FONT,
            bg=COLOR_PANEL,
            fg=COLOR_MUTED,
            justify="left",
            wraplength=500,
        ).pack(anchor="w", pady=(16, 0))

        hline(card, pad_y=18)

        # --- stats ------------------------------------------------------------
        stats = tk.Frame(card, bg=COLOR_PANEL)
        stats.pack(fill="x")

        self.value_labels = {}
        for column, (label, key, color) in enumerate(
            (
                ("AI Steps", "ai_steps", COLOR_AI),
                ("Time Taken", "time", COLOR_TEXT_STRONG),
                ("Difficulty", "difficulty", COLOR_HINT),
                ("Hints Used", "hints_used", COLOR_HINT),
            )
        ):
            stats.grid_columnconfigure(column, weight=1)
            box = tk.Frame(
                stats,
                bg=COLOR_PANEL_ALT,
                padx=10,
                pady=12,
                highlightbackground=COLOR_BORDER,
                highlightthickness=1,
            )
            box.grid(
                row=0,
                column=column,
                sticky="ew",
                padx=(0 if column == 0 else 8, 0),
            )

            tk.Frame(box, height=2, bg=color).pack(fill="x", pady=(0, 6))

            tk.Label(
                box,
                text=label.upper(),
                font=(FONT_FAMILY, 9, "bold"),
                bg=COLOR_PANEL_ALT,
                fg=COLOR_MUTED,
            ).pack(anchor="w")

            value = tk.Label(
                box,
                text="—",
                font=(FONT_FAMILY, 18, "bold"),
                bg=COLOR_PANEL_ALT,
                fg=color,
            )
            value.pack(anchor="w", pady=(4, 0))
            self.value_labels[key] = value
        self.value_labels["hints"] = self.value_labels["hints_used"]

        hline(card, pad_y=18)

        # --- note -------------------------------------------------------------
        note = tk.Frame(card, bg=COLOR_PANEL)
        note.pack(fill="x", pady=(0, 18))

        tk.Frame(note, width=3, bg=COLOR_AI).pack(side="left", fill="y")

        tk.Label(
            note,
            text="A* found the shortest route - compare it with your own run.",
            font=SMALL_FONT,
            bg=COLOR_PANEL,
            fg=COLOR_MUTED,
            anchor="w",
        ).pack(side="left", padx=(10, 0))

        # --- buttons ----------------------------------------------------------
        MenuButton(
            card,
            "Try Again",
            command=lambda: self.app.show_screen("gameplay"),
            variant="primary",
            width=22,
            font=(FONT_FAMILY, 12, "bold"),
            pady=6,
        ).pack(fill="x", pady=(0, 6))

        MenuButton(
            card,
            "Main Menu",
            command=lambda: self.app.show_screen("home"),
            variant="secondary",
            width=22,
            font=(FONT_FAMILY, 12, "bold"),
            pady=6,
        ).pack(fill="x", pady=(0, 6))

        MenuButton(
            card,
            "Exit",
            command=self.app.exit_app,
            variant="danger",
            width=22,
            font=(FONT_FAMILY, 12, "bold"),
            pady=6,
        ).pack(fill="x")

    def on_show(self):
        """Fill the cards from the run the solver just finished."""
        result = self.app.last_result or {}
        steps = result.get("ai_steps")

        values = {
            "ai_steps": str(steps) if steps is not None else "—",
            "time": result.get("time", "00:00"),
            "difficulty": result.get("difficulty", "—"),
            "hints_used": str(result.get("hints_used", result.get("hints", 0)) or 0),
        }

        for key, value in values.items():
            self.value_labels[key].configure(text=value)


# ---------------------------------------------------------------------------
# Player Complete
# ---------------------------------------------------------------------------
class PlayerCompleteScreen(Screen):
    title = "Player Complete"

    BADGE_BG = "#12261a"   # dark green behind the winner badge

    def build(self):
        card = tk.Frame(
            center_container(self),
            bg=COLOR_PANEL,
            width=620,
            padx=32,
            pady=16,
            highlightbackground=COLOR_BORDER,
            highlightthickness=1,
        )
        card.pack()

        # --- header: winner badge + title -------------------------------------
        header = tk.Frame(card, bg=COLOR_PANEL)
        header.pack(fill="x")

        badge = tk.Frame(
            header,
            bg=self.BADGE_BG,
            padx=12,
            pady=6,
            highlightbackground=COLOR_SUCCESS,
            highlightthickness=2,
        )
        badge.pack(side="left", anchor="n")

        tk.Label(
            badge,
            text="✓",
            font=(FONT_FAMILY, 22, "bold"),
            bg=self.BADGE_BG,
            fg=COLOR_SUCCESS,
        ).pack()

        tk.Label(
            badge,
            text="WINNER",
            font=(FONT_FAMILY, 8, "bold"),
            bg=self.BADGE_BG,
            fg=COLOR_MUTED,
        ).pack()

        heading = tk.Frame(header, bg=COLOR_PANEL)
        heading.pack(side="left", fill="x", expand=True, padx=(14, 0))

        tk.Label(
            heading,
            text="PLAYER COMPLETE",
            font=(FONT_FAMILY, 10, "bold"),
            bg=COLOR_PANEL,
            fg=COLOR_SUCCESS,
        ).pack(anchor="w")

        tk.Label(
            heading,
            text="YOU COMPLETED THE MAZE",
            font=(FONT_FAMILY, 20, "bold"),
            bg=COLOR_PANEL,
            fg=COLOR_TEXT_STRONG,
            justify="left",
            wraplength=400,
        ).pack(anchor="w", pady=(2, 0))

        tk.Label(
            card,
            text="Custom Maze completed. Save achievements and best overall records only — challenge progress is unchanged.",
            font=SMALL_FONT,
            bg=COLOR_PANEL,
            fg=COLOR_MUTED,
            justify="left",
            wraplength=520,
        ).pack(anchor="w", pady=(8, 0))

        hline(card, pad_y=8)

        # --- stats ------------------------------------------------------------
        stats = tk.Frame(card, bg=COLOR_PANEL)
        stats.pack(fill="x")

        self.value_labels = {}
        for column, (label, key, color) in enumerate(
            (
                ("Moves", "moves", COLOR_SUCCESS),
                ("Time Taken", "time", COLOR_TEXT_STRONG),
                ("Difficulty", "difficulty", COLOR_HINT),
                ("Maze Size", "size", COLOR_ACCENT),
                ("Hints Used", "hints_used", COLOR_HINT),
            )
        ):
            stats.grid_columnconfigure(column, weight=1)

            box = tk.Frame(
                stats,
                bg=COLOR_PANEL_ALT,
                padx=6,
                pady=6,
                highlightbackground=COLOR_BORDER,
                highlightthickness=1,
            )
            box.grid(
                row=0,
                column=column,
                sticky="ew",
                padx=(0 if column == 0 else 5, 0),
            )

            tk.Frame(box, height=2, bg=color).pack(fill="x", pady=(0, 4))

            tk.Label(
                box,
                text=label.upper(),
                font=(FONT_FAMILY, 8, "bold"),
                bg=COLOR_PANEL_ALT,
                fg=COLOR_MUTED,
            ).pack(anchor="w")

            value = tk.Label(
                box,
                text="—",
                font=(FONT_FAMILY, 14, "bold"),
                bg=COLOR_PANEL_ALT,
                fg=color,
            )
            value.pack(anchor="w", pady=(2, 0))
            self.value_labels[key] = value
        self.value_labels["hints"] = self.value_labels["hints_used"]

        self.new_record_label = tk.Label(
            card,
            text="",
            font=(FONT_FAMILY, 10, "bold"),
            bg=COLOR_PANEL,
            fg=COLOR_AI,
            anchor="w",
        )
        self.new_record_label.pack(fill="x", pady=(4, 0), anchor="w")
        self.record_label = self.new_record_label
        self.record_info_label = tk.Label(
            card,
            text="",
            font=(FONT_FAMILY, 8),
            bg=COLOR_PANEL,
            fg=COLOR_MUTED,
            anchor="w",
            justify="left",
        )
        self.record_info_label.pack(fill="x", pady=(0, 0), anchor="w")

        # --- save progress prompt (achievements/records only) -----------------
        self.progress_panel = tk.Frame(
            card,
            bg=COLOR_PANEL_ALT,
            padx=12,
            pady=6,
            highlightbackground=COLOR_BORDER,
            highlightthickness=1,
        )
        self.progress_panel.pack(fill="x", pady=(8, 0))

        self.progress_kicker = tk.Label(
            self.progress_panel,
            text="CUSTOM MAZE COMPLETE",
            font=(FONT_FAMILY, 8, "bold"),
            bg=COLOR_PANEL_ALT,
            fg=COLOR_SUCCESS,
        )
        self.progress_kicker.pack(anchor="w")

        self.progress_name = tk.Label(
            self.progress_panel,
            text="Save custom achievements & best overall records",
            font=(FONT_FAMILY, 11, "bold"),
            bg=COLOR_PANEL_ALT,
            fg=COLOR_TEXT_STRONG,
        )
        self.progress_name.pack(anchor="w", pady=(2, 0))

        self.save_row = tk.Frame(self.progress_panel, bg=COLOR_PANEL_ALT)
        self.save_row.pack(fill="x", pady=(4, 0))

        tk.Label(
            self.save_row,
            text="Save Progress?",
            font=(FONT_FAMILY, 10, "bold"),
            bg=COLOR_PANEL_ALT,
            fg=COLOR_TEXT,
        ).pack(side="left")

        save_buttons = tk.Frame(self.save_row, bg=COLOR_PANEL_ALT)
        save_buttons.pack(side="right")

        self.save_button = MenuButton(
            save_buttons,
            "SAVE PROGRESS",
            command=self.save_progress,
            variant="primary",
            width=14,
            font=(FONT_FAMILY, 8, "bold"),
            pady=3,
        )
        self.save_button.pack(side="left", padx=(0, 6))

        self.continue_button = MenuButton(
            save_buttons,
            "CONTINUE WITHOUT SAVING",
            command=self.continue_without_saving,
            variant="secondary",
            width=21,
            font=(FONT_FAMILY, 8, "bold"),
            pady=3,
        )
        self.continue_button.pack(side="left")

        self.save_status_label = tk.Label(
            self.progress_panel,
            text="",
            font=SMALL_FONT,
            bg=COLOR_PANEL_ALT,
            fg=COLOR_MUTED,
            anchor="w",
        )
        self.save_status_label.pack(fill="x", pady=(2, 0))

        hline(card, pad_y=8)

        # --- note -------------------------------------------------------------
        note = tk.Frame(card, bg=COLOR_PANEL)
        note.pack(fill="x", pady=(0, 8))

        tk.Frame(note, width=3, bg=COLOR_SUCCESS).pack(side="left", fill="y")

        tk.Label(
            note,
            text="Results will replay your route and compare it with the optimal path.",
            font=SMALL_FONT,
            bg=COLOR_PANEL,
            fg=COLOR_MUTED,
            anchor="w",
        ).pack(side="left", padx=(10, 0))

        # --- buttons ----------------------------------------------------------
        MenuButton(
            card,
            "View Results",
            command=lambda: self.app.show_screen("results"),
            variant="primary",
            width=22,
            font=(FONT_FAMILY, 11, "bold"),
            pady=4,
        ).pack(fill="x", pady=(0, 3))

        MenuButton(
            card,
            "Play Again",
            command=lambda: self.app.show_screen("gameplay"),
            variant="secondary",
            width=22,
            font=(FONT_FAMILY, 11, "bold"),
            pady=4,
        ).pack(fill="x", pady=(0, 3))

        MenuButton(
            card,
            "Main Menu",
            command=lambda: self.app.show_screen("home"),
            variant="secondary",
            width=22,
            font=(FONT_FAMILY, 11, "bold"),
            pady=4,
        ).pack(fill="x")

    def on_show(self):
        """Fill the victory stats from the run the player just finished."""
        result = self.app.last_result or {}
        rows, cols = result.get("rows"), result.get("cols")

        values = {
            "moves": str(result.get("moves", "—")),
            "time": result.get("time", "00:00"),
            "difficulty": result.get("difficulty", "—"),
            "size": f"{rows} × {cols}" if rows and cols else "—",
            "hints_used": str(result.get("hints_used", result.get("hints", 0)) or 0),
        }

        for key, value in values.items():
            self.value_labels[key].configure(text=value)
        try:
            is_record = bool(result.get("new_record"))
            self.new_record_label.configure(text="🏆 NEW RECORD!" if is_record else "")
            rec = result.get("best_record") if isinstance(result.get("best_record"), dict) else self.app.record_for_level(CUSTOM_LEVEL_ID)
            bt = rec.get("best_time") if isinstance(rec, dict) else None
            bm = rec.get("best_moves") if isinstance(rec, dict) else None
            be = rec.get("best_efficiency") if isinstance(rec, dict) else None
            self.record_info_label.configure(
                text=f"Best overall — Best Time: {format_record_time(bt) if bt is not None else '—'} · Least Moves: {bm if bm is not None else '—'} · Highest Efficiency: {f'{float(be):.1f}%' if be is not None else '—'}"
            )
        except Exception:
            pass
        # Custom save prompt is always offered after a custom win (human).
        # It only persists achievements / custom replays / best-overall
        # records via the existing file; challenge progression is untouched.
        try:
            self.progress_kicker.configure(text="CUSTOM MAZE COMPLETE", fg=COLOR_SUCCESS)
            newly = result.get("newly_unlocked_achievements") or result.get("new_achievements") or []
            if newly:
                names = ", ".join(ACHIEVEMENT_BY_ID.get(aid, aid) for aid in newly)
                self.progress_name.configure(text=f"New: {names}", fg=COLOR_TEXT_STRONG)
            else:
                self.progress_name.configure(text="Save custom achievements & best overall records", fg=COLOR_TEXT_STRONG)
            self.save_status_label.configure(text="")
            if not self.save_row.winfo_ismapped():
                self.save_row.pack(fill="x", pady=(4, 0), before=self.save_status_label)
            self.save_button.configure(state="normal", text="SAVE PROGRESS")
        except Exception:
            pass

    def save_progress(self):
        ok, error = self.app.save_progress()
        if ok:
            self.save_status_label.configure(
                text="Progress saved. It will be restored next time.",
                fg=COLOR_SUCCESS,
            )
            self.save_row.pack_forget()
        else:
            self.save_status_label.configure(
                text=f"Could not save progress: {error}",
                fg=COLOR_DANGER,
            )

    def continue_without_saving(self):
        self.save_row.pack_forget()
        self.save_status_label.configure(
            text="Progress kept for this session only.", fg=COLOR_MUTED
        )


# ---------------------------------------------------------------------------
# Challenge Complete
# ---------------------------------------------------------------------------
class ChallengeCompleteScreen(Screen):
    title = "Challenge Complete"

    BADGE_BG = "#2b2416"   # dark amber behind the trophy badge

    def build(self):
        card = tk.Frame(
            center_container(self),
            bg=COLOR_PANEL,
            padx=42,
            pady=24,
            highlightbackground=COLOR_BORDER,
            highlightthickness=1,
        )
        card.pack()

        # Keep the complete-card wide enough for four stats and two save
        # buttons without forcing a fixed height.
        tk.Frame(card, width=620, height=1, bg=COLOR_PANEL).pack()

        # --- header -----------------------------------------------------------
        header = tk.Frame(card, bg=COLOR_PANEL)
        header.pack(fill="x")

        badge = tk.Frame(
            header,
            bg=self.BADGE_BG,
            padx=14,
            pady=7,
            highlightbackground=COLOR_AI,
            highlightthickness=2,
        )
        badge.pack(side="left", anchor="n")

        tk.Label(
            badge,
            text="🏆",
            font=("Segoe UI Emoji", 24),
            bg=self.BADGE_BG,
            fg=COLOR_AI,
        ).pack()

        tk.Label(
            badge,
            text="CHAMPION",
            font=(FONT_FAMILY, 7, "bold"),
            bg=self.BADGE_BG,
            fg=COLOR_MUTED,
        ).pack()

        heading = tk.Frame(header, bg=COLOR_PANEL)
        heading.pack(side="left", fill="x", expand=True, padx=(18, 0))

        tk.Label(
            heading,
            text="CHALLENGE COMPLETE",
            font=(FONT_FAMILY, 10, "bold"),
            bg=COLOR_PANEL,
            fg=COLOR_SUCCESS,
        ).pack(anchor="w")

        self.level_heading = tk.Label(
            heading,
            text="Beginner",
            font=(FONT_FAMILY, 22, "bold"),
            bg=COLOR_PANEL,
            fg=COLOR_SUCCESS,
        )
        self.level_heading.pack(anchor="w", pady=(2, 0))

        self.subtitle = tk.Label(
            heading,
            text="You cleared the Beginner maze.",
            font=SMALL_FONT,
            bg=COLOR_PANEL,
            fg=COLOR_MUTED,
        )
        self.subtitle.pack(anchor="w", pady=(3, 0))

        hline(card, pad_y=16)

        # --- stats ------------------------------------------------------------
        stats = tk.Frame(card, bg=COLOR_PANEL)
        stats.pack(fill="x")

        self.stat_labels = {}
        for column, (label, key) in enumerate(
            (
                ("LEVEL", "level"),
                ("TIME", "time"),
                ("MOVES", "moves"),
                ("EFFICIENCY", "efficiency"),
                ("HINTS USED", "hints_used"),
            )
        ):
            stats.grid_columnconfigure(column, weight=1)

            box = tk.Frame(
                stats,
                bg=COLOR_PANEL_ALT,
                padx=8,
                pady=9,
                highlightbackground=COLOR_BORDER,
                highlightthickness=1,
            )
            box.grid(
                row=0,
                column=column,
                sticky="ew",
                padx=(0 if column == 0 else 6, 0),
            )

            tk.Label(
                box,
                text=label,
                font=(FONT_FAMILY, 8, "bold"),
                bg=COLOR_PANEL_ALT,
                fg=COLOR_MUTED,
            ).pack(anchor="w")

            value = tk.Label(
                box,
                text="—",
                font=(FONT_FAMILY, 16, "bold"),
                bg=COLOR_PANEL_ALT,
                fg=COLOR_TEXT_STRONG,
            )
            value.pack(anchor="w", pady=(3, 0))
            self.stat_labels[key] = value
        self.stat_labels["hints"] = self.stat_labels["hints_used"]
        self.stat_labels["HINTS"] = self.stat_labels["hints_used"]

        self.new_record_label = tk.Label(
            card,
            text="",
            font=(FONT_FAMILY, 10, "bold"),
            bg=COLOR_PANEL,
            fg=COLOR_AI,
            anchor="w",
        )
        self.new_record_label.pack(fill="x", pady=(2, 0), anchor="w")
        self.record_label = self.new_record_label
        self.record_info_label = tk.Label(
            card,
            text="",
            font=(FONT_FAMILY, 8),
            bg=COLOR_PANEL,
            fg=COLOR_MUTED,
            anchor="w",
            justify="left",
        )
        self.record_info_label.pack(fill="x", pady=(0, 0), anchor="w")

        # --- unlock / save progress prompt -----------------------------------
        self.progress_panel = tk.Frame(
            card,
            bg=COLOR_PANEL_ALT,
            padx=14,
            pady=8,
            highlightbackground=COLOR_BORDER,
            highlightthickness=1,
        )
        self.progress_panel.pack(fill="x", pady=(14, 0))

        self.progress_kicker = tk.Label(
            self.progress_panel,
            text="NEW CHALLENGE UNLOCKED",
            font=(FONT_FAMILY, 8, "bold"),
            bg=COLOR_PANEL_ALT,
            fg=COLOR_SUCCESS,
        )
        self.progress_kicker.pack(anchor="w")

        self.progress_name = tk.Label(
            self.progress_panel,
            text="Intermediate Unlocked",
            font=(FONT_FAMILY, 15, "bold"),
            bg=COLOR_PANEL_ALT,
            fg=COLOR_TEXT_STRONG,
        )
        self.progress_name.pack(anchor="w", pady=(2, 0))

        self.save_row = tk.Frame(self.progress_panel, bg=COLOR_PANEL_ALT)
        self.save_row.pack(fill="x", pady=(6, 0))

        tk.Label(
            self.save_row,
            text="Save Progress?",
            font=(FONT_FAMILY, 11, "bold"),
            bg=COLOR_PANEL_ALT,
            fg=COLOR_TEXT,
        ).pack(side="left")

        save_buttons = tk.Frame(self.save_row, bg=COLOR_PANEL_ALT)
        save_buttons.pack(side="right")

        self.save_button = MenuButton(
            save_buttons,
            "SAVE PROGRESS",
            command=self.save_progress,
            variant="primary",
            width=15,
            font=(FONT_FAMILY, 9, "bold"),
            pady=4,
        )
        self.save_button.pack(side="left", padx=(0, 8))

        self.continue_button = MenuButton(
            save_buttons,
            "CONTINUE WITHOUT SAVING",
            command=self.continue_without_saving,
            variant="secondary",
            width=23,
            font=(FONT_FAMILY, 9, "bold"),
            pady=4,
        )
        self.continue_button.pack(side="left")

        self.save_status_label = tk.Label(
            self.progress_panel,
            text="",
            font=SMALL_FONT,
            bg=COLOR_PANEL_ALT,
            fg=COLOR_MUTED,
            anchor="w",
        )
        self.save_status_label.pack(fill="x", pady=(4, 0))

        # --- actions ----------------------------------------------------------
        hline(card, pad_y=14)

        actions = tk.Frame(card, bg=COLOR_PANEL)
        actions.pack(fill="x")

        self.next_button = MenuButton(
            actions,
            "NEXT CHALLENGE",
            command=self.start_next_challenge,
            variant="primary",
            width=22,
            font=(FONT_FAMILY, 12, "bold"),
            pady=5,
        )

        self.play_current_button = MenuButton(
            actions,
            "PLAY CURRENT LEVEL AGAIN",
            command=self.play_current_level_again,
            variant="secondary",
            width=22,
            font=(FONT_FAMILY, 12, "bold"),
            pady=5,
        )

        self.view_results_button = MenuButton(
            actions,
            "VIEW RESULTS",
            command=lambda: self.app.show_screen("results"),
            variant="secondary",
            width=22,
            font=(FONT_FAMILY, 12, "bold"),
            pady=5,
        )
        self.view_results_button.pack(fill="x", pady=(0, 3))
        self.play_current_button.pack(fill="x", pady=(0, 3), before=self.view_results_button)

        MenuButton(
            actions,
            "MAIN MENU",
            command=lambda: self.app.show_screen("home"),
            variant="secondary",
            width=22,
            font=(FONT_FAMILY, 12, "bold"),
            pady=5,
        ).pack(fill="x")

        self._next_level_id = None
        self.current_level_id = None

    # -- screen lifecycle -------------------------------------------------------
    def on_show(self):
        result = self.app.last_result or {}
        level_name = result.get("challenge_name") or "Challenge"
        level_color = result.get("challenge_color") or COLOR_ACCENT
        efficiency = result.get("efficiency")
        self.current_level_id = result.get("challenge")

        self.level_heading.configure(text=level_name, fg=level_color)
        self.subtitle.configure(text=f"You cleared the {level_name} maze.")

        efficiency_text = (
            f"{efficiency:.1f}%" if isinstance(efficiency, (int, float)) else "—"
        )
        values = {
            "level": level_name,
            "time": result.get("time", "00:00"),
            "moves": str(result.get("moves", "—")),
            "efficiency": efficiency_text,
            "hints_used": str(result.get("hints_used", result.get("hints", 0)) or 0),
        }
        for key, value in values.items():
            self.stat_labels[key].configure(text=value)
        self.stat_labels["level"].configure(fg=level_color)

        try:
            is_record = bool(result.get("new_record"))
            self.new_record_label.configure(text="🏆 NEW RECORD!" if is_record else "")
            level_id = result.get("challenge")
            if level_id in LEVEL_BY_ID:
                rec = self.app.record_for_level(level_id)
                bt = rec.get("best_time")
                bm = rec.get("best_moves")
                be = rec.get("best_efficiency")
                self.record_info_label.configure(
                    text=f"Best Time: {format_record_time(bt) if bt is not None else '—'} · Least Moves: {bm if bm is not None else '—'} · Highest Efficiency: {f'{float(be):.1f}%' if be is not None else '—'}"
                )
            else:
                self.record_info_label.configure(text="")
        except Exception:
            pass

        new_id = result.get("newly_unlocked")
        new_name = result.get("newly_unlocked_name")
        changed = bool(result.get("progress_changed"))

        if new_id and new_name:
            new_color = LEVEL_BY_ID.get(new_id, {}).get("color", COLOR_SUCCESS)
            self.progress_kicker.configure(
                text="NEW CHALLENGE UNLOCKED", fg=COLOR_SUCCESS
            )
            self.progress_name.configure(
                text=f"{new_name} Unlocked", fg=new_color
            )
            prompt = changed
        elif changed:
            self.progress_kicker.configure(
                text="PROGRESS UPDATED", fg=COLOR_ACCENT
            )
            if result.get("challenge") == LEVEL_ORDER[-1]:
                self.progress_name.configure(
                    text="All four challenges completed", fg=COLOR_SUCCESS
                )
            else:
                self.progress_name.configure(
                    text="Challenge progress recorded", fg=COLOR_TEXT_STRONG
                )
            prompt = True
        else:
            self.progress_kicker.configure(
                text="CHALLENGE REPLAYED", fg=COLOR_MUTED
            )
            self.progress_name.configure(
                text="No new challenge unlocked", fg=COLOR_TEXT
            )
            prompt = False

        self.save_status_label.configure(text="")
        if prompt and self.app.progress_dirty:
            self.save_row.pack(
                fill="x", pady=(6, 0), before=self.save_status_label
            )
            self.save_button.configure(state="normal", text="SAVE PROGRESS")
        else:
            self.save_row.pack_forget()

        next_id = result.get("next_challenge")
        if next_id and self.app.is_unlocked(next_id):
            self._next_level_id = next_id
            self.next_button.pack(
                fill="x", pady=(0, 3), before=self.play_current_button
            )
        else:
            self._next_level_id = None
            self.next_button.pack_forget()
        # PLAY CURRENT LEVEL AGAIN is always visible; ensure it is packed.
        try:
            if not self.play_current_button.winfo_ismapped():
                self.play_current_button.pack(fill="x", pady=(0, 3), before=self.view_results_button)
        except tk.TclError:
            pass

    # -- actions ---------------------------------------------------------------
    def save_progress(self):
        ok, error = self.app.save_progress()
        if ok:
            self.save_status_label.configure(
                text="Progress saved. It will be restored next time.",
                fg=COLOR_SUCCESS,
            )
            self.save_row.pack_forget()
        else:
            self.save_status_label.configure(
                text=f"Could not save progress: {error}",
                fg=COLOR_DANGER,
            )

    def continue_without_saving(self):
        self.save_row.pack_forget()
        self.save_status_label.configure(
            text="Progress kept for this session only.", fg=COLOR_MUTED
        )

    def start_next_challenge(self):
        if self._next_level_id and self.app.is_unlocked(self._next_level_id):
            self.app.start_challenge(self._next_level_id)

    def play_current_level_again(self):
        """Restart the same challenge tier with a new random DFS maze."""
        level_id = getattr(self, "current_level_id", None)
        if not level_id:
            result = self.app.last_result or {}
            level_id = result.get("challenge")
            self.current_level_id = level_id
        if level_id and self.app.is_unlocked(level_id):
            self.app.start_challenge(level_id)
            return
        if level_id:
            # Fallback if the stored id is unexpectedly locked: still try.
            self.current_level_id = level_id
            self.app.active_challenge = level_id
            self.app.show_screen("gameplay")
            return
        self.app.show_screen("gameplay")


# ---------------------------------------------------------------------------
# Instructions
# ---------------------------------------------------------------------------
class InstructionsScreen(Screen):
    title = "Instructions"

    CONTROLS = (
        ("W A S D  /  Arrow Keys", "Move"),
        ("H", "Smart Hint"),
        ("ENTER", "AI Solver"),
        ("P", "Pause / Resume"),
    )

    FEATURES = (
        "Four Challenge Tiers",
        "Fresh Maze Every Game",
        "AI Solver & Hints",
        "Optimal Path Comparison",
    )

    def build(self):
        card = tk.Frame(
            center_container(self),
            bg=COLOR_PANEL,
            padx=48,
            pady=22,
            highlightbackground=COLOR_BORDER,
            highlightthickness=1,
        )
        card.pack()

        tk.Label(
            card,
            text="Instructions",
            font=HEADING_FONT,
            bg=COLOR_PANEL,
            fg=COLOR_TEXT_STRONG,
        ).pack(anchor="w")

        tk.Label(
            card,
            text="Everything you need to play, including challenge progression.",
            font=SMALL_FONT,
            bg=COLOR_PANEL,
            fg=COLOR_MUTED,
        ).pack(anchor="w", pady=(4, 0))

        # --- controls --------------------------------------------------------
        section_label(card, "CONTROLS", pad_top=12)

        controls = tk.Frame(card, bg=COLOR_PANEL)
        controls.pack(fill="x", pady=(6, 0))
        controls.grid_columnconfigure(0, minsize=214)

        for row, (keys, action) in enumerate(self.CONTROLS):
            tk.Label(
                controls,
                text=keys,
                font=(FONT_FAMILY, 11, "bold"),
                bg=COLOR_PANEL_ALT,
                fg=COLOR_ACCENT,
                padx=12,
                pady=5,
                highlightthickness=1,
                highlightbackground=COLOR_BORDER,
            ).grid(row=row, column=0, sticky="w", pady=3)

            tk.Label(
                controls,
                text=f"= {action}",
                font=BODY_FONT,
                bg=COLOR_PANEL,
                fg=COLOR_TEXT,
            ).grid(row=row, column=1, sticky="w", pady=3)

        # --- goal ------------------------------------------------------------
        section_label(card, "GOAL", pad_top=10)

        goal_row = tk.Frame(card, bg=COLOR_PANEL)
        goal_row.pack(fill="x", pady=(6, 0))

        goal_cell = tk.Frame(goal_row, bg=COLOR_DANGER, width=16, height=16)
        goal_cell.pack(side="left")
        goal_cell.pack_propagate(False)

        tk.Label(
            goal_row,
            text="Reach the red goal cell.",
            font=BODY_FONT,
            bg=COLOR_PANEL,
            fg=COLOR_TEXT,
        ).pack(side="left", padx=(12, 0))

        # --- features --------------------------------------------------------
        section_label(card, "FEATURES", pad_top=10)

        features = tk.Frame(card, bg=COLOR_PANEL)
        features.pack(fill="x", pady=(6, 0))

        for index, feature in enumerate(self.FEATURES):
            row, column = divmod(index, 2)

            item = tk.Frame(features, bg=COLOR_PANEL)
            item.grid(row=row, column=column, sticky="w", pady=4, padx=(0, 36))

            tk.Label(
                item,
                text="•",
                font=(FONT_FAMILY, 13, "bold"),
                bg=COLOR_PANEL,
                fg=COLOR_ACCENT,
            ).pack(side="left")

            tk.Label(
                item,
                text=feature,
                font=BODY_FONT,
                bg=COLOR_PANEL,
                fg=COLOR_TEXT,
            ).pack(side="left", padx=(8, 0))

        # --- back ------------------------------------------------------------
        hline(card, pad_y=14)

        MenuButton(
            card,
            "Back to Home",
            command=lambda: self.app.show_screen("home"),
            variant="primary",
            width=22,
        ).pack(fill="x")


# ---------------------------------------------------------------------------
# Application / navigation
# ---------------------------------------------------------------------------
SCREENS = {
    "splash": SplashScreen,
    "home": HomeScreen,
    "achievements": AchievementsScreen,
    "challenges": ChallengeSelectionScreen,
    "settings": SettingsScreen,
    "gameplay": GameplayScreen,
    "challenge_complete": ChallengeCompleteScreen,
    "player_complete": PlayerCompleteScreen,
    "results": ResultsScreen,
    "instructions": InstructionsScreen,
    "ai_complete": AICompleteScreen,
}


class MazeAdventureApp(tk.Tk):
    """Root window. Owns the screens and switches between them."""

    def __init__(self, fullscreen=True):
        super().__init__()

        self.title(APP_WINDOW_TITLE)
        self.configure(bg=COLOR_BG)
        self.geometry("1280x800")
        self.minsize(1024, 640)
        self.protocol("WM_DELETE_WINDOW", self.exit_app)

        # Runtime icon (bundled next to the source or inside the .exe).
        self._icon_path = resource_path("assets", "maze.ico")
        self._apply_window_icon(self)

        # Shared application state. The Custom Challenge screen writes here;
        # the gameplay screen reads it for non-tiered runs.
        self.settings = {
            "difficulty": "Medium",
            "rows": 21,
            "cols": 21,
        }

        # Challenge progression lives in memory until the player chooses to
        # save. A missing or broken save file simply starts at Beginner.
        self.progress_path = progress_file_path()
        self.progress = load_progress(self.progress_path)
        self.unlocked = set(self.progress.get("unlocked", []))
        self.completed = set(self.progress.get("completed", []))
        self.records = _copy_records(_normalize_records(self.progress.get("records")))
        self.best_records = self.records
        self.best_overall = dict(self.records.get(CUSTOM_LEVEL_ID, _blank_record()))
        self.custom_records = self.records.get(CUSTOM_LEVEL_ID, _blank_record())
        self.achievements = set(_normalize_achievements(self.progress.get("achievements", [])))
        self.replay_counts = _normalize_replay_counts(self.progress.get("replay_counts"))
        self.replays = self.replay_counts
        self.custom_replay_count = int(self.replay_counts.get(CUSTOM_LEVEL_ID, 0) or 0)
        self.progress_dirty = False
        # Custom achievement progress is tracked separately so the challenge
        # dirty flag (and its existing tests) is unaffected. The two are saved
        # together via save_progress() when the player chooses SAVE PROGRESS.
        self.custom_save_pending = False
        self.active_challenge = None

        self.last_result = None    # filled in by the gameplay screen on completion
        self.current_screen = None
        # Kept for backward compatibility (always None; no fade animation).
        self._transition_job = None

        # --- status bar (bottom) ---------------------------------------------
        status = tk.Frame(self, bg=COLOR_PANEL, height=30)
        status.pack(side="bottom", fill="x")
        status.pack_propagate(False)

        self.status_label = tk.Label(
            status, text="", font=SMALL_FONT, bg=COLOR_PANEL, fg=COLOR_MUTED
        )
        self.status_label.pack(side="left", padx=14)

        tk.Label(
            status,
            text="ESC / F11 — toggle fullscreen",
            font=SMALL_FONT,
            bg=COLOR_PANEL,
            fg=COLOR_MUTED,
        ).pack(side="right", padx=14)

        # --- screen container -------------------------------------------------
        self.container = tk.Frame(self, bg=COLOR_BG)
        self.container.pack(fill="both", expand=True)
        self.container.grid_rowconfigure(0, weight=1)
        self.container.grid_columnconfigure(0, weight=1)

        self.screens = {}
        for name, screen_class in SCREENS.items():
            screen = screen_class(self)
            screen.grid(row=0, column=0, sticky="nsew")
            self.screens[name] = screen

        # --- fullscreen -------------------------------------------------------
        self._fullscreen = bool(fullscreen)
        self.attributes("-fullscreen", self._fullscreen)
        self.bind("<Escape>", self.toggle_fullscreen)
        self.bind("<F11>", self.toggle_fullscreen)

        self.show_screen("splash")
        if not self._fullscreen:
            self._center_windowed()

    # -- branding / errors ----------------------------------------------------
    def _apply_window_icon(self, window):
        """Apply the bundled .ico to the main window or a dialog."""
        if not self._icon_path or not os.path.exists(self._icon_path):
            return
        try:
            window.iconbitmap(self._icon_path)
        except tk.TclError:
            pass

    def report_callback_exception(self, exc, value, tb):
        """Show a friendly dialog instead of dying on a callback error."""
        message = f"{exc.__name__}: {value}"
        try:
            messagebox.showerror(
                APP_TITLE,
                "The application hit an unexpected problem.\n\n"
                f"{message}\n\n"
                "You can keep playing, or return to the main menu.",
                parent=self,
            )
        except Exception:
            pass

    # -- navigation -----------------------------------------------------------
    def show_screen(self, name):
        """Raise the screen called ``name`` ("home", "settings", ...)."""
        if name not in self.screens:
            raise ValueError(f"Unknown screen: {name!r}")

        screen = self.screens[name]
        previous = self.screens.get(self.current_screen)
        if previous is not None and previous is not screen:
            previous.on_hide()

        self.current_screen = name
        screen.on_show()
        screen.tkraise()
        self.status_label.configure(text=screen.title)

        # Keyboard focus belongs to the window, never to a button on the
        # screen that just went away.
        try:
            self.focus_set()
        except tk.TclError:
            pass

    # -- challenge progression ------------------------------------------------
    def current_level(self):
        """The active tier's metadata, or None for a custom challenge."""
        return LEVEL_BY_ID.get(self.active_challenge)

    def is_unlocked(self, level_id):
        return level_id in self.unlocked

    def is_completed(self, level_id):
        return level_id in self.completed

    def _set_progress(self, progress):
        """Normalise a progress record and refresh the in-memory sets."""
        had_records = isinstance(progress, dict) and any(
            key in progress for key in ("records", "best_records", "bestRecords")
        )
        had_achievements = isinstance(progress, dict) and any(
            key in progress for key in ("achievements", "achievements_unlocked")
        )
        had_replays = isinstance(progress, dict) and any(
            key in progress for key in ("replay_counts", "replays", "replayCounts")
        )
        self.progress = normalize_progress(progress)
        self.unlocked = set(self.progress.get("unlocked", []))
        self.completed = set(self.progress.get("completed", []))
        if had_records:
            self.records = _copy_records(_normalize_records(self.progress.get("records")))
        # Preserve records unless explicitly provided (e.g. complete_challenge
        # passes only unlocked/completed and must not wipe best records).
        self.best_records = self.records
        if had_achievements:
            self.achievements = set(_normalize_achievements(self.progress.get("achievements", [])))
        if had_replays:
            self.replay_counts = _normalize_replay_counts(self.progress.get("replay_counts"))
            self.replays = self.replay_counts
        self._sync_progress_dict()

    def _sync_progress_dict(self):
        """Mirror in-memory records/achievements/replays into self.progress."""
        if not hasattr(self, "records"):
            self.records = default_records()
        if not hasattr(self, "achievements"):
            self.achievements = set()
        if not hasattr(self, "replay_counts"):
            self.replay_counts = default_replay_counts()
        expanded = _copy_records(self.records)
        self.records = expanded
        self.best_records = expanded
        self.best_overall = dict(expanded.get(CUSTOM_LEVEL_ID, _blank_record()))
        self.custom_records = expanded.get(CUSTOM_LEVEL_ID, _blank_record())
        self.replay_counts = dict(self.replay_counts)
        self.replays = self.replay_counts
        self.custom_replay_count = int(self.replay_counts.get(CUSTOM_LEVEL_ID, 0) or 0)
        if not hasattr(self, "progress") or self.progress is None:
            self.progress = default_progress()
        self.progress["records"] = expanded
        self.progress["best_records"] = expanded
        self.progress["best_overall"] = dict(expanded.get(CUSTOM_LEVEL_ID, _blank_record()))
        self.progress["achievements"] = [
            level_id for level_id in ACHIEVEMENT_ORDER if level_id in self.achievements
        ]
        self.progress["replay_counts"] = dict(self.replay_counts)
        self.progress["replays"] = dict(self.replay_counts)
        self.progress["custom_replays"] = int(self.replay_counts.get(CUSTOM_LEVEL_ID, 0) or 0)
        self.progress["unlocked"] = [level_id for level_id in LEVEL_ORDER if level_id in self.unlocked]
        self.progress["completed"] = [level_id for level_id in LEVEL_ORDER if level_id in self.completed]

    def is_achievement_unlocked(self, achievement_id):
        return achievement_id in self.achievements

    def unlock_achievement(self, achievement_id, notify=True):
        """Unlock an achievement once (tracking/display only, no popup/sound).

        Does not set ``progress_dirty`` itself: the caller decides whether
        the surrounding progress change (challenge completion / replay)
        should mark the save dirty, preserving the existing save flow.
        """
        if achievement_id not in ACHIEVEMENT_BY_ID:
            return False
        if achievement_id in self.achievements:
            return False
        self.achievements.add(achievement_id)
        self._sync_progress_dict()
        # Treasure Hunter: all other achievements -> treasure hunter itself.
        # Checked after every new unlock so the meta-achievement fires last.
        if achievement_id != "treasure_hunter":
            others = [item for item in ACHIEVEMENT_ORDER if item != "treasure_hunter"]
            if all(item in self.achievements for item in others):
                # Avoid recursion via direct add.
                self.achievements.add("treasure_hunter")
                self._sync_progress_dict()
                return True
        return True

    def check_state_achievements(self, notify=True):
        """State-derived achievements: maze master + treasure hunter."""
        newly = []
        if set(LEVEL_ORDER).issubset(self.completed):
            if self.unlock_achievement("maze_master", notify=False):
                newly.append("maze_master")
        # Treasure hunter requires every other achievement.
        others = [item for item in ACHIEVEMENT_ORDER if item != "treasure_hunter"]
        if all(item in self.achievements for item in others):
            if self.unlock_achievement("treasure_hunter", notify=False):
                newly.append("treasure_hunter")
        return newly

    def evaluate_achievements_for_result(self, result):
        """Check run-based achievements for a human completion."""
        if not isinstance(result, dict):
            return []
        if result.get("ai"):
            return []
        newly = []

        def _try(achievement_id):
            if self.unlock_achievement(achievement_id, notify=False):
                newly.append(achievement_id)

        # First Victory: any human completion.
        _try("first_victory")
        # Hint Free.
        try:
            hints = int(result.get("hints_used", result.get("hints", 0)) or 0)
        except (TypeError, ValueError):
            hints = 0
        if hints == 0:
            _try("hint_free")
        # Speed Runner: under 60 seconds.
        try:
            seconds = float(result.get("seconds", result.get("time", 0)) or 0)
            # result["time"] is a string; prefer integer seconds when present.
            if "seconds" not in result:
                # Fallback: treat string time as already parsed elsewhere.
                seconds = float(result.get("seconds", 0) or 0)
        except (TypeError, ValueError):
            seconds = 0
        if seconds < 60:
            _try("speed_runner")
        # Efficiency.
        try:
            efficiency = float(result.get("efficiency", 0) or 0)
        except (TypeError, ValueError):
            efficiency = 0.0
        if efficiency >= 90.0:
            _try("efficient_navigator")
        if efficiency >= 99.99:
            _try("perfectionist")
        # Conquerors (challenge tiers).
        challenge_id = result.get("challenge")
        if challenge_id == "beginner":
            _try("beginner_conqueror")
        elif challenge_id == "intermediate":
            _try("intermediate_conqueror")
        elif challenge_id == "advanced":
            _try("advanced_conqueror")
        elif challenge_id == "expert":
            _try("expert_conqueror")
        # State-derived (after completed is updated).
        for achievement_id in self.check_state_achievements(notify=False):
            if achievement_id not in newly:
                newly.append(achievement_id)
        if newly and result.get("challenge"):
            # Challenge achievements ride on the existing save flow; custom
            # achievements are kept in memory and saved with the next
            # challenge save (custom runs have no save prompt of their own).
            self.progress_dirty = True
            self._sync_progress_dict()
        elif newly:
            # Custom-run achievements are tracked separately from challenge
            # progression so the existing challenge dirty flag (and its
            # tests) is unaffected. They are saved via the Player Complete
            # SAVE PROGRESS option using the same progress file.
            self.custom_save_pending = True
            self._sync_progress_dict()
        return newly

    def update_best_records(self, result):
        """Update bests for a human win (challenge level or custom overall).

        Challenge wins update only that level; custom wins update only the
        separate ``custom`` bucket (best overall) and never touch challenge
        records, unlocked tiers or completed status.
        """
        summary = {
            "best_time": False,
            "best_moves": False,
            "best_efficiency": False,
            "new_record": False,
        }
        if not isinstance(result, dict) or result.get("ai"):
            return summary
        level_id = result.get("challenge")
        is_custom = level_id is None
        if is_custom:
            level_id = CUSTOM_LEVEL_ID
        elif level_id not in LEVEL_BY_ID:
            return summary
        try:
            seconds = int(result.get("seconds", 0) or 0)
        except (TypeError, ValueError):
            seconds = 0
        try:
            moves = int(result.get("moves", 0) or 0)
        except (TypeError, ValueError):
            moves = 0
        try:
            efficiency = float(result.get("efficiency", 0) or 0)
        except (TypeError, ValueError):
            efficiency = 0.0
        # Custom replays count toward Explorer after the first custom win.
        had_custom = False
        if is_custom:
            try:
                had_custom = self.records.get(CUSTOM_LEVEL_ID, {}).get("best_time") is not None
            except AttributeError:
                had_custom = False
        entry = self.records[level_id]
        # Ensure entry has canonical keys even if expanded aliases exist.
        best_time = entry.get("best_time")
        if best_time is None or seconds < int(best_time):
            entry["best_time"] = seconds
            summary["best_time"] = True
        best_moves = entry.get("best_moves")
        if best_moves is None or moves < int(best_moves):
            entry["best_moves"] = moves
            summary["best_moves"] = True
        best_eff = entry.get("best_efficiency")
        if best_eff is None or efficiency > float(best_eff):
            entry["best_efficiency"] = efficiency
            summary["best_efficiency"] = True
        if summary["best_time"] or summary["best_moves"] or summary["best_efficiency"]:
            summary["new_record"] = True
            if is_custom:
                self.custom_save_pending = True
            else:
                self.progress_dirty = True
            # Expand aliases so every spelling stays in sync in memory & file.
            self.records[level_id] = entry
            self._sync_progress_dict()
        if is_custom and had_custom:
            # A subsequent custom completion is a replay of a custom maze.
            self.replay_counts[CUSTOM_LEVEL_ID] = int(self.replay_counts.get(CUSTOM_LEVEL_ID, 0) or 0) + 1
            self.custom_replay_count = int(self.replay_counts[CUSTOM_LEVEL_ID])
            self.custom_save_pending = True
            self._sync_progress_dict()
            if self.replay_counts[CUSTOM_LEVEL_ID] >= 5 and "explorer" not in self.achievements:
                self.unlock_achievement("explorer")
        return summary

    def record_for_level(self, level_id):
        if level_id == CUSTOM_LEVEL_ID:
            return dict(self.records.get(CUSTOM_LEVEL_ID, _blank_record()))
        if level_id not in LEVEL_BY_ID:
            return _blank_record()
        return dict(self.records.get(level_id, _blank_record()))

    def achievement_display(self, achievement_id):
        return ACHIEVEMENT_BY_ID.get(achievement_id, achievement_id)

    # Achievements are tracked and displayed only (no popups/notifications).

    def start_challenge(self, level_id):
        """Start a tier with a fresh random maze of its fixed dimensions."""
        level = LEVEL_BY_ID.get(level_id)
        if level is None or not self.is_unlocked(level_id):
            return False

        # Replay counting (Explorer): starting an already-completed level
        # counts as a replay of that level. One increment per start only.
        if level_id in self.completed:
            self.replay_counts[level_id] = int(self.replay_counts.get(level_id, 0) or 0) + 1
            self.progress_dirty = True
            self._sync_progress_dict()
            if self.replay_counts[level_id] >= 5:
                # Unlock Explorer (and possibly Treasure Hunter) via toast.
                if "explorer" not in self.achievements:
                    self.unlock_achievement("explorer")

        self.active_challenge = level_id
        self.show_screen("gameplay")
        return True

    def complete_challenge(self, level_id):
        """Record a human win, unlock the next tier and report what changed."""
        level = LEVEL_BY_ID.get(level_id)
        empty = {
            "newly_unlocked": None,
            "newly_unlocked_name": None,
            "next_challenge": None,
            "next_challenge_name": None,
            "changed": False,
        }
        if level is None or not self.is_unlocked(level_id):
            return empty

        changed = False
        if level_id not in self.completed:
            self.completed.add(level_id)
            changed = True

        index = LEVEL_ORDER.index(level_id)
        next_id = LEVEL_ORDER[index + 1] if index + 1 < len(LEVEL_ORDER) else None
        newly_unlocked = None

        if next_id and next_id not in self.unlocked:
            self.unlocked.add(next_id)
            newly_unlocked = next_id
            changed = True

        if changed:
            self.progress_dirty = True
            self._set_progress(
                {
                    "unlocked": self.unlocked,
                    "completed": self.completed,
                    "records": self.records,
                    "achievements": list(self.achievements),
                    "replay_counts": dict(self.replay_counts),
                }
            )

        return {
            "newly_unlocked": newly_unlocked,
            "newly_unlocked_name": (
                LEVEL_BY_ID[newly_unlocked]["name"] if newly_unlocked else None
            ),
            "next_challenge": next_id,
            "next_challenge_name": (
                LEVEL_BY_ID[next_id]["name"] if next_id else None
            ),
            "changed": changed,
        }

    def save_progress(self):
        """Save unlocked/completed tiers + records + achievements. Returns ``(ok, error_message)``."""
        try:
            self._sync_progress_dict()
            data = save_progress_data(self.progress, self.progress_path)
        except OSError as error:
            return False, str(error)

        self._set_progress(data)
        self.progress_dirty = False
        self.custom_save_pending = False
        return True, None

    def reset_progress(self):
        """Delete the save file and return to a Beginner-only state."""
        self._set_progress(default_progress())
        self.progress_dirty = False
        self.custom_save_pending = False
        self.active_challenge = None

        try:
            clear_progress_file(self.progress_path)
        except OSError as error:
            return False, str(error)
        return True, None

    # -- window ---------------------------------------------------------------
    def toggle_fullscreen(self, _event=None):
        self._fullscreen = not self._fullscreen
        self.attributes("-fullscreen", self._fullscreen)
        if not self._fullscreen:
            self._center_windowed()
        return "break"

    def _center_windowed(self):
        width, height = 1280, 800
        x = (self.winfo_screenwidth() - width) // 2
        y = (self.winfo_screenheight() - height) // 2
        self.geometry(f"{width}x{height}+{max(x, 0)}+{max(y, 0)}")

    def exit_app(self):
        # Cancel timers/animations before Tk destroys the widgets, otherwise a
        # pending after() callback can fire against a dead canvas.
        if self._transition_job is not None:
            try:
                self.after_cancel(self._transition_job)
            except tk.TclError:
                pass
            self._transition_job = None

        current = self.screens.get(self.current_screen)
        if current is not None:
            try:
                current.on_hide()
            except Exception:
                pass
        self.destroy()


def _show_startup_error(error):
    """Last-resort dialog used when the app cannot build its main window."""
    try:
        root = tk.Tk()
        root.withdraw()
        messagebox.showerror(
            APP_TITLE,
            "Maze Adventure AI could not start.\n\n"
            f"{type(error).__name__}: {error}",
        )
        root.destroy()
    except Exception:
        pass


def main():
    # `--windowed` keeps the app in a normal window - useful while building the game.
    try:
        app = MazeAdventureApp(fullscreen="--windowed" not in sys.argv)
    except Exception as error:
        _show_startup_error(error)
        return

    try:
        app.mainloop()
    except Exception as error:
        try:
            app.destroy()
        except Exception:
            pass
        _show_startup_error(error)


if __name__ == "__main__":
    main()
