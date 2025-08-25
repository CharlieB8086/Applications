#!/usr/bin/env python3
# FloorPlan360 — Tkinter floor-plan editor with selection, marquee, rulers, and PNG export
# Requires: Pillow   ->  pip install pillow

import json, math, sys, tkinter as tk
from tkinter import filedialog, simpledialog, messagebox
from typing import Optional, List, Tuple
from PIL import Image, ImageDraw, ImageFont, ImageTk, ImageGrab

# ---------- Config ----------
GRID_SIZE_PX = 32
GRID_METERS = 0.5
MIN_ZOOM, MAX_ZOOM = 0.4, 2.5

WALL_COLOR = "#222222"
ROOM_FILL = "#c7e6ff"
ROOM_OUTLINE = "#3a78a8"
DOOR_COLOR = "#2a8f2a"
WINDOW_COLOR = "#1f6fbd"
SELECT_COLOR = "#ff6b6b"
TEXT_COLOR = "#111111"
GRID_COLOR = "#e8e8e8"

HIT_TOL = 8
HANDLE_SIZE = 8
ROTATE_HANDLE_OFFSET = 28
MEASURE_OFFSET = 28  # distance (in px @ 1.0 zoom) to push measurement labels off the line

def clamp(v, lo, hi): return max(lo, min(hi, v))

def dist_point_to_segment(px, py, x1, y1, x2, y2):
    dx, dy = x2 - x1, y2 - y1
    if dx == dy == 0:
        return math.hypot(px - x1, py - y1)
    t = max(0, min(1, ((px - x1) * dx + (py - y1) * dy) / (dx*dx + dy*dy)))
    qx, qy = x1 + t*dx, y1 + t*dy
    return math.hypot(px - qx, py - qy)

def screen_angle(cx, cy, px, py):
    # y-axis inverted in canvas; use cy - py so clockwise drag rotates clockwise
    return math.degrees(math.atan2(cy - py, px - cx))

def seg_normal(x1, y1, x2, y2):
    nx, ny = x2 - x1, y2 - y1
    L = math.hypot(nx, ny) or 1.0
    nx, ny = -ny / L, nx / L
    return nx, ny

def rect_norm(x0,y0,x1,y1):
    return (min(x0,x1), min(y0,y1), max(x0,x1), max(y0,y1))

def point_in_rect(px, py, r):
    x0,y0,x1,y1 = rect_norm(*r)
    return (x0 <= px <= x1) and (y0 <= py <= y1)

def seg_intersects_rect(p1, p2, r):
    # coarse: endpoint inside OR intersects any edge
    if point_in_rect(*p1, r) or point_in_rect(*p2, r): return True
    x0,y0,x1,y1 = rect_norm(*r)
    edges = [((x0,y0),(x1,y0)),((x1,y0),(x1,y1)),((x1,y1),(x0,y1)),((x0,y1),(x0,y0))]
    return any(segments_intersect(p1,p2,e[0],e[1]) for e in edges)

def ccw(a,b,c): return (c[1]-a[1])*(b[0]-a[0]) > (b[1]-a[1])*(c[0]-a[0])
def segments_intersect(a,b,c,d):
    return (ccw(a,c,d) != ccw(b,c,d)) and (ccw(a,b,c) != ccw(a,b,d))

class Item:
    def __init__(self, kind, data):
        self.kind = kind
        self.data = data
        self.cid = None
        self.selected = False
        # text caches
        self._pil_img = None
        self._tk_img = None
        self._last_render_key = None
        self._bbox_canvas = None  # for text picking

    def to_json(self): return {"kind": self.kind, "data": self.data}
    @staticmethod
    def from_json(obj): return Item(obj["kind"], obj["data"])

class FloorPlanApp(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("FloorPlan360 — Editor/Viewer")
        self.geometry("1200x800")

        # state
        self.items: List[Item] = []
        self.active_tool = tk.StringVar(value="select")
        self.snap_enabled = tk.BooleanVar(value=True)
        self.grid_m = tk.DoubleVar(value=GRID_METERS)
        self.zoom = 1.0
        self.origin = [80, 80]
        self.temp_preview = None
        self.draw_state = {}
        self.selection: Optional[Item] = None     # single selection (for transforms)
        self.selected_items: List[Item] = []      # multi-selection (marquee)
        self._pan = {"active": False, "space": False, "start": (0,0)}
        try:
            self.iconbitmap("RSFP2.ico")   # place icon.ico in same folder # This is the new Logo
        except Exception as e:
            print("Could not load icon:", e)

        # new: units + rulers
        self.unit = tk.StringVar(value="m")           # m, cm, mm, ft-in
        self.keep_rulers = tk.BooleanVar(value=False) # keep multiple?
        self.rulers: List[Tuple[Tuple[float,float],Tuple[float,float]]] = []

        self._build_ui()
        self._wire_events()
        self._redraw()

    # -------- UI ----------
    def _build_ui(self):
        self.configure(bg="#0f131a")
        tb = tk.Frame(self, bg="#111720"); tb.pack(side=tk.LEFT, fill=tk.Y)

        def tool(txt,val):
            b = tk.Radiobutton(tb, text=txt, value=val, variable=self.active_tool,
                               indicatoron=False, width=16, pady=8,
                               command=self._tool_changed,
                               bg="#111720", fg="#e8ecf2",
                               selectcolor="#18212e",
                               activebackground="#18212e", activeforeground="#e8ecf2",
                               relief="flat", bd=0)
            b.pack(padx=8, pady=4)
            return b

        tool("Select / Move", "select")
        tool("Wall", "wall")
        tool("Room (Rect)", "room")
        tool("Door", "door")
        tool("Window", "window")
        tool("Text Label", "text")
        tool("Ruler", "ruler")
        tool("Eraser", "eraser")

        opt = tk.LabelFrame(tb, text="Options", bg="#111720", fg="#e8ecf2", bd=0)
        opt.pack(fill=tk.X, padx=8, pady=8)
        tk.Checkbutton(opt, text="Snap to grid", variable=self.snap_enabled,
                       bg="#111720", fg="#e8ecf2",
                       activebackground="#18212e", activeforeground="#e8ecf2",
                       selectcolor="#18212e").pack(anchor="w", padx=8, pady=2)

        r1 = tk.Frame(opt, bg="#111720"); r1.pack(fill=tk.X, padx=8, pady=4)
        tk.Label(r1, text="Meters / grid:", bg="#111720", fg="#e8ecf2").pack(side=tk.LEFT)
        e = tk.Entry(r1, textvariable=self.grid_m, width=6, relief="flat")
        e.pack(side=tk.LEFT, padx=6)

        urow = tk.Frame(opt, bg="#111720"); urow.pack(fill=tk.X, padx=8, pady=4)
        tk.Label(urow, text="Units:", bg="#111720", fg="#e8ecf2").pack(side=tk.LEFT)
        tk.OptionMenu(urow, self.unit, "m", "cm", "mm", "ft-in").pack(side=tk.LEFT, padx=6)

        tk.Checkbutton(opt, text="Keep rulers", variable=self.keep_rulers,
                       bg="#111720", fg="#e8ecf2",
                       activebackground="#18212e", activeforeground="#e8ecf2",
                       selectcolor="#18212e").pack(anchor="w", padx=8, pady=2)

        files = tk.LabelFrame(tb, text="File", bg="#111720", fg="#e8ecf2", bd=0)
        files.pack(fill=tk.X, padx=8, pady=8)
        for txt, cmd in [
            ("New", self.new_file),
            ("Save JSON", self.save_json),
            ("Load JSON", self.load_json),
            ("Export PNG", self.export_png),   # <-- export button
        ]:
            tk.Button(files, text=txt, command=cmd, relief="flat",
                      bg="#18212e", fg="#e8ecf2").pack(fill=tk.X, padx=6, pady=3)
            
            

        view = tk.LabelFrame(tb, text="View", bg="#111720", fg="#e8ecf2", bd=0)
        view.pack(fill=tk.X, padx=8, pady=8)
        tk.Button(view, text="Zoom +", command=lambda: self._zoom(1.1), relief="flat", bg="#18212e", fg="#e8ecf2").pack(fill=tk.X, padx=6, pady=3)
        tk.Button(view, text="Zoom -", command=lambda: self._zoom(1/1.1), relief="flat", bg="#18212e", fg="#e8ecf2").pack(fill=tk.X, padx=6, pady=3)
        tk.Button(view, text="Reset View", command=self._reset_view, relief="flat", bg="#18212e", fg="#e8ecf2").pack(fill=tk.X, padx=6, pady=3)

        right = tk.Frame(self); right.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self.canvas = tk.Canvas(right, bg="#fbfdff", highlightthickness=0); self.canvas.pack(fill=tk.BOTH, expand=True)
        self.status = tk.StringVar(value="Ready.")
        tk.Label(right, textvariable=self.status, anchor="w").pack(fill=tk.X)

        tk.Label(tb, text="Shortcuts:\nSpace+Drag: Pan\nDel: Delete selection\nCtrl+S/O: Save/Load\nCtrl+E: Export PNG\n+ / -: Zoom\nShift: Proportional (text)",
                 justify="left", bg="#111720", fg="#a9b3c1").pack(padx=8, pady=8)

    def _wire_events(self):
        c = self.canvas
        c.bind("<Configure>", lambda e: self._redraw())
        c.bind("<ButtonPress-1>", self._on_left_down)
        c.bind("<B1-Motion>", self._on_left_drag)
        c.bind("<ButtonRelease-1>", self._on_left_up)
        c.bind("<Button-3>", self._on_right_click)

        # pan
        c.bind("<ButtonPress-2>", self._on_pan_start)
        c.bind("<B2-Motion>", self._on_pan_drag)
        c.bind("<ButtonRelease-2>", self._on_pan_end)
        self.bind("<space>", lambda e: self._set_pan(True))
        self.bind("<KeyRelease-space>", lambda e: self._set_pan(False))

        # keys
        self.bind("<Delete>", lambda e: self.delete_selection())
        self.bind("<Control-s>", lambda e: (self.save_json(), "break"))
        self.bind("<Control-o>", lambda e: (self.load_json(), "break"))
        self.bind("<Control-e>", lambda e: (self.export_png(), "break"))
        self.bind("+", lambda e: self._zoom(1.1))
        self.bind("-", lambda e: self._zoom(1/1.1))
        c.bind("<Motion>", self._on_motion)

    # -------- coords ----------
    def grid_px(self): return GRID_SIZE_PX * self.zoom
    def world_to_canvas(self, x, y): return (self.origin[0] + x * self.grid_px(), self.origin[1] + y * self.grid_px())
    def canvas_to_world(self, px, py): return ((px - self.origin[0]) / self.grid_px(), (py - self.origin[1]) / self.grid_px())
    def snap_world(self, wx, wy):
        if not self.snap_enabled.get(): return wx, wy
        return round(wx), round(wy)

    # -------- draw ----------
    def _redraw(self):
        c = self.canvas
        c.delete("all")
        self._draw_grid()
        for it in self.items:
            self._draw_item(it)

        # measurement overlays for items
        for it in self.items:
            self._draw_measurement_overlay(it)

        # rulers
        self._draw_rulers()

        # previews
        if self.temp_preview:
            self._draw_preview(*self.temp_preview)

        # selection overlays last
        if len(self.selected_items) > 1:
            self._overlay_group_selection()
        elif self.selection:
            if self.selection.kind == "text":
                self._overlay_text(self.selection)
            elif self.selection.kind == "room":
                self._overlay_room(self.selection)
            elif self.selection.kind in ("wall","door","window"):
                self._overlay_segment(self.selection)

        # marquee rectangle while dragging
        mq = self.draw_state.get("marquee")
        if mq:
            x0,y0 = mq["start_px"]; x1,y1 = mq.get("cur_px",(x0,y0))
            x0,y0,x1,y1 = rect_norm(x0,y0,x1,y1)
            self.canvas.create_rectangle(x0,y0,x1,y1, outline="#4a90e2", dash=(4,2), width=1, fill="", stipple="gray25")

    def _draw_grid(self):
        c = self.canvas
        w, h, step = c.winfo_width(), c.winfo_height(), self.grid_px()
        sx = self.origin[0] % step
        x = sx
        while x < w:
            c.create_line(x, 0, x, h, fill=GRID_COLOR)
            x += step
        sy = self.origin[1] % step
        y = sy
        while y < h:
            c.create_line(0, y, w, y, fill=GRID_COLOR)
            y += step
        c.create_line(0, self.origin[1], w, self.origin[1], fill="#cccccc")
        c.create_line(self.origin[0], 0, self.origin[0], h, fill="#cccccc")

    def _draw_item(self, it: Item):
        c = self.canvas
        if it.kind == "wall":
            p1 = self.world_to_canvas(*it.data["a"]); p2 = self.world_to_canvas(*it.data["b"])
            it.cid = c.create_line(*p1, *p2, fill=WALL_COLOR if not it.selected else SELECT_COLOR,
                                   width=max(2, int(2*self.zoom)))
        elif it.kind == "door":
            p1 = self.world_to_canvas(*it.data["a"]); p2 = self.world_to_canvas(*it.data["b"])
            it.cid = c.create_line(*p1, *p2, fill=DOOR_COLOR if not it.selected else SELECT_COLOR,
                                   width=max(3, int(3*self.zoom)))
        elif it.kind == "window":
            p1 = self.world_to_canvas(*it.data["a"]); p2 = self.world_to_canvas(*it.data["b"])
            it.cid = c.create_line(*p1, *p2, fill=WINDOW_COLOR if not it.selected else SELECT_COLOR,
                                   width=max(3, int(3*self.zoom)), dash=(6,4))
        elif it.kind == "room":
            (x1,y1),(x2,y2) = it.data["a"], it.data["b"]
            p1 = self.world_to_canvas(min(x1,x2), min(y1,y2))
            p2 = self.world_to_canvas(max(x1,x2), max(y1,y2))
            it.cid = c.create_rectangle(*p1, *p2, outline=ROOM_OUTLINE if not it.selected else SELECT_COLOR,
                                        width=max(2, int(2*self.zoom)), fill=ROOM_FILL)
        elif it.kind == "text":
            self._draw_text(it)

    # --- text rendering w/ PIL ---
    def _draw_text(self, it: Item):
        it.data.setdefault("angle", 0.0)
        it.data.setdefault("size", 18)
        it.data.setdefault("color", TEXT_COLOR)
        text = it.data.get("text","Label")
        angle = float(it.data["angle"])
        base_size = int(it.data["size"])
        color = it.data["color"]
        eff_size = max(8, int(base_size * self.zoom))
        key = (text, eff_size, color, int(angle*10))
        if key != it._last_render_key:
            it._pil_img, it._tk_img = self._render_text_image(text, eff_size, color, angle)
            it._last_render_key = key
        cx, cy = self.world_to_canvas(*it.data["p"])
        it.cid = self.canvas.create_image(cx, cy, image=it._tk_img)
        w, h = it._pil_img.size
        it._bbox_canvas = (cx - w//2, cy - h//2, cx + w//2, cy + h//2)

    def _render_text_image(self, text, size, color, angle):
        try:
            font = ImageFont.truetype("arial.ttf", size=size)
        except Exception:
            font = ImageFont.load_default()
        tmp = Image.new("RGBA", (1,1), (0,0,0,0))
        d = ImageDraw.Draw(tmp)
        w, h = d.textbbox((0,0), text, font=font)[2:]
        pad = int(size*0.4)
        img = Image.new("RGBA", (w+2*pad, h+2*pad), (0,0,0,0))
        d = ImageDraw.Draw(img)
        d.text((pad,pad), text, font=font, fill=color)
        if abs(angle) > 0.01:
            img = img.rotate(angle, expand=True, resample=Image.BICUBIC)
        return img, ImageTk.PhotoImage(img)

    # --- previews for drawing tools ---
    def _draw_preview(self, kind, a, b, _more=None):
        c = self.canvas
        if kind in ("wall","door","window"):
            p1 = self.world_to_canvas(*a); p2 = self.world_to_canvas(*b)
            color = {"wall": WALL_COLOR, "door": DOOR_COLOR, "window": WINDOW_COLOR}[kind]
            c.create_line(*p1, *p2, fill=color, width=max(2, int(2*self.zoom)), dash=(4,2))
            meters = math.hypot(b[0]-a[0], b[1]-a[1]) * self.grid_m.get()
            mx,my = (p1[0]+p2[0])/2, (p1[1]+p2[1])/2
            nx,ny = seg_normal(*p1,*p2)
            off = MEASURE_OFFSET * self.zoom
            lx,ly = mx + nx*off, my + ny*off
            c.create_line(mx,my,lx,ly, fill="#9ec7ff", dash=(2,2))
            self._text_badge(lx, ly, self._format_length(meters))
        elif kind == "room":
            p1 = self.world_to_canvas(*a); p2 = self.world_to_canvas(*b)
            self.canvas.create_rectangle(*p1, *p2, outline=ROOM_OUTLINE, dash=(6,4))
        elif kind == "ruler":
            p1 = self.world_to_canvas(*a); p2 = self.world_to_canvas(*b)
            self.canvas.create_line(*p1, *p2, dash=(4,2), width=max(2, int(2*self.zoom)))
            meters = math.hypot(b[0]-a[0], b[1]-a[1]) * self.grid_m.get()
            mx, my = (p1[0]+p2[0])/2, (p1[1]+p2[1])/2
            nx,ny = seg_normal(*p1,*p2)
            off = MEASURE_OFFSET * self.zoom
            lx,ly = mx + nx*off, my + ny*off
            self.canvas.create_line(mx,my,lx,ly, fill="#9ec7ff", dash=(2,2))
            self._text_badge(lx, ly, self._format_length(meters))

    # -------- overlays (selection handles) --------
    def _handle_size(self): return max(6, int(HANDLE_SIZE*self.zoom))

    def _overlay_text(self, it: Item):
        if not it._bbox_canvas: return
        x0,y0,x1,y1 = it._bbox_canvas
        c = self.canvas
        c.create_rectangle(x0,y0,x1,y1, outline=SELECT_COLOR, width=1)
        hs = self._handle_size()
        for (hx,hy,tag) in self._rect_handle_positions(x0,y0,x1,y1):
            c.create_rectangle(hx-hs/2, hy-hs/2, hx+hs/2, hy+hs/2, fill="white", outline=SELECT_COLOR, tags=("h_text",tag))
        cx = (x0+x1)/2; ry = y0 - max(18, int(ROTATE_HANDLE_OFFSET*self.zoom))
        c.create_line(cx, y0, cx, ry, fill=SELECT_COLOR, dash=(4,2))
        c.create_oval(cx-hs/2, ry-hs/2, cx+hs/2, ry+hs/2, fill="white", outline=SELECT_COLOR, tags=("h_text","rotate"))

    def _overlay_room(self, it: Item):
        (ax,ay),(bx,by) = it.data["a"], it.data["b"]
        x0,y0 = self.world_to_canvas(min(ax,bx), min(ay,by))
        x1,y1 = self.world_to_canvas(max(ax,bx), max(ay,by))
        c = self.canvas
        c.create_rectangle(x0,y0,x1,y1, outline=SELECT_COLOR, width=1)
        hs = self._handle_size()
        for (hx,hy,tag) in self._rect_handle_positions(x0,y0,x1,y1):
            c.create_rectangle(hx-hs/2, hy-hs/2, hx+hs/2, hy+hs/2, fill="white", outline=SELECT_COLOR, tags=("h_room",tag))

    def _overlay_segment(self, it: Item):
        (ax,ay),(bx,by) = it.data["a"], it.data["b"]
        x1,y1 = self.world_to_canvas(ax,ay); x2,y2 = self.world_to_canvas(bx,by)
        c = self.canvas
        c.create_line(x1,y1,x2,y2, fill=SELECT_COLOR, width=max(1,int(1*self.zoom)), dash=(4,2))
        hs = self._handle_size()
        for (hx,hy,tag) in [(x1,y1,"a"),(x2,y2,"b")]:
            c.create_rectangle(hx-hs/2, hy-hs/2, hx+hs/2, hy+hs/2, fill="white", outline=SELECT_COLOR, tags=("h_seg",tag))
        mx,my = (x1+x2)/2, (y1+y2)/2
        nx,ny = seg_normal(x1,y1,x2,y2)
        ryx, ryy = mx + nx*max(18,int(ROTATE_HANDLE_OFFSET*self.zoom)), my + ny*max(18,int(ROTATE_HANDLE_OFFSET*self.zoom))
        c.create_line(mx,my, ryx,ryy, fill=SELECT_COLOR, dash=(4,2))
        c.create_oval(ryx-hs/2, ryy-hs/2, ryx+hs/2, ryy+hs/2, fill="white", outline=SELECT_COLOR, tags=("h_seg","rotate"))

    def _overlay_group_selection(self):
        bbox = self._group_canvas_bbox()
        if not bbox: return
        x0,y0,x1,y1 = bbox
        self.canvas.create_rectangle(x0,y0,x1,y1, outline="#ff8e8e", dash=(6,3), width=1)

    def _rect_handle_positions(self, x0,y0,x1,y1):
        cx, cy = (x0+x1)/2, (y0+y1)/2
        return [
            (x0,y0,"nw"), (cx,y0,"n"), (x1,y0,"ne"),
            (x0,cy,"w"),               (x1,cy,"e"),
            (x0,y1,"sw"), (cx,y1,"s"), (x1,y1,"se"),
        ]

    # -------- measurement overlays --------
    def _draw_measurement_overlay(self, it):
        if not it.data.get("measure"):
            return
        g = self.grid_m.get()

        if it.kind in ("wall","door","window"):
            (ax,ay),(bx,by) = it.data["a"], it.data["b"]
            meters = math.hypot(bx-ax, by-ay) * g
            p1 = self.world_to_canvas(ax,ay); p2 = self.world_to_canvas(bx,by)
            mx, my = (p1[0]+p2[0])/2, (p1[1]+p2[1])/2
            nx,ny = seg_normal(*p1,*p2)
            off = MEASURE_OFFSET * self.zoom
            lx,ly = mx + nx*off, my + ny*off
            self.canvas.create_line(mx,my,lx,ly, fill="#9ec7ff", dash=(2,2))
            self._text_badge(lx, ly, self._format_length(meters))

        elif it.kind == "room":
            (ax,ay),(bx,by) = it.data["a"], it.data["b"]
            x0,y0 = min(ax,bx), min(ay,by); x1,y1 = max(ax,bx), max(ay,by)
            w_m = abs(x1-x0)*g
            h_m = abs(y1-y0)*g
            bc = self.world_to_canvas((x0+x1)/2, y1)
            rc = self.world_to_canvas(x1, (y0+y1)/2)
            self._text_badge(bc[0], bc[1] + (MEASURE_OFFSET*0.5)*self.zoom, self._format_length(w_m))
            self._text_badge(rc[0] + (MEASURE_OFFSET*0.5)*self.zoom, rc[1], self._format_length(h_m))
            if it.data.get("show_area", True):
                area = w_m * h_m
                cx, cy = self.world_to_canvas((x0+x1)/2, (y0+y1)/2)
                self._text_badge(cx, cy, f"{area:.2f} m²")

    def _text_badge(self, cx, cy, text):
        pad = 6 * self.zoom
        font = ("Segoe UI", max(9, int(10*self.zoom)))
        t_shadow = self.canvas.create_text(cx+1, cy+1, text=text, font=font, fill="#7a869a")
        t_id = self.canvas.create_text(cx, cy, text=text, font=font, fill="#0b1220")
        bbox = self.canvas.bbox(t_id)
        if not bbox: return
        x0,y0,x1,y1 = bbox
        x0 -= pad; y0 -= pad; x1 += pad; y1 += pad
        self.canvas.create_rectangle(x0,y0,x1,y1, fill="#e8f2ff", outline="#9ec7ff")
        self.canvas.tag_raise(t_id); self.canvas.tag_raise(t_shadow)

    # -------- rulers --------
    def _draw_rulers(self):
        for (a, b) in self.rulers:
            p1 = self.world_to_canvas(*a); p2 = self.world_to_canvas(*b)
            self.canvas.create_line(*p1, *p2, fill="#0d2d6c", dash=(6,3), width=max(2, int(2*self.zoom)))
            meters = math.hypot(b[0]-a[0], b[1]-a[1]) * self.grid_m.get()
            mx, my = (p1[0]+p2[0])/2, (p1[1]+p2[1])/2
            nx,ny = seg_normal(*p1,*p2)
            off = MEASURE_OFFSET * self.zoom
            lx,ly = mx + nx*off, my + ny*off
            self.canvas.create_line(mx,my,lx,ly, fill="#9ec7ff", dash=(2,2))
            self._text_badge(lx, ly, self._format_length(meters))

    def _clear_rulers(self):
        self.rulers.clear()
        self.draw_state.pop("ruler_start", None)
        self.temp_preview = None
        self._redraw()

    # -------- interactions ----------
    def _tool_changed(self):
        self.temp_preview = None; self.draw_state.clear()
        self._status("Tool: " + self.active_tool.get()); self._redraw()

    def _on_left_down(self, e):
        wx, wy = self.canvas_to_world(e.x, e.y)
        if self.snap_enabled.get(): wx, wy = self.snap_world(wx, wy)
        tool = self.active_tool.get()
        if self._pan["active"]: self._on_pan_start(e); return

        if tool == "select":
            handled = self._select_or_begin_transform(e.x, e.y, e.state, allow_marquee=True)
            if not handled:
                self.draw_state["marquee"] = {"start_px": (e.x, e.y), "cur_px": (e.x, e.y)}
        elif tool in ("wall","door","window"):
            st = self.draw_state
            if "start" not in st:
                st["start"] = (wx, wy); self.temp_preview = (tool, (wx, wy), (wx, wy))
            else:
                a = st["start"]; b = (wx, wy)
                if a != b: self.items.append(Item(tool, {"a": a, "b": b}))
                st.clear(); self.temp_preview = None; self._redraw()
        elif tool == "room":
            self.draw_state["start"] = (wx, wy)
            self.temp_preview = ("room", (wx, wy), (wx, wy))
        elif tool == "text":
            txt = simpledialog.askstring("Text Label", "Enter label text:", parent=self)
            if txt:
                self.items.append(Item("text", {"p": (wx, wy), "text": txt, "angle": 0.0, "size": 18, "color": TEXT_COLOR}))
                self._redraw()
        elif tool == "ruler":
            st = self.draw_state
            if "ruler_start" not in st:
                if not self.keep_rulers.get() and self.rulers:
                    self.rulers.clear(); self._redraw()
                st["ruler_start"] = (wx, wy)
                self.temp_preview = ("ruler", (wx, wy), (wx, wy))
            else:
                a = st["ruler_start"]; b = (wx, wy)
                if a != b:
                    if not self.keep_rulers.get():
                        self.rulers.clear()
                    self.rulers.append((a, b))
                st.pop("ruler_start", None); self.temp_preview = None; self._redraw()
        elif tool == "eraser":
            it = self._hit_test(e.x, e.y)
            if it:
                if self.selection is it: self.selection = None
                try: self.selected_items.remove(it)
                except ValueError: pass
                self.items.remove(it); self._redraw()

    def _on_left_drag(self, e):
        wx, wy = self.canvas_to_world(e.x, e.y)
        if self.snap_enabled.get(): wx, wy = self.snap_world(wx, wy)
        tool = self.active_tool.get()
        if self._pan["active"]: self._on_pan_drag(e); return

        if tool in ("wall","door","window","room"):
            if "start" in self.draw_state:
                self.temp_preview = (tool, self.draw_state["start"], (wx, wy)); self._redraw()
        elif tool == "select":
            if "marquee" in self.draw_state:
                self.draw_state["marquee"]["cur_px"] = (e.x, e.y); self._redraw()
            else:
                self._continue_transform(e.x, e.y, e.state)
        elif tool == "ruler":
            if "ruler_start" in self.draw_state:
                self.temp_preview = ("ruler", self.draw_state["ruler_start"], (wx, wy)); self._redraw()

    def _on_left_up(self, e):
        if self.active_tool.get() == "room" and "start" in self.draw_state:
            wx, wy = self.canvas_to_world(e.x, e.y)
            if self.snap_enabled.get(): wx, wy = self.snap_world(wx, wy)
            a = self.draw_state["start"]; b = (wx, wy)
            if a != b: self.items.append(Item("room", {"a": a, "b": b}))
            self.draw_state.clear(); self.temp_preview = None; self._redraw()
        elif self.active_tool.get() == "select":
            if "marquee" in self.draw_state:
                x0,y0 = self.draw_state["marquee"]["start_px"]; x1,y1 = self.draw_state["marquee"]["cur_px"]
                self._apply_marquee_selection(rect_norm(x0,y0,x1,y1))
                self.draw_state.pop("marquee", None); self._redraw()
            else:
                self.draw_state.pop("transform", None)

    # ---- Right-click context menu ----
    def _on_right_click(self, e):
        it = self._hit_test(e.x, e.y)
        menu = tk.Menu(self, tearoff=0)
        if it:
            self._clear_selection()
            it.selected = True; self.selection = it
            self.selected_items = [it]
            self._redraw()

            if it.kind in ("room","wall","door","window"):
                it.data.setdefault("measure", False)
                menu.add_command(
                    label=("Hide Measurements" if it.data["measure"] else "Show Measurements"),
                    command=lambda: self._toggle_measure(it)
                )
                if it.kind == "room":
                    it.data.setdefault("show_area", True)
                    menu.add_command(
                        label=("Hide Area" if it.data["show_area"] else "Show Area"),
                        command=lambda: self._toggle_area(it)
                    )
            menu.add_separator()
            menu.add_command(label="Delete", command=lambda: self._delete_item(it))
        else:
            menu.add_command(label="Clear Rulers", command=self._clear_rulers)

        try:
            menu.tk_popup(e.x_root, e.y_root)
        finally:
            menu.grab_release()

    def _toggle_measure(self, it):
        it.data["measure"] = not it.data.get("measure", False)
        self._redraw()

    def _toggle_area(self, it):
        it.data["show_area"] = not it.data.get("show_area", True)
        self._redraw()

    def _delete_item(self, it):
        if it in self.items:
            try: self.selected_items.remove(it)
            except ValueError: pass
            if self.selection is it: self.selection = None
            self.items.remove(it)
            self._redraw()

    # ---- Select + transform routing ----
    def _select_or_begin_transform(self, px, py, mod_state, allow_marquee=False):
        # Group move if clicking inside group bbox
        if len(self.selected_items) > 1:
            bbox = self._group_canvas_bbox()
            if bbox and point_in_rect(px, py, bbox):
                self._begin_move_group(px, py); return True

        # If a single selection exists, check its handles first
        if self.selection:
            if self.selection.kind == "text":
                h = self._hit_text_handle(self.selection, px, py)
                if h == "rotate": self._begin_text_rotate(self.selection, px, py); return True
                if h in ("nw","n","ne","w","e","sw","s","se"):
                    keep_ratio = bool(mod_state & 0x0001)  # Shift
                    self._begin_text_scale(self.selection, px, py, h, keep_ratio); return True
                if h == "inside": self._begin_move_selected(px, py); return True
            elif self.selection.kind == "room":
                h = self._hit_room_handle(self.selection, px, py)
                if h in ("nw","n","ne","w","e","sw","s","se"):
                    self._begin_room_resize(self.selection, px, py, h); return True
                if h == "inside": self._begin_move_selected(px, py); return True
            elif self.selection.kind in ("wall","door","window"):
                h = self._hit_segment_handle(self.selection, px, py)
                if h in ("a","b"): self._begin_segment_endpoint(self.selection, px, py, h); return True
                if h == "rotate": self._begin_segment_rotate(self.selection, px, py); return True
                if h == "onseg": self._begin_move_selected(px, py); return True

        # Otherwise pick item
        it = self._hit_test(px, py)
        if it:
            self._clear_selection()
            it.selected = True; self.selection = it
            self.selected_items = [it]
            # start move if clicked "inside/on" and not on a handle
            if it.kind == "text":
                if self._hit_text_handle(it, px, py) == "inside": self._begin_move_selected(px, py); return True
            elif it.kind == "room":
                if self._hit_room_handle(it, px, py) == "inside": self._begin_move_selected(px, py); return True
            elif it.kind in ("wall","door","window"):
                if self._hit_segment_handle(it, px, py) == "onseg": self._begin_move_selected(px, py); return True
            self._status(f"Selected {it.kind}"); self._redraw(); return True

        # nothing hit
        if allow_marquee:
            return False
        else:
            self._status("Nothing selected.")
            self._clear_selection(); self._redraw()
            return False

    def _apply_marquee_selection(self, rect_px):
        sels = []
        for it in self.items:
            if it.kind == "room":
                (ax,ay),(bx,by) = it.data["a"], it.data["b"]
                p0 = self.world_to_canvas(min(ax,bx), min(ay,by))
                p1 = self.world_to_canvas(max(ax,bx), max(ay,by))
                if rects_intersect(rect_px, (*p0,*p1)): sels.append(it)
            elif it.kind in ("wall","door","window"):
                p1 = self.world_to_canvas(*it.data["a"]); p2 = self.world_to_canvas(*it.data["b"])
                if seg_intersects_rect(p1, p2, rect_px): sels.append(it)
            elif it.kind == "text" and it._bbox_canvas:
                if rects_intersect(rect_px, it._bbox_canvas): sels.append(it)
        self._clear_selection()
        for it in sels: it.selected = True
        self.selected_items = sels
        self.selection = sels[0] if len(sels) == 1 else None
        self._status(f"Selected {len(sels)} item(s)." if sels else "Nothing selected.")

    def _begin_move_selected(self, px, py):
        wx, wy = self.canvas_to_world(px, py)
        if self.snap_enabled.get(): wx, wy = self.snap_world(wx, wy)
        self.draw_state["transform"] = {"mode":"move_any","start_world":(wx,wy),"item":self.selection}

    def _begin_move_group(self, px, py):
        wx, wy = self.canvas_to_world(px, py)
        if self.snap_enabled.get(): wx, wy = self.snap_world(wx, wy)
        self.draw_state["transform"] = {"mode":"move_group","start_world":(wx,wy)}

    def _continue_transform(self, px, py, mod_state):
        t = self.draw_state.get("transform")
        if not t: return
        mode = t["mode"]
        if mode == "move_any":
            it = t["item"]
            wx, wy = self.canvas_to_world(px, py)
            if self.snap_enabled.get(): wx, wy = self.snap_world(wx, wy)
            sx, sy = t["start_world"]; dx, dy = wx - sx, wy - sy
            t["start_world"] = (wx, wy)
            self._move_item(it, dx, dy); self._redraw()
        elif mode == "move_group":
            wx, wy = self.canvas_to_world(px, py)
            if self.snap_enabled.get(): wx, wy = self.snap_world(wx, wy)
            sx, sy = t["start_world"]; dx, dy = wx - sx, wy - sy
            t["start_world"] = (wx, wy)
            for it in self.selected_items:
                self._move_item(it, dx, dy)
            self._redraw()
        elif mode == "scale_text":
            self._update_text_scale(px, py)
        elif mode == "rotate_text":
            self._update_text_rotate(px, py)
        elif mode == "room_resize":
            self._update_room_resize(px, py)
        elif mode == "seg_endpoint":
            self._update_segment_endpoint(px, py)
        elif mode == "seg_rotate":
            self._update_segment_rotate(px, py)

    # ---- Move generic ----
    def _move_item(self, it: Item, dx, dy):
        if it.kind in ("wall","door","window"):
            ax, ay = it.data["a"]; bx, by = it.data["b"]
            it.data["a"] = (ax+dx, ay+dy); it.data["b"] = (bx+dx, by+dy)
        elif it.kind == "room":
            ax, ay = it.data["a"]; bx, by = it.data["b"]
            it.data["a"] = (ax+dx, ay+dy); it.data["b"] = (bx+dx, by+dy)
        elif it.kind == "text":
            px, py = it.data["p"]; it.data["p"] = (px+dx, py+dy)

    def delete_selection(self):
        if self.selected_items:
            for it in list(self.selected_items):
                if it in self.items: self.items.remove(it)
            self.selected_items.clear()
            self.selection = None
            self._redraw(); self._status("Deleted selection.")
        elif self.selection:
            if self.selection in self.items:
                self.items.remove(self.selection)
            self.selection = None
            self._redraw(); self._status("Deleted selection.")

    # ---- Hit-testing for selection ----
    def _hit_test(self, px, py) -> Optional[Item]:
        best, bestd = None, 1e9
        for it in self.items:
            d = 1e9
            if it.kind in ("wall","door","window"):
                x1,y1 = self.world_to_canvas(*it.data["a"]); x2,y2 = self.world_to_canvas(*it.data["b"])
                d = dist_point_to_segment(px, py, x1, y1, x2, y2)
                if d <= HIT_TOL and d < bestd: best, bestd = it, d
            elif it.kind == "room":
                (ax,ay),(bx,by) = it.data["a"], it.data["b"]
                x0,y0 = self.world_to_canvas(min(ax,bx), min(ay,by))
                x1,y1 = self.world_to_canvas(max(ax,bx), max(ay,by))
                if x0 - HIT_TOL <= px <= x1 + HIT_TOL and y0 - HIT_TOL <= py <= y1 + HIT_TOL:
                    d = min(abs(px-x0), abs(px-x1), abs(py-y0), abs(py-y1))
                    if d < bestd: best, bestd = it, d
            elif it.kind == "text":
                if it._bbox_canvas:
                    x0,y0,x1,y1 = it._bbox_canvas
                    if x0 <= px <= x1 and y0 <= py <= y1:
                        return it
        return best

    def _clear_selection(self):
        for obj in self.items: obj.selected = False
        self.selection = None
        self.selected_items.clear()

    # ---- Text transforms ----
    def _hit_text_handle(self, it: Item, px, py) -> Optional[str]:
        if not it._bbox_canvas: return None
        x0,y0,x1,y1 = it._bbox_canvas
        cx = (x0+x1)/2; ry = y0 - max(18, int(ROTATE_HANDLE_OFFSET*self.zoom))
        hs = self._handle_size()
        if (cx-hs/2) <= px <= (cx+hs/2) and (ry-hs/2) <= py <= (ry+hs/2): return "rotate"
        for (hx,hy,tag) in self._rect_handle_positions(x0,y0,x1,y1):
            if (hx-hs/2) <= px <= (hx+hs/2) and (hy-hs/2) <= py <= (hy+hs/2): return tag
        if x0 <= px <= x1 and y0 <= py <= y1: return "inside"
        return None

    def _begin_text_scale(self, it: Item, px, py, handle_tag: str, keep_ratio: bool):
        x0,y0,x1,y1 = it._bbox_canvas
        self.draw_state["transform"] = {"mode":"scale_text","item":it,"handle":handle_tag,
                                        "keep_ratio":keep_ratio,"start_bbox":(x0,y0,x1,y1),
                                        "start_size":it.data["size"]}

    def _update_text_scale(self, px, py):
        t = self.draw_state["transform"]; it = t["item"]
        x0,y0,x1,y1 = t["start_bbox"]; cx, cy = (x0+x1)/2, (y0+y1)/2
        dx, dy = abs(px-cx)/max(1,(x1-cx)), abs(py-cy)/max(1,(y1-cy))
        handle = t["handle"]
        if handle in ("n","s"): scale = dy
        elif handle in ("e","w"): scale = dx
        else: scale = max(dx,dy) if t["keep_ratio"] else (dx+dy)/2
        scale = clamp(scale, 0.2, 8.0)
        new_size = clamp(int(t["start_size"]*scale), 8, 512)
        if new_size != it.data["size"]:
            it.data["size"] = new_size; it._last_render_key = None; self._redraw()

    def _begin_text_rotate(self, it: Item, px, py):
        cx, cy = self.world_to_canvas(*it.data["p"])
        ang0 = screen_angle(cx, cy, px, py)
        self.draw_state["transform"] = {"mode":"rotate_text","item":it,"center":(cx,cy),
                                        "start_cursor":ang0,"start_angle":float(it.data["angle"])}

    def _update_text_rotate(self, px, py):
        t = self.draw_state["transform"]; it = t["item"]
        cx, cy = t["center"]
        ang = screen_angle(cx, cy, px, py)
        it.data["angle"] = (t["start_angle"] + (ang - t["start_cursor"])) % 360.0
        it._last_render_key = None; self._redraw()

    # ---- Room transforms (axis-aligned) ----
    def _hit_room_handle(self, it: Item, px, py) -> Optional[str]:
        (ax,ay),(bx,by) = it.data["a"], it.data["b"]
        x0,y0 = self.world_to_canvas(min(ax,bx), min(ay,by))
        x1,y1 = self.world_to_canvas(max(ax,bx), max(ay,by))
        hs = self._handle_size()
        for (hx,hy,tag) in self._rect_handle_positions(x0,y0,x1,y1):
            if (hx-hs/2)<=px<=(hx+hs/2) and (hy-hs/2)<=py<=(hy+hs/2): return tag
        if x0 <= px <= x1 and y0 <= py <= y1: return "inside"
        return None

    def _begin_room_resize(self, it: Item, px, py, handle_tag: str):
        self.draw_state["transform"] = {"mode":"room_resize","item":it,"handle":handle_tag}

    def _update_room_resize(self, px, py):
        t = self.draw_state["transform"]; it = t["item"]
        (ax,ay),(bx,by) = it.data["a"], it.data["b"]
        x0,y0 = min(ax,bx), min(ay,by); x1,y1 = max(ax,bx), max(ay,by)
        wx, wy = self.canvas_to_world(px, py)
        if self.snap_enabled.get(): wx, wy = self.snap_world(wx, wy)
        tag = t["handle"]
        if tag in ("w","nw","sw"): x0 = min(wx, x1-0.01)
        if tag in ("e","ne","se"): x1 = max(wx, x0+0.01)
        if tag in ("n","nw","ne"): y0 = min(wy, y1-0.01)
        if tag in ("s","sw","se"): y1 = max(wy, y0+0.01)
        it.data["a"] = (x0,y0); it.data["b"] = (x1,y1); self._redraw()

    # ---- Segment transforms ----
    def _hit_segment_handle(self, it: Item, px, py) -> Optional[str]:
        (ax,ay),(bx,by) = it.data["a"], it.data["b"]
        x1,y1 = self.world_to_canvas(ax,ay); x2,y2 = self.world_to_canvas(bx,by)
        hs = self._handle_size()
        if (x1-hs/2)<=px<=(x1+hs/2) and (y1-hs/2)<=py<=(y1+hs/2): return "a"
        if (x2-hs/2)<=px<=(x2+hs/2) and (y2-hs/2)<=py<=(y2+hs/2): return "b"
        mx,my = (x1+x2)/2, (y1+y2)/2
        nx,ny = seg_normal(x1,y1,x2,y2)
        rx,ry = mx + nx*max(18,int(ROTATE_HANDLE_OFFSET*self.zoom)), my + ny*max(18,int(ROTATE_HANDLE_OFFSET*self.zoom))
        if (rx-hs/2)<=px<=(rx+hs/2) and (ry-hs/2)<=py<=(ry+hs/2): return "rotate"
        if dist_point_to_segment(px, py, x1,y1,x2,y2) <= HIT_TOL: return "onseg"
        return None

    def _begin_segment_endpoint(self, it: Item, px, py, which: str):
        self.draw_state["transform"] = {"mode":"seg_endpoint","item":it,"which":which}

    def _update_segment_endpoint(self, px, py):
        t = self.draw_state["transform"]; it = t["item"]; which = t["which"]
        wx, wy = self.canvas_to_world(px, py)
        if self.snap_enabled.get(): wx, wy = self.snap_world(wx, wy)
        if which == "a": it.data["a"] = (wx, wy)
        else: it.data["b"] = (wx, wy)
        self._redraw()

    def _begin_segment_rotate(self, it: Item, px, py):
        (ax,ay),(bx,by) = it.data["a"], it.data["b"]
        cx, cy = (ax+bx)/2, (ay+by)/2
        self.draw_state["transform"] = {"mode":"seg_rotate","item":it,"center":(cx,cy),"len":math.hypot(bx-ax, by-ay),
                                        "start_cursor":screen_angle(*self.world_to_canvas(cx,cy), px, py)}

    def _update_segment_rotate(self, px, py):
        t = self.draw_state["transform"]; it = t["item"]
        cx, cy = t["center"]; L = max(1e-6, t["len"])
        ang = screen_angle(*self.world_to_canvas(cx,cy), px, py)
        d_ang = ang - t["start_cursor"]
        theta = math.radians(d_ang)
        dx, dy = (L/2)*math.cos(theta), (L/2)*math.sin(theta)
        it.data["a"] = (cx - dx, cy - dy); it.data["b"] = (cx + dx, cy + dy)
        if self.snap_enabled.get():
            it.data["a"] = self.snap_world(*it.data["a"])
            it.data["b"] = self.snap_world(*it.data["b"])
        self._redraw()

    # -------- pan/zoom/status ----------
    def _set_pan(self, on): self._pan["space"] = on
    def _on_pan_start(self, e): self._pan.update({"active": True, "start": (e.x, e.y)})
    def _on_pan_drag(self, e):
        if not self._pan["active"]:
            if self._pan.get("space"): self._on_pan_start(e)
            return
        sx, sy = self._pan["start"]; dx, dy = e.x - sx, e.y - sy
        self._pan["start"] = (e.x, e.y)
        self.origin[0] += dx; self.origin[1] += dy
        self._redraw()
    def _on_pan_end(self, e): self._pan["active"] = False

    def _zoom(self, factor):
        new_zoom = clamp(self.zoom * factor, MIN_ZOOM, MAX_ZOOM)
        if new_zoom == self.zoom: return
        c = self.canvas; cx, cy = c.winfo_width()/2, c.winfo_height()/2
        wx, wy = self.canvas_to_world(cx, cy)
        self.zoom = new_zoom
        cx2, cy2 = self.world_to_canvas(wx, wy)
        self.origin[0] += (cx - cx2); self.origin[1] += (cy - cy2)
        self._redraw()

    def _reset_view(self):
        self.zoom = 1.0; self.origin = [80,80]; self._redraw()

    def _on_motion(self, e):
        wx, wy = self.canvas_to_world(e.x, e.y)
        swx, swy = self.snap_world(wx, wy) if self.snap_enabled.get() else (wx, wy)
        self.status.set(f"World: ({swx:.2f}, {swy:.2f}) — Scale: {self.grid_m.get():.3f} m/cell — Zoom: {self.zoom:.2f}x")

    def _status(self, msg): self.status.set(msg)

    # -------- file ops ----------
    def new_file(self):
        if messagebox.askyesno("New", "Discard current plan and start a new one?"):
            self.items.clear(); self.selection=None; self.selected_items.clear(); self.rulers.clear()
            self.draw_state.clear(); self.temp_preview=None
            self._redraw(); self._status("New project.")

    def save_json(self):
        path = filedialog.asksaveasfilename(title="Save FloorPlan360 JSON", defaultextension=".json", filetypes=[("JSON","*.json")])
        if not path: return
        doc = {"meta": {"meters_per_grid": self.grid_m.get()},
               "items": [it.to_json() for it in self.items],
               "rulers": self.rulers}
        with open(path, "w", encoding="utf-8") as f: json.dump(doc, f, indent=2)
        self._status(f"Saved: {path}")

    def load_json(self):
        path = filedialog.askopenfilename(title="Load FloorPlan360 JSON", filetypes=[("JSON","*.json")])
        if not path: return
        try:
            with open(path, "r", encoding="utf-8") as f: doc = json.load(f)
        except Exception as ex:
            messagebox.showerror("Error", f"Couldn't read file:\n{ex}"); return
        self.items = [Item.from_json(obj) for obj in doc.get("items",[])]
        self.grid_m.set(doc.get("meta",{}).get("meters_per_grid", GRID_METERS))
        self.rulers = doc.get("rulers", [])
        for it in self.items:
            if it.kind == "text":
                it.data.setdefault("angle", 0.0)
                it.data.setdefault("size", 18)
                it.data.setdefault("color", TEXT_COLOR)
        self._clear_selection()
        self._redraw(); self._status(f"Loaded: {path}")

    # ---- PNG Export (Windows-friendly via ImageGrab) ----
    def export_png(self):
        path = filedialog.asksaveasfilename(
            title="Export PNG",
            defaultextension=".png",
            filetypes=[("PNG", "*.png")]
        )
        if not path:
            return

        # Hide overlays for a clean export
        prev_sel = self.selection
        prev_multi = list(self.selected_items)
        prev_preview = self.temp_preview
        prev_marquee = self.draw_state.get("marquee")

        self._clear_selection()
        self.temp_preview = None
        if "marquee" in self.draw_state:
            self.draw_state.pop("marquee")

        # Ensure canvas is fully drawn, then bring window to front (helps ImageGrab on Windows)
        self.update_idletasks()
        try:
            self.attributes("-topmost", True)
            self.update()
            self.after(50, lambda: None)
        except Exception:
            pass

        # Canvas bounding box in screen coords
        x0 = self.canvas.winfo_rootx()
        y0 = self.canvas.winfo_rooty()
        x1 = x0 + self.canvas.winfo_width()
        y1 = y0 + self.canvas.winfo_height()

        # DPI-aware bounding box on Windows (GetDpiForWindow)
        scale = 1.0
        if sys.platform.startswith("win"):
            try:
                import ctypes
                hwnd = self.winfo_id()
                GetDpiForWindow = ctypes.windll.user32.GetDpiForWindow
                GetDpiForWindow.restype = ctypes.c_uint
                dpi = GetDpiForWindow(hwnd)
                scale = dpi / 96.0 if dpi else 1.0
            except Exception:
                try:
                    scale = float(self.winfo_fpixels("1i")) / 72.0
                except Exception:
                    scale = 1.0

        bx0 = int(round(x0 * scale))
        by0 = int(round(y0 * scale))
        bx1 = int(round(x1 * scale))
        by1 = int(round(y1 * scale))

        # Grab and save
        try:
            img = ImageGrab.grab(bbox=(bx0, by0, bx1, by1), all_screens=True)
            img.save(path, "PNG")
            self._status(f"Exported PNG: {path}")
        except Exception as ex:
            messagebox.showerror("Export PNG", f"Failed to export:\n{ex}")

        # Restore overlays/selection
        for it in self.items: it.selected = False
        self.selected_items = prev_multi
        for it in self.selected_items: it.selected = True
        self.selection = prev_sel
        self.temp_preview = prev_preview
        if prev_marquee:
            self.draw_state["marquee"] = prev_marquee
        self._redraw()

    # -------- unit formatting ----------
    def _format_length(self, meters: float) -> str:
        u = self.unit.get()
        if u == "m":
            return f"{meters:.2f} m"
        if u == "cm":
            return f"{meters*100:.1f} cm"
        if u == "mm":
            return f"{meters*1000:.0f} mm"
        if u == "ft-in":
            inches = meters * 39.37007874
            ft = int(inches // 12)
            inch = inches - 12 * ft
            return f"{ft}′ {inch:.1f}″"
        return f"{meters:.2f} m"

    # -------- helpers for group bbox ----------
    def _item_canvas_bbox(self, it: Item):
        if it.kind == "room":
            (ax,ay),(bx,by) = it.data["a"], it.data["b"]
            p0 = self.world_to_canvas(min(ax,bx), min(ay,by))
            p1 = self.world_to_canvas(max(ax,bx), max(ay,by))
            return (*p0,*p1)
        if it.kind in ("wall","door","window"):
            p1 = self.world_to_canvas(*it.data["a"]); p2 = self.world_to_canvas(*it.data["b"])
            x0,y0,x1,y1 = rect_norm(p1[0],p1[1],p2[0],p2[1])
            pad = 4
            return (x0-pad,y0-pad,x1+pad,y1+pad)
        if it.kind == "text" and it._bbox_canvas:
            return it._bbox_canvas
        return None

    def _group_canvas_bbox(self):
        boxes = [self._item_canvas_bbox(it) for it in self.selected_items if self._item_canvas_bbox(it)]
        if not boxes: return None
        x0 = min(b[0] for b in boxes); y0 = min(b[1] for b in boxes)
        x1 = max(b[2] for b in boxes); y1 = max(b[3] for b in boxes)
        return (x0,y0,x1,y1)

def rects_intersect(a, b):
    ax0,ay0,ax1,ay1 = rect_norm(*a); bx0,by0,bx1,by1 = rect_norm(*b)
    return not (ax1 < bx0 or bx1 < ax0 or ay1 < by0 or by1 < ay0)

if __name__ == "__main__":
    FloorPlanApp().mainloop()
