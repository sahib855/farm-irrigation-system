import tkinter as tk
from tkinter import messagebox, ttk
import time
# Try to import PIL, but make the application robust if it fails
try:
    from PIL import Image, ImageTk 
    PIL_AVAILABLE = True
except ImportError:
    PIL_AVAILABLE = False
    print("WARNING: Pillow (PIL) not installed. Using default shapes for nodes.")
    
import heapq 
from pathlib import Path 

# --- Part 1: DAA Algorithms (Kruskal's MST & Dijkstra's) ---

# Kruskal's Helper: Disjoint Set (Union-Find)
class DisjointSet:
    def __init__(self, size):
        self.parent = list(range(size))
        self.rank = [0] * size

    def find(self, i):
        if self.parent[i] == i:
            return i
        self.parent[i] = self.find(self.parent[i])
        return self.parent[i]

    def union(self, i, j):
        root_i = self.find(i)
        root_j = self.find(j)
        if root_i != root_j:
            if self.rank[root_i] < self.rank[root_j]:
                self.parent[root_i] = root_j
            elif self.rank[root_i] > self.rank[root_j]:
                self.parent[root_j] = root_i
            else:
                self.parent[root_j] = root_i
                self.rank[root_i] += 1
            return True
        return False

# Kruskal's now yields steps for visualization
def kruskal_mst_steps(nodes, edges):
    sorted_edges = sorted(edges, key=lambda item: item[0])
    ds = DisjointSet(len(nodes))
    
    for weight, u, v in sorted_edges:
        yield 'CHECK', weight, u, v
        
        if ds.union(u, v):
            yield 'ACCEPT', weight, u, v
        else:
            yield 'REJECT', weight, u, v


def dijkstra_shortest_path_with_steps(nodes, edges, start_node):
    adj = {i: [] for i in range(len(nodes))}
    for cost, u, v in edges:
        adj[u].append((cost, v))
        adj[v].append((cost, u))

    distances = {i: float('inf') for i in range(len(nodes))}
    distances[start_node] = 0
    previous_nodes = {i: None for i in range(len(nodes))}
    priority_queue = [(0, start_node)] 
    
    steps = []

    while priority_queue:
        current_distance, current_node = heapq.heappop(priority_queue)

        if current_distance > distances[current_node]:
            continue

        steps.append(('FINALIZED', current_node))
        
        for weight, neighbor in adj[current_node]:
            distance = current_distance + weight
            if distance < distances[neighbor]:
                distances[neighbor] = distance
                previous_nodes[neighbor] = current_node
                heapq.heappush(priority_queue, (distance, neighbor))
                steps.append(('RELAXED', current_node, neighbor, distance)) 
            else:
                steps.append(('COMPARE_WORSE', current_node, neighbor, distance))

    return distances, previous_nodes, steps

def reconstruct_path(previous_nodes, start_node, end_node):
    path = []
    current_node = end_node
    while current_node is not None:
        path.insert(0, current_node)
        if current_node == start_node:
            break
        current_node = previous_nodes[current_node]
    
    if path and path[0] == start_node:
        path_edges = [(path[i], path[i+1]) for i in range(len(path) - 1)]
        return path_edges
    return []


# --- Part 2: Farm Data Setup ---

# COLOR THEME CONSTANTS (Modern Light-Base Farm Theme)
COLOR_BG_LIGHT = '#F0FFF0'         # Honeydew White (Main Background)
COLOR_FRAME_WHITE = '#FFFFFF'      # Pure White (Containers)
COLOR_PRIMARY_TEXT = '#2F4F4F'     # Dark Slate Gray (High contrast text)
COLOR_BUTTON_ACTION = '#4CAF50'    # Vibrant Lawn Green (Action)
COLOR_MST_PIPE = '#4CAF50'         # Vibrant Lawn Green (Success/MST)
COLOR_SHORTEST_PATH = '#FFA07A'    # Light Salmon/Coral (Path highlight)
COLOR_REPORT_HIGHLIGHT = '#FFC107' # Deep Amber Gold (Cost Highlight)
COLOR_DIJKSTRA_RELAX = '#FF6347'   # Tomato Red (for relaxation step check)
COLOR_FLOW = '#6B8E23'             # Olive Drab (for water flow)
COLOR_WATER_SOURCE = '#4682B4'     # Steel Blue (Distinct Water Source)
COLOR_DANGER = '#DC143C'           # Crimson Red (Exit/Reject)
COLOR_PIPE_DEFAULT = '#A9A9A9'     # Dark Gray (Default Pipe)


# Dimensions and Scaling (Unchanged)
ORIG_CANVAS_WIDTH = 800
ORIG_CANVAS_HEIGHT = 500
CANVAS_WIDTH = 1200 
CANVAS_HEIGHT = 650 
SCALE_X = CANVAS_WIDTH / ORIG_CANVAS_WIDTH
SCALE_Y = CANVAS_HEIGHT / ORIG_CANVAS_HEIGHT

FARM_NODES = [
    (int(100 * SCALE_X), int(100 * SCALE_Y), "Water Source", "source"), # 0
    (int(400 * SCALE_X), int(50 * SCALE_Y), "Field A", "field"),      # 1
    (int(700 * SCALE_X), int(200 * SCALE_Y), "Field B", "field"),     # 2
    (int(200 * SCALE_X), int(400 * SCALE_Y), "Field C", "field"),     # 3
    (int(600 * SCALE_X), int(450 * SCALE_Y), "Field D", "field")      # 4
]

DEFAULT_FARM_EDGES = [
    (10, 0, 1), (15, 0, 3), (5, 1, 2), 
    (25, 1, 3), (20, 2, 4), (12, 3, 4), (30, 0, 4)      
]

PIPE_LINE_MAP = {} 
NODE_TEXT_MAP = {} 
NODE_CANVAS_IDS = {} 

# --- Part 3: Main Application Class (Manages Pages) ---

# Define a placeholder for the image path (User must set this path)
IMAGE_BASE_PATH = Path("D:/DAA project/assets") 

class SmartIrrigationApp(tk.Tk):
    def __init__(self, nodes, default_edges):
        super().__init__()
        self.title("Smart Irrigation Network: Design & Optimization")
        self.attributes('-fullscreen', True) 
        self.protocol("WM_DELETE_WINDOW", self.exit_fullscreen) 
        self.bind("<Escape>", self.exit_fullscreen)
        self.nodes = nodes
        self.current_edges = default_edges
        self.container = tk.Frame(self, bg=COLOR_BG_LIGHT) # Light Theme
        self.container.pack(fill="both", expand=True)
        self.frames = {}
        
        self.frames["SetupPage"] = SetupPage(self.container, self, self.nodes, DEFAULT_FARM_EDGES)
        self.frames["SetupPage"].grid(row=0, column=0, sticky="nsew")

        self.simulator_page = None 
        self.report_page = None
        
        self.last_target_node = None
        self.last_route_distance = None
        
        self.container.grid_rowconfigure(0, weight=1)
        self.container.grid_columnconfigure(0, weight=1)
        
        self.show_frame("SetupPage")

    def show_frame(self, page_name):
        frame = self.frames[page_name]
        frame.tkraise()

    def start_simulation(self, new_edges):
        self.current_edges = new_edges
        
        if self.simulator_page is None:
            self.simulator_page = IrrigationSimulator(self.container, self, self.nodes, self.current_edges)
            self.frames["SimulatorPage"] = self.simulator_page
            self.simulator_page.grid(row=0, column=0, sticky="nsew")
        else:
            self.simulator_page.edges = self.current_edges
            self.simulator_page.reset_pipes(show_all=False) 
            self.simulator_page.draw_farm_layout() 
            self.simulator_page.result_label.config(text="Ready to run optimization algorithms.")
            self.simulator_page.mst_cost_label.config(text="Total Value: --")
            self.simulator_page.path_cost_label.config(text="Route Value: --")
            
        self.last_target_node = None
        self.last_route_distance = None

        self.show_frame("SimulatorPage")

    def show_single_report(self, target_node, distance):
        self.last_target_node = target_node
        self.last_route_distance = distance
        
        if self.report_page is None:
            self.report_page = SingleFieldReportPage(self.container, self, self.nodes)
            self.frames["SingleFieldReportPage"] = self.report_page
            self.report_page.grid(row=0, column=0, sticky="nsew")
            
        self.report_page.update_report(target_node, distance)
        self.show_frame("SingleFieldReportPage")
        

    def exit_fullscreen(self, event=None):
        if "SetupPage" in self.frames and hasattr(self.frames["SetupPage"], 'after_id'):
             self.frames["SetupPage"].after_cancel(self.frames["SetupPage"].after_id)
        if self.simulator_page:
            self.simulator_page.stop_all_animations()
            
        self.attributes("-fullscreen", False)
        self.quit()

# ----------------------------------------------------------------------
# --- Page 1: Setup Page (User Input) - Modern Light Theme ---
# ----------------------------------------------------------------------

class SetupPage(tk.Frame):
    def __init__(self, parent, controller, nodes, default_edges):
        tk.Frame.__init__(self, parent, bg=COLOR_BG_LIGHT) # Light Theme
        self.controller = controller
        self.nodes = nodes
        self.default_edges = default_edges
        self.edge_vars = []
        
        main_frame = tk.Frame(self, bg=COLOR_FRAME_WHITE, padx=50, pady=50, relief='raised', bd=4) # Light Theme
        main_frame.place(relx=0.5, rely=0.5, anchor=tk.CENTER)

        self.welcome_label = tk.Label(main_frame, 
                                     text="Welcome to the Smart Irrigation Optimizer! 🗺️", 
                                     font=('Arial', 28, 'bold'), 
                                     bg=COLOR_FRAME_WHITE, fg=COLOR_PRIMARY_TEXT) # Light Theme
        self.welcome_label.pack(pady=(0, 20))
        self.after_id = None 
        self.animate_welcome_title(0)
        
        tk.Label(main_frame, 
                 text="First, define your network costs. Enter the distance/cost (in meters) for each pipe segment:", 
                 font=('Arial', 14), 
                 bg=COLOR_FRAME_WHITE, fg=COLOR_PRIMARY_TEXT).pack(pady=(0, 20)) # Light Theme

        input_frame = tk.Frame(main_frame, bg=COLOR_BG_LIGHT, padx=10, pady=10) # Light Theme
        input_frame.pack()
        
        for i, (cost, u, v) in enumerate(default_edges):
            u_name = self.nodes[u][2]
            v_name = self.nodes[v][2]
            
            row_label = f"Pipe from {u_name} to {v_name}:"
            
            tk.Label(input_frame, text=row_label, 
                     font=('Arial', 12), bg=COLOR_BG_LIGHT, fg=COLOR_PRIMARY_TEXT, anchor='w').grid(row=i, column=0, padx=5, pady=5, sticky='w') # Light Theme
            
            var = tk.StringVar(value=str(int(cost))) 
            entry = tk.Entry(input_frame, textvariable=var, width=10, font=('Arial', 12), fg=COLOR_PRIMARY_TEXT)
            entry.grid(row=i, column=1, padx=5, pady=5)
            
            tk.Label(input_frame, text="meters", 
                     font=('Arial', 12), bg=COLOR_BG_LIGHT, fg=COLOR_PRIMARY_TEXT, anchor='w').grid(row=i, column=2, padx=5, pady=5, sticky='w') # Light Theme
            
            self.edge_vars.append(((u, v), var))

        tk.Button(main_frame, 
                  text="▶️ Go to Simulator", 
                  command=self.submit_data, 
                  bg=COLOR_BUTTON_ACTION, fg=COLOR_FRAME_WHITE, # Light Theme
                  font=('Arial', 14, 'bold'), 
                  relief='raised', bd=4).pack(pady=20, ipadx=20, ipady=10)

    def animate_welcome_title(self, step):
        # Use high-contrast colors for animation
        colors = [COLOR_PRIMARY_TEXT, COLOR_MST_PIPE, COLOR_REPORT_HIGHLIGHT] 
        color = colors[step % len(colors)]
        self.welcome_label.config(fg=color)
        self.after_id = self.after(500, self.animate_welcome_title, step + 1)


    def submit_data(self):
        if self.after_id:
            self.after_cancel(self.after_id) 

        new_edges = []
        try:
            for (u, v), var in self.edge_vars:
                cost = float(var.get())
                if cost < 0:
                    raise ValueError("Cost must be non-negative.")
                new_edges.append((cost, u, v))
                
            self.controller.start_simulation(new_edges)
            
        except ValueError as e:
            messagebox.showerror("Input Error", f"Invalid cost entered. Please ensure all values are positive numbers.\nError: {e}")
            
# ----------------------------------------------------------------------
# --- Page 2: Simulator Page - Modern Light Theme ---
# ----------------------------------------------------------------------

class IrrigationSimulator(tk.Frame):
    
    # Color and Constant Definitions (Updated to Light Theme)
    MST_COLOR = COLOR_MST_PIPE        
    SHORTEST_PATH_COLOR = COLOR_SHORTEST_PATH 
    RELAX_COLOR = COLOR_DIJKSTRA_RELAX      
    FLOW_COLOR = COLOR_FLOW       
    
    SOURCE_IMAGE = "water_source.png"
    FIELD_IMAGE = "field_icon.png"
    BG_IMAGE = "farm_background.png"
    
    def __init__(self, parent, controller, nodes, edges):
        tk.Frame.__init__(self, parent, bg=COLOR_BG_LIGHT) # Light Theme
        self.controller = controller
        self.nodes = nodes
        self.edges = edges 
        self.start_node = 0
        self.bg_photo = None 
        self.node_images = {} 
        self.active_animations = [] 
        
        self.load_images() 
        
        # --- Canvas setup ---
        canvas_frame = tk.Frame(self, bg=self.cget('bg'))
        canvas_frame.pack(expand=True, fill=tk.BOTH, pady=5) 
        
        # Canvas background should contrast with the main frame background
        self.canvas = tk.Canvas(canvas_frame, width=CANVAS_WIDTH, height=CANVAS_HEIGHT, bg='#EBEBEB', relief='flat', bd=0) 
        self.canvas.pack(pady=(10, 5), padx=20)
        
        self.draw_farm_layout() 
        
        # --- Control Panel setup ---
        control_frame = tk.Frame(self, bg=COLOR_FRAME_WHITE, bd=5, relief='raised') # Light Theme
        control_frame.pack(pady=0, fill=tk.X, padx=0) 
        
        action_frame = tk.Frame(control_frame, bg=COLOR_FRAME_WHITE) # Light Theme
        action_frame.pack(side=tk.TOP, padx=10, pady=(10, 5), fill=tk.X)
        
        tk.Button(action_frame, 
                  text="⏪ Back to Setup", 
                  command=lambda: controller.show_frame("SetupPage"), 
                  bg=COLOR_PRIMARY_TEXT, fg=COLOR_FRAME_WHITE, # Light Theme
                  font=('Arial', 12, 'bold'), 
                  relief='groove', bd=3).pack(side=tk.LEFT, padx=5)

        tk.Button(action_frame, 
                  text="❌ Exit App", 
                  command=self.controller.exit_fullscreen, 
                  bg=COLOR_DANGER, fg=COLOR_FRAME_WHITE, # Light Theme
                  font=('Arial', 12, 'bold'), 
                  relief='groove', bd=3).pack(side=tk.RIGHT, padx=5)

        self.result_label = tk.Label(action_frame, text="Ready to run optimization algorithms.", 
                                     font=('Arial', 12, 'bold'), bg=COLOR_FRAME_WHITE, fg=COLOR_PRIMARY_TEXT) # Light Theme
        self.result_label.pack(side=tk.LEFT, padx=10, expand=True) 

        tk.Frame(control_frame, height=2, bg=COLOR_PIPE_DEFAULT).pack(fill=tk.X, padx=10, pady=5) # Light Theme (Divider)
        
        mst_frame = tk.Frame(control_frame, bg=COLOR_FRAME_WHITE) # Light Theme
        mst_frame.pack(side=tk.TOP, padx=10, pady=5, fill=tk.X) 
        
        tk.Button(mst_frame, 
                  text="▶️ RUN: Optimal Piping Design (Kruskal's MST)", 
                  command=self.run_and_animate_mst, 
                  bg=self.MST_COLOR, fg=COLOR_FRAME_WHITE, # Light Theme
                  font=('Arial', 13, 'bold'), 
                  relief='groove', bd=3).pack(side=tk.LEFT, padx=5, expand=True, ipady=5) 
        
        self.mst_cost_label = tk.Label(mst_frame, text="Total Value: --", 
                                       font=('Arial', 12, 'bold'), bg=COLOR_FRAME_WHITE, fg=self.MST_COLOR, width=15) # Light Theme
        self.mst_cost_label.pack(side=tk.RIGHT, padx=5)

        tk.Frame(control_frame, height=2, bg=COLOR_PIPE_DEFAULT).pack(fill=tk.X, padx=10, pady=5) # Light Theme (Divider)

        # Dijkstra's Section
        shortest_path_frame = tk.Frame(control_frame, bg=COLOR_FRAME_WHITE) # Light Theme
        shortest_path_frame.pack(side=tk.TOP, padx=10, pady=(5, 5), fill=tk.X) 

        tk.Label(shortest_path_frame, text="Target Field:", bg=COLOR_FRAME_WHITE, fg=COLOR_PRIMARY_TEXT, font=('Arial', 12)).pack(side=tk.LEFT, padx=5) # Light Theme
        
        field_names = [f[2] for f in nodes[1:]] 
        self.target_field_var = tk.StringVar(self)
        if field_names:
            self.target_field_var.set(field_names[0]) 
        
        target_menu = ttk.Combobox(shortest_path_frame, textvariable=self.target_field_var, 
                                   values=field_names, width=15, state="readonly", font=('Arial', 12)) 
        target_menu.pack(side=tk.LEFT, padx=5)
        
        tk.Button(shortest_path_frame, 
                  text="▶️ SHOW: Shortest Route (Dijkstra's)", 
                  command=self.run_and_animate_shortest_path, 
                  bg=self.RELAX_COLOR, fg=COLOR_FRAME_WHITE, # Light Theme
                  font=('Arial', 13, 'bold'), 
                  relief='groove', bd=3).pack(side=tk.LEFT, padx=5, ipady=5) 

        # Corrected Button Text
        tk.Button(shortest_path_frame, 
                  text="💸 View Cost Report", 
                  command=self.view_report_page, 
                  bg=COLOR_REPORT_HIGHLIGHT, fg=COLOR_PRIMARY_TEXT, # Light Theme (Dark text on gold)
                  font=('Arial', 13, 'bold'), 
                  relief='groove', bd=3).pack(side=tk.LEFT, padx=10, ipady=5) 
        
        # Ensure Route Value fits
        self.path_cost_label = tk.Label(shortest_path_frame, text="Route Value: --", 
                                        font=('Arial', 12, 'bold'), bg=COLOR_FRAME_WHITE, fg=COLOR_REPORT_HIGHLIGHT, width=18) # Light Theme
        self.path_cost_label.pack(side=tk.LEFT, padx=5, expand=True)

        self.all_distances_label = tk.Label(control_frame, text="", 
                                            font=('Arial', 11, 'italic'), bg=COLOR_FRAME_WHITE, fg=COLOR_PRIMARY_TEXT, pady=5) # Light Theme
        self.all_distances_label.pack(fill=tk.X)
    
    def stop_all_animations(self):
        for after_id in self.active_animations:
            try:
                self.after_cancel(after_id)
            except ValueError:
                pass 
        self.active_animations.clear()

    def load_images(self):
        if not PIL_AVAILABLE: return
        NODE_IMG_SIZE = (70, 70) 
        def safe_load_image(file_name, size):
            try:
                img_path = IMAGE_BASE_PATH / file_name
                if not img_path.exists(): return None 
                img_raw = Image.open(str(img_path)) 
                return ImageTk.PhotoImage(img_raw.resize(size, Image.LANCZOS))
            except Exception as e:
                return None 

        self.node_images['source'] = safe_load_image(self.SOURCE_IMAGE, NODE_IMG_SIZE)
        self.node_images['field'] = safe_load_image(self.FIELD_IMAGE, NODE_IMG_SIZE)
        try:
            bg_path = IMAGE_BASE_PATH / self.BG_IMAGE
            if not bg_path.exists(): self.bg_photo = None
            bg_raw = Image.open(str(bg_path)) 
            self.bg_photo = ImageTk.PhotoImage(bg_raw.resize((CANVAS_WIDTH, CANVAS_HEIGHT), Image.LANCZOS))
        except Exception:
            self.bg_photo = None 
            
    def draw_farm_layout(self):
        self.stop_all_animations() 
        self.canvas.delete("all")
        PIPE_LINE_MAP.clear()
        NODE_TEXT_MAP.clear()
        NODE_CANVAS_IDS.clear() 
        
        # The background should be placed first
        if self.bg_photo:
            self.canvas.create_image(0, 0, image=self.bg_photo, anchor="nw", tags="background")
        
        for cost, u, v in self.edges:
            x1, y1, _, _ = self.nodes[u]
            x2, y2, _, _ = self.nodes[v]
            # Use light gray for default pipe state
            line_id = self.canvas.create_line(x1, y1, x2, y2, fill=COLOR_PIPE_DEFAULT, width=3, dash=(8, 4), state='hidden', tags=f"pipe_{u}_{v}")
            PIPE_LINE_MAP[(u, v)] = line_id
            PIPE_LINE_MAP[(v, u)] = line_id
            mid_x = (x1 + x2) / 2
            mid_y = (y1 + y2) / 2
            # Use dark text for contrast on the light canvas
            text_id = self.canvas.create_text(mid_x, mid_y - 15, text=f"{cost:.0f}", fill=COLOR_PRIMARY_TEXT, font=('Arial', 12, 'bold'), state='hidden', tags="value_label") 
            NODE_TEXT_MAP[(u, v)] = text_id
            NODE_TEXT_MAP[(v, u)] = text_id 
            
        for i, (x, y, label, node_type) in enumerate(self.nodes):
            img = self.node_images.get(node_type)
            if PIL_AVAILABLE and img:
                node_id = self.canvas.create_image(x, y, image=img, tags=f"node_img_{i}")
            else:
                # Use high-contrast fallback colors
                color = COLOR_WATER_SOURCE if i == 0 else COLOR_BUTTON_ACTION 
                node_id = self.canvas.create_oval(x-35, y-35, x+35, y+35, fill=color, outline=COLOR_PRIMARY_TEXT, tags=f"node_fallback_{i}")
            NODE_CANVAS_IDS[i] = node_id 
            # Use dark text for contrast on the light canvas
            self.canvas.create_text(x, y + 45, text=label, fill=COLOR_PRIMARY_TEXT, font=('Arial', 13, 'bold'), tags="node_label") 
        
        # Ensure labels and nodes are on top of pipes
        self.canvas.tag_raise("node_label")
        for i in NODE_CANVAS_IDS.keys():
            self.canvas.tag_raise(f"node_img_{i}")
            self.canvas.tag_raise(f"node_fallback_{i}")
    
    def _animate_node_pulse(self, node_index, pulse_color='#F1C40F', count=0, max_count=4, delay=100):
        node_id = NODE_CANVAS_IDS.get(node_index)
        if not node_id: return
        
        if self.canvas.type(node_id) == 'oval':
            if count % 2 == 0:
                self.canvas.itemconfig(node_id, fill=pulse_color, width=3, outline=pulse_color)
            else:
                is_source = (node_index == 0)
                original_fill = COLOR_WATER_SOURCE if is_source else COLOR_BUTTON_ACTION # Light Theme
                self.canvas.itemconfig(node_id, fill=original_fill, width=1, outline=COLOR_PRIMARY_TEXT)
                
        if count < max_count:
            after_id = self.after(delay, self._animate_node_pulse, node_index, pulse_color, count + 1, max_count, delay)
            self.active_animations.append(after_id)

    def reset_pipes(self, show_all=False):
        self.stop_all_animations() 
        self.canvas.delete("shortest_path_line") 
        self.canvas.delete("shortest_path_value") 
        self.canvas.delete("flow_anim")
        self.all_distances_label.config(text="") 
        for line_id in PIPE_LINE_MAP.values():
            self.canvas.itemconfig(line_id, fill=COLOR_PIPE_DEFAULT, width=3, dash=(8, 4), state='hidden')
        for text_id in NODE_TEXT_MAP.values():
            self.canvas.itemconfig(text_id, state='hidden')
        if show_all:
            for line_id in PIPE_LINE_MAP.values():
                self.canvas.itemconfig(line_id, state='normal')
            for text_id in NODE_TEXT_MAP.values():
                self.canvas.itemconfig(text_id, state='normal')
            self.canvas.tag_lower("background")
            self.canvas.tag_raise("node_label")
            self.canvas.tag_raise("value_label")
            for i in NODE_CANVAS_IDS.keys():
                self.canvas.tag_raise(f"node_img_{i}")
                self.canvas.tag_raise(f"node_fallback_{i}")

    def run_and_animate_mst(self):
        self.reset_pipes(show_all=True)
        self.path_cost_label.config(text="Route Value: --") 
        self.result_label.config(text="Calculating Optimal Piping Design (Kruskal's MST)...")
        self.update()
        
        mst_steps = list(kruskal_mst_steps(self.nodes, self.edges))
        self.total_mst_cost = 0
        self.mst_delay = 500 

        def step_animation(index):
            if index >= len(mst_steps):
                self.result_label.config(text="Optimal Piping Design Complete! (MST Found)")
                self.mst_cost_label.config(text=f"Total Value: {self.total_mst_cost:.1f} meters.")
                return

            step_type, weight, u, v = mst_steps[index]
            pipe_id = PIPE_LINE_MAP.get((u, v)) or PIPE_LINE_MAP.get((v, u))

            if pipe_id:
                if step_type == 'CHECK':
                    # Use Gold for checking, highly visible
                    self.canvas.itemconfig(pipe_id, fill=COLOR_REPORT_HIGHLIGHT, width=5, dash=())
                    self._animate_node_pulse(u, pulse_color=COLOR_REPORT_HIGHLIGHT, count=0, max_count=2, delay=50)
                    self._animate_node_pulse(v, pulse_color=COLOR_REPORT_HIGHLIGHT, count=0, max_count=2, delay=50)
                    self.result_label.config(text=f"Checking Edge: ({self.nodes[u][2]} - {self.nodes[v][2]}) | Cost: {weight:.0f}")
                    next_delay = self.mst_delay

                elif step_type == 'ACCEPT':
                    self.canvas.itemconfig(pipe_id, fill=self.MST_COLOR, width=5, dash=()) 
                    self.total_mst_cost += weight
                    self.result_label.config(text=f"Edge ACCEPTED: ({self.nodes[u][2]} - {self.nodes[v][2]}) | Cost: {weight:.0f}")
                    self.mst_cost_label.config(text=f"Total Value: {self.total_mst_cost:.1f} meters.")
                    next_delay = self.mst_delay

                elif step_type == 'REJECT':
                    self.canvas.itemconfig(pipe_id, fill=COLOR_DANGER, width=6, dash=()) 
                    self.result_label.config(text=f"Edge REJECTED: ({self.nodes[u][2]} - {self.nodes[v][2]}) | CYCLE DETECTED")
                    
                    def reset_reject_line():
                        self.canvas.itemconfig(pipe_id, fill=COLOR_PIPE_DEFAULT, width=3, dash=(8, 4))
                        after_id = self.after(self.mst_delay, step_animation, index + 1)
                        self.active_animations.append(after_id)
                        
                    after_id = self.after(self.mst_delay, reset_reject_line)
                    self.active_animations.append(after_id)
                    return
            
                after_id = self.after(next_delay, step_animation, index + 1)
                self.active_animations.append(after_id)
        
        step_animation(0)

    def run_and_animate_shortest_path(self):
        self.reset_pipes(show_all=False)
        self.mst_cost_label.config(text="Total Value: --") 
        
        target_name = self.target_field_var.get()
        try:
            target_node = next(i for i, node in enumerate(self.nodes) if node[2] == target_name)
        except StopIteration:
            messagebox.showerror("Route Error", "Target field not found.")
            return

        self.result_label.config(text=f"Calculating Shortest Route to {target_name} (Dijkstra's)...")

        distances, previous_nodes, steps = dijkstra_shortest_path_with_steps(self.nodes, self.edges, self.start_node)
        
        self.dijkstra_steps = steps
        self.target_node = target_node
        self.distances = distances
        self.previous_nodes = previous_nodes
        self.dijkstra_delay = 400 
        
        self.controller.last_target_node = target_node
        self.controller.last_route_distance = distances.get(target_node, float('inf'))
        
        self._dijkstra_animate_step(0)

    def view_report_page(self):
        if self.controller.last_route_distance is None:
            messagebox.showinfo("Data Required", "Please run the Dijkstra's Shortest Route calculation first to generate the cost report for a selected field.")
            return
            
        self.stop_all_animations()
        self.controller.show_single_report(self.controller.last_target_node, self.controller.last_route_distance)

    def _dijkstra_animate_step(self, index):
        if index >= len(self.dijkstra_steps):
            self._dijkstra_final_results()
            return

        step = self.dijkstra_steps[index]
        step_type = step[0]
        next_delay = self.dijkstra_delay

        if step_type == 'FINALIZED':
            node_index = step[1]
            self.result_label.config(text=f"Node FINALIZED: Shortest path to {self.nodes[node_index][2]} is set.")
            self._animate_node_pulse(node_index, pulse_color=COLOR_MST_PIPE, max_count=2) # Light Theme
        
        elif step_type == 'RELAXED':
            u, v, new_dist = step[1], step[2], step[3]
            pipe_id = PIPE_LINE_MAP.get((u, v)) or PIPE_LINE_MAP.get((v, u))
            
            if pipe_id:
                self.canvas.itemconfig(pipe_id, fill=self.RELAX_COLOR, width=5, dash=()) 
                self.result_label.config(text=f"Relaxing Edge: {self.nodes[u][2]} -> {self.nodes[v][2]}. New dist to {self.nodes[v][2]}: {new_dist:.1f}")
                
                def reset_relax_line():
                    self.canvas.itemconfig(pipe_id, fill=COLOR_PIPE_DEFAULT, width=3, dash=(8, 4))
                    self._animate_node_pulse(v, pulse_color=COLOR_REPORT_HIGHLIGHT, max_count=2) 
                    after_id = self.after(self.dijkstra_delay, self._dijkstra_animate_step, index + 1)
                    self.active_animations.append(after_id)
                
                after_id = self.after(self.dijkstra_delay, reset_relax_line)
                self.active_animations.append(after_id)
                return
            
        elif step_type == 'COMPARE_WORSE':
            u, v = step[1], step[2]
            self.result_label.config(text=f"Comparison: Edge {self.nodes[u][2]} -> {self.nodes[v][2]} does not improve path.")
            self._animate_node_pulse(v, pulse_color=COLOR_DANGER, max_count=1)

        after_id = self.after(next_delay, self._dijkstra_animate_step, index + 1)
        self.active_animations.append(after_id)

    def _dijkstra_final_results(self):
        total_cost = self.distances[self.target_node]
        target_name = self.nodes[self.target_node][2]
        
        if total_cost == float('inf'):
            self.result_label.config(text=f"Calculation Failed: {target_name} is Unreachable.")
            self.path_cost_label.config(text="Route Value: N/A")
            return
            
        path_edges = reconstruct_path(self.previous_nodes, self.start_node, self.target_node)
        
        self.result_label.config(text=f"Shortest Route to {target_name} Found! Starting water flow...")
        self.path_cost_label.config(text=f"Route Value: {total_cost:.1f} meters.")
        
        self._flow_animation_sequence(path_edges, 0, 
                                      final_callback=lambda: self.controller.show_single_report(self.target_node, total_cost))
        
    def _flow_animation_sequence(self, path_edges, edge_index, final_callback):
        if edge_index >= len(path_edges):
            self.result_label.config(text=f"Water flow reached {self.nodes[self.target_node][2]} successfully! Redirecting to Cost Report...")
            final_callback() 
            return

        u, v = path_edges[edge_index]
        x1, y1, _, _ = self.nodes[u]
        x2, y2, _, _ = self.nodes[v]
        edge_cost = next(cost for cost, n1, n2 in self.edges if (n1 == u and n2 == v) or (n1 == v and n2 == u))
        
        line_id = self.canvas.create_line(x1, y1, x2, y2, fill=self.SHORTEST_PATH_COLOR, width=5, tags="shortest_path_line")
        mid_x = (x1 + x2) / 2
        mid_y = (y1 + y2) / 2
        # Use dark text for contrast on the light canvas
        text_id = self.canvas.create_text(mid_x, mid_y - 15, text=f"{edge_cost:.1f}", fill=COLOR_PRIMARY_TEXT, font=('Arial', 12, 'bold'), tags="shortest_path_value") 
        
        self.canvas.tag_raise("shortest_path_value") 
        for i in NODE_CANVAS_IDS.keys():
            self.canvas.tag_raise(f"node_img_{i}")
            self.canvas.tag_raise(f"node_fallback_{i}")
        self.canvas.tag_raise("node_label")
        
        self._start_single_flow_animation(u, v, lambda: self._flow_animation_sequence(path_edges, edge_index + 1, final_callback))

    def _start_single_flow_animation(self, u, v, next_callback, step=0, total_steps=30, duration_ms=1000, flow_id=None):
        x1, y1, _, _ = self.nodes[u]
        x2, y2, _, _ = self.nodes[v]
        delay = duration_ms // total_steps
        flow_size = 8
        if step == 0:
            flow_id = self.canvas.create_oval(x1 - flow_size, y1 - flow_size, x1 + flow_size, y1 + flow_size, fill=self.FLOW_COLOR, outline=self.FLOW_COLOR, tags="flow_anim") 
            self.canvas.tag_raise("flow_anim")
        if step < total_steps:
            dx = (x2 - x1) / total_steps
            dy = (y2 - y1) / total_steps
            self.canvas.move(flow_id, dx, dy)
            after_id = self.after(delay, self._start_single_flow_animation, u, v, next_callback, step + 1, total_steps, duration_ms, flow_id)
            self.active_animations.append(after_id)
        else:
            self.canvas.delete(flow_id)
            next_callback() 

# ----------------------------------------------------------------------
# --- Page 3: Single Field Report Page - Modern Light Theme ---
# ----------------------------------------------------------------------

class SingleFieldReportPage(tk.Frame):
    def __init__(self, parent, controller, nodes):
        tk.Frame.__init__(self, parent, bg=COLOR_BG_LIGHT) # Light Theme
        self.controller = controller
        self.nodes = nodes
        
        self.COST_PER_METER = 100 
        
        main_frame = tk.Frame(self, bg=COLOR_BG_LIGHT, padx=50, pady=50) # Light Theme
        main_frame.place(relx=0.5, rely=0.5, anchor=tk.CENTER, relwidth=0.8, relheight=0.8)

        # Title
        self.title_label = tk.Label(main_frame, 
                 text="💸 Shortest Pipeline Cost Report 💸", 
                 font=('Arial', 24, 'bold'), 
                 bg=COLOR_BG_LIGHT, fg=COLOR_REPORT_HIGHLIGHT) # Light Theme
        self.title_label.pack(pady=(0, 40))

        # Dynamic Target Field Label
        self.field_label = tk.Label(main_frame, 
                 text="Target Field: --", 
                 font=('Arial', 18, 'bold'), 
                 bg=COLOR_BG_LIGHT, fg=COLOR_MST_PIPE) # Light Theme
        self.field_label.pack(pady=(10, 20))
        
        # Details Frame for a clean layout of results
        details_frame = tk.Frame(main_frame, bg=COLOR_FRAME_WHITE, padx=30, pady=30, relief='raised', bd=3) # Light Theme
        details_frame.pack(pady=20, fill='x', padx=100)

        # Route Value (Distance)
        tk.Label(details_frame, text="Shortest Route Distance:", 
                 font=('Arial', 16), bg=COLOR_FRAME_WHITE, fg=COLOR_PRIMARY_TEXT, anchor='w').grid(row=0, column=0, padx=10, pady=10, sticky='w') # Light Theme
        self.distance_value = tk.Label(details_frame, text="--", 
                                       font=('Arial', 16, 'bold'), bg=COLOR_FRAME_WHITE, fg=COLOR_FLOW, anchor='e') # Light Theme
        self.distance_value.grid(row=0, column=1, padx=10, pady=10, sticky='e')

        # Total Cost (Rs)
        tk.Label(details_frame, text=f"Total Piping Cost (Rs) @ ₹{self.COST_PER_METER}/meter:", 
                 font=('Arial', 16), bg=COLOR_FRAME_WHITE, fg=COLOR_PRIMARY_TEXT, anchor='w').grid(row=1, column=0, padx=10, pady=10, sticky='w') # Light Theme
        self.cost_value = tk.Label(details_frame, text="--", 
                                   font=('Arial', 16, 'bold'), bg=COLOR_FRAME_WHITE, fg=COLOR_REPORT_HIGHLIGHT, anchor='e') # Light Theme
        self.cost_value.grid(row=1, column=1, padx=10, pady=10, sticky='e')
        
        details_frame.grid_columnconfigure(1, weight=1) 

        # Back Button
        tk.Button(main_frame, 
                  text="🔙 Back to Simulator", 
                  command=lambda: controller.show_frame("SimulatorPage"), 
                  bg=COLOR_BUTTON_ACTION, fg=COLOR_FRAME_WHITE, # Light Theme
                  font=('Arial', 14, 'bold'), 
                  relief='raised', bd=4).pack(pady=40, ipadx=20, ipady=10)

    def update_report(self, target_node, distance):
        target_name = self.nodes[target_node][2]
        
        self.field_label.config(text=f"Target Field: **{target_name}**")
        
        if distance == float('inf'):
            self.distance_value.config(text="Unreachable")
            self.cost_value.config(text="N/A (Field is unreachable)")
        else:
            total_cost = distance * self.COST_PER_METER
            
            self.distance_value.config(text=f"{distance:.1f} meters")
            self.cost_value.config(text=f"₹ {total_cost:,.2f}") 
        

# --- Main Execution ---

if __name__ == "__main__":
    if PIL_AVAILABLE:
        print(f"Pillow is available. Checking for assets in: {IMAGE_BASE_PATH.resolve()}")
    else:
        print("Pillow is NOT available. Using fallback shapes for visualization.")
        
    app = SmartIrrigationApp(FARM_NODES, DEFAULT_FARM_EDGES)
    app.mainloop()