import tkinter as tk
from tkinter import ttk, scrolledtext, messagebox
import threading
import time
import datetime
import requests
import base64
import pyautogui
import io
import os
import difflib
import ctypes
from ctypes import wintypes
from PIL import Image, ImageTk, ImageChops, ImageStat, ImageDraw

# =========================================================================
#                                 配置区域
# =========================================================================

# --- API 设置 ---
OCR_API_URL = "http://127.0.0.1:1234/v1/chat/completions"
OCR_MODEL_ID = "qwen/qwen3-vl-4b"

VLM_API_URL = "http://192.168.71.10:1234/v1/chat/completions"
VLM_MODEL_ID = "qwen/qwen3-vl-30b"

# --- 运行参数 ---
CAPTURE_INTERVAL = 2.5  # 采样间隔 (秒)
BATCH_SIZE = 4  # 4帧拼接 (约10秒)
SUMMARY_TRIGGER_BATCHES = 6  # 6次批处理后触发阶段回顾 (约60秒)

# --- 自适应分辨率 ---
OCR_TARGET_WIDTH = 1024
VLM_MAX_DIMENSION = 1560

# --- 视觉参数 ---
SCENE_CHANGE_THRESHOLD = 2.0

# =========================================================================
#                                 提示词 (Prompts)
# =========================================================================

PROMPT_OCR = (
    "你是一个专门的字幕读取程序。这张图片是同一位置、不同时间的字幕区域截图，被纵向拼接在一起。\n"
    "【去重任务】\n"
    "1. 合并重复项：如果连续多行文字内容相同（或仅有微小OCR误差），请只输出一次。\n"
    "2. 忽略无效内容：不输出水印、台标、纯符号或非中文内容。\n"
    "3. 输出格式：直接输出净化后的中文字幕文本，忽略日语和英语,不要加任何序号或前缀。如果全图无中文内容，回复“无”。"
)

PROMPT_BATCH_ANALYSIS = (
    "你是一个客观冷静的视频记录员。正在分析一段约10秒的视频片段。\n"
    "【历史上下文（前20秒）】：\n{history}\n\n"
    "【当前输入】：\n"
    "1. 图片：由4个连续时刻画面按2x2拼接而成。\n"
    "2. 字幕文本：\n{subtitles}\n\n"
    "【分析要求】：\n"
    "1. 客观描述：像监控记录员一样，描述画面中“谁”在“做什么”。重点关注肉眼可见的动作、物体交互和环境变化。\n"
    "2. 视听融合：结合字幕，指出是谁说了这些话。\n"
    "3. 情感推测（基于视觉）：你可以根据画面的光影、色调、构图以及人物的面部表情来推测当前的情感基调（如：压抑、明快、紧张等）。\n"
    "4. 严禁读心：绝对不要猜测人物内心的想法、意图、回忆或潜台词。只描述表现出来的东西。\n"
    "5. 字数限制：150字以内。"
)

PROMPT_PHASE_SUMMARY = (
    "你是一个专业的剧情剪辑师。请进行阶段性回顾。\n"
    "【全局故事脉络（所有已发生的阶段）】：\n{past_summaries}\n\n"
    "【最近1分钟的微观记录】：\n{recent_logs}\n\n"
    "【任务】：\n"
    "1. 逻辑整合：结合全局脉络和最近的细节，概括这1分钟内的剧情。\n"
    "2. 因果梳理：修正碎片化记录中的逻辑断层，明确“因为A做了什么，导致B产生了什么反应”。\n"
    "3. 客观总结：去除琐碎的动作描写，提炼核心事件。不要揣测人物的内心或者想法,只做如实描述。\n"
    "4. 字数限制：250字以内。如果你没有看到多条全局故事脉络，说明故事才刚刚开始，你应该总结的更简单些，不要凑字数。"
)

PROMPT_FINAL_SUMMARY = (
    "你是一位百万粉影视解说博主。全片播放结束，请根据所有的阶段剧情，撰写最终的解说文案。\n"
    "【要求】\n"
    "1. 沉浸感：像讲故事一样，有开端、发展、高潮和结尾。\n"
    "2. 情感共鸣：通过分析人物的心理变化和台词细节，带动观众的情绪。\n"
    "3. 客观解析：按时间线准确复述发生了什么，不要添加任何猜测的细节。\n"
    "4. 字数限制：800字左右。"
)


# =========================================================================
#                                 窗口控制器 (后台控制版)
# =========================================================================

class WindowController:
    """使用 PostMessage 实现后台窗口控制"""

    def __init__(self):
        self.user32 = ctypes.windll.user32
        self.WM_KEYDOWN = 0x0100
        self.WM_KEYUP = 0x0101
        self.VK_SPACE = 0x20  # 空格键

    def toggle_play_pause(self, region):
        if not region: return
        x, y, w, h = region
        center_x = x + w // 2
        center_y = y + h // 2
        point = wintypes.POINT(center_x, center_y)

        # 获取坐标下的窗口句柄
        hwnd = self.user32.WindowFromPoint(point)

        if hwnd:
            # 获取该句柄的根窗口
            root_hwnd = self.user32.GetAncestor(hwnd, 2)  # GA_ROOT = 2
            target_hwnd = root_hwnd if root_hwnd else hwnd

            # 直接发送按键消息，无需置于前台
            self.user32.PostMessageW(target_hwnd, self.WM_KEYDOWN, self.VK_SPACE, 0)
            self.user32.PostMessageW(target_hwnd, self.WM_KEYUP, self.VK_SPACE, 0)
            print(f"Sent SPACE to HWND: {target_hwnd} (Background Mode)")
        else:
            print("No window found under selection.")


# =========================================================================
#                                 主程序逻辑
# =========================================================================

class SubtitleDeduplicator:
    def __init__(self, max_history=10):
        self.history = []
        self.max_history = max_history

    def process(self, raw_text):
        if not raw_text or "无" in raw_text: return ""
        lines = [line.strip() for line in raw_text.split('\n') if line.strip()]
        unique_lines = []
        for line in lines:
            if len(line) < 2: continue
            is_dup = False
            for old in self.history:
                if difflib.SequenceMatcher(None, line, old).ratio() > 0.85:
                    is_dup = True
                    break
            if not is_dup:
                unique_lines.append(line)
                self.history.append(line)
        if len(self.history) > self.max_history:
            self.history = self.history[-self.max_history:]
        return " ".join(unique_lines)


class VideoAnalyzerApp:
    def __init__(self, root):
        self.root = root
        self.root.title("Video AI Analyzer V10.0 (Async & Background Ctrl)")
        self.root.geometry("1400x900")

        style = ttk.Style()
        style.theme_use('clam')
        style.configure("TFrame", background="#f0f0f0")
        style.configure("TLabel", background="#f0f0f0", font=("Microsoft YaHei", 9))
        style.configure("Header.TLabel", font=("Microsoft YaHei", 12, "bold"), foreground="#333")
        style.configure("Status.TLabel", font=("Consolas", 9), foreground="#555")

        self.is_running = False
        self.capture_region = None
        self.region_text = tk.StringVar(value="未选择区域")
        self.status_text = tk.StringVar(value="就绪")
        self.log_filename = ""

        self.diff_var = tk.DoubleVar(value=0.0)
        self.buffer_var = tk.DoubleVar(value=0.0)

        self.frame_buffer = []
        self.subtitle_buffer = []
        self.analysis_logs = []
        self.phase_summaries = []

        self.deduplicator = SubtitleDeduplicator()
        self.video_ctrl = WindowController()
        self.last_pil_image = None

        self.setup_ui()
        self.setup_region_selector()

    def setup_ui(self):
        toolbar = ttk.Frame(self.root, padding=10)
        toolbar.pack(fill=tk.X)

        ttk.Label(toolbar, text="Video AI Analyzer V10", style="Header.TLabel").pack(side=tk.LEFT, padx=(0, 20))
        ttk.Button(toolbar, text="✂️ 框选屏幕区域", command=self.start_region_selection).pack(side=tk.LEFT, padx=5)
        ttk.Label(toolbar, textvariable=self.region_text, foreground="#0066cc").pack(side=tk.LEFT, padx=5)
        ttk.Separator(toolbar, orient=tk.VERTICAL).pack(side=tk.LEFT, padx=20, fill=tk.Y)

        self.btn_start = ttk.Button(toolbar, text="▶ 启动分析", command=self.start_analysis, state=tk.DISABLED)
        self.btn_start.pack(side=tk.LEFT, padx=5)
        self.btn_stop = ttk.Button(toolbar, text="■ 停止并生成报告", command=self.stop_analysis_trigger,
                                   state=tk.DISABLED)
        self.btn_stop.pack(side=tk.LEFT, padx=5)

        main_pane = ttk.PanedWindow(self.root, orient=tk.HORIZONTAL)
        main_pane.pack(fill=tk.BOTH, expand=True, padx=10, pady=(0, 10))

        # 左侧
        left_frame = ttk.Frame(main_pane, width=320)
        main_pane.add(left_frame, weight=0)

        preview_group = ttk.LabelFrame(left_frame, text="实时画面 (Live)", padding=5)
        preview_group.pack(fill=tk.X, pady=5)
        self.lbl_image = ttk.Label(preview_group, text="等待信号...", anchor="center", background="#333",
                                   foreground="#888")
        self.lbl_image.pack(fill=tk.BOTH, expand=True, ipady=40)

        status_group = ttk.LabelFrame(left_frame, text="状态仪表盘", padding=10)
        status_group.pack(fill=tk.X, pady=5)

        ttk.Label(status_group, text="视觉动态:").pack(anchor="w")
        self.pb_diff = ttk.Progressbar(status_group, variable=self.diff_var, maximum=20.0, mode='determinate')
        self.pb_diff.pack(fill=tk.X, pady=(2, 8))

        ttk.Label(status_group, text=f"批处理缓冲:").pack(anchor="w")
        self.pb_buffer = ttk.Progressbar(status_group, variable=self.buffer_var, maximum=BATCH_SIZE, mode='determinate')
        self.pb_buffer.pack(fill=tk.X, pady=(2, 8))

        ttk.Separator(status_group, orient=tk.HORIZONTAL).pack(fill=tk.X, pady=8)
        self.lbl_status_detail = ttk.Label(status_group, textvariable=self.status_text, foreground="#d9534f",
                                           wraplength=280)
        self.lbl_status_detail.pack(anchor="w", fill=tk.X)

        # 中间
        center_frame = ttk.LabelFrame(main_pane, text="📝 实时剧情 (Detail)", padding=5)
        main_pane.add(center_frame, weight=3)
        self.txt_stream = scrolledtext.ScrolledText(center_frame, font=("Microsoft YaHei UI", 10), state='disabled',
                                                    padx=10, pady=10)
        self.txt_stream.pack(fill=tk.BOTH, expand=True)
        self.txt_stream.tag_config("time", foreground="#999999", font=("Consolas", 9))
        self.txt_stream.tag_config("sub", foreground="#0056b3", font=("Microsoft YaHei UI", 10, "bold"))
        self.txt_stream.tag_config("plot", foreground="#333333")

        # 右侧
        right_frame = ttk.LabelFrame(main_pane, text=" 宏观剧情 (Summary)", padding=5)
        main_pane.add(right_frame, weight=2)
        self.txt_summary = scrolledtext.ScrolledText(right_frame, font=("Microsoft YaHei UI", 10), state='disabled',
                                                     padx=10, pady=10)
        self.txt_summary.pack(fill=tk.BOTH, expand=True)
        self.txt_summary.tag_config("header", background="#e9ecef", foreground="#495057",
                                    font=("Microsoft YaHei UI", 10, "bold"))

        self.statusbar = ttk.Label(self.root, text="就绪", relief=tk.SUNKEN, anchor="w", padding=(10, 5))
        self.statusbar.pack(fill=tk.X)

    def setup_region_selector(self):
        self.region_win_class = type('RegionSelectionWindow', (tk.Toplevel,), {})  # 动态定义或保持原类

    # ================= 截图与图像处理 =================

    def start_region_selection(self):
        self.root.iconify()
        time.sleep(0.2)
        RegionSelectionWindow(self.root, self.on_region_selected)

    def on_region_selected(self, region):
        self.root.deiconify()
        self.capture_region = region
        self.region_text.set(f"已选: {region[2]}x{region[3]} @ ({region[0]},{region[1]})")
        self.btn_start.config(state=tk.NORMAL)
        self.update_status("区域已锁定")

    def update_status(self, msg, is_error=False):
        self.status_text.set(msg)
        self.lbl_status_detail.config(foreground="red" if is_error else "#28a745")
        self.statusbar.config(text=f"{msg} | {datetime.datetime.now().strftime('%H:%M:%S')}")

    def capture_screen(self):
        if not self.capture_region: return None
        try:
            return pyautogui.screenshot(region=self.capture_region)
        except:
            return None

    def update_preview_image(self, img):
        if img:
            disp = img.copy()
            disp.thumbnail((280, 200))
            photo = ImageTk.PhotoImage(disp)
            self.lbl_image.config(image=photo, text="")
            self.lbl_image.image = photo

    def adaptive_resize_for_vlm(self, img):
        w, h = img.size
        if w > VLM_MAX_DIMENSION or h > VLM_MAX_DIMENSION:
            ratio = min(VLM_MAX_DIMENSION / w, VLM_MAX_DIMENSION / h)
            return img.resize((int(w * ratio), int(h * ratio)), Image.Resampling.LANCZOS)
        return img

    def adaptive_resize_for_ocr(self, img):
        w, h = img.size
        ratio = OCR_TARGET_WIDTH / w
        return img.resize((OCR_TARGET_WIDTH, int(h * ratio)), Image.Resampling.LANCZOS)

    def stitch_images_grid_2x2(self, images):
        if len(images) != 4: return None
        w, h = images[0].size
        cw, ch = w // 2, h // 2
        target = Image.new('RGB', (w, h))
        target.paste(images[0].resize((cw, ch)), (0, 0))
        target.paste(images[1].resize((cw, ch)), (cw, 0))
        target.paste(images[2].resize((cw, ch)), (0, ch))
        target.paste(images[3].resize((cw, ch)), (cw, ch))
        return target

    def stitch_images_vertical(self, images):
        if not images: return None
        w, h = images[0].size
        target = Image.new('RGB', (w, h * len(images)))
        for i, img in enumerate(images):
            target.paste(img, (0, i * h))
        return target

    def image_to_base64(self, img):
        buffered = io.BytesIO()
        img.save(buffered, format="JPEG", quality=85)
        return f"data:image/jpeg;base64,{base64.b64encode(buffered.getvalue()).decode()}"

    def calculate_diff(self, img_new):
        if self.last_pil_image is None: return 100.0
        i1 = self.last_pil_image.resize((64, 36)).convert("RGB")
        i2 = img_new.resize((64, 36)).convert("RGB")
        diff = ImageChops.difference(i1, i2)
        stat = ImageStat.Stat(diff)
        return sum(stat.mean) / len(stat.mean)

    # ================= 核心流程 =================

    def start_analysis(self):
        self.is_running = True
        self.frame_buffer = []
        self.subtitle_buffer = []
        self.analysis_logs = []
        self.phase_summaries = []
        self.deduplicator = SubtitleDeduplicator()

        self.log_filename = f"movie_log_{datetime.datetime.now().strftime('%Y%m%d_%H%M%S')}.txt"

        self.btn_start.config(state=tk.DISABLED)
        self.btn_stop.config(state=tk.NORMAL)
        self.update_status("分析启动")

        threading.Thread(target=self.analysis_loop, daemon=True).start()

    def stop_analysis_trigger(self):
        self.is_running = False
        self.update_status("请求停止，等待结算...")

    def analysis_loop(self):
        batch_counter = 0

        while self.is_running:
            loop_start = time.time()
            current_img = self.capture_screen()

            if current_img:
                # 1. 更新预览
                self.root.after(0, lambda img=current_img: self.update_preview_image(img))

                # 2. 差异计算
                diff = self.calculate_diff(current_img)
                self.root.after(0, lambda v=diff: self.diff_var.set(v))
                self.last_pil_image = current_img

                # 3. 采集入库
                w, h = current_img.size
                sub_h = int(h / 5)
                self.subtitle_buffer.append(current_img.crop((0, h - sub_h, w, h)))
                self.frame_buffer.append(current_img)

                current_len = len(self.frame_buffer)
                self.root.after(0, lambda v=current_len: self.buffer_var.set(v))
                self.root.after(0, lambda: self.update_status(f"捕获中 {current_len}/{BATCH_SIZE}"))

                if current_len >= BATCH_SIZE:
                    # 并行处理：快照当前数据，启动线程，清空缓冲
                    frames_snapshot = list(self.frame_buffer)
                    subs_snapshot = list(self.subtitle_buffer)
                    current_batch_index = batch_counter

                    # 启动分析线程
                    threading.Thread(
                        target=self.process_batch_async,
                        args=(current_batch_index, frames_snapshot, subs_snapshot)
                    ).start()

                    # 立即清空，准备下一批
                    self.frame_buffer = []
                    self.subtitle_buffer = []
                    self.root.after(0, lambda: self.buffer_var.set(0))

                    batch_counter += 1

                    # 阶段回顾（暂停视频）
                    if batch_counter % SUMMARY_TRIGGER_BATCHES == 0:
                        self.process_phase_summary()

            elapsed = time.time() - loop_start
            wait = max(0.1, CAPTURE_INTERVAL - elapsed)
            time.sleep(wait)

        self.process_final_report()
        self.root.after(0, lambda: self.btn_start.config(state=tk.NORMAL))
        self.root.after(0, lambda: self.btn_stop.config(state=tk.DISABLED))
        self.root.after(0, lambda: self.update_status("已停止"))

    def process_batch_async(self, index, frames, subs):
        """异步处理单批次分析"""
        self.root.after(0, lambda: self.update_status(f"后台分析批次 {index + 1}...", is_error=True))

        # 1. OCR (使用快照数据)
        stitched_sub = self.stitch_images_vertical(subs)
        clean_subs = "无"
        if stitched_sub:
            stitched_sub = self.adaptive_resize_for_ocr(stitched_sub)
            raw = self.call_llm(OCR_API_URL, OCR_MODEL_ID, [
                {"role": "system", "content": PROMPT_OCR},
                {"role": "user",
                 "content": [{"type": "image_url", "image_url": {"url": self.image_to_base64(stitched_sub)}}]}
            ], max_tokens=150)
            clean_subs = self.deduplicator.process(raw)

        # 2. VLM (使用快照数据)
        stitched_plot = self.stitch_images_grid_2x2(frames)
        if stitched_plot:
            stitched_plot = self.adaptive_resize_for_vlm(stitched_plot)

            # 访问共享资源 analysis_logs 
            history_context = "\n".join(self.analysis_logs[-2:]) if self.analysis_logs else "（无历史记录）"

            prompt = PROMPT_BATCH_ANALYSIS.format(
                history=history_context,
                subtitles=clean_subs if clean_subs else "（无对白）"
            )

            plot = self.call_llm(VLM_API_URL, VLM_MODEL_ID, [
                {"role": "user", "content": [
                    {"type": "text", "text": prompt},
                    {"type": "image_url", "image_url": {"url": self.image_to_base64(stitched_plot)}}
                ]}
            ], max_tokens=350)

            if plot:
                entry = f"【片段 {index * 10}s+】\n字幕：{clean_subs}\n剧情：{plot}\n"
                # 写入共享资源 (append 是原子的，基本安全)
                self.analysis_logs.append(entry)
                self.log_stream(index, clean_subs, plot)
                self.write_file(entry)

    def process_phase_summary(self):
        """阶段回顾：暂停视频"""
        # 1. 暂停视频
        self.root.after(0, lambda: self.update_status("⚠️ 阶段回顾，暂停视频..."))
        self.video_ctrl.toggle_play_pause(self.capture_region)

        # 2. 稍微等待确保暂停生效
        time.sleep(1.0)

        self.root.after(0, lambda: self.update_status("AI 生成阶段回顾中..."))

        past_summaries = "\n".join(self.phase_summaries) if self.phase_summaries else "（暂无先前阶段）"
        recent_logs = "\n".join(self.analysis_logs[-SUMMARY_TRIGGER_BATCHES:])

        prompt = PROMPT_PHASE_SUMMARY.format(
            past_summaries=past_summaries,
            recent_logs=recent_logs
        )

        summary = self.call_llm(VLM_API_URL, VLM_MODEL_ID, [
            {"role": "user", "content": prompt}
        ], max_tokens=600)

        if summary:
            self.phase_summaries.append(summary)
            self.log_summary(f"第 {len(self.phase_summaries)} 阶段回顾", summary)
            self.write_file(f"\n=== 阶段回顾 ===\n{summary}\n")

        # 3. 恢复视频
        self.root.after(0, lambda: self.update_status("恢复播放..."))
        self.video_ctrl.toggle_play_pause(self.capture_region)
        time.sleep(0.5)

    def process_final_report(self):
        self.root.after(0, lambda: self.update_status("生成最终解说..."))
        if len(self.analysis_logs) % SUMMARY_TRIGGER_BATCHES != 0:
            self.process_phase_summary()

        context = "\n".join([f"阶段{i + 1}: {s}" for i, s in enumerate(self.phase_summaries)])
        final = self.call_llm(VLM_API_URL, VLM_MODEL_ID, [
            {"role": "system", "content": PROMPT_FINAL_SUMMARY},
            {"role": "user", "content": f"全片脉络：\n{context}"}
        ], max_tokens=2500)

        if final:
            self.write_file("\n\n★ 最终解说 ★\n" + final)
            self.log_summary("★ 全片最终解说 ★", final)
            messagebox.showinfo("完成", "解说文案生成完毕！")

    def call_llm(self, url, model, messages, max_tokens=200):
        try:
            resp = requests.post(url, json={
                "model": model, "messages": messages,
                "temperature": 0.7, "max_tokens": max_tokens
            }, timeout=90)
            if resp.status_code == 200:
                return resp.json()['choices'][0]['message']['content']
        except Exception as e:
            print(f"API Error: {e}")
        return None

    def log_stream(self, index, sub, plot):
        timestamp = datetime.datetime.now().strftime("%H:%M:%S")
        self.root.after(0, lambda: self._insert_stream(timestamp, sub, plot))

    def _insert_stream(self, ts, sub, plot):
        self.txt_stream.config(state='normal')
        self.txt_stream.insert(tk.END, f"[{ts}] 分析节点\n", "time")
        self.txt_stream.insert(tk.END, f"🗣️ {sub}\n", "sub")
        self.txt_stream.insert(tk.END, f"🎬 {plot}\n", "plot")
        self.txt_stream.insert(tk.END, "-" * 40 + "\n", "time")
        self.txt_stream.see(tk.END)
        self.txt_stream.config(state='disabled')

    def log_summary(self, title, content):
        self.root.after(0, lambda: self._insert_summary(title, content))

    def _insert_summary(self, title, content):
        self.txt_summary.config(state='normal')
        self.txt_summary.insert(tk.END, f"\n=== {title} ===\n", "header")
        self.txt_summary.insert(tk.END, f"{content}\n")
        self.txt_summary.see(tk.END)
        self.txt_summary.config(state='disabled')

    def write_file(self, text):
        if self.log_filename:
            with open(self.log_filename, "a", encoding="utf-8") as f:
                f.write(text + "\n")


# 定义选区类 (保持完整，修复引用)
class RegionSelectionWindow(tk.Toplevel):
    def __init__(self, master, callback):
        super().__init__(master)
        self.callback = callback
        self.attributes('-fullscreen', True)
        self.attributes('-alpha', 0.3)
        self.attributes('-topmost', True)
        self.configure(bg='black', cursor="crosshair")

        self.canvas = tk.Canvas(self, bg="black", highlightthickness=0)
        self.canvas.pack(fill=tk.BOTH, expand=True)

        self.start_x = None
        self.start_y = None
        self.rect_id = None

        self.canvas.bind('<Button-1>', self.on_press)
        self.canvas.bind('<B1-Motion>', self.on_drag)
        self.canvas.bind('<ButtonRelease-1>', self.on_release)
        self.bind('<Escape>', lambda e: self.destroy())

    def on_press(self, event):
        self.start_x = event.x
        self.start_y = event.y
        self.rect_id = self.canvas.create_rectangle(
            self.start_x, self.start_y, self.start_x, self.start_y,
            outline='#00ff00', width=2, fill='#ffffff', stipple='gray12'
        )

    def on_drag(self, event):
        self.canvas.coords(self.rect_id, self.start_x, self.start_y, event.x, event.y)

    def on_release(self, event):
        x1 = min(self.start_x, event.x)
        y1 = min(self.start_y, event.y)
        x2 = max(self.start_x, event.x)
        y2 = max(self.start_y, event.y)
        if (x2 - x1) > 50 and (y2 - y1) > 50:
            self.callback((x1, y1, x2 - x1, y2 - y1))
            self.destroy()
        else:
            self.canvas.delete(self.rect_id)


if __name__ == "__main__":
    root = tk.Tk()
    app = VideoAnalyzerApp(root)

    root.mainloop()
