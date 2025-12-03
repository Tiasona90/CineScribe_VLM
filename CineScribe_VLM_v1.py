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
import json
import re
from PIL import Image, ImageTk, ImageChops, ImageStat  # 引入图像计算

try:
    import pygetwindow as gw
except ImportError:
    gw = None
    print("Warning: pygetwindow not installed. Window selection might fail.")

# =========================================================================
#                                 配置区域
# =========================================================================

# --- API 设置 ---
LLM_API_URL = "http://192.168.71.10:1234/v1/chat/completions"
MODEL_ID = "qwen/qwen3-vl-30b"

# --- 运行参数 ---
DEFAULT_INTERVAL = 3  # 默认采样间隔 (秒)
SUMMARY_TRIGGER_COUNT = 12  # 每分析多少帧触发一次阶段回顾
AUTO_PAUSE_VIDEO = True  # 阶段回顾时是否尝试暂停视频

# --- 视觉去重参数 ---
ENABLE_VISUAL_DEDUP = True  # 是否开启视觉去重
SCENE_CHANGE_THRESHOLD = 2.5  # 差异阈值 (0-255)。
MAX_SKIP_COUNT = 10  # 即使画面一直不动，每跳过多少次也强制分析一次

# --- 提示词 (Prompt) 设置 ---

# 1. 单帧分析模式
PROMPT_SINGLE_FRAME = (
    "你是一个客观的视频画面记录员。请分析当前画面。只关注视频内容，忽略各种电脑UI、水印、日语字幕和弹幕内容。\n"
    "【要求】\n"
   "1. 判断说话人：画面下方若有中文字幕，请仔细观察画面中人物的嘴唇状态和肢体语言。\n"
    "   - 如果人物有明显的说话动作或其他可以判断说话人的情况，请明确指出是该人物在说，格式：'人物特征或名字(例如白衣衬衫长发蓝眼男): [字幕内容]'\n"
    "   - 如果画面中人物闭着嘴（主要在倾听）或没有人物或无法判断是谁在说话，请标记为未知人物或者旁白，格式：'未知角色: [字幕内容]'或者类似表达方式\n"
    "2. 视觉描述：客观描述画面视觉内容（人物动作、场景）。重点关注变化部分。\n"
    "3. 情感捕捉：描述画面的情感基调（如紧张、温馨、压抑）。\n"
    "4. 回复字数严格控制在 130字 以内。注意,即使字幕来自未知人物,也应该完整记录。只关注中文即可"
)

# 2. 阶段回顾模式
PROMPT_PHASE_SUMMARY = (
    """你是一个剧情梳理专家。请根据提供的最近多条画面记录，对这段时间的剧情进行阶段性回顾。
    解释这一片段中发生了什么主要事件，包括谁做了什么。
    由于单帧记录可能存在误判（例如将画外音误认为是当前画面人物所说），请你根据上下文逻辑进行修正：
    整合人物的对话（基于字幕记录）和行为。简单分析人物的性格与情感。如果你认为可以确定某个角色的名字，请记录下来。
    语言精炼，承上启下。
    回复字数严格控制在 200字 以内。"""
)

# 3. 最终总结模式 (已优化：强调具体细节和故事性)
PROMPT_FINAL_SUMMARY = (
    "你是一位专注于深度剧情解析的影视解说文案创作者。全片播放结束，请根据所有的剧情阶段回顾，撰写一份细节丰富、剧情连贯的解说文案。\n"
    "【关键要求】\n"
    "1. 拒绝流水账和笼统概括。请像讲故事一样，详细描述关键的情节转折、人物的具体对话内容（基于字幕记录）和他们的情感变化。\n"
    "2. 还原细节：例如不要只说'两人发生了争吵'，要尝试还原争吵的具体内容，例如'A指责B背叛了信任，而B愤怒地辩解...'。\n"
    "3. 逻辑重构：将零散的阶段回顾串联成一个有因有果、起承转合的完整故事。修正之前阶段回顾中可能存在的误判，使整体逻辑自洽。\n"
    "4. 语言风格生动沉浸，像在给朋友绘声绘色地讲电影。\n"
    "5. 回复字数控制在 1500字 以内。"
)


# =========================================================================
#                                 代码主体
# =========================================================================

class VideoAnalyzerApp:
    def __init__(self, root):
        self.root = root
        self.root.title("CineScribe_VLM")
        self.root.geometry("1200x900")

        # 数据存储
        self.is_running = False
        self.target_window_title = tk.StringVar(value="")
        self.log_filename = ""

        # 核心记忆库
        self.raw_frame_logs = []  # 存储每一次单帧分析的文本结果
        self.phase_summaries = []  # 存储每一次阶段回顾的文本结果

        self.sampling_interval = DEFAULT_INTERVAL

        # 视觉去重状态
        self.last_pil_image = None
        self.consecutive_skips = 0

        # 裁切设置 (上, 下, 左, 右) - 单位像素
        self.crop_top = tk.IntVar(value=0)
        self.crop_bottom = tk.IntVar(value=0)
        self.crop_left = tk.IntVar(value=0)
        self.crop_right = tk.IntVar(value=0)

        # 界面初始化
        self.setup_ui()

    def setup_ui(self):
        # 1. 顶部控制栏
        control_frame = ttk.Frame(self.root, padding="10")
        control_frame.pack(fill=tk.X)

        ttk.Label(control_frame, text="目标窗口:").pack(side=tk.LEFT)
        entry_target = ttk.Entry(control_frame, textvariable=self.target_window_title, width=18)
        entry_target.pack(side=tk.LEFT, padx=5)

        self.btn_pick = ttk.Button(control_frame, text="🖱️ 选取", command=self.start_window_picker)
        self.btn_pick.pack(side=tk.LEFT, padx=2)

        ttk.Separator(control_frame, orient=tk.VERTICAL).pack(side=tk.LEFT, padx=10, fill=tk.Y)

        ttk.Label(control_frame, text="间隔(s):").pack(side=tk.LEFT)
        self.spin_interval = ttk.Spinbox(control_frame, from_=0.5, to=10.0, increment=0.5, width=4)
        self.spin_interval.set(DEFAULT_INTERVAL)
        self.spin_interval.pack(side=tk.LEFT, padx=5)

        self.lbl_dedup = ttk.Label(control_frame, text="[视觉去重: ON ]", foreground="blue")
        self.lbl_dedup.pack(side=tk.LEFT, padx=5)

        ttk.Separator(control_frame, orient=tk.VERTICAL).pack(side=tk.LEFT, padx=10, fill=tk.Y)

        self.btn_start = ttk.Button(control_frame, text="▶ 开始", command=self.start_analysis)
        self.btn_start.pack(side=tk.LEFT, padx=5)

        self.btn_stop = ttk.Button(control_frame, text="■ 结束", command=self.stop_analysis_trigger, state=tk.DISABLED)
        self.btn_stop.pack(side=tk.LEFT, padx=5)

        self.lbl_status = ttk.Label(control_frame, text="就绪", foreground="gray")
        self.lbl_status.pack(side=tk.LEFT, padx=15)

        # 2. 中间主要区域
        main_paned = ttk.PanedWindow(self.root, orient=tk.HORIZONTAL)
        main_paned.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)

        # 左侧：图像 + 阶段回顾展示
        left_panel = ttk.Frame(main_paned)
        main_paned.add(left_panel, weight=1)

        # 图像预览与设置区域
        self.img_frame = ttk.LabelFrame(left_panel, text="监控预览与设置", height=300)
        self.img_frame.pack(fill=tk.X, expand=False, pady=(0, 5))

        # --- 裁切控制面板 ---
        crop_frame = ttk.Frame(self.img_frame, padding=5)
        crop_frame.pack(fill=tk.X, side=tk.TOP)

        ttk.Label(crop_frame, text="边缘裁切(px):").pack(side=tk.LEFT)

        ttk.Label(crop_frame, text="上").pack(side=tk.LEFT, padx=(5, 0))
        ttk.Spinbox(crop_frame, from_=0, to=500, textvariable=self.crop_top, width=4).pack(side=tk.LEFT)

        ttk.Label(crop_frame, text="下").pack(side=tk.LEFT, padx=(5, 0))
        ttk.Spinbox(crop_frame, from_=0, to=500, textvariable=self.crop_bottom, width=4).pack(side=tk.LEFT)

        ttk.Label(crop_frame, text="左").pack(side=tk.LEFT, padx=(5, 0))
        ttk.Spinbox(crop_frame, from_=0, to=500, textvariable=self.crop_left, width=4).pack(side=tk.LEFT)

        ttk.Label(crop_frame, text="右").pack(side=tk.LEFT, padx=(5, 0))
        ttk.Spinbox(crop_frame, from_=0, to=500, textvariable=self.crop_right, width=4).pack(side=tk.LEFT)

        # 手动测试按钮
        ttk.Button(crop_frame, text="📸 刷新预览", command=self.preview_capture).pack(side=tk.LEFT, padx=15)
        # ------------------------

        self.lbl_image = ttk.Label(self.img_frame, text="等待选取窗口...", anchor="center", background="#333",
                                   foreground="#ccc")
        self.lbl_image.pack(expand=True, fill=tk.BOTH, padx=5, pady=5)

        # 差异度显示
        self.lbl_diff_val = ttk.Label(self.img_frame, text="视觉差异度(下1/3): 0.0", background="#eee", anchor="e")
        self.lbl_diff_val.pack(fill=tk.X, padx=2, pady=2)

        # 阶段总结列表
        summary_frame = ttk.LabelFrame(left_panel, text="📖 剧情阶段回顾 (自动生成)", padding=5)
        summary_frame.pack(fill=tk.BOTH, expand=True)
        self.txt_summary = scrolledtext.ScrolledText(summary_frame, height=10, font=("Microsoft YaHei", 9),
                                                     state='disabled')
        self.txt_summary.pack(fill=tk.BOTH, expand=True)

        # 右侧：实时单帧日志
        right_panel = ttk.LabelFrame(main_paned, text=" 实时单帧记录", width=500)
        main_paned.add(right_panel, weight=2)

        self.txt_log = scrolledtext.ScrolledText(right_panel, state='disabled', font=("Consolas", 10))
        self.txt_log.pack(expand=True, fill=tk.BOTH)

        # 3. 底部状态栏
        self.lbl_stats = ttk.Label(self.root, text="统计: -", padding=5, relief=tk.SUNKEN)
        self.lbl_stats.pack(fill=tk.X)

    # ================= 核心工具函数 =================

    def calculate_image_diff(self, img_new):
        """
        计算当前帧与上一帧的视觉差异度。
        仅检测画面下 1/3 区域，以极大提高对字幕变化的敏感度。
        """
        if self.last_pil_image is None:
            return 100.0  # 第一帧，差异最大

        try:
            # 1. 获取图像尺寸
            width, height = img_new.size

            # 2. 定义下 1/3 的裁切区域 (Left, Top, Right, Bottom)
            # 假设字幕通常在底部，专注检测这里可以忽略画面上方的背景微动，但敏锐捕捉字幕
            crop_top = int(height * (2 / 3))
            crop_box = (0, crop_top, width, height)

            # 3. 裁切并缩放进行比较
            img1_part = self.last_pil_image.crop(crop_box).resize((64, 20)).convert("RGB")  # 保持一定比例缩放
            img2_part = img_new.crop(crop_box).resize((64, 20)).convert("RGB")

            # 4. 计算差异图像
            diff_img = ImageChops.difference(img1_part, img2_part)

            # 5. 计算平均差异值 (0-255)
            stat = ImageStat.Stat(diff_img)
            diff_val = sum(stat.mean) / len(stat.mean)
            return diff_val
        except Exception as e:
            print(f"Diff calc error: {e}")
            return 100.0

    def log_frame_result(self, message, tag="INFO"):
        """记录单帧分析结果"""
        timestamp = datetime.datetime.now().strftime("%H:%M:%S")
        prefix = ""
        if tag == "SKIP":
            prefix = "⏭️ "
        elif tag == "AI":
            prefix = "🤖 "

        full_msg = f"[{timestamp}] {prefix}{message}\n"
        self._append_text(self.txt_log, full_msg)

        # 仅当 tag 为 AI 时才写入文件
        if self.log_filename and tag == "AI":
            with open(self.log_filename, "a", encoding="utf-8") as f:
                f.write(full_msg)

    def log_summary_result(self, message):
        """记录阶段回顾结果"""
        timestamp = datetime.datetime.now().strftime("%H:%M")
        full_msg = f"\n=== 阶段回顾 [{timestamp}] ===\n{message}\n=======================\n\n"
        self._append_text(self.txt_summary, full_msg)
        self.log_frame_result(f"【触发回顾】 {message[:30]}...", tag="INFO")
        if self.log_filename:
            with open(self.log_filename, "a", encoding="utf-8") as f:
                f.write(full_msg)

    def log_final_report(self, message):
        """记录最终解说"""
        self._append_text(self.txt_log, "\n\n★★★★★ 全片影视解说 ★★★★★\n" + message + "\n")
        if self.log_filename:
            with open(self.log_filename, "a", encoding="utf-8") as f:
                f.write("\n\n★★★★★ 全片影视解说 ★★★★★\n" + message)

    def _append_text(self, widget, text):
        widget.config(state='normal')
        widget.insert(tk.END, text)
        widget.see(tk.END)
        widget.config(state='disabled')

    def control_video(self, action="pause"):
        """尝试控制视频播放/暂停 (发送空格键)"""
        if not AUTO_PAUSE_VIDEO: return
        target_title = self.target_window_title.get()
        if not target_title or not gw: return
        try:
            wins = gw.getWindowsWithTitle(target_title)
            if wins:
                win = wins[0]
                if not win.isActive:
                    win.activate()
                    time.sleep(0.2)
                pyautogui.press('space')
                print(f"Video action: {action}")
        except Exception as e:
            print(f"Video control failed: {e}")

    # ================= 业务逻辑 =================

    def start_window_picker(self):
        if not gw:
            messagebox.showerror("错误", "未安装 pygetwindow")
            return
        self.lbl_status.config(text="请点击目标窗口...", foreground="blue")
        self.picker_win = tk.Toplevel(self.root)
        self.picker_win.attributes('-fullscreen', True)
        self.picker_win.attributes('-alpha', 0.3)
        self.picker_win.configure(bg='grey', cursor="crosshair")
        self.picker_win.bind('<Button-1>', self.on_picker_click)
        self.picker_win.bind('<Escape>', lambda e: self.picker_win.destroy())

    def on_picker_click(self, event):
        x, y = self.root.winfo_pointerx(), self.root.winfo_pointery()
        self.picker_win.destroy()
        self.root.update()
        try:
            windows = gw.getWindowsAt(x, y)
            if windows:
                for w in windows:
                    if "Video AI Analyzer" in w.title: continue
                    if w.title:
                        self.target_window_title.set(w.title)
                        self.lbl_status.config(text=f"已锁定: {w.title}", foreground="green")
                        self.preview_capture()
                        return
            self.lbl_status.config(text="未识别到窗口", foreground="red")
        except Exception as e:
            print(f"Pick error: {e}")

    def preview_capture(self):
        """不进行分析，仅刷新预览图以供调整裁切"""
        if not self.target_window_title.get():
            return
        img, _ = self.capture_screen_data()
        if img is None:
            self.lbl_status.config(text="获取预览失败，窗口可能已关闭或最小化", foreground="red")

    def start_analysis(self):
        if not self.target_window_title.get():
            messagebox.showerror("错误", "请先选择目标窗口！")
            return

        try:
            self.sampling_interval = float(self.spin_interval.get())
        except:
            self.sampling_interval = DEFAULT_INTERVAL

        start_time_str = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
        self.log_filename = f"movie_log_v4_{start_time_str}.txt"

        # 重置数据
        self.raw_frame_logs = []
        self.phase_summaries = []
        self.last_pil_image = None
        self.consecutive_skips = 0

        self.is_running = True
        self.btn_start.config(state=tk.DISABLED)
        self.btn_stop.config(state=tk.NORMAL)
        self.lbl_status.config(text="运行中", foreground="green")

        threading.Thread(target=self.analysis_loop, daemon=True).start()

    def stop_analysis_trigger(self):
        if self.is_running:
            self.is_running = False
            self.lbl_status.config(text="正在停止并生成最终报告...", foreground="orange")

    def capture_screen_data(self):
        """捕获屏幕，并根据裁切设置处理图像，返回 (PIL_Image, Base64_String)"""
        if not gw: return None, None
        try:
            windows = gw.getWindowsWithTitle(self.target_window_title.get())
            if windows:
                win = windows[0]

                # 获取用户设置的裁切值
                c_top = self.crop_top.get()
                c_bottom = self.crop_bottom.get()
                c_left = self.crop_left.get()
                c_right = self.crop_right.get()

                real_left = win.left + c_left
                real_top = win.top + c_top
                real_width = win.width - c_left - c_right
                real_height = win.height - c_top - c_bottom

                if real_width <= 10: real_width = 100
                if real_height <= 10: real_height = 100

                screenshot = pyautogui.screenshot(region=(real_left, real_top, real_width, real_height))

                # 保持原图用于比较
                original_img = screenshot.copy()

                # UI 显示用的缩略图
                img_display = screenshot.copy()
                img_display.thumbnail((380, 250))
                self.photo = ImageTk.PhotoImage(img_display)
                self.lbl_image.config(image=self.photo, text="")

                # LLM 用的 Base64
                screenshot.thumbnail((1024, 1024))
                buffered = io.BytesIO()
                screenshot.save(buffered, format="JPEG", quality=80)
                b64_str = f"data:image/jpeg;base64,{base64.b64encode(buffered.getvalue()).decode()}"

                return original_img, b64_str
        except Exception as e:
            print(f"Capture error: {e}")
        return None, None

    def call_llm(self, messages, max_tokens=200):
        payload = {
            "model": MODEL_ID,
            "messages": messages,
            "temperature": 0.6,
            "max_tokens": max_tokens
        }
        try:
            resp = requests.post(LLM_API_URL, json=payload, timeout=60)
            if resp.status_code == 200:
                return resp.json()['choices'][0]['message']['content']
        except Exception as e:
            print(f"LLM Error: {e}")
        return None

    # ================= 核心 AI 流程 (优化版) =================

    def analysis_loop(self):
        while self.is_running:
            loop_start = time.time()
            pil_img, img_b64 = self.capture_screen_data()

            should_analyze = False
            diff_val = 0.0
            current_loop_wait_setting = self.sampling_interval

            if pil_img and img_b64:
                if ENABLE_VISUAL_DEDUP:
                    diff_val = self.calculate_image_diff(pil_img)

                    diff_color = "red" if diff_val > SCENE_CHANGE_THRESHOLD else "green"
                    self.root.after(0, lambda v=diff_val, c=diff_color: self.lbl_diff_val.config(
                        text=f"视觉差异度(下1/3): {v:.2f} (阈值: {SCENE_CHANGE_THRESHOLD})", foreground=c
                    ))

                    if diff_val > SCENE_CHANGE_THRESHOLD or self.consecutive_skips >= MAX_SKIP_COUNT:
                        should_analyze = True
                        if self.consecutive_skips >= MAX_SKIP_COUNT:
                            self.log_frame_result("强制分析 (超时)", tag="INFO")
                        self.consecutive_skips = 0
                        self.last_pil_image = pil_img
                        current_loop_wait_setting = self.sampling_interval
                    else:
                        should_analyze = False
                        self.consecutive_skips += 1
                        self.log_frame_result(f"画面静止 (Diff: {diff_val:.1f})，延后0.5s检测...", tag="SKIP")
                        current_loop_wait_setting = 0.5
                else:
                    should_analyze = True
                    current_loop_wait_setting = self.sampling_interval

            if should_analyze and img_b64:
                frame_result = self.perform_single_frame_analysis(img_b64)
                if frame_result:
                    self.raw_frame_logs.append(frame_result)
                    self.log_frame_result(frame_result, tag="AI")
                    if len(self.raw_frame_logs) % SUMMARY_TRIGGER_COUNT == 0:
                        self.trigger_phase_summary_sequence()

            elapsed = time.time() - loop_start
            wait_time = max(0.1, current_loop_wait_setting - elapsed)

            self.root.after(0, lambda e=elapsed, w=wait_time: self.lbl_stats.config(
                text=f"已分析: {len(self.raw_frame_logs)}帧 | 阶段回顾: {len(self.phase_summaries)} | 耗时: {e:.2f}s | 下次: {w:.1f}s"
            ))

            time.sleep(wait_time)

        self.perform_final_summary_sequence()
        self.root.after(0, lambda: self.btn_start.config(state=tk.NORMAL))
        self.root.after(0, lambda: self.btn_stop.config(state=tk.DISABLED))
        self.lbl_status.config(text="已完成", foreground="gray")

    def perform_single_frame_analysis(self, img_b64):
        context_text = "【已知历史剧情(阶段回顾)】:\n" + (
            "\n".join(self.phase_summaries) if self.phase_summaries else "无")
        recent_frames = self.raw_frame_logs[-2:]
        context_text += "\n\n【最近2帧记录】:\n" + ("\n".join(recent_frames) if recent_frames else "无")

        messages = [
            {"role": "system", "content": PROMPT_SINGLE_FRAME},
            {"role": "user", "content": [
                {"type": "text", "text": context_text + "\n\n请分析下面这张图片："},
                {"type": "image_url", "image_url": {"url": img_b64}}
            ]}
        ]
        return self.call_llm(messages, max_tokens=150)

    def trigger_phase_summary_sequence(self):
        self.log_frame_result(">>> 触发阶段回顾，尝试暂停视频...", tag="INFO")
        self.control_video("pause")
        time.sleep(1.0)

        summary = self.perform_phase_summary()
        if summary:
            self.phase_summaries.append(summary)
            self.log_summary_result(summary)

        self.log_frame_result(">>> 回顾完成，恢复视频播放...", tag="INFO")
        self.control_video("play")

    def perform_phase_summary(self):
        context_text = "【已知历史剧情(阶段回顾)】:\n" + (
            "\n".join(self.phase_summaries) if self.phase_summaries else "无")
        recent_frames = self.raw_frame_logs[-10:]
        context_text += "\n\n【最近10帧详细记录】:\n" + ("\n".join(recent_frames) if recent_frames else "无")

        messages = [
            {"role": "system", "content": PROMPT_PHASE_SUMMARY},
            {"role": "user", "content": context_text + "\n\n请开始阶段回顾："}
        ]
        return self.call_llm(messages, max_tokens=300)

    def perform_final_summary_sequence(self):
        self.log_frame_result(">>> 正在进行最终结算...", tag="INFO")
        frames_since_last_summary = len(self.raw_frame_logs) % SUMMARY_TRIGGER_COUNT
        if frames_since_last_summary > 0:
            self.log_frame_result(f"补齐剩余 {frames_since_last_summary} 帧的阶段回顾...", tag="INFO")
            summary = self.perform_phase_summary()
            if summary:
                self.phase_summaries.append(summary)
                self.log_summary_result(summary)

        final_report = self.perform_final_summary()
        if final_report:
            self.log_final_report(final_report)
            messagebox.showinfo("完成", "全片解说已生成")

    def perform_final_summary(self):
        context_text = "【全片剧情线索(阶段回顾)】:\n"
        for i, s in enumerate(self.phase_summaries):
            context_text += f"阶段 {i + 1}: {s}\n"

        messages = [
            {"role": "system", "content": PROMPT_FINAL_SUMMARY},
            {"role": "user", "content": context_text + "\n\n请生成最终解说文案："}
        ]
        return self.call_llm(messages, max_tokens=2000)


if __name__ == "__main__":
    root = tk.Tk()
    app = VideoAnalyzerApp(root)

    root.mainloop()
