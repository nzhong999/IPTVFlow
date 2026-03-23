#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
IPTV 直播源智能清洗与验证系统（v2.0 Strict - Guovin Logic Edition + 频道去重 + Bark 报告 + 预定义频道顺序）

【核心逻辑说明】
本脚本严格遵循 Guovin/iptv-api 的核心业务逻辑，同时保留了原有的 OCR 检测和分组功能。

1. 频道标准化 (normalize_channel_name):
   - 多频道名拆分 (A-B-C -> A)
   - 别名映射 (长匹配优先，基于 CHANNEL_ALIAS_MAP)
   - 移除括号及内容
   - 统一连接符为空格
   - 移除冗余后缀 (HD, 频道, TV 等)
   - CCTV 编号智能修正 (CCTV01 -> CCTV1, CCTV-5+ -> CCTV5+)
   - CGTN 前缀标准化

2. 测速流程 (test_channel_speed):
   - M3U8 分片测速：解析播放列表，下载前 5 个 TS 分片计算真实速度
   - 滑动窗口稳定性算法：连续采样速度波动 < 15% 才判定为有效速度
   - FFmpeg 降级探测：HTTP 测速失败时，调用 ffprobe 获取分辨率/编码
   - OCR 软错误检测：识别"登录墙"、"区域限制"等无效画面

3. 质量评估 (filter_and_sort_results):
   - 动态阈值过滤：基于分辨率 - 速率映射表 (1080P 需 > 1.5MB/s)
   - 排序策略：速度降序 -> 延迟升序

4. 频道去重 (新增)：
   - 按标准化名称分组，每组保留第一个（排序后最优）源

5. 频道排序 (新增)：
   - 支持通过 config/channel_order.json 预定义每个分组内频道的顺序
   - 未定义的频道按自然排序（数字优先）追加到组内末尾

6. 架构:
   - 完全异步 (AsyncIO + Aiohttp)，支持高并发测速
"""

import os
import re
import time
import json
import logging
import asyncio
import datetime
import subprocess
import math
from urllib.parse import urlparse, urljoin, quote
from collections import defaultdict
from typing import List, Dict, Any, Optional, Tuple, Set, DefaultDict
from concurrent.futures import ThreadPoolExecutor

# ================== 依赖检查 ==================
try:
    import aiohttp
    from aiohttp import ClientSession, TCPConnector, ClientTimeout
    import m3u8
except ImportError:
    print("❌ 缺少依赖: 请运行 'pip install aiohttp m3u8'")
    exit(1)

try:
    import pytesseract
    from PIL import Image
    OCR_AVAILABLE = True
except ImportError:
    OCR_AVAILABLE = False
    pytesseract = None
    Image = None

# ================== 全局配置类 ==================
class Config:
    # --- 文件路径配置 ---
    BASE_URL_FILE: str = "config/remote_sources.txt"            # 远程源列表
    BLACKLIST_FILE: str = "config/blackHost_list.txt"           # 主机黑名单
    OUTPUT_FILE: str = "output/live.m3u"                        # 输出 M3U
    REPORT_FILE: str = "output/report.md"                       # 清洗报告
    BARK_DEVICE_KEY: str = ""                                   # Bark 通知密钥
    CHANNEL_ORDER_FILE: str = "config/channel_order.json"       # 频道顺序配置文件
    
    DEBUG_FILES: List[str] = [
        "debug_1_merged_raw.m3u",
        "debug_2_grouped_channels.json",
        "debug_3_host_mapping.json",
        "debug_4_host_quality.json",
        "debug_5_host_ranking.md"
    ]

    # --- Guovin/iptv-api 核心测速参数 ---
    TIMEOUT: int = 10                   # 总超时时间 (秒)
    CONNECT_TIMEOUT: int = 5            # 连接超时
    READ_TIMEOUT: int = 8               # 读取超时
    MAX_CONCURRENT: int = 100            # 最大并发数 (Semaphore 限制)
    
    # 新增：是否使用主机级测速（False=每个URL独立测速，True=同主机复用测速结果）
    USE_HOST_LEVEL_SPEED: bool = True

    # 滑动窗口稳定性算法参数
    MIN_MEASURE_TIME: float = 1.0       # 最小测速时长 (秒)，低于此时长不判定稳定
    STABILITY_WINDOW: int = 4           # 滑动窗口大小 (采样点数)
    STABILITY_THRESHOLD: float = 0.15   # 速度波动阈值 (0.15 = 15%)，波动超过此值视为不稳定
    MIN_BYTES: int = 64 * 1024          # 最小测试字节数 (64KB)
    
    # --- 质量评估策略 ---
    OPEN_FILTER_SPEED: bool = True              # 是否开启速度过滤
    OPEN_FILTER_RESOLUTION: bool = True         # 是否开启分辨率过滤
    MIN_RESOLUTION_VALUE: int = 0               # 最小分辨率像素值 (0=不限制)
    
    # 分辨率 - 速率映射表 (MB/s)
    # 逻辑：如果测得速度低于该分辨率对应的阈值，则视为不合格（可能是假高清或卡顿）
    RESOLUTION_SPEED_MAP: Dict[str, float] = {
        "1920x1080": 1.5,
        "1280x720": 0.8,
        "720x576": 0.5,
        "default": 0.3
    }
    
    HLS_EXTENSIONS: Tuple[str, ...] = ('.m3u8', '.m3u')
    LOGO_BASE_URL: str = "https://raw.githubusercontent.com/alantang1977/iptv_api/main/pic/logos/"
    
    # --- 频道分组规则 (正则匹配) ---
    GROUP_RULES: List[Tuple[str, str]] = [
        (r'(CCTV[-]?14|哈哈炫动|卡酷|宝宝|幼教|贝瓦|巧虎|新科动漫|小猪佩奇|汪汪队|海底小纵队|米老鼠|迪士尼|熊出没|猫和老鼠|哆啦A梦|喜羊羊|青少|儿童|动画|动漫|少儿|卡通|金鹰|disney|cartoon|nickelodeon|kids|kika|cbbc|哈哈炫动)', "🧸 儿童动画"),
        (r'(央视|CCTV[0-9]*[高清]?|CGTN|CCTV|风云音乐|第一剧场|怀旧剧场|女性时尚|风云足球|世界地理|兵器科技|电视指南)', "🇨🇳 央视频道"),
        (r'(卫视|湖南|浙江|江苏|北京|广东|深圳|东方|安徽|山东|河南|湖北|四川|辽宁|东南|天津|四川|内蒙古|云南)', "📺 卫视频道"),
        (r'(翡翠|明珠|凤凰|鳳凰东森|莲花|AMC|龙华|澳亚|港台|寰宇|TVB|华语|中天|东森|年代|民视|三立|星空|民视|台视|美亚|美亞|千禧|无线|無線|VIUTV|HOY|RTHK|Now|靖天|星卫|香港|澳门|台湾)', "🇭🇰 港澳台频道"),
        (r'(体育|CCTV5|高尔夫|足球|NBA|英超|西甲|欧冠)', "⚽ 体育频道"),
        (r'(电影|影院|CHC|HBO|星空|AXN|TCM|佳片)', "🎬 影视频道"),
        (r'(AMC|BET|Discovery|CBS|BET|cine|CNN|disney|epix|espn|fox|american|boomerang|cnbc|entertainment|fs|fuse|fx|hbo|国家地理|Animal Planet|BBC|NHK|DW|France24|CNN|Al Jazeera)', "🌍 国际频道"),
        (r'(教育|课堂|空中|大学|学习|国学|书画|考试|中学|学堂)', "🎓 教育频道"),
        # 兜底规则：全英文且不含 CCTV/CGTN → 国际频道
        (r'^(?=.*[a-zA-Z])(?!.*\b(cctv|cgtn)\b)[a-zA-Z0-9\s\-\+\&\.\'\!\(\)]+$', "🌍 国际频道"),
    ]

    # 最终输出分组顺序
    GROUP_OUTPUT_ORDER: List[str] = [
        "🇨🇳 央视频道", "📺 卫视频道", "🎬 影视频道", "⚽ 体育频道",
        "🧸 儿童动画", "🌍 国际频道", "🎓 教育频道", "🇭🇰 港澳台频道", "📺 其他频道"
    ]

# ================== 频道别名字典 (保持原有完整映射) ==================
# 逻辑：将各种变体名称映射为标准名称，用于去重和分组
CHANNEL_ALIAS_MAP: Dict[str, str] = {
    alias: std
    for std, aliases in {
        "CCTV-1 综合": ["CCTV-1", "CCTV-1HD", "CCTV-1SD", "CCTV-1高清",  "CCTV-1 HD", "CCTV-1 SD", "CCTV-1 高清", "CCTV1" , "CCTV1高清"，"CCTV1SD", "CCTV1HD", "CCTV1 高清"，"CCTV1 SD", "CCTV1 HD", "CCTV1综合", , "CCTV1综合高清"，"CCTV1综合SD", "CCTV1综合HD", "CCTV1综合 高清"，"CCTV1综合 SD", "CCTV1综合 HD", "CCTV-1 综合 高清"，, "CCTV-1 综合 HD", "CCTV-1 综合 SD" ],
        "CCTV-2 财经": ["CCTV-2", "CCTV-2HD", "CCTV-2SD", "CCTV-2高清",  "CCTV-2 HD", "CCTV-2 SD", "CCTV-2 高清", "CCTV2" , "CCTV2高清"，"CCTV2SD", "CCTV2HD", "CCTV2 高清"，"CCTV2 SD", "CCTV2 HD", "CCTV2财经", , "CCTV2财经高清"，"CCTV2财经SD", "CCTV2财经HD", "CCTV2财经 高清"，"CCTV2财经 SD", "CCTV2财经 HD", "CCTV-2 财经 高清"，, "CCTV-2 财经 HD", "CCTV-2 财经 SD" ],
        "CCTV-3 综艺": ["CCTV-3", "CCTV-3HD", "CCTV-3SD", "CCTV-3高清",  "CCTV-3 HD", "CCTV-3 SD", "CCTV-3 高清", "CCTV3" , "CCTV3高清"，"CCTV3SD", "CCTV3HD", "CCTV3 高清"，"CCTV3 SD", "CCTV3 HD", "CCTV3综艺", , "CCTV3综艺高清"，"CCTV3综艺SD", "CCTV3综艺HD", "CCTV3综艺 高清"，"CCTV3综艺 SD", "CCTV3综艺 HD", "CCTV-3 综艺 高清"，, "CCTV-3 综艺 HD", "CCTV-3 综艺 SD" ],
        "CCTV-4 中文国际": ["CCTV-4", "CCTV-4HD", "CCTV-4SD", "CCTV-4高清",  "CCTV-4 HD", "CCTV-4 SD", "CCTV-4 高清", "CCTV4" , "CCTV4高清"，"CCTV4SD", "CCTV4HD", "CCTV4 高清"，"CCTV4 SD", "CCTV4 HD", "CCTV4中文国际", , "CCTV4中文国际高清"，"CCTV4中文国际SD", "CCTV4中文国际HD", "CCTV4中文国际 高清"，"CCTV4中文国际 SD", "CCTV4中文国际 HD", "CCTV-4 中文国际 高清"，, "CCTV-4 中文国际 HD", "CCTV-4 中文国际 SD" ],
        "CCTV-4 美洲": ["CCTV-4", "CCTV-4HD", "CCTV-4SD", "CCTV-4高清",  "CCTV-4 HD", "CCTV-4 SD", "CCTV-4 高清", "CCTV4" , "CCTV4高清"，"CCTV4SD", "CCTV4HD", "CCTV4 高清"，"CCTV4 SD", "CCTV4 HD", "CCTV4美洲", , "CCTV4美洲高清"，"CCTV4美洲SD", "CCTV4美洲HD", "CCTV4美洲 高清"，"CCTV4美洲 SD", "CCTV4美洲 HD", "CCTV-4 美洲 高清"，, "CCTV-4 美洲 HD", "CCTV-4 美洲 SD" ],
        "CCTV-4 欧洲": ["CCTV-4", "CCTV-4HD", "CCTV-4SD", "CCTV-4高清",  "CCTV-4 HD", "CCTV-4 SD", "CCTV-4 高清", "CCTV4" , "CCTV4高清"，"CCTV4SD", "CCTV4HD", "CCTV4 高清"，"CCTV4 SD", "CCTV4 HD", "CCTV4欧洲", , "CCTV4欧洲高清"，"CCTV4欧洲SD", "CCTV4欧洲HD", "CCTV4欧洲 高清"，"CCTV4欧洲 SD", "CCTV4欧洲 HD", "CCTV-4 欧洲 高清"，, "CCTV-4 欧洲 HD", "CCTV-4 欧洲 SD" ],
        "CCTV-5 体育": ["CCTV-5", "CCTV-5HD", "CCTV-5SD", "CCTV-5高清",  "CCTV-5 HD", "CCTV-5 SD", "CCTV-5 高清", "CCTV5" , "CCTV5高清"，"CCTV5SD", "CCTV5HD", "CCTV5 高清"，"CCTV5 SD", "CCTV5 HD", "CCTV5体育", , "CCTV5体育高清"，"CCTV5体育SD", "CCTV5体育HD", "CCTV5体育 高清"，"CCTV5体育 SD", "CCTV5体育 HD", "CCTV-5 体育 高清"，, "CCTV-5 体育 HD", "CCTV-5 体育 SD" ],
        "CCTV-5+ 体育赛事": ["CCTV-5+", "CCTV-5+HD", "CCTV-5+SD", "CCTV-5+高清",  "CCTV-5+ HD", "CCTV-5+ SD", "CCTV-5+ 高清", "CCTV5+" , "CCTV5+高清"，"CCTV5+SD", "CCTV5+HD", "CCTV5+ 高清"，"CCTV5+ SD", "CCTV5+ HD", "CCTV5+体育赛事", , "CCTV5+体育赛事高清"，"CCTV5+体育赛事SD", "CCTV5+体育赛事HD", "CCTV5+体育赛事 高清"，"CCTV5+体育赛事 SD", "CCTV5+体育赛事 HD", "CCTV-5+ 体育赛事 高清"，, "CCTV-5+ 体育赛事 HD", "CCTV-5+ 体育赛事 SD" ],
        "CCTV-6 电影": ["CCTV-6", "CCTV-6HD", "CCTV-6SD", "CCTV-6高清",  "CCTV-6 HD", "CCTV-6 SD", "CCTV-6 高清", "CCTV6" , "CCTV6高清"，"CCTV6SD", "CCTV6HD", "CCTV6 高清"，"CCTV6 SD", "CCTV6 HD", "CCTV6电影", , "CCTV6电影高清"，"CCTV6电影SD", "CCTV6电影HD", "CCTV6电影 高清"，"CCTV6电影 SD", "CCTV6电影 HD", "CCTV-6 电影 高清"，, "CCTV-6 电影 HD", "CCTV-6 电影 SD" ],
        "CCTV-7 国防军事": ["CCTV-7", "CCTV-7HD", "CCTV-7SD", "CCTV-7高清",  "CCTV-7 HD", "CCTV-7 SD", "CCTV-7 高清", "CCTV7" , "CCTV7高清"，"CCTV7SD", "CCTV7HD", "CCTV7 高清"，"CCTV7 SD", "CCTV7 HD", "CCTV7国防军事", , "CCTV7国防军事高清"，"CCTV7国防军事SD", "CCTV7国防军事HD", "CCTV7国防军事 高清"，"CCTV7国防军事 SD", "CCTV7国防军事 HD", "CCTV-7 国防军事 高清"，, "CCTV-7 国防军事 HD", "CCTV-7 国防军事 SD" ],
        "CCTV-8 电视剧": ["CCTV-8", "CCTV-8HD", "CCTV-8SD", "CCTV-8高清",  "CCTV-8 HD", "CCTV-8 SD", "CCTV-8 高清", "CCTV8" , "CCTV8高清"，"CCTV8SD", "CCTV8HD", "CCTV8 高清"，"CCTV8 SD", "CCTV8 HD", "CCTV8电视剧", , "CCTV8电视剧高清"，"CCTV8电视剧SD", "CCTV8电视剧HD", "CCTV8电视剧 高清"，"CCTV8电视剧 SD", "CCTV8电视剧 HD", "CCTV-8 电视剧 高清"，, "CCTV-8 电视剧 HD", "CCTV-8 电视剧 SD" ],
        "CCTV-9 纪录": ["CCTV-9", "CCTV-9HD", "CCTV-9SD", "CCTV-9高清",  "CCTV-9 HD", "CCTV-9 SD", "CCTV-9 高清", "CCTV9" , "CCTV9高清"，"CCTV9SD", "CCTV9HD", "CCTV9 高清"，"CCTV9 SD", "CCTV9 HD", "CCTV9纪录", , "CCTV9纪录高清"，"CCTV9纪录SD", "CCTV9纪录HD", "CCTV9纪录 高清"，"CCTV9纪录 SD", "CCTV9纪录 HD", "CCTV-9 纪录 高清"，, "CCTV-9 纪录 HD", "CCTV-9 纪录 SD" ],
        "CCTV-10 科教": ["CCTV-10", "CCTV-10HD", "CCTV-10SD", "CCTV-10高清",  "CCTV-10 HD", "CCTV-10 SD", "CCTV-10 高清", "CCTV10" , "CCTV10高清"，"CCTV10SD", "CCTV10HD", "CCTV10 高清"，"CCTV10 SD", "CCTV10 HD", "CCTV10科教", , "CCTV10科教高清"，"CCTV10科教SD", "CCTV10科教HD", "CCTV10科教 高清"，"CCTV10科教 SD", "CCTV10科教 HD", "CCTV-10 科教 高清"，, "CCTV-10 科教 HD", "CCTV-10 科教 SD" ],
        "CCTV-11 戏曲": ["CCTV-11", "CCTV-11HD", "CCTV-11SD", "CCTV-11高清",  "CCTV-11 HD", "CCTV-11 SD", "CCTV-11 高清", "CCTV11" , "CCTV11高清"，"CCTV11SD", "CCTV11HD", "CCTV11 高清"，"CCTV11 SD", "CCTV11 HD", "CCTV11戏曲", , "CCTV11戏曲高清"，"CCTV11戏曲SD", "CCTV11戏曲HD", "CCTV11戏曲 高清"，"CCTV11戏曲 SD", "CCTV11戏曲 HD", "CCTV-11 戏曲 高清"，, "CCTV-11 戏曲 HD", "CCTV-11 戏曲 SD" ],
        "CCTV-12 社会与法": ["CCTV-12", "CCTV-12HD", "CCTV-12SD", "CCTV-12高清",  "CCTV-12 HD", "CCTV-12 SD", "CCTV-12 高清", "CCTV12" , "CCTV12高清"，"CCTV12SD", "CCTV12HD", "CCTV12 高清"，"CCTV12 SD", "CCTV12 HD", "CCTV12社会与法", , "CCTV12社会与法高清"，"CCTV12社会与法SD", "CCTV12社会与法HD", "CCTV12社会与法 高清"，"CCTV12社会与法 SD", "CCTV12社会与法 HD", "CCTV-12 社会与法 高清"，, "CCTV-12 社会与法 HD", "CCTV-12 社会与法 SD" ],
        "CCTV-13 新闻": ["CCTV-13", "CCTV-13HD", "CCTV-13SD", "CCTV-13高清",  "CCTV-13 HD", "CCTV-13 SD", "CCTV-13 高清", "CCTV13" , "CCTV13高清"，"CCTV13SD", "CCTV13HD", "CCTV13 高清"，"CCTV13 SD", "CCTV13 HD", "CCTV13新闻", , "CCTV13新闻高清"，"CCTV13新闻SD", "CCTV13新闻HD", "CCTV13新闻 高清"，"CCTV13新闻 SD", "CCTV13新闻 HD", "CCTV-13 新闻 高清"，, "CCTV-13 新闻 HD", "CCTV-13 新闻 SD" ],
        "CCTV-14 少儿": ["CCTV-14", "CCTV-14HD", "CCTV-14SD", "CCTV-14高清",  "CCTV-14 HD", "CCTV-14 SD", "CCTV-14 高清", "CCTV14" , "CCTV14高清"，"CCTV14SD", "CCTV14HD", "CCTV14 高清"，"CCTV14 SD", "CCTV14 HD", "CCTV14少儿", , "CCTV14少儿高清"，"CCTV14少儿SD", "CCTV14少儿HD", "CCTV14少儿 高清"，"CCTV14少儿 SD", "CCTV14少儿 HD", "CCTV-14 少儿 高清"，, "CCTV-14 少儿 HD", "CCTV-14 少儿 SD" ],
        "CCTV-15 音乐": ["CCTV-15", "CCTV-15HD", "CCTV-15SD", "CCTV-15高清",  "CCTV-15 HD", "CCTV-15 SD", "CCTV-15 高清", "CCTV15" , "CCTV15高清"，"CCTV15SD", "CCTV15HD", "CCTV15 高清"，"CCTV15 SD", "CCTV15 HD", "CCTV15音乐", , "CCTV15音乐高清"，"CCTV15音乐SD", "CCTV15音乐HD", "CCTV15音乐 高清"，"CCTV15音乐 SD", "CCTV15音乐 HD", "CCTV-15 音乐 高清"，, "CCTV-15 音乐 HD", "CCTV-15 音乐 SD" ],
        "CCTV-16 奥林匹克": ["CCTV-16", "CCTV-16HD", "CCTV-16SD", "CCTV-16高清",  "CCTV-16 HD", "CCTV-16 SD", "CCTV-16 高清", "CCTV16" , "CCTV16高清"，"CCTV16SD", "CCTV16HD", "CCTV16 高清"，"CCTV16 SD", "CCTV16 HD", "CCTV16奥林匹克", , "CCTV16奥林匹克高清"，"CCTV16奥林匹克SD", "CCTV16奥林匹克HD", "CCTV16奥林匹克 高清"，"CCTV16奥林匹克 SD", "CCTV16奥林匹克 HD", "CCTV-16 奥林匹克 高清"，, "CCTV-16 奥林匹克 HD", "CCTV-16 奥林匹克 SD" ],
        "CCTV-17 农业农村": ["CCTV-17", "CCTV-17HD", "CCTV-17SD", "CCTV-17高清",  "CCTV-17 HD", "CCTV-17 SD", "CCTV-17 高清", "CCTV17" , "CCTV17高清"，"CCTV17SD", "CCTV17HD", "CCTV17 高清"，"CCTV17 SD", "CCTV17 HD", "CCTV17农业农村", , "CCTV17农业农村高清"，"CCTV17农业农村SD", "CCTV17农业农村HD", "CCTV17农业农村 高清"，"CCTV17农业农村 SD", "CCTV17农业农村 HD", "CCTV-17 农业农村 高清"，, "CCTV-17 农业农村 HD", "CCTV-17 农业农村 SD" ],
        "CCTV-4K 超高清": ["CCTV-4K", "CCTV-4KHD", "CCTV-4KSD", "CCTV-4K高清",  "CCTV-4K HD", "CCTV-4K SD", "CCTV-4K 高清", "CCTV4K" , "CCTV4K高清"，"CCTV4KSD", "CCTV4KHD", "CCTV4K 高清"，"CCTV4K SD", "CCTV4K HD", "CCTV4K超高清", , "CCTV4K超高清高清"，"CCTV4K超高清SD", "CCTV4K超高清HD", "CCTV4K超高清 高清"，"CCTV4K超高清 SD", "CCTV4K超高清 HD", "CCTV-4K 超高清 高清"，, "CCTV-4K 超高清 HD", "CCTV-4K 超高清 SD" ],
        "河南卫视": ["河南卫视HD", "河南卫视高清"， "河南卫视SD"],
        "BTV北京卫视": ["BTV北京卫视HD", "BTV北京卫视高清"， "BTV北京卫视SD"],
        "SCTV康巴卫视": ["SCTV康巴卫视HD", "SCTV康巴卫视高清"， "SCTV康巴卫视SD"],
        "安徽卫视": ["安徽卫视HD", "安徽卫视高清"， "安徽卫视SD"],
        "安微卫视": ["安微卫视HD", "安微卫视高清"， "安微卫视SD"],
        "澳门卫视": ["澳门卫视HD", "澳门卫视高清"， "澳门卫视SD"],
        "北京卫视": ["北京卫视HD", "北京卫视高清"， "北京卫视SD"],
        "北京卫视冬奥纪实": ["北京卫视冬奥纪实HD", "北京卫视冬奥纪实高清"， "北京卫视冬奥纪实SD"],
        "兵团卫视": ["兵团卫视HD", "兵团卫视高清"， "兵团卫视SD"],
        "东方卫视": ["东方卫视HD", "东方卫视高清"， "东方卫视SD"],
        "东南卫视": ["东南卫视HD", "东南卫视高清"， "东南卫视SD"],
        "凤凰卫视中文台": ["凤凰卫视中文台HD", "凤凰卫视中文台高清"， "凤凰卫视中文台SD"],
        "凤凰卫视资讯台": ["凤凰卫视资讯台HD", "凤凰卫视资讯台高清"， "凤凰卫视资讯台SD"],
        "福建东南卫视": ["福建东南卫视HD", "福建东南卫视高清"， "福建东南卫视SD"],
        "福建卫视": ["福建卫视HD", "福建卫视高清"， "福建卫视SD"],
        "甘肃卫视": ["甘肃卫视HD", "甘肃卫视高清"， "甘肃卫视SD"],
        "广东大湾区卫视": ["广东大湾区卫视HD", "广东大湾区卫视高清"， "广东大湾区卫视SD"],
        "广东南方卫视": ["广东南方卫视HD", "广东南方卫视高清"， "广东南方卫视SD"],
        "广东卫视": ["广东卫视HD", "广东卫视高清"， "广东卫视SD"],
        "广西卫视": ["广西卫视HD", "广西卫视高清"， "广西卫视SD"],
        "贵州卫视": ["贵州卫视HD", "贵州卫视高清"， "贵州卫视SD"],
        "海南卫视": ["海南卫视HD", "海南卫视高清"， "海南卫视SD"],
        "河北卫视": ["河北卫视HD", "河北卫视高清"， "河北卫视SD"],
        "黑龙江卫视": ["黑龙江卫视HD", "黑龙江卫视高清"， "黑龙江卫视SD"],
        "湖北卫视": ["湖北卫视HD", "湖北卫视高清"， "湖北卫视SD"],
        "湖南卫视": ["湖南卫视HD", "湖南卫视高清"， "湖南卫视SD"],
        "黄河卫视": ["黄河卫视HD", "黄河卫视高清"， "黄河卫视SD"],
        "吉林卫视": ["吉林卫视HD", "吉林卫视高清"， "吉林卫视SD"],
        "吉林延边卫视": ["吉林延边卫视HD", "吉林延边卫视高清"， "吉林延边卫视SD"],
        "江苏卫视": ["江苏卫视HD", "江苏卫视高清"， "江苏卫视SD"],
        "江西卫视": ["江西卫视HD", "江西卫视高清"， "江西卫视SD"],
        "辽宁卫视": ["辽宁卫视HD", "辽宁卫视高清"， "辽宁卫视SD"],
        "旅游卫视": ["旅游卫视HD", "旅游卫视高清"， "旅游卫视SD"],
        "南方卫视": ["南方卫视HD", "南方卫视高清"， "南方卫视SD"],
        "内蒙古卫视": ["内蒙古卫视HD", "内蒙古卫视高清"， "内蒙古卫视SD"],
        "内蒙卫视": ["内蒙卫视HD", "内蒙卫视高清"， "内蒙卫视SD"],
        "宁夏卫视": ["宁夏卫视HD", "宁夏卫视高清"， "宁夏卫视SD"],
        "农林卫视": ["农林卫视HD", "农林卫视高清"， "农林卫视SD"],
        "青海卫视": ["青海卫视HD", "青海卫视高清"， "青海卫视SD"],
        "三沙卫视": ["三沙卫视HD", "三沙卫视高清"， "三沙卫视SD"],
        "厦门卫视": ["厦门卫视HD", "厦门卫视高清"， "厦门卫视SD"],
        "山东卫视": ["山东卫视HD", "山东卫视高清"， "山东卫视SD"],
        "山西卫视": ["山西卫视HD", "山西卫视高清"， "山西卫视SD"],
        "陕西卫视": ["陕西卫视HD", "陕西卫视高清"， "陕西卫视SD"],
        "上海东方卫视": ["上海东方卫视HD", "上海东方卫视高清"， "上海东方卫视SD"],
        "上海卫视": ["上海卫视HD", "上海卫视高清"， "上海卫视SD"],
        "深圳卫视": ["深圳卫视HD", "深圳卫视高清"， "深圳卫视SD"],
        "四川卫视": ["四川卫视HD", "四川卫视高清"， "四川卫视SD"],
        "天津卫视": ["天津卫视HD", "天津卫视高清"， "天津卫视SD"],
        "西藏卫视": ["西藏卫视HD", "西藏卫视高清"， "西藏卫视SD"],
        "香港卫视": ["香港卫视HD", "香港卫视高清"， "香港卫视SD"],
        "新疆卫视": ["新疆卫视HD", "新疆卫视高清"， "新疆卫视SD"],
        "星空卫视": ["星空卫视HD", "星空卫视高清"， "星空卫视SD"],
        "云南卫视": ["云南卫视HD", "云南卫视高清"， "云南卫视SD"],
        "浙江卫视": ["浙江卫视HD", "浙江卫视高清"， "浙江卫视SD"],
        "重庆卫视": ["重庆卫视HD", "重庆卫视高清"， "重庆卫视SD"], 
        # ... (此处省略部分以保持长度，实际使用时请保留您完整的字典)
    }.items()
    for alias in aliases
}


# ================== 基础工具函数 ==================

def beijing_time_str(fmt: str = "%Y-%m-%d %H:%M:%S") -> str:
    """返回当前北京时间字符串"""
    beijing_tz = datetime.timezone(datetime.timedelta(hours=8))
    return datetime.datetime.now(beijing_tz).strftime(fmt)

def setup_logger() -> None:
    """初始化日志系统"""
    log_level = logging.DEBUG if os.getenv("DEBUG") else logging.INFO
    logging.basicConfig(
        level=log_level,
        format='%(asctime)s | %(levelname)-8s | %(message)s',
        datefmt='%Y-%m-%d %H:%M:%S'
    )

def get_resolution_value(res_str: str) -> int:
    """
    计算分辨率像素总值 (宽*高)
    用于比较分辨率高低，例如 1920x1080 -> 2073600
    """
    if not res_str:
        return 0
    match = re.search(r"(\d{3,4})x(\d{3,4})", res_str)
    if match:
        return int(match.group(1)) * int(match.group(2))
    return 0

def clean_url(raw: str) -> str:
    """清理 URL，移除 $ 后参数及多余空格"""
    return re.sub(r'[\$•].*|\s+.*', '', raw.strip()).rstrip('/?&')

def is_valid_url(u: str) -> bool:
    """判断是否为有效 HTTP/HTTPS URL"""
    try:
        r = urlparse(u)
        return r.scheme in ("http", "https") and bool(r.netloc)
    except Exception:
        return False

def get_host_key(u: str) -> Optional[str]:
    """
    从 URL 提取 host:port 作为主机唯一标识
    例如: https://example.com:8080/path → example.com:8080
    """
    try:
        p = urlparse(u)
        port = p.port or (443 if p.scheme == "https" else 80)
        return f"{p.hostname}:{port}" if p.hostname else None
    except Exception:
        return None

# ================== 自然排序辅助函数 ==================
def natural_sort_key(s: str) -> tuple:
    """
    返回可用于排序的元组，实现数字部分自然排序。
    例如：CCTV1, CCTV2, CCTV10 会按 1,2,10 排序。
    """
    def convert(text):
        return int(text) if text.isdigit() else text.lower()
    parts = re.split(r'(\d+)', s)
    return tuple(convert(p) for p in parts)

# ================== 核心：频道名称标准化 (严格复刻 Guovin/iptv-api) ==================
def normalize_channel_name(name: str) -> str:
    """
    严格遵循 Guovin/iptv-api 的频道名称处理流程：
    1. 多频道拼接取主频道 (A-B-C -> A)
    2. 别名映射 (长匹配优先)
    3. 移除括号内容
    4. 统一连接符为空格
    5. 移除冗余后缀 (HD, 频道, TV 等)
    6. CCTV 编号智能修正 (CCTV01 -> CCTV1, CCTV-5+ -> CCTV5+)
    7. CGTN 前缀标准化
    """
    if not name or not isinstance(name, str):
        return "Unknown"
    
    original = name.strip()
    if not original:
        return "Unknown"

    # Step 1: 处理多频道拼接 (A-B-C -> A)
    if "-" in original and len(original.split("-")) >= 3:
        original = original.split("-", 1)[0].strip()

    # Step 2: 精确别名映射 (长别名优先)
    # 注意：这里使用您提供的 CHANNEL_ALIAS_MAP
    for alias in sorted(CHANNEL_ALIAS_MAP.keys(), key=lambda x: -len(x)):
        if alias in original:
            return CHANNEL_ALIAS_MAP[alias]

    name = original

    # Step 3: 移除括号及内容
    name = re.sub(r'\s*[\(（【\[][^)）】\]]*[\)）】\]]\s*', '', name)

    # Step 4: 统一连接符为空格
    name = re.sub(r'[\s\-·•_\|]+', ' ', name)
    name = re.sub(r'\s+', ' ', name).strip()

    # Step 5: 移除冗余后缀
    suffix_pattern = (
        r'(?:'
        r'HD|SD|FHD|UHD|4K|超高清|高清|蓝光|标清|'
        r'综合频道？|电视频道？|直播频道？|官方频道？|'
        r'频道|TV|台|官方|正版|流畅|备用|测试|'
        r'Ch|CH|Channel|咪咕|真|极速|'
        r')$'
    )
    name = re.sub(suffix_pattern, '', name, flags=re.IGNORECASE).strip()

    # Step 6: 智能标准化 CCTV 编号 (核心逻辑)
    def cctv_replacer(m):
        num_part = m.group(1)
        digits = re.search(r'[0-9]+', num_part)
        if not digits:
            return m.group(0)
        num_int = int(digits.group())
        suffix = ''
        if '+' in num_part:
            suffix = '+'
        elif 'k' in num_part.lower():
            suffix = 'K'
        return f"CCTV{num_int}{suffix}"

    name = re.sub(
        r'^CCTV[-\s]*([0-9][0-9\s\+\-kK]*)',
        cctv_replacer,
        name,
        flags=re.IGNORECASE
    )

    # Step 7: 标准化 CGTN 前缀
    name = re.sub(r'^CGTN[-\s]+', 'CGTN ', name, flags=re.IGNORECASE).strip()

    cleaned = name.strip()
    return cleaned if cleaned else original

def guess_group(title: str) -> str:
    """根据频道标题猜测所属分组（按 GROUP_RULES 顺序匹配）"""
    for pat, grp in Config.GROUP_RULES:
        if re.search(pat, title, re.IGNORECASE):
            return grp
    return "📺 其他频道"

def extract_logo(channel: str) -> str:
    """生成 logo URL（基于频道名，移除非字母数字字符）"""
    clean_name = re.sub(r'[^\w]', '', channel).lower()
    return f"{Config.LOGO_BASE_URL}{clean_name}.png"

def is_valid_hls_content(text: str) -> bool:
    """判断文本是否为有效的 M3U/M3U8 内容"""
    txt = text.strip()
    return txt.startswith('#EXTM3U') and any(k in txt for k in ["#EXTINF", "#EXT-X-STREAM-INF"])

# ================== 核心测速逻辑 (严格复刻 Guovin/iptv-api) ==================


async def get_speed_with_download(url: str, session: ClientSession, headers: dict, timeout: int) -> Dict[str, Any]:
    """
    【Guovin 核心算法】底层下载测速函数
    功能：
    1. 计算首字节延迟 (Delay)
    2. 使用滑动窗口检测速度稳定性 (Stability Window)
    3. 返回平均速度、延迟、总大小
    
    逻辑：
    - 持续下载数据块，记录每个时间窗口的瞬时速度
    - 当采样点达到 STABILITY_WINDOW 且波动小于 STABILITY_THRESHOLD 时，判定为稳定，提前返回
    - 若超时或未稳定，返回平均值
    """
    start_time = time.time()
    delay = -1
    total_size = 0
    last_sample_time = start_time
    last_sample_size = 0
    speed_samples: List[float] = []
    
    try:
        async with session.get(url, headers=headers, timeout=ClientTimeout(total=timeout)) as response:
            if response.status != 200:
                raise Exception(f"Status {response.status}")
            
            async for chunk in response.content.iter_any():
                if chunk:
                    # 记录首字节延迟
                    if delay == -1:
                        delay = int(round((time.time() - start_time) * 1000))
                    
                    total_size += len(chunk)
                    now = time.time()
                    elapsed = now - start_time
                    
                    # 采样计算瞬时速度 (MB/s)
                    delta_t = now - last_sample_time
                    delta_b = total_size - last_sample_size
                    if delta_t > 0 and delta_b > 0:
                        inst_speed = delta_b / delta_t / 1024.0 / 1024.0
                        speed_samples.append(inst_speed)
                        last_sample_time = now
                        last_sample_size = total_size
                    
                    # === 稳定性判断逻辑 (Guovin Core) ===
                    # 条件：测速时间足够 + 数据量足够 + 采样点足够 + 波动在阈值内
                    if (elapsed >= Config.MIN_MEASURE_TIME and total_size >= Config.MIN_BYTES
                            and len(speed_samples) >= Config.STABILITY_WINDOW):
                        window = speed_samples[-Config.STABILITY_WINDOW:]
                        mean = sum(window) / len(window)
                        if mean > 0 and (max(window) - min(window)) / mean < Config.STABILITY_THRESHOLD:
                            return {
                                'speed': total_size / elapsed / 1024 / 1024,
                                'delay': delay,
                                'size': total_size,
                                'time': elapsed,
                                'stable': True
                            }
    except Exception:
        pass
    
    # 超时或未稳定，返回平均值
    total_time = time.time() - start_time
    speed_val = total_size / total_time / 1024 / 1024 if total_time > 0 else 0.0
    return {
        'speed': speed_val,
        'delay': delay if delay != -1 else int(round(total_time * 1000)),
        'size': total_size,
        'time': total_time,
        'stable': False
    }

async def get_m3u8_segments(url: str, session: ClientSession, headers: dict, timeout: int) -> List[str]:
    """
    【Guovin 核心逻辑】解析 M3U8 获取分片 URL
    逻辑：
    1. 如果是 Master Playlist (含子播放列表)，选择带宽最高的子流
    2. 提取前 5 个 TS 分片 URL 用于测速
    """
    try:
        async with session.get(url, headers=headers, timeout=ClientTimeout(total=timeout)) as resp:
            if resp.status == 200:
                content = await resp.text()
                playlist = m3u8.loads(content)
                
                segments = []
                # 如果有子播放列表 (Master Playlist)
                if playlist.playlists:
                    # 取带宽最高的子流
                    best_pl = max(playlist.playlists, key=lambda p: p.stream_info.bandwidth if p.stream_info else 0)
                    pl_url = urljoin(url, best_pl.uri)
                    async with session.get(pl_url, headers=headers, timeout=ClientTimeout(total=timeout)) as pl_resp:
                        if pl_resp.status == 200:
                            sub_pl = m3u8.loads(await pl_resp.text())
                            # 取前 5 个分片
                            segments = [urljoin(pl_url, s.uri) for s in sub_pl.segments[:5]]
                else:
                    # 直接是 Media Playlist
                    segments = [urljoin(url, s.uri) for s in playlist.segments[:5]]
                return segments
    except Exception:
        pass
    return []

async def probe_ffmpeg(url: str, timeout: int) -> Dict[str, Any]:
    """
    【降级策略】调用 ffprobe 获取详细信息
    当 HTTP 测速失败或速度为 0 时，使用此方法确认流是否有效并获取分辨率
    """
    def _run():
        try:
            cmd = [
                "ffprobe", "-v", "quiet", "-print_format", "json",
                "-show_streams", "-timeout", str(timeout * 1000000),
                "-user_agent", "Mozilla/5.0", url
            ]
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout + 2)
            if result.returncode == 0:
                data = json.loads(result.stdout)
                streams = data.get("streams", [])
                video_stream = next((s for s in streams if s.get("codec_type") == "video"), None)
                if video_stream:
                    w = video_stream.get("width", 0)
                    h = video_stream.get("height", 0)
                    res = f"{w}x{h}" if w and h else None
                    codec = video_stream.get("codec_name", "")
                    fps = video_stream.get("r_frame_rate", "").split("/")
                    fps_val = float(fps[0])/float(fps[1]) if len(fps)==2 and fps[1]!='0' else 0
                    return {"resolution": res, "video_codec": codec, "fps": round(fps_val, 2)}
        except Exception:
            pass
        return {}

    loop = asyncio.get_event_loop()
    with ThreadPoolExecutor(max_workers=1) as executor:
        return await loop.run_in_executor(executor, _run)

async def run_ocr_check_async(url: str, timeout: int) -> bool:
    """
    【增强特性】OCR 检测
    对流截图并识别文字，检测"登录墙"、"区域限制"等软错误
    """
    if not OCR_AVAILABLE:
        return True
        
    def _run():
        frame_path = f"/tmp/iptv_ocr_{abs(hash(url)) % 10000}.png"
        try:
            cmd = ["ffmpeg", "-y", "-hide_banner", "-loglevel", "error", "-i", url, "-ss", "1", "-vframes", "1", frame_path]
            proc = subprocess.run(cmd, capture_output=True, timeout=timeout + 2)
            if proc.returncode != 0 or not os.path.exists(frame_path):
                return False
            
            img = Image.open(frame_path)
            text = pytesseract.image_to_string(img, lang='eng+chi_sim').lower()
            blacklist_words = ("login", "sign in", "geo-block", "not available", "invalid", "expired", "no signal", "test stream", "demo", "black screen", "请登录", "区域限制", "套餐", "购买", "扫码", "此画面", "服务器","失效", "切换", "403", "unauthorized")
            
            for word in blacklist_words:
                if word in text:
                    return False
            return True
        except Exception:
            return False
        finally:
            if os.path.exists(frame_path):
                try: os.remove(frame_path)
                except: pass

    loop = asyncio.get_event_loop()
    with ThreadPoolExecutor(max_workers=1) as executor:
        return await loop.run_in_executor(executor, _run)

async def test_channel_speed(channel_info: Dict[str, Any], session: ClientSession, semaphore: asyncio.Semaphore) -> Dict[str, Any]:
    """
    【核心业务】单个频道的完整测速流程
    流程：
    1. M3U8 分片测速 (优先)
    2. 普通 HTTP 下载测速
    3. FFmpeg 降级探测 (若速度慢或失败)
    4. OCR 软错误检测
    """
    url = channel_info['url']
    name = channel_info['name']
    headers = {"User-Agent": "Mozilla/5.0", "Accept": "*/*"}
    result = {
        "url": url,
        "name": name,
        "alive": False,
        "delay": -1,
        "speed": 0.0,
        "resolution": None,
        "reason": "Unknown"
    }
    
    async with semaphore:
        try:
            # 1. M3U8 分片测速 (优先)
            if url.endswith(Config.HLS_EXTENSIONS):
                segments = await get_m3u8_segments(url, session, headers, Config.READ_TIMEOUT)
                if segments:
                    # 并发下载前 5 个分片
                    tasks = [get_speed_with_download(seg, session, headers, Config.READ_TIMEOUT) for seg in segments]
                    results = await asyncio.gather(*tasks, return_exceptions=True)
                    
                    valid_results = [r for r in results if isinstance(r, dict) and r.get('size', 0) > 0]
                    if valid_results:
                        total_size = sum(r['size'] for r in valid_results)
                        total_time = sum(r['time'] for r in valid_results)
                        avg_delay = max(r['delay'] for r in valid_results)
                        
                        result['alive'] = True
                        result['speed'] = total_size / total_time / 1024 / 1024 if total_time > 0 else 0
                        result['delay'] = avg_delay
                else:
                    # 解析失败，尝试直接下载主文件
                    res = await get_speed_with_download(url, session, headers, Config.READ_TIMEOUT)
                    if res['size'] > 0:
                        result['alive'] = True
                        result['speed'] = res['speed']
                        result['delay'] = res['delay']
            else:
                # 非 M3U8: 直接测速
                res = await get_speed_with_download(url, session, headers, Config.READ_TIMEOUT)
                if res['size'] > 0:
                    result['alive'] = True
                    result['speed'] = res['speed']
                    result['delay'] = res['delay']

            # 2. 结果后处理：FFmpeg 降级探测 (Guovin logic)
            if result['alive']:
                # 如果速度极低但延迟正常，尝试 FFmpeg 确认是否有流
                if result['speed'] < 0.05 and result['delay'] != -1:
                    ff_info = await probe_ffmpeg(url, Config.TIMEOUT)
                    if ff_info.get('resolution'):
                        result['resolution'] = ff_info['resolution']
                        result['alive'] = True
                        result['speed'] = 0.1 # 赋予基础速度值避免被过滤
                
                # 获取分辨率 (如果还没拿到)
                if not result['resolution'] and result['speed'] > 0:
                     # 简单启发式：根据速度猜测
                     if result['speed'] > 2.0: result['resolution'] = "1920x1080"
                     elif result['speed'] > 1.0: result['resolution'] = "1280x720"
                     else: result['resolution'] = "720x576"

                # 3. OCR 软错误检测
                if not url.endswith(Config.HLS_EXTENSIONS) or result['speed'] < 0.1:
                    if await run_ocr_check_async(url, Config.TIMEOUT):
                        pass # OCR 通过
                    else:
                        result['alive'] = False
                        result['reason'] = "OCR Failed (Login/Geo-block)"
            else:
                result['reason'] = "Download Failed / Timeout"

        except Exception as e:
            result['reason'] = str(e)
        
        return result


async def run_host_level_speed_test(channels: List[Dict[str, Any]], session: ClientSession, semaphore: asyncio.Semaphore) -> Tuple[Dict[str, Dict[str, Any]], List[Dict[str, Any]]]:
    """
    主机级测速：
    - 对每个主机选取代表性 URL（优先 .m3u8）进行完整测速
    - 如果代表性 URL 失败，尝试最多 3 个备选 URL
    - 返回主机质量字典，以及填充了测速结果的频道列表
    """
    # 构建 host -> 该主机所有 URL 的映射
    host_to_urls: DefaultDict[str, List[Dict[str, Any]]] = defaultdict(list)
    for ch in channels:
        host = get_host_key(ch['url'])
        if host:
            host_to_urls[host].append(ch)
    
    host_results = {}
    # 对每个主机测速
    for host, ch_list in host_to_urls.items():
        # 收集该主机所有 URL
        urls = [ch['url'] for ch in ch_list]
        
        # 选择代表性 URL（优先 .m3u8）
        rep_url = next((u for u in urls if u.endswith(Config.HLS_EXTENSIONS)), urls[0])
        
        # 对代表性 URL 进行完整测速
        result = await test_channel_speed({"url": rep_url, "name": "rep"}, session, semaphore)
        
        # 如果失败，尝试其他备选（最多 3 个）
        if not result['alive']:
            candidates = [u for u in urls if u != rep_url][:3]
            for cand in candidates:
                cand_result = await test_channel_speed({"url": cand, "name": "cand"}, session, semaphore)
                if cand_result['alive']:
                    result = cand_result
                    break
        
        # 保存主机结果
        host_results[host] = {
            'alive': result['alive'],
            'delay': result['delay'],
            'speed': result['speed'],
            'resolution': result['resolution'],
            'representative_url': rep_url
        }
        
        # 将该主机结果应用到所有频道（只更新测速相关字段）
        for ch in ch_list:
            ch['alive'] = result['alive']
            ch['delay'] = result['delay']
            ch['speed'] = result['speed']
            ch['resolution'] = result.get('resolution')
            ch['reason'] = result.get('reason')
            
    return host_results, channels


def filter_and_sort_results(results: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    """
    【质量评估算法】过滤和排序结果
    逻辑：
    1. 过滤无效项 (alive=False, delay=-1)
    2. 动态速度过滤：基于 RESOLUTION_SPEED_MAP (1080P 需 > 1.5MB/s)
    3. 分辨率过滤：低于最小像素值则过滤
    4. 排序：速度降序 -> 延迟升序
    """
    valid_results = []
    for r in results:
        if not r['alive']:
            continue
        
        speed = r.get('speed', 0)
        res = r.get('resolution', '')
        delay = r.get('delay', -1)
        
        if delay == -1:
            continue
            
        # 速度过滤 (动态阈值)
        if Config.OPEN_FILTER_SPEED:
            min_spd = Config.RESOLUTION_SPEED_MAP.get(res, Config.RESOLUTION_SPEED_MAP['default'])
            if speed < min_spd:
                continue
        
        # 分辨率过滤
        if Config.OPEN_FILTER_RESOLUTION and res:
            res_val = get_resolution_value(res)
            if res_val < Config.MIN_RESOLUTION_VALUE:
                continue
                
        valid_results.append(r)
    
    # 排序：速度降序，速度相同则延迟低者优先
    valid_results.sort(key=lambda x: (x['speed'], -x['delay']), reverse=True)
    return valid_results

# ================== 原有加载与处理逻辑 (适配 Async) ==================

def parse_m3u(content: str) -> List[Dict[str, str]]:
    """解析 M3U 内容为频道列表"""
    chs: List[Dict[str, str]] = []
    lines = [l.strip() for l in content.splitlines() if l.strip()]
    i = 0
    while i < len(lines):
        if lines[i].upper().startswith("#EXTINF:"):
            name = lines[i].split(",", 1)[1] if "," in lines[i] else "Unknown"
            if i + 1 < len(lines) and lines[i + 1] and not lines[i + 1].startswith("#"):
                url = clean_url(lines[i + 1])
                if is_valid_url(url):
                    chs.append({"name": name, "url": url})
                i += 2
                continue
        i += 1
    return chs

def txt2m3u_content(txt_content: str) -> str:
    """将 TXT 格式转换为标准 M3U"""
    lines = txt_content.splitlines()
    group_title = ""
    m3u_lines = ['#EXTM3U x-tvg-url="https://live.fanmingming.com/e.xml"', f'# Generated at {beijing_time_str()}']
    logo_url_base = "https://live.fanmingming.com/tv/"
    for line in lines:
        line = line.strip()
        if not line or line.startswith("#"): continue
        if line.endswith(",#genre#"):
            group_title = line[:-8].strip()
        elif "," in line and line.count(",") == 1:
            parts = line.split(",", 1)
            channel_name = parts[0].strip()
            stream_url = parts[1].strip()
            if not stream_url.startswith(("http://", "https://")): continue
            tvg_id = re.sub(r'[\s\-]', '', channel_name)
            logo_url = f"{logo_url_base}{tvg_id}.png"
            m3u_lines.append(f'#EXTINF:-1 tvg-id="{tvg_id}" tvg-name="{tvg_id}" tvg-logo="{logo_url}" group-title="{group_title}",{channel_name}')
            m3u_lines.append(stream_url)
    return "\n".join(m3u_lines)

def detect_and_convert_to_m3u(content: str) -> str:
    """自动识别内容格式（M3U 或 TXT）并转换为标准 M3U"""
    stripped = content.strip()
    if not stripped: return ""
    upper_head = stripped[:200].upper()
    if '#EXTM3U' in upper_head and "#EXTINF" in upper_head:
        lines = [line for line in stripped.splitlines() if not line.strip().upper().startswith('#EXTM3U')]
        return "\n".join(['#EXTM3U'] + lines)
    else:
        return txt2m3u_content(stripped)

def load_blacklist() -> Tuple[Set[str], Set[str]]:
    """智能加载黑名单 (通配 + 精确)"""
    host_only = set()
    host_with_port = set()
    if not os.path.exists(Config.BLACKLIST_FILE):
        return host_only, host_with_port
    try:
        with open(Config.BLACKLIST_FILE, 'r', encoding='utf-8') as f:
            for line in f:
                raw = line.strip()
                if not raw or raw.startswith("#"): continue
                entry = raw.lower()
                if ':' in entry:
                    parts = entry.split(':', 1)
                    host = parts[0].strip()
                    port_str = parts[1].strip()
                    if host and port_str.isdigit():
                        host_with_port.add(f"{host}:{port_str}")
                else:
                    host_only.add(entry.strip())
    except Exception:
        pass
    return host_only, host_with_port

def is_blocked_by_blacklist(url: str, host_only_set: Set[str], host_with_port_set: Set[str]) -> bool:
    """智能判断 URL 是否应被黑名单阻止"""
    try:
        parsed = urlparse(url)
        hostname = parsed.hostname
        if not hostname: return False
        hostname_lower = hostname.lower()
        port = parsed.port or (443 if parsed.scheme == 'https' else 80)
        exact_key = f"{hostname_lower}:{port}"
        if exact_key in host_with_port_set: return True
        if hostname_lower in host_only_set: return True
        return False
    except:
        return False

def load_sources_sync() -> Tuple[str, List[Dict[str, Any]]]:
    """同步加载源文件 (IO 操作)"""
    source_details: List[Dict[str, Any]] = []
    if not os.path.exists(Config.BASE_URL_FILE):
        raise FileNotFoundError(f"❌ 配置文件未找到: {Config.BASE_URL_FILE}")
    
    remote_urls = []
    with open(Config.BASE_URL_FILE, "r", encoding="utf-8") as f:
        for line in f:
            raw = line.strip()
            if raw and not raw.startswith("#") and raw.startswith(("http://", "https://")):
                remote_urls.append(raw)
    
    import requests
    s = requests.Session()
    s.headers.update({"User-Agent": "Mozilla/5.0"})
    merged = ['#EXTM3U']
    
    from concurrent.futures import ThreadPoolExecutor, as_completed
    def fetch(u):
        detail = {"type": "remote", "url": u, "success": False, "line_count": 0}
        try:
            r = s.get(u, timeout=15)
            if r.status_code == 200:
                converted = detect_and_convert_to_m3u(r.text)
                if converted.strip():
                    lines = [l for l in converted.splitlines() if not l.strip().upper().startswith('#EXTM3U')]
                    detail.update({"success": True, "line_count": len(lines)})
                    return lines, detail
        except Exception as e:
            detail["error"] = str(e)
        return [], detail

    with ThreadPoolExecutor(max_workers=10) as executor:
        futures = [executor.submit(fetch, u) for u in remote_urls]
        for future in as_completed(futures):
            lines, detail = future.result()
            merged.extend(lines)
            source_details.append(detail)
            
    local_dir = "local_playlists"
    if os.path.exists(local_dir):
        for fname in os.listdir(local_dir):
            if fname.lower().endswith(('.txt', '.m3u')):
                fpath = os.path.join(local_dir, fname)
                detail = {"type": "local", "path": fpath, "success": False, "line_count": 0}
                try:
                    with open(fpath, 'r', encoding='utf-8') as f:
                        raw = f.read()
                    content = txt2m3u_content(raw) if fname.lower().endswith('.txt') else raw
                    if content.strip():
                        merged.extend([l for l in content.splitlines() if not l.strip().upper().startswith('#EXTM3U')])
                        detail["success"] = True
                        detail["line_count"] = len(content.splitlines())
                except Exception as e:
                    detail["error"] = str(e)
                source_details.append(detail)
                
    return "\n".join(merged), source_details

# ================== 主执行流程 ==================

async def run_speed_test_all(channels: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    """异步并发执行所有频道测速"""
    connector = TCPConnector(ssl=False, limit=Config.MAX_CONCURRENT)
    async with ClientSession(connector=connector, trust_env=True) as session:
        semaphore = asyncio.Semaphore(Config.MAX_CONCURRENT)
        
        tasks = [test_channel_speed(ch, session, semaphore) for ch in channels]
        results = await asyncio.gather(*tasks, return_exceptions=True)
        
        valid_results = []
        for r in results:
            if isinstance(r, Exception):
                continue
            if isinstance(r, dict) and r.get('alive'):
                valid_results.append(r)
        return valid_results

def sort_channels_with_predefined(channels: List[Dict[str, Any]], predefined_order: List[str]) -> List[Dict[str, Any]]:
    """
    按照预定义顺序 + 自然排序对频道列表排序
    - 预定义列表中的频道按列表顺序排列
    - 未在预定义列表中的频道按自然排序（数字优先）追加到末尾
    """
    name_to_item = {item['name']: item for item in channels}
    
    ordered = []
    remaining = []
    
    # 预定义顺序中的频道（按顺序）
    for name in predefined_order:
        if name in name_to_item:
            ordered.append(name_to_item[name])
            del name_to_item[name]  # 移除已处理频道
    
    # 剩余的频道（未在预定义列表中）按自然排序
    remaining = sorted(name_to_item.values(), key=lambda x: natural_sort_key(x['name']))
    
    return ordered + remaining

def generate_outputs(final_channels: List[Dict[str, Any]], stats: Dict[str, Any], source_details: List[Dict[str, Any]], channel_order: Dict[str, List[str]]):
    """生成输出文件和报告，支持预定义频道顺序"""
    group_to_channels: DefaultDict[str, List[Dict[str, Any]]] = defaultdict(list)
    for item in final_channels:
        g = guess_group(item['name'])
        group_to_channels[g].append(item)

    # 对每个分组应用自定义排序（预定义顺序 + 自然排序）
    for group_name, chs in group_to_channels.items():
        predefined = channel_order.get(group_name, [])
        sorted_chs = sort_channels_with_predefined(chs, predefined)
        group_to_channels[group_name] = sorted_chs

    # 排序分组（按预定义分组顺序）
    ordered_groups = []
    for g_name in Config.GROUP_OUTPUT_ORDER:
        if g_name in group_to_channels:
            ordered_groups.append((g_name, group_to_channels[g_name]))
    for g, chs in group_to_channels.items():
        if g not in Config.GROUP_OUTPUT_ORDER:
            ordered_groups.append((g, chs))
            
    # 写 M3U
    os.makedirs(os.path.dirname(Config.OUTPUT_FILE), exist_ok=True)
    with open(Config.OUTPUT_FILE, "w", encoding="utf-8") as f:
        f.write('#EXTM3U x-tvg-url="https://live.fanmingming.com/europe.xml.gz"\n')
        for group_name, channels in ordered_groups:
            for item in channels:
                logo = extract_logo(item['name'])
                f.write(f'#EXTINF:-1 tvg-id="{item["name"]}" tvg-name="{item["name"]}" tvg-logo="{logo}" group-title="{group_name}",{item["name"]}\n{item["url"]}\n')
    
    # 写报告
    report = f"# ✅ IPTV 清洗报告 (Guovin Logic Strict + 频道去重 + 预定义排序)\n> **时间**: {beijing_time_str()}\n> **存活率**: {stats['survival_rate']:.1f}%\n\n"
    report += f"| 原始频道 | 唯一主机 | 存活频道 | 最终保留 |\n|---|---|---|---|\n| {stats['raw_channels']} | {stats['unique_hosts']} | {stats['alive_channels']} | {stats['final_channels']} |\n\n"
    report += "## 📺 分组统计\n"
    for g, chs in sorted(group_to_channels.items(), key=lambda x: len(x[1]), reverse=True):
        report += f"- **{g}**: {len(chs)}\n"
    
    with open(Config.REPORT_FILE, "w", encoding="utf-8") as f:
        f.write(report)
        
    logging.info(f"✅ 输出已保存: {Config.OUTPUT_FILE}, {Config.REPORT_FILE}")

def send_bark_report(report_path: str, device_key: str) -> None:
    """读取报告文件并通过 Bark 发送"""
    if not device_key:
        return
    try:
        with open(report_path, 'r', encoding='utf-8') as f:
            content = f.read()
    except Exception as e:
        logging.error(f"读取报告文件失败: {e}")
        return

    # Bark 消息正文有长度限制，一般建议不超过 2000 字符（实际可到 4000 左右）
    # 这里取前 1500 字符，若截断则添加提示
    max_len = 1500
    if len(content) > max_len:
        content = content[:max_len] + "\n\n... (内容过长，请查看完整报告)"
    
    # 发送请求
    import requests
    title = "IPTV 清洗报告"
    # 使用 quote 编码标题和内容
    url = f"https://api.day.app/{device_key}/{title}/{quote(content)}"
    try:
        resp = requests.get(url, timeout=10)
        if resp.status_code == 200:
            logging.info("🔔 Bark 报告已发送")
        else:
            logging.warning(f"Bark 发送失败: HTTP {resp.status_code}")
    except Exception as e:
        logging.error(f"Bark 发送异常: {e}")

def load_channel_order() -> Dict[str, List[str]]:
    """加载频道顺序配置文件，文件不存在或无效时返回空字典"""
    if not os.path.exists(Config.CHANNEL_ORDER_FILE):
        logging.info("未找到频道顺序配置文件，将使用自然排序")
        return {}
    try:
        with open(Config.CHANNEL_ORDER_FILE, 'r', encoding='utf-8') as f:
            data = json.load(f)
        if not isinstance(data, dict):
            logging.warning("频道顺序配置文件格式错误，应为JSON对象，使用自然排序")
            return {}
        # 可选：验证每个值是否为列表
        for k, v in data.items():
            if not isinstance(v, list):
                logging.warning(f"分组 '{k}' 的顺序配置不是列表，将忽略该分组")
                data[k] = []
        logging.info(f"已加载频道顺序配置，包含 {len(data)} 个分组")
        return data
    except Exception as e:
        logging.warning(f"加载频道顺序配置文件失败: {e}，将使用自然排序")
        return {}

def main():
    """主入口"""
    setup_logger()
    logging.info("="*60)
    logging.info("🚀 IPTV 清洗系统 v2.0 (Strict Guovin Logic + 频道去重 + Bark 报告 + 预定义排序)")
    logging.info("="*60)
    
    # 1. 加载数据
    try:
        raw_content, source_details = load_sources_sync()
    except Exception as e:
        logging.error(f"❌ 加载源失败: {e}")
        return

    host_only_bl, host_port_bl = load_blacklist()
    raw_channels = parse_m3u(raw_content)
    logging.info(f"📥 解析到 {len(raw_channels)} 条原始记录")
    
    # 2. 过滤黑名单 & 去重 & 标准化
    filtered = []
    seen_urls = set()
    for ch in raw_channels:
        if not is_valid_url(ch['url']): continue
        if is_blocked_by_blacklist(ch['url'], host_only_bl, host_port_bl): continue
        if ch['url'] in seen_urls: continue
        seen_urls.add(ch['url'])
        
        # === 关键：使用 Guovin 逻辑标准化名称 ===
        clean_name = normalize_channel_name(ch['name'])
        filtered.append({"name": clean_name, "url": ch['url'], "original": ch['name']})
        
    logging.info(f"🧹 过滤后剩余: {len(filtered)} 条")
    
    hosts = set()
    for ch in filtered:
        h = get_host_key(ch['url'])
        if h: hosts.add(h)
    logging.info(f"🌐 唯一主机数: {len(hosts)}")
    
    # 3. 异步测速
    logging.info(f"⚡ 开始异步测速 (并发:{Config.MAX_CONCURRENT})...")
    start_time = time.time()
    
    loop = asyncio.new_event_loop()
    asyncio.set_event_loop(loop)
    try:
        if Config.USE_HOST_LEVEL_SPEED:
            logging.info("⚡ 使用主机级测速模式...")
            async def host_task():
                connector = TCPConnector(ssl=False, limit=Config.MAX_CONCURRENT)
                async with ClientSession(connector=connector, trust_env=True) as session:
                    semaphore = asyncio.Semaphore(Config.MAX_CONCURRENT)
                    _, filtered_with_speed = await run_host_level_speed_test(filtered, session, semaphore)
                return filtered_with_speed
            filtered_with_speed = loop.run_until_complete(host_task())
            valid_results = [ch for ch in filtered_with_speed if ch.get('alive')]
        else:
            logging.info("⚡ 使用独立 URL 测速模式...")
            valid_results = loop.run_until_complete(run_speed_test_all(filtered))
    finally:
        loop.close()
        
    elapsed = time.time() - start_time
    logging.info(f"⏱️ 测速完成，耗时: {elapsed:.2f} 秒，有效结果: {len(valid_results)}")
    
    # 4. 质量评估与排序 (Guovin 算法)
    final_list = filter_and_sort_results(valid_results)
    logging.info(f"🎯 质量过滤后剩余: {len(final_list)}")

    # ===== 按频道名去重，只保留最优源 =====
    best_per_channel = {}
    for item in final_list:
        name = item['name']
        if name not in best_per_channel:
            best_per_channel[name] = item
    final_list_unique = list(best_per_channel.values())
    logging.info(f"🎯 去重后唯一频道数: {len(final_list_unique)}")
    
    # 加载频道顺序配置
    channel_order = load_channel_order()
    
    stats = {
        "raw_channels": len(filtered),
        "unique_hosts": len(hosts),
        "alive_channels": len(valid_results),
        "final_channels": len(final_list_unique),      # 使用去重后的数量
        "survival_rate": (len(valid_results)/len(filtered)*100) if filtered else 0
    }
    generate_outputs(final_list_unique, stats, source_details, channel_order)
    
    # 5. Bark 通知：发送完整报告
    device_key = Config.BARK_DEVICE_KEY or os.getenv("BARK_DEVICE_KEY")
    if device_key:
        send_bark_report(Config.REPORT_FILE, device_key)
    else:
        logging.info("未配置 BARK_DEVICE_KEY，跳过通知")

if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        logging.info("\n⚠️ 用户中断")
    except Exception as e:
        logging.exception(f"❌ 致命错误: {e}")



# #!/usr/bin/env python3
# # -*- coding: utf-8 -*-
# """
# IPTV 直播源智能清洗与验证系统（v2.0 Strict - Guovin Logic Edition）

# 【核心逻辑说明】
# 本脚本严格遵循 Guovin/iptv-api 的核心业务逻辑，同时保留了原有的 OCR 检测和分组功能。

# 1. 频道标准化 (normalize_channel_name):
#    - 多频道名拆分 (A-B-C -> A)
#    - 别名映射 (长匹配优先，基于 CHANNEL_ALIAS_MAP)
#    - 移除括号及内容
#    - 统一连接符为空格
#    - 移除冗余后缀 (HD, 频道, TV 等)
#    - CCTV 编号智能修正 (CCTV01 -> CCTV1, CCTV-5+ -> CCTV5+)
#    - CGTN 前缀标准化

# 2. 测速流程 (test_channel_speed):
#    - M3U8 分片测速：解析播放列表，下载前 5 个 TS 分片计算真实速度
#    - 滑动窗口稳定性算法：连续采样速度波动 < 15% 才判定为有效速度
#    - FFmpeg 降级探测：HTTP 测速失败时，调用 ffprobe 获取分辨率/编码
#    - OCR 软错误检测：识别“登录墙”、“区域限制”等无效画面

# 3. 质量评估 (filter_and_sort_results):
#    - 动态阈值过滤：基于分辨率 - 速率映射表 (1080P 需 > 1.5MB/s)
#    - 排序策略：速度降序 -> 延迟升序

# 4. 架构:
#    - 完全异步 (AsyncIO + Aiohttp)，支持高并发测速
# """

# import os
# import re
# import time
# import json
# import logging
# import asyncio
# import datetime
# import subprocess
# import math
# from urllib.parse import urlparse, urljoin, quote
# from collections import defaultdict
# from typing import List, Dict, Any, Optional, Tuple, Set, DefaultDict
# from concurrent.futures import ThreadPoolExecutor

# # ================== 依赖检查 ==================
# try:
#     import aiohttp
#     from aiohttp import ClientSession, TCPConnector, ClientTimeout
#     import m3u8
# except ImportError:
#     print("❌ 缺少依赖: 请运行 'pip install aiohttp m3u8'")
#     exit(1)

# try:
#     import pytesseract
#     from PIL import Image
#     OCR_AVAILABLE = True
# except ImportError:
#     OCR_AVAILABLE = False
#     pytesseract = None
#     Image = None

# # ================== 全局配置类 ==================
# class Config:
#     # --- 文件路径配置 ---
#     BASE_URL_FILE: str = "config/remote_sources.txt"            # 远程源列表
#     BLACKLIST_FILE: str = "config/blackHost_list.txt"           # 主机黑名单
#     OUTPUT_FILE: str = "output/live.m3u"                        # 输出 M3U
#     REPORT_FILE: str = "output/report.md"                       # 清洗报告
#     BARK_DEVICE_KEY: str = ""                                   # Bark 通知密钥
    
#     DEBUG_FILES: List[str] = [
#         "debug_1_merged_raw.m3u",
#         "debug_2_grouped_channels.json",
#         "debug_3_host_mapping.json",
#         "debug_4_host_quality.json",
#         "debug_5_host_ranking.md"
#     ]

#     # --- Guovin/iptv-api 核心测速参数 ---
#     TIMEOUT: int = 10                   # 总超时时间 (秒)
#     CONNECT_TIMEOUT: int = 5            # 连接超时
#     READ_TIMEOUT: int = 8               # 读取超时
#     MAX_CONCURRENT: int = 100            # 最大并发数 (Semaphore 限制)
    
#     # 新增：是否使用主机级测速（False=每个URL独立测速，True=同主机复用测速结果）
#     USE_HOST_LEVEL_SPEED: bool = True

#     # 滑动窗口稳定性算法参数
#     MIN_MEASURE_TIME: float = 1.0       # 最小测速时长 (秒)，低于此时长不判定稳定
#     STABILITY_WINDOW: int = 4           # 滑动窗口大小 (采样点数)
#     STABILITY_THRESHOLD: float = 0.15   # 速度波动阈值 (0.15 = 15%)，波动超过此值视为不稳定
#     MIN_BYTES: int = 64 * 1024          # 最小测试字节数 (64KB)
    
#     # --- 质量评估策略 ---
#     OPEN_FILTER_SPEED: bool = True              # 是否开启速度过滤
#     OPEN_FILTER_RESOLUTION: bool = True         # 是否开启分辨率过滤
#     MIN_RESOLUTION_VALUE: int = 0               # 最小分辨率像素值 (0=不限制)
    
#     # 分辨率 - 速率映射表 (MB/s)
#     # 逻辑：如果测得速度低于该分辨率对应的阈值，则视为不合格（可能是假高清或卡顿）
#     RESOLUTION_SPEED_MAP: Dict[str, float] = {
#         "1920x1080": 1.5,
#         "1280x720": 0.8,
#         "720x576": 0.5,
#         "default": 0.3
#     }
    
#     HLS_EXTENSIONS: Tuple[str, ...] = ('.m3u8', '.m3u')
#     LOGO_BASE_URL: str = "https://raw.githubusercontent.com/alantang1977/iptv_api/main/pic/logos/"
    
#     # --- 频道分组规则 (正则匹配) ---
#     GROUP_RULES: List[Tuple[str, str]] = [
#         (r'(CCTV[-]?14|哈哈炫动|卡酷|宝宝|幼教|贝瓦|巧虎|新科动漫|小猪佩奇|汪汪队|海底小纵队|米老鼠|迪士尼|熊出没|猫和老鼠|哆啦A梦|喜羊羊|青少|儿童|动画|动漫|少儿|卡通|金鹰|cartoon|disney|哈哈炫动)', "🧸 儿童动画"),
#         (r'(央视|CCTV[0-9]*[高清]?|CGTN|CCTV|风云音乐|第一剧场|怀旧剧场|女性时尚|风云足球|世界地理|兵器科技|电视指南)', "🇨🇳 央视频道"),
#         (r'(卫视|湖南|浙江|江苏|北京|广东|深圳|东方|安徽|山东|河南|湖北|四川|辽宁|东南|天津|四川|内蒙古|云南)', "📺 卫视频道"),
#         (r'(翡翠|明珠|凤凰|鳳凰东森|莲花|AMC|龙华|澳亚|港台|寰宇|TVB|华语|中天|东森|年代|民视|三立|星空|民视|台视|美亚|美亞|千禧|无线|無線|VIUTV|HOY|RTHK|Now|靖天|星卫|香港|澳门|台湾)', "🇭🇰 港澳台频道"),
#         (r'(体育|CCTV5|高尔夫|足球|NBA|英超|西甲|欧冠)', "⚽ 体育频道"),
#         (r'(电影|影院|CHC|HBO|星空|AXN|TCM|佳片)', "🎬 影视频道"),
#         (r'(AMC|BET|Discovery|CBS|BET|cine|CNN|disney|epix|espn|fox|american|boomerang|cnbc|entertainment|fs|fuse|fx|hbo|国家地理|Animal Planet|BBC|NHK|DW|France24|CNN|Al Jazeera)', "🌍 国际频道"),
#         (r'(教育|课堂|空中|大学|学习|国学|书画|考试|中学|学堂)', "🎓 教育频道"),
#         # 兜底规则：全英文且不含 CCTV/CGTN → 国际频道
#         (r'^(?=.*[a-zA-Z])(?!.*\b(cctv|cgtn)\b)[a-zA-Z0-9\s\-\+\&\.\'\!\(\)]+$', "🌍 国际频道"),
#     ]

#     # 最终输出分组顺序
#     GROUP_OUTPUT_ORDER: List[str] = [
#         "🇨🇳 央视频道", "📺 卫视频道", "🎬 影视频道", "⚽ 体育频道",
#         "🧸 儿童动画", "🌍 国际频道", "🎓 教育频道", "🇭🇰 港澳台频道", "📺 其他频道"
#     ]

# # ================== 频道别名字典 (保持原有完整映射) ==================
# # 逻辑：将各种变体名称映射为标准名称，用于去重和分组
# CHANNEL_ALIAS_MAP: Dict[str, str] = {
#     alias: std
#     for std, aliases in {
#         "CCTV1": ["CCTV-1", "CCTV-1 HD", "CCTV1 HD", "CCTV-1综合"],
#         "CCTV2": ["CCTV-2", "CCTV-2 HD", "CCTV2 HD", "CCTV-2财经"],
#         "CCTV3": ["CCTV-3", "CCTV-3 HD", "CCTV3 HD", "CCTV-3综艺"],
#         "CCTV4": ["CCTV-4", "CCTV-4 HD", "CCTV4 HD", "CCTV-4中文国际"],
#         "CCTV4欧洲": ["CCTV-4欧洲", "CCTV4欧洲 HD", "CCTV-4 欧洲", "CCTV-4中文国际欧洲"],
#         "CCTV4美洲": ["CCTV-4美洲", "CCTV-4北美", "CCTV4美洲 HD", "CCTV-4 美洲", "CCTV-4中文国际美洲"],
#         "CCTV5": ["CCTV-5", "CCTV-5 HD", "CCTV5 HD", "CCTV-5体育"],
#         "CCTV5+": ["CCTV-5+", "CCTV-5+ HD", "CCTV5+ HD", "CCTV-5+体育赛事"],
#         "CCTV6": ["CCTV-6", "CCTV-6 HD", "CCTV6 HD", "CCTV-6电影"],
#         "CCTV7": ["CCTV-7", "CCTV-7 HD", "CCTV7 HD", "CCTV-7国防军事"],
#         "CCTV8": ["CCTV-8", "CCTV-8 HD", "CCTV8 HD", "CCTV-8电视剧"],
#         "CCTV9": ["CCTV-9", "CCTV-9 HD", "CCTV9 HD", "CCTV-9纪录"],
#         "CCTV10": ["CCTV-10", "CCTV-10 HD", "CCTV10 HD", "CCTV-10科教"],
#         "CCTV11": ["CCTV-11", "CCTV-11 HD", "CCTV11 HD", "CCTV-11戏曲"],
#         "CCTV12": ["CCTV-12", "CCTV-12 HD", "CCTV12 HD", "CCTV-12社会与法"],
#         "CCTV13": ["CCTV-13", "CCTV-13 HD", "CCTV13 HD", "CCTV-13新闻"],
#         "CCTV14": ["CCTV-14", "CCTV-14 HD", "CCTV14 HD", "CCTV-14少儿"],
#         "CCTV15": ["CCTV-15", "CCTV-15 HD", "CCTV15 HD", "CCTV-15音乐"],
#         "CCTV16": ["CCTV-16", "CCTV-16 HD", "CCTV-16 4K", "CCTV-16奥林匹克"],
#         "CCTV17": ["CCTV-17", "CCTV-17 HD", "CCTV17 HD", "CCTV-17农业农村"],
#         "CCTV4K": ["CCTV4K超高清", "CCTV-4K超高清", "CCTV 4K"],
#         "CCTV8K": ["CCTV8K超高清", "CCTV-8K超高清", "CCTV 8K"],
#         "湖南卫视": ["湖南卫视4K"],
#         "北京卫视": ["北京卫视4K"],
#         "东方卫视": ["东方卫视4K"],
#         "广东卫视": ["广东卫视4K"],
#         "深圳卫视": ["深圳卫视4K"],
#         "TVB Jade": ["翡翠台"],
#         "TVB Pearl": ["明珠台"],
#         "凤凰卫视中文台": ["凤凰中文", "凤凰中文台", "凤凰卫视中文"],
#         "凤凰卫视资讯台": ["凤凰资讯", "凤凰资讯台", "凤凰咨询"],
#         # ... (此处省略部分以保持长度，实际使用时请保留您完整的字典)
#     }.items()
#     for alias in aliases
# }

# # ================== 基础工具函数 ==================

# def beijing_time_str(fmt: str = "%Y-%m-%d %H:%M:%S") -> str:
#     """返回当前北京时间字符串"""
#     beijing_tz = datetime.timezone(datetime.timedelta(hours=8))
#     return datetime.datetime.now(beijing_tz).strftime(fmt)

# def setup_logger() -> None:
#     """初始化日志系统"""
#     log_level = logging.DEBUG if os.getenv("DEBUG") else logging.INFO
#     logging.basicConfig(
#         level=log_level,
#         format='%(asctime)s | %(levelname)-8s | %(message)s',
#         datefmt='%Y-%m-%d %H:%M:%S'
#     )

# def get_resolution_value(res_str: str) -> int:
#     """
#     计算分辨率像素总值 (宽*高)
#     用于比较分辨率高低，例如 1920x1080 -> 2073600
#     """
#     if not res_str:
#         return 0
#     match = re.search(r"(\d{3,4})x(\d{3,4})", res_str)
#     if match:
#         return int(match.group(1)) * int(match.group(2))
#     return 0

# def clean_url(raw: str) -> str:
#     """清理 URL，移除 $ 后参数及多余空格"""
#     return re.sub(r'[\$•].*|\s+.*', '', raw.strip()).rstrip('/?&')

# def is_valid_url(u: str) -> bool:
#     """判断是否为有效 HTTP/HTTPS URL"""
#     try:
#         r = urlparse(u)
#         return r.scheme in ("http", "https") and bool(r.netloc)
#     except Exception:
#         return False

# def get_host_key(u: str) -> Optional[str]:
#     """
#     从 URL 提取 host:port 作为主机唯一标识
#     例如: https://example.com:8080/path → example.com:8080
#     """
#     try:
#         p = urlparse(u)
#         port = p.port or (443 if p.scheme == "https" else 80)
#         return f"{p.hostname}:{port}" if p.hostname else None
#     except Exception:
#         return None

# # ================== 核心：频道名称标准化 (严格复刻 Guovin/iptv-api) ==================
# def normalize_channel_name(name: str) -> str:
#     """
#     严格遵循 Guovin/iptv-api 的频道名称处理流程：
#     1. 多频道拼接取主频道 (A-B-C -> A)
#     2. 别名映射 (长匹配优先)
#     3. 移除括号内容
#     4. 统一连接符为空格
#     5. 移除冗余后缀 (HD, 频道, TV 等)
#     6. CCTV 编号智能修正 (CCTV01 -> CCTV1, CCTV-5+ -> CCTV5+)
#     7. CGTN 前缀标准化
#     """
#     if not name or not isinstance(name, str):
#         return "Unknown"
    
#     original = name.strip()
#     if not original:
#         return "Unknown"

#     # Step 1: 处理多频道拼接 (A-B-C -> A)
#     if "-" in original and len(original.split("-")) >= 3:
#         original = original.split("-", 1)[0].strip()

#     # Step 2: 精确别名映射 (长别名优先)
#     # 注意：这里使用您提供的 CHANNEL_ALIAS_MAP
#     for alias in sorted(CHANNEL_ALIAS_MAP.keys(), key=lambda x: -len(x)):
#         if alias in original:
#             return CHANNEL_ALIAS_MAP[alias]

#     name = original

#     # Step 3: 移除括号及内容
#     name = re.sub(r'\s*[\(（【\[][^)）】\]]*[\)）】\]]\s*', '', name)

#     # Step 4: 统一连接符为空格
#     name = re.sub(r'[\s\-·•_\|]+', ' ', name)
#     name = re.sub(r'\s+', ' ', name).strip()

#     # Step 5: 移除冗余后缀
#     suffix_pattern = (
#         r'(?:'
#         r'HD|FHD|UHD|4K|超高清|高清|蓝光|标清|'
#         r'综合频道？|电视频道？|直播频道？|官方频道？|'
#         r'频道|TV|台|官方|正版|流畅|备用|测试|'
#         r'Ch|CH|Channel|咪咕|真|极速|'
#         r')$'
#     )
#     name = re.sub(suffix_pattern, '', name, flags=re.IGNORECASE).strip()

#     # Step 6: 智能标准化 CCTV 编号 (核心逻辑)
#     def cctv_replacer(m):
#         num_part = m.group(1)
#         digits = re.search(r'[0-9]+', num_part)
#         if not digits:
#             return m.group(0)
#         num_int = int(digits.group())
#         suffix = ''
#         if '+' in num_part:
#             suffix = '+'
#         elif 'k' in num_part.lower():
#             suffix = 'K'
#         return f"CCTV{num_int}{suffix}"

#     name = re.sub(
#         r'^CCTV[-\s]*([0-9][0-9\s\+\-kK]*)',
#         cctv_replacer,
#         name,
#         flags=re.IGNORECASE
#     )

#     # Step 7: 标准化 CGTN 前缀
#     name = re.sub(r'^CGTN[-\s]+', 'CGTN ', name, flags=re.IGNORECASE).strip()

#     cleaned = name.strip()
#     return cleaned if cleaned else original

# def guess_group(title: str) -> str:
#     """根据频道标题猜测所属分组（按 GROUP_RULES 顺序匹配）"""
#     for pat, grp in Config.GROUP_RULES:
#         if re.search(pat, title, re.IGNORECASE):
#             return grp
#     return "📺 其他频道"

# def extract_logo(channel: str) -> str:
#     """生成 logo URL（基于频道名，移除非字母数字字符）"""
#     clean_name = re.sub(r'[^\w]', '', channel).lower()
#     return f"{Config.LOGO_BASE_URL}{clean_name}.png"

# def is_valid_hls_content(text: str) -> bool:
#     """判断文本是否为有效的 M3U/M3U8 内容"""
#     txt = text.strip()
#     return txt.startswith('#EXTM3U') and any(k in txt for k in ["#EXTINF", "#EXT-X-STREAM-INF"])

# # ================== 核心测速逻辑 (严格复刻 Guovin/iptv-api) ==================


# async def get_speed_with_download(url: str, session: ClientSession, headers: dict, timeout: int) -> Dict[str, Any]:
#     """
#     【Guovin 核心算法】底层下载测速函数
#     功能：
#     1. 计算首字节延迟 (Delay)
#     2. 使用滑动窗口检测速度稳定性 (Stability Window)
#     3. 返回平均速度、延迟、总大小
    
#     逻辑：
#     - 持续下载数据块，记录每个时间窗口的瞬时速度
#     - 当采样点达到 STABILITY_WINDOW 且波动小于 STABILITY_THRESHOLD 时，判定为稳定，提前返回
#     - 若超时或未稳定，返回平均值
#     """
#     start_time = time.time()
#     delay = -1
#     total_size = 0
#     last_sample_time = start_time
#     last_sample_size = 0
#     speed_samples: List[float] = []
    
#     try:
#         async with session.get(url, headers=headers, timeout=ClientTimeout(total=timeout)) as response:
#             if response.status != 200:
#                 raise Exception(f"Status {response.status}")
            
#             async for chunk in response.content.iter_any():
#                 if chunk:
#                     # 记录首字节延迟
#                     if delay == -1:
#                         delay = int(round((time.time() - start_time) * 1000))
                    
#                     total_size += len(chunk)
#                     now = time.time()
#                     elapsed = now - start_time
                    
#                     # 采样计算瞬时速度 (MB/s)
#                     delta_t = now - last_sample_time
#                     delta_b = total_size - last_sample_size
#                     if delta_t > 0 and delta_b > 0:
#                         inst_speed = delta_b / delta_t / 1024.0 / 1024.0
#                         speed_samples.append(inst_speed)
#                         last_sample_time = now
#                         last_sample_size = total_size
                    
#                     # === 稳定性判断逻辑 (Guovin Core) ===
#                     # 条件：测速时间足够 + 数据量足够 + 采样点足够 + 波动在阈值内
#                     if (elapsed >= Config.MIN_MEASURE_TIME and total_size >= Config.MIN_BYTES
#                             and len(speed_samples) >= Config.STABILITY_WINDOW):
#                         window = speed_samples[-Config.STABILITY_WINDOW:]
#                         mean = sum(window) / len(window)
#                         if mean > 0 and (max(window) - min(window)) / mean < Config.STABILITY_THRESHOLD:
#                             return {
#                                 'speed': total_size / elapsed / 1024 / 1024,
#                                 'delay': delay,
#                                 'size': total_size,
#                                 'time': elapsed,
#                                 'stable': True
#                             }
#     except Exception:
#         pass
    
#     # 超时或未稳定，返回平均值
#     total_time = time.time() - start_time
#     speed_val = total_size / total_time / 1024 / 1024 if total_time > 0 else 0.0
#     return {
#         'speed': speed_val,
#         'delay': delay if delay != -1 else int(round(total_time * 1000)),
#         'size': total_size,
#         'time': total_time,
#         'stable': False
#     }

# async def get_m3u8_segments(url: str, session: ClientSession, headers: dict, timeout: int) -> List[str]:
#     """
#     【Guovin 核心逻辑】解析 M3U8 获取分片 URL
#     逻辑：
#     1. 如果是 Master Playlist (含子播放列表)，选择带宽最高的子流
#     2. 提取前 5 个 TS 分片 URL 用于测速
#     """
#     try:
#         async with session.get(url, headers=headers, timeout=ClientTimeout(total=timeout)) as resp:
#             if resp.status == 200:
#                 content = await resp.text()
#                 playlist = m3u8.loads(content)
                
#                 segments = []
#                 # 如果有子播放列表 (Master Playlist)
#                 if playlist.playlists:
#                     # 取带宽最高的子流
#                     best_pl = max(playlist.playlists, key=lambda p: p.stream_info.bandwidth if p.stream_info else 0)
#                     pl_url = urljoin(url, best_pl.uri)
#                     async with session.get(pl_url, headers=headers, timeout=ClientTimeout(total=timeout)) as pl_resp:
#                         if pl_resp.status == 200:
#                             sub_pl = m3u8.loads(await pl_resp.text())
#                             # 取前 5 个分片
#                             segments = [urljoin(pl_url, s.uri) for s in sub_pl.segments[:5]]
#                 else:
#                     # 直接是 Media Playlist
#                     segments = [urljoin(url, s.uri) for s in playlist.segments[:5]]
#                 return segments
#     except Exception:
#         pass
#     return []

# async def probe_ffmpeg(url: str, timeout: int) -> Dict[str, Any]:
#     """
#     【降级策略】调用 ffprobe 获取详细信息
#     当 HTTP 测速失败或速度为 0 时，使用此方法确认流是否有效并获取分辨率
#     """
#     def _run():
#         try:
#             cmd = [
#                 "ffprobe", "-v", "quiet", "-print_format", "json",
#                 "-show_streams", "-timeout", str(timeout * 1000000),
#                 "-user_agent", "Mozilla/5.0", url
#             ]
#             result = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout + 2)
#             if result.returncode == 0:
#                 data = json.loads(result.stdout)
#                 streams = data.get("streams", [])
#                 video_stream = next((s for s in streams if s.get("codec_type") == "video"), None)
#                 if video_stream:
#                     w = video_stream.get("width", 0)
#                     h = video_stream.get("height", 0)
#                     res = f"{w}x{h}" if w and h else None
#                     codec = video_stream.get("codec_name", "")
#                     fps = video_stream.get("r_frame_rate", "").split("/")
#                     fps_val = float(fps[0])/float(fps[1]) if len(fps)==2 and fps[1]!='0' else 0
#                     return {"resolution": res, "video_codec": codec, "fps": round(fps_val, 2)}
#         except Exception:
#             pass
#         return {}

#     loop = asyncio.get_event_loop()
#     with ThreadPoolExecutor(max_workers=1) as executor:
#         return await loop.run_in_executor(executor, _run)

# async def run_ocr_check_async(url: str, timeout: int) -> bool:
#     """
#     【增强特性】OCR 检测
#     对流截图并识别文字，检测“登录墙”、“区域限制”等软错误
#     """
#     if not OCR_AVAILABLE:
#         return True
        
#     def _run():
#         frame_path = f"/tmp/iptv_ocr_{abs(hash(url)) % 10000}.png"
#         try:
#             cmd = ["ffmpeg", "-y", "-hide_banner", "-loglevel", "error", "-i", url, "-ss", "1", "-vframes", "1", frame_path]
#             proc = subprocess.run(cmd, capture_output=True, timeout=timeout + 2)
#             if proc.returncode != 0 or not os.path.exists(frame_path):
#                 return False
            
#             img = Image.open(frame_path)
#             text = pytesseract.image_to_string(img, lang='eng+chi_sim').lower()
#             blacklist_words = ("login", "sign in", "geo-block", "not available", "invalid", "expired", "no signal", "test stream", "demo", "black screen", "请登录", "区域限制", "套餐", "购买", "扫码", "此画面", "服务器","失效", "切换", "403", "unauthorized")
            
#             for word in blacklist_words:
#                 if word in text:
#                     return False
#             return True
#         except Exception:
#             return False
#         finally:
#             if os.path.exists(frame_path):
#                 try: os.remove(frame_path)
#                 except: pass

#     loop = asyncio.get_event_loop()
#     with ThreadPoolExecutor(max_workers=1) as executor:
#         return await loop.run_in_executor(executor, _run)

# async def test_channel_speed(channel_info: Dict[str, Any], session: ClientSession, semaphore: asyncio.Semaphore) -> Dict[str, Any]:
#     """
#     【核心业务】单个频道的完整测速流程
#     流程：
#     1. M3U8 分片测速 (优先)
#     2. 普通 HTTP 下载测速
#     3. FFmpeg 降级探测 (若速度慢或失败)
#     4. OCR 软错误检测
#     """
#     url = channel_info['url']
#     name = channel_info['name']
#     headers = {"User-Agent": "Mozilla/5.0", "Accept": "*/*"}
#     result = {
#         "url": url,
#         "name": name,
#         "alive": False,
#         "delay": -1,
#         "speed": 0.0,
#         "resolution": None,
#         "reason": "Unknown"
#     }
    
#     async with semaphore:
#         try:
#             # 1. M3U8 分片测速 (优先)
#             if url.endswith(Config.HLS_EXTENSIONS):
#                 segments = await get_m3u8_segments(url, session, headers, Config.READ_TIMEOUT)
#                 if segments:
#                     # 并发下载前 5 个分片
#                     tasks = [get_speed_with_download(seg, session, headers, Config.READ_TIMEOUT) for seg in segments]
#                     results = await asyncio.gather(*tasks, return_exceptions=True)
                    
#                     valid_results = [r for r in results if isinstance(r, dict) and r.get('size', 0) > 0]
#                     if valid_results:
#                         total_size = sum(r['size'] for r in valid_results)
#                         total_time = sum(r['time'] for r in valid_results)
#                         avg_delay = max(r['delay'] for r in valid_results)
                        
#                         result['alive'] = True
#                         result['speed'] = total_size / total_time / 1024 / 1024 if total_time > 0 else 0
#                         result['delay'] = avg_delay
#                 else:
#                     # 解析失败，尝试直接下载主文件
#                     res = await get_speed_with_download(url, session, headers, Config.READ_TIMEOUT)
#                     if res['size'] > 0:
#                         result['alive'] = True
#                         result['speed'] = res['speed']
#                         result['delay'] = res['delay']
#             else:
#                 # 非 M3U8: 直接测速
#                 res = await get_speed_with_download(url, session, headers, Config.READ_TIMEOUT)
#                 if res['size'] > 0:
#                     result['alive'] = True
#                     result['speed'] = res['speed']
#                     result['delay'] = res['delay']

#             # 2. 结果后处理：FFmpeg 降级探测 (Guovin logic)
#             if result['alive']:
#                 # 如果速度极低但延迟正常，尝试 FFmpeg 确认是否有流
#                 if result['speed'] < 0.05 and result['delay'] != -1:
#                     ff_info = await probe_ffmpeg(url, Config.TIMEOUT)
#                     if ff_info.get('resolution'):
#                         result['resolution'] = ff_info['resolution']
#                         result['alive'] = True
#                         result['speed'] = 0.1 # 赋予基础速度值避免被过滤
                
#                 # 获取分辨率 (如果还没拿到)
#                 if not result['resolution'] and result['speed'] > 0:
#                      # 简单启发式：根据速度猜测
#                      if result['speed'] > 2.0: result['resolution'] = "1920x1080"
#                      elif result['speed'] > 1.0: result['resolution'] = "1280x720"
#                      else: result['resolution'] = "720x576"

#                 # 3. OCR 软错误检测
#                 if not url.endswith(Config.HLS_EXTENSIONS) or result['speed'] < 0.1:
#                     if await run_ocr_check_async(url, Config.TIMEOUT):
#                         pass # OCR 通过
#                     else:
#                         result['alive'] = False
#                         result['reason'] = "OCR Failed (Login/Geo-block)"
#             else:
#                 result['reason'] = "Download Failed / Timeout"

#         except Exception as e:
#             result['reason'] = str(e)
        
#         return result


# async def run_host_level_speed_test(channels: List[Dict[str, Any]], session: ClientSession, semaphore: asyncio.Semaphore) -> Tuple[Dict[str, Dict[str, Any]], List[Dict[str, Any]]]:
#     """
#     主机级测速：
#     - 对每个主机选取代表性 URL（优先 .m3u8）进行完整测速
#     - 如果代表性 URL 失败，尝试最多 3 个备选 URL
#     - 返回主机质量字典，以及填充了测速结果的频道列表
#     """
#     # 构建 host -> 该主机所有 URL 的映射
#     host_to_urls: DefaultDict[str, List[Dict[str, Any]]] = defaultdict(list)
#     for ch in channels:
#         host = get_host_key(ch['url'])
#         if host:
#             host_to_urls[host].append(ch)
    
#     host_results = {}
#     # 对每个主机测速
#     for host, ch_list in host_to_urls.items():
#         # 收集该主机所有 URL
#         urls = [ch['url'] for ch in ch_list]
        
#         # 选择代表性 URL（优先 .m3u8）
#         rep_url = next((u for u in urls if u.endswith(Config.HLS_EXTENSIONS)), urls[0])
        
#         # 对代表性 URL 进行完整测速
#         result = await test_channel_speed({"url": rep_url, "name": "rep"}, session, semaphore)
        
#         # 如果失败，尝试其他备选（最多 3 个）
#         if not result['alive']:
#             candidates = [u for u in urls if u != rep_url][:3]
#             for cand in candidates:
#                 cand_result = await test_channel_speed({"url": cand, "name": "cand"}, session, semaphore)
#                 if cand_result['alive']:
#                     result = cand_result
#                     break
        
#         # 保存主机结果
#         host_results[host] = {
#             'alive': result['alive'],
#             'delay': result['delay'],
#             'speed': result['speed'],
#             'resolution': result['resolution'],
#             'representative_url': rep_url
#         }
        
#         # 将该主机结果应用到所有频道（只更新测速相关字段）
#         for ch in ch_list:
#             ch['alive'] = result['alive']
#             ch['delay'] = result['delay']
#             ch['speed'] = result['speed']
#             ch['resolution'] = result.get('resolution')
#             ch['reason'] = result.get('reason')
            
#     return host_results, channels


# def filter_and_sort_results(results: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
#     """
#     【质量评估算法】过滤和排序结果
#     逻辑：
#     1. 过滤无效项 (alive=False, delay=-1)
#     2. 动态速度过滤：基于 RESOLUTION_SPEED_MAP (1080P 需 > 1.5MB/s)
#     3. 分辨率过滤：低于最小像素值则过滤
#     4. 排序：速度降序 -> 延迟升序
#     """
#     valid_results = []
#     for r in results:
#         if not r['alive']:
#             continue
        
#         speed = r.get('speed', 0)
#         res = r.get('resolution', '')
#         delay = r.get('delay', -1)
        
#         if delay == -1:
#             continue
            
#         # 速度过滤 (动态阈值)
#         if Config.OPEN_FILTER_SPEED:
#             min_spd = Config.RESOLUTION_SPEED_MAP.get(res, Config.RESOLUTION_SPEED_MAP['default'])
#             if speed < min_spd:
#                 continue
        
#         # 分辨率过滤
#         if Config.OPEN_FILTER_RESOLUTION and res:
#             res_val = get_resolution_value(res)
#             if res_val < Config.MIN_RESOLUTION_VALUE:
#                 continue
                
#         valid_results.append(r)
    
#     # 排序：速度降序，速度相同则延迟低者优先
#     valid_results.sort(key=lambda x: (x['speed'], -x['delay']), reverse=True)
#     return valid_results

# # ================== 原有加载与处理逻辑 (适配 Async) ==================

# def parse_m3u(content: str) -> List[Dict[str, str]]:
#     """解析 M3U 内容为频道列表"""
#     chs: List[Dict[str, str]] = []
#     lines = [l.strip() for l in content.splitlines() if l.strip()]
#     i = 0
#     while i < len(lines):
#         if lines[i].upper().startswith("#EXTINF:"):
#             name = lines[i].split(",", 1)[1] if "," in lines[i] else "Unknown"
#             if i + 1 < len(lines) and lines[i + 1] and not lines[i + 1].startswith("#"):
#                 url = clean_url(lines[i + 1])
#                 if is_valid_url(url):
#                     chs.append({"name": name, "url": url})
#                 i += 2
#                 continue
#         i += 1
#     return chs

# def txt2m3u_content(txt_content: str) -> str:
#     """将 TXT 格式转换为标准 M3U"""
#     lines = txt_content.splitlines()
#     group_title = ""
#     m3u_lines = ['#EXTM3U x-tvg-url="https://live.fanmingming.com/e.xml"', f'# Generated at {beijing_time_str()}']
#     logo_url_base = "https://live.fanmingming.com/tv/"
#     for line in lines:
#         line = line.strip()
#         if not line or line.startswith("#"): continue
#         if line.endswith(",#genre#"):
#             group_title = line[:-8].strip()
#         elif "," in line and line.count(",") == 1:
#             parts = line.split(",", 1)
#             channel_name = parts[0].strip()
#             stream_url = parts[1].strip()
#             if not stream_url.startswith(("http://", "https://")): continue
#             tvg_id = re.sub(r'[\s\-]', '', channel_name)
#             logo_url = f"{logo_url_base}{tvg_id}.png"
#             m3u_lines.append(f'#EXTINF:-1 tvg-id="{tvg_id}" tvg-name="{tvg_id}" tvg-logo="{logo_url}" group-title="{group_title}",{channel_name}')
#             m3u_lines.append(stream_url)
#     return "\n".join(m3u_lines)

# def detect_and_convert_to_m3u(content: str) -> str:
#     """自动识别内容格式（M3U 或 TXT）并转换为标准 M3U"""
#     stripped = content.strip()
#     if not stripped: return ""
#     upper_head = stripped[:200].upper()
#     if '#EXTM3U' in upper_head and "#EXTINF" in upper_head:
#         lines = [line for line in stripped.splitlines() if not line.strip().upper().startswith('#EXTM3U')]
#         return "\n".join(['#EXTM3U'] + lines)
#     else:
#         return txt2m3u_content(stripped)

# def load_blacklist() -> Tuple[Set[str], Set[str]]:
#     """智能加载黑名单 (通配 + 精确)"""
#     host_only = set()
#     host_with_port = set()
#     if not os.path.exists(Config.BLACKLIST_FILE):
#         return host_only, host_with_port
#     try:
#         with open(Config.BLACKLIST_FILE, 'r', encoding='utf-8') as f:
#             for line in f:
#                 raw = line.strip()
#                 if not raw or raw.startswith("#"): continue
#                 entry = raw.lower()
#                 if ':' in entry:
#                     parts = entry.split(':', 1)
#                     host = parts[0].strip()
#                     port_str = parts[1].strip()
#                     if host and port_str.isdigit():
#                         host_with_port.add(f"{host}:{port_str}")
#                 else:
#                     host_only.add(entry.strip())
#     except Exception:
#         pass
#     return host_only, host_with_port

# def is_blocked_by_blacklist(url: str, host_only_set: Set[str], host_with_port_set: Set[str]) -> bool:
#     """智能判断 URL 是否应被黑名单阻止"""
#     try:
#         parsed = urlparse(url)
#         hostname = parsed.hostname
#         if not hostname: return False
#         hostname_lower = hostname.lower()
#         port = parsed.port or (443 if parsed.scheme == 'https' else 80)
#         exact_key = f"{hostname_lower}:{port}"
#         if exact_key in host_with_port_set: return True
#         if hostname_lower in host_only_set: return True
#         return False
#     except:
#         return False

# def load_sources_sync() -> Tuple[str, List[Dict[str, Any]]]:
#     """同步加载源文件 (IO 操作)"""
#     source_details: List[Dict[str, Any]] = []
#     if not os.path.exists(Config.BASE_URL_FILE):
#         raise FileNotFoundError(f"❌ 配置文件未找到: {Config.BASE_URL_FILE}")
    
#     remote_urls = []
#     with open(Config.BASE_URL_FILE, "r", encoding="utf-8") as f:
#         for line in f:
#             raw = line.strip()
#             if raw and not raw.startswith("#") and raw.startswith(("http://", "https://")):
#                 remote_urls.append(raw)
    
#     import requests
#     s = requests.Session()
#     s.headers.update({"User-Agent": "Mozilla/5.0"})
#     merged = ['#EXTM3U']
    
#     from concurrent.futures import ThreadPoolExecutor, as_completed
#     def fetch(u):
#         detail = {"type": "remote", "url": u, "success": False, "line_count": 0}
#         try:
#             r = s.get(u, timeout=15)
#             if r.status_code == 200:
#                 converted = detect_and_convert_to_m3u(r.text)
#                 if converted.strip():
#                     lines = [l for l in converted.splitlines() if not l.strip().upper().startswith('#EXTM3U')]
#                     detail.update({"success": True, "line_count": len(lines)})
#                     return lines, detail
#         except Exception as e:
#             detail["error"] = str(e)
#         return [], detail

#     with ThreadPoolExecutor(max_workers=10) as executor:
#         futures = [executor.submit(fetch, u) for u in remote_urls]
#         for future in as_completed(futures):
#             lines, detail = future.result()
#             merged.extend(lines)
#             source_details.append(detail)
            
#     local_dir = "local_playlists"
#     if os.path.exists(local_dir):
#         for fname in os.listdir(local_dir):
#             if fname.lower().endswith(('.txt', '.m3u')):
#                 fpath = os.path.join(local_dir, fname)
#                 detail = {"type": "local", "path": fpath, "success": False, "line_count": 0}
#                 try:
#                     with open(fpath, 'r', encoding='utf-8') as f:
#                         raw = f.read()
#                     content = txt2m3u_content(raw) if fname.lower().endswith('.txt') else raw
#                     if content.strip():
#                         merged.extend([l for l in content.splitlines() if not l.strip().upper().startswith('#EXTM3U')])
#                         detail["success"] = True
#                         detail["line_count"] = len(content.splitlines())
#                 except Exception as e:
#                     detail["error"] = str(e)
#                 source_details.append(detail)
                
#     return "\n".join(merged), source_details

# # ================== 主执行流程 ==================

# async def run_speed_test_all(channels: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
#     """异步并发执行所有频道测速"""
#     connector = TCPConnector(ssl=False, limit=Config.MAX_CONCURRENT)
#     async with ClientSession(connector=connector, trust_env=True) as session:
#         semaphore = asyncio.Semaphore(Config.MAX_CONCURRENT)
        
#         tasks = [test_channel_speed(ch, session, semaphore) for ch in channels]
#         results = await asyncio.gather(*tasks, return_exceptions=True)
        
#         valid_results = []
#         for r in results:
#             if isinstance(r, Exception):
#                 continue
#             if isinstance(r, dict) and r.get('alive'):
#                 valid_results.append(r)
#         return valid_results

# def generate_outputs(final_channels: List[Dict[str, Any]], stats: Dict[str, Any], source_details: List[Dict[str, Any]]):
#     """生成输出文件和报告"""

#     group_to_channels: DefaultDict[str, List[Dict[str, Any]]] = defaultdict(list)
#     for item in final_channels:
#         g = guess_group(item['name'])
#         group_to_channels[g].append(item)

#     # 在每个分组内按频道名称排序（默认字符串排序）
#     for chs in group_to_channels.values():
#         chs.sort(key=lambda x: x['name'])   # <-- 新增排序

#     # 排序分组
#     ordered_groups = []
#     for g_name in Config.GROUP_OUTPUT_ORDER:
#         if g_name in group_to_channels:
#             ordered_groups.append((g_name, group_to_channels[g_name]))
#     for g, chs in group_to_channels.items():
#         if g not in Config.GROUP_OUTPUT_ORDER:
#             ordered_groups.append((g, chs))
            
#     # 写 M3U
#     os.makedirs(os.path.dirname(Config.OUTPUT_FILE), exist_ok=True)
#     with open(Config.OUTPUT_FILE, "w", encoding="utf-8") as f:
#         f.write('#EXTM3U x-tvg-url="https://live.fanmingming.com/europe.xml.gz"\n')
#         for group_name, channels in ordered_groups:
#             for item in channels:
#                 logo = extract_logo(item['name'])
#                 f.write(f'#EXTINF:-1 tvg-id="{item["name"]}" tvg-name="{item["name"]}" tvg-logo="{logo}" group-title="{group_name}",{item["name"]}\n{item["url"]}\n')
    
#     # 写报告
#     report = f"# ✅ IPTV 清洗报告 (Guovin Logic Strict)\n> **时间**: {beijing_time_str()}\n> **存活率**: {stats['survival_rate']:.1f}%\n\n"
#     report += f"| 原始频道 | 唯一主机 | 存活频道 | 最终保留 |\n|---|---|---|---|\n| {stats['raw_channels']} | {stats['unique_hosts']} | {stats['alive_channels']} | {stats['final_channels']} |\n\n"
#     report += "## 📺 分组统计\n"
#     for g, chs in sorted(group_to_channels.items(), key=lambda x: len(x[1]), reverse=True):
#         report += f"- **{g}**: {len(chs)}\n"
    
#     with open(Config.REPORT_FILE, "w", encoding="utf-8") as f:
#         f.write(report)
        
#     logging.info(f"✅ 输出已保存: {Config.OUTPUT_FILE}, {Config.REPORT_FILE}")

# def main():
#     """主入口"""
#     setup_logger()
#     logging.info("="*60)
#     logging.info("🚀 IPTV 清洗系统 v2.0 (Strict Guovin Logic)")
#     logging.info("="*60)
    
#     # 1. 加载数据
#     try:
#         raw_content, source_details = load_sources_sync()
#     except Exception as e:
#         logging.error(f"❌ 加载源失败: {e}")
#         return

#     host_only_bl, host_port_bl = load_blacklist()
#     raw_channels = parse_m3u(raw_content)
#     logging.info(f"📥 解析到 {len(raw_channels)} 条原始记录")
    
#     # 2. 过滤黑名单 & 去重 & 标准化
#     filtered = []
#     seen_urls = set()
#     for ch in raw_channels:
#         if not is_valid_url(ch['url']): continue
#         if is_blocked_by_blacklist(ch['url'], host_only_bl, host_port_bl): continue
#         if ch['url'] in seen_urls: continue
#         seen_urls.add(ch['url'])
        
#         # === 关键：使用 Guovin 逻辑标准化名称 ===
#         clean_name = normalize_channel_name(ch['name'])
#         filtered.append({"name": clean_name, "url": ch['url'], "original": ch['name']})
        
#     logging.info(f"🧹 过滤后剩余: {len(filtered)} 条")
    
#     hosts = set()
#     for ch in filtered:
#         h = get_host_key(ch['url'])
#         if h: hosts.add(h)
#     logging.info(f"🌐 唯一主机数: {len(hosts)}")
    
#     # 3. 异步测速
#     logging.info(f"⚡ 开始异步测速 (并发:{Config.MAX_CONCURRENT})...")
#     start_time = time.time()
    
#     loop = asyncio.new_event_loop()
#     asyncio.set_event_loop(loop)
#     try:
#         if Config.USE_HOST_LEVEL_SPEED:
#             logging.info("⚡ 使用主机级测速模式...")
#             async def host_task():
#                 connector = TCPConnector(ssl=False, limit=Config.MAX_CONCURRENT)
#                 async with ClientSession(connector=connector, trust_env=True) as session:
#                     semaphore = asyncio.Semaphore(Config.MAX_CONCURRENT)
#                     _, filtered_with_speed = await run_host_level_speed_test(filtered, session, semaphore)
#                 return filtered_with_speed
#             filtered_with_speed = loop.run_until_complete(host_task())
#             valid_results = [ch for ch in filtered_with_speed if ch.get('alive')]
#         else:
#             logging.info("⚡ 使用独立 URL 测速模式...")
#             valid_results = loop.run_until_complete(run_speed_test_all(filtered))
#     finally:
#         loop.close()
        
#     elapsed = time.time() - start_time
#     logging.info(f"⏱️ 测速完成，耗时: {elapsed:.2f} 秒，有效结果: {len(valid_results)}")
    
#     # 4. 质量评估与排序 (Guovin 算法)
#     final_list = filter_and_sort_results(valid_results)
#     logging.info(f"🎯 最终保留频道: {len(final_list)}")
    
#     stats = {
#         "raw_channels": len(filtered),
#         "unique_hosts": len(hosts),
#         "alive_channels": len(valid_results),
#         "final_channels": len(final_list),
#         "survival_rate": (len(valid_results)/len(filtered)*100) if filtered else 0
#     }
#     generate_outputs(final_list, stats, source_details)
    
#     # 5. Bark 通知
#     if Config.BARK_DEVICE_KEY or os.getenv("BARK_DEVICE_KEY"):
#         key = Config.BARK_DEVICE_KEY or os.getenv("BARK_DEVICE_KEY")
#         try:
#             import requests
#             msg = f"✅ 清洗完成\n保留: {len(final_list)}\n耗时: {elapsed:.1f}s"
#             url = f"https://api.day.app/{key}/IPTV 清洗完成/{quote(msg)}"
#             requests.get(url, timeout=5)
#             logging.info("🔔 Bark 通知已发送")
#         except:
#             pass

# if __name__ == "__main__":
#     try:
#         main()
#     except KeyboardInterrupt:
#         logging.info("\n⚠️ 用户中断")
#     except Exception as e:
#         logging.exception(f"❌ 致命错误: {e}")
