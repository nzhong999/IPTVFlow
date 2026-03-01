#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
IPTV 直播源智能清洗与验证系统（v1.1 - 深度验证增强版）

在 v1.0 基础上新增：
✅ **FFmpeg 深度流验证**：对非 .m3u8 链接，使用 ffprobe 验证音视频流结构
✅ **Tesseract OCR 软错误检测**：截图识别“登录墙”、“区域限制”等无效画面

其余特性同 v1.0（双模源加载、两阶段测速、黑名单、分组、报告等）
"""

import os
import re
import time
import json
import logging
import requests
import datetime
import subprocess
from urllib.parse import urlparse, quote
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor, as_completed
from typing import List, Dict, Any, Optional, Tuple, Set, DefaultDict


# ================== 全局配置类 ==================
class Config:
    """集中管理所有可调参数，便于维护和调整策略"""
    BASE_URL_FILE: str = "config/remote_sources.txt"            # 远程源列表文件
    BLACKLIST_FILE: str = "config/blackHost_list.txt"           # 主机黑名单文件（每行一个 host:port）
    OUTPUT_FILE: str = "output/live.m3u"                        # 最终输出的 M3U 文件
    REPORT_FILE: str = "output/report.md"                       # 清洗报告（Markdown）


    # 新增：Bark 通知设备密钥（可留空，此时从环境变量读取）
    BARK_DEVICE_KEY: str = ""     # 示例: "abc123def456" —— 留空则尝试从环境变量加载

    # 调试中间文件（用于问题排查）
    DEBUG_FILES: List[str] = [
        "debug_1_merged_raw.m3u",
        "debug_2_grouped_channels.json",
        "debug_3_host_mapping.json",
        "debug_4_host_quality.json",
        "debug_5_host_ranking.md"
    ]

    TIMEOUT: int = 8                            # HTTP 请求超时（秒）
    MAX_WORKERS: int = 15                       # 并发线程数
    HTTP_OK: int = 200                          # 成功 HTTP 状态码
    M3U_HEADER: str = '#EXTM3U'                 # M3U 标准头部
    HLS_EXTENSIONS: Tuple[str, ...] = ('.m3u8', '.m3u')  # HLS 流扩展名
    LOGO_BASE_URL: str = "https://raw.githubusercontent.com/alantang1977/iptv_api/main/pic/logos/"

    # 频道分组规则：正则匹配 → 分组名（顺序敏感，优先匹配靠前规则）
    GROUP_RULES: List[Tuple[str, str]] = [
        (r'(CCTV[-]?14|哈哈炫动|卡酷|宝宝|幼教|贝瓦|巧虎|新科动漫|小猪佩奇|汪汪队|海底小纵队|米老鼠|迪士尼|熊出没|猫和老鼠|哆啦A梦|喜羊羊|青少|儿童|动画|动漫|少儿|卡通|金鹰|cartoon|disney|哈哈炫动)', "🧸 儿童动画"),
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

    # 最终播放列表的分组输出顺序（重要！控制 M3U 中分组排列）
    GROUP_OUTPUT_ORDER: List[str] = [
        "🇨🇳 央视频道",
        "📺 卫视频道",
        "🎬 影视频道",
        "⚽ 体育频道",
        "🧸 儿童动画",
        "🌍 国际频道",
        "🎓 教育频道",
        "🇭🇰 港澳台频道",
        "📺 其他频道",  # 默认分组放最后
    ]


# ================== 频道别名字典（标准化名称） ==================
CHANNEL_ALIAS_MAP: Dict[str, str] = {
    alias: std
    for std, aliases in {
        "CCTV1": ["CCTV-1", "CCTV-1 HD", "CCTV1 HD", "CCTV-1综合"],
        "CCTV2": ["CCTV-2", "CCTV-2 HD", "CCTV2 HD", "CCTV-2财经"],
        "CCTV3": ["CCTV-3", "CCTV-3 HD", "CCTV3 HD", "CCTV-3综艺"],
        "CCTV4": ["CCTV-4", "CCTV-4 HD", "CCTV4 HD", "CCTV-4中文国际"],
        "CCTV4欧洲": ["CCTV-4欧洲", "CCTV-4欧洲", "CCTV4欧洲 HD", "CCTV-4 欧洲", "CCTV-4中文国际欧洲", "CCTV4中文欧洲"],
        "CCTV4美洲": ["CCTV-4美洲", "CCTV-4北美", "CCTV4美洲 HD", "CCTV-4 美洲", "CCTV-4中文国际美洲", "CCTV4中文美洲"],
        "CCTV5": ["CCTV-5", "CCTV-5 HD", "CCTV5 HD", "CCTV-5体育"],
        "CCTV5+": ["CCTV-5+", "CCTV-5+ HD", "CCTV5+ HD", "CCTV-5+体育赛事"],
        "CCTV6": ["CCTV-6", "CCTV-6 HD", "CCTV6 HD", "CCTV-6电影"],
        "CCTV7": ["CCTV-7", "CCTV-7 HD", "CCTV7 HD", "CCTV-7国防军事"],
        "CCTV8": ["CCTV-8", "CCTV-8 HD", "CCTV8 HD", "CCTV-8电视剧"],
        "CCTV9": ["CCTV-9", "CCTV-9 HD", "CCTV9 HD", "CCTV-9纪录"],
        "CCTV10": ["CCTV-10", "CCTV-10 HD", "CCTV10 HD", "CCTV-10科教"],
        "CCTV11": ["CCTV-11", "CCTV-11 HD", "CCTV11 HD", "CCTV-11戏曲"],
        "CCTV12": ["CCTV-12", "CCTV-12 HD", "CCTV12 HD", "CCTV-12社会与法"],
        "CCTV13": ["CCTV-13", "CCTV-13 HD", "CCTV13 HD", "CCTV-13新闻"],
        "CCTV14": ["CCTV-14", "CCTV-14 HD", "CCTV14 HD", "CCTV-14少儿"],
        "CCTV15": ["CCTV-15", "CCTV-15 HD", "CCTV15 HD", "CCTV-15音乐"],
        "CCTV16": ["CCTV-16", "CCTV-16 HD", "CCTV-16 4K", "CCTV-16奥林匹克", "CCTV16 4K", "CCTV-16奥林匹克4K"],
        "CCTV17": ["CCTV-17", "CCTV-17 HD", "CCTV17 HD", "CCTV-17农业农村"],
        "CCTV4K": ["CCTV4K超高清", "CCTV-4K超高清", "CCTV-4K 超高清", "CCTV 4K"],
        "CCTV8K": ["CCTV8K超高清", "CCTV-8K超高清", "CCTV-8K 超高清", "CCTV 8K"],
        "兵器科技": ["CCTV-兵器科技", "CCTV兵器科技"],
        "风云音乐": ["CCTV-风云音乐", "CCTV风云音乐"],
        "第一剧场": ["CCTV-第一剧场", "CCTV第一剧场"],
        "风云足球": ["CCTV-风云足球", "CCTV风云足球"],
        "风云剧场": ["CCTV-风云剧场", "CCTV风云剧场"],
        "怀旧剧场": ["CCTV-怀旧剧场", "CCTV怀旧剧场"],
        "女性时尚": ["CCTV-女性时尚", "CCTV女性时尚"],
        "世界地理": ["CCTV-世界地理", "CCTV世界地理"],
        "央视台球": ["CCTV-央视台球", "CCTV央视台球"],
        "高尔夫网球": ["CCTV-高尔夫网球", "CCTV高尔夫网球", "CCTV央视高网", "CCTV-高尔夫·网球", "央视高网"],
        "央视文化精品": ["CCTV-央视文化精品", "CCTV央视文化精品", "CCTV文化精品", "CCTV-文化精品", "文化精品"],
        "卫生健康": ["CCTV-卫生健康", "CCTV卫生健康"],
        "电视指南": ["CCTV-电视指南", "CCTV电视指南"],
        "农林卫视": ["陕西农林卫视"],
        "三沙卫视": ["海南三沙卫视"],
        "兵团卫视": ["新疆兵团卫视"],
        "延边卫视": ["吉林延边卫视"],
        "安多卫视": ["青海安多卫视"],
        "康巴卫视": ["四川康巴卫视"],
        "山东教育卫视": ["山东教育"],
        "中国教育1台": ["CETV1", "中国教育一台", "中国教育1", "CETV-1 综合教育", "CETV-1"],
        "中国教育2台": ["CETV2", "中国教育二台", "中国教育2", "CETV-2 空中课堂", "CETV-2"],
        "中国教育3台": ["CETV3", "中国教育三台", "中国教育3", "CETV-3 教育服务", "CETV-3"],
        "中国教育4台": ["CETV4", "中国教育四台", "中国教育4", "CETV-4 职业教育", "CETV-4"],
        "早期教育": ["中国教育5台", "中国教育五台", "CETV早期教育", "华电早期教育", "CETV 早期教育"],
        "湖南卫视": ["湖南卫视4K"],
        "北京卫视": ["北京卫视4K"],
        "东方卫视": ["东方卫视4K"],
        "广东卫视": ["广东卫视4K"],
        "深圳卫视": ["深圳卫视4K"],
        "山东卫视": ["山东卫视4K"],
        "四川卫视": ["四川卫视4K"],
        "浙江卫视": ["浙江卫视4K"],
        "CHC影迷电影": ["CHC高清电影", "CHC-影迷电影", "影迷电影", "chc高清电影"],
        "淘电影": ["IPTV淘电影", "北京IPTV淘电影", "北京淘电影"],
        "淘精彩": ["IPTV淘精彩", "北京IPTV淘精彩", "北京淘精彩"],
        "淘剧场": ["IPTV淘剧场", "北京IPTV淘剧场", "北京淘剧场"],
        "淘4K": ["IPTV淘4K", "北京IPTV4K超清", "北京淘4K", "淘4K", "淘 4K"],
        "淘娱乐": ["IPTV淘娱乐", "北京IPTV淘娱乐", "北京淘娱乐"],
        "淘BABY": ["IPTV淘BABY", "北京IPTV淘BABY", "北京淘BABY", "IPTV淘baby", "北京IPTV淘baby", "北京淘baby"],
        "淘萌宠": ["IPTV淘萌宠", "北京IPTV萌宠TV", "北京淘萌宠"],
        "魅力足球": ["上海魅力足球"],
        "睛彩青少": ["睛彩羽毛球"],
        "求索纪录": ["求索记录", "求索纪录4K", "求索记录4K", "求索纪录 4K", "求索记录 4K"],
        "金鹰纪实": ["湖南金鹰纪实", "金鹰记实"],
        "纪实科教": ["北京纪实科教", "BRTV纪实科教", "纪实科教8K"],
        "星空卫视": ["星空衛視", "星空衛视", "星空卫視"],
        "CHANNEL[V]": ["CHANNEL-V", "Channel[V]"],
        "凤凰卫视中文台": ["凤凰中文", "凤凰中文台", "凤凰卫视中文", "凤凰卫视"],
        "凤凰卫视香港台": ["凤凰香港台", "凤凰卫视香港", "凤凰香港"],
        "凤凰卫视资讯台": ["凤凰资讯", "凤凰资讯台", "凤凰咨询", "凤凰咨询台", "凤凰卫视咨询台", "凤凰卫视资讯", "凤凰卫视咨询"],
        "凤凰卫视电影台": ["凤凰电影", "凤凰电影台", "凤凰卫视电影", "鳳凰衛視電影台", " 凤凰电影"],
        "茶频道": ["湖南茶频道"],
        "快乐垂钓": ["湖南快乐垂钓"],
        "先锋乒羽": ["湖南先锋乒羽"],
        "天元围棋": ["天元围棋频道"],
        "汽摩": ["重庆汽摩", "汽摩频道", "重庆汽摩频道"],
        "梨园频道": ["河南梨园频道", "梨园", "河南梨园"],
        "文物宝库": ["河南文物宝库"],
        "武术世界": ["河南武术世界"],
        "乐游": ["乐游频道", "上海乐游频道", "乐游纪实", "SiTV乐游频道", "SiTV 乐游频道"],
        "欢笑剧场": ["上海欢笑剧场4K", "欢笑剧场 4K", "欢笑剧场4K", "上海欢笑剧场"],
        "生活时尚": ["生活时尚4K", "SiTV生活时尚", "上海生活时尚"],
        "都市剧场": ["都市剧场4K", "SiTV都市剧场", "上海都市剧场"],
        "游戏风云": ["游戏风云4K", "SiTV游戏风云", "上海游戏风云"],
        "金色学堂": ["金色学堂4K", "SiTV金色学堂", "上海金色学堂"],
        "动漫秀场": ["动漫秀场4K", "SiTV动漫秀场", "上海动漫秀场"],
        "卡酷少儿": ["北京KAKU少儿", "BRTV卡酷少儿", "北京卡酷少儿", "卡酷动画"],
        "哈哈炫动": ["炫动卡通", "上海哈哈炫动"],
        "优漫卡通": ["江苏优漫卡通", "优漫漫画"],
        "金鹰卡通": ["湖南金鹰卡通"],
        "中国交通": ["中国交通频道"],
        "中国天气": ["中国天气频道"],
        "华数4K": ["华数低于4K", "华数4K电影", "华数爱上4K"],
        "TVB Jade": ["翡翠台"],
        "TVB Pearl": ["明珠台"],
        "Phoenix Chinese Channel": ["凤凰中文台"],
        "Phoenix InfoNews Channel": ["凤凰资讯台"],
        "CTi Variety": ["中天综合台"],
        "CTi News": ["中天新闻台"],
        "ETTV News": ["东森新闻台"],
        "ETTV Foreign Movies": ["东森洋片台"],
        "New Tang Dynasty TV": ["新科动漫"],
    }.items()
    for alias in aliases
}

# ================== 工具函数 ==================

def beijing_time_str(fmt: str = "%Y-%m-%d %H:%M:%S") -> str:
    """
    返回当前北京时间字符串（UTC+8），确保跨平台时间一致。
    
    Args:
        fmt: 时间格式字符串
    
    Returns:
        格式化后的北京时间字符串
    """
    beijing_tz = datetime.timezone(datetime.timedelta(hours=8))
    return datetime.datetime.now(beijing_tz).strftime(fmt)


def setup_logger() -> None:
    """初始化日志系统，支持 DEBUG 环境变量控制日志级别"""
    log_level = logging.DEBUG if os.getenv("DEBUG") else logging.INFO
    logging.basicConfig(
        level=log_level,
        format='%(asctime)s | %(levelname)-8s | %(message)s',
        datefmt='%Y-%m-%d %H:%M:%S'
    )


def verify_and_log(filepath: str, desc: str, critical: bool = False) -> bool:
    """
    验证文件是否存在、非空、可读，并记录日志。
    
    Args:
        filepath: 文件路径
        desc: 描述信息
        critical: 是否为关键文件（失败则抛异常）
    
    Returns:
        是否验证通过
    """
    abs_path = os.path.abspath(filepath)
    exists = os.path.exists(filepath)
    size = os.path.getsize(filepath) if exists else 0
    readable = False
    if exists and size > 0:
        try:
            with open(filepath, 'r', encoding='utf-8') as f:
                _ = f.read(100)
            readable = True
        except Exception:
            pass

    if exists and size > 0 and readable:
        logging.info(f"✅ {desc} | 路径: {abs_path} | 大小: {size:,} bytes")
        return True
    else:
        status = []
        if not exists:
            status.append("不存在")
        elif size == 0:
            status.append("为空(0 bytes)")
        else:
            status.append("不可读")
        msg = f"❌ {desc} 失败! 状态: {' + '.join(status)} | 路径: {abs_path}"
        if critical:
            raise RuntimeError(msg)
        logging.error(msg)
        return False


def save_debug(content: Any, filepath: str, desc: str) -> None:
    """
    保存调试中间文件（JSON 或文本），并验证是否成功写入。
    
    Args:
        content: 要保存的内容（str 或 dict/list）
        filepath: 保存路径
        desc: 描述信息
    """
    try:
        with open(filepath, 'w', encoding='utf-8') as f:
            if isinstance(content, str):
                f.write(content)
            else:
                json.dump(content, f, ensure_ascii=False, indent=2)
        verify_and_log(filepath, f"[中间] {desc}")
    except Exception as e:
        logging.error(f"⚠️ 保存 {desc} 失败: {e}")


def cleanup_debug_files() -> None:
    """
    自动删除所有调试中间文件。
    若设置了环境变量 DEBUG=1，则保留文件供排查。
    """
    if os.getenv("DEBUG"):
        logging.info("💡 DEBUG 模式启用，保留所有 debug_* 文件")
        return

    removed = 0
    for f in Config.DEBUG_FILES:
        if os.path.exists(f):
            try:
                os.remove(f)
                removed += 1
            except Exception as e:
                logging.warning(f"⚠️ 无法删除调试文件 {f}: {e}")
    if removed:
        logging.info(f"🧹 已自动清理 {removed} 个调试文件")


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
    从 URL 提取 host:port 作为主机唯一标识。
    例如: https://example.com:8080/path → example.com:8080
    """
    try:
        p = urlparse(u)
        port = p.port or (443 if p.scheme == "https" else 80)
        return f"{p.hostname}:{port}" if p.hostname else None
    except Exception:
        return None


def normalize_channel_name(name: str) -> str:
    """
    标准化频道名称，提升去重和分组准确性。
    
    步骤：
    1. 多频道拼接取主频道（如 A-B-C → A）
    2. 别名映射（长匹配优先）
    3. 移除括号内容
    4. 统一连接符为空格
    5. 移除冗余后缀（高清、HD、频道等）
    6. 标准化 CCTV 编号（CCTV01 → CCTV1）
    7. 标准化 CGTN 前缀
    """
    if not name or not isinstance(name, str):
        return "Unknown"
    original = name.strip()
    if not original:
        return "Unknown"

    # Step 1: 处理多频道拼接
    if "-" in original and len(original.split("-")) >= 3:
        original = original.split("-", 1)[0].strip()

    # Step 2: 精确别名映射（长别名优先）
    for alias in sorted(CHANNEL_ALIAS_MAP.keys(), key=lambda x: -len(x)):
        if alias in original:
            return CHANNEL_ALIAS_MAP[alias]

    # Step 3: 移除括号及内容
    name = re.sub(r'\s*[\(（【\[][^)）】\]]*[\)）】\]]\s*', '', original)

    # Step 4: 统一连接符为空格
    name = re.sub(r'[\s\-·•_\|]+', ' ', name)
    name = re.sub(r'\s+', ' ', name).strip()

    # Step 5: 移除冗余后缀
    suffix_pattern = (
        r'(?:'
        r'HD|FHD|UHD|4K|超高清|高清|蓝光|标清|'
        r'综合频道?|电视频道?|直播频道?|官方频道?|'
        r'频道|TV|台|官方|正版|流畅|备用|测试|'
        r'Ch|CH|Channel|咪咕|真|极速|'
        r')$'
    )
    name = re.sub(suffix_pattern, '', name, flags=re.IGNORECASE).strip()

    # Step 6: 智能标准化 CCTV 编号
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
    """判断文本是否为有效的 M3U/M3U8 内容（包含必要标识）"""
    txt = text.strip()
    return txt.startswith(Config.M3U_HEADER) and any(k in txt for k in ["#EXTINF", "#EXT-X-STREAM-INF"])


# ================== 新增：FFmpeg + OCR 验证工具 ==================

try:
    import pytesseract
    from PIL import Image
except ImportError:
    pytesseract = None
    Image = None


def is_ffmpeg_available() -> bool:
    """检查系统是否安装了 ffprobe（FFmpeg 套件）"""
    try:
        subprocess.run(["ffprobe", "-version"], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=True)
        return True
    except (subprocess.CalledProcessError, FileNotFoundError):
        return False


def is_ocr_available() -> bool:
    """检查 Tesseract OCR 和 Python 依赖是否可用"""
    if not pytesseract or not Image:
        return False
    try:
        subprocess.run(["tesseract", "-v"], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=True)
        return True
    except (subprocess.CalledProcessError, FileNotFoundError):
        return False


def run_ffprobe(url: str, timeout: int = 8) -> bool:
    """使用 ffprobe 验证流是否包含有效音视频"""
    try:
        cmd = [
            "ffprobe", "-v", "quiet", "-print_format", "json",
            "-show_streams", "-timeout", str(timeout * 1000000),
            "-user_agent", "Mozilla/5.0", url
        ]
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout + 2)
        if result.returncode != 0:
            return False
        data = json.loads(result.stdout)
        streams = data.get("streams", [])
        return len(streams) > 0 and any(s.get("codec_type") in ("video", "audio") for s in streams)
    except Exception:
        return False


def run_ocr_check(url: str, timeout: int = 15) -> bool:
    """对流截图并 OCR 检测软错误（如登录墙、区域限制）"""
    frame_path = f"/tmp/iptv_ocr_{abs(hash(url)) % 10000}.png"
    try:
        # 截图
        cmd = ["ffmpeg", "-y", "-hide_banner", "-loglevel", "error", "-i", url, "-ss", "1", "-vframes", "1", frame_path]
        proc = subprocess.run(cmd, capture_output=True, timeout=timeout + 2)
        if proc.returncode != 0 or not os.path.exists(frame_path):
            return False

        # OCR 识别
        img = Image.open(frame_path)
        text = pytesseract.image_to_string(img, lang='eng+chi_sim').lower()
        blacklist_words = (
            "login", "sign in", "geo-block", "not available", "invalid", "expired", "no signal"
            "test stream", "demo", "black screen", "请登录", "区域限制", "套餐", "购买", "扫码", "此画面", "服务器","失效", "切换", "403", "unauthorized"
        )
        for word in blacklist_words:
            if word.lower() in text:
                logging.debug(f"🚫 OCR 检测到黑名单词 '{word}' in {url}")
                os.remove(frame_path)
                return False
        os.remove(frame_path)
        return True
    except Exception as e:
        if os.path.exists(frame_path):
            os.remove(frame_path)
        logging.debug(f"OCR 检查异常 ({url}): {e}")
        return False


def is_valid_hls_stream(url: str, timeout: int = Config.TIMEOUT) -> Dict[str, Any]:
    """
    测试单个 URL 是否为有效 HLS 流。
    新增：对非 .m3u8 链接启用 FFmpeg + OCR 深度验证（若依赖可用）
    """
    headers = {"User-Agent": "Mozilla/5.0", "Accept": "*/*"}
    start = time.time()
    try:
        # HEAD 预检
        try:
            h = requests.head(url, timeout=timeout // 2, headers=headers, allow_redirects=True)
            if h.status_code not in (Config.HTTP_OK, 206, 301, 302):
                return {"alive": False, "latency": time.time() - start, "type": "dead", "reason": f"HEAD {h.status_code}"}
        except Exception:
            pass

        # GET 获取内容片段
        r = requests.get(url, timeout=timeout, headers=headers, stream=True, allow_redirects=True)
        if r.status_code != Config.HTTP_OK:
            return {"alive": False, "latency": time.time() - start, "type": "dead", "reason": f"GET {r.status_code}"}

        content = b""
        for chunk in r.iter_content(512):
            content += chunk
            if len(content) > 2048:
                break
        text = content.decode('utf-8', errors='ignore')
        latency = time.time() - start

        if not is_valid_hls_content(text):
            return {"alive": False, "latency": latency, "type": "not_hls", "reason": "Not valid M3U8"}

        stream_type = "master" if "#EXT-X-STREAM-INF" in text else ("media" if ".ts" in text.lower() else "hls")
        result = {"alive": True, "latency": latency, "type": stream_type, "reason": "OK"}

        # === 新增：对非标准 HLS 链接进行深度验证 ===
        if not url.endswith(Config.HLS_EXTENSIONS):
            # FFmpeg 验证流结构
            if is_ffmpeg_available():
                if not run_ffprobe(url, timeout=8):
                    result.update({"alive": False, "reason": "FFmpeg validation failed"})
                    return result

        return result
    except Exception as e:
        return {"alive": False, "latency": time.time() - start, "type": "error", "reason": str(e)}


def test_single_stream(url: str, timeout: int = Config.TIMEOUT) -> bool:
    """最终频道回检：轻量验证 + OCR（若可用）"""
    headers = {"User-Agent": "Mozilla/5.0", "Accept": "*/*"}
    try:
        r = requests.get(url, timeout=timeout, headers=headers, stream=True)
        if r.status_code != Config.HTTP_OK:
            return False
        content = b""
        for chunk in r.iter_content(512):
            content += chunk
            if len(content) > 2048:
                break
        text = content.decode('utf-8', errors='ignore')
        if not is_valid_hls_content(text):
            return False

        # === 新增：对非 .m3u8 链接启用 OCR 软错误检测 ===
        if not url.endswith(Config.HLS_EXTENSIONS) and is_ocr_available():
            return run_ocr_check(url, timeout=15)

        return True
    except Exception:
        return False


# ================== 原有解析与加载函数（保持不变） ==================

def parse_m3u(content: str) -> List[Dict[str, str]]:
    """
    解析 M3U 内容为频道列表。
    
    Returns:
        [{"name": "频道名", "url": "流地址"}, ...]
    """
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
    """
    将 TXT 格式（group,#genre# + 频道,URL）转换为标准 M3U。
    """
    lines = txt_content.splitlines()
    group_title = ""
    m3u_lines = [
        '#EXTM3U x-tvg-url="https://live.fanmingming.com/e.xml"',
        f'# Generated by IPTV Cleaner at {beijing_time_str()}'
    ]
    logo_url_base = "https://live.fanmingming.com/tv/"

    for line in lines:
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        if line.endswith(",#genre#"):
            group_title = line[:-8].strip()
        elif "," in line and line.count(",") == 1:
            parts = line.split(",", 1)
            channel_name = parts[0].strip()
            stream_url = parts[1].strip()
            if not stream_url.startswith(("http://", "https://")):
                continue
            tvg_id = re.sub(r'[\s\-]', '', channel_name)
            logo_url = f"{logo_url_base}{tvg_id}.png"
            m3u_lines.append(
                f'#EXTINF:-1 tvg-id="{tvg_id}" tvg-name="{tvg_id}" '
                f'tvg-logo="{logo_url}" group-title="{group_title}",{channel_name}'
            )
            m3u_lines.append(stream_url)
    return "\n".join(m3u_lines)


def detect_and_convert_to_m3u(content: str) -> str:
    """自动识别内容格式（M3U 或 TXT）并转换为标准 M3U"""
    stripped = content.strip()
    if not stripped:
        return ""
    upper_head = stripped[:200].upper()
    if Config.M3U_HEADER in upper_head and "#EXTINF" in upper_head:
        lines = [line for line in stripped.splitlines() if not line.strip().upper().startswith(Config.M3U_HEADER)]
        return "\n".join([Config.M3U_HEADER] + lines)
    else:
        return txt2m3u_content(stripped)


def load_blacklist() -> Tuple[Set[str], Set[str]]:
    """
    智能加载黑名单，区分两种模式：
    - 仅主机名（通配）：阻止该主机所有端口
    - 主机名+端口（精确）：阻止特定端口组合
    
    Returns:
        (host_only_set, host_with_port_set)
    """
    host_only = set()
    host_with_port = set()
    
    if not os.path.exists(Config.BLACKLIST_FILE):
        logging.info(f"ℹ️  黑名单文件不存在，跳过过滤")
        return host_only, host_with_port
    
    try:
        with open(Config.BLACKLIST_FILE, 'r', encoding='utf-8') as f:
            for line_num, line in enumerate(f, 1):
                raw = line.strip()
                if not raw or raw.startswith("#"):
                    continue
                    
                # 标准化为小写
                entry = raw.lower()
                
                # 分离两种模式
                if ':' in entry:
                    # 格式：host:port（精确匹配）
                    parts = entry.split(':', 1)
                    host = parts[0].strip()
                    port_str = parts[1].strip()
                    
                    # 验证端口有效性
                    if host and port_str.isdigit():
                        host_with_port.add(f"{host}:{port_str}")
                        logging.debug(f"📝 加载精确黑名单: {host}:{port_str}")
                    else:
                        logging.warning(f"⚠️  第{line_num}行无效的host:port格式: {raw}")
                else:
                    # 格式：host（通配匹配）
                    host_only.add(entry.strip())
                    logging.debug(f"📝 加载通配黑名单: {entry}")
        
        logging.info(f"🛡️  黑名单加载完成: {len(host_only)}个通配 + {len(host_with_port)}个精确")
        
    except Exception as e:
        logging.error(f"❌ 读取黑名单失败: {e}")
    
    return host_only, host_with_port

def is_blocked_by_blacklist(url: str, host_only_set: Set[str], host_with_port_set: Set[str]) -> bool:
    """
    智能判断URL是否应被黑名单阻止
    
    Args:
        url: 要检查的URL
        host_only_set: 仅主机名集合（匹配所有端口）
        host_with_port_set: 主机名+端口集合（精确匹配）
    
    Returns:
        True表示应阻止，False表示放行
    """
    try:
        parsed = urlparse(url)
        hostname = parsed.hostname
        
        if not hostname:
            return False  # 无效URL
        
        # 标准化主机名
        hostname_lower = hostname.lower()
        
        # 获取端口（处理默认端口）
        if parsed.port:
            port = parsed.port
        else:
            # 根据协议使用默认端口
            port = 443 if parsed.scheme == 'https' else 80
        
        # 构造精确匹配键
        exact_key = f"{hostname_lower}:{port}"
        
        # 第一步：精确匹配（优先级高）
        if exact_key in host_with_port_set:
            logging.debug(f"🚫 精确黑名单匹配: {url} → {exact_key}")
            return True
        
        # 第二步：通配匹配
        if hostname_lower in host_only_set:
            logging.debug(f"🚫 通配黑名单匹配: {url} → {hostname_lower}")
            return True
        
        return False
        
    except Exception as e:
        logging.warning(f"⚠️  黑名单检查异常 URL={url}: {e}")
        return False  # 出错时不阻止


# ================== 核心流程函数（保持不变） ==================

def load_sources() -> Tuple[str, List[Dict[str, Any]]]:
    """
    加载远程 + 本地源，返回合并后的 M3U 内容 和 源加载详情列表。
    
    Returns:
        (merged_m3u_content: str, source_load_details: List[dict])
    """
    source_details: List[Dict[str, Any]] = []

    # --- 加载远程源 ---
    if not os.path.exists(Config.BASE_URL_FILE):
        raise FileNotFoundError(f"❌ 配置文件未找到: {os.path.abspath(Config.BASE_URL_FILE)}")

    remote_urls: List[str] = []
    with open(Config.BASE_URL_FILE, "r", encoding="utf-8") as f:
        for i, line in enumerate(f, 1):
            raw = line.strip()
            if raw and not raw.startswith("#") and raw.startswith(("http://", "https://")):
                remote_urls.append(raw)
            elif raw and not raw.startswith("#"):
                logging.warning(f"⚠️  忽略无效URL (第{i}行): {raw}")
    if not remote_urls:
        raise ValueError("baseURL.txt中无有效源URL")

    s = requests.Session()
    s.headers.update({"User-Agent": "Mozilla/5.0"})

    def fetch(u: str) -> Tuple[List[str], Dict[str, Any]]:
        """获取单个远程源内容"""
        detail = {"type": "remote", "url": u, "success": False, "error": "", "line_count": 0}
        try:
            r = s.get(u, timeout=10)
            if r.status_code == Config.HTTP_OK:
                raw_text = r.text
                converted = detect_and_convert_to_m3u(raw_text)
                if not converted.strip():
                    detail["error"] = "内容为空或无法解析"
                    return [], detail
                lines = [line for line in converted.splitlines() if not line.strip().upper().startswith(Config.M3U_HEADER)]
                detail.update({"success": True, "line_count": len(lines)})
                return lines, detail
            else:
                detail["error"] = f"HTTP {r.status_code}"
                return [], detail
        except Exception as e:
            detail["error"] = str(e)
            return [], detail

    merged = [Config.M3U_HEADER]
    with ThreadPoolExecutor(max_workers=min(10, len(remote_urls))) as executor:
        futures = [executor.submit(fetch, u) for u in remote_urls]
        for future in as_completed(futures):
            lines, detail = future.result()
            merged.extend(lines)
            source_details.append(detail)

    remote_content = "\n".join(merged)

    # --- 加载本地源 ---
    local_dir = "local_playlists"
    local_contents: List[str] = []
    if os.path.exists(local_dir):
        for fname in os.listdir(local_dir):
            if not fname.lower().endswith(('.txt', '.m3u')):
                continue
            fpath = os.path.join(local_dir, fname)
            detail = {"type": "local", "path": fpath, "success": False, "error": "", "line_count": 0}
            try:
                with open(fpath, 'r', encoding='utf-8') as f:
                    raw = f.read()
                if fname.lower().endswith('.txt'):
                    m3u_content = txt2m3u_content(raw)
                    logging.info(f"🔄 已转换本地 TXT 文件: {fpath}")
                else:
                    m3u_content = raw
                    logging.info(f"📥 已加载本地 M3U 文件: {fpath}")
                local_contents.append(m3u_content)
                detail.update({"success": True, "line_count": len(m3u_content.splitlines())})
            except Exception as e:
                detail["error"] = str(e)
                logging.error(f"❌ 加载本地文件失败: {fpath} | {e}")
            source_details.append(detail)
    else:
        logging.info("ℹ️  本地源目录 baseM3U 不存在，跳过本地文件加载")

    all_contents = [remote_content] + local_contents
    raw_content = "\n".join(all_contents).strip()
    if not raw_content:
        raise RuntimeError("所有源（远程+本地）均为空或加载失败")

    logging.info(f"🔗 总共合并了 {len(local_contents) + 1} 份源内容（1远程 + {len(local_contents)}本地）")
    save_debug(raw_content, Config.DEBUG_FILES[0], "合并原始M3U")
    return raw_content, source_details


def test_hosts_two_phase(host_to_urls: Dict[str, List[str]]) -> Dict[str, Dict[str, Any]]:
    """
    两阶段主机测速：
    1. 初筛：使用代表性 .m3u8 URL 快速初筛
    2. 回查：对失败主机尝试最多3个备选流进行回查
    
    Returns:
        host_quality: {host: {alive, latency, type, representative_url, trials}}
    """
    # 构建主机数据（已去重）
    host_data: Dict[str, Dict[str, Any]] = {}
    for host, urls in host_to_urls.items():
        rep_url = next((u for u in urls if u.endswith(Config.HLS_EXTENSIONS)), urls[0]) if urls else None
        host_data[host] = {"all_urls": urls, "rep_url": rep_url}

    host_quality: Dict[str, Dict[str, Any]] = {}

    # === 第一阶段：初筛 ===
    initial_results: Dict[str, Dict[str, Any]] = {}
    with ThreadPoolExecutor(max_workers=Config.MAX_WORKERS) as executor:
        future_to_host = {
            executor.submit(is_valid_hls_stream, data["rep_url"]): host
            for host, data in host_data.items() if data["rep_url"]
        }
        for future in as_completed(future_to_host):
            host = future_to_host[future]
            result = future.result()
            initial_results[host] = result
            if result["alive"]:
                host_quality[host] = {
                    "alive": True,
                    "latency": result["latency"],
                    "type": result["type"],
                    "representative_url": host_data[host]["rep_url"],
                    "trials": 1
                }

    # === 第二阶段：失败回查 ===
    hosts_to_retry: List[Tuple[str, List[str]]] = []
    for host, data in host_data.items():
        if host not in host_quality:
            candidates = [u for u in data["all_urls"] if u != data["rep_url"]]
            if candidates:
                hosts_to_retry.append((host, candidates[:3]))  # 最多3个
            else:
                host_quality[host] = {
                    "alive": False,
                    "latency": 999,
                    "type": "no_fallback",
                    "representative_url": data["rep_url"],
                    "trials": 1
                }

    logging.info(f"🔄 初筛失败主机数: {len(hosts_to_retry)}，开始二次测速...")

    if hosts_to_retry:
        def fallback_test(args: Tuple[str, List[str]]) -> Tuple[str, bool, Dict[str, Any], int]:
            host, candidates = args
            for i, url in enumerate(candidates):
                res = is_valid_hls_stream(url)
                if res["alive"]:
                    return host, True, {"latency": res["latency"], "type": res["type"], "url": url}, i + 1
            last_res = is_valid_hls_stream(candidates[-1]) if candidates else None
            return host, False, (last_res or {"latency": 999, "type": "all_failed"}), len(candidates)

        with ThreadPoolExecutor(max_workers=Config.MAX_WORKERS) as executor:
            futures = [executor.submit(fallback_test, (host, cands)) for host, cands in hosts_to_retry]
            for future in as_completed(futures):
                host, success, final_result, trials = future.result()
                rep_url = host_data[host]["rep_url"]
                if success:
                    host_quality[host] = {
                        "alive": True,
                        "latency": final_result["latency"],
                        "type": final_result["type"],
                        "representative_url": final_result["url"],
                        "trials": 1 + trials
                    }
                else:
                    host_quality[host] = {
                        "alive": False,
                        "latency": final_result["latency"],
                        "type": final_result["type"],
                        "representative_url": rep_url,
                        "trials": 1 + trials
                    }

    alive = sum(1 for r in host_quality.values() if r["alive"])
    survival_rate = alive / len(host_to_urls) * 100 if host_to_urls else 0
    logging.info(f"✅ 存活主机: {alive}/{len(host_to_urls)} ({survival_rate:.1f}%)")
    save_debug(host_quality, Config.DEBUG_FILES[3], "Host测速结果（两阶段）")
    return host_quality


def save_host_ranking(host_quality: Dict[str, Dict[str, Any]]) -> None:
    """保存主机测速排名（含完整URL）到 Markdown 文件"""
    ranking = []
    for host, result in host_quality.items():
        if not result.get("alive"):
            continue
        rep_url = result.get("representative_url", "")
        latency_ms = int(result["latency"] * 1000)
        stream_type = result.get("type", "unknown")
        trials = result.get("trials", 1)
        ranking.append({
            "host": host,
            "url": rep_url,
            "latency_ms": latency_ms,
            "type": stream_type,
            "trials": trials
        })

    ranking.sort(key=lambda x: x["latency_ms"])
    lines = [
        "# 🚀 主机测速排名（按延迟升序）",
        "",
        "| 主机 | 延迟(ms) | 类型 | 尝试次数 | 测速链接（完整）|",
        "|------|----------|------|----------|------------------|"
    ]
    for item in ranking:
        url_display = f"`{item['url']}`"
        lines.append(f"| `{item['host']}` | **{item['latency_ms']}** | `{item['type']}` | {item['trials']} | {url_display} |")

    save_debug("\n".join(lines), Config.DEBUG_FILES[4], "主机测速排名（含完整URL）")


def build_final_playlist(
    grouped: DefaultDict[str, List[Dict[str, str]]],
    url_to_host: Dict[str, str],
    host_quality: Dict[str, Dict[str, Any]]
) -> List[Dict[str, str]]:
    """
    构建最终播放列表（含频道级回退验证）。
    对每个频道，按主机延迟排序候选源，并逐个验证流是否真正可用。
    
    Returns:
        [{"channel", "original_name", "url"}, ...]
    """
    channel_to_candidates: Dict[str, List[Dict[str, Any]]] = {}
    for clean_name, items in grouped.items():
        candidates = []
        for item in items:
            url = item["url"]
            host = url_to_host.get(url)
            if host and host_quality.get(host, {}).get("alive"):
                latency = host_quality[host]["latency"]
                candidates.append({
                    "url": url,
                    "latency": latency,
                    "original_name": item["original_name"]
                })
        if candidates:
            candidates.sort(key=lambda x: x["latency"])
            channel_to_candidates[clean_name] = candidates

    final_channels: List[Dict[str, str]] = []
    for clean_name, candidates in channel_to_candidates.items():
        selected = None
        for cand in candidates:
            if test_single_stream(cand["url"]):
                selected = {
                    "channel": clean_name,
                    "original_name": cand["original_name"],
                    "url": cand["url"]
                }
                break
        if selected:
            final_channels.append(selected)
        else:
            logging.warning(f"⚠️  频道 '{clean_name}' 所有候选源均不可用，已跳过")

    logging.info(f"🎯 最终保留频道: {len(final_channels)}")
    return final_channels


def generate_outputs_and_notify(
    final_channels: List[Dict[str, str]],
    stats: Dict[str, Any],
    source_details: List[Dict[str, Any]],
    all_expected_channels: Set[str]
) -> None:
    """
    生成最终输出文件（M3U + Report）并发送 Bark 通知。
    新增：按 Config.GROUP_OUTPUT_ORDER 排序频道 + 可用/无源频道清单。
    """
    # --- 按指定顺序组织频道 ---
    group_to_channels: DefaultDict[str, List[Dict[str, str]]] = defaultdict(list)
    for item in final_channels:
        g = guess_group(item["original_name"])
        group_to_channels[g].append(item)

    # 按预设顺序排列分组
    ordered_groups: List[Tuple[str, List[Dict[str, str]]]] = []
    for group_name in Config.GROUP_OUTPUT_ORDER:
        if group_name in group_to_channels:
            ordered_groups.append((group_name, group_to_channels[group_name]))
    # 添加未在排序列表中的分组（理论上不会发生）
    for g, chs in group_to_channels.items():
        if g not in Config.GROUP_OUTPUT_ORDER:
            ordered_groups.append((g, chs))

    # --- 生成 M3U ---
    with open(Config.OUTPUT_FILE, "w", encoding="utf-8") as f:
        f.write('#EXTM3U x-tvg-url="https://live.fanmingming.com/europe.xml.gz"\n')
        for group_name, channels in ordered_groups:
            for item in channels:
                logo = extract_logo(item["channel"])
                f.write(
                    f'#EXTINF:-1 tvg-id="{item["channel"]}" tvg-name="{item["channel"]}" '
                    f'tvg-logo="{logo}" group-title="{group_name}",{item["channel"]}\n'
                    f'{item["url"]}\n'
                )
    verify_and_log(Config.OUTPUT_FILE, "[输出] 直播源M3U", critical=True)

    # --- 统计分组数量 ---
    group_count = defaultdict(int)
    for item in final_channels:
        group_count[guess_group(item["original_name"])] += 1

    # --- 生成报告 ---
    report = f"""# ✅ IPTV直播源清洗报告
>**生成时间**: {beijing_time_str()}<br>
>**存活率**: {stats['survival_rate']:.1f}%

## 📊 核心统计
| 项目 | 数量 |
|------|------|
| 原始频道 | {stats['raw_channels']} |
| 唯一主机 | {stats['unique_hosts']} |
| 存活主机 | {stats['alive_hosts']} |
| 最终频道 | {stats['final_channels']} |

## 🔗 源加载详情
| 类型 | 标识 | 状态 | 频道数 | 错误信息 |
|------|------|------|------|----------|
"""

    for detail in source_details:
        if detail["type"] == "remote":
            url_full = detail["url"]
            # 使用反引号包裹完整 URL，Markdown 中仍可点击
            status = "✅ 成功" if detail["success"] else "❌ 失败"
            error = detail.get("error", "") or "-"
            report += f"| 远程 | `{url_full}` | {status} | {detail['line_count']} | {error} |\n"
        else:
            filename = os.path.basename(detail["path"])
            status = "✅ 成功" if detail["success"] else "❌ 失败"
            error = detail.get("error", "") or "-"
            report += f"| 本地 | `{filename}` | {status} | {detail['line_count']} | {error} |\n"

    report += "\n## 📺 分组分布\n"
    for g, c in sorted(group_count.items(), key=lambda x: x[1], reverse=True):
        report += f"- **{g}**: {c} 个\n"

    # --- 新增：可用频道与无源频道清单 ---
    available_set = {item["channel"] for item in final_channels}
    unavailable_channels = sorted(all_expected_channels - available_set)

    report += "\n## 📋 可用频道列表\n"
    for ch in sorted(available_set):
        report += f"- {ch}\n"

    report += "\n## ❌ 无有效源的频道\n"
    if unavailable_channels:
        for ch in unavailable_channels:
            report += f"- {ch}\n"
    else:
        report += "- 无\n"

    with open(Config.REPORT_FILE, "w", encoding="utf-8") as f:
        f.write(report)
    verify_and_log(Config.REPORT_FILE, "[输出] 清洗报告")

    # --- Bark 通知（支持 Config + 环境变量）---
    env_key = os.getenv("BARK_DEVICE_KEY", "").strip()
    config_key = Config.BARK_DEVICE_KEY.strip()
    bark_key = env_key or config_key  # 环境变量优先
    
    if bark_key:
        top_groups = sorted(stats['groups'].items(), key=lambda x: x[1], reverse=True)[:8]
        group_lines = [f"• {g}: {c}个" for g, c in top_groups]
        if len(stats['groups']) > 8:
            group_lines.append(f"• ...（共{len(stats['groups'])}组）")

        body = (
            f"⌚️ {beijing_time_str()}\n"
            "━━━━━━━━━━━━━━━━\n"
            "📊 核心数据\n"
            f"  原始频道: {stats['raw_channels']}\n"
            f"  唯一主机: {stats['unique_hosts']}\n"
            f"  存活主机: {stats['alive_hosts']} ({stats['survival_rate']:.1f}%)\n"
            f"  最终频道: {stats['final_channels']}\n"
            "\n📺 保留频道分组\n" +
            "\n".join(group_lines) +
            "\n\n💡 完整报告: report.md"
        )
        try:
            safe_title = quote("📺 IPTV源清洗完成", safe='')
            safe_body = quote(body, safe='')
            url = f"https://api.day.app/{bark_key}/{safe_title}/{safe_body}?group=iptv&icon=📺&level=active"
            resp = requests.get(url, timeout=10)
            logging.info("✅ Bark通知发送成功" if resp.status_code == 200 else f"⚠️ Bark失败 (HTTP {resp.status_code})")
        except Exception as e:
            logging.error(f"❌ Bark异常: {e}")
    else:
        logging.info("ℹ️  未配置 BARK_DEVICE_KEY（Config 或环境变量），跳过通知")


# ================== 主入口 ==================
def main() -> None:
    """主执行流程"""
    setup_logger()
    logger = logging.getLogger()
    cwd = os.getcwd()
    logger.info(f"\n{'='*60}")
    logger.info(f"📍 脚本工作目录: {cwd}")
    logger.info(f"💡 请确认此目录包含: {Config.BASE_URL_FILE}")
    logger.info(f"{'='*60}\n")

    # === 检查可选依赖 ===
    if is_ffmpeg_available():
        logging.info("✅ FFmpeg 可用，将对非 .m3u8 链接启用深度流验证")
    else:
        logging.warning("⚠️  FFmpeg 未安装，跳过深度流验证")

    if is_ocr_available():
        logging.info("✅ OCR 可用，将在最终回检中启用画面软错误检测")
    else:
        logging.warning("⚠️  OCR 依赖缺失，跳过画面检测")

    try:
        test_file = ".write_check.tmp"
        with open(test_file, 'w') as f:
            f.write("dir_check")
        os.remove(test_file)
        logger.info(f"✅ 工作目录可写验证通过")
    except Exception as e:
        logger.critical(f"❌ 工作目录不可写! 请检查权限: {e}")
        return

    # === 加载源 ===
    raw_content, source_details = load_sources()

    # === 加载黑名单 ===
    host_only_blacklist, exact_blacklist = load_blacklist()

    # === 解析原始频道并过滤黑名单 ===
    raw_channels = parse_m3u(raw_content)
    logging.info(f"🧹 解析到 {len(raw_channels)} 条原始频道记录")

    # 过滤黑名单
    filtered_raw_channels = []
    blocked_count = 0

    for ch in raw_channels:
        url = ch["url"]
        if not is_valid_url(url):
            continue
            
        # 智能黑名单检查
        if is_blocked_by_blacklist(url, host_only_blacklist, exact_blacklist):
            blocked_count += 1
            if blocked_count <= 5:  # 只记录前5个，避免日志过多
                logging.debug(f"🚫 黑名单跳过: {ch['name']} → {url}")
            continue
            
        filtered_raw_channels.append(ch)

    if blocked_count > 0:
        logging.info(f"🛡️  黑名单过滤: 阻止了 {blocked_count} 个频道")
    else:
        logging.info("ℹ️  黑名单未匹配到任何频道")

    # 分组（去重）
    grouped: DefaultDict[str, List[Dict[str, str]]] = defaultdict(list)
    seen_urls: Set[str] = set()
    for ch in filtered_raw_channels:
        clean_name = normalize_channel_name(ch["name"])
        if ch["url"] not in seen_urls:
            seen_urls.add(ch["url"])
            grouped[clean_name].append({"original_name": ch["name"], "url": ch["url"]})
    logging.info(f"📦 分组后共 {len(grouped)} 个独立频道")
    save_debug(dict(grouped), Config.DEBUG_FILES[1], "分组频道数据")

    # 重建 url_to_host（仅非黑名单）
    url_to_host: Dict[str, str] = {}
    for items in grouped.values():
        for item in items:
            if (host := get_host_key(item["url"])):
                url_to_host[item["url"]] = host
    logging.info(f"🌐 唯一主机数: {len(url_to_host)}")
    save_debug({h: u for u, h in url_to_host.items()}, Config.DEBUG_FILES[2], "Host映射数据")

    # === 测速与构建最终列表 ===
    host_to_urls = defaultdict(list)
    for items in grouped.values():
        for item in items:
            if (host := url_to_host.get(item["url"])):
                host_to_urls[host].append(item["url"])

    host_quality = test_hosts_two_phase(dict(host_to_urls))
    save_host_ranking(host_quality)
    final_channels = build_final_playlist(grouped, url_to_host, host_quality)

    # === 统计 ===
    alive_hosts = sum(1 for r in host_quality.values() if r["alive"])
    survival_rate = alive_hosts / len(host_to_urls) * 100 if host_to_urls else 0
    group_count = defaultdict(int)
    for item in final_channels:
        group_count[guess_group(item["original_name"])] += 1

    stats = {
        "raw_channels": len(grouped),
        "unique_hosts": len(host_to_urls),
        "alive_hosts": alive_hosts,
        "survival_rate": survival_rate,
        "final_channels": len(final_channels),
        "groups": dict(group_count)
    }

    all_expected_channels = set(grouped.keys())
    generate_outputs_and_notify(final_channels, stats, source_details, all_expected_channels)

    # === 自动清理调试文件 ===
    cleanup_debug_files()

    # === 终极确认 ===
    logger.info("\n" + "="*70)
    logger.info("🔍【终极确认】请核对以下文件路径")
    logger.info("="*70)
    for desc, fname in [(" cleaned M3U", Config.OUTPUT_FILE), ("Report", Config.REPORT_FILE)]:
        abs_path = os.path.abspath(fname)
        if os.path.exists(fname) and os.path.getsize(fname) > 0:
            logger.info(f"✅ {desc} | {abs_path}")
        else:
            logger.error(f"❌ {desc} 未找到! | {abs_path}")
    logger.info("="*70)
    logger.info(f"📌 工作目录: {cwd}")
    logger.info("="*70 + "\n")


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        logging.info("\n⚠️  用户中断执行")
        exit(1)
    except Exception as e:
        logging.exception(f"❌ 脚本执行异常: {e}")
        logging.info("💡 异常发生！中间文件已保留（若 DEBUG=1）")
        exit(1)
