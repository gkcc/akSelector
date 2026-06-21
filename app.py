import sys
import os
import glob
import html
import json
import random
import re
import shutil
import time
import urllib.error
import urllib.request
import zipfile
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple, Set
from xml.etree import ElementTree as ET

from PyQt6.QtWidgets import (
    QApplication, QMainWindow, QWidget,
    QVBoxLayout, QHBoxLayout, QGridLayout, QLabel,
    QPushButton, QTextEdit, QGroupBox, QMessageBox,
    QCheckBox, QComboBox, QListWidget, QListWidgetItem,
    QFrame, QSplitter, QSizePolicy, QDialog, QFormLayout,
    QSpinBox, QDialogButtonBox,
    QTreeWidget, QTreeWidgetItem, QHeaderView, QTabWidget
)
from PyQt6.QtCore import Qt, QModelIndex, QObject, QUrl, QSize, pyqtSignal
from PyQt6.QtGui import QStandardItemModel, QStandardItem, QPixmap, QColor, QBrush


ARKHAMDB_BASE_URL = "https://zh.arkhamdb.com"
ARKHAMDB_CARDS_URL = f"{ARKHAMDB_BASE_URL}/api/public/cards/"
USER_AGENT = "ArkhamInvestigatorPicker/1.0"

DATA_DIR_NAME = "data"
ARKHAMDB_CACHE_FILE = "arkhamdb_investigators.json"
PLAYER_COUNTS_FILE = "player_counts.json"
PLAY_RECORDS_FILE = "play_records.json"
SIMPLIFIED_OVERRIDES_FILE = "simplified_overrides.json"

FACTION_CN = {
    "guardian": "守卫者",
    "seeker": "探求者",
    "rogue": "流浪者",
    "mystic": "潜修者",
    "survivor": "求生者",
    "neutral": "所有",
}

PLAYER_COUNT_FIELD = {
    "小张": "play_zhang",
    "小胡": "play_hu",
}

LEGACY_NAME_CODE_OVERRIDES = {
    "艾格尼丝·贝克（平行）": "90017",
    "格洛丽亚·戈德伯格": "98019",
    "“灰堆”皮特（平行）": "90046",
    "派翠丝·海瑟薇": "06005",
    "塞拉斯·马什（小说）": "98013",
    "“倒霉蛋”奥图尔（平行）": "90008",
    "珍妮·巴恩斯（平行）": "90084",
    "蒙特雷·杰克（平行）": "90062",
    "温妮弗雷德·哈巴莫克": "60301",
    "黛西·沃克（平行）": "90001",
    "诺曼·威瑟斯（小说）": "98007",
    "罗兰·班克斯（平行）": "90024",
    "罗兰·班克斯（小说）": "98004",
    "佐伊·萨马拉斯（平行）": "90059",
    "卡洛琳·弗恩（小说）": "98010",
}

SPECIAL_DUPLICATE_INVESTIGATOR_CODES = {"98004", "98010", "98016", "99001"}

CYCLE_SORT_RULES = [
    (("基础游戏",), (1, 0)),
    (("敦威治遗产",), (2, 0)),
    (("卡尔克萨之路",), (3, 0)),
    (("失落的时代",), (4, 0)),
    (("万象无终",), (5, 0)),
    (("食梦者",), (6, 0)),
    (("纳撒尼尔·曹",), (6, 10)),
    (("哈维·沃尔特斯",), (6, 20)),
    (("温妮弗雷德·哈巴",), (6, 30)),
    (("杰奎琳·法恩",), (6, 40)),
    (("斯特拉·克拉克",), (6, 50)),
    (("调查员新手包",), (6, 90)),
    (("印斯茅斯暗潮",), (7, 0)),
    (("暗与地球之界",), (8, 0)),
    (("绯红密钥",), (9, 0)),
    (("铁杉谷盛宴",), (10, 0)),
    (("The Drowned City", "淹没之城"), (11, 0)),
    (("Core Set (2026)",), (12, 0)),
    (("基础游戏（2026）",), (12, 0)),
    (("小说调查员",), (80, 0)),
    (("The Dirge of Reason",), (80, 5)),
    (("Hour of the Huntress",), (80, 10)),
    (("Ire of the Void",), (80, 20)),
    (("The Deep Gate",), (80, 30)),
    (("Dark Revelations",), (80, 40)),
    (("Blood of Baalshandor",), (80, 45)),
    (("To Fight the Black Wind",), (80, 60)),
    (("调查员扩展包",), (85, 0)),
    (("André Patel",), (80, 50)),
    (("Carolyn Fern",), (80, 60)),
    (("Marie Lambeau",), (80, 70)),
    (("Miguel de la Cruz",), (80, 80)),
    (("Tommy Muldoon",), (80, 90)),
    (("平行调查员挑战",), (90, 0)),
    (("死亡阅读",), (90, 10)),
    (("孤注一掷",), (90, 20)),
    (("血业轮回",), (90, 30)),
    (("照章行事",), (90, 40)),
    (("赤潮升涌",), (90, 50)),
    (("On the Road Again",), (90, 60)),
    (("安魂镇息",), (90, 70)),
    (("Path of the Righteous",), (90, 80)),
    (("Relics of the Past",), (90, 90)),
    (("Hunting for Answers",), (90, 100)),
    (("Pistols and Pearls",), (90, 110)),
    (("Aura of Faith",), (90, 120)),
    (("Enthralling Encore",), (90, 130)),
    (("番外调查员",), (95, 0)),
    (("The Blob That Ate Everything ELSE!",), (95, 0)),
]

STARTER_DECK_CYCLE_PATTERNS = (
    "纳撒尼尔·曹",
    "哈维·沃尔特斯",
    "温妮弗雷德·哈巴",
    "杰奎琳·法恩",
    "斯特拉·克拉克",
)

NOVEL_CYCLE_PATTERNS = (
    "Hour of the Huntress",
    "The Dirge of Reason",
    "Ire of the Void",
    "The Deep Gate",
    "Dark Revelations",
    "Blood of Baalshandor",
    "To Fight the Black Wind",
)

INVESTIGATOR_EXPANSION_PATTERNS = (
    "André Patel",
    "Carolyn Fern",
    "Marie Lambeau",
    "Miguel de la Cruz",
    "Tommy Muldoon",
)

PARALLEL_CHALLENGE_PATTERNS = (
    "死亡阅读",
    "孤注一掷",
    "血业轮回",
    "照章行事",
    "赤潮升涌",
    "On the Road Again",
    "安魂镇息",
    "Path of the Righteous",
    "Relics of the Past",
    "Hunting for Answers",
    "Pistols and Pearls",
    "Aura of Faith",
    "Enthralling Encore",
)

NON_STARTING_INVESTIGATOR_PATTERNS = (
    "不能被选为起始调查员",
    "不能被選為起始調查員",
    "绑定(",
    "綁定(",
    "cannot be chosen as your starting investigator",
    "cannot be chosen as a starting investigator",
    "bonded(",
    "bonded (",
)

try:
    from opencc import OpenCC
    _OPENCC = OpenCC("t2s")
except Exception:
    _OPENCC = None

T2S_FALLBACK_TABLE = str.maketrans({
    "夢": "梦",
    "賞": "赏",
    "獵": "猎",
    "羅": "罗",
    "蘭": "兰",
    "爾": "尔",
    "貝": "贝",
    "齊": "齐",
    "傑": "杰",
    "瑪": "玛",
    "麗": "丽",
    "黛": "黛",
    "溫": "温",
    "亞": "亚",
    "當": "当",
    "斯": "斯",
    "調": "调",
    "查": "查",
    "員": "员",
    "職": "职",
    "衛": "卫",
    "護": "护",
    "倖": "幸",
    "運": "运",
    "師": "师",
    "學": "学",
    "術": "术",
    "獨": "独",
    "佔": "占",
    "啟": "启",
    "陰": "阴",
    "謀": "谋",
    "遺": "遗",
    "產": "产",
    "基": "基",
    "礎": "础",
    "遊": "游",
    "戲": "戏",
})


class WorkerSignals(QObject):
    log_ready = pyqtSignal(str)
    sync_ready = pyqtSignal(object, str, str)


# =============== 数据模型 ===============

@dataclass
class RelatedCard:
    code: str
    name: str
    category: str
    card_type: str
    pack: str
    img1: str
    img2: str
    card_url: str = ""


@dataclass
class Investigator:
    cycle: str          # 循环
    name: str           # 调查员
    alias: str          # 别称
    career: str         # 职介
    sub_career: str     # 副职介（可能包含多个，用“、”等分隔）
    play_zhang: int     # 小张玩过几次
    play_hu: int        # 小胡玩过几次
    img1: str           # 图片1绝对路径（正面）
    img2: str           # 图片2绝对路径（背面）
    code: str = ""      # ArkhamDB 卡牌编号
    source: str = ""    # 数据来源
    card_url: str = ""  # ArkhamDB 页面
    related_cards: List[RelatedCard] = field(default_factory=list)


@dataclass
class PickRecord:
    inv: Investigator
    player: Optional[str]  # 为哪位玩家选的，比如 "小张" / "小胡" / None
    committed: bool = False
    log_id: str = ""


# =============== 工具函数 ===============

def _data_dir(base_dir: str) -> str:
    path = os.path.join(base_dir, DATA_DIR_NAME)
    os.makedirs(path, exist_ok=True)
    return path


def _cache_path(base_dir: str, filename: str) -> str:
    return os.path.join(_data_dir(base_dir), filename)


def _read_json(path: str, default: Any) -> Any:
    if not os.path.exists(path):
        return default
    try:
        with open(path, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return default


def _write_json(path: str, data: Any):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=2)


def _request_json(url: str) -> Any:
    req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    with urllib.request.urlopen(req, timeout=30) as resp:
        return json.load(resp)


def _is_url(value: str) -> bool:
    return value.startswith("http://") or value.startswith("https://")


def _arkhamdb_url(path_or_url: str) -> str:
    if not path_or_url:
        return ""
    if _is_url(path_or_url):
        return path_or_url
    if path_or_url.startswith("/"):
        return ARKHAMDB_BASE_URL + path_or_url
    return f"{ARKHAMDB_BASE_URL}/{path_or_url}"


def _safe_filename_part(text: str) -> str:
    replacements = {
        "<": "＜",
        ">": "＞",
        ":": "：",
        "\"": "”",
        "/": "／",
        "\\": "＼",
        "|": "｜",
        "?": "？",
        "*": "＊",
    }
    cleaned = "".join(replacements.get(ch, ch) for ch in str(text or "").strip())
    cleaned = re.sub(r"[\x00-\x1f]", "", cleaned).strip(" .")
    return cleaned or "未命名调查员"


def _cycle_sort_key(cycle: str) -> Tuple[int, int, str]:
    value = _to_simplified(cycle)
    for patterns, order in CYCLE_SORT_RULES:
        if any(pattern == value for pattern in patterns):
            return order[0], order[1], value
    for patterns, order in CYCLE_SORT_RULES:
        if any(pattern in value for pattern in patterns):
            return order[0], order[1], value
    return 99, 0, value


def _sort_cycles(cycles: List[str]) -> List[str]:
    return sorted(cycles, key=_cycle_sort_key)


def _cycle_display_group(cycle: str) -> str:
    value = _to_simplified(cycle)
    if any(pattern in value for pattern in STARTER_DECK_CYCLE_PATTERNS):
        return "调查员新手包"
    if any(pattern in value for pattern in NOVEL_CYCLE_PATTERNS):
        return "小说调查员"
    if any(pattern in value for pattern in INVESTIGATOR_EXPANSION_PATTERNS):
        return "调查员扩展包"
    if any(pattern in value for pattern in PARALLEL_CHALLENGE_PATTERNS):
        return "平行调查员挑战"
    if value == "Promo":
        return "番外调查员"
    if "The Blob That Ate Everything ELSE!" in value:
        return "番外调查员"
    if "The Drowned City" in value:
        return "淹没之城调查员扩充"
    if "Core Set (2026)" in value:
        return "基础游戏（2026）"
    return value


def _cycle_group_map(investigators: List["Investigator"]) -> Dict[str, Set[str]]:
    groups: Dict[str, Set[str]] = {}
    for inv in investigators:
        group = _cycle_display_group(inv.cycle)
        groups.setdefault(group, set()).add(inv.cycle)
    return {group: groups[group] for group in _sort_cycles(list(groups.keys()))}


def _cycle_folder_name(cycle: str) -> str:
    major, minor, _ = _cycle_sort_key(cycle)
    prefix = f"{major:02d}" if minor == 0 else f"{major:02d}.{minor:02d}"
    return f"{prefix} {_safe_filename_part(_to_simplified(cycle))}"


def _image_folder_name(cycle: str) -> str:
    return _cycle_folder_name(_cycle_display_group(cycle))


def _investigator_sort_key(inv: Investigator) -> Tuple[int, int, str, str]:
    major, minor, cycle = _cycle_sort_key(inv.cycle)
    return major, minor, cycle, inv.name


def _image_ext_from_url(url: str) -> str:
    suffix = Path(url.split("?", 1)[0]).suffix.lower()
    if suffix in {".png", ".jpg", ".jpeg", ".webp"}:
        return suffix
    return ".png"


def _legacy_image_cache_path(base_dir: str, url: str) -> str:
    filename = os.path.basename(url.split("?", 1)[0])
    if not filename:
        filename = str(abs(hash(url))) + ".png"
    images_dir = os.path.join(_data_dir(base_dir), "images")
    return os.path.abspath(os.path.join(images_dir, filename))


def _named_image_cache_path(
    base_dir: str,
    cycle: str,
    investigator_name: str,
    side: str,
    url: str,
    code: str = "",
    name_is_duplicate: bool = False,
) -> str:
    safe_name = _safe_filename_part(investigator_name)
    if name_is_duplicate and code:
        filename = f"{safe_name}（{code}，{side}）{_image_ext_from_url(url)}"
    else:
        filename = f"{safe_name}（{side}）{_image_ext_from_url(url)}"

    images_root = os.path.join(_data_dir(base_dir), "images")
    target = os.path.abspath(os.path.join(images_root, _image_folder_name(cycle), filename))
    legacy = os.path.abspath(os.path.join(images_root, _cycle_folder_name(cycle), filename))

    if target != legacy and not os.path.exists(target) and os.path.exists(legacy) and os.path.getsize(legacy) > 0:
        os.makedirs(os.path.dirname(target), exist_ok=True)
        try:
            shutil.move(legacy, target)
        except Exception:
            try:
                shutil.copy2(legacy, target)
            except Exception:
                pass

    return target


def _named_related_card_cache_path(
    base_dir: str,
    cycle: str,
    investigator_name: str,
    card_name: str,
    side: str,
    url: str,
    code: str = "",
) -> str:
    safe_inv = _safe_filename_part(investigator_name)
    safe_card = _safe_filename_part(card_name)
    code_part = f"（{code}，{side}）" if code else f"（{side}）"
    filename = f"{safe_inv} - {safe_card}{code_part}{_image_ext_from_url(url)}"
    images_root = os.path.join(_data_dir(base_dir), "images")
    return os.path.abspath(os.path.join(
        images_root,
        _image_folder_name(cycle),
        "专属卡与弱点",
        filename,
    ))


def _local_image_path(base_dir: str, path: str) -> str:
    if not path:
        return ""
    if _is_url(path):
        cached = _legacy_image_cache_path(base_dir, path)
        return cached if os.path.exists(cached) and os.path.getsize(cached) > 0 else ""
    return path if os.path.exists(path) else ""


def _cache_remote_image(base_dir: str, url: str, target: Optional[str] = None) -> str:
    """
    下载 ArkhamDB 卡图到本地缓存；失败时返回空串，避免 UI 线程碰网络。
    """
    if not _is_url(url):
        return url

    target = target or _legacy_image_cache_path(base_dir, url)
    images_dir = os.path.join(_data_dir(base_dir), "images")
    os.makedirs(os.path.dirname(target), exist_ok=True)
    if os.path.exists(target) and os.path.getsize(target) > 0:
        return target

    flat_named = os.path.abspath(os.path.join(images_dir, os.path.basename(target)))
    if flat_named != target and os.path.exists(flat_named) and os.path.getsize(flat_named) > 0:
        try:
            shutil.move(flat_named, target)
            return target
        except Exception:
            try:
                shutil.copy2(flat_named, target)
                return target
            except Exception:
                pass

    legacy = _legacy_image_cache_path(base_dir, url)
    if legacy != target and os.path.exists(legacy) and os.path.getsize(legacy) > 0:
        try:
            shutil.move(legacy, target)
            return target
        except Exception:
            try:
                shutil.copy2(legacy, target)
                return target
            except Exception:
                pass

    try:
        req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
        with urllib.request.urlopen(req, timeout=20) as resp:
            content = resp.read()
        with open(target, "wb") as f:
            f.write(content)
        return target
    except Exception:
        return ""


def _card_lookup(cards: List[Dict[str, Any]]) -> Dict[str, Dict[str, Any]]:
    return {str(card.get("code") or ""): card for card in cards if card.get("code")}


def _deck_requirement_card_codes(card: Dict[str, Any]) -> List[str]:
    requirements = card.get("deck_requirements") or {}
    if not isinstance(requirements, dict):
        return []
    required = requirements.get("card") or {}
    if not isinstance(required, dict):
        return []

    codes: List[str] = []
    seen: Set[str] = set()
    for group_key, options in required.items():
        values: List[Any]
        if isinstance(options, dict):
            values = list(options.values())
        elif isinstance(options, list):
            values = options
        else:
            values = [options or group_key]

        for value in values:
            code = str(value or "").strip()
            if code and code not in seen:
                codes.append(code)
                seen.add(code)
    return codes


def _card_display_name(card: Dict[str, Any], overrides: Dict[str, Any]) -> str:
    simplified_name = _to_simplified(card.get("name") or card.get("real_name") or "")
    override = _get_simplified_override(overrides, card, simplified_name)
    return override.get("name") or simplified_name


def _card_display_pack(card: Dict[str, Any]) -> str:
    return _to_simplified(card.get("pack_name") or card.get("pack_code") or "")


def _card_to_related_card(
    card: Dict[str, Any],
    base_dir: Optional[str],
    investigator_cycle: str,
    investigator_name: str,
    overrides: Dict[str, Any],
) -> RelatedCard:
    code = str(card.get("code") or "")
    name = _card_display_name(card, overrides)
    card_type = _to_simplified(card.get("type_name") or card.get("type_code") or "")
    subtype = _to_simplified(card.get("subtype_name") or card.get("subtype_code") or "")
    category = "专属弱点" if str(card.get("subtype_code") or "") == "weakness" else "专属卡牌"
    if subtype and subtype not in {"弱点", "weakness"}:
        card_type = f"{card_type} / {subtype}" if card_type else subtype

    front_url = _arkhamdb_url(str(card.get("imagesrc") or ""))
    back_url = _arkhamdb_url(str(card.get("backimagesrc") or ""))
    if base_dir:
        img1 = _named_related_card_cache_path(
            base_dir, investigator_cycle, investigator_name, name, "正面", front_url, code
        ) if front_url else ""
        img2 = _named_related_card_cache_path(
            base_dir, investigator_cycle, investigator_name, name, "背面", back_url, code
        ) if back_url else ""
    else:
        img1 = front_url
        img2 = back_url

    return RelatedCard(
        code=code,
        name=name,
        category=category,
        card_type=card_type,
        pack=_card_display_pack(card),
        img1=img1,
        img2=img2,
        card_url=f"{ARKHAMDB_BASE_URL}/card/{code}" if code else "",
    )


def _related_cards_for_investigator(
    investigator_card: Dict[str, Any],
    all_cards_by_code: Dict[str, Dict[str, Any]],
    base_dir: Optional[str],
    investigator_cycle: str,
    investigator_name: str,
    overrides: Dict[str, Any],
) -> List[RelatedCard]:
    related: List[RelatedCard] = []
    for code in _deck_requirement_card_codes(investigator_card):
        card = all_cards_by_code.get(code)
        if not card:
            continue
        related.append(_card_to_related_card(
            card,
            base_dir,
            investigator_cycle,
            investigator_name,
            overrides,
        ))
    return related


def _cache_card_images(
    base_dir: str,
    investigator_cards: List[Dict[str, Any]],
    all_cards: Optional[List[Dict[str, Any]]] = None,
    max_workers: int = 8,
) -> Tuple[int, int, int]:
    overrides = _load_simplified_overrides(base_dir)
    all_cards = all_cards or investigator_cards
    all_cards_by_code = _card_lookup(all_cards)
    display_name_counts = _display_name_counts(investigator_cards, overrides)
    jobs: List[Tuple[str, str]] = []
    seen_targets: Set[str] = set()

    for card in investigator_cards:
        inv = _card_to_investigator(
            card,
            base_dir,
            overrides,
            display_name_counts,
            all_cards_by_code,
        )
        for key, target in (("imagesrc", inv.img1), ("backimagesrc", inv.img2)):
            url = _arkhamdb_url(str(card.get(key) or ""))
            if url and target and target not in seen_targets:
                jobs.append((url, target))
                seen_targets.add(target)
        for related in inv.related_cards:
            related_source = all_cards_by_code.get(related.code, {})
            for key, target in (("imagesrc", related.img1), ("backimagesrc", related.img2)):
                url = _arkhamdb_url(str(related_source.get(key) or ""))
                if url and target and target not in seen_targets:
                    jobs.append((url, target))
                    seen_targets.add(target)

    if not jobs:
        return 0, 0, 0

    def cache_one(job: Tuple[str, str]) -> bool:
        url, target = job
        return bool(_cache_remote_image(base_dir, url, target))

    ok = 0
    with ThreadPoolExecutor(max_workers=max_workers) as executor:
        for success in executor.map(cache_one, jobs):
            if success:
                ok += 1

    total = len(jobs)
    return ok, total, total - ok


def find_latest_xlsx(directory: str) -> Optional[str]:
    """
    在指定目录中查找最新修改时间的 .xlsx 文件。
    """
    files = glob.glob(os.path.join(directory, "*.xlsx"))
    if not files:
        return None
    files.sort(key=lambda p: os.path.getmtime(p), reverse=True)
    return files[0]


def _build_image_paths(base_dir: str, name: str) -> Tuple[str, str]:
    """
    根据调查员名字构造图片路径:
      images/<name>（正面）.png / images/<name>（背面）.png
    若全角括号版本不存在，则尝试半角括号版本。
    """
    name = str(name).strip()
    images_dir = os.path.join(base_dir, "images")

    def try_paths(filename_patterns: List[str]) -> str:
        for pat in filename_patterns:
            p = os.path.abspath(os.path.join(images_dir, pat))
            if os.path.exists(p):
                return p
        # 都不存在，则返回第一个作为“预期路径”（UI 会显示“无图片”）
        return os.path.abspath(os.path.join(images_dir, filename_patterns[0]))

    # 正面
    front_patterns = [
        f"{name}（正面）.png",
        f"{name}(正面).png",
    ]
    # 背面
    back_patterns = [
        f"{name}（背面）.png",
        f"{name}(背面).png",
    ]

    img1 = try_paths(front_patterns)
    img2 = try_paths(back_patterns)
    return img1, img2


def _xlsx_col_to_index(col: str) -> int:
    n = 0
    for ch in col:
        n = n * 26 + (ord(ch.upper()) - ord("A") + 1)
    return n


def _read_xlsx_rows(path: str) -> List[List[Any]]:
    """
    用标准库读取简单 xlsx 表格，避免只为迁移旧数据而依赖 openpyxl。
    """
    ns = {"a": "http://schemas.openxmlformats.org/spreadsheetml/2006/main"}
    with zipfile.ZipFile(path) as z:
        shared: List[str] = []
        if "xl/sharedStrings.xml" in z.namelist():
            root = ET.fromstring(z.read("xl/sharedStrings.xml"))
            for si in root.findall("a:si", ns):
                shared.append("".join(t.text or "" for t in si.findall(".//a:t", ns)))

        sheet_name = "xl/worksheets/sheet1.xml"
        if sheet_name not in z.namelist():
            sheets = [name for name in z.namelist() if name.startswith("xl/worksheets/sheet")]
            if not sheets:
                return []
            sheet_name = sorted(sheets)[0]

        sheet = ET.fromstring(z.read(sheet_name))
        rows: List[List[Any]] = []
        for row in sheet.findall(".//a:sheetData/a:row", ns):
            values: Dict[int, Any] = {}
            for cell in row.findall("a:c", ns):
                ref = cell.attrib.get("r", "")
                match = re.match(r"([A-Z]+)", ref)
                if not match:
                    continue
                col_index = _xlsx_col_to_index(match.group(1))
                value_node = cell.find("a:v", ns)
                inline_node = cell.find("a:is", ns)

                value: Any = ""
                if cell.attrib.get("t") == "s" and value_node is not None:
                    idx = int(value_node.text or "0")
                    value = shared[idx] if idx < len(shared) else ""
                elif cell.attrib.get("t") == "inlineStr" and inline_node is not None:
                    value = "".join(t.text or "" for t in inline_node.findall(".//a:t", ns))
                elif value_node is not None:
                    value = value_node.text or ""

                values[col_index] = value

            if values:
                max_col = max(values)
                rows.append([values.get(i, "") for i in range(1, max_col + 1)])
        return rows


def _to_int(value: Any) -> int:
    try:
        return int(value)
    except Exception:
        return 0


def _unique_values(values: List[str]) -> List[str]:
    seen: Set[str] = set()
    result: List[str] = []
    for value in values:
        value = str(value or "").strip()
        if value and value not in seen:
            seen.add(value)
            result.append(value)
    return result


def _to_simplified(text: Any) -> str:
    value = str(text or "")
    if not value:
        return ""
    if _OPENCC is not None:
        try:
            return _OPENCC.convert(value)
        except Exception:
            pass
    return value.translate(T2S_FALLBACK_TABLE)


def _normalize_name(value: str) -> str:
    text = _to_simplified(value)
    text = text.replace("（", "(").replace("）", ")")
    text = text.replace("‧", "·")
    text = text.replace("“", "\"").replace("”", "\"")
    return re.sub(r"\s+", "", text).lower()


def _excel_overrides(base_dir: str) -> Dict[str, Dict[str, str]]:
    latest_xlsx = find_latest_xlsx(base_dir)
    if not latest_xlsx:
        return {}

    overrides: Dict[str, Dict[str, str]] = {}
    try:
        for inv in load_investigators_from_xlsx(latest_xlsx):
            key = _normalize_name(inv.name)
            if not key:
                continue
            overrides[key] = {
                "name": inv.name,
                "alias": inv.alias,
                "career": inv.career,
                "sub_career": inv.sub_career,
            }
    except Exception:
        return {}
    return overrides


def _load_simplified_overrides(base_dir: str) -> Dict[str, Any]:
    """
    手工维护的官方简中覆盖优先，旧 Excel 简中译名次之，繁转简兜底。
    """
    manual = _read_json(_cache_path(base_dir, SIMPLIFIED_OVERRIDES_FILE), {})
    if not isinstance(manual, dict):
        manual = {}

    by_code = manual.get("by_code", {})
    if not isinstance(by_code, dict):
        by_code = {}

    by_name = manual.get("by_name", {})
    if not isinstance(by_name, dict):
        by_name = {}

    normalized_by_name: Dict[str, Dict[str, str]] = {}
    normalized_by_name.update(_excel_overrides(base_dir))
    for name, item in by_name.items():
        if isinstance(item, dict):
            normalized_by_name[_normalize_name(str(name))] = {
                str(k): str(v) for k, v in item.items()
            }

    return {
        "by_code": {
            str(code): {str(k): str(v) for k, v in item.items()}
            for code, item in by_code.items()
            if isinstance(item, dict)
        },
        "by_name": normalized_by_name,
    }


def _get_simplified_override(overrides: Dict[str, Any], card: Dict[str, Any], simplified_name: str) -> Dict[str, str]:
    code = str(card.get("code") or "")
    by_code = overrides.get("by_code", {})
    if code and code in by_code:
        return dict(by_code[code])

    by_name = overrides.get("by_name", {})
    key_candidates = [
        _normalize_name(simplified_name),
        _normalize_name(str(card.get("name") or "")),
        _normalize_name(str(card.get("real_name") or "")),
    ]
    for key in key_candidates:
        if key in by_name:
            return dict(by_name[key])
    return {}


def _display_name_counts(cards: List[Dict[str, Any]], overrides: Dict[str, Any]) -> Dict[str, int]:
    counts: Dict[str, int] = {}
    for card in cards:
        simplified_name = _to_simplified(card.get("name") or card.get("real_name") or "")
        override = _get_simplified_override(overrides, card, simplified_name)
        name = override.get("name") or simplified_name
        key = _normalize_name(name)
        counts[key] = counts.get(key, 0) + 1
    return counts


def _is_starting_investigator_card(card: Dict[str, Any]) -> bool:
    if card.get("type_code") != "investigator":
        return False
    if card.get("duplicate_of_code") and str(card.get("code") or "") not in SPECIAL_DUPLICATE_INVESTIGATOR_CODES:
        return False

    text = " ".join([
        _to_simplified(card.get("text") or ""),
        str(card.get("text") or ""),
        str(card.get("real_text") or ""),
    ]).lower()
    return not any(pattern.lower() in text for pattern in NON_STARTING_INVESTIGATOR_PATTERNS)


def _all_investigator_cards(cards: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    return [
        card for card in cards
        if card.get("type_code") == "investigator"
        and (
            not card.get("duplicate_of_code")
            or str(card.get("code") or "") in SPECIAL_DUPLICATE_INVESTIGATOR_CODES
        )
    ]


def _starting_investigator_cards(cards: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    return [card for card in _all_investigator_cards(cards) if _is_starting_investigator_card(card)]


def load_investigators_from_xlsx(path: str) -> List[Investigator]:
    """
    读取 Excel：
    1: 循环
    2: 调查员
    3: 别称
    4: 职介
    5: 副职介
    6: 小张玩过几次
    7: 小胡玩过几次

    图片路径不再从表中读取，而是根据 name 自动拼:
      images/<name>（正面）.png / images/<name>（背面）.png
    """
    base_dir = os.path.dirname(os.path.abspath(path))
    investigators: List[Investigator] = []
    rows = _read_xlsx_rows(path)

    # 第一行是表头
    for row in rows[1:]:
        values = list(row) + [""] * 7
        cycle = values[0] or ""
        name = values[1] or ""
        alias = values[2] or ""
        career = values[3] or ""
        sub_career = values[4] or ""
        play_zhang = _to_int(values[5])
        play_hu = _to_int(values[6])

        img1, img2 = _build_image_paths(base_dir, name)

        inv = Investigator(
            cycle=str(cycle),
            name=str(name),
            alias=str(alias),
            career=str(career),
            sub_career=str(sub_career),
            play_zhang=play_zhang,
            play_hu=play_hu,
            img1=img1,
            img2=img2,
            source="Excel",
        )
        investigators.append(inv)

    return investigators


def _faction_to_cn(code: str, name: str = "") -> str:
    if code in FACTION_CN:
        return FACTION_CN[code]
    return str(name or "").strip() or "未知"


def _deck_options_to_subcareer(card: Dict[str, Any], main_career: str) -> str:
    options = card.get("deck_options") or []
    subcareers: Set[str] = set()

    for option in options:
        factions = option.get("faction") or []
        for faction in factions:
            cn = _faction_to_cn(str(faction))
            if cn not in {main_career, "中立", "所有"}:
                subcareers.add(cn)

        # Dunwich 式“任意 0 级非本职牌”在 ArkhamDB 通常没有 faction 列表。
        level = option.get("level") or {}
        if (
            option.get("limit")
            and not factions
            and level.get("min") == 0
            and level.get("max") == 0
        ):
            subcareers.add("所有")

    if main_career == "所有":
        return "所有"
    if "所有" in subcareers:
        return "所有"
    return "、".join(sorted(subcareers)) if subcareers else "无"


def _card_to_investigator(
    card: Dict[str, Any],
    base_dir: Optional[str] = None,
    overrides: Optional[Dict[str, Any]] = None,
    display_name_counts: Optional[Dict[str, int]] = None,
    all_cards_by_code: Optional[Dict[str, Dict[str, Any]]] = None,
) -> Investigator:
    code = str(card.get("code") or "")
    career = _faction_to_cn(str(card.get("faction_code") or ""), str(card.get("faction_name") or ""))
    simplified_name = _to_simplified(card.get("name") or card.get("real_name") or "")
    simplified_alias = _to_simplified(card.get("subname") or "")
    simplified_cycle = _to_simplified(card.get("pack_name") or card.get("pack_code") or "")
    override = _get_simplified_override(overrides or {}, card, simplified_name)
    name = override.get("name") or simplified_name
    cycle = override.get("cycle") or simplified_cycle
    front_url = _arkhamdb_url(str(card.get("imagesrc") or ""))
    back_url = _arkhamdb_url(str(card.get("backimagesrc") or ""))
    name_key = _normalize_name(name)
    name_is_duplicate = bool(display_name_counts and display_name_counts.get(name_key, 0) > 1)

    if base_dir:
        img1 = _named_image_cache_path(base_dir, cycle, name, "正面", front_url, code, name_is_duplicate) if front_url else ""
        img2 = _named_image_cache_path(base_dir, cycle, name, "背面", back_url, code, name_is_duplicate) if back_url else ""
    else:
        img1 = front_url
        img2 = back_url

    related_cards = _related_cards_for_investigator(
        card,
        all_cards_by_code or {},
        base_dir,
        cycle,
        name,
        overrides or {},
    )

    return Investigator(
        cycle=cycle,
        name=name,
        alias=override.get("alias") or simplified_alias,
        career=override.get("career") or career,
        sub_career=override.get("sub_career") or _deck_options_to_subcareer(card, career),
        play_zhang=0,
        play_hu=0,
        img1=img1,
        img2=img2,
        code=code,
        source="ArkhamDB",
        card_url=f"{ARKHAMDB_BASE_URL}/card/{code}" if code else "",
        related_cards=related_cards,
    )


def _investigator_key(inv: Investigator) -> str:
    return inv.code or inv.name


def _load_player_counts(base_dir: str) -> Dict[str, Dict[str, int]]:
    data = _read_json(_cache_path(base_dir, PLAYER_COUNTS_FILE), {})
    if not isinstance(data, dict):
        return {}
    result: Dict[str, Dict[str, int]] = {}
    for player, counts in data.items():
        if isinstance(counts, dict):
            result[str(player)] = {str(k): _to_int(v) for k, v in counts.items()}
    return result


def _save_player_counts(base_dir: str, counts: Dict[str, Dict[str, int]]):
    path = _cache_path(base_dir, PLAYER_COUNTS_FILE)
    existing = _read_json(path, {})
    preserved = {
        str(k): v for k, v in existing.items()
        if isinstance(k, str) and k.startswith("_")
    } if isinstance(existing, dict) else {}
    preserved.update(counts)
    _write_json(path, preserved)


def _load_play_records(base_dir: str) -> List[Dict[str, Any]]:
    data = _read_json(_cache_path(base_dir, PLAY_RECORDS_FILE), [])
    if not isinstance(data, list):
        return []
    return [item for item in data if isinstance(item, dict)]


def _save_play_records(base_dir: str, records: List[Dict[str, Any]]):
    _write_json(_cache_path(base_dir, PLAY_RECORDS_FILE), records)


def _new_play_record_id(records: List[Dict[str, Any]]) -> str:
    existing = {str(item.get("id", "")) for item in records if isinstance(item, dict)}
    while True:
        record_id = f"{int(time.time() * 1000)}-{random.randint(1000, 9999)}"
        if record_id not in existing:
            return record_id


def _make_play_record(inv: Investigator, player: str, record_id: str) -> Dict[str, Any]:
    return {
        "id": record_id,
        "recorded_at": time.strftime("%Y-%m-%d %H:%M:%S"),
        "player": player,
        "investigator_key": _investigator_key(inv),
        "code": inv.code,
        "name": inv.name,
        "alias": inv.alias,
        "career": inv.career,
        "sub_career": inv.sub_career,
        "cycle_group": _cycle_display_group(inv.cycle),
        "source_cycle": inv.cycle,
    }


def _append_play_record(base_dir: str, inv: Investigator, player: str) -> str:
    records = _load_play_records(base_dir)
    record_id = _new_play_record_id(records)
    records.append(_make_play_record(inv, player, record_id))
    _save_play_records(base_dir, records)
    return record_id


def _remove_play_record(base_dir: str, record_id: str) -> bool:
    if not record_id:
        return False
    records = _load_play_records(base_dir)
    kept = [item for item in records if str(item.get("id", "")) != record_id]
    if len(kept) == len(records):
        return False
    _save_play_records(base_dir, kept)
    return True


def _update_play_record_player(base_dir: str, record_id: str, player: str) -> bool:
    if not record_id:
        return False
    records = _load_play_records(base_dir)
    changed = False
    for item in records:
        if str(item.get("id", "")) == record_id:
            item["player"] = player
            item["updated_at"] = time.strftime("%Y-%m-%d %H:%M:%S")
            changed = True
            break
    if changed:
        _save_play_records(base_dir, records)
    return changed


def _apply_player_counts(base_dir: str, investigators: List[Investigator]):
    counts = _load_player_counts(base_dir)
    for inv in investigators:
        key = _investigator_key(inv)
        if "小张" in counts and key in counts["小张"]:
            inv.play_zhang = counts["小张"][key]
        if "小胡" in counts and key in counts["小胡"]:
            inv.play_hu = counts["小胡"][key]


def migrate_player_counts_from_xlsx_if_needed(base_dir: str, investigators: List[Investigator]) -> bool:
    """
    首次启用程序内统计时，把旧 Excel 的游玩次数迁移到 player_counts.json。
    不覆盖已有 player_counts.json，避免破坏之后由程序确认写入的记录。
    """
    target = _cache_path(base_dir, PLAYER_COUNTS_FILE)
    if os.path.exists(target):
        return False

    latest_xlsx = find_latest_xlsx(base_dir)
    if not latest_xlsx:
        return False

    old_investigators = load_investigators_from_xlsx(latest_xlsx)
    by_code = {inv.code: inv for inv in investigators if inv.code}
    by_name = {_normalize_name(inv.name): inv for inv in investigators}
    legacy_code_overrides = {
        _normalize_name(name): code
        for name, code in LEGACY_NAME_CODE_OVERRIDES.items()
    }

    counts: Dict[str, Dict[str, int]] = {"小张": {}, "小胡": {}}
    unmatched: List[Dict[str, Any]] = []
    matched = 0

    for old in old_investigators:
        play_zhang = int(old.play_zhang)
        play_hu = int(old.play_hu)
        if not play_zhang and not play_hu:
            continue

        key = _normalize_name(old.name)
        code = legacy_code_overrides.get(key)
        inv = by_code.get(code) if code else by_name.get(key)

        if inv is None:
            unmatched.append({
                "name": old.name,
                "cycle": old.cycle,
                "alias": old.alias,
                "career": old.career,
                "sub_career": old.sub_career,
                "小张": play_zhang,
                "小胡": play_hu,
            })
            continue

        matched += 1
        count_key = _investigator_key(inv)
        if play_zhang:
            counts["小张"][count_key] = play_zhang
        if play_hu:
            counts["小胡"][count_key] = play_hu

    payload: Dict[str, Any] = {
        "_migrated_from": os.path.basename(latest_xlsx),
        "_migrated_at": time.strftime("%Y-%m-%d %H:%M:%S"),
        "_matched_nonzero_rows": matched,
        "_legacy_unmatched": unmatched,
        "小张": counts["小张"],
        "小胡": counts["小胡"],
    }
    _write_json(target, payload)
    return True


def reconcile_legacy_unmatched_counts(base_dir: str, investigators: List[Investigator]) -> int:
    path = _cache_path(base_dir, PLAYER_COUNTS_FILE)
    raw_counts = _read_json(path, {})
    if not isinstance(raw_counts, dict):
        return 0

    legacy = raw_counts.get("_legacy_unmatched", [])
    if not isinstance(legacy, list) or not legacy:
        return 0

    by_code = {inv.code: inv for inv in investigators if inv.code}
    by_name = {_normalize_name(inv.name): inv for inv in investigators}
    legacy_code_overrides = {
        _normalize_name(name): code
        for name, code in LEGACY_NAME_CODE_OVERRIDES.items()
    }

    matched = 0
    remaining: List[Any] = []
    counts = _load_player_counts(base_dir)
    counts.setdefault("小张", {})
    counts.setdefault("小胡", {})

    for item in legacy:
        if not isinstance(item, dict):
            remaining.append(item)
            continue

        key = _normalize_name(str(item.get("name", "")))
        code = legacy_code_overrides.get(key)
        inv = by_code.get(code) if code else by_name.get(key)
        if inv is None:
            remaining.append(item)
            continue

        count_key = _investigator_key(inv)
        zhang = _to_int(item.get("小张"))
        hu = _to_int(item.get("小胡"))
        if zhang:
            counts["小张"][count_key] = _to_int(counts["小张"].get(count_key)) + zhang
        if hu:
            counts["小胡"][count_key] = _to_int(counts["小胡"].get(count_key)) + hu
        matched += 1

    if not matched:
        return 0

    raw_counts["小张"] = counts["小张"]
    raw_counts["小胡"] = counts["小胡"]
    raw_counts["_legacy_unmatched"] = remaining
    raw_counts["_legacy_reconciled_at"] = time.strftime("%Y-%m-%d %H:%M:%S")
    raw_counts["_legacy_reconciled_rows"] = _to_int(raw_counts.get("_legacy_reconciled_rows")) + matched
    _write_json(path, raw_counts)
    return matched


def load_investigators_from_cache(base_dir: str) -> Tuple[List[Investigator], str]:
    cache = _read_json(_cache_path(base_dir, ARKHAMDB_CACHE_FILE), {})
    cards = cache.get("cards") if isinstance(cache, dict) else None
    all_cards = cache.get("all_cards") if isinstance(cache, dict) else None
    if not isinstance(cards, list) or not cards:
        return [], ""
    if not isinstance(all_cards, list) or not all_cards:
        all_cards = cards

    all_investigator_cards = _all_investigator_cards(all_cards)
    starting_cards = _starting_investigator_cards(all_cards)
    if not starting_cards:
        return [], ""

    overrides = _load_simplified_overrides(base_dir)
    all_cards_by_code = _card_lookup(all_cards)
    display_name_counts = _display_name_counts(all_investigator_cards, overrides)
    investigators = [
        _card_to_investigator(card, base_dir, overrides, display_name_counts, all_cards_by_code)
        for card in starting_cards
    ]
    investigators.sort(key=_investigator_sort_key)
    migrate_player_counts_from_xlsx_if_needed(base_dir, investigators)
    reconcile_legacy_unmatched_counts(base_dir, investigators)
    _apply_player_counts(base_dir, investigators)

    synced_at = cache.get("synced_at", "") if isinstance(cache, dict) else ""
    source = f"ArkhamDB 缓存（{synced_at}）" if synced_at else "ArkhamDB 缓存"
    return investigators, source


def sync_investigators_from_arkhamdb(base_dir: str, cache_images: bool = True) -> Tuple[List[Investigator], str]:
    cards = _request_json(ARKHAMDB_CARDS_URL)
    if not isinstance(cards, list):
        raise RuntimeError("ArkhamDB 返回的数据格式不是列表。")

    all_investigator_cards = _all_investigator_cards(cards)
    investigator_cards = _starting_investigator_cards(cards)
    if not investigator_cards:
        raise RuntimeError("没有从 ArkhamDB 读取到调查员。")

    synced_at = time.strftime("%Y-%m-%d %H:%M:%S")
    cache = {
        "synced_at": synced_at,
        "source_url": ARKHAMDB_CARDS_URL,
        "all_cards": cards,
        "cards": all_investigator_cards,
    }
    _write_json(_cache_path(base_dir, ARKHAMDB_CACHE_FILE), cache)

    image_msg = ""
    if cache_images:
        ok, total, failed = _cache_card_images(base_dir, all_investigator_cards, cards)
        image_msg = f"，卡图缓存 {ok}/{total}"
        if failed:
            image_msg += f"（失败 {failed}）"

    overrides = _load_simplified_overrides(base_dir)
    all_cards_by_code = _card_lookup(cards)
    display_name_counts = _display_name_counts(all_investigator_cards, overrides)
    investigators = [
        _card_to_investigator(card, base_dir, overrides, display_name_counts, all_cards_by_code)
        for card in investigator_cards
    ]
    investigators.sort(key=_investigator_sort_key)
    migrate_player_counts_from_xlsx_if_needed(base_dir, investigators)
    reconcile_legacy_unmatched_counts(base_dir, investigators)
    _apply_player_counts(base_dir, investigators)
    return investigators, f"ArkhamDB 在线同步（{synced_at}{image_msg}）"


def load_initial_investigators(base_dir: str) -> Tuple[List[Investigator], str]:
    cached, source = load_investigators_from_cache(base_dir)
    if cached:
        return cached, source

    latest_xlsx = find_latest_xlsx(base_dir)
    if latest_xlsx:
        investigators = load_investigators_from_xlsx(latest_xlsx)
        _apply_player_counts(base_dir, investigators)
        return investigators, f"Excel：{os.path.basename(latest_xlsx)}"

    try:
        return sync_investigators_from_arkhamdb(base_dir, cache_images=True)
    except Exception:
        raise


# =============== 自定义多选下拉框 ===============

class CheckableComboBox(QComboBox):
    """
    支持多选的下拉框，每个选项带勾选框。
    """
    checked_items_changed = pyqtSignal()

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setModel(QStandardItemModel(self))
        self.view().pressed.connect(self.handle_item_pressed)
        self.setEditable(True)
        self.lineEdit().setReadOnly(True)
        self._update_text()

    def add_checkable_items(self, items: List[str]):
        model: QStandardItemModel = self.model()  # type: ignore
        model.clear()
        for text in items:
            item = QStandardItem(text)
            item.setFlags(Qt.ItemFlag.ItemIsEnabled | Qt.ItemFlag.ItemIsUserCheckable)
            item.setData(Qt.CheckState.Unchecked, Qt.ItemDataRole.CheckStateRole)
            model.appendRow(item)
        self._update_text()

    def handle_item_pressed(self, index: QModelIndex):
        item = self.model().itemFromIndex(index)
        if item is None:
            return
        state = item.checkState()
        if state == Qt.CheckState.Checked:
            item.setCheckState(Qt.CheckState.Unchecked)
        else:
            item.setCheckState(Qt.CheckState.Checked)
        self._update_text()
        self.checked_items_changed.emit()

    def checked_items(self) -> List[str]:
        result = []
        for i in range(self.model().rowCount()):
            item = self.model().item(i)
            if item.checkState() == Qt.CheckState.Checked:
                result.append(item.text())
        return result

    def set_checked_items(self, items: Set[str]):
        wanted = set(items)
        for i in range(self.model().rowCount()):
            item = self.model().item(i)
            state = Qt.CheckState.Checked if item.text() in wanted else Qt.CheckState.Unchecked
            item.setCheckState(state)
        self._update_text()
        self.checked_items_changed.emit()

    def _update_text(self):
        texts = self.checked_items()
        if texts:
            display = "，".join(texts)
        else:
            display = "未选择"
        self.lineEdit().setText(display)


# =============== 逻辑层：职介 / 副职介 + 玩家加权随机 ===============

class RandomPicker:
    def __init__(self, investigators: List[Investigator]):
        self.remaining: List[Investigator] = list(investigators)
        self.selected: List[Investigator] = []        # 当前队伍
        self.history: List[PickRecord] = []           # 选人顺序（含为谁选）

    # -------- 职介相关 --------

    def get_locked_careers(self) -> List[str]:
        """
        当前已锁定的职介（不含“所有”），用于“职介不重复”约束展示。
        """
        careers = set()
        for inv in self.selected:
            if not inv.career:
                continue
            if inv.career == "所有":
                continue
            careers.add(inv.career)
        return sorted(careers)

    # -------- 副职介相关 --------

    def _parse_sub_careers(self, sub_career: str) -> Set[str]:
        """
        把副职介字符串拆成若干 tag：
        - 使用 “、”，“，”, “,”, “/” 分隔
        - 忽略空串
        - 忽略 “所有” 和 “无”
        """
        if not sub_career:
            return set()
        s = str(sub_career).strip()
        if not s:
            return set()

        # 统一分隔符
        for ch in [",", "，", "/"]:
            s = s.replace(ch, "、")
        parts = [p.strip() for p in s.split("、")]

        ignore = {"所有", "无"}
        result = {p for p in parts if p and p not in ignore}
        return result

    def _get_locked_subcareers(self) -> Set[str]:
        """
        当前已选队伍中，所有“有效副职介”的集合（忽略“所有”“无”）。
        """
        locked: Set[str] = set()
        for inv in self.selected:
            locked |= self._parse_sub_careers(inv.sub_career)
        return locked

    # -------- 玩家次数相关 --------

    def _get_play_count_for_player(self, inv: Investigator, player: Optional[str]) -> int:
        if player == "小张":
            return inv.play_zhang
        if player == "小胡":
            return inv.play_hu
        return 0

    # -------- 综合加权选择 --------

    def _weighted_choice(
        self,
        candidates: List[Investigator],
        player: Optional[str],
        locked_subs: Set[str],
        soft_avoid_subcareer: bool,
    ) -> Investigator:
        """
        基于两层权重：
        - 玩家玩过次数：次数越多权重越低 (1 / (count + 1))
        - 副职介冲突：若 soft_avoid_subcareer=True 且有冲突，则再乘一个惩罚系数
        """
        weights: List[float] = []

        for inv in candidates:
            # 1) 基于玩过次数
            base = 1.0
            if player:
                count = self._get_play_count_for_player(inv, player)
                base = 1.0 / float(count + 1)

            # 2) 副职介软避免：有冲突则降低概率
            if soft_avoid_subcareer:
                cand_subs = self._parse_sub_careers(inv.sub_career)
                if cand_subs and (cand_subs & locked_subs):
                    # 有交集 -> 惩罚一下，不完全禁止
                    base *= 0.25

            weights.append(base)

        total = sum(weights)
        if total <= 0:
            return random.choice(candidates)

        r = random.random() * total
        acc = 0.0
        for inv, w in zip(candidates, weights):
            acc += w
            if r <= acc:
                return inv

        return candidates[-1]

    # -------- 对外主接口 --------

    def pick_one(
        self,
        max_players: int = 4,
        unique_career: bool = True,
        assign_player: Optional[str] = None,
        lock_career: Optional[str] = None,
        excluded_careers: Optional[Set[str]] = None,
        allowed_cycles: Optional[Set[str]] = None,
        allow_all_for_lock: bool = False,
        force_subcareer_unique: bool = False,
    ) -> Tuple[Optional[Investigator], str]:
        """
        allow_all_for_lock:
          True 时, 锁定职介时, 职介为 "所有" 的调查员也可以参与候选。
        force_subcareer_unique:
          True 时, 有效副职介与已选队伍有交集的调查员会被直接过滤掉。
          False 时, 仍可被选中，但权重较低（软避免）。
        """
        if len(self.selected) >= max_players:
            return None, f"已经达到人数上限 {max_players} 人。"

        candidates = self.candidate_pool(
            unique_career=unique_career,
            lock_career=lock_career,
            excluded_careers=excluded_careers,
            allowed_cycles=allowed_cycles,
            allow_all_for_lock=allow_all_for_lock,
            force_subcareer_unique=force_subcareer_unique,
        )

        if not candidates:
            locked = set(self.get_locked_careers())
            if lock_career and unique_career and lock_career in locked:
                return None, f"已选队伍中包含职介“{lock_career}”，且启用了职介不重复，无法再锁定该职介。"
            if excluded_careers or lock_career or force_subcareer_unique or allowed_cycles is not None:
                return None, "当前循环池/排除/锁定/副职介不重复/职介不重复等设置导致没有可选调查员，请调整后重试。"
            return None, "没有可选的调查员（剩余列表为空）。"

        inv = self._weighted_choice(
            candidates=candidates,
            player=assign_player,
            locked_subs=self._get_locked_subcareers(),
            soft_avoid_subcareer=not force_subcareer_unique,
        )

        self.remaining.remove(inv)
        self.selected.append(inv)
        self.history.append(PickRecord(inv=inv, player=assign_player))
        return inv, ""

    def candidate_pool(
        self,
        unique_career: bool = True,
        lock_career: Optional[str] = None,
        excluded_careers: Optional[Set[str]] = None,
        allowed_cycles: Optional[Set[str]] = None,
        allow_all_for_lock: bool = False,
        force_subcareer_unique: bool = False,
    ) -> List[Investigator]:
        locked = set(self.get_locked_careers())
        locked_subs = self._get_locked_subcareers()
        candidates: List[Investigator] = []

        for inv in self.remaining:
            career = inv.career or ""
            cand_subs = self._parse_sub_careers(inv.sub_career)
            conflict_sub = bool(cand_subs and (cand_subs & locked_subs))

            # 限定循环池
            if allowed_cycles is not None and inv.cycle not in allowed_cycles:
                continue

            # 排除职介
            if excluded_careers and career in excluded_careers:
                continue

            # 职介不重复约束
            if unique_career:
                if career != "所有" and career in locked:
                    continue

            # 副职介强制不重复
            if force_subcareer_unique and conflict_sub:
                # 有交集 -> 直接跳过
                continue

            # 锁定职介约束
            if lock_career:
                # allow_all_for_lock=True 时, career == "所有" 也可以通过
                if career == "所有" and allow_all_for_lock:
                    pass
                elif career != lock_career:
                    continue

            candidates.append(inv)

        return sorted(candidates, key=_investigator_sort_key)

    def undo_last(self) -> Optional[PickRecord]:
        if not self.history:
            return None

        record = self.history.pop()
        inv = record.inv

        if inv in self.selected:
            self.selected.remove(inv)
        if inv not in self.remaining:
            self.remaining.append(inv)

        return record


# =============== 界面层 ===============

class MainWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("诡镇奇谈调查员控制台")
        self.resize(1100, 750)

        self.base_dir = os.path.dirname(os.path.abspath(__file__))
        self.executor = ThreadPoolExecutor(max_workers=1)
        self.signals = WorkerSignals()
        self.signals.log_ready.connect(self._append_log)
        self.signals.sync_ready.connect(self._on_sync_finished)

        # 1. 优先读取 ArkhamDB 缓存；没有缓存时回退旧 Excel；最后才在线兜底。
        try:
            investigators, source = load_initial_investigators(self.base_dir)
        except Exception as exc:
            QMessageBox.critical(
                self,
                "错误",
                f"没有可用的调查员数据。\n\n在线同步失败，且当前目录下没有可回退的 .xlsx 文件。\n\n{exc}"
            )
            raise SystemExit(1)

        if not investigators:
            QMessageBox.critical(
                self,
                "错误",
                "没有读取到有效的调查员数据。"
            )
            raise SystemExit(1)

        self.data_source = source
        self.picker = RandomPicker(investigators)

        # 抽出所有普通职介（过滤掉“所有”和空）
        self.all_careers: List[str] = sorted({
            inv.career for inv in investigators
            if inv.career and inv.career != "所有"
        })
        self.cycle_group_map: Dict[str, Set[str]] = _cycle_group_map(investigators)
        self.all_cycles: List[str] = list(self.cycle_group_map.keys())

        # 3. 搭建 UI
        self._init_ui()
        self._refresh_dynamic_panels()
        self._rebuild_history_list()
        self._append_log(f"已加载：{self.data_source}，共 {len(investigators)} 名调查员。")

    # ---------- UI 构建 ----------

    def _init_ui(self):
        self.resize(1280, 860)
        self._apply_theme()

        central = QWidget()
        central.setObjectName("appRoot")
        self.setCentralWidget(central)

        main_layout = QVBoxLayout(central)
        main_layout.setContentsMargins(18, 16, 18, 16)
        main_layout.setSpacing(12)

        header = QFrame()
        header.setObjectName("appHeader")
        header_layout = QHBoxLayout(header)
        header_layout.setContentsMargins(20, 16, 20, 16)
        header_layout.setSpacing(18)

        title_layout = QVBoxLayout()
        title_layout.setSpacing(4)
        label_title = QLabel("诡镇奇谈调查员控制台")
        label_title.setObjectName("pageTitle")
        label_subtitle = QLabel("调查员池、循环筛选、游玩计数与本地卡图缓存")
        label_subtitle.setObjectName("mutedText")
        title_layout.addWidget(label_title)
        title_layout.addWidget(label_subtitle)
        header_layout.addLayout(title_layout, stretch=1)

        stat_layout = QHBoxLayout()
        stat_layout.setSpacing(8)
        self.label_file = QLabel(f"数据源：{self.data_source}")
        self.label_file.setObjectName("statPill")
        self.label_remaining = QLabel("")
        self.label_remaining.setObjectName("statPillStrong")
        self.label_history_state = QLabel("")
        self.label_history_state.setObjectName("statPill")
        stat_layout.addWidget(self.label_file)
        stat_layout.addWidget(self.label_remaining)
        stat_layout.addWidget(self.label_history_state)
        header_layout.addLayout(stat_layout)
        main_layout.addWidget(header)

        self.label_locked_careers = QLabel("已锁定职介：无")
        self.label_locked_careers.setObjectName("statusBar")
        self.label_locked_careers.setWordWrap(True)
        main_layout.addWidget(self.label_locked_careers)

        # 操作区
        controls_layout = QHBoxLayout()
        controls_layout.setSpacing(12)

        flow_box = QGroupBox("抽选流程")
        flow_layout = QGridLayout(flow_box)
        flow_layout.setContentsMargins(12, 16, 12, 12)
        flow_layout.setHorizontalSpacing(8)
        flow_layout.setVerticalSpacing(8)

        self.btn_pick = QPushButton("随机选调查员")
        self.btn_pick.setObjectName("primaryButton")
        self.btn_pick.setMinimumHeight(40)
        self.btn_pick.clicked.connect(self.on_pick_clicked)
        flow_layout.addWidget(self.btn_pick, 0, 0, 1, 2)

        self.btn_undo = QPushButton("撤销上一次")
        self.btn_undo.setObjectName("dangerButton")
        self.btn_undo.setMinimumHeight(40)
        self.btn_undo.clicked.connect(self.on_undo_clicked)
        flow_layout.addWidget(self.btn_undo, 1, 0)

        self.btn_confirm = QPushButton("确认并记录")
        self.btn_confirm.setObjectName("accentButton")
        self.btn_confirm.setMinimumHeight(40)
        self.btn_confirm.clicked.connect(self.on_confirm_clicked)
        flow_layout.addWidget(self.btn_confirm, 1, 1)

        self.btn_stats = QPushButton("查看统计")
        self.btn_stats.setObjectName("secondaryButton")
        self.btn_stats.setMinimumHeight(40)
        self.btn_stats.clicked.connect(self.on_stats_clicked)
        flow_layout.addWidget(self.btn_stats, 2, 0)

        self.btn_sync = QPushButton("同步 ArkhamDB")
        self.btn_sync.setObjectName("secondaryButton")
        self.btn_sync.setMinimumHeight(40)
        self.btn_sync.clicked.connect(self.on_sync_clicked)
        flow_layout.addWidget(self.btn_sync, 2, 1)
        controls_layout.addWidget(flow_box, stretch=1)

        rule_box = QGroupBox("规则与玩家")
        rule_layout = QGridLayout(rule_box)
        rule_layout.setContentsMargins(12, 16, 12, 12)
        rule_layout.setHorizontalSpacing(10)
        rule_layout.setVerticalSpacing(9)

        # 职介不重复
        self.chk_unique_career = QCheckBox("职介不重复")
        self.chk_unique_career.setChecked(True)
        self.chk_unique_career.stateChanged.connect(self.on_unique_career_changed)
        rule_layout.addWidget(self.chk_unique_career, 0, 0)

        # 副职介强制不重复
        self.chk_force_sub_unique = QCheckBox("副职介强制不重复")
        self.chk_force_sub_unique.setChecked(False)
        self.chk_force_sub_unique.stateChanged.connect(lambda *_: self._refresh_dynamic_panels())
        rule_layout.addWidget(self.chk_force_sub_unique, 0, 1)

        # 为指定玩家选
        self.chk_assign_player = QCheckBox("为指定玩家选")
        self.chk_assign_player.setChecked(False)
        self.chk_assign_player.stateChanged.connect(self.on_assign_player_changed)
        rule_layout.addWidget(self.chk_assign_player, 1, 0)

        self.combo_player = QComboBox()
        self.combo_player.addItems(["小张", "小胡"])
        self.combo_player.setEnabled(False)
        self.combo_player.setMinimumWidth(150)
        self.combo_player.currentTextChanged.connect(lambda *_: self._refresh_dynamic_panels())
        rule_layout.addWidget(self.combo_player, 1, 1)
        controls_layout.addWidget(rule_box, stretch=1)

        pool_box = QGroupBox("候选池")
        pool_layout = QGridLayout(pool_box)
        pool_layout.setContentsMargins(12, 16, 12, 12)
        pool_layout.setHorizontalSpacing(10)
        pool_layout.setVerticalSpacing(9)

        # 锁定职介
        self.chk_lock_career = QCheckBox("锁定职介")
        self.chk_lock_career.setChecked(False)
        self.chk_lock_career.stateChanged.connect(self.on_lock_career_changed)
        pool_layout.addWidget(self.chk_lock_career, 0, 0)

        self.combo_lock_career = QComboBox()
        self.combo_lock_career.addItems(self.all_careers)
        self.combo_lock_career.setEnabled(False)
        self.combo_lock_career.setMinimumWidth(190)
        self.combo_lock_career.currentTextChanged.connect(lambda *_: self._refresh_dynamic_panels())
        pool_layout.addWidget(self.combo_lock_career, 0, 1)

        # 是否允许 “所有” 参与锁定职介
        self.chk_allow_all_for_lock = QCheckBox("包含“所有”")
        self.chk_allow_all_for_lock.setChecked(False)
        self.chk_allow_all_for_lock.setEnabled(False)
        self.chk_allow_all_for_lock.setVisible(False)  # 只在锁定职介开启时显示
        self.chk_allow_all_for_lock.stateChanged.connect(lambda *_: self._refresh_dynamic_panels())
        pool_layout.addWidget(self.chk_allow_all_for_lock, 0, 2)

        # 排除职介
        self.chk_exclude_career = QCheckBox("排除职介")
        self.chk_exclude_career.setChecked(False)
        self.chk_exclude_career.stateChanged.connect(self.on_exclude_career_changed)
        pool_layout.addWidget(self.chk_exclude_career, 1, 0)

        self.combo_exclude_career = CheckableComboBox()
        self.combo_exclude_career.add_checkable_items(self.all_careers)
        self.combo_exclude_career.setEnabled(False)
        self.combo_exclude_career.setMinimumWidth(190)
        self.combo_exclude_career.checked_items_changed.connect(lambda *_: self._refresh_dynamic_panels())
        pool_layout.addWidget(self.combo_exclude_career, 1, 1, 1, 2)

        # 限定循环池
        self.chk_limit_cycles = QCheckBox("限定循环池")
        self.chk_limit_cycles.setChecked(False)
        self.chk_limit_cycles.stateChanged.connect(self.on_limit_cycles_changed)
        pool_layout.addWidget(self.chk_limit_cycles, 2, 0)

        self.combo_cycles = CheckableComboBox()
        self.combo_cycles.add_checkable_items(self.all_cycles)
        self.combo_cycles.setEnabled(False)
        self.combo_cycles.setMinimumWidth(190)
        self.combo_cycles.checked_items_changed.connect(lambda *_: self._refresh_dynamic_panels())
        pool_layout.addWidget(self.combo_cycles, 2, 1, 1, 2)
        controls_layout.addWidget(pool_box, stretch=2)

        main_layout.addLayout(controls_layout)

        # 中间：本次结果 + 图片
        result_splitter = QSplitter(Qt.Orientation.Horizontal)
        result_splitter.setChildrenCollapsible(False)
        result_splitter.setObjectName("contentSplitter")

        current_box = QGroupBox("本次抽到")
        current_layout = QVBoxLayout(current_box)
        current_layout.setContentsMargins(14, 18, 14, 14)
        current_layout.setSpacing(10)

        self.label_current_name = QLabel("（尚未抽取）")
        self.label_current_name.setObjectName("currentName")
        current_layout.addWidget(self.label_current_name)

        self.text_current_detail = QTextEdit()
        self.text_current_detail.setReadOnly(True)
        self.text_current_detail.setMinimumHeight(170)
        current_layout.addWidget(self.text_current_detail)
        self._clear_current_investigator()
        result_splitter.addWidget(current_box)

        # 图片区域（横向大图）
        image_box = QGroupBox("本地卡图")
        image_box_layout = QVBoxLayout(image_box)
        image_box_layout.setContentsMargins(14, 18, 14, 14)
        img_layout = QHBoxLayout()
        img_layout.setSpacing(10)
        self.label_img1 = QLabel()
        self.label_img2 = QLabel()

        for label in (self.label_img1, self.label_img2):
            label.setObjectName("cardImage")
            label.setMinimumSize(340, 220)
            label.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Expanding)

        self.label_img1.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.label_img2.setAlignment(Qt.AlignmentFlag.AlignCenter)

        img_layout.addWidget(self.label_img1)
        img_layout.addWidget(self.label_img2)
        image_box_layout.addLayout(img_layout)

        self.tree_related_cards = QTreeWidget()
        self.tree_related_cards.setColumnCount(4)
        self.tree_related_cards.setHeaderLabels(["专属卡 / 弱点", "类型", "来源", "编号"])
        self.tree_related_cards.setRootIsDecorated(False)
        self.tree_related_cards.setMinimumHeight(125)
        self.tree_related_cards.header().setSectionResizeMode(0, QHeaderView.ResizeMode.Stretch)
        for col in range(1, 4):
            self.tree_related_cards.header().setSectionResizeMode(col, QHeaderView.ResizeMode.ResizeToContents)
        image_box_layout.addWidget(self.tree_related_cards)
        self._clear_related_cards()
        result_splitter.addWidget(image_box)
        result_splitter.setStretchFactor(0, 1)
        result_splitter.setStretchFactor(1, 2)
        result_splitter.setSizes([440, 780])

        main_layout.addWidget(result_splitter, stretch=3)

        # 下方：历史记录 + 日志
        bottom_splitter = QSplitter(Qt.Orientation.Horizontal)
        bottom_splitter.setChildrenCollapsible(False)

        history_box = QGroupBox("队伍与候选池")
        history_layout = QVBoxLayout(history_box)
        history_layout.setContentsMargins(12, 18, 12, 12)

        self.bottom_tabs = QTabWidget()
        self.list_history = QListWidget()
        self.bottom_tabs.addTab(self.list_history, "当前队伍")

        self.tree_candidates = QTreeWidget()
        self.tree_candidates.setColumnCount(5)
        self.tree_candidates.setHeaderLabels(["候选 / 分组", "职介", "副职介", "小张", "小胡"])
        self.tree_candidates.setRootIsDecorated(True)
        self.tree_candidates.header().setSectionResizeMode(0, QHeaderView.ResizeMode.Stretch)
        for col in range(1, 5):
            self.tree_candidates.header().setSectionResizeMode(col, QHeaderView.ResizeMode.ResizeToContents)
        self.bottom_tabs.addTab(self.tree_candidates, "候选池预览")

        history_layout.addWidget(self.bottom_tabs)
        bottom_splitter.addWidget(history_box)

        log_box = QGroupBox("操作日志")
        log_layout = QVBoxLayout(log_box)
        log_layout.setContentsMargins(12, 18, 12, 12)
        self.text_log = QTextEdit()
        self.text_log.setReadOnly(True)
        log_layout.addWidget(self.text_log)
        bottom_splitter.addWidget(log_box)
        bottom_splitter.setStretchFactor(0, 2)
        bottom_splitter.setStretchFactor(1, 1)
        bottom_splitter.setSizes([820, 400])

        main_layout.addWidget(bottom_splitter, stretch=2)

    def _apply_theme(self):
        self.setStyleSheet("""
            QMainWindow, QDialog, QWidget#appRoot {
                background: #f3f5f2;
                color: #202522;
                font-family: "Microsoft YaHei UI", "Microsoft YaHei", "Segoe UI";
                font-size: 13px;
            }
            QFrame#appHeader {
                background: #ffffff;
                border: 1px solid #d9ded8;
                border-radius: 8px;
            }
            QFrame#statsSummary {
                background: #ffffff;
                border: 1px solid #d9ded8;
                border-radius: 8px;
            }
            QLabel#pageTitle {
                color: #202522;
                font-size: 24px;
                font-weight: 700;
            }
            QLabel#mutedText {
                color: #68706b;
                font-size: 12px;
            }
            QLabel#statPill, QLabel#statPillStrong {
                border: 1px solid #d9ded8;
                border-radius: 12px;
                padding: 6px 10px;
                background: #fbfdfd;
                color: #68706b;
                font-size: 12px;
            }
            QLabel#statPillStrong {
                color: #9b2632;
                font-weight: 700;
                border-color: #e4c3c7;
                background: #fff7f7;
            }
            QLabel#statusBar {
                border: 1px solid #d9ded8;
                border-radius: 8px;
                padding: 8px 12px;
                background: #eef0ec;
                color: #4f5852;
                font-size: 12px;
            }
            QGroupBox {
                background: #ffffff;
                border: 1px solid #d9ded8;
                border-radius: 8px;
                margin-top: 12px;
                padding-top: 10px;
                font-weight: 700;
                color: #202522;
            }
            QGroupBox::title {
                subcontrol-origin: margin;
                subcontrol-position: top left;
                left: 10px;
                padding: 0 6px;
                color: #68706b;
                background: #ffffff;
            }
            QPushButton {
                min-height: 36px;
                border: 1px solid #d9ded8;
                border-radius: 8px;
                padding: 8px 12px;
                color: #202522;
                background: #fbfdfd;
                font-weight: 600;
            }
            QPushButton:hover {
                border-color: #1f7471;
                color: #1f7471;
                background: #ffffff;
            }
            QPushButton:pressed {
                background: #eef0ec;
            }
            QPushButton:disabled {
                color: #9aa39d;
                background: #edf0ed;
                border-color: #e1e5e0;
            }
            QPushButton#primaryButton {
                color: #ffffff;
                background: #9b2632;
                border-color: #9b2632;
            }
            QPushButton#primaryButton:hover {
                background: #751a25;
                border-color: #751a25;
                color: #ffffff;
            }
            QPushButton#accentButton {
                color: #ffffff;
                background: #1f7471;
                border-color: #1f7471;
            }
            QPushButton#accentButton:hover {
                background: #155e5b;
                border-color: #155e5b;
                color: #ffffff;
            }
            QPushButton#dangerButton {
                color: #b13b3b;
                background: #fff7f7;
                border-color: #e2b8b8;
            }
            QCheckBox {
                spacing: 7px;
                color: #202522;
                font-weight: 500;
            }
            QComboBox {
                min-height: 34px;
                border: 1px solid #d9ded8;
                border-radius: 8px;
                padding: 5px 10px;
                background: #fbfdfd;
                color: #202522;
            }
            QComboBox:disabled {
                color: #8a938d;
                background: #edf0ed;
            }
            QTextEdit, QListWidget, QTreeWidget {
                border: 1px solid #d9ded8;
                border-radius: 8px;
                background: #fbfdfd;
                color: #202522;
                padding: 8px;
                selection-background-color: #dcebe9;
                selection-color: #202522;
            }
            QListWidget::item {
                padding: 7px 6px;
                border-radius: 6px;
            }
            QListWidget::item:hover, QTreeWidget::item:hover {
                background: #eef0ec;
            }
            QTreeWidget::item {
                padding: 5px 4px;
            }
            QHeaderView::section {
                border: 0;
                border-bottom: 1px solid #d9ded8;
                padding: 7px 8px;
                background: #eef0ec;
                color: #4f5852;
                font-weight: 700;
            }
            QTabWidget::pane {
                border: 0;
                padding-top: 6px;
            }
            QTabBar::tab {
                min-height: 28px;
                border: 1px solid #d9ded8;
                border-radius: 7px;
                padding: 5px 12px;
                margin-right: 6px;
                background: #fbfdfd;
                color: #68706b;
                font-weight: 600;
            }
            QTabBar::tab:selected {
                border-color: #1f7471;
                background: #eef7f5;
                color: #1f7471;
            }
            QLabel#currentName {
                color: #202522;
                font-size: 20px;
                font-weight: 700;
            }
            QLabel#cardImage {
                border: 1px solid #1f2427;
                border-radius: 8px;
                background: #111517;
                color: #cbd4d0;
                font-weight: 600;
            }
            QSplitter::handle {
                background: #d9ded8;
                margin: 4px;
            }
        """)

    # ---------- 事件 ----------

    def _refresh_career_controls(self):
        if not hasattr(self, "combo_lock_career"):
            return

        current_lock = self.combo_lock_career.currentText().strip()
        current_cycles = set(self.combo_cycles.checked_items()) if hasattr(self, "combo_cycles") else set()

        self.combo_lock_career.clear()
        self.combo_lock_career.addItems(self.all_careers)
        if current_lock in self.all_careers:
            self.combo_lock_career.setCurrentText(current_lock)

        self.combo_exclude_career.add_checkable_items(self.all_careers)
        self.combo_cycles.add_checkable_items(self.all_cycles)
        self.combo_cycles.set_checked_items(current_cycles & set(self.all_cycles))

    def _replace_investigators(self, investigators: List[Investigator], source: str):
        self.data_source = source
        self.picker = RandomPicker(investigators)
        self.all_careers = sorted({
            inv.career for inv in investigators
            if inv.career and inv.career != "所有"
        })
        self.cycle_group_map = _cycle_group_map(investigators)
        self.all_cycles = list(self.cycle_group_map.keys())
        self._refresh_career_controls()
        self.label_file.setText(f"数据源：{self.data_source}")
        self._clear_current_investigator()
        self._clear_current_images()
        self._rebuild_history_list()
        self._refresh_dynamic_panels()

    def _adjust_player_count(self, inv: Investigator, player: Optional[str], delta: int):
        if not player or player not in PLAYER_COUNT_FIELD:
            return

        field = PLAYER_COUNT_FIELD[player]
        new_value = max(0, int(getattr(inv, field)) + delta)
        setattr(inv, field, new_value)

        counts = _load_player_counts(self.base_dir)
        key = _investigator_key(inv)
        counts.setdefault(player, {})[key] = new_value
        _save_player_counts(self.base_dir, counts)

    def _set_player_counts_for_investigator(self, inv: Investigator, zhang: int, hu: int):
        zhang = max(0, int(zhang))
        hu = max(0, int(hu))
        inv.play_zhang = zhang
        inv.play_hu = hu

        counts = _load_player_counts(self.base_dir)
        key = _investigator_key(inv)
        counts.setdefault("小张", {})[key] = zhang
        counts.setdefault("小胡", {})[key] = hu
        _save_player_counts(self.base_dir, counts)

    def on_sync_clicked(self):
        self.btn_sync.setEnabled(False)
        QApplication.setOverrideCursor(Qt.CursorShape.WaitCursor)
        self._append_log("开始后台同步 ArkhamDB 调查员数据，并缓存调查员卡图、专属卡与弱点……")
        self.executor.submit(self._sync_worker)

    def _sync_worker(self):
        try:
            investigators, source = sync_investigators_from_arkhamdb(self.base_dir, cache_images=True)
            self.signals.sync_ready.emit(investigators, source, "")
        except Exception as exc:
            self.signals.sync_ready.emit([], "", str(exc))

    def _on_sync_finished(self, investigators: List[Investigator], source: str, error: str):
        QApplication.restoreOverrideCursor()
        self.btn_sync.setEnabled(True)

        if error:
            QMessageBox.warning(self, "同步失败", f"无法同步 ArkhamDB 数据：\n{error}")
            self._append_log(f"同步失败：{error}")
            return

        self._replace_investigators(investigators, source)
        self._append_log(f"同步完成：{source}，共 {len(investigators)} 名调查员。")

    def _expanded_allowed_cycles_from_ui(self) -> Optional[Set[str]]:
        if not self.chk_limit_cycles.isChecked():
            return None
        selected_cycle_groups = set(self.combo_cycles.checked_items())
        allowed_cycles: Set[str] = set()
        for group in selected_cycle_groups:
            allowed_cycles.update(self.cycle_group_map.get(group, {group}))
        return allowed_cycles

    def _current_filter_options(self) -> Dict[str, Any]:
        unique = self.chk_unique_career.isChecked()

        lock_career: Optional[str] = None
        if self.chk_lock_career.isChecked():
            text = self.combo_lock_career.currentText().strip()
            lock_career = text or None

        allow_all_for_lock = False
        if lock_career is not None and self.chk_allow_all_for_lock.isChecked():
            allow_all_for_lock = True

        force_sub_unique = self.chk_force_sub_unique.isChecked()

        excluded_careers: Set[str] = set()
        if self.chk_exclude_career.isChecked():
            excluded_careers = set(self.combo_exclude_career.checked_items())

        return {
            "unique_career": unique,
            "lock_career": lock_career,
            "excluded_careers": excluded_careers if excluded_careers else None,
            "allowed_cycles": self._expanded_allowed_cycles_from_ui(),
            "allow_all_for_lock": allow_all_for_lock,
            "force_subcareer_unique": force_sub_unique,
        }

    def _current_pick_options(self) -> Dict[str, Any]:
        options = self._current_filter_options()
        options["assign_player"] = self.combo_player.currentText() if self.chk_assign_player.isChecked() else None
        return options

    def on_pick_clicked(self):
        if self.chk_limit_cycles.isChecked():
            selected_cycle_groups = set(self.combo_cycles.checked_items())
            if not selected_cycle_groups:
                QMessageBox.information(self, "提示", "已开启限定循环池，请至少选择一个循环。")
                self._append_log("尝试选人失败：限定循环池已开启，但没有选择任何循环。")
                return

        pick_options = self._current_pick_options()
        assign_player = pick_options.get("assign_player")
        inv, msg = self.picker.pick_one(
            max_players=4,
            **pick_options,
        )

        if inv is None:
            QMessageBox.information(self, "提示", msg)
            self._append_log(f"尝试选人失败：{msg}")
            return

        # 更新当前结果 + 图片
        self._show_current_investigator(inv, assign_player, committed=False)
        self._update_current_images(inv)

        # 重建历史显示
        self._rebuild_history_list()

        if assign_player:
            self._append_log(f"抽到：{inv.name}（{inv.career}），为 {assign_player} 选，尚未记入统计。")
        else:
            self._append_log(f"抽到：{inv.name}（{inv.career}），尚未记入统计。")

        self._refresh_dynamic_panels()

    def on_undo_clicked(self):
        record = self.picker.undo_last()
        if record is None:
            QMessageBox.information(self, "提示", "没有可撤销的记录。")
            self._append_log("尝试撤销，但历史为空。")
            return

        inv = record.inv
        player = record.player
        if record.committed:
            self._adjust_player_count(inv, player, -1)
            if record.log_id:
                _remove_play_record(self.base_dir, record.log_id)

        if player:
            self._append_log(f"撤销：{inv.name}（{inv.career}），原本为 {player} 选。")
        else:
            self._append_log(f"撤销：{inv.name}（{inv.career}）。")

        # 撤销后更新当前结果 + 图片
        if self.picker.history:
            last_record = self.picker.history[-1]
            last_inv = last_record.inv
            last_player = last_record.player
            self._show_current_investigator(last_inv, last_player, last_record.committed)
            self._update_current_images(last_inv)
        else:
            self._clear_current_investigator()
            self._clear_current_images()

        self._rebuild_history_list()
        self._refresh_dynamic_panels()

    def on_confirm_clicked(self):
        if not self.picker.history:
            QMessageBox.information(self, "提示", "当前还没有可确认的抽选记录。")
            self._append_log("尝试确认记录，但历史为空。")
            return

        pending = [record for record in self.picker.history if not record.committed]
        if not pending:
            QMessageBox.information(self, "提示", "当前队伍已经全部记录过了。")
            self._append_log("尝试确认记录，但没有未记录项目。")
            return

        unassigned = [record for record in pending if not record.player]
        if unassigned:
            names = "、".join(record.inv.name for record in unassigned[:4])
            if len(unassigned) > 4:
                names += f" 等 {len(unassigned)} 人"
            QMessageBox.information(
                self,
                "需要分配玩家",
                f"还有未分配玩家的调查员：{names}\n\n请先在“当前队伍”里为每位调查员选择小张或小胡，再确认记录。"
            )
            self._append_log(f"确认记录被拦截：{len(unassigned)} 名调查员还没有分配玩家。")
            if hasattr(self, "bottom_tabs"):
                self.bottom_tabs.setCurrentWidget(self.list_history)
            return

        recorded = 0
        for record in pending:
            if record.player:
                record.log_id = _append_play_record(self.base_dir, record.inv, record.player)
            self._adjust_player_count(record.inv, record.player, 1)
            recorded += 1
            record.committed = True

        self._rebuild_history_list()
        if self.picker.history:
            last = self.picker.history[-1]
            self._show_current_investigator(last.inv, last.player, last.committed)

        msg = f"已确认 {len(pending)} 条抽选记录"
        if recorded:
            msg += f"，写入 {recorded} 条玩家游玩次数与游玩记录"
        self._append_log(msg + "。")
        QMessageBox.information(self, "已确认", msg + "。")
        self._refresh_dynamic_panels()

    def on_stats_clicked(self):
        all_investigators = self.picker.selected + self.picker.remaining
        active_total_zhang = sum(inv.play_zhang for inv in all_investigators)
        active_total_hu = sum(inv.play_hu for inv in all_investigators)

        raw_counts = _read_json(_cache_path(self.base_dir, PLAYER_COUNTS_FILE), {})
        legacy = raw_counts.get("_legacy_unmatched", []) if isinstance(raw_counts, dict) else []
        if not isinstance(legacy, list):
            legacy = []

        legacy_total_zhang = sum(_to_int(item.get("小张")) for item in legacy if isinstance(item, dict))
        legacy_total_hu = sum(_to_int(item.get("小胡")) for item in legacy if isinstance(item, dict))

        total_zhang = active_total_zhang + legacy_total_zhang
        total_hu = active_total_hu + legacy_total_hu

        summary = (
            f"当前池统计：小张 {active_total_zhang}，小胡 {active_total_hu}\n"
            f"历史未匹配：小张 {legacy_total_zhang}，小胡 {legacy_total_hu}\n"
            f"合计基线：小张 {total_zhang}，小胡 {total_hu}"
        )

        self._append_log("—— 当前游玩统计 ——")
        self._append_log(summary)
        for inv in sorted(all_investigators, key=_investigator_sort_key):
            if inv.play_zhang or inv.play_hu:
                self._append_log(f"{inv.name}：小张 {inv.play_zhang}，小胡 {inv.play_hu}")
        for item in legacy:
            if isinstance(item, dict):
                self._append_log(
                    f"[历史未匹配] {item.get('name', '')}：小张 {_to_int(item.get('小张'))}，小胡 {_to_int(item.get('小胡'))}"
                )

        self._show_stats_dialog(
            all_investigators=all_investigators,
            legacy=legacy,
            active_total_zhang=active_total_zhang,
            active_total_hu=active_total_hu,
            legacy_total_zhang=legacy_total_zhang,
            legacy_total_hu=legacy_total_hu,
            total_zhang=total_zhang,
            total_hu=total_hu,
        )

    def _show_stats_dialog(
        self,
        all_investigators: List[Investigator],
        legacy: List[Any],
        active_total_zhang: int,
        active_total_hu: int,
        legacy_total_zhang: int,
        legacy_total_hu: int,
        total_zhang: int,
        total_hu: int,
    ):
        dialog = QDialog(self)
        dialog.setWindowTitle("当前游玩统计")
        dialog.resize(980, 680)
        dialog.setStyleSheet(self.styleSheet())

        layout = QVBoxLayout(dialog)
        layout.setContentsMargins(18, 16, 18, 16)
        layout.setSpacing(12)

        title = QLabel("当前游玩统计")
        title.setObjectName("pageTitle")
        subtitle = QLabel("按循环顺序分组；旧表格未匹配项单独归档，确认后的玩家归属会写入最近记录。")
        subtitle.setObjectName("mutedText")
        layout.addWidget(title)
        layout.addWidget(subtitle)

        summary_frame = QFrame()
        summary_frame.setObjectName("statsSummary")
        summary_layout = QHBoxLayout(summary_frame)
        summary_layout.setContentsMargins(10, 10, 10, 10)
        summary_layout.setSpacing(8)
        summary_labels: Dict[str, QLabel] = {}
        for key, text, strong in [
            ("active", f"当前池：小张 {active_total_zhang} / 小胡 {active_total_hu}", False),
            ("legacy", f"历史未匹配：小张 {legacy_total_zhang} / 小胡 {legacy_total_hu}", False),
            ("total", f"合计基线：小张 {total_zhang} / 小胡 {total_hu}", True),
        ]:
            label = QLabel(text)
            label.setObjectName("statPillStrong" if strong else "statPill")
            summary_labels[key] = label
            summary_layout.addWidget(label)
        summary_layout.addStretch()
        layout.addWidget(summary_frame)

        tree = QTreeWidget()
        tree.setColumnCount(7)
        tree.setHeaderLabels(["循环 / 调查员", "职介", "副职介", "别称", "小张", "小胡", "编号"])
        tree.setAlternatingRowColors(True)
        tree.setRootIsDecorated(True)
        tree.header().setSectionResizeMode(0, QHeaderView.ResizeMode.Stretch)
        for col in range(1, 7):
            tree.header().setSectionResizeMode(col, QHeaderView.ResizeMode.ResizeToContents)

        role_kind = Qt.ItemDataRole.UserRole
        role_key = Qt.ItemDataRole.UserRole + 1
        role_legacy_index = Qt.ItemDataRole.UserRole + 2
        investigator_by_key = {_investigator_key(inv): inv for inv in all_investigators}

        grouped: Dict[str, List[Investigator]] = {}
        for inv in sorted(all_investigators, key=_investigator_sort_key):
            grouped.setdefault(_cycle_display_group(inv.cycle) or "未归类", []).append(inv)

        for cycle in _sort_cycles(list(grouped.keys())):
            investigators = grouped[cycle]
            cycle_zhang = sum(inv.play_zhang for inv in investigators)
            cycle_hu = sum(inv.play_hu for inv in investigators)
            cycle_item = QTreeWidgetItem([
                f"{cycle}（{len(investigators)}）",
                "",
                "",
                "",
                str(cycle_zhang),
                str(cycle_hu),
                "",
            ])
            cycle_item.setData(0, role_kind, "group")
            cycle_item.setExpanded(True)
            group_font = cycle_item.font(0)
            group_font.setBold(True)
            for col in range(tree.columnCount()):
                cycle_item.setFont(col, group_font)
                cycle_item.setBackground(col, QBrush(QColor("#eef0ec")))
            tree.addTopLevelItem(cycle_item)

            for inv in investigators:
                child = QTreeWidgetItem([
                    inv.name,
                    inv.career,
                    inv.sub_career or "无",
                    inv.alias or "",
                    str(inv.play_zhang),
                    str(inv.play_hu),
                    inv.code or "",
                ])
                child.setData(0, role_kind, "investigator")
                child.setData(0, role_key, _investigator_key(inv))
                if inv.play_zhang or inv.play_hu:
                    child.setForeground(0, QBrush(QColor("#202522")))
                else:
                    for col in range(tree.columnCount()):
                        child.setForeground(col, QBrush(QColor("#68706b")))
                cycle_item.addChild(child)

        if legacy:
            legacy_item = QTreeWidgetItem([
                f"历史未匹配（{len(legacy)}）",
                "",
                "",
                "",
                str(legacy_total_zhang),
                str(legacy_total_hu),
                "",
            ])
            legacy_item.setData(0, role_kind, "legacy_group")
            legacy_item.setExpanded(True)
            legacy_font = legacy_item.font(0)
            legacy_font.setBold(True)
            for col in range(tree.columnCount()):
                legacy_item.setFont(col, legacy_font)
                legacy_item.setBackground(col, QBrush(QColor("#fff7f7")))
            tree.addTopLevelItem(legacy_item)
            for legacy_index, item in enumerate(legacy):
                if not isinstance(item, dict):
                    continue
                child = QTreeWidgetItem([
                    str(item.get("name", "")),
                    "旧表格",
                    "",
                    "",
                    str(_to_int(item.get("小张"))),
                    str(_to_int(item.get("小胡"))),
                    "",
                ])
                child.setData(0, role_kind, "legacy")
                child.setData(0, role_legacy_index, legacy_index)
                legacy_item.addChild(child)

        def _apply_count_style(item: QTreeWidgetItem):
            played = bool(_to_int(item.text(4)) or _to_int(item.text(5)))
            color = QColor("#202522") if played else QColor("#68706b")
            for col in range(tree.columnCount()):
                item.setForeground(col, QBrush(color))

        def _refresh_stats_totals():
            refreshed_active_zhang = sum(inv.play_zhang for inv in all_investigators)
            refreshed_active_hu = sum(inv.play_hu for inv in all_investigators)
            refreshed_legacy_zhang = sum(_to_int(item.get("小张")) for item in legacy if isinstance(item, dict))
            refreshed_legacy_hu = sum(_to_int(item.get("小胡")) for item in legacy if isinstance(item, dict))

            summary_labels["active"].setText(f"当前池：小张 {refreshed_active_zhang} / 小胡 {refreshed_active_hu}")
            summary_labels["legacy"].setText(f"历史未匹配：小张 {refreshed_legacy_zhang} / 小胡 {refreshed_legacy_hu}")
            summary_labels["total"].setText(
                f"合计基线：小张 {refreshed_active_zhang + refreshed_legacy_zhang} / "
                f"小胡 {refreshed_active_hu + refreshed_legacy_hu}"
            )

            for top_index in range(tree.topLevelItemCount()):
                top_item = tree.topLevelItem(top_index)
                if top_item.data(0, role_kind) not in {"group", "legacy_group"}:
                    continue
                group_zhang = 0
                group_hu = 0
                for child_index in range(top_item.childCount()):
                    child = top_item.child(child_index)
                    group_zhang += _to_int(child.text(4))
                    group_hu += _to_int(child.text(5))
                top_item.setText(4, str(group_zhang))
                top_item.setText(5, str(group_hu))

        def _save_legacy_counts():
            raw_counts = _read_json(_cache_path(self.base_dir, PLAYER_COUNTS_FILE), {})
            if not isinstance(raw_counts, dict):
                raw_counts = {}
            raw_counts["_legacy_unmatched"] = legacy
            _write_json(_cache_path(self.base_dir, PLAYER_COUNTS_FILE), raw_counts)

        def _edit_selected_counts():
            item = tree.currentItem()
            kind = item.data(0, role_kind) if item else None
            if kind not in {"investigator", "legacy"}:
                QMessageBox.information(dialog, "提示", "请先在“累计统计”里选中一名调查员或历史未匹配项。")
                return

            name = item.text(0)
            old_zhang = _to_int(item.text(4))
            old_hu = _to_int(item.text(5))

            edit_dialog = QDialog(dialog)
            edit_dialog.setWindowTitle("修改游玩次数")
            edit_dialog.setStyleSheet(self.styleSheet())
            edit_layout = QVBoxLayout(edit_dialog)
            edit_layout.setContentsMargins(16, 14, 16, 14)
            edit_layout.setSpacing(10)

            name_label = QLabel(name)
            name_label.setObjectName("pageTitle")
            edit_layout.addWidget(name_label)

            form = QFormLayout()
            spin_zhang = QSpinBox()
            spin_zhang.setRange(0, 999)
            spin_zhang.setValue(old_zhang)
            spin_hu = QSpinBox()
            spin_hu.setRange(0, 999)
            spin_hu.setValue(old_hu)
            form.addRow("小张", spin_zhang)
            form.addRow("小胡", spin_hu)
            edit_layout.addLayout(form)

            buttons = QDialogButtonBox(
                QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel
            )
            buttons.accepted.connect(edit_dialog.accept)
            buttons.rejected.connect(edit_dialog.reject)
            edit_layout.addWidget(buttons)

            if edit_dialog.exec() != QDialog.DialogCode.Accepted.value:
                return

            new_zhang = spin_zhang.value()
            new_hu = spin_hu.value()
            if new_zhang == old_zhang and new_hu == old_hu:
                return

            if kind == "investigator":
                inv = investigator_by_key.get(str(item.data(0, role_key)))
                if inv is None:
                    QMessageBox.warning(dialog, "无法修改", "没有找到这名调查员的数据。")
                    return
                self._set_player_counts_for_investigator(inv, new_zhang, new_hu)
            else:
                legacy_index = item.data(0, role_legacy_index)
                if not isinstance(legacy_index, int) or legacy_index < 0 or legacy_index >= len(legacy):
                    QMessageBox.warning(dialog, "无法修改", "没有找到这条历史未匹配记录。")
                    return
                if not isinstance(legacy[legacy_index], dict):
                    QMessageBox.warning(dialog, "无法修改", "这条历史未匹配记录格式异常。")
                    return
                legacy[legacy_index]["小张"] = new_zhang
                legacy[legacy_index]["小胡"] = new_hu
                _save_legacy_counts()

            item.setText(4, str(new_zhang))
            item.setText(5, str(new_hu))
            _apply_count_style(item)
            _refresh_stats_totals()
            self._refresh_dynamic_panels()
            self._append_log(f"已手动修改游玩次数：{name}，小张 {old_zhang}->{new_zhang}，小胡 {old_hu}->{new_hu}。")

        play_records = _load_play_records(self.base_dir)
        recent_tree = QTreeWidget()
        recent_tree.setColumnCount(6)
        recent_tree.setHeaderLabels(["时间", "玩家", "调查员", "循环", "职介", "编号"])
        recent_tree.setAlternatingRowColors(True)
        recent_tree.setRootIsDecorated(False)
        recent_tree.header().setSectionResizeMode(2, QHeaderView.ResizeMode.Stretch)
        for col in [0, 1, 3, 4, 5]:
            recent_tree.header().setSectionResizeMode(col, QHeaderView.ResizeMode.ResizeToContents)

        recent_items = list(reversed(play_records[-80:]))
        if recent_items:
            for item in recent_items:
                if not isinstance(item, dict):
                    continue
                recent_tree.addTopLevelItem(QTreeWidgetItem([
                    str(item.get("recorded_at", "")),
                    str(item.get("player", "")),
                    str(item.get("name", "")),
                    str(item.get("cycle_group") or item.get("source_cycle") or ""),
                    str(item.get("career", "")),
                    str(item.get("code", "")),
                ]))
        else:
            recent_tree.addTopLevelItem(QTreeWidgetItem([
                "暂无确认记录",
                "",
                "",
                "",
                "",
                "",
            ]))

        tabs = QTabWidget()
        tabs.addTab(tree, "累计统计")
        tabs.addTab(recent_tree, f"最近记录（{len(play_records)}）")
        layout.addWidget(tabs, stretch=1)

        edit_button = QPushButton("修改选中次数")
        edit_button.setObjectName("accentButton")
        edit_button.clicked.connect(_edit_selected_counts)

        close_button = QPushButton("关闭")
        close_button.setObjectName("secondaryButton")
        close_button.clicked.connect(dialog.accept)
        button_layout = QHBoxLayout()
        button_layout.addWidget(edit_button)
        button_layout.addStretch()
        button_layout.addWidget(close_button)
        layout.addLayout(button_layout)

        dialog.exec()

    def on_unique_career_changed(self, state: int):
        self._refresh_dynamic_panels()
        if self.chk_unique_career.isChecked():
            self._append_log("已开启：职介不重复约束（“所有”视作百搭，不锁定具体职介）。")
        else:
            self._append_log("已关闭：职介不重复约束。")

    def on_assign_player_changed(self, state: int):
        enabled = self.chk_assign_player.isChecked()
        self.combo_player.setEnabled(enabled)
        self._refresh_dynamic_panels()
        if enabled:
            self._append_log("已开启：为指定玩家选调查员（会按该玩家的玩过次数做加权随机）。")
        else:
            self._append_log("已关闭：为指定玩家选调查员。")

    def on_lock_career_changed(self, state: int):
        enabled = self.chk_lock_career.isChecked()
        self.combo_lock_career.setEnabled(enabled)

        # “包含所有” 只在锁定职介开启时可见可用
        self.chk_allow_all_for_lock.setEnabled(enabled)
        self.chk_allow_all_for_lock.setVisible(enabled)
        if not enabled:
            self.chk_allow_all_for_lock.setChecked(False)
        self._refresh_dynamic_panels()

        if enabled:
            self._append_log("已开启：锁定职介（可通过“包含‘所有’”控制是否纳入“所有”职介）。")
        else:
            self._append_log("已关闭：锁定职介。")

    def on_exclude_career_changed(self, state: int):
        enabled = self.chk_exclude_career.isChecked()
        self.combo_exclude_career.setEnabled(enabled)
        self._refresh_dynamic_panels()
        if enabled:
            self._append_log("已开启：排除职介（从候选中剔除选中的职介）。")
        else:
            self._append_log("已关闭：排除职介。")

    def on_limit_cycles_changed(self, state: int):
        enabled = self.chk_limit_cycles.isChecked()
        self.combo_cycles.setEnabled(enabled)
        self._refresh_dynamic_panels()
        if enabled:
            self._append_log("已开启：限定循环池（只从勾选循环中抽取调查员）。")
        else:
            self._append_log("已关闭：限定循环池。")

    # ---------- 辅助 ----------

    def _show_current_investigator(
        self,
        inv: Investigator,
        player: Optional[str],
        committed: Optional[bool] = None,
    ):
        self.label_current_name.setText(inv.name)
        self.text_current_detail.setHtml(
            self._format_investigator_detail_html(inv, player, committed)
        )

    def _clear_current_investigator(self):
        self.label_current_name.setText("（尚未抽取）")
        self.text_current_detail.setHtml("""
            <div style="color:#68706b; font-size:13px; padding:8px;">
              当前还没有调查员。设置候选池和规则后，点击“随机选调查员”。
            </div>
        """)

    def _format_investigator_detail_html(
        self,
        inv: Investigator,
        player: Optional[str],
        committed: Optional[bool] = None,
    ) -> str:
        def esc(value: Any, fallback: str = "无") -> str:
            text = fallback if value in (None, "") else str(value)
            return html.escape(text)

        status = "已记录" if committed else "未记录"
        status_color = "#256a45" if committed else "#9b2632"
        status_bg = "#f2f8f5" if committed else "#fff7f7"
        player_text = player or "未指定"
        code_text = inv.code or "无"
        url_text = inv.card_url or "无"
        cycle_group = _cycle_display_group(inv.cycle)
        source_cycle_row = ""
        if cycle_group != inv.cycle:
            source_cycle_row = (
                f'<tr><td style="padding:5px 0; color:#68706b;">来源包</td>'
                f'<td>{esc(inv.cycle)}</td></tr>'
            )
        related_summary = "无"
        if inv.related_cards:
            related_summary = "；".join(
                f"{card.category}：{card.name}"
                for card in inv.related_cards[:8]
            )
            if len(inv.related_cards) > 8:
                related_summary += f"；等 {len(inv.related_cards)} 张"

        return f"""
        <html>
        <body style="font-family:'Microsoft YaHei UI','Microsoft YaHei','Segoe UI'; color:#202522;">
          <div style="margin-bottom:10px;">
            <span style="display:inline-block; padding:5px 9px; border:1px solid #d9ded8; border-radius:10px; background:#eef0ec; color:#4f5852;">
              {esc(cycle_group)}
            </span>
            <span style="display:inline-block; padding:5px 9px; border:1px solid #d9ded8; border-radius:10px; background:#fbfdfd; margin-left:4px;">
              {esc(inv.career)}
            </span>
            <span style="display:inline-block; padding:5px 9px; border:1px solid #d9ded8; border-radius:10px; background:#fbfdfd; margin-left:4px;">
              副职介：{esc(inv.sub_career)}
            </span>
            <span style="display:inline-block; padding:5px 9px; border:1px solid {status_color}; border-radius:10px; background:{status_bg}; color:{status_color}; margin-left:4px;">
              {status}
            </span>
          </div>

          <table cellspacing="0" cellpadding="0" style="width:100%; margin-bottom:10px;">
            <tr>
              <td style="width:33%; padding:9px; border:1px solid #d9ded8; background:#ffffff;">
                <div style="font-size:12px; color:#68706b;">小张玩过</div>
                <div style="font-size:22px; font-weight:700; color:#202522;">{inv.play_zhang}</div>
              </td>
              <td style="width:33%; padding:9px; border:1px solid #d9ded8; background:#ffffff;">
                <div style="font-size:12px; color:#68706b;">小胡玩过</div>
                <div style="font-size:22px; font-weight:700; color:#202522;">{inv.play_hu}</div>
              </td>
              <td style="width:34%; padding:9px; border:1px solid #d9ded8; background:#ffffff;">
                <div style="font-size:12px; color:#68706b;">记录状态</div>
                <div style="font-size:18px; font-weight:700; color:{status_color};">{status}</div>
              </td>
            </tr>
          </table>

          <table cellspacing="0" cellpadding="0" style="width:100%; font-size:13px;">
            <tr><td style="padding:5px 0; color:#68706b; width:86px;">别称</td><td>{esc(inv.alias)}</td></tr>
            <tr><td style="padding:5px 0; color:#68706b;">本次玩家</td><td>{esc(player_text)}</td></tr>
            {source_cycle_row}
            <tr><td style="padding:5px 0; color:#68706b;">专属卡/弱点</td><td>{esc(related_summary)}</td></tr>
            <tr><td style="padding:5px 0; color:#68706b;">ArkhamDB</td><td>{esc(code_text)}</td></tr>
            <tr><td style="padding:5px 0; color:#68706b;">卡牌页面</td><td style="color:#1f7471;">{esc(url_text)}</td></tr>
          </table>
        </body>
        </html>
        """

    def _format_investigator_detail(
        self,
        inv: Investigator,
        player: Optional[str],
        committed: Optional[bool] = None,
    ) -> str:
        cycle_group = _cycle_display_group(inv.cycle)
        lines = [
            f"循环：{cycle_group}",
            f"调查员：{inv.name}",
            f"别称：{inv.alias or '（无）'}",
            f"职介：{inv.career}",
            f"副职介：{inv.sub_career or '（无）'}",
            f"小张玩过几次：{inv.play_zhang}",
            f"小胡玩过几次：{inv.play_hu}",
        ]
        if cycle_group != inv.cycle:
            lines.append(f"来源包：{inv.cycle}")
        if inv.code:
            lines.append(f"ArkhamDB 编号：{inv.code}")
        if inv.related_cards:
            lines.append("专属卡/弱点：" + "；".join(
                f"{card.category}：{card.name}"
                for card in inv.related_cards[:8]
            ))
        if inv.card_url:
            lines.append(f"卡牌页面：{inv.card_url}")
        if player:
            lines.append(f"本次为玩家：{player} 选择")
        if committed is not None:
            lines.append(f"记录状态：{'已记录' if committed else '未记录'}")
        return "\n".join(lines)

    def _refresh_dynamic_panels(self):
        self._refresh_top_labels()
        self._refresh_candidate_tree()

    def _refresh_top_labels(self):
        remaining = len(self.picker.remaining)
        selected = len(self.picker.selected)
        pending = sum(1 for record in self.picker.history if not record.committed)
        self.label_remaining.setText(f"候选 {remaining} / 总计 {remaining + selected}")
        self.label_history_state.setText(f"队伍 {len(self.picker.history)} 人 · 未记录 {pending}")

        def summarize(items: List[str], limit: int = 3) -> str:
            if not items:
                return "无"
            if len(items) <= limit:
                return "、".join(items)
            return "、".join(items[:limit]) + f" 等 {len(items)} 项"

        rule_parts = []
        rule_parts.append("职介不重复：开" if self.chk_unique_career.isChecked() else "职介不重复：关")
        if self.chk_unique_career.isChecked():
            locked = self.picker.get_locked_careers()
            rule_parts.append(f"已占职介：{summarize(locked)}")
        if self.chk_force_sub_unique.isChecked():
            rule_parts.append("副职介不重复：开")
        if self.chk_assign_player.isChecked():
            rule_parts.append(f"加权玩家：{self.combo_player.currentText()}")
        if self.chk_lock_career.isChecked():
            lock_text = self.combo_lock_career.currentText().strip() or "未选择"
            all_text = "含所有" if self.chk_allow_all_for_lock.isChecked() else "不含所有"
            rule_parts.append(f"锁定职介：{lock_text}（{all_text}）")
        if self.chk_exclude_career.isChecked():
            rule_parts.append(f"排除职介：{summarize(self.combo_exclude_career.checked_items())}")
        if self.chk_limit_cycles.isChecked():
            rule_parts.append(f"循环池：{summarize(self.combo_cycles.checked_items(), limit=2)}")

        self.label_locked_careers.setText("规则摘要：" + "；".join(rule_parts))

    def _refresh_candidate_tree(self):
        if not hasattr(self, "tree_candidates"):
            return

        self.tree_candidates.clear()
        tab_index = self.bottom_tabs.indexOf(self.tree_candidates) if hasattr(self, "bottom_tabs") else -1

        if self.chk_limit_cycles.isChecked() and not self.combo_cycles.checked_items():
            item = QTreeWidgetItem(["请至少选择一个循环分组", "", "", "", ""])
            item.setForeground(0, QBrush(QColor("#9b2632")))
            self.tree_candidates.addTopLevelItem(item)
            if tab_index >= 0:
                self.bottom_tabs.setTabText(tab_index, "候选池预览（0）")
            return

        candidates = self.picker.candidate_pool(**self._current_filter_options())
        if tab_index >= 0:
            self.bottom_tabs.setTabText(tab_index, f"候选池预览（{len(candidates)}）")

        if not candidates:
            item = QTreeWidgetItem(["当前规则下没有候选调查员", "", "", "", ""])
            item.setForeground(0, QBrush(QColor("#9b2632")))
            self.tree_candidates.addTopLevelItem(item)
            return

        grouped: Dict[str, List[Investigator]] = {}
        for inv in candidates:
            grouped.setdefault(_cycle_display_group(inv.cycle), []).append(inv)

        for group in _sort_cycles(list(grouped.keys())):
            items = sorted(grouped[group], key=_investigator_sort_key)
            group_item = QTreeWidgetItem([
                f"{group}（{len(items)}）",
                "",
                "",
                str(sum(inv.play_zhang for inv in items)),
                str(sum(inv.play_hu for inv in items)),
            ])
            group_item.setExpanded(True)
            group_font = group_item.font(0)
            group_font.setBold(True)
            for col in range(self.tree_candidates.columnCount()):
                group_item.setFont(col, group_font)
                group_item.setBackground(col, QBrush(QColor("#eef0ec")))
            self.tree_candidates.addTopLevelItem(group_item)

            for inv in items:
                child = QTreeWidgetItem([
                    inv.name,
                    inv.career,
                    inv.sub_career or "无",
                    str(inv.play_zhang),
                    str(inv.play_hu),
                ])
                child.setToolTip(
                    0,
                    f"{inv.name}\n来源包：{inv.cycle}\n编号：{inv.code or '无'}\n别称：{inv.alias or '无'}",
                )
                group_item.addChild(child)

    def _path_to_url(self, path: str) -> str:
        return QUrl.fromLocalFile(path).toString()

    def _rebuild_history_list(self):
        """
        按当前 history 重建历史列表，并设置悬停 tooltip（含图片）。
        """
        self.list_history.clear()
        for idx, record in enumerate(self.picker.history, start=1):
            inv = record.inv
            player = record.player

            # 副职介显示用一个友好字符串
            sub_str = inv.sub_career if inv.sub_career else "无"
            status = "已记录" if record.committed else "未记录"
            status_prefix = f"[{status}]"

            if player:
                text = f"{status_prefix} {idx}. {inv.name}（{inv.career} / {sub_str}，为 {player}）"
            else:
                text = f"{status_prefix} {idx}. {inv.name}（{inv.career} / {sub_str}）"

            item = QListWidgetItem()
            item.setData(Qt.ItemDataRole.UserRole, text)
            if record.committed:
                item.setForeground(QBrush(QColor("#256a45")))
                item.setBackground(QBrush(QColor("#f2f8f5")))
            else:
                item.setForeground(QBrush(QColor("#9b2632")))
                item.setBackground(QBrush(QColor("#fff7f7")))

            # 构造 tooltip HTML，内嵌图片（大图）
            html_lines = [
                f"<b>{inv.name}</b>（{inv.career}）",
            ]
            if player:
                html_lines.append(f"为 <b>{player}</b> 选择")
            html_lines.append(f"记录状态：{status}")
            if inv.sub_career:
                html_lines.append(f"副职介：{inv.sub_career}")
            html_lines.append("<br/>")

            img_html = ""
            img1 = _local_image_path(self.base_dir, inv.img1)
            img2 = _local_image_path(self.base_dir, inv.img2)
            if img1:
                img_html += f'<img src="{self._path_to_url(img1)}" width="700">&nbsp;'
            if img2:
                img_html += f'<img src="{self._path_to_url(img2)}" width="700">'
            if img_html:
                html_lines.append(img_html)

            tooltip_html = "<html><body>" + "<br/>".join(html_lines) + "</body></html>"
            item.setToolTip(tooltip_html)

            self.list_history.addItem(item)

            row = QWidget()
            row.setMinimumHeight(54)
            row_layout = QHBoxLayout(row)
            row_layout.setContentsMargins(10, 6, 10, 6)
            row_layout.setSpacing(12)

            label = QLabel(text)
            label.setWordWrap(False)
            label.setMinimumHeight(34)
            label.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Preferred)
            label.setToolTip(tooltip_html)
            label.setStyleSheet(
                "color: #256a45; font-weight: 600;" if record.committed
                else "color: #9b2632; font-weight: 600;"
            )
            row_layout.addWidget(label, stretch=1)

            player_combo = QComboBox()
            if record.committed and record.player:
                player_combo.addItems(["小张", "小胡"])
            else:
                player_combo.addItems(["未指定", "小张", "小胡"])
            player_combo.setFixedWidth(124)
            player_combo.setMinimumHeight(34)
            player_combo.setCurrentText(player or "未指定")
            player_combo.currentTextChanged.connect(
                lambda value, record=record: self._on_history_player_changed(record, value)
            )
            row_layout.addWidget(player_combo)

            item.setSizeHint(QSize(0, 58))
            self.list_history.setItemWidget(item, row)

    def _on_history_player_changed(self, record: PickRecord, value: str):
        new_player = None if value == "未指定" else value
        old_player = record.player
        if old_player == new_player:
            return

        if record.committed:
            if old_player:
                self._adjust_player_count(record.inv, old_player, -1)
            if new_player:
                self._adjust_player_count(record.inv, new_player, 1)
                if record.log_id:
                    _update_play_record_player(self.base_dir, record.log_id, new_player)
                else:
                    record.log_id = _append_play_record(self.base_dir, record.inv, new_player)
            elif record.log_id:
                _remove_play_record(self.base_dir, record.log_id)
                record.log_id = ""

        record.player = new_player
        if record.committed:
            self._append_log(
                f"已调整记录归属：{record.inv.name} 从 {old_player or '未指定'} 改为 {new_player or '未指定'}。"
            )
        else:
            self._append_log(f"已分配玩家：{record.inv.name} -> {new_player or '未指定'}。")

        if self.picker.history and self.picker.history[-1] is record:
            self._show_current_investigator(record.inv, record.player, record.committed)

        self._rebuild_history_list()
        self._refresh_dynamic_panels()

    def _append_log(self, msg: str):
        self.text_log.append(msg)

    def _clear_current_images(self):
        self.label_img1.clear()
        self.label_img2.clear()
        self.label_img1.setText("")
        self.label_img2.setText("")
        self._clear_related_cards()

    def _clear_related_cards(self):
        if not hasattr(self, "tree_related_cards"):
            return
        self.tree_related_cards.clear()
        item = QTreeWidgetItem(["暂无专属卡/弱点数据", "", "", ""])
        item.setForeground(0, QBrush(QColor("#68706b")))
        self.tree_related_cards.addTopLevelItem(item)

    def _set_label_image(self, label: QLabel, path: str, missing_text: str = "本地卡图未缓存"):
        if path and _is_url(path):
            path = _local_image_path(self.base_dir, path)

        if path and os.path.exists(path):
            pix = QPixmap(path)
            if not pix.isNull():
                pix = pix.scaled(
                    label.width(), label.height(),
                    Qt.AspectRatioMode.KeepAspectRatio,
                    Qt.TransformationMode.SmoothTransformation
                )
                label.setPixmap(pix)
                return
        label.clear()
        label.setText(missing_text)

    def _update_current_images(self, inv: Investigator):
        front_missing = "数据源缺少正面图" if not inv.img1 else "本地正面图未缓存"
        back_missing = "数据源未提供背面图" if not inv.img2 else "本地背面图未缓存"
        self._set_label_image(self.label_img1, inv.img1, front_missing)
        self._set_label_image(self.label_img2, inv.img2, back_missing)
        self._update_related_cards(inv)

    def _update_related_cards(self, inv: Investigator):
        if not hasattr(self, "tree_related_cards"):
            return
        self.tree_related_cards.clear()
        if not inv.related_cards:
            self._clear_related_cards()
            return

        for related in inv.related_cards:
            item = QTreeWidgetItem([
                related.name,
                related.category if related.category else related.card_type,
                related.pack,
                related.code,
            ])
            if related.category == "专属弱点":
                item.setForeground(0, QBrush(QColor("#9b2632")))
            else:
                item.setForeground(0, QBrush(QColor("#202522")))

            html_lines = [
                f"<b>{html.escape(related.name)}</b>",
                f"{html.escape(related.category)} · {html.escape(related.card_type or '未知类型')}",
                f"来源：{html.escape(related.pack or '未知')}　编号：{html.escape(related.code or '无')}",
                "<br/>",
            ]
            img_html = ""
            img1 = _local_image_path(self.base_dir, related.img1)
            img2 = _local_image_path(self.base_dir, related.img2)
            if img1:
                img_html += f'<img src="{self._path_to_url(img1)}" width="360">&nbsp;'
            if img2:
                img_html += f'<img src="{self._path_to_url(img2)}" width="360">'
            if img_html:
                html_lines.append(img_html)
            else:
                html_lines.append("本地卡图未缓存")
            tooltip = "<html><body>" + "<br/>".join(html_lines) + "</body></html>"
            for col in range(self.tree_related_cards.columnCount()):
                item.setToolTip(col, tooltip)
            self.tree_related_cards.addTopLevelItem(item)

    def closeEvent(self, event):
        self.executor.shutdown(wait=False, cancel_futures=True)
        super().closeEvent(event)


def main():
    app = QApplication(sys.argv)
    window = MainWindow()
    window.show()
    sys.exit(app.exec())


if __name__ == "__main__":
    main()
