#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
╔══════════════════════════════════════════════════════════════════╗
║                        متره‌یار  MetreYar                       ║
║      نرم‌افزار حرفه‌ای متره و برآورد ساختمان - نسخه ۲.۰.۰       ║
║       طراحی‌شده برای دفتر فنی ایران - کاملاً آفلاین             ║
║                Python + Streamlit + SQLite                       ║
╚══════════════════════════════════════════════════════════════════╝
"""

import streamlit as st
import pandas as pd
import sqlite3
import hashlib
import json
import math
import os
import re
import io
import sys
import logging
import difflib
import tempfile
from pathlib import Path
from datetime import datetime
from dataclasses import dataclass, field, asdict
from typing import Any, Dict, List, Optional, Tuple, Union, Set
from enum import Enum
from collections import Counter, defaultdict

# ──────────────────────────────────────────────
# Logging Configuration
# ──────────────────────────────────────────────
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(name)s: %(message)s",
)
logger = logging.getLogger("MetreYar")

# ──────────────────────────────────────────────
# Application Constants
# ──────────────────────────────────────────────
APP_NAME = "متره‌یار"
APP_VERSION = "2.0.0"
DB_NAME = "metreyar.db"

DEFAULT_WASTE_PERCENTS: Dict[str, float] = {
    "concrete": 5.0,
    "lean_concrete": 3.0,
    "rebar": 5.0,
    "formwork": 5.0,
    "block_joist": 5.0,
    "eps_block": 3.0,
    "masonry": 5.0,
    "default": 3.0,
}

REBAR_UNIT_WEIGHT: Dict[int, float] = {
    6: 0.222, 8: 0.395, 10: 0.617, 12: 0.888,
    14: 1.208, 16: 1.578, 18: 1.998, 20: 2.466,
    22: 2.984, 25: 3.853, 28: 4.834, 30: 5.549,
    32: 6.313, 36: 7.990, 40: 9.864,
}

UNIT_CONVERSIONS = {
    "ft_to_m": 0.3048, "in_to_m": 0.0254, "ft2_to_m2": 0.092903,
    "ft3_to_m3": 0.0283168, "lb_to_kg": 0.453592,
    "in2_to_m2": 0.00064516, "yd3_to_m3": 0.764555,
}

# Iranian Price Book (فهرست بها) Chapter Categories
CHAPTER_TYPES = {
    "01": "عملیات تخریب",
    "02": "عملیات خاکی با دست",
    "03": "عملیات خاکی با ماشین",
    "04": "عملیات بنایی با سنگ",
    "05": "قالب‌بندی چوبی و فلزی",
    "06": "کارهای فولادی با پیچ و مهره",
    "07": "کارهای فولادی با میلگرد",
    "08": "بتن درجا",
    "09": "بتن پیش‌ساخته",
    "10": "کارهای بنایی و آجرچینی",
    "11": "عایق‌کاری رطوبتی",
    "12": "عایق‌کاری حرارتی",
    "13": "فرش کف و پوشش دیوار",
    "14": "کارهای فلزی سبک",
    "15": "کارهای چوبی",
    "16": "کارهای درب و پنجره",
    "17": "اندود و بندکشی",
    "18": "نقاشی",
    "19": "شیشه‌کاری",
    "20": "کاشی‌کاری",
    "21": "سنگ‌کاری",
    "22": "لوله‌کشی گاز",
    "23": "کارهای فاضلاب و آب باران",
    "24": "کارهای متفرقه",
    "25": "کارهای برقی",
}

# Chapters excluded from auto-matching (renovation only)
EXCLUDED_CHAPTERS = ["01"]  # Demolition chapter should not match new construction

# ──────────────────────────────────────────────
# Schemas
# ──────────────────────────────────────────────
PRICE_LIST_SCHEMA = {
    "item_code": str, "description": str, "unit": str,
    "unit_price": float, "chapter": str, "chapter_title": str,
    "is_starred": bool,
}

MATCHED_ITEM_SCHEMA = {
    "source_file": str, "source_table": str, "row_index": int,
    "raw_name": str, "normalized_name": str,
    "element_type": str, "element_position": str,
    "category": str, "structural_group": str, "sub_group": str,
    "item_code": str, "item_description": str, "unit": str,
    "raw_quantity": float, "waste_percent": float, "final_quantity": float,
    "unit_price": float, "total_price": float, "match_method": str,
    "match_confidence": float, "match_details": str,
    "needs_review": bool, "issues": str, "is_title_row": bool,
}

REBAR_LISTOF_SCHEMA = {
    "source_file": str, "source_table": str, "location": str,
    "structural_group": str, "sub_group": str,
    "element_type": str, "element_position": str,
    "diameter": float, "bar_length": float, "cut_length": float,
    "count": float, "bend_shape": str,
    "net_weight": float, "waste_percent": float, "gross_weight": float,
    "item_code": str, "unit_price": float, "total_price": float,
}


def _pandas_dtype(t: type) -> str:
    if t == str: return "object"
    if t == float: return "float64"
    if t == int: return "int64"
    if t == bool: return "bool"
    return "object"


def make_empty_df(schema: Dict[str, type]) -> pd.DataFrame:
    return pd.DataFrame({col: pd.Series(dtype=_pandas_dtype(t)) for col, t in schema.items()})


# ──────────────────────────────────────────────
# Text Normalizer (Comprehensive)
# ──────────────────────────────────────────────
class TextNormalizer:
    """Comprehensive Persian/English text normalizer for construction terms."""

    _CHAR_MAP = str.maketrans({
        'ك': 'ک', 'ي': 'ی', 'ى': 'ی', 'ئ': 'ی', 'ء': '',
        '٠': '۰', '١': '۱', '٢': '۲', '٣': '۳', '٤': '۴',
        '٥': '۵', '٦': '۶', '٧': '۷', '٨': '۸', '٩': '۹',
        'ﺁ': 'آ', 'ﺂ': 'آ', 'ﺃ': 'ا', 'ﺄ': 'ا', 'ﺅ': 'و', 'ﺆ': 'و',
        'ﺇ': 'ا', 'ﺈ': 'ا', 'ﺋ': 'ی', 'ﺌ': 'ی', 'ﺍ': 'ا', 'ﺎ': 'ا',
        'ﺏ': 'ب', 'ﺐ': 'ب', 'ﺑ': 'ب', 'ﺒ': 'ب', 'ﺓ': 'ه', 'ﺔ': 'ه',
        'ﺕ': 'ت', 'ﺖ': 'ت', 'ﺗ': 'ت', 'ﺘ': 'ت', 'ﺙ': 'ث', 'ﺚ': 'ث',
        'ﺛ': 'ث', 'ﺜ': 'ث', 'ﺝ': 'ج', 'ﺞ': 'ج', 'ﺟ': 'ج', 'ﺠ': 'ج',
        'ﺡ': 'ح', 'ﺢ': 'ح', 'ﺣ': 'ح', 'ﺤ': 'ح', 'ﺥ': 'خ', 'ﺦ': 'خ',
        'ﺧ': 'خ', 'ﺨ': 'خ', 'ﺩ': 'د', 'ﺪ': 'د', 'ﺫ': 'ذ', 'ﺬ': 'ذ',
        'ﺭ': 'ر', 'ﺮ': 'ر', 'ﺯ': 'ز', 'ﺰ': 'ز', 'ﺱ': 'س', 'ﺲ': 'س',
        'ﺳ': 'س', 'ﺴ': 'س', 'ﺵ': 'ش', 'ﺶ': 'ش', 'ﺷ': 'ش', 'ﺸ': 'ش',
        'ﺹ': 'ص', 'ﺺ': 'ص', 'ﺻ': 'ص', 'ﺼ': 'ص', 'ﺽ': 'ض', 'ﺾ': 'ض',
        'ﺿ': 'ض', 'ﻀ': 'ض', 'ﻁ': 'ط', 'ﻂ': 'ط', 'ﻃ': 'ط', 'ﻄ': 'ط',
        'ﻅ': 'ظ', 'ﻆ': 'ظ', 'ﻇ': 'ظ', 'ﻈ': 'ظ', 'ﻉ': 'ع', 'ﻊ': 'ع',
        'ﻋ': 'ع', 'ﻌ': 'ع', 'ﻍ': 'غ', 'ﻎ': 'غ', 'ﻏ': 'غ', 'ﻐ': 'غ',
        'ﻑ': 'ف', 'ﻒ': 'ف', 'ﻓ': 'ف', 'ﻔ': 'ف', 'ﻕ': 'ق', 'ﻖ': 'ق',
        'ﻗ': 'ق', 'ﻘ': 'ق', 'ﻙ': 'ک', 'ﻚ': 'ک', 'ﻛ': 'ک', 'ﻜ': 'ک',
        'ﻝ': 'ل', 'ﻞ': 'ل', 'ﻟ': 'ل', 'ﻠ': 'ل', 'ﻡ': 'م', 'ﻢ': 'م',
        'ﻣ': 'م', 'ﻤ': 'م', 'ﻥ': 'ن', 'ﻦ': 'ن', 'ﻧ': 'ن', 'ﻨ': 'ن',
        'ﻩ': 'ه', 'ﻪ': 'ه', 'ﻫ': 'ه', 'ﻬ': 'ه', 'ﻭ': 'و', 'ﻮ': 'و',
        'ﻱ': 'ی', 'ﻲ': 'ی', 'ﻳ': 'ی', 'ﻴ': 'ی',
    })

    _FA_DIGITS = "۰۱۲۳۴۵۶۷۸۹"
    _EN_DIGITS = "0123456789"

    ALIASES: Dict[str, Set[str]] = {
        "concrete": {
            "بتن", "بتن سازه‌ای", "بتن سازه ای", "بتن سازهای", "بتن ریزی",
            "concrete", "conc", "conc.", "rc", "reinforced concrete", "بتن مسلح", "بتن آرمه",
        },
        "lean_concrete": {
            "بتن مگر", "بتن لاغر", "بتن نظافت", "lc-01", "lc 01",
            "lean concrete", "lean conc", "lean", "blinding", "بتن کف", "بتن زیر پی",
        },
        "rebar": {
            "آرماتور", "میلگرد", "میلگرد طولی", "میلگرد عرضی", "خاموت", "آرماتور بندی", "فولاد",
            "rebar", "rb", "reinf", "reinforcement", "steel bar", "bar", "stirrup",
        },
        "formwork": {
            "قالب", "قالب‌بندی", "قالب بندی", "قالبندی",
            "formwork", "form", "fw", "shuttering", "قالب فلزی", "قالب چوبی",
        },
        "column": {
            "ستون", "ستون بتنی", "column", "col", "col.", "ستون بتنی مسلح",
        },
        "beam": {
            "تیر", "تیر بتنی", "beam", "bm", "framing", "تیر اصلی", "تیر فرعی",
        },
        "foundation": {
            "پی", "فونداسیون", "فنداسیون", "شالوده", "wall foundation", "wall_foundation", "wf_",
            "foundation", "footing", "ftg", "fnd", "fndn", "پی نواری", "پی گسترده", "رادیه",
            "raft", "strip footing", "mat foundation",
        },
        "slab": {
            "سقف", "دال", "دال بتنی", "slab", "floor slab", "roof slab", "floor",
            "دال یک‌طرفه", "دال دو‌طرفه", "دال یکطرفه", "دال دوطرفه",
        },
        "block_joist": {
            "تیرچه", "تیرچه بلوک", "سقف تیرچه", "joist", "jst", "block joist",
            "تیرچه و بلوک", "سقف تیرچه بلوک",
        },
        "eps_block": {
            "یونولیت", "eps", "پلی استایرن", "پلی‌استایرن", "بلوک یونولیت",
        },
        "tie_beam": {
            "کلاف", "تیر کلاف", "tie beam", "tie", "ct", "crown tie", "کلاف افقی", "کلاف عمودی",
        },
        "stair": {
            "پله", "راه‌پله", "راه پله", "stair", "stairs", "staircase", "پله بتنی", "str",
        },
        "wall": {
            "دیوار", "دیوار بتنی", "دیوار برشی", "shear wall", "retaining wall", "دیوار حائل",
        },
        "masonry": {
            "بنایی", "آجرکاری", "آجر", "بلوک", "masonry", "brick", "cmu", "بلوک سیمانی",
        },
    }

    _ALIAS_REVERSE: Dict[str, str] = {}

    @classmethod
    def _build_reverse(cls) -> None:
        if cls._ALIAS_REVERSE: return
        for canonical, aliases in cls.ALIASES.items():
            for alias in aliases:
                cls._ALIAS_REVERSE[cls._normalize_text(alias)] = canonical

    @classmethod
    def fa_to_en_digits(cls, text: str) -> str:
        if not text: return ""
        result = []
        for ch in str(text):
            idx = cls._FA_DIGITS.find(ch)
            if idx >= 0: result.append(cls._EN_DIGITS[idx])
            elif '\u0660' <= ch <= '\u0669': result.append(str(ord(ch) - 0x0660))
            else: result.append(ch)
        return "".join(result)

    @classmethod
    def en_to_fa_digits(cls, text: str) -> str:
        if not text: return ""
        return "".join(cls._FA_DIGITS[int(ch)] if ch.isdigit() else ch for ch in str(text))

    @classmethod
    def _normalize_text(cls, text: str) -> str:
        if not text: return ""
        t = str(text).strip().translate(cls._CHAR_MAP)
        t = cls.fa_to_en_digits(t).lower()
        t = t.replace("\u200c", " ").replace("\u200b", "")
        t = t.replace("\u200d", "").replace("\u200e", "").replace("\u200f", "")
        t = re.sub(r'[\u064B-\u065F\u0670]', '', t)
        t = re.sub(r'[-_/\\.,;:!?(){}[\]"\'«»]+', ' ', t)
        return re.sub(r'\s+', ' ', t).strip()

    @classmethod
    def normalize(cls, text: str) -> str:
        return cls._normalize_text(text)

    @classmethod
    def resolve_alias(cls, text: str) -> Optional[str]:
        cls._build_reverse()
        norm = cls._normalize_text(text)
        if norm in cls._ALIAS_REVERSE: return cls._ALIAS_REVERSE[norm]
        words = norm.split()
        for w in words:
            if w in cls._ALIAS_REVERSE: return cls._ALIAS_REVERSE[w]
        for i in range(len(words) - 1):
            pair = f"{words[i]} {words[i + 1]}"
            if pair in cls._ALIAS_REVERSE: return cls._ALIAS_REVERSE[pair]
        return None

    @classmethod
    def detect_category(cls, text: str) -> Tuple[str, float]:
        norm = cls._normalize_text(text)
        if not norm: return ("unknown", 0.0)

        if any(k in norm for k in ["wall foundation", "wf_", "footing", "پی", "فونداسیون", "شالوده"]):
            return ("foundation", 0.95)

        alias = cls.resolve_alias(norm)
        if alias: return (alias, 0.95)

        cls._build_reverse()
        best_match = None
        best_score = 0.0
        for alias_norm, canonical in cls._ALIAS_REVERSE.items():
            if len(alias_norm) < 2: continue
            if alias_norm in norm:
                score = len(alias_norm) / max(len(norm), 1)
                if score > best_score:
                    best_score = score
                    best_match = canonical
        if best_match and best_score > 0.3:
            return (best_match, min(best_score + 0.3, 0.9))
        return ("unknown", 0.0)

    @classmethod
    def detect_structural_group(cls, text: str) -> str:
        cat, _ = cls.detect_category(text)
        group_map = {
            "foundation": "پی", "column": "ستون", "beam": "تیر",
            "slab": "سقف", "block_joist": "سقف تیرچه", "eps_block": "سقف تیرچه",
            "tie_beam": "کلاف", "stair": "پله", "wall": "دیوار",
        }
        return group_map.get(cat, "سایر")

    @classmethod
    def safe_float(cls, value: Any) -> float:
        if value is None: return 0.0
        if isinstance(value, (int, float)): return float(value)
        t = cls.fa_to_en_digits(str(value).strip())
        t = t.replace(',', '.').replace('٫', '.')
        t = re.sub(r'[^\d.\-+eE]', '', t)
        if not t or t in ('.', '-', '+'): return 0.0
        try: return float(t)
        except ValueError: return 0.0

    @classmethod
    def parse_number_with_unit(cls, text: str) -> Tuple[Optional[float], Optional[str]]:
        if not text: return (None, None)
        t = cls.fa_to_en_digits(str(text).strip())
        m = re.match(r'^([+-]?\d+(?:[.,]\d+)?)\s*([a-zA-Z³²%°]+.*)?$', t)
        if m:
            try: val = float(m.group(1).replace(',', '.'))
            except ValueError: return (None, None)
            unit = m.group(2).strip() if m.group(2) else None
            return (val, unit)
        try: return (float(t.replace(',', '.')), None)
        except ValueError: return (None, None)


# ──────────────────────────────────────────────
# Revit Element Detector (فوق‌حرفه‌ای)
# ──────────────────────────────────────────────
class RevitElementDetector:
    """Detects Revit element type from Mark/Name based on Iranian structural naming conventions.
    
    Structural Naming Conventions:
    - BP  = Beam of Foundation Pile (تیر شمعی/آرماتور پی)
    - LG  = Longitudinal Girder (تیر طولی)
    - TR  = Transverse Rebar (میلگرد عرضی)
    - CT  = Cross Tie / Coupling Tie (کلاف)
    - STR = Stair (پله)
    - JST = Joist Stirrup (خاموت تیرچه)
    - JT  = Joist Tie (آرماتور اتصال تیرچه)
    - TM  = Temperature Mesh (میلگرد حرارتی/توری)
    - C   = Column (ستون) - e.g., C1, C2
    - L   = Longitudinal (طولی)
    - T   = Transverse (عرضی) - e.g., T(A-B)
    - ST  = Stirrup (خاموت) - e.g., BP4-ST1-ST
    - B   = Bottom (پایین)
    - Top / T = Top (بالا)
    - R   = Reinforcement / Additional (تقویتی)
    - ADD = Additional (تقویتی)
    - Main = Main bar (اصلی)
    - Starter = Anchor bar (انتظار)
    - F = Foundation/Field
    """

    # Prefix → (structural_group, sub_group)
    PREFIX_MAP: Dict[str, Tuple[str, str]] = {
        "BP": ("پی", "آرماتور پی"),
        "LG": ("تیر", "آرماتور طولی تیر"),
        "TR": ("تیر", "آرماتور عرضی تیر"),
        "CT": ("کلاف", "کلاف"),
        "STR": ("پله", "آرماتور پله"),
        "JST": ("سقف تیرچه", "خاموت تیرچه"),
        "JT": ("سقف تیرچه", "آرماتور اتصال تیرچه"),
        "TM": ("سقف", "میلگرد حرارتی"),
        "C1": ("ستون", "آرماتور ستون"),
        "C2": ("ستون", "آرماتور ستون"),
        "C3": ("ستون", "آرماتور ستون"),
        "C4": ("ستون", "آرماتور ستون"),
        "C5": ("ستون", "آرماتور ستون"),
    }

    # Wall Foundation Marks (L for longitudinal, T for transverse)
    FOUNDATION_MARK_PATTERNS = [
        r'^L\(\s*\d+\s*[-–]\s*\d+\s*\)',   # L(1-2), L(2-3)
        r'^T\(\s*[A-Z]+\s*[-–]\s*[A-Z]+\s*\)',  # T(A-B), T(B-C)
    ]

    @classmethod
    def detect_element(cls, mark: str, family: str = "", table_title: str = "") -> Dict:
        """Detect element structure from Mark/Name.
        Returns dict with: structural_group, sub_group, element_type, element_position
        """
        result = {
            "structural_group": "سایر",
            "sub_group": "نامشخص",
            "element_type": "unknown",
            "element_position": "",
        }
        
        if not mark and not family:
            return result
        
        combined = f"{mark} {family}".strip()
        combined_lower = combined.lower()
        table_lower = table_title.lower() if table_title else ""

        # ==========================================
        # 1. FOUNDATION (Wall Foundation / L(...)/T(...))
        # ==========================================
        for pattern in cls.FOUNDATION_MARK_PATTERNS:
            if re.search(pattern, mark, re.IGNORECASE):
                result["structural_group"] = "پی"
                result["sub_group"] = "پی نواری"
                result["element_type"] = "wall_foundation"
                if mark.upper().startswith("L"):
                    result["element_position"] = "طولی"
                elif mark.upper().startswith("T"):
                    result["element_position"] = "عرضی"
                return result

        if "wall foundation" in combined_lower or "wf_" in combined_lower:
            result["structural_group"] = "پی"
            result["sub_group"] = "پی نواری"
            result["element_type"] = "wall_foundation"
            return result

        if "foundation slab" in combined_lower or "100mm foundation" in combined_lower or "lc-01" in combined_lower:
            result["structural_group"] = "پی"
            result["sub_group"] = "بتن مگر"
            result["element_type"] = "lean_concrete"
            return result

        if "footing" in combined_lower:
            result["structural_group"] = "پی"
            result["sub_group"] = "پی منفرد"
            result["element_type"] = "footing"
            return result

        # ==========================================
        # 2. Extract Prefix (e.g., "BP4-ST1-ADD-B1" -> "BP")
        # ==========================================
        prefix_match = re.match(r'^([A-Z]{1,4})(\d*)', mark.upper().strip())
        prefix = prefix_match.group(1) if prefix_match else ""
        
        # Check for exact prefix match
        for key, (grp, sub) in cls.PREFIX_MAP.items():
            if mark.upper().startswith(key):
                result["structural_group"] = grp
                result["sub_group"] = sub
                result["element_type"] = key.lower()
                break

        # ==========================================
        # 3. Detect Position (Top / Bottom / Longitudinal / Stirrup)
        # ==========================================
        mark_upper = mark.upper()
        
        # Stirrup detection (خاموت)
        if "-ST" in mark_upper or "STIRRUP" in combined_lower or "خاموت" in combined:
            if result["structural_group"] == "سایر":
                if "C1-" in mark_upper or "C2-" in mark_upper:
                    result["structural_group"] = "ستون"
            result["sub_group"] = "خاموت " + result["structural_group"] if result["structural_group"] != "سایر" else "خاموت"
            result["element_position"] = "خاموت"
            return result

        # ADD = Additional / Reinforcement (تقویتی)
        if "-ADD-" in mark_upper or "ADD " in mark_upper:
            if "B" in mark_upper.split("-")[-1]:
                result["element_position"] = "تقویتی پایین"
            elif "T" in mark_upper.split("-")[-1]:
                result["element_position"] = "تقویتی بالا"
            else:
                result["element_position"] = "تقویتی"
            result["sub_group"] = "آرماتور تقویتی " + result["structural_group"]
            return result

        # R1, R2, R3... = Reinforcement bars (تقویتی)
        r_match = re.search(r'-R(\d+)-([BT])', mark_upper)
        if r_match:
            r_num = r_match.group(1)
            pos = r_match.group(2)
            result["element_position"] = f"تقویتی {'پایین' if pos == 'B' else 'بالا'} R{r_num}"
            result["sub_group"] = f"آرماتور تقویتی {result['structural_group']}"
            return result

        # Main-B / Main-T
        if "-MAIN-B" in mark_upper:
            result["element_position"] = "اصلی پایین"
            result["sub_group"] = "آرماتور اصلی " + result["structural_group"]
        elif "-MAIN-T" in mark_upper:
            result["element_position"] = "اصلی بالا"
            result["sub_group"] = "آرماتور اصلی " + result["structural_group"]
        elif "-STARTER" in mark_upper or "STARTER-" in mark_upper:
            result["element_position"] = "انتظار"
            result["sub_group"] = "آرماتور انتظار " + result["structural_group"]
        elif "-TR-" in mark_upper:
            if mark_upper.endswith("-B"):
                result["element_position"] = "عرضی پایین"
            elif mark_upper.endswith("-T"):
                result["element_position"] = "عرضی بالا"
            else:
                result["element_position"] = "عرضی"
            result["sub_group"] = "آرماتور عرضی " + result["structural_group"]
        elif mark_upper.endswith("-B") or mark_upper.endswith("_B"):
            result["element_position"] = "پایین"
            if "آرماتور" not in result["sub_group"]:
                result["sub_group"] = "آرماتور اصلی " + result["structural_group"]
        elif mark_upper.endswith("-T") or mark_upper.endswith("_T"):
            result["element_position"] = "بالا"
            if "آرماتور" not in result["sub_group"]:
                result["sub_group"] = "آرماتور اصلی " + result["structural_group"]
        elif mark_upper.endswith("-L") or "-L-" in mark_upper:
            result["element_position"] = "طولی"
            if "آرماتور" not in result["sub_group"]:
                result["sub_group"] = "آرماتور طولی " + result["structural_group"]

        # ==========================================
        # 4. Table title override (if no prefix matched)
        # ==========================================
        if result["structural_group"] == "سایر" and table_title:
            if "پی" in table_title or "foundation" in table_lower:
                result["structural_group"] = "پی"
                result["sub_group"] = "پی"
            elif "ستون" in table_title or "column" in table_lower:
                result["structural_group"] = "ستون"
                result["sub_group"] = "ستون"
            elif "تیر" in table_title or "beam" in table_lower:
                result["structural_group"] = "تیر"
                result["sub_group"] = "تیر"
            elif "پله" in table_title or "stair" in table_lower:
                result["structural_group"] = "پله"
                result["sub_group"] = "پله"
            elif "سقف" in table_title or "slab" in table_lower or "joist" in table_lower:
                result["structural_group"] = "سقف"
                result["sub_group"] = "سقف"

        # ==========================================
        # 5. Family-based detection (Structural Columns / Framing)
        # ==========================================
        if "structural columns" in combined_lower or "concrete-rectangular-column" in combined_lower or "concrete-square-column" in combined_lower:
            result["structural_group"] = "ستون"
            result["sub_group"] = "بتن ستون"
            result["element_type"] = "column"
        elif "structural framing" in combined_lower or "concrete-rectangular beam" in combined_lower:
            result["structural_group"] = "تیر"
            result["sub_group"] = "بتن تیر"
            result["element_type"] = "beam"
        elif "cast-in-place stair" in combined_lower or "monolithic stair" in combined_lower or "monolithic run" in combined_lower:
            result["structural_group"] = "پله"
            result["sub_group"] = "بتن پله"
            result["element_type"] = "stair"
        elif "floor" in combined_lower and "slab" in combined_lower:
            if "topping" in combined_lower:
                result["structural_group"] = "سقف"
                result["sub_group"] = "بتن روی سقف"
            else:
                result["structural_group"] = "سقف"
                result["sub_group"] = "بتن دال"
        elif "تیرچه و یونولیت" in combined or "joist" in combined_lower:
            result["structural_group"] = "سقف تیرچه"
            if "یونولیت" in combined or "eps" in combined_lower:
                result["sub_group"] = "بلوک یونولیت"
                result["element_type"] = "eps_block"
            elif "پاشنه" in combined:
                result["sub_group"] = "بتن پاشنه تیرچه"
                result["element_type"] = "joist_concrete"
            else:
                result["sub_group"] = "تیرچه"
                result["element_type"] = "joist"

        return result

    @classmethod
    def extract_diameter(cls, text: str) -> int:
        """Extract rebar diameter from text (Φ18, Φ10, 18mm, A-I-8mm)."""
        if not text: return 0
        # Try φ or Φ format
        m = re.search(r'[φΦ]\s*(\d{1,2})', text)
        if m:
            try: return int(m.group(1))
            except: pass
        # Try "18 mm" format
        m = re.search(r'(\d{1,2})\s*mm', text, re.IGNORECASE)
        if m:
            try: return int(m.group(1))
            except: pass
        # Try "Rebar - Φ8" format
        m = re.search(r'rebar\s*-\s*[φΦ]?(\d{1,2})', text, re.IGNORECASE)
        if m:
            try: return int(m.group(1))
            except: pass
        # Try "A-I-8mm" format (A1 - 8mm)
        m = re.search(r'a[\-\s]*i[\-\s]*(\d{1,2})\s*mm', text, re.IGNORECASE)
        if m:
            try: return int(m.group(1))
            except: pass
        return 0

    @classmethod
    def is_a1_rebar(cls, text: str) -> bool:
        """Check if this is A1 (plain/round) rebar (میلگرد ساده)."""
        if not text: return False
        t = text.lower()
        return ("a-i-" in t or "a1" in t or "fy2400" in t or 
                "s240" in t or "plain" in t or "ساده" in text)

    @classmethod
    def is_ajdar_rebar(cls, text: str) -> bool:
        """Check if this is deformed rebar (میلگرد آجدار)."""
        if not text: return False
        t = text.lower()
        return ("a3" in t or "fy4000" in t or "s400" in t or 
                "deformed" in t or "آجدار" in text or 
                bool(re.search(r'[φΦ]\d', text)))


# ──────────────────────────────────────────────
# Fast Fuzzy Matcher
# ──────────────────────────────────────────────
class FuzzyMatcher:
    @staticmethod
    def best_match(query: str, candidates: List[str], threshold: float = 0.35) -> Optional[Tuple[str, float]]:
        if not query or not candidates: return None
        query_words = set(query.split())
        if not query_words: return None

        best_cand = None
        best_score = 0.0
        for cand in candidates:
            cand_words = set(cand.split())
            common = query_words.intersection(cand_words)
            if not common: continue
            overlap = len(common) / max(len(query_words), len(cand_words))
            seq = difflib.SequenceMatcher(None, query, cand).quick_ratio()
            final = max(overlap, seq)
            if final > best_score:
                best_score = final
                best_cand = cand
        if best_cand and best_score >= threshold:
            return (best_cand, best_score)
        return None

    @staticmethod
    def find_all_containing(query: str, candidates: List[Dict], keyword_field: str = "norm_desc",
                            keywords: List[str] = None, exclude_keywords: List[str] = None) -> List[Dict]:
        """Find all candidates that contain ALL required keywords AND NONE of excluded."""
        results = []
        keywords = keywords or []
        exclude_keywords = exclude_keywords or []
        for c in candidates:
            desc = c.get(keyword_field, "")
            if not all(k in desc for k in keywords): continue
            if any(k in desc for k in exclude_keywords): continue
            results.append(c)
        return results


# ══════════════════════════════════════════════════════════════════
# DatabaseManager - نسخه فوق‌حرفه‌ای دفتر فنی (v3.0.0)
# طراحی‌شده با پیشنهادات ۵ متخصص:
#   - کارشناس دفتر فنی (آنالیز بها، تعدیل، مقایسه)
#   - مدیر پروژه (KPI، زمان‌بندی)
#   - متخصص فهرست بها (تجمیعی، نشریه ۴۳۱۱)
#   - Data Scientist (بنچمارک، پیش‌بینی)
#   - UX Designer (One-Page Summary)
# ══════════════════════════════════════════════════════════════════

class DatabaseManager:
    """مدیر پایگاه داده SQLite برای ذخیره‌سازی دائمی پروژه‌های دفتر فنی.
    
    ویژگی‌های حرفه‌ای:
    ─────────────────────────────────────────
    • پروژه‌ها با متادیتای کامل (کارفرما، پیمانکار، مبلغ قرارداد)
    • فهرست بها با پشتیبانی از ردیف‌های ستاره‌دار (آنالیز بها)
    • جداول Revit با ذخیره‌سازی JSON کامل
    • قوانین Mapping با اولویت‌بندی
    • تنظیمات پرت به تفکیک دسته
    • ضرایب پیمان (بالاسری، منطقه‌ای، طبقات، ارتفاع)
    • آنالیز بها برای ردیف‌های ستاره‌دار
    • ذخیره تاریخچه صورت وضعیت‌ها (مقایسه پیشرفت)
    • شاخص‌های تعدیل بانک مرکزی (نشریه ۱۰۰)
    • بنچمارک پروژه‌های مشابه
    • لاگ عملیات (audit trail)
    """

    SCHEMA_VERSION = "3.0.0"

    def __init__(self, db_path: str = DB_NAME):
        self.db_path = db_path
        self.conn: Optional[sqlite3.Connection] = None
        self._init_db()

    def _init_db(self) -> None:
        """راه‌اندازی اتصال با تنظیمات بهینه SQLite."""
        self.conn = sqlite3.connect(
            self.db_path,
            check_same_thread=False,
            detect_types=sqlite3.PARSE_DECLTYPES
        )
        # Performance & safety pragmas
        self.conn.execute("PRAGMA journal_mode=WAL")
        self.conn.execute("PRAGMA foreign_keys=ON")
        self.conn.execute("PRAGMA synchronous=NORMAL")
        self.conn.execute("PRAGMA cache_size=-64000")  # 64MB cache
        self.conn.execute("PRAGMA temp_store=MEMORY")
        self.conn.row_factory = sqlite3.Row  # Named column access
        self._create_tables()
        self._migrate_if_needed()

    def _create_tables(self) -> None:
        """ایجاد کلیه جداول با روابط FK و ایندکس‌های بهینه."""
        c = self.conn.cursor()

        # ──────────────────────────────────────────
        # 1. جدول متادیتای سیستم
        # ──────────────────────────────────────────
        c.execute("""
        CREATE TABLE IF NOT EXISTS system_meta (
            key TEXT PRIMARY KEY,
            value TEXT DEFAULT '',
            updated_at TEXT DEFAULT (datetime('now','localtime'))
        )
        """)

        # ──────────────────────────────────────────
        # 2. پروژه‌ها - با متادیتای کامل دفتر فنی
        # ──────────────────────────────────────────
        c.execute("""
        CREATE TABLE IF NOT EXISTS projects (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            name TEXT NOT NULL,
            description TEXT DEFAULT '',
            price_list_year TEXT DEFAULT '1404',
            client_name TEXT DEFAULT '',
            contractor_name TEXT DEFAULT '',
            consultant_name TEXT DEFAULT '',
            project_location TEXT DEFAULT '',
            project_area_m2 REAL DEFAULT 0,
            floors_count INTEGER DEFAULT 0,
            contract_amount REAL DEFAULT 0,
            contract_date TEXT DEFAULT '',
            contract_number TEXT DEFAULT '',
            start_date TEXT DEFAULT '',
            end_date TEXT DEFAULT '',
            project_type TEXT DEFAULT 'مسکونی',
            structure_type TEXT DEFAULT 'بتنی',
            created_at TEXT DEFAULT (datetime('now','localtime')),
            updated_at TEXT DEFAULT (datetime('now','localtime')),
            settings TEXT DEFAULT '{}',
            status TEXT DEFAULT 'active'
        )
        """)
        c.execute("CREATE INDEX IF NOT EXISTS idx_proj_status ON projects(status)")

        # ──────────────────────────────────────────
        # 3. فهرست بها - با پشتیبانی از ستاره‌دار
        # ──────────────────────────────────────────
        c.execute("""
        CREATE TABLE IF NOT EXISTS price_list_items (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            project_id INTEGER NOT NULL,
            item_code TEXT NOT NULL,
            description TEXT DEFAULT '',
            unit TEXT DEFAULT '',
            unit_price REAL DEFAULT 0,
            chapter TEXT DEFAULT '',
            chapter_title TEXT DEFAULT '',
            is_starred INTEGER DEFAULT 0,
            base_year TEXT DEFAULT '',
            notes TEXT DEFAULT '',
            FOREIGN KEY (project_id) REFERENCES projects(id) ON DELETE CASCADE
        )
        """)
        c.execute("CREATE INDEX IF NOT EXISTS idx_price_code ON price_list_items(project_id, item_code)")
        c.execute("CREATE INDEX IF NOT EXISTS idx_price_chapter ON price_list_items(project_id, chapter)")
        c.execute("CREATE INDEX IF NOT EXISTS idx_price_starred ON price_list_items(project_id, is_starred)")

        # ──────────────────────────────────────────
        # 4. آنالیز بها برای ردیف‌های ستاره‌دار
        # ──────────────────────────────────────────
        c.execute("""
        CREATE TABLE IF NOT EXISTS price_analysis (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            project_id INTEGER NOT NULL,
            starred_code TEXT NOT NULL,
            component_type TEXT DEFAULT 'مصالح',
            component_desc TEXT DEFAULT '',
            component_unit TEXT DEFAULT '',
            component_qty REAL DEFAULT 0,
            component_unit_price REAL DEFAULT 0,
            component_total REAL DEFAULT 0,
            notes TEXT DEFAULT '',
            created_at TEXT DEFAULT (datetime('now','localtime')),
            FOREIGN KEY (project_id) REFERENCES projects(id) ON DELETE CASCADE
        )
        """)
        c.execute("CREATE INDEX IF NOT EXISTS idx_analysis_code ON price_analysis(project_id, starred_code)")

        # ──────────────────────────────────────────
        # 5. فایل‌های Revit
        # ──────────────────────────────────────────
        c.execute("""
        CREATE TABLE IF NOT EXISTS revit_files (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            project_id INTEGER NOT NULL,
            filename TEXT NOT NULL,
            file_type TEXT DEFAULT '',
            detected_category TEXT DEFAULT '',
            upload_time TEXT DEFAULT (datetime('now','localtime')),
            row_count INTEGER DEFAULT 0,
            columns_json TEXT DEFAULT '[]',
            file_hash TEXT DEFAULT '',
            notes TEXT DEFAULT '',
            FOREIGN KEY (project_id) REFERENCES projects(id) ON DELETE CASCADE
        )
        """)
        c.execute("CREATE INDEX IF NOT EXISTS idx_revit_files_proj ON revit_files(project_id)")

        # ──────────────────────────────────────────
        # 6. داده‌های استخراج‌شده Revit
        # ──────────────────────────────────────────
        c.execute("""
        CREATE TABLE IF NOT EXISTS revit_data (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            file_id INTEGER NOT NULL,
            project_id INTEGER NOT NULL,
            row_index INTEGER DEFAULT 0,
            raw_data TEXT DEFAULT '{}',
            raw_name TEXT DEFAULT '',
            normalized_name TEXT DEFAULT '',
            source_table TEXT DEFAULT '',
            detected_category TEXT DEFAULT '',
            detected_group TEXT DEFAULT '',
            sub_group TEXT DEFAULT '',
            element_type TEXT DEFAULT '',
            element_position TEXT DEFAULT '',
            floor_level TEXT DEFAULT '',
            volume REAL DEFAULT 0,
            area REAL DEFAULT 0,
            length REAL DEFAULT 0,
            width REAL DEFAULT 0,
            height REAL DEFAULT 0,
            depth REAL DEFAULT 0,
            count REAL DEFAULT 0,
            weight REAL DEFAULT 0,
            diameter REAL DEFAULT 0,
            bar_length REAL DEFAULT 0,
            number_of_bars REAL DEFAULT 0,
            thickness REAL DEFAULT 0,
            rebar_total_weight REAL DEFAULT 0,
            FOREIGN KEY (file_id) REFERENCES revit_files(id) ON DELETE CASCADE,
            FOREIGN KEY (project_id) REFERENCES projects(id) ON DELETE CASCADE
        )
        """)
        c.execute("CREATE INDEX IF NOT EXISTS idx_revit_data_proj ON revit_data(project_id)")
        c.execute("CREATE INDEX IF NOT EXISTS idx_revit_data_file ON revit_data(file_id)")
        c.execute("CREATE INDEX IF NOT EXISTS idx_revit_data_cat ON revit_data(project_id, detected_category)")
        c.execute("CREATE INDEX IF NOT EXISTS idx_revit_data_group ON revit_data(project_id, detected_group)")

        # ──────────────────────────────────────────
        # 7. قوانین Mapping با اولویت
        # ──────────────────────────────────────────
        c.execute("""
        CREATE TABLE IF NOT EXISTS mapping_rules (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            project_id INTEGER,
            revit_key TEXT NOT NULL,
            match_type TEXT DEFAULT 'exact',
            usage TEXT DEFAULT '',
            category TEXT DEFAULT '',
            chapter TEXT DEFAULT '',
            item_code TEXT DEFAULT '',
            size TEXT DEFAULT '',
            rebar_dia TEXT DEFAULT '',
            notes TEXT DEFAULT '',
            priority INTEGER DEFAULT 0,
            active INTEGER DEFAULT 1,
            created_at TEXT DEFAULT (datetime('now','localtime')),
            FOREIGN KEY (project_id) REFERENCES projects(id) ON DELETE CASCADE
        )
        """)
        c.execute("CREATE INDEX IF NOT EXISTS idx_map_proj ON mapping_rules(project_id, active, priority)")

        # ──────────────────────────────────────────
        # 8. نتایج پردازش (تاریخچه‌دار برای مقایسه)
        # ──────────────────────────────────────────
        c.execute("""
        CREATE TABLE IF NOT EXISTS results (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            project_id INTEGER NOT NULL,
            result_json TEXT NOT NULL,
            result_name TEXT DEFAULT '',
            statement_number INTEGER DEFAULT 0,
            total_price REAL DEFAULT 0,
            final_price REAL DEFAULT 0,
            match_rate REAL DEFAULT 0,
            created_at TEXT DEFAULT (datetime('now','localtime')),
            notes TEXT DEFAULT '',
            FOREIGN KEY (project_id) REFERENCES projects(id) ON DELETE CASCADE
        )
        """)
        c.execute("CREATE INDEX IF NOT EXISTS idx_results_proj ON results(project_id, created_at)")

        # ──────────────────────────────────────────
        # 9. تنظیمات درصد پرت
        # ──────────────────────────────────────────
        c.execute("""
        CREATE TABLE IF NOT EXISTS waste_settings (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            project_id INTEGER NOT NULL,
            category TEXT NOT NULL,
            waste_percent REAL DEFAULT 3.0,
            UNIQUE(project_id, category),
            FOREIGN KEY (project_id) REFERENCES projects(id) ON DELETE CASCADE
        )
        """)

        # ──────────────────────────────────────────
        # 10. ضرایب پیمان
        # ──────────────────────────────────────────
        c.execute("""
        CREATE TABLE IF NOT EXISTS coefficients (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            project_id INTEGER NOT NULL,
            coeff_name TEXT NOT NULL,
            coeff_value REAL DEFAULT 1.0,
            description TEXT DEFAULT '',
            coeff_order INTEGER DEFAULT 0,
            UNIQUE(project_id, coeff_name),
            FOREIGN KEY (project_id) REFERENCES projects(id) ON DELETE CASCADE
        )
        """)

        # ──────────────────────────────────────────
        # 11. شاخص‌های تعدیل (نشریه ۱۰۰ بانک مرکزی)
        # ──────────────────────────────────────────
        c.execute("""
        CREATE TABLE IF NOT EXISTS inflation_indices (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            project_id INTEGER,
            year TEXT NOT NULL,
            quarter INTEGER DEFAULT 1,
            chapter TEXT DEFAULT '',
            index_value REAL DEFAULT 1.0,
            source TEXT DEFAULT 'بانک مرکزی',
            notes TEXT DEFAULT '',
            FOREIGN KEY (project_id) REFERENCES projects(id) ON DELETE CASCADE
        )
        """)
        c.execute("CREATE INDEX IF NOT EXISTS idx_infl_year ON inflation_indices(year, quarter)")

        # ──────────────────────────────────────────
        # 12. بنچمارک پروژه‌های مشابه (برای Data Science)
        # ──────────────────────────────────────────
        c.execute("""
        CREATE TABLE IF NOT EXISTS benchmarks (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            project_type TEXT DEFAULT 'مسکونی',
            structure_type TEXT DEFAULT 'بتنی',
            floors_count INTEGER DEFAULT 0,
            area_m2 REAL DEFAULT 0,
            concrete_per_m2 REAL DEFAULT 0,
            rebar_per_m2 REAL DEFAULT 0,
            formwork_per_m2 REAL DEFAULT 0,
            cost_per_m2 REAL DEFAULT 0,
            year TEXT DEFAULT '',
            location TEXT DEFAULT '',
            notes TEXT DEFAULT '',
            created_at TEXT DEFAULT (datetime('now','localtime'))
        )
        """)

        # ──────────────────────────────────────────
        # 13. لاگ عملیات (audit trail)
        # ──────────────────────────────────────────
        c.execute("""
        CREATE TABLE IF NOT EXISTS activity_log (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            project_id INTEGER,
            action TEXT NOT NULL,
            details TEXT DEFAULT '',
            created_at TEXT DEFAULT (datetime('now','localtime'))
        )
        """)
        c.execute("CREATE INDEX IF NOT EXISTS idx_log_proj ON activity_log(project_id, created_at)")

        # ──────────────────────────────────────────
        # 14. زمان‌بندی اجرا (Timeline)
        # ──────────────────────────────────────────
        c.execute("""
        CREATE TABLE IF NOT EXISTS project_timeline (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            project_id INTEGER NOT NULL,
            phase_name TEXT NOT NULL,
            structural_group TEXT DEFAULT '',
            start_date TEXT DEFAULT '',
            end_date TEXT DEFAULT '',
            duration_days INTEGER DEFAULT 0,
            progress_percent REAL DEFAULT 0,
            estimated_cost REAL DEFAULT 0,
            actual_cost REAL DEFAULT 0,
            notes TEXT DEFAULT '',
            FOREIGN KEY (project_id) REFERENCES projects(id) ON DELETE CASCADE
        )
        """)

        # Store schema version
        c.execute("INSERT OR REPLACE INTO system_meta (key, value) VALUES (?, ?)",
                  ("schema_version", self.SCHEMA_VERSION))
        
        self.conn.commit()

    def _migrate_if_needed(self) -> None:
        """در صورت تغییر schema، migration اتوماتیک انجام می‌شود."""
        try:
            c = self.conn.cursor()
            c.execute("SELECT value FROM system_meta WHERE key='schema_version'")
            row = c.fetchone()
            current = row[0] if row else "1.0.0"
            if current != self.SCHEMA_VERSION:
                logger.info(f"Schema migration: {current} → {self.SCHEMA_VERSION}")
                # Future migration logic here
        except Exception as e:
            logger.warning(f"Migration check failed: {e}")

    def log_action(self, project_id: Optional[int], action: str, details: str = "") -> None:
        """ثبت هر عملیات مهم در لاگ سیستم."""
        try:
            self.conn.execute(
                "INSERT INTO activity_log (project_id, action, details) VALUES (?, ?, ?)",
                (project_id, action, details)
            )
            self.conn.commit()
        except Exception as e:
            logger.warning(f"Log error: {e}")

    # ═══════════════════════════════════════════════════════════
    # مدیریت پروژه‌ها
    # ═══════════════════════════════════════════════════════════
    def create_project(self, name: str, description: str = "",
                       price_list_year: str = "1404", **kwargs) -> int:
        """ایجاد پروژه با پارامترهای اختیاری کامل دفتر فنی."""
        c = self.conn.cursor()
        c.execute("""
            INSERT INTO projects (
                name, description, price_list_year,
                client_name, contractor_name, consultant_name,
                project_location, project_area_m2, floors_count,
                contract_amount, contract_date, contract_number,
                start_date, end_date, project_type, structure_type
            ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        """, (
            name, description, price_list_year,
            kwargs.get("client_name", ""),
            kwargs.get("contractor_name", ""),
            kwargs.get("consultant_name", ""),
            kwargs.get("project_location", ""),
            float(kwargs.get("project_area_m2", 0) or 0),
            int(kwargs.get("floors_count", 0) or 0),
            float(kwargs.get("contract_amount", 0) or 0),
            kwargs.get("contract_date", ""),
            kwargs.get("contract_number", ""),
            kwargs.get("start_date", ""),
            kwargs.get("end_date", ""),
            kwargs.get("project_type", "مسکونی"),
            kwargs.get("structure_type", "بتنی"),
        ))
        self.conn.commit()
        pid = c.lastrowid

        # درج تنظیمات پیش‌فرض پرت
        for cat, wp in DEFAULT_WASTE_PERCENTS.items():
            c.execute(
                "INSERT OR IGNORE INTO waste_settings (project_id, category, waste_percent) VALUES (?, ?, ?)",
                (pid, cat, wp)
            )

        # درج ضرایب پیش‌فرض پیمان (مطابق نشریه ۱۰۰)
        default_coeffs = [
            ("balasari", 1.30, "ضریب بالاسری (پیمان‌کاری - ۳۰٪)", 1),
            ("regional", 1.00, "ضریب منطقه‌ای", 2),
            ("tajhiz_kargah", 1.00, "ضریب تجهیز و برچیدن کارگاه", 3),
            ("tabaghat", 1.00, "ضریب طبقات", 4),
            ("ertefaa", 1.00, "ضریب ارتفاع", 5),
            ("sakht_ozvi", 1.00, "ضریب سختی کار (اعضای ویژه)", 6),
            ("taadil", 1.00, "ضریب تعدیل (نشریه ۱۰۰)", 7),
        ]
        for name_, val, desc, order in default_coeffs:
            c.execute(
                "INSERT OR IGNORE INTO coefficients (project_id, coeff_name, coeff_value, description, coeff_order) "
                "VALUES (?, ?, ?, ?, ?)",
                (pid, name_, val, desc, order)
            )
        self.conn.commit()
        self.log_action(pid, "CREATE_PROJECT", f"پروژه '{name}' ایجاد شد")
        return pid

    def update_project(self, project_id: int, **kwargs) -> None:
        """به‌روزرسانی متادیتای پروژه."""
        if not kwargs:
            return
        fields = []
        values = []
        allowed = {"name", "description", "price_list_year", "client_name",
                   "contractor_name", "consultant_name", "project_location",
                   "project_area_m2", "floors_count", "contract_amount",
                   "contract_date", "contract_number", "start_date", "end_date",
                   "project_type", "structure_type", "status"}
        for k, v in kwargs.items():
            if k in allowed:
                fields.append(f"{k}=?")
                values.append(v)
        if not fields:
            return
        fields.append("updated_at=datetime('now','localtime')")
        values.append(project_id)
        query = f"UPDATE projects SET {', '.join(fields)} WHERE id=?"
        self.conn.execute(query, values)
        self.conn.commit()
        self.log_action(project_id, "UPDATE_PROJECT", ", ".join(kwargs.keys()))

    def list_projects(self) -> List[Dict]:
        c = self.conn.cursor()
        c.execute("""
            SELECT id, name, description, price_list_year, client_name,
                   contractor_name, project_location, project_area_m2,
                   floors_count, contract_amount, project_type, structure_type,
                   status, created_at
            FROM projects
            WHERE status != 'archived'
            ORDER BY id DESC
        """)
        rows = c.fetchall()
        return [dict(r) for r in rows]

    def get_project(self, project_id: int) -> Optional[Dict]:
        """دریافت اطلاعات کامل یک پروژه."""
        c = self.conn.cursor()
        c.execute("SELECT * FROM projects WHERE id=?", (project_id,))
        row = c.fetchone()
        return dict(row) if row else None

    def delete_project(self, project_id: int) -> None:
        proj = self.get_project(project_id)
        name = proj.get("name", "") if proj else ""
        self.conn.execute("DELETE FROM projects WHERE id=?", (project_id,))
        self.conn.commit()
        self.log_action(None, "DELETE_PROJECT", f"پروژه '{name}' حذف شد")

    def archive_project(self, project_id: int) -> None:
        """آرشیو کردن پروژه بجای حذف کامل."""
        self.conn.execute("UPDATE projects SET status='archived' WHERE id=?", (project_id,))
        self.conn.commit()
        self.log_action(project_id, "ARCHIVE_PROJECT", "")

    # ═══════════════════════════════════════════════════════════
    # مدیریت فهرست بها
    # ═══════════════════════════════════════════════════════════
    def save_price_list(self, project_id: int, df: pd.DataFrame) -> int:
        c = self.conn.cursor()
        c.execute("DELETE FROM price_list_items WHERE project_id=?", (project_id,))
        count = 0
        for _, row in df.iterrows():
            c.execute("""
                INSERT INTO price_list_items 
                (project_id, item_code, description, unit, unit_price, 
                 chapter, chapter_title, is_starred, base_year)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
            """, (
                project_id,
                str(row.get("item_code", "")).strip(),
                str(row.get("description", "")),
                str(row.get("unit", "")),
                float(row.get("unit_price", 0) or 0),
                str(row.get("chapter", "")),
                str(row.get("chapter_title", "")),
                int(bool(row.get("is_starred", False))),
                str(row.get("base_year", "")),
            ))
            count += 1
        self.conn.commit()
        self.log_action(project_id, "IMPORT_PRICE_LIST", f"{count} ردیف")
        return count

    def get_price_list(self, project_id: int) -> pd.DataFrame:
        df = pd.read_sql_query(
            """SELECT item_code, description, unit, unit_price, chapter, 
                      chapter_title, is_starred, base_year, notes
               FROM price_list_items WHERE project_id=?""",
            self.conn, params=(project_id,)
        )
        if df.empty:
            return make_empty_df(PRICE_LIST_SCHEMA)
        df["is_starred"] = df["is_starred"].astype(bool)
        return df

    def get_starred_items(self, project_id: int) -> pd.DataFrame:
        """دریافت فقط ردیف‌های ستاره‌دار (نیازمند آنالیز بها)."""
        df = pd.read_sql_query(
            """SELECT item_code, description, unit, unit_price, chapter
               FROM price_list_items 
               WHERE project_id=? AND is_starred=1""",
            self.conn, params=(project_id,)
        )
        return df

    def get_price_for_code(self, project_id: int, item_code: str) -> Optional[Dict]:
        c = self.conn.cursor()
        c.execute("""SELECT item_code, description, unit, unit_price, chapter, is_starred
                     FROM price_list_items WHERE project_id=? AND item_code=?""",
                  (project_id, item_code))
        row = c.fetchone()
        return dict(row) if row else None

    # ═══════════════════════════════════════════════════════════
    # آنالیز بها برای ردیف‌های ستاره‌دار
    # ═══════════════════════════════════════════════════════════
    def save_price_analysis(self, project_id: int, starred_code: str,
                            components: List[Dict]) -> int:
        """ذخیره اجزای تشکیل‌دهنده آنالیز بها."""
        c = self.conn.cursor()
        c.execute("DELETE FROM price_analysis WHERE project_id=? AND starred_code=?",
                  (project_id, starred_code))
        count = 0
        for comp in components:
            qty = float(comp.get("component_qty", 0) or 0)
            price = float(comp.get("component_unit_price", 0) or 0)
            c.execute("""
                INSERT INTO price_analysis
                (project_id, starred_code, component_type, component_desc,
                 component_unit, component_qty, component_unit_price,
                 component_total, notes)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
            """, (
                project_id, starred_code,
                comp.get("component_type", "مصالح"),
                comp.get("component_desc", ""),
                comp.get("component_unit", ""),
                qty, price, qty * price,
                comp.get("notes", ""),
            ))
            count += 1
        self.conn.commit()
        return count

    def get_price_analysis(self, project_id: int, starred_code: str) -> pd.DataFrame:
        df = pd.read_sql_query(
            """SELECT component_type, component_desc, component_unit,
                      component_qty, component_unit_price, component_total, notes
               FROM price_analysis
               WHERE project_id=? AND starred_code=?""",
            self.conn, params=(project_id, starred_code)
        )
        return df

    # ═══════════════════════════════════════════════════════════
    # مدیریت فایل‌های Revit
    # ═══════════════════════════════════════════════════════════
    def save_revit_file(self, project_id: int, filename: str,
                        file_type: str, detected_category: str,
                        row_count: int, columns: List[str],
                        file_hash: str = "") -> int:
        c = self.conn.cursor()
        c.execute("""
            INSERT INTO revit_files
            (project_id, filename, file_type, detected_category, 
             row_count, columns_json, file_hash)
            VALUES (?, ?, ?, ?, ?, ?, ?)
        """, (project_id, filename, file_type, detected_category,
              row_count, json.dumps(columns, ensure_ascii=False), file_hash))
        self.conn.commit()
        fid = c.lastrowid
        self.log_action(project_id, "UPLOAD_REVIT", f"{filename} ({row_count} ردیف)")
        return fid

    def save_revit_data(self, project_id: int, file_id: int, records: List[Dict]) -> int:
        c = self.conn.cursor()
        count = 0
        for rec in records:
            c.execute("""
                INSERT INTO revit_data
                (file_id, project_id, row_index, raw_data, raw_name, 
                 normalized_name, source_table, detected_category, detected_group,
                 sub_group, element_type, element_position, floor_level,
                 volume, area, length, width, height, depth, count, weight,
                 diameter, bar_length, number_of_bars, thickness, rebar_total_weight)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """, (
                file_id, project_id,
                rec.get("row_index", 0),
                json.dumps(rec.get("raw_data", {}), ensure_ascii=False, default=str),
                rec.get("raw_name", ""),
                rec.get("normalized_name", ""),
                rec.get("source_table", ""),
                rec.get("detected_category", ""),
                rec.get("detected_group", ""),
                rec.get("sub_group", ""),
                rec.get("element_type", ""),
                rec.get("element_position", ""),
                rec.get("floor_level", ""),
                rec.get("volume", 0), rec.get("area", 0),
                rec.get("length", 0), rec.get("width", 0),
                rec.get("height", 0), rec.get("depth", 0),
                rec.get("count", 0), rec.get("weight", 0),
                rec.get("diameter", 0), rec.get("bar_length", 0),
                rec.get("number_of_bars", 0), rec.get("thickness", 0),
                rec.get("rebar_total_weight", 0),
            ))
            count += 1
        self.conn.commit()
        return count

    def get_revit_data(self, project_id: int) -> pd.DataFrame:
        df = pd.read_sql_query(
            """SELECT rd.*, rf.filename as source_file 
               FROM revit_data rd
               JOIN revit_files rf ON rd.file_id = rf.id
               WHERE rd.project_id=?""",
            self.conn, params=(project_id,)
        )
        return df

    def get_revit_files(self, project_id: int) -> List[Dict]:
        c = self.conn.cursor()
        c.execute("""
            SELECT id, filename, file_type, detected_category, 
                   upload_time, row_count
            FROM revit_files WHERE project_id=?
            ORDER BY id DESC
        """, (project_id,))
        return [dict(r) for r in c.fetchall()]

    def delete_revit_file(self, file_id: int) -> None:
        c = self.conn.cursor()
        c.execute("SELECT filename, project_id FROM revit_files WHERE id=?", (file_id,))
        row = c.fetchone()
        c.execute("DELETE FROM revit_data WHERE file_id=?", (file_id,))
        c.execute("DELETE FROM revit_files WHERE id=?", (file_id,))
        self.conn.commit()
        if row:
            self.log_action(row["project_id"], "DELETE_REVIT", row["filename"])

    def clear_all_revit_files(self, project_id: int) -> None:
        c = self.conn.cursor()
        c.execute("DELETE FROM revit_data WHERE project_id=?", (project_id,))
        c.execute("DELETE FROM revit_files WHERE project_id=?", (project_id,))
        self.conn.commit()
        self.log_action(project_id, "CLEAR_REVIT", "همه فایل‌های Revit پاک شدند")

    # ═══════════════════════════════════════════════════════════
    # مدیریت قوانین Mapping
    # ═══════════════════════════════════════════════════════════
    def save_mapping_rules(self, project_id: int, df: pd.DataFrame) -> int:
        c = self.conn.cursor()
        c.execute("DELETE FROM mapping_rules WHERE project_id=?", (project_id,))
        count = 0
        for _, row in df.iterrows():
            c.execute("""
                INSERT INTO mapping_rules
                (project_id, revit_key, match_type, usage, category, chapter,
                 item_code, size, rebar_dia, notes, priority, active)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """, (
                project_id,
                str(row.get("revit_key", "")),
                str(row.get("match_type", "exact")),
                str(row.get("usage", "")),
                str(row.get("category", "")),
                str(row.get("chapter", "")),
                str(row.get("item_code", "")),
                str(row.get("size", "")),
                str(row.get("rebar_dia", "")),
                str(row.get("notes", "")),
                int(row.get("priority", 0) or 0),
                int(row.get("active", 1) or 0),
            ))
            count += 1
        self.conn.commit()
        self.log_action(project_id, "IMPORT_MAPPING", f"{count} قانون")
        return count

    def get_mapping_rules(self, project_id: int) -> pd.DataFrame:
        df = pd.read_sql_query(
            """SELECT * FROM mapping_rules 
               WHERE project_id=? AND active=1 
               ORDER BY priority DESC, id ASC""",
            self.conn, params=(project_id,)
        )
        return df

    def add_mapping_rule(self, project_id: int, revit_key: str, item_code: str,
                         match_type: str = "exact", **kwargs) -> int:
        """افزودن یک قانون Mapping (برای موارد ناشناخته)."""
        c = self.conn.cursor()
        c.execute("""
            INSERT INTO mapping_rules
            (project_id, revit_key, match_type, item_code, category, notes, priority, active)
            VALUES (?, ?, ?, ?, ?, ?, ?, 1)
        """, (project_id, revit_key, match_type, item_code,
              kwargs.get("category", ""), kwargs.get("notes", ""),
              int(kwargs.get("priority", 10))))
        self.conn.commit()
        return c.lastrowid

    # ═══════════════════════════════════════════════════════════
    # مدیریت درصد پرت و ضرایب
    # ═══════════════════════════════════════════════════════════
    def get_waste_settings(self, project_id: int) -> Dict[str, float]:
        c = self.conn.cursor()
        c.execute("SELECT category, waste_percent FROM waste_settings WHERE project_id=?",
                  (project_id,))
        result = {r["category"]: r["waste_percent"] for r in c.fetchall()}
        return result if result else DEFAULT_WASTE_PERCENTS.copy()

    def update_waste_setting(self, project_id: int, category: str, waste_percent: float) -> None:
        c = self.conn.cursor()
        c.execute("""
            INSERT INTO waste_settings (project_id, category, waste_percent)
            VALUES (?, ?, ?)
            ON CONFLICT(project_id, category) DO UPDATE SET waste_percent=excluded.waste_percent
        """, (project_id, category, waste_percent))
        self.conn.commit()

    def get_coefficients(self, project_id: int) -> Dict[str, Dict]:
        c = self.conn.cursor()
        c.execute("""
            SELECT coeff_name, coeff_value, description, coeff_order
            FROM coefficients WHERE project_id=?
            ORDER BY coeff_order ASC
        """, (project_id,))
        return {r["coeff_name"]: {
            "value": r["coeff_value"],
            "description": r["description"],
            "order": r["coeff_order"],
        } for r in c.fetchall()}

    def update_coefficient(self, project_id: int, name: str, value: float) -> None:
        c = self.conn.cursor()
        c.execute("""
            UPDATE coefficients SET coeff_value=? 
            WHERE project_id=? AND coeff_name=?
        """, (value, project_id, name))
        self.conn.commit()

    def get_cumulative_coefficient(self, project_id: int) -> float:
        """ضریب تجمیعی تمام ضرایب پیمان."""
        coeffs = self.get_coefficients(project_id)
        result = 1.0
        for _, data in coeffs.items():
            result *= float(data.get("value", 1.0))
        return result

    # ═══════════════════════════════════════════════════════════
    # نتایج و مقایسه صورت وضعیت
    # ═══════════════════════════════════════════════════════════
    def save_result(self, project_id: int, result_dict: Dict,
                    result_name: str = "") -> int:
        """ذخیره نتیجه پردازش با شماره صورت وضعیت خودکار."""
        c = self.conn.cursor()
        c.execute("SELECT COALESCE(MAX(statement_number), 0) FROM results WHERE project_id=?",
                  (project_id,))
        row = c.fetchone()
        next_num = (row[0] if row else 0) + 1

        summary = result_dict.get("summary", {})
        kpi = result_dict.get("kpi", {})
        total = float(summary.get("total_price", 0) or 0)
        final = float(summary.get("final_price", total))
        match_rate = float(kpi.get("match_rate", 0) or 0)

        if not result_name:
            result_name = f"صورت وضعیت شماره {next_num}"

        c.execute("""
            INSERT INTO results 
            (project_id, result_json, result_name, statement_number,
             total_price, final_price, match_rate)
            VALUES (?, ?, ?, ?, ?, ?, ?)
        """, (project_id, json.dumps(result_dict, ensure_ascii=False, default=str),
              result_name, next_num, total, final, match_rate))
        self.conn.commit()
        return c.lastrowid

    def list_results(self, project_id: int) -> List[Dict]:
        """لیست تمام صورت وضعیت‌های ذخیره‌شده (برای مقایسه پیشرفت)."""
        c = self.conn.cursor()
        c.execute("""
            SELECT id, result_name, statement_number, total_price,
                   final_price, match_rate, created_at, notes
            FROM results WHERE project_id=?
            ORDER BY statement_number DESC
        """, (project_id,))
        return [dict(r) for r in c.fetchall()]

    def get_result(self, result_id: int) -> Optional[Dict]:
        """بازیابی کامل یک نتیجه از تاریخچه."""
        c = self.conn.cursor()
        c.execute("SELECT result_json FROM results WHERE id=?", (result_id,))
        row = c.fetchone()
        if row:
            try:
                return json.loads(row["result_json"])
            except Exception as e:
                logger.error(f"JSON parse error: {e}")
        return None

    def compare_results(self, result_id_1: int, result_id_2: int) -> Dict:
        """مقایسه دو صورت وضعیت (پیشرفت پروژه)."""
        r1 = self.get_result(result_id_1)
        r2 = self.get_result(result_id_2)
        if not r1 or not r2:
            return {"error": "یکی از نتایج یافت نشد"}

        s1 = r1.get("summary", {})
        s2 = r2.get("summary", {})
        return {
            "total_price_1": s1.get("total_price", 0),
            "total_price_2": s2.get("total_price", 0),
            "diff_amount": s2.get("total_price", 0) - s1.get("total_price", 0),
            "diff_percent": (
                (s2.get("total_price", 0) - s1.get("total_price", 0))
                / max(s1.get("total_price", 1), 1) * 100
            ),
            "items_1": s1.get("total_items", 0),
            "items_2": s2.get("total_items", 0),
        }

    # ═══════════════════════════════════════════════════════════
    # شاخص‌های تعدیل (نشریه ۱۰۰)
    # ═══════════════════════════════════════════════════════════
    def save_inflation_index(self, year: str, quarter: int, chapter: str,
                             index_value: float, project_id: Optional[int] = None) -> int:
        c = self.conn.cursor()
        c.execute("""
            INSERT INTO inflation_indices
            (project_id, year, quarter, chapter, index_value)
            VALUES (?, ?, ?, ?, ?)
        """, (project_id, year, quarter, chapter, index_value))
        self.conn.commit()
        return c.lastrowid

    def get_inflation_indices(self, project_id: Optional[int] = None) -> pd.DataFrame:
        if project_id:
            df = pd.read_sql_query(
                "SELECT * FROM inflation_indices WHERE project_id=? OR project_id IS NULL "
                "ORDER BY year DESC, quarter DESC",
                self.conn, params=(project_id,)
            )
        else:
            df = pd.read_sql_query(
                "SELECT * FROM inflation_indices ORDER BY year DESC, quarter DESC",
                self.conn
            )
        return df

    # ═══════════════════════════════════════════════════════════
    # بنچمارک پروژه‌های مشابه
    # ═══════════════════════════════════════════════════════════
    def add_benchmark(self, **kwargs) -> int:
        c = self.conn.cursor()
        c.execute("""
            INSERT INTO benchmarks
            (project_type, structure_type, floors_count, area_m2,
             concrete_per_m2, rebar_per_m2, formwork_per_m2, cost_per_m2,
             year, location, notes)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        """, (
            kwargs.get("project_type", "مسکونی"),
            kwargs.get("structure_type", "بتنی"),
            int(kwargs.get("floors_count", 0) or 0),
            float(kwargs.get("area_m2", 0) or 0),
            float(kwargs.get("concrete_per_m2", 0) or 0),
            float(kwargs.get("rebar_per_m2", 0) or 0),
            float(kwargs.get("formwork_per_m2", 0) or 0),
            float(kwargs.get("cost_per_m2", 0) or 0),
            kwargs.get("year", ""),
            kwargs.get("location", ""),
            kwargs.get("notes", ""),
        ))
        self.conn.commit()
        return c.lastrowid

    def get_benchmarks(self, project_type: str = "", structure_type: str = "") -> pd.DataFrame:
        query = "SELECT * FROM benchmarks WHERE 1=1"
        params = []
        if project_type:
            query += " AND project_type=?"
            params.append(project_type)
        if structure_type:
            query += " AND structure_type=?"
            params.append(structure_type)
        query += " ORDER BY created_at DESC"
        return pd.read_sql_query(query, self.conn, params=params)

    # ═══════════════════════════════════════════════════════════
    # زمان‌بندی اجرا
    # ═══════════════════════════════════════════════════════════
    def save_timeline(self, project_id: int, phases: List[Dict]) -> int:
        c = self.conn.cursor()
        c.execute("DELETE FROM project_timeline WHERE project_id=?", (project_id,))
        count = 0
        for ph in phases:
            c.execute("""
                INSERT INTO project_timeline
                (project_id, phase_name, structural_group, start_date, end_date,
                 duration_days, progress_percent, estimated_cost, actual_cost, notes)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """, (
                project_id,
                ph.get("phase_name", ""),
                ph.get("structural_group", ""),
                ph.get("start_date", ""),
                ph.get("end_date", ""),
                int(ph.get("duration_days", 0) or 0),
                float(ph.get("progress_percent", 0) or 0),
                float(ph.get("estimated_cost", 0) or 0),
                float(ph.get("actual_cost", 0) or 0),
                ph.get("notes", ""),
            ))
            count += 1
        self.conn.commit()
        return count

    def get_timeline(self, project_id: int) -> pd.DataFrame:
        return pd.read_sql_query(
            "SELECT * FROM project_timeline WHERE project_id=? ORDER BY start_date ASC",
            self.conn, params=(project_id,)
        )

    # ═══════════════════════════════════════════════════════════
    # لاگ‌ها و آمار
    # ═══════════════════════════════════════════════════════════
    def get_activity_log(self, project_id: Optional[int] = None, limit: int = 100) -> List[Dict]:
        c = self.conn.cursor()
        if project_id:
            c.execute("""
                SELECT * FROM activity_log 
                WHERE project_id=? OR project_id IS NULL
                ORDER BY created_at DESC LIMIT ?
            """, (project_id, limit))
        else:
            c.execute("SELECT * FROM activity_log ORDER BY created_at DESC LIMIT ?", (limit,))
        return [dict(r) for r in c.fetchall()]

    def get_db_stats(self) -> Dict:
        """آمار کلی پایگاه داده."""
        c = self.conn.cursor()
        stats = {}
        for table in ["projects", "price_list_items", "revit_files", "revit_data",
                      "mapping_rules", "results", "benchmarks"]:
            try:
                c.execute(f"SELECT COUNT(*) as cnt FROM {table}")
                stats[table] = c.fetchone()["cnt"]
            except Exception:
                stats[table] = 0
        try:
            stats["db_size_mb"] = round(os.path.getsize(self.db_path) / (1024 * 1024), 2)
        except Exception:
            stats["db_size_mb"] = 0
        return stats

    def close(self) -> None:
        if self.conn:
            self.conn.close()

    def __del__(self):
        try:
            self.close()
        except Exception:
            pass

# ──────────────────────────────────────────────
# Price List Importer (Smart Excel 1404 Reader)
# ──────────────────────────────────────────────
class PriceListImporter:
    """Smart importer for Iranian construction price lists (فهرست بها).
    Handles zero-padded codes (070101 vs 70101), merged cells, and multi-sheet files.
    """

    CODE_PATTERNS = [
        r"کد\s*ردیف", r"شماره\s*ردیف", r"شماره", r"کد", r"ردیف",
        r"item[\s_-]*code", r"code", r"row[\s_-]*number",
    ]
    DESC_PATTERNS = [
        r"شرح", r"شرح\s*عملیات", r"شرح\s*ردیف", r"توضیح",
        r"description", r"desc",
    ]
    UNIT_PATTERNS = [r"واحد", r"unit"]
    PRICE_PATTERNS = [
        r"بهای\s*واحد", r"بهاي\s*واحد", r"قیمت\s*واحد", r"قیمت", r"فی",
        r"بها", r"unit[\s_-]*price", r"price", r"amount",
    ]
    CHAPTER_PATTERNS = [r"فصل", r"chapter", r"chap"]

    @classmethod
    def detect_year(cls, filename: str, df: Optional[pd.DataFrame] = None) -> str:
        text = TextNormalizer.fa_to_en_digits(filename)
        m = re.search(r'(1[34]\d{2})', text)
        if m: return m.group(1)
        if df is not None:
            for col in df.columns[:5]:
                for val in df[col].head(10).astype(str):
                    val = TextNormalizer.fa_to_en_digits(val)
                    m = re.search(r'(1[34]\d{2})', val)
                    if m: return m.group(1)
        return ""

    @classmethod
    def _match_column(cls, col_name: str, patterns: List[str]) -> bool:
        norm = TextNormalizer.normalize(col_name)
        for pat in patterns:
            if re.search(pat, norm, re.IGNORECASE): return True
        return False

    @classmethod
    def _find_header_row(cls, df_raw: pd.DataFrame, max_rows: int = 20) -> int:
        for i in range(min(max_rows, len(df_raw))):
            row_values = [TextNormalizer.normalize(str(v)) for v in df_raw.iloc[i]]
            score = 0
            for val in row_values:
                if not val or val == 'nan': continue
                for pats in [cls.CODE_PATTERNS, cls.DESC_PATTERNS,
                             cls.UNIT_PATTERNS, cls.PRICE_PATTERNS]:
                    if any(re.search(p, val, re.IGNORECASE) for p in pats):
                        score += 1
                        break
            if score >= 2: return i
        return 0

    @classmethod
    def _identify_columns(cls, columns: List[str]) -> Dict[str, Optional[int]]:
        result = {"code": None, "desc": None, "unit": None, "price": None, "chapter": None}
        for i, col in enumerate(columns):
            if result["code"] is None and cls._match_column(col, cls.CODE_PATTERNS): result["code"] = i
            elif result["desc"] is None and cls._match_column(col, cls.DESC_PATTERNS): result["desc"] = i
            elif result["unit"] is None and cls._match_column(col, cls.UNIT_PATTERNS): result["unit"] = i
            elif result["price"] is None and cls._match_column(col, cls.PRICE_PATTERNS): result["price"] = i
            elif result["chapter"] is None and cls._match_column(col, cls.CHAPTER_PATTERNS): result["chapter"] = i
        return result

    @classmethod
    def import_excel(cls, file_data: io.BytesIO, filename: str = "") -> Tuple[pd.DataFrame, Dict]:
        info = {
            "filename": filename, "year": "", "sheets_processed": [],
            "total_rows": 0, "valid_rows": 0, "starred_rows": 0,
            "errors": [], "warnings": [],
        }
        try: xls = pd.ExcelFile(file_data, engine="openpyxl")
        except Exception as e:
            info["errors"].append(f"خطا در باز کردن فایل: {e}")
            return make_empty_df(PRICE_LIST_SCHEMA), info

        all_items = []
        year_detected = ""

        for sheet_name in xls.sheet_names:
            try: df_raw = pd.read_excel(xls, sheet_name=sheet_name, header=None, dtype=str)
            except Exception as e:
                info["warnings"].append(f"شیت '{sheet_name}' قابل خواندن نیست: {e}")
                continue
            if df_raw.empty or len(df_raw) < 2: continue
            try: df_raw = df_raw.ffill(axis=0)
            except Exception: pass

            header_row = cls._find_header_row(df_raw)
            headers = [str(v) for v in df_raw.iloc[header_row]]
            col_map = cls._identify_columns(headers)

            if col_map["code"] is None and col_map["desc"] is None:
                info["warnings"].append(f"شیت '{sheet_name}': ستون‌های شناخته‌شده پیدا نشد")
                continue

            info["sheets_processed"].append(sheet_name)
            df_data = df_raw.iloc[header_row + 1:].reset_index(drop=True)

            if not year_detected:
                year_detected = cls.detect_year(filename, df_raw.iloc[:header_row + 1])

            current_chapter = ""
            current_chapter_title = ""

            for idx, row in df_data.iterrows():
                info["total_rows"] += 1
                code_val = str(row.iloc[col_map["code"]]).strip() if col_map["code"] is not None else ""
                desc_val = str(row.iloc[col_map["desc"]]).strip() if col_map["desc"] is not None else ""
                unit_val = str(row.iloc[col_map["unit"]]).strip() if col_map["unit"] is not None else ""
                price_val = str(row.iloc[col_map["price"]]).strip() if col_map["price"] is not None else "0"
                chapter_val = str(row.iloc[col_map["chapter"]]).strip() if col_map["chapter"] is not None else ""

                code_val = TextNormalizer.fa_to_en_digits(code_val)
                price_val = TextNormalizer.fa_to_en_digits(price_val)

                if code_val in ("", "nan", "None") and desc_val in ("", "nan", "None"): continue
                if chapter_val and chapter_val not in ("", "nan", "None"):
                    current_chapter = TextNormalizer.fa_to_en_digits(chapter_val)
                    current_chapter_title = desc_val if desc_val not in ("", "nan", "None") else ""

                if (unit_val in ("", "nan", "None") and price_val in ("", "nan", "None", "0") and desc_val not in ("", "nan", "None")):
                    ch_match = re.match(r'^(\d{1,2})', code_val)
                    if ch_match and len(code_val) <= 3:
                        current_chapter = code_val
                        current_chapter_title = desc_val
                        continue

                if not re.search(r'\d', code_val): continue
                is_starred = '*' in code_val or '٭' in code_val or '*' in desc_val
                code_val = code_val.replace('*', '').replace('٭', '').strip()
                
                # Standardize 6-digit code with leading zero if needed (e.g. 70101 -> 070101)
                code_clean = re.sub(r'^\d{1,2}\s*-\s*', '', code_val).replace('.', '').strip()
                if len(code_clean) == 5 and code_clean.isdigit():
                    code_clean = "0" + code_clean

                price_float = TextNormalizer.safe_float(price_val)

                item = {
                    "item_code": code_clean,
                    "description": desc_val if desc_val not in ("nan", "None") else "",
                    "unit": unit_val if unit_val not in ("nan", "None") else "",
                    "unit_price": price_float,
                    "chapter": current_chapter or (code_clean[:2] if len(code_clean) >= 2 else ""),
                    "chapter_title": current_chapter_title,
                    "is_starred": is_starred,
                }
                all_items.append(item)
                info["valid_rows"] += 1
                if is_starred: info["starred_rows"] += 1

        info["year"] = year_detected
        if not all_items:
            info["errors"].append("هیچ ردیف معتبری در فایل یافت نشد")
            return make_empty_df(PRICE_LIST_SCHEMA), info

        df = pd.DataFrame(all_items)
        for col, dtype in PRICE_LIST_SCHEMA.items():
            if col not in df.columns: df[col] = None
            try: df[col] = df[col].astype(_pandas_dtype(dtype))
            except Exception: pass
        return df, info


# ──────────────────────────────────────────────
# Revit Multi-Table TXT/CSV Importer (حرفه‌ای)
# ──────────────────────────────────────────────

# ══════════════════════════════════════════════════════════════════
# موتورهای اصلاح‌شده استخراج، وزن‌گیری و تطبیق با فهرست بها ۱۴۰۴
# ══════════════════════════════════════════════════════════════════

class RevitImporter:
    """استخراج‌کننده هوشمند فایل‌های رویت (CSV گیومه‌دار) و داینامو (TSV)."""

    @classmethod
    def detect_encoding(cls, file_bytes: bytes) -> str:
        if file_bytes[:2] in (b'\xff\xfe', b'\xfe\xff'): return 'utf-16'
        if file_bytes[:3] == b'\xef\xbb\xbf': return 'utf-8-sig'
        for enc in ['utf-8-sig', 'utf-8', 'utf-16', 'cp1256', 'windows-1256']:
            try: file_bytes.decode(enc); return enc
            except: continue
        return 'utf-8'

    @classmethod
    def import_file(cls, file_bytes: bytes, filename: str = "") -> Tuple[pd.DataFrame, List[Dict], Dict]:
        info = {
            "filename": filename, "encoding": "", "delimiter": "",
            "columns": [], "detected_type": "Schedule", "detected_confidence": 1.0,
            "total_rows": 0, "valid_rows": 0, "errors": [], "warnings": [],
            "tables_found": 1, "tables_detail": []
        }

        enc = cls.detect_encoding(file_bytes)
        info["encoding"] = enc
        try: text = file_bytes.decode(enc)
        except Exception as e:
            info["errors"].append(f"خطای خواندن فایل: {e}")
            return pd.DataFrame(), [], info

        lines = [l.strip() for l in text.replace('\r\n', '\n').replace('\r', '\n').split('\n') if l.strip()]
        if not lines:
            info["errors"].append("فایل خالی است")
            return pd.DataFrame(), [], info

        # تشخیص نوع جداکننده (تب داینامو یا کامای گیومه‌دار رویت)
        header_line = lines[0]
        sep = '\t' if '\t' in header_line else ','
        info["delimiter"] = sep

        # پاک‌سازی هدرها از گیومه و کاراکترهای اضافه
        headers = [h.strip().strip('"').strip("'") for h in header_line.split(sep)]
        info["columns"] = headers

        records = []
        is_dynamo = "Category" in headers and "Diameter_mm" in headers

        for idx, line in enumerate(lines[1:], start=1):
            # حذف گیومه‌های ابتدایی و انتهایی سطر
            clean_line = line.strip().strip('"')
            parts = [p.strip().strip('"').strip("'") for p in clean_line.split(sep)]
            if len(parts) < 2: continue

            row_dict = {headers[i]: (parts[i] if i < len(parts) else "") for i in range(len(headers))}

            # رد کردن سطرهای عنوان یا مجموع (Grand Total)
            first_val = str(parts[0]).lower()
            if "grand total" in first_val or "مجموع کل" in first_val or "جدول " in first_val:
                continue

            raw_name = ""
            det_cat = "unknown"
            det_group = "سایر"
            
            dia, length_mm, vol_m3, area_m2, qty, steel_type = 0.0, 0.0, 0.0, 0.0, 1.0, ""

            if is_dynamo:
                # 🔴 پردازش تخصصی ساختار داینامو
                cat = str(row_dict.get("Category", "")).strip()
                family = str(row_dict.get("Family", "")).strip()
                type_name = str(row_dict.get("Type", "")).strip()
                mark = str(row_dict.get("Mark", "")).strip()
                host_cat = str(row_dict.get("HostCategory", "")).strip()
                host_type = str(row_dict.get("HostType", "")).strip()

                raw_name = f"{family} {type_name} {mark}".strip() or cat
                
                dia = TextNormalizer.safe_float(row_dict.get("Diameter_mm", 0))
                length_mm = TextNormalizer.safe_float(row_dict.get("Length_mm", 0))
                vol_m3 = TextNormalizer.safe_float(row_dict.get("Volume_m3", 0))
                area_m2 = TextNormalizer.safe_float(row_dict.get("Area_m2", 0))
                qty = TextNormalizer.safe_float(row_dict.get("Quantity", 1)) or 1.0
                steel_type = str(row_dict.get("SteelType", "")).strip()

                if cat == "Rebar" or "Rebar" in family:
                    det_cat, det_group = "rebar", "آرماتور"
                    if "Foundations" in host_cat or "WF_" in host_type: det_group = "پی"
                    elif "Columns" in host_cat or "C1" in mark: det_group = "ستون"
                    elif "Framing" in host_cat or "LG" in mark or "TR" in mark: det_group = "تیر"
                    elif "Stairs" in host_cat or "STR" in mark: det_group = "پله"
                    elif "Floors" in host_cat or "TM" in mark: det_group = "سقف"

                elif cat == "StructuralColumns": det_cat, det_group = "concrete", "ستون"
                elif cat == "StructuralFraming": 
                    if "Joist" in family or "تیرچه" in family: det_cat, det_group = "block_joist", "سقف تیرچه"
                    else: det_cat, det_group = "concrete", "تیر"
                elif cat == "StructuralFoundation":
                    if "100mm" in type_name or "LC" in mark: det_cat, det_group = "lean_concrete", "پی"
                    else: det_cat, det_group = "concrete", "پی"
                elif cat == "Floors": det_cat, det_group = "concrete", "سقف"
                elif cat == "Stairs": det_cat, det_group = "concrete", "پله"
                elif cat == "Walls": det_cat, det_group = "masonry", "دیوار"

            else:
                # 🔴 پردازش تخصصی فایل‌های کلاسیک رویت (استخراج دقیق اعداد گیومه‌دار)
                name_parts = []
                for k, v in row_dict.items():
                    val_str = str(v).strip().strip('"')
                    if not val_str: continue
                    
                    norm_k = k.lower()
                    # استخراج عدد و واحد
                    num_val, unit_val = TextNormalizer.parse_number_with_unit(val_str)
                    num = num_val if num_val is not None else TextNormalizer.safe_float(val_str)

                    if "volume" in norm_k or "حجم" in norm_k or "m³" in val_str or "m3" in val_str:
                        if num > 0: vol_m3 = num
                    elif "area" in norm_k or "مساحت" in norm_k or "m²" in val_str or "m2" in val_str:
                        if num > 0: area_m2 = num
                    elif "length" in norm_k or "طول" in norm_k:
                        if num > 0: length_mm = num
                    elif "count" in norm_k or "quantity" in norm_k or "تعداد" in norm_k:
                        if num > 0: qty = num
                    elif "diameter" in norm_k or "قطر" in norm_k:
                        if num > 0: dia = num
                    else:
                        if not re.match(r'^[\d.,\s\-+]+$', val_str) and len(val_str) > 1:
                            if val_str not in name_parts: name_parts.append(val_str)

                raw_name = " | ".join(name_parts) if name_parts else filename
                
                # تشخیص دسته المان از روی نام
                raw_lower = (raw_name + " " + filename).lower()
                if "یونولیت" in raw_lower or "eps" in raw_lower: det_cat, det_group = "eps_block", "سقف تیرچه"
                elif "تیرچه" in raw_lower or "joist" in raw_lower: det_cat, det_group = "block_joist", "سقف تیرچه"
                elif "مگر" in raw_lower or "lean" in raw_lower: det_cat, det_group = "lean_concrete", "پی"
                elif "بتن" in raw_lower or "concrete" in raw_lower: det_cat, det_group = "concrete", "پی" if "پی" in raw_lower or "foundation" in raw_lower else "سازه"
                elif "آرماتور" in raw_lower or "rebar" in raw_lower or "میلگرد" in raw_lower: det_cat, det_group = "rebar", "آرماتور"
                elif "قالب" in raw_lower or "formwork" in raw_lower: det_cat, det_group = "formwork", "قالب‌بندی"

            if not raw_name: raw_name = filename

            # 🔴 محاسبه فرمول دقیق وزن آرماتور (کیلوگرم)
            weight_kg = 0.0
            if det_cat == "rebar":
                if dia > 0 and length_mm > 0:
                    l_m = length_mm / 1000.0 if length_mm > 100 else length_mm
                    weight_kg = ((dia ** 2) / 162.0) * l_m * qty
                else:
                    weight_kg = TextNormalizer.safe_float(row_dict.get("Weight", 0)) or TextNormalizer.safe_float(row_dict.get("Material: Volume", 0))

            rec = {
                "row_index": idx, "raw_data": row_dict, "source_file": filename,
                "source_table": "Dynamo" if is_dynamo else "Revit Schedule",
                "raw_name": raw_name, "normalized_name": TextNormalizer.normalize(raw_name),
                "detected_category": det_cat, "detected_group": det_group,
                "sub_group": "", "element_type": "", "element_position": "",
                "floor_level": str(row_dict.get("Level", "")),
                "volume": vol_m3, "area": area_m2, "length": length_mm,
                "count": qty, "weight": weight_kg, "diameter": dia, "steel_type": steel_type,
                "bar_length": length_mm / 1000.0 if length_mm > 100 else length_mm,
                "rebar_total_weight": weight_kg,
            }
            records.append(rec)
            info["valid_rows"] += 1

        info["total_rows"] = len(records)
        df = pd.DataFrame([r["raw_data"] for r in records[:100]]) if records else pd.DataFrame()
        return df, records, info


class MappingEngine:
    """موتور تطبیق ترکیبی هوشمند با فهرست بها ۱۴۰۴."""

    def __init__(self, db, project_id: int):
        self.db = db
        self.project_id = project_id
        self._price_dict = {}
        self._norm_price_list = []
        self._mapping_rules = None

    def load(self) -> None:
        self._mapping_rules = self.db.get_mapping_rules(self.project_id)
        price_df = self.db.get_price_list(self.project_id)
        
        if price_df is not None and not price_df.empty:
            for _, row in price_df.iterrows():
                code = str(row.get("item_code", "")).strip()
                item_dict = row.to_dict()
                self._price_dict[code] = item_dict
                clean = code.lstrip('0')
                self._price_dict[clean] = item_dict
                if len(clean) == 5: self._price_dict["0" + clean] = item_dict

                norm_desc = TextNormalizer.normalize(str(row.get("description", "")))
                chapter = str(row.get("chapter", ""))
                if norm_desc and chapter not in EXCLUDED_CHAPTERS:
                    self._norm_price_list.append({
                        "code": code, "norm_desc": norm_desc, "chapter": chapter,
                        "unit_price": float(row.get("unit_price", 0) or 0)
                    })

    def match(self, raw_name: str, normalized_name: str, category: str, group: str, **kwargs) -> Dict:
        # ۱. چک کردن فایل Mapping دستی کاربر
        if self._mapping_rules is not None and not self._mapping_rules.empty:
            for _, rule in self._mapping_rules.iterrows():
                key = str(rule.get("revit_key", "")).strip()
                if key and (key in raw_name or TextNormalizer.normalize(key) in normalized_name):
                    code = str(rule.get("item_code", "")).strip()
                    if code: return self._enrich(code, "exact_mapping", 1.0, f"تطبیق فایلی: {key}")

        # ۲. تطبیق هوشمند خودکار براساس استانداردهای فهرست بهای ۱۴۰۴
        dia = float(kwargs.get("diameter", 0) or 0)
        steel_type = str(kwargs.get("steel_type", "")).strip().lower()

        # آرماتورها (فصل ۷)
        if category == "rebar" or "آرماتور" in raw_name or "rebar" in raw_name.lower():
            if steel_type == "plain" or "a-i" in raw_name.lower() or dia == 8:
                return self._enrich("070101", "auto_1404", 0.98, "میلگرد ساده A1 (ردیف ۰۷۰۱۰۱)")
            elif 0 < dia <= 10:
                return self._enrich("070202", "auto_1404", 0.98, f"میلگرد آجدار سایز {int(dia)} (ردیف ۰۷۰۲۰۲)")
            elif dia > 10:
                return self._enrich("070204", "auto_1404", 0.98, f"میلگرد آجدار سایز {int(dia)} (ردیف ۰۷۰۲۰۴)")
            return self._enrich("070204", "auto_1404", 0.90, "میلگرد آجدار عمومی (ردیف ۰۷۰۲۰۴)")

        # بتن مگر (فصل ۸)
        if category == "lean_concrete" or "مگر" in raw_name or "lean" in raw_name.lower():
            return self._enrich("080101", "auto_1404", 0.98, "بتن مگر ۱۵۰ کیلو سیمان (ردیف ۰۸۰۱۰۱)")

        # بتن سازه‌ای (فصل ۸)
        if category == "concrete" or "بتن" in raw_name or "concrete" in raw_name.lower():
            if group == "پی" or "foundation" in raw_name.lower() or "wf_" in raw_name.lower():
                return self._enrich("080103", "auto_1404", 0.98, "بتن‌ریزی شالوده و پی (ردیف ۰۸۰۱۰۳)")
            elif group == "ستون" or "column" in raw_name.lower():
                return self._enrich("080104", "auto_1404", 0.98, "بتن‌ریزی ستون (ردیف ۰۸۰۱۰۴)")
            elif group == "تیر" or "beam" in raw_name.lower():
                return self._enrich("080105", "auto_1404", 0.98, "بتن‌ریزی تیر (ردیف ۰۸۰۱۰۵)")
            elif group == "سقف" or "slab" in raw_name.lower() or "deck" in raw_name.lower():
                if "topping" in raw_name.lower() or "رویه" in raw_name:
                    return self._enrich("080111", "auto_1404", 0.98, "بتن رویه سقف (ردیف ۰۸۰۱۱۱)")
                return self._enrich("080105", "auto_1404", 0.98, "بتن‌ریزی دال سقف (ردیف ۰۸۰۱۰۵)")
            elif group == "پله" or "stair" in raw_name.lower():
                return self._enrich("080106", "auto_1404", 0.98, "بتن‌ریزی رمپ و دال پله (ردیف ۰۸۰۱۰۶)")
            return self._enrich("080104", "auto_1404", 0.85, "بتن سازه‌ای عمومی (ردیف ۰۸۰۱۰۴)")

        # سقف تیرچه یونولیت (فصل ۱۰ و ۱۹)
        if category in ("block_joist", "eps_block") or "تیرچه" in raw_name or "یونولیت" in raw_name:
            if "یونولیت" in raw_name or "eps" in raw_name.lower():
                return self._enrich("190101", "auto_1404", 0.95, "بلوک پلی‌استایرن یونولیت (ردیف ۱۹۰۱۰۱)")
            return self._enrich("100301", "auto_1404", 0.98, "سقف تیرچه بلوک (ردیف ۱۰۰۳۰۱)")

        # قالب‌بندی (فصل ۵)
        if category == "formwork" or "قالب" in raw_name:
            if group == "پی": return self._enrich("050101", "auto_1404", 0.90, "قالب‌بندی پی")
            if group == "ستون": return self._enrich("050102", "auto_1404", 0.90, "قالب‌بندی ستون")
            return self._enrich("050103", "auto_1404", 0.90, "قالب‌بندی سقف و تیر")

        return {"item_code": "", "match_details": "بدون تطبیق", "needs_review": True}

    def _enrich(self, code: str, method: str, conf: float, details: str) -> Dict:
        clean = code.lstrip('0')
        info = self._price_dict.get(code) or self._price_dict.get(clean) or {}
        return {
            "item_code": code,
            "item_description": info.get("description", details),
            "unit": info.get("unit", ""),
            "unit_price": float(info.get("unit_price", 0) or 0),
            "is_starred": bool(info.get("is_starred", False)),
            "match_method": method, "match_confidence": conf,
            "match_details": details, "needs_review": False if float(info.get("unit_price", 0) or 0) > 0 else True
        }


class TakeoffEngine:
    """موتور محاسبه دقیق متره بر اساس داده‌های رویت و داینامو."""

    def __init__(self, db, project_id: int):
        self.db = db
        self.project_id = project_id
        self.mapping_engine = MappingEngine(db, project_id)

    def run(self) -> Dict:
        self.mapping_engine.load()
        waste_set = self.db.get_waste_settings(self.project_id)
        coeffs = self.db.get_coefficients(self.project_id)
        revit_df = self.db.get_revit_data(self.project_id)

        matched = []
        rebar_lst = []

        for idx, row in revit_df.iterrows():
            cat = str(row.get("detected_category", ""))
            raw_name = str(row.get("raw_name", ""))
            group = str(row.get("detected_group", ""))
            
            # 🔴 تطبیق هوشمند
            res = self.mapping_engine.match(
                raw_name=raw_name,
                normalized_name=str(row.get("normalized_name", "")),
                category=cat, group=group,
                diameter=row.get("diameter", 0),
                steel_type=row.get("steel_type", ""),
                is_dynamo=(str(row.get("source_table", "")) == "Dynamo")
            )

            # 🔴 تعیین قطعیت مقدار خام (Raw Quantity) بدون صفر شدن!
            raw_qty = 0.0
            if cat == "rebar":
                raw_qty = float(row.get("rebar_total_weight", 0) or row.get("weight", 0))
            elif cat in ("concrete", "lean_concrete"):
                raw_qty = float(row.get("volume", 0))
            elif cat in ("formwork", "block_joist", "eps_block", "masonry"):
                raw_qty = float(row.get("area", 0) or row.get("volume", 0) or row.get("count", 1))
            else:
                raw_qty = float(row.get("volume", 0) or row.get("area", 0) or row.get("rebar_total_weight", 0) or row.get("count", 1))

            # اگر با وجود داده باز هم صفر بود، حداقل ۱ عدد لحاظ کند
            if raw_qty == 0 and res.get("item_code"):
                raw_qty = float(row.get("count", 1)) or 1.0

            w_pct = waste_set.get(cat, waste_set.get("default", 3.0))
            f_qty = raw_qty * (1.0 + w_pct / 100.0)
            u_price = float(res.get("unit_price", 0) or 0)
            t_price = f_qty * u_price

            item = {
                "source_file": str(row.get("source_file", "")), "row_index": idx,
                "raw_name": raw_name, "category": cat, "structural_group": group,
                "floor_level": str(row.get("floor_level", "")),
                "item_code": res.get("item_code", ""),
                "item_description": res.get("item_description", ""),
                "unit": res.get("unit", ""),
                "raw_quantity": round(raw_qty, 3),
                "waste_percent": w_pct,
                "final_quantity": round(f_qty, 3),
                "unit_price": u_price,
                "total_price": round(t_price, 0),
                "match_method": res.get("match_method", ""),
                "match_confidence": res.get("match_confidence", 0),
                "match_details": res.get("match_details", ""),
                "needs_review": res.get("needs_review", False),
                "is_starred": res.get("is_starred", False),
                "issues": "بدون کد" if not res.get("item_code") else ""
            }
            matched.append(item)

            # ساخت لیستوفر آرماتور برای تب اختصاصی
            if (cat == "rebar" or "آرماتور" in group) and raw_qty > 0:
                rebar_lst.append({
                    "location": item["floor_level"] or group,
                    "structural_group": group,
                    "diameter": float(row.get("diameter", 0)),
                    "bar_length": float(row.get("bar_length", 0)),
                    "count": float(row.get("count", 1)),
                    "net_weight": round(raw_qty, 2),
                    "waste_percent": w_pct,
                    "gross_weight": round(f_qty, 2),
                    "item_code": item["item_code"],
                    "unit_price": u_price,
                    "total_price": item["total_price"]
                })

        df_m = pd.DataFrame(matched)
        base_cost = float(df_m["total_price"].sum()) if not df_m.empty else 0.0
        
        cum_c = 1.0
        for _, c in coeffs.items(): cum_c *= float(c.get("value", 1.0))

        # 🔴 ساختار کاملاً ایمن و بدون ارور برای داشبورد نتایج
        summary = {
            "total_items": len(df_m),
            "total_price": base_cost,
            "final_price": base_cost * cum_c,
            "starred_price": float(df_m[df_m["is_starred"] == True]["total_price"].sum()) if not df_m.empty and "is_starred" in df_m.columns else 0.0,
            "by_category": {}, "by_group": {}, "by_chapter": {}
        }

        if not df_m.empty:
            for _, r in df_m.iterrows():
                c_name, g_name, price_val = str(r["category"]), str(r["structural_group"]), float(r["total_price"])
                code_val = str(r["item_code"])
                ch_name = code_val[:2] if len(code_val) >= 2 else "نامشخص"

                if c_name not in summary["by_category"]: summary["by_category"][c_name] = {"count": 0, "total_price": 0.0}
                summary["by_category"][c_name]["count"] += 1
                summary["by_category"][c_name]["total_price"] += price_val

                if g_name not in summary["by_group"]: summary["by_group"][g_name] = {"count": 0, "total_price": 0.0}
                summary["by_group"][g_name]["count"] += 1
                summary["by_group"][g_name]["total_price"] += price_val

                if ch_name not in summary["by_chapter"]: summary["by_chapter"][ch_name] = {"count": 0, "total_price": 0.0}
                summary["by_chapter"][ch_name]["count"] += 1
                summary["by_chapter"][ch_name]["total_price"] += price_val

        total_matched = len([i for i in matched if i["item_code"]])

        return {
            "timestamp": datetime.now().isoformat(), "project_id": self.project_id,
            "items_df": df_m, "rebar_listof": pd.DataFrame(rebar_lst),
            "summary": summary,
            "quality": {
                "total_revit_rows": len(revit_df), "valid_rows": len(matched),
                "unmatched": len(matched) - total_matched, "matched_exact": total_matched,
                "issues": [], "final_items": total_matched, "matched_regex": 0,
                "matched_pattern": total_matched, "matched_fuzzy": 0, "zero_quantity": 0,
                "no_price": 0, "needs_review": 0
            },
            "unmatched_items": [i for i in matched if not i["item_code"]],
            "kpi": {
                "match_rate": round((total_matched / max(len(matched), 1)) * 100, 1),
                "total_matched": total_matched,
                "total_unmatched": len(matched) - total_matched
            }
        }

# ──────────────────────────────────────────────
# Excel Exporter (Multi-Sheet Professional)
# ──────────────────────────────────────────────
class ExcelExporter:
    """Generate professional Excel output files for Iranian Technical Offices."""

    @staticmethod
    def export_full_report(result: Dict, project_name: str = "",
                           coefficients: Dict = None) -> io.BytesIO:
        output = io.BytesIO()
        with pd.ExcelWriter(output, engine='xlsxwriter') as writer:
            workbook = writer.book
            header_fmt = workbook.add_format({'bold': True, 'font_size': 11, 'bg_color': '#4472C4',
                                              'font_color': 'white', 'border': 1, 'text_wrap': True,
                                              'align': 'center', 'valign': 'vcenter'})
            title_fmt = workbook.add_format({'bold': True, 'font_size': 14, 'align': 'center'})

            items_df = result.get("items_df", make_empty_df(MATCHED_ITEM_SCHEMA))

            # Sheet 1: صورت وضعیت
            estimate_cols = {"item_code": "کد ردیف", "item_description": "شرح", "unit": "واحد",
                             "final_quantity": "مقدار", "unit_price": "بهای واحد", "total_price": "مبلغ کل"}
            if not items_df.empty:
                est = items_df[items_df["item_code"] != ""][list(estimate_cols.keys())].copy()
                if not est.empty:
                    agg = est.groupby("item_code", as_index=False).agg({
                        "item_description": "first", "unit": "first",
                        "final_quantity": "sum", "unit_price": "first", "total_price": "sum",
                    })
                    agg.columns = [estimate_cols[c] for c in agg.columns]
                else: agg = pd.DataFrame(columns=list(estimate_cols.values()))
            else: agg = pd.DataFrame(columns=list(estimate_cols.values()))

            agg.to_excel(writer, sheet_name="صورت وضعیت", index=False, startrow=2)
            ws = writer.sheets["صورت وضعیت"]
            ws.merge_range(0, 0, 0, 5, f"صورت وضعیت / برآورد - {project_name}", title_fmt)
            for i, col in enumerate(agg.columns):
                ws.write(2, i, col, header_fmt)
                ws.set_column(i, i, 20 if i == 1 else 15)

            # Sheet 2: ریزمتره
            detail_cols = {"source_file": "فایل منبع", "raw_name": "نام Revit", "category": "دسته",
                           "structural_group": "گروه سازه‌ای", "item_code": "کد ردیف",
                           "item_description": "شرح فهرست بها", "unit": "واحد", "raw_quantity": "مقدار خام",
                           "waste_percent": "درصد پرت", "final_quantity": "مقدار نهایی",
                           "unit_price": "بهای واحد", "total_price": "مبلغ کل",
                           "match_method": "روش تطبیق", "match_confidence": "اطمینان"}
            if not items_df.empty:
                dd = items_df[list(detail_cols.keys())].copy()
                dd.columns = [detail_cols[c] for c in dd.columns]
            else: dd = pd.DataFrame(columns=list(detail_cols.values()))
            dd.to_excel(writer, sheet_name="ریزمتره", index=False, startrow=1)
            ws2 = writer.sheets["ریزمتره"]
            ws2.write(0, 0, "ریزمتره تفصیلی", title_fmt)
            for i, col in enumerate(dd.columns):
                ws2.write(1, i, col, header_fmt)
                ws2.set_column(i, i, 15)

            # Sheet 3: لیستوفر
            rebar_df = result.get("rebar_listof", make_empty_df(REBAR_LISTOF_SCHEMA))
            rebar_cols = {"location": "محل مصرف", "structural_group": "گروه سازه‌ای", "sub_group": "بخش",
                          "diameter": "قطر (mm)", "bar_length": "طول شاخه (m)", "count": "تعداد",
                          "net_weight": "وزن خالص (kg)", "waste_percent": "درصد پرت",
                          "gross_weight": "وزن با پرت (kg)", "item_code": "کد ردیف", "total_price": "مبلغ (ریال)"}
            if not rebar_df.empty:
                rb = rebar_df[[c for c in rebar_cols if c in rebar_df.columns]].copy()
                rb.columns = [rebar_cols[c] for c in rb.columns]
            else: rb = pd.DataFrame(columns=list(rebar_cols.values()))
            rb.to_excel(writer, sheet_name="لیستوفر آرماتور", index=False, startrow=1)
            ws3 = writer.sheets["لیستوفر آرماتور"]
            ws3.write(0, 0, "لیستوفر آرماتور", title_fmt)
            for i, col in enumerate(rb.columns): ws3.write(1, i, col, header_fmt)

            # Sheet 4: موارد ناشناخته
            unmatched = result.get("unmatched_items", [])
            if unmatched:
                um = pd.DataFrame(unmatched)
                um.columns = [{"raw_name": "نام اصلی", "normalized_name": "نام نرمال",
                               "category": "دسته تشخیصی", "source_file": "فایل منبع"}.get(c, c) for c in um.columns]
            else: um = pd.DataFrame(columns=["نام اصلی", "نام نرمال", "دسته تشخیصی", "فایل منبع"])
            um.to_excel(writer, sheet_name="موارد ناشناخته", index=False, startrow=1)
            ws4 = writer.sheets["موارد ناشناخته"]
            ws4.write(0, 0, "موارد ناشناخته (بدون تطبیق)", title_fmt)

            # Sheet 5: گزارش کیفیت
            q = result.get("quality", {})
            kpi = result.get("kpi", {})
            q_data = [
                ("تعداد کل ردیف‌های Revit", q.get("total_revit_rows", 0)),
                ("ردیف‌های معتبر", q.get("valid_rows", 0)),
                ("تطبیق دقیق (Exact)", q.get("matched_exact", 0)),
                ("تطبیق Regex", q.get("matched_regex", 0)),
                ("تطبیق الگو Pattern", q.get("matched_pattern", 0)),
                ("تطبیق Fuzzy", q.get("matched_fuzzy", 0)),
                ("بدون تطبیق", q.get("unmatched", 0)),
                ("مقدار صفر", q.get("zero_quantity", 0)),
                ("بدون قیمت", q.get("no_price", 0)),
                ("نیازمند بررسی", q.get("needs_review", 0)),
                ("ردیف‌های نهایی", q.get("final_items", 0)),
                ("", ""),
                ("نرخ تطبیق (%)", kpi.get("match_rate", 0)),
                ("نرخ خطا (%)", kpi.get("unmatched_rate", 0)),
            ]
            qdf = pd.DataFrame(q_data, columns=["شاخص", "مقدار"])
            qdf.to_excel(writer, sheet_name="گزارش کیفیت", index=False, startrow=1)
            ws5 = writer.sheets["گزارش کیفیت"]
            ws5.write(0, 0, "گزارش کیفیت داده", title_fmt)

        output.seek(0)
        return output


# ──────────────────────────────────────────────
# Mapping File Importer
# ──────────────────────────────────────────────
class MappingImporter:
    EXPECTED_COLUMNS = ["revit_key", "match_type", "usage", "category", "chapter",
                        "item_code", "size", "rebar_dia", "notes", "priority", "active"]

    @classmethod
    def import_excel(cls, file_data: io.BytesIO, filename: str = "") -> Tuple[pd.DataFrame, Dict]:
        info = {"filename": filename, "rows": 0, "errors": [], "warnings": []}
        try: df = pd.read_excel(file_data, engine="openpyxl", dtype=str)
        except Exception as e:
            info["errors"].append(f"خطا: {e}")
            return pd.DataFrame(), info
        if df.empty:
            info["errors"].append("فایل خالی است")
            return df, info

        col_map = {}
        for col in df.columns:
            norm = TextNormalizer.normalize(col).replace(" ", "_")
            for expected in cls.EXPECTED_COLUMNS:
                if norm == expected or col.strip().lower() == expected:
                    col_map[col] = expected
                    break
            if col not in col_map:
                best = FuzzyMatcher.best_match(norm, cls.EXPECTED_COLUMNS, threshold=0.7)
                if best: col_map[col] = best[0]

        df = df.rename(columns=col_map)
        for col in cls.EXPECTED_COLUMNS:
            if col not in df.columns: df[col] = ""

        df["active"] = df["active"].apply(lambda x: 1 if str(x).strip().lower() in ("1", "true", "بله", "yes", "") else 0)
        df["priority"] = df["priority"].apply(lambda x: int(TextNormalizer.safe_float(x)))
        info["rows"] = len(df)
        return df, info


# ══════════════════════════════════════════════
# STREAMLIT UI APPLICATION
# ══════════════════════════════════════════════

def get_db() -> DatabaseManager:
    if "db" not in st.session_state:
        st.session_state.db = DatabaseManager(DB_NAME)
    return st.session_state.db


def init_session_state() -> None:
    defaults = {
        "current_project_id": None, "current_project_name": "",
        "current_page": "dashboard", "last_result": None,
    }
    for k, v in defaults.items():
        if k not in st.session_state: st.session_state[k] = v


def apply_rtl_style() -> None:
    st.markdown("""
    <style>
    @import url('https://fonts.googleapis.com/css2?family=Vazirmatn:wght@300;400;500;700&display=swap');
    * { font-family: 'Vazirmatn', 'Tahoma', 'Arial', sans-serif !important; }
    
    /* تنظیمات ساختار کلی راست‌چین */
    .main .block-container { direction: rtl; text-align: right; max-width: 1400px; padding-top: 2rem;}
    h1, h2, h3, h4, h5, h6, p, span, label { direction: rtl; text-align: right; }
    
    /* 🔴 حل قطعی مشکل بریده شدن متن در جداول (مهم) */
    [data-testid="stDataFrame"] { direction: ltr !important; }
    [data-testid="stDataFrame"] div[class*="StyledDataframe"] { direction: ltr !important; }
    
    /* استایل‌های کارت‌های داشبورد */
    .metric-card {
        background: linear-gradient(135deg, #1F4E78 0%, #2980B9 100%);
        color: white; padding: 20px; border-radius: 10px;
        text-align: center; margin: 5px; box-shadow: 0 4px 6px rgba(0,0,0,0.1);
    }
    .metric-card h3 { margin: 0; font-size: 28px; color: white; font-weight: bold;}
    .metric-card p { margin: 5px 0 0 0; font-size: 14px; color: #EBF5FB; }
    .info-box { background-color: #EBF5FB; border-right: 4px solid #3498DB; padding: 15px; border-radius: 5px; margin: 10px 0; }
    </style>
    """, unsafe_allow_html=True)


def render_sidebar() -> None:
    with st.sidebar:
        st.markdown(f"## 🏗️ {APP_NAME}")
        st.markdown(f"نسخه {APP_VERSION}")
        st.markdown("---")
        pages = {
            "dashboard": "📊 داشبورد", "projects": "📁 پروژه‌ها",
            "price_list": "📋 فهرست بها", "revit_upload": "📤 آپلود جداول Revit",
            "mapping": "🔗 Mapping", "settings": "⚙️ تنظیمات",
            "process": "▶️ پردازش متره", "results": "📊 نتایج",
            "detail": "📝 ریزمتره", "rebar": "🔩 لیستوفر آرماتور",
            "quality": "✅ گزارش کیفیت", "export": "💾 خروجی‌ها",
            "help": "❓ راهنما",
        }
        for key, label in pages.items():
            if st.button(label, key=f"nav_{key}", use_container_width=True):
                st.session_state.current_page = key
        st.markdown("---")
        if st.session_state.current_project_name:
            st.info(f"پروژه فعال: {st.session_state.current_project_name}")


def _require_project() -> Optional[int]:
    pid = st.session_state.current_project_id
    if not pid:
        st.warning("⚠️ ابتدا یک پروژه انتخاب کنید (بخش پروژه‌ها)")
        return None
    return pid


def page_dashboard() -> None:
    st.markdown("# 📊 داشبورد")
    db = get_db()
    projects = db.list_projects()
    col1, col2, col3, col4 = st.columns(4)
    with col1:
        st.markdown(f'<div class="metric-card"><h3>{len(projects)}</h3><p>تعداد پروژه‌ها</p></div>', unsafe_allow_html=True)

    pid = st.session_state.current_project_id
    if pid:
        price_df = db.get_price_list(pid)
        revit_files = db.get_revit_files(pid)
        revit_data = db.get_revit_data(pid)
        with col2:
            st.markdown(f'<div class="metric-card"><h3>{len(price_df)}</h3><p>ردیف فهرست بها</p></div>', unsafe_allow_html=True)
        with col3:
            st.markdown(f'<div class="metric-card"><h3>{len(revit_files)}</h3><p>فایل Revit</p></div>', unsafe_allow_html=True)
        with col4:
            st.markdown(f'<div class="metric-card"><h3>{len(revit_data)}</h3><p>ردیف داده Revit</p></div>', unsafe_allow_html=True)

        if st.session_state.last_result:
            st.markdown("### آخرین نتایج پردازش")
            res = st.session_state.last_result
            kpi = res.get("kpi", {})
            c1, c2, c3, c4 = st.columns(4)
            c1.metric("نرخ تطبیق", f"{kpi.get('match_rate', 0)}%")
            c2.metric("ردیف‌های نهایی", kpi.get("total_matched", 0))
            c3.metric("بدون تطبیق", kpi.get("total_unmatched", 0))
            total = res.get("summary", {}).get("total_price", 0)
            c4.metric("مبلغ کل (ریال)", f"{total:,.0f}")
    else:
        with col2:
            st.markdown('<div class="metric-card" style="background: #95a5a6;"><h3>—</h3><p>پروژه‌ای انتخاب نشده</p></div>', unsafe_allow_html=True)

    if not pid: st.info("💡 ابتدا یک پروژه ایجاد یا انتخاب کنید (بخش پروژه‌ها)")


def page_projects() -> None:
    st.markdown("# 📁 مدیریت پروژه‌ها")
    db = get_db()
    st.markdown("### ایجاد پروژه جدید")
    with st.form("new_project"):
        name = st.text_input("نام پروژه")
        desc = st.text_input("توضیحات (اختیاری)")
        year = st.text_input("سال فهرست بها (اختیاری)", "1404")
        if st.form_submit_button("ایجاد پروژه") and name:
            pid = db.create_project(name, desc, year)
            st.session_state.current_project_id = pid
            st.session_state.current_project_name = name
            st.success(f"پروژه «{name}» ایجاد شد")
            st.rerun()

    st.markdown("---")
    st.markdown("### پروژه‌های موجود")
    projects = db.list_projects()
    if not projects: st.info("هنوز پروژه‌ای ایجاد نشده است"); return

    for proj in projects:
        col1, col2, col3 = st.columns([3, 1, 1])
        with col1:
            active = proj["id"] == st.session_state.current_project_id
            marker = " ✅" if active else ""
            st.markdown(f"**{proj['name']}{marker}** — {proj['description']} (سال: {proj['price_list_year']})")
        with col2:
            if st.button("انتخاب", key=f"sel_{proj['id']}"):
                st.session_state.current_project_id = proj["id"]
                st.session_state.current_project_name = proj["name"]
                st.session_state.last_result = None
                st.rerun()
        with col3:
            if st.button("🗑️", key=f"del_{proj['id']}"):
                if proj["id"] == st.session_state.current_project_id:
                    st.session_state.current_project_id = None
                    st.session_state.current_project_name = ""
                db.delete_project(proj["id"])
                st.rerun()


def page_price_list() -> None:
    st.markdown("# 📋 فهرست بها")
    pid = _require_project()
    if not pid: return
    db = get_db()

    st.markdown("### آپلود فایل فهرست بها (Excel)")
    uploaded = st.file_uploader("فایل Excel فهرست بها را انتخاب کنید", type=["xlsx", "xls"], key="price_upload")

    if uploaded:
        with st.spinner("در حال خواندن فهرست بها..."):
            df, info = PriceListImporter.import_excel(io.BytesIO(uploaded.read()), uploaded.name)

        if info["errors"]:
            for e in info["errors"]: st.error(f"❌ {e}")
        if info["warnings"]:
            for w in info["warnings"]: st.warning(f"⚠️ {w}")

        c1, c2, c3, c4 = st.columns(4)
        c1.metric("شیت‌های پردازش‌شده", len(info["sheets_processed"]))
        c2.metric("کل ردیف‌ها", info["total_rows"])
        c3.metric("ردیف‌های معتبر", info["valid_rows"])
        c4.metric("سال تشخیصی", info["year"] or "نامشخص")

        if info["starred_rows"] > 0: st.info(f"🌟 {info['starred_rows']} ردیف ستاره‌دار شناسایی شد")

        if not df.empty:
            st.markdown("### پیش‌نمایش")
            st.dataframe(df.head(20), use_container_width=True)
            if st.button("💾 ذخیره فهرست بها در پروژه", type="primary"):
                count = db.save_price_list(pid, df)
                st.success(f"✅ {count} ردیف فهرست بها ذخیره شد")
                st.rerun()

    st.markdown("---")
    st.markdown("### فهرست بهای فعلی پروژه")
    current = db.get_price_list(pid)
    if current.empty: st.info("فهرست بها هنوز بارگذاری نشده است")
    else:
        st.success(f"✅ {len(current)} ردیف فهرست بها موجود است")
        with st.expander("مشاهده فهرست بها"): st.dataframe(current, use_container_width=True)


def page_revit_upload() -> None:
    st.markdown("# 📤 آپلود جداول Revit")
    pid = _require_project()
    if not pid: return
    db = get_db()

    st.markdown("### آپلود فایل‌های خروجی Revit (TXT یا CSV)")
    uploaded_files = st.file_uploader("فایل‌ها را انتخاب کنید (می‌توانید چند فایل انتخاب کنید)",
                                       type=["txt", "csv"], accept_multiple_files=True, key="revit_upload")

    if uploaded_files:
        for uploaded in uploaded_files:
            st.markdown(f"---\n#### 📄 {uploaded.name}")
            with st.spinner(f"در حال پردازش {uploaded.name}..."):
                file_bytes = uploaded.read()
                raw_df, records, info = RevitImporter.import_file(file_bytes, uploaded.name)

            if info["errors"]:
                for e in info["errors"]: st.error(f"❌ {e}")
                continue
            if info["warnings"]:
                for w in info["warnings"]: st.warning(f"⚠️ {w}")

            c1, c2, c3, c4 = st.columns(4)
            c1.metric("Encoding", info["encoding"])
            c2.metric("Delimiter", repr(info["delimiter"]))
            c3.metric("ردیف‌های معتبر", info["valid_rows"])
            c4.metric("نوع تشخیصی", f"{info['detected_type']} ({info['detected_confidence']:.0%})")

            if info.get("tables_detail"):
                with st.expander(f"📋 جزئیات {info['tables_found']} جدول"):
                    for td in info["tables_detail"]:
                        st.write(f"• **{td['title']}** → {td['category']} ({td['records']} ردیف)")

            if not raw_df.empty:
                with st.expander("پیش‌نمایش داده خام"): st.dataframe(raw_df.head(10), use_container_width=True)

            if records:
                if st.button(f"💾 ذخیره {uploaded.name}", key=f"save_rev_{uploaded.name}"):
                    fid = db.save_revit_file(pid, uploaded.name,
                                              "txt" if uploaded.name.endswith(".txt") else "csv",
                                              info["detected_type"], len(records), info["columns"])
                    cnt = db.save_revit_data(pid, fid, records)
                    st.success(f"✅ {cnt} ردیف از {uploaded.name} ذخیره شد")
                    st.rerun()

    st.markdown("---")
    files = db.get_revit_files(pid)
    ct, cc = st.columns([3, 1])
    with ct: st.markdown("### فایل‌های Revit موجود در پروژه")
    if not files: st.info("هنوز فایلی آپلود نشده است")
    else:
        with cc:
            if st.button("🗑️ حذف همه فایل‌ها", key="clear_all_revit"):
                db.clear_all_revit_files(pid)
                st.rerun()
        for f in files:
            c1, c2 = st.columns([4, 1])
            with c1:
                st.markdown(f"📄 **{f['filename']}** — نوع: `{f['detected_category']}` — **{f['row_count']}** ردیف — `{f['upload_time']}`")
            with c2:
                if st.button("🗑️ حذف", key=f"del_f_{f['id']}"):
                    db.delete_revit_file(f["id"])
                    st.rerun()


def page_mapping() -> None:
    st.markdown("# 🔗 مدیریت Mapping")
    pid = _require_project()
    if not pid: return
    db = get_db()

    st.markdown("### آپلود Mapping.xlsx")
    uploaded = st.file_uploader("فایل Mapping را انتخاب کنید", type=["xlsx", "xls"], key="mapping_upload")
    if uploaded:
        with st.spinner("در حال خواندن Mapping..."):
            df, info = MappingImporter.import_excel(io.BytesIO(uploaded.read()), uploaded.name)
        if info["errors"]:
            for e in info["errors"]: st.error(f"❌ {e}")
        else:
            st.success(f"✅ {info['rows']} قانون Mapping خوانده شد")
            if not df.empty:
                st.dataframe(df.head(20), use_container_width=True)
                if st.button("💾 ذخیره Mapping در پروژه", type="primary"):
                    count = db.save_mapping_rules(pid, df)
                    st.success(f"✅ {count} قانون ذخیره شد")
                    st.rerun()

    st.markdown("---")
    st.markdown("### Mapping فعلی پروژه")
    current = db.get_mapping_rules(pid)
    if current.empty:
        st.info("Mapping هنوز بارگذاری نشده است")
        st.markdown('<div class="info-box">💡 <b>راهنما:</b> فایل Mapping.xlsx باید شامل ستون‌های زیر باشد:<br><code>revit_key, match_type, usage, category, chapter, item_code, size, rebar_dia, notes, priority, active</code></div>', unsafe_allow_html=True)
    else:
        st.success(f"✅ {len(current)} قانون Mapping فعال")
        with st.expander("مشاهده Mapping"): st.dataframe(current, use_container_width=True)


def page_settings() -> None:
    st.markdown("# ⚙️ تنظیمات پروژه")
    pid = _require_project()
    if not pid: return
    db = get_db()

    st.markdown("### 📊 درصد پرت مصالح")
    waste = db.get_waste_settings(pid)
    waste_labels = {"concrete": "بتن", "rebar": "آرماتور", "formwork": "قالب‌بندی",
                    "block_joist": "سقف تیرچه بلوک", "masonry": "بنایی", "default": "سایر (پیش‌فرض)"}
    changed = False
    cols = st.columns(3)
    for i, (k, label) in enumerate(waste_labels.items()):
        with cols[i % 3]:
            cur = waste.get(k, DEFAULT_WASTE_PERCENTS.get(k, 3.0))
            new = st.number_input(f"{label} (%)", min_value=0.0, max_value=50.0,
                                   value=float(cur), step=0.5, key=f"w_{k}")
            if new != cur:
                db.update_waste_setting(pid, k, new)
                changed = True
    if changed: st.success("✅ درصد پرت به‌روزرسانی شد")

    st.markdown("---")
    st.markdown("### 📐 ضرایب پیمان")
    coeffs = db.get_coefficients(pid)
    changed2 = False
    cols2 = st.columns(3)
    for i, (name, data) in enumerate(coeffs.items()):
        with cols2[i % 3]:
            new = st.number_input(data["description"], min_value=0.0, max_value=10.0,
                                   value=float(data["value"]), step=0.01, key=f"c_{name}")
            if new != data["value"]:
                db.update_coefficient(pid, name, new)
                changed2 = True
    if changed2: st.success("✅ ضرایب به‌روزرسانی شد")


def page_process() -> None:
    st.markdown("# ▶️ پردازش متره و برآورد")
    pid = _require_project()
    if not pid: return
    db = get_db()

    price_df = db.get_price_list(pid)
    revit_data = db.get_revit_data(pid)
    status_ok = True
    if price_df.empty: st.warning("⚠️ فهرست بها بارگذاری نشده است"); status_ok = False
    else: st.success(f"✅ فهرست بها: {len(price_df)} ردیف")
    if revit_data.empty: st.warning("⚠️ داده Revit بارگذاری نشده است"); status_ok = False
    else: st.success(f"✅ داده Revit: {len(revit_data)} ردیف")

    mapping_df = db.get_mapping_rules(pid)
    if mapping_df.empty: st.info("ℹ️ Mapping بارگذاری نشده - سیستم از تشخیص خودکار پویای فهرست بها استفاده خواهد کرد")
    else: st.success(f"✅ Mapping: {len(mapping_df)} قانون")

    st.markdown("---")
    if st.button("🚀 شروع پردازش متره", type="primary", disabled=not status_ok, use_container_width=True):
        with st.spinner("در حال پردازش پویای داده‌ها... لطفاً صبر کنید"):
            engine = TakeoffEngine(db, pid)
            result = engine.run()
            st.session_state.last_result = result
            db.save_result(pid, {"timestamp": result["timestamp"], "summary": result["summary"],
                                  "quality": result["quality"], "kpi": result["kpi"]})
        st.success("✅ پردازش کامل شد!")

        q = result["quality"]
        kpi = result["kpi"]
        c1, c2, c3, c4 = st.columns(4)
        c1.metric("ردیف ورودی", q["total_revit_rows"])
        c2.metric("تطبیق‌یافته", kpi["total_matched"])
        c3.metric("بدون تطبیق", kpi["total_unmatched"])
        c4.metric("نرخ تطبیق", f"{kpi['match_rate']}%")

        if q["issues"]:
            st.markdown("### ⚠️ هشدارها")
            for issue in q["issues"]:
                icon = {"error": "❌", "warning": "⚠️", "info": "ℹ️"}.get(issue["type"], "ℹ️")
                st.markdown(f"{icon} **{issue['message']}** — {issue.get('suggestion', '')}")


def page_results() -> None:
    st.markdown("# 📊 نتایج پردازش")
    pid = _require_project()
    if not pid: return
    result = st.session_state.last_result
    if not result: st.info("ابتدا پردازش متره را اجرا کنید"); return

    items_df = result.get("items_df", make_empty_df(MATCHED_ITEM_SCHEMA))
    summary = result.get("summary", {})
    db = get_db()
    coeffs = db.get_coefficients(pid)
    total = summary.get("total_price", 0)
    final = total
    for name, data in coeffs.items(): final *= data["value"]

    st.markdown("### خلاصه مالی")
    c1, c2, c3 = st.columns(3)
    c1.metric("مبلغ خام (ریال)", f"{total:,.0f}")
    c2.metric("مبلغ با ضرایب (ریال)", f"{final:,.0f}")
    c3.metric("تعداد ردیف نهایی", summary.get("total_items", 0))

    st.markdown("### تفکیک بر اساس دسته")
    cat_data = summary.get("by_category", {})
    if cat_data:
        cdf = pd.DataFrame([{"دسته": k, "تعداد": v["count"], "مبلغ (ریال)": f"{v['total_price']:,.0f}"} for k, v in cat_data.items()])
        st.dataframe(cdf, use_container_width=True)

    st.markdown("### تفکیک بر اساس فصل")
    ch_data = summary.get("by_chapter", {})
    if ch_data:
        cdf = pd.DataFrame([{"فصل": k, "تعداد": v["count"], "مبلغ (ریال)": f"{v['total_price']:,.0f}"} for k, v in ch_data.items()])
        st.dataframe(cdf, use_container_width=True)

    st.markdown("### صورت وضعیت (تجمیعی)")
    if not items_df.empty:
        valid = items_df[items_df["item_code"] != ""].copy()
        if not valid.empty:
            agg = valid.groupby("item_code", as_index=False).agg({
                "item_description": "first", "unit": "first",
                "final_quantity": "sum", "unit_price": "first", "total_price": "sum"})
            agg.columns = ["کد ردیف", "شرح", "واحد", "مقدار", "بهای واحد", "مبلغ کل"]
            st.dataframe(agg, use_container_width=True)


def page_detail() -> None:
    st.markdown("# 📝 ریزمتره تفصیلی")
    pid = _require_project()
    if not pid: return
    result = st.session_state.last_result
    if not result: st.info("ابتدا پردازش متره را اجرا کنید"); return
    items_df = result.get("items_df", make_empty_df(MATCHED_ITEM_SCHEMA))
    if items_df.empty: st.info("ردیفی برای نمایش وجود ندارد"); return

    st.markdown("### فیلترها")
    c1, c2, c3 = st.columns(3)
    with c1:
        cats = ["همه"] + sorted(items_df["category"].unique().tolist())
        sc = st.selectbox("دسته", cats)
    with c2:
        grps = ["همه"] + sorted(items_df["structural_group"].unique().tolist())
        sg = st.selectbox("گروه سازه‌ای", grps)
    with c3:
        mths = ["همه"] + sorted(items_df["match_method"].unique().tolist())
        sm = st.selectbox("روش تطبیق", mths)

    filt = items_df.copy()
    if sc != "همه": filt = filt[filt["category"] == sc]
    if sg != "همه": filt = filt[filt["structural_group"] == sg]
    if sm != "همه": filt = filt[filt["match_method"] == sm]

    st.markdown(f"**{len(filt)} ردیف**")
    disp_cols = ["raw_name", "category", "structural_group", "item_code", "unit",
                 "raw_quantity", "waste_percent", "final_quantity", "unit_price",
                 "total_price", "match_method", "match_confidence"]
    cn = {"raw_name": "نام Revit", "category": "دسته", "structural_group": "گروه",
          "item_code": "کد ردیف", "unit": "واحد", "raw_quantity": "مقدار خام",
          "waste_percent": "پرت%", "final_quantity": "مقدار نهایی",
          "unit_price": "بهای واحد", "total_price": "مبلغ کل",
          "match_method": "روش تطبیق", "match_confidence": "اطمینان"}
    disp = filt[[c for c in disp_cols if c in filt.columns]].copy()
    disp.columns = [cn.get(c, c) for c in disp.columns]
    st.dataframe(disp, use_container_width=True)


def page_rebar() -> None:
    st.markdown("# 🔩 لیستوفر آرماتور")
    pid = _require_project()
    if not pid: return
    result = st.session_state.last_result
    if not result: st.info("ابتدا پردازش متره را اجرا کنید"); return
    rebar_df = result.get("rebar_listof", make_empty_df(REBAR_LISTOF_SCHEMA))
    if rebar_df.empty: st.info("ردیف آرماتوری یافت نشد"); return

    st.markdown("### خلاصه وزن آرماتور بر اساس گروه سازه‌ای")
    gs = rebar_df.groupby("structural_group").agg({"net_weight": "sum", "gross_weight": "sum"}).reset_index()
    gs.columns = ["گروه سازه‌ای", "وزن خالص (kg)", "وزن با پرت (kg)"]
    st.dataframe(gs, use_container_width=True)

    st.markdown("### خلاصه بر اساس قطر واقعی (mm)")
    ds = rebar_df.groupby("diameter").agg({"count": "sum", "net_weight": "sum", "gross_weight": "sum"}).reset_index()
    ds.columns = ["قطر (mm)", "تعداد شاخه", "وزن خالص (kg)", "وزن با پرت (kg)"]
    st.dataframe(ds, use_container_width=True)

    st.markdown("### جزئیات کامل لیستوفر")
    disp_cols = {"location": "محل مصرف", "structural_group": "گروه سازه‌ای", "sub_group": "بخش",
                 "diameter": "قطر (mm)", "bar_length": "طول شاخه (m)", "count": "تعداد", "net_weight": "وزن خالص (kg)",
                 "waste_percent": "پرت%", "gross_weight": "وزن با پرت (kg)",
                 "item_code": "کد ردیف", "total_price": "مبلغ کل (ریال)"}
    disp = rebar_df[[c for c in disp_cols if c in rebar_df.columns]].copy()
    disp.columns = [disp_cols[c] for c in disp.columns]
    st.dataframe(disp, use_container_width=True)

    st.markdown("---")
    c1, c2 = st.columns(2)
    c1.metric("وزن خالص کل آرماتور (kg)", f"{rebar_df['net_weight'].sum():,.1f}")
    c2.metric("وزن با پرت کل آرماتور (kg)", f"{rebar_df['gross_weight'].sum():,.1f}")


def page_quality() -> None:
    st.markdown("# ✅ گزارش کیفیت داده")
    pid = _require_project()
    if not pid: return
    result = st.session_state.last_result
    if not result: st.info("ابتدا پردازش متره را اجرا کنید"); return

    q = result.get("quality", {})
    kpi = result.get("kpi", {})

    st.markdown("### شاخص‌های کلیدی")
    c1, c2, c3, c4 = st.columns(4)
    c1.metric("نرخ تطبیق", f"{kpi.get('match_rate', 0)}%")
    c2.metric("نرخ دقیق", f"{kpi.get('exact_rate', 0)}%")
    c3.metric("نرخ خطا", f"{kpi.get('unmatched_rate', 0)}%")
    c4.metric("ردیف‌های نهایی", f"{kpi.get('final_rate', 0)}%")

    st.markdown("### آمار تفصیلی")
    stats = [
        ("تعداد کل ردیف‌های Revit", q.get("total_revit_rows", 0)),
        ("ردیف‌های معتبر", q.get("valid_rows", 0)),
        ("تطبیق دقیق (Exact)", q.get("matched_exact", 0)),
        ("تطبیق Regex", q.get("matched_regex", 0)),
        ("تطبیق الگو (Pattern)", q.get("matched_pattern", 0)),
        ("تطبیق Fuzzy", q.get("matched_fuzzy", 0)),
        ("بدون تطبیق", q.get("unmatched", 0)),
        ("مقدار صفر", q.get("zero_quantity", 0)),
        ("بدون قیمت", q.get("no_price", 0)),
        ("نیازمند بررسی", q.get("needs_review", 0)),
        ("ردیف‌های نهایی", q.get("final_items", 0)),
    ]
    st.dataframe(pd.DataFrame(stats, columns=["شاخص", "مقدار"]), use_container_width=True)

    issues = q.get("issues", [])
    if issues:
        st.markdown("### ⚠️ مشکلات و هشدارها")
        for iss in issues:
            icon = {"error": "❌", "warning": "⚠️", "info": "ℹ️"}.get(iss["type"], "ℹ️")
            st.markdown(f"{icon} **{iss['message']}**\n\n   💡 *{iss.get('suggestion', '')}*")

    unmatched = result.get("unmatched_items", [])
    if unmatched:
        st.markdown("### موارد ناشناخته")
        um = pd.DataFrame(unmatched)
        rn = {"raw_name": "نام اصلی", "normalized_name": "نام نرمال",
              "category": "دسته تشخیصی", "source_file": "فایل منبع"}
        um = um.rename(columns=rn)
        st.dataframe(um, use_container_width=True)
        st.info("💡 برای رفع این موارد، ردیف‌های مربوطه را به Mapping.xlsx اضافه کنید")

    review = result.get("review_items", [])
    if review:
        st.markdown("### موارد نیازمند بررسی")
        rv = pd.DataFrame(review)
        rvc = ["raw_name", "item_code", "match_method", "match_confidence", "match_details", "issues"]
        rvd = rv[[c for c in rvc if c in rv.columns]]
        rn2 = {"raw_name": "نام Revit", "item_code": "کد پیشنهادی", "match_method": "روش",
               "match_confidence": "اطمینان", "match_details": "جزئیات", "issues": "مشکلات"}
        rvd = rvd.rename(columns=rn2)
        st.dataframe(rvd, use_container_width=True)


def page_export() -> None:
    st.markdown("# 💾 خروجی‌ها")
    pid = _require_project()
    if not pid: return
    result = st.session_state.last_result
    if not result: st.info("ابتدا پردازش متره را اجرا کنید"); return

    db = get_db()
    coeffs = db.get_coefficients(pid)

    st.markdown("### دانلود گزارش Excel جامع")
    st.markdown("""
    گزارش شامل:
    - صورت وضعیت / برآورد
    - ریزمتره تفصیلی
    - لیستوفر آرماتور
    - موارد ناشناخته
    - گزارش کیفیت
    """)
    if st.button("📥 تولید و دانلود Excel", type="primary", use_container_width=True):
        with st.spinner("در حال تولید گزارش..."):
            excel_data = ExcelExporter.export_full_report(result,
                            project_name=st.session_state.current_project_name, coefficients=coeffs)
        st.download_button(label="⬇️ دانلود فایل Excel", data=excel_data,
            file_name=f"MetreYar_{st.session_state.current_project_name}_{datetime.now().strftime('%Y%m%d_%H%M')}.xlsx",
            mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet",
            use_container_width=True)


def page_help() -> None:
    st.markdown("# ❓ راهنمای استفاده")
    st.markdown("""
    ## مراحل کار با متره‌یار
    ### ۱. ایجاد پروژه
    از بخش **پروژه‌ها** یک پروژه جدید ایجاد کنید.
    ### ۲. بارگذاری فهرست بها
    از بخش **فهرست بها** فایل Excel فهرست بهای خود را آپلود کنید.
    ### ۳. آپلود جداول Revit
    از بخش **آپلود جداول Revit** فایل‌های TXT یا CSV خروجی Schedule های Revit را آپلود کنید.
    ### ۴. بارگذاری Mapping (اختیاری)
    اگر فایل Mapping.xlsx دارید، آن را آپلود کنید.
    ### ۵. تنظیمات
    درصد پرت و ضرایب پیمان را تنظیم کنید.
    ### ۶. پردازش
    دکمه **شروع پردازش متره** را بزنید.
    ### ۷. بررسی نتایج
    - **نتایج**: خلاصه مالی و صورت وضعیت
    - **ریزمتره**: جزئیات تمام ردیف‌ها
    - **لیستوفر**: آرماتوربندی
    - **گزارش کیفیت**: بررسی صحت تطبیق
    ### ۸. خروجی
    گزارش Excel جامع دانلود کنید.
    """)


def main() -> None:
    st.set_page_config(page_title=APP_NAME, page_icon="🏗️", layout="wide", initial_sidebar_state="expanded")
    init_session_state()
    apply_rtl_style()
    render_sidebar()

    page = st.session_state.current_page
    page_map = {
        "dashboard": page_dashboard, "projects": page_projects,
        "price_list": page_price_list, "revit_upload": page_revit_upload,
        "mapping": page_mapping, "settings": page_settings,
        "process": page_process, "results": page_results,
        "detail": page_detail, "rebar": page_rebar,
        "quality": page_quality, "export": page_export, "help": page_help,
    }
    renderer = page_map.get(page, page_dashboard)
    try:
        renderer()
    except Exception as e:
        logger.exception(f"Error in page '{page}'")
        st.error(f"❌ خطا در بارگذاری صفحه: {e}")
        st.markdown('<div class="info-box">💡 لطفاً اطلاعات زیر را بررسی کنید:<br>- آیا پروژه انتخاب شده است؟<br>- آیا فایل‌های لازم آپلود شده‌اند؟<br>- آیا پردازش متره اجرا شده است؟</div>', unsafe_allow_html=True)
        with st.expander("جزئیات فنی خطا"): st.code(str(e))


if __name__ == "__main__":
    main()