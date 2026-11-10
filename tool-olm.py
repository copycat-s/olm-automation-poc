#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
OLM Solver v2 - Tool tự động giải bài tập trên OLM.vn
Hỗ trợ cả đề thường ([Luyện tập]) & đề thông minh ([Đề thông minh])
"""

import argparse
import base64
import getpass
import hashlib
import json
import os
import random
import re
import shutil
import socket
import subprocess
import sys
import time
import urllib.parse
from datetime import datetime

# Ép requests dùng IPv4 để tránh bị nghẽn mạng do IPv6 trên một số đường truyền
_orig_getaddrinfo = socket.getaddrinfo


def _getaddrinfo_ipv4(host, port, family=0, type=0, proto=0, flags=0):
    return _orig_getaddrinfo(host, port, socket.AF_INET, type, proto, flags)


socket.getaddrinfo = _getaddrinfo_ipv4

import requests

# --- Cấu hình mặc định ---
BASE = "https://olm.vn"
XOR_KEY = "1047823200"
UA = "Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:150.0) Gecko/20100101 Firefox/150.0"
TIMEOUT = 45
DEBUG_DIR = "debug"
ACCOUNTS_FILE = "accounts.json"
PAYLOAD_DUMP_DIR = "payload_dumps"

Q_TYPE_LABEL = {
    "1": "Trắc nghiệm 4 phương án",
    "2": "Điền đáp án",
    "3": "Kéo thả cơ bản",
    "4": "Ghép nối",
    "5": "Sắp xếp",
    "7": "Ghép nối",
    "10": "Gom nhóm",
    "11": "Danh sách thả xuống / Điền từ",
    "13": "Đúng/Sai",
    "17": "Kéo thả nâng cao",
    "18": "Tự luận",
}

UNSUPPORTED = set()

# Danh sách từ khóa JS nguy hiểm nhằm chặn Honeypot / RCE từ server
DANGEROUS_JS = re.compile(
    r"\b(require|process|child_process|fs|net|http|https|tls|dgram|cluster|module|exports|"
    r"global|globalThis|constructor|__proto__|prototype|eval|Function|import|spawn|exec|"
    r"execSync|fork|fetch|XMLHttpRequest|WebSocket)\b",
    re.IGNORECASE,
)

_warned_node_missing = False


# --- Logger đơn giản ---
def ok(m):
    print(f"  [OK] {m}")


def err(m):
    print(f"  [ERR] {m}")


def info(m):
    print(f"  [i] {m}")


def warn(m):
    print(f"  [!] {m}")


def sec(m):
    print(f"\n{'=' * 60}\n  {m}\n{'=' * 60}")


# --- Hàm bóc tách ngoặc lồng nhau (tránh gãy Regex) ---
def extract_balanced(text, start_pos, open_c="{", close_c="}"):
    """
    Trích xuất chính xác khối ngoặc lồng nhau {...} hoặc [...],
    tự động bỏ qua các chuỗi string ('...', \"...\", `...`) và ký tự escape.
    """
    pos = text.find(open_c, start_pos)
    if pos == -1:
        return None
    depth = 0
    in_str = None
    escaped = False
    for i in range(pos, len(text)):
        ch = text[i]
        if in_str:
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == in_str:
                in_str = None
        else:
            if ch in ('"', "'", "`"):
                in_str = ch
            elif ch == open_c:
                depth += 1
            elif ch == close_c:
                depth -= 1
                if depth == 0:
                    return text[pos : i + 1]
    return None


# --- Hàm giải mã nội dung câu hỏi ---
def xor_bytes(data: bytes, key: str) -> bytes:
    kb = key.encode("utf-8")
    return bytes(b ^ kb[i % len(kb)] for i, b in enumerate(data))


def decode_json_content(encoded):
    if not encoded:
        return None
    if isinstance(encoded, dict):
        return encoded

    s = str(encoded).strip()
    if s.startswith("{"):
        try:
            return json.loads(s)
        except Exception:
            return None

    try:
        # Tự bù padding cho base64 nếu thiếu
        cleaned = "".join(s.split())
        pad = (-len(cleaned)) % 4
        if pad:
            cleaned += "=" * pad
        raw = base64.b64decode(cleaned)
    except Exception:
        return None

    dec = xor_bytes(raw, XOR_KEY)
    text = dec.decode("utf-8", errors="ignore")

    if text.lstrip().startswith("<"):
        return None

    # OLM thường encode url 2 lần
    for _ in range(2):
        try:
            new = urllib.parse.unquote(text)
            if new == text:
                break
            text = new
        except Exception:
            break

    try:
        return json.loads(text)
    except Exception:
        return None


# --- Duyệt AST câu hỏi ---
def _walk(node):
    if not isinstance(node, dict):
        return
    yield node
    for c in node.get("children") or []:
        yield from _walk(c)


def _root(decoded):
    return decoded.get("root") or decoded


def _find_by_name(decoded, name):
    for n in _walk(_root(decoded)):
        if n.get("name") == name:
            return n
    return None


# --- Parsers cho các loại câu hỏi ---
def parse_choice(decoded):
    node = _find_by_name(decoded, "quiz-list")
    if not node:
        return None
    items = [c for c in (node.get("children") or []) if c.get("type") == "olm-list-item"]
    if not items:
        return None
    for i, it in enumerate(items):
        if it.get("correct") is True:
            return {"type": "choice", "index": i, "count": len(items)}
    return None


def parse_sort(decoded):
    node = _find_by_name(decoded, "sort-list")
    if not node:
        return None
    items = [c for c in (node.get("children") or []) if c.get("type") == "olm-list-item"]
    if not items:
        return None
    correct_idx = [i for i, it in enumerate(items) if it.get("correct") is True]
    if len(correct_idx) == len(items):
        return {"type": "sort", "order": correct_idx, "count": len(items)}
    return {"type": "sort", "order": list(range(len(items))), "count": len(items)}


def parse_merge(decoded):
    node = _find_by_name(decoded, "merge-list") or _find_by_name(decoded, "link-list")
    if not node:
        for n in _walk(_root(decoded)):
            if n.get("type") == "olm-list" and n.get("children"):
                node = n
                break
    if not node:
        return None

    pair_ids = []
    for item in node.get("children") or []:
        if item.get("type") != "olm-list-item":
            continue
        # Cột trái
        for c in item.get("children") or []:
            if c.get("type") == "position-column" and c.get("position") == "left" and c.get("pairID"):
                pair_ids.append(c["pairID"])
                break
        else:
            # Fallback nếu không có position="left"
            for c in item.get("children") or []:
                if c.get("type") == "position-column" and c.get("pairID"):
                    pair_ids.append(c["pairID"])
                    break

    if not pair_ids:
        return None
    return {"type": "merge", "pairs": pair_ids, "count": len(pair_ids)}


def parse_truefalse(decoded):
    node = _find_by_name(decoded, "true-false")
    if not node:
        return None
    items = [c for c in (node.get("children") or []) if c.get("type") == "olm-list-item"]
    if not items:
        return None
    bits = ["1" if it.get("correct") is True else "0" for it in items]
    return {"type": "truefalse", "bits": bits, "count": len(items)}


def _parse_input_text(decoded, name=""):
    for n in _walk(_root(decoded)):
        if n.get("type") == "olm-input-text" and (n.get("name") == name or not name):
            content = str(n.get("content") or "")
            parts = [p.strip() for p in content.split("||") if p.strip()]
            if not parts:
                return None
            return {
                "type": "input_text",
                "index": 0,
                "name": name,
                "count": len(parts),
                "answer": parts[0],
            }
    return None


def parse_dragmore(decoded):
    for n in _walk(_root(decoded)):
        if n.get("type") == "olm-input-text" and n.get("name") == "dragmore":
            items = [c for c in (n.get("children") or []) if c.get("type") == "drag-more-item"]
            if not items:
                return None
            for i, it in enumerate(items):
                if it.get("correct") is True:
                    return {"type": "choice", "index": i, "count": len(items)}
    return None


def parse_group(decoded):
    node = _find_by_name(decoded, "group-list")
    if not node:
        for n in _walk(_root(decoded)):
            if n.get("name") == "group-list" or (n.get("type") == "olm-list" and n.get("name") == "group-list"):
                node = n
                break
    if not node:
        return None

    groups = []
    all_items = []
    item_counter = 0

    for item in node.get("children") or []:
        if item.get("type") != "olm-list-item":
            continue
        title = ""
        group_pair_id = ""
        group_item_indices = []
        for c in item.get("children") or []:
            if c.get("type") == "group-title":
                title = c.get("text", "").strip()
            elif c.get("type") == "position-column":
                pair_id = c.get("pairID", "")
                if not group_pair_id:
                    group_pair_id = pair_id
                item_text = ""
                for sub in c.get("children") or []:
                    if sub.get("type") == "extended-text":
                        item_text = sub.get("text", "").strip()
                all_items.append({
                    "index": item_counter,
                    "text": item_text,
                    "pairID": pair_id,
                })
                group_item_indices.append(item_counter)
                item_counter += 1

        groups.append({
            "title": title,
            "pairID": group_pair_id,
            "items": group_item_indices,
        })

    if not groups:
        return None

    answer_indices = [g["items"] for g in groups]
    return {
        "type": "group",
        "groups": groups,
        "answer": answer_indices,
        "count": len(all_items),
        "group_count": len(groups),
        "items": all_items,
    }


def parse_fillme(decoded):
    for n in _walk(_root(decoded)):
        if n.get("type") == "fillme-input":
            content = str(n.get("content") or "").strip()
            m = re.search(r"@([a-zA-Z0-9_.]+)@", content)
            if m:
                return {
                    "type": "fillme",
                    "answer": None,
                    "var_name": m.group(1),
                    "count": 1,
                }
            return {
                "type": "fillme",
                "answer": content,
                "count": 1,
            }
    return None


def parse_essay(decoded, q_type=None):
    if str(q_type) == "18":
        return {"type": "essay", "answer": "", "count": 1}
    has_exp = _find_by_name(decoded, "exp") is not None
    has_choice = _find_by_name(decoded, "quiz-list") is not None
    has_sort = _find_by_name(decoded, "sort-list") is not None
    has_merge = (
        _find_by_name(decoded, "merge-list") is not None
        or _find_by_name(decoded, "link-list") is not None
    )
    has_group = _find_by_name(decoded, "group-list") is not None
    has_tf = _find_by_name(decoded, "true-false") is not None
    has_fillme = any(n.get("type") == "fillme-input" for n in _walk(_root(decoded)))
    if has_exp and not (
        has_choice or has_sort or has_merge or has_group or has_tf or has_fillme
    ):
        return {"type": "essay", "answer": "", "count": 1}
    return None


def resolve_fillme_var(meta, qid, var_name):
    params_map = meta.get("params_map", {})
    js_str = params_map.get(str(qid), "")
    if js_str:
        escaped = re.escape(var_name)
        m = re.search(rf"{escaped}\s*=\s*([^;]+);", js_str)
        if m:
            val = m.group(1).strip()
            if (val.startswith('"') and val.endswith('"')) or (
                val.startswith("'") and val.endswith("'")
            ):
                val = val[1:-1]
            return val
    return None


def eval_olm_js(js_code):
    """
    Chạy mã JavaScript sinh biến an toàn:
    - Kiểm tra Node.js có sẵn không
    - Chặn tĩnh các từ khóa truy cập hệ điều hành / runtime (chống Honeypot & RCE)
    - Chạy trong sandbox vm của Node với quyền hạn tối thiểu và timeout
    """
    global _warned_node_missing
    if not js_code:
        return None

    if not shutil.which("node"):
        if not _warned_node_missing:
            warn("Không tìm thấy Node.js trên máy ('node'). Không thể tự sinh biến câu hỏi JS.")
            info("→ Gợi ý cài đặt: 'apt install nodejs' hoặc 'pkg install nodejs'.")
            _warned_node_missing = True
        return None

    # Lớp phòng vệ 1: Chặn đứng mã độc chứa lệnh nguy hiểm
    match = DANGEROUS_JS.search(js_code)
    if match:
        warn(
            f"CẢNH BÁO AN NINH: Phát hiện mã JS chứa từ khóa nguy hiểm ('{match.group(1)}'). Đã chặn thực thi!"
        )
        return None

    # Lớp phòng vệ 2: Chạy mã trong sandbox cách ly (node:vm) qua stdin
    runner = (
        "const vm = require('node:vm');\n"
        "const fs = require('node:fs');\n"
        "const code = fs.readFileSync(0, 'utf-8');\n"
        "const sandbox = {\n"
        "    Math: Math,\n"
        "    random: (min, max) => Math.floor(Math.random() * (max - min + 1)) + min,\n"
        "    p: {},\n"
        "    params: (obj) => {},\n"
        "    parseInt: parseInt,\n"
        "    parseFloat: parseFloat,\n"
        "    isNaN: isNaN,\n"
        "    isFinite: isFinite,\n"
        "    String: String,\n"
        "    Number: Number,\n"
        "    Array: Array,\n"
        "    Boolean: Boolean,\n"
        "};\n"
        "const ctx = vm.createContext(sandbox, { codeGeneration: { strings: false, wasm: false } });\n"
        "try {\n"
        "    vm.runInContext(code, ctx, { timeout: 2000 });\n"
        "    console.log(JSON.stringify(sandbox.p));\n"
        "} catch (e) {\n"
        "    process.exit(2);\n"
        "}\n"
    )

    try:
        res = subprocess.run(
            ["node", "-e", runner],
            input=js_code,
            capture_output=True,
            text=True,
            timeout=5,
        )
        if res.returncode == 0 and res.stdout.strip():
            return json.loads(res.stdout.strip())
    except Exception:
        pass
    return None


def classify_and_parse(decoded, q_type=None):
    parsers = (
        parse_choice,
        parse_group,
        parse_dragmore,
        parse_sort,
        parse_merge,
        parse_truefalse,
        parse_fillme,
        lambda d: parse_essay(d, q_type=q_type),
        lambda d: _parse_input_text(d, "selecttext"),
        lambda d: _parse_input_text(d, "dragtext"),
        lambda d: _parse_input_text(d, ""),
    )
    for fn in parsers:
        try:
            r = fn(decoded)
        except Exception:
            r = None
        if r:
            return r
    return None


# --- Ghi log debug & payload ---
def dump_debug(failed, meta, url):
    if not failed:
        return None
    os.makedirs(DEBUG_DIR, exist_ok=True)
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    fname = os.path.join(DEBUG_DIR, f"debug_olm_{ts}.txt")

    with open(fname, "w", encoding="utf-8") as f:
        f.write("=" * 60 + "\n")
        f.write(f"OLM DEBUG - {datetime.now().isoformat()}\n")
        f.write(f"URL: {url}\n")
        f.write(f"Tổng câu: {len(meta.get('question_ids', []))}\n")
        f.write(f"Số câu fail: {len(failed)}\n")
        f.write(f"id_cate: {meta.get('id_cate')}\n")
        f.write(f"id_courseware: {meta.get('id_courseware')}\n")
        f.write(f"id_subject: {meta.get('id_subject')}\n")
        f.write(f"is_smart: {meta.get('is_smart')}\n")
        f.write("=" * 60 + "\n")

        for i, item in enumerate(failed, 1):
            f.write(f"\n--- FAIL #{i}/{len(failed)} ---\n")
            f.write(f"Lý do: {item.get('reason', '?')}\n")
            f.write(f"id: {item.get('id', '?')}\n")
            f.write(f"title: {item.get('title', '?')}\n")
            q_type = str(item.get("q_type", "?"))
            f.write(f"q_type: {q_type} ({Q_TYPE_LABEL.get(q_type, '?')})\n")
            f.write(f"qType_label: {item.get('qType_label', '?')}\n")

            jc = item.get("json_content", "")
            f.write(f"\n--- json_content (len={len(str(jc))}) ---\n{jc}\n")

            dec = decode_json_content(jc)
            if dec:
                f.write("\n--- decoded ---\n")
                f.write(json.dumps(dec, indent=2, ensure_ascii=False) + "\n")
            else:
                f.write("\n--- decoded: FAIL ---\n")
            f.write("\n")
    return fname


def dump_payload(task, payload):
    try:
        os.makedirs(PAYLOAD_DUMP_DIR, exist_ok=True)
        ts = datetime.now().strftime("%Y%m%d_%H%M%S")
        fname = os.path.join(PAYLOAD_DUMP_DIR, f"payload_{ts}.txt")
        with open(fname, "w", encoding="utf-8") as f:
            f.write(f"# Task: {task.get('title')}\n")
            f.write(f"# URL: {task.get('url')}\n")
            f.write(f"# Time: {datetime.now().isoformat()}\n\n")
            if isinstance(payload, list):
                for k, v in payload:
                    s = str(v)
                    if len(s) > 400:
                        s = s[:400] + f"... [{len(s)} chars]"
                    f.write(f"{k} = {s}\n")
            elif isinstance(payload, dict):
                for k, v in payload.items():
                    s = str(v)
                    if len(s) > 400:
                        s = s[:400] + f"... [{len(s)} chars]"
                    f.write(f"{k} = {s}\n")
            else:
                f.write(str(payload) + "\n")
        return fname
    except Exception as e:
        warn(f"Lỗi dump payload: {e}")
        return None


# --- Quản lý tài khoản & mã hóa mật khẩu ---
def _get_local_key():
    """Tạo khóa mã hóa cục bộ dựa trên thông tin máy tính để tránh lưu plaintext."""
    try:
        user_str = getpass.getuser()
    except Exception:
        user_str = "user"
    seed = f"{user_str}@{socket.gethostname()}-olm-local-salt"
    return hashlib.sha256(seed.encode("utf-8")).digest()


def encrypt_password(pw: str) -> str:
    if not pw:
        return ""
    key = _get_local_key()
    data = pw.encode("utf-8")
    xor_d = bytes(b ^ key[i % len(key)] for i, b in enumerate(data))
    return "enc:v1:" + base64.b64encode(xor_d).decode("utf-8")


def decrypt_password(val: str) -> str:
    if not val:
        return ""
    if str(val).startswith("enc:v1:"):
        try:
            b64_str = str(val)[len("enc:v1:") :]
            xor_d = base64.b64decode(b64_str)
            key = _get_local_key()
            data = bytes(b ^ key[i % len(key)] for i, b in enumerate(xor_d))
            return data.decode("utf-8", errors="ignore")
        except Exception:
            return val
    # Tương thích ngược nếu file đã lưu plaintext trước đó
    return val


def load_accounts():
    if not os.path.exists(ACCOUNTS_FILE):
        return []
    try:
        with open(ACCOUNTS_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
        if not isinstance(data, list):
            return []
        migrated = False
        for acc in data:
            raw_pw = acc.get("password", "")
            if raw_pw and not str(raw_pw).startswith("enc:v1:"):
                migrated = True
            acc["password"] = decrypt_password(raw_pw)
        if migrated:
            save_accounts(data)
        return data
    except Exception:
        return []


def save_accounts(accounts):
    try:
        to_save = []
        for acc in accounts:
            item = dict(acc)
            raw_pw = item.get("password", "")
            if raw_pw and not str(raw_pw).startswith("enc:v1:"):
                item["password"] = encrypt_password(raw_pw)
            to_save.append(item)
        with open(ACCOUNTS_FILE, "w", encoding="utf-8") as f:
            json.dump(to_save, f, ensure_ascii=False, indent=2)
    except Exception as e:
        warn(f"Không lưu được accounts: {e}")


# --- Cấu hình điểm số ---
def random_score(min_score, max_score):
    if min_score > max_score:
        min_score, max_score = max_score, min_score
    min_score = max(0.0, float(min_score))
    max_score = float(max_score)
    if max_score > 10.0:
        warn(f"max_score={max_score} > 10.0 (thang điểm chuẩn thường là 10.0)")

    min_tenth = int(round(min_score * 10))
    max_tenth = int(round(max_score * 10))
    return round(random.randint(min_tenth, max_tenth) / 10.0, 1)


class ScoreConfig:
    def __init__(
        self,
        mode=3,
        score=None,
        correct=None,
        score_min=8.0,
        score_max=10.0,
        max_score=10.0,
    ):
        self.mode = mode
        self.score = score
        self.correct = correct
        self.score_min = score_min
        self.score_max = score_max
        self.max_score = max_score


# --- Phiên làm việc OLM (Session & Auth) ---
class OLMSession:
    def __init__(self):
        self.s = requests.Session()
        self.s.headers.update({
            "User-Agent": UA,
            "Accept": "application/json, text/javascript, */*; q=0.01",
            "Accept-Language": "vi-VN,vi;q=0.9,en;q=0.8",
            "X-Requested-With": "XMLHttpRequest",
            "Origin": BASE,
            "Referer": BASE,
        })
        self.csrf = ""
        self.user = {}
        self.id_school = ""
        self.cli_grade = ""

    def login(self, username, password):
        sec("ĐĂNG NHẬP OLM")
        try:
            r = self.s.get(f"{BASE}/dangnhap", timeout=TIMEOUT)
        except Exception as e:
            err(f"Không kết nối được OLM: {e}")
            return False

        m = re.search(r'name="csrf-token"\s+content="([^"]+)"', r.text)
        self.csrf = m.group(1) if m else self.s.cookies.get("XSRF-TOKEN", "")
        if not self.csrf:
            err("Không lấy được CSRF token từ trang đăng nhập")
            return False
        self.s.headers["X-CSRF-TOKEN"] = self.csrf
        info(f"CSRF: {self.csrf[:20]}...")

        # Bypass kiểm tra 2FA nếu có
        try:
            self.s.post(
                f"{BASE}/2fa/verify/check-enable",
                json={
                    "username": username,
                    "password": password,
                    "remember": "true",
                    "p_seudo_id": "",
                    "device_id": UA,
                    "platform": "web",
                },
                timeout=TIMEOUT,
            )
        except Exception:
            pass

        # Gửi form đăng nhập
        try:
            r = self.s.post(
                f"{BASE}/post-login",
                data={
                    "username": username,
                    "password": password,
                    "remember": "true",
                    "p_seudo_id": "",
                    "device_id": UA,
                    "platform": "web",
                    "_token": self.csrf,
                },
                timeout=TIMEOUT,
            )
            j = r.json()
            if j.get("message") != "success":
                err(f"Đăng nhập thất bại: {j.get('message')}")
                return False
        except Exception as e:
            err(f"Lỗi gửi request đăng nhập: {e}")
            return False

        # Khởi tạo session tại /lop-hoc-cua-toi
        try:
            r_init = self.s.get(f"{BASE}/lop-hoc-cua-toi?action=login", timeout=TIMEOUT)
            m2 = re.search(r'name="csrf-token"\s+content="([^"]+)"', r_init.text)
            if m2:
                self.csrf = m2.group(1)
                self.s.headers["X-CSRF-TOKEN"] = self.csrf
        except Exception:
            pass

        # Lấy thông tin user qua access_token
        tok = self.s.cookies.get("access_token")
        if tok:
            try:
                r_auth = self.s.post(
                    "https://account.olm.vn/auth",
                    json={"access_token": tok},
                    timeout=TIMEOUT,
                )
                auth = r_auth.json()
                self.user = auth.get("user") or {}
            except Exception:
                pass

        school = self.user.get("school")
        if isinstance(school, dict) and school.get("_id"):
            self.id_school = str(school["_id"])
        else:
            self.id_school = self._get_school_id()

        name = self.user.get("name") or username
        ok(f"Đăng nhập thành công: {name} (ID: {self.user.get('_id', '?')})")
        if self.id_school:
            info(f"ID Trường: {self.id_school}")
        return True

    def refresh_csrf(self):
        try:
            r = self.s.get(f"{BASE}/lop-hoc-cua-toi", timeout=TIMEOUT)
            m = re.search(r'name="csrf-token"\s+content="([^"]+)"', r.text)
            if m:
                self.csrf = m.group(1)
            elif self.s.cookies.get("XSRF-TOKEN"):
                self.csrf = self.s.cookies.get("XSRF-TOKEN")
            self.s.headers["X-CSRF-TOKEN"] = self.csrf
        except Exception:
            pass

    def alive(self):
        try:
            r = self.s.get(f"{BASE}/lop-hoc-cua-toi", timeout=TIMEOUT)
            return r.status_code == 200 and "dangnhap" not in r.url
        except Exception:
            return False

    def _get_school_id(self):
        try:
            r = self.s.get(f"{BASE}/lop-hoc-cua-toi", timeout=TIMEOUT)
            m = re.search(r'"school"\s*:\s*\{[^{}]*?"_id"\s*:\s*(\d+)', r.text)
            if m:
                return m.group(1)
            m = re.search(r'id_school["\']?\s*:\s*["\']?(\d+)', r.text)
            if m:
                return m.group(1)
        except Exception:
            pass
        return "0"


# --- Bộ giải đề OLM ---
class OLMSolver(OLMSession):
    def __init__(self):
        super().__init__()
        self._last_payload = None

    # Quét danh sách bài tập từ API v2
    def scan_all_tasks(self, start_page=1, max_pages=20):
        sec("QUÉT DANH SÁCH BÀI TẬP")
        info(f"Bắt đầu từ trang {start_page}, tối đa {max_pages} trang")
        self.refresh_csrf()
        self.s.headers["Referer"] = f"{BASE}/lop-hoc-cua-toi"

        tasks = []
        page = start_page
        pages_scanned = 0
        last_data = {}

        while pages_scanned < max_pages:
            url = f"{BASE}/classes/courseware/list-courseware-of-student?with_stats=1&limit=50&page={page}"
            try:
                r = self.s.get(url, timeout=TIMEOUT)
                if r.status_code != 200:
                    err(f"Trang {page} trả về HTTP {r.status_code}: {r.text[:100]}")
                    break
                data = r.json()
                last_data = data
            except Exception as e:
                err(f"Lỗi tải trang {page}: {e}")
                break

            items = data.get("list") or []
            if not items:
                info(f"Trang {page}: không còn bài tập -> dừng")
                break

            page_tasks = []
            for item in items:
                cate = item.get("cate") or {}
                prefix = cate.get("prefix") or ""
                pref_lower = prefix.lower()

                if "linh hoạt" in pref_lower:
                    task_type = "flexible_practice"
                elif "luyện tập" in pref_lower:
                    task_type = "exercise"
                elif "thông minh" in pref_lower:
                    task_type = "smart_exam"
                elif "kiểm tra" in pref_lower or "đề thi" in pref_lower:
                    task_type = "exam"
                elif "video" in pref_lower:
                    task_type = "video"
                elif "lý thuyết" in pref_lower:
                    task_type = "theory"
                elif "hỏi đáp" in pref_lower:
                    task_type = "qa"
                else:
                    task_type = "unknown"

                is_done = bool(item.get("isDone"))
                rec = item.get("record")
                is_smart = "thông minh" in pref_lower

                if is_done:
                    status = "done"
                elif rec is None:
                    status = "not_opened"
                elif rec.get("date_end", 0) > 0 or rec.get("ended") == 1:
                    status = "not_submitted"
                else:
                    status = "in_progress"

                score = (
                    float(rec.get("score", 0))
                    if rec and rec.get("score") is not None
                    else 0.0
                )
                percent = (
                    int(rec.get("percent", 0))
                    if rec and rec.get("percent") is not None
                    else (100 if is_done else 0)
                )

                id_cate = str(cate.get("id") or item.get("id_skill") or "")
                id_courseware = str(item.get("_id", ""))
                id_grade_task = str(item.get("id_grade") or cate.get("id_grade") or "")

                page_tasks.append({
                    "id_cate": id_cate,
                    "id_courseware": id_courseware,
                    "id_grade": id_grade_task,
                    "title": item.get("title", "").strip(),
                    "type": task_type,
                    "prefix": prefix,
                    "status": status,
                    "score": score,
                    "percent": percent,
                    "url": item.get("_url") or item.get("url") or "",
                    "is_smart": is_smart,
                    "is_done": is_done,
                    "raw": item,
                })

            info(f"Trang {page}: quét được {len(page_tasks)} bài tập")
            tasks.extend(page_tasks)

            pagi = data.get("pagi_info") or {}
            if not pagi.get("hasNextPage") or page >= pagi.get("last", 1):
                break

            page += 1
            pages_scanned += 1
            time.sleep(0.3)

        stats = last_data.get("stats") or {}
        ok(
            f"Tổng cộng quét được {len(tasks)} bài tập. "
            f"(Stats OLM: total={stats.get('total', len(tasks))}, "
            f"done={stats.get('done', '?')}, todo={stats.get('todo', '?')})"
        )
        return tasks

    # Bóc tách metadata từ trang bài tập (sử dụng extract_balanced chống gãy Regex)
    def get_exam_info(self, url, id_cate_hint="", id_courseware_hint="", task_hint=None):
        try:
            r = self.s.get(url, timeout=TIMEOUT)
        except Exception as e:
            err(f"Không thể tải trang bài tập {url}: {e}")
            return None
        html = r.text

        is_smart = bool(
            "thông minh" in html.lower()
            or "EXAM_SMART" in html
            or "exam-smart.js" in html
            or "list_cate_quiz" in html
        )
        is_flexible = bool(
            "linh hoạt" in html.lower()
            or re.search(r'type_practice["\']?\s*:\s*1', html)
        )

        # Trích xuất khối data_cate / data_practice nếu có trong thẻ script
        cate_block = ""
        m_cate = re.search(r'(?:var\s+)?data_cate\s*=\s*(\{)', html)
        if m_cate:
            cate_block = extract_balanced(html, m_cate.start(1), "{", "}") or ""

        def _grab(pat, default=""):
            if cate_block:
                mm = re.search(pat, cate_block)
                if mm:
                    return mm.group(1)
            mm = re.search(pat, html)
            return mm.group(1) if mm else default

        id_cate = id_cate_hint
        if not id_cate:
            m = re.search(r"-(\d{9,})", url)
            if m:
                id_cate = m.group(1)
            else:
                id_cate = _grab(r'id_category["\']?\s*:\s*["\']?(\d+)', "")

        id_courseware = id_courseware_hint
        if not id_courseware:
            m = re.search(r"[?&]i_c=(\d+)", url)
            if m:
                id_courseware = m.group(1)
            else:
                id_courseware = _grab(r'id_courseware["\']?\s*:\s*["\']?(\d+)', "")

        id_subject = _grab(r'id_subject["\']?\s*:\s*["\']?(\d+)', "3")
        id_group = _grab(r'id_group["\']?\s*:\s*["\']?(\d+)')
        id_school = _grab(r'id_school["\']?\s*:\s*["\']?(\d+)')
        type_vip = _grab(
            r'type_vip["\']?\s*:\s*["\']?(\d+)', "530" if is_smart else "200"
        )

        # Nhận diện id_grade thông minh, tuyệt đối không hardcode 10
        id_grade = getattr(self, "cli_grade", "") or ""
        if not id_grade:
            id_grade = _grab(r'id_grade["\']?\s*:\s*["\']?(\d+)', "")
        if not id_grade and task_hint:
            id_grade = str(task_hint.get("id_grade") or "")
        if not id_grade:
            title_ctx = (url + " " + (task_hint.get("title") if task_hint else "")).lower()
            m_grade_text = re.search(r"(?:lớp|khối|k)\s*(\d{1,2})\b", title_ctx)
            if m_grade_text and 1 <= int(m_grade_text.group(1)) <= 12:
                id_grade = m_grade_text.group(1)
        if not id_grade:
            user_grades = self.user.get("grades") or []
            if isinstance(user_grades, list) and user_grades:
                id_grade = str(user_grades[0])
            elif self.user.get("grade") or self.user.get("id_grade"):
                id_grade = str(self.user.get("grade") or self.user.get("id_grade"))
        if not id_grade:
            id_grade = "0"

        # Trích xuất danh sách câu hỏi an toàn
        question_ids = []
        # 1. Mảng list_id_quiz
        m_q = re.search(r'["\']?list_id_quiz["\']?\s*:\s*(\[)', html)
        if m_q:
            arr_str = extract_balanced(html, m_q.start(1), "[", "]")
            if arr_str:
                question_ids = re.findall(r"\d+", arr_str)

        # 2. Chuỗi list_id_quiz ("1,2,3")
        if not question_ids:
            m = re.search(r'["\']?list_id_quiz["\']?\s*:\s*"([^"]+)"', html)
            if m:
                question_ids = [x.strip() for x in m.group(1).split(",") if x.strip()]

        # 3. Mảng list_cate_quiz
        if not question_ids:
            m_qc = re.search(r'["\']?list_cate_quiz["\']?\s*:\s*(\[)', html)
            if m_qc:
                arr_str = extract_balanced(html, m_qc.start(1), "[", "]")
                if arr_str:
                    question_ids = re.findall(r"\d+", arr_str)

        # 4. data-(exam|practice|quiz)
        if not question_ids:
            for mm in re.finditer(r'data-(?:exam|practice|quiz)="([^"]+)"', html):
                raw = urllib.parse.unquote(mm.group(1))
                try:
                    j = json.loads(raw)
                    ids = j.get("list_id_quiz") or []
                    if ids:
                        question_ids = [str(x) for x in ids]
                        break
                except Exception:
                    continue

        # 5. olm-question-node data-id-script (kể cả unicode quotes dạng \\u0022)
        if not question_ids:
            q_scripts = re.findall(r'data-id-script\s*=\s*(?:\\\\u0022|[\"\'])(\d{9,})', html)
            if q_scripts:
                seen = set()
                question_ids = [x for x in q_scripts if not (x in seen or seen.add(x))]

        # 6. id_script trong _content
        if not question_ids:
            q_scripts = re.findall(r'["\']?id_script["\']?\s*:\s*["\']?(\d{9,})', html)
            if q_scripts:
                seen = set()
                question_ids = [x for x in q_scripts if not (x in seen or seen.add(x))]

        if not id_cate:
            err("Không trích xuất được id_category")
            return None
        if not question_ids:
            err("Không trích xuất được list_id_quiz")
            return None

        # Trích xuất record và count_redo bằng extract_balanced
        record_id = ""
        count_redo = "0"
        rec_str = ""
        m_rec = re.search(r'["\']?record["\']?\s*:\s*(\{)', html)
        if m_rec:
            rec_str = extract_balanced(html, m_rec.start(1), "{", "}") or ""
            if rec_str:
                m_id = re.search(r'["\']?_id["\']?\s*:\s*["\']([a-f0-9]{24})["\']', rec_str)
                if m_id:
                    record_id = m_id.group(1)
                m_redo = re.search(r'["\']?count_redo["\']?\s*:\s*["\']?(\d+)', rec_str)
                if m_redo:
                    count_redo = m_redo.group(1)
        else:
            m_id = re.search(r'["\']?record["\']?\s*:\s*["\']([a-f0-9]{24})["\']', html)
            if m_id:
                record_id = m_id.group(1)
            m_redo = re.search(r'["\']?count_redo["\']?\s*:\s*["\']?(\d+)', html)
            if m_redo:
                count_redo = m_redo.group(1)

        score_map = {}
        for mm in re.finditer(
            r'["\']?id_script["\']?\s*:\s*["\']?(\d+)["\']?[\s\S]*?["\']?score["\']?\s*:\s*["\']?([\d.]+)["\']?',
            html,
        ):
            score_map[mm.group(1)] = float(mm.group(2))

        # Trích xuất data_log mảng hoàn chỉnh, không lo bị cắt cụt do dấu ] hay key bị đảo
        params_map = {}
        target_dl = rec_str if rec_str else html
        m_dl = re.search(r'["\']?data_log["\']?\s*:\s*(\[)', target_dl)
        if m_dl:
            dl_str = extract_balanced(target_dl, m_dl.start(1), "[", "]")
            if dl_str:
                try:
                    dl = json.loads(dl_str)
                    for it in dl:
                        qid = str(it.get("idq") or it.get("id_question") or "")
                        if not qid:
                            continue
                        p = it.get("params") or it.get("q_params")
                        if isinstance(p, str):
                            try:
                                pj = json.loads(p)
                                params_map[qid] = pj.get("js", "")
                            except Exception:
                                params_map[qid] = ""
                        elif isinstance(p, dict):
                            params_map[qid] = p.get("js", "")
                        if it.get("score") is not None:
                            score_map[qid] = float(it["score"])
                except Exception:
                    pass

        if not score_map and question_ids:
            per = round(10.0 / len(question_ids), 4)
            score_map = {q: per for q in question_ids}

        # Trích xuất skill_map an toàn
        skill_map = {}
        m_sk = re.search(r'["\']?list_main_skill["\']?\s*:\s*(\{)', html)
        if m_sk:
            sk_str = extract_balanced(html, m_sk.start(1), "{", "}")
            if sk_str:
                try:
                    sk_json = json.loads(sk_str)
                    for qid, sks in sk_json.items():
                        if isinstance(sks, list):
                            skill_map[str(qid)] = [int(x) for x in sks if str(x).isdigit()]
                except Exception:
                    for mm in re.finditer(r'["\']?(\d+)["\']?\s*:\s*\[([^\]]*)\]', sk_str):
                        qid = mm.group(1)
                        skills = [int(x) for x in re.findall(r"\d+", mm.group(2))]
                        skill_map[qid] = skills

        return {
            "id_cate": id_cate,
            "id_courseware": id_courseware,
            "id_subject": id_subject,
            "id_group": id_group,
            "id_school": id_school or self.id_school or "0",
            "id_grade": id_grade,
            "type_vip": type_vip,
            "question_ids": question_ids,
            "url": url,
            "is_smart": is_smart,
            "is_flexible": is_flexible,
            "type_static": "2" if is_flexible else "0",
            "record_id": record_id,
            "count_redo": count_redo,
            "score_map": score_map,
            "skill_map": skill_map,
            "params_map": params_map,
        }

    # Tải nội dung câu hỏi và giải đáp án
    def fetch_answers(self, info_):
        question_ids = info_["question_ids"]
        if not question_ids:
            return {}, []

        self.refresh_csrf()
        payload = {
            "qlib_list": ",".join(str(q) for q in question_ids),
            "id_subject": info_["id_subject"],
            "id_skill": "",
            "cv_q": "1",
            "encodeXORBase64": "true",
        }
        headers = {
            "X-CSRF-TOKEN": self.csrf,
            "X-Requested-With": "XMLHttpRequest",
            "Referer": info_["url"],
        }

        try:
            r = self.s.post(
                f"{BASE}/course/question/get-question-of-ids",
                data=payload,
                headers=headers,
                timeout=TIMEOUT,
            )
        except Exception as e:
            err(f"Gọi API lấy câu hỏi thất bại: {e}")
            return {}, []

        if r.status_code != 200:
            err(f"get-question-of-ids HTTP {r.status_code}")
            return {}, []

        try:
            questions = r.json()
        except Exception as e:
            err(f"JSON câu hỏi không hợp lệ: {e}")
            return {}, []

        if not isinstance(questions, list):
            err(f"Response câu hỏi không phải list (type={type(questions)})")
            return {}, []

        score_map = info_.get("score_map", {})
        skill_map = info_.get("skill_map", {})
        is_smart = info_.get("is_smart", False)

        answers = {}
        failed = []
        skipped = 0

        for item in questions:
            qid_s = str(item.get("old_id") or item.get("_id") or item.get("id"))
            if qid_s not in info_["question_ids"]:
                qid_match = next(
                    (
                        q
                        for q in info_["question_ids"]
                        if q == str(item.get("old_id"))
                        or q == str(item.get("_id"))
                        or q == str(item.get("id"))
                    ),
                    None,
                )
                if qid_match:
                    qid_s = qid_match
                else:
                    skipped += 1
                    continue

            q_type = str(item.get("q_type", ""))
            if q_type in UNSUPPORTED:
                failed.append({
                    **item,
                    "reason": f"Dạng câu {q_type} ({Q_TYPE_LABEL.get(q_type, '?')}) chưa hỗ trợ",
                })
                warn(f"{item.get('title')} (id={qid_s}): dạng q_type={q_type} không hỗ trợ")
                continue

            encoded = item.get("json_content")
            if not encoded:
                failed.append({**item, "reason": "json_content rỗng"})
                warn(f"{item.get('title')} (id={qid_s}): json_content rỗng")
                continue

            decoded = decode_json_content(encoded)
            if not decoded:
                failed.append({**item, "reason": "decode_json_content thất bại"})
                warn(f"{item.get('title')} (id={qid_s}): decode fail")
                continue

            parsed = classify_and_parse(decoded, q_type=q_type)
            if not parsed:
                failed.append({
                    **item,
                    "reason": f"Không nhận diện được cấu trúc AST (q_type={q_type})",
                })
                warn(f"{item.get('title')} (id={qid_s}): không parse được")
                continue

            parsed.update({
                "title": item.get("title", ""),
                "q_type": q_type,
                "id_question": str(item.get("id", "")),
                "score": score_map.get(qid_s, 0.5) if is_smart else 1.0,
                "skills": skill_map.get(qid_s, []),
                "params_js": info_.get("params_map", {}).get(qid_s, ""),
            })

            if parsed.get("type") == "fillme":
                if parsed.get("answer") is None and parsed.get("var_name"):
                    var_name = parsed["var_name"]
                    resolved = resolve_fillme_var(info_, qid_s, var_name)
                    if resolved is not None:
                        parsed["answer"] = resolved
                        ok(f"{item.get('title')} (id={qid_s}) -> giải biến {var_name} = {resolved}")
                    else:
                        for n in _walk(_root(decoded)):
                            if n.get("type") == "code":
                                js_code = n.get("code", "")
                                p_dict = eval_olm_js(js_code)
                                if p_dict and "ans" in p_dict:
                                    parsed["answer"] = str(p_dict["ans"])
                                    js_str = "".join([f"p.{k}={v};" for k, v in p_dict.items()])
                                    parsed["params_js"] = js_str
                                    ok(f"{item.get('title')} (id={qid_s}) -> sinh biến: ans = {p_dict['ans']}")
                                    break
                                m = re.search(rf"{re.escape(var_name)}\s*=\s*([^;]+);", js_code)
                                if m:
                                    parsed["answer"] = m.group(1).strip()
                                    ok(f"{item.get('title')} (id={qid_s}) -> trích biến {var_name} = {parsed['answer']}")
                                    break

            answers[qid_s] = parsed
            ok(f"{item.get('title')} (id={qid_s}) -> dạng {parsed['type']}")

        if skipped:
            info(f"Đã bỏ qua {skipped} câu phụ")

        return answers, failed

    # Xóa kết quả làm bài cũ để làm lại (Redo)
    def redo_exam(self, meta):
        self.refresh_csrf()
        headers = {
            "X-CSRF-TOKEN": self.csrf,
            "X-Requested-With": "XMLHttpRequest",
            "Referer": meta.get("url", f"{BASE}/lop-hoc-cua-toi"),
        }
        id_cate = str(meta.get("id_cate", ""))
        id_user = str(self.user.get("_id", ""))
        record_id = meta.get("record_id", "")

        # 1. Thử DELETE theo record_id
        if record_id:
            try:
                r = self.s.delete(
                    f"{BASE}/course/teacher-static/{record_id}",
                    data={"id_cate": id_cate, "id_user": id_user},
                    headers=headers,
                    timeout=TIMEOUT,
                )
                if r.status_code == 200:
                    ok(f"Redo (DELETE /teacher-static/{record_id}) thành công")
                    return True
            except Exception:
                pass

        # 2. Thử DELETE chung
        try:
            r = self.s.delete(
                f"{BASE}/course/teacher-static",
                data={"id_cate": id_cate, "id_user": id_user},
                headers=headers,
                timeout=TIMEOUT,
            )
            if r.status_code == 200:
                ok("Redo (DELETE /course/teacher-static) thành công")
                return True
        except Exception:
            pass

        # 3. Thử PUT allow_redo
        if record_id:
            try:
                r = self.s.put(
                    f"{BASE}/course/teacher-static/{record_id}",
                    json={"allow_redo": 1},
                    headers=headers,
                    timeout=TIMEOUT,
                )
                if r.status_code == 200:
                    ok(f"Redo (PUT /teacher-static/{record_id}) thành công")
                    return True
            except Exception:
                pass

        return False

    # Nộp đề thường / Luyện tập
    def submit_normal(
        self,
        info_,
        answers,
        fake_seconds,
        correct_count_target=None,
        override_score=None,
    ):
        submit_ids = [str(q) for q in info_["question_ids"] if str(q) in answers]
        if not submit_ids:
            err("Không có câu nào để nộp")
            return False

        n = len(submit_ids)
        self.refresh_csrf()

        per_q = max(1, fake_seconds // n)
        remainder = fake_seconds - per_q * n
        now = int(time.time())
        data_log = []

        if correct_count_target is None:
            correct_indices = set(range(n))
        else:
            correct_count_target = max(0, min(n, correct_count_target))
            correct_indices = set(random.sample(range(n), correct_count_target))

        correct_count = 0
        is_flexible = bool(
            info_.get("is_flexible")
            or info_.get("type_static") == "2"
            or "linh hoạt" in str(info_.get("prefix", "")).lower()
        )

        for i, qid in enumerate(submit_ids):
            a = answers[qid]
            q_params_obj = {"js": ""}
            is_correct = i in correct_indices

            if a["type"] == "choice":
                q_params_obj["order"] = list(range(a["count"]))
                chosen_idx = a["index"] if is_correct else (a["index"] + 1) % a["count"]
                a_params_str = json.dumps([json.dumps([str(chosen_idx)])], ensure_ascii=False)
                result_mix = [1 if is_correct else 0]

            elif a["type"] == "sort":
                q_params_obj["order"] = list(range(a["count"]))
                ord_list = list(a["order"])
                if not is_correct and len(ord_list) > 1:
                    ord_list[0], ord_list[1] = ord_list[1], ord_list[0]
                a_params_str = json.dumps([json.dumps([str(x) for x in ord_list])], ensure_ascii=False)
                result_mix = [1 if is_correct else 0] * a["count"]

            elif a["type"] == "merge":
                q_params_obj["order"] = list(range(a["count"]))
                pairs = list(a["pairs"])
                if not is_correct and len(pairs) > 1:
                    pairs[0], pairs[1] = pairs[1], pairs[0]
                a_params_str = json.dumps([json.dumps(pairs)], ensure_ascii=False)
                result_mix = [1 if is_correct else 0] * a["count"]

            elif a["type"] == "truefalse":
                q_params_obj["order"] = list(range(a["count"]))
                bits = list(a["bits"])
                if not is_correct and bits:
                    bits[0] = "0" if bits[0] == "1" else "1"
                a_params_str = json.dumps([json.dumps([str(b) for b in bits])], ensure_ascii=False)
                result_mix = list(bits) if is_correct else [0] * len(bits)

            elif a["type"] == "input_text":
                q_params_obj["order"] = list(range(a["count"]))
                a_params_str = json.dumps(
                    [json.dumps(str(a["index"] if is_correct else -1))],
                    ensure_ascii=False,
                )
                result_mix = [1 if is_correct else 0]

            elif a["type"] == "group":
                q_params_obj["order"] = list(range(a["count"]))
                ans_group = a["answer"] if is_correct else [list(reversed(g)) for g in a["answer"]]
                a_params_str = json.dumps(ans_group, ensure_ascii=False)
                result_mix = [1 if is_correct else 0]

            elif a["type"] == "fillme":
                q_params_obj["order"] = [0]
                if a.get("params_js"):
                    q_params_obj["js"] = a["params_js"]
                ans_str = str(a.get("answer", "")) if is_correct else "-1"
                a_params_str = json.dumps([json.dumps(ans_str)], ensure_ascii=False)
                result_mix = [1 if is_correct else 0]

            elif a["type"] == "essay":
                q_params_obj["order"] = [0]
                a_params_str = json.dumps([""], ensure_ascii=False)
                result_mix = [2]
                is_correct = False

            if is_correct:
                correct_count += 1

            t_this = per_q + (remainder if i == n - 1 else 0)
            q_params_obj["time"] = t_this * 1000

            if is_flexible:
                q_params_str = json.dumps([json.dumps(q_params_obj, ensure_ascii=False)])
                qid_val = int(qid) if str(qid).isdigit() else qid
                dl_entry = {
                    "q_params": q_params_str,
                    "a_params": a_params_str,
                    "result": 1 if is_correct else 0,
                    "correct": 1 if is_correct else 0,
                    "wrong": 0 if is_correct else 1,
                    "a_index": i,
                    "time_spent": t_this,
                    "correct_skill": [],
                    "wrong_skill": [],
                    "resultMix": result_mix,
                    "json_a_params": "[null]",
                    "id_question": qid_val,
                }
            else:
                dl_entry = {
                    "q_params": json.dumps(q_params_obj, ensure_ascii=False),
                    "a_params": a_params_str,
                    "result": 1 if is_correct else 0,
                    "correct": 1 if is_correct else 0,
                    "wrong": 0 if is_correct else 1,
                    "a_index": i,
                    "time_spent": t_this,
                    "resultMix": result_mix,
                    "json_a_params": "[null]",
                    "id_question": a.get("id_question"),
                }
            data_log.append(dl_entry)

        id_school = self.id_school or info_.get("id_school", "0")
        id_group = info_.get("id_group") or str(self.user.get("id_group", ""))
        id_grade = str(info_.get("id_grade") or "0")

        if is_flexible:
            if override_score is not None:
                score_out = str(round(float(override_score) * 10))
            else:
                score_out = str(round(100.0 * correct_count / n)) if n else "100"
        else:
            if override_score is not None:
                score_out = str(override_score)
            else:
                score_out = str(round(10.0 * correct_count / n, 2)) if n else "10"

        payload = [
            ("id_user", str(self.user.get("_id", ""))),
            ("id_cate", str(info_["id_cate"])),
            ("id_courseware", str(info_["id_courseware"])),
            ("id_group", str(id_group)),
            ("id_school", str(id_school)),
            ("id_grade", id_grade),
            ("name_user", self.user.get("name", "")),
            ("type_vip", str(info_["type_vip"])),
            ("time_init", str(now - fake_seconds - 5)),
            ("time_spent", str(fake_seconds)),
            ("time_stored", str(now)),
            ("date_end", str(now - 3)),
            ("data_log", json.dumps(data_log, ensure_ascii=False)),
            ("score", score_out),
            ("answered", str(n)),
            ("correct", str(correct_count)),
            ("count_problems", str(n)),
            ("missed", str(n - correct_count)),
            ("ended", "1"),
            ("save_star", "1"),
            ("device", "web"),
            ("_token", self.csrf),
        ]
        if is_flexible:
            payload.append(("type_static", "2"))
            payload.append(("wrong", str(n - correct_count)))
            for q_id in info_.get("question_ids", []):
                payload.append(("quiz_list[]", str(q_id)))

        headers = {
            "X-CSRF-TOKEN": self.csrf,
            "X-Requested-With": "XMLHttpRequest",
            "Referer": info_["url"],
        }

        info(
            f"[NORMAL] Gửi {n} câu (đúng: {correct_count}/{n}, điểm: {score_out}, khối lớp: {id_grade}) — time_spent={fake_seconds}s"
        )
        self._last_payload = payload
        dump_payload(info_, payload)

        try:
            r = self.s.post(
                f"{BASE}/course/teacher-static",
                data=payload,
                headers=headers,
                timeout=TIMEOUT,
            )
        except Exception as e:
            err(f"Gửi bài tập thất bại: {e}")
            return False

        if r.status_code == 200:
            try:
                resp = r.json()
                if resp.get("_id") or resp.get("saved") or resp.get("message") == "success":
                    ok(f"Nộp thành công! (Record ID: {resp.get('_id', '?')})")
                    return True
            except Exception:
                pass
            ok("HTTP 200 — Nộp thành công")
            return True

        if r.status_code == 403:
            resp_txt = r.text
            try:
                msg = str(r.json().get("message", ""))
            except Exception:
                msg = resp_txt
            if "đã được nộp trước đó" in msg or "nộp trước đó" in msg or "n\\u1ed9p" in resp_txt:
                warn("Bài tập đã nộp trước đó -> Tự động gọi Redo/Reset...")
                if not info_.get("record_id"):
                    latest_meta = self.get_exam_info(info_.get("url", ""))
                    if latest_meta and latest_meta.get("record_id"):
                        info_["record_id"] = latest_meta["record_id"]
                self.redo_exam(info_)
                time.sleep(1.0)
            else:
                warn("Bị 403, thử refresh CSRF và gửi lại...")

            self.refresh_csrf()
            payload = [(k, (self.csrf if k == "_token" else v)) for k, v in payload]
            headers["X-CSRF-TOKEN"] = self.csrf
            try:
                r2 = self.s.post(
                    f"{BASE}/course/teacher-static",
                    data=payload,
                    headers=headers,
                    timeout=TIMEOUT,
                )
                if r2.status_code == 200:
                    ok("Nộp thành công sau khi retry!")
                    return True
            except Exception:
                pass

        err(f"Nộp thất bại: HTTP {r.status_code} - {r.text[:200]}")
        return False

    # Nộp đề thông minh ([Đề thông minh])
    def submit_smart(
        self,
        info_,
        answers,
        fake_seconds,
        correct_count_target=None,
        override_score=None,
        override_max=None,
    ):
        submit_ids = [str(q) for q in info_["question_ids"] if str(q) in answers]
        if not submit_ids:
            err("Không có câu nào để nộp")
            return False

        n = len(submit_ids)
        self.refresh_csrf()
        now = int(time.time())

        data_log = []
        quiz_list_int = []
        score_list = {}
        correct_count = wrong_count = 0
        correct_skills = []
        wrong_skills = []
        tn_score_real = 0.0

        objective_indices = [
            i for i, qid in enumerate(submit_ids) if answers[qid].get("type") != "essay"
        ]
        if correct_count_target is None:
            correct_indices = set(objective_indices)
        else:
            correct_count_target = max(0, min(len(objective_indices), correct_count_target))
            correct_indices = set(random.sample(objective_indices, correct_count_target))

        for i, qid in enumerate(submit_ids):
            a = answers[qid]
            q_params = {"js": ""}
            result_mix = [1]
            answer_arr = []
            label_arr = []
            skills = a.get("skills", []) or []

            order = list(range(a["count"]))
            random.shuffle(order)
            q_params["order"] = order

            is_correct = i in correct_indices

            if a["type"] == "choice":
                chosen_idx = a["index"] if is_correct else (a["index"] + 1) % a["count"]
                answer_arr = [str(chosen_idx)]
                label_arr = [chr(65 + chosen_idx)]
                result_mix = [1 if is_correct else 0]

            elif a["type"] == "sort":
                ord_list = list(a["order"])
                if not is_correct and len(ord_list) > 1:
                    ord_list[0], ord_list[1] = ord_list[1], ord_list[0]
                answer_arr = [str(x) for x in ord_list]
                result_mix = [1 if is_correct else 0] * a["count"]

            elif a["type"] == "merge":
                pairs = list(a["pairs"])
                if not is_correct and len(pairs) > 1:
                    pairs[0], pairs[1] = pairs[1], pairs[0]
                answer_arr = list(pairs)
                result_mix = [1 if is_correct else 0] * a["count"]

            elif a["type"] == "truefalse":
                bits = list(a["bits"])
                if not is_correct and bits:
                    bits[0] = "0" if bits[0] == "1" else "1"
                answer_arr = [str(b) for b in bits]
                result_mix = list(bits) if is_correct else [0] * len(bits)

            elif a["type"] == "input_text":
                answer_arr = [str(a["index"] if is_correct else -1)]
                result_mix = [1 if is_correct else 0]

            elif a["type"] == "group":
                answer_arr = a["answer"] if is_correct else [list(reversed(g)) for g in a["answer"]]
                label_arr = []
                result_mix = [1 if is_correct else 0]

            elif a["type"] == "fillme":
                chosen_ans = str(a.get("answer", "")) if is_correct else "-1"
                answer_arr = [chosen_ans]
                label_arr = []
                result_mix = [1 if is_correct else 0]
                q_params = {"js": a.get("params_js", "")}

            elif a["type"] == "essay":
                answer_arr = [""]
                label_arr = []
                result_mix = [2]
                q_params = {"js": ""}

            params_str = json.dumps(q_params, separators=(",", ":"), ensure_ascii=False)
            idq = int(a.get("id_question", qid))
            q_type_int = int(a.get("q_type", 1))
            score_val = float(a.get("score", 0.5))

            is_essay = a["type"] == "essay"
            if is_essay:
                chk = 2
                entry_correct_skill = []
                entry_wrong_skill = []
            elif is_correct:
                correct_count += 1
                tn_score_real += score_val
                correct_skills.extend(skills)
                entry_correct_skill = list(skills)
                entry_wrong_skill = []
                chk = 1
            else:
                wrong_count += 1
                wrong_skills.extend(skills)
                entry_correct_skill = []
                entry_wrong_skill = list(skills)
                chk = 0

            log_entry = {
                "answer": json.dumps(answer_arr, separators=(",", ":"), ensure_ascii=False),
                "label": label_arr,
                "params": params_str,
                "result": result_mix,
                "wrong_skill": entry_wrong_skill,
                "correct_skill": entry_correct_skill,
                "type": [q_type_int],
                "idq": idq,
                "score": score_val,
                "chk": chk,
            }
            if is_essay:
                log_entry["tlscore"] = -1
                log_entry["json_answer"] = [""]
            data_log.append(log_entry)
            quiz_list_int.append(idq)
            score_list[str(idq)] = score_val

        tn_score_real = round(tn_score_real, 2)
        if override_score is not None:
            final_score = float(override_score)
            tn_score_out = float(override_score)
        else:
            final_score = tn_score_real
            tn_score_out = tn_score_real

        max_score_out = override_max if override_max else 10.0
        total_q = len(info_["question_ids"])
        missed_count = max(0, total_q - correct_count - wrong_count)

        # Giả lập log thao tác của học sinh
        ip = self.user.get("ip") or "127.0.0.1"
        t = now - fake_seconds
        choose_log = []
        for i in range(n):
            for _ in range(random.randint(1, 2)):
                choose_log.append({
                    "ind": str(i),
                    "t": t,
                    "l": str(len(choose_log) + 1),
                    "ip": ip,
                })
                t += random.randint(1, 3)
        choose_log.append({
            "ind": str(n - 1),
            "t": t,
            "l": str(len(choose_log) + 1),
            "ip": ip,
        })

        id_school = self.id_school or info_.get("id_school", "0")
        id_group = info_.get("id_group") or str(self.user.get("id_group", ""))
        id_grade = str(info_.get("id_grade") or "0")

        payload = {
            "id_user": str(self.user.get("_id", "")),
            "id_cate": str(info_["id_cate"]),
            "id_grade": id_grade,
            "id_courseware": str(info_["id_courseware"]),
            "id_group": str(id_group),
            "id_school": str(id_school),
            "time_init": "",
            "name_user": self.user.get("name", ""),
            "type_vip": str(info_["type_vip"]),
            "time_spent": str(fake_seconds),
            "tl_score": "0",
            "tn_score": str(tn_score_out),
            "ended": "1",
            "missed": str(missed_count),
            "correct": str(correct_count),
            "wrong": str(wrong_count),
            "times": "0",
            "score": str(final_score),
            "max_score": str(max_score_out),
            "type_exam": "1",
            "time_stored": str(now),
            "save_star": "1",
            "date_end": str(now - 5),
            "_id": info_.get("record_id", ""),
            "nx": "",
            "_score": "0",
            "data_log": json.dumps(data_log, separators=(",", ":"), ensure_ascii=False),
            "iframe": "false",
            "count_redo": str(info_.get("count_redo", "0")),
        }

        flat = [(k, v) for k, v in payload.items() if not isinstance(v, list)]
        for sk in correct_skills:
            flat.append(("correct_skill[]", str(sk)))
        for sk in wrong_skills:
            flat.append(("wrong_skill[]", str(sk)))
        for q in quiz_list_int:
            flat.append(("quiz_list[]", str(q)))
        for q, sc in score_list.items():
            flat.append((f"score_list[{q}]", str(sc)))
        for i, entry in enumerate(choose_log):
            flat.append((f"choose_log[{i}][ind]", str(entry["ind"])))
            flat.append((f"choose_log[{i}][t]", str(entry["t"])))
            flat.append((f"choose_log[{i}][l]", str(entry["l"])))

        headers = {
            "X-CSRF-TOKEN": self.csrf,
            "X-Requested-With": "XMLHttpRequest",
            "Referer": info_["url"],
        }

        info(
            f"[SMART] Gửi {n} câu (điểm: {final_score}/{max_score_out}, đúng: {correct_count}/{n}, khối lớp: {id_grade})"
        )
        self._last_payload = flat
        dump_payload(info_, flat)

        try:
            r = self.s.post(
                f"{BASE}/course/teacher-static",
                data=flat,
                headers=headers,
                timeout=TIMEOUT,
            )
        except Exception as e:
            err(f"Gửi bài tập thông minh thất bại: {e}")
            return False

        if r.status_code == 200:
            try:
                resp = r.json()
                rec_id = resp.get("_id")
                if rec_id:
                    ok(f"Nộp thành công! (Record ID: {rec_id})")
                    return True
            except Exception:
                pass
            ok("HTTP 200 — Nộp thành công")
            return True

        if r.status_code == 403:
            resp_txt = r.text
            try:
                msg = str(r.json().get("message", ""))
            except Exception:
                msg = resp_txt
            if "đã được nộp trước đó" in msg or "nộp trước đó" in msg or "n\\u1ed9p" in resp_txt:
                warn("Bài tập đã nộp trước đó -> Tự động gọi Redo/Reset...")
                if not info_.get("record_id"):
                    latest_meta = self.get_exam_info(info_.get("url", ""))
                    if latest_meta and latest_meta.get("record_id"):
                        info_["record_id"] = latest_meta["record_id"]
                self.redo_exam(info_)
                time.sleep(1.0)
            else:
                warn("Bị 403, thử refresh CSRF và retry...")

            self.refresh_csrf()
            headers["X-CSRF-TOKEN"] = self.csrf
            flat = [(k, (self.csrf if k == "_token" else v)) for k, v in flat]
            try:
                r2 = self.s.post(
                    f"{BASE}/course/teacher-static",
                    data=flat,
                    headers=headers,
                    timeout=TIMEOUT,
                )
                if r2.status_code == 200:
                    ok("Nộp thành công sau retry!")
                    return True
            except Exception:
                pass

        err(f"Nộp thất bại: HTTP {r.status_code} - {r.text[:200]}")
        return False

    # Thực hiện làm 1 bài cụ thể
    def solve_one(
        self,
        task,
        min_t,
        max_t,
        score_config=None,
        correct_count_target=None,
        override_score=None,
        override_max=None,
        task_idx=None,
        total_tasks=None,
    ):
        url = task["url"]
        sec(f"LÀM BÀI: {task['title']}")
        info(f"URL: {url}")

        if not self.alive():
            err("Session đã hết hạn")
            return False

        meta = self.get_exam_info(
            url,
            id_cate_hint=task.get("id_cate", ""),
            id_courseware_hint=task.get("id_courseware", ""),
            task_hint=task,
        )
        if not meta:
            err("Không trích xuất được metadata đề thi")
            return False

        n = len(meta["question_ids"])
        if n == 0:
            err("Đề không chứa câu hỏi nào")
            return False

        # Tự động reset nếu bài này đã có kết quả trước đó
        if task.get("status") == "done" or meta.get("record_id"):
            warn("Bài tập đã làm trước đó -> gọi Redo/Reset...")
            if self.redo_exam(meta):
                ok("Reset record thành công, đợi 1.5s...")
                time.sleep(1.5)
                meta = self.get_exam_info(
                    url,
                    id_cate_hint=task.get("id_cate", ""),
                    id_courseware_hint=task.get("id_courseware", ""),
                    task_hint=task,
                ) or meta

        if task.get("prefix"):
            meta["prefix"] = task.get("prefix")
        if task.get("type") == "flexible_practice":
            meta["is_flexible"] = True
            meta["type_static"] = "2"

        kind_label = (
            "[Đề thông minh]"
            if meta["is_smart"]
            else (
                "[Luyện tập linh hoạt]"
                if meta.get("is_flexible")
                else "[Đề thường]"
            )
        )
        grade_info_str = f"khối {meta['id_grade']}" if meta.get("id_grade") and meta["id_grade"] != "0" else "chưa rõ khối"
        info(f"Loại bài: {kind_label} ({n} câu hỏi, {grade_info_str})")
        answers, failed = self.fetch_answers(meta)
        info(f"Giải mã thành công: {len(answers)} câu | Thất bại: {len(failed)} câu")

        if failed:
            dump_f = dump_debug(failed, meta, url)
            if dump_f:
                warn(f"Đã lưu chi tiết câu lỗi vào {dump_f}")
            warn(f"Có {len(failed)} câu không giải được -> Vẫn nộp {len(answers)} câu còn lại")

        if not answers:
            err("Không có câu hỏi nào hợp lệ để nộp")
            return False

        num_essay = sum(1 for a in answers.values() if a.get("type") == "essay")
        num_objective = len(answers) - num_essay
        max_tn_score = sum(
            float(a.get("score", 0.5))
            for a in answers.values()
            if a.get("type") != "essay"
        )
        if max_tn_score <= 0:
            max_tn_score = round(10.0 * num_objective / len(answers), 2) if answers else 10.0
        else:
            max_tn_score = round(max_tn_score, 2)

        # Tính toán điểm theo cấu hình
        if score_config is not None:
            if score_config.mode == 4:
                target_score = random_score(score_config.score_min, score_config.score_max)
                if num_essay > 0 and target_score > max_tn_score:
                    warn(f"Target score {target_score} > max tn_score {max_tn_score} (có {num_essay} câu tự luận). Tự giảm về {max_tn_score}.")
                    target_score = max_tn_score
                correct_count_target = round(target_score / (max_tn_score or 10.0) * num_objective)
                correct_count_target = max(0, min(num_objective, correct_count_target))
                override_score = target_score
                override_max = score_config.max_score or 10.0
                info(f"Score mode: RANDOM [{score_config.score_min} - {score_config.score_max}]")
                idx_str = f"Bài {task_idx}/{total_tasks}:" if task_idx and total_tasks else "Chi tiết bài làm:"
                info(f"{idx_str}")
                info(f"    → Target score: {target_score}")
                info(f"    → Correct target: {correct_count_target}/{num_objective} câu trắc nghiệm" + (f" (+ {num_essay} câu tự luận)" if num_essay else ""))
                info(f"    → Chọn ngẫu nhiên {correct_count_target} câu đúng")
            elif score_config.mode == 1:
                req_score = score_config.score if score_config.score is not None else 10.0
                if num_essay > 0 and req_score > max_tn_score:
                    warn(f"Đề có {num_essay} câu tự luận (chờ GV chấm), max tn_score = {max_tn_score}. Sẽ nộp {num_objective}/{num_objective} câu trắc nghiệm đúng.")
                    target_score = max_tn_score
                    correct_count_target = num_objective
                else:
                    target_score = req_score
                    correct_count_target = round(target_score / (max_tn_score or 10.0) * num_objective)
                    correct_count_target = max(0, min(num_objective, correct_count_target))
                override_score = target_score
                override_max = score_config.max_score or 10.0
                info(f"Score mode: FIXED SCORE {target_score}/{override_max}")
                info(f"    → Correct target: {correct_count_target}/{num_objective} câu trắc nghiệm" + (f" (+ {num_essay} câu tự luận)" if num_essay else ""))
            elif score_config.mode == 2:
                c_val = score_config.correct if score_config.correct is not None else (int(score_config.score) if score_config.score is not None else num_objective)
                correct_count_target = max(0, min(num_objective, c_val))
                override_score = round(max_tn_score * correct_count_target / num_objective, 2) if num_objective else max_tn_score
                override_max = score_config.max_score or 10.0
                info(f"Score mode: FIXED CORRECT {correct_count_target}/{num_objective} (điểm: {override_score})")
            elif score_config.mode == 3:
                if num_essay > 0:
                    warn(f"Đề có {num_essay} câu tự luận (chờ GV chấm), max tn_score = {max_tn_score}. Sẽ nộp {num_objective}/{num_objective} câu trắc nghiệm đúng.")
                    correct_count_target = num_objective
                    override_score = max_tn_score
                else:
                    correct_count_target = n
                    override_score = 10.0
                override_max = score_config.max_score or 10.0
                info(f"Score mode: DEFAULT ({override_score}/10)")

        if min_t > max_t:
            min_t, max_t = max_t, min_t
        fake_seconds = random.randint(min_t, max_t)
        info(f"Thời gian làm bài giả lập: {fake_seconds}s")

        if meta.get("is_smart"):
            return self.submit_smart(
                meta,
                answers,
                fake_seconds,
                correct_count_target=correct_count_target,
                override_score=override_score,
                override_max=override_max,
            )
        else:
            return self.submit_normal(
                meta,
                answers,
                fake_seconds,
                correct_count_target=correct_count_target,
                override_score=override_score,
            )


# --- Menu tương tác dòng lệnh ---
def pick_account(accounts):
    sec("CHỌN TÀI KHOẢN OLM")
    if accounts:
        for i, acc in enumerate(accounts, 1):
            name = acc.get("label") or acc.get("name") or acc.get("username")
            print(f"  {i}. {name} ({acc.get('username')})")
    else:
        print("  (Chưa lưu tài khoản nào)")

    print("  0. Nhập tài khoản mới")
    print("  q. Thoát")

    while True:
        raw = input("\nChọn [1]: ").strip().lower() or "1"
        if raw == "q":
            return None, False
        if raw == "0":
            return None, True
        try:
            n = int(raw)
            if 1 <= n <= len(accounts):
                return accounts[n - 1], False
        except ValueError:
            pass
        warn(f"Vui lòng chọn từ 0-{len(accounts)} hoặc q")


def create_account(accounts):
    sec("NHẬP TÀI KHOẢN MỚI")
    username = input("Username: ").strip()
    if not username:
        err("Username không được rỗng")
        return None
    password = input("Password: ").strip()
    if not password:
        err("Password không được rỗng")
        return None

    for acc in accounts:
        if acc.get("username") == username:
            acc["password"] = password
            save_accounts(accounts)
            return acc

    new_acc = {"username": username, "password": password, "label": username}
    accounts.append(new_acc)
    save_accounts(accounts)
    ok(f"Đã lưu tài khoản {username}")
    return new_acc


def config_score(total_q=20):
    sec("CẤU HÌNH ĐIỂM SỐ")
    print("  1. Điểm cố định (VD: 10, 9.5 điểm)")
    print("  2. Số câu đúng cố định (VD: 18/20 câu)")
    print("  3. Mặc định (Tất cả đúng -> 10/10)")
    print("  4. Random điểm trong khoảng (VD: 8.0 - 10.0)")

    choice = input("\nChọn chế độ (1/2/3/4) [3]: ").strip() or "3"
    if choice == "1":
        try:
            score = float(input("  Điểm muốn đạt [10]: ").strip() or "10")
        except ValueError:
            score = 10.0
        try:
            max_score = float(input("  Thang điểm tối đa [10]: ").strip() or "10")
        except ValueError:
            max_score = 10.0
        info(f"Đã cấu hình: score={score}, max_score={max_score}")
        return ScoreConfig(mode=1, score=score, max_score=max_score)
    elif choice == "2":
        try:
            correct = int(
                input(f"  Số câu muốn đúng (0-{total_q}) [{total_q}]: ").strip()
                or str(total_q)
            )
        except ValueError:
            correct = total_q
        correct = max(0, min(total_q, correct))
        info(f"Đã cấu hình: đúng ngẫu nhiên {correct}/{total_q} câu")
        return ScoreConfig(mode=2, correct=correct)
    elif choice == "4":
        try:
            min_sc = float(input("  Min score [8.0]: ").strip() or "8.0")
        except ValueError:
            min_sc = 8.0
        try:
            max_sc = float(input("  Max score [10.0]: ").strip() or "10.0")
        except ValueError:
            max_sc = 10.0
        if min_sc > max_sc:
            min_sc, max_sc = max_sc, min_sc
        if min_sc < 0.0:
            min_sc = 0.0
        if max_sc > 10.0:
            warn(f"max_score={max_sc} > 10.0 (hệ số điểm tối đa thông thường là 10.0)")
        info(f"→ Sẽ random điểm trong khoảng {min_sc} - {max_sc} (bước 0.1)")
        return ScoreConfig(mode=4, score_min=min_sc, score_max=max_sc)
    else:
        info("Đã cấu hình: Mặc định tất cả đúng (10/10)")
        return ScoreConfig(mode=3)


def pick_tasks(tasks):
    sec("DANH SÁCH BÀI TẬP")
    if not tasks:
        err("Không có bài nào")
        return []

    status_icon = {
        "done": "x",
        "not_submitted": "!",
        "in_progress": "~",
        "not_opened": " ",
    }
    type_label = {
        "flexible_practice": "Luyện tập linh hoạt",
        "exercise": "Luyện tập",
        "smart_exam": "Đề thông minh",
        "exam": "Đề thi/Kiểm tra",
        "video": "Video",
        "theory": "Lý thuyết",
        "qa": "Hỏi đáp",
        "unknown": "Khác",
    }

    groups = {}
    for t in tasks:
        groups.setdefault(t["type"], []).append(t)

    order = [
        "flexible_practice",
        "exercise",
        "smart_exam",
        "exam",
        "video",
        "theory",
        "qa",
        "unknown",
    ]
    idx = 1
    index_map = {}

    for t_type in order:
        group_items = groups.get(t_type, [])
        if not group_items:
            continue
        print(f"\n--- [{type_label.get(t_type, t_type).upper()}] ({len(group_items)} bài) ---")
        for item in group_items:
            icon = status_icon.get(item["status"], " ")
            sc_info = f" (Điểm: {item['score']})" if item["status"] == "done" else ""
            print(f"  {idx:3}. [{icon}] {item['title']}{sc_info}")
            index_map[idx] = item
            idx += 1

    print("\n  0. Thoát")
    print("  all. Chọn tất cả các bài chưa làm ([!], [~], [ ])")
    print("  Legend: [x] Đã xong | [!] Chưa nộp | [~] Đang làm | [ ] Chưa mở")

    while True:
        raw = input("\nNhập số bài muốn giải (VD: 1,3,7 hoặc 'all'): ").strip()
        if not raw:
            continue
        if raw == "0":
            return []
        if raw.lower() == "all":
            return [t for t in tasks if t["status"] != "done"]

        parts = [p.strip() for p in raw.split(",") if p.strip()]
        chosen = []
        bad = []
        for p in parts:
            try:
                n = int(p)
                if n in index_map:
                    chosen.append(index_map[n])
                else:
                    bad.append(p)
            except ValueError:
                bad.append(p)
        if bad:
            warn(f"Lựa chọn không hợp lệ: {', '.join(bad)}")
            continue
        if chosen:
            return chosen


# --- Main entry point ---
def main():
    parser = argparse.ArgumentParser(
        description="OLM Solver v2 — Tự động làm bài tập trên OLM.vn (React SPA v2)"
    )
    parser.add_argument("--username", "-u", help="Tài khoản đăng nhập OLM")
    parser.add_argument("--password", "-p", help="Mật khẩu OLM")
    parser.add_argument("--page", type=int, default=1, help="Trang bắt đầu quét (mặc định 1)")
    parser.add_argument("--max", type=int, default=10, help="Số trang quét tối đa (mặc định 10)")
    parser.add_argument("--url", help="Giải trực tiếp 1 URL bài tập cụ thể")
    parser.add_argument(
        "--grade",
        "-g",
        help="Khối lớp (VD: 8, 9, 10, 11, 12). Mặc định tự động nhận diện theo đề bài/tài khoản.",
    )
    parser.add_argument(
        "--score-mode",
        type=int,
        choices=[1, 2, 3, 4],
        help="Chế độ điểm (1: cố định, 2: số câu, 3: 10/10, 4: random trong khoảng)",
    )
    parser.add_argument("--score", type=float, help="Điểm số mong muốn nếu chọn mode 1")
    parser.add_argument("--correct", type=int, help="Số câu đúng mong muốn nếu chọn mode 2")
    parser.add_argument(
        "--score-min",
        type=float,
        default=8.0,
        help="Điểm tối thiểu khi random (mode 4, mặc định 8.0)",
    )
    parser.add_argument(
        "--score-max",
        type=float,
        default=10.0,
        help="Điểm tối đa khi random (mode 4, mặc định 10.0)",
    )
    parser.add_argument(
        "--random-score",
        nargs=2,
        type=float,
        metavar=("MIN", "MAX"),
        help="Shorthand cho mode 4: random điểm trong khoảng [MIN, MAX] (VD: --random-score 8.5 9.5)",
    )
    parser.add_argument("--min-time", type=int, default=90, help="Thời gian làm bài tối thiểu (giây)")
    parser.add_argument("--max-time", type=int, default=180, help="Thời gian làm bài tối đa (giây)")

    args = parser.parse_args()

    print("\n" + "=" * 60)
    print("          OLM SOLVER v2 - AUTO TOOL (REACT SPA)")
    print("=" * 60)

    # Kiểm tra môi trường Node.js
    if not shutil.which("node"):
        warn("Lưu ý: Không tìm thấy Node.js trên máy (cần Node.js để tự động giải các câu hỏi sinh biến JS).")
        info("→ Nếu gặp câu hỏi sinh biến toán học, vui lòng cài: 'apt install nodejs' hoặc 'pkg install nodejs'.")

    accounts = load_accounts()
    acc = None

    if args.username and args.password:
        acc = {"username": args.username, "password": args.password}
    else:
        while True:
            sel_acc, is_new = pick_account(accounts)
            if sel_acc is None and not is_new:
                warn("Đã hủy và thoát.")
                return
            if is_new:
                created = create_account(accounts)
                if created:
                    acc = created
                    break
            elif sel_acc:
                acc = sel_acc
                break

    solver = OLMSolver()
    if args.grade:
        solver.cli_grade = str(args.grade).strip()

    if not solver.login(acc["username"], acc["password"]):
        err("Không thể đăng nhập. Vui lòng kiểm tra lại tài khoản.")
        return

    # Xác định score_config từ arguments
    score_cfg = None
    if args.random_score:
        s_min, s_max = float(args.random_score[0]), float(args.random_score[1])
        if s_min > s_max:
            s_min, s_max = s_max, s_min
        if s_min < 0.0:
            s_min = 0.0
        score_cfg = ScoreConfig(mode=4, score_min=s_min, score_max=s_max)
    elif args.score_mode == 4:
        s_min, s_max = float(args.score_min), float(args.score_max)
        if s_min > s_max:
            s_min, s_max = s_max, s_min
        if s_min < 0.0:
            s_min = 0.0
        score_cfg = ScoreConfig(mode=4, score_min=s_min, score_max=s_max)
    elif args.score_mode == 1:
        sc = float(args.score) if args.score is not None else 10.0
        score_cfg = ScoreConfig(mode=1, score=sc, max_score=10.0)
    elif args.score_mode == 2:
        c_val = args.correct if args.correct is not None else (int(args.score) if args.score is not None else 18)
        score_cfg = ScoreConfig(mode=2, correct=c_val)
    elif args.score_mode == 3:
        score_cfg = ScoreConfig(mode=3)

    # Chế độ chạy trực tiếp với URL
    if args.url:
        task_direct = {
            "title": "Bài tập trực tiếp",
            "url": args.url,
            "status": "not_opened",
            "is_smart": "thông minh" in args.url.lower(),
        }
        if score_cfg is None:
            score_cfg = ScoreConfig(mode=3)
        solver.solve_one(
            task_direct,
            min_t=args.min_time,
            max_t=args.max_time,
            score_config=score_cfg,
            task_idx=1,
            total_tasks=1,
        )
        return

    # Quét bài tập
    tasks = solver.scan_all_tasks(start_page=args.page, max_pages=args.max)
    if not tasks:
        warn("Không tìm thấy bài tập nào.")
        return

    chosen_tasks = pick_tasks(tasks)
    if not chosen_tasks:
        info("Chưa chọn bài nào. Kết thúc.")
        return

    # Cấu hình thời gian làm bài
    min_t = args.min_time
    max_t = args.max_time
    if not (args.min_time != 90 or args.max_time != 180):
        try:
            raw_min = input(f"\nThời gian tối thiểu mỗi bài ({min_t}s): ").strip()
            if raw_min:
                min_t = int(raw_min)
            raw_max = input(f"Thời gian tối đa mỗi bài ({max_t}s): ").strip()
            if raw_max:
                max_t = int(raw_max)
        except ValueError:
            pass

    if min_t > max_t:
        min_t, max_t = max_t, min_t

    if score_cfg is None:
        score_cfg = config_score(total_q=20)

    # Xử lý tuần tự từng bài
    sec(f"BẮT ĐẦU XỬ LÝ {len(chosen_tasks)} BÀI TẬP")
    success = 0
    failed = 0

    for i, t in enumerate(chosen_tasks, 1):
        print(f"\n[{i}/{len(chosen_tasks)}] Đang thực hiện: {t['title']} ...")
        res = solver.solve_one(
            t,
            min_t=min_t,
            max_t=max_t,
            score_config=score_cfg,
            task_idx=i,
            total_tasks=len(chosen_tasks),
        )
        if res:
            success += 1
        else:
            failed += 1

    sec("KẾT QUẢ HOÀN THÀNH")
    ok(f"Số bài thành công: {success}/{len(chosen_tasks)}")
    if failed:
        warn(f"Số bài thất bại: {failed}/{len(chosen_tasks)}")


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("\n\n[!] Người dùng đã hủy thao tác.")
    except Exception as exc:
        print(f"\n[ERR] Lỗi không xử lý được: {exc}")
        import traceback
        traceback.print_exc()
