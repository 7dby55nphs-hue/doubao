# -*- coding: utf-8 -*-
"""豆包 图生视频（i2v）—— 老接口 /im/sse/send/message 单文件版。

这个文件不 import 项目里任何其它 .py：
  签名 / 上传 / 注册 / 发消息 / 拉消息链 / 读成片 / actionbar 配置解析
  全部在本文件内实现，只依赖 requests（无水印解析额外用 cryptography）。

接口差异：
  老接口 POST /im/sse/send/message → ext.action_bar_instruction（扁平）
  新接口 POST /chat/completion     → chat_ability.ability_param.instruction

用法：
    python i2v_im_sse_standalone.py          # 提交
    python i2v_im_sse_standalone.py --dry    # 只打印请求体，不发
"""

import base64
import hashlib
import hmac
import json
import os
import re
import struct
import sys
import time
import uuid
import zlib
from urllib.parse import quote, urlencode

import requests


# =========================
# 必填参数：改这里
# =========================
SESSIONID = "7e5fb67051886930939c72a44875c952"
PROMPT = "图1中的女子站在窗边，微风轻轻吹动头发，缓缓转头看向镜头并微笑，镜头缓慢推近，柔和自然光，画面自然流畅"
CONVERSATION_ID = ""          # 留空＝新建会话
BOT_ID = "7234781073513644036"

LOCAL_IMAGE_PATHS = [
    r"d:\doubaoapk\年轻女子.png",
]

VIDEO_MODEL_ID = 4            # 4/6=免费额度  5=2 倍消耗  7=5 倍消耗（5/7 需订阅）
VIDEO_DURATION = 15
VIDEO_RATIO_ID = 3            # 3=9:16  4=16:9  5=1:1  6=21:9（竖图用 9:16）
VIDEO_RESOLUTION_ID = 1       # 1=720P  2=1080P（仅 Seedance 2.5 支持）
ACTION_BAR_KEY = "coco_instruction"

SEND_TIMEOUT = 180
WAIT_CREATION_TIMEOUT = 900
POLL_INTERVAL = 10
MAX_AUTO_REPLY = 2

# 无水印清晰度：highest=最高档；也可以写死 "1080p" / "720p"（没有该档自动回退最高档）
NOWM_PREFER = "highest"

CREATION_SCENE = "ai_creation_photo_motion"
AI_CREATION_APP_ID = "db_2UHTeIU"
AI_CREATION_VIDEO_PATH = "/creation/photo-motion"

QUOTA_WORDS = ("额度已用完", "额度不足", "今日视频生成免费额度", "开通订阅畅享")
FAIL_WORDS = ("版权限制", "请更换输入内容", "生成失败", "内容违规", "无法生成", "生成异常")
STARTED = ("预计等待", "已在生成队列", "本次生成将消耗", "生成好了")
PROMPT_WORDS = ("提示词", "复制", "粘贴", "负面", "建议", "参数我给你")


# =========================
# 协议常量
# =========================
APP_NAME = "nova_ai"
AID = "482431"
VERSION_CODE = "15010001"
VERSION_NAME = "15.1.0"
UPDATE_VERSION_CODE = "15010040"
UA = ("com.larus.nova/15010001 (Linux; U; Android 14; zh_CN; LE2120; "
      "Build/UKQ1.231003.002;tt-ok/3.12.13.4)")
HOST = "api-normal.doubao.com"
DEVICE_ID = "1111111111111111"
INSTALL_ID = "2222222222222222"
CDID = "ee3c4d85-c8f0-4c57-8027-1ec83293a5d5"
CHANNEL = "doubao"

CMD_SEND_MESSAGE = 100
CMD_PULL_SINGLE_CHAIN = 3100
CHANNEL_SSE = 3
CHANNEL_HTTP = 2

SERVER_VIDEO_MODEL_OPTIONS = {7: "Seedance 2.5", 5: "Seedance 2.0",
                               4: "Seedance 2.0 Fast", 6: "Seedance 2.0 Mini"}
SERVER_VIDEO_RATIO_OPTIONS = {0: "自动", 1: "3:4", 2: "4:3", 3: "9:16",
                              4: "16:9", 5: "1:1", 6: "21:9"}
VIDEO_PAGE_MODEL_TO_SELECTED = {7: 7, 5: 5, 4: 4, 6: 6}
VIDEO_PAGE_RATIO_TO_SELECTED = {i: i for i in range(7)}
VIDEO_PAGE_DURATION_TO_SELECTED = {i: i for i in range(4, 16)}

_TEXT_RE = re.compile(r'"text"\s*:\s*"((?:[^"\\]|\\.)*)"')
_TEXT_OPEN_RE = re.compile(r'"text"\s*:\s*"((?:[^"\\]|\\.)*)$')

FPLAY_KDF_SALT = base64.b64decode(
    "TdTC5rgxYgkOUrPHpnM7pByyRiuCmrWKGWs521cXdST0m69/COjWjSanLjfBqVovHwWlGJKu8pSXMrYqOKrdWA==")


# =========================
# X-Gorgon / X-Khronos 签名（纯算法）
# =========================
def _key_buf(key_len, heap_ptr):
    return bytes([0x4A, key_len & 0xFF, 0x16, (heap_ptr >> 8) & 0xFF,
                  0x47, 0x6C, (key_len >> 8) & 0xFF, heap_ptr & 0xFF])


def _ksa(key):
    S = list(range(256))
    j = 0
    for i in range(256):
        j = (j + S[i] + key[i % len(key)]) % 256
        S[i] = S[j]
    return S


def _prga(S, data):
    S = list(S)
    out = bytearray()
    i = j = 0
    for b in data:
        i = (i + 1) % 256
        j = (j + S[i]) % 256
        sj = S[j]
        S[i] = sj
        out.append(b ^ S[(sj + sj) % 256])
    return bytes(out)


def _bitrev(b):
    return int(f"{b:08b}"[::-1], 2)


def _mix(buf):
    orig = list(buf)
    n = len(orig)
    res = bytearray(n)
    for i in range(n):
        ns = ((orig[i] & 0xF) << 4) | ((orig[i] >> 4) & 0xF)
        if i + 1 < n:
            val = (ns ^ orig[i + 1]) & 0xFF
        elif n > 1:
            val = (ns ^ res[0]) & 0xFF
        else:
            val = ns
        res[i] = (n ^ (~_bitrev(val) & 0xFF)) & 0xFF
    return bytes(res)


def sign_headers(url, timestamp=None):
    key_len, heap_ptr = 0, 0x9820
    ts = int(timestamp if timestamp is not None else time.time())
    qs = url.split("?", 1)[1] if "?" in url else ""
    h = hashlib.md5(qs.encode()).digest()[:4]
    plain = h + b"\x00" * 8 + bytes.fromhex("00050904") + struct.pack(">I", ts & 0xFFFFFFFF)
    body = _mix(_prga(_ksa(_key_buf(key_len, heap_ptr)), plain))
    header = bytes([0x84, 0x04, heap_ptr & 0xFF, (heap_ptr >> 8) & 0xFF,
                    key_len & 0xFF, (key_len >> 8) & 0xFF])
    return {"X-Gorgon": (header + body).hex(), "X-Khronos": str(ts)}


# =========================
# 小工具
# =========================
def compact_json(obj):
    return json.dumps(obj, ensure_ascii=False, separators=(",", ":"))


def _pick(d, *names):
    if not isinstance(d, dict):
        return None
    for name in names:
        if name in d and d[name] not in (None, ""):
            return d[name]
    return None


def _find_first_key(obj, *names):
    if isinstance(obj, dict):
        for name in names:
            if name in obj and obj[name] not in (None, ""):
                return obj[name]
        for v in obj.values():
            got = _find_first_key(v, *names)
            if got not in (None, ""):
                return got
    elif isinstance(obj, list):
        for v in obj:
            got = _find_first_key(v, *names)
            if got not in (None, ""):
                return got
    return None


def _unescape(s):
    try:
        return json.loads('"%s"' % s)
    except Exception:
        return s


def _safe_json(resp):
    try:
        return resp.json()
    except Exception:
        return None


def _first_url(obj):
    got = _find_first_key(obj, "download_url", "downloadUrl", "DownloadUrl",
                          "main_url", "mainUrl", "MainUrl",
                          "image_url", "imageUrl", "ImageUrl",
                          "preview_url", "previewUrl", "PreviewUrl",
                          "thumb_url", "thumbUrl", "ThumbUrl", "url", "URL", "Url")
    if isinstance(got, str) and got.startswith("http"):
        return got
    if isinstance(got, dict):
        return _first_url(got)
    return ""


def _first_url_in(obj, *paths):
    def get_path(cur, path):
        for key in path:
            if not isinstance(cur, dict):
                return None
            cur = cur.get(key)
        return cur
    for path in paths:
        got = get_path(obj, path if isinstance(path, tuple) else (path,))
        if isinstance(got, str) and got.startswith("http"):
            return got
        if isinstance(got, dict):
            url = _first_url(got)
            if url:
                return url
    return ""


# =========================
# 客户端：请求 / 上传 / 消息链
# =========================
class Client(object):
    _AUTH_CACHE = {}

    def __init__(self, sessionid, bot_id=BOT_ID, conversation_id=""):
        self.sessionid = sessionid
        self.bot_id = bot_id
        self.conversation_id = conversation_id or ""
        self.uid = ""
        self.device_id = DEVICE_ID
        self.install_id = INSTALL_ID
        self.sess = requests.Session()
        self._uid_probing = False

    # ---------- 签名请求 ----------
    def _common(self):
        return (
            "device_platform=android&os=android&ssmix=a"
            "&cdid=%s&channel=%s&aid=%s" % (CDID, CHANNEL, AID)
            + "&app_name=%s&version_code=%s&version_name=%s" % (APP_NAME, VERSION_CODE, VERSION_NAME)
            + "&manifest_version_code=%s&update_version_code=%s" % (VERSION_CODE, UPDATE_VERSION_CODE)
            + "&resolution=1080*2184&dpi=480&device_type=LE2120&device_brand=OnePlus"
            + "&language=zh&os_api=34&os_version=14&ac=wifi"
            + "&uid=%s&iid=%s&device_id=%s" % (self.uid, self.install_id, self.device_id)
        )

    def _cookie(self):
        return "; ".join([
            "install_id=%s" % self.install_id,
            "sessionid=%s" % self.sessionid,
            "sessionid_ss=%s" % self.sessionid,
            "sid_tt=%s" % self.sessionid,
        ])

    def request(self, path, payload, params=None, stream=False, timeout=60, extra_headers=None):
        now_ms = int(time.time() * 1000)
        q = self._common()
        if params:
            q = params + "&" + q
        url = "https://%s%s?%s&_rticket=%d&ts=%d" % (HOST, path, q, now_ms, now_ms // 1000)
        body = json.dumps(payload, separators=(",", ":"), ensure_ascii=False).encode()
        headers = {
            "Host": HOST, "Connection": "keep-alive", "Cookie": self._cookie(),
            "X-OMNI-REQUEST": "1", "sdk-version": "2", "passport-sdk-version": "60592",
            "Content-Type": "application/json; encoding=utf-8", "X-SS-DP": AID,
            "User-Agent": UA, "X-SS-STUB": hashlib.md5(body).hexdigest().upper(),
            "X-SS-REQ-TICKET": str(now_ms), "ttzip-tlb": "1",
            "Accept-Encoding": "gzip, deflate, br, ttzip",
        }
        if extra_headers:
            headers.update(extra_headers)
        headers.update(sign_headers(url))
        return self.sess.post(url, headers=headers, data=body, stream=stream, timeout=timeout)

    # ---------- imagex 上传 ----------
    @staticmethod
    def _aws_v4_headers(ak, sk, token, method, query_pairs, region="cn-north-1",
                        service="imagex"):
        amz_date = time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())
        short_date = amz_date[:8]
        grouped = {}
        for k, v in query_pairs:
            grouped.setdefault(str(k), []).append(str(v))
        parts = []
        for k in sorted(grouped):
            for v in grouped[k]:
                parts.append("%s=%s" % (k, quote(v, safe="-_.~")))
        canonical_query = "&".join(parts)
        signed_headers = "x-amz-date;x-amz-security-token"
        canonical_headers = ("x-amz-date:%s\nx-amz-security-token:%s\n" % (amz_date, token))
        payload_hash = hashlib.sha256(b"").hexdigest()
        canonical_request = "\n".join([method.upper(), "/top/v1", canonical_query,
                                       canonical_headers, signed_headers, payload_hash])
        scope = "%s/%s/%s/aws4_request" % (short_date, region, service)
        string_to_sign = "\n".join([
            "AWS4-HMAC-SHA256", amz_date, scope,
            hashlib.sha256(canonical_request.encode()).hexdigest()])

        def hm(key, msg):
            return hmac.new(key, msg.encode(), hashlib.sha256).digest()

        key = hm(("AWS4" + sk).encode(), short_date)
        key = hm(key, region)
        key = hm(key, service)
        key = hm(key, "aws4_request")
        sig = hmac.new(key, string_to_sign.encode(), hashlib.sha256).hexdigest()
        return {
            "x-amz-date": amz_date,
            "X-Amz-Security-Token": token,
            "Authorization": ("AWS4-HMAC-SHA256 Credential=%s/%s,SignedHeaders=%s,Signature=%s"
                              % (ak, scope, signed_headers, sig)),
        }

    def upload_token(self, scene_id="7", resource_type=2, tenant_id="4"):
        """先走 /alice/resource/prepare_upload；失败再回退 /alice/upload/auth_token。"""
        payload = {"tenant_id": str(tenant_id), "scene_id": str(scene_id),
                   "resource_type": int(resource_type)}
        r = self.request("/alice/resource/prepare_upload", payload, timeout=60)
        j = _safe_json(r) or {}
        prepare_raw = json.dumps(j, ensure_ascii=False)[:600]
        data = j.get("data") if isinstance(j, dict) else None
        auth = (data or {}).get("upload_auth_token") or {}
        tok = {
            "service_id": _pick(data or {}, "service_id", "serviceId"),
            "upload_path_prefix": _pick(data or {}, "upload_path_prefix", "uploadPathPrefix"),
            "upload_host": _pick(data or {}, "upload_host", "uploadHost"),
            "auth": {
                "access_key_id": _pick(auth, "access_key", "accessKey", "access_key_id"),
                "secret_access_key": _pick(auth, "secret_key", "secretKey", "secret_access_key"),
                "session_token": _pick(auth, "session_token", "sessionToken"),
            },
        }
        if tok["service_id"] and tok["upload_host"] and tok["auth"]["access_key_id"]:
            return tok
        r = self.request("/alice/upload/auth_token",
                         {"scene": "chat_input", "data_type": "image"}, timeout=60)
        j = _safe_json(r) or {}
        data = j.get("data") if isinstance(j, dict) else None
        if not isinstance(data, dict):
            raise RuntimeError("上传凭证获取失败（多半是 sessionid 过期/无效）\n"
                               "  prepare_upload: %s\n  auth_token: %s"
                               % (prepare_raw, json.dumps(j, ensure_ascii=False)[:600]))
        host = _pick(data, "upload_host", "uploadHost")
        auth = data.get("auth") or {}
        tok = {
            "service_id": _pick(data, "service_id", "serviceId"),
            "upload_path_prefix": _pick(data, "upload_path_prefix", "uploadPathPrefix"),
            "upload_host": host,
            "auth": {
                "access_key_id": _pick(auth, "access_key", "accessKey", "access_key_id"),
                "secret_access_key": _pick(auth, "secret_key", "secretKey", "secret_access_key"),
                "session_token": _pick(auth, "session_token", "sessionToken"),
            },
        }
        if not (tok["upload_host"] and tok["auth"]["access_key_id"]):
            raise RuntimeError("拿不到上传凭证: %s" % json.dumps(j, ensure_ascii=False)[:800])
        return tok

    def imagex_top(self, token, action, extra, region="cn-north-1",
                   service="imagex", method="GET"):
        auth = token.get("auth") or {}
        host = _pick(token, "upload_host", "uploadHost")
        service_id = _pick(token, "service_id", "serviceId")
        query = [("Action", action), ("Version", "2018-08-01")]
        if service_id:
            query.append(("ServiceId", service_id))
        query.extend(extra)
        headers = self._aws_v4_headers(
            auth.get("access_key_id") or "", auth.get("secret_access_key") or "",
            auth.get("session_token") or "", method, query, region, service)
        url = "https://%s/top/v1?%s" % (host, urlencode(query))
        r = self.sess.get(url, headers=headers, timeout=60) if method == "GET" else \
            self.sess.post(url, headers=headers, data=b"", timeout=60)
        j = _safe_json(r)
        if j is None:
            raise RuntimeError("%s 非 JSON: HTTP %s %s" % (action, r.status_code, r.text[:600]))
        return j

    def imagex_apply(self, token, file_ext, file_size):
        """ApplyImageUpload：先按 App 风格，失败再按 fallback 风格。"""
        prefix = _pick(token, "upload_path_prefix", "uploadPathPrefix") or ""
        ext = file_ext if file_ext.startswith(".") else "." + file_ext
        styles = [[("device_platform", "Android"), ("FileType", "image"),
                   ("UploadNum", "1"), ("Prefix", prefix), ("FileExtension", ext)],
                  [("NeedFallback", "true"), ("FileSize", str(file_size)),
                   ("FileExtension", ext), ("s", uuid.uuid4().hex[:10])],
                  [("device_platform", "Android"), ("FileType", "image"), ("UploadNum", "1")]]
        errors = []
        for extra in styles:
            try:
                resp = self.imagex_top(token, "ApplyImageUpload", extra)
                if _find_first_key(resp, "UploadHost", "UploadNodes", "InnerUploadAddress"):
                    return resp
                errors.append(json.dumps(resp, ensure_ascii=False)[:300])
            except Exception as e:
                errors.append(str(e)[:300])
        raise RuntimeError("ApplyImageUpload 全部失败: %s" % " | ".join(errors))

    def imagex_upload_file(self, apply_resp, file_path):
        data = open(file_path, "rb").read()
        file_md5 = hashlib.md5(data).hexdigest()
        result = apply_resp.get("Result") or {}
        inner = result.get("InnerUploadAddress") or {}
        node = (inner.get("UploadNodes") or [{}])[0]
        source = node or result.get("UploadAddress") or {}
        store = (source.get("StoreInfos") or [{}])[0]
        host = source.get("UploadHost") or (source.get("UploadHosts") or [None])[0]
        store_key = store.get("StoreUri")
        auth = store.get("Auth")
        upload_id = store.get("UploadID")
        if not host or not store_key:
            raise RuntimeError("Apply 里找不到 UploadHost/StoreKey: %s"
                               % json.dumps(apply_resp, ensure_ascii=False)[:800])
        crc = "%08x" % (zlib.crc32(data) & 0xffffffff)
        headers = {
            "Content-Type": "application/octet-stream",
            "X-Upload-Content-Length": str(len(data)),
            "X-Upload-Content-CRC32": crc,
            "X-Upload-Content-Range": "bytes 0-%d/%d" % (len(data) - 1, len(data)),
        }
        if auth:
            headers["Authorization"] = str(auth)
        if upload_id:
            transfer_url = ("https://%s/upload/v1/%s?uploadid=%s&device_type=mobile"
                            "&part_number=1&phase=transfer&part_offset=0"
                            % (host, quote(store_key, safe="/"), quote(upload_id, safe="")))
            self.sess.post(transfer_url, headers=headers, data=data, timeout=120)
            finish_url = ("https://%s/upload/v1/%s?uploadmode=part&phase=finish"
                          "&uploadid=%s&device_type=mobile"
                          % (host, quote(store_key, safe="/"), quote(upload_id, safe="")))
            fh = {"Content-Type": "text/plain"}
            if auth:
                fh["Authorization"] = str(auth)
            finish = self.sess.post(finish_url, headers=fh,
                                    data=("1:%s" % crc).encode(), timeout=120)
            return {"store_key": store_key, "md5": file_md5,
                    "text": finish.text[:800], "json": _safe_json(finish)}
        url = "https://%s/upload/v1/%s" % (host, quote(store_key, safe="/"))
        r = self.sess.post(url, headers=headers, data=data, timeout=120)
        return {"store_key": store_key, "md5": file_md5,
                "text": r.text[:800], "json": _safe_json(r)}

    def imagex_commit(self, token, apply_resp):
        extra = [("device_platform", "android")]
        session_key = _find_first_key(apply_resp, "SessionKey", "session_key")
        if session_key:
            extra.append(("SessionKey", str(session_key)))
        return self.imagex_top(token, "CommitImageUpload", extra, method="POST")

    def upload_image(self, file_path, scene_id="7"):
        """上传 + 注册，返回 {"uri","width","height","md5"}。"""
        if not os.path.exists(file_path):
            raise FileNotFoundError(file_path)
        ext = os.path.splitext(file_path)[1] or ".jpg"
        token = self.upload_token(scene_id=scene_id)
        apply_resp = self.imagex_apply(token, ext, os.path.getsize(file_path))
        upload_resp = self.imagex_upload_file(apply_resp, file_path)
        commit_resp = self.imagex_commit(token, apply_resp)
        uri = (_find_first_key(commit_resp, "Uri", "StoreUri", "StoreKey", "ImageUri",
                               "ImageTosKey", "oid")
               or upload_resp.get("store_key") or "")
        if not uri:
            raise RuntimeError("上传成功但没拿到 uri: %s"
                               % json.dumps(commit_resp, ensure_ascii=False)[:800])
        plugin = ((commit_resp.get("Result") or {}).get("PluginResult") or [{}])[0]
        item = {
            "uri": uri,
            "width": int(plugin.get("ImageWidth") or 0),
            "height": int(plugin.get("ImageHeight") or 0),
            "md5": plugin.get("ImageMd5") or upload_resp.get("md5") or "",
        }
        self.register_resource(uri, **{k: item[k] for k in ("width", "height", "md5")})
        return item

    def register_resource(self, uri, width=0, height=0, md5=""):
        """上传后必须注册，否则服务端解析不到 uri。"""
        data = {"identifier": str(uuid.uuid4())}
        if md5:
            data["md5"] = md5
        if width or height:
            data["image_ori"] = {"width": int(width or 0), "height": int(height or 0)}
        data["metadata"] = {"is_marked": "0"}
        payload = {
            "extra": json.dumps({"bot_id": self.bot_id, "conversation_id": "",
                                 "device_id": self.device_id,
                                 "local_message_id": str(uuid.uuid4())},
                                separators=(",", ":")),
            "resource_list": [{"meta": {"image_meta": {"data": data}},
                               "resource_type": 2, "uri": uri}],
            "scene_id": "7",
            "tenant_id": "4",
        }
        r = self.request("/alice/resource/register", payload, timeout=60)
        if r.status_code >= 400:
            raise RuntimeError("resource/register HTTP %s: %s" % (r.status_code, r.text[:600]))

    # ---------- 消息链 ----------
    def pull_messages(self, conversation_id, anchor_index=0, limit=30, direction=1):
        payload = {
            "cmd": CMD_PULL_SINGLE_CHAIN, "sequence_id": str(uuid.uuid4()),
            "channel": CHANNEL_HTTP, "version": "1",
            "uplink_body": {"pull_singe_chain_uplink_body": {
                "conversation_id": conversation_id, "conversation_type": 3,
                "direction": direction, "anchor_index": anchor_index,
                "limit": limit, "ext": {}}},
        }
        r = self.request("/im/chain/cmd", payload, params="flow_im_arch=v2")
        return _safe_json(r) or {}

    def pull_raw(self, conversation_id, limit=30):
        j = self.pull_messages(conversation_id, limit=limit)
        msgs = (((j.get("downlink_body") or {}).get("pull_singe_chain_downlink_body")
                 or {}).get("messages") or [])
        msgs.sort(key=lambda m: int(m.get("index_in_conv", 0) or 0))
        return msgs

    @staticmethod
    def _content_text(s):
        if not isinstance(s, str) or not s:
            return None
        s = s.strip()
        if s.startswith("{"):
            try:
                j = json.loads(s)
                if isinstance(j, dict):
                    t = j.get("text")
                    return t if isinstance(t, str) else ""
            except Exception:
                pass
            m = _TEXT_RE.search(s) or _TEXT_OPEN_RE.search(s)
            return _unescape(m.group(1)) if m else None
        if s.startswith("["):
            try:
                j = json.loads(s)
                if isinstance(j, list):
                    parts = []
                    for blk in j:
                        if not isinstance(blk, dict):
                            continue
                        tb = (blk.get("content") or {}).get("text_block") or {}
                        if isinstance(tb.get("text"), str):
                            parts.append(tb["text"])
                    return "".join(parts)
            except Exception:
                pass
            m = _TEXT_RE.search(s) or _TEXT_OPEN_RE.search(s)
            return _unescape(m.group(1)) if m else None
        return None

    @staticmethod
    def msg_text(m):
        out = []
        for blk in (m.get("content_block") or []):
            tb = (blk.get("content") or {}).get("text_block") or {}
            if tb.get("text"):
                out.append(tb["text"])
        if out:
            return "".join(out)
        c = m.get("content")
        if isinstance(c, str) and c:
            t = Client._content_text(c)
            if t is not None:
                return t
            if c not in ("{}", "[]"):
                return c
        return ""

    @staticmethod
    def parse_creations(m):
        out = []
        blocks = []
        c = m.get("content")
        if isinstance(c, str) and c.strip().startswith("["):
            try:
                blocks.extend(json.loads(c))
            except Exception:
                pass
        blocks.extend(m.get("content_block") or [])
        for b in blocks:
            if not isinstance(b, dict):
                continue
            cbs = (b.get("content") or {}).get("creation_block") or {}
            for cr in (cbs.get("creations") or []):
                item = {"creation_id": cr.get("id"), "type": cr.get("type")}
                v = cr.get("video") or {}
                if v:
                    item["vid"] = v.get("vid")
                    item["duration"] = v.get("duration")
                    item["cover"] = ((v.get("cover") or {}).get("image_preview") or {}).get("url")
                    item["url"] = v.get("download_url")
                    item["full_url"] = item["url"]
                    item["video_model"] = v.get("video_model")
                elif cr.get("image"):
                    img = cr.get("image") or {}
                    item["url"] = _first_url_in(img, ("image_preview", "url"),
                                                ("image_thumb", "url"),
                                                "image_preview", "image_thumb") or _first_url(img)
                    item["full_url"] = _first_url_in(
                        img, "download_url", "downloadUrl", "DownloadUrl",
                        ("image_ori_raw", "url"), ("image_ori", "url"),
                        "image_ori_raw", "image_ori", "main_url", "MainUrl") or item["url"]
                    item["cover"] = item["url"]
                if not item.get("url"):
                    item["url"] = _first_url(cr)
                    if item["url"]:
                        item["cover"] = item["url"]
                if not item.get("full_url"):
                    item["full_url"] = _first_url_in(
                        cr, "download_url", "downloadUrl", "DownloadUrl",
                        "image_ori_raw", "image_ori", "main_url", "MainUrl") \
                        or item.get("url") or item.get("cover") or ""
                out.append(item)
        return out

    def wait_creations(self, conversation_id, since_index=0, timeout=900, interval=10,
                       fail_words=()):
        """轮询成片；机器人明确回失败/违规时直接抛错，别空等到超时。"""
        start = time.time()
        deadline = start + timeout
        last_report = 0
        newest = since_index
        while time.time() < deadline:
            got = []
            for m in self.pull_raw(conversation_id, limit=20):
                idx = int(m.get("index_in_conv", 0) or 0)
                newest = max(newest, idx)
                if idx <= since_index:
                    continue
                got.extend(self.parse_creations(m))
                if int(m.get("user_type", 0) or 0) != 2:
                    continue
                text = self.msg_text(m)
                if text and any(w in text for w in fail_words):
                    raise RuntimeError(text.strip())
            if got:
                return got
            elapsed = int(time.time() - start)
            if elapsed - last_report >= 30:
                last_report = elapsed
                print("[*] 等待成片 %ds …（最新消息 index=%s）" % (elapsed, newest),
                      flush=True)
            time.sleep(interval)
        return []

    # ---------- uid ----------
    def _adopt_uid(self, conversation_id):
        if not conversation_id:
            return
        try:
            for m in self.pull_raw(conversation_id, limit=20):
                if int(m.get("user_type", 0) or 0) == 1 and m.get("sender_id"):
                    self.uid = str(m["sender_id"])
                    return
        except Exception:
            pass

    # ---------- 发送（老接口） ----------
    def send_message(self, text, conversation_id="", local_conv_id="", timeout=180,
                     ext=None, extra_body=None):
        # uid 拿不到会被当未登录、SSE 不推数据：先发一句探测（会创建一个会话）
        if not self.uid and not self._uid_probing:
            self._uid_probing = True
            try:
                probe = self.send_message("你好", conversation_id="", timeout=90)
                conv = (probe.get("ack") or {}).get("conversation_id") or ""
                if conv:
                    self._adopt_uid(conv)
            except Exception:
                pass
            finally:
                self._uid_probing = False

        body = {
            "conversation_id": conversation_id,
            "conversation_type": 3,
            "sender_id": self.uid,
            "content_type": 1,
            "content": json.dumps({"text": text}, ensure_ascii=False),
            "local_message_id": str(uuid.uuid4()),
            "local_conversation_id": local_conv_id or
            "main_%s_%s-local" % (uuid.uuid4(), self.bot_id),
            "bot_id": self.bot_id,
            "unique_key": "%s_%s" % (self.uid, uuid.uuid4()),
            "ext": dict(ext or {}),
            "bot_type": 0,
            "status": 0,
        }
        if extra_body:
            body.update(extra_body)
        payload = {"cmd": CMD_SEND_MESSAGE, "sequence_id": str(uuid.uuid4()),
                   "channel": CHANNEL_SSE, "version": "1",
                   "uplink_body": {"send_message_body": body}}
        r = self.request("/im/sse/send/message", payload,
                         params="flow_im_arch=v2", stream=True, timeout=timeout)

        events = []
        ack, reply, bot_msg_id = None, "", None
        for line in r.iter_lines(decode_unicode=True):
            if not line or not line.startswith("data:"):
                continue
            try:
                j = json.loads(line[5:].strip())
            except Exception:
                continue
            if not isinstance(j, dict):
                continue
            events.append(j)
            dl = j.get("downlink_body") or {}
            a = dl.get("send_message_ack_downlink_body")
            if a:
                ack = a
            msg = (dl.get("new_message_notify") or {}).get("message") or {}
            if msg.get("user_type") == 2 and bot_msg_id is None:
                bot_msg_id = msg.get("message_id")
                t = self.msg_text(msg)
                if t:
                    reply = t
            chunk = dl.get("fetch_chunk_message_downlink_body")
            if chunk and (bot_msg_id is None or chunk.get("message_id") == bot_msg_id):
                t = self.msg_text(chunk)
                if t:
                    # 服务端有时推"累积快照"而不是增量：相同丢弃、包含则替换、否则追加
                    if t == reply:
                        pass
                    elif reply and t.startswith(reply):
                        reply = t
                    else:
                        reply += t

        if not events:
            return {"status_code": None, "ack": None, "reply": "", "creations": [],
                    "status_desc": "SSE 无数据（HTTP %s）" % r.status_code}
        if ack and ack.get("conversation_id"):
            self.conversation_id = ack["conversation_id"]

        creations = []
        for e in events:
            dl = e.get("downlink_body") or {}
            m = (dl.get("new_message_notify") or {}).get("message") or {}
            if m:
                creations.extend(self.parse_creations(m))
            ch = dl.get("fetch_chunk_message_downlink_body")
            if ch:
                creations.extend(self.parse_creations(ch))
        return {"status_code": events[0].get("status_code"),
                "status_desc": events[0].get("status_desc") or "",
                "ack": ack, "reply": reply, "events": events, "creations": creations}


# =========================
# actionbar：拉视频指令 + 收敛选择器
# =========================
def fetch_actionbar(client, bot_id=BOT_ID):
    payload = {"language_code": "zh", "bot_id": str(bot_id), "conversation_id": ""}
    r = client.request("/alice/bot/action_bar_v3/list", payload, timeout=60)
    j = _safe_json(r) or {}
    if r.status_code != 200 or j.get("code") not in (0, None):
        raise RuntimeError("action_bar_v3/list failed: %s"
                           % json.dumps(j, ensure_ascii=False)[:1500])
    return j


def iter_nodes(obj):
    yield obj
    if isinstance(obj, str):
        s = obj.strip()
        if s.startswith(("{", "[")):
            try:
                yield from iter_nodes(json.loads(s))
            except Exception:
                return
        return
    if isinstance(obj, dict):
        for v in obj.values():
            yield from iter_nodes(v)
    elif isinstance(obj, list):
        for v in obj:
            yield from iter_nodes(v)


def text_of(obj):
    if not isinstance(obj, dict):
        return ""
    keys = ("title", "name", "text", "display_text", "label", "desc", "description",
            "sub_title", "placeholder", "starling_name", "key", "type", "value")
    return " ".join(str(obj[k]) for k in keys if isinstance(obj.get(k), (str, int, float)))


def find_video_conf(actionbar_json):
    fallback = None
    for node in iter_nodes(actionbar_json):
        if not isinstance(node, dict):
            continue
        conf = node.get("instruction_conf") or node.get("instructionConf")
        if not isinstance(conf, dict):
            continue
        try:
            # 优先精确命中视频叶子节点（18），避免拿到父级「AI 创作」(28)
            if int(conf.get("instruction_type")) == 18:
                return json.loads(json.dumps(conf, ensure_ascii=False, default=str))
        except (TypeError, ValueError):
            pass
        if fallback is None:
            ctx = (text_of(node)
                   + json.dumps(conf, ensure_ascii=False, default=str)[:4000]).lower()
            if "seedance" in ctx and "video-ratio" in ctx:
                fallback = json.loads(json.dumps(conf, ensure_ascii=False, default=str))
    return fallback


def decode_tpl(v):
    if isinstance(v, str):
        try:
            return json.loads(v)
        except Exception:
            return v
    return v


def encode_tpl(v):
    return compact_json(v) if isinstance(v, (dict, list)) else v


def apply_selection(node, option_id):
    if not isinstance(node, dict) or option_id is None:
        return
    options = node.get("option_list")
    if not isinstance(options, list):
        return
    for i, opt in enumerate(options):
        if isinstance(opt, dict):
            opt.update({"selected": 0, "is_selected": False,
                        "selected_status": 0, "status": 0})
        if not isinstance(opt, dict):
            continue
        if str(opt.get("id")) == str(option_id):
            opt.update({"selected": 1, "is_selected": True,
                        "selected_status": 1, "status": 1})
            node.update({
                "default_selection_id": opt.get("id"), "default_selection_index": i,
                "current_selection_id": opt.get("id"),
                "selected_option_id": opt.get("id"), "selected_id": opt.get("id"),
                "value": opt.get("id"), "current_selection_index": i,
                "selected_display_text": opt.get("selected_display_text") or opt.get("display_text"),
                "selected_option_key": opt.get("option_key"),
            })
            return


def patch_selectors(conf, selected):
    """模型/比例/时长收敛成"已选中"形态，参考图组件原样保留。"""
    out = json.loads(json.dumps(conf, ensure_ascii=False, default=str))
    model_id = selected.get("selected_model")
    ratio_id = selected.get("selected_ratio")
    duration_id = selected.get("selected_duration")
    resolution_id = selected.get("selected_resolution")
    final_items = []
    for item in out.get("instruction_item_list") or []:
        probe = decode_tpl(item.get("template"))
        if isinstance(probe, dict) and probe.get("media_type") is not None:
            final_items.append(item)
            continue
        if not isinstance(probe, dict) or not isinstance(probe.get("selector_list"), list):
            continue
        selectors_out = []
        for selector in probe.get("selector_list") or []:
            st = decode_tpl(selector.get("template"))
            if not isinstance(st, dict):
                continue
            if str(st.get("label") or "") == "玩法" or int(selector.get("item_type") or 0) == 8:
                continue
            label = str(st.get("label") or "")
            opts = st.get("option_list") or []
            if label == "模型" or any("Seedance" in str(o.get("display_text") or "")
                                     for o in opts if isinstance(o, dict)):
                apply_selection(st, model_id)
                if model_id is not None and isinstance(st.get("option_list"), list):
                    st["option_list"] = [o for o in st["option_list"]
                                         if isinstance(o, dict) and str(o.get("id")) == str(model_id)]
                selectors_out.append({"id": selector.get("id") or st.get("id") or 6,
                                      "item_type": selector.get("item_type") or 3,
                                      "template": encode_tpl(st)})
                continue
            configs = st.get("configs")
            if isinstance(configs, dict):
                if model_id is not None and isinstance(configs.get(str(model_id)), dict):
                    st["configs"] = configs = {str(model_id): configs[str(model_id)]}
                for key in ([str(model_id)] if str(model_id) in configs else list(configs.keys())):
                    config = configs.get(key)
                    if not isinstance(config, dict):
                        continue
                    for sub in config.get("selectors") or []:
                        st2 = decode_tpl(sub.get("template"))
                        if not isinstance(st2, dict):
                            continue
                        sub_label = str(st2.get("label") or "")
                        if sub_label == "比例" or st2.get("key") == "video-ratio":
                            apply_selection(st2, ratio_id)
                            if ratio_id is not None and isinstance(st2.get("option_list"), list):
                                st2["option_list"] = [o for o in st2["option_list"]
                                                      if isinstance(o, dict) and str(o.get("id")) == str(ratio_id)]
                            sub.clear()
                            sub.update({
                                "type": sub.get("type", 1),
                                "template": encode_tpl(st2),
                                "dropdown_box": st2,
                                "id": st2.get("id") or 1,
                                "label": st2.get("label"),
                                "key": st2.get("key") or "video-ratio",
                                "option_list": st2.get("option_list"),
                                "default_selection_index": st2.get("default_selection_index"),
                                "default_selection_id": st2.get("default_selection_id"),
                                "can_be_empty": st2.get("can_be_empty"),
                                "need_save": st2.get("need_save"),
                                "display_column": st2.get("display_column"),
                            })
                        elif sub_label == "时长" or st2.get("key") == "video-duration":
                            dur = {
                                "id": st2.get("id") or 5, "label": st2.get("label"),
                                "key": st2.get("key") or "video-duration",
                                "lower_bound": st2.get("lower_bound"),
                                "upper_bound": st2.get("upper_bound"),
                                "step_length": st2.get("step_length") or 1,
                                "should_show_dots": st2.get("should_show_dots"),
                                "default_selected_duration": duration_id,
                                "selected_duration": duration_id,
                                "can_be_empty": st2.get("can_be_empty"),
                                "need_save": st2.get("need_save"),
                                "tag_starting_duration": st2.get("tag_starting_duration"),
                                "display_starling": st2.get("display_starling"),
                                "message_starling": st2.get("message_starling"),
                            }
                            dur = {k: v for k, v in dur.items() if v is not None}
                            sub.clear()
                            sub.update({
                                "type": sub.get("type", 2),
                                "template": encode_tpl(dur),
                                "duration_seek_bar_selector": dur,
                                "id": dur.get("id") or 5,
                                "label": dur.get("label"),
                                "key": dur.get("key") or "video-duration",
                                "lower_bound": dur.get("lower_bound"),
                                "upper_bound": dur.get("upper_bound"),
                                "step_length": dur.get("step_length"),
                                "should_show_dots": dur.get("should_show_dots"),
                                "default_selected_duration": duration_id,
                                "selected_duration": duration_id,
                                "can_be_empty": dur.get("can_be_empty"),
                                "need_save": dur.get("need_save"),
                                "tag_starting_duration": dur.get("tag_starting_duration"),
                                "display_starling": dur.get("display_starling"),
                                "message_starling": dur.get("message_starling"),
                            })
                        elif sub_label == "分辨率" or st2.get("key") == "video-resolution":
                            if resolution_id is not None:
                                apply_selection(st2, resolution_id)
                                if isinstance(st2.get("option_list"), list):
                                    st2["option_list"] = [o for o in st2["option_list"]
                                                          if isinstance(o, dict) and str(o.get("id")) == str(resolution_id)]
                            res = {
                                "id": st2.get("id") or 7, "label": st2.get("label"),
                                "key": st2.get("key") or "video-resolution",
                                "option_list": st2.get("option_list"),
                                "default_selection_id": st2.get("default_selection_id"),
                                "current_selection_id": st2.get("current_selection_id"),
                                "selected_option_id": st2.get("selected_option_id"),
                                "selected_id": st2.get("selected_id"),
                                "value": st2.get("value"),
                                "can_be_empty": st2.get("can_be_empty"),
                                "need_save": st2.get("need_save"),
                            }
                            res = {k: v for k, v in res.items() if v is not None}
                            sub.clear()
                            sub.update({
                                "type": sub.get("type", 1),
                                "template": encode_tpl(res),
                                "dropdown_box": res,
                                "id": res.get("id") or 7,
                                "label": res.get("label"),
                                "key": res.get("key") or "video-resolution",
                                "option_list": res.get("option_list"),
                                "default_selection_id": res.get("default_selection_id"),
                                "current_selection_id": res.get("current_selection_id"),
                                "selected_option_id": res.get("selected_option_id"),
                                "selected_id": res.get("selected_id"),
                                "value": res.get("value"),
                            })
                st["active_config_key"] = str(model_id) if model_id is not None else None
                selectors_out.append({"id": selector.get("id") or 2,
                                      "item_type": selector.get("item_type") or 9,
                                      "template": encode_tpl(st)})
        if selectors_out:
            final_items.append({
                "id": item.get("id", 2),
                "instruction_item_type": item.get("instruction_item_type", 8),
                "sub_title": item.get("sub_title", ""),
                "template": encode_tpl({"selector_list": selectors_out}),
                "enable_bottom_line": item.get("enable_bottom_line", True),
                "cancel_top_margin": item.get("cancel_top_margin", False),
                "margin_top": item.get("margin_top", 0),
            })
    out["instruction_item_list"] = final_items
    return out


def normalize_video_options(model, duration, ratio, resolution):
    if model not in VIDEO_PAGE_MODEL_TO_SELECTED:
        raise SystemExit("模型 id=%s 不在可用范围: %s"
                         % (model, SERVER_VIDEO_MODEL_OPTIONS))
    if ratio not in VIDEO_PAGE_RATIO_TO_SELECTED:
        raise SystemExit("比例 id=%s 不在可用范围: %s"
                         % (ratio, SERVER_VIDEO_RATIO_OPTIONS))
    if not 4 <= int(duration) <= 15:
        raise SystemExit("时长必须在 4-15 秒之间: %s" % duration)
    return {"selected_model": int(model), "selected_duration": int(duration),
            "selected_ratio": int(ratio), "selected_resolution": int(resolution)}


# =========================
# 参考图注入 / 指令构造
# =========================
def build_media_attachment(uri, width, height, url=None):
    return {"url": url or uri, "uri": uri,
            "image_upload_info": {"width": int(width or 0), "height": int(height or 0)},
            "ai_creation_image": False}


def inject_reference_image(conf, attachments):
    items = conf.get("instruction_item_list") or []
    for item in items:
        if item.get("instruction_item_type") != 15:
            continue
        tpl = decode_tpl(item.get("template"))
        tpl = tpl if isinstance(tpl, dict) else {}
        max_num = int(tpl.get("max_num") or 0)
        if max_num and len(attachments) > max_num:
            raise RuntimeError("参考图最多 %d 张，当前 %d 张" % (max_num, len(attachments)))
        tpl["media_attachment_list"] = attachments
        item["template"] = compact_json(tpl)
        return conf
    raise RuntimeError("actionbar 配置里没有 instruction_item_type=15 的参考图项")


def build_instruction(instruction_conf, prompt, images, selected):
    conf = patch_selectors(instruction_conf, selected)
    creation_type = 7 if images else 6
    conf.update({
        "creation_type": creation_type, "task_type": creation_type,
        "prompt": prompt, "creation_prompt": prompt,
        "ai_creation_app_id": AI_CREATION_APP_ID,
        "ai_creation_applet_path": AI_CREATION_VIDEO_PATH,
        "from_ai_creation_applet": "1", "ai_creation_applet_is_root_page": "0",
        "scene": CREATION_SCENE, "txt_scene": CREATION_SCENE,
        "enter_method": "ai_creation_start_create_video",
    })
    box = conf.setdefault("input_box_content", {})
    box["user_input_content"] = prompt
    box["content"] = prompt
    if images:
        inject_reference_image(conf, [
            build_media_attachment(i["uri"], i.get("width"), i.get("height"), i.get("url"))
            for i in images])
    return conf


def build_ext(conf, prompt, selected, suffix, new_conversation=None):
    if new_conversation is None:
        new_conversation = not CONVERSATION_ID
    ext = {
        "scene": CREATION_SCENE, "txt_scene": CREATION_SCENE,
        "enter_method": "ai_creation_start_create_video",
        "previous_page": "/creation/home",
        "ai_creation_app_id": AI_CREATION_APP_ID,
        "ai_creation_applet_path": AI_CREATION_VIDEO_PATH,
        "from_ai_creation_applet": "1",
        "action_bar_key": ACTION_BAR_KEY,
        "action_bar_instruction_type": str(int(conf.get("instruction_type") or 18)),
        "action_bar_instruction": compact_json(conf),
        "is_manual_input": "false",
        "custom_suffix": suffix,
        "actionbar_instruction_prompt": prompt,
        "creation_remote_video_prompt": prompt,
        "creation_remote_video_direct_send": "1",
    }
    if new_conversation:
        ext["force_new_chat"] = "1"
        ext["sub_conv_firstmet_type"] = "1"
    ext.update({k: str(v) for k, v in selected.items()})
    return ext


# =========================
# 无水印直链（可选，失败不影响出片）
# =========================
def no_watermark_urls(video_model, prefer=None):
    """解无水印直链，返回 [{"url","definition","codec","bitrate",...}]。

    prefer：highest（默认，取最高清晰度）/ "1080p" / "720p" 等；
    同一清晰度优先 h264，其次按码率从高到低。
    """
    prefer = str(prefer or NOWM_PREFER or "highest").lower()
    try:
        from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes
    except Exception:
        return []
    vm = json.loads(video_model) if isinstance(video_model, str) else (video_model or {})
    api = vm.get("fallback_api") or ""
    if "key_seed" not in api:
        return []
    from urllib.parse import parse_qsl, urlsplit, urlunsplit
    sp = urlsplit(api)
    q = [(k, v) for k, v in parse_qsl(sp.query, keep_blank_values=True)
         if k not in ("force_fids", "logo_type", "codec_type", "stream_type")]
    q += [("codec_type", "1"), ("stream_type", "hd")]
    try:
        data = ((requests.get(urlunsplit((sp.scheme, sp.netloc, sp.path, urlencode(q),
                                          sp.fragment)), timeout=30)
                 .json().get("video_info") or {}).get("data") or {})
    except Exception:
        return []
    seed = data.get("key_seed") or ""
    vlist = data.get("video_list") or {}

    def b64d(v):
        s = str(v or "").replace("-", "+").replace("_", "/")
        s += "=" * (-len(s) % 4)
        return base64.b64decode(s)

    def dec(raw):
        ct = b64d(raw)[4:]
        if not ct:
            return ""
        derived = hashlib.sha512(hashlib.sha512(b64d(seed)).digest()
                                 + FPLAY_KDF_SALT).digest()
        d = Cipher(algorithms.AES(derived[:16]), modes.CBC(derived[16:32])).decryptor()
        plain = d.update(ct) + d.finalize()
        pad = plain[-1] if plain else 0
        if 1 <= pad <= 16 and plain[-pad:] == bytes([pad]) * pad:
            plain = plain[:-pad]
        return plain.decode("utf-8", "replace").strip()

    def rank(item):
        m = re.match(r"(\d+)", item["definition"])
        return int(m.group(1)) if m else 0

    items = []
    for name, info in vlist.items():
        if not isinstance(info, dict):
            continue
        for k in ("main_url", "backup_url_1"):
            if not info.get(k):
                continue
            try:
                u = dec(info[k])
            except Exception:
                u = ""
            if not u:
                continue
            items.append({
                "url": u,
                "definition": str(info.get("definition") or ""),
                "codec": str(info.get("codec_type") or ""),
                "bitrate": int(info.get("bitrate") or 0),
                "width": int(info.get("vwidth") or 0),
                "height": int(info.get("vheight") or 0),
                "source": str(name),
            })
    if not items:
        return []

    if prefer not in ("highest", "best"):
        hit = [i for i in items if i["definition"].lower() == prefer]
        if hit:
            items = hit
        else:
            print("[!] 没有 %s 档，回退最高档" % prefer, flush=True)

    best = max(rank(i) for i in items)
    items = [i for i in items if rank(i) == best]
    # 同档：h264 兼容性最好放前面，其余按码率从高到低
    items.sort(key=lambda i: (i["codec"] != "h264", -i["bitrate"]))
    return items


def print_creation(cr):
    print("[%s] creation_id=%s" % ("视频" if cr.get("type") == 2 else "图片",
                                   cr.get("creation_id")))
    if cr.get("duration"):
        print("    时长 %.1fs   封面 %s" % (cr["duration"], cr.get("cover") or ""))
    if cr.get("url"):
        print("    带水印 %s" % cr["url"])
    if cr.get("video_model"):
        for u in no_watermark_urls(cr["video_model"]):
            print("    无水印 [%s][%s %dkbps] %s" % (
                u["definition"] or "?", u["codec"] or "?",
                u["bitrate"] // 1000, u["url"]))


# =========================
# 主流程
# =========================
def main():
    dry = "--dry" in sys.argv

    client = Client(SESSIONID, bot_id=BOT_ID, conversation_id=CONVERSATION_ID)

    images = []
    for path in LOCAL_IMAGE_PATHS:
        if dry:
            images.append({"uri": "tos-cn-i-a9rns2rl98/DRY_RUN.jpeg",
                           "width": 0, "height": 0, "url": ""})
            continue
        print("[*] uploading image:", path)
        item = client.upload_image(path)
        print("[*] image uri:", item["uri"], "size:", item["width"], "x", item["height"])
        images.append({"uri": item["uri"], "width": item["width"],
                       "height": item["height"], "url": ""})

    instruction_conf = find_video_conf(fetch_actionbar(client, bot_id=BOT_ID))
    if instruction_conf is None:
        raise SystemExit("服务端没有下发视频指令（instruction_type=18）")
    selected = normalize_video_options(VIDEO_MODEL_ID, VIDEO_DURATION,
                                       VIDEO_RATIO_ID, VIDEO_RESOLUTION_ID)
    suffix = uuid.uuid4().hex
    local_conv_id = "main_%s_%s-local%s" % (uuid.uuid4(), BOT_ID, suffix)

    conf = build_instruction(instruction_conf, PROMPT, images, selected)
    ext = build_ext(conf, PROMPT, selected, suffix)
    extra_body = {"biz_ext": {"custom_suffix": suffix}, "conversation_scene": 0}

    print("[*] 老接口 /im/sse/send/message")
    print("    prompt:", PROMPT)
    print("    model:", VIDEO_MODEL_ID, "duration:", VIDEO_DURATION,
          "ratio:", VIDEO_RATIO_ID, "resolution:", VIDEO_RESOLUTION_ID)
    print("    instruction_type:", ext["action_bar_instruction_type"],
          "| creation_type:", conf.get("creation_type"))
    print("    image count:", len(images), "| local_conversation_id:", local_conv_id)

    if dry:
        print(json.dumps({"ext": ext, "extra_body": extra_body},
                         ensure_ascii=False, indent=1)[:8000])
        return

    out = client.send_message(PROMPT, conversation_id=CONVERSATION_ID,
                              local_conv_id=local_conv_id, ext=ext,
                              extra_body=extra_body, timeout=SEND_TIMEOUT)
    ack = out.get("ack") or {}
    conv = str(ack.get("conversation_id") or CONVERSATION_ID or "")
    reply = out.get("reply") or ""
    creations = out.get("creations") or []

    print("[*] status:", out.get("status_code"), out.get("status_desc") or "")
    print("[*] conversation:", conv, "| ack message_index:", ack.get("message_index"))
    if reply:
        print("[*] bot:", reply[:300])

    if any(w in reply for w in QUOTA_WORDS):
        print("[!] 今日免费生成额度已用完，已停止")
        raise SystemExit(1)

    selected_name = SERVER_VIDEO_MODEL_OPTIONS.get(VIDEO_MODEL_ID) or ""
    for _ in range(MAX_AUTO_REPLY):
        if creations or any(k in reply for k in STARTED):
            break
        if "确认" in reply:
            echo = ("确认，用 %s 生成" % selected_name) if selected_name else "确认"
        elif any(w in reply for w in PROMPT_WORDS):
            echo = "参考图已经上传好了，不要输出提示词，直接用 %s 开始生成视频" % selected_name
        else:
            echo = ("直接生成，用 %s 生成" % selected_name) if selected_name else "直接生成"
        print("[*] 自动回复「%s」" % echo)
        sub = client.send_message(echo, conversation_id=conv,
                                  local_conv_id=local_conv_id, timeout=SEND_TIMEOUT)
        conv = str((sub.get("ack") or {}).get("conversation_id") or conv)
        reply = sub.get("reply") or reply
        creations = sub.get("creations") or creations
        if reply:
            print("[*] bot:", reply[:300])
        if any(w in reply for w in QUOTA_WORDS):
            print("[!] 今日免费生成额度已用完，已停止")
            raise SystemExit(1)

    if conv and not creations:
        since = int(ack.get("message_index") or 0)
        print("[*] waiting creation card from index", since)
        try:
            creations = client.wait_creations(conv, since_index=since,
                                              timeout=WAIT_CREATION_TIMEOUT,
                                              interval=POLL_INTERVAL,
                                              fail_words=FAIL_WORDS)
        except RuntimeError as e:
            print("[!] 生成失败：%s" % e)
            raise SystemExit(1)

    if creations:
        print(json.dumps(creations, ensure_ascii=False, indent=2)[:30000])
        for creation in creations:
            print_creation(creation)
    else:
        print("[!] no creation card yet")


if __name__ == "__main__":
    main()
