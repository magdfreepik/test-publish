import os, re, time, random, json, html
from datetime import datetime, date, timedelta
from zoneinfo import ZoneInfo

import requests
import backoff
import feedparser
from apscheduler.schedulers.background import BackgroundScheduler

from google.oauth2.credentials import Credentials
from googleapiclient.discovery import build

import markdown as md
import bleach

from flask import Flask, request, jsonify

# =================== إعدادات عامة ===================
TZ = ZoneInfo("Asia/Baghdad")
POST_TIMES_LOCAL = ["10:00", "18:00"]  # يومياً بتوقيت بغداد

SAFE_CALLS_PER_MIN = int(os.getenv("SAFE_CALLS_PER_MIN", "3"))
AI_MAX_RETRIES = int(os.getenv("AI_MAX_RETRIES", "3"))
AI_BACKOFF_BASE = int(os.getenv("AI_BACKOFF_BASE", "4"))

# أسرار أساسية (ضعها في Secrets)
GEMINI_API_KEY = os.environ["GEMINI_API_KEY"]
BLOG_URL = os.environ["BLOG_URL"]
CLIENT_ID = os.environ["CLIENT_ID"]
CLIENT_SECRET = os.environ["CLIENT_SECRET"]
REFRESH_TOKEN = os.environ["REFRESH_TOKEN"]

# أسرار اختيارية
PEXELS_API_KEY = os.getenv("PEXELS_API_KEY", "")
PIXABAY_API_KEY = os.getenv("PIXABAY_API_KEY", "")
FORCED_IMAGE = os.getenv("FEATURED_IMAGE_URL", "").strip()

# ترند دولة واحدة (fallback) أو قائمة دول إقليمية
TREND_GEO = os.getenv("TREND_GEO", "IQ")
TREND_GEO_LIST = [
    g.strip() for g in os.getenv("TREND_GEO_LIST", "").split(",") if g.strip()
]

# منع التكرار موضوعياً عبر عدد أيام
TOPIC_WINDOW_D = int(os.getenv("TOPIC_WINDOW_DAYS",
                               "14"))  # لا نكرر موضوعاً خلال X يوم

# وضع التشغيل
PUBLISH_MODE = os.getenv("PUBLISH_MODE", "draft").lower()  # draft | live
RUN_ONCE = os.getenv("RUN_ONCE", "0") == "1"

# تشغيل عبر كرون خارجي (Webhook) أم جدولة داخلية
USE_EXTERNAL_CRON = os.getenv("USE_EXTERNAL_CRON", "0") == "1"
TRIGGER_TOKEN = os.getenv("TRIGGER_TOKEN", "")  # ضع كلمة سر قوية

# REST v1 (Gemini) – بلا gRPC
GEMINI_API_ROOT = "https://generativelanguage.googleapis.com/v1"
MODEL_CANDIDATES = [
    "models/gemini-1.5-flash-8b",
    "models/gemini-1.5-flash",
    "models/gemini-1.5-pro",
]
GEN_CONFIG = {"temperature": 0.7, "topP": 0.9, "maxOutputTokens": 4096}
_cached_model = None

# منع التكرار (سجلات محلية بسيطة)
HISTORY_TITLES_FILE = "posted_titles.jsonl"  # سجل العناوين
HISTORY_TOPICS_FILE = "used_topics.jsonl"  # سجل المفاتيح الموضوعية
TITLE_WINDOW = 30  # لا نكرّر آخر 30 عنواناً

# Flask app (لو استخدمنا الكرون الخارجي)
app = Flask(__name__)


# =================== أدوات نص/HTML ===================
def clamp_words_ar(text, min_words=1000, max_words=1400):
    words = text.split()
    if len(words) < min_words: return text
    if len(words) <= max_words: return text
    clipped = " ".join(words[:max_words])
    m = re.search(r"(.+[.!؟…])", clipped, flags=re.S)
    return m.group(1) if m else clipped


def strip_code_fences(text):
    text = re.sub(r"```.*?```", "", text, flags=re.S)
    text = re.sub(r"<script.*?>.*?</script>", "", text, flags=re.I | re.S)
    text = re.sub(r"<style.*?>.*?</style>", "", text, flags=re.I | re.S)
    return text


def markdown_to_clean_html(md_text):
    html_raw = md.markdown(md_text, extensions=["extra", "sane_lists"])
    allowed = bleach.sanitizer.ALLOWED_TAGS.union({
        "p", "h2", "h3", "h4", "h5", "h6", "blockquote", "ul", "ol", "li",
        "strong", "em", "a", "img", "hr", "br", "code", "pre"
    })
    attrs = {
        "a": ["href", "title", "rel", "target"],
        "img":
        ["src", "alt", "title", "loading", "decoding", "width", "height"]
    }
    clean = bleach.clean(html_raw,
                         tags=allowed,
                         attributes=attrs,
                         protocols=["http", "https", "mailto"],
                         strip=True)
    clean = clean.replace("<a ", "<a target=\"_blank\" rel=\"noopener\" ")
    return clean


def normalize_headings(md_text: str) -> str:
    # حوّل أسطر تبدأ بـ H2:/H3: إلى Markdown حقيقي (## أو ###)
    md_text = re.sub(r'(?im)^\s*H2\s*[:\-–]\s*(.+)$', r'## \1', md_text)
    md_text = re.sub(r'(?im)^\s*H3\s*[:\-–]\s*(.+)$', r'### \1', md_text)
    # دعم صيغ مثل [H2]...[/H2]
    md_text = re.sub(r'(?is)\[H2\](.+?)\[/H2\]', r'## \1', md_text)
    md_text = re.sub(r'(?is)\[H3\](.+?)\[/H3\]', r'### \1', md_text)
    return md_text


def linkify_urls_md(text: str) -> str:
    # يحوّل أي URL عارٍ إلى ماركداون قابل للنقر
    def _repl(m):
        url = m.group(0)
        return f"[المصدر]({url})"

    # لا يمس الروابط التي هي أصلاً [نص](رابط)
    return re.sub(r'(?<!\()https?://[^\s)]+', _repl, text)


def ensure_references_clickable(article_md, category, topic, news_link=None):
    """يضمن قسم المراجع ويكمله حتى 4 روابط موثوقة على الأقل."""
    text = article_md.strip()
    if "المراجع" not in text:
        text += "\n\n## المراجع\n"

    links = re.findall(r"\[[^\]]+\]\((https?://[^)]+)\)", text)
    needed = max(0, 4 - len(links))

    base_refs = {
        "tech": [
            ("MIT Technology Review", "https://www.technologyreview.com/"),
            ("ACM Digital Library", "https://dl.acm.org/"),
            ("IEEE Spectrum", "https://spectrum.ieee.org/"),
            ("World Economic Forum — Tech",
             "https://www.weforum.org/focus/technology/"),
        ],
        "science": [
            ("Nature", "https://www.nature.com/"),
            ("Science", "https://www.science.org/"),
            ("UNESCO Science Report",
             "https://www.unesco.org/reports/science/"),
            ("Royal Society", "https://royalsociety.org/"),
        ],
        "economy": [
            ("World Bank — Data", "https://data.worldbank.org/"),
            ("OECD Library", "https://www.oecd-ilibrary.org/"),
            ("IMF Publications", "https://www.imf.org/en/Publications"),
            ("UNDP Reports", "https://www.undp.org/publications"),
        ],
        "news": [
            ("Google News", "https://news.google.com/"),
            ("BBC Middle East",
             "https://www.bbc.com/arabic/topics/c2dwq6y7v3yt"),
            ("Al Jazeera — Middle East",
             "https://www.aljazeera.net/news/politics"),
            ("Reuters — Middle East",
             "https://www.reuters.com/world/middle-east/"),
        ],
    }
    extra = []
    if category == "news" and news_link:
        extra.append(("مصدر الخبر", news_link))
    extra += base_refs.get(category, base_refs["science"])

    if needed > 0:
        text += "\n"
        for name, url in extra[:needed]:
            text += f"- [{name}]({url})\n"
    return text


# =================== تاريخ ومنع تكرار ===================
def norm_topic_key(s: str) -> str:
    s = s or ""
    s = s.lower()
    s = re.sub(r"[^\w\u0600-\u06FF]+", " ",
               s)  # أبقِ الأحرف + العربي + الأرقام
    s = re.sub(r"\s+", " ", s).strip()
    return s


def load_jsonl(path):
    if not os.path.exists(path): return []
    out = []
    with open(path, "r", encoding="utf-8") as f:
        for line in f:
            try:
                out.append(json.loads(line))
            except:
                pass
    return out


def append_jsonl(path, obj):
    with open(path, "a", encoding="utf-8") as f:
        f.write(json.dumps(obj, ensure_ascii=False) + "\n")


def recent_titles(limit=TITLE_WINDOW):
    titles = []
    try:
        service = get_blogger_service()
        blog_id = get_blog_id(service, BLOG_URL)
        res = service.posts().list(blogId=blog_id,
                                   fetchBodies=False,
                                   maxResults=limit,
                                   orderBy="PUBLISHED").execute()
        items = res.get("items", []) or []
        titles = [it.get("title", "").strip() for it in items]
    except Exception:
        pass
    titles += [r.get("title", "")
               for r in load_jsonl(HISTORY_TITLES_FILE)][-limit:]
    return set(titles)


def recent_topics(days=TOPIC_WINDOW_D):
    cutoff = datetime.now(TZ) - timedelta(days=days)
    used = []
    for r in load_jsonl(HISTORY_TOPICS_FILE):
        try:
            t = datetime.fromisoformat(r.get("time"))
            if t >= cutoff: used.append(r.get("topic_key", ""))
        except:
            pass
    return set(used)


def record_publish(title, topic_key):
    append_jsonl(HISTORY_TITLES_FILE, {
        "title": title,
        "time": datetime.now(TZ).isoformat()
    })
    append_jsonl(HISTORY_TOPICS_FILE, {
        "topic_key": topic_key,
        "time": datetime.now(TZ).isoformat()
    })


# =================== موديلات Gemini (REST) ===================
def list_models():
    url = f"{GEMINI_API_ROOT}/models?key={GEMINI_API_KEY}"
    r = requests.get(url, timeout=60)
    r.raise_for_status()
    return r.json().get("models", [])


def pick_supported_model():
    global _cached_model
    if _cached_model: return _cached_model
    models = {
        m["name"]: set(m.get("supportedGenerationMethods", []))
        for m in list_models()
    }
    for cand in MODEL_CANDIDATES:
        if cand in models and ({"generateContent", "create"} & models[cand]):
            _cached_model = cand
            return cand
    for name, methods in models.items():
        if {"generateContent", "create"} & methods:
            _cached_model = name
            return name
    raise RuntimeError("لا يوجد موديل Gemini متاح لحسابك.")


def gen_url_for(model_name):
    return f"{GEMINI_API_ROOT}/{model_name}:generateContent?key={GEMINI_API_KEY}"


def _call_gemini_with_model(model_name, prompt):
    payload = {
        "contents": [{
            "role": "user",
            "parts": [{
                "text": prompt
            }]
        }],
        "generationConfig": GEN_CONFIG
    }
    return requests.post(gen_url_for(model_name), json=payload, timeout=120)


@backoff.on_exception(backoff.expo,
                      Exception,
                      base=AI_BACKOFF_BASE,
                      max_tries=AI_MAX_RETRIES)
def ask_gemini(prompt: str) -> str:
    try:
        first = pick_supported_model()
    except Exception:
        first = MODEL_CANDIDATES[0]
    tried = []
    for cand in [first] + [m for m in MODEL_CANDIDATES if m != first]:
        if cand in tried: continue
        tried.append(cand)
        r = _call_gemini_with_model(cand, prompt)
        if r.status_code == 200:
            data = r.json()
            try:
                text = data["candidates"][0]["content"]["parts"][0]["text"]
            except Exception:
                raise RuntimeError(f"Gemini response parsing error: {data}")
            text = strip_code_fences(text.strip())
            return clamp_words_ar(text, 1000, 1400)
        if r.status_code in (403, 404):  # جرب موديل آخر
            continue
        raise RuntimeError(f"Gemini API error {r.status_code}: {r.text[:400]}")
    raise RuntimeError("تعذر استخدام أي موديل من Gemini للحساب الحالي.")


# =================== الصور: ويكيبيديا/ويكيميديا → Pexels/Pixabay → Placeholder ===================
def wiki_lead_image(title, lang="ar"):
    s = requests.get(f"https://{lang}.wikipedia.org/w/api.php",
                     params={
                         "action": "query",
                         "format": "json",
                         "prop": "pageimages",
                         "piprop": "original|thumbnail",
                         "pithumbsize": "1200",
                         "titles": title
                     },
                     timeout=20)
    if s.status_code != 200: return None
    pages = s.json().get("query", {}).get("pages", {})
    for _, p in pages.items():
        if "original" in p: return p["original"]["source"]
        if "thumbnail" in p: return p["thumbnail"]["source"]
    return None


def fetch_image_general(topic):
    for lang in ("ar", "en"):
        try:
            url = wiki_lead_image(topic, lang=lang)
            if url:
                print(f"[IMG] wiki({lang}): {url}")
                return {"url": url, "credit": f'Image via Wikipedia ({lang})'}
        except Exception as e:
            print(f"[IMG] wiki error {lang}: {e}")
    return None


def fetch_image_unsplash(topic):
    if not UNSPLASH_ACCESS_KEY:
        return None
    try:
        r = requests.get(
            "https://api.unsplash.com/search/photos",
            headers={"Authorization": f"Client-ID {UNSPLASH_ACCESS_KEY}"},
            params={
                "query": topic,
                "per_page": 10,
                "orientation": "landscape"
            },
            timeout=30)
        if r.status_code != 200:
            return None
        results = r.json().get("results", [])
        if not results:
            return None
        p = random.choice(results)
        urls = p.get("urls", {}) or {}
        url = urls.get("regular") or urls.get("full") or urls.get("small")
        if not url:
            return None
        user = p.get("user", {}) or {}
        credit_name = user.get("name") or "Unsplash"
        credit_url = (user.get("links")
                      or {}).get("html") or "https://unsplash.com"
        print(f"[IMG] unsplash: {url}")
        return {
            "url":
            url,
            "credit":
            f'صورة من Unsplash — <a href="{html.escape(credit_url)}" target="_blank" rel="noopener">{html.escape(credit_name)}</a>'
        }
    except Exception as e:
        print(f"[IMG] unsplash error: {e}")
        return None


def fetch_image(query):
    if FORCED_IMAGE:
        print(f"[IMG] forced: {FORCED_IMAGE}")
        return {"url": FORCED_IMAGE, "credit": "Image (forced test URL)"}

    topic = (query or "Research").split("،")[0].split(":")[0].strip()

    # 1) ويكيبيديا/ويكيميديا (بدون مفاتيح)
    img = fetch_image_general(topic)
    if img: return img

    # 2) Pexels
    if PEXELS_API_KEY:
        try:
            r = requests.get("https://api.pexels.com/v1/search",
                             headers={"Authorization": PEXELS_API_KEY},
                             params={
                                 "query": topic,
                                 "per_page": 10,
                                 "orientation": "landscape"
                             },
                             timeout=30)
            photos = r.json().get("photos", [])
            if photos:
                p = random.choice(photos)
                url = p["src"]["large2x"]
                print(f"[IMG] pexels: {url}")
                return {
                    "url":
                    url,
                    "credit":
                    f'صورة من Pexels — <a href="{html.escape(p["url"])}" target="_blank" rel="noopener">المصدر</a>'
                }
        except Exception as e:
            print(f"[IMG] pexels error: {e}")

    # 3) Pixabay
    if PIXABAY_API_KEY:
        try:
            r = requests.get("https://pixabay.com/api/",
                             params={
                                 "key": PIXABAY_API_KEY,
                                 "q": topic,
                                 "image_type": "photo",
                                 "per_page": 10,
                                 "safesearch": "true",
                                 "orientation": "horizontal"
                             },
                             timeout=30)
            hits = r.json().get("hits", [])
            if hits:
                p = random.choice(hits)
                url = p["largeImageURL"]
                print(f"[IMG] pixabay: {url}")
                return {
                    "url":
                    url,
                    "credit":
                    f'صورة من Pixabay — <a href="{html.escape(p["pageURL"])}" target="_blank" rel="noopener">المصدر</a>'
                }
        except Exception as e:
            print(f"[IMG] pixabay error: {e}")

    # 4) Placeholder مضمون
    placeholder = "https://via.placeholder.com/1200x630.png?text=Research"
    print(f"[IMG] placeholder: {placeholder}")
    return {"url": placeholder, "credit": "Placeholder"}


def build_post_html(title, img, article_md):
    # صورة البداية بصيغة بسيطة مضمونة مع تعليق مصدر
    img_html = f'''
<p style="margin:0 0 12px 0;">
  <img src="{html.escape(img["url"])}"
       alt="{html.escape(title)}"
       loading="lazy" decoding="async"
       style="max-width:100%;height:auto;border-radius:8px;display:block;margin:auto;" />
</p>
<p style="font-size:0.9em;color:#555;margin:4px 0 16px 0;">{img["credit"]}</p>
<hr/>
'''
    body_html = markdown_to_clean_html(article_md)
    body_html = strip_code_fences(body_html)
    return img_html + body_html


# =================== Google Trends + Google News ===================
def fetch_trends_list(geo: str, max_items=10):
    url = f"https://trends.google.com/trends/trendingsearches/daily/rss?geo={geo}"
    feed = feedparser.parse(url)
    titles = []
    for e in feed.entries[:max_items]:
        t = e.title
        link = f"https://www.google.com/search?q={requests.utils.quote(t)}"
        titles.append((t, link))
    return titles


def fetch_trends_region(geos, per_geo=10):
    """يجمع الترند من عدة دول ويرتّبه حسب التكرار (الأكثر ظهوراً أولاً)."""
    bucket = {}  # key -> {"count": n, "title": t, "link": l}
    for geo in geos:
        items = fetch_trends_list(geo, max_items=per_geo)
        for title, link in items:
            k = norm_topic_key(title)
            if not k:
                continue
            if k not in bucket:
                bucket[k] = {"count": 0, "title": title, "link": link}
            bucket[k]["count"] += 1
    ranked = sorted(bucket.values(), key=lambda x: (-x["count"], x["title"]))
    return [(r["title"], r["link"]) for r in ranked]


def fetch_top_me_news(n=0):
    url = "https://news.google.com/rss?hl=ar&gl=IQ&ceid=IQ:ar"
    feed = feedparser.parse(url)
    if feed.entries:
        idx = min(n, len(feed.entries) - 1)
        e = feed.entries[idx]
        return e.title, e.link
    return None, None


# =================== Blogger API ===================
def get_blogger_service():
    creds = Credentials(None,
                        refresh_token=REFRESH_TOKEN,
                        client_id=CLIENT_ID,
                        client_secret=CLIENT_SECRET,
                        token_uri="https://oauth2.googleapis.com/token",
                        scopes=["https://www.googleapis.com/auth/blogger"])
    return build("blogger", "v3", credentials=creds, cache_discovery=False)


def get_blog_id(service, blog_url):
    return service.blogs().getByUrl(url=blog_url).execute()["id"]


def post_to_blogger(title, html_content, labels=None):
    service = get_blogger_service()
    blog_id = get_blog_id(service, BLOG_URL)
    body = {"kind": "blogger#post", "title": title, "content": html_content}
    if labels: body["labels"] = labels
    is_draft = (PUBLISH_MODE != "live")
    res = service.posts().insert(blogId=blog_id, body=body,
                                 isDraft=is_draft).execute()
    return res


# =================== محاور ثابتة للاختيار ===================
TOPICS_TECH = [
    "تأثير الحوسبة السحابية Cloud Computing على نماذج الأعمال",
    "دور الذكاء الاصطناعي Artificial Intelligence في تحسين الخدمات العامة",
    "الأمن السيبراني Cybersecurity ومخاطر الهجمات على البنية التحتية",
    "إنترنت الأشياء Internet of Things وتحوّلات المدن الذكية",
    "تحليلات البيانات الضخمة Big Data Analytics واتخاذ القرار"
]
TOPICS_SCIENCE = [
    "التجربة والملاحظة في Scientific Method عبر التاريخ",
    "العلاقة بين البحث الأساسي Basic Research والابتكار",
    "التعليم العلمي Scientific Education وبناء رأس المال البشري",
    "تاريخ المختبرات Laboratories ودورها في الدولة الحديثة",
    "الاستقراء Induction والعقلانية في تقدم العلوم"
]
TOPICS_ECON = [
    "الاقتصاد المعرفي Knowledge Economy وصناعة القيمة",
    "التنويع الاقتصادي Economic Diversification في الدول النامية",
    "رأس المال البشري Human Capital ونمو الإنتاجية",
    "سلاسل التوريد العالمية Global Supply Chains والتحولات الجيوسياسية",
    "الاقتصاد السلوكي Behavioral Economics وصنع السياسات"
]


def current_cycle_index(today=None):
    d = today or date.today()
    anchor = date(2025, 1, 1)
    return ((d - anchor).days) % 3


def slot_category_for_today(slot_idx, today=None):
    c = current_cycle_index(today)
    if c == 0: return "tech" if slot_idx == 0 else "science"
    if c == 1: return "economy"
    return "news"


def choose_topic_for_category(category, slot_idx):
    # صباح/مساء مختلف دائماً بseed اليوم والفتحة
    rnd = random.Random(f"{date.today().isoformat()}-{category}-{slot_idx}")
    if category == "tech": return rnd.choice(TOPICS_TECH)
    if category == "science": return rnd.choice(TOPICS_SCIENCE)
    if category == "economy": return rnd.choice(TOPICS_ECON)
    if category == "news":
        # ترند إقليمي من عدة دول إن توفر TREND_GEO_LIST، وإلا دولة واحدة
        if TREND_GEO_LIST:
            trends = fetch_trends_region(TREND_GEO_LIST, per_geo=10)
        else:
            trends = fetch_trends_list(TREND_GEO, max_items=10)

        if trends:
            idx = 0 if slot_idx == 0 else 1
            if len(trends) > idx:
                return trends[idx]

        # خطة بديلة: Google News
        title, link = fetch_top_me_news(n=slot_idx)
        if title: return (title, link)
        return ("تطورات مهمة في الشرق الأوسط — قراءة تحليلية",
                "https://news.google.com/")


def labels_for_category(category):
    return {
        "tech": ["تكنولوجيا", "ابتكار", "رقمنة"],
        "science": ["علوم", "بحث علمي"],
        "economy": ["اقتصاد", "تنمية"],
        "news": ["أخبار", "ترند"]
    }.get(category, ["بحث"])


# =================== البرومبت ===================
def build_prompt_ar(topic, kind="general", news_link=None):
    base_rules = """
- اللغة: عربية فصيحة واضحة.
- الطول: بين 1000 و1400 كلمة.
- استخدم المصطلحات الأساسية بالعربية والإنجليزية فقط.
- هيكل: مقدمة، عناوين فرعية، أمثلة/شواهد، خاتمة مركزة.
- لا أي كود برمجي أو وسوم سكربت أو أقواس ثلاثية.
- أضف فقرة ختامية بعنوان "المراجع" (قائمة نقطية) بحد أدنى 4 مراجع موثوقة مع روابط قابلة للنقر.
- لا تضع صوراً داخل النص (ستُضاف صورة واحدة في البداية برمجياً).
- تجنّب الحشو والتكرار.
""".strip()
    extra = ""
    if kind == "news":
        extra = f"""
- الموضوع مبني على ترند/خبر: "{topic}".
- اربط التحليل بسياق الشرق الأوسط حين يكون مناسباً.
- أدرج رابط المصدر ضمن "المراجع": {news_link}
""".strip()
    return f"""أنت باحث يكتب مقالة عربية رصينة ومفهومة للقارئ العام.
الموضوع: "{topic}"
{base_rules}
{extra}
أنتِج النص النهائي مباشرة دون أي تعليقات جانبية.
""".strip()


# =================== النشر مع منع التكرار ===================
def extract_title(article_md, fallback_topic):
    m = re.search(r"^\s*#+\s*(.+)$", article_md, flags=re.M)
    if m: return m.group(1).strip()[:90]
    for line in article_md.splitlines():
        t = line.strip()
        if t and not t.startswith("#"): return t[:90]
    return (fallback_topic
            if isinstance(fallback_topic, str) else str(fallback_topic))[:90]


def regenerate_until_unique(category, slot_idx, max_tries=3):
    """
    يختار موضوعاً ويولّد مقالة غير مكرّرة عنوانًا ولا موضوعًا.
    لا يرجع أبداً بدون article_md/search_query (يولّد كحل أخير).
    """
    tried_keys = set()
    used_title_set = recent_titles(TITLE_WINDOW)
    used_topic_keys = recent_topics(TOPIC_WINDOW_D)
    last_title, last_article, last_query = "مقال", "", ""

    for _ in range(max_tries):
        picked = choose_topic_for_category(category, slot_idx)
        if isinstance(picked, tuple):
            topic, link = picked
            prompt = build_prompt_ar(topic, kind="news", news_link=link)
            search_query = topic
        else:
            topic = picked
            prompt = build_prompt_ar(topic, kind="general")
            search_query = topic

        topic_key = norm_topic_key(topic)
        if topic_key in used_topic_keys or topic_key in tried_keys:
            tried_keys.add(topic_key)
            continue

        article_md = ask_gemini(prompt)
        article_md = ensure_references_clickable(
            article_md,
            category,
            topic,
            news_link=link if isinstance(picked, tuple) else None)
        title = extract_title(article_md, topic)

        last_title, last_article, last_query = title, article_md, search_query

        if title not in used_title_set:
            return title, article_md, search_query, topic_key

        tried_keys.add(topic_key)

    # fallback مضمون
    fallback_pool = (TOPICS_TECH + TOPICS_SCIENCE + TOPICS_ECON)
    random.shuffle(fallback_pool)
    for fb in fallback_pool:
        fb_key = norm_topic_key(fb)
        if fb_key in used_topic_keys or fb_key in tried_keys:
            continue
        prompt = build_prompt_ar(fb, kind="general")
        article_md = ask_gemini(prompt)
        article_md = ensure_references_clickable(article_md, category, fb)
        title = extract_title(article_md, fb)
        if title in used_title_set:
            suffix = datetime.now(TZ).strftime(" — %Y/%m/%d %H:%M")
            title = f"{title}{suffix}"
        return title, article_md, fb, fb_key

    suffix = datetime.now(TZ).strftime(" — %Y/%m/%d %H:%M")
    return f"{last_title}{suffix}", (last_article or "مقال تجريبي"), (
        last_query or "بحث"), norm_topic_key(last_query or "بحث")


def make_article_once(slot_idx):
    category = slot_category_for_today(slot_idx, date.today())

    # 1) توليد مضمون غير مكرر وضمان "المراجع"
    title, article_md, search_query, topic_key = regenerate_until_unique(
        category, slot_idx)

    # 2) تحويل أي روابط عارية إلى روابط قابلة للنقر
    article_md = linkify_urls_md(article_md)

    # 3) صورة مضمونة في البداية
    image = fetch_image(search_query)
    print(f"[IMG] using: {image['url']}")
    html_content = build_post_html(title, image, article_md)

    # 4) نشر إلى Blogger
    labels = labels_for_category(category)
    result = post_to_blogger(title, html_content, labels=labels)
    record_publish(title, topic_key)

    state = "مسودة" if (PUBLISH_MODE != "live") else "منشور حي"
    print(
        f"[{datetime.now(TZ)}] {state}: {result.get('url', 'بدون رابط')} | {category} | {title}"
    )


# =================== Webhook (لو استخدمنا كرون خارجي) ===================
@app.get("/")
def health():
    return "OK", 200


@app.get("/trigger")
def trigger():
    token = request.args.get("token", "")
    slot = request.args.get("slot", "0")
    if TRIGGER_TOKEN and token != TRIGGER_TOKEN:
        return jsonify({"ok": False, "error": "unauthorized"}), 401
    try:
        i = int(slot)
        if i not in (0, 1):
            return jsonify({"ok": False, "error": "slot must be 0 or 1"}), 400
        make_article_once(i)
        return jsonify({"ok": True, "slot": i}), 200
    except Exception as e:
        return jsonify({"ok": False, "error": str(e)}), 500


# =================== الجدولة الداخلية ===================
def schedule_jobs():
    sched = BackgroundScheduler(timezone=TZ)
    for idx, t in enumerate(POST_TIMES_LOCAL):
        hour, minute = map(int, t.split(":"))
        sched.add_job(lambda i=idx: make_article_once(i),
                      "cron",
                      hour=hour,
                      minute=minute,
                      id=f"post_{t}")
    sched.start()
    print(
        f"الجدولة فعّالة: {POST_TIMES_LOCAL} بتوقيت بغداد — تنويع دائم (Tech/Science → Economy → News). وضع النشر: {PUBLISH_MODE.upper()}"
    )


# =================== التشغيل ===================
if __name__ == "__main__":
    if USE_EXTERNAL_CRON:
        # وضع الكرون الخارجي: شغّل خادم الويب فقط
        port = int(os.getenv("PORT", "8000"))
        print(
            f"External-cron mode ON. Webhook: /trigger?slot=0|1&token=***  Port={port}"
        )
        # اطبع جميع الروابط المحتملة للمشروع
        slug = os.getenv("REPL_SLUG", "blogger-auto-poster").replace("_", "-")
        owner = os.getenv("REPL_OWNER", "magdfreepik")
        guesses = [
            f"https://{slug}--{owner}.replit.app/",
            f"https://{slug}.{owner}.repl.co/",
            f"https://{slug}--{owner}.repl.co/",
            f"https://{slug}.{owner}.replit.app/",
        ]
        print("\n=== Possible public URLs ===")
        for u in guesses:
            print("  ", u)
        print(
            "Open one of those in your browser. Expect `OK` at `/` and use `/trigger?slot=0|1&token=...`.\n"
        )

        app.run(host="0.0.0.0", port=port)
    else:
        # الوضع العادي: بروفة أو جدولة داخلية
        if RUN_ONCE:
            make_article_once(0)  # الصباحية
            make_article_once(1)  # المسائية
        else:
            schedule_jobs()
            try:
                while True:
                    time.sleep(30)
            except KeyboardInterrupt:
                pass
