"""Практика № 2. Друзья и друзья друзей VK.

Python 3.10+, зависимости: python -m pip install "networkx>=3.5,<4" scipy
Проверка доступа: python vk_practice_2.py --probe
Сбор и расчёт:    python vk_practice_2.py
Браузерный сбор:  python vk_practice_2.py --browser
Проверка браузера: python vk_practice_2.py --browser --probe
Проверка API сайта: python vk_practice_2.py --web-api --probe
Сбор через API сайта: python vk_practice_2.py --web-api
Для браузера: python -m pip install playwright; python -m playwright install chromium
При проблемах с Google Sheets: python vk_practice_2.py --input profiles.csv
В CSV должны быть текстовые ссылки на профили VK. Ключ приложения или
пользовательский ключ вводится скрыто или считывается из VK_ACCESS_TOKEN.
В режимах --browser и --web-api сервисный ключ используется только для users.get.
Вход в VK выполняется вручную в отдельном окне Chromium.

В results (results_browser для --browser, results_web_api для --web-api) появятся centrality.csv, coverage.csv, summary.json и edges.tsv.gz.
Кэш списков друзей сохраняется после каждого профиля. При смене ключа или
для повторного сбора укажите новый --output. По умолчанию посредничество
считается точно для графа до 2000 вершин, иначе по 512 источникам.
--samples 0 включает точный расчёт независимо от размера графа.
"""

import argparse
import csv
import getpass
import gzip
import io
import json
import os
from contextlib import contextmanager, nullcontext
from pathlib import Path
import re
import sqlite3
import sys
import time
from urllib.error import HTTPError, URLError
from urllib.parse import parse_qs, parse_qsl, urlencode, urlsplit
from urllib.request import Request, urlopen


SHEET = "https://docs.google.com/spreadsheets/d/1sQ3Gnf4o1KnaQEx-8JWUX2ju81YROpUUwkFwJ-NJQvM/gviz/tq?tqx=out:csv&gid=0"
PROFILE = re.compile(
    r"(?:https?://)?(?:www\.|m\.)?vk\.(?:com|ru)/([a-z0-9_.]+)", re.I
)
API = "https://api.vk.ru/method/"
API_VERSION = "5.199"
PROFILE_ERRORS = {15, 18, 30, 113}
PAGE_SIZE = 5000
MOBILE = "https://m.vk.ru"
BROWSER_PROFILES = (447383697, 118968780)


class VKError(RuntimeError):
    def __init__(self, method, code, message):
        super().__init__(f"{method}: VK API {code} — {message}")
        self.code = code


def profile_names(path):
    if path:
        source = path.read_text(encoding="utf-8-sig")
    else:
        try:
            with urlopen(SHEET, timeout=25) as response:
                source = response.read().decode("utf-8-sig")
        except (OSError, UnicodeError) as exc:
            raise RuntimeError("Не удалось скачать таблицу. Скачайте CSV и укажите --input.") from exc
    names = dict.fromkeys(
        match[1].lower()
        for row in csv.reader(io.StringIO(source))
        for cell in row
        if (match := PROFILE.fullmatch(cell.strip().rstrip("/").split("?")[0].split("#")[0].rstrip("/")))
    )
    if not names:
        raise RuntimeError("В таблице нет текстовых ссылок на профили VK.")
    return list(names)


class VK:
    def __init__(self, token):
        self.token = token
        self.last_request = 0.0

    def call(self, method, **params):
        body = urlencode({"v": API_VERSION, "access_token": self.token, **params}).encode()
        request = Request(API + method, data=body)
        for attempt in range(5):
            time.sleep(max(0, 0.36 - (time.monotonic() - self.last_request)))
            self.last_request = time.monotonic()
            try:
                with urlopen(request, timeout=25) as response:
                    payload = json.load(response)
            except HTTPError as exc:
                if exc.code not in (429, 500, 502, 503, 504) or attempt == 4:
                    raise RuntimeError(f"{method}: HTTP {exc.code} от api.vk.ru") from None
            except (URLError, TimeoutError):
                if attempt == 4:
                    raise RuntimeError(f"{method}: не удалось подключиться к api.vk.ru") from None
            except (ValueError, UnicodeError):
                raise RuntimeError(
                    f"{method}: api.vk.ru вернул ответ вне формата JSON. Проверьте сеть."
                ) from None
            else:
                if "response" in payload:
                    return payload["response"]
                error = payload.get("error", {})
                code = error.get("error_code")
                if code not in (1, 6, 9, 10, 29) or attempt == 4:
                    message = str(error.get("error_msg", "неизвестная ошибка"))
                    raise VKError(method, code, message.replace(self.token, "[скрыто]"))
            time.sleep(2 ** attempt)

    def resolve(self, name):
        user = re.fullmatch(r"id([1-9][0-9]*)", name)
        if user:
            return int(user[1])
        rows = self.call("users.get", user_ids=name)
        return int(rows[0]["id"]) if rows and rows[0].get("id", 0) > 0 else None

    def friends(self, user_id):
        friends = []
        while True:
            page = self.call("friends.get", user_id=user_id, count=PAGE_SIZE, offset=len(friends))
            items = page["items"]
            if not items and len(friends) < page["count"]:
                raise RuntimeError(f"VK вернул неполный список для id{user_id}. Повторите запуск.")
            friends.extend(items)
            if len(friends) >= page["count"]:
                unique = set(friends)
                if len(unique) != page["count"]:
                    raise RuntimeError(f"Список друзей id{user_id} изменился при чтении. Повторите запуск.")
                return sorted(unique - {user_id})


# Profile links reached from the all-friends tab carry the source marker.
FRIEND_LINKS = r"""() => Array.from(document.querySelectorAll('a[href]'), a => {
    const u = new URL(a.href, location.href);
    const section = u.searchParams.get('section');
    if (!['m.vk.ru', 'm.vk.com', 'vk.ru', 'vk.com'].includes(u.hostname)
        || u.searchParams.get('from') !== 'friends'
        || (section && section !== 'all')
        || !/^\/[a-z0-9_.]+\/?$/i.test(u.pathname)
        || !a.getClientRects().length) return null;
    return u.pathname.replaceAll('/', '').toLowerCase();
}).filter(Boolean)"""
FRIEND_COUNT = re.compile(r"^(?:Все\s+)?Друзья\s*([0-9][0-9 \u00a0\u202f]*)$",
                          re.I)
MORE_FRIENDS = re.compile(r"^(?:Показать|Загрузить) ещё(?: друзей)?$|^Далее$", re.I)


class BrowserVK(VK):
    def __init__(self, token, page):
        super().__init__(token)
        self.page = page
        self.aliases = {}

    def resolve(self, name):
        if name not in self.aliases:
            self.aliases[name] = super().resolve(name)
        return self.aliases[name]

    def resolve_links(self, links):
        for name in links:
            numeric = re.fullmatch(r"id([1-9][0-9]*)", name)
            if numeric:
                self.aliases[name] = int(numeric[1])
        missing = sorted(links - self.aliases.keys())
        for start in range(0, len(missing), 100):
            batch = missing[start:start + 100]
            try:
                rows = self.call("users.get", user_ids=",".join(batch), fields="screen_name")
            except VKError as exc:
                if exc.code not in PROFILE_ERRORS:
                    raise
                rows = []
            by_name = {row.get("screen_name", "").lower(): row["id"]
                       for row in rows if row.get("id", 0) > 0}
            for name in batch:
                try:
                    self.aliases[name] = by_name[name] if name in by_name else self.resolve(name)
                except VKError as exc:
                    if exc.code not in PROFILE_ERRORS:
                        raise
                    self.aliases[name] = None
        return {self.aliases[name] for name in links if self.aliases[name] is not None}

    def read_list(self, user_id):
        from playwright.sync_api import Error as PlaywrightError

        url = f"{MOBILE}/friends?id={user_id}"
        page = self.page
        try:
            response = page.goto(url, wait_until="domcontentloaded", timeout=30000)
            if response and response.status in (404, 410):
                return [], "unavailable", None
            if response and not response.ok:
                raise RuntimeError(f"Браузер: HTTP {response.status}, id{user_id}. Сбор остановлен.")

            names = set()
            expected = None
            unchanged = 0
            clicked_links = set()
            for _ in range(160):
                current = urlsplit(page.url)
                if (current.hostname not in {"m.vk.ru", "m.vk.com", "vk.ru", "vk.com"}
                        or current.path.rstrip("/") != "/friends"
                        or parse_qs(current.query).get("id") != [str(user_id)]):
                    raise RuntimeError(f"VK перенаправил страницу списка id{user_id}. "
                                       "Проверьте вход в открытом браузере.")
                body = page.locator("body").inner_text(timeout=10000)
                if re.search(r"введите код с картинки|проверка безопасности|подтвердите, что вы не робот",
                             body, re.I):
                    raise RuntimeError("VK запросил проверку безопасности. Сбор остановлен.")
                if re.search(r"закрытый профиль|профиль закрыт|список друзей скрыт|"
                             r"страница удалена|страница заблокирована|"
                             r"список друзей недоступен", body, re.I):
                    return [], "unavailable", None

                counts = page.get_by_text(FRIEND_COUNT).all_inner_texts()
                for label in counts:
                    match = FRIEND_COUNT.fullmatch(label.strip())
                    if match:
                        expected = int(re.sub(r"\s+", "", match[1]))
                        break

                old_size = len(names)
                names.update(page.evaluate(FRIEND_LINKS))
                if expected is not None and len(names) >= expected:
                    break
                unchanged = unchanged + 1 if len(names) == old_size else 0
                if unchanged >= 5:
                    break

                more = page.get_by_text(MORE_FRIENDS, exact=True)
                if more.count() == 1 and more.is_visible():
                    href = more.evaluate("(el) => el.closest('a')?.href ?? null")
                    if href:
                        target = urlsplit(href)
                        if (href not in clicked_links and target.hostname == current.hostname
                                and target.path == current.path
                                and parse_qs(target.query).get("id") == [str(user_id)]):
                            clicked_links.add(href)
                            page.goto(href, wait_until="domcontentloaded", timeout=30000)
                    else:
                        control = more.locator("xpath=ancestor-or-self::*[self::button or @role='button'][1]")
                        if control.count() == 1:
                            control.click(timeout=5000)
                page.evaluate("window.scrollTo(0, document.scrollingElement.scrollHeight)")
                page.wait_for_timeout(700)

            if not names and expected != 0:
                if re.search(r"друзей пока нет|нет друзей|у пользователя нет друзей", body, re.I):
                    return [], "ok", 0
                raise RuntimeError(f"В браузере не распознан список id{user_id}. "
                                   "Сделайте скрин открывшейся страницы и повторите проверку.")
        except PlaywrightError:
            raise RuntimeError(f"Браузер прервал загрузку списка id{user_id}. "
                               "Повторный запуск продолжит с кэша.") from None

        ids = self.resolve_links(names) - {user_id}
        status = "ok" if expected == len(ids) else "partial"
        return sorted(ids), status, expected


class WebAPIVK(VK):
    """Reuse a successful friends.get request observed in this user's browser."""

    def __init__(self, token, context, request):
        super().__init__(token)
        self.context = context
        url = urlsplit(request.url)
        if url.scheme != "https" or url.hostname not in {
            "api.vk.ru", "api.vk.com", "web.api.vk.ru", "web.api.vk.com"
        }:
            raise RuntimeError("Неподдерживаемый адрес API.")
        if url.path != "/method/friends.get" or request.method not in {"GET", "POST"}:
            raise RuntimeError("Ожидался запрос friends.get.")
        self.endpoint = url._replace(query="", fragment="").geturl()
        self.query = dict(parse_qsl(url.query, keep_blank_values=True))
        headers = request.all_headers()
        self.headers = {
            key: value for key, value in headers.items()
            if key.lower() not in {"cookie", "host", "content-length", "accept-encoding"}
            and not key.startswith(":")
        }
        self.http_method = request.method
        self.is_json = "application/json" in headers.get("content-type", "").lower()
        if request.post_data:
            self.body = (json.loads(request.post_data) if self.is_json else
                         dict(parse_qsl(request.post_data, keep_blank_values=True)))
        else:
            self.body = {}
        if not isinstance(self.body, dict):
            raise RuntimeError("Формат запроса friends.get пока не поддерживается.")
        params = {**self.query, **self.body}
        if not str(params.get("user_id", "")).isdigit():
            raise RuntimeError("В запросе сайта отсутствует числовой user_id.")
        self.observed_user = int(params["user_id"])
        self.observed_items = set()
        self.observed_count = None

    def call(self, method, **params):
        if method != "friends.get":
            return super().call(method, **params)
        from playwright.sync_api import Error as PlaywrightError

        query, body = self.query.copy(), self.body.copy()
        # Collect the full unfiltered list in the default stable ID order.
        for key in ("user_id", "count", "offset", "fields", "order", "list_id"):
            query.pop(key, None)
            body.pop(key, None)
        destination = query if self.http_method == "GET" else body
        destination.update(params)
        url = self.endpoint + ("?" + urlencode(query) if query else "")
        options = {"method": self.http_method, "headers": self.headers,
                   "timeout": 30000, "max_redirects": 0}
        if self.http_method == "POST":
            options["data" if self.is_json else "form"] = body

        for attempt in range(4):
            time.sleep(max(0, 0.4 - (time.monotonic() - self.last_request)))
            self.last_request = time.monotonic()
            try:
                response = self.context.request.fetch(url, **options)
            except PlaywrightError:
                raise RuntimeError("HTTP-запрос к VK прервался. Повторите запуск с сохранённым кэшем.") from None
            try:
                status = response.status
                payload = response.json() if response.ok else None
            except (ValueError, PlaywrightError):
                raise RuntimeError("VK вернул ответ вне формата JSON. Сбор остановлен.") from None
            finally:
                response.dispose()
            if status in {429, 500, 502, 503, 504} and attempt < 3:
                time.sleep(2 ** (attempt + 1))
                continue
            if not 200 <= status < 300:
                raise RuntimeError(f"Запрос сайта: HTTP {status}. Сбор остановлен.")
            if not isinstance(payload, dict):
                raise RuntimeError("VK изменил формат ответа friends.get.")
            if "response" in payload:
                result = payload["response"]
                if not (isinstance(result, dict) and isinstance(result.get("count"), int)
                        and isinstance(result.get("items"), list)):
                    raise RuntimeError("В friends.get отсутствуют count/items. Сбор остановлен.")
                # Browser responses may return objects even when fields is omitted.
                result = dict(result)
                items = [item.get("id") if isinstance(item, dict) else item
                         for item in result["items"]]
                if any(type(item) is not int or item <= 0 for item in items):
                    raise RuntimeError("В списке друзей встретились записи без числового ID.")
                result["items"] = items
                return result
            code = payload.get("error", {}).get("error_code")
            if code in {1, 6, 10} and attempt < 3:
                time.sleep(2 ** (attempt + 1))
                continue
            messages = {
                5: "Сессия больше не принимается. Повторите вход через --web-api.",
                14: "VK запросил CAPTCHA. Сбор остановлен.",
                15: "Список недоступен для текущего аккаунта.",
                18: "Страница удалена или заблокирована.",
                29: "Достигнут лимит VK. Сбор остановлен, кэш сохранён.",
                30: "Профиль закрыт.",
                1051: "VK запретил прямое повторение запроса сайта для этой сессии.",
            }
            raise VKError(method, code, messages.get(code, "Запрос сайта отклонён."))
        raise RuntimeError("VK временно не отвечает.")


def diagnostic_url(url):
    """Keep endpoint paths and parameter names, never query values."""
    parsed = urlsplit(url)
    path = parsed.path
    if not re.fullmatch(r"/(?:method/[A-Za-z.]+|[A-Za-z_.-]+/?)?", path):
        path = "/<other>"
    return {"host": parsed.hostname, "path": path,
            "query_keys": sorted(set(parse_qs(parsed.query, keep_blank_values=True)))}


def diagnostic_shape(value, depth=0):
    if depth >= 4:
        return type(value).__name__
    if isinstance(value, dict):
        return {
            key if re.fullmatch(r"[A-Za-z_]{1,50}", str(key)) else "<dynamic-key>":
            diagnostic_shape(item, depth + 1)
            for key, item in list(value.items())[:25]
        }
    if isinstance(value, list):
        return {"type": "array", "length": len(value),
                "first_item": diagnostic_shape(value[0], depth + 1) if value else None}
    return type(value).__name__


def diagnostic_response(response):
    from playwright.sync_api import Error as PlaywrightError

    request = response.request
    entry = {**diagnostic_url(request.url), "http_method": request.method,
             "resource_type": request.resource_type, "http_status": response.status}
    try:
        content_type = response.headers.get("content-type", "").split(";")[0]
        entry["content_type"] = content_type
        data = request.post_data or ""
        try:
            params = json.loads(data)
        except ValueError:
            params = dict(parse_qsl(data, keep_blank_values=True))
        if isinstance(params, dict):
            entry["body_keys"] = sorted(
                key for key in params if re.fullmatch(r"[A-Za-z_]{1,50}", str(key)))
            if params.get("act") in {"get_friends", "load_friends", "get_list", "load",
                                     "get", "get_section", "load_section", "get_all"}:
                entry["act"] = params["act"]
        if "json" in content_type or request.resource_type in {"xhr", "fetch"}:
            raw = response.text()
            # Some VK AJAX responses begin with an HTML comment marker.
            json_text = raw.removeprefix("<!--").lstrip()
            try:
                payload = json.loads(json_text)
            except ValueError:
                entry["response_format"] = "html" if "<" in raw[:200] else "text"
            else:
                entry["response_shape"] = diagnostic_shape(payload)
        elif "html" in content_type:
            raw = response.text()
            entry["html_has_friends_source_links"] = "from=friends" in raw
    except PlaywrightError:
        entry["body_available"] = False
    return entry


def connect_web_api(page, context, token, output):
    """Observe only reads on the test friends page; retain credentials in memory."""
    from playwright.sync_api import Error as PlaywrightError

    observed = []

    def receive(response):
        url = urlsplit(response.url)
        host = url.hostname or ""
        is_vk = host in {"vk.ru", "vk.com"} or host.endswith((".vk.ru", ".vk.com"))
        if is_vk and response.request.resource_type in {"fetch", "xhr", "document"} and len(observed) < 150:
            observed.append(response)

    page.on("response", receive)
    diagnostics = []
    chosen = None
    try:
        print("Проверяю запросы сайта на странице друзей…", flush=True)
        page.goto(f"{MOBILE}/friends?id={BROWSER_PROFILES[0]}", wait_until="domcontentloaded")
        for _ in range(20):
            page.wait_for_timeout(800)
            if any(urlsplit(response.url).path == "/method/friends.get" for response in observed):
                break
            page.evaluate("window.scrollTo(0, document.scrollingElement.scrollHeight)")
        for response in observed:
            request = response.request
            path = urlsplit(request.url).path
            entry = diagnostic_response(response)
            try:
                payload = response.json()
                if isinstance(payload, dict):
                    error = payload.get("error")
                    code = error.get("error_code") if isinstance(error, dict) else None
                    if type(code) is int:
                        entry["vk_error_code"] = code
                    result = payload.get("response")
                    if isinstance(result, dict):
                        entry["response_type"] = "object"
                        entry["has_count_items"] = "count" in result and "items" in result
                    else:
                        entry["response_type"] = type(result).__name__
                    if (chosen is None and path == "/method/friends.get" and response.ok
                            and isinstance(result, dict) and type(result.get("count")) is int
                            and isinstance(result.get("items"), list)):
                        candidate = WebAPIVK(token, context, request)
                        if candidate.observed_user == BROWSER_PROFILES[0]:
                            ids = {item.get("id") if isinstance(item, dict) else item
                                   for item in result["items"]}
                            if all(type(item) is int and item > 0 for item in ids):
                                candidate.observed_items = ids
                                candidate.observed_count = result["count"]
                                chosen = candidate
            except (PlaywrightError, ValueError, RuntimeError):
                entry["supported_response"] = False
            diagnostics.append(entry)
    finally:
        page.remove_listener("response", receive)

    page_state = diagnostic_url(page.url)
    page_state["friend_source_links"] = page.locator('a[href*="from=friends"]').count()
    page_state["friends_counter_labels"] = page.get_by_text(FRIEND_COUNT).all_inner_texts()
    # Only endpoint metadata and response shapes are written, never credentials or bodies.
    diagnostic_path = output / "api_diagnostic.json"
    diagnostic_path.write_text(json.dumps(
        {"diagnostic_version": 2, "network_requests": diagnostics,
         "page": page_state, "friends_request_found": chosen is not None},
        ensure_ascii=False, indent=2), encoding="utf-8")
    if chosen is None:
        raise RuntimeError(f"Записана диагностика {len(diagnostics)} запросов. "
                           f"Пришлите файл {diagnostic_path}.")
    started = time.monotonic()
    for index, user_id in enumerate(BROWSER_PROFILES):
        friends = chosen.friends(user_id)
        if index == 0 and (len(friends) != chosen.observed_count
                           or not chosen.observed_items.issubset(friends)):
            raise RuntimeError("Прямой запрос вернул другой список, чем страница VK. "
                               "Проверка остановлена.")
        print(f"HTTP API: id{user_id}, получено {len(friends)} друзей, статус ok", flush=True)
    print(f"Проверка HTTP API завершена за {time.monotonic() - started:.1f} с.", flush=True)
    return chosen


@contextmanager
def open_browser(args, vk):
    from playwright.sync_api import Error as PlaywrightError, sync_playwright

    with sync_playwright() as playwright:
        try:
            context = playwright.chromium.launch_persistent_context(
                str((args.output / "vk_browser_profile").resolve()), headless=False,
                locale="ru-RU", viewport={"width": 1280, "height": 900},
            )
        except PlaywrightError:
            raise RuntimeError("Chromium не запустился. Закройте окно прошлого запуска или выполните: "
                               "python -m playwright install chromium") from None
        try:
            page = context.pages[0] if context.pages else context.new_page()
            page.goto(f"{MOBILE}/friends?id={BROWSER_PROFILES[0]}", wait_until="domcontentloaded")
            print("В окне Chromium войдите в VK, если сайт просит. "
                  "Дождитесь открытия VK и вернитесь в PowerShell.", flush=True)
            input("Нажмите Enter, чтобы начать: ")
            if args.web_api:
                reader = connect_web_api(page, context, vk.token, args.output)
                yield reader
                return
            browser = BrowserVK(vk.token, page)
            if args.probe:
                complete = True
                for user_id in BROWSER_PROFILES:
                    ids, status, expected = browser.read_list(user_id)
                    print(f"id{user_id}: найдено {len(ids)} / {expected if expected is not None else '?'} "
                          f"друзей, статус {status}", flush=True)
                    complete = complete and status == "ok" and bool(ids)
                if not complete:
                    raise RuntimeError("Проверка не подтвердила полный список. Пришлите строки проверки.")
            yield browser
        except PlaywrightError:
            raise RuntimeError("Chromium не смог открыть m.vk.ru. Проверьте сайт в браузере.") from None
        finally:
            context.close()


def collect(vk, db, graph, ids, depth):
    coverage = []
    started = time.monotonic()
    for index, user_id in enumerate(ids, 1):
        row = db.execute("SELECT status, ids FROM friends WHERE user_id = ?", (user_id,)).fetchone()
        if row and row[0] != "partial":
            status, data = row
            friends = json.loads(data)
        else:
            try:
                if isinstance(vk, BrowserVK):
                    friends, status, _ = vk.read_list(user_id)
                else:
                    friends, status = vk.friends(user_id), "ok"
            except VKError as exc:
                if exc.code not in PROFILE_ERRORS:
                    raise
                status, friends = f"vk_error_{exc.code}", []
            with db:
                db.execute("INSERT OR REPLACE INTO friends VALUES (?, ?, ?)",
                           (user_id, status, json.dumps(friends)))
        graph.add_node(user_id)
        graph.add_edges_from((user_id, friend) for friend in friends)
        coverage.append((user_id, depth, status, len(friends) if status in {"ok", "partial"} else ""))
        if index == 1 or index % 25 == 0 or index == len(ids):
            elapsed = time.monotonic() - started
            remaining = elapsed / index * (len(ids) - index)
            print(f"Уровень {depth}: {index}/{len(ids)}, прошло {elapsed / 60:.1f} мин, "
                  f"оценка остатка {remaining / 60:.1f} мин", flush=True)
    return coverage


def centralities(graph, members, samples):
    import networkx as nx

    if graph.number_of_edges() == 0:
        return {node: ("", "", "", 1) for node in members}, 0
    if samples is None:
        samples = 512 if len(graph) > 2000 else 0
    k = samples if 0 < samples < len(graph) else None
    print(f"Посредничество: {'точный расчёт' if k is None else f'выборка из {k} вершин'}", flush=True)
    betweenness = nx.betweenness_centrality(graph, k=k, seed=42)
    eigen = {}
    component_size = {}
    member_ids = set(members)
    for component in nx.connected_components(graph):
        targets = component & member_ids
        if not targets:
            continue
        size = len(component)
        component_size.update(dict.fromkeys(targets, size))
        if size == 1:
            eigen.update(dict.fromkeys(targets, ""))
        elif size == 2:
            eigen.update(dict.fromkeys(targets, 2 ** -0.5))
        else:
            scores = nx.eigenvector_centrality_numpy(graph.subgraph(component), max_iter=1000, tol=1e-8)
            eigen.update((node, scores[node]) for node in targets)
    return {
        node: (betweenness[node], nx.closeness_centrality(graph, node), eigen[node], component_size[node])
        for node in members
    }, k


def write_csv(path, header, rows):
    temporary = path.with_suffix(".tmp")
    with temporary.open("w", encoding="utf-8-sig", newline="") as file:
        writer = csv.writer(file)
        writer.writerow(header)
        writer.writerows(rows)
    temporary.replace(path)


def resolve_members(vk, names):
    resolved, unresolved = {}, []
    for name in names:
        try:
            user_id = vk.resolve(name)
        except VKError as exc:
            if exc.code not in PROFILE_ERRORS:
                raise
            user_id = None
        if user_id is None:
            unresolved.append(name)
        else:
            resolved.setdefault(user_id, name)
    return resolved, unresolved


def run(args):
    import networkx as nx

    names = profile_names(args.input)
    print(f"Уникальных ссылок в списке: {len(names)}", flush=True)
    token = (os.environ.get("VK_ACCESS_TOKEN") or getpass.getpass("Ключ доступа VK: ")).strip()
    if not token:
        raise RuntimeError("Для запроса нужен ключ доступа VK.")
    vk = VK(token)
    if args.probe and not (args.browser or args.web_api):
        for name in names[:3]:
            try:
                user_id = vk.resolve(name)
                if user_id is not None:
                    print(f"id{user_id}: API вернул {len(vk.friends(user_id))} друзей.")
                    return
            except VKError as exc:
                if exc.code not in PROFILE_ERRORS:
                    raise
                print(exc)
        raise RuntimeError("Первые три ссылки не дали доступного списка друзей.")

    args.output.mkdir(parents=True, exist_ok=True)
    cache_name = "friends_cache.sqlite3"
    if args.browser:
        cache_name = "friends_browser_cache.sqlite3"
    elif args.web_api:
        cache_name = "friends_web_api_cache.sqlite3"
    graph = nx.Graph()
    with (open_browser(args, vk) if args.browser or args.web_api else nullcontext(vk)) as reader:
        if args.probe:
            return
        members, unresolved = resolve_members(reader, names)
        if not members:
            raise RuntimeError("VK не распознал ни одного профиля из таблицы.")
        with sqlite3.connect(args.output / cache_name) as db:
            db.execute("CREATE TABLE IF NOT EXISTS friends (user_id INTEGER PRIMARY KEY, status TEXT, ids TEXT)")
            coverage = collect(reader, db, graph, list(members), 0)
            first_hop = sorted(set(graph) - members.keys())
            coverage.extend(collect(reader, db, graph, first_hop, 1))

    status_by_id = {user_id: status for user_id, _, status, _ in coverage}
    rows = [
        (f"https://vk.ru/{members[user_id]}", user_id, depth, status, count)
        if user_id in members else ("", user_id, depth, status, count)
        for user_id, depth, status, count in coverage
    ]
    rows.extend((f"https://vk.ru/{name}", "", 0, "unresolved", "") for name in unresolved)
    write_csv(args.output / "coverage.csv",
              ["profile", "vk_id", "depth", "status", "friends_returned"], rows)

    scores, k = centralities(graph, members, args.samples)
    result_rows = []
    for user_id, name in members.items():
        status = status_by_id[user_id]
        metrics = scores[user_id] if graph.degree(user_id) or status == "ok" else ("", "", "", "")
        result_rows.append((f"https://vk.ru/{name}", user_id, status, *metrics))
    result_rows.extend((f"https://vk.ru/{name}", "", "unresolved", "", "", "", "")
                       for name in unresolved)
    write_csv(args.output / "centrality.csv",
              ["profile", "vk_id", "friends_status", "betweenness", "closeness",
               "eigenvector_within_component", "component_size"], result_rows)
    with gzip.open(args.output / "edges.tsv.gz", "wt", encoding="utf-8") as file:
        file.write("source\ttarget\n")
        file.writelines(f"{u}\t{v}\n" for u, v in graph.edges)
    summary = {
        "friends_source": "web_api" if args.web_api else ("browser" if args.browser else "api"),
        "members_resolved": len(members),
        "members_unresolved": len(unresolved),
        "first_hop_profiles": len(first_hop),
        "vertices": graph.number_of_nodes(),
        "edges": graph.number_of_edges(),
        "components": nx.number_connected_components(graph),
        "friends_lists_ok": sum(row[2] == "ok" for row in coverage),
        "friends_lists_partial": sum(row[2] == "partial" for row in coverage),
        "friends_lists_unavailable": sum(row[2] not in {"ok", "partial"} for row in coverage),
        "betweenness": "not_computed" if not graph.number_of_edges() else ("exact" if k is None else "sampled"),
        "betweenness_sample_size": k or None,
        "eigenvector": "L2-normalized within each connected component; blank for isolates",
        "closeness": "NetworkX Wasserman–Faust correction for disconnected graphs",
    }
    (args.output / "summary.json").write_text(json.dumps(summary, indent=2), encoding="utf-8")
    print(f"Готово. Вершин: {len(graph)}, рёбер: {graph.number_of_edges()}. Файлы: {args.output}")
    if not graph.number_of_edges():
        print("VK не вернул ни одного наблюдаемого ребра. Метрики оставлены пустыми.")


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--input", type=Path, help="CSV со ссылками вместо Google Sheets")
    parser.add_argument("--output", type=Path, help="Каталог результатов и кэша")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--browser", action="store_true", help="Читать списки друзей на m.vk.ru")
    mode.add_argument("--web-api", action="store_true", help="Повторять HTTP API запрос списка из своей браузерной сессии")
    parser.add_argument("--probe", action="store_true", help="Проверить источник списков друзей")
    parser.add_argument("--samples", type=int, help="Число источников для оценки посредничества (0 — точно)")
    args = parser.parse_args()
    if args.output is None:
        args.output = Path("results_browser" if args.browser else "results")
        if args.web_api:
            args.output = Path("results_web_api")
    if args.samples is not None and args.samples < 0:
        parser.error("--samples должно быть неотрицательным")
    try:
        run(args)
    except ImportError as exc:
        if exc.name == "playwright":
            parser.exit(1, "Установите браузер: python -m pip install playwright\n"
                           "Затем выполните: python -m playwright install chromium\n")
        parser.exit(1, f"Установите зависимости: python -m pip install \"networkx>=3.5,<4\" scipy\n{exc}\n")
    except (RuntimeError, OSError, sqlite3.Error) as exc:
        parser.exit(1, f"{exc}\n")


if __name__ == "__main__":
    main()
