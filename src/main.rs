// Ẩn cửa sổ Terminal đen trên Windows
#![windows_subsystem = "windows"]
#![allow(dead_code, unused_imports, unused_variables, unreachable_code)]

use std::{
    collections::{HashMap, VecDeque},
    sync::{
        atomic::{AtomicUsize, Ordering},
        Arc, Mutex as StdMutex,
    },
    time::{Duration, Instant},
};
use tao::{
    dpi::LogicalSize,
    event::{Event, StartCause},
    event_loop::{ControlFlow, EventLoopBuilder},
    window::WindowBuilder,
};
use tokio::{
    runtime::Builder,
    sync::{RwLock, Semaphore, Mutex as TokioMutex},
    task::JoinSet,
    io::{AsyncSeekExt, AsyncWriteExt},
};
use uuid::Uuid;
use wry::WebViewBuilder;
use aes_gcm::{
    aead::{Aead, KeyInit},
    Aes256Gcm, Nonce,
};
use argon2::{
    password_hash::{PasswordHasher, SaltString},
    Argon2, Params, Version,
};
use reqwest::RequestBuilder;
use base64::{engine::general_purpose, Engine as _};
use regex::Regex;
use serde_json::Value as JsonValue;
use zeroize::{Zeroize, ZeroizeOnDrop};
use rand::RngCore;
use url::Url;

#[macro_export]
macro_rules! json {
    ($($tt:tt)*) => { serde_json::json!($($tt)*) };
}

#[derive(Debug, Clone)]
enum Ev {
    Js(String),
    NewTab(usize),
    CloseTab(usize),
}

// ======================
// MODULE: STATE
// ======================
mod state {
    use super::*;

    #[derive(Clone, Debug, PartialEq)]
    pub enum TabMode { Normal, Incognito, Tor }

    #[derive(Clone, Debug, Default)]
    pub struct TabConfig {
        pub proxy: bool, pub proxy_url: String,
        pub tor: bool, pub warp: bool,
        pub ad: bool, pub trk: bool,
        pub sinkhole: bool, pub cookie: bool,
        pub anti_fp: bool,
    }

    #[derive(Clone, Debug, serde::Serialize, serde::Deserialize, Zeroize, ZeroizeOnDrop)]
    pub struct VaultEntry {
        pub domain: String, pub user: String, pub pass: String,
        pub nonce: String, pub salt: String,
        pub created: u64, pub last_used: u64,
    }

    #[derive(Clone, Debug, Default, Zeroize, ZeroizeOnDrop)]
    pub struct AiCfg { pub endpoint: String, pub key: String, pub model: String }

    #[derive(Clone, Debug, Default)]
    pub struct SyncConfig { pub chrome: bool, pub firefox: bool, pub edge: bool }

    #[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
    pub struct Bookmark { pub title: String, pub url: String }

    #[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
    pub struct HistoryEntry { pub url: String, pub title: String, pub time: u64 }

    #[derive(Debug)]
    pub struct TabState {
        pub id: Uuid, pub name: String, pub url: String,
        pub hist: Vec<String>, pub hist_pos: usize,
        pub cfg: TabConfig, pub mode: TabMode,
        pub last_active: Instant,
        pub frozen: bool,
        pub ai: AiCfg, pub ai_mem: VecDeque<(String, String)>,
        pub client: Option<reqwest::Client>,
        pub client_cfg_hash: u64,
        pub last_html: Option<String>,
        pub load_gen: u64,
    }

    impl TabState {
        pub fn new(mode: TabMode) -> Self {
            let is_incog = matches!(mode, TabMode::Incognito | TabMode::Tor);
            Self {
                id: Uuid::new_v4(),
                name: match mode {
                    TabMode::Normal => "New Tab",
                    TabMode::Incognito => "Private Tab",
                    TabMode::Tor => "Tor Tab"
                }.into(),
                url: "nexus://home".into(),
                hist: Vec::with_capacity(32),
                hist_pos: 0,
                cfg: TabConfig {
                    proxy_url: "socks5h://127.0.0.1:1080".into(),
                    ad: true, trk: true, sinkhole: true,
                    cookie: !is_incog, anti_fp: true,
                    tor: matches!(mode, TabMode::Tor),
                    ..Default::default()
                },
                mode, last_active: Instant::now(),
                frozen: false,
                ai: AiCfg::default(),
                ai_mem: VecDeque::with_capacity(40),
                client: None,
                client_cfg_hash: 0,
                last_html: None,
                load_gen: 0,
            }
        }

        #[inline] pub fn push_ai(&mut self, r: String, c: String) {
            self.ai_mem.push_back((r, c));
            if self.ai_mem.len() > 40 { self.ai_mem.pop_front(); }
        }

        pub fn push_hist(&mut self, url: String) {
            if self.hist.get(self.hist_pos).map(|u| u == &url).unwrap_or(false) { return; }
            if !self.hist.is_empty() && self.hist_pos + 1 < self.hist.len() {
                self.hist.truncate(self.hist_pos + 1);
            }
            self.hist.push(url);
            if self.hist.len() > 100 { self.hist.remove(0); }
            self.hist_pos = self.hist.len().saturating_sub(1);
            self.last_active = Instant::now();
        }

        pub fn go_back(&mut self) -> Option<String> {
            (self.hist_pos > 0).then(|| { self.hist_pos -= 1; self.hist[self.hist_pos].clone() })
        }

        pub fn go_fwd(&mut self) -> Option<String> {
            (self.hist_pos + 1 < self.hist.len()).then(|| {
                self.hist_pos += 1; self.hist[self.hist_pos].clone()
            })
        }

        pub fn current(&self) -> Option<String> {
            self.hist.get(self.hist_pos).cloned()
        }

        pub fn update_client(&mut self) {
            let new_hash = self.cfg_hash();
            if self.client_cfg_hash != new_hash {
                self.client = Some(super::net::build_client(&self.cfg));
                self.client_cfg_hash = new_hash;
            }
        }

        // ✅ FIX #13: Bỏ `cookie` khỏi hash — build_client() không đọc field này,
        // nên trước đây mỗi lần bật/tắt Cookie Shield sẽ vô tình tạo lại
        // reqwest::Client với cookie jar RỖNG, làm mất session đăng nhập của tab.
        fn cfg_hash(&self) -> u64 {
            use std::hash::{Hash, Hasher};
            let mut h = std::collections::hash_map::DefaultHasher::new();
            self.cfg.proxy.hash(&mut h);
            self.cfg.proxy_url.hash(&mut h);
            self.cfg.tor.hash(&mut h);
            self.cfg.warp.hash(&mut h);
            h.finish()
        }
    }

    #[derive(Debug)]
    pub struct State {
        pub active_tab: usize,
        pub tabs: Vec<TabState>,
        pub blocked: u64,
        pub global_cfg: GlobalConfig,
        pub sync: SyncState,
        pub bookmarks: Vec<Bookmark>,
        pub history: Vec<HistoryEntry>,
        pub vault: Vec<VaultEntry>,
    }

    impl State {
        pub fn new() -> Self {
            let tabs = vec![TabState::new(TabMode::Normal)];
            Self {
                active_tab: 0,
                tabs,
                blocked: 0,
                global_cfg: GlobalConfig::default(),
                sync: SyncState::default(),
                bookmarks: Vec::new(),
                history: Vec::new(),
                vault: Vec::new(),
            }
        }

        #[inline] pub fn active_tab(&self) -> &TabState { &self.tabs[self.active_tab] }
        #[inline] pub fn active_tab_mut(&mut self) -> &mut TabState { &mut self.tabs[self.active_tab] }

        pub fn new_tab(&mut self, mode: TabMode) -> usize {
            let idx = self.tabs.len();
            self.tabs.push(TabState::new(mode));
            self.active_tab = idx;
            idx
        }

        pub fn close_tab(&mut self, idx: usize) -> bool {
            (self.tabs.len() > 1 && idx < self.tabs.len()).then(|| {
                self.tabs.remove(idx);
                if self.active_tab >= idx && self.active_tab > 0 { self.active_tab -= 1; }
                if self.active_tab >= self.tabs.len() { self.active_tab = self.tabs.len() - 1; }
            }).is_some()
        }

        pub fn switch_tab(&mut self, idx: usize) {
            if idx < self.tabs.len() { self.active_tab = idx; }
        }
    }

    #[derive(Clone, Debug)]
    pub struct GlobalConfig {
        pub ad: bool, pub trk: bool, pub sinkhole: bool, pub anti_fp: bool,
        pub auto_save_passwords: bool, pub show_password_suggestions: bool,
    }

    impl Default for GlobalConfig {
        fn default() -> Self {
            Self {
                ad: true, trk: true, sinkhole: true, anti_fp: true,
                auto_save_passwords: true, show_password_suggestions: true,
            }
        }
    }

    #[derive(Debug, Default, Clone)]
    pub struct SyncState {
        pub config: SyncConfig,
        pub chrome_vault: Vec<VaultEntry>,
        pub firefox_vault: Vec<VaultEntry>,
        pub edge_vault: Vec<VaultEntry>, // ✅ FIX #14: tách riêng khỏi chrome_vault
    }

    impl SyncState {
        // ✅ FIX #6: Trả về số entries MỚI import, không phải tổng tất cả
        pub fn import_from_browser(&mut self, browser: &str) -> usize {
            let entries = match browser {
                "chrome" => super::sync::import_from_chrome(),
                "firefox" => super::sync::import_from_firefox(),
                "edge" => super::sync::import_from_edge(),
                _ => Ok(Vec::new()),
            }.unwrap_or_default();

            let count = entries.len(); // ✅ lưu trước khi move

            // ✅ FIX #14: trước đây nhánh "edge" ghi vào chrome_vault, nên lần
            // sync Chrome kế tiếp (self.chrome_vault = entries) sẽ xoá sạch
            // dữ liệu Edge vừa gộp. Giờ mỗi nguồn có chỗ chứa riêng.
            match browser {
                "chrome" => self.chrome_vault = entries,
                "firefox" => self.firefox_vault = entries,
                "edge" => self.edge_vault = entries,
                _ => {}
            }
            count // ✅ trả về số mới import
        }

        pub fn sync_to_vault(&self, vault: &mut Vec<VaultEntry>) {
            let mut all = vault.clone();
            all.extend(self.chrome_vault.clone());
            all.extend(self.firefox_vault.clone());
            all.extend(self.edge_vault.clone());
            all.sort_by(|a, b| a.domain.cmp(&b.domain));
            all.dedup_by(|a, b| a.domain == b.domain && a.user == b.user);
            *vault = all;
        }
    }

    pub async fn save_session(urls: &[String]) {
        let filtered: Vec<String> = urls.iter().filter(|u| **u != "nexus://home").cloned().collect();
        let _ = tokio::fs::write("session.json", serde_json::to_string(&filtered).unwrap_or_default()).await;
    }

    pub fn load_session() -> Vec<String> {
        std::fs::read_to_string("session.json").ok()
            .and_then(|s| serde_json::from_str(&s).ok())
            .unwrap_or_default()
    }

    pub async fn save_bookmarks(bookmarks: &[Bookmark]) {
        let _ = tokio::fs::write("bookmarks.json", serde_json::to_string(bookmarks).unwrap_or_default()).await;
    }

    pub fn load_bookmarks() -> Vec<Bookmark> {
        std::fs::read_to_string("bookmarks.json").ok()
            .and_then(|s| serde_json::from_str(&s).ok())
            .unwrap_or_default()
    }

    pub async fn save_history(history: &[HistoryEntry]) {
        let _ = tokio::fs::write("history.json", serde_json::to_string(history).unwrap_or_default()).await;
    }

    pub fn load_history() -> Vec<HistoryEntry> {
        std::fs::read_to_string("history.json").ok()
            .and_then(|s| serde_json::from_str(&s).ok())
            .unwrap_or_default()
    }
}

// ======================
// MODULE: NET
// ======================
mod net {
    use super::*;

    // ✅ FIX #4: Không unwrap() trên Proxy::all — tránh panic nếu URL sai
    pub fn build_client(c: &state::TabConfig) -> reqwest::Client {
        let jar = Arc::new(reqwest::cookie::Jar::default());
        let mut b = reqwest::Client::builder()
            .user_agent("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36")
            .cookie_provider(jar)
            .danger_accept_invalid_certs(false)
            .timeout(Duration::from_secs(30));

        if c.tor {
            if let Ok(p) = reqwest::Proxy::all("socks5h://127.0.0.1:9050") { b = b.proxy(p); }
        } else if c.warp {
            if let Ok(p) = reqwest::Proxy::all("socks5h://127.0.0.1:2053") { b = b.proxy(p); }
        } else if c.proxy {
            if let Ok(p) = reqwest::Proxy::all(&c.proxy_url) { b = b.proxy(p); }
        }

        b.build().unwrap_or_else(|_| reqwest::Client::new())
    }
}

// ======================
// MODULE: SINKHOLE
// ======================
mod sinkhole {
    #[inline] pub fn check(u: &str) -> bool {
        u.contains("doubleclick") || u.contains("adsense") || u.contains("mixpanel") ||
        u.contains("hotjar") || u.contains("facebook.com/tr") || u.contains("google-analytics")
    }
}

// ======================
// MODULE: INJECTION
// ======================
mod injection {
    use super::*;

    lazy_static::lazy_static! {
        static ref PAYLOAD_CACHE: StdMutex<HashMap<u64, String>> = StdMutex::new(HashMap::new());
    }

    pub fn get_security_payload(cfg: &state::TabConfig) -> String {
        let hash = cfg_hash(cfg);
        if let Some(cached) = PAYLOAD_CACHE.lock().unwrap().get(&hash) { return cached.clone(); }

        let (mut css, mut js) = (String::new(), String::new());

        if cfg.ad {
            css.push_str(r#"[class*="ad-"],[id*="ad-"],.adsbygoogle,#google_ads,iframe[src*="doubleclick"],[class*="sponsor"],[id*="banner"],.ad-container,.adsbox{display:none!important;height:0!important;width:0!important;overflow:hidden!important}"#);
            js.push_str(r#"
            if (window.location.hostname.includes('youtube.com')) {
                setInterval(() => {
                    const skipBtn = document.querySelector('.ytp-ad-skip-button, .ytp-ad-skip-button-modern, .ytp-skip-ad-button');
                    if (skipBtn) { skipBtn.click(); }
                    const ad = document.querySelector('.ad-showing video');
                    if (ad && !isNaN(ad.duration)) { ad.currentTime = ad.duration; }
                    document.querySelectorAll('ytd-ad-slot-renderer, ytd-promoted-sparkles-web-renderer, ytd-banner-promo-renderer, ytd-player-legacy-desktop-watch-ads-renderer').forEach(e => e.remove());
                }, 300);
            }
            "#);
        }

        if cfg.trk {
            js.push_str(r#"
            !function(){
                const trackers = ['analytics','segment.io','mixpanel','hotjar','facebook.com/tr','trackcmp'];
                const isTracker = u => {
                    try { let s = typeof u === 'string' ? u : (u.url || u.href || ''); return trackers.some(t => s.includes(t)); } catch(e) { return false; }
                };
                const notify = () => { try { window.top.postMessage(JSON.stringify({a:'inc',p:''}),'*'); } catch(e) {} };

                const origFetch = window.fetch;
                window.fetch = function(input, init) {
                    if (isTracker(input)) { notify(); return Promise.reject("Blocked"); }
                    return origFetch.apply(this, arguments);
                };

                const origOpen = XMLHttpRequest.prototype.open;
                XMLHttpRequest.prototype.open = function(method, url) {
                    if (isTracker(url)) { notify(); return; }
                    return origOpen.apply(this, arguments);
                };

                navigator.sendBeacon = () => false;
            }();
            "#);
        }

        if cfg.cookie { js.push_str(r#"!function(){const t=Object.getOwnPropertyDescriptor(Document.prototype,"cookie");t&&(Object.defineProperty(document,"cookie",{set(n){/(_ga|track|fbp)/.test(n)||t.set.call(this,n)},get(){return t.get.call(this)}}))}()"#); }

        if cfg.anti_fp { js.push_str(r#"
        !function(){
            const fakeCanvas=()=>"data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAYAAAAfFcSJAAAACklEQVR4nGMAAQAABQABDQottAAAAABJRU5ErkJggg==";
            HTMLCanvasElement.prototype.toDataURL=fakeCanvas;
            HTMLCanvasElement.prototype.toBlob=function(c){c(new Blob([fakeCanvas()]));};
            if(window.WebGLRenderingContext){
                const t=WebGLRenderingContext.prototype.getParameter;
                WebGLRenderingContext.prototype.getParameter=function(n){return 37445===n?"Nexus":37446===n?"Nexus":t.apply(this,arguments)};
            }
            if(window.WebGL2RenderingContext){
                const t2=WebGL2RenderingContext.prototype.getParameter;
                WebGL2RenderingContext.prototype.getParameter=function(n){return 37445===n?"Nexus":37446===n?"Nexus":t2.apply(this,arguments)};
            }
            Object.defineProperty(navigator,"hardwareConcurrency",{get:()=>4});
            Object.defineProperty(navigator,"deviceMemory",{get:()=>4});
            Object.defineProperty(navigator,"platform",{get:()=>"Win32"});
        }()
        "#); }

        js.push_str(r#"
        !function(){
            window.nexusGeneratePassword=(len)=>{const t="ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789!@#$%^&*";return Array.from(crypto.getRandomValues(new Uint8Array(len||16)),n=>t[n%t.length]).join("")};
            window.nexusFillPassword=(t,n)=>{let o=null,e=null;for(const n of document.querySelectorAll("input"))"password"===n.type&&!e&&(e=n),(/text|email/.test(n.type)||/user|email/i.test(n.name))&&(o=n);o&&(o.value=t);e&&(e.value=n)};

            let lastSig = "";
            const guessUserField = (pwField) => {
                const inputs = Array.from(document.querySelectorAll('input'));
                const i = inputs.indexOf(pwField);
                for (let k = i - 1; k >= 0; k--) {
                    const el = inputs[k];
                    if (/text|email/.test(el.type) || /user|email|login/i.test(el.name || el.id || '')) return el;
                }
                return inputs.find(el => el !== pwField && (/text|email/.test(el.type) || /user|email|login/i.test(el.name || el.id || ''))) || null;
            };
            // ✅ FIX #19: expose ra window để listener 'submit' thật (bên dưới) gọi lại được —
            // đây là tín hiệu đáng tin cậy nhất khi form submit chuẩn, thay vì chỉ đoán qua Enter/click.
            window.__nexusReportPassword = (pwField) => {
                if (!pwField || !pwField.value) return;
                const userField = guessUserField(pwField);
                const sig = window.location.href + '|' + (userField ? userField.value : '') + '|' + pwField.value;
                if (sig === lastSig) return;
                lastSig = sig;
                window.top.postMessage(JSON.stringify({a:"password-detected",p:{url:window.location.href,username:userField?userField.value:"",password:pwField.value}}),'*');
            };
            document.addEventListener('keydown', function(e) {
                if (e.key === 'Enter' && e.target && e.target.type === 'password') window.__nexusReportPassword(e.target);
            }, true);
            document.addEventListener('click', function(e) {
                const btn = e.target.closest('button, input[type="submit"], [role="button"], a');
                if (!btn) return;
                const label = (btn.textContent || btn.value || '').trim();
                if (!/log\s*in|sign\s*in|submit|continue|next/i.test(label) && btn.type !== 'submit') return;
                const pw = document.querySelector('input[type="password"]');
                if (pw && pw.value) window.__nexusReportPassword(pw);
            }, true);
        }();

        document.addEventListener('click', function(e) {
            let a = e.target.closest('a');
            if (a && a.href && !a.href.startsWith('javascript:') && !a.href.startsWith('#')) {
                e.preventDefault();
                e.stopPropagation();
                e.stopImmediatePropagation();
                if (a.target === '_blank') {
                    window.top.postMessage(JSON.stringify({a: 'new-tab-url', p: a.href}), '*');
                } else {
                    window.top.postMessage(JSON.stringify({a: 'nav-internal', p: a.href}), '*');
                }
            }
        }, true);

        // ✅ FIX #11: Giữ nguyên multipart/form-data (file upload) thay vì chỉ gửi key-value
        document.addEventListener('submit', function(e) {
            e.stopPropagation();
            e.stopImmediatePropagation();
            e.preventDefault();
            let form = e.target;
            const pwField = form.querySelector && form.querySelector('input[type="password"]');
            if (pwField && window.__nexusReportPassword) window.__nexusReportPassword(pwField);
            let method = (form.method || 'get').toLowerCase();
            let url = new URL(form.action || window.location.href);
            let formData = new FormData(form);
            let hasFiles = false;
            for (let [key, value] of formData.entries()) {
                if (value instanceof File) { hasFiles = true; break; }
            }

            if (method === 'get') {
                for (let [key, value] of formData.entries()) {
                    if (!(value instanceof File)) url.searchParams.append(key, value);
                }
                window.top.postMessage(JSON.stringify({a: 'nav-internal', p: url.href}), '*');
            } else if (hasFiles) {
                // ✅ File upload: dùng fetch trực tiếp trong iframe thay vì IPC
                fetch(url.href, { method: 'POST', body: formData, credentials: 'include' })
                    .then(r => r.text())
                    .then(html => {
                        window.top.postMessage(JSON.stringify({a: 'nav-internal', p: url.href}), '*');
                    })
                    .catch(() => {
                        window.top.postMessage(JSON.stringify({a: 'nav-internal', p: url.href}), '*');
                    });
            } else {
                let body = {};
                for (let [key, value] of formData.entries()) { body[key] = value; }
                window.top.postMessage(JSON.stringify({a: 'nav-post', p: {url: url.href, body: body}}), '*');
            }
        }, true);

        window.open = function(url) {
            window.top.postMessage(JSON.stringify({a: 'new-tab-url', p: url}), '*');
            return null;
        };
        "#);

        let payload = format!(r#"<style id="nexus-shield-css">{}</style><script id="nexus-shield-js">{}</script>"#, css, js);
        PAYLOAD_CACHE.lock().unwrap().insert(hash, payload.clone());
        payload
    }

    fn cfg_hash(cfg: &state::TabConfig) -> u64 {
        use std::hash::{Hash, Hasher};
        let mut h = std::collections::hash_map::DefaultHasher::new();
        cfg.ad.hash(&mut h); cfg.trk.hash(&mut h);
        cfg.cookie.hash(&mut h); cfg.anti_fp.hash(&mut h);
        h.finish()
    }
}

// ======================
// MODULE: VAULT
// ======================
mod vault {
    use super::*;
    use rand::seq::SliceRandom;

    const VAULT_FILE: &str = "nexus_vault.dat";
    lazy_static::lazy_static! {
        static ref VAULT_LOCK: TokioMutex<()> = TokioMutex::new(());
    }

    fn argon2() -> Argon2<'static> {
        let m_cost = if num_cpus::get() > 4 { 192 * 1024 } else { 128 * 1024 };
        Argon2::new(argon2::Algorithm::Argon2id, Version::V0x13,
            Params::new(m_cost, 3, std::cmp::min(4, num_cpus::get().try_into().unwrap_or(4)), None).unwrap())
    }

    fn derive_key(master: &str, salt: &[u8]) -> Option<[u8; 32]> {
        let mut key = [0u8; 32];
        argon2().hash_password_into(master.as_bytes(), salt, &mut key).ok()?;
        Some(key)
    }

    // ✅ FIX #1: salt.decode_b64(&mut raw_salt) KHÔNG tồn tại → dùng b64_decode()
    pub fn encrypt(data: &str, master: &str) -> Option<(String, String, String)> {
        if master.is_empty() { return None; }
        let salt = SaltString::generate(rand::thread_rng());
        let salt_bytes = salt.b64_decode().ok()?;          // ✅ FIX
        let key = derive_key(master, &salt_bytes)?;         // ✅ FIX: &salt_bytes
        let cipher = Aes256Gcm::new_from_slice(&key).ok()?;

        let mut nonce = [0u8; 12];
        rand::rngs::OsRng.try_fill_bytes(&mut nonce).ok()?;

        let ciphertext = cipher.encrypt(Nonce::from_slice(&nonce), data.as_bytes()).ok()?;

        Some((
            general_purpose::STANDARD.encode(&ciphertext),
            general_purpose::STANDARD.encode(nonce),
            salt.as_str().to_string(),
        ))
    }

    // ✅ FIX #2: Cùng lỗi decode_b64
    pub fn decrypt(enc: &str, nonce: &str, salt: &str, master: &str) -> Option<String> {
        let ciphertext = general_purpose::STANDARD.decode(enc).ok()?;
        let nonce_bytes = general_purpose::STANDARD.decode(nonce).ok()?;
        if nonce_bytes.len() != 12 { return None; }

        let salt_value = SaltString::from_b64(salt).ok()?;
        let salt_bytes = salt_value.b64_decode().ok()?;     // ✅ FIX
        let key = derive_key(master, &salt_bytes)?;          // ✅ FIX: &salt_bytes
        let cipher = Aes256Gcm::new_from_slice(&key).ok()?;
        String::from_utf8(cipher.decrypt(Nonce::from_slice(&nonce_bytes), ciphertext.as_slice()).ok()?).ok()
    }

    pub fn generate(len: usize) -> String {
        const CHARSET: &[u8] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789!@#$%^&*";
        let mut rng = rand::thread_rng();
        (0..len).map(|_| *CHARSET.choose(&mut rng).unwrap() as char).collect()
    }

    pub fn load() -> Vec<state::VaultEntry> {
        std::fs::read(VAULT_FILE).ok()
            .and_then(|b| serde_json::from_slice(&b).ok())
            .unwrap_or_default()
    }

    pub async fn save(entries: &[state::VaultEntry]) -> bool {
        let _guard = VAULT_LOCK.lock().await;
        let temp = format!("{}.tmp", VAULT_FILE);
        match serde_json::to_vec(entries) {
            Ok(b) => tokio::fs::write(&temp, b).await.is_ok() && tokio::fs::rename(temp, VAULT_FILE).await.is_ok(),
            Err(_) => false,
        }
    }
}

// ======================
// MODULE: SYNC
// ======================
mod sync {
    use super::*;
    pub fn import_from_chrome() -> Result<Vec<state::VaultEntry>, String> { Ok(Vec::new()) }
    pub fn import_from_firefox() -> Result<Vec<state::VaultEntry>, String> { Ok(Vec::new()) }
    pub fn import_from_edge() -> Result<Vec<state::VaultEntry>, String> { Ok(Vec::new()) }
}

// ======================
// MODULE: AI
// ======================
mod ai {
    use super::*;

    pub async fn ask(prompt: String, st: Arc<RwLock<state::State>>) -> String {
        let (cfg, ai, mut history) = {
            let g = st.read().await;
            let t = g.active_tab();
            (t.cfg.clone(), t.ai.clone(), t.ai_mem.clone())
        };

        if ai.endpoint.is_empty() || ai.key.is_empty() {
            return "⚠ AI not configured. Enter Endpoint + API Key + Model in the AI panel.".into();
        }

        let client = {
            let mut g = st.write().await;
            let t = g.active_tab_mut();
            t.update_client();
            t.client.clone().unwrap_or_else(reqwest::Client::new)
        };

        let model = if ai.model.is_empty() { "gpt-4o-mini" } else { &ai.model }.to_string();
        history.push_back(("user".into(), prompt.clone()));
        // ✅ FIX #9: Trim history tạm thời nếu > 40
        while history.len() > 40 { history.pop_front(); }

        let messages: Vec<JsonValue> = history.iter().map(|(r,c)| json!({"role":r,"content":c})).collect();

        let body = json!({ "model": model, "messages": messages, "stream": false });

        let reply = match client
            .post(&ai.endpoint)
            .bearer_auth(&ai.key)
            .header(reqwest::header::CONTENT_TYPE, "application/json")
            .body(serde_json::to_vec(&body).unwrap_or_default())
            .send().await
        {
            Ok(response) => match response.text().await {
                Ok(text) => serde_json::from_str::<JsonValue>(&text)
                    .ok()
                    .and_then(|v| v["choices"][0]["message"]["content"].as_str().map(String::from))
                    .unwrap_or_else(|| "⚠ Invalid AI response.".into()),
                Err(_) => "⚠ Invalid AI response.".into(),
            },
            Err(_) => "⚠ Invalid AI response.".into(),
        };

        {
            let mut g = st.write().await;
            let t = g.active_tab_mut();
            t.push_ai("user".into(), prompt);
            t.push_ai("assistant".into(), reply.clone());
        }
        reply
    }
}

// ======================
// MODULE: DL
// ======================
mod dl {
    use super::*;

    const PARTS: usize = 16;

    pub async fn turbo(url: String, st: Arc<RwLock<state::State>>) {
        let client = {
            let mut g = st.write().await;
            let t = g.active_tab_mut();
            t.update_client();
            t.client.clone().unwrap_or_else(reqwest::Client::new)
        };

        let (len, accept_ranges) = client.head(&url).send().await
            .ok()
            .map(|r| (r.content_length().unwrap_or(0),
                r.headers().get("accept-ranges").and_then(|v| v.to_str().ok()).map(|v| v.contains("bytes")).unwrap_or(false)))
            .unwrap_or((0, false));

        let f_name = url.split('/').next_back().filter(|s| !s.is_empty()).unwrap_or("nxdl.bin").to_string();
        let f_name = format!("./{}", f_name);

        if len == 0 || !accept_ranges {
            if let Ok(r) = client.get(&url).send().await {
                if let Ok(b) = r.bytes().await { let _ = tokio::fs::write(&f_name, &b).await; }
            }
            return;
        }

        let chunk = len.div_ceil(PARTS as u64);
        let file = match tokio::fs::OpenOptions::new().write(true).create(true).truncate(true).open(&f_name).await {
            Ok(f) => Arc::new(TokioMutex::new(f)),
            Err(_) => return,
        };

        // ✅ FIX #12: Dùng Semaphore permit guard để tránh leak permit
        let (sem, failed) = (Arc::new(Semaphore::new(PARTS)), Arc::new(AtomicUsize::new(0)));
        let mut set = JoinSet::new();

        for i in 0..PARTS {
            let (client, url, sem, file, failed) = (client.clone(), url.clone(), sem.clone(), file.clone(), failed.clone());
            let (s, e) = (i as u64 * chunk, (i as u64 * chunk + chunk - 1).min(len - 1));
            if s > e { continue; }

            set.spawn(async move {
                // ✅ FIX #12: Giữ permit guard sống đến hết scope → tự release khi drop
                let _permit = match sem.acquire_owned().await {
                    Ok(p) => p,
                    Err(_) => return,
                };
                let response = client.get(&url).header("Range", format!("bytes={}-{}", s, e)).send().await;
                if let Ok(response) = response {
                    if let Ok(bytes) = response.bytes().await {
                        let mut f = file.lock().await;
                        if f.seek(std::io::SeekFrom::Start(s)).await.is_ok() { f.write_all(&bytes).await.ok(); }
                    } else { failed.fetch_add(1, Ordering::SeqCst); }
                } else { failed.fetch_add(1, Ordering::SeqCst); }
            });
        }

        while set.join_next().await.is_some() {}
        if failed.load(Ordering::SeqCst) > 0 { let _ = tokio::fs::remove_file(&f_name).await; }
    }
}

// ======================
// MODULE: SEARCH
// ======================
mod search {
    pub fn resolve(i: &str) -> String {
        let t = i.trim();
        if t.is_empty() { return "nexus://home".into(); }
        if t.starts_with("http://") || t.starts_with("https://") || t.starts_with("nexus://") { return t.into(); }

        let looks_like_host = !t.contains(' ')
            && !t.starts_with('.') && !t.ends_with('.')
            && (t.contains('.') || t.starts_with("localhost"));

        if looks_like_host { format!("https://{}", t) }
        else {
            format!("https://html.duckduckgo.com/html/?q={}", url::form_urlencoded::byte_serialize(t.as_bytes()).collect::<String>())
        }
    }
}

// ======================
// MODULE: EXTENSIONS
// ======================
mod extensions {
    use super::*;
    use std::path::PathBuf;
    use tokio::fs;

    const EXTENSIONS_DIR: &str = "nexus_extensions";
    const MANIFEST_FILE: &str = "manifest.json";

    #[derive(Debug, Clone, serde::Deserialize)]
    pub struct ExtensionManifest {
        pub name: String, pub version: String, pub description: String,
        pub permissions: Vec<String>,
        pub content_scripts: Option<Vec<ContentScript>>,
        pub background: Option<BackgroundScript>,
        pub icons: Option<std::collections::HashMap<String, String>>,
    }

    #[derive(Debug, Clone, serde::Deserialize)]
    pub struct ContentScript {
        pub matches: Vec<String>, pub js: Vec<String>,
        pub css: Option<Vec<String>>, pub run_at: Option<String>,
    }

    #[derive(Debug, Clone, serde::Deserialize)]
    pub struct BackgroundScript {
        pub service_worker: Option<String>,
        pub scripts: Option<Vec<String>>,
    }

    #[derive(Debug)]
    pub struct Extension {
        pub id: String, pub path: PathBuf, pub manifest: ExtensionManifest, pub enabled: bool,
    }

    impl Extension {
        pub async fn load(id: &str) -> Result<Self, String> {
            let path = PathBuf::from(EXTENSIONS_DIR).join(id);
            let manifest_path = path.join(MANIFEST_FILE);
            let manifest_content = fs::read_to_string(&manifest_path).await.map_err(|e| format!("Failed to read manifest: {}", e))?;
            let manifest: ExtensionManifest = serde_json::from_str(&manifest_content).map_err(|e| format!("Invalid manifest.json: {}", e))?;
            let enabled = !path.join("DISABLED").exists();
            Ok(Self { id: id.to_string(), path, manifest, enabled })
        }

        pub async fn get_content_script_injection(&self, url: &str) -> Option<String> {
            if !self.enabled { return None; }
            let scripts = self.manifest.content_scripts.as_ref()?
                .iter()
                .filter(|cs| cs.matches.iter().any(|pattern| url_matches_pattern(url, pattern)))
                .flat_map(|cs| cs.js.iter().map(|js| (js, cs.run_at.clone())))
                .collect::<Vec<_>>();

            if scripts.is_empty() { return None; }

            let mut js_injection = String::new();
            for (js_file, run_at) in scripts {
                let js_path = self.path.join(js_file);
                if let Ok(js_content) = fs::read_to_string(&js_path).await {
                    let run_condition = match run_at.as_deref() {
                        Some("document_start") => "document.readyState !== 'loading'",
                        Some("document_end") => "document.readyState === 'interactive' || document.readyState === 'complete'",
                        Some("document_idle") => "document.readyState === 'complete'",
                        _ => "true",
                    };
                    js_injection.push_str(&format!(
                        r#"(function(){{if({0}){{{1}}};document.addEventListener('readystatechange',function(){{if({0}){{{1}}}}});}})();"#,
                        run_condition, js_content
                    ));
                }
            }
            Some(js_injection)
        }

        pub async fn get_css_injection(&self, url: &str) -> Option<String> {
            if !self.enabled { return None; }
            let css_files = self.manifest.content_scripts.as_ref()?
                .iter()
                .filter(|cs| cs.matches.iter().any(|pattern| url_matches_pattern(url, pattern)))
                .flat_map(|cs| cs.css.as_deref().unwrap_or(&[]).iter())
                .collect::<Vec<_>>();

            if css_files.is_empty() { return None; }
            let mut css_injection = String::new();
            for css_file in css_files {
                let css_path = self.path.join(css_file);
                if let Ok(css_content) = fs::read_to_string(&css_path).await { css_injection.push_str(&css_content); }
            }
            Some(css_injection)
        }

        pub async fn get_background_script(&self) -> Option<String> {
            if !self.enabled { return None; }
            let bg_script = match &self.manifest.background {
                Some(bg) => {
                    if let Some(worker) = &bg.service_worker { Some(self.path.join(worker)) }
                    else if let Some(scripts) = &bg.scripts { scripts.first().map(|first_script| self.path.join(first_script)) }
                    else { None }
                }
                None => None,
            };
            match bg_script { Some(path) => fs::read_to_string(&path).await.ok(), None => None }
        }
    }

    // ✅ FIX #8: Thêm anchors ^...$ để tránh false positive
    fn url_matches_pattern(url: &str, pattern: &str) -> bool {
        if pattern == "<all_urls>" { return true; }
        let escaped = pattern.replace('.', r"\.").replace('*', ".*");
        let anchored = format!("^{}$", escaped);
        Regex::new(&anchored).map(|re| re.is_match(url)).unwrap_or(false)
    }

    pub async fn load_all_extensions() -> Vec<Extension> {
        let mut extensions = Vec::new();
        if let Ok(entries) = fs::read_dir(EXTENSIONS_DIR).await {
            let mut stream = entries;
            while let Some(entry) = stream.next_entry().await.ok().flatten() {
                let path = if entry.file_type().await.ok().map(|ft| ft.is_dir()).unwrap_or(false) { entry.path() } else { continue; };
                if let Some(id) = path.file_name().and_then(|s| s.to_str()) {
                    if let Ok(ext) = Extension::load(id).await { extensions.push(ext); }
                }
            }
        }
        extensions
    }

    pub async fn get_injections_for_url(url: &str, extensions: &[Extension]) -> (Option<String>, Option<String>) {
        let mut js_injections = Vec::new();
        let mut css_injections = Vec::new();
        for ext in extensions {
            if let Some(js) = ext.get_content_script_injection(url).await { js_injections.push(js); }
            if let Some(css) = ext.get_css_injection(url).await { css_injections.push(css); }
        }
        (
            if js_injections.is_empty() { None } else { Some(js_injections.join("\n")) },
            if css_injections.is_empty() { None } else { Some(css_injections.join("\n")) }
        )
    }

    pub mod api {
        use super::*;
        pub fn setup_extension_apis(webview: &wry::WebView) {
            webview.evaluate_script(r#"
                if (typeof chrome === 'undefined') {
                    window.chrome = {
                        runtime: {
                            getManifest: function() { return { name: "Nexus Browser", version: "1.0" }; },
                            sendMessage: function(message, responseCallback) {
                                if (window.ipc) { window.ipc.postMessage(JSON.stringify({ a: 'ext-msg', p: message })); }
                            }
                        }
                    };
                }
            "#).ok();
        }
    }
}

// ======================
// MODULE: AUTOCONFIG
// ======================
mod autoconfig {
    use super::*;

    pub async fn detect_warp() -> bool {
        tokio::net::TcpStream::connect("127.0.0.1:2053").await.is_ok()
    }

    pub async fn detect_tor() -> bool {
        tokio::net::TcpStream::connect("127.0.0.1:9050").await.is_ok()
    }
}

// ======================
// MAIN HTML (UI BROWSER STYLE)
// ======================
fn html() -> String {
    r###"<!DOCTYPE html>
<html lang="en"><head><meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1.0">
<style>
*{box-sizing:border-box;margin:0;padding:0;font-family:-apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,Helvetica,Arial,sans-serif}
:root{--bg:#dee1e6;--panel:#ffffff;--input:#f1f3f4;--brd:#dadce0;--acc:#1a73e8;--acc-hover:#1557b0;--on-acc:#ffffff;--t1:#202124;--t2:#5f6368;--t3:#80868b;--star:#e8a33d}
:root[data-theme="dark"]{--bg:#17181a;--panel:#222327;--input:#2c2d32;--brd:#3a3b40;--acc:#8ab4f8;--acc-hover:#aecbfa;--on-acc:#062e6f;--t1:#e8eaed;--t2:#b0b3b8;--t3:#8a8d93;--star:#f0b64d}
html,body{transition:background-color .2s ease,color .2s ease}
body{background:var(--bg);color:var(--t1);height:100vh;display:flex;flex-direction:column;overflow:hidden}
#app{display:flex;flex-direction:column;height:100vh}
/* scrollbar mảnh, đồng bộ theme thay vì scrollbar mặc định to thô của OS */
*::-webkit-scrollbar{width:8px;height:8px}
*::-webkit-scrollbar-track{background:transparent}
*::-webkit-scrollbar-thumb{background:var(--brd);border-radius:8px}
*::-webkit-scrollbar-thumb:hover{background:var(--t3)}

#tabs-bar{display:flex;align-items:center;height:42px;padding:6px 8px 0;background:var(--bg);gap:2px;z-index:10}
.tab{display:flex;align-items:center;max-width:220px;min-width:140px;height:34px;padding:0 8px 0 14px;
  border-radius:10px 10px 0 0;background:transparent;color:var(--t2);cursor:pointer;white-space:nowrap;
  overflow:hidden;transition:background .15s ease;position:relative}
.tab:hover{background:color-mix(in srgb, var(--t1) 6%, transparent)}
.tab.active{background:var(--panel);color:var(--t1)}
.tab.active::after{content:"";position:absolute;left:8px;right:8px;top:0;height:2px;border-radius:0 0 2px 2px;background:var(--acc)}
.tab.frozen .tab-title{opacity:.55}
.tab-favicon{width:16px;height:16px;border-radius:5px;flex-shrink:0;margin-right:8px;display:flex;align-items:center;justify-content:center;font-size:9px;font-weight:700;color:var(--on-acc);background:var(--acc);text-transform:uppercase}
.tab-title{flex:1;overflow:hidden;text-overflow:ellipsis;margin-right:6px;font-size:12.5px;font-weight:500}
.tab-close{display:flex;align-items:center;justify-content:center;flex-shrink:0;width:22px;height:22px;
  border-radius:50%;color:var(--t3);opacity:0;transition:opacity .15s,background .15s}
.tab:hover .tab-close,.tab.active .tab-close{opacity:1}
.tab-close:hover{background:color-mix(in srgb, var(--t1) 10%, transparent);color:var(--t1)}
.tab-close svg{width:13px;height:13px}
#new-tab-btn,#new-incognito-btn{width:30px;height:30px;display:flex;align-items:center;justify-content:center;
  border-radius:50%;color:var(--t2);cursor:pointer;flex-shrink:0;margin-left:2px;transition:background .15s}
#new-tab-btn:hover,#new-incognito-btn:hover{background:color-mix(in srgb, var(--t1) 8%, transparent);color:var(--t1)}
#new-tab-btn svg,#new-incognito-btn svg{width:16px;height:16px}

#toolbar{display:flex;align-items:center;gap:2px;padding:8px 10px;background:var(--panel);border-bottom:1px solid var(--brd);z-index:10;position:relative}
#load-bar{position:absolute;left:0;bottom:-1px;height:2px;width:0;background:var(--acc);opacity:0;
  transition:width .35s ease,opacity .2s ease;z-index:20}
#load-bar.show{opacity:1}
.nav-btn{width:34px;height:34px;display:flex;align-items:center;justify-content:center;border:none;
  background:transparent;color:var(--t2);cursor:pointer;border-radius:50%;flex-shrink:0;transition:background .15s,color .15s}
.nav-btn:hover{background:var(--input);color:var(--t1)}
.nav-btn:disabled{opacity:.35;cursor:default}
.nav-btn:disabled:hover{background:transparent}
.nav-btn svg{width:18px;height:18px}
.toolbar-gap{width:8px;flex-shrink:0}

.url-wrap{flex:1;display:flex;align-items:center;height:36px;background:var(--input);border:1px solid transparent;
  border-radius:18px;padding:0 6px 0 12px;transition:box-shadow .15s,border-color .15s,background .15s;min-width:0}
.url-wrap:focus-within{background:var(--panel);border-color:var(--brd);box-shadow:0 1px 8px rgba(0,0,0,.12)}
.url-icon{color:var(--t3);flex-shrink:0;display:flex}
.url-icon svg{width:15px;height:15px}
#url-bar{flex:1;height:100%;background:transparent;border:none;padding:0 10px;font-size:13.5px;color:var(--t1);
  outline:none;min-width:0}
.url-star{width:28px;height:28px;display:flex;align-items:center;justify-content:center;border:none;
  background:transparent;color:var(--t3);cursor:pointer;border-radius:50%;flex-shrink:0;transition:background .15s,color .15s}
.url-star:hover{background:var(--brd);color:var(--t1)}
.url-star.saved{color:var(--star)}
.url-star svg{width:15px;height:15px}

.tool-btn{width:34px;height:34px;display:flex;align-items:center;justify-content:center;border:none;
  background:transparent;color:var(--t2);cursor:pointer;border-radius:50%;flex-shrink:0;margin-left:2px;
  transition:background .15s,color .15s}
.tool-btn:hover{background:var(--input);color:var(--t1)}
.tool-btn svg{width:18px;height:18px}
.tool-btn.active-toggle{color:var(--acc);background:color-mix(in srgb, var(--acc) 14%, transparent)}

#bookmarks-bar{display:flex;align-items:center;gap:4px;padding:4px 12px;background:var(--panel);border-bottom:1px solid var(--brd);min-height:32px}
.bm-item{padding:4px 10px;border-radius:4px;font-size:13px;color:var(--t2);cursor:pointer;white-space:nowrap}
.bm-item:hover{background:var(--input);color:var(--t1)}

#workspace{flex:1;background:var(--panel);overflow:hidden;position:relative}
iframe{width:100%;height:100%;border:none}

#sidebar{position:fixed;right:-320px;top:0;width:320px;height:100vh;background:var(--panel);border-left:1px solid var(--brd);box-shadow:-8px 0 24px rgba(0,0,0,.12);z-index:1000;overflow-y:auto;transition:right .25s ease}
#sidebar.open{right:0}
.sidebar-header{display:flex;justify-content:space-between;align-items:center;padding:18px 20px;border-bottom:1px solid var(--brd);font-weight:700;font-size:15px;position:sticky;top:0;background:var(--panel);z-index:1}
.sidebar-close{width:28px;height:28px;display:flex;align-items:center;justify-content:center;font-size:18px;cursor:pointer;color:var(--t2);line-height:1;background:none;border:none;border-radius:50%;transition:background .15s,color .15s}
.sidebar-close:hover{background:var(--input);color:var(--t1)}
.sidebar-section{padding:14px 20px;border-bottom:1px solid var(--brd)}
.sidebar-section:last-child{border-bottom:none}
.section-title{font-size:11px;color:var(--t3);text-transform:uppercase;letter-spacing:.6px;margin-bottom:10px;font-weight:700}
.row{display:flex;justify-content:space-between;align-items:center;padding:9px 0;font-size:13.5px}
.switch{position:relative;width:36px;height:20px;flex-shrink:0}
.switch input{opacity:0;width:0;height:0}
.slider{position:absolute;cursor:pointer;inset:0;background:var(--brd);transition:.2s;border-radius:20px}
.slider:before{position:absolute;content:"";height:14px;width:14px;left:3px;bottom:3px;background:#fff;transition:.2s;border-radius:50%;box-shadow:0 1px 2px rgba(0,0,0,.25)}
input:checked+.slider{background:var(--acc)}
input:checked+.slider:before{transform:translateX(16px)}

.modal{position:fixed;top:54px;right:14px;width:340px;max-width:92vw;max-height:calc(100vh - 80px);
  overflow-y:auto;background:var(--panel);border:1px solid var(--brd);border-radius:12px;
  box-shadow:0 16px 40px rgba(0,0,0,.18);z-index:1001;padding:18px;
  visibility:hidden;opacity:0;transform:scale(.96) translateY(-6px);transform-origin:top center;
  transition:opacity .16s ease,transform .16s ease,visibility 0s linear .16s}
.modal.show{visibility:visible;opacity:1;transform:scale(1) translateY(0);transition:opacity .16s ease,transform .16s ease}
/* ✅ FIX #17: right dùng làm mặc định; JS (positionModal) sẽ set left/right + --arrow-x
   theo đúng nút vừa bấm, để mũi tên luôn trỏ đúng vào nút mở modal đó */
.modal::before{content:"";position:absolute;top:-6px;right:var(--arrow-x,22px);width:12px;height:12px;
  background:var(--panel);border-left:1px solid var(--brd);border-top:1px solid var(--brd);
  transform:rotate(45deg);border-radius:2px 0 0 0}
.modal-title{font-size:16px;font-weight:700;margin-bottom:14px;color:var(--t1)}
.modal-input{width:100%;padding:10px;margin:8px 0;background:var(--input);border:1px solid var(--brd);border-radius:8px;color:var(--t1);outline:none;font-size:13.5px}
.modal-input:focus{border-color:var(--acc);background:var(--panel)}
.modal-btn{width:100%;padding:10px;margin:4px 0;background:var(--panel);border:1px solid var(--brd);color:var(--t1);cursor:pointer;font-weight:600;border-radius:8px;font-size:13.5px;transition:background .15s,border-color .15s}
.modal-btn:hover{background:var(--input)}
.modal-btn.primary{background:var(--acc);color:var(--on-acc);border-color:var(--acc)}
.modal-btn.primary:hover{background:var(--acc-hover)}

#dev-console{position:fixed;bottom:14px;right:14px;width:420px;height:220px;background:var(--panel);color:var(--t2);border:1px solid var(--brd);border-radius:10px;padding:12px;font-size:11.5px;font-family:"SF Mono",Consolas,Menlo,monospace;z-index:999;display:none;overflow-y:auto;box-shadow:0 16px 40px rgba(0,0,0,.18)}
#dev-console.show{display:block}
.log-entry{margin-bottom:5px;padding-bottom:5px;word-break:break-all;color:var(--t1);border-bottom:1px solid var(--brd)}
.log-entry:last-child{border-bottom:none;margin-bottom:0;padding-bottom:0}

#pass-popup{position:fixed;bottom:20px;right:20px;width:320px;background:var(--panel);border:1px solid var(--brd);border-radius:12px;box-shadow:0 16px 40px rgba(0,0,0,.18);z-index:1002;padding:16px;
  visibility:hidden;opacity:0;transform:translateY(14px) scale(.98);transform-origin:bottom right;
  transition:opacity .18s ease,transform .18s ease,visibility 0s linear .18s}
#pass-popup.show{visibility:visible;opacity:1;transform:translateY(0) scale(1);transition:opacity .18s ease,transform .18s ease}
.popup-header{display:flex;justify-content:space-between;margin-bottom:12px}
.popup-title{font-weight:600;font-size:14px}
.popup-close{cursor:pointer;color:var(--t3);font-size:18px}
.popup-domain{font-size:13px;color:var(--t2);margin-bottom:8px}
.popup-pass{font-family:monospace;background:var(--input);padding:8px;border-radius:4px;margin-bottom:12px;font-size:13px}
.popup-actions{display:flex;gap:8px}
.popup-btn{flex:1;padding:8px;border:1px solid var(--brd);background:var(--panel);color:var(--t1);border-radius:4px;cursor:pointer;font-size:13px}
.popup-btn.primary{background:var(--acc);color:var(--on-acc);border:none}

.history-item{display:block;width:100%;text-align:left;padding:8px;border-bottom:1px solid var(--brd);cursor:pointer;font-size:13px;color:var(--t1)}
.history-item:hover{background:var(--input)}
</style></head><body>
<div id="app">
  <div id="tabs-bar"></div>
  <div id="toolbar">
    <div id="load-bar"></div>
    <button class="nav-btn" id="btn-back" onclick="sr('back')" title="Back (Alt+←)">
      <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M19 12H5M12 19l-7-7 7-7"/></svg>
    </button>
    <button class="nav-btn" id="btn-fwd" onclick="sr('fwd')" title="Forward (Alt+→)">
      <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M5 12h14M12 5l7 7-7 7"/></svg>
    </button>
    <button class="nav-btn" onclick="sr('ref')" title="Reload (Ctrl+R)">
      <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M21 12a9 9 0 1 1-2.64-6.36"/><polyline points="21 3 21 9 15 9"/></svg>
    </button>
    <div class="toolbar-gap"></div>
    <div class="url-wrap">
      <span class="url-icon" title="Shields active">
        <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M12 2l8 3.5v5.5c0 5-3.4 8.6-8 10-4.6-1.4-8-5-8-10V5.5L12 2z"/></svg>
      </span>
      <input type="text" id="url-bar" data-i18n-placeholder="url_ph" placeholder="Search or type URL" onkeydown="if(event.key==='Enter')sr('nav',this.value)">
      <button class="url-star" id="star-btn" onclick="sr('bookmark', (tabs[activeTab]&&tabs[activeTab].url)||'')" data-i18n-title="bookmark" title="Bookmark">
        <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M12 2l3.09 6.26L22 9.27l-5 4.87L18.18 21 12 17.77 5.82 21 7 14.14l-5-4.87 6.91-1.01L12 2z"/></svg>
      </button>
    </div>
    <button class="tool-btn" onclick="toggleModal('history-modal',this)" data-i18n-title="history" title="History (Ctrl+H)">
      <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="12" r="9"/><polyline points="12 7 12 12 15.5 14"/></svg>
    </button>
    <button class="tool-btn" onclick="toggleModal('vault',this)" data-i18n-title="vault" title="Vault">
      <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><rect x="4" y="11" width="16" height="9" rx="2"/><path d="M8 11V7a4 4 0 0 1 8 0v4"/></svg>
    </button>
    <button class="tool-btn" onclick="toggleModal('ai-modal',this)" data-i18n-title="ai" title="AI Assistant">
      <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M12 3l1.8 5.3L19 10l-5.2 1.8L12 17l-1.8-5.2L5 10l5.2-1.7L12 3z"/><path d="M19 3.5l.5 1.4 1.4.5-1.4.5-.5 1.4-.5-1.4-1.4-.5 1.4-.5z"/></svg>
    </button>
    <button class="tool-btn" onclick="openExtensions(this)" data-i18n-title="extensions" title="Extensions">
      <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><rect x="3" y="3" width="7" height="7" rx="1.5"/><rect x="14" y="3" width="7" height="7" rx="1.5"/><rect x="3" y="14" width="7" height="7" rx="1.5"/><rect x="14" y="14" width="7" height="7" rx="1.5"/></svg>
    </button>
    <button class="tool-btn" onclick="toggleTheme()" id="theme-btn" data-i18n-title="theme" title="Toggle theme (Ctrl+Shift+L)">
      <svg id="iconSun" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round"><circle cx="12" cy="12" r="4.5"/><path d="M12 2v2.5M12 19.5V22M4.2 4.2l1.8 1.8M18 18l1.8 1.8M2 12h2.5M19.5 12H22M4.2 19.8L6 18M18 6l1.8-1.8"/></svg>
      <svg id="iconMoon" style="display:none" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M20 14.5A8.5 8.5 0 1 1 9.5 4a6.8 6.8 0 0 0 10.5 10.5z"/></svg>
    </button>
    <button class="tool-btn" onclick="toggleSidebar()" data-i18n-title="menu" title="Menu">
      <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><line x1="3" y1="6" x2="21" y2="6"/><line x1="3" y1="12" x2="21" y2="12"/><line x1="3" y1="18" x2="21" y2="18"/></svg>
    </button>
  </div>
  <div id="bookmarks-bar"><div class="bm-empty" data-i18n="empty_bm" style="color:var(--t3);font-size:13px;padding:4px 10px;">No bookmarks yet. Click the star to save this page.</div></div>

  <div id="workspace"></div>
  <div id="dev-console"></div>
  <div id="sidebar">
    <div class="sidebar-header">
      <span data-i18n="settings">Nexus Settings</span>
      <button class="sidebar-close" onclick="toggleSidebar()">&times;</button>
    </div>
    <div class="sidebar-section"><div class="section-title" data-i18n="general">GENERAL</div>
      <div class="row"><span data-i18n="lang_row">Tiếng Việt</span><label class="switch"><input type="checkbox" id="lang-toggle" onchange="toggleLang()"><span class="slider"></span></label></div>
      <div class="row"><span data-i18n="console">Developer Console</span><label class="switch"><input type="checkbox" id="console-toggle" onchange="document.getElementById('dev-console').classList.toggle('show', this.checked)"><span class="slider"></span></label></div>
    </div>
    <div class="sidebar-section"><div class="section-title" data-i18n="connection">CONNECTION</div>
      <div class="row"><span data-i18n="warp">Cloudflare WARP</span><label class="switch"><input type="checkbox" id="warp-toggle" onchange="ts('warp',this.checked)"><span class="slider"></span></label></div>
      <div class="row"><span data-i18n="tor">Tor Network</span><label class="switch"><input type="checkbox" id="tor-toggle" onchange="ts('tor',this.checked)"><span class="slider"></span></label></div>
    </div>
    <div class="sidebar-section"><div class="section-title" data-i18n="shields">SHIELDS</div>
      <div class="row"><span data-i18n="ad">Ad Blocker</span><label class="switch"><input type="checkbox" checked onchange="ts('ad',this.checked)"><span class="slider"></span></label></div>
      <div class="row"><span data-i18n="trk">Tracker Block</span><label class="switch"><input type="checkbox" checked onchange="ts('trk',this.checked)"><span class="slider"></span></label></div>
      <div class="row"><span data-i18n="cookie">Cookie Shield</span><label class="switch"><input type="checkbox" checked onchange="ts('cookie',this.checked)"><span class="slider"></span></label></div>
      <div class="row"><span data-i18n="sink">Domain Sinkhole</span><label class="switch"><input type="checkbox" checked onchange="ts('sink',this.checked)"><span class="slider"></span></label></div>
      <div class="row"><span data-i18n="anti_fp">Anti-Fingerprint</span><label class="switch"><input type="checkbox" checked onchange="ts('anti_fp',this.checked)"><span class="slider"></span></label></div>
    </div>
    <div class="sidebar-section"><div class="section-title" data-i18n="passwords">PASSWORDS</div>
      <div class="row"><span data-i18n="auto_save">Auto Save</span><label class="switch"><input type="checkbox" checked onchange="ts('auto-save',this.checked)"><span class="slider"></span></label></div>
      <div class="row"><span data-i18n="pass_suggest">Password Suggest</span><label class="switch"><input type="checkbox" checked onchange="ts('pass-suggest',this.checked)"><span class="slider"></span></label></div>
    </div>
    <div class="sidebar-section"><div class="section-title" data-i18n="sync">SYNC</div>
      <div class="row"><span>Chrome</span><label class="switch"><input type="checkbox" onchange="ts('sync-chrome',this.checked)"><span class="slider"></span></label></div>
      <div class="row"><span>Firefox</span><label class="switch"><input type="checkbox" onchange="ts('sync-firefox',this.checked)"><span class="slider"></span></label></div>
      <div class="row"><span>Edge</span><label class="switch"><input type="checkbox" onchange="ts('sync-edge',this.checked)"><span class="slider"></span></label></div>
      <button class="modal-btn primary" onclick="sr('sync-now')" data-i18n="sync_now">Sync Now</button>
    </div>
  </div>

  <div id="history-modal" class="modal">
    <div class="modal-title" data-i18n="history_title">History</div>
    <div id="history-list" style="max-height:300px;overflow-y:auto;margin-bottom:20px;"></div>
    <button class="modal-btn" onclick="toggleModal('history-modal')" data-i18n="close">Close</button>
  </div>

  <div id="vault" class="modal">
    <div class="modal-title" data-i18n="vault_title">Vault</div>
    <input type="password" id="v-master" class="modal-input" data-i18n-placeholder="master_ph" placeholder="Master Password">
    <input type="text" id="v-domain" class="modal-input" data-i18n-placeholder="domain_ph" placeholder="Domain">
    <input type="text" id="v-user" class="modal-input" data-i18n-placeholder="user_ph" placeholder="Username">
    <input type="password" id="v-pass" class="modal-input" data-i18n-placeholder="pass_ph" placeholder="Password">
    <button class="modal-btn primary" onclick="vAct('save')" data-i18n="save">Save</button>
    <button class="modal-btn" onclick="vAct('get')" data-i18n="retrieve">Retrieve</button>
    <button class="modal-btn" onclick="vAct('gen')" data-i18n="gen">Generate</button>
    <button class="modal-btn" onclick="toggleModal('vault')" data-i18n="close">Close</button>
    <div id="v-res" style="margin-top:12px;font-size:13px;color:var(--t2)"></div>
  </div>

  <div id="ai-modal" class="modal">
    <div class="modal-title" data-i18n="ai_title">AI Assistant</div>
    <input type="text" id="ai-endpoint" class="modal-input" placeholder="API Endpoint">
    <input type="password" id="ai-key" class="modal-input" placeholder="API Key">
    <input type="text" id="ai-model" class="modal-input" placeholder="Model (e.g., gpt-4o-mini)">
    <button class="modal-btn primary" onclick="aiCfg()" data-i18n="save">Save</button>
    <textarea id="ai-prompt" class="modal-input" rows="3" data-i18n-placeholder="ask_ph" placeholder="Ask anything..."></textarea>
    <button class="modal-btn" onclick="aiAsk()" data-i18n="ask">Ask</button>
    <div id="ai-log" style="margin-top:12px;max-height:200px;overflow-y:auto;font-size:13px"></div>
    <button class="modal-btn" onclick="toggleModal('ai-modal')" data-i18n="close">Close</button>
  </div>

  <div id="ext-modal" class="modal">
    <div class="modal-title" data-i18n="extensions">Extensions</div>
    <div id="ext-list" style="max-height:320px;overflow-y:auto;margin-bottom:16px;"></div>
    <button class="modal-btn" onclick="toggleModal('ext-modal')" data-i18n="close">Close</button>
  </div>

  <div id="pass-popup">
    <div class="popup-header"><div class="popup-title" data-i18n="save_pass">Save Password?</div><span class="popup-close" onclick="hidePassPopup()">&times;</span></div>
    <div class="popup-domain" id="suggest-domain"></div>
    <div class="popup-pass" id="suggest-pass"></div>
    <div class="popup-actions">
      <button class="popup-btn primary" onclick="savePassPopup()" data-i18n="save">Save</button>
      <button class="popup-btn" id="gen-pass-btn" onclick="genPassPopup()" data-i18n="gen_new">Generate New</button>
    </div>
  </div>
</div>
<script>
let tabs = [{name:'New Tab', url:'nexus://home', frozen:false}];
let activeTab = 0;
let currentMasterPass = '';
let lang = 'en';

const i18n = {
  en: {
    url_ph: "Search or type URL", bookmark: "Bookmark", history: "History (Ctrl+H)", vault: "Vault", ai: "AI Assistant", console: "Developer Console", menu: "Menu", extensions: "Extensions", theme: "Toggle theme (Ctrl+Shift+L)", general: "GENERAL", lang_row: "Vietnamese",
    empty_bm: "No bookmarks yet. Click the star to save this page.",
    settings: "Nexus Settings", connection: "CONNECTION", warp: "Cloudflare WARP", tor: "Tor Network",
    shields: "SHIELDS", ad: "Ad Blocker", trk: "Tracker Block", cookie: "Cookie Shield", sink: "Domain Sinkhole", anti_fp: "Anti-Fingerprint",
    passwords: "PASSWORDS", auto_save: "Auto Save", pass_suggest: "Password Suggest",
    sync: "SYNC", sync_now: "Sync Now",
    history_title: "History", empty_hist: "No history yet.", no_ext: "No extensions installed.",
    vault_title: "Vault", master_ph: "Master Password", domain_ph: "Domain", user_ph: "Username", pass_ph: "Password",
    save: "Save", retrieve: "Retrieve", gen: "Generate", close: "Close",
    ai_title: "AI Assistant", ask_ph: "Ask anything...", ask: "Ask",
    save_pass: "Save Password?", gen_new: "Generate New",
    saved_bm: "Saved to bookmarks", err_save_bm: "Cannot save this page",
    master_req: "Please enter Master Password in Vault before saving!", synced: "Synced: Chrome({}), Firefox({}), Edge({})"
  },
  vi: {
    url_ph: "Tìm kiếm hoặc nhập URL", bookmark: "Lưu trang", history: "Lịch sử (Ctrl+H)", vault: "Kho mật khẩu", ai: "Trợ lý AI", console: "Developer Console", menu: "Menu", extensions: "Tiện ích mở rộng", theme: "Đổi giao diện (Ctrl+Shift+L)", general: "CHUNG", lang_row: "Tiếng Việt",
    empty_bm: "Chưa có dấu trang. Bấm biểu tượng ngôi sao để lưu trang này.",
    settings: "Cài đặt Nexus", connection: "KẾT NỐI", warp: "Cloudflare WARP", tor: "Mạng Tor",
    shields: "LÁ CHẮN", ad: "Chặn Quảng cáo", trk: "Chặn Tracker", cookie: "Bảo vệ Cookie", sink: "Chặn Domain", anti_fp: "Anti-Fingerprint",
    passwords: "MẬT KHẨU", auto_save: "Tự động lưu", pass_suggest: "Gợi ý mật khẩu",
    sync: "ĐỒNG BỘ HÒA", sync_now: "Đồng bộ ngay",
    history_title: "Lịch sử duyệt web", empty_hist: "Chưa có lịch sử.", no_ext: "Chưa có tiện ích mở rộng nào.",
    vault_title: "Kho Mật Khẩu", master_ph: "Mật khẩu chính", domain_ph: "Tên miền", user_ph: "Tên đăng nhập", pass_ph: "Mật khẩu",
    save: "Lưu", retrieve: "Lấy mật khẩu", gen: "Tạo mật khẩu", close: "Đóng",
    ai_title: "Trợ lý AI", ask_ph: "Nhập câu hỏi...", ask: "Hỏi AI",
    save_pass: "Lưu mật khẩu?", gen_new: "Tạo mới",
    saved_bm: "Đã lưu trang vào Bookmark", err_save_bm: "Không thể lưu trang này",
    master_req: "Vui lòng nhập Master Password trong Vault trước khi lưu!", synced: "Đồng bộ: Chrome({}), Firefox({}), Edge({})"
  }
};

function applyLang() {
  document.querySelectorAll('[data-i18n]').forEach(el => { const k = el.getAttribute('data-i18n'); if(i18n[lang][k]) el.textContent = i18n[lang][k]; });
  document.querySelectorAll('[data-i18n-placeholder]').forEach(el => { const k = el.getAttribute('data-i18n-placeholder'); if(i18n[lang][k]) el.placeholder = i18n[lang][k]; });
  document.querySelectorAll('[data-i18n-title]').forEach(el => { const k = el.getAttribute('data-i18n-title'); if(i18n[lang][k]) el.title = i18n[lang][k]; });
  const langToggle = document.getElementById('lang-toggle');
  if (langToggle) langToggle.checked = lang === 'vi';
}
function toggleLang() { lang = lang === 'en' ? 'vi' : 'en'; applyLang(); }

function applyTheme(theme) {
  document.documentElement.setAttribute('data-theme', theme);
  document.getElementById('iconSun').style.display = theme === 'dark' ? 'none' : 'block';
  document.getElementById('iconMoon').style.display = theme === 'dark' ? 'block' : 'none';
  try { localStorage.setItem('nexus-theme', theme); } catch(e) {}
}
function toggleTheme() {
  const cur = document.documentElement.getAttribute('data-theme') === 'dark' ? 'dark' : 'light';
  applyTheme(cur === 'dark' ? 'light' : 'dark');
}
function initTheme() {
  let saved = null;
  try { saved = localStorage.getItem('nexus-theme'); } catch(e) {}
  if (saved === 'dark' || saved === 'light') { applyTheme(saved); return; }
  applyTheme(window.matchMedia && window.matchMedia('(prefers-color-scheme: dark)').matches ? 'dark' : 'light');
}

function escHtml(s) { return String(s).replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;').replace(/"/g,'&quot;').replace(/'/g,'&#39;'); }
function escAttr(s) { return String(s).replace(/&/g,'&amp;').replace(/"/g,'&quot;').replace(/'/g,'&#39;'); }

function tabLetter(name) {
  const c = String(name || '?').trim().replace(/^https?:\/\//, '').charAt(0);
  return c ? c.toUpperCase() : '?';
}
function renderTabs() {
  const closeIcon = '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round"><line x1="18" y1="6" x2="6" y2="18"/><line x1="6" y1="6" x2="18" y2="18"/></svg>';
  document.getElementById('tabs-bar').innerHTML = tabs.map((t,i)=>`
    <div class="tab ${i===activeTab?'active':''} ${t.frozen?'frozen':''}" onclick="switchTab(${i})">
      <span class="tab-favicon">${t.frozen?'❄':escHtml(tabLetter(t.name))}</span>
      <span class="tab-title">${escHtml(t.name)}</span>
      <span class="tab-close" onclick="closeTab(${i},event)">${closeIcon}</span>
    </div>`).join('')
    + `<div id="new-tab-btn" onclick="newTab('normal')" title="New Tab"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round"><line x1="12" y1="5" x2="12" y2="19"/><line x1="5" y1="12" x2="19" y2="12"/></svg></div>`
    + `<div id="new-incognito-btn" onclick="newTab('incognito')" title="Incognito"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M17.9 17.9A10.9 10.9 0 0 1 12 20c-7 0-11-8-11-8a21.4 21.4 0 0 1 4.2-5.5M9.9 4.2A10.8 10.8 0 0 1 12 4c7 0 11 8 11 8a21.4 21.4 0 0 1-2.6 3.9M14 14.2a3 3 0 1 1-4.2-4.2"/><line x1="2" y1="2" x2="22" y2="22"/></svg></div>`;
}
function newTab(m) { sr('new-tab',m); }
function closeTab(i,e) { e.stopPropagation(); if(tabs.length>1) sr('close-tab',i); }
function switchTab(i) { sr('switch-tab',i); }

let bookmarksList = [];
// ✅ FIX #18: .url-star.saved đã có CSS sẵn nhưng chưa bao giờ được bật —
// nút bookmark giờ sẽ tô vàng khi trang hiện tại đã có trong danh sách lưu.
function updateStarState() {
  const cur = (tabs[activeTab] && tabs[activeTab].url) || '';
  const star = document.getElementById('star-btn');
  if (star) star.classList.toggle('saved', bookmarksList.some(b => b.url === cur));
}
function renderBookmarks(bms) {
  bookmarksList = bms || [];
  const bar = document.getElementById('bookmarks-bar');
  if(!bms || bms.length === 0) {
    bar.innerHTML = `<div class="bm-empty" data-i18n="empty_bm" style="color:var(--t3);font-size:13px;padding:4px 10px;">${i18n[lang].empty_bm}</div>`;
  } else {
    bar.innerHTML = bms.map(b => `<div class="bm-item" onclick="sr('nav','${escAttr(b.url)}')">${escHtml(b.title)}</div>`).join('');
  }
  updateStarState();
}

function renderHistory(hist) {
  const list = document.getElementById('history-list');
  if(!hist || hist.length === 0) {
    list.innerHTML = `<p style="color:var(--t2)">${i18n[lang].empty_hist}</p>`;
    return;
  }
  list.innerHTML = hist.slice().reverse().map(h => `<div class="history-item" onclick="sr('nav','${escAttr(h.url)}');toggleModal('history-modal')">${escHtml(h.title)} <span style="color:var(--t3);font-size:11px;">(${new Date(h.time*1000).toLocaleString()})</span></div>`).join('');
}

function openExtensions(btn){ sr('ext-list'); toggleModal('ext-modal', btn); }
function renderExtensions(list){
  const c = document.getElementById('ext-list');
  if(!list || list.length===0){ c.innerHTML = `<p style="color:var(--t2)">${i18n[lang].no_ext}</p>`; return; }
  c.innerHTML = list.map((e,i)=>`
    <div class="row" style="align-items:flex-start;flex-direction:column;padding:10px 0;border-bottom:1px solid var(--brd)">
      <div style="display:flex;justify-content:space-between;width:100%;align-items:center">
        <div><b>${escHtml(e.name)}</b> <span style="color:var(--t3);font-size:11px">v${escHtml(e.version)}</span></div>
        <label class="switch"><input type="checkbox" data-ext-idx="${i}" ${e.enabled?'checked':''} onchange="toggleExt(${i},this.checked)"><span class="slider"></span></label>
      </div>
      <div style="color:var(--t2);font-size:12px;margin-top:4px">${escHtml(e.description||'')}</div>
    </div>`).join('');
  window._extList = list;
}
function toggleExt(i,enabled){ const e=(window._extList||[])[i]; if(e) sr('ext-toggle',{id:e.id,enabled}); }

function showLoading(){ const b=document.getElementById('load-bar'); b.style.width='0'; b.classList.add('show'); requestAnimationFrame(()=>{ requestAnimationFrame(()=>{ b.style.width='75%'; }); }); }
function hideLoading(){ const b=document.getElementById('load-bar'); b.style.width='100%'; setTimeout(()=>{ b.classList.remove('show'); setTimeout(()=>{ b.style.width='0'; }, 200); }, 150); }

function sr(a,p){window.ipc&&window.ipc.postMessage(JSON.stringify({a,p}))}
function ts(k,v){sr('shld',{s:k,v:v})}
function v(id){return document.getElementById(id).value}
// ✅ FIX #17: định vị modal ngay dưới nút vừa bấm, kẹp trong viewport,
// và đặt --arrow-x để mũi tên trỏ đúng vào giữa nút đó.
function positionModal(modal, btn) {
  if (!btn) { modal.style.left = ''; modal.style.right = '14px'; modal.style.removeProperty('--arrow-x'); return; }
  const r = btn.getBoundingClientRect();
  const mw = modal.offsetWidth || 340;
  let left = Math.round(r.left + r.width / 2 - mw / 2);
  left = Math.max(10, Math.min(left, window.innerWidth - mw - 10));
  modal.style.left = left + 'px';
  modal.style.right = 'auto';
  const arrowFromRight = (left + mw) - (r.left + r.width / 2) - 6;
  modal.style.setProperty('--arrow-x', Math.max(14, Math.min(arrowFromRight, mw - 34)) + 'px');
}
function toggleModal(id, btn){
  const target = document.getElementById(id);
  const willOpen = !target.classList.contains('show');
  document.querySelectorAll('.modal.show').forEach(m => { if (m.id !== id) m.classList.remove('show'); });
  if (willOpen) positionModal(target, btn);
  target.classList.toggle('show', willOpen);
}
document.addEventListener('click', function(e) {
  const openModal = document.querySelector('.modal.show');
  if (openModal && !openModal.contains(e.target) && !e.target.closest('.tool-btn')) {
    openModal.classList.remove('show');
  }
}, true);
function toggleSidebar(){document.getElementById('sidebar').classList.toggle('open')}
function lg(m,t){const c=document.getElementById('dev-console');c.innerHTML=`<div class="log-entry">[${new Date().toLocaleTimeString()}] ${m}</div>`+c.innerHTML}
// ✅ FIX #21: currentMasterPass trước đây không bao giờ được gán -> popup lưu
// mật khẩu nhanh luôn báo "chưa nhập Master Password" dù đã nhập trong Vault.
function vAct(a){
  const m = v('v-master');
  if (m) currentMasterPass = m;
  sr('vault',{a,m,d:v('v-domain'),u:v('v-user'),p:v('v-pass')});
}
function vRes(t){document.getElementById('v-res').textContent=t}
function aiCfg(){sr('ai_cfg',{e:v('ai-endpoint'),k:v('ai-key'),m:v('ai-model')})}
function aiAsk(){const q=v('ai-prompt');if(q){sr('ai',q);document.getElementById('ai-prompt').value=''}}
function addAi(t){document.getElementById('ai-log').innerHTML+=`<div style="margin:4px 0;padding:6px;background:var(--input);border-radius:4px">${t}</div>`}

function showPassPopup(d) {
  try { document.getElementById('suggest-domain').textContent = new URL(d.url).hostname; } catch(e) { document.getElementById('suggest-domain').textContent = d.url; }
  document.getElementById('suggest-pass').textContent = '•'.repeat(d.password.length);
  // ✅ FIX #16: setting "Password Suggest" giờ thực sự điều khiển nút này
  document.getElementById('gen-pass-btn').style.display = d.suggest === false ? 'none' : '';
  window.passData = d;
  document.getElementById('pass-popup').classList.add('show');
}
function hidePassPopup() { document.getElementById('pass-popup').classList.remove('show'); }
function savePassPopup() {
  if (window.passData) {
    if (!currentMasterPass) { alert(i18n[lang].master_req); toggleModal('vault'); return; }
    sr('save-password', {url: window.passData.url, username: window.passData.username, password: window.passData.password, master: currentMasterPass});
    hidePassPopup();
  }
}
// ✅ FIX #5: nexusGeneratePassword chỉ có trong iframe → tự generate trên main page
function genPassPopup() {
  if (window.passData) {
    const charset = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789!@#$%^&*";
    const arr = crypto.getRandomValues(new Uint8Array(16));
    const p = Array.from(arr, n => charset[n % charset.length]).join('');
    document.getElementById('suggest-pass').textContent = p;
    window.passData.password = p;
    sr('fill-password', {url: window.passData.url, username: window.passData.username, password: p});
  }
}

window.addEventListener('message',function(event) {
  try {
    const data = JSON.parse(event.data);
    if (data.a === 'update-tabs') updateTabs(data.p);
    else if (data.a === 'update-bookmarks') renderBookmarks(data.p);
    else if (data.a === 'update-history') renderHistory(data.p);
    else if (data.a === 'password-detected') showPassPopup(data.p);
    else if (data.a === 'nav-internal') sr('nav-internal', data.p);
    else if (data.a === 'nav-post') sr('nav-post', data.p);
    else if (data.a === 'new-tab-url') sr('new-tab-url', data.p);
    else if (data.a === 'console-log') lg(data.p);
    else if (data.a === 'inc') sr('inc', '');
    else if (data.a === 'ext-list-response') renderExtensions(data.p);
    else if (data.a === 'ext-toggle-response') {}
  } catch (e) {}
});

window.updateTabs = function(d) {
  tabs = d.tabs; activeTab = d.activeTab; renderTabs();
  let url = tabs[activeTab].url;
  document.getElementById('url-bar').value = url === 'nexus://home' ? '' : url;
  updateStarState();
}

function closeTopmostOverlay() {
  const openModal = document.querySelector('.modal.show');
  if (openModal) { openModal.classList.remove('show'); return true; }
  if (document.getElementById('sidebar').classList.contains('open')) { toggleSidebar(); return true; }
  if (document.getElementById('pass-popup').classList.contains('show')) { hidePassPopup(); return true; }
  if (document.getElementById('dev-console').classList.contains('show')) { document.getElementById('dev-console').classList.remove('show'); return true; }
  return false;
}

document.addEventListener('keydown', function(e) {
  const typingInField = /^(input|textarea)$/i.test(document.activeElement.tagName);
  const mod = e.ctrlKey || e.metaKey;

  if (e.key === 'Escape') { closeTopmostOverlay(); return; }

  if (mod && e.shiftKey && (e.key === 'L' || e.key === 'l')) { e.preventDefault(); toggleTheme(); return; }
  if (mod && e.shiftKey && (e.key === 'N' || e.key === 'n')) { e.preventDefault(); newTab('incognito'); return; }
  if (mod && (e.key === 't' || e.key === 'T')) { e.preventDefault(); newTab('normal'); return; }
  if (mod && (e.key === 'w' || e.key === 'W')) { e.preventDefault(); if (tabs.length > 1) sr('close-tab', activeTab); return; }
  if (mod && (e.key === 'l' || e.key === 'L')) { e.preventDefault(); const b = document.getElementById('url-bar'); b.focus(); b.select(); return; }
  if (mod && (e.key === 'h' || e.key === 'H')) { e.preventDefault(); toggleModal('history-modal'); return; }
  if (mod && (e.key === 'r' || e.key === 'R')) { e.preventDefault(); sr('ref'); return; }
  if (!typingInField && e.key === 'F5') { e.preventDefault(); sr('ref'); return; }
  if (e.altKey && e.key === 'ArrowLeft') { e.preventDefault(); sr('back'); return; }
  if (e.altKey && e.key === 'ArrowRight') { e.preventDefault(); sr('fwd'); return; }
  if (!typingInField && mod && e.key >= '1' && e.key <= '9') {
    e.preventDefault();
    const idx = e.key === '9' ? tabs.length - 1 : Math.min(parseInt(e.key,10) - 1, tabs.length - 1);
    switchTab(idx);
  }
});

initTheme();
applyLang();
renderTabs();
</script></body></html>"###.into()
}

// ======================
// RENDER PAGE
// ======================
// ✅ FIX #7: Revoke Blob URL sau khi iframe load xong → tránh memory leak
fn render_page(html_out: &str, url: &str, px: &tao::event_loop::EventLoopProxy<Ev>) {
    if let (Ok(h), Ok(u)) = (serde_json::to_string(html_out), serde_json::to_string(url)) {
        let _ = px.send_event(Ev::Js(format!(
            "let w=document.getElementById('workspace');w.innerHTML='';let f=document.createElement('iframe');f.sandbox='allow-scripts allow-same-origin allow-forms allow-presentation allow-popups';f.style='width:100%;height:100%;border:none;background:var(--panel);';let b=new Blob([{0}],{{type:'text/html'}});let blobUrl=URL.createObjectURL(b);f.onload=function(){{URL.revokeObjectURL(blobUrl)}};f.src=blobUrl;w.appendChild(f);",
            h
        )));
        let _ = px.send_event(Ev::Js(format!("document.getElementById('url-bar').value={};", u)));
        let _ = px.send_event(Ev::Js("hideLoading();".into()));
    }
}

async fn commit_render(html: &str, url: &str, tab_idx: usize, my_gen: u64, st: &Arc<RwLock<state::State>>, px: &tao::event_loop::EventLoopProxy<Ev>) {
    let mut g = st.write().await;
    if let Some(t) = g.tabs.get_mut(tab_idx) {
        if t.load_gen == my_gen {
            t.last_html = Some(html.to_string());
            drop(g);
            render_page(html, url, px);
        }
    }
}

// ======================
// LOAD URL
// ======================
async fn load_url(url: String, tab_idx: usize, st: Arc<RwLock<state::State>>, px: &tao::event_loop::EventLoopProxy<Ev>, record: bool) {
    load_url_method(url, tab_idx, "GET", None, st, px, record).await;
}

async fn load_url_method(url: String, tab_idx: usize, method: &str, body: Option<serde_json::Value>, st: Arc<RwLock<state::State>>, px: &tao::event_loop::EventLoopProxy<Ev>, record: bool) {
    let url = {
        if let Ok(parsed) = url::Url::parse(&url) {
            let is_ddg_redirect = matches!(parsed.host_str(), Some("duckduckgo.com") | Some("www.duckduckgo.com"))
                && parsed.path() == "/l/";
            if is_ddg_redirect {
                parsed.query_pairs().find(|(k, _)| k == "uddg").map(|(_, v)| v.into_owned()).unwrap_or(url)
            } else { url }
        } else { url }
    };

    let (cfg, my_gen) = {
        let mut g = st.write().await;
        match g.tabs.get_mut(tab_idx) {
            Some(t) => { t.load_gen += 1; (t.cfg.clone(), t.load_gen) }
            None => return,
        }
    };
    let load_started_safe = url.replace('\'', "\\'").replace('\n', " ");

    if url != "nexus://home" {
        let proxy_note = if cfg.tor { " via Tor" } else if cfg.warp { " via WARP" } else { "" };
        let _ = px.send_event(Ev::Js("let w=document.getElementById('workspace');w.innerHTML='<div style=\"display:flex;justify-content:center;align-items:center;height:100vh;background:var(--panel);color:var(--t3)\">Loading...</div>';".into()));
        let _ = px.send_event(Ev::Js(format!("document.getElementById('url-bar').value='{}';", url.replace('\'', "\\'").replace('\n', " "))));
        let _ = px.send_event(Ev::Js(format!("lg('→ loading {}{}'); showLoading();", load_started_safe, proxy_note)));
    }

    if url == "nexus://home" {
        let home_html = r#"
        <!DOCTYPE html><html><head><meta charset="UTF-8">
        <script>
        // ✅ FIX #20: iframe workspace được tạo từ Blob URL nên kế thừa cùng origin
        // với trang chủ -> đọc chung được localStorage. Đồng bộ đúng theme người
        // dùng đã chọn thủ công (nexus-theme) thay vì chỉ đoán theo OS, và áp
        // dụng TRƯỚC khi vẽ để không bị nháy sai màu.
        (function(){
            var t = null;
            try { t = localStorage.getItem('nexus-theme'); } catch(e) {}
            if (t !== 'dark' && t !== 'light') {
                t = (window.matchMedia && window.matchMedia('(prefers-color-scheme: dark)').matches) ? 'dark' : 'light';
            }
            document.documentElement.setAttribute('data-theme', t);
        })();
        </script>
        <style>
        :root{--bg:#ffffff;--t1:#202124;--t2:#5f6368;--brd:#dadce0;--acc:#1a73e8;--panel:#f1f3f4}
        :root[data-theme="dark"]{--bg:#1a1a1e;--t1:#e8eaed;--t2:#9aa0a6;--brd:#3a3a40;--acc:#8ab4f8;--panel:#2f2f35}
        *{box-sizing:border-box}
        body{margin:0;height:100vh;display:flex;flex-direction:column;align-items:center;justify-content:center;background:var(--bg);color:var(--t1);font-family:-apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,sans-serif}
        .logo{display:flex;align-items:center;gap:14px;margin-bottom:28px}
        .logo svg{width:46px;height:46px;color:var(--acc)}
        h1{font-size:2.6rem;font-weight:600;letter-spacing:-.5px;margin:0}
        .search-wrap{width:100%;max-width:580px;padding:0 20px}
        .search{width:100%;padding:14px 20px;border-radius:26px;border:1px solid var(--brd);box-shadow:0 1px 6px rgba(0,0,0,.08);font-size:15px;outline:none;background:var(--panel);color:var(--t1)}
        .search:focus{border-color:var(--acc)}
        .hint{margin-top:16px;font-size:12.5px;color:var(--t2);text-align:center}
        </style></head><body>
        <div class="logo">
        <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M12 2l8 3.5v5.5c0 5-3.4 8.6-8 10-4.6-1.4-8-5-8-10V5.5L12 2z"/></svg>
        <h1>Nexus</h1>
        </div>
        <div class="search-wrap">
        <input type="text" class="search" placeholder="Search the web..." autofocus onkeydown="if(event.key==='Enter'&&this.value.trim()) window.top.postMessage(JSON.stringify({a:'nav-internal', p: this.value}), '*')">
        <div class="hint">Shields, Vault &amp; AI are one click away in the toolbar above.</div>
        </div>
        </body></html>
        "#;
        render_page(home_html, &url, px);
        if record {
            let mut g = st.write().await;
            if let Some(t) = g.tabs.get_mut(tab_idx) {
                t.push_hist(url.clone());
                t.url = url;
                t.name = "New Tab".into();
                t.last_html = Some(home_html.to_string());
            }
            update_tabs(&g, px);
        }
        return;
    }

    if cfg.sinkhole && sinkhole::check(&url) {
        let safe_url = url.replace('\'', "\\'").replace('\n', " ");
        let _ = px.send_event(Ev::Js(format!("lg('SINKHOLE blocked: {}'); hideLoading();", safe_url)));
        let blocked = { let mut g = st.write().await; g.blocked += 1; g.blocked };
        let _ = px.send_event(Ev::Js(format!("lg('Total blocked: {}');", blocked)));
        return;
    }

    let client = {
        let mut g = st.write().await;
        match g.tabs.get_mut(tab_idx) {
            Some(t) => { t.update_client(); t.client.clone().unwrap_or_else(reqwest::Client::new) }
            None => return,
        }
    };

    let secure_url = if url.starts_with("http://") && !url.contains("localhost") && !url.contains("127.0.0.1") {
        url.replace("http://", "https://")
    } else { url.clone() };

    let clean_url = if let Ok(mut parsed_url) = Url::parse(&secure_url) {
        let mut query_pairs: Vec<(String, String)> = Vec::new();
        for (k, v) in parsed_url.query_pairs() {
            if !k.starts_with("utm_") && k != "fbclid" && k != "gclid" && k != "msclkid" {
                query_pairs.push((k.into_owned(), v.into_owned()));
            }
        }
        parsed_url.query_pairs_mut().clear().extend_pairs(query_pairs);
        parsed_url.to_string()
    } else { secure_url.clone() };

    let req = if method == "POST" {
        let mut form = HashMap::new();
        if let Some(b) = body {
            if let Some(obj) = b.as_object() {
                for (k, v) in obj {
                    let val_str = if let Some(s) = v.as_str() { s.to_string() } else { v.to_string() };
                    form.insert(k.clone(), val_str);
                }
            }
        }
        client.post(&clean_url).form(&form)
    } else {
        client.get(&clean_url)
    };

    let t_start = std::time::Instant::now();
    let response = req
        .header("Accept", "text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,*/*;q=0.8")
        .header("Accept-Language", "en-US,en;q=0.9,vi;q=0.8")
        .header("Accept-Encoding", "identity")
        .header("DNT", "1")
        .send().await;
    let elapsed_ms = t_start.elapsed().as_millis();
    let err_detail = response.as_ref().err().map(|e| e.to_string()).unwrap_or_default();

    if let Ok(r) = response {
        let _ = px.send_event(Ev::Js(format!("lg('← {} in {}ms — {}');", r.status().as_u16(), elapsed_ms, load_started_safe)));
        let status = r.status();
        let content_type = r.headers().get(reqwest::header::CONTENT_TYPE)
            .and_then(|v| v.to_str().ok()).unwrap_or("text/html").to_lowercase();

        if content_type.contains("text/html") || content_type.contains("text/plain") {
            match r.text().await {
                Ok(h) => {
                let safe_url = clean_url.replace('&', "&amp;").replace('"', "&quot;");
                let shield = injection::get_security_payload(&cfg);
                let inj = format!(r#"<base href="{}">{}"#, safe_url, shield);

                let lower_h = h.to_ascii_lowercase();
                let mut html_out = if let Some(start) = lower_h.find("<head>") {
                    let pos = start + 6;
                    format!("{}{}{}", &h[..pos], inj, &h[pos..])
                } else if let Some(start) = lower_h.find("<head ") {
                    let pos = h[start..].find('>').map(|e| start + e + 1).unwrap_or(start);
                    format!("{}{}{}", &h[..pos], inj, &h[pos..])
                } else { format!("{}{}", inj, h) };

                let extensions = extensions::load_all_extensions().await;
                let (ext_js, ext_css) = extensions::get_injections_for_url(&clean_url, &extensions).await;
                if ext_js.is_some() || ext_css.is_some() {
                    let ext_api = r#"<script>if(typeof chrome==='undefined'){window.chrome={runtime:{sendMessage:function(m,c){window.top.postMessage(JSON.stringify({a:'ext-msg',p:m}),'*');}}}}</script>"#;
                    let css_tag = ext_css.map(|c| format!(r#"<style id="nexus-ext-css">{}</style>"#, c)).unwrap_or_default();
                    let js_tag = ext_js.map(|j| format!(r#"<script id="nexus-ext-js">{}</script>"#, j)).unwrap_or_default();
                    let ext_inj = format!("{}{}{}", ext_api, css_tag, js_tag);
                    let lower_out = html_out.to_ascii_lowercase();
                    if let Some(body_end) = lower_out.rfind("</body>") { html_out.insert_str(body_end, &ext_inj); }
                    else { html_out.push_str(&ext_inj); }
                }
                commit_render(&html_out, &clean_url, tab_idx, my_gen, &st, px).await;
                }
                Err(_) => {
                    let msg = format!("This page sent a response NEXUS couldn't decode as text (HTTP {}). It may require a browser feature NEXUS doesn't yet support.", status.as_u16());
                    let html = format!(r#"<html><body style="font-family:sans-serif;padding:60px;text-align:center;color:#5f6368"><h2>Couldn't display this page</h2><p>{}</p></body></html>"#, msg);
                    commit_render(&html, &clean_url, tab_idx, my_gen, &st, px).await;
                }
            }
        } else if content_type.contains("image/") {
            let safe_img_url = clean_url.replace('&', "&amp;").replace('"', "&quot;").replace('<', "&lt;");
            let html = format!(r#"<html><body style="margin:0;background:#0e0e0e;display:flex;justify-content:center;align-items:center;height:100vh;"><img src="{}" style="max-width:100%;max-height:100%;"></body></html>"#, safe_img_url);
            commit_render(&html, &clean_url, tab_idx, my_gen, &st, px).await;
        } else {
            let safe_url = clean_url.replace('\'', "\\'").replace('\n', " ");
            let _ = px.send_event(Ev::Js(format!("lg('Downloading: {}'); hideLoading();", safe_url)));
            tokio::spawn(dl::turbo(clean_url.clone(), st.clone()));
            return;
        }

        if record {
            let mut g = st.write().await;
            if let Some(t) = g.tabs.get_mut(tab_idx) {
                t.push_hist(clean_url.clone());
                t.url = clean_url.clone();
                if let Ok(parsed) = url::Url::parse(&clean_url) {
                    t.name = parsed.host_str().unwrap_or("New Tab").to_string();
                }
            }
            let title = g.tabs.get(tab_idx).map(|t| t.name.clone()).unwrap_or_default();
            let time = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map_or(0, |d| d.as_secs());
            g.history.push(state::HistoryEntry { url: clean_url.clone(), title, time });

            // ✅ FIX #10: Chỉ clone 1 lần thay vì 2
            let hist_clone = g.history.clone();
            let st_urls: Vec<String> = g.tabs.iter().map(|t| t.url.clone()).collect();
            update_tabs(&g, px);
            drop(g);

            tokio::spawn(async move {
                state::save_history(&hist_clone).await;
                state::save_session(&st_urls).await;
            });

            if let Ok(hd) = serde_json::to_string(&hist_clone) {
                let _ = px.send_event(Ev::Js(format!(r#"if(window.renderHistory)window.renderHistory({})"#, hd)));
            }
        }
    } else {
        let safe_url = clean_url.replace('\'', "\\'").replace('\n', " ");
        let safe_err = err_detail.replace('\'', "\\'").replace('\n', " ");
        let _ = px.send_event(Ev::Js(format!("lg('✗ failed after {}ms: {} — {}');", elapsed_ms, safe_url, safe_err)));
        let safe_display = clean_url.replace('&', "&amp;").replace('"', "&quot;").replace('<', "&lt;");
        let safe_err_display = err_detail.replace('&', "&amp;").replace('<', "&lt;");
        let html = format!(
            r#"<html><body style="font-family:sans-serif;padding:60px;text-align:center;color:#5f6368">
            <h2>Couldn't reach this page</h2>
            <p>NEXUS couldn't connect to <b>{}</b> (waited {}ms).</p>
            <p style="color:#80868b;font-size:13px;max-width:520px;margin:12px auto 0">{}</p>
            <p style="color:#80868b;font-size:13px">This can happen if the site is down, your network is blocking it,
            or (if Tor/WARP is on) the proxy isn't actually running.</p>
            </body></html>"#, safe_display, elapsed_ms, safe_err_display);
        commit_render(&html, &clean_url, tab_idx, my_gen, &st, px).await;
    }
}

// ======================
// UPDATE TABS
// ✅ FIX #3: Bỏ tokio::spawn bên trong — caller tự lo việc save async
// ======================
fn update_tabs(state: &state::State, px: &tao::event_loop::EventLoopProxy<Ev>) {
    let tabs = state.tabs.iter().map(|t| json!({
        "id": t.id, "name": t.name, "url": t.url, "frozen": t.frozen,
        "mode": match t.mode { state::TabMode::Normal => "normal", state::TabMode::Incognito => "incognito", state::TabMode::Tor => "tor" }
    })).collect::<Vec<_>>();

    if let Ok(t) = serde_json::to_string(&tabs) {
        let _ = px.send_event(Ev::Js(format!(r#"if(window.updateTabs)window.updateTabs({{"tabs":{},"activeTab":{}}})"#, t, state.active_tab)));
    }
    // ✅ Không gọi tokio::spawn ở đây nữa — tránh panic khi gọi từ sync context
}

// ======================
// MAIN FUNCTION
// ======================
fn main() {
    dotenvy::dotenv().ok();
    std::env::set_var("WEBKIT_DISABLE_COMPOSITING_MODE", "1");

    let el = EventLoopBuilder::<Ev>::with_user_event().build();
    let w = WindowBuilder::new()
        .with_title("Nexus Browser")
        .with_inner_size(LogicalSize::new(1200, 800))
        .build(&el).unwrap();

    let mut initial = state::State::new();
    initial.vault = vault::load();

    let saved_tabs = state::load_session();
    if !saved_tabs.is_empty() {
        initial.tabs.clear();
        for url in saved_tabs {
            let mut tab = state::TabState::new(state::TabMode::Normal);
            tab.url = url;
            initial.tabs.push(tab);
        }
    }
    initial.bookmarks = state::load_bookmarks();
    initial.history = state::load_history();

    let st = Arc::new(RwLock::new(initial));
    let px = el.create_proxy();

    let rt = Builder::new_multi_thread()
        .worker_threads(std::cmp::max(2, num_cpus::get() - 1))
        .thread_stack_size(2 * 1024 * 1024)
        .enable_all().build().unwrap();

    let handle = rt.handle().clone();
    let handle_for_loop = handle.clone();
    let (ist, ipx) = (st.clone(), px.clone());

    let freeze_st = st.clone();
    let freeze_px = px.clone();
    rt.spawn(async move {
        let mut interval = tokio::time::interval(Duration::from_secs(60));
        loop {
            interval.tick().await;
            let mut g = freeze_st.write().await;
            let active_idx = g.active_tab;
            let mut changed = false;
            for (i, tab) in g.tabs.iter_mut().enumerate() {
                if i != active_idx && !tab.frozen && tab.last_active.elapsed() > Duration::from_secs(300) {
                    tab.frozen = true;
                    tab.client = None;
                    changed = true;
                }
            }
            if changed {
                update_tabs(&g, &freeze_px);
                // ✅ Save session từ async context (an toàn)
                let st_urls: Vec<String> = g.tabs.iter().map(|t| t.url.clone()).collect();
                tokio::spawn(async move { state::save_session(&st_urls).await; });
            }
        }
    });

    let bm_init = st.blocking_read().bookmarks.clone();
    if let Ok(b) = serde_json::to_string(&bm_init) {
        let _ = px.send_event(Ev::Js(format!(r#"if(window.renderBookmarks)window.renderBookmarks({})"#, b)));
    }

    let hist_init = st.blocking_read().history.clone();
    if let Ok(h) = serde_json::to_string(&hist_init) {
        let _ = px.send_event(Ev::Js(format!(r#"if(window.renderHistory)window.renderHistory({})"#, h)));
    }

    let wb = WebViewBuilder::new()
        .with_devtools(false)
        .with_user_agent("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36")
        .with_html(html())
        .with_back_forward_navigation_gestures(false)
        .with_hotkeys_zoom(false)
        .with_ipc_handler(move |request: wry::http::Request<String>| {
            let msg = request.into_body();
            let (ist, ipx, handle) = (ist.clone(), ipx.clone(), handle.clone());
            let p: JsonValue = match serde_json::from_str(&msg) { Ok(v) => v, Err(_) => return };
            let (a, d) = (p["a"].as_str().unwrap_or("").to_string(), p["p"].clone());

            handle.spawn(async move {
                match a.as_str() {
                    "nav" | "nav-internal" => if let Some(u) = d.as_str().map(search::resolve) {
                        let idx = { ist.read().await.active_tab };
                        load_url(u, idx, ist.clone(), &ipx, true).await;
                    },
                    "nav-post" => {
                        let url = d["url"].as_str().unwrap_or("").to_string();
                        let body = d["body"].clone();
                        let idx = { ist.read().await.active_tab };
                        load_url_method(url, idx, "POST", Some(body), ist.clone(), &ipx, true).await;
                    }
                    "new-tab-url" => if let Some(url) = d.as_str() {
                        let mut g = ist.write().await;
                        let idx = g.new_tab(state::TabMode::Normal);
                        // ✅ FIX #15: KHÔNG gửi Ev::NewTab ở đây — event đó khiến
                        // tao event-loop tự spawn load_url("nexus://home") song
                        // song với load_url(target) bên dưới, đua nhau ghi vào
                        // cùng một tab và có thể xoá mất trang đích vừa mở.
                        update_tabs(&g, &ipx);
                        let u = url.to_string();
                        drop(g);
                        load_url(u, idx, ist.clone(), &ipx, true).await;
                    }
                    "console-log" => if let Some(msg) = d.as_str() {
                        let safe_msg = msg.replace('\'', "\\'").replace('\n', " ");
                        ipx.send_event(Ev::Js(format!("lg('{}');", safe_msg))).ok();
                    }
                    "bookmark" => if let Some(url) = d.as_str() {
                        if url.is_empty() || url == "nexus://home" {
                            ipx.send_event(Ev::Js("lg('Cannot save this page');".into())).ok();
                            return;
                        }
                        let mut g = ist.write().await;
                        let title = g.active_tab().name.clone();
                        g.bookmarks.push(state::Bookmark { title, url: url.to_string() });
                        let bms = g.bookmarks.clone();
                        drop(g);

                        if let Ok(b) = serde_json::to_string(&bms) {
                            ipx.send_event(Ev::Js(format!(r#"if(window.renderBookmarks)window.renderBookmarks({})"#, b))).ok();
                        }
                        tokio::spawn(async move { state::save_bookmarks(&bms).await; });

                        ipx.send_event(Ev::Js("lg('Saved to bookmarks');".into())).ok();
                    }
                    "back" => { let mut g = ist.write().await; let idx = g.active_tab; if let Some(u) = g.active_tab_mut().go_back() { drop(g); load_url(u, idx, ist.clone(), &ipx, false).await; } }
                    "fwd" => { let mut g = ist.write().await; let idx = g.active_tab; if let Some(u) = g.active_tab_mut().go_fwd() { drop(g); load_url(u, idx, ist.clone(), &ipx, false).await; } }
                    "ref" => { let g = ist.read().await; let idx = g.active_tab; if let Some(u) = g.active_tab().current() { drop(g); load_url(u, idx, ist.clone(), &ipx, false).await; } }
                    "inc" => { let c = { let mut g = ist.write().await; g.blocked += 1; g.blocked }; ipx.send_event(Ev::Js(format!("lg('Blocked request: {}');", c))).ok(); }
                    "shld" => if let (Some(s), Some(v)) = (d["s"].as_str(), d["v"].as_bool()) {
                        let mut g = ist.write().await;
                        { let tab = g.active_tab_mut(); match s {
                            "ad" => tab.cfg.ad = v, "trk" => tab.cfg.trk = v, "sink" => tab.cfg.sinkhole = v,
                            "cookie" => tab.cfg.cookie = v, "anti_fp" => tab.cfg.anti_fp = v,
                            "warp" => { tab.cfg.warp = v; if v { tab.cfg.tor = false; ipx.send_event(Ev::Js("document.getElementById('tor-toggle').checked=false;".into())).ok(); } },
                            "tor" => { tab.cfg.tor = v; if v { tab.cfg.warp = false; ipx.send_event(Ev::Js("document.getElementById('warp-toggle').checked=false;".into())).ok(); } },
                            _ => {} }
                            if matches!(s, "ad" | "trk" | "sink" | "cookie" | "anti_fp" | "warp" | "tor") { tab.update_client(); }
                        }
                        match s { "auto-save" => g.global_cfg.auto_save_passwords = v, "pass-suggest" => g.global_cfg.show_password_suggestions = v, "sync-chrome" => g.sync.config.chrome = v, "sync-firefox" => g.sync.config.firefox = v, "sync-edge" => g.sync.config.edge = v, _ => {} }
                    },
                    "ai_cfg" => if let (Some(e), Some(k), Some(m)) = (d["e"].as_str(), d["k"].as_str(), d["m"].as_str()) {
                        let mut g = ist.write().await; let tab = g.active_tab_mut();
                        tab.ai.endpoint = e.into(); tab.ai.key = k.into(); tab.ai.model = m.into();
                        ipx.send_event(Ev::Js("lg('AI config saved');".into())).ok();
                    },
                    "ai" => if let Some(p) = d.as_str() {
                        let r = ai::ask(p.into(), ist.clone()).await;
                        if let Ok(j) = serde_json::to_string(&r) { ipx.send_event(Ev::Js(format!("addAi({});", j))).ok(); }
                    }
                    "vault" => if let (Some(a), Some(m), Some(d), Some(u), Some(p)) = (d["a"].as_str(), d["m"].as_str(), d["d"].as_str(), d["u"].as_str(), d["p"].as_str()) {
                        let (act, m, d, u, p) = (a.to_string(), m.to_string(), d.to_string(), u.to_string(), p.to_string());
                        let master = zeroize::Zeroizing::new(m.clone());
                        let is_incognito = { ist.read().await.active_tab().mode == state::TabMode::Incognito };
                        if is_incognito {
                            ipx.send_event(Ev::Js("vRes('Vault is not available in Incognito tabs');".into())).ok();
                        } else if act == "save" && !master.is_empty() && !d.is_empty() {
                            if let Some((enc, nonce, salt)) = vault::encrypt(&p, &master) {
                                let entries = {
                                    let mut g = ist.write().await;
                                    g.vault.push(state::VaultEntry {
                                        domain: d, user: u, pass: enc, nonce, salt,
                                        created: std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map_or(0, |d| d.as_secs()),
                                        last_used: std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map_or(0, |d| d.as_secs()),
                                    });
                                    g.vault.clone()
                                };
                                let msg = if vault::save(&entries).await { "vRes('Saved successfully');" } else { "vRes('Save failed');" };
                                ipx.send_event(Ev::Js(msg.into())).ok();
                            }
                        } else if act == "get" {
                            let found = { let g = ist.read().await; g.vault.iter().find(|e| e.domain == d).map(|e| (e.user.clone(), e.pass.clone(), e.nonce.clone(), e.salt.clone())) };
                            if let Some((user, pass, nonce, salt)) = found {
                                if let Some(dec) = vault::decrypt(&pass, &nonce, &salt, &master) {
                                    if let Ok(d) = serde_json::to_string(&dec) { ipx.send_event(Ev::Js(format!("document.getElementById('v-pass').value={};vRes('Password for {}');", d, user.replace('\'', "")))).ok(); }
                                } else { ipx.send_event(Ev::Js("vRes('Wrong master password');".into())).ok(); }
                            } else { ipx.send_event(Ev::Js("vRes('Not found');".into())).ok(); }
                        } else if act == "gen" {
                            let gpw = vault::generate(16);
                            if let Ok(g) = serde_json::to_string(&gpw) { ipx.send_event(Ev::Js(format!("document.getElementById('v-pass').value={};vRes('Generated');", g))).ok(); }
                        }
                    },
                    "new-tab" => if let Some(m) = d.as_str() {
                        let mode = match m { "incognito" => state::TabMode::Incognito, "tor" => state::TabMode::Tor, _ => state::TabMode::Normal };
                        let mut g = ist.write().await; let idx = g.new_tab(mode);
                        ipx.send_event(Ev::NewTab(idx)).ok(); update_tabs(&g, &ipx);
                    }
                    "close-tab" => if let Some(i) = d.as_u64() {
                        let mut g = ist.write().await; if g.close_tab(i as usize) { ipx.send_event(Ev::CloseTab(i as usize)).ok(); update_tabs(&g, &ipx); }
                    },
                    "switch-tab" => if let Some(i) = d.as_u64() {
                        let idx = i as usize;
                        let mut g = ist.write().await;
                        g.switch_tab(idx);
                        if let Some(tab) = g.tabs.get_mut(idx) {
                            tab.frozen = false;
                            tab.last_active = Instant::now();
                        }
                        update_tabs(&g, &ipx);
                        let cached = g.tabs.get(idx).and_then(|t| {
                            t.last_html.clone().map(|h| (h, t.url.clone()))
                        });
                        match cached {
                            Some((html, url)) => { drop(g); render_page(&html, &url, &ipx); }
                            None => {
                                let url = g.tabs.get(idx).map(|t| t.url.clone()).unwrap_or_default();
                                drop(g);
                                if !url.is_empty() { load_url(url, idx, ist.clone(), &ipx, false).await; }
                            }
                        }
                    },
                    "unfreeze-tab" => if let Some(i) = d.as_u64() {
                        let idx = i as usize;
                        let url = {
                            let mut g = ist.write().await;
                            match g.tabs.get_mut(idx) {
                                Some(tab) => { tab.frozen = false; tab.last_active = Instant::now(); tab.url.clone() }
                                None => return,
                            }
                        };
                        let mut g = ist.write().await; g.switch_tab(idx); update_tabs(&g, &ipx); drop(g);
                        load_url(url, idx, ist.clone(), &ipx, false).await;
                    },
                    "password-detected" => {
                        let (url, user, pass) = (d["url"].as_str().unwrap_or(""), d["username"].as_str().unwrap_or(""), d["password"].as_str().unwrap_or(""));
                        // ✅ FIX #16: đọc show_password_suggestions thay vì bỏ quên nó
                        let (auto_save, suggest) = {
                            let g = ist.read().await;
                            (g.global_cfg.auto_save_passwords, g.global_cfg.show_password_suggestions)
                        };
                        if !url.is_empty() && auto_save {
                            let url_js = serde_json::to_string(url).unwrap_or_default();
                            let user_js = serde_json::to_string(user).unwrap_or_default();
                            let pass_js = serde_json::to_string(pass).unwrap_or_default();
                            ipx.send_event(Ev::Js(format!(r#"if(window.showPassPopup)window.showPassPopup({{"url":{},"username":{},"password":{},"suggest":{}}})"#, url_js, user_js, pass_js, suggest))).ok();
                        }
                    },
                    "save-password" => {
                        let (url, user, pass, master) = (d["url"].as_str().unwrap_or(""), d["username"].as_str().unwrap_or(""), d["password"].as_str().unwrap_or(""), d["master"].as_str().unwrap_or(""));
                        if !url.is_empty() && !user.is_empty() && !pass.is_empty() && !master.is_empty() {
                            let domain = if let Ok(parsed) = Url::parse(url) { parsed.domain().map(|d| d.to_string()).unwrap_or_else(|| url.to_string()) } else { url.split('/').next().unwrap_or(url).to_string() };
                            let mut g = ist.write().await;
                            if let Some(entry) = g.vault.iter_mut().find(|e| e.domain == domain && e.user == user) {
                                if let Some((enc, nonce, salt)) = vault::encrypt(pass, master) {
                                    entry.pass = enc;
                                    entry.nonce = nonce;
                                    entry.salt = salt;
                                    entry.last_used = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map_or(0, |d| d.as_secs());
                                }
                            } else if let Some((enc, nonce, salt)) = vault::encrypt(pass, master) {
                                g.vault.push(state::VaultEntry {
                                    domain: domain.clone(), user: user.into(), pass: enc, nonce, salt,
                                    created: std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map_or(0, |d| d.as_secs()),
                                    last_used: std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map_or(0, |d| d.as_secs()),
                                });
                            }
                            let vault_clone = g.vault.clone();
                            drop(g);
                            tokio::spawn(async move { vault::save(&vault_clone).await; });
                        }
                    },
                    "fill-password" => {
                        let (user, pass) = (d["username"].as_str().unwrap_or(""), d["password"].as_str().unwrap_or(""));
                        if !user.is_empty() && !pass.is_empty() {
                            let user_js = serde_json::to_string(user).unwrap_or_default();
                            let pass_js = serde_json::to_string(pass).unwrap_or_default();
                            ipx.send_event(Ev::Js(format!(r#"if(window.nexusFillPassword)window.nexusFillPassword({},{});"#, user_js, pass_js))).ok();
                        }
                    },
                    "sync-now" => {
                        let mut g = ist.write().await;
                        let (c, f, e) = (g.sync.import_from_browser("chrome"), g.sync.import_from_browser("firefox"), g.sync.import_from_browser("edge"));
                        let sync_snapshot = g.sync.clone();
                        sync_snapshot.sync_to_vault(&mut g.vault);
                        let vault_clone = g.vault.clone();
                        drop(g);
                        tokio::spawn(async move { vault::save(&vault_clone).await; });
                        ipx.send_event(Ev::Js(format!("lg('Synced: Chrome({}), Firefox({}), Edge({})');", c, f, e))).ok();
                    },
                    "ext-list" => {
                        let extensions = extensions::load_all_extensions().await;
                        let ext_data = extensions.iter().map(|e| json!({ "id": e.id, "name": e.manifest.name, "version": e.manifest.version, "description": e.manifest.description, "enabled": e.enabled })).collect::<Vec<_>>();
                        ipx.send_event(Ev::Js(format!(r#"if(window.postMessage)window.postMessage(JSON.stringify({{a:'ext-list-response',p:{}}}));"#, serde_json::to_string(&ext_data).unwrap_or_default()))).ok();
                    },
                    "ext-toggle" => if let (Some(id), Some(enabled)) = (d["id"].as_str(), d["enabled"].as_bool()) {
                        if id.is_empty() || id.contains('/') || id.contains('\\') || id.contains("..") { return; }
                        let ext_dir = std::path::Path::new("nexus_extensions").join(id);
                        if ext_dir.exists() {
                            if enabled { std::fs::remove_file(ext_dir.join("DISABLED")).ok(); }
                            else { std::fs::write(ext_dir.join("DISABLED"), "").ok(); }
                            let id_js = serde_json::to_string(id).unwrap_or_default();
                            ipx.send_event(Ev::Js(format!(r#"if(window.postMessage)window.postMessage(JSON.stringify({{a:'ext-toggle-response',p:{{id:{},enabled:{}}}}}));"#, id_js, enabled))).ok();
                        }
                    },
                    "ext-msg" => { ipx.send_event(Ev::Js(format!("lg('Extension message: {}');", d))).ok(); },
                    _ => {}
                }
            });
        });

    let wv = wb.build(&w).unwrap();

    extensions::api::setup_extension_apis(&wv);

    let px_clone = px.clone();
    let st_detect = st.clone();
    rt.spawn(async move {
        let warp_detected = autoconfig::detect_warp().await;
        let tor_detected = autoconfig::detect_tor().await;
        if warp_detected || tor_detected {
            let mut g = st_detect.write().await;
            let tab = g.active_tab_mut();
            if warp_detected && !tor_detected { tab.cfg.warp = true; }
            if tor_detected { tab.cfg.tor = true; tab.cfg.warp = false; }
            tab.update_client();
        }
        let _ = px_clone.send_event(Ev::Js(format!(
            "document.getElementById('warp-toggle').checked = {}; document.getElementById('tor-toggle').checked = {};",
            warp_detected && !tor_detected, tor_detected
        )));
    });

    update_tabs(&st.blocking_read(), &px);

    el.run(move |ev, _, cf| {
        *cf = ControlFlow::Wait;
        match ev {
            Event::NewEvents(StartCause::Init) => {
                px.send_event(Ev::Js("lg('Nexus Core initialized');".into())).ok();
                handle_for_loop.spawn({
                    let (st, px) = (st.clone(), px.clone());
                    async move {
                        let st_read = st.read().await;
                        let first_url = st_read.tabs[0].url.clone();
                        drop(st_read);
                        load_url(first_url, 0, st, &px, false).await;
                    }
                });
            }
            Event::UserEvent(Ev::Js(j)) => {
                let _ = wv.evaluate_script(&j);
            }
            Event::UserEvent(Ev::NewTab(idx)) => {
                update_tabs(&st.blocking_read(), &px);
                handle_for_loop.spawn({
                    let (st, px) = (st.clone(), px.clone());
                    async move {
                        load_url("nexus://home".into(), idx, st, &px, false).await;
                    }
                });
            }
            Event::UserEvent(Ev::CloseTab(_)) => {
                update_tabs(&st.blocking_read(), &px);
            }
            Event::WindowEvent { event: tao::event::WindowEvent::CloseRequested, .. } => *cf = ControlFlow::Exit,
            _ => {}
        }
    });
}
