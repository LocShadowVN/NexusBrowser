// Hide the black terminal window on Windows
#![windows_subsystem = "windows"]
#![allow(dead_code, unused_imports, unused_variables, unreachable_code)]

use std::{
    collections::HashMap,
    sync::{atomic::{AtomicUsize, Ordering}, Arc, Mutex as StdMutex},
    time::{Duration, Instant},
};
use tao::{
    dpi::LogicalSize,
    event::{Event, StartCause, WindowEvent},
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
    password_hash::SaltString,
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
enum Ev { Js(String) }

// Vault master password — RAM only, zeroized on drop.
lazy_static::lazy_static! {
    static ref MASTER: TokioMutex<Option<zeroize::Zeroizing<String>>> = TokioMutex::new(None);
    static ref RE_TITLE: Regex = Regex::new(r"(?is)<title[^>]*>(.*?)</title>").unwrap();
    static ref RE_BASE: Regex = Regex::new(r"(?i)<base[^>]*>").unwrap();
    static ref RE_CSP: Regex = Regex::new(r#"(?i)<meta[^>]+http-equiv\s*=\s*["']?(content-security-policy|refresh)["']?[^>]*>"#).unwrap();
}

// ======================
// MODULE: STATE
// ======================
mod state {
    use super::*;

    #[derive(Clone, Debug, PartialEq)]
    pub enum TabMode { Normal, Incognito }

    #[derive(Clone, Debug, Default)]
    pub struct TabConfig {
        pub proxy: bool, pub proxy_url: String,
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

    #[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
    pub struct Bookmark { pub title: String, pub url: String }

    #[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
    pub struct HistoryEntry { pub url: String, pub title: String, pub time: u64 }

    // Shield popup log entries (deduped per domain)
    #[derive(Clone, Debug, serde::Serialize)]
    pub struct BlockedLog { pub domain: String, pub kind: String, pub n: u64 }

    #[derive(Debug)]
    pub struct TabState {
        pub id: Uuid, pub name: String, pub url: String,
        pub hist: Vec<String>, pub hist_pos: usize,
        pub cfg: TabConfig, pub mode: TabMode,
        pub last_active: Instant,
        pub frozen: bool,
        pub jar: Arc<reqwest::cookie::Jar>,            // persistent cookie jar per tab
        pub client: Option<reqwest::Client>,
        pub client_cfg_hash: u64,
        pub pinned: HashMap<String, reqwest::Client>,   // DoH-pinned clients per host
        pub last_html: Option<String>,
        pub load_gen: u64,
    }

    impl TabState {
        pub fn new(mode: TabMode) -> Self {
            // defaults aligned with the Balanced profile (apply_global overrides anyway)
            Self {
                id: Uuid::new_v4(),
                name: match mode {
                    TabMode::Normal => "New Tab",
                    TabMode::Incognito => "Private Tab",
                }.into(),
                url: "nexus://home".into(),
                hist: Vec::with_capacity(32),
                hist_pos: 0,
                cfg: TabConfig {
                    proxy_url: "socks5h://127.0.0.1:1080".into(),
                    ad: true, trk: true, sinkhole: false,
                    cookie: false, anti_fp: false,
                    ..Default::default()
                },
                mode, last_active: Instant::now(),
                frozen: false,
                jar: Arc::new(reqwest::cookie::Jar::default()),
                client: None, client_cfg_hash: 0,
                pinned: HashMap::new(),
                last_html: None, load_gen: 0,
            }
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
                self.client = Some(super::net::build_client(&self.cfg, self.jar.clone(), None));
                self.client_cfg_hash = new_hash;
                self.pinned.clear(); // pins depend on the proxy config — rebuild lazily
            }
        }

        // ✅ FIX #13 (kept): `cookie` excluded from the hash — build_client ignores it,
        // so toggling Cookie Shield must not rebuild the client (an empty jar = lost login).
        fn cfg_hash(&self) -> u64 {
            use std::hash::{Hash, Hasher};
            let mut h = std::collections::hash_map::DefaultHasher::new();
            self.cfg.proxy.hash(&mut h);
            self.cfg.proxy_url.hash(&mut h);
            h.finish()
        }
    }

    // Apply global defaults (Settings → Privacy) to a tab.
    // Same rules for every tab mode — private tabs get no *weaker* blocking.
    pub fn apply_global(g: &GlobalConfig, t: &mut TabState) {
        t.cfg.ad = g.ad; t.cfg.trk = g.trk; t.cfg.sinkhole = g.sinkhole;
        t.cfg.anti_fp = g.anti_fp; t.cfg.cookie = g.cookie;
    }

    // defaults = Balanced (matches what the UI, site and README claim)
    #[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
    pub struct GlobalConfig {
        #[serde(default = "d_true")] pub ad: bool,
        #[serde(default = "d_true")] pub trk: bool,
        #[serde(default = "d_false")] pub sinkhole: bool,
        #[serde(default = "d_false")] pub anti_fp: bool,
        #[serde(default = "d_false")] pub cookie: bool,
        #[serde(default = "d_true")] pub auto_save_passwords: bool,
        #[serde(default = "d_true")] pub show_password_suggestions: bool, // kept for old config.json compat
        #[serde(default = "d_engine")] pub search_engine: String,
        #[serde(default = "d_home")] pub home: String,
        #[serde(default)] pub secure_dns: bool,
        #[serde(default = "d_dns")] pub dns_endpoint: String,
    }
    fn d_true() -> bool { true }
    fn d_false() -> bool { false }
    fn d_engine() -> String { "duckduckgo".into() }
    fn d_home() -> String { "nexus://home".into() }
    fn d_dns() -> String { "https://1.1.1.1/dns-query".into() }

    impl Default for GlobalConfig {
        fn default() -> Self {
            Self {
                ad: true, trk: true, sinkhole: false, anti_fp: false, cookie: false,
                auto_save_passwords: true, show_password_suggestions: true,
                search_engine: "duckduckgo".into(), home: "nexus://home".into(),
                secure_dns: false, dns_endpoint: "https://1.1.1.1/dns-query".into(),
            }
        }
    }

    #[derive(Debug)]
    pub struct State {
        pub active_tab: usize,
        pub tabs: Vec<TabState>,
        pub blocked: u64,
        pub blocked_log: Vec<BlockedLog>,
        pub global_cfg: GlobalConfig,
        pub sync: SyncState,
        pub bookmarks: Vec<Bookmark>,
        pub history: Vec<HistoryEntry>,
        pub vault: Vec<VaultEntry>,
    }

    impl State {
        pub fn new() -> Self {
            Self {
                active_tab: 0, tabs: vec![TabState::new(TabMode::Normal)],
                blocked: 0, blocked_log: Vec::new(),
                global_cfg: GlobalConfig::default(),
                sync: SyncState::default(),
                bookmarks: Vec::new(), history: Vec::new(), vault: Vec::new(),
            }
        }

        #[inline] pub fn active_tab(&self) -> &TabState { &self.tabs[self.active_tab] }
        #[inline] pub fn active_tab_mut(&mut self) -> &mut TabState { &mut self.tabs[self.active_tab] }

        // new tabs inherit the default shield level from Settings → Privacy
        pub fn new_tab(&mut self, mode: TabMode) -> usize {
            let mut t = TabState::new(mode);
            apply_global(&self.global_cfg, &mut t);
            let idx = self.tabs.len();
            self.tabs.push(t);
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

        pub fn push_block(&mut self, domain: &str, kind: &str) {
            self.blocked += 1;
            if let Some(e) = self.blocked_log.iter_mut().find(|e| e.domain == domain && e.kind == kind) {
                e.n += 1;
            } else {
                self.blocked_log.push(BlockedLog { domain: domain.into(), kind: kind.into(), n: 1 });
                if self.blocked_log.len() > 300 { self.blocked_log.remove(0); }
            }
        }
    }

    #[derive(Clone, Debug, Default)]
    pub struct SyncConfig { pub chrome: bool, pub firefox: bool, pub edge: bool }

    #[derive(Debug, Default, Clone)]
    pub struct SyncState {
        pub config: SyncConfig,
        pub chrome_vault: Vec<VaultEntry>,
        pub firefox_vault: Vec<VaultEntry>,
        pub edge_vault: Vec<VaultEntry>, // ✅ FIX #14 (kept): separate from chrome_vault
    }

    impl SyncState {
        // ✅ FIX #6 (kept): returns the number of NEWLY imported entries
        pub fn import_from_browser(&mut self, browser: &str) -> usize {
            let entries = match browser {
                "chrome" => super::sync::import_from_chrome(),
                "firefox" => super::sync::import_from_firefox(),
                "edge" => super::sync::import_from_edge(),
                _ => Ok(Vec::new()),
            }.unwrap_or_default();
            let count = entries.len();
            match browser {
                "chrome" => self.chrome_vault = entries,
                "firefox" => self.firefox_vault = entries,
                "edge" => self.edge_vault = entries,
                _ => {}
            }
            count
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

    pub async fn save_config(c: &GlobalConfig) {
        let _ = tokio::fs::write("config.json", serde_json::to_vec(c).unwrap_or_default()).await;
    }

    pub fn load_config() -> GlobalConfig {
        std::fs::read_to_string("config.json").ok()
            .and_then(|s| serde_json::from_str(&s).ok())
            .unwrap_or_default()
    }
}

// ======================
// MODULE: NET
// ======================
mod net {
    use super::*;

    // ✅ FIX #4 (kept): never unwrap() on Proxy::all.
    // ✅ F2: the cookie jar is shared per tab, so rebuilding the client
    //   (e.g. toggling the proxy) no longer wipes the login session.
    pub fn build_client(c: &state::TabConfig, jar: Arc<reqwest::cookie::Jar>, pin: Option<(&str, std::net::SocketAddr)>) -> reqwest::Client {
        let mut b = reqwest::Client::builder()
            .user_agent("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36")
            .cookie_provider(jar)
            .danger_accept_invalid_certs(false)
            .connect_timeout(Duration::from_secs(10));

        if let Some((host, addr)) = pin { b = b.resolve(host, addr); }
        if c.proxy {
            if let Ok(p) = reqwest::Proxy::all(&c.proxy_url) { b = b.proxy(p); }
        }
        b.build().unwrap_or_else(|_| reqwest::Client::new())
    }
}

// ======================
// MODULE: DOH (Secure DNS / DNS-over-HTTPS)
// ======================
mod doh {
    use super::*;

    lazy_static::lazy_static! {
        static ref CACHE: StdMutex<HashMap<String, (Vec<std::net::IpAddr>, u64)>> = StdMutex::new(HashMap::new());
        // Bootstrap client — resolves the DoH server itself via system DNS (once),
        // then every site hostname goes through the encrypted resolver.
        static ref BOOT: reqwest::Client = reqwest::Client::builder()
            .user_agent("Mozilla/5.0 NexusBrowser/1.0")
            .connect_timeout(Duration::from_secs(4))
            .timeout(Duration::from_secs(4))
            .build().unwrap_or_else(|_| reqwest::Client::new());
    }

    fn now() -> u64 {
        std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map(|d| d.as_secs()).unwrap_or(0)
    }

    // ✅ FIX compile: reqwest without the `json` feature has no .json() —
    // parse with text() + serde_json instead.
    async fn query(endpoint: &str, host: &str, rtype: &str) -> Option<(Vec<std::net::IpAddr>, u64)> {
        let text = BOOT.get(endpoint)
            .query(&[("name", host), ("type", rtype)])
            .header("accept", "application/dns-json")
            .send().await.ok()?
            .text().await.ok()?;
        let v: JsonValue = serde_json::from_str(&text).ok()?;
        let ttl = v["Answer"].as_array()
            .and_then(|a| a.first())
            .and_then(|a| a["TTL"].as_u64())
            .unwrap_or(60).clamp(60, 3600);
        let ips = v["Answer"].as_array()?
            .iter()
            .filter(|a| matches!(a["type"].as_u64(), Some(1) | Some(28)))
            .filter_map(|a| a["data"].as_str())
            .filter_map(|s| s.parse::<std::net::IpAddr>().ok())
            .collect::<Vec<_>>();
        if ips.is_empty() { None } else { Some((ips, ttl)) }
    }

    // Resolve one hostname via DoH. Falls back to None (→ system DNS) on failure.
    pub async fn resolve_ip(endpoint: &str, host: &str) -> Option<std::net::IpAddr> {
        if let Ok(ip) = host.parse::<std::net::IpAddr>() { return Some(ip); } // IP literal
        {
            let c = CACHE.lock().unwrap();
            if let Some((ips, exp)) = c.get(host) {
                if *exp > now() && !ips.is_empty() { return ips.first().cloned(); }
            }
        }
        let mut res = query(endpoint, host, "A").await;
        if res.is_none() { res = query(endpoint, host, "AAAA").await; }
        let (ips, ttl) = res?;
        CACHE.lock().unwrap().insert(host.to_string(), (ips.clone(), now() + ttl));
        ips.first().cloned()
    }

    pub fn clear_cache() { CACHE.lock().unwrap().clear(); }
}

// ======================
// MODULE: SINKHOLE (network-layer block)
// ======================
mod sinkhole {
    const AD: &[&str] = &[
        "doubleclick", "googlesyndication", "googleadservices", "adservice.google",
        "adsystem", "adsense", "adnxs", "rubiconproject", "pubmatic", "openx",
        "casalemedia", "criteo", "taboola", "outbrain", "bidswitch", "adsrvr",
        "amazon-adsystem", "scorecardresearch", "moatads", "zedo", "popads",
        "popcash", "mgid", "revcontent", "adsterra", "propellerads", "teads",
        "smartadserver", "adskeeper", "adfox",
    ];
    const TRK: &[&str] = &[
        "google-analytics", "analytics.google", "googletagmanager", "segment.io",
        "segment.com", "mixpanel", "hotjar", "crazyegg", "mouseflow", "fullstory",
        "logrocket", "heapanalytics", "amplitude", "branch.io", "appsflyer",
        "kochava", "chartbeat", "newrelic", "mc.yandex", "clarity.ms",
        "trackcmp", "facebook.com/tr", "bat.bing", "analytics.tiktok",
        "tr.snapchat", "stats.wp.com",
    ];

    // Returns the block kind for the popup ("Ad" / "Tracker")
    pub fn check(u: &str) -> Option<&'static str> {
        let l = u.to_ascii_lowercase();
        if AD.iter().any(|d| l.contains(d)) { return Some("Ad"); }
        if TRK.iter().any(|d| l.contains(d)) { return Some("Tracker"); }
        None
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
            css.push_str(r#"[class*="ad-"],[id*="ad-"],[class*="advert"],[id*="advert"],.adsbygoogle,ins.adsbygoogle,#google_ads,div[id^="google_ads"],div[id^="div-gpt-ad"],iframe[src*="doubleclick"],iframe[src*="googlesyndication"],[class*="sponsor"],[id*="banner"],.ad-container,.adsbox,.ad-slot,.ad_label,[data-ad],[aria-label="Advertisement"],[class*="commercial"]{display:none!important;height:0!important;width:0!important;overflow:hidden!important}"#);
            // pages render via srcdoc → window.location is about:srcdoc, use baseURI
            js.push_str(r#"
            if ((function(){try{return new URL(document.baseURI).hostname}catch(e){return''}})().includes('youtube.com')) {
                setInterval(() => {
                    const skipBtn = document.querySelector('.ytp-ad-skip-button, .ytp-ad-skip-button-modern, .ytp-skip-ad-button');
                    if (skipBtn) { skipBtn.click(); }
                    const ad = document.querySelector('.ad-showing video');
                    if (ad && !isNaN(ad.duration)) { ad.currentTime = ad.duration; }
                    document.querySelectorAll('ytd-ad-slot-renderer, ytd-promoted-sparkles-web-renderer, ytd-banner-promo-renderer').forEach(e => e.remove());
                }, 300);
            }
            "#);
        }

        // F6/F7/F8: Brave-style blocking — fetch/XHR/beacon hooks + WebSocket/EventSource
        //    + a MutationObserver stripping script/img/iframe nodes pointing at known hosts.
        if cfg.ad || cfg.trk {
            js.push_str(r#"
            !function(){
                const NX_ADS=['doubleclick','googlesyndication','googleadservices','adservice.google','adsystem','adsense','adnxs','rubiconproject','pubmatic','openx','casalemedia','criteo','taboola','outbrain','bidswitch','adsrvr','amazon-adsystem','scorecardresearch','moatads','zedo','popads','popcash','mgid','revcontent','adsterra','propellerads','teads','smartadserver'];
                const NX_TRK=['googletagmanager','google-analytics','analytics.google','segment.io','segment.com','mixpanel','hotjar','crazyegg','mouseflow','fullstory','logrocket','heapanalytics','amplitude','branch.io','appsflyer','kochava','chartbeat','mc.yandex','clarity.ms','facebook.com/tr','bat.bing','analytics.tiktok','tr.snapchat','stats.wp.com','trackcmp'];
                const asUrl=u=>{try{if(typeof u==='string')return new URL(u,document.baseURI);if(u&&u.url)return new URL(u.url,document.baseURI);if(u&&u.href)return new URL(u.href,document.baseURI);}catch(e){}return null};
                const kindOfHost=h=>{const s=String(h||'').toLowerCase();if(NX_ADS.some(t=>s.indexOf(t)>=0))return'Ad';if(NX_TRK.some(t=>s.indexOf(t)>=0))return'Tracker';return''};
                const blockedHost=h=>!!kindOfHost(h);
                const notify=u=>{try{const x=asUrl(u);window.top.postMessage(JSON.stringify({a:'inc',p:x?x.href:String(u)}),'*')}catch(e){}};
                const matches=u=>{const x=asUrl(u);return !!(x&&blockedHost(x.hostname))};

                const origFetch=window.fetch;
                window.fetch=function(input,init){
                    if(matches(input)){notify(input);return Promise.reject(new Error('Blocked by Nexus'));}
                    return origFetch.apply(this,arguments);
                };
                const origOpen=XMLHttpRequest.prototype.open;
                XMLHttpRequest.prototype.open=function(method,url){
                    if(matches(url)){notify(url);return;}
                    return origOpen.apply(this,arguments);
                };
                if(navigator.sendBeacon){
                    const origBeacon=navigator.sendBeacon.bind(navigator);
                    navigator.sendBeacon=function(u,d){if(matches(u)){notify(u);return false;}return origBeacon(u,d);};
                }
                try{
                    const OWs=window.WebSocket;
                    const WS=function(url,protocols){
                        if(matches(url)){notify(url);return new OWs('wss://nexus-blocked.invalid');}
                        return protocols===undefined?new OWs(url):new OWs(url,protocols);
                    };
                    WS.prototype=OWs.prototype; window.WebSocket=WS;
                }catch(e){}
                try{
                    const OES=window.EventSource;
                    const ES=function(url,config){
                        if(matches(url)){notify(url);return new OES('https://nexus-blocked.invalid');}
                        return config===undefined?new OES(url):new OES(url,config);
                    };
                    ES.prototype=OES.prototype; window.EventSource=ES;
                }catch(e){}

                // subresource stripping: script/img/iframe/embed/object/video/audio/source/link
                const BLOCK_TAGS={script:1,iframe:1,img:1,embed:1,object:1,video:1,audio:1,source:1,link:1};
                const stripEl=el=>{
                    if(!el||el.nodeType!==1)return;
                    const tag=(el.tagName||'').toLowerCase();
                    if(!BLOCK_TAGS[tag])return;
                    const u=el.src||el.href||'';
                    if(!u)return;
                    const x=asUrl(u); if(!x)return;
                    if(blockedHost(x.hostname)){
                        notify(x.href);
                        try{el.remove()}catch(e){try{el.parentNode&&el.parentNode.removeChild(el)}catch(e2){}}
                    }
                };
                const scan=root=>{try{if(root&&root.querySelectorAll)root.querySelectorAll('script,iframe,img,embed,object,video,audio,source,link').forEach(stripEl)}catch(e){}};
                try{
                    const mo=new MutationObserver(muts=>{
                        for(const m of muts){
                            const nodes=m.addedNodes||[];
                            for(let i=0;i<nodes.length;i++){const n=nodes[i];stripEl(n);if(n&&n.nodeType===1)scan(n);}
                        }
                    });
                    mo.observe(document.documentElement||document,{childList:true,subtree:true});
                    document.addEventListener('DOMContentLoaded',function(){scan(document)});
                }catch(e){}
            }();
            "#);
        }

        if cfg.cookie { js.push_str(r#"!function(){const t=Object.getOwnPropertyDescriptor(Document.prototype,"cookie");t&&(Object.defineProperty(document,"cookie",{set(n){/(_ga|_gid|_gcl|_fbp|_uet|__qca|_hj|track)/.test(n)||t.set.call(this,n)},get(){return t.get.call(this)}}))}()"#); }

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
            try{Object.defineProperty(navigator,"deviceMemory",{get:()=>4})}catch(e){}
            Object.defineProperty(navigator,"platform",{get:()=>"Win32"});
            try{Object.defineProperty(navigator,"webdriver",{get:()=>false})}catch(e){}
        }()
        "#); }

        // navigation + password helpers — all URLs come from document.baseURI (srcdoc!)
        js.push_str(r#"
        !function(){
            const nxBase=()=>{try{return document.baseURI||window.location.href}catch(e){return''}};
            window.nexusGeneratePassword=(len)=>{const t="ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789!@#$%^&*";return Array.from(crypto.getRandomValues(new Uint8Array(len||16)),n=>t[n%t.length]).join("")};
            window.nexusFillPassword=(t,n)=>{let o=null,e=null;for(const el of document.querySelectorAll("input"))"password"===el.type&&!e&&(e=el),(/text|email/.test(el.type)||/user|email/i.test(el.name||el.id||''))&&!o&&(o=el);o&&(o.value=t);e&&(e.value=n)};

            let lastSig="";
            const guessUserField=(pwField)=>{
                const inputs=Array.from(document.querySelectorAll('input'));
                const i=inputs.indexOf(pwField);
                for(let k=i-1;k>=0;k--){
                    const el=inputs[k];
                    if(/text|email/.test(el.type)||/user|email|login/i.test(el.name||el.id||''))return el;
                }
                return inputs.find(el=>el!==pwField&&(/text|email/.test(el.type)||/user|email|login/i.test(el.name||el.id||'')))||null;
            };
            // ✅ FIX #19 (kept): exposed so the real submit listener below can call it
            window.__nexusReportPassword=(pwField)=>{
                if(!pwField||!pwField.value)return;
                const userField=guessUserField(pwField);
                const sig=nxBase()+'|'+(userField?userField.value:'')+'|'+pwField.value;
                if(sig===lastSig)return;lastSig=sig;
                window.top.postMessage(JSON.stringify({a:"password-detected",p:{url:nxBase(),username:userField?userField.value:"",password:pwField.value}}),'*');
            };
            document.addEventListener('keydown',function(e){
                if(e.key==='Enter'&&e.target&&e.target.type==='password')window.__nexusReportPassword(e.target);
            },true);
            document.addEventListener('click',function(e){
                const btn=e.target.closest&&e.target.closest('button, input[type="submit"], [role="button"], a');
                if(!btn)return;
                const label=(btn.textContent||btn.value||'').trim();
                if(!/log\s*in|sign\s*in|submit|continue|next/i.test(label)&&btn.type!=='submit')return;
                const pw=document.querySelector('input[type="password"]');
                if(pw&&pw.value)window.__nexusReportPassword(pw);
            },true);
        }();

        document.addEventListener('click', function(e){
            let a=e.target.closest&&e.target.closest('a');
            if(!a||!a.href||a.href.startsWith('javascript:')||a.href.startsWith('#')||/^(mailto|tel):/i.test(a.href))return;
            e.preventDefault();e.stopPropagation();e.stopImmediatePropagation();
            if(/\.(zip|rar|7z|tar|gz|xz|exe|msi|apk|iso|dmg|pdf|mp3|mp4|mkv|avi|docx?|xlsx?|pptx?)(\?|#|$)/i.test(a.href)){
                window.top.postMessage(JSON.stringify({a:'dl-start',p:a.href}),'*');return;
            }
            if(a.target==='_blank'||e.ctrlKey||e.metaKey){ window.top.postMessage(JSON.stringify({a:'new-tab-url',p:a.href}),'*'); }
            else{ window.top.postMessage(JSON.stringify({a:'nav-internal',p:a.href}),'*'); }
        }, true);
        document.addEventListener('auxclick', function(e){
            if(e.button!==1)return;
            let a=e.target.closest&&e.target.closest('a');
            if(a&&a.href&&!a.href.startsWith('javascript:')){ e.preventDefault();window.top.postMessage(JSON.stringify({a:'new-tab-url',p:a.href}),'*'); }
        }, true);
        // ✅ FIX #11 (kept) + srcdoc: forms resolve against document.baseURI
        document.addEventListener('submit', function(e){
            e.preventDefault();
            let form=e.target;
            const pwField=form.querySelector&&form.querySelector('input[type="password"]');
            if(pwField&&window.__nexusReportPassword)window.__nexusReportPassword(pwField);
            let method=(form.method||'get').toLowerCase();
            let base=document.baseURI||window.location.href;
            let url;try{url=new URL(form.action||base,base)}catch(_){url=new URL(base)}
            let formData=new FormData(form);
            let hasFiles=false;
            for(let [k,v] of formData.entries()){if(v instanceof File){hasFiles=true;break}}
            if(method==='get'){
                for(let [k,v] of formData.entries()){if(!(v instanceof File))url.searchParams.append(k,v)}
                window.top.postMessage(JSON.stringify({a:'nav-internal',p:url.href}),'*');
            }else if(hasFiles){
                fetch(url.href,{method:'POST',body:formData})
                    .catch(function(){})
                    .finally(function(){window.top.postMessage(JSON.stringify({a:'nav-internal',p:url.href}),'*')});
            }else{
                let body={};
                for(let [k,v] of formData.entries()){body[k]=v}
                window.top.postMessage(JSON.stringify({a:'nav-post',p:{url:url.href,body:body}}),'*');
            }
        }, true);
        window.addEventListener('message',function(e){
            try{const m=JSON.parse(e.data);
                if(m&&m.a==='nexus-fill'&&m.p&&window.nexusFillPassword)window.nexusFillPassword(m.p.pass,m.p.user);
            }catch(_){}
        });
        window.open=function(url){window.top.postMessage(JSON.stringify({a:'new-tab-url',p:url}),'*');return null;};
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

    // ✅ FIX #22 (kept): b64_decode() takes a &mut buffer and returns a borrowed slice
    #[allow(deprecated)]
    pub fn encrypt(data: &str, master: &str) -> Option<(String, String, String)> {
        if master.is_empty() { return None; }
        let salt = SaltString::generate(rand::thread_rng());
        let mut salt_buf = [0u8; 64];
        let salt_bytes = salt.b64_decode(&mut salt_buf).ok()?;
        let key = derive_key(master, salt_bytes)?;
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

    #[allow(deprecated)]
    pub fn decrypt(enc: &str, nonce: &str, salt: &str, master: &str) -> Option<String> {
        let ciphertext = general_purpose::STANDARD.decode(enc).ok()?;
        let nonce_bytes = general_purpose::STANDARD.decode(nonce).ok()?;
        if nonce_bytes.len() != 12 { return None; }

        let salt_value = SaltString::from_b64(salt).ok()?;
        let mut salt_buf = [0u8; 64];
        let salt_bytes = salt_value.b64_decode(&mut salt_buf).ok()?;
        let key = derive_key(master, salt_bytes)?;
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
// MODULE: SYNC (stub)
// ======================
mod sync {
    use super::*;
    pub fn import_from_chrome() -> Result<Vec<state::VaultEntry>, String> { Ok(Vec::new()) }
    pub fn import_from_firefox() -> Result<Vec<state::VaultEntry>, String> { Ok(Vec::new()) }
    pub fn import_from_edge() -> Result<Vec<state::VaultEntry>, String> { Ok(Vec::new()) }
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
            let manifest_content = fs::read_to_string(path.join(MANIFEST_FILE)).await.map_err(|e| format!("Failed to read manifest: {}", e))?;
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
                if let Ok(js_content) = fs::read_to_string(self.path.join(js_file)).await {
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
                if let Ok(c) = fs::read_to_string(self.path.join(css_file)).await { css_injection.push_str(&c); }
            }
            Some(css_injection)
        }

        pub async fn get_background_script(&self) -> Option<String> {
            if !self.enabled { return None; }
            let bg = match &self.manifest.background {
                Some(bg) => {
                    if let Some(worker) = &bg.service_worker { Some(self.path.join(worker)) }
                    else if let Some(scripts) = &bg.scripts { scripts.first().map(|s| self.path.join(s)) }
                    else { None }
                }
                None => None,
            };
            match bg { Some(path) => fs::read_to_string(&path).await.ok(), None => None }
        }
    }

    // ✅ FIX #8 (kept): anchored regex avoids false positives
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
}

// ======================
// MODULE: DL (16-thread download with progress)
// ======================
mod dl {
    use super::*;

    const PARTS: usize = 16;

    fn ev(px: &tao::event_loop::EventLoopProxy<Ev>, v: JsonValue) {
        let _ = px.send_event(Ev::Js(format!("if(window.NX)NX.onEvent({})", v)));
    }

    // safe filename: strip query, decode %XX, drop dangerous chars, cap length
    fn safe_name(url: &str) -> String {
        let raw = url.rsplit('/').next().unwrap_or("").split('?').next().unwrap_or("");
        let b = raw.as_bytes();
        let mut out: Vec<u8> = Vec::with_capacity(b.len());
        let mut i = 0;
        while i < b.len() {
            if b[i] == b'%' && i + 2 < b.len() {
                if let Ok(v) = u8::from_str_radix(&raw[i + 1..i + 3], 16) { out.push(v); i += 3; continue; }
            }
            out.push(b[i]); i += 1;
        }
        let s = String::from_utf8_lossy(&out);
        let cleaned: String = s.chars().filter(|c| !matches!(c, '\\' | '/' | ':' | '*' | '?' | '"' | '<' | '>' | '|')).collect();
        let cleaned = cleaned.trim().trim_start_matches('.').to_string();
        if cleaned.is_empty() { "nexus-download.bin".into() } else { cleaned.chars().take(120).collect() }
    }

    pub async fn turbo(url: String, client: reqwest::Client, px: tao::event_loop::EventLoopProxy<Ev>) {
        let id = Uuid::new_v4().to_string();
        let name = safe_name(&url);
        let _ = std::fs::create_dir_all("downloads");
        let path = std::path::PathBuf::from("downloads").join(&name);
        ev(&px, json!({"ev":"dl","p":{"id":id,"name":name,"recv":0,"total":0,"done":false,"error":null}}));

        let (len, ranges) = client.head(&url).send().await.ok()
            .map(|r| (r.content_length().unwrap_or(0),
                r.headers().get("accept-ranges").and_then(|v| v.to_str().ok()).map(|v| v.contains("bytes")).unwrap_or(false)))
            .unwrap_or((0, false));

        if len == 0 || !ranges {
            match client.get(&url).timeout(Duration::from_secs(600)).send().await {
                Ok(mut resp) => {
                    let total = resp.content_length().unwrap_or(0);
                    let mut f = match tokio::fs::File::create(&path).await {
                        Ok(f) => f,
                        Err(_) => { ev(&px, json!({"ev":"dl","p":{"id":id,"done":true,"error":"Could not create file"}})); return; }
                    };
                    let (mut recv, mut last) = (0u64, 0u64);
                    loop {
                        match resp.chunk().await {
                            Ok(Some(ch)) => {
                                recv += ch.len() as u64;
                                if f.write_all(&ch).await.is_err() {
                                    ev(&px, json!({"ev":"dl","p":{"id":id,"done":true,"error":"Write error"}})); return;
                                }
                                if recv - last >= 262144 { last = recv;
                                    ev(&px, json!({"ev":"dl","p":{"id":id,"recv":recv,"total":total,"done":false}})); }
                            }
                            Ok(None) => break,
                            Err(e) => { ev(&px, json!({"ev":"dl","p":{"id":id,"done":true,"error":format!("Network error: {}", e)}})); return; }
                        }
                    }
                    ev(&px, json!({"ev":"dl","p":{"id":id,"recv":recv,"total":total,"done":true,"error":null}}));
                }
                Err(e) => ev(&px, json!({"ev":"dl","p":{"id":id,"done":true,"error":format!("Network error: {}", e)}})),
            }
            return;
        }

        let chunk = len.div_ceil(PARTS as u64);
        let file = match tokio::fs::OpenOptions::new().write(true).create(true).truncate(true).open(&path).await {
            Ok(f) => Arc::new(TokioMutex::new(f)),
            Err(_) => { ev(&px, json!({"ev":"dl","p":{"id":id,"done":true,"error":"Could not create file"}})); return; }
        };

        // ✅ FIX #12 (kept): permit guard lives to end of scope → auto-release
        let (sem, recv_sum, failed) = (Arc::new(Semaphore::new(PARTS)), Arc::new(AtomicUsize::new(0)), Arc::new(AtomicUsize::new(0)));
        let mut set = JoinSet::new();

        for i in 0..PARTS {
            let (client, url, sem, file, recv_sum, failed, px) =
                (client.clone(), url.clone(), sem.clone(), file.clone(), recv_sum.clone(), failed.clone(), px.clone());
            let (s, e) = (i as u64 * chunk, (i as u64 * chunk + chunk - 1).min(len - 1));
            if s > e { continue; }
            let id2 = id.clone();
            set.spawn(async move {
                let _permit = match sem.acquire_owned().await { Ok(p) => p, Err(_) => return };
                let response = client.get(&url).header("Range", format!("bytes={}-{}", s, e)).send().await;
                if let Ok(response) = response {
                    if let Ok(bytes) = response.bytes().await {
                        recv_sum.fetch_add(bytes.len(), Ordering::SeqCst);
                        let mut f = file.lock().await;
                        if f.seek(std::io::SeekFrom::Start(s)).await.is_ok() { f.write_all(&bytes).await.ok(); }
                        else { failed.fetch_add(1, Ordering::SeqCst); }
                    } else { failed.fetch_add(1, Ordering::SeqCst); }
                } else { failed.fetch_add(1, Ordering::SeqCst); }
                ev(&px, json!({"ev":"dl","p":{"id":id2,"recv":recv_sum.load(Ordering::SeqCst),"total":len,"done":false}}));
            });
        }

        while set.join_next().await.is_some() {}
        if failed.load(Ordering::SeqCst) > 0 {
            let _ = tokio::fs::remove_file(&path).await;
            ev(&px, json!({"ev":"dl","p":{"id":id,"done":true,"error":"A part failed — removed partial file"}}));
        } else {
            ev(&px, json!({"ev":"dl","p":{"id":id,"recv":len,"total":len,"done":true,"error":null}}));
        }
    }
}

// ======================
// MODULE: SEARCH
// ======================
mod search {
    pub fn resolve(i: &str) -> String { resolve_engine(i, "duckduckgo") }

    pub fn resolve_engine(i: &str, engine: &str) -> String {
        let t = i.trim();
        if t.is_empty() { return "nexus://home".into(); }
        if t.starts_with("http://") || t.starts_with("https://") || t.starts_with("nexus://") { return t.into(); }
        let looks_like_host = !t.contains(' ')
            && !t.starts_with('.') && !t.ends_with('.')
            && (t.contains('.') || t.starts_with("localhost"));
        if looks_like_host { return format!("https://{}", t); }
        let q: String = url::form_urlencoded::byte_serialize(t.as_bytes()).collect();
        match engine {
            "google" => format!("https://www.google.com/search?q={}", q),
            "bing" => format!("https://www.bing.com/search?q={}", q),
            "brave" => format!("https://search.brave.com/search?q={}", q),
            "startpage" => format!("https://www.startpage.com/sp/search?query={}", q),
            _ => format!("https://html.duckduckgo.com/html/?q={}", q),
        }
    }
}

// ======================
// MAIN HTML (UI)
// ======================
fn html() -> String {
    r###"<!DOCTYPE html>
<html lang="en" data-theme="light">
<head><meta charset="UTF-8"><title>Nexus</title>
<style>
*{box-sizing:border-box;margin:0;padding:0;font-family:-apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,Arial,sans-serif}
:root{--bg:#dfe3e8;--panel:#fff;--input:#f1f3f4;--brd:#dadce0;--acc:#1a73e8;--on-acc:#fff;--t1:#202124;--t2:#5f6368;--t3:#80868b;--star:#f9ab00;--ok:#188038;--bad:#d93025;--tabh:36px;--tbh:44px}
html[data-theme=dark]{--bg:#141517;--panel:#232427;--input:#2b2c31;--brd:#3c3d42;--acc:#8ab4f8;--on-acc:#062e6f;--t1:#e8eaed;--t2:#b0b3b8;--t3:#8a8d93;--star:#fdd663;--ok:#81c995;--bad:#f28b82}
html[data-density=compact]{--tabh:30px;--tbh:38px}
html,body{height:100%}
body{background:var(--bg);color:var(--t1);overflow:hidden;font-size:13px;user-select:none}
button{font:inherit;color:inherit;background:none;border:none;cursor:pointer}
svg{fill:none;stroke:currentColor;stroke-width:1.8;stroke-linecap:round;stroke-linejoin:round;display:block;width:18px;height:18px}
::-webkit-scrollbar{width:9px;height:9px}::-webkit-scrollbar-thumb{background:var(--brd);border-radius:9px}::-webkit-scrollbar-track{background:transparent}
#app{display:flex;flex-direction:column;height:100vh}

#tabs-bar{display:flex;align-items:flex-end;height:calc(var(--tabh) + 8px);padding:6px 8px 0;gap:3px}
#tabs{display:flex;align-items:flex-end;gap:3px;overflow-x:auto;flex:1;min-width:0;scrollbar-width:none}
#tabs::-webkit-scrollbar{display:none}
.tab{display:flex;align-items:center;height:var(--tabh);min-width:150px;max-width:230px;padding:0 6px 0 12px;border-radius:9px 9px 0 0;color:var(--t2);position:relative;flex-shrink:1;transition:background .15s}
.tab:hover{background:color-mix(in srgb,var(--t1) 7%,transparent)}
.tab.active{background:var(--panel);color:var(--t1)}
.tab.frozen{opacity:.5}
.tab-favicon{width:17px;height:17px;border-radius:4px;flex-shrink:0;margin-right:8px;display:flex;align-items:center;justify-content:center;font-size:10px;font-weight:700;color:var(--on-acc);background:var(--acc);text-transform:uppercase}
.tab.incog .tab-favicon{background:#8e44ad}
.tab-title{flex:1;min-width:0;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;font-weight:500;font-size:12.5px}
.tab-close{width:22px;height:22px;border-radius:50%;display:flex;align-items:center;justify-content:center;color:var(--t3);opacity:0;flex-shrink:0;margin-left:4px}
.tab-close svg{width:12px;height:12px}
.tab:hover .tab-close,.tab.active .tab-close{opacity:1}
.tab-close:hover{background:color-mix(in srgb,var(--t1) 12%,transparent);color:var(--t1)}
#new-tab,#new-private{width:30px;height:30px;border-radius:50%;display:flex;align-items:center;justify-content:center;color:var(--t2);flex-shrink:0;margin:0 0 4px 3px}
#new-tab svg,#new-private svg{width:16px;height:16px}
#new-tab:hover,#new-private:hover{background:color-mix(in srgb,var(--t1) 9%,transparent);color:var(--t1)}

#toolbar{display:flex;align-items:center;gap:2px;height:var(--tbh);padding:0 10px;background:var(--panel);border-bottom:1px solid var(--brd);position:relative;z-index:50}
#loadbar{position:absolute;left:0;bottom:0;height:2.5px;width:0;background:var(--acc);opacity:0;transition:width .3s ease,opacity .25s;z-index:5}
#loadbar.show{opacity:1}
.nbtn{min-width:34px;height:34px;border-radius:50%;display:flex;align-items:center;justify-content:center;color:var(--t2);flex-shrink:0;padding:0 4px;position:relative}
.nbtn:hover{background:var(--input);color:var(--t1)}
.nbtn:disabled{opacity:.35}.nbtn:disabled:hover{background:none}
#url-wrap{flex:1;min-width:0;display:flex;align-items:center;height:34px;background:var(--input);border:1px solid transparent;border-radius:17px;padding:0 4px 0 12px;margin:0 6px;position:relative;transition:background .15s,box-shadow .15s}
#url-wrap.focus{background:var(--panel);border-color:var(--brd);box-shadow:0 2px 10px rgba(0,0,0,.14)}
#sec-ic{display:flex;flex-shrink:0;color:var(--t3)}
#sec-ic svg{width:15px;height:15px}
#sec-ic.ok{color:var(--ok)}#sec-ic.bad{color:var(--bad)}
#url{flex:1;min-width:0;border:none;background:none;outline:none;font-size:13.5px;color:var(--t1);padding:0 8px;user-select:text}
#btn-star{width:28px;height:28px;border-radius:50%;display:flex;align-items:center;justify-content:center;color:var(--t3);flex-shrink:0}
#btn-star svg{width:16px;height:16px}
#btn-star:hover{background:var(--brd);color:var(--t1)}
#btn-star.saved{color:var(--star)}#btn-star.saved svg{fill:var(--star)}
#btn-shield{height:30px;padding:0 12px;border-radius:15px;border:1px solid var(--brd);color:var(--t2);font-weight:600;font-size:12px;display:flex;align-items:center;gap:6px;flex-shrink:0;margin-left:4px}
#btn-shield svg{width:14px;height:14px}
#btn-shield:hover{background:var(--input);color:var(--t1)}
.badge{position:absolute;top:1px;right:0;background:var(--bad);color:#fff;font-size:9px;font-weight:700;min-width:15px;height:15px;border-radius:8px;display:flex;align-items:center;justify-content:center;padding:0 3px}

#suggest{position:absolute;top:calc(100% + 6px);left:0;right:0;background:var(--panel);border:1px solid var(--brd);border-radius:12px;box-shadow:0 12px 32px rgba(0,0,0,.22);display:none;z-index:600;max-height:320px;overflow-y:auto}
.sug-item{display:flex;align-items:center;gap:10px;padding:9px 14px;cursor:pointer}
.sug-item:hover,.sug-item.sel{background:var(--input)}
.sug-ic{color:var(--t3);display:flex;flex-shrink:0}.sug-ic svg{width:15px;height:15px}
.sug-t{color:var(--t1);white-space:nowrap;overflow:hidden;text-overflow:ellipsis;max-width:55%}
.sug-u{color:var(--t3);font-size:12px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;flex:1;text-align:right}

#bm-bar{display:flex;align-items:center;gap:2px;height:32px;padding:0 12px;background:var(--panel);border-bottom:1px solid var(--brd);overflow-x:auto}
.bm-item{padding:4px 10px;border-radius:6px;color:var(--t2);white-space:nowrap;cursor:pointer;font-size:12.5px}
.bm-item:hover{background:var(--input);color:var(--t1)}

#workspace{flex:1;position:relative;background:var(--panel);overflow:hidden}
#view{position:absolute;inset:0;width:100%;height:100%;border:none;background:#fff}
html[data-theme=dark] #view{background:#1b1c1f}
#newtab,#settings{position:absolute;inset:0;overflow-y:auto;display:none;background:var(--panel)}
#newtab{flex-direction:column}

.nt-wrap{margin:auto;max-width:560px;padding:40px 20px;text-align:center;display:flex;flex-direction:column;gap:22px}
.nt-logo{font-size:36px;font-weight:800;letter-spacing:-1.5px}.nt-logo b{color:var(--acc)}
#nt-greet{color:var(--t2);font-size:14px;margin-top:-14px}
.nt-search{display:flex;align-items:center;height:46px;border:1px solid var(--brd);border-radius:23px;padding:0 8px 0 18px;background:var(--input);box-shadow:0 1px 6px rgba(0,0,0,.08)}
.nt-search:focus-within{border-color:var(--acc);background:var(--panel);box-shadow:0 2px 14px color-mix(in srgb,var(--acc) 30%,transparent)}
.nt-search svg{width:18px;height:18px;color:var(--t3)}
#nt-q{flex:1;border:none;background:none;outline:none;font-size:15px;color:var(--t1);padding:0 12px;user-select:text}
.nt-grid{display:grid;grid-template-columns:repeat(4,1fr);gap:14px}
.nt-link{display:flex;flex-direction:column;align-items:center;gap:8px;padding:12px 6px;border-radius:12px;cursor:pointer}
.nt-link:hover{background:var(--input)}
.nt-ico{width:42px;height:42px;border-radius:12px;display:flex;align-items:center;justify-content:center;color:#fff;font-weight:700;font-size:16px}
.nt-link span{font-size:12px;color:var(--t2);max-width:100%;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
#nt-stats{color:var(--t3);font-size:12px}
#nt-hint{color:var(--t3);font-size:11.5px}

.set-nav{width:220px;flex-shrink:0;border-right:1px solid var(--brd);padding:16px 10px;display:flex;flex-direction:column;gap:2px}
.set-back{display:flex;align-items:center;gap:8px;padding:10px 12px;margin-bottom:10px;border-radius:8px;color:var(--t2);font-weight:600;cursor:pointer}
.set-back svg{width:16px;height:16px}
.set-back:hover{background:var(--input);color:var(--t1)}
.set-nav-item{display:flex;align-items:center;gap:10px;padding:10px 14px;border-radius:8px;color:var(--t2);cursor:pointer}
.set-nav-item svg{width:15px;height:15px}
.set-nav-item.on{background:color-mix(in srgb,var(--acc) 14%,transparent);color:var(--acc);font-weight:600}
.set-body{flex:1;overflow-y:auto;padding:24px 32px;user-select:text}
.set-sec{max-width:640px;margin-bottom:30px;scroll-margin-top:16px}
.set-h{font-size:17px;font-weight:700;margin-bottom:4px}
.set-sub{color:var(--t3);font-size:12px;margin-bottom:14px}
.card{border:1px solid var(--brd);border-radius:12px;overflow:hidden;margin-bottom:14px}
.crow{display:flex;align-items:center;justify-content:space-between;padding:13px 16px;border-bottom:1px solid var(--brd);gap:12px}
.crow:last-child{border-bottom:none}
.crow .ct{font-weight:500}.crow .cd{color:var(--t3);font-size:11.5px;margin-top:2px}
.sw{position:relative;width:36px;height:20px;flex-shrink:0;display:inline-block}
.sw input{display:none}
.sw span{position:absolute;inset:0;border-radius:12px;background:var(--brd);transition:.18s;cursor:pointer}
.sw span::before{content:"";position:absolute;width:14px;height:14px;border-radius:50%;background:#fff;top:3px;left:3px;transition:.18s;box-shadow:0 1px 2px rgba(0,0,0,.3)}
.sw input:checked+span{background:var(--acc)}
.sw input:checked+span::before{transform:translateX(16px)}
.seg{display:flex;background:var(--input);border-radius:9px;padding:3px;flex-shrink:0}
.seg button{padding:5px 12px;border-radius:7px;color:var(--t2);font-weight:500;font-size:12.5px}
.seg button.on{background:var(--panel);color:var(--t1);box-shadow:0 1px 3px rgba(0,0,0,.15)}
.tin{width:100%;padding:9px 12px;background:var(--input);border:1px solid var(--brd);border-radius:8px;color:var(--t1);outline:none;font-size:13px;user-select:text}
.tin:focus{border-color:var(--acc);background:var(--panel)}
.btn{padding:9px 16px;border-radius:8px;border:1px solid var(--brd);background:var(--panel);color:var(--t1);font-weight:600;cursor:pointer}
.btn:hover{background:var(--input)}
.btn.pri{background:var(--acc);border-color:var(--acc);color:var(--on-acc)}
.btn.danger{color:var(--bad)}
.radios{display:flex;flex-direction:column}
.radio{display:flex;align-items:center;gap:10px;padding:11px 16px;border-bottom:1px solid var(--brd);cursor:pointer}
.radio:last-child{border-bottom:none}
.radio input{accent-color:var(--acc)}
.swatches{display:flex;gap:8px}
.swatch{width:22px;height:22px;border-radius:50%;border:2px solid transparent;cursor:pointer}
.swatch.on{border-color:var(--t1)}
.p-note{padding:9px 12px;color:var(--t3);font-size:11.5px;line-height:1.55}

.p-row{display:flex;align-items:center;gap:10px;padding:10px 16px;border-bottom:1px solid color-mix(in srgb,var(--brd) 55%,transparent)}
.p-row:last-child{border-bottom:none}
.p-ic{width:26px;display:flex;justify-content:center;color:var(--t3);flex-shrink:0}
.p-ic svg{width:15px;height:15px}
.p-main{flex:1;min-width:0;cursor:pointer}
.p-t{color:var(--t1);font-size:12.5px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.p-u{color:var(--t3);font-size:11px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.p-act{display:flex;gap:2px;flex-shrink:0}
.p-act button{width:28px;height:28px;border-radius:50%;display:flex;align-items:center;justify-content:center;color:var(--t3)}
.p-act svg{width:14px;height:14px}
.p-act button:hover{background:var(--input);color:var(--t1)}
.p-row.err .p-t{color:var(--bad)}
.p-row.done .p-ic{color:var(--ok)}
.dl-bar{height:4px;border-radius:3px;background:var(--input);overflow:hidden;margin-top:6px}
.dl-bar i{display:block;height:100%;background:var(--acc);width:0;transition:width .2s}
.empty{padding:36px 20px;text-align:center;color:var(--t3);font-size:12.5px;line-height:1.7}
.krow{display:flex;gap:16px;padding:9px 16px;border-bottom:1px solid color-mix(in srgb,var(--brd) 55%,transparent);font-size:13px}
.krow:last-child{border-bottom:none}
.kk{width:150px;color:var(--t2);font-weight:600;flex-shrink:0;font-size:12px}

.pop{position:fixed;top:50px;min-width:240px;max-width:360px;background:var(--panel);border:1px solid var(--brd);border-radius:12px;box-shadow:0 14px 40px rgba(0,0,0,.22);z-index:800;padding:7px;display:none}
.pop.show{display:block;animation:popin .13s ease}
@keyframes popin{from{opacity:0;transform:translateY(-5px)}}
.pop-item{display:flex;align-items:center;gap:11px;padding:9px 12px;border-radius:8px;color:var(--t1);cursor:pointer;font-size:13px;white-space:nowrap}
.pop-item svg{width:16px;height:16px;color:var(--t2)}
.pop-item:hover{background:var(--input)}
.pop-item .kbd{margin-left:auto;color:var(--t3);font-size:11px}
.pop-sep{height:1px;background:var(--brd);margin:6px 4px}
.pop-note{padding:8px 12px;color:var(--t3);font-size:11px;line-height:1.5}
.sp-head{padding:10px 12px 6px;font-weight:700;font-size:13px}
.sp-count{padding:2px 12px 8px;color:var(--t2);font-size:12px;border-bottom:1px solid var(--brd);margin-bottom:6px}
.sl-wrap{max-height:180px;overflow-y:auto;margin:0 4px 6px;border:1px solid color-mix(in srgb,var(--brd) 60%,transparent);border-radius:8px}
.sl-row{display:flex;align-items:center;gap:8px;padding:6px 10px;font-size:11.5px;border-bottom:1px solid color-mix(in srgb,var(--brd) 40%,transparent)}
.sl-row:last-child{border-bottom:none}
.sl-u{flex:1;min-width:0;color:var(--t1);overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.sl-t{color:var(--t3);flex-shrink:0}
.sl-n{color:var(--acc);font-weight:700;flex-shrink:0}
.sp-lv{padding:8px 12px 4px;font-size:11px;color:var(--t3);font-weight:700;text-transform:uppercase;letter-spacing:.5px}

#pass-pop{position:fixed;bottom:24px;right:24px;width:330px;background:var(--panel);border:1px solid var(--brd);border-radius:14px;box-shadow:0 18px 44px rgba(0,0,0,.25);z-index:950;padding:16px;display:none}
#pass-pop.show{display:block;animation:popin .18s ease}
.pp-h{display:flex;align-items:center;gap:9px;font-weight:700;margin-bottom:10px}
.pp-h svg{width:17px;height:17px;color:var(--acc)}
.pp-row{display:flex;justify-content:space-between;padding:5px 0;font-size:12.5px}
.pp-row b{color:var(--t2);font-weight:500;margin-right:10px}
.pp-btns{display:flex;gap:8px;margin-top:12px}
.pp-btns .btn{flex:1;padding:8px}

#toasts{position:fixed;bottom:24px;left:50%;transform:translateX(-50%);z-index:1200;display:flex;flex-direction:column;gap:8px;align-items:center}
.toast{background:#2b2c30;color:#e8eaed;padding:10px 18px;border-radius:10px;font-size:12.5px;box-shadow:0 6px 20px rgba(0,0,0,.3);max-width:70vw;animation:tin2 .2s ease}
.toast.err{background:#c5221f;color:#fff}
.toast.out{opacity:0;transition:opacity .35s}
@keyframes tin2{from{opacity:0;transform:translateY(8px)}}

#devlog{position:fixed;bottom:0;right:0;width:430px;height:230px;background:rgba(23,24,26,.97);color:#d5d7db;border:1px solid #333;border-bottom:none;border-right:none;border-radius:10px 0 0 0;font:11.5px/1.5 Consolas,Menlo,monospace;z-index:1100;display:none;flex-direction:column}
#devlog.show{display:flex}
#devlog .dh{display:flex;justify-content:space-between;align-items:center;padding:6px 10px;color:#8ab4f8;border-bottom:1px solid #333;font-family:inherit}
#devlog .db{flex:1;overflow-y:auto;padding:8px 10px;user-select:text}
.log-line{padding:1px 0;word-break:break-all}.log-line .t{color:#6f7277}
</style></head>
<body>
<div id="app">
 <div id="tabs-bar">
  <div id="tabs"></div>
  <button id="new-tab" title="New tab (Ctrl+T)"></button>
  <button id="new-private" title="Private tab (Ctrl+Shift+N)"></button>
 </div>
 <div id="toolbar">
  <div id="loadbar"></div>
  <button class="nbtn" id="btn-back" title="Back (Alt+←)"></button>
  <button class="nbtn" id="btn-fwd" title="Forward (Alt+→)"></button>
  <button class="nbtn" id="btn-reload" title="Reload (Ctrl+R)"></button>
  <button class="nbtn" id="btn-home" title="Home"></button>
  <div id="url-wrap">
   <span id="sec-ic" title="Internal Nexus page"></span>
   <input id="url" placeholder="Search or type URL" spellcheck="false" autocomplete="off">
   <div id="suggest"></div>
   <button id="btn-star" title="Bookmark (Ctrl+D)"></button>
  </div>
  <button id="btn-shield" title="Protections — click for details"></button>
  <button class="nbtn" id="btn-dl" title="Downloads (Ctrl+J)"><span class="badge" id="dl-badge" style="display:none">0</span></button>
  <button class="nbtn" id="btn-menu" title="Menu"></button>
 </div>
 <div id="bm-bar"></div>
 <div id="workspace">
  <iframe id="view" sandbox="allow-scripts allow-forms allow-modals"></iframe>
  <div id="newtab"><div class="nt-wrap">
   <div class="nt-logo">ne<b>x</b>us</div>
   <div id="nt-greet"></div>
   <div class="nt-search"><span id="nt-sic"></span><input id="nt-q" placeholder="Search the web or enter URL"></div>
   <div class="nt-grid" id="nt-links"></div>
   <div id="nt-stats"></div>
   <div id="nt-hint">Ctrl+T New tab · Ctrl+L Address bar · Ctrl+H History · Alt+← Back</div>
  </div></div>
  <div id="settings"></div>
 </div>
</div>
<div class="pop" id="menu-pop"></div>
<div class="pop" id="shield-pop"></div>
<div class="pop" id="dl-pop"></div>
<div id="pass-pop">
 <div class="pp-h"><span id="pp-ic"></span><span>Save password to Vault?</span></div>
 <div class="pp-row"><b>Site</b><span id="pp-site"></span></div>
 <div class="pp-row"><b>Username</b><span id="pp-user"></span></div>
 <div id="pp-master-row" style="display:none;margin-top:8px"><input class="tin" id="pp-master" type="password" placeholder="Vault master password"></div>
 <div class="pp-btns"><button class="btn pri" id="pp-save">Save</button><button class="btn" id="pp-no">Not now</button></div>
</div>
<div id="toasts"></div>
<div id="devlog"><div class="dh"><span>NEXUS CONSOLE</span><button id="devlog-close">✕</button></div><div class="db" id="devlog-body"></div></div>
<script>
(function(){
'use strict';
var $=function(s,r){return (r||document).querySelector(s)};
var $$=function(s,r){return Array.prototype.slice.call((r||document).querySelectorAll(s))};
function h(t,c,html){var e=document.createElement(t);if(c)e.className=c;if(html!=null)e.innerHTML=html;return e}
function esc(s){return String(s==null?'':s).replace(/[&<>"']/g,function(m){return({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'})[m]})}

/* ===== SVG icons ===== */
var I={
back:'<svg viewBox="0 0 24 24"><path d="M15 18l-6-6 6-6"/></svg>',
fwd:'<svg viewBox="0 0 24 24"><path d="M9 18l6-6-6-6"/></svg>',
reload:'<svg viewBox="0 0 24 24"><path d="M20 12a8 8 0 1 1-2.34-5.66M20 4v5h-5"/></svg>',
home:'<svg viewBox="0 0 24 24"><path d="M3 11l9-8 9 8M5 10v10h5v-6h4v6h5V10"/></svg>',
plus:'<svg viewBox="0 0 24 24"><path d="M12 5v14M5 12h14"/></svg>',
close:'<svg viewBox="0 0 24 24"><path d="M6 6l12 12M18 6L6 18"/></svg>',
star:'<svg viewBox="0 0 24 24"><path d="M12 3l2.7 5.6 6.1.9-4.4 4.3 1 6.1L12 17l-5.4 2.9 1-6.1L3.2 9.5l6.1-.9z"/></svg>',
shield:'<svg viewBox="0 0 24 24"><path d="M12 3l7 3v5c0 4.8-3.2 8.3-7 10-3.8-1.7-7-5.2-7-10V6z"/></svg>',
dl:'<svg viewBox="0 0 24 24"><path d="M12 3v12M8 11l4 4 4-4M5 21h14"/></svg>',
dots:'<svg viewBox="0 0 24 24"><circle cx="12" cy="5" r="1.4" style="fill:currentColor;stroke:none"/><circle cx="12" cy="12" r="1.4" style="fill:currentColor;stroke:none"/><circle cx="12" cy="19" r="1.4" style="fill:currentColor;stroke:none"/></svg>',
lock:'<svg viewBox="0 0 24 24"><rect x="5" y="11" width="14" height="9" rx="2"/><path d="M8 11V7a4 4 0 0 1 8 0v4"/></svg>',
globe:'<svg viewBox="0 0 24 24"><circle cx="12" cy="12" r="9"/><path d="M3 12h18M12 3c2.7 2.5 4 5.6 4 9s-1.3 6.5-4 9c-2.7-2.5-4-5.6-4-9s1.3-6.5 4-9"/></svg>',
search:'<svg viewBox="0 0 24 24"><circle cx="11" cy="11" r="7"/><path d="M21 21l-4.3-4.3"/></svg>',
clock:'<svg viewBox="0 0 24 24"><circle cx="12" cy="12" r="9"/><path d="M12 7v5l3.5 2"/></svg>',
trash:'<svg viewBox="0 0 24 24"><path d="M4 7h16M9 7V4h6v3M6 7l1 14h10l1-14"/></svg>',
copy:'<svg viewBox="0 0 24 24"><rect x="9" y="9" width="11" height="11" rx="2"/><path d="M5 15V5a1 1 0 0 1 1-1h10"/></svg>',
key:'<svg viewBox="0 0 24 24"><circle cx="8" cy="12" r="4"/><path d="M12 12h9M18 12v4M21 12v3"/></svg>',
grid:'<svg viewBox="0 0 24 24"><rect x="4" y="4" width="6" height="6" rx="1.5"/><rect x="14" y="4" width="6" height="6" rx="1.5"/><rect x="4" y="14" width="6" height="6" rx="1.5"/><rect x="14" y="14" width="6" height="6" rx="1.5"/></svg>',
gear:'<svg viewBox="0 0 24 24"><circle cx="12" cy="12" r="3"/><path d="M12 2v3M12 19v3M2 12h3M19 12h3M4.9 4.9l2.1 2.1M17 17l2.1 2.1M19.1 4.9L17 7M7 17l-2.1 2.1"/></svg>',
check:'<svg viewBox="0 0 24 24"><path d="M4 12l5 5L20 6"/></svg>',
incog:'<svg viewBox="0 0 24 24"><path d="M4 10l2-5h12l2 5M4 10h16"/><circle cx="8.5" cy="14.5" r="3"/><circle cx="15.5" cy="14.5" r="3"/></svg>',
book:'<svg viewBox="0 0 24 24"><path d="M6 3h12a2 2 0 0 1 2 2v16l-8-4-8 4V5a2 2 0 0 1 2-2z"/></svg>',
folder:'<svg viewBox="0 0 24 24"><path d="M3 6h6l2 2h10v12H3z"/></svg>',
info:'<svg viewBox="0 0 24 24"><circle cx="12" cy="12" r="9"/><path d="M12 8v.5M12 11v5"/></svg>',
arrow:'<svg viewBox="0 0 24 24"><path d="M5 12h14M13 6l6 6-6 6"/></svg>'
};
 $('#btn-back').innerHTML=I.back;$('#btn-fwd').innerHTML=I.fwd;
 $('#btn-reload').innerHTML=I.reload;$('#btn-home').innerHTML=I.home;
 $('#new-tab').innerHTML=I.plus;$('#new-private').innerHTML=I.incog;
 $('#btn-star').innerHTML=I.star;$('#btn-dl').insertAdjacentHTML('afterbegin',I.dl);
 $('#btn-menu').innerHTML=I.dots;$('#btn-shield').innerHTML=I.shield+'<span id="shield-n">0</span>';
 $('#nt-sic').innerHTML=I.search;$('#pp-ic').innerHTML=I.key;

/* ===== local prefs ===== */
var P=Object.assign({theme:'system',accent:'',density:'normal',showBm:true},JSON.parse(localStorage.getItem('nx-prefs')||'{}'));
function saveP(){try{localStorage.setItem('nx-prefs',JSON.stringify(P))}catch(_){}}
function applyTheme(){var t=P.theme;if(t==='system')t=matchMedia('(prefers-color-scheme: dark)').matches?'dark':'light';document.documentElement.dataset.theme=t}
try{matchMedia('(prefers-color-scheme: dark)').addEventListener('change',function(){if(P.theme==='system')applyTheme()})}catch(_){}
applyTheme();
if(P.accent)document.documentElement.style.setProperty('--acc',P.accent);
document.documentElement.dataset.density=P.density;

/* ===== mirror of Rust state ===== */
var S={tabs:[],active:0,pageBlocked:0,blockedRust:0,log:[],rlog:[],canBack:false,canFwd:false,
 bookmarks:[],history:[],config:{},cfg:{},vaultLocked:true,vaultEntries:[],downloads:{},
 cur:{url:'',title:''}};
var booted=false,pendingSec=null,pendingSave=null,pendingAfterUnlock=false;
var ipc=function(a,p){try{if(window.ipc)window.ipc.postMessage(JSON.stringify({a:a,p:p===undefined?null:p}))}catch(e){}};
ipc('get-state');
var bt=0;var bootT=setInterval(function(){if(booted||++bt>8)clearInterval(bootT);else ipc('get-state')},700);

var fmtB=function(n){n=+n||0;if(n<1024)return n+' B';var u=['KB','MB','GB'],i=-1;do{n/=1024;i++}while(n>=1024&&i<2);return n.toFixed(1)+' '+u[i]};
var ago=function(t){var s=Math.max(0,Date.now()/1000-(+t||0));if(s<60)return'just now';if(s<3600)return Math.floor(s/60)+' min ago';if(s<86400)return Math.floor(s/3600)+' h ago';return Math.floor(s/86400)+' d ago'};
function rnd32(n){try{var a=new Uint32Array(n);crypto.getRandomValues(a);return a}catch(e){var a=[];for(var i=0;i<n;i++)a.push(Math.floor(Math.random()*4294967296));return a}}
function toast(kind,text){var t=h('div','toast'+(kind==='err'?' err':''));t.textContent=text;$('#toasts').appendChild(t);setTimeout(function(){t.classList.add('out')},2300);setTimeout(function(){t.remove()},2750)}
function devlog(m){var b=$('#devlog-body');b.appendChild(h('div','log-line','<span class="t">'+new Date().toLocaleTimeString()+'</span> '+esc(m)));while(b.children.length>300)b.firstChild.remove();b.scrollTop=b.scrollHeight}
function toggleDev(force){var d=$('#devlog');var on=force===undefined?!d.classList.contains('show'):force;d.classList.toggle('show',on)}
 $('#devlog-close').onclick=function(){toggleDev(false)};
function copyText(t){if(navigator.clipboard&&navigator.clipboard.writeText){navigator.clipboard.writeText(t).then(function(){toast('ok','Copied')}).catch(function(){fbCopy(t)})}else fbCopy(t)}
function fbCopy(t){var i=h('input');i.value=t;document.body.appendChild(i);i.select();try{document.execCommand('copy');toast('ok','Copied')}catch(e){toast('err','Copy failed')}i.remove()}

/* ===== shield log ===== */
function host(u){try{return new URL(u).hostname||u}catch(e){return String(u).replace(/^https?:\/\//,'').split('/')[0]||u}}
var ADW=['doubleclick','googlesyndication','googleadservices','adsystem','adsense','adnxs','rubiconproject','pubmatic','openx','casalemedia','criteo','taboola','outbrain','mgid','revcontent','adsterra','popads','scorecardresearch','teads'];
var TRW=['analytics','googletagmanager','segment','mixpanel','hotjar','fullstory','logrocket','amplitude','appsflyer','kochava','chartbeat','clarity.ms','facebook.com/tr','bat.bing','tiktok','snapchat','yandex','beacon','track'];
function classify(u){u=String(u||'').toLowerCase();
 if(ADW.some(function(t){return u.indexOf(t)>=0}))return'Ad';
 if(TRW.some(function(t){return u.indexOf(t)>=0}))return'Tracker';
 return'Other'}
function pushLog(u){u=String(u||'');var last=S.log[S.log.length-1];
 if(last&&last.u===u){last.n++}else{S.log.push({u:u,n:1});if(S.log.length>300)S.log.shift()}
 if($('#shield-pop').classList.contains('show'))buildShieldPop()}
function pushRlog(domain,kind){domain=String(domain||'');var f=null;
 for(var i=0;i<S.rlog.length;i++)if(S.rlog[i].domain===domain&&S.rlog[i].kind===kind){f=S.rlog[i];break}
 if(f)f.n++;else{S.rlog.push({domain:domain,kind:kind||'Blocked',n:1});if(S.rlog.length>300)S.rlog.shift()}}

/* ===== protection profiles (unified rules, cookie counted) ===== */
var PROFILES={strict:{ad:true,trk:true,sinkhole:true,anti_fp:true,cookie:true},
 balanced:{ad:true,trk:true,sinkhole:false,anti_fp:false,cookie:false},
 off:{ad:false,trk:false,sinkhole:false,anti_fp:false,cookie:false}};
var PROFILE_DESC={strict:'Strict — blocks ads, trackers, tracking cookies and fingerprinting. Some sites may break.',
 balanced:'Balanced — blocks obvious ads and trackers. Fewer site breakages.',
 off:'Off — no blocking on this tab.'};
function curTabProfile(){var c=S.cfg||{};
 if(c.ad&&c.trk&&c.sinkhole&&c.anti_fp&&c.cookie)return'strict';
 if(c.ad&&c.trk&&!c.sinkhole&&!c.anti_fp&&!c.cookie)return'balanced';
 if(!c.ad&&!c.trk&&!c.sinkhole&&!c.anti_fp&&!c.cookie)return'off';
 return'custom'}
function applyProfile(name){var p=PROFILES[name];if(!p)return;
 for(var k in p)ipc('tab-cfg',{field:k,value:p[k]});
 toast('info','Applying '+({strict:'Strict',balanced:'Balanced',off:'Off'})[name]+' protection — reloading…');
 setTimeout(function(){ipc('reload',null)},250)}
function curGlobalProfile(){var c=S.config||{};
 if(c.ad&&c.trk&&c.sinkhole&&c.anti_fp&&c.cookie)return'strict';
 if(c.ad&&c.trk&&!c.sinkhole&&!c.anti_fp&&!c.cookie)return'balanced';
 if(!c.ad&&!c.trk)return'off';
 return'custom'}
function applyGlobalProfile(name){var f=PROFILES[name];if(f)ipc('set-config',f)}

/* ===== render tabs / nav / bars ===== */
function renderTabs(){var w=$('#tabs');w.innerHTML='';
 S.tabs.forEach(function(t){
  var el=h('div','tab'+(t.active?' active':'')+(t.mode==='incognito'?' incog':'')+(t.frozen?' frozen':''));
  var fv='<span class="tab-favicon">'+esc((t.title||'?').trim().charAt(0).toUpperCase()||'?')+'</span>';
  el.innerHTML=fv+'<span class="tab-title">'+esc(t.title||'New Tab')+(t.frozen?' ❄':'')+'</span><span class="tab-close">'+I.close+'</span>';
  el.title=(t.title||'')+(t.url&&t.url!=='nexus://home'?'\n'+t.url:'');
  el.onclick=function(e){if(e.target.closest('.tab-close'))return;ipc(t.frozen?'unfreeze-tab':'switch-tab',t.i)};
  el.querySelector('.tab-close').onclick=function(e){e.stopPropagation();ipc('close-tab',t.i)};
  el.onauxclick=function(e){if(e.button===1){e.preventDefault();ipc('close-tab',t.i)}};
  w.appendChild(el)})}
function updateNavBtns(){$('#btn-back').disabled=!S.canBack;$('#btn-fwd').disabled=!S.canFwd}
function updateShield(){var n=$('#shield-n');if(n)n.textContent=S.pageBlocked>999?'999+':S.pageBlocked;
 var nb=$('#nt-stats');if(nb)nb.textContent=S.blockedRust?'🛡 '+S.blockedRust+' ad & tracker requests blocked (lifetime)':''}
function renderStar(){var u=S.cur.url||'';var b=$('#btn-star');
 b.classList.toggle('saved',S.bookmarks.some(function(x){return x.url===u}))}
function secIcon(){var u=S.cur.url||'';var el=$('#sec-ic');
 if(u.indexOf('https://')===0){el.innerHTML=I.lock;el.className='ok';el.title='HTTPS — secure connection'}
 else if(u.indexOf('http://')===0){el.innerHTML=I.info;el.className='bad';el.title='HTTP — NOT secure!'}
 else{el.innerHTML=I.globe;el.className='';el.title='Internal Nexus page'}}
function renderBm(){var bar=$('#bm-bar');bar.style.display=P.showBm?'flex':'none';bar.innerHTML='';
 S.bookmarks.slice(0,40).forEach(function(b){var el=h('span','bm-item');el.textContent=b.title||b.url;el.title=b.url;el.onclick=function(){ipc('nav',b.url)};bar.appendChild(el)})}

/* ===== new tab page ===== */
var QUICK=[['YouTube','https://youtube.com'],['GitHub','https://github.com'],['Wikipedia','https://wikipedia.org'],['Reddit','https://reddit.com'],['Facebook','https://facebook.com'],['Gmail','https://mail.google.com'],['VNExpress','https://vnexpress.net'],['Zing News','https://zingnews.vn']];
function ntRender(){var hr=new Date().getHours();
 $('#nt-greet').textContent=(hr<11?'Good morning':hr<13?'Good day':hr<18?'Good afternoon':'Good evening')+' 👋';
 var w=$('#nt-links');w.innerHTML='';
 QUICK.forEach(function(q){var hh=0;for(var i=0;i<q[0].length;i++)hh=(hh*31+q[0].charCodeAt(i))%360;
  var el=h('div','nt-link','<div class="nt-ico" style="background:hsl('+hh+',55%,45%)">'+esc(q[0].charAt(0))+'</div><span>'+esc(q[0])+'</span>');
  el.onclick=function(){ipc('nav',q[1])};w.appendChild(el)});
 updateShield()}
 $('#nt-q').addEventListener('keydown',function(e){if(e.key==='Enter'){var v=e.target.value.trim();if(v){e.target.value='';ipc('nav',v)}}});

/* ===== page render + loadbar ===== */
function setPage(d){
 var at=S.tabs[S.active];
 if(d.id&&at&&at.id&&at.id!==d.id)return;
 S.cur={url:d.url||'',title:d.title||''};
 S.pageBlocked=0;S.log=[];
 var home=String(S.cur.url).indexOf('nexus://home')===0;
 var set=String(S.cur.url).indexOf('nexus://settings')===0;
 $('#view').style.display=(!home&&!set&&d.html)?'block':'none';
 $('#newtab').style.display=home?'flex':'none';
 $('#settings').style.display=set?'flex':'none';
 if(set)buildSettings(pendingSec);pendingSec=null;
 else if(!home&&d.html){try{$('#view').srcdoc=d.html}catch(e){devlog('srcdoc err: '+e)}}
 $('#url').value=set?'nexus://settings':(home?'':S.cur.url);
 secIcon();renderTabs();updateNavBtns();renderStar();updateShield()}
var loadT=0;
function loadOn(){var b=$('#loadbar');b.classList.add('show');b.style.width='30%';clearTimeout(loadT);loadT=setTimeout(function(){b.style.width='84%'},500)}
function loadOff(){var b=$('#loadbar');b.style.width='100%';setTimeout(function(){b.classList.remove('show');setTimeout(function(){b.style.width='0'},260)},220)}

/* ===== omnibox + suggestions ===== */
function go(v){v=(v||'').trim();if(v)ipc('nav',v)}
var urlIn=$('#url');
urlIn.addEventListener('focus',function(){$('#url-wrap').classList.add('focus');urlIn.select();showSuggest()});
urlIn.addEventListener('blur',function(){$('#url-wrap').classList.remove('focus');setTimeout(hideSuggest,160)});
urlIn.addEventListener('input',showSuggest);
urlIn.addEventListener('keydown',function(e){
 if(e.key==='Enter'){e.preventDefault();var it=sugSel>=0?sugItems[sugSel]:null;hideSuggest();urlIn.blur();go(it?it.go:urlIn.value)}
 else if(e.key==='ArrowDown'||e.key==='ArrowUp'){e.preventDefault();moveSug(e.key==='ArrowDown'?1:-1)}
 else if(e.key==='Escape'){hideSuggest();urlIn.value=S.cur.url||'';urlIn.blur()}
});
var sugItems=[],sugSel=-1;
function showSuggest(){var q=urlIn.value.trim();var box=$('#suggest');sugItems=[];sugSel=-1;
 if(!q){hideSuggest();return}
 var isUrl=/^(https?:\/\/|nexus:\/\/)/i.test(q)||(!q.includes(' ')&&q.includes('.'));
 sugItems.push({t:isUrl?'Go to '+q:'Search for "'+q+'"',u:isUrl?q:'keyword',ic:isUrl?I.arrow:I.search,go:q});
 var ql=q.toLowerCase();
 S.history.filter(function(x){return String(x.url).toLowerCase().indexOf(ql)>=0||String(x.title).toLowerCase().indexOf(ql)>=0}).slice(0,5).forEach(function(x){sugItems.push({t:x.title||x.url,u:x.url,ic:I.clock,go:x.url})});
 S.bookmarks.filter(function(b){return String(b.url).toLowerCase().indexOf(ql)>=0||String(b.title).toLowerCase().indexOf(ql)>=0}).slice(0,3).forEach(function(b){sugItems.push({t:b.title||b.url,u:b.url,ic:I.star,go:b.url})});
 box.innerHTML='';
 sugItems.forEach(function(it){
  var el=h('div','sug-item','<span class="sug-ic">'+it.ic+'</span><span class="sug-t">'+esc(it.t)+'</span><span class="sug-u">'+esc(it.u)+'</span>');
  el.addEventListener('mousedown',function(e){e.preventDefault();go(it.go);urlIn.blur()});box.appendChild(el)});
 box.style.display=sugItems.length?'block':'none'}
function moveSug(d){if(!sugItems.length)return;sugSel=(sugSel+d+sugItems.length)%sugItems.length;$$('#suggest .sug-item').forEach(function(el,i){el.classList.toggle('sel',i===sugSel)})}
function hideSuggest(){$('#suggest').style.display='none'}

/* ===== popups ===== */
function closePops(){$$('.pop').forEach(function(p){p.classList.remove('show')})}
function openPop(sel,anchor){closePops();var el=$(sel);el.classList.add('show');
 var r=anchor.getBoundingClientRect();var w=el.offsetWidth;
 el.style.left=Math.max(10,Math.min(r.left,innerWidth-w-10))+'px';el.style.top=(r.bottom+7)+'px'}
document.addEventListener('click',function(e){if(!e.target.closest('.pop')&&!e.target.closest('#btn-menu,#btn-shield,#btn-dl'))closePops()});

function openSettingsSec(sec){pendingSec=sec;closePops();
 if(String(S.cur.url).indexOf('nexus://settings')===0)buildSettings(sec);
 else go('nexus://settings')}
var MENU=[
 [I.plus,'New Tab','Ctrl+T',function(){ipc('new-tab',{mode:'normal'})}],
 [I.incog,'Private Tab','Ctrl+Shift+N',function(){ipc('new-tab',{mode:'incognito'})}],
 null,
 [I.clock,'History','Ctrl+H',function(){openSettingsSec('hist')}],
 [I.book,'Bookmarks','',function(){openSettingsSec('bm')}],
 [I.dl,'Downloads','Ctrl+J',function(){openSettingsSec('dl')}],
 [I.grid,'Extensions','',function(){openSettingsSec('ext')}],
 null,
 [I.key,'Vault','',function(){openSettingsSec('vault')}],
 [I.gear,'Settings','',function(){go('nexus://settings')}],
 [I.info,'Developer console','Ctrl+Shift+I',function(){toggleDev()}]
];
function buildMenu(){var m=$('#menu-pop');m.innerHTML='';
 MENU.forEach(function(x){if(!x){m.appendChild(h('div','pop-sep'));return}
  var it=h('div','pop-item',x[0]+'<span>'+x[1]+'</span>'+(x[2]?'<span class="kbd">'+x[2]+'</span>':''));
  it.onclick=function(){closePops();x[3]()};m.appendChild(it)});
 m.appendChild(h('div','pop-note','Nexus Browser 1.0'))}

/* shield popup: count + blocked list + 3 levels */
function buildShieldPop(){var p=$('#shield-pop');p.innerHTML='';
 p.appendChild(h('div','sp-head','Protections for this site'));
 p.appendChild(h('div','sp-count','Blocked '+S.pageBlocked+' requests on this page · '+S.blockedRust+' lifetime'));
 if(S.log.length){
  p.appendChild(h('div','sp-lv','On this page'));
  var w=h('div','sl-wrap');
  S.log.slice().reverse().forEach(function(l){
   w.appendChild(h('div','sl-row','<span class="sl-u">'+esc(host(l.u))+'</span><span class="sl-t">'+esc(classify(l.u))+'</span><span class="sl-n">×'+l.n+'</span>'))});
  p.appendChild(w)}
 if(S.rlog.length){
  p.appendChild(h('div','sp-lv','Network layer (lifetime)'));
  var w2=h('div','sl-wrap');
  S.rlog.slice().reverse().forEach(function(l){
   w2.appendChild(h('div','sl-row','<span class="sl-u">'+esc(l.domain)+'</span><span class="sl-t">'+esc(l.kind)+'</span><span class="sl-n">×'+l.n+'</span>'))});
  p.appendChild(w2)}
 if(!S.log.length&&!S.rlog.length)p.appendChild(h('div','pop-note','Nothing blocked yet.'));
 p.appendChild(h('div','sp-lv','Protection level (this tab)'));
 var cur=curTabProfile();var seg=h('div','seg');seg.style.margin='4px 12px 8px';
 [['strict','Strict'],['balanced','Balanced'],['off','Off']].forEach(function(o){
  var b=h('button',null,o[1]);if(cur===o[0])b.classList.add('on');
  b.onclick=function(){applyProfile(o[0])};seg.appendChild(b)});
 p.appendChild(seg);
 p.appendChild(h('div','pop-note',PROFILE_DESC[cur]||'Custom — toggles set manually in Settings → Privacy.'))}

/* downloads */
function dlRow(d){var pct=d.total?Math.min(100,Math.round(d.recv*100/d.total)):0;
 var r=h('div','p-row'+(d.error?' err':'')+((d.done&&!d.error)?' done':''));
 r.innerHTML='<div class="p-ico">'+((d.done&&!d.error)?I.check:(d.error?I.close:I.dl))+'</div><div class="p-main"><div class="p-t">'+esc(d.name)+'</div><div class="p-u">'+(d.error?esc(d.error):(d.total?fmtB(d.recv)+' / '+fmtB(d.total)+' · '+pct+'%':fmtB(d.recv)))+'</div>'+(d.done?'':'<div class="dl-bar"><i style="width:'+pct+'%"></i></div>')+'</div>';
 return r}
function buildDlPop(){var p=$('#dl-pop');p.innerHTML='';
 p.appendChild(h('div','sp-head','Downloads'));
 var list=Object.keys(S.downloads).map(function(k){return S.downloads[k]});
 if(!list.length)p.appendChild(h('div','pop-note','Nothing downloaded yet.'));
 else list.slice(-4).reverse().forEach(function(d){p.appendChild(dlRow(d))});
 var all=h('div','pop-item',I.folder+'<span>See all in Settings</span>');
 all.onclick=function(){closePops();openSettingsSec('dl')};p.appendChild(all)}

/* ===== settings ===== */
var ACCENTS=['','#8e44ad','#0f9d58','#e37400','#d93025','#00838f'];
var ENG=[['duckduckgo','DuckDuckGo'],['google','Google'],['bing','Bing'],['brave','Brave'],['startpage','Startpage']];
var DNSP=[['https://1.1.1.1/dns-query','Cloudflare (1.1.1.1)'],['https://8.8.8.8/resolve','Google (8.8.8.8)']];
var SECS=[['look','Appearance',I.gear],['search','Search',I.search],['priv','Privacy and security',I.shield],
 ['hist','History',I.clock],['bm','Bookmarks',I.book],['keys','Shortcuts',I.grid],
 ['dl','Downloads',I.dl],['ext','Extensions',I.grid],['vault','Vault',I.key],
 ['sync','Sync',I.copy],['adv','Advanced',I.info]];
// JS-side defaults mirror the Rust Balanced defaults
var DEFB={secure_dns:false,sinkhole:false,anti_fp:false,cookie:false};
function cfgB(k){var d=DEFB[k]!==undefined?DEFB[k]:true;return S.config[k]===undefined?d:!!S.config[k]}

function renderHistSec(root){
 var sr=h('div','crow','<input class="tin" id="h-q" placeholder="Search history…">');
 var list=h('div');list.id='hist-list';
 var clear=h('div','crow','<div><div class="ct">Clear all browsing history</div><div class="cd">Bookmarks and vault are kept</div></div>');
 var cb=h('button','btn danger','Clear');cb.onclick=function(){if(confirm('Clear all browsing history?'))ipc('history-clear',null)};
 clear.appendChild(cb);
 root.appendChild(sr);root.appendChild(list);root.appendChild(clear);
 var draw=function(q){list.innerHTML='';var ql=(q||'').toLowerCase();
  var items=S.history.filter(function(x){return !ql||String(x.url).toLowerCase().indexOf(ql)>=0||String(x.title).toLowerCase().indexOf(ql)>=0});
  if(!items.length){list.appendChild(h('div','empty','History is empty.'));return}
  items.slice(0,300).forEach(function(x){
   var r=h('div','p-row','<div class="p-ic">'+I.clock+'</div><div class="p-main"><div class="p-t">'+esc(x.title||x.url)+'</div><div class="p-u">'+esc(x.url)+' · '+ago(x.time)+'</div></div><div class="p-act"><button title="Open">'+I.arrow+'</button><button title="Delete">'+I.trash+'</button></div>');
   var btns=r.querySelectorAll('button');
   btns[0].onclick=function(){ipc('nav',x.url)};
   btns[1].onclick=function(){ipc('history-remove',{url:x.url,time:x.time})};
   r.querySelector('.p-main').onclick=function(){ipc('nav',x.url)};
   list.appendChild(r)})};
 draw('');
 window._drawHist=draw;
 sr.querySelector('#h-q').addEventListener('input',function(e){draw(e.target.value)})}
function renderBmSec(root){var list=h('div');list.id='bm-list';root.appendChild(list);
 var draw=function(){list.innerHTML='';
  if(!S.bookmarks.length){list.appendChild(h('div','empty','No bookmarks yet — click the star next to the address bar.'));return}
  S.bookmarks.slice().reverse().forEach(function(b){
   var r=h('div','p-row','<div class="p-ic">'+I.star+'</div><div class="p-main"><div class="p-t">'+esc(b.title||b.url)+'</div><div class="p-u">'+esc(b.url)+'</div></div><div class="p-act"><button title="Open">'+I.arrow+'</button><button title="Delete">'+I.trash+'</button></div>');
   var btns=r.querySelectorAll('button');
   btns[0].onclick=function(){ipc('nav',b.url)};
   btns[1].onclick=function(){ipc('bookmark-remove',b.url)};
   r.querySelector('.p-main').onclick=function(){ipc('nav',b.url)};
   list.appendChild(r)})};
 draw();window._drawBm=draw}
function renderDlSec(root){
 var open=h('div','crow','<div><div class="ct">Download folder</div><div class="cd">downloads/ (next to the executable)</div></div>');
 var ob=h('button','btn','Open');ob.onclick=function(){ipc('open-dl-dir',null)};open.appendChild(ob);
 root.appendChild(open);
 var list=h('div');list.id='dl-list';root.appendChild(list);
 var draw=function(){var items=Object.keys(S.downloads).map(function(k){return S.downloads[k]});list.innerHTML='';
  if(!items.length){list.appendChild(h('div','empty','Nothing downloaded yet. Clicking file links (.zip, .pdf, .exe…) starts a download.'));return}
  items.slice().reverse().forEach(function(d){list.appendChild(dlRow(d))})};
 draw();window._drawDl=draw}
function renderExtSec(root){var list=h('div');list.id='ext-list-el';root.appendChild(list);
 window._extDraw=function(l){list.innerHTML='';
  if(!l||!l.length){list.appendChild(h('div','empty','No extensions yet.<br>Put each extension in a subfolder of <b>nexus_extensions/</b> (with manifest.json).'));return}
  l.forEach(function(x){
   var r=h('div','p-row','<div class="p-ic">'+I.grid+'</div><div class="p-main"><div class="p-t">'+esc(x.name)+' <span style="color:var(--t3)">v'+esc(x.version)+'</span></div><div class="p-u">'+esc(x.desc||x.id)+'</div></div><label class="sw"><input type="checkbox"'+(x.enabled?' checked':'')+'><span></span></label>');
   r.querySelector('input').onchange=function(e){ipc('ext-toggle',{id:x.id,enabled:e.target.checked})};
   list.appendChild(r)})};
 ipc('ext-list',null)}
function renderVaultSec(root){
 if(S.vaultLocked){
  root.innerHTML='';
  root.appendChild(h('div','p-row','<div class="p-ic">'+I.lock+'</div><div class="p-main"><div class="p-t">Vault is locked</div><div class="p-u">AES-256-GCM + Argon2id — only you can read it.</div></div>'));
  var f=h('div','p-row','<input class="tin" id="v-master" type="password" placeholder="Master password" style="margin-right:8px"><button class="btn pri" id="v-unlock">Unlock</button>');
  root.appendChild(f);
  f.querySelector('#v-unlock').onclick=function(){var v=f.querySelector('#v-master').value;if(v)ipc('vault-unlock',v)};
  f.querySelector('#v-master').addEventListener('keydown',function(e){if(e.key==='Enter')f.querySelector('#v-unlock').click()});
  return}
 root.innerHTML='';
 var tr=h('div','p-row','<div class="p-ic">'+I.key+'</div><div class="p-main"><div class="p-t">Vault is unlocked</div><div class="p-u">'+S.vaultEntries.length+' passwords</div></div>');
 var lock=h('button','btn','Lock');lock.onclick=function(){ipc('vault-lock',null)};
 tr.appendChild(lock);root.appendChild(tr);
 var gen=h('div','p-row','<div class="p-main"><div class="p-t" id="v-pass" style="font-family:Consolas,Menlo,monospace">&nbsp;</div><div class="p-u">Random 16-character password</div></div>');
 var gb=h('button','btn','Generate');var cpb=h('button','btn','Copy');
 gb.onclick=function(){var cs='ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnpqrstuvwxyz23456789!@#$%^&*';var a=rnd32(16);var pw='';for(var i=0;i<16;i++)pw+=cs[a[i]%cs.length];gen.querySelector('#v-pass').textContent=pw};
 cpb.onclick=function(){copyText(gen.querySelector('#v-pass').textContent)};
 gen.appendChild(gb);gen.appendChild(cpb);root.appendChild(gen);
 var list=h('div');root.appendChild(list);
 var draw=function(){list.innerHTML='';
  if(!S.vaultEntries.length){list.appendChild(h('div','empty','Vault is empty. When you sign in to a website, Nexus will offer to save the password here.'));return}
  S.vaultEntries.forEach(function(e){
   var r=h('div','p-row','<div class="p-ic">'+I.key+'</div><div class="p-main"><div class="p-t">'+esc(e.user)+'</div><div class="p-u">'+esc(e.domain)+'</div></div><div class="p-act"><button title="Fill in form" data-a="fill">'+I.check+'</button><button title="Copy" data-a="copy">'+I.copy+'</button><button title="Delete" data-a="del">'+I.trash+'</button></div>');
   r.querySelectorAll('.p-act button').forEach(function(b){b.onclick=function(){var a=b.getAttribute('data-a');
    if(a==='fill')ipc('vault-copy',{domain:e.domain,user:e.user,act:'fill'});
    else if(a==='copy')ipc('vault-copy',{domain:e.domain,user:e.user,act:'copy'});
    else if(a==='del'&&confirm('Delete '+e.user+' @ '+e.domain+'?'))ipc('vault-delete',{domain:e.domain,user:e.user})}});
   list.appendChild(r)})};
 draw()}

function buildSettings(sec){
 var root=$('#settings');root.innerHTML='';
 var nav=h('div','set-nav');var body=h('div','set-body');
 var back=h('div','set-back',I.back+'<span>← Back to home</span>');back.onclick=function(){go('nexus://home')};nav.appendChild(back);
 var secs={};
 SECS.forEach(function(s){var it=h('div','set-nav-item',s[2]+'<span>'+s[1]+'</span>');
  it.onclick=function(){$$('.set-nav-item',nav).forEach(function(x){x.classList.toggle('on',x===it)});
   if(secs[s[0]])secs[s[0]].scrollIntoView({behavior:'smooth',block:'start'})};
  it.dataset.sec=s[0];nav.appendChild(it)});
 function mksec(id,t,sub){var s=h('div','set-sec','<div class="set-h">'+t+'</div><div class="set-sub">'+(sub||'')+'</div>');secs[id]=s;return s}
 function card(){return h('div','card')}
 function row(t,d,ctrl){var r=h('div','crow','<div><div class="ct">'+t+'</div>'+(d?'<div class="cd">'+d+'</div>':'')+'</div>');if(ctrl)r.appendChild(ctrl);return r}
 function mkSw(ck,onch){var l=h('label','sw','<input type="checkbox"'+(ck?' checked':'')+'><span></span>');l.querySelector('input').onchange=function(e){onch(e.target.checked)};return l}
 function mkSeg(opts,val,onch){var s=h('div','seg');opts.forEach(function(o){var b=h('button',null,o[1]);if(o[0]===val)b.classList.add('on');
  b.onclick=function(){$$('button',s).forEach(function(x){x.classList.remove('on')});b.classList.add('on');onch(o[0])};s.appendChild(b)});return s}
 function mkTin(ph,val,type){var i=h('input','tin');i.placeholder=ph;i.type=type||'text';if(val!=null)i.value=val;return i}

 /* Appearance */
 var c1=card();
 c1.appendChild(row('Theme','Light, dark, or follow the system',mkSeg([['light','Light'],['dark','Dark'],['system','System']],P.theme,function(v){P.theme=v;applyTheme();saveP()})));
 var accRow=h('div','crow','<div><div class="ct">Accent color</div><div class="cd">Primary UI color</div></div>');
 var aw=h('div','swatches');ACCENTS.forEach(function(a){var s=h('button','swatch'+(P.accent===a?' on':''));s.style.background=a||'var(--acc)';
  s.onclick=function(){P.accent=a;saveP();if(a)document.documentElement.style.setProperty('--acc',a);else document.documentElement.style.removeProperty('--acc');buildSettings(sec)};aw.appendChild(s)});
 accRow.appendChild(aw);c1.appendChild(accRow);
 c1.appendChild(row('Bookmarks bar','Show the bar under the address bar',mkSw(P.showBm,function(v){P.showBm=v;saveP();renderBm()})));
 c1.appendChild(row('Compact UI','Reduce tab and toolbar heights',mkSeg([['normal','Normal'],['compact','Compact']],P.density,function(v){P.density=v;saveP();document.documentElement.dataset.density=v})));
 var sLook=mksec('look','Appearance','Customize the look of Nexus');
 sLook.appendChild(c1);body.appendChild(sLook);

 /* Search */
 var c2=card();var rd=h('div','radios');
 ENG.forEach(function(o){var l=h('label','radio','<input type="radio" name="eng"><span>'+o[1]+'</span>');
  var inp=l.querySelector('input');inp.checked=(S.config.search_engine||'duckduckgo')===o[0]);
  inp.onchange=function(){if(inp.checked)ipc('set-config',{search_engine:o[0]})};rd.appendChild(l)});
 c2.appendChild(rd);
 var hi=mkTin('nexus://home',S.config.home);
 hi.addEventListener('change',function(e){ipc('set-config',{home:e.target.value})});
 c2.appendChild(row('Home page','Opened by the home button',hi));
 var sSearch=mksec('search','Search','Default engine for keywords typed in the address bar');
 sSearch.appendChild(c2);body.appendChild(sSearch);

 /* Privacy and security */
 var c3=card();
 c3.appendChild(row('Default protection level (new tabs)','Strict blocks everything · Balanced blocks ads & trackers · Off disables blocking',
  mkSeg([['strict','Strict'],['balanced','Balanced'],['off','Off']],curGlobalProfile(),applyGlobalProfile)));
 [['ad','Block ads','Hide and neutralize ads on pages'],
  ['trk','Block trackers','Block fetch/XHR/beacon/WebSocket calls to trackers'],
  ['sinkhole','Network-level sinkhole','Block known ad/tracker domains before requests leave your machine'],
  ['anti_fp','Anti-fingerprinting','Blur canvas, WebGL and hardware info'],
  ['cookie','Block tracking cookies','Filters _ga, _fbp and similar cookies'],
  ['auto_save_passwords','Offer to save passwords','Show the save-password popup on login forms']].forEach(function(x){
   c3.appendChild(row(x[1],x[2],mkSw(cfgB(x[0]),function(v){var o={};o[x[0]]=v;ipc('set-config',o)})))});
 var sPriv=mksec('priv','Privacy and security','Defaults for new tabs — per-tab control lives in the Shield button');
 sPriv.appendChild(c3);

 /* Secure DNS card */
 var dnsC=card();
 dnsC.appendChild(row('Secure DNS (DNS-over-HTTPS)','Resolve site domains via encrypted DNS instead of your ISP',mkSw(cfgB('secure_dns'),function(v){ipc('set-config',{secure_dns:v})})));
 var de=mkTin('https://1.1.1.1/dns-query',S.config.dns_endpoint);
 de.addEventListener('change',function(e){ipc('set-config',{dns_endpoint:e.target.value})});
 dnsC.appendChild(row('Resolver endpoint','JSON DoH endpoint (dns-json)',de));
 var pr=h('div','crow','<div><div class="ct">Presets</div><div class="cd">Cloudflare · Google</div></div>');
 var pb=h('div');pb.style.display='flex';pb.style.gap='8px';
 DNSP.forEach(function(x){var b=h('button','btn',x[1]);b.onclick=function(){de.value=x[0];ipc('set-config',{dns_endpoint:x[0]})};pb.appendChild(b)});
 pr.appendChild(pb);dnsC.appendChild(pr);
 dnsC.appendChild(h('div','p-note','Covers page navigations and downloads. Bypassed when a tab proxy is enabled (SOCKS5h resolves remotely). Falls back to system DNS if the resolver fails.'));
 sPriv.appendChild(dnsC);
 body.appendChild(sPriv);

 /* History */
 var sHist=mksec('hist','History','Private tabs are never recorded here');
 var histCard=card();sHist.appendChild(histCard);renderHistSec(histCard);body.appendChild(sHist);

 /* Bookmarks */
 var sBm=mksec('bm','Bookmarks','Click the star next to the address bar to add a page');
 var bmCard=card();sBm.appendChild(bmCard);renderBmSec(bmCard);body.appendChild(sBm);

 /* Shortcuts */
 var c6=card();
 [['Ctrl + T','New tab'],['Ctrl + Shift + N','Private tab'],['Ctrl + W','Close current tab'],['Ctrl + L','Focus the address bar'],
  ['Ctrl + D','Bookmark current page'],['Ctrl + R / F5','Reload page'],['Ctrl + Tab','Switch tabs (Shift to go back)'],
  ['Ctrl + 1…9','Jump to tab N'],['Alt + ← / →','Back / forward in tab history'],
  ['Ctrl + J','Downloads'],['Ctrl + H','History'],['Ctrl + Shift + I','Developer console'],['Esc','Close open popup']].forEach(function(k){
  c6.appendChild(h('div','krow','<span class="kk">'+k[0]+'</span><span>'+k[1]+'</span>'))});
 var sKeys=mksec('keys','Shortcuts','Nexus keyboard shortcuts');
 sKeys.appendChild(c6);body.appendChild(sKeys);

 /* Downloads */
 var sDl=mksec('dl','Downloads','Files are saved in downloads/');
 var dlCard=card();sDl.appendChild(dlCard);renderDlSec(dlCard);body.appendChild(sDl);

 /* Extensions */
 var sExt=mksec('ext','Extensions','Each extension is a subfolder of nexus_extensions/ with manifest.json');
 var extCard=card();sExt.appendChild(extCard);renderExtSec(extCard);body.appendChild(sExt);

 /* Vault */
 var sV=mksec('vault','Vault','Local password store, end-to-end encrypted (AES-256-GCM + Argon2id)');
 var vCard=card();vCard.id='vault-card';sV.appendChild(vCard);renderVaultSec(vCard);body.appendChild(sV);

 /* Sync */
 var c7=card();
 [['chrome','Chrome'],['firefox','Firefox'],['edge','Edge']].forEach(function(x){
  var b=h('button','btn','Import');b.onclick=function(){ipc('sync-import',x[0])};
  c7.appendChild(row('Import from '+x[1],'Copy saved passwords into the vault (stub)',b))});
 var sSync=mksec('sync','Sync','Import data from other browsers');
 sSync.appendChild(c7);body.appendChild(sSync);

 /* Advanced */
 var c8=card();
 c8.appendChild(row('Developer console','Show internal logs and extension messages',mkSw($('#devlog').classList.contains('show'),function(v){toggleDev(v)})));
 var pi=mkTin('socks5h://host:port',S.cfg.proxy_url);
 pi.addEventListener('change',function(e){ipc('tab-cfg',{field:'proxy_url',value:e.target.value})});
 c8.appendChild(row('Proxy for current tab','SOCKS/HTTP — enable the switch below',pi));
 c8.appendChild(row('Enable proxy for this tab','Only applies to the current tab',mkSw(!!S.cfg.proxy,function(v){ipc('tab-cfg',{field:'proxy',value:v})})));
 c8.appendChild(row('Version','Nexus Browser 1.0 · Rust + tao + wry + reqwest'));
 var sAdv=mksec('adv','Advanced','Developer tools and proxy');
 sAdv.appendChild(c8);body.appendChild(sAdv);

 root.appendChild(nav);root.appendChild(body);
 if(sec){var it=nav.querySelector('.set-nav-item[data-sec="'+sec+'"]');
  if(it){it.classList.add('on');secs[sec].scrollIntoView()}}
}

/* ===== save-password popup (never in private tabs) ===== */
var ppT=0;
function hidePassPop(){clearTimeout(ppT);$('#pass-pop').classList.remove('show')}
function onPassDetected(p){if(!p||!p.password)return;
 if(S.config&&S.config.auto_save_passwords===false)return;
 var at=S.tabs[S.active];
 if(at&&at.mode==='incognito')return; // private tabs never save passwords
 pendingSave={url:p.url||S.cur.url,username:p.username||'',password:p.password};
 $('#pp-site').textContent=host(p.url||'');
 $('#pp-user').textContent=p.username||'(empty)';
 $('#pp-master-row').style.display=S.vaultLocked?'block':'none';
 $('#pp-master').value='';
 $('#pass-pop').classList.add('show');
 clearTimeout(ppT);ppT=setTimeout(hidePassPop,60000)}
 $('#pp-no').onclick=function(){pendingSave=null;pendingAfterUnlock=false;hidePassPop()};
 $('#pp-save').onclick=function(){if(!pendingSave)return;
 if(S.vaultLocked){var m=$('#pp-master').value;if(!m){toast('err','Enter the vault master password');return}
  pendingAfterUnlock=true;ipc('vault-unlock',m);hidePassPop()}
 else{ipc('vault-save',pendingSave);pendingSave=null;hidePassPop()}};

/* ===== messages from the page iframe ===== */
window.addEventListener('message',function(e){
 var m;try{m=JSON.parse(e.data)}catch(_){return}
 if(!m||!m.a)return;
 switch(m.a){
  case 'inc':S.pageBlocked++;pushLog(typeof m.p==='string'?m.p:'');updateShield();break;
  case 'nav-internal':ipc('nav',m.p);break;
  case 'new-tab-url':ipc('new-tab',{mode:'normal',url:m.p});break;
  case 'nav-post':ipc('nav-post',m.p);break;
  case 'dl-start':ipc('dl-start',m.p);break;
  case 'password-detected':onPassDetected(m.p);break;
  case 'ext-msg':devlog('[ext] '+JSON.stringify(m.p));break;
  case 'console-log':devlog(String(m.p));break;
 }});

/* ===== dynamic updates ===== */
function upDl(d){if(!d||!d.id)return;
 S.downloads[d.id]=Object.assign({},S.downloads[d.id]||{name:'…',recv:0,total:0},d);
 var active=Object.keys(S.downloads).map(function(k){return S.downloads[k]}).filter(function(x){return !x.done}).length;
 var b=$('#dl-badge');b.style.display=active?'flex':'none';b.textContent=active;
 if(window._drawDl)window._drawDl();
 if($('#dl-pop').classList.contains('show'))buildDlPop()}
function onVault(d){S.vaultLocked=!!d.locked;
 if(!d.locked&&d.entries)S.vaultEntries=d.entries;
 var vc=$('#vault-card');if(vc)renderVaultSec(vc);
 if(!d.locked&&pendingAfterUnlock&&pendingSave){ipc('vault-save',pendingSave);pendingSave=null;pendingAfterUnlock=false}}
function doFill(d){if(d.act==='copy'){copyText(d.pass);return}
 try{$('#view').contentWindow.postMessage(JSON.stringify({a:'nexus-fill',p:{user:d.user,pass:d.pass}}),'*');toast('ok','Filled '+d.user)}
 catch(e){toast('err','Could not fill — on an internal page?')}}

/* ===== toolbar wiring ===== */
 $('#btn-back').onclick=function(){ipc('back',null)};
 $('#btn-fwd').onclick=function(){ipc('fwd',null)};
 $('#btn-reload').onclick=function(){ipc('reload',null)};
 $('#btn-home').onclick=function(){ipc('home',null)};
 $('#new-tab').onclick=function(){ipc('new-tab',{mode:'normal'})};
 $('#new-private').onclick=function(){ipc('new-tab',{mode:'incognito'})};
 $('#btn-shield').onclick=function(e){buildShieldPop();openPop('#shield-pop',e.currentTarget)};
 $('#btn-dl').onclick=function(e){buildDlPop();openPop('#dl-pop',e.currentTarget)};
 $('#btn-menu').onclick=function(e){buildMenu();openPop('#menu-pop',e.currentTarget)};
function starClick(){var u=S.cur.url||'';
 if(!u||u.indexOf('nexus://')===0){toast('info','Cannot bookmark internal pages');return}
 if(S.bookmarks.some(function(b){return b.url===u})){ipc('bookmark-remove',u);toast('info','Bookmark removed')}
 else{ipc('bookmark-add',{title:S.cur.title||u,url:u});toast('ok','Bookmarked')}}
 $('#btn-star').onclick=starClick;

/* ===== shortcuts ===== */
document.addEventListener('keydown',function(e){
 var mod=e.ctrlKey||e.metaKey;
 var tag=(e.target.tagName||'').toLowerCase();
 if(!mod&&!e.altKey&&(tag==='input'||tag==='textarea')&&e.key!=='Escape')return;
 if(e.key==='Escape'){closePops();return}
 if(mod&&e.shiftKey&&(e.key==='N'||e.key==='n')){e.preventDefault();ipc('new-tab',{mode:'incognito'});return}
 if(mod&&(e.key==='t'||e.key==='T')){e.preventDefault();ipc('new-tab',{mode:'normal'})}
 else if(mod&&(e.key==='w'||e.key==='W')){e.preventDefault();ipc('close-tab',S.active)}
 else if(mod&&(e.key==='l'||e.key==='L')){e.preventDefault();urlIn.focus()}
 else if(mod&&(e.key==='d'||e.key==='D')){e.preventDefault();starClick()}
 else if((mod&&(e.key==='r'||e.key==='R'))||e.key==='F5'){e.preventDefault();ipc('reload',null)}
 else if(mod&&e.key==='Tab'){e.preventDefault();var d=e.shiftKey?-1:1;ipc('switch-tab',(S.active+d+Math.max(1,S.tabs.length))%Math.max(1,S.tabs.length))}
 else if(e.altKey&&e.key==='ArrowLeft'){e.preventDefault();ipc('back',null)}
 else if(e.altKey&&e.key==='ArrowRight'){e.preventDefault();ipc('fwd',null)}
 else if(mod&&e.shiftKey&&(e.key==='I'||e.key==='i')){e.preventDefault();toggleDev()}
 else if(mod&&(e.key==='j'||e.key==='J')){e.preventDefault();openSettingsSec('dl')}
 else if(mod&&(e.key==='h'||e.key==='H')){e.preventDefault();openSettingsSec('hist')}
 else if(mod&&!e.shiftKey&&e.key>='1'&&e.key<='9'){e.preventDefault();
  var idx=e.key==='9'?S.tabs.length-1:Math.min(parseInt(e.key,10)-1,S.tabs.length-1);
  ipc('switch-tab',idx)}
});

/* ===== single entry point from Rust ===== */
window.NX={onEvent:function(s){
 var m;try{m=JSON.parse(s)}catch(e){return devlog('bad event: '+String(s).slice(0,80))}
 var d=(m&&m.p==null)?{}:m.p;
 switch(m.ev){
  case 'state':booted=true;
   S.tabs=d.tabs||[];S.active=d.active|0;S.canBack=!!d.canBack;S.canFwd=!!d.canFwd;
   S.blockedRust=d.blocked|0;
   S.rlog=(d.blockedLog||[]).map(function(x){return{domain:x.domain,kind:x.kind,n:x.n}});
   S.bookmarks=d.bookmarks||[];S.history=d.history||[];
   S.config=d.config||{};S.cfg=d.cfg||{};
   S.vaultLocked=!!(d.vault&&d.vault.locked);
   renderTabs();renderBm();updateNavBtns();updateShield();renderStar();
   if($('#settings').style.display==='flex'){
    if(window._drawHist)window._drawHist($('#h-q')?$('#h-q').value:'');
    if(window._drawBm)window._drawBm()}
   break;
  case 'page':setPage(d);break;
  case 'load':d.on?loadOn():loadOff();break;
  case 'blocked':S.blockedRust=d.total|0;pushRlog(d.domain,d.kind);updateShield();
   if($('#shield-pop').classList.contains('show'))buildShieldPop();break;
  case 'dl':upDl(d);break;
  case 'vault':onVault(d);break;
  case 'vault-fill':doFill(d);break;
  case 'toast':toast(d.kind||'info',d.text||'');break;
  case 'ext-list':if(window._extDraw)window._extDraw(d.list||[]);break;
 }}};
ntRender();renderTabs();renderBm();
devlog('Nexus UI ready.');
})();
</script>
</body></html>"###.into()
}

// ======================
// BRIDGE: Rust ⇄ UI
// ======================
fn ev(px: &tao::event_loop::EventLoopProxy<Ev>, name: &str, p: JsonValue) {
    let _ = px.send_event(Ev::Js(format!("if(window.NX)NX.onEvent({})", json!({"ev": name, "p": p}))));
}

fn toast(px: &tao::event_loop::EventLoopProxy<Ev>, kind: &str, text: &str) {
    ev(px, "toast", json!({"kind": kind, "text": text}));
}

fn host_of(u: &str) -> String {
    Url::parse(u).ok().and_then(|x| x.host_str().map(|s| s.to_string())).unwrap_or_else(|| u.chars().take(40).collect())
}

fn now_secs() -> u64 {
    std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map(|d| d.as_secs()).unwrap_or(0)
}

// privacy: private tabs never land in session.json
fn session_urls(g: &state::State) -> Vec<String> {
    g.tabs.iter()
        .filter(|t| matches!(t.mode, state::TabMode::Normal) && t.url != "nexus://home")
        .map(|t| t.url.clone()).collect()
}

// ✅ FIX compile: bind the guard, deref explicitly with &*g —
// &st.read().await in one expression doesn't coerce to &State here.
async fn persist_session(st: &Arc<RwLock<state::State>>) {
    let g = st.read().await;
    let urls = session_urls(&*g);
    drop(g);
    state::save_session(&urls).await;
}

fn vault_list(entries: &[state::VaultEntry]) -> Vec<JsonValue> {
    entries.iter().map(|e| json!({"domain": e.domain, "user": e.user})).collect()
}

async fn send_state(st: &Arc<RwLock<state::State>>, px: &tao::event_loop::EventLoopProxy<Ev>) {
    let g = st.read().await;
    let tabs: Vec<JsonValue> = g.tabs.iter().enumerate().map(|(i, t)| json!({
        "i": i, "id": t.id.to_string(),
        "mode": match t.mode { state::TabMode::Normal => "normal", state::TabMode::Incognito => "incognito" },
        "title": t.name, "url": t.url, "active": i == g.active_tab, "frozen": t.frozen
    })).collect();
    let at = g.active_tab();
    let history: Vec<JsonValue> = g.history.iter().rev().take(400).map(|x| json!({"url": x.url, "title": x.title, "time": x.time})).collect();
    let blog: Vec<JsonValue> = g.blocked_log.iter().map(|b| json!({"domain": b.domain, "kind": b.kind, "n": b.n})).collect();
    let locked = MASTER.try_lock().map(|m| m.is_none()).unwrap_or(true);
    let p = json!({
        "tabs": tabs, "active": g.active_tab,
        "canBack": at.hist_pos > 0, "canFwd": at.hist_pos + 1 < at.hist.len(),
        "blocked": g.blocked, "blockedLog": blog,
        "bookmarks": g.bookmarks, "history": history,
        "config": serde_json::to_value(&g.global_cfg).unwrap_or(json!({})),
        "cfg": {"ad": at.cfg.ad, "trk": at.cfg.trk, "cookie": at.cfg.cookie, "anti_fp": at.cfg.anti_fp,
                "sinkhole": at.cfg.sinkhole, "proxy": at.cfg.proxy, "proxy_url": at.cfg.proxy_url},
        "vault": {"locked": locked, "count": g.vault.len()},
    });
    drop(g);
    ev(px, "state", p);
}

// Pick the client for a URL: base client, or a DoH-pinned client (Secure DNS).
// Pinned clients are cached per tab+host and share the tab's cookie jar.
async fn client_for(st: &Arc<RwLock<state::State>>, tab_idx: usize, url: &str) -> Option<reqwest::Client> {
    let (cfg, jar, base, secure_dns, endpoint) = {
        let mut g = st.write().await;
        let (sd, ep) = (g.global_cfg.secure_dns, g.global_cfg.dns_endpoint.clone());
        let t = g.tabs.get_mut(tab_idx)?;
        t.update_client();
        (t.cfg.clone(), t.jar.clone(), t.client.clone(), sd, ep)
    };
    if secure_dns && !cfg.proxy { // socks5h resolves via the proxy → DoH would be bypassed anyway
        if let Ok(parsed) = Url::parse(url) {
            if let Some(host) = parsed.host_str() {
                // never resolve the DoH endpoint through itself
                let ep_host = Url::parse(&endpoint).ok().and_then(|u| u.host_str().map(|s| s.to_string()));
                if ep_host.as_deref() != Some(host) {
                    { // cached pinned client?
                        let g = st.read().await;
                        if let Some(t) = g.tabs.get(tab_idx) {
                            if let Some(c) = t.pinned.get(host) { return Some(c.clone()); }
                        }
                    }
                    if let Some(ip) = doh::resolve_ip(&endpoint, host).await {
                        let port = parsed.port_or_known_default().unwrap_or(443);
                        let addr = std::net::SocketAddr::new(ip, port);
                        let c = net::build_client(&cfg, jar, Some((host, addr)));
                        let mut g = st.write().await;
                        if let Some(t) = g.tabs.get_mut(tab_idx) {
                            t.pinned.insert(host.to_string(), c.clone());
                            while t.pinned.len() > 32 {
                                let k = t.pinned.keys().next().cloned();
                                match k { Some(k) => { t.pinned.remove(&k); }, None => break }
                            }
                        }
                        return Some(c);
                    }
                }
            }
        }
    }
    Some(base.unwrap_or_else(reqwest::Client::new))
}

async fn handle_ipc(msg: String, st: Arc<RwLock<state::State>>, px: tao::event_loop::EventLoopProxy<Ev>) {
    let p: JsonValue = match serde_json::from_str(&msg) { Ok(v) => v, Err(_) => return };
    let a = p["a"].as_str().unwrap_or("").to_string();
    let d = p["p"].clone();
    match a.as_str() {
        "get-state" => send_state(&st, &px).await,

        "nav" | "nav-internal" => if let Some(u) = d.as_str() {
            let engine = st.read().await.global_cfg.search_engine.clone();
            let url = search::resolve_engine(u, &engine);
            let idx = st.read().await.active_tab;
            load_url(url, idx, st.clone(), &px, true).await;
        },

        "nav-post" => {
            let url = d["url"].as_str().unwrap_or("").to_string();
            let body = d["body"].clone();
            let idx = st.read().await.active_tab;
            load_url_method(url, idx, "POST", Some(body), st.clone(), &px, true).await;
        },

        "back" => {
            let (idx, u) = { let mut g = st.write().await; let idx = g.active_tab; (idx, g.active_tab_mut().go_back()) };
            if let Some(u) = u { load_url(u, idx, st.clone(), &px, false).await; }
        },
        "fwd" => {
            let (idx, u) = { let mut g = st.write().await; let idx = g.active_tab; (idx, g.active_tab_mut().go_fwd()) };
            if let Some(u) = u { load_url(u, idx, st.clone(), &px, false).await; }
        },
        // reload falls back to the tab URL when history is empty
        "reload" => {
            let (idx, u) = {
                let g = st.read().await;
                let idx = g.active_tab;
                let t = g.active_tab();
                (idx, t.current().or_else(|| Some(t.url.clone())))
            };
            if let Some(u) = u { load_url(u, idx, st.clone(), &px, false).await; }
        },
        "home" => {
            let hp = st.read().await.global_cfg.home.clone();
            let idx = st.read().await.active_tab;
            load_url(hp, idx, st.clone(), &px, true).await;
        },

        // ✅ FIX #15 (kept): load directly, no racing NewTab event
        "new-tab" | "new-tab-url" => {
            let mode = match d["mode"].as_str().unwrap_or("normal") {
                "incognito" => state::TabMode::Incognito,
                _ => state::TabMode::Normal,
            };
            let url = d["url"].as_str().map(|s| s.to_string());
            let idx = { let mut g = st.write().await; g.new_tab(mode) };
            send_state(&st, &px).await;
            load_url(url.unwrap_or_else(|| "nexus://home".into()), idx, st.clone(), &px, false).await;
        },

        "close-tab" => if let Some(i) = d.as_u64() {
            { let mut g = st.write().await; if !g.close_tab(i as usize) { return; } }
            persist_session(&st).await;
            render_tab(st.clone(), &px).await;
            send_state(&st, &px).await;
        },

        "switch-tab" | "unfreeze-tab" => if let Some(i) = d.as_u64() {
            let idx = i as usize;
            { let mut g = st.write().await;
              g.switch_tab(idx);
              if let Some(t) = g.tabs.get_mut(idx) { t.frozen = false; t.last_active = Instant::now(); } }
            render_tab(st.clone(), &px).await;
            send_state(&st, &px).await;
        },

        "tab-cfg" => {
            let field = d["field"].as_str().unwrap_or("").to_string();
            let v = d["value"].clone();
            { let mut g = st.write().await; let t = g.active_tab_mut();
              match field.as_str() {
                "ad" => t.cfg.ad = v.as_bool().unwrap_or(true),
                "trk" => t.cfg.trk = v.as_bool().unwrap_or(true),
                "cookie" => t.cfg.cookie = v.as_bool().unwrap_or(true),
                "anti_fp" => t.cfg.anti_fp = v.as_bool().unwrap_or(true),
                "sinkhole" => t.cfg.sinkhole = v.as_bool().unwrap_or(true),
                "proxy" => t.cfg.proxy = v.as_bool().unwrap_or(false),
                "proxy_url" => if let Some(u) = v.as_str() { t.cfg.proxy_url = u.to_string(); },
                _ => {}
              } }
            { let mut g = st.write().await; g.active_tab_mut().update_client(); }
            send_state(&st, &px).await;
        },

        "set-config" => if let Some(obj) = d.as_object() {
            let (cfg, dns_changed) = {
                let mut g = st.write().await;
                let c = &mut g.global_cfg;
                let mut dc = false;
                for (k, v) in obj {
                    match k.as_str() {
                        "ad" => c.ad = v.as_bool().unwrap_or(c.ad),
                        "trk" => c.trk = v.as_bool().unwrap_or(c.trk),
                        "sinkhole" => c.sinkhole = v.as_bool().unwrap_or(c.sinkhole),
                        "anti_fp" => c.anti_fp = v.as_bool().unwrap_or(c.anti_fp),
                        "cookie" => c.cookie = v.as_bool().unwrap_or(c.cookie),
                        "auto_save_passwords" => c.auto_save_passwords = v.as_bool().unwrap_or(c.auto_save_passwords),
                        "show_password_suggestions" => c.show_password_suggestions = v.as_bool().unwrap_or(c.show_password_suggestions),
                        "search_engine" => if let Some(s) = v.as_str() { c.search_engine = s.to_string(); },
                        "home" => if let Some(s) = v.as_str() { c.home = s.to_string(); },
                        "secure_dns" => { c.secure_dns = v.as_bool().unwrap_or(c.secure_dns); dc = true; }
                        "dns_endpoint" => { if let Some(s) = v.as_str() { c.dns_endpoint = s.to_string(); } dc = true; }
                        _ => {}
                    }
                }
                (g.global_cfg.clone(), dc)
            };
            if dns_changed {
                doh::clear_cache();
                let mut g = st.write().await;
                for t in g.tabs.iter_mut() { t.pinned.clear(); }
            }
            { let c = cfg.clone(); tokio::spawn(async move { state::save_config(&c).await; }); }
            send_state(&st, &px).await;
        },

        "bookmark-add" => {
            let title = d["title"].as_str().unwrap_or("").to_string();
            let url = d["url"].as_str().unwrap_or("").to_string();
            if !url.is_empty() {
                { let mut g = st.write().await;
                  g.bookmarks.retain(|b| b.url != url);
                  g.bookmarks.push(state::Bookmark { title: if title.is_empty() { host_of(&url) } else { title }, url }); }
                let bms = st.read().await.bookmarks.clone();
                state::save_bookmarks(&bms).await;
                send_state(&st, &px).await;
            }
        },
        "bookmark-remove" => if let Some(u) = d.as_str() {
            { let mut g = st.write().await; g.bookmarks.retain(|b| b.url != u); }
            let bms = st.read().await.bookmarks.clone();
            state::save_bookmarks(&bms).await;
            send_state(&st, &px).await;
        },

        "history-clear" => {
            { let mut g = st.write().await; g.history.clear(); }
            state::save_history(&[]).await;
            send_state(&st, &px).await;
            toast(&px, "ok", "Browsing history cleared");
        },
        "history-remove" => {
            let url = d["url"].as_str().unwrap_or("").to_string();
            let time = d["time"].as_u64().unwrap_or(0);
            { let mut g = st.write().await; g.history.retain(|x| !(x.url == url && x.time == time)); }
            let hist = st.read().await.history.clone();
            state::save_history(&hist).await;
            send_state(&st, &px).await;
        },

        // ----- vault -----
        "vault-unlock" => if let Some(m) = d.as_str() {
            if m.is_empty() { return; }
            let master = zeroize::Zeroizing::new(m.to_string());
            let entries = vault::load();
            if let Some(first) = entries.first() {
                if vault::decrypt(&first.pass, &first.nonce, &first.salt, &master).is_none() {
                    toast(&px, "err", "Wrong master password");
                    return;
                }
            }
            *MASTER.lock().await = Some(master);
            ev(&px, "vault", json!({"locked": false, "entries": vault_list(&entries)}));
            toast(&px, "ok", "Vault unlocked");
        },
        "vault-lock" => {
            *MASTER.lock().await = None;
            ev(&px, "vault", json!({"locked": true, "entries": []}));
            toast(&px, "info", "Vault locked");
        },
        "vault-save" => {
            let url = d["url"].as_str().unwrap_or("").to_string();
            let user = d["username"].as_str().unwrap_or("").to_string();
            let pass = d["password"].as_str().unwrap_or("").to_string();
            if pass.is_empty() { return; }
            let master = match MASTER.lock().await.clone() {
                Some(m) => m,
                None => { toast(&px, "err", "Vault is locked — unlock before saving"); return; }
            };
            let domain = host_of(&url);
            let mut entries = vault::load();
            entries.retain(|e| !(e.domain == domain && e.user == user));
            match vault::encrypt(&pass, &master) {
                Some((enc, nonce, salt)) => {
                    let now = now_secs();
                    entries.push(state::VaultEntry { domain: domain.clone(), user: user.clone(), pass: enc, nonce, salt, created: now, last_used: now });
                    let ok = vault::save(&entries).await;
                    { let mut g = st.write().await; g.vault = entries.clone(); }
                    ev(&px, "vault", json!({"locked": false, "entries": vault_list(&entries)}));
                    toast(&px, if ok { "ok" } else { "err" }, if ok { "Saved to vault" } else { "Vault write failed" });
                }
                None => toast(&px, "err", "Encryption failed"),
            }
        },
        "vault-copy" => {
            let domain = d["domain"].as_str().unwrap_or("").to_string();
            let user = d["user"].as_str().unwrap_or("").to_string();
            let act = d["act"].as_str().unwrap_or("fill").to_string();
            let master = match MASTER.lock().await.clone() {
                Some(m) => m,
                None => { toast(&px, "err", "Vault is locked"); return; }
            };
            let entries = vault::load();
            if let Some(e) = entries.iter().find(|e| e.domain == domain && e.user == user) {
                if let Some(pass) = vault::decrypt(&e.pass, &e.nonce, &e.salt, &master) {
                    ev(&px, "vault-fill", json!({"user": user, "pass": pass, "act": act}));
                    return;
                }
            }
            toast(&px, "err", "Not found or decryption failed");
        },
        "vault-delete" => {
            let domain = d["domain"].as_str().unwrap_or("").to_string();
            let user = d["user"].as_str().unwrap_or("").to_string();
            let mut entries = vault::load();
            entries.retain(|e| !(e.domain == domain && e.user == user));
            if vault::save(&entries).await {
                { let mut g = st.write().await; g.vault = entries.clone(); }
                ev(&px, "vault", json!({"locked": false, "entries": vault_list(&entries)}));
            }
        },

        // ----- extensions -----
        "ext-list" => {
            let exts = extensions::load_all_extensions().await;
            let list: Vec<JsonValue> = exts.iter().map(|e| json!({
                "id": e.id, "name": e.manifest.name, "version": e.manifest.version,
                "desc": e.manifest.description, "enabled": e.enabled })).collect();
            ev(&px, "ext-list", json!({"list": list}));
        },
        "ext-toggle" => if let (Some(id), Some(enabled)) = (d["id"].as_str(), d["enabled"].as_bool()) {
            if id.is_empty() || id.contains('/') || id.contains('\\') || id.contains("..") { return; }
            let dir = std::path::Path::new("nexus_extensions").join(id);
            if dir.exists() {
                if enabled { let _ = std::fs::remove_file(dir.join("DISABLED")); }
                else { let _ = std::fs::write(dir.join("DISABLED"), b""); }
                let exts = extensions::load_all_extensions().await;
                let list: Vec<JsonValue> = exts.iter().map(|e| json!({
                    "id": e.id, "name": e.manifest.name, "version": e.manifest.version,
                    "desc": e.manifest.description, "enabled": e.enabled })).collect();
                ev(&px, "ext-list", json!({"list": list}));
            }
        },

        "sync-import" => {
            let browser = d.as_str().unwrap_or("").to_string();
            let n = { let mut g = st.write().await; g.sync.import_from_browser(&browser) };
            if n > 0 { toast(&px, "ok", &format!("Imported {} items from {}", n, browser)); }
            else { toast(&px, "info", "No items found (import is a stub)"); }
        },

        // ----- downloads -----
        "dl-start" => if let Some(u) = d.as_str().map(|s| s.to_string()) {
            let idx = st.read().await.active_tab;
            let client = match client_for(&st, idx, &u).await { Some(c) => c, None => reqwest::Client::new() };
            let px2 = px.clone();
            tokio::spawn(async move { dl::turbo(u, client, px2).await; });
        },
        "open-dl-dir" => {
            let _ = std::fs::create_dir_all("downloads");
            #[cfg(windows)]
            { let _ = std::process::Command::new("explorer").arg("downloads").spawn(); }
            #[cfg(not(windows))]
            { let _ = std::process::Command::new("xdg-open").arg("downloads").spawn(); }
        },

        _ => {}
    }
}

// ======================
// LOAD URL
// ======================
async fn load_url(url: String, tab_idx: usize, st: Arc<RwLock<state::State>>, px: &tao::event_loop::EventLoopProxy<Ev>, record: bool) {
    load_url_method(url, tab_idx, "GET", None, st, px, record).await;
}

async fn load_url_method(url: String, tab_idx: usize, method: &str, body: Option<JsonValue>, st: Arc<RwLock<state::State>>, px: &tao::event_loop::EventLoopProxy<Ev>, record: bool) {
    // ✅ kept: unwrap DDG redirect /l/?uddg=
    let url = {
        if let Ok(parsed) = url::Url::parse(&url) {
            let is_ddg = matches!(parsed.host_str(), Some("duckduckgo.com") | Some("www.duckduckgo.com")) && parsed.path() == "/l/";
            if is_ddg { parsed.query_pairs().find(|(k, _)| k == "uddg").map(|(_, v)| v.into_owned()).unwrap_or(url) }
            else { url }
        } else { url }
    };

    let (cfg, my_gen) = {
        let mut g = st.write().await;
        match g.tabs.get_mut(tab_idx) {
            Some(t) => { t.load_gen += 1; (t.cfg.clone(), t.load_gen) }
            // never leave the loadbar spinning
            None => { ev(px, "load", json!({"on": false})); return; }
        }
    };

    ev(px, "load", json!({"on": true}));

    // internal pages
    if !url.starts_with("http") {
        let title = if url.starts_with("nexus://settings") { "Settings" } else { "New Tab" };
        { let mut g = st.write().await;
          if let Some(t) = g.tabs.get_mut(tab_idx) {
              t.url = url.clone();
              if record { t.push_hist(url.clone()); }
              t.name = title.into();
              t.last_html = None;
          } }
        let id = { let g = st.read().await; g.tabs.get(tab_idx).map(|t| t.id.to_string()).unwrap_or_default() };
        ev(px, "page", json!({"html": null, "url": url, "title": title, "id": id}));
        ev(px, "load", json!({"on": false}));
        send_state(&st, px).await;
        persist_session(&st).await;
        return;
    }

    // ✅ kept: https upgrade + strip utm/fbclid/gclid/msclkid
    let secure_url = if url.starts_with("http://") && !url.contains("localhost") && !url.contains("127.0.0.1") {
        url.replace("http://", "https://")
    } else { url.clone() };
    let clean_url = if let Ok(mut p) = Url::parse(&secure_url) {
        let keep: Vec<(String, String)> = p.query_pairs()
            .filter(|(k, _)| !k.starts_with("utm_") && k != "fbclid" && k != "gclid" && k != "msclkid")
            .map(|(k, v)| (k.into_owned(), v.into_owned())).collect();
        p.query_pairs_mut().clear().extend_pairs(keep.iter().map(|(k, v)| (k.as_str(), v.as_str())));
        p.to_string()
    } else { secure_url.clone() };

    // network-layer block (sinkhole) — with kind for the Shield popup
    if cfg.sinkhole {
        if let Some(kind) = sinkhole::check(&clean_url) {
            let host = host_of(&clean_url);
            let total = { let mut g = st.write().await; g.push_block(&host, kind); g.blocked };
            ev(px, "blocked", json!({"domain": host, "kind": kind, "total": total}));
            ev(px, "load", json!({"on": false}));
            let html = format!(r#"<html><head><meta charset="UTF-8"></head><body style="font-family:sans-serif;display:flex;align-items:center;justify-content:center;height:100vh;background:#fafafa;color:#5f6368;text-align:center"><div><div style="font-size:44px">🛡</div><h2 style="margin:12px 0">Blocked at the network layer</h2><p>{} is a known ad / tracking domain.<br>Nexus stopped this request before it left your machine.</p></div></body></html>"#, host);
            commit_render(&html, &clean_url, &format!("Blocked · {}", host), tab_idx, my_gen, &st, px).await;
            return;
        }
    }

    // client (with Secure DNS pinning if enabled)
    let client = match client_for(&st, tab_idx, &clean_url).await {
        Some(c) => c,
        // never leave the loadbar spinning
        None => { ev(px, "load", json!({"on": false})); return; }
    };

    let req: RequestBuilder = if method == "POST" {
        let mut form = HashMap::new();
        if let Some(b) = &body { if let Some(obj) = b.as_object() {
            for (k, v) in obj {
                let vs = if let Some(s) = v.as_str() { s.to_string() } else { v.to_string() };
                form.insert(k.clone(), vs);
            } } }
        client.post(&clean_url).form(&form)
    } else { client.get(&clean_url) };

    let t_start = Instant::now();
    let response = req
        .header("Accept", "text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,*/*;q=0.8")
        .header("Accept-Language", "en-US,en;q=0.9,vi;q=0.8")
        .header("Accept-Encoding", "identity")
        .header("DNT", "1")
        .timeout(Duration::from_secs(45))
        .send().await;
    let elapsed = t_start.elapsed().as_millis();
    let err_detail = response.as_ref().err().map(|e| e.to_string()).unwrap_or_default();

    if let Ok(r) = response {
        let status = r.status();
        let content_type = r.headers().get(reqwest::header::CONTENT_TYPE)
            .and_then(|v| v.to_str().ok()).unwrap_or("text/html").to_lowercase();

        if content_type.contains("text/html") || content_type.contains("text/plain") || content_type.contains("xml") {
            match r.text().await {
                Ok(html_raw) => {
                    // strip the page's own <base> + CSP/refresh meta tags
                    let cleaned = RE_CSP.replace_all(&RE_BASE.replace_all(&html_raw, ""), "").into_owned();
                    let safe_base = clean_url.replace('&', "&amp;").replace('"', "&quot;").replace('<', "&lt;");
                    let shield = injection::get_security_payload(&cfg);
                    let inj = format!(r#"<base href="{}">{}"#, safe_base, shield);

                    let lower = cleaned.to_ascii_lowercase();
                    let mut html_out = if let Some(start) = lower.find("<head>") {
                        format!("{}{}{}", &cleaned[..start + 6], inj, &cleaned[start + 6..])
                    } else if let Some(start) = lower.find("<head ") {
                        let end = cleaned[start..].find('>').map(|e| start + e + 1).unwrap_or(start + 6);
                        format!("{}{}{}", &cleaned[..end], inj, &cleaned[end..])
                    } else { format!("{}{}", inj, cleaned) };

                    let exts = extensions::load_all_extensions().await;
                    let (ext_js, ext_css) = extensions::get_injections_for_url(&clean_url, &exts).await;
                    if ext_js.is_some() || ext_css.is_some() {
                        let ext_api = r#"<script>if(typeof chrome==='undefined'){window.chrome={runtime:{sendMessage:function(m,c){window.top.postMessage(JSON.stringify({a:'ext-msg',p:m}),'*');}}}}</script>"#;
                        let css_tag = ext_css.map(|c| format!("<style>{}</style>", c)).unwrap_or_default();
                        let js_tag = ext_js.map(|j| format!("<script>{}</script>", j)).unwrap_or_default();
                        let ext_inj = format!("{}{}{}", css_tag, ext_api, js_tag);
                        let lo = html_out.to_ascii_lowercase();
                        if let Some(be) = lo.rfind("</body>") { html_out.insert_str(be, &ext_inj); }
                        else { html_out.push_str(&ext_inj); }
                    }

                    let title = RE_TITLE.captures(&html_out)
                        .and_then(|c| c.get(1)).map(|m| m.as_str().trim().to_string())
                        .filter(|s| !s.is_empty())
                        .unwrap_or_else(|| host_of(&clean_url));
                    commit_render(&html_out, &clean_url, &title, tab_idx, my_gen, &st, px).await;
                }
                Err(_) => {
                    let html = format!(r#"<html><head><meta charset="UTF-8"></head><body style="font-family:sans-serif;padding:60px;text-align:center;color:#5f6368"><h2>Couldn't display this page</h2><p>The site sent a response Nexus couldn't decode (HTTP {}). It may need a browser feature Nexus doesn't support yet.</p></body></html>"#, status.as_u16());
                    commit_render(&html, &clean_url, &host_of(&clean_url), tab_idx, my_gen, &st, px).await;
                }
            }
        } else if content_type.contains("image/") {
            let safe_img = clean_url.replace('&', "&amp;").replace('"', "&quot;").replace('<', "&lt;");
            let html = format!(r#"<html><head><meta charset="UTF-8"></head><body style="margin:0;background:#0e0e0e;display:flex;justify-content:center;align-items:center;height:100vh"><img src="{}" style="max-width:100%;max-height:100%"></body></html>"#, safe_img);
            commit_render(&html, &clean_url, &host_of(&clean_url), tab_idx, my_gen, &st, px).await;
        } else {
            // not a page → download (16 threads + progress)
            ev(px, "load", json!({"on": false}));
            toast(px, "info", "Download started…");
            let px2 = px.clone();
            let u = clean_url.clone();
            tokio::spawn(async move { dl::turbo(u, client, px2).await; });
            return;
        }

        if record {
            let mut g = st.write().await;
            let is_incog = g.tabs.get(tab_idx).map(|t| matches!(t.mode, state::TabMode::Incognito)).unwrap_or(false);
            if let Some(t) = g.tabs.get_mut(tab_idx) {
                t.push_hist(clean_url.clone());
                t.url = clean_url.clone();
            }
            let title = g.tabs.get(tab_idx).map(|t| t.name.clone()).unwrap_or_default();
            if !is_incog {
                g.history.push(state::HistoryEntry { url: clean_url.clone(), title, time: now_secs() });
                if g.history.len() > 2000 { let n = g.history.len() - 2000; g.history.drain(0..n); }
            }
            // ✅ FIX #10/#23 (kept): serialize before moving into spawn
            let hist = g.history.clone();
            let urls = session_urls(&g);
            drop(g);
            tokio::spawn(async move {
                state::save_history(&hist).await;
                state::save_session(&urls).await;
            });
            send_state(&st, px).await;
        }
    } else {
        let html = format!(
            r#"<html><head><meta charset="UTF-8"></head><body style="font-family:sans-serif;padding:60px;text-align:center;color:#5f6368"><h2>Couldn't reach this page</h2><p>Nexus couldn't load <b>{}</b> (waited {}ms).</p><p style="color:#80868b;font-size:13px;max-width:520px;margin:12px auto 0">{}</p><p style="color:#80868b;font-size:13px">The site may be down, your network may block it, or (if a proxy is on) the proxy isn't running.</p></body></html>"#,
            clean_url.replace('&', "&amp;").replace('<', "&lt;"), elapsed, err_detail.replace('&', "&amp;").replace('<', "&lt;"));
        commit_render(&html, &clean_url, &host_of(&clean_url), tab_idx, my_gen, &st, px).await;
    }
}

async fn commit_render(html: &str, url: &str, title: &str, tab_idx: usize, my_gen: u64, st: &Arc<RwLock<state::State>>, px: &tao::event_loop::EventLoopProxy<Ev>) {
    let id = {
        let mut g = st.write().await;
        match g.tabs.get_mut(tab_idx) {
            Some(t) => {
                if t.load_gen != my_gen { return; } // a newer nav already won
                t.last_html = Some(html.to_string());
                t.url = url.to_string();
                t.name = title.to_string();
                t.id.to_string()
            }
            None => return,
        }
    };
    ev(px, "page", json!({"html": html, "url": url, "title": title, "id": id}));
    ev(px, "load", json!({"on": false}));
}

async fn render_tab(st: Arc<RwLock<state::State>>, px: &tao::event_loop::EventLoopProxy<Ev>) {
    let (html, url, title, id) = {
        let g = st.read().await;
        let t = g.active_tab();
        (t.last_html.clone(), t.url.clone(), t.name.clone(), t.id.to_string())
    };
    if url.starts_with("http") && html.is_none() {
        let idx = st.read().await.active_tab;
        load_url(url, idx, st, px, false).await;
        return;
    }
    let html_opt = if url.starts_with("http") { html } else { None };
    ev(px, "page", json!({"html": html_opt, "url": url, "title": title, "id": id}));
    ev(px, "load", json!({"on": false}));
}

// ======================
// MAIN
// ======================
fn main() {
    std::env::set_var("WEBKIT_DISABLE_COMPOSITING_MODE", "1");

    let el = EventLoopBuilder::<Ev>::with_user_event().build();
    let w = WindowBuilder::new()
        .with_title("Nexus Browser")
        .with_inner_size(LogicalSize::new(1200.0, 800.0))
        .build(&el).unwrap();

    let mut initial = state::State::new();
    initial.global_cfg = state::load_config();
    state::apply_global(&initial.global_cfg.clone(), &mut initial.tabs[0]);
    initial.vault = vault::load();

    let saved = state::load_session();
    if !saved.is_empty() {
        initial.tabs.clear();
        let gc = initial.global_cfg.clone();
        for u in saved {
            let mut tab = state::TabState::new(state::TabMode::Normal);
            tab.url = u.clone();
            tab.name = host_of(&u);
            tab.hist.push(u);
            state::apply_global(&gc, &mut tab);
            initial.tabs.push(tab);
        }
        initial.active_tab = 0;
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

    // freeze background tabs after 5 min (drops the client, keeps cached html)
    let freeze_st = st.clone();
    let freeze_px = px.clone();
    rt.spawn(async move {
        let mut interval = tokio::time::interval(Duration::from_secs(60));
        loop {
            interval.tick().await;
            let (changed, urls) = {
                let mut g = freeze_st.write().await;
                let active = g.active_tab;
                let mut changed = false;
                for (i, tab) in g.tabs.iter_mut().enumerate() {
                    if i != active && !tab.frozen && tab.last_active.elapsed() > Duration::from_secs(300) {
                        tab.frozen = true;
                        tab.client = None;
                        tab.pinned.clear();
                        changed = true;
                    }
                }
                (changed, session_urls(&g))
            };
            if changed {
                send_state(&freeze_st, &freeze_px).await;
                tokio::spawn(async move { state::save_session(&urls).await; });
            }
        }
    });

    let wv = WebViewBuilder::new()
        .with_devtools(false)
        .with_user_agent("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36")
        .with_html(html())
        .with_back_forward_navigation_gestures(false)
        .with_hotkeys_zoom(false)
        .with_ipc_handler(move |request: wry::http::Request<String>| {
            let msg = request.into_body();
            let (ist, ipx, handle) = (ist.clone(), ipx.clone(), handle.clone());
            handle.spawn(async move {
                handle_ipc(msg, ist, ipx).await;
            });
        })
        .build(&w)
        .unwrap();

    el.run(move |ev, _, cf| {
        *cf = ControlFlow::Wait;
        match ev {
            Event::NewEvents(StartCause::Init) => {
                handle_for_loop.spawn({
                    let (st, px) = (st.clone(), px.clone());
                    async move {
                        send_state(&st, &px).await;
                        let first = { let g = st.read().await; g.tabs[0].url.clone() };
                        load_url(first, 0, st, &px, false).await;
                    }
                });
            }
            Event::UserEvent(Ev::Js(j)) => { let _ = wv.evaluate_script(&j); }
            Event::WindowEvent { event: WindowEvent::CloseRequested, .. } => *cf = ControlFlow::Exit,
            _ => {}
        }
    });
}
