# NEXUS

**A privacy-first desktop browser, built from scratch in Rust.**

[![Built with Rust](https://img.shields.io/badge/built_with-Rust-CE422B?logo=rust&logoColor=white)](https://www.rust-lang.org/)
[![License: MPL-2.0](https://img.shields.io/badge/license-MPL--2.0-blue)](LICENSE)
[![Platforms](https://img.shields.io/badge/platforms-Windows%20%7C%20macOS%20%7C%20Linux-informational)](#system-requirements)

---

## Contents

- [Introduction](#introduction)
- [Features](#features)
- [How It Compares](#how-it-compares)
- [Installation](#installation)
- [System Requirements](#system-requirements)
- [Data & Storage](#data--storage)
- [Keyboard Shortcuts](#keyboard-shortcuts)
- [Known Limitations](#known-limitations)
- [Development Notes](#development-notes)
- [Contributing](#contributing)
- [License](#license)

## Introduction

NEXUS is a desktop browser written in Rust on top of `wry` and `tao` — not a Chromium fork. Every request a page makes goes through a Rust-controlled pipeline first, which is what makes its blocking, cookie handling and DNS possible at all.

The goal is simple: a browser that doesn't phone home, doesn't need an account, and doesn't quietly eat your RAM while you're not looking.

## Features

### Shield — blocking at two layers

| Layer | What it does |
|---|---|
| **1 · Network** | Known ad/tracker domains (doubleclick, taboola, criteo, google-analytics, …) are dropped before the request ever leaves your machine |
| **2 · The page** | Whatever slips through gets stopped in-page: `fetch`, XHR, beacons, WebSockets, and ad script/image/iframe nodes stripped as they appear |

Each tab runs at one of three levels, switchable from the Shield button on the toolbar:

| Level | Behavior |
|---|---|
| **Strict** | Ads, trackers, tracking cookies and fingerprinting — all blocked. Some sites may break |
| **Balanced** *(default)* | Ads and obvious trackers blocked, fewer site breakages |
| **Off** | No blocking on that tab, for the one site that misbehaves |

The Shield button shows the count **and every domain blocked on the current page**, grouped by type (Ad / Tracker) with hit counts.

### Privacy & security

- HTTPS upgrading, and tracking parameters (`utm_*`, `gclid`, `fbclid`, `msclkid`) stripped from URLs
- Tracking cookies (`_ga`, `_fbp`, `_hj`, …) filtered
- Anti-fingerprinting: canvas, WebGL vendor and hardware info are blurred
- Private tabs skip history, session restore and password saving by design

> Anti-fingerprinting reduces what a site can read about your machine — it is not full anonymity.

### Secure DNS

Domain lookups go through encrypted DNS-over-HTTPS — Cloudflare (`1.1.1.1`), Google, or your own resolver — so your ISP can't build a browsing profile from DNS queries. Results are cached with their real TTL; if the resolver is unreachable, NEXUS falls back to system DNS instead of failing.

### Encrypted vault

Passwords are stored locally, encrypted with **AES-256-GCM**, key derived via **Argon2id**. The master password lives in RAM and is zeroized on lock. Nothing syncs to a server, because there isn't one — forget the master password and the vault is gone (that's the design, not a bug).

### Downloads

- File links (.zip, .pdf, .exe, …) detected automatically
- Up to **16 parallel range requests** with a live progress bar
- Single-stream fallback when the server doesn't support ranges

### Performance

- Background tabs idle for 5+ minutes are suspended — connection pool released, page cached, snaps back instantly on click
- Built on Tokio's async runtime for non-blocking networking

### Extensions

NEXUS implements enough of `chrome.runtime` that many Manifest-style content scripts run unmodified. Drop an extension folder into `nexus_extensions/` and toggle it in Settings.

## How It Compares

| | NEXUS | Chrome | Brave | Firefox |
|---|:---:|:---:|:---:|:---:|
| Core engine | Rust + OS WebView | Chromium (C++) | Chromium (C++) | Gecko (C++/Rust) |
| Telemetry | None | Heavy | Anonymized | Opt-out |
| Ad & tracker blocking | Built-in, 2 layers | Extension required | Built-in | Extension required |
| Network-layer blocking | Yes (sinkhole) | No | Yes | Via extensions |
| Secure DNS (DoH) | 1.1.1.1 / custom | Yes | Yes | Yes |
| Per-site block details | Every domain, per page | Counts only | Counts only | Not shown |
| Password vault encryption | AES-256-GCM + Argon2id | OS keychain | OS keychain | OS keychain |
| Idle memory | Low | High | Moderate | Moderate |
| Complex web apps | Good, not universal | Complete | Complete | Complete |
| Funding | None | Ad revenue | Crypto + ads | Search deals |

NEXUS renders pages through the OS's native WebView instead of shipping a browser engine — that's most of the memory savings, and the occasional compatibility gap.

## Installation

Prebuilt binaries for every release:

| Platform | File |
|---|---|
| Windows 10/11 (x64) | `nexus-windows-x64.zip` — extract, run `nexus.exe` |
| Linux (x64) | `nexus-linux-x64.deb` — `sudo dpkg -i nexus-linux-x64.deb` |
| Linux (x64, portable) | `nexus-linux-x64.AppImage` — `chmod +x`, run |
| macOS (x64) | `nexus-macos-x64.zip` — extract, run |

Latest release: **https://github.com/LocShadowVN/NexusBrowser/releases/latest**

Or build from source:

```bash
git clone https://github.com/LocShadowVN/NexusBrowser
cd NexusBrowser
cargo build --release
```

## System Requirements

| Component | Minimum |
|---|---|
| OS | Windows 10/11 (64-bit), macOS 11+, Ubuntu 20.04+ / Fedora 34+ / Arch |
| CPU | Dual-core 64-bit |
| RAM | 2 GB |
| Storage | 150 MB free |

Linux additionally needs WebKitGTK 4.1 and GTK 3 (pulled automatically by the `.deb`).

## Data & Storage

Everything lives next to the executable — no hidden profile folders:

| File / folder | Contents |
|---|---|
| `session.json` | Open tabs for next launch (private tabs excluded) |
| `bookmarks.json` | Bookmarks |
| `history.json` | Browsing history, private tabs excluded (max 2000 entries) |
| `config.json` | Settings |
| `nexus_vault.dat` | Encrypted password vault |
| `nexus_extensions/` | Extensions |
| `downloads/` | Downloaded files |

## Keyboard Shortcuts

| Shortcut | Action |
|---|---|
| `Ctrl + T` / `Ctrl + Shift + N` | New tab / new private tab |
| `Ctrl + W` | Close tab |
| `Ctrl + L` | Focus address bar |
| `Ctrl + D` | Bookmark page |
| `Ctrl + R` / `F5` | Reload |
| `Alt + ←` / `→` | Back / forward |
| `Ctrl + Tab` / `Ctrl + 1–9` | Switch tabs |
| `Ctrl + J` / `Ctrl + H` | Downloads / history |
| `Ctrl + Shift + I` | Developer console |
| `Esc` | Dismiss open popup |

## Known Limitations

Honest ones, so you know what you're installing:

- **Complex web apps** — pages that depend on localStorage or SPA routing may not work fully, because NEXUS renders pages through its own pipeline to keep blocking and cookies under Rust's control
- **File uploads** — multipart POSTs are sent directly from the page; the response isn't re-rendered
- **Browser import** — the Chrome/Firefox/Edge import is a stub
- **Fingerprinting** — reduced, not eliminated; Brave's farbling is stronger

## Development Notes

Everything lives in a single `src/main.rs`, organized into modules: `state`, `net`, `doh`, `sinkhole`, `injection`, `vault`, `sync`, `extensions`, `dl`, `search`, plus the embedded UI and the IPC bridge.

Maintained by [@LocShadowVN](https://github.com/LocShadowVN), with AI coding assistants used for implementation help and debugging — the architecture, tradeoffs and final review are human-driven.

## Contributing

Bug reports, feature ideas and pull requests are all welcome — especially from Rust developers who care about privacy.

## License

Distributed under **MPL-2.0** — see [LICENSE](LICENSE). No paid tier, no plans for one.

---

Built in Rust, by one developer who'd rather own a browser than rent one.
