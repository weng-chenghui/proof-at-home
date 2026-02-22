// shared.js — proof-at-home web UI helpers

async function api(method, path, body, contentType) {
    const opts = { method, headers: {} };
    const token = localStorage.getItem('pah_jwt_token');
    if (token) opts.headers['Authorization'] = 'Bearer ' + token;
    if (body && contentType === 'application/gzip') {
        opts.headers['Content-Type'] = 'application/gzip';
        opts.body = body;
    } else if (body) {
        opts.headers['Content-Type'] = 'application/json';
        opts.body = JSON.stringify(body);
    }
    const res = await fetch(path, opts);
    if (!res.ok) {
        const err = await res.json().catch(() => ({ error: res.statusText }));
        throw { status: res.status, ...err };
    }
    const text = await res.text();
    return text ? JSON.parse(text) : {};
}

function initNav() {
    const nav = document.getElementById('navbar');
    if (!nav) return;
    nav.innerHTML = `
        <a class="nav-brand" href="/">proof-at-home</a>
        <a href="/problems.html">Problems</a>
        <a href="/reviews.html">Reviews</a>
        <a href="/submit-problem.html">Submit Problem</a>
        <a href="/submit-result.html">Submit Result</a>
        <a href="/submit-batch.html">Submit Batch</a>
        <a href="/submit-review.html">Submit Review</a>
        <a href="/settings.html">Settings</a>
    `;
}

function showMsg(containerId, text, isError) {
    const el = document.getElementById(containerId);
    if (!el) return;
    el.className = 'msg ' + (isError ? 'msg-error' : 'msg-success');
    el.textContent = text;
    el.style.display = 'block';
}

function hideMsg(containerId) {
    const el = document.getElementById(containerId);
    if (el) el.style.display = 'none';
}

function difficultyBadge(d) {
    const cls = d === 'easy' ? 'badge-easy' : d === 'medium' ? 'badge-medium' : 'badge-hard';
    return `<span class="badge ${cls}">${d}</span>`;
}

function statusDot(s) {
    const cls = s === 'proved' ? 'status-proved' : 'status-open';
    return `<span class="status-dot ${cls}"></span>${s || 'open'}`;
}

function escapeHtml(str) {
    if (!str) return '';
    return str.replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;');
}

document.addEventListener('DOMContentLoaded', initNav);
