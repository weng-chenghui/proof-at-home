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

// Decode JWT and extract the logged-in username
function getLoggedInUser() {
    const token = localStorage.getItem('pah_jwt_token');
    if (!token) return null;
    try {
        const payload = JSON.parse(atob(token.split('.')[1]));
        return payload.username || payload.nickname || payload.email || payload.sub || null;
    } catch { return null; }
}

// Returns true if logged in
function isLoggedIn() {
    return !!localStorage.getItem('pah_jwt_token');
}

// Show login gate on submit pages. Returns true if gate was shown (not logged in).
function loginGate(formId) {
    if (isLoggedIn()) return false;
    const form = document.getElementById(formId);
    if (form) form.style.display = 'none';
    const container = form ? form.parentElement : document.querySelector('.container');
    const gate = document.createElement('div');
    gate.className = 'login-gate';
    gate.innerHTML = `
        <div class="login-gate-icon">&#128274;</div>
        <h2>Login Required</h2>
        <p>Please log in or sign up to submit.</p>
        <a href="/login.html" class="btn">Log In</a>
        <a href="/signup.html" class="btn btn-secondary" style="margin-left:0.5rem">Sign Up</a>
    `;
    container.appendChild(gate);
    return true;
}

// Auto-fill a username field from JWT
function autoFillUsername(fieldId) {
    const field = document.getElementById(fieldId);
    if (!field) return;
    const user = getLoggedInUser();
    if (user) {
        field.value = user;
        field.readOnly = true;
        const hint = field.parentElement.querySelector('.hint');
        if (hint) {
            hint.textContent = 'From login';
        } else {
            const h = document.createElement('div');
            h.className = 'hint';
            h.textContent = 'From login';
            field.parentElement.appendChild(h);
        }
    }
}

// Auto-generate a UUID field with regenerate button
function autoGenId(fieldId) {
    const field = document.getElementById(fieldId);
    if (!field) return;
    field.value = crypto.randomUUID();
    field.readOnly = true;
    const wrapper = document.createElement('div');
    wrapper.className = 'id-field-actions';
    const regenBtn = document.createElement('button');
    regenBtn.type = 'button';
    regenBtn.className = 'btn-secondary btn-sm';
    regenBtn.textContent = 'Regenerate';
    regenBtn.onclick = () => { field.value = crypto.randomUUID(); field.readOnly = true; };
    const editBtn = document.createElement('button');
    editBtn.type = 'button';
    editBtn.className = 'btn-secondary btn-sm';
    editBtn.textContent = 'Edit';
    editBtn.onclick = () => { field.readOnly = false; field.focus(); };
    wrapper.appendChild(regenBtn);
    wrapper.appendChild(editBtn);
    field.parentElement.appendChild(wrapper);
    // Add hint
    const hint = field.parentElement.querySelector('.hint');
    if (!hint) {
        const h = document.createElement('div');
        h.className = 'hint';
        h.textContent = 'Generated automatically';
        field.parentElement.appendChild(h);
    }
}

function initNav() {
    const nav = document.getElementById('navbar');
    if (!nav) return;
    const token = localStorage.getItem('pah_jwt_token');
    const user = getLoggedInUser();

    const userSection = token
        ? `<div class="nav-user">
               <span class="nav-username">${escapeHtml(user || 'User')}</span>
               <a href="#" onclick="navLogout(event)">Logout</a>
           </div>`
        : `<div class="nav-user"><a href="/login.html">Log In</a> <a href="/signup.html">Sign Up</a></div>`;

    nav.innerHTML = `
        <a class="nav-brand" href="/">proof-at-home</a>
        <div class="nav-links">
            <a href="/conjectures.html">Conjectures</a>
            <a href="/reviews.html">Certificates</a>
            <a href="/nft-gallery.html">NFT Gallery</a>
            <a href="/submit-conjecture.html">Submit Conjecture</a>
        </div>
        ${userSection}
    `;
}

function toggleNavDropdown(e) {
    e.preventDefault();
    e.stopPropagation();
    const menu = e.target.closest('.nav-dropdown').querySelector('.nav-dropdown-menu');
    menu.classList.toggle('open');
    // Close on outside click
    const close = (ev) => {
        if (!e.target.closest('.nav-dropdown').contains(ev.target)) {
            menu.classList.remove('open');
            document.removeEventListener('click', close);
        }
    };
    if (menu.classList.contains('open')) {
        setTimeout(() => document.addEventListener('click', close), 0);
    }
}

function navLogout(e) {
    e.preventDefault();
    localStorage.removeItem('pah_jwt_token');
    window.location.reload();
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
