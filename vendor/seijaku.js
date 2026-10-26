/* seijaku — clean-room walk through a procedural Kyoto house.
   idea after @mengto (mengto/seijaku); no code copied. */
(function () {
  "use strict";

  var cv = document.getElementById("canvas");
  var panel = document.getElementById("panel");
  var toggle = document.getElementById("toggle");
  var whereEl = document.getElementById("where");
  var shot = document.getElementById("shot");
  var cap = document.getElementById("cap");
  var jumps = document.getElementById("jumps");

  var M_PLASTER = 0, M_TIMBER = 1, M_TATAMI = 2, M_SHOJI = 3, M_STONE = 4;
  var M_LEAF = 5, M_WATER = 6, M_ROOF = 7, M_CLOTH = 8;

  var STOPS = [
    { x: 0.55, y: 1.64, z: 3.15, lx: 0.68, ly: 1.32, lz: 12.0, room: "Entrance garden" },
    { x: 0.62, y: 1.58, z: 8.6, lx: 0.70, ly: 1.38, lz: 17.2, room: "Entrance garden" },
    { x: 0.60, y: 1.62, z: 17.2, lx: 0.45, ly: 1.48, lz: 26.0, room: "Genkan" },
    { x: 0.55, y: 1.84, z: 27.0, lx: -0.15, ly: 1.50, lz: 35.5, room: "Paper screens" },
    { x: 0.70, y: 1.82, z: 36.2, lx: 0.25, ly: 1.45, lz: 45.5, room: "Main hall" },
    { x: 0.58, y: 1.80, z: 45.2, lx: 0.20, ly: 1.32, lz: 51.2, room: "Tea room" },
    { x: 0.15, y: 1.55, z: 56.4, lx: 2.45, ly: 0.40, lz: 60.0, room: "Koi courtyard" },
    { x: 0.28, y: 1.58, z: 61.2, lx: 2.55, ly: 0.42, lz: 60.6, room: "Koi courtyard" },
    { x: 0.52, y: 1.82, z: 73.6, lx: -0.20, ly: 1.32, lz: 81.5, room: "Bedroom" },
    { x: 0.58, y: 1.80, z: 85.2, lx: 0.15, ly: 1.22, lz: 92.5, room: "Bath" },
    { x: 0.48, y: 1.58, z: 99.0, lx: 1.05, ly: 1.55, lz: 112.0, room: "Back garden" }
  ];
  var JUMPS = [
    ["Entrance garden", 0],
    ["Genkan", 2],
    ["Paper screens", 3],
    ["Tea room", 5],
    ["Koi courtyard", 6],
    ["Bedroom", 8],
    ["Bath", 9],
    ["Back garden", 10]
  ];

  var PAL = {
    spring: { top: [0.55, 0.70, 0.82], hor: [0.86, 0.91, 0.80], fog: [0.78, 0.86, 0.78], sun: [1.0, 0.97, 0.88], leaf: [0.93, 0.58, 0.66], leaf2: [0.98, 0.74, 0.78], moss: [0.36, 0.58, 0.30], gravel: [0.70, 0.68, 0.60], water: [0.22, 0.46, 0.50], hill: [0.52, 0.62, 0.52], part: [0.96, 0.62, 0.70] },
    summer: { top: [0.32, 0.55, 0.82], hor: [0.70, 0.86, 0.92], fog: [0.68, 0.82, 0.80], sun: [1.0, 0.98, 0.90], leaf: [0.18, 0.48, 0.24], leaf2: [0.28, 0.58, 0.28], moss: [0.20, 0.46, 0.22], gravel: [0.66, 0.64, 0.56], water: [0.10, 0.40, 0.46], hill: [0.40, 0.52, 0.42], part: [0.98, 0.92, 0.55] },
    autumn: { top: [0.48, 0.40, 0.40], hor: [0.95, 0.72, 0.50], fog: [0.86, 0.72, 0.58], sun: [1.0, 0.78, 0.50], leaf: [0.78, 0.22, 0.12], leaf2: [0.88, 0.46, 0.16], moss: [0.34, 0.42, 0.22], gravel: [0.72, 0.66, 0.56], water: [0.16, 0.34, 0.38], hill: [0.55, 0.46, 0.42], part: [0.90, 0.40, 0.16] },
    winter: { top: [0.62, 0.66, 0.74], hor: [0.84, 0.86, 0.88], fog: [0.80, 0.82, 0.84], sun: [0.92, 0.94, 0.96], leaf: [0.55, 0.58, 0.60], leaf2: [0.70, 0.72, 0.74], moss: [0.48, 0.50, 0.44], gravel: [0.74, 0.74, 0.72], water: [0.28, 0.40, 0.46], hill: [0.72, 0.74, 0.76], part: [0.95, 0.96, 0.98] }
  };

  var season = "autumn";
  var progress = 0;
  var vel = 0;
  var yaw = 0;
  var pitch = 0;
  var fov = 1.06;
  var glide = null;
  var dragging = false;
  var moved = false;
  var stillT = 0;
  var lastRoom = "";
  var audioOn = false;
  var readySent = false;
  var drew = false;
  var t0 = 0;

  var gl, sceneProg, skyProg, ptProg;
  var worldBuf, worldVAO, worldN = 0;
  var koiBuf, koiVAO, koiN = 0, koiArr;
  var ptBuf, ptVAO;
  var skyBuf, skyVAO;
  var P = new Float32Array(16);
  var V = new Float32Array(16);
  var MVP = new Float32Array(16);
  var verts = [];

  var NPART = 56;
  var px = new Float32Array(NPART);
  var py = new Float32Array(NPART);
  var pz = new Float32Array(NPART);
  var pvy = new Float32Array(NPART);
  var pph = new Float32Array(NPART);
  var pdat = new Float32Array(NPART * 6);

  var KOI = [
    { cx: -0.42, cz: 6.85, rx: 0.11, rz: 0.09, y: 0.33, sp: 0.7, ph: 0.4, sc: 0.15, col: [0.92, 0.42, 0.16] },
    { cx: 2.55, cz: 60.2, rx: 1.15, rz: 1.45, y: 0.12, sp: 0.32, ph: 1.1, sc: 0.38, col: [0.90, 0.36, 0.14] },
    { cx: 2.55, cz: 60.2, rx: 0.85, rz: 1.15, y: 0.14, sp: 0.46, ph: 2.5, sc: 0.30, col: [0.94, 0.90, 0.84] },
    { cx: 2.55, cz: 60.2, rx: 1.30, rz: 0.95, y: 0.10, sp: 0.38, ph: 3.7, sc: 0.34, col: [0.82, 0.26, 0.12] },
    { cx: 2.55, cz: 60.2, rx: 0.62, rz: 1.30, y: 0.13, sp: 0.52, ph: 5.1, sc: 0.26, col: [0.95, 0.55, 0.22] },
    { cx: 2.55, cz: 60.2, rx: 1.00, rz: 1.20, y: 0.11, sp: 0.28, ph: 0.3, sc: 0.32, col: [0.22, 0.16, 0.14] }
  ];

  function clamp(v, a, b) { return v < a ? a : v > b ? b : v; }
  function ler(a, b, t) { return a + (b - a) * t; }
  function smooth(t) { return t * t * (3 - 2 * t); }

  function shield(el) {
    var names = ["pointerdown", "pointermove", "pointerup", "pointercancel", "touchstart", "touchmove", "touchend", "wheel", "mousedown", "mouseup", "click", "dblclick"];
    for (var i = 0; i < names.length; i++) {
      el.addEventListener(names[i], function (e) { e.stopPropagation(); });
    }
  }
  shield(toggle);
  shield(panel);
  toggle.addEventListener("click", function (e) {
    e.stopPropagation();
    var on = !panel.classList.contains("open");
    panel.classList.toggle("open", on);
    toggle.setAttribute("aria-expanded", on ? "true" : "false");
    toggle.setAttribute("aria-label", on ? "Hide notes" : "Notes");
  });
  document.getElementById("seasons").addEventListener("click", function (e) {
    var b = e.target.closest ? e.target.closest("button") : null;
    if (!b) return;
    setSeason(b.getAttribute("data-s"));
  });
  for (var ji = 0; ji < JUMPS.length; ji++) {
    var jb = document.createElement("button");
    jb.type = "button";
    jb.textContent = JUMPS[ji][0];
    jb.setAttribute("data-i", String(JUMPS[ji][1]));
    jumps.appendChild(jb);
  }
  jumps.addEventListener("click", function (e) {
    var b = e.target.closest ? e.target.closest("button") : null;
    if (!b) return;
    var idx = parseInt(b.getAttribute("data-i"), 10);
    glide = idx / (STOPS.length - 1);
    vel = 0;
    moved = true;
  });

  function setSeason(name) {
    if (!PAL[name] || name === season && worldN) {
      season = name;
    } else {
      season = name;
      if (gl) rebuildWorld();
    }
    var buttons = document.querySelectorAll("#seasons button");
    for (var i = 0; i < buttons.length; i++) {
      buttons[i].classList.toggle("on", buttons[i].getAttribute("data-s") === season);
    }
  }

  function pingReady() {
    if (readySent) return;
    if (window.__gbSandbox && typeof window.__gbSandbox.ready === "function") {
      readySent = true;
      window.__gbSandbox.ready();
    }
  }

  function viewSize() {
    var w = cv.clientWidth;
    var h = cv.clientHeight;
    if (w < 2) w = window.innerWidth || 390;
    if (h < 2) h = window.innerHeight || 844;
    return [w, h];
  }
  function fit() {
    var s = viewSize();
    var d = Math.min(window.devicePixelRatio || 1, 1.5);
    var w = Math.max(2, Math.round(s[0] * d));
    var h = Math.max(2, Math.round(s[1] * d));
    if (cv.width !== w || cv.height !== h) {
      cv.width = w;
      cv.height = h;
    }
  }

  function armAudio() {
    if (audioOn) {
      if (window.__seijakuAudio && window.__seijakuAudio.state === "suspended") {
        window.__seijakuAudio.resume();
      }
      return;
    }
    var AC = window.AudioContext || window.webkitAudioContext;
    if (!AC) return;
    audioOn = true;
    var ac = new AC();
    window.__seijakuAudio = ac;
    var n = Math.floor(ac.sampleRate * 1.5);
    var buf = ac.createBuffer(1, n, ac.sampleRate);
    var data = buf.getChannelData(0);
    var prev = 0;
    for (var i = 0; i < n; i++) {
      var white = Math.random() * 2 - 1;
      prev = prev * 0.96 + white * 0.04;
      data[i] = prev * 2.2;
    }
    function loop(filterFreq, type, gain) {
      var src = ac.createBufferSource();
      src.buffer = buf;
      src.loop = true;
      var f = ac.createBiquadFilter();
      f.type = type;
      f.frequency.value = filterFreq;
      var g = ac.createGain();
      g.gain.value = gain;
      src.connect(f);
      f.connect(g);
      g.connect(ac.destination);
      src.start();
    }
    loop(520, "lowpass", 0.045);
    loop(1800, "bandpass", 0.012);
    var o1 = ac.createOscillator();
    var o2 = ac.createOscillator();
    o1.type = "sine";
    o2.type = "sine";
    o1.frequency.value = 174.61;
    o2.frequency.value = 220.0;
    var gd = ac.createGain();
    gd.gain.value = 0.012;
    o1.connect(gd);
    o2.connect(gd);
    gd.connect(ac.destination);
    o1.start();
    o2.start();
  }

  var ptrs = {};
  var gesture = 0;
  var pinch0 = 0;
  var fov0 = fov;

  function pinchDist() {
    var ks = Object.keys(ptrs);
    if (ks.length < 2) return 0;
    var a = ptrs[ks[0]], b = ptrs[ks[1]];
    return Math.hypot(a.x - b.x, a.y - b.y);
  }
  cv.addEventListener("pointerdown", function (e) {
    if (e.target !== cv) return;
    e.preventDefault();
    ptrs[e.pointerId] = { x: e.clientX, y: e.clientY, mode: 0 };
    try { cv.setPointerCapture(e.pointerId); } catch (err) {}
    dragging = true;
    vel = 0;
    glide = null;
    armAudio();
    if (Object.keys(ptrs).length === 2) {
      pinch0 = pinchDist();
      fov0 = fov;
    }
  }, { passive: false });
  cv.addEventListener("pointermove", function (e) {
    var p = ptrs[e.pointerId];
    if (!p) return;
    e.preventDefault();
    var ks = Object.keys(ptrs);
    if (ks.length >= 2 && pinch0 > 8) {
      var d = pinchDist();
      if (d > 8) fov = clamp(fov0 * (pinch0 / d), 0.62, 1.08);
      p.x = e.clientX;
      p.y = e.clientY;
      return;
    }
    var dx = e.clientX - p.x;
    var dy = e.clientY - p.y;
    if (!p.mode) {
      if (Math.abs(dx) + Math.abs(dy) < 4) return;
      p.mode = Math.abs(dx) > Math.abs(dy) ? 1 : 2;
      gesture = p.mode;
    }
    if (p.mode === 1) {
      yaw = clamp(yaw - dx * 0.0055, -1.05, 1.05);
      pitch = clamp(pitch - dy * 0.0032, -0.42, 0.38);
      vel = 0;
    } else {
      progress = clamp(progress + (-dy) * 0.00082, 0, 1);
      vel = (-dy) * 0.00009;
      moved = true;
    }
    p.x = e.clientX;
    p.y = e.clientY;
    stillT = 0;
  }, { passive: false });
  function endPtr(e) {
    var p = ptrs[e.pointerId];
    delete ptrs[e.pointerId];
    if (!Object.keys(ptrs).length) dragging = false;
  }
  cv.addEventListener("pointerup", endPtr);
  cv.addEventListener("pointercancel", endPtr);
  cv.addEventListener("wheel", function (e) {
    e.preventDefault();
    var dy = e.deltaY;
    if (e.deltaMode === 1) dy *= 16;
    if (e.deltaMode === 2) dy *= 400;
    progress = clamp(progress + clamp(dy, -80, 80) * 0.00042, 0, 1);
    vel = 0;
    glide = null;
    moved = true;
    stillT = 0;
    armAudio();
  }, { passive: false });

  function sample(t) {
    var n = STOPS.length - 1;
    var x = clamp(t, 0, 0.999999) * n;
    var i = Math.floor(x);
    var f = smooth(x - i);
    var a = STOPS[i], b = STOPS[i + 1];
    return {
      x: ler(a.x, b.x, f), y: ler(a.y, b.y, f), z: ler(a.z, b.z, f),
      lx: ler(a.lx, b.lx, f), ly: ler(a.ly, b.ly, f), lz: ler(a.lz, b.lz, f),
      room: (x - i) < 0.5 ? a.room : b.room
    };
  }
  function applyLook(cam) {
    var fx = cam.lx - cam.x, fy = cam.ly - cam.y, fz = cam.lz - cam.z;
    var cy = Math.cos(yaw), sy = Math.sin(yaw);
    var rx = fx * cy - fz * sy;
    var rz = fx * sy + fz * cy;
    var horiz = Math.hypot(rx, rz) || 1;
    var cp = Math.cos(pitch), sp = Math.sin(pitch);
    var h2 = horiz * cp - fy * sp;
    var y2 = fy * cp + horiz * sp;
    cam.lx = cam.x + (rx / horiz) * h2;
    cam.ly = cam.y + y2;
    cam.lz = cam.z + (rz / horiz) * h2;
    return cam;
  }

  function lookAt(out, ex, ey, ez, cx, cy, cz) {
    var zx = ex - cx, zy = ey - cy, zz = ez - cz;
    var zl = Math.hypot(zx, zy, zz) || 1;
    zx /= zl; zy /= zl; zz /= zl;
    var xx = zz, xy = 0, xz = -zx;
    var xl = Math.hypot(xx, xz) || 1;
    xx /= xl; xz /= xl;
    var yx = zy * xz - zz * xy;
    var yy = zz * xx - zx * xz;
    var yz = zx * xy - zy * xx;
    out[0] = xx; out[4] = xy; out[8] = xz; out[12] = -(xx * ex + xy * ey + xz * ez);
    out[1] = yx; out[5] = yy; out[9] = yz; out[13] = -(yx * ex + yy * ey + yz * ez);
    out[2] = zx; out[6] = zy; out[10] = zz; out[14] = -(zx * ex + zy * ey + zz * ez);
    out[3] = 0; out[7] = 0; out[11] = 0; out[15] = 1;
  }
  function perspective(out, fovy, aspect, near, far) {
    var f = 1 / Math.tan(fovy / 2);
    var nf = 1 / (near - far);
    out[0] = f / aspect; out[1] = 0; out[2] = 0; out[3] = 0;
    out[4] = 0; out[5] = f; out[6] = 0; out[7] = 0;
    out[8] = 0; out[9] = 0; out[10] = (far + near) * nf; out[11] = -1;
    out[12] = 0; out[13] = 0; out[14] = 2 * far * near * nf; out[15] = 0;
  }
  function mul(out, a, b) {
    for (var c = 0; c < 4; c++) {
      for (var r = 0; r < 4; r++) {
        out[c * 4 + r] = a[r] * b[c * 4] + a[4 + r] * b[c * 4 + 1] + a[8 + r] * b[c * 4 + 2] + a[12 + r] * b[c * 4 + 3];
      }
    }
  }

  function emitBox(cx, cy, cz, sx, sy, sz, yaw, r, g, b, m, out) {
    var hx = sx * 0.5, hy = sy * 0.5, hz = sz * 0.5;
    var c = Math.cos(yaw), s = Math.sin(yaw);
    function rot(x, y, z) {
      return [cx + x * c - z * s, cy + y, cz + x * s + z * c];
    }
    function rn(x, y, z) {
      return [x * c - z * s, y, x * s + z * c];
    }
    var cnr = [
      rot(-hx, -hy, -hz), rot(hx, -hy, -hz), rot(hx, hy, -hz), rot(-hx, hy, -hz),
      rot(-hx, -hy, hz), rot(hx, -hy, hz), rot(hx, hy, hz), rot(-hx, hy, hz)
    ];
    var faces = [
      [3, 2, 1, 0, rn(0, 0, -1)],
      [4, 5, 6, 7, rn(0, 0, 1)],
      [0, 1, 5, 4, rn(0, -1, 0)],
      [7, 6, 2, 3, rn(0, 1, 0)],
      [0, 4, 7, 3, rn(-1, 0, 0)],
      [1, 2, 6, 5, rn(1, 0, 0)]
    ];
    var order = [0, 1, 2, 0, 2, 3];
    for (var f = 0; f < 6; f++) {
      var F = faces[f];
      var n = F[4];
      for (var k = 0; k < 6; k++) {
        var p = cnr[F[order[k]]];
        out.push(p[0], p[1], p[2], n[0], n[1], n[2], r, g, b, m);
      }
    }
  }
  function box(x, y, z, sx, sy, sz, col, m) {
    emitBox(x, y, z, sx, sy, sz, 0, col[0], col[1], col[2], m, verts);
  }
  function shoji(x, y, z, w, h, axis) {
    var wood = [0.30, 0.18, 0.11];
    var paper = [0.97, 0.90, 0.74];
    var t = 0.045;
    if (axis === "x") {
      box(x, y, z, 0.025, h, w, paper, M_SHOJI);
      box(x, y + h * 0.5, z, 0.06, t, w + 0.05, wood, M_TIMBER);
      box(x, y - h * 0.5, z, 0.06, t, w + 0.05, wood, M_TIMBER);
      box(x, y, z - w * 0.5, 0.06, h, t, wood, M_TIMBER);
      box(x, y, z + w * 0.5, 0.06, h, t, wood, M_TIMBER);
      box(x, y, z, 0.045, h, t * 0.7, wood, M_TIMBER);
      box(x, y, z, 0.045, t * 0.7, w, wood, M_TIMBER);
    } else {
      box(x, y, z, w, h, 0.025, paper, M_SHOJI);
      box(x, y + h * 0.5, z, w + 0.05, t, 0.06, wood, M_TIMBER);
      box(x, y - h * 0.5, z, w + 0.05, t, 0.06, wood, M_TIMBER);
      box(x - w * 0.5, y, z, t, h, 0.06, wood, M_TIMBER);
      box(x + w * 0.5, y, z, t, h, 0.06, wood, M_TIMBER);
      box(x, y, z, t * 0.7, h, 0.045, wood, M_TIMBER);
      box(x, y, z, w, t * 0.7, 0.045, wood, M_TIMBER);
    }
  }
  function noren(x, y, z, w, h, col) {
    var strips = 3;
    var gap = w / strips;
    var sw = gap * 0.78;
    for (var i = 0; i < strips; i++) {
      box(x - w * 0.5 + gap * (i + 0.5), y - h * 0.5, z, sw, h, 0.02, col, M_CLOTH);
    }
  }
  function canopy(x, z, h, c1, c2) {
    var trunk = [0.28, 0.16, 0.10];
    box(x, h * 0.34, z, 0.14, h * 0.68, 0.14, trunk, M_TIMBER);
    box(x, h * 0.82, z, 1.15, 0.7, 1.05, c1, M_LEAF);
    box(x + 0.42, h * 1.02, z - 0.2, 0.78, 0.48, 0.72, c2, M_LEAF);
    box(x - 0.36, h * 0.96, z + 0.28, 0.7, 0.42, 0.68, c1, M_LEAF);
    box(x, 0.03, z, 1.5, 0.04, 1.5, [0.32, 0.26, 0.20], M_STONE);
  }
  function lantern(x, z) {
    var stone = [0.52, 0.50, 0.46];
    var roof = [0.22, 0.18, 0.18];
    box(x, 0.14, z, 0.46, 0.28, 0.46, stone, M_STONE);
    box(x, 0.62, z, 0.14, 0.68, 0.14, stone, M_STONE);
    box(x, 1.05, z, 0.32, 0.30, 0.32, [0.98, 0.78, 0.46], M_SHOJI);
    box(x, 1.28, z, 0.52, 0.08, 0.52, roof, M_ROOF);
    box(x, 1.40, z, 0.30, 0.14, 0.30, roof, M_ROOF);
  }
  function postsAlong(z0, z1, xs, y0) {
    var step = 3.15;
    for (var z = z0; z <= z1 + 0.05; z += step) {
      for (var i = 0; i < xs.length; i++) {
        box(xs[i], y0 + 1.08, z, 0.12, 2.16, 0.12, [0.29, 0.17, 0.10], M_TIMBER);
      }
    }
  }
  function roofSpan(z0, z1, snow) {
    var zc = (z0 + z1) * 0.5;
    var len = (z1 - z0) + 0.7;
    var roof = [0.20, 0.16, 0.17];
    box(-0.85, 2.70, zc, 6.5, 0.14, len, roof, M_ROOF);
    box(-0.85, 2.86, zc, 0.36, 0.16, len * 0.96, [0.16, 0.13, 0.14], M_ROOF);
    box(-0.85, 2.50, zc, 5.9, 0.06, (z1 - z0), [0.84, 0.76, 0.62], M_PLASTER);
    if (snow) {
      box(-0.85, 2.80, zc, 6.5, 0.06, len, [0.94, 0.95, 0.96], M_PLASTER);
    }
  }

  function buildWorld() {
    verts = [];
    var pal = PAL[season];
    var snow = season === "winter";
    var timber = [0.34, 0.20, 0.12];
    var plaster = [0.91, 0.86, 0.76];
    var indigo = [0.15, 0.20, 0.36];
    var hinoki = [0.72, 0.56, 0.34];
    var tatami = [0.62, 0.58, 0.30];
    var futon = [0.88, 0.85, 0.78];

    box(0, -0.28, 55, 52, 0.56, 190, pal.gravel, M_STONE);
    box(-8.5, 0.7, 46, 7, 1.4, 3.2, pal.hill, M_STONE);
    box(9.2, 0.55, 58, 6, 1.1, 3, pal.hill, M_STONE);

    canopy(-1.2, 13.4, 2.2, pal.leaf, pal.leaf2);
    canopy(2.25, 14.2, 1.85, pal.leaf2, pal.leaf);
    canopy(1.2, 106.2, 2.3, season === "winter" ? pal.leaf : [0.16, 0.34, 0.20], season === "winter" ? pal.leaf2 : [0.22, 0.42, 0.24]);
    lantern(1.22, 8.55);
    lantern(1.35, 104.2);

    var stones = [[0.42, 5.7], [0.78, 7.05], [0.38, 8.35], [0.82, 9.55]];
    for (var s = 0; s < stones.length; s++) {
      box(stones[s][0], 0.045, stones[s][1], 0.52, 0.07, 0.36, [0.58, 0.56, 0.52], M_STONE);
    }
    box(-0.42, 0.16, 6.85, 0.58, 0.24, 0.58, [0.50, 0.48, 0.44], M_STONE);
    box(-0.42, 0.30, 6.85, 0.40, 0.06, 0.40, pal.water, M_WATER);
    box(-0.2, 0.36, 6.85, 0.24, 0.03, 0.05, hinoki, M_TIMBER);
    box(-1.55, 0.03, 10.4, 0.9, 0.045, 0.7, pal.moss, M_LEAF);
    box(2.0, 0.03, 10.8, 0.85, 0.045, 0.65, pal.moss, M_LEAF);

    for (var b = 0; b < 6; b++) {
      var bx = 2.55 + (b % 3) * 0.16;
      var bz = 6.2 + Math.floor(b / 3) * 0.18;
      box(bx, 1.15, bz, 0.06, 2.3, 0.06, [0.35, 0.48, 0.24], M_TIMBER);
      box(bx, 2.25, bz, 0.28, 0.12, 0.22, pal.leaf, M_LEAF);
    }

    box(0.7 - 0.95, 1.15, 11.15, 0.16, 2.3, 0.16, timber, M_TIMBER);
    box(0.7 + 0.95, 1.15, 11.15, 0.16, 2.3, 0.16, timber, M_TIMBER);
    box(0.7, 2.32, 11.15, 2.25, 0.16, 0.22, timber, M_TIMBER);
    box(0.7, 2.52, 11.15, 2.7, 0.10, 0.85, [0.18, 0.15, 0.16], M_ROOF);
    box(0.7, 2.66, 11.15, 1.7, 0.10, 0.5, [0.16, 0.13, 0.14], M_ROOF);
    if (snow) box(0.7, 2.60, 11.15, 2.7, 0.05, 0.85, [0.94, 0.95, 0.96], M_PLASTER);
    noren(0.7, 2.15, 11.22, 1.55, 0.95, indigo);

    box(0.7, 0.06, 17.2, 4.6, 0.12, 7.2, [0.55, 0.53, 0.48], M_STONE);
    box(-1.6, 0.10, 16.2, 0.7, 0.12, 0.28, [0.25, 0.18, 0.14], M_TIMBER);
    box(-1.15, 0.10, 16.35, 0.55, 0.10, 0.22, [0.2, 0.16, 0.14], M_TIMBER);
    box(-3.35, 1.25, 17.4, 0.14, 2.2, 6.6, plaster, M_PLASTER);
    shoji(-0.55, 1.35, 16.4, 1.35, 1.7, "x");
    noren(0.7, 2.05, 14.2, 1.2, 0.7, indigo);

    function wing(z0, z1) {
      var zc = (z0 + z1) * 0.5;
      var len = z1 - z0;
      box(0.7, 0.16, zc, 2.15, 0.32, len, hinoki, M_TIMBER);
      box(-1.95, 0.16, zc, 2.85, 0.32, len, [0.40, 0.26, 0.16], M_TIMBER);
      box(-3.42, 1.35, zc, 0.12, 2.15, len, plaster, M_PLASTER);
      postsAlong(z0, z1, [-0.45, 1.75], 0.32);
      roofSpan(z0, z1, snow);
      var mats = Math.max(1, Math.round(len / 1.9));
      for (var i = 0; i < mats; i++) {
        for (var k = 0; k < 2; k++) {
          box(-2.35 + k * 0.95, 0.35, z0 + 0.95 + i * (len - 0.4) / mats, 0.88, 0.05, Math.min(1.7, (len - 0.5) / mats), tatami, M_TATAMI);
        }
      }
    }
    wing(21.6, 40.2);
    wing(40.2, 51.6);
    wing(68.0, 79.4);
    wing(79.4, 91.6);

    box(0.65, 0.28, 21.55, 2.0, 0.18, 0.42, hinoki, M_TIMBER);

    shoji(-0.45, 1.45, 24.2, 1.7, 1.85, "x");
    shoji(-0.45, 1.45, 32.4, 1.7, 1.85, "x");
    shoji(-0.45, 1.45, 37.6, 1.55, 1.85, "x");
    shoji(-0.45, 1.45, 43.4, 1.5, 1.75, "x");
    shoji(-0.45, 1.45, 48.6, 1.45, 1.7, "x");
    shoji(-0.45, 1.45, 71.5, 1.6, 1.8, "x");
    shoji(-0.45, 1.45, 76.4, 1.5, 1.75, "x");
    shoji(-2.0, 1.45, 91.45, 1.5, 1.5, "z");

    box(-2.9, 1.35, 30.2, 0.06, 1.15, 0.62, [0.25, 0.18, 0.16], M_TIMBER);
    box(-2.85, 1.35, 30.24, 0.02, 0.95, 0.42, [0.86, 0.82, 0.72], M_SHOJI);
    box(-2.2, 0.48, 30.6, 0.16, 0.22, 0.16, [0.45, 0.22, 0.28], M_LEAF);
    box(-1.85, 0.46, 31.4, 0.9, 0.18, 0.9, [0.36, 0.22, 0.13], M_TIMBER);
    box(-2.15, 0.40, 33.2, 0.55, 0.1, 0.55, indigo, M_CLOTH);
    box(-1.55, 0.40, 29.4, 0.55, 0.1, 0.55, [0.55, 0.18, 0.16], M_CLOTH);
    box(-1.7, 0.85, 26.4, 0.22, 0.7, 0.22, [0.96, 0.86, 0.62], M_SHOJI);

    box(-1.9, 0.28, 46.2, 0.7, 0.16, 0.7, [0.12, 0.10, 0.10], M_STONE);
    box(-1.9, 0.38, 46.2, 0.28, 0.06, 0.28, [0.85, 0.32, 0.12], M_SHOJI);
    box(-1.9, 0.55, 46.2, 0.22, 0.22, 0.22, [0.15, 0.12, 0.12], M_STONE);
    box(-2.3, 0.42, 44.2, 0.5, 0.08, 0.5, indigo, M_CLOTH);
    box(-1.4, 0.42, 48.0, 0.5, 0.08, 0.5, [0.45, 0.16, 0.14], M_CLOTH);

    box(2.55, 0.08, 60.2, 3.5, 0.1, 5.0, pal.water, M_WATER);
    box(2.55, 0.12, 57.55, 3.7, 0.16, 0.28, [0.48, 0.46, 0.42], M_STONE);
    box(2.55, 0.12, 62.85, 3.7, 0.16, 0.28, [0.48, 0.46, 0.42], M_STONE);
    box(0.95, 0.14, 60.2, 0.35, 0.22, 4.4, [0.50, 0.48, 0.44], M_STONE);
    box(4.35, 0.16, 60.2, 0.4, 0.28, 4.6, [0.46, 0.44, 0.40], M_STONE);
    box(3.6, 0.28, 58.2, 0.7, 0.28, 0.55, [0.42, 0.40, 0.38], M_STONE);
    box(1.7, 0.22, 62.2, 0.5, 0.24, 0.45, [0.40, 0.38, 0.36], M_STONE);
    box(3.3, 0.04, 64.2, 2.2, 0.06, 1.4, pal.moss, M_LEAF);
    canopy(3.5, 55.2, 2.3, pal.leaf, pal.leaf2);
    for (var q = 0; q < 5; q++) {
      box(4.3, 1.3, 57.5 + q * 0.22, 0.055, 2.6, 0.055, [0.30, 0.46, 0.22], M_TIMBER);
      box(4.3, 2.5, 57.5 + q * 0.22, 0.26, 0.1, 0.2, pal.leaf, M_LEAF);
    }
    var stepZ = [53.2, 54.6, 56.0, 64.6, 66.0];
    for (var st = 0; st < stepZ.length; st++) {
      box(0.55, 0.06, stepZ[st], 0.55, 0.08, 0.38, [0.56, 0.54, 0.50], M_STONE);
    }

    box(-2.05, 0.42, 74.2, 1.15, 0.1, 2.05, futon, M_PLASTER);
    box(-2.15, 0.50, 73.3, 0.55, 0.1, 0.38, [0.86, 0.84, 0.80], M_PLASTER);
    box(-1.85, 0.48, 75.2, 0.85, 0.08, 0.7, indigo, M_CLOTH);
    box(-2.85, 1.15, 77.4, 0.08, 1.5, 1.3, [0.42, 0.28, 0.22], M_TIMBER);

    box(-1.85, 0.55, 85.4, 1.45, 0.55, 1.15, hinoki, M_TIMBER);
    box(-1.85, 0.62, 85.4, 1.15, 0.28, 0.85, pal.water, M_WATER);
    box(-2.7, 0.28, 87.6, 0.28, 0.32, 0.28, hinoki, M_TIMBER);
    box(-1.05, 0.22, 87.4, 0.22, 0.2, 0.22, [0.45, 0.32, 0.2], M_TIMBER);
    box(0.7, 0.2, 84.0, 1.6, 0.08, 2.2, [0.52, 0.50, 0.46], M_STONE);

    box(0.4, 0.05, 104, 2.6, 0.08, 1.8, pal.moss, M_LEAF);
    box(-1.2, 0.06, 100.5, 1.4, 0.08, 1.2, pal.moss, M_LEAF);
    for (var f = 0; f < 7; f++) {
      box(-2.6 + f * 0.85, 0.55, 108.5, 0.08, 1.1, 0.9, [0.34, 0.28, 0.2], M_TIMBER);
    }
    box(0.2, 0.04, 96.5, 0.5, 0.06, 0.36, [0.55, 0.53, 0.48], M_STONE);
    box(0.55, 0.04, 98.2, 0.48, 0.06, 0.34, [0.55, 0.53, 0.48], M_STONE);
    box(0.3, 0.04, 100.2, 0.5, 0.06, 0.36, [0.55, 0.53, 0.48], M_STONE);

    var arr = new Float32Array(verts.length);
    for (var i = 0; i < verts.length; i++) arr[i] = verts[i];
    verts = [];
    return arr;
  }

  var VS = [
    "#version 300 es",
    "precision mediump float;",
    "layout(location=0) in vec3 aP;",
    "layout(location=1) in vec3 aN;",
    "layout(location=2) in vec3 aC;",
    "layout(location=3) in float aM;",
    "uniform mat4 uMVP;",
    "uniform float uTime;",
    "out vec3 vN; out vec3 vW; out vec3 vC; out float vM;",
    "void main(){",
    "  vec3 p=aP; float m=aM;",
    "  if(m>4.5 && m<5.5){",
    "    p.x+=sin(uTime*1.15+p.z*0.7+p.y)*0.045;",
    "    p.z+=cos(uTime*0.9+p.x*0.6)*0.03;",
    "  } else if(m>7.5 && m<8.5){",
    "    p.x+=sin(uTime*1.6+p.y*6.5+p.z)*0.028;",
    "  } else if(m>5.5 && m<6.5){",
    "    p.y+=sin(p.x*2.1+uTime*1.5)*sin(p.z*1.7-uTime*1.15)*0.012;",
    "  }",
    "  vW=p; vN=aN; vC=aC; vM=m;",
    "  gl_Position=uMVP*vec4(p,1.0);",
    "}"
  ].join("\n");

  var FS = [
    "#version 300 es",
    "precision mediump float;",
    "in vec3 vN; in vec3 vW; in vec3 vC; in float vM;",
    "out vec4 o;",
    "uniform vec3 uL; uniform vec3 uSun; uniform vec3 uFog; uniform vec3 uEye; uniform float uTime;",
    "void main(){",
    "  vec3 n=normalize(vN);",
    "  float nd=max(dot(n,uL),0.0);",
    "  float hemi=n.y*0.5+0.5; float downf=clamp(-n.y,0.0,1.0);",
    "  vec3 alb=vC; float m=vM;",
    "  if(m<0.5){ alb*=0.94+0.06*sin(vW.x*5.0+vW.z*4.0); }",
    "  else if(m<1.5){ alb*=0.74+0.26*smoothstep(0.2,0.8,sin(vW.y*42.0+vW.x*2.2)*0.5+0.5); }",
    "  else if(m<2.5){ alb*=0.92+0.06*sin(vW.x*64.0)+0.04*sin(vW.z*64.0); }",
    "  else if(m<3.5){ alb*=1.04+0.05*sin(vW.x*9.0+vW.y*7.0); }",
    "  else if(m<4.5){ alb*=0.94; }",
    "  else if(m<5.5){ alb*=0.86+0.14*sin(vW.x*1.7+vW.z*1.3+uTime*0.2); }",
    "  else if(m<6.5){ float w=sin(vW.x*3.0+uTime*1.6)*sin(vW.z*2.3-uTime*1.2); alb=mix(alb,vec3(0.78,0.90,0.92),0.16+0.1*w); alb+=uSun*pow(max(w,0.0),3.0)*0.16; }",
    "  else if(m<7.5){ float tile=step(0.52,fract(vW.x*3.2+vW.z*0.4)); alb*=0.84+0.2*tile; }",
    "  else { alb*=0.92+0.08*sin(vW.y*28.0); }",
    "  vec3 lit=alb*(0.50+0.24*hemi+0.22*downf)+alb*nd*uSun*0.58;",
    "  if(m>2.5 && m<3.5) lit=alb*(0.82+0.18*hemi)+vec3(0.20,0.14,0.06);",
    "  float dist=distance(vW,uEye);",
    "  float fog=smoothstep(8.5,36.0,dist);",
    "  lit=mix(lit,uFog,fog);",
    "  o=vec4(lit,1.0);",
    "}"
  ].join("\n");

  var SKY_VS = "#version 300 es\nin vec2 a;out vec2 v;void main(){v=a*0.5+0.5;gl_Position=vec4(a,0.0,1.0);}";
  var SKY_FS = [
    "#version 300 es",
    "precision mediump float;",
    "in vec2 v; out vec4 o;",
    "uniform vec3 uTop; uniform vec3 uHor; uniform vec3 uSun; uniform float uTime;",
    "void main(){",
    "  float h=v.y;",
    "  vec3 col=mix(uHor,uTop,smoothstep(0.0,0.78,h));",
    "  vec2 su=vec2(0.74,0.70);",
    "  float d=length((v-su)*vec2(0.62,1.0));",
    "  col+=uSun*exp(-d*d*22.0)*0.55;",
    "  float c=sin(v.x*8.0+v.y*2.4+uTime*0.04)*sin(v.x*2.2-uTime*0.02);",
    "  col+=vec3(1.0,0.98,0.94)*smoothstep(0.35,0.9,c)*0.05*smoothstep(0.25,0.75,h);",
    "  o=vec4(col,1.0);",
    "}"
  ].join("\n");

  var PT_VS = [
    "#version 300 es",
    "precision highp float;",
    "layout(location=0) in vec3 aP;",
    "layout(location=1) in vec3 aC;",
    "uniform mat4 uMVP; uniform float uScale;",
    "out vec3 vC;",
    "void main(){ gl_Position=uMVP*vec4(aP,1.0); gl_PointSize=max(2.0,uScale); vC=aC; }"
  ].join("\n");
  var PT_FS = [
    "#version 300 es",
    "precision highp float;",
    "in vec3 vC; out vec4 o; uniform float uTime; uniform float uMode;",
    "void main(){",
    "  vec2 q=gl_PointCoord*2.0-1.0;",
    "  if(dot(q,q)>1.0) discard;",
    "  float a=0.9;",
    "  if(uMode>0.5) a=0.25+0.75*(0.5+0.5*sin(uTime*3.2+vC.x*12.0));",
    "  o=vec4(vC,a);",
    "}"
  ].join("\n");

  function sh(type, src) {
    var s = gl.createShader(type);
    gl.shaderSource(s, src);
    gl.compileShader(s);
    if (!gl.getShaderParameter(s, gl.COMPILE_STATUS)) {
      console.error(gl.getShaderInfoLog(s));
      return null;
    }
    return s;
  }
  var progSeq = 1;
  function program(vs, fs) {
    var p = gl.createProgram();
    var a = sh(gl.VERTEX_SHADER, vs);
    var b = sh(gl.FRAGMENT_SHADER, fs);
    if (!a || !b) return null;
    gl.attachShader(p, a);
    gl.attachShader(p, b);
    gl.linkProgram(p);
    if (!gl.getProgramParameter(p, gl.LINK_STATUS)) {
      console.error(gl.getProgramInfoLog(p));
      return null;
    }
    p._id = String(progSeq++);
    return p;
  }
  function meshVAO(buf) {
    var vao = gl.createVertexArray();
    gl.bindVertexArray(vao);
    gl.bindBuffer(gl.ARRAY_BUFFER, buf);
    var stride = 40;
    gl.enableVertexAttribArray(0);
    gl.vertexAttribPointer(0, 3, gl.FLOAT, false, stride, 0);
    gl.enableVertexAttribArray(1);
    gl.vertexAttribPointer(1, 3, gl.FLOAT, false, stride, 12);
    gl.enableVertexAttribArray(2);
    gl.vertexAttribPointer(2, 3, gl.FLOAT, false, stride, 24);
    gl.enableVertexAttribArray(3);
    gl.vertexAttribPointer(3, 1, gl.FLOAT, false, stride, 36);
    gl.bindVertexArray(null);
    return vao;
  }

  function rebuildWorld() {
    var arr = buildWorld();
    worldN = arr.length / 10;
    gl.bindBuffer(gl.ARRAY_BUFFER, worldBuf);
    gl.bufferData(gl.ARRAY_BUFFER, arr, gl.STATIC_DRAW);
  }

  function seedParts() {
    for (var i = 0; i < NPART; i++) {
      px[i] = (Math.random() - 0.5) * 12;
      pz[i] = i < 24 ? Math.random() * 16 : Math.random() * 108;
      py[i] = 0.3 + Math.random() * 3.2;
      pvy[i] = 0.35 + Math.random() * 0.55;
      pph[i] = Math.random() * 6.28;
    }
  }

  var ptLive = false;
  function updateParts(dt) {
    var pal = PAL[season];
    var summer = season === "summer" ? 1 : 0;
    var fall = season === "winter" ? 0.55 : 1;
    for (var i = 0; i < NPART; i++) {
      if (summer) {
        py[i] += Math.sin(pph[i]) * dt * 0.25;
        px[i] += Math.cos(pph[i]) * dt * 0.15;
      } else {
        py[i] -= pvy[i] * dt * fall;
        px[i] += Math.sin(pph[i] + py[i]) * dt * 0.25;
        if (py[i] < 0) {
          py[i] = 2.6 + (i % 7) * 0.22;
          px[i] = ((i * 17) % 12) - 6;
          pz[i] = (i * 13) % 108;
        }
      }
      var o = i * 6;
      pdat[o] = px[i];
      pdat[o + 1] = py[i];
      pdat[o + 2] = pz[i];
      pdat[o + 3] = pal.part[0];
      pdat[o + 4] = pal.part[1];
      pdat[o + 5] = pal.part[2];
    }
    gl.bindBuffer(gl.ARRAY_BUFFER, ptBuf);
    if (!ptLive) {
      gl.bufferData(gl.ARRAY_BUFFER, pdat, gl.DYNAMIC_DRAW);
      ptLive = true;
    } else {
      gl.bufferSubData(gl.ARRAY_BUFFER, 0, pdat);
    }
    return summer;
  }

  var BX = [-1, 1, 1, -1, -1, 1, 1, -1];
  var BY = [-1, -1, 1, 1, -1, -1, 1, 1];
  var BZ = [-1, -1, -1, -1, 1, 1, 1, 1];
  var FACE = [3, 2, 1, 0, 4, 5, 6, 7, 0, 1, 5, 4, 7, 6, 2, 3, 0, 4, 7, 3, 1, 2, 6, 5];
  var TRI = [0, 1, 2, 0, 2, 3];
  var NORM = [0, 0, -1, 0, 0, 1, 0, -1, 0, 0, 1, 0, -1, 0, 0, 1, 0, 0];
  var cX = new Float32Array(8), cY = new Float32Array(8), cZ = new Float32Array(8);
  var koiArr = new Float32Array(KOI.length * 2 * 36 * 10);
  var koiLive = false;

  function writeBox(out, o, cx, cy, cz, sx, sy, sz, yaw, r, g, b, m) {
    var hx = sx * 0.5, hy = sy * 0.5, hz = sz * 0.5;
    var co = Math.cos(yaw), si = Math.sin(yaw);
    for (var i = 0; i < 8; i++) {
      var x = BX[i] * hx, z = BZ[i] * hz;
      cX[i] = cx + x * co - z * si;
      cY[i] = cy + BY[i] * hy;
      cZ[i] = cz + x * si + z * co;
    }
    for (var f = 0; f < 6; f++) {
      var nx = NORM[f * 3], ny = NORM[f * 3 + 1], nz = NORM[f * 3 + 2];
      var rnx = nx * co - nz * si, rny = ny, rnz = nx * si + nz * co;
      var base = f * 4;
      for (var k = 0; k < 6; k++) {
        var vi = FACE[base + TRI[k]];
        out[o++] = cX[vi];
        out[o++] = cY[vi];
        out[o++] = cZ[vi];
        out[o++] = rnx;
        out[o++] = rny;
        out[o++] = rnz;
        out[o++] = r;
        out[o++] = g;
        out[o++] = b;
        out[o++] = m;
      }
    }
    return o;
  }

  function updateKoi(time) {
    var o = 0;
    for (var i = 0; i < KOI.length; i++) {
      var k = KOI[i];
      var a = time * k.sp + k.ph;
      var x = k.cx + Math.cos(a) * k.rx;
      var z = k.cz + Math.sin(a) * k.rz;
      var yawK = a;
      var sc = k.sc;
      var dirx = -Math.sin(yawK), dirz = Math.cos(yawK);
      o = writeBox(koiArr, o, x, k.y, z, sc * 0.22, sc * 0.1, sc * 0.72, yawK, k.col[0], k.col[1], k.col[2], M_PLASTER);
      o = writeBox(koiArr, o, x - dirx * sc * 0.42, k.y, z - dirz * sc * 0.42, sc * 0.3, sc * 0.05, sc * 0.22, yawK, k.col[0] * 0.8, k.col[1] * 0.75, k.col[2] * 0.7, M_PLASTER);
    }
    koiN = o / 10;
    gl.bindBuffer(gl.ARRAY_BUFFER, koiBuf);
    if (!koiLive) {
      gl.bufferData(gl.ARRAY_BUFFER, koiArr, gl.DYNAMIC_DRAW);
      koiLive = true;
    } else {
      gl.bufferSubData(gl.ARRAY_BUFFER, 0, koiArr);
    }
  }

  function fallback2d() {
    var ctx = cv.getContext("2d");
    if (!ctx) return;
    function paint() {
      fit();
      var w = cv.width, h = cv.height;
      var g = ctx.createLinearGradient(0, 0, 0, h);
      g.addColorStop(0, "#6a5348");
      g.addColorStop(0.45, "#e7b07a");
      g.addColorStop(1, "#cbb89a");
      ctx.fillStyle = g;
      ctx.fillRect(0, 0, w, h);
      ctx.fillStyle = "#b7a48a";
      ctx.fillRect(0, h * 0.62, w, h);
      ctx.fillStyle = "#3a2416";
      ctx.fillRect(w * 0.16, h * 0.40, w * 0.028, h * 0.24);
      ctx.fillStyle = "#c4452d";
      ctx.beginPath();
      ctx.arc(w * 0.18, h * 0.38, w * 0.13, 0, 6.2832);
      ctx.fill();
      ctx.fillStyle = "#2c1c12";
      ctx.fillRect(w * 0.36, h * 0.34, w * 0.03, h * 0.30);
      ctx.fillRect(w * 0.60, h * 0.34, w * 0.03, h * 0.30);
      ctx.fillRect(w * 0.34, h * 0.32, w * 0.32, h * 0.035);
      ctx.fillStyle = "#243044";
      ctx.fillRect(w * 0.43, h * 0.40, w * 0.045, h * 0.16);
      ctx.fillRect(w * 0.49, h * 0.40, w * 0.045, h * 0.16);
      ctx.fillRect(w * 0.55, h * 0.40, w * 0.045, h * 0.16);
      ctx.fillStyle = "#f3e2b0";
      ctx.fillRect(w * 0.46, h * 0.46, w * 0.10, h * 0.14);
      if (!drew) {
        drew = true;
        pingReady();
      }
      requestAnimationFrame(paint);
    }
    paint();
  }

  function bootGl() {
    fit();
    gl = cv.getContext("webgl2", { antialias: false, alpha: false, depth: true, stencil: false, powerPreference: "high-performance" });
    if (!gl) return false;
    sceneProg = program(VS, FS);
    skyProg = program(SKY_VS, SKY_FS);
    ptProg = program(PT_VS, PT_FS);
    if (!sceneProg || !skyProg || !ptProg) return false;
    worldBuf = gl.createBuffer();
    worldVAO = meshVAO(worldBuf);
    rebuildWorld();
    koiBuf = gl.createBuffer();
    koiVAO = meshVAO(koiBuf);
    ptBuf = gl.createBuffer();
    ptVAO = gl.createVertexArray();
    gl.bindVertexArray(ptVAO);
    gl.bindBuffer(gl.ARRAY_BUFFER, ptBuf);
    gl.enableVertexAttribArray(0);
    gl.vertexAttribPointer(0, 3, gl.FLOAT, false, 24, 0);
    gl.enableVertexAttribArray(1);
    gl.vertexAttribPointer(1, 3, gl.FLOAT, false, 24, 12);
    gl.bindVertexArray(null);
    skyBuf = gl.createBuffer();
    gl.bindBuffer(gl.ARRAY_BUFFER, skyBuf);
    gl.bufferData(gl.ARRAY_BUFFER, new Float32Array([-1, -1, 1, -1, -1, 1, 1, 1]), gl.STATIC_DRAW);
    skyVAO = gl.createVertexArray();
    gl.bindVertexArray(skyVAO);
    gl.bindBuffer(gl.ARRAY_BUFFER, skyBuf);
    gl.enableVertexAttribArray(0);
    gl.vertexAttribPointer(0, 2, gl.FLOAT, false, 0, 0);
    gl.bindVertexArray(null);
    seedParts();
    gl.enable(gl.DEPTH_TEST);
    gl.disable(gl.CULL_FACE);
    return true;
  }

  var loc = {};
  function L(prog, name) {
    var k = prog._id + name;
    if (loc[k] === undefined) loc[k] = gl.getUniformLocation(prog, name);
    return loc[k];
  }

  var last = 0;
  function frame(t) {
    requestAnimationFrame(frame);
    if (!t0) t0 = t;
    var dt = last ? Math.min(0.033, (t - last) / 1000) : 0.016;
    last = t;
    if (!dragging) {
      if (glide != null) {
        progress += (glide - progress) * Math.min(1, dt * 4.5);
        if (Math.abs(glide - progress) < 0.0015) {
          progress = glide;
          glide = null;
        }
      } else {
        progress = clamp(progress + vel, 0, 1);
        vel *= 0.92;
        if (Math.abs(vel) < 0.00002) vel = 0;
        if (progress <= 0 || progress >= 1) vel = 0;
      }
    }
    var cam = applyLook(sample(progress));
    if (cam.room !== lastRoom) {
      lastRoom = cam.room;
      whereEl.textContent = cam.room;
      cap.textContent = cam.room;
    }
    var moving = dragging || Math.abs(vel) > 0.00004 || glide != null;
    if (moved && !moving) stillT += dt;
    else stillT = 0;
    if (shot) shot.classList.toggle("show", moved && stillT > 1.15);

    fit();
    var pal = PAL[season];
    gl.viewport(0, 0, cv.width, cv.height);
    gl.clearColor(pal.hor[0], pal.hor[1], pal.hor[2], 1);
    gl.clear(gl.COLOR_BUFFER_BIT | gl.DEPTH_BUFFER_BIT);
    gl.disable(gl.DEPTH_TEST);
    gl.useProgram(skyProg);
    gl.uniform3fv(L(skyProg, "uTop"), pal.top);
    gl.uniform3fv(L(skyProg, "uHor"), pal.hor);
    gl.uniform3fv(L(skyProg, "uSun"), pal.sun);
    gl.uniform1f(L(skyProg, "uTime"), t * 0.001);
    gl.bindVertexArray(skyVAO);
    gl.drawArrays(gl.TRIANGLE_STRIP, 0, 4);

    var aspect = cv.width / Math.max(1, cv.height);
    perspective(P, fov, aspect, 0.08, 90);
    lookAt(V, cam.x, cam.y, cam.z, cam.lx, cam.ly, cam.lz);
    mul(MVP, P, V);
    var eye = [cam.x, cam.y, cam.z];
    var light = [0.15, 0.92, -0.32];
    var ll = Math.hypot(light[0], light[1], light[2]);
    light[0] /= ll; light[1] /= ll; light[2] /= ll;

    gl.enable(gl.DEPTH_TEST);
    gl.clear(gl.DEPTH_BUFFER_BIT);
    updateKoi(t * 0.001);
    gl.useProgram(sceneProg);
    gl.uniformMatrix4fv(L(sceneProg, "uMVP"), false, MVP);
    gl.uniform1f(L(sceneProg, "uTime"), t * 0.001);
    gl.uniform3fv(L(sceneProg, "uL"), light);
    gl.uniform3fv(L(sceneProg, "uSun"), pal.sun);
    gl.uniform3fv(L(sceneProg, "uFog"), pal.fog);
    gl.uniform3fv(L(sceneProg, "uEye"), eye);
    gl.bindVertexArray(worldVAO);
    gl.drawArrays(gl.TRIANGLES, 0, worldN);
    gl.bindVertexArray(koiVAO);
    gl.drawArrays(gl.TRIANGLES, 0, koiN);

    var summer = updateParts(dt);
    gl.enable(gl.BLEND);
    gl.blendFunc(gl.SRC_ALPHA, gl.ONE_MINUS_SRC_ALPHA);
    gl.depthMask(false);
    gl.useProgram(ptProg);
    gl.uniformMatrix4fv(L(ptProg, "uMVP"), false, MVP);
    gl.uniform1f(L(ptProg, "uTime"), t * 0.001);
    gl.uniform1f(L(ptProg, "uMode"), summer);
    gl.uniform1f(L(ptProg, "uScale"), Math.max(2.5, cv.height / 140));
    gl.bindVertexArray(ptVAO);
    gl.drawArrays(gl.POINTS, 0, NPART);
    gl.depthMask(true);
    gl.disable(gl.BLEND);

    if (!drew) {
      drew = true;
      pingReady();
    } else if (!readySent) {
      pingReady();
    }
  }

  window.addEventListener("resize", fit);

  function start() {
    try {
      if (!bootGl()) {
        fallback2d();
        return;
      }
    } catch (err) {
      console.error(err);
      fallback2d();
      return;
    }
    requestAnimationFrame(frame);
  }
  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", start);
  } else {
    start();
  }
})();
