/* ========= Helpers ========= */
function mulberry32(a){ return function(){ let t=a+=0x6D2B79F5; t=Math.imul(t^t>>>15, t|1); t^=t+Math.imul(t^t>>>7, t|61); return ((t^t>>>14)>>>0)/4294967296; } }
function hashStringToInt(str){ let h=2166136261>>>0; for(let i=0;i<str.length;i++){h^=str.charCodeAt(i); h=Math.imul(h,16777619)} return h>>>0 }
const clamp=(x,a,b)=>Math.min(b,Math.max(a,x));
const TAU=Math.PI*2;

/* ========= Palettes ========= */
const PAL=()=>{
  const app=document.getElementById('app');
  const css=v=>getComputedStyle(app).getPropertyValue(v).trim();
  return {
    bg: getComputedStyle(document.body).backgroundColor || '#0b1220',
    waves: [css('--wave1'), css('--wave2'), css('--wave3'), css('--wave4')]
  };
};

/* ========= Canvas / Scene ========= */
let canvas, ctx, DPR=1, W=1600, H=900, running=true;
let seedRand, hue=0, palette=null;
const layers = [
  { amp: 40, speed: 0.35 },
  { amp: 60, speed: 0.25 },
  { amp: 75, speed: 0.20 },
  { amp: 90, speed: 0.15 }
];
let tPhase=0;

/* Per-layer state */
const LSTATE = layers.map(()=>({
  xDrift: 0, xVel: 0,
  parallax: 0,
  thickness: 1.5
}));
/* ========= Rock Oscillator State ========= */
const ROCK_OSC = layers.map((_,i)=>({
  y:0, v:0, phase:0
}));
let prevEnvVals = {bass:0, sub:0, flux:0};


/* ========= Styles (architectures) ========= */
let STYLE = 'pop'; // 'pop' | 'rock'

// Pop: исходная мягкая архитектура (округлые вершины).
const POP_CFG = {
  attack:{ sub:0.25, bass:0.22, lowmid:0.18, mid:0.16, highmid:0.16, treble:0.20 },
  release:{ sub:0.08, bass:0.10, lowmid:0.12, mid:0.12, highmid:0.14, treble:0.16 },
  ampK(env){ return 0.75 + env.bass*1.2 + env.rms*0.3; },
  rippleK(env){ return 0.35 + env.highmid*0.7 + env.treble*0.5; },
  kick(env){ return env.sub*0.6 + env.bass*0.45 + env.flux*0.15; },
  xVelBase(i){ return (i+1)*0.02; },
  xVelKick:0.05,
  fluxThresh:0.9,
  swellK:0.12,
  thicknessTarget(env){ return 1.2 + env.lowmid*0.8 + env.mid*0.6; },
  steps: 96,
  strokeJoin: 'round',
  strokeCap: 'round',
  strokeThinK: 1.0,
  rippleFreq: 1.18,
};

// Rock: другая архитектура — остро, «кусп», локальный сжим, edge jitter.
// Амплитуда не увеличивается относительно Pop.

const ROCK_CFG = {
  attack:{ sub:0.30, bass:0.26, lowmid:0.20, mid:0.18, highmid:0.18, treble:0.22 },
  release:{ sub:0.05, bass:0.06, lowmid:0.10, mid:0.10, highmid:0.12, treble:0.14 },
  ampK(env){ return 0.75 + env.bass*1.2 + env.rms*0.3; }, // та же высота, что у Pop
  rippleK(env){ return 0.35 + env.highmid*0.7 + env.treble*0.55; },
  kick(env){ return env.sub*0.65 + env.bass*0.55 + env.flux*0.25; },
  xVelBase(i){ return (i+1)*0.03; },
  xVelKick:0.08,
  fluxThresh:0.82,
  swellK:0.20,
  thicknessTarget(env){ return 1.15 + env.lowmid*0.7 + env.mid*0.5 + env.bass*0.25; },
  steps: 80,
  strokeJoin: 'miter',
  strokeCap: 'butt',
  strokeThinK: 0.9,
  rippleFreq: 1.35,
  // Параметры осциллятора
  kxBase: 0.020,              // пространственная частота по X
  w0:    [9.0, 11.0, 13.5, 16.0], // собств. частота для слоёв (рад/с в наших условных ед.)
  zeta:  [0.28,0.24,0.20,0.18],   // демпфирование (чуть меньше впереди)
  drive: { flux: 1.1, bassJerk: 0.9, sub: 0.6 } // вклад силового воздействия
};


function CFG(){ return STYLE==='rock' ? ROCK_CFG : POP_CFG; }

/* ========= Audio ========= */
let AC=null, analyser=null, timeAnalyser=null, dataArray=null, gain=null, srcNode=null, mediaStream=null, usingMic=false, activeAudio=null;
let destNode=null;
let recTimeoutId = null;
let autoStopCleanup = null;

function setupAudio(){
  if(!AC) AC=new (window.AudioContext||window.webkitAudioContext)();
  if(!analyser){ analyser=AC.createAnalyser(); analyser.fftSize=2048; analyser.smoothingTimeConstant=0.88; }
  if(!timeAnalyser){ timeAnalyser=AC.createAnalyser(); timeAnalyser.fftSize=1024; }
  if(!gain){ gain=AC.createGain(); gain.gain.value=1.0; }
  if(!destNode){ destNode = AC.createMediaStreamDestination(); }
  if(!dataArray) dataArray=new Uint8Array(analyser.frequencyBinCount);

  try{ gain.disconnect(); }catch{}
  gain.connect(analyser);
  analyser.connect(AC.destination);
  gain.connect(timeAnalyser);
  gain.connect(destNode);
}

function connectSource(node){
  if(srcNode) try{ srcNode.disconnect(); }catch{}
  node.connect(gain);
  srcNode=node;
}

function useFile(file){
  usingMic=false; stopMic(); setupAudio();
  if(activeAudio){ try{ activeAudio.pause(); }catch{} activeAudio=null; }

  const audio=new Audio();
  activeAudio=audio;
  audio.src=URL.createObjectURL(file);
  audio.crossOrigin="anonymous";
  audio.loop=true;
  audio.autoplay=false;
  audio.preload='metadata';

  const node=AC.createMediaElementSource(audio);
  connectSource(node);

  setStatus('Файл загружен — готов к записи');
}

async function useMic(){
  usingMic=true; setupAudio();
  if(activeAudio){ try{ activeAudio.pause(); }catch{} activeAudio=null; }
  try{
    mediaStream=await navigator.mediaDevices.getUserMedia({audio:true, video:false});
    const node=AC.createMediaStreamSource(mediaStream); connectSource(node);
    if(AC.state!=='running') await AC.resume();
    setStatus('Микрофон активен');
  }catch{ setStatus('Доступ к микрофону отклонён'); }
}
function stopMic(){ if(mediaStream){ for(const t of mediaStream.getTracks()) t.stop(); mediaStream=null; } }

/* ========= Analysis ========= */
const AENV = { sub:0, bass:0, lowmid:0, mid:0, highmid:0, treble:0, flux:0, centroid:0, rolloff:0, rms:0 };
const prevSpec = { buf:null };
function idxFor(freq, sr, n){ const nyq=sr/2; return Math.max(0, Math.min(n-1, Math.round(freq/nyq*n))); }
function avg(a,l,r){ let s=0,c=0; for(let i=l;i<=r;i++){ s+=a[i]; c++; } return c?s/c:0; }
function envFollow(prev,val,attack,release){ return (val>prev) ? prev + (val-prev)*attack : prev + (val-prev)*release; }

function analyze(){
  if(!analyser){ return AENV; }
  analyser.getByteFrequencyData(dataArray);
  const sr = AC?.sampleRate || 44100;
  const n = analyser.frequencyBinCount;

  const i = f => idxFor(f, sr, n);
  const subB   = avg(dataArray, i(20),   i(60));
  const bassB  = avg(dataArray, i(60),   i(150));
  const lowmB  = avg(dataArray, i(150),  i(400));
  const midB   = avg(dataArray, i(400),  i(1200));
  const highmB = avg(dataArray, i(1200), i(3000));
  const trebB  = avg(dataArray, i(3000), i(8000));

  const sens = parseFloat(document.getElementById('sens').value || '1.0');
  const norm = v => Math.min(1.8, (v * sens) / 140);

  let flux = 0;
  if(!prevSpec.buf) prevSpec.buf = new Uint8Array(n);
  for(let k=0;k<n;k++){ const d=dataArray[k]-prevSpec.buf[k]; if(d>0) flux += d; }
  let sum=0, weighted=0;
  for(let k=0;k<n;k++){ sum += dataArray[k]; weighted += dataArray[k]*k; }
  const centroidIdx = sum>0 ? (weighted/sum) : 0;
  let cum=0, rollIdx=0, target=sum*0.85;
  for(let k=0;k<n;k++){ cum += dataArray[k]; if(cum>=target){ rollIdx=k; break; } }
  prevSpec.buf.set(dataArray);

  const tbuf = new Uint8Array(timeAnalyser.fftSize);
  timeAnalyser.getByteTimeDomainData(tbuf);
  let rms=0; for(let k=0;k<tbuf.length;k++){ const x=(tbuf[k]-128)/128; rms += x*x; } rms = Math.sqrt(rms/tbuf.length);

  const cfg = CFG();

  AENV.sub     = envFollow(AENV.sub,     norm(subB),   cfg.attack.sub,  cfg.release.sub);
  AENV.bass    = envFollow(AENV.bass,    norm(bassB),  cfg.attack.bass, cfg.release.bass);
  AENV.lowmid  = envFollow(AENV.lowmid,  norm(lowmB),  cfg.attack.lowmid, cfg.release.lowmid);
  AENV.mid     = envFollow(AENV.mid,     norm(midB),   cfg.attack.mid,  cfg.release.mid);
  AENV.highmid = envFollow(AENV.highmid, norm(highmB), cfg.attack.highmid, cfg.release.highmid);
  AENV.treble  = envFollow(AENV.treble,  norm(trebB),  cfg.attack.treble, cfg.release.treble);

  const fluxN = Math.min(2.0, flux/800 * sens);
  const centN = centroidIdx / n;
  const rollN = rollIdx / n;
  const rmsN  = rms;

  AENV.flux    = envFollow(AENV.flux,    fluxN, 0.25, 0.12);
  AENV.centroid= envFollow(AENV.centroid,centN, 0.20, 0.14);
  AENV.rolloff = envFollow(AENV.rolloff, rollN,0.20, 0.14);
  AENV.rms     = envFollow(AENV.rms,     rmsN, 0.25, 0.16);

  return AENV;
}

/* ========= Noise ========= */
function makeNoise1D(rand){
  const n=5;
  const freq=[], amp=[], phase=[];
  for(let i=0;i<n;i++){
    freq.push((0.0006 + rand()*0.0015)*(1+i*0.8));
    amp.push(1.0/Math.pow(1.6,i+1));
    phase.push(rand()*TAU);
  }
  return (x, t)=>{
    let y=0;
    for(let i=0;i<n;i++) y += Math.sin(x*freq[i] + t*(0.6+i*0.15) + phase[i]) * amp[i];
    return y;
  };
}
let NOISES=[];

/* ========= Rendering utilities ========= */
function rngFrom(x){ // детерминированный "шум" для edge jitter
  const s = Math.sin(x*12.9898 + 78.233) * 43758.5453;
  return s - Math.floor(s);
}

/* ========= Rendering ========= */
function resize(){
  const r=canvas.getBoundingClientRect();
  DPR=Math.max(1, Math.min(window.devicePixelRatio||1, 3));
  W = r.width;
  H = r.height;
  canvas.width  = Math.floor(W * DPR);
  canvas.height = Math.floor(H * DPR);
  ctx.setTransform(DPR,0,0,DPR,0,0);
}
function clearSoft(fade){
  ctx.fillStyle=`rgba(0,0,0,${fade})`;
  ctx.fillRect(0,0,W,H);
}

function drawLayerPop(i, baseY, ampK, rippleK, thickness, xDrift, parallax){
  const color=palette.waves[i%palette.waves.length] || '#fff';
  const width=W, height=H;
  const cfg=POP_CFG;
  const steps=cfg.steps;
  const dx=width/(steps-1);

  const prevIdx = (i>0? i-1 : 0);
  const noiseMain = NOISES[i] || NOISES[0];
  const noiseRipple = NOISES[prevIdx] || NOISES[0];

  ctx.beginPath();
  for(let s=0;s<steps;s++){
    const x=s*dx + xDrift;
    const n=noiseMain(x, tPhase * (1+layers[i].speed*0.18) + parallax);
    const r=noiseRipple(x*cfg.rippleFreq, tPhase*0.72 + i*0.3);
    const y=baseY + n * layers[i].amp * ampK + r * layers[i].amp * 0.35 * rippleK;
    if(s===0) ctx.moveTo(x - xDrift, y); else ctx.lineTo(x - xDrift, y);
  }

  ctx.lineTo(width, height);
  ctx.lineTo(0, height);
  ctx.closePath();

  ctx.globalCompositeOperation='source-over';
  ctx.globalAlpha=0.10;
  ctx.fillStyle=color;
  ctx.fill();

  ctx.globalAlpha=0.75;
  ctx.strokeStyle=color;
  ctx.lineWidth=thickness * cfg.strokeThinK;
  ctx.lineJoin=cfg.strokeJoin; ctx.lineCap=cfg.strokeCap;
  ctx.stroke();
  ctx.globalAlpha=1.0;
}


function drawLayerRock(i, baseY, ampK, rippleK, thickness, xDrift, parallax){
  const color=palette.waves[i%palette.waves.length] || '#fff';
  const width=W, height=H;
  const cfg=ROCK_CFG;
  const steps=cfg.steps;
  const dx=width/(steps-1);

  const prevIdx = (i>0? i-1 : 0);
  const noiseMain = NOISES[i] || NOISES[0];
  const noiseRipple = NOISES[prevIdx] || NOISES[0];

  // 1) Базовая мягкая линия (высота как у Pop)
  const xs=new Array(steps);
  const yBase=new Array(steps);
  for(let s=0;s<steps;s++){
    const x=s*dx + xDrift;
    const n=noiseMain(x, tPhase * (1+layers[i].speed*0.18) + parallax);
    const r=noiseRipple(x*cfg.rippleFreq, tPhase*0.72 + i*0.3);
    const y0 = baseY + n * layers[i].amp * ampK + r * layers[i].amp * 0.30 * rippleK;
    xs[s]=x - xDrift;
    yBase[s]=y0;
  }

  // 2) Осциллирующий «звон» вокруг базы — управляется физикой
  const osc = ROCK_OSC[i];
  const kx = cfg.kxBase*(1 + i*0.18); // чаще у «передних» слоёв
  const envHigh = (AENV.highmid*0.7 + AENV.treble*0.9 + AENV.flux*0.5);
  const envWindow = (s)=>{ // затухание к краям
    const t=s/(steps-1);
    return Math.sin(Math.PI*t)**0.9;
  };

  const ys = new Array(steps);
  for(let s=0;s<steps;s++){
    const oscX = Math.sin(kx*xs[s] + osc.phase);                 // осцилляция вдоль X
    const envAmp = envWindow(s) * (0.6 + 0.4*envHigh);            // локальная громкость «звона»
    let ring = osc.y * oscX * envAmp;

    // Жёсткий лимит: не выше базовой по модулю
    const limit = Math.abs(yBase[s]-baseY) * 0.95;
    if(Math.abs(ring) > limit) ring = Math.sign(ring)*limit;

    ys[s] = yBase[s] + ring;
  }

  // Рендер
  ctx.beginPath();
  for(let s=0;s<steps;s++){
    if(s===0) ctx.moveTo(xs[s], ys[s]); else ctx.lineTo(xs[s], ys[s]);
  }
  ctx.lineTo(width, height);
  ctx.lineTo(0, height);
  ctx.closePath();

  ctx.globalCompositeOperation='source-over';
  ctx.globalAlpha=0.10;
  ctx.fillStyle=color;
  ctx.fill();

  ctx.globalAlpha=0.92;
  ctx.strokeStyle=color;
  ctx.lineWidth=thickness * cfg.strokeThinK;
  ctx.lineJoin=cfg.strokeJoin;
  ctx.miterLimit=22;
  ctx.lineCap=cfg.strokeCap;
  ctx.stroke();

  ctx.globalAlpha=1.0;
}

function drawLayer(i, baseY, ampK, rippleK, thickness, xDrift, parallax){
  if(STYLE==='rock'){
    drawLayerRock(i, baseY, ampK, rippleK, thickness, xDrift, parallax);
  }else{
    drawLayerPop(i, baseY, ampK, rippleK, thickness, xDrift, parallax);
  }
}


/* ========= Playback ========= */
async function setPlayback(paused){
  const btn=document.getElementById('btnPlayPause');
  if(paused){
    running=false;
    if(activeAudio){ try{ activeAudio.pause(); }catch{} }
    if(usingMic && AC){ try{ await AC.suspend(); }catch{} }
    btn.textContent='▶ Пуск';
    setStatus('Пауза');
  }else{
    running=true;
    if(activeAudio){ try{ await activeAudio.play(); setStatus('Играет файл'); }catch{} }
    if(usingMic && AC){ try{ await AC.resume(); setStatus('Микрофон активен'); }catch{} }
    btn.textContent='⏸ Пауза';
    tick();
  }
}

async function ensurePlayingAudio(){
  try{
    setupAudio();
    if(usingMic){
      if(AC.state!=='running') await AC.resume();
      setStatus('Микрофон активен');
    }else{
      if(AC.state!=='running') await AC.resume();
    }
  }catch(e){ console.warn(e); }
}

/* ========= UI helpers ========= */
function setStatus(t){
  const s=document.getElementById('status');
  if(s) s.textContent=t;
  updateHudSpace();
}

/* ========= Theme ========= */
function setTheme(name){
  const app=document.getElementById('app');
  app.setAttribute('data-theme', name);
  localStorage.setItem('organic_waves_theme', name);
  palette=PAL();
  updateHudSpace();
}
function generate(seedStr){
  const seed=hashStringToInt(seedStr);
  seedRand=mulberry32(seed);
  hue=Math.floor(seedRand()*360);
  NOISES = layers.map(()=>makeNoise1D(seedRand));
  palette=PAL();
}

/* ========= Swell ========= */
let swell=0;
function triggerSwell(amount){ swell = Math.min(1.0, swell + amount); }

/* ========= Main loop ========= */
let rafId=0;

function tick(){
  if(!running){ cancelAnimationFrame(rafId); return; }

  const env = analyze();
  const cfg = CFG();

  const baseFade = (document.getElementById('app').dataset.theme==='mono') ? 0.085 : 0.065;
  const fade = clamp(baseFade * (0.9 + env.sub*0.4 + env.bass*0.3) - swell*0.03, 0.02, 0.16);
  clearSoft(fade);

  const speed = 0.55 + env.mid*0.55 + env.centroid*0.35;
  tPhase += 0.006 * speed;

  // === Rock oscillator physics ===
  const dt = 0.016 * (0.9 + speed*0.4); // условный шаг времени
  if(STYLE==='rock'){
    for(let i=0;i<ROCK_OSC.length;i++){
      const osc = ROCK_OSC[i];
      const w0 = ROCK_CFG.w0[i] || ROCK_CFG.w0[ROCK_CFG.w0.length-1];
      const z  = ROCK_CFG.zeta[i] || ROCK_CFG.zeta[ROCK_CFG.zeta.length-1];
      // Возбуждение: flux + производная баса/суббаса
      const bassJerk = Math.max(0, env.bass - prevEnvVals.bass) + Math.max(0, env.sub - prevEnvVals.sub);
      const F = ROCK_CFG.drive.flux*env.flux + ROCK_CFG.drive.bassJerk*bassJerk + ROCK_CFG.drive.sub*env.sub;

      // y'' + 2ζω y' + ω² y = F(t)
      const a = F - 2*z*w0*osc.v - (w0*w0)*osc.y;
      osc.v += a * dt;
      osc.y += osc.v * dt;

      // мягкая стабилизация амплитуды (чтобы не разгонялось)
      const maxAmp = 40; // px в логике before-clamp, реальный вклад ограничивается дальше
      if(osc.y >  maxAmp) osc.y =  maxAmp;
      if(osc.y < -maxAmp) osc.y = -maxAmp;

      // фаза для пространственного паттерна
      osc.phase += dt * (0.8 + i*0.15 + env.centroid*0.5);
    }
    prevEnvVals = { bass: env.bass, sub: env.sub, flux: env.flux };
  }

  // Parallax одинаковый, но в rock ощущается резче
  LSTATE.forEach((ls, i)=>{
    const targetParallax = (i-1.5)*0.12 * (0.3 + env.centroid*0.9);
    ls.parallax = ls.parallax + (targetParallax - ls.parallax)*0.08;
  });

  // Движение слоёв
  LSTATE.forEach((ls, i)=>{
    const kick = cfg.kick(env);
    ls.xVel += ( cfg.xVelBase(i) + kick*cfg.xVelKick ) * (i%2===0 ? 1 : -1);
    ls.xVel *= 0.90;
    ls.xDrift += ls.xVel;
  });

  // Толщина линий
  LSTATE.forEach((ls)=>{
    const tTarget = cfg.thicknessTarget(env);
    ls.thickness = ls.thickness + (tTarget - ls.thickness)*0.12;
  });

  const ampK    = cfg.ampK(env); // одинаковая высота
  const rippleK = cfg.rippleK(env);

  if(env.flux > cfg.fluxThresh) triggerSwell((env.flux-cfg.fluxThresh)*cfg.swellK);
  swell *= 0.94;

  const baseY = H/2;
  drawLayer(3, baseY+90, ampK*0.9, rippleK*0.8, LSTATE[3].thickness+1.0, LSTATE[3].xDrift, LSTATE[3].parallax);
  drawLayer(2, baseY+30, ampK*0.8, rippleK*0.9, LSTATE[2].thickness+0.7, LSTATE[2].xDrift, LSTATE[2].parallax);
  drawLayer(1, baseY-10, ampK*0.7, rippleK*1.0, LSTATE[1].thickness+0.5, LSTATE[1].xDrift, LSTATE[1].parallax);
  drawLayer(0, baseY-40, ampK*0.6, rippleK*1.1, LSTATE[0].thickness+0.3, LSTATE[0].xDrift, LSTATE[0].parallax);

  rafId=requestAnimationFrame(tick);
}


/* ========= Recording (Canvas + Audio, with auto-stop) ========= */
let canvasStream=null;
let recorder=null, recChunks=[], recActive=false;

function getSupportedMime(){
  const options=[
    'video/webm;codecs=vp9,opus',
    'video/webm;codecs=vp8,opus',
    'video/webm;codecs=vp9',
    'video/webm;codecs=vp8',
    'video/webm'
  ];
  for (const m of options){ if (MediaRecorder.isTypeSupported(m)) return m; }
  return '';
}

function getCombinedStream(){
  if (!canvasStream) canvasStream = canvas.captureStream(30); // видео 30 FPS
  const audioStream = destNode?.stream;                       // аудио из AC
  const tracks = [
    ...canvasStream.getTracks(),
    ...(audioStream ? audioStream.getTracks() : [])
  ];
  return new MediaStream(tracks);
}

function waitForMetadata(media){
  if (media.readyState >= 1) return Promise.resolve();
  return new Promise(res => media.addEventListener('loadedmetadata', res, { once:true }));
}

function armAutoStopFromMedia(media){
  if (autoStopCleanup) { try{ autoStopCleanup(); }catch{} autoStopCleanup=null; }
  const onEnded = () => { stopRecording(); };
  const onEmptied = () => { stopRecording(); };
  media.addEventListener('ended', onEnded,   { once:true });
  media.addEventListener('emptied', onEmptied, { once:true });
  autoStopCleanup = () => {
    media.removeEventListener('ended', onEnded);
    media.removeEventListener('emptied', onEmptied);
  };
}

function clearAutoStopGuards(){
  if (recTimeoutId){ clearTimeout(recTimeoutId); recTimeoutId=null; }
  if (autoStopCleanup){ try{ autoStopCleanup(); }catch{} autoStopCleanup=null; }
}

async function startRecording(){
  await ensurePlayingAudio();
  if(!destNode){ setupAudio(); }

  const mime = getSupportedMime();
  const stream = getCombinedStream();

  if (activeAudio instanceof HTMLMediaElement){
    try{ await waitForMetadata(activeAudio); }catch{}
    activeAudio.loop = false;
    activeAudio.currentTime = 0;
    armAutoStopFromMedia(activeAudio);

    if (isFinite(activeAudio.duration) && activeAudio.duration > 0){
      const remainingMs = Math.max(0, (activeAudio.duration - activeAudio.currentTime) * 1000);
      recTimeoutId = setTimeout(()=> stopRecording(), remainingMs + 350);
    }
  }

  recChunks=[];
  try{
    recorder = new MediaRecorder(stream, mime ? { mimeType: mime } : {});
  }catch(e){
    setStatus('MediaRecorder не поддерживается');
    console.error(e);
    clearAutoStopGuards();
    return;
  }

  recorder.ondataavailable = e=>{ if(e.data.size>0) recChunks.push(e.data); };
  recorder.onstop = ()=>{
    const type = mime || 'video/webm';
    const blob = new Blob(recChunks, { type });
    const url = URL.createObjectURL(blob);
    const a = document.createElement('a');
    a.href = url;
    a.download = `organic_waves_${new Date().toISOString().replace(/[:.]/g,'-')}.webm`;
    document.body.appendChild(a); a.click(); a.remove();
    URL.revokeObjectURL(url);
    if (activeAudio instanceof HTMLMediaElement){ activeAudio.loop = true; }
    setStatus('Запись сохранена');
  };

  recorder.start();
  if (activeAudio instanceof HTMLMediaElement){
    try{ await activeAudio.play(); }catch(e){ console.warn(e); }
  }

  recActive=true;
  document.getElementById('btnRec').textContent='■ Стоп';
  setStatus('Запись идёт…');
}

function stopRecording(){
  clearAutoStopGuards();
  if (recorder && recActive){
    recActive=false;
    try{ recorder.stop(); }catch(e){ console.warn(e); }
    document.getElementById('btnRec').textContent='⏺ Запись';
    setStatus('Запись сохраняется…');
  }
}

/* === HUD spacer === */
function updateHudSpace(){
  const hud = document.querySelector('.hud');
  const h = hud ? hud.offsetHeight : 0;
  document.documentElement.style.setProperty('--hud-space', (h + 40) + 'px');
}

/* ========= Init ========= */
(function(){
  canvas=document.getElementById('cnv');
  ctx=canvas.getContext('2d', { alpha:false });
  resize(); window.addEventListener('resize', resize);

  const savedTheme=localStorage.getItem('organic_waves_theme');
  if(savedTheme){
    document.querySelector(`input[name="theme"][value="${savedTheme}"]`)?.setAttribute('checked','checked');
    setTheme(savedTheme);
  } else setTheme('calm');

  const savedStyle = localStorage.getItem('ow_style');
  STYLE = (savedStyle==='rock'||savedStyle==='pop') ? savedStyle : 'pop';
  const styleInput = document.querySelector(`input[name="style"][value="${STYLE}"]`);
  if(styleInput) styleInput.checked = true;

  document.querySelectorAll('input[name="theme"]').forEach(r=>{
    r.addEventListener('change', e=> setTheme(e.target.value));
  });
  document.querySelectorAll('input[name="style"]').forEach(r=>{
    r.addEventListener('change', e=>{
      STYLE = e.target.value;
      localStorage.setItem('ow_style', STYLE);
      setStatus(STYLE==='rock' ? 'Стиль: Rock' : 'Стиль: Pop');
    });
  });

  const seedFromHash = () => {
    const h=location.hash.replace(/^#/,'').trim();
    return h && h.length>0 ? h : Math.random().toString(36).slice(2,10);
  };
  const s=seedFromHash(); location.hash=s; generate(s);

  ctx.fillStyle=PAL().bg; ctx.fillRect(0,0,W,H);

  document.getElementById('fileInput').addEventListener('change', e=>{
    const f=e.target.files[0]; if(!f) return; useFile(f);
  });
  document.getElementById('btnMic').addEventListener('click', ()=> useMic());
  document.getElementById('btnPlayPause').addEventListener('click', async ()=>{
    await setPlayback(running);
  });
  document.getElementById('btnRec').addEventListener('click', async ()=>{
    if(!recActive){ await startRecording(); }
    else{ stopRecording(); }
  });

  document.addEventListener('keydown', async (e)=>{
    if (e.target && (e.target.tagName==='INPUT' || e.target.tagName==='TEXTAREA' || e.isComposing)) return;
    if (e.ctrlKey || e.metaKey || e.altKey) return;
    if (e.code==='Space'){ e.preventDefault(); await setPlayback(running); }
    if (e.code==='KeyR'){ e.preventDefault(); if(!recActive) await startRecording(); else stopRecording(); }
  });

  window.addEventListener('hashchange', ()=>{ const s=seedFromHash(); generate(s); });

  running=true; tick();
})();
