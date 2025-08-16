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

  AENV.sub     = envFollow(AENV.sub,     norm(subB),   0.25, 0.08);
  AENV.bass    = envFollow(AENV.bass,    norm(bassB),  0.22, 0.10);
  AENV.lowmid  = envFollow(AENV.lowmid,  norm(lowmB),  0.18, 0.12);
  AENV.mid     = envFollow(AENV.mid,     norm(midB),   0.16, 0.12);
  AENV.highmid = envFollow(AENV.highmid, norm(highmB), 0.16, 0.14);
  AENV.treble  = envFollow(AENV.treble,  norm(trebB),  0.20, 0.16);

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

function drawLayer(i, baseY, ampK, rippleK, thickness, xDrift, parallax){
  const color=palette.waves[i%palette.waves.length] || '#fff';
  const width=W, height=H;
  const steps=96;
  const dx=width/(steps-1);

  const prevIdx = (i>0? i-1 : 0);
  const noiseMain = NOISES[i] || NOISES[0];
  const noiseRipple = NOISES[prevIdx] || NOISES[0];

  ctx.beginPath();
  for(let s=0;s<steps;s++){
    const x=s*dx + xDrift;
    const n=noiseMain(x, tPhase * (1+layers[i].speed*0.18) + parallax);
    const r=noiseRipple(x*1.18, tPhase*0.72 + i*0.3);
    const y=baseY +
      n * layers[i].amp * ampK +
      r * layers[i].amp * 0.35 * rippleK;
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
  ctx.lineWidth=thickness;
  ctx.lineJoin='round'; ctx.lineCap='round';
  ctx.stroke();

  ctx.globalAlpha=1.0;
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

  const baseFade = (document.getElementById('app').dataset.theme==='mono') ? 0.085 : 0.065;
  const fade = clamp(baseFade * (0.9 + env.sub*0.4 + env.bass*0.3) - swell*0.03, 0.02, 0.16);
  clearSoft(fade);

  const speed = 0.55 + env.mid*0.55 + env.centroid*0.35;
  tPhase += 0.006 * speed;

  LSTATE.forEach((ls, i)=>{
    const targetParallax = (i-1.5)*0.12 * (0.3 + env.centroid*0.9);
    ls.parallax = ls.parallax + (targetParallax - ls.parallax)*0.08;
  });

  LSTATE.forEach((ls, i)=>{
    const kick = env.sub*0.6 + env.bass*0.45 + env.flux*0.15;
    ls.xVel += ( (i+1)*0.02 + kick*0.05 ) * (i%2===0 ? 1 : -1);
    ls.xVel *= 0.90;
    ls.xDrift += ls.xVel;
  });

  LSTATE.forEach((ls)=>{
    const tTarget = 1.2 + env.lowmid*0.8 + env.mid*0.6;
    ls.thickness = ls.thickness + (tTarget - ls.thickness)*0.12;
  });

  const ampK    = 0.75 + env.bass*1.2 + env.rms*0.3;
  const rippleK = 0.35 + env.highmid*0.7 + env.treble*0.5;

  if(env.flux > 0.9) triggerSwell((env.flux-0.9)*0.12);
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
let recTimeoutId = null;
let autoStopCleanup = null;

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
  // Видео из canvas (30 FPS)
  if (!canvasStream) canvasStream = canvas.captureStream(30);
  // Аудио из AudioContext -> destNode.stream
  const audioStream = destNode?.stream;
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
  await ensurePlayingAudio();              // готовим аудиоконтекст/микрофон
  if(!destNode){ setupAudio(); }

  const mime = getSupportedMime();
  const stream = getCombinedStream();

  // Если источник — файл: стартуем СТРОГО тут, автостоп по окончанию
  if (activeAudio instanceof HTMLMediaElement){
    try{ await waitForMetadata(activeAudio); }catch{}
    activeAudio.loop = false;              // временно убираем луп
    activeAudio.currentTime = 0;           // пишем «с нуля»
    armAutoStopFromMedia(activeAudio);

    // страховка по длительности
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

  // Важно: сначала стартуем рекордер, затем play(), чтобы не потерять первые кадры/сэмплы
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

  const saved=localStorage.getItem('organic_waves_theme');
  if(saved){
    document.querySelector(`input[name="theme"][value="${saved}"]`)?.setAttribute('checked','checked');
    setTheme(saved);
  } else setTheme('calm');

  document.querySelectorAll('input[name="theme"]').forEach(r=>{
    r.addEventListener('change', e=> setTheme(e.target.value));
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
