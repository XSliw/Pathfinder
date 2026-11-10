/* Pathfinder v4: one Leaflet instance, explicit user events, no render->value loop. */
(() => {
  'use strict';
  let parentOrigin = '*', args = null, map = null, session = null;
  const client = globalThis.crypto?.randomUUID?.() || ('c' + Date.now() + Math.random().toString(36).slice(2));
  let sequence = 0, pending = null, pendingTimer = null, noticeTimer = null;
  let commandId = null, viewRequest = 0, mode = 'Осмотр', frameHeight = 0;
  let tileSignature = '', tiles = [], retryNumber = 0, revisions = {};
  const groups = {}, root = document.getElementById('map');
  const status = document.getElementById('status'), statusText = document.getElementById('status-text');
  let resizeTimer, storageTimer;
  function post(type, extra = {}) {
    window.parent.postMessage({isStreamlitMessage:true, type, ...extra}, parentOrigin);
  }
  function notice(text, error = false, persistent = false) {
    clearTimeout(noticeTimer); statusText.textContent = text;
    status.dataset.kind = error ? 'error' : 'info'; status.hidden = false;
    if (!persistent) noticeTimer = setTimeout(() => { status.hidden = true; }, 6500);
  }
  document.getElementById('dismiss').onclick = () => { status.hidden = true; };
  document.getElementById('reload').onclick = () => window.location.reload();
  function sizeFrame() {
    // Height is determined by width only: parent iframe height cannot feed back into it.
    const height = window.innerWidth < 600 ? 460 : 560;
    if (height !== frameHeight) { frameHeight = height; post('streamlit:setFrameHeight', {height}); }
    clearTimeout(resizeTimer);
    resizeTimer = setTimeout(() => {
      if (map && root.getBoundingClientRect().width > 0) map.invalidateSize({pan:false, debounceMoveend:true});
    }, 120);
  }
  function viewport() {
    const c = map.getCenter(), b = map.getBounds();
    return {center:{lat:c.lat,lng:c.lng}, zoom:map.getZoom(),
      bounds:{_southWest:{lat:b.getSouth(),lng:b.getWest()},_northEast:{lat:b.getNorth(),lng:b.getEast()}}};
  }
  function storageKey() { return 'pathfinder-v4-view:' + session; }
  function saveView() {
    clearTimeout(storageTimer);
    storageTimer = setTimeout(() => {
      try { sessionStorage.setItem(storageKey(), JSON.stringify(viewport())); } catch (_) { /* storage can be disabled */ }
    }, 180);
  }
  function readView() {
    try {
      const v = JSON.parse(sessionStorage.getItem(storageKey()));
      if (v && Number.isFinite(v.center.lat) && Number.isFinite(v.center.lng) && Number.isFinite(v.zoom)) return v;
    } catch (_) { /* no cached view */ }
    return null;
  }
  function submit(action, details = {}) {
    if (!args || !map || pending || args.disabled) return false;
    const event = {session, client, seq:++sequence, action, ...details, viewport:viewport()};
    pending = event.seq;
    if (action === 'point') notice('Сохраняем точку…', false, true);
    post('streamlit:setComponentValue', {value:event, dataType:'json'});
    clearTimeout(pendingTimer);
    pendingTimer = setTimeout(() => {
      // Never replay an unacknowledged tap automatically. A delayed response may still arrive.
      if (pending !== null) notice('Сервер не ответил. Дождитесь соединения или обновите страницу. Точка не отправляется повторно.', true, true);
    }, 12000);
    return true;
  }
  function labelNode(text) { const el = document.createElement('span'); el.textContent = String(text || ''); return el; }
  function decorate(control) {
    L.DomEvent.disableClickPropagation(control); L.DomEvent.disableScrollPropagation(control);
    return control;
  }
  function controls() {
    const control = L.control({position:'topright'});
    control.onAdd = () => {
      const box = decorate(L.DomUtil.create('div','pf-control'));
      const items = [
        ['Во весь экран','<path d="M8 3H3v5m13-5h5v5M3 16v5h5m13-5v5h-5"/>', () => {
          const p = document.documentElement;
          if (!document.fullscreenElement) {
            if (p.requestFullscreen) p.requestFullscreen().catch(() => notice('Полноэкранный режим недоступен в этом браузере.',true));
            else notice('Полноэкранный режим недоступен в этом браузере.',true);
          } else if (document.exitFullscreen) document.exitFullscreen().catch(() => {});
        }],
        ['Моё местоположение','<circle cx="12" cy="12" r="6"/><circle cx="12" cy="12" r="2"/><path d="M12 2v3m0 14v3M2 12h3m14 0h3"/>', () => {
          if (!navigator.geolocation) return notice('Браузер не поддерживает геолокацию.',true);
          navigator.geolocation.getCurrentPosition(pos => {
            const ll = [pos.coords.latitude,pos.coords.longitude];
            if (!groups.location) groups.location = L.layerGroup().addTo(map);
            groups.location.clearLayers();
            L.circle(ll,{radius:Math.min(pos.coords.accuracy,2000),color:'#1768b8',weight:1,fillOpacity:.1}).addTo(groups.location);
            L.circleMarker(ll,{radius:6,color:'#fff',weight:2,fillColor:'#1768b8',fillOpacity:1}).addTo(groups.location);
            map.setView(ll, Math.max(14,map.getZoom()),{animate:false});
          }, () => notice('Местоположение недоступно. Проверьте разрешение браузера.',true),
          {enableHighAccuracy:true, timeout:12000, maximumAge:30000});
        }],
        ['Повторить загрузку слоёв','<path d="M20 7a9 9 0 1 0 1 8M20 2v6h-6"/>', () => { retryNumber++; syncTiles(args.tiles); }]
      ];
      for (const [title,svg,fn] of items) {
        const btn = document.createElement('button'); btn.type='button'; btn.title=title; btn.setAttribute('aria-label',title);
        btn.innerHTML='<svg viewBox="0 0 24 24" aria-hidden="true">'+svg+'</svg>'; btn.onclick=fn; box.appendChild(btn);
      }
      return box;
    }; control.addTo(map);
  }
  function init(data) {
    const v = readView();
    map = L.map(root, {center:v ? [v.center.lat,v.center.lng] : data.center, zoom:v ? v.zoom : data.zoom,
      maxZoom:20, preferCanvas:true, fadeAnimation:false, zoomAnimation:false, markerZoomAnimation:false,
      attributionControl:true, bounceAtZoomLimits:false});
    map.attributionControl.setPrefix(false);
    for (const [name,z] of [['paper',240],['heat',360],['terrain',430],['route',610]]) map.createPane(name).style.zIndex=z;
    for (const key of ['terrain','routes','points','warnings','nogos','km']) groups[key]=L.layerGroup().addTo(map);
    L.control.scale({imperial:false}).addTo(map); controls();
    map.on('click', e => {
      if (mode !== 'Осмотр') submit('point',{lat:e.latlng.lat,lng:e.latlng.lng,role:mode});
    });
    // View changes stay entirely inside the browser: zero Python messages on pan/zoom.
    map.on('moveend', saveView);
    clearTimeout(window.pfBootTimer);
    document.getElementById('boot').hidden=true;
    if (v && data.command.id === 0) commandId=0;
  }
  function syncTiles(specs) {
    const signature = JSON.stringify([specs,retryNumber]);
    if (signature === tileSignature) return;
    tileSignature=signature;
    tiles.forEach(layer => map.removeLayer(layer)); tiles=[];
    for (const spec of specs) {
      const layer = L.tileLayer(spec.url, {maxZoom:20, maxNativeZoom:spec.native,
        attribution:spec.attribution, opacity:spec.opacity ?? 1, tms:!!spec.tms, pane:spec.pane || 'tilePane',
        keepBuffer:4, updateWhenIdle:true, updateWhenZooming:false, crossOrigin:false});
      let ok=0, errors=0;
      layer.on('loading',()=>{ok=0;errors=0;});
      layer.on('tileload',()=>{ok++;}); layer.on('tileerror',()=>{errors++;});
      layer.on('load',()=>{
        if (!map.hasLayer(layer) || ok || errors<3) return;
        if (!spec.fallback) map.removeLayer(layer);
        notice(spec.fallback ? 'Карта недоступна. Проверьте интернет и повторите загрузку слоёв.' :
          spec.label+' недоступен. '+(spec.base ? 'Показана OSM.' : 'Слой отключён.')+' Повтор — кнопка со стрелкой.', true);
      });
      layer.addTo(map); tiles.push(layer);
    }
  }
  function updateGroup(name, data, paint) {
    const hash=JSON.stringify(data);
    if (revisions[name]===hash) return;
    revisions[name]=hash; groups[name].clearLayers(); paint(groups[name]);
  }
  function syncData(data) {
    syncTiles(data.tiles);
    updateGroup('terrain',data.features,g => {
      if (data.features.features.length) L.geoJSON(data.features,{pane:'terrain',style:f=>data.styles[f.properties.kind],
        onEachFeature:(f,l)=>l.bindTooltip(labelNode(f.properties.description),{sticky:false})}).addTo(g);
    });
    updateGroup('routes',data.lines,g=>data.lines.forEach(line=>line.strokes.forEach(([color,weight])=>
      L.polyline(line.coords,{pane:'route',color,weight,opacity:line.opacity ?? 1,
        dashArray:line.dash || null,smoothFactor:1.2,interactive:!!line.title})
        .bindTooltip(labelNode(line.title)).addTo(g))));
    updateGroup('points',data.points,g=>data.points.forEach(p=> {
      const node=document.createElement('div');node.className='pf-pin '+(p.label==='Б'?'finish':p.label==='А'?'':'via');node.textContent=p.label;
      const icon=L.divIcon({className:'',html:node.outerHTML,iconSize:[34,34],iconAnchor:[17,17]});
      L.marker(p.coords,{icon,keyboard:true}).bindTooltip(labelNode(p.title)).addTo(g);
    }));
    updateGroup('warnings',data.warnings,g=>data.warnings.forEach(w=> {
      const popup=document.createElement('div'), title=document.createElement('strong');title.textContent=w.name;
      popup.append(title,document.createElement('br'),document.createTextNode(w.detail));
      L.circleMarker([w.lat,w.lon],{radius:7,pane:'route',color:'#fff',weight:2,
        fillColor:w.info?'#1768b8':'#b8432c',fillOpacity:1}).bindTooltip(labelNode(w.name)).bindPopup(popup).addTo(g);
    }));
    updateGroup('nogos',data.nogos,g=>data.nogos.forEach(p=>L.circle([p[1],p[0]],{radius:150,pane:'route',color:'#dc2626',weight:2,fillOpacity:.12}).bindTooltip('Запрет обхода · 150 м').addTo(g)));
    updateGroup('km',data.km,g=>data.km.forEach(p=>L.circleMarker(p.coords,{radius:5,pane:'route',color:'#fff',weight:2,fillColor:'#203346',fillOpacity:1}).bindTooltip(labelNode(p.title)).addTo(g)));
  }
  function render(data) {
    if (!data || !data.session) return;
    if (typeof L === 'undefined') {
      document.getElementById('boot-text').textContent='Не удалось загрузить библиотеку карты. Проверьте интернет или доступ к CDN.';
      document.getElementById('reload').hidden=false;return;
    }
    if (session && session !== data.session) {
      map?.remove();map=null;pending=null;clearTimeout(pendingTimer);commandId=null;viewRequest=0;tileSignature='';revisions={};
    }
    session=data.session;args=data;mode=data.mode || 'Осмотр';
    if (pending !== null && (data.acks?.[client] || 0) >= pending) {
      pending=null;clearTimeout(pendingTimer);status.hidden=true;
    }
    if (!map) init(data);
    syncData(data);
    if (data.command.id !== commandId) {
      commandId=data.command.id;
      if (data.command.kind==='retry') {retryNumber++;syncTiles(data.tiles);}
      else if (data.command.fit && data.fit_bounds.length>1) map.fitBounds(data.fit_bounds,{padding:[32,32],animate:false});
      else if (data.command.fit && data.fit_bounds.length===1) map.setView(data.fit_bounds[0],data.zoom,{animate:false});
      else map.setView(data.center,data.zoom,{animate:false});
    }
    if (data.view_request > Math.max(viewRequest,data.view_completed || 0)) {
      if (submit('scan',{request:data.view_request})) viewRequest=data.view_request;
    }
    sizeFrame();
  }
  function onMessage(event) {
    if (event.source !== window.parent || event.data?.type !== 'streamlit:render') return;
    parentOrigin=event.origin && event.origin!=='null' ? event.origin : '*';
    try { render(event.data.args); }
    catch (err) { clearTimeout(window.pfBootTimer);document.getElementById('boot').hidden=true;console.error('Pathfinder map:',err);notice('Ошибка отображения карты. Обновите страницу.',true,true); }
  }
  window.addEventListener('message',onMessage);
  const observer=new ResizeObserver(sizeFrame); observer.observe(root);
  const onVisible=()=>{if(!document.hidden)sizeFrame();};
  document.addEventListener('visibilitychange',onVisible);
  window.addEventListener('resize',sizeFrame);
  window.addEventListener('orientationchange',sizeFrame);
  window.addEventListener('pagehide',()=>{
    observer.disconnect();clearTimeout(resizeTimer);clearTimeout(storageTimer);clearTimeout(pendingTimer);clearTimeout(noticeTimer);
    document.removeEventListener('visibilitychange',onVisible);window.removeEventListener('message',onMessage);
    window.removeEventListener('resize',sizeFrame);window.removeEventListener('orientationchange',sizeFrame);
    map?.remove();
  },{once:true});
  post('streamlit:componentReady',{apiVersion:1});sizeFrame();
})();
