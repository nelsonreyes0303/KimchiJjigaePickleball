/* Queue checks: randomized open plays run through the real app code, with the club's rules checked after every
   action. Loaded into the app page by dev/queue-check.html. Nothing is saved: the app's save is switched off and
   its state is put back afterwards.
   window.__fuzz(nights, seed, opts) -> { nights, actions, failures:[{rule, detail, trail}], stats, rest:[minutes] }
   opts: players, courts, mix:[novice, lowint, highint] weights, calm (arrivals and games only), drags:false, undo:false */
window.__fuzz=function(nNights, seed0, opts){
  const RESTM=(typeof REST_MIN==="number")?REST_MIN:3, CF=(typeof courtFallback==="function")?courtFallback:(()=>null), RT=(typeof restTick==="function")?restTick:(()=>{}), LGE=(typeof lastGameEnds==="function")?lastGameEnds:(()=>{ const m={}; (state.log||[]).forEach(g=>[...g.w,...g.l].forEach(x=>{ m[x.id]=Math.max(m[x.id]||0,g.t||0); })); return m; });
  opts=opts||{};
  const LV=["novice","lowint","highint"], MIX=[[1,1,1],[1,1,3],[3,1,1],[1,3,1],[2,0.4,2],[1,0.3,3],[0,1,1],[1,1,0]];
  const out={nights:0,actions:0,failures:[],stats:{starts:0,exceptionStarts:0,restBreaks:0,idleMinutes:0,maxWait:0,drags:0,ticks:0,undo:0,setups:0}};
  const realNow=Date.now;
  const sv={save:window.save,toast:window.toast,confirm:window.confirm}, wasAdmin=sessionStorage.getItem(ADMIN_OK);
  const keepState=state, keepUndo=undoStack.slice();
  const hasAudit=typeof auditPending!=="undefined", keepPend=hasAudit?auditPending.slice():null, keepOut=hasAudit?auditOut.slice():null;   // simulated actions must never reach the real audit
  window.save=()=>{}; window.toast=()=>{}; window.confirm=()=>true;
  sessionStorage.setItem(ADMIN_OK,"1");
  let trail=[]; const fail=(night,t,rule,detail)=>{ if(out.failures.length<40) out.failures.push({night,min:Math.round(t),rule,detail,trail:out.failures.some(f=>f.night===night)?undefined:trail.slice(-10)}); };
  try{
  for(let night=0; night<nNights; night++){
    let r=(seed0+night*7919)>>>0; const rnd=()=>{r=r+0x6D2B79F5|0;let t=Math.imul(r^r>>>15,1|r);t=t+Math.imul(t^t>>>7,61|t)^t;return((t^t>>>14)>>>0)/4294967296;};
    const pick=a=>a[Math.floor(rnd()*a.length)];
    const t0=1800000000000; let now=t0; Date.now=()=>now; const minute=()=>(now-t0)/60000;
    const nP=opts.players||(4+Math.floor(rnd()*33)), nC=opts.courts||(1+Math.floor(rnd()*4));
    const mix=opts.mix||pick(MIX); const wsum=mix.reduce((a,b)=>a+b,0);
    const lvl=()=>{ let x=rnd()*wsum; for(let i=0;i<3;i++){ if((x-=mix[i])<0) return LV[i]; } return LV[2]; };
    state=fresh(); state.courts=[]; for(let i=0;i<nC;i++) state.courts.push({id:"c"+(i+1),seats:[null,null,null,null],started:null});
    for(let i=1;i<=nP;i++) state.players["p"+i]={id:"p"+i,name:"N"+night+"-"+i,level:lvl(),in:false,openMix:true,qkey:0,games:0,wins:0,losses:0,pg:0};
    state.seq=nP+1; state.queue=[]; state.session={active:true,startedAt:now,name:"fuzz",id:now};
    try{ undoStack.length=0; }catch(e){} trail=[];
    const early=opts.calm ? Math.max(4,Math.floor(nP*0.8)) : Math.max(4,Math.floor(nP*(0.3+rnd()*0.6)));
    const arrivals=Object.keys(state.players).map((id,i)=>({id,t:t0+(i<early?Math.floor(rnd()*3*60000):Math.floor(rnd()*(opts.calm?25:70)*60000))})).sort((a,b)=>a.t-b.t);
    const ends={}, pendingStart={}, adminMade=new Set(), levelChanged=new Set(); let freeSince={};
    const pinKeys=()=>(state.frontPinned||[]).map(fourKey);
    const lastEnd=LGE;
    const restedOK=(id,e)=>!e[id] || now-e[id]>=RESTM*60000;
    // every 4-player combination of rested, queued players that the level and pair rules allow
    const legalRestedGroupExists=()=>{
      const e=lastEnd(), lset=new Set(state.qlocked||[]);
      const ids=state.queue.filter(id=>(restedOK(id,e)||lset.has(id)) && !P(id).grp);
      const n=ids.length;
      for(let a=0;a<n;a++)for(let b=a+1;b<n;b++)for(let c=b+1;c<n;c++)for(let d=c+1;d<n;d++){
        const g=[ids[a],ids[b],ids[c],ids[d]];
        if(!levelsOK(g)) continue;
        if(g.some(x=>{ const pt=P(x).partner; return pt && !g.includes(pt); })) continue;
        return g;
      }
      return null;
    };
    const anyLegalGroupExists=()=>{ const ids=state.queue.filter(id=>!P(id).grp), n=ids.length;
      for(let a=0;a<n;a++)for(let b=a+1;b<n;b++)for(let c=b+1;c<n;c++)for(let d=c+1;d<n;d++){ const g=[ids[a],ids[b],ids[c],ids[d]];
        if(levelsOK(g) && !g.some(x=>{ const pt=P(x).partner; return pt && !g.includes(pt); })) return true; } return false; };
    const check=(label)=>{
      out.actions++; if(label!=="clock") { trail.push(Math.round(minute()*10)/10+" "+label+" | courts "+state.courts.map(c=>c.seats.map(x=>x?nm(x).replace(/^Nd+-/,""):"-").join(",")).join(" ; ")+" | queue "+state.queue.map(x=>P(x)?nm(x).replace(/^Nd+-/,""):"??"+x).join(",")); if(trail.length>30) trail.shift(); }
      const e=lastEnd(), man=manualActive(), gq=queueGroups(), lset=new Set(state.qlocked||[]);
      // consistency: nobody lost or doubled
      const seen={}; state.queue.forEach(id=>{ seen[id]=(seen[id]||0)+1; }); state.courts.forEach(c=>c.seats.forEach(id=>{ if(id) seen[id]=(seen[id]||0)+1; }));
      Object.entries(seen).forEach(([id,k])=>{ if(k>1) fail(night,minute(),"player in two places",nm(id)+" after "+label); });
      Object.values(state.players).forEach(p=>{ if(p.in && p.level && !seen[p.id]) fail(night,minute(),"checked-in player missing",p.name+" after "+label); });
      gq.groups.forEach((g,i)=>{
        if(g.length!==4 || new Set(g).size!==4) fail(night,minute(),"group not four players",label);
        if(g.some(x=>!state.queue.includes(x))) fail(night,minute(),"group has someone not in line",label);
        if(!man && !levelsOK(g) && !g.every(x=>lset.has(x)) && !adminMade.has(fourKey(g)) && !(P(g[0]).grp && g.every(x=>P(x).grp===P(g[0]).grp)) && !g.some(x=>levelChanged.has(x))) fail(night,minute(),"illegal levels",g.map(x=>nm(x)+"/"+lvlAbbr(P(x).level)).join(" ")+" after "+label);
      });
      // the rest rule on Next up / Group 2
      if(!man){
        gq.groups.slice(0,Math.max(1,pinnedGroups())).forEach((g,i)=>{
          if(adminMade.has(fourKey(g))) return;
          const fresh=g.filter(x=>!lset.has(x) && !restedOK(x,e));
          if(fresh.length) fail(night,minute(),"just-off player in "+(i?"Group 2":"Next up"),fresh.map(x=>nm(x)+" rested "+((now-e[x])/60000).toFixed(1)+"m").join(", ")+" after "+label);
        });
      }
      const w=Math.max(0,...state.queue.map(id=>(now-waitSince(id))/60000)); if(w>out.stats.maxWait){ out.stats.maxWait=w; const id=state.queue.reduce((a,b)=>waitSince(a)<=waitSince(b)?a:b); const p=P(id); out.longest=p.name+" "+lvlAbbr(p.level)+(p.partner?" pair with "+nm(p.partner)+"/"+lvlAbbr(P(p.partner).level)+(onCourt(p.partner)?" (on court)":state.queue.includes(p.partner)?"":" (partner not in line)"):"")+(p.grp?" set-up/play-again group":"")+" · queue levels "+state.queue.map(x=>lvlAbbr(P(x).level)).join("")+" · "+(manualActive()?"after a drag":""); }
    };
    const stable=(fn,label,allowLeave)=>{          // fixed groups must survive this action
      const before=pinKeys(), man0=manualActive(); fn(); const after=pinKeys();
      before.forEach(k=>{ if(k===allowLeave) return; if(!after.includes(k) && !man0) fail(night,minute(),"fixed group changed by "+label,k.split("|").map(nm).join("/")+" -> "+after.map(a=>a.split("|").map(nm).join("/")).join(" | ")); });
      check(label);
    };
    const tick=()=>{ RT(); out.stats.ticks++; };
    const tryStart=(c)=>{
      const gq=queueGroups(); const g=gq.groups[0]||CF(gq); if(!g) return false;
      const e=lastEnd(), man=manualActive(), lset=new Set(state.qlocked||[]);
      const fresh=g.filter(x=>!lset.has(x) && !restedOK(x,e));
      const fromFallback=!gq.groups[0];
      if(fresh.length && !man && !adminMade.has(fourKey(g))){
        const alt=legalRestedGroupExists();
        if(alt) fail(night,minute(),"just-off player sent on court though rested players could play",fresh.map(nm).join(", ")+" · rested option "+alt.map(nm).join("/"));
        else { out.stats.exceptionStarts++; if(!fromFallback) fail(night,minute(),"just-off player came from Next up, not the empty-court exception",fresh.map(nm).join(", ")); }
      }
      const key=fourKey(g);
      if(!man && !levelsOK(g) && !adminMade.has(key) && !g.every(x=>lset.has(x)) && !(P(g[0]).grp && g.every(x=>P(x).grp===P(g[0]).grp)) && !g.some(x=>levelChanged.has(x))) fail(night,minute(),"illegal group sent on court",g.map(x=>nm(x)+"/"+lvlAbbr(P(x).level)).join(" ")+(fromFallback?" (empty-court exception)":" (Next up)"));
      stable(()=>startCourt(c),"start",gq.groups[0]?fourKey(gq.groups[0]):null);
      if(!c.seats.every(Boolean)) { fail(night,minute(),"start did nothing",key); return false; }
      out.stats.starts++; { const e2=lastEnd(); c.seats.forEach(x=>{ if(e2[x]){ const m=(now-e2[x])/60000; out.rest=out.rest||[]; out.rest.push(m); } }); } ends[c.id]=now+(6+rnd()*10)*60000; delete freeSince[c.id]; return true;
    };
    let ai=0, guard=0;
    while(minute()<240 && guard++<4000){
      // next event: an arrival, a game end, a pending admin tap on Start, or a 15-second look at the screen
      const busy=state.courts.filter(c=>c.seats.every(Boolean));
      const tEnd=Math.min(...busy.map(c=>ends[c.id]),Infinity);
      const tArr=ai<arrivals.length?arrivals[ai].t:Infinity;
      const tStart=Math.min(...Object.values(pendingStart),Infinity);
      const t=Math.min(tEnd,tArr,tStart,now+15000);
      now=Math.max(now,t);
      if(t===tArr){ const id=arrivals[ai++].id; stable(()=>checkIn(id),"check-in"); }
      else if(t===tEnd){ const c=busy.find(c=>ends[c.id]===tEnd);
        if(rnd()<0.08) stable(()=>toggleAgain(c),"play again on");
        stable(()=>finishGame(c, rnd()<.5?"A":"B", rnd()<.7?{ws:11,ls:Math.floor(rnd()*10)}:null),"picking a winner");
        pendingStart[c.id]=now+Math.floor(rnd()*rnd()*120000); freeSince[c.id]=now; }
      else if(t===tStart){ const id=Object.keys(pendingStart).find(k=>pendingStart[k]===tStart); delete pendingStart[id]; const c=state.courts.find(x=>x.id===id); if(!c.seats.some(Boolean) && !tryStart(c)) pendingStart[id]=now+30000; }
      else {
        tick();
        const before=pinKeys(); check("clock");
        // random admin actions, a few times an hour each
        const x=opts.calm ? (rnd()<0.05?0.055:1) : rnd();   /* calm: only the odd +2 min */
        const waiting=state.queue.slice();
        if(x<0.012 && waiting.length){ const id=pick(waiting); checkOut(id); check("check-out");   /* may break a group, so not a stability check */ }
        else if(x<0.02){ const out_=Object.values(state.players).filter(p=>!p.in&&p.level&&ai>=arrivals.length); if(out_.length){ const id=pick(out_).id; stable(()=>checkIn(id),"re-check-in"); } }
        else if(x<0.03 && waiting.length>=2){ const a=pick(waiting), b=pick(waiting); if(a!==b && !onCourt(a)&&!onCourt(b)){ selPair=null; stable(()=>{ pairToggle(a); pairToggle(b); },"pairing"); } }
        else if(x<0.04 && opts.drags!==false && waiting.length>=2){ const a=pick(waiting), b=pick(waiting); if(a!==b){ out.stats.drags++; doSwap({type:"queue",id:a},{type:"queue",id:b}); commit(); pinKeys().forEach(k=>adminMade.add(k)); check("drag"); } }
        else if(x<0.05){ const g=queueGroups().groups; if(g.length>2){ const gg=pick(g.slice(2)); toggleGroupLock(gg); adminMade.add(fourKey(gg)); check("lock a group"); } }
        else if(x<0.06){ stable(()=>skipTime(),"+2 min"); tick(); check("+2 min tick"); }
        else if(x<0.065 && waiting.length){ const id=pick(waiting); levelChanged.add(id); setLevel(id, pick(LV)); check("level change"); }
        else if(x<0.07 && undoStack.length && opts.undo!==false){ out.stats.undo++; undo(); check("undo"); }
        else if(x<0.075 && waiting.length>=6){ setupPick=[]; const pool=waiting.slice().sort(()=>rnd()-.5); for(const id of pool){ if(setupPick.length<4 && !P(id).partner && levelsOK(setupPick.concat([id]))) setupPick.push(id); }
          if(setupPick.length===4){ out.stats.setups++; confirmSetup(); pinKeys().forEach(k=>adminMade.add(k)); check("set up game"); } }
        // a free court with nothing pending: start if anything can play, and watch for idle courts
        state.courts.forEach(c=>{ if(c.seats.some(Boolean) || pendingStart[c.id]) return;
          if(!tryStart(c)){ freeSince[c.id]=freeSince[c.id]||now;
            if(now-freeSince[c.id]>=2*60000 && anyLegalGroupExists() && !manualActive()){ out.stats.idleMinutes+=0.25; if(now-freeSince[c.id]<2*60000+15000) fail(night,minute(),"court idle 2 min while a legal game exists",c.id+" · queue "+state.queue.map(id=>nm(id)+"/"+lvlAbbr(P(id).level)).join(" ")); } } });
      }
    }
    out.nights++;
  }
  } catch(e){ out.failures.push({rule:"ERROR",detail:e.message+" "+(e.stack||"").split("\n").slice(1,3).join(" ")}); }
  finally{ Date.now=realNow; Object.assign(window,sv); state=keepState; undoStack.length=0; keepUndo.forEach(x=>undoStack.push(x)); if(wasAdmin===null) sessionStorage.removeItem(ADMIN_OK); if(hasAudit){ auditPending=keepPend; auditOut=keepOut; } }
  out.stats.maxWait=Math.round(out.stats.maxWait);
  return out;
};


/* The Oct 25 case, with placeholder names: three courts, Next up held (three High Int + a Low Int), and only
   two High Ints and two Novices waiting, which cannot make a legal group. A game of three High Ints and a Low Int
   ends. The four who just finished must not fill Group 2; when six more players check in a minute later, Group 2
   forms from them. Returns a list of "PASS …" / "FAIL …" lines. */
window.__qcOct25=function(){
  const R=[], realNow=Date.now, keep=state, sv={save:window.save,toast:window.toast}, wasAdmin=sessionStorage.getItem(ADMIN_OK);
  const hasAudit=typeof auditPending!=="undefined", keepPend=hasAudit?auditPending.slice():null, keepOut=hasAudit?auditOut.slice():null;
  const ok=(c,t)=>R.push((c?"PASS ":"FAIL ")+t);
  let now=1800000000000; Date.now=()=>now; window.save=()=>{}; window.toast=()=>{}; sessionStorage.setItem(ADMIN_OK,"1");
  try{
    const L={H:"highint",L:"lowint",N:"novice"}, add=(id,l)=>{ state.players[id]={id,name:id,level:L[l],in:true,openMix:true,qkey:0,games:0,wins:0,losses:0,pg:0,waitSince:now-10*60000,checkedInAt:now-12*60000}; };
    state=fresh(); state.courts=[1,2,3].map(i=>({id:"c"+i,seats:[null,null,null,null],started:null}));
    ["NextH1:H","NextH2:H","NextH3:H","NextL1:L","WaitH1:H","WaitH2:H","WaitN1:N","WaitN2:N","OffH1:H","OffL1:L","OffH2:H","OffH3:H",
     "Court1a:H","Court1b:L","Court1c:L","Court1d:L","Court3a:N","Court3b:N","Court3c:L","Court3d:N"].forEach(x=>{ const [id,l]=x.split(":"); add(id,l); });
    ["LateN1:N","LateN2:N","LateL1:L","LateL2:L","LateH1:H","LateH2:H"].forEach(x=>{ const [id,l]=x.split(":"); add(id,l); state.players[id].in=false; });
    state.courts[0].seats=["Court1a","Court1b","Court1c","Court1d"]; state.courts[2].seats=["Court3a","Court3b","Court3c","Court3d"];
    state.courts[1].seats=["OffH1","OffL1","OffH2","OffH3"]; state.courts.forEach(c=>{ c.started=now-10*60000; });
    state.queue=["NextH1","NextH2","NextH3","NextL1","WaitH1","WaitH2","WaitN1","WaitN2"];
    state.session={active:true,startedAt:now-15*60000,name:"oct25",id:now}; state.frontPinned=[["NextH1","NextH2","NextH3","NextL1"]];
    commit();
    const off=["OffH1","OffL1","OffH2","OffH3"], inFixed=()=>queueGroups().groups.slice(0,2).flat();
    finishGame(state.courts[1],"A",{ws:11,ls:7});
    ok(!inFixed().some(x=>off.includes(x)), "winner picked: the four who just finished are not in Next up or Group 2");
    ok(queueGroups().resting.length===4, "winner picked: Group 2 shows as forming, the four are resting");
    now+=20000; startCourt(state.courts[1]);
    ok(state.courts[1].seats.join()==="NextH1,NextH2,NextH3,NextL1", "Start game: the held Next up goes on court");
    ok(!inFixed().some(x=>off.includes(x)), "after the start: still nobody who just finished in Next up or Group 2");
    now+=60000; ["LateN1","LateN2","LateL1","LateL2","LateH1","LateH2"].forEach(id=>checkIn(id));
    const g=queueGroups().groups;
    ok(g.length>=2 && !inFixed().some(x=>off.includes(x)), "six check in: Next up and Group 2 form from rested players ("+g.slice(0,2).map(x=>x.join("/")).join(" | ")+")");
    ok((state.frontPinned||[]).length===2, "six check in: both groups are fixed");
    now+=3*60000; restTick();
    ok(true, "after 3 minutes the four who finished can join a later group ("+(queueGroups().groups.findIndex(x=>x.some(y=>off.includes(y)))+1||"none yet")+")");
  }catch(e){ R.push("FAIL error: "+e.message); }
  finally{ Date.now=realNow; Object.assign(window,sv); state=keep; if(wasAdmin===null) sessionStorage.removeItem(ADMIN_OK); if(hasAudit){ auditPending=keepPend; auditOut=keepOut; } }
  return R;
};
