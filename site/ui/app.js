(() => {
 'use strict';
 const data = window.CHOMP_CATALOG || {results: []};
 const rows = Array.isArray(data.results) ? data.results : [];
 const $ = id => document.getElementById(id);
 const labels = {'lean-verified':'Lean verified','paper-reviewed':'Paper reviewed','paper-proof':'Paper proof','withheld':'Withheld: proof gap','conditional':'Conditional','open':'Open','refuted':'Refuted','source-collected':'Source collected','formal':'Lean verified','verified':'Lean verified'};
 const state = {kind:'main', status:'all', topic:'all', query:'', sort:'relevance', page:1};
 const PAGE = 20;
 const esc = v => String(v == null ? '' : v).replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
 const safeHref = v => { const s = String(v || ''); return /^(https?:\/\/|[a-zA-Z0-9_.-]+\/|[a-zA-Z0-9_.-]+\.html|#)/.test(s) && !s.includes('..') ? s : ''; };
 const source = r => r.kind === 'paper-source' || r.evidenceLevel === 'source-inventory';
 const formal = r => ['formal','lean'].includes(r.kind);
 const topic = r => r.topic || 'Other';
 const mainResult = r => r.mainResult || r.kind==='paper';
 const inKind = r => state.kind==='sources'?source(r):state.kind==='main'?mainResult(r):state.kind==='paper'?r.kind==='paper':state.kind==='formal'?formal(r):!source(r);
 const asArray = v => Array.isArray(v) ? v : v ? [v] : [];
 const searchIndex = new Map(rows.map(r => [r.id, [r.title,r.summary,r.statement,r.id,topic(r),r.sourcePath,r.formalization,r.searchText,r.originalText,...asArray(r.assumptions),...asArray(r.declarations).map(d=>typeof d==='object'?[d.name,d.statement].filter(Boolean).join(' '):d)].flat().filter(Boolean).join(' ').normalize('NFKC').toLowerCase()]));
 function button(name, value, count, group) {return `<button class="filter-btn" type="button" data-group="${group}" data-value="${esc(value)}" aria-pressed="${state[group] === value}">${esc(name)}<span>${count}</span></button>`;}
 function filters(){
  $('kind-filters').innerHTML = button('Featured records','main',rows.filter(mainResult).length,'kind')+button('All results','results',rows.filter(r=>!source(r)).length,'kind')+button('Lean sources','formal',rows.filter(formal).length,'kind')+button('Paper results','paper',rows.filter(r=>r.kind==='paper').length,'kind');
  const scoped = rows.filter(inKind);
  const topics = [...new Set(scoped.map(topic))].sort();
  $('topic-filters').innerHTML = button('All topics','all',scoped.length,'topic')+topics.map(t=>button(t,t,scoped.filter(r=>topic(r)===t).length,'topic')).join('');
  const statuses = [...new Set(scoped.map(r=>r.status))].sort();
  $('status').innerHTML = '<option value="all">All statuses</option>'+statuses.map(s=>`<option value="${esc(s)}">${esc(labels[s]||s)}</option>`).join('');
  if(!statuses.includes(state.status)) state.status='all'; $('status').value=state.status;
 }
 function filtered(){
  const terms=state.query.normalize('NFKC').toLowerCase().split(/\s+/).filter(Boolean);
  let list=rows.filter(r=> inKind(r) && (state.status==='all'||r.status===state.status) && (state.topic==='all'||topic(r)===state.topic) && terms.every(t=>searchIndex.get(r.id).includes(t)));
  if(state.sort==='date')list.sort((a,b)=>String(b.date||'').localeCompare(String(a.date||''))||a.title.localeCompare(b.title));
  else if(state.sort==='title')list.sort((a,b)=>a.title.localeCompare(b.title));
  else list.sort((a,b)=>{const score=r=> terms.reduce((s,t)=>s+(r.title.toLowerCase().includes(t)?5:0)+(String(r.id).toLowerCase().includes(t)?3:0),0)+(formal(r)?1:0);return score(b)-score(a)||String(b.date||'').localeCompare(String(a.date||''));});
  return list;
 }
 function link(href,text){const h=safeHref(href);return h?`<a href="${esc(h)}">${esc(text)}</a>`:'';}
 function card(r){
  const badge = r.status==='lean-verified'?'formal':r.status;
  const assumptions = asArray(r.assumptions);
  const verification = r.formalization || r.verification || 'See the source for verification scope.';
  const renderedProof = p => String(p||'').startsWith('papers/') ? String(p).replace(/\.md(?=#|$)/,'.html') : p;
  const extra = (r.additionalAttachments||[]).map(a=>typeof a==='string'?link(renderedProof(a),'Additional source'):link(renderedProof(a.path||a.href),a.label||'Additional source')).join('');
  return `<article class="result-card" id="${esc(r.id)}"><div class="card-meta"><span class="badge ${esc(badge)}">${esc(labels[r.status] || (formal(r)?'Lean source':r.status))}</span><span>${esc(topic(r))}</span>${r.date?`<time>${esc(r.date)}</time>`:''}<span>${source(r)?'Original source':formal(r)?'Lean source module':'Paper result'}</span></div><h3>${r.pageHref?link(r.pageHref,r.title):esc(r.title)}</h3><p class="summary">${esc(r.summary)}</p>${formal(r)?`<p class="summary">${Number(r.declarationCount||asArray(r.declarations).length).toLocaleString()} declarations indexed · see the complete source record.</p>`:''}${r.statement&&!source(r)&&!formal(r)?`<div class="statement">${esc(r.statement)}</div>`:''}<details><summary>Assumptions &amp; evidence</summary>${assumptions.length?`<ul>${assumptions.map(a=>`<li>${esc(a)}</li>`).join('')}</ul>`:'<p>No additional assumptions are listed in this entry; consult the exact source statement.</p>'}<p class="evidence">${esc(verification)}</p><p class="evidence">Source: ${esc(r.sourcePath || 'Source listed in attachment')}${r.sourceLine?` · line ${Number(r.sourceLine)}`:''}</p>${r.sourceLanguage?`<p>Original language: ${esc(r.sourceLanguage)}.</p>`:''}${r.scopeNote?`<p>${esc(r.scopeNote)}</p>`:''}</details><div class="card-links">${link(r.pageHref,'Read result')}${link(r.englishProof,r.status==='withheld'?'English audit and replacement':'English proof and audit')}${link(r.attachment,formal(r)?'Audited Lean source':'Download proof (Markdown)')}${link(r.leanSource||r.sourceHref,'Lean source')}${link(r.receiptHref,'Verification receipt')}${extra}<a href="#id=${encodeURIComponent(r.id)}" class="permalink" data-id="${esc(r.id)}">Permalink ↗</a></div></article>`;
 }
 function render(){
  filters(); const list=filtered(); const pages=Math.max(1,Math.ceil(list.length/PAGE)); state.page=Math.min(state.page,pages);
  const noun = state.kind==='sources' ? (list.length===1?'source document':'source documents') : (list.length===1?'result':'results');
  $('result-count').textContent=`${list.length.toLocaleString()} ${noun}${state.query?' for “'+state.query+'”':''}`;
  $('results').innerHTML=list.length?list.slice((state.page-1)*PAGE,state.page*PAGE).map(card).join(''):'<div class="empty"><h3>No matching results</h3><p>Try a shorter phrase, a theorem identifier, or another topic. Only records with an explicit audit disposition are shown.</p><button type="button" class="reset" data-action="reset">Clear search and filters</button></div>';
  $('pagination').innerHTML=pages>1?`<button type="button" data-page="${state.page-1}" ${state.page===1?'disabled':''}>Previous</button><span>Page ${state.page} of ${pages}</span><button type="button" data-page="${state.page+1}" ${state.page===pages?'disabled':''}>Next</button>`:'';
 }
 function reset(){Object.assign(state,{kind:'main',status:'all',topic:'all',query:'',page:1});$('query').value='';history.replaceState(null,'',location.pathname+location.search);render();}
 function hash(){
  const p=new URLSearchParams(location.hash.slice(1));const id=p.get('id');
  if(id){const r=rows.find(r=>r.id===id);if(r){Object.assign(state,{kind:source(r)?'sources':'results',status:'all',topic:'all',query:'',page:1});$('query').value='';const list=filtered();state.page=Math.floor(list.findIndex(x=>x.id===id)/PAGE)+1;render();requestAnimationFrame(()=>{const el=document.getElementById(id);if(el){el.classList.add('highlight');el.scrollIntoView({block:'start'});}});}return;}
  if(p.has('q')){state.kind='results';state.query=p.get('q');$('query').value=state.query;state.page=1;render();}
 }
 document.addEventListener('click',e=>{const b=e.target.closest('button');if(!b)return;if(b.dataset.group){state[b.dataset.group]=b.dataset.value;state.page=1;if(b.dataset.group==='kind'){state.topic='all';state.status='all';}render();}else if(b.dataset.page){state.page=Number(b.dataset.page);render();$('library-title').scrollIntoView({block:'start'});}else if(b.dataset.action==='reset')reset();});
 $('search-form').addEventListener('submit',e=>e.preventDefault());
  let timer;$('query').addEventListener('input',()=>{clearTimeout(timer);timer=setTimeout(()=>{state.query=$('query').value.trim();if(state.query&&state.kind==='main'){state.kind='results';state.topic='all';state.status='all';}state.page=1;render();history.replaceState(null,'','#q='+encodeURIComponent(state.query));},120);});
 $('clear-search').addEventListener('click',()=>{state.query='';state.page=1;$('query').value='';history.replaceState(null,'',location.pathname+location.search);render();$('query').focus();});
 $('status').addEventListener('change',()=>{state.status=$('status').value;state.page=1;render();});$('sort').addEventListener('change',()=>{state.sort=$('sort').value;state.page=1;render();});$('reset').addEventListener('click',reset);window.addEventListener('hashchange',hash);
 const generated=String(data.generatedAt||'2026-10-14').slice(0,10);$('snapshot').textContent=`Evidence snapshot · ${generated}`;render();hash();
})();
