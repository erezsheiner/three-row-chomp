// Static Markdown rendering. The bundled marked 17.0.5 is MIT licensed.
// Raw HTML is escaped; only safe local/external links remain clickable.
import { Marked } from './vendor/marked.mjs';
import katex from './vendor/katex.mjs';
import fs from 'node:fs';
import path from 'node:path';

const tasks = JSON.parse(fs.readFileSync(0, 'utf8'));
const renderedPaths = new Set(tasks.map(t => path.resolve(t.output)));
let mathExpressions = 0;
const math = (source, displayMode) => {
  mathExpressions++;
  return katex.renderToString(source, {displayMode, throwOnError:true, trust:false, strict:'error', maxExpand:10000});
};
const escape = x => String(x).replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
for (const task of tasks) {
  const used = new Map();
  const renderer = {
    html({text}) {
      // Marked may tokenize an inline empty anchor as two HTML tokens.
      const anchor = text.trim().match(/^<a\s+id=["']([a-zA-Z0-9_-]+)["']\s*>(<\/a>)?$/);
      if (anchor) return `<a id="${anchor[1]}">${anchor[2] ? '</a>' : ''}`;
      if (text.trim() === '</a>') return '</a>';
      return escape(text);
    },
    heading({tokens, depth, text}) {
      const base = text.toLowerCase().replace(/<[^>]*>/g,'').replace(/[^\p{L}\p{N}_ -]/gu,'').trim().replace(/\s+/g,'-') || 'section';
      const count = used.get(base) || 0; used.set(base,count+1);
      const id = count ? `${base}-${count}` : base;
      return `<h${depth} id="${escape(id)}">${this.parser.parseInline(tokens)}</h${depth}>`;
    },
    link({href, tokens}) {
      const label = this.parser.parseInline(tokens);
      if (href.startsWith('../docs/')) href = '../documentation/' + href.slice('../docs/'.length);
      const localMarkdown = href.split('#')[0];
      const linkedPath = path.resolve(path.dirname(task.output), localMarkdown);
      const docRoot = path.resolve(task.siteRoot, 'documentation');
      if (localMarkdown.endsWith('.md') && renderedPaths.has(linkedPath.replace(/\.md$/, '.html'))) href = href.replace(/\.md(?=#|$)/, '.html');
      const leanRoot = path.resolve(task.siteRoot, 'lean');
      if (linkedPath.startsWith(leanRoot + path.sep)) {
        const sourcePath = path.resolve(task.siteRoot, 'sources/lean', path.relative(leanRoot, linkedPath));
        href = path.relative(path.dirname(task.output), sourcePath).split(path.sep).join('/') + (href.includes('#') ? '#'+href.split('#')[1] : '');
      }
      if (task.rewriteLeanLinks && href.startsWith('../lean/')) href = '../sources/lean/' + href.slice('../lean/'.length);
      if (/^https?:\/\//i.test(href) || /^#[a-zA-Z0-9_-]+$/.test(href)) return `<a href="${escape(href)}">${label}</a>`;
      // Historical relative paths are documentary references. Retain them as
      // text unless the referenced file actually exists inside this website.
      if (!/^[a-zA-Z][a-zA-Z0-9+.-]*:/.test(href) && !href.startsWith('/')) {
        const target = path.resolve(path.dirname(task.output), decodeURIComponent(href.split('#')[0]));
        const root = path.resolve(task.siteRoot);
        if (target.startsWith(root + path.sep) && (fs.existsSync(target) || renderedPaths.has(target))) return `<a href="${escape(href)}">${label}</a>`;
      }
      return `${label} <span class="path">(${escape(href)})</span>`;
    },
    image({text}) { return `<span>${escape(text || 'Image referenced in original source')}</span>`; }
  };
  const engine = new Marked({gfm:true});
  engine.use({extensions:[{
    name:'displayMath',level:'block',start(src){return src.search(/\\\[|\$\$/);},
    tokenizer(src){const m=/^(?:\\\[([\s\S]*?)\\\]|\$\$([\s\S]*?)\$\$)\s*(?:\n|$)/.exec(src);if(m)return {type:'displayMath',raw:m[0],text:m[1]??m[2]};},
    renderer(token){return '<div class="math-display">'+math(token.text,true)+'</div>';}
  },{
    name:'inlineMath',level:'inline',start(src){return src.indexOf('\\(');},
    tokenizer(src){const m=/^\\\(([\s\S]*?)\\\)/.exec(src);if(m)return {type:'inlineMath',raw:m[0],text:m[1]};},
    renderer(token){return math(token.text,false);}
  }]});
  engine.use({renderer});
  const body = engine.parse(fs.readFileSync(task.input,'utf8'));
  fs.mkdirSync(path.dirname(task.output),{recursive:true});
  fs.writeFileSync(task.output,task.before+body+task.after,'utf8');
}
process.stdout.write(JSON.stringify({rendered:tasks.length,mathExpressions}));
