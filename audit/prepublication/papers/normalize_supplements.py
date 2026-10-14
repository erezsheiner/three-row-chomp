from pathlib import Path
import re
folder=Path(__file__).resolve().parent/'supplements'
slash=chr(92)
for name in ['CANONICAL-DEFINITIONS.md','COUNT-CLOCK-AND-ABSTRACT-BOUNDARY.md']:
    p=folder/name;t=p.read_text(encoding='utf-8')
    # An inline delimiter belongs outside a display, never within it.
    def display_fix(match):
        return re.sub(r'\\\((.*?)\\\)',lambda m:'('+m.group(1)+')',match.group(0),flags=re.S)
    t=re.sub(r'\\\[.*?\\\]',display_fix,t,flags=re.S)
    parts=[];i=0;count=0
    while i<len(t):
        if t.startswith(slash+'(',i) or t.startswith(slash+'[',i):
            end=slash+(')'if t[i+1]=='('else']')
            j=t.find(end,i+2)
            assert j>=0,(name,i)
            parts.append(t[i:j+2]);i=j+2;continue
        if t[i]=='(' and (i==0 or not(t[i-1].isalnum()or t[i-1]in (slash,'_'))):
            j=i+1;depth=1
            while j<len(t)and depth:
                if t[j]=='(':depth+=1
                elif t[j]==')':depth-=1
                j+=1
            if depth==0:
                body=t[i+1:j-1].rstrip(slash)
                math=bool(re.search(r'[<>=_\\{}]',body)or re.fullmatch(r'[A-Za-z][A-Za-z0-9]*|[0-9]+|[A-Za-z][A-Za-z0-9]*\(.*\)',body))
                if math:
                    parts.append(slash+'('+body+slash+')');i=j;count+=1;continue
        parts.append(t[i]);i+=1
    t=''.join(parts)
    t=t.replace(chr(96)+'CANONICAL-FOUNDATIONS.md'+chr(96),'[canonical foundation](../../audit/full/CANONICAL-FOUNDATIONS.md)')
    p.write_text(t,encoding='utf-8')
    print(name,count)
links={
 'GHOST-TOKENS-AND-OWNER-TRANSPORT.md':[
 ('The canonical foundation supplies','The [canonical foundation](../../audit/full/CANONICAL-FOUNDATIONS.md) supplies')],
 'SOURCE-TIME-AND-TIGHTNESS.md':[
 ('conventions of CANONICAL-DEFINITIONS.md','conventions of [Canonical definitions](CANONICAL-DEFINITIONS.md)'),
 ('theorem R195B30Depth20AffineRails.gameF_col31_rail','theorem [R195B30Depth20AffineRails.gameF_col31_rail](../../lean/core/R195B30Depth20AffineRails.lean)'),
 ('the delivered tight_width18_base.json','the delivered [tight-width base](../../certificates/inputs/tight_width18_base.json)')]
}
for name,replacements in links.items():
    p=folder/name;t=p.read_text(encoding='utf-8')
    for old,new in replacements:
        assert old in t or new in t,old;t=t.replace(old,new)
    p.write_text(t,encoding='utf-8')
