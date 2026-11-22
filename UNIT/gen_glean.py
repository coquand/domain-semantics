# gen_glean.py: regenerate the body of GLean.seg from GAT.seg (run from UNIT/).
# Add an entry to drop/rec for each rule whose premises the lean GAT omits.
import re,sys
src=open('GAT.seg').read()
blk=src[src.index('data GDer'):]
blk=blk[blk.index('=')+1:blk.index(';\n')]
# strip comments
blk='\n'.join(l for l in blk.split('\n') if not l.strip().startswith('--'))
parts=re.split(r'\n\s*\|\s*',' \n'+blk.strip())
cons=[]
for p in parts:
    p=' '.join(p.split())
    if not p: continue
    name=p.split()[0]; rest=p[len(name):].strip()
    al=[]; i=0
    while rest[i]=='(':
        d=0; j=i
        while True:
            if rest[j]=='(': d+=1
            elif rest[j]==')':
                d-=1
                if d==0: break
            j+=1
        g=rest[i+1:j]; names,ty=g.split(':',1)
        for n in names.split(): al.append((n,ty.strip()))
        i=j+1
        while i<len(rest) and rest[i]==' ': i+=1
    assert rest[i]==':', p
    res=rest[i+1:].strip()
    cons.append((name,al,res))
drop={
 'gm-app':['h1'],'gm-sb':['hA'],'ge-pi':['h0'],'ge-sb':['h0','h2','h3'],'gm-sym':['hA'],
 'gm-elam':['h0'],'gm-eapp':['h0','hB','ha'],'gm-epic':['h0'],'gm-esb':['hA','h0','h2','h3'],
 'gm-beta':['hA','hB'],'gm-eta':['hA','hB'],'gq-lift':['h0','h2'],'gq-sec':['hA','ha','ha\''],
}
P='gpresup'
rec={
 'gm-app':{'h1':'wf-ext-inv G A (gpresup (gjty (gext G A) B) xh2)'},
 'gm-sb':{'hA':'(gpresup (gjtm G a A) xh1).2'},
 'ge-pi':{'h0':'(gpresup (gjeqty G A A\') xh1).2.1'},
 'ge-sb':{'h0':'(gpresup (gjeqty G A A\') xh1).2.1','h2':'(gpresup (gjeqsub D s s\' G) xh4).2.2.1','h3':'(gpresup (gjeqsub D s s\' G) xh4).2.2.2'},
 'gm-sym':{'hA':'(gpresup (gjeqtm G a b A) xh).2.1'},
 'gm-elam':{'h0':'(gpresup (gjeqty G A A\') xh1).2.1'},
 'gm-eapp':{'h0':'(gpresup (gjeqty G A A\') xh1).2.1','hB':'(gpresup (gjeqty (gext G A) B B\') xh2).2.1','ha':'(gpresup (gjeqtm G a a\' A) xh4).2.2.1'},
 'gm-epic':{'h0':'(gpresup (gjeqtm G a a\' (guu n)) xh1).2.2.1'},
 'gm-esb':{'hA':'(gpresup (gjeqtm G a a\' A) xh1).2.1','h0':'(gpresup (gjeqtm G a a\' A) xh1).2.2.1','h2':'(gpresup (gjeqsub D s s\' G) xh4).2.2.1','h3':'(gpresup (gjeqsub D s s\' G) xh4).2.2.2'},
 'gm-beta':{'hA':'wf-ext-inv G A (gpresup (gjtm (gext G A) b B) xh1).1','hB':'(gpresup (gjtm (gext G A) b B) xh1).2'},
 'gm-eta':{'hA':'(ty-gpi-inv G A B (gpresup (gjtm G f (gpi A B)) xh).2).1','hB':'(ty-gpi-inv G A B (gpresup (gjtm G f (gpi A B)) xh).2).2'},
 'gq-lift':{'h0':'(gpresup (gjeqty G A A\') xh1).2.1','h2':'(gpresup (gjeqsub D s s\' G) xh3).2.2.1'},
 'gq-sec':{'hA':'(gpresup (gjeqty G A A\') xh1).2.1','ha':'(gpresup (gjeqtm G a a\' A) xh2).2.2.1','ha\'':'(gpresup (gjeqtm G a a\' A) xh2).2.2.2'},
}
isder=lambda ty: ty.startswith('GDer')
out=[]
# data
out.append('data GDerL : (J : GJ) -> U l =')
for i,(n,al,res) in enumerate(cons):
    kept=[(a,t) for a,t in al if a not in drop.get(n,[])]
    s=('    ' if i==0 else '  | ')+'l'+n
    if kept: s+=' '+' '.join('(%s : %s)'%(a,t.replace('GDer','GDerL')) for a,t in kept)
    s+=' : '+res.replace('GDer','GDerL')
    out.append(s)
out[-1]+=' ;'
out.append('')
# to-glean
out.append('to-glean : (J : GJ) -> GDer J -> GDerL J = split {')
L=[]
for n,al,res in cons:
    ds=[a for a,t in al if isder(t)]
    lhs=n+(' '+' '.join(a for a,t in al) if al else '')
    if ds: lhs+=' | '+' '.join('x'+a.replace("'",'p') for a in ds)
    rhs='l'+n+''.join(' '+(('x'+a.replace("'",'p')) if isder(t) else a) for a,t in al if a not in drop.get(n,[]))
    L.append('  %s -> %s'%(lhs,rhs))
out.append(' ;\n'.join(L)+' } ;')
out.append('')
out.append('to-gder : (J : GJ) -> GDerL J -> GDer J = split {')
L=[]
for n,al,res in cons:
    kept=[(a,t) for a,t in al if a not in drop.get(n,[])]
    ds=[a for a,t in kept if isder(t)]
    lhs='l'+n+(' '+' '.join(a for a,t in kept) if kept else '')
    if ds: lhs+=' | '+' '.join('x'+a.replace("'",'p') for a in ds)
    args=[]
    for a,t in al:
        if a in drop.get(n,[]): args.append('('+rec[n][a]+')')
        elif isder(t): args.append('x'+a.replace("'",'p'))
        else: args.append(a)
    rhs=n+''.join(' '+x for x in args)
    L.append('  %s -> %s'%(lhs,rhs))
out.append(' ;\n'.join(L)+' } ;')
body='\n'.join(out)+'\n'

# the header (inversions) is kept verbatim from the current GLean.seg;
# only the data type and the two translations are regenerated.
cur=open('GLean.seg').read()
open('GLean.seg','w').write(cur[:cur.index('data GDerL')]+body)
