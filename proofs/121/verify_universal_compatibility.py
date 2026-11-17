"""Independent reconstruction of universal residual cuts and compatibility bounds."""
from verify_round12 import allowed,g,K,R
from verify_round456 import load
from verify_resume import DCASES
from itertools import combinations_with_replacement
from math import comb
import json,time

def template(n,ws,w):
 L=n-w;d=(n-3)//2;rd=d-w//2;rw=allowed(L,6,rd);cells=[]
 for a,b in combinations_with_replacement(ws,2):
  i=(w+a-b)//2;j=(a+b-w)//2
  if 0<=i<=w and j in rw:cells.append([a,b,i,j])
 A=[];B=[];dim=len(ws)+2
 def row(a,b):A.append(a);B.append(b)
 for z,v in enumerate(ws):
  co=[int(a==v)+int(b==v) for a,b,i,j in cells];rhs=[0]*dim;rhs[z]=1;rhs[-1]=-int(v==w);row(co,rhs);row([-x for x in co],[-x for x in rhs])
 co=[j for a,b,i,j in cells];rhs=[0]*dim;rhs[-1]=32*L;row(co,rhs);row([-x for x in co],[-x for x in rhs])
 for t in range(2,5):
  co=[K(L,t,j) for a,b,i,j in cells];rhs=[0]*dim;rhs[-1]=comb(L,t);row([-x for x in co],rhs)
  if t==2:rhs=[0]*dim;rhs[-2]=64;rhs[-1]=-comb(L,2);row(co,rhs)
 if rd%2:
  for t in range(1,5):
   rhs=[0]*dim;rhs[-1]=comb(L+1,t);row([-K(L+1,t,j+j%2) for a,b,i,j in cells],rhs)
 return dict(cells=cells,A=A,B=B)

def check(n):
 start=time.perf_counter();src=load(f'R{n}-gauss-integers.json');state=load(f'R{n}-universal.json');templates=load(f'R{n}-universal-templates.json');ws=state['weights'];vs=[[x['A'][str(w)] for w in ws]+[x['B2'],1] for x in src];left=set(range(len(src)))
 for w,t in templates.items():
  expected=template(n,ws,int(w));assert all(t[k]==v for k,v in expected.items()),(n,w)
 for cut in state['cuts']:
  t=templates[str(cut['anchor'])];y=cut['y'];assert len(y)==len(t['A']) and all(isinstance(v,int) and v>=0 for v in y)
  assert all(sum(v*t['A'][i][j] for i,v in enumerate(y))>=0 for j in range(len(t['cells'])))
  co=[sum(v*t['B'][i][j] for i,v in enumerate(y)) for j in range(len(ws)+2)];assert co==cut['coefficients'];wi=ws.index(cut['anchor']);gone=[i for i in left if vs[i][wi] and sum(a*b for a,b in zip(co,vs[i]))<0];assert len(gone)==cut['excluded'];left.difference_update(gone)
 assert sorted(left)==state['left'];print('UNIVERSAL PASS',n,len(state['cuts']),len(left),'seconds',time.perf_counter()-start,flush=True);return dict(n=n,cuts=len(state['cuts']),remaining=len(left),seconds=time.perf_counter()-start)

def compatibility():
 src=load('R63-gauss-integers.json');counts=[]
 for case,(L,D) in enumerate(DCASES):
  bd=(comb(L,2)+sum(a*K(L,2,w) for w,a in D.items()))//128;dv=sorted(w for w,a in D.items() for _ in range(a));out=[]
  for ix,e in enumerate(src):
   if e['B2']>bd:continue
   rv=sorted(int(w) for w,a in e['A'].items() for _ in range(a))
   if any(d>2*r for d,r in zip(dv,rv)):continue
   lower=sum(d*r for d,r in zip(dv,reversed(rv)));upper=sum(d*r for d,r in zip(dv,rv))
   constant=comb(121,2)+K(121,2,58)+sum(4*d*d-232*d for d in dv)+sum(8*r*r-20*r+7212 for r in rv)
   if constant-8*upper>256*bd or constant-8*lower<256*e['B2']:continue
   out.append(ix)
  assert out==load(f'R63-compatible-case{case}.json');counts.append(len(out));print('COMPATIBILITY PASS',case,len(out),flush=True)
 return counts
if __name__=='__main__':
 start=time.perf_counter();out=dict(universal=[check(59),check(63)],compatibility=compatibility());out['seconds']=time.perf_counter()-start;(R/'universal-compatibility-verification.json').write_text(json.dumps(out,indent=2), encoding='utf-8');print('PASS',out['seconds'],flush=True)
