"""Independent integer verification of round-1/round-2 necessary-condition cuts.
No import of any solver or model-builder. General coding lemmas are in proof sections 10/11.
"""
from pathlib import Path
from math import comb,gcd
from functools import lru_cache
import json,re,time
R=Path(__file__).resolve().parent;WS=[30,32,34,36,38,40,44,46,48,52,56,62]
@lru_cache(None)
def K(n,j,w):return sum((-1)**t*comb(w,t)*comb(n-w,j-t) for t in range(max(0,j-n+w),min(j,w)+1))
def g(k,d):return sum((d+2**i-1)//2**i for i in range(k))
def norm(a,b):
 z=gcd(*[abs(v) for v in a+b]) or 1;return [v//z for v in a],[v//z for v in b]
@lru_cache(None)
def allowed(n,k,d,div=1,full=True,depth=2):
 d=div*((d+div-1)//div)
 if g(k,d)>n or k>n or (n,k,d) in {(13,5,6),(41,6,20),(25,6,12),(17,6,8)}:return []
 if d%2 and div==1:
  e=allowed(n+1,k,d+1,2,False,depth);return [v for v in range(d,n+1) if v+v%2 in e]
 if n==g(k,d):div=max(div,d&-d);full=True
 so=div%4==0
 if so and 2*k>n:return []
 projective=full and n-g(k-1,d)==1;out=[]
 for v in range(d,n+1,div):
  if so and full and v==n-1:continue
  if so and projective and v==n-2:continue
  rd=d-v//2;rd+=rd%2 if so else 0
  if v<2*d and g(k-1,rd)>n-v:continue
  if depth and k>1 and v<2*d and not allowed(n-v,k-1,rd,2 if so else 1,full,depth-1):continue
  out.append(v)
 return out

def verify_template(T):
 w=T['anchor'];L=63-w;rd=30-w//2;cells=T['cells'];assert T['rws']==allowed(L,6,rd,2 if T.get('radical_anchor') else 1)
 expected=[]
 for p,a in enumerate(WS):
  for b in WS[p:]:
   i=(w+a-b)//2;j=(a+b-w)//2
   if 0<=i<=w and j in T['rws'] and (not T.get('radical_anchor') or i%2==0):expected.append([a,b,i,j])
 assert cells==expected
 for A,B,label in zip(T['A'],T['B'],T['labels']):
  rhs=[0]*14
  if label.startswith('Base parent'):
   a=int(re.search(r'A(\d+)',label)[1]);co=[int(x==a)+int(y==a) for x,y,i,j in cells];rhs[WS.index(a)]=1;rhs[-1]=-int(a==w)
   if label.endswith('>='):co=[-v for v in co];rhs=[-v for v in rhs]
  elif label.startswith('Base full'):
   co=[j for x,y,i,j in cells];rhs[-1]=32*L
   if label.endswith('>='):co=[-v for v in co];rhs=[-v for v in rhs]
  elif label=='Base T B2 <= R B2':co=[K(L,2,j) for a,b,i,j in cells];rhs[-2]=64;rhs[-1]=-comb(L,2)
  elif label.startswith('Base T'):
   t=int(re.search(r'B(\d+)',label)[1]);co=[-K(L,t,j) for a,b,i,j in cells];rhs[-1]=comb(L,t)
  elif label.startswith('Parity'):
   assert rd%2;t=int(re.search(r'B(\d+)',label)[1]);co=[-K(L+1,t,j+j%2) for a,b,i,j in cells];rhs[-1]=comb(L+1,t)
  elif label.startswith('Split'):
   u,v=map(int,re.search(r'B(\d+),(\d+)',label).groups());co=[-(K(w,u,i)+K(w,u,w-i))*K(L,v,j) for a,b,i,j in cells];rhs[-1]=(K(w,u,0)+K(w,u,w))*comb(L,v)
  elif label.startswith('Gauss'):
   G=int(label.split()[1]);co=[(-1)**((j+j%2)//2) for a,b,i,j in cells];rhs[-1]=G-1
   if label.endswith('>='):co=[-v for v in co];rhs=[-v for v in rhs]
  elif label.startswith('Oddset'):
   mask=int(label.split()[-1]);co=[-int(((mask>>WS.index(a))&1)!=((mask>>WS.index(b))&1)) for a,b,i,j in cells];rhs[-1]=-1
  else:raise ValueError(label)
  aa,bb=norm(co,rhs);assert aa==A and bb==B,label

def main():
 start=time.perf_counter();source=json.loads((R/'R63-gauss-integers.json').read_text(encoding='utf-8'));pairs=json.loads((R/'fixedR-resume-feasible.json').read_text(encoding='utf-8'));initial={p['R_index'] for p in pairs};vectors={i:[source[i]['A'][str(w)] for w in WS]+[source[i]['B2'],1] for i in initial};left=initial.copy();verified=[]
 cache={}
 for stage in [1,2]:
  state=json.loads((R/f'round{stage}-state.json').read_text(encoding='utf-8'))
  for index,cut in enumerate(state['cuts']):
   path=cut['model'] if stage==2 else f'round1-template-{cut["anchor"]}.json'
   if path not in cache:
    T=json.loads((R/path).read_text(encoding='utf-8'));verify_template(T);cache[path]=T
   T=cache[path];ys={v['row']:v['multiplier'] for v in cut['y']};assert len(ys)==len(cut['y']) and all(v>=0 for v in ys.values())
   assert all(sum(v*T['A'][i][j] for i,v in ys.items())>=0 for j in range(len(T['cells'])))
   co=[sum(v*T['B'][i][j] for i,v in ys.items()) for j in range(14)];assert co==cut['coefficients']
   masks=sorted({int(T['labels'][i].split()[-1]) for i,v in ys.items() if v and T['labels'][i].startswith('Oddset')});assert masks==cut.get('odd_masks',[])
   w=cut['anchor'];removed=[]
   for ix in sorted(left):
    z=vectors[ix]
    if not z[WS.index(w)]:continue
    if not all((sum(z[j] for j in range(12) if mask>>j&1)-((mask>>WS.index(w))&1))%2 for mask in masks):continue
    if sum(a*b for a,b in zip(co,z))<0:removed.append(ix)
   assert removed==cut['removed'];left.difference_update(removed)
  assert sorted(left)==state['left'];assert {p['pair_id'] for p in pairs if p['R_index'] in left}==set(state['pairs_left'])
  verified.append(dict(round=stage,cuts=len(state['cuts']),R_remaining=len(left),pairs_remaining=len(state['pairs_left']),complete=state['complete']))
  print('PASS',verified[-1],flush=True)
 out=dict(rounds=verified,templates_verified=len(cache),seconds=time.perf_counter()-start)
 (R/'round12-verification.json').write_text(json.dumps(out,indent=2), encoding='utf-8');print('ALL CERTIFICATES VERIFIED',out,flush=True)
if __name__=='__main__':main()
