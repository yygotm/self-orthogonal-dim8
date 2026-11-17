"""Independent arithmetic verifier. Standard library only; no solver imports.
It checks exported LP statements, not their mathematical encoding automatically.
The code-to-model derivation is in subcode-proof.md/report.md.
"""
from pathlib import Path
from fractions import Fraction as F
from math import comb
from collections import Counter
from itertools import product
import json,sys,time
R=Path(__file__).resolve().parent
start=time.perf_counter()
def K(n,j,w):return sum((-1)**i*comb(w,i)*comb(n-w,j-i) for i in range(max(0,j-n+w),min(j,w)+1))
def chi(x,y):return 1-2*((x&y).bit_count()%2)
def check_lp(name,negative=False):
 m=json.loads((R/(name+'-model.json')).read_text(encoding='utf-8'));r=json.loads((R/(name+'-result.json')).read_text(encoding='utf-8'));A=m['A'];b=m['b']
 if r['status']=='feasible':
  x=list(map(F,r['x']));assert all(v>=0 for v in x);assert all(sum(F(a)*v for a,v in zip(row,x))<=F(bb) for row,bb in zip(A,b))
 else:
  assert r['status']=='infeasible';y=[F(0)]*len(b)
  for v in r['y']:y[v['row']]=F(v['multiplier'])
  if negative:y[next(i for i,v in enumerate(y) if v)]=-1
  assert all(v>=0 for v in y),'negative dual multiplier'
  assert all(sum(y[i]*F(A[i][j]) for i in range(len(b)))>=0 for j in range(len(m['variables'])))
  assert sum(v*F(bb) for v,bb in zip(y,b))<0
 return r['status']
if '--negative-control' in sys.argv:
 check_lp('no_R49',True);raise AssertionError('negative control unexpectedly passed')
# The128 seven-sign functions used in the subcode classification.
hist=Counter()
for mask in range(128):
 s=[0]+[1-2*((mask>>(z-1))&1) for z in range(1,8)]
 f=[sum(s[z]*chi(z,a) for z in range(8)) for a in range(8)]
 if max(f)>3:continue
 c=Counter(f);hist[tuple(sorted(c.items()))]+=1
 if c==Counter({-5:1,-1:4,3:3}):
  minus=f.index(-5);P={a^minus for a in range(8) if f[a] in [-5,3]};assert len(P)==4 and all(a^b in P for a in P for b in P)
 else:assert c==Counter({-7:1,1:7})
assert hist==Counter({((-7,1),(1,7)):8,((-5,1),(-1,4),(3,3)):56})
print('SEVEN-SIGN LEMMA 128 checked;64 admissible',flush=True)
# Local8-point Fourier implications, checked independently over small integer vectors.
validI=0
for a0 in range(-5,6):
 for tail in product([-1,0,1],repeat=7):
  a=(a0,*tail);f=[sum(a[z]*chi(z,h) for z in range(8)) for h in range(8)]
  if not all(v in [-8,0,8] for v in f):continue
  validI+=1;assert not any(a) or (all(abs(v)==1 for v in a) and sum(v!=0 for v in f)==1)
assert validI==17
validII=0
for v0 in range(-8,9,2):
 for tail in product(range(-4,5,2),repeat=4):
  w=[sum(tail[z]*chi(z,h) for z in range(4)) for h in range(4)]
  if not all(v0+sgn*x in [-16,0,16] for x in w for sgn in [-1,1]):continue
  validII+=1;assert v0 in [-8,0,8]
  if any(tail):
   assert all(abs(v)==4 for v in tail)
   prod=1
   for v in tail:prod*=v//4
   assert prod==(-1 if v0 else 1)
  else:assert v0==0
print('LOCAL FOURIER LEMMAS',validI,validII,flush=True)
# Explicit examples of every subcode distribution; these are not extensions to C.
expected=[{60:112,64:15},{60:108,64:15,76:4},{60:104,64:15,68:8},{60:96,64:31},{60:98,64:27,68:2},{60:105,64:14,68:7,72:1},{60:100,64:23,68:4}]
for case in range(7):
 if case==0:columns=[x for x in range(1,128) if x>=8]
 else:
  j=[0]*64
  if case in [1,2,3]:
   for b in range(8):j[8*b]=1
   size={1:1,2:2,3:4}[case]
   for a in range(4,8):
    for b in range(size):j[a+8*b]=4//size
  elif case==4:
   for b in range(8):j[8*b]=2 if b<2 else 1
   for a in range(1,8):
    for b in range(2):j[a+8*b]=1
  elif case==5:
   for b in range(8):j[8*b]=3 if b==0 else 1
   for a in range(1,8):j[a]=2
  else:
   for b in range(4):j[8*b]=2
   for a in range(4,8):
    for b in range(4):j[a+8*(b+(4 if a==7 else 0))]=1
  assert sum(j)==24;columns=[1,1]
  for y in range(1,64):
   v=-sum(j[u]*chi(u,y) for u in range(64));assert v%8==0;s=v//8;m=1 if y<8 else 2
   assert abs(s)<=m and (m+s)%2==0
   columns.extend([2*y]*((m+s)//2));columns.extend([2*y+1]*((m-s)//2))
 weights={u:sum((u&x).bit_count()%2 for x in columns) for u in range(1,128)}
 assert Counter(weights.values())==Counter(expected[case]);assert all(w%4==0 for w in weights.values())
 assert all(sum(((x>>a)&1)*((x>>b)&1) for x in columns)%2==0 for a in range(7) for b in range(7))
 print('SUBCODE EXAMPLE',case,len(columns),dict(Counter(weights.values())),flush=True)

# Reconstruct the three two-moment contradiction certificates independently.
from verification_models import System
for name,n,k,ws in [('no_R49',49,7,[24,32]),('no_R33',33,7,[16]),('no_C60',121,8,[60,64])]:
 M=System(ws);M.eq([1]*len(ws),2**k-1);M.eq(ws,2**(k-1)*n);M.le([-K(n,2,w) for w in ws],comb(n,2))
 saved=json.loads((R/(name+'-model.json')).read_text(encoding='utf-8'));assert saved['variables']==M.variables and saved['A']==M.A and saved['b']==M.b;assert check_lp(name)=='infeasible'
 print('BASIC FARKAS',name,'PASS',flush=True)
print('PASS hand-lemma finite arithmetic',time.perf_counter()-start,flush=True)
