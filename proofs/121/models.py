"""Exact necessary weight-enumerator models; no classified codes are inputs.
The Fraction simplex is copied unchanged from ../lemma20-97/exact_lp.py.
Model export format follows ../lemma20-97/global_models.py.
"""
from pathlib import Path
from fractions import Fraction as Q
from math import comb,gcd,lcm
from functools import lru_cache
import json,time
from exact_lp import ExactLP
ROOT=Path(__file__).resolve().parent
@lru_cache(None)
def K(n,j,w):
 return sum((-1)**s*comb(w,s)*comb(n-w,j-s) for s in range(max(0,j-(n-w)),min(j,w)+1))
def g(k,d):return sum((d+(1<<i)-1)//(1<<i) for i in range(k))
def c4(d):return 4*((d+3)//4)
def support(n,k,d,div=2,so=True,full=True,projective=False):
 out=[];excluded={}
 for w in range(d,n+1):
  if w%div:continue
  why=None
  if so and full and w==n-1:why='Lemma 3: full SO excludes n-1'
  if so and projective and w==n-2:why='Lemma 3: projective SO excludes n-2'
  if w<2*d:
   rd=d-w//2
   if so:rd+=rd%2
   if g(k-1,rd)>n-w:why=f'residual [{n-w},{k-1},>={rd}], Griesmer={g(k-1,rd)}'
  if why:excluded[w]=why
  else:out.append(w)
 return out,excluded
class Model:
 def __init__(self,variables):self.variables=variables;self.A=[];self.b=[];self.labels=[]
 def le(self,co,b,label):
  if isinstance(co,dict):co=[co.get(v,0) for v in self.variables]
  co=list(map(Q,co));b=Q(b);assert len(co)==len(self.variables)
  den=lcm(*[x.denominator for x in co+[b]])
  ints=[int(x*den) for x in co];bb=int(b*den);common=gcd(*[abs(x) for x in ints+[bb]]) or 1
  self.A.append([x//common for x in ints]);self.b.append(bb//common);self.labels.append(label)
 def eq(self,co,b,label):
  if isinstance(co,dict):co=[co.get(v,0) for v in self.variables]
  self.le(co,b,label+' <=');self.le([-x for x in co],-b,label+' >=')
 def save(self,name,result=None):
  (ROOT/(name+'-model.json')).write_text(json.dumps(dict(variables=self.variables,A=self.A,b=self.b,labels=self.labels),indent=2),encoding='utf-8')
  if result is not None:
   r=dict(result)
   if r['status']=='infeasible':
    nz=[(i,v) for i,v in enumerate(r['y']) if v];den=lcm(*[v.denominator for _,v in nz]);ints=[int(v*den) for _,v in nz];common=gcd(*ints) or 1
    r['y']=[dict(row=i,multiplier=a//common,label=self.labels[i]) for (i,v),a in zip(nz,ints)]
   else:r['x']=[str(x) for x in r.get('x',[])]
   (ROOT/(name+'-result.json')).write_text(json.dumps(r,indent=2,default=str),encoding='utf-8')
 def solve(self,c=None,limit=120):return ExactLP(self.A,self.b,c,limit).solve()
def ordinary(n,k,d,div=2,so=True,full=True,projective=False,weights=None):
 weights=weights or support(n,k,d,div,so,full,projective)[0]
 M=Model(weights);M.eq([1]*len(weights),2**k-1,'A0=1 and nonzero total')
 for j in range(1,n+1):
  row=[K(n,j,w) for w in weights]
  if (j==1 and full) or (j==2 and projective):M.eq(row,-comb(n,j),f'B{j}=0')
  else:M.le([-v for v in row],comb(n,j),f'B{j}>=0')
  if so:M.le([-v+2**k*int(w==j) for w,v in zip(weights,row)],comb(n,j),f'B{j}>=A{j}')
 return M
if __name__=='__main__':
 for name,n,k,d,div,so,proj in [('A_min44',90,8,44,2,True,True),('D89',89,7,44,4,True,True),('D90',90,7,44,4,True,False)]:
  s,e=support(n,k,d,div,so,True,proj);print('SUPPORT',name,s,'EXCLUSIONS',e,flush=True)
  M=ordinary(n,k,d,div,so,True,proj);r=M.solve();M.save(name,r)
  print('LP',name,r['status'],'seconds',r.get('seconds'),'pivots',r['pivots'],flush=True)
  if r['status']=='feasible':print('WITNESS',dict(zip(M.variables,map(str,r['x']))),flush=True)
  else:print('CERT',[(M.labels[i],str(y)) for i,y in enumerate(r['y']) if y],flush=True)
