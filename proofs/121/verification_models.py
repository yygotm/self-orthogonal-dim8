"""Independent reconstruction of ordinary and one-anchor C systems."""
from verify_resume import System,K,DCASES,norm,R
from verify_round456 import load,verify_lp
from verify_round12 import g
from math import comb,lcm
from functools import lru_cache
import json

def ordinary(n,k,ws,so,full,proj):
 M=System(ws);M.eq([1]*len(ws),2**k-1)
 for j in range(1,n+1):
  co=[K(n,j,w) for w in ws]
  if (j==1 and full) or (j==2 and proj):M.eq(co,-comb(n,j))
  else:M.le([-v for v in co],comb(n,j))
  if so:M.le([-v+2**k*int(w==j) for w,v in zip(ws,co)],comb(n,j))
 return M

def simple_support(n,k,d,div,so,full,proj):
 out=[]
 for w in range(d,n+1):
  if w%div:continue
  if so and full and w==n-1:continue
  if so and proj and w==n-2:continue
  rd=d-w//2;rd+=rd%2 if so else 0
  if w<2*d and g(k-1,rd)>n-w:continue
  out.append(w)
 return out
@lru_cache(None)
def rws(n,k,d):
 aa=[e for e in load('recursive-audit.json') if e.get('effective',[])[:3]==[n,k,d] and e.get('effective',[0]*6)[5] and 'weights' in e]
 return min((e['weights'] for e in aa),key=len) if aa else simple_support(n,k,d,2,False,True,False)

def global_C(case,excluded=(),active=None,fixed=None):
 L,D=DCASES[case];ws=sorted(list(D)+list(range(58,111,4)));G=System(ws);G.eq([1]*len(ws),255)
 for w,a in D.items():G.eq([int(v==w) for v in ws],a)
 G.le([-int(v==58) for v in ws],-1);bd=(comb(L,2)+sum(a*K(L,2,w) for w,a in D.items()))//128
 for j in range(1,122):
  co=[K(121,j,w) for w in ws]
  if j==1:G.eq(co,-121)
  else:G.le([-v for v in co],comb(121,j))
  G.le([-v+256*int(w==j) for w,v in zip(ws,co)],comb(121,j));dn=comb(121,j)+sum(a*K(121,j,w) for w,a in D.items());G.le(co,2*dn-comb(121,j))
  if j==2:G.le(co,256*bd-comb(121,j))
 G.compact()
 for w in excluded:G.eq([int(v==w) for v in ws],0)
 if active is not None:
  N=System(active);ii=[ws.index(w) for w in active]
  for co,b in zip(G.A,G.b):N.le([co[i] for i in ii],b)
  G=N;ws=active
 if fixed:
  for w in ws:G.eq([int(v==w) for v in ws],fixed[w])
 return G

def split_C(case,w,excluded=(),active=None,fixed=None):
 G=global_C(case,excluded,active,fixed);L=121-w;rd=58-w//2;rd+=rd%2;div=2 if L!=g(7,rd) else max(2,rd&-rd);ws=[j for j in rws(L,7,rd) if j%div==0];N=ordinary(L,7,ws,div>=4,True,L-g(6,rd)==1);cells=[]
 for a in G.variables:
  if a%4:continue
  for b in G.variables:
   if b%4!=2:continue
   i=(w+a-b)//2;j=(a+b-w)//2
   if i%2==0 and 0<=i<=w and 0<j<=L and j in ws:cells.append([a,b,i,j])
 M=System(cells)
 for co,b in zip(G.A,G.b):
  f=dict(zip(G.variables,co));M.le([f[a]+f[z] for a,z,i,j in cells],b-f.get(w,0))
 for co,b in zip(N.A,N.b):
  f=dict(zip(ws,co));M.le([f[j] for a,z,i,j in cells],b)
 mult=L-g(6,rd);M.le([K(L,2,j) for a,b,i,j in cells],128*L*(mult-1)//2-comb(L,2));M.compact();return M
