"""Independent completeness check of saved formal integer enumerator tables.
This is certificate-table verification, not a search over generator matrices.
No solver or enumerator imports. Standard library integer arithmetic only.
"""
from pathlib import Path
from fractions import Fraction
from functools import lru_cache
from math import comb
import json,time
from verification_models import DCASES,rws
R=Path(__file__).resolve().parent
@lru_cache(None)
def K(n,j,w):return sum((-1)**t*comb(w,t)*comb(n-w,j-t) for t in range(max(0,j-n+w),min(j,w)+1))
def check_C():
 out=[]
 for case in range(7):
  d=json.loads((R/f'C-integer-case{case}.json').read_text(encoding='utf-8'));ws=d['single_weights'];assert ws==list(range(58,111,4));J=d['J'];q0=d['Q0'];mb=d['maxB2'];assert 0<J<128
  D={int(w):a for w,a in d['D'].items()};L,expected=DCASES[case];assert D==expected;assert mb==(comb(L,2)+sum(a*K(L,2,w) for w,a in expected.items()))//128;assert J*4+58*128+sum(w*a for w,a in D.items())==128*121
  assert 16*(2*q0+J)+58**2*128+2*58*4*J+sum(w*w*a for w,a in D.items())==64*121*122
  # Unbounded coin DP, counting choices for a_j (j>=2). a_1 and a_0 are forced.
  maxq=q0+4*mb;dp=[[0]*(maxq+1) for _ in range(J+1)];dp[0][0]=1
  for j in range(2,len(ws)):
   cost=j*(j-1)//2
   for mass in range(j,J+1):
    for q in range(cost,maxq+1):dp[mass][q]+=dp[mass-j][q-cost]
  total=sum(dp[m][q0+4*b] for m in range(J+1) for b in range(mb+1));seen=set()
  for row in d['candidates']:
   b,*aa=row;assert len(aa)==14 and 0<=b<=mb and all(isinstance(a,int) and a>=0 for a in aa);assert sum(aa)==128 and aa[0]>0;assert sum(j*a for j,a in enumerate(aa))==J;assert sum(j*(j-1)//2*a for j,a in enumerate(aa))==q0+4*b;seen.add(tuple(row))
  assert len(seen)==len(d['candidates'])==total
  # Inclusion of ALL moment-feasible vectors proves completeness even without using further MW tests.
  out.append(dict(case=case,complete_moment_table=total));print('C COMPLETE',case,total,flush=True)
 return out

def check_R(n):
 data=json.loads((R/f'R{n}-gauss-integers.json').read_text(encoding='utf-8'));old=json.loads((R/f'R{n}-moment-integers.json').read_text(encoding='utf-8'));ws=old['weights'];assert ws==rws(n,7,(n-3)//2);base=ws[0];costs=[(w-base)//2 for w in ws];T=127;J=(64*n-base*T)//2;assert costs[:2]==[0,1];maxb=15
 q0=(32*n*(n+1)-base*base*T-4*base*J-4*J)//8;assert 8*q0+base*base*T+4*base*J+4*J==32*n*(n+1)
 expected={tuple(x['A'][str(w)] for w in ws):(i,x['B2']) for i,x in enumerate(data)};assert len(expected)==len(data);km=[[K(n,j,w) for w in ws] for j in range(n+1)];counts=[0]*len(ws);visited=0;valid=set();start=time.perf_counter()
 def walk(pos,mass,q,used):
  nonlocal visited
  if pos==1:
   bnum=q-q0
   if bnum<0 or bnum%8 or bnum>8*maxb:return
   counts[1]=J-mass;counts[0]=T-used-counts[1]
   if counts[0]<0:return
   visited+=1;G=1+sum((-1)**(w//2)*a for w,a in zip(ws,counts))
   if G not in [0,-64,-32,-16,16,32,64,128]:return
   for j in range(2,n+1):
    value=comb(n,j)+sum(a*c for a,c in zip(counts,km[j]))
    if value<0 or value%128:return
   tup=tuple(counts);assert tup in expected,('missing necessary distribution',n,tup);idx,b=expected[tup];assert b==bnum//8;valid.add(tup);return
  c=costs[pos];qcost=c*(c-1)//2
  for a in range(min((J-mass)//c,(q0+8*maxb-q)//qcost,T-used)+1):counts[pos]=a;walk(pos-1,mass+a*c,q+a*qcost,used+a)
 walk(len(ws)-1,0,0,0)
 assert valid==set(expected);assert visited==old['visited'];print('R COMPLETE',n,'moment vectors',visited,'Gauss/MW',len(valid),'seconds',round(time.perf_counter()-start,3),flush=True);return dict(n=n,moment_vectors=visited,complete_Gauss_MW_table=len(valid),seconds=time.perf_counter()-start)
if __name__=='__main__':
 start=time.perf_counter();out=dict(C=check_C(),R=[check_R(59),check_R(63)]);out['seconds']=time.perf_counter()-start;(R/'integer-table-verification.json').write_text(json.dumps(out,indent=2), encoding='utf-8');print('PASS all integer table completeness checks',out['seconds'],flush=True)
