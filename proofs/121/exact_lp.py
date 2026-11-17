"""Two-phase simplex over Fraction. Ax<=b, x>=0. Exact primal or Farkas output."""
from fractions import Fraction as Q
import time
class ExactLP:
 def __init__(self,A,b,c=None,limit=180):
  self.m=len(b);self.n=len(A[0]) if A else len(c or [])
  self.A=[[Q(v) for v in row] for row in A];self.b=list(map(Q,b))
  self.c=list(map(Q,c or [0]*self.n));self.start=time.perf_counter();self.limit=limit;self.pivots=0
  m,n=self.m,self.n
  self.B=[n+i for i in range(m)];self.N=list(range(n))+[-1]
  self.D=[[Q(0) for _ in range(n+2)] for __ in range(m+2)]
  for i in range(m):
   self.D[i][:n]=self.A[i][:];self.D[i][n]=-Q(1);self.D[i][n+1]=self.b[i]
  for j in range(n):self.D[m][j]=-self.c[j]
  self.D[m+1][n]=Q(1)
 def pivot(self,r,s):
  D=self.D;m,n=self.m,self.n;p=D[r][s]
  for i in range(m+2):
   if i==r or not D[i][s]:continue
   factor=D[i][s]/p
   for j in range(n+2):
    if j!=s and D[r][j]:D[i][j]-=D[r][j]*factor
  for j in range(n+2):
   if j!=s:D[r][j]/=p
  for i in range(m+2):
   if i!=r:D[i][s]/=-p
  D[r][s]=1/p
  self.B[r],self.N[s]=self.N[s],self.B[r];self.pivots+=1
  if time.perf_counter()-self.start>self.limit:raise TimeoutError(('LP time limit',self.pivots))
 def phase(self,phase):
  x=self.m+1 if phase==1 else self.m
  while True:
   cols=[j for j in range(self.n+1) if not (phase==2 and self.N[j]==-1)]
   # Bland entering rule prevents cycling under exact degeneracy.
   neg=[j for j in cols if self.D[x][j]<0]
   if not neg:return True
   s=min(neg,key=lambda j:self.N[j])
   rows=[i for i in range(self.m) if self.D[i][s]>0]
   if not rows:return False
   r=min(rows,key=lambda i:(self.D[i][self.n+1]/self.D[i][s],self.B[i]))
   self.pivot(r,s)
 def farkas(self):
  y=[Q(0)]*self.m
  for j,var in enumerate(self.N):
   if var>=self.n:y[var-self.n]=self.D[self.m+1][j]
  assert all(v>=0 for v in y)
  assert all(sum(y[i]*self.A[i][j] for i in range(self.m))>=0 for j in range(self.n))
  assert sum(y[i]*self.b[i] for i in range(self.m))<0
  return y
 def solve(self):
  if self.m:
   r=min(range(self.m),key=lambda i:self.D[i][self.n+1])
   if self.D[r][self.n+1]<0:
    self.pivot(r,self.n)
    assert self.phase(1),'auxiliary LP unbounded'
    if self.D[self.m+1][self.n+1]<0:
     return dict(status='infeasible',y=self.farkas(),pivots=self.pivots,seconds=time.perf_counter()-self.start)
    assert self.D[self.m+1][self.n+1]==0
    for i in range(self.m):
     if self.B[i]==-1:
      cols=[j for j in range(self.n+1) if self.D[i][j]]
      if cols:self.pivot(i,min(cols,key=lambda j:self.N[j]))
  bounded=self.phase(2)
  if not bounded:return dict(status='unbounded',pivots=self.pivots)
  x=[Q(0)]*self.n
  for i,var in enumerate(self.B):
   if 0<=var<self.n:x[var]=self.D[i][self.n+1]
  assert all(v>=0 for v in x)
  assert all(sum(a*v for a,v in zip(row,x))<=bb for row,bb in zip(self.A,self.b))
  return dict(status='feasible',x=x,objective=sum(a*b for a,b in zip(self.c,x)),
              pivots=self.pivots,seconds=time.perf_counter()-self.start)

def self_test():
 for A,b,expected in [([[1],[-1]],[1,-2],'infeasible'),
  ([[1],[-1]],[2,-1],'feasible'),([[1,1],[-1,0],[0,-1]],[1,-1,-1],'infeasible')]:
  assert ExactLP(A,b).solve()['status']==expected
 r=ExactLP([[1,1],[1,0],[0,1]],[4,3,2],[2,1]).solve()
 assert r['objective']==7 and r['x']==[3,1]
 return True
if __name__=='__main__':print('EXACT_SIMPLEX_SELF_TEST',self_test())

