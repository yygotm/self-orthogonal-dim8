"""Split enumerator LP with actual orbit marginals and all partition MacWilliams cuts.
Adapted from lemma20-97/partition_lp.py; no classification inputs.
"""
from models import *
from bmodels import coupled

def compact(M):
 best={}
 for row,b,label in zip(M.A,M.b,M.labels):
  key=tuple(row)
  if not any(row) and b>=0:continue
  if key not in best or b<best[key][0]:best[key]=(b,label)
 M.A=[list(row) for row in best];M.b=[v[0] for v in best.values()];M.labels=[v[1] for v in best.values()]
 return M

def split(G,n,k,d,w,coset=False):
 assert w<2*d and w in G.variables
 L=n-w;rd=d-w//2;rd+=rd%2
 rdiv=2
 if L==g(k-1,rd):rdiv=max(rdiv,rd&-rd)
 rso=rdiv>=4;rproj=L-g(k-2,rd)==1
 from dscreen import rweights
 R=ordinary(L,k-1,rd,rdiv,rso,True,rproj,[v for v in rweights(L,k-1,rd) if v%rdiv==0])
 if coset and w%4==2:pairs=[(a,b) for a in G.variables if a%4==0 for b in G.variables if b%4==2]
 else:pairs=[(a,b) for a in G.variables for b in G.variables if a<=b and a%4==b%4]
 cells=[]
 for a,b in pairs:
  if (w+a-b)%2:continue
  i=(w+a-b)//2;j=(a+b-w)//2
  if i%2 or not (0<=i<=w and 0<j<=L) or j not in R.variables:continue
  if coset and w%4==0 and a%4==0:
   dd=c4(d)-w//2;dd+=dd%2
   if j<dd or (j<2*dd and g(k-3,dd-j//2)>L-j):continue
  cells.append((a,b,i,j))
 M=Model(cells)
 for row,bb,label in zip(G.A,G.b,G.labels):
  co=dict(zip(G.variables,row));M.le([co[a]+co[b] for a,b,i,j in cells],bb-co.get(w,0),'global: '+label)
 for row,bb,label in zip(R.A,R.b,R.labels):
  co=dict(zip(R.variables,row));M.le([co[j] for a,b,i,j in cells],bb,'residual: '+label)
 mult=L-g(k-2,rd)
 M.le([K(L,2,j) for a,b,i,j in cells],(2**(k-1))*L*(mult-1)//2-comb(L,2),f'residual multiplicity<={mult}')
 KA=[[K(w,r,i) for i in range(w+1)] for r in range(w+1)]
 KB=[[K(L,s,j) for j in range(L+1)] for s in range(L+1)]
 cuts=[]
 for r in range(w+1):
  for s in range(L+1):
   kval=[(KA[r][i]+KA[r][w-i])*KB[s][j] for a,b,i,j in cells]
   const=(KA[r][0]+KA[r][w])*KB[s][0]
   ac=[int((r,s)==(i,j))+int((r,s)==(w-i,j)) for a,b,i,j in cells]
   fixedac=int((r,s)==(0,0))+int((r,s)==(w,0))
   co=[-v+2**k*t for v,t in zip(kval,ac)];bb=const-2**k*fixedac
   if any(co) or bb<0:cuts.append((r+s,r,s,co,bb,f'w{w}: dual>=code ({r},{s})'))
   if coset:
    sh=[((1 if a%4==0 else -1)*KA[r][i]+(1 if b%4==0 else -1)*KA[r][w-i])*KB[s][j] for a,b,i,j in cells]
    constsh=(KA[r][0]+(1 if w%4==0 else -1)*KA[r][w])*KB[s][0]
    co=[-v for v in sh]
    if any(co) or constsh<0:cuts.append((r+s,r,s,co,constsh,f'w{w}: shadow>=0 ({r},{s})'))
 return compact(M),cuts

def cut_solve(M,cuts,name,limit=300):
 print('START',name,'variables',len(M.variables),'rows',len(M.b),'cuts',len(cuts),flush=True)
 start=time.perf_counter();added=set();history=[]
 for it in range(60):
  r=M.solve(limit=90);history.append(dict(iteration=it,status=r['status'],rows=len(M.b),pivots=r['pivots'],seconds=r.get('seconds')))
  print('ITER',name,it,r['status'],'elapsed',round(time.perf_counter()-start,2),flush=True)
  if r['status']=='infeasible':break
  x=r['x'];viol=[]
  for ix,(deg,a,b,co,bb,label) in enumerate(cuts):
   if ix in added:continue
   value=sum(u*v for u,v in zip(co,x))-bb
   if value>0:viol.append((deg,-value,ix))
  if not viol:
   print('ALL_CUTS_FEASIBLE',name,flush=True);break
  viol.sort();degree=viol[0][0]
  for deg,neg,ix in [v for v in viol if v[0]==degree][:10]:
   _,a,b,co,bb,label=cuts[ix];M.le(co,bb,label);added.add(ix)
  if time.perf_counter()-start>limit:raise TimeoutError('split five-minute guard')
 else:raise TimeoutError('split iteration guard')
 M.save(name,r);(ROOT/(name+'-history.json')).write_text(json.dumps(history,indent=2),encoding='utf-8')
 return r

def Dmodel():
 M=ordinary(90,7,44,4,True,True,False,[44,48,52,56,60,64,68,72]);M.le([K(90,2,w) for w in M.variables],128*45-comb(90,2),'D B2<=45');return M
if __name__=='__main__':
 import argparse
 ap=argparse.ArgumentParser();ap.add_argument('kind',choices=['C','D']);ap.add_argument('anchors',nargs='+',type=int);args=ap.parse_args()
 for w in args.anchors:
  G=coupled() if args.kind=='C' else Dmodel();k,d=(8,42) if args.kind=='C' else (7,44)
  M,cuts=split(G,90,k,d,w,args.kind=='C');r=cut_solve(M,cuts,f'{args.kind}_split{w}')
  print('RESULT',args.kind,w,r['status'],flush=True)


