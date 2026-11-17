from models import *
from dscreen import compact,rweights
DCASES=[(120,{60:112,64:15}),(121,{60:108,64:15,76:4}),(121,{60:104,64:15,68:8}),(121,{60:96,64:31}),(121,{60:98,64:27,68:2}),(121,{60:105,64:14,68:7,72:1}),(121,{60:100,64:23,68:4})]
S=[w for w in support(121,8,58)[0] if w%4==2 and w!=118]
def coupled(case):
 L,A=DCASES[case];ws=sorted(list(A)+S);M=Model(ws)
 M.eq([1]*len(ws),255,'C total')
 for w,a in A.items():M.eq({w:1},a,f'D A{w}')
 M.le({58:-1},-1,'minimum58 attained')
 bD=(comb(L,2)+sum(a*K(L,2,w) for w,a in A.items()))//128
 for j in range(1,122):
  row=[K(121,j,w) for w in ws]
  if j==1:M.eq(row,-121,'C full')
  else:M.le([-v for v in row],comb(121,j),f'C B{j}>=0')
  M.le([-v+256*int(w==j) for w,v in zip(ws,row)],comb(121,j),f'Cdual contains C {j}')
  dnum=comb(121,j)+sum(a*K(121,j,w) for w,a in A.items())
  M.le(row,2*dnum-comb(121,j),f'Cdual contained Ddual {j}')
  if j==2:M.le(row,256*bD-comb(121,j),'C B2<=D B2')
 return compact(M)
if __name__=='__main__':
 print('SINGLES',S,flush=True)
 for i in range(7):
  M=coupled(i);r=M.solve(limit=20);M.save(f'Ccase-{i}',r);print('CASE',i,r['status'],'seconds',r.get('seconds'),flush=True)
  if r['status']=='feasible': print(dict(zip(M.variables,map(str,r['x']))),flush=True)
