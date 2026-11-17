from models import *
from enumerators import enumerate_distributions
from itertools import combinations_with_replacement

def compact(M):
 best={}
 for row,b,l in zip(M.A,M.b,M.labels):
  key=tuple(row)
  if not any(row) and b>=0:continue
  if key not in best or b<best[key][0]:best[key]=(b,l)
 M.A=[list(x) for x in best];M.b=[x[0] for x in best.values()];M.labels=[x[1] for x in best.values()];return M
AUD=json.loads((ROOT/'recursive-audit.json').read_text())
def rweights(n,k,d):
 rows=[e for e in AUD if e.get('effective',[])[:3]==[n,k,d] and e.get('effective',[0]*6)[5]]
 if rows:return min([e['weights'] for e in rows if 'weights' in e],key=len)
 return support(n,k,d,2,False,True,False)[0]

def aux_ok(c):
 b=c['B'][2];cnt={8:b+6,16:121-2*b,24:b}
 for j in range(32):
  v=comb(31,j)+sum(a*K(31,j,w) for w,a in cnt.items())
  if v<0 or v%128 or v//128<cnt.get(j,0):return False
 return True

def dsplit(A,b,w):
 L=121-w;rd=60-w//2;rd+=rd%2;ws=rweights(L,6,rd)
 pairs=[]
 for a,z in combinations_with_replacement(A,2):
  i=(w+a-z)//2;j=(a+z-w)//2
  if i%2 or not 0<=i<=w or j not in ws:continue
  if b>0 and w>64 and a>64 and z>64:continue # shorten a repeated point: no weights >64 in E119
  pairs.append((a,z,i,j))
 M=Model(pairs)
 for v,count in A.items():M.eq([int(a==v)+int(z==v) for a,z,i,j in pairs],count-int(v==w),f'D A{v}')
 M.eq([j for a,z,i,j in pairs],32*L,'R first moment')
 for t in range(2,L+1):
  row=[K(L,t,j) for a,z,i,j in pairs];M.le([-x for x in row],comb(L,t),f'R B{t}>=0')
  if t==2:M.le(row,64*b-comb(L,t),'R B2<=D B2')
 return compact(M)
if __name__=='__main__':
 data=json.loads((ROOT/'D121-integer.json').read_text())['candidates'];aux=[(i,c) for i,c in enumerate(data) if aux_ok(c)];print('AUX FILTER',len(data),len(aux),'B2',sorted({c['B'][2] for i,c in aux}),flush=True)
 left=[];results=[];start=time.perf_counter()
 for i,c in aux:
  A={int(w):a for w,a in c['A'].items() if a};b=c['B'][2];entry={'index':i,'A':A,'B2':b,'tests':[]}
  for w in sorted(A,reverse=True):
   M=dsplit(A,b,w);r=M.solve(limit=5);entry['tests'].append([w,r['status']])
   if r['status']=='infeasible':M.save(f'Dscreen-{i}',r);break
  else:left.append(entry)
  results.append(entry)
  if len(results)%100==0:print('SCREEN',len(results),'left',len(left),'seconds',time.perf_counter()-start,flush=True)
  if time.perf_counter()-start>600:raise TimeoutError('ten-minute campaign guard')
 (ROOT/'Dscreen-results.json').write_text(json.dumps(results));(ROOT/'Dscreen-survivors.json').write_text(json.dumps(left,indent=2))
 print('SURVIVORS',len(left),'seconds',time.perf_counter()-start,flush=True)
 for x in left:print(x['index'],x['A'],'B2',x['B2'],flush=True)

