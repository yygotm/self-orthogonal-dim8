"""Independent verifier for the resumed3,421-pair campaign.
No solver or model-builder imports. Reconstructs the base model and every split
Krawtchouk inequality; checks each pair's fixed residual marginals and provenance.
"""
from pathlib import Path
from fractions import Fraction
from math import comb,gcd,lcm
from functools import lru_cache
from collections import Counter
import hashlib,json,sys,time
R=Path(__file__).resolve().parent
DCASES=[(120,{60:112,64:15}),(121,{60:108,64:15,76:4}),(121,{60:104,64:15,68:8}),(121,{60:96,64:31}),(121,{60:98,64:27,68:2}),(121,{60:105,64:14,68:7,72:1}),(121,{60:100,64:23,68:4})]
S=list(range(58,111,4));RWS=[30,32,34,36,38,40,44,46,48,52,56,62]
@lru_cache(None)
def K(n,j,w):return sum((-1)**s*comb(w,s)*comb(n-w,j-s) for s in range(max(0,j-n+w),min(j,w)+1))
def norm(row,b):
 d=gcd(*[abs(x) for x in row+[b]]) or 1
 return [x//d for x in row],b//d
class System:
 def __init__(self,variables):self.variables=variables;self.A=[];self.b=[]
 def le(self,row,b):
  row,b=norm(row,b);self.A.append(row);self.b.append(b)
 def eq(self,row,b):self.le(row,b);self.le([-v for v in row],-b)
 def compact(self):
  best={}
  for row,b in zip(self.A,self.b):
   if not any(row) and b>=0:continue
   key=tuple(row)
   if key not in best or b<best[key]:best[key]=b
  self.A=[list(row) for row in best];self.b=list(best.values())

def rebuild(case,excluded):
 L,D=DCASES[case];ws=sorted(list(D)+S);G=System(ws);G.eq([1]*len(ws),255)
 for w,a in D.items():G.eq([int(v==w) for v in ws],a)
 G.le([-int(v==58) for v in ws],-1)
 bd=(comb(L,2)+sum(a*K(L,2,w) for w,a in D.items()))//128
 for j in range(1,122):
  row=[K(121,j,w) for w in ws]
  if j==1:G.eq(row,-121)
  else:G.le([-v for v in row],comb(121,j))
  G.le([-v+256*int(w==j) for w,v in zip(ws,row)],comb(121,j))
  dn=comb(121,j)+sum(a*K(121,j,w) for w,a in D.items());G.le(row,2*dn-comb(121,j))
  if j==2:G.le(row,256*bd-comb(121,j))
 G.compact()
 for w in excluded:G.eq([int(v==w) for v in ws],0)
 Q=System(RWS);Q.eq([1]*len(RWS),127)
 for j in range(1,64):
  row=[K(63,j,w) for w in RWS]
  if j==1:Q.eq(row,-63)
  else:Q.le([-v for v in row],comb(63,j))
 cells=[]
 for a in ws:
  if a%4:continue
  for b in ws:
   if b%4!=2:continue
   i=(58+a-b)//2;j=(a+b-58)//2
   if i%2==0 and 0<=i<=58 and j in RWS:cells.append([a,b,i,j])
 M=System(cells)
 for row,b in zip(G.A,G.b):
  c=dict(zip(ws,row));M.le([c[a]+c[z] for a,z,i,j in cells],b-c[58])
 for row,b in zip(Q.A,Q.b):
  c=dict(zip(RWS,row));M.le([c[j] for a,z,i,j in cells],b)
 M.le([K(63,2,j) for a,z,i,j in cells],128*63-comb(63,2));M.compact()
 cuts=[]
 for r in range(59):
  for s in range(64):
   co=[];shadow=[]
   const=(K(58,r,0)+K(58,r,58))*K(63,s,0)
   fixed=int((r,s)==(0,0))+int((r,s)==(58,0))
   for a,b,i,j in cells:
    kval=(K(58,r,i)+K(58,r,58-i))*K(63,s,j)
    ac=int((r,s)==(i,j))+int((r,s)==(58-i,j));co.append(-kval+256*ac)
    shadow.append(-(K(58,r,i)-K(58,r,58-i))*K(63,s,j))
   bb=const-256*fixed
   if any(co) or bb<0:cuts.append((co,bb))
   shconst=(K(58,r,0)-K(58,r,58))*K(63,s,0)
   if any(shadow) or shconst<0:cuts.append((shadow,shconst))
 return M,cuts

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
if __name__=='__main__':
 start=time.perf_counter();prov=json.loads((R/'fixedR-resume-provenance.json').read_text(encoding='utf-8'))
 # The old campaign hashes its historical proof, preserved before the authorized continuation.
 for name,h in prov['input_sha256'].items():
  historical='subcode-proof-before-1300.md' if name=='subcode-proof.md' else name
  assert sha(R/historical)==h,(name,historical)
 cat=json.loads((R/'fixedR-pair-catalog.json').read_text(encoding='utf-8'));summary=json.loads((R/'fixedR-resume-summary.json').read_text(encoding='utf-8'));results=json.loads((R/'fixedR-resume-results.json').read_text(encoding='utf-8'));pending=json.loads((R/'fixedR-resume-pending.json').read_text(encoding='utf-8'));source=json.loads((R/'R63-gauss-integers.json').read_text(encoding='utf-8'));ids=json.loads((R/'R63-universal.json').read_text(encoding='utf-8'))['left'];ex=json.loads((R/'iter-summary.json').read_text(encoding='utf-8'))
 expected=[]
 for case in range(7):
  compatible=set(json.loads((R/f'R63-compatible-case{case}.json').read_text(encoding='utf-8')))
  expected.extend((case,i) for i in ids if i in compatible)
 assert len(expected)==3421 and [(p['case'],p['R_index']) for p in cat]==expected
 for p in cat:
  assert p['residual_distribution']==source[p['R_index']]['A'] and p['residual_B2']==source[p['R_index']]['B2'];assert p['residual_source_index']==p['R_index'];assert not p['uses_LinCode_classification']
 resultids={x['pair_id'] for x in results};pendingids={x['pair_id'] for x in pending};assert len(resultids)==len(results) and resultids.isdisjoint(pendingids) and resultids|pendingids=={p['pair_id'] for p in cat}
 assert summary['completed']==len(results) and summary['pending']==len(pending)
 bases={};counters=Counter();casecounts=Counter();integer_x=0;integer_C=0
 for rr in results:
  p=cat[rr['pair_number']-1];case=p['case'];ix=p['R_index'];assert rr['pair_id']==p['pair_id'] and rr['case']==case and rr['R_index']==ix and not rr['uses_LinCode_classification']
  if case not in bases:
   M,cuts=rebuild(case,ex[case]['excluded']);saved=json.loads((R/f'fixedR-base-case{case}-model.json').read_text(encoding='utf-8'));assert M.variables==saved['variables'] and M.A==saved['A'] and M.b==saved['b'],'independent base reconstruction failed'
   savedcuts=json.loads((R/f'fixedR-cuts-case{case}.json').read_text(encoding='utf-8'));assert [(x[3],x[4]) for x in savedcuts]==cuts,'independent split cut reconstruction failed'
   allowed={(tuple(norm(co,b)[0]),norm(co,b)[1]) for co,b in cuts};bases[case]=(M,cuts,allowed)
  M,cuts,allowed=bases[case];AA=M.A[:];bb=M.b[:]
  for j,count in source[ix]['A'].items():
   co=[int(jj==int(j)) for a,b,i,jj in M.variables]
   for sign in [1,-1]:
    row,v=norm([sign*a for a in co],sign*count);AA.append(row);bb.append(v)
  if '--negative-control' in sys.argv:bb[-1]-=1
  assert sha(R/rr['model'])==rr['model_sha256'] and sha(R/rr['result'])==rr['result_sha256']
  mm=json.loads((R/rr['model']).read_text(encoding='utf-8'));result=json.loads((R/rr['result']).read_text(encoding='utf-8'));assert mm['variables']==M.variables
  assert mm['A'][:len(AA)]==AA and mm['b'][:len(bb)]==bb,'fixed residual margins mismatch'
  assert all((tuple(row),b) in allowed for row,b in zip(mm['A'][len(AA):],mm['b'][len(bb):]))
  assert result['status']==rr['status'];counters[result['status']]+=1;casecounts[(case,result['status'])]+=1
  if result['status']=='feasible':
   x=list(map(Fraction,result['x']));den=lcm(*[a.denominator for a in x]);xx=[int(a*den) for a in x];assert all(v>=0 for v in xx)
   assert all(sum(a*v for a,v in zip(row,xx))<=b*den for row,b in zip(mm['A'],mm['b']))
   assert all(sum(a*v for a,v in zip(co,xx))<=b*den for co,b in cuts),'a split inequality outside saved LP is violated'
   cw=Counter({58:Fraction(1)})
   for (a,b,i,j),v in zip(M.variables,x):cw[a]+=v;cw[b]+=v
   assert {str(w):str(v) for w,v in sorted(cw.items()) if v}==rr['C_primal_distribution']
   integer_x+=all(v.denominator==1 for v in x);integer_C+=all(v.denominator==1 for v in cw.values())
  else:
   assert result['status']=='infeasible';y=[0]*len(mm['b'])
   for term in result['y']:y[term['row']]=term['multiplier']
   assert all(v>=0 for v in y)
   assert all(sum(y[i]*mm['A'][i][j] for i in range(len(y)))>=0 for j in range(len(M.variables)))
   assert sum(v*b for v,b in zip(y,mm['b']))<0
  if sum(counters.values())%250==0:print('VERIFIED',sum(counters.values()),dict(counters),'seconds',round(time.perf_counter()-start,2),flush=True)
 assert counters['feasible']==summary['feasible'] and counters['infeasible']==summary['infeasible']
 for row in summary['per_case']:
  assert row['feasible']==casecounts[(row['case'],'feasible')] and row['infeasible']==casecounts[(row['case'],'infeasible')]
 feasible=json.loads((R/'fixedR-resume-feasible.json').read_text(encoding='utf-8'));assert {x['pair_id'] for x in feasible}=={x['pair_id'] for x in results if x['status']=='feasible'}
 out=dict(total=3421,completed=len(results),pending=len(pending),feasible=counters['feasible'],infeasible=counters['infeasible'],integer_primal_solutions=integer_x,integer_C_marginals=integer_C,independently_rebuilt_cases=len(bases),all_split_inequalities_checked=True,seconds=time.perf_counter()-start)
 (R/'fixedR-resume-verification.json').write_text(json.dumps(out,indent=2), encoding='utf-8');print('PASS',json.dumps(out),flush=True)
