"""Independent verifier of the final 30-pair elimination (round22).
Imports only independent verifiers; no LP solver or search-side model builder.
"""
from verify_round910 import lifted,check_base_row,cweight,split_cut,key
from verify_round456 import load,verify_lp,R
from verification_models import split_C,DCASES,K
from verify_resume import System
from fractions import Fraction as Q
from math import comb,ceil,floor
from itertools import combinations
from functools import lru_cache
import json,time,re,sys
SRC=load('R63-gauss-integers.json')
@lru_cache(None)
def ctable(case):return load(f'C-integer-case{case}.json')

def verify_table(prefix,case,ix,P,exc):
 t=load(prefix+'-table.json');data=ctable(case);ws=data['single_weights'];active=sorted(({58}|{v for c in P['variables'] if c['kind']=='D' for v in c['cell'][:2]})-set(exc));assert active==t['active'] and exc==t['excluded'];ids=[i for i,e in enumerate(data['candidates']) if e[0]>=SRC[ix]['B2'] and all(e[j+1]==0 for j,w in enumerate(ws) if w not in active)];assert ids==t['source_indices'];N=System(P['variables']);D={int(w):a for w,a in data['D'].items()}
 if not ids:N.le([0]*len(N.variables),-1);assert not t['bounds'];return N,t
 singles=[w for w in active if w%4==2];fs=[('A '+','.join(map(str,ww)),{w:1 for w in ww},0,1) for size in [1,2] for ww in combinations(singles,size)];fs += [(f'B{j}',{w:K(121,j,w) for w in active},comb(121,j),256) for j in range(1,17)]
 assert len(fs)==len(t['bounds'])
 for (label,f,c,s),saved in zip(fs,t['bounds']):
  vals=[(c+sum(f.get(w,0)*a for w,a in D.items())+sum(f.get(w,0)*a for w,a in zip(ws,data['candidates'][ci][1:])))//s for ci in ids];lo=min(vals);hi=max(vals);expected=dict(label=label,coefficients={str(w):a for w,a in f.items()},constant=c,scale=s,lower=lo,upper=hi);assert saved==expected
  co=[f.get(v['cell'][0],0)+f.get(v['cell'][1],0) if v['kind']=='D' else 0 for v in N.variables];fixed=c+f.get(58,0);N.le(co,s*hi-fixed);N.le([-v for v in co],fixed-s*lo)
 return N,t

@lru_cache(None)
def verify_C_test(case,ci):
 data=ctable(case);row=data['candidates'][ci];A={int(w):a for w,a in data['D'].items()};A.update(dict(zip(data['single_weights'],row[1:])));s=load(f'round20-C{case}-{ci}-summary.json');assert s['status']=='infeasible' and A.get(62,0)>0;active=sorted(w for w,a in A.items() if a);M=split_C(case,62,active=active,fixed=A);ws={c[3] for c in M.variables};src=load('R59-gauss-integers.json');ids=load('R59-universal.json')['left'];eligible=[i for i in ids if src[i]['B2']<=row[0] and all(not a or int(w) in ws for w,a in src[i]['A'].items())];assert eligible==s['eligible_R59_indices'] and sorted(ws)==s['allowed_R59_weights'];assert [e['R59_index'] for e in s['tests']]==eligible
 for e in s['tests']:
  N=System(M.variables);N.A=M.A[:];N.b=M.b[:]
  for j,count in src[e['R59_index']]['A'].items():N.eq([int(c[3]==int(j)) for c in N.variables],count)
  saved=load(e['name']+'-model.json');assert N.variables==saved['variables'] and N.A==saved['A'][:len(N.A)] and N.b==saved['b'][:len(N.b)]
  for co,b,label in zip(saved['A'][len(N.A):],saved['b'][len(N.b):],saved['labels'][len(N.b):]):
   r,t=map(int,re.findall(r'\((\d+),(\d+)\)',label)[-1]);aa,bb=split_cut(N.variables,62,r,t,'shadow' in label);assert key(co,b)==key(aa,bb)
  result=load(e['name']+'-result.json');assert result['status']=='infeasible' and e['status']=='infeasible';verify_lp(saved,result)
 return len(eligible)

def main():
 start=time.perf_counter();r10=load('round10-state.json');assert r10['complete'];inputs={(e['case'],e['R_index']):e for e in r10['results'] if e['status']!='infeasible'};state=load('round22-state.json');assert state['complete'] and not state['pairs_left'];assert {(e['case'],e['R_index']) for e in state['results']}==set(inputs);counts=dict(pairs=0,C_fixed=0,dual_bounds=0,C_profiles_using_R59=0,R59_branches=0)
 for e in state['results']:
  case,ix=e['case'],e['R_index'];source=inputs[case,ix];P=load(source['root_name']+'-model.json');_,meta=lifted(case,ix);N=System(P['variables']);N.A=P['A'][:];N.b=P['b'][:];exc=source['excluded'][:]
  if case==1:
   for w in sorted({v for c in P['variables'] if c['kind']=='D' for v in c['cell'][:2] if v%4==2 and v>78 and v not in exc}):N.eq(cweight(P['variables'],w),0);exc.append(w)
   N.le([-a-b+4*c for a,b,c in zip(cweight(P['variables'],66),cweight(P['variables'],70),cweight(P['variables'],78))],-4)
  prefix=f'round22-case{case}-R{ix}';T,tab=verify_table(prefix,case,ix,P,exc);N.A+=T.A;N.b+=T.b;base=load(e['base']+'-model.json');assert N.variables==base['variables'] and N.A==base['A'][:len(N.A)] and N.b==base['b'][:len(N.b)]
  for co,b,label in zip(base['A'][len(N.A):],base['b'][len(N.b):],base['labels'][len(N.b):]):check_base_row(co,b,label,P,meta,exc)
  rr=load(e['base']+'-result.json');verify_lp(base,rr)
  if rr['status']=='infeasible':assert e['status']=='infeasible' and not e['tests'];counts['pairs']+=1;continue
  bd=load(e['bounds']);assert bd['initial_indices']==tab['source_indices'];ids=bd['initial_indices'][:];data=ctable(case);wi={w:j+1 for j,w in enumerate(data['single_weights'])}
  for cut in bd['bounds']:
   ww=cut['weights'];co=[sum(cweight(P['variables'],w)[i] for w in ww) for i in range(len(P['variables']))];constant=int(58 in ww);assert co==cut['coefficients'] and constant==cut['constant'];sign=cut['sign'];assert sign in [-1,1];y={v['row']:Q(v['value']) for v in cut['dual']};assert len(y)==len(cut['dual']) and all(v>=0 and 0<=i<len(base['b']) for i,v in y.items());obj=[sign*v for v in co]
   assert all(sum(v*base['A'][i][j] for i,v in y.items())>=obj[j] for j in range(len(obj)));o=sum(v*base['b'][i] for i,v in y.items());assert o==Q(cut['optimum']);value=constant+sign*o;b=floor(value) if sign==1 else ceil(value);assert b==cut['integer_bound'];ids=[ci for ci in ids if (sum(data['candidates'][ci][wi[w]] for w in ww)<=b if sign==1 else sum(data['candidates'][ci][wi[w]] for w in ww)>=b)];counts['dual_bounds']+=1
  assert ids==bd['final_indices'] and [t['C_index'] for t in e['tests']]==ids and not e['remaining_C']
  for t in e['tests']:
   ci=t['C_index'];A={int(w):a for w,a in data['D'].items()};A.update(dict(zip(data['single_weights'],data['candidates'][ci][1:])));NN=System(P['variables']);NN.A=base['A'][:];NN.b=base['b'][:]
   for w,a in A.items():NN.eq(cweight(P['variables'],w),a-int(w==58))
   saved=load(t['root_name']+'-model.json');assert NN.variables==saved['variables'] and NN.A==saved['A'][:len(NN.A)] and NN.b==saved['b'][:len(NN.b)]
   for co,b,label in zip(saved['A'][len(NN.A):],saved['b'][len(NN.b):],saved['labels'][len(NN.b):]):check_base_row(co,b,label,P,meta,exc)
   result=load(t['root_name']+'-result.json');verify_lp(saved,result);counts['C_fixed']+=1
   if result['status']=='feasible':
    if t.get('hand_lemma'):assert case==1 and ci==247 and t['hand_lemma']=='subcode-proof.md section31'
    else:assert t['C_test']==load(f'round20-C{case}-{ci}-summary.json');counts['R59_branches']+=verify_C_test(case,ci);counts['C_profiles_using_R59']+=1
   assert t['status']=='infeasible'
  counts['pairs']+=1;print('ROUND22 VERIFIED',counts['pairs'],case,ix,'C profiles',len(ids),'seconds',round(time.perf_counter()-start,3),flush=True)
 counts['seconds']=time.perf_counter()-start;counts['remaining_pairs']=0;(R/'round22-verification.json').write_text(json.dumps(counts,indent=2), encoding='utf-8');print('PASS FINAL THIRTY PAIRS',counts,flush=True)
if __name__=='__main__':main()
