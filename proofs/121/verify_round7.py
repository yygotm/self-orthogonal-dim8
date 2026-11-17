"""Verify integer/parity bound certificates without optimization or solver imports."""
from verify_round456 import R,K,load,verify_lp
from verify_round12 import norm
from fractions import Fraction as Q
from math import comb,ceil,floor
import time,json
start=time.perf_counter();src=load('R63-gauss-integers.json');state=load('round7-state.json');count=0
for entry in state['results']:
 ix=entry['R_index'];old=load(f'round6-R{ix}-model.json');M=load(entry['model']);cuts=load(entry['certificates']);A=old['A'][:];b=old['b'][:];ws=old['variables'];dist={int(w):v for w,v in src[ix]['A'].items()};G=1+sum((-1)**(w//2)*v for w,v in dist.items());S=abs(G);h=2*(S.bit_length()-1)-7
 for cut in cuts:
  f=cut['function'];j=int(f['name'][1:])
  if f['name'].startswith('A'):expected=dict(name=f'A{j}',co=[int(w==j) for w in ws],constant=0,scale=1,period=1,remainder=0)
  else:
   T=comb(63,j)+sum((-1)**(w//2)*v*K(63,j,w) for w,v in dist.items());assert T%S==0;expected=dict(name=f'B{j}',co=[K(63,j,w) for w in ws],constant=comb(63,j),scale=2**h,period=2,remainder=(T//S)%2)
  assert f==expected and cut['prefix_rows']==len(b)
  sign=1 if cut['kind']=='upper' else -1;c=[sign*v for v in f['co']];assert c==cut['objective'];y={v['row']:Q(v['value']) for v in cut['y']};assert all(v>=0 and i<len(b) for i,v in y.items())
  assert all(sum(v*A[i][j] for i,v in y.items())>=c[j] for j in range(len(ws)))
  o=sum(v*b[i] for i,v in y.items());assert o==Q(cut['optimum']);bound=(Q(f['constant'])+sign*o)/f['scale'];assert bound==Q(cut['raw_bound']);p=f['period'];r=f['remainder'];rounded=r+p*(floor((bound-r)/p) if sign==1 else ceil((bound-r)/p));assert rounded==cut['rounded_bound']
  rhs=(f['scale']*rounded-f['constant'])*sign;row,bb=norm(c,[rhs]);A.append(row);b.append(bb[0]);count+=1
 assert A==M['A'] and b==M['b'] and ws==M['variables'];res=load(entry['result']);assert res['status']==entry['status'];verify_lp(M,res)
print('PASS',len(state['results']),'R models',count,'certified integer/parity cuts; complete',state['complete'],'seconds',time.perf_counter()-start)
(R/'round7-verification.json').write_text(json.dumps(dict(R_models=len(state['results']),cuts=count,complete=state['complete'],seconds=time.perf_counter()-start),indent=2), encoding='utf-8')
