"""Independent certificate and model verification, rounds 4/5/6.
Imports only the independent verifier's arithmetic; never the solver/model builders.
"""
from verify_round12 import R,WS,K,g,norm,verify_template
from fractions import Fraction as Q
from math import comb
import json,time

def load(name):return json.loads((R/name).read_text(encoding='utf-8'))
def verify_dual(T,c):
 y={t['row']:t['multiplier'] for t in c['y']};assert len(y)==len(c['y']) and all(v>=0 for v in y.values())
 assert all(sum(v*T['A'][i][j] for i,v in y.items())>=0 for j in range(len(T['cells'])))
 co=[sum(v*T['B'][i][j] for i,v in y.items()) for j in range(14)];assert co==c['coefficients']
def verify_lp(M,res):
 if res['status']=='feasible':
  x=list(map(Q,res['x']));assert all(v>=0 for v in x);assert all(sum(a*v for a,v in zip(row,x))<=b for row,b in zip(M['A'],M['b']))
 else:
  assert res['status']=='infeasible';y={t['row']:t['multiplier'] for t in res['y']};assert all(v>=0 for v in y.values())
  assert all(sum(v*M['A'][i][j] for i,v in y.items())>=0 for j in range(len(M['variables'])))
  assert sum(v*M['b'][i] for i,v in y.items())<0
class Sys:
 def __init__(self,ws):self.ws=ws;self.A=[];self.b=[]
 def le(self,a,b):
  a,bs=norm(a,[b]);self.A.append(a);self.b.append(bs[0])
 def eq(self,a,b):self.le(a,b);self.le([-v for v in a],-b)
def radical_model(ix,src):
 a={int(w):v for w,v in src[ix]['A'].items()};G=1+sum((-1)**(w//2)*v for w,v in a.items());S=abs(G);h=2*(S.bit_length()-1)-7;ws=[w for w,v in a.items() if v and w%4==0];M=Sys(ws)
 M.eq([1]*len(ws),2**h-1)
 for j in range(1,64):
  row=[K(63,j,w) for w in ws];M.le([-v for v in row],comb(63,j));M.le([-v+2**h*int(w==j) for w,v in zip(ws,row)],comb(63,j))
 for w in ws:M.le([int(v==w) for v in ws],a[w])
 M.le([K(63,1,w) for w in ws],2**h*(63-g(h,32))-63)
 fail=[]
 for j in range(64):
  T=comb(63,j)+sum((-1)**(w//2)*v*K(63,j,w) for w,v in a.items());B=comb(63,j)+sum(v*K(63,j,w) for w,v in a.items());assert B%128==0
  if T%S:fail.append([j,T,S]);continue
  lower=max(abs(T)//S,B//128);M.le([-K(63,j,w) for w in ws],comb(63,j)-2**h*lower)
 return M,fail

def main():
 start=time.perf_counter();src=load('R63-gauss-integers.json');pairs=load('round2-surviving-pairs.json');left={p['R_index'] for p in pairs};V={ix:[src[ix]['A'][str(w)] for w in WS]+[src[ix]['B2'],1] for ix in left};state=load('round4-state.json');cuts=[];cache={};GS={0,-32,-16,-8,8,16,32,64}
 for c in state['cuts']:
  T=load(c['model']);verify_template(T);verify_dual(T,c);assert c['G'] in GS;cuts.append(c);gone=[]
  for ix in sorted(left):
   for w in WS:
    if w>=60 or not V[ix][WS.index(w)]:continue
    eliminated={cc['G'] for cc in cuts if cc['anchor']==w and sum(a*b for a,b in zip(cc['coefficients'],V[ix]))<0}
    if eliminated==GS:gone.append(ix);break
  assert gone==c['removed_after_all_G'];left.difference_update(gone)
 assert sorted(left)==state['left'];assert {p['pair_id'] for p in pairs if p['R_index'] in left}==set(state['pairs_left']);print('ROUND4 PASS',len(cuts),len(left),len(state['pairs_left']),flush=True)
 state5=load('round5-state.json');left5=[]
 for r in state5['results']:
  ix=r['R_index'];assert ix in left;M,fail=radical_model(ix,src)
  if fail:assert r['status']=='signed divisibility contradiction' and fail==r['fail'];continue
  saved=load(r['model']);assert saved['variables']==M.ws and saved['A']==M.A and saved['b']==M.b;res=load(r['result']);assert res['status']==r['status'];verify_lp(saved,res)
  if res['status']=='feasible':left5.append(ix)
 assert len(state5['results'])==len(left) and set(left5)==set(state5['left']);print('ROUND5 PASS',len(left5),len(state5['pairs_left']),flush=True)
 state6=load('round6-state.json');bad={ix:set() for ix in left5}
 for c in state6['cuts']:
  w=c['anchor'];name=f'round6-template-{w}.json'
  if name not in cache:T=load(name);assert T['radical_anchor'];verify_template(T);cache[name]=T
  T=cache[name];verify_dual(T,c)
  affected=[ix for ix in left5 if V[ix][WS.index(w)] and w not in bad[ix] and sum(a*b for a,b in zip(c['coefficients'],V[ix]))<0];assert affected==c['affected']
  for ix in affected:bad[ix].add(w)
 assert {str(ix):sorted(ws) for ix,ws in bad.items()}==state6['radical_exclusions']
 left6=[]
 for r in state6['results']:
  ix=r['R_index'];M,fail=radical_model(ix,src);assert not fail
  for w in sorted(bad[ix]):
   if w in M.ws:M.eq([int(v==w) for v in M.ws],0)
  saved=load(r['model']);assert saved['variables']==M.ws and saved['A']==M.A and saved['b']==M.b;res=load(r['result']);verify_lp(saved,res);assert res['status']==r['status']
  if res['status']=='feasible':left6.append(ix)
 assert set(left6)==set(state6['left']);pp=[p for p in load('round5-surviving-pairs.json') if p['R_index'] in left6];assert {p['pair_id'] for p in pp}==set(state6['pairs_left']);assert pp==load('round6-surviving-pairs.json')
 out=dict(round4_R=len(left),round5_R=len(left5),round6_R=len(left6),pairs_remaining=len(pp),seconds=time.perf_counter()-start);(R/'round456-verification.json').write_text(json.dumps(out,indent=2), encoding='utf-8');print('ROUND6 PASS AND DONE',out,flush=True)
if __name__=='__main__':main()
