"""Independent model/certificate checker for lifted radical and shared anchors.
No optimization or model-builder imports. Proof sections 18 and 19.
"""
from verify_resume import System,norm,K,DCASES
from verify_round456 import load,verify_lp,R
from verify_round12 import allowed,g
from fractions import Fraction as Q
from math import comb
from functools import lru_cache
import re,json,time,sys
SOURCE=load('R63-gauss-integers.json')

def key(a,b):
 a,b=norm(a,b);return (tuple(a),b)

def split_cut(cells,w,r,s,shadow=False):
 L=121-w
 if shadow:
  return [-((1 if a%4==0 else -1)*K(w,r,i)+(1 if b%4==0 else -1)*K(w,r,w-i))*K(L,s,j) for a,b,i,j in cells],(K(w,r,0)-K(w,r,w))*comb(L,s)
 return [-(K(w,r,i)+K(w,r,w-i))*K(L,s,j)+256*(int((r,s)==(i,j))+int((r,s)==(w-i,j))) for a,b,i,j in cells],(K(w,r,0)+K(w,r,w))*comb(L,s)-256*(int((r,s)==(0,0))+int((r,s)==(w,0)))

def lifted_cut(cells,Y,h,S,r,s,label):
 nx=len(cells);ny=len(Y)
 if 'Csplit ' in label:
  co,b=split_cut(cells,58,r,s,'shadow' in label);return co+[0]*ny,b
 kd=[K(58,r,i)*K(63,s,j) for a,b,i,j in cells];kh=[kd[i] for i in Y];sd=[(-1)**(j//2)*v for (a,b,i,j),v in zip(cells,kd)];c=comb(58,r)*comb(63,s)
 if label.startswith('Hdual>=C'):
  ac=[int((r,s)==(i,j))+int((r,s)==(58-i,j)) for a,b,i,j in cells];return [2**h*v for v in ac]+[-v for v in kh],c-2**h*(int((r,s)==(0,0))+int((r,s)==(58,0)))
 if label.startswith('Hdual>=Ddual'):return kd+[-(128//2**h)*v for v in kh],(128//2**h-1)*c
 if label.startswith('Lifted Gauss plus'):return [2**h*v for v in sd]+[-S*v for v in kh],(S-2**h)*c
 if label.startswith('Lifted Gauss minus'):return [-2**h*v for v in sd]+[-S*v for v in kh],(S+2**h)*c
 raise ValueError(label)

def validate_lifted_metadata(meta,case,ix):
 # The two previously verified parent models must belong to this exact pair.
 assert meta['case']==case and meta['R_index']==ix, 'lifted metadata pair mismatch'
 assert meta['original_C']==f'fixedR-case{case}-R{ix}-model.json', 'lifted original_C mismatch'
 assert meta['source_H']==f'round7-R{ix}-model.json', 'lifted source_H mismatch'

@lru_cache(None)
def lifted(case,ix):
 meta=load(f'round9-case{case}-R{ix}-metadata.json');validate_lifted_metadata(meta,case,ix)
 old=load(f'fixedR-case{case}-R{ix}-model.json');H=load(f'round7-R{ix}-model.json');A=SOURCE[ix]['A'];exc=load('iter-summary.json')[case]['excluded'];keep=[i for i,(a,b,t,j) in enumerate(old['variables']) if A[str(j)] and b not in exc];cells=[old['variables'][i] for i in keep];Y=[i for i,(a,b,t,j) in enumerate(cells) if j%4==0 and j in H['variables']]
 G=1+sum((-1)**(int(w)//2)*v for w,v in A.items());S=abs(G);h=2*(S.bit_length()-1)-7;assert S==2**((h+7)//2) and h in [1,3,5];assert max(int(w) for w,v in A.items() if v)<=48
 assert meta['D_cells']==cells and meta['H_cell_indices']==Y and meta['original_variable_indices']==keep and (meta['G'],meta['S'],meta['h'])==(G,S,h)
 variables=[dict(kind='D',cell=c) for c in cells]+[dict(kind='H',cell=cells[i]) for i in Y];M=System(variables);nx=len(cells);ny=len(Y)
 for row,b in zip(old['A'],old['b']):M.le([row[i] for i in keep]+[0]*ny,b)
 for row,b in zip(H['A'],H['b']):
  co=dict(zip(H['variables'],row));M.le([0]*nx+[co[cells[i][3]] for i in Y],b)
 for yi,i in enumerate(Y):
  co=[0]*(nx+ny);co[i]=-1;co[nx+yi]=1;M.le(co,0)
 for j in range(1,122):M.le([0]*nx+[-K(121,j,cells[i][0])+2**h*int(cells[i][0]==j) for i in Y],comb(121,j))
 M.le([0]*nx+[K(121,1,cells[i][0]) for i in Y],2**h*(121-g(h,60))-121)
 for j in range(1,59):M.le([0]*nx+[-K(58,j,cells[i][2])+2**h*int(cells[i][2]==j) for i in Y],comb(58,j))
 M.compact();saved=load(f'round9-case{case}-R{ix}-model.json');assert variables==saved['variables'];assert M.A==saved['A'][:len(M.A)] and M.b==saved['b'][:len(M.b)]
 for row,b,label in zip(saved['A'][len(M.A):],saved['b'][len(M.b):],saved['labels'][len(M.b):]):
  r,s=map(int,re.findall(r'\((\d+),(\d+)\)',label)[-1]);co,bb=lifted_cut(cells,Y,h,S,r,s,label);assert key(row,b)==key(co,bb),label
 res=load(f'round9-case{case}-R{ix}-result.json');verify_lp(saved,res)
 return saved,meta

def cweight(variables,w):return [int(v['cell'][0]==w)+int(v['cell'][1]==w) if v['kind']=='D' else 0 for v in variables]

def check_base_row(row,b,label,base,meta,excluded):
 # Accept a previously verified base inequality or a newly justified zero marginal.
 if key(row,b) in {(tuple(a),bb) for a,bb in zip(base['A'],base['b'])}:return
 if label.startswith('proved absent C weight '):
  w=int(re.search(r'weight (\d+)',label)[1]);assert w in excluded;sgn=-1 if label.endswith('>=') else 1;assert key(row,b)==key([sgn*v for v in cweight(base['variables'],w)],0);return
 r,s=map(int,re.findall(r'\((\d+),(\d+)\)',label)[-1]);co,bb=lifted_cut(meta['D_cells'],meta['H_cell_indices'],meta['h'],meta['S'],r,s,label);assert key(row,b)==key(co,bb),label

def audit_rws(n,k,d):
 audit=load('recursive-audit.json');entries=[e for e in audit if e.get('effective',[])[:3]==[n,k,d] and e.get('effective',[0]*6)[5] and 'weights' in e]
 if entries:return min((e['weights'] for e in entries),key=len)
 return [w for w in range(d,n+1,2) if not (w<2*d and g(k-1,d-w//2)>n-w)]

def check_joint(name,metadata,base,meta,excluded,G):
 M=load(name+'-model.json');info=load(metadata);w=info['anchor'];L=121-w;rd=58-w//2;rd+=rd%2;nx=len(base['variables']);active=sorted(({58}|{x for v in base['variables'] if v['kind']=='D' for x in v['cell'][:2]})-set(excluded));assert info['active_C_weights']==active and info['excluded_C_weights']==excluded and info['base_variables']==nx
 rdiv=2 if L!=g(7,rd) else max(2,rd&-rd);rws=set(audit_rws(L,7,rd))&set(allowed(L,7,rd,2));rws={j for j in rws if j%rdiv==0};cells=[]
 for a in active:
  if a%4:continue
  for b in active:
   if b%4!=2:continue
   i=(w+a-b)//2;j=(a+b-w)//2
   if i%2==0 and 0<=i<=w and 0<j<=L and j in rws:cells.append([a,b,i,j])
 assert cells==info['other_cells'];assert M['variables']==[dict(kind='base',variable=v) for v in base['variables']]+[dict(kind='other',cell=c) for c in cells]
 for row,bb,label in zip(M['A'],M['b'],M['labels']):
  if label.startswith('base '):assert not any(row[nx:]);check_base_row(row[:nx],bb,label[5:],base,meta,excluded);continue
  co=[0]*nx;b=0
  if label.startswith('same C A'):
   v=int(re.search(r'A(\d+)',label)[1]);co=cweight(base['variables'],v)+[-int(a==v)-int(z==v) for a,z,i,j in cells];b=int(v==w)-int(v==58)
   if label.endswith('>='):co=[-v for v in co];b=-b
  elif label.startswith('other residual Gauss'):
   assert G is not None;co+=[(-1)**(j//2) for a,b,i,j in cells];b=G-1
   if label.endswith('>='):co=[-v for v in co];b=-b
  elif label.startswith('other w'):
   r,s=map(int,re.findall(r'\((\d+),(\d+)\)',label)[-1]);v,b=split_cut(cells,w,r,s,'shadow' in label);co+=v
  elif label.startswith('other residual multiplicity'):
   mult=L-g(6,rd);co+=[K(L,2,j) for a,b,i,j in cells];b=128*L*(mult-1)//2-comb(L,2)
  elif label.startswith('other residual: A0'):
   co+=[1]*len(cells);b=127
   if label.endswith('>='):co=[-v for v in co];b=-b
  elif label.startswith('other residual: B'):
   t=int(re.search(r'B(\d+)',label)[1]);v=[K(L,t,j) for a,b,i,j in cells]
   if re.search(r'B\d+=0',label):
    assert t==1 or (t==2 and L-g(6,rd)==1);co+=v;b=-comb(L,t)
    if label.endswith('>='):co=[-v for v in co];b=-b
   else:
    co += [-v+ (128*int(j==t) if '>=A' in label else 0) for (a,b,i,j),v in zip(cells,v)];b=comb(L,t)
    if '>=A' in label:assert rdiv%4==0
  else:raise ValueError(label)
  assert key(row,bb)==key(co,b),(name,label)
 res=load(name+'-result.json');verify_lp(M,res);return res

def main():
 start=time.perf_counter();state9=load('round9-state.json');left=[]
 for e in state9['results']:
  M,meta=lifted(e['case'],e['R_index']);res=load(e['result']);assert res['status']==e['status']
  if res['status']=='feasible':left.append((e['case'],e['R_index']))
 assert set(left)=={(p['case'],p['R_index']) for p in load('round9-surviving-pairs.json')};print('ROUND9 PASS',len(state9['results']),len(left),flush=True)
 state10=load('round10-state.json');gone=[];branches=0
 for e in state10['results']:
  case,ix=e['case'],e['R_index'];assert (case,ix) in left;base,meta=lifted(case,ix);exc=[]
  for event in e['history']:
   tests=event['tests'];seen=set();free=None
   for t in tests:
    res=check_joint(t['name'],event['metadata'],base,meta,exc,t['G']);assert res['status']==t['status'];branches+=1
    if t['G'] is None:free=res['status']
    elif res['status']=='infeasible':seen.add(t['G'])
   if event['status']=='infeasible':
    assert free=='infeasible' or seen=={0,-64,-32,-16,16,32,64,128};exc.append(event['anchor'])
  assert exc==e['excluded']
  if e['status']!='unresolved':
   M=load(e['root_name']+'-model.json');assert M['variables']==base['variables']
   for row,b,label in zip(M['A'],M['b'],M['labels']):check_base_row(row,b,label,base,meta,exc)
   res=load(e['root_name']+'-result.json');verify_lp(M,res);assert res['status']==e['status']
  if e['status']=='infeasible':gone.append((case,ix))
  if len(gone)%20==0:print('ROUND10 checked',case,ix,'eliminated',len(gone),'seconds',round(time.perf_counter()-start,2),flush=True)
 pp=[p for p in load('round9-surviving-pairs.json') if p['pair_id'] in state10['pairs_left']];assert {(p['case'],p['R_index']) for p in pp}==set(left)-set(gone)
 out=dict(round9_remaining=len(left),round10_checked=len(state10['results']),branches=branches,round10_remaining=len(pp),complete=state10['complete'],seconds=time.perf_counter()-start);(R/'round910-verification.json').write_text(json.dumps(out,indent=2), encoding='utf-8');print('PASS',out,flush=True)
if __name__=='__main__':main()

