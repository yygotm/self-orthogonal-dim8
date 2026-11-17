"""Independent audit of the recursive bound proof tree and old C exclusions."""
from verification_models import *
from verify_round910 import split_cut,key
from fractions import Fraction as Q
import re,time

def validate_recursive_columns(name,expected,saved):
 assert saved['variables']==expected, (name,'recursive variable columns mismatch')
 assert all(len(row)==len(expected) for row in saved['A']), (name,'recursive matrix width mismatch')

def main():
 start=time.perf_counter();audit=load('recursive-audit.json');by={tuple(e['parameters']):e for e in audit};assert len(by)==len(audit);checked=0;metadata_repairs=[]
 def feasible(e):return e.get('feasible') if e['status']=='parity extension' else e['status']=='feasible'
 for e in audit:
  n,k,d,div,so,full,depth=e['parameters'];d=div*((d+div-1)//div);status=e['status']
  if status=='parity extension':
   assert div==1 and d%2;target=[n+1,k,d+1,2,False,False,depth];assert e['target']==target and e['feasible']==feasible(by[tuple(target)]);continue
  if n==g(k,d):full=True;div=lcm(div,d&-d)
  so=so or div%4==0
  if status=='SO dimension contradiction':assert so and 2*k>n;continue
  if status=='hand lemma: no even [13,5,6]':assert (n,k,d,div)==(13,5,6,2);continue
  assert g(k,d)<=n and k<=n;m=n-g(k-1,d) if k>1 else n;proj=full and m==1;assert e['effective']==[n,k,d,div,so,full,proj];ws=simple_support(n,k,d,div,so,full,proj)
  for w in list(ws):
   if w==2*d:
    r=k-max(0,n-w-(1 if so and n>w else 0))
    if r>=2 and d%(2**(r-2)):ws.remove(w)
   if w in ws and depth>0 and k>1 and w<2*d:
    rd=d-w//2;rd+=rd%2 if so else 0;child=(n-w,k-1,rd,2 if so else 1,False,full,depth-1)
    assert child in by
    if not feasible(by[child]):ws.remove(w)
  if not ws:assert status=='empty support' and e['weights']==[];continue
  M=ordinary(n,k,ws,so,full,proj)
  if full and k>1:M.le([K(n,2,w) for w in ws],2**k*((m-1)*n//2)-comb(n,2))
  if n in ws and k>1:
   ww=[w for w in ws if w==n or n-w in ws];N=ordinary(n,k,ww,so,full,proj);N.eq([int(w==n) for w in ww],1)
   for w in ww:
    if w!=n:N.eq([int(v==w)-int(v==n-w) for v in ww],0)
   saved=load(e['name']+'_allone-model.json');assert N.variables==saved['variables'] and N.A==saved['A'] and N.b==saved['b'];rr=load(e['name']+'_allone-result.json');verify_lp(saved,rr)
   if rr['status']=='infeasible':M.eq([int(w==n) for w in ws],0);ws=ws[:];ws.remove(n);assert e['allone_excluded']
  assert ws==e['weights'];saved=load(e['name']+'-model.json');assert M.A==saved['A'] and M.b==saved['b'],e['name']
  validate_recursive_columns(e['name'],M.variables,saved)
  rr=load(e['name']+'-result.json');assert rr['status']==status;verify_lp(saved,rr);checked+=1
 (R/'recursive-metadata-reconstruction.json').write_text(json.dumps(metadata_repairs,indent=2), encoding='utf-8')
 print('RECURSIVE METADATA RECONSTRUCTIONS',len(metadata_repairs),flush=True)
 print('RECURSIVE PROOF TREE PASS',len(audit),checked,'LP models',flush=True)
 count=0
 for case,summary in enumerate(load('iter-summary.json')):
  files=[]
  for p in R.glob(f'iter-case{case}-*-w*-result.json'):
   mt=re.match(r'iter-case\d+-(\d+)-w(\d+)-result.json',p.name)
   if mt:files.append((int(mt[1]),0 if int(mt[2])==58 else 200-int(mt[2]),int(mt[2]),p.name[:-12]))
  excluded=[]
  for cycle,order,w,name in sorted(files):
   rr=load(name+'-result.json')
   if rr['status']!='infeasible':continue
   assert w not in excluded;M=split_C(case,w,excluded);saved=load(name+'-model.json');assert M.variables==saved['variables'] and M.A==saved['A'][:len(M.A)] and M.b==saved['b'][:len(M.b)],name
   for row,b,label in zip(saved['A'][len(M.A):],saved['b'][len(M.b):],saved['labels'][len(M.b):]):
    r,s=map(int,re.findall(r'\((\d+),(\d+)\)',label)[-1]);co,bb=split_cut(M.variables,w,r,s,'shadow' in label);assert key(row,b)==key(co,bb),label
   verify_lp(saved,rr);excluded.append(w);count+=1
  assert excluded==summary['excluded'],(case,excluded,summary)
 print('INITIAL C WEIGHT EXCLUSIONS PASS',count,'seconds',time.perf_counter()-start,flush=True);(R/'initial-proof-verification.json').write_text(json.dumps(dict(recursive_entries=len(audit),LP_models=checked,C_exclusions=count,seconds=time.perf_counter()-start),indent=2), encoding='utf-8')
if __name__=='__main__':main()

