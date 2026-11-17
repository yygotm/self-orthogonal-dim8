"""Proof-certificate verification only. Python standard library; no LP solver.
All paths are relative to this file. Does not access the source manuscript or
other project folders. The general hand lemmas remain mathematics in proof.md.
"""
from pathlib import Path
import json,subprocess,sys,time
R=Path(__file__).resolve().parent
def load(n):return json.loads((R/n).read_text(encoding='utf-8'))
def ids(rows):
 out={(p['case'],p['R_index']) for p in rows};assert len(out)==len(rows);return out
def pairs(n):return load(f'round{n}-surviving-pairs.json')
def coverage():
 current=load('fixedR-resume-feasible.json');assert len(current)==2918;chain=[2918]
 for n,want in [(1,1248),(2,1248),(4,662),(5,256),(6,206),(7,206),(8,206)]:
  state=load(f'round{n}-state.json');assert state['complete'];nxt=pairs(n)
  expected=[p for p in current if p['R_index'] in state['left']]
  assert ids(nxt)==ids(expected);assert {p['pair_id'] for p in nxt}==set(state['pairs_left']);assert len(nxt)==want
  if n in [5,6,7,8]:
   rr=state['results'];assert {r['R_index'] for r in rr}=={p['R_index'] for p in current} and len(rr)==len({r['R_index'] for r in rr})
  current=nxt;chain.append(len(current))
 for n,want in [(9,191),(10,30),(22,0)]:
  st=load(f'round{n}-state.json');assert st['complete'];assert ids(st['results'])==ids(current)
  nxt=pairs(n);expected=[p for p in st['results'] if p['status']!='infeasible'];assert ids(nxt)==ids(expected)
  assert {p['pair_id'] for p in nxt}==set(st['pairs_left']);assert len(nxt)==want;current=nxt;chain.append(len(current))
 print('COVERAGE CHAIN',chain,flush=True);return chain
if __name__=='__main__':
 start=time.perf_counter()
 if '--negative-control' in sys.argv:
  r=subprocess.run([sys.executable,'-X','utf8','-B',str(R/'verify_hand_basics.py'),'--negative-control'],cwd=R);assert r.returncode!=0;print('EXPECTED NONZERO: corrupted negative dual multiplier rejected',flush=True);sys.exit(1)
 chain=coverage();rows=[]
 scripts=['verify_hand_basics.py','verify_initial_proof.py','verify_integer_tables.py','verify_universal_compatibility.py','verify_resume.py','verify_round12.py','verify_round456.py','verify_round7.py','verify_round910.py','verify_section31.py','verify_section33.py','verify_round22.py']
 for script in scripts:
  cmd=[sys.executable,'-X','utf8','-B',str(R/script)];print('COMMAND',json.dumps(cmd),flush=True);t=time.perf_counter();r=subprocess.run(cmd,cwd=R);dt=time.perf_counter()-t;assert r.returncode==0,(script,r.returncode);rows.append(dict(script=script,exit_code=r.returncode,seconds=dt));print('VERIFIED',script,round(dt,3),'seconds',flush=True)
 out=dict(status='PASS',coverage_chain=chain,remaining_pairs=0,closed=True,checks=rows,seconds=time.perf_counter()-start)
 (R/'final-verification.json').write_text(json.dumps(out,indent=2),encoding='utf-8');print('PASS FINAL NONEXISTENCE CERTIFICATE CHAIN',json.dumps(out),flush=True)
