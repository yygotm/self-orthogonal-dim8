"""Independent verifier for proof.md. Standard library only; no LP solver imports.
Reconstructs the final mathematical models, checks completeness of the integer
case table and exact Farkas certificates. Also checks small Fourier identities.
It does not formalize the external Ward/Helleseth theorems or replace the prose proof.
"""
from pathlib import Path
from fractions import Fraction
from math import comb,gcd
from itertools import combinations_with_replacement,product
import json,sys,time,hashlib
ROOT=Path(__file__).resolve().parent

def kraw(n,t,w):
 return sum((-1)**a*comb(w,a)*comb(n-w,t-a) for a in range(max(0,t-n+w),min(t,w)+1))
def griesmer(k,d):return sum((d+2**i-1)//2**i for i in range(k))
def norm(row,b):
 row=list(row);g=gcd(*[abs(x) for x in row+[b]]) or 1
 return [x//g for x in row],b//g

def table():
 out=[]
 for e in range(2):
  for c in range(4):
   for b in range(5):
    for a in range(13):
     t=a+3*b+6*c+10*e
     if t<12 or a+3*b+4*c+8*e>12 or (a+b)%2:continue
     A={44:84+a+2*b+3*c+4*e,48:43-2*a-3*b-4*c-5*e,52:a,56:b,60:c,64:e,72:0}
     beta=(t-12)//2
     assert sum(A.values())==127 and sum(w*v for w,v in A.items())==5760
     assert (comb(90,2)+sum(v*kraw(90,2,w) for w,v in A.items()))==128*beta
     out.append({'A':{str(w):v for w,v in A.items()},'B2':beta})
 assert len(out)==20
 assert json.loads((ROOT/'low-moment-candidates.json').read_text(encoding='utf-8-sig'))==out
 return out

def rebuild(record,anchor):
 A={int(w):v for w,v in record['A'].items() if v};beta=record['B2'];L=90-anchor
 allowed=[18,20,22,32] if anchor==52 else [14,16,20,24,30]
 assert anchor in (52,60) and A.get(anchor,0)>0
 variables=[]
 for a,b in combinations_with_replacement(sorted(A),2):
  i=(anchor+a-b)//2;j=(a+b-anchor)//2
  if i%2==0 and 0<=i<=anchor and j in allowed:variables.append([a,b,i,j])
 rows=[];rhs=[];labels=[]
 def le(row,b,label):
  rr,bb=norm(row,b);rows.append(rr);rhs.append(bb);labels.append(label)
 def eq(row,b,label):
  le(row,b,label+' <=');le([-v for v in row],-b,label+' >=')
 for w,num in A.items():eq([int(a==w)+int(b==w) for a,b,i,j in variables],num-int(w==anchor),f'D A{w}')
 eq([j for a,b,i,j in variables],32*L,'residual first moment')
 for t in (2,3):
  rr=[kraw(L,t,j) for a,b,i,j in variables]
  le([-v for v in rr],comb(L,t),f'residual B{t}>=0')
  if t==2:le(rr,64*beta-comb(L,2),'residual B2 <= parent B2')
 if anchor==52:
  for j,num in [(18,30),(20,30),(22,2),(32,1)]:eq([int(jj==j) for a,b,i,jj in variables],num,f'R38 A{j}')
 best={}
 for rr,bb,label in zip(rows,rhs,labels):
  key=tuple(rr)
  if not any(rr) and bb>=0:continue
  if key not in best or bb<best[key][0]:best[key]=(bb,label)
 return {'variables':variables,'A':[list(k) for k in best],'b':[v[0] for v in best.values()],'labels':[v[1] for v in best.values()]}

def certificates(records,negative=False):
 summary=json.loads((ROOT/'final-screen-summary.json').read_text(encoding='utf-8'))
 assert len(summary)==20
 survivors=[];count=0
 for ix,item in enumerate(summary):
  assert item['index']==ix and item['A']=={w:a for w,a in records[ix]['A'].items() if a} and item['B2']==records[ix]['B2']
  failures=[v for v in item['tests'] if v['status']=='infeasible']
  if not failures:survivors.append(ix);continue
  anchor=failures[-1]['anchor'];M=rebuild(records[ix],anchor)
  saved=json.loads((ROOT/f'final-screen-{ix}-model.json').read_text(encoding='utf-8'))
  assert M==saved,('model mismatch',ix)
  R=json.loads((ROOT/f'final-screen-{ix}-result.json').read_text(encoding='utf-8'));assert R['status']=='infeasible'
  y=[Fraction(0)]*len(M['b'])
  for v in R['y']:
   assert M['labels'][v['row']]==v['label'];y[v['row']]+=Fraction(v['multiplier'])
  if negative and count==0:
   pos=next(i for i,v in enumerate(y) if v);y[pos]=-y[pos]
  assert all(v>=0 for v in y),('negative dual multiplier',ix)
  ya=[sum(v*row[j] for v,row in zip(y,M['A'])) for j in range(len(M['variables']))]
  yb=sum(v*b for v,b in zip(y,M['b']))
  assert all(v>=0 for v in ya) and yb<0,('invalid certificate',ix,ya,yb)
  print('FARKAS',ix,'anchor',anchor,'variables',len(M['variables']),'nonzero_dual',sum(v!=0 for v in y),'yb',str(yb))
  count+=1
 assert count==16 and survivors==[4,15,16,17]
 print('CASE_TABLE 20; FARKAS 16; HAND_CASES',survivors)

def numeric():
 assert [(k,d,griesmer(k,d)) for k,d in [(8,44),(7,44),(6,44),(5,44),(5,6),(5,4),(6,18),(5,12)]]==[(8,44,90),(7,44,89),(6,44,88),(5,44,86),(5,6,13),(5,4,9),(6,18,38),(5,12,24)]
 # Tiny distributions used for impossible branches.
 cases=[(25,6,{12:52,16:11},-3),(26,7,{12:92,16:35},-4),(30,7,{14:63,16:63,30:1},-6),(88,6,{44:62,88:1},77)]
 for n,k,A,beta in cases:
  assert sum(A.values())==2**k-1 and sum(w*a for w,a in A.items())==2**(k-1)*n
  assert comb(n,2)+sum(a*kraw(n,2,w) for w,a in A.items())==2**k*beta
 assert comb(11,4)+18*kraw(11,4,4)+13*kraw(11,4,8)==32*(-2)
 assert sum((w-44)*(w-48)*a for w,a in {44:Fraction(352,3),48:Fraction(13,3),56:Fraction(16,3)}.items())==512
 assert 64*(62)==3968<4096 and 64*60==3840<4096 and 64*64==4096
 for b in (0,1):
  m=8-4*b
  assert 4*m+36*(32-m)==32*(28+4*b)
  assert abs(8*m-192)==128+32*b>64+16*b
 print('NUMERICAL_MOMENTS_AND_GRIESMER OK')

def walsh(values):
 return [sum(v*(-1)**((u&x).bit_count()%2) for x,v in enumerate(values)) for u in range(len(values))]
def poly3(q,l,c):
 out=[]
 for x in range(8):
  a=x&1;b=(x>>1)&1;d=(x>>2)&1
  value=c^((l&x).bit_count()%2)^((q&1)*a*b)^(((q>>1)&1)*a*d)^(((q>>2)&1)*b*d)
  out.append((-1)**value)
 return out

def fourier_checks():
 # Exhaust all 256 truth tables only for the 3-variable elementary lemma.
 good=0
 for mask in range(256):
  f=[1-2*((mask>>x)&1) for x in range(8)];W=walsh(f)
  if max(map(abs,W))>4:continue
  assert mask.bit_count()%2==0
  assert W.count(0)==4 and all(v in (0,4,-4) for v in W)
  assert any(f==poly3(q,l,c) for q in range(1,8) for l in range(8) for c in (0,1))
  good+=1
 assert good==112
 # Normalized triples with b1+b2+b3 constant; this is a small identity check,
 # not enumeration of [90,8] codes or proof of the normalization step.
 W={(q,l,c):walsh(poly3(q,l,c)) for q in range(1,8) for l in range(8) for c in (0,1)}
 tested=0;accepted=0
 for q1 in range(1,8):
  for q2 in range(1,8):
   if q1==q2:continue
   q3=q1^q2
   for l1 in range(8):
    for l2 in range(8):
     for c1,c2,c3 in product((0,1),repeat=3):
      tested+=1;ww=[W[q1,l1,c1],W[q2,l2,c2],W[q3,l1^l2,c3]]
      B=[[sum((-1)**((h&z).bit_count()%2)*ww[z-1][v] for z in (1,2,3)) for v in range(8)] for h in range(4)]
      if max(max(row) for row in B)>4:continue
      accepted+=1
      assert all(set(row)<={4,-4,-12} and sum(x==-4 for x in row)%2==1 for row in B)
      flat=[x for row in B for x in row]
      assert flat.count(4)==18 and flat.count(-4)==12 and flat.count(-12)==2
 assert tested==21504 and accepted>0
 # Same-plane Walsh sign product cannot be constantly negative: 512 triples.
 phases=[[(-1)**((x&1)*((x>>1)&1)+((l&x).bit_count()%2)+c) for x in range(4)] for l in range(4) for c in (0,1)]
 for a,b,c in product(phases,repeat=3):assert [x*y*z for x,y,z in zip(a,b,c)]!=[-1]*4
 # Rank-two quadratic Walsh formula in five variables, in canonical coordinates.
 for l in range(32):
  for c in (0,1):
   vals=[(-1)**((x&1)*((x>>1)&1)+((x&l).bit_count()%2)+c) for x in range(32)]
   spec=walsh(vals);assert spec.count(0)==28 and all(v in (0,16,-16) for v in spec)
 print('FOURIER_SMALL_CHECKS truth_tables=256 normalized_triples=21504 accepted='+str(accepted)+' same_plane=512 rank2_quadratics=64')
 # Positive control: [7,3,4] simplex is genuinely SO.
 words=[[(u&p).bit_count()%2 for p in range(1,8)] for u in range(8)]
 assert [sum(w) for w in words]==[0]+[4]*7
 assert all(sum(x*y for x,y in zip(a,b))%2==0 for a in words for b in words)
 print('POSITIVE_CONTROL SO_SIMPLEX_7_3_4 OK')
 from collections import Counter
 ham=[mask.bit_count() for mask in range(128) if __import__('functools').reduce(int.__xor__,[i+1 for i in range(7) if mask>>i&1],0)==0]
 assert Counter(ham)=={0:1,3:7,4:7,7:1}
 # Explicit R38 Belov matrix; 32 affine points and the even [6,5,2] part.
 cols=[32+x for x in range(32)]+[1,2,4,8,16,31]
 enum=Counter(sum((u&x).bit_count()%2 for x in cols) for u in range(64))
 assert enum=={0:1,18:30,20:30,22:2,32:1}
 # A consistent D for row17, used only as a positive construction check.
 Rcols=[32,32]
 for z in (1,2,3):
  for x in range(8):
   x1=x&1;x2=(x>>1)&1;x3=(x>>2)&1
   bit=[0,x2*x3,x1*x3,1^((x1^x2)*x3)][z]
   Rcols.append((bit<<5)|(z<<3)|x)
 renum=Counter(sum((u&x).bit_count()%2 for x in Rcols) for u in range(64))
 assert renum=={0:1,12:46,16:15,20:2}
 Dcols=[64+x for x in range(64)]+Rcols
 denum=Counter(sum((u&x).bit_count()%2 for x in Dcols) for u in range(128))
 assert denum=={0:1,44:92,48:30,52:4,64:1}
 # A consistent D for row15, again not a classification input.
 Dcols=[]
 for z,plane,center in [(1,[0,1,2,3],0),(2,[0,1,4,5],0),(3,[0,1,6,7],1)]:
  exceptional={v^center for v in plane}
  for x in range(32):Dcols += [(z<<5)|x]*(1-int(x in exceptional)+2*int(x==center))
 assert len(Dcols)==90
 denum=Counter(sum((u&x).bit_count()%2 for x in Dcols) for u in range(128))
 assert denum=={0:1,44:93,48:31,60:3}
 print('CONSTRUCTION_CONTROLS Hamming7 R38 R26 D_rows15_17 OK')

def main():
 start=time.perf_counter();records=table();certificates(records,'--negative-control' in sys.argv)
 numeric();fourier_checks()
 print('VERIFIED final numerical/certificate layer; hand theorems remain as stated in proof.md')
 print('SECONDS',time.perf_counter()-start)
if __name__=='__main__':main()
