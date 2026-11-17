"""Independent checker: stdlib only; imports neither the LP solver nor any model generator.
Rebuilds all small LP matrices using a Krawtchouk recurrence, checks exact witnesses/
Farkas vectors, integer obstructions, Fourier moment constants, canonical subcodes,
and completeness of the final ordinary-enumerator CSV files.
This is an arithmetic/certificate checker; the coding/Fourier lemmas are proved in proof.md.
"""
from pathlib import Path
from fractions import Fraction as Q
from math import comb
from collections import Counter
import json,hashlib,csv,itertools,sys,time,os,argparse
ROOT=Path(__file__).resolve().parent

def need(condition,message):
 if not condition:raise ValueError(message)

def krow(n,w):
 out=[1]
 if n:out.append(n-2*w)
 for j in range(1,n):
  v=(n-2*w)*out[j]-(n-j+1)*out[j-1]
  need(v%(j+1)==0,'Krawtchouk recurrence integrality')
  out.append(v//(j+1))
 return out

def g(k,d):return sum(-(-d//(2**i)) for i in range(k))

def support(n,k,d,div=2,so=True):
 out=[]
 for w in range(d,n+1):
  if w%div or (so and w==n-1):continue
  if w<2*d:
   rd=d-w//2
   if so:rd+=rd%2
   if g(k-1,rd)>n-w:continue
  out.append(w)
 return out

def elementary(n,k,weights,projective=False):
 ks={w:krow(n,w) for w in weights};A=[];b=[]
 rows=[([1 for w in weights],2**k-1),([ks[w][1] for w in weights],-n)]
 if projective:rows.append(([ks[w][2] for w in weights],-comb(n,2)))
 for row,bb in rows:A.extend([row,[-x for x in row]]);b.extend([bb,-bb])
 if not projective:A.append([-ks[w][2] for w in weights]);b.append(comb(n,2))
 return A,b

def cmodel(n,L):
 D={48:124,64:3} if L==96 else {48:108,52:16,64:3}
 ws=[46,50,54,62,66,70,78] if n==96 else [46,50,54,58,62,66,70,74,78,82,86,94];ks={w:krow(n,w) for w in set(ws)|set(D)}
 A=[];b=[]
 def le(row,rhs):A.append(row);b.append(rhs)
 def eq(row,rhs):le(row,rhs);le([-v for v in row],-rhs)
 eq([1]*len(ws),128);le([-int(w==46) for w in ws],-1)
 for j in range(n+1):
  co=[ks[w][j] for w in ws];const=comb(n,j)+sum(a*ks[w][j] for w,a in D.items())
  le([256*int(w==j)-ks[w][j] for w in ws],const-256*D.get(j,0))
  le(co,const)
  if j==1:eq(co,-const)
  if j==2:
   if L==96:eq(co,-const)
   else:le(co,768-const)
 return A,b

def verify_lp(cert,negative=False):
 specs={'min48':(97,8,[48,64],False),'R13':(13,5,[6,8,12],True),'R41':(41,6,[20,24,32],True),'R25':(25,6,[12,16],False),'R17':(17,6,[8],False),'D96':(96,7,[48,64,96],True)}
 expected={name:elementary(*spec) for name,spec in specs.items()}
 expected['D68']=([[1,1],[-1,-1],[1,-3],[-1,3],[96,72]],[63,-63,-29,29,5368])
 expected['C96_D96']=cmodel(96,96);expected['C97_D96']=cmodel(97,96);expected['C97_D97']=cmodel(97,97)
 need(set(cert)==set(expected),'unexpected certificate case set')
 for name,(A,b) in expected.items():
  entry=cert[name];need(entry['A']==A and entry['b']==b,f'{name}: regenerated LP mismatch')
  sol=entry['solution']
  if sol['status']=='infeasible':
   y=list(map(Q,sol['y']))
   if negative and name=='min48':y=[Q(0)]*len(y)
   need(len(y)==len(b) and all(v>=0 for v in y),f'{name}: bad nonnegative dual vector')
   column=[sum(y[i]*A[i][j] for i in range(len(b))) for j in range(len(A[0]))]
   contradiction=sum(v*bb for v,bb in zip(y,b))
   need(all(v>=0 for v in column),f'{name}: Farkas column negative')
   need(contradiction<0,f'{name}: Farkas constant is not negative')
   print('VERIFIED_FARKAS',name,'nonzero_rows',sum(v!=0 for v in y),'combined_A',list(map(str,column)),'combined_b',str(contradiction))
  else:
   x=list(map(Q,sol['x']));need(all(v>=0 for v in x),f'{name}: negative primal')
   need(all(sum(a*v for a,v in zip(row,x))<=bb for row,bb in zip(A,b)),f'{name}: primal inequality failed')
   print('VERIFIED_PRIMAL',name,'x',list(map(str,x)))


def integer_obstructions():
 for n,k,ws,coeffs,target,rhs in [(13,5,[6,8,12],[18,-2,1],[0,0,48],64),(41,6,[20,24,32],[140,-6,1],[0,0,192],128)]:
  kr={w:krow(n,w) for w in ws}
  eqs=[[1]*3,[w for w in ws],[kr[w][2] for w in ws]]
  bs=[2**k-1,2**(k-1)*n,-comb(n,2)]
  got=[sum(coeffs[i]*eqs[i][j] for i in range(3)) for j in range(3)]
  bb=sum(c*b for c,b in zip(coeffs,bs))
  need(got==target and bb==rhs and rhs%target[-1]!=0,'integer moment obstruction')
  print('VERIFIED_INTEGER_OBSTRUCTION',n,k,got,'=',rhs)
 # All uses of Griesmer equality in the final hand proof.
 for n,k,d,power in [(13,5,6,2),(41,6,20,4),(25,6,12,4),(17,6,8,8),(16,5,8,8)]:
  need(g(k,d)==n and d%power==0,'Ward hypothesis arithmetic')
 need(support(97,8,48)==[48,64],'min48 support')
 need(support(96,7,48,4)==[48,64,96],'D96 support')
 need(support(97,7,48,4)==[48,52,56,64,68,72,80],'initial D97 support')
 need(support(13,5,6,2,False)==[6,8,12],'R13 support')
 need(support(41,6,20,4)==[20,24,28,32],'R41 support before deleting 28')
 need(support(25,6,12,4)==[12,16],'R25 support')
 need(support(17,6,8,8)==[8],'R17 support')
 # Residual of R41 at 28 is precisely the excluded R13.
 need(41-28==13 and 20-28//2==6,'R41 to R13 residual arithmetic')
 # Enumerate the pair cells at D weight68 independently.
 pairs=[];weights=[48,52,64,68]
 for a,b in itertools.combinations_with_replacement(weights,2):
  i=(68+a-b)//2;j=(a+b-68)//2
  if i%2 or not(0<=i<=68 and 14<=j<=29):continue
  if j<28 and g(5,14-j//2)>29-j:continue
  pairs.append((a,b,i,j))
 need(pairs==[(48,48,34,14),(48,52,32,16)],'D68 orbit cell set')
 # The candidate pair counts would be X=40,Y=23, and B2(D)=-1.
 need((comb(97,2)+103*krow(97,48)[2]+23*krow(97,52)[2]+krow(97,68)[2])//128==-1,'D68 dual obstruction')
 print('VERIFIED_SUPPORTS_AND_WARD_HYPOTHESES', 'D68_cells',pairs)


def quartet(H):
 m=H//2;vals=set();maxsq=0
 for z in itertools.product(range(m+1),repeat=3):
  z4=m-sum(z)
  if z4<0:continue
  zs=z+(z4,);W=[H-8*x for x in zs];need(sum(W)==0,'quartet zero sum')
  for chi in [(1,-1,1,-1),(1,1,-1,-1),(1,-1,-1,1)]:
   v=sum(a*b for a,b in zip(chi,W));need(v%4==0,'quartet inverse denominator');v//=4
   vals.add(v);maxsq=max(maxsq,v*v)
 return vals,maxsq


def fourier_and_structure():
 # Classify the auxiliary projective 8-divisible V by its first three moments.
 possibilities=[]
 for a in [4,8,12,16,20]:
  for r in range(1,8):
   if (a*a-47*a+512)*2**r==512:possibilities.append((a,r))
 need(possibilities==[(16,5)],'auxiliary V classification arithmetic')
 # Check B2(D)=3b-6 for every candidate b; the moment equation fixes A52.
 for b64 in range(8):
  a52=28-4*b64;a48=127-a52-b64
  num=comb(97,2)+a48*krow(97,48)[2]+a52*krow(97,52)[2]+b64*krow(97,64)[2]
  need(num==128*(3*b64-6),'D B2 expression')
 vals4,max4=quartet(4);vals6,max6=quartet(6)
 need(vals4=={-4,0,4} and vals6=={-6,-2,2,6},'quartet spectra')
 need(32*max4<32**2,'D96,N96 Parseval contradiction')
 # D96,N97: Walsh values +/-2,+/-6 have 28 large values by Parseval.
 need((1024-32*4)//32==28,'large Walsh count')
 fourth=28*6**4+4*2**4;lower=32*(32**2+31*16)
 need(fourth==36352 and lower==48640 and fourth<lower,'fourth moment contradiction')
 # D97: each of the fifteen ordinary pairs contributes4; special pair contributes>=0.
 energies=[]
 for s,t in itertools.product([-1,1],repeat=2):
  energies.append((s+t)**2+(s-t)**2)
 need(set(energies)=={4} and max4+max6==52 and 15*4==60 and 52<60,'D97 pair-energy contradiction')
 print('VERIFIED_FOURIER','quartet4',sorted(vals4),'quartet6',sorted(vals6),'D96_fourth',fourth,'<',lower,'D97_energy',52,'<',60)
 # Positive controls: exactly enumerate 128 words of the two derived canonical D's.
 for N in [96,97]:
  cols=[]
  if N==96:
   cols=[u|(b<<5) for b in [1,2,3] for u in range(32)]
  else:
   # u=(a,t in F2^4), b in F2^2.
   cols=[1]
   for b in [1,2,3]:
    for t in range(1,16):
     for a in [0,1]:cols.append(a|(t<<1)|(b<<5))
    cols.extend([1|(b<<5)]*2)
  need(len(cols)==N and all(cols),'canonical column length/fullness')
  distribution=Counter(sum((u&v).bit_count()%2 for v in cols) for u in range(128))
  expected={0:1,48:124,64:3} if N==96 else {0:1,48:108,52:16,64:3}
  need(dict(distribution)==expected,'canonical D weight distribution')
  need(distribution[0]==1 and all(w%4==0 for w in distribution),'canonical D rank and doubly-evenness')
  need(sum(m*(m-1)//2 for m in Counter(cols).values())==(0 if N==96 else 3),'canonical repeated points')
  print('VERIFIED_CANONICAL_D',N,'distribution',dict(sorted(distribution.items())))


def ordinary_candidate(A,n):
 ws=list(A);ks={w:krow(n,w) for w in ws}
 for j in range(n//2+1):
  c=comb(n,j)+sum(a*ks[w][j] for w,a in A.items())
  sh=comb(n,j)+sum(a*ks[w][j]*(1 if w%4==0 else -1) for w,a in A.items())
  if c%256 or sh%256 or c<256*max(A.get(j,0),A.get(n-j,0)) or sh<0:return False
 return True


def verify_csv():
 for n,L,D,bs,singles in [(96,96,{48:124,64:3},[0],[46,50,54,62,66,70,78]),(97,96,{48:124,64:3},[0],[46,50,54,58,62,66,70,74,78,82,86,94]),(97,97,{48:108,52:16,64:3},range(4),[46,50,54,58,62,66,70,74,78,82,86,94])]:
  path=ROOT/f'final-ordinary-C{n}-D{L}.csv';raw=list(csv.DictReader(path.open(encoding='utf-8')))
  ws=sorted(set(D)|set(singles));stored={tuple(int(row[key]) for key in ['B2']+list(map(str,ws))) for row in raw}
  need(len(stored)==len(raw),'duplicate CSV row')
  Z=(128*n-sum(w*a for w,a in D.items())-5888)//4
  TD=sum(w*w*a for w,a in D.items());high=sorted([(w-46)//4 for w in singles if w>50],reverse=True)
  expected=set();counts={}
  def rec(pos,remainingU,remainingZ,usedN,b2):
   if pos==len(high):
    if remainingU:return
    a1=remainingZ;a0=128-usedN-a1
    if a0<1 or a1<0 or (50 not in singles and a1):return
    aa={**D,46:a0}
    if a1:aa[50]=a1
    aa.update({46+4*z:a for z,a in counts.items() if a})
    if ordinary_candidate(aa,n):expected.add(tuple([b2]+[aa.get(w,0) for w in ws]))
    return
   z=high[pos]
   for a in range(1+min(remainingU//(z*(z-1)),remainingZ//z)):
    counts[z]=a;rec(pos+1,remainingU-a*z*(z-1),remainingZ-a*z,usedN+a,b2)
   counts.pop(z,None)
  for b2 in bs:
   num=64*n*(n+1)+128*b2-TD-46**2*128-368*Z
   need(num%16==0,'integer enumerator moment division')
   U=num//16-Z
   if U>=0:rec(0,U,Z,0,b2)
  need(expected==stored,f'CSV completeness mismatch {n},{L}')
  print('VERIFIED_COMPLETE_ORDINARY_CSV',n,L,'candidates',len(stored))


def lower_cpu_priority():
 if os.name != 'nt':
  print('CPU_PRIORITY: platform default (non-Windows)')
  return
 import ctypes
 kernel=ctypes.WinDLL('kernel32',use_last_error=True)
 kernel.GetCurrentProcess.restype=ctypes.c_void_p
 kernel.SetPriorityClass.argtypes=[ctypes.c_void_p,ctypes.c_uint32]
 kernel.GetPriorityClass.argtypes=[ctypes.c_void_p]
 kernel.GetPriorityClass.restype=ctypes.c_uint32
 handle=kernel.GetCurrentProcess()
 if not kernel.SetPriorityClass(handle,0x4000):raise ctypes.WinError(ctypes.get_last_error())
 if kernel.GetPriorityClass(handle)!=0x4000:raise RuntimeError('CPU priority did not change')
 print('CPU_PRIORITY: BelowNormal',flush=True)

def verify_optional_sources(directory):
 hashes={
 'kurz-self_orthogonal-draft-20261026.pdf':'46f407ad9c1e0514692c408ab1e329abd1e3a294055b70937e8a60f828666fb3',
 'kurz-self_orthogonal-draft-20261026.txt':'de23d0e056e40e15081f5af3dbe87c0704fca33b26f6ce3514ad960117613d60'}
 checked=0
 for name,expected in hashes.items():
  path=directory/name
  if not path.exists():
   print('SOURCE_HASH skipped: optional source file missing:',name)
   continue
  need(hashlib.sha256(path.read_bytes()).hexdigest()==expected,'source hash mismatch: '+str(path))
  checked+=1
 print('VERIFIED_FIXED_SOURCE_HASHES',checked,'skipped',len(hashes)-checked)


def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--source-dir',type=Path,default=ROOT/'refs',help='Optional source-manuscript directory; defaults to refs beside this script')
 parser.add_argument('--negative-control',action='store_true')
 args=parser.parse_args()
 lower_cpu_priority()
 start=time.perf_counter()
 verify_optional_sources(args.source_dir)
 cert=json.loads((ROOT/'final-certificate.json').read_text(encoding='utf-8'))
 verify_lp(cert,args.negative_control)
 integer_obstructions();fourier_and_structure();verify_csv()
 print('CHECK_OK','seconds',round(time.perf_counter()-start,6))
if __name__=='__main__':main()

