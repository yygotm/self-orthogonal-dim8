"""Small independent arithmetic checks supporting the hand lemma in section31."""
from collections import Counter
from pathlib import Path
import json
R=Path(__file__).resolve().parent
p=1;columns=[]
for y in range(1,8):
 for v in range(16):
  m=(2-int(v==0)) if y==p else int(v!=0)
  columns += [(y,v)]*m
assert len(columns)==121
chi=lambda a,b:1-2*((a&b).bit_count()%2)
weights={(a,u):sum(((a&y).bit_count()+(u&v).bit_count())%2 for y,v in columns) for a in range(8) for u in range(16)}
assert Counter(weights.values())==Counter({0:1,60:108,64:15,76:4})
assert Counter(weights[a,0] for a in range(1,8))==Counter({60:3,76:4})
for u in range(1,16):assert Counter(weights[a,u] for a in range(8))==Counter({60:7,64:1})
for pp in range(1,8):
 ys=[y for y in range(1,8) if y!=pp]
 for b in range(8):
  for c in range(8):assert b==c or any(chi(b,y)!=chi(c,y) for y in ys)
 for sign in [-1,1]:
  M=[(80+sign*16*chi(a,pp))//8 for a in range(8)];assert set(M)=={8,12} and max(M)<16
for k in [3,4]:
 for a in range(2**k):assert sum(chi(a,b) for b in range(2**k))==(2**k if a==0 else 0)
for u in range(1,16):assert sum((u&v).bit_count()%2 for v in range(1,16))==8
assert (15**2+15)//16==15
print('PASS section31: canonical D, F, six-character separation, Walsh orthogonality, and M<=12<16')
(R/'section31-verification.json').write_text(json.dumps(dict(canonical_columns=121,words_checked=128,hand_lemma_C_case=1,hand_lemma_C_index=247,passed=True),indent=2), encoding='utf-8')
