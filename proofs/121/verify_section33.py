from itertools import combinations_with_replacement
from collections import Counter
n=0
for points in combinations_with_replacement(range(8),5):
 a=Counter(points);sigma=0
 for x in points:sigma^=x
 hist=Counter(a.values());assert a[sigma]>=1+4*hist[5]-hist[3]-hist[2];n+=1
assert n==792
print('PASS section33 local inequality on all 792 mass-five multisets on F2^3')
