- **Claim:** No binary self-orthogonal [90,8,≥42] code exists; this is the dimension-8 case with parameters [90,8,42] in Lemma 21 of Kurz's October 29 draft (arXiv:2610.39870v1).
- **Method:** No exhaustive computer enumeration of codes is used. Finite exact computations (certificates and tables) are used.
- **Status:** Found using AI tools and checked by independent AI reviews and exact computer checks. Not yet checked by a human expert.

Note: References to Kurz's draft in the body use the October 29 version. Statements about Lean formalization or completion of a new independent review describe the original proof-writing stage; they do not deny the subsequent independent AI reviews and exact checks reported in the status panel.

# Nonexistence of SO [90,8,>=42]₂

Written: 2026-10-28. The claim concerns minimum distance **at least 42**. Lower-bound constructions are not considered.
This is a mathematical proof consisting of mathematical arguments and 16 rational Farkas certificates.
No exhaustive search over generator matrices, LinCode classification results, or classification counts from Table 1 are assumed.

## 1. Notation and general results used

View the nonzero columns of a generator matrix of a binary linear code as points of F₂ᵏ, with multiplicities m(p).
Full length means that there are no zero columns; projectivity means full length with pairwise distinct columns.
A_w counts codewords of weight w, and B_j counts codewords of weight j in the dual. For a full-length code,
B₂=Σ_p binom(m(p),2). We do not use this formula when zero columns are present.

We use the following results.

- Griesmer: g(k,d)=Σ_{i=0}^{k-1} ceil(d/2^i)≤n.
- Shortening a full-length code at a point of multiplicity m gives a full-length [n−m,k−1,≥d] code.
  Hence m≤n−g(k−1,d).
- The ordinary residual with respect to a codeword of weight w<2d has parameters [n−w,k−1,≥d−floor(w/2)].
  **If the parent is full-length**, so is the residual. If the parent is SO, the residual is even, and the distance lower bound is rounded up to the next even integer.
  An even residual is not assumed to be SO. Its columns form a subset of the parent's columns, so B₂(residual)≤B₂(parent).
- In an SO code, q(x)=wt(x)/2 mod2 is linear. Its kernel D is doubly-even and has codimension ≤1.
  A full-length SO code has no codeword of weight n−1, and a projective SO code has no codeword of weight n−2.
- Ward: in a binary code meeting the Griesmer bound, 2^r|d implies that every codeword weight is a multiple of 2^r.
  Reference: H. N. Ward, *Divisibility of codes meeting the Griesmer bound*,
  J. Combin. Theory Ser. A 83(1),79–93(1998), Theorem 1 in Kurz's draft (printed p.3).
  We do not reprove the theorem from the original paper here.
- MacWilliams: `Σ_w K_j(n,w)A_w=2^k B_j`,
  `K_j(n,w)=Σ_s (−1)^s binom(w,s)binom(n−w,j−s)`.
  For a full-length code, `Σ_{w>0}A_w=2^k−1`, ΣwA_w=2^{k−1}n.
- Structure theorem for binary Griesmer codes: if d≤2^{k−1}, the code is of Solomon–Stiffler or Belov type.
  Reference: T. Helleseth, *A characterization of codes meeting the Griesmer bound*,
  Information and Control 50(2),128–159(1981). The specific consequence needed is derived in §3.
  This was checked against Kurz's October 29 draft pp.11–12 and Shi–Li–Helleseth–Kim, arXiv:2303.16729v1,
  pp.2,8–9 and the proof of Proposition 6.10 on p.25. This is an external structure theorem,
  not an input from computer classification of codes. The complete proof in Helleseth's original paper has not been rechecked.

On the finite group V=F₂ʳ, define the Walsh transform by hat(f)(u)=Σ_x f(x)(−1)^{u·x}.
Inversion, Parseval, and duality take the forms
f(x)=2^{−r}Σ_u hat(f)(u)(−1)^{u·x}, Σ hat(f)²=2^rΣ f²,
Σ hat(f)g=Σ f hat(g). All subsequent applications use integers.

## 2. Small auxiliary results and the lengths of C and D

### 2.1 One-weight codes and the boundary weight 2d

For a binary one-weight code of dimension r and nonzero weight a, every nonzero column has multiplicity a/2^{r−1}.
This follows by Walsh inversion of the weight function. In particular, 2^{r−1}|a.
If an [n,k,≥d] code has a codeword of weight 2d, the kernel of projection off its support has dimension
r≥k−(n−2d). The kernel contains the all-one word of length 2d, and all its other nonzero weights are d.
A hyperplane not containing the all-one word is a one-weight code of dimension r−1, so r≥2 implies 2^{r−2}|d.

### 2.2 Small nonexistence results and residual weight supports

(1) There is no even [13,5,6] code. Since g(5,6)=13, g(4,6)=12, it would be full-length and projective.
Excluding weight 10 by the ordinary residual bound leaves weights 6,8,12.
The total count and moments of orders 1 and 2 give 3A₁₂=4, contrary to integrality.
This is an integrality contradiction, not infeasibility of the rational LP.

(2) There is no [9,5,4] code. Since g(5,4)=9, Ward's theorem gives 4-divisibility and SO, but 2·5>9.
Hence there is no [8,5,3] code either (its parity extension would give the former).
Likewise, the parity extension of a [12,5,5] code contradicts (1).
The new column in a parity extension is not assumed nonzero. In these cases Griesmer equality forces full length.

(3) There is no even [22,6,10] code. Since g(6,12)>22, weight 10 occurs, and its [12,5,5] residual contradicts (2).
Similarly, an even [14,6,6] code would have a weight-6 codeword whose [8,5,3] residual contradicts (2).
A [10,6,4] code meets the Griesmer bound, so Ward gives 4-divisibility and SO, contradicting 2·6>10.

(4) The nonzero weights of a full-length even [30,6,14] code lie in {14,16,20,24,30}.
The ordinary residuals at weights 18,22,26 would be [12,5,5], [8,5,3], [4,5,1], respectively, all impossible.
Weight 28 is impossible by §2.1: r≥4 would require 4|14.

(5) A full-length even [26,6,12] code is 4-divisible.
Weights 14,18,22 are excluded by the same small residuals as in (4). Weight 12 must occur by Griesmer,
and an all-one word of weight 26 would produce its complement of weight 14. Thus the weights lie in {12,16,20,24}.

(6) There is no [25,6,12] code. Griesmer equality and Ward give 4-divisibility and SO; the code is full-length and projective.
The residual bound and the SO exclusions of n−1,n−2 leave only weights 12,16.
The total count and first moment give (A₁₂,A₁₆)=(52,11), B₂=−3.
There is no [17,6,8] code either: Ward gives 8-divisibility, and the full-length SO exclusion of n−1 leaves only weight 8,
whereas 63·8≠32·17.

### 2.3 Excluding the branch of minimum distance at least 44

An SO [90,8,≥44] code would be full-length and projective since g(8,44)=90, g(7,44)=89, and 4-divisible by Ward.
The SO residual bound, together with the projective SO exclusion of the boundary weight 88=n−2, leaves nonzero weights {44,48,56,60,64,72}.
The residual at weight 60 is full-length even [30,7,14]. It meets the Griesmer bound and is projective; the ordinary residual bound leaves
weights {14,16,20,28,30}. Weight 28 is impossible because §2.1 with r≥5 would require 8|14.
If weight 30 occurs, complementation excludes 20, and A₁₄=A₁₆=63, A₃₀=1 give B₂=−6.
If 30 does not occur, the moments for weights 14,16,20 give A₁₆=−5. Both cases are impossible.
The residual [26,7,12] at weight 64 meets the Griesmer bound, is 4-divisible by Ward, and is full-length and projective.
Only weights 12,16 remain, giving (A₁₂,A₁₆)=(92,35), B₂=−4.
The residual [18,7,8] at weight 72 meets the Griesmer bound and is 8-divisible by Ward; it is projective and SO, excluding 16=n−2 as well,
so only weight 8 remains, whereas 127·8≠64·18.
Thus the original C has weights 44,48,56. The total count and moments of orders 1 and 2 give
(A₄₄,A₄₈,A₅₆)=(240,−15,30), a contradiction.

Henceforth assume an SO [90,8,≥42] code exists. Weight 42 occurs, and D=C₄ has dimension 7 and minimum weight at least 44.
Its effective length L is 89 or 90 since g(7,44)=89.
If L=89, the code is full-length and projective; full-length SO excludes 88=n−1, and the SO residual bound leaves weights {44,48,56,60,64,72}.
The residuals at 64,72 are excluded by (6). For the remaining weights,
Σ(w−44)(w−48)A_w=512, or 3A₅₆+6A₆₀=16, which is impossible.
Thus both D and C have full length 90.

### 2.4 Weight support and multiplicities of D

Shortening and g(6,44)=88 bound the point multiplicities of D by 2. Let b=B₂(D) be the number of repeated points.
The SO residual bound leaves weights 44,48,52,56,60,64,68,72,76,80,88 for D.
Weights 68,76,80 are excluded by the residuals in (3).
If a word of weight 88 exists, the even projection onto the 2 outside coordinates has rank 1, and both columns are the same nonzero point p.
Its kernel K corresponds to the message hyperplane p^⊥. Of the remaining 88 columns, only a column p could vanish on K,
but p already occurs twice outside, so such a column would have multiplicity at least 3 in D.
Thus K is full-length [88,6,44]. It contains the all-one word, so its distribution is 44^62 88^1; the moments give B₂(K)=77.
On the other hand, g(5,44)=86 gives point multiplicities ≤2 for K, and hence B₂(K)≤44, a contradiction.
The resulting weight support of D is {44,48,52,56,60,64,72}.

## 3. The structure theorem for the residual at weight 52

The residual R at weight 52 in D is full-length even [38,6,18], with g(6,18)=38.
Since 18≤2^5, Helleseth's theorem from §1 applies.
The SS type would require a 4-space and a 3-space corresponding to 32−18=8+4+2 inside a 6-space with no shared nonzero point,
which is impossible. For the Belov type, s=ceil(18/32)=1, 6>u₁>…>u_t>u≥3, and the distance deficit is

14=Σ_{i=1}^t 2^{u_i−1}+2^u−2.

If u=4, the sum is 0, so t=0. If u=3, the sum is 8, so t=1,u₁=4.
Since u≥5 gives 2^u−2>14, the 2 possibilities are (t,u)=(0,4) and (t,u,u₁)=(1,3,4).
In the latter case, the removed point set is `(U₁\{0})∪((S\{0})\T)`, where dim U₁=dim S=4,
and T consists of 5 distinct nonzero points in S, of rank 4 and total sum 0. Here we use the definition of Γ(u+1) on p.9 of Shi et al., with |T|=u+2, not the length formula in their Equation (4).
Since s=1, the 2 removed sets must be disjoint, requiring `(U₁∩S)\{0}⊆T`.
But dim(U₁∩S)≥4+4−6=2 inside a 6-space, so T contains the 3 points {x,y,x+y} of a line.
These 3 points sum to 0, so the remaining 2 points of T also sum to 0 and must coincide, a contradiction.
Thus (t,u,u₁)=(1,3,4) is impossible, leaving only (t,u)=(0,4).
Its columns are the 32 points outside a hyperplane in a 6-space, together with 6 points inside that hyperplane of sum 0 and rank 5.
The latter generate the even [6,5,2] code. This form directly gives

R: 18^30 20^30 22^2 32^1.                                      (R38)

This is a mathematical consequence of the structure theorem, without adopting a LinCode candidate table.
Griesmer equality also implies that the minimum distance is exactly 18.

## 4. Shortening at repeated points and a new upper bound on their number

### 4.1 A full-length 4-divisible [88,6,44] code has 2 possible distributions

Let E be such a code. Place j(u)=(wt_E(u)−44)/4 points at each nonzero message u,
forming a point multiset M. The first moment gives #M=11.
Write C(M) for the code with the points of M as columns, and wt_M(y) for the weight of its codeword with message y.
The rank r of M is dim C(M); distinguish point multiplicities m_M from codeword weights.
Walsh inversion of the weights gives `m_E(y)=wt_M(y)/4` for a nonzero column position y.
Thus C(M) is 4-divisible, with nonzero weights 4,8. The SO dimension bound and first moment give 3≤r≤5. Indeed, the total weight 2^{r−1}·11 is divisible by 4, forcing r≥3.
If r=5, then (A₄,A₈)=(18,13), and MacWilliams gives B₄=−2.

If r=4, then (A₄,A₈)=(8,7). Let W be the set of 7 messages of weight 8. Then
`m_M(p)=wt_W(p)−3≥0`, so W generates [7,4,≥3].
The 7 columns of its 3-row parity-check matrix are distinct and nonzero, hence are all the nonzero 3-vectors.
This is the Hamming code, with distribution 3^7 4^7 7^1. Thus the positive multiplicities of M are 1 at 7 points and 4 at 1 point.
Similarly, if r=3, the 4 weight-8 messages W satisfy `m_M(p)=2wt_W(p)−3≥0`.
W generates the even [4,3,2] code, with distribution 2^6 4^1. The positive multiplicities of M are 1 at 6 points and 5 at 1 point.
The original E therefore has one of the following 2 distributions.

E₀: 44^55 48^7 60^1;   E₁: 44^56 48^6 64^1.                (E88)

### 4.2 b≤A₆₀+A₆₄

Shortening D at a repeated point p gives full-length E=[88,6,44], so (E88) applies.
E has a unique codeword h of weight 60 or 64, with h(p)=0.
Another repeated point q projects to a repeated point of E. Since the point multiplicities of E are ≤2, q+p is not a column of D.
If h also vanished at this projected point, further shortening would give full-length [86,5,44], contrary to its first moment.
Indeed, the sum of the excesses of the 31 nonzero weights over 44 is 16·86−31·44=12, while h alone contributes at least 16.
Hence h(q)=1. Thus h cannot be assigned to another repeated point, giving
an injection from repeated points to codewords of weight 60/64, and b≤A₆₀+A₆₄.

## 5. A small integer table and rational certificates

Put a=A₅₂, b₅₆=A₅₆, c=A₆₀, e=A₆₄, f=A₇₂.
The total count, first moment, and B₂ formula give

A₄₈=43−2a−3b₅₆−4c−5e−7f,
A₄₄=84+a+2b₅₆+3c+4e+6f,
B₂=(a+3b₅₆+6c+10e+21f−12)/2.

From B₂≥0 and §4.2,

12≤a+3b₅₆+6c+10e+21f,
a+3b₅₆+4c+8e+21f≤12,
a+b₅₆≡0 (mod2).

Thus f=0, 0≤a≤12, 0≤b₅₆≤4, 0≤c≤3, 0≤e≤1.
Checking at most these 520 integer tuples gives exactly the 20 rows of `low-moment-candidates.json`.
In each row, fix a codeword of weight 52 or 60. For a pair {x,x+c₀}, let a',b' be the total weights,
and w the weight of the fixed codeword. The split weights inside and outside its support are i=(w+a'−b')/2, j=(a'+b'−w)/2.
Here i is even and 0≤i≤w. Use nonnegative variables for the numbers of pairs of each type.
Impose the parent weight counts, the residual first moment, B₂,B₃≥0, and B₂(residual)≤B₂(D).
For w=52, also fix the 4 counts in (R38). For w=60, use the weight support in §2.2(4).

The 16 certificates in `final-screen-<row>-model.json` and `final-screen-<row>-result.json` (where `<row>` denotes the table row number)
give y≥0,yA≥0,yb<0 for Ax≤b,x≥0.
The historical search script `final_screen.py` is not included in the publication package and is not needed for verification; the included independent checker is `verify_final.py`.
The checker reconstructs and compares the models from the formulas, without calling a solver.
The 4 remaining rows are:

| Row | Nonzero distribution of D | B₂ |
|---:|---|---:|
|4|44^92 48^31 56^4|0|
|15|44^93 48^31 60^3|3|
|16|44^90 48^34 52^2 64^1|0|
|17|44^92 48^30 52^4 64^1|1|

Row 4 can also be excluded mathematically. Since D is projective, consider the 37 points P obtained by deleting its 90 columns from the 127 points.
The weights on P for nonzero messages are 8^4 16^31 20^92. The sum of 2 of the 4 weight-8 codewords has weight 8 or 16.
If the sum has weight 16, the supports are disjoint; if it has weight 8, the 3 codewords form a line.
If there is no line, 3 supports are pairwise disjoint and their sum has weight 24. If a line exists, it is unique,
and the support of the remaining 1 codeword is disjoint from those of all 3 codewords on the line.
Thus a 3-dimensional subcode is supported on 20 coordinates (12 from the line and the remaining 8).
There are 17 distinct nonzero columns annihilating this 3-space, but its 4-dimensional annihilator has only 15 nonzero points.
This is a contradiction. It remains to treat rows 15,16,17.

## 6. The 2 rows containing weight 64: reduction by Parseval

In rows 16,17, there is a unique codeword c₀ of weight 64.
If there is a repeated point, §4.2 shows that c₀ vanishes there. Thus the 64 columns on the support of c₀ are distinct
and comprise all 64 points of a 6-dimensional affine space.
D is the juxtaposition of these 64 RM-type columns with a full-length R=[26,6,12] on a hyperplane.
R is 4-divisible by §2.2(5).

Take a word z from C\D, let f:F₂⁶→{±1} be its sign function on the 64 columns, and let g be its remaining part.
Put F=hat(f), H(u)=26−2wt(g+R(u)).
The weights of the 2 codewords in z+D differing by c₀ give

|F(u)|≤6−H(u),  H(u)≤6.                                    (P)

Let b_D count the repeated points of R, and b_C those whose 2 columns are not separated by z.
Full length and Parseval give

ΣF²=4096, ΣH=0, `ΣH²=64(26−2b_D+4b_C)`,
`Σ(6−H)²=64(62−2b_D+4b_C)`.

In row 16, `b_D=b_C=0`, and the right-hand side is 3968<4096.
In row 17, b_C=0 would give 3840<4096.
Thus only row 17 with `b_D=b_C=1` remains, and equality must hold everywhere in (P).
Hence F²=(6−H)², and every codeword in g+R has weight at least 10.

## 7. Equality in row 17: an integrality contradiction with 32 terms

### 7.1 The shortened code of length 24

Shortening R at its 2 repeated columns gives a full-length 4-divisible [24,5,12] code E.
The same weight inversion as in §4.1 gives an auxiliary point multiset M of size 3, with `m_E(y)=wt_M(y)/2`.
The corresponding C(M) is even of length 3. Rank 1 would make M consist of 3 copies of one point, with odd nonzero weight 3, which is impossible. Thus its dimension is 2, giving the simplex code.
Thus the columns of E are (z,x), `z∈F₂²\{0}`, x∈F₂³, in 3 blocks of 8 columns each.
Adding a codeword of R to z allows the 2 repeated entries of g to be set to 00.
Every word in the coset of the remaining 24-bit g modulo E has weight at least 10.

Let b₁,b₂,b₃ be the Boolean functions on the 3 blocks, `e_i=(−1)^{b_i}`, `W_i=hat(e_i)`.
Then `B(h,v)=Σ_{i=1}^3 (−1)^{h·z_i}W_i(v)≤4`, and Σ_h B(h,v)=0.
Adding terms in pairs gives |W_i(v)|≤4.
A Boolean function in 3 variables of odd weight has all Walsh coefficients 2 mod4; under the bound 4 they would all be ±2,
contrary to Parseval. Thus each b_i has even weight and zero cubic ANF coefficient, hence degree at most 2.
An affine function would have a Walsh coefficient of absolute value 8, so the quadratic part has rank 2.
W_i is ±4 at the 4 points of an affine plane and zero elsewhere.

### 7.2 The 3 planes and an odd mixed moment

If exactly 2 of the W_i are nonzero at some v, one B value is 8, which is impossible.
If all 3 are nonzero, their signs must have negative product.
Counting the size t of the common intersection of the 3 planes gives t=2 or 4.
The case t=4, where all 3 planes coincide, is impossible.
Indeed, change coordinates so that each quadratic part is x₁x₂. On the common plane, the Walsh signs are
(−1)^{(v₁+l₁)(v₂+l₂)+c}. The product of 3 such signs still has a v₁v₂ term and cannot be constantly negative.
Thus t=2. The 3 distinct normals sum to 0, and in 3 variables the corresponding quadratic parts also sum to 0.
We may add a common linear function to b₁,b₂,b₃ (adding a codeword of E), so henceforth
b₁+b₂+b₃=c is constant.
The union of the 3 planes has 4·3−2·3+2=8 points and covers the whole 8-point space. Thus at each v exactly 1 or 3 of the W_i are nonzero, and B(h,v)∈{4,−4,−12}.

Put N_h=#{v:B(h,v)=−4}. The identity
1_{B=−4}=1−(B+4)²/64 and Walsh duality give

`N_h=3−(−1)^c Σ_{i<j} σ_iσ_j W_k(0)/4 −Σ_i σ_i e_i(0)`,

where `σ_i=(−1)^{h·z_i}`, {i,j,k}={1,2,3}.
The final sum is odd, and the number of nonzero W_k(0)/4 is also odd, being 1 or 3. Hence **every N_h is odd**.

### 7.3 Contradiction with integer Walsh inversion

Let p be the repeated point of R. The message hyperplane p^⊥ annihilating p is the message space of the shortened code E.
Choose coordinates (h,v)∈F₂²×F₂³ on this 5-space, consistent with the columns (z,x) of E in §7.1.
Use (u₀,h,v) as coordinates on the full message space of R, with p^⊥ given by u₀=0, and dual coordinates `(x₀,x_h,x_v)`.
On this hyperplane H=2+B, so |F(0,h,v)|=4−B(h,v).
Put `f₀(x_h,x_v)=f(0,x_h,x_v)`, `f₁(x_h,x_v)=f(1,x_h,x_v)`, a=(f₀+f₁)/2.
Then a is integer-valued, with hat(a)(h,v)=F(0,h,v)/2.
The function η(h,v)=hat(a)(h,v)/4 is 0 when B=4, ±1 when B=−4, and ±2 when B=−12.
Walsh inversion gives

`a(x_h,x_v)=(1/8)Σ_{h,v}η(h,v)(−1)^{h·x_h+v·x_v}`.

Writing `S(x_h,x_v)` for the signed sum on the right, integrality of a requires every S to be divisible by 8.
Fix x_v=0 and take the second difference in the 2 coordinates of the dual variable x_h. Then

S((0,0),0)−S((1,0),0)−S((0,1),0)+S((1,1),0)=4Σ_v η((1,1),v)

is divisible by 8. Thus Σ_v η((1,1),v) must be even.
But this sum has the same parity as N_{(1,1)}, which is odd by §7.2, a contradiction.
This also excludes row 17.

## 8. Row 15: blocks of length 30 and a small Walsh lemma

### 8.1 Decomposition into 3 blocks

The sum of 2 of the 3 codewords of weight 60 in D cannot have weight 44.
If the sum had weight 44, a weight-60 residual would contain weight 22, contrary to §2.2(4).
Thus the sum has weight 48 or 60.
If the 3 codewords were independent, their 3-dimensional span would have 3 weights 60, 3 weights 48, and 1 remaining weight 44 or 48.
Its effective length would be the total weight/4=92 or 93, exceeding 90.
Thus the 3 codewords form a line H, a full-length 2-dimensional code with 3 nonzero weights 60.
The 90 coordinates split into blocks of 30 columns corresponding to the 3 nonzero column types of H.

In each nonzero coset of D/H, the 4 codeword weights sum to 180.
Since H contains all words of weight 60, these 4 weights are 44,44,44,48.
Let h_i be the word of H that is zero on block i and all-one on the other 2 blocks.
For u∉H, let (a₁,a₂,a₃) be its block weights and s=a₁+a₂+a₃. The 4 weights in u+H are
s and 60−s+2a_i (i=1,2,3).
If s=48, the other 3 weights are 44, so (a₁,a₂,a₃)=(16,16,16).
If s=44, the other 3 weights are 44,44,48, so 2 of the a_i are 14 and 1 is 16.
Thus every word outside H has weight 14 or 16 on every block, and is never zero there.

Let L_i be the restriction of D to its block i of 30 columns. Its kernel is contained in H, whose only words zero on this block are
0 and h_i. Thus the kernel is ⟨h_i⟩, and dim L_i=7−1=6.
The image of H consists of the zero and all-one words, and L_i is full-length. Each of the 31 nonzero cosets of D/H gives
2 complementary words of weights 14 and 16 in L_i. Each fiber has size 2, the order of the kernel, so distinct cosets have disjoint images.
Hence every L=L_i has nonzero weight distribution 14^31 16^31 30^1.
The Griesmer bound after shortening gives point multiplicities ≤2, and the moments give B₂(L)=1.
Choose the all-one word as a row. The columns then lie in an affine 5-space of 32 points,
with 1 point repeated and 3 points missing.
The Walsh values for the remaining 5 message coordinates are ±2, so these 4 points sum to 0.
Thus the 4 points form an affine 2-plane A.

### 8.2 Walsh lemma

**Lemma.** Let s be an integer-valued function on F₂⁵, taking values ±1 outside an affine 2-plane A,
zero at 3 points of A, and 0 or ±2 at the remaining 1 point.
Its Walsh coefficients cannot all lie in {−6,−2,2,6}.

Proof. Let b=1 if the value at the remaining point is ±2, and b=0 if it is 0.
Put F=hat(s), m=#{u:|F(u)|=2}. Parseval gives
4m+36(32−m)=32(28+4b), hence m=8−4b.
Since F/2 is odd, define ε(u)∈{±1} by ε(u)≡F(u)/2 mod4.
Put S₀=Σ_x s(x), L(u)=Σ_x s(x)(u·x), so F(u)/2=S₀/2−L(u). Since F(u)/2 is odd for every u, S₀≡2 (mod4) and L(u)≡0 (mod2). Thus q(u)=(S₀−2)/4−L(u)/2 (mod2), with ε=(−1)^q, has degree at most 2, and its polar form is

q(u+v)+q(u)+q(v)+q(0)=Σ_x s(x)(u·x)(v·x) mod2.

The right-hand side is the Gram form of the points outside A. The Gram form of all of F₂⁵ is 0, and that of an affine 2-plane is
rtᵀ+trᵀ for its 2 direction vectors r,t, of rank 2.
Thus q has rank 2. Its Walsh transform hat(ε) is ±16 at exactly 4 points and zero elsewhere
(this follows directly by separating the quadratic form into 1 product and 3 radical variables).
On the other hand, Fε is 2 when |F|=2 and −6 when |F|=6, so

ΣFε=8m−192=−128−32b.

Walsh duality gives |ΣFε|=|Σs hat(ε)|≤16(4+b)=64+16b.
This is less than 128+32b, a contradiction. □

### 8.3 Applying the lemma

On each block of 30 columns of z∈C\D, let s_i be the function obtained by adding signs at equal columns.
The function s_i itself satisfies the conditions in §8.2.
Fix the remaining 5 message coordinates u, and write T_h for the total Walsh values after adding each of the 4 words of H.
Every word has weight at least 42 and 2 mod4, so T_h≤6, T_h≡6 mod8.
Since H is full-length, Σ_h T_h=0.
Each block Walsh value F_i is 1/4 of the difference between 2 terms of T_h and the other 2, so |F_i|≤6.
Writing `T_h=6−8n_h` gives Σ n_h=3, hence F_i≡2 mod4.
Thus every F_i is ±2,±6, contrary to §8.2.
Row 15 is also impossible.

## 9. Conclusion and scope of verification

All branches have been excluded, so there is no SO [90,8,≥42]₂ code.
The branch of minimum distance greater than 42 was also excluded in §2.3.

The mathematical arguments establish the passage from codes to points, residuals, and Walsh functions, the application of the external structure theorem in §3,
the small shortened-code structures, and the Fourier arguments in §7 and §8.
The certificates verify the completeness of the 20 rows in §5 and the 16 rational contradictions.
The checking script reconstructs these models and also checks the accompanying numerical data and small Walsh identities.
The script alone does not prove Ward/Helleseth or the general mathematical arguments.
Lean formalization and external review were not carried out as part of the source proof task.
