- **Claim:** No binary self-orthogonal [97,8,≥46] code exists; this is the dimension-8 case with parameters [97,8,46] in Lemma 21 of Kurz's October 29 draft (arXiv:2610.39870v1).
- **Method:** No exhaustive computer enumeration of codes is used. The proof uses mathematical arguments and small exact calculations, with rational certificates for verification.
- **Status:** Found using AI tools and checked by independent AI reviews and exact computer checks. Not yet checked by a human expert.

Note: Bibliographic labels in the body refer to the October 26 source draft. Statements about Lean formalization or completion of a new independent review describe the original proof-writing stage; they do not deny the subsequent independent AI reviews and exact checks reported in the status panel.

# Nonexistence of SO [97,8,≥46]: a proof not using classification results

## 0. Statement and established results used

There is no binary self-orthogonal code C⊆F₂^97 with dim C=8 and all nonzero codeword weights at least 46.
Zero coordinates are allowed initially. The lower-bound construction and ñ₂(8,46)≤98 are outside the scope of this proof.

We use the Griesmer bound g(k,d)=Σ_{i=0}^{k−1}⌈d/2^i⌉,
Proposition 1, Lemmas 1–3, and the MacWilliams identities (Proposition 2) in Kurz's draft,
and **Theorem 1 (divisibility of codes meeting the Griesmer bound)**.
The last theorem appears on printed p.3 of the draft and states that a Griesmer code over a prime field is p^r-divisible if p^r|d.
The reference given in the draft is [65, Theorem 1], H. N. Ward, *Divisibility of codes meeting the Griesmer bound*,
J. Combin. Theory Ser. A **83**(1), 79–93 (1998) (also [46], and [27] for the binary case).
We adopt the theorem as stated in the draft; we have not rechecked the proof in Ward's original paper. When n=g(k,d), strict monotonicity of g implies that the actual minimum distance equals the lower bound d.
We do not use the Solomon–Stiffler/Belov classification theorem, LinCode, existing classification tables, or codetables.

The core of the proof is a mathematical argument. Rational certificates supplement the checks of small moment systems.
There is no need to rerun the solving program: verify_final.py uses only the standard library for verification.
The general Griesmer/Ward/MacWilliams/Fourier results and the passage from codes to matrices below are mathematical arguments to be read as such; they have not been formalized in Lean.

## 1. Basic consequences

For an SO code, every codeword has even weight, and q(x)=wt(x)/2 mod2 is linear.
D=ker q=C₄ is the doubly-even subcode (draft p.5, Proposition 1).
A residual code of an SO code is even, but is not necessarily SO.
We maintain this distinction throughout.
Whenever SO is needed again, we first establish 4-divisibility using Ward's theorem.

For a nonzero codeword of weight w<2d in an SO [N,k,≥d] code C, the residual code has parameters [N−w,k−1,≥r],
where r is the smallest even integer at least d−w/2.
If the parent code C is full-length, so is this residual code.
Thus g(k−1,r)>N−w excludes that weight (Lemmas 1,2).
When taking a further residual of an ordinary even code, we do not round r up to an even integer.

If a point occurs m times among the columns of a generator matrix of a full-length code, shortening at that point reduces the dimension by 1 and gives length N−m.
Thus, for a k-dimensional code of minimum weight d, N−m≥g(k−1,d).
B₁ counts zero columns, and B₂ counts unordered pairs {i,j} (i≠j) of equal columns, including pairs of zero columns.

## 2. The branch of minimum weight at least 48

Since g(8,48)=97, the effective length is 97. Lemmas 1–3 and the Griesmer bound
leave only nonzero weights 48,64 (96=n−1 is also excluded because the code is full-length and SO).
The first 2 MacWilliams equations give A₄₈+A₆₄=255, 48A₄₈+64A₆₄=128·97,
and hence A₄₈=244, A₆₄=11.
The third equation gives B₂=−9, a contradiction.
`final-certificate.json:min48` contains a Farkas vector for this contradiction.
Henceforth we may therefore assume that C has a codeword of weight 46 and dim D=7.

## 3. Effective lengths and repeated points

Since D has minimum weight at least 48 and dimension 7, its effective length L is at least g(7,48)=96.
Writing N for the effective length of C, the 3 possibilities for (N,L) are (96,96),(97,96),(97,97).

Shortening D at a point gives dimension 6 and minimum weight at least 48, so L−m≥g(6,48)=95.
Thus D is projective when L=96, and every point has multiplicity at most 2 when L=97.
An SO code of dimension 7 obtained by shortening C at a point has a doubly-even subcode of dimension at least 6 and minimum weight at least 48,
so again N−m≥95. Thus C is projective when N=96, and every point has multiplicity at most 2 when N=97.

When L=96, D is projective. Repeated columns of C would restrict to repeated nonzero columns of D,
or to 2 zero columns. D has no repeated nonzero columns and at most 1 zero column, so C is projective as well.
When L=97, the classification in Section 5 shows that D has exactly 3 repeated points.
Since D⊆C implies C⊥⊆D⊥, the number B₂(C) of repeated points of C lies between 0 and 3.

## 4. D when L=96

Lemmas 1,2 and the Griesmer bound leave nonzero weights 48,64,96 for D.
Projectivity gives B₁=B₂=0. The unique solution of the first 3 MacWilliams equations is
A₄₈=124, A₆₄=3, A₉₆=0 (certificate D96).

The columns of D are 96 distinct points of `F₂⁷\{0}`. Their complement T has 31 points.
In the full simplex code every nonzero functional has weight 64, so its weight on T is 16 or 0.
The nonzero functionals vanishing on T correspond to the 3 codewords of weight 64 in D.
Thus the space U spanned by T has codimension 2, and dim U=5.
T consists of all 31 points of `U\{0}`, and the column set of D is F₂⁷\U, the 3 nonzero cosets of U.
This follows from the geometry of the columns, without citing a classification table of Griesmer codes.

## 5. Classifying D when L=97 by a mathematical argument

### 5.1 Small auxiliary results excluding weights 56,72,80

The initial remaining weights of D are {48,52,56,64,68,72,80} (Lemmas 1–3 and the Griesmer bound).

**There is no even [13,5,6] code.** Full length is forced by equality in the Griesmer bound g(5,6)=13.
The Griesmer bound after shortening forces projectivity. Excluding weight 10 by the ordinary residual bound leaves nonzero weights 6,8,12.
Multiplying the MacWilliams total-count, first-moment, and B₂=0 equations by 18,−2,1, respectively, and adding gives
48A₁₂=64, or 3A₁₂=4. This is impossible because A₁₂ is an integer.
The rational LP itself is feasible, with unique solution (A₆,A₈,A₁₂)=(68/3,7,4/3).
The contradiction is an integrality contradiction, not a Farkas contradiction.

**There is no [41,6,20] code.** Since g(6,20)=41, Ward's theorem gives 4-divisibility and hence SO.
The code is full-length and projective. The residual bound and Lemma 3 leave weights 20,24,28,32.
Weight 28 would yield an even [13,5,6] residual code, excluded above.
For the remaining weights 20,24,32, multiplying the total-count, first-moment, and B₂=0 equations by 140,−6,1 gives
192A₃₂=128, or 3A₃₂=2, contrary to integrality.
The unique rational LP solution is (154/3,11,2/3).
A codeword of weight 56 in D would have a [41,6,20] residual code, so weight 56 is excluded.

A codeword of weight 72 in D gives a [25,6,12] residual code. Griesmer equality and Ward's theorem give 4-divisibility and SO.
Lemmas 1–3 leave only weights 12,16. The MacWilliams equations give A₁₂=52,A₁₆=11,B₂=−3.
Weight 80 gives a [17,6,8] residual code, which is 8-divisible and SO by Ward's theorem.
Full length and SO exclude 16=n−1, leaving only nonzero weight 8; the first 2 moments then contradict each other.
Short rational Farkas certificates (R25,R17) are included for these 2 cases.

### 5.2 Excluding weight 68 with a 2-cell split enumerator

At this stage the weight set is 48,52,64,68. Suppose c∈D has weight 68.
Pair x with x+c, and put a=wt(x), b=wt(x+c).
The weights on the 68 support coordinates and the 29 complementary coordinates are i=(68+a−b)/2, j=(a+b−68)/2.
Since the code is SO, i is even. The residual is even [29,6,≥14]; we also impose the Griesmer bound on its ordinary residuals.
Only 2 nontrivial pairs remain: (a,b,i,j)=(48,48,34,14),(48,52,32,16).
Let X,Y count the pairs in these 2 cells, excluding the pair consisting of zero and c. The 128 codewords of D form 64 pairs, so
 X+Y=63.
Since D is full-length of dimension 7, its first moment is Σ_{x∈D}wt(x)=2⁶·97=6208.
The zero-and-c pair contributes 68, and each pair in the respective cells contributes 96,100, so
 68+96X+100Y=6208, or 96X+100Y=6140.
Multiplying the total-count equation by 97 and subtracting this equation gives
 X−3Y=97·63−6140=−29.
Thus X=40,Y=23. D would have weight distribution 48^103 52^23 68^1, but B₂=−1.

The integer Farkas combination multiplies the following 3 ≤ inequalities
 −X−Y≤−63,  −X+3Y≤29,  96X+72Y≤5368
by 90,6,1, respectively. The left-hand side is 0 and the right-hand side is −128.
This is the certificate in `final-certificate.json:D68` (normalized by a positive common factor).

### 5.3 Classifying the weight distribution and column set

The nonzero weights of D are 48,52,64. Put b=A₆₄ and a=A₅₂. Then
 a+4b=28,  A₄₈=99+3b,  B₂=3b−6.
Hence b∈{2,3,4,5,6,7}, a∈{20,16,12,8,4,0}.

Identify the message space of D with F₂⁷.
Let V be the set of a messages of weight 52 and W the set of b messages of weight 64.
These are distinct nonzero points. Form an auxiliary column multiset M with each point of V once and each point of W 4 times (length 28).
Fourier inversion gives the multiplicity m_D(y) of a nonzero column y in a generator matrix of the original D as
 `m_D(y)=(12−Σ_{u∈V}(−1)^{u·y}−4Σ_{u∈W}(−1)^{u·y})/16`
        =(wt_M(y)−8)/8  (y≠0).
Thus M is 8-divisible, every nonzero message has weight at least 8, and the dimension is 7.

The code obtained by projection onto V is full-length, projective, and 4-divisible.
Since M is 8-divisible, the supports of any 2 codewords on V intersect in a multiple of 4 coordinates.
If V had a codeword of weight 4, all other codewords would be zero or all-one on those 4 support coordinates, making those 4 columns equal.
This contradicts projectivity, so every nonzero weight of V is at least 8.

This intersection divisibility makes wt(v)/4 mod2 a linear map on V.
Let V₈ be its kernel, and suppose the map is nonzero.
Coordinates vanishing on the kernel correspond to the unique nonzero functional on V/V₈, so projectivity of V allows at most 1 such coordinate.
Let z count the coordinates on which V₈ vanishes identically; projectivity gives z≤1. Thus the average weight on V\V₈ is (a+z)/2≤(20+1)/2=10.5.
However, every such weight is 4 mod8 and is not 4, hence is at least 12, a contradiction.
Thus V itself is 8-divisible, with nonzero weights 8,16 only.

Suppose a>0, and write r=dim V. Eliminating the first 3 moments of a projective 8-divisible code gives
 a²−47a+512=2^(9−r).
The unique solution with a∈{4,8,12,16,20}, 1≤r≤7 is (a,r)=(16,5).
If a=0, then M=4W. Its 8-divisibility makes W an even code, but an even code of length 7 has dimension ≤6, contrary to the dimension 7 of M.
Thus b=3, D has weight distribution 48^108 52^16 64^3, and B₂=3.

V is projective [16,5,8], with weight distribution 8^30 16^1.
The functional corresponding to the weight-16 codeword is 1 on all 16 points of V, so V is an entire affine hyperplane in a 5-dimensional space.
Since M and V are both 8-divisible, the projection onto W is an even code of length 3.
The 3 points are distinct and nonzero, so dim W=2, and W consists of all nonzero points of a 2-dimensional space.
Since dim M=7=5+2, the 2 projections are independent and the column space splits as a direct sum.

We may therefore write a nonzero column as y=(a,t,b), a∈F₂, t∈F₂⁴, b∈F₂².
The expression for m_D(y) gives the following columns for all 97 coordinates of D.
- In each of the 3 blocks with b≠0: (0,t,b),(1,t,b) occur once each for t≠0 (30 coordinates), and (1,0,b) occurs twice.
- The additional 1 coordinate: (1,0,0).
This is unique up to equivalence, without importing candidates from LinCode.
verify_final.py generates only the 128 codewords of this column set, checking the distribution 48^108 52^16 64^3 and SO as a positive control.

## 6. A Fourier lemma involving only 4 integers

Assign real numbers T_j to the 3 nonzero points j of G=F₂², and put `S_β=Σ_{j≠0}(−1)^{β·j}T_j`.
Then Σ_β S_β=0. If S_β≤H and S_β≡H mod8, write `S_β=H−8z_β` with nonnegative integers z_β≥0; then Σz_β=H/2.
For nonzero j, `T_j=(1/4)Σ_β(−1)^{β·j}S_β=−2Σ_β(−1)^{β·j}z_β`.
Consequently,
- if H=4, then T_j∈{−4,0,4};
- if H=6, then T_j∈{−6,−2,2,6}.
The latter follows because the sum is 3, making the signed sum odd. No classification search is needed.
The checker merely enumerates the 10 and 20 quadruples of nonnegative integers with sum 2 or 3.

## 7. Excluding C when D has effective length 96

On the 3 cosets of U from Section 4, let s_j:U→{±1}, |U|=32, be the sign functions of a representative of C\D.
Put `T_j(v)=Σ_{x∈U}s_j(x)(−1)^{v·x}`.

When N=96, the weights in C\D are 2 mod4 and at least 46, so the length-96 Walsh values are 4 mod8 and at most 4.
For fixed v, Section 6 applies to the 4 quotient characters β with H=4.
Hence every T_j(v) has absolute value at most 4.
But Parseval gives Σ_v T_j(v)²=32²=1024, whereas the upper bound is 32·16=512, a contradiction.

When N=97, every codeword in C\D is 1 at the unique zero coordinate of D.
The length-96 Walsh values are 6 mod8 and at most 6, so Section 6 applies with H=6.
Each T_j(v)∈{±2,±6}. Fix any j and write s=s_j.
Parseval implies that 28 values have |T|=6 and 4 have |T|=2, giving ΣT⁴=36352.
Since T(0)=32−2wt(the negative-sign set of s) is 2 mod4, the negative-sign set has odd size.
For nonzero h, R(h)=Σ_x s(x)s(x+h)=32−4m_h.
Here m_h counts the disagreeing pairs {x,x+h}, and has the same parity as the size of the negative-sign set. Thus R(h)≡4 mod8 and R(h)²≥16.
Since R(0)=32, the Fourier fourth-moment identity gives
 Σ_v T(v)⁴=32Σ_h R(h)²≥32(32²+31·16)=48640.
This contradicts 36352<48640.

## 8. Excluding C when D has effective length 97

Use the 3 blocks of 32 coordinates and the additional 1 coordinate from Section 5.
By adding the row of D corresponding to a, a representative of C\D can be made 0 at the additional coordinate. Fix its sign there to be +1.
In each block j, for t≠0 write s₀(t),s₁(t) for the signs on (0,t,j),(1,t,j).
At t=0, write `s_A(0),s_B(0)` for the signs on the 2 repeated coordinates.

Put P(t)=s₀(t)+s₁(t), Q(t)=s₀(t)−s₁(t) (t≠0),
and `P(0)=s_A(0)+s_B(0)`, Q(0)=−P(0).
For a character τ∈F₂⁴, put P̂(τ)=Σ_t P(t)(−1)^{τ·t}, Q̂(τ)=Σ_t Q(t)(−1)^{τ·t}.
For messages of D with a=0, the block Fourier coefficients are the transform of P; with a=1, they are the transform of Q.
The total Walsh value on C\D is 97−2wt(c)≤5 and is 5 mod8.
The additional coordinate contributes +1 when a=0 and −1 when a=1.
Thus, for fixed τ, Section 6 applies to the 4 characters of the quotient F₂² with H=4,H=6, respectively.
The 16 Fourier coefficients of P have absolute value ≤4, and those of Q have absolute value ≤6.
Parseval gives
 Σ_t P(t)²≤16, Σ_t Q(t)²≤36.
However, the 15 pairs with t≠0 satisfy P(t)²+Q(t)²=4, and at t=0 we have 2P(0)²≥0, so
 Σ_t(P(t)²+Q(t)²)≥60.
This contradicts the upper bound 16+36=52.

Sections 2,7,8 cover all branches of effective length and minimum weight. Hence there is no SO [97,8,≥46] code. Since zero coordinates can be added to shorter codes, ñ₂(8,46)≥98 also follows. □

