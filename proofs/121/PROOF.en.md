- **Claim:** No binary self-orthogonal [121,8,≥58] code exists; this is Lemma 22 of Kurz's October 29 draft (arXiv:2610.39870v1).
- **Method:** No exhaustive computer enumeration of codes is used. Finite exact computations (certificates and tables) are used. Lemma 20 is assumed.
- **Status:** Found using AI tools and checked by independent AI reviews and exact computer checks. Not yet checked by a human expert.

Note: Bibliographic labels in the body refer to the October 26 source draft. Statements about Lean formalization or completion of a new independent review describe the original proof-writing stage; they do not deny the subsequent independent AI reviews and exact checks reported in the status panel.

# Nonexistence of SO [121,8,≥58]₂: mathematical lemmas and exact certificates

**Theorem. There is no binary self-orthogonal [121,8,≥58] code.**

The proof consists of Lemma 20 in Kurz's draft, which supplies full length, the established Griesmer, Ward, and MacWilliams results, the mathematical lemmas below, and the accompanying finite integer/rational certificates. We do not use LinCode, the draft's LinCode classification tables, or its exclusions obtained by classification. We do use finite tables containing all weight distributions satisfying necessary conditions, but these do not classify actual codes or equivalence classes of generator matrices.

The mathematical arguments are in §§1–8,20,31,33 and Appendix A. The finite computations are in §§9–19,22,28,30,32,34. The verification entry point is `verify_final.py`, run as `python -X utf8 -B verify_final.py`. All checks use standard-library integers and Fraction, without calling an LP solver. The general mathematical implications have not been formalized in Lean.

Section numbering is retained from an earlier working record in which the conditions were introduced; that record itself is not included in the publication package. Sections describing trials not used in the final exclusion are omitted. The exclusion of a particular distribution in §31 is subsumed by §33, but is retained as an accessible special case. The completed round 22, strengthening round 21, is recorded in §32.

The argument proceeds by excluding minimum distance ≥60→deriving the 7 distributions of D=C4→forming a table containing all necessary distributions of the weight-58 residual R→excluding 503 of 3,421 pairs→2,918→1,248→662→256→206→191→30→0 pairs. Each exclusion follows from an exact Farkas certificate or an explicit integrality or mathematical implication. LP feasibility is not treated as code existence, and a candidate is not excluded merely because a solution is fractional.

## 1. Definitions, results used, and scope of verification

A binary [n,k,d] code means a code with minimum distance **at least** d, following footnote 2 on printed p.3 of Kurz's draft.
We use the Griesmer bound, Proposition 1, Lemmas 1–3, Lemma 20, the MacWilliams identities, and the binary case of Theorem 1 in the draft.
Theorem 1 is attributed to H. N. Ward, *Divisibility of codes meeting the Griesmer bound*, J. Combin. Theory Ser. A 83(1),79–93 (1998), Theorem 1 (reference [65] in the draft).
We adopt the draft's statement that, over a prime field, n=g(k,d) and 2^r|d imply that all codeword weights are multiples of 2^r. The original proof has not been rechecked.
The derivation of C4 below uses neither LinCode, code classification tables, nor the Solomon–Stiffler/Belov structure theorem. For full length we assume the nonexistence of SO [120,8,58] from Lemma 20 of the draft (printed p.21), as permitted in the source task. The proof given there cites known dimension-7 bounds and the structure of Griesmer codes, but not the LinCode classifications in Lemmas 21 and 22. We do not reprove Lemma 20 itself.

For a point of multiplicity m in full-length [n,k,d], shortening gives n−m≥g(k−1,d), bounding m from above.
The remaining columns after shortening form a full-length code. Residual full length is used only when the parent is full-length.
The residual of an SO code is even, but need not be SO. We treat a residual as SO only when Ward's theorem has established 4-divisibility.
B1 counts zero columns; B2 counts unordered pairs of equal columns, including pairs of zero columns.

For a full-length code with column multiplicities m(y) and codeword weights w(u), for y≠0 we have

    m(y)=−2^(1−k) Σ_u w(u)(−1)^(u·y).

The sum of all codeword weights is 2^(k−1)n. All Walsh transforms below are defined as unnormalized sums.
An r-dimensional code whose nonzero weights are all a is a repeated simplex code, with every nonzero column occurring a/2^(r−1) times. This also follows from the inversion formula above.

The mathematical arguments are given in this file; finite arithmetic is checked by `verify_final.py` and the independent verification files it calls. They do not import the solving-side Python code. They do not, however, automatically prove the coding-theoretic modeling of the LPs.

## 2. The branch of minimum distance at least 60 is impossible

Since g(8,60)=121, the code is full-length and is 4-divisible by Ward. It is projective since g(7,60)=120.
Lemmas 1–3 and Griesmer leave weights 60,64,72,88.

Weight 72 gives a full-length even [49,7,24] residual. Since g(7,24)=49, Ward makes it 8-divisible and SO. Of the possible weights 24,32,40,48, weight 40 is excluded by Griesmer for its residual, and 48 by the full-length SO exclusion of n−1.
For the remaining weights 24,32, the total count and first moment give A24=116,A32=11, and B2=−5.

Weight 88 gives a full-length even [33,7,16] residual. Since g(7,16)=33, Ward makes it 16-divisible and SO.
Weight 32=n−1 is excluded, while weight 16 alone gives 127·16≠64·33.

Thus only weights 60,64 remain for the original code. The total count and first moment give A60=208,A64=47, B2=−27.
The model/result JSON files `no_R49`, `no_R33`, `no_C60` are Farkas certificates for the respective small contradictions.
The 3 Ward applications are 4|60 for [121,8,60], 8|24 for [49,7,24], and 16|16 for [33,7,16]. In all cases k≥1 and Griesmer equality hold, so the actual minimum distance is the specified d as well.

## 3. Lengths and multiplicities of C and D=C4

Henceforth suppose C is SO [121,8,≥58]. By Section 2, weight 58 occurs, and the kernel D of q(x)=wt(x)/2 mod2 has dimension 7, minimum distance at least 60, and is 4-divisible.
The nonexistence of SO [120,8,58] in Lemma 20 makes C full-length.
Shortening C at a point gives an SO code of dimension 7, containing a doubly-even subcode of dimension at least 6 and minimum distance at least 60. Its length is therefore at least g(6,60)=119. Thus the multiplicities of C are at most 2.
The effective length L of D is at least g(7,60)=120, hence 120 or 121. Shortening D at a point similarly gives m≤L−119. D is projective if L=120 and has multiplicities at most 2 if L=121.
Since D⊆C gives C⊥⊆D⊥, we have B2(C)≤B2(D). Returning D with L=120 to the original 121 coordinates introduces only 1 zero column, so B2(D)=0 in that case as well.

## 4. The case L=120

D is obtained by removing 7 points from the 127-point 7-dimensional simplex code. Its weights are 60 or 64.
The complement T has weights 0 or 4. The formula for one-weight codes of length 7 shows that T consists of all 7 nonzero points of a 3-dimensional space.
Thus the weight distribution of D is

    60^112 64^15.

Superscripts denote numbers of codewords.

## 5. L=121: the structure obtained by shortening at a repeated point

If D were projective, its complement in the simplex code would consist of 6 distinct points, with every nonzero weight equal to 4.
The one-weight formula would require a 2-fold repetition of a dimension-2 simplex code, contradicting distinctness.
Thus D has a repeated point p. Shortening at its 2 coordinates gives a full-length 4-divisible E=[119,6,60].

Write the nonzero weights of E as 60+4j(u). Then j(u)≥0, and summing the weights gives Σj(u)=7.
Form the multiset M containing each nonzero u∈F2^6 with multiplicity j(u). Inversion gives

    m_E(y)=1+wt_M(y)/4   (y≠0)

Thus M is a 4-divisible code of length 7. Its only nonzero weight is 4, so M is precisely the dimension-3 simplex code.
Consequently,

    E: 60^56 64^7.

Let U⊂F2^6 be the annihilator of the 3-space spanned by M. Then dim U=3, and the columns of E have multiplicity 1 on `U\{0}` and multiplicity 2 outside U.

## 6. Reduction to 64 nonnegative integers

A representative h of D/E is 11 at the 2 removed coordinates. At each column y of E among the remaining 119 coordinates, let s(y) be the sum of the signs (−1)^h.
Then s(0)=0, with values ±1 on `U\{0}` and 0,±2 outside U.
Its Walsh transform F(u) satisfies

    wt(h+E(u))=(123−F(u))/2,
    F(u)≤3,  F(u)≡3 (mod8).

Hence J(u)=(3−F(u))/8 is a nonnegative integer, with ΣJ=24.
Write y=(z,t)∈F2^3×F2^3 with U={t=0}, and let the dual variable be u=(a,b).
Writing F0(a) for the Walsh transform of the 7 signs on `U\{0}`, we have

    Σ_b J(a,b)=3−F0(a).

A small check of all 128 assignments of the 7 signs shows that max F0≤3 permits only the following 2 types.

- I: F0 has value −7 once and value 1 at 7 points. Translate the position of −7 to 0.
- II: value −5 once, −1 at 4 points, and 3 at 3 points. After moving the position of −5 to 0, the positions of 3 are the 3 nonzero points of a 2-space P.

`verify_hand_basics.py` independently checks all 128 assignments. There are 8 sign vectors of type I and 56 of type II.

For fixed t≠0, put `v_a(t)=Σ_b J(a,b)(−1)^(b·t)`. Inversion gives

    Σ_a v_a(t)(−1)^(a·z) = −8s(z,t) ∈ {0,±16}.

We use this to determine only the multiplicities of J, without enumerating J itself.

## 7. Type I

The row masses of J are 10 at a=0 and 2 at each of the 7 rows a≠0.
Put `a_a=v_a/2`. For a≠0, a_a∈{0,±1}, and |a_0|≤5.
The 8-point Walsh transform has values only 0,±8. Inversion implies that all a_a have the same parity.
If they are even, the 7 values a_a are 0, and the remaining a_0 is also 0.
If they are odd, those 7 values are ±1. Parseval gives q=(a_0^2+7)/8∈{1,2,4} for the number q of nonzero transform entries.
By inversion the parity of a_a is the parity of q, so q=1. Thus a_0=±1, and a is a signed character.
This local implication is also checked on 11·3^7=24,057 small integer vectors; all 17 qualifying vectors have the stated form.

A nonnegative integer row of mass 2 consists of a point repeated twice or 2 distinct points.
In the latter case, its Fourier zero set is t·d=1, where d is the difference of the 2 points.
The 7 rows have the same zero set, so either all are repeated points or all are pairs with the same difference d.

In the former case, let β(a) be the repeated-point position for a≠0. For each nonzero frequency t, the local conclusion gives a linear form ℓ_t such that `v_a(t)/2=(−1)^(c(t)+ℓ_t(a))` for all a∈F2^3. Fix distinct nonzero a1,a2, so a1+a2≠0. Then

    c(t)=(β(a1)+β(a2)+β(a1+a2))·t  (mod 2).

Indeed, adding the 3 exponents c(t)+ℓ_t(a1), c(t)+ℓ_t(a2), c(t)+ℓ_t(a1+a2) cancels the linear parts and leaves c(t). Put β0=β(a1)+β(a2)+β(a1+a2) and define β(0)=β0. Then β(a)·t=c(t)+ℓ_t(a) at every nonzero t, so β is affine in a. Also v_0(t)=2(−1)^(β0·t). Inverting with mass 10 at zero frequency gives J(0,b)=1+2·1_(b=β0), namely 3 at 1 point and 1 at each of the remaining 7 points.
Thus the positive multiplicities of J are 1^7 2^7 3^1.

In the latter case, use the same argument on the 4-point quotient by `<d>`. The row of mass 10 is invariant under d; taking the common value of each pair as its value on the quotient gives mass 5. For nonzero t∈d⊥, the same sum of exponents at 3 points shows that the nonzero Fourier coefficients on the quotient form the character of a point β0. Inversion gives the quotient values 1+1_(b=β0).
Thus 1 pair has value 2 at each point, the remaining 6 points have value 1 each, and each of the other 7 rows has value 1 at each of 2 points.
The positive multiplicities of J are therefore 1^20 2^2.

Adding the 64 weights 60+4J(u) of h+E(u) to the 56 weights 60 and 7 weights 64 of E gives the following 2 possibilities.

    60^105 64^14 68^7 72^1,
    60^98 64^27 68^2.

## 8. Type II

The row masses are 8 at a=0, 0 for `a∈P\{0}`, and 4 on the 4 rows outside P.
Let W_z be the 4-point Walsh transform of the 4 values v_a outside P. The 8-point transform has values `v_0+W_z` and `v_0−W_z`.
These lie in 0,±16, and |v_0|≤8, so v_0∈{0,±8}.

If v_0=0, then W_z∈{0,±16}. The bound |v_a|≤4 and Parseval imply either that all v_a=0, or that all 4 are ±4 with affine-character signs.
If v_0=±8, then all W_z=±8. Parseval implies that all 4 values are ±4, and their 4 signs have product −1.
This implication is also checked on 9·5^4=5,625 small integer vectors; 25 qualify.

If a nonnegative distribution of mass m has Fourier coefficients only 0,±m, it is uniform on a coset of a subspace.
Indeed, the characters of absolute coefficient m are precisely those constant on the support, and all other coefficients vanish; inversion therefore gives uniformity.
Thus the 4 rows are uniform on cosets of a common subspace T. Integrality gives |T|=1,2,4.
The row of mass 8 is also uniform on a coset of a subspace S, with T⊆S by containment of the Fourier zero sets.

On T⊥, the product of the Fourier signs of the 4 rows is a character.
It must be −1 on `S⊥\{0}` and +1 on T⊥\S⊥.
No character is −1 at every nonzero point of a space of dimension at least 2.
If S⊥ is a 1-dimensional line and T⊥ is larger, adding 2 points outside the line produces its nonzero point, again a contradiction.
Thus either S=F2^3, or S=T with dim T=2.

If S=F2^3, the positive multiplicities of J for |T|=1,2,4 are respectively

    1^8 4^4,   1^8 2^8,   1^24.

If S=T is a 2-space, they are 1^16 2^4.
The resulting weight distributions of D are

    60^108 64^15 76^4,
    60^104 64^15 68^8,
    60^96 64^31,
    60^100 64^23 68^4.

Sections 4,7,8 give exactly 7 possibilities, agreeing with the table on p.23 of the draft.
For all 7 possibilities, explicit column multisets are constructed by small Walsh inversions, and their length, dimension, weight distribution, and SO property are checked by `verify_hand_basics.py`. These are examples of D, not of the desired C.

## 9. Initial weight restrictions and the certificate format

All nonzero weights of D lie in 60,64,68,72,76.
Griesmer and evenness of SO residuals initially leave singly-even weights 58,62,...,110, and 118 for C.
If weight 118 occurs, the kernel K supported on its support has dimension at least 6 (the even residual on the 3 outside coordinates has dimension at most 2).
Apart from the weight-118 word itself, the nonzero weights of K are 58 or 60.
K4 would have dimension at least 5 and only nonzero weight 60, contradicting the one-weight requirement 2^(dim K4−1)|60.
Thus the initial singly-even set is S={58,62,66,70,74,78,82,86,90,94,98,102,106,110}.


### 9.1 All ordinary and split MacWilliams conditions

Put `K_j^(n)(w)=Σ_t (−1)^t binom(w,t) binom(n−w,j−t)`. For a code of dimension k, set A0=1 and write

    2^k B_j = Σ_w A_w K_j^(n)(w).

We use B_j≥0, B1=0 for full length, B2=0 for projectivity, and `B_j≥A_j` for SO. If D⊆C, then C⊥⊆D⊥, giving `B_j(C)≤B_j(D)`. Comparisons use the same length, including zero columns. The first moments for a full-length code are

    Σ_(w>0) A_w = 2^k−1,
    Σ_w w A_w = 2^(k−1)n,
    Σ_w w² A_w = 2^(k−2)n(n+1)+2^(k−1)B2.

Choose a singly-even anchor c of weight w<116, so `C=D⊕<c>`. A nontrivial pair {x,x+c} contains 1 word of D of weight a and 1 word of C\D of weight b; its cell count X_(a,b) is a nonnegative integer. The inside and outside weights are i=(w+a−b)/2, j=(a+b−w)/2. SO makes i,j even. Include the zero pair {0,c} separately, once. The map D→Res(C;c) is an isomorphism, and each nonzero residual word corresponds to 1 cell.

The split dual coefficient multiplied by 256 is the zero-pair contribution plus

    Σ X_(a,b)[K_r^(w)(i)+K_r^(w)(w−i)]K_s^(121−w)(j)

For all degrees 0≤r≤w, 0≤s≤121−w, impose dual coefficient ≥ original split coefficient, as required by C⊆C⊥. Also, q(x)=wt(x)/2 mod2 is linear on the SO code C, so q(x)=v·x for some ambient vector v. The signed MacWilliams sum is 256 times the split count in the coset v+C⊥ and is nonnegative. In this shadow condition, replace the “+” in the displayed sum by “−”: the sign on D is + and that on C\D is −.

The initial iteration excluded 43 weights in total across the 7 cases by conditional Farkas certificates. `iter-summary.json` records their exclusion order within each case. `verify_initial_proof.py` independently reconstructs the zero weights and residual constraints available at each stage, and checks that the added rows in each certificate are the correct split formulas.

### 9.2 Recursive residual restrictions and their justification

For a codeword of weight w<2d in full-length [n,k,≥d], the residual outside its support is full-length [n−w,k−1,≥d−floor(w/2)]. If the parent is SO, the residual is even and the lower bound is rounded up to an even integer. A residual of a general even code is not assumed SO. Only in the Griesmer equality case is Ward used to increase divisibility by a power of 2; 4-divisibility then gives SO. For an odd minimum-distance lower bound d, use necessary conditions on the parity extension [n+1,k,≥d+1], allowing its added coordinate to be zero.

A full-length SO code cannot have weight n−1: its projection onto the 1 complementary coordinate is always even, forcing that column to be zero. A projective SO code cannot have weight n−2: the projection onto the 2 complementary coordinates is even, forcing the 2 columns to be equal. A multiplicity bound m gives B2≤floor(n(m−1)/2).

If a codeword of weight 2d exists and the kernel supported there has dimension r, all its nonzero weights except the all-one word are d. Shortening at 1 coordinate gives a one-weight subcode of dimension r−1, so 2^(r−2)|d (r≥2). The outside projection dimension gives r≥k−(n−2d), improved to r≥k−(n−2d−1) for an SO parent with nonempty outside support. We use the resulting integer contradictions. In a branch containing the all-one word, impose A_n=1 and `A_w=A_(n−w)`; a Farkas contradiction confined to that branch yields A_n=0 in the parent system.

For child codes as well, form ordinary weight-distribution LPs using allowed weights, total count and first moment, MacWilliams nonnegativity, and the full-length, SO, and column-multiplicity conditions already justified at that stage. A Farkas contradiction for the child system (including a contradiction from moments alone) excludes the parent weight producing that child. This rule is used in addition to checking the residual Griesmer bound. For example, nonexistence of children [22,6,≥10] and [14,6,≥6] excludes weights 42,50 in W63 and 38,46 in W59.

These recursions are recorded in the 256 entries of `recursive-audit.json`. `verify_initial_proof.py` independently checks child parameters, Ward's Griesmer equality and divisibility conditions, the SO dimension bound, the all-one branches, and 173 LP matrices. Every Ward application has n=g(k,d), 2^r|d, k≥1, with actual distance d by equality. The 4 small lemmas are reproduced in Appendix A. The same rules used by the historical search routine `rsupport` are independently reimplemented in `verify_round12.py:allowed`.

### 9.3 Complete containing tables of integer distributions and the initial 3,421 pairs

R=Res(C;c58) is full-length even [63,7,≥30]. Its necessary weight set is

    W63={30,32,34,36,38,40,44,46,48,52,56,62}.

The Gauss sum of q=wt/2 satisfies G∈{0,−64,−32,−16,16,32,64,128}. This follows by applying the sum-of-squares argument of §13 in dimension 7. When G is nonzero, the polar form has rank 0,2,4,6, and q vanishes on its radical; rank 0 permits only G=128.

`R63-gauss-integers.json` (65,902 rows) contains all integer distributions satisfying the total count and moments of orders 1 and 2 for R, B2∈{0,…,15}, all MacWilliams nonnegative-integrality conditions, and the Gauss-sum condition. An independent loop checks this by successively choosing counts from the highest weight down within finite ranges, then determining the final 2 counts from the total and first moment. It visits 371,033 moment-consistent vectors; after the Gauss and full MacWilliams tests, the result agrees exactly with the saved table.

The 129 rational cuts from low-degree conditions on second residuals (B2–B4, or B1–B4 of the parity extension when the distance lower bound is odd) leave 574 rows. Each cut applies only when its anchor count is positive. `R63-universal.json` and `R63-universal-templates.json` contain the certificates and matrices.

Next combine the weights d_i of nonzero words of D with their corresponding residual weights r_i. The weights in C\D satisfy `58−d_i+2r_i≥58`, hence `d_i≤2r_i`. By the rearrangement inequality, Σd_i r_i is at most the sum of similarly ordered products and at least the sum of oppositely ordered products. Also,

    256 B2(C) = binom(121,2)+K2^(121)(58)
                 +Σ_i(4d_i²−232d_i)+Σ_i(8r_i²−20r_i+7212)−8Σ_i d_i r_i.

Combine this with B2(R)≤B2(C)≤B2(D). Intersecting the 7 compatible tables from these necessary conditions with the 574 rows gives 3,421 pairs. `verify_universal_compatibility.py` independently checks the formula and every table. The provenance and original row number of R for each pair are in `fixedR-pair-catalog.json`; no pair comes from LinCode.

Fix R as the outside marginal of the weight-58 split table for each of the 3,421 pairs, and impose §9.1. Farkas certificates exclude 503 pairs. The remaining 2,918 are treated from §10 onward. `verify_resume.py` reconstructs all pairs and checks the exclusion certificates. Rational feasible solutions for surviving pairs are also checked, without inferring actual code existence.

### 9.4 Certificate format

All LPs have the form MX≤b, X≥0. A Farkas certificate is a nonnegative rational vector λ satisfying λM≥0 and λb<0, yielding the contradiction 0≤λMX≤λb<0. Clearing denominators and storing integers gives the same verification.

For a parameterized system MX≤Bz, λM≥0 gives the necessary condition λBz≥0. A cut is shared only with candidates satisfying its conditions, such as existence of the anchor. An upper-bound certificate λM≥c gives cX≤λb. Optimality is not required for exclusion; validity of this bound suffices. The rounding formulas for integer-valued quantities and quantities in known residue classes are given in §16.

The checker does not merely trust saved matrices: it also verifies that every row used is reconstructed from the formulas in this proof. The underlying mathematical implications are justified by the mathematical argument, not by a software formalization.

## 10. Iteration: second residuals and all split MacWilliams identities (round 1)

The conditions in this section do not use LinCode classification tables or exclusions obtained by classification.
Let R=Res(C;c), wt(c)=58, so R is full-length even [63,7,30], with B2(R)≤B2(C)≤B2(D)≤15.
The stronger bound 15 is already imposed in §9.3 through the integer table for R and compatibility conditions. By contrast, the explicit B2(R) upper-bound row saved in the initial fixed-R LP has bound 63, a weaker necessary condition than 15. The fixed R marginal already satisfies bound 15, so this is a safe relaxation; not every LP row is claimed to represent the bound 15 itself.
Fix a candidate distribution A, and take a word r∈R with A_w>0 and w<60. R is even but is not assumed SO.
T=Res(R;r) is full-length [L,6,δ], where L=63−w, δ=30−w/2.
The weight set for T is obtained from Griesmer, its ordinary residuals, and Ward only when Griesmer equality holds (implemented in the historical search routine `rscreen.py:rsupport`, which is not included in the publication package).
We also use the established nonexistence of even [13,5,6], [41,6,20], [25,6,12], [17,6,8] (Appendix A; see Section 5.1 of `../97/PROOF.en.md` in the publication package).
The columns of T are the outside columns of R with 1 zero row removed, so B2(T)≤B2(R). No new identifications of points occur.

Pair {x,x+r} in R, omit {0,r}, and put a=wt(x)≤b=wt(x+r).
Let X_(a,b)≥0 count the pairs, and put i=(w+a−b)/2, j=(a+b−w)/2.
Require 0≤i≤w, j to be an allowed weight of T, and the count of each a to be `A_a−1_(a=w)`. Since R is not SO, no evenness condition is imposed on i.
The first moment of T is ΣjX=32L; in every degree, binom(L,s)+ΣX K_s^(L)(j)≥0.
The condition B2(T)≤B2(R) is ΣX K_2^(L)(j)≤64B2(R)−binom(L,2).
If δ is odd, add a parity coordinate to T and impose MacWilliams nonnegativity in every degree for the weights j+(j mod2). The added column is allowed to be zero.

The dual split coefficient for the support-w/outside-L partition of R itself, multiplied by 128, is

    (K_u^(w)(0)+K_u^(w)(w)) K_v^(L)(0)
    + Σ_(a,b) X_(a,b) (K_u^(w)(i)+K_u^(w)(w−i)) K_v^(L)(j) ≥ 0

Impose this for every 0≤u≤w, 0≤v≤L. Neither R⊆R⊥ nor a shadow condition is used here.
The equations correspond to the Base/Parity/Split rows of `round1_residual.py` (a historical search script not included in the publication package).

Write the matrix system as MX≤Bz, X≥0, `z=(A_30,A_32,...,A_62,B2(R),1)`.
An exact nonnegative rational λ with λM≥0 gives the necessary condition λBz≥0.
Candidates satisfying λBz<0 can be excluded, but only in the branch A_w>0.
Share this with all remaining candidates. Save λ and the rows used, so that the certificate is checked using integer inner products alone.
Candidates yielding fractional feasible solutions are retained. Fractionality is not a reason to claim nonexistence of an integer solution.

## 11. Odd-set conditions from integrality of pairs (round 2)

For an actual code, X_(a,b) in Section 10 counts pairs of codewords and is a nonnegative integer.
For any weight set S, put `b(S)=Σ_(a∈S)(A_a−1_(a=w))`.
A pair entirely within S contributes 2 to b(S); a pair crossing between S and its complement contributes 1.
Thus, if b(S) is odd, the number of crossing pairs is positive and odd. In particular,

    Σ_(a∈S,b∉S or a∉S,b∈S) X_(a,b) ≥ 1.

This is a rigorous necessary condition from integrality, not an exclusion based on finding a fractional LP solution.
In `round2_oddsets.py` (a historical search script not included in the publication package), the `Oddset mask ...` rows express it as −ΣX≤−1.
Masks use the weight order WS=(30,32,34,36,38,40,44,46,48,52,56,62).
When sharing a rational Farkas certificate using such rows, recheck that b(S) is odd for every mask used.
Do not apply the certificate to a candidate failing its mask conditions.

## 13. Gauss sums for second residuals (round 4)

Parity-extend T=[L,6,δ] from Section 10 to an even code T+ of dimension 6.
On T+, q(x)=wt(x)/2 mod2 is a quadratic form whose polar form is the ordinary inner product.
For a quadratic form in dimension 6, the sum G=Σ_x(−1)^q(x) satisfies

    G ∈ {0,−32,−16,−8,8,16,32,64}.

Indeed, if V0 is the radical of the polar form β, then
G²=2^6 Σ_(t∈V0)(−1)^q(t). This is 0 when q|V0 is nonzero, and 2^(6+dim V0) otherwise.
The alternating form β has rank 0,2,4,6. In rank 0 with nonzero sum, q=0 gives G=64, not −64.
Thus, expressing the counts of nonzero words of T of weight j using the X variables of Section 10, one of the 8 equations

    Σ X_(a,b) (−1)^((j+(j mod2))/2) = G−1

holds. Add this equation to the LP for each G.
If all 8 branches are infeasible with exact Farkas certificates, exclude that R distribution and anchor.
Retain the candidate if even 1 branch is feasible. Finding a single fractional solution whose G is outside the set does not justify exclusion.
When sharing certificates with other R distributions, apply them only to the same anchor and G branch.
The input to this round is the 1,248 pairs from round 2. The 4-part split in round 3 excluded no additional pairs and is not part of the proof's dependencies.

## 14. The radical of the quadratic form and signed MacWilliams identities (round 5)

For the surviving R in round 4, the Gauss sum G of q=wt/2 mod2 is nonzero.
Put S=|G|=2^s, and let H be the radical of β(x,y)=x·y. Then q|H=0, dim H=2s−7.
Thus H=R∩R⊥ is doubly-even, has nonzero weights at least 32, and satisfies `A_w(H)≤A_w(R)`.
Griesmer bounds the number of zero columns of H by B1(H)≤63−g(dim H,32).

For each word y in the ambient space, put F(y)=Σ_(x∈R)(−1)^(q(x)+x·y).
The sum-of-squares calculation for quadratic forms gives |F(y)|=S for y∈H⊥ and F(y)=0 otherwise.
Summing over words y of weight j gives

    T_j=Σ_w (−1)^(w/2) A_w(R) K_j^(63)(w)=Σ_(wt(y)=j) F(y).

Thus S|T_j, `|T_j|/S≤B_j(H)`. Also R⊥⊆H⊥ gives `B_j(R)≤B_j(H)`.
Combine these necessary conditions in every degree with the full MacWilliams identities and SO property of H in a small LP for its unknown weight distribution.
Exclude only R for which this LP is infeasible. A feasible fractional H distribution does not justify exclusion.
The rows of `round5_radical.py` (a historical search script not included in the publication package) correspond to `ordinary`, `H subset R`, `H zero columns`, `radical dual bound j`.

## 15. Residuals anchored at radical codewords (round 6)

Fix the weight w of a nonzero word h in H=R∩R⊥ from Section 14. Since H is doubly-even, w≡0 mod4.
Since h is orthogonal to all of R, the intersection i in the pairs of Section 10 is even. Evenness of R makes the outside weight j even as well.
Thus Res(R;h) is full-length even [63−w,6,30−w/2]. The remaining H weights are below 60, so the residual has dimension 6.
Restrict the cells in Section 10 to even i and j in the allowed weight set of this even residual.
If this LP is infeasible, exclude **only weight w in the radical H**, not all codewords of weight w in the original R.
When sharing rational certificates with other R candidates, retain the same conditional implication for a radical anchor.
Finally return A_w(H)=0 to the H LP of Section 14, and exclude only those R candidates for which it becomes infeasible.

## 16. Strengthening radical integrality and parity conditions by LP dual bounds (round 7)

The F(y) of Section 14 takes values ±S on H⊥ and is zero elsewhere.
Let N+,N− count the positive and negative values at weight j. Then B_j(H)=N++N−, T_j/S=N+−N−.
Hence `B_j(H)≡T_j/S` (mod2). Also A_w(H) is an integer.

Suppose the rational LP gives upper bound U and lower bound L on a linear quantity f, and f≡r (mod p) is known. Then strengthen the bounds to

    r+p ceil((L−r)/p) ≤ f ≤ r+p floor((U−r)/p)

For A_w(H), use (p,r)=(1,0); for B_j(H), use (2,(T_j/S) mod2).
This rounds bounds common to all feasible points to integers; it does not exclude a fractional solution merely because it is fractional.
Save a dual vector y≥0, yM≥c, yb=optimal value for each maximization.
The inequality chain and final Farkas certificate can be checked using only integer and Fraction inner products.
This stage performs no branching or exhaustive candidate search, only LP optimization and addition of justified bounds.


## 18. Lifting the radical to C4 and linking the support of length 58 to its complement of length 63 (round 9)

Write `C=D⊕<c>`, wt(c)=58, D=C4. Projection from D to R=Res(C;c) is an isomorphism in dimension 7.
For a word d of D with inside and outside weights (i,j), both i,j are even, and i+j≡0 mod4.
Thus the inside and outside forms q=wt/2 mod2 induce the same quadratic form on the message space of D.
Let H_D be the subcode obtained by lifting its radical H_R back to D. Then dim H_D=dim H_R=h, H_D⊆D, and its minimum weight is at least 60.
Both the inside and outside projections of H_D are doubly-even.
The 40 residual distributions remaining here have maximum weight at most 48, while the minimum weight of D is 60; hence the inside projection is also injective, of dimension h.

In the 1-word split table at weight 58, X_(a,b,i,j) represents 1 word of D and 1 word of C\D.
Let Y in the same cells count words of H_D, with 0≤Y≤X, permitting only cells with j≡0 mod4.
Impose all radical conditions through round 7 on the outside marginal of Y.
Impose the full MacWilliams identities and SO property on H_D at length 121 and its inside projection at length 58.
Griesmer bounds the zero columns of H_D by B1(H_D)≤121−g(h,60).

For split degree (r,s), let `F_D,F_H` be the unnormalized Krawtchouk sums of D and H_D,
and T_D the sum over D with sign (−1)^(j/2). Each nonzero word is counted once in 1 cell.
Since H_D⊆C⊆C⊥ and H_D⊆D,

    F_H/2^h ≥ A_(r,s)(C),
    F_H/2^h ≥ F_D/128.

Moreover, the radical of this quadratic form is H_D. Applying the argument of Section 14 to D in the ambient 121 coordinates gives

    S F_H ≥ ±2^h T_D.

Here S is the absolute Gauss sum of the fixed R distribution.
In `round9_lifted_radical.py` (a historical search script not included in the publication package), these are the `Hdual>=C`, `Hdual>=Ddual`, and `Lifted Gauss plus/minus` rows.
Check every split degree, and exclude a specified C4,R pair only if its LP becomes infeasible.

## 19. Iterating with a common C marginal across multiple anchors (round 10)

Let X be the round-9 variables with C4 and the weight-58 residual distribution fixed.
Assume a codeword of another singly-even weight w exists, and form its ordinary 1-word split table Z.
Equate every C weight count obtained from X with the corresponding count from Z. Different anchors may not use different C distributions.
Impose on Z the residual conditions for a full-length even [121−w,7,≥58−w/2 rounded up to an even integer] code, and the split dual/shadow conditions in every degree.

This residual is also even of dimension 7, so its Gauss sum is one of {0,−64,−32,−16,16,32,64,128}.
At least 1 of the 8 branches fixing 1+Σ_Z(−1)^(j/2)Z to these values must hold.
First solve the LP without fixing this value. If the solution has an allowed Gauss sum, retain it; otherwise solve the 8 branches exactly.
If all 8 branches (or the unfixed system) are infeasible, weight w cannot occur for this C4,R pair, so return A_w(C)=0 to X.
This uses integrality of A_w in an actual code: if it is positive, an anchor can be chosen. The value of a fractional solution alone never implies A_w=0.
Feed excluded weights into the next anchor conditions and then into the next round. Exclude a pair only when X itself becomes infeasible.

## 20. The full-length 3-dimensional subcode generated by the 4 weight-76 words in case1

The case1 in Section 8 is |T|=1,S=F2^3. Its 4 weight-76 words come from 1 point (a,b_a) for each of the 4 values a outside P.
At every nonzero frequency t the product of the Fourier signs of the 4 rows is +1, so the 4 values b_a sum to 0. Hence the 4 points (a,b_a) form an affine 2-plane.
The 4 words of D lie in the same coset outside E, and their span F has dimension 3. Those 4 words have weight 76; the other 3 nonzero words have nonzero a and hence weight 60 in E.
Thus the sum of all weights of F is `4*76+3*60=484=4*121`, so F is full-length.
The 8 weights in every coset of C/F also sum to 484. In a coset in C\D, all weights are at least 58 and 2 mod4, so each is at most `484−7*58=78`.
Thus in case1, A_w(C)=0 (w>78). This follows from the small Fourier argument of Section 8, without a code classification.

## 22. Returning necessary linear bounds from integer tables of ordinary weight distributions (round 12)

The files `C-integer-case0.json`–`C-integer-case6.json`, constructed from necessary conditions, are integer tables for ordinary C weight distributions with C4 fixed, not code classification tables.
They use counts a_j≥0 on S={58+4j}, Σa_j=128, Σj a_j=J, and the second-moment identity Σbinom(j,2)a_j=Q0+4B2(C).
B2(C) is an integer from 0 to B2(D). Require a_0≥1, and check nonnegative integrality of all MacWilliams coefficients and the conditions that the dual contains C and is contained in the dual of D.
Choose counts starting at high j, bounding them by the remaining mass and nonnegativity of the second moment; the final `a_1,a_0` are determined by the equations. Thus the finite table contains all integer distributions satisfying the necessary conditions (the historical generation script `c_integer.py` is not included in the publication package).

Extract only rows consistent with the fixed case,R and all zero weights already proved. Weights absent from the LP cells are also zero.
For every C weight count, sum of 2 weight counts, and ordinary dual coefficient B_j (1≤j≤16), return to the LP the minimum and maximum over this table.
These are necessary linear inequalities obtained from a containing table of integer solutions; no fractional solution is treated as integral, or used alone to exclude a candidate.
If no rows remain for a case,R, that branch is impossible. `verify_integer_tables.py` independently verifies completeness. In case order, the row counts are 9,127, 108,323, 50,519, 24,871, 31,063, 57,218, 37,513, totaling 318,634. The independent check compares dynamic-programming counts of moment-consistent vectors with the saved table's distinctness, total counts, and moments. Since inclusion of every moment-consistent vector is verified, additional MacWilliams tests need not be assumed for completeness.

## 28. Applying second-residual restrictions to integer distributions of length-59 residuals (round 18)

The residual at a weight-62 word is full-length even [59,7,28]. The existing `R59-gauss-integers.json` is a complete necessary table of distributions satisfying ordinary MacWilliams nonnegative integrality, B2≤15, and the dimension-7 Gauss-sum condition.
For each positive weight w<56 as anchor, take a full-length [59−w,6,28−w/2] residual. By the general argument of Section 10, impose marginal counts, first moment, B2–B4 nonnegativity, and B2(residual)≤B2(parent).
If the minimum-distance lower bound is odd, also impose B1–B4 nonnegativity on the parity extension. The parent is not assumed SO here.
Share rational Farkas certificates as conditional linear inequalities across all distributions. These are exact LP calculations, not searches over generator matrices or code equivalence classes.


The necessary weight set is W59={28,30,32,34,36,40,42,44,48,52,56,58}. Checking 222,496 moment-consistent vectors gives exactly the 23,765 saved distributions after Gauss and full MacWilliams tests. After 50 conditional Farkas cuts, 197 distributions remain. This is not a copy of the draft's classification table of 143 codes.

## 30. Splits with fixed surviving integer distributions of length 59 (round 20)

The 197 distributions surviving round 18 necessarily include any actual length-59 residual. For each C distribution with positive weight-62 count, fix each residual distribution as the outside marginal of the split table.
A row with a positive outside weight that cannot be produced from the C distribution, or with B2(R)>B2(C), is excluded by the corresponding necessary condition alone.
Check all remaining rows by exact LP; if every row has a Farkas certificate of infeasibility, that C distribution is impossible.
This uses a necessary containing table of integer ordinary weight distributions and independently generated rational exclusion certificates, not a LinCode table of surviving codes.

## 31. Excluding a particular C distribution in case1 using column structure and Walsh transforms alone

Here we exclude the branch D=60^108 64^15 76^4, C\D=58^96 62^16 74^16 (case1 in the saved table, C_index=247). This section uses neither LP nor code classification.

### 31.1 Putting the columns of D into standard form

The full-length 3-dimensional subcode F from Section 20 has 3 nonzero weights 60 and 4 weights 76. Identify the dual of its message space with F2^3, and let p be the nonzero point distinguishing the 4 weight-76 words.
Fourier inversion gives column multiplicity 31 at p and 15 at the other 6 nonzero points. D/F has dimension 4.
The 8 weights in every coset other than F sum to 484. Since they are all at least 60 and divisible by 4, each such coset has 1 weight 64 and 7 weights 60.
For each nonzero message u of D/F, let α(u)∈F2^3 be the position of weight 64. The sign sum in the block of column type y of F is −(−1)^(α(u)·y), by 8-point inversion.

For y≠0,p, view the length-15 block as a multiset m_y(v) of 4-dimensional columns v for D/F. Its nonzero-frequency Fourier coefficients are ±1, and the zero-frequency coefficient is 15.
Parseval gives `Σ_v m_y(v)^2=(15^2+15)/16=15=Σ_v m_y(v)`. Nonnegative integrality makes every multiplicity 0 or 1, with only 1 point v_y missing among the 16 points.
Thus for nonzero u, (−1)^(α(u)·y)=(−1)^(u·v_y). Define α(0)=0; each component indexed by these 6 values y is linear.
These 6 points span F2^3, so α(u) itself is linear, including its p component.
The p block has length 31 and the same nonzero-frequency coefficients −(−1)^(u·v_p), so inversion gives `m_p(v)=2−1_(v=v_p)`.
A shear of the basis of D moves every v_y to 0, giving the following column form.

- y≠0,p: each of the 15 points v≠0 occurs once; v=0 does not occur.
- y=p: each of the 15 points v≠0 occurs twice; v=0 occurs once.

Here `y∈F2^3\{0},v∈F2^4`, and the length is `6*15+31=121`. This standard form is derived using the structure of F established in Sections 8,20, not from the weight distribution alone.

### 31.2 The 16 rows for the coset of C

Fix z∈C\D, and let ε_y(v) be the sum of its coordinate signs (−1)^z over columns with the same (y,v).
For y≠p and v≠0 the values ε are ±1, with ε_y(0)=0. At p, ε_p(0)=±1.
Put `s_y(u)=Σ_v ε_y(v)(−1)^(u·v)`. Writing weights in z+D as 58+4J(a,u) gives

    Σ_(y≠0) s_y(u)(−1)^(a·y)=5−8J(a,u),
    Σ_a J(a,u)=5,
    s_y(u)=−Σ_a J(a,u)(−1)^(a·y)  (y≠0).

The assumed C distribution makes J take values 0,1,4, with 16 occurrences of 4 and 16 of 1 in total.
Each of the 16 rows indexed by u has mass 5, so each has 1 entry 4 and 1 entry 1, at distinct positions a(u),b(u).
Thus s_y(u)=−4(−1)^(a(u)·y)−(−1)^(b(u)·y).

### 31.3 The position of 1 is constant, contradicting its marginal count

Fix y≠0,p. For nonzero u−u', exactly 8 values v have inner product 1 with it, and all have v≠0.
Since ε_y(v) is ±1, the sum of these 8 values is even. Thus `s_y(u)−s_y(u')` is divisible by 4.
Reducing the displayed formula mod4 makes (−1)^(b(u)·y) independent of u. Since the 6 values y span the 3-space, b(u)=b0 is constant.
Hence M(b0)=Σ_u J(b0,u)=16.

On the other hand, M(a)=Σ_u J(a,u) has mass 80, and its Fourier coefficient for y≠0 is

    Σ_a M(a)(−1)^(a·y)=−Σ_u s_y(u)=−16 ε_y(0).

This is 0 for the 6 values y≠p, and ±16 at p. Inversion on 8 points makes every M(a) equal to 10±2, hence 8 or 12.
This contradicts M(b0)=16, excluding the C distribution.

The finite checks need only the 127 nonzero codewords of the standard form with 121 columns, orthogonality on 8 and 16 points, and 12<16. No large code search is required.

## 32. Iterating integer C distributions for the remaining 30 pairs (round 22)

For each pair surviving round 10, first add the case1 upper bound 78 from §20 and A66+A70−4A78≥4 from §33. Do not impose these on other cases. From the integer containing table of §22, extract only rows consistent with the pair and the already excluded weights, and return all bounds on weight and dual counts common to these rows to the LP.

In that LP, compute exact upper and lower bounds on each C weight count and each sum of 2 counts. Round the bounds certified by the 128 saved dual vectors to integers, and remove integer C distributions violating them from the containing table. Then fix each remaining distribution in the original table and check it.

Infeasibility of the fixed root LP gives a Farkas contradiction. Surviving fixed C distributions have A62>0, so use the length-59 containing table from §30. Check all 197 rows consistent with B2(R59)≤B2(C) and the weights available in the split, obtaining Farkas contradictions on all branches. Some checking branches allow the special case in §31, but do not count it again when §33 already excludes it.

`round22-state.json` has status=infeasible for all 30 pairs and pairs_left=[]. Fixed-C checks cover 32 distributions counted with repetitions, and fixed length-59 residual checks cover 1,371 branches counted with repetitions. `verify_round22.py` checks completeness, each upper-bound certificate, the fixed C, correspondence with every R59 row, and the final Farkas contradiction. Certificates for the same fixed C may be reused across pairs. No unchecked or feasible branch is counted as excluded.

## 33. A new necessary condition for every C distribution in case1

Use the standard form of D from Section 31.1. For general C, each of the 16 rows J of Section 31.2 still has mass 5, and J ranges from 0 to 5 (Section 20).
Let σ(u)=Σ_a (J(a,u) mod2)a be the XOR of the positions occurring an odd number of times in the row.
On the 6 blocks y≠0,p, s_y(u) mod4 is constant. Since `FourierJ_y=5−2Σ_(a·y=1)J(a,u)`, σ(u)·y is independent of u.
These 6 points span, so σ(u)=σ0 is constant.
The marginal-sum calculation in Section 31.3 does not depend on the form of the C distribution, so M(a)=Σ_u J(a,u) is 8 or 12.

An integer row of mass 5 has only 7 possible partitions of its positive values: 5, 4+1, 3+2, 3+1+1, 2+2+1, 2+1+1+1, 1+1+1+1+1.
For each type, let N_j count positions with value j. Then

    J(σ(u),u) ≥ 1+4N_5−N_3−N_2.

This is immediate for the first 5 types. For type 2+1+1+1, the right-hand side is 0. For 5 entries equal to 1, the XOR of those 5 points lies among them (the XOR of the 3 complementary points is none of those 3), so the left-hand side is 1.
Sum over the 16 rows and use M(σ0)≤12 to get

    16+4A_78(C)−A_70(C)−A_66(C) ≤ 12,
    A_66(C)+A_70(C)−4A_78(C) ≥ 4.

The exclusion of the particular distribution in Section 31 is also a special case of this inequality. The local implication for the 7 types can be independently checked on all 792 small multisets of mass 5 on 8 points.

## 34. Coverage of all candidates and conclusion

|Stage|Input pairs|Excluded pairs|Remaining pairs|Main certificates/checker|
|---|---:|---:|---:|---|
|Initial fixed R|3421|503|2918|fixedR-resume-results.json / verify_resume.py|
|Round 1|2918|1670|1248|round1-state.json / verify_round12.py|
|Round 2|1248|0|1248|round2-state.json / verify_round12.py|
|Round 4|1248|586|662|round4-state.json / verify_round456.py|
|Round 5|662|406|256|round5-state.json / verify_round456.py|
|Round 6|256|50|206|round6-state.json / verify_round456.py|
|Round 7|206|0|206|round7-state.json / verify_round7.py|
|Round 9|206|15|191|round9-state.json / verify_round910.py|
|Round 10|191|161|30|round10-state.json / verify_round910.py|
|Round 22|30|30|0|round22-state.json / verify_round22.py|

Rounds 3,8 excluded 0 additional pairs and are not dependencies of the proof. Exploratory trials in rounds 11–21 were used to obtain the lemmas or certificates in §§20,22,28,30,31,33. The table above completes the final coverage. `verify_final.py` checks the input and output ID sets of each round, absence of duplicates, and runs all independent checks. The full list of surviving pairs, `round22-surviving-pairs.json`, is an empty array.

By §2, the assumed C has weight 58. D is one of the 7 cases, and the complete containing table and compatibility conditions put its residual distribution R in one of the initial 3,421 pairs. Every exclusion in the table is a contradiction to necessary conditions, and all pairs have been excluded. Thus C does not exist. □

## Appendix A. The 4 small nonexistence lemmas used in the recursion

For the four elementary nonexistence lemmas, see Section 5.1 of `../97/PROOF.en.md` in the publication package. The arguments are reproduced below to make the dependencies explicit.

1. Even [13,5,≥6]: g(5,6)=13 forces full length, and Griesmer after shortening forces projectivity. Weight 10 is excluded because its ordinary residual [3,4,≥1] violates Griesmer, leaving nonzero weights 6,8,12. The total count and moments of orders 1 and 2 are ΣA=31, ΣwA=208, Σw²A=1456. Multiplying by 48,−14,1 and adding gives 24A12=32, hence 3A12=4, contrary to integrality. A general [13,5,6] code is also even by Griesmer equality and Ward.
2. [41,6,≥20]: g(6,20)=41 and 4|20 give 4-divisibility and SO by Ward. The code is full-length and projective. Residuals and full-length SO restrictions leave only 20,24,28,32. Weight 28 gives the even [13,5,6] residual excluded above. We have ΣA=63, ΣwA=1312, Σw²A=27552. Multiplying by 480,−44,1 and adding gives 96A32=64, hence 3A32=2, a contradiction.
3. [25,6,≥12]: g(6,12)=25 and 4|12 give 4-divisibility and SO by Ward. Residuals and full length leave weights 12,16. The total count and first moment give A12=52, A16=11. The second moment gives B2=−3, a contradiction.
4. [17,6,≥8]: g(6,8)=17 and 8|8 give 8-divisibility and SO by Ward. Weight 16=n−1 is excluded, leaving only nonzero weight 8. But ΣA=63 and `ΣwA=32*17=544` contradict `63*8=504`.

Every Ward application has k≥1, n=g(k,d), and the stated power of 2 dividing d. These are not exclusions based merely on a fractional solution of a rational relaxation: 1,2 give explicit integrality contradictions, and 3,4 give moment contradictions.

## Appendix B. Implementation and scope of verification

The historical matrix-generation and LP-search code is not distributed in full and is not required to reproduce the checks. The publication package retains the generation-side files `bmodels.py`, `dscreen.py`, `exact_lp.py`, `models.py`, and `split_models.py` only as originals required for provenance-hash checks. Their historical provenance comments are retained as part of the checked byte sequences, not as references to the current publication folders. The verification side consists of `verify_final.py`, `verification_models.py`, `verify_*.py`. The verification side does not import the search side, but checks the saved integers/rationals and the necessary-condition formulas.

In 16 old recursive JSON files, the matrix retained the all-one variable with A_n=0 while only the variable-name array omitted n, an output inconsistency. Following review, the saved JSON `variables` were matched to the full column names reconstructed from the formulas. Matrices, right-hand sides, solutions, and certificates were unchanged. The internal correction list, before/after hash records, 16 original models, and reconstruction record are not included in the publication package. `verify_initial_proof.py` requires exact agreement of column names and every row length, without automatic repair of mismatches. The generated verification report `recursive-metadata-reconstruction.json` is an empty list for the corrected inputs. The historical proof hash is checked against the snapshot `subcode-proof-before-1300.md` included in `data.tar.xz`, not against the updated proof text. The verifier uses this snapshot only for a provenance-hash check and does not derive mathematical constraints from its text.

This is a mathematical proof combining mathematical arguments and finite exact certificates, independent of LinCode. It does not claim a short proof reducing even all certificate checks to arguments without computation, a Lean formalization, or completion of a new independent review. Nor do we claim to have reproved Ward's theorem or Lemma 20 in this work.
