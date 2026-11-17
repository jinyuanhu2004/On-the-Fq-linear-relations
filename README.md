# Megaera in Lean 4

This project formalizes the completeness and dimension results in Jinyuan Hu's *On the Fq-linear relations among multiple zeta values in positive characteristic*. The reference edition is the 26-page file supplied as `Megaera (1).pdf`, SHA-256 `52839ebd866603831f9bc45c045db0009f62f05b7c5f0e2ad734fb965a1a5f45`. The mathematical target is the space of relations among Carlitz multiple polylogarithm values at the all-ones point, as defined in §1.1.

## Main theorems

| Manuscript | Lean declaration | Conclusion |
| --- | --- | --- |
| Theorem 1.10, §2 | `FinalBinary.theorem_1_10_section_two` | Every homogeneous relation is a linear combination of the BCP generators. Every such combination is a relation. |
| Theorem 1.10, §4 | `EditionOneFour.theorem_1_10` | Both cases use the procedure on pp. 24–25. Starting at $G=\operatorname{Ind}P$, cancel its current least tuple when legal, and stop at zero or at an illegal least tuple. [Proof](Megaera/EditionOneFour.lean) |
| Lemma 1.8, Remark 2.14 and Theorem 1.9(iii) | `EditionOneCarry.lemma_1_8`, `remark_2_14`, `relation_iff_carry` | Formula (1.16) evaluates to zero, and its generators span $\mathcal H(\ker\mathcal L)$ and the full relation space. The proofs include a terminal second mark. [Proofs](Megaera/EditionOneCarry.lean) |
| Remark 1.11 | `FinalRemarkBPrimitives.remark_1_11` | Replacing $B^*$ by $B$ gives the same homogeneous span. |
| Theorem 1.12 | `EditionOneThree.theorem_1_12` | The coefficient of $X^w$ in the series below is the dimension of the relation space for each $w>0$. The proof passes through the successive quotient isomorphisms of the revised Theorem 3.3. [Proof](Megaera/EditionOneThree.lean) |
| Value-space dimension | `FinalValueSpace.value_rank_nullity` | The sum of the dimensions of the value space and the relation space is $\lvert\mathcal I_w\rvert$. `FinalValueSpace.value_generating_series` deduces the value-space series (1.18) from this equality. |

Every declaration above is in the namespace `Megaera`. For $r_w=\dim_{\mathbb F_q}R_w$, the dimension theorem gives

$$
\sum_{w\ge1} r_w X^w
=\frac{X^{2q+1}(1-X)^2}{(1-2X)(1-2X+X^{q+1})^2}.
$$

For $d_w=\dim_{\mathbb F_q}Z_w$, equation (1.18) becomes

$$
\sum_{w\ge1}d_wX^w=\frac{X(1-X^q)(1-2X+X^q)}{(1-2X+X^{q+1})^2}.
$$

Lean proves the identities coefficientwise after multiplication by the denominators. The dimension statements exhibit finite bases with unique coordinates. Theorem 1.12 constructs the ranks of the four spaces in §3. Rank–nullity of the CMPL evaluation gives the second formula. [Relation dimensions](Megaera/EditionOneThree.lean) · [Integer coefficients](Megaera/Dimension.lean) · [Value dimensions](Megaera/FinalValueSeries.lean)

## Mathematical inputs

The scalar hypotheses specify a field of cardinality $q$. The external number-theoretic input to the two completeness theorems and Theorem 1.12 is TT independence at positive weights. Its Lean statement says that for a finite relation among TT values with coefficients in $\mathbb F_q[\theta]$, each polynomial coefficient is zero. This is the polynomial-coefficient consequence of the manuscript's cited Theorem 1.2. This literature input is a theorem parameter. The software audit distinguishes such parameters from global logical axioms. [Chang–Chen–Mishiba, Theorem 1.5 and equation (2.7)](https://doi.org/10.1017/fmp.2023.26) · [Im–Kim–Le–Ngo Dac–Pham](https://doi.org/10.1017/fmp.2024.18)

Equation (2.3) is proved in this edition of the project. With $T=\theta^{-1}$, the coefficients of $1/\ell_d$ give the exact and truncated degree sums. Finite-field Frobenius and the Carlitz denominator recursion give the fundamental binary relation. The operators preserve that relation. Summation over levels, including the endpoint $d=-1$, proves the lifted row identity. The proof of the primitive binary relation and the soundness of all BCP generators uses the same concrete sums. [Finite-field proof](Megaera/FinalFiniteFrobenius.lean) · [Binary identities](Megaera/FinalBinaryProof.lean) · [Lifted row identity and completeness](Megaera/FinalBinaryRows.lean)

The manuscript transfers its CMPL conclusions to Thakur multiple zeta values by the separately cited Theorem 1.1. Given its weight-preserving $\mathbb F_q$-linear automorphism $T$ and $\zeta\circ T=\operatorname{Li}$, Lean proves that the kernel of the actual zeta evaluation is $T(\mathrm{BCP}_w)$. Transporting a relation basis gives dimension $r_w$. The two value spaces coincide inside the same space of series, so the zeta values also satisfy (1.18). The project assumes the transfer automorphism and derives all these consequences. [Thakur transfer](Megaera/EditionOneZeta.lean)

The project derives the quadruple-carry span and both CMPL dimension formulas independently of manuscript reference [7]. The star-value basis recalled from [7] in Theorem 1.9(ii) is outside the agreed scope.

## Proofs of the intermediate results

| Manuscript | Formal result |
| --- | --- |
| Lemma 2.1 and Theorem 2.2 | Both shifts preserve the homogeneous relation. The primitive and its BCP translates satisfy the degree-by-degree binary identity. [Shift proofs](Megaera/FinalBinaryShifts.lean) |
| Lemma 2.4 and Theorems 2.8–2.9 | Canonical rows separate the non-TT coordinates. Every homogeneous $\mathcal L$-row straightens to bounded-prefix rows. The square and terminal relations present the kernel. [Straightening](Megaera/FinalCanonical.lean) · [Kernel](Megaera/ScalarKernel.lean) · [Canonical rank](Megaera/FinalLRank.lean) |
| Lemma 2.6 and Theorem 2.7 | $\operatorname{Ind}$ preserves relations and is nilpotent on each weight. Backward closure gives the whole relation space. [Induction](Megaera/FinalInduction.lean) |
| Theorem 2.11 and Corollary 2.12 | The cut identity holds in both components. The generalized primitive span and the span of the $C$-translates agree at each weight. [Cut identity](Megaera/Convolution.lean) · [Graded span](Megaera/FinalOperatorSpan.lean) |
| Theorem 2.13 | $\mathrm{BCP}_w=\mathcal H(\ker\mathcal L)$, including both inclusions on homogeneous coordinates. [Proof](Megaera/FinalKernelL.lean) |
| Lemmas 2.15–2.18 | Singleton reflection gives the kernel elimination. The generators in Theorem 2.17 span precisely $\ker\mathcal H$ on marked-pair coordinates, before applying $\mathcal L$. The $\mathcal L$-readout is Lemma 2.18. [Reflection](Megaera/SingletonClosure.lean) · [Marked kernel](Megaera/FinalKernelH.lean) · [Readout](Megaera/Lambda.lean) |
| Lemma 3.1 and Corollary 3.2 | The actual lifts $B_h^*C_t(R_1)$ span $U_w$. Projection has image $\mathcal L_w$ and kernel $D_1R_w$. Lifting a basis of the image and adjoining a basis of the kernel gives the rank sum. [Rows and projection](Megaera/FinalDegreeOne.lean) · [Basis proof](Megaera/FinalBasisRanks.lean) |
| Theorem 3.3 | Restriction to tuples with first entry $n$ induces $V^{\rm Fix}_{w,n}/V^{\rm Fix}_{w,n+1}\simeq V_{w-n}$ for $V=R,U$. Lean constructs both inverse maps, identifies equality of classes, and proves linearity. Summing the dimensions gives the fixed-space rank identity. [Quotient isomorphisms and ranks](Megaera/EditionOneThree.lean) |
| Lemma 3.4 | The unprefixed lift induces a linear isomorphism $S_{w-q}/R^{\rm Fix}_{w-q}\simeq U_w/U^{\rm Fix}_w$. The proof identifies its image and kernel, counts each fiber, and includes the boundary $w=q$. The nonempty-prefix rows span $U_w^{\rm Fix}$. [Linear isomorphism](Megaera/FinalQuotientSpaces.lean) · [Quotient rank](Megaera/FinalQuotientRank.lean) · [Fixed span](Megaera/FinalFixedSpan.lean) |

## Reading the final manuscript alongside Lean

- **Primitive indices.** The primitive index $s$ in Theorem 1.10 is nonempty, as in Theorem 2.2. The prefix and the $C$-label may each be empty. For (1.16), a right label $v=r_2::t$ encodes $r_2>0$ and an empty right label encodes $(r_2,t)=(0,\emptyset)$.
- **Theorems 2.8–2.9.** Lean proves the signed normal form using $s_i=qk_i+r_i$, $1\leq r_i\leq q$. It vanishes for $r_\ell=q$. All three clauses of the recursive row map $f$ give $\mathcal L f(s)=s-\mathcal E(s)$, with $\mathcal E$ the signed normal form. In equation (2.4) on p. 12, splitting the earlier canonical entry moves the later mark from $i$ to $i+1$. The congruence is $-E_i(s)+E(s)\equiv E_{i+1}(s^{\rm cano})-\mathbf 1_{r_i>0}E(s^i)\pmod {Q_w}$. When the later entry is a terminal $q$, its split term is absent. The module proves both cases in the weight-$w$ quotient and proves that the two genuine splits commute at the shifted indices. [Normal form and congruences](Megaera/EditionOneSectionTwo.lean)
- **Theorem 2.17, p. 18.** In the elimination step with $s=(n)$ the term inside the prefix is $(n+1)+(n,1)$. The minus sign **outside** the prefixed $\Lambda(R_n)$ term is retained. This follows by substituting $(n)$ in the displayed statement on p. 17. [Marked kernel](Megaera/FinalKernelH.lean)
- **Theorem 3.3 and Lemma 3.4, pp. 19–20.** At $n=w$ the last graded piece is zero. The sum in Theorem 3.3 uses the zero space in weight zero and $V^{\rm Fix}_{w,w+1}=0$. For Lemma 3.4 the ambient coefficient space $\mathcal S_0$ still has basis $\{\emptyset\}$. In weights $w<q$ the spaces $U_w$ and $U_w^{\rm Fix}$ vanish, giving the remaining initial coefficients of (1.21). [Successive quotients](Megaera/EditionOneThree.lean) · [Boundary ranks](Megaera/FinalQuotientRank.lean)
- **Section 4.2, p. 22.** With $q^+\emptyset=(q)$, the tuple $(s_i,q^+t_i)$ has depth $\operatorname{dep}(s_i)+\max(1,\operatorname{dep}(t_i))$. The lower bound supplied by minimality applies to this expression, including when $t_i=\emptyset$. If the distinguished tail is empty, there is one shortest tail $(q-1)$ in $\mathcal H[s;\emptyset]$. [Depth comparison and terminal case](Megaera/FourCases.lean)
- **Section 4.3, pp. 24–25.** For $G=\operatorname{Ind}P$ the least surviving tuple strictly increases at each subtraction. In Case II, $S(G)$ keeps its nonzero initial value. A term at the selected depth therefore survives, and the lower bound on all surviving depths makes this the depth of the current minimum. [Reduction and pivot depth](Megaera/EditionOneFour.lean)

## Verification

Use Lean 4.19.0 in the directory containing `lakefile.toml`. The project uses the Lean standard library.

```text
lake build
lake env lean Audit.lean
```

The audit checks the transitive proof dependencies of the project's theorems. It rejects axioms outside Lean's three standard logical principles, including proof placeholders. It verifies that the §4 proof uses both cases and the current-minimum algorithm, that Theorem 1.12 uses the two quotient isomorphisms of Theorem 3.3, and that the MZV dimension proof transports a basis of the actual relation space. [Audit script](Audit.lean)
