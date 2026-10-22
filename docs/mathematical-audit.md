# Mathematical coverage audit: version_final.pdf

This is the mathematical inventory prepared before implementation. For the current
verified implementation status, see `coverage.md`.

Source: uploaded 21-page PDF, dated October 22, 2026. SHA-256:
`820a347ef0cb76519085fdca29d1eea73a8329b16a478e36c087119b64f5e68c`.

This is a mathematical and dependency audit, not a claim of Lean verification.
I found no counterexample to Theorem 1 or Lemmas 1–6. The core argument is coherent.

## Scope and exact claim inventory

The paper contains exactly one numbered theorem, six numbered lemmas, two remarks,
and numerous unnumbered analytic statements. Verifying only the seven numbered
results does not establish the user's requested coverage of every mathematical
argument.

| Claim | Location | Required content |
|---|---|---|
| Model and divergences | pp.1,3 | Euclidean Gaussian normalization; Borel probability prior; support in closed ball; mixture law equals the law of tTheta+Z; positive normalized mixture density; real-integral KL and chi-square agree with measure divergences; H² uses the unhalved convention |
| Theorem 1 | p.1, proof pp.4–5 | Symmetric KL ≤ (2M²+4)H² and max of both directed chi-square divergences ≤ (18 exp(4M²)-2)H², all dimensions and arbitrary compactly supported priors |
| Remark 1 | pp.1–2 | Well-defined optimal ratios; explicit Gaussian pair computations; lower bounds; supremum upper bounds; large-M asymptotics |
| Interpolation and posterior means | p.3, (2.1)–(2.4) | p₀=q₀=phi; p₁,q₁ endpoint laws; zero initial divergences; canonical Bayes posterior means; norm bounds M and difference bound 2M |
| Lemma 1 | p.3, Appendix A | All three curves finite, globally C¹ in t, and exact derivative identities (2.5), including t=0 |
| Hellinger monotonicity | pp.3–4 | D′≥0 for t≥0, hence D(t)≤D(1) for 0≤t≤1 |
| KL reduction | p.4, (2.6)–(2.8) | Root-density algebra, integration order, J′≤4M²tD+4D′, derivative of F_KL, monotonicity from derivative sign, endpoints |
| Chi-square reduction | pp.4–5, (2.9)–(2.13) | Nonnegative integrand factorization, integral equals C+2D, differential inequality, integrating factor, endpoints, reverse-direction symmetry |
| Section 3 | pp.5–6, (3.1)–(3.3) | Correct f-domain; generalized Fisher matrix and trace; spatial C²; PDE; a rigorously justified de Bruijn identity and its specialization |
| Score identities | p.8, (A.1) | Gradient of log density and log likelihood ratio, from explicit posterior numerator rather than an assumed version of conditional expectation |
| Lemma 2 | p.8, proof pp.14–17 | Gaussian integration by parts for any C¹ g with exponential growth of value and gradient; absolute integrability of both sides; no unproved boundary assumption |
| Derivative calculations | pp.8–10, (A.4)–(A.10) | Pointwise derivatives of log/product/quotient/sqrt; normalization derivative zero; Lemma 2 with log rho, rho, rho⁻¹, rho², rho±½; Bochner integral add/subtract/constant operations with integrability |
| Lemma 3 | pp.10–11, (A.11)–(A.14) | Explicit Gaussian-exponential-polynomial integral bounds, including 2^(k+d/2) k! exp((c+1)²) and sharper k=0 bound 2^(d/2)exp(c²) |
| Lemma 4 | pp.11–12, (A.15)–(A.17) | Parameter-dependent dominated differentiation on an open interval, common null set, joint measurability, derivative measurability, C¹ conclusion from continuity of integrated derivative |
| Lemma 5 | pp.12–14, (A.18)–(A.25) | Density upper/lower envelopes; t derivative formula; derivative relative bound; spatial derivative formula; joint C¹ regularity |
| Cutoff construction | p.16, (A.34)–(A.38) | Specific piecewise cubic cutoff, C¹ at both joins and the origin after composing with norm, compact support, 0≤chi≤1, gradient ≤3/(2R), boundary error tends zero |
| Likelihood ratio bounds | p.17, (A.39)–(A.40) | Two-sided exponential rho bound and absolute log-ratio bound |
| Lemma 6 | pp.17–18, (A.41)–(A.43) | Spatial derivative of rho^alpha for every real alpha; explicit uniform exponential-growth constants for powers and log |
| Divergence regularity | pp.18–21, (A.44)–(A.51) | Normalization derivative; all explicit dominating functions P and Q; each finite integral; C¹ of each directed KL, chi-square, affinity; D=2-2A and 0≤D≤2 |

## Dependency order

1. Euclidean/Gaussian model, finite-dimensional Lebesgue integration, compact support.
2. Lemma 3 and Lemma 4, independently.
3. Lemma 5 using Lemma 4, plus Gaussian kernel differentiation and support bounds.
4. Canonical posterior means, posterior norm bound, and score identities (A.1), using Lemma 5.
5. Lemma 2 using Lemmas 3 and 5, the explicit cutoff, dominated convergence, and Fubini.
6. Lemma 6 using Lemma 5, (A.1), and elementary real powers/logarithms.
7. Appendix A.3.6 using Lemmas 3–5 and the likelihood-ratio bounds.
8. Lemma 1 using items 5–7 and integral algebra.
9. Theorem 1 using Lemma 1, the posterior bound, polynomial identities, and one-variable calculus.
10. Remark 1 using Gaussian pair integrations, Theorem 1, convolution injectivity, supremum machinery, and limits.
11. Section 3 using spatial C² (stronger than Lemma 5's C¹), the PDE, and either a direct generalized identity with growth assumptions or a full formalization of the relevant specialization of the external theorem.

There is no need to introduce Brownian motion, stochastic integrals, Girsanov,
or Ito calculus to formalize this version of the paper.

## Necessary qualifications and corrections

### 1. Radius zero in Remark 1

Theorem 1 is valid for M=0: the sole prior is delta₀ and all divergences vanish.
But Remark 1's ratio sets have no distinct priors at M=0, and its lower-bound
expressions are 0/0. State Remark 1 and its two-sided numerical bounds for M>0.
One may separately define any desired convention for C_KL(0) and C_chi(0).

### 2. f-generator regularity at zero in Section 3

Section 3 calls f twice continuously differentiable on [0,infinity), then uses
f_K(r)=r log r-r+1 and f_H(r)=(sqrt r-1)². Both fail differentiability at zero.
The appropriate class here is C²((0,infinity)) with continuous extensions at zero,
because the mixture densities and their ratios are strictly positive. The generic
definition for arbitrary nonnegative p,q additionally needs conventions on q=0;
one can avoid that issue by stating the section for strictly positive densities.
For the conventional nonnegative f-divergence, normalize f(1)=0.

### 3. What the external de Bruijn identity establishes at t=0

Substituting score identities in (3.3) gives t D_f′(t)=t² E_f(t).
Cancellation establishes the derivative formula only at t≠0. To include zero,
use continuity of the derivative and a locally dominated energy integral, or the
direct derivative computation in Appendix A. Section 3 should mention this.
This does not affect the paper's direct proof of Lemma 1.

### 4. Side conditions for Section 3

The paper lists rather than proves the boundary and differentiation conditions.
They are true for the three specific generators under compact prior support, but
must be supplied to call the entire Section 3 proof formally complete.

The source Proposition 6 explicitly says second parameter derivative
integrability is unnecessary when L2=0. Since this paper sets L2=0, do not treat
second t derivatives as an unavoidable blocker. Spatial second derivatives are
still needed for the PDE; time first-derivative uniform integrable domination and
vanishing spatial boundary fluxes remain necessary.

Primary source checked: I. Valero Toranzo, S. Zozor, J.-M. Brossier,
https://arxiv.org/pdf/1611.09400, Proposition 6, printed p.16 (PDF page 16),
including its immediately following paragraph. Web reference: turn3view0 or
turn5view0; the parent must open the source itself before using a web citation.

### 5. Canonical posterior means and injectivity

Conditional expectations are only determined almost everywhere. For pointwise
identities at every x, define u_t(x) as the ratio of the vector kernel integral
to p_t(x), and separately prove it is a version of E[Theta|X(t)=x].

To define optimal ratios over pi≠eta, prove Gaussian convolution injectivity:
pi≠eta implies their mixture laws differ, hence H²>0. Characteristic functions
provide one route. This extra obligation is easy to miss because it is not a
numbered lemma. The explicit delta±M lower bound only needs its own H² positivity.

### 6. Minor notation/cross-reference issues

Appendix A.3.4 (A.29) and nearby text contain stale symbols f_t^G and E_G u_t,
and a reference to “inequality (3)” where (A.31) is intended. These should be
read as p_t and u_t. In A.3.6 “the derivative of H_0” should be J_0; on the last
page the integrability bounds are from Lemma 3, not Lemma 4. These are editorial,
not substantive counterexamples.

## Verification acceptance rules

- A theorem with derivative identities as hypotheses is a valid conditional
  reduction, but is not Theorem 1 for arbitrary supported prior measures.
- A structure whose fields are the paper's analytic conclusions is an interface,
  not a proof of those conclusions. Its concrete construction must be proved.
- A real-valued Bochner integral can evaluate to zero when its integrand is not
  integrable in Lean. Establish integrability explicitly before claiming it
  represents a finite divergence.
- Kernel audit must recursively inspect dependencies, not merely grep the top
  theorem for `sorry`. Exclude `sorryAx`, custom axioms, opaque assumed analytic
  facts, and untrusted evaluation-based proof shortcuts.
- A successful build plus no `sorry` does not show semantic correspondence.
  Record each paper statement, precise Lean declaration, hypotheses, and whether
  all paper-required assumptions are discharged.
- A replacement proof may establish a conclusion while leaving the paper's
  original mathematical argument unverified; track those separately because the
  user explicitly requested all arguments.

