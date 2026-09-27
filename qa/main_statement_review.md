# Final main-statement and citation review

Reviewed 2026-09-18T02:01:22.171056+00:00. **Pass: the revised manuscript main theorem matches the original formal target; the weak-solution wording precision is resolved.** This is a statement/citation review. The separate aggregate build owns full dependency replay.

## Unchanged target and actual proof

- `SharpWasserstein/Dynamics.lean:103` still defines the original `MainTheorem`. Its complete source SHA-256 is `fd209dcbcde483eb1b7336cee62d1f9e9741d7299033240591d6637b34f545b8`, exactly equal to both the archived `qa/history/verification_before_main_completion_2026-09-17.json` entry (timestamp `2026-09-17T03:39:16.189207+00:00`) and `qa/history/verification_checkpoint_before_main_completion_2026-09-17.json` entry (timestamp `2026-09-18T01:40:40.394088+00:00`). No target hypothesis or conclusion was changed. Historical “open target” comments and checkpoint status describe the previous state, not the new proof.
- `SharpWasserstein/Main.lean:13` declares `main_theorem : MainTheorem` and applies `main_of_uniform_finite_action_transport` to the proved `RoughEulerianTransport.uniform_finite_action_transport`. It adds no transport, entropy, source regularity, product-initial-data, or common-label hypothesis to the original target. The intermediate common-label data are constructed for the actual switch curve.
- Manuscript `thm:main` starts at line 199. It states the same finite-horizon, all-level estimate for the unnormalized quadratic product cost.

## Mathematical scope checks

| Item | Exact evidence and conclusion |
|---|---|
| Quantifiers and constant | `Dynamics.MainTheorem` chooses `C ≥ 0` after `d,C₀,T,M,L₁,L₂` and before `b,μ,P`. `MainFiniteActionReduction.lean:18` supplies the explicit `WassersteinEndpoint.coefficient d M L₁ L₂ C₀ T`; its definition uses only these parameters. There is no dependence on N, k, the particular initial laws, their moments, or higher derivative bounds. |
| Kernel regularity | `BoundedSmoothKernel` is actual C∞ regularity plus a separate finite uniform bound at each derivative order, precisely the stated C_b∞ convention. `KernelBounds` controls value and the two first derivatives. Higher derivatives are needed for the proof, but do not occur among final constant parameters. |
| Norm convention | `Transport.productCost` is literally `∑ i ∑ a (x i a−y i a)^2`, despite the ambient finite-function sup norm. The manuscript uses the same unnormalized Euclidean cost. `EuclideanDrift.particleDrift_quadratic_difference` proves the full-cost bound with coefficient `2*d*(L₁²+L₂²)`, independent of N; `EuclideanFlow.euclidean_particleDrift_lipschitz` takes its square root. If the manuscript derivative bounds are Euclidean operator bounds, the sup-operator bounds may be chosen as √d times those bounds, by ‖v‖∞≤‖v‖₂≤√d‖v‖∞. This changes only the allowed d dependence, never the particle scaling. |
| Self interaction and noise | `Dynamics.particleDrift` sums every `j : Fin N`, including j=i, with 1/N. `Dynamics.generator` is Δ plus drift, with no factor 1/2. `BrownianNoise.scalarPath` multiplies actual Brownian motion by √2 and `scalarPath_hasLaw` gives variance 2t. `BrownianParticleWeak.globalLaw_weakEvolution` proves this exact generator for the actual constructed law. |
| Initial laws and references | `IsParticleEvolution` requires only the genuine weak evolution and exchangeability of P(0); it does not impose independence, absolute continuity, or entropy. The `WeakEvolution` fields include probability, finite second moments, local uniform moment bounds, continuous test pairings and the actual integrated equation. `ParticleWeakIdentification.eq_globalLaw_of_weakEvolution` identifies arbitrary supplied particle weak laws with the constructed Brownian laws. `ReferenceTensorIdentification` handles the prescribed reference/tensor identification. Correlated and singular P₂ initial laws remain allowed. |
| Time and marginal scope | `InitialHierarchy` quantifies over every N≥1 and 1≤k≤N; `PropagatedHierarchy` uses the same single constant for all those levels and every t∈[0,T]. This is exactly the displayed supremum bound, includes t=0 and k=N, and makes no uniform-in-T claim. d≥1 and finite positive T agree. |
| Weak-solution wording | Manuscript line 182 now explicitly says “narrowly continuous weak probability solution” with “locally bounded second moments.” This resolves the earlier ambiguity about isolated-time representatives and matches the original formal weak class. Under bounded drift, compact tests have bounded generator, supplying the ordinary integrability conditions in that convention. |

The entropy-cost proof also retains the corrected direction: controlled history relative to the uncontrolled comparison history, expectation under the first law, coefficient h/4 for Gaussian covariance 2hI, and endpoint comparison Q(x) relative to Q(y). The final coupling argument uses arbitrary couplings followed by the infimum, as in the formal route.

## All revised citation sites

All 12 bibliography entries and all 12 citation sites were compared with the existing authoritative-source report at `/Users/tudou/Desktop/research/rethlas/manuscripts/sharp_wasserstein_bounded_kernel_open/qa/reference_audit.md`. Every cited key resolves; every bibliography key is used; metadata retain the verified titles, authors, years, volumes, pages and DOI values.

| Citation keys | Revised claim reviewed |
|---|---|
| Kac; McKean; Sznitman; Chaintron–Diez | Historical origins, systematic treatment and survey only. |
| Dobrushin; Malrieu | Transport stability for regular interactions and a specifically qualified granular-media diffusion example; no general theorem is attributed to the latter. |
| Jabin–Wang | Full-law entropy methods for low-regularity kernels; no attribution of the new local tangent hierarchy. |
| Lacker | Theorem 2.2 and Corollary 2.6, with initial entropy hierarchy and interaction-adapted transport inequality explicitly retained; bounded interactions handled through Pinsker. The text claims the sharp order, not an exact remainder-free finite-N formula or resolution of the broader path-space question. |
| Lacker–Le Flem | Theorem 2.1(1) and Remark 2.3, with uniform LSI and sufficiently favorable noise/interaction regime explicitly retained. Pinsker/transport conversion is correctly qualified. |
| Benamou–Brenier; AGS (two sites) | Background dynamic transport principle. The revised finite-action lemma now proves its own precise common-label version, so it no longer substitutes an unverified use of AGS Theorem 8.3.1 for missing measurability or endpoint hypotheses. |
| Sznitman at nonlinear well-posedness | Explicitly **standard background**. `MainTheorem` is an estimate for supplied evolutions; `main_theorem` must not be advertised as a separate proof of nonlinear existence. The text correctly separates that background from the proved identification with prescribed linear Brownian evolutions. |
| Hoeffding | Applied conditionally on X_i to independent centered bounded j≠i summands, componentwise in fixed d; the bounded self term is retained. No tail or moment assumption on the reference distribution is inferred. |

The bounded-class sharpness claim uses the manuscript's own b=0 correlated Gaussian example, rather than borrowing an unbounded-kernel optimality example from a cited paper. No citation defect or unsupported stronger attributed result remains.

## Reproducibility identifiers

- Revised manuscript SHA-256: `b9b05c4498b9e4d70c7366e2f9b6d3188adf56b45ad3dbf45581438376314330`.
- New `Main.lean` SHA-256: `cdb058def9a42f32737c9c637ef91a5eff239867f5fa56b7c5788d8e4160ce7f`.
- Prior reference-audit SHA-256: `f35577cbf23511ff4a25c4a538dc410ca44513c6a0b19c0961aa33875ad058e4`.
- Earlier checkpoint manifest SHA-256 at review: `d0e6a6b6b50ec06a334000030de1dd103fa9260df5a6d36f2be023faa5265beb`.
- Citation-site lines at review: 69, 71, 71, 74, 76, 80, 81, 90, 152, 186, 342, 563.

No Lean source was edited for this review.
