module

public import SharpWasserstein.Compat
public import SharpWasserstein.GaussianSharpness

@[expose] public section

/-!
# Covariance characterization of the concrete Gaussian constructions

Finite Gaussian matrices are compared by characteristic functionals. This provides
an actual equality of measures from equality of covariance matrices.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators InnerProductSpace

namespace SharpWasserstein.GaussianSharpness

/-- A finite real matrix as a continuous linear map. -/
def matrixMap {m k : ℕ} (A : Fin k → Fin m → ℝ) :
    (Fin m → ℝ) →L[ℝ] (Fin k → ℝ) :=
  ContinuousLinearMap.pi fun i => ∑ j, A i j • ContinuousLinearMap.proj j

@[simp] theorem matrixMap_apply {m k : ℕ} (A : Fin k → Fin m → ℝ)
    (ω : Fin m → ℝ) (i : Fin k) : matrixMap A ω i = ∑ j, A i j * ω j := by
  simp [matrixMap]

def matrixLaw {m k : ℕ} (A : Fin k → Fin m → ℝ) : Measure (Fin k → ℝ) :=
  (standardLabels m).map (matrixMap A)

theorem matrixLaw_probability {m k : ℕ} (A : Fin k → Fin m → ℝ) :
    IsProbabilityMeasure (matrixLaw A) := by
  letI := standardLabels_probability m
  exact Measure.isProbabilityMeasure_map (matrixMap A).continuous.measurable.aemeasurable

theorem matrixLaw_isGaussian {m k : ℕ} (A : Fin k → Fin m → ℝ) :
    IsGaussian (matrixLaw A) := by
  letI := standardLabels_isGaussian m
  exact isGaussian_map (matrixMap A)

theorem matrix_quadraticForm {m k : ℕ} (A : Fin k → Fin m → ℝ) (w : Fin k → ℝ) :
    (∑ l, (∑ i, w i * A i l)^2) =
      ∑ i, ∑ j, (w i * w j) * (∑ l, A i l * A j l) := by
  calc
    (∑ l, (∑ i, w i * A i l)^2) =
        ∑ l, ∑ i, ∑ j, (w i * w j) * (A i l * A j l) := by
      apply Finset.sum_congr rfl
      intro l _
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ i, ∑ j, ∑ l, (w i * w j) * (A i l * A j l) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := by simp only [Finset.mul_sum]

/-- Equality of the actual covariance matrices gives equality of these Gaussian measures. -/
theorem matrixLaw_eq_of_covariance {m n k : ℕ}
    (A : Fin k → Fin m → ℝ) (B : Fin k → Fin n → ℝ)
    (hAB : ∀ i j, (∑ l, A i l * A j l) = ∑ l, B i l * B j l) :
    matrixLaw A = matrixLaw B := by
  letI := matrixLaw_probability A
  letI := matrixLaw_probability B
  apply Measure.ext_of_charFunDual
  funext L
  change charFunDual ((standardLabels m).map (matrixMap A)) L =
    charFunDual ((standardLabels n).map (matrixMap B)) L
  rw [charFunDual_map, charFunDual_map, charFunDual_standardLabels, charFunDual_standardLabels]
  congr 3
  simp only [ContinuousLinearMap.comp_apply]
  have heA (l : Fin m) : L (matrixMap A (Pi.single l 1)) =
      ∑ i, L (Pi.single i 1) * A i l := by
    rw [dual_eq_weightedSum]
    simp [Pi.single_apply]
  have heB (l : Fin n) : L (matrixMap B (Pi.single l 1)) =
      ∑ i, L (Pi.single i 1) * B i l := by
    rw [dual_eq_weightedSum]
    simp [Pi.single_apply]
  simp_rw [heA, heB, matrix_quadraticForm, hAB]

/-- Embed scalar particle coordinates into one-dimensional positions. -/
def scalarPositions (k : ℕ) : (Fin k → ℝ) →L[ℝ] Configuration 1 k :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun _ : Fin 1 =>
    ContinuousLinearMap.proj i

@[simp] theorem scalarPositions_apply (k : ℕ) (x : Fin k → ℝ) (i : Fin k) (j : Fin 1) :
    scalarPositions k x i j = x i := rfl

/-- The square root of the rank-one covariance matrix. -/
def stretchMatrix (k : ℕ) (a r : ℝ) (i j : Fin k) : ℝ :=
  (if i = j then Real.sqrt a else 0) +
    (Real.sqrt (a + r) - Real.sqrt a) / (k : ℝ)

theorem diagonal_constant_gram {k : ℕ} (α c : ℝ) (i j : Fin k) :
    (∑ l, ((if i = l then α else 0) + c) * ((if j = l then α else 0) + c)) =
      (if i = j then α^2 else 0) + 2*α*c + (k : ℝ)*c^2 := by
  simp only [add_mul, mul_add, Finset.sum_add_distrib]
  simp only [ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  by_cases hij : i = j <;> simp [hij] <;> ring

theorem stretchMatrix_gram {k : ℕ} (hk : 0 < k) {a r : ℝ} (ha : 0 ≤ a) (har : 0 ≤ a+r)
    (i j : Fin k) :
    (∑ l, stretchMatrix k a r i l * stretchMatrix k a r j l) =
      (if i = j then a else 0) + r / (k : ℝ) := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  simp only [stretchMatrix]
  rw [diagonal_constant_gram, Real.sq_sqrt ha]
  have hs := Real.sq_sqrt har
  have hs' := Real.sq_sqrt ha
  field_simp [hkR]
  nlinarith

/-- Additional standard Gaussian label 0 supplies the common noise. -/
def commonNoiseMatrix (k : ℕ) (a s : ℝ) (i : Fin k) (l : Fin (k+1)) : ℝ :=
  (if l = 0 then Real.sqrt s else 0) + (if l = i.succ then Real.sqrt a else 0)

theorem commonNoiseMatrix_gram (k : ℕ) {a s : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s)
    (i j : Fin k) :
    (∑ l, commonNoiseMatrix k a s i l * commonNoiseMatrix k a s j l) =
      (if i = j then a else 0) + s := by
  rw [Fin.sum_univ_succ]
  simp only [commonNoiseMatrix, if_true, Fin.succ_ne_zero, if_false, zero_add,
    Fin.succ_inj]
  simp only [mul_ite, ite_mul, zero_mul, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  by_cases hij : i = j <;> simp [hij, eq_comm, Real.mul_self_sqrt ha] <;>
    nlinarith [Real.sq_sqrt hs]

/-- Actual additive common-noise construction from k+1 independent standard Gaussian labels. -/
def commonNoiseLaw (k : ℕ) (a s : ℝ) : Measure (Configuration 1 k) :=
  (matrixLaw (commonNoiseMatrix k a s)).map (scalarPositions k)

theorem commonNoiseLaw_isGaussian (k : ℕ) (a s : ℝ) : IsGaussian (commonNoiseLaw k a s) := by
  letI := matrixLaw_isGaussian (commonNoiseMatrix k a s)
  exact isGaussian_map (scalarPositions k)

theorem stretchLabel_eq_matrix {k : ℕ} (hk : 0 < k) (a r : ℝ) :
    RankOneTransport.stretchLabel (Real.sqrt a) (Real.sqrt (a+r)) (commonDirection k)
      (standardVector k) = scalarPositions k ∘ matrixMap (stretchMatrix k a r) := by
  funext ω i j
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hs : Real.sqrt (k : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hkR).ne'
  have hsq := Real.sq_sqrt hkR.le
  change Real.sqrt a * ω i +
    ((Real.sqrt (a+r) - Real.sqrt a) *
      ⟪commonDirection k, standardVector k ω⟫_ℝ) * (Real.sqrt (k : ℝ))⁻¹ = _
  rw [commonMode_formula]
  simp only [Function.comp_apply, scalarPositions_apply, matrixMap_apply, stretchMatrix,
    add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, ← Finset.mul_sum]
  field_simp
  rw [hsq]
  ring

theorem correlatedLaw_eq_matrixLaw {k : ℕ} (hk : 0 < k) (a r : ℝ) :
    correlatedLaw k a r = (matrixLaw (stretchMatrix k a r)).map (scalarPositions k) := by
  unfold correlatedLaw matrixLaw
  rw [Measure.map_map (scalarPositions k).continuous.measurable (matrixMap _).continuous.measurable,
    stretchLabel_eq_matrix hk]

/-- The common-noise law is exactly the mode-stretch law used for the transport calculation. -/
theorem commonNoiseLaw_eq_correlated {k : ℕ} (hk : 0 < k) {a s : ℝ}
    (ha : 0 ≤ a) (hs : 0 ≤ s) :
    commonNoiseLaw k a s = correlatedLaw k a ((k : ℝ)*s) := by
  rw [correlatedLaw_eq_matrixLaw hk]
  unfold commonNoiseLaw
  congr 1
  apply matrixLaw_eq_of_covariance
  intro i j
  rw [commonNoiseMatrix_gram k ha hs, stretchMatrix_gram hk ha (by positivity)]
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  simp [hkR]

/-- Coordinate formula for the additive common-noise labels. -/
theorem commonNoiseMatrix_apply (k : ℕ) (a s : ℝ) (ω : Fin (k+1) → ℝ) (i : Fin k) :
    matrixMap (commonNoiseMatrix k a s) ω i =
      Real.sqrt a * ω i.succ + Real.sqrt s * ω 0 := by
  simp only [matrixMap_apply, commonNoiseMatrix, add_mul, Finset.sum_add_distrib,
    ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/-- No unspecified probability law is used in the correlated Gaussian example. -/
theorem commonNoiseLaw_explicit (k : ℕ) (a s : ℝ) :
    commonNoiseLaw k a s = (standardLabels (k+1)).map
      (fun ω i (_ : Fin 1) => Real.sqrt a * ω i.succ + Real.sqrt s * ω 0) := by
  unfold commonNoiseLaw matrixLaw
  rw [Measure.map_map (scalarPositions k).continuous.measurable (matrixMap _).continuous.measurable]
  congr 1
  funext ω i j
  exact commonNoiseMatrix_apply k a s ω i

theorem correlatedLaw_isGaussian {k : ℕ} (hk : 0 < k) (a r : ℝ) :
    IsGaussian (correlatedLaw k a r) := by
  rw [correlatedLaw_eq_matrixLaw hk]
  letI := matrixLaw_isGaussian (stretchMatrix k a r)
  exact isGaussian_map (scalarPositions k)

theorem marginal_matrixLaw {k N m : ℕ} (h : k ≤ N) (A : Fin N → Fin m → ℝ) :
    marginal h ((matrixLaw A).map (scalarPositions N)) =
      (matrixLaw (fun i l => A (Fin.castLE h i) l)).map (scalarPositions k) := by
  unfold marginal matrixLaw
  rw [Measure.map_map (measurable_restrictCoordinates h)
      (scalarPositions N).continuous.measurable,
    Measure.map_map ((measurable_restrictCoordinates h).comp (scalarPositions N).continuous.measurable) (matrixMap A).continuous.measurable,
    Measure.map_map (scalarPositions k).continuous.measurable (matrixMap _).continuous.measurable]
  congr 1

/-- All levels of the additive construction are marginals of a single particle law. -/
theorem marginal_commonNoiseLaw {k N : ℕ} (h : k ≤ N) {a s : ℝ}
    (ha : 0 ≤ a) (hs : 0 ≤ s) :
    marginal h (commonNoiseLaw N a s) = commonNoiseLaw k a s := by
  unfold commonNoiseLaw
  rw [marginal_matrixLaw]
  congr 1
  apply matrixLaw_eq_of_covariance
  intro i j
  rw [commonNoiseMatrix_gram N ha hs, commonNoiseMatrix_gram k ha hs]
  simp

/-- Permuting particle labels preserves the entire common-noise Gaussian law. -/
theorem commonNoiseLaw_exchangeable (k : ℕ) {a s : ℝ}
    (ha : 0 ≤ a) (hs : 0 ≤ s) : Exchangeable (commonNoiseLaw k a s) := by
  intro σ
  unfold commonNoiseLaw matrixLaw
  rw [Measure.map_map (by fun_prop) (scalarPositions k).continuous.measurable,
    Measure.map_map (by fun_prop) (matrixMap _).continuous.measurable]
  have he : ((fun x : Configuration 1 k => fun i => x (σ i)) ∘ scalarPositions k) ∘
      matrixMap (commonNoiseMatrix k a s) =
      scalarPositions k ∘ matrixMap (fun i l => commonNoiseMatrix k a s (σ i) l) := by
    funext ω i j
    rfl
  rw [he, ← Measure.map_map (scalarPositions k).continuous.measurable
    (matrixMap _).continuous.measurable]
  change (matrixLaw (fun i l => commonNoiseMatrix k a s (σ i) l)).map (scalarPositions k) = _
  congr 1
  apply matrixLaw_eq_of_covariance
  intro i j
  rw [commonNoiseMatrix_gram k ha hs, commonNoiseMatrix_gram k ha hs]
  simp

/-- The N-particle Gaussian law used in the manuscript at the variance parameter a. -/
def particleGaussianLaw (N : ℕ) (a : ℝ) : Measure (Configuration 1 N) :=
  commonNoiseLaw N a (1 / (N : ℝ))

theorem particleGaussianLaw_marginal {k N : ℕ} (hk : 0 < k) (hkN : k ≤ N)
    {a : ℝ} (ha : 0 ≤ a) :
    marginal hkN (particleGaussianLaw N a) = correlatedLaw k a ((k : ℝ) / N) := by
  unfold particleGaussianLaw
  rw [marginal_commonNoiseLaw hkN ha (by positivity),
    commonNoiseLaw_eq_correlated hk ha (by positivity)]
  simp only [mul_one_div]

/-- Exact unnormalized transport cost of the genuine k-marginal. -/
theorem particleGaussianLaw_transport_exact {k N : ℕ} (hk : 0 < k) (hkN : k ≤ N)
    (a : ℝ) (ha : 0 < a) :
    wassersteinSq (marginal hkN (particleGaussianLaw N a))
      (tensorLaw (oneParticleGaussian a) k) =
      ENNReal.ofReal (localRate k N /
        (Real.sqrt (a + (k : ℝ) / N) + Real.sqrt a)^2) := by
  rw [particleGaussianLaw_marginal hk hkN ha.le]
  exact gaussian_rankOne_transport_rationalized hk a ha

/-- One exchangeable N-particle initial law satisfies every required positive-level bound. -/
theorem particleGaussianLaw_initial_allLevels {N : ℕ} (hN : 0 < N) :
    Exchangeable (particleGaussianLaw N 1) ∧
      ∀ (k : ℕ) (_hk : 0 < k) (hkN : k ≤ N),
        wassersteinSq (marginal hkN (particleGaussianLaw N 1))
          (tensorLaw (oneParticleGaussian 1) k) ≤
          ENNReal.ofReal ((1 / 4 : ℝ) * localRate k N) := by
  refine ⟨commonNoiseLaw_exchangeable N (by norm_num) (by positivity), ?_⟩
  intro k hk hkN
  rw [particleGaussianLaw_marginal hk hkN (by norm_num)]
  exact gaussian_initial_bound hk hN

/-- The matching lower rate now applies to genuine marginals of one N-particle law. -/
theorem particleGaussianLaw_fixed_time_lower {k N : ℕ} (hk : 0 < k) (hkN : k ≤ N)
    (t : ℝ) (ht : 0 ≤ t) :
    ENNReal.ofReal (localRate k N /
      (Real.sqrt ((1 + 2*t) + 1) + Real.sqrt (1 + 2*t))^2) ≤
      wassersteinSq (marginal hkN (particleGaussianLaw N (1 + 2*t)))
        (tensorLaw (oneParticleGaussian (1 + 2*t)) k) := by
  rw [particleGaussianLaw_marginal hk hkN (by positivity)]
  exact gaussian_fixed_time_lower hk hkN t ht

/-- Gaussian configuration laws have the actual unnormalized Euclidean second moment. -/
theorem isGaussian_hasSecondMoment {d N : ℕ} (μ : Measure (Configuration d N))
    [IsGaussian μ] : HasSecondMoment μ := by
  have hc (i : Fin N) (j : Fin d) : MemLp (fun x : Configuration d N => x i j) 2 μ := by
    let L : Configuration d N →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) j).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Position d) i)
    exact IsGaussian.memLp_dual μ L 2 (by norm_num)
  have hi : Integrable (fun x : Configuration d N => productCost x 0) μ := by
    simp only [productCost, Pi.zero_apply, sub_zero]
    apply integrable_finsetSum
    intro i _
    apply integrable_finsetSum
    intro j _
    exact (hc i j).integrable_sq
  exact (lintegral_ofReal_ne_top_iff_integrable hi.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => productCost_nonneg x 0))).mpr hi |>.lt_top

theorem commonNoiseLaw_secondMoment (k : ℕ) (a s : ℝ) : HasSecondMoment (commonNoiseLaw k a s) := by
  letI := commonNoiseLaw_isGaussian k a s
  exact isGaussian_hasSecondMoment _

theorem particleGaussianLaw_probability (N : ℕ) (a : ℝ) :
    IsProbabilityMeasure (particleGaussianLaw N a) :=
  (commonNoiseLaw_isGaussian N a (1 / (N : ℝ))).toIsProbabilityMeasure

theorem particleGaussianLaw_secondMoment (N : ℕ) (a : ℝ) :
    HasSecondMoment (particleGaussianLaw N a) := commonNoiseLaw_secondMoment N a _

end SharpWasserstein.GaussianSharpness
