import SharpWasserstein.TransportMoments
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Tactic.FunProp

/-!
# The triangle inequality for the actual quadratic transport infimum

The transport cost is realized as an L² seminorm of Euclidean displacement.
The coupling argument below constructs a common triple law by disintegration;
no existence of a glued coupling or triangle inequality is assumed.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators ProbabilityTheory

namespace SharpWasserstein

/-- Coordinate displacement with the Euclidean, not the ambient Pi, norm. -/
def transportDisplacement {d N : ℕ} (z : Configuration d N × Configuration d N) :
    EuclideanSpace ℝ (Fin N × Fin d) :=
  WithLp.toLp 2 (fun i => z.1 i.1 i.2 - z.2 i.1 i.2)

theorem continuous_transportDisplacement {d N : ℕ} :
    Continuous (transportDisplacement (d := d) (N := N)) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin N × Fin d => ℝ)).comp
  fun_prop

theorem productCost_eq_displacement_norm_sq {d N : ℕ}
    (x y : Configuration d N) : productCost x y = ‖transportDisplacement (x, y)‖ ^ 2 := by
  simp [EuclideanSpace.real_norm_sq_eq, transportDisplacement, productCost, Fintype.sum_prod_type]

theorem transportDisplacement_add {d N : ℕ} (x y z : Configuration d N) :
    transportDisplacement (x, z) = transportDisplacement (x, y) + transportDisplacement (y, z) := by
  ext i
  change x i.1 i.2 - z i.1 i.2 = (x i.1 i.2 - y i.1 i.2) + (y i.1 i.2 - z i.1 i.2)
  ring

/-- The square root of the genuine coupling cost is its Euclidean L² displacement seminorm. -/
theorem transportCost_root_eq_eLpNorm {d N : ℕ}
    (γ : Measure (Configuration d N × Configuration d N)) :
    transportCost γ ^ (1 / 2 : ℝ) = eLpNorm transportDisplacement 2 γ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
  norm_num only [ENNReal.toReal_ofNat]
  congr 1
  apply lintegral_congr
  intro z
  rw [ENNReal.rpow_two, productCost_eq_displacement_norm_sq,
    ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem transportCost_map_root_eq_eLpNorm {Ω : Type*} [MeasurableSpace Ω]
    {d N : ℕ} (P : Measure Ω) (f g : Ω → Configuration d N)
    (hf : Measurable f) (hg : Measurable g) :
    transportCost (Measure.map (fun ω => (f ω, g ω)) P) ^ (1 / 2 : ℝ) =
      eLpNorm (fun ω => transportDisplacement (f ω, g ω)) 2 P := by
  rw [transportCost_root_eq_eLpNorm,
    eLpNorm_map_measure continuous_transportDisplacement.stronglyMeasurable.aestronglyMeasurable
      (hf.prodMk hg).aemeasurable]
  rfl

/-- Minkowski on a common triple law bounds the cost of its endpoint marginal. -/
theorem transportCost_triple_triangle {d N : ℕ}
    (P : Measure ((Configuration d N × Configuration d N) × Configuration d N)) :
    transportCost (Measure.map (fun z => (z.1.1, z.2)) P) ^ (1 / 2 : ℝ) ≤
      transportCost (Measure.map Prod.fst P) ^ (1 / 2 : ℝ) +
      transportCost (Measure.map (fun z => (z.1.2, z.2)) P) ^ (1 / 2 : ℝ) := by
  let f := fun z : (Configuration d N × Configuration d N) × Configuration d N =>
    transportDisplacement (z.1.1, z.1.2)
  let g := fun z : (Configuration d N × Configuration d N) × Configuration d N =>
    transportDisplacement (z.1.2, z.2)
  have hf : AEStronglyMeasurable f P :=
    (continuous_transportDisplacement.comp continuous_fst).stronglyMeasurable.aestronglyMeasurable
  have hg : AEStronglyMeasurable g P := (continuous_transportDisplacement.comp
    ((continuous_snd.comp continuous_fst).prodMk continuous_snd)).stronglyMeasurable.aestronglyMeasurable
  have hsum : (fun z : (Configuration d N × Configuration d N) × Configuration d N =>
      transportDisplacement (z.1.1, z.2)) = f + g := by
    funext z
    exact transportDisplacement_add z.1.1 z.1.2 z.2
  rw [transportCost_map_root_eq_eLpNorm P (fun z => z.1.1) (fun z => z.2) (by fun_prop) (by fun_prop),
    transportCost_map_root_eq_eLpNorm P (fun z => z.1.2) (fun z => z.2) (by fun_prop) (by fun_prop)]
  have hfst : transportCost (Measure.map Prod.fst P) ^ (1 / 2 : ℝ) = eLpNorm f 2 P := by
    rw [transportCost_root_eq_eLpNorm,
      eLpNorm_map_measure continuous_transportDisplacement.stronglyMeasurable.aestronglyMeasurable
        measurable_fst.aemeasurable]
    rfl
  rw [hfst, hsum]
  exact eLpNorm_add_le hf hg (by norm_num)

/-- Positive powers preserve infima in the extended nonnegative reals. -/
theorem ennreal_rpow_iInf {ι : Sort*} (f : ι → ℝ≥0∞) {p : ℝ} (hp : 0 < p) :
    (⨅ i, f i) ^ p = ⨅ i, (f i) ^ p :=
  (ENNReal.orderIsoRpow p hp).map_iInf f

/-- The last two coordinates of a composition-product depend only on its middle marginal. -/
theorem map_compProd_prodMkLeft {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (γ : Measure (X × Y)) [SFinite γ] (K : Kernel Y Z) [IsSFiniteKernel K] :
    Measure.map (fun z : (X × Y) × Z => (z.1.2, z.2)) (γ ⊗ₘ Kernel.prodMkLeft X K) =
      γ.snd ⊗ₘ K := by
  ext s hs
  have hp : Measurable (fun z : (X × Y) × Z => (z.1.2, z.2)) := by fun_prop
  rw [Measure.map_apply hp hs, Measure.compProd_apply (hp hs), Measure.compProd_apply hs]
  rw [Measure.snd, lintegral_map (Kernel.measurable_kernel_prodMk_left hs) measurable_snd]
  rfl

/-- Endpoint projection of a genuine triple law is a coupling of its outer marginals. -/
theorem triple_endpoint_isCoupling {X : Type*} [MeasurableSpace X]
    {μ ν ρ : Measure X} {γ₁ γ₂ : Measure (X × X)}
    (h₁ : IsCoupling μ ν γ₁) (h₂ : IsCoupling ν ρ γ₂)
    (G : Measure ((X × X) × X)) [IsProbabilityMeasure G]
    (hG₁ : Measure.map Prod.fst G = γ₁)
    (hG₂ : Measure.map (fun z => (z.1.2, z.2)) G = γ₂) :
    IsCoupling μ ρ (Measure.map (fun z => (z.1.1, z.2)) G) := by
  have h13 : Measurable (fun z : (X × X) × X => (z.1.1, z.2)) := by fun_prop
  have h23 : Measurable (fun z : (X × X) × X => (z.1.2, z.2)) := by fun_prop
  refine ⟨Measure.isProbabilityMeasure_map h13.aemeasurable, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst h13]
    change Measure.map (Prod.fst ∘ Prod.fst) G = μ
    rw [← Measure.map_map measurable_fst measurable_fst, hG₁, h₁.2.1]
  · rw [Measure.map_map measurable_snd h13]
    change Measure.map (Prod.snd ∘ (fun z : (X × X) × X => (z.1.2, z.2))) G = ρ
    rw [← Measure.map_map measurable_snd h23, hG₂, h₂.2.2]

/-- Actual coupling gluing, constructed from the conditional kernel of the second coupling. -/
theorem coupling_gluing {X : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    {μ ν ρ : Measure X} {γ₁ γ₂ : Measure (X × X)}
    (h₁ : IsCoupling μ ν γ₁) (h₂ : IsCoupling ν ρ γ₂) :
    ∃ G : Measure ((X × X) × X), IsProbabilityMeasure G ∧
      Measure.map Prod.fst G = γ₁ ∧
      Measure.map (fun z => (z.1.2, z.2)) G = γ₂ := by
  letI : IsProbabilityMeasure γ₁ := h₁.1
  letI : IsProbabilityMeasure γ₂ := h₂.1
  let G := γ₁ ⊗ₘ Kernel.prodMkLeft X γ₂.condKernel
  refine ⟨G, inferInstance, ?_, ?_⟩
  · exact Measure.fst_compProd γ₁ (Kernel.prodMkLeft X γ₂.condKernel)
  · change Measure.map (fun z : (X × X) × X => (z.1.2, z.2))
      (γ₁ ⊗ₘ Kernel.prodMkLeft X γ₂.condKernel) = γ₂
    rw [map_compProd_prodMkLeft]
    have hmiddle : γ₁.snd = γ₂.fst := h₁.2.2.trans h₂.2.1.symm
    rw [hmiddle]
    exact γ₂.disintegrate γ₂.condKernel

theorem wassersteinSq_root_eq_iInf {d N : ℕ}
    (μ ν : Measure (Configuration d N)) :
    wassersteinSq μ ν ^ (1 / 2 : ℝ) =
      ⨅ (γ : Measure (Configuration d N × Configuration d N)) (_ : IsCoupling μ ν γ),
        transportCost γ ^ (1 / 2 : ℝ) := by
  unfold wassersteinSq
  rw [ennreal_rpow_iInf _ (by norm_num : (0 : ℝ) < 1 / 2)]
  congr 1
  funext γ
  exact ennreal_rpow_iInf _ (by norm_num : (0 : ℝ) < 1 / 2)

/-- The square-root triangle inequality for the genuine transport infimum,
including infinite values. Neither gluing nor a transport triangle is a hypothesis. -/
theorem wassersteinSq_root_triangle {d N : ℕ}
    (μ ν ρ : Measure (Configuration d N)) :
    wassersteinSq μ ρ ^ (1 / 2 : ℝ) ≤
      wassersteinSq μ ν ^ (1 / 2 : ℝ) + wassersteinSq ν ρ ^ (1 / 2 : ℝ) := by
  rw [wassersteinSq_root_eq_iInf μ ν, wassersteinSq_root_eq_iInf ν ρ]
  apply ENNReal.le_iInf₂_add_iInf₂
  intro γ₁ h₁ γ₂ h₂
  obtain ⟨G, hGprob, hG₁, hG₂⟩ := coupling_gluing h₁ h₂
  letI : IsProbabilityMeasure G := hGprob
  have houter := triple_endpoint_isCoupling h₁ h₂ G hG₁ hG₂
  have hcost := ENNReal.rpow_le_rpow (wassersteinSq_le_cost houter)
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  exact hcost.trans (by simpa only [hG₁, hG₂] using transportCost_triple_triangle G)

/-- The ordinary real square-root triangle inequality on probability laws with second moments. -/
theorem wassersteinSq_sqrt_triangle {d N : ℕ}
    (μ ν ρ : Measure (Configuration d N))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (hμ : HasSecondMoment μ) (hν : HasSecondMoment ν) (hρ : HasSecondMoment ρ) :
    Real.sqrt (wassersteinSq μ ρ).toReal ≤
      Real.sqrt (wassersteinSq μ ν).toReal + Real.sqrt (wassersteinSq ν ρ).toReal := by
  have h₁ : wassersteinSq μ ν ≠ ∞ := (wassersteinSq_lt_top μ ν hμ hν).ne
  have h₂ : wassersteinSq ν ρ ≠ ∞ := (wassersteinSq_lt_top ν ρ hν hρ).ne
  have hp₁ : wassersteinSq μ ν ^ (1 / 2 : ℝ) ≠ ∞ := by
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) h₁
  have hp₂ : wassersteinSq ν ρ ^ (1 / 2 : ℝ) ≠ ∞ := by
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) h₂
  have ht := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hp₁, hp₂⟩)
    (wassersteinSq_root_triangle μ ν ρ)
  rw [ENNReal.toReal_add hp₁ hp₂] at ht
  simpa only [← ENNReal.toReal_rpow, ← Real.sqrt_eq_rpow] using ht

/-- A probability law with a finite, unnormalized Euclidean second moment. -/
structure QuadraticProbabilityLaw (d N : ℕ) where
  measure : Measure (Configuration d N)
  probability : IsProbabilityMeasure measure
  secondMoment : HasSecondMoment measure

/-- The actual transport infimum defines a pseudometric on P₂ probability laws.
Separation of laws is not needed for the endpoint assembly. -/
@[reducible] def quadraticProbabilityPseudoMetricSpace (d N : ℕ) :
    PseudoMetricSpace (QuadraticProbabilityLaw d N) where
  dist μ ν := Real.sqrt (wassersteinSq μ.measure ν.measure).toReal
  dist_self μ := by
    letI : IsProbabilityMeasure μ.measure := μ.probability
    simp
  dist_comm μ ν := by rw [wassersteinSq_symm]
  dist_triangle μ ν ρ := by
    letI : IsProbabilityMeasure μ.measure := μ.probability
    letI : IsProbabilityMeasure ν.measure := ν.probability
    letI : IsProbabilityMeasure ρ.measure := ρ.probability
    exact wassersteinSq_sqrt_triangle μ.measure ν.measure ρ.measure
      μ.secondMoment ν.secondMoment ρ.secondMoment

attribute [instance] quadraticProbabilityPseudoMetricSpace

theorem quadraticProbability_dist_eq {d N : ℕ} (μ ν : QuadraticProbabilityLaw d N) :
    dist μ ν = Real.sqrt (wassersteinSq μ.measure ν.measure).toReal := rfl

theorem quadraticProbability_dist_sq {d N : ℕ} (μ ν : QuadraticProbabilityLaw d N) :
    dist μ ν ^ 2 = (wassersteinSq μ.measure ν.measure).toReal := by
  rw [quadraticProbability_dist_eq, Real.sq_sqrt ENNReal.toReal_nonneg]

/-- No infinite cost is lost by taking `toReal` on P₂ probability laws. -/
theorem quadraticProbability_ofReal_dist_sq {d N : ℕ}
    (μ ν : QuadraticProbabilityLaw d N) :
    ENNReal.ofReal (dist μ ν ^ 2) = wassersteinSq μ.measure ν.measure := by
  letI : IsProbabilityMeasure μ.measure := μ.probability
  letI : IsProbabilityMeasure ν.measure := ν.probability
  rw [quadraticProbability_dist_sq]
  exact ENNReal.ofReal_toReal (wassersteinSq_lt_top μ.measure ν.measure
    μ.secondMoment ν.secondMoment).ne

end SharpWasserstein
