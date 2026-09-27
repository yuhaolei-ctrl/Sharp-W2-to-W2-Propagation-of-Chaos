import SharpWasserstein.EntropyChainRule
import SharpWasserstein.EntropyDataProcessing
import SharpWasserstein.EntropyHierarchy
import SharpWasserstein.Transport
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.Composition.Lemmas

/-!
# Entropy increments of exchangeable laws

The probabilistic foundation is the superadditivity of actual relative entropy
against a product reference. It follows from the proved data-processing
inequality and Mathlib's disintegration and joint-law chain rule.
-/

noncomputable section

open MeasureTheory InformationTheory ProbabilityTheory
open scoped ENNReal

namespace SharpWasserstein

instance tensorLaw_isProbabilityMeasure {d n : ℕ} (r : Measure (Position d))
    [IsProbabilityMeasure r] : IsProbabilityMeasure (tensorLaw r n) := by
  unfold tensorLaw
  infer_instance

instance marginal_isProbabilityMeasure {d k N : ℕ} (hk : k ≤ N)
    (P : Measure (Configuration d N)) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (marginal hk P) :=
  Measure.isProbabilityMeasure_map (measurable_restrictCoordinates hk).aemeasurable

/-- Actual KL is invariant under a measurable equivalence. -/
theorem klDiv_map_measurableEquiv
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ ν : Measure A} [IsFiniteMeasure μ] [IsFiniteMeasure ν] (e : A ≃ᵐ B) :
    klDiv (μ.map e) (ν.map e) = klDiv μ ν := by
  apply le_antisymm (klDiv_map_le e.measurable)
  have h := klDiv_map_le (μ := μ.map e) (ν := ν.map e) e.symm.measurable
  simpa only [Measure.map_map e.symm.measurable e.measurable,
    e.symm_comp_self, Measure.map_id] using h

/-- Relative entropy against a product reference dominates the sum of the
two marginal relative entropies. This is the conditional-mutual-information
nonnegativity argument needed for monotone entropy increments. -/
theorem klDiv_marginals_add_le_product
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [StandardBorelSpace B] [Nonempty B]
    {P : Measure (A × B)} {μ : Measure A} {ν : Measure B}
    [IsProbabilityMeasure P] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    klDiv P.fst μ + klDiv P.snd ν ≤ klDiv P (μ.prod ν) := by
  have hchain := klDiv_compProd_eq_add (μ := P.fst) (ν := μ)
    (κ := P.condKernel) (η := Kernel.const A ν)
  rw [P.disintegrate P.condKernel, Measure.compProd_const,
    Measure.compProd_const] at hchain
  have hs : klDiv P.snd ν ≤ klDiv P (P.fst.prod ν) := by
    have h := klDiv_map_le (μ := P) (ν := P.fst.prod ν) measurable_snd
    simpa only [Measure.snd, Measure.map_snd_prod, measure_univ, one_smul] using h
  rw [hchain]
  exact add_le_add le_rfl hs

/-- Real-valued product superadditivity, with finiteness justified before
converting from the extended-real inequality. -/
theorem toReal_klDiv_marginals_add_le_product
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [StandardBorelSpace B] [Nonempty B]
    {P : Measure (A × B)} {μ : Measure A} {ν : Measure B}
    [IsProbabilityMeasure P] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hfinite : klDiv P (μ.prod ν) ≠ ∞) :
    (klDiv P.fst μ).toReal + (klDiv P.snd ν).toReal ≤ (klDiv P (μ.prod ν)).toReal := by
  have h := klDiv_marginals_add_le_product (P := P) (μ := μ) (ν := ν)
  have hn := ENNReal.add_ne_top.mp (ne_top_of_le_ne_top hfinite h)
  have hr := ENNReal.toReal_mono hfinite h
  rwa [ENNReal.toReal_add hn.1 hn.2] at hr

/-- Data processing when only the second coordinate of a joint kernel law
is observed. -/
theorem klDiv_compProd_map_le
    {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    {μ ν : Measure A} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {κ η : Kernel A B} [IsFiniteKernel κ] [IsFiniteKernel η]
    {f : B → C} (hf : Measurable f) :
    klDiv (μ ⊗ₘ κ.map f) (ν ⊗ₘ η.map f) ≤ klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) := by
  rw [Measure.compProd_map hf, Measure.compProd_map hf]
  exact klDiv_map_le (measurable_id.prodMap hf)

/-- Adjacent entropy convexity from equality of the two conditional marginals.
This equality is a symmetry of genuine conditional laws, not an entropy
monotonicity assumption. -/
theorem entropy_second_difference_nonneg_of_equal_kernel_marginals
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [StandardBorelSpace B] [Nonempty B]
    {μ ν : Measure A} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {r : Measure B} [IsProbabilityMeasure r]
    {κ : Kernel A (B × B)} [IsMarkovKernel κ]
    (hsym : κ.fst =ᵐ[μ] κ.snd)
    (hfinite : klDiv (μ ⊗ₘ κ) (ν ⊗ₘ Kernel.const A (r.prod r)) ≠ ∞) :
    0 ≤ (klDiv (μ ⊗ₘ κ) (ν ⊗ₘ Kernel.const A (r.prod r))).toReal
      - 2 * (klDiv (μ ⊗ₘ κ.fst) (ν ⊗ₘ Kernel.const A r)).toReal
      + (klDiv μ ν).toReal := by
  have href : (Kernel.const A (r.prod r)).fst = Kernel.const A r := by
    ext a : 1
    simp only [Kernel.fst_apply, Kernel.const_apply, Measure.map_fst_prod,
      measure_univ, one_smul]
  have hle := klDiv_compProd_map_le (μ := μ) (ν := ν) (κ := κ)
    (η := Kernel.const A (r.prod r)) measurable_fst
  rw [← Kernel.fst_eq, ← Kernel.fst_eq, href] at hle
  have hmidfinite := ne_top_of_le_ne_top hfinite hle
  have hpaircond := conditional_joint_klDiv_ne_top hfinite
  have hmidcond := conditional_joint_klDiv_ne_top hmidfinite
  have hpairint := integrable_kernel_klDiv_toReal hpaircond
  have hmidint := integrable_kernel_klDiv_toReal hmidcond
  simp only [Kernel.const_apply] at hpairint hmidint
  have hpoint : ∀ᵐ a ∂μ, 2 * (klDiv (κ.fst a) r).toReal
      ≤ (klDiv (κ a) (r.prod r)).toReal := by
    filter_upwards [ae_kernel_klDiv_ne_top hpaircond, hsym] with a ha hs
    simp only [Kernel.const_apply] at ha
    have h := toReal_klDiv_marginals_add_le_product (P := κ a) (μ := r) (ν := r) ha
    change (klDiv (κ.fst a) r).toReal + (klDiv (κ.snd a) r).toReal ≤ _ at h
    rw [← hs] at h
    linarith
  have h := integral_mono_ae (hmidint.const_mul 2) hpairint hpoint
  rw [integral_const_mul] at h
  have hpairEq := integral_kernel_klDiv_eq_entropy_increment hfinite
  have hmidEq := integral_kernel_klDiv_eq_entropy_increment hmidfinite
  simp only [Kernel.const_apply] at hpairEq hmidEq
  rw [hpairEq, hmidEq] at h
  linarith

/-- Swapping the last two coordinates of an actual joint law gives equality
of its two one-coordinate marginals over the common prefix. -/
theorem equal_pair_marginals_of_swap
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {P : Measure (A × (B × B))}
    (hsym : P.map (Prod.map id Prod.swap) = P) :
    P.map (Prod.map id Prod.fst) = P.map (Prod.map id Prod.snd) := by
  calc
    P.map (Prod.map id Prod.fst)
        = (P.map (Prod.map id Prod.swap)).map (Prod.map id Prod.fst) := by rw [hsym]
    _ = P.map (Prod.map id Prod.snd) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl

/-- The entropy second difference for a law invariant under swapping its last
two coordinates. All three entropies are KL divergences of actual marginals. -/
theorem entropy_second_difference_nonneg_of_pair_swap
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [StandardBorelSpace B] [Nonempty B]
    {P : Measure (A × (B × B))} [IsProbabilityMeasure P]
    {ν : Measure A} [IsFiniteMeasure ν] {r : Measure B} [IsProbabilityMeasure r]
    (hsym : P.map (Prod.map id Prod.swap) = P)
    (hfinite : klDiv P (ν.prod (r.prod r)) ≠ ∞) :
    0 ≤ (klDiv P (ν.prod (r.prod r))).toReal
      - 2 * (klDiv (P.map (Prod.map id Prod.fst)) (ν.prod r)).toReal
      + (klDiv P.fst ν).toReal := by
  have hfst : P.fst ⊗ₘ P.condKernel.fst = P.map (Prod.map id Prod.fst) := by
    rw [Kernel.fst_eq, Measure.compProd_map measurable_fst, P.disintegrate P.condKernel]
  have hsnd : P.fst ⊗ₘ P.condKernel.snd = P.map (Prod.map id Prod.snd) := by
    rw [Kernel.snd_eq, Measure.compProd_map measurable_snd, P.disintegrate P.condKernel]
  have hker : P.condKernel.fst =ᵐ[P.fst] P.condKernel.snd := by
    apply Kernel.compProd_eq_iff.mp
    rw [hfst, hsnd]
    exact equal_pair_marginals_of_swap hsym
  have h := entropy_second_difference_nonneg_of_equal_kernel_marginals
    (ν := ν) (r := r) hker (by
      simpa only [P.disintegrate P.condKernel, Measure.compProd_const] using hfinite)
  simpa only [P.disintegrate P.condKernel, Measure.compProd_const, hfst] using h

/-- Separate the last particle from the preceding configuration. -/
def splitLastParticle (d n : ℕ) :
    Configuration d (n + 1) ≃ᵐ Configuration d n × Position d :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ Position d) (Fin.last n)).trans
    MeasurableEquiv.prodComm

theorem splitLastParticle_apply {d n : ℕ} (x : Configuration d (n + 1)) :
    splitLastParticle d n x =
      (restrictCoordinates (Nat.le_succ n) x, x (Fin.last n)) := by
  apply Prod.ext
  · funext i
    change x ((Fin.last n).succAbove i) = x (Fin.castLE (Nat.le_succ n) i)
    rw [Fin.succAbove_last]
    rfl
  · rfl

/-- The reference tensor law splits into its prefix tensor law and one copy
of the reference measure. -/
theorem map_tensorLaw_splitLastParticle {d n : ℕ} (r : Measure (Position d))
    [IsProbabilityMeasure r] :
    (tensorLaw r (n + 1)).map (splitLastParticle d n) = (tensorLaw r n).prod r := by
  have h := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ r) (Fin.last n)
  exact (Measure.measurePreserving_swap.comp h).map_eq

/-- Separate the last two particles from the preceding configuration. -/
def splitLastTwoParticles (d n : ℕ) :
    Configuration d (n + 2) ≃ᵐ Configuration d n × (Position d × Position d) :=
  ((splitLastParticle d (n + 1)).trans
    ((splitLastParticle d n).prodCongr (MeasurableEquiv.refl _))).trans
      MeasurableEquiv.prodAssoc

theorem splitLastTwoParticles_apply {d n : ℕ} (x : Configuration d (n + 2)) :
    splitLastTwoParticles d n x =
      (restrictCoordinates (by omega : n ≤ n + 2) x,
        (x (Fin.castSucc (Fin.last n)), x (Fin.last (n + 1)))) := by
  change ((splitLastParticle d n ((splitLastParticle d (n + 1) x).1)).1,
    ((splitLastParticle d n ((splitLastParticle d (n + 1) x).1)).2,
      (splitLastParticle d (n + 1) x).2)) = _
  simp only [splitLastParticle_apply]
  rfl

theorem map_tensorLaw_splitLastTwoParticles {d n : ℕ} (r : Measure (Position d))
    [IsProbabilityMeasure r] :
    (tensorLaw r (n + 2)).map (splitLastTwoParticles d n) =
      (tensorLaw r n).prod (r.prod r) := by
  have h1 : MeasurePreserving (splitLastParticle d (n + 1))
      (tensorLaw r (n + 2)) ((tensorLaw r (n + 1)).prod r) :=
    ⟨(splitLastParticle d (n + 1)).measurable, map_tensorLaw_splitLastParticle r⟩
  have h2 : MeasurePreserving (splitLastParticle d n)
      (tensorLaw r (n + 1)) ((tensorLaw r n).prod r) :=
    ⟨(splitLastParticle d n).measurable, map_tensorLaw_splitLastParticle r⟩
  exact ((measurePreserving_prodAssoc (tensorLaw r n) r r).comp
    ((h2.prod (MeasurePreserving.id r)).comp h1)).map_eq

theorem marginal_marginal {d k m N : ℕ} (hk : k ≤ m) (hm : m ≤ N)
    (P : Measure (Configuration d N)) :
    marginal hk (marginal hm P) = marginal (hk.trans hm) P := by
  unfold marginal
  rw [Measure.map_map (measurable_restrictCoordinates hk) (measurable_restrictCoordinates hm)]
  rfl

theorem marginal_self {d N : ℕ} (P : Measure (Configuration d N)) :
    marginal (le_refl N) P = P := by
  change P.map id = P
  exact Measure.map_id

theorem marginal_tensorLaw_succ {d n : ℕ} (r : Measure (Position d))
    [IsProbabilityMeasure r] :
    marginal (Nat.le_succ n) (tensorLaw r (n + 1)) = tensorLaw r n := by
  change (tensorLaw r (n + 1)).map (restrictCoordinates (Nat.le_succ n)) = _
  calc
    (tensorLaw r (n + 1)).map (restrictCoordinates (Nat.le_succ n))
        = ((tensorLaw r (n + 1)).map (splitLastParticle d n)).map Prod.fst := by
      rw [Measure.map_map measurable_fst (splitLastParticle d n).measurable]
      congr 1
      funext x
      exact (congrArg Prod.fst (splitLastParticle_apply x)).symm
    _ = tensorLaw r n := by
      rw [map_tensorLaw_splitLastParticle r, Measure.map_fst_prod, measure_univ, one_smul]

theorem marginal_tensorLaw {d k N : ℕ} (hk : k ≤ N) (r : Measure (Position d))
    [IsProbabilityMeasure r] : marginal hk (tensorLaw r N) = tensorLaw r k := by
  induction N generalizing k with
  | zero =>
    have hk0 : k = 0 := by omega
    subst k
    exact marginal_self _
  | succ N ih =>
    by_cases heq : k = N + 1
    · subst k
      exact marginal_self _
    · have hkN : k ≤ N := by omega
      rw [← marginal_marginal hkN (Nat.le_succ N), marginal_tensorLaw_succ r]
      exact ih hkN

theorem marginal_klDiv_ne_top {d k N : ℕ} (hk : k ≤ N)
    {P : Measure (Configuration d N)} [IsProbabilityMeasure P]
    {r : Measure (Position d)} [IsProbabilityMeasure r]
    (hfinite : klDiv P (tensorLaw r N) ≠ ∞) :
    klDiv (marginal hk P) (tensorLaw r k) ≠ ∞ := by
  have h := klDiv_map_le (μ := P) (ν := tensorLaw r N) (measurable_restrictCoordinates hk)
  change klDiv (marginal hk P) (marginal hk (tensorLaw r N)) ≤ _ at h
  rw [marginal_tensorLaw hk r] at h
  exact ne_top_of_le_ne_top hfinite h

/-- Observe a prefix and the next two particles of a larger configuration. -/
def pairObservation {d n N : ℕ} (h : n + 2 ≤ N)
    (x : Configuration d N) : Configuration d n × (Position d × Position d) :=
  (restrictCoordinates (by omega : n ≤ N) x,
    (x ⟨n, by omega⟩, x ⟨n + 1, by omega⟩))

theorem measurable_pairObservation {d n N : ℕ} (h : n + 2 ≤ N) :
    Measurable (pairObservation (d := d) h) := by
  exact (measurable_restrictCoordinates _).prodMk
    ((measurable_pi_apply _).prodMk (measurable_pi_apply _))

theorem pairObservation_eq_split {d n N : ℕ} (h : n + 2 ≤ N) :
    pairObservation (d := d) h = splitLastTwoParticles d n ∘ restrictCoordinates h := by
  funext x
  rw [Function.comp_apply, splitLastTwoParticles_apply]
  rfl

/-- Exchangeability of the full law implies the required two-particle symmetry
of a prefix observation; no symmetry of a chosen conditional kernel is assumed. -/
theorem pairObservation_swap_invariant {d n N : ℕ} (h : n + 2 ≤ N)
    {P : Measure (Configuration d N)} (hex : Exchangeable P) :
    (P.map (pairObservation h)).map (Prod.map id Prod.swap) = P.map (pairObservation h) := by
  let a : Fin N := ⟨n, by omega⟩
  let b : Fin N := ⟨n + 1, by omega⟩
  let e := Equiv.swap a b
  have he : Measurable (fun x : Configuration d N ↦ fun i ↦ x (e i)) := by
    exact measurable_pi_lambda _ (fun i ↦ measurable_pi_apply (e i))
  have hfun : (Prod.map id Prod.swap) ∘ pairObservation h =
      pairObservation h ∘ (fun x : Configuration d N ↦ fun i ↦ x (e i)) := by
    funext x
    apply Prod.ext
    · funext i
      change x (Fin.castLE _ i) = x (e (Fin.castLE _ i))
      have hia : Fin.castLE (show n ≤ N by omega) i ≠ a := by
        intro hi
        have hv := congrArg Fin.val hi
        change (i : ℕ) = n at hv
        omega
      have hib : Fin.castLE (show n ≤ N by omega) i ≠ b := by
        intro hi
        have hv := congrArg Fin.val hi
        change (i : ℕ) = n + 1 at hv
        omega
      rw [show e (Fin.castLE _ i) = Fin.castLE _ i from Equiv.swap_apply_of_ne_of_ne hia hib]
    · change (x b, x a) = (x (e a), x (e b))
      simp only [e, Equiv.swap_apply_left, Equiv.swap_apply_right]
  rw [Measure.map_map (by fun_prop) (measurable_pairObservation h), hfun,
    ← Measure.map_map (measurable_pairObservation h) he, hex e]

/-- The observation of a prefix and two subsequent particles is exactly the
measurable splitting of the corresponding marginal law. -/
theorem map_pairObservation {d n N : ℕ} (h : n + 2 ≤ N)
    (P : Measure (Configuration d N)) :
    P.map (pairObservation h) = (marginal h P).map (splitLastTwoParticles d n) := by
  rw [pairObservation_eq_split, ← Measure.map_map
    (splitLastTwoParticles d n).measurable (measurable_restrictCoordinates h)]
  rfl

theorem pairObservation_fst {d n N : ℕ} (h : n + 2 ≤ N)
    (P : Measure (Configuration d N)) :
    (P.map (pairObservation h)).fst = marginal (by omega : n ≤ N) P := by
  rw [Measure.fst, Measure.map_map measurable_fst (measurable_pairObservation h)]
  rfl

theorem pairObservation_prefix_one {d n N : ℕ} (h : n + 2 ≤ N)
    (P : Measure (Configuration d N)) :
    (P.map (pairObservation h)).map (Prod.map id Prod.fst) =
      (marginal (by omega : n + 1 ≤ N) P).map (splitLastParticle d n) := by
  rw [Measure.map_map (by fun_prop) (measurable_pairObservation h)]
  unfold marginal
  rw [Measure.map_map (splitLastParticle d n).measurable (measurable_restrictCoordinates _)]
  congr 1
  funext x
  simp only [Function.comp_apply, splitLastParticle_apply]
  rfl

/-- Convexity of the actual finite-coordinate entropy sequence follows from
exchangeability and finite full relative entropy against a tensor reference. -/
theorem exchangeable_marginal_entropy_second_difference {d n N : ℕ}
    (h : n + 2 ≤ N) {P : Measure (Configuration d N)} [IsProbabilityMeasure P]
    {r : Measure (Position d)} [IsProbabilityMeasure r]
    (hex : Exchangeable P) (hfinite : klDiv P (tensorLaw r N) ≠ ∞) :
    0 ≤ (klDiv (marginal h P) (tensorLaw r (n + 2))).toReal
      - 2 * (klDiv (marginal (by omega : n + 1 ≤ N) P) (tensorLaw r (n + 1))).toReal
      + (klDiv (marginal (by omega : n ≤ N) P) (tensorLaw r n)).toReal := by
  let Q := P.map (pairObservation h)
  haveI : IsProbabilityMeasure Q :=
    Measure.isProbabilityMeasure_map (measurable_pairObservation h).aemeasurable
  have hKL : klDiv Q ((tensorLaw r n).prod (r.prod r)) =
      klDiv (marginal h P) (tensorLaw r (n + 2)) := by
    rw [show Q = (marginal h P).map (splitLastTwoParticles d n) from map_pairObservation h P,
      ← map_tensorLaw_splitLastTwoParticles r]
    exact klDiv_map_measurableEquiv _
  have hmid : klDiv (Q.map (Prod.map id Prod.fst)) ((tensorLaw r n).prod r) =
      klDiv (marginal (by omega : n + 1 ≤ N) P) (tensorLaw r (n + 1)) := by
    rw [show Q.map (Prod.map id Prod.fst) = _ from pairObservation_prefix_one h P,
      ← map_tensorLaw_splitLastParticle r]
    exact klDiv_map_measurableEquiv _
  have hQfinite : klDiv Q ((tensorLaw r n).prod (r.prod r)) ≠ ∞ := by
    rw [hKL]
    exact marginal_klDiv_ne_top h hfinite
  have hc := entropy_second_difference_nonneg_of_pair_swap
    (P := Q) (ν := tensorLaw r n) (r := r) (pairObservation_swap_invariant h hex) hQfinite
  rw [hKL, hmid, show Q.fst = _ from pairObservation_fst h P] at hc
  exact hc

/-- The real finite-coordinate KL sequence. Values past the full particle
number are set to zero and are never used by the finite hierarchy. -/
def marginalEntropy {d N : ℕ} (P : Measure (Configuration d N))
    (r : Measure (Position d)) (m : ℕ) : ℝ :=
  if hm : m ≤ N then (klDiv (marginal hm P) (tensorLaw r m)).toReal else 0

theorem marginalEntropy_eq {d m N : ℕ} (hm : m ≤ N)
    (P : Measure (Configuration d N)) (r : Measure (Position d)) :
    marginalEntropy P r m = (klDiv (marginal hm P) (tensorLaw r m)).toReal := by
  simp only [marginalEntropy, dif_pos hm]

theorem marginalEntropy_nonneg {d N : ℕ} (P : Measure (Configuration d N))
    (r : Measure (Position d)) (m : ℕ) : 0 ≤ marginalEntropy P r m := by
  unfold marginalEntropy
  split_ifs
  · exact ENNReal.toReal_nonneg
  · exact le_rfl

/-- Probability laws on a subsingleton space coincide. -/
theorem probabilityMeasure_eq_of_subsingleton {A : Type*} [MeasurableSpace A]
    [Subsingleton A] (μ ν : Measure A) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    μ = ν := by
  ext s _
  by_cases hs : s.Nonempty
  · obtain ⟨a, ha⟩ := hs
    have hu : s = Set.univ := Set.eq_univ_of_forall (fun x ↦ by
      rw [Subsingleton.elim x a]
      exact ha)
    simp only [hu, measure_univ]
  · have he : s = ∅ := Set.not_nonempty_iff_eq_empty.mp hs
    simp only [he, measure_empty]

theorem marginalEntropy_zero {d N : ℕ} (P : Measure (Configuration d N))
    [IsProbabilityMeasure P] (r : Measure (Position d)) [IsProbabilityMeasure r] :
    marginalEntropy P r 0 = 0 := by
  rw [marginalEntropy_eq (Nat.zero_le N),
    probabilityMeasure_eq_of_subsingleton (marginal (Nat.zero_le N) P) (tensorLaw r 0),
    klDiv_self, ENNReal.toReal_zero]

/-- Actual exchangeable marginal entropy increments are increasing at every
adjacent pair of levels. -/
theorem exchangeable_entropy_increment_step {d m N : ℕ} (hm : m + 2 ≤ N)
    {P : Measure (Configuration d N)} [IsProbabilityMeasure P]
    {r : Measure (Position d)} [IsProbabilityMeasure r]
    (hex : Exchangeable P) (hfinite : klDiv P (tensorLaw r N) ≠ ∞) :
    entropyIncrement (marginalEntropy P r) m ≤ entropyIncrement (marginalEntropy P r) (m + 1) := by
  have hc := exchangeable_marginal_entropy_second_difference hm hex hfinite
  unfold entropyIncrement
  rw [marginalEntropy_eq (by omega : m + 1 ≤ N), marginalEntropy_eq (by omega : m ≤ N),
    marginalEntropy_eq (by omega : m + 1 + 1 ≤ N)]
  change _ ≤ (klDiv (marginal hm P) (tensorLaw r (m + 2))).toReal - _
  linarith

/-- The sequence hypotheses used by the entropy hierarchy are discharged by
exchangeability, a probability tensor reference, and finite full KL divergence.
In particular, monotonicity of entropy increments is proved rather than assumed. -/
theorem exchangeable_finiteEntropyConditions {d N : ℕ}
    {P : Measure (Configuration d N)} [IsProbabilityMeasure P]
    {r : Measure (Position d)} [IsProbabilityMeasure r]
    (hex : Exchangeable P) (hfinite : klDiv P (tensorLaw r N) ≠ ∞) :
    FiniteEntropyConditions (marginalEntropy P r) N := by
  refine ⟨marginalEntropy_zero P r, ?_, ?_⟩
  · unfold entropyIncrement
    rw [marginalEntropy_zero P r, sub_zero]
    exact marginalEntropy_nonneg P r 1
  · have hmon : ∀ j, j < N → ∀ i, i ≤ j →
        entropyIncrement (marginalEntropy P r) i ≤ entropyIncrement (marginalEntropy P r) j := by
      intro j
      induction j with
      | zero =>
        intro _ i hi
        have hi0 : i = 0 := by omega
        subst i
        exact le_rfl
      | succ j ih =>
        intro hj i hi
        by_cases hij : i = j + 1
        · subst i
          exact le_rfl
        · exact (ih (by omega) i (by omega)).trans
            (exchangeable_entropy_increment_step (by omega : j + 2 ≤ N) hex hfinite)
    exact fun i j hij hj ↦ hmon j hj i hij

/-- The entropy source coefficient estimate now has actual measure-theoretic
inputs: its only remaining quantitative entropy hypothesis is the profile. -/
theorem exchangeable_entropy_external_source_bound {d N m : ℕ} {A : ℝ}
    {P : Measure (Configuration d N)} [IsProbabilityMeasure P]
    {r : Measure (Position d)} [IsProbabilityMeasure r]
    (hex : Exchangeable P) (hfinite : klDiv P (tensorLaw r N) ≠ ∞)
    (hN : 0 < N) (hm : 0 < m) (hmN : m ≤ N) (hA : 0 ≤ A)
    (hprofile : ∀ j, j ≤ N → marginalEntropy P r j ≤ A * (j : ℝ) ^ 2 / (N : ℝ) ^ 2) :
    (((N : ℝ) - m) / N) ^ 2 * m * entropyIncrement (marginalEntropy P r) m ≤
      4 * A * (m : ℝ) ^ 2 / (N : ℝ) ^ 2 :=
  entropy_external_source_bound (exchangeable_finiteEntropyConditions hex hfinite)
    hN hm hmN hA hprofile

end SharpWasserstein
