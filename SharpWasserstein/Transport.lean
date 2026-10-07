module

public import SharpWasserstein.Compat
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FunProp

@[expose] public section

/-! The actual unnormalized quadratic transport cost on particle configurations.
The surrounding Pi type has its usual sup norm; that norm is deliberately NOT
used as the transport cost. No transport metric theorem is assumed here. -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators

namespace SharpWasserstein

abbrev Position (d : ℕ) := Fin d → ℝ
abbrev Configuration (d N : ℕ) := Fin N → Position d

def productCost {d N : ℕ} (x y : Configuration d N) : ℝ :=
  ∑ i, ∑ a, (x i a - y i a) ^ 2

theorem productCost_nonneg {d N : ℕ} (x y : Configuration d N) :
    0 ≤ productCost x y := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun a _ => sq_nonneg _

@[simp] theorem productCost_self {d N : ℕ} (x : Configuration d N) :
    productCost x x = 0 := by simp [productCost]

theorem productCost_symm {d N : ℕ} (x y : Configuration d N) :
    productCost x y = productCost y x := by
  unfold productCost
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  ring

def IsCoupling {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) (γ : Measure (X × X)) : Prop :=
  IsProbabilityMeasure γ ∧ Measure.map Prod.fst γ = μ ∧ Measure.map Prod.snd γ = ν

def transportCost {d N : ℕ}
    (γ : Measure (Configuration d N × Configuration d N)) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (productCost z.1 z.2) ∂γ

/-- Squared quadratic Wasserstein distance, defined by the infimum over real
probability couplings. The extended value records possible infinite cost. -/
def wassersteinSq {d N : ℕ} (μ ν : Measure (Configuration d N)) : ℝ≥0∞ :=
  ⨅ (γ : Measure (Configuration d N × Configuration d N)) (_ : IsCoupling μ ν γ),
    transportCost γ

theorem wassersteinSq_le_cost {d N : ℕ}
    {μ ν : Measure (Configuration d N)} {γ : Measure (Configuration d N × Configuration d N)}
    (hγ : IsCoupling μ ν γ) : wassersteinSq μ ν ≤ transportCost γ := by
  exact iInf_le_of_le γ (iInf_le_of_le hγ le_rfl)

def HasSecondMoment {d N : ℕ} (μ : Measure (Configuration d N)) : Prop :=
  (∫⁻ x, ENNReal.ofReal (productCost x 0) ∂μ) < ∞

def tensorLaw {d : ℕ} (μ : Measure (Position d)) (N : ℕ) :
    Measure (Configuration d N) := Measure.pi fun _ => μ

def restrictCoordinates {d k N : ℕ} (h : k ≤ N)
    (x : Configuration d N) : Configuration d k := fun i => x (Fin.castLE h i)

def marginal {d k N : ℕ} (h : k ≤ N) (P : Measure (Configuration d N)) :
    Measure (Configuration d k) := Measure.map (restrictCoordinates h) P

def Exchangeable {d N : ℕ} (P : Measure (Configuration d N)) : Prop :=
  ∀ e : Equiv.Perm (Fin N), Measure.map (fun x i => x (e i)) P = P

theorem measurable_restrictCoordinates {d k N : ℕ} (h : k ≤ N) :
    Measurable (restrictCoordinates (d := d) h) := by
  exact Measurable.of_eval fun i => measurable_pi_apply _

theorem measurable_productCost {d N : ℕ} :
    Measurable (fun z : Configuration d N × Configuration d N => productCost z.1 z.2) := by
  unfold productCost
  fun_prop

theorem diagonal_isCoupling {d N : ℕ} (μ : Measure (Configuration d N))
    [IsProbabilityMeasure μ] :
    IsCoupling μ μ (Measure.map (fun x => (x, x)) μ) := by
  have hd : Measurable (fun x : Configuration d N => (x, x)) :=
    measurable_id.prodMk measurable_id
  refine ⟨Measure.isProbabilityMeasure_map hd.aemeasurable, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst hd]
    exact Measure.map_id
  · rw [Measure.map_map measurable_snd hd]
    exact Measure.map_id

@[simp] theorem wassersteinSq_self {d N : ℕ} (μ : Measure (Configuration d N))
    [IsProbabilityMeasure μ] : wassersteinSq μ μ = 0 := by
  apply le_antisymm _ bot_le
  calc
    wassersteinSq μ μ ≤ transportCost (Measure.map (fun x => (x, x)) μ) :=
      wassersteinSq_le_cost (diagonal_isCoupling μ)
    _ = 0 := by
      have hd : Measurable (fun x : Configuration d N => (x, x)) :=
        measurable_id.prodMk measurable_id
      rw [transportCost, lintegral_map (μ := μ) (g := fun x => (x, x))
        measurable_productCost.ennreal_ofReal hd]
      simp

theorem coupling_swap {d N : ℕ} {μ ν : Measure (Configuration d N)}
    {γ : Measure (Configuration d N × Configuration d N)} (hγ : IsCoupling μ ν γ) :
    IsCoupling ν μ (Measure.map Prod.swap γ) := by
  letI : IsProbabilityMeasure γ := hγ.1
  refine ⟨Measure.isProbabilityMeasure_map measurable_swap.aemeasurable, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst measurable_swap]
    exact hγ.2.2
  · rw [Measure.map_map measurable_snd measurable_swap]
    exact hγ.2.1

theorem transportCost_swap {d N : ℕ}
    (γ : Measure (Configuration d N × Configuration d N)) :
    transportCost (Measure.map Prod.swap γ) = transportCost γ := by
  rw [transportCost, lintegral_map measurable_productCost.ennreal_ofReal measurable_swap]
  simp only [Prod.swap, productCost_symm]
  rfl

theorem wassersteinSq_symm {d N : ℕ} (μ ν : Measure (Configuration d N)) :
    wassersteinSq μ ν = wassersteinSq ν μ := by
  have swap_le : ∀ μ ν : Measure (Configuration d N), wassersteinSq μ ν ≤ wassersteinSq ν μ := by
    intro μ ν
    apply le_iInf
    intro γ
    apply le_iInf
    intro hγ
    exact (wassersteinSq_le_cost (coupling_swap hγ)).trans_eq (transportCost_swap γ)
  exact le_antisymm (swap_le μ ν) (swap_le ν μ)

theorem productCost_restrict_le {d k N : ℕ} (h : k ≤ N) (x y : Configuration d N) :
    productCost (restrictCoordinates h x) (restrictCoordinates h y) ≤ productCost x y := by
  classical
  let e : Fin k ↪ Fin N := ⟨Fin.castLE h, Fin.castLE_injective h⟩
  let f : Fin N → ℝ := fun i => ∑ a, (x i a - y i a) ^ 2
  change (∑ i : Fin k, f (e i)) ≤ ∑ j : Fin N, f j
  calc
    (∑ i : Fin k, f (e i)) = ∑ j ∈ Finset.univ.map e, f j :=
      (Finset.sum_map _ _ _).symm
    _ ≤ ∑ j : Fin N, f j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem coupling_marginal {d k N : ℕ} (h : k ≤ N)
    {μ ν : Measure (Configuration d N)}
    {γ : Measure (Configuration d N × Configuration d N)} (hγ : IsCoupling μ ν γ) :
    IsCoupling (marginal h μ) (marginal h ν)
      (Measure.map (fun z => (restrictCoordinates h z.1, restrictCoordinates h z.2)) γ) := by
  letI : IsProbabilityMeasure γ := hγ.1
  have hq := measurable_restrictCoordinates (d := d) h
  have hm : Measurable (fun z : Configuration d N × Configuration d N =>
      (restrictCoordinates h z.1, restrictCoordinates h z.2)) :=
    (hq.comp measurable_fst).prodMk (hq.comp measurable_snd)
  refine ⟨Measure.isProbabilityMeasure_map hm.aemeasurable, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst hm]
    change Measure.map (restrictCoordinates h ∘ Prod.fst) γ = Measure.map _ μ
    rw [← Measure.map_map hq measurable_fst, hγ.2.1]
  · rw [Measure.map_map measurable_snd hm]
    change Measure.map (restrictCoordinates h ∘ Prod.snd) γ = Measure.map _ ν
    rw [← Measure.map_map hq measurable_snd, hγ.2.2]

theorem transportCost_marginal_le {d k N : ℕ} (h : k ≤ N)
    (γ : Measure (Configuration d N × Configuration d N)) :
    transportCost (Measure.map
      (fun z => (restrictCoordinates h z.1, restrictCoordinates h z.2)) γ) ≤
      transportCost γ := by
  have hq := measurable_restrictCoordinates (d := d) h
  have hm : Measurable (fun z : Configuration d N × Configuration d N =>
      (restrictCoordinates h z.1, restrictCoordinates h z.2)) :=
    (hq.comp measurable_fst).prodMk (hq.comp measurable_snd)
  rw [transportCost, lintegral_map (g := fun z : Configuration d N × Configuration d N =>
    (restrictCoordinates h z.1, restrictCoordinates h z.2))
    (measurable_productCost (d := d) (N := k)).ennreal_ofReal hm]
  apply lintegral_mono
  intro z
  exact ENNReal.ofReal_le_ofReal (productCost_restrict_le h z.1 z.2)

/-- Genuine transport contraction under coordinate deletion. -/
theorem wassersteinSq_marginal_le {d k N : ℕ} (h : k ≤ N)
    (μ ν : Measure (Configuration d N)) :
    wassersteinSq (marginal h μ) (marginal h ν) ≤ wassersteinSq μ ν := by
  apply le_iInf
  intro γ
  apply le_iInf
  intro hγ
  exact (wassersteinSq_le_cost (coupling_marginal h hγ)).trans
    (transportCost_marginal_le h γ)

end SharpWasserstein
