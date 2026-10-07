module

public import SharpWasserstein.Compat
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Normed.Module.RCLike.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Hilbert-space tangent energy

The variational energy is proved equal to the squared norm of the Riesz
representative, and consistent representatives satisfy an exact Pythagorean
energy-increment identity. These results apply to any real Hilbert space.

The manuscript's realization of this Hilbert space as the closed space of
weighted `L²` gradients, its distributional divergence, and its evolution by a
diffusion are not definitions or hypotheses hidden in this module. Establishing
that realization and the analytic evolution remains a separate task.
-/

noncomputable section

namespace SharpWasserstein.TangentEnergy

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The objective in the weighted negative-Sobolev variational definition. -/
def dualObjective (ℓ : E →L[ℝ] ℝ) (v : E) : ℝ := 2 * ℓ v - ‖v‖ ^ 2

/-- The Hilbert-space variational tangent energy, with supremum in `ℝ`. -/
def dualEnergy (ℓ : E →L[ℝ] ℝ) : ℝ := sSup (Set.range (dualObjective ℓ))

section Riesz

variable [CompleteSpace E]

/-- Riesz representative of a continuous real linear functional. -/
def rieszRepresentative (ℓ : E →L[ℝ] ℝ) : E :=
  (InnerProductSpace.toDual ℝ E).symm ℓ

@[simp]
theorem inner_rieszRepresentative (ℓ : E →L[ℝ] ℝ) (v : E) :
    ⟪rieszRepresentative ℓ, v⟫_ℝ = ℓ v :=
  InnerProductSpace.toDual_symm_apply

/-- The representing vector exists and is unique. -/
theorem existsUnique_rieszRepresentative (ℓ : E →L[ℝ] ℝ) :
    ∃! w : E, ∀ v : E, ⟪w, v⟫_ℝ = ℓ v := by
  refine ⟨rieszRepresentative ℓ, inner_rieszRepresentative ℓ, ?_⟩
  intro w hw
  apply (InnerProductSpace.toDual ℝ E).injective
  apply ContinuousLinearMap.ext
  intro v
  simpa only [InnerProductSpace.toDual_apply_apply, inner_rieszRepresentative] using hw v

/-- Completing the square identifies both the optimizer and the energy. -/
theorem dualObjective_eq_sub_sq (ℓ : E →L[ℝ] ℝ) (v : E) :
    dualObjective ℓ v = ‖rieszRepresentative ℓ‖ ^ 2 -
      ‖v - rieszRepresentative ℓ‖ ^ 2 := by
  rw [norm_sub_sq_real, real_inner_comm (rieszRepresentative ℓ) v,
    inner_rieszRepresentative]
  unfold dualObjective
  ring

/-- The variational supremum is attained at the Riesz representative. -/
theorem dualObjective_isGreatest (ℓ : E →L[ℝ] ℝ) :
    IsGreatest (Set.range (dualObjective ℓ)) (‖rieszRepresentative ℓ‖ ^ 2) := by
  constructor
  · exact ⟨rieszRepresentative ℓ, by simp [dualObjective_eq_sub_sq]⟩
  · rintro y ⟨v, rfl⟩
    rw [dualObjective_eq_sub_sq]
    exact sub_le_self _ (sq_nonneg _)

/-- Exact dual energy characterization, with no assumed energy bound. -/
theorem dualEnergy_eq_norm_sq (ℓ : E →L[ℝ] ℝ) :
    dualEnergy ℓ = ‖rieszRepresentative ℓ‖ ^ 2 :=
  (dualObjective_isGreatest ℓ).csSup_eq

/-- The variational energy also equals the square of the functional's norm. -/
theorem dualEnergy_eq_dual_norm_sq (ℓ : E →L[ℝ] ℝ) :
    dualEnergy ℓ = ‖ℓ‖ ^ 2 := by
  rw [dualEnergy_eq_norm_sq]
  congr 1
  exact (InnerProductSpace.toDual ℝ E).symm.norm_map ℓ

theorem dualEnergy_nonneg (ℓ : E →L[ℝ] ℝ) : 0 ≤ dualEnergy ℓ := by
  rw [dualEnergy_eq_norm_sq]
  exact sq_nonneg _

/-- Uniqueness of the variational maximizer. -/
theorem dualObjective_eq_energy_iff (ℓ : E →L[ℝ] ℝ) (v : E) :
    dualObjective ℓ v = dualEnergy ℓ ↔ v = rieszRepresentative ℓ := by
  rw [dualObjective_eq_sub_sq, dualEnergy_eq_norm_sq]
  constructor
  · intro h
    have hz : ‖v - rieszRepresentative ℓ‖ ^ 2 = 0 := by linarith
    have hn : ‖v - rieszRepresentative ℓ‖ = 0 := sq_eq_zero_iff.mp hz
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)
  · intro h
    simp [h]

end Riesz


/-- Finite variational energy forces continuity; continuity is not an extra assumption. -/
theorem continuous_of_bounded_variationalObjective (ℓ : E →ₗ[ℝ] ℝ)
    (h : BddAbove (Set.range (fun v : E => 2 * ℓ v - ‖v‖ ^ 2))) :
    Continuous ℓ := by
  obtain ⟨C, hC⟩ := h
  have hb (v : E) : 2 * ℓ v - ‖v‖ ^ 2 ≤ C := hC ⟨v, rfl⟩
  have hs : ∀ v ∈ Metric.sphere (0 : E) 1, ‖ℓ v‖ ≤ (C + 1) / 2 := by
    intro v hv
    have hnorm : ‖v‖ = 1 := by simpa using hv
    have hp := hb v
    have hn := hb (-v)
    simp only [map_neg, norm_neg] at hn
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor <;> nlinarith [hp, hn]
  have hbound (v : E) : ‖ℓ v‖ ≤ ((C + 1) / 2) * ‖v‖ := by
    simpa using ℓ.bound_of_sphere_bound (by norm_num : (0 : ℝ) < 1)
      ((C + 1) / 2) hs v
  exact AddMonoidHomClass.continuous_of_bound ℓ ((C + 1) / 2) hbound

/-- The continuous functional built from a merely linear finite-energy tangent. -/
def continuousTangentOfBound (ℓ : E →ₗ[ℝ] ℝ)
    (h : BddAbove (Set.range (fun v : E => 2 * ℓ v - ‖v‖ ^ 2))) : E →L[ℝ] ℝ :=
  ⟨ℓ, continuous_of_bounded_variationalObjective ℓ h⟩

@[simp]
theorem continuousTangentOfBound_apply (ℓ : E →ₗ[ℝ] ℝ)
    (h : BddAbove (Set.range (fun v : E => 2 * ℓ v - ‖v‖ ^ 2))) (v : E) :
    continuousTangentOfBound ℓ h v = ℓ v := rfl

/-- Riesz representation follows from the variational finiteness hypothesis itself. -/
theorem existsUnique_riesz_of_bounded_variationalObjective [CompleteSpace E]
    (ℓ : E →ₗ[ℝ] ℝ)
    (h : BddAbove (Set.range (fun v : E => 2 * ℓ v - ‖v‖ ^ 2))) :
    ∃! w : E, ∀ v : E, ⟪w, v⟫_ℝ = ℓ v :=
  existsUnique_rieszRepresentative (continuousTangentOfBound ℓ h)

/-- Exact variational value for a functional initially assumed only to be linear. -/
theorem linear_variationalEnergy_eq_norm_sq [CompleteSpace E] (ℓ : E →ₗ[ℝ] ℝ)
    (h : BddAbove (Set.range (fun v : E => 2 * ℓ v - ‖v‖ ^ 2))) :
    sSup (Set.range (fun v : E => 2 * ℓ v - ‖v‖ ^ 2)) =
      ‖rieszRepresentative (continuousTangentOfBound ℓ h)‖ ^ 2 :=
  dualEnergy_eq_norm_sq (continuousTangentOfBound ℓ h)

section Projection

variable (K : Submodule ℝ E) [K.HasOrthogonalProjection]

/-- The exact increment from a tangent to its projection on a lower-level space. -/
theorem projection_energy_increment (w : E) :
    ‖w‖ ^ 2 - ‖K.starProjection w‖ ^ 2 = ‖w - K.starProjection w‖ ^ 2 := by
  have h := norm_sub_sq_real w (K.starProjection w)
  have ho := K.starProjection_inner_eq_zero w (K.starProjection w)
    (K.starProjection_apply_mem w)
  rw [inner_sub_left, real_inner_self_eq_norm_sq] at ho
  nlinarith

theorem projection_energy_mono (w : E) :
    ‖K.starProjection w‖ ^ 2 ≤ ‖w‖ ^ 2 := by
  have h := projection_energy_increment K w
  nlinarith [sq_nonneg ‖w - K.starProjection w‖]

/-- Consistency of pairings identifies the lower-level field as an orthogonal projection. -/
theorem projection_eq_of_consistent_pairings (w v : E) (hv : v ∈ K)
    (hpair : ∀ z ∈ K, ⟪w, z⟫_ℝ = ⟪v, z⟫_ℝ) :
    K.starProjection w = v := by
  apply K.eq_starProjection_of_mem_of_inner_eq_zero hv
  intro z hz
  rw [inner_sub_left, hpair z hz, sub_self]

/-- The precise Pythagorean identity used for consistent marginal tangent fields. -/
theorem consistent_energy_increment (w v : E) (hv : v ∈ K)
    (hpair : ∀ z ∈ K, ⟪w, z⟫_ℝ = ⟪v, z⟫_ℝ) :
    ‖w‖ ^ 2 - ‖v‖ ^ 2 = ‖w - v‖ ^ 2 := by
  have hp := projection_eq_of_consistent_pairings K w v hv hpair
  simpa [hp] using projection_energy_increment K w

/-- A consistent lower-level representative has no larger energy. -/
theorem consistent_energy_mono (w v : E) (hv : v ∈ K)
    (hpair : ∀ z ∈ K, ⟪w, z⟫_ℝ = ⟪v, z⟫_ℝ) :
    ‖v‖ ^ 2 ≤ ‖w‖ ^ 2 := by
  have h := consistent_energy_increment K w v hv hpair
  nlinarith [sq_nonneg ‖w - v‖]

end Projection

/-- Closed subspaces of a Hilbert space satisfy the manuscript's increment identity. -/
theorem closedSubspace_energy_increment [CompleteSpace E] (K : ClosedSubmodule ℝ E)
    (w v : E) (hv : v ∈ K) (hpair : ∀ z ∈ K, ⟪w, z⟫_ℝ = ⟪v, z⟫_ℝ) :
    ‖w‖ ^ 2 - ‖v‖ ^ 2 = ‖w - v‖ ^ 2 :=
  consistent_energy_increment K.toSubmodule w v hv hpair

/-- Scalar Young absorption, in the form needed for the Hessian residual. -/
theorem young_absorption (a x y : ℝ) :
    2 * a * x * y ≤ x ^ 2 + a ^ 2 * y ^ 2 := by
  nlinarith [sq_nonneg (x - a * y)]

/-- Absorb two residual products with separate energy and Hessian terms. -/
theorem two_term_young_absorption (a b r e q : ℝ) :
    2 * a * r * e + 2 * b * r * q ≤
      e ^ 2 + q ^ 2 + (a ^ 2 + b ^ 2) * r ^ 2 := by
  nlinarith [sq_nonneg (e - a * r), sq_nonneg (q - b * r)]

/-- Hilbert-space Young inequality, without a scalar sign restriction. -/
theorem inner_young_absorption (x y : E) :
    2 * ⟪x, y⟫_ℝ ≤ ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  have h := norm_sub_sq_real x y
  nlinarith [sq_nonneg ‖x - y‖]

end SharpWasserstein.TangentEnergy
