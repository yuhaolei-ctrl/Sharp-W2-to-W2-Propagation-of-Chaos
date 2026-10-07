module

public import SharpWasserstein.Compat
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Finite cooperative hierarchy comparison

This module proves the finite-dimensional comparison argument used for tangent
energies. The differential inequalities are explicit hypotheses: their origin
in the diffusion PDE and the justification of differentiability are not claimed
here. Right derivatives on `[a,b)` and continuity on `[a,b]` suffice.
-/

open Set Real

namespace SharpWasserstein

/-- Scalar one-sided Grönwall, with zero initial upper bound. -/
theorem scalar_le_zero_of_deriv_le_mul
    {f f' : ℝ → ℝ} {K a b : ℝ}
    (hc : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ico a b, HasDerivWithinAt f (f' t) (Ici t) t)
    (ha : f a ≤ 0)
    (hbound : ∀ t ∈ Ico a b, f' t ≤ K * f t) :
    ∀ t ∈ Icc a b, f t ≤ 0 := by
  intro t ht
  have h := le_gronwallBound_of_liminf_deriv_right_le
    (δ := 0) (K := K) (ε := 0) hc
    (fun x hx r hr => (hd x hx).liminf_right_slope_le hr) ha
    (by simpa using hbound) t ht
  simpa only [gronwallBound_ε0_δ0] using h

/-- Comparison of two scalar curves from an inequality for their difference. -/
theorem scalar_comparison
    {f g f' g' : ℝ → ℝ} {K a b : ℝ}
    (hfc : ContinuousOn f (Icc a b)) (hgc : ContinuousOn g (Icc a b))
    (hfd : ∀ t ∈ Ico a b, HasDerivWithinAt f (f' t) (Ici t) t)
    (hgd : ∀ t ∈ Ico a b, HasDerivWithinAt g (g' t) (Ici t) t)
    (ha : f a ≤ g a)
    (hbound : ∀ t ∈ Ico a b, f' t - g' t ≤ K * (f t - g t)) :
    ∀ t ∈ Icc a b, f t ≤ g t := by
  have h := scalar_le_zero_of_deriv_le_mul (f := fun t => f t - g t)
    (f' := fun t => f' t - g' t) (K := K)
    (hfc.sub hgc) (fun t ht => (hfd t ht).sub (hgd t ht))
    (sub_nonpos.mpr ha) hbound
  exact fun t ht => sub_nonpos.mp (h t ht)

/-- Comparison for levels `1,...,N` of the cooperative hierarchy.

The coefficient `C*m` multiplying the next level is nonnegative. Backward
induction therefore reduces every level to scalar Grönwall, starting at `N`.
Neither nonnegativity nor monotonicity of the curves themselves is needed.
-/
theorem finite_cooperative_comparison
    {N : ℕ} {C a b : ℝ} (hC : 0 ≤ C)
    {E F Ed Fd : ℕ → ℝ → ℝ}
    (hEc : ∀ m, 1 ≤ m → m ≤ N → ContinuousOn (E m) (Icc a b))
    (hFc : ∀ m, 1 ≤ m → m ≤ N → ContinuousOn (F m) (Icc a b))
    (hEd : ∀ m, 1 ≤ m → m ≤ N → ∀ t ∈ Ico a b,
      HasDerivWithinAt (E m) (Ed m t) (Ici t) t)
    (hFd : ∀ m, 1 ≤ m → m ≤ N → ∀ t ∈ Ico a b,
      HasDerivWithinAt (F m) (Fd m t) (Ici t) t)
    (hinit : ∀ m, 1 ≤ m → m ≤ N → E m a ≤ F m a)
    (hE : ∀ m, 1 ≤ m → m < N → ∀ t ∈ Ico a b,
      Ed m t ≤ C * E m t + C * m * (E (m + 1) t - E m t))
    (hF : ∀ m, 1 ≤ m → m < N → ∀ t ∈ Ico a b,
      C * F m t + C * m * (F (m + 1) t - F m t) ≤ Fd m t)
    (hEN : ∀ t ∈ Ico a b, Ed N t ≤ C * E N t)
    (hFN : ∀ t ∈ Ico a b, C * F N t ≤ Fd N t) :
    ∀ m, 1 ≤ m → m ≤ N → ∀ t ∈ Icc a b, E m t ≤ F m t := by
  intro m hm hmN
  induction hmN using Nat.decreasingInduction with
  | self =>
      apply scalar_comparison (K := C)
        (hEc N hm le_rfl) (hFc N hm le_rfl)
        (hEd N hm le_rfl) (hFd N hm le_rfl) (hinit N hm le_rfl)
      intro t ht
      have he := hEN t ht
      have hf := hFN t ht
      linarith
  | of_succ m hmN ih =>
      apply scalar_comparison (K := C * (1 - m))
        (hEc m hm (Nat.le_of_lt hmN)) (hFc m hm (Nat.le_of_lt hmN))
        (hEd m hm (Nat.le_of_lt hmN)) (hFd m hm (Nat.le_of_lt hmN))
        (hinit m hm (Nat.le_of_lt hmN))
      intro t ht
      have he := hE m hm hmN t ht
      have hf := hF m hm hmN t ht
      have hn := ih (Nat.le_trans hm (Nat.le_succ m)) t ⟨ht.1, le_of_lt ht.2⟩
      have hn' := mul_le_mul_of_nonneg_left hn
        (mul_nonneg hC (Nat.cast_nonneg m))
      nlinarith

/-- The quadratic supersolution, shifted to initial time `a`. -/
noncomputable def quadraticProfile (A C a : ℝ) (N m : ℕ) (t : ℝ) : ℝ :=
  A * exp (4 * C * (t - a)) * (m : ℝ) ^ 2 / (N : ℝ) ^ 2

@[simp] theorem quadraticProfile_initial (A C a : ℝ) (N m : ℕ) :
    quadraticProfile A C a N m a = A * (m : ℝ) ^ 2 / (N : ℝ) ^ 2 := by
  simp [quadraticProfile]

/-- Exact derivative of the explicit profile. -/
theorem hasDerivAt_quadraticProfile (A C a : ℝ) (N m : ℕ) (t : ℝ) :
    HasDerivAt (quadraticProfile A C a N m)
      (4 * C * quadraticProfile A C a N m t) t := by
  have hExp := (((hasDerivAt_id t).sub_const a).const_mul (4 * C)).exp
  have h := ((hExp.const_mul A).mul_const ((m : ℝ) ^ 2)).div_const ((N : ℝ) ^ 2)
  apply h.congr_deriv
  dsimp [quadraticProfile]
  ring

/-- The profile is nonnegative for nonnegative initial size. -/
theorem quadraticProfile_nonneg {A C a t : ℝ} {N m : ℕ} (hA : 0 ≤ A) :
    0 ≤ quadraticProfile A C a N m t := by
  unfold quadraticProfile
  positivity

/-- The factor `4*C` dominates the entire quadratic hierarchy. -/
theorem quadraticProfile_supersolution
    {A C a t : ℝ} {N m : ℕ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hm : 1 ≤ m) :
    C * quadraticProfile A C a N m t +
      C * m * (quadraticProfile A C a N (m + 1) t -
        quadraticProfile A C a N m t) ≤
      4 * C * quadraticProfile A C a N m t := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hfactor : 0 ≤ C * (A * exp (4 * C * (t - a)) / (N : ℝ) ^ 2) := by
    positivity
  have harith : (m : ℝ) ^ 2 + m * (((m : ℝ) + 1) ^ 2 - (m : ℝ) ^ 2) ≤
      4 * (m : ℝ) ^ 2 := by nlinarith
  have h := mul_le_mul_of_nonneg_left harith hfactor
  calc
    _ = (C * (A * exp (4 * C * (t - a)) / (N : ℝ) ^ 2)) *
        ((m : ℝ) ^ 2 + m * (((m : ℝ) + 1) ^ 2 - (m : ℝ) ^ 2)) := by
      simp only [quadraticProfile, Nat.cast_add, Nat.cast_one]
      ring
    _ ≤ (C * (A * exp (4 * C * (t - a)) / (N : ℝ) ^ 2)) *
        (4 * (m : ℝ) ^ 2) := h
    _ = _ := by unfold quadraticProfile; ring

/-- The terminal level satisfies the supersolution inequality too. -/
theorem quadraticProfile_boundary {A C a t : ℝ} {N : ℕ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) :
    C * quadraticProfile A C a N N t ≤ 4 * C * quadraticProfile A C a N N t := by
  have h := quadraticProfile_nonneg (C := C) (a := a) (t := t) (N := N) (m := N) hA
  nlinarith [mul_nonneg hC h]

/-- Propagation of `A*m^2/N^2` by the actual finite differential hierarchy.

This theorem is conditional only on the displayed real-variable hypotheses.
It does not assume the desired propagated estimate or a comparison principle.
-/
theorem finite_cooperative_quadratic_bound
    {N : ℕ} {A C a b : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    {E Ed : ℕ → ℝ → ℝ}
    (hEc : ∀ m, 1 ≤ m → m ≤ N → ContinuousOn (E m) (Icc a b))
    (hEd : ∀ m, 1 ≤ m → m ≤ N → ∀ t ∈ Ico a b,
      HasDerivWithinAt (E m) (Ed m t) (Ici t) t)
    (hinit : ∀ m, 1 ≤ m → m ≤ N → E m a ≤ A * (m : ℝ) ^ 2 / (N : ℝ) ^ 2)
    (hE : ∀ m, 1 ≤ m → m < N → ∀ t ∈ Ico a b,
      Ed m t ≤ C * E m t + C * m * (E (m + 1) t - E m t))
    (hEN : ∀ t ∈ Ico a b, Ed N t ≤ C * E N t) :
    ∀ m, 1 ≤ m → m ≤ N → ∀ t ∈ Icc a b,
      E m t ≤ A * exp (4 * C * (t - a)) * (m : ℝ) ^ 2 / (N : ℝ) ^ 2 := by
  apply finite_cooperative_comparison (F := quadraticProfile A C a N)
    (Fd := fun m t => 4 * C * quadraticProfile A C a N m t) hC hEc
  · intro m _ _
    exact (continuous_iff_continuousAt.mpr
      (fun t => (hasDerivAt_quadraticProfile A C a N m t).continuousAt)).continuousOn
  · exact hEd
  · intro m _ _ t _
    exact (hasDerivAt_quadraticProfile A C a N m t).hasDerivWithinAt
  · simpa using hinit
  · exact hE
  · intro m hm _ t _
    exact quadraticProfile_supersolution hA hC hm
  · exact hEN
  · intro t _
    exact quadraticProfile_boundary hA hC

end SharpWasserstein
