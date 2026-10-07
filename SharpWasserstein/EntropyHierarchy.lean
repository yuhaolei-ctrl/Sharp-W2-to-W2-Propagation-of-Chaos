module

public import SharpWasserstein.Compat
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Finite entropy-increment and source-energy estimates

This module proves the finite-sequence and real-algebra part of the entropy
source estimate. The sequence hypotheses are explicit: identifying them with
relative entropies requires the probabilistic chain-rule argument, which is
not claimed by this module.
-/

namespace SharpWasserstein

/-- The increment with left endpoint `m`, corresponding to δ_{m+1}. -/
def entropyIncrement (h : ℕ → ℝ) (m : ℕ) : ℝ := h (m + 1) - h m

/-- A lower bound on each increment telescopes over a finite block. -/
theorem entropy_block_telescope (h : ℕ → ℝ) (m len : ℕ) (d : ℝ)
    (hinc : ∀ j, m ≤ j → j < m + len → d ≤ entropyIncrement h j) :
    h m + (len : ℝ) * d ≤ h (m + len) := by
  induction len with
  | zero => simp
  | succ len ih =>
    have hprev : h m + (len : ℝ) * d ≤ h (m + len) := by
      apply ih
      intro j hj hj'
      exact hinc j hj (by omega)
    have hlast := hinc (m + len) (by omega) (by omega)
    unfold entropyIncrement at hlast
    push_cast
    simpa [Nat.add_assoc] using (show h m + ((len : ℝ) + 1) * d ≤
      h (m + len + 1) by nlinarith)

/-- Explicit sequence conditions used by the entropy hierarchy.

The final condition states convexity of the finite entropy sequence, expressed
as monotonicity of its successive increments. -/
structure FiniteEntropyConditions (h : ℕ → ℝ) (N : ℕ) : Prop where
  zero : h 0 = 0
  first_nonneg : 0 ≤ entropyIncrement h 0
  increasing : ∀ i j, i ≤ j → j < N →
    entropyIncrement h i ≤ entropyIncrement h j

theorem entropy_increment_nonneg {h : ℕ → ℝ} {N m : ℕ}
    (hc : FiniteEntropyConditions h N) (hm : m < N) :
    0 ≤ entropyIncrement h m :=
  le_trans hc.first_nonneg (hc.increasing 0 m (Nat.zero_le m) hm)

theorem entropy_level_nonneg {h : ℕ → ℝ} {N m : ℕ}
    (hc : FiniteEntropyConditions h N) (hm : m ≤ N) : 0 ≤ h m := by
  have hb := entropy_block_telescope h 0 m 0 (by
    intro j _ hj
    exact entropy_increment_nonneg hc (by omega))
  simpa [hc.zero] using hb

/-- Any following block pays for its first increment. -/
theorem entropy_increment_block {h : ℕ → ℝ} {N m len : ℕ}
    (hc : FiniteEntropyConditions h N) (hblock : m + len ≤ N) :
    (len : ℝ) * entropyIncrement h m ≤ h (m + len) := by
  have hb := entropy_block_telescope h m len (entropyIncrement h m) (by
    intro j hj hj'
    exact hc.increasing m j hj (by omega))
  have hn := entropy_level_nonneg hc (show m ≤ N by omega)
  linarith

/-- The manuscript's low-level bound δ_{m+1} ≤ h_{2m}/m. -/
theorem entropy_increment_low {h : ℕ → ℝ} {N m : ℕ}
    (hc : FiniteEntropyConditions h N) (hm : 0 < m) (h2m : 2 * m ≤ N) :
    entropyIncrement h m ≤ h (2 * m) / (m : ℝ) := by
  have hb := entropy_increment_block (m := m) (len := m) hc (by omega)
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  apply (le_div_iff₀ hmr).2
  have hsum : m + m = 2 * m := by omega
  rw [hsum] at hb
  nlinarith

/-- The manuscript's upper-boundary bound δ_{m+1} ≤ h_N/(N-m). -/
theorem entropy_increment_high {h : ℕ → ℝ} {N m : ℕ}
    (hc : FiniteEntropyConditions h N) (hm : m < N) :
    entropyIncrement h m ≤ h N / ((N - m : ℕ) : ℝ) := by
  have hb := entropy_increment_block (m := m) (len := N - m) hc (by omega)
  have hlen : (0 : ℝ) < ((N - m : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < N - m by omega)
  apply (le_div_iff₀ hlen).2
  simpa [Nat.add_sub_of_le (Nat.le_of_lt hm), mul_comm] using hb

/-- In the lower half of the hierarchy the external coefficient is at most one. -/
theorem external_coefficient_le_one {N m : ℝ} (hN : 0 < N)
    (hm : 0 ≤ m) (hmN : m ≤ N) : ((N - m) / N) ^ 2 ≤ 1 := by
  have hα0 : 0 ≤ (N - m) / N := div_nonneg (sub_nonneg.mpr hmN) hN.le
  have hα1 : (N - m) / N ≤ 1 := by
    apply (div_le_iff₀ hN).2
    linarith
  nlinarith

/-- The coefficient near the upper boundary compensates for the short block. -/
theorem external_source_high_algebra {N m d A : ℝ}
    (hm : 0 ≤ m) (hmN : m ≤ N) (hhalf : N ≤ 2 * m)
    (hA : 0 ≤ A) (hblock : (N - m) * d ≤ A) :
    ((N - m) / N) ^ 2 * m * d ≤ A * m ^ 2 / N ^ 2 := by
  have hr0 : 0 ≤ N - m := sub_nonneg.mpr hmN
  have hrm : N - m ≤ m := by linarith
  calc
    ((N - m) / N) ^ 2 * m * d =
        ((N - m) * m * ((N - m) * d)) / N ^ 2 := by ring
    _ ≤ ((N - m) * m * A) / N ^ 2 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hblock (mul_nonneg hr0 hm)) (sq_nonneg N)
    _ ≤ A * m ^ 2 / N ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg N)
      nlinarith [mul_le_mul_of_nonneg_left hrm (mul_nonneg hA hm)]

/-- A quadratic all-level entropy bound controls every entropy by `A`. -/
theorem quadratic_profile_le_constant {A N m : ℝ}
    (hA : 0 ≤ A) (hN : 0 < N) (hm : 0 ≤ m) (hmN : m ≤ N) :
    A * m ^ 2 / N ^ 2 ≤ A := by
  apply (div_le_iff₀ (sq_pos_of_pos hN)).2
  have hsq : m ^ 2 ≤ N ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hsq hA]

/-- The full external source estimate, including the zero boundary coefficient.

The bound is derived from finite-sequence conditions and the all-level entropy
profile, rather than assumed as an abstract hierarchy conclusion. -/
theorem entropy_external_source_bound {h : ℕ → ℝ} {N m : ℕ} {A : ℝ}
    (hc : FiniteEntropyConditions h N) (hN : 0 < N) (hm : 0 < m)
    (hmN : m ≤ N) (hA : 0 ≤ A)
    (hprofile : ∀ j, j ≤ N → h j ≤ A * (j : ℝ) ^ 2 / (N : ℝ) ^ 2) :
    (((N : ℝ) - m) / N) ^ 2 * m * entropyIncrement h m ≤
      4 * A * (m : ℝ) ^ 2 / (N : ℝ) ^ 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hmr : (0 : ℝ) ≤ m := by positivity
  have hmNr : (m : ℝ) ≤ N := by exact_mod_cast hmN
  have hright : 0 ≤ A * (m : ℝ) ^ 2 / (N : ℝ) ^ 2 := by positivity
  by_cases hend : m = N
  · subst m
    simpa using (show 0 ≤ 4 * A * (N : ℝ) ^ 2 / (N : ℝ) ^ 2 by positivity)
  have hmstrict : m < N := by omega
  by_cases hlow : 2 * m ≤ N
  · have hb := entropy_increment_block (m := m) (len := m) hc (by omega)
    have hp := hprofile (2 * m) hlow
    have hsum : m + m = 2 * m := by omega
    rw [hsum] at hb
    have hbound : (m : ℝ) * entropyIncrement h m ≤
        4 * A * (m : ℝ) ^ 2 / (N : ℝ) ^ 2 := by
      calc
        (m : ℝ) * entropyIncrement h m ≤ h (2 * m) := hb
        _ ≤ A * ((2 * m : ℕ) : ℝ) ^ 2 / (N : ℝ) ^ 2 := hp
        _ = 4 * A * (m : ℝ) ^ 2 / (N : ℝ) ^ 2 := by push_cast; ring
    have hδ := entropy_increment_nonneg hc hmstrict
    have hcoef := external_coefficient_le_one hNr hmr hmNr
    have hmul := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hmr hδ)
    nlinarith
  · have hb := entropy_increment_block (m := m) (len := N - m) hc (by omega)
    have hsum : m + (N - m) = N := by omega
    rw [hsum] at hb
    have hdiff : ((N - m : ℕ) : ℝ) = (N : ℝ) - m := by
      exact Nat.cast_sub hmN
    rw [hdiff] at hb
    have hp := hprofile N (le_refl N)
    have htop : h N ≤ A := le_trans hp
      (quadratic_profile_le_constant hA hNr (by positivity) (le_refl _))
    have hblock : ((N : ℝ) - m) * entropyIncrement h m ≤ A := le_trans hb htop
    have hhalf : (N : ℝ) ≤ 2 * m := by exact_mod_cast (show N ≤ 2 * m by omega)
    have hhigh := external_source_high_algebra hmr hmNr hhalf hA hblock
    calc
      (((N : ℝ) - m) / N) ^ 2 * m * entropyIncrement h m ≤
          A * (m : ℝ) ^ 2 / (N : ℝ) ^ 2 := hhigh
      _ ≤ 4 * (A * (m : ℝ) ^ 2 / (N : ℝ) ^ 2) := by linarith
      _ = 4 * A * (m : ℝ) ^ 2 / (N : ℝ) ^ 2 := by ring

/-- Algebraic final step for the internal bounded-sum estimate. -/
theorem entropy_internal_source_bound {I C A N m h : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hN : 0 < N) (hm : 0 ≤ m) (hmN : m ≤ N)
    (hprofile : h ≤ A * m ^ 2 / N ^ 2)
    (hI : I ≤ C * m ^ 2 / N ^ 2 * (1 + h)) :
    I ≤ C * (1 + A) * m ^ 2 / N ^ 2 := by
  have hh : h ≤ A := le_trans hprofile (quadratic_profile_le_constant hA hN hm hmN)
  have hc : 0 ≤ C * m ^ 2 / N ^ 2 := by positivity
  calc
    I ≤ C * m ^ 2 / N ^ 2 * (1 + h) := hI
    _ ≤ C * m ^ 2 / N ^ 2 * (1 + A) :=
      mul_le_mul_of_nonneg_left (by linarith) hc
    _ = C * (1 + A) * m ^ 2 / N ^ 2 := by ring

/-- Combining squared internal and external velocities incurs a factor two. -/
theorem combine_source_energy_bounds {E I X p C A : ℝ}
    (hE : E ≤ 2 * I + 2 * X)
    (hI : I ≤ C * (1 + A) * p) (hX : X ≤ 4 * C * A * p) :
    E ≤ 2 * C * (1 + 5 * A) * p := by
  nlinarith

/-- Composed numerical source estimate.

The assumptions on `I`, `X`, and `E` are precisely the output inequalities of
the bounded-sum, conditional Pinsker, and squared-velocity steps. This theorem
does not formalize those measure-theoretic arguments. -/
theorem source_energy_from_entropy_profile {h : ℕ → ℝ} {N m : ℕ}
    {A C E I X : ℝ}
    (hc : FiniteEntropyConditions h N) (hN : 0 < N) (hm : 0 < m)
    (hmN : m ≤ N) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hprofile : ∀ j, j ≤ N → h j ≤ A * (j : ℝ) ^ 2 / (N : ℝ) ^ 2)
    (hI : I ≤ C * (m : ℝ) ^ 2 / (N : ℝ) ^ 2 * (1 + h m))
    (hX : X ≤ C * ((((N : ℝ) - m) / N) ^ 2 * m * entropyIncrement h m))
    (hE : E ≤ 2 * I + 2 * X) :
    E ≤ 2 * C * (1 + 5 * A) * (m : ℝ) ^ 2 / (N : ℝ) ^ 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hmNr : (m : ℝ) ≤ N := by exact_mod_cast hmN
  have hi := entropy_internal_source_bound hC hA hNr (show (0 : ℝ) ≤ m by positivity)
    hmNr (hprofile m hmN) hI
  have hx := mul_le_mul_of_nonneg_left
    (entropy_external_source_bound hc hN hm hmN hA hprofile) hC
  have hi' : I ≤ C * (1 + A) * ((m : ℝ) ^ 2 / (N : ℝ) ^ 2) := by
    convert hi using 1
    ring
  have hx' : X ≤ 4 * C * A * ((m : ℝ) ^ 2 / (N : ℝ) ^ 2) := by
    calc
      X ≤ C * ((((N : ℝ) - m) / N) ^ 2 * m * entropyIncrement h m) := hX
      _ ≤ C * (4 * A * (m : ℝ) ^ 2 / (N : ℝ) ^ 2) := hx
      _ = 4 * C * A * ((m : ℝ) ^ 2 / (N : ℝ) ^ 2) := by ring
  have he := combine_source_energy_bounds hE hi' hx'
  convert he using 1
  ring

end SharpWasserstein
