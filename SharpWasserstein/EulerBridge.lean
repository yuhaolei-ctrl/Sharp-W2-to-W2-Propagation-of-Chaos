import SharpWasserstein.ControlledBridge
import SharpWasserstein.EulerConvergence

/-! Exact deterministic conjugacy of Euler schemes under the linear meeting
bridge. This identifies the controlled endpoint with the uncontrolled endpoint
from the other initial point; it does not assume a change of measure. -/

noncomputable section
open Set
open scoped NNReal

namespace SharpWasserstein.EulerBridge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def shiftedDrift (v : ℝ → E → E) (x y : E) (T : ℝ) : ℝ → E → E :=
  fun t z => v t (z+(1-t/T) • (y-x)) + T⁻¹ • (y-x)

theorem shiftedDrift_continuous {v : ℝ → E → E} (x y : E) (T : ℝ)
    (hv : Continuous (Function.uncurry v)) :
    Continuous (Function.uncurry (shiftedDrift v x y T)) := by
  unfold shiftedDrift Function.uncurry
  exact (hv.comp (continuous_fst.prodMk
    (continuous_snd.add (by fun_prop)))).add continuous_const

theorem shiftedDrift_lipschitz {v : ℝ → E → E} (x y : E) (T : ℝ)
    {K : ℝ≥0} (hv : ∀ t, LipschitzWith K (v t)) (t : ℝ) :
    LipschitzWith K (shiftedDrift v x y T t) := by
  apply LipschitzWith.of_dist_le_mul
  intro z z'
  simpa only [shiftedDrift, dist_add_right] using (hv t).dist_le_mul
    (z+(1-t/T) • (y-x)) (z'+(1-t/T) • (y-x))

theorem shiftedDrift_norm_le {v : ℝ → E → E} (x y : E) {T M : ℝ}
    (hT : 0 < T) (hb : ∀ t z, ‖v t z‖ ≤ M) (t : ℝ) (z : E) :
    ‖shiftedDrift v x y T t z‖ ≤ M + T⁻¹ * ‖y-x‖ := by
  unfold shiftedDrift
  exact (norm_add_le _ _).trans (add_le_add (hb _ _) (by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hT)]))

theorem nodes_conjugacy (v : ℝ → E → E) (x y : E) (w : ℝ → E) (T δ : ℝ) (n : ℕ) :
    Euler.nodes (shiftedDrift v x y T) x w δ n + (1-(n : ℝ)*δ/T) • (y-x) =
      Euler.nodes v y w δ n := by
  induction n with
  | zero => simp [Euler.nodes]; abel
  | succ n ih =>
    simp only [Euler.nodes, shiftedDrift, Nat.cast_add, Nat.cast_one]
    rw [ih, smul_add]
    have ha : δ • (T⁻¹ • (y-x)) + (1-((n : ℝ)+1)*δ/T) • (y-x) =
        (1-(n : ℝ)*δ/T) • (y-x) := by
      rw [smul_smul, ← add_smul]
      congr 1
      ring
    calc
      _ = (Euler.nodes (shiftedDrift v x y T) x w δ n + (1-(n : ℝ)*δ/T) • (y-x)) +
          δ • v ((n : ℝ)*δ) (Euler.nodes v y w δ n) + (w (((n : ℝ)+1)*δ)-w ((n : ℝ)*δ)) := by
        rw [← ha]
        abel
      _ = _ := by rw [ih]

theorem endpoint_conjugacy (v : ℝ → E → E) (x y : E) (w : ℝ → E)
    {T : ℝ} (hT : 0 < T) (n : ℕ) :
    Euler.nodes (shiftedDrift v x y T) x w (T/(n+1)) (n+1) =
      Euler.nodes v y w (T/(n+1)) (n+1) := by
  have h := nodes_conjugacy v x y w T (T/(n+1)) (n+1)
  have hn : (0 : ℝ) < (n : ℝ)+1 := by positivity
  have ht : ((n+1 : ℕ) : ℝ) * (T/((n : ℝ)+1)) / T = 1 := by
    push_cast
    field_simp
  simpa only [ht, sub_self, zero_smul, add_zero] using h

end SharpWasserstein.EulerBridge
