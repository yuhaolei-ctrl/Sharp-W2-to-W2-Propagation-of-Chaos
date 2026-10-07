module

public import SharpWasserstein.Compat
public import SharpWasserstein.RoughEulerianTimeSmoothing
public import SharpWasserstein.SmoothCutoff
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Group.Integral

@[expose] public section

/-! A concrete normalized compact smooth time kernel. Its value and derivative
bounds, support, and interior-window normalization are all proved. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval ContDiff
namespace SharpWasserstein.RoughEulerianTime

def timeBump (ε : ℝ) (hε : 0 < ε) : ContDiffBump (0 : ℝ) :=
  ⟨ε/2,ε,by positivity,by linarith⟩

def timeKernel (ε : ℝ) (hε : 0 < ε) : ℝ → ℝ := (timeBump ε hε).normed volume

theorem timeKernel_nonneg {ε : ℝ} (hε : 0 < ε) (r : ℝ) : 0 ≤ timeKernel ε hε r :=
  (timeBump ε hε).nonneg_normed r

theorem timeKernel_smooth {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ ∞ (timeKernel ε hε) :=
  (timeBump ε hε).contDiff_normed

theorem timeKernel_compact {ε : ℝ} (hε : 0 < ε) : HasCompactSupport (timeKernel ε hε) :=
  (timeBump ε hε).hasCompactSupport_normed

theorem timeKernel_integrable {ε : ℝ} (hε : 0 < ε) : Integrable (timeKernel ε hε) :=
  (timeBump ε hε).integrable_normed

theorem timeKernel_integral {ε : ℝ} (hε : 0 < ε) : (∫ r, timeKernel ε hε r) = 1 :=
  (timeBump ε hε).integral_normed

theorem timeKernel_neg {ε : ℝ} (hε : 0 < ε) (r : ℝ) : timeKernel ε hε (-r) = timeKernel ε hε r :=
  (timeBump ε hε).normed_neg r

theorem timeKernel_eq_zero {ε r : ℝ} (hε : 0 < ε) (hr : ε ≤ |r|) : timeKernel ε hε r = 0 := by
  unfold timeKernel ContDiffBump.normed
  rw [(timeBump ε hε).zero_of_le_dist (by simpa [timeBump, dist_zero_right, Real.norm_eq_abs] using hr)]
  exact zero_div _

theorem timeKernel_hasDerivAt {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    HasDerivAt (timeKernel ε hε) (deriv (timeKernel ε hε) r) r :=
  ((timeKernel_smooth hε).differentiable (by simp) r).hasDerivAt

theorem timeKernel_deriv_continuous {ε : ℝ} (hε : 0 < ε) : Continuous (deriv (timeKernel ε hε)) :=
  (timeKernel_smooth hε).continuous_deriv (by simp)

theorem timeKernel_bounds {ε : ℝ} (hε : 0 < ε) :
    ∃ C D : ℝ, (∀ r, ‖timeKernel ε hε r‖ ≤ C) ∧ ∀ r, ‖deriv (timeKernel ε hε) r‖ ≤ D := by
  obtain ⟨C,hC⟩ := (timeKernel_compact hε).exists_bound_of_continuous (timeKernel_smooth hε).continuous
  obtain ⟨D,hD⟩ := (timeKernel_compact hε).deriv.exists_bound_of_continuous (timeKernel_deriv_continuous hε)
  exact ⟨C,D,hC,hD⟩

theorem timeKernel_window_normalization {ε a b t : ℝ} (hε : 0 < ε)
    (ha : a+ε ≤ t) (hb : t+ε ≤ b) : (∫ s in Icc a b, timeKernel ε hε (t-s)) = 1 := by
  have hz (s : ℝ) (hs : s ∉ Icc a b) : timeKernel ε hε (t-s) = 0 := by
    have hs' : s < a ∨ b < s := by simpa only [mem_Icc, not_and_or, not_le] using hs
    apply timeKernel_eq_zero hε
    rcases hs' with hs' | hs'
    · exact (by linarith : ε ≤ t-s).trans (le_abs_self _)
    · exact (by linarith : ε ≤ -(t-s)).trans (neg_le_abs _)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  have he (s : ℝ) : timeKernel ε hε (t-s) = timeKernel ε hε (s-t) := by
    rw [← neg_sub s t, timeKernel_neg hε]
  simp_rw [he]
  rw [integral_sub_right_eq_self, timeKernel_integral hε]

/-- For interior times, the actual compact time mollifier changes the weak
integral equation into a genuine classical derivative with its original sign. -/
theorem timeKernel_hasDerivAt_source {ε a b t : ℝ} (hε : 0 < ε)
    (ha : a+ε ≤ t) (hb : t+ε ≤ b) {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hg : IntegrableOn g (Icc a b))
    (heq : ∀ s ∈ Icc a b, f s-f a = ∫ r in a..s, g r) :
    HasDerivAt (timeConvolution (timeKernel ε hε) a b f)
      (timeConvolution (timeKernel ε hε) a b g t) t := by
  obtain ⟨C,D,hC,hD⟩ := timeKernel_bounds hε
  apply timeConvolution_hasDerivAt_source (by linarith) hf hg heq
    (timeKernel_hasDerivAt hε) (timeKernel_deriv_continuous hε) hC hD
  · exact timeKernel_eq_zero hε ((by linarith : ε ≤ t-a).trans (le_abs_self _))
  · exact timeKernel_eq_zero hε ((by linarith : ε ≤ -(t-b)).trans (neg_le_abs _))

end SharpWasserstein.RoughEulerianTime
