import Mathlib.Analysis.Fourier.AddCircleMulti

/-! Actual mean-square convergence of complex Fourier partial sums on the unit
torus, stated as an integral for later transfer to the real fundamental cube. -/

noncomputable section
namespace SharpWasserstein.TorusFourierConvergence
open MeasureTheory Filter UnitAddTorus
open scoped ENNReal Topology BigOperators InnerProductSpace

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Finite complex Fourier sum using the genuine Haar Fourier coefficients. -/
def series {n : ℕ} (s : Finset (Fin n → ℤ)) (f : C(UnitAddTorus (Fin n), ℂ)) :
    C(UnitAddTorus (Fin n), ℂ) := ∑ k ∈ s, mFourierCoeff f k • mFourier k

/-- The actual continuous Fourier sums converge in the genuine `L²` space. -/
theorem toLp_series_tendsto {n : ℕ} (f : C(UnitAddTorus (Fin n), ℂ)) :
    Tendsto (fun s => (series s f).toLp 2 volume ℂ) atTop (𝓝 (f.toLp 2 volume ℂ)) := by
  have h := hasSum_mFourier_series_L2 (f.toLp 2 volume ℂ)
  simpa only [HasSum, SummationFilter.unconditional_filter, series, map_sum, map_smul, mFourierCoeff_toLp, mFourierLp] using h

/-- The exact `L²` norm is the actual square-integral of a continuous function. -/
theorem norm_toLp_sq {n : ℕ} (f : C(UnitAddTorus (Fin n), ℂ)) :
    ‖f.toLp 2 volume ℂ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp_rw [real_inner_self_eq_norm_sq]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume f] with x hx
  rw [hx]

/-- Fourier mean-square convergence in integral form, without assumed coefficient decay. -/
theorem integral_error_tendsto {n : ℕ} (f : C(UnitAddTorus (Fin n), ℂ)) :
    Tendsto (fun s => ∫ x, ‖series s f x - f x‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
  have h := ((toLp_series_tendsto f).sub (tendsto_const_nhds (x := f.toLp 2 volume ℂ))).norm.pow 2
  simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h
  convert h using 1
  funext s
  rw [← map_sub, norm_toLp_sq]
  rfl

end SharpWasserstein.TorusFourierConvergence
