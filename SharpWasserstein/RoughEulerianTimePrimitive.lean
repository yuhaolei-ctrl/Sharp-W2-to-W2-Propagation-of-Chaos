import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! Fubini and integration by parts for genuine L¹ time primitives. These
identities regularize an integrated weak continuity equation without assuming
that its rough source has a derivative at every time. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
namespace SharpWasserstein.RoughEulerianTime

/-- Swap the triangular integral defining an L¹ primitive. Both original
scalar fields are only integrable; no pointwise differentiability is used. -/
theorem integral_primitive_swap {a b : ℝ} {g h : ℝ → ℝ}
    (hg : IntegrableOn g (Icc a b)) (hh : IntegrableOn h (Icc a b)) :
    (∫ s in Icc a b, h s * ∫ r in Icc a s, g r) =
      ∫ r in Icc a b, (∫ s in Icc r b, h s) * g r := by
  let Q : ℝ × ℝ → ℝ := {p : ℝ × ℝ | p.2 ≤ p.1}.indicator (fun p => h p.1*g p.2)
  have hi : Integrable Q ((volume.restrict (Icc a b)).prod (volume.restrict (Icc a b))) :=
    (hh.mul_prod hg).indicator (isClosed_le continuous_snd continuous_fst).measurableSet
  have hL (s : ℝ) (hs : s ∈ Icc a b) :
      (∫ r in Icc a b, Q (s,r)) = h s * ∫ r in Icc a s, g r := by
    have he : Iic s ∩ Icc a b = Icc a s := by
      ext r
      simp only [mem_inter_iff, mem_Iic, mem_Icc]
      constructor
      · exact fun hr => ⟨hr.2.1,hr.1⟩
      · exact fun hr => ⟨hr.2,hr.1,hr.2.trans hs.2⟩
    change (∫ r in Icc a b, (Iic s).indicator (fun r => h s*g r) r) = _
    rw [integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic, he,
      integral_const_mul]
  have hR (r : ℝ) (hr : r ∈ Icc a b) :
      (∫ s in Icc a b, Q (s,r)) = (∫ s in Icc r b, h s) * g r := by
    have he : Ici r ∩ Icc a b = Icc r b := by
      ext s
      simp only [mem_inter_iff, mem_Ici, mem_Icc]
      constructor
      · exact fun hs => ⟨hs.1,hs.2.2⟩
      · exact fun hs => ⟨hs.1,hr.1.trans hs.1,hs.2⟩
    change (∫ s in Icc a b, (Ici r).indicator (fun s => h s*g r) s) = _
    rw [integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici, he,
      integral_mul_const]
  calc
    _ = ∫ s in Icc a b, ∫ r in Icc a b, Q (s,r) :=
      setIntegral_congr_fun measurableSet_Icc (fun s hs => (hL s hs).symm)
    _ = ∫ r in Icc a b, ∫ s in Icc a b, Q (s,r) := integral_integral_swap hi
    _ = _ := setIntegral_congr_fun measurableSet_Icc hR

/-- Integration by parts for an actual L¹ primitive and a C¹ multiplier,
derived from triangular Fubini rather than a pointwise derivative of the primitive. -/
theorem integral_derivative_mul_primitive {a b : ℝ} {g H H' : ℝ → ℝ}
    (hg : IntegrableOn g (Icc a b)) (hH : ∀ s, HasDerivAt H (H' s) s) (hH' : Continuous H') :
    (∫ s in Icc a b, H' s * ∫ r in Icc a s, g r) =
      H b * (∫ r in Icc a b, g r) - ∫ r in Icc a b, H r * g r := by
  have hHc : Continuous H := continuous_iff_continuousAt.mpr (fun s => (hH s).continuousAt)
  have hHg : IntegrableOn (fun r => H r*g r) (Icc a b) :=
    IntegrableOn.continuousOn_mul hHc.continuousOn hg isCompact_Icc
  rw [integral_primitive_swap hg hH'.integrableOn_Icc]
  have hinner (r : ℝ) (hr : r ∈ Icc a b) : (∫ s in Icc r b, H' s) = H b-H r := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hr.2]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hH s) (hH'.intervalIntegrable r b)
  calc
    _ = ∫ r in Icc a b, (H b-H r)*g r :=
      setIntegral_congr_fun measurableSet_Icc (fun r hr => by rw [hinner r hr])
    _ = _ := by
      simp_rw [sub_mul]
      rw [integral_sub (hg.const_mul (H b)) hHg, integral_const_mul]

/-- A continuous curve satisfying the original integrated equation can be
integrated by parts against smooth time multipliers, with only L¹ source data. -/
theorem integral_derivative_mul_weak_curve {a b : ℝ} (hab : a ≤ b) {f g H H' : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hg : IntegrableOn g (Icc a b))
    (heq : ∀ s ∈ Icc a b, f s-f a = ∫ r in a..s, g r)
    (hH : ∀ s, HasDerivAt H (H' s) s) (hH' : Continuous H') :
    (∫ s in Icc a b, H' s*f s) = H b*f b-H a*f a-∫ s in Icc a b, H s*g s := by
  have hp (s : ℝ) (hs : s ∈ Icc a b) : (∫ r in Icc a s, g r) = f s-f a := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs.1]
    exact (heq s hs).symm
  have hh := integral_derivative_mul_primitive hg hH hH'
  have hleft : (∫ s in Icc a b, H' s * ∫ r in Icc a s, g r) =
      (∫ s in Icc a b, H' s*f s) - (∫ s in Icc a b, H' s)*f a := by
    calc
      _ = ∫ s in Icc a b, H' s*(f s-f a) :=
        setIntegral_congr_fun measurableSet_Icc (fun s hs => by rw [hp s hs])
      _ = _ := by
        simp_rw [mul_sub]
        have hprod : IntegrableOn (fun s => H' s*f s) (Icc a b) :=
          (hH'.continuousOn.mul hf).integrableOn_Icc
        rw [integral_sub hprod
          (hH'.integrableOn_Icc.mul_const (f a)), integral_mul_const]
  have hderiv : (∫ s in Icc a b, H' s) = H b-H a := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hH s) (hH'.intervalIntegrable a b)
  rw [hleft, hderiv, hp b ⟨hab,le_rfl⟩] at hh
  linarith

end SharpWasserstein.RoughEulerianTime
