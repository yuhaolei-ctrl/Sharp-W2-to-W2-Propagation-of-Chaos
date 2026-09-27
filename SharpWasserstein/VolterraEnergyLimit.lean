import SharpWasserstein.VolterraHierarchy
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Integrating factors and vanishing-error limits for finite trial energies.
The limiting energy is never differentiated. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology Interval
namespace SharpWasserstein.VolterraEnergyLimit

/-- A finite differentiable trial energy satisfies the actual positive-kernel
integral inequality. The forcing need only be integrable. -/
theorem integrating_factor_bound {f f' g : ℝ → ℝ} {α a t : ℝ} (hat : a ≤ t)
    (hc : ContinuousOn f (Icc a t))
    (hd : ∀ r ∈ Ioo a t,HasDerivAt f (f' r) r)
    (hg : IntervalIntegrable g volume a t)
    (hb : ∀ r ∈ Ioo a t,f' r ≤ α*f r+g r) :
    f t ≤ Real.exp (α*(t-a))*f a+(∫ r in a..t,Real.exp (α*(t-r))*g r) := by
  let w := fun r => Real.exp (α*(t-r))
  have hw : Continuous w := by fun_prop
  have hD (r : ℝ) (hr : r ∈ Ioo a t) : HasDerivAt (fun u => w u*f u)
      (w r*(f' r-α*f r)) r := by
    have he := (((hasDerivAt_id r).const_sub t).const_mul α).exp
    have hh := he.mul (hd r hr)
    simp only [id_eq] at hh
    convert hh using 1 <;> first | rfl | dsimp only [w]; ring
  have hi : IntervalIntegrable (fun r => w r*g r) volume a t :=
    hg.continuousOn_mul hw.continuousOn
  have his : IntegrableOn (fun r => w r*g r) (Icc a t) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hat).mp hi
  have h := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hat
    (hw.continuousOn.mul hc) (fun r hr => (hD r hr).hasDerivWithinAt) his
    (fun r hr => mul_le_mul_of_nonneg_left (by linarith [hb r hr]) (Real.exp_pos _).le)
  change w t*f t-w a*f a ≤ _ at h
  simp only [w,sub_self,mul_zero,Real.exp_zero,one_mul] at h
  linarith

/-- A bounded kernel sends an actual L¹ error to zero. This result needs no
pointwise choice of a tangent vector field. -/
theorem weighted_error_tendsto {e : ℕ → ℝ → ℝ} {w : ℝ → ℝ} {a t B : ℝ}
    (hat : a ≤ t) (he : ∀ j,IntervalIntegrable (e j) volume a t)
    (hB : ∀ r ∈ Icc a t,‖w r‖ ≤ B)
    (hlim : Tendsto (fun j => ∫ r in a..t,‖e j r‖) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ r in a..t,w r*e j r) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _
    (show Tendsto (fun j => B*(∫ r in a..t,‖e j r‖)) atTop (𝓝 0) by
      simpa using hlim.const_mul B)
  intro j
  have hi : IntervalIntegrable (fun r => B*‖e j r‖) volume a t := (he j).norm.const_mul B
  have h := intervalIntegral.norm_integral_le_of_norm_le hat
    (show ∀ᵐ r ∂volume,r ∈ Ioc a t → ‖w r*e j r‖ ≤ B*‖e j r‖ by
      filter_upwards [] with r hr
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hB r ⟨hr.1.le,hr.2⟩) (norm_nonneg _)) hi
  simpa only [intervalIntegral.integral_const_mul] using h

/-- Pass from the proved finite differential inequalities to a limiting
Volterra inequality using genuine L¹ error convergence. No derivative,
absolute continuity, or even continuity of the limit E is required. -/
theorem limit_integrating_factor_bound {f f' err : ℕ → ℝ → ℝ}
    {E g : ℝ → ℝ} {α a t : ℝ} (hat : a ≤ t)
    (hc : ∀ j,ContinuousOn (f j) (Icc a t))
    (hd : ∀ j r,r ∈ Ioo a t → HasDerivAt (f j) (f' j r) r)
    (hg : IntervalIntegrable g volume a t)
    (herr : ∀ j,IntervalIntegrable (err j) volume a t)
    (hb : ∀ j r,r ∈ Ioo a t → f' j r ≤ α*f j r+g r+err j r)
    (hstart : Tendsto (fun j => f j a) atTop (𝓝 (E a)))
    (hend : Tendsto (fun j => f j t) atTop (𝓝 (E t)))
    (herror : Tendsto (fun j => ∫ r in a..t,‖err j r‖) atTop (𝓝 0)) :
    E t ≤ Real.exp (α*(t-a))*E a+(∫ r in a..t,Real.exp (α*(t-r))*g r) := by
  let w := fun r => Real.exp (α*(t-r))
  have hw : Continuous w := by fun_prop
  have hB : ∀ r ∈ Icc a t,‖w r‖ ≤ Real.exp (|α| *(t-a)) := by
    intro r hr
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      α*(t-r) ≤ |α| *(t-r) := mul_le_mul_of_nonneg_right (le_abs_self _) (sub_nonneg.mpr hr.2)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith [hr.1]) (abs_nonneg _)
  have hwe := weighted_error_tendsto hat herr hB herror
  have hbound (j : ℕ) : f j t ≤ Real.exp (α*(t-a))*f j a+
      (∫ r in a..t,w r*g r)+(∫ r in a..t,w r*err j r) := by
    have h := integrating_factor_bound hat (hc j) (hd j) (hg.add (herr j))
      (fun r hr => by simpa only [Pi.add_apply,add_assoc] using hb j r hr)
    have hgi := hg.continuousOn_mul hw.continuousOn
    have hei := (herr j).continuousOn_mul hw.continuousOn
    have heq : (fun r => w r*(g r+err j r)) = fun r => w r*g r+w r*err j r := by
      funext r
      ring
    change f j t ≤ Real.exp (α*(t-a))*f j a+(∫ r in a..t,w r*(g r+err j r)) at h
    rw [heq,intervalIntegral.integral_add hgi hei] at h
    linarith
  have hright := ((hstart.const_mul (Real.exp (α*(t-a)))).add_const
    (∫ r in a..t,w r*g r)).add hwe
  have h := le_of_tendsto_of_tendsto hend hright (Eventually.of_forall hbound)
  simpa only [add_zero] using h

end SharpWasserstein.VolterraEnergyLimit
