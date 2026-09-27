import SharpWasserstein.SwitchSourceDerivativeShortTime

/-! The synchronous comparison allows the observable itself to vary with
remaining time. Joint continuity of its first spatial differential suffices;
no time derivative or second spatial derivative of the observable is assumed. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal Interval ContDiff
namespace SharpWasserstein.SwitchSourceDerivative
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- The exact first-order line-integral formula for a C¹ real observable. -/
theorem test_sub_eq_integral_fderiv {F : E → ℝ} (hF : ContDiff ℝ 1 F) (x y : E) :
    F x-F y = ∫ u in (0:ℝ)..1,fderiv ℝ F (y+u • (x-y)) (x-y) := by
  have hd (u : ℝ) : HasDerivAt (fun r : ℝ => F (y+r • (x-y)))
      (fderiv ℝ F (y+u • (x-y)) (x-y)) u :=
    ((hF.differentiable (by norm_num)) _).hasFDerivAt.comp_hasDerivAt u
      (by simpa only [one_smul,id_eq] using
        (((hasDerivAt_id u).smul_const (x-y)).const_add y))
  have hc : Continuous (fun u : ℝ => fderiv ℝ F (y+u • (x-y)) (x-y)) :=
    ((hF.continuous_fderiv (by norm_num)).comp
      (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0:ℝ)) (b := 1)
    (fun u _ => hd u) (hc.intervalIntegrable 0 1)
  simpa only [one_smul,zero_smul,add_zero,add_sub_cancel] using he.symm

/-- First-order drift comparison for an actual smoothly varying family of
first differentials, even though the individual trajectories are rough. -/
theorem trajectory_moving_test_difference_hasDerivWithinAt_zero
    {v q : ℝ → E → E} {w X Y : ℝ → E} {x : E} {T : ℝ}
    (hT : 0 ≤ T) (hw : w 0 = 0)
    (hX : FiniteAdditiveTrajectory v w x T X)
    (hY : FiniteAdditiveTrajectory q w x T Y)
    {M A : ℝ≥0} (hv : ∀ r ∈ Icc 0 T, ∀ z, ‖v r z‖ ≤ M)
    (hq : ∀ r ∈ Icc 0 T, ∀ z, ‖q r z‖ ≤ A)
    {F : ℝ → E → ℝ} (hF : ∀ r, ContDiff ℝ 1 (F r))
    (hDF : Continuous (fun p : ℝ × E => fderiv ℝ (F p.1) p.2))
    {L : ℝ≥0} (hL : ∀ r z, ‖fderiv ℝ (F r) z‖ ≤ L) :
    HasDerivWithinAt (fun r => F r (X r)-F r (Y r))
      (fderiv ℝ (F 0) x (v 0 x-q 0 x)) (Icc 0 T) 0 := by
  let l : Filter ℝ := 𝓝[Icc 0 T \ {0}] 0
  have hx := hX.initial hT hw
  have hy := hY.initial hT hw
  have hd : HasDerivWithinAt (fun r => X r-Y r) (v 0 x-q 0 x) (Icc 0 T) 0 := by
    simpa only [hx,hy] using trajectory_difference_hasDerivWithinAt hX hY ⟨le_rfl,hT⟩
  have ha : Tendsto (fun r => r⁻¹ • (X r-Y r)) l (𝓝 (v 0 x-q 0 x)) := by
    have hh := hasDerivWithinAt_iff_tendsto_slope.mp hd
    have he : slope (fun r => X r-Y r) 0 = fun r => r⁻¹ • (X r-Y r) := by
      funext r
      simp only [slope_def_module,hx,hy,sub_self,sub_zero]
    rw [he] at hh
    exact hh
  have hx' : Tendsto X l (𝓝 x) := by
    simpa only [hx] using ((hX.continuous 0 ⟨le_rfl,hT⟩).mono sdiff_subset).tendsto
  have hy' : Tendsto Y l (𝓝 x) := by
    simpa only [hy] using ((hY.continuous 0 ⟨le_rfl,hT⟩).mono sdiff_subset).tendsto
  have hr' : Tendsto (fun r : ℝ => r) l (𝓝 0) := nhdsWithin_le_nhds
  have hint : Tendsto
      (fun r => ∫ u in (0:ℝ)..1,
        fderiv ℝ (F r) (Y r+u • (X r-Y r)) (r⁻¹ • (X r-Y r))) l
      (𝓝 (∫ _u in (0:ℝ)..1,fderiv ℝ (F 0) x (v 0 x-q 0 x))) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (bound := fun _ => (L:ℝ)*(M+A))
    · filter_upwards [] with r
      exact ((((hF r).continuous_fderiv (by norm_num)).comp
        (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with r hr
      filter_upwards [] with u _hu
      have hr0 : r ≠ 0 := hr.2
      have hn := trajectory_difference_norm_le hX hY hv hq hr.1
      have haB : ‖r⁻¹ • (X r-Y r)‖ ≤ (M:ℝ)+A := by
        rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg hr.1.1]
        calc
          r⁻¹*‖X r-Y r‖ ≤ r⁻¹*(((M:ℝ)+A)*r) :=
            mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr hr.1.1)
          _ = _ := by field_simp
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul (hL _ _) haB (norm_nonneg _) L.coe_nonneg)
    · exact intervalIntegrable_const
    · filter_upwards [] with u _hu
      have hz : Tendsto (fun r => Y r+u • (X r-Y r)) l (𝓝 x) := by
        simpa only [sub_self,smul_zero,add_zero] using hy'.add ((hx'.sub hy').const_smul u)
      have hD := hDF.continuousAt.tendsto.comp (hr'.prodMk_nhds hz)
      exact (continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp
        (hD.prodMk_nhds ha)
  have he (r : ℝ) : r⁻¹*(F r (X r)-F r (Y r)) =
      ∫ u in (0:ℝ)..1,fderiv ℝ (F r) (Y r+u • (X r-Y r)) (r⁻¹ • (X r-Y r)) := by
    rw [test_sub_eq_integral_fderiv (hF r),← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u _
    simp only [map_smul,smul_eq_mul]
  apply hasDerivWithinAt_iff_tendsto_slope.mpr
  have heq : slope (fun r => F r (X r)-F r (Y r)) 0 = fun r =>
      ∫ u in (0:ℝ)..1,fderiv ℝ (F r) (Y r+u • (X r-Y r)) (r⁻¹ • (X r-Y r)) := by
    funext r
    simp only [slope_def_module,hx,hy,sub_self,sub_zero,smul_eq_mul]
    exact he r
  rw [heq]
  simpa only [intervalIntegral.integral_const,sub_zero,one_smul] using hint

end SharpWasserstein.SwitchSourceDerivative
