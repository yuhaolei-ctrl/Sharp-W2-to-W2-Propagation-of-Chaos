module

public import SharpWasserstein.Compat
public import SharpWasserstein.SinePeriodization
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.Prod

@[expose] public section

/-! Actual first derivatives of the sine periodization converge in operator
norm, also along moving points. This is needed for tangent-source limits,
where convergence of the underlying particle laws alone does not suffice. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators ContDiff
namespace SharpWasserstein.SinePeriodization

theorem scalar_hasDerivAt {R : ℝ} (hR : R ≠ 0) (x : ℝ) :
    HasDerivAt (scalar R) (Real.cos (x/R)) x := by
  have h := (((hasDerivAt_id x).div_const R).sin).const_mul R
  have he : R*(Real.cos (x/R)*(1/R)) = Real.cos (x/R) := by field_simp
  change HasDerivAt (fun y => R*Real.sin (y/R)) (Real.cos (x/R)) x
  convert h using 1 <;> first | rfl | exact he.symm

def coordinateProjection {d : ℕ} (i : Fin d) : Position d →L[ℝ] Position d :=
  (ContinuousLinearMap.single ℝ (fun _ : Fin d => ℝ) i).comp (ContinuousLinearMap.proj i)

def coordinateDerivative {d : ℕ} (R : ℝ) (x : Position d) : Position d →L[ℝ] Position d :=
  ∑ i : Fin d, Real.cos (x i/R) • coordinateProjection i

theorem coordinateDerivative_apply {d : ℕ} (R : ℝ) (x v : Position d) (i : Fin d) :
    coordinateDerivative R x v i = Real.cos (x i/R)*v i := by
  simp [coordinateDerivative,coordinateProjection,Finset.sum_apply,Pi.single_apply]

theorem coordinateProjection_sum {d : ℕ} :
    (∑ i : Fin d, coordinateProjection i) = ContinuousLinearMap.id ℝ (Position d) := by
  ext v i
  simp [coordinateProjection,Finset.sum_apply,Pi.single_apply]

theorem coordinates_hasFDerivAt {d : ℕ} {R : ℝ} (hR : R ≠ 0) (x : Position d) :
    HasFDerivAt (coordinates R) (coordinateDerivative R x) x := by
  have he : coordinateDerivative R x = ContinuousLinearMap.pi
      (fun i : Fin d => Real.cos (x i/R) • ContinuousLinearMap.proj i) := by
    ext v i
    simp [coordinateDerivative_apply]
  rw [he]
  apply hasFDerivAt_pi.mpr
  intro i
  exact (scalar_hasDerivAt hR (x i)).comp_hasFDerivAt x (hasFDerivAt_apply i x)

theorem fderiv_coordinates {d : ℕ} {R : ℝ} (hR : R ≠ 0) (x : Position d) :
    fderiv ℝ (coordinates R) x = coordinateDerivative R x :=
  (coordinates_hasFDerivAt hR x).fderiv

/-- The actual coordinate Jacobian converges in operator norm along any
converging sequence of spatial points. -/
theorem coordinateDerivative_tendsto {d : ℕ} {x : ℕ → Position d} {y : Position d}
    (hx : Tendsto x atTop (𝓝 y)) :
    Tendsto (fun k : ℕ => coordinateDerivative ((k : ℝ)+1) (x k)) atTop
      (𝓝 (ContinuousLinearMap.id ℝ (Position d))) := by
  have h (i : Fin d) : Tendsto (fun k : ℕ => Real.cos (x k i/((k : ℝ)+1))) atTop (𝓝 1) := by
    have hz := Real.continuous_cos.continuousAt.tendsto.comp ((tendsto_pi_nhds.mp hx i).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
    simpa only [Function.comp_def,div_eq_mul_inv,one_div,one_mul,mul_zero,Real.cos_zero] using hz
  have hs := tendsto_finsetSum Finset.univ
    (fun i _ => (h i).smul (tendsto_const_nhds (x := coordinateProjection i)))
  simpa only [coordinateDerivative,one_smul,coordinateProjection_sum] using hs

theorem coordinates_tendsto {d : ℕ} (y : Position d) :
    Tendsto (fun k : ℕ => coordinates ((k : ℝ)+1) y) atTop (𝓝 y) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : Tendsto (fun k : ℕ => (‖y‖^3/6)*(1/((k : ℝ)+1))^2) atTop (𝓝 0) := by
    simpa using ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2).const_mul (‖y‖^3/6)
  apply squeeze_zero (fun _ => norm_nonneg _) _ hb
  intro k
  have h := coordinates_error (R := (k : ℝ)+1) (by positivity) (norm_nonneg y) y le_rfl
  convert h using 1
  field_simp

theorem coordinates_moving_tendsto {d : ℕ} {x : ℕ → Position d} {y : Position d}
    (hx : Tendsto x atTop (𝓝 y)) :
    Tendsto (fun k : ℕ => coordinates ((k : ℝ)+1) (x k)) atTop (𝓝 y) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h₁ : Tendsto (fun k => ‖x k-y‖) atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.mp hx
  have h₂ := tendsto_iff_norm_sub_tendsto_zero.mp (coordinates_tendsto y)
  have hs := h₁.add h₂
  rw [zero_add] at hs
  apply squeeze_zero (fun _ => norm_nonneg _) _ hs
  intro k
  calc
    ‖coordinates ((k : ℝ)+1) (x k)-y‖ ≤ ‖coordinates ((k : ℝ)+1) (x k)-coordinates ((k : ℝ)+1) y‖ +
        ‖coordinates ((k : ℝ)+1) y-y‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖x k-y‖+‖coordinates ((k : ℝ)+1) y-y‖ := add_le_add
      (by simpa using (coordinates_lipschitz (d := d) (R := (k : ℝ)+1) (by positivity)).norm_sub_le (x k) y) le_rfl

/-- Exact chain rule for the actual periodized interaction kernel. -/
theorem fderiv_kernel {d : ℕ} {R : ℝ} (hR : R ≠ 0)
    {b : Position d → Position d → Position d}
    (hb : ContDiff ℝ 1 (Function.uncurry b)) (x y : Position d) :
    fderiv ℝ (Function.uncurry (kernel R b)) (x,y) =
      (fderiv ℝ (Function.uncurry b) (coordinates R x,coordinates R y)).comp
        ((coordinateDerivative R x).prodMap (coordinateDerivative R y)) := by
  have hp := HasFDerivAt.prodMap (x,y) (coordinates_hasFDerivAt hR x) (coordinates_hasFDerivAt hR y)
  exact ((hb.differentiable (by norm_num) _).hasFDerivAt.comp (x,y) hp).fderiv

/-- Actual kernel Jacobians converge in operator norm at moving points;
the conclusion is stronger than convergence of kernel values. -/
theorem fderiv_kernel_moving_tendsto {d : ℕ}
    {b : Position d → Position d → Position d}
    (hb : ContDiff ℝ 1 (Function.uncurry b))
    {x y : ℕ → Position d} {a c : Position d}
    (hx : Tendsto x atTop (𝓝 a)) (hy : Tendsto y atTop (𝓝 c)) :
    Tendsto (fun k : ℕ => fderiv ℝ (Function.uncurry (kernel ((k : ℝ)+1) b)) (x k,y k))
      atTop (𝓝 (fderiv ℝ (Function.uncurry b) (a,c))) := by
  have hz := (coordinates_moving_tendsto hx).prodMk_nhds (coordinates_moving_tendsto hy)
  have hd := (hb.continuous_fderiv (by norm_num)).continuousAt.tendsto.comp hz
  have hp := (ContinuousLinearMap.prodMapL ℝ (Position d) (Position d) (Position d) (Position d)).continuous.continuousAt.tendsto.comp
    ((coordinateDerivative_tendsto hx).prodMk_nhds (coordinateDerivative_tendsto hy))
  have he : (ContinuousLinearMap.id ℝ (Position d)).prodMap
      (ContinuousLinearMap.id ℝ (Position d)) = ContinuousLinearMap.id ℝ (Position d × Position d) := by
    ext p <;> rfl
  simp only [Function.comp_def,ContinuousLinearMap.prodMapL_apply,he] at hp
  have hc : Continuous (fun p : ((Position d × Position d) →L[ℝ] Position d) ×
      ((Position d × Position d) →L[ℝ] (Position d × Position d)) => p.1.comp p.2) :=
    continuous_fst.clm_comp continuous_snd
  have h := hc.continuousAt.tendsto.comp (hd.prodMk_nhds hp)
  simp only [Function.comp_def,ContinuousLinearMap.comp_id] at h
  have heq (k : ℕ) := fderiv_kernel (R := (k : ℝ)+1) (by positivity) hb (x k) (y k)
  simp_rw [heq]
  exact h

end SharpWasserstein.SinePeriodization
