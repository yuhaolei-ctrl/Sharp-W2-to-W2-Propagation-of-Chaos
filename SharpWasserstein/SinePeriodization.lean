import SharpWasserstein.DriftBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-! Smooth periodic approximation by coordinate sine maps. Unlike wrapping a
cutoff across a seam, this construction is globally smooth from its definition. -/
noncomputable section
open Set Filter
open scoped NNReal Topology
namespace SharpWasserstein.SinePeriodization

def scalar (R x : ℝ) : ℝ := R * Real.sin (x/R)

def coordinates {d : ℕ} (R : ℝ) (x : Position d) : Position d := fun a => scalar R (x a)

def kernel {d : ℕ} (R : ℝ) (b : Position d → Position d → Position d)
    (x y : Position d) : Position d := b (coordinates R x) (coordinates R y)

theorem scalar_contDiff (R : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (scalar R) :=
  contDiff_const.mul (Real.contDiff_sin.comp (contDiff_id.div_const R))

theorem coordinates_contDiff {d : ℕ} (R : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (coordinates (d := d) R) := by
  apply contDiff_pi.mpr
  intro a
  exact (scalar_contDiff R).comp (contDiff_apply ℝ ℝ a)

theorem kernel_contDiff {d : ℕ} (R : ℝ) {b : Position d → Position d → Position d}
    (hb : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry b)) :
    ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (kernel R b)) :=
  hb.comp (((coordinates_contDiff R).comp contDiff_fst).prodMk
    ((coordinates_contDiff R).comp contDiff_snd))

theorem scalar_periodic {R : ℝ} (hR : R ≠ 0) : Function.Periodic (scalar R) (2*Real.pi*R) := by
  intro x
  have he : (x+2*Real.pi*R)/R = x/R+2*Real.pi := by field_simp
  simp only [scalar,he,Real.sin_add_two_pi]

theorem scalar_lipschitz {R : ℝ} (hR : R ≠ 0) : LipschitzWith 1 (scalar R) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq,NNReal.coe_one,one_mul]
  calc
    |scalar R x-scalar R y| = |R| * |Real.sin (x/R)-Real.sin (y/R)| := by rw [scalar,scalar,← mul_sub,abs_mul]
    _ ≤ |R| * |x/R-y/R| := mul_le_mul_of_nonneg_left (Real.abs_sin_sub_sin_le _ _) (abs_nonneg _)
    _ = |x-y| := by rw [← sub_div,abs_div,mul_div_cancel₀ _ (abs_ne_zero.mpr hR)]

theorem coordinates_lipschitz {d : ℕ} {R : ℝ} (hR : R ≠ 0) :
    LipschitzWith 1 (coordinates (d := d) R) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one,one_mul,dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro a
  have he : ‖scalar R (x a)-scalar R (y a)‖ ≤ ‖x a-y a‖ := by
    simpa only [NNReal.coe_one,one_mul,dist_eq_norm] using
      (scalar_lipschitz hR).dist_le_mul (x a) (y a)
  exact he.trans (norm_le_pi_norm (x-y) a)

theorem scalar_error {R : ℝ} (hR : 0 < R) (x : ℝ) :
    |scalar R x-x| ≤ |x|^3/(6*R^2) := by
  have he : scalar R x-x = R*(Real.sin (x/R)-x/R) := by
    dsimp [scalar]
    field_simp
  rw [he,abs_mul,abs_of_pos hR]
  calc
    _ ≤ R*(|x/R|^3/6) := mul_le_mul_of_nonneg_left
      (by simpa only [abs_sub_comm] using Real.abs_sub_sin_le (x/R)) hR.le
    _ = _ := by rw [abs_div,abs_of_pos hR]; field_simp

theorem coordinates_error {d : ℕ} {R A : ℝ} (hR : 0 < R) (hA : 0 ≤ A)
    (x : Position d) (hx : ‖x‖ ≤ A) : ‖coordinates R x-x‖ ≤ A^3/(6*R^2) := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro a
  have ha : |x a| ≤ A := (by simpa only [Real.norm_eq_abs] using (norm_le_pi_norm x a).trans hx)
  exact (scalar_error hR (x a)).trans (div_le_div_of_nonneg_right
    (pow_le_pow_left₀ (abs_nonneg _) ha 3) (by positivity))

theorem kernel_value_bound {d : ℕ} (R : ℝ) {b : Position d → Position d → Position d} {M : ℝ}
    (hb : ∀ x y, ‖b x y‖ ≤ M) (x y : Position d) : ‖kernel R b x y‖ ≤ M :=
  hb _ _

theorem kernel_first_lipschitz {d : ℕ} {R : ℝ} (hR : R ≠ 0)
    {b : Position d → Position d → Position d} {L : ℝ≥0}
    (hb : ∀ y, LipschitzWith L (fun x => b x y)) (y : Position d) :
    LipschitzWith L (fun x => kernel R b x y) := by
  simpa only [mul_one,kernel,Function.comp_def] using (hb (coordinates R y)).comp (coordinates_lipschitz hR)

theorem kernel_second_lipschitz {d : ℕ} {R : ℝ} (hR : R ≠ 0)
    {b : Position d → Position d → Position d} {L : ℝ≥0}
    (hb : ∀ x, LipschitzWith L (b x)) (x : Position d) :
    LipschitzWith L (kernel R b x) := by
  change LipschitzWith L (fun y => kernel R b x y)
  simpa only [mul_one,kernel,Function.comp_def] using (hb (coordinates R x)).comp (coordinates_lipschitz hR)

theorem coordinates_periodic {d : ℕ} {R : ℝ} (hR : R ≠ 0) (a : Fin d)
    (x : Position d) :
    coordinates R (x+Pi.single a (2*Real.pi*R)) = coordinates R x := by
  ext j
  by_cases hj : j = a
  · subst j
    simpa [coordinates] using scalar_periodic hR (x a)
  · simp [coordinates,Pi.single_eq_of_ne hj]

theorem kernel_periodic_first {d : ℕ} {R : ℝ} (hR : R ≠ 0)
    (b : Position d → Position d → Position d) (a : Fin d) (x y : Position d) :
    kernel R b (x+Pi.single a (2*Real.pi*R)) y = kernel R b x y := by
  simp only [kernel,coordinates_periodic hR]

theorem kernel_periodic_second {d : ℕ} {R : ℝ} (hR : R ≠ 0)
    (b : Position d → Position d → Position d) (a : Fin d) (x y : Position d) :
    kernel R b x (y+Pi.single a (2*Real.pi*R)) = kernel R b x y := by
  simp only [kernel,coordinates_periodic hR]

theorem kernel_bounds {d : ℕ} {R M L₁ L₂ : ℝ} (hR : R ≠ 0)
    {b : Position d → Position d → Position d} (hb : BoundedSmoothKernel b)
    (hbound : KernelBounds b M L₁ L₂) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) :
    KernelBounds (kernel R b) M L₁ L₂ := by
  refine ⟨kernel_value_bound R hbound.value, ?_, ?_⟩
  · intro x y
    have hl : ∀ y, LipschitzWith ⟨L₁,hL₁⟩ (fun x => b x y) := by
      intro y
      apply LipschitzWith.of_dist_le_mul
      intro x z
      exact kernel_first_difference hb hbound x z y
    exact norm_fderiv_le_of_lipschitz ℝ (kernel_first_lipschitz hR hl y)
  · intro x y
    have hl : ∀ x, LipschitzWith ⟨L₂,hL₂⟩ (b x) := by
      intro x
      apply LipschitzWith.of_dist_le_mul
      intro y z
      exact kernel_second_difference hb hbound x y z
    exact norm_fderiv_le_of_lipschitz ℝ (kernel_second_lipschitz hR hl x)

theorem kernel_error {d : ℕ} {R A M L₁ L₂ : ℝ} (hR : 0 < R) (hA : 0 ≤ A)
    {b : Position d → Position d → Position d} (hb : BoundedSmoothKernel b)
    (hbound : KernelBounds b M L₁ L₂) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (x y : Position d) (hx : ‖x‖ ≤ A) (hy : ‖y‖ ≤ A) :
    ‖kernel R b x y-b x y‖ ≤ (L₁+L₂)*(A^3/(6*R^2)) := by
  have he := kernel_joint_difference hb hbound (coordinates R x) x (coordinates R y) y
  have h1 := mul_le_mul_of_nonneg_left (coordinates_error hR hA x hx) hL₁
  have h2 := mul_le_mul_of_nonneg_left (coordinates_error hR hA y hy) hL₂
  exact he.trans (by nlinarith)

theorem kernel_uniformOn_ball {d : ℕ} {A M L₁ L₂ : ℝ} (hA : 0 ≤ A)
    {b : Position d → Position d → Position d} (hb : BoundedSmoothKernel b)
    (hbound : KernelBounds b M L₁ L₂) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) :
    TendstoUniformlyOn (fun n : ℕ => Function.uncurry (kernel ((n : ℝ)+1) b))
      (Function.uncurry b) atTop (Metric.ball 0 A) := by
  have hz : Tendsto (fun n : ℕ => ((L₁+L₂)*A^3/6)*(1/((n : ℝ)+1))^2)
      atTop (𝓝 0) := by
    simpa using ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2).const_mul ((L₁+L₂)*A^3/6)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hz.eventually (gt_mem_nhds hε)] with n hn z hz
  have hn0 : 0 < (n : ℝ)+1 := by positivity
  have hzn : ‖z‖ ≤ A := (by simpa only [Metric.mem_ball,dist_zero_right] using hz : ‖z‖ < A).le
  have hx : ‖z.1‖ ≤ A := (norm_fst_le z).trans hzn
  have hy : ‖z.2‖ ≤ A := (norm_snd_le z).trans hzn
  calc
    dist (Function.uncurry b z) (Function.uncurry (kernel ((n : ℝ)+1) b) z) =
        ‖kernel ((n : ℝ)+1) b z.1 z.2-b z.1 z.2‖ := by rw [dist_eq_norm,norm_sub_rev]; rfl
    _ ≤ (L₁+L₂)*(A^3/(6*((n : ℝ)+1)^2)) := kernel_error hn0 hA hb hbound hL₁ hL₂ _ _ hx hy
    _ = ((L₁+L₂)*A^3/6)*(1/((n : ℝ)+1))^2 := by field_simp
    _ < ε := hn

theorem kernel_locallyUniform {d : ℕ} {M L₁ L₂ : ℝ}
    {b : Position d → Position d → Position d} (hb : BoundedSmoothKernel b)
    (hbound : KernelBounds b M L₁ L₂) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) :
    TendstoLocallyUniformly (fun n : ℕ => Function.uncurry (kernel ((n : ℝ)+1) b))
      (Function.uncurry b) atTop := by
  apply tendstoLocallyUniformly_of_forall_exists_nhds
  intro z
  refine ⟨Metric.ball 0 (‖z‖+1), Metric.isOpen_ball.mem_nhds ?_,
    kernel_uniformOn_ball (by positivity) hb hbound hL₁ hL₂⟩
  simp only [Metric.mem_ball,dist_zero_right]
  linarith

end SharpWasserstein.SinePeriodization
