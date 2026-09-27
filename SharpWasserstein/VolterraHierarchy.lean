import SharpWasserstein.CooperativeHierarchy
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FunProp

/-! Sharp quadratic comparison for a finite positive-kernel Volterra hierarchy.
The energy curves themselves are only interval integrable. All differentiation
below concerns the explicit exponential comparison profile, never the energies. -/
noncomputable section
open Set MeasureTheory Real
open scoped Interval
namespace SharpWasserstein.VolterraHierarchy

/-- The explicit comparison profile is continuous for every real parameter. -/
theorem quadraticProfile_continuous (A C a : ℝ) (N m : ℕ) :
    Continuous (quadraticProfile A C a N m) :=
  continuous_iff_continuousAt.mpr
    (fun t => (hasDerivAt_quadraticProfile A C a N m t).continuousAt)

/-- An exact integrating-factor identity for the explicit quadratic profile. -/
theorem quadraticProfile_kernel_identity (A C a α t : ℝ) (N m : ℕ) :
    (∫ r in a..t,exp (α*(t-r))*((4*C-α)*quadraticProfile A C a N m r)) =
      quadraticProfile A C a N m t-
        exp (α*(t-a))*quadraticProfile A C a N m a := by
  have hd (r : ℝ) : HasDerivAt
      (fun u => exp (α*(t-u))*quadraticProfile A C a N m u)
      (exp (α*(t-r))*((4*C-α)*quadraticProfile A C a N m r)) r := by
    have he := (((hasDerivAt_id r).const_sub t).const_mul α).exp
    have hh := he.mul (hasDerivAt_quadraticProfile A C a N m r)
    simp only [id_eq] at hh
    convert hh using 1 <;> first | rfl | ring
  have hc : Continuous (fun r => exp (α*(t-r))*((4*C-α)*quadraticProfile A C a N m r)) :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id))).mul
      (continuous_const.mul (quadraticProfile_continuous A C a N m))
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r _ => hd r) (hc.intervalIntegrable a t)
  simpa only [sub_self,mul_zero,exp_zero,one_mul] using hi

/-- The quadratic profile increases with its level. -/
theorem quadraticProfile_step_nonneg {A C a t : ℝ} {N m : ℕ} (hA : 0 ≤ A) :
    0 ≤ quadraticProfile A C a N (m+1) t-quadraticProfile A C a N m t := by
  have hfactor : 0 ≤ A*exp (4*C*(t-a))/(N:ℝ)^2 := by positivity
  have hstep : 0 ≤ ((m:ℝ)+1)^2-(m:ℝ)^2 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have he : quadraticProfile A C a N (m+1) t-quadraticProfile A C a N m t =
      (A*exp (4*C*(t-a))/(N:ℝ)^2)*(((m:ℝ)+1)^2-(m:ℝ)^2) := by
    simp only [quadraticProfile,Nat.cast_add,Nat.cast_one]
    ring
  rw [he]
  exact mul_nonneg hfactor hstep

/-- The same profile works for every constant rate `0 ≤ q ≤ C*m`. -/
theorem quadraticProfile_rate_supersolution {A C a t q : ℝ} {N m : ℕ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hm : 1 ≤ m) (hq : q ≤ C*m) :
    q*quadraticProfile A C a N (m+1) t ≤
      (4*C-(C-q))*quadraticProfile A C a N m t := by
  have hs := quadraticProfile_supersolution (C := C) (a := a) (t := t) (N := N) hA hC hm
  have hr := mul_le_mul_of_nonneg_right hq
    (quadraticProfile_step_nonneg (C := C) (a := a) (t := t) (N := N) (m := m) hA)
  nlinarith

/-- The genuine positive-kernel integral supersolution. The coefficient `4*C`
is derived from the level algebra and exact integration of the profile. -/
theorem quadraticProfile_volterra_supersolution {A C a t q : ℝ} {N m : ℕ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hm : 1 ≤ m) (hq : q ≤ C*m) (hat : a ≤ t) :
    exp ((C-q)*(t-a))*quadraticProfile A C a N m a+
      q*(∫ r in a..t,exp ((C-q)*(t-r))*quadraticProfile A C a N (m+1) r) ≤
        quadraticProfile A C a N m t := by
  have hc₁ : Continuous (fun r => q*(exp ((C-q)*(t-r))*quadraticProfile A C a N (m+1) r)) :=
    continuous_const.mul ((Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id))).mul
      (quadraticProfile_continuous A C a N (m+1)))
  have hc₂ : Continuous (fun r => exp ((C-q)*(t-r))*((4*C-(C-q))*quadraticProfile A C a N m r)) :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id))).mul
      (continuous_const.mul (quadraticProfile_continuous A C a N m))
  have hi := intervalIntegral.integral_mono_on (μ := volume) hat (hc₁.intervalIntegrable a t)
    (hc₂.intervalIntegrable a t) (fun r _ => ?_)
  · rw [intervalIntegral.integral_const_mul,quadraticProfile_kernel_identity] at hi
    linarith
  · have h := mul_le_mul_of_nonneg_left
      (quadraticProfile_rate_supersolution (a := a) (t := r) (N := N) hA hC hm hq)
      (exp_pos ((C-q)*(t-r))).le
    nlinarith

/-- The top-level exponential bound is dominated by the same profile. -/
theorem quadraticProfile_volterra_boundary {A C a t : ℝ} {N : ℕ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hat : a ≤ t) :
    exp (C*(t-a))*quadraticProfile A C a N N a ≤ quadraticProfile A C a N N t := by
  have he : exp (C*(t-a)) ≤ exp (4*C*(t-a)) := by
    apply exp_le_exp.mpr
    nlinarith [mul_nonneg hC (sub_nonneg.mpr hat)]
  have hfactor : 0 ≤ A*(N:ℝ)^2/(N:ℝ)^2 := by positivity
  have hh := mul_le_mul_of_nonneg_right he hfactor
  rw [quadraticProfile_initial]
  unfold quadraticProfile
  convert hh using 1 <;> first | rfl | ring

/-- Backward induction for the actual integral hierarchy. No sign,
continuity, or differentiability assumption on the energy curves is needed;
interval integrability and the displayed Volterra inequalities suffice. -/
theorem finite_quadratic_bound_variable_rate
    {N : ℕ} (hN : 0 < N) {A C a b : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hab : a ≤ b)
    {E : ℕ → ℝ → ℝ} {q : ℕ → ℝ}
    (hq0 : ∀ m,1 ≤ m → m < N → 0 ≤ q m)
    (hqC : ∀ m,1 ≤ m → m < N → q m ≤ C*m)
    (hEi : ∀ m,1 ≤ m → m ≤ N → IntervalIntegrable (E m) volume a b)
    (hinit : ∀ m,1 ≤ m → m ≤ N → E m a ≤ A*(m:ℝ)^2/(N:ℝ)^2)
    (hE : ∀ m,1 ≤ m → m < N → ∀ t ∈ Icc a b,
      E m t ≤ exp ((C-q m)*(t-a))*E m a+
        q m*(∫ r in a..t,exp ((C-q m)*(t-r))*E (m+1) r))
    (hEN : ∀ t ∈ Icc a b,E N t ≤ exp (C*(t-a))*E N a) :
    ∀ m,1 ≤ m → m ≤ N → ∀ t ∈ Icc a b,
      E m t ≤ A*exp (4*C*(t-a))*(m:ℝ)^2/(N:ℝ)^2 := by
  intro m hm hmN
  change ∀ t ∈ Icc a b,E m t ≤ quadraticProfile A C a N m t
  induction hmN using Nat.decreasingInduction with
  | self =>
      intro t ht
      calc
        E N t ≤ exp (C*(t-a))*E N a := hEN t ht
        _ ≤ exp (C*(t-a))*quadraticProfile A C a N N a :=
          mul_le_mul_of_nonneg_left (by simpa using hinit N hN le_rfl) (exp_pos _).le
        _ ≤ quadraticProfile A C a N N t := quadraticProfile_volterra_boundary hA hC ht.1
  | of_succ m hmN ih =>
      intro t ht
      have hnext := ih (Nat.le_trans hm (Nat.le_succ m))
      have hEi' : IntervalIntegrable (E (m+1)) volume a t :=
        (hEi (m+1) (Nat.le_trans hm (Nat.le_succ m)) hmN).mono_set (by
          rw [uIcc_of_le ht.1,uIcc_of_le hab]
          exact fun r hr => ⟨hr.1,hr.2.trans ht.2⟩)
      have hkernel : Continuous (fun r => exp ((C-q m)*(t-r))) := by fun_prop
      have hprof : Continuous (fun r => exp ((C-q m)*(t-r))*quadraticProfile A C a N (m+1) r) :=
        hkernel.mul (quadraticProfile_continuous A C a N (m+1))
      have hi := intervalIntegral.integral_mono_on ht.1
        (hEi'.continuousOn_mul hkernel.continuousOn) (hprof.intervalIntegrable a t)
        (fun r hr => mul_le_mul_of_nonneg_left
          (hnext r ⟨hr.1,hr.2.trans ht.2⟩) (exp_pos _).le)
      calc
        E m t ≤ exp ((C-q m)*(t-a))*E m a+
            q m*(∫ r in a..t,exp ((C-q m)*(t-r))*E (m+1) r) := hE m hm hmN t ht
        _ ≤ exp ((C-q m)*(t-a))*quadraticProfile A C a N m a+
            q m*(∫ r in a..t,exp ((C-q m)*(t-r))*quadraticProfile A C a N (m+1) r) :=
          add_le_add
            (mul_le_mul_of_nonneg_left (by simpa using hinit m hm hmN.le) (exp_pos _).le)
            (mul_le_mul_of_nonneg_left hi (hq0 m hm hmN))
        _ ≤ quadraticProfile A C a N m t :=
          quadraticProfile_volterra_supersolution hA hC hm (hqC m hm hmN) ht.1

/-- The manuscript's exact rate `C*m`, for merely integrable limiting energies. -/
theorem finite_quadratic_bound
    {N : ℕ} (hN : 0 < N) {A C a b : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hab : a ≤ b)
    {E : ℕ → ℝ → ℝ}
    (hEi : ∀ m,1 ≤ m → m ≤ N → IntervalIntegrable (E m) volume a b)
    (hinit : ∀ m,1 ≤ m → m ≤ N → E m a ≤ A*(m:ℝ)^2/(N:ℝ)^2)
    (hE : ∀ m,1 ≤ m → m < N → ∀ t ∈ Icc a b,
      E m t ≤ exp ((C-C*m)*(t-a))*E m a+
        C*m*(∫ r in a..t,exp ((C-C*m)*(t-r))*E (m+1) r))
    (hEN : ∀ t ∈ Icc a b,E N t ≤ exp (C*(t-a))*E N a) :
    ∀ m,1 ≤ m → m ≤ N → ∀ t ∈ Icc a b,
      E m t ≤ A*exp (4*C*(t-a))*(m:ℝ)^2/(N:ℝ)^2 :=
  finite_quadratic_bound_variable_rate hN hA hC hab
    (fun m _ _ => mul_nonneg hC (Nat.cast_nonneg m)) (fun _ _ _ => le_rfl) hEi hinit hE hEN

end SharpWasserstein.VolterraHierarchy
