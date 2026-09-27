import SharpWasserstein.VolterraFourierLimit

/-! Finite physical Fourier differential inequalities assemble into a genuine
limiting Volterra hierarchy and its sharp quadratic comparison. The finite
inequalities remain an explicit interface; no limiting energy derivative or
limiting hierarchy is assumed. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology Interval
namespace SharpWasserstein.VolterraFourier
open WeightedTangent

/-- Restriction of a genuine integrable interval curve to an initial subinterval. -/
theorem intervalIntegrable_prefix {f : ℝ → ℝ} {a b t : ℝ}
    (hab : a ≤ b) (ht : t ∈ Icc a b) (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable f volume a t :=
  hf.mono_set (by
    rw [uIcc_of_le ht.1,uIcc_of_le hab]
    exact fun r hr => ⟨hr.1,hr.2.trans ht.2⟩)

variable {d N : ℕ} (P : ℝ)
  (μ : (m : ℕ) → ℝ → Measure (Point (m*d))) [∀ m t,IsFiniteMeasure (μ m t)]
  (U : (m : ℕ) → (t : ℝ) → gradientClosure (μ m t))
  {a b C : ℝ} {q K : ℕ → ℝ} {B : ℕ → ℝ → ℝ} {f' : ℕ → ℕ → ℝ → ℝ}

/-- Limit assembly for actual weighted physical Fourier energies, including
scalar integrability and the top level. The error coefficient may have any
sign and depend on the finite particle number and level. -/
theorem hierarchy_of_finite_derivatives (hN : 0 < N) (hab : a ≤ b)
    (hU : ∀ m,1 ≤ m → m ≤ N → ∀ r ∈ Icc a b,
      U m r ∈ WeightedPeriodicFourierPhysical.periodicSpace P (μ m r))
    (hc : ∀ m,1 ≤ m → m ≤ N → ∀ j,ContinuousOn (finiteEnergy P (μ m) (U m) j) (Icc a b))
    (hd : ∀ m,1 ≤ m → m ≤ N → ∀ j r,r ∈ Ioo a b →
      HasDerivAt (finiteEnergy P (μ m) (U m) j) (f' m j r) r)
    (hB : ∀ m,1 ≤ m → m ≤ N → IntervalIntegrable (B m) volume a b)
    (hbound : ∀ m,1 ≤ m → m ≤ N → ∀ r ∈ Icc a b,totalEnergy (μ m) (U m) r ≤ B m r)
    (hfinite : ∀ m,1 ≤ m → m < N → ∀ j r,r ∈ Ioo a b →
      f' m j r ≤ (C-q m)*finiteEnergy P (μ m) (U m) j r+
        q m*totalEnergy (μ (m+1)) (U (m+1)) r+K m*gap P (μ m) (U m) j r)
    (htop : ∀ j r,r ∈ Ioo a b →
      f' N j r ≤ C*finiteEnergy P (μ N) (U N) j r+K N*gap P (μ N) (U N) j r) :
    (∀ m,1 ≤ m → m ≤ N → IntervalIntegrable (totalEnergy (μ m) (U m)) volume a b) ∧
    (∀ m,1 ≤ m → m < N → ∀ t ∈ Icc a b,
      totalEnergy (μ m) (U m) t ≤ Real.exp ((C-q m)*(t-a))*totalEnergy (μ m) (U m) a+
        q m*(∫ r in a..t,Real.exp ((C-q m)*(t-r))*totalEnergy (μ (m+1)) (U (m+1)) r)) ∧
    (∀ t ∈ Icc a b,totalEnergy (μ N) (U N) t ≤
      Real.exp (C*(t-a))*totalEnergy (μ N) (U N) a) := by
  have hEi (m : ℕ) (hm : 1 ≤ m) (hmN : m ≤ N) :
      IntervalIntegrable (totalEnergy (μ m) (U m)) volume a b :=
    totalEnergy_intervalIntegrable P (μ m) (U m) hab (hU m hm hmN) (hc m hm hmN)
      (hB m hm hmN) (hbound m hm hmN)
  refine ⟨hEi,?_,?_⟩
  · intro m hm hmN t ht
    have hh := volterra_bound_of_finite_derivative P (μ m) (U m) ht.1
      (α := C-q m) (K := K m) (g := fun r => q m*totalEnergy (μ (m+1)) (U (m+1)) r)
      (fun r hr => hU m hm hmN.le r ⟨hr.1,hr.2.trans ht.2⟩)
      (fun j => (hc m hm hmN.le j).mono (Icc_subset_Icc_right ht.2))
      (fun j r hr => hd m hm hmN.le j r ⟨hr.1,hr.2.trans_le ht.2⟩)
      ((intervalIntegrable_prefix hab ht (hEi (m+1) (by omega) hmN)).const_mul (q m))
      (intervalIntegrable_prefix hab ht (hB m hm hmN.le))
      (fun r hr => hbound m hm hmN.le r ⟨hr.1,hr.2.trans ht.2⟩)
      (fun j r hr => hfinite m hm hmN j r ⟨hr.1,hr.2.trans_le ht.2⟩)
    have heq : (∫ r in a..t,Real.exp ((C-q m)*(t-r))*
        (q m*totalEnergy (μ (m+1)) (U (m+1)) r)) =
        q m*(∫ r in a..t,Real.exp ((C-q m)*(t-r))*totalEnergy (μ (m+1)) (U (m+1)) r) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro r _
      ring
    rwa [heq] at hh
  · intro t ht
    have hh := volterra_bound_of_finite_derivative P (μ N) (U N) ht.1
      (α := C) (K := K N) (g := fun _ => (0:ℝ))
      (fun r hr => hU N hN le_rfl r ⟨hr.1,hr.2.trans ht.2⟩)
      (fun j => (hc N hN le_rfl j).mono (Icc_subset_Icc_right ht.2))
      (fun j r hr => hd N hN le_rfl j r ⟨hr.1,hr.2.trans_le ht.2⟩)
      (intervalIntegrable_const)
      (intervalIntegrable_prefix hab ht (hB N hN le_rfl))
      (fun r hr => hbound N hN le_rfl r ⟨hr.1,hr.2.trans ht.2⟩)
      (fun j r hr => by simpa only [add_zero] using htop j r ⟨hr.1,hr.2.trans_le ht.2⟩)
    simpa only [mul_zero,intervalIntegral.integral_zero,add_zero] using hh

/-- The sharp quadratic bound follows from actual finite Fourier derivative
inequalities and recovery, with no derivative or Volterra premise for the
limiting weighted energies. -/
theorem quadratic_bound_of_finite_derivatives (hN : 0 < N)
    {A : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hab : a ≤ b)
    (hq0 : ∀ m,1 ≤ m → m < N → 0 ≤ q m)
    (hqC : ∀ m,1 ≤ m → m < N → q m ≤ C*m)
    (hU : ∀ m,1 ≤ m → m ≤ N → ∀ r ∈ Icc a b,
      U m r ∈ WeightedPeriodicFourierPhysical.periodicSpace P (μ m r))
    (hc : ∀ m,1 ≤ m → m ≤ N → ∀ j,ContinuousOn (finiteEnergy P (μ m) (U m) j) (Icc a b))
    (hd : ∀ m,1 ≤ m → m ≤ N → ∀ j r,r ∈ Ioo a b →
      HasDerivAt (finiteEnergy P (μ m) (U m) j) (f' m j r) r)
    (hB : ∀ m,1 ≤ m → m ≤ N → IntervalIntegrable (B m) volume a b)
    (hbound : ∀ m,1 ≤ m → m ≤ N → ∀ r ∈ Icc a b,totalEnergy (μ m) (U m) r ≤ B m r)
    (hfinite : ∀ m,1 ≤ m → m < N → ∀ j r,r ∈ Ioo a b →
      f' m j r ≤ (C-q m)*finiteEnergy P (μ m) (U m) j r+
        q m*totalEnergy (μ (m+1)) (U (m+1)) r+K m*gap P (μ m) (U m) j r)
    (htop : ∀ j r,r ∈ Ioo a b →
      f' N j r ≤ C*finiteEnergy P (μ N) (U N) j r+K N*gap P (μ N) (U N) j r)
    (hinit : ∀ m,1 ≤ m → m ≤ N → totalEnergy (μ m) (U m) a ≤ A*(m:ℝ)^2/(N:ℝ)^2) :
    ∀ m,1 ≤ m → m ≤ N → ∀ t ∈ Icc a b,
      totalEnergy (μ m) (U m) t ≤ A*Real.exp (4*C*(t-a))*(m:ℝ)^2/(N:ℝ)^2 := by
  obtain ⟨hEi,hE,hEN⟩ := hierarchy_of_finite_derivatives P μ U hN hab hU hc hd hB hbound hfinite htop
  exact VolterraHierarchy.finite_quadratic_bound_variable_rate hN hA hC hab hq0 hqC hEi hinit hE hEN

/-- Distinct level-dependent finite baseline coefficients may be bounded by
one comparison constant. This uses nonnegativity of the genuine finite trial
energies, rather than imposing an equality of the analytic coefficients. -/
theorem quadratic_bound_of_finite_derivatives_bounded_coefficients (hN : 0 < N)
    {A : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hab : a ≤ b)
    (D : ℕ → ℝ) (hD : ∀ m,1 ≤ m → m ≤ N → D m ≤ C)
    (hq0 : ∀ m,1 ≤ m → m < N → 0 ≤ q m)
    (hqC : ∀ m,1 ≤ m → m < N → q m ≤ C*m)
    (hU : ∀ m,1 ≤ m → m ≤ N → ∀ r ∈ Icc a b,
      U m r ∈ WeightedPeriodicFourierPhysical.periodicSpace P (μ m r))
    (hc : ∀ m,1 ≤ m → m ≤ N → ∀ j,ContinuousOn (finiteEnergy P (μ m) (U m) j) (Icc a b))
    (hd : ∀ m,1 ≤ m → m ≤ N → ∀ j r,r ∈ Ioo a b →
      HasDerivAt (finiteEnergy P (μ m) (U m) j) (f' m j r) r)
    (hB : ∀ m,1 ≤ m → m ≤ N → IntervalIntegrable (B m) volume a b)
    (hbound : ∀ m,1 ≤ m → m ≤ N → ∀ r ∈ Icc a b,totalEnergy (μ m) (U m) r ≤ B m r)
    (hfinite : ∀ m,1 ≤ m → m < N → ∀ j r,r ∈ Ioo a b →
      f' m j r ≤ (D m-q m)*finiteEnergy P (μ m) (U m) j r+
        q m*totalEnergy (μ (m+1)) (U (m+1)) r+K m*gap P (μ m) (U m) j r)
    (htop : ∀ j r,r ∈ Ioo a b →
      f' N j r ≤ D N*finiteEnergy P (μ N) (U N) j r+K N*gap P (μ N) (U N) j r)
    (hinit : ∀ m,1 ≤ m → m ≤ N → totalEnergy (μ m) (U m) a ≤ A*(m:ℝ)^2/(N:ℝ)^2) :
    ∀ m,1 ≤ m → m ≤ N → ∀ t ∈ Icc a b,
      totalEnergy (μ m) (U m) t ≤ A*Real.exp (4*C*(t-a))*(m:ℝ)^2/(N:ℝ)^2 := by
  apply quadratic_bound_of_finite_derivatives P μ U hN hA hC hab hq0 hqC hU hc hd hB hbound
    (f' := f') (K := K) ?_ ?_ hinit
  · intro m hm hmN j r hr
    have hmul := mul_le_mul_of_nonneg_right
      (sub_le_sub_right (hD m hm hmN.le) (q m)) (finiteEnergy_nonneg P (μ m) (U m) j r)
    linarith [hfinite m hm hmN j r hr]
  · intro j r hr
    have hmul := mul_le_mul_of_nonneg_right
      (hD N hN le_rfl) (finiteEnergy_nonneg P (μ N) (U N) j r)
    linarith [htop j r hr]

end SharpWasserstein.VolterraFourier
