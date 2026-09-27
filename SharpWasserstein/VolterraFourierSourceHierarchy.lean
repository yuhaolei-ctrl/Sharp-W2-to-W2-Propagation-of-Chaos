import SharpWasserstein.VolterraFourierSource

/-! The actual periodic variational source hierarchy is obtained from finite
physical Fourier trial inequalities. Only full source finiteness, a coarse
integrable full-energy domination, and the initial full-energy profile are
used; no limiting hierarchy or limiting derivative is supplied. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology Interval
namespace SharpWasserstein.VolterraFourier
open WeightedTangent

/-- Concrete source-level assembly. The analytic finite inequality has the
exact `D*e + q*(E_next-e) + K*(E-e)` shape. Actual recovery removes the final
gap, positive-kernel comparison then yields the sharp quadratic profile. -/
theorem source_quadratic_bound_of_finite_derivatives {d N : ℕ}
    (P : ℝ) (μ : (m : ℕ) → ℝ → Measure (Point (m*d))) [∀ m t,IsFiniteMeasure (μ m t)]
    (σ : (m : ℕ) → ℝ → (Test (m*d) →ₗ[ℝ] ℝ))
    (hN : 0 < N) {a b A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hab : a ≤ b)
    (D q K : ℕ → ℝ) (hD : ∀ m,1 ≤ m → m ≤ N → D m ≤ C)
    (hq0 : ∀ m,1 ≤ m → m < N → 0 ≤ q m)
    (hqC : ∀ m,1 ≤ m → m < N → q m ≤ C*m)
    (hσ : ∀ m,1 ≤ m → m ≤ N → ∀ r ∈ Icc a b,FiniteEnergy (μ m r) (σ m r))
    (hc : ∀ m,1 ≤ m → m ≤ N → ∀ j,
      ContinuousOn (sourceFiniteEnergy P (μ m) (σ m) j) (Icc a b))
    {f' : ℕ → ℕ → ℝ → ℝ}
    (hd : ∀ m,1 ≤ m → m ≤ N → ∀ j r,r ∈ Ioo a b →
      HasDerivAt (sourceFiniteEnergy P (μ m) (σ m) j) (f' m j r) r)
    {B : ℕ → ℝ → ℝ}
    (hB : ∀ m,1 ≤ m → m ≤ N → IntervalIntegrable (B m) volume a b)
    (hbound : ∀ m,1 ≤ m → m ≤ N → ∀ r ∈ Icc a b,
      WeightedTangent.energy (μ m r) (σ m r) ≤ B m r)
    (hfinite : ∀ m,1 ≤ m → m < N → ∀ j r,r ∈ Ioo a b →
      f' m j r ≤ D m*sourceFiniteEnergy P (μ m) (σ m) j r+
        q m*(WeightedPeriodicTangentPhysical.energy P (μ (m+1) r) (σ (m+1) r)-
          sourceFiniteEnergy P (μ m) (σ m) j r)+
        K m*(WeightedPeriodicTangentPhysical.energy P (μ m r) (σ m r)-
          sourceFiniteEnergy P (μ m) (σ m) j r))
    (htop : ∀ j r,r ∈ Ioo a b →
      f' N j r ≤ D N*sourceFiniteEnergy P (μ N) (σ N) j r+
        K N*(WeightedPeriodicTangentPhysical.energy P (μ N r) (σ N r)-
          sourceFiniteEnergy P (μ N) (σ N) j r))
    (hinit : ∀ m,1 ≤ m → m ≤ N →
      WeightedTangent.energy (μ m a) (σ m a) ≤ A*(m:ℝ)^2/(N:ℝ)^2) :
    ∀ m,1 ≤ m → m ≤ N → ∀ t ∈ Icc a b,
      WeightedPeriodicTangentPhysical.energy P (μ m t) (σ m t) ≤
        A*Real.exp (4*C*(t-a))*(m:ℝ)^2/(N:ℝ)^2 := by
  have hh := quadratic_bound_of_finite_derivatives_bounded_coefficients P μ
    (fun m => sourceRepresentative P (μ m) (σ m)) hN hA hC hab D hD hq0 hqC
    (fun m _ _ r _ => sourceRepresentative_mem P (μ m) (σ m) r)
    hc hd hB
    (show ∀ m,1 ≤ m → m ≤ N → ∀ r ∈ Icc a b,
      totalEnergy (μ m) (sourceRepresentative P (μ m) (σ m)) r ≤ B m r by
      intro m hm hmN r hr
      rw [totalEnergy_sourceRepresentative]
      exact (WeightedPeriodicTangentPhysical.energy_le_full P (μ m r) (σ m r)
        (hσ m hm hmN r hr)).trans (hbound m hm hmN r hr))
    (K := K) (show ∀ m,1 ≤ m → m < N → ∀ j r,r ∈ Ioo a b →
      f' m j r ≤ (D m-q m)*finiteEnergy P (μ m) (sourceRepresentative P (μ m) (σ m)) j r+
        q m*totalEnergy (μ (m+1)) (sourceRepresentative P (μ (m+1)) (σ (m+1))) r+
        K m*gap P (μ m) (sourceRepresentative P (μ m) (σ m)) j r by
      intro m hm hmN j r hr
      have h := hfinite m hm hmN j r hr
      simp only [gap,totalEnergy_sourceRepresentative,sourceFiniteEnergy] at h ⊢
      convert h using 1
      ring)
    (show ∀ j r,r ∈ Ioo a b →
      f' N j r ≤ D N*finiteEnergy P (μ N) (sourceRepresentative P (μ N) (σ N)) j r+
        K N*gap P (μ N) (sourceRepresentative P (μ N) (σ N)) j r by
      intro j r hr
      simpa only [gap,totalEnergy_sourceRepresentative,sourceFiniteEnergy] using htop j r hr)
    (show ∀ m,1 ≤ m → m ≤ N →
      totalEnergy (μ m) (sourceRepresentative P (μ m) (σ m)) a ≤ A*(m:ℝ)^2/(N:ℝ)^2 by
      intro m hm hmN
      rw [totalEnergy_sourceRepresentative]
      exact (WeightedPeriodicTangentPhysical.energy_le_full P (μ m a) (σ m a)
        (hσ m hm hmN a ⟨le_rfl,hab⟩)).trans (hinit m hm hmN))
  simpa only [totalEnergy_sourceRepresentative] using hh

end SharpWasserstein.VolterraFourier
