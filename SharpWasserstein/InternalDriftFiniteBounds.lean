module

public import SharpWasserstein.Compat
public import SharpWasserstein.ExternalInteractionPeriodic
public import SharpWasserstein.EuclideanFlow
public import SharpWasserstein.ParticleWeakIdentification
public import SharpWasserstein.PropagatedSourceEquation

@[expose] public section

/-! The finite hierarchy's actual internal drift is a scaled genuine
m-particle drift. Its Euclidean Jacobian bound is independent of N and m
when m ≤ N, while auxiliary all-derivative bounds remain finite. -/
noncomputable section
open scoped ContDiff NNReal BigOperators
namespace SharpWasserstein.ExternalInteractionPeriodic
open WeightedTangent NoiseAverage PropagatedSourceEquation
variable {d m N : ℕ}

theorem internalDrift_eq_scaled {b : Position d → Position d → Position d}
    (hm : 0 < m) : internalDrift (m := m) N b =
      fun x => ((m:ℝ)/(N:ℝ)) • configurationEuclidean d m
        (particleDrift b ((configurationEuclidean d m).symm x)) := by
  funext x
  rw [← map_smul]
  unfold internalDrift
  apply congrArg (configurationEuclidean d m)
  ext i r
  simp only [particleDrift,Pi.smul_apply,smul_eq_mul]
  have hm' : (m:ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hm)
  field_simp

/-- Higher derivatives have actual global finite bounds; no such bound will
enter the limiting hierarchy coefficient. -/
theorem internalDrift_allDerivativesBounded {b : Position d → Position d → Position d}
    (hb : BoundedSmoothKernel b) (hm : 0 < m) :
    AllDerivativesBounded (internalDrift (m := m) N b) := by
  rw [internalDrift_eq_scaled hm]
  exact (equivDrift_allDerivativesBounded (configurationEuclidean d m)
    (particleDrift_smooth hb) (particleDrift_allDerivativesBounded hb)).const_smul
    (equivDrift_smooth _ (particleDrift_smooth hb)) _

theorem internalDrift_lipschitz {b : Position d → Position d → Position d}
    {M L₁ L₂ : ℝ} (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
    (hm : 0 < m) (hmN : m ≤ N) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) :
    LipschitzWith ⟨Real.sqrt (2*(d:ℝ)*(L₁^2+L₂^2)),Real.sqrt_nonneg _⟩
      (internalDrift (m := m) N b) := by
  have hN : (0:ℝ)<N := Nat.cast_pos.mpr (lt_of_lt_of_le hm hmN)
  have hs : |(m:ℝ)/(N:ℝ)| ≤ 1 := by
    rw [abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hN.le)]
    exact (div_le_one hN).mpr (Nat.cast_le.mpr hmN)
  have hp := euclidean_particleDrift_lipschitz hm hb hbound hL₁ hL₂
  rw [internalDrift_eq_scaled hm]
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm,← smul_sub,norm_smul,Real.norm_eq_abs]
  calc
    _ ≤ ‖configurationEuclidean d m (particleDrift b ((configurationEuclidean d m).symm x))-
        configurationEuclidean d m (particleDrift b ((configurationEuclidean d m).symm y))‖ :=
      mul_le_of_le_one_left (norm_nonneg _) hs
    _ ≤ _ := by simpa only [dist_eq_norm] using hp.dist_le_mul x y

theorem internalDrift_fderiv_bound {b : Position d → Position d → Position d}
    {M L₁ L₂ : ℝ} (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
    (hm : 0 < m) (hmN : m ≤ N) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (x : Point (m*d)) :
    ‖fderiv ℝ (internalDrift (m := m) N b) x‖ ≤ Real.sqrt (2*(d:ℝ)*(L₁^2+L₂^2)) := by
  exact norm_fderiv_le_of_lipschitz ℝ (internalDrift_lipschitz hb hbound hm hmN hL₁ hL₂)

end SharpWasserstein.ExternalInteractionPeriodic
