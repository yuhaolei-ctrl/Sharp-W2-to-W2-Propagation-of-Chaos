module

public import SharpWasserstein.Compat
public import SharpWasserstein.FrozenGaussianExpectation

@[expose] public section

/-! The exact frozen-drift generator formula integrated from time zero. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators Interval
namespace SharpWasserstein.FrozenGaussian
open GaussianSharpness

theorem constant_generator_test {d N : ℕ} {φ : Configuration d N → ℝ}
    (hφ : SmoothCompactTest φ) (u : Configuration d N) :
    SmoothCompactTest (generator (fun _ => u) φ) := by
  refine ⟨?_, CompactGenerator.generator_compact hφ _⟩
  apply (CompactGenerator.laplacian_test hφ).1.add
  apply ContDiff.sum
  intro i _
  apply ContDiff.sum
  intro a _
  exact contDiff_const.mul (CompactGenerator.coordinate_test hφ i a).1

def timeExpectation {d N : ℕ} (φ : Configuration d N → ℝ) (x u : Configuration d N) (t : ℝ) : ℝ :=
  expectation φ x u (Real.sqrt (2*t))

theorem timeExpectation_continuous {d N : ℕ} {φ : Configuration d N → ℝ}
    (hφ : SmoothCompactTest φ) (x u : Configuration d N) : Continuous (timeExpectation φ x u) :=
  (expectation_continuous hφ x u).comp (by fun_prop)

theorem timeExpectation_zero {d N : ℕ} (φ : Configuration d N → ℝ) (x u : Configuration d N) :
    timeExpectation φ x u 0 = φ x := by
  letI := standardLabels_probability (N*d+1)
  simp [timeExpectation, expectation, label]

theorem timeExpectation_hasDerivAt {d N : ℕ} {φ : Configuration d N → ℝ}
    (hφ : SmoothCompactTest φ) (x u : Configuration d N) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (timeExpectation φ x u) (timeExpectation (generator (fun _ => u) φ) x u t) t := by
  have hpos : 0 < 2*t := by positivity
  have hsqrt : Real.sqrt (2*t) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hr : HasDerivAt (fun s : ℝ => Real.sqrt (2*s)) (1 / Real.sqrt (2*t)) t := by
    have hi : HasDerivAt (fun s : ℝ => 2*s) 2 t := by
      simpa using (hasDerivAt_id t).const_mul 2
    convert! (Real.hasDerivAt_sqrt hpos.ne').comp t hi using 1
    field_simp
  have h := (expectation_hasDerivAt hφ x u (Real.sqrt (2*t))).comp t hr
  convert! h using 1
  dsimp [timeExpectation]
  field_simp [hsqrt]

/-- Exact one-step weak generator identity, with arbitrary frozen position and
drift vector and the true sqrt(2) diffusion coefficient. -/
theorem timeExpectation_sub_eq_integral {d N : ℕ} {φ : Configuration d N → ℝ}
    (hφ : SmoothCompactTest φ) (x u : Configuration d N) {t : ℝ} (ht : 0 ≤ t) :
    timeExpectation φ x u t - φ x =
      ∫ s in 0..t, timeExpectation (generator (fun _ => u) φ) x u s := by
  rw [← timeExpectation_zero φ x u]
  symm
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht
    (timeExpectation_continuous hφ x u).continuousOn
    (fun s hs => timeExpectation_hasDerivAt hφ x u hs.1)
    ((timeExpectation_continuous (constant_generator_test hφ u) x u).intervalIntegrable 0 t)

end SharpWasserstein.FrozenGaussian
