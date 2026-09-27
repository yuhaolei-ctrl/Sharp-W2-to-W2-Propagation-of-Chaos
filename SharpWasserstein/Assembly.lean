import SharpWasserstein.EntropyHierarchy
import SharpWasserstein.CooperativeHierarchy
import SharpWasserstein.TangentEnergy
import SharpWasserstein.RegularizationRates
import Mathlib.Topology.MetricSpace.Basic

/-!
# Composition of the verified estimates

The source and finite cooperative comparison are genuinely composed below.
The Hilbert-space specialization uses the proved variational-energy/Riesz-norm
identity, rather than a formal symbol called an energy.

These theorems retain the analytic bridges as explicit hypotheses: the entropy
sequence conditions, the bounded-sum and conditional-Pinsker inequalities,
the initial velocity decomposition, and the evolution differential inequality.
They do not assert that a diffusion supplies those hypotheses.

The endpoint theorem uses an actual pseudometric triangle inequality and the
proved Lebesgue integral of the inverse-square-root speed bound. Its length
and decoupled-distance hypotheses still require the transport/PDE arguments.
No identification with the separately defined Wasserstein infimum is claimed.
-/

noncomputable section

open Set Real MeasureTheory

namespace SharpWasserstein

/-- The numerical entropy source estimate, propagated by the finite hierarchy.

`H` is the entropy-profile coefficient at the switch time `a`; `K` is the
source-estimate constant; `C` is the coefficient in the evolution hierarchy.
The initial source-energy profile is derived here, not assumed.
-/
theorem propagated_source_energy
    {N : ℕ} {H K C a b : ℝ} {h : ℕ → ℝ}
    (hN : 0 < N) (hH : 0 ≤ H) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hc : FiniteEntropyConditions h N)
    (hprofile : ∀ j, j ≤ N → h j ≤ H * (j : ℝ) ^ 2 / (N : ℝ) ^ 2)
    {E Ed : ℕ → ℝ → ℝ} {I X : ℕ → ℝ}
    (hI : ∀ m, 1 ≤ m → m ≤ N →
      I m ≤ K * (m : ℝ) ^ 2 / (N : ℝ) ^ 2 * (1 + h m))
    (hX : ∀ m, 1 ≤ m → m ≤ N →
      X m ≤ K * ((((N : ℝ) - m) / N) ^ 2 * m * entropyIncrement h m))
    (hsource : ∀ m, 1 ≤ m → m ≤ N → E m a ≤ 2 * I m + 2 * X m)
    (hEc : ∀ m, 1 ≤ m → m ≤ N → ContinuousOn (E m) (Icc a b))
    (hEd : ∀ m, 1 ≤ m → m ≤ N → ∀ t ∈ Ico a b,
      HasDerivWithinAt (E m) (Ed m t) (Ici t) t)
    (hE : ∀ m, 1 ≤ m → m < N → ∀ t ∈ Ico a b,
      Ed m t ≤ C * E m t + C * m * (E (m + 1) t - E m t))
    (hEN : ∀ t ∈ Ico a b, Ed N t ≤ C * E N t) :
    ∀ m, 1 ≤ m → m ≤ N → ∀ t ∈ Icc a b,
      E m t ≤ (2 * K * (1 + 5 * H)) * exp (4 * C * (t - a)) *
        (m : ℝ) ^ 2 / (N : ℝ) ^ 2 := by
  apply finite_cooperative_quadratic_bound
    (A := 2 * K * (1 + 5 * H)) (by positivity) hC hEc hEd
  · intro m hm hmN
    exact source_energy_from_entropy_profile hc hN hm hmN hH hK hprofile
      (hI m hm hmN) (hX m hm hmN) (hsource m hm hmN)
  · exact hE
  · exact hEN

/-- Hilbert-space specialization with the genuine variational dual energy.

The spaces may depend on the level. Continuity, the right derivatives, and
both hierarchy inequalities are still analytic hypotheses about these actual
energies; no assertion about weighted gradient spaces or diffusions is hidden.
-/
theorem propagated_riesz_energy
    {V : ℕ → Type*} [∀ m, NormedAddCommGroup (V m)]
    [∀ m, InnerProductSpace ℝ (V m)] [∀ m, CompleteSpace (V m)]
    (ℓ : (m : ℕ) → ℝ → V m →L[ℝ] ℝ)
    {N : ℕ} {H K C a b : ℝ} {h : ℕ → ℝ}
    (hN : 0 < N) (hH : 0 ≤ H) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hc : FiniteEntropyConditions h N)
    (hprofile : ∀ j, j ≤ N → h j ≤ H * (j : ℝ) ^ 2 / (N : ℝ) ^ 2)
    {Ed : ℕ → ℝ → ℝ} {I X : ℕ → ℝ}
    (hI : ∀ m, 1 ≤ m → m ≤ N →
      I m ≤ K * (m : ℝ) ^ 2 / (N : ℝ) ^ 2 * (1 + h m))
    (hX : ∀ m, 1 ≤ m → m ≤ N →
      X m ≤ K * ((((N : ℝ) - m) / N) ^ 2 * m * entropyIncrement h m))
    (hsource : ∀ m, 1 ≤ m → m ≤ N →
      TangentEnergy.dualEnergy (ℓ m a) ≤ 2 * I m + 2 * X m)
    (hEc : ∀ m, 1 ≤ m → m ≤ N →
      ContinuousOn (fun t => TangentEnergy.dualEnergy (ℓ m t)) (Icc a b))
    (hEd : ∀ m, 1 ≤ m → m ≤ N → ∀ t ∈ Ico a b,
      HasDerivWithinAt (fun u => TangentEnergy.dualEnergy (ℓ m u))
        (Ed m t) (Ici t) t)
    (hE : ∀ m, 1 ≤ m → m < N → ∀ t ∈ Ico a b,
      Ed m t ≤ C * TangentEnergy.dualEnergy (ℓ m t) +
        C * m * (TangentEnergy.dualEnergy (ℓ (m + 1) t) -
          TangentEnergy.dualEnergy (ℓ m t)))
    (hEN : ∀ t ∈ Ico a b, Ed N t ≤ C * TangentEnergy.dualEnergy (ℓ N t)) :
    ∀ m, 1 ≤ m → m ≤ N → ∀ t ∈ Icc a b,
      ‖TangentEnergy.rieszRepresentative (ℓ m t)‖ ^ 2 ≤
        (2 * K * (1 + 5 * H)) * exp (4 * C * (t - a)) *
          (m : ℝ) ^ 2 / (N : ℝ) ^ 2 := by
  have hp := propagated_source_energy (E := fun m t => TangentEnergy.dualEnergy (ℓ m t))
    hN hH hK hC hc hprofile hI hX hsource hEc hEd hE hEN
  simpa only [TangentEnergy.dualEnergy_eq_norm_sq] using hp

/-- Explicit constant obtained by adding the interpolation and decoupled lengths. -/
def endpointConstant (K L C₀ T : ℝ) : ℝ :=
  (K * (T + 2 * sqrt T) + exp (L * T) * sqrt C₀) ^ 2

theorem endpointConstant_nonneg (K L C₀ T : ℝ) :
    0 ≤ endpointConstant K L C₀ T := sq_nonneg _

/-- Endpoint assembly in an actual pseudometric space.

The first hypothesis is a length bound with an actual interval integral.
Proving it for the interpolation curve is an outstanding analytic bridge.
The second is the decoupled stability estimate. This theorem neither assumes
nor fabricates a pseudometric instance for the custom Wasserstein infimum.
-/
theorem metric_endpoint_assembly
    {M : Type*} [PseudoMetricSpace M] (x r y : M)
    {K L C₀ T : ℝ} {k N : ℕ} (hK : 0 ≤ K) (hT : 0 ≤ T)
    (hlength : dist x r ≤
      K * (∫ s in (0 : ℝ)..T, RegularizationRates.speedRate s) * ((k : ℝ) / N))
    (hdecoupled : dist r y ≤ exp (L * T) * sqrt C₀ * ((k : ℝ) / N)) :
    dist x y ^ 2 ≤ endpointConstant K L C₀ T * (k : ℝ) ^ 2 / (N : ℝ) ^ 2 := by
  rw [RegularizationRates.integral_speedRate] at hlength
  have hb : 0 ≤
      (K * (T + 2 * sqrt T) + exp (L * T) * sqrt C₀) * ((k : ℝ) / N) := by
    positivity
  have hd : dist x y ≤
      (K * (T + 2 * sqrt T) + exp (L * T) * sqrt C₀) * ((k : ℝ) / N) := by
    calc
      dist x y ≤ dist x r + dist r y := dist_triangle x r y
      _ ≤ K * (T + 2 * sqrt T) * ((k : ℝ) / N) +
          exp (L * T) * sqrt C₀ * ((k : ℝ) / N) := add_le_add hlength hdecoupled
      _ = _ := by ring
  calc
    dist x y ^ 2 ≤
        ((K * (T + 2 * sqrt T) + exp (L * T) * sqrt C₀) * ((k : ℝ) / N)) ^ 2 :=
      (sq_le_sq₀ dist_nonneg hb).2 hd
    _ = endpointConstant K L C₀ T * (k : ℝ) ^ 2 / (N : ℝ) ^ 2 := by
      unfold endpointConstant
      ring

end SharpWasserstein
