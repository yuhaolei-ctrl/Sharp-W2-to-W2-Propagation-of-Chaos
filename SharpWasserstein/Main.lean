import SharpWasserstein.MainFiniteActionReduction
import SharpWasserstein.RoughFiniteAction

/-! Complete proof of the original sharp Wasserstein propagation target.
The constants are chosen before the kernel, reference evolution and particle
family. No rough transport, source hierarchy, entropy estimate, regularity of
densities, or independent initial particles is added as a premise. -/
noncomputable section
namespace SharpWasserstein

/-- The original finite-horizon, all-marginal Wasserstein propagation theorem
for the stated bounded smooth interaction and correlated P₂ initial laws. -/
theorem main_theorem : MainTheorem :=
  main_of_uniform_finite_action_transport
    RoughEulerianTransport.uniform_finite_action_transport

end SharpWasserstein
