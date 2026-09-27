import SharpWasserstein.ExternalInteractionGradient
import SharpWasserstein.PropagatedSourcePermutationParticle
import SharpWasserstein.WeightedSourceSymmetry
import Mathlib.Order.Interval.Finset.Fin

/-! Actual observation maps for a prefix and one external particle. Their
transposition identity gives the correct scalar-test and differential
transformation, in genuine Euclidean coordinates. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal ContDiff InnerProductSpace BigOperators
namespace SharpWasserstein.ExternalInteractionSymmetry
open WeightedTangent WeightedMarginal PropagatedSourcePermutation ExternalInteraction

/-- Observe the first m particles and one specified particle, in the same
Euclidean coordinates as the external interaction estimate. -/
def observation {d m N : ℕ} (hm : m ≤ N) (j : Fin N) :
    Point (N*d) →L[ℝ] Point (m*d+d) where
  toFun x := WithLp.toLp 2 (Fin.addCases
    (fun k => (configurationEuclidean d N).symm x
      (Fin.castLE hm (finProdFinEquiv.symm k).1) (finProdFinEquiv.symm k).2)
    (fun a => (configurationEuclidean d N).symm x j a))
  map_add' x y := by
    ext k
    cases k using Fin.addCases <;> simp
  map_smul' c x := by
    ext k
    cases k using Fin.addCases <;> simp
  cont := (PiLp.continuous_toLp 2 (fun _ : Fin (m*d+d) => ℝ)).comp (by
    apply continuous_pi
    intro k
    cases k using Fin.addCases <;> simp only [Fin.addCases_left, Fin.addCases_right] <;> fun_prop)

@[simp] theorem observation_prefix {d m N : ℕ} (hm : m ≤ N) (j : Fin N)
    (x : Configuration d N) :
    prefixProjection (m*d) d (observation hm j (configurationEuclidean d N x)) =
      configurationEuclidean d m (restrictCoordinates hm x) := by
  ext k
  obtain ⟨⟨i,a⟩,rfl⟩ := finProdFinEquiv.surjective k
  simp [prefixProjection, observation, restrictCoordinates]
  change x (Fin.castLE hm (finProdFinEquiv.symm (finProdFinEquiv (i,a))).1)
    (finProdFinEquiv.symm (finProdFinEquiv (i,a))).2 = x (Fin.castLE hm i) a
  rw [Equiv.symm_apply_apply]


@[simp] theorem observation_positions {d m N : ℕ} (hm : m ≤ N) (j : Fin N)
    (x : Configuration d N) :
    positions (observation hm j (configurationEuclidean d N x)) = restrictCoordinates hm x := by
  unfold positions
  rw [observation_prefix, ContinuousLinearEquiv.symm_apply_apply]

@[simp] theorem observation_external {d m N : ℕ} (hm : m ≤ N) (j : Fin N)
    (x : Configuration d N) :
    externalPosition (observation hm j (configurationEuclidean d N x)) = x j := by
  funext a
  simp [externalPosition, suffixProjection, observation]


/-- Every permutation fixing the retained prefix simply relabels the observed
external particle. This is a literal identity of continuous linear maps. -/
theorem observation_permutation {d m N : ℕ} (hm : m ≤ N)
    (e : Equiv.Perm (Fin N)) (he : ∀ i : Fin m, e (Fin.castLE hm i) = Fin.castLE hm i)
    (j : Fin N) :
    (observation (d := d) hm j).comp (euclideanPermutation e).toContinuousLinearMap =
      observation hm (e j) := by
  ext x k
  obtain ⟨z,rfl⟩ := (configurationEuclidean d N).surjective x
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    euclideanPermutation_coordinates]
  cases k using Fin.addCases <;> simp [observation, configurationPermutation, he]


/-- Swapping two external labels fixes every retained particle. -/
theorem external_swap_fixes_prefix {m N : ℕ} (hm : m < N)
    (j : Fin N) (hj : m ≤ j.val) (i : Fin m) :
    Equiv.swap (⟨m,hm⟩ : Fin N) j (Fin.castLE hm.le i) = Fin.castLE hm.le i := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h
    have hv := congrArg Fin.val h
    change i.val = m at hv
    omega
  · intro h
    have hv := congrArg Fin.val h
    change i.val = j.val at hv
    omega

/-- Actual scalar tests with external index j are pullbacks of the same
next-particle test by the concrete transposition. No compactness of a cylinder
function is silently asserted. -/
theorem observation_test_swap {d m N : ℕ} (hm : m < N) (j : Fin N) (hj : m ≤ j.val)
    (F : Point (m*d+d) → ℝ) :
    (F ∘ observation hm.le ⟨m,hm⟩) ∘ euclideanPermutation (Equiv.swap ⟨m,hm⟩ j) =
      F ∘ observation hm.le j := by
  have h := observation_permutation (d := d) hm.le (Equiv.swap ⟨m,hm⟩ j)
    (external_swap_fixes_prefix hm j hj) ⟨m,hm⟩
  simp only [Equiv.swap_apply_left] at h
  funext x
  exact congrArg F (congrArg (fun L : Point (N*d) →L[ℝ] Point (m*d+d) => L x) h)

/-- The genuine external interaction associated to a particular full particle. -/
def particleInteraction {d m N : ℕ} (hm : m ≤ N) (j : Fin N)
    (b : Position d → Position d → Position d) (f : Point (m*d) → ℝ) : Point (N*d) → ℝ :=
  interaction b f ∘ observation hm j

/-- The observed test is exactly the m-block interaction with particle j. -/
theorem particleInteraction_eq_sum {d m N : ℕ} (hm : m ≤ N) (j : Fin N)
    (b : Position d → Position d → Position d) (f : Point (m*d) → ℝ)
    (x : Configuration d N) :
    particleInteraction hm j b f (configurationEuclidean d N x) =
      ∑ i : Fin m, ∑ a : Fin d, b (x (Fin.castLE hm i)) (x j) a *
        gradient f (configurationEuclidean d m (restrictCoordinates hm x)) (finProdFinEquiv (i,a)) := by
  unfold particleInteraction
  rw [Function.comp_apply, interaction_eq_sum, observation_prefix,
    observation_positions, observation_external]
  rfl

/-- The actual interaction differential includes both retained and external
coordinates through the true observation derivative. -/
theorem particleInteraction_fderiv {d m N : ℕ} (hm : m ≤ N) (j : Fin N)
    {b : Position d → Position d → Position d} (hb : BoundedSmoothKernel b)
    {f : Point (m*d) → ℝ} (hf : ContDiff ℝ ∞ f) (x v : Point (N*d)) :
    fderiv ℝ (particleInteraction hm j b f) x v =
      ⟪gradient (interaction b f) (observation hm j x), observation hm j v⟫_ℝ := by
  rw [inner_gradient_left]
  unfold particleInteraction
  rw [fderiv_comp x ((interaction_smooth hb hf).differentiable (by simp) _)
    (observation hm j).differentiableAt, ContinuousLinearMap.fderiv]
  rfl

end SharpWasserstein.ExternalInteractionSymmetry
