import SharpWasserstein.WeightedPeriodicTangentPhysical
import SharpWasserstein.ExternalInteractionSymmetryEstimate
import SharpWasserstein.SinePeriodization

/-! Genuine physical-period invariance of the external interaction and the
internal mean-field drift test, derived from actual coordinate shifts of the
kernel and ordinary Fréchet gradients. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace BigOperators
namespace SharpWasserstein.ExternalInteractionPeriodic
open WeightedTangent WeightedMarginal PeriodicIntegrationByParts PeriodicBochner
open ExternalInteraction WeightedPeriodicFourierScale
variable {n d m : ℕ}

def lattice (P : ℝ) (k : Fin n → ℤ) : Coordinates n := fun i => (k i : ℝ)*P

def euclideanLattice (P : ℝ) (k : Fin n → ℤ) : Point n :=
  (coordinateEquiv n).symm (lattice P k)

theorem coordinate_lattice_periodic {E : Type*} {f : Coordinates n → E} {P : ℝ}
    (hp : ∀ i, Function.Periodic f (Pi.single i P)) (k : Fin n → ℤ) (x : Coordinates n) :
    f (x+lattice P k) = f x := by
  have hsum (s : Finset (Fin n)) : Function.Periodic f (∑ i ∈ s,(k i) • Pi.single i P) := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.sum_empty]; exact fun x => by rw [add_zero]
    | @insert i s hi ih =>
        rw [Finset.sum_insert hi]
        exact ((hp i).zsmul (k i)).add_period ih
  have he : (∑ i : Fin n,(k i) • Pi.single i P) = lattice P k := by
    ext j
    simp [lattice,Finset.sum_apply,Pi.single_apply]
  simpa only [he] using hsum Finset.univ x

theorem euclidean_lattice_periodic {E : Type*} {f : Point n → E} {P : ℝ}
    (hp : ∀ i, Function.Periodic (f ∘ (coordinateEquiv n).symm) (Pi.single i P))
    (k : Fin n → ℤ) (x : Point n) : f (x+euclideanLattice P k) = f x := by
  have h := coordinate_lattice_periodic hp k (coordinateEquiv n x)
  simpa only [Function.comp_apply,map_add,ContinuousLinearEquiv.symm_apply_apply,euclideanLattice] using h

theorem gradient_lattice_periodic {f : Point n → ℝ} {P : ℝ}
    (hp : PeriodicOf P (f ∘ (coordinateEquiv n).symm)) (k : Fin n → ℤ) (x : Point n) :
    gradient f (x+euclideanLattice P k) = gradient f x := by
  have he : (fun y => f (y+euclideanLattice P k)) = f := funext (euclidean_lattice_periodic hp k)
  have hd := fderiv_comp_add_right (𝕜 := ℝ) (f := f) (x := x) (euclideanLattice P k)
  rw [he] at hd
  exact congrArg (InnerProductSpace.toDual ℝ (Point n)).symm hd.symm

theorem of_euclidean_lattice_periodic {E : Type*} {F : Point n → E} {P : ℝ}
    (h : ∀ k x, F (x+euclideanLattice P k) = F x) :
    ∀ i, Function.Periodic (F ∘ (coordinateEquiv n).symm) (Pi.single i P) := by
  intro i x
  have he : lattice P (Pi.single i (1 : ℤ)) = Pi.single i P := by
    ext j
    by_cases hj : j=i <;> simp [lattice,hj]
  have hh := h (Pi.single i 1) ((coordinateEquiv n).symm x)
  simpa only [euclideanLattice,he,← map_add,Function.comp_apply] using hh

theorem kernel_lattice {P : ℝ} {b : Position d → Position d → Position d}
    (hx : ∀ a x y, b (x+Pi.single a P) y = b x y)
    (hy : ∀ a x y, b x (y+Pi.single a P) = b x y)
    (k l : Fin d → ℤ) (x y : Position d) :
    b (x+lattice P k) (y+lattice P l) = b x y := by
  rw [coordinate_lattice_periodic (f := fun z => b z (y+lattice P l))
      (P := P) (fun a z => hx a z _) k x,
    coordinate_lattice_periodic (f := fun z => b x z) (P := P) (fun a z => hy a x z) l y]

theorem positions_lattice (P : ℝ) (k : Fin (m*d+d) → ℤ) (z : Point (m*d+d)) (i : Fin m) :
    positions (z+euclideanLattice P k) i =
      positions z i+lattice P (fun a => k ((finProdFinEquiv (i,a)).castAdd d)) := by
  ext a
  rfl

theorem externalPosition_lattice (P : ℝ) (k : Fin (m*d+d) → ℤ) (z : Point (m*d+d)) :
    externalPosition (z+euclideanLattice P k) =
      externalPosition z+lattice P (fun a => k (a.natAdd (m*d))) := by
  ext a
  rfl

theorem prefixProjection_lattice (P : ℝ) (k : Fin (n+m) → ℤ) (z : Point (n+m)) :
    prefixProjection n m (z+euclideanLattice P k) =
      prefixProjection n m z+euclideanLattice P (fun i => k (i.castAdd m)) := by
  ext i
  rfl

theorem force_lattice {P : ℝ} {b : Position d → Position d → Position d}
    (hx : ∀ a x y, b (x+Pi.single a P) y = b x y)
    (hy : ∀ a x y, b x (y+Pi.single a P) = b x y)
    (k : Fin (m*d+d) → ℤ) (z : Point (m*d+d)) :
    force b (z+euclideanLattice P k) = force b z := by
  unfold force
  congr 1
  funext i
  rw [positions_lattice,externalPosition_lattice,kernel_lattice hx hy]

/-- The actual external interaction has the physical kernel/potential period
in every retained and extra-particle coordinate. -/
theorem interaction_periodic {P : ℝ} {b : Position d → Position d → Position d}
    (hx : ∀ a x y, b (x+Pi.single a P) y = b x y)
    (hy : ∀ a x y, b x (y+Pi.single a P) = b x y)
    {f : Point (m*d) → ℝ} (hp : PeriodicOf P (f ∘ (coordinateEquiv (m*d)).symm)) :
    PeriodicOf P (interaction b f ∘ (coordinateEquiv (m*d+d)).symm) := by
  apply of_euclidean_lattice_periodic
  intro k x
  unfold interaction
  rw [force_lattice hx hy,prefixProjection_lattice,gradient_lattice_periodic hp]

/-- The genuine internal m-particle sum with the original full-N normalization,
including all diagonal self-interaction terms. -/
def internalDrift (N : ℕ) (b : Position d → Position d → Position d) (x : Point (m*d)) : Point (m*d) :=
  configurationEuclidean d m (fun i => (N : ℝ)⁻¹ • ∑ j : Fin m,
    b ((configurationEuclidean d m).symm x i) ((configurationEuclidean d m).symm x j))

theorem internalDrift_lattice {P : ℝ} {b : Position d → Position d → Position d}
    (hx : ∀ a x y, b (x+Pi.single a P) y = b x y)
    (hy : ∀ a x y, b x (y+Pi.single a P) = b x y)
    (N : ℕ) (k : Fin (m*d) → ℤ) (z : Point (m*d)) :
    internalDrift N b (z+euclideanLattice P k) = internalDrift N b z := by
  unfold internalDrift
  congr 1
  funext i
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have he (a : Fin m) : (configurationEuclidean d m).symm (z+euclideanLattice P k) a =
      (configurationEuclidean d m).symm z a+lattice P (fun r => k (finProdFinEquiv (a,r))) := by
    ext r
    rfl
  rw [he i,he j,kernel_lattice hx hy]

/-- The actual internal drift applied to the potential is a physical-period
scalar test; its periodicity is derived, not assumed as a source hypothesis. -/
theorem internalDrift_pairing_periodic {P : ℝ} {b : Position d → Position d → Position d}
    (hx : ∀ a x y, b (x+Pi.single a P) y = b x y)
    (hy : ∀ a x y, b x (y+Pi.single a P) = b x y)
    (N : ℕ) {f : Point (m*d) → ℝ}
    (hp : PeriodicOf P (f ∘ (coordinateEquiv (m*d)).symm)) :
    PeriodicOf P ((fun x => ⟪internalDrift N b x,gradient f x⟫_ℝ) ∘
      (coordinateEquiv (m*d)).symm) := by
  apply of_euclidean_lattice_periodic
  intro k x
  rw [internalDrift_lattice hx hy,gradient_lattice_periodic hp]

/-- In particular the implemented sine-periodized kernel supplies the actual
physical period 2πR required above. -/
theorem sine_interaction_periodic {R : ℝ} (hR : R ≠ 0)
    (b : Position d → Position d → Position d) {f : Point (m*d) → ℝ}
    (hp : PeriodicOf (2*Real.pi*R) (f ∘ (coordinateEquiv (m*d)).symm)) :
    PeriodicOf (2*Real.pi*R)
      (interaction (SinePeriodization.kernel R b) f ∘ (coordinateEquiv (m*d+d)).symm) :=
  interaction_periodic (SinePeriodization.kernel_periodic_first hR b)
    (SinePeriodization.kernel_periodic_second hR b) hp

/-- At the full level this is exactly the implemented particle drift,
including the diagonal term, expressed in genuine Euclidean coordinates. -/
theorem internalDrift_eq_particleDrift (b : Position d → Position d → Position d)
    (x : Point (m*d)) : internalDrift m b x =
      configurationEuclidean d m (particleDrift b ((configurationEuclidean d m).symm x)) := rfl

theorem internalDrift_smooth {b : Position d → Position d → Position d}
    (hb : BoundedSmoothKernel b) (N : ℕ) : ContDiff ℝ ∞ (internalDrift (m := m) N b) := by
  apply (configurationEuclidean d m).contDiff.comp
  apply contDiff_pi.mpr
  intro i
  apply ContDiff.const_smul
  apply ContDiff.sum
  intro j _
  exact hb.smooth.comp (((contDiff_pi.mp (configurationEuclidean d m).symm.contDiff) i).prodMk
    ((contDiff_pi.mp (configurationEuclidean d m).symm.contDiff) j))

theorem internalDrift_pairing_smooth {b : Position d → Position d → Position d}
    (hb : BoundedSmoothKernel b) (N : ℕ) {f : Point (m*d) → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun x => ⟪internalDrift N b x,gradient f x⟫_ℝ) :=
  (internalDrift_smooth hb N).inner ℝ (BochnerIdentity.smooth_gradient hf)

/-- The internal scalar test is exactly the actual drift differential. -/
theorem internalDrift_pairing_eq_fderiv (N : ℕ) (b : Position d → Position d → Position d)
    (f : Point (m*d) → ℝ) (x : Point (m*d)) :
    ⟪internalDrift N b x,gradient f x⟫_ℝ = fderiv ℝ f x (internalDrift N b x) := by
  rw [real_inner_comm,inner_gradient_left]

/-- Every normalized physical Fourier/smooth test has the required actual
period in the unscaled Euclidean coordinates. -/
theorem physicalPotential_periodic {P : ℝ} (hP : P ≠ 0) {f : Coordinates n → ℝ}
    (hp : Periodic f) : PeriodicOf P
      (WeightedPeriodicFourierPhysical.physicalPotential P f ∘ (coordinateEquiv n).symm) := by
  have he : WeightedPeriodicFourierPhysical.physicalPotential P f ∘ (coordinateEquiv n).symm =
      rescale P⁻¹ f := by
    funext x
    simp only [WeightedPeriodicFourierPhysical.physicalPotential,pullback,Function.comp_apply,
      ContinuousLinearEquiv.apply_symm_apply]
  rw [he]
  exact rescale_inverse_periodic hP hp

end SharpWasserstein.ExternalInteractionPeriodic
