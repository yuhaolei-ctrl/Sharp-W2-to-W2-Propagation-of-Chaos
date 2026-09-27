import SharpWasserstein.PeriodicFourierDerivative
import Mathlib.Analysis.Fourier.AddCircleMulti

/-! Exact passage between the periodic Euclidean cube and the unit torus.
The cube carries product Lebesgue measure and the torus carries probability
Haar measure; no normalization or coordinate derivative is changed. -/
noncomputable section
open MeasureTheory Set Function
open scoped ENNReal BigOperators Topology
namespace SharpWasserstein.PeriodicTorusBridge
open PeriodicIntegrationByParts PeriodicFourierTests

def toTorus {n : ℕ} (x : Coordinates n) : UnitAddTorus (Fin n) := fun i => (x i : UnitAddCircle)

def haar (n : ℕ) : Measure (UnitAddTorus (Fin n)) :=
  Measure.pi (fun _ : Fin n => AddCircle.haarAddCircle)

instance haar_isProbabilityMeasure (n : ℕ) : IsProbabilityMeasure (haar n) := by
  unfold haar
  infer_instance

theorem unitCircle_volume_eq_haar : (volume : Measure UnitAddCircle) = AddCircle.haarAddCircle := by
  rw [AddCircle.volume_eq_smul_haarAddCircle]
  simp

theorem torus_volume_eq_haar (n : ℕ) : (volume : Measure (UnitAddTorus (Fin n))) = haar n := by
  change (Measure.pi fun _ : Fin n => (volume : Measure UnitAddCircle)) = _
  simp only [unitCircle_volume_eq_haar,haar]

theorem toTorus_openQuotient (n : ℕ) : IsOpenQuotientMap (toTorus (n := n)) :=
  IsOpenQuotientMap.piMap (fun _ : Fin n => QuotientAddGroup.isOpenQuotientMap_mk)

theorem toTorus_continuous (n : ℕ) : Continuous (toTorus (n := n)) := (toTorus_openQuotient n).continuous

theorem toTorus_surjective (n : ℕ) : Surjective (toTorus (n := n)) := (toTorus_openQuotient n).surjective

theorem measurePreserving_toTorus (n : ℕ) : MeasurePreserving (toTorus (n := n)) (cube n) (haar n) := by
  apply measurePreserving_pi
  intro i
  have h := UnitAddCircle.measurePreserving_mk 0
  simpa only [zero_add,PeriodicIntegrationByParts.unitInterval,unitCircle_volume_eq_haar] using h

theorem integral_toTorus {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : UnitAddTorus (Fin n) → E) (hf : AEStronglyMeasurable f (haar n)) :
    (∫ x, f (toTorus x) ∂cube n) = ∫ z, f z ∂haar n :=
  (measurePreserving_toTorus n).hasLaw.integral_comp hf

/-- Coordinate periods imply invariance under every integer lattice vector. -/
theorem periodic_integer_shift {n : ℕ} {E : Type*} {f : Coordinates n → E}
    (hp : ∀ i, Function.Periodic f (Pi.single i 1)) (k : Fin n → ℤ) (x : Coordinates n) :
    f (x + fun i => (k i : ℝ)) = f x := by
  have hsum (s : Finset (Fin n)) : Function.Periodic f (∑ i ∈ s, (k i) • Pi.single i (1 : ℝ)) := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.sum_empty]; exact fun x => by rw [add_zero]
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact ((hp i).zsmul (k i)).add_period ih
  have he : (∑ i : Fin n, (k i) • Pi.single i (1 : ℝ)) = fun i => (k i : ℝ) := by
    funext j
    simp [Finset.sum_apply,Pi.single_apply]
  simpa only [he] using hsum Finset.univ x

theorem periodic_eq_of_toTorus_eq {n : ℕ} {E : Type*} {f : Coordinates n → E}
    (hp : ∀ i, Function.Periodic f (Pi.single i 1)) {x y : Coordinates n}
    (hxy : toTorus x = toTorus y) : f x = f y := by
  have hi (i : Fin n) : ∃ k : ℤ, (k : ℝ) = x i-y i := by
    have he : ((x i-y i : ℝ) : UnitAddCircle) = 0 := by
      rw [AddCircle.coe_sub]
      exact sub_eq_zero.mpr (congrFun hxy i)
    simpa only [zsmul_eq_mul,mul_one] using (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp he
  choose k hk using hi
  have he : x = y + fun i => (k i : ℝ) := by funext i; simp only [Pi.add_apply,hk]; ring
  rw [he]
  exact periodic_integer_shift hp k y

/-- Descend an actual coordinate-periodic function through the quotient. -/
def lift {n : ℕ} {E : Type*} (f : Coordinates n → E) : UnitAddTorus (Fin n) → E :=
  fun z => f (Function.invFun toTorus z)

theorem lift_toTorus {n : ℕ} {E : Type*} {f : Coordinates n → E}
    (hp : ∀ i, Function.Periodic f (Pi.single i 1)) (x : Coordinates n) : lift f (toTorus x) = f x :=
  periodic_eq_of_toTorus_eq hp (Function.rightInverse_invFun (toTorus_surjective n) (toTorus x))

theorem lift_continuous {n : ℕ} {E : Type*} [TopologicalSpace E] {f : Coordinates n → E}
    (hp : ∀ i, Function.Periodic f (Pi.single i 1)) (hf : Continuous f) : Continuous (lift f) := by
  apply (toTorus_openQuotient n).continuous_comp_iff.mp
  have he : lift f ∘ toTorus = f := funext (lift_toTorus hp)
  rw [he]
  exact hf

def continuousLift {n : ℕ} {E : Type*} [TopologicalSpace E] (f : Coordinates n → E)
    (hp : ∀ i, Function.Periodic f (Pi.single i 1)) (hf : Continuous f) : C(UnitAddTorus (Fin n), E) :=
  ⟨lift f,lift_continuous hp hf⟩


/-- Complex presentation of the real periodic lift, used by the Fourier basis. -/
def complexLift {n : ℕ} (f : Coordinates n → ℝ) (hp : Periodic f) (hf : Continuous f) :
    C(UnitAddTorus (Fin n), ℂ) :=
  ⟨fun z => ((lift f z : ℝ) : ℂ),Complex.continuous_ofReal.comp (lift_continuous hp hf)⟩

theorem complexLift_toTorus {n : ℕ} (f : Coordinates n → ℝ) (hp : Periodic f)
    (hf : Continuous f) (x : Coordinates n) : complexLift f hp hf (toTorus x) = (f x : ℂ) :=
  congrArg Complex.ofReal (lift_toTorus hp x)

theorem integral_lift {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [SecondCountableTopology E] {f : Coordinates n → E}
    (hp : ∀ i, Function.Periodic f (Pi.single i 1)) (hf : Continuous f) :
    (∫ z, lift f z ∂haar n) = ∫ x, f x ∂cube n := by
  rw [← integral_toTorus _ (lift_continuous hp hf).aestronglyMeasurable]
  simp_rw [lift_toTorus hp]

/-- Exact complex exponential convention for the torus Fourier monomial. -/
theorem mFourier_toTorus {n : ℕ} (k : Fin n → ℤ) (x : Coordinates n) :
    UnitAddTorus.mFourier k (toTorus x) = Complex.exp ((phase k x : ℝ)*Complex.I) := by
  simp only [UnitAddTorus.mFourier,ContinuousMap.coe_mk,toTorus,fourier_coe_apply,
    Complex.ofReal_one,div_one]
  rw [← Complex.exp_sum]
  congr 1
  simp only [phase_apply,Complex.ofReal_mul,Complex.ofReal_sum,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  ring

theorem mFourier_toTorus_cosine_sine {n : ℕ} (k : Fin n → ℤ) (x : Coordinates n) :
    UnitAddTorus.mFourier k (toTorus x) = (cosine k x : ℂ) + Complex.I*(sine k x : ℂ) := by
  rw [mFourier_toTorus,Complex.exp_mul_I]
  simp only [cosine,sine,← Complex.ofReal_cos,← Complex.ofReal_sin]
  ring


/-- The real sine/cosine coefficient equals the library's actual torus
Fourier coefficient with its negative-frequency convention. -/
theorem mFourierCoeff_lift {n : ℕ} {f : Coordinates n → ℝ}
    (hp : Periodic f) (hf : Continuous f) (k : Fin n → ℤ) :
    UnitAddTorus.mFourierCoeff (fun z => ((lift f z : ℝ) : ℂ)) k =
      PeriodicFourierDerivative.coefficient f k := by
  change (∫ z, UnitAddTorus.mFourier (-k) z * ((lift f z : ℝ) : ℂ) ∂haar n) = _
  have hm : AEStronglyMeasurable (fun z => UnitAddTorus.mFourier (-k) z * ((lift f z : ℝ) : ℂ)) (haar n) :=
    ((UnitAddTorus.mFourier (-k)).continuous.mul
      (Complex.continuous_ofReal.comp (lift_continuous hp hf))).aestronglyMeasurable
  rw [← integral_toTorus _ hm]
  have he : (fun x : Coordinates n => UnitAddTorus.mFourier (-k) (toTorus x) * ((lift f (toTorus x) : ℝ) : ℂ)) =
      fun x => ((f x * cosine k x : ℝ) : ℂ) - Complex.I*((f x * sine k x : ℝ) : ℂ) := by
    funext x
    rw [UnitAddTorus.mFourier_neg,mFourier_toTorus_cosine_sine,lift_toTorus hp]
    apply Complex.ext <;> simp <;> ring
  rw [he]
  have hc := continuous_integrable_cube (hf.mul (smooth_cosine k).continuous)
  have hs := continuous_integrable_cube (hf.mul (smooth_sine k).continuous)
  change Integrable (fun x => f x * cosine k x) (cube n) at hc
  change Integrable (fun x => f x * sine k x) (cube n) at hs
  have hc' : Integrable (fun x => ((f x * cosine k x : ℝ) : ℂ)) (cube n) := hc.ofReal
  have hs' : Integrable (fun x => ((f x * sine k x : ℝ) : ℂ)) (cube n) := hs.ofReal
  calc
    _ = (∫ x, ((f x * cosine k x : ℝ) : ℂ) ∂cube n) -
        ∫ x, Complex.I * ((f x * sine k x : ℝ) : ℂ) ∂cube n :=
      integral_sub hc' (hs'.const_mul Complex.I)
    _ = _ := by
      rw [integral_const_mul,integral_complex_ofReal,integral_complex_ofReal]
      rfl


theorem mFourierCoeff_complexLift {n : ℕ} (f : Coordinates n → ℝ)
    (hp : Periodic f) (hf : Continuous f) (k : Fin n → ℤ) :
    UnitAddTorus.mFourierCoeff (complexLift f hp hf) k =
      PeriodicFourierDerivative.coefficient f k := mFourierCoeff_lift hp hf k

end SharpWasserstein.PeriodicTorusBridge
