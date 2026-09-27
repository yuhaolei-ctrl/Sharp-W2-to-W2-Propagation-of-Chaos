import SharpWasserstein.GaussianMoments
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Genuine Gaussian integration by parts

Stein's identity is proved by integration by parts against the explicit Gaussian
density. The boundary contribution is eliminated by the actual integrability
hypotheses of the whole-line integration-by-parts theorem.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
namespace SharpWasserstein.GaussianSharpness

theorem gaussian_integrable_iff_density {f : ℝ → ℝ} :
    Integrable f (gaussianReal 0 1) ↔
      Integrable (fun x => gaussianPDFReal 0 1 x * f x) volume := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0)]
  have h := integrable_withDensity_iff_integrable_smul'
    (μ := (volume : Measure ℝ)) (g := f) (measurable_gaussianPDF 0 1)
    (Eventually.of_forall (fun x => gaussianPDF_lt_top (μ := 0) (v := 1) (x := x)))
  simpa only [gaussianPDF_def, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 1 _),
    smul_eq_mul] using h

theorem gaussianPDF_standard_hasDerivAt (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have hq : HasDerivAt (fun y : ℝ => -y^2 / 2) (-x) x := by
    convert! (((hasDerivAt_id x).pow 2).neg.div_const 2) using 1
    norm_num
    ring
  have h := hq.exp.const_mul ((Real.sqrt (2*Real.pi))⁻¹)
  simp only [gaussianPDFReal_def, NNReal.coe_one, mul_one, sub_zero]
  convert! h using 1
  ring

/-- Scalar Stein identity, proved for every bounded C¹ test with bounded derivative. -/
theorem standardGaussian_stein {g g' : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt g (g' x) x) (hgc : Continuous g')
    (C D : ℝ) (hC : ∀ x, ‖g x‖ ≤ C) (hD : ∀ x, ‖g' x‖ ≤ D) :
    (∫ x, x * g x ∂gaussianReal 0 1) = ∫ x, g' x ∂gaussianReal 0 1 := by
  have hcont : Continuous g := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  have hg : Integrable g (gaussianReal 0 1) :=
    Integrable.of_bound hcont.aestronglyMeasurable C (Eventually.of_forall hC)
  have hg' : Integrable g' (gaussianReal 0 1) :=
    Integrable.of_bound hgc.aestronglyMeasurable D (Eventually.of_forall hD)
  have hxg : Integrable (fun x => x * g x) (gaussianReal 0 1) :=
    ((memLp_id_gaussianReal' (μ := 0) (v := 1) 1 (by norm_num)).integrable le_rfl).mul_bdd
      hcont.aestronglyMeasurable (Eventually.of_forall hC)
  have h1 := gaussian_integrable_iff_density.mp hg'
  have h2 := (gaussian_integrable_iff_density.mp hxg).neg
  have h3 := gaussian_integrable_iff_density.mp hg
  have hi := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := gaussianPDFReal 0 1) (v := g) (u' := fun x => -x * gaussianPDFReal 0 1 x)
    (v' := g') (fun x _ => gaussianPDF_standard_hasDerivAt x) (fun x _ => hd x)
    h1 (by convert h2 using 1; ext x; dsimp; ring) h3
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0),
    integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [smul_eq_mul]
  rw [hi]
  rw [← integral_neg]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by ring)

/-- Stein's identity in one coordinate of the genuine finite Gaussian product. -/
theorem standardLabels_stein {n : ℕ} (i : Fin (n+1)) {f g : (Fin (n+1) → ℝ) → ℝ}
    (hfm : AEStronglyMeasurable f (standardLabels (n+1)))
    (hgm : AEStronglyMeasurable g (standardLabels (n+1)))
    (hd : ∀ (ω : Fin n → ℝ) (z : ℝ),
      HasDerivAt (fun y => f (i.insertNth y ω)) (g (i.insertNth z ω)) z)
    (hgc : ∀ ω : Fin n → ℝ, Continuous (fun z => g (i.insertNth z ω)))
    (C D : ℝ) (hC : ∀ ω, ‖f ω‖ ≤ C) (hD : ∀ ω, ‖g ω‖ ≤ D) :
    (∫ ω, ω i * f ω ∂standardLabels (n+1)) = ∫ ω, g ω ∂standardLabels (n+1) := by
  letI := standardLabels_probability (n+1)
  letI := standardLabels_probability n
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i).symm
  have hp : MeasurePreserving e ((gaussianReal 0 1).prod (standardLabels n))
      (standardLabels (n+1)) :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => gaussianReal 0 1) i).symm
  have hif : Integrable (fun ω => ω i * f ω) (standardLabels (n+1)) :=
    ((coordinate_memLp (n+1) i).integrable (by norm_num)).mul_bdd hfm
      (Eventually.of_forall hC)
  have hig : Integrable g (standardLabels (n+1)) :=
    Integrable.of_bound hgm D (Eventually.of_forall hD)
  rw [← hp.integral_comp' (fun ω => ω i * f ω), ← hp.integral_comp' g]
  have hi1 : Integrable (fun x => e x i * f (e x))
      ((gaussianReal 0 1).prod (standardLabels n)) :=
    (hp.integrable_comp hif.aestronglyMeasurable).mpr hif
  have hi2 : Integrable (fun x => g (e x))
      ((gaussianReal 0 1).prod (standardLabels n)) := (hp.integrable_comp hgm).mpr hig
  rw [integral_prod_symm _ hi1, integral_prod_symm _ hi2]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro ω
  change (∫ z : ℝ, i.insertNth (α := fun _ : Fin (n+1) => ℝ) z ω i * f (i.insertNth z ω) ∂gaussianReal 0 1) =
    ∫ z : ℝ, g (i.insertNth z ω) ∂gaussianReal 0 1
  simp only [Fin.insertNth_apply_same]
  exact standardGaussian_stein (hd ω) (hgc ω) C D (fun z => hC _) (fun z => hD _)

end SharpWasserstein.GaussianSharpness
