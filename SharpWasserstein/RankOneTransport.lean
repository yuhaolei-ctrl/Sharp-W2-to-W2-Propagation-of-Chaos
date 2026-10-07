module

public import SharpWasserstein.Compat
public import SharpWasserstein.DynamicTransport

@[expose] public section

/-!
# Exact transport cost of stretching one common mode

The upper bound uses the explicit common-label coupling. The lower bound uses
the scalar projection of every admissible coupling and the L² triangle
inequality. No optimal-coupling existence or Gaussian transport formula is assumed.
-/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace

namespace SharpWasserstein.RankOneTransport

abbrev Vector (d N : ℕ) := EuclideanSpace ℝ (Fin N × Fin d)

theorem toEuclidean_ofEuclidean {d N : ℕ} (x : Vector d N) :
    configurationToEuclidean (configurationOfEuclidean x) = x := by
  ext i
  simp [configurationToEuclidean, configurationOfEuclidean, transportDisplacement]

def mode {d N : ℕ} (u : Vector d N) (x : Configuration d N) : ℝ :=
  ⟪u, configurationToEuclidean x⟫_ℝ

theorem continuous_mode {d N : ℕ} (u : Vector d N) : Continuous (mode u) :=
  continuous_const.inner continuous_configurationToEuclidean

theorem mode_sub {d N : ℕ} (u : Vector d N) (x y : Configuration d N) :
    mode u x - mode u y = ⟪u, transportDisplacement (x, y)⟫_ℝ := by
  rw [mode, mode, ← inner_sub_right]
  congr 1
  ext i
  simp [configurationToEuclidean, transportDisplacement]

def scaleLabel {Ω : Type*} {d N : ℕ} (α : ℝ) (Z : Ω → Vector d N) :
    Ω → Configuration d N := fun ω => configurationOfEuclidean (α • Z ω)

def stretchLabel {Ω : Type*} {d N : ℕ} (α β : ℝ) (u : Vector d N)
    (Z : Ω → Vector d N) : Ω → Configuration d N :=
  fun ω => configurationOfEuclidean (α • Z ω + ((β - α) * ⟪u, Z ω⟫_ℝ) • u)

theorem measurable_scaleLabel {Ω : Type*} [MeasurableSpace Ω] {d N : ℕ}
    (α : ℝ) {Z : Ω → Vector d N} (hZ : StronglyMeasurable Z) :
    Measurable (scaleLabel α Z) := by
  exact (continuous_configurationOfEuclidean.comp_stronglyMeasurable
    (hZ.const_smul α)).measurable

theorem measurable_stretchLabel {Ω : Type*} [MeasurableSpace Ω] {d N : ℕ}
    (α β : ℝ) (u : Vector d N) {Z : Ω → Vector d N} (hZ : StronglyMeasurable Z) :
    Measurable (stretchLabel α β u Z) := by
  exact (continuous_configurationOfEuclidean.comp_stronglyMeasurable
    ((hZ.const_smul α).add (((stronglyMeasurable_const.inner hZ).const_mul (β - α)).smul_const u))).measurable

theorem mode_scaleLabel {Ω : Type*} {d N : ℕ} (α : ℝ) (u : Vector d N)
    (Z : Ω → Vector d N) (ω : Ω) :
    mode u (scaleLabel α Z ω) = α * ⟪u, Z ω⟫_ℝ := by
  simp [mode, scaleLabel, toEuclidean_ofEuclidean, inner_smul_right]

theorem mode_stretchLabel {Ω : Type*} {d N : ℕ} (α β : ℝ) (u : Vector d N)
    (hu : ‖u‖ = 1) (Z : Ω → Vector d N) (ω : Ω) :
    mode u (stretchLabel α β u Z ω) = β * ⟪u, Z ω⟫_ℝ := by
  simp only [mode, stretchLabel, toEuclidean_ofEuclidean, inner_add_right, inner_smul_right,
    real_inner_self_eq_norm_sq, hu]
  ring

theorem mode_eLpNorm_scaleLaw {Ω : Type*} [MeasurableSpace Ω] {d N : ℕ}
    (P : Measure Ω) {Z : Ω → Vector d N} (hZ : StronglyMeasurable Z)
    (u : Vector d N) (hmode : eLpNorm (fun ω => ⟪u, Z ω⟫_ℝ) 2 P = 1)
    {α : ℝ} (hα : 0 ≤ α) :
    eLpNorm (mode u) 2 (Measure.map (scaleLabel α Z) P) = ENNReal.ofReal α := by
  rw [eLpNorm_map_measure (continuous_mode u).stronglyMeasurable.aestronglyMeasurable
    (measurable_scaleLabel α hZ).aemeasurable]
  change eLpNorm (fun ω => mode u (scaleLabel α Z ω)) 2 P = _
  simp only [mode_scaleLabel]
  change eLpNorm (α • (fun ω => ⟪u, Z ω⟫_ℝ)) 2 P = _
  rw [eLpNorm_const_smul, hmode, mul_one, ← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg hα]

theorem mode_eLpNorm_stretchLaw {Ω : Type*} [MeasurableSpace Ω] {d N : ℕ}
    (P : Measure Ω) {Z : Ω → Vector d N} (hZ : StronglyMeasurable Z)
    (u : Vector d N) (hu : ‖u‖ = 1)
    (hmode : eLpNorm (fun ω => ⟪u, Z ω⟫_ℝ) 2 P = 1)
    (α : ℝ) {β : ℝ} (hβ : 0 ≤ β) :
    eLpNorm (mode u) 2 (Measure.map (stretchLabel α β u Z) P) = ENNReal.ofReal β := by
  rw [eLpNorm_map_measure (continuous_mode u).stronglyMeasurable.aestronglyMeasurable
    (measurable_stretchLabel α β u hZ).aemeasurable]
  change eLpNorm (fun ω => mode u (stretchLabel α β u Z ω)) 2 P = _
  simp only [mode_stretchLabel α β u hu]
  change eLpNorm (β • (fun ω => ⟪u, Z ω⟫_ℝ)) 2 P = _
  rw [eLpNorm_const_smul, hmode, mul_one, ← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg hβ]

/-- Every coupling has at least the scalar-mode cost. -/
theorem coupling_root_cost_lower {d N : ℕ} (u : Vector d N) (hu : ‖u‖ = 1)
    {μ ν : Measure (Configuration d N)} {α β : ℝ} (hα : 0 ≤ α)
    (hμ : eLpNorm (mode u) 2 μ = ENNReal.ofReal β)
    (hν : eLpNorm (mode u) 2 ν = ENNReal.ofReal α)
    {γ : Measure (Configuration d N × Configuration d N)} (hγ : IsCoupling μ ν γ) :
    ENNReal.ofReal (β - α) ≤ transportCost γ ^ (1 / 2 : ℝ) := by
  let f := fun z : Configuration d N × Configuration d N => mode u z.1
  let g := fun z : Configuration d N × Configuration d N => mode u z.2
  have hf : AEStronglyMeasurable f γ :=
    ((continuous_mode u).comp continuous_fst).stronglyMeasurable.aestronglyMeasurable
  have hg : AEStronglyMeasurable g γ :=
    ((continuous_mode u).comp continuous_snd).stronglyMeasurable.aestronglyMeasurable
  have hfn : eLpNorm f 2 γ = ENNReal.ofReal β := by
    rw [← hμ, ← hγ.2.1, eLpNorm_map_measure
      (continuous_mode u).stronglyMeasurable.aestronglyMeasurable measurable_fst.aemeasurable]
    rfl
  have hgn : eLpNorm g 2 γ = ENNReal.ofReal α := by
    rw [← hν, ← hγ.2.2, eLpNorm_map_measure
      (continuous_mode u).stronglyMeasurable.aestronglyMeasurable measurable_snd.aemeasurable]
    rfl
  have ht := eLpNorm_add_le (f := f - g) (g := g) (μ := γ) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  rw [sub_add_cancel, hfn, hgn] at ht
  have hl : ENNReal.ofReal (β - α) ≤ eLpNorm (f - g) 2 γ := by
    rw [ENNReal.ofReal_sub β hα]
    exact tsub_le_iff_right.mpr ht
  apply hl.trans
  rw [transportCost_root_eq_eLpNorm]
  apply eLpNorm_mono_ae (hf.sub hg)
  filter_upwards [] with z
  change ‖mode u z.1 - mode u z.2‖ ≤ ‖transportDisplacement z‖
  rw [mode_sub]
  simpa only [hu, one_mul] using norm_inner_le_norm u (transportDisplacement z)

theorem stretch_scale_displacement {Ω : Type*} {d N : ℕ} (α β : ℝ) (u : Vector d N)
    (Z : Ω → Vector d N) (ω : Ω) :
    transportDisplacement (stretchLabel α β u Z ω, scaleLabel α Z ω) =
      ((β - α) * ⟪u, Z ω⟫_ℝ) • u := by
  rw [stretchLabel, scaleLabel, displacement_configurationOfEuclidean]
  abel

theorem stretch_scale_commonLabel_cost {Ω : Type*} [MeasurableSpace Ω] {d N : ℕ}
    (P : Measure Ω) {Z : Ω → Vector d N} (hZ : StronglyMeasurable Z)
    (u : Vector d N) (hu : ‖u‖ = 1)
    (hmode : eLpNorm (fun ω => ⟪u, Z ω⟫_ℝ) 2 P = 1)
    {α β : ℝ} (hαβ : α ≤ β) :
    transportCost (Measure.map (fun ω => (stretchLabel α β u Z ω, scaleLabel α Z ω)) P) ^
      (1 / 2 : ℝ) = ENNReal.ofReal (β - α) := by
  rw [transportCost_map_root_eq_eLpNorm P _ _
    (measurable_stretchLabel α β u hZ) (measurable_scaleLabel α hZ)]
  have he : eLpNorm (fun ω => transportDisplacement
      (stretchLabel α β u Z ω, scaleLabel α Z ω)) 2 P =
      eLpNorm ((β - α) • (fun ω => ⟪u, Z ω⟫_ℝ)) 2 P := by
    apply eLpNorm_congr_norm_ae
      (continuous_transportDisplacement.comp_aestronglyMeasurable
        ((measurable_stretchLabel α β u hZ).prodMk (measurable_scaleLabel α hZ)).aestronglyMeasurable)
      (by fun_prop)
    filter_upwards [] with ω
    rw [stretch_scale_displacement, norm_smul, hu, mul_one]
    rfl
  rw [he, eLpNorm_const_smul, hmode, mul_one, ← ofReal_norm,
    Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hαβ)]

/-- Exact square-root transport cost, with a constructed coupling attaining the lower bound. -/
theorem wassersteinSq_root_stretch_scale {Ω : Type*} [MeasurableSpace Ω] {d N : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] {Z : Ω → Vector d N} (hZ : StronglyMeasurable Z)
    (u : Vector d N) (hu : ‖u‖ = 1)
    (hmode : eLpNorm (fun ω => ⟪u, Z ω⟫_ℝ) 2 P = 1)
    {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) :
    wassersteinSq (Measure.map (stretchLabel α β u Z) P) (Measure.map (scaleLabel α Z) P) ^
      (1 / 2 : ℝ) = ENNReal.ofReal (β - α) := by
  apply le_antisymm
  · have hm := (measurable_stretchLabel α β u hZ).prodMk (measurable_scaleLabel α hZ)
    have hγ : IsCoupling (Measure.map (stretchLabel α β u Z) P) (Measure.map (scaleLabel α Z) P)
        (Measure.map (fun ω => (stretchLabel α β u Z ω, scaleLabel α Z ω)) P) := by
      refine ⟨Measure.isProbabilityMeasure_map hm.aemeasurable, ?_, ?_⟩
      · rw [Measure.map_map measurable_fst hm]
        rfl
      · rw [Measure.map_map measurable_snd hm]
        rfl
    exact (ENNReal.rpow_le_rpow (wassersteinSq_le_cost hγ)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans_eq
      (stretch_scale_commonLabel_cost P hZ u hu hmode hαβ)
  · rw [wassersteinSq_root_eq_iInf]
    apply le_iInf
    intro γ
    apply le_iInf
    intro hγ
    exact coupling_root_cost_lower u hu hα
      (mode_eLpNorm_stretchLaw P hZ u hu hmode α (hα.trans hαβ))
      (mode_eLpNorm_scaleLaw P hZ u hmode hα) hγ

/-- The exact cost is the genuine extended-valued infimum over probability couplings. -/
theorem wassersteinSq_stretch_scale {Ω : Type*} [MeasurableSpace Ω] {d N : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] {Z : Ω → Vector d N} (hZ : StronglyMeasurable Z)
    (u : Vector d N) (hu : ‖u‖ = 1)
    (hmode : eLpNorm (fun ω => ⟪u, Z ω⟫_ℝ) 2 P = 1)
    {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) :
    wassersteinSq (Measure.map (stretchLabel α β u Z) P) (Measure.map (scaleLabel α Z) P) =
      ENNReal.ofReal ((β - α) ^ 2) := by
  have he := congrArg (fun z : ℝ≥0∞ => z ^ (2 : ℝ))
    (wassersteinSq_root_stretch_scale P hZ u hu hmode hα hαβ)
  rw [← ENNReal.rpow_mul] at he
  norm_num only [one_div, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), ENNReal.rpow_one] at he
  simpa only [ENNReal.rpow_two, ENNReal.ofReal_pow (sub_nonneg.mpr hαβ)] using he

end SharpWasserstein.RankOneTransport
