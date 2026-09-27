import SharpWasserstein.ParticleFlow

/-! Permutation covariance of the constructed particle flow and preservation
of exchangeability under permutation-invariant continuous noise. -/

noncomputable section
open Set MeasureTheory

namespace SharpWasserstein

/-- Permuting whole particles is a continuous linear equivalence. -/
def configurationPermutation {d N : ℕ} (e : Equiv.Perm (Fin N)) :
    Configuration d N ≃L[ℝ] Configuration d N where
  toFun x := fun i => x (e i)
  invFun x := fun i => x (e.symm i)
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The self-interacting mean-field drift commutes with particle permutations. -/
theorem particleDrift_permutation {d N : ℕ}
    (b : Position d → Position d → Position d) (e : Equiv.Perm (Fin N))
    (x : Configuration d N) :
    particleDrift b (configurationPermutation e x) =
      configurationPermutation e (particleDrift b x) := by
  funext i
  change (N : ℝ)⁻¹ • ∑ j, b (x (e i)) (x (e j)) =
    (N : ℝ)⁻¹ • ∑ j, b (x (e i)) (x j)
  congr 1
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

theorem particleDrift_permutation_conjugate {d N : ℕ}
    (b : Position d → Position d → Position d) (e : Equiv.Perm (Fin N))
    (x : Configuration d N) :
    configurationPermutation e (particleDrift b ((configurationPermutation e).symm x)) =
      particleDrift b x := by
  rw [← particleDrift_permutation, ContinuousLinearEquiv.apply_symm_apply]

/-- Apply the same particle permutation to the entire continuous noise path. -/
def permutedPath {d N : ℕ} {T : ℝ} (e : Equiv.Perm (Fin N))
    (w : C(Icc 0 T, Configuration d N)) : C(Icc 0 T, Configuration d N) :=
  ⟨fun t => configurationPermutation e (w t),
    (configurationPermutation e).continuous.comp w.continuous⟩

theorem permutedPath_continuous {d N : ℕ} {T : ℝ} (e : Equiv.Perm (Fin N)) :
    Continuous (permutedPath (d := d) (T := T) e) :=
  ContinuousMap.continuous_postcomp ⟨configurationPermutation e,
    (configurationPermutation e).continuous⟩

namespace ParticleFlow

variable {d N : ℕ} {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
  (hN : 0 < N) (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
  (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)

/-- Covariance is obtained from integral-equation uniqueness, not assumed of
the selected solution map. -/
theorem solution_permutation {T : ℝ} (hT : 0 ≤ T) (e : Equiv.Perm (Fin N))
    (x : Configuration d N) (w : C(Icc 0 T, Configuration d N))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    solution hN hb hbound hM hL₁ hL₂ hT (configurationPermutation e x) (permutedPath e w) t =
      configurationPermutation e (solution hN hb hbound hM hL₁ hL₂ hT x w t) := by
  apply solution_unique hN hb hbound hM hL₁ hL₂ hT _ _
    (X := fun s => configurationPermutation e (solution hN hb hbound hM hL₁ hL₂ hT x w s)) _ ht
  have h := (solution_trajectory hN hb hbound hM hL₁ hL₂ hT x w).map_equiv
    (configurationPermutation e)
  have hv : (fun (_ : ℝ) y => configurationPermutation e
      (particleDrift b ((configurationPermutation e).symm y))) = (fun _ => particleDrift b) := by
    funext s y
    exact particleDrift_permutation_conjugate b e y
  rw [hv] at h
  exact h

/-- Exchangeable initial data and permutation-invariant noise give an
exchangeable particle law at every time in the constructed interval. -/
theorem law_exchangeable {T : ℝ}
    [MeasurableSpace C(Icc 0 T, Configuration d N)] [BorelSpace C(Icc 0 T, Configuration d N)]
    (hT : 0 ≤ T) (μ : Measure (Configuration d N))
    (ξ : Measure C(Icc 0 T, Configuration d N))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ξ]
    (hμ : Exchangeable μ)
    (hξ : ∀ e : Equiv.Perm (Fin N), Measure.map (permutedPath e) ξ = ξ)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    Exchangeable (law hN hb hbound hM hL₁ hL₂ hT μ ξ t) := by
  intro e
  let F : Configuration d N × C(Icc 0 T, Configuration d N) → Configuration d N :=
    fun p => solution hN hb hbound hM hL₁ hL₂ hT p.1 p.2 t
  have hF : Measurable F := solution_measurable hN hb hbound hM hL₁ hL₂ hT ht
  have he : Measurable (configurationPermutation (d := d) e) :=
    (configurationPermutation e).continuous.measurable
  have hew : Measurable (permutedPath (d := d) (T := T) e) :=
    (permutedPath_continuous e).measurable
  have hpair : Measure.map (Prod.map (configurationPermutation e) (permutedPath e)) (μ.prod ξ) =
      μ.prod ξ := by
    rw [← Measure.map_prod_map μ ξ he hew, hξ e]
    change (Measure.map (fun x i => x (e i)) μ).prod ξ = μ.prod ξ
    rw [hμ e]
  change Measure.map (configurationPermutation e) (Measure.map F (μ.prod ξ)) =
    Measure.map F (μ.prod ξ)
  rw [Measure.map_map he hF]
  have hfun : configurationPermutation e ∘ F =
      F ∘ Prod.map (configurationPermutation e) (permutedPath e) := by
    funext p
    exact (solution_permutation hN hb hbound hM hL₁ hL₂ hT e p.1 p.2 ht).symm
  rw [hfun, ← Measure.map_map hF (he.prodMap hew), hpair]

end ParticleFlow
end SharpWasserstein
