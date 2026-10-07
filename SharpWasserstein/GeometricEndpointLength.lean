module

public import SharpWasserstein.Compat
public import SharpWasserstein.TransportTriangle
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-! Summing genuine finite-action bounds on geometrically shrinking intervals
removes the nonintegrable energy singularity 1/s. The resulting length is finite
and proportional to K, without assuming a metric derivative or a Lagrangian
representation of the original curve. -/
noncomputable section
open Set Filter
open scoped Topology
namespace SharpWasserstein.GeometricEndpointLength
variable {X : Type*} [PseudoMetricSpace X]

def time (T : ℝ) (n : ℕ) : ℝ := T*(1/4:ℝ)^n
theorem time_pos {T : ℝ} (hT : 0 < T) (n : ℕ) : 0 < time T n := by
  unfold time
  positivity
theorem time_le {T : ℝ} (hT : 0 ≤ T) (n : ℕ) : time T n ≤ T := by
  exact mul_le_of_le_one_right hT (pow_le_one₀ (by norm_num) (by norm_num))
theorem time_succ (T : ℝ) (n : ℕ) : 4*time T (n+1)=time T n := by
  unfold time
  rw [pow_succ]
  ring
theorem sqrt_time_succ (T : ℝ) (n : ℕ) :
    2*Real.sqrt (time T (n+1))=Real.sqrt (time T n) := by
  have he := time_succ T n
  have h4 : Real.sqrt (4:ℝ)=2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 4),Real.sqrt_nonneg (4:ℝ)]
  rw [← he,Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4),h4]

/-- An elementary finite-action estimate on each interval [a,4a] suffices
for the endpoint length bound, even though the corresponding energy behaves
like 1/a near zero. The constant remains independent of all particle counts. -/
theorem endpoint_of_geometric_action {f : ℝ → X} {T K : ℝ}
    (hT : 0 < T) (hK : 0 ≤ K) (hc : ContinuousWithinAt f (Icc 0 T) 0)
    (haction : ∀ a,0 < a → 4*a ≤ T →
      dist (f a) (f (4*a))^2 ≤ 9*K^2*(a^2+a)) :
    dist (f 0) (f T) ≤ K*(T+3*Real.sqrt T) := by
  have hstep (a : ℝ) (ha : 0 < a) (haT : 4*a ≤ T) :
      dist (f a) (f (4*a)) ≤ 3*K*(a+Real.sqrt a) := by
    apply (sq_le_sq₀ dist_nonneg (by positivity)).mp
    have hs : a^2+a ≤ (a+Real.sqrt a)^2 := by
      nlinarith [Real.sq_sqrt ha.le,Real.sqrt_nonneg a]
    calc
      _ ≤ 9*K^2*(a^2+a) := haction a ha haT
      _ ≤ 9*K^2*(a+Real.sqrt a)^2 := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by ring
  have hb (n : ℕ) :
      dist (f (time T n)) (f T) ≤ K*(T+3*Real.sqrt T)-K*(time T n+3*Real.sqrt (time T n)) := by
    induction n with
    | zero => simp [time]
    | succ n ih =>
      have ht := time_succ T n
      have hs := sqrt_time_succ T n
      have hh := hstep (time T (n+1)) (time_pos hT _) (ht ▸ time_le hT.le n)
      rw [ht] at hh
      calc
        _ ≤ dist (f (time T (n+1))) (f (time T n))+dist (f (time T n)) (f T) := dist_triangle _ _ _
        _ ≤ 3*K*(time T (n+1)+Real.sqrt (time T (n+1)))+
            (K*(T+3*Real.sqrt T)-K*(time T n+3*Real.sqrt (time T n))) := add_le_add hh ih
        _ = _ := by nlinarith
  have hz : Tendsto (fun n => time T n) atTop (𝓝 0) := by
    simpa only [time,mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/4) (by norm_num)).const_mul T
  have hz' : Tendsto (fun n => time T n) atTop (𝓝[Icc 0 T] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hz,Eventually.of_forall fun n => ⟨(time_pos hT n).le,time_le hT.le n⟩⟩
  have hd := (hc.tendsto.comp hz').dist (tendsto_const_nhds (x := f T))
  exact le_of_tendsto hd (Eventually.of_forall fun n => (hb n).trans
    (sub_le_self _ (mul_nonneg hK (by positivity [time_pos hT n]))))

/-- Uniform local finite-action control with the 1/a singularity gives the
complete endpoint estimate by the proved geometric summation. -/
theorem endpoint_of_local_action {f : ℝ → X} {T K : ℝ}
    (hT : 0 < T) (hK : 0 ≤ K) (hc : ContinuousWithinAt f (Icc 0 T) 0)
    (haction : ∀ a b,0 < a → a ≤ b → b ≤ T →
      dist (f a) (f b)^2 ≤ K^2*(b-a)^2*(1+1/a)) :
    dist (f 0) (f T) ≤ K*(T+3*Real.sqrt T) := by
  apply endpoint_of_geometric_action hT hK hc
  intro a ha haT
  have hh := haction a (4*a) ha (by linarith) haT
  convert hh using 1
  field_simp
  ring

end SharpWasserstein.GeometricEndpointLength
