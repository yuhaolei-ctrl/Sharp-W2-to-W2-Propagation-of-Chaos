import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Def
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Independence.CharacteristicFunction
open MeasureTheory ContinuousLinearMap
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
example (L : StrongDual ℝ E →L[ℝ] StrongDual ℝ E →L[ℝ] ℝ) : ℝ := by
  letI : NormedAddCommGroup (StrongDual ℝ E) := inferInstance
  exact ‖L‖
example (L : StrongDual ℝ E →L[ℝ] StrongDual ℝ E →L[ℝ] ℝ) : ℝ := by
  letI : NormedAddCommGroup (StrongDual ℝ E →L[ℝ] ℝ) := inferInstance
  exact ‖L‖
example (L : StrongDual ℝ E →L[ℝ] StrongDual ℝ E →L[ℝ] ℝ) : ℝ := by
  letI : NormedSpace ℝ (StrongDual ℝ E →L[ℝ] ℝ) := inferInstance
  exact ‖L‖
