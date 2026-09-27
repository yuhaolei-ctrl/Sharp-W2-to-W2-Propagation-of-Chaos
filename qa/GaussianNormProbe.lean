import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Def
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Independence.CharacteristicFunction
open MeasureTheory ContinuousLinearMap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
#synth NormedAddCommGroup (StrongDual ℝ E)
#synth NormedSpace ℝ (StrongDual ℝ E)
#synth Norm (StrongDual ℝ E →L[ℝ] ℝ)
#synth NormedSpace ℝ (StrongDual ℝ E →L[ℝ] ℝ)
#synth Norm (StrongDual ℝ E →L[ℝ] StrongDual ℝ E →L[ℝ] ℝ)
set_option trace.Meta.synthInstance true in
example (L : StrongDual ℝ E →L[ℝ] StrongDual ℝ E →L[ℝ] ℝ) : ℝ := ‖L‖
