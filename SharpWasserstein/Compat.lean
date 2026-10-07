/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Compatibility lemmas

Statements that were available under these names in the Mathlib revision the development was
first written against. They are proved here from the current Mathlib API.
-/

@[expose] public section

namespace MeasureTheory.Measure

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- The image of a probability measure is a probability measure. -/
theorem isProbabilityMeasure_map {μ : Measure α} [IsProbabilityMeasure μ] {f : α → β}
    (_hf : AEMeasurable f μ) : IsProbabilityMeasure (μ.map f) :=
  inferInstance

end MeasureTheory.Measure
