# Vendored: brownian-motion

Source: https://github.com/RemyDegenne/brownian-motion at commit `0d5b6eb928e616d3b1f774ad7d233c167d9f42c9`
(Apache License 2.0, see `LICENSE` in this directory; authors as listed in each file header).

Only the import closure of `BrownianMotion.Gaussian.BrownianMotion` is kept. The files were adapted
to Mathlib `v4.35.0-rc3`: declarations that have since been upstreamed to Mathlib were removed in
favour of the Mathlib versions, and the construction is stated with Mathlib's
`ProbabilityTheory.IsBrownianReal`. Modified files say so in their header.
