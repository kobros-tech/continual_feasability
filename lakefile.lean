import Lake
open Lake DSL

package «continual_feasibility» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.36.0"

@[default_target]
lean_lib ContinualFeasibility

lean_lib Tests
