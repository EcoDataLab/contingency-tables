import Lake

open Lake DSL

package Math115 where
  version := v!"0.1.0"
  fixedToolchain := true
  leanOptions := #[⟨`autoImplicit, false⟩]

-- Match the reviewed OpenAI snapshot.  The focused harness avoids resolving
-- unrelated manuscript dependencies; it does not edit any upstream source.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "d13f23b723b8a846827a245b89c10fc7d3f11612"

lean_lib OAI where
  srcDir := "../.upstream/openai-math/lean"
  globs := #[`OAI.+]

lean_lib ComparatorChallenges where
  srcDir := "../.upstream/openai-math/lean"
  globs := #[`ComparatorChallenges.+]

@[default_target] lean_lib Math115
