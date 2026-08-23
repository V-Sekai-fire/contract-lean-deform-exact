-- SPDX-License-Identifier: MIT
-- Copyright (c) 2026-present K. S. Ernest (iFire) Lee

import Lake
open Lake DSL

package «lean-deform-exact» where

-- Pinned to the toolchain, matching `truth_research_zk` and `lean-humanoid-rom`. A proof
-- that only builds against a moving Mathlib is a proof nobody can re-check.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.30.0"

@[default_target]
lean_lib «DeformExact» where
  roots := #[`DeformExact]
