import Lake
open Lake DSL

package «first-order-modal-logic» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «FirstOrderModalLogic» {
  roots := #[`src]
}
