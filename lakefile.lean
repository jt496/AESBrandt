import Lake
open Lake DSL

package «aES_Brandt» {
  -- add any package configuration options here
}

require "leanprover-community" / "mathlib"

@[default_target]
lean_lib «AESBrandt» {
  -- add any library configuration options here
}
