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

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"