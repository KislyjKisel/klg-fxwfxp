import Lake
open Lake DSL

require pod from git
  "https://github.com/KislyjKisel/lean-pod" @ "main"

require «nest-core» from git
  "https://github.com/hargonix/nest-core" @ "main"

require «nest-unit» from git
  "https://github.com/hargonix/nest-unit" @ "main"

package «klg-fxwfxp» where
  moreLeanArgs := #["-DautoImplicit=false"]
  moreServerArgs := #["-DautoImplicit=false"]

lean_lib Klg.Fixed32
lean_lib Klg.Fixed64

@[default_target]
lean_exe Tests
