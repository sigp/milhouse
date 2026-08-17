import Lake
open Lake DSL

-- Path to a checkout of https://github.com/AeneasVerif/aeneas with the Lean
-- backend; override with `lake build -Kaeneas=/path/to/aeneas/backends/lean`
-- if it does not sit next to the milhouse repository.
require aeneas from
  (get_config? aeneas |>.getD "../../aeneas/backends/lean")

package «tree» {}

@[default_target] lean_lib Tree
