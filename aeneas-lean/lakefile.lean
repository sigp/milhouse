import Lake
open Lake DSL

-- Install the pinned official bundle with `python3 scripts/aeneas_toolchain.py`
-- from the repository root. An explicit backend path remains available with
-- `lake build -Kaeneas=/path/to/aeneas/backends/lean`.
require aeneas from
  (get_config? aeneas |>.getD ".lake/aeneas/backends/lean")

package «tree» {}

@[default_target] lean_lib Tree
