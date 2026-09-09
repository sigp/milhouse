#!/usr/bin/env python3
"""Run via lake env; compile only the separately extracted control functions."""

import os
import shutil
import subprocess
import sys
from pathlib import Path


def main():
    if len(sys.argv) != 2:
        print("Usage: lake env python3 check_controls.py GENERATED_ROOT", file=sys.stderr)
        return 1
    root = Path(sys.argv[1]).resolve()
    env = os.environ.copy()
    env["LEAN_PATH"] = str(root) + os.pathsep + env.get("LEAN_PATH", "")
    source = Path(__file__).with_name("CheckControls.lean")
    shutil.copyfile(source, root / source.name)
    for name in ["ControlsOnly/Types", "ControlsOnly/Funs", "CheckControls"]:
        result = subprocess.run(
            ["lean", "-o", name + ".olean", name + ".lean"],
            cwd=root, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        )
        print(result.stdout, end="")
        if result.returncode:
            return result.returncode
        if name == "CheckControls":
            for theorem in ["read_plain_value", "read_nested_value",
                            "read_shared_field_value", "read_unique_field_value"]:
                expected = f"'{theorem}' does not depend on any axioms"
                if expected not in result.stdout:
                    print(f"Missing axiom-free control proof: {theorem}", file=sys.stderr)
                    return 1
    print("All four separately extracted control bodies validate without axioms")
    return 0


if __name__ == "__main__":
    sys.exit(main())
