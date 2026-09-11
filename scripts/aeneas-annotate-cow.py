#!/usr/bin/env python3
"""Supply the type of an unconstrained continuation in CowOnMut.run."""

import sys
from pathlib import Path


def main() -> int:
    path = Path(sys.argv[1])
    source = path.read_text()
    start = source.index("def cow.CowOnMut.run\n")
    end = source.index("\npartial_fixpoint", start)
    body = source[start:end]
    untyped = "| none => ok (none, fun o1 => none)"
    typed = ("| none => ok (none, fun (o1 : Option cow.CowOnMut) => "
             "(none : Option cow.CowOnMut))")
    if body.count(untyped) != 1:
        raise ValueError("Expected exactly one untyped empty-chain continuation")
    path.write_text(source[:start] + body.replace(untyped, typed) + source[end:])
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except Exception as error:
        print(f"CoW continuation annotation failed: {error}", file=sys.stderr)
        sys.exit(1)
