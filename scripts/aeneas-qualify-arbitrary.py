"""Disambiguate generated Arbitrary field types without changing the interface."""

import re
import sys
from pathlib import Path


path = Path(sys.argv[1])
source = path.read_text()
pattern = r"(structure arbitrary\.Arbitrary \(Self : Type\) where\n)(.*?)(?=\n\n)"


def qualify(match: re.Match[str]) -> str:
    fields = match[2]
    for old, new in (
        ("arbitrary.unstructured.Unstructured", "_root_.arbitrary.unstructured.Unstructured"),
        ("arbitrary.error.Error", "milhouse.arbitrary.error.Error"),
        ("arbitrary.MaxRecursionReached", "_root_.arbitrary.MaxRecursionReached"),
    ):
        fields = re.sub(r"(?<![\w.])" + re.escape(old), new, fields)
    return match[1] + fields


result, count = re.subn(pattern, qualify, source, flags=re.DOTALL)
if count != 1:
    raise SystemExit(f"Expected exactly one generated Arbitrary trait, found {count}")
path.write_text(result)
