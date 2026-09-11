#!/usr/bin/env python3
"""Install the pinned official Aeneas bundle in the project's ignored cache."""

import argparse
import hashlib
import json
import platform
import shutil
import subprocess
import sys
import tarfile
import tempfile
import urllib.request
from pathlib import Path


REPO = Path(__file__).resolve().parent.parent
PIN_PATH = REPO / "aeneas-toolchain.json"


def load_pin():
    return json.loads(PIN_PATH.read_text())


def default_bundle(repo=REPO):
    return repo / "aeneas-lean/.lake/aeneas"


def check_bundle(bundle, pin):
    for executable, argument, expected in [
        ("aeneas", "-version", pin["aeneasVersion"]),
        ("charon", "version", pin["charonVersion"]),
        ("charon", "toolchain-version", pin["rustToolchain"]),
    ]:
        actual = subprocess.check_output([str(bundle / executable), argument], text=True).strip()
        if actual != expected:
            raise ValueError(f"Unexpected {executable} {argument}: {actual}")
    if (bundle / "backends/lean/lean-toolchain").read_text().strip() != pin["leanToolchain"]:
        raise ValueError("Unexpected Lean backend toolchain")
    if not (bundle / "charon-driver").is_file():
        raise ValueError("The Charon driver is missing")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive", type=Path, help="Use an already downloaded archive; its digest is still checked")
    parser.add_argument("--check", action="store_true", help="Check the installed bundle without downloading")
    args = parser.parse_args()
    if platform.system() != "Linux" or platform.machine() != "x86_64":
        raise ValueError("This official bundle requires Linux x86_64; use explicit compiler/backend paths on other hosts")
    pin = load_pin()
    destination = default_bundle()
    if destination.exists():
        if json.loads((destination / "milhouse-toolchain.json").read_text()) != pin:
            raise ValueError(f"A different bundle is installed; move {destination} aside before installing")
        check_bundle(destination, pin)
    elif args.check:
        raise ValueError(f"Bundle is not installed at {destination}; run this script without --check")
    else:
        destination.parent.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(prefix="aeneas-install-", dir=destination.parent) as temporary:
            work = Path(temporary)
            archive = args.archive.resolve() if args.archive else work / "release.tar.gz"
            if not args.archive:
                print(f"Downloading {pin['archiveUrl']}", flush=True)
                with urllib.request.urlopen(pin["archiveUrl"]) as response, archive.open("wb") as output:
                    shutil.copyfileobj(response, output)
            with archive.open("rb") as source:
                digest = hashlib.file_digest(source, "sha256").hexdigest()
            if digest != pin["archiveSha256"]:
                raise ValueError(f"Archive SHA-256 mismatch: {digest}")
            unpacked = work / "bundle"
            unpacked.mkdir()
            with tarfile.open(archive, "r:gz") as source:
                source.extractall(unpacked, filter="data")
            check_bundle(unpacked, pin)
            (unpacked / "milhouse-toolchain.json").write_text(json.dumps(pin, indent=2) + "\n")
            unpacked.rename(destination)
    print(f"Verified {pin['aeneasVersion']} at {destination}")
    print(f"Rust components required separately: rustc-dev, rust-src, llvm-tools, miri, rustfmt ({pin['rustToolchain']})")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, tarfile.TarError, subprocess.SubprocessError) as error:
        print(f"Aeneas setup failed: {error}", file=sys.stderr)
        sys.exit(1)
