#!/usr/bin/env python3
"""Download and extract parser headers locally, without installing system packages.

Run with: uv run python pipeline/setup_clang_parser.py
Uses configured apt repositories and their SHA-256/SHA-512 metadata. Downloads
Clang headers matching the Python libclang and x86_64 Linux development headers.
Only dpkg-deb extraction is performed; package maintainer scripts are not run.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import shlex
import shutil
import subprocess
import tempfile
import urllib.request
from importlib.metadata import version
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUTPUT = ROOT / "tools/.cache/c2r-clang"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()
    for tool in ("apt-get", "dpkg-deb"):
        if shutil.which(tool) is None:
            raise SystemExit(f"{tool} is required for this setup helper.")
    libclang_version = version("libclang")
    major = libclang_version.split(".", 1)[0]
    output = args.output.expanduser().resolve() / f"libclang-{libclang_version}"
    destination = output / "root"
    metadata_path = output / "metadata.json"
    if metadata_path.is_file():
        saved = json.loads(metadata_path.read_text())
        if ((Path(saved["resource_include"]) / "stddef.h").is_file()
                and (Path(saved["x86_include"]) / "sys/mman.h").is_file()):
            print(f"Parser headers already available: {metadata_path}")
            return 0
    if destination.exists():
        raise SystemExit(f"Incomplete setup at {destination}; choose another --output directory.")
    downloads = output / "downloads"
    downloads.mkdir(parents=True, exist_ok=True)
    packages = [f"libclang-common-{major}-dev", "libc6-dev-amd64-cross", "linux-libc-dev-amd64-cross"]
    records = []
    with tempfile.TemporaryDirectory(prefix=".extract-", dir=output) as temporary:
        extracted = Path(temporary) / "root"
        extracted.mkdir()
        for package in packages:
            result = subprocess.run(["apt-get", "--print-uris", "download", package],
                                    check=True, capture_output=True, text=True)
            entries = [shlex.split(line) for line in result.stdout.splitlines()
                       if line.startswith("'")]
            if len(entries) != 1 or len(entries[0]) != 4:
                raise RuntimeError(f"Expected one apt download URI for {package}: {result.stdout}")
            url, filename, size, checksum = entries[0]
            algorithm, separator, expected = checksum.partition(":")
            if Path(filename).name != filename or not separator or algorithm not in {"SHA256", "SHA512"}:
                raise RuntimeError(f"Unsupported package metadata for {package}")
            algorithm, expected = algorithm.lower(), expected.lower()
            target = downloads / filename
            if not target.is_file() or hashlib.new(algorithm, target.read_bytes()).hexdigest() != expected:
                with urllib.request.urlopen(url.replace("http://", "https://", 1), timeout=120) as response:
                    with target.open("wb") as stream:
                        shutil.copyfileobj(response, stream)
            if target.stat().st_size != int(size) or hashlib.new(algorithm, target.read_bytes()).hexdigest() != expected:
                raise RuntimeError(f"Package integrity check failed: {package}")
            subprocess.run(["dpkg-deb", "--extract", str(target), str(extracted)], check=True)
            records.append({"package": package, "url": url, "filename": filename,
                            algorithm: expected, "size": int(size)})
            print(f"Extracted locally: {package}", flush=True)
        resources = sorted((extracted / "usr/lib" / f"llvm-{major}" / "lib/clang").glob("*/include"))
        resources = [path for path in resources if (path / "stddef.h").is_file()]
        x86_include = extracted / "usr/x86_64-linux-gnu/include"
        if len(resources) != 1 or not (x86_include / "sys/mman.h").is_file():
            raise RuntimeError("Downloaded packages do not contain the expected parser headers")
        resource_relative = resources[0].relative_to(extracted)
        x86_relative = x86_include.relative_to(extracted)
        extracted.replace(destination)
    metadata = {"libclang_version": libclang_version,
                "resource_include": str(destination / resource_relative),
                "x86_include": str(destination / x86_relative), "packages": records}
    metadata_path.write_text(json.dumps(metadata, indent=2) + "\n")
    print(f"Parser headers ready: {metadata_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
