#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
OUT_ZIP="${1:-oeis-a245211-v1.1.0.zip}"
ARCHIVE_ROOT="oeis-a245211-v1.1.0"

python3 - "${REPO_ROOT}" "${OUT_ZIP}" "${ARCHIVE_ROOT}" <<'PYEOF'
import os
import sys
import zipfile
from pathlib import Path

repo_root = Path(sys.argv[1]).resolve()
out_zip = Path(sys.argv[2]).resolve()
archive_root = sys.argv[3]

out_zip.parent.mkdir(parents=True, exist_ok=True)
if out_zip.exists():
    out_zip.unlink()

excluded_names = {
    ".git",
    ".lake",
    "__pycache__",
    ".DS_Store",
}
excluded_suffixes = {
    ".aux",
    ".fdb_latexmk",
    ".fls",
    ".log",
    ".out",
    ".synctex.gz",
    ".toc",
    ".zip",
}

def should_include(path: Path) -> bool:
    for part in path.parts:
        if part in excluded_names:
            return False
    if path.suffix in excluded_suffixes:
        return False
    return True

include_dirs = [
    "lean/oeis-a245211",
    "docs/oeis-a245211",
    "design",
]
include_files = [
    ("lean/oeis-a245211/CITATION.cff", f"{archive_root}/CITATION.cff"),
    ("lean/oeis-a245211/.zenodo.json", f"{archive_root}/.zenodo.json"),
    ("lean/oeis-a245211/LICENSE", f"{archive_root}/LICENSE"),
    ("lean/oeis-a245211/NOTICE", f"{archive_root}/NOTICE"),
    ("solver/a245211_search.py", f"{archive_root}/solver/a245211_search.py"),
    ("solver/README.md", f"{archive_root}/solver/README.md"),
]

written = []
with zipfile.ZipFile(out_zip, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as zf:
    for rel_src, arc_dst in include_files:
        src = repo_root / rel_src
        if not src.is_file():
            raise FileNotFoundError(f"Missing required release file: {src}")
        zf.write(src, arc_dst)
        written.append(arc_dst)

    for rel_dir in include_dirs:
        base = repo_root / rel_dir
        if not base.is_dir():
            raise FileNotFoundError(f"Missing required release directory: {base}")
        for root, dirs, files in os.walk(base):
            dirs[:] = sorted(d for d in dirs if d not in excluded_names)
            for fname in sorted(files):
                fpath = Path(root) / fname
                rel = fpath.relative_to(repo_root)
                if not should_include(rel):
                    continue
                arcname = f"{archive_root}/{rel.as_posix()}"
                zf.write(fpath, arcname)
                written.append(arcname)

print(f"Created {out_zip} ({out_zip.stat().st_size} bytes, {len(written)} files)")
PYEOF
