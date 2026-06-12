#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import json
import re

ROOT = Path(__file__).resolve().parents[1]
SCAN_DIRS = [ROOT / "Iris", ROOT / "IrisMath"]
EXCLUDED_PARTS = {".git", ".lake", "lake-packages", "build"}

TOKENS = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "axiom": re.compile(r"\baxiom\b"),
    "opaque": re.compile(r"\bopaque\b"),
    "unsafe": re.compile(r"\bunsafe\b"),
}

def strip_comments(src: str) -> str:
    out: list[str] = []
    i = 0
    depth = 0
    while i < len(src):
        if depth == 0 and src.startswith("--", i):
            j = src.find("\n", i)
            if j == -1:
                break
            out.append("\n")
            i = j + 1
        elif src.startswith("/-", i):
            depth += 1
            out.append(" ")
            i += 2
        elif depth > 0 and src.startswith("-/", i):
            depth -= 1
            out.append(" ")
            i += 2
        elif depth > 0:
            out.append("\n" if src[i] == "\n" else " ")
            i += 1
        else:
            out.append(src[i])
            i += 1
    return "".join(out)

def lean_files() -> list[Path]:
    files: list[Path] = []
    for base in SCAN_DIRS:
        if base.exists():
            for path in base.rglob("*.lean"):
                if not EXCLUDED_PARTS.intersection(path.parts):
                    files.append(path)
    return sorted(files)

def main() -> int:
    findings: list[dict[str, object]] = []
    for path in lean_files():
        cleaned = strip_comments(path.read_text(encoding="utf-8"))
        for lineno, line in enumerate(cleaned.splitlines(), start=1):
            for token, pattern in TOKENS.items():
                if pattern.search(line):
                    findings.append({
                        "file": str(path.relative_to(ROOT)),
                        "line": lineno,
                        "token": token,
                        "text": line.strip(),
                    })

    proof_debt = [f for f in findings if f["token"] in {"sorry", "admit", "axiom", "opaque"}]
    unsafe = [f for f in findings if f["token"] == "unsafe"]

    report = {
        "repository": "leanprover-community/iris-lean",
        "audit": "block_comment_aware_visible_proof_debt_surface",
        "scanned_roots": [str(p.relative_to(ROOT)) for p in SCAN_DIRS if p.exists()],
        "proof_debt_tokens": ["sorry", "admit", "axiom", "opaque"],
        "unsafe_token": "unsafe",
        "proof_debt_findings": proof_debt,
        "unsafe_findings": unsafe,
        "status": "NO_ACTIVE_SORRY_ADMIT_AXIOM_OPAQUE_SURFACE" if not proof_debt else "ACTIVE_PROOF_DEBT_SURFACE_FOUND",
    }

    out = ROOT / "docs" / "status" / "proof_debt_surface_audit_latest.json"
    out.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    print(report["status"])
    print(f"unsafe_findings={len(unsafe)}")
    print(f"wrote={out.relative_to(ROOT)}")

    return 0 if not proof_debt else 1

if __name__ == "__main__":
    raise SystemExit(main())
