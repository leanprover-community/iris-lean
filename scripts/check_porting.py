#!/usr/bin/env python3
"""
Iris-Lean Porting Completeness Checker

Compares Iris-Rocq definitions against Iris-Lean's @[rocq_alias] annotations
to track porting progress.

Usage:
  python3 scripts/check_porting.py [options]

Options:
  --format summary|csv|html   Output format (default: summary)
  --output PATH               Output file path
  --rocq-commit SHA           Iris-Rocq revision to check against
  --no-build                  Skip running lake exe dumpPortingData
  --cache-dir DIR             Cache directory (default: .lake/iris-rocq-cache)
"""

from __future__ import annotations

import argparse
import csv
import io
import json
import os
import re
import subprocess
import sys
import tarfile
import urllib.request
from collections import defaultdict
from dataclasses import dataclass, field
from pathlib import Path

# ============================================================================
# Configuration
# ============================================================================

DEFAULT_ROCQ_REVISION = (Path(__file__).parent / "ROCQ_REVISION").read_text().strip()

# Iris-Rocq is hosted on the MPI-SWS GitLab instance.
GITLAB_PROJECT_ID = "iris%2Firis"  # URL-encoded "iris/iris"
GITLAB_API_BASE = "https://gitlab.mpi-sws.org/api/v4"
GITLAB_WEB_BASE = "https://gitlab.mpi-sws.org/iris/iris"
GITHUB_WEB_BASE = "https://github.com/leanprover-community/iris-lean"

# Within the Iris-Rocq tarball, source files live under this prefix.
ROCQ_SRC_PREFIX = "iris/"

# Directory prefixes (relative to ROCQ_SRC_PREFIX) to ignore entirely.
IGNORED_DIRS = ["prelude/", "deprecated/"]

# HTML report template, kept separate for readability.
TEMPLATE_PATH = Path(__file__).parent / "report_template.html"


def log(msg: str) -> None:
    print(msg, file=sys.stderr)



# ============================================================================
# Rocq Definition Parsing
# ============================================================================

# Rocq vernacular keywords that introduce named definitions.
_DEF_KEYWORDS = (
    r"Definition|Lemma|Theorem|Instance|Class|Record|Structure|"
    r"Inductive|Fixpoint|CoFixpoint|Variant|Corollary|Proposition|"
    r"Fact|Remark|Example|Canonical\s+Structure"
)

# Matches a named definition line. Captures the identifier (group 1).
# Handles optional prefixes like "Global", "Local", "Program", "#[export]".
# Identifiers may contain apostrophes (e.g., csum_updateP'_l).
_DEF_RE = re.compile(
    rf"^\s*(?:(?:Global|Local|Program|#\[(?:export|global)\])\s+)*"
    rf"(?:{_DEF_KEYWORDS})\s+"
    rf"(\w[\w']*)",
    re.MULTILINE,
)

# Module/Section tracking: Modules qualify names (e.g., Module bi -> bi.foo),
# but Sections do not. 
_MODULE_START_RE = re.compile(r"^\s*Module\s+(\w+)", re.MULTILINE)
_MODULE_TYPE_RE = re.compile(r"^\s*Module\s+Type\b")  # Module Types are skipped
_SECTION_START_RE = re.compile(r"^\s*Section\s+(\w+)", re.MULTILINE)
_END_RE = re.compile(r"^\s*End\s+(\w+)\s*\.", re.MULTILINE)

# Lines starting with these keywords are not definitions and are skipped.
# This includes tactics (Ltac), notations, hints, scope commands, etc.
_SKIP_RE = re.compile(
    r"^\s*(?:Notation|Ltac|Ltac2|Tactic\s+Notation|Hint|Arguments|"
    r"Typeclasses\s+(?:Opaque|Transparent)|"
    r"Existing\s+Instance|Params|"
    r"(?:Declare|Delimit|Bind|Open|Close)\s+Scope|"
    r"Coercion|Import|Export|Require|From|Set|Unset)\b"
)


def _strip_comments(text: str) -> str:
    """Remove nested Rocq (* ... *) comments.

    Rocq comments nest, so (* (* inner *) outer *) is one comment.
    We strip them to avoid picking up commented-out definitions.
    """
    out: list[str] = []
    depth = 0
    i = 0
    while i < len(text):
        if text[i : i + 2] == "(*":
            depth += 1
            i += 2
        elif text[i : i + 2] == "*)" and depth > 0:
            depth -= 1
            i += 2
        elif depth == 0:
            out.append(text[i])
            i += 1
        else:
            i += 1
    return "".join(out)


def parse_rocq_file(text: str) -> list[str]:
    """Extract fully-qualified definition names from a Rocq .v file.

    Module prefixes are included; Section prefixes are not.
    """
    text = _strip_comments(text)

    names: list[str] = []
    module_stack: list[str] = []  # current Module nesting, used for name qualification
    section_names: set[str] = set()  # track Section names so End can distinguish them

    for line in text.split("\n"):
        # Track Module open (but not Module Type, which is a signature)
        if m := _MODULE_START_RE.match(line):
            if not _MODULE_TYPE_RE.match(line):
                module_stack.append(m.group(1))
            continue

        # Track Section open (for disambiguation on End)
        if m := _SECTION_START_RE.match(line):
            section_names.add(m.group(1))
            continue

        # Handle End: pop Section or Module depending on which name matches
        if m := _END_RE.match(line):
            name = m.group(1)
            if name in section_names:
                section_names.discard(name)
            elif module_stack and module_stack[-1] == name:
                module_stack.pop()
            continue

        # Skip non-definition vernacular (tactics, notations, imports, etc.)
        if _SKIP_RE.match(line):
            continue

        # Extract definition name and qualify with Module prefix
        if m := _DEF_RE.match(line):
            ident = m.group(1)
            qualified = ".".join([*module_stack, ident]) if module_stack else ident
            names.append(qualified)

    return names


# ============================================================================
# Iris-Rocq Download and Cache
# ============================================================================

def _resolve_commit(ref: str) -> str:
    """Resolve a Git ref (branch, tag, or SHA) to a full commit SHA via GitLab API."""
    url = f"{GITLAB_API_BASE}/projects/{GITLAB_PROJECT_ID}/repository/commits/{ref}"
    try:
        with urllib.request.urlopen(url, timeout=30) as resp:
            return json.loads(resp.read())["id"]
    except Exception:
        log(f"Warning: could not resolve ref '{ref}', use default")
        return ref

def download_iris_rocq(commit: str, cache_dir: Path) -> tuple[dict[str, list[str]], str]:
    """Download and parse Iris-Rocq definitions, caching the result as JSON.

    The tarball is downloaded from the GitLab archive API, parsed for all .v
    files under iris/, and the extracted definitions are cached as JSON keyed
    by the resolved commit SHA. Subsequent calls with the same SHA hit the cache.

    Returns (file_path -> definition_names, resolved_commit_sha).
    """
    # Always resolve to a concrete SHA so branch names get pinned in the cache.
    resolved = _resolve_commit(commit)
    if resolved != commit:
        log(f"Resolved '{commit}' -> {resolved}")

    cache_file = cache_dir / resolved / "rocq_definitions.json"
    if cache_file.exists():
        log(f"Using cached Rocq definitions from {cache_file}")
        with open(cache_file) as f:
            return json.load(f), resolved

    # Download the tarball from GitLab.
    log(f"Downloading Iris-Rocq at {resolved}...")
    url = (
        f"{GITLAB_API_BASE}/projects/{GITLAB_PROJECT_ID}"
        f"/repository/archive.tar.gz?sha={resolved}"
    )
    with urllib.request.urlopen(url, timeout=120) as resp:
        tarball_data = resp.read()
    log(f"Downloaded {len(tarball_data) / 1024:.0f} KB, parsing...")

    # Parse every .v file under the iris/ source directory.
    definitions: dict[str, list[str]] = {}
    with tarfile.open(fileobj=io.BytesIO(tarball_data), mode="r:gz") as tf:
        for member in tf.getmembers():
            if not member.isfile() or not member.name.endswith(".v"):
                continue
            # The archive has a top-level directory (e.g., "iris-master-SHA/").
            parts = member.name.split("/", 1)
            if len(parts) < 2:
                continue
            rel_path = parts[1]
            if not rel_path.startswith(ROCQ_SRC_PREFIX):
                continue
            fobj = tf.extractfile(member)
            if fobj is None:
                continue
            defs = parse_rocq_file(fobj.read().decode("utf-8", errors="replace"))
            if defs:
                definitions[rel_path] = defs

    # Cache the parsed definitions so we don't re-download next time.
    cache_file.parent.mkdir(parents=True, exist_ok=True)
    with open(cache_file, "w") as f:
        json.dump(definitions, f, indent=2)

    total_defs = sum(len(v) for v in definitions.values())
    log(f"Parsed {total_defs} definitions from {len(definitions)} files")
    return definitions, resolved


# ============================================================================
# Lean Data
# ============================================================================

def run_lake_dump(output_path: str = ".lake/porting_data.json") -> None:
    """Run `lake exe dumpPortingData` to dump all Rocq.* aliases to JSON.

    The Lean executable scans the compiled environment for declarations in the
    Rocq namespace (created by @[rocq_alias]) and #rocq_ignore entries.
    """
    log("Running lake exe dumpPortingData...")
    result = subprocess.run(
        ["lake", "exe", "dumpPortingData", output_path],
        capture_output=True, text=True,
    )
    if result.returncode != 0:
        log(f"Error running lake exe dumpPortingData:\n{result.stderr}")
        sys.exit(1)
    log(result.stdout.strip())


@dataclass
class ConceptEntry:
    dir: str       # e.g. "proofmode/"
    feature: str   # e.g. "IPM Tactics"
    subfeature: str  # e.g. "iIntros" or "" for top-level
    status: str    # "ported" | "missing" | "blocked" | "unreachable" (should not happen)
    reason: str


@dataclass
class LeanData:
    aliases: dict[str, str]
    ignores: dict[str, str]
    ignored_files: dict[str, str]
    concepts: list[ConceptEntry]

def parse_status(status : str | dict[str, list[str]]) -> str:
    if type(status) is str:
        # ported | missing
        return status
    elif type(status) is dict and [*status.keys()][0] == "depends_on":
        # blocked
        return "blocked"
    else: # Should be unreachable
        return "unreachable"
    
def load_lean_data(json_path: str) -> LeanData:
    """Load Lean alias/ignore/concept data from the JSON dump."""
    with open(json_path) as f:
        data = json.load(f)
    aliases = {a["rocq"]: a["lean"] for a in data["aliases"]}
    ignores = {i["rocq"]: i["reason"] for i in data["ignores"]}
    ignored_files = {
        ROCQ_SRC_PREFIX + e["folder"] + "/" + e["file"]: e["reason"]
        for e in data.get("ignored_files", [])
    }
    concepts = [
        ConceptEntry(
            dir=c["folder"], feature=c["feature"],
            subfeature=c.get("subfeature") or "",
            status=parse_status(c["status"]), reason=c["reason"],
        )
        for c in data.get("concepts", [])
    ]
    return LeanData(aliases, ignores, ignored_files, concepts)


# ============================================================================
# Report
# ============================================================================

@dataclass
class ReportEntry:
    rocq_file: str
    rocq_name: str
    status: str  # "ported" | "ignored" | "missing" | "stale_alias" | "stale_ignore"
    lean_name: str = ""
    reason: str = ""


@dataclass
class Report:
    entries: list[ReportEntry] = field(default_factory=list)
    concepts: list[ConceptEntry] = field(default_factory=list)
    rocq_commit: str = ""
    lean_rev: str = ""
    total_rocq: int = 0

    def count(self, status: str) -> int:
        return sum(1 for e in self.entries if e.status == status)

    def by_status(self, status: str) -> list[ReportEntry]:
        return [e for e in self.entries if e.status == status]


def compute_report(
    rocq_defs: dict[str, list[str]],
    aliases: dict[str, str],
    ignores: dict[str, str],
    ignored_files: dict[str, str],
    concepts: list[ConceptEntry],
    rocq_commit: str,
    lean_rev: str = "Local",
) -> Report:
    """Classify each Rocq definition and produce a report.

    Each Rocq definition is classified as:
      - "ported":  has a matching @[rocq_alias] in Lean
      - "ignored": listed in #rocq_ignore or #rocq_ignore_file
      - "missing": exists in Rocq but has no alias or ignore entry

    Additionally, aliases/ignores that reference names not found in Rocq
    are flagged as "stale_alias" or "stale_ignore".
    """
    report = Report(rocq_commit=rocq_commit, lean_rev=lean_rev, concepts=concepts)

    # Flatten Rocq definitions: name -> source file path
    name_to_file: dict[str, str] = {}
    for filepath, names in rocq_defs.items():
        for name in names:
            name_to_file[name] = filepath
    report.total_rocq = len(name_to_file)

    # Classify each Rocq definition against Lean aliases and ignore lists
    for name, filepath in sorted(name_to_file.items()):
        if name in aliases:
            report.entries.append(ReportEntry(filepath, name, "ported", lean_name=aliases[name]))
        elif name in ignores or filepath in ignored_files or any(
            filepath.startswith(ROCQ_SRC_PREFIX + d) for d in IGNORED_DIRS
        ):
            if name in ignores:
                reason = ignores[name]
            elif filepath in ignored_files:
                reason = f"file ignored: {ignored_files[filepath]}"
            else:
                reason = f"directory ignored"
            report.entries.append(ReportEntry(filepath, name, "ignored", reason=reason))
        else:
            report.entries.append(ReportEntry(filepath, name, "missing"))

    # Detect stale entries: aliases or ignores pointing to names that
    # no longer exist in Rocq (possibly renamed or removed upstream).
    all_rocq = set(name_to_file)
    for name, lean_name in sorted(aliases.items()):
        if name not in all_rocq:
            report.entries.append(ReportEntry("", name, "stale_alias", lean_name=lean_name))
    for name, reason in sorted(ignores.items()):
        if name not in all_rocq:
            report.entries.append(ReportEntry("", name, "stale_ignore", reason=reason))

    return report


# ============================================================================
# Output: Summary
# ============================================================================

def output_summary(report: Report, out=sys.stdout) -> None:
    """Print a human-readable summary to the given stream."""
    p = lambda *a, **kw: print(*a, file=out, **kw)

    pct = report.count("ported") / report.total_rocq * 100 if report.total_rocq else 0

    p("=" * 60)
    p("Iris Porting Completeness Report")
    p("=" * 60)
    p(f"Rocq commit: {report.rocq_commit}")
    p(f"Total Rocq definitions: {report.total_rocq}")
    p(f"Ported (with rocq_alias): {report.count('ported')}")
    p(f"Ignored: {report.count('ignored')}")
    p(f"Missing: {report.count('missing')}")
    if n := report.count("stale_alias"):
        p(f"Stale aliases: {n}")
    if n := report.count("stale_ignore"):
        p(f"Stale ignores: {n}")
    p(f"\nProgress: {pct:.1f}%")

    # Per-file breakdown
    files: dict[str, dict[str, int]] = defaultdict(lambda: defaultdict(int))
    for e in report.entries:
        if e.rocq_file:
            files[e.rocq_file][e.status] += 1

    p(f"\nPer-file breakdown:")
    p("-" * 60)
    for filepath in sorted(files):
        counts = files[filepath]
        total = sum(counts.values())
        done = counts.get("ported", 0) + counts.get("ignored", 0)
        file_pct = done / total * 100 if total else 0
        parts = [f"{counts[s]} {s}" for s in ("ported", "ignored", "missing") if counts.get(s)]
        display = filepath.removeprefix(ROCQ_SRC_PREFIX)
        p(f"  {display:40s} {done:3d}/{total:<3d} ({file_pct:5.1f}%) [{', '.join(parts)}]")


# ============================================================================
# Output: CSV
# ============================================================================

def output_csv(report: Report, path: str) -> None:
    """Write report as CSV."""
    fh = open(path, "w", newline="") if path != "-" else sys.stdout
    writer = csv.writer(fh)
    writer.writerow(["rocq_file", "rocq_name", "status", "lean_name", "reason"])
    for e in report.entries:
        writer.writerow([e.rocq_file, e.rocq_name, e.status, e.lean_name, e.reason])
    if path != "-":
        fh.close()
        log(f"Wrote CSV to {path}")


# ============================================================================
# Output: HTML
# ============================================================================

# Fixed column widths for definition tables (name 40%, status 10%, detail 50%).
_COLGROUP = (
    '<colgroup><col class="col-name"><col class="col-status">'
    '<col class="col-detail"></colgroup>'
)

# CSS class for each status badge (rendered via ::before pseudo-elements in the template).
_BADGE_CLS = {
    "ported": "badge-ported",
    "ignored": "badge-ignored",
    "missing": "badge-missing",
    "stale_alias": "badge-stale",
    "stale_ignore": "badge-stale",
}


def _render_entry_row(e: ReportEntry) -> str:
    """Render a single definition as an HTML table row."""
    badge = _BADGE_CLS.get(e.status, "")
    detail = e.lean_name if e.status == "ported" else e.reason
    return (
        f'<tr class="entry {e.status}" data-name="{e.rocq_name}">'
        f"<td>{e.rocq_name}</td>"
        f'<td><span class="badge {badge}"></span></td>'
        f"<td>{detail}</td></tr>"
    )


def _stats_html(n_done: int, n_total: int) -> str:
    """Render the stats + mini-bar fragment used by both folder and file headers."""
    pct = n_done / n_total * 100 if n_total else 0
    return (
        f'<span class="section-stats">{n_done}/{n_total} ({pct:.0f}%)</span>'
        f'<span class="mini-bar"><span class="mini-bar-fill"'
        f' style="width:{pct:.1f}%"></span></span>'
    )


def _render_file_section(
    filepath: str, entries: list[ReportEntry], rocq_commit: str
) -> str:
    """Render a collapsible section for one Rocq .v file (nested inside a folder)."""
    display = filepath.removeprefix(ROCQ_SRC_PREFIX)
    filename = display.split("/", 1)[1] if "/" in display else display
    n_done = sum(1 for e in entries if e.status in ("ported", "ignored"))
    n_total = len(entries)
    link = f"{GITLAB_WEB_BASE}/-/blob/{rocq_commit}/{filepath}"

    rows = "".join(
        _render_entry_row(e)
        for e in sorted(entries, key=lambda x: (x.status != "missing", x.rocq_name))
    )

    return (
        f'<div class="file-section">'
        f'<div class="section-header" onclick="toggle(this)">'
        f'<span class="arrow">&#9654;</span>'
        f'<code class="file-name">{filename}</code>'
        f'<a class="file-link" href="{link}" target="_blank"'
        f' onclick="event.stopPropagation()">[src]</a>'
        f'{_stats_html(n_done, n_total)}'
        f"</div>"
        f'<table class="file-table">{_COLGROUP}'
        f"<thead><tr><th>Rocq Name</th><th>Status</th><th>Details</th></tr></thead>"
        f"<tbody>{rows}</tbody></table></div>"
    )


def _render_concept_section(
    feature: str, entries: list[ConceptEntry],
) -> str:
    """Render a collapsible section for a concept (feature), nested inside a folder.

    If the concept has no subfeatures, it shows as a single-row section.
    If it has subfeatures, each subfeature is a row within the section.
    """
    top = [e for e in entries if not e.subfeature]
    subs = [e for e in entries if e.subfeature]

    items = subs if subs else top
    n_done = sum(1 for e in items if e.status == "ported")
    n_total = len(items)

    top_reason = top[0].reason if top else ""
    top_status = top[0].status if top else ""

    rows = ""
    if subs:
        for e in sorted(subs, key=lambda x: (x.status != "missing", x.subfeature)):
            badge = _BADGE_CLS.get(e.status, "")
            rows += (
                f'<tr class="entry {e.status}" data-name="{e.subfeature}">'
                f"<td>{e.subfeature}</td>"
                f'<td><span class="badge {badge}"></span></td>'
                f"<td>{e.reason}</td></tr>"
            )
    elif top:
        badge = _BADGE_CLS.get(top_status, "")
        rows = (
            f'<tr class="entry {top_status}" data-name="{feature}">'
            f"<td>{feature}</td>"
            f'<td><span class="badge {badge}"></span></td>'
            f"<td>{top_reason}</td></tr>"
        )

    return (
        f'<div class="file-section">'
        f'<div class="section-header" onclick="toggle(this)">'
        f'<span class="arrow">&#9654;</span>'
        f'<code class="file-name">{feature}</code>'
        f'{_stats_html(n_done, n_total)}'
        f"</div>"
        f'<table class="file-table">{_COLGROUP}'
        f"<thead><tr><th>Name</th><th>Status</th><th>Details</th></tr></thead>"
        f"<tbody>{rows}</tbody></table></div>"
    )


def _render_folder_section(
    folder: str,
    file_sections: list[tuple[str, str]],
    concept_sections: list[tuple[str, str]],
    folder_done: int,
    folder_total: int,
) -> str:
    """Render a top-level collapsible folder containing file and concept sections."""
    # Merge and sort children by sort key
    children = sorted(file_sections + concept_sections, key=lambda x: x[0])
    children_html = "\n".join(html for _, html in children)

    return (
        f'<div class="folder-section">'
        f'<div class="section-header" onclick="toggle(this)">'
        f'<span class="arrow">&#9654;</span>'
        f'<code class="folder-name">{folder}/</code>'
        f'{_stats_html(folder_done, folder_total)}'
        f"</div>"
        f'<div class="folder-children">{children_html}</div>'
        f"</div>"
    )


def _render_stale_section(entries: list[ReportEntry]) -> str:
    """Render the collapsible section for stale alias/ignore entries."""
    if not entries:
        return ""
    rows = "".join(_render_entry_row(e) for e in entries)
    return (
        f'<div class="folder-section open">'
        f'<div class="section-header" onclick="toggle(this)">'
        f'<span class="arrow">&#9654;</span>'
        f'<code class="folder-name">Stale Entries</code>'
        f'<span class="section-stats">{len(entries)} entries</span></div>'
        f'<div class="folder-children">'
        f'<div class="file-section open">'
        f'<table class="file-table" style="display:table">{_COLGROUP}'
        f"<thead><tr><th>Name</th><th>Status</th><th>Details</th></tr></thead>"
        f"<tbody>{rows}</tbody></table></div>"
        f"</div></div>"
    )


def output_html(report: Report, path: str) -> None:
    """Generate a self-contained HTML report from the template."""
    # Partition entries into per-file and stale
    files_data: dict[str, list[ReportEntry]] = defaultdict(list)
    stale_entries: list[ReportEntry] = []
    for e in report.entries:
        if e.status in ("stale_alias", "stale_ignore"):
            stale_entries.append(e)
        elif e.rocq_file:
            files_data[e.rocq_file].append(e)

    total = report.total_rocq
    ported = report.count("ported")
    pct = ported / total * 100 if total else 0

    # Group concepts by (dir, feature)
    concept_groups: dict[tuple[str, str], list[ConceptEntry]] = defaultdict(list)
    for c in report.concepts:
        concept_groups[(c.dir, c.feature)].append(c)

    # Build folder -> children mapping
    folder_files: dict[str, list[tuple[str, str]]] = defaultdict(list)  # folder -> [(sort_key, html)]
    folder_concepts: dict[str, list[tuple[str, str]]] = defaultdict(list)
    folder_stats: dict[str, dict[str, int]] = defaultdict(lambda: {"done": 0, "total": 0})

    for fp, entries in files_data.items():
        display = fp.removeprefix(ROCQ_SRC_PREFIX)
        folder = display.split("/")[0]
        n_done = sum(1 for e in entries if e.status in ("ported", "ignored"))
        n_total = len(entries)
        folder_stats[folder]["done"] += n_done
        folder_stats[folder]["total"] += n_total
        folder_files[folder].append((display, _render_file_section(fp, entries, report.rocq_commit)))

    for (dir_path, feature), entries in concept_groups.items():
        folder = dir_path.rstrip("/")
        subs = [e for e in entries if e.subfeature]
        tops = [e for e in entries if not e.subfeature]
        items = subs if subs else tops
        n_done = sum(1 for e in items if e.status == "ported")
        n_total = len(items)
        folder_stats[folder]["done"] += n_done
        folder_stats[folder]["total"] += n_total
        sort_key = dir_path + feature
        folder_concepts[folder].append((sort_key, _render_concept_section(feature, entries)))

    # Render all folder sections
    all_folders = sorted(set(folder_files) | set(folder_concepts) | set(folder_stats))
    folder_sections = "\n".join(
        _render_folder_section(
            folder,
            folder_files.get(folder, []),
            folder_concepts.get(folder, []),
            folder_stats[folder]["done"],
            folder_stats[folder]["total"],
        )
        for folder in all_folders
    )

    # Fill template
    template = TEMPLATE_PATH.read_text()
    replacements = {
        "gitlab_web_base": GITLAB_WEB_BASE,
        "rocq_commit": report.rocq_commit,
        "rocq_commit_short": report.rocq_commit[:12],
        "lean_rev_html": (
            f'<a href="{GITHUB_WEB_BASE}/commit/{report.lean_rev}">{report.lean_rev[:12]}</a>'
            if len(report.lean_rev) >= 40
            else report.lean_rev
        ),
        "total": str(total),
        "ported": str(ported),
        "ignored": str(report.count("ignored")),
        "missing": str(report.count("missing")),
        "stale": str(report.count("stale_alias")),
        "pct": f"{pct:.1f}",
        "folder_sections": folder_sections,
        "stale_section": _render_stale_section(stale_entries),
    }
    html = template
    for key, value in replacements.items():
        html = html.replace("{{" + key + "}}", value)

    with open(path, "w") as f:
        f.write(html)
    log(f"Wrote HTML report to {path}")


# ============================================================================
# Main
# ============================================================================

# Maps --format values to their output functions.
FORMATTERS = {
    "summary": lambda report, args: output_summary(
        report, out=open(args.output, "w") if args.output else sys.stdout
    ),
    "csv": lambda report, args: output_csv(report, args.output or "-"),
    "html": lambda report, args: output_html(report, args.output or "report.html"),
}


def main():
    parser = argparse.ArgumentParser(description="Iris-Lean porting completeness checker")
    parser.add_argument("--format", choices=FORMATTERS, default="summary")
    parser.add_argument("--output", "-o", help="Output file path")
    parser.add_argument("--rocq-commit", default=DEFAULT_ROCQ_REVISION,
                        help="Iris-Rocq commit SHA or branch")
    parser.add_argument("--no-build", action="store_true",
                        help="Skip running lake exe dumpPortingData")
    parser.add_argument("--lean-rev", default="Local",
                        help="Iris-Lean revision label (default: Local)")
    parser.add_argument("--cache-dir", default=".lake/iris-rocq-cache")
    parser.add_argument("--lean-json", default=".lake/porting_data.json")
    args = parser.parse_args()

    # Step 1: Collect Lean-side data (rocq_alias + #rocq_ignore entries).
    if not args.no_build:
        run_lake_dump(args.lean_json)
    elif not os.path.exists(args.lean_json):
        log(f"Error: {args.lean_json} not found. Run without --no-build first.")
        sys.exit(1)
    lean = load_lean_data(args.lean_json)
    log(f"Loaded {len(lean.aliases)} aliases, {len(lean.ignores)} ignores, "
        f"{len(lean.ignored_files)} ignored files, and {len(lean.concepts)} concepts from Lean")

    # Step 2: Collect Rocq-side data (download, parse, cache).
    rocq_defs, rocq_commit = download_iris_rocq(args.rocq_commit, Path(args.cache_dir))

    # Step 3: Diff and output.
    report = compute_report(rocq_defs, lean.aliases, lean.ignores, lean.ignored_files,
                            lean.concepts, rocq_commit, args.lean_rev)
    FORMATTERS[args.format](report, args)


if __name__ == "__main__":
    main()
