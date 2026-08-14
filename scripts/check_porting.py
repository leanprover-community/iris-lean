#!/usr/bin/env python3
"""
Iris-Lean Porting Completeness Checker

Compares Iris-Rocq definitions against Iris-Lean's @[rocq_alias] annotations
to track porting progress.

Usage:
  python3 scripts/check_porting.py [options]

Options:
  --format stale|csv|html     Output format (default: stale)
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
import urllib.error
import urllib.request
from collections import defaultdict
from dataclasses import dataclass, field
from pathlib import Path

# ============================================================================
# Configuration
# ============================================================================

# The Lean package root (contains lakefile.toml and .lake/).
LEAN_PKG_DIR = Path(__file__).parent.parent / "Iris"

GITHUB_WEB_BASE = "https://github.com/leanprover-community/iris-lean"

# The pinned Iris-Rocq revision, in its own file so CI can `cat` it.
REVISION_PATH = Path(__file__).parent / "ROCQ_REVISION"


@dataclass(frozen=True)
class Repo:
    """The Iris-Rocq GitLab repository every tracked package comes from."""
    project: str    # URL-encoded project path, e.g. "iris%2Firis"
    api_base: str
    web_base: str

    @property
    def revision(self) -> str:
        """The pinned commit SHA, from `scripts/ROCQ_REVISION`."""
        return REVISION_PATH.read_text().strip()

    def commit_url(self, commit: str) -> str:
        return f"{self.web_base}/-/commit/{commit}"

    def blob_url(self, commit: str, path: str) -> str:
        return f"{self.web_base}/-/blob/{commit}/{path}"

    def archive_url(self, sha: str) -> str:
        return (f"{self.api_base}/projects/{self.project}"
                f"/repository/archive.tar.gz?sha={sha}")

    def commit_api_url(self, ref: str) -> str:
        return f"{self.api_base}/projects/{self.project}/repository/commits/{ref}"


CONFIG_PATH = Path(__file__).parent / "porting_config.json"


@dataclass(frozen=True)
class Package:
    """A tracked directory of `REPO`, named on the report by `dir`.

    `prefix` qualifies every Rocq definition name in the package, so that short
    names colliding across packages (`pointsto`) stay distinct; it also spells
    the package's directory argument to `#rocq_ignore_file` / `#rocq_concept`.
    At most one package may take `""` and go unprefixed.

    `folders` are the immediate subdirectories, each a directory argument as
    `<prefix><folder>`. `ignored_dirs` are subdirectories skipped entirely.
    """
    dir: str
    prefix: str = ""
    folders: tuple[str, ...] = ()
    ignored_dirs: tuple[str, ...] = ()

    def arg(self, folder: str = "") -> str:
        """This package's directory argument, or one of its folders'."""
        return self.prefix + folder if folder else self.prefix.rstrip(".")


def load_config(path: Path = CONFIG_PATH) -> tuple[Repo, list[Package]]:
    """Read the config shared with `Iris/Std/RocqPorting.lean`, so the two can't drift."""
    cfg = json.loads(path.read_text())
    r = cfg["repo"]
    return (
        Repo(project=r["project"], api_base=r["apiBase"], web_base=r["webBase"]),
        [Package(dir=p["dir"], prefix=p.get("prefix", ""),
                 folders=tuple(p.get("folders", ())),
                 ignored_dirs=tuple(p.get("ignoredDirs", ())))
         for p in cfg["packages"]],
    )


REPO, PACKAGES = load_config()

# HTML report template, kept separate for readability.
TEMPLATE_PATH = Path(__file__).parent / "report_template.html"


def log(msg: str) -> None:
    print(msg, file=sys.stderr)


def package_of(rel_path: str) -> Package | None:
    """The package owning a tarball-relative path, or None if untracked."""
    return next((p for p in PACKAGES if rel_path.startswith(p.dir + "/")), None)


def package_of_name(name: str) -> Package | None:
    """The package whose prefix claims a qualified name; longest prefix wins.

    Stale entries have no source file left, so only the name identifies them.

    >>> package_of_name("heap_lang.pointsto").dir
    'iris_heap_lang'
    >>> package_of_name("fupd_keep_plain").dir
    'iris'
    """
    matches = [p for p in PACKAGES if name.startswith(p.prefix)]
    return max(matches, key=lambda p: len(p.prefix), default=None)


def directory_args() -> list[str]:
    """Accepted `#rocq_ignore_file` / `#rocq_concept` directories.

    >>> directory_args()[:2], directory_args()[-1]
    (['algebra', 'base_logic'], 'heap_lang.lib')
    """
    return [a for p in PACKAGES
            for a in (p.arg(), *(p.arg(f) for f in p.folders)) if a]


def is_directory_arg(folder: str) -> bool:
    """Whether `folder` names a tracked directory.

    >>> is_directory_arg("heap_lang.lib"), is_directory_arg("typo")
    (True, False)
    """
    return folder.rstrip("/") in directory_args()


def qualify(name: str, rel_path: str) -> str:
    """Prefix a parsed definition name with its package's prefix.

    >>> qualify("pointsto", "iris_heap_lang/primitive_laws.v")
    'heap_lang.pointsto'
    >>> qualify("cmra_op_ne", "iris/algebra/cmra.v")
    'cmra_op_ne'
    """
    pkg = package_of(rel_path)
    return (pkg.prefix if pkg else "") + name


def qualify_ambiguous(name: str, rel_path: str) -> str:
    """Qualify an ambiguous name with its Rocq source filename.

    This is used whenever the short name occurs in multiple source files,
    regardless of whether the declarations are local or exported.

    >>> qualify_ambiguous("lock_inv", "iris_heap_lang/lib/spin_lock.v")
    'heap_lang.spin_lock.lock_inv'
    >>> qualify_ambiguous("helper", "iris/algebra/ofe.v")
    'ofe.helper'
    """
    pkg = package_of(rel_path)
    stem = rel_path.rsplit("/", 1)[-1].removesuffix(".v")
    return f"{pkg.prefix if pkg else ''}{stem}.{name}"


def unqualify(name: str, rel_path: str) -> str:
    """Strip that prefix again for display; the section already shows it.

    >>> unqualify("heap_lang.pointsto", "iris_heap_lang/primitive_laws.v")
    'pointsto'
    >>> unqualify("heap_lang.spin_lock.lock_inv", "iris_heap_lang/lib/spin_lock.v")
    'lock_inv'
    """
    pkg = package_of(rel_path)
    short = name.removeprefix(pkg.prefix) if pkg else name
    if pkg:
        source_prefix = rel_path.rsplit("/", 1)[-1].removesuffix(".v") + "."
        short = short.removeprefix(source_prefix)
    return short


def split_path(rel_path: str) -> tuple[str, str, str]:
    """Split a tracked .v path into (package, folder, filename).

    The folder is the immediate subdirectory; anything deeper is flattened into
    the filename. A file at the package root has no folder.

    >>> split_path("iris/base_logic/lib/gen_heap.v")
    ('iris', 'base_logic', 'lib/gen_heap.v')
    >>> split_path("iris_heap_lang/lang.v")
    ('iris_heap_lang', '', 'lang.v')
    """
    pkg = package_of(rel_path)
    if pkg is None:
        return "", "", rel_path
    folder, _, filename = rel_path[len(pkg.dir) + 1:].rpartition("/")
    head, _, rest = folder.partition("/")
    return pkg.dir, head, f"{rest}/{filename}" if rest else filename


def folder_path(folder: str, file: str) -> str:
    """Resolve a directory argument plus a relative file to a tarball path.

    >>> folder_path("proofmode", "tokens.v")
    'iris/proofmode/tokens.v'
    >>> folder_path("heap_lang.lib", "diverge.v")
    'iris_heap_lang/lib/diverge.v'
    """
    folder = folder.rstrip("/")
    for pkg in PACKAGES:
        if folder == pkg.arg():
            return f"{pkg.dir}/{file}"
        for sub in pkg.folders:
            if folder == pkg.arg(sub):
                return f"{pkg.dir}/{sub}/{file}"
    raise ValueError(f"{folder!r} is not a tracked directory; "
                     f"expected one of {directory_args()}")



# ============================================================================
# Rocq Definition Parsing
# ============================================================================

# Rocq vernacular keywords that introduce named definitions.
_DEF_KEYWORDS = (
    r"Definition|Lemma|Theorem|Instance|Class|Record|Structure|"
    r"Inductive|Fixpoint|CoFixpoint|Variant|Corollary|Proposition|"
    r"Fact|Remark|Example|Canonical\s+Structure"
)

# Matches a named definition line. Captures the modifiers and identifier.
# Handles optional prefixes like "Global", "Local", "Program", "#[export]".
# Identifiers may contain apostrophes (e.g., csum_updateP'_l).
_DEF_RE = re.compile(
    rf"^\s*(?P<modifiers>(?:(?:Global|Local|Program|#\[(?:export|global|local)\])\s+)*)"
    rf"(?:{_DEF_KEYWORDS})\s+"
    rf"(?P<identifier>\w[\w']*)",
    re.MULTILINE,
)

# A mutual definition continues with `with <name>`, which declares a name just as
# the head keyword does -- `Inductive expr := ... with val := ...` defines both.
# Anchored at column 0 so that `with` clauses of a *nested* mutual block (a local
# helper inside another definition's body, indented) are correctly skipped. The
# lookahead requires a parameter list, type ascription, or `:=` to follow, so
# prose and tactic text beginning with "with" is not mistaken for a definition.
_WITH_DEF_RE = re.compile(r"^with\s+(\w[\w']*)\s*(?=[({:])")

# Module/Section tracking: Modules qualify names (e.g., Module bi -> bi.foo),
# but Sections do not.
# `Module Export M` and `Module Import M` are valid forms where the name is M,
# not the Export/Import keyword.
_MODULE_START_RE = re.compile(r"^\s*Module\s+(?:Export\s+|Import\s+)?(\w+)", re.MULTILINE)
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


@dataclass(frozen=True)
class ParsedDefinition:
    name: str
    is_local: bool = False


def parse_rocq_file(text: str) -> list[ParsedDefinition]:
    """Extract definitions and their locality from a Rocq .v file.

    Module prefixes are included; Section prefixes are not.

    A mutual block declares one name per `with` clause:

    >>> parse_rocq_file("Inductive expr :=\\n | Val (v : val)\\nwith val :=\\n | LitV.")
    [ParsedDefinition(name='expr', is_local=False), ParsedDefinition(name='val', is_local=False)]

    Only at column 0, so an indented `with` -- a mutual helper local to another
    definition's body -- contributes no name:

    >>> parse_rocq_file("Fixpoint f x := 0\\n  with g y := 1.")
    [ParsedDefinition(name='f', is_local=False)]

    `Local` and `#[local]` declarations retain that information so collisions
    between private names in separate libraries can be disambiguated later:

    >>> parse_rocq_file("Local Definition helper := 0.\\n#[local] Instance instFoo : Foo := {}.")
    [ParsedDefinition(name='helper', is_local=True), ParsedDefinition(name='instFoo', is_local=True)]
    """
    text = _strip_comments(text)
    # A mutual `with` sometimes sits alone on its line, the name following on the
    # next. Join the two so the line-based matching below sees one head.
    text = re.sub(r"^with[ \t]*\n[ \t]*", "with ", text, flags=re.MULTILINE)

    definitions: list[ParsedDefinition] = []
    module_stack: list[str] = []  # current Module nesting, used for name qualification
    section_names: set[str] = set()  # track Section names so End can distinguish them
    mutual_is_local = False  # `with` clauses inherit the head declaration's locality

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

        # Extract definition name and qualify with Module prefix. A mutual
        # block's `with` clauses declare names too, so they count as well.
        if m := _DEF_RE.match(line):
            ident = m.group("identifier")
            modifiers = m.group("modifiers")
            mutual_is_local = "Local" in modifiers.split() or "#[local]" in modifiers.split()
            qualified = ".".join([*module_stack, ident]) if module_stack else ident
            definitions.append(ParsedDefinition(qualified, mutual_is_local))
        elif m := _WITH_DEF_RE.match(line):
            ident = m.group(1)
            qualified = ".".join([*module_stack, ident]) if module_stack else ident
            definitions.append(ParsedDefinition(qualified, mutual_is_local))

    return definitions


def qualify_definitions(
    parsed: dict[str, list[ParsedDefinition]],
) -> dict[str, list[str]]:
    """Apply package prefixes and disambiguate cross-file name collisions.

    Unique names retain the existing short alias convention. If the same
    qualified short name occurs in multiple files, every occurrence gains its
    source filename so each Rocq declaration has a distinct key.

    >>> qualified = qualify_definitions({
    ...   "iris_heap_lang/lib/spin_lock.v": [ParsedDefinition("lock_inv", True)],
    ...   "iris_heap_lang/lib/ticket_lock.v": [ParsedDefinition("lock_inv", True)],
    ... })
    >>> qualified["iris_heap_lang/lib/spin_lock.v"]
    ['heap_lang.spin_lock.lock_inv']
    >>> qualified["iris_heap_lang/lib/ticket_lock.v"]
    ['heap_lang.ticket_lock.lock_inv']
    """
    base_names = {
        path: [qualify(definition.name, path) for definition in definitions]
        for path, definitions in parsed.items()
    }
    files_by_name: dict[str, set[str]] = defaultdict(set)
    for path, names in base_names.items():
        for name in names:
            files_by_name[name].add(path)
    ambiguous = {name for name, files in files_by_name.items() if len(files) > 1}

    return {
        path: [
            qualify_ambiguous(definition.name, path)
            if base_name in ambiguous else base_name
            for definition, base_name in zip(definitions, base_names[path], strict=True)
        ]
        for path, definitions in parsed.items()
    }


# ============================================================================
# Iris-Rocq Download and Cache
# ============================================================================

_FULL_SHA_RE = re.compile(r"[0-9a-f]{40}\Z")


def _resolve_commit(ref: str) -> str:
    """Resolve a Git ref (branch, tag, or SHA) to a full commit SHA via GitLab API.

    A full SHA already *is* the answer, so it is returned without a request: the
    API could only echo it back, and asking costs a network round trip that would
    otherwise have to time out before an offline run could reach the cache.

    Anything else -- a branch or tag -- must be resolved, because the result names
    the cache directory and is reported as the revision checked against. Failing
    to resolve is therefore fatal: carrying on with a branch name would pin the
    cache to that name forever and label the report with a moving target.
    """
    if _FULL_SHA_RE.match(ref):
        return ref
    try:
        with urllib.request.urlopen(REPO.commit_api_url(ref), timeout=30) as resp:
            return json.loads(resp.read())["id"]
    except Exception as e:
        reason = f"HTTP {e.code}" if isinstance(e, urllib.error.HTTPError) else e
        raise SystemExit(
            f"Error: could not resolve '{ref}' via {REPO.web_base} ({reason}).\n"
            f"Pass a full 40-character SHA to --rocq-commit to work offline."
        )

def download_iris_rocq(commit: str, cache_dir: Path) -> tuple[dict[str, list[str]], str]:
    """Download and parse a repo's tracked packages, caching the result as JSON.

    The tarball is downloaded from the GitLab archive API, parsed for every .v
    file under the repo's tracked package directories, and the extracted
    definitions are cached as JSON keyed by the resolved commit SHA. Subsequent
    calls with the same SHA hit the cache.

    Returns (file_path -> definition_names, resolved_commit_sha).
    """
    # Resolve to a concrete SHA so branch names get pinned in the cache. A full
    # SHA resolves offline, so a warm cache needs no network at all.
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
    try:
        with urllib.request.urlopen(REPO.archive_url(resolved), timeout=120) as resp:
            tarball_data = resp.read()
    except Exception as e:
        reason = f"HTTP {e.code}" if isinstance(e, urllib.error.HTTPError) else e
        msg = [f"Error: could not download {REPO.web_base} at '{resolved}' ({reason}).",
               f"Nothing cached for this revision either ({cache_file})."]
        # Point at revisions that *are* cached, so an offline run has a way out.
        others = sorted(p.name for p in cache_dir.glob("*")
                        if (p / "rocq_definitions.json").exists())
        if others:
            msg.append("Cached revisions you can use with --rocq-commit:")
            msg += [f"  {o}" for o in others]
        raise SystemExit("\n".join(msg))
    log(f"Downloaded {len(tarball_data) / 1024:.0f} KB, parsing...")

    # Parse every .v file under the tracked source roots.
    parsed: dict[str, list[ParsedDefinition]] = {}
    with tarfile.open(fileobj=io.BytesIO(tarball_data), mode="r:gz") as tf:
        for member in tf.getmembers():
            if not member.isfile() or not member.name.endswith(".v"):
                continue
            # The archive has a top-level directory (e.g., "iris-master-SHA/").
            parts = member.name.split("/", 1)
            if len(parts) < 2:
                continue
            rel_path = parts[1]
            if package_of(rel_path) is None:
                continue
            fobj = tf.extractfile(member)
            if fobj is None:
                continue
            parsed_definitions = parse_rocq_file(
                fobj.read().decode("utf-8", errors="replace")
            )
            if parsed_definitions:
                parsed[rel_path] = parsed_definitions

    definitions = qualify_definitions(parsed)

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
        cwd=LEAN_PKG_DIR,
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
    status: str    # "ported" | "missing"
    reason: str


@dataclass
class LeanData:
    aliases: dict[str, str]
    ignores: dict[str, str]
    ignored_files: dict[str, str]
    concepts: list[ConceptEntry]


def load_lean_data(json_path: str) -> LeanData:
    """Load Lean alias/ignore/concept data from the JSON dump.

    This is where a bad `#rocq_ignore_file` / `#rocq_concept` directory is caught:
    the Lean side accepts any identifier, so the check lives here.
    """
    with open(json_path) as f:
        data = json.load(f)
    bad = sorted({e["folder"] for e in data.get("ignored_files", [])
                  + data.get("concepts", []) if not is_directory_arg(e["folder"])})
    if bad:
        raise SystemExit(
            f"Error: unknown #rocq_ignore_file / #rocq_concept "
            f"{'directories' if len(bad) > 1 else 'directory'} {', '.join(map(repr, bad))}.\n"
            f"Expected one of: {', '.join(directory_args())}"
        )
    aliases = {a["rocq"]: a["lean"] for a in data["aliases"]}
    ignores = {i["rocq"]: i["reason"] for i in data["ignores"]}
    ignored_files = {
        folder_path(e["folder"], e["file"]): e["reason"]
        for e in data.get("ignored_files", [])
    }
    concepts = [
        ConceptEntry(
            dir=c["folder"], feature=c["feature"],
            subfeature=c.get("subfeature") or "",
            status=c["status"], reason=c["reason"],
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

    Names arrive already qualified by their package prefix, so `pointsto` from
    `iris` and `heap_lang.pointsto` from `iris_heap_lang` are distinct keys.
    Ambiguous file-local names also carry their source filename.
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
        pkg = package_of(filepath)
        in_ignored_dir = pkg is not None and split_path(filepath)[1] in pkg.ignored_dirs
        if name in aliases:
            report.entries.append(ReportEntry(filepath, name, "ported", lean_name=aliases[name]))
        elif name in ignores or filepath in ignored_files or in_ignored_dir:
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
# Output: Stale names
# ============================================================================

def output_stale(report: Report, out=sys.stdout) -> None:
    """Print the list of stale aliases and stale ignores."""
    p = lambda *a, **kw: print(*a, file=out, **kw)

    p(f"Lean revision:                 {report.lean_rev}")
    p(f"Checked against Rocq revision: {report.rocq_commit}")
    p()

    stale_aliases = sorted(report.by_status("stale_alias"), key=lambda e: e.rocq_name)
    stale_ignores = sorted(report.by_status("stale_ignore"), key=lambda e: e.rocq_name)

    if not stale_aliases and not stale_ignores:
        p("No stale entries.")
        return

    p(f"Stale aliases ({len(stale_aliases)}):")
    for e in stale_aliases:
        p(f"  {e.rocq_name}")
    p()
    p(f"Stale ignores ({len(stale_ignores)}):")
    for e in stale_ignores:
        p(f"  {e.rocq_name}")


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
    """Render a single definition as an HTML table row.

    The package prefix is dropped from the displayed name -- the enclosing folder
    already says `heap_lang/` -- but kept in `data-name` so search finds both the
    short and the qualified form.
    """
    badge = _BADGE_CLS.get(e.status, "")
    detail = e.lean_name if e.status == "ported" else e.reason
    short = unqualify(e.rocq_name, e.rocq_file)
    return (
        f'<tr class="entry {e.status}" data-name="{e.rocq_name}">'
        f"<td>{short}</td>"
        f'<td><span class="badge {badge}"></span></td>'
        f'<td><div class="detail-scroll">{detail}</div></td></tr>'
    )


def _stats_html(n_ported: int, n_ignored: int, n_total: int) -> str:
    """Render the stats + mini-bar fragment used by both folder and file headers."""
    n_done = n_ported + n_ignored
    pct = n_done / n_total * 100 if n_total else 0
    pct_ported = n_ported / n_total * 100 if n_total else 0
    pct_ignored = n_ignored / n_total * 100 if n_total else 0
    return (
        f'<span class="section-stats">{n_done}/{n_total} ({pct:.0f}%)</span>'
        f'<span class="mini-bar">'
        f'<span class="mini-bar-fill ported" style="width:{pct_ported:.2f}%"></span>'
        f'<span class="mini-bar-fill ignored" style="width:{pct_ignored:.2f}%"></span>'
        f'</span>'
    )


def _render_file_section(
    filepath: str, entries: list[ReportEntry], rocq_commit: str
) -> str:
    """Render a collapsible section for one Rocq .v file (nested inside a folder)."""
    filename = split_path(filepath)[2]
    n_ported = sum(1 for e in entries if e.status == "ported")
    n_ignored = sum(1 for e in entries if e.status == "ignored")
    n_total = len(entries)
    link = REPO.blob_url(rocq_commit, filepath)

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
        f'{_stats_html(n_ported, n_ignored, n_total)}'
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
    n_ported = sum(1 for e in items if e.status == "ported")
    n_ignored = sum(1 for e in items if e.status == "ignored")
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
                f'<td><div class="detail-scroll">{e.reason}</div></td></tr>'
            )
    elif top:
        badge = _BADGE_CLS.get(top_status, "")
        rows = (
            f'<tr class="entry {top_status}" data-name="{feature}">'
            f"<td>{feature}</td>"
            f'<td><span class="badge {badge}"></span></td>'
            f'<td><div class="detail-scroll">{top_reason}</div></td></tr>'
        )

    return (
        f'<div class="file-section">'
        f'<div class="section-header" onclick="toggle(this)">'
        f'<span class="arrow">&#9654;</span>'
        f'<code class="file-name">{feature}</code>'
        f'{_stats_html(n_ported, n_ignored, n_total)}'
        f"</div>"
        f'<table class="file-table">{_COLGROUP}'
        f"<thead><tr><th>Name</th><th>Status</th><th>Details</th></tr></thead>"
        f"<tbody>{rows}</tbody></table></div>"
    )


def _render_folder_section(
    folder: str,
    file_sections: list[tuple[str, str]],
    concept_sections: list[tuple[str, str]],
    folder_ported: int,
    folder_ignored: int,
    folder_total: int,
) -> str:
    """Render a top-level collapsible folder containing file and concept sections."""
    # Concepts first (sorted), then files (sorted)
    children = sorted(concept_sections, key=lambda x: x[0]) + sorted(file_sections, key=lambda x: x[0])
    children_html = "\n".join(html for _, html in children)

    return (
        f'<div class="folder-section">'
        f'<div class="section-header" onclick="toggle(this)">'
        f'<span class="arrow">&#9654;</span>'
        f'<code class="folder-name">{folder}/</code>'
        f'{_stats_html(folder_ported, folder_ignored, folder_total)}'
        f"</div>"
        f'<div class="folder-children">{children_html}</div>'
        f"</div>"
    )


def _render_package_section(
    package: str,
    children: list[str],
    ported: int,
    ignored: int,
    total: int,
) -> str:
    """Render a collapsible package section above its children.

    Children are the package's folder sections followed by any file sections for
    files sitting at the package root, which have no folder to nest under.
    Packages start expanded, since they are the page's top-level structure.
    """
    return (
        f'<div class="package-section open">'
        f'<div class="section-header package-header" onclick="toggle(this)">'
        f'<span class="arrow">&#9654;</span>'
        f'<code class="package-name">{package}</code>'
        f'{_stats_html(ported, ignored, total)}'
        f"</div>"
        f'<div class="package-children">{"".join(children)}</div>'
        f"</div>"
    )


def _render_stale_section(entries: list[ReportEntry]) -> str:
    """Render the collapsible section for stale alias/ignore entries.

    Stale entries have no source file left, so they cannot be filed under a
    folder. They are grouped by the package their name belongs to, so it is clear
    which package a removed-upstream alias came from.
    """
    if not entries:
        return ""

    by_package: dict[str, list[ReportEntry]] = defaultdict(list)
    for e in entries:
        pkg = package_of_name(e.rocq_name)
        by_package[pkg.dir if pkg else ""].append(e)

    groups = ""
    for package in [p.dir for p in PACKAGES] + [""]:
        group = by_package.get(package)
        if not group:
            continue
        rows = "".join(_render_entry_row(e) for e in group)
        groups += (
            f'<div class="file-section open">'
            f'<div class="section-header" onclick="toggle(this)">'
            f'<span class="arrow">&#9654;</span>'
            f'<code class="file-name">{package or "(unknown package)"}</code>'
            f'<span class="section-stats">{len(group)} entries</span></div>'
            f'<table class="file-table" style="display:table">{_COLGROUP}'
            f"<thead><tr><th>Name</th><th>Status</th><th>Details</th></tr></thead>"
            f"<tbody>{rows}</tbody></table></div>"
        )

    return (
        f'<div class="folder-section open">'
        f'<div class="section-header" onclick="toggle(this)">'
        f'<span class="arrow">&#9654;</span>'
        f'<code class="folder-name">Stale Entries</code>'
        f'<span class="section-stats">{len(entries)} entries</span></div>'
        f'<div class="folder-children">{groups}</div>'
        f"</div>"
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
    ignored = report.count("ignored")
    done = ported + ignored
    pct = done / total * 100 if total else 0
    pct_ported = ported / total * 100 if total else 0
    pct_ignored = ignored / total * 100 if total else 0

    # Group concepts by (dir, feature)
    concept_groups: dict[tuple[str, str], list[ConceptEntry]] = defaultdict(list)
    for c in report.concepts:
        concept_groups[(c.dir, c.feature)].append(c)

    # Build (package, folder) -> children mapping. An empty folder means the file
    # sits at the package root and hangs directly off the package section.
    Key = tuple[str, str]
    folder_files: dict[Key, list[tuple[str, str]]] = defaultdict(list)  # -> [(sort_key, html)]
    folder_concepts: dict[Key, list[tuple[str, str]]] = defaultdict(list)
    folder_stats: dict[Key, dict[str, int]] = defaultdict(
        lambda: {"ported": 0, "ignored": 0, "total": 0}
    )

    def add_stats(key: Key, entries: list) -> None:
        """Fold a group of entries (which all carry a `.status`) into `key`'s totals."""
        folder_stats[key]["ported"] += sum(1 for e in entries if e.status == "ported")
        folder_stats[key]["ignored"] += sum(1 for e in entries if e.status == "ignored")
        folder_stats[key]["total"] += len(entries)

    for fp, entries in files_data.items():
        package, folder, display = split_path(fp)
        key = (package, folder)
        add_stats(key, entries)
        folder_files[key].append((display, _render_file_section(fp, entries, report.rocq_commit)))

    for (dir_path, feature), entries in concept_groups.items():
        # A concept's `dir` is a directory name, so resolve it the same way as
        # `#rocq_ignore_file` to find which package and folder it belongs to.
        package, folder, _ = split_path(folder_path(dir_path.rstrip("/"), "_"))
        subs = [e for e in entries if e.subfeature]
        items = subs if subs else [e for e in entries if not e.subfeature]
        key = (package, folder)
        add_stats(key, items)
        folder_concepts[key].append((dir_path + feature, _render_concept_section(feature, entries)))

    # Render each package as its own section: folders first (as collapsible
    # groups), then any files that live at the package root.
    all_keys = sorted(set(folder_files) | set(folder_concepts) | set(folder_stats))
    sections = []
    for package in (p.dir for p in PACKAGES):
        keys = [k for k in all_keys if k[0] == package]
        if not keys:
            continue
        children: list[str] = [
            _render_folder_section(
                folder, folder_files.get((package, folder), []),
                folder_concepts.get((package, folder), []),
                folder_stats[(package, folder)]["ported"],
                folder_stats[(package, folder)]["ignored"],
                folder_stats[(package, folder)]["total"],
            )
            for _, folder in keys if folder
        ]
        # Then files that live at the package root, with no folder wrapper.
        root = (package, "")
        if root in folder_stats:
            loose = sorted(folder_concepts.get(root, [])) + sorted(folder_files.get(root, []))
            children.extend(html for _, html in loose)
        sections.append(_render_package_section(
            package, children,
            *(sum(folder_stats[k][s] for k in keys)
              for s in ("ported", "ignored", "total")),
        ))
    folder_sections = "\n".join(sections)

    # Fill template
    template = TEMPLATE_PATH.read_text()
    replacements = {
        "rocq_commit_url": REPO.commit_url(report.rocq_commit),
        "rocq_commit_short": report.rocq_commit[:12],
        "lean_rev_html": (
            f'<a href="{GITHUB_WEB_BASE}/commit/{report.lean_rev}">{report.lean_rev[:12]}</a>'
            if len(report.lean_rev) >= 40
            else report.lean_rev
        ),
        "total": str(total),
        "ported": str(ported),
        "ignored": str(ignored),
        "missing": str(report.count("missing")),
        "stale": str(report.count("stale_alias")),
        "pct": f"{pct:.1f}",
        "pct_ported": f"{pct_ported:.2f}",
        "pct_ignored": f"{pct_ignored:.2f}",
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
    "stale": lambda report, args: output_stale(
        report, out=open(args.output, "w") if args.output else sys.stdout
    ),
    "csv": lambda report, args: output_csv(report, args.output or "-"),
    "html": lambda report, args: output_html(report, args.output or "report.html"),
}


# Config values CI asks for, so workflows never rebuild URLs by hand. The
# revision is not here: it lives in `scripts/ROCQ_REVISION`, which CI can `cat`.
CONFIG_QUERIES = {
    "commit-api-url": lambda: REPO.commit_api_url("master"),
}


def main():
    parser = argparse.ArgumentParser(description="Iris-Lean porting completeness checker")
    parser.add_argument("--print", choices=CONFIG_QUERIES, dest="print_key",
                        help="Print a value from the porting config and exit")
    parser.add_argument("--format", choices=FORMATTERS, default="stale")
    parser.add_argument("--output", "-o", help="Output file path")
    parser.add_argument("--rocq-commit", default=REPO.revision,
                        help="Iris-Rocq commit SHA or branch")
    parser.add_argument("--no-build", action="store_true",
                        help="Skip running lake exe dumpPortingData")
    parser.add_argument("--lean-rev", default="Local",
                        help="Iris-Lean revision label (default: Local)")
    parser.add_argument("--cache-dir", default=str(LEAN_PKG_DIR / ".lake/iris-rocq-cache"))
    parser.add_argument("--lean-json", default=str(LEAN_PKG_DIR / ".lake/porting_data.json"))
    args = parser.parse_args()

    # Step 0: A config query short-circuits everything else.
    if args.print_key:
        print(CONFIG_QUERIES[args.print_key]())
        return

    # Step 1: Collect Lean-side data (rocq_alias + #rocq_ignore entries).
    if not args.no_build:
        run_lake_dump(args.lean_json)
    elif not os.path.exists(args.lean_json):
        log(f"Error: {args.lean_json} not found. Run without --no-build first.")
        sys.exit(1)
    lean = load_lean_data(args.lean_json)
    log(f"Loaded {len(lean.aliases)} aliases, {len(lean.ignores)} ignores, "
        f"{len(lean.ignored_files)} ignored files, and {len(lean.concepts)} concepts from Lean")

    # Step 2: Collect Rocq-side data (download, parse, cache). Every package
    # tracked today comes from one repo, which `--rocq-commit` pins.
    rocq_defs, rocq_commit = download_iris_rocq(args.rocq_commit, Path(args.cache_dir))

    # Step 3: Diff and output.
    report = compute_report(rocq_defs, lean.aliases, lean.ignores, lean.ignored_files,
                            lean.concepts, rocq_commit, args.lean_rev)
    FORMATTERS[args.format](report, args)


if __name__ == "__main__":
    main()
