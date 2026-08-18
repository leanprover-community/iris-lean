# Porting Completeness Checker

Compares Iris-Rocq definitions against Iris-Lean's `@[rocq_alias]` annotations
to track porting progress.

## Quick Start

```sh
# Generate an HTML report (builds Lean, downloads Rocq, writes report.html)
python3 scripts/check_porting.py --format html -o report.html
```

## Options

| Flag | Description | Default |
|---|---|---|
| `--format` | Output format: `stale` (list of stale Rocq names — aliases/ignores pointing to names removed upstream), `csv`, or `html` | `stale` |
| `-o`, `--output` | Output file path | stdout (stale/csv) |
| `--rocq-commit` | Iris-Rocq commit SHA or branch to check against | Value from `scripts/ROCQ_REVISION` |
| `--lean-rev` | Lean revision label shown in the HTML report | `Local` |
| `--no-build` | Skip running `lake exe dumpPortingData` | off |
| `--cache-dir` | Cache directory for downloaded Rocq definitions | `.lake/iris-rocq-cache` |
| `--lean-json` | Path to the Lean JSON dump | `.lake/porting_data.json` |
| `--print` | Print one config value (`commit-api-url`) and exit; used by CI | — |

## How It Works

1. **Lean side** -- `lake exe dumpPortingData` scans the compiled Lean environment
   and writes a JSON file containing all `@[rocq_alias]` mappings, `#rocq_ignore`
   entries, `#rocq_ignore_file` entries, and `#rocq_concept` entries.

2. **Rocq side** -- The script downloads the Iris-Rocq source tarball from GitLab
   at the pinned revision, parses every `.v` file under the tracked package
   directories for definition names, and caches the result under `--cache-dir`.

3. **Diff** -- Each Rocq definition is classified as:
   - **ported** -- has a matching `@[rocq_alias]` in Lean
   - **ignored** -- listed via `#rocq_ignore`, `#rocq_ignore_file`, or in one of
     its package's `ignoredDirs`
   - **missing** -- no alias or ignore entry

   Lean-side aliases or ignores whose Rocq target no longer exists upstream
   are flagged as `stale_alias` / `stale_ignore`. The default `stale` format
   prints just those names (grouped, with the checked-against revision on the
   first line); `csv` and `html` include the full per-definition classification.
   `#rocq_concept` entries appear as separate feature sections alongside files
   in the HTML report.

## Packages

Tracked directories are listed in [`porting_config.json`](porting_config.json);
anything absent from it (`iris_deprecated/`, `iris_unstable/`) is untracked. Each
is rendered as a report section, with its immediate subdirectories as folders and
anything deeper flattened into the file name — so `base_logic/lib/gen_heap.v`
shows as `lib/gen_heap.v` under `base_logic`.

Rocq short names are only unique within a package (`pointsto` is defined in both
`iris/base_logic/lib/gen_heap.v` and `iris_heap_lang/primitive_laws.v`), so each
package has a `prefix` that keeps its definitions distinct. `iris` claims the
unprefixed namespace; at most one package may. The same prefix spells the
directory argument of `#rocq_ignore_file` / `#rocq_concept`:

```
@[rocq_alias heap_lang.pointsto] theorem pointsTo ...
#rocq_ignore heap_lang.pretty_int "Rocq-specific pretty printing"

#rocq_ignore_file proofmode     "tokens.v"   "Rocq-specific tokenizer"
#rocq_ignore_file heap_lang.lib "diverge.v"  "Not needed"
```

Declarations use the short convention unless the same name occurs in multiple
tracked files. Every ambiguous occurrence includes its source filename, so the
two local `lock_inv` declarations in the spin and ticket locks are
`heap_lang.spin_lock.lock_inv` and `heap_lang.ticket_lock.lock_inv`.

## Configuration Files

- **`scripts/ROCQ_REVISION`** -- The Iris-Rocq commit SHA to track against.
  Update this when bumping the upstream revision.

- **`scripts/porting_config.json`** -- The tracked repo and packages. To track
  another directory, add a package entry — no code changes needed. The Lean
  commands accept any directory name; unknown ones are reported by this script.
