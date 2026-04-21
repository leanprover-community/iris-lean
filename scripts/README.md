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
| `--format` | Output format: `summary`, `csv`, or `html` | `summary` |
| `-o`, `--output` | Output file path | stdout (summary/csv) |
| `--rocq-commit` | Iris-Rocq commit SHA or branch to check against | Value from `scripts/ROCQ_REVISION` |
| `--lean-rev` | Lean revision label shown in the HTML report | `Local` |
| `--no-build` | Skip running `lake exe dumpPortingData` | off |
| `--cache-dir` | Cache directory for downloaded Rocq definitions | `.lake/iris-rocq-cache` |
| `--lean-json` | Path to the Lean JSON dump | `.lake/porting_data.json` |

## How It Works

1. **Lean side** -- `lake exe dumpPortingData` scans the compiled Lean environment
   and writes a JSON file containing all `@[rocq_alias]` mappings, `#rocq_ignore`
   entries, `#rocq_ignore_file` entries, and `#rocq_concept` entries.

2. **Rocq side** -- The script downloads the Iris-Rocq source tarball from GitLab
   at the revision specified in `scripts/ROCQ_REVISION`, parses every `.v` file
   for definition names, and caches the result under `--cache-dir`.

3. **Diff** -- Each Rocq definition is classified as:
   - **ported** -- has a matching `@[rocq_alias]` in Lean
   - **ignored** -- listed via `#rocq_ignore`, `#rocq_ignore_file`, or in an ignored directory
   - **missing** -- no alias or ignore entry

   Additionally, `#rocq_concept` entries appear as separate feature sections
   alongside files in the HTML report.

## Configuration Files

- **`scripts/ROCQ_REVISION`** -- Single line containing the Iris-Rocq commit SHA
  to track against. Update this when bumping the upstream revision.
