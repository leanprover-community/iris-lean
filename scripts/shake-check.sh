#!/bin/sh
# Dry run: report each import `lake shake` thinks is unused, one per line, showing the
# actual import. Skips our deliberate `import Iris.Init` invariant (shake flags those as
# "implied", but we keep them on purpose). No edits are applied.
lake shake --gh-style "$@" 2>&1 | grep 'warning: unused import' | cut -d: -f1,2 |
while IFS=: read -r file line; do
  src=$(sed -n "${line}p" "$file")
  case $src in *"import Iris.Init"*) continue ;; esac
  echo "$file:$line: $src"
done
