#!/bin/bash

# Update Bluebell.lean with all imports
# This script generates the main library file by scanning all .lean files

set -e  # Exit on any error

echo "Updating Bluebell.lean with all imports..."

# Generate imports for Bluebell
git ls-files 'src/Bluebell/*.lean' | LC_ALL=C sort | sed 's/\.lean//;s,^src/,,;s,/,.,g;s/^/import /' > src/Bluebell.lean

echo "✓ Bluebell.lean updated with $(wc -l < src/Bluebell.lean) imports"

# Uncomment if you have Examples
# git ls-files 'Examples/*.lean' | LC_ALL=C sort | sed 's/\.lean//;s,/,.,g;s/^/import /' > Examples.lean
