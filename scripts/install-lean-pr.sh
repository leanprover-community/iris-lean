#!/usr/bin/env bash
# Build a Lean 4 PR from source and register it with elan as `lean-pr<N>`.
#
#   scripts/install-lean-pr.sh            # PR 14942, all cores
#   PR=14942 JOBS=12 DIR=~/lean-pr scripts/install-lean-pr.sh
#
# macOS deps:  brew install cmake gmp libuv pkgconf
# Linux deps:  cmake, g++ or clang, libgmp-dev, libuv1-dev, git
set -euo pipefail

PR="${PR:-14942}"
DIR="${DIR:-$HOME/lean-pr$PR}"
if [[ "$(uname)" == Darwin ]]; then
  JOBS="${JOBS:-$(sysctl -n hw.ncpu)}"
else
  JOBS="${JOBS:-$(nproc)}"
fi
NAME="lean-pr$PR"

for tool in git cmake elan pkg-config; do
  command -v "$tool" >/dev/null || { echo "missing: $tool" >&2; exit 1; }
done

if command -v brew >/dev/null; then
  for pkg in libuv gmp; do
    pc="$(brew --prefix "$pkg" 2>/dev/null)/lib/pkgconfig"
    if [[ -d "$pc" ]]; then PKG_CONFIG_PATH="$pc${PKG_CONFIG_PATH:+:$PKG_CONFIG_PATH}"; fi
  done
  export PKG_CONFIG_PATH
fi
pkg-config --exists libuv ||
  { echo "pkg-config ($(command -v pkg-config)) cannot find libuv; PKG_CONFIG_PATH=${PKG_CONFIG_PATH:-}" >&2; exit 1; }

mkdir -p "$DIR"

# Lake archives static libraries with Apple's `libtool -static`; a GNU libtool earlier in PATH breaks it.
if [[ "$(uname)" == Darwin ]]; then
  mkdir -p "$DIR/shim"
  ln -sf /usr/bin/libtool "$DIR/shim/libtool"
  export PATH="$DIR/shim:$PATH"
fi

cd "$DIR"
if [[ ! -d src/.git ]]; then
  git init -q src
  git -C src remote add origin https://github.com/leanprover/lean4.git
fi
git -C src fetch --depth 1 origin "pull/$PR/head"
git -C src checkout -q --detach FETCH_HEAD
echo "Building PR $PR at $(git -C src rev-parse --short HEAD) with $JOBS jobs"

cd src
cmake --preset release
cmake --build build/release -j "$JOBS"

TC="$DIR/src/build/release/stage1"
"$TC/bin/lean" --version

# The PR's own test pins the elaboration behaviour; `#guard_msgs` is silent on success.
"$TC/bin/lean" tests/elab/implicitAutoParamClass.lean
echo "implicitAutoParamClass.lean: ok"

elan toolchain uninstall "$NAME" 2>/dev/null || true
elan toolchain link "$NAME" "$TC"
echo "Linked: put '$NAME' in lean-toolchain to use it."
