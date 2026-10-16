/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nickolai Zeldovich
-/
module

public import Iris.BI.BigOp
public import Iris.ProofMode
public import Iris.Instances.UPred

/-!
# Kernel cost of the conditional modalities (`□?p P` and friends)

Regression test for https://github.com/leanprover-community/iris-lean/pull/712
Building this file should be fast (sub 1s), see explanation of the test below.

The proof mode stores every hypothesis as `□?p P`, so `iintro`/`iexact` leave the kernel the check
`□?false P =?= P`.  While `intuitionisticallyIf` was a `def` with an `if` body, the kernel unfolded the user's `P`
first; for `P := cellRes …` below (an `if` on a decided width) both sides become `ite`s, and the kernel compares the
two branches `cell … 8 … w =?= cell … 4 … (extractLsb' 0 32 w)` argument by argument through every layer of `cell`,
evaluating the bytes `nthByte` of the symbolic `w` (shifts and divisions on a half-symbolic `Nat`) at each layer
before it gives up.  As an `abbrev` with a `match` body, the wrapper unfolds first and reduces on `false`.

Measured on this file (`lake env lean`, a 64-vCPU x86 VM): with the `def`/`if` version (728a171) each example costs
~10.5 s of kernel time (11 s wall, the two run in parallel; 21 s CPU); with the `abbrev`/`match` version the whole
file takes 0.5 s, imports included.  The same shape in a downstream RISC-V development cost 11.7 s per `iexact`.
-/

@[expose] public section

namespace IrisTest.KernelIif
open Iris Iris.BI Iris.ProofMode

/-- Byte `j` (little-endian) of an `8*n`-bit word. -/
def nthByte {n : Nat} (w : BitVec (8 * n)) (j : Nat) : BitVec 8 := w.extractLsb' (8 * j) 8

/-- A 4- or 8-byte memory cell. -/
structure Cell where
  addr : BitVec 64
  w8 : Bool
  val : BitVec 64

variable {M : Type} [UCMRA M]
variable (hist : BitVec 64 → List (BitVec 8 × Nat) → UPred M) (win : BitVec 64 → Option (BitVec 64))

/-- The byte at `a` holds `v`: its history's latest entry. -/
def byte (a : BitVec 64) (v : BitVec 8) : UPred M :=
  iprop(∃ (e : BitVec 8 × Nat) (H : List (BitVec 8 × Nat)), hist a (e :: H) ∗ ⌜e.1 = v⌝)

/-- The `n`-byte word `w` at the aligned physical address `pa`. -/
def pword (pa : BitVec 64) (n : Nat) (w : BitVec (8 * n)) : UPred M :=
  iprop(⌜pa.toNat % n = 0⌝ ∗ [∗list] j ∈ List.range n, byte hist (pa + BitVec.ofNat 64 j) (nthByte w j))

/-- The `n`-byte word `w` at the virtual address `va`, through the translation `win`. -/
def cell (va : BitVec 64) (n : Nat) (w : BitVec (8 * n)) : UPred M :=
  iprop(∃ pa, ⌜win va = some pa⌝ ∗ pword hist pa n w)

/-- A cell of either width. -/
def cellRes (c : Cell) : UPred M :=
  if c.w8 then cell hist win c.addr 8 c.val else cell hist win c.addr 4 (BitVec.extractLsb' 0 32 c.val)

/- `iexact` leaves the kernel the check `□?false (cellRes …) =?= cellRes …`.
Kernel typechecking should be fast. -/
example (a w : BitVec 64) (Q : UPred M) :
    cellRes hist win ⟨a, true, w⟩ ∗ Q ⊢ cellRes hist win ⟨a, true, w⟩ := by
  iintro ⟨H, _⟩
  iexact H

/- The same on the right of the `∗`. Kernel typechecking should also be fast. -/
example (a w : BitVec 64) (Q : UPred M) :
    Q ∗ cellRes hist win ⟨a, true, w⟩ ⊢ cellRes hist win ⟨a, true, w⟩ := by
  iintro ⟨_, H⟩
  iexact H

end IrisTest.KernelIif
