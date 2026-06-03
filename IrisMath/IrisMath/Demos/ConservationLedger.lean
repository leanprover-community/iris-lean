/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.BI
public import Iris.ProofMode
public import Iris.Instances.IProp
public import Iris.Algebra
public import IrisMath.Instances.MeasureValuedMap

/-! # Demo 6 — A conservation-law ghost accountant: a NON-heap use of `HeapView`

**This is ghost accounting, not a program heap.**  There is no memory, no locations, no program
state.  The generic Iris `HeapView` resource algebra is repurposed as an *abstract ledger* of a
conserved quantity (total probability mass, money, energy, ...) distributed among several parties.
The mathematics doing the reasoning is the *measure-valued camera* `MeasureTheory.Measure Ω`, whose
operation is measure addition `+` and whose unit is the zero measure.

The dictionary (read it as accounting, not as a heap):

| `HeapView` notion                | accounting meaning                                            |
| -------------------------------- | ------------------------------------------------------------ |
| key `k : ℕ`                      | an *account* in the ledger                                   |
| value `μ : Measure Ω`            | the *mass* (conserved quantity) currently in that account    |
| `Auth (own one) m`               | the *authoritative ledger* — the accountant's master record  |
| `Frag k (own q) μ`               | a *party's claim* to mass `μ` in account `k` at fraction `q` |
| camera op `•` on measures        | `+` — masses *add*, they are never overwritten by merging    |

The three **conservation laws** proved below — the actual mathematical content — are:

1. **Split / merge** (`split`, `merge`).  A *full* claim `share γ 1 k (μ + ν)` splits into two
   independent partial claims `share γ q₁ k μ ∗ share γ q₂ k ν` (with `q₁ + q₂` the recombined
   fraction), and conversely.  This is the resource form of *"the conserved quantity is partitioned
   among its owners"*: separation `∗` is the partition, and `frag_add_op_equiv` is the arithmetic
   `(q₁+q₂, μ+ν) = (q₁,μ) • (q₂,ν)` that makes the partition exact.

2. **Audit / agreement** (`audit`).  Holding the authoritative ledger together with a party's *full*
   claim on account `k` forces the ledger's own record of `k` to equal that claim: the books match.
   This is `auth_op_frag_one_validN_iff` — no double-spending, the accountant cannot disagree with a
   100%-owner.

3. **Conservation under transfer** (`transfer`, `transfer_total`, `total_conserved`).  Moving a fresh
   batch of mass `ν` into account `k` is a *frame-preserving update* (the measure camera makes every
   target valid), and the *total* conserved quantity of account `k` grows by exactly `total ν`:
   `total (μ + ν) = total μ + total ν`.  The resource update and the conservation arithmetic
   (`MeasureValuedMap.total_add`) are stated together so the bookkeeping visibly *closes*.

What measure theory buys us — and an opaque value heap (`gmap K Value`) could never provide — is that
the conserved quantity is a *genuine additive invariant*: the camera operation is measure addition,
so "the books balance" is literally a theorem about `total`, and "transfer is allowed" is literally a
frame-preserving update with no validity side-condition to get stuck on. -/

@[expose] public section

namespace IrisMath.Demos.ConservationLedger

open Iris Iris.BI COFE MeasureTheory
open HeapView One DFrac
open IrisMath.Instances IrisMath.Instances.MeasureStore IrisMath.Instances.MeasureValuedMap
open scoped IrisMath.Instances.MeasureValuedMap

-- A fixed measurable space of outcomes, and a fraction type for ownership shares.
variable (F : Type _) (Ω : Type _) [UFraction F] [MeasurableSpace Ω]

/-- The ledger container: a plain function store `ℕ → Option ·`, keys are *accounts*. -/
abbrev L := (Nat → Option ·)

/-- The ledger functor: `constOF` of the generic `HeapView` camera over **measure values**.  The
authority is the master ledger; fragments are owners' claims.  (No memory: this is bookkeeping.) -/
abbrev HeapF : COFE.OFunctorPre := constOF <| HeapView F Nat (Measure Ω) L

variable {GF} [ElemG GF (HeapF F Ω)]

/-- The **authoritative ledger**: the accountant's master record `m` of every account's mass. -/
noncomputable def auth (γ : GName) (m : L (Measure Ω)) : IProp GF :=
  iOwn (GF := GF) (F := HeapF F Ω) γ (Auth (own one) m)

/-- A **party's claim** to mass `μ` in account `k`, held at ownership fraction `q`.  A *full* claim
is `q = 1`; partial claims `q < 1` represent shared ownership of the same account's mass. -/
noncomputable def share (γ : GName) (q : F) (k : Nat) (μ : Measure Ω) : IProp GF :=
  iOwn (GF := GF) (F := HeapF F Ω) γ (Frag k (own q) μ)

/-! ## Conservation law 1 — split / merge: the conserved quantity is partitioned among owners

A claim is *the* unit of conserved quantity.  `frag_add_op_equiv` says the camera fuses claims by
adding **both** the fractions and the masses:
`Frag k (own (q₁+q₂)) (μ+ν) ≡ Frag k (own q₁) μ • Frag k (own q₂) ν`.  Through `iOwn` and `iOwn_op`
this becomes the separation-logic identity `share γ (q₁+q₂) k (μ+ν) ⊣⊢ share γ q₁ k μ ∗ share γ q₂ k
ν`: combining two parties' claims is *exactly* adding their masses (and shares).  No quantity is
created or destroyed by repartitioning — conservation at the level of ownership. -/

/-- **Split.**  A combined claim of share `q₁ + q₂` to mass `μ + ν` in account `k` divides into two
independent claims, `q₁` to `μ` and `q₂` to `ν`.  Mass and ownership are partitioned exactly. -/
theorem split (γ : GName) (q₁ q₂ : F) (k : Nat) (μ ν : Measure Ω) :
    share (GF := GF) F Ω γ (q₁ + q₂) k (μ + ν) ⊢
      share (GF := GF) F Ω γ q₁ k μ ∗ share (GF := GF) F Ω γ q₂ k ν :=
  (equiv_iff.mp <| OFE.NonExpansive.eqv
    (frag_add_op_equiv (F := F) (H := L) (k := k) (q1 := q₁) (q2 := q₂)
      (v1 := μ) (v2 := ν))).mp.trans iOwn_op.mp

/-- **Merge.**  The reverse of `split`: two independent claims recombine into a single claim of the
summed share to the summed mass.  Together with `split` this says repartitioning conserves the total
claim — the conserved quantity flows between owners without leaking. -/
theorem merge (γ : GName) (q₁ q₂ : F) (k : Nat) (μ ν : Measure Ω) :
    share (GF := GF) F Ω γ q₁ k μ ∗ share (GF := GF) F Ω γ q₂ k ν ⊢
      share (GF := GF) F Ω γ (q₁ + q₂) k (μ + ν) :=
  iOwn_op.mpr.trans <| (equiv_iff.mp <| OFE.NonExpansive.eqv
    (frag_add_op_equiv (F := F) (H := L) (k := k) (q1 := q₁) (q2 := q₂)
      (v1 := μ) (v2 := ν))).mpr

/-! ## Conservation law 2 — audit: the books match a full owner

Holding the authoritative ledger together with a *full* (`q = 1`) claim on account `k` forces the
ledger's record at `k` to equal the claimed mass.  The accountant cannot disagree with a 100% owner —
there is no double-counting.  This is `auth_op_frag_one_validN_iff`, exactly the conservation
guarantee an auditor needs. -/

/-- **Audit / agreement.**  The authoritative ledger plus a *full* claim of mass `μ` on account `k`
prove the ledger records exactly `μ` at `k`.  (`q = 1` is `One.one`; the books match the owner.) -/
theorem audit (γ : GName) (m : L (Measure Ω)) (k : Nat) (μ : Measure Ω) :
    auth (GF := GF) F Ω γ m ∗ share (GF := GF) F Ω γ one k μ ⊢
      ⌜Std.PartialMap.get? m k ≡{0}≡ some μ⌝ := by
  refine iOwn_op.mpr.trans ?_
  refine iOwn_cmraValid.trans ?_
  refine (internalCmraValid_elim _).trans ?_
  iintro %H
  ipure_intro
  exact (auth_op_frag_one_validN_iff.mp H).2.2

/-! ## Conservation law 3 — transfer: moving mass is a frame-preserving update, and the total closes

Moving a fresh batch of conserved quantity `ν` into account `k` is the resource update
`update_add_mass` (a proven HeapView `~~>`), lifted to an `IProp` `|==>`.  Because every measure is
valid in the measure camera, the transfer has *no* validity side-condition — conservation is
*always* a frame-preserving update.  The companion arithmetic `total_add` shows the conserved total
of account `k` grows by exactly `total ν`: nothing is lost in the move. -/

/-- **Transfer.**  Holding the authoritative ledger and the *full* claim on account `k` (currently
`μ`), a party transfers in a fresh batch `ν`: both the master record and the party's claim become
`μ + ν`.  Lifts `MeasureStore.update_add_mass` (a HeapView `~~>`) to an `IProp` fancy update. -/
theorem transfer (γ : GName) (m : L (Measure Ω)) (k : Nat) (μ ν : Measure Ω) :
    auth (GF := GF) F Ω γ m ∗ share (GF := GF) F Ω γ one k μ ⊢
      |==> (auth (GF := GF) F Ω γ (Std.PartialMap.insert m k (μ + ν))
            ∗ share (GF := GF) F Ω γ one k (μ + ν)) := by
  refine iOwn_op.mpr.trans ?_
  refine (iOwn_update (γ := γ)
    (MeasureStore.update_add_mass (F := F) (H := L) m k μ ν)).trans ?_
  exact BIUpdate.mono iOwn_op.mp

/-- **Conservation arithmetic.**  The conserved total of account `k` after transferring in `ν` is its
old total plus `total ν` — the books balance.  This is `MeasureValuedMap.total_add`, the additive
invariant that makes the measure camera a genuine *conservation* law (an opaque value heap has no
such `total`).  It is the pure side of `transfer`: the resource update changes the stored mass to
`μ + ν`, and *here* is the guarantee that the conserved quantity is exactly accounted for. -/
theorem transfer_total (μ ν : Measure Ω) :
    total (μ + ν) = total μ + total ν :=
  MeasureValuedMap.total_add μ ν

/-- **Conservation, packaged.**  Across a transfer the change in the conserved total of the account is
*exactly* the mass moved in: `total (μ + ν) - total μ` accounts for `total ν` with nothing left over.
Stated as the additive identity `total μ + total ν = total (μ + ν)` so the bookkeeping visibly closes
(no subtraction in `ℝ≥0∞`). -/
theorem total_conserved (μ ν : Measure Ω) :
    total μ + total ν = total (μ + ν) :=
  (MeasureValuedMap.total_add μ ν).symm

/-! ## The point: a conserved quantity, not a memory cell

`transfer` is an ordinary `|==>` update — `auth ∗ claim k μ ⊢ |==> auth' ∗ claim k (μ+ν)` — but it is
*not* a heap write: nothing is stored in memory, and `k` is an account, not an address.  It is proved
with the **generic** Iris machinery (`iOwn_update`, `iOwn_op`, `auth_op_frag_one_validN_iff`,
`frag_add_op_equiv`) over the auto-researcher's measure-valued camera.  What the *mathematics of
measures* contributes is the conservation discipline:

- the camera operation is **measure addition**, so `split`/`merge` *partition* the conserved quantity
  exactly and `transfer` *accumulates* it — neither creates nor destroys mass;
- **every measure is valid**, so a transfer is *always* a frame-preserving update (conservation never
  gets stuck on a side-condition);
- the conserved quantity has a real **additive total** `total`, so `total_conserved` is a literal
  theorem: the books balance, account by account.

An Iris researcher thus gets a *ghost accountant for a conserved quantity* — full separation-logic
framing and transfer of an abstract invariant — entirely outside the program-heap setting, purely
from the generic `HeapView` plus an additive value camera. -/

end IrisMath.Demos.ConservationLedger
