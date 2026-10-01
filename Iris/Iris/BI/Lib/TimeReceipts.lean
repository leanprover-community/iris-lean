/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
module

public import Iris.Algebra.Lib.TimeReceipts
public import Iris.BI
public import Iris.ProofMode
public import Iris.Instances.IProp

@[expose] public section

/-!
# Time receipts

Time receipts are a resource tracking permissions to eliminate multiple laters around each
(program) step. As for later credits, there is a single instance of the time receipt ghost state,
with the authoritative supply `TimeReceipt.supply`.

There are two kinds of time receipts:

- Persistent time receipts `⧖□ n` represent a lower bound on the number of laters that can be
  eliminated each step, and the remaining number of later credits generated *during* each
  (program) step.
- Exclusive time receipts `⧖+ n` represent permissions to generate later credits *around* each
  (program) step.

Exclusive time receipts can be converted into persistent ones by either adding them to an existing
persistent time receipt (`TimeReceipt.pers_incr`), or by creating a persistent copy for the same
amount (`TimeReceipt.excl_pers_get`).

The supply is usually not used directly; it serves the internal model of the physical step
modality, which models the elimination of laters and generation of later credits using time
receipts.
-/

namespace Iris
open BI ProofMode

/-- The ghost state for time receipts is available in `GF`. -/
@[rocq_alias time_receiptGpreS]
class TimeReceiptGpreS (GF : BundledGFunctors) where
  elem : ElemG GF (constOF TimeReceipt)

attribute [reducible, instance] TimeReceiptGpreS.elem

/-- The ghost state for time receipts is available in `GF`, together with the name of its single
instance. -/
@[rocq_alias time_receiptGS]
class TimeReceiptGS (GF : BundledGFunctors) extends TimeReceiptGpreS GF where
  name : GName

#rocq_ignore «time_receiptΣ» "Superseded by the `TimeReceiptGpreS` typeclass on `BundledGFunctors`."
#rocq_ignore «subG_time_receiptΣ» "Superseded by Lean's direct `ElemG` typeclass synthesis."

namespace TimeReceipt

section Rules

variable {GF : BundledGFunctors} [TR : TimeReceiptGS GF]

/-- Ownership of `n` exclusive time receipts. Use it through the notation `⧖+ n`. -/
@[rocq_alias time_receipt_excl]
def excl (n : Nat) : IProp GF :=
  iOwn (E := TR.elem) TR.name (fragExcl n)

#rocq_ignore time_receipt_excl_def "`time_receipt_excl` is defined without `seal`/`unseal`."
#rocq_ignore time_receipt_excl_aux "`time_receipt_excl` is defined without `seal`/`unseal`."
#rocq_ignore time_receipt_excl_eq "`time_receipt_excl` is defined without `seal`/`unseal`."

/-- Ownership of a persistent time receipt for `n`. Use it through the notation `⧖□ n`. -/
@[rocq_alias time_receipt_pers]
def pers (n : Nat) : IProp GF :=
  iOwn (E := TR.elem) TR.name (fragPers n)

#rocq_ignore time_receipt_pers_def "`time_receipt_pers` is defined without `seal`/`unseal`."
#rocq_ignore time_receipt_pers_aux "`time_receipt_pers` is defined without `seal`/`unseal`."
#rocq_ignore time_receipt_pers_eq "`time_receipt_pers` is defined without `seal`/`unseal`."

/-- The authoritative supply of `m` time receipts. -/
@[rocq_alias time_receipt_supply]
def supply (m : Nat) : IProp GF :=
  iOwn (E := TR.elem) TR.name (auth m)

#rocq_ignore time_receipt_supply_def "`time_receipt_supply` is defined without `seal`/`unseal`."
#rocq_ignore time_receipt_supply_aux "`time_receipt_supply` is defined without `seal`/`unseal`."
#rocq_ignore time_receipt_supply_eq "`time_receipt_supply` is defined without `seal`/`unseal`."

notation:max "⧖+ " n:40 => excl n
notation:max "⧖□ " n:40 => pers n

@[rocq_alias time_receipt_excl_timeless]
instance {n : Nat} : Timeless (PROP := IProp GF) (⧖+ n) :=
  iOwn_timeless

@[rocq_alias time_receipt_excl_0_persistent]
instance : Persistent (PROP := IProp GF) (⧖+ 0) := by
  unfold excl
  infer_instance

@[rocq_alias time_receipt_pers_timeless]
instance {n : Nat} : Timeless (PROP := IProp GF) (⧖□ n) :=
  iOwn_timeless

@[rocq_alias time_receipt_pers_persistent]
instance {n : Nat} : Persistent (PROP := IProp GF) (⧖□ n) := by
  unfold pers
  infer_instance

@[rocq_alias time_receipt_excl_split]
theorem excl_split (n₁ n₂ : Nat) : ⧖+ (n₁ + n₂) ⊣⊢@{IProp GF} ⧖+ n₁ ∗ ⧖+ n₂ :=
  iOwn_op (E := TR.elem) (a1 := fragExcl n₁) (a2 := fragExcl n₂)

@[rocq_alias time_receipt_pers_split]
theorem pers_split (n₁ n₂ : Nat) : ⧖□ (max n₁ n₂) ⊣⊢@{IProp GF} ⧖□ n₁ ∗ ⧖□ n₂ :=
  iOwn_op (E := TR.elem) (a1 := fragPers n₁) (a2 := fragPers n₂)

@[rocq_alias time_receipt_excl_zero]
theorem excl_zero : ⊢@{IProp GF} |==> ⧖+ 0 :=
  iOwn_unit (ε := UCMRA.unit)

@[rocq_alias time_receipt_pers_zero]
theorem pers_zero : ⊢@{IProp GF} |==> ⧖□ 0 :=
  iOwn_unit (ε := UCMRA.unit)

@[rocq_alias time_receipt_excl_weaken]
theorem excl_weaken {n₁ : Nat} (n₂ : Nat) (h : n₂ ≤ n₁) : ⊢@{IProp GF} ⧖+ n₁ -∗ ⧖+ n₂ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  iintro H
  icases (excl_split n₂ k).mp $$ H with ⟨$, -⟩

@[rocq_alias time_receipt_pers_weaken]
theorem pers_weaken {n₁ : Nat} (n₂ : Nat) (h : n₂ ≤ n₁) : ⊢@{IProp GF} ⧖□ n₁ -∗ ⧖□ n₂ := by
  rw [← Nat.max_eq_right h]
  iintro H
  icases (pers_split n₂ n₁).mp $$ H with ⟨$, -⟩

@[rocq_alias time_receipt_excl_succ]
theorem excl_succ (n : Nat) : ⧖+ (.succ n) ⊣⊢@{IProp GF} ⧖+ 1 ∗ ⧖+ n :=
  Nat.succ_eq_one_add n ▸ excl_split 1 n

@[rocq_alias time_receipt_pers_incr]
theorem pers_incr (n₁ n₂ : Nat) : ⊢@{IProp GF} ⧖+ n₁ -∗ ⧖□ n₂ ==∗ ⧖□ (n₁ + n₂) := by
  unfold excl pers
  iintro Htr Htrp
  iapply iOwn_update_op (fragExcl_persist n₁ n₂) $$ [$Htr $Htrp]

@[rocq_alias time_receipt_excl_pers_get]
theorem excl_pers_get (n : Nat) : ⊢@{IProp GF} ⧖+ n ==∗ ⧖+ n ∗ ⧖□ n := by
  unfold excl pers
  iintro Htr
  imod iOwn_update (fragExcl_get_pers n) $$ Htr with ⟨$, $⟩

@[rocq_alias time_receipt_supply_pers_bound]
theorem supply_pers_bound (n m : Nat) : ⊢@{IProp GF} supply m -∗ ⧖□ n -∗ ⌜n ≤ m⌝ := by
  unfold supply pers
  iintro Hauth Htrp
  icombine Hauth Htrp gives %hop
  ipureintro
  exact (auth_op_fragPers_valid_iff ..).mp hop

@[rocq_alias time_receipt_supply_bound_both]
theorem supply_bound_both (n₁ n₂ m : Nat) :
    ⊢@{IProp GF} supply m -∗ ⧖+ n₁ -∗ ⧖□ n₂ -∗ ⌜n₁ + n₂ ≤ m⌝ := by
  iintro Hauth Htr Htrp
  imod pers_incr $$ Htr Htrp with Htrp
  iapply supply_pers_bound $$ Hauth Htrp

/-- Increments the supply by incrementing both the exclusive and the persistent partition by `k`,
so that the persistent partition remains at least as large as the exclusive one (as required by
`excl_pers_get`). Since the exact size of the persistent partition is unknown, a lower bound
`⧖□ n` is incremented. No exclusive time receipt is needed, since the resulting `⧖+ k` can be
combined with any existing exclusive time receipt afterwards. -/
@[rocq_alias time_receipt_supply_incr]
theorem supply_incr (k m n : Nat) :
    ⊢@{IProp GF} supply m -∗ ⧖□ n ==∗ supply (m + k + k) ∗ ⧖+ k ∗ ⧖□ (n + k) := by
  unfold supply excl pers
  iintro Hauth Htrp
  imod iOwn_update_op (auth_incr m n k) $$ [$Hauth $Htrp] with ⟨⟨$, $⟩, $⟩

/- The `.succ` rules take priority over the `+` rules, so `n + 1` splits off `1` first. -/

@[rocq_alias from_sep_time_receipt_excl_add]
instance (priority := default - 10) {n₁ n₂ : Nat} :
    FromSep (PROP := IProp GF) (⧖+ (n₁ + n₂)) (⧖+ n₁) (⧖+ n₂) where
  from_sep := (excl_split n₁ n₂).mpr

@[rocq_alias from_sep_time_receipt_excl_S]
instance (priority := default) {n : Nat} :
    FromSep (PROP := IProp GF) (⧖+ (.succ n)) (⧖+ 1) (⧖+ n) where
  from_sep := (excl_succ n).mpr

@[rocq_alias combine_sep_time_receipt_excl_add]
instance (priority := default) {n₁ n₂ : Nat} :
    CombineSepAs (PROP := IProp GF) (⧖+ n₁) (⧖+ n₂) (⧖+ (n₁ + n₂)) where
  combine_sep_as := (excl_split n₁ n₂).mpr

#rocq_ignore combine_sep_time_receipt_excl_S_l
  "Not necessary in Lean as it is more common to use +1 instead of .succ"

@[rocq_alias into_sep_time_receipt_excl_add]
instance (priority := default - 10) {n₁ n₂ : Nat} :
    IntoSep (PROP := IProp GF) (⧖+ (n₁ + n₂)) (⧖+ n₁) (⧖+ n₂) where
  into_sep := (excl_split n₁ n₂).mp

@[rocq_alias into_sep_time_receipt_excl_S]
instance (priority := default) {n : Nat} :
    IntoSep (PROP := IProp GF) (⧖+ (.succ n)) (⧖+ 1) (⧖+ n) where
  into_sep := (excl_succ n).mp

@[rocq_alias combine_sep_time_receipt_pers_max]
instance {n₁ n₂ : Nat} :
    CombineSepAs (PROP := IProp GF) (⧖□ n₁) (⧖□ n₂) (⧖□ (max n₁ n₂)) where
  combine_sep_as := (pers_split n₁ n₂).mpr

end Rules

@[rocq_alias time_receipt_supply_alloc]
theorem supply_alloc {GF : BundledGFunctors} [TimeReceiptGpreS GF] (n : Nat) :
    ⊢@{IProp GF} |==> ∃ _ : TimeReceiptGS GF, supply (n + n) ∗ ⧖+ n := by
  have hvalid := (auth_op_fragExcl_valid_iff (n + n) n).mpr (Nat.le_refl _)
  imod iOwn_alloc (E := TimeReceiptGpreS.elem) _ hvalid with ⟨%γ, Hauth, Htr⟩
  iexists { name := γ }
  unfold supply excl
  iframe

end TimeReceipt

end Iris
