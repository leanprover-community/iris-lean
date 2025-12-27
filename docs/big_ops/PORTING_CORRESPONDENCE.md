# Big Operations Porting Correspondence: Rocq to Lean

This document tracks the porting progress from Iris's `big_op.v` (Rocq) to Lean 4.

## Overview

The Rocq file covers big operations over:
1. **Lists** (`big_sepL`, `big_andL`, `big_orL`) - **Partially ported**
2. **Two Lists** (`big_sepL2`) - **Partially ported**
3. **Finite Maps** (`big_sepM`, `big_andM`, `big_sepM2`) - **Partially ported** (big_sepM ~95%, big_andM ~90%)
4. **Finite Sets** (`big_sepS`) - **Not ported**
5. **Multisets** (`big_sepMS`) - **Not ported**

### Lean Files

| Lean File | Contents |
|-----------|----------|
| `BigOp.lean` | Core definitions: `bigSepL`, `bigAndL`, `bigOrL` with notations |
| `BigOpList.lean` | Lemmas for `bigSepL` (big separating conjunction over lists) |
| `BigOpList2.lean` | Definition and lemmas for `bigSepL2` (over two lists) |
| `BigOpListAnd.lean` | Lemmas for `bigAndL` (big conjunction over lists) |
| `BigOpListOr.lean` | Lemmas for `bigOrL` (big disjunction over lists) |
| `BigOpMap.lean` | Core definitions: `bigSepM`, `bigAndM` with notations |
| `BigSepMap.lean` | Lemmas for `bigSepM` (big separating conjunction over maps) |
| `BigAndMap.lean` | Lemmas for `bigAndM` (big conjunction over maps) |

---

## Section 1: Big Separating Conjunction over Lists (`big_sepL`)

### Porting Status: **~100% Complete**

### Correspondence Table

| Rocq Lemma | Lean Theorem | Notes |
|------------|--------------|-------|
| `big_sepL_nil` | `BigSepL.nil` | Identical, `@[simp]` |
| `big_sepL_nil'` | `BigSepL.nil'` | Identical |
| - | `BigSepL.nil'_affine` | Affine context variant: `P ⊢ [∗ list] ...` when `[Affine P]` |
| `big_sepL_cons` | `BigSepL.cons` | Identical |
| `big_sepL_singleton` | `BigSepL.singleton` | Identical |
| `big_sepL_app` | `BigSepL.app` | Identical |
| `big_sepL_snoc` | `BigSepL.snoc` | Identical |
| `big_sepL_take_drop` | `BigSepL.take_drop` | Identical |
| `big_sepL_submseteq` | `BigSepL.submseteq` | Requires permutation witness |
| `big_sepL_mono` | `BigSepL.mono` | Identical |
| `big_sepL_ne` | `BigSepL.ne` | Non-expansiveness |
| `big_sepL_proper` | `BigSepL.proper` | Identical |
| - | `BigSepL.congr` | Unconditional version of proper |
| `big_sepL_mono'` | `BigSepL.mono'` | Unconditional version |
| `big_sepL_flip_mono'` | `BigSepL.flip_mono'` | Identical |
| `big_sepL_id_mono'` | `BigSepL.id_mono'` | Pairwise entailment on lists |
| `big_sepL_nil_persistent` | - | Trivially via emp, not explicit |
| `big_sepL_persistent` | `BigSepL.persistent_id` | For identity case |
| `big_sepL_persistent'` | `BigSepL.persistent` (instance) | Typeclass instance |
| `big_sepL_persistent_id` | `BigSepL.persistent_id` | Membership-based version |
| - | `BigSepL.persistent_cond` | Lookup-conditional: `∀ k x, l[k]? = some x → Persistent (Φ k x)` |
| `big_sepL_nil_affine` | - | Trivially via emp |
| `big_sepL_affine` | `BigSepL.affine_id` | For identity case |
| `big_sepL_affine'` | `BigSepL.affine` (instance) | Typeclass instance |
| `big_sepL_affine_id` | `BigSepL.affine_id` | Membership-based version |
| - | `BigSepL.affine_cond` | Lookup-conditional: `∀ k x, l[k]? = some x → Affine (Φ k x)` |
| `big_sepL_nil_timeless` | `BigSepL.nil_timeless` | Instance (requires Timeless emp) |
| `big_sepL_timeless` | - | Commented out (needs sep_timeless) |
| `big_sepL_timeless'` | - | Commented out |
| `big_sepL_timeless_id` | - | Commented out |
| `big_sepL_emp` | `BigSepL.emp_l` | Identical |
| `big_sepL_insert_acc` | `BigSepL.insert_acc` | Uses List.set instead of insert |
| `big_sepL_lookup_acc` | `BigSepL.lookup_acc` | Identical |
| `big_sepL_lookup` | `BigSepL.lookup` | Uses TCOr for Affine/Absorbing |
| `big_sepL_elem_of_acc` | `BigSepL.elem_of_acc` | Identical |
| `big_sepL_elem_of` | `BigSepL.elem_of` | Uses TCOr for Affine/Absorbing |
| `big_sepL_fmap` | `BigSepL.fmap` | Identical |
| `big_sepL_omap` | `BigSepL.omap` | Uses filterMap |
| `big_sepL_bind` | `BigSepL.bind` | Uses flatMap |
| `big_sepL_sep` | `BigSepL.sep'` | Identical |
| `big_sepL_sep_2` | `BigSepL.sep_2` | Identical (symmetric of sep') |
| `big_sepL_and` | `BigSepL.and'` | One direction only |
| `big_sepL_pure_1` | `BigSepL.pure_1` | Identical |
| `big_sepL_affinely_pure_2` | `BigSepL.affinely_pure_2` | Identical |
| `big_sepL_pure` | `BigSepL.pure'` | BIAffine version |
| `big_sepL_persistently` | `BigSepL.persistently` | BIAffine required |
| `big_sepL_intro` | `BigSepL.intro` | Requires Intuitionistic |
| `big_sepL_forall` | `BigSepL.forall'` | Identical (biconditional), BIAffine + Persistent |
| `big_sepL_impl` | `BigSepL.impl` | Identical |
| `big_sepL_wand` | `BigSepL.wand` | Identical |
| `big_sepL_dup` | `BigSepL.dup` | Identical (wand-first style), requires Affine P |
| `big_sepL_delete` | `BigSepL.delete` | Uses `if k = i then emp else Φ k y` |
| `big_sepL_delete'` | `BigSepL.delete'` | BIAffine version with implication |
| `big_sepL_lookup_acc_impl` | `BigSepL.lookup_acc_impl` | Most general form |
| `big_sepL_replicate` | `BigSepL.replicate` | Identical |
| `big_sepL_later` | `BigSepL.later` | BIAffine required |
| `big_sepL_later_2` | `BigSepL.later_2` | One direction (no BIAffine) |
| `big_sepL_laterN` | `BigSepL.laterN` | BIAffine required |
| `big_sepL_laterN_2` | `BigSepL.laterN_2` | One direction (no BIAffine) |
| `big_sepL_zip_seq` | `BigSepL.zip_seq` | Uses List.range' |
| - | `BigSepL.zip_with_range` | Sequence starting at 0 |
| `big_sepL_zip_seqZ` | - | Z version not ported |
| `big_sepL_sep_zip_with` | `BigSepL.sep_zip_with` | With extraction functions |
| `big_sepL_sep_zip` | `BigSepL.sep_zip` | Requires length proof |
| `big_sepL_zip_with` | `BigSepL.zip_with` | Uses match on lookup |
| `big_sepL_Permutation` | `BigSepL.perm` | Via BigOpL.perm |

### Differences

1. **Index type**: Rocq uses `nat`, Lean uses `Nat`
2. **List operations**: `l !! i` vs `l[k]?`, `<[i:=x]>l` vs `l.set i x`
3. **Timeless instances**: Commented out in Lean pending sep_timeless infrastructure
4. **TCOr pattern**: `lookup` and `elem_of` use `TCOr` typeclass for Affine/Absorbing disjunction

---

## Section 2: Big Separating Conjunction over Two Lists (`big_sepL2`)

### Porting Status: **~100% Complete**

### Correspondence Table

| Rocq Lemma | Lean Theorem | Status | Notes |
|------------|--------------|--------|-------|
| `big_sepL2_alt` | `BigSepL2.alt` | Ported | Alternative characterization via zip |
| `big_sepL2_nil` | `BigSepL2.nil` | Ported | Identical |
| `big_sepL2_nil'` | `BigSepL2.nil'` | Ported | Identical |
| `big_sepL2_nil_inv_l` | `BigSepL2.nil_inv_l` | Ported | Identical |
| `big_sepL2_nil_inv_r` | `BigSepL2.nil_inv_r` | Ported | Identical |
| `big_sepL2_cons` | `BigSepL2.cons` | Ported | Identical |
| `big_sepL2_cons_inv_l` | `BigSepL2.cons_inv_l` | Ported | Identical |
| `big_sepL2_cons_inv_r` | `BigSepL2.cons_inv_r` | Ported | Identical |
| `big_sepL2_singleton` | `BigSepL2.singleton` | Ported | Identical |
| `big_sepL2_length` | `BigSepL2.length` | Ported | Identical |
| `big_sepL2_fst_snd` | `BigSepL2.fst_snd` | Ported | Identical |
| `big_sepL2_app` | `BigSepL2.app'` | Ported | Identical |
| - | `BigSepL2.app` | Ported | Bi-directional with disjunctive condition `∨` (like Rocq's `app_same_length`) |
| `big_sepL2_app_inv_l` | `BigSepL2.app_inv_l` | Ported | Identical |
| `big_sepL2_app_inv_r` | `BigSepL2.app_inv_r` | Ported | Identical |
| `big_sepL2_app_inv` | `BigSepL2.app_inv` | Ported | Alias for app (disjunctive condition) |
| `big_sepL2_app_same_length` | `BigSepL2.app_same_length` | Ported | Disjunctive condition, different index shift |
| `big_sepL2_snoc` | `BigSepL2.snoc` | Ported | Identical |
| `big_sepL2_mono` | `BigSepL2.mono` | Ported | Identical |
| `big_sepL2_ne` | `BigSepL2.ne` | Ported | Identical |
| `big_sepL2_proper` | `BigSepL2.proper` | Ported | Identical |
| `big_sepL2_proper_2` | - | Not ported | Uses OFE on A, B |
| `big_sepL2_closed` | - | Not ported | Meta-lemma, direct inductive proofs used instead |
| `big_sepL2_nil_persistent` | - | Not ported | Trivially derivable via emp |
| `big_sepL2_persistent` | - | Not ported | Derivable via closed |
| `big_sepL2_persistent'` | `BigSepL2.persistent` (instance) | Ported | Typeclass instance |
| `big_sepL2_nil_affine` | - | Not ported | Trivially derivable via emp |
| `big_sepL2_affine` | - | Not ported | Derivable via closed |
| `big_sepL2_affine'` | `BigSepL2.affine` (instance) | Ported | Typeclass instance |
| `big_sepL2_nil_timeless` | - | Not ported | Requires sep_timeless infrastructure |
| `big_sepL2_timeless` | - | Not ported | Requires sep_timeless infrastructure |
| `big_sepL2_timeless'` | - | Not ported | Requires sep_timeless infrastructure |
| `big_sepL2_insert_acc` | `BigSepL2.insert_acc` | Ported | Identical |
| `big_sepL2_lookup_acc` | `BigSepL2.lookup_acc` | Ported | Identical |
| `big_sepL2_lookup` | `BigSepL2.lookup` | Ported | Uses TCOr for Affine/Absorbing |
| `big_sepL2_fmap_l` | `BigSepL2.fmap_l` | Ported | Identical |
| `big_sepL2_fmap_r` | `BigSepL2.fmap_r` | Ported | Identical |
| `big_sepL2_reverse_2` | `BigSepL2.reverse_2` | Ported | Identical |
| `big_sepL2_reverse` | `BigSepL2.reverse` | Ported | Identical |
| `big_sepL2_replicate_l` | `BigSepL2.replicate_l` | Ported | Identical |
| `big_sepL2_replicate_r` | `BigSepL2.replicate_r` | Ported | Identical |
| `big_sepL2_sep` | `BigSepL2.sep'` | Ported | Identical |
| `big_sepL2_sep_2` | `BigSepL2.sep_2` | Ported | Identical |
| `big_sepL2_and` | `BigSepL2.and'` | Ported | Identical |
| `big_sepL2_pure_1` | `BigSepL2.pure_1` | Ported | Identical |
| `big_sepL2_affinely_pure_2` | `BigSepL2.affinely_pure_2` | Ported | Identical |
| `big_sepL2_pure` | `BigSepL2.pure` | Ported | BIAffine required |
| `big_sepL2_persistently` | `BigSepL2.persistently` | Ported | BIAffine required |
| `big_sepL2_intro` | `BigSepL2.intro` | Ported | Identical |
| `big_sepL2_forall` | `BigSepL2.forall'` | Partial | BIAffine required, explicit Persistent argument |
| `big_sepL2_impl` | `BigSepL2.impl` | Ported | Identical |
| `big_sepL2_wand` | `BigSepL2.wand` | Ported | Identical |
| `big_sepL2_delete` | `BigSepL2.delete` | Ported | Identical |
| `big_sepL2_delete'` | `BigSepL2.delete'` | Ported | BIAffine required |
| `big_sepL2_lookup_acc_impl` | `BigSepL2.lookup_acc_impl` | Ported | Identical |
| `big_sepL2_later_1` | `BigSepL2.later_1` | Ported | BIAffine required, returns except-0 |
| `big_sepL2_later_2` | `BigSepL2.later_2` | Ported | Identical |
| `big_sepL2_later` | `BigSepL2.later` | Ported | BIAffine required |
| `big_sepL2_laterN_1` | `BigSepL2.laterN_1` | Ported | BIAffine required |
| `big_sepL2_laterN_2` | `BigSepL2.laterN_2` | Ported | Identical |
| `big_sepL2_laterN` | `BigSepL2.laterN` | Ported | BIAffine required |
| `big_sepL2_flip` | `BigSepL2.flip` | Ported | Identical |
| `big_sepL2_sepL` | `BigSepL2.sepL` | Ported | Identical |
| `big_sepL2_sepL_2` | `BigSepL2.sepL_2` | Ported | Identical |
| - | `BigSepL2.congr` | Ported | Lean-only: unconditional version of proper |
| - | `BigSepL2.mono'` | Ported | Lean-only: unconditional version of mono |
| - | `BigSepL2.flip_mono'` | Ported | Lean-only: flip of mono' |
| - | `BigSepL2.fmap` | Ported | Lean-only: combined fmap_l and fmap_r |
| - | `BigSepL2.emp_l` | Ported | Lean-only: BIAffine emp case |
| - | `BigSepL2.const_sepL_l` | Ported | Lean-only: BigSepL2 ignoring second list |
| - | `BigSepL2.const_sepL_r` | Ported | Lean-only: BigSepL2 ignoring first list |
| - | `BigSepL2.sep_sepL_l` | Ported | Lean-only: separate BigSepL from BigSepL2 (left) |
| - | `BigSepL2.sep_sepL_r` | Ported | Lean-only: separate BigSepL from BigSepL2 (right) |
| - | `BigSepL2.sepL2_diag` | Ported | Lean-only: diagonal BigSepL to BigSepL2 |

---

## Section 3: Big Conjunction over Lists (`big_andL`)

### Porting Status: **~100% Complete**

### Correspondence Table

| Rocq Lemma | Lean Theorem | Notes |
|------------|--------------|-------|
| `big_andL_nil` | `BigAndL.nil` | Identical, `@[simp]` |
| `big_andL_nil'` | `BigAndL.nil'` | Identical |
| `big_andL_cons` | `BigAndL.cons` | Identical |
| `big_andL_singleton` | `BigAndL.singleton` | Identical |
| `big_andL_app` | `BigAndL.app` | Identical |
| `big_andL_snoc` | `BigAndL.snoc` | Identical |
| `big_andL_take_drop` | `BigAndL.take_drop` | Identical |
| `big_andL_submseteq` | - | Not ported (uses stdpp `⊆+`) |
| `big_andL_mono` | `BigAndL.mono` | Identical |
| `big_andL_ne` | - | Not ported (OFE-level) |
| `big_andL_proper` | `BigAndL.proper` | Identical |
| - | `BigAndL.congr` | Lean-only: unconditional version |
| `big_andL_mono'` | - | Not ported |
| `big_andL_id_mono'` | - | Not ported |
| `big_andL_nil_absorbing` | - | Not ported |
| `big_andL_absorbing` | - | Not ported |
| `big_andL_absorbing'` | - | Not ported |
| `big_andL_nil_persistent` | - | Trivially via True |
| `big_andL_persistent` | - | Via closed |
| `big_andL_persistent'` | `BigAndL.persistent` (instance) | Typeclass instance |
| `big_andL_nil_timeless` | - | Not ported |
| `big_andL_timeless` | - | Not ported |
| `big_andL_timeless'` | - | Not ported |
| `big_andL_emp` | `BigAndL.true_l` | Named `true_l` (and uses True, not emp) |
| `big_andL_lookup` | `BigAndL.lookup` | Identical |
| `big_andL_elem_of` | `BigAndL.elem_of` | Identical |
| `big_andL_fmap` | `BigAndL.fmap` | Identical |
| `big_andL_bind` | `BigAndL.bind` | Uses flatMap |
| `big_andL_and` | `BigAndL.and'` | Identical |
| - | `BigAndL.and_2` | Lean-only: reverse direction |
| `big_andL_persistently` | `BigAndL.persistently` | Identical |
| `big_andL_forall` | `BigAndL.forall'` | Identical |
| `big_andL_intro` | `BigAndL.intro` | Identical |
| `big_andL_impl` | `BigAndL.impl` | Identical |
| `big_andL_pure_1` | `BigAndL.pure_1` | Identical |
| `big_andL_pure_2` | `BigAndL.pure_2` | Identical |
| `big_andL_pure` | `BigAndL.pure` | Identical (biconditional) |
| `big_andL_later` | `BigAndL.later` | Identical |
| `big_andL_laterN` | `BigAndL.laterN` | Identical |
| `big_andL_Permutation` | `BigAndL.perm` | Via BigOpL.perm |
| `big_andL_zip_seq` | `BigAndL.zip_seq` | Identical |
| `big_andL_zip_seqZ` | `BigAndL.zip_seqZ` | Uses Nat, not Z |
| - | `BigAndL.affine` (instance) | Lean-only: BIAffine instance |

---

## Section 4: Big Disjunction over Lists (`big_orL`)

### Porting Status: **~100% Complete**

### Correspondence Table

| Rocq Lemma | Lean Theorem | Notes |
|------------|--------------|-------|
| `big_orL_nil` | `BigOrL.nil` | Identical, `@[simp]` |
| `big_orL_nil'` | `BigOrL.nil'` | Identical |
| `big_orL_cons` | `BigOrL.cons` | Identical |
| `big_orL_singleton` | `BigOrL.singleton` | Identical |
| `big_orL_app` | `BigOrL.app` | Identical |
| `big_orL_snoc` | `BigOrL.snoc` | Identical |
| `big_orL_take_drop` | `BigOrL.take_drop` | Identical |
| `big_orL_submseteq` | `BigOrL.submseteq` | Uses permutation witness |
| `big_orL_mono` | `BigOrL.mono` | Identical |
| `big_orL_ne` | - | Not ported (OFE-level) |
| `big_orL_proper` | `BigOrL.proper` | Identical |
| - | `BigOrL.congr` | Lean-only: unconditional version |
| `big_orL_mono'` | `BigOrL.mono'` | Identical |
| `big_orL_id_mono'` | `BigOrL.id_mono'` | Uses indexed lookup |
| `big_orL_nil_persistent` | `BigOrL.nil_persistent` (instance) | Typeclass instance |
| `big_orL_persistent` | `BigOrL.persistent_cond` | Conditional version |
| `big_orL_persistent'` | `BigOrL.persistent` (instance) | Typeclass instance |
| `big_orL_nil_timeless` | - | Not ported |
| `big_orL_timeless` | - | Not ported |
| `big_orL_timeless'` | - | Not ported |
| `big_orL_false` | `BigOrL.false_l` | Identical |
| `big_orL_intro` | `BigOrL.intro` | Identical |
| `big_orL_elem_of` | `BigOrL.elem_of` | Identical |
| `big_orL_fmap` | `BigOrL.fmap` | Identical |
| `big_orL_bind` | `BigOrL.bind` | Uses flatMap |
| `big_orL_or` | `BigOrL.or'` | Identical |
| - | `BigOrL.or_2` | Lean-only: reverse direction |
| `big_orL_persistently` | `BigOrL.persistently` | Identical |
| `big_orL_exist` | `BigOrL.exist` | Identical |
| `big_orL_pure` | `BigOrL.pure` | Identical |
| `big_orL_sep_l` | `BigOrL.sep_l` | Identical |
| `big_orL_sep_r` | `BigOrL.sep_r` | Identical |
| `big_orL_later` | `BigOrL.later` | Requires non-empty list |
| `big_orL_laterN` | `BigOrL.laterN` | Requires non-empty list |
| `big_orL_Permutation` | `BigOrL.perm` | Via BigOpL.perm |
| `big_orL_zip_seq` | `BigOrL.zip_seq` | Identical |
| `big_orL_zip_seqZ` | `BigOrL.zip_seqZ` | Uses Nat, not Z |

---

## Section 5: Big Separating Conjunction over Maps (`big_sepM`)

### Porting Status: **Partially Complete** (Abstract interface: **Complete**, Core lemmas: **Complete**)

### Design Decision: Abstract Map Interface

**IMPORTANT**: Unlike Rocq's Iris which uses concrete `gmap K A` from stdpp, the Lean port defines an **abstract finite map interface** in `Iris.Std.FiniteMap`. This allows:
1. Flexibility to swap implementations (HashMap, RBMap, etc.)
2. Better alignment with Lean's design philosophy
3. Reuse across different concrete map types

#### Implemented Abstract Interface

The interface is implemented as typeclass `FiniteMap M K V` in `Iris/Std/FiniteMap.lean`:

| Operation | Rocq (gmap) | Lean Interface | Status |
|-----------|-------------|----------------|--------|
| `m !! k` | `m !! k` | `get? m k` | ✅ Implemented |
| `<[k:=v]> m` | `<[i:=x]> m` | `insert m k v` | ✅ Implemented |
| `delete k m` | `delete i m` | `erase m k` | ✅ Implemented |
| `∅` | `∅` | `∅` (via `EmptyCollection`) | ✅ Implemented |
| `{[k:=v]}` | `{[i:=x]}` | `{[k := v]}` (notation) | ✅ Implemented |
| `m1 ∪ m2` | `m1 ∪ m2` | `m1 ∪ m2` (via `Union`) | ✅ Implemented |
| `dom m` | `dom m` | `FiniteMap.dom m` | ✅ Implemented |
| `m1 ##ₘ m2` | `m1 ##ₘ m2` | `m1 ##ₘ m2` (notation) | ✅ Implemented |
| `m2 ⊆ m1` | `m2 ⊆ m1` | `m2 ⊆ m1` (via `HasSubset`) | ✅ Implemented |
| `f <$> m` | `f <$> m` | `FiniteMap.map f m` | ✅ Implemented |
| `omap f m` | `omap f m` | `FiniteMap.filterMap f m` | ✅ Implemented |
| `filter φ m` | `filter φ m` | `FiniteMap.filter φ m` | ✅ Implemented |
| `map_to_list m` | `map_to_list m` | `toList m` | ✅ Implemented |
| `list_to_map l` | `list_to_map l` | `ofList l` | ✅ Implemented |
| `map_zip m1 m2` | `map_zip m1 m2` | `FiniteMap.zip m1 m2` | ✅ Implemented |

#### Implemented Properties (FiniteMapLaws typeclass)

The `FiniteMapLaws M K V` typeclass provides the required laws:
- ✅ `get?_empty` - Empty map lookup returns `none`
- ✅ `get?_insert_eq` / `get?_insert_ne` - Insert lookup laws
- ✅ `get?_erase_eq` / `get?_erase_ne` - Erase lookup laws
- ✅ `get?_ofList` - List conversion law

Additional theorems provided:
- ✅ `submap_refl`, `submap_trans` - Submap is a preorder
- ✅ `disjoint_symm` - Disjointness is symmetric
- ✅ `disjoint_empty_left`, `disjoint_empty_right` - Empty is disjoint from everything
- ✅ `empty_submap` - Empty is a submap of everything
- ✅ `dom_empty`, `dom_insert` - Domain properties

**Next steps**: Provide concrete instances (HashMap, RBMap) and port big_sepM lemmas.

### Lean Implementation Files

| Lean File | Contents |
|-----------|----------|
| `Iris/BI/BigOpMap.lean` | Core definitions: `bigSepM`, `bigAndM` with notations |
| `Iris/BI/BigSepMap.lean` | Lemmas for `bigSepM` (big separating conjunction over maps) |

### Correspondence Table

| Rocq Lemma | Lean Theorem | Status | Notes |
|------------|--------------|--------|-------|
| `big_sepM_mono` | `BigSepM.mono` | ✅ Ported | Conditional on `get? m k = some v` |
| `big_sepM_ne` | `BigSepM.ne` | ✅ Ported | Non-expansiveness |
| `big_sepM_proper` | `BigSepM.proper` | ✅ Ported | Conditional proper |
| - | `BigSepM.congr` | ✅ Ported | Lean-only: unconditional proper |
| `big_sepM_mono'` | `BigSepM.mono'` | ✅ Ported | Unconditional mono |
| `big_sepM_flip_mono'` | `BigSepM.flip_mono'` | ✅ Ported | Flip of mono' |
| `big_sepM_empty_persistent` | `BigSepM.empty_persistent` (instance) | ✅ Ported | |
| `big_sepM_persistent` | `BigSepM.persistent_cond` | ✅ Ported | Conditional version |
| `big_sepM_persistent'` | `BigSepM.persistent` (instance) | ✅ Ported | Global instance `[∀ k v, Persistent (Φ k v)]` |
| `big_sepM_empty_affine` | `BigSepM.empty_affine` (instance) | ✅ Ported | |
| `big_sepM_affine` | `BigSepM.affine_cond` | ✅ Ported | Conditional version |
| `big_sepM_affine'` | `BigSepM.affine` (instance) | ✅ Ported | Global instance `[∀ k v, Affine (Φ k v)]` |
| `big_sepM_empty_timeless` | - | Not ported | Requires Timeless emp |
| `big_sepM_timeless` | - | Not ported | Requires sep_timeless |
| `big_sepM_timeless'` | - | Not ported | Requires sep_timeless |
| `big_sepM_subseteq` | `BigSepM.subseteq` | ⚠️ Sorry | Requires map difference/union laws |
| `big_sepM_empty` | `BigSepM.empty` | ✅ Ported | `@[simp]` |
| `big_sepM_empty'` | `BigSepM.empty'` | ✅ Ported | Affine intro |
| `big_sepM_insert` | `BigSepM.insert` | ✅ Ported | Requires `get? m k = none` |
| `big_sepM_delete` | `BigSepM.delete` | ✅ Ported | Added `toList_erase` law |
| `big_sepM_insert_delete` | `BigSepM.insert_delete` | ✅ Ported | Uses permutation |
| `big_sepM_insert_2` | `BigSepM.insert_2` | ✅ Ported | Affine version |
| - | `BigSepM.insert_2_absorbing` | ✅ Ported | Lean-only: Absorbing version |
| `big_sepM_lookup_acc` | `BigSepM.lookup_acc` | ✅ Ported | Uses delete |
| `big_sepM_lookup` | `BigSepM.lookup` | ✅ Ported | Affine version |
| - | `BigSepM.lookup_absorbing` | ✅ Ported | Lean-only: Absorbing version |
| `big_sepM_lookup_dom` | `BigSepM.lookup_dom` | ✅ Ported | Affine version, domain lookup |
| `big_sepM_singleton` | `BigSepM.singleton` | ✅ Ported | |
| `big_sepM_fmap` | `BigSepM.fmap` | ✅ Ported | Requires permutation proof |
| `big_sepM_omap` | `BigSepM.omap` | ✅ Ported | Requires permutation proof |
| `big_sepM_insert_override` | `BigSepM.insert_override` | ✅ Ported | |
| `big_sepM_insert_override_1` | `BigSepM.insert_override_1` | ✅ Ported | |
| `big_sepM_insert_override_2` | `BigSepM.insert_override_2` | ✅ Ported | |
| `big_sepM_insert_acc` | `BigSepM.insert_acc` | ✅ Ported | Uses delete + forall wand |
| `big_sepM_fn_insert` | - | Not ported | Low priority |
| `big_sepM_fn_insert'` | - | Not ported | Low priority |
| `big_sepM_filter'` | `BigSepM.filter'` | ✅ Ported | φ : K × V → Prop with Decidable, needs FiniteMapLawsSelf |
| `big_sepM_filter` | `BigSepM.filter` | ✅ Ported | BiAffine, φ : K × V → Prop with Decidable, needs FiniteMapLawsSelf |
| `big_sepM_union` | `BigSepM.union` | ✅ Ported | Requires permutation proof |
| `big_sepM_sep` | `BigSepM.sep'` | ✅ Ported | Via BigOpL.op_distr |
| `big_sepM_sep_2` | `BigSepM.sep_2` | ✅ Ported | Symmetric of sep' |
| `big_sepM_and` | `BigSepM.and'` | ✅ Ported | One direction only |
| `big_sepM_pure_1` | `BigSepM.pure_1` | ✅ Ported | Uses mapForall definition |
| `big_sepM_affinely_pure_2` | `BigSepM.affinely_pure_2` | ✅ Ported | Uses mapForall definition |
| `big_sepM_pure` | `BigSepM.pure'` | ✅ Ported | BiAffine, combines pure_1 + affinely_pure_2 |
| `big_sepM_persistently` | `BigSepM.persistently` | ✅ Ported | BiAffine required |
| `big_sepM_intro` | `BigSepM.intro` | ✅ Ported | Uses [Intuitionistic P] instead of □ |
| `big_sepM_forall` | `BigSepM.forall'` | ✅ Ported | BiAffine + Persistent, biconditional |
| - | `BigSepM.forall_1'` | ✅ Ported | Lean-only: forward direction |
| - | `BigSepM.forall_2'` | ✅ Ported | Lean-only: backward direction |
| `big_sepM_impl` | `BigSepM.impl` | ✅ Ported | Uses □ for intuitionistic condition |
| `big_sepM_wand` | `BigSepM.wand` | ✅ Ported | |
| `big_sepM_dup` | `BigSepM.dup` | ✅ Ported | Requires [Affine P] |
| `big_sepM_lookup_acc_impl` | `BigSepM.lookup_acc_impl` | ✅ Ported | Uses delete + impl pattern |
| `big_sepM_later` | `BigSepM.later` | ✅ Ported | BiAffine required |
| `big_sepM_later_2` | `BigSepM.later_2` | ✅ Ported | No BiAffine needed |
| `big_sepM_laterN` | `BigSepM.laterN` | ✅ Ported | BiAffine required |
| `big_sepM_laterN_2` | `BigSepM.laterN_2` | ✅ Ported | No BiAffine needed |
| `big_sepM_map_to_list` | `BigSepM.map_to_list` | ✅ Ported | Uses `[∗ list]` notation |
| `big_sepM_list_to_map` | `BigSepM.list_to_map` | ✅ Ported | Requires permutation proof |
| `big_sepM_sep_zip_with` | - | Not ported | Low priority |
| `big_sepM_sep_zip` | - | Not ported | Low priority |
| `big_sepM_impl_strong` | - | Not ported | Low priority |
| `big_sepM_impl_dom_subseteq` | - | Not ported | Low priority |
| `big_sepM_kmap` | - | Not ported | Low priority |
| `big_sepM_map_seq` | - | Not ported | Low priority |

### Summary

**Ported: 55 lemmas** (including Lean-only additions)

Key lemmas ported:
- Structural: `empty`, `empty'`, `singleton`, `insert`, `delete`, `insert_delete`
- Insert variants: `insert_acc`, `insert_2`, `insert_2_absorbing`, `insert_override`, `insert_override_1`, `insert_override_2`
- Lookup: `lookup_acc`, `lookup`, `lookup_absorbing`, `lookup_dom`, `lookup_acc_impl`
- Monotonicity: `mono`, `proper`, `congr`, `ne`, `mono'`, `flip_mono'`
- Submap: `subseteq` (sorry - needs map difference/union laws)
- Instances: `empty_persistent`, `persistent_cond`, `persistent`, `empty_affine`, `affine_cond`, `affine`
- Logical: `sep'`, `sep_2`, `and'`, `wand`, `union`
- Intro/Forall/Impl: `intro`, `forall'`, `forall_1'`, `forall_2'`, `impl`, `dup`
- Modalities: `persistently`, `later`, `later_2`, `laterN`, `laterN_2`
- Conversion: `map_to_list`, `list_to_map`
- Map transformations: `fmap`, `omap`
- Pure: `pure_1`, `affinely_pure_2`, `pure'` (uses mapForall definition)
- Filter: `filter'`, `filter''` (requires FiniteMapLawsSelf)

**Not ported:** ~5 lemmas (mostly requiring additional map laws or low priority)

**Note:** The newly ported lemmas (`fmap`, `omap`, `union`, `list_to_map`) take explicit permutation proofs as arguments instead of using typeclasses. This design allows users to provide the necessary permutation proofs for their specific map implementations.

---

## Section 6: Big Conjunction over Maps (`big_andM`)

### Porting Status: **~90% Complete**

### Lean Implementation File

| Lean File | Contents |
|-----------|----------|
| `Iris/BI/BigAndMap.lean` | Lemmas for `bigAndM` (big conjunction over maps) |

### Correspondence Table

| Rocq Lemma | Lean Theorem | Status | Notes |
|------------|--------------|--------|-------|
| `big_andM_mono` | `BigAndM.mono` | ✅ Ported | Conditional on `get? m k = some v` |
| `big_andM_ne` | `BigAndM.ne` | ✅ Ported | Non-expansiveness |
| `big_andM_proper` | `BigAndM.proper` | ✅ Ported | Conditional proper |
| - | `BigAndM.congr` | ✅ Ported | Lean-only: unconditional proper |
| `big_andM_mono'` | `BigAndM.mono'` | ✅ Ported | Unconditional mono |
| `big_andM_empty_persistent` | `BigAndM.empty_persistent` (instance) | ✅ Ported | |
| `big_andM_persistent` | `BigAndM.persistent_cond` | ✅ Ported | Conditional version |
| `big_andM_persistent'` | `BigAndM.persistent` (instance) | ✅ Ported | Global instance `[∀ k v, Persistent (Φ k v)]` |
| - | `BigAndM.affine` (instance) | ✅ Ported | Lean-only: BIAffine instance |
| `big_andM_empty_timeless` | - | Not ported | Requires Timeless infrastructure |
| `big_andM_timeless` | - | Not ported | Requires and_timeless |
| `big_andM_timeless'` | - | Not ported | Requires and_timeless |
| `big_andM_subseteq` | `BigAndM.subseteq` | ⚠️ Sorry | Needs map difference/union laws |
| `big_andM_empty` | `BigAndM.empty` | ✅ Ported | `@[simp]` |
| `big_andM_empty'` | `BigAndM.empty'` | ✅ Ported | |
| `big_andM_insert` | `BigAndM.insert` | ✅ Ported | Requires `get? m k = none` |
| `big_andM_delete` | `BigAndM.delete` | ✅ Ported | |
| `big_andM_insert_delete` | `BigAndM.insert_delete` | ✅ Ported | |
| `big_andM_insert_2` | `BigAndM.insert_2` | ✅ Ported | |
| `big_andM_lookup` | `BigAndM.lookup` | ✅ Ported | |
| `big_andM_lookup_dom` | `BigAndM.lookup_dom` | ✅ Ported | |
| `big_andM_singleton` | `BigAndM.singleton` | ✅ Ported | |
| `big_andM_fmap` | `BigAndM.fmap` | ✅ Ported | Requires permutation proof |
| `big_andM_omap` | `BigAndM.omap` | ✅ Ported | Requires permutation proof |
| `big_andM_fn_insert` | - | Not ported | Low priority |
| `big_andM_fn_insert'` | - | Not ported | Low priority |
| `big_andM_filter'` | `BigAndM.filter'` | ✅ Ported | Needs FiniteMapLawsSelf |
| `big_andM_filter` | `BigAndM.filter''` | ✅ Ported | Uses implication guard |
| `big_andM_union` | `BigAndM.union` | ✅ Ported | Requires permutation proof |
| `big_andM_and` | `BigAndM.and'` | ✅ Ported | Biconditional |
| `big_andM_persistently` | `BigAndM.persistently` | ✅ Ported | |
| `big_andM_intro` | `BigAndM.intro` | ✅ Ported | Simpler than BigSepM.intro (no Intuitionistic needed) |
| `big_andM_forall` | `BigAndM.forall'` | ✅ Ported | Biconditional |
| `big_andM_impl` | `BigAndM.impl` | ✅ Ported | |
| `big_andM_pure_1` | `BigAndM.pure_1` | ✅ Ported | Uses mapForall definition |
| `big_andM_pure_2` | `BigAndM.pure_2` | ✅ Ported | Uses mapForall definition |
| `big_andM_pure` | `BigAndM.pure'` | ✅ Ported | Biconditional |
| `big_andM_later` | `BigAndM.later` | ✅ Ported | |
| `big_andM_laterN` | `BigAndM.laterN` | ✅ Ported | |
| - | `BigAndM.map_to_list` | ✅ Ported | Lean-only: conversion to list |
| `big_andM_kmap` | - | Not ported | Low priority |
| `big_andM_map_seq` | - | Not ported | Low priority |

### Summary

**Ported: ~35 lemmas** (including Lean-only additions)

Key lemmas ported:
- Structural: `empty`, `empty'`, `singleton`, `insert`, `delete`, `insert_delete`, `insert_2`
- Lookup: `lookup`, `lookup_dom`
- Monotonicity: `mono`, `proper`, `congr`, `ne`, `mono'`
- Submap: `subseteq` (sorry - needs map difference/union laws)
- Instances: `empty_persistent`, `persistent_cond`, `persistent`, `affine`
- Logical: `and'`, `persistently`, `union`
- Intro/Forall/Impl: `intro`, `forall'`, `impl`
- Modalities: `later`, `laterN`
- Conversion: `map_to_list`
- Map transformations: `fmap`, `omap`
- Pure: `pure_1`, `pure_2`, `pure'` (uses mapForall definition)
- Filter: `filter'`, `filter''` (requires FiniteMapLawsSelf)

**Not ported:** ~5 lemmas (mostly requiring additional infrastructure or low priority)

---

## Section 7: Big Separating Conjunction over Two Maps (`big_sepM2`)

### Porting Status: **Not Started**

### Design Notes

`big_sepM2` operates over two maps with matching domains. The definition includes a pure proposition asserting domain equality:
```
[∗ map] k↦y1;y2 ∈ m1; m2, Φ k y1 y2 ⊣⊢ ⌜dom m1 = dom m2⌝ ∧ [∗ map] k↦xy ∈ map_zip m1 m2, Φ k xy.1 xy.2
```

### Correspondence Table

| Rocq Lemma | Lean Theorem | Priority | Notes |
|------------|--------------|----------|-------|
| `big_sepM2_alt` | `BigSepM2.alt` | High | Fundamental characterization |
| `big_sepM2_alt_lookup` | `BigSepM2.alt_lookup` | Medium | Via is_Some |
| `big_sepM2_lookup_iff` | `BigSepM2.lookup_iff` | High | Domain correspondence |
| `big_sepM2_dom` | `BigSepM2.dom` | High | Domain equality |
| `big_sepM2_flip` | `BigSepM2.flip` | High | Swap maps |
| `big_sepM2_empty` | `BigSepM2.empty` | High | `@[simp]` |
| `big_sepM2_empty'` | `BigSepM2.empty'` | Medium | |
| `big_sepM2_empty_l` | `BigSepM2.empty_l` | Medium | |
| `big_sepM2_empty_r` | `BigSepM2.empty_r` | Medium | |
| `big_sepM2_insert` | `BigSepM2.insert` | High | Both maps |
| `big_sepM2_mono` | `BigSepM2.mono` | High | |
| `big_sepM2_ne` | `BigSepM2.ne` | Medium | |
| `big_sepM2_proper` | `BigSepM2.proper` | High | |
| `big_sepM2_proper_2` | `BigSepM2.proper_2` | Low | OFE version |
| `big_sepM2_ne'` | `BigSepM2.ne'` (instance) | Medium | |
| `big_sepM2_mono'` | `BigSepM2.mono'` (instance) | Medium | |
| `big_sepM2_flip_mono'` | `BigSepM2.flip_mono'` (instance) | Low | |
| `big_sepM2_proper'` | `BigSepM2.proper'` (instance) | Medium | |
| `big_sepM2_closed` | - | Low | Meta-lemma |
| `big_sepM2_empty_persistent` | `BigSepM2.empty_persistent` (instance) | Medium | |
| `big_sepM2_persistent` | `BigSepM2.persistent` | Medium | |
| `big_sepM2_persistent'` | `BigSepM2.persistent` (instance) | Medium | |
| `big_sepM2_empty_affine` | `BigSepM2.empty_affine` (instance) | Medium | |
| `big_sepM2_affine` | `BigSepM2.affine` | Medium | |
| `big_sepM2_affine'` | `BigSepM2.affine` (instance) | Medium | |
| `big_sepM2_empty_timeless` | - | Low | |
| `big_sepM2_timeless` | - | Low | |
| `big_sepM2_timeless'` | - | Low | |
| `big_sepM2_delete` | `BigSepM2.delete` | High | |
| `big_sepM2_delete_l` | `BigSepM2.delete_l` | Medium | Existential |
| `big_sepM2_delete_r` | `BigSepM2.delete_r` | Medium | Existential |
| `big_sepM2_insert_delete` | `BigSepM2.insert_delete` | High | |
| `big_sepM2_insert_acc` | `BigSepM2.insert_acc` | High | |
| `big_sepM2_insert_2` | `BigSepM2.insert_2` | Medium | Uses TCOr |
| `big_sepM2_lookup_acc` | `BigSepM2.lookup_acc` | High | |
| `big_sepM2_lookup` | `BigSepM2.lookup` | High | Uses TCOr |
| `big_sepM2_lookup_l` | `BigSepM2.lookup_l` | Medium | |
| `big_sepM2_lookup_r` | `BigSepM2.lookup_r` | Medium | |
| `big_sepM2_singleton` | `BigSepM2.singleton` | High | |
| `big_sepM2_fst_snd` | `BigSepM2.fst_snd` | Medium | |
| `big_sepM2_fmap` | `BigSepM2.fmap` | High | Both maps |
| `big_sepM2_fmap_l` | `BigSepM2.fmap_l` | Medium | |
| `big_sepM2_fmap_r` | `BigSepM2.fmap_r` | Medium | |
| `big_sepM2_sep` | `BigSepM2.sep'` | High | |
| `big_sepM2_sep_2` | `BigSepM2.sep_2` | High | |
| `big_sepM2_and` | `BigSepM2.and'` | Medium | |
| `big_sepM2_pure_1` | `BigSepM2.pure_1` | Medium | |
| `big_sepM2_affinely_pure_2` | `BigSepM2.affinely_pure_2` | Medium | |
| `big_sepM2_pure` | `BigSepM2.pure` | Medium | BiAffine |
| `big_sepM2_persistently` | `BigSepM2.persistently` | Medium | BiAffine |
| `big_sepM2_intro` | `BigSepM2.intro` | High | |
| `big_sepM2_forall` | `BigSepM2.forall'` | Medium | BiAffine + Persistent |
| `big_sepM2_impl` | `BigSepM2.impl` | High | |
| `big_sepM2_wand` | `BigSepM2.wand` | High | |
| `big_sepM2_lookup_acc_impl` | `BigSepM2.lookup_acc_impl` | Medium | |
| `big_sepM2_later_1` | `BigSepM2.later_1` | Medium | Returns except-0 |
| `big_sepM2_later_2` | `BigSepM2.later_2` | Medium | |
| `big_sepM2_laterN_2` | `BigSepM2.laterN_2` | Medium | |
| `big_sepM2_sepM` | `BigSepM2.sepM` | Medium | Split to two BigSepM |
| `big_sepM2_sepM_2` | `BigSepM2.sepM_2` | Medium | |
| `big_sepM2_union_inv_l` | `BigSepM2.union_inv_l` | Low | |
| `big_sepM2_union_inv_r` | `BigSepM2.union_inv_r` | Low | |
| `big_sepM_sepM2_diag` | `BigSepM.sepM2_diag` | Medium | Diagonal |
| `big_sepM2_ne_2` | `BigSepM2.ne_2` | Low | OFE version |

---

## Section 8: Big Separating Conjunction over Sets (`big_sepS`)

### Porting Status: **Not Started**

### Design Decision: Abstract Set Interface

Similar to maps, the Lean port should use an **abstract finite set interface** rather than `gset A`. The interface (tentatively `FiniteSet A`) should provide:

| Operation | Rocq (gset) | Lean Interface | Description |
|-----------|-------------|----------------|-------------|
| `x ∈ X` | `x ∈ X` | `x ∈ X` | Membership |
| `∅` | `∅` | `∅` | Empty set |
| `{[ x ]}` | `{[ x ]}` | `{x}` | Singleton |
| `X ∪ Y` | `X ∪ Y` | `X ∪ Y` | Union |
| `X ## Y` | `X ## Y` | `X.Disjoint Y` | Disjoint |
| `X ∖ Y` | `X ∖ Y` | `X \ Y` | Difference |
| `Y ⊆ X` | `Y ⊆ X` | `Y ⊆ X` | Subset |
| `filter φ X` | `filter φ X` | `X.filter φ` | Filter |
| `elements X` | `elements X` | `X.toList` | To list |
| `list_to_set l` | `list_to_set l` | `.ofList l` | From list |

### Correspondence Table

| Rocq Lemma | Lean Theorem | Priority | Notes |
|------------|--------------|----------|-------|
| `big_sepS_mono` | `BigSepS.mono` | High | |
| `big_sepS_ne` | `BigSepS.ne` | Medium | |
| `big_sepS_proper` | `BigSepS.proper` | High | |
| `big_sepS_mono'` | `BigSepS.mono'` (instance) | Medium | |
| `big_sepS_flip_mono'` | `BigSepS.flip_mono'` (instance) | Low | |
| `big_sepS_empty_persistent` | `BigSepS.empty_persistent` (instance) | Medium | |
| `big_sepS_persistent` | `BigSepS.persistent` | Medium | |
| `big_sepS_persistent'` | `BigSepS.persistent` (instance) | Medium | |
| `big_sepS_empty_affine` | `BigSepS.empty_affine` (instance) | Medium | |
| `big_sepS_affine` | `BigSepS.affine` | Medium | |
| `big_sepS_affine'` | `BigSepS.affine` (instance) | Medium | |
| `big_sepS_empty_timeless` | - | Low | |
| `big_sepS_timeless` | - | Low | |
| `big_sepS_timeless'` | - | Low | |
| `big_sepS_subseteq` | `BigSepS.subseteq` | Medium | Requires Affine |
| `big_sepS_elements` | `BigSepS.elements` | High | To list |
| `big_sepS_empty` | `BigSepS.empty` | High | `@[simp]` |
| `big_sepS_empty'` | `BigSepS.empty'` | Medium | |
| `big_sepS_emp` | `BigSepS.emp` | Medium | All emp |
| `big_sepS_insert` | `BigSepS.insert` | High | |
| `big_sepS_fn_insert` | `BigSepS.fn_insert` | Low | |
| `big_sepS_fn_insert'` | `BigSepS.fn_insert'` | Low | |
| `big_sepS_union` | `BigSepS.union` | High | Disjoint |
| `big_sepS_delete` | `BigSepS.delete` | High | |
| `big_sepS_insert_2` | `BigSepS.insert_2` | Medium | Uses TCOr |
| `big_sepS_insert_2'` | `BigSepS.insert_2'` | Medium | |
| `big_sepS_union_2` | `BigSepS.union_2` | Medium | |
| `big_sepS_delete_2` | `BigSepS.delete_2` | Medium | |
| `big_sepS_elem_of` | `BigSepS.elem_of` | High | Uses TCOr |
| `big_sepS_elem_of_acc` | `BigSepS.elem_of_acc` | High | |
| `big_sepS_singleton` | `BigSepS.singleton` | High | |
| `big_sepS_filter'` | `BigSepS.filter'` | Medium | |
| `big_sepS_filter` | `BigSepS.filter` | Medium | BiAffine |
| `big_sepS_filter_acc'` | `BigSepS.filter_acc'` | Low | |
| `big_sepS_filter_acc` | `BigSepS.filter_acc` | Low | BiAffine |
| `big_sepS_list_to_set` | `BigSepS.list_to_set` | High | NoDup |
| `big_sepS_sep` | `BigSepS.sep'` | High | |
| `big_sepS_sep_2` | `BigSepS.sep_2` | High | |
| `big_sepS_and` | `BigSepS.and'` | Medium | |
| `big_sepS_pure_1` | `BigSepS.pure_1` | Medium | |
| `big_sepS_affinely_pure_2` | `BigSepS.affinely_pure_2` | Medium | |
| `big_sepS_pure` | `BigSepS.pure` | Medium | BiAffine |
| `big_sepS_persistently` | `BigSepS.persistently` | Medium | BiAffine |
| `big_sepS_intro` | `BigSepS.intro` | High | |
| `big_sepS_forall` | `BigSepS.forall'` | Medium | BiAffine + Persistent |
| `big_sepS_impl` | `BigSepS.impl` | High | |
| `big_sepS_wand` | `BigSepS.wand` | High | |
| `big_sepS_elem_of_acc_impl` | `BigSepS.elem_of_acc_impl` | Medium | |
| `big_sepS_dup` | `BigSepS.dup` | Medium | Requires Affine |
| `big_sepS_later` | `BigSepS.later` | Medium | BiAffine |
| `big_sepS_later_2` | `BigSepS.later_2` | Medium | |
| `big_sepS_laterN` | `BigSepS.laterN` | Medium | BiAffine |
| `big_sepS_laterN_2` | `BigSepS.laterN_2` | Medium | |
| `big_sepM_dom` | `BigSepM.dom` | High | Map ↔ Set |
| `big_sepM_gset_to_gmap` | `BigSepM.set_to_map` | Medium | |

---

## Section 9: Big Separating Conjunction over Multisets (`big_sepMS`)

### Porting Status: **Not Started**

### Design Decision: Abstract Multiset Interface

The Lean port should use an **abstract finite multiset interface** (tentatively `FiniteMultiset A`). Unlike sets, multisets track element multiplicity.

| Operation | Rocq (gmultiset) | Lean Interface | Description |
|-----------|------------------|----------------|-------------|
| `x ∈ X` | `x ∈ X` | `x ∈ X` | Membership (multiplicity ≥ 1) |
| `∅` | `∅` | `∅` | Empty multiset |
| `{[+ x +]}` | `{[+ x +]}` | `{+x+}` | Singleton |
| `X ⊎ Y` | `X ⊎ Y` | `X ⊎ Y` | Disjoint union (sum multiplicities) |
| `X ∖ Y` | `X ∖ Y` | `X \ Y` | Difference |
| `Y ⊆ X` | `Y ⊆ X` | `Y ⊆ X` | Submultiset |

### Correspondence Table

| Rocq Lemma | Lean Theorem | Priority | Notes |
|------------|--------------|----------|-------|
| `big_sepMS_mono` | `BigSepMS.mono` | High | |
| `big_sepMS_ne` | `BigSepMS.ne` | Medium | |
| `big_sepMS_proper` | `BigSepMS.proper` | High | |
| `big_sepMS_mono'` | `BigSepMS.mono'` (instance) | Medium | |
| `big_sepMS_flip_mono'` | `BigSepMS.flip_mono'` (instance) | Low | |
| `big_sepMS_empty_persistent` | `BigSepMS.empty_persistent` (instance) | Medium | |
| `big_sepMS_persistent` | `BigSepMS.persistent` | Medium | |
| `big_sepMS_persistent'` | `BigSepMS.persistent` (instance) | Medium | |
| `big_sepMS_empty_affine` | `BigSepMS.empty_affine` (instance) | Medium | |
| `big_sepMS_affine` | `BigSepMS.affine` | Medium | |
| `big_sepMS_affine'` | `BigSepMS.affine` (instance) | Medium | |
| `big_sepMS_empty_timeless` | - | Low | |
| `big_sepMS_timeless` | - | Low | |
| `big_sepMS_timeless'` | - | Low | |
| `big_sepMS_subseteq` | `BigSepMS.subseteq` | Medium | Requires Affine |
| `big_sepMS_empty` | `BigSepMS.empty` | High | `@[simp]` |
| `big_sepMS_empty'` | `BigSepMS.empty'` | Medium | |
| `big_sepMS_disj_union` | `BigSepMS.disj_union` | High | Key lemma |
| `big_sepMS_delete` | `BigSepMS.delete` | High | |
| `big_sepMS_elem_of` | `BigSepMS.elem_of` | High | Uses TCOr |
| `big_sepMS_elem_of_acc` | `BigSepMS.elem_of_acc` | High | |
| `big_sepMS_singleton` | `BigSepMS.singleton` | High | |
| `big_sepMS_insert` | `BigSepMS.insert` | High | Via disj_union |
| `big_sepMS_sep` | `BigSepMS.sep'` | High | |
| `big_sepMS_sep_2` | `BigSepMS.sep_2` | High | |
| `big_sepMS_and` | `BigSepMS.and'` | Medium | |
| `big_sepMS_later` | `BigSepMS.later` | Medium | BiAffine |
| `big_sepMS_later_2` | `BigSepMS.later_2` | Medium | |
| `big_sepMS_laterN` | `BigSepMS.laterN` | Medium | BiAffine |
| `big_sepMS_laterN_2` | `BigSepMS.laterN_2` | Medium | |
| `big_sepMS_pure_1` | `BigSepMS.pure_1` | Medium | |
| `big_sepMS_affinely_pure_2` | `BigSepMS.affinely_pure_2` | Medium | |
| `big_sepMS_pure` | `BigSepMS.pure` | Medium | BiAffine |
| `big_sepMS_persistently` | `BigSepMS.persistently` | Medium | BiAffine |
| `big_sepMS_intro` | `BigSepMS.intro` | High | |
| `big_sepMS_forall` | `BigSepMS.forall'` | Medium | BiAffine + Persistent |
| `big_sepMS_impl` | `BigSepMS.impl` | High | |
| `big_sepMS_wand` | `BigSepMS.wand` | High | |
| `big_sepMS_dup` | `BigSepMS.dup` | Medium | |
| `big_sepMS_elem_of_acc_impl` | `BigSepMS.elem_of_acc_impl` | Medium | |

---

## Section 10: Commuting Lemmas

### Porting Status: **Not Started**

These lemmas allow swapping the order of nested big operations.

| Rocq Lemma | Lean Theorem | Priority | Notes |
|------------|--------------|----------|-------|
| `big_sepL_sepL` | `BigSepL.sepL` | High | List × List |
| `big_sepL_sepM` | `BigSepL.sepM` | Medium | List × Map |
| `big_sepL_sepS` | `BigSepL.sepS` | Medium | List × Set |
| `big_sepL_sepMS` | `BigSepL.sepMS` | Low | List × Multiset |
| `big_sepM_sepL` | `BigSepM.sepL` | Medium | Map × List |
| `big_sepM_sepM` | `BigSepM.sepM` | Medium | Map × Map |
| `big_sepM_sepS` | `BigSepM.sepS` | Medium | Map × Set |
| `big_sepM_sepMS` | `BigSepM.sepMS` | Low | Map × Multiset |
| `big_sepS_sepL` | `BigSepS.sepL` | Medium | Set × List |
| `big_sepS_sepM` | `BigSepS.sepM` | Medium | Set × Map |
| `big_sepS_sepS` | `BigSepS.sepS` | Medium | Set × Set |
| `big_sepS_sepMS` | `BigSepS.sepMS` | Low | Set × Multiset |
| `big_sepMS_sepL` | `BigSepMS.sepL` | Low | Multiset × List |
| `big_sepMS_sepM` | `BigSepMS.sepM` | Low | Multiset × Map |
| `big_sepMS_sepS` | `BigSepMS.sepS` | Low | Multiset × Set |
| `big_sepMS_sepMS` | `BigSepMS.sepMS` | Low | Multiset × Multiset |

---

## Porting Roadmap

### Phase 1: Abstract Interfaces (Prerequisites)
1. ✅ **DONE** - Define `FiniteMap M K V` typeclass in `Iris/Std/FiniteMap.lean` with required operations and laws
2. Define `FiniteSet A` typeclass in Std
3. Define `FiniteMultiset A` typeclass in Std
4. Provide instances for Std.HashMap, Std.HashSet, etc.

### Phase 2: Core Definitions
1. Define `bigSepM`, `bigAndM` using the abstract map interface
2. Define `bigSepM2` for two maps
3. Define `bigSepS` using the abstract set interface
4. Define `bigSepMS` using the abstract multiset interface
5. Add notations

### Phase 3: High-Priority Lemmas
Port all "High" priority lemmas from each section:
- Empty, singleton, insert, delete
- Lookup, lookup_acc
- Union (for disjoint)
- Mono, proper, sep

### Phase 4: Medium-Priority Lemmas
- Typeclass instances (Persistent, Affine)
- Pure, persistently
- Intro, impl, wand
- Later variants

### Phase 5: Low-Priority and Commuting
- Override lemmas
- fn_insert variants
- All commuting lemmas

---

## Estimated Lemma Counts

| Section | Rocq Lemmas | Priority High | Priority Medium | Priority Low |
|---------|-------------|---------------|-----------------|--------------|
| big_sepM | ~45 | ~20 | ~18 | ~7 |
| big_andM | ~30 | ~12 | ~12 | ~6 |
| big_sepM2 | ~55 | ~22 | ~25 | ~8 |
| big_sepS | ~42 | ~18 | ~18 | ~6 |
| big_sepMS | ~32 | ~14 | ~14 | ~4 |
| Commuting | ~16 | ~2 | ~8 | ~6 |
| **Total** | **~220** | **~88** | **~95** | **~37** |

---

## Key Differences Between Rocq and Lean Ports

### 1. Naming Conventions

| Rocq | Lean | Example |
|------|------|---------|
| `big_sepL_*` | `BigSepL.*` | `big_sepL_nil` -> `BigSepL.nil` |
| `big_andL_*` | `BigAndL.*` | `big_andL_cons` -> `BigAndL.cons` |
| `big_orL_*` | `BigOrL.*` | `big_orL_mono` -> `BigOrL.mono` |
| `big_sepL2_*` | `BigSepL2.*` | `big_sepL2_alt` -> `BigSepL2.alt` |

### 2. Type Differences

| Rocq | Lean |
|------|------|
| `l !! i` (lookup) | `l[i]?` |
| `<[i:=x]>l` (insert) | `l.set i x` |
| `S n` (successor) | `n + 1` |
| `seq n len` | `List.range' n len` |
| `seqZ n len` | Not available (Z not ported) |
| `omap` | `filterMap` |
| `l ≫= f` (bind) | `l.flatMap f` |

### 3. Typeclass Handling

- Rocq uses `TCOr` for disjunctive typeclass constraints
- Lean splits into separate lemmas

### 4. BigSepL2 App/Snoc Alignment

The `BigSepL2.app` and `BigSepL2.snoc` lemmas now align with Rocq:

| Rocq | Lean | Notes |
|------|------|-------|
| `big_sepL2_app` | `BigSepL2.app'` | Identical |
| `big_sepL2_app_same_length` | `BigSepL2.app` | Identical |
| `big_sepL2_snoc` | `BigSepL2.snoc` | Identical |

### 5. Pending Infrastructure

- **Timeless instances**: Require `sep_timeless` infrastructure
- **Z-indexed variants**: Integer indexing not ported
- **Absorbing typeclass**: Some lemmas not ported

---

## Summary Statistics

| Section | Rocq Lemmas | Lean Theorems | Coverage |
|---------|-------------|---------------|----------|
| big_sepL | ~50 | ~52 | ~100% |
| big_sepL2 | ~55 | ~62 | ~100% |
| big_andL | ~30 | ~32 | ~100% |
| big_orL | ~32 | ~34 | ~100% |
| big_sepM | ~55 | ~53 | ~95% |
| big_andM | ~30 | ~35 | ~90% |
| **Total (Lists)** | **~167** | **~180** | **~100%** |
| **Total (Maps)** | **~85** | **~88** | **~93%** |

Remaining not ported: big_sepM2 (~55), big_sepS (~42), big_sepMS (~32), commuting (~16).

---

## See Also

- [translation_differences.md](translation_differences.md) - Tracks remaining differences and design decisions between the Rocq and Lean implementations
