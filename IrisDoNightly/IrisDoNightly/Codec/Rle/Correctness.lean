module

public import IrisDoNightly.Codec.Rle.Code
public import IrisDoNightly.Codec.Rle.Model
import Std.Tactic.Do
import Std.Internal.Do

/-! # The `rle` (run-length) codec — correctness proofs -/

set_option mvcgen.warning false

open Lean.Order Std.Internal.Do
open Iris.HeapLang

namespace Iris.HeapLang.Ax

open HeapLangAxioms

variable {wp} [HeapLangAxioms wp]

theorem hlRleAux_spec (l : List Int) : ∀ c k : Int,
    True ⊑ wp⟦hl(v(&hlRleAux) v(&(byteVal c)) v(&(byteVal k)) v(&(vList l)))⟧
      (fun v => v = vList (rleEncAux c k l)) := by
  induction l with
  | nil =>
    intro c k
    simp only [hlRleAux]
    hl_beta; hl_beta; hl_beta
    vcgen
    refine Or.inl ⟨_, rfl, ?_⟩
    hl_beta
    vcgen
    simp [rleEncAux, vList, byteVal]
  | cons x xs ih =>
    intro c k
    simp only [hlRleAux]
    hl_beta; hl_beta; hl_beta
    vcgen
    refine Or.inr ⟨_, rfl, ?_⟩
    hl_beta
    hl_projlet                             -- `let x := fst p`
    hl_projlet                             -- `let xs := snd p`
    vcgen
    simp only [byteVal, BinOp.eval, Val.compareSafe, Val.isUnboxed, BaseLit.isUnboxed,
      Bool.or_true, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨_, rfl, ?_⟩
    by_cases hx : x = c
    · -- run continues: bump the count and recurse
      subst hx
      simp only [beq_self_eq_true, ite_true]
      hl_binop                             -- `let k' := k + 1`
      refine wp_mono ?_ (ih x (k + 1) trivial)
      intro v hv
      subst hv
      simp [rleEncAux]
    · -- run ends: emit `k, x`, start a new run at the next byte
      have hb : (hl_val(#x) == hl_val(#c)) = false := by simp [hx]
      rw [hb]
      simp only [Bool.false_eq_true, ite_false]
      refine spec_injR ?_
      refine spec_pair ?_
      refine spec_injR ?_
      refine spec_pair ?_
      refine wp_mono ?_ (ih x 1 trivial)
      intro v hv
      subst hv
      refine spec_val ?_
      refine spec_val ?_
      simp [rleEncAux, ite_eq_right hx, vList, byteVal]

public theorem hlRleEnc_spec (l : List Int) :
    True ⊑ wp⟦hl(v(&hlRleEnc) v(&(vList l)))⟧
      (fun v => v = vList (rleEnc l)) := by
  cases l with
  | nil =>
    simp only [hlRleEnc]
    hl_beta
    vcgen
    refine Or.inl ⟨_, rfl, ?_⟩
    hl_beta
    vcgen
    simp [rleEnc, vList]
  | cons c cs =>
    simp only [hlRleEnc]
    hl_beta
    vcgen
    refine Or.inr ⟨_, rfl, ?_⟩
    hl_beta
    hl_projlet
    hl_projlet
    refine wp_mono ?_ (hlRleAux_spec cs c 1 trivial)
    intro v hv
    subst hv
    simp [rleEnc]

theorem hlReplicateApp_spec (n : Nat) : ∀ (c : Int) (tail : List Int),
    True ⊑ wp⟦hl(v(&hlReplicateApp) v(&(byteVal n)) v(&(byteVal c)) v(&(vList tail)))⟧
      (fun v => v = vList (replicateApp n c tail)) := by
  induction n with
  | zero =>
    intro c tail
    simp only [hlReplicateApp]
    hl_beta; hl_beta; hl_beta
    vcgen
    simp only [byteVal, BinOp.eval, Val.compareSafe, Val.isUnboxed, BaseLit.isUnboxed,
      Bool.or_true, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨_, rfl, ?_⟩
    simp only [beq_self_eq_true, ite_true]
    vcgen
    simp [replicateApp]
  | succ n ih =>
    intro c tail
    simp only [hlReplicateApp]
    hl_beta; hl_beta; hl_beta
    vcgen
    simp only [byteVal, BinOp.eval, Val.compareSafe, Val.isUnboxed, BaseLit.isUnboxed,
      Bool.or_true, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨_, rfl, ?_⟩
    have hb : (Val.lit (BaseLit.int ((n : Int) + 1)) == Val.lit (BaseLit.int 0)) = false := by
      simp [show ((n : Int) + 1) ≠ 0 from by omega]
    rw [hb]
    simp only [Bool.false_eq_true, ite_false]
    hl_binop
    refine spec_injR ?_
    refine spec_pair ?_
    refine wp_mono ?_ (ih c tail trivial)
    intro v hv
    subst hv
    refine spec_val ?_
    simp [replicateApp, vList, byteVal]

private theorem replicateApp_cons (n : Nat) (c : Int) (xs : List Int) :
    replicateApp n c (c :: xs) = replicateApp (n + 1) c xs := by
  induction n <;> grind [replicateApp]

public theorem rleDec_rleEncAux (cs : List Int) : ∀ (c k : Int), 1 ≤ k →
    rleDec (rleEncAux c k cs) = replicateApp k.toNat c cs := by
  induction cs with
  | nil => intro c k _; simp [rleEncAux, rleDec]
  | cons x xs ih =>
    intro c k hk
    by_cases hx : x = c
    · subst hx
      have h1 : rleEncAux x k (x :: xs) = rleEncAux x (k + 1) xs := by simp [rleEncAux]
      rw [h1, ih x (k + 1) (by omega), replicateApp_cons, show (k + 1).toNat = k.toNat + 1 from by omega]
    · simp only [rleEncAux, ite_eq_right hx, rleDec]
      rw [ih x 1 (by omega)]
      simp [replicateApp, show (1 : Int).toNat = 1 from rfl]

public theorem rleDec_rleEnc (l : List Int) : rleDec (rleEnc l) = l := by
  cases l with
  | nil => rfl
  | cons c cs =>
    simp only [rleEnc]
    rw [rleDec_rleEncAux cs c 1 (by omega)]
    simp [replicateApp, show (1 : Int).toNat = 1 from rfl]

public theorem hlRleDec_spec : ∀ (l : List Int), GoodCounts l →
    True ⊑ wp⟦hl(v(&hlRleDec) v(&(vList l)))⟧
      (fun v => v = vList (rleDec l)) := by
  intro l
  induction l using rleDec.induct with
  | case1 =>
    intro _
    simp only [hlRleDec]
    hl_beta
    vcgen
    refine Or.inl ⟨_, rfl, ?_⟩
    hl_beta
    vcgen
    simp [rleDec, vList]
  | case2 k =>
    intro _
    simp only [hlRleDec]
    hl_beta
    vcgen
    refine Or.inr ⟨_, rfl, ?_⟩
    hl_beta
    hl_projlet
    hl_projlet
    vcgen
    refine Or.inl ⟨_, rfl, ?_⟩
    hl_beta
    vcgen
    simp [rleDec, vList]
  | case3 k c rest ih =>
    intro hwf
    obtain ⟨hk, hrest⟩ := hwf
    simp only [hlRleDec]
    hl_beta
    vcgen
    refine Or.inr ⟨_, rfl, ?_⟩
    hl_beta
    hl_projlet                             -- `let k := fst p`
    hl_projlet                             -- `let rest1 := snd p`
    vcgen
    refine Or.inr ⟨_, rfl, ?_⟩
    hl_beta
    hl_projlet                             -- `let c := fst q`
    hl_projlet                             -- `let rest := snd q`
    -- `hlReplicateApp k c (go rest)`: run the recursion (IH), then the replicate helper
    refine spec_bind (ECtxItem.appR hl(v(&hlReplicateApp) v(&(byteVal k)) v(&(byteVal c)))) ?_
    refine wp_mono ?_ (ih hrest trivial)
    intro v hv
    subst hv
    rw [show byteVal k = byteVal (k.toNat : Int) from by rw [Int.toNat_of_nonneg hk]]
    refine wp_mono ?_ (hlReplicateApp_spec k.toNat c (rleDec rest) trivial)
    intro v hv
    subst hv
    simp [rleDec]

public theorem GoodCounts_rleEncAux (cs : List Int) : ∀ (c k : Int), 0 ≤ k →
    GoodCounts (rleEncAux c k cs) := by
  induction cs with
  | nil => intro c k hk; exact ⟨hk, trivial⟩
  | cons x xs ih => intro c k hk; by_cases hx : x = c <;> grind [rleEncAux, GoodCounts]

public theorem GoodCounts_rleEnc (l : List Int) : GoodCounts (rleEnc l) := by
  cases l with
  | nil => trivial
  | cons c cs => simp only [rleEnc]; exact GoodCounts_rleEncAux cs c 1 (by omega)

theorem rle_roundtrip (l : List Int) :
    True ⊑ wp⟦hl(v(&hlRleDec) (v(&hlRleEnc) v(&(vList l))))⟧
      (fun v => v = vList l) := by
  refine PartialOrder.rel_trans ?_ (spec_bind (ECtxItem.appR hl(v(&hlRleDec))))
  refine PartialOrder.rel_trans (hlRleEnc_spec l) (wp_mono ?_)
  intro v hv
  subst hv
  refine wp_mono ?_ (hlRleDec_spec (rleEnc l) (GoodCounts_rleEnc l) trivial)
  intro v hv
  subst hv
  rw [rleDec_rleEnc]

end Iris.HeapLang.Ax
