module

public import IrisDoNightly.Codec.Rle.Code
public import IrisDoNightly.Codec.Rle.Model
public import IrisDoNightly.Codec.Auto
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
    grind [rleEncAux, vList, byteVal]
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
      grind [rleEncAux]
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
      grind [rleEncAux, vList, byteVal]

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
    grind [rleEnc, vList]
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
    grind [rleEnc]

-- === clean CPS helper (vcgen'-driven, `Auto` spec set opened for this section) ===
section
open scoped Iris.HeapLang.Ax.Auto

/-- `hlReplicateApp` (3-arg, `Nat` recursion, `if k=0` guard) — arity-generic `vcgen'` drives all
stepping; the vacuous guard branch is closed by `exfalso; grind`, then `simp_all` — (vcgen-ish) then
(grind-ish). -/
theorem hlReplicateApp_cps (n : Nat) : ∀ (c : Int) (tail : List Int), ∀ Φ : Val → Prop,
    Φ (vList (replicateApp n c tail))
      ⊑ wp⟦hl(v(&hlReplicateApp) v(&(byteVal n)) v(&(byteVal c)) v(&(vList tail)))⟧ Φ := by
  induction n with
  | zero =>
    intro c tail Φ; simp only [hlReplicateApp]
    vcgen' [] <;> (try (exfalso; grind)) <;> (try simp_all [replicateApp, vList, byteVal])
  | succ n ih =>
    intro c tail Φ; simp only [hlReplicateApp]
    vcgen' [ih] <;> (try (exfalso; grind)) <;> (try simp_all [replicateApp, vList, byteVal])

end

/-- Closed `hlReplicateApp` spec — 1-line corollary of the CPS form. -/
theorem hlReplicateApp_spec (n : Nat) : ∀ (c : Int) (tail : List Int),
    True ⊑ wp⟦hl(v(&hlReplicateApp) v(&(byteVal n)) v(&(byteVal c)) v(&(vList tail)))⟧
      (fun v => v = vList (replicateApp n c tail)) :=
  fun c tail _ => hlReplicateApp_cps n c tail _ rfl

private theorem replicateApp_cons (n : Nat) (c : Int) (xs : List Int) :
    replicateApp n c (c :: xs) = replicateApp (n + 1) c xs := by
  induction n <;> grind [replicateApp]

public theorem rleDec_rleEncAux (cs : List Int) : ∀ (c k : Int), 1 ≤ k →
    rleDec (rleEncAux c k cs) = replicateApp k.toNat c cs := by
  induction cs <;> intro c k hk <;>
    grind [rleEncAux, rleDec, replicateApp, replicateApp_cons, Int.toNat_of_nonneg]

public theorem rleDec_rleEnc (l : List Int) : rleDec (rleEnc l) = l := by
  cases l <;> grind [rleEnc, rleDec, replicateApp, rleDec_rleEncAux]

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
    grind [rleDec, vList]
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
    grind [rleDec, vList]
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
    grind [rleDec]

public theorem GoodCounts_rleEncAux (cs : List Int) : ∀ (c k : Int), 0 ≤ k →
    GoodCounts (rleEncAux c k cs) := by
  induction cs with
  | nil => intro c k hk; exact ⟨hk, trivial⟩
  | cons x xs ih => intro c k hk; by_cases hx : x = c <;> grind [rleEncAux, GoodCounts]

public theorem GoodCounts_rleEnc (l : List Int) : GoodCounts (rleEnc l) := by
  cases l <;> grind [rleEnc, GoodCounts, GoodCounts_rleEncAux]

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
