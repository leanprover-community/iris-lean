module

public import IrisDoNightly.Codec.Lzss.Code
public import IrisDoNightly.Codec.Lzss.Model
import Std.Tactic.Do
import Std.Internal.Do

/-! # The `lzss` codec — correctness proofs

The verified core is the decoder: on any well-formed (`WF`) token stream the HeapLang decoder computes
exactly the pure model `lzssDecode`.  The hash-chain compressor is an untrusted oracle whose only
round-trip obligation is to emit a `WF` token stream; it need not find the optimal parse. -/

set_option mvcgen.warning false

open Lean.Order Std.Internal.Do
open Iris.HeapLang

namespace Iris.HeapLang.Ax

open HeapLangAxioms

variable {wp} [HeapLangAxioms wp]

/-- **Overlap = run-length.**  A back-copy at offset 1 replicates the last byte — the identity that
ties `lzss`'s self-referential copy to `rle`'s `replicate`.  This is the reusable core lemma. -/
private theorem copyBack_offset_one (b : Int) :
    ∀ (k : Nat) (acc : List Int),
      copyBack 1 k (acc ++ [b]) = acc ++ b :: List.replicate k b := by
  intro k; induction k <;> grind [copyBack]

/-- **Trivial round-trip.**  The degenerate all-literals encoder round-trips: the base case every
`Factors`-valid parse specialises — the hash-chain oracle only ever *improves* the ratio. -/
private theorem lzssDecode_lit (l : List Int) : lzssDecode [Tok.lit l] = l := by
  grind [lzssDecode, lzssDecodeAux]

/-- A literal `[b]` followed by `copy 1 n` decodes to `b` repeated `n+1` times — `lzss` expressing an
`rle` run, verified through the shared overlap lemma. -/
private theorem lzssDecode_run (b : Int) (n : Nat) :
    lzssDecode [Tok.lit [b], Tok.copy 1 n] = b :: List.replicate n b := by
  grind [lzssDecode, lzssDecodeAux, copyBack_offset_one]

theorem hlLength_spec (t : List Int) :
    True ⊑ wp⟦hl(v(&hlLength) v(&(vList t)))⟧
      (fun v => v = byteVal (t.length : Int)) := by
  induction t with
  | nil =>
    intro
    simp only [hlLength]
    hl_beta
    vcgen
    refine Or.inl ⟨_, rfl, ?_⟩
    hl_beta
    vcgen
    grind [byteVal]
  | cons x xs ih =>
    intro
    simp only [hlLength]
    hl_beta
    vcgen
    refine Or.inr ⟨_, rfl, ?_⟩
    hl_beta
    hl_projlet                             -- `let xs := snd p`
    hl_call ih                             -- `let n := go xs`
    refine spec_binop ?_
    refine spec_val ?_
    refine spec_val ?_
    simp only [byteVal, BinOp.eval, Option.some.injEq, exists_eq_left']

theorem hlSnoc_spec (t : List Int) : ∀ b : Int,
    True ⊑ wp⟦hl(v(&hlSnoc) v(&(vList t)) v(&(byteVal b)))⟧
      (fun v => v = vList (t ++ [b])) := by
  induction t with
  | nil =>
    intro b
    simp only [hlSnoc]
    hl_beta; hl_beta
    vcgen
    refine Or.inl ⟨_, rfl, ?_⟩
    hl_beta
    refine spec_injR ?_
    refine spec_pair ?_
    refine spec_injL ?_                    -- `injl(#())` (right pair element)
    refine spec_val ?_
    refine spec_val ?_
    grind [byteVal]
  | cons x xs ih =>
    intro b
    simp only [hlSnoc]
    hl_beta; hl_beta
    vcgen
    refine Or.inr ⟨_, rfl, ?_⟩
    hl_beta
    hl_projlet                             -- `let x := fst p`
    hl_projlet                             -- `let xs := snd p`
    hl_call (ih b)                         -- `let xs' := go xs b`
    refine spec_injR ?_
    refine spec_pair ?_
    refine spec_val ?_
    refine spec_val ?_
    grind [byteVal]

/-- Bridge between the two indexing conventions: `hlNth`'s model `nthD` (an `Int` index, returning
`0` off the end) agrees with `List.getD` at the corresponding `Nat` index. -/
private theorem nthD_eq_getD (xs : List Int) : ∀ r : Int, 0 ≤ r → nthD xs r = xs.getD r.toNat 0 := by
  induction xs with
  | nil => intro r _; simp [nthD]
  | cons x xs ih =>
    intro r hr
    by_cases hr0 : r = 0
    · subst hr0; simp [nthD]
    · have h1 : r.toNat = (r - 1).toNat + 1 := by omega
      have := ih (r - 1) (by omega)
      grind [nthD, List.getD_cons_succ]

/-- **The random-access crux, verified heap-free.**  `hlCopyBack` computes exactly `copyBack` on the
`Val`-threaded buffer, provided the back-reference stays in range (`off ≤ acc.length`, the `Factors`
well-formedness the oracle must maintain). -/
theorem hlCopyBack_spec (k : Nat) : ∀ (off : Nat) (acc : List Int), off ≤ acc.length →
    True ⊑ wp⟦hl(v(&hlCopyBack) v(&(byteVal k)) v(&(byteVal off)) v(&(vList acc)))⟧
      (fun v => v = vList (copyBack off k acc)) := by
  induction k with
  | zero =>
    intro off acc _
    simp only [hlCopyBack]
    hl_beta; hl_beta; hl_beta
    vcgen
    simp only [byteVal, BinOp.eval, Val.compareSafe, Val.isUnboxed, BaseLit.isUnboxed,
      Bool.or_true, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨_, rfl, ?_⟩
    simp only [beq_self_eq_true, ite_true]
    vcgen
    grind [copyBack]
  | succ k ih =>
    intro off acc hpre
    simp only [hlCopyBack]
    hl_beta; hl_beta; hl_beta
    vcgen
    simp only [byteVal, BinOp.eval, Val.compareSafe, Val.isUnboxed, BaseLit.isUnboxed,
      Bool.or_true, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨_, rfl, ?_⟩
    have hb : (Val.lit (BaseLit.int ((k : Int) + 1)) == Val.lit (BaseLit.int 0)) = false := by
      simp [show ((k : Int) + 1) ≠ 0 from by omega]
    rw [hb]
    simp only [Bool.false_eq_true, ite_false]
    hl_call (hlLength_spec acc)            -- `let n := hlLength acc`
    hl_binop                               -- `let idx := n - off`
    hl_call (hlNth_spec acc ((acc.length : Int) - (off : Int)))   -- `let b := hlNth acc idx`
    hl_call (hlSnoc_spec acc (nthD acc ((acc.length : Int) - (off : Int))))  -- `let acc' := hlSnoc acc b`
    hl_binop                               -- `let k' := k - 1`
    refine wp_mono ?_ (ih off (acc ++ [nthD acc ((acc.length : Int) - (off : Int))]) (by simp; omega) trivial)
    intro v hv
    subst hv
    -- close: `copyBack off k (acc ++ [nthD …]) = copyBack off (k+1) acc`
    have hr : nthD acc ((acc.length : Int) - (off : Int)) = acc.getD (acc.length - off) 0 := by
      rw [nthD_eq_getD acc _ (by omega)]
      congr 1
      omega
    rw [hr]
    rfl

theorem hlAppend_spec (xs : List Int) : ∀ ys : List Int,
    True ⊑ wp⟦hl(v(&hlAppend) v(&(vList xs)) v(&(vList ys)))⟧
      (fun v => v = vList (xs ++ ys)) := by
  induction xs with
  | nil =>
    intro ys
    simp only [hlAppend]
    hl_beta; hl_beta
    vcgen
    refine Or.inl ⟨_, rfl, ?_⟩
    hl_beta
    vcgen
  | cons x xs ih =>
    intro ys
    simp only [hlAppend]
    hl_beta; hl_beta
    vcgen
    refine Or.inr ⟨_, rfl, ?_⟩
    hl_beta
    hl_projlet                             -- `let x := fst p`
    hl_projlet                             -- `let xs' := snd p`
    hl_call (ih ys)                        -- `let r := go xs' ys`
    refine spec_injR ?_
    refine spec_pair ?_
    refine spec_val ?_
    refine spec_val ?_
    grind [byteVal]

theorem hlLzssDecodeAux_spec (ts : List Tok) : ∀ acc : List Int, WF ts acc →
    True ⊑ wp⟦hl(v(&hlLzssDecodeAux) v(&(tokList ts)) v(&(vList acc)))⟧
      (fun v => v = vList (lzssDecodeAux ts acc)) := by
  induction ts with
  | nil =>
    intro acc _
    simp only [hlLzssDecodeAux, tokList]
    hl_beta; hl_beta
    vcgen
    refine Or.inl ⟨_, rfl, ?_⟩
    hl_beta
    vcgen
    grind [lzssDecodeAux]
  | cons t ts' ih =>
    intro acc hwf
    cases t with
    | lit bs =>
      simp only [hlLzssDecodeAux, tokList, tokVal]
      hl_beta; hl_beta
      vcgen
      refine Or.inr ⟨_, rfl, ?_⟩
      hl_beta
      hl_projlet                           -- `let t := fst p`
      hl_projlet                           -- `let ts' := snd p`
      vcgen                                -- inner `match t`
      refine Or.inl ⟨_, rfl, ?_⟩
      hl_beta
      hl_call (hlAppend_spec acc bs)       -- `let acc1 := hlAppend acc bs`
      refine wp_mono ?_ (ih (acc ++ bs) hwf trivial)
      intro v hv; subst hv
      grind [lzssDecodeAux]
    | copy off len =>
      simp only [hlLzssDecodeAux, tokList, tokVal]
      hl_beta; hl_beta
      vcgen
      refine Or.inr ⟨_, rfl, ?_⟩
      hl_beta
      hl_projlet                           -- `let t := fst p`
      hl_projlet                           -- `let ts' := snd p`
      vcgen                                -- inner `match t`
      refine Or.inr ⟨_, rfl, ?_⟩
      hl_beta
      hl_projlet                           -- `let off := fst q`
      hl_projlet                           -- `let len := snd q`
      obtain ⟨hoff, hwf'⟩ := hwf
      hl_call (hlCopyBack_spec len off acc hoff)   -- `let acc2 := hlCopyBack len off acc`
      refine wp_mono ?_ (ih (copyBack off len acc) hwf' trivial)
      intro v hv; subst hv
      grind [lzssDecodeAux]

/-- **`lzss` decoder verified heap-free.**  On any well-formed token stream, the HeapLang decoder
computes exactly the pure model `lzssDecode`. -/
theorem hlLzssDecode_spec (ts : List Tok) (h : WF ts []) :
    True ⊑ wp⟦hl(v(&hlLzssDecode) v(&(tokList ts)))⟧
      (fun v => v = vList (lzssDecode ts)) := by
  simp only [hlLzssDecode]
  hl_beta
  refine wp_mono ?_ (hlLzssDecodeAux_spec ts [] h trivial)
  intro v hv; subst hv
  rfl

/-- **End-to-end `lzss` round-trip (trivial encoder).**  Decoding the all-literals encoding of any
byte-list returns it unchanged. -/
theorem lzss_trivial_roundtrip (l : List Int) :
    True ⊑ wp⟦hl(v(&hlLzssDecode) v(&(tokList [Tok.lit l])))⟧
      (fun v => v = vList l) := by
  intro _
  refine wp_mono ?_ (hlLzssDecode_spec [Tok.lit l] trivial trivial)
  intro v hv
  rw [hv, lzssDecode_lit]

end Iris.HeapLang.Ax
