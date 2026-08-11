/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
module

public import Iris.HeapLang.DerivedLaws
public import Iris.HeapLang.ProofMode

/-! # Array utilities

* `arrayFree`, to deallocate an entire array in one go.
* `arrayCopyTo`, a function which copies to an array in-place.
* Using `arrayCopyTo` we also implement `arrayClone`, which allocates a fresh array and copies
  to it.
* `arrayInit`, to create and initialize an array with a given function. Specifically,
  `arrayInit n f` creates a new array of size `n` in which the `i`th element is initialized
  with `f #i`.

Iris-Lean has no total weakest precondition yet, so only the partial (`wp_`) versions of the
specifications are ported. -/

namespace Iris.HeapLang

open BI Iris ProgramLogic

@[expose] public section

@[rocq_alias heap_lang.array_free]
def arrayFree : Val := hl_val%
  rec freeN ptr n :=
    if n ≤ #(0 : Int) then #()
    else (free(ptr); freeN (ptr +ₗ #(1 : Int)) (n - #(1 : Int)))

@[rocq_alias heap_lang.array_copy_to]
def arrayCopyTo : Val := hl_val%
  rec copyTo dst src n :=
    if n ≤ #(0 : Int) then #()
    else (dst ← !src; copyTo (dst +ₗ #(1 : Int)) (src +ₗ #(1 : Int)) (n - #(1 : Int)))

@[rocq_alias heap_lang.array_clone]
def arrayClone : Val := hl_val%
  λ src n,
    let dst := allocn(n, #());
    &arrayCopyTo dst src n;
    dst

/-- `arrayInitLoop src i n f` initializes elements `i`, `i+1`, …, `n` of the array `src` to
`f #i`, `f #(i+1)`, …, `f #n`. -/
@[rocq_alias heap_lang.array_init_loop]
def arrayInitLoop : Val := hl_val%
  rec loop src i n f :=
    if i = n then #()
    else (src +ₗ i ← f i; loop src (i + #(1 : Int)) n f)

@[rocq_alias heap_lang.array_init]
def arrayInit : Val := hl_val%
  λ n f,
    let src := allocn(n, #());
    &arrayInitLoop src #(0 : Int) n f;
    src

section Proof

variable {GF : BundledGFunctors} {hlc : HasLC} [HeapLangGS hlc GF]

@[rocq_alias heap_lang.wp_array_free]
theorem wp_array_free (s : Stuckness) (E : CoPset) (l : Loc) (vs : List Val) (n : Int)
    (hn : n = vs.length) :
    {{ (l ↦∗ vs : IProp GF) }} hl(&arrayFree #l #n) @ s; E {{ RET hl_val(#()); True }} := by
  subst hn
  induction vs generalizing l with
  | nil =>
    iintro %Φ Hl HΦ
    wp_rec
    wp_pures
    rw [decide_eq_true (show ((([] : List Val).length : Int) ≤ 0) by simp)]
    wp_pures
    iapply HΦ
    itrivial
  | cons w vs ih =>
    iintro %Φ Hl HΦ
    icases array_cons.1 $$ Hl with ⟨Hw, Hl⟩
    wp_rec
    wp_pures
    rw [decide_eq_false (show ¬ (((w :: vs).length : Int) ≤ 0) by simp)]
    wp_free
    wp_pures
    rw [show (((w :: vs).length : Int) - 1) = (vs.length : Int) by simp]
    iapply ih $$ Hl HΦ

@[rocq_alias heap_lang.wp_array_copy_to]
theorem wp_array_copy_to (s : Stuckness) (E : CoPset) (dst src : Loc) (vdst vsrc : List Val)
    (dq : DFrac) (n : Int) (hdst : (vdst.length : Int) = n) (hsrc : (vsrc.length : Int) = n) :
    {{ (dst ↦∗ vdst ∗ src ↦∗{dq} vsrc : IProp GF) }} hl(&arrayCopyTo #dst #src #n) @ s; E
    {{ RET hl_val(#()); dst ↦∗ vsrc ∗ src ↦∗{dq} vsrc }} := by
  subst hdst
  revert hsrc
  induction vdst generalizing dst src vsrc with
  | nil =>
    cases vsrc with
    | cons v2 vsrc =>
      exact fun hsrc => absurd hsrc (by simp; omega)
    | nil =>
      intro _
      iintro %Φ ⟨Hdst, Hsrc⟩ HΦ
      wp_rec
      wp_pures
      rw [decide_eq_true (show ((([] : List Val).length : Int) ≤ 0) by simp)]
      wp_pures
      iapply HΦ
      iframe
  | cons v1 vdst ih =>
    cases vsrc with
    | nil =>
      exact fun hsrc => absurd hsrc (by simp; omega)
    | cons v2 vsrc =>
      intro hsrc
      iintro %Φ ⟨Hdst, Hsrc⟩ HΦ
      icases array_cons.1 $$ Hdst with ⟨Hv1, Hdst⟩
      icases array_cons.1 $$ Hsrc with ⟨Hv2, Hsrc⟩
      wp_rec
      wp_pures
      rw [decide_eq_false (show ¬ (((v1 :: vdst).length : Int) ≤ 0) by simp)]
      wp_load
      wp_store
      wp_pures
      rw [show (((v1 :: vdst).length : Int) - 1) = (vdst.length : Int) by simp]
      iapply ih (dst + (1 : Int)) (src + (1 : Int)) vsrc (by simp at hsrc; omega) $$
        %Φ [$Hdst $Hsrc] [Hv1 Hv2 HΦ]
      iintro !> ⟨Hdst, Hsrc⟩
      iapply HΦ
      iframe

@[rocq_alias heap_lang.wp_array_clone]
theorem wp_array_clone (s : Stuckness) (E : CoPset) (l : Loc) (dq : DFrac) (vl : List Val)
    (n : Int) (hvl : (vl.length : Int) = n) (hn : 0 < n) :
    {{ (l ↦∗{dq} vl : IProp GF) }} hl(&arrayClone #l #n) @ s; E
    {{ l', RET hl_val(#l'); l' ↦∗ vl ∗ l ↦∗{dq} vl }} := by
  iintro %Φ Hvl HΦ
  wp_lam
  wp_allocN dst with Hdst
  wp_pures
  wp_bind &arrayCopyTo _ _ _
  iapply wp_array_copy_to s E dst l (List.replicate n.toNat hl_val(#())) vl dq n
    (by simp only [List.length_replicate]; omega) hvl $$ [$Hdst $Hvl]
  iintro !> ⟨Hdst, Hl⟩
  wp_pures
  iapply HΦ
  iframe

section ArrayInit

variable (Q : Nat → Val → IProp GF)

@[rocq_alias heap_lang.wp_array_init_loop]
theorem wp_array_init_loop (s : Stuckness) (E : CoPset) (l : Loc) (i k : Nat) (n : Int)
    (f : Val) (hn : n = Int.ofNat (i + k)) :
    {{ (l + Int.ofNat i) ↦∗ List.replicate k hl_val(#()) ∗
        [∗list] j ∈ List.range' i k, WP hl(&f #(Int.ofNat j)) @ s; E {{ Q j }} }}
      hl(&arrayInitLoop #l #(Int.ofNat i) #n &f) @ s; E
    {{ vs, RET hl_val(#()); ⌜vs.length = k⌝ ∗ (l + Int.ofNat i) ↦∗ vs ∗
        [∗list] j ↦ v ∈ vs, Q (i + j) v }} := by
  subst hn
  induction k generalizing i with
  | zero =>
    iintro %Φ ⟨Hl, Hf⟩ HΦ
    wp_rec
    wp_pures
    simp only [Nat.add_zero, beq_self_eq_true]
    wp_pures
    imodintro
    iapply HΦ $$ %([] : List Val)
    isimp only [array_nil.to_eq, BigSepL.bigSepL_nil.to_eq]
    itrivial
  | succ k ih =>
    iintro %Φ ⟨Hl, Hf⟩ HΦ
    wp_rec
    wp_pures
    rw [show (hl_val(#(Int.ofNat i)) == hl_val(#(Int.ofNat (i + (k + 1))))) = false by
      simp; omega]
    wp_pures
    ieval (simp only [List.replicate_succ]) at Hl
    ieval (simp only [List.range'_succ]) at Hf
    icases array_cons.1 $$ Hl with ⟨Hl, HSl⟩
    icases BigSepL.bigSepL_cons.1 $$ Hf with ⟨Hf, HSf⟩
    wp_bind &f _
    iapply wp_wand $$ Hf
    iintro %v Hv
    wp_store
    wp_pures
    rw [show Int.ofNat i + 1 = Int.ofNat (i + 1) from rfl,
      show Int.ofNat (i + (k + 1)) = Int.ofNat (i + 1 + k) by congr 1; omega]
    iapply ih (i + 1) $$ %Φ [HSl HSf] [Hl Hv HΦ]
    · rw [show l + Int.ofNat (i + 1) = l + Int.ofNat i + (1 : Int) from
        (loc_add_assoc l (Int.ofNat i) 1).symm]
      iframe
    · iintro !> %vs ⟨%hlen, HSl, Hvs⟩
      iapply HΦ $$ %(v :: vs)
      rw [show l + Int.ofNat (i + 1) = l + Int.ofNat i + (1 : Int) from
        (loc_add_assoc l (Int.ofNat i) 1).symm]
      ieval (simp only [show ∀ j, i + 1 + j = i + (j + 1) from fun j => by omega]) at Hvs
      iframe Hl HSl
      isplitl []
      · ipureintro
        simp [hlen]
      · iapply BigSepL.bigSepL_cons.2
        iframe

@[rocq_alias heap_lang.wp_array_init]
theorem wp_array_init (s : Stuckness) (E : CoPset) (n : Int) (f : Val) (hn : 0 < n) :
    {{ [∗list] i ∈ List.range n.toNat, WP hl(&f #(Int.ofNat i)) @ s; E {{ Q i }} }}
      hl(&arrayInit #n &f) @ s; E
    {{ l vs, RET hl_val(#l); ⌜(vs.length : Int) = n⌝ ∗ l ↦∗ vs ∗
        [∗list] k ↦ v ∈ vs, Q k v }} := by
  iintro %Φ Hf HΦ
  wp_lam
  wp_allocN src with Hl
  wp_pures
  wp_bind &arrayInitLoop _ _ _ _
  iapply wp_array_init_loop Q s E src 0 n.toNat n f (by simp; omega) $$ [Hl Hf]
  · rw [show src + Int.ofNat 0 = src from loc_add_zero src, List.range_eq_range']
    iframe
  · iintro !> %vs ⟨%hlen, Hl, Hvs⟩
    wp_pures
    imodintro
    iapply HΦ $$ %src %vs
    rw [show src + Int.ofNat 0 = src from loc_add_zero src]
    ieval (simp only [Nat.zero_add]) at Hvs
    isplitl []
    · ipureintro
      omega
    · iframe Hl Hvs

end ArrayInit

section ArrayInitFmap

variable {α : Type _} (g : α → Val) (Q : Nat → α → IProp GF)

@[rocq_alias heap_lang.wp_array_init_fmap]
theorem wp_array_init_fmap (s : Stuckness) (E : CoPset) (n : Int) (f : Val) (hn : 0 < n) :
    {{ [∗list] i ∈ List.range n.toNat,
        WP hl(&f #(Int.ofNat i)) @ s; E {{ v, ∃ x, ⌜v = g x⌝ ∗ Q i x }} }}
      hl(&arrayInit #n &f) @ s; E
    {{ l xs, RET hl_val(#l); ⌜(xs.length : Int) = n⌝ ∗ l ↦∗ xs.map g ∗
        [∗list] k ↦ x ∈ xs, Q k x }} := by
  iintro %Φ Hf HΦ
  iapply wp_array_init (fun i v => iprop(∃ x, ⌜v = g x⌝ ∗ Q i x)) s E n f hn $$ Hf
  iintro !> %l %vs ⟨%hlen, Hl, Hvs⟩
  icases BigSepL.bigSepL_exists_eq $$ Hvs with ⟨%xs, %heq, Hxs⟩
  subst heq
  iapply HΦ $$ %l %xs
  isplitl []
  · ipureintro
    simpa using hlen
  · iframe Hl Hxs

end ArrayInitFmap

end Proof

end
end Iris.HeapLang
