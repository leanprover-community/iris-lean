/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iris-Lean Contributors
-/
module

public import IrisMath.Termination.Adequacy
public import IrisMath.Termination.Thunk

/-! # A logical relation for termination

This file ports `theories/examples/termination/logrel.v` of Transfinite Iris: a semantic model of
a linear type system with (synchronous) channels, natural-number iteration and (in the second
part) type polymorphism, in the sequential termination logic. Every well-typed program is
strongly normalizing (`simple_logrel_adequacy`, `logrel_adequacy`).

The token camera is `Auth Unit` (as in the original submission of the Rocq development), not
`Excl Unit`.
-/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false

universe w v u

namespace Iris.Transfinite.Termination.Logrel

open Iris Iris.Std Iris.BI Iris.HeapLang Iris.HeapLang.Transfinite ProgramLogic Language
open Ordinal

/-! ## Code -/

/-- A diverging expression (Rocq: `div`). -/
def div : Exp := hl((rec f x := f x) #())

/-- The empty channel state (Rocq: `EV`). -/
def EV : Val := hl_val(injl(#()))
/-- A channel holding a value (Rocq: `VV`). -/
def VV (v : Val) : Val := hl_val(injr(injl(&v)))
/-- A channel holding a continuation (Rocq: `CV`). -/
def CV (f : Val) : Val := hl_val(injr(injr(&f)))

/-- Rocq: `caseof`. -/
def caseof : Val := hl_val%
  λ e eE eV eC,
    match e with
    | injl(_) => eE #()
    | injr(x) => match x with
      | injl(v) => eV v
      | injr(f) => eC f

/-- Rocq: `letpair`. -/
def letpair : Val := hl_val% λ p f, f (fst(p)) (snd(p))

/-- Rocq: `iter`. -/
def iter : Val := hl_val%
  rec iter s := λ n f, if n = #(0 : Int) then s else iter (f s) (n - #1) f

/-- Rocq: `chan`. -/
def chan : Val := hl_val% λ _, let c := ref(injl(#())); (c, c)

/-- Rocq: `put`. -/
def put : Val := hl_val%
  λ p, let c := fst(p); let v := snd(p);
    &caseof (!c) (λ _, c ← injr(injl(v))) (λ _, &div) (λ f, (c ← injl(#()); f v))

/-- Rocq: `get`. -/
def get : Val := hl_val%
  λ p, let c := fst(p); let f := snd(p);
    &caseof (!c) (λ _, c ← injr(injr(f))) (λ v, (c ← injl(#()); f v)) (λ _, &div)

/-! ## Tokens -/

variable {SI : Type v} [instSI : Iris.SIdx SI]
local stepindex SI

variable {GF : BundledGFunctors.{u}}

section Tokens

variable [Etok : ElemG GF (constOFU.{max u v} (Auth Unit))]

/-- An exclusive token (Rocq: `tok`). -/
def tok (γ : GName) : IProp GF := iOwn (E := Etok) γ (ULift.up (● ()))

/-- Rocq: `tok_alloc`. -/
theorem tok_alloc : ⊢ |==> ∃ γ, tok (GF := GF) γ := by
  unfold tok
  exact iOwn_alloc (E := Etok) _ (Auth.auth_valid.mpr trivial)

/-- Rocq: `tok_unique`. -/
theorem tok_unique (γ : GName) : tok (GF := GF) γ ∗ tok γ ⊢ False := by
  unfold tok
  iintro ⟨H1, H2⟩
  ihave H := (iOwn_op (E := Etok) (γ := γ) (a1 := ULift.up (● ()))
    (a2 := ULift.up (● ()))).mpr $$ [H1 H2]
  · iframe
  ihave ⟨Hv, -⟩ := iOwn_valid_l $$ H
  icases internalCmraValid_discrete.mp $$ Hv with %Hv
  exact (Auth.auth_op_valid.mp Hv).elim

instance tok_timeless (γ : GName) : Timeless (tok (GF := GF) γ) := by
  unfold tok; infer_instance

end Tokens

/-! ## Execution lemmas -/

variable [Hheap : HeapLangTGS GF] [Htc : TcGS.{w} GF]

/-- The time-credit weakest precondition for heap_lang. -/
abbrev twp (e : Exp) (Φ : Val → IProp GF) : IProp GF :=
  tcwp (ι := heapRefIrisGS) (G := Htc) .NotStuck ⊤ e Φ

/-- Rocq: `rwp_put_empty`. -/
theorem rwp_put_empty (l : Loc) (v : Val) :
    l ↦ some EV ⊢ twp.{w} hl(v(&put) v((#l, &v)))
      fun w => iprop(⌜w = hl_val(#())⌝ ∗ l ↦ some (VV v)) := by
  iintro Hl
  unfold put caseof EV VV
  twp_pures
  twp_apply rwp_load $$ Hl
  iintro Hl
  twp_pures
  twp_apply rwp_store $$ Hl
  iintro Hl
  iframe
  ipureintro; rfl

/-- Rocq: `rwp_put_cont`. -/
theorem rwp_put_cont (l : Loc) (f v : Val) (Φ : Val → IProp GF) :
    l ↦ some (CV f) ∗ twp.{w} hl(v(&f) v(&v)) Φ ⊢ twp.{w} hl(v(&put) v((#l, &v)))
      fun w => iprop(Φ w ∗ l ↦ some EV) := by
  iintro ⟨Hl, Hwp⟩
  unfold put caseof EV CV
  twp_pures
  twp_apply rwp_load $$ Hl
  iintro Hl
  twp_pures
  twp_apply rwp_store $$ Hl
  iintro Hl
  twp_pures
  iapply rwp_wand $$ Hwp
  iintro %w Hw
  iframe

/-- Rocq: `rwp_get_empty`. -/
theorem rwp_get_empty (l : Loc) (f : Val) :
    l ↦ some EV ⊢ twp.{w} hl(v(&get) v((#l, &f)))
      fun w => iprop(⌜w = hl_val(#())⌝ ∗ l ↦ some (CV f)) := by
  iintro Hl
  unfold get caseof EV CV
  twp_pures
  twp_apply rwp_load $$ Hl
  iintro Hl
  twp_pures
  twp_apply rwp_store $$ Hl
  iintro Hl
  iframe
  ipureintro; rfl

/-- Rocq: `rwp_get_val`. -/
theorem rwp_get_val (l : Loc) (f v : Val) (Φ : Val → IProp GF) :
    l ↦ some (VV v) ∗ twp.{w} hl(v(&f) v(&v)) Φ ⊢ twp.{w} hl(v(&get) v((#l, &f)))
      fun w => iprop(Φ w ∗ l ↦ some EV) := by
  iintro ⟨Hl, Hwp⟩
  unfold get caseof EV VV
  twp_pures
  twp_apply rwp_load $$ Hl
  iintro Hl
  twp_pures
  twp_apply rwp_store $$ Hl
  iintro Hl
  twp_pures
  iapply rwp_wand $$ Hwp
  iintro %w Hw
  iframe

/-- Rocq: `rwp_chan`. -/
theorem rwp_chan :
    ⊢ twp.{w} (GF := GF) hl(v(&chan) #())
      fun v => iprop(∃ l : Loc, ⌜v = hl_val((#l, #l))⌝ ∗ l ↦ some EV) := by
  unfold chan EV
  twp_pures
  twp_apply rwp_alloc
  iintro %l Hl
  twp_pures
  iexists l
  iframe
  ipureintro; rfl

/-! ## Semantic types and closed lemmas -/

section Closed

variable [Hseq : SeqG GF]

/-- The sequential weakest precondition at the full mask (Rocq: `SEQ e [{ v, Φ v }]`). -/
abbrev seqT (e : Exp) (Φ : Val → IProp GF) : IProp GF := tseq.{w} ⊤ e Φ

/-- Semantic types (Rocq: `ltype`). -/
abbrev ltype (GF : BundledGFunctors) := Val → IProp GF

/-- Rocq: `lunit`. -/
def lunit : ltype GF := fun v => iprop(⌜v = hl_val(#())⌝)
/-- Rocq: `lbool`. -/
def lbool : ltype GF := fun v => iprop(∃ b : Bool, ⌜v = hl_val(#b)⌝)
/-- Rocq: `lnat`. -/
def lnat : ltype GF := fun v => iprop(∃ n : Nat, ⌜v = hl_val(#(n : Int))⌝)
/-- Rocq: `ltensor`. -/
def ltensor (A B : ltype GF) : ltype GF := fun v => iprop(∃ v₁ v₂,
  ⌜v = hl_val((&v₁, &v₂))⌝ ∗ A v₁ ∗ B v₂)
/-- Rocq: `larr`. -/
def larr (A B : ltype GF) : ltype GF := fun f => iprop(∀ v, A v -∗ seqT.{w} hl(v(&f) v(&v)) B)

/-- Rocq: `closed_unit_intro`. -/
theorem closed_unit_intro : ⊢ seqT.{w} (GF := GF) hl(#()) lunit := by
  iapply seq_value
  unfold lunit
  ipureintro; rfl

/-- Rocq: `closed_unit_elim`. -/
theorem closed_unit_elim (e₁ e₂ : Exp) (Φ : Val → IProp GF) :
    seqT.{w} e₁ lunit ∗ seqT.{w} e₂ Φ ⊢ seqT.{w} hl(&e₁; &e₂) Φ := by
  unfold seqT tseq seq lunit
  iintro ⟨He, He₂⟩ Hna
  twp_bind (&e₁)
  ihave H := He $$ Hna
  twp_apply rwp_wand $$ H
  iintro %v ⟨Hna, %rfl⟩
  twp_pures
  iapply He₂ $$ Hna

/-- Rocq: `closed_bool_intro`. -/
theorem closed_bool_intro (b : Bool) : ⊢ seqT.{w} (GF := GF) hl(#b) lbool := by
  iapply seq_value
  unfold lbool
  iexists b
  ipureintro; rfl

/-- Rocq: `closed_bool_elim`. -/
theorem closed_bool_elim (e e₁ e₂ : Exp) (A : ltype GF) (P : IProp GF) :
    seqT.{w} e lbool ∗ (P -∗ seqT.{w} e₁ A) ∗ (P -∗ seqT.{w} e₂ A) ∗ P ⊢
      seqT.{w} hl(if &e then &e₁ else &e₂) A := by
  unfold seqT tseq seq lbool
  iintro ⟨He, H₁, H₂, HP⟩ Hna
  twp_bind (&e)
  ihave H := He $$ Hna
  twp_apply rwp_wand $$ H
  iintro %v ⟨Hna, %b, %rfl⟩
  cases b
  · twp_pures
    iapply H₂ $$ HP Hna
  · twp_pures
    iapply H₁ $$ HP Hna

/-- Rocq: `closed_nat_intro`. -/
theorem closed_nat_intro (n : Nat) : ⊢ seqT.{w} (GF := GF) hl(#(n : Int)) lnat := by
  iapply seq_value
  unfold lnat
  iexists n
  ipureintro; rfl

/-- Rocq: `closed_nat_add`. -/
theorem closed_nat_add (e₁ e₂ : Exp) :
    seqT.{w} (GF := GF) e₁ lnat ∗ seqT.{w} e₂ lnat ⊢ seqT.{w} hl(&e₁ + &e₂) lnat := by
  unfold seqT tseq seq lnat
  iintro ⟨H₁, H₂⟩ Hna
  twp_bind (&e₂)
  ihave H := H₂ $$ Hna
  twp_apply rwp_wand $$ H
  iintro %v₂ ⟨Hna, %n₂, %rfl⟩
  twp_bind (&e₁)
  ihave H := H₁ $$ Hna
  twp_apply rwp_wand $$ H
  iintro %v₁ ⟨Hna, %n₁, %rfl⟩
  twp_pures
  iframe
  iexists n₁ + n₂
  ipureintro
  push_cast
  rfl

/-- `n` copies of `α` under the natural sum (Rocq: `natmul`). -/
def natmul : Nat → Ordinal.{w} → Ordinal.{w}
  | 0, _ => 0
  | n + 1, α => α ♯ natmul n α

/-- The supremum of the `natmul n α` (Rocq: `omul`). -/
def omul (α : Ordinal.{w}) : Ordinal.{w} := ⨆ n : Nat, natmul n α

theorem natmul_le_omul (n : Nat) (α : Ordinal.{w}) : natmul n α ≤ omul α :=
  le_ciSup (Ordinal.bddAbove_range _) n

/-- Rocq: `closed_nat_iter_n`. -/
theorem closed_nat_iter_n (n : Nat) (s : Exp) (f : Val) (α : Ordinal.{w}) (A : ltype GF) :
    seqT.{w} s A ∗ □ (tc (GF := GF) α -∗ ∀ v, A v -∗ seqT.{w} hl(v(&f) v(&v)) A) ∗
      tc (GF := GF) (natmul n α) ⊢ seqT.{w} hl(v(&iter) &s #(n : Int) v(&f)) A := by
  iintro ⟨H₁, #H₂, Hc⟩
  unfold seqT tseq seq
  iintro Hna
  iinduction n generalizing %s H₁ Hc Hna with
  | zero =>
    twp_bind (&s)
    ihave H := H₁ $$ Hna
    twp_apply rwp_wand $$ H
    iintro %v ⟨Hna, Hv⟩
    unfold iter
    twp_pures
    rw [show (hl_val(#((0 : Nat) : Int)) == hl_val(#(0 : Int))) = true by simp]
    twp_pures
    iframe
  | succ n ih =>
    rw [natmul]
    icases (tc_split α (natmul n α)).mp $$ Hc with ⟨Hα, Hc⟩
    twp_bind (&s)
    ihave H := H₁ $$ Hna
    twp_apply rwp_wand $$ H
    iintro %v ⟨Hna, Hv⟩
    unfold iter
    twp_pures
    rw [show (hl_val(#((n + 1 : Nat) : Int)) == hl_val(#(0 : Int))) = false by simp; omega]
    twp_pures
    rw [show ((n + 1 : Nat) : Int) - 1 = (n : Int) by omega]
    iapply ih $$ %(hl(v(&f) v(&v))) [Hα Hv] Hc Hna
    ihave H := H₂ $$ Hα %v Hv
    iexact H

/-- Rocq: `closed_nat_iter`. -/
theorem closed_nat_iter (e₁ e₂ : Exp) (f : Val) (α : Ordinal.{w}) (A : ltype GF) :
    seqT.{w} e₁ lnat ∗ seqT.{w} e₂ A ∗
      □ (tc (GF := GF) α -∗ ∀ v, A v -∗ seqT.{w} hl(v(&f) v(&v)) A) ∗ tc (GF := GF) (omul α) ⊢
      seqT.{w} hl(v(&iter) &e₂ &e₁ v(&f)) A := by
  iintro ⟨H₁, H₂, #H₃, Hc⟩
  unfold seqT tseq seq lnat
  iintro Hna
  twp_bind (&e₁)
  ihave H := H₁ $$ Hna
  twp_apply rwp_wand $$ H
  iintro %v ⟨Hna, %n, %rfl⟩
  iapply tc_weaken (β := natmul n α) rfl (natmul_le_omul n α)
  iframe Hc
  iintro Hα
  ihave H := closed_nat_iter_n n e₂ f α A $$ [H₂ Hα]
  · unfold seqT tseq seq
    iframe
    iexact H₃
  unfold seqT tseq seq
  iapply H $$ Hna

/-- Rocq: `closed_fun_intro`. -/
theorem closed_fun_intro (x : String) (e : Exp) (A B : ltype GF) :
    (∀ v, A v -∗ seqT.{w} (e.subst (.named x) v) B) ⊢
      seqT.{w} (Exp.rec_ .anon (.named x) e) (larr.{w} A B) := by
  unfold larr seqT tseq seq
  iintro H Hna
  twp_pures
  iframe
  iintro %v Hv Hna
  twp_pures
  iapply H $$ Hv Hna

/-- Rocq: `closed_fun_elim`. -/
theorem closed_fun_elim (e₁ e₂ : Exp) (A B : ltype GF) :
    seqT.{w} e₁ (larr.{w} A B) ∗ seqT.{w} e₂ A ⊢ seqT.{w} hl(&e₁ &e₂) B := by
  unfold larr seqT tseq seq
  iintro ⟨H₁, H₂⟩ Hna
  twp_bind (&e₂)
  ihave H := H₂ $$ Hna
  twp_apply rwp_wand $$ H
  iintro %v ⟨Hna, HA⟩
  twp_bind (&e₁)
  ihave H := H₁ $$ Hna
  twp_apply rwp_wand $$ H
  iintro %f ⟨Hna, HAB⟩
  iapply HAB $$ HA Hna

/-- Rocq: `closed_tensor_intro`. -/
theorem closed_tensor_intro (e₁ e₂ : Exp) (A B : ltype GF) :
    seqT.{w} e₁ A ∗ seqT.{w} e₂ B ⊢ seqT.{w} hl((&e₁, &e₂)) (ltensor A B) := by
  unfold seqT tseq seq ltensor
  iintro ⟨H₁, H₂⟩ Hna
  twp_bind (&e₂)
  ihave H := H₂ $$ Hna
  twp_apply rwp_wand $$ H
  iintro %v₂ ⟨Hna, HB⟩
  twp_bind (&e₁)
  ihave H := H₁ $$ Hna
  twp_apply rwp_wand $$ H
  iintro %v₁ ⟨Hna, HA⟩
  twp_pures
  iframe Hna
  iexists v₁, v₂
  iframe HA HB
  ipureintro; rfl

/-- `let: (x, y) := e₁ in e₂` (Rocq notation). -/
def letPair (x y : String) (e₁ e₂ : Exp) : Exp :=
  hl(v(&letpair) &e₁ &(Exp.rec_ .anon (.named x) (Exp.rec_ .anon (.named y) e₂)))

/-- Rocq: `closed_tensor_elim`. -/
theorem closed_tensor_elim (x y : String) (e₁ e₂ : Exp) (A B C : ltype GF) (hxy : x ≠ y) :
    seqT.{w} e₁ (ltensor A B) ∗
      (∀ v₁ v₂, A v₁ -∗ B v₂ -∗ seqT.{w} ((e₂.subst (.named x) v₁).subst (.named y) v₂) C) ⊢
      seqT.{w} (letPair x y e₁ e₂) C := by
  unfold seqT tseq seq ltensor letPair
  iintro ⟨H₁, H₂⟩ Hna
  twp_pures
  twp_bind (&e₁)
  ihave H := H₁ $$ Hna
  twp_apply rwp_wand $$ H
  iintro %p ⟨Hna, %v₁, %v₂, %rfl, Hv₁, Hv₂⟩
  unfold letpair
  twp_pures
  rw [Exp.subst_rec_ne (.inr rfl) (.inl (by simpa using hxy))]
  twp_pures
  iapply H₂ $$ Hv₁ Hv₂ Hna

section Channels

variable [Etok : ElemG GF (constOFU.{max u v} (Auth Unit))]

/-- The channel invariant (Rocq: `ch_inv`). -/
def chInv (γget γput : GName) (l : Loc) (A : Val → IProp GF) : IProp GF :=
  iprop(l ↦ some EV ∨ (∃ v, l ↦ some (VV v) ∗ tok γput ∗ A v) ∨
    (∃ f, l ↦ some (CV f) ∗ tok γget ∗
      ∀ v, A v -∗ seqT.{w} hl(v(&f) v(&v)) fun v => iprop(⌜v = hl_val(#())⌝)))

/-- The namespace of the channel invariants (Rocq: `lN`). -/
def lN : Namespace := nroot.@"type"

/-- Rocq: `lget`. -/
def lget (A : ltype GF) : ltype GF := fun v => iprop(∃ (l : Loc) (γget γput : GName),
  ⌜v = hl_val(#l)⌝ ∗ tok γget ∗ NonAtomicInvariant.inv Hseq.name (lN.@l) (chInv.{w} γget γput l A) ∗
    tc (GF := GF) (1 : Ordinal.{w}))
/-- Rocq: `lput`. -/
def lput (A : ltype GF) : ltype GF := fun v => iprop(∃ (l : Loc) (γget γput : GName),
  ⌜v = hl_val(#l)⌝ ∗ tok γput ∗ NonAtomicInvariant.inv Hseq.name (lN.@l) (chInv.{w} γget γput l A) ∗
    tc (GF := GF) (1 : Ordinal.{w}))
theorem nclose_subset_top' (N : Namespace) : (↑N : CoPset) ⊆ ⊤ := fun _ _ => CoPset.mem_full

/-- Rocq: `closed_get`. -/
theorem closed_get (e₁ e₂ : Exp) (A : ltype GF) :
    seqT.{w} e₁ (lget.{w} A) ∗ seqT.{w} e₂ (larr.{w} A lunit) ⊢
      seqT.{w} hl(v(&get) (&e₁, &e₂)) lunit := by
  unfold lget larr lunit chInv EV VV CV seqT tseq seq
  iintro ⟨H₁, H₂⟩ Hna
  twp_bind (&e₂)
  ihave H := H₂ $$ Hna
  twp_apply rwp_wand $$ H
  iintro %f ⟨Hna, Hf⟩
  twp_bind (&e₁)
  ihave H := H₁ $$ Hna
  twp_apply rwp_wand $$ H
  iintro %p ⟨Hna, %l, %γget, %γput, %rfl, Hget, #I, Hone⟩
  imod NonAtomicInvariant.inv_acc_open (nclose_subset_top' _) (nclose_subset_top' _) $$ I Hna
    with P
  iapply tcwp_burn_credit rfl $$ Hone
  inext
  twp_pure
  icases P with ⟨HI, Hna, Hclose⟩
  icases HI with (HI | ⟨%v, Hl, Hput, Hv⟩ | ⟨%f', Hl, Hget', -⟩)
  · ihave H := rwp_get_empty l f $$ [HI]
    · unfold EV
      iexact HI
    unfold CV
    iapply rwp_strong_mono (Std.IsPreorder.le_refl _) LawfulSet.subset_refl $$ H
    iintro %w ⟨%rfl, Hl⟩
    imod Hclose $$ [Hf Hl Hget Hna] with Hna
    · iframe Hna
      inext
      iright
      iright
      iexists f
      iframe
    imodintro
    iframe Hna
    ipureintro; rfl
  · ihave Hf := Hf $$ %v Hv
    unfold get caseof
    twp_pures
    twp_apply rwp_load $$ Hl
    iintro Hl
    twp_pures
    twp_apply rwp_store $$ Hl
    iintro Hl
    iapply fupd_rwp
    imod Hclose $$ [Hl Hna] with Hna
    · iframe Hna
      inext
      ileft
      iexact Hl
    imodintro
    twp_pures
    iapply Hf $$ Hna
  · iexfalso
    iapply tok_unique $$ [Hget Hget']
    iframe

/-- Rocq: `closed_put`. -/
theorem closed_put (e₁ e₂ : Exp) (A : ltype GF) :
    seqT.{w} e₁ (lput.{w} A) ∗ seqT.{w} e₂ A ⊢ seqT.{w} hl(v(&put) (&e₁, &e₂)) lunit := by
  unfold lput lunit chInv EV VV CV seqT tseq seq
  iintro ⟨H₁, H₂⟩ Hna
  twp_bind (&e₂)
  ihave H := H₂ $$ Hna
  twp_apply rwp_wand $$ H
  iintro %v ⟨Hna, Hv⟩
  twp_bind (&e₁)
  ihave H := H₁ $$ Hna
  twp_apply rwp_wand $$ H
  iintro %p ⟨Hna, %l, %γget, %γput, %rfl, Hput, #I, Hone⟩
  imod NonAtomicInvariant.inv_acc_open (nclose_subset_top' _) (nclose_subset_top' _) $$ I Hna
    with P
  iapply tcwp_burn_credit rfl $$ Hone
  inext
  twp_pure
  icases P with ⟨HI, Hna, Hclose⟩
  icases HI with (HI | ⟨%v', Hl, Hput', -⟩ | ⟨%f, Hl, Hget, Hf⟩)
  · ihave H := rwp_put_empty l v $$ [HI]
    · unfold EV
      iexact HI
    unfold VV
    iapply rwp_strong_mono (Std.IsPreorder.le_refl _) LawfulSet.subset_refl $$ H
    iintro %w ⟨%rfl, Hl⟩
    imod Hclose $$ [Hv Hl Hput Hna] with Hna
    · iframe Hna
      inext
      iright
      ileft
      iexists v
      iframe
    imodintro
    iframe Hna
    ipureintro; rfl
  · iexfalso
    iapply tok_unique $$ [Hput Hput']
    iframe
  · ihave Hf := Hf $$ %v Hv
    unfold put caseof
    twp_pures
    twp_apply rwp_load $$ Hl
    iintro Hl
    twp_pures
    twp_apply rwp_store $$ Hl
    iintro Hl
    iapply fupd_rwp
    imod Hclose $$ [Hl Hna] with Hna
    · iframe Hna
      inext
      ileft
      iexact Hl
    imodintro
    twp_pures
    iapply Hf $$ Hna

/-- Rocq: `closed_chan`. -/
theorem closed_chan (A : ltype GF) :
    tc (GF := GF) 1 ∗ tc (GF := GF) 1 ⊢
      seqT.{w} hl(v(&chan) #()) (ltensor (lget.{w} A) (lput.{w} A)) := by
  unfold seqT tseq seq ltensor lget lput
  iintro ⟨Hone, Hone'⟩ Hna
  ihave H := rwp_chan (GF := GF) (Htc := Htc)
  iapply rwp_strong_mono (Std.IsPreorder.le_refl _) LawfulSet.subset_refl $$ H
  iintro %v ⟨%l, %rfl, Hl⟩
  imod tok_alloc (GF := GF) with ⟨%γget, Hget⟩
  imod tok_alloc (GF := GF) with ⟨%γput, Hput⟩
  ihave HI : ▷ chInv.{w} γget γput l A $$ [Hl]
  · inext
    unfold chInv
    ileft
    iexact Hl
  imod NonAtomicInvariant.inv_alloc (p := Hseq.name) (N := lN.@l) $$ HI with #I
  imodintro
  iframe Hna
  iexists hl_val(#l), hl_val(#l)
  isplitr
  · ipureintro; rfl
  isplitl [Hget Hone]
  · iexists l, γget, γput
    iframe Hget Hone
    isplitr
    · ipureintro; rfl
    iexact I
  · iexists l, γget, γput
    iframe Hput Hone'
    isplitr
    · ipureintro; rfl
    iexact I

end Channels

end Closed

/-! ## The simple logical relation -/

section Simple

open PartialMap BigSepM

variable [Hseq : SeqG GF] [Etok : ElemG GF (constOFU.{max u v} (Auth Unit))]

/-- Typing contexts. -/
abbrev Ctx (GF : BundledGFunctors) := VarMapF (ltype GF)
/-- Substitutions. -/
abbrev Subst := VarMapF Val

/-- Rocq: `env_ltyped`. -/
def envLtyped (Γ : Ctx GF) (θ : Subst) : IProp GF :=
  iprop([∗map] x ↦ A ∈ Γ, ∃ v, ⌜get? θ x = some v⌝ ∗ A v)

/-- The semantic typing judgment (Rocq: `ltyped`, notation `Γ ⊨ e : A`). -/
def ltyped (Γ : Ctx GF) (e : Exp) (A : ltype GF) : Prop :=
  ⊢ ∃ α : Ordinal.{w}, tc (GF := GF) α -∗ ∀ θ : Subst, envLtyped Γ θ -∗
    seqT.{w} (e.substMap θ) A

@[simp] theorem substMap_ofVal (θ : Subst) (v : Val) :
    (ToVal.ofVal v : Exp).substMap θ = ToVal.ofVal v := rfl

/-- Rocq: `env_ltyped_split`. -/
theorem env_ltyped_split {Γ Δ : Ctx GF} {θ : Subst} (h : Γ ##ₘ Δ) :
    envLtyped (PartialMap.union Γ Δ) θ ⊢ envLtyped Γ θ ∗ envLtyped Δ θ := by
  unfold envLtyped
  exact (bigSepM_union (PROP := IProp GF) h).1

/-- Rocq: `env_ltyped_empty`. -/
theorem env_ltyped_empty (θ : Subst) : ⊢ envLtyped (GF := GF) ∅ θ := by
  unfold envLtyped
  exact bigSepM_empty.2

/-- Rocq: `env_ltyped_insert`. -/
theorem env_ltyped_insert (Γ : Ctx GF) (θ : Subst) (A : ltype GF) (v : Val) (x : String) :
    envLtyped Γ θ ∗ A v ⊢ envLtyped (insert Γ x A) (insert θ x v) := by
  unfold envLtyped
  have hmono : ∀ Γ' : Ctx GF, (∀ y B, get? Γ' y = some B → y ≠ x) →
      ([∗map] y ↦ B ∈ Γ', ∃ w, ⌜get? θ y = some w⌝ ∗ B w) ⊢
        [∗map] y ↦ B ∈ Γ', ∃ w, ⌜get? (insert θ x v) y = some w⌝ ∗ B w := fun Γ' hne =>
    bigSepM_mono fun {y B} hy => by
      iintro ⟨%w, %hw, HB⟩
      iexists w
      iframe
      ipureintro
      rw [LawfulPartialMap.get?_insert_ne (hne y B hy).symm]
      exact hw
  cases hx : get? Γ x with
  | none =>
    refine .trans ?_ (bigSepM_insert hx).2
    iintro ⟨HΓ, HA⟩
    isplitl [HA]
    · iexists v
      iframe
      ipureintro
      exact LawfulPartialMap.get?_insert_eq rfl
    · iapply hmono Γ (fun y B hy hyx => by subst hyx; simp_all) $$ HΓ
  | some B =>
    rw [← LawfulPartialMap.insert_delete (m := Γ)]
    refine .trans ?_ (bigSepM_insert (LawfulPartialMap.get?_delete_eq rfl)).2
    iintro ⟨HΓ, HA⟩
    icases (bigSepM_delete hx).1 $$ HΓ with ⟨-, HΓ⟩
    isplitl [HA]
    · iexists v
      iframe
      ipureintro
      exact LawfulPartialMap.get?_insert_eq rfl
    · iapply hmono (delete Γ x) (fun y B hy hyx => by
        subst hyx; simp [LawfulPartialMap.get?_delete_eq] at hy) $$ HΓ

/-- Rocq: `env_ltyped_weaken`. -/
theorem env_ltyped_weaken (x : String) (A : ltype GF) (Γ : Ctx GF) (θ : Subst)
    (hx : get? Γ x = none) : envLtyped (insert Γ x A) θ ⊢ envLtyped Γ θ := by
  unfold envLtyped
  refine (bigSepM_insert hx).1.trans sep_elim_right

/-- Rocq: `variable`. -/
theorem variable_rule (x : String) (A : ltype GF) :
    ltyped.{w} (singleton x A) (.var x) A := by
  unfold ltyped envLtyped
  iexists (0 : Ordinal.{w})
  iintro - %θ HΓ
  ihave ⟨%v, %hv, HA⟩ := bigSepM_lookup (LawfulPartialMap.get?_singleton_eq rfl) $$ HΓ
  simp only [Exp.substMap]
  rw [hv]
  iapply seq_value
  iexact HA

/-- Rocq: `weaken`. -/
theorem weaken_rule (x : String) (Γ : Ctx GF) (e : Exp) (A B : ltype GF) (hx : get? Γ x = none)
    (He : ltyped.{w} Γ e B) : ltyped.{w} (insert Γ x A) e B := by
  unfold ltyped at *
  ihave ⟨%α, He⟩ := He
  iexists α
  iintro Hα %θ Hθ
  iapply He $$ Hα %θ
  iapply env_ltyped_weaken x A Γ θ hx $$ Hθ

/-- Rocq: `unit_intro`. -/
theorem unit_intro : ltyped.{w} (GF := GF) ∅ hl(#()) lunit := by
  unfold ltyped
  iexists (0 : Ordinal.{w})
  iintro - %θ -
  simp only [substMap_ofVal]
  iapply closed_unit_intro

/-- Rocq: `unit_elim`. -/
theorem unit_elim (Γ Δ : Ctx GF) (e e' : Exp) (A : ltype GF) (hdis : Γ ##ₘ Δ)
    (He : ltyped.{w} Γ e lunit) (He' : ltyped.{w} Δ e' A) :
    ltyped.{w} (PartialMap.union Γ Δ) hl(&e; &e') A := by
  unfold ltyped at *
  ihave ⟨%α₁, He⟩ := He
  ihave ⟨%α₂, He'⟩ := He'
  iexists α₁ ♯ α₂
  iintro Hc %θ HΓ
  icases (tc_split α₁ α₂).mp $$ Hc with ⟨Hα₁, Hα₂⟩
  icases env_ltyped_split hdis $$ HΓ with ⟨HΓ, HΔ⟩
  ihave H₁ := He $$ Hα₁ %θ HΓ
  ihave H₂ := He' $$ Hα₂ %θ HΔ
  simp only [Exp.substMap, Binder.deleteMap]
  iapply closed_unit_elim
  iframe

/-- Rocq: `bool_intro`. -/
theorem bool_intro (b : Bool) : ltyped.{w} (GF := GF) ∅ hl(#b) lbool := by
  unfold ltyped
  iexists (0 : Ordinal.{w})
  iintro - %θ -
  simp only [substMap_ofVal]
  iapply closed_bool_intro

/-- Rocq: `bool_elim`. -/
theorem bool_elim (Γ Δ : Ctx GF) (e e₁ e₂ : Exp) (A : ltype GF) (hdis : Γ ##ₘ Δ)
    (He : ltyped.{w} Γ e lbool) (H₁ : ltyped.{w} Δ e₁ A) (H₂ : ltyped.{w} Δ e₂ A) :
    ltyped.{w} (PartialMap.union Γ Δ) hl(if &e then &e₁ else &e₂) A := by
  unfold ltyped at *
  ihave ⟨%α, He⟩ := He
  ihave ⟨%α₁, H₁⟩ := H₁
  ihave ⟨%α₂, H₂⟩ := H₂
  iexists α ♯ α₁ ♯ α₂
  iintro Hc %θ HΓ
  icases (tc_split _ α₂).mp $$ Hc with ⟨Hc, Hα₂⟩
  icases (tc_split α α₁).mp $$ Hc with ⟨Hα, Hα₁⟩
  icases env_ltyped_split hdis $$ HΓ with ⟨HΓ, HΔ⟩
  ihave He := He $$ Hα %θ HΓ
  simp only [Exp.substMap]
  iapply closed_bool_elim (P := envLtyped Δ θ)
  iframe He HΔ
  isplitl [H₁ Hα₁]
  · iapply H₁ $$ Hα₁ %θ
  · iapply H₂ $$ Hα₂ %θ

/-- Rocq: `nat_intro`. -/
theorem nat_intro (n : Nat) : ltyped.{w} (GF := GF) ∅ hl(#(n : Int)) lnat := by
  unfold ltyped
  iexists (0 : Ordinal.{w})
  iintro - %θ -
  simp only [substMap_ofVal]
  iapply closed_nat_intro

/-- Rocq: `nat_plus`. -/
theorem nat_plus (e₁ e₂ : Exp) (Γ Δ : Ctx GF) (hdis : Γ ##ₘ Δ)
    (H₁ : ltyped.{w} Γ e₁ lnat) (H₂ : ltyped.{w} Δ e₂ lnat) :
    ltyped.{w} (PartialMap.union Γ Δ) hl(&e₁ + &e₂) lnat := by
  unfold ltyped at *
  ihave ⟨%α₁, H₁⟩ := H₁
  ihave ⟨%α₂, H₂⟩ := H₂
  iexists α₁ ♯ α₂
  iintro Hc %θ HΓ
  icases (tc_split α₁ α₂).mp $$ Hc with ⟨Hα₁, Hα₂⟩
  icases env_ltyped_split hdis $$ HΓ with ⟨HΓ, HΔ⟩
  ihave H₁ := H₁ $$ Hα₁ %θ HΓ
  ihave H₂ := H₂ $$ Hα₂ %θ HΔ
  simp only [Exp.substMap]
  iapply closed_nat_add
  iframe

/-- Rocq: `nat_elim`. -/
theorem nat_elim (e e₀ eS : Exp) (x : String) (A : ltype GF) (Γ Δ : Ctx GF) (hdis : Γ ##ₘ Δ)
    (He : ltyped.{w} Γ e lnat) (H₀ : ltyped.{w} Δ e₀ A)
    (HS : ltyped.{w} (PartialMap.singleton x A) eS A) :
    ltyped.{w} (PartialMap.union Γ Δ)
      hl(v(&iter) &e₀ &e v(&(Val.rec_ .anon (.named x) eS))) A := by
  rw [show PartialMap.singleton x A = PartialMap.insert (∅ : Ctx GF) x A from rfl] at HS
  unfold ltyped at *
  ihave ⟨%αe, He⟩ := He
  ihave ⟨%α₀, H₀⟩ := H₀
  ihave ⟨%αS, #HS⟩ := HS
  iexists αe ♯ α₀ ♯ omul αS
  iintro Hc %θ HΓ
  icases (tc_split _ (omul αS)).mp $$ Hc with ⟨Hc, HαS⟩
  icases (tc_split αe α₀).mp $$ Hc with ⟨Hαe, Hα₀⟩
  icases env_ltyped_split hdis $$ HΓ with ⟨HΓ, HΔ⟩
  ihave He := He $$ Hαe %θ HΓ
  ihave H₀ := H₀ $$ Hα₀ %θ HΔ
  simp only [Exp.substMap, substMap_ofVal]
  iapply closed_nat_iter
  iframe He H₀ HαS
  iintro !> Hα %v Hv
  unfold seqT tseq seq
  iintro Hna
  twp_pures
  ihave H := HS $$ Hα %(PartialMap.insert (∅ : Subst) x v) [Hv]
  · iapply env_ltyped_insert
    iframe
    iapply env_ltyped_empty
  rw [Exp.substMap_insert, LawfulPartialMap.delete_empty, Exp.substMap_empty]
  simp only [Exp.subst]
  iapply H $$ Hna

/-- Rocq: `fun_intro`. -/
theorem fun_intro (Γ : Ctx GF) (x : String) (e : Exp) (A B : ltype GF)
    (He : ltyped.{w} (PartialMap.insert Γ x A) e B) :
    ltyped.{w} Γ (Exp.rec_ .anon (.named x) e) (larr.{w} A B) := by
  unfold ltyped at *
  ihave ⟨%α, He⟩ := He
  iexists α
  iintro Hα %θ HΓ
  simp only [Exp.substMap, Binder.deleteMap]
  iapply closed_fun_intro
  iintro %v Hv
  ihave H := He $$ Hα %(PartialMap.insert θ x v) [HΓ Hv]
  · iapply env_ltyped_insert
    iframe
  rw [Exp.substMap_insert]
  simp only [Exp.subst]
  iexact H

/-- Rocq: `fun_elim`. -/
theorem fun_elim (Γ Δ : Ctx GF) (e₁ e₂ : Exp) (A B : ltype GF) (hdis : Γ ##ₘ Δ)
    (H₁ : ltyped.{w} Γ e₁ (larr.{w} A B)) (H₂ : ltyped.{w} Δ e₂ A) :
    ltyped.{w} (PartialMap.union Γ Δ) hl(&e₁ &e₂) B := by
  unfold ltyped at *
  ihave ⟨%α₁, H₁⟩ := H₁
  ihave ⟨%α₂, H₂⟩ := H₂
  iexists α₁ ♯ α₂
  iintro Hc %θ HΓ
  icases (tc_split α₁ α₂).mp $$ Hc with ⟨Hα₁, Hα₂⟩
  icases env_ltyped_split hdis $$ HΓ with ⟨HΓ, HΔ⟩
  ihave H₁ := H₁ $$ Hα₁ %θ HΓ
  ihave H₂ := H₂ $$ Hα₂ %θ HΔ
  simp only [Exp.substMap]
  iapply closed_fun_elim
  iframe

/-- Rocq: `tensor_intro`. -/
theorem tensor_intro (Γ Δ : Ctx GF) (e₁ e₂ : Exp) (A B : ltype GF) (hdis : Γ ##ₘ Δ)
    (H₁ : ltyped.{w} Γ e₁ A) (H₂ : ltyped.{w} Δ e₂ B) :
    ltyped.{w} (PartialMap.union Γ Δ) hl((&e₁, &e₂)) (ltensor A B) := by
  unfold ltyped at *
  ihave ⟨%α₁, H₁⟩ := H₁
  ihave ⟨%α₂, H₂⟩ := H₂
  iexists α₁ ♯ α₂
  iintro Hc %θ HΓ
  icases (tc_split α₁ α₂).mp $$ Hc with ⟨Hα₁, Hα₂⟩
  icases env_ltyped_split hdis $$ HΓ with ⟨HΓ, HΔ⟩
  ihave H₁ := H₁ $$ Hα₁ %θ HΓ
  ihave H₂ := H₂ $$ Hα₂ %θ HΔ
  simp only [Exp.substMap]
  iapply closed_tensor_intro
  iframe

theorem substMap_letPair (θ : Subst) (x y : String) (e₁ e₂ : Exp) :
    (letPair x y e₁ e₂).substMap θ =
      letPair x y (e₁.substMap θ) (e₂.substMap (delete (delete θ x) y)) := by
  simp [letPair, Exp.substMap, Binder.deleteMap]

/-- Rocq: `tensor_elim`. -/
theorem tensor_elim (Γ Δ : Ctx GF) (x y : String) (e₁ e₂ : Exp) (A B C : ltype GF) (hxy : x ≠ y)
    (hdis : Γ ##ₘ Δ) (H₁ : ltyped.{w} Γ e₁ (ltensor A B))
    (H₂ : ltyped.{w} (PartialMap.insert (PartialMap.insert Δ y B) x A) e₂ C) :
    ltyped.{w} (PartialMap.union Γ Δ) (letPair x y e₁ e₂) C := by
  unfold ltyped at *
  ihave ⟨%α₁, H₁⟩ := H₁
  ihave ⟨%α₂, H₂⟩ := H₂
  iexists α₁ ♯ α₂
  iintro Hc %θ HΓ
  icases (tc_split α₁ α₂).mp $$ Hc with ⟨Hα₁, Hα₂⟩
  icases env_ltyped_split hdis $$ HΓ with ⟨HΓ, HΔ⟩
  ihave H₁ := H₁ $$ Hα₁ %θ HΓ
  rw [substMap_letPair]
  iapply closed_tensor_elim x y _ _ A B C hxy
  iframe H₁
  iintro %v₁ %v₂ Hv₁ Hv₂
  ihave H := H₂ $$ Hα₂
    %(PartialMap.insert (PartialMap.insert θ y v₂) x v₁) [HΔ Hv₁ Hv₂]
  · iapply env_ltyped_insert
    iframe Hv₁
    iapply env_ltyped_insert
    iframe
  rw [show PartialMap.insert (PartialMap.insert θ y v₂) x v₁ =
    (Binder.named x).insertMap v₁ ((Binder.named y).insertMap v₂ θ) from rfl,
    Exp.substMap_insertMap_2]
  simp only [Binder.deleteMap]
  iexact H

/-- Rocq: `chan_alloc`. -/
theorem chan_alloc (A : ltype GF) :
    ltyped.{w} (GF := GF) ∅ hl(v(&chan) #()) (ltensor (lget.{w} A) (lput.{w} A)) := by
  unfold ltyped
  iexists (1 : Ordinal.{w}) ♯ 1
  iintro Hc %θ -
  simp only [Exp.substMap, substMap_ofVal]
  iapply closed_chan
  iapply (tc_split 1 1).mp $$ Hc

/-- Rocq: `chan_get`. -/
theorem chan_get (Γ Δ : Ctx GF) (e₁ e₂ : Exp) (A : ltype GF) (hdis : Γ ##ₘ Δ)
    (H₁ : ltyped.{w} Γ e₁ (lget.{w} A)) (H₂ : ltyped.{w} Δ e₂ (larr.{w} A lunit)) :
    ltyped.{w} (PartialMap.union Γ Δ) hl(v(&get) (&e₁, &e₂)) lunit := by
  unfold ltyped at *
  ihave ⟨%α₁, H₁⟩ := H₁
  ihave ⟨%α₂, H₂⟩ := H₂
  iexists α₁ ♯ α₂
  iintro Hc %θ HΓ
  icases (tc_split α₁ α₂).mp $$ Hc with ⟨Hα₁, Hα₂⟩
  icases env_ltyped_split hdis $$ HΓ with ⟨HΓ, HΔ⟩
  ihave H₁ := H₁ $$ Hα₁ %θ HΓ
  ihave H₂ := H₂ $$ Hα₂ %θ HΔ
  simp only [Exp.substMap, substMap_ofVal]
  iapply closed_get
  iframe

/-- Rocq: `chan_put`. -/
theorem chan_put (Γ Δ : Ctx GF) (e₁ e₂ : Exp) (A : ltype GF) (hdis : Γ ##ₘ Δ)
    (H₁ : ltyped.{w} Γ e₁ (lput.{w} A)) (H₂ : ltyped.{w} Δ e₂ A) :
    ltyped.{w} (PartialMap.union Γ Δ) hl(v(&put) (&e₁, &e₂)) lunit := by
  unfold ltyped at *
  ihave ⟨%α₁, H₁⟩ := H₁
  ihave ⟨%α₂, H₂⟩ := H₂
  iexists α₁ ♯ α₂
  iintro Hc %θ HΓ
  icases (tc_split α₁ α₂).mp $$ Hc with ⟨Hα₁, Hα₂⟩
  icases env_ltyped_split hdis $$ HΓ with ⟨HΓ, HΔ⟩
  ihave H₁ := H₁ $$ Hα₁ %θ HΓ
  ihave H₂ := H₂ $$ Hα₂ %θ HΔ
  simp only [Exp.substMap, substMap_ofVal]
  iapply closed_put
  iframe

end Simple

end Iris.Transfinite.Termination.Logrel
