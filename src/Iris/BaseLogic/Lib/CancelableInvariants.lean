/-
Copyright (c) 2026 Sam Hart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Hart
-/
import Iris.Algebra.Excl
import Iris.Algebra.Frac
import Iris.BaseLogic.Lib.Invariants

/-! # Cancelable Invariants

Port of `iris/base_logic/lib/cancelable_invariants.v`.

Cancelable invariants extend standard invariants with a fractional ownership
 token that can permanently cancel the invariant and extract its body.

## Main definitions
- `cinv_own` — fractional token for cancelation
- `cinv` — cancelable invariant

## Main results
- `cinv_alloc`, `cinv_acc`, `cinv_cancel`
- proof mode instances `IntoInv`, `IntoAcc`
-/

namespace Iris.BaseLogic

open _root_.Iris _root_.Iris.Algebra _root_.Iris.Std _root_.Iris.BI

/-- Ghost state carrier for cancelable invariants. -/
abbrev CinvR (F : Type _) : Type _ :=
  Option (Excl (LeibnizO Unit)) × Option (Frac F)

variable {GF : BundledGFunctors} {M : Type _ → Type _} {F : Type _}
variable [UFraction F]
variable [FiniteMap Positive M] [DecidableEq Positive]
variable [FiniteMapLaws Positive M] [HeapFiniteMap Positive M]
variable [ElemG GF (InvF GF M F)]
variable [ElemG GF (COFE.constOF CoPsetDisj)]
variable [ElemG GF (COFE.constOF GSetDisj)]
variable [ElemG GF (COFE.constOF (CinvR F))]

private abbrev maskDiff (E : Iris.Set Positive) (N : Namespace) : Iris.Set Positive :=
  fun x => E x ∧ ¬(nclose N).mem x

/-- Keep IProp entailments opaque for proof mode (avoid unfolding to `holds`). -/
private structure IPropEntails (P Q : IProp GF) : Prop where
  toEntails : P ⊢ Q

private def wrapEntails {P Q : IProp GF} (h : P ⊢ Q) :
    IPropEntails (GF := GF) P Q :=
  ⟨h⟩

local instance asEmpValid_IPropEntails_cinv (d : Iris.ProofMode.AsEmpValid.Direction)
    (P Q : IProp GF) :
    Iris.ProofMode.AsEmpValid d (IPropEntails (GF := GF) P Q) iprop(P -∗ Q) := by
  -- reuse the proof mode instance for entailments
  have hEntails :
      Iris.ProofMode.AsEmpValid d (P ⊢ Q) iprop(P -∗ Q) := by infer_instance
  refine ⟨?_, ?_⟩
  · intro hd h
    exact (hEntails.as_emp_valid.1 hd) h.toEntails
  · intro hd h
    exact ⟨(hEntails.as_emp_valid.2 hd) h⟩

/-! ## Definitions -/

/-- Fractional ownership token for a cancelable invariant.
Coq: `cinv_own` in `cancelable_invariants.v`. -/
noncomputable def cinv_own (_W : WsatGS GF) (γ : GName) (p : F) : IProp GF :=
  -- store the fractional token in the right component
  iOwn (GF := GF) (F := COFE.constOF (CinvR F)) γ (none, some ((p : F) : Frac F))

/-- Internal exclusive token for cancelable invariant proofs.
Coq: `cinv_excl` in `cancelable_invariants.v`. -/
noncomputable def cinv_excl (_W : WsatGS GF) (γ : GName) : IProp GF :=
  -- store the exclusive token in the left component
  iOwn (GF := GF) (F := COFE.constOF (CinvR F)) γ
    (some (Excl.excl (LeibnizO.mk ())), none)

/-- Internal body of a cancelable invariant. -/
private abbrev cinv_body (W : WsatGS GF) (γ : GName) (P : IProp GF) : IProp GF :=
  BIBase.or (BIBase.sep P (cinv_excl (F := F) W γ)) (cinv_own (F := F) W γ (1 : F))

/-- Cancelable invariant.
Coq: `cinv` in `cancelable_invariants.v`. -/
noncomputable def cinv (W : WsatGS GF) (N : Namespace) (γ : GName) (P : IProp GF) : IProp GF :=
  -- invariant body: `P ∗ cinv_excl γ` or the full token
  inv (GF := GF) (M := M) (F := F) W N (cinv_body (F := F) W γ P)

/-! ## Properties -/

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
/-- `cinv` is persistent (inherits from `inv`).
Coq: `cinv_persistent`. -/
theorem cinv_persistent (W : WsatGS GF) (N : Namespace) (γ : GName) (P : IProp GF) :
    Persistent (cinv (M := M) (F := F) W N γ P) := by
  -- reuse persistence of `inv`
  refine ⟨?_⟩
  simpa [cinv, cinv_body] using
    (inv_persistent (GF := GF) (M := M) (F := F) (W := W) (N := N)
      (P := cinv_body (F := F) W γ P))

omit [DecidableEq Positive]
  [ElemG GF (COFE.constOF CoPsetDisj)]
  [ElemG GF (COFE.constOF GSetDisj)] in
/-- Two full ownership tokens are contradictory.
Coq: `cinv_own_1_l`. -/
theorem cinv_own_1_l (W : WsatGS GF) (γ : GName) (q : F) :
    cinv_own (F := F) W γ (1 : F) ⊢
    BIBase.wand (cinv_own (F := F) W γ q) (BIBase.pure False : IProp GF) := by
  -- validity of the combined token contradicts `one_whole`
  refine wand_intro ?_
  refine (iOwn_cmraValid_op (GF := GF) (F := COFE.constOF (CinvR F)) (γ := γ)
    (a1 := (none, some ((1 : F) : Frac F))) (a2 := (none, some ((q : F) : Frac F)))).trans ?_
  refine (UPred.cmraValid_elim
    (a := ((none, some ((1 : F) : Frac F)) : CinvR F) •
      (none, some ((q : F) : Frac F)))).trans ?_
  refine BI.pure_mono ?_
  intro hvalid0
  have hproper : Fraction.Proper ((1 : F) + q) := by
    -- validity reduces to the fractional component
    simpa [CMRA.ValidN, Prod.ValidN, CMRA.op, Prod.op, optionOp] using hvalid0
  exact (UFraction.one_whole (α := F)).2 ⟨q, hproper⟩

omit [DecidableEq Positive]
  [ElemG GF (COFE.constOF CoPsetDisj)]
  [ElemG GF (COFE.constOF GSetDisj)] in
/-- Two exclusive tokens are contradictory.
Coq: `cinv_excl_excl`. -/
theorem cinv_excl_excl (W : WsatGS GF) (γ : GName) :
    cinv_excl (F := F) W γ ⊢
    BIBase.wand (cinv_excl (F := F) W γ) (BIBase.pure False : IProp GF) := by
  -- exclusive tokens cannot be combined
  refine wand_intro ?_
  refine (iOwn_cmraValid_op (GF := GF) (F := COFE.constOF (CinvR F)) (γ := γ)
    (a1 := (some (Excl.excl (LeibnizO.mk ())), none))
    (a2 := (some (Excl.excl (LeibnizO.mk ())), none))).trans ?_
  refine (UPred.cmraValid_elim
    (a := ((some (Excl.excl (LeibnizO.mk ())), none) : CinvR F) •
      (some (Excl.excl (LeibnizO.mk ())), none))).trans ?_
  refine BI.pure_mono ?_
  intro hvalid0
  have hleft : ✓{0} (Excl.excl (LeibnizO.mk ()) • Excl.excl (LeibnizO.mk ())) := by
    -- reduce to validity of the excl component
    simp [CMRA.ValidN, Prod.ValidN, CMRA.op, Prod.op, optionOp, optionValidN] at hvalid0
  exact (_root_.Iris.CMRA.not_valid_exclN_op_left (n := 0)
    (x := Excl.excl (LeibnizO.mk ())) (y := Excl.excl (LeibnizO.mk ())) hleft)

/-! ## Allocation -/

omit [DecidableEq Positive] in
/-- Validity of the combined ghost token. -/
private theorem cinv_token_valid :
    ✓ ((some (Excl.excl (LeibnizO.mk ())), some ((1 : F) : Frac F)) : CinvR F) := by
  -- validity is componentwise for the product/option CMRA
  refine And.intro ?_ ?_
  · simp [CMRA.Valid, optionValid]
  · simpa [CMRA.Valid, optionValid] using
      (UFraction.one_whole (α := F)).1

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
/-- Allocate an exclusive token together with the full fractional token. -/
private theorem cinv_own_excl_alloc (W : WsatGS GF) (E : Iris.Set Positive) :
    (BIBase.emp : IProp GF) ⊢
      uPred_fupd (M := M) (F := F) W E E
        (BIBase.exists fun (γ : GName) =>
          BIBase.sep (cinv_excl (F := F) W γ) (cinv_own (F := F) W γ (1 : F)) : IProp GF) := by
  -- allocate the combined element and split ownership
  have hvalid := (cinv_token_valid (F := F))
  have halloc :
      (BIBase.emp : IProp GF) ⊢
        BUpd.bupd (BIBase.exists fun γ =>
          iOwn (GF := GF) (F := COFE.constOF (CinvR F)) γ
            ((some (Excl.excl (LeibnizO.mk ())), some ((1 : F) : Frac F)) : CinvR F)) :=
    iOwn_alloc (GF := GF) (F := COFE.constOF (CinvR F)) _ hvalid
  have halloc' :
      (BIBase.emp : IProp GF) ⊢
        uPred_fupd (M := M) (F := F) W E E
          (BIBase.exists fun γ =>
            iOwn (GF := GF) (F := COFE.constOF (CinvR F)) γ
              ((some (Excl.excl (LeibnizO.mk ())), some ((1 : F) : Frac F)) : CinvR F)) :=
    halloc.trans (bupd_fupd (W := W) (M := M) (F := F) (E := E)
      (P := BIBase.exists fun γ =>
        iOwn (GF := GF) (F := COFE.constOF (CinvR F)) γ
          ((some (Excl.excl (LeibnizO.mk ())), some ((1 : F) : Frac F)) : CinvR F)))
  have hsplit :
      BIBase.exists (fun γ =>
        iOwn (GF := GF) (F := COFE.constOF (CinvR F)) γ
          ((some (Excl.excl (LeibnizO.mk ())), some ((1 : F) : Frac F)) : CinvR F)) ⊢
      BIBase.exists fun γ =>
        BIBase.sep (cinv_excl (F := F) W γ) (cinv_own (F := F) W γ (1 : F)) := by
    -- split ownership into exclusive and fractional parts
    refine exists_elim ?_
    intro γ
    have hsep :
        iOwn (GF := GF) (F := COFE.constOF (CinvR F)) γ
          ((some (Excl.excl (LeibnizO.mk ())), some ((1 : F) : Frac F)) : CinvR F) ⊢
          BIBase.sep (cinv_excl (F := F) W γ) (cinv_own (F := F) W γ (1 : F)) := by
      simpa [cinv_excl, cinv_own, CMRA.op, Prod.op, optionOp]
        using (iOwn_op (GF := GF) (F := COFE.constOF (CinvR F)) (γ := γ)
          (a1 := (some (Excl.excl (LeibnizO.mk ())), none))
          (a2 := (none, some ((1 : F) : Frac F)))).1
    iintro Hown
    iapply (wrapEntails (GF := GF) (exists_intro γ))
    iapply (wrapEntails (GF := GF) hsep)
    iexact Hown
  exact halloc'.trans (fupd_mono (W := W) (M := M) (F := F) (E1 := E) (E2 := E)
    (P := _) (Q := _) hsplit)

omit [DecidableEq Positive]
  [ElemG GF (COFE.constOF CoPsetDisj)]
  [ElemG GF (COFE.constOF GSetDisj)] in
/-- Build the later'd invariant body from the left branch. -/
private theorem cinv_body_later_left (W : WsatGS GF) (γ : GName) (P : IProp GF) :
    BIBase.sep (cinv_excl (F := F) W γ) (BIBase.later P) ⊢
      BIBase.later (cinv_body (F := F) W γ P) := by
  -- push `cinv_excl` under `▷` and inject into the left branch
  have hsep :
      BIBase.sep (cinv_excl (F := F) W γ) (BIBase.later P) ⊢
        BIBase.later (BIBase.sep P (cinv_excl (F := F) W γ)) := by
    refine (sep_mono (later_intro (P := cinv_excl (F := F) W γ)) .rfl).trans ?_
    refine (sep_comm (P := BIBase.later (cinv_excl (F := F) W γ)) (Q := BIBase.later P)).1.trans ?_
    exact (later_sep (P := P) (Q := cinv_excl (F := F) W γ)).2
  exact hsep.trans (later_mono (P := BIBase.sep P (cinv_excl (F := F) W γ))
    (Q := cinv_body (F := F) W γ P)
    (or_intro_l (Q := cinv_own (F := F) W γ (1 : F))))

omit [DecidableEq Positive]
  [ElemG GF (COFE.constOF CoPsetDisj)]
  [ElemG GF (COFE.constOF GSetDisj)] in
/-- Build the later'd body from two latered components. -/
private theorem cinv_body_later_left_later (W : WsatGS GF) (γ : GName) (P : IProp GF) :
    BIBase.sep (BIBase.later P) (BIBase.later (cinv_excl (F := F) W γ)) ⊢
      BIBase.later (cinv_body (F := F) W γ P) := by
  -- combine the latered pieces and inject into the left branch
  have hsep :
      BIBase.sep (BIBase.later P) (BIBase.later (cinv_excl (F := F) W γ)) ⊢
        BIBase.later (BIBase.sep P (cinv_excl (F := F) W γ)) :=
    (later_sep (P := P) (Q := cinv_excl (F := F) W γ)).2
  exact hsep.trans (later_mono (P := BIBase.sep P (cinv_excl (F := F) W γ))
    (Q := cinv_body (F := F) W γ P)
    (or_intro_l (Q := cinv_own (F := F) W γ (1 : F))))

/-- Allocate a cancelable invariant from a later'd proposition.
Coq: `cinv_alloc`. -/
theorem cinv_alloc (W : WsatGS GF) (E : Iris.Set Positive) (N : Namespace)
    (P : IProp GF)
    (hfresh : ∀ E : GSet, ∃ i, ¬E.mem i ∧ (nclose N).mem i) :
    BIBase.later P ⊢
    uPred_fupd (M := M) (F := F) W E E
      (BIBase.exists fun (γ : GName) =>
        BIBase.sep (cinv (M := M) (F := F) W N γ P) (cinv_own (F := F) W γ (1 : F)) : IProp GF) := by
  -- allocate tokens, then build the invariant around the exclusive token
  have hframe :
      BIBase.later P ⊢
        uPred_fupd (M := M) (F := F) W E E
          (BIBase.sep (BIBase.exists fun γ =>
            BIBase.sep (cinv_excl (F := F) W γ) (cinv_own (F := F) W γ (1 : F)))
            (BIBase.later P)) := by
    -- frame `▷ P` through the token allocation
    refine (sep_emp (P := BIBase.later P)).2.trans ?_
    refine (sep_mono .rfl
      (cinv_own_excl_alloc (W := W) (M := M) (F := F) (E := E))).trans ?_
    refine (sep_comm (P := BIBase.later P)
      (Q := uPred_fupd (M := M) (F := F) W E E
        (BIBase.exists fun γ =>
          BIBase.sep (cinv_excl (F := F) W γ) (cinv_own (F := F) W γ (1 : F))))).1.trans ?_
    exact fupd_frame_r (W := W) (M := M) (F := F) (E1 := E) (E2 := E)
      (P := BIBase.exists fun γ => BIBase.sep (cinv_excl (F := F) W γ) (cinv_own (F := F) W γ (1 : F)))
      (Q := BIBase.later P)
  have hpost :
      BIBase.sep (BIBase.exists fun γ =>
        BIBase.sep (cinv_excl (F := F) W γ) (cinv_own (F := F) W γ (1 : F))) (BIBase.later P) ⊢
        uPred_fupd (M := M) (F := F) W E E
          (BIBase.exists fun γ =>
            BIBase.sep (cinv (M := M) (F := F) W N γ P) (cinv_own (F := F) W γ (1 : F)) : IProp GF) := by
    -- pull the existential out of the separating conjunction
    refine (sep_exists_r (Φ := fun γ => BIBase.sep (cinv_excl (F := F) W γ)
        (cinv_own (F := F) W γ (1 : F))) (Q := BIBase.later P)).1.trans ?_
    refine exists_elim ?_
    intro γ
    have halloc :
        BIBase.sep (cinv_excl (F := F) W γ) (BIBase.later P) ⊢
          uPred_fupd (M := M) (F := F) W E E (cinv (M := M) (F := F) W N γ P) := by
      -- pack `▷ body` and call `inv_alloc`
      have hbody := cinv_body_later_left (W := W) (F := F) (γ := γ) (P := P)
      have halloc :=
        inv_alloc (W := W) (M := M) (F := F) (N := N) (E := E)
          (P := cinv_body (F := F) W γ P) hfresh
      simpa [cinv, cinv_body] using hbody.trans halloc
    have hframe' :
        BIBase.sep (BIBase.sep (cinv_excl (F := F) W γ) (cinv_own (F := F) W γ (1 : F))) (BIBase.later P) ⊢
          uPred_fupd (M := M) (F := F) W E E
            (BIBase.sep (cinv (M := M) (F := F) W N γ P) (cinv_own (F := F) W γ (1 : F))) := by
      -- reassociate to frame the fractional token through the update
      refine (sep_assoc (P := cinv_excl (F := F) W γ) (Q := cinv_own (F := F) W γ (1 : F))
        (R := BIBase.later P)).1.trans ?_
      refine (sep_mono .rfl
        (sep_comm (P := cinv_own (F := F) W γ (1 : F)) (Q := BIBase.later P)).1).trans ?_
      refine (sep_assoc (P := cinv_excl (F := F) W γ) (Q := BIBase.later P)
        (R := cinv_own (F := F) W γ (1 : F))).2.trans ?_
      refine (sep_mono halloc .rfl).trans ?_
      exact fupd_frame_r (W := W) (M := M) (F := F) (E1 := E) (E2 := E)
        (P := cinv (M := M) (F := F) W N γ P) (Q := cinv_own (F := F) W γ (1 : F))
    iintro Hctx
    icases Hctx with ⟨Hpair, HP⟩
    icases Hpair with ⟨Hexcl, Hown⟩
    have hexists :
        BIBase.sep (cinv (M := M) (F := F) W N γ P) (cinv_own (F := F) W γ (1 : F)) ⊢
          BIBase.exists fun γ =>
            BIBase.sep (cinv (M := M) (F := F) W N γ P) (cinv_own (F := F) W γ (1 : F)) := by
      -- introduce the chosen name into the existential
      iintro Hpair
      iapply (wrapEntails (GF := GF) (exists_intro γ))
      iexact Hpair
    iapply (wrapEntails (GF := GF) (fupd_mono (W := W) (M := M) (F := F)
      (E1 := E) (E2 := E)
      (P := BIBase.sep (cinv (M := M) (F := F) W N γ P) (cinv_own (F := F) W γ (1 : F)))
      (Q := BIBase.exists fun γ =>
        BIBase.sep (cinv (M := M) (F := F) W N γ P) (cinv_own (F := F) W γ (1 : F)))
      hexists))
    iapply (wrapEntails (GF := GF) hframe')
    isplitl [Hexcl Hown]
    · isplitl [Hexcl]
      · iexact Hexcl
      · iexact Hown
    · iexact HP
  have hmono :=
    fupd_mono (W := W) (M := M) (F := F) (E1 := E) (E2 := E)
      (P := _) (Q := uPred_fupd (M := M) (F := F) W E E _) hpost
  exact hframe.trans (hmono.trans (fupd_trans (W := W) (M := M) (F := F)
    (E1 := E) (E2 := E) (E3 := E) (P := _)))

/-! ## Accessors -/

omit [DecidableEq Positive]
  [ElemG GF (COFE.constOF CoPsetDisj)]
  [ElemG GF (COFE.constOF GSetDisj)] in
/-- Right branch yields a contradiction with any external fraction. -/
private theorem cinv_own_later_false (W : WsatGS GF) (γ : GName) (p : F) :
    BIBase.sep (BIBase.later (cinv_own (F := F) W γ (1 : F))) (cinv_own (F := F) W γ p) ⊢
      BIBase.later (BIBase.pure False : IProp GF) := by
  -- move the contradiction under `▷` and apply it
  have hwand :
      BIBase.later (cinv_own (F := F) W γ (1 : F)) ⊢
        BIBase.wand (BIBase.later (cinv_own (F := F) W γ p))
          (BIBase.later (BIBase.pure False : IProp GF)) := by
    refine (later_mono
      (P := cinv_own (F := F) W γ (1 : F))
      (Q := BIBase.wand (cinv_own (F := F) W γ p) (BIBase.pure False))
      (cinv_own_1_l (W := W) (γ := γ) (q := p))).trans ?_
    exact later_wand (P := cinv_own (F := F) W γ p) (Q := BIBase.pure False)
  refine (sep_mono hwand (later_intro (P := cinv_own (F := F) W γ p))).trans ?_
  exact wand_elim_l

omit [DecidableEq Positive] [FiniteMapLaws Positive M]
  [ElemG GF (COFE.constOF CoPsetDisj)]
  [ElemG GF (COFE.constOF GSetDisj)] in
/-- Cancel a nested `except0` inside a separating conjunction.

    This is a local copy of the invariant helper to avoid opening the private lemma.
    Coq: internal lemma used in `inv_acc_timeless`. -/
private theorem except0_sep_idemp (P Q R : IProp GF) :
    BIBase.except0 (BIBase.sep P (BIBase.sep (BIBase.except0 Q) R)) ⊣⊢
      BIBase.except0 (BIBase.sep P (BIBase.sep Q R)) := by
  -- distribute except0, eliminate the inner idempotence, then reassemble
  calc
    BIBase.except0 (BIBase.sep P (BIBase.sep (BIBase.except0 Q) R))
        ⊣⊢ BIBase.sep (BIBase.except0 P)
              (BIBase.except0 (BIBase.sep (BIBase.except0 Q) R)) := by
          -- push except0 into the outer sep
          exact (except0_sep (P := P) (Q := BIBase.sep (BIBase.except0 Q) R))
    _ ⊣⊢ BIBase.sep (BIBase.except0 P)
            (BIBase.sep (BIBase.except0 (BIBase.except0 Q)) (BIBase.except0 R)) := by
          -- distribute except0 across the inner sep
          exact sep_congr_r (except0_sep (P := BIBase.except0 Q) (Q := R))
    _ ⊣⊢ BIBase.sep (BIBase.except0 P)
            (BIBase.sep (BIBase.except0 Q) (BIBase.except0 R)) := by
          -- collapse the redundant except0
          exact sep_congr_r (sep_congr_l except0_idemp)
    _ ⊣⊢ BIBase.sep (BIBase.except0 P) (BIBase.except0 (BIBase.sep Q R)) := by
          -- reassemble the inner except0
          exact sep_congr_r (except0_sep (P := Q) (Q := R)).symm
    _ ⊣⊢ BIBase.except0 (BIBase.sep P (BIBase.sep Q R)) := by
          -- pull except0 back out
          exact (except0_sep (P := P) (Q := BIBase.sep Q R)).symm

omit [DecidableEq Positive] [FiniteMapLaws Positive M]
  [ElemG GF (COFE.constOF (CinvR F))] in
/-- Drop an extra `except0` under `fupd`.

    This mirrors the helper used for invariants to simplify postconditions.
    Coq: internal lemma used in `inv_acc_timeless`. -/
private theorem fupd_drop_except0_post {W : WsatGS GF}
    (E1 E2 : Iris.Set Positive) (P Q : IProp GF) :
    uPred_fupd (M := M) (F := F) W E1 E2
        (BIBase.sep (BIBase.except0 P) Q) ⊢
      uPred_fupd (M := M) (F := F) W E1 E2 (BIBase.sep (PROP := IProp GF) P Q) := by
  -- push except0 through the fupd post, then cancel the redundant layer
  unfold uPred_fupd
  refine wand_mono_r ?_
  refine BIUpdate.mono ?_
  let A : IProp GF := wsat (GF := GF) (M := M) (F := F) W
  let B : IProp GF := ownE W (⟨E2⟩ : CoPset)
  have h :
      BIBase.except0 (BIBase.sep A (BIBase.sep B (BIBase.sep (BIBase.except0 P) Q))) ⊣⊢
        BIBase.except0 (BIBase.sep A (BIBase.sep B (BIBase.sep (PROP := IProp GF) P Q))) := by
    -- reassociate, drop the inner except0, then reassociate back
    calc
      BIBase.except0 (BIBase.sep A (BIBase.sep B (BIBase.sep (BIBase.except0 P) Q)))
          ⊣⊢ BIBase.except0 (BIBase.sep (BIBase.sep A B)
            (BIBase.sep (BIBase.except0 P) Q)) := by
            -- expose the left-associated sep
            exact except0_congr (sep_assoc (P := A) (Q := B)
              (R := BIBase.sep (BIBase.except0 P) Q)).symm
      _ ⊣⊢ BIBase.except0 (BIBase.sep (BIBase.sep A B) (BIBase.sep (PROP := IProp GF) P Q)) := by
            -- remove the redundant except0 on the postcondition
            exact except0_sep_idemp (P := BIBase.sep A B) (Q := P) (R := Q)
      _ ⊣⊢ BIBase.except0 (BIBase.sep A (BIBase.sep B (BIBase.sep (PROP := IProp GF) P Q))) := by
            -- restore right association
            exact except0_congr (sep_assoc (P := A) (Q := B) (R := BIBase.sep (PROP := IProp GF) P Q))
  simpa [A, B] using h.1

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
/-- Open a cancelable invariant with a fractional token.
Coq: `cinv_acc`. -/
theorem cinv_acc (W : WsatGS GF) (E : Iris.Set Positive) (N : Namespace)
    (γ : GName) (p : F) (P : IProp GF) (hN : Subset (nclose N).mem E) :
    cinv (M := M) (F := F) W N γ P ⊢
    BIBase.wand (cinv_own (F := F) W γ p)
      (uPred_fupd (M := M) (F := F) W E (maskDiff E N)
        (BIBase.sep (BIBase.later P)
          (BIBase.sep (cinv_own (F := F) W γ p)
            (BIBase.wand (BIBase.later P)
              (uPred_fupd (M := M) (F := F) W
                (maskDiff E N) E
                (BIBase.pure True)))))) := by
  -- open the underlying invariant and rule out the cancelled branch
  iintro Hinv
  iintro Hown
  let Qacc : IProp GF :=
    uPred_fupd (M := M) (F := F) W E (maskDiff E N)
      (BIBase.sep (BIBase.later (cinv_body (F := F) W γ P))
        (BIBase.wand (BIBase.later (cinv_body (F := F) W γ P))
          (uPred_fupd (M := M) (F := F) W (maskDiff E N) E (BIBase.pure True))))
  have hacc : cinv (M := M) (F := F) W N γ P ⊢ Qacc := by
    -- unfold the invariant body and reuse `inv_acc`
    simpa [cinv, cinv_body, Qacc] using
      (inv_acc (W := W) (M := M) (F := F) (E := E) (N := N)
        (P := cinv_body (F := F) W γ P) hN)
  ihave Hacc := (wrapEntails (GF := GF) hacc) $$ Hinv
  have hframe :=
    fupd_frame_r (W := W) (M := M) (F := F) (E1 := E) (E2 := maskDiff E N)
      (P := BIBase.sep (BIBase.later (cinv_body (F := F) W γ P))
        (BIBase.wand (BIBase.later (cinv_body (F := F) W γ P))
          (uPred_fupd (M := M) (F := F) W (maskDiff E N) E
            (BIBase.pure True))))
      (Q := cinv_own (F := F) W γ p)
  have hpost :
      BIBase.sep (BIBase.sep (BIBase.later (cinv_body (F := F) W γ P))
        (BIBase.wand (BIBase.later (cinv_body (F := F) W γ P))
          (uPred_fupd (M := M) (F := F) W (maskDiff E N) E
            (BIBase.pure True))))
        (cinv_own (F := F) W γ p) ⊢
      BIBase.sep (BIBase.except0 (cinv_own (F := F) W γ p))
        (BIBase.sep (BIBase.later P)
          (BIBase.wand (BIBase.later P)
            (uPred_fupd (M := M) (F := F) W (maskDiff E N) E
              (BIBase.pure True) : IProp GF))) := by
    -- split on the invariant body and close using the exclusive token
    iintro Hctx
    icases Hctx with ⟨Hbody, Hown'⟩
    icases Hbody with ⟨Hbody, Hclose⟩
    ihave Hbody' :=
      (wrapEntails (GF := GF)
        (later_or (P := BIBase.sep P (cinv_excl (F := F) W γ))
          (Q := cinv_own (F := F) W γ (1 : F))).1) $$ Hbody
    icases Hbody' with (Hleft | Hright)
    · -- left branch: reopen the invariant with the exclusive token
      ihave Hleft' :=
        (wrapEntails (GF := GF)
          (later_sep (P := P) (Q := cinv_excl (F := F) W γ)).1) $$ Hleft
      icases Hleft' with ⟨HP, Hexcl⟩
      isplitl [Hown']
      · -- expose the token under `◇`
        iapply (wrapEntails (GF := GF)
          (except0_intro (P := cinv_own (F := F) W γ p)))
        iexact Hown'
      · isplitl [HP]
        · iexact HP
        · iintro HP'
          iapply Hclose
          iapply (wrapEntails (GF := GF)
            (cinv_body_later_left_later (W := W) (F := F) (γ := γ) (P := P)))
          isplitl [HP']
          · iexact HP'
          · iexact Hexcl
    · -- right branch: contradiction with the external fraction
      ihave Hfalse : BIBase.later (BIBase.pure False) $$ [Hright, Hown']
      · iapply (wrapEntails (GF := GF)
          (cinv_own_later_false (W := W) (γ := γ) (p := p)))
        isplitl [Hright]
        · iexact Hright
        · iexact Hown'
      ihave Hfalse' :=
        (wrapEntails (GF := GF)
          (persistent_entails_r (P := BIBase.later (BIBase.pure False))
            (Q := BIBase.later (BIBase.pure False)) .rfl)) $$ Hfalse
      icases Hfalse' with ⟨Hfalse₁, Hfalse₂⟩
      ihave HP :=
        (wrapEntails (GF := GF)
          (later_mono (P := BIBase.pure False) (Q := P) false_elim)) $$ Hfalse₁
      ihave Hfalse'' :=
        (wrapEntails (GF := GF)
          (persistent_entails_r (P := BIBase.later (BIBase.pure False))
            (Q := BIBase.later (BIBase.pure False)) .rfl)) $$ Hfalse₂
      icases Hfalse'' with ⟨Hfalse₂a, Hfalse₂b⟩
      ihave Hown'' :=
        (wrapEntails (GF := GF) (by
          simpa [BIBase.except0] using
            (or_intro_l (P := BIBase.later (BIBase.pure False))
              (Q := cinv_own (F := F) W γ p)))) $$ Hfalse₂a
      isplitl [Hown'']
      ·
        simp [BIBase.except0]
      · isplitl [HP]
        · iexact HP
        · iintro _
          ihave HbodyFalse :=
            (wrapEntails (GF := GF)
              (later_mono (P := BIBase.pure False)
                (Q := cinv_body (F := F) W γ P) false_elim)) $$ Hfalse₂b
          iapply Hclose
          iexact HbodyFalse
  -- apply the postcondition and frame the token
  have hreorder :
      BIBase.sep (cinv_own (F := F) W γ p)
        (BIBase.sep (BIBase.later P)
          (BIBase.wand (BIBase.later P)
            (uPred_fupd (M := M) (F := F) W (maskDiff E N) E
              (BIBase.pure True) : IProp GF))) ⊢
      BIBase.sep (BIBase.later P)
        (BIBase.sep (cinv_own (F := F) W γ p)
          (BIBase.wand (BIBase.later P)
            (uPred_fupd (M := M) (F := F) W (maskDiff E N) E
              (BIBase.pure True) : IProp GF))) := by
    -- reassociate, swap the first two conjuncts, then reassociate back
    refine (sep_assoc (P := cinv_own (F := F) W γ p)
      (Q := BIBase.later P)
      (R := BIBase.wand (BIBase.later P)
        (uPred_fupd (M := M) (F := F) W (maskDiff E N) E
          (BIBase.pure True) : IProp GF))).symm.1.trans ?_
    refine (sep_congr_l sep_comm).1.trans ?_
    exact (sep_assoc (P := BIBase.later P)
      (Q := cinv_own (F := F) W γ p)
      (R := BIBase.wand (BIBase.later P)
        (uPred_fupd (M := M) (F := F) W (maskDiff E N) E
          (BIBase.pure True) : IProp GF))).1
  have hdrop :=
    fupd_drop_except0_post (W := W) (M := M) (F := F)
      (E1 := E) (E2 := maskDiff E N)
      (P := cinv_own (F := F) W γ p)
      (Q := BIBase.sep (BIBase.later P)
        (BIBase.wand (BIBase.later P)
          (uPred_fupd (M := M) (F := F) W (maskDiff E N) E
            (BIBase.pure True) : IProp GF)))
  have hmono :=
    fupd_mono (W := W) (M := M) (F := F) (E1 := E) (E2 := maskDiff E N)
      (P := _) (Q := _) hpost
  have hreorder' :=
    fupd_mono (W := W) (M := M) (F := F) (E1 := E) (E2 := maskDiff E N)
      (P := _) (Q := _) hreorder
  iapply (wrapEntails (GF := GF) (hmono.trans (hdrop.trans hreorder')))
  iapply (wrapEntails (GF := GF) hframe)
  isplitl [Hacc]
  · iexact Hacc
  · iexact Hown
  -- done: `fupd_mono` applied directly to the framed access

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
/-- This is the `cinv_acc` accessor specialized to the full token.
Coq: `cinv_acc_1` (non-atomic) — we use the atomic accessor in this model. -/
theorem cinv_acc_1 (W : WsatGS GF) (E : Iris.Set Positive) (N : Namespace)
    (γ : GName) (P : IProp GF) (hN : Subset (nclose N).mem E) :
    cinv (M := M) (F := F) W N γ P ⊢
    BIBase.wand (cinv_own (F := F) W γ (1 : F))
      (uPred_fupd (M := M) (F := F) W E (maskDiff E N)
        (BIBase.sep (BIBase.later P)
          (BIBase.sep (cinv_own (F := F) W γ (1 : F))
            (BIBase.wand (BIBase.later P)
              (uPred_fupd (M := M) (F := F) W (maskDiff E N) E
                (BIBase.pure True)))))) := by
  -- specialize `cinv_acc` to the full token
  simpa using
    (cinv_acc (W := W) (M := M) (F := F)
      (E := E) (N := N) (γ := γ) (p := (1 : F)) (P := P) hN)

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
/-- Cancel an invariant: open with the full token (atomic accessor).

This is a weakened version of Coq's `cinv_cancel`, since we only have the
atomic accessor in this model. -/
theorem cinv_cancel (W : WsatGS GF) (E : Iris.Set Positive) (N : Namespace)
    (γ : GName) (P : IProp GF) (hN : Subset (nclose N).mem E) :
    cinv (M := M) (F := F) W N γ P ⊢
    BIBase.wand (cinv_own (F := F) W γ (1 : F))
      (uPred_fupd (M := M) (F := F) W E (maskDiff E N)
        (BIBase.sep (BIBase.later P)
          (BIBase.sep (cinv_own (F := F) W γ (1 : F))
            (BIBase.wand (BIBase.later P)
              (uPred_fupd (M := M) (F := F) W (maskDiff E N) E
                (BIBase.pure True)))))) := by
  -- specialize the atomic accessor to the full token
  simpa using
    (cinv_acc (W := W) (M := M) (F := F)
      (E := E) (N := N) (γ := γ) (p := (1 : F)) (P := P) hN)

/-! ## Proof Mode Integration -/

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
/-- `cinv` can be opened by `iInv`. -/
instance into_inv_cinv {W : WsatGS GF} (N : Namespace) (γ : GName) (P : IProp GF) :
    Iris.ProofMode.IntoInv (PROP := IProp GF)
      (cinv (M := M) (F := F) W N γ P) N := by
  -- marker instance carries only the namespace
  exact ⟨⟩

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
/-- Accessor instance for cancelable invariants. -/
instance into_acc_cinv {W : WsatGS GF}
    (E : Iris.Set Positive) (N : Namespace) (γ : GName) (P : IProp GF) (p : F) :
    Iris.ProofMode.IntoAcc (PROP := IProp GF) (X := Unit)
      (cinv (M := M) (F := F) W N γ P)
      (Subset (nclose N).mem E) (cinv_own (F := F) W γ p)
      (uPred_fupd (M := M) (F := F) W E (maskDiff E N))
      (uPred_fupd (M := M) (F := F) W (maskDiff E N) E)
      (fun _ => BIBase.sep (BIBase.later P) (cinv_own (F := F) W γ p))
      (fun _ => BIBase.later P)
      (fun _ => some (BIBase.pure True)) := by
  -- unfold the accessor and use `cinv_acc`
  refine ⟨?_⟩
  intro hsubset
  -- unfold the accessor to match `cinv_acc`
  simp [Iris.ProofMode.accessor]
  iintro Hinv
  iintro Hown
  let Ψ : Unit → IProp GF := fun _ =>
    BIBase.sep (BIBase.sep (BIBase.later P) (cinv_own (F := F) W γ p))
      (BIBase.wand (BIBase.later P)
        (uPred_fupd (M := M) (F := F) W (maskDiff E N) E (BIBase.pure True)))
  have hreassoc :
      BIBase.sep (BIBase.later P)
        (BIBase.sep (cinv_own (F := F) W γ p)
          (BIBase.wand (BIBase.later P)
            (uPred_fupd (M := M) (F := F) W (maskDiff E N) E
              (BIBase.pure True)))) ⊢ Ψ () := by
    -- reassociate the separating conjunction to match the accessor shape
    exact (sep_assoc (P := BIBase.later P)
      (Q := cinv_own (F := F) W γ p)
      (R := BIBase.wand (BIBase.later P)
        (uPred_fupd (M := M) (F := F) W (maskDiff E N) E
          (BIBase.pure True)))).symm.1
  have hmono₁ :=
    fupd_mono (W := W) (M := M) (F := F) (E1 := E) (E2 := maskDiff E N)
      (P := _) (Q := _) hreassoc
  have hmono₂ :=
    fupd_mono (W := W) (M := M) (F := F) (E1 := E) (E2 := maskDiff E N)
      (P := Ψ ()) (Q := BIBase.exists Ψ) (exists_unit (Ψ := Ψ)).2
  have hacc :=
    cinv_acc (W := W) (M := M) (F := F)
      (E := E) (N := N) (γ := γ) (p := p) (P := P) hsubset
  have hacc' := hacc.trans (wand_mono_r (hmono₁.trans hmono₂))
  ihave Hacc := (wrapEntails (GF := GF) hacc') $$ Hinv
  ihave Hacc' := Hacc $$ Hown
  iexact Hacc'

end Iris.BaseLogic
