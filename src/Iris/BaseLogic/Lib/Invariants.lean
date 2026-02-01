/-
Copyright (c) 2026 Sam Hart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Hart
-/
import Iris.BaseLogic.Lib.FancyUpdates
import Iris.ProofMode.Tactics
import Iris.Std.Namespace

/-! # Invariants

Reference: `iris/base_logic/lib/invariants.v`

Invariants are the main user-facing mechanism for shared ownership in Iris.
An invariant `inv N P` asserts that proposition `P` is maintained as an
invariant registered under namespace `N`. It is a *derived* definition built
on top of fancy updates and world satisfaction — not a new primitive.

## Definition

```
inv N P := □ ∀ E, ⌜↑N ⊆ E⌝ → |={E, E ∖ ↑N}=> ▷ P ∗ (▷ P ={E ∖ ↑N, E}=∗ True)
```

## Main Results

- `inv_persistent` — `inv N P` is persistent
- `inv_alloc` — `▷ P ={E}=∗ inv N P`
- `inv_alloc_open` — allocate and immediately open
- `inv_acc` — `↑N ⊆ E → inv N P ={E,E∖↑N}=∗ ▷ P ∗ (▷ P ={E∖↑N,E}=∗ True)`
- `inv_acc_timeless` — strip `▷` when `P` is timeless
-/

namespace Iris.BaseLogic

open Iris Iris.Algebra Iris.Std Iris.BI

variable {GF : BundledGFunctors} {M : Type _ → Type _} {F : Type _}
variable [UFraction F]
variable [FiniteMap Positive M] variable [FiniteMapLaws Positive M] [HeapFiniteMap Positive M]
variable [ElemG GF (InvF GF M F)]
variable [ElemG GF (COFE.constOF CoPsetDisj)]
variable [ElemG GF (COFE.constOF GSetDisj)]

/-- Mask difference: `E ∖ ↑N` as a set predicate. -/
private abbrev maskDiff (E : Iris.Set Positive) (N : Namespace) :
    Iris.Set Positive :=
  fun x => E x ∧ ¬(nclose N).mem x

-- Keep IProp entailments opaque for proof mode (avoid unfolding to `holds`).
private structure IPropEntails (P Q : IProp GF) : Prop where
  toEntails : P ⊢ Q

private def wrapEntails {P Q : IProp GF} (h : P ⊢ Q) :
    IPropEntails (GF := GF) P Q :=
  ⟨h⟩

local instance asEmpValid_IPropEntails_inv (d : Iris.ProofMode.AsEmpValid.Direction)
    (P Q : IProp GF) :
    Iris.ProofMode.AsEmpValid d (IPropEntails (GF := GF) P Q) iprop(P -∗ Q) := by
  have hEntails :
      Iris.ProofMode.AsEmpValid d (P ⊢ Q) iprop(P -∗ Q) := inferInstance
  refine ⟨?_, ?_⟩
  · intro hd h
    exact (hEntails.as_emp_valid.1 hd) h.toEntails
  · intro hd h
    exact ⟨(hEntails.as_emp_valid.2 hd) h⟩

-- Make `ownI` persistent for proof mode use.
instance ownI_persistent_inst {W : WsatGS GF} (i : Positive) (P : IProp GF) :
    Persistent (ownI (GF := GF) (M := M) (F := F) W i P) :=
  ⟨ownI_persistent (W := W) (i := i) (P := P)⟩

/-! ## Internal Model -/

/-- Internal invariant ownership: existential over a name in the namespace.

    Coq: `own_inv` -/
noncomputable def own_inv (_W : WsatGS GF)
    (N : Namespace) (P : IProp GF) : IProp GF :=
  BIBase.exists fun i =>
    BIBase.and (BIBase.pure ((nclose N).mem i))
      (ownI (GF := GF) (M := M) (F := F) _W i P)

-- `own_inv` is persistent: pure facts plus persistent `ownI`.
local instance own_inv_persistent_inst {W : WsatGS GF} (N : Namespace) (P : IProp GF) :
    Persistent (own_inv (GF := GF) (M := M) (F := F) W N P) := by
  -- unfold and rely on `exists_persistent`/`and_persistent`.
  unfold own_inv
  infer_instance

/-- Access an internal invariant: open it to get `▷ P` and a closing view shift.

    Coq: `own_inv_acc` -/
theorem own_inv_acc {W : WsatGS GF}
    (N : Namespace) (E : Iris.Set Positive) (P : IProp GF)
    (h : Subset (nclose N).mem E) :
    own_inv (GF := GF) (M := M) (F := F) W N P ⊢
      uPred_fupd (M := M) (F := F) W E (maskDiff E N)
        (BIBase.sep (BIBase.later P)
          (BIBase.wand (BIBase.later P)
            (uPred_fupd (M := M) (F := F) W (maskDiff E N) E
              (BIBase.pure True)))) := by
  classical
  unfold uPred_fupd
  unfold own_inv
  -- eliminate the existential invariant name
  refine exists_elim ?_
  intro i
  iintro Hinv
  iintro H
  icases Hinv with ⟨Hmem, HownI⟩
  icases Hmem with %Hmem
  icases HownI with #HownI
  icases H with ⟨Hwsat, HownE⟩
  -- split the enabled mask into `↑N` and `E \ ↑N`
  have hmask : mask E = (nclose N) ∪ mask (maskDiff E N) := by
    ext x; constructor
    · intro hx
      by_cases hxN : (nclose N).mem x
      · exact Or.inl hxN
      · exact Or.inr ⟨hx, hxN⟩
    · intro hx
      cases hx with
      | inl hxN => exact h _ hxN
      | inr hxDiff => exact hxDiff.1
  have hdisj : CoPset.Disjoint (nclose N) (mask (maskDiff E N)) := by
    intro x hx
    exact hx.2.2 hx.1
  have hsplit :
      ownE W (mask E) ⊢
        BIBase.sep (ownE W (nclose N)) (ownE W (mask (maskDiff E N))) := by
    -- rewrite the mask to the disjoint union and apply `ownE_op`
    rw [hmask]
    exact (ownE_op (W := W) (E₁ := nclose N) (E₂ := mask (maskDiff E N)) hdisj).1
  ihave Hsplit := (wrapEntails (GF := GF) hsplit) $$ HownE
  icases Hsplit with ⟨HownEN, HownEdiff⟩

  -- split `↑N` into `{i}` and the remainder
  let rest : CoPset := nclose N \ CoPset.singleton i
  have hmaskN : (nclose N) = (CoPset.singleton i) ∪ rest := by
    ext x; constructor
    · intro hxN
      by_cases hx : x = i
      · left; simpa [CoPset.mem_singleton] using hx
      · right; exact ⟨hxN, by simpa [CoPset.mem_singleton, rest] using hx⟩
    · intro hx
      cases hx with
      | inl hx =>
          have hx' : x = i := by simpa [CoPset.mem_singleton] using hx
          subst hx'
          exact Hmem
      | inr hx => exact hx.1
  have hdisjN : CoPset.Disjoint (CoPset.singleton i) rest := by
    intro x hx
    exact hx.2.2 hx.1
  have hsplitN :
      ownE W (nclose N) ⊢
        BIBase.sep (ownE W (CoPset.singleton i)) (ownE W rest) := by
    -- rewrite the namespace to the singleton union and apply `ownE_op`
    rw [hmaskN]
    exact (ownE_op (W := W) (E₁ := CoPset.singleton i) (E₂ := rest) hdisjN).1
  ihave HsplitN := (wrapEntails (GF := GF) hsplitN) $$ HownEN
  icases HsplitN with ⟨HownEi, HownErest⟩

  -- open the invariant
  icases (wrapEntails (GF := GF)
    (ownI_open (W := W) (M := M) (F := F) i P)) $$ [Hwsat, HownI, HownEi]
    with ⟨Hsep, HownD⟩
  · -- build the premise `(wsat ∗ ownI) ∗ ownE`
    isplitl [Hwsat HownI]
    · isplitl [Hwsat]
      · iexact Hwsat
      · iexact HownI
    · iexact HownEi
  icases Hsep with ⟨Hwsat', HlaterP⟩

  -- introduce bupd and except0
  iapply BIUpdate.intro
  iapply (wrapEntails (GF := GF) (except0_intro (P := _)))
  -- assemble the postcondition
  isplitl [Hwsat']
  · iexact Hwsat'
  · isplitl [HownEdiff]
    · iexact HownEdiff
    · isplitl [HlaterP]
      · iexact HlaterP
      · -- closing wand
        iintro HP
        iintro Hclose
        icases Hclose with ⟨Hwsat2, HownEdiff2⟩
        ihave Hclose' :=
          (wrapEntails (GF := GF)
            (ownI_close (W := W) (M := M) (F := F) i P)) $$ [Hwsat2, HownI, HP, HownD]
        · -- build the premise `((wsat ∗ ownI) ∗ ▷ P) ∗ ownD`
          isplitl [Hwsat2 HownI HP]
          · isplitl [Hwsat2 HownI]
            · isplitl [Hwsat2]
              · iexact Hwsat2
              · iexact HownI
            · iexact HP
          · iexact HownD
        icases Hclose' with ⟨Hwsat3, HownEi'⟩
        have hjoinN :
            BIBase.sep (ownE W (CoPset.singleton i)) (ownE W rest) ⊢
            ownE W (nclose N) := by
          -- rewrite the namespace to the singleton union and apply `ownE_op`
          rw [hmaskN]
          exact (ownE_op (W := W) (E₁ := CoPset.singleton i) (E₂ := rest) hdisjN).2
        ihave HjoinN := (wrapEntails (GF := GF) hjoinN) $$ [HownEi', HownErest]
        · -- assemble the singleton/rest split
          isplitl [HownEi']
          · iexact HownEi'
          · iexact HownErest
        have hjoin :
            BIBase.sep (ownE W (nclose N)) (ownE W (mask (maskDiff E N))) ⊢
            ownE W (mask E) := by
          -- rewrite the mask to the disjoint union and apply `ownE_op`
          rw [hmask]
          exact (ownE_op (W := W) (E₁ := nclose N)
            (E₂ := mask (maskDiff E N)) hdisj).2
        ihave Hjoin := (wrapEntails (GF := GF) hjoin) $$ [HjoinN, HownEdiff2]
        · -- rejoin `↑N` with the remaining mask
          isplitl [HjoinN]
          · iexact HjoinN
          · iexact HownEdiff2
        iapply BIUpdate.intro
        iapply (wrapEntails (GF := GF) (except0_intro (P := _)))
        isplitl [Hwsat3]
        · iexact Hwsat3
        · isplitl [Hjoin]
          · iexact Hjoin
          · ipure_intro
            exact True.intro

/-! ## Definition -/

/-- Semantic invariant: `inv N P` asserts that `P` is maintained as an
    invariant under namespace `N`. This is persistent — once allocated,
    the invariant exists forever.

    Coq: `inv_def` -/
noncomputable def inv (_W : WsatGS GF)
    (N : Namespace) (P : IProp GF) : IProp GF :=
  BIBase.persistently <|
    BIBase.forall fun E : Iris.Set Positive =>
      BIBase.imp (BIBase.pure (Subset (nclose N).mem E))
        (uPred_fupd (M := M) (F := F) _W E (maskDiff E N)
          (BIBase.sep (BIBase.later P)
            (BIBase.wand (BIBase.later P)
              (uPred_fupd (M := M) (F := F) _W (maskDiff E N) E
                (BIBase.pure True)))))

-- `inv` as a non-expansive body over a latered parameter.
private def invBody (_W : WsatGS GF)
    (N : Namespace) (X : IProp GF) : IProp GF :=
  BIBase.persistently <|
    BIBase.forall fun E : Iris.Set Positive =>
      BIBase.imp (BIBase.pure (Subset (nclose N).mem E))
        (uPred_fupd (M := M) (F := F) _W E (maskDiff E N)
          (BIBase.sep X
            (BIBase.wand X
              (uPred_fupd (M := M) (F := F) _W (maskDiff E N) E
                (BIBase.pure True)))))

/-! ## Notation -/

-- `inv` notation inside `iprop(...)` quotations.
macro_rules
  | `(iprop(inv $W $N $P)) =>
      `(Iris.BaseLogic.inv (W := $W) $N iprop($P))

delab_rule Iris.BaseLogic.inv
  | `($_ $W $N $P) => do
      -- display as `inv W N P` inside `iprop(...)`.
      `(iprop(inv $W $N $(← unpackIprop P)))

private theorem own_inv_to_inv {W : WsatGS GF}
    (N : Namespace) (P : IProp GF) :
    own_inv (GF := GF) (M := M) (F := F) W N P ⊢
      inv (GF := GF) (M := M) (F := F) W N P := by
  unfold inv
  refine (persistently_intro''
    (P := own_inv (GF := GF) (M := M) (F := F) W N P) (Q := _) ?_)
  -- show the invariant body from internal ownership
  refine forall_intro ?_
  intro E
  refine imp_intro ?_
  -- pull the pure subset assumption into the context
  refine pure_elim_r ?_
  intro hsubset
  exact (own_inv_acc (W := W) (N := N) (E := E) (P := P) hsubset)

omit [UFraction F] [FiniteMap Positive M]   [FiniteMapLaws Positive M] [HeapFiniteMap Positive M]
  [ElemG GF (InvF GF M F)] [ElemG GF (COFE.constOF CoPsetDisj)]
  [ElemG GF (COFE.constOF GSetDisj)] in
private theorem except0_sep_idemp {P Q R : IProp GF} :
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

omit [FiniteMapLaws Positive M] in
private theorem fupd_drop_except0_post {W : WsatGS GF}
    (E1 E2 : Iris.Set Positive) (P Q : IProp GF) :
    uPred_fupd (M := M) (F := F) W E1 E2
        (BIBase.sep (BIBase.except0 P) Q) ⊢
      uPred_fupd (M := M) (F := F) W E1 E2 (BIBase.sep (PROP := IProp GF) P Q) := by
  -- drop the redundant except0 under the outer except0 of fupd
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

/-! ## Properties -/

omit [FiniteMapLaws Positive M] in
/-- `inv N P` is persistent.

    Coq: `inv_persistent` -/
theorem inv_persistent {W : WsatGS GF}
    (N : Namespace) (P : IProp GF) :
    inv (GF := GF) (M := M) (F := F) W N P ⊢
      BIBase.persistently (inv (GF := GF) (M := M) (F := F) W N P) := by
  simpa [inv] using
    (persistently_idem_2 (PROP := IProp GF)
      (P := BIBase.forall fun E : Iris.Set Positive =>
        BIBase.imp (BIBase.pure (Subset (nclose N).mem E))
          (uPred_fupd (M := M) (F := F) W E (maskDiff E N)
            (BIBase.sep (BIBase.later P)
              (BIBase.wand (BIBase.later P)
                (uPred_fupd (M := M) (F := F) W (maskDiff E N) E
                  (BIBase.pure True)))))))

instance inv_persistent_inst {W : WsatGS GF} (N : Namespace) (P : IProp GF) :
    Persistent (inv (GF := GF) (M := M) (F := F) W N P) :=
  ⟨inv_persistent (W := W) (N := N) (P := P)⟩

omit [FiniteMapLaws Positive M] in
/-- Non-expansive core of `inv` over a latered parameter. -/
private theorem invBody_ne {W : WsatGS GF} (N : Namespace) :
    OFE.NonExpansive (invBody (GF := GF) (M := M) (F := F) W N) := by
  -- Push non-expansiveness through persistently, forall, imp, and fupd.
  refine ⟨?_⟩
  intro n X Y hXY
  unfold invBody
  refine (persistently_ne.ne ?_)
  refine forall_ne ?_
  intro E
  refine (imp_ne.ne .rfl ?_)
  have hwand :
      BIBase.wand X (uPred_fupd (M := M) (F := F) W (maskDiff E N) E
        (BIBase.pure True)) ≡{n}≡
      BIBase.wand Y (uPred_fupd (M := M) (F := F) W (maskDiff E N) E
        (BIBase.pure True)) :=
    (wand_ne.ne hXY .rfl)
  have hsep : BIBase.sep X (BIBase.wand X
      (uPred_fupd (M := M) (F := F) W (maskDiff E N) E
        (BIBase.pure True))) ≡{n}≡
      BIBase.sep Y (BIBase.wand Y
        (uPred_fupd (M := M) (F := F) W (maskDiff E N) E
          (BIBase.pure True))) :=
    (sep_ne.ne hXY hwand)
  exact (uPred_fupd_ne (W := W) (E1 := E) (E2 := maskDiff E N)).ne hsep

/-- `inv N` is contractive in its body. -/
instance inv_contractive {W : WsatGS GF} (N : Namespace) :
    OFE.Contractive (fun P => inv (GF := GF) (M := M) (F := F) W N P) := by
  -- `inv` is `invBody` applied to the contractive `later`.
  refine ⟨?_⟩
  intro n P Q hPQ
  have hlater :
      BIBase.later P ≡{n}≡ BIBase.later Q :=
    (OFE.Contractive.distLater_dist
      (f := BIBase.later (PROP := IProp GF)) hPQ)
  simpa [inv, invBody] using
    (invBody_ne (GF := GF) (M := M) (F := F) (N := N) (W := W)).ne hlater

/-- `inv N` is non-expansive in its body. -/
instance inv_ne {W : WsatGS GF} (N : Namespace) :
    OFE.NonExpansive (fun P => inv (GF := GF) (M := M) (F := F) W N P) := by
  -- contractive functions are non-expansive
  infer_instance

omit [FiniteMapLaws Positive M] in
/-- `inv` respects equivalence of its body. -/
theorem inv_proper {W : WsatGS GF} (N : Namespace) {P Q : IProp GF}
    (h : P ≡ Q) : inv (GF := GF) (M := M) (F := F) W N P ≡
      inv (GF := GF) (M := M) (F := F) W N Q := by
  -- non-expansiveness preserves equivalence
  exact OFE.NonExpansive.eqv (f := fun P => inv (GF := GF) (M := M) (F := F) W N P) h

/-! ## Allocation -/

/-- Allocate a new invariant from `▷ P`.

    Proof strategy: use `ownI_alloc` from wsat to get a fresh invariant name
    in `↑N`, then pack behind `□` to form `inv N P`.

    Coq: `inv_alloc` -/
theorem inv_alloc {W : WsatGS GF}
    (N : Namespace) (E : Iris.Set Positive) (P : IProp GF)
    (hfresh : ∀ E : GSet, ∃ i, ¬E.mem i ∧ (nclose N).mem i) :
    BIBase.later P ⊢
      uPred_fupd (M := M) (F := F) W E E
        (inv (GF := GF) (M := M) (F := F) W N P) := by
  classical
  unfold uPred_fupd
  iintro HP
  iintro H
  icases H with ⟨Hwsat, HownE⟩
  -- allocate a fresh invariant name under `↑N`
  ihave Halloc :=
    (wrapEntails (GF := GF)
      (ownI_alloc (GF := GF) (M := M) (F := F) (W := W)
        (φ := fun i => (nclose N).mem i) (P := P) hfresh)) $$ [Hwsat, HP]
  · -- build the premise `wsat ∗ ▷ P`
    isplitl [Hwsat]
    · iexact Hwsat
    · iexact HP
  -- map the update result into the invariant and add except-0
  have hmono :
      BIBase.sep (ownE W (mask E)) (BIBase.exists fun i =>
        BIBase.sep (BIBase.pure ((nclose N).mem i))
          (BIBase.sep (wsat (GF := GF) (M := M) (F := F) W)
            (ownI (GF := GF) (M := M) (F := F) W i P))) ⊢
      BIBase.except0 (BIBase.sep (wsat (GF := GF) (M := M) (F := F) W)
        (BIBase.sep (ownE W (mask E))
          (inv (GF := GF) (M := M) (F := F) W N P))) := by
    -- pull the existential out of the sep, then build the postcondition
    refine (sep_exists_l (P := ownE W (mask E))
      (Ψ := fun i =>
        BIBase.sep (BIBase.pure ((nclose N).mem i))
          (BIBase.sep (wsat (GF := GF) (M := M) (F := F) W)
            (ownI (GF := GF) (M := M) (F := F) W i P)))).1.trans ?_
    refine exists_elim ?_
    intro i
    iintro Hres
    icases Hres with ⟨HownE', Hrest⟩
    icases Hrest with ⟨Hmem, Hrest⟩
    icases Hmem with %Hmem
    icases Hrest with ⟨Hwsat', HownI⟩
    -- assemble the postcondition, building `inv` from `own_inv`
    iapply (wrapEntails (GF := GF) (except0_intro (P := _)))
    isplitl [Hwsat']
    · iexact Hwsat'
    · isplitl [HownE']
      · iexact HownE'
      · -- derive `inv` from the internal ownership witness
        iapply (wrapEntails (GF := GF)
          (own_inv_to_inv (W := W) (N := N) (P := P)))
        unfold own_inv
        iexists i
        isplit
        · ipure_intro
          exact Hmem
        · iexact HownI
  -- frame `ownE` through the update and apply monotonicity
  iapply (wrapEntails (GF := GF)
    (BIUpdate.mono
      (P := BIBase.sep (ownE W (mask E)) (BIBase.exists fun i =>
        BIBase.sep (BIBase.pure ((nclose N).mem i))
          (BIBase.sep (wsat (GF := GF) (M := M) (F := F) W)
            (ownI (GF := GF) (M := M) (F := F) W i P))))
      (Q := BIBase.except0 <|
        BIBase.sep (wsat (GF := GF) (M := M) (F := F) W)
          (BIBase.sep (ownE W (mask E))
            (inv (GF := GF) (M := M) (F := F) W N P)))
      hmono))
  iapply (wrapEntails (GF := GF)
    (bupd_frame_l (P := ownE W (mask E))
      (Q := BIBase.exists fun i =>
        BIBase.sep (BIBase.pure ((nclose N).mem i))
          (BIBase.sep (wsat (GF := GF) (M := M) (F := F) W)
            (ownI (GF := GF) (M := M) (F := F) W i P)))))
  isplitl [HownE]
  · iexact HownE
  · iexact Halloc

/-- Allocate an invariant and immediately open it.

    Coq: `inv_alloc_open` -/
theorem inv_alloc_open {W : WsatGS GF}
    (N : Namespace) (E : Iris.Set Positive) (P : IProp GF)
    (h : Subset (nclose N).mem E)
    (hfresh : ∀ E : GSet, ∃ i, ¬E.mem i ∧ (nclose N).mem i) :
    (BIBase.emp : IProp GF) ⊢
      uPred_fupd (M := M) (F := F) W E (maskDiff E N)
        (BIBase.sep (inv (GF := GF) (M := M) (F := F) W N P)
          (BIBase.wand (BIBase.later P)
            (uPred_fupd (M := M) (F := F) W (maskDiff E N) E
              (BIBase.pure True)))) := by
  classical
  unfold uPred_fupd
  iintro Hemp
  iintro H
  icases H with ⟨Hwsat, HownE⟩
  ihave HwsatB :=
    (wrapEntails (GF := GF)
      (BIUpdate.intro (P := wsat (GF := GF) (M := M) (F := F) W))) $$ Hwsat
  -- allocate and immediately open an invariant in `↑N`
  ihave Halloc :=
    (wrapEntails (GF := GF)
      (ownI_alloc_open (GF := GF) (M := M) (F := F) (W := W)
        (φ := fun i => (nclose N).mem i) (P := P) hfresh)) $$ HwsatB
  ihave Halloc' :=
    (wrapEntails (GF := GF)
      (bupd_frame_l (P := ownE W (mask E))
        (Q := BIBase.exists fun i =>
          BIBase.sep (BIBase.pure ((nclose N).mem i))
            (BIBase.sep
              (BIBase.wand (ownE W (CoPset.singleton i))
                (wsat (GF := GF) (M := M) (F := F) W))
              (BIBase.sep (ownI (GF := GF) (M := M) (F := F) W i P)
                (ownD W (GSet.singleton i))))))) $$ [HownE, Halloc]
  · isplitl [HownE]
    · iexact HownE
    · iexact Halloc
  have hmono_wand :
      (BIBase.emp : IProp GF) ⊢
        iprop((ownE W (mask E) ∗
          BIBase.exists fun i =>
            BIBase.sep (BIBase.pure ((nclose N).mem i))
              (BIBase.sep
                (BIBase.wand (ownE W (CoPset.singleton i))
                  (wsat (GF := GF) (M := M) (F := F) W))
                (BIBase.sep (ownI (GF := GF) (M := M) (F := F) W i P)
                  (ownD W (GSet.singleton i))))) -∗
          BIBase.except0
            (BIBase.sep (wsat (GF := GF) (M := M) (F := F) W)
              (BIBase.sep (ownE W (mask (maskDiff E N)))
                (BIBase.sep (inv (GF := GF) (M := M) (F := F) W N P)
                  (BIBase.wand (BIBase.later P)
                    (uPred_fupd (M := M) (F := F) W (maskDiff E N) E
                      (BIBase.pure True))))))) := by
    iintro -
    iintro Hres
    icases Hres with ⟨HownE, Halloc⟩
    icases Halloc with ⟨%i, Halloc⟩
    icases Halloc with ⟨Hmem, Halloc⟩
    icases Hmem with %Hmem
    icases Halloc with ⟨HopenW, Halloc⟩
    icases Halloc with ⟨HownI', HownD⟩
    icases HownI' with #HownI'
    -- split `ownE E` into `ownE {i}`, `ownE (↑N \ {i})`, and `ownE (E \ ↑N)`
    have hmask : mask E = (nclose N) ∪ mask (maskDiff E N) := by
      ext x; constructor
      · intro hx
        by_cases hxN : (nclose N).mem x
        · exact Or.inl hxN
        · exact Or.inr ⟨hx, hxN⟩
      · intro hx
        cases hx with
        | inl hxN => exact h _ hxN
        | inr hxDiff => exact hxDiff.1
    have hdisj : CoPset.Disjoint (nclose N) (mask (maskDiff E N)) := by
      intro x hx
      exact hx.2.2 hx.1
    let rest : CoPset := nclose N \ CoPset.singleton i
    have hmaskN : (nclose N) = (CoPset.singleton i) ∪ rest := by
      ext x; constructor
      · intro hxN
        by_cases hx : x = i
        · left; simpa [CoPset.mem_singleton] using hx
        · right; exact ⟨hxN, by simpa [CoPset.mem_singleton, rest] using hx⟩
      · intro hx
        cases hx with
        | inl hx =>
            have hx' : x = i := by simpa [CoPset.mem_singleton] using hx
            subst hx'
            exact Hmem
        | inr hx => exact hx.1
    have hdisjN : CoPset.Disjoint (CoPset.singleton i) rest := by
      intro x hx
      exact hx.2.2 hx.1
    have hsplit :
        ownE W (mask E) ⊢
          BIBase.sep (ownE W (nclose N)) (ownE W (mask (maskDiff E N))) := by
      -- rewrite the mask to the disjoint union and apply `ownE_op`
      rw [hmask]
      exact (ownE_op (W := W) (E₁ := nclose N) (E₂ := mask (maskDiff E N)) hdisj).1
    ihave Hsplit := (wrapEntails (GF := GF) hsplit) $$ HownE
    icases Hsplit with ⟨HownEN, HownEdiff⟩
    have hsplitN :
        ownE W (nclose N) ⊢
          BIBase.sep (ownE W (CoPset.singleton i)) (ownE W rest) := by
      -- rewrite the namespace to the singleton union and apply `ownE_op`
      rw [hmaskN]
      exact (ownE_op (W := W) (E₁ := CoPset.singleton i) (E₂ := rest) hdisjN).1
    ihave HsplitN := (wrapEntails (GF := GF) hsplitN) $$ HownEN
    icases HsplitN with ⟨HownEi, HownErest⟩
    -- open the invariant using the allocated opener
    ihave Hwsat' := HopenW $$ HownEi
    -- build the result
    iapply (wrapEntails (GF := GF) (except0_intro (P := _)))
    isplitl [Hwsat']
    · iexact Hwsat'
    · isplitl [HownEdiff]
      · iexact HownEdiff
      · -- package `inv` and the closing wand
        isplitl []
        · -- `inv` from `own_inv`
          iapply (wrapEntails (GF := GF) (own_inv_to_inv (W := W) (N := N) (P := P)))
          unfold own_inv
          iexists i
          isplit
          · ipure_intro
            exact Hmem
          · iexact HownI'
        · iintro HP
          unfold uPred_fupd
          iintro Hclose
          icases Hclose with ⟨Hwsat2, HownEdiff2⟩
          ihave Hclose' :=
            (wrapEntails (GF := GF)
              (ownI_close (W := W) (M := M) (F := F) i P)) $$ [Hwsat2, HownI', HP, HownD]
          · -- build the premise `((wsat ∗ ownI) ∗ ▷ P) ∗ ownD`
            isplitl [Hwsat2 HP]
            · isplitl [Hwsat2]
              · isplitl [Hwsat2]
                · iexact Hwsat2
                · iexact HownI'
              · iexact HP
            · iexact HownD
          icases Hclose' with ⟨Hwsat3, HownEi'⟩
          have hjoinN :
              BIBase.sep (ownE W (CoPset.singleton i)) (ownE W rest) ⊢
              ownE W (nclose N) := by
            -- rewrite the namespace to the singleton union and apply `ownE_op`
            rw [hmaskN]
            exact (ownE_op (W := W) (E₁ := CoPset.singleton i) (E₂ := rest) hdisjN).2
          ihave HjoinN := (wrapEntails (GF := GF) hjoinN) $$ [HownEi', HownErest]
          · -- assemble the singleton/rest split
            isplitl [HownEi']
            · iexact HownEi'
            · iexact HownErest
          have hjoin :
              BIBase.sep (ownE W (nclose N)) (ownE W (mask (maskDiff E N))) ⊢
              ownE W (mask E) := by
            -- rewrite the mask to the disjoint union and apply `ownE_op`
            rw [hmask]
            exact (ownE_op (W := W) (E₁ := nclose N)
              (E₂ := mask (maskDiff E N)) hdisj).2
          ihave Hjoin := (wrapEntails (GF := GF) hjoin) $$ [HjoinN, HownEdiff2]
          · -- rejoin `↑N` with the remaining mask
            isplitl [HjoinN]
            · iexact HjoinN
            · iexact HownEdiff2
          iapply BIUpdate.intro
          iapply (wrapEntails (GF := GF) (except0_intro (P := _)))
          isplitl [Hwsat3]
          · iexact Hwsat3
          · isplitl [Hjoin]
            · iexact Hjoin
            · ipure_intro
              exact True.intro
  have hmono :
      BIBase.sep (ownE W (mask E))
        (BIBase.exists fun i =>
          BIBase.sep (BIBase.pure ((nclose N).mem i))
            (BIBase.sep
              (BIBase.wand (ownE W (CoPset.singleton i))
                (wsat (GF := GF) (M := M) (F := F) W))
              (BIBase.sep (ownI (GF := GF) (M := M) (F := F) W i P)
                (ownD W (GSet.singleton i))))) ⊢
      BIBase.except0
        (BIBase.sep (wsat (GF := GF) (M := M) (F := F) W)
          (BIBase.sep (ownE W (mask (maskDiff E N)))
            (BIBase.sep (inv (GF := GF) (M := M) (F := F) W N P)
              (BIBase.wand (BIBase.later P)
                (uPred_fupd (M := M) (F := F) W (maskDiff E N) E
                  (BIBase.pure True)))))) := by
    -- move the wand proof under a sep and eliminate it
    refine (sep_emp (P := BIBase.sep (ownE W (mask E))
      (BIBase.exists fun i =>
        BIBase.sep (BIBase.pure ((nclose N).mem i))
          (BIBase.sep
            (BIBase.wand (ownE W (CoPset.singleton i))
              (wsat (GF := GF) (M := M) (F := F) W))
            (BIBase.sep (ownI (GF := GF) (M := M) (F := F) W i P)
              (ownD W (GSet.singleton i))))))).2.trans ?_
    refine (sep_mono .rfl hmono_wand).trans ?_
    exact wand_elim_r
  have hmono' := by
    -- unfold the nested fupd to match the goal after `unfold uPred_fupd`
    simpa [uPred_fupd, wsat'] using hmono
  iapply (wrapEntails (GF := GF) (BIUpdate.mono hmono'))
  iexact Halloc'

/-! ## Access -/

omit [FiniteMapLaws Positive M] in
/-- Open an invariant: given `↑N ⊆ E`, access `▷ P` with a closing view shift.

    Proof strategy: unfold `inv` definition, apply the universally quantified
    body to `E` with the subset proof.

    Coq: `inv_acc` -/
theorem inv_acc {W : WsatGS GF}
    (E : Iris.Set Positive) (N : Namespace) (P : IProp GF)
    (h : Subset (nclose N).mem E) :
    inv (GF := GF) (M := M) (F := F) W N P ⊢
      uPred_fupd (M := M) (F := F) W E (maskDiff E N)
        (BIBase.sep (BIBase.later P)
          (BIBase.wand (BIBase.later P)
            (uPred_fupd (M := M) (F := F) W (maskDiff E N) E
              (BIBase.pure True)))) := by
  have hwand :
      (BIBase.emp : IProp GF) ⊢
        iprop((inv (GF := GF) (M := M) (F := F) W N P) -∗
          (uPred_fupd (M := M) (F := F) W E (maskDiff E N)
            (BIBase.sep (BIBase.later P)
              (BIBase.wand (BIBase.later P)
                (uPred_fupd (M := M) (F := F) W (maskDiff E N) E
                  (BIBase.pure True)))))) := by
    unfold inv
    iintro -
    iintro Hinv
    iapply Hinv $$ %E
    ipure_intro
    exact h
  -- eliminate the wand using `emp` framing
  refine (sep_emp (P := inv (GF := GF) (M := M) (F := F) W N P)).2.trans ?_
  refine (sep_mono .rfl hwand).trans ?_
  exact wand_elim_r

omit [FiniteMapLaws Positive M] in
/-- Access a timeless invariant: strip the `▷` when `P` is timeless.

    Coq: `inv_acc_timeless` -/
theorem inv_acc_timeless {W : WsatGS GF}
    (E : Iris.Set Positive) (N : Namespace) (P : IProp GF)
    (h : Subset (nclose N).mem E)
    (htimeless : (BIBase.later P : IProp GF) ⊢
      BIBase.or (BIBase.later (BIBase.pure False)) P) :
    inv (GF := GF) (M := M) (F := F) W N P ⊢
      uPred_fupd (M := M) (F := F) W E (maskDiff E N)
        (BIBase.sep P
          (BIBase.wand P
            (uPred_fupd (M := M) (F := F) W (maskDiff E N) E
              (BIBase.pure True)))) := by
  -- first open the invariant, then use timelessness to drop the later
  have hclose :
      BIBase.wand (BIBase.later P)
        (uPred_fupd (M := M) (F := F) W (maskDiff E N) E (BIBase.pure True)) ⊢
      BIBase.wand P
        (uPred_fupd (M := M) (F := F) W (maskDiff E N) E (BIBase.pure True) : IProp GF) :=
    wand_mono (later_intro (P := P)) .rfl
  have hpost :
      BIBase.sep (BIBase.later P)
        (BIBase.wand (BIBase.later P)
          (uPred_fupd (M := M) (F := F) W (maskDiff E N) E (BIBase.pure True))) ⊢
      BIBase.sep (BIBase.except0 P)
        (BIBase.wand P
          (uPred_fupd (M := M) (F := F) W (maskDiff E N) E (BIBase.pure True)) : IProp GF) :=
    sep_mono htimeless hclose
  refine (inv_acc (W := W) (E := E) (N := N) (P := P) h).trans ?_
  -- replace `▷ P` by `◇ P` in the postcondition
  have hmono :=
    fupd_mono (W := W) (M := M) (F := F) (E1 := E) (E2 := maskDiff E N)
      (P := _ ) (Q := _ ) hpost
  -- drop the redundant `◇` under the outer except-0
  exact hmono.trans (fupd_drop_except0_post (W := W) (M := M) (F := F)
    (E1 := E) (E2 := maskDiff E N) (P := P)
    (Q := BIBase.wand P
      (uPred_fupd (M := M) (F := F) W (maskDiff E N) E (BIBase.pure True))))

/-! ## Derived Properties -/

omit [FiniteMapLaws Positive M] in
private theorem maskDiff_self (N : Namespace) :
    maskDiff (nclose N).mem N = (fun _ => False) := by
  -- membership is contradictory for the same namespace
  funext i; simp [maskDiff]

omit [FiniteMapLaws Positive M] in
private theorem mask_union_diff (N : Namespace) (E : Iris.Set Positive)
    (h : Subset (nclose N).mem E) :
    (fun x => (nclose N).mem x ∨ maskDiff E N x) = E := by
  -- split on whether `x` is in the namespace
  funext i; apply propext; constructor
  · intro hx; cases hx with
    | inl hN => exact h _ hN
    | inr hdiff => exact hdiff.1
  · intro hE; by_cases hN : (nclose N).mem i
    · exact Or.inl hN
    · exact Or.inr ⟨hE, hN⟩

/-! ### Mask Helpers -/

/- A two-namespace mask difference. -/
private abbrev maskDiff2 (E : Iris.Set Positive) (N1 N2 : Namespace) :
    Iris.Set Positive :=
  -- drop both namespaces from the mask
  fun x => E x ∧ ¬(nclose N1).mem x ∧ ¬(nclose N2).mem x

omit [FiniteMapLaws Positive M] in
private theorem maskDiff2_eq (E : Iris.Set Positive) (N1 N2 : Namespace) :
    maskDiff (maskDiff E N1) N2 = maskDiff2 E N1 N2 := by
  -- unfold nested differences and reassociate
  funext i; simp [maskDiff, maskDiff2, and_assoc]

omit [FiniteMapLaws Positive M] in
private theorem maskDiff2_subset_of_union (E : Iris.Set Positive)
    (N1 N2 N : Namespace)
    (hsubset : Subset (fun x => (nclose N1).mem x ∨ (nclose N2).mem x) (nclose N).mem) :
    Subset (maskDiff E N) (maskDiff2 E N1 N2) := by
  -- use the union subset to exclude both namespaces
  intro i hi
  have hN1 : ¬(nclose N1).mem i := by
    intro hN1; exact hi.2 (hsubset _ (Or.inl hN1))
  have hN2 : ¬(nclose N2).mem i := by
    intro hN2; exact hi.2 (hsubset _ (Or.inr hN2))
  exact ⟨hi.1, hN1, hN2⟩

omit [FiniteMapLaws Positive M] in
private theorem nclose_subset_maskDiff (E : Iris.Set Positive)
    (N1 N2 : Namespace)
    (hdisj : CoPset.Disjoint (nclose N1) (nclose N2))
    (hE : Subset (nclose N2).mem E) :
    Subset (nclose N2).mem (maskDiff E N1) := by
  -- keep `N2` inside the mask while excluding `N1`
  intro i hi
  have hN1 : ¬(nclose N1).mem i := by
    intro hN1; exact (hdisj i) ⟨hN1, hi⟩
  exact ⟨hE _ hi, hN1⟩

omit [FiniteMapLaws Positive M] in
private theorem fupd_from_split' {W : WsatGS GF}
    (E1 E2 : Iris.Set Positive) (E3 : CoPset)
    (hE : mask E1 = mask E2 ∪ E3) (hdisj : CoPset.Disjoint (mask E2) E3)
    (P : IProp GF) :
    BIBase.sep (ownE W E3) P ⊢ uPred_fupd (M := M) (F := F) W E2 E1 P := by
  -- reassemble the mask, then wrap with except-0 and bupd
  unfold uPred_fupd
  refine wand_intro ?_
  refine (sep_comm (P := BIBase.sep (ownE W E3) P)
    (Q := BIBase.sep (wsat' (M := M) (F := F) W) (ownE W (mask E2)))).1.trans ?_
  refine (sep_assoc (P := wsat' (M := M) (F := F) W) (Q := ownE W (mask E2))
    (R := BIBase.sep (ownE W E3) P)).1.trans ?_
  refine (sep_mono .rfl
    (sep_assoc (P := ownE W (mask E2)) (Q := ownE W E3) (R := P)).2).trans ?_
  have hown : BIBase.sep (ownE W (mask E2)) (ownE W E3) ⊢ ownE W (mask E1) := by
    -- collapse the split mask back to `E1`
    simpa [hE] using (ownE_op (W := W) (E₁ := mask E2) (E₂ := E3) hdisj).2
  refine (sep_mono .rfl (sep_mono hown .rfl)).trans ?_
  exact (except0_intro).trans BIUpdate.intro

omit [FiniteMapLaws Positive M] in
private theorem fupd_mask_intro {W : WsatGS GF}
    (E1 E2 : Iris.Set Positive) (h : Subset E2 E1) (P : IProp GF) :
    BIBase.wand (uPred_fupd (M := M) (F := F) W E2 E1 (BIBase.emp : IProp GF)) P ⊢
      uPred_fupd (M := M) (F := F) W E1 E2 P := by
  -- split `E1` into `E2` plus the disjoint remainder, then apply the wand
  rcases CoPset.subseteq_disjoint_union (s₁ := mask E2) (s₂ := mask E1) h with
    ⟨E3, hE, hdisj⟩
  let Hwand : IProp GF :=
    BIBase.wand (uPred_fupd (M := M) (F := F) W E2 E1 (BIBase.emp : IProp GF)) P
  have hsplit : ownE W (mask E1) ⊢ BIBase.sep (ownE W (mask E2)) (ownE W E3) := by
    -- expose the split mask via `ownE_op`
    simpa [hE] using (ownE_op (W := W) (E₁ := mask E2) (E₂ := E3) hdisj).1
  have hwand :
      BIBase.sep (ownE W E3) Hwand ⊢ P := by
    -- build the closing fupd from `ownE E3`, then eliminate the wand
    have hfupd :
        BIBase.sep (ownE W E3) (BIBase.emp : IProp GF) ⊢
          uPred_fupd (M := M) (F := F) W E2 E1 (BIBase.emp : IProp GF) :=
      fupd_from_split' (W := W) (E1 := E1) (E2 := E2) (E3 := E3) hE hdisj
        (P := (BIBase.emp : IProp GF))
    refine (sep_mono (sep_emp (P := ownE W E3)).2 .rfl).trans ?_
    refine (sep_mono hfupd .rfl).trans ?_
    exact wand_elim_r
  unfold uPred_fupd
  refine wand_intro ?_
  refine (sep_comm (P := Hwand) (Q := BIBase.sep (wsat' (M := M) (F := F) W)
    (ownE W (mask E1)))).1.trans ?_
  refine (sep_assoc (P := wsat' (M := M) (F := F) W) (Q := ownE W (mask E1))
    (R := Hwand)).1.trans ?_
  refine (sep_mono .rfl (sep_mono hsplit .rfl)).trans ?_
  refine (sep_mono .rfl
    (sep_assoc (P := ownE W (mask E2)) (Q := ownE W E3)
      (R := Hwand)).1).trans ?_
  refine (sep_assoc (P := wsat' (M := M) (F := F) W) (Q := ownE W (mask E2))
    (R := BIBase.sep (ownE W E3) Hwand)).2.trans ?_
  -- introduce the bupd and the except-0 wrapper
  have hupd :
      BIBase.sep (BIBase.sep (wsat' (M := M) (F := F) W) (ownE W (mask E2))) P ⊢
        BUpd.bupd (BIBase.except0 (BIBase.sep (wsat' (M := M) (F := F) W)
          (BIBase.sep (ownE W (mask E2)) P))) := by
    -- reassociate, then use `bupd` intro and monotonicity for `except0`
    refine (sep_assoc (P := wsat' (M := M) (F := F) W) (Q := ownE W (mask E2)) (R := P)).1.trans ?_
    exact (BIUpdate.intro (P := BIBase.sep (wsat' (M := M) (F := F) W)
      (BIBase.sep (ownE W (mask E2)) P))).trans
        (BIUpdate.mono (PROP := IProp GF)
          (except0_intro (P := BIBase.sep (wsat' (M := M) (F := F) W)
            (BIBase.sep (ownE W (mask E2)) P))))
  exact (sep_mono .rfl hwand).trans hupd

omit [FiniteMapLaws Positive M] in
private theorem fupd_wand_r {W : WsatGS GF}
    (E1 E2 : Iris.Set Positive) (P Q : IProp GF) :
    BIBase.sep (uPred_fupd (M := M) (F := F) W E1 E2 P) (BIBase.wand P Q) ⊢
      uPred_fupd (M := M) (F := F) W E1 E2 Q := by
  -- frame the wand through the update, then eliminate it
  iintro H
  iapply (wrapEntails (GF := GF)
    (fupd_mono (W := W) (E1 := E1) (E2 := E2)
      (P := BIBase.sep P (BIBase.wand P Q)) (Q := Q) (wand_elim_r (P := P) (Q := Q))))
  iapply (wrapEntails (GF := GF)
    (fupd_frame_r (W := W) (M := M) (F := F) (E1 := E1) (E2 := E2)
      (P := P) (Q := BIBase.wand P Q)))
  iexact H

omit [FiniteMapLaws Positive M] in
private theorem maskDiff_union_right (E : Iris.Set Positive) (N : Namespace) :
    (fun x => maskDiff (nclose N).mem N x ∨ maskDiff E N x) = maskDiff E N := by
  -- the left disjunct is always false
  funext i; simp [maskDiff]

omit [FiniteMapLaws Positive M] in
private theorem inv_close_strong {W : WsatGS GF}
    (N : Namespace) (P : IProp GF) :
    BIBase.wand (BIBase.later P)
      (uPred_fupd (M := M) (F := F) W
        (maskDiff (nclose N).mem N) (nclose N).mem (BIBase.pure True)) ⊢
      BIBase.forall fun E' : Iris.Set Positive =>
        BIBase.wand (BIBase.later P)
          (uPred_fupd (M := M) (F := F) W E'
            (fun x => (nclose N).mem x ∨ E' x) (BIBase.pure True)) := by
  classical
  iintro Hclose
  iintro %E'
  iintro HP
  -- apply the original close shift and frame the extra mask
  have hdisj : CoPset.Disjoint (mask (fun _ => False)) (mask E') := by
    intro i hi; exact hi.1
  have hframe :
      BIBase.wand (BIBase.later P)
          (uPred_fupd (M := M) (F := F) W (maskDiff (nclose N).mem N)
            (nclose N).mem (BIBase.pure True)) ⊢
        BIBase.wand (BIBase.later P)
          (uPred_fupd (M := M) (F := F) W E'
            (fun x => (nclose N).mem x ∨ E' x) (BIBase.pure True)) := by
    refine wand_mono_r ?_
    have hframe' :
        uPred_fupd (M := M) (F := F) W (fun _ => False) (nclose N).mem (BIBase.pure True) ⊢
          uPred_fupd (M := M) (F := F) W
            (fun x => False ∨ E' x) (fun x => (nclose N).mem x ∨ E' x) (BIBase.pure True) :=
      fupd_mask_frame_r (M := M) (F := F) (W := W) (E1 := fun _ => False)
        (E2 := (nclose N).mem) (Ef := E') (P := BIBase.pure True) hdisj
    have hfalse : (fun x => False ∨ E' x) = E' := by
      funext i; simp
    simpa [maskDiff_self (N := N), hfalse] using hframe'
  ihave Hclose' := (wrapEntails (GF := GF) hframe) $$ Hclose
  ispecialize Hclose' $$ HP
  iexact Hclose'

/-! ### Combination and Splitting -/

omit [FiniteMapLaws Positive M]
  [ElemG GF (COFE.constOF CoPsetDisj)] [ElemG GF (COFE.constOF GSetDisj)] in
private theorem later_dup (P : IProp GF) :
    BIBase.persistently (BIBase.wand P (BIBase.sep P P)) ⊢
      BIBase.wand (BIBase.later P) (BIBase.sep (BIBase.later P) (BIBase.later P)) := by
  -- duplicate a latered proposition using the persistent duplicator
  iintro Hdup
  iintro HP
  ihave Hdup' :=
    (wrapEntails (GF := GF)
      (intuitionistically_elim (P := BIBase.wand P (BIBase.sep P P)))) $$ Hdup
  ihave Hlater :=
    (wrapEntails (GF := GF)
      (later_intro (P := BIBase.wand P (BIBase.sep P P)))) $$ Hdup'
  ihave Hwand :=
    (wrapEntails (GF := GF)
      (later_wand (P := P) (Q := BIBase.sep P P))) $$ Hlater
  ispecialize Hwand $$ HP
  ihave Hsplit := (wrapEntails (GF := GF)
    (later_sep (P := P) (Q := P)).1) $$ Hwand
  iexact Hsplit

omit [FiniteMapLaws Positive M]
  [ElemG GF (COFE.constOF CoPsetDisj)] [ElemG GF (COFE.constOF GSetDisj)] in
private theorem inv_split_l_transform (P Q : IProp GF) :
    (BIBase.emp : IProp GF) ⊢
      BIBase.later (BIBase.intuitionistically
        (BIBase.wand (BIBase.sep (PROP := IProp GF) P Q)
          (BIBase.sep P (BIBase.wand P (BIBase.sep (PROP := IProp GF) P Q))))) := by
  -- build the latered, persistent split/merge witness
  have hwand :
      (BIBase.emp : IProp GF) ⊢
        BIBase.wand (BIBase.sep (PROP := IProp GF) P Q)
          (BIBase.sep P (BIBase.wand P (BIBase.sep (PROP := IProp GF) P Q))) := by
    iintro _
    iintro HPQ
    icases HPQ with ⟨HP, HQ⟩
    isplitl [HP]
    · iexact HP
    · iintro HP'
      isplitl [HP']
      · iexact HP'
      · iexact HQ
  have hbox :
      BIBase.intuitionistically (BIBase.emp : IProp GF) ⊢
        BIBase.wand (BIBase.sep (PROP := IProp GF) P Q)
          (BIBase.sep P (BIBase.wand P (BIBase.sep (PROP := IProp GF) P Q))) :=
    (intuitionistically_elim (P := (BIBase.emp : IProp GF))).trans hwand
  have hboxed :
      BIBase.intuitionistically (BIBase.emp : IProp GF) ⊢
        BIBase.intuitionistically
          (BIBase.wand (BIBase.sep (PROP := IProp GF) P Q)
            (BIBase.sep P (BIBase.wand P (BIBase.sep (PROP := IProp GF) P Q)))) :=
    intuitionistically_intro' hbox
  have hemp :
      (BIBase.emp : IProp GF) ⊢
        BIBase.intuitionistically (BIBase.emp : IProp GF) :=
    (intuitionistically_emp (PROP := IProp GF)).2
  exact (hemp.trans hboxed).trans (later_intro (P := _))

omit [FiniteMapLaws Positive M] in
private theorem inv_acc_strong_frame {W : WsatGS GF}
    (E : Iris.Set Positive) (N : Namespace) (P : IProp GF)
    (h : Subset (nclose N).mem E) :
    uPred_fupd (M := M) (F := F) W (nclose N).mem
        (maskDiff (nclose N).mem N)
        (BIBase.sep (BIBase.later P)
          (BIBase.wand (BIBase.later P)
            (uPred_fupd (M := M) (F := F) W (maskDiff (nclose N).mem N)
              (nclose N).mem (BIBase.pure True)))) ⊢
      uPred_fupd (M := M) (F := F) W E (maskDiff E N)
        (BIBase.sep (BIBase.later P)
          (BIBase.wand (BIBase.later P)
            (uPred_fupd (M := M) (F := F) W (maskDiff (nclose N).mem N)
              (nclose N).mem (BIBase.pure True)))) := by
  -- rewrite mask unions and apply `fupd_mask_frame_r`
  have hdisj :
      CoPset.Disjoint (mask (nclose N).mem) (mask (maskDiff E N)) := by
    intro i hi; exact hi.2.2 hi.1
  simpa [mask_union_diff (N := N) (E := E) h, maskDiff_union_right (E := E) (N := N),
    maskDiff_self (N := N)] using
    (fupd_mask_frame_r (W := W) (E1 := (nclose N).mem)
      (E2 := maskDiff (nclose N).mem N) (Ef := maskDiff E N)
      (P := BIBase.sep (BIBase.later P)
        (BIBase.wand (BIBase.later P)
          (uPred_fupd (M := M) (F := F) W (maskDiff (nclose N).mem N)
            (nclose N).mem (BIBase.pure True))))
      hdisj)

omit [FiniteMapLaws Positive M] in
private theorem inv_acc_strong_post {W : WsatGS GF}
    (N : Namespace) (P : IProp GF) :
    BIBase.sep (BIBase.later P)
        (BIBase.wand (BIBase.later P)
          (uPred_fupd (M := M) (F := F) W (maskDiff (nclose N).mem N)
            (nclose N).mem (BIBase.pure True))) ⊢
      BIBase.sep (BIBase.later P)
        (BIBase.forall fun E' : Iris.Set Positive =>
          BIBase.wand (BIBase.later P)
            (uPred_fupd (M := M) (F := F) W E'
              (fun x => (nclose N).mem x ∨ E' x) (BIBase.pure True))) := by
  -- keep the later and strengthen the closing wand
  exact sep_mono .rfl (inv_close_strong (W := W) (N := N) (P := P))

omit [FiniteMapLaws Positive M] in
private theorem inv_acc_strong_mono {W : WsatGS GF}
    (E : Iris.Set Positive) (N : Namespace) (P : IProp GF) :
    uPred_fupd (M := M) (F := F) W E (maskDiff E N)
        (BIBase.sep (BIBase.later P)
          (BIBase.wand (BIBase.later P)
            (uPred_fupd (M := M) (F := F) W (maskDiff (nclose N).mem N)
              (nclose N).mem (BIBase.pure True)))) ⊢
      uPred_fupd (M := M) (F := F) W E (maskDiff E N)
        (BIBase.sep (BIBase.later P)
          (BIBase.forall fun E' : Iris.Set Positive =>
            BIBase.wand (BIBase.later P)
              (uPred_fupd (M := M) (F := F) W E'
                (fun x => (nclose N).mem x ∨ E' x) (BIBase.pure True)))) := by
  -- lift the postcondition via `fupd_mono`
  exact fupd_mono (W := W) (M := M) (F := F) (E1 := E) (E2 := maskDiff E N)
    (P := BIBase.sep (BIBase.later P)
      (BIBase.wand (BIBase.later P)
        (uPred_fupd (M := M) (F := F) W (maskDiff (nclose N).mem N)
          (nclose N).mem (BIBase.pure True))))
    (Q := BIBase.sep (BIBase.later P)
      (BIBase.forall fun E' : Iris.Set Positive =>
        BIBase.wand (BIBase.later P)
          (uPred_fupd (M := M) (F := F) W E'
            (fun x => (nclose N).mem x ∨ E' x) (BIBase.pure True))))
    (inv_acc_strong_post (W := W) (N := N) (P := P))

omit [FiniteMapLaws Positive M] in
/-- Combine disjoint invariants into a larger namespace.

    Coq: `inv_combine` -/
theorem inv_combine {W : WsatGS GF}
    (N1 N2 N : Namespace) (P Q : IProp GF)
    (hdisj : CoPset.Disjoint (nclose N1) (nclose N2))
    (hsubset : Subset (fun x => (nclose N1).mem x ∨ (nclose N2).mem x) (nclose N).mem) :
    inv (GF := GF) (M := M) (F := F) W N1 P ⊢
      BIBase.wand (inv (GF := GF) (M := M) (F := F) W N2 Q)
        (inv (GF := GF) (M := M) (F := F) W N (BIBase.sep (PROP := IProp GF) P Q)) := by
  classical
  iintro HinvP
  iintro HinvQ
  -- unfold the invariant body and build it under a persistent context
  let body : IProp GF :=
    BIBase.forall fun E : Iris.Set Positive =>
      BIBase.imp (BIBase.pure (Subset (nclose N).mem E))
        (uPred_fupd (M := M) (F := F) W E (maskDiff E N)
          (BIBase.sep (BIBase.later (BIBase.sep (PROP := IProp GF) P Q))
            (BIBase.wand (BIBase.later (BIBase.sep (PROP := IProp GF) P Q))
              (uPred_fupd (M := M) (F := F) W (maskDiff E N) E (BIBase.pure True)))))
  have hbody :
      BIBase.sep (inv (GF := GF) (M := M) (F := F) W N1 P)
        (inv (GF := GF) (M := M) (F := F) W N2 Q) ⊢
        body := by
    -- unpack the invariant context and prove the body
    iintro Hctx
    icases Hctx with ⟨HinvP', HinvQ'⟩
    iintro %E
    iintro hE
    icases hE with %hE
    -- derive namespace inclusions for both invariants
    have hN1 : Subset (nclose N1).mem E := by
      intro i hi; exact hE _ (hsubset _ (Or.inl hi))
    have hN2 : Subset (nclose N2).mem E := by
      intro i hi; exact hE _ (hsubset _ (Or.inr hi))
    have hN2' :
        Subset (nclose N2).mem (maskDiff E N1) :=
      nclose_subset_maskDiff (E := E) (N1 := N1) (N2 := N2) hdisj hN2
    -- abbreviations for the staged postconditions
    let E12 : Iris.Set Positive := maskDiff (maskDiff E N1) N2
    let postP : IProp GF :=
      BIBase.sep (BIBase.later P)
        (BIBase.wand (BIBase.later P)
          (uPred_fupd (M := M) (F := F) W (maskDiff E N1) E (BIBase.pure True)))
    let postQ : IProp GF :=
      BIBase.sep (BIBase.later Q)
        (BIBase.wand (BIBase.later Q)
          (uPred_fupd (M := M) (F := F) W E12 (maskDiff E N1) (BIBase.pure True)))
    let postPQ : IProp GF :=
      BIBase.sep (BIBase.later (BIBase.sep (PROP := IProp GF) P Q))
        (BIBase.wand (BIBase.later (BIBase.sep (PROP := IProp GF) P Q))
          (uPred_fupd (M := M) (F := F) W (maskDiff E N) E (BIBase.pure True)))
    -- open the left invariant
    ihave HaccP :=
      (wrapEntails (GF := GF)
        (inv_acc (W := W) (M := M) (F := F) (E := E) (N := N1) (P := P) hN1)) $$ HinvP'
    -- sequence the two accesses with `fupd_trans`
    iapply (wrapEntails (GF := GF)
      (fupd_trans (W := W) (E1 := E) (E2 := maskDiff E N1) (E3 := maskDiff E N)
        (P := postPQ)))
    -- strengthen the postcondition after opening `N1`
    have hpost :
        BIBase.sep postP (inv (GF := GF) (M := M) (F := F) W N2 Q) ⊢
          uPred_fupd (M := M) (F := F) W (maskDiff E N1) (maskDiff E N) postPQ := by
      -- open `N2` under a framed postcondition
      iintro Hctx'
      icases Hctx' with ⟨HpostP, HinvQ''⟩
      iapply (wrapEntails (GF := GF)
        (fupd_trans (W := W) (E1 := maskDiff E N1) (E2 := E12) (E3 := maskDiff E N)
          (P := postPQ)))
      -- open the right invariant inside the postcondition
      ihave HaccQ :=
        (wrapEntails (GF := GF)
          (inv_acc (W := W) (M := M) (F := F) (E := maskDiff E N1) (N := N2) (P := Q) hN2')) $$ HinvQ''
      have hpostQ :
          BIBase.sep postQ postP ⊢ uPred_fupd (M := M) (F := F) W E12 (maskDiff E N) postPQ := by
        -- introduce the smaller mask and assemble the closing wand
        iintro Hpost
        icases Hpost with ⟨HpostQ, HpostP⟩
        icases HpostP with ⟨HP, HcloseP⟩
        icases HpostQ with ⟨HQ, HcloseQ⟩
        have hsubset_mask : Subset (maskDiff E N) E12 := by
          -- rewrite the two-step mask difference
          simpa [E12, maskDiff2_eq] using
            (maskDiff2_subset_of_union (E := E) (N1 := N1) (N2 := N2) (N := N) hsubset)
        iapply (wrapEntails (GF := GF)
          (fupd_mask_intro (W := W) (E1 := E12) (E2 := maskDiff E N) hsubset_mask postPQ))
        iintro Hclose
        have hlater :
            BIBase.sep (BIBase.later P) (BIBase.later Q) ⊢ BIBase.later (BIBase.sep (PROP := IProp GF) P Q) :=
          (later_sep (P := P) (Q := Q)).2
        ihave HPQ := (wrapEntails (GF := GF) hlater) $$ [HP, HQ]
        -- unfold the target postcondition and split it
        simp
        isplitl [HPQ]
        · iexact HPQ
        · -- close the smaller mask, then `N2`, then `N1`
          iintro HPQ'
          ihave HPQ'' :=
            (wrapEntails (GF := GF)
              (later_sep (P := P) (Q := Q)).1) $$ HPQ'
          icases HPQ'' with ⟨HP', HQ'⟩
          -- first close `Q`, then re-close the outer mask
          iapply (wrapEntails (GF := GF)
            (fupd_trans (W := W) (E1 := maskDiff E N) (E2 := maskDiff E N1) (E3 := E)
              (P := BIBase.pure True)))
          iapply (wrapEntails (GF := GF)
            (fupd_wand_r (W := W) (M := M) (F := F) (E1 := maskDiff E N) (E2 := maskDiff E N1)
              (P := BIBase.pure True)
              (Q := uPred_fupd (M := M) (F := F) W (maskDiff E N1) E (BIBase.pure True))))
          isplitl [Hclose HcloseQ HQ']
          · -- close `Q` inside the intermediate mask
            iapply (wrapEntails (GF := GF)
              (fupd_trans (W := W) (E1 := maskDiff E N) (E2 := E12) (E3 := maskDiff E N1)
                (P := BIBase.pure True)))
            iapply (wrapEntails (GF := GF)
              (fupd_wand_r (W := W) (M := M) (F := F) (E1 := maskDiff E N) (E2 := E12)
                (P := (BIBase.emp : IProp GF))
                (Q := uPred_fupd (M := M) (F := F) W E12 (maskDiff E N1) (BIBase.pure True))))
            isplitl [Hclose]
            · iexact Hclose
            · iintro -
              iapply HcloseQ
              iexact HQ'
          · -- ignore `True` and close `P`
            iintro _
            iapply HcloseP
            iexact HP'
      iapply (wrapEntails (GF := GF)
        (fupd_mono (W := W) (E1 := maskDiff E N1) (E2 := E12) (P := BIBase.sep postQ postP)
          (Q := uPred_fupd (M := M) (F := F) W E12 (maskDiff E N) postPQ) hpostQ))
      iapply (wrapEntails (GF := GF)
        (fupd_frame_r (W := W) (M := M) (F := F) (E1 := maskDiff E N1) (E2 := E12)
          (P := postQ) (Q := postP)))
      isplitl [HaccQ]
      · iexact HaccQ
      · iexact HpostP
    iapply (wrapEntails (GF := GF)
      (fupd_mono (W := W) (E1 := E) (E2 := maskDiff E N1)
        (P := BIBase.sep postP (inv (GF := GF) (M := M) (F := F) W N2 Q))
        (Q := uPred_fupd (M := M) (F := F) W (maskDiff E N1) (maskDiff E N) postPQ) hpost))
    iapply (wrapEntails (GF := GF)
      (fupd_frame_r (W := W) (M := M) (F := F) (E1 := E) (E2 := maskDiff E N1)
        (P := postP)
        (Q := inv (GF := GF) (M := M) (F := F) W N2 Q)))
    isplitl [HaccP]
    · iexact HaccP
    · iexact HinvQ'
  have hpers :
      BIBase.sep (inv (GF := GF) (M := M) (F := F) W N1 P)
        (inv (GF := GF) (M := M) (F := F) W N2 Q) ⊢
        BIBase.persistently body :=
    persistently_intro''
      (P := BIBase.sep (inv (GF := GF) (M := M) (F := F) W N1 P)
        (inv (GF := GF) (M := M) (F := F) W N2 Q))
      (Q := body) hbody
  iapply (wrapEntails (GF := GF) (by simpa [body] using hpers))
  isplitl [HinvP]
  · iexact HinvP
  · iexact HinvQ

omit [FiniteMapLaws Positive M] in
/-- Combine invariants using a duplicable left component.

    Coq: `inv_combine_dup_l` -/
theorem inv_combine_dup_l {W : WsatGS GF}
    (N : Namespace) (P Q : IProp GF) :
    BIBase.persistently (BIBase.wand P (BIBase.sep P P)) ⊢
      BIBase.wand (inv (GF := GF) (M := M) (F := F) W N P)
        (BIBase.wand (inv (GF := GF) (M := M) (F := F) W N Q)
          (inv (GF := GF) (M := M) (F := F) W N (BIBase.sep (PROP := IProp GF) P Q))) := by
  classical
  iintro Hdup
  iintro HinvP
  iintro HinvQ
  -- unfold the invariant body and build it under a persistent context
  let body : IProp GF :=
    BIBase.forall fun E : Iris.Set Positive =>
      BIBase.imp (BIBase.pure (Subset (nclose N).mem E))
        (uPred_fupd (M := M) (F := F) W E (maskDiff E N)
          (BIBase.sep (BIBase.later (BIBase.sep (PROP := IProp GF) P Q))
            (BIBase.wand (BIBase.later (BIBase.sep (PROP := IProp GF) P Q))
              (uPred_fupd (M := M) (F := F) W (maskDiff E N) E (BIBase.pure True)))))
  have hbody :
      BIBase.sep (BIBase.persistently (BIBase.wand P (BIBase.sep P P)))
        (BIBase.sep (inv (GF := GF) (M := M) (F := F) W N P)
          (inv (GF := GF) (M := M) (F := F) W N Q)) ⊢
        body := by
    -- unpack the invariant context and prove the body
    iintro Hctx
    icases Hctx with ⟨Hdup', HinvPQ⟩
    icases HinvPQ with ⟨HinvP', HinvQ'⟩
    iintro %E
    iintro hE
    icases hE with %hE
    -- abbreviations for postconditions
    let postP : IProp GF :=
      BIBase.sep (BIBase.later P)
        (BIBase.wand (BIBase.later P)
          (uPred_fupd (M := M) (F := F) W (maskDiff E N) E (BIBase.pure True)))
    let postQ : IProp GF :=
      BIBase.sep (BIBase.later Q)
        (BIBase.wand (BIBase.later Q)
          (uPred_fupd (M := M) (F := F) W (maskDiff E N) E (BIBase.pure True)))
    let postPQ : IProp GF :=
      BIBase.sep (BIBase.later (BIBase.sep (PROP := IProp GF) P Q))
        (BIBase.wand (BIBase.later (BIBase.sep (PROP := IProp GF) P Q))
          (uPred_fupd (M := M) (F := F) W (maskDiff E N) E (BIBase.pure True)))
    -- open the left invariant first
    ihave HaccP :=
      (wrapEntails (GF := GF)
        (inv_acc (W := W) (M := M) (F := F) (E := E) (N := N) (P := P) hE)) $$ HinvP'
    iapply (wrapEntails (GF := GF)
      (fupd_trans (W := W) (E1 := E) (E2 := maskDiff E N) (E3 := maskDiff E N) (P := postPQ)))
    iapply (wrapEntails (GF := GF)
      (fupd_mono (W := W) (E1 := E) (E2 := maskDiff E N)
        (P := BIBase.sep postP
          (BIBase.sep (inv (GF := GF) (M := M) (F := F) W N Q)
            (BIBase.persistently (BIBase.wand P (BIBase.sep P P)))))
        (Q := uPred_fupd (M := M) (F := F) W (maskDiff E N) (maskDiff E N) postPQ) ?_))
    · -- close `P`, open `Q`, then build the combined invariant
      iintro Hpost
      icases Hpost with ⟨HpostP, Hrest⟩
      icases Hrest with ⟨HinvQ'', Hdup''⟩
      icases HpostP with ⟨HP, HcloseP⟩
      ihave HPdup :=
        (wrapEntails (GF := GF) (later_dup (P := P))) $$ Hdup''
      ispecialize HPdup $$ HP
      icases HPdup with ⟨HP1, HP2⟩
      -- close the left invariant to restore the mask
      ihave Hclosed := HcloseP $$ HP2
      -- open the right invariant
      ihave HaccQ :=
        (wrapEntails (GF := GF)
          (inv_acc (W := W) (M := M) (F := F) (E := E) (N := N) (P := Q) hE)) $$ HinvQ''
      -- build the postcondition for the combined invariant
      have hpostQ : BIBase.sep postQ (BIBase.later P) ⊢ postPQ := by
        -- use the remaining `▷P` and `▷Q`
        iintro Hpost
        icases Hpost with ⟨HpostQ, HP1'⟩
        icases HpostQ with ⟨HQ, HcloseQ⟩
        have hlater :
            BIBase.sep (BIBase.later P) (BIBase.later Q) ⊢ BIBase.later (BIBase.sep (PROP := IProp GF) P Q) :=
          (later_sep (P := P) (Q := Q)).2
        ihave HPQ := (wrapEntails (GF := GF) hlater) $$ [HP1', HQ]
        -- unfold the target postcondition and split it
        simp
        isplitl [HPQ]
        · iexact HPQ
        · -- close using the right invariant only
          iintro HPQ'
          ihave HPQ'' :=
            (wrapEntails (GF := GF)
              (later_sep (P := P) (Q := Q)).1) $$ HPQ'
          icases HPQ'' with ⟨_, HQ'⟩
          iapply HcloseQ
          iexact HQ'
      -- sequence closing `P` with opening `Q`
      iapply (wrapEntails (GF := GF)
        (fupd_trans (W := W) (E1 := maskDiff E N) (E2 := E) (E3 := maskDiff E N) (P := postPQ)))
      iapply (wrapEntails (GF := GF)
        (fupd_wand_r (W := W) (M := M) (F := F) (E1 := maskDiff E N) (E2 := E)
          (P := BIBase.pure True)
          (Q := uPred_fupd (M := M) (F := F) W E (maskDiff E N) postPQ)))
      isplitl [Hclosed]
      · iexact Hclosed
      · -- ignore `True` and use the access to `Q`
        iintro _
        iapply (wrapEntails (GF := GF)
          (fupd_mono (W := W) (M := M) (F := F) (E1 := E) (E2 := maskDiff E N)
            (P := BIBase.sep postQ (BIBase.later P)) (Q := postPQ) hpostQ))
        iapply (wrapEntails (GF := GF)
          (fupd_frame_r (W := W) (M := M) (F := F) (E1 := E) (E2 := maskDiff E N)
            (P := postQ) (Q := BIBase.later P)))
        isplitl [HaccQ]
        · iexact HaccQ
        · iexact HP1
    iapply (wrapEntails (GF := GF)
      (fupd_frame_r (W := W) (M := M) (F := F) (E1 := E) (E2 := maskDiff E N)
        (P := postP)
        (Q := BIBase.sep (inv (GF := GF) (M := M) (F := F) W N Q)
          (BIBase.persistently (BIBase.wand P (BIBase.sep P P))))))
    isplitl [HaccP]
    · iexact HaccP
    · isplitl [HinvQ']
      · iexact HinvQ'
      · iexact Hdup'
  have hpers :
      BIBase.sep (BIBase.persistently (BIBase.wand P (BIBase.sep P P)))
        (BIBase.sep (inv (GF := GF) (M := M) (F := F) W N P)
          (inv (GF := GF) (M := M) (F := F) W N Q)) ⊢
        BIBase.persistently body :=
    persistently_intro''
      (P := BIBase.sep (BIBase.persistently (BIBase.wand P (BIBase.sep P P)))
        (BIBase.sep (inv (GF := GF) (M := M) (F := F) W N P)
          (inv (GF := GF) (M := M) (F := F) W N Q)))
      (Q := body) hbody
  iapply (wrapEntails (GF := GF) (by simpa [body] using hpers))
  isplitl [Hdup]
  · iexact Hdup
  · isplitl [HinvP]
    · iexact HinvP
    · iexact HinvQ

omit [FiniteMapLaws Positive M] in
/-- Invariants are except-0.

    Coq: `except_0_inv` -/
theorem except_0_inv {W : WsatGS GF}
    (N : Namespace) (P : IProp GF) :
    BIBase.except0 (inv (GF := GF) (M := M) (F := F) W N P) ⊢
      inv (GF := GF) (M := M) (F := F) W N P := by
  -- unfold the invariant body and eliminate the outer `◇` by cases
  unfold inv
  let body : IProp GF :=
    BIBase.forall fun E : Iris.Set Positive =>
      BIBase.imp (BIBase.pure (Subset (nclose N).mem E))
        (uPred_fupd (M := M) (F := F) W E (maskDiff E N)
          (BIBase.sep (BIBase.later P)
            (BIBase.wand (BIBase.later P)
              (uPred_fupd (M := M) (F := F) W (maskDiff E N) E (BIBase.pure True)))))
  have hfalse_body : BIBase.later (BIBase.pure False) ⊢ body := by
    refine forall_intro ?_
    intro E
    refine imp_intro ?_
    refine pure_elim_r ?_
    intro _
    -- `▷ False` proves any fancy update
    unfold uPred_fupd
    refine wand_intro ?_
    refine (sep_elim_l (P := BIBase.later (BIBase.pure False))
      (Q := BIBase.sep (wsat' (M := M) (F := F) W) (ownE W (mask E)))).trans ?_
    let post : IProp GF :=
      BIBase.sep (wsat' (M := M) (F := F) W)
        (BIBase.sep (ownE W (mask (maskDiff E N)))
          (BIBase.sep (BIBase.later P)
            (BIBase.wand (BIBase.later P)
              (uPred_fupd (M := M) (F := F) W (maskDiff E N) E (BIBase.pure True)))))
    have hor : BIBase.later (BIBase.pure False) ⊢ BIBase.except0 post := by
      -- `◇ post` is `▷ False ∨ post`
      exact or_intro_l
    refine (BIUpdate.intro (P := BIBase.later (BIBase.pure False))).trans ?_
    exact BIUpdate.mono (PROP := IProp GF) hor
  have hfalse_pers :
      BIBase.later (BIBase.pure False) ⊢ BIBase.persistently body :=
    persistently_intro'' (P := BIBase.later (BIBase.pure False)) (Q := body) hfalse_body
  have hcase :
      BIBase.or (BIBase.later (BIBase.pure False)) (BIBase.persistently body) ⊢
        BIBase.persistently body :=
    or_elim hfalse_pers .rfl
  simpa [BIBase.except0, body] using hcase

/-! ### Proof Mode Integration -/

omit [FiniteMapLaws Positive M] in
instance is_except0_inv {W : WsatGS GF} (N : Namespace) (P : IProp GF) :
    Iris.ProofMode.IsExcept0 (PROP := IProp GF)
      (inv (GF := GF) (M := M) (F := F) W N P) := by
  -- reuse the derived lemma
  exact ⟨except_0_inv (W := W) (N := N) (P := P)⟩

omit [FiniteMapLaws Positive M] in
instance into_inv_inv {W : WsatGS GF} (N : Namespace) (P : IProp GF) :
    Iris.ProofMode.IntoInv (PROP := IProp GF)
      (inv (GF := GF) (M := M) (F := F) W N P) N :=
  ⟨⟩

omit [FiniteMapLaws Positive M] in
instance into_acc_inv {W : WsatGS GF}
    (E : Iris.Set Positive) (N : Namespace) (P : IProp GF) :
    Iris.ProofMode.IntoAcc (PROP := IProp GF) (X := Unit)
      (inv (GF := GF) (M := M) (F := F) W N P)
      (Subset (nclose N).mem E) (BIBase.pure True)
      (uPred_fupd (M := M) (F := F) W E (maskDiff E N))
      (uPred_fupd (M := M) (F := F) W (maskDiff E N) E)
      (fun _ => BIBase.later P) (fun _ => BIBase.later P)
      (fun _ => some (BIBase.pure True)) := by
  -- unfold the accessor and use `inv_acc`
  refine ⟨?_⟩
  intro hsubset
  iintro Hinv
  iintro _
  let Ψ : Unit → IProp GF := fun _ =>
    BIBase.sep (BIBase.later P)
      (BIBase.wand (BIBase.later P)
        (uPred_fupd (M := M) (F := F) W (maskDiff E N) E (BIBase.pure True)))
  -- unfold the accessor to match `inv_acc`
  simp [Iris.ProofMode.accessor]
  have hmono :=
    fupd_mono (W := W) (M := M) (F := F) (E1 := E) (E2 := maskDiff E N)
      (P := Ψ ()) (Q := BIBase.exists Ψ) (exists_unit (Ψ := Ψ)).2
  have hacc :=
    inv_acc (W := W) (M := M) (F := F) (E := E) (N := N) (P := P) hsubset
  iapply (wrapEntails (GF := GF) (hacc.trans hmono))
  iexact Hinv

omit [FiniteMapLaws Positive M] in
/-- Strong invariant accessor: closing under any mask extension.

    Coq: `inv_acc_strong` -/
theorem inv_acc_strong {W : WsatGS GF}
    (E : Iris.Set Positive) (N : Namespace) (P : IProp GF)
    (h : Subset (nclose N).mem E) :
    inv (GF := GF) (M := M) (F := F) W N P ⊢
      uPred_fupd (M := M) (F := F) W E (maskDiff E N)
        (BIBase.sep (BIBase.later P)
          (BIBase.forall fun E' : Iris.Set Positive =>
            BIBase.wand (BIBase.later P)
              (uPred_fupd (M := M) (F := F) W E'
                (fun x => (nclose N).mem x ∨ E' x) (BIBase.pure True)))) := by
  classical
  iintro Hinv
  -- open at the minimal mask and frame to `E`
  have hsubset : Subset (nclose N).mem (nclose N).mem := by
    intro i hi; exact hi
  ihave Hacc :=
    (wrapEntails (GF := GF)
      (inv_acc (W := W) (M := M) (F := F) (E := (nclose N).mem) (N := N) (P := P) hsubset)) $$ Hinv
  ihave Hacc' :=
    (wrapEntails (GF := GF)
      (inv_acc_strong_frame (M := M) (F := F) (W := W) (E := E) (N := N) (P := P) h)) $$ Hacc
  iapply (wrapEntails (GF := GF)
    (inv_acc_strong_mono (W := W) (E := E) (N := N) (P := P)))
  iexact Hacc'

omit [FiniteMapLaws Positive M] in
/-- Alter the content of an invariant.

    Coq: `inv_alter` -/
theorem inv_alter {W : WsatGS GF}
    (N : Namespace) (P Q : IProp GF) :
    (BIBase.emp : IProp GF) ⊢
      BIBase.wand (inv (GF := GF) (M := M) (F := F) W N P)
        (BIBase.wand (BIBase.later (BIBase.intuitionistically
          (BIBase.wand P (BIBase.sep Q (BIBase.wand Q P)))))
          (inv (GF := GF) (M := M) (F := F) W N Q)) := by
  classical
  iintro Hemp
  iintro Hinv
  iintro Hpq
  -- build the invariant body from a persistent sep context
  let body : IProp GF :=
    BIBase.forall fun E : Iris.Set Positive =>
      BIBase.imp (BIBase.pure (Subset (nclose N).mem E))
        (uPred_fupd (M := M) (F := F) W E (maskDiff E N)
          (BIBase.sep (BIBase.later Q)
            (BIBase.wand (BIBase.later Q)
              (uPred_fupd (M := M) (F := F) W (maskDiff E N) E
                (BIBase.pure True)))))
  have hbody_wand :
      (BIBase.emp : IProp GF) ⊢
        iprop((inv (GF := GF) (M := M) (F := F) W N P ∗
          BIBase.later (BIBase.intuitionistically
            (BIBase.wand P (BIBase.sep Q (BIBase.wand Q P))))) -∗ body) := by
    iintro -
    iintro Hctx
    icases Hctx with ⟨Hinv', Hpq'⟩
    iintro %E
    iintro hsubset
    icases hsubset with %hsubset
    -- open the invariant and frame the transformation hypothesis
    ihave Hacc :=
      (wrapEntails (GF := GF)
        (inv_acc (W := W) (M := M) (F := F) (E := E) (N := N) (P := P) hsubset)) $$ Hinv'
    ihave Hacc' :=
      (wrapEntails (GF := GF)
        (fupd_frame_r (W := W) (M := M) (F := F) (E1 := E) (E2 := maskDiff E N)
          (P := BIBase.sep (BIBase.later P)
            (BIBase.wand (BIBase.later P)
              (uPred_fupd (M := M) (F := F) W (maskDiff E N) E (BIBase.pure True))))
          (Q := BIBase.later (BIBase.intuitionistically
            (BIBase.wand P (BIBase.sep Q (BIBase.wand Q P))))))) $$ [Hacc, Hpq']
    · -- frame the transformation hypothesis across the update
      isplitl [Hacc]
      · iexact Hacc
      · iexact Hpq'
    -- transform the postcondition
    have hpost :
        BIBase.sep
          (BIBase.sep (BIBase.later P)
            (BIBase.wand (BIBase.later P)
              (uPred_fupd (M := M) (F := F) W (maskDiff E N) E (BIBase.pure True))))
          (BIBase.later (BIBase.intuitionistically
            (BIBase.wand P (BIBase.sep Q (BIBase.wand Q P))))) ⊢
        BIBase.sep (BIBase.later Q)
          (BIBase.wand (BIBase.later Q)
            (uPred_fupd (M := M) (F := F) W (maskDiff E N) E (BIBase.pure True)) : IProp GF) := by
      iintro Hpost
      icases Hpost with ⟨HpostP, Hpq''⟩
      icases HpostP with ⟨HlateP, HcloseP⟩
      -- derive ▷(P -∗ Q ∗ (Q -∗ P)) from ▷□(...)
      ihave Hpq''' :=
        (wrapEntails (GF := GF)
          (later_mono (P := BIBase.intuitionistically
            (BIBase.wand P (BIBase.sep Q (BIBase.wand Q P))))
            (Q := BIBase.wand P (BIBase.sep Q (BIBase.wand Q P)))
            (intuitionistically_elim (P := BIBase.wand P (BIBase.sep Q (BIBase.wand Q P)))))) $$ Hpq''
      -- apply later wand to obtain ▷(Q ∗ (Q -∗ P))
      ihave Hwand :=
        (wrapEntails (GF := GF)
          (later_wand (P := P) (Q := BIBase.sep Q (BIBase.wand Q P)))) $$ Hpq'''
      ispecialize Hwand $$ HlateP
      -- split the later'd pair
      ihave Hsplit :=
        (wrapEntails (GF := GF)
          (later_sep (P := Q) (Q := BIBase.wand Q P)).1) $$ Hwand
      icases Hsplit with ⟨HlateQ, HlateQtoP⟩
      isplitl [HlateQ]
      · iexact HlateQ
      · iintro Hq
        ihave Hqp :=
          (wrapEntails (GF := GF) (later_wand (P := Q) (Q := P))) $$ HlateQtoP
        ispecialize Hqp $$ Hq
        iapply HcloseP
        iexact Hqp
    iapply (wrapEntails (GF := GF)
      (fupd_mono (W := W) (M := M) (F := F) (E1 := E) (E2 := maskDiff E N)
        (P := BIBase.sep
          (BIBase.sep (BIBase.later P)
            (BIBase.wand (BIBase.later P)
              (uPred_fupd (M := M) (F := F) W (maskDiff E N) E (BIBase.pure True))))
          (BIBase.later (BIBase.intuitionistically
            (BIBase.wand P (BIBase.sep Q (BIBase.wand Q P))))))
        (Q := BIBase.sep (BIBase.later Q)
          (BIBase.wand (BIBase.later Q)
            (uPred_fupd (M := M) (F := F) W (maskDiff E N) E (BIBase.pure True))))
        hpost))
    iexact Hacc'
  have hbody :
      BIBase.sep (inv (GF := GF) (M := M) (F := F) W N P)
        (BIBase.later (BIBase.intuitionistically
          (BIBase.wand P (BIBase.sep Q (BIBase.wand Q P))))) ⊢
        body := by
    -- move the wand proof under a sep and eliminate it
    refine (sep_emp (P := BIBase.sep (inv (GF := GF) (M := M) (F := F) W N P)
      (BIBase.later (BIBase.intuitionistically
        (BIBase.wand P (BIBase.sep Q (BIBase.wand Q P))))))).2.trans ?_
    refine (sep_mono .rfl hbody_wand).trans ?_
    exact wand_elim_r
  -- wrap the body in persistently using the persistent context
  have hpers :
      BIBase.sep (inv (GF := GF) (M := M) (F := F) W N P)
        (BIBase.later (BIBase.intuitionistically
          (BIBase.wand P (BIBase.sep Q (BIBase.wand Q P))))) ⊢
        BIBase.persistently body :=
    persistently_intro''
      (P := BIBase.sep (inv (GF := GF) (M := M) (F := F) W N P)
        (BIBase.later (BIBase.intuitionistically
          (BIBase.wand P (BIBase.sep Q (BIBase.wand Q P))))))
      (Q := body) hbody
  -- fold the invariant definition on the postcondition
  have hpers' :
      BIBase.sep (inv (GF := GF) (M := M) (F := F) W N P)
        (BIBase.later (BIBase.intuitionistically
          (BIBase.wand P (BIBase.sep Q (BIBase.wand Q P))))) ⊢
        inv (GF := GF) (M := M) (F := F) W N Q :=
    hpers.trans (BIBase.Entails.of_eq (by rfl))
  iapply (wrapEntails (GF := GF) hpers')
  -- supply the persistent context
  isplitl [Hinv]
  · iexact Hinv
  · iexact Hpq

-- Abbreviation for the wand-based `P ↔ Q`.
private abbrev iffWand (P Q : IProp GF) : IProp GF :=
  BIBase.and (BIBase.wand P Q) (BIBase.wand Q P)

omit [ElemG GF (COFE.constOF CoPsetDisj)]
  [ElemG GF (COFE.constOF GSetDisj)] in
private theorem iff_wand_left (P Q : IProp GF) :
    BIBase.intuitionistically (iffWand P Q) ⊢ BIBase.wand P Q := by
  -- Pull the left implication out of the persistent conjunction.
  exact (intuitionistically_elim (P := iffWand P Q)).trans
    (and_elim_l (P := BIBase.wand P Q) (Q := BIBase.wand Q P))

omit [ElemG GF (COFE.constOF CoPsetDisj)]
  [ElemG GF (COFE.constOF GSetDisj)] in
private theorem iff_wand_right (P Q : IProp GF) :
    BIBase.intuitionistically (iffWand P Q) ⊢ BIBase.wand Q P := by
  -- Pull the right implication out of the persistent conjunction.
  exact (intuitionistically_elim (P := iffWand P Q)).trans
    (and_elim_r (P := BIBase.wand P Q) (Q := BIBase.wand Q P))

omit [ElemG GF (COFE.constOF CoPsetDisj)]
  [ElemG GF (COFE.constOF GSetDisj)] in
private theorem iff_to_sep_wand (P Q : IProp GF) :
    BIBase.intuitionistically (iffWand P Q) ⊢
      BIBase.wand P (BIBase.sep Q (BIBase.wand Q P)) := by
  -- Duplicate the iff and use each direction once.
  refine wand_intro ?_
  have hdup :
      BIBase.intuitionistically (iffWand P Q) ⊢
        BIBase.sep (BIBase.intuitionistically (iffWand P Q))
          (BIBase.intuitionistically (iffWand P Q)) :=
    (intuitionistically_sep_idem (P := iffWand P Q)).2
  refine (sep_mono_l hdup).trans ?_
  refine sep_assoc_l.trans ?_
  have hQ :
      BIBase.sep (BIBase.intuitionistically (iffWand P Q)) P ⊢ Q :=
    (sep_mono_l (iff_wand_left (P := P) (Q := Q))).trans wand_elim_l
  refine (sep_mono (iff_wand_right (P := P) (Q := Q)) hQ).trans ?_
  exact sep_comm.1

omit [FiniteMapLaws Positive M] in
/-- Invariant content equivalence.

    Coq: `inv_iff` -/
theorem inv_iff {W : WsatGS GF}
    (N : Namespace) (P Q : IProp GF) :
    (BIBase.emp : IProp GF) ⊢
      BIBase.wand (inv (GF := GF) (M := M) (F := F) W N P)
        (BIBase.wand (BIBase.later (BIBase.intuitionistically
          (BIBase.and (BIBase.wand P Q) (BIBase.wand Q P))))
          (inv (GF := GF) (M := M) (F := F) W N Q)) := by
  classical
  iintro Hemp
  iintro Hinv
  iintro Hpq
  -- Lift the iff into the wand form expected by `inv_alter`.
  have hbox :
      BIBase.intuitionistically (iffWand P Q) ⊢
      BIBase.intuitionistically
        (BIBase.wand P (BIBase.sep Q (BIBase.wand Q P))) :=
    intuitionistically_intro' (iff_to_sep_wand (P := P) (Q := Q))
  ihave Hpq' :=
    (wrapEntails (GF := GF)
      (later_mono
        (P := BIBase.intuitionistically (iffWand P Q))
        (Q := BIBase.intuitionistically
          (BIBase.wand P (BIBase.sep Q (BIBase.wand Q P))))
        hbox)) $$ Hpq
  -- Apply `inv_alter` with the converted hypothesis.
  ihave Hinv' :=
    (wrapEntails (GF := GF)
      (inv_alter (W := W) (M := M) (F := F) (N := N) (P := P) (Q := Q))) $$ Hemp
  ispecialize Hinv' $$ Hinv
  ispecialize Hinv' $$ Hpq'
  iexact Hinv'

omit [FiniteMapLaws Positive M] in
/-- Split an invariant on the left component.

    Coq: `inv_split_l` -/
theorem inv_split_l {W : WsatGS GF}
    (N : Namespace) (P Q : IProp GF) :
    inv (GF := GF) (M := M) (F := F) W N (BIBase.sep (PROP := IProp GF) P Q) ⊢
      inv (GF := GF) (M := M) (F := F) W N P := by
  -- build the wand via `inv_alter`, then eliminate it with `emp`
  have hwand :
      (BIBase.emp : IProp GF) ⊢
        BIBase.wand
          (inv (GF := GF) (M := M) (F := F) W N (BIBase.sep (PROP := IProp GF) P Q))
          (inv (GF := GF) (M := M) (F := F) W N P) := by
    let Einv : IProp GF :=
      inv (GF := GF) (M := M) (F := F) W N (BIBase.sep (PROP := IProp GF) P Q)
    let Hstep : IProp GF :=
      BIBase.later (BIBase.intuitionistically
        (BIBase.wand (BIBase.sep (PROP := IProp GF) P Q)
          (BIBase.sep P (BIBase.wand P (BIBase.sep (PROP := IProp GF) P Q)))))
    have Halter :
        (BIBase.emp : IProp GF) ⊢
          BIBase.wand Einv
            (BIBase.wand Hstep (inv (GF := GF) (M := M) (F := F) W N P)) :=
      inv_alter (W := W) (M := M) (F := F) (N := N)
        (P := BIBase.sep (PROP := IProp GF) P Q) (Q := P)
    have Htrans : (BIBase.emp : IProp GF) ⊢ Hstep :=
      inv_split_l_transform (P := P) (Q := Q)
    refine wand_intro ?_
    -- duplicate `emp` so we can build the close shift and the mask introduction
    have hemp_dup :
        (BIBase.emp : IProp GF) ⊢
          BIBase.sep (BIBase.emp : IProp GF) (BIBase.emp : IProp GF) :=
      (sep_emp (P := (BIBase.emp : IProp GF))).2
    refine (sep_mono hemp_dup .rfl).trans ?_
    refine (sep_right_comm (P := (BIBase.emp : IProp GF))
      (Q := (BIBase.emp : IProp GF)) (R := Einv)).1.trans ?_
    have hleft :
        BIBase.sep (BIBase.emp : IProp GF) Einv ⊢
          BIBase.wand Hstep (inv (GF := GF) (M := M) (F := F) W N P) := by
      refine (sep_mono Halter .rfl).trans ?_
      exact wand_elim_l
    refine (sep_mono hleft .rfl).trans ?_
    refine (sep_mono .rfl Htrans).trans ?_
    exact wand_elim_l
  refine (sep_emp (P := inv (GF := GF) (M := M) (F := F) W N (BIBase.sep (PROP := IProp GF) P Q))).2.trans ?_
  refine (sep_mono .rfl hwand).trans ?_
  exact wand_elim_r

omit [FiniteMapLaws Positive M] in
/-- Split an invariant on the right component.

    Coq: `inv_split_r` -/
theorem inv_split_r {W : WsatGS GF}
    (N : Namespace) (P Q : IProp GF) :
    inv (GF := GF) (M := M) (F := F) W N (BIBase.sep (PROP := IProp GF) P Q) ⊢
      inv (GF := GF) (M := M) (F := F) W N Q := by
  -- commute the sep and reuse the left split lemma
  have hcomm :
      inv (GF := GF) (M := M) (F := F) W N (BIBase.sep (PROP := IProp GF) P Q) ⊢
        inv (GF := GF) (M := M) (F := F) W N (BIBase.sep Q P) := by
    have hsep : BIBase.sep (PROP := IProp GF) P Q ≡ BIBase.sep Q P := by
      have hsep' : BIBase.sep (PROP := IProp GF) P Q ⊣⊢ BIBase.sep Q P :=
        sep_comm (P := P) (Q := Q)
      exact (BI.equiv_iff (P := BIBase.sep (PROP := IProp GF) P Q) (Q := BIBase.sep Q P)).2 hsep'
    have hEquiv :
        inv (GF := GF) (M := M) (F := F) W N (BIBase.sep (PROP := IProp GF) P Q) ≡
          inv (GF := GF) (M := M) (F := F) W N (BIBase.sep Q P) :=
      inv_proper (W := W) (N := N) (P := BIBase.sep (PROP := IProp GF) P Q) (Q := BIBase.sep Q P) hsep
    have hBi :
        inv (GF := GF) (M := M) (F := F) W N (BIBase.sep (PROP := IProp GF) P Q) ⊣⊢
          inv (GF := GF) (M := M) (F := F) W N (BIBase.sep Q P) :=
      (BI.equiv_iff (P := inv (GF := GF) (M := M) (F := F) W N (BIBase.sep (PROP := IProp GF) P Q))
        (Q := inv (GF := GF) (M := M) (F := F) W N (BIBase.sep Q P))).1 hEquiv
    exact hBi.1
  exact hcomm.trans (inv_split_l (W := W) (M := M) (F := F) (N := N) (P := Q) (Q := P))

omit [FiniteMapLaws Positive M] in
/-- Split an invariant into two components.

    Coq: `inv_split` -/
theorem inv_split {W : WsatGS GF}
    (N : Namespace) (P Q : IProp GF) :
    inv (GF := GF) (M := M) (F := F) W N (BIBase.sep (PROP := IProp GF) P Q) ⊢
      BIBase.sep (inv (GF := GF) (M := M) (F := F) W N P)
        (inv (GF := GF) (M := M) (F := F) W N Q) := by
  -- apply both split lemmas under a separating conjunction
  iintro Hinv
  isplit
  · iapply (wrapEntails (GF := GF)
      (inv_split_l (W := W) (M := M) (F := F) (N := N) (P := P) (Q := Q)))
    iexact Hinv
  · iapply (wrapEntails (GF := GF)
      (inv_split_r (W := W) (M := M) (F := F) (N := N) (P := P) (Q := Q)))
    iexact Hinv

end Iris.BaseLogic
