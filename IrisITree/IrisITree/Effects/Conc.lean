module

import Iris.ProofMode
public import ITree.Effects.Conc
public import IrisITree.Core.Wpi

public section

namespace IrisITree

open Iris Iris.BI ITree ITree.Effects

section handler

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]

def concH : IHandler PROP concE where
  ihandle
    | .fork, Φ, Φs => iprop(Φ .parent ∗ |={⊤, ∅}=> Φs .child)
    | .yield, Φ, _ => iprop(|={∅, ⊤}=> |={⊤, ∅}=> Φ ⟨⟩)
    | .kill, _, _ => iprop(|={∅, ⊤}=> True)
  ihandle_mono := by
    iintro %i %Φ %Φ' %Φs %Φs' HΦwand #Hswand HH
    cases i <;> dsimp only
    · icases HH with ⟨HΦ, HΦs⟩
      ihave HΦ' := HΦwand $$ %ForkResult.parent HΦ
      isplitl [HΦ']
      · iexact HΦ'
      · imod HΦs; imodintro; iapply Hswand; iexact HΦs
    · imod HH; itrivial
    · imod HH; imodintro; imod HH; imodintro; iapply HΦwand $$ [$]

end handler

section wpi_rules

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]
  {E : Effect} {H : IHandler PROP E}
  [concE -< E] [Hin : InH concH H]

theorem wpi_kill M (Φ : PUnit → PROP) :
    True -∗ WPi kill @> H; ⊤, M {{Φ}} := by
  iintro Ht; unfold kill
  iapply wpi_trigger_bind
  simp [concH]
  iapply fupd_mask_intro_subseteq (by simp) $$ [$]

theorem wpi_fork M (Φ : PUnit → PROP) :
    Φ ⟨⟩ -∗
    WPi t @> H; ⊤ {{ _v, iprop(True) }} -∗
    WPi fork t @> H; M {{Φ}} := by
  iintro HΦ Ht; unfold fork
  iapply wpi_trigger_bind
  iapply fupd_mask_intro (by simp); iintro Hm
  simp [concH]; isplitr [Ht]
  · imod Hm; iapply wpi_pure; iexact HΦ
  · imod Ht; imodintro; iapply wpi_bind'
    iapply wpi_wand $$ [$]; iintro %_ _
    iapply wpi_kill $$ [$]

theorem wpi_yield (Φ : PUnit → PROP) :
    Φ ⟨⟩ -∗
    WPi yield @> H; ⊤ {{Φ}} := by
  iintro HΦ; unfold yield
  iapply wpi_trigger; simp [concH]
  iapply fupd_mask_intro_subseteq (by simp)
  iapply fupd_mask_intro_subseteq (by simp) $$ [$]

end wpi_rules

section exec

open ITree.Exec

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP] [BIAffine PROP]

private theorem filterMap_set_perm {T U : Type _} (f : T → U)
    (xs : List (Option T)) (i : Nat) (old new : Option T)
    (hi : i < xs.length) (hx : xs[i] = old) :
    ((old.map f).toList ++ (xs.set i new).filterMap (Option.map f)).Perm
      ((new.map f).toList ++ xs.filterMap (Option.map f)) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih => cases i with
    | zero =>
      simp at hx; subst a
      cases old <;> cases new <;> simp
      exact .swap _ _ _
    | succ i =>
      simp at hi hx ⊢; have hp := ih i hi hx
      cases a with
      | none => exact hp
      | some y =>
        cases old <;> cases new <;> simp at hp ⊢
        · exact hp
        · exact (List.Perm.cons (f y) hp).trans (List.Perm.swap _ _ _)
        · exact (List.Perm.swap _ _ _).trans (List.Perm.cons (f y) hp)
        · exact (List.Perm.swap _ _ _).trans ((List.Perm.cons (f y) hp).trans (List.Perm.swap _ _ _))

instance coneEH_adequate {GE GR} :
    EHandlerAdequate (PROP:=PROP) concH (concEH (GE:=GE) (GR:=GR)) where
  inv s Ms := iprop(<affine> ⌜Ms = s.pool.filterMap fun t =>
      (fun t P => iprop(|={⊤, ∅}=> P t)) <$> t⌝)
  adequate := by
    intro G i s Ms C k Hhandle
    simp [concH, concEH] at Hhandle ⊢
    cases i <;> simp at Hhandle ⊢
    · -- Fork case
      iintro ⟨_, _⟩ %h !>
      iexists _, _, fun P => P (k .parent), Ms ++ [(fun P => iprop(|={⊤, ∅}=> P (k .child)))],
        [fun P => P (k .parent), fun P => iprop(|={⊤, ∅}=> P (k .child))]
      isplitr; itrivial
      isplitr; itrivial
      simp; iframe; isplitr
      · ipureintro; simp [h, ConcState.add]
      · iintro %_ $
    · -- Kill case
      iintro Ht %h; rcases Hhandle with ⟨i, t', hi, Hget, HC⟩; imodintro
      let f := fun t (P: (ITree GE GR → PROP)) => iprop(|={⊤, ∅}=> P t)
      iexists t', ConcState.yield s.pool i hi, f t',
        (ConcState.yield s.pool i hi).pool.filterMap (Option.map f), []
      isplitr; ipureintro; exact HC
      isplitr; ipureintro
      simpa [f, ConcState.yield, h] using
        filterMap_set_perm f s.pool i (some t') none hi Hget
      isplitr; simp; exact .rfl
      isplitr; ipureintro; congr
      simp [f]; imod Ht; iintro %P $
    · -- Yield case
      iintro >Ht %h; rcases Hhandle with ⟨i, t', hi, Hget, HC⟩
      iapply fupd_mask_intro (by simp); iintro Hemp
      let f := fun t (P : ITree GE GR → PROP) => iprop(|={⊤, ∅}=> P t)
      let tp' := s.pool.set s.curr (some (k ⟨⟩))
      have hi' : i < tp'.length := by simpa [tp'] using hi
      iexists t', ConcState.yield tp' i hi', f t',
        (ConcState.yield tp' i hi').pool.filterMap (Option.map f), [f (k ⟨⟩)]
      isplitr; ipureintro; exact HC
      isplitr; ipureintro
      simpa [f, ConcState.yield, tp', h] using
        (filterMap_set_perm f tp' i (some t') none hi' Hget).trans
          (filterMap_set_perm f s.pool s.curr none (some (k ⟨⟩))
            s.curr_in_pool s.curr_is_none)
      isplitl [Ht]; simp [f]; iframe
      isplitr; ipureintro; congr
      simp [f]; imod Hemp; iintro %x $

end exec

end IrisITree
