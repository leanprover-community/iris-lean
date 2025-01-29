/-
Copyright (c) 2025 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Iris.Algebra.OFE

namespace Iris.COFE.OFunctor
open OFE

variable {F : Type u → Type u → Type u} [OFunctorContractive F]
variable [∀ α [COFE α], IsCOFE (F α α)]
variable [inh : Inhabited (F (ULift Unit) (ULift Unit))]

namespace Fix.Impl

variable (F) in
def A : Nat → Type u
  | 0 => ULift Unit
  | n+1 => F (A n) (A n)

instance instA' : ∀ n, COFE (A F n)
  | 0 => inferInstanceAs (COFE (ULift _))
  | n+1 => haveI := instA' n; inferInstanceAs (COFE (F _ _))

variable (F) in
mutual
def up : ∀ k, A F k -n> A F (k+1)
  | 0 => ⟨fun _ => inh.default, ⟨fun _ _ _ _ => .rfl⟩⟩
  | k+1 => map (down k) (up k)
def down : ∀ k, A F (k+1) -n> A F k
  | 0 => ⟨fun _ => ⟨()⟩, ⟨fun _ _ _ _ => .rfl⟩⟩
  | k+1 => map (up k) (down k)
end

theorem down_up : ∀ {k} x, down F k (up F k x) ≡ x
  | 0, ⟨()⟩ => .rfl
  | _+1, _ => (map_comp ..).symm.trans <|
    (map_ne.eqv down_up down_up _).trans map_id

theorem up_down {k} (x) : up F (k+1) (down F (k+1) x) ≡{k}≡ x := by
  refine (map_comp ..).dist.symm.trans <| .trans ?_ map_id.dist
  open OFunctorContractive in exact match k with
  | 0 => map_contractive.zero (x := (_, _)) (y := (_, _)) _ _
  | k+1 => map_contractive.succ (x := (_, _)) (y := (_, _)) _ ⟨up_down, up_down⟩ _

variable (F) in
@[ext] structure Tower : Type u where
  val k : A F k
  protected down {k} : down F k (val (k+1)) ≡ val k

instance : CoeFun (Tower F) (fun _ => ∀ k, A F k) := ⟨Tower.val⟩

instance : OFE (Tower F) where
  Equiv f g := ∀ k, f k ≡ g k
  Dist n f g := ∀ k, f k ≡{n}≡ g k
  equiv_eqv := {
    refl _ _ := equiv_eqv.refl _
    symm h _ := equiv_eqv.symm (h _)
    trans h1 h2 _ := equiv_eqv.trans (h1 _) (h2 _)
  }
  dist_eqv := {
    refl _ _ := dist_eqv.refl _
    symm h _ := dist_eqv.symm (h _)
    trans h1 h2 _ := dist_eqv.trans (h1 _) (h2 _)
  }
  equiv_dist {_ _} := by simp [equiv_dist]; apply forall_comm
  dist_lt h1 h2 _ := dist_lt (h1 _) h2

def towerChain (c : Chain (Tower F)) (k : Nat) : Chain (A F k) where
  chain i := c.1 i k
  cauchy h := c.cauchy h k

instance : COFE (Tower F) where
  compl c := by
    refine ⟨fun k => compl ⟨fun i => c.1 i k, fun h => c.cauchy h k⟩, ?_⟩
    refine equiv_dist.2 fun n => ?_
    refine ((down ..).ne.1 conv_compl).trans <| .trans ?_ conv_compl.symm
    exact (c.chain n).down.dist
  conv_compl _ := conv_compl

variable (F) in
def upN {k} : ∀ n, A F k -n> A F (k + n)
  | 0 => .id
  | n+1 => (up F (k + n)).comp (upN n)

variable (F) in
def downN {k} : ∀ n, A F (k + n) -n> A F k
  | 0 => .id
  | n+1 => (downN n).comp (down F (k + n))

theorem downN_upN {k} (x : A F k) : ∀ {i}, downN F i (upN F i x) ≡ x
  | 0 => .rfl
  | n+1 => ((downN F n).ne.eqv (down_up ..)).trans (downN_upN _)

protected theorem Tower.up (X : Tower F) : up F (k+1) (X (k+1)) ≡{k}≡ X (k+2) :=
  ((up ..).ne.1 X.down.symm.dist).trans <| up_down _

protected theorem Tower.upN (X : Tower F) : ∀ i, upN F i (X (k+1)) ≡{k}≡ X (k+1+i)
  | 0 => .rfl
  | n+1 => by
    have : ∀ j, k+n+1 = j → up F j (X j) ≡{k}≡ X (j+1) := by
      rintro _ rfl; exact X.up.le (Nat.le_add_right ..)
    exact ((up ..).ne.1 (X.upN _)).trans <| this _ (Nat.add_right_comm ..)

protected theorem Tower.downN (X : Tower F) : ∀ i, downN F i (X (k+i)) ≡ X k
  | 0 => .rfl
  | _+1 => ((downN ..).ne.eqv X.down).trans (X.downN _)

instance (k : Nat) : NonExpansive (fun X : Tower F => X.val k) := ⟨fun _ _ _ => (· _)⟩

def Tower.proj (k) : Tower F -n> A F k := ⟨(· k), ⟨fun _ _ _ => (· _)⟩⟩

def eqToHom (e : i = k) : A F i -n> A F k := e ▸ .id

theorem eqToHom_up {k k'} {x : A F k} (e : k = k') :
    eqToHom (congrArg Nat.succ e) (up F k x) = up F k' (eqToHom e x) := by
  cases e; rfl

theorem down_eqToHom {k k'} {x : A F (k+1)} (e : k = k') :
    down F k' (eqToHom (congrArg Nat.succ e) x) = eqToHom e (down F k x) := by
  cases e; rfl

def embed : A F k -n> A F i :=
  if h : k ≤ i then (eqToHom (Nat.add_sub_cancel' h)).comp (upN ..)
  else (downN ..).comp (eqToHom (Nat.add_sub_cancel' (Nat.le_of_not_ge h)).symm)

protected def Tower.embed (k) : A F k -n> Tower F := by
  refine ⟨fun n => ⟨fun _ => embed n, fun {i} => ?_⟩, ⟨fun _ _ _ h _ => embed.ne.1 h⟩⟩
  dsimp [embed]; split <;> rename_i h₁
  · split <;> rename_i h₂
    · suffices ∀ a b (e₁ : k+a = i+1) (e₂ : k+b = i),
        down F i (eqToHom e₁ (upN F a n)) ≡ eqToHom e₂ (upN F b n) from this ..
      rintro a _ eq rfl
      rw [Nat.add_assoc, Nat.add_left_cancel_iff] at eq; subst a
      apply down_up
    · cases (Nat.lt_or_eq_of_le h₁).resolve_left (h₂ ∘ Nat.lt_succ.1)
      have {a b} (e₁ : i+1+a = i+1) (e₂ : i+1 = i+b) :
          down F i (eqToHom e₁ (upN F a n)) ≡ downN F b (eqToHom e₂ n) := by
        cases Nat.add_left_cancel (k := 0) e₁; cases Nat.add_left_cancel e₂
        exact .rfl
      apply this <;> simp [Nat.add_sub_cancel_left]
  · rw [dif_neg (mt Nat.le_succ_of_le h₁)]
    suffices ∀ k a b (e₁ : k = i+1+a) (e₂ : k = i+b) (n : A F k),
        down F i (downN F a (eqToHom e₁ n)) ≡ downN F b (eqToHom e₂ n) from this ..
    rintro k a b eq rfl n
    rw [Nat.add_assoc, Nat.add_left_cancel_iff, Nat.add_comm] at eq; subst eq
    show _ ≡ downN F a (down F (i+a) n)
    induction a with
    | zero => exact .rfl
    | succ a ih =>
      dsimp [downN, Hom.comp]
      rw [down_eqToHom (Nat.add_right_comm i a 1)]
      apply ih

theorem Tower.embed_up (x : A F k) :
    Tower.embed (k+1) (up F k x) ≡ Tower.embed k x := by
  refine equiv_dist.2 fun n i => ?_
  dsimp [Tower.embed, embed]; split <;> rename_i h₁
  · simp [Nat.le_of_succ_le h₁]
    suffices ∀ a b (e₁ : k + 1 + a = i) (e₂ : k+b = i),
      eqToHom e₁ (upN F a (up F k x)) = eqToHom e₂ (upN F b x) from this .. ▸ .rfl
    rintro a b eq rfl
    rw [Nat.add_right_comm, Nat.add_assoc, Nat.add_left_cancel_iff] at eq; subst b
    show _ = up F (k + a) (upN F a x); clear h₁
    induction a with
    | zero => rfl
    | succ a ih =>
      dsimp [upN, Hom.comp]
      rw [eqToHom_up (by omega : k + 1 + a = k + (a + 1))]; congr 1; apply ih
  · split <;> rename_i h₂
    · cases Nat.le_antisymm h₂ (Nat.not_lt.1 h₁)
      have {a b} {e₁ : k+1 = k+a} {e₂ : k+b = k+0} :
        downN F a (eqToHom e₁ (up F k x)) ≡{n}≡ eqToHom e₂ (upN F b x) := by
        cases Nat.add_left_cancel e₁; cases Nat.add_left_cancel e₂
        exact (down_up ..).dist
      exact this
    · dsimp [Hom.comp]
      suffices ∀ a b (e₁ : k + 1 = i + a) (e₂ : k = i + b),
        downN F a (eqToHom e₁ (up F k x)) ≡{n}≡
        downN F b (eqToHom e₂ x) from this ..
      rintro a b eq rfl; cases Nat.add_left_cancel (m := b+1) eq
      exact (downN ..).ne.1 (down_up x).dist

theorem Tower.embed_self (X : Tower F) :
    Tower.embed (k+1) (X (k+1)) ≡{k}≡ X := by
  refine fun i => ?_
  dsimp [Tower.embed, embed]; split <;> rename_i h₁
  · refine ((eqToHom _).ne.1 (X.upN _)).trans ?_
    suffices ∀ a e, eqToHom e (X a) = X i from this .. ▸ .rfl
    rintro _ rfl; rfl
  · suffices ∀ a e, downN F a (eqToHom e (X (k + 1))) ≡{k}≡ X i from this ..
    rintro (_|a) eq
    · cases show k+1=i from eq; exact .rfl
    · cases show k=i+a from Nat.succ.inj eq
      exact (X.downN _).dist

instance : Inhabited (Tower F) := ⟨Tower.embed 0 ⟨()⟩⟩

def unfoldChain (X : Tower F) : Chain (F (Tower F) (Tower F)) where
  chain n := map (Tower.proj _) (Tower.embed _) (X (n+1))
  cauchy {n i} h := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h; clear h
    induction k with
    | zero => exact .rfl
    | succ k ih =>
      exact (((map ..).ne.1 X.up).le (Nat.le_add_right ..)).symm.trans <|
        (map_comp ..).dist.symm.trans <|
        (map_ne.ne (·.down.dist) (fun Y => (Tower.embed_up Y).dist) _).trans ih

def Tower.iso : OFE.Iso (F (Tower F) (Tower F)) (Tower F) where
  hom.f X := {
    val n := (down F n).comp (map (Tower.embed _) (Tower.proj _)) X
    down {n} := (down ..).ne.eqv <|
      (map_comp ..).symm.trans (map_ne.eqv Tower.embed_up (·.down) _)
  }
  hom.ne.1 _ _ _ h _ := by dsimp only; exact (Hom.ne _).1 h
  inv.f X := compl (unfoldChain X)
  inv.ne.1 n _ _ h := by
    refine conv_compl.trans <| .trans ?_ conv_compl.symm
    exact (map ..).ne.1 (h (n+1))
  hom_inv {X} k := equiv_dist.2 fun n => by
    refine ((down ..).ne.1 (.trans ?_ (X.downN n).dist)).trans X.down.dist
    refine ((map ..).ne.1 (conv_compl.trans
      ((unfoldChain ..).cauchy (show n ≤ k+n+1 by omega)).symm)).trans ?_
    refine (((map ..).comp _).ne.1 (X.up.le (Nat.le_add_left ..)).symm).trans (Equiv.dist ?_)
    refine ((map_comp ..).trans <| (map ..).ne.eqv (map_comp ..)).symm.trans ?_
    refine .trans (y := map (upN F n) (downN F n) (X (k+n+1))) ?_ ?_
    · refine map_ne.eqv (fun Y => ?_) (fun Y => ?_) _
      · simp [Hom.comp, Tower.embed, Tower.proj, embed, (by omega : k ≤ k+n+1)]
        have {a e} : down F (k + n) (eqToHom e (upN F a Y)) ≡ upN F n Y := by
          cases Nat.add_left_cancel (k := n+1) e; exact (down_up _)
        exact this
      · simp [Hom.comp, Tower.embed, Tower.proj, embed, show ¬k+n+1 ≤ k by omega]
        have {a e} : downN F a (eqToHom e (up F (k + n) Y)) ≡ downN F n Y := by
          cases Nat.add_left_cancel (m := n+1) e; exact (downN ..).ne.eqv (down_up _)
        exact this
    · have e : k+n+1 = k+1+n := by omega
      suffices ∀ x y, eqToHom e x = y → map (upN F n) (downN F n) x ≡ downN F n y by
        apply this; clear this; revert e; generalize k+1+n = a; rintro rfl; rfl
      rintro x _ rfl
      induction n with
      | zero => exact map_id
      | succ n ih =>
        refine (map_comp ..).trans <| (ih (Nat.succ.inj e) _).trans ((downN ..).ne.eqv ?_)
        exact .of_eq (down_eqToHom _).symm
  inv_hom := equiv_dist.2 fun n => by
    refine (conv_compl' n.le_succ).trans ?_
    dsimp [unfoldChain]; rw [down]
    refine ((map_comp ..).trans <| (map ..).ne.eqv (map_comp ..)).dist.symm.trans ?_
    refine (map_ne.ne (fun Y => ?_) (fun Y => ?_) _).trans map_id.dist
    · exact ((Tower.embed _).ne.1 Y.up).trans (Y.embed_self.le (by omega))
    · exact ((Tower.embed _).ne.1 Y.down.dist).trans Y.embed_self

end Fix.Impl
open Fix.Impl

variable (F) in
def Fix : Type u := Tower F

instance : Inhabited (Fix F) := inferInstanceAs (Inhabited (Tower F))
instance : COFE (Fix F) := inferInstanceAs (COFE (Tower F))

def Fix.iso : OFE.Iso (F (Fix F) (Fix F)) (Fix F) := Tower.iso

def Fix.fold : F (Fix F) (Fix F) -n> Fix F := Fix.iso.hom
def Fix.unfold : Fix F -n> F (Fix F) (Fix F) := Fix.iso.inv
theorem Fix.fold_unfold (X : Fix F) : Fix.fold (Fix.unfold X) ≡ X := Fix.iso.hom_inv
theorem Fix.unfold_fold (X : F (Fix F) (Fix F)) : Fix.unfold (Fix.fold X) ≡ X := Fix.iso.inv_hom

attribute [irreducible] Fix Fix.fold Fix.unfold Fix.iso
