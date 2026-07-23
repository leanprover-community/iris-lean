/-
Copyright (c) 2025 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Sebastian Graf
-/
module

public import Iris.Algebra.OFE
meta import Iris.Std.RocqPorting

@[expose] public section

#rocq_ignore solution "Use OFE.iso + Inhabited + COFE."

namespace Iris.COFE.OFunctor
open OFE

variable {F : ∀ α β [COFE α] [COFE β], Type u} [OFunctorContractive F]
variable [∀ α [COFE α], IsCOFE (F α α)]
variable [inh : Inhabited (F (ULift Unit) (ULift Unit))]

namespace Fix.Impl

variable (F) in
@[rocq_alias solver.A']
def A' : Nat → Σ α : Type u, COFE α
  | 0 => ⟨ULift Unit, inferInstance⟩
  | n+1 => let ⟨A, _⟩ := A' n; ⟨F A A, inferInstance⟩

variable (F) in
def A (n : Nat) : Type u := (A' F n).1

instance instA' (n) : COFE (A' F n).1 := (A' F n).2
instance instA (n) : COFE (A F n) := (A' F n).2
#rocq_ignore solver.A_cofe "Inference succeeds automatically via `instA`/`instA'`"

variable (F) in
/-- The section/retraction pair at every level, computed by a single recursion so
that evaluating either component at level `k` costs `O(k)` (the naive mutual
recursion recomputes both branches at every level, which is `2^k`). -/
def updown : ∀ k, (A F k -n> A F (k+1)) × (A F (k+1) -n> A F k)
  | 0 => (⟨fun _ => inh.default, ⟨fun _ _ _ _ => .rfl⟩⟩, ⟨fun _ => ⟨()⟩, ⟨fun _ _ _ _ => .rfl⟩⟩)
  | k+1 => let (u, d) := updown k; (map d u, map u d)

variable (F) in
@[rocq_alias solver.f]
def up (k : Nat) : A F k -n> A F (k+1) := (updown F k).1

variable (F) in
-- rocq_alias solver.g
def down (k : Nat) : A F (k+1) -n> A F k := (updown F k).2

#rocq_ignore solver.f_S "Not needed"
#rocq_ignore solver.g_S "Not needed"

@[rocq_alias solver.gf]
theorem down_up : ∀ {k} x, down F k (up F k x) = x
  | 0, ⟨()⟩ => rfl
  | _+1, x => OFE.eq_dist.mpr fun _ => (map_comp _ _ _ _ _).dist.symm.trans <|
    Dist.trans
      (map_ne.ne (fun y => (down_up y).dist) (fun y => (down_up y).dist) x)
      (map_id _).dist

@[rocq_alias solver.fg]
theorem up_down {k} (x) : up F (k+1) (down F (k+1) x) ≡{k}≡ x := by
  refine (map_comp _ _ _ _ _).dist.symm.trans <| .trans ?_ (map_id _).dist
  open OFunctorContractive in exact match k with
  | 0 => map_contractive.zero (x := (_, _)) (y := (_, _)) _ _
  | k+1 => map_contractive.succ (x := (_, _)) (y := (_, _)) _ ⟨up_down, up_down⟩ _

variable (F) in
@[ext, rocq_alias solver.tower]
structure Tower : Type u where
  val k : A F k
  protected down {k} : down F k (val (k+1)) = val k

instance : CoeFun (Tower F) (fun _ => ∀ k, A F k) := ⟨Tower.val⟩

@[rocq_alias solver.T]
instance : OFE (Tower F) where
  Dist n f g := ∀ k, f k ≡{n}≡ g k
  dist_eqv := {
    refl _ _ := dist_eqv.refl _
    symm h _ := dist_eqv.symm (h _)
    trans h1 h2 _ := dist_eqv.trans (h1 _) (h2 _)
  }
  eq_dist {_ _} := by rw [Tower.ext_iff, funext_iff]; simpa only [eq_dist] using forall_comm
  dist_lt h1 h2 _ := dist_lt (h1 _) h2

#rocq_ignore solver.tower_equiv "Included in OFE (Tower F) instance"
#rocq_ignore solver.tower_dist "Included in OFE (Tower F) instance"
#rocq_ignore solver.tower_ofe_mixin "Not needed"

@[rocq_alias solver.tower_chain]
def towerChain (c : Chain (Tower F)) (k : Nat) : Chain (A F k) where
  chain i := c.1 i k
  cauchy h := c.cauchy h k

instance : COFE (Tower F) where
  compl c := by
    refine ⟨fun k => compl ⟨fun i => c.1 i k, fun h => c.cauchy h k⟩, ?_⟩
    refine OFE.eq_dist.mpr (fun n => ?_)
    refine ((down ..).ne.1 conv_compl).trans <| .trans ?_ conv_compl.symm
    exact (c.chain n).down.dist
  conv_compl _ := conv_compl

#rocq_ignore solver.tower_cofe "Use IsCOFE instance"
#rocq_ignore solver.tower_compl "Use IsCOFE instance"
#rocq_ignore solver.tower_car_ne "Use NonExpansive instance"

variable (F) in
@[rocq_alias solver.ff]
def upN {k} : ∀ n, A F k -n> A F (k + n)
  | 0 => .id
  | n+1 => (up F (k + n)).comp (upN n)

variable (F) in
@[rocq_alias solver.gg]
def downN {k} : ∀ n, A F (k + n) -n> A F k
  | 0 => .id
  | n+1 => (downN n).comp (down F (k + n))

@[rocq_alias solver.ggff]
theorem downN_upN {k} (x : A F k) : ∀ {i}, downN F i (upN F i x) = x
  | 0 => rfl
  | n+1 => (congrArg (fun a => (downN F n) a) (down_up _)).trans (downN_upN _)

@[rocq_alias solver.f_tower]
protected theorem Tower.up (X : Tower F) : up F (k+1) (X (k+1)) ≡{k}≡ X (k+2) :=
  ((up ..).ne.1 X.down.symm.dist).trans <| up_down _

@[rocq_alias solver.ff_tower]
protected theorem Tower.upN (X : Tower F) : ∀ i, upN F i (X (k+1)) ≡{k}≡ X (k+1+i)
  | 0 => .rfl
  | n+1 => by
    have : ∀ j, k+n+1 = j → up F j (X j) ≡{k}≡ X (j+1) := by
      rintro _ rfl; exact X.up.le (Nat.le_add_right ..)
    exact ((up ..).ne.1 (X.upN _)).trans <| this _ (Nat.add_right_comm ..)

@[rocq_alias solver.gg_tower]
protected theorem Tower.downN (X : Tower F) : ∀ i, downN F i (X (k+i)) = X k
  | 0 => rfl
  | _+1 => (congrArg (fun a => (downN ..) a) X.down).trans (X.downN _)

instance (k : Nat) : NonExpansive (fun X : Tower F => X.val k) := ⟨fun _ _ _ => (· _)⟩

@[rocq_alias solver.project]
def Tower.proj (k) : Tower F -n> A F k := ⟨(· k), ⟨fun _ _ _ => (· _)⟩⟩

@[rocq_alias solver.coerce]
def eqToHom (e : i = k) : A F i -n> A F k := e ▸ .id

@[rocq_alias solver.coerce_f]
theorem eqToHom_up {k k'} {x : A F k} (e : k = k') :
    eqToHom (congrArg Nat.succ e) (up F k x) = up F k' (eqToHom e x) := by
  cases e; rfl

@[rocq_alias solver.g_coerce]
theorem down_eqToHom {k k'} {x : A F (k+1)} (e : k = k') :
    down F k' (eqToHom (congrArg Nat.succ e) x) = eqToHom e (down F k x) := by
  cases e; rfl

@[rocq_alias solver.embed_coerce]
def embed : A F k -n> A F i :=
  if h : k ≤ i then (eqToHom (Nat.add_sub_cancel' h)).comp (upN ..)
  else (downN ..).comp (eqToHom (Nat.add_sub_cancel' (Nat.le_of_not_ge h)).symm)

#rocq_ignore solver.coerce_id "Not needed"
#rocq_ignore solver.coerce_proper "Inlined in embed"
#rocq_ignore solver.embed_ne "Implicit in embed"

@[rocq_alias solver.embed]
protected def Tower.embed (k) : A F k -n> Tower F := by
  refine ⟨fun n => ⟨fun _ => embed n, fun {i} => ?_⟩, ⟨fun _ _ _ h _ => embed.ne.1 h⟩⟩
  dsimp [embed]; split <;> rename_i h₁
  · split <;> rename_i h₂
    · suffices ∀ a b (e₁ : k+a = i+1) (e₂ : k+b = i),
        down F i (eqToHom e₁ (upN F a n)) = eqToHom e₂ (upN F b n) from this _ _ _ _
      rintro a _ eq rfl
      rw [Nat.add_assoc, Nat.add_left_cancel_iff] at eq; subst a
      exact down_up _
    · cases (Nat.lt_or_eq_of_le h₁).resolve_left (h₂ ∘ Nat.lt_succ_iff.1)
      have {a b} (e₁ : i+1+a = i+1) (e₂ : i+1 = i+b) :
          down F i (eqToHom e₁ (upN F a n)) = downN F b (eqToHom e₂ n) := by
        cases Nat.add_left_cancel (k := 0) e₁; cases Nat.add_left_cancel e₂
        rfl
      apply this <;> simp [Nat.add_sub_cancel_left]
  · rw [dif_neg (mt Nat.le_succ_of_le h₁)]
    suffices ∀ k a b (e₁ : k = i+1+a) (e₂ : k = i+b) (n : A F k),
        down F i (downN F a (eqToHom e₁ n)) = downN F b (eqToHom e₂ n) from this _ _ _ _ _ _
    rintro k a b eq rfl n
    rw [Nat.add_assoc, Nat.add_left_cancel_iff, Nat.add_comm] at eq; subst eq
    show _ = downN F a (down F (i+a) n)
    induction a with
    | zero => rfl
    | succ a ih =>
      dsimp [downN, Hom.comp]
      rw [down_eqToHom (Nat.add_right_comm i a 1)]
      apply ih

@[rocq_alias solver.embed_f]
theorem Tower.embed_up (x : A F k) :
    Tower.embed (k+1) (up F k x) = Tower.embed k x := by
  refine OFE.eq_dist.mpr (fun n i => ?_)
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
        exact (down_up _).dist
      exact this
    · dsimp [Hom.comp]
      suffices ∀ a b (e₁ : k + 1 = i + a) (e₂ : k = i + b),
        downN F a (eqToHom e₁ (up F k x)) ≡{n}≡
        downN F b (eqToHom e₂ x) from this ..
      rintro a b eq rfl; cases Nat.add_left_cancel (m := b+1) eq
      exact (downN ..).ne.1 (down_up x).dist

@[rocq_alias solver.embed_tower]
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
#rocq_ignore solver.tower_inhabited "Implicit in Lean's Inhabited (Tower F) instance"

@[rocq_alias solver.unfold_chain]
def unfoldChain (X : Tower F) : Chain (F (Tower F) (Tower F)) where
  chain n := map (Tower.proj _) (Tower.embed _) (X (n+1))
  cauchy {n i} h := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h; clear h
    induction k with
    | zero => exact .rfl
    | succ k ih =>
      exact (((map ..).ne.1 X.up).le (Nat.le_add_right ..)).symm.trans <|
        (map_comp _ _ _ _ _).dist.symm.trans <|
        (map_ne.ne (·.down.dist) (fun Y => (Tower.embed_up Y).dist) _).trans ih

def Tower.isoAux : OFE.Iso (F (Tower F) (Tower F)) (Tower F) where
  hom.f X := {
    val n := (down F n).comp (map (Tower.embed _) (Tower.proj _)) X
    down {n} := OFE.eq_dist.mpr fun m => (down ..).ne.1 <|
      (map_comp _ _ _ _ _).dist.symm.trans <|
        map_ne.ne (fun Y => (Tower.embed_up Y).dist) (fun Y => Y.down.dist) _
  }
  hom.ne.1 _ _ _ h _ := by dsimp only; exact (Hom.ne _).1 h
  inv.f X := compl (unfoldChain X)
  inv.ne.1 n _ _ h := by
    refine conv_compl.trans <| .trans ?_ conv_compl.symm
    exact (map ..).ne.1 (h (n+1))
  hom_inv {X} := OFE.eq_dist.mpr fun n => by
    intro k
    refine ((down ..).ne.1 (.trans ?_ (X.downN n).dist)).trans X.down.dist
    refine ((map ..).ne.1 (conv_compl.trans
      ((unfoldChain ..).cauchy (show n ≤ k+n+1 by omega)).symm)).trans ?_
    refine (((map ..).comp _).ne.1 (X.up.le (Nat.le_add_left ..)).symm).trans (Equiv.dist ?_)
    refine (OFE.equiv_iff_eq.mpr ((map_comp _ _ _ _ _).trans
      (congrArg (fun a => (map ..) a) (map_comp _ _ _ _ _)))).symm.trans ?_
    refine .trans (y := map (upN F n) (downN F n) (X (k+n+1))) ?_ ?_
    · refine fun m => map_ne.ne (fun Y => ?_) (fun Y => ?_) _
      · simp [Hom.comp, Tower.embed, Tower.proj, embed, (by omega : k ≤ k+n+1)]
        have {a e} : down F (k + n) (eqToHom e (upN F a Y)) = upN F n Y := by
          cases Nat.add_left_cancel (k := n+1) e; exact down_up _
        exact this.dist
      · simp [Hom.comp, Tower.embed, Tower.proj, embed, show ¬k+n+1 ≤ k by omega]
        have {a e} : downN F a (eqToHom e (up F (k + n) Y)) = downN F n Y := by
          cases Nat.add_left_cancel (m := n+1) e; exact congrArg (fun a => (downN ..) a) (down_up _)
        exact this.dist
    · have e : k+n+1 = k+1+n := by omega
      suffices ∀ x y, eqToHom e x = y → map (upN F n) (downN F n) x ≡ downN F n y by
        apply this; clear this; revert e; generalize k+1+n = a; rintro rfl; rfl
      rintro x _ rfl
      induction n with
      | zero => exact OFE.equiv_iff_eq.mpr (map_id _)
      | succ n ih =>
        refine (OFE.equiv_iff_eq.mpr (map_comp _ _ _ _ _)).trans <|
          (ih (Nat.succ.inj e) _).trans (OFE.equiv_iff_eq.mpr (congrArg (fun a => (downN ..) a) ?_))
        exact (down_eqToHom _).symm
  inv_hom := OFE.eq_dist.mpr fun n => by
    refine (conv_compl' n.le_succ).trans ?_
    dsimp [unfoldChain]; rw [down]
    refine ((map_comp _ _ _ _ _).trans
      (congrArg (fun a => (map ..) a) (map_comp _ _ _ _ _))).dist.symm.trans ?_
    refine (map_ne.ne (fun Y => ?_) (fun Y => ?_) _).trans (map_id _).dist
    · exact ((Tower.embed _).ne.1 Y.up).trans (Y.embed_self.le (by omega))
    · exact ((Tower.embed _).ne.1 Y.down.dist).trans Y.embed_self

opaque Tower.iso : OFE.Iso (F (Tower F) (Tower F)) (Tower F) := Tower.isoAux

end Fix.Impl
open Fix.Impl

#rocq_ignore solver.result "Use `Fix F` with Inhabited + COFE instances and Fix.iso"

variable (F) in
def Fix : Type u := Tower F

instance : Inhabited (Fix F) := inferInstanceAs (Inhabited (Tower F))
instance : COFE (Fix F) := inferInstanceAs (COFE (Tower F))

def Fix.iso : OFE.Iso (F (Fix F) (Fix F)) (Fix F) := Tower.iso

@[rocq_alias solver.fold]
def Fix.fold : F (Fix F) (Fix F) -n> Fix F := Fix.iso.hom
#rocq_ignore solver.fold_ne "Implicit in the OFE.Iso structure"
@[rocq_alias solver.unfold]
def Fix.unfold : Fix F -n> F (Fix F) (Fix F) := Fix.iso.inv
#rocq_ignore solver.unfold_ne "Implicit in the OFE.Iso structure"
theorem Fix.fold_unfold (X : Fix F) : Fix.fold (Fix.unfold X) = X := Fix.iso.hom_inv
theorem Fix.unfold_fold (X : F (Fix F) (Fix F)) : Fix.unfold (Fix.fold X) = X :=
  Fix.iso.inv_hom

attribute [irreducible] Fix Fix.fold Fix.unfold Fix.iso
