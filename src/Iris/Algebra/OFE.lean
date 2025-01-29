/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

namespace Iris

/-- Ordered family of equivalences -/
class OFE (α : Type _) where
  Equiv : α → α → Prop
  Dist : Nat → α → α → Prop
  equiv_eqv : Equivalence Equiv
  dist_eqv : Equivalence (Dist n)
  equiv_dist : Equiv x y ↔ ∀ n, Dist n x y
  dist_lt : Dist n x y → m < n → Dist m x y

open OFE

scoped infix:40 " ≡ " => OFE.Equiv
scoped notation:40 x " ≡{" n "}≡ " y:41 => OFE.Dist n x y

namespace OFE

theorem Equiv.rfl [OFE α] {x : α} : x ≡ x := equiv_eqv.1 _
theorem Equiv.symm [OFE α] {x : α} : x ≡ y → y ≡ x := equiv_eqv.2
theorem Equiv.trans [OFE α] {x : α} : x ≡ y → y ≡ z → x ≡ z := equiv_eqv.3
theorem Equiv.dist [OFE α] {x : α} : x ≡ y → x ≡{n}≡ y := (equiv_dist.1 · _)
theorem Equiv.of_eq [OFE α] {x y : α} : x = y → x ≡ y := (· ▸ .rfl)

theorem Dist.lt [OFE α] {m n} {x y : α} : x ≡{n}≡ y → m < n → x ≡{m}≡ y := dist_lt

theorem Dist.le [OFE α] {m n} {x y : α} (h : x ≡{n}≡ y) (h' : m ≤ n) : x ≡{m}≡ y :=
  if hm : m = n then hm ▸ h else h.lt (Nat.lt_of_le_of_ne h' hm)

theorem Dist.rfl [OFE α] {n} {x : α} : x ≡{n}≡ x := dist_eqv.1 _
theorem Dist.symm [OFE α] {n} {x : α} : x ≡{n}≡ y → y ≡{n}≡ x := dist_eqv.2
theorem Dist.trans [OFE α] {n} {x : α} : x ≡{n}≡ y → y ≡{n}≡ z → x ≡{n}≡ z := dist_eqv.3

class NonExpansive [OFE α] [OFE β] (f : α → β) : Prop where
  ne : ∀ ⦃n x₁ x₂⦄, x₁ ≡{n}≡ x₂ → f x₁ ≡{n}≡ f x₂

instance id_ne [OFE α] : NonExpansive (@id α) := ⟨fun _ _ _ h => h⟩

theorem NonExpansive.eqv [OFE α] [OFE β] {f : α → β} [NonExpansive f]
    ⦃x₁ x₂⦄ (h : x₁ ≡ x₂) : f x₁ ≡ f x₂ :=
  equiv_dist.2 fun _ => ne (equiv_dist.1 h _)

class NonExpansive₂ [OFE α] [OFE β] [OFE γ] (f : α → β → γ) : Prop where
  ne : ∀ ⦃n x₁ x₂⦄, x₁ ≡{n}≡ x₂ → ∀ ⦃y₁ y₂⦄, y₁ ≡{n}≡ y₂ → f x₁ y₁ ≡{n}≡ f x₂ y₂

theorem NonExpansive₂.eqv [OFE α] [OFE β] [OFE γ] {f : α → β → γ} [NonExpansive₂ f]
    ⦃x₁ x₂⦄ (hx : x₁ ≡ x₂) ⦃y₁ y₂⦄ (hy : y₁ ≡ y₂) : f x₁ y₁ ≡ f x₂ y₂ :=
  equiv_dist.2 fun _ => ne hx.dist hy.dist

def DistLater [OFE α] (n : Nat) (x y : α) : Prop := ∀ m, m < n → x ≡{m}≡ y

theorem DistLater.rfl [OFE α] {n} {x : α} : DistLater n x x := fun _ _ => .rfl
theorem DistLater.symm [OFE α] {n} {x : α} (h : DistLater n x y) : DistLater n y x :=
  fun _ hm => (h _ hm).symm
theorem DistLater.trans [OFE α] {n} {x : α} (h1 : DistLater n x y) (h2 : DistLater n y z) :
    DistLater n x z := fun _ hm => (h1 _ hm).trans (h2 _ hm)

theorem distLater_eqv [OFE α] {n} : Equivalence (α := α) (DistLater n) where
  refl _ := DistLater.rfl
  symm h := h.symm
  trans h1 := h1.trans

theorem Dist.distLater [OFE α] {n} {x y : α} (h : x ≡{n}≡ y) : DistLater n x y :=
  fun _ => dist_lt h

theorem DistLater.dist_lt [OFE α] {m n} {x y : α} (h : DistLater n x y) (hm : m < n) : x ≡{m}≡ y :=
  h _ hm

theorem distLater_zero [OFE α] {x y : α} : DistLater 0 x y := nofun

theorem distLater_succ [OFE α] {n} {x y : α} : DistLater n.succ x y ↔ x ≡{n}≡ y :=
  ⟨(·.dist_lt (Nat.lt_succ_self _)), fun h1 _ h2 => h1.le (Nat.le_of_lt_succ h2)⟩

class Contractive [OFE α] [OFE β] (f : α → β) : Prop where
  distLater_dist : DistLater n x y → f x ≡{n}≡ f y

theorem Contractive.zero [OFE α] [OFE β] (f : α → β) [Contractive f] {x y} : f x ≡{0}≡ f y :=
  Contractive.distLater_dist distLater_zero

theorem Contractive.succ [OFE α] [OFE β] (f : α → β) [Contractive f] {n x y}
    (h : x ≡{n}≡ y) : f x ≡{n.succ}≡ f y :=
  Contractive.distLater_dist (distLater_succ.2 h)

def ofDiscrete (Equiv : α → α → Prop) (equiv_eqv : Equivalence Equiv) : OFE α where
  Equiv := Equiv
  Dist _ := Equiv
  equiv_eqv := equiv_eqv
  dist_eqv := equiv_eqv
  equiv_dist := (forall_const _).symm
  dist_lt h _ := h

class Discrete (α : Type _) [OFE α] : Prop where
  discrete_0 {x y : α} : x ≡{0}≡ y → x ≡ y

@[ext] structure Hom (α β : Type _) [OFE α] [OFE β] where
  f : α → β
  ne : NonExpansive f

infixr:25 " -n> " => Hom

instance [OFE α] [OFE β] : CoeFun (α -n> β) (fun _ => α → β) := ⟨Hom.f⟩

protected def Hom.id [OFE α] : α -n> α where
  f := id
  ne.ne _ _ _ := id

protected def Hom.comp [OFE α] [OFE β] [OFE γ] (g : β -n> γ) (f : α -n> β) : α -n> γ where
  f := g.f ∘ f.f
  ne.1 _ _ _ h := g.ne.1 (f.ne.1 h)

theorem Hom.comp_assoc [OFE α] [OFE β] [OFE γ] [OFE δ]
    (h : γ -n> δ) (g : β -n> γ) (f : α -n> β) : (h.comp g).comp f = h.comp (g.comp f) := rfl

theorem InvImage.equivalence {α : Sort u} {β : Sort v}
    {r : β → β → Prop} {f : α → β} (H : Equivalence r) : Equivalence (InvImage r f) where
  refl _ := H.refl _
  symm := H.symm
  trans := H.trans

instance : OFE Unit where
  Equiv _ _ := True
  Dist _ _ _ := True
  equiv_eqv := ⟨fun _ => ⟨⟩, id, fun _ => id⟩
  dist_eqv := ⟨fun _ => ⟨⟩, id, fun _ => id⟩
  equiv_dist := by simp
  dist_lt _ _ := ⟨⟩

instance [OFE α] : OFE (ULift α) where
  Equiv x y := x.down ≡ y.down
  Dist n x y := x.down ≡{n}≡ y.down
  equiv_eqv := InvImage.equivalence equiv_eqv
  dist_eqv := InvImage.equivalence dist_eqv
  equiv_dist := equiv_dist
  dist_lt := dist_lt

def uliftUpHom [OFE α] : α -n> ULift α where
  f := .up
  ne.1 _ _ _ := id

def uliftDownHom [OFE α] : ULift α -n> α where
  f := ULift.down
  ne.1 _ _ _ := id

def _root_.Option.Forall₂ (R : α → β → Prop) : Option α → Option β → Prop
  | none, none => True
  | some a, some b => R a b
  | _, _ => False

theorem _root_.Option.Forall₂.equivalence {R : α → α → Prop}
    (H : Equivalence R) : Equivalence (Option.Forall₂ R) where
  refl | none => trivial | some _ => H.1 _
  symm {x y} := by cases x <;> cases y <;> simp [Option.Forall₂]; apply H.2
  trans {x y z} := by cases x <;> cases y <;> cases z <;> simp [Option.Forall₂]; apply H.3

instance [OFE α] : OFE (Option α) where
  Equiv := Option.Forall₂ Equiv
  Dist n := Option.Forall₂ (Dist n)
  equiv_eqv := Option.Forall₂.equivalence equiv_eqv
  dist_eqv := Option.Forall₂.equivalence dist_eqv
  equiv_dist {x y} := by cases x <;> cases y <;> simp [Option.Forall₂]; apply equiv_dist
  dist_lt {_ x y _} := by cases x <;> cases y <;> simp [Option.Forall₂]; apply dist_lt

instance [OFE α] [OFE β] : OFE (α -n> β) where
  Equiv f g := ∀ x, f x ≡ g x
  Dist n f g := ∀ x, f x ≡{n}≡ g x
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

instance [OFE α] [OFE β] : OFE (α × β) where
  Equiv a b := a.1 ≡ b.1 ∧ a.2 ≡ b.2
  Dist n a b := a.1 ≡{n}≡ b.1 ∧ a.2 ≡{n}≡ b.2
  equiv_eqv := {
    refl _ := ⟨equiv_eqv.refl _, equiv_eqv.refl _⟩
    symm h := ⟨equiv_eqv.symm h.1, equiv_eqv.symm h.2⟩
    trans h1 h2 := ⟨equiv_eqv.trans h1.1 h2.1, equiv_eqv.trans h1.2 h2.2⟩
  }
  dist_eqv := {
    refl _ := ⟨dist_eqv.refl _, dist_eqv.refl _⟩
    symm h := ⟨dist_eqv.symm h.1, dist_eqv.symm h.2⟩
    trans h1 h2 := ⟨dist_eqv.trans h1.1 h2.1, dist_eqv.trans h1.2 h2.2⟩
  }
  equiv_dist {_ _} := by simp [equiv_dist, forall_and]
  dist_lt h1 h2 := ⟨dist_lt h1.1 h2, dist_lt h1.2 h2⟩

@[ext] structure Iso (α β : Type _) [OFE α] [OFE β] where
  hom : α -n> β
  inv : β -n> α
  hom_inv : hom (inv x) ≡ x
  inv_hom : inv (hom x) ≡ x

instance [OFE α] [OFE β] : CoeFun (Iso α β) (fun _ => α -n> β) := ⟨Iso.hom⟩

end OFE

structure Chain (α : Type _) [OFE α] where
  chain : Nat → α
  cauchy : n ≤ i → chain i ≡{n}≡ chain n

instance [OFE α] : CoeFun (Chain α) (fun _ => Nat → α) := ⟨Chain.chain⟩

namespace Chain

def map [OFE α] [OFE β] (f : α -n> β) (c : Chain α) : Chain β where
  chain n := f (c n)
  cauchy h := f.ne.1 (c.cauchy h)

end Chain

/-- Complete ordered family of equivalences -/
class IsCOFE (α : Type _) [OFE α] where
  compl : Chain α → α
  conv_compl {c : Chain α} : compl c ≡{n}≡ c n

/-- Complete ordered family of equivalences -/
class abbrev COFE (α : Type _) := OFE α, IsCOFE α

namespace COFE
export IsCOFE (compl conv_compl)

theorem conv_compl' [COFE α] {c : Chain α} {n i} (h : n ≤ i) : compl c ≡{n}≡ c i :=
  conv_compl.trans (c.cauchy h).symm

def ofDiscrete (Equiv : α → α → Prop) (equiv_eqv : Equivalence Equiv) : COFE α :=
  let _ := OFE.ofDiscrete Equiv equiv_eqv
  { compl := fun c => c 0
    conv_compl := fun {_ c} => equiv_eqv.2 (c.cauchy (Nat.zero_le _)) }

instance [COFE α] : COFE (ULift α) where
  compl c := ⟨compl (c.map uliftDownHom)⟩
  conv_compl := conv_compl

instance : COFE Unit where
  compl _ := ()
  conv_compl := ⟨⟩

class OFunctor (F : Type _ → Type _ → Type _) where
  cofe [COFE α] [COFE β] : OFE (F α β)
  map [COFE α₁] [COFE α₂] [COFE β₁] [COFE β₂] :
    (α₂ -n> α₁) → (β₁ -n> β₂) → F α₁ β₁ -n> F α₂ β₂
  map_ne [COFE α₁] [COFE α₂] [COFE β₁] [COFE β₂] :
    NonExpansive₂ (@map α₁ α₂ β₁ β₂ _ _ _ _)
  map_id [COFE α] [COFE β] : map (@Hom.id α _) (@Hom.id β _) x ≡ x
  map_comp [COFE α₁] [COFE α₂] [COFE α₃] [COFE β₁] [COFE β₂] [COFE β₃]
    (f : α₂ -n> α₁) (g : α₃ -n> α₂) (f' : β₁ -n> β₂) (g' : β₂ -n> β₃) (x : F α₁ β₁) :
    map (f.comp g) (g'.comp f') x ≡ map g g' (map f f' x)

class OFunctorContractive (F : Type _ → Type _ → Type _) extends OFunctor F where
  map_contractive [COFE α₁] [COFE α₂] [COFE β₁] [COFE β₂] :
    Contractive (Function.uncurry (@map α₁ α₂ β₁ β₂ _ _ _ _))

attribute [instance] OFunctor.cofe

end COFE
