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
  dist_eqv : Equivalence (Dist n)
  equiv_dist : Equiv x y ↔ ∀ n, Dist n x y
  dist_lt : Dist n x y → m < n → Dist m x y

open OFE

scoped infix:40 " ≡ " => OFE.Equiv
scoped notation:40 x " ≡{" n "}≡ " y:41 => OFE.Dist n x y

namespace OFE

theorem Dist.lt [OFE α] {m n} {x y : α} : x ≡{n}≡ y → m < n → x ≡{m}≡ y := dist_lt

theorem Dist.le [OFE α] {m n} {x y : α} (h : x ≡{n}≡ y) (h' : m ≤ n) : x ≡{m}≡ y :=
  if hm : m = n then hm ▸ h else h.lt (Nat.lt_of_le_of_ne h' hm)

@[simp] theorem Dist.rfl [OFE α] {n} {x : α} : x ≡{n}≡ x := dist_eqv.1 _
theorem Dist.symm [OFE α] {n} {x : α} : x ≡{n}≡ y → y ≡{n}≡ x := dist_eqv.2
theorem Dist.trans [OFE α] {n} {x : α} : x ≡{n}≡ y → y ≡{n}≡ z → x ≡{n}≡ z := dist_eqv.3
theorem Dist.of_eq [OFE α] {x y : α} : x = y → x ≡{n}≡ y := (· ▸ .rfl)

theorem equiv_eqv [ofe : OFE α] : Equivalence ofe.Equiv := by
  constructor
  · rintro x; rw [ofe.equiv_dist]; rintro n; exact Dist.rfl
  · rintro x y; simp [ofe.equiv_dist]; rintro h n; exact Dist.symm (h n)
  · rintro x y z; simp [ofe.equiv_dist]; rintro h₁ h₂ n; exact Dist.trans (h₁ n) (h₂ n)

@[simp] theorem Equiv.rfl [OFE α] {x : α} : x ≡ x := equiv_eqv.1 _
theorem Equiv.symm [OFE α] {x : α} : x ≡ y → y ≡ x := equiv_eqv.2
theorem Equiv.trans [OFE α] {x : α} : x ≡ y → y ≡ z → x ≡ z := equiv_eqv.3
theorem Equiv.dist [OFE α] {x : α} : x ≡ y → x ≡{n}≡ y := (equiv_dist.1 · _)
theorem Equiv.of_eq [OFE α] {x y : α} : x = y → x ≡ y := (· ▸ .rfl)

instance [OFE α]: Trans OFE.Equiv OFE.Equiv (OFE.Equiv : α → α → Prop) where
  trans := Equiv.trans

instance [OFE α]{n: Nat}: Trans (OFE.Dist n) (OFE.Dist n) (OFE.Dist n : α → α → Prop) where
  trans := Dist.trans

/-- A function `f : α → β` is non-expansive if it preserves `n`-equivalence. -/
class NonExpansive [OFE α] [OFE β] (f : α → β) : Prop where
  ne : ∀ ⦃n x₁ x₂⦄, x₁ ≡{n}≡ x₂ → f x₁ ≡{n}≡ f x₂

instance id_ne [OFE α] : NonExpansive (@id α) := ⟨fun _ _ _ h => h⟩

/-- A non-expansive function preserves equivalence. -/
theorem NonExpansive.eqv [OFE α] [OFE β] {f : α → β} [NonExpansive f]
    ⦃x₁ x₂⦄ (h : x₁ ≡ x₂) : f x₁ ≡ f x₂ :=
  equiv_dist.2 fun _ => ne (equiv_dist.1 h _)

/-- A function `f : α → β → γ` is non-expansive if it preserves `n`-equivalence in each argument. -/
class NonExpansive₂ [OFE α] [OFE β] [OFE γ] (f : α → β → γ) : Prop where
  ne : ∀ ⦃n x₁ x₂⦄, x₁ ≡{n}≡ x₂ → ∀ ⦃y₁ y₂⦄, y₁ ≡{n}≡ y₂ → f x₁ y₁ ≡{n}≡ f x₂ y₂

theorem NonExpansive₂.eqv [OFE α] [OFE β] [OFE γ] {f : α → β → γ} [NonExpansive₂ f]
    ⦃x₁ x₂⦄ (hx : x₁ ≡ x₂) ⦃y₁ y₂⦄ (hy : y₁ ≡ y₂) : f x₁ y₁ ≡ f x₂ y₂ :=
  equiv_dist.2 fun _ => ne hx.dist hy.dist

/-- `DistLater n x y` means that `x` and `y` are `m`-equivalent for all `m < n`. -/
def DistLater [OFE α] (n : Nat) (x y : α) : Prop := ∀ m, m < n → x ≡{m}≡ y

@[simp] theorem DistLater.rfl [OFE α] {n} {x : α} : DistLater n x x := fun _ _ => .rfl
theorem DistLater.symm [OFE α] {n} {x : α} (h : DistLater n x y) : DistLater n y x :=
  fun _ hm => (h _ hm).symm
theorem DistLater.trans [OFE α] {n} {x : α} (h1 : DistLater n x y) (h2 : DistLater n y z) :
    DistLater n x z := fun _ hm => (h1 _ hm).trans (h2 _ hm)

/-- `DistLater n`-equivalence is an equivalence relation. -/
theorem distLater_eqv [OFE α] {n} : Equivalence (α := α) (DistLater n) where
  refl _ := DistLater.rfl
  symm h := h.symm
  trans h1 := h1.trans

/-- `n`-equivalence implies `DistLater n`-equivalence. -/
theorem Dist.distLater [OFE α] {n} {x y : α} (h : x ≡{n}≡ y) : DistLater n x y :=
  fun _ => dist_lt h

/-- `DistLater n`-equivalence implies `m`-equivalence for all `m < n`. -/
theorem DistLater.dist_lt [OFE α] {m n} {x y : α} (h : DistLater n x y) (hm : m < n) : x ≡{m}≡ y :=
  h _ hm

/-- `DistLater 0`-equivalence is trivial. -/
@[simp] theorem distLater_zero [OFE α] {x y : α} : DistLater 0 x y := nofun

/-- `DistLater n`-equivalence is equivalent to `(n + 1)`-equivalence. -/
theorem distLater_succ [OFE α] {n} {x y : α} : DistLater n.succ x y ↔ x ≡{n}≡ y :=
  ⟨(·.dist_lt (Nat.lt_succ_self _)), fun h1 _ h2 => h1.le (Nat.le_of_lt_succ h2)⟩

/-- A function `f : α → β` is contractive if it sends `DistLater n`-equivalent inputs to `n`-equivalent outputs. -/
class Contractive [OFE α] [OFE β] (f : α → β) : Prop where
  distLater_dist : DistLater n x y → f x ≡{n}≡ f y

@[simp] theorem Contractive.zero [OFE α] [OFE β] (f : α → β) [Contractive f] {x y} :
    f x ≡{0}≡ f y :=
  Contractive.distLater_dist distLater_zero

theorem Contractive.succ [OFE α] [OFE β] (f : α → β) [Contractive f] {n x y}
    (h : x ≡{n}≡ y) : f x ≡{n.succ}≡ f y :=
  Contractive.distLater_dist (distLater_succ.2 h)

/-- A contractive function is non-expansive. -/
instance [OFE α] [OFE β] (f : α → β) [Contractive f] : NonExpansive f where
  ne := fun _ _ _ h => Contractive.distLater_dist (Dist.distLater h)

/-- A contractive function preserves equivalence. -/
theorem Contractive.eqv [OFE α] [OFE β] (f : α → β) [Contractive f] ⦃x y : α⦄ (h : x ≡ y) :
    f x ≡ f y := NonExpansive.eqv h

/-- Constant functions are contractive. -/
instance [OFE α] [OFE β] {x : β} : Contractive (fun _ : α => x) where
  distLater_dist := fun _ => Dist.rfl

/-- The discrete OFE obtained from an equivalence relation `Equiv` -/
def ofDiscrete (Equiv : α → α → Prop) (equiv_eqv : Equivalence Equiv) : OFE α where
  Equiv := Equiv
  Dist _ := Equiv
  dist_eqv := equiv_eqv
  equiv_dist := (forall_const _).symm
  dist_lt h _ := h

/-- A discrete OFE is one where equivalence is implied by `0`-equivalence. -/
class Discrete (α : Type _) [OFE α] : Prop where
  discrete_0 {x y : α} : x ≡{0}≡ y → x ≡ y

/-- For discrete OFEs, `n`-equivalence implies equivalence for any `n`. -/
theorem Discrete.discrete_n [OFE α] [Discrete α] {n} {x y : α} (h : x ≡{n}≡ y) : x ≡ y :=
  Discrete.discrete_0 (OFE.Dist.le h (Nat.zero_le _))

/-- A morphism between OFEs, written `α -n> β`, is defined to be a function that is non-expansive. -/
@[ext] structure Hom (α β : Type _) [OFE α] [OFE β] where
  f : α → β
  ne : NonExpansive f

@[inherit_doc]
infixr:25 " -n> " => Hom

instance [OFE α] [OFE β] : CoeFun (α -n> β) (fun _ => α → β) := ⟨Hom.f⟩
instance [OFE α] [OFE β] (f : α -n> β) : NonExpansive f := f.ne

/-- The identity morphism on an OFE. -/
protected def Hom.id [OFE α] : α -n> α where
  f := id
  ne.ne _ _ _ := id

/-- The composition of two morphisms between OFEs. -/
protected def Hom.comp [OFE α] [OFE β] [OFE γ] (g : β -n> γ) (f : α -n> β) : α -n> γ where
  f := g.f ∘ f.f
  ne.1 _ _ _ h := g.ne.1 (f.ne.1 h)

@[simp] theorem Hom.id_apply [OFE α] {x} : (Hom.id : α -n> α) x = x := rfl
@[simp] theorem Hom.comp_apply [OFE α] [OFE β] [OFE γ] {g : β -n> γ} {f : α -n> β} {x} :
    (g.comp f) x = g (f x) := rfl

@[simp] theorem Hom.id_comp [OFE α] [OFE β] {f : α -n> β} : Hom.id.comp f = f := rfl
@[simp] theorem Hom.comp_id [OFE α] [OFE β] {f : α -n> β} : f.comp Hom.id = f := rfl

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
  dist_eqv := ⟨fun _ => ⟨⟩, id, fun _ => id⟩
  equiv_dist := by simp
  dist_lt _ _ := ⟨⟩

instance [OFE α] : OFE (ULift α) where
  Equiv x y := x.down ≡ y.down
  Dist n x y := x.down ≡{n}≡ y.down
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
  dist_eqv := Option.Forall₂.equivalence dist_eqv
  equiv_dist {x y} := by cases x <;> cases y <;> simp [Option.Forall₂]; apply equiv_dist
  dist_lt {_ x y _} := by cases x <;> cases y <;> simp [Option.Forall₂]; apply dist_lt

theorem OFE.eqv_of_some_eqv_some [OFE α]{x y: α}(h: some x ≡ some y): x ≡ y := h
theorem OFE.some_eqv_some_of_eqv [OFE α]{x y: α}(h: x ≡ y): some x ≡ some y := h

theorem OFE.equiv_some [OFE α]{o: Option α}{y: α}(e: o ≡ some y)
    : ∃z, o = some z ∧ z ≡ y := by
  unfold OFE.Equiv instOption Option.Forall₂ at e
  match o with
  | .none => dsimp at e
  | .some x => dsimp at e; exact ⟨x, rfl, e⟩

theorem OFE.dist_some_right [OFE α]{n mx y}(h: mx ≡{n}≡ some y)
    : ∃z: α, mx = some z ∧ y ≡{n}≡ z :=
  suffices hh: ∀mx my y, mx ≡{n}≡ my → my = some y → ∃ t, mx = some t ∧ t ≡{n}≡ y
  from (hh mx (some y) _ h rfl).elim (λt h ↦ ⟨t, h.left, h.right.symm⟩)
  λmx _ y e1 e2 ↦
    match mx with
    | .some t => ⟨t, rfl, (e2 ▸ e1: some t ≡{n}≡ some y)⟩
    | .none => False.elim (e2 ▸ e1 : none ≡{n}≡ some y)

instance [OFE α] [OFE β] : OFE (α -n> β) where
  Equiv f g := ∀ x, f x ≡ g x
  Dist n f g := ∀ x, f x ≡{n}≡ g x
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
  dist_eqv := {
    refl _ := ⟨dist_eqv.refl _, dist_eqv.refl _⟩
    symm h := ⟨dist_eqv.symm h.1, dist_eqv.symm h.2⟩
    trans h1 h2 := ⟨dist_eqv.trans h1.1 h2.1, dist_eqv.trans h1.2 h2.2⟩
  }
  equiv_dist {_ _} := by simp [equiv_dist, forall_and]
  dist_lt h1 h2 := ⟨dist_lt h1.1 h2, dist_lt h1.2 h2⟩

/-- An isomorphism between two OFEs is a pair of morphisms whose composition is equivalent to the identity morphism. -/
@[ext] structure Iso (α β : Type _) [OFE α] [OFE β] where
  hom : α -n> β
  inv : β -n> α
  hom_inv : hom (inv x) ≡ x
  inv_hom : inv (hom x) ≡ x

attribute [simp] Iso.hom_inv Iso.inv_hom

instance [OFE α] [OFE β] : CoeFun (Iso α β) (fun _ => α -n> β) := ⟨Iso.hom⟩
instance [OFE α] [OFE β] (iso : Iso α β) : NonExpansive iso.hom := iso.hom.ne
instance [OFE α] [OFE β] (iso : Iso α β) : NonExpansive iso.inv := iso.inv.ne

@[simp] theorem Iso.hom_inv_dist [OFE α] [OFE β] (iso : Iso α β) {n} {x} :
    iso.hom (iso.inv x) ≡{n}≡ x :=
  OFE.equiv_dist.mp (Iso.hom_inv iso) _

@[simp] theorem Iso.inv_hom_dist [OFE α] [OFE β] (iso : Iso α β) {n} {x} :
    iso.inv (iso.hom x) ≡{n}≡ x :=
  OFE.equiv_dist.mp (Iso.inv_hom iso) _

/-- OFE isomorphisms preserve equivalence. -/
theorem Iso.hom_eqv [OFE α] [OFE β] (iso : Iso α β) ⦃x y⦄ :
    x ≡ y ↔ iso.hom x ≡ iso.hom y :=
  ⟨fun h => NonExpansive.eqv h,
  fun h => Equiv.trans (Equiv.symm iso.inv_hom) <| Equiv.trans (NonExpansive.eqv h) (iso.inv_hom)⟩

/-- The inverse of an OFE isomorphism preserves equivalence. -/
theorem Iso.inv_eqv [OFE α] [OFE β] (iso : Iso α β) ⦃x y⦄ :
    x ≡ y ↔ iso.inv x ≡ iso.inv y :=
  ⟨fun h => NonExpansive.eqv h,
  fun h => Equiv.trans (Equiv.symm iso.hom_inv) <| Equiv.trans (NonExpansive.eqv h) (iso.hom_inv)⟩

/-- OFE isomorphisms preserve `n`-equivalence. -/
theorem Iso.hom_dist [OFE α] [OFE β] (iso : Iso α β) {n} ⦃x y⦄ :
    x ≡{n}≡ y ↔ iso.hom x ≡{n}≡ iso.hom y :=
  ⟨fun h => NonExpansive.ne h, fun h => Dist.trans (Dist.symm iso.inv_hom_dist) <|
    Dist.trans (NonExpansive.ne h) (iso.inv_hom_dist)⟩

/-- The inverse of an OFE isomorphism preserves `n`-equivalence. -/
theorem Iso.inv_dist [OFE α] [OFE β] (iso : Iso α β) {n} ⦃x y⦄ :
    x ≡{n}≡ y ↔ iso.inv x ≡{n}≡ iso.inv y :=
  ⟨fun h => NonExpansive.ne h, fun h => Dist.trans (Dist.symm iso.hom_inv_dist) <|
    Dist.trans (NonExpansive.ne h) (iso.hom_inv_dist)⟩

/-- The identity OFE isomorphism -/
def Iso.id [OFE α] : Iso α α where
  hom := Hom.id
  inv := Hom.id
  hom_inv := by intro x; simp
  inv_hom := by intro x; simp

@[simp] theorem Iso.id_apply [OFE α] {x} : ((Iso.id : Iso α α) : α -n> α) x = x := rfl

/-- The inverse of an OFE isomorphism -/
def Iso.symm [OFE α] [OFE β] (iso : Iso α β) : Iso β α where
  hom := iso.inv
  inv := iso.hom
  hom_inv := by intro x; simp
  inv_hom := by intro x; simp

/-- Composition of OFE isomorphisms -/
def Iso.comp [OFE α] [OFE β] [OFE γ] (iso1 : Iso β γ) (iso2 : Iso α β) : Iso α γ where
  hom := iso1.hom.comp iso2.hom
  inv := iso2.inv.comp iso1.inv
  hom_inv := by
    intro x; simp
    exact .trans (NonExpansive.eqv <| .trans iso2.hom_inv .rfl) iso1.hom_inv
  inv_hom := by
    intro x; simp
    exact .trans (NonExpansive.eqv <| .trans iso1.inv_hom .rfl) iso2.inv_hom

end OFE

/-- A chain in an OFE is a `Nat`-indexed sequence of elements that is upward-closed in terms of `n`-equivalence. -/
structure Chain (α : Type _) [OFE α] where
  chain : Nat → α
  cauchy : n ≤ i → chain i ≡{n}≡ chain n

instance [OFE α] : CoeFun (Chain α) (fun _ => Nat → α) := ⟨Chain.chain⟩

namespace Chain

/-- The constant chain. -/
def const [OFE α] (a : α) : Chain α where
  chain := fun _ => a
  cauchy _ := OFE.Dist.rfl

@[simp] theorem const_apply [OFE α] {a : α} {n} : const a n = a := rfl

/-- Mapping a chain through a non-expansive function. -/
def map [OFE α] [OFE β] (f : α -n> β) (c : Chain α) : Chain β where
  chain n := f (c n)
  cauchy h := f.ne.1 (c.cauchy h)

@[simp] theorem map_apply [OFE α] [OFE β] {f : α -n> β} {c : Chain α} {n} :
    map f c n = f (c n) := rfl

@[simp] theorem map_id [OFE α] {c : Chain α} : map (Hom.id : α -n> α) c = c := by
  simp [map]

theorem map_comp [OFE α] [OFE β] [OFE γ] {f : α -n> β} {g : β -n> γ} {c : Chain α} :
    map (g.comp f) c = map g (map f c) := by
  simp [map]

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

/-- Chain maps commute with completion. -/
theorem compl_map [COFE α] [COFE β] (f : α -n> β) (c : Chain α) :
    compl (Chain.map f c) ≡ f (compl c) := by
  refine OFE.equiv_dist.mpr (fun n => ?_)
  exact Dist.trans conv_compl (NonExpansive.ne (Dist.symm conv_compl))

/-- Constant chains complete to their constant value -/
@[simp] theorem compl_const [COFE α] (a : α) : compl (Chain.const a) ≡ a :=
  OFE.equiv_dist.mpr (fun _ => conv_compl)

/-- Completion of discrete COFEs is the constant value. -/
@[simp] theorem discrete_cofe_compl [COFE α] [OFE.Discrete α] (c : Chain α) : compl c ≡ c 0 :=
  Discrete.discrete_0 conv_compl

/-- The discrete COFE obtained from an equivalence relation `Equiv` -/
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
