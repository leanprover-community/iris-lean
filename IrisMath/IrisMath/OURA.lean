/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Shing Hin Ho, František Silváši, Julian Sutherland
-/
module

public import Iris.Algebra.CMRA
public import Iris.BI.BI
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Data.Setoid.Basic
public import Mathlib.Order.UpperLower.CompleteLattice

/-!
# Ordered unital resource algebras

An *ordered unital resource algebra* (OURA) is a commutative monoid with a preorder and a
validity predicate `✓`, in which `1` is valid, validity is downward closed, and validity of a
product cancels on the right.  Such an algebra carries no step-indexing, so it is a discrete
CMRA (`instCMRA`, via `CMRA.ofDiscreteTotal`) and in fact a `UCMRA` (`instUCMRA`).

The upper sets of an OURA model a separation logic: `UpperSet M` is closed under the usual
connectives (`and`, `or`, `imp`, `sep`, `wand`, `persistently`, `pure`, `emp`, `sForall`,
`sExists`), and `entail` orders them.  Quotienting by mutual entailment (`bientail`) yields
`OURAProp M`, which is a `BI` -- the main result of this file.

## Main definitions

* `OrderedUnitalResourceAlgebra` : the algebra
* `UpperSetBI.entail` / `UpperSetBI.bientail` : entailment and its symmetrization
* `UpperSetBI.OURAProp` : upper sets up to mutual entailment, a `BI`
-/

@[expose] public section

namespace Iris

/-- An ordered unital resource algebra is a type with a multiplication, a one, a preorder `≤`,
  and a validity predicate `✓`, such that:

  - `1` is valid
  - validity is downward closed: `a ≤ b → ✓ b → ✓ a`
  - validity of multiplication cancels on the right: `✓ (a * b) → ✓ a`
  - multiplication on the right is monotone: `a ≤ b → a * c ≤ b * c` -/
class OrderedUnitalResourceAlgebra (M : Type*) extends
    CommMonoid M, Preorder M, MulRightMono M where
  /-- The validity predicate, written `✓`. -/
  valid : M → Prop
  valid_one : valid (1 : M)
  valid_mono {a b : M} : a ≤ b → valid b → valid a
  valid_mul {a b : M} : valid (a * b) → valid a

export OrderedUnitalResourceAlgebra (valid valid_one valid_mono valid_mul)

attribute [simp] valid_one

namespace OrderedUnitalResourceAlgebra

section

variable {I M : Type*} [OrderedUnitalResourceAlgebra M]

instance : MulRightMono M := ⟨fun _ _ _ h ↦ mul_left_mono h⟩

/-- A resource algebra on `M` is lifted pointwise to a resource algebra on `I → M`,
validity being required of every component. -/
instance {I : Type*} : OrderedUnitalResourceAlgebra (I → M) where
  valid x := ∀ i, valid (x i)
  valid_one := by intro i; exact valid_one
  valid_mono := by intro _ _ hab hb i; exact valid_mono (hab i) (hb i)
  valid_mul := by intro _ _ hab i; exact valid_mul (hab i)
  elim := by intro _ _ _ h; exact fun i => mul_left_mono (h i)

/-- An ordered unital resource algebra does not care about step-indexing, so it carries the
discrete OFE. -/
instance instOFE : OFE M := OFE.ofDiscrete M

instance instOFEDiscrete : OFE.Discrete M := ⟨id⟩

/-- An ordered unital resource algebra is a discrete CMRA whose core is the unit. -/
instance instCMRA : CMRA M :=
  CMRA.ofDiscreteTotal (fun _ ↦ 1) (· * ·) valid
    (fun x y z ↦ (mul_assoc x y z).symm) mul_comm one_mul (fun _ ↦ rfl)
    (fun _ _ _ ↦ ⟨1, (one_mul 1).symm⟩) (fun _ _ ↦ valid_mul)

@[simp]
abbrev carrier := M

end

@[reducible]
def subalgebra
  {α : Type*} {p : α → Prop} (i : OrderedUnitalResourceAlgebra α)
  (hu : p i.one) (hc : ∀ x y : α, p x → p y → p (i.mul x y))
  : OrderedUnitalResourceAlgebra {x : α // p x} := {
  valid x := i.valid x.val
  mul x y := ⟨i.mul x.val y.val, hc x.val y.val x.property y.property⟩
  mul_assoc x y z := by
    have : (x.val * y.val) * z.val = x.val * (y.val * z.val) := by grind
    aesop
  one := ⟨i.one, hu⟩
  one_mul := by
    rintro ⟨x, hx⟩
    have : i.one * x = x := by apply i.one_mul
    aesop
  mul_one := by
    rintro ⟨x, hx⟩
    have : x * i.one = x := by apply i.mul_one
    aesop
  mul_comm := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    have : x * y = y * x := by apply i.mul_comm
    aesop
  elim := by
    intro a b c h
    have := i.elim
    aesop
  valid_one := by apply i.valid_one
  valid_mono := by
    intro a b h
    have := @i.valid_mono a b h
    aesop
  valid_mul := by
    intro a b h
    have := @i.valid_mul a b h
    aesop
}

@[reducible]
def indexedProduct
  {I : Type*} {α : I → Type _}
  (f : (i : I) → OrderedUnitalResourceAlgebra (α i))
  : OrderedUnitalResourceAlgebra ((i : I) → α i) := {
  mul x y i := (f i).mul (x i) (y i)
  mul_assoc x y z := by funext; simp; grind
  one i := (f i).one
  one_mul x := by simp
  mul_one x := by simp
  mul_comm x y := by funext; simp; grind
  valid x := ∀ i : I, (f i).valid (x i)
  le x y := ∀ i : I, (f i).le (x i) (y i)
  le_refl x i := by grind
  le_trans x y z h₁ h₂ := by grind
  elim := by intro a b c h i; unfold Function.swap; simp; have := (f i).elim; aesop
  valid_one i := by aesop
  valid_mono x y i := by have := fun i ↦ (f i).valid_mono (x i) (y i); aesop
  valid_mul x := by have := fun i ↦ (f i).valid_mul (x i); aesop
  npow_zero := by simp
  npow_succ n x := by funext i; exact @pow_succ (α i) (f i).toMonoid (x i) n
}

/-- Technically binary product is just an instnace of indexed product, but
    it is convenient to redefine it -/
@[reducible]
def product
  {α β : Type*}
  (r₁ : OrderedUnitalResourceAlgebra α) (r₂ : OrderedUnitalResourceAlgebra β)
  : OrderedUnitalResourceAlgebra (α × β) := {
  valid x := r₁.valid x.1 ∧ r₂.valid x.2
  elim := by
    intro a b c h
    unfold Function.swap
    simp_all
    obtain ⟨a₁, a₂⟩ := a
    obtain ⟨b₁, b₂⟩ := b
    obtain ⟨c₁, c₂⟩ := c
    simp_all
    constructor
    · have := @r₁.elim a₁ b₁ c₁ h.1
      aesop
    · have := @r₂.elim a₂ b₂ c₂ h.2
      aesop
  valid_one := by constructor <;> aesop
  valid_mono := by
    intro a b h₁ h₂
    obtain ⟨a₁, a₂⟩ := a
    obtain ⟨b₁, b₂⟩ := b
    have : r₁.valid a₁ := @r₁.valid_mono a₁ b₁ h₁.1 h₂.1
    have : r₂.valid a₂ := @r₂.valid_mono a₂ b₂ h₁.2 h₂.2
    constructor <;> aesop
  valid_mul := by
    intro a b h
    obtain ⟨a₁, a₂⟩ := a
    obtain ⟨b₁, b₂⟩ := b
    simp_all
    have : r₁.valid a₁ := @r₁.valid_mul a₁ b₁ h.1
    have : r₂.valid a₂ := @r₂.valid_mul a₂ b₂ h.2
    constructor <;> aesop
}

@[simp]
def quotientMul
  {α : Type*} {R : Setoid α} {ra : OrderedUnitalResourceAlgebra α}
  (hclo : (p₁ q₁ p₂ q₂ : α) → (h₁ : R p₁ p₂) → (h₂ : R q₁ q₂) →
    R (ra.mul p₁ q₁) (ra.mul p₂ q₂)) (p q : Quotient R)
  : Quotient R :=
  Quotient.lift₂ (f := fun x y ↦ ⟦ra.mul x y⟧) (by
    intro p₁ q₁ p₂ q₂ hp hq
    have := hclo p₁ q₁ p₂ q₂ hp hq
    exact Quot.sound this) p q

@[simp]
def quotientOne
  {α : Type*} {R : Setoid α} (ra : OrderedUnitalResourceAlgebra α)
  : Quotient R := ⟦ra.one⟧

lemma quotientMul_injective
  {α : Type*} {R : Setoid α} {ra : OrderedUnitalResourceAlgebra α}
  (hclo : (p₁ q₁ p₂ q₂ : α) → (h₁ : R p₁ p₂) → (h₂ : R q₁ q₂) → R (p₁ * q₁) (p₂ * q₂))
  {p q r : Quotient R} (h : p.out * q.out = r.out)
  : quotientMul hclo p q = r := by
  have h₁ : quotientMul hclo ⟦p.out⟧ ⟦q.out⟧ = ⟦p.out * q.out⟧ := rfl
  rw [Quotient.out_eq p, Quotient.out_eq q] at h₁
  rw [h₁, h, Quotient.out_eq]

lemma quotientMul_commutes_out_singleton
  {α : Type*} {R : Setoid α} {ra : OrderedUnitalResourceAlgebra α}
  (hclo : (p₁ q₁ p₂ q₂ : α) → (h₁ : R p₁ p₂) → (h₂ : R q₁ q₂) → R (p₁ * q₁) (p₂ * q₂))
  (x y : α)
  : R ((Quot.mk R x).out * (Quot.mk R y).out) ((quotientMul hclo ⟦x⟧ ⟦y⟧).out) := by
  have : R x (Quot.mk (⇑R) x).out := by
    apply Quotient.exact; symm; exact Quotient.out_eq _
  have : R y (Quot.mk (⇑R) y).out := by
    apply Quotient.exact; symm; exact Quotient.out_eq _
  have h₁ := hclo x y (Quot.mk R x).out (Quot.mk R y).out (by assumption) (by assumption)
  have h₂ : R (x * y) (Quot.mk R (x * y)).out := by
    apply Quotient.exact
    symm
    apply Quot.out_eq _
  apply R.symm
  apply R.symm at h₂
  have := R.trans h₂ h₁
  aesop

lemma quotientMul_commutes_out
  {α : Type*} {R : Setoid α} {ra : OrderedUnitalResourceAlgebra α}
  (hclo : (p₁ q₁ p₂ q₂ : α) → (h₁ : R p₁ p₂) → (h₂ : R q₁ q₂) → R (p₁ * q₁) (p₂ * q₂))
  (p q : Quotient R)
  : R (p.out * q.out) ((quotientMul hclo p q).out) := by
  have := @Quot.induction_on₂ α α (r := R) (s := R)
    (δ := fun p q ↦ R (ra.mul p.out q.out) ((quotientMul hclo p q).out))
    (q₁ := p) (q₂ := q) (by
      have := quotientMul_commutes_out_singleton hclo
      aesop)
  have : R (p.out * q.out) (quotientMul hclo p q).out := by aesop
  assumption

@[reducible]
def quotient
  {α : Type*} {R : Setoid α} {ra : OrderedUnitalResourceAlgebra α}
  (hclo : (p₁ q₁ p₂ q₂ : α) → (h₁ : R p₁ p₂) → (h₂ : R q₁ q₂) → R (p₁ * q₁) (p₂ * q₂))
  (hvalid : (x x' : α) → R x x' → ra.valid x → ra.valid x')
  (hle : (x x' y y' : α) → x ≤ y → R x x' → R y y' → x' ≤ y')
  : OrderedUnitalResourceAlgebra (Quotient R) := {
  mul := quotientMul hclo
  mul_assoc := by
    intro p q r
    apply Quot.induction_on₃ (δ := fun p q r ↦
      quotientMul hclo (quotientMul hclo p q) r =
        quotientMul hclo p (quotientMul hclo q r)) p
    intro a b c
    have h : Mul.mul (Mul.mul a b) c = Mul.mul a (Mul.mul b c) := by
      apply ra.mul_assoc a b c
    conv_rhs => simp; rw [← h]
    rfl
  one := quotientOne (R := R) ra
  one_mul := by
    intro p
    simp only [OfNat.ofNat, quotientOne]
    apply Quot.induction_on (r := R) (β := fun p ↦ quotientMul hclo ⟦One.one⟧ p = p) p
    intro a
    apply Quot.sound
    have : ra.mul One.one a = a := by
      have := ra.one_mul a
      assumption
    aesop
  mul_one := by
    intro p
    simp only [OfNat.ofNat, quotientOne]
    apply Quot.induction_on (r := R) (β := fun p ↦ quotientMul hclo p ⟦One.one⟧ = p) p
    intro a
    apply Quot.sound
    have : ra.mul a One.one = a := by
      have := ra.mul_one a
      assumption
    aesop
  mul_comm := by
    intro p q
    apply Quot.induction_on₂ (δ := fun p q ↦ quotientMul hclo p q = quotientMul hclo q p) p q
    intro a b
    apply Quot.sound
    have : a * b = b * a := ra.mul_comm a b
    simp only [HMul.hMul] at this
    rw [this]
  valid x := ∀ x' : α, ⟦x'⟧ = x → ra.valid x'
  le p q := ∀ p' q' : α, ⟦p'⟧ = p → ⟦q'⟧ = q → p' ≤ q'
  le_refl := by
    intro x p q h₁ h₂
    have hx : ⟦x.out⟧ = x := Quotient.out_eq x
    rw [← hx] at h₁ h₂
    apply hle x.out p x.out q (by aesop)
    · have := Quotient.exact h₁
      exact id (Setoid.symm this)
    · have := Quotient.exact h₂
      exact id (Setoid.symm this)
  le_trans := by
    intro a b c hab hbc p' q' h₁ h₂
    have hab' : a.out ≤ b.out := hab a.out b.out (Quotient.out_eq a) (Quotient.out_eq b)
    have hbc' : b.out ≤ c.out := hbc b.out c.out (Quotient.out_eq b) (Quotient.out_eq c)
    have : a.out ≤ c.out := ra.le_trans a.out b.out c.out hab' hbc'
    apply hle a.out p' c.out q' this
    · have : ⟦a.out⟧ = a := Quotient.out_eq a
      rw [← this] at h₁
      apply Quotient.exact (by aesop)
    · have : ⟦c.out⟧ = c := Quotient.out_eq c
      rw [← this] at h₂
      apply Quotient.exact (by aesop)
  elim := by
    simp only [Covariant, Function.swap]
    intro m n₁ n₂ h p' q' hp hq
    have helim := @ra.elim m.out n₁.out n₂.out
    simp only [Function.swap] at helim
    have : n₁.out ≤ n₂.out := by aesop
    have : n₁.out * m.out ≤ n₂.out * m.out := by aesop
    apply hle (n₁.out * m.out) p' (n₂.out * m.out) q' (by assumption)
    · have h₁ := quotientMul_commutes_out hclo n₁ m
      have h₂ : R (quotientMul hclo n₁ m).out p' := by
        have h₃ : ⟦(quotientMul hclo n₁ m).out⟧ = quotientMul hclo n₁ m :=
          Quotient.out_eq _
        have : Quot.mk R p' = ⟦(quotientMul hclo n₁ m).out⟧ := by
          rw [h₃]
          aesop
        have := Quotient.exact this
        apply Quotient.exact
        aesop
      have h₃ : R (n₁.out * m.out) p' := R.trans h₁ h₂
      assumption
    · have h₁ := quotientMul_commutes_out hclo n₂ m
      have h₂ : R (quotientMul hclo n₂ m).out q' := by
        have h₃ : ⟦(quotientMul hclo n₂ m).out⟧ = quotientMul hclo n₂ m :=
          Quotient.out_eq _
        have : Quot.mk R q' = ⟦(quotientMul hclo n₂ m).out⟧ := by
          rw [h₃]
          aesop
        have := Quotient.exact this
        apply Quotient.exact
        aesop
      have h₃ : R (n₂.out * m.out) q' := R.trans h₁ h₂
      assumption
  valid_one := by
    intro o ho
    simp only [OfNat.ofNat, One.one, quotientOne] at ho
    have : R o One.one := Quotient.exact ho
    apply hvalid One.one o (R.symm this)
    exact ra.valid_one
  valid_mono := by
    intro a b h₁ h₂ x hx
    have ha : ⟦a.out⟧ = a := Quotient.out_eq a
    have hb : ⟦b.out⟧ = b := Quotient.out_eq b
    have := ra.valid_mono (a := a.out) (b := b.out)
    have : ra.valid a.out := by
      have : a.out ≤ b.out := h₁ a.out b.out ha hb
      have : ra.valid b.out := h₂ b.out hb
      aesop
    have : R x a.out := by
      rw [← ha] at hx
      exact Quotient.exact (by assumption)
    have := hvalid a.out x (R.symm (by assumption)) (by assumption)
    assumption
  valid_mul := by
    intro a b h x hx
    have ha : ⟦a.out⟧ = a := Quotient.out_eq a
    have := ra.valid_mul (a := a.out) (b := b.out)
    have : ra.valid a.out := by
      have : R (a.out * b.out) (quotientMul hclo a b).out := quotientMul_commutes_out hclo a b
      have : ⟦a.out * b.out⟧ = quotientMul hclo a b := by
        have := Quotient.sound this
        have : ⟦(quotientMul hclo a b).out⟧ = quotientMul hclo a b := Quotient.out_eq _
        aesop
      have := h (a.out * b.out) (by aesop)
      aesop
    rw [← ha] at hx
    have : R x a.out := Quotient.exact (by assumption)
    have := hvalid a.out x (R.symm (by assumption)) (by assumption)
    assumption
}

instance instUCMRA
  {M : Type*} [ra : OrderedUnitalResourceAlgebra M]
  : Iris.UCMRA M := {
  unit := ra.one
  unit_valid := ra.valid_one
  unit_left_id := by
    intro x
    have : One.one * x = x := by change 1 * x = x; aesop
    aesop
  pcore_unit := by rfl
}

end OrderedUnitalResourceAlgebra

namespace UpperSetBI

variable {M : Type} [OrderedUnitalResourceAlgebra M]

def pure (φ : Prop) : UpperSet M := {
  carrier := {x | φ}
  upper' := by aesop
}

def own (b : M) : UpperSet M := {
  carrier := {a | b ≤ a}
  upper' := by
    intro x y h₁ h₂
    have : b ≤ x := by aesop
    have : b ≤ y := by grind
    aesop
}

def and (P Q : UpperSet M) : UpperSet M := {
  carrier := {a | a ∈ P ∧ a ∈ Q}
  upper' := by
    intro x y h₁ h₂
    have := P.upper'
    have := Q.upper'
    aesop
}

def or (P Q : UpperSet M) : UpperSet M := {
  carrier := {a | a ∈ P ∨ a ∈ Q}
  upper' := by
    intro x y h₁ h₂
    have := P.upper'
    have := Q.upper'
    aesop
}

def sep (P Q : UpperSet M) : UpperSet M := {
  carrier := {a | ∃ (b₁ b₂ : M), (b₁ * b₂) ≤ a ∧ b₁ ∈ P ∧ b₂ ∈ Q}
  upper' := by
    intro a b h₁ h₂
    grind
}

def entail (P Q : UpperSet M) : Prop :=
  ∀ m, ✓m → m ∈ P → m ∈ Q

def bientail (P Q : UpperSet M) : Prop :=
  entail P Q ∧ entail Q P

@[simp, grind .]
lemma entail_refl {x : UpperSet M} : entail x x := by simp [entail]

@[simp, grind .]
lemma entail_trans {x y z : UpperSet M} :
  entail x y → entail y z → entail x z := by grind [entail]

@[simp, grind .]
lemma bientail_refl {x : UpperSet M} : bientail x x := by simp [bientail]

@[simp, grind .]
lemma bientail_symm {x y : UpperSet M} :
  bientail x y → bientail y x := by grind [bientail]

@[simp, grind .]
lemma bientail_trans {x y z : UpperSet M} :
  bientail x y → bientail y z → bientail x z := by grind [bientail]


def sForall (Ψ : UpperSet M → Prop) : UpperSet M := {
  carrier := {a | ∀ p, Ψ p → a ∈ p}
  upper' := by
    intro a b hle ha p hΨ
    exact p.upper' hle (ha p hΨ)
}

def sExists (Ψ : UpperSet M → Prop) : UpperSet M := {
  carrier := {a | ∃ p, Ψ p ∧ a ∈ p}
  upper' := by
    intro a b hle ⟨p, hΨ, hpa⟩
    exact ⟨p, hΨ, p.upper' hle hpa⟩
}

def persistently (P : UpperSet M) : UpperSet M := {
  carrier := {_a | 1 ∈ P}
  upper' := by intro _ _ _ h; exact h
}

@[simp]
def wand (P Q : UpperSet M) : UpperSet M := {
  carrier := {a | ∀ b, ✓ (a * b) → b ∈ P → (a * b) ∈ Q}
  upper' := by
    intro a c hac ha b hvcb hPb
    have hab : a * b ≤ c * b := mul_left_mono hac
    have hvab : ✓ (a * b) := valid_mono hab hvcb
    exact Q.upper' hab (ha b hvab hPb)
}

@[simp]
def imp (P Q : UpperSet M) : UpperSet M := {
  carrier := {a | ∀ b, a ≤ b → ✓ b → b ∈ P → b ∈ Q}
  upper' := by
    intro a c hac ha b hcb hvb hPb
    exact ha b (le_trans hac hcb) hvb hPb
}

@[simp]
def emp : UpperSet M := {
  carrier := {a | 1 ≤ a}
  upper' := by
    intro a b hle ha
    simp only [Set.mem_ofPred_eq] at *
    apply le_trans <;> aesop
}

/-! ### Basic algebraic helpers -/

lemma valid_mul_l {a b : M} (h : ✓ (a * b)) : ✓ a := valid_mul h

lemma valid_mul_r {a b : M} (h : ✓ (a * b)) : ✓ b := by
  rw [mul_comm] at h
  exact valid_mul h

lemma mul_le_mul_right_le {a b : M} (h : a ≤ b) (c : M) : a * c ≤ b * c :=
  mul_left_mono (a := c) h

lemma mul_le_mul_left_le {a b : M} (h : a ≤ b) (c : M) : c * a ≤ c * b := by
  rw [mul_comm c a, mul_comm c b]
  exact mul_left_mono (a := c) h

/-! ### The BI laws, stated on representatives -/

lemma entail_pure_intro {φ : Prop} {P : UpperSet M} (h : φ) : entail P (pure φ) :=
  fun _ _ _ ↦ h

lemma entail_pure_elim' {φ : Prop} {P : UpperSet M}
    (h : φ → entail (pure True) P) : entail (pure φ) P :=
  fun m hm hφ ↦ h hφ m hm trivial

lemma entail_and_elim_l {P Q : UpperSet M} : entail (and P Q) P :=
  fun _ _ h ↦ h.1

lemma entail_and_elim_r {P Q : UpperSet M} : entail (and P Q) Q :=
  fun _ _ h ↦ h.2

lemma entail_and_intro {P Q R : UpperSet M} (h₁ : entail P Q) (h₂ : entail P R) :
    entail P (and Q R) :=
  fun m hm h ↦ ⟨h₁ m hm h, h₂ m hm h⟩

lemma entail_or_intro_l {P Q : UpperSet M} : entail P (or P Q) :=
  fun _ _ h ↦ Or.inl h

lemma entail_or_intro_r {P Q : UpperSet M} : entail Q (or P Q) :=
  fun _ _ h ↦ Or.inr h

lemma entail_or_elim {P Q R : UpperSet M} (h₁ : entail P R) (h₂ : entail Q R) :
    entail (or P Q) R :=
  fun m hm h ↦ h.elim (h₁ m hm) (h₂ m hm)

lemma entail_imp_intro {P Q R : UpperSet M} (h : entail (and P Q) R) :
    entail P (imp Q R) :=
  fun _ _ hP b hle hv hQ ↦ h b hv ⟨P.upper' hle hP, hQ⟩

lemma entail_imp_elim {P Q R : UpperSet M} (h : entail P (imp Q R)) :
    entail (and P Q) R :=
  fun m hm hPQ ↦ h m hm hPQ.1 m (le_refl m) hm hPQ.2

lemma entail_sep_mono {P P' Q Q' : UpperSet M} (h : entail P Q) (h' : entail P' Q') :
    entail (sep P P') (sep Q Q') := by
  rintro m hm ⟨b₁, b₂, hle, hb₁, hb₂⟩
  have hv : ✓ (b₁ * b₂) := valid_mono hle hm
  exact ⟨b₁, b₂, hle, h b₁ (valid_mul_l hv) hb₁, h' b₂ (valid_mul_r hv) hb₂⟩

lemma entail_emp_sep_l {P : UpperSet M} : entail (sep emp P) P := by
  rintro m hm ⟨b₁, b₂, hle, hb₁, hb₂⟩
  have h₁ : b₂ ≤ b₁ * b₂ := by simpa using mul_le_mul_right_le hb₁ b₂
  exact P.upper' (le_trans h₁ hle) hb₂

lemma entail_emp_sep_r {P : UpperSet M} : entail P (sep emp P) :=
  fun m _ hP ↦ ⟨1, m, le_of_eq (one_mul m), le_refl 1, hP⟩

lemma entail_sep_symm {P Q : UpperSet M} :
    entail (sep P Q) (sep Q P) := by
  rintro m _ ⟨b₁, b₂, hle, hb₁, hb₂⟩
  exact ⟨b₂, b₁, by rwa [mul_comm], hb₂, hb₁⟩

lemma entail_sep_assoc_l {P Q R : UpperSet M} :
    entail (sep (sep P Q) R) (sep P (sep Q R)) := by
  rintro m _ ⟨c₁, c₂, hle, ⟨b₁, b₂, hle', hb₁, hb₂⟩, hc₂⟩
  refine ⟨b₁, b₂ * c₂, ?_, hb₁, ⟨b₂, c₂, le_refl _, hb₂, hc₂⟩⟩
  calc b₁ * (b₂ * c₂) = b₁ * b₂ * c₂ := by rw [mul_assoc]
    _ ≤ c₁ * c₂ := mul_le_mul_right_le hle' c₂
    _ ≤ m := hle

lemma entail_wand_intro {P Q R : UpperSet M} (h : entail (sep P Q) R) :
    entail P (wand Q R) :=
  fun m _ hP b hv hQ ↦ h (m * b) hv ⟨m, b, le_refl _, hP, hQ⟩

lemma entail_wand_elim {P Q R : UpperSet M} (h : entail P (wand Q R)) :
    entail (sep P Q) R := by
  rintro m hm ⟨b₁, b₂, hle, hb₁, hb₂⟩
  have hv : ✓ (b₁ * b₂) := valid_mono hle hm
  exact R.upper' hle (h b₁ (valid_mul_l hv) hb₁ b₂ hv hb₂)

lemma entail_persistently_mono {P Q : UpperSet M} (h : entail P Q) :
    entail (persistently P) (persistently Q) :=
  fun _ _ hP ↦ h 1 valid_one hP

lemma entail_persistently_idem_2 {P : UpperSet M} :
    entail (persistently P) (persistently (persistently P)) :=
  fun _ _ hP ↦ hP

lemma entail_persistently_emp_2 : entail (emp : UpperSet M) (persistently emp) :=
  fun _ _ _ ↦ le_refl 1

lemma entail_persistently_and_2 {P Q : UpperSet M} :
    entail (and (persistently P) (persistently Q))
      (persistently (and P Q)) :=
  fun _ _ h ↦ h

lemma entail_persistently_absorb_l {P Q : UpperSet M} :
    entail (sep (persistently P) Q) (persistently P) := by
  rintro m _ ⟨_, _, _, hb₁, _⟩
  exact hb₁

lemma entail_persistently_and_l {P Q : UpperSet M} :
    entail (and (persistently P) Q) (sep P Q) :=
  fun m _ h ↦ ⟨1, m, le_of_eq (one_mul m), h.1, h.2⟩

/-! ### Congruence of the connectives with respect to bi-entailment -/

lemma entail_eq_of_bientail {P P₁ Q Q₁ : UpperSet M}
    (hP : bientail P P₁) (hQ : bientail Q Q₁) : entail P Q = entail P₁ Q₁ := by
  refine propext ⟨fun h m hm hm' ↦ ?_, fun h m hm hm' ↦ ?_⟩
  · exact hQ.1 m hm (h m hm (hP.2 m hm hm'))
  · exact hQ.2 m hm (h m hm (hP.1 m hm hm'))

lemma bientail_and {P P₁ Q Q₁ : UpperSet M}
    (hP : bientail P P₁) (hQ : bientail Q Q₁) :
    bientail (and P Q) (and P₁ Q₁) :=
  ⟨fun m hm h ↦ ⟨hP.1 m hm h.1, hQ.1 m hm h.2⟩,
   fun m hm h ↦ ⟨hP.2 m hm h.1, hQ.2 m hm h.2⟩⟩

lemma bientail_or {P P₁ Q Q₁ : UpperSet M}
    (hP : bientail P P₁) (hQ : bientail Q Q₁) :
    bientail (or P Q) (or P₁ Q₁) :=
  ⟨fun m hm h ↦ h.elim (fun h ↦ Or.inl (hP.1 m hm h)) (fun h ↦ Or.inr (hQ.1 m hm h)),
   fun m hm h ↦ h.elim (fun h ↦ Or.inl (hP.2 m hm h)) (fun h ↦ Or.inr (hQ.2 m hm h))⟩

lemma bientail_imp {P P₁ Q Q₁ : UpperSet M}
    (hP : bientail P P₁) (hQ : bientail Q Q₁) : bientail (imp P Q) (imp P₁ Q₁) :=
  ⟨fun _ _ h b hle hv hb ↦ hQ.1 b hv (h b hle hv (hP.2 b hv hb)),
   fun _ _ h b hle hv hb ↦ hQ.2 b hv (h b hle hv (hP.1 b hv hb))⟩

lemma bientail_sep {P P₁ Q Q₁ : UpperSet M}
    (hP : bientail P P₁) (hQ : bientail Q Q₁) :
    bientail (sep P Q) (sep P₁ Q₁) :=
  ⟨entail_sep_mono hP.1 hQ.1, entail_sep_mono hP.2 hQ.2⟩

lemma bientail_wand {P P₁ Q Q₁ : UpperSet M}
    (hP : bientail P P₁) (hQ : bientail Q Q₁) : bientail (wand P Q) (wand P₁ Q₁) :=
  ⟨fun _ _ h b hv hb ↦ hQ.1 _ hv (h b hv (hP.2 b (valid_mul_r hv) hb)),
   fun _ _ h b hv hb ↦ hQ.2 _ hv (h b hv (hP.1 b (valid_mul_r hv) hb))⟩

lemma bientail_persistently {P Q : UpperSet M} (h : bientail P Q) :
    bientail (persistently P) (persistently Q) :=
  ⟨entail_persistently_mono h.1, entail_persistently_mono h.2⟩

instance BientailSetoid : Setoid (UpperSet M) where
  r := bientail
  iseqv :=
  {
    refl {_} := bientail_refl
    symm := bientail_symm
    trans := bientail_trans
  }

def OURAProp (M : Type) [OrderedUnitalResourceAlgebra M] := Quotient (BientailSetoid (M := M))

namespace OURAProp

def map (f : UpperSet M → UpperSet M)
         (hf : ∀ {P Q}, bientail P Q → bientail (f P) (f Q)) : OURAProp M → OURAProp M :=
  Quotient.map f fun _ _ h ↦ hf h

def map₂ (f : UpperSet M → UpperSet M → UpperSet M)
          (hf : ∀ {P P₁ Q Q₁}, bientail P P₁ → bientail Q Q₁ → bientail (f P Q) (f P₁ Q₁)) :
    OURAProp M → OURAProp M → OURAProp M :=
  Quotient.map₂ f fun _ _ h₁ _ _ h₂ ↦ hf h₁ h₂

/-- `n`-equivalence on the quotient is plain equality, so it is a discrete (C)OFE.
The `OFE` instance comes from `COFE.toOFE`. -/
instance : Iris.COFE (OURAProp M) := Iris.COFE.ofDiscrete _

instance : Iris.BI.BIBase (OURAProp M) where
  Entails := Quotient.lift₂ entail fun _ _ _ _ h₁ h₂ ↦ entail_eq_of_bientail h₁ h₂
  emp := Quotient.mk _ emp
  pure P := Quotient.mk _ (pure P)
  and := map₂ and fun h₁ h₂ ↦ bientail_and h₁ h₂
  or := map₂ or fun h₁ h₂ ↦ bientail_or h₁ h₂
  imp := map₂ imp fun h₁ h₂ ↦ bientail_imp h₁ h₂
  sForall P := Quotient.mk _ (sForall fun p ↦ P (Quotient.mk _ p))
  sExists P := Quotient.mk _ (sExists fun p ↦ P (Quotient.mk _ p))
  sep := map₂ sep fun h₁ h₂ ↦ bientail_sep h₁ h₂
  wand := map₂ wand fun h₁ h₂ ↦ bientail_wand h₁ h₂
  persistently := map persistently fun h ↦ bientail_persistently h
  later := id

/-- On the quotient, `n`-equivalence is plain equality. -/
theorem dist_iff_eq {n : ℕ} {x y : OURAProp M} : Iris.OFE.Dist n x y ↔ x = y := Iff.rfl

theorem nonExpansive_of_dist_eq {f : OURAProp M → OURAProp M} :
    Iris.OFE.NonExpansive f :=
  ⟨fun _ _ _ h ↦ dist_iff_eq.2 (by rw [dist_iff_eq.1 h])⟩

theorem nonExpansive₂_of_dist_eq {f : OURAProp M → OURAProp M → OURAProp M} :
    Iris.OFE.NonExpansive₂ f :=
  ⟨fun _ _ _ h₁ _ _ h₂ ↦ dist_iff_eq.2 (by rw [dist_iff_eq.1 h₁, dist_iff_eq.1 h₂])⟩

/-- Entailment on the quotient is reflexive. -/
theorem entails_rfl {P : OURAProp M} : Iris.BI.BIBase.Entails P P := by
  induction P using Quotient.ind
  exact entail_refl

instance : Iris.BI (OURAProp M) where
  entails_refl := entails_rfl
  entails_trans := by
    intro P Q R
    induction P using Quotient.ind
    induction Q using Quotient.ind
    induction R using Quotient.ind
    exact entail_trans
  equiv_iff := by
    intro P Q
    induction P using Quotient.ind
    induction Q using Quotient.ind
    refine ⟨fun h ↦ ⟨(Quotient.exact h).1, (Quotient.exact h).2⟩, fun h ↦ ?_⟩
    exact Quotient.sound ⟨h.1, h.2⟩
  and_ne := nonExpansive₂_of_dist_eq
  or_ne := nonExpansive₂_of_dist_eq
  imp_ne := nonExpansive₂_of_dist_eq
  sForall_ne := by
    intro n P₁ P₂ h
    have h' : P₁ = P₂ := Iris.liftRel_eq.mp h
    rw [h']
    exact dist_iff_eq.2 rfl
  sExists_ne := by
    intro n P₁ P₂ h
    have h' : P₁ = P₂ := Iris.liftRel_eq.mp h
    rw [h']
    exact dist_iff_eq.2 rfl
  sep_ne := nonExpansive₂_of_dist_eq
  wand_ne := nonExpansive₂_of_dist_eq
  persistently_ne := nonExpansive_of_dist_eq
  later_ne := nonExpansive_of_dist_eq
  pure_intro := by
    intro φ P h
    induction P using Quotient.ind
    exact entail_pure_intro h
  pure_elim' := by
    intro φ P
    induction P using Quotient.ind
    exact fun h ↦ entail_pure_elim' h
  and_elim_l := by
    intro P Q
    induction P using Quotient.ind
    induction Q using Quotient.ind
    exact entail_and_elim_l
  and_elim_r := by
    intro P Q
    induction P using Quotient.ind
    induction Q using Quotient.ind
    exact entail_and_elim_r
  and_intro := by
    intro P Q R
    induction P using Quotient.ind
    induction Q using Quotient.ind
    induction R using Quotient.ind
    exact fun h₁ h₂ ↦ entail_and_intro h₁ h₂
  or_intro_l := by
    intro P Q
    induction P using Quotient.ind
    induction Q using Quotient.ind
    exact entail_or_intro_l
  or_intro_r := by
    intro P Q
    induction P using Quotient.ind
    induction Q using Quotient.ind
    exact entail_or_intro_r
  or_elim := by
    intro P Q R
    induction P using Quotient.ind
    induction Q using Quotient.ind
    induction R using Quotient.ind
    exact fun h₁ h₂ ↦ entail_or_elim h₁ h₂
  imp_intro := by
    intro P Q R
    induction P using Quotient.ind
    induction Q using Quotient.ind
    induction R using Quotient.ind
    exact fun h ↦ entail_imp_intro h
  imp_elim := by
    intro P Q R
    induction P using Quotient.ind
    induction Q using Quotient.ind
    induction R using Quotient.ind
    exact fun h ↦ entail_imp_elim h
  sForall_intro := by
    intro P Ψ
    induction P using Quotient.ind with
    | _ P => exact fun h m hm hP p hΨ ↦ h (Quotient.mk _ p) hΨ m hm hP
  sForall_elim := by
    intro Ψ p
    induction p using Quotient.ind with
    | _ p => exact fun hΨ _ _ hm ↦ hm p hΨ
  sExists_intro := by
    intro Ψ p
    induction p using Quotient.ind with
    | _ p => exact fun hΨ m _ hp ↦ ⟨p, hΨ, hp⟩
  sExists_elim := by
    intro Φ Q
    induction Q using Quotient.ind with
    | _ Q =>
      rintro h m hm ⟨q, hΦ, hq⟩
      exact h (Quotient.mk _ q) hΦ m hm hq
  sep_mono := by
    intro P P' Q Q'
    induction P using Quotient.ind
    induction P' using Quotient.ind
    induction Q using Quotient.ind
    induction Q' using Quotient.ind
    exact fun h h' ↦ entail_sep_mono h h'
  emp_sep := by
    intro P
    induction P using Quotient.ind
    exact ⟨entail_emp_sep_l, entail_emp_sep_r⟩
  sep_symm := by
    intro P Q
    induction P using Quotient.ind
    induction Q using Quotient.ind
    exact entail_sep_symm
  sep_assoc_l := by
    intro P Q R
    induction P using Quotient.ind
    induction Q using Quotient.ind
    induction R using Quotient.ind
    exact entail_sep_assoc_l
  wand_intro := by
    intro P Q R
    induction P using Quotient.ind
    induction Q using Quotient.ind
    induction R using Quotient.ind
    exact fun h ↦ entail_wand_intro h
  wand_elim := by
    intro P Q R
    induction P using Quotient.ind
    induction Q using Quotient.ind
    induction R using Quotient.ind
    exact fun h ↦ entail_wand_elim h
  persistently_mono := by
    intro P Q
    induction P using Quotient.ind
    induction Q using Quotient.ind
    exact fun h ↦ entail_persistently_mono h
  persistently_idem_2 := by
    intro P
    induction P using Quotient.ind
    exact entail_persistently_idem_2
  persistently_emp_2 := entail_persistently_emp_2
  persistently_and_2 := by
    intro P Q
    induction P using Quotient.ind
    induction Q using Quotient.ind
    exact entail_persistently_and_2
  persistently_and_l := by
    intro P Q
    induction P using Quotient.ind
    induction Q using Quotient.ind
    exact entail_persistently_and_l
  persistently_absorb_l := by
    intro P Q
    induction P using Quotient.ind
    induction Q using Quotient.ind
    exact entail_persistently_absorb_l
  later_mono := id
  later_intro := entails_rfl
  later_sForall_2 := by
    intro Φ m hm h r hΦ
    exact h (imp (pure (Φ (Quotient.mk _ r))) r)
      ⟨Quotient.mk _ r, rfl⟩ m (le_refl m) hm hΦ
  later_sExists_false := by
    rintro Φ m _ ⟨r, hΦ, hr⟩
    exact Or.inr ⟨and (pure (Φ (Quotient.mk _ r))) r,
      ⟨Quotient.mk _ r, rfl⟩, hΦ, hr⟩
  later_sep := fun {_ _} ↦ ⟨entails_rfl, entails_rfl⟩
  later_persistently := fun {_} ↦ ⟨entails_rfl, entails_rfl⟩
  later_false_em := by
    intro P
    induction P using Quotient.ind
    exact fun _ _ hP ↦ Or.inr fun _ _ _ hb ↦ hb.elim

end OURAProp

end UpperSetBI

end Iris
