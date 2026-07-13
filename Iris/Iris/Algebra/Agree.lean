/-
Copyright (c) 2025 Leo Stefanesco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leo Stefanesco, Puming Liu, Sergei Stepanenko
-/
module

public import Iris.Algebra.CMRA
public import Iris.Algebra.OFE
public import Iris.Algebra.IsOp
meta import Iris.Std.RocqPorting

@[expose] public section

namespace Iris

/-!
# The agreement camera

`Agree.Raw α` is a nonempty list over `α`. `Agree α` is
`Agree.Raw α` quotiented by having the same
elements (i.e., a finite nonempty set).
When `α` is an OFE, `Agree α` carries the Hausdorff distance.
-/

/-! ## The raw representation -/

section Raw

variable {α : Type u}

@[ext]
structure Agree.Raw α where
  car : List α
  not_nil : car ≠ []
attribute [simp] Agree.Raw.not_nil

namespace Agree.Raw

def toAgree (a : α) : Raw α := ⟨[a], by simp⟩

theorem mem (x : Raw α) : ∃ a, a ∈ x.car := by
  rcases x with ⟨as, h⟩
  rcases as
  · contradiction
  · simp_all

def map' (f : α → β) (a : Raw α) : Raw β := ⟨a.car.map f, by simp⟩

@[simp] theorem map'_car {f : α → β} {x : Raw α} : (map' f x).car = x.car.map f := rfl

def op (x y : Raw α) : Raw α :=
  ⟨x.car ++ y.car, List.append_ne_nil_of_left_ne_nil x.not_nil _⟩

theorem map'_op {f : α → β} {x y : Raw α} : map' f (op x y) = op (map' f x) (map' f y) := by
  ext; simp [op, map']

def SameElems (x y : Raw α) : Prop :=
  (∀ a ∈ x.car, a ∈ y.car) ∧ (∀ b ∈ y.car, b ∈ x.car)

theorem sameElems_equivalence : Equivalence (SameElems (α := α)) where
  refl _ := ⟨fun _ h => h, fun _ h => h⟩
  symm h := ⟨h.2, h.1⟩
  trans h₁ h₂ := ⟨fun _ ha => h₂.1 _ (h₁.1 _ ha), fun _ hc => h₁.2 _ (h₂.2 _ hc)⟩

instance instSetoid : Setoid (Raw α) := ⟨SameElems, sameElems_equivalence⟩

theorem sameElems_def {x y : Raw α} : x ≈ y ↔ SameElems x y := .rfl

theorem op_sameElems {a b c d : Raw α} (h₁ : SameElems a c) (h₂ : SameElems b d) :
    SameElems (op a b) (op c d) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩ <;> simp only [op, List.mem_append] at hx ⊢
  · exact hx.imp (h₁.1 x) (h₂.1 x)
  · exact hx.imp (h₁.2 x) (h₂.2 x)

theorem map'_sameElems {f : α → β} {x y : Raw α} (h : SameElems x y) :
    SameElems (map' f x) (map' f y) := by
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩ <;>
  · simp only [map'_car, List.mem_map] at ha ⊢
    obtain ⟨b, hb, rfl⟩ := ha
    exact ⟨b, by first | exact h.1 _ hb | exact h.2 _ hb, rfl⟩

variable [OFE α]

def dist (n : Nat) (x y : Raw α) : Prop :=
  (∀ a ∈ x.car, ∃ b ∈ y.car, a ≡{n}≡ b) ∧
  (∀ b ∈ y.car, ∃ a ∈ x.car, a ≡{n}≡ b)

theorem dist_equiv : Equivalence (dist (α := α) n) where
  refl := fun ⟨x, h⟩ => by
    refine ⟨?_, ?_⟩
    · intro a ha; exists a
    · intro b hb; exists b
  symm := fun ⟨h₁, h₂⟩ => by
    refine ⟨?_, ?_⟩
    · intro a ha
      obtain ⟨b, hb, hd⟩ := h₂ a ha
      exact ⟨b, hb, hd.symm⟩
    · intro b hb
      obtain ⟨a, ha, hd⟩ := h₁ b hb
      exact ⟨a, ha, hd.symm⟩
  trans := fun ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩ => by
    refine ⟨?_, ?_⟩
    · intro a ha
      obtain ⟨b, hb, hd₁⟩ := h₁ a ha
      obtain ⟨c, hc, hd₂⟩ := h₂ b hb
      exact ⟨c, hc, hd₁.trans hd₂⟩
    · intro c hc
      obtain ⟨b, hb, hd₁⟩ := h₂' c hc
      obtain ⟨a, ha, hd₂⟩ := h₁' b hb
      exact ⟨a, ha, hd₂.trans hd₁⟩

theorem dist_lt {x y : Raw α} (h : dist n x y) (hlt : m < n) : dist m x y := by
  obtain ⟨h₁, h₂⟩ := h
  refine ⟨?_, ?_⟩
  · intro a ha
    obtain ⟨b, hb, hd⟩ := h₁ a ha
    exact ⟨b, hb, OFE.Dist.lt hd hlt⟩
  · intro b hb
    obtain ⟨a, ha, hd⟩ := h₂ b hb
    exact ⟨a, ha, OFE.Dist.lt hd hlt⟩

theorem dist_congr {a b c d : Raw α} (hac : SameElems a c) (hbd : SameElems b d) :
    dist n a b ↔ dist n c d :=
  have imp {a b c d : Raw α} (hac : SameElems a c) (hbd : SameElems b d) : dist n a b → dist n c d :=
    fun h => ⟨fun x hx => (h.1 x (hac.2 x hx)).imp fun _ p => ⟨hbd.1 _ p.1, p.2⟩,
              fun y hy => (h.2 y (hbd.2 y hy)).imp fun _ p => ⟨hac.1 _ p.1, p.2⟩⟩
  ⟨imp hac hbd, imp (sameElems_equivalence.symm hac) (sameElems_equivalence.symm hbd)⟩

def validN (n : Nat) (x : Raw α) : Prop :=
  match x.car with
  | [_] => True
  | _ => ∀ a ∈ x.car, ∀ b ∈ x.car, a ≡{n}≡ b

theorem validN_iff {x : Raw α} :
    x.validN n ↔ ∀ a ∈ x.car, ∀ b ∈ x.car, a ≡{n}≡ b := by
  rcases x with ⟨⟨⟩ | ⟨a, ⟨⟩| _⟩, _⟩ <;> simp_all [validN, OFE.Dist.rfl]

theorem validN_congr {x y : Raw α} (h : SameElems x y) : validN n x ↔ validN n y := by
  simp only [validN_iff]
  exact ⟨fun hv a ha b hb => hv a (h.2 a ha) b (h.2 b hb),
         fun hv a ha b hb => hv a (h.1 a ha) b (h.1 b hb)⟩

def valid (x : Raw α) : Prop := ∀ n, x.validN n

theorem op_comm {x y : Raw α} : ∀ n, dist n (op x y) (op y x) := by
  intro n; simp_all only [dist, op, List.mem_append]
  refine ⟨?_, ?_⟩ <;> exact fun _ ha => ⟨_, ha.symm, .rfl⟩

theorem op_commN {x y : Raw α} : dist n (op x y) (op y x) := op_comm n

theorem op_assoc {x y z : Raw α} : ∀ n, dist n (op x (op y z)) (op (op x y) z) := by
  intro n; simp_all only [dist, op, List.mem_append, List.append_assoc]
  refine ⟨?_, ?_⟩ <;> (intro a ha; exists a)

theorem idemp {x : Raw α} : ∀ n, dist n (op x x) x := by
  intro n; refine ⟨?_, ?_⟩ <;> (intro a ha; exists a; simp_all [op])

theorem validN_ne {x y : Raw α} : dist n x y → x.validN n → y.validN n := by
  simp only [dist, validN_iff, and_imp]
  intro h₁ h₂ hn a ha b hb
  have ⟨a', ha', ha'a⟩ := h₂ _ ha
  have ⟨b', hb', hb'b⟩ := h₂ _ hb
  have ha'b' := hn _ ha' _ hb'
  exact ha'a.symm.trans (ha'b'.trans hb'b)

theorem validN_succ {x : Raw α} : x.validN (n + 1) → x.validN n := by
  simp only [validN_iff]; intro hsuc a ha b hb
  exact OFE.dist_lt (hsuc a ha b hb) (by omega)

theorem validN_op_left {x y : Raw α} : (op x y).validN n → x.validN n := by
  simp only [op, validN_iff, List.mem_append]
  exact fun h a ha b hb => h _ (.inl ha) _ (.inl hb)

theorem op_ne {x y₁ y₂ : Raw α} (h : dist n y₁ y₂) : dist n (op x y₁) (op x y₂) := by
  obtain ⟨heq₁, heq₂⟩ := h
  simp only [dist, op, List.mem_append]
  refine ⟨?_, ?_⟩
  · rintro a (hx | hy)
    · exists a; simp [hx]
    · obtain ⟨b, hb, heq⟩ := heq₁ _ hy
      exists b; simp_all
  · rintro a (hx | hy)
    · exists a; simp [hx]
    · obtain ⟨b, hb, heq⟩ := heq₂ _ hy
      exists b; simp_all

theorem op_ne₂ {x₁ x₂ y₁ y₂ : Raw α} (hx : dist n x₁ x₂) (hy : dist n y₁ y₂) :
    dist n (op x₁ y₁) (op x₂ y₂) :=
  dist_equiv.trans (op_ne hy) <| dist_equiv.trans (op_comm n) <|
    dist_equiv.trans (op_ne hx) (op_comm n)

theorem op_invN {x y : Raw α} : (op x y).validN n → dist n x y := by
  simp only [op, validN_iff, List.mem_append, dist]
  intro h; refine ⟨?_, ?_⟩
  · intro a ha
    obtain ⟨b, hb⟩ := mem y
    exists b; simp_all
  · intro a ha
    obtain ⟨b, hb⟩ := mem x
    exists b; simp_all

theorem op_inv {x y : Raw α} : (op x y).valid → ∀ n, dist n x y := by
  simp only [valid]
  intro h n
  exact op_invN (h n)

@[simp] theorem toAgree_validN {a : α} : (toAgree a).validN n := by
  simp [validN, toAgree]

theorem toAgree_injN {a b : α} : dist n (toAgree a) (toAgree b) → a ≡{n}≡ b := by
  intro ⟨h₁, h₂⟩; simp_all [toAgree]

theorem toAgree_uninjN {x : Raw α} : x.validN n → ∃ a, dist n (toAgree a) x := by
  rw [validN_iff]
  obtain ⟨a, ha⟩ := mem x
  intro h; exists a
  refine ⟨?_, ?_⟩ <;> intros
  · exists a; simp_all [toAgree]
  · simp_all [toAgree]

theorem toAgree_uninj {x : Raw α} : x.valid → ∃ a, ∀ n, dist n (toAgree a) x := by
  simp only [valid, validN_iff]
  obtain ⟨a, ha⟩ := mem x
  intro h; exists a; intro n
  refine ⟨?_, ?_⟩ <;> intros
  · exists a; simp_all [toAgree]
  · simp_all [toAgree]

variable [OFE β] {f : α → β}

theorem map'_ne [OFE.NonExpansive f] {x₁ x₂ : Raw α} (h : dist n x₁ x₂) :
    dist n (map' f x₁) (map' f x₂) := by
  refine ⟨?_, ?_⟩
  · simp only [map', List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro a ha
    obtain ⟨b, hb, heq⟩ := h.1 a ha
    exact ⟨f b, ⟨b, hb, rfl⟩, OFE.NonExpansive.ne heq⟩
  · simp only [map', List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro a ha
    obtain ⟨b, hb, heq⟩ := h.2 a ha
    exact ⟨f b, ⟨b, hb, rfl⟩, OFE.NonExpansive.ne heq⟩

theorem map'_validN [OFE.NonExpansive f] {x : Raw α} (h : x.validN n) : (map' f x).validN n := by
  rw [validN_iff] at h ⊢
  simp only [map'_car, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  exact fun a ha b hb => OFE.NonExpansive.ne (h a ha b hb)

theorem discrete_0 [OFE.Discrete α] {x y : Raw α} (h : dist 0 x y) (n) : dist n x y := by
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · obtain ⟨b, hb, heq⟩ := h.1 a ha; exact ⟨b, hb, OFE.discrete_n heq⟩
  · obtain ⟨a, ha, heq⟩ := h.2 b hb; exact ⟨a, ha, OFE.discrete_n heq⟩

theorem discrete_valid [OFE.Discrete α] {x : Raw α} (h : x.validN 0) : x.valid := by
  rw [validN_iff] at h
  intro n; rw [validN_iff]
  exact fun a ha b hb => OFE.discrete_n (h a ha b hb)

theorem toAgree_discrete {a : α} [Ha : OFE.DiscreteE a] {y : Raw α}
    (h : dist 0 (toAgree a) y) (n) : dist n (toAgree a) y := by
  refine ⟨fun x hx => ?_, fun c hc => ?_⟩
  · rw [show x = a from by simpa [toAgree] using hx]
    obtain ⟨b, hb, hd⟩ := h.1 a (by simp [toAgree])
    exact ⟨b, hb, (Ha.discrete hd).dist⟩
  · obtain ⟨x, hx, hd⟩ := h.2 c hc
    rw [show x = a from by simpa [toAgree] using hx] at hd
    exact ⟨a, by simp [toAgree], (Ha.discrete hd).dist⟩

theorem exists_forall_dist {a : α} {l : List α}
    (h : ∀ n, ∃ b ∈ l, a ≡{n}≡ b) : ∃ b ∈ l, ∀ n, a ≡{n}≡ b := by
  induction l with
  | nil => simpa using h 0
  | cons c l ih =>
    by_cases hc : ∀ n, a ≡{n}≡ c
    · exact ⟨c, List.mem_cons_self, hc⟩
    · obtain ⟨n₀, hn₀⟩ := Classical.not_forall.mp hc
      have hl : ∀ n, ∃ b ∈ l, a ≡{n}≡ b := fun n => by
        obtain ⟨b, hb, hd⟩ := h (max n n₀)
        rcases List.mem_cons.mp hb with rfl | hb'
        · exact absurd (hd.le (Nat.le_max_right n n₀)) hn₀
        · exact ⟨b, hb', hd.le (Nat.le_max_left n n₀)⟩
      obtain ⟨b, hb, hd⟩ := ih hl
      exact ⟨b, List.mem_cons_of_mem _ hb, hd⟩

theorem sameElems_of_dist {x y : Raw α} (h : ∀ n, dist n x y) : SameElems x y :=
  have key : ∀ {x y : Raw α}, (∀ n, dist n x y) → ∀ a ∈ x.car, a ∈ y.car := by
    intro x y h a ha
    obtain ⟨b, hb, hd⟩ := exists_forall_dist (fun n => (h n).1 a ha)
    exact OFE.Equiv.to_eq (OFE.equiv_dist.mpr hd) ▸ hb
  ⟨key h, key (fun n => Raw.dist_equiv.symm (h n))⟩

end Agree.Raw

end Raw

section Quotient

open OFE
open Agree (Raw)

variable {α : Type u}

@[rocq_alias agree]
def Agree (α : Type u) : Type u := Quotient (Raw.instSetoid (α := α))

namespace Agree

def mk (x : Raw α) : Agree α := Quotient.mk _ x

@[elab_as_elim, induction_eliminator]
theorem ind {motive : Agree α → Prop} (mk : ∀ x : Raw α, motive (Agree.mk x)) (x : Agree α) :
    motive x := Quotient.ind mk x

theorem sound {x y : Raw α} (h : Raw.SameElems x y) : mk x = mk y := Quotient.sound h

theorem exact {x y : Raw α} (h : mk x = mk y) : Raw.SameElems x y := Quotient.exact h

theorem mk_eq {x y : Raw α} : mk x = mk y ↔ Raw.SameElems x y := ⟨exact, sound⟩

def lift {γ : Sort w} (f : Raw α → γ) (resp : ∀ x y, Raw.SameElems x y → f x = f y) :
    Agree α → γ := Quotient.lift f resp

def lift₂ {γ : Sort w} (f : Raw α → Raw α → γ)
    (resp : ∀ a b c d, Raw.SameElems a c → Raw.SameElems b d → f a b = f c d) :
    Agree α → Agree α → γ := Quotient.lift₂ f resp

@[simp] theorem lift_mk {γ : Sort w} (f : Raw α → γ) (resp) (x : Raw α) :
    lift f resp (mk x) = f x := rfl
@[simp] theorem lift₂_mk {γ : Sort w} (f) (resp) (x y : Raw α) :
    lift₂ (γ := γ) f resp (mk x) (mk y) = f x y := rfl

def op : Agree α → Agree α → Agree α :=
  lift₂ (fun x y => mk (Raw.op x y))
    (fun _ _ _ _ hac hbd => sound (Raw.op_sameElems hac hbd))

@[simp] theorem op_mk {x y : Raw α} : op (mk x) (mk y) = mk (Raw.op x y) := rfl

instance : Membership α (Agree α) where
  mem x a := lift (a ∈ ·.car) (fun _ _ h => propext ⟨(h.1 a ·), (h.2 a ·)⟩) x

@[simp] theorem mem_mk {a : α} {x : Raw α} : a ∈ mk x ↔ a ∈ x.car := .rfl

@[rocq_alias elem_of_agree]
theorem mem_of_agree (x : Agree α) : ∃ a, a ∈ x := x.ind fun r => Raw.mem r

end Agree

namespace Agree

variable [OFE α] [OFE β]

@[rocq_alias agree_dist]
def dist (n : Nat) : Agree α → Agree α → Prop :=
  lift₂ (Raw.dist n) (fun _ _ _ _ hac hbd => propext (Raw.dist_congr hac hbd))

@[rocq_alias agree_ofe_mixin]
instance instOFE : OFE (Agree α) where
  Dist := dist
  dist_eqv := by
    refine ⟨Quotient.ind fun a => Raw.dist_equiv.refl a, fun {x y} h => ?_, fun {x y z} h₁ h₂ => ?_⟩
    · induction x, y using Quotient.ind₂ with | _ a b => exact Raw.dist_equiv.symm h
    · induction x, y using Quotient.ind₂ with | _ a b =>
        induction z using Quotient.ind with | _ c => exact Raw.dist_equiv.trans h₁ h₂
  eq_dist {x y} := by
    induction x, y using Quotient.ind₂ with | _ a b =>
      refine ⟨fun h n => ?_, fun h => sound (Raw.sameElems_of_dist h)⟩
      exact (Raw.dist_congr (Raw.sameElems_equivalence.refl a) (Agree.exact h)).mp
        (Raw.dist_equiv.refl a)
  dist_lt := fun {n x y m} h hlt => by
    induction x, y using Quotient.ind₂ with | _ a b => exact Raw.dist_lt h hlt

#rocq_ignore agreeO "Use Agree with a typeclass instance instead."
#rocq_ignore agree_equiv "Defined in Agree OFE instance."

def validN (n : Nat) : Agree α → Prop :=
  lift (Raw.validN n) (fun _ _ h => propext (Raw.validN_congr h))

@[rocq_alias agree_validN_def]
theorem validN_iff {x : Agree α} : validN n x ↔ ∀ a ∈ x, ∀ b ∈ x, a ≡{n}≡ b :=
  x.ind fun _ => Raw.validN_iff

def valid : Agree α → Prop :=
  lift Raw.valid fun _ _ h => propext
    ⟨fun hv m => (Raw.validN_congr h).mp (hv m), fun hv m => (Raw.validN_congr h).mpr (hv m)⟩

@[simp] theorem dist_mk {n} {x y : Raw α} : mk x ≡{n}≡ mk y ↔ Raw.dist n x y := .rfl
@[simp] theorem validN_mk {n} {x : Raw α} : validN n (mk x) ↔ x.validN n := .rfl
@[simp] theorem valid_mk {x : Raw α} : valid (mk x) ↔ x.valid := .rfl

@[rocq_alias agree_comm]
theorem op_comm {x y : Agree α} : op x y ≡ op y x :=
  x.ind fun _ => y.ind fun _ => Raw.op_comm

theorem op_commN {x y : Agree α} : op x y ≡{n}≡ op y x := op_comm n

@[rocq_alias agree_assoc]
theorem op_assoc {x y z : Agree α} : op x (op y z) ≡ op (op x y) z :=
  x.ind fun _ => y.ind fun _ => z.ind fun _ => Raw.op_assoc

theorem op_idemp {x : Agree α} : op x x ≡ x :=
  x.ind fun _ => Raw.idemp

@[rocq_alias agree_validN_ne]
theorem validN_ne {x y : Agree α} : x ≡{n}≡ y → validN n x → validN n y :=
  x.ind fun _ => y.ind fun _ => Raw.validN_ne

theorem validN_succ {x : Agree α} : validN (n + 1) x → validN n x :=
  x.ind fun _ => Raw.validN_succ

theorem validN_op_left {x y : Agree α} : validN n (op x y) → validN n x :=
  x.ind fun _ => y.ind fun _ => Raw.validN_op_left

@[rocq_alias agree_op_ne']
theorem op_ne {x : Agree α} : OFE.NonExpansive (op x) :=
  ⟨fun {_} y₁ y₂ => x.ind fun _ => y₁.ind fun _ => y₂.ind fun _ h => Raw.op_ne (dist_mk.mp h)⟩

@[rocq_alias agree_op_ne]
theorem op_ne₂ : OFE.NonExpansive₂ (op (α := α)) := by
  refine ⟨fun {n} x₁ x₂ hx y₁ y₂ hy => ?_⟩
  exact op_ne.ne hy |>.trans (op_comm n) |>.trans (op_ne.ne hx) |>.trans (op_comm n)

@[rocq_alias agree_op_invN]
theorem op_invN {x y : Agree α} : validN n (op x y) → x ≡{n}≡ y :=
  x.ind fun _ => y.ind fun _ => Raw.op_invN

@[rocq_alias agree_op_inv]
theorem op_inv {x y : Agree α} : valid (op x y) → x ≡ y :=
  x.ind fun _ => y.ind fun _ => Raw.op_inv

@[rocq_alias agree_cmra_mixin]
instance instCMRA : CMRA (Agree α) where
  pcore := some
  op := op
  ValidN := validN
  Valid := valid
  op_ne := op_ne
  pcore_ne := by simp
  validN_ne := validN_ne
  valid_iff_validN := fun {x} => x.ind fun _ => .rfl
  validN_succ := validN_succ
  assoc := op_assoc
  comm := op_comm
  pcore_op_left := fun {x cx} h => by obtain rfl := Option.some.inj h; exact op_idemp
  pcore_idem := fun {x cx} h => by obtain rfl := Option.some.inj h; exact .rfl
  pcore_op_mono := fun {x cx} h y => by obtain rfl := Option.some.inj h; exact ⟨y, .rfl⟩
  validN_op_left := validN_op_left
  extend {n x y₁ y₂ hval heq₁} := by
    have heq₂ := op_invN (validN_ne heq₁ hval)
    have heq₃ : op y₁ y₂ ≡{n}≡ y₁ := op_ne.ne heq₂.symm |>.trans (op_idemp n)
    exact ⟨x, x, op_idemp.symm, heq₁.trans heq₃, heq₁.trans heq₃ |>.trans heq₂⟩

#rocq_ignore agreeR "Use the plain Agree type with a typeclass instance instead."
#rocq_ignore agree_op_instance "Use the CMRA instance instead."
#rocq_ignore agree_pcore_instance "Use the CMRA instance instead."
#rocq_ignore agree_validN_instance "Use the CMRA instance instead."
#rocq_ignore agree_valid_instance "Use the CMRA instance instead."

theorem op_def {x y : Agree α} : x • y = op x y := rfl
theorem validN_def {x : Agree α} : ✓{n} x ↔ validN n x := .rfl
theorem valid_def {x : Agree α} : ✓ x ↔ valid x := .rfl

@[rocq_alias agree_pcore]
theorem pcore_some {x : Agree α} : CMRA.pcore x = some x := rfl

@[rocq_alias agree_cmra_total]
instance : CMRA.IsTotal (Agree α) where
  total x := ⟨x, rfl⟩

@[rocq_alias agree_idemp]
theorem idemp {x : Agree α} : x • x ≡ x := op_idemp

#rocq_ignore agree_validN_proper "Derivable from Agree.validN_ne using NonExpansive.eqv"
#rocq_ignore agree_op_proper "Derivable from Agree.op_ne₂ using NonExpansive₂.eqv"
#rocq_ignore to_agree_op_inv "Use the general op_invN theorem."
#rocq_ignore to_agree_op_invN "Use the general op_inv theorem."

@[rocq_alias agree_cmra_discrete]
instance instCMRADiscrete [OFE.Discrete α] : CMRA.Discrete (Agree α) where
  discrete_0 {x y} := x.ind fun _ => y.ind fun _ => Raw.discrete_0
  discrete_valid {x} := x.ind fun _ => Raw.discrete_valid

instance instDiscrete [OFE.Discrete α] : OFE.Discrete (Agree α) where
  discrete_0 {x y} := x.ind fun _ => y.ind fun _ => Raw.discrete_0

@[rocq_alias agree_includedN]
theorem includedN {x y : Agree α} : x ≼{n} y ↔ y ≡{n}≡ y • x := by
  refine ⟨fun ⟨z, h⟩ => ?_, fun h => ⟨y, h.trans op_commN⟩⟩
  calc
    y ≡{n}≡ x • z := h
    _ ≡{n}≡ (x • x) • z := .op_l (idemp.symm n)
    _ ≡{n}≡ x • (x • z) := CMRA.op_assocN.symm
    _ ≡{n}≡ x • y := h.symm.op_r
    _ ≡{n}≡ y • x := op_commN

@[rocq_alias agree_included]
theorem included {x y : Agree α} : x ≼ y ↔ y ≡ y • x :=
  ⟨fun ⟨z, h⟩ n => includedN.mp ⟨z, h n⟩, fun h => ⟨y, h.trans op_comm⟩⟩

@[rocq_alias agree_valid_includedN]
theorem valid_includedN {x y : Agree α} : ✓{n} y → x ≼{n} y → x ≡{n}≡ y := by
  intro hval ⟨z, heq⟩
  calc
    x ≡{n}≡ x • x := .symm (idemp _)
    _ ≡{n}≡ x • z := (op_invN <| heq.validN.mp hval).op_r
    _ ≡{n}≡ y := heq.symm

@[rocq_alias agree_valid_included]
theorem valid_included {x y : Agree α} : ✓ y → x ≼ y → x ≡ y := by
  intro hval ⟨z, heq⟩
  calc
    x ≡ x • x := idemp.symm
    _ ≡ x • z := .op_r <| op_inv <| (CMRA.valid_iff heq).mp hval
    _ ≡ y := heq.symm

instance {x : Agree α} : IsOp d x x x where
  is_op := idemp.symm

end Agree

@[rocq_alias to_agree]
def toAgree (a : α) : Agree α := Agree.mk (Agree.Raw.toAgree a)

theorem toAgree_def {a : α} : toAgree a = Agree.mk (Agree.Raw.toAgree a) := rfl

section

variable [OFE α]

@[rocq_alias to_agree_ne]
instance instNonExpansive_toAgree : OFE.NonExpansive (@toAgree α) where
  ne n x₁ x₂ heq := by refine ⟨?_, ?_⟩ <;> simp_all [Agree.Raw.toAgree]

#rocq_ignore to_agree_proper "Derivable from instNonExpansive_toAgree with NonExpansive.eqv"

@[rocq_alias to_agree_injN]
theorem Agree.toAgree_injN {a b : α} : toAgree a ≡{n}≡ toAgree b → a ≡{n}≡ b :=
  Raw.toAgree_injN

@[rocq_alias to_agree_inj]
theorem Agree.toAgree_inj {a b : α} : toAgree a ≡ toAgree b → a ≡ b := by
  simp only [OFE.equiv_dist]
  exact fun heq n => toAgree_injN (heq n)

@[simp] theorem Agree.toAgree_validN {a : α} : ✓{n} toAgree a := Raw.toAgree_validN (a := a) (n := n)

@[simp] theorem Agree.toAgree_valid {a : α} : ✓ toAgree a :=
  fun m => Agree.toAgree_validN (a := a) (n := m)

@[rocq_alias to_agree_uninjN]
theorem Agree.toAgree_uninjN {x : Agree α} : ✓{n} x → ∃ a, toAgree a ≡{n}≡ x :=
  x.ind fun _ h => Raw.toAgree_uninjN h

@[rocq_alias to_agree_uninj]
theorem Agree.toAgree_uninj {x : Agree α} : ✓ x → ∃ a, toAgree a ≡ x :=
  x.ind fun _ h => (Raw.toAgree_uninj h).imp fun _ h n => h n

instance toAgree.ne : OFE.NonExpansive (toAgree : α → Agree α) := instNonExpansive_toAgree

theorem toAgree.inj {a1 a2 : α} {n} (H : toAgree a1 ≡{n}≡ toAgree a2) : a1 ≡{n}≡ a2 :=
  Agree.toAgree_injN H

namespace Agree

@[rocq_alias agree_cancelable]
instance {x : Agree α} : CMRA.Cancelable x where
  cancelableN hval heq :=
    (Agree.op_invN hval).symm.trans (Agree.op_invN ((OFE.Dist.validN heq).mp hval))

@[rocq_alias agree_core_id]
instance (a : α) : CMRA.CoreId (toAgree a) where
  core_id := by simp [CMRA.pcore]

@[simp, rocq_alias to_agree_includedN]
theorem toAgree_includedN {a b : α} : toAgree a ≼{n} toAgree b ↔ a ≡{n}≡ b := by
  refine ⟨?_, ?_⟩ <;> intro h
  · exact toAgree_injN (valid_includedN trivial h)
  · exists toAgree a
    calc
      toAgree b ≡{n}≡ toAgree a := OFE.NonExpansive.ne h.symm
      _         ≡{n}≡ toAgree a • toAgree a := .symm (idemp n)

@[simp, rocq_alias to_agree_included]
theorem toAgree_included {a b : α} : toAgree a ≼ toAgree b ↔ a ≡ b := by
  refine ⟨?_, ?_⟩ <;> intro h
  · exact toAgree_inj (valid_included (fun _ => trivial) h)
  · exists toAgree a
    calc
      toAgree b ≡ toAgree a := OFE.NonExpansive.eqv (OFE.Equiv.symm h)
      _         ≡ toAgree a • toAgree a := .symm (CMRA.pcore_op_left rfl)

@[simp, rocq_alias to_agree_included_L]
theorem toAgree_included_L {a b : α} :
    toAgree a ≼ toAgree b ↔ a = b := by
  rw [toAgree_included]; exact ⟨OFE.Equiv.to_eq, OFE.Equiv.of_eq⟩

@[rocq_alias to_agree_op_validN]
theorem toAgree_op_validN_iff_dist {a b : α} :
    ✓{n} (toAgree a • toAgree b) ↔ a ≡{n}≡ b := by
  refine ⟨?_, ?_⟩ <;> intro h
  · exact toAgree_injN (op_invN h)
  · have heqv : toAgree a • toAgree b ≡{n}≡ toAgree a := calc
      toAgree a • toAgree b ≡{n}≡ toAgree a • toAgree a := (OFE.NonExpansive.ne h).symm.op_r
      _ ≡{n}≡ toAgree a := idemp n
    exact heqv.symm.validN.mp trivial

@[rocq_alias to_agree_op_valid]
theorem toAgree_op_valid_iff_equiv {a : α} : ✓ (toAgree a • toAgree b) ↔ a ≡ b := by
  simp [OFE.equiv_dist, CMRA.valid_iff_validN, toAgree_op_validN_iff_dist]

@[rocq_alias to_agree_discrete]
instance toAgree.is_discrete {a : α} [OFE.DiscreteE a] : OFE.DiscreteE (toAgree a) where
  discrete {y} := y.ind fun _ h n => Raw.toAgree_discrete h n

end Agree

@[rocq_alias to_agree_op_valid_L]
theorem toAgree_op_valid_iff_eq {a : α} :
    ✓ (toAgree a • toAgree b) ↔ a = b := by
  rw [Agree.toAgree_op_valid_iff_equiv]; exact ⟨OFE.Equiv.to_eq, OFE.Equiv.of_eq⟩

#rocq_ignore to_agree_op_inv_L "Use toAgree_op_valid_iff_eq"

end

end Quotient

/-! ## Functoriality -/

section agree_map

open Agree (Raw)

@[rocq_alias agree_map]
def Agree.map' (f : α → β) : Agree α → Agree β :=
  Agree.lift (fun x => Agree.mk (Raw.map' f x))
    (fun _ _ h => Agree.sound (Raw.map'_sameElems h))

@[simp] theorem Agree.map'_mk (f : α → β) {x : Raw α} :
    Agree.map' f (Agree.mk x) = Agree.mk (Raw.map' f x) := rfl

@[simp] theorem Agree.map'_id (x : Agree α) : Agree.map' id x = x :=
  x.ind fun _ => congrArg mk (Raw.ext (by simp [Raw.map'_car]))

theorem Agree.map'_compose {f : α → β} {g : β → γ} (x : Agree α) :
    Agree.map' (g ∘ f) x = Agree.map' g (Agree.map' f x) :=
  x.ind fun _ => congrArg mk (Raw.ext (by simp [Raw.map'_car, List.map_map]))

variable {α β γ : Type _} [OFE α] [OFE β] [OFE γ] {f : α → β} [hne : OFE.NonExpansive f]

@[rocq_alias agree_map_ne]
instance instNonExpansive_AgreeMap' : OFE.NonExpansive (Agree.map' f) where
  ne _ x y := x.ind fun _ => y.ind fun _ h => Raw.map'_ne (Agree.dist_mk.mp h)

#rocq_ignore agree_map_proper "Derivable from instNonExpansive_AgreeMap' with NonExpansive.eqv"

variable (f) in
@[rocq_alias agree_map_morphism]
def Agree.map : (Agree α) -C> (Agree β) where
  f := map' f
  ne := instNonExpansive_AgreeMap'
  validN {_n x} := x.ind fun _ => Raw.map'_validN
  pcore _ := .rfl
  op x y := x.ind fun _ => y.ind fun _ => .of_eq (congrArg mk Raw.map'_op)

@[simp] theorem Agree.map_mk (f : α → β) [OFE.NonExpansive f] (x : Raw α) :
    Agree.map f (mk x) = mk (Raw.map' f x) := rfl

@[rocq_alias agreeO_map]
abbrev Agree.map_hom : (Agree α) -n> (Agree β) := CMRA.Hom.toHom (Agree.map f)

@[rocq_alias agreeO_map_ne]
theorem Agree.map_ne {f g : α → β} [OFE.NonExpansive f] [OFE.NonExpansive g] {x : Agree α}
    (heq : ∀ a, f a ≡{n}≡ g a) : map f x ≡{n}≡ map g x :=
  x.ind fun _ => by
    refine dist_mk.mpr ⟨?_, ?_⟩ <;> simp only [Raw.map'_car, List.mem_map] <;> rintro _ ⟨a, ha, rfl⟩
    · exact ⟨g a, ⟨a, ha, rfl⟩, heq a⟩
    · exact ⟨f a, ⟨a, ha, rfl⟩, heq a⟩

@[rocq_alias agree_map_ext]
theorem Agree.agree_map_ext {f g : α → β} [OFE.NonExpansive f] [OFE.NonExpansive g] {x : Agree α}
    (H : ∀ a, f a ≡ g a) : map f x ≡ map g x :=
  OFE.equiv_dist.mpr fun _ => map_ne (H · |>.dist)

@[rocq_alias agree_map_id]
theorem Agree.map_id (x : Agree α) : Agree.map id x = x :=
  x.ind fun _ => congrArg mk (Raw.ext (by simp [Raw.map'_car]))

@[rocq_alias agree_map_compose]
theorem Agree.map_compose (f : α -n> β) (g : β -n> γ) (x : Agree α) :
    Agree.map (g.comp f) x = Agree.map g (Agree.map f x) :=
  x.ind fun _ => congrArg mk (Raw.ext (by simp [Raw.map'_car, OFE.Hom.comp, List.map_map]))

@[rocq_alias agree_map_to_agree]
theorem Agree.map_toAgree {x : α} : Agree.map f (toAgree x) = toAgree (f x) :=
  congrArg mk (Raw.ext rfl)

end agree_map

section agree_rfunctor

@[rocq_alias agreeRF]
abbrev AgreeRF (F : COFE.OFunctorPre) : COFE.OFunctorPre :=
  fun A B _ _ => Agree (F A B)

instance {F} [COFE.OFunctor F] : RFunctor (AgreeRF F) where
  map f g := Agree.map (COFE.OFunctor.map f g)
  map_ne.ne _ _ _ Hx _ _ Hy _ := Agree.map_ne <| COFE.OFunctor.map_ne.ne Hx Hy
  map_id x := by
    conv => right; rw [← (Agree.map_id x)]
    exact (Agree.map_id x) ▸ Agree.agree_map_ext COFE.OFunctor.map_id
  map_comp f g f' g' x := by
    rw [← Agree.map_compose]
    apply Agree.agree_map_ext
    apply COFE.OFunctor.map_comp

@[rocq_alias agreeRF_contractive]
instance {F} [COFE.OFunctorContractive F] : RFunctorContractive (AgreeRF F) where
  map_contractive.1 H _ := Agree.map_ne (COFE.OFunctorContractive.map_contractive.1 H)

end agree_rfunctor
