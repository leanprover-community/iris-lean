import Iris.Algebra.DFrac
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Rat.Star

namespace Bluebell

open Iris

/-- Permissions as pointwise `DFrac F` over variables of type `α`.
Requires a `UFraction F` instance so that `DFrac F` is a CMRA.
This inherits CMRA/UCMRA structure from function instances. -/
abbrev Permission (α F : Type*) [UFraction F] := α → DFrac F

namespace Permission

variable {α F : Type*} [UFraction F]

/-- Construct permissions by taking pointwise `DFrac.own` of `p : α → Frac F`. -/
def ofFrac (p : α → Frac F) : Permission α F :=
  fun a => DFrac.own (p a : F)

/-- The all-one permission (own the whole fraction at every variable). -/
def one : Permission α F := fun _ => DFrac.own (1 : F)

instance : One (Permission α F) := ⟨one⟩

/-- Zero-permission for `DFrac F` is represented by `discard`. -/
def isZero (x : DFrac F) : Prop := x = DFrac.discard

/-- Having some ownership means not `discard` (either `own _` or `ownDiscard _`). -/
def hasOwnership (x : DFrac F) : Prop := x ≠ DFrac.discard

/-- The set of variables where the permission is zero (`discard`). -/
def zeroSupport (p : Permission α F) : α → Prop := fun a => p a = DFrac.discard

/-- The set of variables with some ownership (not `discard`). -/
def nonZeroSupport (p : Permission α F) : α → Prop := fun a => p a ≠ DFrac.discard

/-! ### API lemmas (statements only)

These lemmas describe how zero/non-zero support behaves with respect to the
pointwise CMRA operation on permissions and the `one` permission. Proofs will be
added later. -/

/-- Zero-support of the pointwise permission operation equals intersection (as a predicate). -/
theorem zeroSupport_op (p₁ p₂ : Permission α F) :
    zeroSupport (fun a => p₁ a • p₂ a) =
      (fun a => p₁ a = DFrac.discard ∧ p₂ a = DFrac.discard) := by
  funext a
  simp [zeroSupport, DFrac_CMRA, op]
  split <;> simp_all

/-- Non-zero support implication: if the op is non-zero at `a`, then at least one side is non-zero. -/
theorem nonZeroSupport_op_imp (p₁ p₂ : Permission α F) :
    ∀ a, (p₁ a • p₂ a) ≠ DFrac.discard → (p₁ a ≠ DFrac.discard ∨ p₂ a ≠ DFrac.discard) := by
  intro a h
  simp [DFrac_CMRA, op] at h
  split at h <;> simp_all

/-- The `one` permission has empty zero-support (as a predicate). -/
@[simp] theorem zeroSupport_one :
    zeroSupport (1 : Permission α F) = (fun _ => False) := by
  funext a
  -- `1` is the constant permission `a ↦ DFrac.own 1`, which is not `discard`.
  simp [zeroSupport, one, OfNat.ofNat, One.one]

end Permission


/-! ## Paper-style rational permissions

We reintroduce the paper RA version of permissions: nonnegative rationals with
pointwise addition. We use `Multiplicative (α → ℚ≥0)` so that:
- multiplication `*` on this type corresponds to pointwise addition on `ℚ≥0`;
- the unit `1` corresponds to the constant-0 function, matching the RA unit.

Validity is encoded as a separate predicate: pointwise `≤ 1`.
-/

/-- Paper-style permissions over `α`: maps to nonnegative rationals, with
pointwise addition encoded via `Multiplicative`. -/
def PermissionRat (α : Type*) := Multiplicative (α → ℚ≥0)

namespace PermissionRat

open Iris Iris.CMRA OFE.Discrete

variable (α : Type*)

@[simp] instance : COFE (PermissionRat α) := COFE.ofDiscrete _ Eq_Equivalence
instance : OFE.Leibniz (PermissionRat α) := ⟨(·)⟩
instance : OFE.Discrete (PermissionRat α) := ⟨congrArg id⟩

variable {α : Type*}

/-- Validity: pointwise budget `≤ 1`. -/
def valid (p : PermissionRat α) : Prop := ∀ a, (p a) ≤ (1 : ℚ≥0)

/-- Core choice: constant-0 function (the additive unit). -/
def zero : PermissionRat α := fun _ => (0 : ℚ≥0)

def one : PermissionRat α := fun _ => (1 : ℚ≥0)

instance : Zero (PermissionRat α) := ⟨zero⟩
instance : One (PermissionRat α) := ⟨one⟩

/-- Primitive pcore. Defined to be the constant-0 function for every permission. -/
def pcore : Option (PermissionRat α) := some (zero : PermissionRat α)

/-- Primitive op (pointwise addition). -/
def op (p q : PermissionRat α) : PermissionRat α := fun a => p a + q a

/-- CMRA structure for `PermissionRat`. -/
noncomputable instance : CMRA (PermissionRat α) where
  pcore := fun _ => pcore
  op := op
  ValidN _ p := valid (α := α) p
  Valid p := valid (α := α) p
  op_ne := { ne _ _ _ := congrArg (op _) }
  pcore_ne {_} := by
    intro x y cx hxy hcx
    -- pcore is constant; deduce cx = zero
    have hx : cx = zero := by
      have : some cx = some (zero : PermissionRat α) := by simpa [pcore] using hcx.symm
      exact Option.some.inj this
    refine ⟨zero, by simp [pcore], ?_⟩
    simp [hx]
  validN_ne := by
    intro _ x y hxy
    have : x = y := hxy
    simp_all
  valid_iff_validN := ⟨fun v _ => v, fun v => v 0⟩
  validN_succ := id
  validN_op_left := by
    intro n p q hv a
    have : p a + q a ≤ (1 : ℚ≥0) := hv a
    have hle : p a ≤ p a + q a := by simp
    exact le_trans hle this
  assoc := by intro x y z; funext a; simp [op, add_assoc]
  comm := by intro x y; funext a; simp [op, add_comm]
  pcore_op_left := by intro x cx hx; cases hx; funext a; simp [op, pcore, zero]
  pcore_idem := by intro x cx hx; cases hx; rfl
  pcore_op_mono := by
    intro x cx hx y
    -- From hx, cx = zero
    have hx' : cx = zero := by
      have : some cx = some (zero : PermissionRat α) := by
        simpa [pcore] using hx.symm
      exact Option.some.inj this
    refine ⟨zero, ?_⟩
    -- pcore (x ⊗ y) = some zero = some (cx ⊗ zero)
    -- after rewriting cx = zero
    simp [pcore, op, zero, hx', CMRA.op]
    unfold zero op
    simp
  extend {n x y₁ y₂} Hvalid Heq := by
    -- In a discrete OFE, Dist implies Eq; pick trivial witnesses
    have Heq' := (discrete Heq)
    refine ⟨y₁, y₂, ?_, ?_, ?_⟩
    · -- x ≡ y₁ ⊗ y₂ by discrete Dist
      simpa [op] using Heq'
    · rfl
    · rfl

/-- UCMRA instance: unit is the constant-0 function, which matches the RA unit. -/
noncomputable instance : UCMRA (PermissionRat α) where
  unit := (zero : PermissionRat α)
  unit_valid := by intro a; simp [valid, zero]
  unit_left_id := by intro x; funext a; simp [op, zero, instCMRA]
  pcore_unit := by simp [pcore, zero, CMRA.pcore]

end PermissionRat

end Bluebell
