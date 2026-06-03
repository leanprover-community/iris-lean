module

public import Mathlib.Tactic.Linter.Header
public import Iris

/-! # Reference: the functional model of `LawfulPartialMap`

The denotation of every lawful partial map is a function `K → Option V`, and the 7 laws say each
operation acts correctly on that function. This file records the canonical functional ops so that
subagent prototypes can mirror the proof shape: implement `den : R V → (K → Option V)`, prove it
commutes with each op, and the laws fall out.

Non-extensionality lever: let `R V` carry MORE structure than the function determines (a log, an
unnormalized representative, a non-canonical encoding) while keeping `den` forgetful. Then
`equiv ↔ eq` fails: distinct representatives, same denotation.
-/

@[expose] public section

namespace IrisMath.PMapHarness

open Iris.Std Iris.Std.PartialMap

/-- The functional denotation model `K → Option V`. -/
abbrev Den (K V : Type _) := K → Option V

namespace Den

variable {K V V' : Type _} [DecidableEq K]

def empty : Den K V := fun _ => none
def insert (m : Den K V) (k : K) (v : V) : Den K V := fun k' => if k = k' then some v else m k'
def delete (m : Den K V) (k : K) : Den K V := fun k' => if k = k' then none else m k'
def bindAlter (f : K → V → Option V') (m : Den K V) : Den K V' := fun k => (m k).bind (f k)
def merge (op : K → V → V → V) (m₁ m₂ : Den K V) : Den K V :=
  fun k => Option.merge (op k) (m₁ k) (m₂ k)

theorem get_empty (k : K) : (empty : Den K V) k = none := rfl
theorem get_insert_eq {m : Den K V} {k k' v} : k = k' → (insert m k v) k' = some v := by
  intro h; simp [insert, h]
theorem get_insert_ne {m : Den K V} {k k' v} : k ≠ k' → (insert m k v) k' = m k' := by
  intro h; simp [insert, h]
theorem get_delete_eq {m : Den K V} {k k'} : k = k' → (delete m k) k' = none := by
  intro h; simp [delete, h]
theorem get_delete_ne {m : Den K V} {k k'} : k ≠ k' → (delete m k) k' = m k' := by
  intro h; simp [delete, h]

end Den

end IrisMath.PMapHarness
