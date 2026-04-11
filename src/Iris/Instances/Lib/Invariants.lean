/-
Copyright (c) 2026 Sergei Stepanenko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.Algebra
public import Iris.ProofMode
public import Iris.BI.Algebra
public import Iris.Std.Namespaces
public import Iris.Instances.IProp
public import Iris.Instances.Lib.FUpd

@[expose] public section

/-! ## Invariants
TODO: into_inv_inv, into_acc_inv
-/

namespace Iris.Inv

open Iris OFE COFE BI FUpd

section InvariantDefinition

variable {GF : BundledGFunctors} [InvGS_gen hlc GF]

def inv (N : Namespace) (P : IProp GF) : IProp GF :=
  sorry

def own_inv (N : Namespace) (P : IProp GF) : IProp GF :=
  sorry

end InvariantDefinition

section Instances

variable {GF : BundledGFunctors} [InvGS_gen hlc GF]

instance inv_contractive (N : Namespace) : Contractive (inv (GF := GF) N) := by
  sorry

instance inv_ne (N : Namespace) : NonExpansive (inv (GF := GF) N) := by
  sorry

instance inv_persistent (N : Namespace) (P : IProp GF) : Persistent (inv N P) := by
  sorry

instance is_except_0_inv (N : Namespace) (P : IProp GF) : ProofMode.IsExcept0 (inv N P) := by
  sorry

end Instances

section BasicLemmas

variable {GF : BundledGFunctors} [InvGS_gen hlc GF]

theorem own_inv_acc (E : CoPset) (N : Namespace) (P : IProp GF) :
  ⊢ own_inv N P -∗ |={E, E}=> ▷ P ∗ (▷ P -∗ |={E, E}=> True) := by
  sorry

-- Fresh invariant name exists
-- TODO: Requires proper Namespace and Finset types
-- theorem fresh_inv_name (E : Finset Nat) (N : Namespace) :
--   ∃ i, i ∉ E ∧ i ∈ N.toSet := by
--   sorry

theorem own_inv_alloc (N : Namespace) (E : CoPset) (P : IProp GF) :
  ⊢ ▷ P -∗ |={E}=> own_inv N P := by
  sorry

theorem own_inv_alloc_open (N : Namespace) (E : CoPset) (P : IProp GF) :
  ⊢ |={E, E}=> own_inv N P ∗ (▷ P -∗ |={E, E}=> True) := by
  sorry

theorem own_inv_to_inv (M : Namespace) (P : IProp GF) :
  ⊢ own_inv M P -∗ inv M P := by
  sorry

end BasicLemmas

section Allocation

variable {GF : BundledGFunctors} [InvGS_gen hlc GF]

theorem inv_alloc (N : Namespace) (E : CoPset) (P : IProp GF) :
  ⊢ ▷ P -∗ |={E}=> inv N P := by
  sorry

theorem inv_alloc_open (N : Namespace) (E : CoPset) (P : IProp GF) :
  ⊢ |={E, E}=> inv N P ∗ (▷ P -∗ |={E, E}=> True) := by
  sorry

end Allocation

section Access

variable {GF : BundledGFunctors} [InvGS_gen hlc GF]

theorem inv_acc (E : CoPset) (N : Namespace) (P : IProp GF) :
  ⊢ inv N P -∗ |={E, E}=> ▷ P ∗ (▷ P -∗ |={E, E}=> True) := by
  sorry

theorem inv_acc_strong (E : CoPset) (N : Namespace) (P : IProp GF) :
  ⊢ inv N P -∗ |={E, E}=>
    ▷ P ∗ (∀ E', ▷ P -∗ |={E', E'}=> True) := by
  sorry

theorem inv_acc_timeless (E : CoPset) (N : Namespace) (P : IProp GF) [Timeless P] :
  ⊢ inv N P -∗ |={E, E}=> P ∗ (P -∗ |={E, E}=> True) := by
  sorry

end Access

section Modification

variable {GF : BundledGFunctors} [InvGS_gen hlc GF]

theorem inv_alter (N : Namespace) (P Q : IProp GF) :
  ⊢ inv N P -∗ ▷ □ (P -∗ iprop(Q ∗ (Q -∗ P))) -∗ inv N Q := by
  sorry

theorem inv_iff (N : Namespace) (P Q : IProp GF) :
  ⊢ inv N P -∗ ▷ □ (P ↔ Q) -∗ inv N Q := by
  sorry

end Modification

section Combination

variable {GF : BundledGFunctors} [InvGS_gen hlc GF]

theorem inv_combine (N1 N2 N : Namespace) (P Q : IProp GF) :
  ⊢ inv N1 P -∗ inv N2 Q -∗ inv N iprop(P ∗ Q) := by
  sorry

theorem inv_combine_dup_l (N : Namespace) (P Q : IProp GF) :
  ⊢ □ (P -∗ iprop(P ∗ P)) -∗ inv N P -∗ inv N Q -∗ inv N iprop(P ∗ Q) := by
  sorry

end Combination

section Splitting

variable {GF : BundledGFunctors} [InvGS_gen hlc GF]

theorem inv_split_l (N : Namespace) (P Q : IProp GF) :
  ⊢ inv N iprop(P ∗ Q) -∗ inv N P := by
  sorry

theorem inv_split_r (N : Namespace) (P Q : IProp GF) :
  ⊢ inv N iprop(P ∗ Q) -∗ inv N Q := by
  sorry

theorem inv_split (N : Namespace) (P Q : IProp GF) :
  ⊢ inv N iprop(P ∗ Q) -∗ iprop(inv N P ∗ inv N Q) := by
  sorry

end Splitting

section Except0

variable {GF : BundledGFunctors} [InvGS_gen hlc GF]

theorem except_0_inv (N : Namespace) (P : IProp GF) :
  ⊢ ◇ inv N P -∗ inv N P := by
  sorry

end Except0

end Iris.Inv

end
