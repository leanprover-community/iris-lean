# Changes 

This page lists the important changes between Iris-Lean and Iris-Rocq, as well as our plans for preserving forward-compatilibity with future versions of Iris. 

## Restriction to Leibniz OFEs

All `OFE` types in Iris-Lean must be Leibniz: there is no field for equivlances in `OFE` as it is expected that equivalence coincides with equality.
Doing so enables vastly better interoperability between Iris constructions and Lean tactics.

#### Compatibility

An `OFE` that is not Leibniz can be made so using a quotient type; `OFE.ofQuotient` provides a constructor for an `OFE` instance with an equivalence provided. 
`Agree.lean` demonstrates how to apply this technique. 
We expect it to work for all `OFE` constructions.

## Generalized Heap Types

In several places (`HeapView.lean`), `gmap` has been generalized to `LawfulPartialMap` or `LawfulFiniteMap`. 
This generalization means some constructions like `HeapView.lean` lose the constraint that map domains must be finite, and all constructions lose the constraint that key types must be countable.

#### Compatibility

This is a straightforward generalization: you can make the same generalization using `LawfulPartialMap`, or `LawfulFiniteMap` if the domain of your map must be finite. 
If you would prefer a concrete map type both `(K → Option ·)` or `ExtTreeMap` are good options (see `HeapInstances.lean`, for the latter note that you can always define a trivial order on key types). 

## Set-based Quantifiers in BI

The type of the `forall` and `exists` quantifiers in `BIBase.lean` are set-based, rather than indexed. In Lean:
```lean
class BIBase (PROP : Type u) where
  sForall : (PROP → Prop) → PROP
  sExists : (PROP → Prop) → PROP
```
vs. in Rocq:
```rocq
Section bi_mixin.
  Context {PROP : Type} `{!Dist PROP, !Equiv PROP}.
  Context (bi_forall : ∀ A, (A → PROP) → PROP).
  Context (bi_exist : ∀ A, (A → PROP) → PROP).
```
This ameliorates some universe issues and quantify over types in any universe, as demonstrated in the following snippet:

```lean
namespace Indexed /- Indexed quantifiers -/
class BI (PROP : Type _) : Type _ where
  iQuantifier {A : Type _} : (A → PROP) → PROP
variable (PROP : Type 3) [BI PROP]
variable (X : Type 2) (Y : Type 2) (d : X → PROP)
-- Breaks when the universes for X and Y disagree:
#check BI.iQuantifier (fun y : Y => BI.iQuantifier d)
end Indexed

namespace Set /- Set-based quantifiers -/
class BI (PROP : Type _) : Type _ where
  sQuantifier : (PROP → Prop) → PROP
def BI.iQuantifier {PROP : Type _} [BI PROP] {ι : Type _} (I : ι → PROP) : PROP :=
  BI.sQuantifier (fun P => ∃ i : ι, I i = P)
variable (PROP : Type 1) [BI PROP]
variable (X : Type 2) (Y : Type 6) (d : X → PROP)
-- Works no matter the universe levels for X, Y and PROP:
#check BI.iQuantifier (fun y : Y => BI.iQuantifier d)
end Set
```

#### Compatibility

This change is known to cause issues with syntactic presentations of higher-order logic (a la Nola), however suspect that semantic presentations can be generalized in this form. 
Comment with a GitHub issue or in the [Zulip thread](https://leanprover.zulipchat.com/#narrow/channel/490604-iris-lean/topic/Why.20are.20sForall.20and.20sExists.20defined.20the.20way.20they.20are.3F/with/571684692) if you have issues with this.

## Unbundled Typeclass Hierarchy 

Iris-Lean does not use canonical structures, using typeclasses instead. 

#### Compatibility 

While typeclasses are mostly a drop-in replacement for canonical structures, replicating all behaviours of canonical structures is still an open question (importantly: the default inference of terms including metavariables).
Options are being considered on the [Zulip](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Emulating.20eager.20default.20instance.3F/with/622571850).



