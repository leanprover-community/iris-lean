/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Michael Sammler, Yunsong Yang
-/
module

public import Iris.BI
public import Iris.ProofMode.Classes
public import Iris.Std
public meta import Iris.Std.Expr

public meta section

namespace Iris.ProofMode
open Lean Expr Meta Qq BI Std

@[expose, match_pattern] def nameAnnotation := `name
@[expose, match_pattern] def ivarAnnotation := `ivar

/--
Identity wrapper used as a marker around top-level Iris hypotheses.
This is to solve the issues that `rw` and `simp` may erase the metadata of a hypothesis,
which is needed for the proof mode pretty-printer/parser to display the hypothesis correctly.

The underlying issue is `rw`'s `kabstract`-based implementation: without a real head symbol,
rewriting can abstract away the metadata wrapper and the pretty-printer/parser loses
the named hypothesis.

`IrisHyp` should be only inserted at the outermost level of Iris hypotheses.
See https://github.com/leanprover-community/iris-lean/issues/469
-/
@[expose, reducible] public def IrisHyp {α : Sort u} (x : α) : α := x

structure IVarId where
  name : Name
  -- caches whether the ivar is persistent or not to allow
  -- retrieving this information in O(1) and without `Hyps`
  -- TODO: cache more here? E.g. also the user name?
  persistent? : Bool
  deriving Inhabited, BEq, Hashable, Repr, DecidableEq

def IVarId.spatial? (ivar : IVarId) : Bool := !ivar.persistent?

def mkFreshIVarId [Monad m] [MonadNameGenerator m] (persistent? : Bool) : m IVarId :=
  return { name := (← mkFreshId), persistent? }

@[expose] def IVarIdSet := Std.TreeSet IVarId (Name.quickCmp ·.name ·.name)
  deriving Inhabited, EmptyCollection, Singleton

def parseName? : Expr → Option (Name × Name × Expr)
  | .mdata ⟨[(nameAnnotation, .ofName name), (ivarAnnotation, .ofName ivar)]⟩
      (.app (.app c _α) e) => do
    if c.constName? != some ``IrisHyp then
      failure
    some (name, ivar, e)
  | _ => none

def mkNameAnnotation {prop : Q(Type u)} (name : Name) (ivar : IVarId)
    (e : Q($prop)) : Q($prop) :=
  .mdata ⟨[(nameAnnotation, .ofName name), (ivarAnnotation, .ofName ivar.name)]⟩ q(IrisHyp $e)

def getFreshName : TSyntax ``binderIdent → CoreM (Name × Syntax)
  | `(binderIdent| $name:ident) => pure (name.getId, name)
  | stx => return (← mkFreshUserName `x, stx)

def isTrue (p : Q(Bool)) : Bool := p.constName! == ``true

def matchBool (p : Q(Bool)) : ($p =Q true) ⊕' ($p =Q false) :=
  if isTrue p then .inl ⟨⟩ else .inr ⟨⟩

/--
  Given two values `p1` and `p2`, check whether both are syntactically
  `q(true)` and, if so, return `q(true)`. Otherwise, return `q(false)`.
  This is useful for determining whether the combined hypothesis should
  exist in the intuitionistic context or the spatial context.
-/
def conj (p1 p2 : Q(Bool)) : Q(Bool) :=
  match matchBool p1, matchBool p2 with
  | .inl _, .inl _ => q(true)
  | _, _           => q(false)

def mkIntuitionisticIf {prop : Q(Type u)} (_bi : Q(BI $prop))
    (p : Q(Bool)) (e : Q($prop)) : {A : Q($prop) // $A =Q iprop(□?$p $e)} :=
  match matchBool p with
  | .inl _ => ⟨q(iprop(□ $e)), ⟨⟩⟩
  | .inr _ => ⟨e, ⟨⟩⟩

section Hyp

structure Hyp (prop : Q(Type u)) where
  name : Name
  ivar : IVarId
  p : Q(Bool)
  ty : Q($prop)
  deriving Inhabited, Repr

/-- The un-annotated proposition of this hypothesis: `□?p ty`. -/
def Hyp.e {prop : Q(Type u)} (bi : Q(BI $prop)) (h : Hyp prop) :
    {A : Q($prop) // $A =Q iprop(□?$(h.p) $(h.ty))} :=
  mkIntuitionisticIf bi h.p h.ty

def Hyp.tm {prop : Q(Type u)} (bi : Q(BI $prop)) (h : Hyp prop) : Q($prop) :=
  mkIntuitionisticIf bi h.p (mkNameAnnotation h.name h.ivar h.ty)

def Hyp.persistent? (h : Hyp prop) : Bool := isTrue h.p

def Hyp.spatial? (h : Hyp prop) : Bool := !isTrue h.p

@[inline] def sepFold {prop : Q(Type u)} (bi : Q(BI $prop))
    (proj : Hyp prop → Q($prop)) (hs : Array (Hyp prop)) : Q($prop) :=
  if h : 0 < hs.size then
    hs.foldl (init := proj hs[0]) (start := 1) fun acc x => q(iprop($acc ∗ $(proj x)))
  else q(emp)

def sepFoldE {prop : Q(Type u)} (bi : Q(BI $prop)) (hs : Array (Hyp prop)) : Q($prop) :=
  sepFold bi (fun h => (h.e bi).1) hs

def sepFoldTm {prop : Q(Type u)} (bi : Q(BI $prop)) (hs : Array (Hyp prop)) : Q($prop) :=
  sepFold bi (·.tm bi) hs

end Hyp

section Theorems
open Iris BI

-- base cases (first element)
theorem part_init_l [BI PROP] {x : PROP}     : x ⊣⊢ x ∗ emp := sep_emp.symm
theorem part_init_r [BI PROP] {x : PROP}     : x ⊣⊢ emp ∗ x := emp_sep.symm
theorem part_init_b [BI PROP] {x : PROP}     : □ x ⊣⊢ □ x ∗ □ x := intuitionistically_sep_idem.symm

-- general step, both sides already non-empty
theorem part_l [BI PROP] {A L R x : PROP} (h : A ⊣⊢ L ∗ R) : A ∗ x ⊣⊢ (L ∗ x) ∗ R :=
  (sep_congr_left h).trans sep_right_comm
theorem part_r [BI PROP] {A L R x : PROP} (h : A ⊣⊢ L ∗ R) : A ∗ x ⊣⊢ L ∗ (R ∗ x) :=
  (sep_congr_left h).trans sep_assoc
theorem part_b [BI PROP] {A L R x : PROP} (h : A ⊣⊢ L ∗ R) :
    A ∗ □ x ⊣⊢ (L ∗ □ x) ∗ (R ∗ □ x) :=
  (sep_congr h intuitionistically_sep_idem.symm).trans sep_sep_sep_comm

-- boundary steps, needed only to avoid emitting `emp ∗ _` / `_ ∗ emp` in the results
theorem part_l_of_emptyL [BI PROP] {A R x : PROP} (h : A ⊣⊢ emp ∗ R) : A ∗ x ⊣⊢ x ∗ R :=
  (sep_congr_left (h.trans emp_sep)).trans sep_comm
theorem part_r_of_emptyR [BI PROP] {A L x : PROP} (h : A ⊣⊢ L ∗ emp) : A ∗ x ⊣⊢ L ∗ x :=
  sep_congr_left (h.trans sep_emp)
theorem part_b_of_emptyL [BI PROP] {A R x : PROP} (h : A ⊣⊢ emp ∗ R) :
    A ∗ □ x ⊣⊢ □ x ∗ (R ∗ □ x) :=
  calc
    _ ⊣⊢ (emp ∗ R) ∗ □ x := sep_congr_left h
    _ ⊣⊢ R ∗ □ x         := sep_congr_left emp_sep
    _ ⊣⊢ □ x ∗ (R ∗ □ x) := by
      have : □ x ∗ (R ∗ □ x) ⊣⊢ R ∗ □ x :=
        calc
          _ ⊣⊢ (□ x ∗ R) ∗ □ x := sep_assoc.symm
          _ ⊣⊢ (R ∗ □ x) ∗ □ x := sep_congr_left sep_comm
          _ ⊣⊢ R ∗ (□ x ∗ □ x) := sep_assoc
          _ ⊣⊢ R ∗ □ x         := sep_congr_right intuitionistically_sep_idem
      exact this.symm

theorem part_b_of_emptyR [BI PROP] {A L x : PROP} (h : A ⊣⊢ L ∗ emp) :
    A ∗ □ x ⊣⊢ (L ∗ □ x) ∗ □ x :=
  calc
    _ ⊣⊢ (L ∗ emp) ∗ □ x := sep_congr_left h
    _ ⊣⊢ L ∗ □ x         := sep_congr_left sep_emp
    _ ⊣⊢ (L ∗ □ x) ∗ □ x := by
      have : (L ∗ □ x) ∗ □ x ⊣⊢ L ∗ □ x :=
        calc
          _ ⊣⊢ L ∗ (□ x ∗ □ x) := sep_assoc
          _ ⊣⊢ L ∗ □ x         := sep_congr_right intuitionistically_sep_idem
      exact this.symm

end Theorems

section hyps

structure Hyps {prop : Q(Type u)} (bi : Q(BI $prop)) (e : Q($prop)) where
  mk ::
  /-- the hypotheses in context order; the *only* representation of the context -/
  toArray : Array (Hyp prop)
  /-- cached annotated term, definitionally equal to `e` (see `sepFoldTm`) -/
  tm : Q($prop)
  deriving Repr

def Hyps.ofArray {prop : Q(Type u)} (bi : Q(BI $prop)) (hs : Array (Hyp prop))
    (e := sepFoldE bi hs) : Hyps bi e :=
  ⟨hs, sepFoldTm bi hs⟩

instance : Inhabited (Hyps bi s) := ⟨⟨#[], s⟩⟩

def Hyps.mkEmp {prop : Q(Type u)} (bi : Q(BI $prop)) (e := q(BI.emp : $prop)) : Hyps bi e :=
  Hyps.ofArray bi #[] e

def Hyps.mkHyp {prop : Q(Type u)} (bi : Q(BI $prop))
    (name : Name) (ivar : IVarId) (p : Q(Bool)) (ty : Q($prop)) (e := q(iprop(□?$p $ty))) :
    Hyps bi e :=
  Hyps.ofArray bi #[{ name, ivar, p, ty }] e

def Hyps.add {prop : Q(Type u)} (bi : Q(BI $prop))
    (name : Name) (ivar : IVarId) (p : Q(Bool)) (ty : Q($prop)) {e} (h : Hyps bi e)
    : (e' : Q($prop)) × Hyps bi e' × Q(iprop($e ∗ □?$p $ty ⊣⊢ $e')) :=
  let hyp : Hyp prop := { name, ivar, p, ty }
  if h.toArray.isEmpty then
    have : $e =Q emp := ⟨⟩
    ⟨_, Hyps.mkHyp bi name ivar p ty, q(emp_sep)⟩
  else
    ⟨_, Hyps.ofArray bi (h.toArray.push hyp), q(sorry)⟩

partial def parseHyps? {prop : Q(Type u)} (bi : Q(BI $prop)) (expr : Expr) :
    Option ((s : Q($prop)) × Hyps bi s) := do
  let hs ← go expr #[]
  some ⟨_, Hyps.ofArray bi hs⟩
where
  parseLeaf? (e : Expr) : Option (Hyp prop) :=
    if let some #[_, _, P] := appM? e ``intuitionistically then do
      let (name, ivar, ty) ← parseName? P
      some { name, ivar := ⟨ivar, true⟩, p := q(true), ty }
    else do
      let (name, ivar, ty) ← parseName? e
      some { name, ivar := ⟨ivar, false⟩, p := q(false), ty }
  go (e : Expr) (acc : Array (Hyp prop)) : Option (Array (Hyp prop)) := do
    if let some #[_, _, P, Q] := appM? e ``sep then do
      let acc ← go P acc
      some (acc.push (← parseLeaf? Q))
    else if e.isAppOfArity ``emp 2 && acc.isEmpty then
      some acc
    else
      some (acc.push (← parseLeaf? e))

partial def Hyps.find? {u prop bi e} (name : Name)
    (h : @Hyps u prop bi e) : Option (IVarId × Q($prop)) :=
  h.toArray.findSomeRev? fun x => if name == x.name then some (x.ivar, x.ty) else none

def Hyps.findM? [Monad m] {prop : Q(Type u)} {bi : Q(BI $prop)}
    (p : Name → IVarId → Q(Bool) → Q($prop) → m Bool) {e} (hyps : Hyps bi e) :
    m (Option (Name × IVarId × Q(Bool) × Q($prop))) :=
  hyps.toArray.findSomeRevM? fun x => do
    if ← p x.name x.ivar x.p x.ty then
      return some (x.name, x.ivar, x.p, x.ty)
    else
      return none

partial def Hyps.getDecl? {u prop bi} (ivar : IVarId) {s}:
    @Hyps u prop bi s → Option (Name × IVarId × Q(Bool) × Q($prop)) := fun h =>
  h.toArray.findSomeRev? fun x => if ivar == x.ivar then some (x.name, x.ivar, x.p, x.ty) else none

def Hyps.getUserName? {u prop bi} (ivar : IVarId) (h : @Hyps u prop bi s) : Option Name :=
  h.getDecl? ivar |>.map (·.1)

def Hyps.spatialIVarIds {u prop bi} {s} (hyps : @Hyps u prop bi s) : List IVarId :=
  (hyps.toArray.filterMap fun x => if x.spatial? then some x.ivar else none).toList

def Hyps.intuitionisticIVarIds {u prop bi} {s} (hyps : @Hyps u prop bi s) : List IVarId :=
  (hyps.toArray.filterMap fun x => if x.persistent? then some x.ivar else none).toList

private def Hyps.accuGo {prop : Q(Type u)} (bi : Q(BI $prop))
    (hs : Array (Hyp prop)) (k : Nat) (e' sp : Q($prop)) (pf : Q($e' ⊢ $sp)) :
    (a sp' : Q($prop)) × Q(iprop($a ∗ $e') ⊢ $sp') :=
  match k with
  | 0 =>
    have pf' : Q(iprop((emp : $prop) ∗ $e') ⊢ $sp) := q(emp_sep.mp.trans $pf)
    ⟨q(emp), sp, pf'⟩
  | j + 1 =>
    let x := hs[j]!
    let ty := x.ty
    let ⟨xe, _⟩ := x.e bi
    -- one hypothesis: from `pf : e' ⊢ sp` build `xe ∗ e' ⊢ sp1`
    let ⟨sp1, pf1⟩ : (sp1 : Q($prop)) × Q(iprop($xe ∗ $e') ⊢ $sp1) :=
      match matchBool x.p with
      | .inl _ =>   -- intuitionistic: dropped
        have h : Q(iprop(□ $ty ∗ $e') ⊢ $sp) :=
          q((sep_mono_left intuitionistically_elim_emp).trans (emp_sep.mp.trans $pf))
        ⟨sp, h⟩
      | .inr _ =>   -- spatial: accumulated
        if sp == (q(emp) : Q($prop)) then
          have pfE : Q($e' ⊢ (emp : $prop)) := pf
          have h : Q(iprop($ty ∗ $e') ⊢ $ty) := q((sep_mono_right $pfE).trans sep_emp.mp)
          ⟨ty, h⟩
        else
          have h : Q(iprop($ty ∗ $e') ⊢ iprop($ty ∗ $sp)) := q(sep_mono_right $pf)
          ⟨q(iprop($ty ∗ $sp)), h⟩
    if j = 0 then
      ⟨xe, sp1, pf1⟩
    else
      let ⟨a, sp2, pf2⟩ := Hyps.accuGo bi hs j q(iprop($xe ∗ $e')) sp1 pf1
      have pf3 : Q(iprop(($a ∗ $xe) ∗ $e') ⊢ $sp2) := q(sep_assoc.mp.trans $pf2)
      ⟨q(iprop($a ∗ $xe)), sp2, pf3⟩


/--
  Given any hypotheses `hyps` representing `e`, filter in all spatial hypotheses
  and prove that `e` implies the set of spatial hypotheses.
-/
def Hyps.buildAccuProof {prop : Q(Type u)} {bi : Q(BI $prop)} {e}
    (hyps : Hyps bi e) : (spatialProps : Q($prop)) × Q($e ⊢ $spatialProps) :=
  let hs := hyps.toArray
  have pf0 : Q(iprop(emp : $prop) ⊢ iprop(emp : $prop)) := q(.rfl)
  let ⟨a, sp, pf⟩ := Hyps.accuGo bi hs hs.size q(emp) q(emp) pf0
  have pfA : Q($a ⊢ $sp) := q(sep_emp.mpr.trans $pf)
  have pfE : Q($e ⊢ $sp) := pfA   -- `a` is the canonical fold of `hs`, i.e. `e`
  ⟨sp, pfE⟩

variable (oldIVar : IVarId) (new : Name) {prop : Q(Type u)} {bi : Q(BI $prop)} in
def Hyps.rename {e} (h : Hyps bi e) : Option (Hyps bi e) := do
  let i ← h.toArray.findIdx? (·.ivar == oldIVar)     -- rhs-first, as before
  let hs := h.toArray.modify i ({ · with name := new })
  some ⟨hs, sepFoldTm bi hs⟩     -- `e` unchanged; only `tm` is rebuilt

def Hyps.select (ty : Expr) :
    ∀ {s}, @Hyps u prop bi s → MetaM (IVarId × Q(Bool) × Q($prop)) := fun h => do
  let some r ← h.toArray.findSomeRevM? fun x => do
    if ← isDefEq ty x.ty then pure (some (x.ivar, x.p, x.ty)) else pure none
    | failure
  pure r

theorem intuitionistically_sep_dup [BI PROP] {P : PROP} : □ P ⊣⊢ □ P ∗ □ P :=
  intuitionistically_sep_idem.symm

theorem sep_emp_rev [BI PROP] {P : PROP} : P ⊣⊢ P ∗ emp := sep_emp.symm

theorem emp_sep_rev [BI PROP] {P : PROP} : P ⊣⊢ emp ∗ P := emp_sep.symm

section split


inductive Side | left | right | both deriving DecidableEq

private def Hyps.partitionGo {prop : Q(Type u)} (bi : Q(BI $prop))
    (side : Hyp prop → Side) (hs : Array (Hyp prop)) (k : Nat)
    (l r : Array (Hyp prop)) (a el er : Q($prop)) (pf : Q($a ⊣⊢ $el ∗ $er)) :
    (a' el' er' : Q($prop)) × Array (Hyp prop) × Array (Hyp prop) ×
      Q($a' ⊣⊢ $el' ∗ $er') :=
  if hk : k < hs.size then
    let x := hs[k]
    match side x, matchBool x.p with
    -- `both` duplicates an intuitionistic hypothesis into each half.
    -- Note we spell `□ $ty` out syntactically instead of going through `x.e`,
    -- so that Qq can see the `□` that `part_b*` needs.  The resulting `Expr` is
    -- identical to `(x.e bi).1`, so canonicity is preserved.
    | .both, .inl _ =>
      let ty := x.ty
      if l.isEmpty then
        have pfE : Q($a ⊣⊢ iprop((emp : $prop) ∗ $er)) := pf
        have pf' : Q(iprop($a ∗ □ $ty) ⊣⊢ iprop(□ $ty ∗ ($er ∗ □ $ty))) :=
          q(part_b_of_emptyL $pfE)
        partitionGo bi side hs (k + 1) (l.push x) (r.push x)
          q(iprop($a ∗ □ $ty)) q(iprop(□ $ty)) q(iprop($er ∗ □ $ty)) pf'
      else if r.isEmpty then
        have pfE : Q($a ⊣⊢ iprop($el ∗ (emp : $prop))) := pf
        have pf' : Q(iprop($a ∗ □ $ty) ⊣⊢ iprop(($el ∗ □ $ty) ∗ □ $ty)) :=
          q(part_b_of_emptyR $pfE)
        partitionGo bi side hs (k + 1) (l.push x) (r.push x)
          q(iprop($a ∗ □ $ty)) q(iprop($el ∗ □ $ty)) q(iprop(□ $ty)) pf'
      else
        have pf' : Q(iprop($a ∗ □ $ty) ⊣⊢ iprop(($el ∗ □ $ty) ∗ ($er ∗ □ $ty))) :=
          q(part_b $pf)
        partitionGo bi side hs (k + 1) (l.push x) (r.push x)
          q(iprop($a ∗ □ $ty)) q(iprop($el ∗ □ $ty)) q(iprop($er ∗ □ $ty)) pf'
    | .right, _ =>
      let ⟨xe, _⟩ := x.e bi
      if r.isEmpty then
        have pfE : Q($a ⊣⊢ iprop($el ∗ (emp : $prop))) := pf
        have pf' : Q(iprop($a ∗ $xe) ⊣⊢ iprop($el ∗ $xe)) := q(part_r_of_emptyR $pfE)
        partitionGo bi side hs (k + 1) l (r.push x) q(iprop($a ∗ $xe)) el xe pf'
      else
        have pf' : Q(iprop($a ∗ $xe) ⊣⊢ iprop($el ∗ ($er ∗ $xe))) := q(part_r $pf)
        partitionGo bi side hs (k + 1) l (r.push x)
          q(iprop($a ∗ $xe)) el q(iprop($er ∗ $xe)) pf'
    -- `.left`, plus the defensive case `.both` on a *spatial* hypothesis, which
    -- would be unsound to duplicate.  Callers must not produce it.
    | _, _ =>
      let ⟨xe, _⟩ := x.e bi
      if l.isEmpty then
        have pfE : Q($a ⊣⊢ iprop((emp : $prop) ∗ $er)) := pf
        have pf' : Q(iprop($a ∗ $xe) ⊣⊢ iprop($xe ∗ $er)) := q(part_l_of_emptyL $pfE)
        partitionGo bi side hs (k + 1) (l.push x) r q(iprop($a ∗ $xe)) xe er pf'
      else
        have pf' : Q(iprop($a ∗ $xe) ⊣⊢ iprop(($el ∗ $xe) ∗ $er)) := q(part_l $pf)
        partitionGo bi side hs (k + 1) (l.push x) r
          q(iprop($a ∗ $xe)) q(iprop($el ∗ $xe)) er pf'
  else
    ⟨a, el, er, l, r, pf⟩
termination_by hs.size - k

def Hyps.partition {prop : Q(Type u)} {bi : Q(BI $prop)} {e}
    (hyps : Hyps bi e) (side : Hyp prop → Side) :
    (el er : Q($prop)) × Hyps bi el × Hyps bi er × Q($e ⊣⊢ $el ∗ $er) :=
  let hs := hyps.toArray
  if h : 0 < hs.size then
    let x := hs[0]
    -- The first hypothesis is special: the fold of `hs[0…0]` is `x` itself,
    -- with no `∗` above it, so the three `part_init_*` lemmas are needed.
    let ⟨_, el, er, l, r, pf⟩ :=
      match side x, matchBool x.p with
      | .both, .inl _ =>
        let ty := x.ty
        have pf : Q(iprop(□ $ty) ⊣⊢ iprop(□ $ty ∗ □ $ty)) := q(part_init_b)
        Hyps.partitionGo bi side hs 1 #[x] #[x]
          q(iprop(□ $ty)) q(iprop(□ $ty)) q(iprop(□ $ty)) pf
      | .right, _ =>
        let ⟨xe, _⟩ := x.e bi
        have pf : Q($xe ⊣⊢ iprop((emp : $prop) ∗ $xe)) := q(part_init_r)
        Hyps.partitionGo bi side hs 1 #[] #[x] xe q(emp) xe pf
      | _, _ =>
        let ⟨xe, _⟩ := x.e bi
        have pf : Q($xe ⊣⊢ iprop($xe ∗ (emp : $prop))) := q(part_init_l)
        Hyps.partitionGo bi side hs 1 #[x] #[] xe xe q(emp) pf
    -- `a'` is the canonical fold of all of `hs`, i.e. `e` itself.
    have pf : Q($e ⊣⊢ $el ∗ $er) := pf
    ⟨el, er, Hyps.ofArray bi l el, Hyps.ofArray bi r er, pf⟩
  else
    have pf0 : Q(iprop(emp : $prop) ⊣⊢ iprop((emp : $prop) ∗ (emp : $prop))) :=
      q(emp_sep_rev)
    have pf : Q($e ⊣⊢ iprop((emp : $prop) ∗ (emp : $prop))) := pf0
    ⟨q(emp), q(emp), Hyps.ofArray bi #[], Hyps.ofArray bi #[], pf⟩

def Hyps.split {prop : Q(Type u)} (bi : Q(BI $prop)) (toRight : Name → IVarId → Bool)
    {e} (hyps : Hyps bi e) :
    (elhs erhs : Q($prop)) × Hyps bi elhs × Hyps bi erhs × Q($e ⊣⊢ $elhs ∗ $erhs) :=
  let ⟨el, er, l, r, pf⟩ := hyps.partition fun x =>
    if x.persistent? then .both
    else if toRight x.name x.ivar then .right else .left
  ⟨el, er, l, r, pf⟩

end split

section remove

structure RemoveHyp {prop : Q(Type u)} (bi : Q(BI $prop)) (e : Q($prop)) where
  (e' : Q($prop)) (hyps' : Hyps bi e') (out out' : Q($prop)) (p : Q(Bool))
  (eq : $out =Q iprop(□?$p $out'))
  (pf : Q($e ⊣⊢ $e' ∗ $out))
  deriving Inhabited

def Hyps.removeG [Monad m] {prop : Q(Type u)} {bi : Q(BI $prop)} {e : Q($prop)}
    (rp : Bool) (hyps : Hyps bi e)
    (check : Name → IVarId → Q(Bool) → Q($prop) → m (Option α)) :
    m (Option (α × RemoveHyp bi e)) := do
  let hs := hyps.toArray
  -- reverse scan: same order as the old `rhs`-before-`lhs` recursion
  let some (i, a) ← scan hs hs.size | return none
  let x := hs[i]!
  let keep := !rp && x.persistent?
  let ⟨el, er, hypsL, _, pf⟩ := hyps.partition fun y =>
    if y.ivar == x.ivar then (if keep then .both else .right) else .left
  -- `er` is the fold of the singleton `#[x]`, i.e. `(x.e bi).1`, which is why
  -- the `=Q` witness below is justified.
  return some (a, ⟨el, hypsL, er, x.ty, x.p, ⟨⟩, pf⟩)
where
  scan (hs : Array (Hyp prop)) : Nat → m (Option (Nat × α))
    | 0 => return none
    | i + 1 => do
      let x := hs[i]!
      match ← check x.name x.ivar x.p x.ty with
      | some a => return some (i, a)
      | none   => scan hs i

def Hyps.remove {prop : Q(Type u)} {bi : Q(BI $prop)} {e}
    (rp : Bool) (hyps : Hyps bi e) (ivar : IVarId) : RemoveHyp bi e :=
  match Id.run (hyps.removeG rp fun _ ivar' _ _ => if ivar == ivar' then some () else none) with
  | some (_, r) => r
  | none => panic! "variable not found"

end remove

section replace

-- TODO: What to do with this? Is this necessary? Should this be a general abstraction?
def Replaces [BI PROP] (K A B : PROP) := (B -∗ K) ⊢ (A -∗ K)

theorem Replaces.apply [BI PROP] {P P' Q : PROP}
    (h : Replaces Q P P') (h_entails : P' ⊢ Q) : P ⊢ Q :=
  wand_entails <| (entails_wand h_entails).trans h

theorem replaces_right [BI PROP] {K P Q Q' : PROP} (h : Replaces K Q Q') :
    Replaces K iprop(P ∗ Q) iprop(P ∗ Q') :=
  wand_intro <| sep_assoc.2.trans <| wand_elim <|
  (wand_intro <| sep_assoc.1.trans wand_elim_left).trans h

theorem replaces_left [BI PROP] {K P P' Q : PROP} (h : Replaces K P P') :
    Replaces K iprop(P ∗ Q) iprop(P' ∗ Q) :=
  (wand_mono_left sep_comm.1).trans <| (replaces_right h).trans (wand_mono_left sep_comm.1)

theorem to_persistent_spatial [BI PROP] {P P' Q : PROP}
    [hP : IntoPersistently false P P'] [or : TCOr (Affine P) (Absorbing Q)] :
    Replaces Q P iprop(□ P') :=
  match or with
  | TCOr.l => wand_mono_left <| (affine_affinely P).2.trans (affinely_mono hP.1)
  | TCOr.r =>
    wand_intro <| (sep_mono_right <| hP.1.trans absorbingly_intuitionistically.2).trans <|
    absorbingly_sep_right.1.trans <| (absorbingly_mono wand_elim_left).trans absorbing

theorem to_persistent_intuitionistic [BI PROP] {P P' Q : PROP}
    [hP : IntoPersistently true P P'] : Replaces Q iprop(□ P) iprop(□ P') :=
  wand_mono_left <| affinely_mono hP.1

theorem from_affine [BI PROP] {p : Bool} {P P' Q : PROP} [hP : FromAffinely P' P p] :
    Replaces Q iprop(□?p P) P' :=
  wand_mono_left <| affinelyIf_of_intuitionisticallyIf.trans hP.1

theorem replace_hyp {PROP} [BI PROP] {p} {ty ty' e0 : PROP}
  (h : e0 ⊢ <pers> (ty -∗ ty')) :
  ∀ P, (□?p ty ∗ P) ∧ e0 ⊢ □?p ty' ∗ P := fun _ =>
  (and_mono_right h).trans <| persistent_and_affinely_sep_right_mp.trans <|
  sep_comm.1.trans <| sep_assoc.2.trans <| sep_mono_left <|
    match p with
    | false => (sep_mono_left intuitionistically_elim).trans <| wand_elim_left
    | true => intuitionistically_sep_mpr.trans <| intuitionistically_mono wand_elim_left

theorem replace_hyp_sep_left {PROP} [BI PROP] {elhs elhs' erhs e0 : PROP}
  (h : ∀ P, (elhs ∗ P) ∧ e0 ⊢ elhs' ∗ P) :
  ∀ P, ((elhs ∗ erhs) ∗ P) ∧ e0 ⊢ (elhs' ∗ erhs) ∗ P := fun P =>
  calc iprop(((elhs ∗ erhs) ∗ P) ∧ e0)
    _ ⊢ (elhs ∗ (erhs ∗ P)) ∧ e0 := and_mono_left sep_assoc.1
    _ ⊢ elhs' ∗ (erhs ∗ P) := h _
    _ ⊢ (elhs' ∗ erhs) ∗ P := sep_assoc.2

theorem replace_hyp_sep_right {PROP} [BI PROP] {elhs erhs' erhs e0 : PROP}
  (h : ∀ P, (erhs ∗ P) ∧ e0 ⊢ erhs' ∗ P) :
  ∀ P, ((elhs ∗ erhs) ∗ P) ∧ e0 ⊢ (elhs ∗ erhs') ∗ P := fun P =>
  calc iprop(((elhs ∗ erhs) ∗ P) ∧ e0)
    _ ⊢ (erhs ∗ (elhs ∗ P)) ∧ e0 := and_mono_left <| (sep_mono_left sep_comm.2).trans sep_assoc.1
    _ ⊢ erhs' ∗ (elhs ∗ P) := h _
    _ ⊢ (elhs ∗ erhs') ∗ P := sep_assoc.2.trans (sep_mono_left sep_comm.2)

theorem replace_finish {PROP} [BI PROP] {e e' : PROP}
  (h : ∀ P, (e ∗ P) ∧ e ⊢ e' ∗ P) :
  e ⊢ e' :=
    calc e
      _ ⊢ (e ∗ emp) ∧ e := and_intro sep_emp.2 .rfl
      _ ⊢ e' ∗ emp := h _
      _ ⊢ e' := sep_emp.1

/-- Extend a congruence proof about the fold of `hs[:k]` to the fold of `hs`. -/
private def replaceLift {prop : Q(Type u)} (bi : Q(BI $prop)) (e0 : Q($prop))
    (hs : Array (Hyp prop)) (k : Nat) (a a' : Q($prop))
    (pf : Q(∀ P, (($a ∗ P) ∧ $e0 ⊢ $a' ∗ P))) :
    (b b' : Q($prop)) × Q(∀ P, (($b ∗ P) ∧ $e0 ⊢ $b' ∗ P)) :=
  if hk : k < hs.size then
    let ⟨x, _⟩ := hs[k].e bi   -- destructuring keeps the `=Q` in scope for Qq
    have pf' : Q(∀ P, ((iprop($a ∗ $x) ∗ P) ∧ $e0 ⊢ iprop($a' ∗ $x) ∗ P)) :=
      q(replace_hyp_sep_left $pf)
    replaceLift bi e0 hs (k + 1) q(iprop($a ∗ $x)) q(iprop($a' ∗ $x)) pf'
  else ⟨a, a', pf⟩
termination_by hs.size - k
decreasing_by omega

variable [Monad m] [MonadLiftT MetaM m] {prop : Q(Type u)}
  {bi : Q(BI $prop)} {e : Q($prop)} (hyps : Hyps bi e) (ivar : IVarId)
  (repl : Name → Q(Bool) → (ty : Q($prop)) → m ((ty' : Q($prop)) × Q($e ⊢ <pers> ($ty -∗ $ty')))) in
def Hyps.replace : m (Option ((e' : Q($prop)) × Hyps bi e' × Q($e ⊢ $e'))) := do
  let hs := hyps.toArray
  -- forward scan, first match — same order as the old `lhs`-before-`rhs` recursion
  let some i := hs.findIdx? (·.ivar == ivar) | return none
  let x := hs[i]!
  let ⟨ty', pf0⟩ ← repl x.name x.p x.ty
  let x' : Hyp prop := { x with ty := ty' }
  let ⟨xe,  _⟩ := x.e bi
  let ⟨xe', _⟩ := x'.e bi
  -- focus on `hs[i]` …
  have pfHyp : Q(∀ P, (($xe ∗ P) ∧ $e ⊢ $xe' ∗ P)) := q(replace_hyp $pf0)
  -- … then step out of the innermost `∗` if there is a prefix, and lift through
  -- each trailing hypothesis.
  let ⟨_, b', pf⟩ :=
    if i = 0 then
      replaceLift bi e hs 1 xe xe' pfHyp
    else
      let pre := sepFoldE bi (hs.extract 0 i)   -- unchanged by the replacement
      have pfPre : Q(∀ P, ((iprop($pre ∗ $xe) ∗ P) ∧ $e ⊢ iprop($pre ∗ $xe') ∗ P)) :=
        q(replace_hyp_sep_right $pfHyp)
      replaceLift bi e hs (i + 1) q(iprop($pre ∗ $xe)) q(iprop($pre ∗ $xe')) pfPre
  -- `b` is the canonical fold of `hs`, i.e. `e`
  have pf : Q(∀ P, (($e ∗ P) ∧ $e ⊢ $b' ∗ P)) := pf
  have pfFin : Q($e ⊢ $b') := q(replace_finish $pf)
  return some ⟨b', Hyps.ofArray bi (hs.set! i x') b', pfFin⟩


end replace


section dependency

partial def Hyps.findDependencyOnFVar {prop : Q(Type u)} {bi : Q(BI $prop)}
    (fvarId : FVarId) : ∀ {e}, Hyps bi e → Option (Name × IVarId × Q(Bool) × Q($prop)) :=
  fun h =>  h.toArray.findSome? fun x => if (x.ty : Expr).containsFVar fvarId then some (x.name, x.ivar, x.p, x.ty) else none

/-- Check that removing the Lean local `fvarId` leaves no dangling dependencies in the
proofmode context, an optional goal, or remaining Lean locals not accepted by `allowedDep`. -/
def Hyps.checkRemovableFVar {prop : Q(Type u)} {bi : Q(BI $prop)} {e}
    (hyps : Hyps bi e) (tac : String) (fvarId : FVarId)
    (goal? : Option Expr := none) (allowedDep : FVarId → Bool := fun _ => false) :
    MetaM LocalDecl := do
  let ldecl ← fvarId.getDecl
  if let some (name, _, _, _) := hyps.findDependencyOnFVar fvarId then
    throwError "{tac}: proofmode hypothesis {name} depends on {ldecl.userName}"
  if let some goal := goal? then
    let goal ← instantiateMVars goal
    if goal.containsFVar fvarId then
      throwError "{tac}: goal depends on {ldecl.userName}"
  let deps ← collectForwardDeps #[mkFVar fvarId] false
  if let some dep := deps.find? (fun e => e.fvarId! != fvarId && !allowedDep e.fvarId!) then
    let depDecl := (← getLCtx).getFVar! dep
    throwError "{tac}: Lean hypothesis {depDecl.userName} depends on {ldecl.userName}"
  return ldecl

end dependency

end hyps

/-- This is the same as `Entails`, but it takes a `BI` instead.
This constant is used to detect iris proof goals. -/
@[expose]
def Entails' [BI PROP] : PROP → PROP → Prop := Entails

structure IrisGoal where
  u : Level
  prop : Q(Type u)
  bi : Q(BI $prop)
  e : Q($prop)
  hyps : Hyps bi e
  goal : Q($prop)

def isIrisGoal (expr : Expr) : Bool := isAppOfArity expr ``Entails' 4

def parseIrisGoal? (expr : Expr) : Option IrisGoal := do
  -- remove top-level metadata when matching on the goal
  let expr := expr.consumeMData
  let some #[prop, bi, P, goal] := expr.appM? ``Entails' | none
  let u := expr.getAppFn.constLevels![0]!
  let ⟨e, hyps⟩ ← parseHyps? bi P
  some { u, prop, bi, e, hyps, goal }

/--
  Parse an Iris entailment (`Entails` rather than `Entails'`).
-/
def parseEntails? (expr : Expr) : Option <| Expr × Expr × Expr × Expr :=
  match expr.consumeMData.appM? ``Entails with
  | some #[prop, bi, e, goal] => some ⟨prop, bi, e, goal⟩
  | _ => none

def IrisGoal.toExpr : IrisGoal → Expr
  | { hyps, goal, .. } => q(Entails' $(hyps.tm) $goal)

def IrisGoal.strip : IrisGoal → Expr
  | { e, goal, .. } =>
    if e.consumeMData.isAppOfArity ``emp 2 then
      q(BIBase.EmpValid $goal)
    else
      q(Entails $e $goal)

/-- This is only used for display purposes, so that we can render context variables that appear
to have type `A : PROP` even though `PROP` is not a type. -/
def HypMarker {PROP : Type _} (_A : PROP) : Prop := True

/-- addLocalVarInfo associates the syntax `stx` (usually representing a hypothesis) with its type.
This allows one to hover over the syntax and see the type. isBinder marks the place where the
 hypothesis is introduced, e.g. for jump to definition. -/
def addLocalVarInfo (stx : Syntax) (lctx : LocalContext)
    (expr : Expr) (expectedType? : Option Expr) (isBinder := false) : MetaM Unit := do
  Elab.withInfoContext' (pure ())
    (fun _ =>
      return .inl <| .ofTermInfo
        { elaborator := .anonymous, lctx, expr, stx, expectedType?, isBinder })
    (return .ofPartialTermInfo { elaborator := .anonymous, lctx, stx, expectedType? })

def addHypInfo (stx : Syntax) (name : Name) (ivar : IVarId) (prop : Q(Type u)) (ty : Q($prop))
    (isBinder := false) : MetaM Unit := do
  let lctx ← getLCtx
  let ty := q(HypMarker $ty)
  addLocalVarInfo stx (lctx.mkLocalDecl ⟨ivar.name⟩ name ty) (.fvar ⟨ivar.name⟩) ty isBinder

/-- Hyps.findWithInfo should be used on names obtained from the syntax of a tactic to
highlight them correctly. -/
def Hyps.findWithInfo {u prop bi} (hyps : @Hyps u prop bi s) (name : Ident) : MetaM IVarId := do
  let some (ivar, ty) := hyps.find? name.getId | throwError "unknown hypothesis {name}"
  addHypInfo name name.getId ivar prop ty
  pure (ivar)

/-- Hyps.addWithInfo should be used by tactics that introduce a hypothesis based on the name
given by the user. -/
def Hyps.addWithInfo {prop : Q(Type u)} (bi : Q(BI $prop))
    (name : TSyntax ``binderIdent) (p : Q(Bool)) (ty : Q($prop)) {e} (h : Hyps bi e)
    : MetaM (IVarId × (e' : Q($prop)) × Hyps bi e' × Q(iprop($e ∗ □?$p $ty ⊣⊢ $e'))) := do
  let ivar' ← mkFreshIVarId (isTrue p)
  let (nameTo, nameRef) ← getFreshName name
  addHypInfo nameRef nameTo ivar' prop ty (isBinder := true)
  let ⟨e', hyps, pf⟩ := Hyps.add bi nameTo ivar' p ty h
  return ⟨ivar', e', hyps, pf⟩

private def Hyps.introGo {prop : Q(Type u)} (bi : Q(BI $prop))
    (hs : Array (Hyp prop)) : (k : Nat) → Option ((a : Q($prop)) × Q($a ⊢ □ $a))
  | 0 =>
    have pf : Q(iprop(emp : $prop) ⊢ □ (emp : $prop)) := q(intuitionistically_emp.mpr)
    some ⟨q(emp), pf⟩
  | j + 1 => do
    let x := hs[j]!
    guard x.persistent?
    let ty := x.ty
    have pfX : Q(iprop(□ $ty) ⊢ □ iprop(□ $ty)) := q(intuitionistically_idem.mpr)
    if j = 0 then
      some ⟨q(iprop(□ $ty)), pfX⟩
    else
      let ⟨a, pfA⟩ ← Hyps.introGo bi hs j
      have pf : Q(iprop($a ∗ □ $ty) ⊢ □ iprop($a ∗ □ $ty)) :=
        q((sep_mono $pfA $pfX).trans intuitionistically_sep_mpr)
      some ⟨q(iprop($a ∗ □ $ty)), pf⟩

/--
  Given hypothesis `hyps` representing `e` where every hypothesis exist in the
  intuitionistic context, return the proof of `e ⊢ □ e`. Return `none` if
  `hyps` contains hypotheses in the spatial context.
-/
def Hyps.buildIntuitionisticProof {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {e}
    (hyps : Hyps bi e) : Option Q($e ⊢ □ $e) := do
  let hs := hyps.toArray
  -- O(n) pre-check, so we never build a proof only to discard it
  guard <| hs.all (·.persistent?)
  let ⟨_, pf⟩ ← Hyps.introGo bi hs hs.size
  have pfE : Q($e ⊢ □ $e) := pf
  some pfE
