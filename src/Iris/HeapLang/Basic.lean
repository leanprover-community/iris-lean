/-
Copyright (c) 2025 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Std.Data.HashMap

/-! # The HeapLang language

We port over the definition of the `HeapLang` language in the Rocq's Iris development. -/

open Std

section Prelude

/-- Location type for the heap. Defined as a wrapper around `Int`. -/
@[reducible]
def Location := Int

/-- Type for prophecy identifiers. Defined as a wrapper around `Nat`. -/
@[reducible]
def ProphId := Nat

/-- Type for binders, which can be either anonymous or named with a string. -/
inductive Binder : Type where
  | BAnon : Binder
  | BNamed (s : String) : Binder
deriving DecidableEq, Inhabited

/-- Get list of strings from a binder. Returns empty list for anonymous binder,
    singleton list for named binder. -/
def binderList (b : Binder) : List String :=
  match b with
  | .BAnon => []
  | .BNamed s => [s]

/-- Add a binder to a list of strings. Used for collecting free variables. -/
def consBinder (b : Binder) (ss : List String) : List String :=
  match b with
  | .BAnon => ss
  | .BNamed s => s :: ss

/-- Add a list of binders to a list of strings. Used for collecting free variables. -/
def appBinder (bs : List Binder) (ss : List String) : List String :=
  match bs with
  | [] => ss
  | b :: bs => consBinder b (appBinder bs ss)

/-- Delete a binding from a map based on binder. -/
def binderDelete [BEq String] (b : Binder) (m : HashMap String A) : HashMap String A :=
  match b with
  | .BAnon => m
  | .BNamed s => m.erase s

/-- Insert a binding into a map based on binder. -/
def binderInsert [BEq String] (b : Binder) (x : A) (m : HashMap String A) : HashMap String A :=
  match b with
  | .BAnon => m
  | .BNamed s => m.insert s x

end Prelude

namespace HeapLang

inductive BaseLit : Type where
  | LitInt (n : Int) | LitBool (b : Bool) | LitUnit | LitPoison
  | LitLoc (l : Location) | LitProph (p: ProphId)
deriving DecidableEq, Inhabited

inductive UnOp : Type where
  | NegOp | MinusUnOp
deriving DecidableEq, Inhabited

inductive BinOp : Type where
  | PlusOp | MinusOp | MultOp | QuotOp | RemOp -- Arithmetic
  | AndOp | OrOp | XorOp -- Bitwise
  | ShiftLOp | ShiftROp -- Shifts
  | LeOp | LtOp | EqOp -- Relations
  | OffsetOp -- Pointer offset
deriving DecidableEq, Inhabited

mutual

/-- The type of values in `HeapLang`. Defined in mutual recursion with `Expr`. -/
inductive Val : Type where
  | Lit (l : BaseLit)
  | Rec (f x : Binder) (e : Expr)
  | Pair (v1 v2 : Val)
  | InjL (v : Val)
  | InjR (v : Val)
deriving DecidableEq, Inhabited

/-- The type of expressions in `HeapLang` -/
inductive Expr : Type where
  -- Values
  | Val (v : Val)
  -- Base lambda calculus
  | Var (x : String)
  | Rec (f x : Binder) (e : Expr)
  | App (e1 e2 : Expr)
  -- Base types and their operations
  | UnOp (op : UnOp) (e : Expr)
  | BinOp (op : BinOp) (e1 e2 : Expr)
  | If (e0 e1 e2 : Expr)
  -- Products
  | Pair (e1 e2 : Expr)
  | Fst (e : Expr)
  | Snd (e : Expr)
  -- Sums
  | InjL (e : Expr)
  | InjR (e : Expr)
  | Case (e0 : Expr) (e1 : Expr) (e2 : Expr)
  -- Heap
  | AllocN (e1 e2 : Expr) -- array length (positive number), initial value
  | Free (e : Expr)
  | Load (e : Expr)
  | Store (e1 : Expr) (e2 : Expr)
  | CmpXchg (e0 : Expr) (e1 : Expr) (e2 : Expr) -- Compare-exchange
  | Xchg (e0 : Expr) (e1 : Expr) -- exchange
  | FAA (e1 : Expr) (e2 : Expr) -- Fetch-and-add
  -- Concurrency
  | Fork (e : Expr)
  -- Prophecy
  | NewProph
  -- wrapped expr, proph, val
  | Resolve (e0 : Expr) (e1 : Expr) (e2 : Expr)
deriving DecidableEq, Inhabited

end

/-- An observation consists of a prophecy identifier and two values. -/
def Observation := (ProphId × Val × Val)

/-- Return the value of an expression if it is a value. -/
def toVal (e : Expr) : Option Val :=
  match e with
  | .Val v => some v
  | _ => none

/-- Convert a value to an expression. -/
@[reducible] def ofVal (v : Val) : Expr := .Val v

@[simp] theorem toVal_ofVal (v : Val) : toVal (ofVal v) = some v := by
  simp [toVal, ofVal]

@[simp] theorem ofVal_of_toVal (e : Expr) (v : Val) (h : toVal e = some v) : ofVal v = e := by
  cases e <;> simp [toVal] at h
  subst h; simp [ofVal]

-- /-- Injectivity of `ofVal` -/
-- instance : Function.Injective ofVal where
--   injective := by
--     intro a b h
--     cases a <;> cases b <;> try injection h <;> assumption

def BaseLit.isUnboxed (l : BaseLit) : Prop :=
  match l with
  | .LitProph _ | .LitPoison => False
  | .LitInt _ | .LitBool _  | .LitLoc _ | .LitUnit => True

def Val.isUnboxed (v : Val) : Prop :=
  match v with
  | .Lit l => BaseLit.isUnboxed l
  | .Pair v1 v2 => v1.isUnboxed ∧ v2.isUnboxed
  | .InjL v | .InjR v => v.isUnboxed
  | _ => False

-- instDecidablePredBaseLitIsUnboxed
instance : DecidablePred BaseLit.isUnboxed := fun l => match l with
  | .LitProph _ | .LitPoison => isFalse (by simp [BaseLit.isUnboxed])
  | .LitInt _ | .LitBool _  | .LitLoc _ | .LitUnit => isTrue (by simp [BaseLit.isUnboxed])

-- instDecidablePredValIsUnboxed
instance : DecidablePred Val.isUnboxed := fun v => match h : v with
  | .Lit l => instDecidablePredBaseLitIsUnboxed l
  | .Pair v1 v2 => @instDecidableAnd _ _
      (instDecidablePredValIsUnboxed v1) (instDecidablePredValIsUnboxed v2)
  | .InjL v | .InjR v => instDecidablePredValIsUnboxed v
  | .Rec f x e => isFalse (by simp [Val.isUnboxed])

/-- Two values are safe to compare if at least one of them is unboxed. -/
def Val.canCompare (vl v1 : Val) : Prop :=
  vl.isUnboxed ∨ v1.isUnboxed

instance : DecidableRel Val.canCompare := fun vl v1 => by simp [Val.canCompare]; infer_instance

/-- The state of the heap language, consisting of a heap mapping locations to optional values
    and a set of used prophecy identifiers. -/
structure State where
  heap : HashMap Location (Option Val)
  usedProphId : List ProphId
deriving Inhabited

/-- Update the heap component of a state -/
def State.updateHeap (f : HashMap Location (Option Val) → HashMap Location (Option Val))
    (σ : State) : State :=
  { σ with heap := f σ.heap }

/-- Update the used prophecy identifiers of a state -/
def State.updateUsedProphId (f : List ProphId → List ProphId) (σ : State) : State :=
  { σ with usedProphId := f σ.usedProphId }

/-- Create an array in the heap starting at location `l` with values `vs` -/
def heapArray (l : Location) (vs : List Val) : HashMap Location (Option Val) :=
  vs.foldl (fun acc v => acc.insert l (some v)) HashMap.empty

/-- Initialize a heap region with n copies of value v starting at location l -/
def State.initHeap (l : Location) (n : Int) (v : Val) (σ : State) : State :=
  σ.updateHeap (fun _ => heapArray l (List.replicate n.toNat v))

@[simp]
theorem heapArray_singleton {l : Location} {v : Val} :
    heapArray l [v] = HashMap.empty.insert l (some v) := rfl

@[simp]
theorem heapArray_cons {l : Location} {v : Val} {vs : List Val} :
    heapArray l (v :: vs) = (heapArray (l + 1) vs).insert l (some v) := by
  simp [heapArray]; sorry

@[simp]
theorem heapArray_lookup {l : Location} {vs : List Val} {ow : Option Val} {k : Location} :
    (heapArray l vs)[k]? = some ow ↔
      ∃ j w, 0 ≤ j ∧ k = l + j ∧ ow = some w ∧ vs[j.toNat]? = some w := by
  induction vs with
  | nil => simp [heapArray]
  | cons v vs ih =>
    simp_all [HashMap.getElem?_insert]
    sorry

-- TODO: need to define `HashMap.isDisjoint`
-- theorem heap_array_map_disjoint (hmap : HashMap Location (Option Val)) (l : Location)
--     (vs : List Val) (h : ∀ i, 0 ≤ i → i < vs.length → hmap[l + i]? = None) :
--     (heapArray l vs).isDisjoint hmap := by sorry

@[simp]
theorem State.initHeap_singleton {l : Location} {v : Val} {σ : State} :
    State.initHeap l 1 v σ = State.updateHeap (fun _ => heapArray l [v]) σ := rfl

/-- Evaluation contexts -/
inductive EvalCtx : Type where
  | AppLCtx (v2 : Val)
  | AppRCtx (e1 : Expr)
  | UnOpCtx (op : UnOp)
  | BinOpLCtx (op : BinOp) (v2 : Val)
  | BinOpRCtx (op : BinOp) (e1 : Expr)
  | IfCtx (e1 e2 : Expr)
  | PairLCtx (v2 : Val)
  | PairRCtx (e1 : Expr)
  | FstCtx
  | SndCtx
  | InjLCtx
  | InjRCtx
  | CaseCtx (e1 : Expr) (e2 : Expr)
  | AllocNLCtx (v2 : Val)
  | AllocNRCtx (e1 : Expr)
  | FreeCtx
  | LoadCtx
  | StoreLCtx (v2 : Val)
  | StoreRCtx (e1 : Expr)
  | XchgLCtx (v2 : Val)
  | XchgRCtx (e1 : Expr)
  | CmpXchgLCtx (v1 : Val) (v2 : Val)
  | CmpXchgMCtx (e0 : Expr) (v2 : Val)
  | CmpXchgRCtx (e0 : Expr) (e1 : Expr)
  | FaaLCtx (v2 : Val)
  | FaaRCtx (e1 : Expr)
  | ResolveLCtx (ctx : EvalCtx) (v1 : Val) (v2 : Val)
  | ResolveMCtx (e0 : Expr) (v2 : Val)
  | ResolveRCtx (e0 : Expr) (e1 : Expr)
deriving DecidableEq, Inhabited

/-- Fill an evaluation context with an expression -/
def EvalCtx.fill (e : Expr) (Ki : EvalCtx) : Expr :=
  match Ki with
  | .AppLCtx v2 => .App e (ofVal v2)
  | .AppRCtx e1 => .App e1 e
  | .UnOpCtx op => .UnOp op e
  | .BinOpLCtx op v2 => .BinOp op e (.Val v2)
  | .BinOpRCtx op e1 => .BinOp op e1 e
  | .IfCtx e1 e2 => .If e e1 e2
  | .PairLCtx v2 => .Pair e (.Val v2)
  | .PairRCtx e1 => .Pair e1 e
  | .FstCtx => .Fst e
  | .SndCtx => .Snd e
  | .InjLCtx => .InjL e
  | .InjRCtx => .InjR e
  | .CaseCtx e1 e2 => .Case e e1 e2
  | .AllocNLCtx v2 => .AllocN e (.Val v2)
  | .AllocNRCtx e1 => .AllocN e1 e
  | .FreeCtx => .Free e
  | .LoadCtx => .Load e
  | .StoreLCtx v2 => .Store e (.Val v2)
  | .StoreRCtx e1 => .Store e1 e
  | .XchgLCtx v2 => .Xchg e (.Val v2)
  | .XchgRCtx e1 => .Xchg e1 e
  | .CmpXchgLCtx v1 v2 => .CmpXchg e (.Val v1) (.Val v2)
  | .CmpXchgMCtx e0 v2 => .CmpXchg e0 e (.Val v2)
  | .CmpXchgRCtx e0 e1 => .CmpXchg e0 e1 e
  | .FaaLCtx v2 => .FAA e (.Val v2)
  | .FaaRCtx e1 => .FAA e1 e
  | .ResolveLCtx K v1 v2 => .Resolve (K.fill e) (.Val v1) (.Val v2)
  | .ResolveMCtx ex v2 => .Resolve ex e (.Val v2)
  | .ResolveRCtx ex e1 => .Resolve ex e1 e

/-- Substitution -/
def subst (x : String) (v : Val) (e : Expr) : Expr :=
  match e with
  | .Val _ => e
  | .Var y => if decide (x = y) then .Val v else .Var y
  | .Rec f y e =>
     .Rec f y $ if decide (.BNamed x ≠ f ∧ .BNamed x ≠ y) then subst x v e else e
  | .App e1 e2 => .App (subst x v e1) (subst x v e2)
  | .UnOp op e => .UnOp op (subst x v e)
  | .BinOp op e1 e2 => .BinOp op (subst x v e1) (subst x v e2)
  | .If e0 e1 e2 => .If (subst x v e0) (subst x v e1) (subst x v e2)
  | .Pair e1 e2 => .Pair (subst x v e1) (subst x v e2)
  | .Fst e => .Fst (subst x v e)
  | .Snd e => .Snd (subst x v e)
  | .InjL e => .InjL (subst x v e)
  | .InjR e => .InjR (subst x v e)
  | .Case e0 e1 e2 => .Case (subst x v e0) (subst x v e1) (subst x v e2)
  | .AllocN e1 e2 => .AllocN (subst x v e1) (subst x v e2)
  | .Free e => .Free (subst x v e)
  | .Load e => .Load (subst x v e)
  | .Xchg e1 e2 => .Xchg (subst x v e1) (subst x v e2)
  | .Store e1 e2 => .Store (subst x v e1) (subst x v e2)
  | .CmpXchg e0 e1 e2 => .CmpXchg (subst x v e0) (subst x v e1) (subst x v e2)
  | .FAA e1 e2 => .FAA (subst x v e1) (subst x v e2)
  | .Fork e => .Fork (subst x v e)
  | .NewProph => .NewProph
  | .Resolve ex e1 e2 => .Resolve (subst x v ex) (subst x v e1) (subst x v e2)

/-- Substitution for binders -/
def subst' (mx : Binder) (v : Val) : Expr → Expr :=
  match mx with
  | .BNamed x => subst x v
  | .BAnon => id

/-- The evaluation of unary operations -/
def UnOp.eval (v : Val) (op : UnOp) : Option Val :=
  match op, v with
  | .NegOp, .Lit (.LitBool b) => some (.Lit (.LitBool (¬ b)))
  | .NegOp, .Lit (.LitInt n) => some (.Lit (.LitInt (- n)))
  | .MinusUnOp, .Lit (.LitInt n) => some (.Lit (.LitInt (- n)))
  | _, _ => none

/-- The evaluation of binary operations on integers -/
def BinOp.evalInt (n1 n2 : Int) (op : BinOp) : Option Val :=
  match op with
  | .PlusOp => some (.Lit (.LitInt (n1 + n2)))
  | .MinusOp => some (.Lit (.LitInt (n1 - n2)))
  | .MultOp => some (.Lit (.LitInt (n1 * n2)))
  | .QuotOp => some (.Lit (.LitInt (n1 / n2)))
  | .RemOp => some (.Lit (.LitInt (n1 % n2)))
  | .AndOp => some (.Lit (.LitBool ((n1 == 0) && (n2 == 0))))
  | .OrOp => some (.Lit (.LitBool ((n1 == 0) || (n2 == 0))))
  | .XorOp => some (.Lit (.LitBool ((n1 == 0) ^^ (n2 == 0))))
  | .ShiftLOp => some (.Lit (.LitInt (0))) -- n1 <<< n2
  | .ShiftROp => some (.Lit (.LitInt (0))) -- n1 >>> n2
  | .LeOp => some (.Lit (.LitBool (decide (n1 ≤ n2))))
  | .LtOp => some (.Lit (.LitBool (decide (n1 < n2))))
  | .EqOp => some (.Lit (.LitBool (decide (n1 = n2))))
  | .OffsetOp => none

/-- The evaluation of binary operations on booleans -/
def BinOp.evalBool (b1 b2 : Bool) (op : BinOp) : Option Val :=
  match op with
  | .PlusOp | .MinusOp | .MultOp | .QuotOp | .RemOp => none
  | .AndOp => some (.Lit (.LitBool (b1 && b2)))
  | .OrOp => some (.Lit (.LitBool (b1 || b2)))
  | .XorOp => some (.Lit (.LitBool (b1 ^^ b2)))
  | .ShiftLOp | .ShiftROp => none
  | .LeOp | .LtOp => none
  | .EqOp => some (.Lit (.LitBool (decide (b1 = b2))))
  | .OffsetOp => none

/-- The evaluation of binary operations on locations -/
def BinOp.evalLoc (op : BinOp) (l1 : Location) (v2 : Val) : Option Val :=
  match op, v2 with
  | .OffsetOp, .Lit (.LitInt off) => some (.Lit (.LitLoc (l1 + off)))
  | .LeOp, .Lit (.LitLoc l2) => some (.Lit (.LitBool (decide (l1 ≤ l2))))
  | .LtOp, .Lit (.LitLoc l2) => some (.Lit (.LitBool (decide (l1 < l2))))
  | _, _ => none

/-- The evaluation of binary operations -/
def BinOp.eval (op : BinOp) (v1 v2 : Val) : Option Val :=
  if op = .EqOp then
    if Val.canCompare v1 v2 then
      some (.Lit (.LitBool (v1 = v2)))
    else
      none
  else
    match v1, v2 with
    | .Lit (.LitInt n1), .Lit (.LitInt n2) => BinOp.evalInt n1 n2 op
    | .Lit (.LitBool b1), .Lit (.LitBool b2) => BinOp.evalBool b1 b2 op
    | .Lit (.LitLoc l1), v2 => BinOp.evalLoc op l1 v2
    | _, _ => none

/-- Basic step relation for the heap language. This is a predicate on the current `Expr`, current `State`, and the list of `Observation`s, with the next `Expr`, next `State`, and list of next `Expr`. -/
inductive BaseStep : Expr → State → List Observation → Expr → State → List Expr → Prop where
  -- A recursive function steps to a value of itself
  | recS (f x : Binder) (e : Expr) (σ : State) :
      BaseStep (.Rec f x e) σ [] (.Val (.Rec f x e)) σ []
  -- A pair of values steps to a value pair
  | pairS (v1 v2 : Val) (σ : State) :
      BaseStep (.Pair (.Val v1) (.Val v2)) σ [] (.Val (.Pair v1 v2)) σ []
  -- A left injection steps to a value left injection
  | injLS (v : Val) (σ : State) :
      BaseStep (.InjL (.Val v)) σ [] (.Val (.InjL v)) σ []
  -- A right injection steps to a value right injection
  | injRS (v : Val) (σ : State) :
      BaseStep (.InjR (.Val v)) σ [] (.Val (.InjR v)) σ []
  -- A beta reduction steps to the substituted expression
  | betaS (f x : Binder) (e1 : Expr) (v2 : Val) (e' : Expr) (σ : State)
    (hSubst : e' = subst' x v2 (subst' f (.Rec f x e1) e1)) :
      BaseStep (.App (.Val (.Rec f x e1)) (.Val v2)) σ [] e' σ []
  -- A unary operation steps to the result of the operation
  | unOpS (op : UnOp) (v v' : Val) (σ : State)
    (hOp : op.eval v = some v') :
      BaseStep (.UnOp op (.Val v)) σ [] (.Val v') σ []
  -- A binary operation steps to the result of the operation
  | binOpS (op : BinOp) (v1 v2 v' : Val) (σ : State)
    (hOp : op.eval v1 v2 = some v') :
      BaseStep (.BinOp op (.Val v1) (.Val v2)) σ [] (.Val v') σ []
  -- An if-then-else steps to the `true` branch if the condition is true
  | ifTrueS (e1 e2 : Expr) (σ : State) :
      BaseStep (.If (.Val (.Lit (.LitBool true))) e1 e2) σ [] e1 σ []
  -- An if-then-else steps to the `false` branch if the condition is false
  | ifFalseS (e1 e2 : Expr) (σ : State) :
      BaseStep (.If (.Val (.Lit (.LitBool false))) e1 e2) σ [] e2 σ []
  -- A first projection steps to the value of the first component of a pair
  | fstS (v1 v2 : Val) (σ : State) :
      BaseStep (.Fst (.Val (.Pair v1 v2))) σ [] (.Val v1) σ []
  -- A second projection steps to the value of the second component of a pair
  | sndS (v1 v2 : Val) (σ : State) :
      BaseStep (.Snd (.Val (.Pair v1 v2))) σ [] (.Val v2) σ []
  -- A case statement steps to the result of the first branch if the value is a left injection
  | caseLS (v : Val) (e1 e2 : Expr) (σ : State) :
      BaseStep (.Case (.Val (.InjL v)) e1 e2) σ [] (.App e1 (.Val v)) σ []
  -- A case statement steps to the result of the second branch if the value is a right injection
  | caseRS (v : Val) (e1 e2 : Expr) (σ : State) :
      BaseStep (.Case (.Val (.InjR v)) e1 e2) σ [] (.App e2 (.Val v)) σ []
  -- An allocation of `n` memory locations steps to the updated state with the allocated memory,
  -- if the first `n` memory locations are empty
  | allocNS (n : Int) (v : Val) (σ : State) (l : Location)
    (hn : n > 0)
    (hHeap : ∀ i, i ≥ 0 → i < n → σ.heap[l + i]? = none) :
      BaseStep (.AllocN (.Val (.Lit (.LitInt n))) (.Val v)) σ
               []
               (.Val (.Lit (.LitLoc l))) (State.initHeap l n v σ)
               []
  -- A free steps to a unit value if the memory can be freed
  | freeS (l : Location) (v : Val) (σ : State)
    (hHeap : σ.heap[l]? = some (some v)) :
      BaseStep (.Free (.Val (.Lit (.LitLoc l)))) σ [] (.Val (.Lit (.LitUnit))) σ []
  -- A load steps to the value at the memory location if it is present
  | loadS (l : Location) (v : Val) (σ : State)
    (hHeap : σ.heap[l]? = some (some v)) :
      BaseStep (.Load (.Val (.Lit (.LitLoc l)))) σ [] (.Val v) σ []
  -- A store steps to a unit value if the memory can be stored to
  | storeS (l : Location) (v : Val) (w : Val) (σ : State)
    (hHeap : σ.heap[l]? = some (some v)) :
      BaseStep (.Store (.Val (.Lit (.LitLoc l))) (.Val w)) σ [] (.Val (.Lit (.LitUnit))) σ []
  -- An exchange steps to the value at the memory location, and the updated state,
  -- if the memory location is present and contains the first value
  | xchgS (l : Location) (v1 : Val) (v2 : Val) (σ : State)
    (hHeap : σ.heap[l]? = some (some v1)) :
      BaseStep (.Xchg (.Val (.Lit (.LitLoc l))) (.Val v2)) σ
               []
               (.Val v1) (State.updateHeap (HashMap.insert · l (some v2)) σ)
               []
  -- A compare-and-exchange steps to the value at the memory location, and the updated state,
  -- if the memory location is present and contains the first value
  -- and the comparison holds
  -- (note that this compares values in the same way as [EqOp])
  | cmpXchgS (l : Location) (v1 : Val) (v2 : Val) (vl : Val) (σ : State) (b : Bool)
    (hGet : σ.heap[l]? = some (some vl))
    (hVal : Val.canCompare vl v1)
    (hBool : b = decide (vl = v1)) :
    BaseStep (.CmpXchg (.Val (.Lit (.LitLoc l))) (.Val v1) (.Val v2)) σ
               []
               (.Val (.Pair vl (.Lit (.LitBool b))))
                (if b then State.updateHeap (HashMap.insert · l (some v2)) σ else σ)
               []
  -- A fetch-and-add steps to the value at the memory location, and the updated state,
  -- if the memory location is present and contains the first value
  | faaS (l : Location) (i1 : Int) (i2 : Int) (σ : State)
    (hHeap : σ.heap[l]? = some (some (.Lit (.LitInt i1)))) :
      BaseStep (.FAA (.Val (.Lit (.LitLoc l))) (.Val (.Lit (.LitInt i2)))) σ
               []
               (.Val (.Lit (.LitInt i1)))
               (State.updateHeap (HashMap.insert · l (some (.Lit (.LitInt (i1 + i2))))) σ)
               []
  -- A fork steps to the updated state with the forked expression
  | forkS (e : Expr) (σ : State) :
      BaseStep (.Fork e) σ [] (.Val (.Lit (.LitUnit))) σ [e]
  -- A new prophecy steps to the updated state with the new prophecy,
  -- if the prophecy is not already used
  | newProphS (σ : State) (p : ProphId)
    (hProph : p ∉ σ.usedProphId) :
      BaseStep (.NewProph) σ
                []
                (.Val (.Lit (.LitProph p)))
                (State.updateUsedProphId (fun ls => ls.cons p) σ)
                []
  -- A resolve steps to the updated state with the resolved value and the list of observations,
  -- if the expression steps to the value
  | resolveS (p : ProphId) (v : Val) (e : Expr) (σ : State) (w : Val) (σ' : State)
    (κs : List (ProphId × (Val × Val))) (ts : List Expr)
    (hStep : BaseStep e σ κs (.Val v) σ' ts) :
      BaseStep (.Resolve e (.Val (.Lit (.LitProph p))) (.Val w)) σ
               (κs ++ [(p, (v, w))])
               (.Val v) σ' ts

-- `Function.Injective` is defined in mathlib
-- /-- Filling evaluation context is injective -/
-- instance : Function.Injective (EvalCtx.fill) := by
--   intro x y h
--   sorry

variable {Ki Ki1 Ki2 : EvalCtx} {e e1 e2 e2' : Expr} {σ1 σ1' σ2 σ2' : State}
    {κ κ' : List Observation} {efs efs' : List Expr}

/-- Filling evaluation context preserves values -/
theorem EvalCtx.fill_val (h : Option.isSome (toVal (Ki.fill e))) : Option.isSome (toVal e) := by
  cases Ki <;> simp [EvalCtx.fill, toVal] at h

/-- If both expressions are not values and filling them with two evaluation contexts yields the same
  result, then the contexts are equal. --/
theorem EvalCtx.fill_inj_of_ne_val (h1 : toVal e1 = none) (h2 : toVal e2 = none)
    (h : Ki1.fill e1 = Ki2.fill e2) : Ki1 = Ki2 := by sorry
  -- How to not time out?
  -- cases Ki1 <;> cases Ki2 <;> simp [EvalCtx.fill, toVal] at h1 h2 h

/-- If filling an evaluation context `K` with expression `e` yields a value `v`,
    then `K` must be empty and `e` must be that value. --/
theorem EvalCtx.fill_val_some (K : List EvalCtx) (e : Expr) (v : Val)
    (h : toVal (List.foldl (fun acc k => EvalCtx.fill acc k) e K) = some v) :
      K = [] ∧ e = .Val v := by
  match K with
  | [] => simp [toVal] at h; split at h <;> simp_all
  | Ki :: K =>
    simp [toVal] at h; split at h <;> simp_all
    · sorry

/-- If an expression can step, then it is not a value -/
@[simp]
theorem BaseStep.step_ne_val (h : BaseStep e1 σ1 κ e2 σ2 efs) : toVal e1 = none := by
  cases h <;> simp [toVal]

@[simp]
theorem BaseStep.ctx_fill_val (h : BaseStep (Ki.fill e) σ1 κ e2 σ2 efs) : (toVal e).isSome := by
  cases Ki <;> simp [EvalCtx.fill, ofVal, toVal] at h ⊢ <;> cases h
  any_goals simp
  split <;> simp_all
  rename_i ctx v p v' ks hStep e' h
  sorry

/-- Given a location `l` and a positive number `n`, allocating `n` copies of value `v`
  succeeds. --/
@[simp]
theorem BaseStep.allocN_apply (v : Val) (n : Int) (σ : State) (l : Location)
    (hn : n > 0) (hFresh : ∀ i, i ≥ 0 → i < n → σ.heap[l + i]? = none) :
    BaseStep (.AllocN (.Val (.Lit (.LitInt n))) (.Val v)) σ []
              (.Val (.Lit (.LitLoc l))) (State.initHeap l n v σ) [] :=
  BaseStep.allocNS n v σ l hn hFresh

/-- Given a fresh prophecy identifier `p`, creating a new prophecy succeeds. --/
@[simp]
theorem BaseStep.newProph_apply (σ : State) (p : ProphId) (hp : p ∉ σ.usedProphId) :
    BaseStep .NewProph σ [] (.Val (.Lit (.LitProph p)))
            (State.updateUsedProphId (fun ls => ls.cons p) σ) [] :=
  BaseStep.newProphS σ p hp

/-- If an expression makes a base step to a value under some state,
    then any base step from that expression under any other state must also be to a value. --/
theorem BaseStep.toVal_isSome_of_toVal_isSome (h : BaseStep e1 σ1 κ e2 σ2 efs)
    (h' : BaseStep e1 σ1' κ' e2' σ2' efs') (hVal : Option.isSome (toVal e2)) :
      Option.isSome (toVal e2') := by
  cases h' <;> simp_all [toVal] <;> cases h <;> simp_all

end HeapLang
