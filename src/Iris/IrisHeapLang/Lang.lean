import Std

namespace HeapLang

abbrev Loc := Int

instance : Inhabited (Loc) := inferInstance
instance : BEq (Loc) := inferInstance
instance : DecidableEq (Loc) := inferInstance

abbrev ProphId := {x : Int // x ≥ 0} -- Why does Rocq Iris do this?

inductive BaseLit where
  | Int (n : Int)
  | Bool (b : Bool)
  | Unit
  | Poison
  | Loc (l : Loc)
  | Prophecy (p : ProphId)
deriving DecidableEq, Inhabited

-- Why are there two different ways to negate?
inductive UnOp where
  | Neg
  | Minus
deriving Inhabited, DecidableEq

inductive BinOp where
  | Plus
  | Minus
  | Mult
  | Quot
  | Rem
  | And
  | Or
  | Xor
  | ShiftL
  | ShiftR
  | Le
  | Lt
  | Eq
  | Offset
deriving Inhabited, DecidableEq

inductive Binder
  | BAnon
  | BNamed (name : String)
deriving DecidableEq

mutual
inductive Val where
  | Lit (l : BaseLit)
  | Rec (f x : Binder) (e : Expr)
  | Pair (v₁ v₂ : Val)
  | InjL (v : Val)
  | InjR (v : Val)

-- The comments are borrowed as is from Iris Rocq
inductive Expr where
  -- values
  | Val (v : Val)
  -- basic lambda calculus
  | Var (x : String)
  | Rec (f x : Binder) (e : Expr)
  | App (e₁ e₂ : Expr)
  -- Base types and their operations
  | Unop (op : UnOp) (e : Expr)
  | Binop (op : BinOp) (e₁ e₂ : Expr)
  | If (e₁ e₂ e₂ : Expr)
  -- Products
  | Pair (e₁ e₂ : Expr)
  | Fst (e : Expr)
  | Snd (e : Expr)
  -- Sums
  | InjL (e : Expr)
  | InjR (e : Expr)
  | Case (e₀ e₁ e₂ : Expr)
  -- Heap
  | AllocN (e₁ e₂ : Expr) -- array length (positive number), initial value
  | Free (e : Expr)
  | Load (e : Expr)
  | Store (e₁ e₂ : Expr)
  | CmpXchg (e₀ e₁ e₂ : Expr) -- Compare-exchange
  | Xchg (e₁ e₂ : Expr) -- exchange
  | FAA (e₁ e₂ : Expr) --  Fetch-and-add
  -- Concurrency
  | Fork (e : Expr)
  -- Prophecy
  | NewProph
  | Resolve (e₀ e₁ e₂ : Expr) -- wrapped expr, proph, val

end

instance : Inhabited Val where
  default := .Lit BaseLit.Unit

instance : Inhabited Expr where
  default := .Val default


mutual
def valEq (v₁ v₂ : Val) : Bool :=
  match v₁, v₂ with
  | .Lit x, .Lit y => decide (x = y)
  | .InjL x, .InjL y => valEq x y
  | .InjR x, .InjR y => valEq x y
  | .Pair x₁ x₂, .Pair y₁ y₂ => valEq x₁ y₁ && valEq x₂ y₂
  | .Rec f₁ x₁ e₁, .Rec f₂ x₂ e₂ => decide (f₁ = f₂) && decide (x₁ = x₂) && exprEq e₁ e₂
  | _, _ => false

def exprEq (e₁ e₂ : Expr) : Bool :=
  match e₁, e₂ with
  | .Val v₁, .Val v₂ => valEq v₁ v₂
  | .Var x₁, .Var x₂ => decide (x₁ = x₂)
  | .Rec f₁ x₁ e₁, .Rec f₂ x₂ e₂ =>
            decide (f₁ = f₂)
        &&  decide (x₁ = x₂)
        &&  exprEq e₁ e₂
  | .App e₁ f₁, .App e₂ f₂ => exprEq e₁ e₂ && exprEq f₁ f₂
  | .Unop op₁ e₁, .Unop op₂ e₂ => decide (op₁ = op₂) && exprEq e₁ e₂
  | .Binop op₁ e₁ f₁, .Binop op₂ e₂ f₂ =>
            decide (op₁ = op₂)
        &&  exprEq e₁ e₂
        &&  exprEq f₁ f₂
  | .If cond₁ left₁ right₁, .If cond₂ left₂ right₂ =>
            exprEq cond₁ cond₂
        &&  exprEq left₁ left₂
        &&  exprEq right₁ right₂
  | .Pair e₁ f₁, .Pair e₂ f₂ =>
        exprEq e₁ e₂ && exprEq f₁ f₂
  | .Fst e₁, .Fst e₂ => exprEq e₁ e₂
  | .Snd e₁, .Snd e₂ => exprEq e₁ e₂
  | .InjL e₁, .InjL e₂ => exprEq e₁ e₂
  | .InjR e₁, .InjR e₂ => exprEq e₁ e₂
  | .Case e₁ f₁ g₁, .Case e₂ f₂ g₂ => exprEq e₁ e₂ && exprEq f₁ f₂ && exprEq g₁ g₂
  | .AllocN n₁ v₁, .AllocN n₂ v₂ => exprEq n₁ n₂ && exprEq v₁ v₂
  | .Free e₁, .Free e₂ => exprEq e₁ e₂
  | .Load e₁, .Load e₂ => exprEq e₁ e₂
  | .Store e₁ f₁, .Store e₂ f₂ => exprEq e₁ e₂ && exprEq f₁ f₂
  | .CmpXchg e₁ f₁ g₁, .CmpXchg e₂ f₂ g₂ =>
            exprEq e₁ e₂
        &&  exprEq f₁ f₂
        &&  exprEq g₁ g₂
  | .Xchg e₁ f₁, .Xchg e₂ f₂ => exprEq e₁ e₂ && exprEq f₁ f₂
  | .FAA e₁ f₁, .FAA e₂ f₂ => exprEq e₁ e₂ && exprEq f₁ f₂
  | .Fork e₁, .Fork e₂ => exprEq e₁ e₂
  | .NewProph, .NewProph => True
  | .Resolve e₁ f₁ g₁, .Resolve e₂ f₂ g₂ =>
            exprEq e₁ e₂
        &&  exprEq f₁ f₂
        &&  exprEq g₁ g₂
  | _, _ => false
end

instance : BEq Val where
  beq := valEq

instance : BEq Expr where
  beq := exprEq

macro "big_decide_tactic" : tactic => do
  `(tactic|
    all_goals
    try {
      apply isFalse
      simp_all
    }
    try {
      apply isTrue
      simp_all
    }
  )
macro "decide_tactic" : tactic => do
  `(tactic|
      (
        · apply isTrue
          simp_all
        all_goals
          apply isFalse
          simp_all

      )
    )
mutual
noncomputable instance exprDecEq (e₁ e₂ : Expr) : Decidable (e₁ = e₂) := by
  cases e₁ <;> cases e₂
  big_decide_tactic
  case Val.Val x y =>
    by_cases x = y
    decide_tactic
  case Var.Var x y =>
    by_cases x = y
    decide_tactic
  case InjL.InjL x y =>
    by_cases x = y
    decide_tactic
  case InjR.InjR x y =>
    by_cases x = y
    decide_tactic
  case Pair.Pair x₁ x₂ y₁ y₂ =>
    by_cases h₁ : x₁ = y₁ <;> by_cases h₂ : x₂ = y₂
    decide_tactic
  case Rec.Rec f₁ x₁ e₁ f₂ x₂ e₂ =>
    by_cases h₁ : f₁ = f₂ <;> by_cases h₂ : x₁ = x₂ <;> by_cases h₃ : e₁ = e₂
    decide_tactic
  case App.App e₁ f₁ e₂ f₂ =>
    by_cases h₁ : e₁ = e₂ <;> by_cases h₂ : f₁ = f₂
    decide_tactic
  case Unop.Unop op₁ f₁ op₂ f₂ =>
    by_cases op₁ = op₂ <;> by_cases f₁ = f₂
    decide_tactic
  case Binop.Binop op₁ f₁ g₁ op₂ f₂ g₂ =>
    by_cases op₁ = op₂ <;> by_cases f₁ = f₂ <;> by_cases g₁ = g₂
    decide_tactic
  case If.If cond₁ l₁ r₁ cond₂ l₂ r₂ =>
    by_cases cond₁ = cond₂ <;> by_cases l₁ = l₂ <;> by_cases r₁ = r₂
    decide_tactic
  case Fst.Fst e₁ e₂ =>
    by_cases e₁ = e₂
    decide_tactic
  case Snd.Snd e₁ e₂ =>
    by_cases e₁ = e₂
    decide_tactic
  case Case.Case c₁ f₁ g₁ c₂ f₂ g₂ =>
    by_cases c₁ = c₂ <;> by_cases f₁ = f₂ <;> by_cases g₁ = g₂
    decide_tactic
  case AllocN.AllocN e₁ f₁ e₂ f₂ =>
    by_cases e₁ = e₂ <;> by_cases f₁ = f₂
    decide_tactic
  case Free.Free e₁ e₂ =>
    by_cases e₁ = e₂
    decide_tactic
  case Load.Load e₁ e₂ =>
    by_cases e₁ = e₂
    decide_tactic
  case Store.Store f₁ e₁ f₂ e₂  =>
    by_cases f₁ = f₂ <;> by_cases e₁ = e₂
    decide_tactic
  case CmpXchg.CmpXchg e₁ f₁ g₁ e₂ f₂ g₂ =>
    by_cases e₁ = e₂ <;> by_cases f₁ = f₂ <;> by_cases g₁ = g₂
    decide_tactic
  case Xchg.Xchg e₁ f₁ e₂ f₂ =>
    by_cases e₁ = e₂ <;> by_cases f₁ = f₂
    decide_tactic
  case FAA.FAA e₁ f₁ e₂ f₂ =>
    by_cases e₁ = e₂ <;> by_cases f₁ = f₂
    decide_tactic
  case Fork.Fork e₁ e₂ =>
    by_cases e₁ = e₂
    decide_tactic
  case Resolve e₁ f₁ g₁ e₂ f₂ g₂ =>
    by_cases e₁ = e₂ <;> by_cases f₁ = f₂ <;> by_cases g₁ = g₂
    decide_tactic

noncomputable instance valDecEq (v₁ v₂ : Val) : Decidable (v₁ = v₂) := by
  cases v₁ <;> cases v₂
  big_decide_tactic
  case Lit.Lit x y =>
        by_cases x = y
        decide_tactic
  case InjL.InjL x y =>
        by_cases x = y
        decide_tactic
  case InjR.InjR x y =>
        by_cases x = y
        decide_tactic
  case Pair.Pair x₁ x₂ y₁ y₂ =>
        by_cases x₁ = y₁ <;> by_cases x₂ = y₂
        decide_tactic
  case Rec.Rec f₁ x₁ e₁ f₂ x₂ e₂ =>
        by_cases f₁ = f₂ <;> by_cases x₁ = x₂ <;> by_cases e₁ = e₂
        decide_tactic

end




def toVal (e : Expr) : Option Val :=
  match e with
  | .Val v => some v
  | _ => none

-- Defined for completeness with the Rocq version
abbrev ofVal (v : Val) : Expr := .Val v

def BaseLit.isUnboxed (l : BaseLit) :=
  match l with
  | .Prophecy _ => False
  | .Poison => False
  | _ => True

def Val.isUnboxed (l : Val) :=
  match l with
  | .Lit l => l.isUnboxed
  | .InjL x => x.isUnboxed
  | .InjR x => x.isUnboxed
  | _ => False


theorem toOfVal : ∀ v, toVal (ofVal v) = some v := by
  intro v
  simp [toVal, ofVal]

theorem ofToVal : ∀ e : Expr, ∀ v : Val,
  toVal e = some v → ofVal v = e :=  by
  intro e v h
  revert v
  cases h : e <;> simp [Expr.Val, ofVal, toVal]


inductive ECtxItem where
  | AppL (v₂ : Val)
  | AppR (e₁ : Expr)
  | Unop (op : UnOp)
  | BinopL (op : BinOp) (v₂ : Val)
  | BinopR (op : BinOp) (e₁ : Expr)
  | If (e₁ e₂ : Expr)
  | PairL (v₂ : Val)
  | PairR (e₁ : Expr)
  | Fst
  | Snd
  | InjL
  | InjR
  | Case (e₁ e₂ : Expr)
  | AllocNL (v₂ : Val)
  | AllocNR (e₁ : Expr)
  | Free
  | Load
  | StoreL (v₂ : Val)
  | StoreR (e₁ : Expr)
  | XchgL (v₂ : Val)
  | XchgR (e₁ : Expr)
  | CmpXchgL (v₁ v₂ : Val)
  | CmpXchgM (e₀ : Expr) (v₂ : Val)
  | CmpXchgR (e₀ e₁ : Expr)
  | FaaL (v₂ : Val)
  | FaaR (e₁ : Expr)
  | ResolveL (ctx : ECtxItem) (v₁ v₂ : Val)
  | ResolveM (e₀ : Expr) (v₂ : Val)
  | ResolveR (e₀ e₁ : Expr)


def FillItem (Ki : ECtxItem) (e : Expr) : Expr :=
  match Ki with
  | .AppL v₂ => .App e (ofVal v₂)
  | .AppR e₁ => .App e₁ e
  | .Unop op => .Unop op e
  | .BinopL op v₂ => .Binop op e (.Val v₂)
  | .BinopR op e₁ => .Binop op e₁ e
  | .If e₁ e₂ => .If e e₁ e₂
  | .PairL v₂ => .Pair e (.Val v₂)
  | .PairR e₁ => .Pair e₁ e
  | .Fst => .Fst e
  | .Snd => .Snd e
  | .InjL => .InjL e
  | .InjR => .InjR e
  | .Case e₁ e₂ => .Case e e₁ e₂
  | .AllocNL v₂ => .AllocN e (.Val v₂)
  | .AllocNR e₁ => .AllocN e₁ e
  | .Free => .Free e
  | .Load => .Load e
  | .StoreL v₂ => .Store e (.Val v₂)
  | .StoreR e₁ => .Store e₁ e
  | .XchgL v₂ => .Xchg e (.Val v₂)
  | .XchgR e₁ => .Xchg e₁ e
  | .CmpXchgL v₁ v₂ => .CmpXchg e (.Val v₁) (.Val v₂)
  | .CmpXchgM e₀ v₂ => .CmpXchg e₀ e (.Val v₂)
  | .CmpXchgR e₀ e₁ => .CmpXchg e₀ e₁ e
  | .FaaL v₂ => .FAA e (.Val v₂)
  | .FaaR e₁ => .FAA e₁ e
  | .ResolveL K v₁ v₂ => .Resolve (FillItem K e) (.Val v₁) (.Val v₂)
  | .ResolveM ex v₂ => .Resolve ex e (.Val v₂)
  | .ResolveR ex e₁ => .Resolve ex e₁ e

-- Substitution
def subst (x : String) (v : Val) (e : Expr)  : Expr :=
  match e with
  | .Val _ => e
  | .Var y => if decide (x = y) then .Val v else .Var y
  | .Rec f y e =>
     .Rec f y $ if decide (.BNamed x ≠ f ∧ .BNamed x ≠ y) then subst x v e else e
  | .App e₁ e₂ => .App (subst x v e₁) (subst x v e₂)
  | .Unop op e => .Unop op (subst x v e)
  | .Binop op e₁ e₂ => .Binop op (subst x v e₁) (subst x v e₂)
  | .If e₀ e₁ e₂ => .If (subst x v e₀) (subst x v e₁) (subst x v e₂)
  | .Pair e₁ e₂ => .Pair (subst x v e₁) (subst x v e₂)
  | .Fst e => .Fst (subst x v e)
  | .Snd e => .Snd (subst x v e)
  | .InjL e => .InjL (subst x v e)
  | .InjR e => .InjR (subst x v e)
  | .Case e₀ e₁ e₂ => .Case (subst x v e₀) (subst x v e₁) (subst x v e₂)
  | .AllocN e₁ e₂ => .AllocN (subst x v e₁) (subst x v e₂)
  | .Free e => .Free (subst x v e)
  | .Load e => .Load (subst x v e)
  | .Xchg e₁ e₂ => .Xchg (subst x v e₁) (subst x v e₂)
  | .Store e₁ e₂ => .Store (subst x v e₁) (subst x v e₂)
  | .CmpXchg e₀ e₁ e₂ => .CmpXchg (subst x v e₀) (subst x v e₁) (subst x v e₂)
  | .FAA e₁ e₂ => .FAA (subst x v e₁) (subst x v e₂)
  | .Fork e => .Fork (subst x v e)
  | .NewProph => .NewProph
  | .Resolve ex e₁ e₂ => .Resolve (subst x v ex) (subst x v e₁) (subst x v e₂)

def subst' (mx : Binder) (v : Val) : Expr → Expr :=
  match mx with
  | .BNamed x => subst x v
  | .BAnon => id

def unOpEval (op : UnOp) (v : Val) : Option Val :=
  match op, v with
  | .Neg, .Lit (.Bool b) => some $ .Lit $ .Bool (not b)
  | .Neg, .Lit (.Int n) => some $ .Lit $ .Int (Int.not n)
  | .Minus, .Lit (.Int n) => some $ .Lit $ .Int (- n)
  | _, _ => none


def binOpEvalInt (op : BinOp) (n₁ n₂ : Int) : Option BaseLit :=
  match op with
  | .Plus => some $ .Int (n₁ + n₂)
  | .Minus => some $ .Int (n₁ - n₂)
  | .Mult => some $ .Int (n₁ * n₂)
  | .Quot => some $ .Int (n₁ /  n₂)
  | .Rem => some $ .Int (n₁ % n₂)
  | .And => sorry -- some $ .Int (n₁ &&& n₂) -- need the mathlib bitwise defs
  | .Or => sorry -- some $ .Int (n₁ ||| n₂)
  | .Xor => sorry -- some $ .Int (Int.xor n₁ n₂)
  | .ShiftL => sorry -- some $ .Int (n₁ <<< n₂)
  | .ShiftR => sorry -- some $ .Int (n₁ >>> n₂)
  | .Le => some $ .Bool (decide (n₁ ≤ n₂))
  | .Lt => some $ .Bool (decide (n₁ < n₂))
  | .Eq => some $ .Bool (decide (n₁ = n₂))
  | .Offset => none

def binOpEvalBool (op : BinOp) (b₁ b₂ : Bool) : Option BaseLit :=
  match op with
  | .Plus | .Minus | .Mult | .Quot | .Rem => none -- (* Arithmetic *)
  | .And => some <| .Bool <| b₁ && b₂
  | .Or => some <| .Bool <| b₁ || b₂
  | .Xor => some <| .Bool <| xor b₁ b₂
  | .ShiftL | .ShiftR => none -- (* Shifts *)
  | .Le | .Lt => none -- (* InEquality *)
  | .Eq => some <| .Bool <| decide (b₁ = b₂)
  | .Offset => none

def binOpEvalLoc (op : BinOp) (l₁ : Loc) (v₂ : BaseLit) : Option BaseLit :=
  match op, v₂ with
  | .Offset, .Int offset => some <| .Loc (l₁ + offset)
  | .Le, .Loc l₂ => some <| .Bool (decide (l₁ ≤ l₂))
  | .Lt, .Loc l₂ => some $ .Bool (decide (l₁ < l₂))
  | _, _ => none

def valsCompareSafe (vl v₁ : Val) : Prop :=
  Val.isUnboxed vl ∨ Val.isUnboxed v₁


-- Replace this with a proper decidable instance later.
open Classical in
noncomputable def binOpEval (op : BinOp) (v₁ v₂ : Val) : Option Val :=
  if decide (op = .Eq) then
    if decide (valsCompareSafe v₁ v₂) then
      some <| .Lit <| .Bool <| decide (v₁ = v₂)
    else
      none
  else
    match v₁, v₂ with
    | .Lit (.Int n₁), .Lit (.Int n₂) => do
          let val ← binOpEvalInt op n₁ n₂
          return .Lit <| val
    | .Lit (.Bool b₁), .Lit (.Bool b₂) => do
          let val ← binOpEvalBool op b₁ b₂
          return .Lit <| val
    | .Lit (.Loc l₁), .Lit v₂ => do
          let val ← binOpEvalLoc op l₁ v₂
          return .Lit <| val
    | _, _ => none


structure State where
  heap : Loc → Option Val
  usedProphId : ProphId → Prop

def stateUpdHeap
  (update: (Loc → Option Val) → (Loc → Option Val))
  (σ: State) : State where
    heap := update σ.heap
    usedProphId := σ.usedProphId

end HeapLang
