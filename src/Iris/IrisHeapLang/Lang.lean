
namespace HeapLang

abbrev loc := Int
abbrev ProphId := {x : Int // x ≥ 0} -- Why does Rocq Iris do this?

inductive BaseLit where
  | Int (n : Int)
  | Bool (b : Bool)
  | Unit
  | LitPoison
  | Loc (l : loc)
  | Prophecy (p : ProphId)


-- Why are there two different ways to negate?
inductive UnOp where
  | Neg
  | Minus

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


inductive Binder
  | BAnon
  | BNamed (name : Lean.Ident)

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
  | Xchg (e₀ e₁ : Expr) -- exchange
  | FAA (e₁ e₂ : Expr) --  Fetch-and-add
  -- Concurrency
  | Fork (e : Expr)
  -- Prophecy
  | NewProph
  | Resolve (e₀ e₁ e₂ : Expr) -- wrapped expr, proph, val
end

def toVal (e : Expr) : Option Val :=
  match e with
  | .Val v => some v
  | _ => none

def BaseLit.isUnboxed (l : BaseLit) :=
  match l with
  | .Prophecy _ => False
  | .LitPoison => False
  | _ => True
end HeapLang


/-
val :=
  | LitV (l : base_lit)
  | RecV (f x : binder) (e : expr)
  | PairV (v1 v2 : val)
  | InjLV (v : val)
  | InjRV (v : val).
Inductive base_lit : Set :=
  | LitInt (n : Z) | LitBool (b : bool) | LitUnit | LitPoison
  | LitLoc (l : loc) | LitProphecy (p: proph_id).
Inductive un_op : Set :=
  | NegOp | MinusUnOp.
Inductive bin_op : Set :=
  (** We use "quot" and "rem" instead of "div" and "mod" to
      better match the behavior of 'real' languages:
      e.g., in Rust, -30 -4 == 7. ("div" would return 8.) *)
  | PlusOp | MinusOp | MultOp | QuotOp | RemOp (* Arithmetic *)
  | AndOp | OrOp | XorOp (* Bitwise *)
  | ShiftLOp | ShiftROp (* Shifts *)
  | LeOp | LtOp | EqOp (* Relations *)
  | OffsetOp. (* Pointer offset *)

Inductive expr :=
  (* Values *)
  | Val (v : val)
  (* Base lambda calculus *)
  | Var (x : string)
  | Rec (f x : binder) (e : expr)
  | App (e1 e2 : expr)
  (* Base types and their operations *)
  | UnOp (op : un_op) (e : expr)
  | BinOp (op : bin_op) (e1 e2 : expr)
  | If (e0 e1 e2 : expr)
  (* Products *)
  | Pair (e1 e2 : expr)
  | Fst (e : expr)
  | Snd (e : expr)
  (* Sums *)
  | InjL (e : expr)
  | InjR (e : expr)
  | Case (e0 : expr) (e1 : expr) (e2 : expr)
  (* Heap *)
  | AllocN (e1 e2 : expr) (* array length (positive number), initial value *)
  | Free (e : expr)
  | Load (e : expr)
  | Store (e1 : expr) (e2 : expr)
  | CmpXchg (e0 : expr) (e1 : expr) (e2 : expr) (* Compare-exchange *)
  | Xchg (e0 : expr) (e1 : expr) (* exchange *)
  | FAA (e1 : expr) (e2 : expr) (* Fetch-and-add *)
  (* Concurrency *)
  | Fork (e : expr)
  (* Prophecy *)
  | NewProph
  | Resolve (e0 : expr) (e1 : expr) (e2 : expr) (* wrapped expr, proph, val *)
with val :=
  | LitV (l : base_lit)
  | RecV (f x : binder) (e : expr)
  | PairV (v1 v2 : val)
  | InjLV (v : val)
  | InjRV (v : val).

-/
