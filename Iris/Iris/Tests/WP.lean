/-
Copyright (c) 2026 Fernando Leal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.ProgramLogic.WeakestPre
public import Iris.HeapLang

@[expose] public section

namespace Iris.Tests
open Iris

/- This section checks whether the syntax is recognized correctly for all combinations -/
section TestWP
set_option linter.unusedVariables false

variable (PROP Expr : Type _) (Val : Type _) (A : Type _)
variable [Wp PROP Expr Val A]
variable [Wp PROP Expr Val Stuckness]
variable [TotalWp PROP Expr Val A]
variable [TotalWp PROP Expr Val Stuckness]

variable (e : Expr) (s : A) (E : CoPset)

-- Base no-binder cases
variable (Φ : Val → PROP)

/-- info: WP e @ s ; E {{ Φ }} : PROP -/
#guard_msgs in #check WP e @ s ; E {{ Φ }}
/-- info: WP e @ E {{ Φ }} : PROP -/
#guard_msgs in #check WP e @ E {{ Φ }}
/-- info: WP e @ E ? {{ Φ }} : PROP -/
#guard_msgs in #check WP e @ E ? {{ Φ }}
/-- info: WP e {{ Φ }} : PROP -/
#guard_msgs in #check WP e {{ Φ }}
/-- info: WP e ? {{ Φ }} : PROP -/
#guard_msgs in #check WP e ? {{ Φ }}

/-- info: WP e @ s ; E [{ Φ }] : PROP -/
#guard_msgs in #check WP e @ s ; E [{ Φ }]
/-- info: WP e @ E [{ Φ }] : PROP -/
#guard_msgs in #check WP e @ E [{ Φ }]
/-- info: WP e @ E ? [{ Φ }] : PROP -/
#guard_msgs in #check WP e @ E ? [{ Φ }]
/-- info: WP e [{ Φ }] : PROP -/
#guard_msgs in #check WP e [{ Φ }]
/-- info: WP e ? [{ Φ }] : PROP -/
#guard_msgs in #check WP e ? [{ Φ }]

/-- info: WP e @ s ; E {{ Φ }} : PROP -/
#guard_msgs in #check WP e @ s ; E ⦃ Φ ⦄
/-- info: WP e @ E {{ Φ }} : PROP -/
#guard_msgs in #check WP e @ E ⦃ Φ ⦄
/-- info: WP e @ E ? {{ Φ }} : PROP -/
#guard_msgs in #check WP e @ E ? ⦃ Φ ⦄
/-- info: WP e {{ Φ }} : PROP -/
#guard_msgs in #check WP e ⦃ Φ ⦄
/-- info: WP e ? {{ Φ }} : PROP -/
#guard_msgs in #check WP e ? ⦃ Φ ⦄

/-- info: WP e @ s ; E [{ Φ }] : PROP -/
#guard_msgs in #check WP e @ s ; E 〖 Φ 〗
/-- info: WP e @ E [{ Φ }] : PROP -/
#guard_msgs in #check WP e @ E 〖 Φ 〗
/-- info: WP e @ E ? [{ Φ }] : PROP -/
#guard_msgs in #check WP e @ E ? 〖 Φ 〗
/-- info: WP e [{ Φ }] : PROP -/
#guard_msgs in #check WP e 〖 Φ 〗
/-- info: WP e ? [{ Φ }] : PROP -/
#guard_msgs in #check WP e ? 〖 Φ 〗

-- Base binder cases
variable (Φ : PROP)

/-- info: WP e @ s ; E {{ v, Φ }} : PROP -/
#guard_msgs in #check WP e @ s ; E {{v,  Φ }}
/-- info: WP e @ E {{ v, Φ }} : PROP -/
#guard_msgs in #check WP e @ E {{ v,  Φ}}
/-- info: WP e @ E ? {{ v, Φ }} : PROP -/
#guard_msgs in #check WP e @ E ? {{ v,  Φ}}
/-- info: WP e {{ v, Φ }} : PROP -/
#guard_msgs in #check WP e {{v,  Φ }}
/-- info: WP e ? {{ v, Φ }} : PROP -/
#guard_msgs in #check WP e ? {{v,  Φ }}

/-- info: WP e @ s ; E [{ v, Φ }] : PROP -/
#guard_msgs in #check WP e @ s ; E [{v,  Φ }]
/-- info: WP e @ E [{ v, Φ }] : PROP -/
#guard_msgs in #check WP e @ E [{ v, Φ }]
/-- info: WP e @ E ? [{ v, Φ }] : PROP -/
#guard_msgs in #check WP e @ E ? [{ v, Φ }]
/-- info: WP e [{ v, Φ }] : PROP -/
#guard_msgs in #check WP e [{v,  Φ }]
/-- info: WP e ? [{ v, Φ }] : PROP -/
#guard_msgs in #check WP e ? [{v,  Φ }]

/-- info: WP e @ s ; E {{ v, Φ }} : PROP -/
#guard_msgs in #check WP e @ s ; E ⦃v, Φ⦄
/-- info: WP e @ E {{ v, Φ }} : PROP -/
#guard_msgs in #check WP e @ E ⦃v, Φ⦄
/-- info: WP e @ E ? {{ v, Φ }} : PROP -/
#guard_msgs in #check WP e @ E ? ⦃v, Φ⦄
/-- info: WP e {{ v, Φ }} : PROP -/
#guard_msgs in #check WP e ⦃v, Φ⦄
/-- info: WP e ? {{ v, Φ }} : PROP -/
#guard_msgs in #check WP e ? ⦃v, Φ⦄

/-- info: WP e @ s ; E [{ v, Φ }] : PROP -/
#guard_msgs in #check WP e @ s ; E 〖v, Φ〗
/-- info: WP e @ E [{ v, Φ }] : PROP -/
#guard_msgs in #check WP e @ E 〖v, Φ〗
/-- info: WP e @ E ? [{ v, Φ }] : PROP -/
#guard_msgs in #check WP e @ E ? 〖v, Φ〗
/-- info: WP e [{ v, Φ }] : PROP -/
#guard_msgs in #check WP e 〖v, Φ〗
/-- info: WP e ? [{ v, Φ }] : PROP -/
#guard_msgs in #check WP e ? 〖v, Φ〗

-- BI binder cases
variable [BI PROP]

/-- info: WP e ? {{ v, Φ ∗ Φ }} : PROP -/
#guard_msgs in #check WP e ? {{v, Φ ∗ Φ}}
/-- info: WP e ? {{ v, Φ ∧ Φ }} : PROP -/
#guard_msgs in #check WP e ? {{v, Φ ∧ Φ}}
/-- info: WP e ? {{ v, Φ ∨ Φ }} : PROP -/
#guard_msgs in #check WP e ? {{v, Φ ∨ Φ}}
/-- info: WP e ? {{ v, Φ -∗ Φ }} : PROP -/
#guard_msgs in #check WP e ? {{v, Φ -∗ Φ}}

/-- info: WP e ? [{ v, Φ ∗ Φ }] : PROP -/
#guard_msgs in #check WP e ? [{v, Φ ∗ Φ}]
/-- info: WP e ? [{ v, Φ -∗ Φ }] : PROP -/
#guard_msgs in #check WP e ? [{v, Φ -∗ Φ}]

/-- info: WP e ? {{ v, Φ ∗ Φ }} : PROP -/
#guard_msgs in #check WP e ? ⦃v, Φ ∗ Φ⦄
/-- info: WP e ? [{ v, Φ ∗ Φ }] : PROP -/
#guard_msgs in #check WP e ? 〖v, Φ ∗ Φ〗

/-- info: WP e @ E {{ v, Φ ∗ Φ }} : PROP -/
#guard_msgs in #check WP e @ E {{v, Φ ∗ Φ}}
/-- info: WP e {{ v, Φ -∗ Φ }} : PROP -/
#guard_msgs in #check WP e {{v, Φ -∗ Φ}}

-- BI no-binder cases
variable (Φ : Val → PROP)

/-- info: WP e ? {{ v, Φ v ∗ Φ v }} : PROP -/
#guard_msgs in #check WP e ? {{v, Φ v ∗ Φ v}}
/-- info: WP e ? {{ v, Φ v ∧ Φ v }} : PROP -/
#guard_msgs in #check WP e ? {{v, Φ v ∧ Φ v}}
/-- info: WP e ? {{ v, Φ v ∨ Φ v }} : PROP -/
#guard_msgs in #check WP e ? {{v, Φ v ∨ Φ v}}
/-- info: WP e ? {{ v, Φ v -∗ Φ v }} : PROP -/
#guard_msgs in #check WP e ? {{v, Φ v -∗ Φ v}}
/-- info: WP e ? [{ v, Φ v ∗ Φ v }] : PROP -/
#guard_msgs in #check WP e ? [{v, Φ v ∗ Φ v}]
/-- info: WP e ? [{ v, Φ v -∗ Φ v }] : PROP -/
#guard_msgs in #check WP e ? [{v, Φ v -∗ Φ v}]
/-- info: WP e ? {{ v, Φ v ∗ Φ v }} : PROP -/
#guard_msgs in #check WP e ? ⦃v, Φ v ∗ Φ v⦄
/-- info: WP e ? [{ v, Φ v ∗ Φ v }] : PROP -/
#guard_msgs in #check WP e ? 〖v, Φ v ∗ Φ v〗
/-- info: WP e @ E {{ v, Φ v ∗ Φ v }} : PROP -/
#guard_msgs in #check WP e @ E {{v, Φ v ∗ Φ v}}
/-- info: WP e {{ v, Φ v -∗ Φ v }} : PROP -/
#guard_msgs in #check WP e {{v, Φ v -∗ Φ v}}

end TestWP

section HeapLangTestWP
set_option linter.unusedVariables false

open Iris.HeapLang

variable (PROP : Type _) [BI PROP]
variable [Wp PROP Exp Val Stuckness]
variable (E : CoPset) (Φ : Val → PROP) (P : PROP)

/-- info: WP hl(#1) {{ Φ }} : PROP -/
#guard_msgs in #check WP hl(#1) {{ Φ }}
/-- info: WP hl((#1 + #2)) {{ Φ }} : PROP -/
#guard_msgs in #check WP hl(#1 + #2) {{ Φ }}
/-- info: WP hl((#1 < #2)) {{ Φ }} : PROP -/
#guard_msgs in #check WP hl(#1 < #2) {{ Φ }}
/-- info: WP hl(if (#0 < #1) then #1 else #2) {{ Φ }} : PROP -/
#guard_msgs in #check WP hl(if #0 < #1 then #1 else #2) {{ Φ }}
/-- info: WP hl((λ x, x)) {{ Φ }} : PROP -/
#guard_msgs in #check WP hl(λ x, x) {{ Φ }}
/-- info: WP hl((rec f x := f x)) {{ Φ }} : PROP -/
#guard_msgs in #check WP hl(rec f x := f x) {{ Φ }}
/-- info: WP hl(#1; #2) {{ Φ }} : PROP -/
#guard_msgs in #check WP hl(#1; #2) {{ Φ }}
/-- info: WP hl((#1, #2)) {{ Φ }} : PROP -/
#guard_msgs in #check WP hl((#1, #2)) {{ Φ }}
/-- info: WP hl(ref(#0)) {{ Φ }} : PROP -/
#guard_msgs in #check WP hl(ref(#0)) {{ Φ }}
/-- info: WP hl(if (#1 < #2) then (#1 + #1) else #0) {{ Φ }} : PROP -/
#guard_msgs in #check WP hl(if #1 < #2 then #1 + #1 else #0) {{ Φ }}
/-- info: WP hl(#1) {{ v, ⌜v = hl_val(#1)⌝ }} : PROP -/
#guard_msgs in #check (WP hl(#1) {{ v, ⌜v = hl_val(#1)⌝ }} : PROP)

end HeapLangTestWP
