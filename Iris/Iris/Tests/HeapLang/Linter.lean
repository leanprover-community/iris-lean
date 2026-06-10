/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.HeapLang

@[expose] public section
namespace Iris.Tests.HeapLang.Linter

open Iris.HeapLang

set_option linter.heapLang.freeVars true

#guard_msgs(drop info, check warning) in
#check hl(λ x, x + #1)

#guard_msgs(drop info, check warning) in
#check hl(rec f x := f x)

#guard_msgs(drop info, check warning) in
#check hl(let z := #1; z + z)

#guard_msgs(drop info, check warning) in
#check hl(λ x y, let z := #1; #2; x + y + z)

#guard_msgs(drop info, check warning) in
#check hl(match injl(#1) with | injl(a) => a | injr(b) => b)

section
variable (e : Exp)
#guard_msgs(drop info, check warning) in
#check hl(&e + #1)
end

-- Escaped binder taints the scope (partial analysis)
section
variable (b : Binder)
#guard_msgs(drop info, check warning) in
#check hl(λ &b, y)
end

/--
warning: unbound HeapLang variable `foo`.

• If you meant a meta-level (Lean) definition, escape it: `&foo`.
• Otherwise `foo` is a free variable, and likely a typo.
You can suppress this warning with `set_option linter.heapLang.freeVars false`

Note: This linter can be disabled with `set_option linter.heapLang.freeVars false`
-/
#guard_msgs(drop info, check warning) in
#check hl(foo #1)

/--
warning: unbound HeapLang variable `y`.

• If you meant a meta-level (Lean) definition, escape it: `&y`.
• Otherwise `y` is a free variable, and likely a typo.
You can suppress this warning with `set_option linter.heapLang.freeVars false`

Note: This linter can be disabled with `set_option linter.heapLang.freeVars false`
-/
#guard_msgs(drop info, check warning) in
#check hl(λ x, x + y)

/--
warning: unbound HeapLang variable `x`.

• If you meant a meta-level (Lean) definition, escape it: `&x`.
• Otherwise `x` is a free variable, and likely a typo.
You can suppress this warning with `set_option linter.heapLang.freeVars false`

Note: This linter can be disabled with `set_option linter.heapLang.freeVars false`
-/
#guard_msgs(drop info, check warning) in
#check hl((let x := #1; x) + x)

-- Opt-out
set_option linter.heapLang.freeVars false in
#guard_msgs(drop info, check warning) in
#check hl(bar #1)

-- Keyword without parens
/--
warning: unbound HeapLang variable `ref`.

• If you meant a meta-level (Lean) definition, escape it: `&ref`.
• Otherwise `ref` is a free variable, and likely a typo.
You can suppress this warning with `set_option linter.heapLang.freeVars false`

Note: This linter can be disabled with `set_option linter.heapLang.freeVars false`
-/
#guard_msgs(drop info, check warning) in
#check hl(λ _, ref #true)

-- Partiality: nested exprs not inspected
#guard_msgs(drop info, check warning) in
#check hl(let c := ref(#0); &(hl(c ← #1)))

end Iris.Tests.HeapLang.Linter
