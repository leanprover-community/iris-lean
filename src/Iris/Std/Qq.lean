/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Qq

@[expose] public section
open Qq

instance : Inhabited (QuotedDefEq a b) := ⟨⟨⟩⟩
