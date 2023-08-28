/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro
-/
import Iris.BI.Classes
import Iris.BI.DerivedLaws
import Iris.BI.Extensions
import Iris.BI.BI
import Iris.Std.Classes

namespace Iris.BI
open Iris.Std
open BI


-- Intuitionistic
instance emp_intuitionistic [BI PROP] : Intuitionistic iprop(emp : PROP) where
  intuitionistic := intuitionistically_emp.2

instance and_intuitionistic [BI PROP] (P Q : PROP) [Intuitionistic P] [Intuitionistic Q] :
    Intuitionistic iprop(P ∧ Q) where
  intuitionistic := (and_mono intuitionistic intuitionistic).trans intuitionistically_and.2

instance or_intuitionistic [BI PROP] (P Q : PROP) [Intuitionistic P] [Intuitionistic Q] :
    Intuitionistic iprop(P ∨ Q) where
  intuitionistic := (or_mono intuitionistic intuitionistic).trans intuitionistically_or.2

instance exists_intuitionistic [BI PROP] (Φ : α → PROP) [∀ x, Intuitionistic (Φ x)] :
    Intuitionistic iprop(∃ x, Φ x) where
  intuitionistic := (exists_mono fun _ => intuitionistic).trans intuitionistically_exists.2

instance sep_intuitionistic [BI PROP] (P Q : PROP) [Intuitionistic P] [Intuitionistic Q] :
    Intuitionistic iprop(P ∗ Q) where
  intuitionistic := (sep_mono intuitionistic intuitionistic).trans intuitionistically_sep_2

instance intuitionistically_intuitionistic [BI PROP] (P : PROP) : Intuitionistic iprop(□ P) where
  intuitionistic := intuitionistically_idem.2
