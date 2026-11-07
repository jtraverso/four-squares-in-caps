/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import FourSquaresCaps.FinalH2
public import FourSquaresCaps.JacobiCount

/-!
# H2: four squares in arbitrary caps (unconditional)

`fourSquaresDense_of_reps` (delta method, Route J) reduces `FourSquaresDense` to a linear lower
bound for `r₄(m)`, `m` odd, which Jacobi's theorem (`Jacobi.reps_card_ge`, `r₄(m) = 8σ(m)`)
provides.
-/

@[expose] public section

namespace FourSquaresCaps

theorem fourSquaresDense : FourSquaresDense :=
  fourSquaresDense_of_reps ⟨8, by norm_num, 1, fun m _ hm => by
    have := Jacobi.reps_card_ge m hm
    exact_mod_cast this⟩

end FourSquaresCaps
