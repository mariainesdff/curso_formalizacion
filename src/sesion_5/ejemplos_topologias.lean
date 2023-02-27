/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : María Inés de Frutos-Fernández
-/

import topology.basic

noncomputable theory

/-!
# Espacios topológicos en Lean

Para cualquier tipo `α : Type`,una topología en `α` está definida en la clase `topological_space`. 
El conjunto `univ` contiene todos los elementos de un tipo.

```
@[protect_proj] class topological_space (α : Type u) :=
(is_open        : set α → Prop) -- Qué conjuntos son abiertos en esta topología.
(is_open_univ   : is_open univ) -- univ es abierto.
(is_open_inter  : ∀s t, is_open s → is_open t → is_open (s ∩ t))
-- la intersección de dos abiertos es un conjunto abierto.
(is_open_sUnion : ∀s, (∀t∈s, is_open t) → is_open (⋃₀ s))
-- la unión arbitraria de abiertos es un abierto.
```
-/

universe u

namespace topological_space

open set

open_locale classical

variables (X : Type u)

-- Recordad el truco `{!}` para acceder al menú de sugerencias.

/-- La topología discreta es aquella en la que todo subconjunto de `X` (es decir, todo término de
  tipo `set X`) es abierto. -/
def discreta : topological_space X :=
sorry

/-- La topología indiscreta o trivial es aquella en la que los únicos abiertos son `X` y `∅`. -/
def indiscreta : topological_space X :=
sorry

/-- La función `id : (X, discreta) ----->  (X, indiscreta)` es continuais continuous . -/
example : @continuous X X (discreta X) (indiscreta X) id :=
sorry

/-- Sin embargo, `id : (X, indiscreta) ------> (X, discreta)` no lo es. -/
example (x y : X) (h : x ≠ y) : ¬ @continuous X X (indiscreta X) (discreta X) id :=
begin
  sorry
end

end topological_space
