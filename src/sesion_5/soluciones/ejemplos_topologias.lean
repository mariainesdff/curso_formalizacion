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

/-- La topología discreta es aquella en la que todo subconjunto de `X` (es decir, todo término de
  tipo `set X`) es abierto. -/
def discreta : topological_space X :=
{ is_open        := λ _ , true ,
  is_open_univ   := trivial,
  is_open_inter  := λ _ _ _ _, trivial,
  is_open_sUnion := λ _ _, trivial }

/-- La topología indiscreta o trivial es aquella en la que los únicos abiertos son `X` y `∅`. -/
def indiscreta : topological_space X :=
{ is_open        := λ S, S = set.univ ∨ S = ∅,
  is_open_univ   := or.inl rfl,
  is_open_inter  := begin
    rintros S T hS hT, 
    cases hS with hSu hSe,
    { cases hT with hTu hTe,
      { left,
        rw [hSu, hTu, univ_inter] },
      { right,
        rw [hSu, hTe, inter_empty ], }},
    { right,
      rw [hSe, empty_inter] }
  end,
  is_open_sUnion := λ F hF,
  begin
    by_cases h : univ ∈ F,
    { left,
      rw sUnion_eq_univ_iff,
      intros x,
      exact ⟨univ, h, mem_univ _⟩ },
    { right,
      rw sUnion_eq_empty,
      intros S hSF,
      cases hF S hSF with hSu hSe,
      { rw hSu at hSF,
        exact absurd hSF h },
      { exact hSe }}
  end }

/-- La función `id : (X, discreta) ----->  (X, indiscreta)` es continuais continuous . -/
example : @continuous X X (discreta X) (indiscreta X) id :=
{ is_open_preimage := λ _ _, trivial }

/-- Sin embargo, `id : (X, indiscreta) ------> (X, discreta)` no lo es. -/
example (x y : X) (h : x ≠ y) : ¬ @continuous X X (indiscreta X) (discreta X) id :=
begin
  rw [continuous_def, not_forall],
  use ({x} : set X) ,
  rw [not_imp, preimage_id_eq, id.def],
  refine ⟨trivial, _⟩,
  change ¬ ({x} = univ ∨ {x} = ∅),
  rw push_neg.not_or_eq,
  refine ⟨_, singleton_ne_empty _⟩,
  { rw [eq_univ_iff_forall, not_forall],
    use y,
    exact h.symm, },
end

end topological_space
