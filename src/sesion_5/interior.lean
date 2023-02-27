/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : María Inés de Frutos-Fernández
-/

import topology.basic

/-!

# API para el `interior` de un conjunto.

Fijamos un espacio topológico `X` y un subconjunto `S : set X`. 

En Lean, `interior S` denota el interior de `S`, es decir, el mayor 
subconjunto abierto de `S`. Sin embargo, para practicar parte
de lo introducido en el fichero `conjuntos_2.lean`, en este 
fichero definiremos de nuevo esta noción (que denotaremos
`interior' S`) y crearemos su API básica.

-/

--Fijamos un espacio topológico `X` y un subconjunto `S : set X`. 
variables {X : Type} [topological_space X] (S : set X)

/-

## API para espacios topológicos

`is_open S : Prop` es el predicado que dice que `S : set X` es abierto.

Los siguientes lemas de `mathlib` serán útiles en estos ejercicios:
* is_open_univ
* is_open_Union, is_open_bUnion
* is_open.inter

Los nombres son descriptivos, pero si queréis aseguraros de que un
lema dice lo que creéis, podéis utilizar #check o buscarlo en la
documentación de mathlib (https://leanprover-community.github.io/mathlib_docs/).
-/


open set

/-- El interior de `S` es la unión de todos los subconjuntos abiertos de `X`
  contenidos en `S`. -/
def interior' (S : set X) : set X := ⋃ (U ∈ {V : set X | is_open V ∧ V ⊆ S}), U

-- Lema de reescritura
lemma mem_interior' (x : X) :
  x ∈ interior' S ↔ ∃ (U : set X) (hU : is_open U) (hUS : U ⊆ S), x ∈ U :=
begin
  unfold interior',
  simp only [set.mem_set_of_eq, set.mem_Union, exists_prop],
  tauto,
end

/-- Como hemos definido `interior'` como una `bUnion`, podemos empezar
  la demostración con `apply is_open_bUnion`. -/
lemma interior'_open : is_open (interior' S) := 
begin
  sorry
end

lemma interior'_subset : interior' S ⊆ S :=
begin
  sorry
end

variable {S}

lemma subset_interior' {U : set X} (hU : is_open U) (hUS : U ⊆ S) : U ⊆ interior' S :=
begin
  sorry
end

lemma interior'_mono {S T : set X} (hST : S ⊆ T) : interior' S ⊆ interior' T :=
begin
  sorry
end


/- En lugar de empezar con `ext x`, podéis usar `apply set.subset.antisymm`,
  que dice que si `S ⊆ T` y `T ⊆ S` entonces `S = T`. -/
lemma interior'_interior' : interior' (interior' S) = interior' S :=
begin
  sorry
end

--Ejemplos de interiores:

lemma interior'_empty : interior' (∅ : set X) = ∅ :=
begin
  sorry
end

lemma interior'_univ : interior' (set.univ : set X) = set.univ :=
begin
  sorry
end

lemma interior'_inter (S T : set X) : interior' (S ∩ T) = interior' S ∩ interior' T :=
begin
  sorry
end
 