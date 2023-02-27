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
  apply is_open_bUnion,
  intros U hU,
  exact hU.left,
end

lemma interior'_subset : interior' S ⊆ S :=
begin
  intros x hx,
  rw mem_interior' at hx,
  obtain ⟨U, hU, hUS, hUX⟩ := hx,
  exact hUS hUX,
end

variable {S}

lemma subset_interior' {U : set X} (hU : is_open U) (hUS : U ⊆ S) : U ⊆ interior' S :=
begin
  intros x hx,
  rw mem_interior',
  exact ⟨U, hU, hUS, hx⟩,
end

lemma interior'_mono {S T : set X} (hST : S ⊆ T) : interior' S ⊆ interior' T :=
begin
  rintros x hx,
  rw mem_interior' at hx ⊢,
  obtain ⟨U, hU, hUS, hUx⟩ := hx,
  exact ⟨U, hU, subset_trans hUS hST, hUx⟩,
end


/- En lugar de empezar con `ext x`, podéis usar `apply set.subset.antisymm`,
  que dice que si `S ⊆ T` y `T ⊆ S` entonces `S = T`. -/
lemma interior'_interior' : interior' (interior' S) = interior' S :=
begin
  apply set.subset.antisymm,
  { exact interior'_subset _ },
  { exact subset_interior' (interior'_open _) rfl.subset },
end

--Ejemplos de interiores:

lemma interior'_empty : interior' (∅ : set X) = ∅ :=
begin
  exact set.eq_empty_of_subset_empty (interior'_subset _)
end

lemma interior'_univ : interior' (set.univ : set X) = set.univ :=
begin
  exact set.eq_univ_of_univ_subset (subset_interior' is_open_univ rfl.subset)
end

lemma interior'_inter (S T : set X) : interior' (S ∩ T) = interior' S ∩ interior' T :=
begin
  apply set.subset.antisymm,
  { rw [set.subset_inter_iff],
    exact ⟨interior'_mono (inter_subset_left _ _), interior'_mono (inter_subset_right _ _)⟩, },
  { rintros x ⟨hxS, hxT⟩,
    rw mem_interior' at hxS hxT ⊢,
    obtain ⟨U, hU, hUS, hUx⟩ := hxS,
    obtain ⟨V, hV, hVT, hVx⟩ := hxT,
    refine ⟨U ∩ V, hU.inter hV, inter_subset_inter hUS hVT, mem_inter hUx hVx⟩ },
end
