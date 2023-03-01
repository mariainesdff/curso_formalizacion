/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : María Inés de Frutos-Fernández
-/

import order.filter.basic

/-!
# Filtros
La definición de `filtro` en Lean es la siguiente:

structure filter (α : Type*) :=
(sets                   : set (set α))
(univ_sets              : set.univ ∈ sets)
(sets_of_superset {x y} : x ∈ sets → x ⊆ y → y ∈ sets)
(inter_sets {x y}       : x ∈ sets → y ∈ sets → x ∩ y ∈ sets)


## Notación y resultados útiles.

Fijamos `α : Type`, `F : filter α` y `S : set α`.

Por definición, la notación `S ∈ F` significa `S ∈ F.sets`. 
(La intuición es `F ⊆ S`, aunque por supuesto esto no tiene
sentido porque `F` es un filtro, no un subconjunto).

Dos filtros `F` y `G` son iguales si y sólo si 
`∀ S, S ∈ F ↔ S ∈ G`. 

Los lemas correspondientes a las condiciones que
aparecen en la definición de filtro son:

`univ_mem : univ ∈ F`
`mem_of_superset : S ∈ F → S ⊆ T → T ∈ F`
`inter_mem : S ∈ F → T ∈ F → S ∩ T ∈ F`

Estos lemas están en el espacio de nombres `filter`.
-/

-- Abrimos los espacios de nombres `filter` y `set`.
open filter set 

--  Sea `α` un tipo, `F` un filtro sobre `α`, y `S` y `T` dos subconjuntos de `α`.
variables (α : Type) (F : filter α) (S T : set α)

/-
Dos subconjuntos `S` y `T` están en un filtro `F` si y sólo
si su intersección está en `F`.

Los lemas `inter_subset_left S T : S ∩ T ⊆ S` e `inter_subset_right S T : S ∩ T ⊆ S`
son útiles para esta demostración.
-/
example : S ∩ T ∈ F ↔ S ∈ F ∧ T ∈ F :=
begin
  split,
  { intro hST,
    exact ⟨mem_of_superset hST (inter_subset_left S T), 
      mem_of_superset hST (inter_subset_right S T) ⟩, },
  { rintro ⟨hS, hT⟩,
    exact inter_mem hS hT }
end

/-! ## Ejemplos de filtros -/

/- ### Filtros principales
Dado un subconjunto `X` de `α`, el filtro principal de `X` es la 
colección de subconjuntos de `α` que contienen `X`.
Está definido en mathlib, y denotado mediante `𝓟 X`, pero en 
este ejemplo vamos a demostrar nosotros mismos que es un filtro.

Lemas útiles:
`mem_univ s : s ∈ univ`
`subset.trans : A ⊆ B → B ⊆ C → A ⊆ C`
`subset_inter : X ⊆ S → X ⊆ T → X ⊆ S ∩ T`
`mem_set_of_eq : x ∈ {a : α | p a} = p x`
-/

-- El filtro principal de `X`.
example (X : set α) : filter α :=
{ sets := {S : set α | X ⊆ S},
  univ_sets := begin
    exact subset_univ _,
  end,
  sets_of_superset := begin
    intros S T hS hST,
    exact subset.trans hS hST,
  end,
  inter_sets := begin
    intros S T hS hT,
    exact subset_inter hS hT,
  end }

/-- ### EL filtro `at_top` en un conjunto totalmente ordenado

Sea `L` un conjunto linearmente ordenado no vacío.
Vamos a construir un filtro `at_top` que representa un
"entorno infinitesimal" de `∞`. En concreto, los conjuntos 
pertenecientes a este filtro serán aquellos `X : set L`
para los que existe un `x : L` tal que para todo `y ≥ x`, `y ∈ X`.
-/
def at_top (L : Type) [linear_order L] (e : L) : filter L :=
{ sets := {X : set L | ∃ x : L, ∀ y, x ≤ y → y ∈ X},
  univ_sets := begin
    use e,
    rintros y -,
    exact mem_univ _,
  end,
  sets_of_superset := begin
    intros S T hS hST,
    simp only [mem_set_of_eq] at hS ⊢,
    obtain ⟨s, hs⟩ := hS,
    use s,
    intros x hx,
    exact hST (hs x hx),
  end,
  inter_sets := begin
    rintros S T ⟨s, hs⟩ ⟨t, ht⟩,
    use max s t,
    intros x hx,
    exact ⟨hs _ (le_trans (le_max_left s t) hx), ht _ (le_trans (le_max_right s t) hx)⟩,
  end }

/-! ### El filtro cofinito
El filtro cofinito en un tipo `α` es la colección de subconjuntos `S : set α`
con la propiedad de que el complemento `Sᶜ`de `S` es finito.

Lemas útiles:
`compl_univ : univᶜ = ∅`
`finite_empty : finite ∅`
`compl_subset_compl : Xᶜ ⊆ Yᶜ ↔ Y ⊆ X`
`finite.subset : S.finite → ∀ {T : set α}, T ⊆ S → T.finite`
`compl_inter S T : (S ∩ T)ᶜ = Sᶜ ∪ Tᶜ`
`finite.union : S.finite → T.finite → (S ∪ T).finite`.
-/
def cofinite (α : Type) : filter α :=
{ sets := { S : set α | (Sᶜ).finite },
  univ_sets := begin
    simp only [mem_set_of_eq, compl_univ, finite_empty],
  end,
  sets_of_superset := begin
    intros S T hS hST,
    rw ← compl_subset_compl at hST, 
    exact finite.subset hS hST,
  end,
  inter_sets := begin
    intros S T hS hT,
    rw [mem_set_of_eq, compl_inter],
    exact finite.union hS hT,
  end }

-- Esta instrucción nos permite acceder a la notación `𝓟 X` para el filtro principal
open_locale filter

/-!
## El orden (≤) sobre los filtros de `α`
Los filtros están parcialmente ordenados, mediante la relación `≤`
definida mediante `F ≤ G` si y sólo si `G.sets ⊆ F.sets`. 
(Cuanto más pequeño es el filtro `F`, más grande es la colección
`F.sets`, ya que el "conjunto generalizado" `F` está "contenido"
en más conjuntos).

En este ejemplo vamos a demostrar que `𝓟 S ≤ 𝓟 T ↔ S ⊆ T`.
Esto es lo que dice el lema `principal_mono` de mathlib,
pero vamos a demostrarlo utilizando los lemas:
`mem_principal : T ∈ 𝓟 S ↔ S ⊆ T`
`mem_principal_self S : S ∈ 𝓟 S`
`le_def : F ≤ G ↔ ∀ (S : set α), S ∈ G → S ∈ F`
-/

example (S T : set α) : 𝓟 S ≤ 𝓟 T ↔ S ⊆ T :=
begin
  split; -- La siguiente instrucción se aplica a todas las metas abiertas (por el ;).
  intro hST,
  { rw ← mem_principal, -- Puedes comentarla y la prueba sigue funcionando
    rw le_def at hST,
    exact hST T (mem_principal_self T), },
  { intros X hX,
    rw mem_principal at hX ⊢, -- Puedes comentarla y la prueba sigue funcionando
    exact subset.trans hST hX, },
end

/- Este ejemplo se llama `le_principal_iff` en mathlib, pero podemos demostrarlo a
  partir de las definiciones y lemas anteriores. -/
example (F : filter α) (S : set α) : F ≤ 𝓟 S ↔ S ∈ F :=
begin
  rw le_def,
  exact ⟨λ h, h S (mem_principal_self S), λ h T hT, mem_of_superset h hT⟩,
end
