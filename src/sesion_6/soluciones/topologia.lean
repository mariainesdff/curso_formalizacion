/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : María Inés de Frutos-Fernández
-/

import topology.instances.real
import topology.subset_properties

variables (X Y : Type) [topological_space X] [topological_space Y] (f : X → Y)

open filter set

open_locale filter -- para acceder a la notación 𝓟
open_locale topology -- para acceder a la notación 𝓝 

/-
## Filtro de entornos
Si `α` es un espacio topológico y `a : α`, entonces `𝓝 a` es el filtro sobre `α`
determinado por `X ∈ 𝓝 a` si y sólo si `X` contiene un entorno abierto de `a`, 
o equivalentemente, si `a` está en el interior de `X`.

Interpretamos `𝓝 a` como el "subconjunto generalizado" de `α` 
correspondiente a un entorno abierto intinitesimal de `a`. 
-/

variables {α : Type*} [topological_space α]

open set


/- En este ejemplo vamos a demostrar que `𝓝 a` es un filtro.

Lemas útiles:

`interior_univ : interior univ = univ`
`mem_univ x : x ∈ univ`
`interior_mono : s ⊆ t → interior s ⊆ interior t`
`??? : interior (s ∩ t) = interior s ∩ interior t` -- ¿Puedes encontrar este lema?
 -/
example (a : α): filter α :=
{ sets := {X : set α | a ∈ interior X},
  univ_sets := begin
    simp only [mem_set_of_eq, interior_univ],
  end,
  sets_of_superset := begin
    intros S T hS hST,
    simp only [mem_set_of_eq] at hS ⊢,
    exact mem_of_subset_of_mem (interior_mono hST) hS,
  end,
  inter_sets := begin
    intros S T hS hT,
    simp only [mem_set_of_eq, interior_inter, mem_inter_iff],
    exact ⟨hS, hT⟩,
  end }

/-
## Puntos de acumulación

Un punto de acumulación, o punto límite (`cluster_pt` en mathlib) `x : α`
de un filtro `F : filter α` en un espacio topológico `α` es un `x : α`
tal que  `𝓝 x ⊓ F ≠ ⊥`.

¿Qué significa esto? `⊥` denota el filtro más pequeño, es decir,
el filtro que contiene todos los subconjuntos de `α`.
Por otro lado, `𝓝 x ⊓ F` es el filtro generado por `F` y por los
entornos de `x`,
Por tanto, el enunciado `𝓝 x ⊓ F ≠ ⊥` dice que no existen conjuntos
`A ∈ 𝓝 x` y `B ∈ F` tal que `A ∩ B = ∅`, o en otras palabras, que 
cada elemento del filtro `F` interseca cada entorno de `x`.

Por ejemplo, si `F = 𝓟 S` es el filtro principal de un subconjunto `S` 
de `α`, entonces los puntos de acumulación de `𝓟 S` son los puntos
`x` tales que cualquier abierto que contiene a  `x` tiene intersección
no vacía con `S`. Equivalentemente, `x` está en la clausura de `S`.

La idea es que debemos pensar en el punto de acumulación `a : α` de `F : filter α` 
como un punto en la clausura del "subconjunto generalizado" correspondiente a `F`. 
-/

/-- Este lema se llama `cluster_pt.mono` en mathlib. 

La idea es que si `F` y `G` son "subconjuntos generalizados" de un espacio
topológico y "`F ⊆ G`", entonces "`clausura F ⊆ clausura G`".

Empieza la demostración reescribiendo `cluster_pt_iff`.-/
example {x : α} {F G : filter α} (hxF : cluster_pt x F) (hFG : F ≤ G) :
  cluster_pt x G :=
begin
  rw cluster_pt_iff at hxF ⊢,
  intros S hS T hT,
  exact hxF hS (hFG hT),
end

/-
## Compacidad
La definición de compacto (`is_compact`) en mathlib está escrita utilizando
filtros: un subconjunto `S` de un espacio topológico `α` es *compacto*
si para todo filtro no trivial `F ≠ ⊥` tal que `S ∈ F`,
existe `a : α` tal que todo subconjunto de `F` interseca todo entorno abierto de `a`:

`def is_compact (S : set α) := ∀ ⦃F⦄ [ne_bot F], F ≤ 𝓟 S → ∃ a ∈ S, cluster_pt a F`

Esta definición es equivalente a la definición "usual" de subconjunto compacto.

En el siguiente ejercicio, vamos a utilizarla para demostrar que un subconjunto
cerrado de un conjunto compacto es compacto. En realidad demostraremos algo más 
general: si `α` es un espacio topológico, entonces la intersección de un
subconjunto compacto de `α` y un subconjunto cerrado de `α` es un subconjunto
compacto de `α`.
-/

lemma closed_of_compact (S : set X) (hS : is_compact S)
  (C : set X) (hC : is_closed C) : is_compact (S ∩ C) :=
begin
  rw is_compact,
  /-  Sea `F` un filtro distinto de `⊥`, y tal que `F ≤ 𝓟 (S ∩ C)` 
  (es decir, que contiene `S ∩ C`). -/
  intros F hnF hFSC,
  -- Tenemos que encontrar un punto límite para `F` contenido en `S ∩ C`.

  /- Como `ne_bot f` está entre `[ ]` en la definición de `is_compact`,
    el sistema de inferencia de clases va a buscarlo. Para que lo encuentre,
    lo añadimos explícitamente con esta instrucción `haveI`.-/
  haveI := hnF,

  /- Primero demostraremos que, dado que `S` es compacto, podemos encontrar un
    punto límite `a` para `F` en `S`. -/
  have hFS : ∃ (a : X) (H : a ∈ S), cluster_pt a F,
  { apply hS,
    apply le_trans hFSC,
    rw principal_mono,
    exact set.inter_subset_left _ _, },
  obtain ⟨a, haS, haF⟩ := hFS,

  /- Ahora demostramos que `a` también está en `C`, porque `C` es cerrado.
  Lemas útiles:
  `is_closed.closure_eq : is_closed C → closure C = C`
  `mem_closure_iff_cluster_pt : a ∈ closure S ↔ cluster_pt a (𝓟 S)`- -/
  have haC : a ∈ C,
  { rw [← hC.closure_eq, mem_closure_iff_cluster_pt],
    apply cluster_pt.mono haF,
    apply le_trans hFSC,
    rw principal_mono,
    exact set.inter_subset_right _ _, },

 exact ⟨a, ⟨haS, haC⟩, haF⟩,
end