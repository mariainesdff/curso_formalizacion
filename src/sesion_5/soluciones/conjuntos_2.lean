/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : María Inés de Frutos-Fernández
-/

import data.set.lattice -- para uniones e intersecciones arbitrarias

/-

# Conjuntos

Recordad que `set X` es el tipo de subconjuntos de `X`. Es decir, `S : set X` 
indica que `S` es un conjunto de términos de `X`.

En la segunda sesión del curso, aprendimos a indicar pertenencia a 
un conjunto (`x ∈ S`, donde `x : X`) y demostramos algunos lemas sobre
inclusión de conjuntos (`⊆`), uniones (`∪`) e intersecciones (`∩`).


## Detalle de implementación

Internamente, `set X` está implementado como una función de `X` a `Prop`. 
Un `S : set X` está representado mediante la función que manda todos
los elementos de `S` a `true` y el resto de elementos de `X` a `false.`
El enunciado `a ∈ S` está representado por la proposición `S a`.

Sin embargo, para trabajar con conjuntos en Lean no es necesario conocer
este detalle de implementación, sino cuál es la API disponible (es decir,
qué resultados sobre conjuntos ya están demostrados en mathlib).

## Notación

Dados tipos `(X Y : Type)` y una función `f : X → Y`:

El conjunto vacío es `∅ : set X`.

El conjunto que contiene todos los elementos de `X` es `univ : set X`.

El complemento de `S : set X` es `Sᶜ : set X`.

Dado `S : set X`, la imagen de `S` bajo `f` se denota como `f '' S : set Y`.

Dado `T : set Y`, `f ⁻¹' T : set X` denota la preimagen de `T`.

El rango de `f` se puede escribir como `f '' univ` ó `range f`. 

-/

variables (X Y Z : Type) (f : X → Y) (g : Y → Z) (S : set X) (y : Y)

open set

/-!

## Imagen

`y ∈ f '' S` es definicionalmente igual a `∃ x : X, x ∈ S ∧ f x = y`,
y el correspondiente lema de reescritura es
`mem_image f S y : y ∈ f '' S ↔ ∃ (x : X), x ∈ S ∧ f x = y`
-/

-- Vamos a ver cómo simplificar el siguiente ejemplo.
example : id '' S = S :=
begin
  ext x,
  split,
  { intro hx,
    rw mem_image at hx,
    obtain ⟨x', h, h'⟩ := hx,
    rw ← h',
    exact h, },
  { intro hx,
    rw mem_image,
    use x,
    use hx,
    refl, },
end

-- Aunque por supuesto ya lo tenemos en mathlib:
example : id '' S = S :=
begin
  apply image_id', -- por ejemplo, `simp` o `library_search` lo demostrarían
end


lemma image_comp (S : set X) : (g ∘ f) '' S = g '' (f '' S) :=
begin
  ext x,
  simp only [mem_image, exists_exists_and_eq_and],
end

open function

-- Recordad que podéis usar `dsimp only` para simplificar las evaluaciones de lambdas.
lemma image_injective : injective f → injective (λ S, f '' S) :=
begin
  intros hf S T hST,
  dsimp only at hST,
  ext x,
  rw [← injective.mem_set_image hf, ← injective.mem_set_image hf, hST],
end

/-!

## Preimagen

Por definición, tenemos `x ∈ f ⁻¹' T ↔ f x ∈ T`. El correspondiente lema
de reescritura es `mem_preimage : x ∈ f ⁻¹' T ↔ f x ∈ T`.
-/

example (S : set X) : S = id ⁻¹' S :=
begin
  simp only [preimage_id_eq, id.def],
end

-- Una vez terminado este ejercicio, mirad la solución propuesta.
example (T : set Z) : (g ∘ f) ⁻¹' T = f ⁻¹' (g ⁻¹' T) :=
begin
  refl,
end

/-- `squeeze_simp` o ` library_search` encuentran la demostración de este lema 
  y los dos siguientes en la librería, pero intentad demostrarlos a partir de
  las definiciones. -/
lemma preimage_injective (hf : surjective f) : injective (λ T, f ⁻¹' T) :=
begin
  intros S T hST,
  dsimp only at hST,
  ext y,
  obtain ⟨x, hxy⟩ := hf y,
  rw [← hxy, ← mem_preimage, ← mem_preimage, hST],
end

lemma image_surjective (hf : surjective f) : surjective (λ S, f '' S) :=
begin
  intros T,
  use f⁻¹' T,
  dsimp only,
  ext y,
  split,
  { rintros ⟨x, hx, rfl⟩,
    exact hx, },
  { intros hy,
    obtain ⟨x, rfl⟩ := hf y,
    use [x, hy, rfl], }
end

lemma preimage_surjective (hf : injective f) : surjective (λ S, f ⁻¹' S) :=
begin
  intros S,
  use f '' S,
  dsimp only,
  ext x,
  split,
  { rintros ⟨y, hyS, hyx⟩,
    rwa ← hf hyx, },
  { intros hx,
    exact ⟨x, hx, rfl⟩, }
end

/-!

## Uniones arbitrarias (`Union`)

Dado un tipo `(ι : Type)` y una función `(F : ι → set X)` , los
`F i` para `i : ι` son una familia de subconjuntos de `X`, y por
tanto podemos tomar su unión.
En Lean, esto se representa mediante `Union F` (la U mayúscula es
necesaria para uniones arbitrarias). También está disponible la
notación `⋃ (i : ι), F i`.

Podéis utilizar el siguiente lema, que dice que `x : X` pertenece
a `Union F` si y sólo si pertenece a uno de los conjuntos `F i`:
`mem_Union : (x ∈ ⋃ (i : ι), F i) ↔ ∃ j : ι, x ∈ F j`

-/

variables (ι : Type) (F : ι → set X) (x : X)

lemma image_Union (F : ι → set X) (f : X → Y) :
  f '' (⋃ (i : ι), F i) = ⋃ (i : ι), f '' (F i) :=
begin
  ext y,
  split,
  { rintro ⟨x, h, rfl⟩,
    rw mem_Union at h ⊢,
    obtain ⟨i, hi⟩ := h,
    use [i, x, hi], },
  { intro h,
    rw mem_Union at h,
    rcases h with ⟨i, x, hxi, rfl⟩,
    use x,
    rw mem_Union,
    use [i, hxi] }
end

/-!

## bUnion

En ocasiones, dados `ι : Type` y `F : ι → set X`, no queremos tomar
la unión sobre todos los términos de `ι`, sino sólo sobre
aquéllos que pertenezcan a un subconjunto `Z : set ι`.
Para ello podemos utilizar la notación `⋃ (i ∈ Z), F i`.

Los lemas para este tipo de uniones tienen `bUnion` en el nombre.
Por ejemplo:
`mem_bUnion_iff : (x ∈ ⋃ (i ∈ J), F i) ↔ ∃ (j ∈ J), x ∈ F j`

-/

lemma preimage_bUnion (F : ι → set Y) (Z : set ι) :
  f ⁻¹' (⋃ (i ∈ Z), F i) = ⋃ (i ∈ Z), f ⁻¹' (F i) :=
begin
  ext x,
  simp only [mem_Union, mem_preimage],
end