/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : María Inés de Frutos-Fernández
-/

import tactic

/-! 
# Nuevas tácticas
* `use`
* `intro` (nueva forma de uso)
* `cases` (nueva forma de uso)
* `rintro`
* `ext`
-/

/- ## use 
Dada una meta de la forma `⊢ ∃ a, P a`, donde `P a` es una proposición, si `x : X` es el término que
queremos utilizar en la demostración, la táctica `use x` convertirá la meta en `⊢ P x`.
-/

example : ∃ P : Prop, P ∧ true ↔ false :=
begin
  use false,
  tauto,  -- cierra la meta construyendo una tabla de verdad
end

/- ## intro (nueva forma de uso)
Si la meta actual es de la forma `∀ x : t, u`, entonces `intro x` introduce una hipótesis local 
`x : t` y modifica la meta a `⊢ u`.
 -/

example (X : Type) : ∀ x : X, x = x :=
begin
  intro x,
  refl,
end

/- ## rintro 
La táctica `rintro` permite combinar `intro` y `cases` en una misma aplicación.
-/

/- Dada una meta de la forma `P ∧ Q → R`,  `rintro ⟨hP, hQ⟩` es equivalente a la secuencia
`intro h, cases h with hP hQ,`. Es decir, introduce dos hipótesis `hP : P` y `hQ : Q` y
cambia la meta a `R`. -/
example (P Q : Prop) : P ∧ Q → P :=
begin
  rintro ⟨hP, hQ⟩,
  exact hP,
end

/- Dada una meta de la forma `P ∨ Q → R`,  `rintro (hP | hQ)` es equivalente a la secuencia
`intro h, cases h with hP hQ,`. Es decir, introduce dos metas de la forma `⊢ R`, una asumiendo
 `hP : P` la otra asumiendo `hQ : Q`. -/
example (P Q R : Prop) (hPR : P → R) (hQR : Q → R) : P ∨ Q → R :=
begin
  rintro (hP | hQ),
  { exact hPR hP },
  { exact hQR hQ },
end

/- ## cases (nueva forma de uso) 
Dada una hipótesis `h : ∃ a : X, P a`, donde `P a` es una proposición, la táctica 
`cases h with x hx` devuelve un término `x : X` y una demostración `hx : P x`.
-/
example (X : Type) (P Q : X → Prop) (h : ∃ x : X, P x) : ∃ x : X, P x ∨ Q x :=
begin
  cases h with x hx,
  use x,
  left,
  exact hx,
end

/- ## ext 
Para demostrar que dos conjuntos son iguales, basta demostrar que tienen los mismos elementos.#check
Dada la meta `⊢ S = T`, donde `S` y `T` son conjuntos (de elementos de mismo tipo), `ext a`
convierte la meta en `⊢ a ∈ S ↔ a ∈ T`.
-/

example (X : Type) (S T : set X) (hST : S ⊆ T) (hTS : T ⊆ S) : S = T :=
begin
  ext a,
  split,
  { apply hST },
  { apply hTS }
end
