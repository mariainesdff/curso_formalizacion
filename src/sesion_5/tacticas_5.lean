/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : María Inés de Frutos-Fernández
-/

import tactic
import data.nat.parity
import data.real.basic
import data.finset.basic
import data.real.basic


/-! 
# Nuevas tácticas
* `rwa`
* `rintro` (truco con `rfl`)
-/

/- ## rwa
  Combina las tácticas `rw` y `assumption`. Es decir, si una de nuestras
  hipótesis locales (digamos `h`) es igual a la meta después de aplicar 
  el rewrite, `rwa` cierra la meta, ahorrándonos la instrucción `exact h`. -/

example {P Q R : Prop} (h1 : P ↔ Q) (h2 : Q ↔ R) : 
  P ↔ R :=
begin
  rwa h1
  -- equivalente a
  -- rw h1, exact h2,
end


/- ## rintro

Una forma alternative de utilizar `rintro` es sustituyendo uno de los argumentos,
que necesariamente debe ser de la forma `h : a = b`, por la palabra clave `rfl`. 
El efecto es que `rintro` reemplazará b por a ó viceversa en todo lugar posible.

Este truco también funciona con otras tácticas como `rcases` y `obtain`.
-/

-- Versión sin rfl
example {X Y : Type} (f : X → Y) {y : Y} (T : set Y) :
  (∃ x : X, x ∈ f ⁻¹' T ∧ f x = y) → y ∈ T :=
begin
  rintro ⟨x, hx, hxy⟩,
  rw ← hxy,
  exact hx,
end

-- Versión con rfl
example {X Y : Type} (f : X → Y) {y : Y} (T : set Y) :
  (∃ x : X, x ∈ f ⁻¹' T ∧ f x = y) → y ∈ T :=
begin
  rintro ⟨x, hx, rfl⟩,
  exact hx,
end

