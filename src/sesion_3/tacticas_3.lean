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
* `refine`
* `obtain`
* `swap`
* `library_search`
* `simp`
* `group`
-/

/- ## refine 
Funciona como exact, pero permitiendo utilizar barras bajas _ en la expresión; cada una de ellas
será reemplazada por la submeta correspondiente. 

Por ejemplo, dada una meta de forma `P ∧ Q`, `refine ⟨_, _⟩`, es equivalente a `split`. Pero 
`refine` es más flexible: si por ejemplo ya tenemos una demostración `hP : P`, podemos usar
`refine ⟨hP, _⟩` y la meta pasará a ser `⊢ Q`.
-/

example {n : ℕ} : even n ↔ even (n^2) :=
begin
  refine ⟨λ hn, even.pow_of_ne_zero hn (two_ne_zero), λ hn, _⟩,
  rw [pow_two, nat.even_mul, or_self] at hn,
  exact hn,
end
/- ## obtain
La táctica `obtain` combina `have` y `cases`.
La instrucción `obtain ⟨pattern⟩ : type := proof` es equivalente a
```
have h : type,
{ ... },
rcases h with ⟨patt⟩
```
En muchos casos no es necesario incluir el tipo explícitamente
-/

example {n : ℕ} (hn : even n) : odd (n + 1) :=
begin
  obtain ⟨k, hk⟩ := hn,
  refine ⟨k, _⟩,
  rw [hk, two_mul],
end

example {X Y Z : Type*} {f : X → Y} {g : Y → Z} (hf : function.surjective f) 
  (hg : function.surjective g) : function.surjective (g ∘ f) :=
begin
  intros z,
  have hgz : ∃ (a : Y), g a = z,
  { exact hg z},
  cases hgz with y hy,
  obtain ⟨x, hx⟩ := hf y,
  use x,
  rw [function.comp_app, hx, hy],
end

/- ## swap 
La táctica `swap` intercambia las dos primeras metas.

También se puede utilizar como `swap n`, que convierte la enésima meta en la primera.
-/

example {Ω : Type*} {X Y : set Ω} (hXY : X ⊆ Y) (hYX : Y ⊆ X) : X = Y :=
begin
  ext a,
  split,
  swap,
  { apply hYX },
  { apply hXY },
end

/- ## library_search 
`library_search` intenta cerrar la meta actual aplicando un lema existente en la librería mathlib.
Si lo encuentra, imprime un mensaje `exact ...` con la solución empleada.

-/

--example {n m : ℕ} : n + m = m + n := by library_search

--example {n m : ℕ} (hn : even n) (hm : odd m) : odd (m + n) := by library_search

/- ## simp
Muchos lemas de mathlib que demuestran igualdades o equivalencias lógicas están marcados con la 
etiqueta `@[simp]`. También podemos utilizar esta etiqueta en lemas que demostremos.

La táctica `simp` intenta encontrar lemas cuyo lado izquierdo aparece en la meta, y sustituirlos por
el lado derecho (por tanto, si creamos un lema marcado `@[simp]`, el lado derecho debe ser la 
expresión más sencilla).

También podemos usar `simp [lema1, lema2, ...]` para que, además de los lemas etiquetados, el 
simplificador también intente utilizar los lemas proporcionados.

Podemos utilizar `simp` en hipótesis locales, con la sintaxis `simp at h`.

No es buena práctica utilizar `simp` en el medio de una demostración; es mejor sustituirlo por
una aplicación de `simp only [...]`, como veremos abajo.
-/

example : (0 : ℝ) + 1 = 1 + 0 := by simp

open_locale big_operators
open finset

example (n : ℕ) : ∑ i in range n, (i : ℝ) = n * (n - 1) / 2 :=
begin
  induction n with d hd,
  { -- la suma sobre el conjunto vacío es 0 * (0 - 1) / 2
    simp },
  { -- inducción
    rw [sum_range_succ, hd],
    simp, -- reduce la meta a ⊢ ↑d * (↑d - 1) / 2 + ↑d = (↑d + 1) * ↑d / 2
    ring, 
  }
end

/- ### simp only
Si utilizamos `simp only [h₁ h₂ ... hₙ]` en lugar de `simp [h₁ h₂ ... hₙ]`, el simplificador sólo
utilizará los lemas hᵢ, pero no los lemas marcados con `@[simp]`.
-/

example (n : ℕ) : ∑ i in range n, (i : ℝ) = n * (n - 1) / 2 :=
begin
  induction n with d hd,
  { -- la suma sobre el conjunto vacío es 0 * (0 - 1) / 2
    simp only [range_zero, sum_empty, nat.cast_zero, zero_mul, zero_div], },
  { -- inducción
    rw [sum_range_succ, hd],
    simp only [nat.cast_succ, add_tsub_cancel_right], 
    -- reduce la meta a ⊢ ↑d * (↑d - 1) / 2 + ↑d = (↑d + 1) * ↑d / 2
    ring, 
  }
end

/- ### squeeze_simp 
`squeeze_simp` funciona como `simp`, y además imprime un mensaje `simp only [...]` con la lista
de lemas que han sido utilizados.
-/

--example : (0 : ℝ) + 1 = 1 + 0 := by squeeze_simp

/- ## group
Esta táctica se utiliza para simplificar expresiones en grupos multiplicativos, utilizando sólo
los axiomas de grupo, sin asumir conmutatividad.

No utiliza las hipótesis locales, por lo que es probable que haya que combinarla con otras tácticas
como rw.
-/

-- Ejemplo tomado de la documentación de mathlib
example {G : Type} [group G] (a b c d : G) (h : c = (a*b^2)*((b*b)⁻¹*a⁻¹)*d) : a*c*d⁻¹ = a :=
begin
  group at h, -- normaliza `h`, obteniendo `h : c = d`
  rw h,       -- la meta es ahora `a*d*d⁻¹ = a`
  group,      -- group cierra la meta
end
