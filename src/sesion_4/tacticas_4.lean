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
* `specialize`
* `convert`
* `linarith`
-/

/- ## specialize
La táctica `specialize` se puede aplicar a hipótesis locales
de la forma `∀ x₁ ... xₙ , P x₁ ... xₙ` o `P → Q → R → ...`.  

Al aplicar `specialize h a₁ ... aₙ`, las premisas de `h` se instancian con los
argumentos `a₁ ... aₙ`.

La táctica añade una nueva hipótesis `h := h a₁ ... aₙ` con el mismo nombre e intenta
eliminar la anterior

NOTA: no siempre es necesario utilizar esta táctica. Es especialmente útil cuando queremos
reescribir en la hipótesis resultante.
-/

example (h : ∀ n : ℕ, even (2*n)) : even 2 :=
begin
  specialize h 1,
  rw mul_one at h,
  exact h,
end

example {P Q : Prop} (hP : P) (h : P → Q) : Q :=
begin
  specialize h hP,
  exact h,
  -- Pero también podríamos haber hecho `exact h hP` directamente.
end

/- ## convert
`convert h` es similar a `refine h`, pero el tipo de `h` no tiene que ser exactamente
igual al de la meta, sino que se crearán nuevas metas para cada una de las diferencias.
-/

example (x y z ε : ℝ) (h : |x| < ε) : |x + z - z| < ε :=
begin
  convert h,
  ring,
end

/- A veces `convert` es demasiado agresivo. Podemos controlar su comportamiento utilizando
`convert h using n`, donde `n` es un número pequeño.  -/
example {x : ℝ} (hx : |x| = 3) : |(-x)| = 3 :=
begin
  --convert hx, -- Reduce la meta a -x = x
  convert hx using 1,
  exact abs_neg _,
end

/- ## linarith 
La táctica `linarith` se puede utilizar para demostrar una desigualdad linear, o para derivar
una contradicción a partir de una familia de igualdades y desigualdades.
Utiliza las hipótesis locales.
-/

example {a b c d : ℝ} (h1 : a < b) (h2 : b ≤ c) (h3 : c = d) :
  a + a < d + b :=
begin
  linarith
end


example (x y z : ℚ) (h1 : 2*x  < 3*y) (h2 : -4*x + 2*z < 0) (h3 : 12*y - 4* z < 0)  : false :=
by linarith
