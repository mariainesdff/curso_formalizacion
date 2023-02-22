/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : María Inés de Frutos-Fernández
-/

import tactic 
import data.real.basic

/-
# Ejercicios sobre números reales

Los siguientes ejercicios aparecen como pasos intermedios en algunos
de los problemas de `limites.lean`. Intenta resolverlos utilizando
las tácticas `library_search` y `linarith`.

NOTA: adaptado de los cursos de formalización de Kevin Buzzard.
-/

example (x : ℝ) : |(-x)| = |x| :=
begin
  sorry
end

example (x y : ℝ) : |x - y| = |y - x| :=
begin
  sorry
end 

example (A B C : ℕ) : max A B ≤ C ↔ A ≤ C ∧ B ≤ C :=
begin
  sorry
end

example (x y : ℝ) : |x| < y ↔ -y < x ∧ x < y :=
begin
  sorry
end

example (ε : ℝ) (hε : 0 < ε) : 0 < ε / 2 :=
begin
  sorry
end

example (a b x y : ℝ) (h1 : a < x) (h2 : b < y) : a + b < x + y :=
begin
  sorry
end

example (ε : ℝ) (hε : 0 < ε) : 0 < ε / 3 :=
begin
  sorry
end

example (a b c d x y : ℝ) (h1 : a + c < x) (h2 : b + d < y) :
  a + b + c + d < x + y :=
begin
  sorry,
end