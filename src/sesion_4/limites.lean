/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : María Inés de Frutos-Fernández
-/

import tactic 
import data.real.basic

/-
# Límites de secuencias en Lean
Escribimos la definicón `ε` - `N` del límite de una secuencia de
números reales y demostramos resultados sobre límites.

NOTA: adaptado de los cursos de formalización de Kevin Buzzard.
-/

/- ### Notación lambda (λ) para funciones
Recordatorio: para representar una función `f` en Lean, utilizamos notación lambda:
`λ x, f x` es la función que asigna a `x` el valor `f (x)`. -/

def f : ℕ → ℝ := λ n, n^2 + 3 -- `f(n) = n^2 + 3`

example : f 3 = 12 :=
begin
  rw f,
  dsimp only, -- Para simplificar la aplicación de funciones
  norm_num, -- Normaliza expresiones numéricas
end

/-
## Límite de una secuencia
-/

/-- Si `a(n)` es una secuencia de números reales y `L` es un real,
 `tends_to a L` dice que el límite de `a(n)` cuando `n → ∞` es `L`. -/
def tends_to (a : ℕ → ℝ) (L : ℝ) : Prop :=
∀ ε > 0, ∃ N : ℕ, ∀ n, N ≤ n → |a n - L| < ε

/-- Este lema nos permite reescribir la definición de `tends_to` en nuestras pruebas. -/
theorem tends_to_def {a : ℕ → ℝ} {t : ℝ} :
  tends_to a t ↔ ∀ ε, 0 < ε → ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε :=
begin
  refl
end

/-
## Ejercicios
-/

/-- El límite de la secuencia constante con valor `c` es `c`. -/
theorem tends_to_const (c : ℝ) : tends_to (λ n, c) c :=
begin
  sorry
end

/-- Si `a(n)` tiende a `L` entonces `a(n) + c` tiende a `t + c` -/
theorem tends_to_add_const {a : ℕ → ℝ} {L : ℝ} (c : ℝ)
  (h : tends_to a L) :
  tends_to (λ n, a n + c) (L + c) :=
begin
  sorry
end

/-- Si `a(n)` tiende a `L`, entonces `-a(n)` tiende a `-L`.
Si simplificar la expresión dentro del valor absoluto te está
dando problemas, ve a la hoja `reales.lean`.
-/
theorem tends_to_neg {a : ℕ → ℝ} {L : ℝ} (ha : tends_to a L) :
  tends_to (λ n, - a n) (-L) :=
begin
  sorry
end

/-- Si `a(n)` tiende a `La` y `b(n)` tiende a `Lb` entonces `a(n) + b(n)`
tiende a `La + Lb`.
Esta demostración es más complicada que las anteriores.
-/
theorem tends_to_add {a b : ℕ → ℝ} {La Lb : ℝ}
  (ha : tends_to a La) (hb : tends_to b Lb) :
  tends_to (λ n, a n + b n) (La + Lb) :=
begin
  sorry
end

/-- Si `a(n)` tiende a `La` y `b(n)` tiende a `Lb` entonces `a(n) - b(n)`
tiende a `La - Lb`. -/
theorem tends_to_sub {a b : ℕ → ℝ} {La Lb : ℝ}
  (ha : tends_to a La) (hb : tends_to b Lb) :
  tends_to (λ n, a n - b n) (La - Lb) :=
begin
  sorry
end

/-- Si `a(n)` tiende a `L`, entonces `c*a(n)` tiende a `c*L`.
Pista: tratad el caso `c = 0` por separado, utilizando `by_cases hc : c = 0`.
-/
lemma tends_to_mul_const_left {a : ℕ → ℝ} {L c : ℝ} (h : tends_to a L) :
  tends_to (λ n, c * (a n)) (c * L) := 
begin
  sorry
end

/- Lema del sandwich. -/
theorem sandwich (a b c : ℕ → ℝ) (L : ℝ) (ha : tends_to a L) (hc : tends_to c L) 
  (hab : ∀ n, a n ≤ b n) (hbc : ∀ n, b n ≤ c n) : 
  tends_to b L :=
begin
  sorry
end
