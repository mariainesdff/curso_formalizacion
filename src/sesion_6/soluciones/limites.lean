/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : María Inés de Frutos-Fernández
-/

import sesion_4.soluciones.limites

import topology.instances.real

/-
# Límites de secuencias en Lean

Ahora que sabemos cómo utilizar filtros en Lean, podemos reescribir
las soluciones de los ejercicios de límites de la sesión 4.

-/

open filter

open_locale topology -- para acceder a la notación 𝓝 

namespace limites

-- Nuestra definición `tends_to` es equivalente a `filter.tendsto`
lemma tends_to_iff_tendsto (a : ℕ → ℝ) (l : ℝ) :
  tends_to a l ↔ tendsto a at_top (𝓝 l) :=
begin
  rw metric.tendsto_at_top,
  rw tends_to,
  congr',
end

/-- El límite de la secuencia constante con valor `c` es `c`. -/
theorem tends_to_const (c : ℝ) : tends_to (λ n, c) c :=
begin
  rw tends_to_iff_tendsto,
  exact tendsto_const_nhds,
end

/-- Si `a(n)` tiende a `L` entonces `a(n) + c` tiende a `t + c` -/
theorem tends_to_add_const {a : ℕ → ℝ} {L : ℝ} (c : ℝ)
  (h : tends_to a L) :
  tends_to (λ n, a n + c) (L + c) :=
begin
  rw tends_to_iff_tendsto at *,
  exact tendsto.add_const c h,
end

/-- Si `a(n)` tiende a `L`, entonces `-a(n)` tiende a `-L`.
Si simplificar la expresión dentro del valor absoluto te está
dando problemas, ve a la hoja `reales.lean`.
-/
theorem tends_to_neg {a : ℕ → ℝ} {L : ℝ} (ha : tends_to a L) :
  tends_to (λ n, - a n) (-L) :=
begin
  rw tends_to_iff_tendsto at *,
  exact tendsto.neg ha,
end

/-- Si `a(n)` tiende a `La` y `b(n)` tiende a `Lb` entonces `a(n) + b(n)` 
  tiende a `La + Lb`. -/
theorem tends_to_add {a b : ℕ → ℝ} {La Lb : ℝ}
  (ha : tends_to a La) (hb : tends_to b Lb) :
  tends_to (λ n, a n + b n) (La + Lb) :=
begin
  rw tends_to_iff_tendsto at *,
  exact tendsto.add ha hb,
end


/-- Si `a(n)` tiende a `La` y `b(n)` tiende a `Lb` entonces `a(n) - b(n)`
tiende a `La - Lb`. -/
theorem tends_to_sub {a b : ℕ → ℝ} {La Lb : ℝ}
  (ha : tends_to a La) (hb : tends_to b Lb) :
  tends_to (λ n, a n - b n) (La - Lb) :=
begin
  rw tends_to_iff_tendsto at *,
  exact tendsto.sub ha hb,
end

/-- Si `a(n)` tiende a `L`, entonces `c*a(n)` tiende a `c*L`.
Pista: tratad el caso `c = 0` por separado, utilizando `by_cases hc : c = 0`.
-/
lemma tends_to_mul_const_left {a : ℕ → ℝ} {L c : ℝ} (h : tends_to a L) :
  tends_to (λ n, c * (a n)) (c * L) := 
begin
  rw tends_to_iff_tendsto at *,
  exact tendsto.const_mul c h,
end

/- Lema del sandwich. -/
theorem sandwich (a b c : ℕ → ℝ) (L : ℝ) (ha : tends_to a L) (hc : tends_to c L) 
  (hab : ∀ n, a n ≤ b n) (hbc : ∀ n, b n ≤ c n) : 
  tends_to b L :=
begin
  rw tends_to_iff_tendsto at *,
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le ha hc hab hbc, 
  -- Buscando `sandwich` o `squeeze` en la documentación de mathlib, aparece este lema.
end

/-- Si `a(n)` tiende a `La` y `b(n)` tiende a `Lb` entonces `a(n) * b(n)` 
  tiende a `La * Lb`. -/
theorem tends_to_mul {a b : ℕ → ℝ} {La Lb : ℝ}
  (ha : tends_to a La) (hb : tends_to b Lb) :
  tends_to (λ n, a n * b n) (La * Lb) :=
begin
  rw tends_to_iff_tendsto at *,
  exact tendsto.mul ha hb,
end

end limites