/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : María Inés de Frutos-Fernández
-/

import data.real.basic -- Importamos los números reales.

/-!
Algunos de estos ejercicios se han adaptado de la charla de estructuras y classes de LftCM 2022:
<https://icerm.brown.edu/video_archive/?play=2897>
-/

open nat

noncomputable theory 

/-! # Estructuras

Una estructura es una colección de campos de datos, posiblemente con restricciones que dichos
datos deben satisfacer.

Una instancia de la estructura es una colección concreta de datos que satisfacen las restricciones.
-/

/-- Un elemento de ℝ³ es una tupla de tres números reales. -/
@[ext] structure R3 :=
(x : ℝ)
(y : ℝ)
(z : ℝ)

/- Marcar la definición con la etiqueta `@[ext]` hace que Lean genere teoremas para demostrar
que dos términos de `R3` son iguales cuando sus componentes lo son. También nos permitirá
utlizar la táctica `ext` en metas de ese tipo. -/
/- Cuál es el tipo de `R3`? -/
--#check R3

/- Hay varias formas de crear una instancia de `R3`? -/

/- Si no sabemos qué campos debemos proporcionar para crear una instancia de una
estructura, podemos reemplazar el sorry por `{!}`, pulsar en la bombilla, y seleccionar
la opción "Generate a skeleton for the structure under construction".-/ 
def R3_ex : R3 :=
sorry

-- Esta sintaxis también nos permite especificar los argumentos en otro orden.
--#check ({x := 1, z := 3,  y := 2,} : R3)

-- El constructor por defecto se llama `R3.mk`. 
--#check R3.mk 1 2 3

-- Podemos utilizar la sintaxis de constructor anónimo.
--#check (⟨1, 2, 3⟩ : R3)

/- Dos instancias de `R3` son iguales cuando todas sus componentes coinciden. -/

example (a b : R3) (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) : a = b :=
begin
  ext,
  exacts [hx, hy, hz], -- esta sintaxis nos permite cerrar las 3 metas a la vez.
end


/- Dada una instancia de `R3`, podemos acceder a cada una de las coordenadas: -/

def v : R3 := ⟨1, 2, 3⟩
--#check R3.x
--#check v.z


/- Las estructuras también pueden tener campos proposicionales. -/

@[ext] structure R3_plus :=
(x y z : ℝ)
(x_pos : x > 0)
(y_pos : y > 0)
(z_pos : z > 0)

--#check R3_plus.mk

/- Cuándo son dos términos de tipo `R3_plus` iguales? -/

example (a b : R3_plus) (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) : a = b :=
begin
  ext,
  exacts [hx, hy, hz],
end

/- Por último, también es posible crear estructuras con parámetros. -/

/-- Definimos ℝ^n, donde `n` es un número natural -/
structure Rn (n : ℕ) :=
(coeff : fin n → ℝ)

--variables (n :  ℕ)
--#check Rn n

--#check Rn.mk
--#check Rn.mk (λ (k : fin 5), k)
--def ex : Rn 5 := ⟨(λ k, k)⟩ 

/-- La siguiente definición es distinta: incluye n-tuplas de números reales para cualquier `n`. -/
structure Rn' :=
(n : ℕ)
(coeff : fin n → ℝ)

--#check Rn'.mk 5 (λ k, k)


/-!
## Ejercicios de creación de estructuras
En los siguientes ejercicios, se pide crear una estructura en Lean para representar cada uno de
los objetos matemáticos descritos. Las soluciones propuestas no siempre son únicas, pregunta si
tienes dudas sobre si tu solución es correcta.
-/

/- 
Crea un tipo `even_natural_number`, compuesto por pares cuya primera componente es un número
natural y la segunda una demostración de que el número es par.
-/
structure even_natural_number : Type :=
(n : ℕ)
(even_n : even n)


/- Define una estructura de secuencias `ℕ → ℕ` eventualmente constantes. El primer campo de la
estructura será una secuencia `seq : ℕ → ℕ`, y el segundo el enunciado de que `seq` satisface
la propiedad deseada. -/
structure event_const_seq :=
(seq : ℕ → ℕ)
(event_const : ∃ N : ℕ, ∀ n ≥ N, seq n = seq N)

/- Define una estructura cuyos términos sean dos números naturales distintos. -/
structure two_distinct_points :=
(x : ℕ)
(y : ℕ)
(x_ne_y : x ≠ y)

/- Define una estructura de grupo multiplicativo sobre un tipo `G`. Para ello, necesitarás campos
de datos para indicar las operaciones y el elemento identidad, y campos proposicionales para 
establecer los axiomas deseados.
-/
structure Group (G : Type*) :=
(one : G)
(mul : G → G → G)
(inv : G → G)
(mul_assoc : ∀ (x y z : G), mul (mul x y) z = mul x (mul y z)) --∀ x y z, (x*y)*z = x*(y*z)
(one_mul : ∀ (x : G), mul one x = x) --∀ x, 1*x = x
(inv_mul_self : ∀ (x : G), mul (inv x) x = one) -- --∀ x, x⁻¹ * x = 1