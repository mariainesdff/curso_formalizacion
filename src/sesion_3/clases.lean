/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : María Inés de Frutos-Fernández
-/

import data.real.basic -- Importamos los números reales.

/-!
Algunos de estos ejemplos se han adaptado de la charla de estructuras y classes de LftCM 2022:
<https://icerm.brown.edu/video_archive/?play=2897>
-/


noncomputable theory 

/-! # Clases

Referencia : Theorem Proving in Lean.

Cualquier estructura en Lean se puede marcar como una *clase de tipos*.
Podemos declarar *instancias* de una clase.
Cuando el elaborador está buscando un elemento de una clase, puede consultar una tabla con las 
instancias declaradas para encontrar un elemento apropiado.
-/

/-! ## Variables -/

--En Lean, podemos usar distintos tipos de variables
variable (r : ℝ) -- variable explícita.
variable {n : ℕ} -- variable implícita. Para argumentos que se pueden inferir a partir de otros.
variable (G : Type*)
variable [group G] -- argumentos entre `[ ]` son inferidos por el mecanismo de inferencia de clases.

/- Las variables que acabamos de declarar estarán visibles hasta el final del fichero. No es posible
tener dos variables visibles con el mismo nombre. 

Podemos modificar este comportamiento utilizando secciones:
-/
section ejemplo
variable (a : ℕ)
--variable (a : ℝ) -- da error
end ejemplo

variable (a : ℕ)

-- Ejemplos
lemma nat.add_pos (n m : ℕ) (hm : 0 < m) : 
  0 < n + m :=
sorry

lemma nat.add_pos' (n : ℕ) {m : ℕ} (hm : 0 < m) : 
  0 < n + m :=
sorry

example (n m : ℕ) (hm : 0 < m) : 
  0 < m + n :=
begin
  rw add_comm, -- ¿por qué funciona esto?
  sorry
  --exact nat.add_pos n m hm,
  --exact nat.add_pos n _ hm, -- Lean puede deducir m a partir de hm
  --exact nat.add_pos' n hm -- con la segunda variante, la barra _ no es necesara.
end

/- ¿Por qué hemos podido utilizar `add_comm` en el ejemplo anterior?
  `add_comm` es un teorema sobre semigrupos aditivos conmutativos.
  Lean ha encontrado automáticamente la estructura de semigrupo de `ℕ`, mediante un proceso
  llamado *inferencia de clases*. -/

/- Cualquier estructura en Lean se puede marcar como una *clase de tipos*. Por ejemplo,
  `add_group` es la clase de grupos aditivos. -/
--#check add_group

/- Podemos declarar *instancias* de una clase. Por ejemplo, la estructura de grupo aditivo de `ℤ`
está registrada en la instancia `int.add_group`. -/
--#check int.add_group

/-Cuando el elaborador está buscando un elemento de una clase, puede consultar una tabla con las 
instancias declaradas para encontrar un elemento apropiado. -/
--#check add_comm -- tiene un argumento [add_comm_semigroup G]

/- En Lean utilizamos clases para registrar estructuras algebraicas, topológicas, analíticas, ... -/

-- Ejemplo: Podemos crear una clase para indicar que un tipo es no vacío.
class no_vacio (A : Type) : Prop :=
(has_val : ∃ x : A, true)

instance : no_vacio ℤ :=
{ has_val := ⟨0, trivial⟩ }

instance {A B : Type} [ha : no_vacio A] [hb : no_vacio B] :
  no_vacio (A × B) :=
begin
  cases ha.has_val with a _,
  cases hb.has_val with b _,
  apply no_vacio.mk,
  use (a, b)
end

-- Ejemplo
instance producto_de_grupos {G H : Type*} [group G] [group H] : group (G × H) := infer_instance


