/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : María Inés de Frutos-Fernández
-/

import topology.continuous_function.compact -- funciones continuas, conjuntos compactos

/-!

# Ejercicio
En este fichero el objetivo es demostrar que si `f : X → Y`
es una función continua y `S : set X` es un conjunto compacto,
entonces su imagen `f '' S : set Y` también es compacta. 

Un lema útil para esta demostración es

* `continuous.is_open_preimage` : la preimagen de un abierto bajo
una función continua es un abierto.
-/

-- Fijamos espacios topológicos X e Y 
variables (X Y : Type) [topological_space X] [topological_space Y]

-- S es un subconjunto de X
variable (S : set X)

-- `f : X → Y` es una función
variables (f : X → Y) 

-- Si f es continua y S es compacto,  la imagen f(S) también es un conjunto compacto.
example (hf : continuous f) (hS : is_compact S) : is_compact (f '' S) :=
begin
  rw is_compact_iff_finite_subcover at hS ⊢,
  sorry
end




