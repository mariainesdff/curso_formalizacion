/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : María Inés de Frutos-Fernández
-/

import tactic

/-!
# Conjuntos
-/

/- Definimos un tipo `Ω` y tres conjuntos `X`, `Y`, `Z` cuyos elementos son de tipo `Ω`.
  Para nuestro modelo mental, podemos pensar que estamos definiendo un conjunto `Ω` y tres 
  subconjuntos `X`, `Y`, `Z` del mismo.
  Definimos también elementos `a, b, c, x, y, z` de `Ω`.
 -/
variables (Ω : Type) (X Y Z : set Ω) (a b c x y z : Ω)

-- Abrimos un `namespace` para evitar conflictos con los nombres.
namespace conjuntos

/-!

# Subconjuntos

El símbolo `⊆` se escribe mediante `\sub` o `\ss`
-/

-- `X ⊆ Y` significa `∀ a, a ∈ X → a ∈ Y`, por definición.

lemma subset_def : X ⊆ Y ↔ ∀ a, a ∈ X → a ∈ Y :=
begin
  refl -- por definición
end

lemma subset_refl : X ⊆ X :=
begin
  sorry,
end

/- En este lema, tras empezar con `rw subset_def at *`, la hipótesis `hYZ` se transforma en
`hYZ : ∀ (a : Ω), a ∈ Y → a ∈ Z` (y similarmente para `hXY`).
Como `hYZ` es una implicación, una vez reducimos la meta a `a ∈ Z`, podemos avanzar en la 
demostración utilizando `apply hYZ`.
Frecuentemente, también es útil pensar en `hYZ` como una función, que dados un término `a` de
tipo `Ω` y una demostración `haY` de que `a ∈ Y`, devuelve una demostración `haZ` de `a ∈ Z`.
-/
lemma subset_trans (hXY : X ⊆ Y) (hYZ : Y ⊆ Z) : X ⊆ Z :=
begin
  rw subset_def at *,
  sorry
end

/-!

# Igualdad de conjuntos
Dos conjuntos son iguales si y sólo si tienen los mismos elementos.
En Lean, el nombre de este lema es `set.ext_iff`.
-/

example : X = Y ↔ (∀ a, a ∈ X ↔ a ∈ Y) :=
begin
  exact set.ext_iff
end

/- Cuando queremos reducir la meta `⊢ X = Y` a demostrar `a ∈ X ↔ a ∈ Y` para `a : Ω`
  arbitrario, utilizamos la táctica `ext`. -/

lemma subset.antisymm (hXY : X ⊆ Y) (hYX : Y ⊆ X) : X = Y :=
begin
  ext a,
  sorry
end

/-!

### Uniones e intersecciones

Notación: `\cup` o `\un` para obtener `∪`, y `\cap` o `\i` para `∩`

-/

lemma union_def : a ∈ X ∪ Y ↔ a ∈ X ∨ a ∈ Y :=
begin
  refl,
end

lemma inter_def : a ∈ X ∩ Y ↔ a ∈ X ∧ a ∈ Y :=
begin
  refl,
end

/- Uniones. -/

lemma union_self : X ∪ X = X :=
begin
  sorry
end

lemma subset_union_left : X ⊆ X ∪ Y :=
begin
  sorry
end

lemma subset_union_right : Y ⊆ X ∪ Y :=
begin
  sorry
end

lemma union_subset_iff : X ∪ Y ⊆ Z ↔ X ⊆ Z ∧ Y ⊆ Z :=
begin
  sorry
end

variable (W : set Ω)

lemma union_subset_union (hWX : W ⊆ X) (hYZ : Y ⊆ Z) : W ∪ Y ⊆ X ∪ Z :=
begin
  sorry
end

lemma union_subset_union_left (hXY : X ⊆ Y) : X ∪ Z ⊆ Y ∪ Z :=
begin
  sorry
end

/- Intersecciones -/

lemma inter_subset_left : X ∩ Y ⊆ X :=
begin
  sorry
end

lemma inter_self : X ∩ X = X :=
begin
  sorry
end

lemma inter_comm : X ∩ Y = Y ∩ X :=
begin
  sorry
end

lemma inter_assoc : X ∩ (Y ∩ Z) = (X ∩ Y) ∩ Z :=
begin
  sorry
end

/-!

### Para todo y existe

-/

lemma not_exists_iff_forall_not : ¬ (∃ a, a ∈ X) ↔ ∀ b, ¬ (b ∈ X) :=
begin
  sorry,
end

example : ¬ (∀ a, a ∈ X) ↔ ∃ b, ¬ (b ∈ X) :=
begin
  sorry,
end

end conjuntos