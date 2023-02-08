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
  refl,
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
  intros a ha,
  apply hYZ,
  exact hXY a ha,
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
  split,
  { apply hXY },
  { apply hYX }
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
  ext x,
  rw union_def,
  /- Podríamos terminar con `rw or_self`, pero para practicar con otras prácticas, hagamos : -/
  split; -- Al terminar con `;`, la siguiente táctica se aplica a todas las metas.
  intro hX,
  { cases hX with hX hX;
    exact hX, },
  { left,
    exact hX }
end

lemma subset_union_left : X ⊆ X ∪ Y :=
begin
  intros x hx,
  rw union_def,
  left,
  exact hx,
end

lemma subset_union_right : Y ⊆ X ∪ Y :=
begin
  intros y hy,
  right,
  assumption,
end

lemma union_subset_iff : X ∪ Y ⊆ Z ↔ X ⊆ Z ∧ Y ⊆ Z :=
begin
  split,
  { intro h,
    split,
    { intros x hx,
      apply h,
      exact subset_union_left Ω X Y hx },
    { intros y hy,
      apply h,
      right,
      assumption }},
  { rintros ⟨hXZ, hYZ⟩ a (haX | haY),
    { exact hXZ haX },
    { exact hYZ haY }}
end

variable (W : set Ω)

lemma union_subset_union (hWX : W ⊆ X) (hYZ : Y ⊆ Z) : W ∪ Y ⊆ X ∪ Z :=
begin
  rintros a (haW | haY),
  { left,
    exact hWX haW },
  { right,
    exact hYZ haY }
end

lemma union_subset_union_left (hXY : X ⊆ Y) : X ∪ Z ⊆ Y ∪ Z :=
begin
  apply union_subset_union,
  { exact hXY },
  { exact subset_refl Ω Z },
end

/- Intersecciones -/

lemma inter_subset_left : X ∩ Y ⊆ X :=
begin
  rintros x ⟨hxX, hxY⟩,
  exact hxX,
end

lemma inter_self : X ∩ X = X :=
begin
  ext x,
  split,
  { rintro ⟨hx, -⟩,
    exact hx, },
  { intro hx,
    exact ⟨hx, hx⟩ }
end

lemma inter_comm : X ∩ Y = Y ∩ X :=
begin
  ext,
  split,
  { rintro ⟨hX, hY⟩,
    exact ⟨hY, hX⟩, },
  { rintro ⟨hY, hX⟩,
    exact ⟨hX, hY⟩ }
end

lemma inter_assoc : X ∩ (Y ∩ Z) = (X ∩ Y) ∩ Z :=
begin
  ext,
  split,
  { rintro ⟨hX, ⟨hY, hZ⟩⟩, 
    exact ⟨⟨hX, hY⟩, hZ⟩ },
  { rintro ⟨⟨hX, hY⟩, hZ⟩,
    exact ⟨hX, ⟨hY, hZ⟩⟩ },
end

/-!

### Para todo y existe

-/

lemma not_exists_iff_forall_not : ¬ (∃ a, a ∈ X) ↔ ∀ b, ¬ (b ∈ X) :=
begin
  split,
  { intros hX b hb,
    apply hX,
    use [b, hb], },
  { intros h1 h2,
    cases h2 with b hb,
    exact h1 b hb },
end

example : ¬ (∀ a, a ∈ X) ↔ ∃ b, ¬ (b ∈ X) :=
begin
  split,
  { intro hX,
    by_contra hnX,
    apply hX,
    intro a,
    by_contra ha,
    apply hnX,
    use a, },
  { rintro ⟨b, hb⟩ hX,
    exact hb (hX b), }
end

end conjuntos