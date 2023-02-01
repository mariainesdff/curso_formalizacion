/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : María Inés de Frutos-Fernández
-/

import tactic -- importa todas las tácticas de Lean

/-!
# Lógica proposicional en Lean

`P : Prop` significa que `P` es una proposición. 
`h : P` significa que `h` es una demostración de que `P` es cierta.

En el apartado `Tactic state` de la ventana `Lean infoview`, detrás del símbolo `⊢` se muestra
el resultado que queremos demostrar. Encima de dicha línea tenemos las hipótesis activas.

Lean 3 utiliza la siguente notación para las conectivas lógicas:
* `→` ("implica" -- escrito `\l`)
* `¬` ("no" -- escrito  `\not` o `\n`)
* `∧` ("y" -- escrito  `\and` o `\an`)
* `↔` ("si y sólo si" -- escrito  `\iff` o `\lr`)
* `∨` ("o" -- escrito  `\or` o `\v`

NOTA: en VSCode, para saber cómo se ha escrito un símbolo UNICODE, basta dejar el cursor
sobre él.

# Tácticas
Para completar los ejercicios, será necesario utlizar las siguientes tácticas de Lean, cuyo 
funcionamiento se describe en el fichero `tacticas.lean`. Los ejercicios de la primera sección
pueden resolverse utilizando exclusivamente `intro`, `exact`, y `apply`. En los comentarios al
inicio de cada sección se indica qué nuevas tácticas son necesarias.

* `intro`
* `exact`
* `apply`
* `triv`
* `exfalso`
* `change`
* `by_contra`
* `cases`
* `split`
* `refl`
* `rw`
* `have`
* `left`
* `right`

-/ 

-- `P`, `Q`, `R` y `S` denotan proposiciones.
variables (P Q R S : Prop)

/- Convención: utilizaremos variables cuyo nombre comienza por with `h` (como `hP` or `h1`) para
demostraciones o hipótesis. -/


/-
## Implicación
La táctica `sorry` se utiliza para evitar el error que de otro modo produce Lean cuando no 
aportamos la demostración de un resultado.

En los ejemplos siguientes, reemplaza el `sorry` por una demostración que utilice las tácticas
`intro`, `exact` y `apply`. Recuerda añadir una coma al final de cada instrucción.
-/
section implicacion


/-- Toda proposición se sigue de sí misma -/
example : P → P :=
begin
  intro hP,
  exact hP
end

/- NOTA: La convención en Lean es que `P → Q → R` significa `P → (Q → R)` (es decir, los
paréntesis implícitos asocian por la derecha).

En particular, en este ejemplo se nos pide demostrar `P → (Q → P)`.

Como consejo general, si no estamos seguros de si una cierta operación se está asociando por la
derecha o por la izquierda, podemos consultarlo pasando el cursor sobre la línea correspondiente
en el `Tactic state`.
-/
example : P → Q → P :=
begin
  intro hP,
  intro hQ,
  exact hP,
end

/-- "Modus Ponens": dado `P` y `P → Q`, podemos deducir `Q`. -/
lemma modus_ponens : P → (P → Q) → Q :=
begin
  intro hP,
  intro hPQ,
  apply hPQ,
  exact hP,
end

/-- `→` es transitiva. Es decir, si `P → Q` y `Q → R` son verdaderas, `P → R` también. -/
example : (P → Q) → (Q → R) → (P → R) :=
begin
  intro hPQ,
  intro hQR,
  intro hP,
  apply hQR,
  apply hPQ,
  exact hP,
end

example : (P → Q → R) → (P → Q) → (P → R) :=
begin
  intros hPQR hPQ hP,
  apply hPQR,
  { exact hP },
  { apply hPQ,
    exact hP }
  
end

/- 
Termina los ejemplos de esta sección si quieres más práctica con `intro`, `exact` y `apply`; de lo
contrario, puedes pasar a la sección `verdadero_falso`.
-/

example : (P → Q) → ((P → Q) → P) → Q :=
begin
  intros hPQ h,
  apply hPQ,
  apply h,
  exact hPQ,
end

example : ((P → Q) → R) → ((Q → R) → P) → ((R → P) → Q) → P :=
begin
  intros h1 h2 h3,
  apply h2,
  intro hQ,
  apply h1,
  intro hP,
  exact hQ
end

example : ((Q → P) → P) → (Q → R) → (R → P) → P :=
begin
  intros h hQR hRP,
  apply h,
  intro hQ,
  apply hRP,
  exact hQR hQ,
end

example : (((P → Q) → Q) → Q) → (P → Q) :=
begin
  intros h hP,
  apply h,
  intros hPQ,
  exact hPQ hP,
end

example :
  (((P → Q → Q) → ((P → Q) → Q)) → R) →
  ((((P → P) → Q) → (P → P → Q)) → R) →
  (((P → P → Q) → ((P → P) → Q)) → R) → R :=
begin
  intros h1 h2 h3,
  apply h2,
  intros h4 hP h5,
  apply h4,
  intro hP,
  exact h5,
end

end implicacion

section verdadero_falso

/-!
# Verdadero y falso
Introducimos dos nuevas tácticas:
* `triv`: demuestra `⊢ true`.
* `exfalso`: sustituye el resultado a probar por `false`.
-/
example : true :=
begin
  triv,
end

example : true → true :=
begin
  intro h,
  triv
end

example : false → true :=
begin
  intro h,
  triv
end

example : false → false :=
begin
  intro h,
  exact h,
end

example : (true → false) → false :=
begin
  intro h,
  apply h,
  triv,
end

example : false → P :=
begin
  intro h,
  exfalso,
  exact h,
end

example : true → false → true → false → true → false :=
begin
  intros h1 h2 h3 h4 h5,
  exact h2,
end

example : P → ((P → false) → false) :=
begin
  intros hP h,
  exact h hP,
end

example : (P → false) → P → Q :=
begin
  intros h hP,
  exfalso,
  exact h hP,
end

example : (true → false) → P :=
begin
  intros h,
  exfalso,
  apply h,
  triv,
end


end verdadero_falso


section negacion

/-!
# Negación
En Lean, `¬ P` *está definido como* `P → false`. Por tanto, `¬ P` y `P → false`
son *iguales por definición* (hablaremos de esto más adelante en el curso). 

Las siguientes tácticas podrían ser útiles en esta sección:
* `change`
* `by_contra`
-/


example : ¬ true → false :=
begin
  intro h,
  change true → false at h, -- Esta línea no es necesaria para la demostración
  apply h,
  triv,
end

example : false → ¬ true :=
begin
  intros hf ht,
  exact hf,
end

example : ¬ false → true :=
begin
  intro h,
  triv,
end

example : true → ¬ false :=
begin
  intros ht hf,
  exact hf,
end

example : false → ¬ P :=
begin
  intros hf hP,
  exact hf,
end

example : P → ¬ P → false :=
begin
  intros hP hnP,
  exact hnP hP,
end

example : P → ¬ (¬ P) :=
begin
  intros hP hnP,
  exact hnP hP,
end

example : (P → Q) → (¬ Q → ¬ P) :=
begin
  intros hPQ hnQ hP,
  apply hnQ,
  apply hPQ,
  exact hP,
end

example : ¬ ¬ false → false :=
begin
  intros h,
  apply h,
  intros h1,
  exact h1,
end

example : ¬ ¬ P → P :=
begin
  intros h,
  by_contra hnP,
  apply h,
  exact hnP,
end

example : (¬ Q → ¬ P) → (P → Q) :=
begin
  intros h hP,
  by_contra hnQ,
  apply h,
  { exact hnQ },
  { exact hP }
end


end negacion


section conjuncion

/-!
# Conjunción
Añadimos las tácticas:
* `cases`
* `split`
-/

example : P ∧ Q → P :=
begin
  intros hPQ,
  cases hPQ with hP hQ,
  exact hP,
end

example : P ∧ Q → Q :=
begin
  intros hPQ,
  cases hPQ with hP hQ,
  exact hQ,
end

example : (P → Q → R) → (P ∧ Q → R) :=
begin
  intros h hPQ,
  cases hPQ with hP hQ,
  exact h hP hQ,
end

example : P → Q → P ∧ Q :=
begin
  intros hP hQ,
  split,
  exact hP,
  exact hQ,
end

/-- `∧` es simétrica. -/
example : P ∧ Q → Q ∧ P :=
begin
  rintro ⟨hP, hQ⟩,
  exact ⟨hQ, hP⟩,
end

example : P → P ∧ true :=
begin
  intros hP,
  split,
  { exact hP },
  { triv },
end

example : false → P ∧ false :=
begin
  intros h,
  split,
  { exfalso,
    exact h },
  { exact h },
end

/-- `∧` es transitiva. -/
example : (P ∧ Q) → (Q ∧ R) → (P ∧ R) :=
begin
  rintros ⟨hP, hQ⟩ ⟨-, hR⟩,
  exact ⟨hP, hR⟩,
end

example : ((P ∧ Q) → R) → (P → Q → R) :=
begin
  intros h hP hQ,
  exact h ⟨hP, hQ⟩,
end

end conjuncion

section doble_implicacion

/-!
# Doble implicación
Nuevas tácticas:
* `refl`
* `rw`
* `have`
-/

example : P ↔ P :=
begin
  refl,
end

example : (P ↔ Q) → (Q ↔ P) :=
begin
  intro h,
  rw h,
end

example : (P ↔ Q) ↔ (Q ↔ P) :=
begin
  /- Si terminamos la línea con `;`, la siguiente instrucción se aplica a todas 
    las metas abiertas. -/
  split;
  { intro h, rw h },
end

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
begin
  intros hPQ hQR,
  rw hPQ,
  exact hQR,
end

example : P ∧ Q ↔ Q ∧ P :=
begin
  split;
  { rintro ⟨h1, h2⟩,
    exact ⟨h2, h1⟩ }
end

example : ((P ∧ Q) ∧ R) ↔ (P ∧ (Q ∧ R)) :=
begin
  split,
  { rintros ⟨⟨hP, hQ⟩, hR⟩,
    exact ⟨hP, ⟨hQ, hR⟩⟩ },
  { rintros ⟨hP, ⟨hQ, hR⟩⟩,
    exact ⟨⟨hP, hQ⟩, hR⟩ }
end

example : P ↔ (P ∧ true) :=
begin
  split,
  { intro hP,
    split,
    { exact hP },
    { triv }},
  { rintros ⟨h, -⟩,
    exact h }
end

example : false ↔ (P ∧ false) :=
begin
  split,
  { intro h,
    exfalso,
    exact h },
  { rintro ⟨-, h⟩,
    exact h }
end

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) :=
begin
  intros hPQ hRS,
  rw hPQ,
  rw hRS,
end

/- Una forma de demostrar este teorema es utilizando `by_cases hP : P`. Sin embargo, también es
posible dar una demostración constructiva, utilizando la táctica `have`. -/
example : ¬ (P ↔ ¬ P) :=
begin
  intro h,
  by_cases hP : P,
  { cases h with h1 h2,
    apply h1;
    exact hP, },
  { apply hP,
    rw h,
    exact hP, }
end

-- Demostración constructiva
example : ¬ (P ↔ ¬ P) :=
begin
  intro h,
  cases h with h1 h2,
  have hP : P,
  { apply h2,
    intro hP,
    exact (h1 hP) hP, },
  have hnP : ¬ P,
  { exact h1 hP, },
  exact hnP hP,
end

end doble_implicacion


section disyuncion

/-!
# Disyunción
Nuevas tácticas
* `left` y `right`
* `cases` (nueva funcionalidad)
-/


example : P → P ∨ Q :=
begin
  intros hP,
  left,
  exact hP,
end

example : Q → P ∨ Q :=
begin
  intros hQ,
  right,
  exact hQ,
end

example : P ∨ Q → (P → R) → (Q → R) → R :=
begin
  intros h1 h2 h3,
  cases h1 with hP hQ,
  { exact h2 hP },
  { exact h3 hQ },
end

/- `∨` es simétrica -/
example : P ∨ Q → Q ∨ P :=
begin
  intros h,
  cases h with hP hQ,
  { right, 
    exact hP },
  { left,
    exact hQ },
end

/- `∨` es asociativa -/
example : (P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R) :=
begin
  split,
  { rintros (( hP | hQ) | hR),
    { left, exact hP },
    { right, left, exact hQ },
    { right, right, exact hR }},
  { rintros (hP | (hQ | hR)),
    { left, left, exact hP },
    { left, right, exact hQ },
    { right, exact hR }}
end

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S :=
begin
  rintros h1 h2 (hP | hQ),
  { left, exact h1 hP, },
  { right, exact h2 hQ, }
end

example : (P → Q) → P ∨ R → Q ∨ R :=
begin
  rintros h (hP | hR),
  { left, exact h hP },
  { right, exact hR },
end

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) :=
begin
  intros h1 h2,
  rw h1,
  rw h2,
end

-- Leyes de de Morgan.
example : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q :=
begin
  split,
  { intro h,
    split,
    { intro hP,
      apply h,
      left, 
      exact hP },
    { intro hQ,
      apply h,
      right,
      exact hQ } },
  { rintro ⟨hnP, hnQ⟩ (hP | hQ),
    { apply hnP, exact hP },
    { exact hnQ hQ }}
end

example : ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
  split,
  { intro h,
    by_cases hP : P,
    { right,
      intro hQ,
      apply h,
      exact ⟨hP, hQ⟩ },
    { left,
      exact hP } },
  { rintro (hnP | hnQ) ⟨hP, hQ⟩,
    { contradiction },
    { apply hnQ, exact hQ }}
end


end disyuncion

