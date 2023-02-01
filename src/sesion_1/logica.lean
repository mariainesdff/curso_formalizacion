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
  sorry
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
  sorry
end

/-- "Modus Ponens": dado `P` y `P → Q`, podemos deducir `Q`. -/
lemma modus_ponens : P → (P → Q) → Q :=
begin
  sorry
end

/-- `→` es transitiva. Es decir, si `P → Q` y `Q → R` son verdaderas, `P → R` también. -/
example : (P → Q) → (Q → R) → (P → R) :=
begin
  sorry,
end

example : (P → Q → R) → (P → Q) → (P → R) :=
begin
  sorry
end

/- 
Termina los ejemplos de esta sección si quieres más práctica con `intro`, `exact` y `apply`; de lo
contrario, puedes pasar a la sección `verdadero_falso`.
-/

example : (P → Q) → ((P → Q) → P) → Q :=
begin
  sorry
end

example : ((P → Q) → R) → ((Q → R) → P) → ((R → P) → Q) → P :=
begin
  sorry
end

example : ((Q → P) → P) → (Q → R) → (R → P) → P :=
begin
  sorry
end

example : (((P → Q) → Q) → Q) → (P → Q) :=
begin
  sorry
end

example :
  (((P → Q → Q) → ((P → Q) → Q)) → R) →
  ((((P → P) → Q) → (P → P → Q)) → R) →
  (((P → P → Q) → ((P → P) → Q)) → R) → R :=
begin
  sorry
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
  sorry
end

example : true → true :=
begin
  sorry
end

example : false → true :=
begin
  sorry
end

example : false → false :=
begin
  sorry
end

example : (true → false) → false :=
begin
  sorry
end

example : false → P :=
begin
  sorry
end

example : true → false → true → false → true → false :=
begin
  sorry
end

example : P → ((P → false) → false) :=
begin
  sorry
end

example : (P → false) → P → Q :=
begin
  sorry
end

example : (true → false) → P :=
begin
  sorry
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
  sorry
end

example : false → ¬ true :=
begin
  sorry
end

example : ¬ false → true :=
begin
  sorry
end

example : true → ¬ false :=
begin
  sorry
end

example : false → ¬ P :=
begin
  sorry
end

example : P → ¬ P → false :=
begin
  sorry
end

example : P → ¬ (¬ P) :=
begin
  sorry
end

example : (P → Q) → (¬ Q → ¬ P) :=
begin
  sorry
end

example : ¬ ¬ false → false :=
begin
  sorry
end

example : ¬ ¬ P → P :=
begin
  sorry
end

example : (¬ Q → ¬ P) → (P → Q) :=
begin
  sorry,
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
  sorry
end

example : P ∧ Q → Q :=
begin
  sorry
end

example : (P → Q → R) → (P ∧ Q → R) :=
begin
  sorry
end

example : P → Q → P ∧ Q :=
begin
  sorry
end

/-- `∧` es simétrica. -/
example : P ∧ Q → Q ∧ P :=
begin
  sorry
end

example : P → P ∧ true :=
begin
  sorry
end

example : false → P ∧ false :=
begin
  sorry
end

/-- `∧` es transitiva. -/
example : (P ∧ Q) → (Q ∧ R) → (P ∧ R) :=
begin
  sorry,
end

example : ((P ∧ Q) → R) → (P → Q → R) :=
begin
  sorry,
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
  sorry
end

example : (P ↔ Q) → (Q ↔ P) :=
begin
  sorry
end

example : (P ↔ Q) ↔ (Q ↔ P) :=
begin
  sorry
end

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
begin
  sorry
end

example : P ∧ Q ↔ Q ∧ P :=
begin
  sorry
end

example : ((P ∧ Q) ∧ R) ↔ (P ∧ (Q ∧ R)) :=
begin
  sorry
end

example : P ↔ (P ∧ true) :=
begin
  sorry
end

example : false ↔ (P ∧ false) :=
begin
  sorry
end

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) :=
begin
  sorry
end

/- Una forma de demostrar este teorema es utilizando `by_cases hP : P`. Sin embargo, también es
posible dar una demostración constructiva, utilizando la táctica `have`. -/
example : ¬ (P ↔ ¬ P) :=
begin
  sorry,
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
  sorry
end

example : Q → P ∨ Q :=
begin
  sorry,
end

example : P ∨ Q → (P → R) → (Q → R) → R :=
begin
  sorry
end

/- `∨` es simétrica. -/
example : P ∨ Q → Q ∨ P :=
begin
  sorry
end

/- `∨` es asociativa. -/
example : (P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R) :=
begin
  sorry,
end

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S :=
begin
  sorry,
end

example : (P → Q) → P ∨ R → Q ∨ R :=
begin
  sorry,
end

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) :=
begin
  sorry,
end

-- Leyes de de Morgan.
example : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q :=
begin
  sorry
end

example : ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
  sorry
end

end disyuncion

