/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : María Inés de Frutos-Fernández
-/

import tactic -- importa todas las tácticas de Lean

/-!

# Tácticas
En este fichero describimos el funcionamiento de las siguientes tácticas de Lean y proporcionamos
ejemplos de uso de las mismas.
* `sorry`
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
* `by_cases`


CONSEJO: Aprovecha la interactividad de Lean. Dentro de una demostración delimitada por `begin` y
`end`, pulsando al final de cada línea podemos ver en la ventana derecha el estado actual de la 
demostración.
-/ 

/- # Tácticas -/

--  `P`, `Q` y `R` denotan proposiciones.
variables (P Q R : Prop)

/- ## sorry 
  `sorry` se puede utilizar para cerrar cualquier meta. Genera un aviso de que dicha meta no ha
  sido cerrada, que aparece en la sección "All Messages" del "Lean infoview". El número total de
  warnings aparece en la parte inferior de la pantalla.
-/

example (P NP : Prop) : P = NP := 
begin
  sorry
end 


/- ## exact 

Si queremos demostrar una meta `P` y tenemos disponible la hipótesis `hP : P`, podemos cerrar la
meta utilizando la táctica `exact hP`

NOTA: `exact P` no funciona en esta situación (no debemos confundir la proposición `P` con su
demostración `hP`).  -/

example (hP : P) (hQ : Q) : P :=
begin
  exact hP,
end

/-  ## intro

Dada la meta `P → Q`, la táctica `intro hP` introduce una hipótesis local `hP : P` y cambia la meta
a `Q`.

VARIANTE: `intros` puede utilizarse para introducir varias hipótesis en una misma línea. -/

example (hQ : Q) : P → Q :=
begin
  intro hP,
  exact hQ,
end

example : Q → P → Q :=
begin
  intros hQ hP,
  exact hQ,
end

/- ## apply

La táctica `apply` se utiliza para razonar hacia atrás. Por ejemplo, si el estado táctico es

hPQ : P → Q
⊢ Q,

tras utilizar `apply hPQ` el estado cambiará a

hPQ : P → Q
⊢ P.

Es decir, la demostración de `Q` se reduce a demostrar `P` y las hipótesis activas no se modifican.

En general, `apply h` intenta unificar la meta actual con la conclusión del término `h`. Si tiene
éxito, la meta es reemplazada por una o varias metas (tantas como premisas tenga `h`).
 -/

example (h : P → Q) (hP : P) : Q :=
begin
  apply h,
  exact hP,
end

-- En este ejemplo, `apply` genera dos submetas
example (hP : P) (hQ : Q) (h : P → Q → Q)  : Q :=
begin
  apply h,
  /- RECOMENDACIÓN DE ESTILO: cuando la aplicación de una táctica introduce nuevas submetas, es
    recomendable englobar la demostración de cada una entre llaves `{ }`. -/
  { exact hP }, 
  { exact hQ }
end

/- ## triv 
La táctica `triv` demuestra `⊢ true`.
-/

example : true :=
begin
  triv,
end

/- ## exfalso 
La táctica `exfalso` cambia cualquier meta a `false`.
-/

example (hP : P) (h : P → false) : Q := 
begin
  exfalso,
  apply h,
  exact hP
end

/- ## change 
La táctica `change` permite reemplazar una meta `⊢ P` por otra `⊢ Q`, siempre que `P` y `Q` sean
definicionalmente iguales. También puede utilizarse en hipótesis: `change Q at h` reemplaza `h : P`
por `h : Q`. 
-/

example (hPQ : ¬ P ↔ Q) (hQ : Q) : P → false :=
begin
  change ¬ P,  -- ¬ P está definido como P → false.
  rw hPQ,
  exact hQ,
end

example (hP : P) (hnP : ¬ P) : false :=
begin
  change P → false at hnP, -- ¬ P está definido como P → false.
  exact hnP hP,
end

/- ## by_contra
La táctica `by_contra` permite realizar demostraciones por reducción al absurdo. Si la meta es 
```
⊢ P
```

entonces la instrucción `by_contra h,`cambiará el "Tactic state" a

```
h : ¬P
⊢ false
```

-/


/- ## cases

`cases` es una táctica de propósito general para deconstruir hipótesis. Aquí presentamos dos de los
casos de uso más básicos; veremos otros a medida que avance el curso.

### Ejemplos

1) Si tenemos como hipótesis una conjunción `hPaQ : P ∧ Q`, la instrucción `cases hPaQ with hP hQ,`
eliminará `hPaQ` y la reemplazará por las dos hipótesis
```
hP : P
hQ : Q
```

2) Dada la hipótesis `hPiQ : P ↔ Q`, `cases hPiQ with hPQ hQP,`
reemplazará `hPiQ` por las dos hipótesis.
```
hPQ : P → Q
hQP : Q → P
```

Por otro lado, como veremos más abajo también podemos utilizar la táctica `rw h` con hipótesis
de la forma `h : P ↔ Q`, y habrá que valorar cuál de las dos tácticas es más útil en cada
situación.

-/

/- ## split

Si la meta actual es una conjunción `⊢ P ∧ Q`, podemos utilizar la táctica `split` para dividirla
en las dos metas `⊢ P` y `⊢ Q`. 

Tras usar `split`, la recomendación de estilo es utilizar llaves `{ }` para delimitar la 
demostración de cada una de las nuevas metas.

```
split,
{ demostración de P },
{ demostración de Q },
```

Similarmente, `split,` transforma la meta `⊢ P ↔ Q` en dos metas `⊢ P → Q` y `⊢ Q → P`.

-/

/- ## refl 
La táctica `refl` cierra metas de la forma `⊢ P = Q` donde `P` y `Q` son iguales por definición.
También demuestra metas de la forma `R x y`, donde `x` e `y` son definicionalmente iguales y `R` es
una relación binaria reflexiva . -/

example : ¬ P ↔ P → false :=
begin
  refl,
end

/- ## rw

Dada una hipótesis `h : P = Q`, podemos utilizar `rw h` para sustituir todas las apariciones de `P`
por `Q` en la meta. La táctica también puede utilizarse cuando `h` es una equivalencia lógica en 
lugar de una igualdad. El argumento `h` puede ser tanto una hipótesis local como un teorema.

NOTAS:

1) Si queremos utilizar `h : P = Q` para sustituir `Q` por `P`, la sintáxis es `rw ← h`. Esta flecha
a la izquierda se puede obtener escribiendo `\l`.

2) `rw` sólo funciona con hipótesis de la forma `a = b` o `P ↔ Q`, pero no con implicaciones `P → Q`.
(en dicho caso, utilizaríamos la táctica `apply`).

3) `rw` se puede utilizar en hipótesis, utilizando la palabra clave `at`.

AVISO: Antes de terminar, `rw` invoca la táctica `refl`.
-/

example (a b : ℕ) (hab : a = b) (hb : b + 1 = 3) : a + 1 = 3 := 
begin
  rw hab,
  exact hb
end

example (h1 : P ↔ Q) (h2 : Q → R) : P → R :=
begin
  rw h1,
  exact h2,
end

example (hQ : ¬ Q) : ¬(P ∧ Q)  := 
begin
  -- `not_and` es una demostración de la equivalencia `¬(P ∧ Q) ↔ (P → ¬Q)`.
  rw not_and,
  intro hP,
  exact hQ,
end

example (hP : ¬P) (hPQ : P = Q) : ¬ Q :=
begin
  rw ← hPQ,
  exact hP,
end

example (h1 : P ↔ Q) (h2 : P → R) : Q → R :=
begin
  rw h1 at h2,
  exact h2,
end

/- ## have

La táctica `have` se utiliza para introducir una nueva hipótesis dentro del estado táctico (que
tendremos que demostrar a partir de las hipótesis existentes).

Para utilizarla, escribimos: 
  have h : t,
  { p },
donde `h` es el nombre que queremos dar a la hipótesis, `t` es la hipótesis a demostrar y `p` 
una demostración de la misma. -/

example : (P → Q) → (¬ Q → ¬ P) :=
begin
  intros hPQ hnQ hP,
  have hQ : Q,     -- introducimos la hipótesis, que aparece como meta en el estado táctico
  {exact hPQ hP }, -- demostramos la hipótesis
  exact hnQ hQ,    -- la utilizamos para cerrar la meta principal
end

/- ## left 

La táctica `left` convierte la meta `⊢ P ∨ Q` en `⊢ P`. -/

example (hP : P) : P ∨ Q :=
begin
  left,
  exact hP,
end

/- ## right 

La táctica `right` convierte la meta `⊢ P ∨ Q` en `⊢ Q`. -/

example (hQ : Q) : P ∨ Q :=
begin
  right,
  exact hQ,
end

/-

## by_cases

Dada una proposición `P`, la táctica `by_cases h : P` divide la demostración de la meta en dos
casos: uno asumiento `h : P` y otro asumiendo `h : ¬P`.
-/

example : P ∨ ¬ P :=
begin
by_cases hP : P,
{ left, exact hP },
{ right, exact hP },
end
