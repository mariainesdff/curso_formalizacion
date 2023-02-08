/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : María Inés de Frutos-Fernández
-/

import tactic

/-!

# Funciones en Lean.

La notación para funciones es la habitual en matemáticas: dados dos tipos `X` e `Y`, `f : X → Y` 
denota una función de `X` a `Y`. 

Internamente, `X → Y` denota el tipo de funciones de `X` a `Y`, y `f : X → Y` indica que  `f` es un
término de tipo `X → Y`, es decir, una  función de `X` a `Y`. 


NOTACIÓN: dado `x : X` y `f : X → Y`, para denotar la evaluación  `f(x)` es posible omitir los 
paréntesis, escribiendo simplemente `f x`. Sin embargo, para expresiones más complicadas los 
paréntesis son necesarios. Por ejemplo, dados `x : X`, `f : X → Y` y `g : Y → Z`, para evaluar
la composición `g(f(x))` necesitamos al menos los paréntesis exteriores: `g(f x)`.


## Inyectividad y sobreyectividad

Lean conoce las definiciones de función injectiva (`function.injective`) y sobreyectiva 
(`function.surjective`). Dada cualquier función `f : X → Y`, `function.injective f`
y `function.surjective f` son proposiciones (verdaderas o falsas dependiendo de `f`).

-/

/- Si abrimos el `namespace` "function", no es necesario escribir `function.`; podemos escribir
`injective f` y `surjective f`. -/

open function

/- Fijamos tres tipos `X`, `Y`, `Z` (podemos pensar en ellos como conjuntos) y dos funciones 
`f : X → Y`, `g : Y → Z`. -/
variables {X Y Z : Type} {f : X → Y} {g : Y → Z}

/- Sean `a,b,x` elementos de `X`, `y ∈ Y`, `z ∈ Z`. -/
variables (a b x : X) (y : Y) (z : Z)

-- Abrimos un `namespace` propio para evitar colisiones de nomenclatura con lemas existentes.
namespace funciones

/-!
# Funciones inyectivas
-/

/- Comprobamos que en Lean la definición de función sobreyectiva es la esperada. -/
lemma injective_def : injective f ↔ ∀ a b : X, f a = f b → a = b :=
begin
  refl -- cierto por definición
end

-- La táctica `rw injective_def` cambia `injective f` por su definición.

/- Comprobamos que la función identidad ` id : X → X` está definida como `id(x) = x`. -/
lemma id_eval : id x = x :=
begin
  refl -- cierto por definición
end

-- La composición de funciones se denota mediante `∘`. Por definición, `(g ∘ f) (x) = g(f(x))`.
lemma comp_eval : (g ∘ f) x = g (f x) :=
begin
  refl
end

/- La razón por la que demostramos estos teoremas demostrables "por definición" (`refl`) es que
esto nos permite utilizar la táctica  `rw` para reemplazar términos por su definición. -/

/- Por ejemplo, podemos empezar la siguiente demostración con `rw injective_def`, y más adelante 
utilizar `rw id_eval`. -/
example : injective (id : X → X) :=
begin
  rw injective_def,
  sorry
end

/- Si eliminamos la instrucción  `rw injective_def`, nada cambia. El motivo es que esta instrucción
no es realmente necesaria para Lean (ya que sólo está reescribiendo una definición), pero puede
ser útil para la persona escribiendo la demostración. Prueba a hacer lo mismo con `rw id_eval`. -/

/-- La composición de dos funciones inyectivas es inyectiva. -/
lemma injective_comp (hf : injective f) (hg : injective g) : injective (g ∘ f) :=
begin
  sorry,
end

/- Ejercicio -/
example (f : X → Y) (g : Y → Z) : 
  injective (g ∘ f) → injective f :=
begin
  sorry
end


/-!

### Funciones sobreyectivas

-/

/- Comprobamos que en Lean la definición de función sobreyectiva es la esperada. -/
lemma surjective_def : surjective f ↔ ∀ y : Y, ∃ x : X, f x = y :=
begin
  refl
end

/-- La función identidad es sobreyectiva. -/
lemma surjective_id : surjective (id : X → X) :=
begin
  sorry,
end


/-- Una composición de funciones sobreyectivas es sobreyectiva. -/
lemma surjective_comp (hf : surjective f) (hg : surjective g) : surjective (g ∘ f) :=
begin
  sorry,
end

/- Ejercicio -/
example (f : X → Y) (g : Y → Z) : 
  surjective (g ∘ f) → surjective g :=
begin
  sorry
end

/-!
### Funciones biyectivas
-/

/- En Lean, una función biyectiva es, por definición, una función inyectiva y sobreyectiva. -/
lemma bijective_def : bijective f ↔ injective f ∧ surjective f :=
begin
  refl
end

/-- La función identidad es biyectiva. -/
lemma bijective_id : bijective (id : X → X) :=
begin
  sorry,
end

/-- Una composición de funciones biyectivas es biyectiva. -/
lemma bijective_comp (hf : bijective f) (hg : bijective g) : bijective (g ∘ f) :=
begin
  sorry,
end

end funciones