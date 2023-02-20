/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : María Inés de Frutos-Fernández
-/

import tactic
import group_theory.subgroup.basic -- importamos subgrupos de mathlib

/-!
# Subggrupos y homomorfismos

Para practicar el uso de lemas de la librería, crearemos nuestra propia definición de subgrupo,
y demostraremos lemas sobre ella utilizando la API de grupos de mathlib.

Después demostraremos lemas sobre homomorfismos de grupo (para ello, pasaremos a utilizar la 
definición de subgrupo disponible en mathlib). -/

/-- `subgrupo G` es el tipo de subgrupos de un grupo `G`. -/
@[ext] structure subgrupo (G : Type) [group G] :=
(carrier : set G) -- `carrier` es un subconjunto de `G`
(one_mem' : (1 : G) ∈ carrier) 
-- después añadiremos otra versión `one_mem` de este axioma sin nombrar el `carrier`
(mul_mem' {x y} : x ∈ carrier → y ∈ carrier → x * y ∈ carrier) -- también `mul_mem`
(inv_mem' {x} : x ∈ carrier → x⁻¹ ∈ carrier) -- también `inv_mem`

/- NOTA: no queremos que `subgrupo` sea una clase, ya que `G` puede tener múltiples subgrupos. -/

/- Gracias a la etiqueta `@[ext]`, la táctica `ext` funciona sobre subgrupos y nos permite 
  reemplazar una igualdad de subgrupos `H₁ = H₂` por `∀ g, g ∈ H₁ ↔ g ∈ H₂`. -/

namespace subgrupo

-- Sea G un grupo y H un subgrupo de G
variables {G : Type} [group G] (H : subgrupo G)

/-- Esta instancia nos permite hablar de elementos de un subgrupo, y utilizar la notación `x ∈ H`
  para ello. -/
instance : has_mem G (subgrupo G) :=
{ mem := λ m H, m ∈ H.carrier }

/-- Esta instancia nos permite interpretar un `H : subgrupo G` como un conjunto `H : set G`. -/
instance : has_coe (subgrupo G) (set G) := 
{ coe := λ H, H.carrier }

/-- `g` es un elemento de `H` considerado como suconjunto de `G`, si y sólo si `g` es un
elemento del sugrupo `H` de `G`. -/
@[simp] lemma mem_coe {g : G} : g ∈ (H : set G) ↔ g ∈ H :=
begin
  -- These two concepts just mean the same thing
  refl
end

/-- Añadimos otro lemma de extensionalidad: dos subgrupos de un grupo son iguales si tienen
  los mismos elementos.-/
@[ext] def ext' (H K : subgrupo G) (h : ∀ g : G, g ∈ H ↔ g ∈ K) : H = K :=
begin
  ext x,
  exact h x,
end

theorem one_mem : (1 : G) ∈ H :=
begin
  apply H.one_mem',
end

theorem mul_mem {x y : G} : x ∈ H → y ∈ H → x * y ∈ H :=
begin
  apply H.mul_mem',
end

theorem inv_mem {x : G} : x ∈ H → x⁻¹ ∈ H :=
begin
  apply H.inv_mem',
end

/- ## Ejercicios sobre subgrupos
En esta sección hay una lista de teoremas sobre subgrupos. Para demostrarlos, tendréis que 
usar los tres lemas anteriores, así como resultados sobre grupos disponibles en mathlib.

Si `H : subgrupo G`, y `x y : G`, los lemas anteriores dicen:
`H.one_mem : (1 : G) ∈ H`
`H.mul_mem : x ∈ H → y ∈ H → x * y ∈ H`
`H.inv_mem : x ∈ H → x⁻¹ ∈ H`
-/

@[simp] theorem inv_mem_iff {x : G} : x⁻¹ ∈ H ↔ x ∈ H := 
begin
  sorry
end

theorem mul_mem_cancel_left {x y : G} (hx : x ∈ H) :
  x * y ∈ H ↔ y ∈ H :=
begin
  sorry
end

theorem mul_mem_cancel_right {x y : G} (hx : x ∈ H) :
  y * x ∈ H ↔ y ∈ H :=
begin
  sorry
end

/-- `conjugate H g` es el subgrupo conjugado `gHg⁻¹` de `H`. -/
def conjugate (H : subgrupo G) (g : G) : subgrupo G :=
{ carrier := { a : G | ∃ h ∈ H, a = g * h * g⁻¹ },
  one_mem' := begin 
    simp only [exists_prop, set.mem_set_of_eq], 
    sorry
  end,
  inv_mem' := begin 
    sorry
  end,
  mul_mem' := begin 
    sorry
  end,
}

/-- Definición de abeliano. -/
def is_abelian (G : Type) [group G] : Prop :=
∀ a b : G, a * b = b * a

/-- Un subgrupo es normal si y sólo si es igual a todos sus conjugados. -/
def is_normal {G : Type} [group G] (H : subgrupo G) : Prop :=
∀ g : G, conjugate H g = H

/-- Si G es abeliano, todos sus subgrupos son normales. -/
example (h_ab : is_abelian G) (H : subgrupo G) : is_normal H :=
begin
  sorry
end

end subgrupo

/-
# Homomorfismos de grupos
Creamos el tipo `hom_grupos G H` de homomorfismos de grupos de `G` a `H`, y la notación `G →** H`,
es decir, `f : G →** H` indica que `f` es un homomorfismo de grupos de`G` a `H`".
-/

/-- `hom_grupos G H` es el tipo de homomorfismos de grupos de `G` a `H`. -/
@[ext] structure hom_grupos (G H : Type) [group G] [group H] :=
(to_fun : G → H)
(map_mul' (a b : G) : to_fun (a * b) = to_fun a * to_fun b)

namespace hom_grupos

-- `G` y `H` son grupos
variables {G H : Type} [group G] [group H]

-- Fijamos la notación.
notation G ` →** ` H := hom_grupos G H

/-- Esta instancia nos permite ver un homomorfismo de grupos como una función.  -/
instance : has_coe_to_fun (G →** H) (λ _, G → H) :=
{ coe := hom_grupos.to_fun }

/- la instancia anterior nos permite escribir `f (a)` -/
lemma map_mul (f : G →** H) (a b : G) : 
  f (a * b) = f a * f b :=
begin
  -- `f.map_mul` y `f.map_mul'` son *definicionalmente iguales*, pero *sintácticamente distintos*.
  exact f.map_mul' a b
end

/- ## Ejercicios sobre homomorfismos de grupos -/

-- Sea `f` un homomorfismo de grupos
variable (f : G →** H)

-- El siguiente comentario nos indica un lema ↑til para probar `map_one`.
-- example (a b : G) : a * b = b ↔ a = 1 := by library_search 
@[simp] lemma map_one : f 1 = 1 :=
begin
  sorry
end

lemma map_inv (a : G) : f a⁻¹ = (f a)⁻¹ :=
begin
  sorry
end

variable (G)

/-- `id G` es el homomorfismo identidad de `G` a `G`. -/
def id : G →** G :=
{ to_fun   := λ a, a,
  map_mul' := begin 
    sorry
  end } 

variables {K : Type} [group K] {G}

/-- `φ.comp ψ` es la composición de `φ` y `ψ`. -/
def comp (φ : G →** H) (ψ : H →** K) : G →** K :=
{ to_fun := λ g, ψ (φ g),
  map_mul' := λ a b, begin 
    sorry, 
  end 
}
lemma id_comp : (id G).comp f = f :=
begin
  sorry,
end

lemma comp_id : f.comp (id H) = f :=
begin
  sorry,
end

lemma comp_assoc {L : Type} [group L] (φ : G →** H) (ψ : H →** K) (ρ : K →** L) :
  (φ.comp ψ).comp ρ = φ.comp (ψ.comp ρ) :=
begin
  sorry,
end

/-- El kernel de un homomorfismo de grupos, como subgrupo del dominio. -/
def ker (f : G →** H) : subgroup G :=
{ carrier := {g : G | f g = 1 },
  one_mem' := begin sorry, end,
  mul_mem' := begin 
    sorry,
  end,
  inv_mem' := begin 
    sorry,
  end,
}

/-- La imagen de un homomorfismo de grupos, como subgrupo del codominio. -/
def im (f : G →** H) : subgroup H :=
{ carrier := {h : H | ∃ g : G, f g = h },
  one_mem' := begin 
    sorry,
  end,
  mul_mem' :=  begin 
    sorry,
  end,
  inv_mem' := begin 
    sorry,
  end,
}

/-- La imagen de un subgrupo bajo un homomorfismo de grupos, como subgrupo del codominio. -/
def map (f : G →** H) (K : subgroup G) : subgroup H :=
{ carrier := {h : H | ∃ g : G, g ∈ K ∧ f g = h },
  one_mem' := begin 
    sorry,
  end,
  mul_mem' := begin
    sorry,
  end,
  inv_mem' := begin
    sorry,
  end,
}

/-- La preimagen de un subgrupo bajo un homomorfismo de grupos, como subgrupo del dominio. -/
def comap (f : G →** H) (K : subgroup H) : subgroup G :=
{ carrier := {g : G | f g ∈ K },
  one_mem' := begin 
    sorry,
  end,
  mul_mem' := begin 
    sorry,
  end,
  inv_mem' := begin
    sorry,
  end,
}

end hom_grupos




