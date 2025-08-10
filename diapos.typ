#import "@preview/touying:0.6.1": *
#import themes.metropolis: *
#import "@preview/theorion:0.3.2": *
#import cosmos.clouds: *
#show: show-theorion

#show: metropolis-theme.with(
  aspect-ratio: "16-9",
  config-info(
    title: "Qué $#%\*& es una demostración?",
    author: "Eric Brandwein",
    date: "2025-08-22",
    institution: "Cubaweeki",
  )
)

#set text(lang: "es")
#show link: set text(blue)

#title-slide()

== Qué #("$#%\*&") es una demostración?

Una secuencia de aplicaciones de axiomas y teoremas.

= Ejemplos

== Ejemplos
#theorem[$(a+0)+c = a + (c + 0).$]<fact:ejemplito>

== Ejemplos: Secuencia de Aplicaciones

#theorion-restate(filter: it => it.label == <fact:ejemplito>)
#proof[
$
    (a+0)+c = a + (c + 0) &<=> (a)+c = a + (c + 0) &->"por axioma de la suma de 0."\
    &<=> a + c = a + (c + 0) &->"por regla de paréntesis extra."\
    &<=> a + c = a + (c) &->"por axioma de la suma de 0."\
    &<=> a + c = a + c &->"por regla de paréntesis extra."\
    &<=> #[*True*] &->"por identidad de términos."
$
]

== Ejemplos: Lenguaje de Programación (Lean 4)

#theorion-restate(filter: it => it.label == <fact:ejemplito>)
#proof[
```lean
    import Mathlib.Data.Real.Basic

    example (a c : Nat) : (a + 0) + c = a + (c + 0) := by
        rewrite [add_zero] -- a + c = a + (c + 0)
        rewrite [add_zero] -- a + c = a + c
```
]

#pause

Podemos correr la demo #link("https://live.lean-lang.org/#codez=JYWwDg9gTgLgBAWQIYwBYBtgCMB0ARFJHAJQFMl0cAhJAZ2AGMAoJ0gDyXHVLgAok4DOAC44gVEIAlCL4CA1HAAMU+UIC8cOXyHylI9VgCeTOHCgB3OAG0kAExsB9AF6koEALrHTF63acv3QA")[acá].

== Ejemplos: Lenguaje Natural Formal

#theorion-restate(filter: it => it.label == <fact:ejemplito>)

#proof[
    Nótese que $a$ sumado a $c$ es equivalente a sí mismo. Luego, por axioma de suma de cero, podemos sumar un cero a la $a$ de la izquierda, y sumar un cero a la $c$ de la izquierda, y obtener el enunciado del teorema.
]

== Ejemplos: La Posta

#theorion-restate(filter: it => it.label == <fact:ejemplito>)

#proof[
    Vale por propiedades básicas de la aritmética.
]

#pause
#v(3em)
#align(center)[Esto es *más difícil* de pasar a algo formal.]

= Cosas Malas en Demos

== Ejemplo Malo

#theorion-restate(filter: it => it.label == <fact:ejemplito>)
#proof[Vale porque todo natural es positivo.]

== Ejemplo Malo (más sutil)

#theorion-restate(filter: it => it.label == <fact:ejemplito>)
#proof[Como todo natural es positivo, la suma de $a$ con $0$ es igual a $a$, y lo mismo con $c$.]

== Errores comunes

*1.* Deducir algo falso usando mal las conclusiones de un teorema/axioma/definición. #pause

*2.* Deducir algo verdadero usando las hipótesis incorrectas. #pause

*3.* No contemplar todos los casos. #pause

*4.* Falta de formalismo, o sea, decir los pasos muy por arriba. #pause

*5.* Terminar demostrando otra cosa. #pause

*6.* Que no se entienda nada, i.e. errores de escritura (ambigüedad, gramática, caligrafía, palabras raras o frases largas). #pause


== Una más que queda rara
*7.* Repetir lo que dijiste antes para darle más "fuerza".

== Cómo encontrar estos errores
Muy parecido a *debuggear un programa*.

#exercise[
Entren a la materia que más les guste de https://cubawiki.com.ar (álgebra, análisis, Algo 2,  Algo 3) y busquen cualquier demo de un alumno. Traten de ver qué errores de estos tienen.
]

= Recomendaciones

== Recomendaciones
- Pasen las ideas a definiciones formales.#pause

- Sépanse los axiomas y teoremas comunes del área.#pause

- Ante la duda, háganlo más riguroso.#pause

- Usen expresiones estándar.#pause

- Lean muchas demos bien escritas del área.#pause

- Practiquen, practiquen, practiquen.#pause

- Muestren sus demos a sus compañeros y a los profes.#pause

- Lean sus demos de nuevo, y corrijan los errores que tuvieron.#pause

- *Escriban bien, loco.*

== Ejercicio
Agarren la demo que encontraron antes que tenía el error y escríbanla de cero. Hagan muchas versiones, y hagan que cada versión sea más formal que la anterior, hasta llegar a una versión casi completamente formalizada.

== Bibliografía útil

- #link("https://github.com/fedelebron/algo3/blob/main/Clases/Demostraciones.pdf")[El libro de demostraciones de Fede Lebrón.]

- https://users.metu.edu.tr/serge/courses/111-2011/textbook-math111.pdf
- https://longformmath.com/proofs-book/
- Libros de texto del área que estén estudiando.