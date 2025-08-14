#import "@preview/touying:0.6.1": *
#import themes.metropolis: *
#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#import "@preview/curryst:0.5.1": rule, prooftree

#show: show-theorion

#let with-cubawiki-background(content) = {
  set page(background: 
    place(
      bottom + left, 
      dx: -100pt, 
      dy: 150pt, 
      image("280px-Logocubawiki.png", width: 700pt)
    ) + square(fill: rgb(255, 255, 255, 230), width: 100%)
  )
  content
}

#show: metropolis-theme.with(
  config-colors(secondary: navy),
  config-info(
    title: "Qué $#%\*& es una demostración?",
    author: "Eric Brandwein",
    date: "25/08/2025",
    institution: "Cubaweeki 2025"
  )
)

#set text(lang: "es", font: "Noto Sans")
#show link: set text(blue)

#with-cubawiki-background(title-slide())
// #title-slide()

#set page(background:[])

== Qué #("$#%\*&") es una demostración?

Una secuencia de aplicaciones de *axiomas* y *teoremas*.

#pause

Tiene *reglas de inferencia* para llevar de un estado a otro.#footnote[https://en.wikipedia.org/wiki/Formal_system]

#pause
#v(3em)
$
prooftree(rule(B, A, A arrow.double B))
$

#with-cubawiki-background[= Ejemplos]

---
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
    Nótese que $a$ sumado a $c$ es equivalente a sí mismo. Luego, por axioma de suma de cero, podemos sumar un cero a la $a$ de la izquierda, y sumar un cero a la $c$ de la derecha, y obtener el enunciado del teorema.
]

== Ejemplos: La Posta

#theorion-restate(filter: it => it.label == <fact:ejemplito>)

#proof[
    Vale por propiedades básicas de la aritmética.
]

#pause
#v(3em)
#align(center)[Esto es *más difícil* de pasar a algo formal.]

#with-cubawiki-background[= Cosas Malas en Demos]

== Errores Comunes

*1.* Deducir algo falso usando mal las conclusiones y/o hipótesis de un teorema/axioma/regla de inferencia.
#pause

#theorem[$A or B arrow.double A and B$.]
#proof[Asumamos que se cumple $A or B$. Alguno de los dos debe ser cierto. Asumamos sin pérdida de generalidad que $A$ es cierto. Con el mismo argumento, podemos asumir que $B$ es cierto. Por lo tanto, $A and B$ es cierto. Con esto tenemos que $A or B arrow.double A and B$, que es lo que queríamos demostrar.]

---

*2.* Deducir algo verdadero usando las hipótesis incorrectas.

#pause

#theorion-restate(filter: it => it.label == <fact:ejemplito>)
#proof[Vale porque todo natural es positivo.]
---

*2.* Deducir algo verdadero usando las hipótesis incorrectas.

#theorion-restate(filter: it => it.label == <fact:ejemplito>)
#proof[Como todo natural es positivo, la suma de $a$ con $0$ es igual a $a$, y lo mismo con $c$.]

---

*3.* No contemplar todos los casos.
#pause

#let caballos = emoji.horse
#theorem[Todos los caballos son del mismo color.]
#proof[Demostramos por inducción en el tamaño del conjunto #caballos de todos los caballos.
- #underline[Caso base] ($abs(caballos) = 1$): Trivial.
- #underline[Paso inductivo]: Elijamos dos caballos $c_1$ y $c_2$ de #caballos. Sea $caballos_A := {c_1, c_2}$ y $caballos_B := caballos without c_2$. Por hipótesis inductiva, ambos conjuntos $caballos_A$ y $caballos_B$ tienen caballos del mismo color, porque forman un conjunto de menos elementos. Como $caballos_A$ y $caballos_B$ comparten el caballo $c_1$, todos los caballos de #caballos tienen el mismo color.
]


---

*4.* Falta de formalismo, o sea, decir los pasos muy por arriba.

#pause
#theorem[$a + 0 + c = a + c + 0$.]
#proof[Vale por @fact:ejemplito.]

== Más errores comunes
*5.* Terminar demostrando otra cosa.
#pause

#block(inset: (left: 2em))[_- Ejemplo: Quería demostrar $A arrow.double B$ asumiendo $A$ y me mezclé y terminé demostrando $A$ de nuevo._]

#pause
*6.* Que no se entienda nada, i.e. errores de escritura (ambigüedad, gramática, caligrafía, palabras raras o frases largas).


== Algo más que queda raro
*7.* Repetir lo que dijiste antes para darle más "fuerza".
#pause

#theorion-restate(filter: it => it.label == <fact:ejemplito>)
#proof[No podría pasar que $(a + 0) + c eq.not a + (c + 0)$, porque la suma no funciona así. Como los números son naturales, $(a + 0) + c eq.not a + (c + 0)$ es falso.]

== Cómo encontrar estos errores?
Muy parecido a *debuggear un programa*.
#pause

#exercise[
Entren a la materia que más les guste de https://cubawiki.com.ar (álgebra, análisis, Algo 2,  Algo 3) y busquen cualquier demo de un alumno. Traten de ver qué errores de estos tienen.
]

#with-cubawiki-background[= Recomendaciones]

---
- *Practiquen, practiquen, practiquen.*#pause

- Pasen las ideas a definiciones formales.#pause

- Sépanse los axiomas y teoremas comunes del área.#pause

- Ante la duda, háganlo más riguroso.#pause

- Usen expresiones estándar.#pause

- Separen sus demos en lemitas. #pause

- Lean muchas demos bien escritas del área.#pause

- Muestren sus demos a sus compañeros y a los profes.#pause

- Lean sus demos de nuevo, y corrijan los errores que tuvieron.#pause

- *Escriban bien, loco.*

== Ejercicio
#exercise[Agarren la demo que encontraron antes que tenía el error y escríbanla de cero. Hagan muchas versiones, y hagan que cada versión sea más formal que la anterior, hasta llegar a una versión casi completamente formalizada.]

#with-cubawiki-background[
== Bibliografía útil
  - #link("https://github.com/fedelebron/algo3/blob/main/Clases/Demostraciones.pdf")[El libro de demostraciones de Fede Lebrón.]

  - https://users.metu.edu.tr/serge/courses/111-2011/textbook-math111.pdf

  - https://longformmath.com/proofs-book/

  - Libros de texto del área que estén estudiando.
]