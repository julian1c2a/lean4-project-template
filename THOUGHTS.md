# Thoughts — ProjectName

**Last updated:** 2026-04-20 00:00
**Author**: Julián Calderón Almendros

> This is an informal design journal. Record ideas, alternatives considered,
> open questions, and future directions here. Not normative — purely exploratory.
> Useful for AI context on "why" decisions were made.

---

## Design Philosophy

[Record the core design philosophy of the project here. Examples:

- Why no Mathlib dependency?
- What mathematical system is being formalized?
- What pedagogical or research goals does this serve?]

---

## Ideas and Alternatives

### 2026-04-21 — Automatización de Tácticas (Fase 4)

**Identidad y Debilitamiento**:

- Se ha implementado con éxito la táctica `derive_hyp` (basada en recursión sobre `List.Mem.head` y `List.Mem.tail` mediante `MetaM`) para cerrar automáticamente cualquier objetivo de la forma `Γ ⊢ f` siempre que `f ∈ Γ`. Esto cubre completamente la regla de identidad.
- Para el debilitamiento (`weakening`), un enfoque similar con una macro/táctica `derive_weaken T` puede tomar un teorema `T : Γ ⊢ f`, aplicar `Derives.weakening`, y luego descargar la submeta de inclusión de listas iterando sobre los elementos de `Γ` (usando `prove_mem` internamente para cada uno). Debido a que las listas `Γ` en nuestras pruebas suelen ser concretas (ej. `[A, B]`), este enfoque sintáctico funcionará bien.

**Automatización de `rewrite_at`**:

- El problema central de `rewrite_at` es que aplicar una regla local en Deducción Natural (`LocalRule`) en una posición `p` arbitraria requiere especificar explícitamente esa posición y las subfórmulas exactas (`sub` y `sub'`), lo que hace que las pruebas sean largas y propensas a errores de índice.
- *Investigación de enfoque*: En lugar de forzar al usuario a proporcionar la posición `p`, podemos crear una táctica en Lean 4 (`derive_rewrite`) que haga lo siguiente:
  1. Tome como argumento la fórmula original (o busque en `Γ` si se aplica hacia adelante) y la regla a aplicar (ej. `LocalRule.doubleNegElim`).
  2. Implemente una función `MetaM` que recorra el AST de la fórmula (`Formula`) construyendo la lista de todas las posiciones válidas (`getAllPositions`).
  3. En cada posición `p`, extraiga la subfórmula con `getAt?` e intente unificarla con el lado izquierdo de la regla dada.
  4. Si unifica, aplique `Derives.rewrite_at` con esa `p` y verifique si el resultado (`replaceAt`) coincide con el objetivo esperado.
- *Desafío*: `LocalRule` en Lean está definido como un `Prop`, lo que significa que no podemos "ejecutarlo" para extraer el patrón directamente en código de nivel de término fácilmente sin usar `Expr` unificators de `Lean.Meta`.
- *Alternativa más simple*: En lugar de recibir un `LocalRule`, la táctica podría recibir la subfórmula a buscar y la subfórmula de reemplazo explícitamente, y la táctica simplemente encuentra la posición `p` donde ocurre esa subfórmula por primera vez y delega al usuario la prueba de que `LocalRule sub sub'` es válida.

---

## Open Questions

- [ ] [Question 1 — e.g., "Should we use hierarchical partition keys?"]
- [ ] [Question 2 — e.g., "Is the current axiom ordering optimal?"]

---

## Lessons Learned

### Naming Conventions

- Mathlib naming conventions (NAMING-CONVENTIONS.md) significantly improve searchability
- The `mem_X_iff` pattern is more discoverable than `X_is_specified`
- Predicates as prefix (`isNat_zero`) are more consistent than suffix (`zero_is_nat`)

### Module Organization

- Subdirectories should mirror sub-namespaces
- Each subdirectory benefits from a `Basic.lean` for foundational definitions
- Extension modules (`FooExt.lean`) are preferable to modifying frozen modules

### Documentation

- REFERENCE.md must be self-sufficient for AI assistants
- The "project" protocol (AI-GUIDE.md §12) prevents documentation drift
- Annotations (`@importance`, `@axiom_system`) help AI prioritize context loading

---

## Future Directions

[Record long-term goals and aspirations for the project.]

---

## Aids on how is established the intention of this project

  1. Motor de razonamiento basado en reglas de inferencia de Deducción Natural.
  
  2. Formalización de un sistema lógico específico (ej. lógica proposicional, lógica de primer orden).
  
  3. Enfoque en la automatización de pruebas y la generación de contraejemplos.
  
  4. Sin dependencia de Mathlib para mantener la simplicidad y el control total sobre las definiciones y teoremas. De hecho este proyecto será la base para otros proyectos de formalización matemática que dependerán exclusivamente de este, y no de MathLib ni ninguna otra biblioteca externa. Solo dependerá del Core de Lean 4.
  
  5. Además de la lógica de predicados de primer orden, está implementada la lógica de primer orden con predicado de igualdad.
  
  6. Se mantendrá separada la lógica de primer orden con igualdad intuicionista de la lógica de primer orden con igualdad clásica, para facilitar la comparación entre ambas, de forma que lo que podamos demostrar solo de forma intuicionista será constructivista, y desde el punto de vista de Lean 4, decidible y computable, y podrá generar programas a partir de las pruebas, mientras que lo que solo podamos demostrar con lógica clásica, no será computable ni decidible, y no podrá generar programas a partir de las pruebas.
  
  7. Se implementará un sistema de tipos dependientes para la lógica de primer orden con igualdad, de forma que podamos formalizar la teoría de tipos dependientes dentro de esta lógica, y así poder comparar la teoría de tipos dependientes con la lógica de primer orden con igualdad, y ver qué cosas podemos demostrar en cada una de ellas.
  
  8. Como el proyecto tiene carácter fundacional, se implementará el conjunto de metateoría (metateoremas) de la lógica de primer orden con igualdad, incluyendo la completitud, la compacidad, la Löweheim-Skolen, la completitud de Gödel, la compacidad, etc. y se formalizarán las demostraciones de estos metateoremas dentro del sistema lógico que hemos implementado, para así tener una base sólida para la teoría de la lógica de primer orden con igualdad, y poder comparar esta teoría con otras teorías lógicas, como la teoría de tipos dependientes, la teoría de categorías, etc.
  
  9. Igualmente se implementará el punto 8. para la lógica de primer orden con igualdad pero con tipos dependientes.
  
  10. Nos queda que el motor de razonamiento sea capaz de generar contraejemplos de fórmulas no demostrables, y para esto se implementará un sistema de semántica de modelos para la lógica de primer orden con igualdad, de forma que podamos formalizar la teoría de modelos dentro de esta lógica, y así poder generar contraejemplos a partir de la semántica de modelos.
  
  11. De los puntos 1. al 10. nos hemos centrado exclusivamente en el motor de razonamiento y sus propiedades metateóricas. A partir de aquí le daremos un vuelco. Haremos un trabajo paralelo pero basado en strings, esto es, de forma más tradicional, tendremos un alfabeto inicial de símbolos, y a partir de ahí construiremos términos y fórmulas como strings, y luego implementaremos un sistema de razonamiento basado en reglas de inferencia sobre estos strings, y así podremos comparar el sistema de razonamiento basado en términos y fórmulas con el sistema de razonamiento basado en strings. El sistema de razonamiento basado en strings nos permitirá generar contraejemplos de forma más sencilla, ya que podremos manipular los strings directamente para generar contraejemplos a partir de la semántica de modelos. Este sistema basado en strings será completamente paralelo al sitema del motor principal basado en Lean 4. Este otro motor dará una vis material al motor principal. Una representación.
  
  12. El sistema de razonamiento principal deberá poder exportar sus purebas a una forma legible por humanos y tradicional (sin tácticas) en formato de strings (el segundo motor), de forma que podamos comparar las pruebas generadas por el motor principal con las pruebas generadas por el sistema basado en strings, y así poder verificar la corrección del motor principal, y también tener una representación más tradicional de las pruebas para su estudio y análisis.
  
  13. Se implementará un sistema de generación automática de pruebas, basado en técnicas de búsqueda heurística, para que el motor de razonamiento pueda generar automáticamente pruebas para fórmulas dadas, y así poder explorar el espacio de fórmulas demostrables dentro del sistema lógico que hemos implementado, y también poder comparar la capacidad de generación automática de pruebas del motor principal con la capacidad de generación automática de pruebas del sistema basado en strings.
  
  14. Se implementará un sistema de generación automática de contraejemplos, basado en técnicas de búsqueda heurística, para que el motor de razonamiento pueda generar automáticamente contraejemplos para fórmulas no demostrables, y así poder explorar el espacio de fórmulas no demostrables dentro del sistema lógico que hemos implementado, y también poder comparar la capacidad de generación automática de contraejemplos del motor principal con la capacidad de generación automática de contraejemplos del sistema basado en strings.
  
  15. Se implementará un parser para generar a partir de strings las fórmulas y los términos del sistema lógico, pasando del segundo motor al motor principal, de forma que podamos escribir fórmulas y términos en formato de strings, y luego parsearlos para generar las fórmulas y términos del sistema lógico, y así poder comparar la capacidad de parsing del motor principal con la capacidad de parsing del sistema basado en strings.
  
  16. Como intención de futuro, podemos buscar formas de ampliar el sistema lógico de primer orden con igualdad, aún con tipos dependientes a lógicas de orden superior, incluso HOL con una pila de tipos y tipos dependientes, y así poder comparar la capacidad de demostración de la lógica de primer orden con igualdad con la capacidad de demostración de la lógica de orden superior, y ver qué cosas podemos demostrar en cada una de ellas, y también poder comparar la capacidad de generación automática de pruebas y contraejemplos en cada una de ellas.
