# Convenciones de Nombres — Estilo Estricto Mathlib

Documento de referencia permanente para este proyecto.
Todas las reglas se basan estrictamente en las Mathlib Naming Conventions.

**Última actualización:** YYYY-MM-DD
**Autor:** [Nombre del Autor]

---

## 0. La Regla de Oro: Ante la duda, busca en Mathlib

Este documento cubre el 95% de los casos de uso diario, pero la matemática formal es vasta. Si te enfrentas a un concepto, teorema o estructura cuyo nombre no encaja de forma obvia en las reglas de este documento, **NO inventes un nombre**. En su lugar, el asistente de IA o el desarrollador debe buscar el equivalente en el repositorio de Mathlib (por ejemplo, examinando cómo se nombra en `Data.Set.Basic`, `Data.Nat.Basic`, etc.) y sugerir adoptar exactamente esa misma nomenclatura. El objetivo es **emular Mathlib con precisión quirúrgica**.

---

## 1. Reglas Generales de Capitalización

| Tipo de declaración | Convención | Ejemplo |
| --- | --- | --- |
| Teoremas, lemas (retornan `Prop`) | `snake_case` | `union_comm`, `mem_powerset_iff` |
| Types, Props, Structures, Classes | `UpperCamelCase` | `IsFunction`, `IsNat`, `ExistsUnique` |
| Funciones que retornan `Type` | Por tipo de retorno | `powerset` (→ Type → snake), `IsNat` (→ Prop → Upper) |
| Constructores / valores (Type) | `lowerCamelCase` | `cero`, `succ`, `insertarOrdenado` |
| Acrónimos | Tratados como palabra | `PROJECT_NAME` (namespace), `project_name` (snake_case) |

---

## 2. Diccionario Universal de Símbolos

| Símbolo | Palabra en nombres | Notas / Ejemplos |
| --- | --- | --- |
| `∈` / `∉` | `mem` / `not_mem` | `mem_succ_iff` |
| `∪` / `∩` | `union` / `inter` | Operaciones binarias |
| `⋃` / `⋂` | `sUnion` / `sInter` | `s` = "set of sets" |
| `⊆` / `⊂` | `subset` / `ssubset` | `⊂` lleva una `s` extra por estricto |
| `𝒫` | `powerset` | Sin "Of" |
| `σ` | `succ` | Sucesor |
| `∅` | `empty` o `zero` | Depende del contexto de la teoría |
| `△` / `ᶜ` / `\` | `symmDiff` / `compl` / `sdiff` | Diferencia simétrica, complemento, resta |
| `×ₛ` | `prod` | Producto cartesiano |
| `⟂` | `disjoint` | Conjuntos disjuntos |
| `↔` / `¬` | `iff` / `not` | `iff` siempre va como sufijo |
| `∃` / `∀` | `exists` / `forall` | |
| `∘` / `⁻¹` | `comp` / `inv` | Composición, Inversa |
| `+` / `*` / `-` | `add` / `mul` / `sub` | `sub` para binario, `neg` para unario |
| `^` / `/` / `∣` | `pow` / `div` / `dvd` | `dvd` = divide |
| `≤` / `<` | `le` / `lt` | |
| `≥` / `>` | `ge` / `gt` | Solo usar para versiones con argumentos intercambiados |
| `0` / `1` | `zero` / `one` | |

---

## 3. Las 13 Reglas de Formación de Nombres

### REGLA 1: Conclusión primero, hipótesis con `_of_`

El nombre describe **qué se demuestra**, no el camino para llegar a ello.

> ❌ `element_is_property` — `(isProperty n → m ∈ n → isProperty m)`
> ✅ `isProperty_of_isProperty_of_mem` — Conclusión: `isProperty`, Hipótesis: `isProperty`, `mem`

### REGLA 2: Bicondicionales llevan el sufijo `_iff`

Si el teorema es una equivalencia (`↔`), el sufijo `_iff` es obligatorio.

> ❌ `BinInter_empty` — `(x ∩ y = ∅ ↔ x ⟂ y)`
> ✅ `inter_eq_empty_iff_disjoint`

### REGLA 3: Prohibido `_wc` — Usar `.mp`, `.mpr` o `_of_`

Los sufijos heredados como `_wc` (weak condition) están prohibidos.
Si tienes `A ↔ B`, usa `theorem.mp` (`A → B`) o `theorem.mpr` (`B → A`). Si creas un lema separado unidireccional, aplica la Regla 1 (`_of_`).

> ❌ `ExtSet_wc` — `(A ⊆ B → B ⊆ A → A = B)`
> ✅ `eq_of_subset_of_subset`

### REGLA 4: Sufijos axiomáticos estándar para propiedades algebraicas

En lugar de deletrear la propiedad, usa los sufijos estándar:

- `_comm` (conmutatividad): `union_comm`
- `_assoc` (asociatividad): `inter_assoc`
- `_self` (idempotencia/identidad): `union_self` (`A ∪ A = A`)
- `_left` / `_right` (variantes laterales): `union_subset_left`
- `_refl`, `_symm`, `_trans`, `_antisymm`, `_cancel`, `_mono`, `_inj` (inyectividad).

### REGLA 5: Predicados como prefijo, operaciones en orden infijo

> ❌ `zero_is_nat`
> ✅ `isNat_zero`

**Excepción:** Los predicados de morfismos (`_injective`, `_surjective`, `_bijective`) siempre van como sufijo (ej. `succ_injective`).

### REGLA 6: Abreviaturas estándar para inecuaciones

| Condición | Abreviatura |
| --- | --- |
| `x > 0` | `pos` |
| `x < 0` | `neg` |
| `x ≥ 0` | `nonneg` |
| `x ≤ 0` | `nonpos` |

### REGLA 7: El prefijo `Is` en mayúscula para definiciones `Prop`

Las definiciones que retornan `Prop` deben ser `UpperCamelCase`.

> ❌ `def isSingleValued ...`
> ✅ `def IsSingleValued ...`

**Nota:** En los teoremas que los usan, vuelven a `snake_case` en minúscula: `isSingleValued_empty`.

### REGLA 8: Funciones y constructores (no `Prop`) en `lowerCamelCase`

Cualquier función o constructor que retorne datos (universo, números, listas) usa `lowerCamelCase`. No prefijar tipos.

> ❌ `PowerSetOf`, `BinUnion`, `UnionSet`
> ✅ `powerset`, `union`, `sUnion`

### REGLA 9: Especificaciones como `mem_X_iff`

Para axiomas o teoremas que definen la membresía de un conjunto, usar este patrón en lugar de `_is_specified`.

> ❌ `SpecSet_is_specified` — `(x ∈ {z ∈ A | P} ↔ x ∈ A ∧ P x)`
> ✅ `mem_sep_iff`, `mem_powerset_iff`, `mem_union_iff`

### REGLA 10: Existencia y Unicidad

Si un teorema demuestra `∃!`, usar el sufijo `_unique`.

> ❌ `BinInterUniqueSet`
> ✅ `inter_unique`, `powerset_unique`

### REGLA 11: Variantes laterales `_left` y `_right`

Usadas para indicar qué lado de una operación es el afectado.

- `add_le_add_left` — si `a ≤ b`, entonces `c + a ≤ c + b`.
- `subset_union_left` — `A ⊆ A ∪ B`.

### REGLA 12: Nombres Propios

Los teoremas con nombres matemáticos históricos mantienen sus nombres propios.

> ✅ `cantor_schroeder_bernstein`, `cantor_no_surjection`.

### REGLA 13: Sufijos de Dominio (Evitar colisiones)

Cuando se construyen estructuras avanzadas y se quieren evitar colisiones con operaciones nativas (como `Nat.*`), se debe añadir un sufijo en mayúscula.

- Estructura `Z`: `addZ`, `mulZ`, `leZ`, `isPositiveZ`.
- Estructura `Q`: `addQ`, `mulQ`, `isPositiveQ`.

**Nota:** Predicados como `isPositiveZ` bajan a minúscula inicial porque el sufijo de dominio ya actúa como demarcador.

---

## 4. Estructura de Archivos, Directorios y Módulos

La jerarquía de archivos debe reflejar la jerarquía matemática y organizativa de manera predecible.

- **Nombres de archivos y directorios:** Siempre en `UpperCamelCase`.
- **Mapeo de Módulos:** La ruta del archivo define exactamente el nombre del módulo.
  Un archivo en `Data/Set/Basic.lean` se declara automáticamente como el módulo `Data.Set.Basic`.
- **Archivos `Basic.lean`:** El archivo que contiene las definiciones fundamentales y las propiedades más elementales de una estructura debe llamarse `Basic.lean` (ej. `NumberTheory/Basic.lean`).
- **Archivos `Lemmas.lean` o temáticos:** Las propiedades derivadas más avanzadas se separan en archivos descriptivos (ej. `Order.lean`, `Equiv.lean`).

---

## 5. Espacios de Nombres (Namespaces)

- **Convención de nombre:** Los namespaces usan `UpperCamelCase` (ej. `Peano`, `ZFC`, `Polynomial`).
- **Regla de No Redundancia (CRÍTICA):** Nunca repitas el nombre del namespace en los teoremas o definiciones que contiene. El sistema de Lean ya provee el prefijo cuando se usa desde fuera.

  > Contexto: estás dentro de `namespace Set`.
  > ❌ `theorem set_subset_refl ...` — desde fuera se vería como `Set.set_subset_refl`.
  > ✅ `theorem subset_refl ...` — desde fuera se ve limpio como `Set.subset_refl`.

- **Apertura y Cierre:** Siempre cierra un namespace de forma explícita: `end MiNamespace`.
- **Bloques de variables:** Los bloques `variable` se declaran típicamente justo después de abrir el namespace.

---

## 6. Diccionario Estándar de Variables

Para mantener la consistencia en todas las firmas de teoremas, Mathlib utiliza un conjunto estandarizado de letras según el tipo.

| Tipo de Objeto | Letras Preferidas | Ejemplo de uso en código |
| --- | --- | --- |
| Tipos (Types/Sorts) | `α`, `β`, `γ`, `δ`, `ι` (Griegas) | `variable {α β : Type}` |
| Elementos Genéricos | `x`, `y`, `z`, `a`, `b`, `c` | `∀ x y : α, x = y` |
| Naturales / Enteros | `m`, `n`, `k`, `i`, `j` | `∀ n : ℕ, n < succ n` |
| Funciones | `f`, `g`, `h` | `f : α → β` |
| Conjuntos (Mathlib Set) | `s`, `t`, `u` (Minúsculas) | `s ⊆ t` |
| Conjuntos (Teoría Axiomática Pura) | `A`, `B`, `C`, `X`, `Y` (Mayúsculas)* | `A ⊆ A ∪ B` |
| Proposiciones / Pruebas | `p`, `q`, `r` o `h`, `h₁`, `h₂` | `(h : p ∧ q)` |
| Predicados (Prop-valued fun) | `P`, `Q`, `R` | `P : α → Prop` |
| Universos | `u`, `v`, `w` | `universe u` |

> \* En Mathlib estándar los conjuntos son `s`, `t`. Si el proyecto es fundamentalmente sobre Teoría de Conjuntos pura —como ZFC o Peano— usar `A`, `B`, `C` es aceptable si facilita la lectura de fórmulas complejas, pero debe mantenerse de manera consistente.

---

## 7. Clases de Tipos (Typeclasses)

- **Nomenclatura:** Las Typeclasses se escriben en `UpperCamelCase`.
- **Semántica:** Preferiblemente deben ser un sustantivo (para estructuras) o un adjetivo (para propiedades).
  - Estructura: `Group`, `Ring`, `TopologicalSpace`.
  - Propiedad: `DecidableEq`, `IsCommutative`, `Fintype`.
- **No incluir** sufijos redundantes como `Class`.
