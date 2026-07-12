# Convenciones de Nombres — Estilo Mathlib

> Documento de referencia permanente para este proyecto. Todas las reglas se basan en
> las [convenciones de nomenclatura de Mathlib](https://leanprover-community.github.io/contribute/naming.html),
> adaptadas al dominio específico del proyecto.
>
> **Los nombres de identificadores (tipos, teoremas, funciones, variables) van siempre
> en inglés** — es la convención de Mathlib y la que sigue todo el ecosistema Lean 4.
> La prosa de este documento (explicaciones, motivación) va en español para que quede
> clara sin ambigüedad.

**Última actualización:** YYYY-MM-DD
**Autor**: [Nombre del Autor]

---

## 1. Reglas de Capitalización

| Tipo de declaración | Convención | Ejemplo |
|---|---|---|
| Teoremas, lemas (términos `Prop`) | `snake_case` | `union_comm`, `mem_powerset_iff` |
| Tipos, `Prop`s, estructuras, clases | `UpperCamelCase` | `IsFunction`, `IsNat`, `BoolAlg.Basic` |
| Funciones que devuelven `Type` | según el tipo de retorno | `powerset` (→ tipo → `snake`), `IsNat` (→ `Prop` → `Upper`) |
| Otros términos `Type` | `lowerCamelCase` | `successor`, `fromPeano`, `binUnion` |
| Acrónimos | como grupo, mayúsculas u minúsculas | `ZFC` (namespace), `zfc` (en snake_case) |

---

## 2. Diccionario Símbolo → Palabra

| Símbolo | En nombres | Nota |
|---|---|---|
| ∈ | `mem` | `x ∈ A` → `mem` |
| ∉ | `not_mem` | |
| ∪ | `union` | binaria |
| ∩ | `inter` | binaria |
| ⋃ | `sUnion` | `s` = "conjunto de conjuntos" |
| ⋂ | `sInter` | ídem |
| ⊆ | `subset` | no estricta |
| ⊂ | `ssubset` | estricta (`s` extra) |
| 𝒫 | `powerset` | |
| σ | `succ` | |
| ∅ | `empty` | |
| △ | `symmDiff` | |
| ᶜ | `compl` | complemento |
| \ | `sdiff` | diferencia de conjuntos |
| ×ₛ | `prod` | producto cartesiano |
| ⟂ | `disjoint` | |
| = | `eq` | a menudo se omite |
| ≠ | `ne` | |
| → | `of` / implícito | la conclusión va primero |
| ↔ | `iff` | sufijo |
| ¬ | `not` | |
| ∃ | `exists` | |
| ∀ | `forall` | |
| ∘ | `comp` | composición |
| ⁻¹ | `inv` | inverso |
| + | `add` | |
| \* / · | `mul` | |
| − | `sub` (binaria) / `neg` (unaria) | |
| ^ | `pow` | |
| / | `div` | |
| ∣ | `dvd` | divide |
| ≤ / < | `le` / `lt` | |
| ≥ / > | `ge` / `gt` | solo para versiones con argumentos intercambiados |
| 0 / 1 | `zero` / `one` | |

---

## 3. Reglas de Formación de Nombres (12 reglas)

### REGLA 1 — Conclusión primero, hipótesis con `_of_`

El nombre describe **qué se demuestra**, no el camino para llegar a ello:

```text
-- Patrón:     A → B → C
-- Nombre:     c_of_a_of_b
-- Orden:      conclusión_of_hipótesis1_of_hipótesis2

-- Ejemplo:
-- Teorema:  isNat n → isNat (σ n)
-- Nombre:   isNat_succ_of_isNat
```

### REGLA 2 — Los bicondicionales llevan el sufijo `_iff`

```text
-- Teorema:  x ∈ (𝒫 A) ↔ x ⊆ A
-- Nombre:   mem_powerset_iff
```

### REGLA 3 — Prohibido `_wc` — usar `.mp`/`.mpr` o `_of_`

```text
-- Dirección de ida de un iff:    inter_eq_empty_iff_disjoint.mp
-- Dirección de vuelta:           inter_eq_empty_iff_disjoint.mpr
-- Como teorema unidireccional:   disjoint_of_inter_eq_empty
```

### REGLA 4 — Propiedades algebraicas → sufijo axiomático corto

```text
-- conmutatividad:   union_comm, inter_comm
-- asociatividad:    inter_assoc, union_assoc
-- absorción:        union_inter_self
-- distributividad:  union_inter_distrib_left
```

**Sufijos axiomáticos estándar (Mathlib):**

| Sufijo | Significado | Ejemplo |
|---|---|---|
| `_comm` | conmutatividad | `union_comm` |
| `_assoc` | asociatividad | `inter_assoc` |
| `_refl` | reflexividad | `subset_refl` |
| `_irrefl` | irreflexividad | `ssubset_irrefl` |
| `_symm` | simetría | `disjoint_symm` |
| `_trans` | transitividad | `subset_trans` |
| `_antisymm` | antisimetría | `subset_antisymm` |
| `_asymm` | asimetría | `ssubset_asymm` |
| `_inj` | inyectividad (iff) | `succ_inj` (σ a = σ b ↔ a = b) |
| `_injective` | inyectividad (predicado) | `succ_injective` |
| `_self` | operación consigo mismo | `union_self` (A ∪ A = A) |
| `_left` / `_right` | variante lateral | `union_subset_left` |
| `_cancel` | cancelación | `add_left_cancel` |
| `_mono` | monotonía | `powerset_mono` |

### REGLA 5 — Predicados como prefijo, operaciones en orden infijo

```text
-- Predicado como prefijo:  isNat_zero (no zero_is_nat)
-- Excepción:               succ_injective (_injective/_surjective siempre van de sufijo)
```

### REGLA 6 — Abreviaturas estándar para condiciones frecuentes

| En vez de | Usa | Significado |
|---|---|---|
| `zero_lt_x` | `pos` | x > 0 |
| `x_lt_zero` | `neg` | x < 0 |
| `x_le_zero` | `nonpos` | x ≤ 0 |
| `zero_le_x` | `nonneg` | x ≥ 0 |

### REGLA 7 — Prefijo `Is` para predicados `Prop`

```text
-- Definición (Prop):    def IsNat (n : U) : Prop := ...     (UpperCamelCase)
-- En nombres de teorema: isNat_zero, isNat_succ, isNat_of_mem (lowerCamelCase dentro de snake_case)
```

### REGLA 8 — Funciones/constructores no-`Prop`: `lowerCamelCase`

```text
-- powerset (no PowerSetOf)  — lowerCamelCase, quitar "Of"
-- union (no BinUnion)       — se quita "Bin" (la aridad ya es binaria)
-- sep (no SpecSet)          — "sep" es el estándar de Mathlib para separación
-- comp (no FunctionComposition)
-- image (no ImageSet)
```

### REGLA 9 — Especificaciones: `_iff` y `mem_X_iff`

El patrón `X_is_specified` se sustituye por `mem_X_iff`:

```text
-- mem_succ_iff      (antes: successor_is_specified)
-- mem_inter_iff     (antes: BinInter_is_specified)
-- mem_union_iff     (antes: BinUnion_is_specified)
-- mem_sep_iff       (antes: SpecSet_is_specified)
```

### REGLA 10 — Existencia y unicidad

```text
-- inter_unique      (antes: BinInterUniqueSet)
-- powerset_unique   (antes: PowerSetExistsUnique)
-- sUnion_unique     (antes: UnionExistsUnique)
```

### REGLA 11 — Variantes laterales `_left` / `_right`

```text
-- subset_union_left    — A ⊆ (A ∪ B), el subconjunto es el argumento izquierdo
-- subset_union_right   — B ⊆ (A ∪ B), el subconjunto es el argumento derecho
```

### REGLA 12 — Nombres propios

Los teoremas con nombre histórico mantienen su nombre propio tal cual:

```text
-- cantor_no_surjection
-- cantor_schroeder_bernstein
```

> **Nota:** los nombres propios matemáticos se conservan sin traducir ni normalizar.
> Solo se normalizan las palabras operacionales (`mem`, `union`, etc.).

---

## 4. Tablas de Referencia Rápida

### 4.1 Definiciones — renombrados habituales

| Antes | Después | Motivo |
|---|---|---|
| `BinInter` | `inter` | se quita "Bin" |
| `BinUnion` | `union` | se quita "Bin" |
| `PowerSetOf` | `powerset` | lowerCamelCase, se quita "Of" |
| `UnionSet` | `sUnion` | "s" = conjunto-de-conjuntos |
| `SpecSet` | `sep` | estándar Mathlib |
| `successor` | `succ` | abreviatura estándar |
| `FunctionComposition` | `comp` | abreviatura estándar |
| `IdFunction` | `id` | abreviatura estándar |
| `InverseFunction` | `inv` | abreviatura estándar |
| `ImageSet` | `image` | simplificación |
| `PreimageSet` | `preimage` | simplificación |
| `Restriction` | `restrict` | simplificación |
| `isNat` | `IsNat` | UpperCamelCase (Prop) |

### 4.2 Teoremas — `_is_specified` → `mem_X_iff`

| Antes | Después | Desglose |
|---|---|---|
| `PowerSet_is_specified` | `mem_powerset_iff` | mem + 𝒫 + ↔ |
| `successor_is_specified` | `mem_succ_iff` | mem + σ + ↔ |
| `BinInter_is_specified` | `mem_inter_iff` | mem + ∩ + ↔ |
| `BinUnion_is_specified` | `mem_union_iff` | mem + ∪ + ↔ |

### 4.3 Teoremas — propiedades algebraicas

| Antes | Después | Desglose |
|---|---|---|
| `BinUnion_commutative` | `union_comm` | ∪ + conmutatividad |
| `BinInter_commutative` | `inter_comm` | ∩ + conmutatividad |
| `subseteq_reflexive` | `subset_refl` | ⊆ + reflexividad |
| `subseteq_transitive` | `subset_trans` | ⊆ + transitividad |

---

## 5. Estructura de Archivos, Directorios y Módulos

La jerarquía de archivos refleja la jerarquía matemática y organizativa de forma
predecible.

- **Nombres de archivos y directorios**: siempre `UpperCamelCase`.
- **Mapeo módulo↔ruta**: la ruta del archivo define exactamente el nombre del módulo
  (`Data/Set/Basic.lean` → módulo `Data.Set.Basic`).
- **`Basic.lean`**: contiene las definiciones fundamentales y propiedades más
  elementales de una estructura (p. ej. `NumberTheory/Basic.lean`).
- **Ficheros temáticos** (`Order.lean`, `Equiv.lean`, …): propiedades derivadas más
  avanzadas, separadas por tema.
- **Barrels**: ver `AI-GUIDE.md` §18 — un fichero por directorio con 2+ submódulos,
  solo `import`, sin código.

---

## 6. Espacios de Nombres (Namespaces)

- Convención: `UpperCamelCase` (`Peano`, `ZFC`, `Polynomial`).
- **Regla de no redundancia (crítica)**: nunca repetir el nombre del namespace dentro
  de los teoremas/definiciones que contiene — Lean ya añade el prefijo al usarlo desde
  fuera.

  ```text
  -- Dentro de `namespace Set`:
  -- Mal:  theorem set_subset_refl ...   (se vería `Set.set_subset_refl` desde fuera)
  -- Bien: theorem subset_refl ...       (se ve limpio como `Set.subset_refl`)
  ```

- Cerrar siempre el namespace explícitamente (`end MiNamespace`) para evitar
  confusiones de alcance.
- Los bloques `variable` se declaran justo después de abrir el namespace.

---

## 7. Diccionario Estándar de Variables

Para mantener consistencia en las firmas, Mathlib usa un conjunto estandarizado de
letras según el tipo del objeto:

| Tipo de objeto | Letras preferidas | Ejemplo |
|---|---|---|
| Tipos (`Type`/`Sort`) | `α, β, γ, δ, ι` | `variable {α β : Type}` |
| Elementos genéricos | `x, y, z, a, b, c` | `∀ x y : α, x = y` |
| Naturales/enteros | `m, n, k, i, j` | `∀ n : ℕ, n < succ n` |
| Funciones | `f, g, h` | `f : α → β` |
| Conjuntos (estilo Mathlib `Set`) | `s, t, u` (minúsculas) | `s ⊆ t` |
| Conjuntos (teoría axiomática pura) | `A, B, C, X, Y` (mayúsculas)* | `A ⊆ A ∪ B` |
| Proposiciones/pruebas | `p, q, r` o `h, h₁, h₂` | `(h : p ∧ q)` |
| Predicados (`α → Prop`) | `P, Q, R` | `P : α → Prop` |
| Universos | `u, v, w` | `universe u` |

\* En Mathlib estándar los conjuntos son `s, t`. Si el proyecto trata fundamentalmente
teoría de conjuntos pura (ZFC, Peano, HF…), usar `A, B, C` es aceptable si facilita la
lectura de fórmulas complejas — pero debe mantenerse consistente en todo el proyecto.

---

## 8. Clases de Tipos (Typeclasses)

- Nomenclatura: `UpperCamelCase`.
- Semántica: sustantivo para estructuras (`Group`, `Ring`, `TopologicalSpace`),
  adjetivo para propiedades (`DecidableEq`, `IsCommutative`, `Fintype`).
- No añadir sufijos redundantes como `Class`.

---

## 9. Convenciones locales (específicas del proyecto)

Cada proyecto puede necesitar convenciones propias que no encajan en las reglas
universales de arriba (p. ej. un sufijo de dominio para evitar colisiones entre
estructuras isomorfas, o una convención de sufijo para un subsistema concreto).

**No las declares aquí de forma universal si no se van a seguir de verdad** — la
auditoría cruzada de 2026-07-12 encontró exactamente este problema: una "REGLA 13" de
sufijos de dominio (`addZ`, `mulQ`) documentada como regla general en un proyecto que
en la práctica nunca la usó (usó namespaces anidados en su lugar), y una convención de
sufijo `*VN` realmente muy usada en otro proyecto que no estaba documentada en ningún
sitio.

**Cómo hacerlo bien**: documenta aquí, en esta sección, solo las convenciones locales
que el código *realmente sigue* — verificado por grep antes de escribirlas, no
aspiracional — y enlaza a `DECISIONS.md` si la convención nace de una decisión
arquitectónica concreta (ADR).

<!-- Ejemplo de entrada real (borrar si no aplica a este proyecto):
### Sufijo `*VN` — transporte de aritmética de Peano a HFSet
Módulos que codifican la construcción de von Neumann `vN : ℕ₀ → HFSet` llevan el
sufijo `VN` en el nombre de archivo y usan un namespace `VN` (p. ej. `VN/PowVN.lean`,
`namespace VN`, `powVN`). Ver DECISIONS.md ADR-000.
-->

---

## 10. Nota de Migración

Durante el desarrollo, los nombres se renombran progresivamente siguiendo estas
convenciones. Orden de prioridad sugerido:

1. Módulos base (axiomas): extensión, especificación, unión, partes.
2. Números naturales: módulo básico + aritmética.
3. Funciones y relaciones.
4. Estructuras derivadas: álgebras booleanas, cardinalidad, etc.

Cada renombrado se verifica con compilación completa antes de continuar.
