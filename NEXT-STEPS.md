# Próximos Pasos — FOL

**Última actualización:** 2026-04-25 22:30
**Autor**: Julián Calderón Almendros

> Este archivo hace un seguimiento de las fases de desarrollo planificadas para el proyecto de Lógica de Primer Orden (FOL).
> **Nota:** Para el detalle exhaustivo de reglas lógicas y teoremas a demostrar, consulta [STARTING_FOL.md](STARTING_FOL.md).

---

## Fase 1: Fundamentos Lógicos (Deducción Natural)

**Objetivo**: Completar las reglas base de deducción en `FOL/FOL.lean`.

**Tareas**:

- [x] Implementar la regla de Reductio ad Absurdum (RAA) en `Derives` para habilitar la lógica clásica.
- [x] Implementar la regla de debilitamiento (Weakening).
- [x] Refinar las reglas de cuantificadores ($\forall$ y $\exists$) con gestión de variables libres (índices de De Bruijn).

**Dependencias**: Ninguna (Nivel 0)
**Complejidad**: Media

---

## Fase 2: Primeros Teoremas (Nivel 1 y 2)

**Objetivo**: Demostrar las tautologías fundamentales descritas en `STARTING_FOL.md`.

**Módulos propuestos**:

- [x] `FOL/Theorems/Impl.lean` — Tautologías de implicación (Identidad, K, S, Silogismo).
- [x] `FOL/Theorems/Neg.lean` — Propiedades de la negación (Doble negación, Contrapositivas, Explosión).

**Dependencias**: Fase 1 completada.
**Complejidad**: Media

---

## Fase 3: Conectivos Derivados y Cuantificadores (Nivel 3 y 4)

**Objetivo**: Establecer y demostrar el comportamiento de $\land$, $\lor$, $\Leftrightarrow$ y la interacción de $\forall$ / $\exists$.

**Módulos propuestos**:

- [x] `FOL/Theorems/Derived.lean` — Leyes de De Morgan, Conmutatividad, Tercio Excluso.
- [x] `FOL/Theorems/Quantifiers.lean` — Dualidad y distribución de cuantificadores.

**Dependencias**: Fase 2 completada.
**Complejidad**: Media / Alta (por la gestión de sustituciones y De Bruijn).

---

## Fase 4: Automatización y Tácticas

**Objetivo**: Facilitar la escritura de pruebas mediante metaprogramación o automatización básica en Lean 4.

**Tareas**:

- [x] Investigar la creación de una táctica que aplique `rewrite_at` automáticamente buscando posiciones válidas.
- [x] Automatizar la regla de identidad y debilitamiento.
- [x] Implementar macros finales para `derive_rewrite` y `derive_weaken`.

**Dependencias**: Fase 3 completada.
**Complejidad**: Alta

---

## Fase 5: Metamatemática y Completitud

**Objetivo**: Estudiar las propiedades formales del sistema deductivo y establecer la semántica completa de la Lógica de Primer Orden.

**Tareas**:

- [x] **Teorema de Deducción:** Demostrar que si $Γ, A \vdash B$, entonces $Γ \vdash A \Rightarrow B$.
- [x] **Semántica y Modelos (Opción B):** Definir noción de modelo y relación de satisfacción ($\models$).
- [x] **Teorema de Corrección (Soundness):** Demostrar que si $Γ \vdash A$, entonces $Γ \models A$.
- [x] Demostrar los 5 lemas semánticos auxiliares en `Semantics.lean`.
- [x] **Teorema de Completitud:** Demostrar que si $Γ \models A$, entonces $Γ \vdash A$.
- [x] **Consistencia:** Demostrar la consistencia del sistema (`consistency_of_satisfiable`).
- [x] **Teorema de Compacidad:** Demostrar que un conjunto de fórmulas es satisfacible si y solo si todo subconjunto finito lo es (`compactness_theorem`).

**Dependencias**: Fase 1-4 completadas.
**Complejidad**: Muy Alta

---

## Fase 6: FOL con Igualdad (FOL=)

**Objetivo**: Extender el lenguaje y el sistema deductivo para soportar el predicado de igualdad lógica (`=`).

**Tareas**:
- [x] Modificar la sintaxis en `FOL.lean` añadiendo el constructor de igualdad a `Formula` (`eq : Term → Term → Formula`).
- [x] Añadir las reglas de inferencia para la igualdad (Reflexividad y Sustitución de Leibniz) en `Derives`.
- [x] Actualizar la semántica en `Semantics.lean` para que la igualdad sintáctica coincida con la igualdad semántica del modelo.
- [x] Adaptar las pruebas de Soundness y Completeness a la nueva sintaxis y reglas (usando dominios cociente).

**Dependencias**: Fase 5 completada.
**Complejidad**: Alta

---

## Resumen de Estado

| Fase | Descripción | Estado |
|-------|-------------|--------|
| 1 | Fundamentos Lógicos | ✅ Completo |
| 2 | Primeros Teoremas | ✅ Completo |
| 3 | Conectivos y Cuantificadores | ✅ Completo |
| 4 | Automatización | ✅ Completo |
| 5 | Metamatemática | ✅ Completo |
| 6 | FOL con Igualdad | ✅ Completo |
