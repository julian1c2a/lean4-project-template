# Guía Maestra de la IA — Estándares de Documentación y Desarrollo

**Última actualización:** YYYY-MM-DD  
**Autor:** [Nombre del Autor]

Este documento establece los requisitos universales y estándares para la documentación técnica, escritura de código y flujo de trabajo de este proyecto Lean 4.

> Este archivo es el **primer documento** que un asistente de IA debe leer.  
> Define el protocolo de documentación del proyecto, las convenciones de nomenclatura,
> la política de bloqueo de archivos, el formato de código y la lista de verificación de cumplimiento.  
> **Léelo completamente antes de modificar cualquier archivo `.lean` o documentación.**

---

## Sistema REFERENCE — Arquitectura en Árbol

### (0.) Naturaleza de la documentación

Esta documentación es puramente técnica, no para usuarios finales. Es una referencia para asistentes de IA y desarrolladores experimentados de Lean 4. Debe ser clara, precisa y completa, pero no pedagógica.

### (0.5.) Arquitectura en Árbol y Navegación Fuerte

El sistema de referencia no es monolítico, sino que se organiza en un árbol de documentos interconectados:

- **Índice Raíz** (`PROJECT_ROOT/REFERENCE.md`): Actúa como punto de entrada, catálogo general del proyecto y mapa de navegación.
- **Nodos Temáticos** (`PROJECT_ROOT/doc/REFERENCE-{campo-temático}.md`): Archivos dedicados a ramas matemáticas específicas (ej. `REFERENCE-Arith.md`, `REFERENCE-GroupTheory.md`).
- **Navegación Fuerte**: Es obligatorio mantener enlaces robustos. Cada archivo temático **DEBE** contener:
  - Enlaces de retorno al padre (`REFERENCE.md`).
  - Enlaces transversales a otros hijos/temas relacionados.
  - Enlaces explícitos a los puntos de entrada principales (los archivos `.lean` fundamentales del tema).

### (1.) Catálogo de módulos Lean

El índice raíz (`REFERENCE.md`) debe listar todos los archivos `.lean` (en `PROJECT_ROOT/` y subdirectorios) con su ubicación, espacio de nombres (*namespace*), dependencias y enlazarlos a su documento temático (`doc/REFERENCE-*.md`) correspondiente.

### (2.) Dependencias de módulos

Cada módulo debe documentar claramente (en su respectivo archivo temático) de qué módulos depende y qué módulos dependen de él. Esto es crítico para la navegación de la IA sin tener que cargar el proyecto completo.

### (3.) Espacios de nombres (Namespaces)

Los namespaces no son necesariamente iguales a los módulos. Documentar en el sistema REFERENCE qué namespaces existen, a qué módulos pertenecen y cómo se relacionan entre sí. Todos los namespaces deben derivar de `PROJECT_NAME`.

### (4.) Definiciones introducidas

Para cada módulo y namespace, documentar todas las definiciones en su archivo temático correspondiente indicando:

- **(4.1) Firma y notación:** Firma en Lean 4 más la notación matemática pura (sin explicaciones).
- **(4.2) Computabilidad:** Indicar si es `computable` o `noncomputable`, si tiene contraparte booleana y si es decidible.
- **(4.3) Bien-fundación:** Indicar si incluye prueba de terminación (`termination_by`).
- **(4.4) Notación:** Registrar notaciones introducidas (infijo, prefijo, macros), símbolos usados y prioridades.

### (5.) Axiomas

Cada axioma debe documentar su ubicación (módulo, namespace) y su relación con las definiciones dentro del archivo temático pertinente.

### (6.) Formato estricto para Axiomas y Definiciones

Proporcionar siempre:

- Notación matemática pura (legibilidad humana).
- Firma exacta en Lean 4.
- Dependencias necesarias para construir la definición/axioma.

### (7.) Teoremas (Sin pruebas)

Los teoremas principales deben documentarse **sin ningún tipo de prueba**, solo con:

- Notación matemática.
- Firma exacta en Lean 4.
- Ubicación (módulo, namespace).

### (8.) Prohibición de contenido no probado

Nada que no esté probado entra en el sistema REFERENCE. **Cero TODOs, cero teoremas pendientes.** Solo lo que ya compila y está demostrado en los archivos `.lean`.

### (9.) Trazabilidad y actualización

Actualizar el archivo `doc/REFERENCE-{tema}.md` correspondiente cada vez que se modifique un archivo `.lean`. Registrar la fecha de modificación del archivo proyectado.

### (10.) Autosuficiencia

El sistema REFERENCE completo debe contener suficiente información para escribir nuevos módulos o pruebas **sin cargar el resto del proyecto**.

### (11–14.) Protocolo de "Proyección" y Exportaciones

- "Proyectar" significa trasladar todo lo público de un `.lean` al archivo `doc/REFERENCE-{tema}.md` que le corresponda.
- Todo lo exportable (no `private`) **DEBE** proyectarse y **DEBE** aparecer en el bloque `export` del archivo `.lean`.

---

## Formato y Estilo de Código

### (15.) Argumentos implícitos y alineación

Para mantener la legibilidad en firmas complejas, las declaraciones largas deben dividirse. El símbolo `:=` y `by` deben estar tabulados o en líneas separadas de forma limpia.

```lean
private theorem singleton_eq_pair {a b c : Type}
  (h : singleton a = pair b c) :
    a = b ∧ a = c
      := by
  ...
```

### (16.) Excepción de una línea (One-liner term-mode)

Si la declaración completa (nombre, parámetros, tipo, `:=` y cuerpo) cabe cómodamente en una sola línea (≤ 90 caracteres) y la prueba es un término trivial, se prefiere la forma compacta:

```lean
theorem subset_refl (A : Type) : A ⊆ A := fun _ h => h
```

---

## Arquitectura de Exportaciones y Directorios

### (17.) Bloques de Exportación (*Export blocks*)

Todo módulo de producción (hoja) **DEBE** terminar con un bloque `export` que liste todas las definiciones, teoremas y lemas públicos. Las declaraciones `private` (o con sufijo `_aux`) nunca se exportan.

```lean
-- Al final del archivo, fuera del namespace
export PROJECT_NAME.SubModulo (add_comm add_assoc)
```

### (18.) Archivos "Barrel" (Paraguas)

Cualquier subdirectorio con 2+ módulos en `PROJECT_ROOT/` debe tener un archivo barrel (ej. `PROJECT_ROOT/Algebra.lean` para el directorio `PROJECT_ROOT/Algebra/`) que importe todos sus submódulos. Estos archivos **no contienen código**, solo sentencias `import`.

---

## Sistema de Bloqueo de Archivos

Implementado vía `git-lock.bash` para proteger módulos completos de alteraciones accidentales.

| Nivel | Comando | Propósito |
| --- | --- | --- |
| **Lock** | `bash git-lock.bash lock <file>` | Bloqueo temporal de sesión para trabajar en un solo archivo a la vez. |
| **Freeze** | `bash git-lock.bash freeze <file>` | Módulo completado (✅). Inmutable para siempre. |

### (19.) Extensiones de Módulos Congelados (*Frozen*)

Si un módulo congelado `Foo.lean` necesita nuevo contenido, no se descongela. Se crea `FooExt.lean` (o preferiblemente un nombre semántico como `FooDivisibility.lean`), que importa a `Foo.lean` y reabre su namespace.

---

## Trazabilidad y Documentación Anexa

### (20.) Marcas de Tiempo

Todos los archivos de documentación técnica (`REFERENCE`, `CHANGELOG`, `STATUS`, etc.) deben incluir una marca de tiempo bajo el título en formato `YYYY-MM-DD HH:MM`.

### (21.) Encabezado de Copyright

Todos los archivos `.lean` sin excepción deben comenzar con:

```lean
/-
Copyright (c) YYYY. All rights reserved.
Author: [Nombre del Autor]
License: MIT
-/
```

### (22.) Anotaciones para la IA

En los archivos `doc/REFERENCE-{tema}.md`, usar etiquetas de contexto:

- `@axiom_system`: (ej. `PROJECT_NAME`)
- `@importance`: `high` (usado por 3+ módulos), `medium` (1–2), `low` (interno).

### (23.) Archivos de Referencia Cruzada

La documentación del proyecto se divide en los siguientes archivos complementarios:

| Archivo | Propósito |
| ------- | --------- |
| `REFERENCE.md` & `doc/REFERENCE-*.md` | Sistema de referencia en árbol interconectado. |
| `NAMING-CONVENTIONS.md` | Reglas estrictas de nomenclatura estilo Mathlib. |
| `PLANNING.md` | Visión a largo plazo y hoja de ruta extendida (actúa como un `NEXT-STEPS.md` de alto nivel). |
| `NEXT-STEPS.md` | Fases planificadas y tabla de sorries a corto/medio plazo. |
| `THOUGHTS.md` | Diario de decisiones de diseño, ideas y rutas alternativas. |
| `DECISIONS.md` | *Architectural Decision Records* (ADRs) formales. |
| `DEPENDENCIES.md` | Grafo y listado maestro de las dependencias (imports) entre módulos. |
| `WORKFLOW.md` | Metodologías y flujos de trabajo operativos de Git, IA y Lean. |
| `CURRENT-STATUS-PROJECT.md` | Snapshot en vivo del build, jobs y estatus general. |

---

## Comandos Interactivos para la IA

La IA debe obedecer estos comandos exactos cuando el usuario los invoque:

---

### `actualiza doc`

**Propósito:** Sincronizar toda la documentación viva tras una sesión.

**Flujo:**

1. Lee `lake build` (errores, sorries, warnings).
2. Lee estado previo de `NEXT-STEPS.md`, `CHANGELOG.md`, `CURRENT-STATUS-PROJECT.md`.
3. Actualiza `CHANGELOG.md` con los cambios de la sesión y sorries cerrados.
4. Actualiza `NEXT-STEPS.md` (mueve completados, actualiza tabla de sorries).
5. Actualiza `CURRENT-STATUS-PROJECT.md` (snapshot de build y estado de módulos: 🔄 → 🔶 → ✅ → 🧊).
6. Actualiza el árbol de directorios en `AI-GUIDE.md` si hubo cambios estructurales.

---

### `actualiza_documentacion`

**Propósito:** Sincronizar los documentos de alto nivel, estado, dependencias y flujos del proyecto.

**Archivos afectados:** `README.md`, `CURRENT-STATUS-PROJECT.md`, `DECISIONS.md`, `DEPENDENCIES.md`, `WORKFLOW.md`.

**Flujo:**

1. Ejecuta / Lee `lake build` para obtener los datos más recientes (número de jobs, errores, sorries pendientes).
2. Actualiza `CURRENT-STATUS-PROJECT.md` reflejando el progreso de los módulos y el resumen de compilación.
3. Actualiza `README.md` con las métricas actuales del repositorio y ajusta la descripción si se ha alcanzado algún hito mayor.
4. Actualiza `DECISIONS.md` si se han tomado decisiones arquitectónicas o de convenciones nuevas durante la sesión (añadiendo un nuevo ADR).
5. Actualiza `DEPENDENCIES.md` revisando si se han creado nuevos archivos `.lean` o modificado las sentencias `import`, ajustando el grafo de dependencias acorde.
6. Revisa y actualiza `WORKFLOW.md` si la dinámica de la sesión requiere asentar una nueva regla de trabajo operativa.

---

### `pon_al_dia_el_plan`

**Propósito:** Limpiar y sincronizar la planificación del proyecto, eliminando el ruido de tareas ya completadas.

**Archivos afectados:** `NEXT-STEPS.md`, `PLANNING.md`, `THOUGHTS.md`.

**Flujo:**

1. Revisa detenidamente lo logrado en la sesión actual y cruza esta información con `THOUGHTS.md` y `PLANNING.md` para identificar qué tareas o ideas se han materializado.
2. Limpia exhaustivamente `NEXT-STEPS.md`, simplificando y eliminando cualquier rastro de elementos, fases o tareas que ya estén hechos (evitando la acumulación de tareas fantasma).
3. Promueve objetivos estructurados desde la visión a largo plazo (`PLANNING.md`) hacia las siguientes fases activas de `NEXT-STEPS.md`.

---

### `revisa_pensamientos`

**Propósito:** Analizar las notas de diseño y proponer próximos pasos.

**Archivos afectados:** `THOUGHTS.md`.

**Flujo:**

1. Lee íntegramente `THOUGHTS.md`.
2. Extrae y categoriza las ideas discutidas (decisiones pendientes, refactorizaciones imaginadas, dudas).
3. Responde en el chat con comentarios constructivos: qué ideas están lo suficientemente maduras para pasar a `NEXT-STEPS.md`, cuáles requieren más investigación y posibles soluciones a dilemas de diseño planteados en el archivo.

---

### `compila_y_comprueba`

**Propósito:** Ejecutar una comprobación exhaustiva del proyecto y dejar un registro verboso.

**Archivos afectados:** `build_report.txt` (sobrescrito en cada llamada).

**Flujo:**

1. Ejecuta el comando de compilación completo del proyecto (`lake build`).
2. Captura toda la salida estándar y de errores (warnings, sorries, outputs, jobs).
3. Escribe/Sobrescribe el archivo `build_report.txt` con el volcado íntegro de esta compilación.
4. Informa brevemente en el chat del resultado global (éxito/fracaso y número de errores si los hay) invitando a revisar el fichero generado para más detalles.

---

### `dame_situación`

**Propósito:** Reporte de solo lectura del estado actual.

**Salida:** Resumen con Jobs/Errores/Sorries, Tabla de sorries vigentes, Último cambio en Changelog, Módulos incompletos, y Próximo objetivo.

---

### `proyecta`

**Propósito:** Actualización local y exhaustiva del sistema REFERENCE para un archivo o sesión específica.

**Flujo:** Siguiendo estrictamente las reglas de esta guía (secciones 1 a 14), extrae todo el contenido público (listado en el bloque `export`) de los archivos modificados. Transfiere esa información al archivo temático `doc/REFERENCE-{campo}.md` que corresponda, formateándola de manera exhaustiva (firma exacta de Lean 4, notación pura, computabilidad, dependencias). Asegúrate de actualizar el índice raíz (`REFERENCE.md`) si se trata de un archivo temático nuevo.

---

### `repasa_y_proyecta`

**Propósito:** Sincronización masiva y profunda de todo el repositorio hacia el árbol REFERENCE.

**Flujo:** Recorre exhaustivamente módulo por módulo todo el directorio `PROJECT_ROOT/`. Por cada archivo `.lean`:

1. Lee su bloque `export`.
2. Verifica que cada elemento exportado esté correctamente documentado en su `doc/REFERENCE-{campo}.md` respectivo.
3. Detecta "elementos fantasma" en todo el árbol de referencias (declaraciones eliminadas, renombradas o devueltas a `private` en el código fuente) y los elimina.
4. Asegura la coherencia de fechas, jerarquía de dependencias, enlaces de navegación fuerte, y actualiza el índice general `REFERENCE.md`.

---

### `guarda_y_sube`

**Propósito:** Flujo de Git seguro y ciclo completo de actualización del repositorio preservando los bloqueos locales.

**Flujo exacto a ejecutar:**

1. Ejecutar `lake build` para garantizar que no hay errores de compilación.

2. Descongelar los archivos Lean en los que se ha estado trabajando:

   ```bash
   bash git-lock.bash unlock modulo_1.lean ... modulo_n.lean
   ```

3. Añadir todos los cambios al staging area:

   ```bash
   git add *
   ```

4. Crear el commit:

   ```bash
   git commit -m "mensaje muy descriptivo de lo hecho"
   ```

5. Subir los cambios al repositorio remoto:

   ```bash
   git push
   ```

6. Volver a congelar los mismos archivos por seguridad:

   ```bash
   bash git-lock.bash lock modulo_1.lean ... modulo_n.lean
   ```
