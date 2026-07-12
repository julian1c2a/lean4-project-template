# Decisiones de Diseño — ProjectName

**Última actualización:** YYYY-MM-DD
**Autor**: [Nombre del Autor]

Registro de decisiones arquitectónicas (ADR) de este proyecto. Cada entrada documenta
*qué* se decidió y *por qué*, para referencia futura.

> **Este fichero es el lugar de lo específico de ESTE proyecto.** Lo universal
> (aplicable a cualquier proyecto nacido de esta plantilla) vive en `AI-GUIDE.md`. Si
> una regla solo tiene sentido para este proyecto concreto (una directiva fundacional
> como "cero `Classical`", una elección de representación matemática, un mandato sobre
> qué tipo base usar), documéntala aquí — en la sección **MANDATORIES** si es una
> directiva no negociable, o como un ADR normal si es una decisión de diseño reversible.

---

## ⚠️ MANDATORIES (reglas vinculantes de este proyecto — lectura obligatoria)

> Plantilla vacía. Rellenar solo si el proyecto tiene directivas fundacionales no
> negociables — es decir, reglas cuyo incumplimiento se considera un defecto de build,
> no una preferencia de estilo. Ejemplos reales de proyectos hermanos (no aplican aquí
> a menos que se declaren explícitamente):
>
> - *Pureza constructiva*: cero `Classical.*`, footprint objetivo
>   `#print axioms ⊆ {propext, Quot.sound}`, verificado por un gate `#assert_no_classical`.
> - *Tipo base exclusivo*: usar siempre `ℕ₀` de una librería propia y nunca `Nat` de
>   Lean, salvo excepción técnica documentada (kernel, `sizeOf`, `termination_by`).
> - *Cero axiomas espurios*: cualquier `axiom` declarado debe llevar su justificación
>   en `AXIOMS.md` (o equivalente) y, si se demuestra innecesario, se retira en vez de
>   mantenerse "por si acaso".
>
> Si no hay ninguna directiva de este tipo, deja esta sección con el siguiente aviso:
> **"Sin MANDATORIES declaradas — este proyecto no tiene directivas fundacionales no
> negociables más allá de los ADR de abajo."**

---

## ADR-001: Sin dependencia de Mathlib

**Fecha**: YYYY-MM-DD
**Estado**: Aceptado

**Decisión**: este proyecto no depende de Mathlib.

**Justificación**: [explicar por qué — objetivo educativo, rendimiento, evitar el
desgaste de la API de Mathlib, etc.]

**Consecuencias**: toda la infraestructura necesaria (`ExistsUnique`, decidibilidad,
etc.) se construye desde cero.

---

## ADR-002: `autoImplicit = false`

**Fecha**: YYYY-MM-DD
**Estado**: Aceptado

**Decisión**: `moreServerArgs := #["-DautoImplicit=false"]` en `lakefile.lean`.

**Justificación**: las anotaciones de tipo explícitas evitan problemas accidentales de
polimorfismo de universos y hacen el código más legible y mantenible.

**Consecuencias**: todas las variables deben declararse o anotarse explícitamente.

---

## ADR-003: Sistema de bloqueo de archivos

**Fecha**: YYYY-MM-DD
**Estado**: Aceptado

**Decisión**: usar `git-lock.bash` + `locked_files.txt`/`frozen_files.txt` + hook
`pre-commit` para prevenir ediciones accidentales de módulos terminados.

**Justificación**: las pruebas de Lean 4 son frágiles — cambios pequeños en módulos
terminados pueden romper pruebas dependientes. El sistema de bloqueo hace esto
explícito y mecánico en vez de depender de la memoria del desarrollador.

**Consecuencias**: el flujo de trabajo exige bloquear/desbloquear ficheros (ver
`AI-GUIDE.md` §20-21). **Debe usarse de verdad** — un sistema documentado pero con las
listas siempre vacías no aporta nada (lección aprendida en la auditoría cruzada de
2026-07-12: en varios proyectos hermanos llevaba vacío desde el primer commit).

---

## ADR-004: Convenciones de nombres Mathlib

**Fecha**: YYYY-MM-DD
**Estado**: Aceptado

**Decisión**: todos los identificadores siguen las convenciones de nombres de
Mathlib4, documentadas en `NAMING-CONVENTIONS.md`.

**Justificación**: consistencia con el ecosistema Lean 4 más amplio. Hace los teoremas
localizables por patrón de nombre (`mem_X_iff`, `sujeto_predicado`). Facilita una
futura integración con Mathlib si se desea.

**Consecuencias**: puede requerir migración de nombres existentes. Ver
`NAMING-CONVENTIONS.md` para el diccionario completo y las 12 reglas de formación.
`REFERENCE.md` §0 da una referencia rápida.

---

## ADR-005: Namespace plano por fichero — los directorios organizan, no anidan namespaces

**Fecha**: 2026-07-12 (corrige una versión anterior de este ADR que proponía
mirroring completo de directorio; revertido tras auditar la práctica real en Peano)
**Estado**: Aceptado

**Decisión**: cada fichero `.lean` recibe **un namespace propio de un solo nivel**
bajo el namespace raíz del proyecto: `ProjectName/Foo/Bar.lean` →
`namespace ProjectName.Bar` (**no** `ProjectName.Foo.Bar`). El nombre del namespace
suele coincidir con el nombre del fichero (el concepto matemático que trata), no con
su ruta completa. Los subdirectorios (`Foo/`) son **puramente organizativos** —
agrupan ficheros por tema para navegación humana — y **no** determinan el namespace.

Dentro de un mismo fichero puede haber sub-namespaces **más finos** que distingan
sub-conceptos (p. ej. `ProjectName.FSet.ℕ₀FSet`, `ProjectName.FSet.TupleFSet` dentro
de `FSet.lean`) — eso sí está permitido y es el "grano más fino" que complementa la
regla, siempre que quede documentado en el propio fichero.

**Regla derivada — un namespace no se comparte entre ficheros distintos**: si dos
ficheros de un mismo directorio (p. ej. `GroupTheory/Action.lean` y
`GroupTheory/NormalSubgroup.lean`) declaran literalmente el mismo namespace interno
(`namespace GroupTheory`), es casi siempre un descuido, no una decisión — mezcla las
declaraciones de ambos ficheros en un único namespace, dificulta saber qué fichero
define qué símbolo, y arrastra colisiones de nombre silenciosas. Cada fichero
consigue su propio namespace y usa `open Project.OtroFichero` para acceder a lo que
necesite de sus dependencias.

**Justificación**: es la convención que ya sigue de facto la mayoría del código real
de los proyectos de este ecosistema (verificado por auditoría exhaustiva en Peano,
2026-07-12: 57/57 ficheros de producción usaban `Peano.<Concepto>` plano, nunca la
ruta completa de directorio) — codificar aquí lo que el código ya hace evita que la
documentación contradiga la práctica real. Un mapeo 1:1 directorio↔namespace se
vuelve verboso y fragil en proyectos con más de 3-4 niveles de subdirectorios
temáticos (`Combinatorics/GroupTheory/Sylow/Sylow.lean` → `Peano.Sylow`, no
`Peano.Combinatorics.GroupTheory.Sylow.Sylow`).

**Consecuencias**: `new-module.bash` crea el fichero en el subdirectorio indicado
pero declara el namespace con el nombre del fichero, no la ruta completa.
`gen-root.bash` sigue escaneando subdirectorios recursivamente para los `import`,
pero eso es independiente del namespace. Al revisar un PR/commit que introduce un
namespace nuevo, comprobar que ningún otro fichero ya lo usa (`grep -rn "namespace
ProjectName.NombreElegido"` antes de crear el fichero).

---

## ADR-006: Subdirectorios temáticos para la organización de módulos

**Fecha**: YYYY-MM-DD
**Estado**: Aceptado

**Decisión**: agrupar módulos relacionados en subdirectorios temáticos
(`UpperCamelCase`) en vez de mantenerlos todos sueltos en la raíz del proyecto.

**Justificación**: más allá de un puñado de módulos, una carpeta plana deja de ser
navegable. Los subdirectorios temáticos (p. ej. `Algebra/`, `NumberTheory/`,
`Topology/`) hacen explícita la arquitectura matemática del proyecto.

**Consecuencias**: cada subdirectorio con 2+ módulos requiere un barrel (`AI-GUIDE.md`
§18). Ver también ADR-005.

---

## ADR-007: Árbol de documentación `doc/REFERENCE-{tema}.md`

**Fecha**: YYYY-MM-DD
**Estado**: Aceptado

**Decisión**: `REFERENCE.md` es solo el índice raíz; el detalle exhaustivo de cada
subsistema vive en nodos temáticos bajo `doc/REFERENCE-{tema}.md`, con navegación
fuerte bidireccional entre índice y nodos, y entre nodos relacionados entre sí.

**Justificación**: un único `REFERENCE.md` monolítico deja de ser navegable (y de
poder proyectarse de forma incremental) mucho antes de los 100 módulos. Partirlo por
subsistema mantiene cada nodo manejable y evita que sesiones de trabajo aisladas
tengan que cargar todo el proyecto para encontrar una firma.

**Consecuencias**: cada subsistema nuevo lo bastante grande necesita su propio nodo
(`AI-GUIDE.md` §0.5). El comando `proyecta`/`repasa_y_proyecta` debe mantener los
enlaces cruzados al día.

---

## ADR-008: Sistema de anotaciones en REFERENCE.md

**Fecha**: YYYY-MM-DD
**Estado**: Aceptado

**Decisión**: las entradas de REFERENCE.md incluyen anotaciones `@axiom_system` y
`@importance`.

**Justificación**: ayuda a los asistentes de IA a priorizar qué módulos/teoremas
cargar como contexto. Da una clasificación rápida sin tener que leer el código del
módulo.

**Consecuencias**: las anotaciones deben mantenerse al actualizar módulos. Ver
`AI-GUIDE.md` (Sistema de anotaciones para REFERENCE.md).

---

## ADR-009: `NAMING-CONVENTIONS.md` como fichero separado

**Fecha**: YYYY-MM-DD
**Estado**: Aceptado

**Decisión**: las convenciones de nombres viven en un `NAMING-CONVENTIONS.md`
dedicado, con un resumen en `AI-GUIDE.md` y en `REFERENCE.md` §0.

**Justificación**: el diccionario completo con 12 reglas y tablas de migración es
demasiado extenso para `AI-GUIDE.md`. Un fichero separado permite ejemplos detallados
sin sobrecargar la guía principal.

**Consecuencias**: tres lugares referencian el naming: `NAMING-CONVENTIONS.md`
(canónico), `AI-GUIDE.md` (resumen), `REFERENCE.md` §0 (guía de lectura rápida). Los
tres deben mantenerse sincronizados — si divergen, `NAMING-CONVENTIONS.md` es
autoritativo.

---

## Plantilla para nuevas decisiones

## ADR-NNN: [Título]

**Fecha**: YYYY-MM-DD
**Estado**: [Propuesto | Aceptado | Obsoleto | Sustituido por ADR-XXX]

**Contexto**: [¿Por qué hace falta esta decisión?]

**Decisión**: [¿Qué se decidió?]

**Justificación**: [¿Por qué esta opción frente a las alternativas?]

**Consecuencias**: [¿Cuáles son las contrapartidas?]
