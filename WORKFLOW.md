# Development Workflow

**Autor**: [Nombre del Autor]
**Última actualización:** YYYY-MM-DD

Guía operativa del proyecto. Cubre los **dos modos** activos: sesiones con asistente IA
(**modo principal**) y trabajo humano con `git-lock.bash` (legacy, opcional).

> **Por qué este orden.** Durante mucho tiempo esta guía presentaba `git-lock.bash` como
> el flujo obligatorio y las sesiones de IA como una nota a pie. La práctica real en los
> proyectos hermanos es la contraria, y mantener la ficción tenía un coste medible: en
> varios repos `locked_files.txt` llevaba vacío desde el primer commit — un sistema
> documentado pero no usado, que no protege nada y confunde a quien llega.

---

## Parte 1 — Arrancar un proyecto nuevo desde la plantilla

### Paso 1 — Clonar la plantilla

```bash
git clone https://github.com/your-username/lean4-project-template MyProject
cd MyProject
```

### Paso 2 — Ejecutar el setup

```bash
bash setup.bash MyProject "Your Full Name" your-github-username
```

Ese único comando:

- Renombra `ProjectName/` → `MyProject/` y `ProjectName.lean` → `MyProject.lean`
- Sustituye `ProjectName`, `Your Name`, `your-username` en todos los ficheros
- Actualiza el año de copyright
- Commitea el resultado

### Paso 3 — Instalar el hook de git (solo si vas a usar el modo humano)

```bash
bash git-lock.bash init
```

Instala el hook `pre-commit`, que bloquea commits que toquen ficheros bloqueados y avisa
de `sorry` en los ficheros staged. Se ejecuta una vez por máquina/clon: el hook vive en
`.git/hooks/`, que no se versiona.

> **NO ejecutes `git init` ni `lake init`.**
>
> - `git init` ya lo hizo `git clone`; repetirlo reinicializa el repo y rompe el historial.
> - `lake init` sobreescribiría `lakefile.lean` con uno por defecto, perdiendo la
>   configuración de la plantilla (`autoImplicit=false`, `globs`, dependencias comentadas).
>
> Si activas una dependencia en `lakefile.lean`, usa `lake update` (no `lake init`).

### Paso 4 — Crear el repositorio y subirlo

```bash
# Opción A: con gh CLI
gh repo create MyProject --public --source=. --push

# Opción B: manualmente
git remote add origin https://github.com/your-username/MyProject.git
git push -u origin master
```

### Paso 5 — Personalizar

| Fichero | Qué actualizar |
|------|----------------|
| `DECISIONS.md` | **⚠️ Primero: la sección MANDATORIES.** Las directivas no negociables del proyecto (pureza constructiva, tipo base exclusivo, política de axiomas). Si no hay ninguna, **decláralo explícitamente** |
| `README.md` | Descripción del proyecto, tabla de módulos |
| `lakefile.lean` | Dependencias externas; `globs` si se quiere |
| `NAMING-CONVENTIONS.md` | §9 «convenciones locales» — las reglas de nombres propias del dominio |
| `check-doc-sync.bash` | El bloque `CONFIGURACIÓN`: documentos autoritativos y `SYMBOL_PREFIXES` |
| `NEXT-STEPS.md` | Fases iniciales de desarrollo |
| `THOUGHTS.md` | Filosofía de diseño y decisiones iniciales |
| `LICENSE` | Nombre del autor y año |

---

## Parte 2 — Modo IA (flujo principal)

Sesiones colaborativas con Claude Code (u otro asistente). Sin locks por fichero; el
control de cambios se hace por **commits frecuentes + build verde como gate**.

### Ciclo de trabajo típico

1. **Orientación**: el asistente lee `AI-GUIDE.md` (protocolo), **`DECISIONS.md`
   §MANDATORIES (obligatorio antes de tocar un `.lean`)**, `REFERENCE.md` (mapa del
   proyecto), `NEXT-STEPS.md` (qué toca ahora), `CURRENT-STATUS-PROJECT.md` (sorrys +
   módulos) y `MEMORY.md` si existe (checkpoints de sesiones previas).
2. **Edición directa**: el asistente modifica `.lean` con `Edit`/`Write`; cada cambio
   significativo seguido de `lake build` para detectar regresiones inmediatas.
3. **Commit frecuente** tras cada milestone (un módulo cerrado, un axioma eliminado, una
   doc actualizada), en formato Conventional Commits informal.
4. **Push** al final de cada milestone — no esperar al final de la sesión.
5. **Doc sync** al cerrar un bloque: actualizar `REFERENCE.md`, `CHANGELOG.md`,
   `CURRENT-STATUS-PROJECT.md`, `NEXT-STEPS.md`, y **dejar `bash check-doc-sync.bash`
   en verde** (AI-GUIDE §27).
6. **Checkpoint** al cerrar sesión: estado + siguiente paso, indexado en `MEMORY.md`.

### Gate de calidad

* `lake build` debe pasar (exit 0) **antes de commitear**.
* `bash check-doc-sync.bash` en verde antes de cerrar una pasada de documentación.
  ⚠️ Corregir el **cuerpo** de los documentos, no solo su banner.
* La línea base de `sorry` del proyecto se declara en `CURRENT-STATUS-PROJECT.md`.
  Cualquier `sorry` nuevo exige justificación explícita en el commit.
* Ninguna MANDATORY de `DECISIONS.md` puede quedar violada: su incumplimiento es un
  **defecto de build**, no una preferencia de estilo.

### Comandos formales (definidos en `AI-GUIDE.md` §«Comandos Interactivos para la IA»)

| Comando | Qué hace |
|---|---|
| `dame situación` | Reporte read-only: build, sorrys, módulos, último cambio |
| `actualiza doc` | Pasada completa de documentación tras una sesión de desarrollo |
| `proyecta` | Extrae los `export` nuevos a `REFERENCE.md` y sus nodos |
| `repasa_y_proyecta` | Revisión completa + caza de elementos fantasma |
| `guarda y sube` | Build + docsync + commit + push |

### Convención de commits

```text
<tipo>(<scope>): <resumen corto>

<cuerpo opcional: el porqué, decisiones, pendientes>

Co-Authored-By: Claude Opus X.Y <noreply@anthropic.com>
```

Tipos: `feat`, `fix`, `chore`, `docs`, `refactor`. El scope suele ser el módulo tocado.

---

## Parte 3 — Modo humano legacy (`git-lock.bash`)

Flujo histórico con bloqueos explícitos por fichero (ADR-003). **No se usa en sesiones
IA**, pero la infraestructura sigue disponible y es útil para congelar módulos terminados.

### La regla de un solo fichero

> **A lo sumo un `.lean` puede estar desbloqueado en cualquier momento.**

```bash
bash git-lock.bash list                      # qué hay desbloqueado
bash git-lock.bash unlock MyProject/X.lean   # desbloquea para editar
# … editar X.lean …
bash git-lock.bash lock   MyProject/X.lean   # bloquea al terminar
```

Si cambias de fichero a mitad de sesión: `lock` el actual antes del `unlock` del siguiente.

### Congelado permanente

Los módulos terminados pueden marcarse como inmutables (`bash git-lock.bash freeze`).
Las extensiones se hacen entonces vía `*Ext.lean` (ver `AI-GUIDE.md` §21).

⚠️ **Si adoptas este modo, úsalo de verdad.** Un `locked_files.txt` permanentemente vacío
es peor que no tener el sistema: da una falsa sensación de protección.

---

## Parte 4 — Protocolo de commit

```bash
# 1. Compilar
make build

# 2. Sorrys
make sorry

# 3. Documentación al día (AI-GUIDE §12 y §27)
make docsync

# 4. Stage de ficheros CONCRETOS (evitar git add -A)
git add MyProject/ModuleName.lean REFERENCE.md CHANGELOG.md

git commit -m "feat(ModuleName): N definiciones y M teoremas"
git push origin master
```

---

## Parte 5 — Toolchain

```bash
bash update-toolchain.bash            # prueba la última estable publicada
bash update-toolchain.bash v4.31.0    # prueba una versión concreta
bash update-toolchain.bash --check    # solo informa si hay una más nueva
```

Compila la librería completa con la versión nueva; commitea si pasa y **revierte
automáticamente** si falla.

> ⚠️ Un bump que rompe el build casi nunca es un problema matemático: suele ser una
> divergencia de `simp`/`omega` entre versiones (cambia la forma normal y un `simpa`
> deja de cerrar la meta). Se arregla en la prueba concreta. Si el proyecto tiene
> dependencias locales, todas deben subir a la vez.

---

## Parte 6 — Mantenimiento

```bash
bash gen-root.bash                    # regenera el barrel raíz MyProject.lean
bash new-module.bash ModuleName       # crea MyProject/ModuleName.lean desde plantilla
bash new-module.bash Topic/SubModule  # idem, anidado
bash check-sorry.bash                 # cuenta sorrys reales
bash check-doc-sync.bash --quick      # doc ↔ código, sin build
bash git-lock.bash list               # estado lock/frozen
```

Si añades un módulo a mano (sin `new-module.bash`), ejecuta `gen-root.bash` para
sincronizar el import raíz.

---

## Parte 7 — Ficheros clave

| Fichero | Propósito |
|---|---|
| `AI-GUIDE.md` | **Lee primero**: protocolos, formato, comandos formales. Universal |
| `DECISIONS.md` | ADRs + **MANDATORIES**. Lo específico de ESTE proyecto. Lectura obligatoria |
| `REFERENCE.md` (+ `doc/REFERENCE-*.md`) | Mapa técnico: módulos, defs, teoremas, axiomas |
| `NEXT-STEPS.md` | Qué toca ahora. Se actualiza cada sesión |
| `PLANNING.md` | Plan estratégico de largo plazo |
| `CURRENT-STATUS-PROJECT.md` | Snapshot del build + métricas |
| `CHANGELOG.md` | Historia cronológica (diario: sus cifras son históricas por diseño) |
| `DEPENDENCIES.md` | Grafo de dependencias, verificado contra los `import` reales |
| `NAMING-CONVENTIONS.md` | Convenciones Mathlib-style, 12 reglas de formación |
| `THOUGHTS.md` | Diario informal, no normativo |
| `WORKFLOW.md` | Este fichero |

---

## Referencia rápida

```bash
bash setup.bash Name "Author" user   # inicializar proyecto nuevo
bash git-lock.bash init              # instalar hook (una vez por clon)
make new NAME=Module                 # crear módulo nuevo
make build                           # compilar
make sorry                           # buscar sorrys
make docsync                         # doc ↔ código (AI-GUIDE §27)
make status                          # lock + sorry
bash gen-root.bash                   # regenerar imports raíz
bash update-toolchain.bash vX.Y.Z    # actualizar Lean
```
