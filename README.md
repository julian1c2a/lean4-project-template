# Lógica de Primer Orden con Igualdad (FOL=) en Lean 4

[![Lean 4](https://img.shields.io/badge/Lean-v4.28.0-blue)](https://leanprover.github.io/)
[![Build Status](https://img.shields.io/badge/build-passing-brightgreen)](CURRENT-STATUS-PROJECT.md)
[![License](https://img.shields.io/badge/license-MIT-green)](LICENSE)
[![Coverage](https://img.shields.io/badge/proofs-100%25%20complete-brightgreen)](CURRENT-STATUS-PROJECT.md)

> **Status**: See [CURRENT-STATUS-PROJECT.md](CURRENT-STATUS-PROJECT.md) for complete details

Una formalización matemática profunda y rigurosa de la **Lógica de Primer Orden con Igualdad (FOL=)** en Lean 4. Construida completamente desde cero, **sin dependencias externas** (ni siquiera de Mathlib), alcanzando el **100% de demostraciones completadas (0 sorries)**.

## 📖 Introducción

Este proyecto no es solo una sintaxis; es una recreación desde los primeros principios de cómo funciona la matemática deductiva. Formaliza la **sintaxis**, el sistema de **Deducción Natural**, la **semántica de Tarski** y los **Metateoremas Universales** que gobiernan la lógica de primer orden clásica.

El objetivo ha sido proporcionar una base computacionalmente limpia y verificada algorítmicamente por el kernel de Lean 4 sobre el comportamiento del razonamiento lógico formal.

## ✨ Características Principales

- **Sintaxis Blindada (De Bruijn)**: Implementación de fórmulas y términos mediante índices de De Bruijn. Esto elimina de raíz el problema matemático de la captura y colisión de variables (alfa-equivalencia) en los cuantificadores ($\forall, \exists$).
- **Sistema Deductivo de Vanguardia**: Formalización de un sistema de Deducción Natural completo, extendido nativamente con el axioma de Sustitución de Leibniz para la Igualdad (`eq_subst`) y mecanismos de reescritura de subfórmulas (`LocalRule`).
- **Automatización Integrada**: Uso nativo de metaprogramación (`MetaM`) y macros en Lean 4 para dotar al sistema de tácticas inteligentes (`derive_hyp`, `derive_weaken`, `derive_refl`, `derive_raa`), haciendo las pruebas fluidas.
- **Semántica de Modelos Cocientes**: Definición rigurosa de Modelos semánticos y funciones de evaluación, soportando dominios basados en **Clases de Equivalencia (`Quotient`)** para interpretar la identidad matemática de la igualdad.

## 🏆 Hitos Metamatemáticos Demostrados

Este repositorio contiene pruebas 100% formalizadas en código de los pilares de la metamatemática moderna:

1. **Equivalencias Lógicas (Nivel Objeto):** Doble Negación, Leyes de De Morgan, Dualidad de Cuantificadores, Congruencia de la Igualdad.
2. **Teorema de Deducción:** $\Gamma, A \vdash B \implies \Gamma \vdash A \Rightarrow B$.
3. **Teorema de Corrección (Soundness):** $\Gamma \vdash A \implies \Gamma \models A$.
4. **Lema de Lindenbaum y Construcción de Henkin:** Todo conjunto consistente se puede extender a un conjunto máximamente consistente con testigos existenciales.
5. **Teorema de Completitud de Gödel:** $\Gamma \models A \implies \Gamma \vdash A$.
6. **Teorema de Compacidad:** Un conjunto infinito de fórmulas tiene modelo si y solo si todo subconjunto finito lo tiene.

## 📂 Arquitectura del Proyecto

| Module | Namespace | Dependencies | Status |
|--------|-----------|--------------|--------|
| `Prelim.lean` | `top-level` | `Init.Classical` | ✅ Complete |
| `FOL.lean` | `top-level` | `Prelim.lean` | ✅ Complete |
| `Tactics.lean` | `top-level` | `FOL.lean` | ✅ Complete |
| `Deduction.lean` | `FOL.Metamath.Deduction` | `FOL.lean`, `Tactics.lean` | ✅ Complete |
| `Semantics.lean` | `FOL.Metamath.Semantics` | `FOL.lean` | ✅ Complete |
| `Soundness.lean` | `FOL.Metamath.Soundness` | `Semantics.lean`, `Tactics.lean` | ✅ Complete |
| `Completeness.lean` | `FOL.Metamath.Completeness` | `Semantics.lean`, `Deduction.lean` | ✅ Complete |
| `Compacity.lean` | `FOL.Metamath.Compacity` | `Completeness.lean`, `Soundness.lean` | ✅ Complete |
| `Eq.lean` | `FOL.Theorems.Eq` | `FOL.lean`, `Tactics.lean` | ✅ Complete |

### Estructura de Directorios

```text
FOL/
├── Prelim.lean              # Fundamentos axiomáticos
├── FOL.lean                 # Sintaxis De Bruijn y Deducción Natural (Γ ⊢ f)
├── Tactics.lean             # Macros de automatización (MetaM)
├── Deduction.lean           # Teorema de Deducción
├── Semantics.lean           # Evaluación Semántica, Modelos y Lógica de Cocientes (Γ ⊨ f)
├── Soundness.lean           # Teorema de Corrección
├── Completeness.lean        # Modelo Canónico de Henkin y Completitud
├── Compacity.lean           # Teorema de Compacidad y Consistencia
└── Theorems/                # Demostraciones de Nivel Objeto
    ├── Impl.lean
    ├── Neg.lean
    ├── Derived.lean
    ├── Eq.lean
    └── Quantifiers.lean
```

> As the project grows, organize modules into thematic subdirectories.
> See AI-GUIDE.md §22 for the directory organization protocol.

## Installation

```bash
git clone https://github.com/julian1c2a/ProjectName.git
cd ProjectName
lake build
```

## Requirements

- **Lean 4**: v4.28.0 or later
- **Lake**: Included with Lean 4

## Development Workflow

```bash
# Initialize lock system (first time only)
bash git-lock.bash init

# Create a new module (supports subdirectories)
bash new-module.bash ModuleName
bash new-module.bash Topic/SubModule

# Build
make build

# Check for sorry
make sorry

# Show locked files and sorry status
make status

# Regenerate root import file
bash gen-root.bash
```

> See [WORKFLOW.md](WORKFLOW.md) for the complete development workflow.

## Documentation

| Document | Purpose |
|----------|---------|
| [WORKFLOW.md](WORKFLOW.md) | ⭐ **Complete development workflow** (start here after setup) |
| [REFERENCE.md](REFERENCE.md) | Technical reference for all definitions and theorems |
| [AI-GUIDE.md](AI-GUIDE.md) | Documentation standards, naming conventions, and AI assistant guide |
| [NAMING-CONVENTIONS.md](NAMING-CONVENTIONS.md) | Full Mathlib-style naming dictionary and formation rules |
| [CHANGELOG.md](CHANGELOG.md) | Change history |
| [DEPENDENCIES.md](DEPENDENCIES.md) | Module dependency diagrams |
| [DECISIONS.md](DECISIONS.md) | Architectural Decision Records (ADR) |
| [CURRENT-STATUS-PROJECT.md](CURRENT-STATUS-PROJECT.md) | Current project status and metrics |
| [NEXT-STEPS.md](NEXT-STEPS.md) | Planned development phases |
| [THOUGHTS.md](THOUGHTS.md) | Design journal and ideas |

## Naming Conventions

This project follows [Mathlib4 naming conventions](https://leanprover-community.github.io/contribute/naming.html).
See [NAMING-CONVENTIONS.md](NAMING-CONVENTIONS.md) for the full reference.

**Quick summary:**

| Entity | Convention | Example |
|--------|------------|---------|
| Module | `UpperCamelCase` | `CoreAxioms.lean` |
| Namespace | `UpperCamelCase` | `ProjectName.Topic` |
| Type / Prop predicate | `UpperCamelCase` | `IsSet`, `IsFun` |
| Function / value def | `lowerCamelCase` | `powerset`, `dom` |
| Axiom | `TAG_ShortName` | `ZF_Ext`, `MK_Pair` |
| Theorem | `subject_predicate` | `mem_pair_iff` |

## License

This project is under the MIT License. See [LICENSE](LICENSE) for details.

## Author

Julián Calderón Almendros

## Credits

### Educational Resources

- [add resources here]

### Bibliographic References

- [add references here]

### AI Tools

- Claude Code AI (Anthropic)

---

**Author**: Julián Calderón Almendros
*Last updated: 2026-04-25 21:30*
