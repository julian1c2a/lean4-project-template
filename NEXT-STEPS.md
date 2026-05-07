# Next Steps — ProjectName

**Last updated:** 2025-01-01 00:00
**Author**: Your Name

> This file tracks planned development phases (short-to-medium term). Each phase includes
> objectives, modules to create, dependencies, and estimated complexity.
> For long-term goals and strategic roadmap, see [PLANNING.md](PLANNING.md).

---

## Phase 1: Foundations

**Objective**: Establish core infrastructure in `Prelim.lean`.

**Modules**:

- [ ] `Prelim.lean` — ExistsUnique, basic infrastructure

**Dependencies**: None (Level 0)
**Complexity**: Simple

---

## Phase 2: Core Modules

**Objective**: Build the first domain-specific modules.

**Modules**:

- [ ] `Topic/Basic.lean` — Core definitions
- [ ] `Topic/Properties.lean` — Fundamental properties

**Dependencies**: Phase 1 complete
**Complexity**: Medium

---

## Phase 3: Naming Migration

**Objective**: Ensure all identifiers follow Mathlib naming conventions.

**Modules**: All existing modules
**Reference**: [NAMING-CONVENTIONS.md](NAMING-CONVENTIONS.md)

**Steps**:

1. Audit all exported names against NAMING-CONVENTIONS.md
2. Rename definitions: `UpperCamelCase` for Prop, `lowerCamelCase` for functions
3. Rename theorems: `subject_predicate` pattern with standard suffixes
4. Verify full compilation after each rename batch
5. Update REFERENCE.md with new names

**Dependencies**: Phase 2 substantially complete
**Complexity**: Medium (mechanical but requires full recompilation)

---

## Phase 4: Annotations and Documentation

**Objective**: Add `@importance` and `@axiom_system` annotations to REFERENCE.md.

**Steps**:

1. Classify each module by axiom system
2. Rate importance of each theorem (high/medium/low)
3. Update REFERENCE.md §3 with annotations

**Dependencies**: Phase 3 complete
**Complexity**: Simple

---

## Future Phases

*(Add new phases here as the project grows)*

### Phase N: [Title]

**Objective**: ...

**Modules**:

- [ ] ...

**Dependencies**: Phase N-1
**Complexity**: Simple | Medium | Complex

---

## Phase Status Summary

| Phase | Description | Status |
|-------|-------------|--------|
| 1 | Foundations | 🔄 In progress |
| 2 | Core Modules | ❌ Pending |
| 3 | Naming Migration | ❌ Pending |
| 4 | Annotations | ❌ Pending |
