# Plan de Salida a Cadena (String) desde FOL (AST y TextSyntax)

Este documento detalla la estrategia y el diseño para convertir términos y fórmulas desde su representación interna (AST o TextSyntax) a cadenas de caracteres (`String`) altamente legibles.

## 1. Decisiones de Diseño Fundamentales

A partir de las directrices establecidas:

1. **Ruta de Conversión:** Se utilizará un enfoque en **dos pasos**:
   - `Formula → TextFormula`: Traducción del Árbol de Sintaxis Abstracta (AST) a la lista lineal de símbolos.
   - `TextFormula → String`: Renderizado de la lista de símbolos a una cadena de texto.
   Esto permite que cualquier mejora en el renderizado beneficie tanto a las fórmulas generadas programáticamente (AST) como a las escritas manualmente con la sintaxis de texto.

2. **Variables Acotadas (De Bruijn):** 
   - Se representarán utilizando el formato `$v_{índice}$` (por ejemplo, `$v_0$`, `$v_1$`).
   - **Regla estricta:** La letra `v` (ni minúscula ni mayúscula) NO se usará jamás para nombrar variables libres, constantes, funciones ni predicados. Esto previene cualquier colisión visual o semántica.

3. **Uso de Paréntesis:**
   - Se utilizarán **paréntesis totales (explícitos)** en cada operación y conectiva binaria para evitar absolutamente toda ambigüedad. 
   - Ejemplo: En lugar de `A ∧ B ∨ C`, la salida estricta será `( ( A ∧ B ) ∨ C )`.

4. **Espaciado y Formato:**
   - La salida utilizará **espaciado generoso** para mejorar la legibilidad.
   - Habrá espacios alrededor de todos los conectores lógicos y de los cuantificadores.
   - Ejemplo de término: `f(x, y)` (espacio después de la coma).
   - Ejemplo de fórmula binaria: `( A ∧ B )` (espacios internos que separan los operandos del operador y de los paréntesis).
   - Ejemplo de cuantificador: `∀ $v_0$ ( P($v_0$) )`.

---

## 2. Detalle de las Transformaciones

### Fase 1: Ajustes en TextSyntax (`TextSyntax/Basic.lean`)
* **Símbolos:** Modificaremos la representación textual de `bvar i` para que imprima `$v_{i}$`.
* **Renderizador base:** Crearemos una función que tome un `TextFormula` y produzca el `String` final con el espaciado correcto. Dado que `TextFormula` es solo una lista de símbolos, la función `textFormulaToString` actual (que concatena sin espacios) será mejorada para insertar espacios lógicos.

### Fase 2: Traducción `Term → TextTerm` y `Formula → TextFormula` (`FOL.lean` o nuevo módulo)
Crearemos las funciones que traduzcan la estructura inductiva al flujo lineal de símbolos.

**Reglas de Traducción para Términos (`termToText`)**:
- `.bvar n` ↦ `[Symbol.bvar n]`
- `.fvar s` ↦ `[Symbol.fvar s]`
- `.func f ts` ↦ `[Symbol.func f, Symbol.lparen] ++ (lista separada por Symbol.comma) ++ [Symbol.rparen]`

**Reglas de Traducción para Fórmulas (`formulaToText`)**:
*NOTA: Se envolverán las operaciones en paréntesis `lparen` y `rparen` según la regla de paréntesis totales.*
- `.bottom` ↦ `[Symbol.bottom_sym]`
- `.eq t1 t2` ↦ `[Symbol.lparen] ++ termToText t1 ++ [Symbol.eq_sym] ++ termToText t2 ++ [Symbol.rparen]`
- `.atom p ts` ↦ Igual que funciones: `[Symbol.pred p, Symbol.lparen] ++ ... ++ [Symbol.rparen]`
- `.impl f1 f2` ↦ `[Symbol.lparen] ++ formulaToText f1 ++ [Symbol.impl_sym] ++ formulaToText f2 ++ [Symbol.rparen]`
- `.and f1 f2` ↦ `[Symbol.lparen] ++ formulaToText f1 ++ [Symbol.and_sym] ++ formulaToText f2 ++ [Symbol.rparen]`
- `.or f1 f2` ↦ `[Symbol.lparen] ++ formulaToText f1 ++ [Symbol.or_sym] ++ formulaToText f2 ++ [Symbol.rparen]`
- `.forall f` ↦ `[Symbol.forall_sym, Symbol.lparen] ++ formulaToText f ++ [Symbol.rparen]` *(Opcional: podemos poner el símbolo explícito de la variable ligada a la que atañe el cuantificador. En De Bruijn puro, el `forall` no indica el índice directamente en la cabeza, pero por legibilidad, si queremos que se lea `∀ $v_0$`, tendremos que analizar la profundidad o simplemente imprimir `∀` y ya).*
- `.ex f` ↦ `[Symbol.exists_sym, Symbol.lparen] ++ formulaToText f ++ [Symbol.rparen]`

**Pregunta para el usuario (Cuantificadores en la salida):**
En índices de De Bruijn, un cuantificador no lleva nombre de variable asociado (ej. `∀. P(#0)`). Al renderizar a texto:
- *Opción Q1:* Imprimimos simplemente `∀ ( ... )` y asumimos que el lector sabe que el índice de mayor valor dentro atañe a este cuantificador.
- *Opción Q2:* Queremos que la salida imprima explícitamente `∀ $v_{profundidad}$ ( ... )`. Para hacer esto, la función `formulaToText` necesitaría un parámetro extra (el contador de profundidad) que se incrementa al pasar por un cuantificador.

---

## 3. Próximos Pasos de Implementación
1. Implementar la impresión base en `Basic.lean` para `$v_{n}$`.
2. Escribir el traductor `Formula → TextFormula`.
3. Escribir la lógica de espaciado en la conversión `TextFormula → String`.
4. Añadir casos de prueba para verificar que `∀. P(#0) ∧ Q(y)` sale exactamente como `( ∀ ( P($v_0$) ) ∧ Q(y) )`.
