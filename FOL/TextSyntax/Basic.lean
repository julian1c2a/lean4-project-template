/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import FOL.FOL

namespace FOL.TextSyntax

/-!
# Sintaxis Basada en Texto (Cadenas y Símbolos)

Este módulo proporciona una representación alternativa de las fórmulas de la Lógica
de Primer Orden (FOL) utilizando listas de símbolos o caracteres explícitos,
en paralelo al enfoque basado en Árboles de Sintaxis Abstracta (AST) de `FOL.lean`.
-/

/-- Un alfabeto básico para Lógica de Primer Orden usando símbolos explícitos -/
inductive Symbol where
  | fvar (name : String)    -- Variables Libres (x, y, z...)
  | bvar (index : Nat)      -- Variables Acotadas (Ligadas) con índices de De Bruijn
  | func (name : String)    -- Funciones (f, g, h...)
  | pred (name : String)    -- Predicados (P, Q, R...)
  | forall_sym              -- ∀
  | exists_sym              -- ∃
  | and_sym                 -- ∧
  | or_sym                  -- ∨
  | impl_sym                -- ⇒
  | iff_sym                 -- ⇔
  | not_sym                 -- ¬
  | eq_sym                  -- ≐
  | bottom_sym              -- ⊥
  | lparen                  -- (
  | rparen                  -- )
  | comma                   -- ,
  deriving Repr, BEq

/-- En esta representación, un Término es simplemente una lista de símbolos -/
abbrev TextTerm := List Symbol

/-- De la misma manera, una Fórmula es una lista de símbolos secuenciales -/
abbrev TextFormula := List Symbol

/-- Funciones de ayuda para mostrar símbolos como texto -/
def Symbol.toString : Symbol → String
  | fvar n     => n
  | bvar i     => s!"v_{i}"
  | func n     => n
  | pred n     => n
  | forall_sym => "∀"
  | exists_sym => "∃"
  | and_sym    => "∧"
  | or_sym     => "∨"
  | impl_sym   => "⇒"
  | iff_sym    => "⇔"
  | not_sym    => "¬"
  | eq_sym     => "≐"
  | bottom_sym => "⊥"
  | lparen     => "("
  | rparen     => ")"
  | comma      => ","

instance : ToString Symbol := ⟨Symbol.toString⟩

/-- Heurística para saber si hay que añadir un espacio después de s1 y antes de s2 -/
def needsSpace (s1 s2 : Symbol) : Bool :=
  match s1, s2 with
  | Symbol.func _, Symbol.lparen => false
  | Symbol.pred _, Symbol.lparen => false
  | Symbol.lparen, Symbol.fvar _ => false
  | Symbol.lparen, Symbol.bvar _ => false
  | Symbol.lparen, Symbol.func _ => false
  | _, Symbol.comma              => false
  | Symbol.fvar _, Symbol.rparen => false
  | Symbol.bvar _, Symbol.rparen => false
  | Symbol.rparen, Symbol.rparen => false
  | Symbol.not_sym, _            => false
  | _, _                         => true

/-- Función auxiliar para procesar la lista de símbolos y añadir espacios lógicos -/
def textFormulaToStringAux : List Symbol → String
  | [] => ""
  | [s] => toString s
  | s1 :: s2 :: rest =>
    let sep := if needsSpace s1 s2 then " " else ""
    toString s1 ++ sep ++ textFormulaToStringAux (s2 :: rest)

/-- Convertir una fórmula/término de texto a una cadena legible -/
def textFormulaToString (f : List Symbol) : String :=
  textFormulaToStringAux f

/-- Traducir un Término (AST) a TextTerm (lista de símbolos) -/
partial def termToText (t : Term) : TextTerm :=
  match t with
  | .bvar n => [Symbol.bvar n]
  | .fvar s => [Symbol.fvar s]
  | .func f ts =>
    let args := ts.map termToText
    let argList := (args.intersperse [Symbol.comma]).foldr (· ++ ·) []
    [Symbol.func f, Symbol.lparen] ++ argList ++ [Symbol.rparen]

/-- Traducir una Fórmula (AST) a TextFormula (lista de símbolos).
    `depth` lleva la cuenta de la profundidad de cuantificadores para las variables ligadas. -/
def formulaToText (depth : Nat) (f : Formula) : TextFormula :=
  match f with
  | .bottom => [Symbol.bottom_sym]
  | .eq t1 t2 => [Symbol.lparen] ++ termToText t1 ++ [Symbol.eq_sym] ++ termToText t2 ++ [Symbol.rparen]
  | .atom p ts =>
    if ts.isEmpty then
      [Symbol.pred p]
    else
      let args := ts.map termToText
      let argList := (args.intersperse [Symbol.comma]).foldr (· ++ ·) []
      [Symbol.pred p, Symbol.lparen] ++ argList ++ [Symbol.rparen]
  | .impl f1 f2 => [Symbol.lparen] ++ formulaToText depth f1 ++ [Symbol.impl_sym] ++ formulaToText depth f2 ++ [Symbol.rparen]
  | .and f1 f2 => [Symbol.lparen] ++ formulaToText depth f1 ++ [Symbol.and_sym] ++ formulaToText depth f2 ++ [Symbol.rparen]
  | .or f1 f2 => [Symbol.lparen] ++ formulaToText depth f1 ++ [Symbol.or_sym] ++ formulaToText depth f2 ++ [Symbol.rparen]
  | .forall f1 => [Symbol.forall_sym, Symbol.bvar depth, Symbol.lparen] ++ formulaToText (depth + 1) f1 ++ [Symbol.rparen]
  | .ex f1 => [Symbol.exists_sym, Symbol.bvar depth, Symbol.lparen] ++ formulaToText (depth + 1) f1 ++ [Symbol.rparen]

end FOL.TextSyntax
