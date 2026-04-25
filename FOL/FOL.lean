/-
  Formalización de Lógica de Primer Orden (FOL) en Lean 4.
  Este archivo define la sintaxis, un sistema de navegación por posiciones
  y un sistema de derivación que permite aplicar reglas en subexpresiones exactas.
-/

-- 1. SINTAXIS: Términos y Fórmulas
-- Usamos índices de De Bruijn para las variables (Nat) para evitar colisiones de nombres.

inductive Term where
  | var  : Nat → Term
  | func : String → List Term → Term
  deriving Repr, BEq

inductive Formula where
  | bottom : Formula
  | eq     : Term → Term → Formula
  | atom   : String → List Term → Formula
  | impl   : Formula → Formula → Formula
  | forall : Formula → Formula
  | and    : Formula → Formula → Formula
  | or     : Formula → Formula → Formula
  | ex     : Formula → Formula
  deriving Repr, BEq

-- Definición de conectores lógicos derivados
def neg (f : Formula) : Formula := Formula.impl f Formula.bottom

def top : Formula := neg Formula.bottom

def iff (f1 f2 : Formula) : Formula := Formula.and (Formula.impl f1 f2) (Formula.impl f2 f1)

-- Notaciones para hacer las fórmulas legibles
notation "⊥" => Formula.bottom
notation "⊤" => top
prefix:75 "¬ " => neg
infix:50 " ≐ " => Formula.eq
infixr:70 " ∧ " => Formula.and
infixr:65 " ∨ " => Formula.or
infixr:60 " ⇒ " => Formula.impl
infix:55 " ⇔ " => iff
prefix:80 "∀. " => Formula.forall
prefix:80 "∃. " => Formula.ex

-- Coerción para escribir átomos proposicionales más fácilmente (ej. "P" en lugar de .atom "P" [])
instance : Coe String Formula where
  coe s := Formula.atom s []

-- Notación para variables de De Bruijn
prefix:max "#" => Term.var

-- 1.5. LIFT Y SUSTITUCIÓN (De Bruijn)

-- LIFT (Desplazamiento de índices libres)
-- Aumenta en 1 las variables libres a partir de la profundidad 'c'
mutual
def liftTerm (c : Nat) (t : Term) : Term :=
  match t with
  | .var n => if n < c then .var n else .var (n + 1)
  | .func f ts => .func f (liftTerms c ts)

def liftTerms (c : Nat) (ts : List Term) : List Term :=
  match ts with
  | [] => []
  | t :: ts' => liftTerm c t :: liftTerms c ts'
end

def liftFormula (c : Nat) (f : Formula) : Formula :=
  match f with
  | .bottom => .bottom
  | .eq t1 t2 => .eq (liftTerm c t1) (liftTerm c t2)
  | .atom p ts => .atom p (liftTerms c ts)
  | .impl f1 f2 => .impl (liftFormula c f1) (liftFormula c f2)
  | .forall f1 => .forall (liftFormula (c + 1) f1)
  | .and f1 f2 => .and (liftFormula c f1) (liftFormula c f2)
  | .or f1 f2 => .or (liftFormula c f1) (liftFormula c f2)
  | .ex f1 => .ex (liftFormula (c + 1) f1)

-- SUSTITUCIÓN
-- Reemplaza la variable libre 'v' con el término 's'
mutual
def substTerm (v : Nat) (s : Term) (t : Term) : Term :=
  match t with
  | .var n =>
      if n = v then s
      else if n > v then .var (n - 1)
      else .var n
  | .func f ts => .func f (substTerms v s ts)

def substTerms (v : Nat) (s : Term) (ts : List Term) : List Term :=
  match ts with
  | [] => []
  | t :: ts' => substTerm v s t :: substTerms v s ts'
end

def substFormula (v : Nat) (s : Term) (f : Formula) : Formula :=
  match f with
  | .bottom => .bottom
  | .eq t1 t2 => .eq (substTerm v s t1) (substTerm v s t2)
  | .atom p ts => .atom p (substTerms v s ts)
  | .impl f1 f2 => .impl (substFormula v s f1) (substFormula v s f2)
  | .forall f1 => .forall (substFormula (v + 1) (liftTerm 0 s) f1)
  | .and f1 f2 => .and (substFormula v s f1) (substFormula v s f2)
  | .or f1 f2 => .or (substFormula v s f1) (substFormula v s f2)
  | .ex f1 => .ex (substFormula (v + 1) (liftTerm 0 s) f1)

-- 2. NAVEGACIÓN: Posiciones en el árbol (AST)
-- Una posición es un camino desde la raíz hasta una subfórmula.

inductive Pos where
  | root  : Pos
  | left  : Pos → Pos   -- Lado izquierdo de op binaria
  | right : Pos → Pos   -- Lado derecho de op binaria
  | body  : Pos → Pos   -- Dentro de un cuantificador
  deriving Repr

-- Función para obtener la subfórmula en una posición dada
def getAt? (f : Formula) : Pos → Option Formula
  | .root => some f
  | .left p =>
      match f with
      | .impl f1 _ | .and f1 _ | .or f1 _ => getAt? f1 p
      | _ => none
  | .right p =>
      match f with
      | .impl _ f2 | .and _ f2 | .or _ f2 => getAt? f2 p
      | _ => none
  | .body p =>
      match f with
      | .forall f1 | .ex f1 => getAt? f1 p
      | _ => none

-- Función para reemplazar una subfórmula en una posición exacta
def replaceAt (f : Formula) (p : Pos) (newSub : Formula) : Formula :=
  match p with
  | .root => newSub
  | .left p' =>
      match f with
      | .impl f1 f2 => .impl (replaceAt f1 p' newSub) f2
      | .and f1 f2 => .and (replaceAt f1 p' newSub) f2
      | .or f1 f2 => .or (replaceAt f1 p' newSub) f2
      | _ => f
  | .right p' =>
      match f with
      | .impl f1 f2 => .impl f1 (replaceAt f2 p' newSub)
      | .and f1 f2 => .and f1 (replaceAt f2 p' newSub)
      | .or f1 f2 => .or f1 (replaceAt f2 p' newSub)
      | _ => f
  | .body p' =>
      match f with
      | .forall f1 => .forall (replaceAt f1 p' newSub)
      | .ex f1 => .ex (replaceAt f1 p' newSub)
      | _ => f

-- 3. REGLAS DE TRANSFORMACIÓN
-- Definimos reglas de reescritura lógica que pueden aplicarse localmente.

inductive LocalRule : Formula → Formula → Prop where
  | commuteImpl   : ∀ A B C, LocalRule (.impl A (.impl B C)) (.impl B (.impl A C))
  -- Se pueden añadir más reglas como De Morgan, etc.

-- 4. SISTEMA DE DERIVACIÓN (Deducción Natural + Reescritura Local)
-- Este predicado 'Derives' certifica que una fórmula es válida bajo un contexto Γ.

inductive Derives : List Formula → Formula → Prop where
  | hyp : ∀ Γ f, f ∈ Γ → Derives Γ f

  -- Reglas estándar de Deducción Natural
  | intro_impl : ∀ Γ A B, Derives (A :: Γ) B → Derives Γ (.impl A B)
  | elim_impl  : ∀ Γ A B, Derives Γ (.impl A B) → Derives Γ A → Derives Γ B

  -- Reglas de conjunción
  | intro_and  : ∀ Γ A B, Derives Γ A → Derives Γ B → Derives Γ (.and A B)
  | elim_and_l : ∀ Γ A B, Derives Γ (.and A B) → Derives Γ A
  | elim_and_r : ∀ Γ A B, Derives Γ (.and A B) → Derives Γ B

  -- Reglas de disyunción
  | intro_or_l : ∀ Γ A B, Derives Γ A → Derives Γ (.or A B)
  | intro_or_r : ∀ Γ A B, Derives Γ B → Derives Γ (.or A B)
  | elim_or    : ∀ Γ A B C, Derives Γ (.or A B) → Derives (A :: Γ) C → Derives (B :: Γ) C → Derives Γ C

  -- Reglas de Cuantificadores
  | intro_forall : ∀ Γ A, Derives (Γ.map (liftFormula 0)) A → Derives Γ (.forall A)
  | elim_forall  : ∀ Γ A t, Derives Γ (.forall A) → Derives Γ (substFormula 0 t A)

  | intro_ex : ∀ Γ A t, Derives Γ (substFormula 0 t A) → Derives Γ (.ex A)
  | elim_ex  : ∀ Γ A B, Derives Γ (.ex A) → Derives (A :: Γ.map (liftFormula 0)) (liftFormula 0 B) → Derives Γ B

  -- Lógica Intuicionista (Ex Falso Quodlibet)
  | bot_elim : ∀ Γ A, Derives Γ ⊥ → Derives Γ A

  -- Reglas de Igualdad
  | eq_refl  : ∀ Γ t, Derives Γ (.eq t t)
  | eq_subst : ∀ Γ A t1 t2, Derives Γ (.eq t1 t2) → Derives Γ (substFormula 0 t1 A) → Derives Γ (substFormula 0 t2 A)

  -- Debilitamiento (Weakening)
  | weakening : ∀ Γ Γ' f, Derives Γ f → (∀ x, x ∈ Γ → x ∈ Γ') → Derives Γ' f

  -- REGLA MAESTRA: Aplicación de regla en subexpresión exacta
  -- Permite transformar 'f' en 'f'' si existe una posición 'p' donde 'sub' se transforma en 'sub''
  | rewrite_at : ∀ Γ f f' p sub sub',
      Derives Γ f →
      getAt? f p = some sub →
      LocalRule sub sub' →
      f' = replaceAt f p sub' →
      Derives Γ f'

infix:50 " ⊢ " => Derives

-- 5. EJEMPLO DE USO
-- Vamos a ver cómo se vería la estructura de una fórmula y su manipulación.

def formula_ejemplo : Formula :=
  .impl (.atom "P" []) (neg (neg (.atom "Q" [])))

-- Queremos aplicar Doble Negación sólo al átomo Q, que está en la posición:
-- Raíz -> Derecha (lado derecho de la implicación)
def posicion_Q : Pos := .right .root

-- La fórmula resultante tras aplicar la regla en esa posición exacta sería:
def formula_simplificada : Formula :=
  replaceAt formula_ejemplo posicion_Q (.atom "Q" [])

-- Comprobación:
-- formula_simplificada es P → Q
