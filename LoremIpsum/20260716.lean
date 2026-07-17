import Batteries
import Lean

section

universe u v

abbrev MyOptionT (m : Type u -> Type v) (α : Type u) : Type v :=
  m (Option α)

namespace MyOptionT

def mk {m : Type u -> Type v} {α : Type u}
    (x : m (Option α)) : MyOptionT m α :=
  x

def pure {m : Type u -> Type v} [Pure m] {α : Type u} (a : α) :
    MyOptionT m α :=
  MyOptionT.mk (Pure.pure (some a))

def bind {m : Type u -> Type v} [Monad m] {α β : Type u}
    (x : MyOptionT m α) (k : α -> MyOptionT m β) :
    MyOptionT m β :=
  MyOptionT.mk do
    match <- x with
    | none => Pure.pure none
    | some a => k a

def fail {m : Type u -> Type v} [Pure m] {α : Type u} : MyOptionT m α :=
  MyOptionT.mk (Pure.pure none)

def fromOption {m : Type u -> Type v} [Pure m] {α : Type u}
    (x : Option α) : MyOptionT m α :=
  MyOptionT.mk (Pure.pure x)

instance instMonad {m : Type u -> Type v} [Monad m] :
    Monad (MyOptionT m) where
  pure := MyOptionT.pure
  bind := MyOptionT.bind

end MyOptionT

abbrev Env := List (String × String)
abbrev EnvM (α : Type) : Type := StateM Env α

def lookupNat (key : String) : MyOptionT EnvM Nat :=
  MyOptionT.mk do
    let env <- get
    Pure.pure (env.lookup key >>= String.toNat?)

def loadRange : MyOptionT EnvM (Nat × Nat) := do
  let lo <- lookupNat "lower"
  let hi <- lookupNat "upper"
  if lo <= hi then
    pure (lo, hi)
  else
    MyOptionT.fail

#eval loadRange [("lower", "8000"), ("upper", "8080")]
-- (some (8000, 8080), [("lower", "8000"), ("upper", "8080")])

#eval loadRange [("lower", "8000")]
-- (none, [("lower", "8000")])

#eval loadRange [("lower", "9000"), ("upper", "8000")]
-- (none, [("lower", "9000"), ("upper", "8000")])

end

open Lean Elab Command Term Meta Tactic

elab "#parseTerm " s:str : command => do
  let input := s.getString
  let env <- getEnv
  match Parser.runParserCategory env `term input with
  | .ok stx => logInfo m!"term syntax kind: {stx.getKind}"
  | .error err => logError err

elab "#showExpr " t:term : command => do
  liftTermElabM do
    let e <- Term.elabTerm t none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e <- instantiateMVars e
    logInfo m!"{repr e}"

elab "#assertType " termStx:term " : " typeStx:term : command => do
  liftTermElabM do
    let expected <- Term.elabType typeStx
    discard <| Term.elabTermEnsuringType termStx expected
    Term.synthesizeSyntheticMVarsNoPostponing
    logInfo "success"

#parseTerm "x * 2"
-- term syntax kind: «term_*_»

#showExpr fun (x : Nat) => x * 2
-- Lean.Expr.lam ...

def double : Nat → Nat := fun x ↦ x * 2

#assertType double 3 : Nat
-- success

#guard_expr (Nat.succ 1) = 2

def joinDigits (left right : Nat) : Nat :=
  left * 10 + right

infixl:65 " <+> " => joinDigits

#parseTerm "1 <+> 2 <+> 3"
-- term syntax kind: «term_<+>_»

#eval 1 <+> 2 <+> 3
-- 123

#eval 1 <+> (2 <+> 3)
-- 33

syntax "twice " term : term

macro_rules
  | `(twice $x) => `($x + $x)

#check twice 3
-- 3 + 3 : Nat

#guard_expr (twice 3) = 6

#eval twice 3
-- 6

#check Lean.Parser.Command.meta

elab "count_goals" : tactic => do
  let goals <- getGoals
  logInfo m!"goals: {goals.length}"

example : True := by
  count_goals
  trivial
  count_goals
  count_goals
  count_goals
  count_goals
-- goals: 1
