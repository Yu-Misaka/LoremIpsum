import Batteries

#check String.toNat?

#guard "42".toNat? == some 42

-- #guard_expr "42".toNat? =~ some 42

-- #help command "#guard"

#guard compare 3 7 == Ordering.lt
#guard compare 7 7 == Ordering.eq
#guard compare 9 7 == Ordering.gt

section

inductive GuessError where
  | notANumber
  | tooSmall
  | tooLarge
  | outOfFuel
deriving Repr, BEq

def describe : GuessError → String
  | .notANumber => "Not a number."
  | .tooSmall => "Too small."
  | .tooLarge => "Too large."
  | .outOfFuel => "Out of guesses."

inductive Result (err a : Type) where
  | ok (x : a)
  | error (e : err)
deriving Repr, BEq

def Result.bind {err a b : Type} : Result err a → (a → Result err b) → Result err b
  | .ok x, k => k x
  | .error e, _ => .error e

instance {err : Type} : Monad (Result err) where
  pure := .ok
  bind := .bind

def parseGuess (line : String) : Result GuessError Nat :=
  match line.trimAscii.toNat? with
  | none => .error .notANumber
  | some n => .ok n

def judge (secret guess : Nat) : Result GuessError Unit :=
  match compare guess secret with
  | .lt => .error .tooSmall
  | .gt => .error .tooLarge
  | .eq => .ok ()

def checkLine (secret : Nat) (line : String) : Result GuessError Unit := do
  let guess ← parseGuess line
  judge secret guess

#guard checkLine 42 "42" == .ok ()
#guard checkLine 42 "40" == .error .tooSmall
#guard checkLine 42 "100" == .error .tooLarge
#guard checkLine 42 "forty-two" == .error .notANumber

def play (secret : Nat) : (fuel : Nat) → IO Unit
  | 0 => IO.println (describe .outOfFuel ++ s!" It was {secret}.")
  | fuel + 1 => do
    -- let _ ← IO.print "> "
    IO.print "> "
    let line ← (← IO.getStdin).getLine
    match checkLine secret line with
    | .ok () => IO.println "Correct."
    | .error e =>
      IO.println (describe e)
      play secret fuel

def guesses : Nat := 7

def main : IO Unit := do
  IO.println s!"I picked a number between 1 and 100. \
    You have {guesses} guesses."
  let secret ← IO.rand 1 100
  play secret guesses

end

section

structure MonadOps (m : Type → Type) where
  -- 考虑`m`为`Option`
  pure : {a : Type} → (x : a) → m a
  map : {a b : Type} → (f : a → b) → (xs : m a) → m b
  join : {a : Type} → (xss : m (m a)) → m a

#check Option.map
#check List.map

variable {a b : Type}

def pure (x : a) : List a := [x]

def join : List (List a) → List a
  | [] => []
  | xs :: xss => xs ++ join xss

#guard join [[1, 2], [], [3]] == [1, 2, 3]

def bind (xs : List a) (k : a → List b) : List b :=
  join (xs.map k)

#guard bind [1, 2, 3] (fun n => List.replicate n n) == [1, 2, 2, 3, 3, 3]
#guard bind [1, 2, 3] (fun n => List.replicate n n)
    == [1, 2, 3].flatMap (fun n => List.replicate n n)

#check Option.join

def bind' (x : Option a) (k : a -> Option b) : Option b :=
  Option.join (x.map k)

#guard bind' (some 4) (fun n => if n % 2 == 0 then some (n / 2) else none) == some 2
#guard bind' (some 3) (fun n => if n % 2 == 0 then some (n / 2) else none) == none
#guard bind' none (fun n => some (n + 1)) == none

end

section

variable {m a b}

def mapViaBind [Monad m] (f : a -> b) (x : m a) : m b :=
  x >>= fun y => pure (f y)

def joinViaBind [Monad m] (x : m (m a)) : m a :=
  x >>= id

#guard mapViaBind (· + 1) (some 2) == some 3
#guard joinViaBind (some (some 5)) == some 5

end

section

def div? (m n : Nat) : Option Nat :=
  if n == 0 then none else some (m / n)

def ratioBind (s t : String) : Option Nat :=
  s.toNat?.bind fun m =>
    t.toNat?.bind fun n =>
      div? m n

def ratioInfix (s t : String) : Option Nat :=
  s.toNat? >>= fun m =>
    t.toNat? >>= fun n =>
      div? m n

def ratioDo (s t : String) : Option Nat := do
  let m ← s.toNat?
  let n ← t.toNat?
  div? m n

def ratioDo' (s t : String) : Option Nat := do
  let n ← t.toNat?
  div? (← s.toNat?) n

end

section

def factorial : Nat -> Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

#guard factorial 4 == 24

def factIter (product : Nat) : Nat -> Nat
  | 0 => product
  | n + 1 => factIter (product * (n + 1)) n

#guard factIter 1 4 == 24

variable {a b}

def foldl (step : b -> a -> b) (acc : b) : List a -> b
  | [] => acc
  | x :: xs => foldl step (step acc x) xs

#guard foldl (fun product n => product * n) 1 [1, 2, 3, 4] == 24

def zero_add : (n : Nat) -> 0 + n = n
  | 0 => rfl
  | n + 1 => congrArg (· + 1) $ zero_add n

def swapPair : Int × Int -> Int × Int := by
  intro p
  constructor
  · exact p.2
  · exact p.1

#guard swapPair (1, -2) == (-2, 1)

def swapMain : IO Unit := do
  let line ← (← IO.getStdin).getLine
  let [a, b] := line.trimAscii.toString.splitOn " "
    | IO.println "expected two integers"
  let some m := a.toInt?
    | IO.println s!"{a} is not an integer"
  let some n := b.toInt?
    | IO.println s!"{b} is not an integer"
  let (x, y) := swapPair (m, n)
  IO.println s!"{x} {y}"

end

#check LawfulMonad

section

declare_syntax_cat compClause

syntax ident " in " term : compClause

syntax "[" term " | " compClause,+ "]" : term

macro_rules
  | `([$e | $x:ident in $xs]) => `(($xs) >>= fun $x => pure $e)
  | `([$e | $x:ident in $xs, $cs,*]) => `(($xs) >>= fun $x => [$e | $cs,*])

#guard [x + y | x in some 1, y in some 2] == some 3
#guard [x + 1 | x in (none : Option Nat)] == none

end

--引用透明性

section

variable (a b)

inductive State (s : Type) : Type -> Type 1 where
  | get : State s s
  | put : s -> State s Unit
  | pure : a -> State s a
  | bind : State s a -> (a -> State s b) -> State s b

#check ()

end
