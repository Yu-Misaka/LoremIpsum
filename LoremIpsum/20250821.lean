inductive AExp : Type where
  | num : Int → AExp
  | var : String → AExp
  | add : AExp → AExp → AExp
  | sub : AExp → AExp → AExp
  | mul : AExp → AExp → AExp
  | div : AExp → AExp → AExp

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

def add : Nat → Nat → Nat
  | m, Nat.zero => m
  | m, Nat.succ n => Nat.succ (add m n)

#eval add 2 7
#reduce add 2 7

def mul : Nat → Nat → Nat
  | _, Nat.zero => Nat.zero
  | m, Nat.succ n => add m (mul m n)

#reduce mul 2 0
#reduce mul 2 8

def power : Nat → Nat → Nat
  | _, Nat.zero => 1
  | m, Nat.succ n => mul m (power m n)

def powerParam (m : Nat) : Nat → Nat
  | Nat.zero => 1
  | Nat.succ n => mul m (power m n)

example (m : Nat) : power m = powerParam m :=
  funext fun k ↦
    match k with
    | Nat.zero => rfl
    | Nat.succ _ => rfl

-- f(f(...(f z)...))
-- ↑ n times
def iter (α : Type) (z : α) (f : α → α) : Nat → α
  | Nat.zero => z
  | Nat.succ n => f (iter α z f n)

def powerIter (m n : Nat) : Nat :=
  iter Nat 1 (mul m) n

-- (m : Nat) → (n : Nat) → powerIter m k = power m k
theorem powerIter_eq_power : ∀ m k, powerIter m k = power m k
  | _, Nat.zero => rfl
  | m, Nat.succ n =>
    -- change mul m (iter Nat 1 (mul m) n) = mul m (power m n)
    -- congr
    -- exact (powerIter_eq_power m n)
    congrArg (mul m) (powerIter_eq_power m n)

def reverse {α : Type } : List α → List α
  | [] => []
  | x :: xs => reverse xs ++ [x]

example {α : Type } : ∀ xs : List α, reverse (reverse xs) = xs := by
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs =>
    change reverse (reverse xs ++ [x]) = x :: xs
    -- ↑ want to "distribute" outer `reverse` over ++
    sorry

/-
Mathlib imported: ↓

example {α : Type*} : ∀ xs : List α, reverse (reverse xs) = xs := by
  intro xs
  induction' xs with x xs ih
  · rfl
  · change reverse (reverse xs ++ [x]) = x :: xs
    -- ↑ want to "distribute" outer `reverse` over ++
    sorry
-/

theorem reverse_append {α : Type} :
    ∀ xs ys : List α, reverse (xs ++ ys) = reverse ys ++ reverse xs
  | [], ys => by
    change reverse ys = reverse ys ++ []
    exact (List.append_nil _).symm
  | x :: xs, ys => by
    change reverse (xs ++ ys) ++ [x] = reverse ys ++ (reverse xs ++ [x])
    rw [← List.append_assoc, reverse_append xs]

theorem reverse_append_ind {α : Type} :
    ∀ xs ys : List α, reverse (xs ++ ys) = reverse ys ++ reverse xs := by
  intro xs ys
  induction xs with
  | nil => simp [reverse]
  | cons x xs ih => simp [reverse, ih]
  /-
  induction' xs with x xs ih
  · simp [reverse]
  · simp [reverse, ih]
    -/

theorem reverse_reverse {α : Type} :
    ∀ xs : List α, reverse (reverse xs) = xs
  | [] => rfl
  | x :: xs => by
    -- simp [reverse, reverse_append, reverse_reverse xs]
    change reverse (reverse xs ++ [x]) = x :: xs
    rw [reverse_append, reverse_reverse xs]
    rfl
