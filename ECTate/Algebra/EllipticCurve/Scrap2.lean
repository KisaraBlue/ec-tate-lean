example (n : ℕ) : 1 = 1 :=
if h : n = 0 then
 have : n = 0 := h
 sorry
else by rfl



def foo_alg (n : ℕ :=0) : ℕ :=
  if h0 : n = 0 then 1 else
  if h1 : n = 1 then 2 else unreachable!

example : foo_alg 1 = 2 := by
  --rw [foo_alg]
  simp

#reduce foo_alg 1

-- Defines a function that takes a name and produces a greeting.
def getGreeting (name : String) := s!"Hello, {name}! Isn't Lean great?"


#eval println! getGreeting "Pi"

-- The `main` function is the entry point of your program.
-- Its type is `IO Unit` because it can perform `IO` operations (side effects).
def main : IO Unit :=
  -- Define a list of names
  let names := ["Sebastian", "Leo", "Daniel"]


  -- Map each name to a greeting
  let greetings := names.map getGreeting

  -- Print the list of greetings
  for greeting in greetings do
    IO.println greeting

#eval main

def fact x :=
  match x with
  | 0   => 1
  | n+1 => (n+1) * fact n

def fib n :=
  match n with
  | 0 => 0
  | 1 => 1
  | (n+2) => fib n + fib (n+1)

  def fib' :=
  fun
  | 0 => 0
  | 1 => 1
  | (n+2) => fib n + fib (n+1)

#check fib'

def fib2 n :=
  if n <2 then
    match n with
    | 0 => 0
    | 1 => 1
    | n+2 => unreachable!
  else
    fib2 (n-1) + fib2 (n-2)

#eval fib' 8

#eval [fib' 1, fib 2, fib 3, fib 4, fib 5, fib' 6]
def bar := fact 100

def sampleFunction1 x := ((x*x + 3) : ℤ)
#check sampleFunction1 3

def foo := sampleFunction1 2

#eval foo+bar
#eval s!"The result of squaring the integer 4573 and adding 3 is {foo}"

-- Conditionals use if/then/else
def sampleFunction3 (x : Int) :=
  if x > 100 then
    2*x*x - x + 3
  else
    2*x*x + x - 37

#eval println! "The result of applying sampleFunction3 to 2 is {sampleFunction3 2}"




-- Lean has first-class functions.
-- `twice` takes two arguments `f` and `a` where
-- `f` is a function from natural numbers to natural numbers, and
-- `a` is a natural number.
def twice (f : Nat → Nat) (a) :=
  f (f a)

#check twice

-- `fun` is used to declare anonymous functions
#eval twice (λ x => x + 2) 10

-- You can prove theorems about your functions.
-- The following theorem states that for any natural number `a`,
-- adding 2 twice produces a value equal to `a + 4`.
theorem twiceAdd2 (a : Nat) : twice (fun x => x + 2) a = a + 4 := by
  -- The proof is by reflexivity. Lean "symbolically" reduces both sides of the equality
  -- until they are identical.
  rfl

variable (a : ℕ)

def fib2 n :=


#reduce twice (fun x => x + 2) a
#reduce a + 4
-- `(· + 2)` is syntax sugar for `(fun x => x + 2)`. The parentheses + `·` notation
-- is useful for defining simple anonymous functions.
#eval twice (· * 3) 10

-- Enumerated types are a special case of inductive types in Lean,
-- which we will learn about later.
-- The following command creates a new type `Weekday`.
inductive Weekday where
  | sunday    : Weekday
  | monday    : Weekday
  | tuesday   : Weekday
  | wednesday : Weekday
  | thursday  : Weekday
  | friday    : Weekday
  | saturday  : Weekday

#check Weekday.sunday

-- `Weekday` has 7 constructors/elements.
-- The constructors live in the `Weekday` namespace.
-- Think of `sunday`, `monday`, …, `saturday` as being distinct elements of `Weekday`,
-- with no other distinguishing properties.
-- The command `#check` prints the type of a term in Lean.
#check Weekday.friday
#check Weekday.monday

-- The `open` command opens a namespace, making all declarations in it accessible without
-- qualification.
/-open Weekday
#check sunday
#check tuesday
-/
-- You can define functions by pattern matching.
-- The following function converts a `Weekday` into a natural number.
def natOfWeekday (d : Weekday) : Nat :=
  match d with
  | Weekday.sunday    => 1
  | Weekday.monday    => 2
  | Weekday.tuesday   => 3
  | Weekday.wednesday => 4
  | Weekday.thursday  => 5
  | Weekday.friday    => 6
  | Weekday.saturday  => 7
open Weekday

#eval natOfWeekday tuesday

def isMonday : Weekday → Bool :=
  -- `fun` + `match`  is a common idiom.
  -- The following expression is syntax sugar for
  -- `fun d => match d with | monday => true | _ => false`.
  fun
    | monday => true
    | _      => false

#eval isMonday monday
#eval isMonday sunday

-- Lean has support for type classes and polymorphic methods.
-- The `toString` method converts a value into a `String`.
#eval toString 10
#eval toString (10, 20)

#check (10,20,3,-1)

-- The method `toString` converts values of any type that implements
-- the class `ToString`.
-- You can implement instances of `ToString` for your own types.
instance : ToString Weekday where
  toString (d : Weekday) : String :=
    match d with
    | sunday    => "Sunday"
    | monday    => "Monday"
    | tuesday   => "Tuesday"
    | wednesday => "Wednesday"
    | thursday  => "Thursday"
    | friday    => "Friday"
    | saturday  => "Saturday"

#eval toString (sunday, 10)

def Weekday.next (d : Weekday) : Weekday :=
  match d with
  | sunday    => monday
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => saturday
  | saturday  => sunday

#eval Weekday.next Weekday.wednesday
-- Since the `Weekday` namespace has already been opened, you can also write
#eval next wednesday

-- Matching on a parameter like in the previous definition
-- is so common that Lean provides syntax sugar for it. The following
-- function uses it.
def Weekday.previous : Weekday -> Weekday
  | sunday    => saturday
  | monday    => sunday
  | tuesday   => monday
  | wednesday => tuesday
  | thursday  => wednesday
  | friday    => thursday
  | saturday  => friday

#eval next (previous wednesday)

-- We can prove that for any `Weekday` `d`, `next (previous d) = d`
theorem Weekday.nextOfPrevious (d : Weekday) : next (previous d) = d :=
  match d with
  | sunday    => rfl
  | monday    => rfl
  | tuesday   => rfl
  | wednesday => rfl
  | thursday  => rfl
  | friday    => rfl
  | saturday  => rfl

-- You can automate definitions such as `Weekday.nextOfPrevious`
-- using metaprogramming (or "tactics").
theorem Weekday.nextOfPrevious' (d : Weekday) : next (previous d) = d := by
  cases d       -- A proof by case distinction
  all_goals rfl  -- Each case is solved using `rfl`

  #eval Lean.versionString

inductive Palindrome : List α → Prop where
  | nil      : Palindrome []
  | single   : (a : α) → Palindrome [a]
  | sandwich : (a : α) → Palindrome as → Palindrome ([a] ++ as ++ [a])

  #check Palindrome
  #reduce Palindrome []


  inductive Even : ℕ → Prop where
    | z : Even 0
    | p2 : (n : ℕ) → Even n → Even (n+2)

#check Even.z

#reduce Even 2

inductive MyNat where
  | zero: MyNat
  | succ: MyNat -> MyNat

open MyNat
#check succ (succ (zero))
#check MyNat

example : Even 248 := by
repeat apply Even.p2
exact Even.z
