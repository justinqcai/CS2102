/-
Name:Justin Cai, jc5pz

This exam has 44 questions. Most are short, but you should 
still move along. Don't get hung up for too long on any one 
question. Most questions don't depend on other questions. A
good strategy is to make a pass over the exam, answer all of
the questions that are easy for you to answer, then repeat
this procedure with the remaining questions until you are
done or the time is up.

We will penalize late submissions at the rate of 3 points per 
minute. Be sure to upload, check, and if necessary fix, your
submission well before the end of the exam period.
-/

/-
I.LOGIC
-/

/-
A. Types

A logic is a formal language. The logic of Lean is typed. 
Every correctly formed term in Lean has a type. Lean also 
supports the definition of new types. The terms (or values) 
of a type are defined by its constructors. The next few 
problems test your ability to define your own types in Lean,
including enumerated types, polymorphic types, and recursive 
types. 
-/

/- 1. Enumerated types [2 points]. 

Define a type, Food, with exactly the following values: 
steak, chicken, applepie, cookie, salad.
-/
inductive Food : Type 
| steak : Food
| chicken : Food
| applepie : Food
| cookie : Food
| salad : Food


/- 2. Polymorphic types [2 points]

Define a type, Box T, where T is any type, with just one 
constructor, called mk, taking just one argument, of type T. 
You can think of a value of this type as being like a box 
containing the given value as its contents. Once you
define the type, define two values, the first called 
aBoxedNat, containing the natural number, zero, and the 
second called aBoxedString, containing the string, "Hello, 
Lean!".
-/

inductive Box {T : Type} 
| mk : T → Box

def aBoxedNat := Box.mk 0
def aBoxedString := Box.mk "Hello, Lean!"

/- 3. Recursive types [2 points]

Define a type called Tree_nat. A value of this type 
represents a "tree" of natural numbers. Such a tree is either 
empty, or it is a natural number and two smaller trees of the 
same type. Your type will have two constructors. Call them 
empty and mk. Once you define your type, give two example 
values, the first (called eTree) being empty, and the second, 
called aTree having the value 0 and two smaller trees, the 
first empty and the second having the value 1 and two smaller 
trees, both empty. Do not open the Tree_nat namespace.
-/

inductive Tree_nat : Type 
| empty : Tree_nat
| mk : ℕ → Tree_nat → Tree_nat → Tree_nat
                            -- start adding constructors here
def eTree := Tree_nat.empty
def aTree := 
Tree_nat.mk 0 Tree_nat.empty (Tree_nat.mk 1 Tree_nat.empty Tree_nat.empty)


/- 4. [2 points]

Define a polymorphic type, Tree T, where T is any type. 
Start with the partial solution we've provided. Note that T 
is an explicit parameter of the polymorphic Tree type in this 
definition. A value of this type represents a "tree" of 
objects of type T. Such a tree is either empty, or it is a 
value of type T and two smaller trees of the same Tree type. 
Your type will have two constructors. Call them empty and mk. 

Once you define your type, give two example values, called 
eTree' and aTree', respectively. The first must be the empty 
tree of natural numbers. The second must be a non-empty tree 
with the value 0 and two smaller trees, the first empty and 
the second having the value 1 and two empty trees. 

Note: you will have to give an explicit type parameter when 
you create an empty tree. The mk constructor won't require 
one. It's a good idea to put each argument to a constructor 
on a separate line. It's also a good idea to use parentheses 
around tree construction expressions to make sure Lean knows 
how to "parse" your logic.
-/

inductive Tree (T : Type): Type 
| empty : Tree
| mk : T → Tree → Tree → Tree                            -- start adding constructors here

def eTree' := Tree.empty (nat)
def aTree' := Tree.mk 0 (Tree.empty(nat)) (Tree.mk 1 (Tree.empty(nat)) (Tree.empty(nat))

/- 5. [2 points]

What is the type of a function that takes a natural number 
and a string, in that order, and that returns true if the 
given string has the given natural number at its length and 
that return false otherwise? Use function type notation here.

Answer: 
ℕ → string → Prop
-/


/- B. Functions

The formal language of predicate logic allows for the use of 
functions. Lean allows you to define new functions that you 
can then use in logical expressions (and for ordinary 
programming as well). This section of the exam tests your 
ability to read, write, and reason about functions in 
predicate logic.
-/

/- 6. [2 points]

Rewrite the following function using lambda-style notation. 
Do this by filling in the holes in the second definition.
-/

def mult (n1 n2 : ℕ) : ℕ := n1 * n2

def mult_lambda_style : ℕ → ℕ → ℕ := 
    λ n1 n2,
        n1 * n2




/- 7. [3 points] Here we first remind you of the definition 
of a type for representing lists of natural numbers. We open 
the name space and give an example, representing the list [4,
3,2,1]. Now write a recursive function, reduce_list_sum, that 
computes the sum of the values in a given list of natural 
numbers. Define your function by cases, with one case for an 
empty list (in which case the sum is zero), and one case for 
a non-empty list, in which case the list has a natural number 
at its head and a smaller list as its tail. When you've 
gotten it right, the test case we provide will pass.
-/

-- type for representing lists of natural numbers
inductive list_nat : Type
| nil_nat : list_nat
| cons_nat : ℕ → list_nat → list_nat

-- open the namespace
open list_nat 

-- a term representing the list, [4,3,2,1]
def list_test_case : list_nat := 
    cons_nat 
        4 
        (cons_nat 
            3 
            (cons_nat 
                2 
                (cons_nat 
                    1 
                    nil_nat
                )
            )
        )

-- Your function definition goes here
def list_nat_reduce : list_nat → ℕ 
| nil_nat := 0 
| (cons_nat n l) := n + list_nat_reduce l                       -- replace with your cases

-- test case
example : list_nat_reduce list_test_case = 10 := rfl


/- C. Propositions and Predicates

The language of predicate logic includes propositions and 
predicates. Predicates can be thought of as propositions with 
parameters. A predicate with no parameters left to fill in is 
simply a proposition. In this section, we test your 
understanding of basic concepts involving propositions and 
predicates. We introduce a few assumptions to start with, 
which we then use in the following questions.
-/

-- Assume there are people
axiom Person : Type

-- Assume there are people called Tom, Mary, etc.
axioms (Tom Mary Jane Hamid Yu : Person)

-- Assume being nice is a property that a person can have
axiom nice : Person → Prop

/-
Assume that one person can like another person. For example,
we'd write the proposition, Tom likes Mary, as (likes Tom 
Mary).  
-/ 
axiom likes : Person → Person → Prop

/--/
Write formal propositions in Lean for each of the following 
informal propositions. Replace the holes (underscores) in the 
following incomplete Lean definitions with your answers.
-/

-- 8. [1 point] Tom is nice
def prob_0 := nice Tom

-- 9. [1 point] If everyone is nice, Tom is nice
def prob_1 := (∀ P : Person, nice P) → nice Tom

-- 10. [2 points] Tom is nice and Mary is nice
def prob_2 := nice Tom ∧ nice Mary

-- 11. [2 points] Tom is not nice
def prob_3 := ¬(nice Tom)

-- 12. [2 points] Tom is nice or Hamid is nice
def prob_4 := nice Tom ∨ nice Hamid

/- 
13. [2 points] One but not both of Tom and Hamid are nice 
(use parentheses to make intent clear)
-/
def prob_5 := (nice Tom ∧ ¬nice Hamid) ∨ (nice Hamid ∧ ¬ nice Tom)

/- 
14. [2 points] Everyone likes anyone who is nice (think in 
terms of "if ... then ...")
-/
def prob_6 := ∀ P1: Person, nice P1 → ∀ P: Person, likes P P1

/- 
15. [2 points] No one likes anyone who is not nice 
(implications might help here)
-/
def prob_7 := ∀ P : Person, ¬nice P → ¬(∀ P1: Person, likes P1 P)

-- 16. [2 points] Everyone likes him or herself
def prob_8 := ∀ P: Person, likes P P

/-
17. [2 points] Let p1, p2, p3 be people. If p1 does not like 
p2, and p2 does not like p3, then p1 likes p3. This is a 
logical statement of the adage that the enemy of my enemy is 
my friend.
-/

def prob_9 := ∀ p1 p2 p3: Person, ¬likes p1 p2 ∧ ¬likes p2 p3 → likes p1 p3

/-
18. [2 points] No one likes Tom
-/
def prob_10 := ∀ P: Person, ¬likes P Tom

/-
19. [2 points] Not everyone likes Tom
-/

def prob_11 := ¬ (∀ P: Person, likes P Tom)

/-
20. [2 points] A person likes Tom if and only if that person 
likes Yu.
-/

def prob_12 := ∀ P: Person, likes P Tom ↔ likes P Yu

/-
Translate the following three logical propositions into 
natural language. 
-/

-- 21. [2 points] 
def prob_13 := ∃ p1, ∀ p2, likes p2 p1  

-- Answer: there is someone everyone likes

-- 22. [2 points] 
def prob_14 := 
    (∀ p1 p2, likes p1 p2 ↔ likes p2 p1) →
    likes Tom Yu → 
    likes Yu Tom

-- Answer: if people only like others if and only if they are liked back, then 
-- if Tom likes Yu then Yu likes Tom

-- 23. [extra credit] 
def prob_15 := ¬ ∀ p1, ∃ p2, ¬ likes p1 p2


-- Answer: not everyone dislikes someone

/-
24. [2 points] Define a predicate, dislikes, so that p1 
dislikes p2 (dislikes p1 p2) means that p1 does not
like p2
-/

-- Answer below
def dislikes (p1 p2 : Person) := ¬likes p1 p2

/-
25. [2 points] Define a predicate, friendOfFriend, that is 
true of two people, p1 and p2, if there is someone, p, who 
p1 likes, and where p, in turn, likes p2.  
-/

-- Answer:
def friendOfFriend (p1 p2 : Person) := ∃ p: Person, likes p1 p ∧ likes p p2

/-
I. PROOFS
-/

/-
Some of the following exercises use the 
following additional assumptions: Tom, Mary, 
and Jane are nice; Hamid and Yu are not nice; 
and Tom likes Mary. We now formalize these facts.
-/
axioms 
    (nT: nice Tom) 
    (nM: nice Mary) 
    (nJ: nice Jane) 
    (nnHamid: ¬ nice Hamid) 
    (nnYu: ¬ nice Yu)
    (likesTM: likes Tom Mary)


/- 
26. [3 points] Prove that there is someone who is not nice.
-/

example : ∃ p, ¬ nice p := 
begin
    apply exists.intro Hamid,
    exact nnHamid,
end


/-
27. [5 points] Prove the following. The proposition could 
be expressed in English as follows: If whenever any two 
people, p1 and p2, are nice, then p1 likes p2; then if 
there exist two nice people, x and y; then there exist 
two people, p and q, where p likes q. Write a brief 
comment in English before each line of your proof 
script to explain what logical inference rule you're 
using.
-/ 

example : 
    (∀ p1 p2, nice p1 → nice p2 → likes p1 p2) → 
    (∃ x y : Person, nice x ∧ nice y) → 
    ∃ p q, likes p q  :=
begin
  --assuming if whenever two people are nice, then one likes the other
    assume ppnice,
--assuming there exists two nice people
    assume xnice,
--eliminating the first nice person that exists
    apply exists.elim xnice,
--assuming the first nice person is x
    assume x,
--assuming there exists another nice person
    assume ynice,
--eliminating the second nice person that exists
    apply exists.elim ynice,
--assuming the second nice person is y
    assume y,
--assuming there are two nice people x and y
    assume func,
--introducing x and y as the two people that exist where x likes y
    apply exists.intro x,
    apply exists.intro y,
--defining the function that says if x is nice and y is nice then x likes y
    have xynice := ppnice x y,
--defining xnice to be a proof of x being nice and ynice to be a proof of y is nice
    have xnice := func.1,
    have ynice := func.2,
--calling the xynice function using the proofs of x is nice and y is nice to get
--a proof of x liking y 
    exact xynice (xnice) (ynice),
end

/- 
28. [3 points] Prove the following proposition. 
-/

example : likes Tom Yu ∨ likes Tom Mary → ∃ p, likes Tom p :=
begin
    assume TYoTM,
    cases TYoTM with TY TM,
        apply exists.intro Yu,
        assumption,
        apply exists.intro Mary,
        assumption,
end

/- 29. [3 points] Using "example", state and prove the 
proposition (formally) that Tom is nice and Tom likes Mary. 
Remember, again, that you have certain proofs already defined 
(as axioms); you can use them here.
-/

-- Answer here
example : nice Tom ∧ likes Tom Mary :=
begin
    split,
        exact nT,
        exact likesTM,
end
/-
30. [3 points] Prove that not everyone is not nice. Hint:
remember that you have some people and proofs
that they are nice, or not nice, as assumptions.
-/

example : ¬ (∀ p, ¬ nice p) :=
begin
    assume notnice,
    have TomNotNice := notnice Tom,
    exact TomNotNice nT,
end

/-
31. [3 points] Prove that the following formula can be 
satisfied using only the propositions, true and false, as 
witnesses.
-/

example : ∃ (P Q : Prop), (P ∨ Q) ∧ (P ∧ ¬ Q) :=
begin
    apply exists.intro true,
    apply exists.intro false,
    simp,
end

/- 
32. [3 points] Prove the following by induction. Be sure 
to use the induction tactic. Note: you might not need to use 
the induction hypothesis!
-/

example : ∀ (n : ℕ), n = 0 ∨ ∃ n', n = nat.succ n' :=
begin
    assume n,
    induction n,
    apply or.inl,
    trivial,
    cases n_ih,
    apply or.inr,
    apply exists.intro 0,
    rw n_ih,
    apply or.inr,
    apply exists.elim n_ih,
    assume n,
    assume nfunc,
    rw nfunc,
    apply exists.intro (nat.succ n),
    exact rfl,
end
/- 
33. [3 points] Prove the same thing without using induction 
(hint: case analysis on n).
-/
example : ∀ (n : ℕ), n = 0 ∨ ∃ n', n = nat.succ n' :=
begin
    assume n,
    cases n,
    apply or.inl,
    exact rfl,
    apply or.inr,
    apply exists.intro n,
    exact rfl,
end

/-
III. Informal Proofs
-/

/- 34. [3 points] 
First in Lean write a predicate, even : ℕ → Prop, expressing 
what it means for a natural number, n, to be even. Then write 
a concise *informal* proof of the proposition that for any 
two natural numbers, n and m, if n and m are even, then n + m 
is even. Make reference to the formal definition of what it 
means to be even from within your informal proof. Hint: A 
direct proof in which you start by assuming that m and n are 
even and then go from there is easiest. 
-/

def even : ℕ → Prop := λ n, ∃ m, n = 2 * m

/-
Your proof here.
We're trying to prove that if even(n) ∧ even(m), then even(n+m)
    1. assume n is even, which means there exists a nat N where n = N*2
        a. apply exists.elim to assume the nat N
    2. assume m is even, which means there exists a nat M where m = M*2
        a. apply exists.elim to assume the nat M
    3. we're trying to prove even(n+m); this means there exists
    some value NM where n+m = 2*NM
        a. to get to this point, unfold even
    4. introduce NM to be N + M (where N * 2 = n and M*2 = m)
        a. by applying exists.intro (N+M)
    5. substitute n in the equation we're trying to prove for 2*N
        a. rewrite 
    6. substitute m in the equation we're trying to prove for 2 * M
        a. rewrite
    7. Thus, we now have the equation 2*N + 2*M = 2*(N+M)
    8. Distribute on the right side
    9. We now have 2*N + 2*M = 2*N + 2*M
    10. This equation is equal, thus the goal has been proved
-/


/-
IV. Set Theory
-/

/-
We introduce a few sets and ask you to then answer several 
questions. Give your answers as plain text. You do not have 
to use Lean syntax to answer the questions in this section of 
the exam.
-/

def s1 : set ℕ := { 1, 2, 3 }
def s2 : set ℕ := { 3, 6 }
def s3 : set ℕ := {}
def s4 : set string := {"ILove", "Logic"} 

/-
35. [2 points] Using display notation (curly braces around a 
list of values), what is the union of s1 and s2? 

Answer: {1, 2, 3, 6}
-/

/-
36. [2 points] Using display notation, what is the 
intersection of s1 and s2? 

Answer: {3}
-/

/-
37. [2 points] Using display notation, what is the set 
difference, s1 - s2? 

Answer: {1, 2}
-/

/-
38. [3 points] Suppose prime and even are two predicates over 
the natural numbers, such that the proposition, "prime n", is 
true if and only if n is prime in the usual sense, and the 
proposition, "even n", is true if and only if n is even in 
the usual sense. Use *set comprehension notation* to 
represent the set of natural numbers that are both even and 
prime.

Answer: set nat := {n | prime n ∧ even n}

Now write down this set using display notation. Hint: You do 
have to figure out what specific elements are in this set. 

Answer: 
{2}
-/

/-
39. [3 points] Use display notation to write the powerset of 
s2.

Answer: 
{
    {},
    {3},
    {6},
    {3, 6}
}
-/

/-
40. [3 points] Use display notation to write the product set 
(aka Cartesian product) of s2 and s4.

Answer:
{(3, "ILove"), (3, "Logic"), (6, "ILove"), (6, "Logic")}
-/

/-
41. [3 points] How many elements are in the powerset of the 
product set of s2 and s4?

Answer: 16
-/

/-
42. [3 points] An element of the powerset of the product set 
of s2 and s4 is some subset of the product set. Give one such 
value (element) that represents a function from s2 to s4 that
is injective but not surjective. 

Answer: {(3, "ILove"), (6, "ILove")}
-/



/- 
43. [3 points] Give two values from the powerset of the 
product set, each of which represents a bijective function
from s2 to s4.

Answer: {(3, "ILove"), (6, "Logic")}
        {(3, "Logic", (6, "ILove")}
-/

/-
44. [3 points] The biggest open problem in computer science 
is whether two classes of problems are equivalent. The 
problem goes by the name, P=NP. No one knows whether P=NP or 
not. We'll introduce PeqNP as a value of type Prop to 
represent the proposition that P=NP. Prove the following 
theorem. You may use classical reasoning. 
-/

open classical

axiom PeqNP : Prop
example : PeqNP ∨ ¬ PeqNP :=
begin
    cases em PeqNP,
        exact or.inl h,
        exact or.inr h,
end

/-
45. Extra Credit: Give a concise but still complete informal 
proof that the square root of two is irrational. Hints: First
you might rephrase the proposition in the form of a negation.
The use the method of proof by negation. This involves making
an assumption. The key is then to deduce consequences of that
assumption, and show that it leads to a contradiction. Only a
complete correct proof will receive credit.

Answer: 
1. we're trying to prove that the square root of two is NOT rational
2. thus, we're really trying to prove false
    a. we get to this point by assuming the premise that
    root 2 is rational
3. the definition of a rational number is that it has to be
expressible by the ratio of two integers, and can't be infinite
and nonrecurring when expressed as a decimal. 
4. obtain the proof/definition of a rational number
5. root 2 is an infinite and recurring decimal and cannot
be expressed by the ratio of two integers
6. the proof of root two being rational contradicts the 
definition of a rational number
7. thus, we have a contradiction and the negation is proved.
-/
