/- Justin cai, jc5pz-/
/-
POINTS: Welcome to the first CS2102 exam. The exam has 12 
questions. Points for each question are as indicated, for a
total of 100 points.

READ CAREFULLY: If you are unable to answer a question in 
a way that Lean accepts as syntactically correct, *comment 
out your malformed answer*. Otherwise an error in your answer 
can cause Lean not to recognize correct answers to other 
questions. If you are sure an answer is correct but Lean is
not accepting it, look for problems in the preceding logic.

Do not change or delete any of the questions.

WHAT TO DO: Complete the exam by following the instructions 
for each question. Save your file then upload the completed 
and saved file to Collab. You have 75 minutes from the start 
of the exam to the time where it must be uploaded to Collab.

OPEN NOTES: You may use the class notes for this exam, whether
provided to you by the instructors or taken by you (or for you).

STRICTLY INDIVIDUAL EFFORT: This is a strictly individual exam,
taken under the honor system. Do not communicate with anyone except
for the instructor about the content of this exam, by any means,
until you are sure that each person you are communicating with 
has already completed the test.
-/

/- 1. (5 points)
What is the type of function1 (just below)? Give you answer by
replacing the hole (underscore) in the subsequent definition 
with your answer.
-/

def function1 (f: ℕ → ℕ) (g: ℕ → ℕ) := 
  λ (x: ℕ), 3
#check function1

def function1_type : Type :=
  (ℕ → ℕ ) → (ℕ → ℕ ) → ℕ → ℕ 





/- 2. (10 points)
Define three equivalent functions, called product1, 
product2, and product3. Each must take two natural 
numbers as its arguments and return their product.  
Define the first version using C-style notation, 
the second using a lambda abstraction, and the third
using a tactic script.
-/

-- Answer below:

-- ANSWER

-- C-style here
def product1 (a b: ℕ ) : ℕ := a * b



-- Lambda abstraction here
def product2: ℕ → ℕ → ℕ :=
  λ a b : ℕ,
    a * b


-- Tactic script here
def product3 (a b : ℕ ) : ℕ :=
begin
  exact a * b
end




/- 3. (5 points)

Given the definition of product1, what function 
is (product1 5)? Answer by replacing the hole in 
the following definition with a lambda abstraction.
-/

def product1_5 := λ a : ℕ, product1 5 a





/- 4. (5 points)
Which of the following properties does "product1_5" have?
Answer by placing a Y (for yes, it has this property), or
N (for no, it doesn't have this property), BEFORE the name
of each property, just after the dash.


-- ANSWER 

- Y injective
- N surjective
- N one-to-many
- N strictly partial
- N bijective
-/





/- 5. (5 points)
Complete the  proof of the following conjecture, that
(product1 4 6) = 24. Fill in the proposition to be
proved in the first hole (underscore) and a proof in
the second hole.
-/

-- ANSWER 
example : (product1 4 6) = 24 := rfl



/- 6. (10 points)
Prove the proposition that, for any natural 
numbers, a, b, and c, if b = a, then if c = b, then a = c.
Fill in the hole in the following example accordingly, 
replacing the underscore with a proof.
-/

-- Complete  by replacing the hole with a proof:
example: ∀ a b c: ℕ, b = a → c = b → a = c := 
    λ a b c,
      λ ba : b = a,
        λ cb : c = b,
          eq.trans (eq.symm ba) (eq.symm cb)






/- 7. (10 points)
In the context of the following assumptions, use
"example" to formally state and prove the proposition
that "Jane is nice."
-/

axiom Person : Type
axioms Jill Jane : Person
axiom IsNice : Person → Prop
axiom JillIsNice : IsNice Jill
axiom JillIsJane : Jill = Jane

-- Fill in the holes with your proposition and proof
example : IsNice Jane := 
  eq.subst JillIsJane JillIsNice 





/- 8. (10 points)
Use "example" to prove that true ∧ true implies
true. Give two proofs, the first using a term-style 
proof (e.g., a lambda expression term), and the
second, using a tactic script.
-/

-- Your answers here
example : true ∧ true → true := and.elim_left

example : true ∧ true → true :=
begin
  exact and.elim_left
end



/- 9. (10 points)
Define a function, called exfalso, that takes a proof 
of false as an argument, and that returns a proof of 
3 = 7 as a result.
-/

-- ANSWER
def exfalso (f: false) : 3 = 7 :=
begin 
  exact false.elim f
end



/- 10. (10 points)
Formally state and prove the proposition, 
that, for any propositions, A, B, and C, 
A ∧ B ∧ C → C ∧ A ∧ B. You may write the
proof in any style you wish. One way to do it 
would be to define a function that takes the
propositions, A, B, and C, and a proof of the 
premise as its arguments and that returns a 
proof of the conclusion as a result. You 
might also use a tactic script. 
-/

-- ANSWER 

example:  ∀ (A B C : Prop ) , A ∧ B ∧ C → C ∧ A ∧ B :=
begin
  intros A B C,
  assume abc,
  have c := abc.2.2,
  have a := abc.1,
  have b:= abc.2.1,
  exact and.intro c (and.intro a b),
end
    



/- 11. (10 points)
Formally (in Lean), prove that if A, B, and C
are any propositions, and if C is true, then 
A ∧ B ∧ C → B ∧ A.
-/

-- Complete the following by replacing _ with a proof:
theorem temp :  ∀(A B C: Prop), C → (A ∧ B ∧ C → B ∧ A) :=
begin
  assume A B C, 
  assume c,
  assume abc,
  have a := abc.1,
  have bc := abc.2,
  have b := bc.1,
  have ba := and.intro b a,
  exact ba,
end
    





/- 12. (10 points)

Define a predicate, gt5, that is true for all and only for
natural numbers greater than 5. You may use the expression,
n > 5, in your answer. Then fill in the hole in the following
definition with the type of the term (gt5 4).
-/

-- ANSWER
def gt5 : ℕ → Prop := 
  λ n : ℕ ,
    if n > 5 then tt else ff

-- ANSWER
def type_of_gt5_4 := (5 > 4 : Prop)



/- 13. EXTRA CREDIT 5 points

Give brief natural-language (in English) rendition
of the following formal proposition.

∃ n, m : ℕ, isPrime n ∧ isPrime m ∧ m = n + 2

Answer: There exists an n and m, both Nats,
n is prime and m is prime, and m is equal to n + 2

If by isPrime we mean the ordinary concept of primeness 
from basic arithmetic, then this proposition is true.
Prove it by giving values for n and m that satisfy the 
predicate along with a very brief argument that the two
numbers do actually satisfy the predicate.

Answer:

n = 1
m = 3

Argument: 
1 is prime and 3 is prime, and 1 + 2 = 3, thus n=1 and m=3 
satisfies this predicate

-/
