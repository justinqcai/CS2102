/-
UVa CS 2102 Discrete Math, Semester Exam 2.

This is an individual evaluation. You may not
communicate with anyone about it by any means
for any reason whether directly or indirectly,
while you, or anyone else in this class with 
whom you might be communicating, directly or 
indirectly, has not yet taken and completed 
the submission of their exam. You may not get
information from anyone else that could help
you with this exam, nor may you allow any of
your information to be so obtained by others.
Violations of these rules will result in the
failure of the exam, of the course, and can 
be referred to the Honor Committee. Please
signal that you understand by signing the
Honor Pledge electronically when you submit
your exam. Some students will be on travel
or otherwise unable to take the exam today.
Do not make answers or any other knowledge
of the exam available until your instructors 
indicate that all exams have been submitted. 
That will take up to one full week. 

The exam has six questions for a total of
100 points with an extra credit question
worth two points. Several of the questions
have several parts. In these cases, the total
points for a question are evenly distributed
over the parts.

If you don't know how to solve a particular
problem, just move on the the next problem.
Come back to any problems you skipped when
you are finished with all the problems you
know how to solve without difficuty. 

This is an open book, open your-own-notes
exam.

Turn off all communications software on all
of your electronic devices before starting 
this test. Turn off your cell phone. Turn off 
your smart watch. Exit from Skype, messenger, 
messages, Facetime, Signal, WhatsApp, and 
all other such services.
-/


/-
The first three questions of the exam
use definitions that we enclose within
a namespace. The end  of the namespace 
is after question 3. You can basically 
ignore this except for a brief note in 
the instructions for question 3, below.
-/
namespace quantifiers

/-
The following sequence of three problems
uses two defintions that we now provide.
We assume there are people, and that one 
person can like another. We formalize 
these assumptions in the following axioms. 
We assume that there are people, formally
represented as terms of a type, Person;
and we assume that and given person, p1, 
might Like another person, p2, represented 
as a predicate, Likes, taking two arguments
of type Person. We intepret "Likes p1 p2" 
as asserting that the person, p1, likes the 
person, p2.
-/

axiom Person : Type
axiom Likes : Person → Person → Prop

/-
1. [30 points in 5 parts with 6 points each] 

For each part of this problem, write a formal 
proposition in Lean that expresses the given 
propositions given in English. Give you answers 
by filling them in in place of the holes.
-/

/-
1a. Everyone likes someone.
-/

def everyoneLikesSomeone : Prop := 
  (∀ (P: Person), ∃ (S : Person), Likes P S)

/-
1b. There is someone nobody likes.
-/

def thereIsSomeoneNobodyLikes : Prop :=
  (∃ (S : Person), ∀ P : Person, ¬Likes P S)

/-
1c. Someone likes everyone.
-/
def someoneLikesEveryone : Prop :=
  (∃ (S : Person), ∀ P : Person, Likes S P)

/-
1d. There is someone who doesn't like anyone.
-/

def thereIsSomeoneWhoLikesNoOne : Prop :=
  (∃ ( S : Person), ∀ P : Person, ¬Likes S P)

/-
1e. A predicate can be understood as defining 
a relation. The pairs in the relation defined
by the Likes predicate are all of those pairs
of persons, (p1, p2) such that "Likes p1 p2" is
true. What you are to express formally here is 
the proposition that "Likes is symmetric."
-/
def likesIsSymmetric : Prop :=
  ∀ p1 p2 : Person, Likes p1 p2 ↔ Likes p2 p1


/-
2. [5 points] Define a new predicate, LikedBy, 
true for Persons p1 and p2 if "Likes p1 p2". 
Remember that we formalize a predicate as a 
function. You should use the Likes predicate 
in formulating your answer.
-/

def LikedBy (p2 p1 : Person) : Prop :=
  Likes p1 p2

/-

3. [10 points] 
You are to prove that "if there is someone who
nobody likes, then if Likes is also a symmetric 
relation, then there is someone who doesn't like 
anybody." Give your formal proof in place of the 
hole.

Note: When you introduce the premises, they
will appear in your context with the name of
the enclosing "quantifiers" namespace attached. 
E.g., you'll see "quantifiers.likesIsSymmetric". 
If/when you want to use such a value, leave off 
the name of the namespace. For example, you 
would simply refer to the preceding value as 
likesIsSymmetric.
-/
open classical 

example : 
    thereIsSomeoneNobodyLikes → 
    likesIsSymmetric →
    thereIsSomeoneWhoLikesNoOne
:=
begin
  assume SNL,
  assume LIS,
  apply exists.elim SNL,
  assume S,
  assume Pfunc,
  -- have Sfunc := Pfunc S,
  apply exists.intro,
    assume P,
    assume like,
    have likeo := LIS S P,
    have likesp := likeo.1,
    have likeps := likesp like,
    have pf := Pfunc P,
    exact pf likeps,
    -- cases em (Likes P S) with l nl,
    --   contradiction,
    --   assume l,
    --   have Ls := LIS S P,
    --   have PS := Ls l,
    --   contradiction,
end

-- end of quantifiers namespace
end quantifiers



/- 
4. [10 points] Implication and bi-implication

Prove each of the following propositions. Hint: Don't get distracted
by seemingly confusing complexities. Just focus on the overall form 
and content of the propositions to be proved.
-/

-- 4a. Note: the conjecture to be proved is an implication.
example : 
(¬ ∃ (a b c n : ℕ), a > 0 ∧ b > 0 ∧ c > 0 ∧ n > 2 ∧ a^n + b^n = c^n) →
1 + 1 = 2 :=
begin
  assume func,
  exact rfl,
end 

-- 4b.
example : 
1 + 1 = 0 → 
(¬ ∃ (a b c n : ℕ), a > 0 ∧ b > 0 ∧ c > 0 ∧ n > 2 ∧ a^n + b^n = c^n) :=
begin
  assume ooz,
  assume func,
  have contra : 1 + 1 ≠ 0 :=
    begin
      apply nat.no_confusion,
    end,
  contradiction,
end


/-
Extra Credit [2 points[]]. What is the common name for the conjecture,
¬ ∃ (a b c n : ℕ), a > 0 ∧ b > 0 ∧ c > 0 ∧ n > 2 → a^n + b^n = c^n.

Your Answer: Fermat's Last Theorem

-/



-- 4c. [15 points] Prove that conjunction is associative.

example : ∀ (P Q R : Prop), P ∧ Q ∧ R ↔ (P ∧ Q) ∧ R :=
begin
  intros P Q R,
  apply iff.intro,
    assume pqr,
      have p := pqr.1,
      have q := pqr.2.1,
      have r := pqr.2.2,
      exact and.intro (and.intro p q) r,
    assume paqr,
      have paq := paqr.1,
      have r := paqr.2,
      have p := paq.1,
      have q := paq.2,
      exact and.intro p (and.intro q r),
end


/-
5. [20 points] Boolean Satisfiability.
-/

-- 5a. Find a solution; the only witnesses you may use are true and false.

example : ∃ (P Q : Prop), ((P ∧ ¬ Q) ∨ (Q ∧ ¬ P)) ∧ ¬ Q :=
begin
  apply exists.intro true,
  apply exists.intro false,
  split,
    apply or.inl,
      split,
        exact true.intro,
        exact false.elim,
      exact false.elim,
end

-- 5b. Show there is no satisfying solution for the following formula.
open classical

example : ¬ ∃ (P Q : Prop), ((P ∧ ¬ Q) ∨ (Q ∧ ¬ P)) ∧ ¬ (Q ∨ P) :=
begin
  assume func,
  apply exists.elim func,
  assume P,
  assume Pf,
  apply exists.elim Pf,
  assume Q,
  assume Qf,
  cases Qf with q1 q2,
    cases q1 with qq q3,
      have p := qq.1,
      have f : false := q2 (or.inr p),
      exact f,
      have q := q3.1,
      have f : false := q2 (or.inl q),
      exact f,
  -- cases em P with p np,
  --   cases em Q with q nq,
  --     have nqop := Qf.2,
  --     have f : false := nqop (or.inl q),
  --     exact f,
  --     have nqop := Qf.2,
  --     have f : false := nqop (or.inr p),
  --     exact f,
  --     cases em Q with q nq,
  --     have nqop := Qf.2,
  --     have f : false := nqop(or.inl q),
  --     exact f,
  --     have pnqqnp := Qf.1,
  --     cases pnqqnp with pnq qnp,
  --     have p := pnq.1,
  --     exact np p,
  --     have q := qnp.1,
  --     exact nq q,
end


/-
6. [10 points] Classical reasoning. Prove the following conjecture.
You may use the axiom of the excluded middle.
-/

open classical

example: ∀(A B: Prop),
  ¬(A ∧ B) → (¬A ∨ ¬B) :=
begin
  intros A B,
  assume nab,
  cases em A with a na,
    cases em B with b nb,
      have f : false := nab (and.intro a b),
      exact false.elim f,
      exact or.inr nb,
      exact or.inl na,
end