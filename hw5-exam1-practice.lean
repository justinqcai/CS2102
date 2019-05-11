/-
Justin Cai, jc5pz
Here is the practice exam. It provides you
with a set of problems illustrative of the
material to be tested. This is a homework
assignment due this coming Thursday. We will
review the questions in class.

Copy this file your "work" directory. Work
on it there. Upload to Collab when done.

Note: An incorrect answer above or below
a correct answer can cause Lean to be unable
to process the correct answer. If you are not
able to complete a problem successfully please
comment out your incomplete answer so that we
can see your work but so that your incomplete
work does not cause problems for surrounding
problems and answers.
-/

/-
PART I: Functions. Functions are an essential
element of the language of predicate logic. In
this section, you show that you understand how
to define, use, and reason about functions in
Lean.
-/

/- 1.
Study each of the following definitions,
then answer the associated question about
the types involved in these definitions.
-/

-- Consider this function
def f (n : ℕ) (s : string) := s

/-
a. What is it's return type? Answer:
string
-/

/-
b. What is the type of (f 5)? Answer:
string
-/

/-
c. What is the value of (f 0 "yay")
"yay"
-/

/-
d. What is the type of this function?
ℕ → string
-/


/- 2.
Define three functions called square,
square', and square'', each of type
ℕ → ℕ. Each function must return the
square of the value to which it is
applied. Write the first function in
"C" style, the second using a tactic
script, and the third using a lambda
abstraction. Declare all argument and
return types explicitly. Answer below.
-/
def square (x: nat) : nat := x^2

def square': ℕ → ℕ :=
begin
    assume x,
    exact x*x,
end


def square'': ℕ → ℕ := λ x, x^2




/- 3.
Construct three proofs to test your
function definitions. The first must
use "lemma" to define a proof, called
square_3_9, of the proposition that
(square 3) equals 9. The second must
use "theorem" to define a proof, called
square'_4_16, of the proposition that
square' applied to 4 reduces to 16. The
third must prove that square'' 5 is
equal to 25. This third proof must not
use the equals sign, =, but must use
"eq" instead to state the proposition
to be proved. Hint on #3, sometimes
you need to use parentheses to express
how you want terms to be grouped. Answer
below.
-/

lemma square_3_9 : 9 = 9 :=
begin
    apply eq.refl(square 3)
end

theorem square'_4_16 : 16 = 16 :=
begin
    apply eq.refl(square' 4)
end

example: eq 25 25 := 
begin
    apply eq.refl(square'' 5)
end





/- 4.
Define a function called last_first.
It must take two string values, called
"first" and "last" (without quotes),
and return a string consisting of "last"
followed by a comma and a space followed
by "first".

For example (last_first "Orson" "Welles")
must return the string, "Welles, Orson".
Write a test case for your function to
prove that (last_first "Orson" "Welles")
is "Welles, Orson". Use "example", to
check the proof. Hint: The ++ operator
implements the string append function.
Answer below.
-/
def last_first (first: string) (last: string) := last ++ ", " ++ first
example: last_first "Orson" "Welles" = "Welles, Orson" :=
begin
    apply eq.refl
end



/- 5.

Complete the following definition of a
function, called apply3. It takes, as an
argument, a function, you might call it f,
of type ℕ → ℕ. It must return a function,
also of type ℕ to ℕ, that, when applied
to a value, n, returns the result of
applying the given function, f, to the
given value, n, three times. The function
returned must compute f(f(f(n))) when it
is applied to an argument, n.
-/

def apply3 :(ℕ → ℕ) → (ℕ → ℕ) :=
    λ f : ℕ → ℕ,
    λ n:ℕ , 
    f(f(f n))

/- 6.

The Lean libraries define a function,
string.length, that takes a string and
returns its length as a natural number.
Define a function, len2, that takes two
strings and returns the sum of their
lengths. You may use the ++ operator
but not the + operator in your answer.
Follow your function definition with a
test case in the form of a proof using
"example" showing that len2 applied to
"Orson" and "Welles" is 11. Remember:
you might need parenthesis in some
cases to group terms correctly into
larger terms.
-/
def len2 (first: string) (second: string) : ℕ := 
    (first ++ second).length
example: len2 "Orson" "Welles" = 11 :=
begin
    apply eq.refl
end

/- 7.
Use "example" to prove that there is a
function of the following type:

((ℕ → ℕ) → (ℕ → ℕ)) →
    ((ℕ → ℕ) → ℕ) →
        ((ℕ → ℕ) → ℕ)
-/
example: ((ℕ → ℕ) → (ℕ → ℕ)) → 
    ((ℕ → ℕ ) → ℕ ) → ((ℕ→ℕ) → ℕ) :=
begin
    assume a b c,
    exact b c
end

/-
PART II: Functions, revisited. In
mathematics,  functions play a central
role. A function, f, in the mathematical
sense is a triple, f = { D, P, C }, where
D, a set, is the domain of definition of
f, C is the co-domain of f, and P is a
set of ordered pairs, each with a first
element from D and a second element from
C,. In addition, P has one additional
essential  property, the subject of one
of the following questions.
-/

/- 8.

What one additional property is essential to
the definition of what it means for a triple,
{ D, P, C } to be a function?

Name the property. Answer:
Single valued

Now explain precisely what it means:  "That there
are no two pairs, (x, y) and (x', y') such that..."

Fill in the blank, and use a logical ∧ in answering.
You might also want to use = or ≠.

Answer:
x=x' ∧ y ≠ y'
x can equal x' and y isn't equal to y'
-/

/- 9.

Give names to the following concepts:

The set of all values appearing as the first
element of any pair in P.

Answer: Domain

The set of all values appearing as the second
element of any pair in P.

Answer: Range

The property that the set of all values
appearing as the first element of P is the
same as the entire set, D.

Answer: Total

The property that the set of all 
values appearing as the second element of 
P is the same as the entire set, C. 

Answer: Surjective

The property of being one-to-one and onto.

Answer: Bijective

-/

/- 10.

What does it mean for a function, f, to be
injective? Give you answer by completing the
following sentences with logical expressions.

"A function, f, is said to be injective if
it has no two pairs, (x, y) and (x', y'),
such that ..."

Answer: x ≠ x' ∧ y=y'

In other words, "If (x, y) and (x', y') are
related by f and x ≠ x' then ..."

Answer:
f(x) ≠ f(x')
-/


/- 11.

Suppose that S and T are types and that f
is defined to be a function, *in Lean*, of
type S → T. Which of the following properties,
if any, does f necessarily have?

- injective
- surjective
- bijective
- one-to-many
- one-to-one
- onto
- single-valued
- partial
- total

Answer:
Surjective, total
-/

/-
PART III: Logic and Proof.
-/

/- 12a.

Use axiom and/or axioms in Lean to express,
in formal logic, the following assumptions:

- T is a type
- t1 and t2 are values of type T
- t1 = t2

Answer immediately after this comment block.
If you need to introduce a name, use eqt1t2.
-/
axiom T : Type
axioms t1 t2 : T
axiom eqt1t2 : t1 = t2


/- 12b.

Use axiom or axioms to represent the
additional assumptions that

- P is a predicate expressing a property of objects of type T
- t1 has property P

If you need to use a name, use Pt1
-/
axiom P : T → Prop
axiom Pt1 : P t1


/- 12 c.

Now use "example" to assert, and then
prove, that t2 also has property P.
-/
example : P t2 := eq.subst eqt1t2 Pt1

/- 13 a.
Define eq_1_0 to be the proposition, 1 = 0.
-/
def eq_1_0 : Prop := 1 = 0


/- 13 b.
Define pf_eq_0_0 to be a proof of the
proposition that 0 = 0. Use the lemma
keyword.
-/
lemma pf_eq_0_0 : 0 = 0 := rfl

/- 13 c.
Write a function, w, that takes three
values, a, b, and c of type ℕ, and that
also takes proofs, cb : c = b, and
ba : b = a, and that returns a proof
that a = c.
-/
def w (a b c: ℕ ) (cb: c = b) (ba : b = a) : a = c := 
    eq.trans(eq.symm ba) (eq.symm cb)


/- 13d.

What is the type of this function?

Answer: ℕ → c = b → b = a → a = c

What is the form of this proposition?

Answer: ℕ → Prop → Prop → Prop

What's the form the proposition after the
comma?

Answer: ℕ → Prop

What is the premise of the proposition after
the comma?

Answer: For 3 Nats a b c given c = b and b = a, then a = b and b = c then a = c

-/

/- 14.
Complete the following proofs. Give each one
in the form indicated by a comment preceding
the statement of the conjecture to be proved.
When using tactic scripts, remember to write
begin/end pairs right away, so Lean knowns
you want to use a tactic script.
-/

-- lambda expression
example : ∀ (s : string), s = s :=
λ s: string,
eq.refl s


-- lambda expresion
example : ∀ (n : ℕ), ∀ (m : ℕ), true :=
λ n m: ℕ, true.intro


-- tactic script
example : ∀ (T : Type), ∀ (t : T), eq t t :=
begin
    assume T: Type,
    assume t: T,
    exact eq.refl t
end


-- tactic script
example :
    ∀ (T : Type),
    ∀ (P : T → Prop),
    ∀ t1 t2 : T,
    ∀ Pt1 : P t1,
    ∀ t2t1 : t2 = t1,
    P t2 :=
begin
    assume T P t1 t2 Pt1 t2t1,
    exact eq.subst (eq.symm(t2t1)) Pt1
end

/-
The following problems involve implications.
For example, false → P in an implication. To
prove an implication, just show that there is
(give) a function of the specified type.
-/

-- lambda expression
example : ∀ (P : Prop), false → P :=
λ P i, false.elim i


-- tactic script
example : ∀ (P : Prop), false → P :=
begin
    assume P i,
    exact false.elim i
end
    


-- lambda expression
example : ∀ (P Q : Prop), P ∧ Q → Q ∧ P :=
λ P Q,
    λ pq: P ∧ Q, 
        and.intro pq.elim_right pq.elim_left


-- tactic script
example : ∀ (P Q : Prop), P ∧ Q → Q ∧ P :=
begin
    assume P Q,
    assume pq: P ∧ Q,
    exact and.intro pq.elim_right pq.elim_left
end


-- tactic script
example :
    ∀ T : Type,
    ∀ (t1 t2 t3 : T),
    t1 = t2 ∧ t2 = t3 → t1 = t3 :=
begin
    assume T t1 t2 t3,
    assume t1t2t3: t1 = t2 ∧ t2 = t3,
    exact eq.trans(t1t2t3.elim_left) (t1t2t3.elim_right)
end



/- 15.

Use Lean to model a world in which there
are Dogs, all Dogs are friendly, and Fido
is a Dog, with a proof that in this world,
Fido must be friendly, too.
-/
axiom Dog : Type
axiom Fido : Dog
axiom Friendly: Dog → Prop
axiom FriendlyDog : ∀ d: Dog, Friendly d
example : Friendly Fido :=
begin
    exact FriendlyDog Fido
end
