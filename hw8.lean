
/-
Justin Cai, jc5pz
-/

/- 1a. 

Implement a function, bool_implies, that takes
two bool values, b1 and b2 (not propositions),
and that returns the the value of b1 → b2.
Here the → operator means implication in Boolean
algebra. To know what your function should do,
write out the truth table for implication. You
may  not use Lean's → operator (which does work
for bool values, by the way) in your answer. 
-/

def bool_implies : bool → bool → bool
|   tt tt := tt
|   tt ff := ff
|   ff tt := tt
|   ff ff := tt


/- 1b.
Given your implementation of bool_implies,
prove the following proposition. Use induction
rather than the cases tactic to do case
analysis on Boolean values. 
-/

example : ∀ b1 b2 : bool, 
    (bool_implies b1 b2 = tt) → (b2 = tt ∨ b1 = ff) :=
begin
    intros b1 b2,
    assume bitt,
    induction b1,
    apply or.inr,
    exact rfl,
    induction b2,
    contradiction,
    apply or.inl,
    exact rfl,
end 

/- 2a.

A tree of natural numbers is either empty or
it is constructed from a natural number and
two smaller trees of natural numbers. Give
an inductive definition of the type of such
trees. Call you datatype tree_nat. Your type
will have two constructors. Call the first
one "empty", and call the second "node".
Hint: The second will take three arguments.
-/

inductive tree_nat : Type
| empty : tree_nat
| node : ℕ → tree_nat → tree_nat → tree_nat

/- 2b.

Define aTree to be a node containing the
value 3 and two trees, the first one empty
and the second one a node containing the
value 2 and two empty trees.
-/

def aTree := 
tree_nat.node 3 tree_nat.empty 
    (tree_nat.node 2 tree_nat.empty tree_nat.empty)
    


/- 3. Define a polymorphic type, "tree", 
just like tree_nat, but where the value stored
in a node can be of any type, T. Then define 
aTree' to be the same as aTree except that it's 
now of type tree rather than of type tree_nat.
Make the type argument implicit. Finally
define a tree of strings, aTree'', just like
aTree' except that 3 is replaced by "Hi!" and
2 is replaced by "Jo".
-/

-- Your answer here
inductive tree {T: Type}: Type
| empty : tree
| node : T → tree → tree → tree

def aTree' := tree.node 3 tree.empty (tree.node 2 tree.empty tree.empty)

def aTree'' := tree.node("Hi!") tree.empty (tree.node "Jo" tree.empty tree.empty)

/- 4.

Write a recursive function, num_nodes, 
that takes a value of type tree T, as an 
argument, where T is some type, and that 
returns the number of nodes in the tree. 
The number of nodes in an empty tree is zero, 
while the number of nodes in a non-empty 
tree is one (for the "top" node) plus the 
number of nodes in each of the subtrees.

The "at sign" before "tree" in the following
function signature tells Lean that even though
tree takes its type argument implicitly, in 
this case we want to give it explicitly. We
need to specify T explicitly here because Lean
has no way of knowing that's what we want.
-/

def num_nodes : ∀ {T : Type}, @tree T → nat
| T tree.empty := 0
| T (tree.node n1 n2 n3) := 1 + num_nodes(n2) + num_nodes(n3)


/- 
The following questions use our definition of
the nas to practice proof by induction. Here is
our nat type and the implementations of addition
and multiplication.
-/

inductive mynat : Type
| zero : mynat
| succ : mynat → mynat

def add_mynat: mynat → mynat → mynat
| mynat.zero m := m
| (mynat.succ n') m :=
    mynat.succ (add_mynat n' m)

def mult_mynat: mynat → mynat → mynat
| mynat.zero m := mynat.zero
| (mynat.succ n') m :=
    add_mynat m (mult_mynat n' m) 


/-
Here's a proof that zero is a right identity
for addition. We explain details in comments.
You will want to use some of the same ideas in
your proofs. 
-/

theorem zero_right_id_add : ∀ (n : mynat),
    add_mynat n mynat.zero = n :=
begin
-- forall introduction
intro n,
-- induction
induction n with n' ih,

-- base case
exact rfl,

-- recursive case
-- first simplify based on definition of add_mynat
simp [add_mynat],
-- now apply induction hypothesis
exact ih,
end

/- #5

Prove the following by induction on n in Lean.
-/

-- 5b. Prove that succ (n + m) = n + (succ m).
theorem add_succ': ∀ (n m : mynat) , mynat.succ (add_mynat n m) = add_mynat n (mynat.succ m) :=
begin
    intros n m,
    induction n with n' ih,
    simp[add_mynat],
    simp[add_mynat],
    assumption,
end

theorem add_succ : ∀ (n m : mynat), 
    mynat.succ (add_mynat n m) = add_mynat n (mynat.succ m) :=
begin
    intros n m,
    induction n with n' ih,
    exact rfl,
    simp [add_mynat],
    assumption,
end


-- 5a. Prove zero is a right identity for mult.
theorem zero_right_absorb_mult' : ∀ (n : mynat),
    mult_mynat n mynat.zero = mynat.zero :=
begin
    intro n,
    induction n with n' ih,
    trivial,
    simp[mult_mynat],
    assumption,
end

theorem zero_right_absorb_mult : ∀ (n : mynat), 
  mult_mynat n mynat.zero = mynat.zero :=
begin
    intros n,
    induction n with n' ih,
    exact rfl,
    induction n',
    exact rfl,
    simp [mult_mynat],
    assumption,
end

-- 5b. Prove addition is associative.
theorem addition_assoc' :
    ∀ (n m p : mynat),
        add_mynat (add_mynat n m) p = 
        add_mynat n (add_mynat m p) :=
begin
    intros n m p,
    induction n with n' ih,
    trivial,
    simp[add_mynat],
    assumption,
end

theorem addition_assoc : 
    ∀ (n m p : mynat), 
        add_mynat (add_mynat n m) p = 
        add_mynat n (add_mynat m p) :=
begin
    intros n m p,
    induction n,
    exact rfl,
    simp [add_mynat],
    assumption,
end

-- 5c. Prove addition is commutative.
lemma add_n_succ_m': 
    ∀ n m : mynat,
        add_mynat n (mynat.succ m) =
            mynat.succ (add_mynat n m) :=
    begin
        intros n m,
        induction n with n' ih,
        trivial,
        simp[add_mynat],
        assumption,
    end
lemma add_n_succ_m :
    ∀ n m : mynat,
        add_mynat n (mynat.succ m) =
            mynat.succ (add_mynat n m) :=
    begin
        intros n m,
        induction n with n' h,
            apply rfl,
            simp[add_mynat],
            assumption,
    end

theorem addition_comm' :
    ∀ (n m : mynat), add_mynat n m = add_mynat m n :=
begin
    intros n m,
    induction n,
    simp[add_mynat],
    induction m,
    trivial,
    simp[add_mynat],
    assumption,
    simp[add_mynat],
    rw n_ih,
    rw add_succ,
end

theorem addition_comm :
    ∀ (n m : mynat), add_mynat n m = add_mynat m n :=
begin
    intros n m,
    induction n with n' ih,
    induction m with m' ih2,
    exact rfl,
    simp[add_mynat],
    assumption,
    simp[add_mynat],
    rw ih,
    rw add_n_succ_m,
    -- induction m with m' ih',
    --     simp [add_mynat],
    --     simp[add_mynat],
        
end


/- 6a. 

Complete then test the following definition of
a function that computes the n'th Fibonacci 
number when given n as an argument.
-/
def fib' : ℕ → ℕ 
| nat.zero := 0
| (nat.succ nat.zero) := 1
| (n + 2) := fib'(n + 1) + fib'(n)

def fib : ℕ → ℕ 
| nat.zero := 0
| (nat.succ nat.zero) := 1
| (n + 2 ) := (fib (n+1)) + fib n

#eval fib 8

/- 6b.

Implement the factorial function. You will need to 
define the function for both its base and recursive
cases.
-/

def fac : ℕ → ℕ
| nat.zero := 1
| (nat.succ n) := (nat.succ n) * (fac n)


/- 7.

Give an *informal* proof by induction of the proposition
that forall natural numbers, n, the sum of the natural 
numbers from 0 to n is n * (n + 1) / 2.

1. Let n be a number. Prove by induction 
    a. Base case
        1. The sum of all numbers from 0-n is equal to n * (n + 1) / 2
        2. The sum of all numbers from 0-n is 0 if n = 0
    b. Inductive case
        1. Assume relationship is true for P(n) and prove for P(n+1)
        2. 0+1+...+(n-1)+n = n*(n + 1)/2
        3. Substitute 0+1+...+(n-1)+n  with n * (n + 1) / 2
        4. Simplify left side by commutative property: (n + 1) * (n + 2) / 2
        5. Distribute: (n^2 + 3n + 2) / 2
        6. Distribute the left side: (n^2 + 3n + 2) / 2 + (n + 1) = (n^2 + 3n + 2)
        7. Separate terms: (n^2) / (2+)n / 2 + (n+1) = (n^2) / (2+3n) / (2+2) / 2
        8. Eliminate from both sides: (n + 1) = 2n / 2 + 2 / 2
        9. Simplify: (n + 1) = n + 1
2. Proven for base and induction case, therefore this is true for all natrual numbers
-/