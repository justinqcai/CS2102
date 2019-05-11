/- Justin Cai, jc5pz -/

/-
Read, and if you have already read, then re-read, the 
chapters in the notes on proofs of disjunctions and negations. 
We have added some new material, especially under negation
elimination.

In proofs of bi-implications, use comments to mark the start of
the proofs of the implications in each direction. Label one as
"forward" the other other as "backward."

The collaboration policy for this homework is "no collaboration
allowed." You may study and discuss the underlying concepts with
anyone.

You may provide proofs in the style of your choice: term-style,
tactic style, or mixed. Yes, you can using tactic scripts within
terms and terms within tactic scripts. You may use any tactics 
you know of. As a courtesy, we provide begin/end pairs, in case
you should want to use them. Otherwise you may delete them.
-/

/- 
1. 15 points
-/
example : ∀ (P Q : Prop), P ∧ Q → P ∨ Q :=
begin
    intros P Q,
    assume paq,
    have p := paq.left,
    exact or.inl p,
end


/-
2. 15 points
-/
example : 
    ∀ (P Q R : Prop), (P ∨ Q) → (Q ∨ R) → ¬ Q → (P ∧ R) :=
begin
    intros P Q R,
    assume poq,
    assume qor,
    assume nq,
    cases poq with p q,
    cases qor with q r,
    
        contradiction,
        exact and.intro p r,
        contradiction,
end 

/-
3. 15 points
-/
example : 
    ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) :=
begin
    intros P Q R,
    apply iff.intro,
    /- forward -/
        assume paqor,
        have p := paqor.1,
        have qor := paqor.2,
        cases qor with q r,
            apply or.inl,
            exact and.intro p q,
            apply or.inr,
            exact and.intro p r,
    /- backward -/
        assume paqopar,
        cases paqopar with paq par,
           have p := paq.1,
           have q := paq.2,
           exact and.intro p (or.inl q),
           have p := par.1,
           have r := par.2,
           exact and.intro p (or.inr r),
end


/-
4. 10 points
-/

example : ∀ (P Q R : Prop), P → Q → R → ¬ Q → (Q ∨ ¬ Q) :=
begin
    intros P Q R,
    assume p,
    assume q,
    assume r,
    assume nq,
    contradiction,
end

open classical      -- hint: you can now use em easily

/-
4a. 5 points. Write *your own* proof of this conjecture.
-/

example : ∀ (P Q : Prop), ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q :=
begin
    intros P Q,
    apply iff.intro,
    /- forward-/
        assume npoq,
        cases em P with p np,
        have f : false := npoq (or.inl p),
        exact false.elim f,
        cases em Q with q nq,
        have f : false := npoq (or.inr q),
        exact false.elim f,
        exact and.intro np nq,
    /-backward-/
        assume npanq,
        assume npoq,
        cases npoq with p q,
        have np := npanq.left,
        contradiction,
        have nq := npanq.right,
        contradiction,
end

/-
4b. 5 points. Is this theorem classically true in neither, one, or
both directions. Explain your answer in relation to your proof. 

Answer: 
This theorem is classically true in both directions. It's definitely
classically true in forward direction because it requires the use of em 
(aka classical logic) for the proof to even work, and it's classically true
in backward direction because the backward proof is true in constructive
logic, making it also true in classical logic.
-/

/-
5. 5 points. Write *your own proof* of this conjecture.
-/
example : ∀ (P Q : Prop), ¬ (P ∧ Q) ↔ (¬ P ∨ ¬ Q) :=
begin
    intros P Q,
    apply iff.intro,
    /- forward -/
        assume npaq,
        cases em P with p np,
        cases em Q with q nq,
        have f : false := npaq (and.intro p q),
        exact false.elim f,
        exact or.inr nq,
        exact or.inl np,
    /-backward-/
        assume nponq,
        assume paq,
        cases nponq with np nq,
        have p := paq.left,
        have f : false := np p,
        exact false.elim f,
        have q := paq.right,
        have f : false := nq q,
        exact false.elim f,
end


/-
6. 10 points
-/

example : ∀ (P : Prop), (¬ ¬ P → P) ↔ (P ∨ ¬ P) :=
begin
    intro P,
    apply iff.intro,
    /-forward-/
        assume nnpp,
        cases em P with p np,
        exact or.inl p,
        exact or.inr np,
    /-backward-/
        assume ponp,
        assume nnp,
        cases ponp with p np,
        exact p,
        contradiction,
end


/-
7. 5 points

Tranlate the preceding proposition into English,
referring explicitly to the principles of negation 
elimination and excluded middle. Write your sentence
here:

The proposition states that for all P of type Prop, (P implies false 
implies false implies P) implies ((P or P implies false) is true), and vice
versa.

1. Assumed P
2. Applied bi-implication introduction
3. Forward proof
    a. Assumed not not P implies P
    b. Used the law of excluded middle (which states that either P or not P
    must be true) to create two cases for P to prove.
    I must prove: 
        1. that if P is true then P or not P is true
        2. and that if not P is true then P or not P is true
    c. Since I am given a proof of P, I am able to apply the or introduction
    rule for the left side (which is asking for a proof of P)
    d. Since I am given a proof of not P, I am able to apply the or 
    introduction rule for the right side (which is asking for a proof of 
    not P)
4. Backward proof
    a. Assumed P or not P is true
    b. Assumed not not P is true
    c. Created two cases for P or not P to prove.
    I must prove:
        1. If P is true, then P is true
        2. If not P is true, then P is true
    d. Since I am given a proof of P, all I had to do was apply that proof of P to
    prove that P is true
    e. Since I am given a proof of not P and a proof of not not P, there is a 
    contradiction in the proposition due to negation elimination; all I had to do 
    was apply the contradiction rule
-/


/-
8. [10 points]
-/
example : 
    (∀ ( P Q : Prop ), (P → Q) ↔ (¬ Q → ¬ P)) → 
        ∀ (Raining Wet : Prop), (¬ Wet → ¬ Raining) → 
            (Raining → Wet) :=
begin
    intros PQ,
    assume Raining Wet,
    assume nWetnRaining,
    assume Rain,
    have RainingWet := PQ Raining Wet,
    have RWback := RainingWet.2,
    exact RWback nWetnRaining Rain,
end

example : 
    (∀ ( P Q : Prop ), (P → Q) ↔ (¬ Q → ¬ P)) → 
        ∀ (Raining Wet : Prop), (¬ Wet → ¬ Raining) → 
            (Raining → Wet) :=
begin
    intros PQnQnP Raining Wet,
    assume nwnr,
    assume r,
    have pfRW := PQnQnP Raining Wet,
    apply iff.elim_right pfRW nwnr,
    exact r,
end


/-
9. [5 points]

What is the name of the principle expressed by the
premise, (P → Q) ↔ (¬ Q → ¬ P)), in the preceding
problem? Answer here:

Proof by Contrapositive 
-/