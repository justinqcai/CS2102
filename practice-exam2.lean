
/-
Conjunctions, disjunctions, implication, iff,
negation
-/

/-
1. Prove that 3 + 3 = 6 and 2 + 6 = 8 implies
that 1 + 1 = 2.
-/

-- answer:
example : 3 + 3 = 6 ∧ 2 + 6 = 8 → 1 + 1 = 2 :=
begin
     assume ttts,

     exact rfl,
end
/-
2. Prove that 2 + 5 = 3 or 9 + 1 = 5 implies
that 2 + 3 = 9.
-/

-- answer:
example : 2 + 5 = 0 ∨ 9 + 1 = 0 → 2 + 3 = 9 :=
begin
     assume tof,
     cases tof,
          have contra : 2 + 5 ≠ 0 :=
          begin
               apply nat.no_confusion,
          end,
          contradiction,
          have contra : 9 + 1 ≠ 0 :=
          begin
               apply nat.no_confusion,
          end,
          contradiction,
end
/-
3. Prove that ¬(A ∧ B ∧ C) ↔ (¬A ∨ ¬B ∨ ¬C).
You may use the axiom of the excluded middle.
-/
open classical
--axiom em: ∀(P: Prop), P ∨ ¬P

-- answer:
example : ∀ (A B C : Prop), ¬(A ∧ B ∧ C) ↔ (¬A ∨ ¬B ∨ ¬C) :=
begin
     intros A B C,
     apply iff.intro,
     /- forward -/
          assume nabc,
          cases em A with a na,
          cases em B with b nb,
          cases em C with c nc,
          have f : false := nabc (and.intro a (and.intro b c)),
          exact false.elim f,
          exact or.inr (or.inr nc),
          exact or.inr (or.inl nb),
          exact or.inl na,
     /- backward -/
          assume nanbnc,
          assume abc,
          cases nanbnc with na nbnc,
          have f : false := na abc.1,
          exact f,
          cases nbnc with nb nc,
          have f : false := nb abc.2.1,
          exact f,
          have f : false := nc abc.2.2,
          exact f,
end

/-
4. Prove that ¬(A ∨ B ∨ C) ↔ (¬A ∧ ¬B ∧ ¬C).
You may *NOT* use the axiom of the excluded middle.
-/
example : ∀ (A B C : Prop), ¬(A ∨ B ∨ C) ↔ (¬A ∧ ¬B ∧ ¬C) :=
begin
     intros,
     split,
          assume nabc,
          split,
          assume a,
          exact nabc (or.inl a),
          split,
          assume b,
          exact nabc (or.inr (or.inl b)),
          assume c,
          exact nabc (or.inr (or.inr c)),
          assume nabc,
          assume abc,
          cases abc with a bc,
          exact (nabc.1 a),
          cases bc with b c,
          exact (nabc.2.1 b),
          exact (nabc.2.2 c),
end
-- answer:
example : ∀ (A B C : Prop), ¬(A ∨ B ∨ C) ↔ (¬A ∧ ¬B ∧ ¬C) :=
begin
     intros A B C,
     apply iff.intro,
     /- forward -/
          assume nabc,
          apply and.intro,
          assume a,
          have f : false := nabc (or.inl a),
          exact f,
          apply and.intro,
          assume b,
          have f : false := nabc (or.inr (or.inl b)),
          exact f,
          assume c,
          have f : false := nabc (or.inr (or.inr c)),
          exact f,
     /-backward-/
          assume nanbnc,
          assume abc,
          cases abc with a bc,
          have na := nanbnc.1,
          exact false.elim (na a),
          cases bc with b c,
          have nb := nanbnc.2.1,
          exact false.elim (nb b),
          have nc := nanbnc.2.2,
          exact false.elim (nc c),
end
/-
5a. Prove that ¬(A ∨ ¬B) ↔ (¬A ∧ B).
You may use the axiom of the excluded middle.
-/

-- answer:
example : ∀ (A B : Prop), ¬(A ∨ ¬B) ↔ (¬A ∧ B) :=
begin
     intros A B,
     apply iff.intro,
     /- forward-/
          assume nanb,
          apply and.intro,
          assume a,
          have f : false := nanb (or.inl a),
          exact f,
          cases em B with b nb,
          exact b,
          have f : false := nanb (or.inr nb),
          exact false.elim f,
     /-backward-/
          assume nab,
          assume anb,
          cases anb with a nb,
          have na := nab.1,
          exact false.elim (na a),
          have b := nab.2,
          exact false.elim (nb b),
end
/-
5b. Prove that ¬(A ∧ ¬B) ↔ (¬A ∨ B).
You may use the axiom of the excluded middle.
-/

-- answer:
example : ∀ (A B : Prop), ¬(A ∧ ¬B) ↔ (¬A ∨ B) :=
begin
     intros A B,
     apply iff.intro,
     /-forward-/
          assume nanb,
          cases em A with a na,
          cases em B with b nb,
          apply or.inr b,
          have f : false := nanb (and.intro a nb),
          exact false.elim f,
          apply or.inl na,
     /-backward-/
          assume nab,
          assume anb,
          cases nab with na b,
          have a := anb.1,
          exact na a,
          have nb := anb.2,
          exact nb b,
end
/-
6. Prove that ¬P ∨ ¬Q ∨ R is true if and only
if P → Q → R. You may use the axiom of the
excluded middle.
-/
-- answer:
example : ∀ (P Q R : Prop ), (P → Q → R) ↔ (¬P ∨ ¬Q ∨ R) :=
begin
     intros P Q R,
     split,
          assume pqr,
          cases em P with p np,
          have QR := pqr p,
          cases em Q with q nq,
          have r := QR q,
          exact or.inr (or.inr r),
          exact or.inr (or.inl nq),
          exact or.inl np,

          assume npnqr,
          assume p,
          assume q,
          cases npnqr with np nqr,
               contradiction,
               cases nqr with nq r,
               contradiction,
               exact r,     
end
/-
7. Prove that ¬¬¬P → ¬P. You may use the axiom
of the excluded middle.
-/

-- answer:
example : ∀ P : Prop, ¬¬¬P → ¬P :=
begin
     intro P,
     assume nnnp,
     assume p,
     cases em ¬P with p np,
          contradiction,
          exact nnnp np,
end
/-
Universal Quantifiers, Existential Quantifiers, and
Satisfiability.
-/

/-
8. Prove the following statements are satisfiable
or prove that they are not. You may use the axiom
of the excluded middle to prove cases where the
statements are not satisfiable.
-/

/-
8a. (P ∨ Q) ∧ (¬P ∨ Q) ∧ (P ∨ ¬Q)
-/
example : ∃ P Q : Prop, (P ∨ Q) ∧ (¬P ∨ Q) ∧ (P ∨ ¬Q) :=
begin
     apply exists.intro true,
     apply exists.intro true,
     simp,
end
-- answer:
example : ∃ P Q : Prop, (P ∨ Q) ∧ (¬P ∨ Q) ∧ (P ∨ ¬Q) := 
begin
     apply exists.intro true,
     apply exists.intro true,
     split,
          exact or.inl true.intro,
          split,
          exact or.inr true.intro,
          exact or.inl true.intro,
end

/-
8b. (P ∨ Q) ∧ (¬P ∨ Q) ∧ (P ∨ ¬Q) ∧ (¬P ∨ ¬Q)
-/

-- answer:
example : ¬∃ (P Q : Prop), (P ∨ Q) ∧ (¬P ∨ Q) ∧ (P ∨ ¬Q) ∧ (¬P ∨ ¬Q) :=
begin
     assume func,
     apply exists.elim func,
     assume P,
     assume Pf,
     apply exists.elim Pf,
     assume Q,
     assume Qf,
     cases em P with p np,
          cases em Q with q nq,
               have npnq := Qf.2.2.2,
               cases npnq with np nq,
               contradiction,
               contradiction,
               have npq := Qf.2.1,
               cases npq with np q,
               contradiction,
               contradiction,
               cases em Q with q nq,
               have pnq := Qf.2.2.1,
               cases pnq with p nq,
               contradiction,
               contradiction,
               have pq := Qf.1,
               cases pq with p q,
               contradiction,
               contradiction,
end
/-
8c. (P ∨ Q ∨ R) ∧ (¬P ∨ Q ∨ R) ∧
     (P ∨ ¬Q ∨ ¬R) ∧ (¬P ∨ ¬Q ∨ ¬R)
-/
example : ∃ P Q R: Prop, (P ∨ Q ∨ R) ∧ (¬P ∨ Q ∨ R) ∧
     (P ∨ ¬Q ∨ ¬R) ∧ (¬P ∨ ¬Q ∨ ¬R) :=
begin
     apply exists.intro true,
     apply exists.intro true,
     apply exists.intro false,
     simp,
end
-- answer:
example : ∃ (P Q R : Prop), (P ∨ Q ∨ R) ∧ (¬P ∨ Q ∨ R) ∧
     (P ∨ ¬Q ∨ ¬R) ∧ (¬P ∨ ¬Q ∨ ¬R) :=
begin
     apply exists.intro true,
     apply exists.intro true,
     apply exists.intro false,
     split,
     exact or.inl true.intro,
     split,
     exact or.inr (or.inl true.intro),
     split,
     exact or.inl true.intro,
     exact or.inr (or.inr false.elim),


end
/-
9. Prove that exists a number such that
it is both even and a multiple of 3.
Use the supplied definitions of even and prime.
-/
def isEven' (n: ℕ ) := ∃ m :ℕ, n = m*2
def isMult3' (n: ℕ ) := ∃ m: ℕ, n = m*3

example : ∃ (n: ℕ ), isEven' n ∧ isMult3' n :=
begin
     apply exists.intro 6,
     split,
     unfold isEven',
     apply exists.intro 3,
     trivial,
     unfold isMult3',
     apply exists.intro 2,
     trivial,
end

def isEven(n: ℕ) := (∃(m: ℕ), m * 2 = n)

def isMult3(n: ℕ) := (∃(m: ℕ), m * 3 = n)

-- answer
example : ∃ (n: ℕ ), isEven n ∧ isMult3 n :=
begin
     have isEven6 : isEven 6 := ⟨3, rfl⟩,
     have isPrime6 : isMult3 6 := ⟨ 2, rfl ⟩ ,
     have both := and.intro isEven6 isPrime6,
     exact ⟨ 6, both ⟩ , 
end
/-
10a. Write the lemma that if there exists 
 someone that you can fool all of the time, 
 then there always exists someone you can fool.
 Use the supplied axioms, and make sure you use
 at least as many parentheses as needed. (It's
 okay to use more than you need.)
10b. Prove the above lemma.
-/

axioms Person Time: Type
axiom fool: Person → Time → Prop
example : (∃ p: Person, ∀ t: Time, fool p t) → 
     (∀ t : Time, ∃ p : Person, fool p t):=
begin
     assume foolish,
     assume T,
     apply exists.elim foolish,
     assume P,
     assume func,
     have ifunc := func T,
     apply exists.intro P,
     assumption,
end

-- answers:
example : (∃(p : Person), ∀ (t : Time), fool p t) → 
          (∀ (t : Time), ∃ (p : Person), fool p t) := 
begin
     assume idiot,
     assume t,
     apply exists.elim idiot,
     assume p,
     assume tpfunc,
     have idiotfunc := tpfunc t,
     exact ⟨ p, idiotfunc ⟩ ,
end
