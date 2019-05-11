/-
Justin Cai, jc5pz
Read and reread the chapters on implication and
bi-implication. Be sure to understand that a proof
of an implication is a function from proofs of the
premise to proofs of the conclusion, and that you
use such a function by applying it to a proof of a
premise to derive a proof of a conclusion. To build
your understanding, prove each of the following 
conjectures using first a tactic script and then 
in term-style.
-/

/- 1. -/
example : ∀ (P Q : Prop), P → Q → P ∧ Q :=
begin
    assume P Q,
    assume PimpQ,
    assume Q,
    exact and.intro PimpQ Q,
end


example : ∀ (P Q : Prop), P → Q → P ∧ Q :=
assume P Q,
assume PimpQ,
assume Q,
and.intro PimpQ Q

/- 2. -/
example : ∀ (P Q R : Prop), (P ∧ Q) → R → (P ∧ R) :=
begin
    assume P Q R,
    assume PQimpR,
    assume R,
    exact and.intro (and.elim_left PQimpR) R,
end


example : ∀ (P Q R : Prop), (P ∧ Q) → R → (P ∧ R) :=
    assume P Q R,
    assume PQimpR,
    assume R,
    and.intro (and.elim_left PQimpR) R


/- 3. -/
example : ∀ (P Q R : Prop), (P ∧ Q) → (Q ∧ R) → (P ∧ R) :=
begin
    assume P Q R,
    assume PQ,
    assume QR,
    exact and.intro (and.elim_left PQ) (and.elim_right QR),
end

example : ∀ (P Q R : Prop), (P ∧ Q) → (Q ∧ R) → (P ∧ R) :=
assume P Q R,
assume PQ,
assume QR,
and.intro (and.elim_left PQ) (and.elim_right QR)

/- 4. -/
theorem and_comm' : 
    ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P :=
begin
    assume P Q,
    apply iff.intro,
        assume PQ,
        exact and.intro (and.elim_right PQ) (and.elim_left PQ),
        assume QP,
        exact and.intro (and.elim_right QP) (and.elim_left QP)
end

theorem and_comm'' : 
    ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P :=
    assume P Q,
    iff.intro
    (assume PQ,
        and.intro (and.elim_right PQ) (and.elim_left PQ))
    (assume QP,
        and.intro (and.elim_right QP) (and.elim_left QP))


/- 5. -/
example : ∀ (P : Prop), P ∧ false → 0 = 1 :=
begin
    assume P,
    assume Pf,
    exact false.elim (and.elim_right Pf)
end


example : ∀ (P : Prop), P ∧ false → 0 = 1 :=
    assume P,
    assume Pf,
    false.elim (and.elim_right Pf)


/- 6. -/
example : ∀ (P : Prop), true ∧ P → P :=
begin
    assume P,
    assume Pt,
    exact and.elim_right Pt
end


example : ∀ (P : Prop), true ∧ P → P :=
    assume P,
    assume Pt,
    and.elim_right Pt


/- 7. Try using the rw tactic. -/
example : ∀ (n m k : ℕ), n = m → m = k → n = k :=
begin
    intros n m k,
    assume nm mk,
    rw nm,
    assumption,
end


example : ∀ (n m k : ℕ), n = m → m = k → n = k :=
    assume n m k,
    assume nm,
    assume mk,
    eq.trans nm mk


/- 8. -/
example : ∀ (s t : string), s = t ↔ t = s :=
begin
    assume s t,
    apply iff.intro,
        assume st,
        rw st,
        assume ts,
        exact eq.symm ts
end


example : ∀ (s t : string), s = t ↔ t = s :=
    assume s t,
    iff.intro
        (assume st,
        eq.symm st)
        (assume ts,
        eq.symm ts)


/- 9. -/
example : 
    ∀ (T : Type) (t1 t2 : T) (P : T → Prop),
        P t1 ∧ t1 = t2 → P t2 :=
begin
    assume T,
    assume t1 t2,
    assume P,
    assume Pt1t2,
    have Pt1 := and.elim_left Pt1t2,
    have t1t2 := and.elim_right Pt1t2,
    exact eq.subst t1t2 Pt1
end



example : 
    ∀ (T : Type) (t1 t2 : T) (P : T → Prop),
        P t1 ∧ t1 = t2 → P t2 :=
    λ T : Type,
        λ t1 t2 : T,
            λ P : T → Prop,
                assume Pt1t2 : P t1 ∧ t1 = t2,
                    let Pt1 := Pt1t2.left in
                        let t1t2 := Pt1t2.right in
                            eq.subst (t1t2) (Pt1)

#reduce let x : ℕ := 5 in let y : ℕ := 6 in x + y

/- 10. -/
theorem and_assoc' : 
    ∀ (P Q R : Prop), 
        P ∧ Q ∧ R ↔ (P ∧ Q) ∧ R :=
begin
    assume P Q R,
    apply iff.intro,
        assume PQR,
        have P := and.elim_left PQR,
        have QR := and.elim_right PQR,
        have Q := and.elim_left QR,
        have R := and.elim_right QR,
        exact (and.intro (and.intro P Q) R),
        assume PaQR,
        have PQ := and.elim_left PaQR,
        have R := and.elim_right PaQR,
        have P := and.elim_left PQ,
        have Q := and.elim_right PQ,
        have QR := and.intro Q R,
        exact (and.intro P QR)
end


theorem and_assoc'' : 
    ∀ (P Q R : Prop), 
        P ∧ Q ∧ R ↔ (P ∧ Q) ∧ R :=
assume P Q R,
    iff.intro
        (assume PQR : P ∧ Q ∧ R,
        let P := PQR.1 in
        let QR := PQR.2 in
        let Q := QR.1 in 
        let R := QR.2 in
        and.intro (and.intro P Q) (R))
        (assume PaQR : (P ∧ Q) ∧ R, 
        let PQ := PaQR.1 in
        let R := PaQR.2 in
        let P := PQ.1 in
        let Q := PQ.2 in
        and.intro P (and.intro Q R))


theorem and_assoc''' : 
    ∀ (P Q R : Prop), 
        P ∧ Q ∧ R ↔ (P ∧ Q) ∧ R :=
begin
    assume P Q R,
    split,
    assume h,
    have p := h.left,
    have qr := h.right,
    have q := h.right.left,
    have r := h.right.right,
    exact ((p, q), r),
        assume PaQR,
        have PQ := and.elim_left PaQR,
        have R := and.elim_right PaQR,
        have P := and.elim_left PQ,
        have Q := and.elim_right PQ,
        have QR := and.intro Q R,
        exact (and.intro P QR)
end