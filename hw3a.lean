/-
Justin Cai, jc5pz

/-
Complete each of the following partial definitions in Lean by replacing 
the underscore characters with code to define functions of the specified 
types using lambda notation. We only care that you define some function 
of each required type, not what particular function you define.

In preparation, note that if you hover your mouse over an underscore, 
Lean will tell you what type of term you is needed to fill that hole. 
The type that Lean requires appears after the "turnstile" symbol, |-, 
in the message Lean will give you. Even more interestingly, if you 
fill in a hole with a term of the right type that itself has one or 
more remaining holes, Lean will tell you what types of terms are needed 
to fill in those holes! You can thus fill a hole in an incremental manner, 
refining a partial solution at each step until all holes are filled, 
guided by the types that Lean tells you are needed for any given hole. 
We recommend that you try developing your answers in this "top-down 
structured" style of programming. That said, we will grade you only on 
your answers and not on how you developed them.
-/
-/
-- 9. 
def hw2_1: ℕ → ℕ :=
    λ(x: ℕ), 
        x * x


-- 10.
def hw2_2: ℕ → ℕ → ℕ :=
    λ (x: ℕ),
        λ (y: ℕ ),
                x * y


-- 11.
def hw2_3: (ℕ → ℕ) → (ℕ → ℕ) :=
    λ (x: ℕ → ℕ ),
        λ (y: ℕ ),
                x y


-- 12.
def hw2_4: (ℕ → ℕ) → ((ℕ → ℕ) → ℕ) :=
    λ (x: ℕ → ℕ ),
        λ (y: ℕ → ℕ),
                x (y 1)



-- 13.
def hw2_5: (ℕ → ℕ) → ((ℕ → ℕ) → (ℕ → ℕ)) :=
    λ (x: ℕ → ℕ ),
        λ (y: ℕ → ℕ ),
                λ (z: ℕ ),
                        x (y z)
