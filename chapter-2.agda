-- Induction makes you feel guilty for getting something out of
-- nothing … but it is one of the greatest ideas of civilization.
--                                                - Herbert Wilf

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)

-- left identity C:               C op n ≡ n
-- right identity C:              n op C ≡ n
-- associativity:          m op (n op p) ≡ (m op n) op p
-- commutativity:                 m op n ≡ n op m
-- distributivity (op₁ over op₂)
-- from the left         (n op₂ p) op₁ m ≡ (n op₁ m) op₂ (p op₁ m)
-- from the right        m op₁ (n op₂ p) ≡ (m op₁ n) op₂ (m op₁ p)

-- Exercise operators (practice)

-- A pair of operators that have an identity and are associative,
-- commutative, and distribute over one another.


-- operator ∨
-- left identity F                 F ∨ p ≡ p
-- right identity F                p ∨ F ≡ p
-- associativity             p ∨ (q ∨ r) ≡ (p ∨ q) ∨ r
-- commutativity                   p ∨ q ≡ q ∨ p

-- operator ∧
-- left identity T                 T ∧ p ≡ p
-- right identity T                p ∧ T ≡ p
-- associativity             p ∧ (q ∧ r) ≡ (p ∧ q) ∧ r
-- commutativity                   p ∧ q ≡ q ∧ p
-- distributivity (left)     p ∧ (q ∨ r) ≣ (p ∧ q) ∨ (p ∧ r)
--                (right)    (p ∨ q) ∧ r ≡ (p ∧ r) ∨ (q ∧ r)


-- Has an identity and is associative but is not commutative.

-- operator -
-- no left identity               
-- right identity 0:                  n - 0 ≡ n
-- associativity:               m - (n - p) ≡ (m - n) - p
-- no commutativity

-- operator /
-- no left identity               
-- right identity 1:                  n / 1 ≡ n
-- associativity:               m / (n / p) ≡ (m / n) / p
-- no commutativity 
-- distributivity (only right)  (n - p) / m ≡ (n / m) - (n / p)



-- ASSOCIATIVITY

_ : (3 + 4) + 5 ≡ 3 + (4 + 5)
_ =
  begin
    (3 + 4) + 5
  ≡⟨⟩
    7 + 5
  ≡⟨⟩
    12
  ≡⟨⟩
    3 + 9
  ≡⟨⟩
    3 + (4 + 5)
  ∎



-- PROOF BY INDUCTION

-- definition:
--   base case: zero is a natural
--   inductive case: if m is a natural then suc m is a natural

-- proof:
--   base case: show property holds for zero
--   inductive case: assuming property P holds for an arbitrary number m,
--                   show that P also holds for suc m



-- OUR FIRST PROOF: ASSOCIATIVITY

-- we are defining the identifier +-assoc which provides evidence for
-- the proposition ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
-- (admire the universal quantifier!)
+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)

-- proof for base case
+-assoc zero n p = 
  begin
    (zero + n) + p
  ≡⟨⟩                -- because base case: zero + n ≡ n
    n + p
  ≡⟨⟩                -- because base case in reverse: x ≡ zero + x
    zero + (n + p)
  ∎
  
-- proof for inductive case
+-assoc (suc m) n p =
  begin
    ((suc m) + n) + p 
  ≡⟨⟩                -- because inductive case of addition: (suc m) + n = suc (m + n)
    suc (m + n) + p
  ≡⟨⟩                -- because reverse inductive case of addition
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩ -- we provide a JUSTIFICATION
                                -- using the CONGRUENCE relation

                                -- cong suc (+- assoc m n p)
                                -- takes
                                --   (m + n) + p ≡ m + (n + p)
                                -- and yields
                                --   suc ((m + n) + p) ≡ suc (m + (n + p))

                                -- WHAT THIS MEANS:
                                -- since we assume that P m n p holds
                                -- we know that ((m + n) + p) ≡ (m + (n + p))
                                -- so we can replace ((m + n) + p)
                                -- with (m + (n + p))
    suc (m + (n + p))
  ≡⟨⟩                            -- because reverse inductive case:
                                -- suc (m + n) = (suc m) + n
    (suc m) + (n + p)
  ∎

-- NOTE: Identifiers cannot contain @ . () {} ; _
-- NOTE: ≡⟨⟩ this is a chain reasoning operator
--
--       also it looks like a jellyfish
--       ≡⟨...⟩ is a jellyfish with a big thought



-- INDUCTION AS RECURSION



-- TERMINOLOGY AND NOTATION

-- this
-- +-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
-- is equivalent to this
-- +-assoc : ∀ (m : ℕ) → ∀ (n : ℕ) → ∀ (p : ℕ) → (m + n) + p ≡ m + (n + p)

-- functions with universally quantified arguments are DEPENDENT FUNCTIONS



-- OUR SECOND PROOF: COMMUTATIVITY
-- LEMMA: zero is a left-identity

+-identity⃗ : ∀ (m : ℕ) → m + zero ≡ m   -- QUESTION \^r produces ⃗ ? SOLVED!
+-identity⃗ zero =
  begin                          -- base case is best case
    zero + zero
  ≡⟨ refl ⟩                       -- the book didn't say anything about C-l
    zero
   ∎
+-identity⃗ (suc m) =            -- so basically we're trying to get to 
  begin                          -- suc ::lhs of initial proposion::
    (suc m) + zero               -- so that we can end up with   
  ≡⟨ refl ⟩                             -- suc ::rhs of initial proposition::
    suc (m + zero)   
  ≡⟨ cong suc (+-identity⃗ m) ⟩        -- magic spell: C-c C-z, C-c C-SPC
    suc m
  ∎ 
-- C-c C-d
-- ≡⟨⟩           <=>          ≡⟨ refl ⟩



-- LEMMA: m + suc n ≡ suc (m + n) by analogy to suc m + n ≡ suc (m + n)

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc(m + n)
+-suc zero n = 
  begin
    zero + suc n 
  ≡⟨⟩                 -- because base case of +: zero + n ≡ n
    suc n    
  ≡⟨⟩                 -- because rev. base case of +: zero + n ≡ n
    suc (zero + n)
  ∎
+-suc (suc m) n =
  begin
    (suc m) + (suc n)
  ≡⟨⟩                 -- inductive case of +: (suc m) + n = suc (m + n)
    suc (m + (suc n))
  ≡⟨ cong suc (+-suc m n) ⟩ 
    suc (suc (m + n) )
  ≡⟨⟩                 -- reverse inductive case of +: (suc m) + n = suc (m + n)
    suc ((suc m) + n)
  ∎



-- PROPOSITION

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
    m + zero
  ≡⟨ +-identity⃗ m ⟩ -- from LEMMA: plus has left identity zero
    m
  ≡⟨⟩ -- from reverse base case 
    zero + m
  ∎
+-comm m (suc n) =
    m + (suc n)                -- starts with the lhs of +-comm
  ≡⟨ +-suc m n ⟩                -- from LEMMA 
    suc (m + n)                  -- now we have the comm inductive case on the inside
                                -- and a suc on the outside, so I can apply cong
  ≡⟨ cong suc (+-comm m n)  ⟩   -- from cong-ing the inductive case
    suc (n + m)                -- almost there
  ≡⟨⟩                           -- from reverse of base case of naturals
    (suc n) + m                 -- ends with the rhs of +-comm
  ∎



-- CCOORROOLLAARRYY: rearranging

+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ +-assoc m n (p + q) ⟩ -- from associativity
    m + (n + (p + q))
  ≡⟨ cong (m +_) (sym (+-assoc n p q)) ⟩ -- from cong on reverse associativity with preceding m +
                                  -- XXX not really sure how to read (m +_): apply m with arg +_?
                                  -- XXX what is this sym stuff?
                                  -- sym X represents what i keep refering to as "reverse X"
    m + ((n + p) + q)
  ≡⟨ sym (+-assoc m (n + p) q) ⟩   -- from reverse associativity
    (m + (n + p)) + q
  ≡⟨⟩
    m + (n + p) + q
  ∎

-- EXERCISE finite-+-assoc



-- ASSOCIATIVITY WITH REWRITE

-- What is rewrite?
-- When is rewrite used?

--+-assoc' : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
--+-assoc' zero n p = refl
--+-assoc' (suc m) n p rewrite +-assoc' m n p = refl             -- O.O
--
--+-identity' : ∀ (n : ℕ) → n + zero ≡ n
--+-identity' zero = refl
--+-identity' (suc n) rewrite +-identity' n = refl
--
--+-suc' : ∀ (m n : ℕ) → m + suc(n) ≡ suc(m + n)
--+-suc' zero n = refl
--+-suc' (suc m) n rewrite +-suc' m n = refl
--
--+-comm' : ∀ (m n : ℕ) → m + n ≡ n + m
--+-comm' m zero rewrite +-identity' m = refl
--+-comm' m (suc n) rewrite +-suc' m n | +-comm' m n = refl




-- BUILDING PROOFS INTERACTIVELY

+-assoc' : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc' zero n p = refl                               -- what is the goal precisely?
+-assoc' (suc m) n p rewrite +-assoc' m n p = refl     -- I feel cheated --I had to type rewrite by hand?


-- now you're thinking with ---portals--- holes?

+-identity' : ∀ (n : ℕ) → n + zero ≡ n
+-identity' zero = refl
+-identity' (suc n) rewrite +-identity' n = refl

+-suc' : ∀ (m n : ℕ) → m + suc(n) ≡ suc(m + n)
+-suc' zero n = refl
+-suc' (suc m) n rewrite +-suc' m n = refl 

+-comm' : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm' m zero rewrite +-identity' m = refl
+-comm' m (suc n) rewrite +-suc' m n | +-comm' m n = refl




-- EXERCISE +-swap

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
-- +-swap m n p =
--   begin
--     m + (n + p)
--   ≡⟨ sym (+-assoc m n p) ⟩
--     (m + n) + p
--   ≡⟨ cong (_+ p) (+-comm m n) ⟩
--     (n + m) + p
--   ≡⟨ +-assoc n m p ⟩
--     n + (m + p)
--   ∎

-- +-swap m n p rewrite +-assoc m n p | (cong (_+ p) (+-comm m n)) | +-assoc n m p = {!!} -- ?????????

+-swap m n p rewrite (sym (+-assoc m n p)) | +-comm m n | +-assoc n m p = refl
--+-swap m n p rewrite (sym (+-assoc m n p)) = {!!}

-- every time I think agda will do something smart for me, it turns out I need to do it by hand...




-- EXERCISE *-distrib-+

--*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p

*-distrib-+' : ∀ (m n p : ℕ) → p * (m + n) ≡ p * n + p * m
*-distrib-+' m n zero = refl
*-distrib-+' m n (suc p) rewrite *-distrib-+' m n p                                 -- m + n + (p * n + p * m)
                               | cong ((m + n) +_) (+-comm (p * n) (p * m))         -- m + n + (p * m + p * n)
                               | sym (+-assoc (m + n) (p * m) (p * n))              -- ((m + n) + (p * m)) + p * n
                               | cong (_+ (p * n)) (+-assoc m n (p * m))            -- (m + (n + (p * m))) + p * n
                               | cong (_+ (p * n)) (cong (m +_) (+-comm n (p * m))) -- (m + ((p * m) + n)) + p * n
                               | cong (_+ (p * n)) (sym (+-assoc m (p * m) n))      -- ((m + (p * m)) + n) + (p * n)
                               | +-assoc (m + (p * m)) n (p * n)                    -- (m + (p * m)) + (n + (p * n))
                                                                                    -- ((suc p) * m) + ((suc p) * n)
                               | +-comm ((suc p) * m) ((suc p) * n)                 -- (suc p) * n + (suc p) * m
                               = refl                                            
--                             =
--                             begin
--                              p * (m + n) 
--                             ≡⟨ .. ⟩
--                               m + n + (p * n + p * m)
--                             ≡⟨ ... ⟩
--                               m + n + (p * m + p * n)
--                             ≡⟨ sym (+-assoc (m + n) (p * m) (p * n))  ⟩
--                               ((m + n) + (p * m)) + p * n
--                             ≡⟨ cong (_+ (p * n)) (+-assoc m n (p * m)) ⟩
--                               (m + (n + (p * m))) + p * n
--                             ≡⟨ cong (_+ (p * n)) (cong (m +_) (+-comm n (p * m))) ⟩
--                               (m + ((p * m) + n)) + p * n
--                             ≡⟨ cong (_+ (p * n)) (sym (+-assoc m (p * m) n)) ⟩
--                               ((m + (p * m)) + n) + (p * n)
--                             ≡⟨ +-assoc (m + (p * m)) n (p * n) ⟩
--                               (m + (p * m)) + (n + (p * n))
--                             ≡⟨⟩
--                               ((suc p) * m) + ((suc p) * n)
--                             ≡⟨ +-comm ((suc p) * m) ((suc p) * n) ⟩
--                               (suc p) * n + (suc p) * m
--                            ∎

--*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
--*-comm zero m =
--  begin
--    zero * m
--  ≡⟨⟩
--    zero * (zero + m)
--  ≡⟨ cong (zero *_) (+-comm zero m) ⟩
--    zero * (m + zero)
  -- *-distrib-+' : ∀ (m n p : ℕ) → p * (m + n) ≡ p * n + p * m
--  ≡⟨ *-distrib-+' m zero zero ⟩
--    (zero * zero) + (m * zero)  
  --≡⟨ +-comm (zero * zero) (zero * m) ⟩
  --  (zem) + (zero * zero)
--  ≡⟨⟩
--    m + zero * zero
--  ≡⟨⟩
--    m * zero
--  ∎

-- *-assoc' : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
-- *-assoc' m n zero = refl

--*-assoc : ∀ (m n p : ℕ) → m * (n * p) ≡ (m * n) * p
--*-assoc zero n p = refl                              
--*-assoc (suc m) n p  =
--  begin
--    (suc m) * (n * p)
--  ≡⟨⟩
--    (n * p) + (m * (n * p))
--  ≡⟨ cong ((n * p) +_) (*-assoc m n p)  ⟩
--    (n * p) + ((m * n) * p)
--  ≡⟨ +-comm (n * p) ((m * n) * p) ⟩
--    ((m * n) * p) + (n * p)
--  --≡⟨  ⟩
--         
--  ≡⟨⟩
--    ((suc m) * n) * p
--  ∎

-- install "which keys" from GH
-- goodgmenet should be a word



------------------------------------------------------------------------------------
------------------------------------------------------------------------------------
---                 ----------------------------------------------------------------
--- A NEW BEGINNING ----------------------------------------------------------------
---                 ----------------------------------------------------------------
------------------------------------------------------------------------------------
------------------------------------------------------------------------------------

*-identity⃗ : ∀ (m : ℕ) → m * zero ≡ zero
*-identity⃗ zero = refl
*-identity⃗ (suc m) =
  begin
    (suc m) * zero
  ≡⟨⟩
    zero + (m * zero)
  ≡⟨ cong (zero +_) (*-identity⃗ m) ⟩
    zero + zero
  ≡⟨⟩
    zero
  ∎

*-suc : ∀ (m n : ℕ) → m * (suc n) ≡ m + (m * n)
*-suc zero n =
  begin 
    zero * (suc n)
  ≡⟨⟩
    zero
  ≡⟨⟩
    zero + zero
  ≡⟨⟩
    zero + (zero * n)
  ∎
*-suc (suc m) n =
  begin
    (suc m) * (suc n)
  ≡⟨⟩
    (suc n) + (m * (suc n))
  ≡⟨ cong ((suc n) +_) (*-suc m n) ⟩
    (suc n) + (m + (m * n))
  ≡⟨ sym (+-assoc (suc n) m (m * n)) ⟩
    ((suc n) + m) + (m * n)
  ≡⟨⟩
    suc (n + m) + (m * n)
  ≡⟨ cong (_+ (m * n)) (cong (suc) (+-comm n m)) ⟩
    suc(m + n) + (m * n)
  ≡⟨⟩
    ((suc m) + n) + (m * n)
  ≡⟨ +-assoc (suc m) n (m * n) ⟩
    (suc m) + (n + (m * n))
  ≡⟨⟩
    (suc m) + ((suc m) * n)
  ∎

*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ m n zero =
  begin 
    (m + n) * zero
  ≡⟨ *-identity⃗ (m + n) ⟩
    zero
  ≡⟨⟩
    zero + zero
  ≡⟨ cong (zero +_) (sym (*-identity⃗ n)) ⟩
    zero + n * zero
  ≡⟨ cong (_+ (n * zero)) (sym (*-identity⃗ m))  ⟩
    m * zero + n * zero    
  ∎
*-distrib-+ m n (suc p) =
  begin
    (m + n) * (suc p)    
  ≡⟨ *-suc (m + n) p ⟩
    (m + n) + (m + n) * p
  ≡⟨ cong ((m + n) +_) (*-distrib-+ m n p) ⟩
    (m + n) + (m * p + n * p)
  ≡⟨ +-assoc m n (m * p + n * p)  ⟩
    m + (n + (m * p + n * p))
  ≡⟨ cong (m +_) (cong (n +_) (+-comm (m * p) (n * p)))  ⟩
    m + (n + (n * p + m * p))
  ≡⟨ cong (m +_) (sym (+-assoc n (n * p) (m * p)))  ⟩
    m + ((n + (n * p)) + m * p)
  ≡⟨ cong (m +_) (+-comm (n + (n * p)) (m * p))  ⟩
    m + ((m * p) + (n + (n * p)))
  ≡⟨ sym (+-assoc m (m * p) (n + (n * p))) ⟩
    (m + (m * p)) + (n + (n * p))
  ≡⟨ cong ((m + (m * p)) +_) (sym (*-suc n p)) ⟩
    (m + (m * p)) + (n * (suc p))
  ≡⟨ cong (_+ (n * (suc p))) (sym (*-suc m p)) ⟩
    (m * (suc p)) + (n * (suc p))
  ∎

-- recurse over m
*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p =
  begin
    ((suc m) * n) * p
  ≡⟨⟩
    (n + (m * n)) * p
  ≡⟨ *-distrib-+ n (m * n) p ⟩
    (n * p) + ((m * n) * p)
  ≡⟨ cong ((n * p) +_) (*-assoc m n p) ⟩
    (n * p) + (m * (n * p))               
  ≡⟨⟩
    (suc m) * (n * p)
  ∎
  
*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm zero n =
  begin
    zero * n
  ≡⟨⟩
    zero    
  ≡⟨ sym (*-identity⃗ n) ⟩
    n * zero
  ∎
*-comm (suc m) n =
  begin
    (suc m) * n
  ≡⟨⟩
    n + (m * n)
  ≡⟨ cong (n +_) (*-comm m n) ⟩
    n + (n * m)  
  ≡⟨ sym (*-suc n m) ⟩
    n * (suc m)
  ∎
  
-- zero may be a left-annihilator for monus
0∸n≡0 : ∀ (n : ℕ) → zero ∸ n ≡ zero
0∸n≡0 zero = refl
0∸n≡0 (suc n) = refl
--                                                           QUESTION: Why doesn't 0∸n≡0 n = refl work?


∸-+-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc zero n p = 
  begin
    (zero ∸ n) ∸ p
  ≡⟨ cong (_∸ p) (0∸n≡0 n) ⟩
    zero ∸ p
  ≡⟨ 0∸n≡0 p ⟩
    zero
  ≡⟨ sym (0∸n≡0 (n + p))  ⟩
    zero ∸ (n + p)
  ∎
∸-+-assoc (suc m) (suc n) p = -- we have to recurse over two, because that's how the definition of ∸ works
  begin
    (suc m) ∸ (suc n) ∸ p
  ≡⟨⟩
    m ∸ n ∸ p
  ≡⟨ ∸-+-assoc m n p ⟩
    m ∸ (n + p)
  ∎
∸-+-assoc m zero p = refl                                    -- QUESTION why gray highlight?




-- had to go back to the top and import _^_ at this point!

-- this turned out to be unnecessary when I picked the "right" variable to split on
--^-zero : ∀ (m : ℕ) → zero ^ m ≡ zero
--^-zero zero = refl 

^-distrib-+ : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)   
--^-distrib-+ zero n p rewrite ^-zero (n + p) =  
--  begin
--    zero * zero
--  ≡⟨ cong (_* zero) (sym (^-zero n)) ⟩
--    (zero ^ n) * zero
--  ≡⟨ cong ((zero ^ n) *_) (sym (^-zero p)) ⟩
--    (zero ^ n) * (zero ^ p)
--  ∎

-- QUESTION: why didn't this work
-- ^-distrib-+ zero n p rewrite ^-zero (n + p) =                        --          ≡ zero
--                           -- trivially                               --          ≡ zero * zero
--                            | cong (_* zero) (sym (^-zero n))         --          ≡ (zero ^ n) * zero
--                            | cong ((zero ^ n) *_) (sym (^-zero p))   --          ≡ (zero ^ n) * (zero ^ p)
--                            = refl                                    -- end goal:  (zero ^ n) * (zero ^ p)

*-identity-1 : ∀ (m : ℕ) → (suc zero) * m ≡ m
*-identity-1 zero = refl
*-identity-1 (suc m) rewrite *-identity-1 m = refl

^-distrib-+ m (suc n) p =                                               -- starting:   m ^ ((suc n) + p)
                                                                        -- end goal:   (m ^ (suc n)) * (m ^ p)
  begin
    m ^ ((suc n) + p)
  ≡⟨⟩
    m ^ (suc (n + p))
  ≡⟨⟩
    m * m ^ (n + p)
  ≡⟨ cong (m *_) (^-distrib-+ m n p) ⟩
    m * (m ^ n * m ^ p)
  ≡⟨ sym (*-assoc m (m ^ n) (m ^ p)) ⟩
    m * m ^ n * m ^ p
  ≡⟨⟩
    (m ^ (suc n) * (m ^ p))
  ∎
^-distrib-+ m zero p =
  begin
    m ^ (zero + p)
  ≡⟨⟩
    m ^ p
  ≡⟨ sym (*-identity-1 (m ^ p)) ⟩
    (suc zero) * m ^ p 
  ≡⟨⟩
    m ^ zero * m ^ p
  ∎

^-distrib-* : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^-distrib-* m n (suc p) rewrite ^-distrib-* m n p =        -- (m * n) * ((m ^ p) * (n ^ p))
  begin
    (m * n) * ((m ^ p) * (n ^ p))
  ≡⟨ *-assoc m n ((m ^ p) * (n ^ p)) ⟩ 
    m * (n * ((m ^ p) * (n ^ p)))
  ≡⟨ cong (m *_) (cong (n *_) (*-comm (m ^ p) (n ^ p))) ⟩
    m * (n * ((n ^ p) * (m ^ p)))
  ≡⟨ cong (m *_) (sym (*-assoc n (n ^ p) (m ^ p))) ⟩
    m * ((n * n ^ p) * m ^ p)
  ≡⟨ cong (m *_) (*-comm (n * n ^ p) (m ^ p)) ⟩
    m * (m ^ p * (n * n ^ p))
  ≡⟨ sym (*-assoc m (m ^ p) (n * (n ^ p))) ⟩
    (m * m ^ p) * (n * (n ^ p))
  ≡⟨⟩
    (m ^ (suc p)) * (n ^ (suc p))
  ∎
^-distrib-* m n zero = refl
                                                                         
^*-distrib-^ : ∀ (m n p : ℕ) → m ^ (n * p) ≡ (m ^ n) ^ p
^*-distrib-^ m n zero =
  begin
    m ^ (n * zero)
  ≡⟨ cong (m ^_) (*-comm n zero) ⟩
    m ^ (zero * n)
  ≡⟨⟩
    m ^ zero
  ≡⟨⟩
    (m ^ n) ^ zero
  ∎
^*-distrib-^ m n (suc p) =
  begin
    m ^ (n * (suc p))
  ≡⟨ cong (m ^_) (*-comm n (suc p)) ⟩
    m ^ ((suc p) * n)
  ≡⟨⟩
    m ^ (n + p * n)
  ≡⟨ ^-distrib-+ m n (p * n) ⟩
    m ^ n * m ^ (p * n)
  ≡⟨ cong ((m ^ n) *_) (cong (m ^_) (*-comm p n)) ⟩
    m ^ n * m ^ (n * p)
  ≡⟨ cong ((m ^ n) *_) ( ^*-distrib-^ m n p) ⟩
    m ^ n * ((m ^ n) ^ p)
  ≡⟨⟩
    (m ^ n) ^ (suc p)
  ∎

-- Copying over Bin functions
data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin
  
inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (p O) = p I
inc (p I) = (inc p) O

from : Bin → ℕ
from ⟨⟩ = 0         -- QUESTION
from (p O) = 2 * (from p)
from (p I) = 2 * (from p) + 1

to : ℕ → Bin
to 0 = ⟨⟩ O
to (suc n)  = inc (to n)
--

--from (inc b) ≡ suc (from b)
--to (from b) ≡ b
--from (to n) ≡ n

from-inc≡suc-from : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
from-inc≡suc-from ⟨⟩ = refl
from-inc≡suc-from (b O) =
  begin
    from (inc (b O))
  ≡⟨⟩
    from (b I)
  ≡⟨⟩
    2 * (from b) + 1
  ≡⟨ +-comm (2 * (from b)) 1 ⟩
   1 + (2 * (from b))
  ≡⟨⟩
    suc (2 * (from b))
  ≡⟨⟩
    suc (from (b O))
  ∎
from-inc≡suc-from (b I) =
  begin
    from (inc (b I))
  ≡⟨⟩
    from ((inc b) O)
  ≡⟨⟩
    2 * (from (inc b))
  ≡⟨ cong (2 *_) (from-inc≡suc-from b) ⟩
    2 * (suc (from b))
  ≡⟨ *-comm 2 (suc (from b)) ⟩
    (suc (from b)) * 2
  ≡⟨⟩
    2 + ((from b) * 2)
  ≡⟨⟩
    suc (1 + ((from b) * 2))
  ≡⟨ cong (1 +_) (+-comm 1 ((from b) * 2)) ⟩
    suc ((from b) * 2 + 1)
  ≡⟨ cong (1 +_) (cong (_+ 1) (*-comm (from b) 2)) ⟩
    suc (2 * (from b) + 1)
  ≡⟨⟩
    suc (from (b I))
  ∎

--to-from : ∀ (b : Bin) → to (from b) ≡ b
--to-from ⟨⟩ =
--  begin
--    to (from ⟨⟩)
--  ≡⟨⟩
--    to 0
--  ≡⟨⟩
--    ⟨⟩ O -- can't get from here
--  ≡⟨⟩
--    ⟨⟩   -- to here
--  ∎
-- to-from (b O) = {!!}
-- to-from (b I) = {!!}

-- counter-example: to (from ⟨⟩) ≡/≡ ⟨⟩ because ⟨⟩ O ≡/≡ ⟨⟩

from-inc : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
from-inc ⟨⟩ = refl
from-inc (p O) =
  begin
    from (inc (p O))
  ≡⟨⟩
    from (p I)
  ≡⟨⟩
    2 * (from p) + 1
  ≡⟨ +-comm (2 * (from p)) 1 ⟩
    1 + (2 * (from p))
  ≡⟨⟩
    suc (2 * (from p))
  ≡⟨⟩
    suc (from (p O))
  ∎
from-inc (p I) =
  begin
    from (inc (p I))
  ≡⟨⟩
    from ((inc p) O)
  ≡⟨⟩
    2 * (from (inc p))
  ≡⟨ cong (2 *_) (from-inc p) ⟩
    2 * (suc (from p))
  ≡⟨ *-comm 2 (suc (from p)) ⟩
    (suc (from p)) * 2
  ≡⟨⟩
    2 + (from p) * 2
  ≡⟨ cong (2 +_) (*-comm (from p) 2) ⟩
    2 + 2 * (from p)
  ≡⟨⟩
    suc (1 + (2 * (from p)))
  ≡⟨ cong suc (+-comm 1 (2 * (from p))) ⟩
    suc ((2 * (from p)) + 1)
  ≡⟨⟩
    suc (from (p I))
  ∎

from-to : ∀ (n : ℕ) → from (to n) ≡ n
from-to zero = refl
from-to (suc n) =
  begin
    from (to (suc n))
  ≡⟨⟩
    from (inc (to n))
  ≡⟨ from-inc (to n) ⟩
    suc (from (to n))
  ≡⟨ cong suc (from-to n) ⟩
    suc n
  ∎
