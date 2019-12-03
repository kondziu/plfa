-- Induction makes you feel guilty for getting something out of
-- nothing … but it is one of the greatest ideas of civilization.
--                                                - Herbert Wilf

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)

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

*-assoc : ∀ (m n p : ℕ) → m * (n * p) ≡ (m * n) * p
*-assoc zero n p = refl                              
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
--

-- install "which keys" from GH
