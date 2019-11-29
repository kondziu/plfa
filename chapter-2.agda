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
  ≡⟨⟩                -- because inductive case: (suc m) + n = suc (m + n)
    suc (m + n) + p
  ≡⟨⟩                -- likewise
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

+-identity⃗ : ∀ (m : ℕ) → m + zero ≡ m   -- QUESTION \^r produces ⃗ ?
+-identity⃗ zero =
  begin                          -- base case is best case
    zero + zero
  ≡⟨⟩
    zero
   ∎
+-identity⃗ (suc m) =            -- so basically we're trying to get to 
  begin                          -- suc ::lhs of initial proposion::
    (suc m) + zero               -- so that we can end up with   
  ≡⟨⟩                             -- suc ::rhs of initial proposition::
    suc (m + zero)
  ≡⟨ {!cong suc ?!} ⟩   
  --≡⟨ cong suc (+-identity⃗ m) ⟩
    suc m
  ∎

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
