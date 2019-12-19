import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)

data _≤_ : ℕ → ℕ → Set where

  z≤n : ∀ {n : ℕ}               -- this is a constructor for the base case
      --------                   -- this is just a comment, no magic here
   → zero ≤ n                   -- this is a type

  s≤s : ∀ {m n : ℕ}             -- this is a constructor for the inductive case
    → m ≤ n                     -- this is a type                                -- if this proposition holds
       -------------             -- this is just a comment, no magic here
    → suc m ≤ suc n             -- this is a type                                -- then this proposition holds


-- these constructors produce evidence for the propositions

-- IMPLICIT ARGUMENTS

--    +-comm : ∀ (m n : ℕ)  -- explicit arguments
--
--    vs 
--
--    z≤n : ∀ {n : ℕ}       -- implicit argument

-- we use these differently:
--    comm x y
-- vs z≤n
-- vs z≤n {x} {y}
-- vs z≤n {n = x}

-- PRECEDENCE

infix 4 _≤_

-- DECIDABILITY

-- INVERSION

inv-s≤s : ∀ {m n : ℕ}
  → suc m ≤ suc n
     -------------
  → m ≤ n

inv-s≤s (s≤s m≤n) = m≤n        -- m≤n is a variable name
                               -- QUESTION: I don't understand what (s≤s m≤n) means?

inv-z≤n : ∀ {m : ℕ}
  → m ≤ zero
     --------
  → m ≡ zero

inv-z≤n z≤n = refl             -- QUESTION: why are we passing a constructor to a proposition here?

-- PROPERTIES OF ORDERNG RELATIONS

-- Reflexive:      for all n,                                    n ≤ n
-- Transitive:     for all m, n, p  if m ≤ n and n ≤ p then      m ≤ p
-- Anti-symmetric: for all m, n     if m ≤ n and n ≤ m then      m ≡ n
-- Total:          for all m, n                                  m ≤ n or n ≤ m

-- Preorder:       reflexive and transitive
-- Partial order:  reflexive and transitive and anti-symmetric
-- Total order:    reflexive and transitive and anti-symmetric and total

-- EXERCISE orderings

-- A preorder that is not a partial order                        TODO
-- A partial order that is not a total order                     TODO

-- REFLEXIVITY

≤-refl : ∀ {n : ℕ}
     -----
  → n ≤ n

≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl     -- QUESTION: I still don't get it
                                -- We are passing a constructor to another constructor?
                                -- This somehow signifies that we get there by induction...
                                -- Ok. So "≤-refl {n} gives us a proof of n ≤ n"
                                --        "applying s≤s to [the proof that n ≤ n] yields a proof of suc n ≤ suc n"



-- TRANSITIVITY
                                
