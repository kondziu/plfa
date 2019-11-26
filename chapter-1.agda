data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

seven : ℕ
seven = suc (suc (suc (suc (suc (suc (suc zero))))))

{-# BUILTIN NATURAL ℕ #-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎) -- QUESTION what is Eq.≡-Reasoning
                                              -- QUESTION what is ≡⟨⟩ 

_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

-- 0 + n ≡ n
-- (1+m) + n ≡ 1 + (m + n)

_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
    ≡⟨⟩  -- is shorthand for
      (suc (suc zero)) + (suc (suc (suc zero)))
    ≡⟨⟩  -- inductive case
      suc ((suc zero) + (suc (suc (suc zero))))
    ≡⟨⟩  -- inductive case
      suc (suc (zero + (suc (suc (suc zero)))))
    ≡⟨⟩  -- base case
      suc (suc (suc (suc (suc zero))))
    ≡⟨⟩  -- is longhand for
      5
    ∎

_ =
  begin
    2 + 3
    ≡⟨⟩
      (suc 1 + 3)
    ≡⟨⟩
      suc (suc (0 + 3))
    ≡⟨⟩
      suc (suc 3)
    ≡⟨⟩
      5
    ∎

-- Agda, why am I writing these derivations?
-- Aren't you the automatic proof thingy?
-- Shouldn't you be writing the derivations?

_ : 2 + 3 ≡ 5
_ = refl

-- Oh, ok. Carry on.

-- Exercise +- example (practice)

_ =
  begin
    3 + 4
    ≡⟨⟩
    (suc (suc (suc zero)) + suc (suc (suc (suc zero))))
    ≡⟨⟩
    suc ((suc (suc zero)) + suc (suc (suc (suc zero))))
    ≡⟨⟩
    suc (suc ((suc zero) + suc (suc (suc (suc zero)))))
    ≡⟨⟩
    suc (suc (suc (zero + suc (suc (suc (suc zero))))))
    ≡⟨⟩
    suc (suc (suc (suc (suc (suc (suc zero))))))
    ≡⟨⟩
    7
  ∎

_*_ : ℕ → ℕ → ℕ
zero * n = zero
(suc m) * n = n + (m * n)

-- 0 * n ≡ 0
-- (1 + m) * n ≡ n + (m * n)

_ =
  begin
    2 * 3
  ≡⟨⟩        --inductive case
    3 + (1 * 3)
  ≡⟨⟩        -- inductive case
    3 + (3 + (0 * 3))
  ≡⟨⟩        -- base case
    3 + (3 + 0)
  ≡⟨⟩        -- simplify
    6
  ∎

-- Example *-example

_ =
  begin
    3 * 4
  ≡⟨⟩
    4 + (2 * 4)
  ≡⟨⟩
    4 + (4 + (1 * 4))
  ≡⟨⟩
    4 + (4 + (4 + (0 * 4)))
  ≡⟨⟩
    4 + (4 + (4 + 0))
  ≡⟨⟩
    4 + (4 + 4)
  ≡⟨⟩
    4 + 8
  ≡⟨⟩
    12
  ∎

-- Exercise _^_

_^_ : ℕ → ℕ → ℕ
m ^ zero = (suc zero)
-- m ^ (suc zero) = m
m ^ (suc n) = m * (m ^ n)
  
_ =
  begin
    3 ^ 4
  ≡⟨⟩
    3 * (3 ^ 3)
  ≡⟨⟩
    3 * (3 * (3 ^ 2))
  ≡⟨⟩
    3 * (3 * (3 * (3 ^ 1)))
  ≡⟨⟩
    3 * (3 * (3 * (3 * (3 ^ 0))))
  ≡⟨⟩
    3 * (3 * (3 * (3 * 1)))
  ≡⟨⟩
    3 * (3 * (3 * 3))
  ≡⟨⟩
    3 * (3 * 9)
  ≡⟨⟩
    3 * 27
  ≡⟨⟩
    81
  ∎

_∸_ : ℕ → ℕ → ℕ
m ∸ zero = m
zero ∸ suc n = zero
suc m ∸ suc n = m ∸ n

_ =
  begin
    3 ∸ 2
  ≡⟨⟩
    2 ∸ 1
  ≡⟨⟩
    1 ∸ 0
  ≡⟨⟩
    1
  ∎

_ =
  begin
    2 ∸ 3
  ≡⟨⟩
    1 ∸ 2
  ≡⟨⟩
    0 ∸ 1
  ≡⟨⟩
    0
  ∎

-- Exercise ∸-examples

_ =
  begin
    5 ∸ 3
  ≡⟨⟩
    4 ∸ 2
  ≡⟨⟩
    3 ∸ 1
  ≡⟨⟩
    2 ∸ 0
  ≡⟨⟩
    2
  ∎

_ =
  begin
    3 ∸ 5
  ≡⟨⟩
    2 ∸ 4
  ≡⟨⟩
    1 ∸ 3
  ≡⟨⟩
    0 ∸ 2
  ≡⟨⟩
    0
  ∎

infixl 6  _+_  _∸_
infixl 7  _*_

-- remember: currying

--_+_ : ℕ → ℕ → ℕ
--zero + n = n
--suc m + n = suc (m + n)

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

-- ⟨⟩ I O I I ≡ ⟨⟩ O I O I I

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (p O) = p I
inc (p I) = (inc p) O

_ =
  begin
    inc (⟨⟩ O)
  ≡⟨⟩
    ⟨⟩ I
  ∎

_ =
  begin
    inc (⟨⟩ I)
  ≡⟨⟩
    ⟨⟩ I O
  ∎

_ =
  begin
    inc (⟨⟩ I O)
  ≡⟨⟩
    ⟨⟩ I I
  ∎

_ =
  begin
    inc (⟨⟩ I I)
  ≡⟨⟩
    (inc (⟨⟩ I)) O
  ≡⟨⟩
    ⟨⟩ I O O
  ∎

--to : ℕ → Bin
--to 0 = ⟨⟩ O
--to 1 = ⟨⟩ I
--to (2 * m + n) = ⟨⟩ I (to n)

from : Bin → ℕ
from ⟨⟩ = 0         -- QUESTION
from (p O) = 2 * (from p)
from (p I) = 2 * (from p) + 1

_ =
  begin
    from (⟨⟩ O)
  ≡⟨⟩
    0
  ∎

_ =
  begin
    from (⟨⟩ I)
  ≡⟨⟩
    1
  ∎

_ =
  begin
    from (⟨⟩ I O)
  ≡⟨⟩
    2 * from (⟨⟩ I)
  ≡⟨⟩
    2 * 1
  ≡⟨⟩
    2
  ∎

_ =
  begin
    from  (⟨⟩ I I)
  ≡⟨⟩
    2 * (from (⟨⟩ I)) + 1
  ≡⟨⟩
    2 * 1 + 1
  ≡⟨⟩
    2 + 1
  ≡⟨⟩
    3
  ∎

_ =
  begin
    from (⟨⟩ I O O)
  ≡⟨⟩
    2 * (from (⟨⟩ I O))
  ≡⟨⟩
    2 * (2 * from (⟨⟩ I))
  ≡⟨⟩
    2 * (2 * 1)
  ≡⟨⟩
    2 * 2
  ≡⟨⟩
    4
  ∎

to : ℕ → Bin
to 0 = ⟨⟩ O
to (suc n)  = inc (to n)
--to (2 * p) = (to p) O     -- QUESTION :<
--to (2 * p + 1) = (to p) I


_ =
  begin
    to 0
  ≡⟨⟩
    ⟨⟩ O
  ∎

_ =
  begin
    to 1
  ≡⟨⟩
    ⟨⟩ I
  ∎

_ =
  begin
    to 2
  ≡⟨⟩
    (to 1) O
  ≡⟨⟩
    ⟨⟩ I O
  ∎

_ =
  begin
    to 3
  ≡⟨⟩
    (to 1) I
  ≡⟨⟩
    ⟨⟩ I I
  ∎

_ =
  begin
    to 4
  ≡⟨⟩
    (to 2) O
  ≡⟨⟩
    (to 1) O O
  ≡⟨⟩
    ⟨⟩ I O O
  ∎    

-- import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)



