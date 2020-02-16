import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)

data _≤_ : ℕ → ℕ → Set where  -- this is important:
                                 -- R: "Read 'Set' as 'Proposition'"
                                 -- R: "The meaning of this construct is described by the
                                 --     constructors"

                                 -- the two constructors below describe how this
                                 -- data type operates, this statement ties them
                                 -- together into a "data type?"

  z≤n : ∀ {n : ℕ}               -- this is a constructor for the base case
      --------                   -- this is just a comment, no magic here
   → zero ≤ n                   -- this is a type
                                 -- this means roughly: for all natural numbers,
                                 -- zero is less or equal to any natural number

  s≤s : ∀ {m n : ℕ}             -- this is a constructor for the inductive case
    → m ≤ n                     -- this is a type                                
       -------------             -- this is just a comment, no magic here
    → suc m ≤ suc n             -- this is a type
                                 -- this means roughly:
                                 --   if you provide to me evidence
                                 --   that m ≤ n
                                 --   then I will produce for you the evidence
                                 --   that suc m ≤ suc n

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

-- the implicit arguments can be used implicitly or explicitly

--_ : 2 ≤ 4
--_ = s≤s (s≤s z≤n)
--2≤4 <= 1≤3 <= 0≤2 <= (base case 2)
--_ = s≤s {1} {3} (s≤s {0} {2} (z≤n {2}))
--_ = s≤s {m = 1} {n = 3} (s≤s {m = 0} {n = 2} (z≤n {n = 2}))

-- precedence

infix 4 _≤_

-- decidability

-- inversion

inv-s≤s : ∀ {m n : ℕ}
  → suc m ≤ suc n             
     -------------
  → m ≤ n

inv-s≤s (s≤s m≤n) = m≤n        -- m≤n is a variable name
                               -- question: i don't understand what (s≤s m≤n) means?
                               -- i think it means the following:
                               -- 1. let's say i have some proposition, which i don't know,
                               --    but i'll call it m≤n
                               -- 2. if i use this proposition to show that s≤s i'll get some
                               --    evidence x
                               -- 3. if i then use this evidence x as the assumption in inv-s≤s,
                               --    what i get in return is some evidence that will be the same
                               --    as the initial proposition m≤n

inv-z≤n : ∀ {m : ℕ}
  → m ≤ zero
     --------
  → m ≡ zero

inv-z≤n z≤n = refl             -- question: why are we passing a constructor to a proposition here?
                               -- a guess:
                               -- 1. z≤n doesn't require any evidence, just a natural number.
                               --    we can assume that some natural number k exists. this k is passed
                               --    to z≤n implicitly, so it doesn't actually need to be named.
                               -- 2. the result of z≤n is evidence that (zero ≤ k).
                               -- 3. we use this evidence in inv-z≤n. our k number is gets plugged
                               --    in implicitly as m, i think. so what we're saying here is
                               --    that we know (zero ≤ k) and (k ≤ zero).
                               -- 4. i guess from this somehow we arrive at (k ≡ zero)...?

-- properties of orderng relations

-- reflexive:      for all n,                                    n ≤ n
-- transitive:     for all m, n, p  if m ≤ n and n ≤ p then      m ≤ p
-- anti-symmetric: for all m, n     if m ≤ n and n ≤ m then      m ≡ n
-- total:          for all m, n                                  m ≤ n or n ≤ m

-- preorder:       reflexive and transitive  (aka quasiorder)
-- partial order:  reflexive and transitive and anti-symmetric
-- total order:    reflexive and transitive and anti-symmetric and total

-- exercise orderings

-- a preorder that is not a partial order                        has-the-same-sign-as
-- a partial order that is not a total order                     ≤ on naturals + null

-- reflexivity

--≤-refl : ∀ {n : ℕ}
--     -----
--  → n ≤ n


--≤-refl {zero} = z≤n
--≤-refl {suc n} = s≤s ≤-refl   -- question: i still don't get it
                                -- we are passing a constructor to another constructor?
                                -- this somehow signifies that we get there by induction...
                                -- ok. so "≤-refl {n} gives us a proof of n ≤ n"
                                --        "applying s≤s to [the proof that n ≤ n]
                                --         yields a proof of suc n ≤ suc n"

                                -- ok. after i mulled it over and talked with colette a
                                -- bunch i figured it out for myself.

                                -- the constructor z≤n only takes the implicit parameter n.
                                -- when it is applied it returns evidence (a sort of impromptu
                                -- proposition?) that.


-- try to prove it by myself
≤-refl : ∀ {n : ℕ} → n ≤ n
≤-refl {zero} = z≤n             -- I used a hole. It showed me that if I plug zero into ≤-refl
                                -- then I will get zero ≤ zero.
≤-refl {suc n} = s≤s ≤-refl       -- The hole showed me that I need to show that (suc n ≤ suc n)
                                -- (suc n ≤ suc m) is the output of the constructor s≤s.
                                -- So I apply that constructor with a hole an an argument.
                                -- The hole says I need to show that n ≤ n.
                                -- (n ≤ n) is the output of ≤-refl, so I can use ≤-refl inductively.
                                -- ≤-refl doesn't need any arguments from me, so I'm done.

-- transitivity

≤-trans : ∀ {m n p : ℕ}
  → m ≤ n                      -- Since this thing has two conditions, then I must split them into 
  → n ≤ p                      -- two "arguments"
  -------
  → m ≤ p

--≤-trans {n = zero} = {!!}     -- I start with m ≤ zero and zero ≤ p. But then I don't know how to apply anything :c
--≤-trans {n = suc n} = {!!}

--≤-trans = {!!}                -- I don't know how to make the hole split on the definition of _≤_
≤-trans z≤n _ = z≤n             -- Ok... so manually and laboriously I say we're starting from z≤n
                                -- The hole tells me I need to show now that n ≤ p → zero ≤ p
                                -- Oh, ok. We need to provide bot conditions, and we can say a condition is irrelevant.
                                -- And I guess that makes sense, because it doesn't matter what we know about n ≤ p,
                                -- It must necessarily be true from z≤z that (zero ≤ p).
                                -- So I put _ as the second "argument" and the hole says: zero ≤ p
                                -- Since zero ≤ p is the output of z≤z, I apply that. C-SPC, done.
                                
≤-trans (s≤s m≤n) (s≤s n≤p) = (s≤s (≤-trans m≤n n≤p))
                                -- Ok. So this is like breaking on the definition of ℕ,
                                -- except we're breaking on the definition of _≤_. So we started with zero,
                                -- now we will do suc. So I write ≤-trans s≤s. Except that of course doesn't compile.
                                -- So I put in some variable x (which in the book is m≤n).
                                -- Now I am getting suc n ≤ p → suc m ≤ p from the hole.
                                -- I guess I cal plug (s≤s y) in the other argument too.
                                -- Now I am getting suc m ≤ suc n in the hole. Uh... what now.
                                -- I guess I need to get from suc m ≤ suc n to m ≤ n, so I use (s≤s ?)
                                -- Now the hole says m ≤ n.
                                -- I guss I can use induction now. (≤-trans ? ?) does in the hole
                                -- Goals for the holes are now: m \le _n_30 and _n_30 ≤ n.
                                -- These look like m ≤ n and n ≤ p maybe? Sort of?
                                -- I plugged in x and y and it works, but I'm not sure why again.
                                -- When investigating what it could mean i renamed x and y to m≤n and n≤p...

-- Anti-symmetry

≤-antisym : ∀ {m n : ℕ}
  → m ≤ n
  → n ≤ m
  → m ≡ n

≤-antisym z≤n z≤n = refl
≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m) -- woot!

-- Why is it ok to omit ≤-antisym z≤n s≤s and ≤-antisym s≤s z≤n?
-- Becuase that can't happen and agda somehow figures it out I guess.
-- Mostly, because agda doesn't shout at me to do it though...

-- Total

data Total (m n : ℕ) : Set where

  forward :
       m ≤ n
       -----
    → Total m n

  flipped :
       n ≤ m
       -----
    → Total m n

-- We're defining it like this because we don't have any other way of
-- defining a logical OR (disjunction). Otherwise we could have probably
-- just written the definition as usual.
-- This is annoyingly obfuscated now.

--≤-total : ∀ (m n : ℕ) → Total m n
--≤-total zero n = forward z≤n
--≤-total (suc m) zero = flipped z≤n
----≤-total (suc m) (suc n) = forward (s≤s {!!})
--≤-total (suc m) (suc n) with ≤-total m n
--...                        | forward m≤n = {!!}
--...                        | flipped n≤m = {!!}

-- Helper function
≤-helper : ∀ {m n : ℕ} → Total m n → Total (suc m) (suc n)
≤-helper (forward m≤n) = forward (s≤s m≤n)
≤-helper (flipped n≤m) = flipped (s≤s n≤m)

≤-total' : ∀ (m n : ℕ) → Total m n
≤-total' zero n = forward z≤n
≤-total' (suc m) zero = flipped z≤n
≤-total' (suc m) (suc n) = ≤-helper(≤-total' m n)

-- Helper function with `where`
≤-total'' : ∀ (m n : ℕ) → Total m n
≤-total'' zero n = forward z≤n
≤-total'' (suc m) zero = flipped z≤n
≤-total'' (suc m) (suc n) = helper (≤-total'' m n)
  where
    helper : Total m n → Total (suc m) (suc n)
    helper (forward m≤n) = forward (s≤s m≤n)
    helper (flipped n≤m) = flipped (s≤s n≤m)

-- The dreaded `with`
≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero n = forward z≤n
≤-total (suc m) zero = flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n                   
...                        | forward m≤n = forward (s≤s m≤n)
...                        | flipped n≤m = flipped (s≤s n≤m)

-- So this means, first apply ≤-total m n
--   and then, take the result (which is Total m n)
--   and do with it one of those two cases.
-- Whatever the cases return, is the proof for the original statement.
-- Ok. I kind of see how this makes sense.
-- I just wish the type of what with gets and returns were more explicit.

-- Monotonicity

-- I think if I met an operator at a party I'd ask if it is smooth.

+-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
  → n + p ≤ n + q
+-monoʳ-≤ zero p q p≤q = p≤q
+-monoʳ-≤ (suc n) p q p≤q = s≤s (+-monoʳ-≤ n p q p≤q)

-- I think this is what's happening here:
-- +-monoʳ-≤ n p q p≤q    returns     n + p ≤ n + q   (induction)
-- n + p ≤ n + q          returns     suc(n + p) ≤ suc(n + p)
--
-- and i guess from the definition of addition?
-- suc(n + p) ≤ suc(n + p) returns   suc(n) + p ≤ suc(n) + p

+-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
  → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n rewrite +-comm m p | +-comm n p = +-monoʳ-≤ p m n m≤n

-- Here we just rewrite the inequality by applying commutativity of addition
-- and then we can use the proof for the right side of monotonicty.
-- This was fairly straightforward.
--
-- I wonder if this can be done with jellyfish.

+-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
  → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q =  ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)

-- Exercise *-mono-≤

open import Data.Nat using (_*_)
open import Data.Nat.Properties using (*-comm)

*-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
  → n * p ≤ n * q
*-monoʳ-≤ zero p q p≤q = z≤n
*-monoʳ-≤ (suc n) p q p≤q = +-mono-≤ p q (n * p) (n * q) p≤q (*-monoʳ-≤ n p q p≤q) -- p + n * p ≤ q + n * q

-- This was way more difficult at the outset then it is at the end.

*-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
  → m * p ≤ n * p
  -- p * m ≤ p * n
  -- p→n, m→p, n→q ⇒ p m n
*-monoˡ-≤ m n p m≤n rewrite *-comm m p | *-comm n p = *-monoʳ-≤ p m n m≤n

-- Lost 10 minutes on a typo (*-comm p m → *-comm m p)

*-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
  → m * p ≤ n * q
*-mono-≤ m n p q m≤n p≤q = ≤-trans (*-monoˡ-≤ m n p m≤n) (*-monoʳ-≤ n p q p≤q)

-- Ok, that last one was easier than expected.


-- Strict inequality

infix 4 _<_

data _<_ : ℕ → ℕ → Set where

  z<s : ∀ {n : ℕ} → zero < suc n -- zero < 1
  s<s : ∀ {m n : ℕ} → m < n → suc m < suc n


--≤-<-equiv : ∀ (m n : ℕ) → (suc m ≤ n) ≡ (m < n) -- TODO
--<-≤-equivalence m < n → suc m ≤ n

<-trans : ∀ {m n p : ℕ} → m < n → n < p → m < p 
<-trans z<s (s<s n<p) = z<s
<-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)

<-⇒-≤ : ∀ {m n : ℕ} → m < n → (suc m) ≤ n
<-⇒-≤ z<s = s≤s z≤n
<-⇒-≤ (s<s m<n) = s≤s (<-⇒-≤ m<n)

≤-⇒-< : ∀ (m n : ℕ) → suc m ≤ n → m < n
≤-⇒-< zero zero ()
≤-⇒-< zero (suc n) (s≤s sm≤n₁) = z<s
≤-⇒-< (suc m) zero ()
≤-⇒-< (suc m) (suc n) (s≤s sm≤n₁) = s<s (≤-⇒-< m n sm≤n₁)  

<-trans' : ∀ {m n p : ℕ} → m < n → n < p → m < p
<-trans' {m} {n} {p} m<n n<p = ≤-⇒-< m p sm≤p
  where
    -- m<n : m < n
    -- n<p : n < p
    
    sm≤n : (suc m) ≤ n
    sm≤n = <-⇒-≤ m<n
    
    sn≤p : (suc n) ≤ p
    sn≤p = <-⇒-≤ n<p

    n≤sn : n ≤ suc n
    n≤sn = +-mono-≤ zero (suc zero) n n z≤n ≤-refl

    sm≤p : (suc m) ≤ p
    sm≤p = ≤-trans sm≤n (≤-trans n≤sn sn≤p)   


data Trichotomy : ∀ (n m : ℕ) → Set where

    lesser  : ∀ (n m : ℕ) → n < m → Trichotomy n m
    equal   : ∀ (n m : ℕ) → n ≡ m → Trichotomy n m
    greater : ∀ (n m : ℕ) → m < n → Trichotomy n m

inv-s<s : ∀ {n m : ℕ} → suc n < suc m → n < m
--inv-z<s : ∀ {n m : ℕ} → zero < suc n → zero < n

<-trichotomy : ∀ (n m : ℕ) → Trichotomy n m
<-trichotomy zero zero = equal zero zero refl
<-trichotomy zero (suc m) = lesser zero (suc m) z<s
<-trichotomy (suc n) zero = greater (suc n) zero z<s
<-trichotomy (suc n) (suc m) = <-trichotomy-helper (<-trichotomy n m)
  where
    <-trichotomy-helper : Trichotomy n m → Trichotomy (suc n) (suc m)
    <-trichotomy-helper (lesser  n m n<m) = lesser (suc n) (suc m) (s<s n<m)
    <-trichotomy-helper (equal   n m n≡m) = equal (suc n) (suc m) (cong suc n≡m)
    <-trichotomy-helper (greater n m m<n) = greater (suc n) (suc m) (s<s m<n)
    
-- This is what C-c C-a did for me:
--    <-trichotomy-helper (lesser .0 .(suc _) z<s) = lesser 1 (suc (suc n)) (s<s z<s)
--    <-trichotomy-helper (lesser .(suc _) .(suc _) (s<s x)) = lesser (suc (suc m)) (suc (suc n)) (s<s (s<s x))
--    <-trichotomy-helper (equal n .n refl) = equal (suc m) (suc m) refl
--    <-trichotomy-helper (greater .(suc _) .0 z<s) = greater (suc (suc n)) 1 (s<s z<s)
--    <-trichotomy-helper (greater .(suc _) .(suc _) (s<s x)) = greater (suc (suc n)) (suc (suc m)) (s<s (s<s x)) 


+-mono-< : ∀ (m n p q : ℕ) → m < n → p < q → m + p < n + q
+-mono-< m n p q m<n p<q = <-trans (+-mono-<ˡ m n p m<n) (+-mono-<ʳ n p q p<q)

  where
    +-mono-<ʳ : ∀ (n p q : ℕ) → p < q → n + p < n + q
    +-mono-<ʳ zero p q p<q = p<q
    +-mono-<ʳ (suc n) p q p<q = s<s (+-mono-<ʳ n p q p<q)
    
    +-mono-<ˡ : ∀ (m n p : ℕ) → m < n → m + p < n + p
    +-mono-<ˡ m n p m<n rewrite +-comm m p | +-comm n p = +-mono-<ʳ p m n m<n

--≤-iff-< : ∀ {m n : ℕ} → ?

data even : ℕ → Set
data odd  : ℕ → Set

data even where
  zero : even zero                           
  sucE  : ∀ {n : ℕ} → odd n → even (suc n)      

data odd where
  sucO : ∀ {n : ℕ} → even n → odd (suc n)

e+e≡e : ∀ {m n : ℕ} → even m → even n → even (m + n)
o+e≡o : ∀ {m n : ℕ} → odd m → even n → odd (m + n)

e+e≡e zero en = en
e+e≡e (sucE om) en = sucE (o+e≡o om en)
o+e≡o (sucO em) en = sucO (e+e≡e em en)

e+o≡o : ∀ {m n : ℕ} → even m → odd n → odd (m + n)
e+o≡o {m} {n} em on rewrite +-comm m n = o+e≡o on em

o+o≡e : ∀ {m n : ℕ} → odd m → odd n → even (m + n)
o+o≡e (sucO zero) (sucO zero) = sucE (sucO zero)

o+o≡e {m} {n} om (sucO en) rewrite +-comm m n = sucE (e+o≡o en om) -- even (om + sucO en)

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
from (p O) = (from p) + (from p)
from (p I) = (from p) + (from p) + 1

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc n)  = inc (to n)

data One : Bin → Set where
  just_I : One (⟨⟩ I)
  I⋯I : ∀ {b : Bin} → One b → One (b I)
  I⋯O : ∀ {b : Bin} → One b → One (b O)

bin₀ = ⟨⟩ O
bin₁ = ⟨⟩ I
bin₂ = ⟨⟩ I I
bin₃ = ⟨⟩ I I O

p₁ = just_I
p₂ = I⋯I p₁
p₃ = I⋯I p₂

data Can : Bin → Set where
  just_O : Can (⟨⟩ O)
  I⋯ : ∀ {b : Bin} → One b → Can b

p₄ = just_O
p₅ = I⋯ p₁
p₆ = I⋯ p₂
p₇ = I⋯ p₃ 

--f : Bin → ℕ
--f (⟨⟩ I) = 1
--f (p I) = f (p) + 1
--f (p O) = 0
--f ⟨⟩ = 0

inc-preserves-one : ∀ {b : Bin} → One b → One (inc b)
inc-preserves-one just_I = I⋯O just_I
inc-preserves-one (I⋯I oneb) = I⋯O (inc-preserves-one oneb)
inc-preserves-one (I⋯O oneb) = I⋯I oneb
    
inc-preserves-can : ∀ {b : Bin} → Can b → Can (inc b)
inc-preserves-can   {⟨⟩}     canb             = I⋯ just_I
inc-preserves-can   {⟨⟩ O}   just_O           = I⋯ just_I
inc-preserves-can   {b O}   (I⋯ onebO)       = I⋯ (inc-preserves-one onebO)
inc-preserves-can   {b I}   (I⋯ onebI)       = I⋯ (inc-preserves-one onebI)

-- TODO examine the case of minus
minus : ∀ (n m : ℕ) → m ≤ n → ℕ
minus' : ∀ {n m : ℕ} → m ≤ n → ℕ

-- Auto-fill solution: C-c C-a
-- Take me to the definition: M-.

to-preserves-can : ∀ {n : ℕ} → Can (to n)
to-preserves-can {zero} = just_O
to-preserves-can {suc n} = I⋯ (can⇒one+1 (to-preserves-can {n}))
  where
    can⇒one+1 : ∀ {b : Bin} → Can (b) → One (inc b)
    can⇒one+1 {⟨⟩} canb = just_I
    can⇒one+1 {⟨⟩ O} just_O = just_I
    can⇒one+1 {b O} (I⋯ onebO) = inc-preserves-one onebO
    can⇒one+1 {b I} (I⋯ onebI) = inc-preserves-one onebI

data NonZero : ℕ → Set where
  non-zero : ∀ {n : ℕ} → NonZero (suc n)

open import chapter-2 using (+-suc)

--f : ∀ (b : Bin) → inc (b O) ≡ (b I)

zero<one : ∀ {b : Bin} → One b → zero < (from b)

shift : ∀ {n : ℕ} → zero < n → to (n + n) ≡ to(n) O
shift {n} = {!!} 
--shift {suc n} rewrite +-suc n (suc n)
--                    | +-suc n n
--                   = {!!}

to-from≡id : ∀ {b : Bin} → Can b → to (from b) ≡ b
to-from≡id {⟨⟩ O} just_O = refl
to-from≡id {p O} (I⋯ (I⋯O onepO)) rewrite shift (zero<one onepO) = {!!}
to-from≡id {⟨⟩ I} (I⋯ just_I) = {!!}
to-from≡id {p I} (I⋯ (I⋯I onepI)) = {!!}

  --where
    
    --_ = to (from (p I)) ≡ inc (to (2 * from(p)))
    --_ = to (from (p I)) ≡ 
    
    -- (from p) + (from p)


-- alt + . GO TO STUFF
