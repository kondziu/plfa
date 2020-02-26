import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)

_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
(g ∘ f) x  = g (f x)

_∘′_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
g ∘′ f  =  λ x → g (f x)

-- Extensionality
postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x) → f ≡ g

-- For any functions f and g,
-- If you show me a proposition that for any x,
--        the result of f x and g x is the same
-- Then, I will provide evidence that f and g
--        are equivalent.

_+′_ : ℕ → ℕ → ℕ
m +′ zero  = m
m +′ suc n = suc (m +′ n)

same-app : ∀ (m n : ℕ) → m +′ n ≡ m + n
same-app m zero =
  begin (m +′ zero) ≡⟨⟩ m ≡⟨⟩ zero + m ≡⟨ +-comm zero m ⟩ m + zero ∎
same-app m (suc n) =
  begin m +′ suc n ≡⟨⟩ suc (m +′ n) ≡⟨ cong suc (same-app m n) ⟩
        suc (m + n) ≡⟨ cong suc (+-comm m n) ⟩
        suc (n + m) ≡⟨⟩ (suc n) + m ≡⟨ +-comm (suc n) m ⟩ m + suc n ∎  

same : _+′_ ≡ _+_
same = extensionality (λ m → extensionality (λ n → same-app m n))

-- I don't think I understand this. Lets go through this slowly.
--
-- The proof that _+_ ≡ _+′_ is that:
--
--   (Starting form the end) λ n → same-app m n (where m is some m)
--   same-app m n produces evidence that m +′ n ≡ m + n
--   and now we know that (m, n : ℕ) I think
--   so λ n → same-app m n is the same as λ n → m +′ n ≡ m + n
--
--   Do now the left extensionality:
--   we provide evidence that λ n → m +′ n ≡ m + n, which
--   returns evidence that... what?
--
--      m +′_ ≡ m +_ ?
--
--   We then do the right extentionality, to which we provide
--   evidence that λ m → m +′_ ≡ m +_, which I guess gives us...
--   _+′_ ≡ _+_ or something like that.
--
--   Oh, QED. Ok.

postulate
  ∀-extensionality : ∀ {A : Set} {B : A → Set} {f g : ∀(x : A) → B x}
    → (∀ (x : A) → f x ≡ g x) → f ≡ g

-- Um.
--
-- So let's say there is some type A.
--
-- And let's say there is some predicate B from A to Set.
-- So it takes a TYPE A and returns an unknown member of Set.
-- So it returns any value of any standard type (member of Set).
-- B is a CONSTRUCTOR.
--
-- And let's say there is a couple of functions f g,
--   which take an argument of type A
--   and return a B that wraps that argument.
--
-- If we provide evidence that for all x's of type A, f x ≡ g x
-- then f ≡ g.
--
-- So basically the function type A → B changes to ∀ (x : A) → B x.
--
-- Um.
--
-- "Dependent types are types whose definition depends on a value."
--
-- This does not help. I need an adult.
--
-- Oh, wait. {B : A → Set} means B is the type of A, right?
-- Ugh, I don't know.
--
-- From Colette:
-- A dependent function doesn't just take any value, it takes a value
-- that can be refered to in other places. What it returns depends on
-- what you give it.
--
-- I still don't get it.

-- Isomorphism

infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to : A → B                            -- a function from A to B
    from : B → A                          -- a function from B to A
    from∘to : ∀ (x : A) → from (to x) ≡ x -- evidence that from is a left-inverse of to
    to∘from : ∀ (y : B) → to (from y) ≡ y -- evidence that to is right-inverse of from    
open _≃_

-- what is left-inverse and right-inverse:

-- From MathWorld
-- Given a map f:S->T between sets S and T, the map g:T->S is called a
-- left inverse to f provided that g degreesf=id_S, that is, composing
-- f with g from the left gives the identity on S. Often f is a map of
-- a specific type, such as a linear map between vector spaces, or a
-- continuous map between topological spaces, and in each such case,
-- one often requires a right inverse to be of the same type as that of f. 

-- a record o.o
-- this record is equivalent to this:

data _≃′_ (A B : Set) : Set where
  mk-≃′ : ∀ (to : A → B) →
          ∀ (from : B → A) →
          ∀ (from∘to : (∀ (x : A) → from (to x) ≡ x)) →
          ∀ (to∘from : (∀ (y : B) → to (from y) ≡ y)) →
          A ≃′ B

to′ : ∀ {A B : Set} → (A ≃′ B) → (A → B)
to′ (mk-≃′ f g g∘f f∘g) = f

from′ : ∀ {A B : Set} → (A ≃′ B) → (B → A)
from′ (mk-≃′ f g g∘f f∘g) = g

from∘to′ : ∀ {A B : Set} → (A≃′B : A ≃′ B) → (∀ (x : A) → from′ A≃′B (to′ A≃′B x) ≡ x)
from∘to′ (mk-≃′ f g g∘f f∘g) = g∘f

to∘from′ : ∀ {A B : Set} → (A≃′B : A ≃′ B) → (∀ (y : B) → to′ A≃′B (from′ A≃′B y) ≡ y)
to∘from′ (mk-≃′ f g g∘f f∘g) = f∘g

-- Data 



