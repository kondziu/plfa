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
--
-- And let's say there is a couple of functions f g,
--   which take an argument of type A
--   and return a B that wraps that argument.
--
-- If we provide evidence that for all x's of type A, f x ≡ g x
-- then f ≡ g.
--
-- So basically the function type A → B changes to ∀ (x : A) → B x.

-- Um.
--
-- "Dependent types are types whose definition depends on a value."
--
-- This does not help. I need an adult.

-- Oh, wait. {B : A → Set} means B is the type of A, right?
-- Ugh, I don't know.

