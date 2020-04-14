import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import chapter-5 using (_≃_; _≲_; extensionality)
open chapter-5.≃-Reasoning

-- Conjunction is product
data _×_ (A B : Set) : Set where

  ⟨_,_⟩  : A → B → A × B       -- So this is basically a constructor that's supposed to
                                -- look like a pair of values, but the ⟨ ⟩ symbols don't have
                                -- any intrinsic meaning in Agda. We give them meaning by
                                -- defining this constructor, in fact.
                                --
                                -- Since we have this freedom it is also possible to define
                                -- this as _,_ or even x_,_y if we feel so inclined.
                                -- (Although only one of these makes sense...)
                                --
                                -- This will be useful to represent pairs of types and
                                -- other cartesian product things.

proj₁ : {A B : Set} → A × B → A -- proj probably stands for projection (I am told: definitely)
proj₁ ⟨ x , y ⟩ = x

proj₂ : {A B : Set} → A × B → B
proj₂ ⟨ x , y ⟩ = y

record _x'_ (A B : Set) : Set where
  field
    proj₁' : A
    proj₂' : B
open _x'_

_ = record { proj₁' = 1 ; proj₂' = 2 } -- this is the same as
_ = ⟨ 1 , 2 ⟩                           -- this

-- I guess there are more than one representations of the same concept, and which one might
-- be more natural to pick over the other in specific cases.

-- terminology note from the book;
--
--   When ⟨_,_⟩ appears in a term on the right-hand side of an equation we refer to it as a
--   constructor, and when it appears in a pattern on the left-hand side of an equation we
--   refer to it as a destructor.
--
--   Other terminology refers to ⟨_,_⟩ as introducing a conjunction, and to proj₁ and proj₂
--   as eliminating a conjunction; indeed, the former is sometimes given the name ×-I and
--   the latter two the names ×-E₁ and ×-E₂.

η-x : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-x ⟨ x , y ⟩ = refl

-- Probably refers to η-reduction?
--
-- From wiki:
--
--     η-reduction expresses the idea of extensionality, which in this context is that
--     two functions are the same if and only if they give the same result for all
--     arguments.

infixr 2 _×_              -- m ≤ n × n ≤ p is equivalent to (m ≤ n) × (n ≤ p)

data Bool : Set where
  true  : Bool
  false : Bool

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

_ = ⟨ true  , aa ⟩
_ = ⟨ true  , bb ⟩
_ = ⟨ true ,  cc ⟩
_ = ⟨ false , aa ⟩
_ = ⟨ false , bb ⟩
_ = ⟨ false , cc ⟩

×-count : Bool × Tri → ℕ
×-count ⟨ true  , aa ⟩  =  1
×-count ⟨ true  , bb ⟩  =  2
×-count ⟨ true  , cc ⟩  =  3
×-count ⟨ false , aa ⟩  =  4
×-count ⟨ false , bb ⟩  =  5
×-count ⟨ false , cc ⟩  =  6

×-comm : ∀ {A B : Set} → A × B ≃ B × A
×-comm =
  record {
    to = λ{ ⟨ x , y ⟩ → ⟨ y , x ⟩ };
    from = λ{ ⟨ y , x ⟩ → ⟨ x , y ⟩ };
    from∘to = λ{ ⟨ x , y ⟩ → refl };
    to∘from = λ{ ⟨ y , x ⟩ → refl }}

--    commutativity
-- vs commutativity up to isomoprphism
--
-- So, while ℕ × Bool is not the same as Bool × ℕ, there is an isomorphism between
-- those two types. Any value of type ℕ × Bool has a corresponding value of type
-- Bool × ℕ.

x-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
x-assoc =
  record {
    to = λ { ⟨ ⟨ x , y ⟩ , z ⟩ →  ⟨ x , ⟨ y , z ⟩ ⟩ };
    from = λ { ⟨ x , ⟨ y , z ⟩ ⟩ → ⟨ ⟨ x , y ⟩ , z ⟩ };
    from∘to = λ { ⟨ ⟨ x , y ⟩ , z ⟩ → refl };
    to∘from = λ { ⟨ x , ⟨ y , z ⟩ ⟩ → refl }}

--    associativity
-- vs associativity up to isomorphism
--
-- by analogy to above

-- EXERCISE ⇔≃×

-- Show that A ⇔ B as defined earlier is isomorphic to (A → B) × (B → A).

-- Reminder: ⇔ is this
record _⇔_ (A B : Set) : Set where
  field
    to : A → B
    from : B → A
open _⇔_

-- This basically defines a relation between A and B that states that A and B are
-- equivalent... ?
--
-- As in "A if and only if B."
--
-- Ok.
--
-- And I'm supposed to show that this relation is the same as saying "if A then B" and
-- "if B then A," which makes sense.
--
-- Oh, and isomorphism, is, of course, what we have been doing all along: _≃_, which
-- is proven by filling in record { to, from, to∘from, from∘to }.
--
-- Ok, good talk.

-- No idea what to call this thing, so I'll call it this just to be annoying... to myself?
⇔-≃-←×→ : ∀ {A B : Set} → A ⇔ B ≃ (A → B) × (B → A)
⇔-≃-←×→ = record {                        -- whose stupid idea was it to name it this...
    to = λ { A⇔B → ⟨ (to A⇔B) , (from A⇔B) ⟩ } ;                  -- i hate agda
    from = λ { ⟨ A→B , B→A ⟩ →  record { to = A→B; from = B→A } }; -- and myself
    to∘from = λ { ⟨ A→B , B→A ⟩ → refl };
    from∘to = λ { A⇔B → refl }}

-- I guess I was probably supposed to call it ⇔≃×
⇔≃× : ∀ {A B : Set} → A ⇔ B ≃ (A → B) × (B → A)
⇔≃× = ⇔-≃-←×→

-- TRUSTH IS (an absolute) UNIT

-- Unlike Booleans, Truth is a type onto itself.
data ⊤ : Set where tt : ⊤

-- what's wrong with the word "true?"
-- is it secretly not "true" but "top" or something?

-- From the book:
--
--   There is an introduction rule, but no elimination rule. Given evidence that ⊤ holds,
--   there is nothing more of interest we can conclude. Since truth always holds, knowing
--   that it holds tells us nothing new.
--
-- Evidence that Phil does not care about truth.

-- I am told that an introduction rule creates a value this type, and an elimination rule
-- takes a value of this type and does something with it, eg. producing a value of a different
-- type.


-- From the book:
--
--   The nullary case of η-× is η-⊤, which asserts that any value of type ⊤ must be equal
--   to tt:
--
-- Phil is making up words?
--
-- From wiktionary:
--
--   nullary: (mathematics, of a function) Taking no entries; having trivial domain; having
--            the arity of zero.
--
-- Note to self: don't play scrabble with Phil.

η-⊤ : ∀ (w : ⊤) → tt ≡ w
η-⊤ tt = refl

⊤-count : ⊤ → ℕ
⊤-count tt = 1

⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A
⊤-identityˡ =
  record {
    to =  λ ⊤×A → proj₂ ⊤×A;
    from = λ A →  ⟨ tt , A ⟩; -- :p
    to∘from =  λ A → refl;
    from∘to = λ { ⟨ tt , A ⟩ → refl }}

⊤-identityʳ : ∀ {A : Set} → (A × ⊤) ≃ A
⊤-identityʳ = 
  record {
    to =  λ A×⊤ → proj₁ A×⊤;
    from = λ A → ⟨ A , tt ⟩;
    to∘from =  λ A → refl;
    from∘to = λ { ⟨ A , tt ⟩ → refl }}
-- ⊤-identityʳ {A} = ≃-begin (A × ⊤) ≃⟨ ×-comm ⟩ (⊤ × A) ≃⟨ ⊤-identityˡ ⟩ A ≃-∎

-- DISJUNCTION to wąsata ryba
-- (joke reference: https://pl.wikipedia.org/wiki/Sum_pospolity)

data _⊎_ (A B : Set) : Set where

  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

-- In other words: given the evidence that either A or B is true
--                 we can provide evidence that A ⊎ B.

case-⊎ : ∀ {A B C : Set} → (A → C) → (B → C) → A ⊎ B → C
case-⊎ A→C B→C (inj₁ A) = A→C (A) -- if we know A, apply A to A→C to get C
case-⊎ A→C B→C (inj₂ B) = B→C (B) -- if we know B, apply B to B→C to get C

-- From book, a note on terminology:
--
--   When inj₁ and inj₂ appear on the right-hand side of an equation
--   we refer to them as constructors, and when they appear on the
--   left-hand side we refer to them as destructors. We also refer to
--   case-⊎ as a destructor, since it plays a similar role. Other
--   terminology refers to inj₁ and inj₂ as introducing a disjunction,
--   and to case-⊎ as eliminating a disjunction; indeed the former are
--   sometimes given the names ⊎-I₁ and ⊎-I₂ and the latter the name
--   ⊎-E.

η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ x) = refl
η-⊎ (inj₂ y) = refl

uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B) → case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-⊎ h (inj₁ x) = refl
uniq-⊎ h (inj₂ y) = refl

infixr 1 _⊎_ -- A × C ⊎ B × C is the same as (A × C) ⊎ (B × C)

-- EXERCISE ⊎-comm

⊎-comm : ∀ {A B : Set} → A ⊎ B ≃ B ⊎ A
⊎-comm = 
  record {
    to =  λ { (inj₁ a) → inj₂ a ;
              (inj₂ b) → inj₁ b };
    from = λ { (inj₁ b) → inj₂ b ;
               (inj₂ a) → inj₁ a };
    to∘from = λ { (inj₁ b) → refl ;
                  (inj₂ a) → refl };
    from∘to = λ { (inj₁ a) → refl ;
                  (inj₂ b) → refl }}

-- EXERCISE ⊎-assoc

⊎-assoc : ∀ {A B C : Set} → ((A ⊎ B) ⊎ C) ≃ (A ⊎ (B ⊎ C))
⊎-assoc = 
  record {
    to =  λ { (inj₁ (inj₁ a)) → inj₁ a;
              (inj₁ (inj₂ b)) → inj₂ (inj₁ b);
              (inj₂ c) → inj₂ (inj₂ c)};
    from = λ { (inj₁ a) → inj₁ (inj₁ a);
               (inj₂ (inj₁ b)) → inj₁ (inj₂ b);
               (inj₂ (inj₂ c)) → inj₂ c};
    to∘from = λ { (inj₁ a) → refl; 
                  (inj₂ (inj₁ b)) → refl;
                  (inj₂ (inj₂ c)) → refl};
    from∘to = λ { (inj₁ (inj₁ a)) → refl;
                  (inj₁ (inj₂ b)) → refl;
                  (inj₂ c) → refl}}

-- I want kimchi NAO :<
-- NO IDEA :<
-- Kolonial, i think
-- i could MAKE KIMCHI
-- mebbe
-- it will be ready in... a month?

open import IO
_ = run (putStrLn "kimchi!")


-- FALSE IS EMPTY

data ⊥ : Set where
  -- lies!

-- Remember when in Sailor Moon whenever somebody said something
-- really dumb the other characters suddely fall over on the heads?
--
--  ⊤ ◠ ⊥

-- ex falso
⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()

-- From the book:
--
--   This is our first use of the absurd pattern ().
--
-- No it isn't:
--
--   chapter-3.agda:344:≤-⇒-< zero zero ()
--   chapter-3.agda:346:≤-⇒-< (suc m) zero ()

uniq-⊥ : ∀ {C : Set} (h : ⊥ → C) (w : ⊥) → ⊥-elim w ≡ h w
uniq-⊥ h ()

⊥-count : ⊥ → ℕ
⊥-count ()

-- EXERCISE ⊥-identityˡ

⊥-identityˡ : ∀ {A : Set} → (⊥ ⊎ A) ≃ A
⊥-identityˡ {A} =
  record {
    to =  λ { (inj₂ a) → a };
    from = λ { a → inj₂ a };
    to∘from = λ { a → refl };
    from∘to = λ { (inj₂ a) → refl }}  

-- EXERCISE ⊥-identityʳ

⊥-identityʳ : ∀ {A : Set} → (A ⊎ ⊥) ≃ A
⊥-identityʳ {A} = ≃-begin (A ⊎ ⊥) ≃⟨ ⊎-comm ⟩ (⊥ ⊎ A) ≃⟨ ⊥-identityˡ ⟩ A ≃-∎
