-- EQUALITY: Equality and equational reasoning

-- What's this about parameters being an index to other parameters?
-- Can we talk a bit more about what a set is?

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : ∀ {A B C : Set} (f : A → B → C) {x₁ x₂ : A} {y₁ y₂ : B} → x₁ ≡ x₂ → y₁ ≡ y₂ → f x₁ y₁ ≡ f x₂ y₂
cong₂ f refl refl = refl

cong-app : ∀ {A B : Set} {f g : A → B} → f ≡ g → ∀ (x : A) → f x ≡ g x
cong-app refl x = refl

subst : ∀ {A : Set} {x y : A} (P : A → Set) → x ≡ y → P x → P y
subst P refl px = px

-- Chains of equations

-- accidentally found out C-c C-? lists major mode bidings starting with C-c 

module ≡-Reasoning {A : Set} where

  infix  1  begin_
  infixr 2  _≡⟨⟩_ _≡⟨_⟩_
  infix  3  _∎

  begin_ : ∀ {x y : A}
    → x ≡ y → x ≡ y
  begin x≡y = x≡y

  _≡⟨⟩_ : ∀ (x : A) {y : A} → x ≡ y → x ≡ y
  x ≡⟨⟩ x≡y = x≡y

  _≡⟨_⟩_ : ∀ (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
  x ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

  _∎ : ∀ (x : A) → x ≡ x
  x ∎ = refl

open ≡-Reasoning

-- Jellyfish are just the lies of clever tricks ;-;
-- I kind of understand it, but I don't think I could come up with somethign like this.

trans′ : ∀ {A : Set} {x y z : A}
  → x ≡ y
  → y ≡ z
    -----
  → x ≡ z
trans′ {A} {x} {y} {z} x≡y y≡z =
  begin
    x
  ≡⟨ x≡y ⟩
    y
  ≡⟨ y≡z ⟩
    z
  ∎

-- Chains of equations, another example

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero    + n  =  n
(suc m) + n  =  suc (m + n)

-- postulate (I'm going to prove these for practice)
+-identity : ∀ (m : ℕ) → m + zero ≡ m
+-identity zero = refl
+-identity (suc m) = cong suc (+-identity m)

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n = cong suc (+-suc m n)

-- Using postulate revents it from complaining that there's no proof.


+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero = begin m + zero ≡⟨ +-identity m ⟩ m ≡⟨ refl ⟩ zero + m ∎
+-comm m (suc n) = begin m + suc n ≡⟨ +-suc m n ⟩ suc (m + n) ≡⟨ cong suc (+-comm m n) ⟩ (suc n) + m ∎

-- Yup, the jellyfish still work.

-- EXERCISE ≤-Reasoning

{- The proof of monotonicity from Chapter Relations can be written in
   a more readable form by using an analogue of our notation for
   ≡-Reasoning. Define ≤-Reasoning analogously, and use it to write
   out an alternative proof that addition is monotonic with regard to
   inequality. Rewrite all of +-monoˡ-≤, +-monoʳ-≤, and +-mono-≤. -}

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n : ℕ} → zero ≤ n
  s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n

infix 4 _≤_

-- postulate (I'm going to prove these for practice).
≤-trans : ∀ {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p
≤-trans z≤n _ = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

module ≤-Reasoning where

  infix  1 begin-≤_
  infixr 2 _≤⟨⟩_ _≤⟨_⟩_ _≡⟨_⟩-≤_
  infix  3 _∎-≤

  begin-≤_ : ∀ {x y : ℕ} → x ≤ y → x ≤ y
  begin-≤ x≤y = x≤y

  _∎-≤ : ∀ (x : ℕ) → x ≤ x
  zero ∎-≤ = z≤n
  suc x ∎-≤ = s≤s (x ∎-≤)

  _≤⟨⟩_ : ∀ (x : ℕ) {y : ℕ} → x ≤ y → x ≤ y
  x ≤⟨⟩ x≤y = x≤y

  _≤⟨_⟩_ : ∀ (x : ℕ) {y z : ℕ} → x ≤ y → y ≤ z → x ≤ z
  x ≤⟨ x≤y ⟩ y≤z = ≤-trans x≤y y≤z 

   {- So...
     x ≡⟨ y ⟩-≤ z 

     So there is some x and some z.
     x is an expression, and z looks like an expression, but
     actually it will be a series of ≤-jellyfish that all show
     that `something ≤ something else`. This kissy jellyfish
     should comport to that, so the return type is `x ≤ z`.

     But the kissy jellyfish shows that x can be transformed into 
     something that is lower than z via equality. So we should 
     have a  proof that that x ≡ y, because that's the 
     transformation. 

     And then, we have to say that whatever we transformed x 
     into is still lower than z.

     So that's why I think this type signature makes sense.
  -}
  _≡⟨_⟩-≤_ : ∀ (x : ℕ) {y z : ℕ} → x ≡ y → y ≤ z → x ≤ z

  {- So...

    In this proof we have to show that x≤z given that x≡y and 
    y≤z. This seems easy? Well, at least it seems true.
  -}
  y ≡⟨ refl ⟩-≤ y≤z = y≤z -- Seems suspiciously simple...

  {- Just for fun... -}
  --_≡⟨⟩-≤_ : ∀ (x : ℕ) {y : ℕ} → x ≡ y → x ≤ y
  --zero ≡⟨⟩-≤ refl = z≤n
  --suc x ≡⟨⟩-≤ refl = s≤s (x ≡⟨⟩-≤ refl)


open ≤-Reasoning

+-monoʳ-≤ : ∀ (n p q : ℕ) → p ≤ q → n + p ≤ n + q
+-monoʳ-≤ zero p q p≤q =
  begin-≤
    zero + p
  ≡⟨ refl ⟩-≤
    p
  ≤⟨ p≤q ⟩
    q
  ≡⟨ refl ⟩-≤
    zero + q
  ∎-≤

+-monoʳ-≤ (suc n) p q p≤q =
  begin-≤
    (suc n) + p
  ≡⟨ refl ⟩-≤
    suc (n + p)
  ≤⟨ s≤s (+-monoʳ-≤ n p q p≤q) ⟩
    suc (n + q)
  ≡⟨ refl ⟩-≤
    suc(n) + q
  ∎-≤

+-monoˡ-≤ : ∀ (m n p : ℕ) → m ≤ n → m + p ≤ n + p
+-monoˡ-≤ m n zero m≤n =
  begin-≤
    m + zero
  ≡⟨ +-comm m zero ⟩-≤
    zero + m
  ≡⟨ refl ⟩-≤
    m ≤⟨ m≤n ⟩ n
  ≡⟨ refl ⟩-≤
    zero + n
  ≡⟨ +-comm zero n ⟩-≤
    n + zero
  ∎-≤ 
+-monoˡ-≤ m n (suc p) m≤n =
  begin-≤
    m + (suc p)
  ≡⟨ +-comm m (suc p) ⟩-≤
    (suc p) + m
  ≡⟨ refl ⟩-≤
    suc (p + m)
  ≡⟨ cong suc (+-comm p m) ⟩-≤
    suc(m + p)
  ≤⟨ s≤s (+-monoˡ-≤ m n p m≤n) ⟩
    suc(n + p)
  ≡⟨ cong suc (+-comm n p) ⟩-≤
    suc(p + n)
  ≡⟨ refl ⟩-≤
    (suc p) + n
  ≡⟨ +-comm (suc p) n ⟩-≤
    n + (suc p)
  ∎-≤

+-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q =
  begin-≤
    m + p
  ≤⟨ ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q) ⟩
    n + q
  ∎-≤
{- cheating a bit, but whatever, this one was really tedious -}



--postulate
--  distater : zero ≡ suc zero

-- REWRITING

data even : ℕ → Set
data odd : ℕ → Set

data even where
  even-zero : even zero
  even-sec : ∀ {n : ℕ} → odd n → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ} → even n → odd (suc n)

{-# BUILTIN EQUALITY _≡_ #-}


even-comm : ∀ (m n : ℕ) → even (m + n) → even (n + m)
even-comm m n e[m+n] rewrite +-comm m n = e[m+n]

-- MULTIPLE REWRITES

+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ zero n rewrite +-identity n = refl
+-comm′ (suc m) n rewrite +-comm′ m n | +-suc n m = refl
              -- rewrite +-suc n m | +-comm′ m n = refl

-- +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
{- wait what? suc n m?

  So this rewrite takes              `(suc m) + n`
  and then somehow matches that with `n + (suc m)`
  which should yield                 `suc (n + m)`
  but which somehow yields           `suc (m + n)` ???

  so +-suc n m and +-comm′ m n are in reverse order here
  so I guess order does not matter?

  wtf
-}


-- REWRITING EXPANDED

even-comm′′′ : ∀ (m n : ℕ) → even (m + n) → even (n + m)
even-comm′′′ m n e[m+n] rewrite +-comm n m = e[m+n]

-- is syntactic sugar for:

even-comm′ : ∀ (m n : ℕ) → even (m + n) → even (n + m)
even-comm′ m n e[m+n] with  m + n   | +-comm m n               {- +-comm n m? -}
...                     | .(n + m) | refl        = e[m+n]     {- e[m+n] -}

-- OK, I'm going to look into what this means on my own because
-- the book doesn't say anything, and I don't remember Ana's
-- explanation from the reading group >_<

{-  
  "With abstraction was first introduced by Conor McBride 
   [McBride2004] and lets you pattern match on the result 
   of an intermediate computation by effectively adding an 
   extra argument to the left-hand side of your function."

  "In the simplest case the with construct can be used just 
   to discriminate on the result of an interediate 
   computation."

   From: https://agda.readthedocs.io/en/v2.5.2/language/with-abstraction.html
-}

{-
  So I guess this is a filter function for lists.
  I can't add it because it has Bools and lists,
  and I don't want to mess anything up with extra imports.
-}

{-
 filter : {A : Set} → (A → Bool) → List A → List A
 filter f [] = []                                -- applied to an empty list yields an empty list
 filter f (x :: xs) with f x                     -- applied to a non-empty list, um...
 ...                   | true = x :: filter f xs -- if (f x) ≡ true, then stuff?
 ...                   | false = filter f xs     -- if (f x) ≡ false, then other stuff?
                                                 -- not sure about that `≡` specifically, but
                                                 -- some kind of equivalence-type thing happens
-}

-- I'll try to write this using with, maybe.
{-
  +-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
  +-comm′ zero n rewrite +-identity n = refl
  +-comm′ (suc m) n rewrite +-comm′ m n | +-suc n m = refl

  +-identity : ∀ (m : ℕ) → m + zero ≡ m
  +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
-}

-- fuck this aaaaaaaaaaaaaaaaaa

-- So maybe just mechanistically:

{-
  "The rewrite construction takes a term eq of type lhs ≡ rhs, 
   where _≡_ is the built-in equality type, and expands to 
   a with-abstraction of lhs and eq followed by a match of the 
   result of eq against refl:

     f ps rewrite eq = v

     -->

     f ps with lhs | eq
     ...    | .rhs | refl = v
  "
-}

+-comm′′′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′′′ zero n with n + zero | +-identity n
...               | .n       | refl         = refl
--+-comm′′′ (suc m) n with suc n + m      | +-suc n m
--...                  | .(n + suc(m)) | r2 = {!!} 
--with n + suc m      | +-suc n m
--...                                                    | .(suc (n + m)) | refl      = {!!}
--+-comm′′′ (suc m) n  with (suc m) + n | +-comm′′′ m n | +-suc n m 
--...                   | .(n + (suc m)) | refl | refl = refl
--aAAAAAAAAAAAAAaaaaaAAAAAaaaaaaaaaaaaAAAAAAAAAAAAAAAAaaaaaaaaaAAAaaaaAAAaaa

-- I really just don't know.

----------------------------------------------------------
----------------------------------------------------------
----------------------------------------------------------

-- Whatever

-- Leibniz equality

-- \.= => ≐

-- "Spock's law." Nerds.

_≐_ : ∀ {A : Set} (x y : A) → Set₁
-- So I can see that this definition is generic, since it works
-- for any type (a type is an object of "kind" Set) and we call
-- that type A internally to this definition.

-- This definition is a definition of a function. Or is it?

-- We return a Set₁ which I understand is the set of all "kinds."
-- That is to say, I don't understand, but I'll go with it.
-- The book calls this LEVELS. 

-- Ha, I accidentally typed A as ∀

_≐_ {A} x y = ∀ (P : A → Set) → P x → P y
-- This is weird, I don't get it at all.
-- So, ∀ (P : A → Set) → P x → P y is a proposition!
-- Proposition is a thing of type Set₁
-- Uh... I'm not really sure what's going on here outside of
-- that. I'll keep reading, I guess.

-- I'm back. The way we use this is to say, let's say we have
-- a type A and some elements of that type called x and y. 
-- Then, next step. We look at each of the all properties that
-- x satisfies. (It's best to manage not to actually look at each
-- one individually, but as an abstract group, I guess?) Now, our
-- job is to prove that we y also satisfies each these properties.
-- If we manage to do that, cool, x ≐ y. If we fail with even one,
-- then we cannot show that x ≐ y, which I guess implies x ≐̸ y.

refl-≐ : ∀ {A : Set} {x : A} → x ≐ x
refl-≐ {A} {x} P Px = Px
-- Here, this works for any property and any type too.
-- Wait, reflexivity is not a constructor, it's a proposition!

trans-≐ : ∀ {A : Set} {x y z : A} → x ≐ y → y ≐ z → x ≐ z
trans-≐ {A} {x} {y} {z} x≐y y≐z P Px = y≐z P (x≐y P Px)
-- I can't split on x≐y and y≐z, because, I guess, it's not a
-- data type?
-- Oh, I forgot to add P and Px...
{- So...

  We need to present evidence that z satisfies P to win

  y≐z P ? needs evidence that y satifies P
          and returns evidence that z satisfies P

  x≐y P ? needs evidence that x satisfies P
          and returns evidence that y satisfies P

  Px is evidence that x satisfies P

  So we basically need to plug the output of (x≐y P Px)
  Into y≐z P ? and we get the evidence we need.
-}

sym-≐ : ∀ {A : Set} {x y : A} → x ≐ y → y ≐ x
sym-≐ {A} {x} {y} x≐y P = Qy {- XXX -}
  where
    Q : A → Set      -- Q is a property (it has the same type as P)
    Q z = P z → P x  -- If there is evidence that z satisfies P
                      -- Then property Q provides evidence that
                      -- x satisfies P ???
    Qx : Q x          -- Qx is a piece of evidence that x satisfies Q
    Qx = refl-≐ P     -- x satisfies Q because...
                      -- if we apply P to refl-≐ we get, uh... P x → P x?
                      -- which is the same as Q x, I guess?
    Qy : Q y          -- y satisfies Q because
    Qy = x≐y Q Qx     -- if we apply Q and Qx to x≐y we get, uh... Q y
                      -- So now when we got back to the hole marked XXX,
                      -- There the goal is P y → P x, which we can get
                      -- from the property Q of y, which we have proved
                      -- as Qy, so we plug Qy into XXX.

                      -- This is really convoluted, and I'm 100% certain
                      -- I couldn't prove this on my own at this point.

≡-implies-≐ : ∀ {A : Set} {x y : A} → x ≡ y → x ≐ y
≡-implies-≐ {A} {x} {y} x≡y P = subst P x≡y -- ok, i managaed to do one...

≐-implies-≡ : ∀ {A : Set} {x y : A} → x ≐ y → x ≡ y
≐-implies-≡ {A} {x} {y} x≐y = {!!}
  where
    Q : A → Set      -- So here we're going to define a propert
    Q z = x ≡ z       -- And this property will say that our x is equals to some z
    Qx : Q x          -- Now we will prove this propery for x
    Qx = refl         -- Which, obviously, x ≡ x
    Qy : Q y          -- Now we will show this property for y, that is x ≡ y
    Qy = x≐y Q Qx     -- So when we start the proof, the goal is to get Q y
                      -- We can get Q y from x≐y, so let's do that with a couple of holes
                      -- The first hole is the property we need, so Q
                      -- The second hole is the proof that x satisfies Q, so Qx
                      
{-
  I think we missed a trick.

  ≐ is Leibniz equality, because there's a dot above each i in Leibniz
  
  ̈= is Löf equality, because there's two dots above the ö in Löf
-}

-- UNIVERSE POLYMORPHISM
-- aaaaaaaaaaaaaaaAAAAAAAAAAAaaaaAAaaaaaAAaaaaAAaaaAAaaaaAAaaaaAaaaaAAaaaa

open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)

data _≡′_ {ℓ : Level} {A : Set ℓ} (x : A) : A → Set ℓ where -- \ell
  refl′ : x ≡′ x

sym′ : ∀ {ℓ : Level} {A : Set ℓ} {x y : A} → x ≡′ y → y ≡′ x
sym′ refl′ = refl′


_≐′_ : ∀ {ℓ : Level} {A : Set ℓ} (x y : A) → Set (lsuc ℓ)
_≐′_ {ℓ} {A} x y = ∀ (P : A → Set ℓ) → P x → P y


-- this is insane
-- but, i guess, necessary
-- i hate maths
-- bring forth the dragon

-- ye gods, it's starting to make sense

_∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
  → (B → C) → (A → B) → A → C
(g ∘ f) x  =  g (f x)
