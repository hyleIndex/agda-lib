{-# OPTIONS --without-K --allow-unsolved-metas --rewriting #-}

module HoTT.path where

open import HoTT.core
open import HoTT.type
open import HoTT.function

ap : ∀ {i j} {A : Type i} {B : Type j} {x y : A} (f : A → B)
     → (x ≡ y) → (f x ≡ f y)
ap f refl = refl

infixl 40 ap
syntax ap f p = p |in-ctx f

ap-id : ∀ {i} {A : Type i} {x y : A} (p : x ≡ y) → ap id p ≡ p
ap-id refl = refl

ap-cst : ∀ {i j} {A : Type i} {B : Type j} {x y : A} (b : B) (p : x ≡ y)
         → ap (const b) p ≡ refl
ap-cst b refl = refl

ap-∘ : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k}
      (g : B → C) (f : A → B)
      {x y : A} (p : x ≡ y)
      → ap (g ∘ f) p ≡ ap g (ap f p)
ap-∘ g f refl = refl

