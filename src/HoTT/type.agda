{-# OPTIONS --without-K --rewriting #-}

module HoTT.type where

open import HoTT.core

Type : ∀ i → Set (lsuc i)
Type i = Set i

Type₀ = Set
Type₁ = Set₁

∏ : ∀ {i j} (A : Type i) (B : A → Type j) → Type (lmax i j)
∏ A B = (a : A) → B a

J : ∀ {i j} {A : Type i} (P : (x y : A) → x ≡ y → Type j)
    → ((x : A) → P x x refl) → {x y : A} (p : x ≡ y) → P x y p
J P b {x = x} refl = b x
