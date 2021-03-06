{-# OPTIONS --without-K --rewriting #-}

module HoTT.function where

open import HoTT.type
open import HoTT.core

_∘_ : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k}
      → (B → C) → (A → B) → (A → C)
g ∘ f = λ x → g (f x)

infixr 20 _∘_

id : ∀ {i} {A : Type i} → A → A
id x = x

_∘'_ : ∀ {i j k}
      {A : Type i} {B : A → Type j} {C : {x : A} → B x → Type k} →
      (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
      ((x : A) → C (g x))
f ∘' g = λ x → f (g x)

infixr 9 _∘'_

const : ∀ {i j} {A : Type i} {B : Type j} → A → B → A
const x = λ _ → x

Extensionality : ∀ i j → Type (lmax (lsuc i) (lsuc j))
Extensionality i j = {X : Type i} {Y : Type j}
                     → {f g : X → Y}
                     → ((x : X) → f x ≡ g x)
                     → f ≡ g

Extensionality' : ∀ i j → Type (lmax (lsuc i) (lsuc j))
Extensionality' i j = {X : Type i} {Y : X → Type j}
                      → {f g : (x : X) → (Y x)}
                      → ((x : X) → f x ≡ g x)
                      → f ≡ g

StrongExt : ∀ i j → Type (lmax (lsuc i) (lsuc j))
StrongExt i j = {X : Type i} {Y : X → Type j}
                →  {f g : (x : X) → (Y x)}
                → (∀ x → f x ≡ g x) ≡ (f ≡ g)

funext-inv : ∀ {i j} {X : Type i} {Y : X → Type j}
             → {f g : (x : X) → (Y x)}
             → (f ≡ g)
             → (∀ x → f x ≡ g x)
funext-inv refl x = refl
