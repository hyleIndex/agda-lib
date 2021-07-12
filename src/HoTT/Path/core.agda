{-# OPTIONS --without-K --allow-unsolved-metas --rewriting #-}

module HoTT.Path.core where

open import HoTT.core
open import HoTT.type
open import HoTT.function

ap : ∀ {i j} {A : Type i} {B : Type j} {x y : A} (f : A → B)
     → (x ≡ y) → (f x ≡ f y)
ap f refl = refl

infixl 40 ap
syntax ap f p = p |in-ctx f

transport : ∀ {i j} {A : Type i} {x y : A} (B : A → Type j)
            → (x ≡ y)
            → (B x → B y)
transport B refl b = b

coe : ∀ {i} {A B : Type i}
      → A ≡ B
      → A → B
coe refl a = a

infixr 80 _∙_

_∙_ : ∀ {i} {A : Type i} {x y z : A} (p : x ≡ y) (q : y ≡ z) → x ≡ z
_∙_ = trans

infix 100 !_

!_ : ∀ {i} {A : Type i} {x y : A} (p : x ≡ y) → y ≡ x
!_ = sym
