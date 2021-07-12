{-# OPTIONS --without-K --allow-unsolved-metas --rewriting #-}

module HoTT.Path.proposition where

open import HoTT.core
open import HoTT.type
open import HoTT.function
open import HoTT.Path.core

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

funextinv-ap : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} {f f' : A → B}
               → (g : B → C) → (p : f ≡ f') → (x : A)
               → funext-inv (ap (λ f → g ∘ f) p) x ≡ ap g (funext-inv p x)
funextinv-ap g refl x = refl

funextinv-ap' : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} {g g' : B → C}
               → (f : A → B) → (p : g ≡ g') → (x : A)
               → funext-inv (ap (λ g → g ∘ f) p) x ≡ funext-inv p (f x)
funextinv-ap' g refl x = refl

transport-cst : ∀ {i j} {A : Type i} {B : Type j} {x y : A} (p : x ≡ y) (b : B)
                → transport (const B) p b ≡ b
transport-cst refl b = refl

transport-ap : ∀ {i i' j} {A : Type i} {A' : Type i'} {x y : A} (B : A' → Type j) (f : A → A') (p : x ≡ y) (b : B (f x))
               → transport (B ∘ f) p b ≡ transport B (ap f p) b
transport-ap B f refl b = refl

transport-ap-ext : ∀ {i i' j} {A : Type i} {A' : Type i'} {x y : A} (B : A' → Type j) (f : A → A') (p : x ≡ y)
                   → transport (B ∘ f) p ≡ transport B (ap f p)
transport-ap-ext B f refl = refl

transport-nat : ∀ {i j k} {A : Type i} {a a' : A} (B : A → Type j) (B' : A → Type k) (f : {a : A} → B a → B' a) (p : a ≡ a') (x : B a)
                → transport B' p (f x) ≡ f (transport B p x)
transport-nat B B' f refl x = refl

coe-ap : ∀ {i j} {A : Type i} {x y : A} (B : A → Type j) (p : x ≡ y)
         → coe (ap B p) ≡ transport B p
coe-ap B refl = refl

coe-injective : ∀ {i} {A B : Type i} (p : A ≡ B) {x y : A}
                → coe p x ≡ coe p y → x ≡ y
coe-injective refl q = q

transport-arg : ∀ {i j} {A A' : Type i} {B : Type j} (p : A ≡ A') (f : A → B)
                → transport (λ A → A → B) p f ≡ λ x → f (coe (sym p) x)
transport-arg refl f = refl

!-! : ∀ {i} {A : Type i} {x y : A} (p : x ≡ y)
      → ! ! p ≡ p
!-! refl = refl

∙-unit-l : ∀ {i} {A : Type i} {x y : A} (p : x ≡ y)
           → refl ∙ p ≡ p
∙-unit-l p = refl

∙-unit-r : ∀ {i} {A : Type i} {x y : A} (p : x ≡ y)
           → p ∙ refl ≡ p
∙-unit-r refl = refl

∙-inv-l : ∀ {i} {A : Type i} {x y : A} (p : x ≡ y)
          → ! p ∙ p ≡ refl
∙-inv-l refl = refl

∙-inv-r : ∀ {i} {A : Type i} {x y : A} (p : x ≡ y)
          → p ∙ ! p ≡ refl
∙-inv-r refl = refl

∙-sym : ∀ {i} {A : Type i} {x y z : A} (p : x ≡ y) (q : y ≡ z)
        → ! (p ∙ q) ≡ ! q ∙ ! p
∙-sym p refl = ap sym (∙-unit-r p)

∙-assoc : ∀ {i} {A : Type i} {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
          → (p ∙ q) ∙ r ≡ p ∙ q ∙ r
∙-assoc refl q r = refl

ap-∙ : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) {x y z : A} (p : x ≡ y) (q : y ≡ z)
       → ap f (p ∙ q) ≡ ap f p ∙ ap f q
ap-∙ f refl q = refl

ap-! : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) {x y : A} (p : x ≡ y)
       → ap f (! p) ≡ (! ap f p)
ap-! f refl = refl

coe-∙! : ∀ {i} {A B : Type i} (e : A ≡ B) (x : B)
         → (coe e (coe (! e) x) ≡ x)
coe-∙! refl x = refl

coe-!∙ : ∀ {i} {A B : Type i} (p : B ≡ A) (x : B)
         → coe (! p) (coe p x) ≡ x
coe-!∙ refl x = refl

sym-ap : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) {x y : A} (p : x ≡ y)
         → sym (ap f p) ≡ ap f (sym p)
sym-ap f refl = refl

transport-∙ : ∀ {i j} {A : Type i} {x y z : A} (B : A → Type j) (p : x ≡ y) (q : y ≡ z) (b : B x)
              → transport B (p ∙ q) b ≡ transport B q (transport B p b)
transport-∙ B refl refl b = refl
