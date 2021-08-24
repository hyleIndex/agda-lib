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

transport-∙-ext : ∀ {i j} {A : Type i} {x y z : A} (B : A → Type j) (p : x ≡ y) (q : y ≡ z)
                  → transport B (p ∙ q) ≡ (transport B q) ∘ (transport B p)
transport-∙-ext B refl refl = refl

coe-∙ : ∀ {i} {A B C : Type i} (p : A ≡ B) (q : B ≡ C)
        → coe (p ∙ q) ≡ coe q ∘ coe p
coe-∙ refl relf = refl

transport-≡-ap : ∀ {i j} {A : Type i} {B : Type j} {x y : A} (f g : A → B) (p : x ≡ y) (q : f x ≡ g x)
                 → transport (λ x → f x ≡ g x) p q ≡ ! ap f p ∙ q ∙ ap g p
transport-≡-ap f g refl q = ! ∙-unit-r q

transport-≡-l : ∀ {i} {A : Type i} {x y : A} (a : A) (p : x ≡ y) (q : x ≡ a)
                → transport (λ x → x ≡ a) p q ≡ ! p ∙ q
transport-≡-l a refl refl = ! ∙-inv-r refl

transport-≡-r : ∀ {i} {A : Type i} {x y : A} (a : A) (p : x ≡ y) (q : a ≡ x)
                → transport (λ x → a ≡ x) p q ≡ q ∙ p
transport-≡-r a refl refl = refl

transport-→ : ∀ {i j k} {X : Type i} (A : X → Type j) (B : X → Type k) {x y : X} (p : x ≡ y) (f : A x → B x)
              → transport (λ x → A x → B x) p f ≡ (transport B p) ∘ f ∘ (transport A (! p))
transport-→ A B refl f = refl

transport-inv : ∀ {i j} {A : Type i} {x y : A} (B : A → Type j) (p : x ≡ y) (b : B y) → transport B p (transport B (! p) b) ≡ b
transport-inv B p b = ! transport-∙ B (! p) p b ∙ ap (λ q → transport B q b) (∙-inv-l p)

transport-inv' : ∀ {i j} {A : Type i} {x y : A} (B : A → Type j) (p : x ≡ y) (b : B x) → transport B (! p) (transport B p b) ≡ b
transport-inv' B p b = ! transport-∙ B p (! p) b ∙ ap (λ q → transport B q b) (∙-inv-r p)

transport-Π : ∀ {i j k} {X : Type i} (A : X → Type j) (B : (x : X) → A x → Type k) {x y : X} (p : x ≡ y) (f : (a : A x) → B x a)
              → transport (λ x → (a : A x) → B x a) p f ≡ λ a → transport2 B p (transport-inv A p a) (f (transport A (! p) a))
transport-Π A B refl f = refl

×-ext : ∀ {i j} {A : Type i} {B : Type j} {x y : A × B} (p : fst x ≡ fst y) (q : snd x ≡ snd y) → x ≡ y
×-ext refl refl = refl

module _  {i j} {A : Type i} {B : A → Type j} where
  Σ-ext : {x y : Σ A B} (p : fst x ≡ fst y) (q : transport B p (snd x) ≡ snd y) → x ≡ y
  Σ-ext refl refl = refl

  Σ-ext-∙ : {x y z : Σ A B} → (p : fst x ≡ fst y) (p' : fst y ≡ fst z) (q : transport B p (snd x) ≡ snd y) (q' : transport B p' (snd y) ≡ snd z)
            → Σ-ext (p ∙ p') (transport-∙ B p p' (snd x) ∙ ap (transport B p') q ∙ q') ≡ Σ-ext p q ∙ Σ-ext p' q'
  Σ-ext-∙ refl refl refl refl = refl

  Σ-ext-fst : {x y : Σ A B} → (p : fst x ≡ fst y) (q : transport B p (snd x) ≡ snd y) → ap fst (Σ-ext p q) ≡ p
  Σ-ext-fst refl refl = refl

  Σ-ext-! : {x y : Σ A B} (p : fst x ≡ fst y) (q : transport B p (snd x) ≡ snd y)
            → ! (Σ-ext p q)  ≡ Σ-ext (! p) ((ap (transport B (! p)) (! q)) ∙ (transport-inv' B p (snd x))) 
  Σ-ext-! refl refl = refl

  Σ-ext-ext : {x y : Σ A B} {p p' : fst x ≡ fst y} {q : transport B p (snd x) ≡ snd y}
                                                    {q' : transport B p' (snd x) ≡ snd y}
              (P : p ≡ p') (Q : transport (λ p → transport B p (snd x) ≡ snd y) P q ≡ q')
              → Σ-ext p q ≡ Σ-ext p' q'
  Σ-ext-ext refl refl = refl

  Σ-lift : {x y : A} (b : B x) (p : x ≡ y) → (x , b) ≡ (y , transport B p b)
  Σ-lift b p = Σ-ext p refl

transport-Σ : ∀ {i j k} {X : Type i} (A : X → Type j) (B : (x : X) → A x → Type k) {x y : X} (p : x ≡ y) (u : Σ (A x) (B x))
              → transport (λ x → Σ (A x) (B x)) p u ≡ ((transport A p (fst u)) , transport2 B p refl (snd u))
transport-Σ A B refl u = refl

apd : ∀ {i j} {A : Type i} {B : A → Type j} {x y : A} (f : (x : A) → B x) (p : x ≡ y) → transport B p (f x) ≡ f y
apd f refl = refl

apd-nd : ∀ {i j} {A : Type i} {B : Type j} {x y : A} (f : A → B) (p : x ≡ y)
         → apd f p ≡ transport-cst p (f x) ∙ ap f p
apd-nd f refl = refl

apnd : ∀ {i j} {A : Type i} {B : Type j} {x y : A} (f : A → B) (p : x ≡ y)
       → ap f p ≡ ! transport-cst p (f x) ∙ apd f p
apnd f refl = refl

ap-transport-cst : ∀ {i j k} {A : Type i} {x y : A} {B : Type j} {B' : Type k} (f : B → B') (p : x ≡ y) (b : B)
                   → ap f (transport-cst p b) ≡ ! transport-nat (λ _ → B) (λ _ → B') f p b ∙ transport-cst p (f b)
ap-transport-cst f refl b = refl
