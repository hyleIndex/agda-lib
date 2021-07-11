{-# OPTIONS --without-K --rewriting #-}

module HoTT.core where

open import Agda.Primitive renaming (_⊔_ to lmax) public
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; trans ; module ≡-Reasoning) public
open import Function using (case_of_) public
open import Data.Unit using (⊤ ; tt) public
open import Data.Empty public
open import Relation.Nullary using (¬_) public
open import Data.Product using (_×_ ; Σ ; _,_) renaming (proj₁ to fst ; proj₂ to snd) public
open import Data.Sum renaming (_⊎_ to _⊔_ ; inj₁ to inl ; inj₂ to inr) public

{-# BUILTIN REWRITE _≡_ #-}
