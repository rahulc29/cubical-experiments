{-# OPTIONS --cubical #-}

module TemporalLogic (P : Set) where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Functions.Logic
open import Cubical.Relation.Nullary
open import Cubical.Data.Nat

data Term : Set where
  ⊥ₜ : Term
  `_ : P → Term
  _⭆_ : Term → Term → Term
  ○_ : Term → Term

infixr 10 _⭆_

-- Subobject classifier
Ω = hProp ℓ-zero

_∈_ : P → (P → Ω) → Ω
p ∈ Α = Α p

Α : Set₁
Α = ℕ → (P → Ω)

_⊨_ : Α → Term → Ω
α ⊨ ⊥ₜ = ⊥
α ⊨ (` p) = p ∈ (α zero)
α ⊨ (ϕ ⭆ ψ) = ((α ⊨ ϕ) ⇒ ⊥) ⊔ (α ⊨ ψ)
α ⊨ (○ x) = (λ x → α (suc x)) ⊨ x

