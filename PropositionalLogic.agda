{-# OPTIONS --cubical #-}
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Functions.Logic renaming (⊥ to ⊥ₚ ; ⊤ to ⊤ₚ)

module PropositionalLogic (V : Set) where

-- Syntax 
data Term : Set where
  `_ : V → Term
  _⊃_ : Term → Term → Term
  _⋀_ : Term → Term → Term
  ⊤ₜ : Term
  ⊥ₜ : Term

infixr 6 _⸲_
data Context : Set where
  ⟨⟩ : Context
  _⸲_ : Context → Term → Context

-- Long Live Inductive Data Types!

data _∈_ : Term → Context → Set where
  here : ∀ (A : Term) → (Γ : Context) → A ∈ (Γ ⸲ A)
  there : ∀ {B : Term} → (A : Term) → (Γ : Context) → A ∈ Γ → A ∈ (Γ ⸲ B)

data _⊢_ : Context → Term → Set where
  intro-V : ∀ {Γ A} → A ∈ Γ → Γ ⊢ A
  intro-⊤ : ∀ {Γ} → Γ ⊢ ⊤ₜ
  intro-⊃ : ∀ {Γ A B} → ((Γ ⸲ A) ⊢ B) → Γ ⊢ (A ⊃ B)
  intro-⋀ : ∀ {Γ A B} → Γ ⊢ A → Γ ⊢ B → Γ ⊢ (A ⋀ B)
  elim-⊥ : ∀ {Γ A} → Γ ⊢ ⊥ₜ → Γ ⊢ A
  elim-⊃ : ∀ {Γ A B} → Γ ⊢ (A ⊃ B) → Γ ⊢ A → Γ ⊢ B
  elim-⋀ˡ : ∀ {Γ A B} → Γ ⊢ (A ⋀ B) → Γ ⊢ A
  elim-⋀ʳ : ∀ {Γ A B} → Γ ⊢ (A ⋀ B) → Γ ⊢ B

-- A is a tautology if it can be derived in the empty context
tautology : Term → Set
tautology A = ⟨⟩ ⊢ A

A∈⟨A⟩ : ∀ {A : Term} → A ∈ (⟨⟩ ⸲ A)
A∈⟨A⟩ {A} = here A ⟨⟩

⟨A⟩⊢A : ∀ {A : Term} → (⟨⟩ ⸲ A) ⊢ A
⟨A⟩⊢A {A} = intro-V (A∈⟨A⟩)

A⊃A : ∀ (A : Term) → tautology (A ⊃ A)
A⊃A A = intro-⊃ (⟨A⟩⊢A {A = A}) 

⟨A,B⟩⊢A : ∀ (A B : Term) → ((⟨⟩ ⸲ A) ⸲ B) ⊢ A
⟨A,B⟩⊢A A B = intro-V {Γ =  ((⟨⟩ ⸲ A) ⸲ B) } {A = A} (there {B = B} A (⟨⟩ ⸲ A) (A∈⟨A⟩ {A = A}))

⟨⟩,A⊢B⊃A : ∀ (A B : Term) → (⟨⟩ ⸲ A) ⊢ (B ⊃ A)
⟨⟩,A⊢B⊃A A B = intro-⊃ (⟨A,B⟩⊢A A B)

⟨⟩⊢A⊃B⊃A : ∀ (A B : Term) → (⟨⟩) ⊢ (A ⊃ (B ⊃ A))
⟨⟩⊢A⊃B⊃A A B = intro-⊃ (⟨⟩,A⊢B⊃A A B)

A⊃B⊃A-tautology : ∀ {A B : Term} → tautology (A ⊃ (B ⊃ A))
A⊃B⊃A-tautology {A} {B} = ⟨⟩⊢A⊃B⊃A A B

⊤-tautology : tautology ⊤ₜ
⊤-tautology = intro-⊤

Ω = hProp ℓ-zero

Model : Set₁
Model = V → Ω

_⊨_ : Model → Term → Ω
v ⊨ (` x) = v x
v ⊨ (x ⊃ y) = ((v ⊨ x ⇒ ⊥ₚ) ⊔ (v ⊨ y))
v ⊨ (x ⋀ y) = (v ⊨ x) ⊓ (v ⊨ y)
v ⊨ ⊤ₜ = ⊤ₚ
v ⊨ ⊥ₜ = ⊥ₚ
