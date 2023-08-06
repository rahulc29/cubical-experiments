Ceremonial imports :

```agda
{-# OPTIONS --cubical #-}
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
```

How do we model finality? Do we use `X → Bool`? Booleans are not always the best, but in this case, I think they'll be good.

Before anything, we need the syntax of the λ calculus:

```agda
module CEKMachines (V : Set) where

data Lambda : Set
data Term : Set
data Lambda where
  ƛ_⇒_ : V → Term → Lambda
data Term where
  `_ : V → Term
  Λ_ : Lambda → Term
  _*_ : Term → Term → Term
```

An environment is a function from the set `V` into the denotable values.

```agda
Environment : Set
data Denotable : Set
Environment = V → Denotable
data Denotable where
  closure : Lambda → Environment → Denotable
data Continuation : Set where
  finished : Continuation
  argument : Term → Environment → Continuation → Continuation
  function : Lambda → Environment → Continuation → Continuation
```

Continuations are of three kinds - we have finished evaluating, we have to evaluate an argument, we need to evaluate a function.

Now, onto the state space!

```agda
record MachineState : Set where
  constructor ⟨_,_,_⟩ 
  field
    term : Term
    environment : Environment
    continuation : Continuation
open MachineState
```

State transition function time!

```agda
step : MachineState → MachineState
step ⟨ ` x , ρ , κ ⟩ = ⟨ Λ (closure→ƛ (ρ x)) , closure→ρ' (ρ x) , κ ⟩
                      where
                        closure→ƛ : Denotable → Lambda 
                        closure→ƛ (closure lam _) = lam
                        closure→ρ' : Denotable → Environment
                        closure→ρ' (closure _ ρ') = ρ' 
step ⟨ (f * e) , ρ , κ ⟩ = ⟨ f , ρ , argument e ρ κ ⟩
step ⟨ Λ lam , ρ , (argument e ρ' κ) ⟩ = ⟨ e , ρ' , function lam ρ κ ⟩
step ⟨ Λ lam , ρ , (function (ƛ x ⇒ e) ρ' κ) ⟩ = ⟨ e , {!!} , {!!} ⟩ 
```
