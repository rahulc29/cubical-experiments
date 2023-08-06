Ceremonial imports :

```agda
{-# OPTIONS --cubical --guardedness #-}
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Data.Maybe
open import Cubical.Data.Sigma
```

Let us define streams (they are the final coalgebra of a certain functor).

```agda
record Stream (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Stream A
open Stream
```

Let us define the function that extracts even indexed elements.

```agda
evens : ∀ {A : Set} → Stream A → Stream A
head (evens x) = head x
tail (evens x) = evens (tail (tail x))
```

Similary, we construct the function that extracts odd indexed elements.

```agda
odds : ∀ {A : Set} → Stream A → Stream A
head (odds x) = head (x .tail)
tail (odds x) = odds (tail (tail x))
```

We now define bisimulation relations for streams

```agda
record _≈_ {A : Set} (x y : Stream A) : Set where
  coinductive
  field
    head-≡ : head x ≡ head y
    tail-≈ : tail x ≈ tail y
open _≈_
```

Okay, now we have a proof of coinductive extensionality!

```agda
≈→≡ : ∀ {A : Set} → ∀ {xs ys : Stream A} → xs ≈ ys → xs ≡ ys
head (≈→≡ xs≈ys i) = (head-≡ xs≈ys) i
tail (≈→≡ xs≈ys i) = ≈→≡ (tail-≈ xs≈ys) i

≡→≈ : ∀ {A : Set} → ∀ {xs ys : Stream A} → xs ≡ ys → xs ≈ ys
head-≡ (≡→≈ xs≡ys) = λ i → head (xs≡ys i)
tail-≈ (≡→≈ xs≡ys) = ≡→≈ (λ i → tail (xs≡ys i))
```

Now we must show our equation.

```agda
{-# TERMINATING #-}
evens∙tail≈odds : ∀ {A : Set} → ∀ (xs : Stream A) → evens (tail xs) ≈ odds xs
head-≡ (evens∙tail≈odds xs) = refl
tail-≈ (evens∙tail≈odds xs) = ≡→≈ ((≈→≡ (evens∙tail≈odds (tail (tail xs)))) ∙ (sym refl))

evens∙tail≡odds : ∀ {A : Set} → ∀ (xs : Stream A) → evens (tail xs) ≡ odds xs
evens∙tail≡odds xs = ≈→≡ (evens∙tail≈odds xs)
```

Now let us define the merge operation for streams. The merge operation takes the first element from the left stream and the second element from the second stream.

```agda
merge : ∀ {A : Set} → Stream A → Stream A → Stream A
head (merge x y) = x .head
tail (merge x y) = merge y (x .tail)
```

## Predicates and Temporal Logic

We define a predicate as a family of types indexed by the state space.

```agda
record Predicate (X : Set) : Set₁ where
  field
    section : X → Set
    prop : ∀ {x : X} → isProp (section x)
open Predicate
```

We define the next operator for predicates along with streams

```agda
next : ∀ {X : Set} → Predicate (Stream X) → Predicate (Stream X)
next p .section x = p .section (x .tail)
next p .prop x = p .prop {!!}
```
