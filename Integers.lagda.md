Imports are necessary obviously!

```agda
{-# OPTIONS --cubical #-}

open import Cubical.Core.Everything
```

Let's make the goddamned integers!

```agda
data ℤ : Set where
  zero : ℤ
  succ : ℤ → ℤ
  pred : ℤ → ℤ
  succ∙pred≡id : ∀ {z : ℤ} → succ (pred z) ≡ z
  pred∙succ≡id : ∀ {z : ℤ} → pred (succ z) ≡ z
```

Let us define addition using the old properties of associativity : `a + (b + 1) = (a + b) + 1`

```agda
_+_ : ℤ → ℤ → ℤ
zero + n = n
(succ n) + m = succ (n + m)
(pred n) + m = n + m
```
