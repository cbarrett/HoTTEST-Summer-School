# Week 02 - Agda Exercises

## Please read before starting the exercises

**The exercises are designed to increase in difficulty so that we can cater to
our large and diverse audience. This also means that it is *perfectly fine* if
you don't manage to do all exercises: some of them are definitely a bit hard for
beginners and there are likely too many exercises! You *may* wish to come back
to them later when you have learned more.**

Having said that, here we go!

This is a markdown file with Agda code, which means that it displays nicely on
GitHub, but at the same time you can load this file in Agda and fill the holes
to solve exercises.

**Please make a copy of this file to work in, so that it doesn't get overwritten
  (in case we update the exercises through `git`)!**

```agda
{-# OPTIONS --without-K --allow-unsolved-metas #-}

module 02-Exercises where

open import prelude
open import decidability
open import sums
```

## Part I: Propositions as types


### Exercise 1 (★)

Prove
```agda
uncurry : {A B X : Type} → (A → B → X) → (A × B → X)
uncurry f = λ x → f (pr₁ x) (pr₂ x)

curry : {A B X : Type} → (A × B → X) → (A → B → X)
curry f = λ x y → f (x , y)
```
You might know these functions from programming e.g. in Haskell.
But what do they say under the propositions-as-types interpretation?

A: It's the famous tensor-hom adjunction. Or, in propositions-as-types, it says that
assuming A, and then assuming B, we can prove X is the same as assuming A and B,
in the first place, we can prove X, and vice versa.

### Exercise 2 (★)

Consider the following goals:
```agda
[i] : {A B C : Type} → (A × B) ∔ C → (A ∔ C) × (B ∔ C)
[i] (inl (a , b)) = (inl a , inl b)
[i] (inr c) = (inr c , inr c)

[ii] : {A B C : Type} → (A ∔ B) × C → (A × C) ∔ (B × C)
[ii] (inl a , c) = inl (a , c)
[ii] (inr b , c) = inr (b , c)

[iii] : {A B : Type} → ¬ (A ∔ B) → ¬ A × ¬ B
[iii] n = (λ ha → n (inl ha)) , (λ hb → n (inr hb))

[iv] : {A B : Type} → ¬ (A × B) → ¬ A ∔ ¬ B
[iv] = {!!}
-- Not possible, we don't know which element of the coproduct to give.
-- Logically, this means A ^ B implies false does not imply A implies false,
-- or B implies false, which does seems reasonable, thinking constructively.

[v] : {A B : Type} → (A → B) → ¬ B → ¬ A
[v] f nb = λ ha → nb (f ha)

[vi] : {A B : Type} → (¬ A → ¬ B) → B → A
[vi] = {!!}
-- Not possible, we only have the assumptions that, if you can prove A implies false,
-- that you can derive B implies false, and the simple assumption of B. Crucially,
-- we don't have any way to get an A.

[vii] : {A B : Type} → ((A → B) → A) → A
[vii] = {!!}
-- Not possible. We are never given an A, we only have f, which needs us to give it
-- an A implies B. But we have no way to construct such a term, as there is no way
-- to get a B from an A given the information we have.

[viii] : {A : Type} {B : A → Type}
    → ¬ (Σ a ꞉ A , B a) → (a : A) → ¬ B a
[viii] n a = λ hb → n (a , hb)

[ix] : {A : Type} {B : A → Type}
    → ¬ ((a : A) → B a) → (Σ a ꞉ A , ¬ B a)
[ix] n = {!!}
-- Not possible. Just because we know that "forall a, B of a" implies false, that does
-- not give us any way to find out which `a` (of possibly many) is "the" `a` that fails.

[x] : {A B : Type} {C : A → B → Type}
      → ((a : A) → (Σ b ꞉ B , C a b))
      → Σ f ꞉ (A → B) , ((a : A) → C a (f a))
[x] f = (λ a → pr₁ (f a)) , λ a → pr₂ (f a)
```
For each goal determine whether it is provable or not.
If it is, fill it. If not, explain why it shouldn't be possible.
Propositions-as-types might help.


### Exercise 3 (★★)

```agda
¬¬_ : Type → Type
¬¬ A = ¬ (¬ A)

¬¬¬ : Type → Type
¬¬¬ A = ¬ (¬¬ A)
```
In the lecture we have discussed that we can't  prove `∀ {A : Type} → ¬¬ A → A`.
What you can prove however, is
```agda
tne : ∀ {A : Type} → ¬¬¬ A → ¬ A
tne nnna = λ ha → nnna λ hna → hna ha
```


### Exercise 4 (★★★)
Prove
```agda
¬¬-functor : {A B : Type} → (A → B) → ¬¬ A → ¬¬ B
¬¬-functor = {!!}

¬¬-kleisli : {A B : Type} → (A → ¬¬ B) → ¬¬ A → ¬¬ B
¬¬-kleisli = {!!}
```
Hint: For the second goal use `tne` from the previous exercise





## Part II: `_≡_` for `Bool`

**In this exercise we want to investigate what equality of booleans looks like.
In particular we want to show that for `true false : Bool` we have `true ≢ false`.**

### Exercise 1 (★)

Under the propositions-as-types paradigm, an inhabited type corresponds
to a true proposition while an uninhabited type corresponds to a false proposition.
With this in mind construct a family
```agda
bool-as-type : Bool → Type
bool-as-type true = 𝟙
bool-as-type false = 𝟘
```
such that `bool-as-type true` corresponds to "true" and
`bool-as-type false` corresponds to "false". (Hint:
we have seen canonical types corresponding true and false in the lectures)


### Exercise 2 (★★)

Prove
```agda
bool-≡-char₁ : ∀ (b b' : Bool) → b ≡ b' → (bool-as-type b ⇔ bool-as-type b')
bool-≡-char₁ b .b (refl .b) = id , id
```


### Exercise 3 (★★)

Using ex. 2, concldude that
```agda
true≢false : ¬ (true ≡ false)
true≢false hp = (pr₁ (bool-≡-char₁ true false hp) ⋆)
```

You can actually prove this much easier! How?

```agda
-- Using Agda's syntax for pattern matching to discharge a contradiction
true≢false' : ¬ (true ≡ false)
true≢false' ()
```

### Exercise 4 (★★★)

Finish our characterisation of `_≡_` by proving
```agda
bool-≡-char₂ : ∀ (b b' : Bool) → (bool-as-type b ⇔ bool-as-type b') → b ≡ b'
bool-≡-char₂ = {!!}
```


## Part III (🌶)
A type `A` is called *discrete* if it has decidable equality.
Consider the following predicate on types:
```agda
has-bool-dec-fct : Type → Type
has-bool-dec-fct A = Σ f ꞉ (A → A → Bool) , (∀ x y → x ≡ y ⇔ (f x y) ≡ true)
```
Prove that
```agda
decidable-equality-char : (A : Type) → has-decidable-equality A ⇔ has-bool-dec-fct A
decidable-equality-char = {!!}
```
