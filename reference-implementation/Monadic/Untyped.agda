
module Monadic.Untyped where

open import Data.Nat using (ℕ; zero; suc; 2+)
open import Data.Fin using (Fin; zero; suc; #_)
open import Core.Untyped using (Term; var; lam; _·_; Π; U; N; zero; suc)

--------------------------------------------------------------------------------
-- * Syntax

mutual 
  data Value (n : ℕ) : Set where
    var  : (x : Fin n) → Value n
    lam  : Computation (suc n) → Value n
    Π    : Value n → Value (suc n) → Value n
    U    : (l : ℕ) → Value n

    -- Base terms
    N    : Value n
    zero : Value n

  infixl 5 _·_ 
  infixr 4 _⨟_ 

  data Computation (n : ℕ) : Set where
    suc  : Value n → Computation n
    _·_  : Value n → Value n → Computation n
    val  : Value n → Computation n
    _⨟_  : Computation n → Computation (suc n) → Computation n

--------------------------------------------------------------------------------
-- * Weakening

data Wk : ℕ → ℕ → Set where
  i : ∀ {m} → Wk m m
  ↑_       : ∀ {m n} → Wk m n → Wk (suc m) n
  ⇑_       : ∀ {m n} → Wk m n → Wk (suc m) (suc n)

infixl 5 _∙_ 

_∙_ : ∀ {l m n} (η : Wk l m) (η₁ : Wk m n) → Wk l n
i     ∙ η₁     = η₁
(↑ η) ∙ η₁     = ↑ (η ∙ η₁)
(⇑ η) ∙ i      = ⇑ η
(⇑ η) ∙ (↑ η₁) = ↑ (η ∙ η₁)
(⇑ η) ∙ (⇑ η₁) = ⇑ (η ∙ η₁)

wkVar : {m n : ℕ} (η : Wk m n) (x : Fin n) → Fin m
wkVar i     x       = x
wkVar (↑ η) x       = suc (wkVar η x)
wkVar (⇑ η) zero    = zero
wkVar (⇑ η) (suc x) = suc (wkVar η x)

mutual
  wkᵛ : ∀ {m n} (η : Wk m n) (v : Value n) → Value m
  wkᵛ η (var x)  = var (wkVar η x)
  wkᵛ η (lam t)  = lam (wkᶜ (⇑ η) t)
  wkᵛ η (Π v v₁) = Π (wkᵛ η v) (wkᵛ (⇑ η) v₁)
  wkᵛ η (U l)    = U l
  wkᵛ η N        = N
  wkᵛ η zero     = zero

  wkᶜ : ∀ {m n} (η : Wk m n) (t : Computation n) → Computation m
  wkᶜ η (v · v₁) = wkᵛ η v · wkᵛ η v₁
  wkᶜ η (suc v)  = suc (wkᵛ η v)
  wkᶜ η (val v)  = val (wkᵛ η v)
  wkᶜ η (t ⨟ t₁) = wkᶜ η t ⨟ wkᶜ (⇑ η) t₁

--------------------------------------------------------------------------------
-- * Substitution

-- TODO

--------------------------------------------------------------------------------
-- * Core to Monadic translation

fromCore : ∀ {n} → Term n → Computation n
fromCore (var x)  = val (var x)
fromCore (lam t)  = val (lam (fromCore t))
fromCore (t · t₁) = fromCore t ⨟ wkᶜ (↑ i) (fromCore t₁) ⨟ var (# 1) · var (# 0)
fromCore (Π t t₁) = fromCore t ⨟ fromCore t₁ ⨟ val (Π (var (# 1)) (var (# 0))) -- Maybe wrong (need to substitute)
fromCore (U l)    = val (U l)
fromCore N        = val N
fromCore zero     = val zero
fromCore (suc t)  = fromCore t ⨟ suc (var (# 0))
