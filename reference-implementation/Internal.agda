{-# OPTIONS --erasure #-}

module Internal where

open import Data.Nat using (ℕ; zero; suc; _⊔_)
open import Function using (_∘_; _∘′_)
open import Relation.Binary.PropositionalEquality using (subst; subst₂; cong; cong₂; sym; _≡_; trans; refl; module ≡-Reasoning)
open ≡-Reasoning
open import Data.Product using (Σ; Σ-syntax; ∃; ∃-syntax; _,_; proj₁; proj₂; <_,_>; map₂)

data Scope : Set

data Term (@0 Γ : Scope) : Set

Typ = Term


private variable
  m n     : ℕ
  l l₁    : ℕ
  Γ Δ α β γ : Scope
  t t′ t₁ t₂ : Term Γ 
  A B C   : Typ Γ


infixl 6 _▹_

data Scope where
  ∅   : Scope
  _▹_ : (Γ : Scope) (A : Typ Γ) → Scope

foldl : {B : Set} → (∀ {Γ} → B → (A : Typ Γ) → B) → B → Scope → B
foldl c n ∅       = n
foldl c n (α ▹ A) = c (foldl c n α) A

data _∈_ : {@0 Γ : Scope} → @0 Typ Γ → @0 Scope → Set where
  here  : A ∈ (Γ ▹ A)
  there : A ∈ Γ → A ∈ (Γ ▹ B)

infix 30 U_

data Term Γ where
  -- Types
  U_   : (l : ℕ) → Typ Γ
  Π    : (A : Typ Γ) (B : Typ (Γ ▹ A)) → Typ Γ
  -- _≣_  : (t t₁ : Term Γ) → Typ Γ
  Nat  : Typ Γ

  -- Values
  lam  : (A : Typ Γ) (t : Term (Γ ▹ A)) → Term Γ
  app  : (t t₁ : Term Γ) → Term Γ
  var  : (p : A ∈ Γ) → Term Γ
  -- refl : Term Γ
  lit  : (n : ℕ) → Term Γ


infix 5 _⊆_

data _⊆_ : @0 Scope → @0 Scope → Set
wk : (η : α ⊆ β) (t : Term α) → Term β

data _⊆_ where
  identity : α ⊆ α
  ↑_       : {B : Typ β} (η : α ⊆ β) → α ⊆ (β ▹ B)
  ⇑_       : {A : Typ α} (η : α ⊆ β) → (α ▹ A) ⊆ (β ▹ wk η A)

pattern ↑id = ↑ identity

wk∈ : {A : Typ Γ} (η : α ⊆ β) (p : A ∈ α) → ∃[ Δ ] Σ[ B ∈ Term Δ ] B ∈ β
wk∈ identity p         = _ , _ , p
wk∈ (↑ η)    here      = _ , _ , here
wk∈ (↑ η)    (there p) = map₂ (map₂ there) (wk∈ η (there p))
wk∈ (⇑ η)    here      = _ , _ , here
wk∈ (⇑ η)    (there p) = map₂ (map₂ there) (wk∈ η (p))


-- wk identity t        = t  -- make explicit proof instead
wk η (U l)           = U l
wk η (Π A B)         = Π (wk η A) (wk (⇑ η) B)
wk η Nat             = Nat
wk η (lam A t)       = lam (wk η A) (wk (⇑ η) t)
wk η (app t t₁)      = app (wk η t) (wk η t₁)
wk η (var {A = A} p) = var (proj₂ (proj₂ (wk∈ η p)))
wk η (lit n)         = lit n

mutual
  infixr 9 _∙_

  _∙_ : ∀ {α β} → β ⊆ γ → α ⊆ β → α ⊆ γ
  identity ∙ η₁       = η₁
  (↑ η)    ∙ η₁       = ↑ (η ∙ η₁)
  (⇑ η)    ∙ identity = ⇑ η
  (⇑ η)    ∙ (↑ η₁)   = ↑ (η ∙ η₁)
  (⇑ η)    ∙ (⇑ η₁)   = 
    subst (λ B → _ ▹ _ ⊆ _ ▹ B) (sym (wk-comp η η₁)) 
    (⇑ (η ∙ η₁))

  ∙-identityₗ : (η : α ⊆ β) → identity ∙ η ≡ η
  ∙-identityₗ _ = refl
  
  ∙-identityᵣ : (η : α ⊆ β) → η ∙ identity ≡ η
  ∙-identityᵣ identity = refl
  ∙-identityᵣ (↑ η)    = cong ↑_ (∙-identityᵣ  η)
  ∙-identityᵣ (⇑ η)    = refl

  wk-comp : (η : β ⊆ γ) (η₁ : α ⊆ β) → wk η (wk η₁ t) ≡ wk (η ∙ η₁) t
  wk-comp identity η₁ = {! !}
  wk-comp (↑ η) η₁ = {! !}
  wk-comp (⇑ η) η₁ = {! !}

∅⊆α : ∅ ⊆ α
∅⊆α {∅} = identity
∅⊆α {α ▹ A} = ↑ ∅⊆α

mutual 
  _◃_ : Term ∅ → Scope → Scope
  A ◃ ∅ = ∅ ▹ A
  A ◃ (α ▹ B) = (A ◃ α) ▹ wk ↓id B

  ↓id : α ⊆ (A ◃ α)
  ↓id {α = ∅}     = ↑ identity
  ↓id {α = α ▹ B} = ⇑ ↓id

mutual 
  infixl 5 _++_

  _++_ : Scope → Scope → Scope
  α ++ ∅ = α
  α ++ (β ▹ A) = (α ++ β) ▹ wk ↡id A

  ↡id : α ⊆ (β ++ α)
  ↡id {α = ∅} = ∅⊆α
  ↡id {α = α ▹ A} {β = β} = ⇑ ↡id 

↟_ : (η : α ⊆ β) → α ⊆ (β ++ γ)
↟_ {γ = ∅} η = η
↟_ {γ = γ ▹ C} η = ↑ (↟ η)

↟id : α ⊆ (α ++ β)
↟id = ↟ identity

_⇒_ : Scope → Scope → Set
α ⇒ β = ∀ {Γ} {A : Term Γ} → A ∈ α → Term β

⇒id : α ⇒ α 
⇒id = var

⇒cons : {A : Term Γ} (t : Term Γ) (σ : Γ ⇒ Δ) → (Γ ▹ A) ⇒ Δ
⇒cons {Γ = ∅} t σ here = wk ∅⊆α t
⇒cons {Γ = Γ ▹ A} t σ here = σ here
⇒cons t σ (there p) = σ p

⇒singleton : {A : Typ Γ} (t : Term Γ) → (Γ ▹ A) ⇒ Γ
⇒singleton t = ⇒cons t ⇒id

⇒lift : (σ : α ⇒ β) → (α ▹ A) ⇒ (β ▹ B)
⇒lift {B = B} σ here = var here
⇒lift σ (there p) = wk ↑id (σ p) 

_[_] : (t : Term Γ) (σ : Γ ⇒ Δ) → Term Δ
(U l)    [ σ ] = U l
Π A B    [ σ ] = Π (A [ σ ]) (B [ ⇒lift σ ])
Nat      [ σ ] = Nat
lam A t  [ σ ] = lam (A [ σ ]) (t [ ⇒lift σ ])
app t t₁ [ σ ] = app (t [ σ ]) (t [ σ ])
var p    [ σ ] = σ p
lit n    [ σ ] = lit n

_[_]₀ : {A : Typ Γ} (B : Typ (Γ ▹ A)) (t : Term Γ) → Typ Γ
B [ t ]₀ = B [ ⇒singleton t ]

U₀ U₁ : Term Γ
U₀ = U 0
U₁ = U 1

infixr 5 _⟶_

_⟶_ : (A B : Term Γ) → Term Γ
A ⟶ B = Π A (wk ↑id B)

-- Example
type-id : Term ∅
type-id = Π U₀ (var here ⟶ var here)

term-id : Term ∅
term-id = lam U₀ (lam (var here) (var here))

data _⊢_∈_ (Γ : Scope) : Term Γ → Term Γ → Set 
data _⊢_≅_∈_ (Γ : Scope) : Term Γ → Term Γ → Term Γ → Set

data _⊢_∈_ Γ where
  -- Types
  ty-universe
    ---------------------
    : Γ ⊢ U l ∈ U (suc n)

  {-
  ty-equality-types 
    : (let Uₗ = U l)
    → Γ ⊢ A ∈ Uₗ 
    → Γ ⊢ B ∈ Uₗ
    ----------------
    → Γ ⊢ A ≣ B ∈ Uₗ
  -}

  ty-nat 
    --------------
    : Γ ⊢ Nat ∈ U₀

  ty-pi
    : Γ ⊢ A ∈ U l
    → (Γ ▹ A) ⊢ B ∈ U l₁
    -----------------------
    → Γ ⊢ Π A B ∈ U (l ⊔ l₁)

  -- Values

  ty-lam 
    : (Γ ▹ A) ⊢ t ∈ B
    ---------------------
    → Γ ⊢ lam A t ∈ Π A B

  ty-var
    : (p : A ∈ Γ)
    ---------------
    → Γ ⊢ var p ∈ A

  ty-app
    : Γ ⊢ t  ∈ Π A B
    → Γ ⊢ t₁ ∈ A
    ----------------
    → Γ ⊢ app t t₁ ∈ (B [ t₁ ]₀)

  {-
  ty-refl 
    : Γ ⊢ t ∈ A
    --------------------
    → Γ ⊢ refl ∈ (t ≣ t)
  -}

  ty-lit
    ---------------
    : Γ ⊢ lit n ∈ Nat

  -- Conversion

  ty-conversion
    : Γ ⊢ t ∈ A
    → Γ ⊢ A ≅ B ∈ U l
    -----------------
    → Γ ⊢ t ∈ B


data _⊢_≅_∈_ Γ where
  conv-refl
    : Γ ⊢ t ∈ A
    -----------
    → Γ ⊢ t ≅ t ∈ A
  conv-sym
    : Γ ⊢ t ≅ t₁ ∈ A
    ----------------
    → Γ ⊢ t₁ ≅ t ∈ A

  conv-trans
    : Γ ⊢ t  ≅ t₁ ∈ A
    → Γ ⊢ t₁ ≅ t₂ ∈ A
    ----------------
    → Γ ⊢ t  ≅ t₂ ∈ A

  conv-type 
    : Γ ⊢ t ≅ t₁ ∈ A
    → Γ ⊢ A ≅ B  ∈ U l
    -----------------
    → Γ ⊢ t ≅ t₁ ∈ B

 -- TODO: rest
