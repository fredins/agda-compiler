
module Internal where

open import Data.Product using (_×_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.String using (String)

module Scope where

  infixl 5 _▹_

  data Scope (A : Set) : Set where
    ∅   : Scope A
    _▹_ : (α : Scope A) (x : A) → Scope A

  _++_ : ∀ {A} (α β : Scope A) → Scope A
  α ++ ∅ = α
  α ++ (β ▹ x) = (α ++ β) ▹ x


module Thinning where

  open Scope using (Scope; ∅; _▹_)

  private variable
    A : Set
    α α₁ β β₁ : Scope A

  infix 4 _⊆_

  data _⊆_ {A : Set} : Scope A → Scope A → Set where
    base  : ∅ ⊆ ∅
    _keep_ : ∀ (φ : α ⊆ β) x → α ▹ x ⊆ β ▹ x
    _drop_ : ∀ (φ : α ⊆ β) x → α ⊆ β ▹ x

  ⊆-syntax : (A : Set) → Scope A → Scope A → Set
  ⊆-syntax A = _⊆_ {A = A} 
  
  syntax ⊆-syntax A α β = α ⊆[ A ] β

  _++_ : (φ : α ⊆ β) (ψ : α₁ ⊆ β₁) → (α Scope.++ α₁) ⊆ (β Scope.++ β₁)
  φ ++ base = φ
  φ ++ (ψ keep x) = (φ ++ ψ) keep x
  φ ++ (ψ drop x) = (φ ++ ψ) drop x


module Cover where

  open Scope using (Scope; ∅; _▹_)
  open Thinning using (_⊆_; ⊆-syntax; base; _keep_; _drop_) public 

  private variable
    A : Set
    α α₁ β β₁ γ γ₁ : Scope A
    φ φ₁ ψ ψ₁ : α ⊆ β

  infixl 5 _left_ _right_ _both_

  data Cover {A : Set} : α ⊆[ A ] γ → β ⊆[ A ] γ → Set where
    base  : Cover base base
    _left_  : ∀ (c : Cover φ ψ) x → Cover (φ keep x) (ψ drop x)  
    _right_ : ∀ (c : Cover φ ψ) x → Cover (φ drop x) (ψ keep x) 
    _both_  : ∀ (c : Cover φ ψ) x → Cover (φ keep x) (ψ keep x) 


  _++_ : (c : Cover φ ψ) (c₁ : Cover φ₁ ψ₁) → Cover (φ Thinning.++ φ₁) (ψ Thinning.++ ψ₁)
  c ++ base = c
  c ++ (c₁ left x) = (c ++ c₁) left x
  c ++ (c₁ right x) = (c ++ c₁) right x
  c ++ (c₁ both x) = (c ++ c₁) both x

  record _⊗_ {A : Set} (F G : Scope A → Set) (α : Scope A) : Set where
      constructor _⟨_⟩_
      field
        {fvₗ} : Scope A
        {fvᵣ} : Scope A
        {thₗ} : fvₗ ⊆ α
        {thᵣ} : fvᵣ ⊆ α
        outl  : F fvₗ
        cover : Cover thₗ thᵣ
        outr  : G fvᵣ

  infix 4 _▷_
    
  record _▷_ {A : Set} (β : Scope A) (F : Scope A → Set) (α : Scope A) : Set where
    constructor bind
    field 
      {support} : Scope A
      thinning  : support ⊆ β
      body      : F (α Scope.++ support)

  data None {A : Set} : Scope A → Set where
    none : None ∅

  data Only (x : A) : Scope A → Set where
    only : Only x (∅ ▹ x)


open Scope using (Scope; ∅; _▹_)
open Thinning using (_⊆_; base; _keep_; _drop_)
open Cover using (Cover; base; _left_; _right_; _both_; _⊗_; _⟨_⟩_; _▷_; bind; None; none; Only; only)



infixr 5 _∷_ _∷[_]_ 

data Vars {A : Set} : Scope A → Set where
  [] : Vars ∅
  _∷_ : ∀ x {α} → (Only x ⊗ Vars) α → Vars α

pattern _∷[_]_ x c xs = x ∷ only ⟨ c ⟩ xs

ex : Vars (∅ ▹ "x" ▹ "y" ▹ "z")
ex = "x" ∷[ base both "x" right "y" right "z" ] "y" ∷[ base right "x" left "y" right "z" ] "z" ∷[ base right "x" left "z" ] "x" ∷[ base left "x" ] []

private variable
  K : Set
  α : Scope K
 
data Term {K : Set} : Scope K → Set where
  U_  : (l : ℕ) → Term ∅
  Π   : ∀ x → (Term ⊗ (∅ ▹ x ▷ Term)) α → Term α
  Nat : Term ∅
  lam : ∀ x → (Term ⊗ (∅ ▹ x ▷ Term)) α → Term α
  var : ∀ x → Term (∅ ▹ x)
  lit : (n : ℕ) → Term ∅

pattern var! x = var x only

data Con {K : Set} : Scope K → Set where
  nil  : Con ∅
  cons : ∀ {x} → (Term ⊗ (∅ ▹ x ▷ Con)) α → Con α

