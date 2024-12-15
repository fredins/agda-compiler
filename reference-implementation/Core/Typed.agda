module Core.Typed where

open import Data.Nat using (ℕ; zero; suc; _⊔_)
open import Data.Fin using (Fin; zero; suc)

open import Core.Untyped

private variable 
  m n l l₁  : ℕ
  A B t t₁  : Term _
  Γ         : Con Term _
  x         : Fin _

infix 4 _∷_∈_

-- Well-formed variable
data _∷_∈_ : (x : Fin n) (A : Term n) (Γ : Con Term n) → Set where
  here  : zero ∷ wk1 A ∈ Γ ▹ A
  there : x ∷ A ∈ Γ → suc x ∷ wk1 A ∈ Γ ▹ B

mutual
  infix 4 ⊢_ _⊢_

  -- Well-formed context
  data ⊢_ : Con Term n → Set where
    ε : 
      ---
      ⊢ ε 
    ▹_ : 
      Γ ⊢ A → 
      -------
      ⊢ Γ ▹ A

  -- Well-formed type
  data _⊢_ (Γ : Con Term n) : Term n → Set where
    Π : 
      Γ ▹ A ⊢ B → 
      -----------
      Γ ⊢ Π A B

    U : 
      ⊢ Γ → 
      -------
      Γ ⊢ U l

    N : 
      ⊢ Γ → 
      -----
      Γ ⊢ N


infix 4 _⊢_∷_

-- Well-formed term of a type
data _⊢_∷_ (Γ : Con Term n) : Term n → Term n → Set where
  var : 
    ⊢ Γ → 
    x ∷ A ∈ Γ → 
    -----------------
    Γ ⊢ var x ∷ A

  lam : 
    Γ ▹ A ⊢ B → 
    Γ ▹ A ⊢ t ∷ B → 
    -----------------
    Γ ⊢ lam t ∷ Π A B

  _·_ : 
    Γ ⊢ t ∷ Π A B → 
    Γ ⊢ t₁ ∷ A → 
    ----------------------
    Γ ⊢ t · t₁ ∷ B [ t₁ ]₀

  Π : 
    Γ ⊢ A ∷ U l → 
    Γ ▹ A ⊢ B ∷ U l₁ → 
    ----------------------
    Γ ⊢ Π A B ∷ U (l ⊔ l₁)

  U : 
    ⊢ Γ → 
    -------------------
    Γ ⊢ U l ∷ U (suc l)

  N : 
    ⊢ Γ → 
    -----------
    Γ ⊢ N ∷ U 0

  zero : 
    ⊢ Γ → 
    ------------
    Γ ⊢ zero ∷ N

  suc : 
    Γ ⊢ t ∷ N → 
    -------------
    Γ ⊢ suc t ∷ N

  {-
    ⊥ : 
      ⊢ Γ → 
      -----------
      Γ ⊢ ⊥ ∷ U 0
  -}
       

