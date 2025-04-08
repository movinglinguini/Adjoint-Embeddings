open import Data.String hiding (length; _++_)
open import Data.Vec
open import Data.Nat hiding (_≟_; _≥_)
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Vec.Relation.Unary.Any

module S4.Embedding where
  {- Some set up... -}
  -- A PropAtom is the smallest unit in our logics.
  -- They construct arbitrary propositions.
  PropAtom = String 

  {-
    Initializing S4 is easy. We just need to pass in a PropAtom and
    a way to compare PropAtoms. 
  -}
  open import S4.Logic PropAtom _≟_
    renaming (_⊢_ to _⊢ˢ_)
  
  {-
    Initializing Adjoint Logic is a little more involved. To do this
    we'll need:

    1. Modes
    2. A preordering on our modes
    3. Structural rules for our modes
    4. An operation on pairs of modes
  -}
  
  -- Let's start with our modes
  data Mode : Set where
    mValid : Mode
    mTrue : Mode
  
  -- Now the preordering on modes
  data _≥_ : Mode → Mode → Set where
    v≥t : mValid ≥ mTrue
    m≥m : ∀ { m } → m ≥ m

  -- Now the structural rules for our modes
  data mContractable : Mode → Set where
    contr/valid : mContractable mValid
    contr/true : mContractable mTrue

  data mWeakenable : Mode → Set where
    weak/valid : mWeakenable mValid
    weak/true : mWeakenable mTrue

  -- We need a notion of "harmlessness" for our modes.
  -- This comes up whenever we need to "consume" our modes, such as
  -- when we use the id rule or split a context.
  data mHarmless : Mode → Set where
    harml/valid : mHarmless mValid
    harml/true : mHarmless mTrue

  -- Finally, the binary operation on modes
  data _∙_⇒_ : Mode → Mode → Mode → Set where
    v∙v : mValid ∙ mValid ⇒ mValid
    t∙t : mTrue ∙ mTrue ⇒ mTrue

  -- Now, we can initialize Adjoint Logic
  open import Adjoint.Logic 
    PropAtom Mode mWeakenable mContractable mHarmless _∙_⇒_ _≥_ 
    renaming (_⊢_ to _⊢ᵃ_; Context to AdjointContext)

  private
    variable
      n m o : ℕ 
      Aₛ Bₛ : Proposition
      Aₐ : Prop 
      Δ : HypContext n Validity
      Γ : HypContext m Truth
      Ψ Ψ' Ψ₁ Ψ₂ : AdjointContext o
      t : Hypothesis
      k : Mode
      Aₕ Bₕ : Proposition × Hypothesis
      Aₘ Aₘ' : Prop × Mode

  {-
    Okay, so from here, we want to think about comparing S4 to ADJ.
    First, we need some translations. First, translating propositions.
  -}
  propToProp : Proposition → Prop
  propToProp (` x) = ` x
  propToProp (A ⊃ B) = (propToProp A) ⊸ (propToProp B)
  propToProp (■ A) = ↓[ mTrue ][ mValid ](↑[ mValid ][ mTrue ] (propToProp A))

  -- Translating tagged propositions. Note that all propositions
  -- translate to an adjoint propositon with the mode for truth.
  translS4-TProp : (Proposition × Hypothesis) → (Prop × Mode)
  translS4-TProp (A , true) = (propToProp A) , mTrue
  translS4-TProp (A , valid) = ↑[ mValid ][ mTrue ](propToProp A) , mTrue

  -- Translating entire contexts. It's annoying that we have to go by induction
  -- on the validity type, but c'est la vie.
  τ : ∀ t → HypContext n t → AdjointContext n
  τ Validity ([] , all-valid) = []
  τ Validity (A ∷ Δ , onlyv/s all-valid x) = translS4-TProp A ∷ τ Validity (Δ , all-valid)
  τ Truth ([] , all-truth) = []
  τ Truth (A ∷ Γ , onlyt/s all-truth x) = translS4-TProp A ∷ τ Truth (Γ , all-truth) 
  
  -- And now we define some relations that we'll need for our proofs.

  -- First, we define ↑-ifying a truth proposition. We simply
  -- apply an upshift to it.
  data ↑-prop : Prop × Mode → Prop × Mode → Set where
    ↑/prop : ↑-prop (Aₐ , mTrue) (↑[ mValid ][ mTrue ] Aₐ , mTrue)

  -- Second, we distribute ↑ across a context.
  data ↑-ctxt : AdjointContext n → AdjointContext n → Set where
    ↑/ctxt/z : ↑-ctxt [] []

    ↑/ctxt/s : 
      ↑-ctxt Ψ Ψ'    →   ↑-prop Aₘ Aₘ'
      → ↑-ctxt (Aₘ ∷ Ψ) (Aₘ' ∷ Ψ)

  embed-S4-1 : ∀ { Δ : HypContext (suc n) Validity } { Γ : HypContext (suc m) Truth }
    → (Δ , Γ) ⊢ˢ (Aₛ , true)
    → ↑-ctxt (τ Validity Δ) Ψ₁
    → (Ψ₁ ++ (τ Truth Γ)) ⊢ᵃ (translS4-TProp (Aₛ , true)) 

  embed-S4-2 : ∀ { Δ : HypContext (suc n) Validity }
    → (Δ , ([] , onlyt/z)) ⊢ˢ (Aₛ , true)
    → ↑-ctxt (τ Validity Δ) Ψ
    → ↑-prop (translS4-TProp (Aₛ , true)) Aₘ
    → Ψ ⊢ᵃ Aₘ

  embed-S4-1 (hyp x) _ = {!   !}
  embed-S4-1 (⊃I D) _ = ⊸R (embed-S4-1 {!   !} {!   !}) -- Needs exchange
  embed-S4-1 (⊃E D D₁) _ = {!   !}
  embed-S4-1 (hyp* x) _ = {!   !}
  embed-S4-1 (■I D) _ = ↓R {!   !} {!   !} {!   !} (↑R ({!   !}))
  embed-S4-1 (■E D D₁) _ = {!   !}
  
  embed-S4-2 {Δ = Aₛ ∷ fst , onlyv/s snd x} (⊃I D) (↑/ctxt/s ↑-c x₁) ↑/prop = ↑R (⊸R {!   !}) -- Needs substitution principle for S4
  embed-S4-2 (⊃E D D₁) ↑-c ↑/prop = {!   !}
  embed-S4-2 (hyp* x) ↑-c ↑/prop = ↑R (id {!   !} {!   !} {!   !})
  embed-S4-2 (■I D) ↑-c ↑/prop = ↑R (↓R {!   !} {!   !} {!   !} (↑R {!   !}))
  embed-S4-2 (■E D D₁) ↑-c ↑/prop = ↑R {!   !}
 
    