open import Data.String hiding (length)
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
      Aₛ : Proposition
      Aₐ : Prop 
      Δ : HypContext n Validity
      Γ : HypContext m Truth
      Ψ : AdjointContext (n + m)
      t : Hypothesis
      k : Mode
      Aₕ : Proposition × Hypothesis
      Aₘ : Proposition × Mode

  {-
    Okay, so from here, we want to think about comparing S4 to ADJ.
    First, we need some translations. First, translating contexts.
  -}
  private
    propToProp : Proposition → Prop
    propToProp (` x) = ` x
    propToProp (A ⊃ B) = (propToProp A) ⊸ (propToProp B)
    propToProp (■ A) = ↑[ mValid ][ mTrue ] (propToProp A)
    
    hypToMode : Hypothesis → Mode
    hypToMode true = mTrue
    hypToMode valid = mValid

  propS4toPropADJ : (Proposition × Hypothesis) → (Prop × Mode)
  propS4toPropADJ (A , true) = (propToProp A) , mTrue
  propS4toPropADJ (A , valid) = ↑[ mValid ][ mTrue ](propToProp A) , mTrue
  
  Δ⇒Ψ : HypContext n Validity → AdjointContext n
  Δ⇒Ψ ([] , snd) = []
  Δ⇒Ψ (x ∷ fst , onlyv/s snd x₁) = (propS4toPropADJ x) ∷ (Δ⇒Ψ (fst , snd))

  ADJ-embeds-S4-1 : (Δ , ([] , onlyt/z)) ⊢ˢ Aₕ → (Δ⇒Ψ Δ) ⊢ᵃ (propS4toPropADJ Aₕ)
  ADJ-embeds-S4-1 (⊃I D) = ⊸R {!   !}
  ADJ-embeds-S4-1 (⊃E D D₁) = {!  !}
  ADJ-embeds-S4-1 {Δ = Δ} (hyp* {B} x) = {!   !}
  ADJ-embeds-S4-1 (■I D) = ↑R (ADJ-embeds-S4-1 D)
  ADJ-embeds-S4-1 (■E D D₁) = ↑L {!   !} m≥m (ADJ-embeds-S4-1 D₁)
 