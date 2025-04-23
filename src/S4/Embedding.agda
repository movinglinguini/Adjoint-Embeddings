open import Data.String hiding (length; _++_; map)
open import Data.Vec
open import Data.Nat hiding (_≟_; _≥_)
open import Data.Product hiding (map)
open import Relation.Binary.PropositionalEquality
open import Data.Vec.Relation.Unary.Any hiding (map)

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
    renaming (_⊢_ to _⊢ˢ_) public
  
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
    mIrrelevant : Mode
  
  -- Now the preordering on modes
  data _≥_ : Mode → Mode → Set where
    v≥t : mValid ≥ mTrue
    i≥t : mIrrelevant ≥ mTrue
    i≥v : mIrrelevant ≥ mValid
    m≥m : ∀ { m } → m ≥ m

  -- Now the structural rules for our modes
  data mContractable : Mode → Set where
    contr/valid : mContractable mValid
    contr/true : mContractable mTrue
    contr/irr : mContractable mIrrelevant

  data mWeakenable : Mode → Set where
    weak/valid : mWeakenable mValid
    weak/true : mWeakenable mTrue
    weak/irr : mWeakenable mIrrelevant

  -- We need a notion of "harmlessness" for our modes.
  -- This comes up whenever we need to "consume" our modes, such as
  -- when we use the id rule or split a context.
  data mHarmless : Mode → Set where
    harml/irr : mHarmless mIrrelevant

  -- Finally, the binary operation on modes
  data _∙_⇒_ : Mode → Mode → Mode → Set where
    v∙v : mValid ∙ mValid ⇒ mValid
    t∙t : mTrue ∙ mTrue ⇒ mTrue
    i∙t : mIrrelevant ∙ mTrue ⇒ mTrue
    t∙i : mTrue ∙ mIrrelevant ⇒ mTrue
    i∙i : mIrrelevant ∙ mIrrelevant ⇒ mIrrelevant

  -- Now, we can initialize Adjoint Logic
  open import Adjoint.Logic 
    PropAtom Mode mWeakenable mContractable mHarmless _∙_⇒_ _≥_ mIrrelevant
    renaming (_⊢_ to _⊢ᵃ_; Context to AdjointContext) public

  variable
    n m o : ℕ 
    Aₛ Bₛ : Proposition
    Aₐ Bₐ : Prop 
    Δ : HypContext n Validity
    Γ : HypContext m Truth
    Ψ Ψ' Ψ₁ Ψ₂ : AdjointContext o
    t : ContextType
    k : Mode
    Aₕ Bₕ : Proposition × Hypothesis
    Aₘ Aₘ' Bₘ Cₘ : Prop × Mode

  {- Some helper relations -}
  data Only-mTrue : AdjointContext n → Set where
    onlyt/z : Only-mTrue []

    onlyt/s : 
      Only-mTrue Ψ
      → Only-mTrue ((Aₐ , mTrue) ∷ Ψ)

  data Only-mValid : AdjointContext n → Set where
    onlyv/z : Only-mValid []

    onlyv/s :
      Only-mValid Ψ
      → Only-mValid ((Aₐ , mValid) ∷ Ψ)

  -- We define ↑-ifying a truth proposition. We simply
  -- apply an upshift to it.
  data ↑-prop : Prop × Mode → Prop × Mode → Set where
    ↑/prop/z : ↑-prop (Aₐ , mTrue) (↑[ mTrue ][ mValid ] Aₐ , mValid)

  -- Second, we distribute ↑ across a context.
  data ↑-ctxt : AdjointContext n → AdjointContext n → Set where
    ↑/ctxt/z : ↑-ctxt [] []

    ↑/ctxt/s : 
      ↑-ctxt Ψ Ψ'    →   ↑-prop Aₘ Aₘ'
      → ↑-ctxt (Aₘ ∷ Ψ) (Aₘ' ∷ Ψ')

  {- Some helper functions -}
  -- Replace all modes in a context with mIrrelevant
  irrelify : AdjointContext n → AdjointContext n
  irrelify Ψ = map (λ x → (proj₁ x) , mIrrelevant) Ψ

  -- A context that has been irrelified is only full of irrelevant modes
  irrel-irrel : cIrrelevant (irrelify Ψ)
  irrel-irrel {Ψ = []} = irr/z
  irrel-irrel {Ψ = x ∷ Ψ} = irr/s irrel-irrel
  
  {-
    Okay, so from here, we want to think about comparing S4 to ADJ.
    First, we need some translations. First, translating propositions.
  -}
  propToProp : Proposition → Prop
  propToProp (` x) = ` x
  propToProp (A ⊃ B) = (propToProp A) ⊸ (propToProp B)
  propToProp (■ A) = ↓[ mTrue ][ mValid ](↑[ mTrue ][ mValid ] (propToProp A))
  -- propToProp (A ∧ B) = (propToProp A) ⊗ (propToProp B)
  -- propToProp (A ∨ B) = (propToProp A) & (propToProp B)

  -- Translating tagged propositions. Note that all propositions
  -- translate to an adjoint propositon with the mode for truth.
  translS4-TProp : (Proposition × Hypothesis) → (Prop × Mode)
  translS4-TProp (A , _) = (propToProp A) , mTrue

  -- Translating entire contexts. It's annoying that we have to go by induction
  -- on the validity type, but c'est la vie.
  τ : ∀ t → HypContext n t → AdjointContext n
  τ Validity ([] , all-valid) = []
  τ Validity (A ∷ Δ , onlyv/s all-valid x) = translS4-TProp A ∷ τ Validity (Δ , all-valid)
  τ Truth ([] , all-truth) = []
  τ Truth (A ∷ Γ , onlyt/s all-truth x) = translS4-TProp A ∷ τ Truth (Γ , all-truth) 

  {- Properties of the translation -}
  -- The translation of the truth context is all of mode true
  trans-true : Only-mTrue (τ Truth Γ)
  trans-true {Γ = [] , snd} = onlyt/z
  trans-true {Γ = x ∷ fst , onlyt/s snd x₁} = onlyt/s trans-true

  -- The up-shifted translation of the validity context is all of mode valid
  trans-valid : ↑-ctxt (τ Validity Δ) Ψ → Only-mValid Ψ 
  trans-valid {Δ = [] , snd} ↑/ctxt/z = onlyv/z
  trans-valid {Δ = x ∷ fst , onlyv/s snd x₁} (↑/ctxt/s up-ctxt ↑/prop/z) = onlyv/s (trans-valid up-ctxt)


  
 
                            