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
    harml/valid : mHarmless mValid
    harml/true : mHarmless mTrue
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
    PropAtom Mode mWeakenable mContractable mHarmless _∙_⇒_ _≥_ 
    renaming (_⊢_ to _⊢ᵃ_; Context to AdjointContext)

  private
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
      Aₘ Aₘ' Bₘ : Prop × Mode

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

  data Only-mIrrelevant : AdjointContext n → Set where
    onlyi/z : Only-mIrrelevant []

    onlyi/s :
      Only-mIrrelevant Ψ
      → Only-mIrrelevant ((Aₐ , mIrrelevant) ∷ Ψ)

  -- We define ↑-ifying a truth proposition. We simply
  -- apply an upshift to it.
  data ↑-prop : Prop × Mode → Prop × Mode → Set where
    ↑/prop/z : ↑-prop (Aₐ , mTrue) (↑[ mValid ][ mTrue ] Aₐ , mValid)

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
  irrel-irrel : Only-mIrrelevant (irrelify Ψ)
  irrel-irrel {Ψ = []} = onlyi/z
  irrel-irrel {Ψ = x ∷ Ψ} = onlyi/s irrel-irrel
  
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

  
  -- Just going to postulate a bunch of commonly accepted lemmas
  postulate
    {- When can bring elements of the context from the tail to the head. -}
    exch-Ψ-1 : (Ψ₁ ++ (Aₘ ∷ Ψ₂)) ⊢ᵃ Bₘ → (Aₘ ∷ Ψ₁ ++ Ψ₂) ⊢ᵃ Bₘ
    exch-Ψ-2 : (Aₘ ∷ Ψ₁ ++ Ψ₂) ⊢ᵃ Bₘ → (Ψ₁ ++ (Aₘ ∷ Ψ₂)) ⊢ᵃ Bₘ

    -- Every translation from an S4 context to an adjoint context is weakenable
    weaken-transl-Ψ : ∀ { Δ : HypContext n t } 
      → Ψ ≡ (τ t Δ)
      → cWeakenable Ψ
    
    -- Similar to the above, but when we upshift the translated context
    weaken-transl-up-Ψ :
      ↑-ctxt (τ Validity Δ) Ψ
      → cWeakenable Ψ

    -- The following two lemmas are similar to the above, but 
    -- concerning contraction rather than weakening.
    contr-transl-Ψ : ∀ { Δ : HypContext n t }
      → Ψ ≡ (τ t Δ)
      → cContractable Ψ

    contr-transl-up-Ψ :
      ↑-ctxt (τ Validity Δ) Ψ
      → cContractable Ψ

    -- If I concat two weakenable contexts, the result is weakenable
    weaken-concat : 
      cWeakenable Ψ₁    →   cWeakenable Ψ₂
      → cWeakenable (Ψ₁ ++ Ψ₂)

    -- Same idea as above with contractability.
    contr-concat :
      cContractable Ψ₁    →   cContractable Ψ₂
      → cContractable (Ψ₁ ++ Ψ₂)

    -- Any adjoint context is greater than mTrue, since mTrue is bottom.
    mTrue-bot : Ψ ≥ᶜ mTrue

    -- I can do no-op updates to contexts.
    update-id : ∀ { Ψ : AdjointContext n } → update (Aₘ ∷ Ψ) Aₘ Aₘ (Aₘ ∷ Ψ)

    weaken-++R : (Ψ₁ ++ []) ⊢ᵃ Aₘ → (Ψ₁ ++ Ψ₂) ⊢ᵃ Aₘ

  {- Now, some lemmas -}

  -- The merge operation on modes is reflexive.
  ∙-id : k ∙ k ⇒ k
  ∙-id {mValid} = v∙v
  ∙-id {mTrue} = t∙t
  ∙-id {mIrrelevant} = i∙i

  -- The merge operation on contexts is reflexive.
  merge-id : merge Ψ Ψ Ψ
  merge-id {Ψ = []} = merge/z
  merge-id {Ψ = x ∷ Ψ} = merge/s merge-id ∙-id

  -- A fully truth context can merge with a fully irrelevant context
  merge-irrel : Only-mTrue Ψ → merge (irrelify Ψ) Ψ Ψ
  merge-irrel onlyt/z = merge/z
  merge-irrel (onlyt/s ot) = merge/s (merge-irrel ot) i∙t

  {- A context consisting of only valid things is weakenable -}
  valid-weakenable : Only-mValid Ψ → cWeakenable Ψ
  valid-weakenable onlyv/z = weak/z
  valid-weakenable (onlyv/s ov) = weak/s (valid-weakenable ov) weak/valid

  {- Similar lemma to above, but for irrelevant contexts -}
  irrel-weakenable : Only-mIrrelevant Ψ → cWeakenable Ψ
  irrel-weakenable onlyi/z = weak/z
  irrel-weakenable (onlyi/s oi) = weak/s (irrel-weakenable oi) weak/irr

  {- Similar to lemma above, but for truth contexts -}
  true-weakenable : Only-mTrue Ψ → cWeakenable Ψ
  true-weakenable onlyt/z = weak/z
  true-weakenable (onlyt/s ot) = weak/s (true-weakenable ot) weak/true

  -- Implication lemma for S4-embedded Adjoint logic
  gen-⊸ : Ψ ⊢ᵃ (Aₐ , mTrue) → Ψ ⊢ᵃ (Aₐ ⊸ Bₐ , mTrue) → Ψ ⊢ᵃ (Bₐ , mTrue)
  gen-⊸ D1 D2 = {!   !}

  {-
   Theorems we want to prove. We want to show that our S4 instantiation of Adjoint Logic
   is equivalent to the original S4. That is, we can prove something in one system iff
   we can prove it in the other. There are two iff statements to prove.
  -}

  -- First, the more general one. 
  -- (=>) If we can prove S4 with an arbitrary Δ and Γ, then
  -- we can prove the equivalent in adjoint logic.
  embed-S4-1-if : ∀ { Δ : HypContext n Validity } { Γ : HypContext m Truth }
    → (Δ , Γ) ⊢ˢ (Aₛ , true)
    → ↑-ctxt (τ Validity Δ) Ψ₁
    → (Ψ₁ ++ (τ Truth Γ)) ⊢ᵃ (translS4-TProp (Aₛ , true)) 

  -- (<=) If we can prove a statement in adjoint logic,
  -- then we can prove the equivalent in S4.
  embed-S4-1-oif : ∀ { Δ : HypContext n Validity } { Γ : HypContext m Truth }
    → (Ψ₁ ++ (τ Truth Γ)) ⊢ᵃ (translS4-TProp (Aₛ , true)) 
    → ↑-ctxt (τ Validity Δ) Ψ₁
    → (Δ , Γ) ⊢ˢ (Aₛ , true)

  embed-S4-1-if {Ψ₁ = Ψ₁} {Γ = Γ} (hyp) up-ctxt 
    = exch-Ψ-2 
        (id { k = mTrue } 
            update-id (weak/s (weaken-concat (weaken-transl-up-Ψ up-ctxt) (weaken-transl-Ψ refl)) weak/true) 
          harml/true)
  embed-S4-1-if (⊃I D) up-ctxt = ⊸R (exch-Ψ-1 (embed-S4-1-if D up-ctxt))
  embed-S4-1-if { Ψ₁ = Ψ₁ } { Γ = Γ } (⊃E D D₁) up-ctxt = gen-⊸ (embed-S4-1-if D₁ up-ctxt) (embed-S4-1-if D up-ctxt)
  embed-S4-1-if { Γ = Γ } hyp* (↑/ctxt/s {Ψ' = Ψ'} up-ctxt ↑/prop/z) 
    = ↑L consume/yes v≥t 
      (id { k = mTrue } update/z (weak/s (weaken-concat (weaken-transl-up-Ψ up-ctxt) (weaken-transl-Ψ { t = Truth } { Δ = Γ } refl)) weak/true) harml/true)
  embed-S4-1-if { Ψ₁ = Ψ₁ } { Γ = Γ } (■I D) up-ctxt 
    = ↓R M (mValid-bot (Ψ₁-valid) irrel-irrel) (weaken-concat (valid-weakenable Ψ₁-valid) (true-weakenable trans-true)) 
      (↑R (weaken-++R (embed-S4-1-if D up-ctxt))) 
    where
      tΓ = τ Truth Γ
      IΓ = map (λ x → proj₁ x , mIrrelevant) tΓ

      M1 : merge Ψ₁ Ψ₁ Ψ₁
      M1 = merge-id

      M2 : merge IΓ tΓ tΓ
      M2  = merge-irrel trans-true

      M : merge (Ψ₁ ++ IΓ) (Ψ₁ ++ tΓ) (Ψ₁ ++ tΓ)
      M = merge-concat M1 M2

      ≥ᶜ-lem-1 : Only-mValid Ψ → Ψ ≥ᶜ mValid
      ≥ᶜ-lem-1 onlyv/z = ≥/z
      ≥ᶜ-lem-1 (onlyv/s ov) = ≥/s (≥ᶜ-lem-1 ov) m≥m

      ≥ᶜ-lem-2 : Only-mIrrelevant Ψ → Ψ ≥ᶜ mValid
      ≥ᶜ-lem-2 onlyi/z = ≥/z
      ≥ᶜ-lem-2 (onlyi/s oi) = ≥/s (≥ᶜ-lem-2 oi) i≥v

      mValid-bot : ∀ { Ψ₁ : AdjointContext n } { Ψ₂ : AdjointContext m } → Only-mValid Ψ₁ → Only-mIrrelevant Ψ₂ → (Ψ₁ ++ Ψ₂) ≥ᶜ mValid
      mValid-bot ov oi = ≥ᶜ-concat (≥ᶜ-lem-1 ov) (≥ᶜ-lem-2 oi)

      Ψ₁-valid : Only-mValid Ψ₁
      Ψ₁-valid = trans-valid up-ctxt

      IΓ-irrel : Only-mIrrelevant IΓ
      IΓ-irrel = irrel-irrel
      
  embed-S4-1-if { Ψ₁ = Ψ₁ } { Γ = Γ } (■E D D₁) up-ctxt 
    = cut merge-id merge-id merge-id mTrue-bot mTrue-bot m≥m (contr-concat (contr-transl-up-Ψ up-ctxt) (contr-transl-Ψ refl)) 
      (embed-S4-1-if D up-ctxt) 
      (↓L consume/yes (embed-S4-1-if D₁ (↑/ctxt/s up-ctxt ↑/prop/z)))
    where
      tΓ = τ Truth Γ  
  
  embed-S4-1-oif D1 up-ctxt = {! D1  !}

  embed-S4-2 : ∀ { Δ : HypContext (suc n) Validity }
    → (Δ , ([] , onlyt/z)) ⊢ˢ (Aₛ , true)
    → ↑-ctxt (τ Validity Δ) Ψ
    → ↑-prop (translS4-TProp (Aₛ , true)) Aₘ
    → Ψ ⊢ᵃ Aₘ
  embed-S4-2 D up-ctxt up-prop = {!   !}
 
                           