open import Data.String

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
    Valid : Mode
    True : Mode
  
  -- Now the preordering on modes
  data _≥_ : Mode → Mode → Set where
    v≥t : Valid ≥ True

  -- Now the structural rules for our modes
  data mContractable : Mode → Set where
    contr/valid : mContractable Valid
    contr/true : mContractable True

  data mWeakenable : Mode → Set where
    weak/valid : mWeakenable Valid
    weak/true : mWeakenable True

  -- We need a notion of "harmlessness" for our modes.
  -- This comes up whenever we need to "consume" our modes, such as
  -- when we use the id rule or split a context.
  data mHarmless : Mode → Set where
    harml/valid : mHarmless Valid
    harml/true : mHarmless True

  -- Finally, the binary operation on modes
  data _∙_⇒_ : Mode → Mode → Mode → Set where
    v∙v : Valid ∙ Valid ⇒ Valid

  open import Adjoint.Logic 
    PropAtom Mode mWeakenable mContractable {!   !} {!   !} _≥_ 