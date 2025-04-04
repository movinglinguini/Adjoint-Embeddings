open import Data.String

module ADJS4 where
  {- Some set up... -}
  PropAtom = String 

  open import S4.Logic PropAtom _≟_ hiding (_≟_)