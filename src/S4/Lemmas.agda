{-# OPTIONS --allow-unsolved-metas #-}
open import Data.Vec
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Vec.Relation.Unary.Any

open import S4.Embedding

module S4.Lemmas where
  -- Just going to postulate a bunch of commonly accepted lemmas
  postulate
    {- When can bring elements of the context from the tail to the head. -}
    exch-Ψ-1 : (Ψ₁ ++ (Aₘ ∷ Ψ₂)) ⊢ᵃ Bₘ → (Aₘ ∷ Ψ₁ ++ Ψ₂) ⊢ᵃ Bₘ
    exch-Ψ-2 : (Aₘ ∷ Ψ₁ ++ Ψ₂) ⊢ᵃ Bₘ → (Ψ₁ ++ (Aₘ ∷ Ψ₂)) ⊢ᵃ Bₘ

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

    weaken : Ψ ⊢ᵃ Aₘ → (Bₘ ∷ Ψ) ⊢ᵃ Aₘ

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

  {- We now make very similar arguments to the above, but for contractability -}
  valid-contractable : Only-mValid Ψ → cContractable Ψ
  valid-contractable onlyv/z = cont/z
  valid-contractable (onlyv/s ov) = cont/s (valid-contractable ov) contr/valid

  true-contractable : Only-mTrue Ψ → cContractable Ψ
  true-contractable onlyt/z = cont/z
  true-contractable (onlyt/s ot) = cont/s (true-contractable ot) contr/true

  {- Lemma: the translation of an S4 context is weakenable -}
  trans-weakenable : ↑-ctxt (τ Validity Δ) Ψ → cWeakenable (Ψ ++ (τ Truth Γ))
  trans-weakenable up-ctxt = weaken-concat (valid-weakenable (trans-valid up-ctxt)) (true-weakenable trans-true)

  {- Lemma: Same as above, but for contractability. -}
  trans-contractable : ↑-ctxt (τ Validity Δ) Ψ → cContractable (Ψ ++ (τ Truth Γ))
  trans-contractable up-ctxt = contr-concat (valid-contractable (trans-valid up-ctxt)) (true-contractable trans-true)

  {- Lemma: Any context in S4-Adjoint Logic is contractable --}
  Ψ-contractable : cContractable Ψ
  Ψ-contractable {Ψ = []} = cont/z
  Ψ-contractable {Ψ = (fst , mValid) ∷ Ψ} = cContractable.cont/s Ψ-contractable contr/valid
  Ψ-contractable {Ψ = (fst , mTrue) ∷ Ψ} = cContractable.cont/s Ψ-contractable contr/true
  Ψ-contractable {Ψ = (fst , mIrrelevant) ∷ Ψ} = cContractable.cont/s Ψ-contractable contr/irr

  {- Lemma: Similar to the above, but for weakenability --}
  Ψ-weakenable : cWeakenable Ψ
  Ψ-weakenable {Ψ = []} = cWeakenable.weak/z
  Ψ-weakenable {Ψ = (fst , mValid) ∷ Ψ} = cWeakenable.weak/s Ψ-weakenable weak/valid
  Ψ-weakenable {Ψ = (fst , mTrue) ∷ Ψ} = cWeakenable.weak/s Ψ-weakenable weak/true
  Ψ-weakenable {Ψ = (fst , mIrrelevant) ∷ Ψ} = cWeakenable.weak/s Ψ-weakenable weak/irr

  {- Lemma: Implication lemma for S4-embedded Adjoint Logic. -}
  gen-⊸ : Ψ ⊢ᵃ (Aₐ , mTrue) → Ψ ⊢ᵃ (Aₐ ⊸ Bₐ , mTrue) → Ψ ⊢ᵃ (Bₐ , mTrue)
  gen-⊸ D1 D2 = {!   !}

  {- Lemma: If I have truth context membership in S4, then I have the capacity to update in Adjoint Logic -}
  ∈⇒update-Γ : (to/truth (Aₛ , true) prop/true) ∈ʰ Γ → update (τ Truth Γ) (translS4-TProp (Aₛ , true)) (translS4-TProp (Aₛ , true)) (τ Truth Γ)
  ∈⇒update-Γ {Γ = .((_ , true) ∷ _) , onlyt/s snd x} (here refl) = update-id
  ∈⇒update-Γ {Γ = .(_ ∷ _) , onlyt/s snd x} (there mem) = update/s (∈⇒update-Γ mem)

  {- Extends the above lemma to work with prepending the truth context with an arbitrary context -}
  ∈⇒update-++Γ : 
    (to/truth (Aₛ , true) prop/true) ∈ʰ Γ 
    → update (Ψ ++ (τ Truth Γ)) (translS4-TProp (Aₛ , true)) (translS4-TProp (Aₛ , true)) (Ψ ++ (τ Truth Γ))
  ∈⇒update-++Γ {Ψ = []} mem = ∈⇒update-Γ mem
  ∈⇒update-++Γ {Ψ = x ∷ Ψ} mem = update/s (∈⇒update-++Γ mem)

  {- Lemma: If I have a validity context membership in S4, then I have the capacity to update in Adjoint Logic -}
  ∈⇒update-Δ : (to/validity (Aₛ , valid) prop/valid) ∈ʰ Δ 
    → ↑-ctxt (τ Validity Δ) Ψ
    → update Ψ (↑[ mTrue ][ mValid ](propToProp Aₛ) , mValid) (↑[ mTrue ][ mValid ](propToProp Aₛ) , mValid) Ψ
  ∈⇒update-Δ {Δ = .((_ , valid) ∷ _) , onlyv/s snd x} (here refl) (↑/ctxt/s up-ctxt ↑/prop/z) = update-id
  ∈⇒update-Δ {Δ = .(_ ∷ _) , onlyv/s snd x} (there mem) (↑/ctxt/s up-ctxt x₁) = update/s (∈⇒update-Δ mem up-ctxt)

  {- Extends the above lemma to work with appending the validity context with an arbitrary context-}
  ∈⇒update-Δ++ : (to/validity (Aₛ , valid) prop/valid) ∈ʰ Δ 
    → ↑-ctxt (τ Validity Δ) Ψ₁
    → update (Ψ₁ ++ Ψ₂) (↑[ mTrue ][ mValid ](propToProp Aₛ) , mValid) (↑[ mTrue ][ mValid ](propToProp Aₛ) , mValid) (Ψ₁ ++ Ψ₂)
  ∈⇒update-Δ++ {Δ = .((_ , valid) ∷ _) , onlyv/s snd x} (here refl) (↑/ctxt/s up-ctxt ↑/prop/z) = update-id
  ∈⇒update-Δ++ {Δ = .(_ ∷ _) , onlyv/s snd x} (there mem) (↑/ctxt/s up-ctxt ↑/prop/z) = update/s (∈⇒update-Δ++ mem up-ctxt)

  {- If I have an upshifted truth hyp in my context, then I can prove the truth hyp. -}
  update-↑valid⇒update-true : 
    update Ψ (↑[ mTrue ][ mValid ](Aₐ) , mValid) (↑[ mTrue ][ mValid ](Aₐ) , mValid) Ψ
    → Ψ ⊢ᵃ (Aₐ , mTrue)
  update-↑valid⇒update-true update/z = ↑L consume/yes m≥m (id update-id (weak/s Ψ-weakenable weak/true) harml/true)
  update-↑valid⇒update-true (update/s U) = weaken (update-↑valid⇒update-true U)

  