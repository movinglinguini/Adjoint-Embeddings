open import Data.Vec
open import Data.Product hiding (map)
open import Relation.Binary.PropositionalEquality
open import Data.Vec.Relation.Unary.Any hiding (map)

open import S4.Embedding
open import S4.Lemmas

module S4.Theorems where
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
  embed-S4-1-if {Ψ₁ = Ψ₁} {Γ = Γ} (hyp x) up-ctxt = id (∈⇒update-++Γ x) (trans-weakenable up-ctxt) harml/true
  embed-S4-1-if (⊃I D) up-ctxt = ⊸R (exch-Ψ-1 (embed-S4-1-if D up-ctxt))
  embed-S4-1-if { Ψ₁ = Ψ₁ } { Γ = Γ } (⊃E D D₁) up-ctxt = gen-⊸ (embed-S4-1-if D₁ up-ctxt) (embed-S4-1-if D up-ctxt)
  embed-S4-1-if (hyp* x) up-ctxt = update-↑valid⇒update-true (∈⇒update-Δ++ x up-ctxt)
  embed-S4-1-if { Ψ₁ = Ψ₁ } { Γ = Γ } (■I D) up-ctxt
    = ↓R M (mValid-bot (Ψ₁-valid) irrel-irrel) (trans-weakenable up-ctxt) 
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
    = cut merge-id merge-id merge-id mTrue-bot mTrue-bot m≥m (trans-contractable up-ctxt) 
      (embed-S4-1-if D up-ctxt) -- IH
      (↓L consume/yes (embed-S4-1-if D₁ (↑/ctxt/s up-ctxt ↑/prop/z))) -- ↓L, then IH
  -- embed-S4-1-if (∧I D₁ D₂) up-ctxt = ?
  --   -- = ⊗R merge-id merge-id merge-id (contr-concat (valid-contractable (trans-valid up-ctxt)) (true-contractable trans-true)) 
  --   --   (embed-S4-1-if D₁ up-ctxt) -- IH
  --   --   (embed-S4-1-if D₂ up-ctxt) -- IH     
  -- embed-S4-1-if (∧E₁ D) up-ctxt = ?
  --   -- = cut merge-id merge-id merge-id mTrue-bot mTrue-bot m≥m (trans-contractable up-ctxt) 
  --   --   (embed-S4-1-if D up-ctxt) -- IH
  --   --   (⊗L consume/yes (id (update/s update-id) (weak/s (weak/s (weaken-concat (valid-weakenable (trans-valid up-ctxt)) (true-weakenable trans-true)) weak/true) weak/true) harml/true))
  -- embed-S4-1-if (∧E₂ D) up-ctxt = ?
  --   -- = cut merge-id merge-id merge-id mTrue-bot mTrue-bot m≥m (trans-contractable up-ctxt) 
  --   --   (embed-S4-1-if D up-ctxt) -- IH
  --   --   (⊗L consume/yes (id update-id (weak/s (weak/s (trans-weakenable up-ctxt) weak/true) weak/true) harml/true))
  -- embed-S4-1-if (∨I₁ D) up-ctxt = ⊕R₁ (embed-S4-1-if D up-ctxt) -- IH
  -- embed-S4-1-if (∨I₂ D) up-ctxt = ⊕R₂ (embed-S4-1-if D up-ctxt) -- IH
  
  -- (<=) If we can prove a statement in adjoint logic,
  -- then we can prove the equivalent in S4.
  embed-S4-1-oif : ∀ { Ψ Aₐ } { Δ : HypContext n Validity } { Γ : HypContext m Truth }
    → ↑-ctxt (τ Validity Δ) Ψ₁
    → Ψ ≡ (Ψ₁ ++ (τ Truth Γ))
    → Aₐ ≡ (translS4-TProp (Aₛ , true))
    → Ψ ⊢ᵃ Aₐ
    → (Δ , Γ) ⊢ˢ (Aₛ , true)
  embed-S4-1-oif up-ctxt refl eq2 (id x x₁ x₂) = hyp {!   !}
  embed-S4-1-oif up-ctxt eq1 eq2 (cut x x₁ x₂ x₃ x₄ x₅ x₆ D1 D2) = {!   !}
  embed-S4-1-oif {Aₛ = Aₛ ⊃ Aₛ₁} up-ctxt refl refl (⊸R D1) = ⊃I (embed-S4-1-oif up-ctxt refl refl (exch-Ψ-2 D1))
  embed-S4-1-oif up-ctxt refl refl (⊸L  x x₁ x₂ x₃ x₄ x₅ x₆ x₇ D1 D2) = {!   !}
  embed-S4-1-oif up-ctxt eq1 eq2 (↓R x x₁ x₂ D1) = {!   !}
  embed-S4-1-oif up-ctxt eq1 eq2 (↓L x D1) = {!   !}
  -- ↑R is illegal!
  embed-S4-1-oif {Aₛ = ` x} up-ctxt eq1 () (↑R D1)
  embed-S4-1-oif {Aₛ = Aₛ ⊃ Aₛ₁} up-ctxt eq1 () (↑R D1)
  embed-S4-1-oif {Aₛ = ■ Aₛ} up-ctxt eq1 () (↑R D1)
  embed-S4-1-oif up-ctxt eq1 eq2 (↑L x x₁ D1) = {!   !}

  embed-S4-2 : ∀ { Δ : HypContext n Validity }
    → (Δ , ([] , onlyt/z)) ⊢ˢ (Aₛ , true)
    → ↑-ctxt (τ Validity Δ) Ψ
    → ↑-prop (translS4-TProp (Aₛ , true)) Aₘ
    → Ψ ⊢ᵃ Aₘ
  embed-S4-2 D up-ctxt up-prop = {!  !}                