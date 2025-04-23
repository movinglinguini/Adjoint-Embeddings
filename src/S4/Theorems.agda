open import Data.Vec
open import Data.Nat
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
  -- (<=) If we can prove a statement in adjoint logic,
  -- then we can prove the equivalent in S4.
  embed-S4-1-oif : ∀ { Ψ₂ Aₘ } { Δ : HypContext n Validity } { Γ : HypContext m Truth }
    → ↑-ctxt (τ Validity Δ) Ψ₁
    → Ψ₂ ≡ (τ Truth Γ)
    → Ψ ≡ (Ψ₁ ++ Ψ₂)
    → Aₘ ≡ ((propToProp Aₛ) , mTrue)
    → (Ψ₁ ++ τ Truth Γ) ⊢ᵃ Aₘ
    → (Δ , Γ) ⊢ˢ (Aₛ , true)

  embed-S4-2-if : ∀ { Δ : HypContext n Validity }
    → ↑-ctxt (τ Validity Δ) Ψ₁
    → ↑-prop (translS4-TProp (Aₛ , true)) Aₘ
    → Ψ₁ ⊢ᵃ Aₘ
    → (Δ , ([] , onlyt/z)) ⊢ˢ (Aₛ , true)

  embed-S4-2-oif : ∀ { Ψ₂ : AdjointContext m } { Δ : HypContext n Validity }
    → ↑-ctxt (τ Validity Δ) Ψ₁
    → ↑-prop (translS4-TProp (Aₛ , true)) Aₘ
    → (Δ , ([] , onlyt/z)) ⊢ˢ (Aₛ , true)
    → (Ψ₁ ++ Ψ₂) ⊢ᵃ Aₘ 


  -- Proofs
  embed-S4-1-if {Ψ₁ = Ψ₁} {Γ = Γ} (hyp x) up-ctxt = id (∈⇒update-++Γ x) (trans-weakenable up-ctxt)
  embed-S4-1-if (⊃I D) up-ctxt = ⊸R (exch-Ψ-1 (embed-S4-1-if D up-ctxt))
  embed-S4-1-if { Ψ₁ = Ψ₁ } { Γ = Γ } (⊃E D D₁) up-ctxt = gen-⊸ (embed-S4-1-if D₁ up-ctxt) (embed-S4-1-if D up-ctxt)
  embed-S4-1-if (hyp* x) up-ctxt = update-↑valid⇒update-true (∈⇒update-Δ++ x up-ctxt)
  embed-S4-1-if { Ψ₁ = Ψ₁ } { Γ = Γ } (■I D) up-ctxt
    = ↓R M (mValid-bot Ψ₁-valid IΓ-irrel) (trans-weakenable up-ctxt)
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

      ≥ᶜ-lem-1 : ∀ { Ψ : AdjointContext n } → Only-mValid Ψ → Ψ ≥ᶜ mValid
      ≥ᶜ-lem-1 onlyv/z = ≥/z
      ≥ᶜ-lem-1 (onlyv/s ov) = ≥/s (≥ᶜ-lem-1 ov) m≥m

      ≥ᶜ-lem-2 : ∀ { Ψ : AdjointContext n } → cIrrelevant Ψ → Ψ ≥ᶜ mValid
      ≥ᶜ-lem-2 irr/z = ≥/z
      ≥ᶜ-lem-2 (irr/s oi) = ≥/s (≥ᶜ-lem-2 oi) i≥v

      mValid-bot : ∀ { Ψ₁ : AdjointContext n } { Ψ₂ : AdjointContext m } → Only-mValid Ψ₁ → cIrrelevant Ψ₂ → (Ψ₁ ++ Ψ₂) ≥ᶜ mValid
      mValid-bot ov oi = ≥ᶜ-concat (≥ᶜ-lem-1 ov) (≥ᶜ-lem-2 oi)

      Ψ₁-valid : Only-mValid Ψ₁
      Ψ₁-valid = trans-valid up-ctxt

      IΓ-irrel : cIrrelevant IΓ
      IΓ-irrel = irrel-irrel
      
  embed-S4-1-if { Ψ₁ = Ψ₁ } { Γ = Γ } (■E D1 D2) up-ctxt 
    = cut merge-id merge-id merge-id mTrue-bot mTrue-bot m≥m (trans-contractable up-ctxt) 
      (embed-S4-1-if D1 up-ctxt) -- IH
      (↓L (consume/yes update/z) (exch₀ (contract (embed-S4-1-if D2 (↑/ctxt/s up-ctxt ↑/prop/z))))) -- ↓L, then IH
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

  embed-S4-1-oif up-ctxt eq1 eq2 eq3 (id x x₁) = {!   !}
  embed-S4-1-oif up-ctxt eq1 eq2 eq3 (cut x x₁ x₂ x₃ x₄ x₅ x₆ D1 D2) = {!   !}
  embed-S4-1-oif {Aₛ = Aₛ ⊃ Aₛ₁} up-ctxt refl refl refl (⊸R D1) = ⊃I (embed-S4-1-oif up-ctxt refl refl refl (exch-Ψ-2 D1))
  embed-S4-1-oif up-ctxt refl refl refl (⊸L M12 M23 M C12 C23 Δ₁≥m Δ₂≥m Δ₂-contract D1 D2) = subst-1 {!   !} (⊃E (hyp (consume⇒∈ up-ctxt refl (lem M {! C12  !} {!  C23 !}))) {!   !})
    where
      lem : ∀ { Δ₁₂ Δ₁₂' Δ₂₃ Δ₂₃' Δ Δ' : AdjointContext n } { A m } → merge Δ₁₂ Δ₂₃ Δ → mayConsume Δ₁₂ (A , m) Δ₁₂' → mayConsume Δ₂₃ (A , m) Δ₂₃' → mayConsume Δ (A , m) Δ'
      lem {zero} {Δ₂₃' = []} merge/z (consume/yes ()) C2
      lem {zero} merge/z (consume/no ()) C2
      lem {suc n} (merge/s M x) (consume/yes x₁) (consume/yes x₂) = consume/yes {!   !}
      lem {suc n} (merge/s M x) (consume/yes x₁) (consume/no x₂) = {!   !}
      lem {suc n} (merge/s M x) (consume/no x₁) C2 = {!   !}
  embed-S4-1-oif {Aₛ = ■ Aₛ} up-ctxt eq1 eq2 eq3 (↓R M Δ₁≥m Δ₂-weak D1) = {!   !}
  embed-S4-1-oif up-ctxt eq1 eq2 refl (↓L C D1) = {!   !}
  embed-S4-1-oif {Aₛ = ` x} up-ctxt eq1 eq2 () (↑R D1)
  embed-S4-1-oif {Aₛ = Aₛ ⊃ Aₛ₁} up-ctxt eq1 eq2 () (↑R D1)
  embed-S4-1-oif {Aₛ = ■ Aₛ} up-ctxt eq1 eq2 () (↑R D1)
  embed-S4-1-oif up-ctxt eq1 eq2 eq3 (↑L x x₁ D1) = {!   !}
  
  -- embed-S4-1-oif up-ctxt eq1 eq2 eq3 (id x x₁) = {!   !}
  -- embed-S4-1-oif up-ctxt eq1 eq2 eq3 (cut x x₁ x₂ x₃ x₄ x₅ x₆ D1 D2) = {!   !}
  -- embed-S4-1-oif up-ctxt eq1 eq2 eq3 (⊸R D1) = {!   !}
  -- embed-S4-1-oif up-ctxt eq1 eq2 eq3 (⊸L M1 M2 M C1 C2 Δ₁≥m Δ₂≥m Δ₂-contract D1 D2) = {!   !}
  -- embed-S4-1-oif {Aₛ = ■ Aₛ} {Δ = Δ} {Γ} up-ctxt refl eq2 refl (↓R (merge/s M x) Δ₂≥m (exh/s Δ₂-exh harml/irr) Δ₂-weak D1) = {!   !}
  -- embed-S4-1-oif up-ctxt eq1 eq2 eq3 (↓L x D1) = {!   !}
  -- embed-S4-1-oif up-ctxt eq1 eq2 eq3 (↑R D1) = {!   !}
  -- embed-S4-1-oif up-ctxt eq1 eq2 eq3 (↑L x x₁ D1) = {!   !}
     