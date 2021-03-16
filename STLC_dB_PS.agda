
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Agda.Builtin.Nat
open import Data.Unit
open import Data.Product
open import Data.String



module STLC_dB_PS where
  module Syntax where
    data Con : Set
    data Sub : Con -> Con -> Set
    data Ty : Set
    data Tm : (Σ : Con) -> Ty -> Set

    data Con where
      · : Con
      _▹_ : Con -> Ty -> Con

    data Ty where
      U : Ty
      Arr : Ty -> Ty -> Ty

    data Sub where
      ε : {Σ : Con} -> Sub Σ ·
      ⟨_,_⟩ : {Σ Δ : Con} -> {A : Ty} -> (γ : Sub Σ Δ) -> (Tm Σ A) -> (Sub Σ (Δ ▹ A))
      id : {Σ : Con} -> Sub Σ Σ
      π₁ : {Σ Δ : Con} -> {A : Ty} -> (Sub Σ (Δ ▹ A)) -> (Sub Σ Δ)
      _∘_ : {Σ Δ Ξ : Con} -> (Sub Σ Δ) -> (Sub Δ Ξ) -> (Sub Σ Ξ)

    data Tm where
      app : {Σ : Con} -> {A : Ty} -> {B : Ty} -> (Tm Σ (Arr A B))
               -> (Tm Σ A) -> (Tm Σ B)
      lam : {Σ : Con} -> {A : Ty} -> {B : Ty} -> (Tm (Σ ▹ A) B) -> (Tm Σ (Arr A B))
      π₂ : {Σ Δ : Con} -> {A : Ty} -> (γ : Sub Σ (Δ ▹ A)) -> (Tm Σ A )
      _[_]t : {Σ Δ : Con} -> {A : Ty} -> (Tm Δ A) -> (γ : Sub Σ Δ) -> (Tm Σ A)
      star : {Σ : Con} -> (Tm Σ U)


    wk : {Σ : Con} -> {A : Ty} -> (Sub (Σ ▹ A) Σ)
    wk = π₁ id

    vz : {Σ : Con} -> {A : Ty} -> (Tm (Σ ▹ A) A)
    vz = π₂ id

    vs : {Σ : Con} -> {A B : Ty} -> (Tm Σ A) -> (Tm (Σ ▹ B) A)
    vs x =  x [ wk ]t

    lift : {Σ Δ : Con} -> (γ : Sub Σ Δ) -> (A : Ty) -> (Sub (Σ ▹ A) (Δ ▹ A))
    lift γ A = ⟨ (wk ∘ γ) , vz ⟩

    sub0 : {Σ : Con} -> {A : Ty} → (Tm Σ A) → (Sub Σ (Σ ▹ A))
    sub0 t = ⟨ id , t ⟩

    app1 : {Σ : Con} -> {A : Ty} -> {B : Ty} -> (Tm Σ (Arr A B)) -> (Tm (Σ ▹ A) B)
    app1 t = (app (t [ wk ]t) vz)

    data Nf : Con -> Ty -> Set
    data Ne : Con -> Ty -> Set

    data Nf where
      Lam : {Γ : Con} -> {A B : Ty} -> (Nf (Γ ▹ A) B) -> (Nf Γ (Arr A B))
      Neu : {Γ : Con} -> {A : Ty} -> (Ne Γ A) -> (Nf Γ A)
    data Ne where
      Var0 : {Γ : Con} -> {A : Ty} -> (Ne (Γ ▹ A) A)
      VarS : {Γ : Con} -> {A B : Ty} -> (Ne Γ A) -> (Ne (Γ ▹ B) A)
      App : {Γ : Con} -> {A B : Ty} -> (Ne Γ (Arr A B)) -> (Nf Γ A) -> (Ne Γ B)
      Star : {Γ : Con} -> (Ne Γ U)

    NfTm : {Γ : Con} -> {A : Ty} -> (Nf Γ A) -> (Tm Γ A)
    NeTm : {Γ : Con} -> {A : Ty} -> (Ne Γ A) -> (Tm Γ A)

    NeTm Var0 = vz
    NeTm (VarS t) = vs (NeTm t)
    NeTm (App t u) = app (NeTm t) (NfTm u)
    NeTm Star = star

    NfTm (Lam s) = (lam (NfTm s))
    NfTm (Neu t) = NeTm t

    data NfSub : Con -> Con -> Set
    data NeSub : Con -> Con -> Set

    data NfSub where
      Nf⟨_,_⟩ : {Γ Δ : Con} -> {A : Ty} -> (NfSub Γ Δ)
                -> (Nf Γ A) -> (NfSub Γ (Δ ▹ A))
      NeuS : {Γ Δ : Con} -> NeSub Γ Δ -> NfSub Γ Δ
    data NeSub where
      Nε : {Γ : Con} -> NeSub Γ ·
      Ne⟨_,_⟩ : {Γ Δ : Con} -> {A : Ty} -> (NeSub Γ Δ)
                -> (Ne Γ A) -> (NeSub Γ (Δ ▹ A))

    SubNf : {Γ Δ : Con} -> NfSub Γ Δ -> Sub Γ Δ
    SubNe : {Γ Δ : Con} -> NeSub Γ Δ -> Sub Γ Δ
    SubNe Nε = ε
    SubNe Ne⟨ γ , t ⟩ = ⟨ (SubNe γ) , (NeTm t) ⟩
    SubNf Nf⟨ γ , t ⟩ = ⟨ (SubNf γ) , (NfTm t) ⟩
    SubNf (NeuS γ) = SubNe γ

    wkNeSub : {Γ Δ : Con} -> {A : Ty} -> NeSub Γ Δ -> NeSub (Γ ▹ A) Δ
    wkNeSub {Γ} {·} Nε = Nε
    wkNeSub {Γ} {Δ ▹ A} Ne⟨ γ , t ⟩ = Ne⟨ (wkNeSub γ) , VarS t ⟩

    Nid : {Γ : Con} -> NeSub Γ Γ
    Nid {·} = Nε
    Nid {Γ ▹ A} = Ne⟨ wkNeSub Nid , Var0 ⟩

    toStrC : Con -> String
    toStrT : Ty -> String
    toStrt : {Γ : Con} -> {A : Ty} -> (Tm Γ A) -> String
    toStrS : {Γ Δ : Con} -> Sub Γ Δ -> String

    toStrC · = "·"
    toStrC (Γ ▹ A) = (toStrC Γ) ++"▹"++ (toStrT A)
    toStrT U = "U"
    toStrT (Arr A B) = "("++(toStrT A)++" → "++(toStrT B)++")"
    toStrt (app t u) = "("++(toStrt t)++" "++(toStrt u)++")"
    toStrt (lam s) = "(λ "++(toStrt s)++")"
    toStrt (π₂ γ) = "(π₂ "++(toStrS γ)++")"
    toStrt (t [ γ ]t) = "("++(toStrt t)++"["++(toStrS γ)++"])"
    toStrt star = "⋆"
    toStrS ε = "ε"
    toStrS (⟨ γ , t ⟩) = "⟨"++(toStrS γ)++","++(toStrt t)++"⟩"
    toStrS id = "id"
    toStrS (π₁ γ) = "(π₁ "++(toStrS γ)++")"
    toStrS (γ ∘ δ) = "("++(toStrS γ)++"∘"++(toStrS δ)++")"


    toStrNf : {Γ : Con} -> {A : Ty} -> Nf Γ A -> String
    toStrNe : {Γ : Con} -> {A : Ty} -> Ne Γ A -> String

    toStrNe Var0 = "vz"
    toStrNe (VarS t) = "(vs "++(toStrNe t)++")"
    toStrNe (App t u) = "("++(toStrNe t)++" "++(toStrNf u)++")"
    toStrNe Star = "⋆"

    toStrNf (Lam s) = "(λ "++(toStrNf s)++")"
    toStrNf (Neu t) = toStrNe t

  module PShModel where
    Ren : Set
    Ren = Syntax.Con

    data Wk : Ren -> Ren -> Set where
      id : {Γ : Ren} -> Wk Γ Γ
      w1 : {Γ Δ : Ren} -> {A : Syntax.Ty}
           -> (Wk Γ Δ) -> (Wk (Γ Syntax.▹ A) Δ)
      w2 : {Γ Δ : Ren} -> {A : Syntax.Ty}
           -> (Wk Γ Δ) -> (Wk (Γ Syntax.▹ A) (Δ Syntax.▹ A))

    _∘w_ : {Γ Δ Ξ : Ren} -> (Wk Γ Δ) -> (Wk Δ Ξ) -> Wk Γ Ξ
    id ∘w w' = w'
    (w1 w) ∘w w' = w1 (w ∘w w')
    (w2 w) ∘w id = w2 w
    (w2 w) ∘w (w1 w') = w1 (w ∘w w')
    (w2 w) ∘w (w2 w') = w2 (w ∘w w')

    record PSh : Set₁ where
      constructor Fun
      field
        ! : Ren -> Set
        $ : {Γ Δ : Ren} -> (Wk Γ Δ) -> (! Δ) -> (! Γ)

    open PSh
    open Syntax

    NatT : PSh -> PSh -> Set
    NatT P Q = (Δ : Ren) -> (P .! Δ) -> (Q .! Δ)

    _[_]Ne : {Γ Δ : Ren} -> {A : Ty} -> (Ne Δ A) -> (Wk Γ Δ) -> (Ne Γ A)
    _[_]Nf : {Γ Δ : Ren} -> {A : Ty} -> (Nf Δ A) -> (Wk Γ Δ) -> (Nf Γ A)
    (Lam s) [ w ]Nf = Lam (s [ (w2 w) ]Nf)
    (Neu t) [ w ]Nf = Neu (t [ w ]Ne)
    Var0 [ (w2 w) ]Ne = Var0
    Var0 [ (w1 w) ]Ne = VarS (Var0 [ w ]Ne)
    t [ id ]Ne = t
    (VarS {Γ} {A} {B} t) [ (w2 {Δ} {Γ} {B} w) ]Ne = VarS (t [ w ]Ne)
    (VarS t) [ (w1 w) ]Ne = VarS ((VarS t) [ w ]Ne)
    (App t u) [ w ]Ne = App (t [ w ]Ne) (u [ w ]Nf)
    Star [ w ]Ne = Star

    evalC : Con -> PSh
    evalT : Ty -> PSh
    evalt : {Γ : Con} -> {A : Ty} -> (Tm Γ A) -> (NatT (evalC Γ) (evalT A))
    evalS : {Γ Δ : Con} -> (Sub Γ Δ) -> (NatT (evalC Γ) (evalC Δ))


    evalC · = Fun (λ Δ -> ⊤) (λ _ _ -> tt)
    evalC (Γ ▹ A) = Fun (λ Δ -> (evalC Γ .! Δ) × (evalT A .! Δ))
                        (λ w p -> (evalC Γ .$ w (fst p), evalT A .$ w (snd p)))


    evalT U = Fun (λ Δ -> Nf Δ U) (λ γ t -> t [ γ ]Nf)
    evalT (Arr A B) = Fun (λ Δ -> ((Ξ : Ren) -> (Wk Ξ Δ)
                               -> ((evalT A).! Ξ) -> ((evalT B).! Ξ)))
                          (λ w f -> (λ Ξ w' -> f Ξ (w' ∘w w)))


    evalt {Γ} (app t u) Δ γ = ((evalt t Δ γ Δ id) (evalt u Δ γ))
    evalt {Γ} {Arr A B} (lam s) Δ γ = (λ Ξ (w : Wk Ξ Δ) (x : evalT A .! Ξ) ->
                                         (evalt s Ξ (evalC Γ .$ w γ , x )))
    evalt (π₂ γ) Δ σ = snd (evalS γ Δ σ)
    evalt {Γ} {A} (t [ γ ]t) Δ σ = (evalt t Δ (evalS γ Δ σ))
    evalt {Σ} {A} star Δ σ = Neu Star


    evalS ε Δ σ = tt
    evalS (⟨ γ , t ⟩) Δ σ = (evalS γ Δ σ , evalt t Δ σ)
    evalS id Δ σ = σ
    evalS (π₁ γ) Δ σ = fst (evalS γ Δ σ)
    evalS (γ ∘ δ) Δ σ = (evalS δ Δ (evalS γ Δ σ))


  module Nbe where
    open Syntax
    open PShModel
    open PSh

    reifyC : Con -> Con
    reifyT : Ty -> Ty
    reifyt : (A : Ty) -> {Δ : Ren} -> (evalT A .! Δ) -> Nf Δ A
    reifyS : (Γ : Con)-> {Δ : Ren} -> (evalC Γ .! Δ) -> (NfSub Δ Γ)

    reflect : (A : Ty) -> {Δ : Ren} -> (Ne Δ A) -> (evalT A) .! Δ
    reflectS : (Γ Δ : Ren) -> (γ : NeSub Γ Δ) -> (evalC Δ .! Γ)

    reifyC Γ = Γ

    reifyT A = A

    reifyt U ⟦t⟧ = ⟦t⟧
    reifyt (Arr A B) {Δ} ⟦t⟧ = (Lam (reifyt B (⟦t⟧ (Δ ▹ A) (w1 id)
                                    (reflect A Var0))))

    reifyS · {Δ} ⟦γ⟧ = (NeuS Nε)
    reifyS (Γ ▹ A) {Δ} ⟦γ⟧ = Nf⟨ (reifyS Γ (fst ⟦γ⟧)) , (reifyt A (snd ⟦γ⟧)) ⟩

    reflect U {Δ} t = Neu t
    reflect (Arr A B) {Δ} t Ξ w u = reflect B (App (t [ w ]Ne) (reifyt A u))

    reflectS Γ Δ Nε = tt
    reflectS Γ (Δ ▹ A) (Ne⟨ γ , t ⟩) = (reflectS Γ Δ γ , reflect A t)

    nbet : (Γ : Con) -> (A : Ty) -> (t : Tm Γ A) -> (Nf Γ A)
    nbet Γ A t = reifyt A (evalt t Γ (reflectS Γ Γ Nid))

    nbeS : (Γ Δ : Con) -> (γ : Sub Γ Δ) -> (NfSub Γ Δ)
    nbeS Γ Δ γ = reifyS Δ {Γ} (evalS γ Γ (reflectS Γ Γ Nid))


  open import IO
  open import Level
  open Syntax
  open Nbe using (nbet)

  open import Data.List.Base as List using (List; _∷_; [])

  _=>_ : Ty -> Ty -> Ty
  A => B = (Arr A B)
  infixr 4 _=>_

  I : ∀{Γ A} -> Tm Γ (A => A)
  I = (lam vz)

  K : ∀{Γ A B} -> Tm Γ (A => B => A)
  K = (lam (lam (vs (app I vz))))

  S : ∀{Γ A B C} -> Tm Γ ((A => B => C) => (A => B) => A => C)
  S = lam (lam (lam (app (app (vs (vs vz)) vz) (app (vs vz) vz))))

  test : List (Σ Ty (λ A -> (Tm · A)))
  test = ((U => U) , lam (app (app K vz) (app I star)))
         ∷ (((U => U => U) => (U => U) => U => U) , S)
         ∷ (((U => U) => U => U) , (app S K))
         ∷ ((U => U) , (app (app S K) I))
         ∷ []

  main = run {0ℓ}
         (IO.List.sequence
           (let runtest p = (putStrLn ((toStrt (snd p))++" : "++(toStrT (fst p))))
                         >> (putStrLn (toStrNf (nbet _ (fst p) (snd p))))
                          in (List.map runtest test)))
