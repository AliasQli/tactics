{-# OPTIONS --without-K #-}

module Tactic where

open import Agda.Primitive
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma renaming (_,_ to _,,_)

record 𝒰 : Setω where
  constructor ⦅_⦆
  field
    {ℓ} : Level
    Ty : Set ℓ
open 𝒰 public

{-# NO_UNIVERSE_CHECK #-}
data List (A : Setω) : Set where
  [] : List A
  _∷_ : A -> List A -> List A
open List public
infixr 5 _∷_

private variable
  u v : Level
  A B C D E : Set u
  P : A -> Set u
  a b c : A
  α β γ : Setω
  U : 𝒰
  US : List 𝒰

sigma-syntax : (A : Set u) (B : A -> Set v) → Set (u ⊔ v)
sigma-syntax = Σ

syntax sigma-syntax A (λ a -> B) = Σ[ a ∶ A ] B
infixr 2 sigma-syntax

_++_ : List α -> List α -> List α
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

data Env : List 𝒰 -> Setω where
  ∅   : Env []
  _◂_ : A -> Env US -> Env (⦅ A ⦆ ∷ US)
infixr 5 _◂_

by_ : (Env [] -> Env (⦅ A ⦆ ∷ [])) -> A
by tactics with tactics ∅
...           | x ◂ ∅ = x
infixr 0 by_

_,_ : (β -> γ) -> (α -> β) -> α -> γ
f , g = λ x -> f (g x)
infixr 2 _,_

_∎ : (Env [] -> Env US) -> Env [] -> Env US
tactics ∎ = tactics
infixl 1 _∎

record Casing (A : Set u) : Setω where
  constructor casing
  field
    Types : Set v -> List 𝒰
    cases : A -> Env (Types C ++ US) -> Env (⦅ C ⦆ ∷ US)
open Casing {{...}} using (cases)

record Inductive (A : Set u) : Setω where
  constructor induct
  field
    Types : (A -> Set v) -> List 𝒰
    induction : (a : A) -> Env (Types P ++ US) -> Env (⦅ P a ⦆ ∷ US)
open Inductive {{...}} using (induction)

instance
  _ : Casing Bool
  _ = record
    { Types = λ C -> ⦅ C ⦆ ∷ ⦅ C ⦆ ∷ []
    ; cases = λ 
        { true  (t ◂ f ◂ xs) -> t ◂ xs
        ; false (z ◂ f ◂ xs) -> f ◂ xs
        }
    }

  _ : Casing Nat
  _ = record
    { Types = λ C -> ⦅ C ⦆ ∷ ⦅ (Nat -> C) ⦆ ∷ []
    ; cases = λ
        { zero    (z ◂ s ◂ xs) -> z ◂ xs
        ; (suc n) (z ◂ s ◂ xs) -> s n ◂ xs
        }
    }

  _ : Inductive Bool
  _ = record
    { Types     = λ P -> ⦅ P true ⦆ ∷ ⦅ P false ⦆ ∷ []
    ; induction = λ
        { true  (t ◂ f ◂ xs) -> t ◂ xs
        ; false (t ◂ f ◂ xs) -> f ◂ xs
        }
    }

  _ : Inductive Nat
  _ = record
    { Types     = λ P -> ⦅ P zero ⦆ ∷ ⦅ (∀ n -> P n -> P (suc n)) ⦆ ∷ []
    ; induction = λ { n (z ◂ f ◂ xs) -> helper n z f ◂ xs }
    } where
        helper : ∀ n -> P zero -> (∀ n -> P n -> P (suc n)) -> P n
        helper zero    z f = z
        helper (suc n) z f = f n (helper n z f)

  inductiveΣ : Inductive (Σ A P)
  inductiveΣ {A = A} {P = P} = record
    { Types     = λ C -> ⦅ (∀ a -> (p : P a) -> C (a ,, p)) ⦆ ∷ []
    ; induction = λ { (a ,, p) (f ◂ xs) -> f a p ◂ xs }
    }

  inductive≡ : Inductive (Σ[ x ∶ A ] Σ[ y ∶ A ] x ≡ y)
  inductive≡ = record
    { Types     = λ C -> ⦅ (∀ a -> C (a ,, a ,, refl)) ⦆ ∷ []
    ; induction = λ { (a ,, a ,, refl) (f ◂ xs) -> f a ◂ xs }
    }

record App (A : Set u) : Setω where
  constructor app
  field
    Froms : List 𝒰
    To : 𝒰
    apply : A -> Env (Froms ++ US) -> Env (To ∷ US)
open App {{...}} using (apply)

instance
  AppZ : App A
  AppZ {A = A} = record
    { Froms = []
    ; To    = ⦅ A ⦆
    ; apply = λ a xs -> a ◂ xs
    }
  AppS : {{App B}} -> App (A -> B)
  AppS {A = A} {{app F T ap}} = record
    { Froms = ⦅ A ⦆ ∷ F
    ; To    = T
    ; apply = λ { f (a ◂ fxs) -> ap (f a) fxs }
    }

exact : A -> Env US -> Env (⦅ A ⦆ ∷ US)
exact = apply

apply1 : (A -> B) -> (env : Env (⦅ A ⦆ ∷ US)) -> Env (⦅ B ⦆ ∷ US)
apply1 = apply

apply2 : (A -> B -> C) -> Env (⦅ A ⦆ ∷ ⦅ B ⦆ ∷ US) -> Env (⦅ C ⦆ ∷ US)
apply2 = apply

apply3 : (A -> B -> C -> D) -> Env (⦅ A ⦆ ∷ ⦅ B ⦆ ∷ ⦅ C ⦆ ∷ US) -> Env (⦅ D ⦆ ∷ US)
apply3 = apply

reflexivity : Env US -> Env (⦅ a ≡ a ⦆ ∷ US)
reflexivity = exact refl

rw : a ≡ b -> Env (⦅ P b ⦆ ∷ US) -> Env (⦅ P a ⦆ ∷ US)
rw refl xs = xs

record Intro (how : ∀ {u v} {A : Set u} -> (A -> Set v) -> Set (u ⊔ v)) : Setω where
  field
    introduce : (∀ a -> Env [] -> Env (⦅ P a ⦆ ∷ [])) -> Env US -> Env (⦅ how P ⦆ ∷ US)
  introduce-ty : (A : Set u) {P : A -> Set v} -> (∀ a -> Env [] -> Env (⦅ P a ⦆ ∷ [])) -> Env US -> Env (⦅ how P ⦆ ∷ US)
  introduce-ty _ = introduce

  syntax introduce A (λ a -> b) = introduce a ∶ A ; b
  infixr 2 introduce
  syntax introduce-ty (λ a -> b) = introduce a ∶ A ; b
  infixr 2 introduce-ty
open Intro {{...}}

instance 
  _ : Intro (λ P -> (∀ a -> P a))
  _ = record
    { introduce = λ tactics xs -> (λ a -> by tactics a) ◂ xs
    }
  _ : Intro (λ P -> (∀ {a} -> P a))
  _ = record
    { introduce = λ tactics xs -> (λ {a} -> by tactics a) ◂ xs
    }

intro-ty-syntax : (A : Set u) {P : A -> Set v} -> (∀ a -> Env [] -> Env (⦅ P a ⦆ ∷ [])) -> Env US -> Env (⦅ (∀ a -> P a) ⦆ ∷ US)
intro-ty-syntax = introduce-ty
syntax intro-ty-syntax A (λ a -> b) = intro a ∶ A ; b
infixr 2 intro-ty-syntax

intro-syntax : (∀ a -> Env [] -> Env (⦅ P a ⦆ ∷ [])) -> Env US -> Env (⦅ (∀ a -> P a) ⦆ ∷ US)
intro-syntax = introduce
syntax intro-syntax (λ a -> b) = intro a ; b
infixr 2 intro-syntax

intro'-ty-syntax : (A : Set u) {P : A -> Set v} -> (∀ a -> Env [] -> Env (⦅ P a ⦆ ∷ [])) -> Env US -> Env (⦅ (∀ {a} -> P a) ⦆ ∷ US)
intro'-ty-syntax = introduce-ty
syntax intro'-ty-syntax A (λ a -> b) = intro' a ∶ A ; b
infixr 2 intro'-ty-syntax

intro'-syntax : (∀ a -> Env [] -> Env (⦅ P a ⦆ ∷ [])) -> Env US -> Env (⦅ (∀ {a} -> P a) ⦆ ∷ US)
intro'-syntax = introduce
syntax intro'-syntax (λ a -> b) = intro' a ; b
infixr 2 intro'-syntax

have-syntax : (a : A) -> (∀ a -> Env [] -> Env (⦅ P a ⦆ ∷ [])) -> Env US -> Env (⦅ P a ⦆ ∷ US)
have-syntax a f xs = (by f a) ◂ xs
syntax have-syntax subgoal (λ a -> b) = have a := subgoal ; b
infixr 2 have-syntax

have-ty-syntax : (A : Set u) {P : A -> Set v} -> (a : A) -> (∀ a -> Env [] -> Env (⦅ P a ⦆ ∷ [])) -> Env US -> Env (⦅ P a ⦆ ∷ US)
have-ty-syntax _ = have-syntax
syntax have-ty-syntax A subgoal (λ a -> b) = have a ∶ A := subgoal ; b
infixr 2 have-ty-syntax

haveω-syntax : {α : Setω} {P : α -> Set v} -> (a : α) -> (∀ a -> Env [] -> Env (⦅ P a ⦆ ∷ [])) -> Env US -> Env (⦅ P a ⦆ ∷ US)
haveω-syntax a f xs = (by f a) ◂ xs
syntax haveω-syntax subgoal (λ a -> b) = haveω a := subgoal ; b
infixr 2 haveω-syntax

haveω-ty-syntax : (α : Setω) {P : α -> Set v} -> (a : α) -> (∀ a -> Env [] -> Env (⦅ P a ⦆ ∷ [])) -> Env US -> Env (⦅ P a ⦆ ∷ US)
haveω-ty-syntax _ = haveω-syntax
syntax haveω-ty-syntax A subgoal (λ a -> b) = haveω a ∶ A := subgoal ; b
infixr 2 haveω-ty-syntax

module Examples where

  boolToNat : Bool -> Nat
  boolToNat b = by
    cases b ,
    exact 1 ,
    exact 0 ∎

  _ : boolToNat true ≡ 1
  _ = refl

  _ : boolToNat false ≡ 0
  _ = refl

  pred : Nat -> Nat
  pred n = by
    cases n ,
    exact 0 ,
    exact (λ x -> x) ∎

  _ : pred 5 ≡ 4
  _ = refl

  _ : pred 0 ≡ 0
  _ = refl

  succ : Nat -> Nat
  succ = by
    intro n ;
    apply suc ,
    exact n ∎

  _ : succ 3 ≡ 4
  _ = refl


  private variable
    f g h : A -> B

  _~_ : (f g : A -> B) -> Set _
  f ~ g = ∀ x -> f x ≡ g x

  refl~ : f ~ f
  refl~ x = by
    reflexivity ∎

  sym~ : f ~ g -> g ~ f
  sym~ = by
    intro H ; intro x ;
    haveω sym ∶ (∀ {u} {A : Set u} {a b : A} -> a ≡ b -> b ≡ a) := by
      intro' a ; intro' b ;
      intro eq ∶ a ≡ b ;
      induction {P = λ {(a ,, b ,, _) -> b ≡ a}} (a ,, b ,, eq) ,
      intro x ;
      reflexivity ;
    apply sym ,
    exact (H x) ∎

  trans~ : {f g h : A -> B} -> f ~ g -> g ~ h -> f ~ h
  trans~ {B = B} H1 H2 x = by
    have trans ∶ ({a b c : B} -> a ≡ b -> b ≡ c -> a ≡ c) 
      := (λ {refl refl -> refl}) ;
    apply trans ,
    exact (H1 x) ,
    exact (H2 x) ∎

  zero-plus : ∀ n -> 0 + n ≡ n
  zero-plus n = by
    reflexivity ∎

  plus-zero : ∀ n -> n + 0 ≡ n
  plus-zero n = by
    induction {P = λ n -> n + 0 ≡ n} n ,
    reflexivity ,
    intro n ; intro ih ;
    rw {P = λ x -> suc x ≡ suc n} ih , 
    reflexivity ∎
