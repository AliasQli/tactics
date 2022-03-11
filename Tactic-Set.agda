{-# OPTIONS --without-K #-}

module Tactic-Set where

open import Agda.Primitive
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma renaming (_,_ to _,,_)

module Util where

  private variable
    u : Level
    A B : Set u
    a b c : A

  id : A -> A
  id x = x

  map : (A -> B) -> List A -> List B
  map f [] = []
  map f (x ∷ xs) = f x ∷ map f xs

  _++_ : List A -> List A -> List A
  [] ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

open Util

private variable
  u : Level
  A B C D X : Set
  XS : List Set
  P : A -> Set
  a b : A

data Env : List Set -> Set₁ where
  ∅   : Env []
  _◂_ : X -> Env XS -> Env (X ∷ XS)
infixr 20 _◂_

hd : Env (X ∷ XS) -> X
hd (x ◂ xs) = x

by_ : (Env [] -> Env (A ∷ [])) -> A
by tactics with tactics ∅
... | x ◂ ∅ = x
infixr 1 by_

_,_ : ∀{u v w} {A : Set u} {B : Set v} {C : Set w} -> (B -> C) -> (A -> B) -> A -> C
f , g = λ x -> f (g x)
infixr 2 _,_

_∎ : (Env [] -> Env XS) -> Env [] -> Env XS
_∎ = id
infixl 1.5 _∎

record Casing (A : Set) : Set₁ where
  constructor casing
  field
    Types : List (Set -> Set)
    cases : A -> Env (map (λ t -> t X) Types ++ XS) -> Env (X ∷ XS)
open Casing {{...}} using (cases)

record Inductive (A : Set) : Set₁ where
  constructor induct
  field
    Types : List ((A -> Set) -> Set)
    induction : (a : A) -> Env (map (λ t -> t P) Types ++ XS) -> Env (P a ∷ XS)
open Inductive {{...}} using (induction)

instance
  _ : Casing Bool
  _ = record
    { Types = id ∷ id ∷ []
    ; -- cases : Bool -> Env (X ∷ X ∷ xs) -> Env (X ∷ XS)
      cases = λ 
        { true  (t ◂ f ◂ xs) -> t ◂ xs
        ; false (z ◂ f ◂ xs) -> f ◂ xs
        }
    }

  _ : Casing Nat
  _ = record
    { Types = id ∷ (λ A -> (Nat -> A)) ∷ []
    ; -- cases : Nat -> Env (A ∷ (Nat -> A) ∷ XS) -> Env (A ∷ XS)
      cases = λ 
        { zero    (z ◂ f ◂ xs)  -> z ◂ xs
        ; (suc n) (z ◂ f ◂ xs)  -> f n ◂ xs
        }
    }

  _ : Inductive Bool
  _ = record
    { Types = (λ P -> P true) ∷ (λ P -> P false) ∷ []
    ; -- induction : (b : Bool) -> Env (P true ∷ P flase ∷ XS) -> Env (P b ∷ XS)
      induction = λ 
        { true  (t ◂ f ◂ xs) -> t ◂ xs
        ; false (z ◂ f ◂ xs) -> f ◂ xs
        }
    }

  _ : Inductive Nat
  _ = record
    { Types = (λ P -> P zero) ∷ (λ P -> (∀ n -> P n -> P (suc n))) ∷ []
    ; -- induction : (n : Nat) -> Env (P zero ∷ (∀ n -> P n -> P (suc n)) ∷ XS) -> Env (P n ∷ XS)
      induction = λ 
        { n (z ◂ f ◂ xs) -> helper n z f ◂ xs
        }
    }
      where
        helper : {P : Nat -> Set} -> (n : Nat) -> P zero -> (∀ n -> P n -> P (suc n)) -> P n
        helper zero z f = z
        helper (suc n) z f = f n (helper n z f)

  -- inductiveΣ : Inductive (Σ A P)
  -- inductiveΣ {A} {P} = record
  --   { Types = (λ C -> (∀ (a : A) -> (p : P a) -> C (a ,, p))) ∷ []
  --   ; -- induction : (s : Σ A P) -> Env ((∀ (a : A) -> (p : P a) -> C (a ,, p)) ∷ XS) -> Env (C s ∷ XS)
  --     induction = λ
  --       { (a ,, p) (f ◂ xs) -> f a p ◂ xs
  --       }
  --   }
  
  inductive≡ : Inductive (Σ A (λ x -> Σ A (x ≡_)))
  inductive≡ {A} = record
    { Types = (λ C -> (∀ (a : A) -> C (a ,, a ,, refl))) ∷ []
    ; -- 
      induction = λ
        { (a ,, a ,, refl) (f ◂ xs) -> f a ◂ xs
        }
    }

record App (A : Set) : Set₁ where
  constructor app
  field
    Froms : List Set
    To : Set
    apply : A -> Env (Froms ++ XS) -> Env (To ∷ XS)
open App {{...}} using (apply)

instance
  AppZ : App A
  AppZ {A = A} = record
    { Froms = []
    ; To    = A
    ; apply = λ a xs -> a ◂ xs
    }
  AppS : {{App B}} -> App (A -> B)
  AppS {A = A} {{app F T ap}} = record
    { Froms = A ∷ F
    ; To    = T
    ; apply = λ {f (a ◂ fxs) -> ap (f a) fxs}
    }

exact : X -> Env XS -> Env (X ∷ XS)
exact = apply

apply1 : ((a : A) -> P a) -> (env : Env (A ∷ XS)) -> Env (P (hd env) ∷ XS)
apply1 f (a ◂ xs) = f a ◂ xs

apply2 : (A -> B -> C) -> Env (A ∷ B ∷ XS) -> Env (C ∷ XS)
apply2 f (a ◂ b ◂ xs) = f a b ◂ xs

apply3 : (A -> B -> C -> D) -> Env (A ∷ B ∷ C ∷ XS) -> Env (D ∷ XS)
apply3 f (a ◂ b ◂ c ◂ xs) = f a b c ◂ xs

reflexivity : Env XS -> Env ((a ≡ a) ∷ XS)
reflexivity = exact refl

goal : (X : Set) -> Env (X ∷ XS) -> Env (X ∷ XS)
goal _ = id
-- syntax goal A tactics = goal A , tactics
-- infixr 2 goal

rw : {P : A -> Set} -> a ≡ b -> Env (P b ∷ XS) -> Env (P a ∷ XS)
rw refl xs = xs

intro-ty-syntax : (A : Set) {P : A -> Set} -> ((a : A) -> Env [] -> Env (P a ∷ [])) -> Env XS -> Env (((a : A) -> P a) ∷ XS)
intro-ty-syntax _ tactics xs = (λ a -> by tactics a) ◂ xs
syntax intro-ty-syntax A (λ a -> b) = intro a ∶ A ,, b
infixr 2 intro-ty-syntax

intro-syntax : ((a : A) -> Env [] -> Env (P a ∷ [])) -> Env XS -> Env (((a : A) -> P a) ∷ XS)
intro-syntax = intro-ty-syntax _
syntax intro-syntax (λ a -> b) = intro a ,, b
infixr 2 intro-syntax

intro'-ty-syntax : (A : Set) {P : A -> Set} -> ((a : A) -> Env [] -> Env (P a ∷ [])) -> Env XS -> Env (({a : A} -> P a) ∷ XS)
intro'-ty-syntax _ tactics xs = (λ {a} -> by tactics a) ◂ xs
syntax intro'-ty-syntax A (λ a -> b) = intro' a ∶ A ,, b
infixr 2 intro'-ty-syntax

intro'-syntax : ((a : A) -> Env [] -> Env (P a ∷ [])) -> Env XS -> Env (({a : A} -> P a) ∷ XS)
intro'-syntax = intro'-ty-syntax _
syntax intro'-syntax (λ a -> b) = intro' a ,, b
infixr 2 intro'-syntax

have-ty-syntax : (A : Set u) {P : A -> Set} -> (a : A) -> ((a : A) -> Env [] -> Env (P a ∷ [])) -> Env XS -> Env (P a ∷ XS)
have-ty-syntax _ a f xs = (by f a) ◂ xs -- subgoal = apply1 (λ f -> f subgoal) -- (f ◂ xs) = f have ◂ xs
syntax have-ty-syntax A subgoal (λ a -> b) = have a ∶ A := subgoal ,, b
infixr 2 have-ty-syntax

have-syntax : {A : Set u} {P : A -> Set} -> (a : A) -> ((a : A) -> Env [] -> Env (P a ∷ [])) -> Env XS -> Env (P a ∷ XS)
have-syntax = have-ty-syntax _
syntax have-syntax subgoal (λ a -> b) = have a := subgoal ,, b
infixr 2 have-syntax

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
    exact id ∎

  _ : pred 5 ≡ 4
  _ = refl

  _ : pred 0 ≡ 0
  _ = refl

  succ : Nat -> Nat
  succ = by
    intro n ,,
    apply suc ,
    exact n ∎

  _ : succ 3 ≡ 4
  _ = refl


  private variable
    f g h : A -> B

  _~_ : (f g : A -> B) -> Set
  f ~ g = ∀ x -> f x ≡ g x

  refl~ : f ~ f
  refl~ x = by
    reflexivity ∎

  sym~ : f ~ g -> g ~ f
  sym~ = by
    intro H ,, intro x ,,
    have sym ∶ ({A : Set} {a b : A} -> a ≡ b -> b ≡ a) := by
      intro' a ,, intro' b ,,
      intro eq ∶ a ≡ b ,,
      induction {P = λ {(a ,, b ,, _) -> b ≡ a}} (a ,, b ,, eq) ,
      intro x ,,
      reflexivity ∎ ,,
    apply sym ,
    exact (H x) ∎

  trans~ : f ~ g -> g ~ h -> f ~ h
  trans~ H1 H2 x = by
    have trans ∶ ({A : Set} {a b c : A} -> a ≡ b -> b ≡ c -> a ≡ c) 
      := (λ {refl refl -> refl}) ,,
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
    intro n ,, intro ih ,,
    rw {P = λ x -> suc x ≡ suc n} ih , 
    reflexivity ∎
 