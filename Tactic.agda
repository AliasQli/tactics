module Tactic where

open import Agda.Primitive
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Agda.Builtin.Nat

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

  sym : a ≡ b -> b ≡ a
  sym refl = refl

  trans : a ≡ b -> b ≡ c -> a ≡ c
  trans refl refl = refl

  cong : (f : A -> B) -> a ≡ b -> f a ≡ f b
  cong _ refl = refl

open Util

private variable
  A B C X : Set
  XS : List Set
  P : A -> Set
  a b : A

data Env : List Set -> Set where
  ∅   : Env []
  _◂_ : X -> Env XS -> Env (X ∷ XS)
infixr 20 _◂_

by_ : (Env [] -> Env (A ∷ [])) -> A
by tactics with tactics ∅
... | x ◂ ∅ = x
infixr 1 by_

_,_ : (B -> C) -> (A -> B) -> A -> C
f , g = λ x -> f (g x)
infixr 2 _,_

_∎ : A -> A
_∎ = id
infixl 1.5 _∎

record Casing (A : Set) : Set₁ where
  constructor casing
  field
    Types : List (Set -> Set)
    cases : A -> Env (map (λ t -> t X) Types ++ XS) -> Env (X ∷ XS)
open Casing {{...}}

record Inductive (A : Set) : Set₁ where
  constructor induct
  field
    Types : List ((A -> Set) -> Set)
    induction : (a : A) -> Env (map (λ t -> t P) Types ++ XS) -> Env (P a ∷ XS)
open Inductive {{...}}

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

exact : X -> Env XS -> Env (X ∷ XS)
exact = _◂_

reflexivity : Env XS -> Env ((a ≡ a) ∷ XS)
reflexivity = exact refl

apply : (A -> B) -> Env (A ∷ XS) -> Env (B ∷ XS)
apply f (a ◂ xs) = f a ◂ xs

apply2 : (A -> B -> C) -> Env (A ∷ B ∷ XS) -> Env (C ∷ XS)
apply2 f (a ◂ b ◂ xs) = f a b ◂ xs

rw : ∀ {u} {A : Set u} {P : A -> Set} {a b : A} -> a ≡ b -> Env (P b ∷ XS) -> Env (P a ∷ XS)
rw refl xs = xs

intro-syntax : ((a : A) -> Env [] -> Env (P a ∷ [])) -> Env XS -> Env (((a : A) -> P a) ∷ XS)
intro-syntax tactics xs = (λ a -> by tactics a) ◂ xs
syntax intro-syntax (λ a -> b) = intro a , b
infixr 2 intro-syntax

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
    intro n ,
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
  sym~ H x = by
    apply sym ,
    exact (H x) ∎

  trans~ : f ~ g -> g ~ h -> f ~ h
  trans~ H1 H2 x = by
    apply2 trans ,
    exact (H1 x) ,
    exact (H2 x) ∎


  zero-plus : ∀ n -> 0 + n ≡ n
  zero-plus n = by
    reflexivity ∎

  plus-zero : ∀ n -> n + 0 ≡ n
  plus-zero n = by
    induction {P = λ n -> n + 0 ≡ n} n ,
    reflexivity , 
    intro n , intro ih , 
    rw {P = λ x -> suc x ≡ suc n} ih , 
    reflexivity ∎
