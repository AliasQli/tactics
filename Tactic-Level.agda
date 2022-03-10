module Tactic-Level where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

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
  f g h : A -> B
  a b c : A
  U : 𝒰
  US : List 𝒰

map : ∀ {A B} -> (A -> B) -> List A -> List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

_++_ : ∀ {A} -> List A -> List A -> List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

data Env : List 𝒰 -> Setω where
  ∅   : Env []
  _◂_ : A -> Env US -> Env (⦅ A ⦆ ∷ US)
infixr 5 _◂_

record Inductive (A : Set u) : Setω where
  constructor induct
  field
    Types : (A -> Set v) -> List 𝒰
    induction : (a : A) -> Env (Types P ++ US) -> Env (⦅ P a ⦆ ∷ US)
open Inductive {{...}}

instance
  _ : Inductive Nat
  _ = record
    { Types = λ P -> ⦅ P zero ⦆ ∷ ⦅ (∀ n -> P n -> P (suc n)) ⦆ ∷ []
    ; induction = λ{ n (z ◂ f ◂ xs) -> helper n z f ◂ xs}
    }
      where
        helper : {P : Nat -> Set v} -> (n : Nat) -> P zero -> (∀ n -> P n -> P (suc n)) -> P n
        helper zero z f = z
        helper (suc n) z f = f n (helper n z f)
