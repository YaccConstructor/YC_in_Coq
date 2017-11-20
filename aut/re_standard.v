From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop path choice finset fingraph.

Require Import regexp.

Section Standard.
  Variable char: finType.
  
  Fixpoint standard (e: regular_expression char) :=
    match e with
        | Not _ => false
        | And _ _ => false
        | Dot => false
        | _ => true
    end.
End Standard.
