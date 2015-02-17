(************************************************************************************************)
(* Constructors plugin.                                                                         *)
(* Copyright (c) 2010-2015 Matthieu Sozeau <mattam@mattam.org>.                                 *)
(************************************************************************************************)

Require Import Constructors.Constructors Bvector.

Ltac apply_in_dyn_list v :=
  match v with
    | cons (mkDyn _ ?x) ?rest => apply x || apply_in_dyn_list rest
    | nil => fail
  end.

Ltac constructor_of ind :=
  constructors_of ind ltac:(apply_in_dyn_list).

Ltac constructor_tac := 
  match goal with
    | |- ?T => repeat constructor_of T
  end.

Goal Bvector (S 0).
constructor_tac. exact true.
Defined.
