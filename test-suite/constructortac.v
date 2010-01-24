Require Import Constructors Bvector.

Ltac apply_in_dyn_list v :=
  match v with
    | cons (mkDyn _ ?x) ?rest => apply x || apply_in_dyn_list rest
    | nil => fail
  end.

Ltac constructor_of ind :=
  let x := fresh in
    constructors of ind in x ;
    let v := eval cbv in x in
      clear x;
      apply_in_dyn_list v.

Ltac constructor_tac := 
  match goal with
    | |- ?T => repeat constructor_of T
  end.

Goal vector nat (S 0).
constructor_tac. exact 0.
Defined.