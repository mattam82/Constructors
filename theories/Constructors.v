Require Export Constructors.Dynamic.

Declare ML Module "constructors_plugin".

(** A CPS version of the tactic that gives the constructor list directly
   to [tac]. *)

Ltac constructors_of ind tac :=
  let x := fresh in 
  constructors of ind in x ;
  let cs := eval cbv in x in
    clear x; tac cs. 
