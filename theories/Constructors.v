(************************************************************************************************)
(* Constructors plugin.                                                                         *)
(* Copyright (c) 2010-2015 Matthieu Sozeau <mattam@mattam.org>.                                 *)
(************************************************************************************************)

Require Export Constructors.Dynamic.

Declare ML Module "constructors".

(** A CPS version of the tactic that gives the constructor list directly
   to [tac]. *)

Ltac constructors_of ind tac :=
  let x := fresh "H" in 
  constructors of ind in x ;
  let cs := eval cbv in x in
    clear x; tac cs. 
