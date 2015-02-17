(************************************************************************************************)
(* Constructors plugin.                                                                         *)
(* Copyright (c) 2010-2015 Matthieu Sozeau <mattam@mattam.org>.                                 *)
(************************************************************************************************)

Record dyn : Type := mkDyn {
  dyn_type : Type;
  dyn_value : dyn_type }.