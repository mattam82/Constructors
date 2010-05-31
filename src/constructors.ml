(***********************************************************)
(* Copyright 2010 Matthieu Sozeau <mattam@mattam.org>      *)
(* This file is distributed under the terms of the         *)
(* GNU Lesser General Public License Version 2.1           *)
(***********************************************************)

(** Constructors - An example plugin and tactic for Coq

    This defines a tactic [constructors of c in id] that puts
    the list of constructors of the inductive type [c] in the 
    (fresh) hypothesis [id]. We build a [list dynamic] where 
    [dyn] is defined in a support file of the plugin
    (in theories/Dynamic.v) and is isomorphic to a sigma type.
*)

(* These are necessary for grammar extensions like the one at the end 
   of the module *)

(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmo" i*)

(* $$ *)

open Term
open Names
open Coqlib

(* Getting constrs (primitive Coq terms) from exisiting Coq libraries. *)

let find_constant contrib dir s =
  Libnames.constr_of_global (Coqlib.find_reference contrib dir s)

let contrib_name = "constructors"
let init_constant dir s = find_constant contrib_name dir s

let constructors_path = ["Constructors";"Dynamic"]

(* We use lazy as the Coq library is not yet loaded when we
   initialize the plugin, once [Constructors.Dynamic] is loaded 
   in the interpreter this will resolve correctly. *)

let coq_dynamic_ind = lazy (init_constant constructors_path "dyn")
let coq_dynamic_constr = lazy (init_constant constructors_path "mkDyn")
let coq_dynamic_type = lazy (init_constant constructors_path "dyn_type")
let coq_dynamic_obj = lazy (init_constant constructors_path "dyn_value")

(* Reflect the constructor of [dyn] values *)

let mkDyn ty value = 
  mkApp (Lazy.force coq_dynamic_constr, [| ty ; value |])

(* We also need lists from the standard library. *)

let list_path = ["Coq";"Init";"Datatypes"]
let coq_list_ind = lazy (init_constant list_path "list")
let coq_list_nil = lazy (init_constant list_path "nil")
let coq_list_cons = lazy (init_constant list_path "cons")

(* Now the real tactic. *)

let constructors env c =
  (* Decompose the application of the inductive type to params and arguments. *)
  let ind, args = Inductive.find_rectype env c in
  (* Find information about it (constructors, other inductives in the same block...) *)
  let mindspec = Global.lookup_inductive ind in
  (* The [list dyn] term *)
  let listty = mkApp (Lazy.force coq_list_ind, [| Lazy.force coq_dynamic_ind |]) in
  let listval =
    (* We fold on the constructors and build a [dyn] object for each one. *)
    Util.array_fold_right_i (fun i v l -> 
      (* Constructors are just referenced using the inductive type
	 and constructor number (starting at 1). *)
      let cd = mkConstruct (ind, succ i) in
      let d = mkDyn v cd in
	(* Cons the constructor on the list *)
	mkApp (Lazy.force coq_list_cons, [| Lazy.force coq_dynamic_ind; d; l |]))
      (* An array of types for the constructors, with parameters abstracted too. *)
      (Inductive.type_of_constructors ind mindspec)
      (* Our init is just the empty list *)
      (mkApp (Lazy.force coq_list_nil, [| Lazy.force coq_dynamic_ind |]))
  in listval, listty

open Tacmach
open Tacticals
open Tacexpr
open Tacinterp

(* A clause specifying that the [let] should not try to fold anything the goal
   matching the list of constructors (see [letin_tac] below). *)

let nowhere = { onhyps = Some []; concl_occs = Rawterm.no_occurrences_expr }

(* This adds an entry to the grammar of tactics, similar to what
   Tactic Notation does. There's currently no way to return a term 
   through an extended tactic, hence the use of a let binding. *)

TACTIC EXTEND constructors_of_in
| ["constructors" "of" constr(c) "in" ident(id) ] -> 
    [ fun gl -> (* The current goal *)
      let v, t = constructors (pf_env gl) c in
	(* Defined the list in the context using name [id]. *)
	Tactics.letin_tac None (Name id) v (Some t) nowhere gl
    ]
END

