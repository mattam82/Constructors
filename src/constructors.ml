(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmo" i*)

(* $$ *)

open Term
open Names
open Coqlib

let find_constant contrib dir s =
  Libnames.constr_of_global (Coqlib.find_reference contrib dir s)

let contrib_name = "constructors"
let init_constant dir s = find_constant contrib_name dir s
let init_reference dir s = Coqlib.find_reference contrib_name dir s

let constructors_path = ["Constructors";"Dynamic"]
let coq_dynamic_ind = lazy (init_constant constructors_path "dyn")
let coq_dynamic_constr = lazy (init_constant constructors_path "mkDyn")
let coq_dynamic_type = lazy (init_constant constructors_path "dyn_type")
let coq_dynamic_obj = lazy (init_constant constructors_path "dyn_value")

let mkDyn ty value = 
  mkApp (Lazy.force coq_dynamic_constr, [| ty ; value |])

let list_path = ["Coq";"Init";"Datatypes"]
let coq_list_ind = lazy (init_constant list_path "list")
let coq_list_nil = lazy (init_constant list_path "nil")
let coq_list_cons = lazy (init_constant list_path "cons")

open Tacmach
open Tacticals
open Tacexpr

let nowhere = { onhyps = Some []; concl_occs = Rawterm.no_occurrences_expr }

let constructors c id gl =
  let ind, args = Inductive.find_rectype (pf_env gl) c in
  let mindspec = Global.lookup_inductive ind in
  let listty = mkApp (Lazy.force coq_list_ind, [| Lazy.force coq_dynamic_ind |]) in
  let listval =
    Util.array_fold_right_i (fun i v l -> 
      let cd = mkConstruct (ind, succ i) in
      let d = mkDyn v cd in
	mkApp (Lazy.force coq_list_cons, [| Lazy.force coq_dynamic_ind; d; l |]))
      (Inductive.type_of_constructors ind mindspec)
      (mkApp (Lazy.force coq_list_nil, [| Lazy.force coq_dynamic_ind |]))
  in
    Tactics.letin_tac None (Name id) listval (Some listty) nowhere gl

TACTIC EXTEND constructors
| ["constructors" "of" constr(c) "in" ident(id) ] -> 
    [ constructors c id ]
END

