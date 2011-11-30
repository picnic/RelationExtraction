(****************************************************************************)
(*  RelationExtraction - Extraction of inductive relations for Coq          *)
(*                                                                          *)
(*  This program is free software: you can redistribute it and/or modify    *)
(*  it under the terms of the GNU General Public License as published by    *)
(*  the Free Software Foundation, either version 3 of the License, or       *)
(*  (at your option) any later version.                                     *)
(*                                                                          *)
(*  This program is distributed in the hope that it will be useful,         *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of          *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the           *)
(*  GNU General Public License for more details.                            *)
(*                                                                          *)
(*  You should have received a copy of the GNU General Public License       *)
(*  along with this program.  If not, see <http://www.gnu.org/licenses/>.   *)
(*                                                                          *)
(*  Copyright 2011 Pierre-Nicolas Tollitte <tollitte@ensiie.fr> CNAM-ENSIIE *)
(****************************************************************************)

open Host_stuff
open Pred

type htyp = Term.types option

type henv = {
  ind_refs : (ident * Libnames.reference) list;
  ind_grefs : (ident * Libnames.global_reference) list;
  cstrs : (ident * Term.constr) list;
}

let coq_get_fake_type () = None

let coq_functions = {
  h_get_fake_type = coq_get_fake_type;
}


(* Extraction of dependencies *)
let extract_dependencies henv =
  (* We need a list of references *)
  let refl = List.map (fun (_, c) -> 
    let i = begin match Term.kind_of_term c with
      | Term.Construct _ -> let ind, _ = Term.destConstruct c in
        let _, oib = Inductive.lookup_mind_specif (Global.env ()) ind in
        oib.Declarations.mind_typename
      | Term.Const c -> Names.id_of_string (Names.string_of_con c)
      | _ -> assert false
    end in
    
    (* Hack to remove the [module.]name which is not handle by the extraction 
       plugin *)
    let i = try
      let i = Names.string_of_id i in
      let pos = String.rindex i '.' + 1 in
      Names.id_of_string (String.sub i pos (String.length i - pos))
    with Not_found -> i in

    Libnames.Ident (Util.dummy_loc, i)
  ) henv.cstrs in
  (* Not required anymore (Coq bool is mapped to OCaml bool) *)
  (*let refl = (Libnames.Qualid 
    (Util.dummy_loc, Libnames.qualid_of_string "Coq.Init.Datatypes.bool"))::
    refl in *)
  Extract_env.full_extraction None refl


(* Generates mode arguments for nb parameters. *)
let rec gen_param_args nb =
  if nb = 0 then []
  else (gen_param_args (nb-1))@[nb]

let adapt_mode ind_ref mode = 
  let ind = Term.destInd (Libnames.constr_of_global (Nametab.global ind_ref)) in
  let _, oib = Inductive.lookup_mind_specif (Global.env ()) ind in
  let parameters = oib.Declarations.mind_arity_ctxt in
  let fil = List.filter ( fun (n, _, _) -> match n with
    | Names.Anonymous -> false
    | _ -> true ) parameters in
  let param_nb = List.length fil in
Printf.eprintf "nb_params : %d\n" param_nb;
  let mode = List.map (fun i -> i + param_nb) mode in
  (gen_param_args param_nb) @ mode

(* Checks if x is present in the list option l. *)
let rec list_mem_option x l = match l with
  | Some (a::tl) -> x = a || list_mem_option x (Some tl)
  | Some [] -> false
  | _ -> true


(* Gets the type of one inductive body *)
let get_user_arity = function
  | Declarations.Monomorphic m -> m.Declarations.mind_user_arity
  | _ -> Util.errorlabstrm "RelationExtraction"
                      (Pp.str "Cannot deal with polymorphic inductive arity")

let make_mode ind_glb user_mode =
  let ind = Term.destInd (Libnames.constr_of_global ind_glb) in
  let _, oib = Inductive.lookup_mind_specif (Global.env ()) ind in
  let typ = get_user_arity oib.Declarations.mind_arity in
  let (args_real, _) = Term.decompose_prod typ in
  let args_nb = List.length args_real in

  let args_imp = match Impargs.implicits_of_global ind_glb with
    | (_, a)::_ -> a
    | _ -> [] in

  let args = if args_nb > (List.length args_imp) then
    Array.to_list (Array.make args_nb false)
  else
    List.map Impargs.is_status_implicit args_imp in

  let rec rec_mode args i = match args with
    | [] -> []
    | a::tl_args -> if a then
(* This would be needed in the case where implicit arguments were not 
   parameters... *)
        (*MSkip::(rec_mode tl_args i)*)
(* The following line assumes that all implicit arguments are included in the
   mode. This is done by the adapt_mode function when implicit arguments are
   parameters. So we assume that all implicits arguments are parameters detected
   by adapt_mode. *)
        MSkip::(rec_mode tl_args (i+1))
      else if list_mem_option i user_mode then
        MInput::(rec_mode tl_args (i+1))
      else MOutput::(rec_mode tl_args (i+1)) in
  rec_mode args 1

