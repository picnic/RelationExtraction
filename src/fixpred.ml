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
(*  Copyright 2011, 2012 CNAM-ENSIIE                                        *)
(*                 Catherine Dubois <dubois@ensiie.fr>                      *)
(*                 David Delahaye <david.delahaye@cnam.fr>                  *)
(*                 Pierre-Nicolas Tollitte <tollitte@ensiie.fr>             *)
(****************************************************************************)

open Pred
open Coq_stuff
open Host_stuff
open Minimlgen
open Proof_scheme

open Term
open Names
open Declarations
open Util
open Pp
open Nametab
open Libnames

exception RelExtNoFixTuple
exception RelExtImcompleteFunction

let flatmap f l = List.flatten (List.map f l)


(* Pattern matching compilation *)

(* Renames the term if i is not present in the pattern. *)
let rec rename_var_pattern oi ni (p, ty) = match p with
  | MLPVar vi when vi = oi -> MLPVar ni, ty
  | MLPTuple pl -> MLPTuple (List.map (rename_var_pattern oi ni) pl), ty
  | MLPRecord (il, pl) -> 
    MLPRecord (il, List.map (rename_var_pattern oi ni) pl), ty
  | MLPConstr (i, pl) -> 
    MLPConstr (i, List.map (rename_var_pattern oi ni) pl), ty
  | _ -> p, ty

(* Renames a variable in a term. *)
let rec rename_var_term oi ni (t, ty) = match t with
  | MLTVar vi when vi = oi -> MLTVar ni, ty
  | MLTASome t -> MLTASome (rename_var_term oi ni t), ty
  | MLTTuple tl -> MLTTuple (List.map (rename_var_term oi ni) tl), ty
  | MLTRecord (il, tl) -> 
    MLTRecord (il, List.map (rename_var_term oi ni) tl), ty
  | MLTConstr (i, tl) -> MLTConstr (i, List.map (rename_var_term oi ni) tl), ty
  | MLTFun (i, tl, m) -> MLTFun (i, List.map (rename_var_term oi ni) tl, m), ty
  | MLTFunNot (i, tl, m) -> 
    MLTFunNot (i, List.map (rename_var_term oi ni) tl, m), ty
  | MLTMatch (t, an, ptl) -> MLTMatch (rename_var_term oi ni t, an,
    List.map (fun (p,t,an) -> 
      rename_var_pattern oi ni p, rename_var_term oi ni t, an) ptl), ty
  | MLTALin _ -> anomalylabstrm "RelationExtraction" (str "Not implanted yet")
  | _ -> t, ty

(* Extracts the first column of a patterns matrix. *)
let rec extract_one_col pltl = match pltl with
  | [] -> [], []
  | (p::pl_tail, t, an)::pltl_tail -> 
    let col, npltl = extract_one_col pltl_tail in
    p::col, (pl_tail,t,an)::npltl
  | _ -> assert false


(* Merges a column into a patterns matrix. *)
let merge_col pl pltl = List.map2 (fun p (pl, t, an) -> p::pl, t, an) pl pltl
(* Same function but with list of patterns in the "column". *)
let merge_cols pll pltl = 
  List.map2 (fun pl2 (pl, t, an) -> pl2@pl, t, an) pll pltl

(* Explodes tuples into a patterns matrix. *)
let rec normalize_pltl_tuples tl pltl = match tl with
  | (MLTTuple tup, _)::tl_tail -> let ntl = tup@tl_tail in
    let tuple_col, npltl = extract_one_col pltl in
    let ncols = List.map (function
      | MLPTuple pl, _ -> pl
      | _ -> raise RelExtNoFixTuple
    ) tuple_col in
    let npltl = merge_cols ncols npltl in
    normalize_pltl_tuples ntl npltl
  | t::tl_tail -> let col, pltl_tail = extract_one_col pltl in
    let ntl, npltl = normalize_pltl_tuples tl_tail pltl_tail in
    t::ntl, merge_col col npltl
  | [] -> tl, pltl

(* pltl is a pattern matrix with a list of patterns and a term in each row.
 After normalization, each row must have the same number of pattern as tl 
 and must not contain any tuple. 
 If there is a default case, it is removed. *)
let rec normalize_pltl tl pltl =
  let npltl = List.filter (fun (pl, t, an) ->
    List.for_all (function MLPWild, _ -> false | _ -> true) pl
  ) pltl in
  normalize_pltl_tuples tl npltl

(* Generates the default case (None or False). *)
let gen_default_case env mode = 
  if is_full_extraction mode then fake_type env FixFalse
  else fake_type env FixNone

(* Gives a new fresh identifier for a variable. *)
let get_fresh_var =
  let i = ref 0 in
  fun () -> i := !i + 1; "fix_" ^ (string_of_int !i)

(* Makes a list of n fresh variables. *)
let rec make_cstr_pat_vars n =
  if n = 0 then [] 
  else (ident_of_string (get_fresh_var ())) :: (make_cstr_pat_vars (n-1))

(* Makes a list of n wild patterns. *)
let rec make_wild_pats env n =
  if n = 0 then [] else (fake_type env MLPWild) :: (make_wild_pats env (n-1))

(* Gets the type from a product. *)
let typ_from_named env ind (_,c) = match kind_of_term c with
  | Ind ind ->
    let _,idc = Inductive.lookup_mind_specif (Global.env ()) ind in
    CTSum (List.map (fun cstr_id  -> 
      (ident_of_string (string_of_id cstr_id))
    ) (Array.to_list idc.mind_consnames)), Some c (* c is the type of idc *)
  | Rel _ -> let ty = mkInd ind in
    let _,oib = Inductive.lookup_mind_specif (Global.env ()) ind in
    CTSum (List.map (fun cstr_id  -> 
      (ident_of_string (string_of_id cstr_id))
    ) (Array.to_list oib.mind_consnames)), Some ty
  | _ -> unknown_type env

(* Filters l2 with p applied on l1. *)
let rec filter2 p l1 l2 = match l1, l2 with
  | a::tl1, b::tl2 -> if p a then let l2 = filter2 p tl1 tl2 in
      b::l2
    else filter2 p tl1 tl2
  | _ -> l2

(* Finds the Coq type of constr *)
let coq_type_explorer env cstr = match kind_of_term cstr with
  | Construct (ind, i) ->
    let mib,oib = Inductive.lookup_mind_specif (Global.env ()) ind in
    let (n, _) = decompose_prod oib.mind_user_lc.(i-1) in
    let n = List.map (typ_from_named env ind) (List.rev n) in
(*basic imp args filter, TODO: unification with the host2spec algorithm ?*)
    let imp = match Impargs.implicits_of_global (
        Libnames.global_of_constr cstr) with
      | (_,a)::_ -> a
      | _ -> [] in
    let filter = fun a -> not (Impargs.is_status_implicit a) in
    let n = if List.length n <> List.length imp then n
      else filter2 filter imp n in
(*end*)
    List.length n, n
  | _ -> assert false

(* Finds the list of constructors of a coq inductive type. *)
let clear_type_from_coq typ = match kind_of_term typ with
  | Ind ind -> 
    let _,oib = Inductive.lookup_mind_specif (Global.env ()) ind in
    let cstrs_names = List.map (fun n -> ident_of_string (string_of_id n))
      (Array.to_list oib.mind_consnames) in
    CTSum cstrs_names

(* Gets the arity and types of the arguments of a constructor by searching it 
 in the first column of a patterns matrix. 
 If the constructor is not present in the first column, tries to find it using
 the cstr's id and the spec. *)
(* TODO: better handle for the case : (0, []), done ?*)
let rec get_cstr_arity_and_types env cstr pltl = match pltl with
  | [] -> let cstr = try List.assoc cstr env.extr_henv.cstrs with Not_found -> 
      anomalylabstrm "RelationExtraction" 
      (str "Cannot find a constructor in the extraction environment") in
    coq_type_explorer env cstr
  | ((MLPConstr (c, args), _)::_, _, _)::_ when c = cstr ->
    (List.length args, List.map snd args)
  | _::pltl_tail -> get_cstr_arity_and_types env cstr pltl_tail

(* filtering useless cases *)
let filter_next_pats pltl tl = 
  let rec filter_pll pll tl = match tl with
    | [] -> pll, tl
    | t::tl_tail -> try 
      let npll, ntl = filter_pll (List.map List.tl pll) tl_tail in
      if List.for_all (function | (MLPWild, _)::_ -> true | _ -> false) pll then 
        npll, ntl
      else List.map2 (fun pl npl -> (List.hd pl)::npl) pll npll, t::ntl 
    with _ -> assert false in
  let filtered_pll, ntl = 
    filter_pll (List.map (fun (pl, t, an) -> pl) pltl) tl in
  (List.map2 (fun pl (_,t,an) -> pl, t, an) filtered_pll pltl, ntl)

(* Compiles a normalized pattern matching. *)
let rec compile_fix_match comp (env, id_fun) binded_vars tl pltl = match tl with
  | [] -> begin match pltl with
    | [[], t, _] -> build_fix_term comp (env, id_fun) binded_vars t
               (* no more terms to match *)
    | _ -> assert false
  end
  | (mt, ((CTNone, _) ))::_ -> anomalylabstrm "RelationExtraction"
                                 (str "Missing type information")
  | (mt, ((CTSum cstr_list, _) as mt_ty))::tl_tail ->
    (* match mt with the first pattern of every pl present in pltl *)

    (* are there any variables or constructors in the patterns ? *)
    let is_variables = List.exists (fun (pl, _, _) -> match pl with 
      | p::_ -> (match p with | MLPVar _, _ -> true | _ -> false)
      | _ -> assert false) pltl in
    let is_constrs = List.exists (fun (pl, _, _) -> match pl with 
      | p::_ -> (match p with | MLPConstr _, _ -> true | _ -> false)
      | _ -> assert false) pltl in
    let an = flatmap (fun (_, _, an) -> an) pltl in
    let nmt, lams, npltl = if is_variables then 
        let nvar = ident_of_string (get_fresh_var ()) in
        (* if there is at least one variable: we create a variable for 
                                                                    the letin *)
        let npltl = List.map ( fun (pl, t, an) -> match pl with
          | (MLPVar v, vty)::pl_tail -> 
                (MLPWild, vty)::pl_tail, rename_var_term v nvar t, an
          (* then we replace each occurence of the variables by the 
             letin variable; v is no longer needed -> replaced by MLPWild *)
          | _ -> pl, t, an
        ) pltl in
        ( build_fix_term comp (env, id_fun) binded_vars (MLTVar nvar, mt_ty),
          (* The pattern matching is done on the letin var to avoid 
                                                            multiple calculi. *)
          [nvar, build_fix_term comp (env, id_fun) binded_vars (mt, mt_ty)],
          npltl )
      else 
        (build_fix_term comp (env, id_fun) binded_vars (mt, mt_ty)), [], pltl in
    let anlams = flatmap (fun (pl, _, an) -> match pl with
      | (MLPVar _, _)::_ -> an
      | _ -> []
    ) pltl in
      
    let nterm = if is_constrs then
      let pats = List.map (fun cstr -> (* one pattern for each constr *)
        let cstr_arity, args_types = get_cstr_arity_and_types env cstr npltl in
        let wild_pats = make_wild_pats env cstr_arity in
        (* pat_vars will be used as arguments in the pattern. *)
        let pat_vars = make_cstr_pat_vars cstr_arity in
        (* next_pats will be added to the patterns matrix. *)
        let next_pats = flatmap (fun (pl, t, an) -> match pl with
          | (MLPConstr (c, args), ty)::pl_tail when c = cstr ->
            (* when an argument is a var, it is replaced by the pat_var;
               when it is a contr, it is left untouched. *)
            [List.fold_right2 (fun (a, ty) pv (pl, t, an) -> match a with
              | MLPVar v -> ((MLPWild, ty)::pl, rename_var_term v pv t, an)
              | _ -> ((a, ty)::pl, t, an)
            ) args pat_vars (pl_tail, t, an)]
          | (MLPWild, ty)::pl_tail -> [(wild_pats@pl_tail, t, an)]
          | _ -> []
        ) npltl in
        let ntl = (List.map2 (fun v ty -> 
          (MLTVar v, ty)) pat_vars args_types)@tl_tail in
        (* filter patterns for which we have only wildcards. *)
        let next_pats, ntl = filter_next_pats next_pats ntl in

        (* filter annotations, the cstr wust be in the pattern *)
        let ancstr = flatmap (fun (pl, _, an) -> match pl with
          | (MLPConstr (c, _), _)::_ when c = cstr -> an
          | _ -> []
        ) npltl in

        if List.length next_pats = 0 then
          (* TODO: if full extraction => false *)
          if is_full_extraction (List.hd (extr_get_modes env id_fun)) then
            (pat_vars, gen_default_case env 
              (List.hd (extr_get_modes env id_fun)), ancstr)
          else if comp then 
            (pat_vars, gen_default_case env 
              (List.hd (extr_get_modes env id_fun)), ancstr)
          else raise RelExtImcompleteFunction
        else
          (pat_vars, compile_fix_match comp 
            (env, id_fun) binded_vars ntl next_pats, ancstr)
      ) cstr_list in
      (FixCase (nmt, an, pats), (CTNone, None))

      else (* only variables: no pattern matching needed *)
        let ntl = List.tl tl in
        let _, npltl = extract_one_col npltl in
        compile_fix_match comp (env, id_fun) binded_vars ntl npltl in
      List.fold_right (fun (i, l) t -> 
        FixLetin (i, l, t, anlams), (CTNone, None)) lams nterm



(* Builds a fix_term, destructuring complex pattern matchings. *)
and build_fix_term c (env, id_fun) binded_vars (t,ty) = match t with
(* TODO: check if there are renaming matches, if not, add the Some constr. *)
  | MLTVar i -> FixVar i, ty
  | MLTTuple tl -> raise RelExtNoFixTuple
  | MLTConstr (i, tl) -> 
    FixConstr (i, List.map (build_fix_term c (env, id_fun) binded_vars) tl), ty
  | MLTConst i -> FixConst i, ty
  | MLTFun (i, tl, _) -> 
    FixFun (i, List.map (build_fix_term c (env, id_fun) binded_vars) tl), ty
  | MLTFunNot (i, tl, _) -> 
    FixFunNot (i, List.map (build_fix_term c (env, id_fun) binded_vars) tl), ty
  | MLTMatch (t, _, ptl) ->
    let tl, pltl = normalize_pltl 
      [t] (List.map (fun (p, t, an) -> [p], t, an) ptl) in
    compile_fix_match c (env, id_fun) binded_vars tl pltl
  | MLTALin _ -> anomalylabstrm "RelationExtraction" (str "Not implanted yet")
  | MLTATrue -> FixTrue, ty
  | MLTAFalse -> FixFalse, ty
  | MLTANone -> FixNone, ty
  | MLTASome t -> FixSome (build_fix_term c (env, id_fun) binded_vars t), ty
  | MLTADefault -> 
    if is_full_extraction (List.hd (extr_get_modes env id_fun)) then 
      fake_type env FixFalse
    else fake_type env FixNone
  | _ -> anomalylabstrm "RelationExtraction" (str "Not implanted yet")


(* Transform added pattern constrs (the ones with an A) to basic pattern
   constrs. *)
let rec transform_pat_constrs (lpat, ty) = match lpat with
  | MLPTuple pl -> MLPTuple (transform_pat_constrs_list pl), ty
  | MLPRecord (il, pl) -> MLPRecord (il, transform_pat_constrs_list pl), ty
  | MLPConstr (i, pl) -> MLPConstr (i, transform_pat_constrs_list pl), ty
  | MLPATrue -> MLPConstr (ident_of_string "true", []), 
    (CTSum [ident_of_string "true";ident_of_string "false"], 
     Some (constr_of_global 
       (locate (qualid_of_string "Coq.Init.Datatypes.bool"))))
  | MLPAFalse -> MLPConstr (ident_of_string "false", []), 
    (CTSum [ident_of_string "true";ident_of_string "false"], 
      Some (constr_of_global
        (locate (qualid_of_string "Coq.Init.Datatypes.bool"))))
  | MLPASome p -> 
    MLPConstr (ident_of_string "Some", [transform_pat_constrs p]), ty
  | MLPANone -> MLPConstr (ident_of_string "None", []), ty
  | _ -> lpat, ty
and transform_pat_constrs_list lpat_list =
  List.map transform_pat_constrs lpat_list

(* Transform added constrs (the ones with an A) to basic constrs. *)
let rec transform_constrs (lterm, ty) = match lterm with
  | MLTTuple tl -> MLTTuple (transform_constrs_list tl), ty
  | MLTRecord (il, tl) -> MLTRecord (il, transform_constrs_list tl), ty
  | MLTConstr (i, tl) -> MLTConstr (i, transform_constrs_list tl), ty
  | MLTFun (i, tl, m) -> MLTFun (i, transform_constrs_list tl, m), ty
  | MLTFunNot (i, tl, m) -> MLTFunNot (i, transform_constrs_list tl, m), ty
  | MLTMatch (t, an, ptl) -> MLTMatch (transform_constrs t, an,
    List.map (fun (p, t, an) -> 
      transform_pat_constrs p, transform_constrs t, an) ptl), ty
  | MLTATrue -> MLTConstr (ident_of_string "true", []), 
    (CTSum [ident_of_string "true";ident_of_string "false"], 
      Some (constr_of_global 
        (locate (qualid_of_string "Coq.Init.Datatypes.bool"))))
  | MLTAFalse -> MLTConstr (ident_of_string "false", []), 
    (CTSum [ident_of_string "true";ident_of_string "false"], 
      Some (constr_of_global
        (locate (qualid_of_string "Coq.Init.Datatypes.bool"))))
  | MLTASome t -> MLTConstr (ident_of_string "Some", [transform_constrs t]), ty
  | MLTANone -> MLTConstr (ident_of_string "None", []), ty
  | _ -> lterm, ty
and transform_constrs_list lterm_list =
  List.map transform_constrs lterm_list

(* We must add this constructors: true, false, Some, None *)
let add_standard_constr_to_spec env = 
  let true_cstr = constr_of_global
    (locate (qualid_of_string "Coq.Init.Datatypes.true"))
  and false_cstr = constr_of_global
    (locate (qualid_of_string "Coq.Init.Datatypes.false"))
  and some_cstr = constr_of_global
    (locate (qualid_of_string "Coq.Init.Datatypes.Some"))
  and none_cstr = constr_of_global
    (locate (qualid_of_string "Coq.Init.Datatypes.None"))
  in 
let henv = { env.extr_henv with cstrs =
    (ident_of_string "true", true_cstr)::(ident_of_string "false", false_cstr)::
    (ident_of_string "None", none_cstr)::(ident_of_string "Some", some_cstr)::
    env.extr_henv.cstrs } in
  { env with extr_henv = henv }

(* Change the type of incomplete function with the option type. *)
let rec complete_fun_with_option env f = 
  let rec cfwo_rec (lterm, ty) = match lterm with
    | MLTVar _ | MLTTuple _ | MLTRecord _ | MLTConstr _ | MLTConst _ | MLTFun _ 
    | MLTFunNot _ | MLTATrue | MLTAFalse | MLTASome _ | MLTANone -> 
      if get_completion_status env f.mlfun_name then
        let opt = constr_of_global 
          (locate (qualid_of_string "Coq.Init.Datatypes.option")) in
        match ty with
        | _, Some ctyp ->
          let ctyp = Some (mkApp (opt, [|ctyp|])) in
          let typ = (CTSum [ident_of_string "Some";ident_of_string "None"], 
            ctyp) in
          MLTASome (lterm, ty), typ
        | _ -> assert false
      else lterm, ty
    | MLTMatch ((MLTFun(i,args,m), (_,Some ctyp)), an, ptl) 
    when get_completion_status env i -> 

     let opt = constr_of_global 
       (locate (qualid_of_string "Coq.Init.Datatypes.option")) in
     let ctyp = Some (mkApp (opt, [|ctyp|])) in
     let typ = (CTSum [ident_of_string "Some";ident_of_string "None"], ctyp) in
     MLTMatch ((MLTFun(i,args,m), typ), an,
       List.map (fun (p, t, an) -> match p with
         | MLPWild, _ -> p, cfwo_rec t, an
         | _ -> (MLPASome p, typ), cfwo_rec t, an) ptl), ty
    | MLTMatch (lt, an, ptl) -> MLTMatch (lt, an,
       List.map (fun (p, t, an) -> p, cfwo_rec t, an) ptl), ty
    | MLTALin _ -> lterm, ty
    | MLTADefault -> lterm, ty in
  {f with mlfun_body = cfwo_rec f.mlfun_body}

(* Generates a fix function from a ml function. *)
let build_fix_fun (env, id_fun) f =
  let build_f comp f =
    let t = transform_constrs f.mlfun_body in
    { fixfun_name = f.mlfun_name;
      fixfun_args = f.mlfun_args;
      fixfun_body = build_fix_term comp (env, id_fun) [] t; } in
  build_f (get_completion_status env f.mlfun_name) 
    (complete_fun_with_option env f)

(* Generates one fix function. *)
let gen_fix_fun env id =
  let f = extr_get_mlfun env id in
  build_fix_fun (env, id) f

(* TODO: For mutual recursive functions, the completion status
   of a function may depend on an other one. So this function 
   must be call until all the completion status remain the same. *)
let test_functions_completion env =
  let ids = List.map fst env.extr_mlfuns in
  List.fold_left (fun env id -> 
    try let _ = gen_fix_fun env id in env 
    with RelExtImcompleteFunction ->
      let f = extr_get_mlfun env id in
      { env with extr_compl = (f.mlfun_name, true)::env.extr_compl }
  ) env ids

let mk_pa_var fn sn = {
  pi_func_name = fn;
  pi_spec_name = sn;
}

let build_proof_scheme fixfun = 
  let rec rec_ps (ft, (ty, cty)) an = match ft with
    | FixCase (t, anmatch, iltl) -> let cstr_list = match t with
        | (_, (CTSum cl, _)) -> List.map string_of_ident cl
        | _ -> anomalylabstrm "RelationExtraction" 
                 (str "Missing type information") in
      List.flatten (List.map2 (fun (il, next_t, anpat) cstr ->
        let pall = rec_ps next_t anpat in
        List.map (fun (p, al) -> if List.exists (fun a -> match p with
            | Some pn -> a.pa_prop_name = pn
            | None -> false ) anpat then
          p, (CaseConstr (t, cstr, List.map 
            (fun i -> mk_pa_var (string_of_ident i) None) il))::al
        else p, (CaseDum (t, cstr, List.map 
               (fun i -> mk_pa_var (string_of_ident i) None) il))::al) pall
      ) iltl cstr_list)
    | FixLetin (i, t, next_t, an) -> let pall = rec_ps next_t an in
      List.map (fun (p, al) -> if List.exists (fun a -> match p with 
          | Some pn -> a.pa_prop_name = pn 
          | None -> false) an then
        p, LetVar (mk_pa_var (string_of_ident i) None, t)::al
      else p, LetDum (mk_pa_var (string_of_ident i) None, t)::al) pall
    | _ -> begin match an with 
      | [] -> [None, [OutputTerm None]]
      | [{pa_prop_name = pn; pa_renamings = _}] -> 
        [Some pn, [OutputTerm (Some (ft, (ty, cty)))]]
      | _ -> assert false
    end in
  let pall = rec_ps fixfun.fixfun_body [] in
  let branches = List.map (fun (p, al) -> let p = match p with
      | None -> None
      | Some p -> Some (string_of_ident p) in
    {psb_prop_name = p; psb_branch = al}) pall in
  { scheme_branches = branches; }

(* Build all fix functions. *)
let build_all_fixfuns env =
  let env = add_standard_constr_to_spec env in
  let env = test_functions_completion env in
  let ids = List.map fst env.extr_mlfuns in
  List.fold_left (fun env id -> 
    let fixfun = gen_fix_fun env id in
    { env with extr_fixfuns = (id, 
      (fixfun, build_proof_scheme fixfun))::env.extr_fixfuns }
  ) env ids
  
