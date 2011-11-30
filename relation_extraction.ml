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

open Util
open Pp
open Printer
open Declarations
open Names
open Term
open Pattern
open Libnames
open Nametab
open Univ
open Miniml
open Common
open Extract_env
open Table
open Pred
open Coq_stuff


(************************)
(* Predicate extraction *)
(************************)


(* Main routine *)
let extract_relation_common dep ord ind_ref modes =
  (* Initial henv *)
  let ind_refs, ind_grefs = List.split (List.map ( fun (ind_ref, _) ->
    let ind = destInd (constr_of_global (global ind_ref)) in
    let _, oib = Inductive.lookup_mind_specif (Global.env ()) ind in
    let id = ident_of_string (string_of_id oib.mind_typename) in
    (id, ind_ref), (id, global ind_ref) ) modes) in
  let henv = { ind_refs = ind_refs; ind_grefs = ind_grefs; cstrs = [] } in
  
  (* Extractions *)
  let ids = List.map (fun ind_ref ->
    let ind = destInd (constr_of_global (global ind_ref)) in
    let _, oib = Inductive.lookup_mind_specif (Global.env ()) ind in
  (*let idrs = List.map (fun oib -> Ident (dummy_loc, oib.mind_typename)) 
             oibs in*)
  (*TODO: add irds to ind_refs if they are not present ? 
          ie no mode given, or fail ? *)
    ident_of_string (string_of_id oib.mind_typename)
  ) ind_ref in
  let extractions = List.map (fun id -> id, (None, ord)) ids in

  (* Modes *)
  let modes = List.map ( fun (ind_ref, mode) ->
    let ind_glb = global ind_ref in
    let ind = destInd (constr_of_global ind_glb) in
    let _, oib = Inductive.lookup_mind_specif (Global.env ()) ind in
    let id = ident_of_string (string_of_id oib.mind_typename) in
    (id, [make_mode ind_glb (Some (adapt_mode ind_ref mode))]) 
  ) modes in
  let eq_modes = [[MSkip;MInput;MOutput]; [MSkip;MOutput;MInput]; 
                  [MSkip;MInput;MInput]] in
  let modes = (ident_of_string "eq", eq_modes)::modes in

  (* Compilation *)
  let empty_env = {
    extr_modes = modes;
    extr_extractions = extractions;
    extr_specs = [];
    extr_trees = [];
    extr_mlfuns = [];
    extr_fixfuns = [];
    extr_henv = henv;
    extr_hf = coq_functions;
  } in
  let env = Host2spec.find_specifications empty_env in
  (*Printf.eprintf "%s\n" (pp_extract_env env);*)
  let env = try Pred.make_trees env with
    | RelationExtractionProp (Some p_id, s) -> errorlabstrm "RelationExtraction"
      (str ("Extraction failed at " ^ string_of_ident p_id ^ ": " ^ s))
    | RelationExtractionProp (None, s) -> errorlabstrm "RelationExtraction"
      (str ("Extraction failed: " ^ s))
  in
  let env = Pred.make_ml_funs env in
  (*Printf.eprintf "%s\n" (pp_extract_env env);*)

  (* Before generating the MiniML code, we first extract all the dependences *)
  let _ = if dep then extract_dependencies env.extr_henv else () in

  Minimlgen.gen_miniml env

let relation_extraction_single ind_ref modes =
  extract_relation_common false false [ind_ref] modes

let relation_extraction_single_order ind_ref modes =
  extract_relation_common false true [ind_ref] modes

let relation_extraction ind_ref modes =
  extract_relation_common true false (List.map fst modes) modes

let relation_extraction_order ind_ref modes =
  extract_relation_common true true (List.map fst modes) modes

let relation_extraction_fixpoint = relation_extraction


(* DEBUG: Displaying a constant idr:
let cstr = constr_of_global (global idr) in
constr_display cstr; let cst = destConst cstr in
let cst_body = Global.lookup_constant cst in
let cstr = match cst_body.Declarations.const_body with 
  Def cs -> Declarations.force cs in
constr_display cstr *)

 
let relation_extraction_fixpoint idr modes =
  let _ = idr, modes in ()

let extraction_print str =
  Printf.printf "%s\n" str
