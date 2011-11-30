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

(* Coq types. *)
type htyp = Term.types option

(* Coq environment. *)
type henv = {
  ind_refs : (ident * Libnames.reference) list;
  ind_grefs : (ident * Libnames.global_reference) list;
  cstrs : (ident * Term.constr) list;
}

(* Functions to manipulate Coq data. *)
val coq_functions : (htyp, henv) host_functions

(* Extraction of dependencies *)
val extract_dependencies : henv -> unit

(* Mode adapter for parameters. Must be used on all modes given by the user. *)
val adapt_mode : Libnames.reference -> int list -> int list

(* Mode conversion, with skipers for implicit arguments. If the mode is not provided,
   it returns the full mode.
   adapt_mode may be invoked prior to this function. *)
val make_mode : Libnames.global_reference -> (int list) option -> mode


