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

(* Host is the host language (Coq or Focalize). In order to generate 
   functions, we need to keep information from these languages. Some part 
   (mostly typing information) is kept into the AST we manipulate by compiling 
   the predicates and the remaining part is kept into an host environment. 
*)

(* Type information for a term. This is kept into the AST. *)
type 'htyp host_term_type = 'htyp

(* Environment for host stuff. *)
type 'henv host_env = 'henv

(* Functions for host langage manipulations. *)
type ('htyp, 'henv) host_functions = {
  h_get_fake_type : unit -> 'htyp host_term_type;
}


