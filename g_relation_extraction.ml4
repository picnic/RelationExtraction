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
(*  Copyright 2011, 2014 CNAM-ENSIIE                                        *)
(*                 Catherine Dubois <dubois@ensiie.fr>                      *)
(*                 David Delahaye <david.delahaye@cnam.fr>                  *)
(*                 Pierre-Nicolas Tollitte <tollitte@ensiie.fr>             *)
(****************************************************************************)


(*i camlp4deps: "parsing/grammar.cma" i*)

open Genarg
open Pp
open Relation_extraction

VERNAC ARGUMENT EXTEND mode
  | [ "(" global(id) "[" integer_list(mde) "]" "as" string(f) ")" ] -> [ (Some f, id, mde, None) ]
  | [ "(" global(id) "[" integer_list(mde) "]" ")" ] -> [ (None, id, mde, None) ]
END


VERNAC ARGUMENT EXTEND rec_style
  | [ "Struct" integer(i) ] -> [ Some (Pred.StructRec i) ]
  | [ "Counter" ] -> [ Some Pred.FixCount ]
  | [] -> [ None ]
END

VERNAC ARGUMENT EXTEND modewithrec
  | [ "(" global(id) "[" integer_list(mde) "]" rec_style(r) "as" string(f) ")" ] -> [ (Some f, id, mde, r) ]
  | [ "(" global(id) "[" integer_list(mde) "]" rec_style(r) ")" ] -> [ (None, id, mde, r) ]
END


VERNAC COMMAND EXTEND ExtractionRelation
| [ "Extraction" "Relation" mode_list(modes) ] ->
  [ relation_extraction modes ]
END

VERNAC COMMAND EXTEND ExtractionRelationRelaxed
| [ "Extraction" "Relation" "Relaxed" mode_list(modes) ] ->
  [ relation_extraction_order modes ]
END

VERNAC COMMAND EXTEND ExtractionRelationSingle
| [ "Extraction" "Relation" "Single" mode_list(modes) ] ->
  [ relation_extraction_single modes ]
END

VERNAC COMMAND EXTEND ExtractionRelationSingleRelaxed
| [ "Extraction" "Relation" "Single" "Relaxed" mode_list(modes) ] ->
  [ relation_extraction_single_order modes ]
END


VERNAC COMMAND EXTEND ExtractionRelationFixpoint
| [ "Extraction" "Relation" "Fixpoint" modewithrec_list(modes) ] ->
  [ relation_extraction_fixpoint modes ]
END

VERNAC COMMAND EXTEND ExtractionRelationFixpointRelaxed
| [ "Extraction" "Relation" "Fixpoint" "Relaxed" modewithrec_list(modes) ] ->
  [ relation_extraction_fixpoint_order modes ]
END


