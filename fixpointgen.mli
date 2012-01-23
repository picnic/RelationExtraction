open Pred
open Fixpred

(* Generates Coq Fixpoints and register them in the Coq environment. *)
val gen_fixpoint : 
(Term.constr option Host_stuff.host_term_type Host_stuff.host_term_type, Coq_stuff.henv Host_stuff.host_env Host_stuff.host_env) extract_env 
 -> unit

