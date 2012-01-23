open Pred

exception RelExtNoFixTuple
exception RelExtImcompleteFunction

(**************)
(* Algorithms *)
(**************)

(* Tries to build all fix_fun from ml_fun. Pattern-matchings are compiled.
   Functions are completed if needed. *)
val build_all_fixfuns : 
(Term.constr option Host_stuff.host_term_type Host_stuff.host_term_type, Coq_stuff.henv Host_stuff.host_env Host_stuff.host_env) extract_env 
->
(Term.constr option Host_stuff.host_term_type Host_stuff.host_term_type, Coq_stuff.henv Host_stuff.host_env Host_stuff.host_env) extract_env 

