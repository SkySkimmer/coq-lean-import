From LeanImport Require Import Lean.
(* Set Lean Error Mode "Skip". *)
(*
Redirect "init1.log" Lean Import "../dumps/init" 1 414836.
Set Lean Error Mode "Fail".

Fail Redirect "init2.log" Lean Import "../dumps/init" 414836 414837.
(* This fails because it expects to reduce a well-founded fixpoint in conversion mode,
   but the principal argument is Irrelevant so skip_irrelevant_stack does nonsense
   (mildly not a Coq bug since the fixpoint can only be defined
   thanks to acc being declared with unchecked univs)
*)
Set Lean Error Mode "Skip".

Redirect "init3.log" Lean Import "../dumps/init" 414837. *)
