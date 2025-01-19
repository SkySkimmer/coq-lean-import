From LeanImport Require Import Lean.


Redirect "core1.log" Lean Import "../dumps/core" 1 5584.

Fail Redirect "core2.log" Lean Import "../dumps/core" 5584 63566.

(* Redirect "core3.log" Lean Import "../dumps/core" 5086 63566. *)