From LeanImport Require Import Lean.


Redirect "core1.log" Lean Import "../dumps/core" 1 5584.

Fail Redirect "core2.log" Lean Import "../dumps/core" 5584 63566.

(* Redirect "core3.log" Lean Import "../dumps/core" 5086 63566. *)

Set Printing Universes.
Print String.
Print Char.
Print UInt32.
Eval hnf in LT_lt_inst1 Nat instLTNat.
Print Nat_le.
Print Or.
Print And.
Print Fin.
Print UInt32_isValidChar.
Print Nat_isValidChar.
Print UInt32_toNat.
(* Compute Z.of_nat (nat_of_Nat UInt32_size. *)
(* n < 0xd800 ∨ (0xdfff < n ∧ n < 0x110000) *)
(* Eval hnf in UInt32_isValidChar _. *)