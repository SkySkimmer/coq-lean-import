From LeanImport Require Import Lean.

Set Lean Error Mode "Stop".

Time Redirect "mathlib.log" Lean Import "/home/gaetan/dev/lean/library/mathlib.out".

(*
without hack first error at line 183121 (for int.div_zero)
with hack first error at line 210064 (for rat.one_mul)
 *)

Fail Check fun n d => fun x :
 has_mul_mul_inst1 rat rat_has_mul
    (rat_mk (has_one_one_inst1 int int_has_one) (has_one_one_inst1 int int_has_one))
    (rat_mk n (coe nat int (coe_to_lift nat int (coe_base nat int int_has_coe)) d)) =
  rat_mk n (coe nat int (coe_to_lift nat int (coe_base nat int int_has_coe)) d)
=>
x  :
 has_mul_mul_inst1 rat rat_has_mul (has_one_one_inst1 rat rat_has_one)
    (rat_mk n (coe nat int (coe_to_lift nat int (coe_base nat int int_has_coe)) d)) =
  rat_mk n (coe nat int (coe_to_lift nat int (coe_base nat int int_has_coe)) d).
