From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac ZBridge.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWalkKit.
Open Scope Z_scope.

(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac chk64 := lazymatch goal with |- context [negb (bv_eqb (Z_to_bv 64 ?A) (Z_to_bv 64 ?B))] =>
  let EQ := fresh "EQ" in
  assert (EQ : Z_to_bv 64 A = Z_to_bv 64 B);
  [ apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 64) with (2^64);
    rewrite ?swrap32_eq; rewrite ?Z.shiftl_mul_pow2 by lia; Z.div_mod_to_equations; lia
  | rewrite EQ; clear EQ; if_false ] end.

(* [comment removed for export] *)
Ltac shr61 := match goal with |- context [Z_to_bv 64 (?e ≫ 61)] =>
  replace (e ≫ 61) with 0 by (symmetry; rewrite Z.shiftr_div_pow2 by lia; apply Z.div_small;
    change (2^61) with 2305843009213693952; lia) end; if_false.
