(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import base.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec AxSymExec3 PnDecFacts PnDecBv.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNARVBV.

(* [comment removed for export] *)
Lemma sx32_u E j v : ev E j = Z_to_bv 64 v -> 0 <= v <= 4294967295 ->
  bv_unsigned (edenot E (EExt true 0 4 (EVar j))) = (if v <? 2 ^ 31 then v else v - 2 ^ 32 + 2 ^ 64).
Proof.
  intros Ej Hv. cbn [edenot]. rewrite Ej. unfold ext_val, ext_Z. rewrite (PNDBV.u_lit v) by lia.
  change (8 * Z.of_nat 0) with 0. change (2 ^ 0) with 1. rewrite Z.div_1_r. change (8 * Z.of_nat 4) with 32. change (8 * N.of_nat 4)%N with 32%N.
  rewrite (Z.mod_small v) by lia. rewrite Z_to_bv_unsigned.
  unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2 ^ 32). change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 64) with (2 ^ 64).
  destruct (Z.ltb_spec v (2 ^ 31)) as [LT|GE].
  - rewrite (Z.mod_small (v + 2 ^ 31)) by lia. replace (v + 2 ^ 31 - 2 ^ 31) with v by lia. rewrite Z.mod_small by lia. reflexivity.
  - replace ((v + 2 ^ 31) mod 2 ^ 32) with (v + 2 ^ 31 - 2 ^ 32) by (apply (Z.mod_unique_pos _ _ 1); lia).
    replace (v + 2 ^ 31 - 2 ^ 32 - 2 ^ 31) with (v - 2 ^ 32) by lia.
    replace ((v - 2 ^ 32) mod 2 ^ 64) with (v - 2 ^ 32 + 2 ^ 64) by (apply (Z.mod_unique_pos _ _ (-1)); lia). reflexivity.
Qed.
Lemma slt0_val E X : bv_unsigned (edenot E (EAlu ALU_SLT X (ELit 0))) = (if bv_unsigned (edenot E X) <? 2 ^ 63 then 0 else 1).
Proof.
  cbn [edenot alu64 alu32 alu mul_div]. unfold bv_lts.
  pose proof (bv_unsigned_in_range _ (edenot E X)) as RX. change (bv_modulus 64) with (2 ^ 64) in RX.
  assert (S0 : bv_signed (Z_to_bv 64 0) = 0) by reflexivity. rewrite S0.
  unfold bv_signed, bv_swrap, bv_wrap. change (bv_modulus 64) with (2 ^ 64). change (bv_half_modulus 64) with (2 ^ 63).
  destruct (Z.ltb_spec (bv_unsigned (edenot E X)) (2 ^ 63)) as [LT|GE].
  - rewrite (Z.mod_small (bv_unsigned (edenot E X) + 2 ^ 63)) by lia.
    destruct (Z.ltb_spec (bv_unsigned (edenot E X) + 2 ^ 63 - 2 ^ 63) 0) as [A|A]; [lia| reflexivity].
  - replace ((bv_unsigned (edenot E X) + 2 ^ 63) mod 2 ^ 64) with (bv_unsigned (edenot E X) + 2 ^ 63 - 2 ^ 64) by (apply (Z.mod_unique_pos _ _ 1); lia).
    destruct (Z.ltb_spec (bv_unsigned (edenot E X) + 2 ^ 63 - 2 ^ 64 - 2 ^ 63) 0) as [A|A]; [reflexivity| lia].
Qed.
(* [comment removed for export] *)
Lemma lw_nonneg E j v : 0 <= bv_unsigned (edenot E (EAlu ALU_SLT (EExt true 0 4 (EVar j)) (ELit 0))) <= 0 ->
  ev E j = Z_to_bv 64 v -> 0 <= v <= 4294967295 -> v < 2 ^ 31 /\ edenot E (EExt true 0 4 (EVar j)) = Z_to_bv 64 v.
Proof.
  intros H Ej Hv. rewrite slt0_val in H. pose proof (sx32_u E j v Ej Hv) as U.
  destruct (Z.ltb_spec v (2 ^ 31)) as [LT|GE].
  - split; [exact LT|]. apply bv_eq. rewrite U. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. reflexivity.
  - exfalso. rewrite U in H. destruct (Z.ltb_spec (v - 2 ^ 32 + 2 ^ 64) (2 ^ 63)) as [A|A]; lia.
Qed.
Lemma lw_neg E j v : 1 <= bv_unsigned (edenot E (EAlu ALU_SLT (EExt true 0 4 (EVar j)) (ELit 0))) <= 1 ->
  ev E j = Z_to_bv 64 v -> 0 <= v <= 4294967295 -> 2 ^ 31 <= v.
Proof.
  intros H Ej Hv. rewrite slt0_val in H. pose proof (sx32_u E j v Ej Hv) as U.
  destruct (Z.ltb_spec v (2 ^ 31)) as [LT|GE]; [| exact GE].
  exfalso. rewrite U in H. destruct (Z.ltb_spec v (2 ^ 63)) as [A|A]; lia.
Qed.

End PNARVBV.
