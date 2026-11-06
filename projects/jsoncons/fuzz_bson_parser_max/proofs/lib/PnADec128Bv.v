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

Module PNADBV.

(* [comment removed for export] *)
Lemma test_val E X : bv_unsigned (edenot E (EAlu ALU_SLTU (EAlu ALU_SUB X (ELit 0)) (ELit 1))) = (if bv_unsigned (edenot E X) =? 0 then 1 else 0).
Proof.
  cbn [edenot alu64 alu32 alu mul_div]. rewrite PNDBV.bv_sub_0. rewrite PNDBV.ltu1. apply PNDBV.bvu_if.
Qed.
Lemma test_iff E X : (1 <= bv_unsigned (edenot E (EAlu ALU_SLTU (EAlu ALU_SUB X (ELit 0)) (ELit 1))) <= 1 <-> bv_unsigned (edenot E X) = 0)
  /\ (0 <= bv_unsigned (edenot E (EAlu ALU_SLTU (EAlu ALU_SUB X (ELit 0)) (ELit 1))) <= 0 <-> bv_unsigned (edenot E X) <> 0).
Proof.
  rewrite test_val. destruct (Z.eqb_spec (bv_unsigned (edenot E X)) 0) as [Z0|NZ]; split; split; intros H; try lia; try assumption.
Qed.

(* [comment removed for export] *)
Lemma sxw_zero E X : bv_unsigned (edenot E (EAluw ALU_ADD X (ELit 0))) = 0 <-> bv_unsigned (edenot E X) mod 2 ^ 32 = 0.
Proof.
  pose proof (PNDBV.sextw_zero (edenot E X)) as H. cbn [edenot alu64 alu32 alu mul_div].
  destruct (Z.eqb_spec (bv_unsigned (sext 64 (low32 (edenot E X) + low32 (Z_to_bv 64 0)))) 0) as [A|A];
    destruct (Z.eqb_spec (bv_unsigned (edenot E X) mod 2 ^ 32) 0) as [B|B]; try discriminate H; split; intros; try assumption; contradiction.
Qed.

(* [comment removed for export] *)
Lemma sx32_zero E j v : ev E j = Z_to_bv 64 v -> 0 <= v <= 4294967295 -> bv_unsigned (edenot E (EExt true 0 4 (EVar j))) = 0 <-> v = 0.
Proof.
  intros Ej Hv. cbn [edenot]. rewrite Ej. unfold ext_val, ext_Z. rewrite (PNDBV.u_lit v) by lia.
  change (8 * Z.of_nat 0) with 0. change (2 ^ 0) with 1. rewrite Z.div_1_r. change (8 * Z.of_nat 4) with 32. change (8 * N.of_nat 4)%N with 32%N.
  rewrite (Z.mod_small v) by lia. rewrite Z_to_bv_unsigned.
  unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2 ^ 32). change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 64) with (2 ^ 64).
  destruct (Z_lt_le_dec v (2 ^ 31)) as [LT|GE].
  - rewrite (Z.mod_small (v + 2 ^ 31)) by lia. replace (v + 2 ^ 31 - 2 ^ 31) with v by lia. rewrite Z.mod_small by lia. reflexivity.
  - replace ((v + 2 ^ 31) mod 2 ^ 32) with (v + 2 ^ 31 - 2 ^ 32) by (apply (Z.mod_unique_pos _ _ 1); lia).
    replace (v + 2 ^ 31 - 2 ^ 32 - 2 ^ 31) with (v - 2 ^ 32) by lia.
    replace ((v - 2 ^ 32) mod 2 ^ 64) with (v - 2 ^ 32 + 2 ^ 64) by (apply (Z.mod_unique_pos _ _ (-1)); lia). lia.
Qed.
Lemma lw_zero E j v : 1 <= bv_unsigned (edenot E (EAlu ALU_SLTU (EAlu ALU_SUB (EExt true 0 4 (EVar j)) (ELit 0)) (ELit 1))) <= 1 ->
  ev E j = Z_to_bv 64 v -> 0 <= v <= 4294967295 -> v = 0.
Proof. intros H Ej Hv. apply (sx32_zero E j v Ej Hv). apply (proj1 (test_iff E _)). exact H. Qed.

(* [comment removed for export] *)
Lemma w_zero E X : 1 <= bv_unsigned (edenot E (EAlu ALU_SLTU (EAlu ALU_SUB (EAluw ALU_ADD X (ELit 0)) (ELit 0)) (ELit 1))) <= 1 -> bv_unsigned (edenot E X) mod 2 ^ 32 = 0.
Proof. intros H. apply (sxw_zero E X). apply (proj1 (test_iff E _)). exact H. Qed.
Lemma w_nonzero E X : 0 <= bv_unsigned (edenot E (EAlu ALU_SLTU (EAlu ALU_SUB (EAluw ALU_ADD X (ELit 0)) (ELit 0)) (ELit 1))) <= 0 -> bv_unsigned (edenot E X) mod 2 ^ 32 <> 0.
Proof. intros H Z0. apply (proj1 (proj2 (test_iff E _)) H). apply (sxw_zero E X). exact Z0. Qed.

(* [comment removed for export] *)
Definition XA : expr := EAlu ALU_OR (EAlu ALU_ADD (EMd M_MUL (ELit 16384) (EVar 37)) (EAlu ALU_AND (EVar 39) (ELit 16383))) (EVar 36).
Definition XB : expr := EAlu ALU_OR (EAlu ALU_OR (EMd M_MUL (ELit 4294967296) (EVar 35)) (EAlu ALU_SRL (EVar 35) (ELit 32))) (EVar 35).
Section Test.
Variables (hi lo : Z).
Hypothesis Fhi : 0 <= hi < 2 ^ 64.
Hypothesis Flo : 0 <= lo < 2 ^ 64.
Definition msb : Z := (32768 * hi) mod 2 ^ 64 / 2305843009213693952.
Definition hi32 : Z := hi / 4294967296.
Lemma msb_range : 0 <= msb <= 7.
Proof. unfold msb. pose proof (Z.mod_pos_bound (32768 * hi) (2 ^ 64) ltac:(lia)) as B. split; [apply Z.div_pos; lia|]. apply Z.lt_succ_r. apply Z.div_lt_upper_bound; lia. Qed.
Lemma hi32_range : 0 <= hi32 <= 4294967295.
Proof. unfold hi32. split; [apply Z.div_pos; lia|]. apply Z.lt_succ_r. apply Z.div_lt_upper_bound; lia. Qed.
Variable E : env.
Hypothesis E35 : ev E 35 = Z_to_bv 64 lo.
Hypothesis E36 : ev E 36 = Z_to_bv 64 hi.
Hypothesis E37 : ev E 37 = Z_to_bv 64 msb.
Hypothesis E39 : ev E 39 = Z_to_bv 64 hi32.
Lemma XA_val : bv_unsigned (edenot E XA) = Z.lor (PNDBV.parts0 hi) hi.
Proof.
  pose proof msb_range as Hm. pose proof hi32_range as Hh.
  unfold XA. cbn [edenot alu64 alu32 alu mul_div]. rewrite E36, E37, E39. PNDBV.bvz. unfold PNDBV.parts0, msb, hi32. reflexivity.
Qed.
Lemma XB_val : bv_unsigned (edenot E XB) = Z.lor (Z.lor ((4294967296 * lo) mod 2 ^ 64) (lo / 2 ^ 32)) lo.
Proof.
  unfold XB. cbn [edenot alu64 alu32 alu mul_div]. rewrite E35. PNDBV.bvz. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma A_nz : Z.lor (PNDBV.parts0 hi) hi mod 2 ^ 32 <> 0 -> (hi mod 2 ^ 49) * 2 ^ 64 + lo <> 0.
Proof.
  destruct (PNDBV.hi_fields hi Fhi) as (a & b & c & d & EQ & Ha & Hb & Hc & Hd).
  unfold PNDBV.parts0. rewrite (PNDBV.f_parts0 hi a b c d EQ Ha Hb Hc Hd), (PNDBV.f_mod49 hi a b c d EQ Ha Hb Hc Hd).
  rewrite (PNDBV.mod32_lor (2 ^ 14 * b + c) hi) by (clear -Hb Hc Fhi; lia).
  rewrite (Z.mod_small (2 ^ 14 * b + c)) by (clear -Hb Hc; lia). rewrite (PNDBV.f_mod32 hi a b c d EQ Ha Hb Hc Hd).
  intros NZ W0. apply NZ. apply PNDBV.lor_zero_iff. clear -W0 Hb Hc Hd Flo. lia.
Qed.
Lemma B_nz : Z.lor (Z.lor ((4294967296 * lo) mod 2 ^ 64) (lo / 2 ^ 32)) lo mod 2 ^ 32 <> 0 -> (hi mod 2 ^ 49) * 2 ^ 64 + lo <> 0.
Proof.
  pose proof (Z.div_mod lo (2 ^ 32) ltac:(lia)) as EL. pose proof (Z.mod_pos_bound lo (2 ^ 32) ltac:(lia)) as BL.
  assert (QL : 0 <= lo / 2 ^ 32 < 2 ^ 32). { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. change (2 ^ 32 * 2 ^ 32) with (2 ^ 64); lia. }
  pose proof (Z.mod_pos_bound (4294967296 * lo) (2 ^ 64) ltac:(lia)) as BM.
  assert (NN : forall x y, 0 <= x -> 0 <= y -> 0 <= Z.lor x y) by (intros x y Hx Hy; apply Z.lor_nonneg; split; assumption).
  pose proof (Z.mod_pos_bound hi (2 ^ 49) ltac:(lia)) as BH.
  intros NZ W0. apply NZ. assert (L0 : lo = 0) by (clear -W0 BH Flo; lia). rewrite L0. reflexivity.
Qed.
End Test.
End PNADBV.
