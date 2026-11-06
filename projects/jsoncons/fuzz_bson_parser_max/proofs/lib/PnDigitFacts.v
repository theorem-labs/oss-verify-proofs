(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec AxSymExec3.
Import AX2.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNDG.

(* [comment removed for export] *)
Lemma mag_pos x : 0 <= x < 2 ^ 32 -> x * 3435973837 / 2 ^ 35 = x / 10.
Proof.
  intros Hx. symmetry. apply (Zdiv_unique (x * 3435973837) (2 ^ 35) (x / 10) (2 * (x / 10) + (x mod 10) * 3435973837)).
  - pose proof (Z.mod_pos_bound x 10 ltac:(lia)). pose proof (Z.div_pos x 10 ltac:(lia) ltac:(lia)).
    assert (x / 10 < 429496730) by (apply Z.div_lt_upper_bound; lia). lia.
  - pose proof (Z.div_mod x 10 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma quot_pos x : 0 <= x < 2 ^ 32 ->
  (((((4294967296 * x) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368) = x / 10.
Proof.
  intros Hx. rewrite (Z.mod_small (4294967296 * x)) by lia.
  replace (4294967296 * x * 14757395259826634752) with ((x * 3435973837) * 2 ^ 64) by lia.
  rewrite Z.div_mul by lia. change 34359738368 with (2 ^ 35). apply mag_pos. exact Hx.
Qed.

Lemma mag_neg a : 1 <= a <= 2 ^ 31 -> - (1717986919 * a) / 2 ^ 34 + 1 = - (a / 10).
Proof.
  intros Ha.
  assert (Q : - (1717986919 * a) / 2 ^ 34 = - (a / 10) - 1); [|lia].
  symmetry. apply (Zdiv_unique (- (1717986919 * a)) (2 ^ 34) (- (a / 10) - 1) (2 ^ 34 - 6 * (a / 10) - (a mod 10) * 1717986919)).
  - pose proof (Z.mod_pos_bound a 10 ltac:(lia)). pose proof (Z.div_pos a 10 ltac:(lia) ltac:(lia)).
    assert (a / 10 < 214748365) by (apply Z.div_lt_upper_bound; lia).
    pose proof (Z.div_mod a 10 ltac:(lia)). lia.
  - pose proof (Z.div_mod a 10 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Local Lemma shamt34 : bv_unsigned (bv_and (Z_to_bv 64 34) (Z_to_bv 64 63)) = 34.
Proof. vm_compute. reflexivity. Qed.

Local Lemma wrap64_id z : 0 <= z < 2 ^ 64 -> bv_wrap 64 z = z.
Proof. intros Hz. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. exact Hz. Qed.

Local Lemma swrap32_id z : - 2 ^ 31 <= z < 2 ^ 31 -> bv_swrap 32 z = z.
Proof. intros Hz. apply bv_swrap_small. change (bv_half_modulus 32) with (2 ^ 31). lia. Qed.
Local Lemma swrap64_id z : - 2 ^ 63 <= z < 2 ^ 63 -> bv_swrap 64 z = z.
Proof. intros Hz. apply bv_swrap_small. change (bv_half_modulus 64) with (2 ^ 63). lia. Qed.

(* [comment removed for export] *)
Lemma quot_neg (w : word) a : 1 <= a <= 2 ^ 31 -> w = Z_to_bv 64 (2 ^ 64 - a) ->
  sext 64 (low32 ((Z_to_bv 64 1717986919 * w) `ashiftr` bv_and (Z_to_bv 64 34) (Z_to_bv 64 63)) + low32 (Z_to_bv 64 1))
  = Z_to_bv 64 (- (a / 10)).
Proof.
  intros Ha ->. apply bv_eq. rewrite Z_to_bv_unsigned.
  unfold sext. rewrite bv_sign_extend_unsigned. rewrite bv_add_signed. unfold low32. rewrite !bv_extract_signed.
  rewrite bv_ashiftr_unsigned, shamt34, bv_mul_signed, !Z_to_bv_signed, !Z_to_bv_unsigned.
  change (Z.of_N 0) with 0. rewrite !Z.shiftr_0_r.
  assert (S1 : bv_swrap 64 1717986919 = 1717986919) by (vm_compute; reflexivity). rewrite S1.
  assert (S2 : bv_swrap 64 (2 ^ 64 - a) = - a).
  { rewrite <- (bv_swrap_wrap 64). unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    replace (2 ^ 64 - a) with (- a + 1 * 2 ^ 64) by lia. rewrite Z.mod_add by lia.
    change (- a mod 2 ^ 64) with (bv_wrap 64 (- a)). rewrite bv_swrap_wrap. apply swrap64_id. lia. }
  rewrite S2. replace (1717986919 * - a) with (- (1717986919 * a)) by lia.
  rewrite (swrap64_id (- (1717986919 * a))) by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  pose proof (mag_neg a Ha) as MG. set (q := - (1717986919 * a) / 2 ^ 34) in *.
  assert (Hq : - 214748365 - 1 <= q <= 0).
  { subst q. pose proof (Z.div_pos a 10 ltac:(lia) ltac:(lia)). assert (a / 10 < 214748365) by (apply Z.div_lt_upper_bound; lia). lia. }
  (* [comment removed for export] *)
  assert (W1 : bv_swrap 32 (bv_wrap 64 q) = q).
  { rewrite <- (bv_swrap_wrap 32 (bv_wrap 64 q)).
    assert (E : bv_wrap 32 (bv_wrap 64 q) = bv_wrap 32 q).
    { unfold bv_wrap. change (bv_modulus 64) with (2 ^ 32 * 2 ^ 32). change (bv_modulus 32) with (2 ^ 32).
      rewrite Z.rem_mul_r by lia. rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_mod. lia. }
    rewrite E, bv_swrap_wrap. apply swrap32_id. lia. }
  rewrite W1. change (bv_swrap 32 (bv_wrap 64 1)) with 1.
  rewrite (swrap32_id (q + 1)) by lia. rewrite MG. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma t0_neg (w : word) a : 1 <= a <= 2 ^ 31 -> w = Z_to_bv 64 (2 ^ 64 - a) ->
  (a <= 9 <-> 18446744073709551596 < bv_unsigned (sext 64 (low32 w + low32 (Z_to_bv 64 (-10))))).
Proof.
  intros Ha ->. unfold sext. rewrite bv_sign_extend_unsigned, bv_add_signed. unfold low32. rewrite !bv_extract_signed, !Z_to_bv_unsigned.
  change (Z.of_N 0) with 0. rewrite !Z.shiftr_0_r.
  rewrite (wrap64_id (2 ^ 64 - a)) by lia. change (bv_wrap 64 (-10)) with (2 ^ 64 - 10).
  rewrite <- (bv_swrap_wrap 32 (2 ^ 64 - a)), <- (bv_swrap_wrap 32 (2 ^ 64 - 10)).
  assert (E1 : bv_wrap 32 (2 ^ 64 - a) = bv_wrap 32 (- a)).
  { unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32). replace (2 ^ 64 - a) with (- a + (2 ^ 32) * 2 ^ 32) by lia. apply Z.mod_add. lia. }
  assert (E2 : bv_wrap 32 (2 ^ 64 - 10) = bv_wrap 32 (- 10)) by (vm_compute; reflexivity).
  rewrite E1, E2, !bv_swrap_wrap. rewrite (swrap32_id (- a)) by lia. rewrite (swrap32_id (-10)) by lia.
  (* [comment removed for export] *)
  destruct (Z_lt_le_dec (2 ^ 31 - 10) a) as [BIG|SMALL].
  - assert (S : bv_swrap 32 (- a + -10) = 2 ^ 32 - a - 10).
    { rewrite <- bv_swrap_wrap. unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32).
      replace (- a + -10) with ((2 ^ 32 - a - 10) + (-1) * 2 ^ 32) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
      apply swrap32_id. lia. }
    rewrite S. rewrite wrap64_id by lia. lia.
  - rewrite (swrap32_id (- a + -10)) by lia.
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    replace (- a + -10) with ((2 ^ 64 - a - 10) + (-1) * 2 ^ 64) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma slt0 v : - 2 ^ 63 <= v < 2 ^ 63 ->
  bv_unsigned (alu64 Instr.ALU_SLT (Z_to_bv 64 v) (Z_to_bv 64 0)) = (if v <? 0 then 1 else 0).
Proof.
  intros Hv. cbn [alu64 alu]. unfold bv_lts. rewrite !Z_to_bv_signed, (swrap64_id v), (swrap64_id 0) by lia.
  destruct (v <? 0); reflexivity.
Qed.

End PNDG.
