(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import StartupTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Definition tolower_w (x : word) : word := v_or x (v_slli (v_sltiu (v_addiw x (-65)) 26) 5).
Definition tolower_Z (c : Z) : Z := if ((65 <=? c) && (c <=? 90))%Z then (c + 32)%Z else c.

Lemma lor_32_add : forall c, (0 <= c)%Z -> Z.testbit c 5 = false -> Z.lor c 32 = (c + 32)%Z.
Proof.
  intros c Hc Hb. rewrite <- Z.lxor_lor.
  - symmetry. apply Z.add_nocarry_lxor. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.eq_dec i 5) as [->|Hne]; [rewrite Hb; reflexivity|].
    change 32%Z with (2 ^ 5)%Z. rewrite Z.pow2_bits_eqb by lia. replace (5 =? i)%Z with false by (symmetry; apply Z.eqb_neq; lia).
    apply andb_false_r.
  - apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.eq_dec i 5) as [->|Hne]; [rewrite Hb; reflexivity|].
    change 32%Z with (2 ^ 5)%Z. rewrite Z.pow2_bits_eqb by lia. replace (5 =? i)%Z with false by (symmetry; apply Z.eqb_neq; lia).
    apply andb_false_r.
Qed.

Lemma half_modulus_32 : bv_half_modulus 32 = 2147483648%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma tolower_w_spec : forall c, (0 <= c <= 255)%Z -> tolower_w (Z_to_bv 64 c) = Z_to_bv 64 (tolower_Z c).
Proof.
  intros c Hc. unfold tolower_w, tolower_Z, v_or, v_slli, v_sltiu, v_addiw.
  rewrite (u_Z2bv c) by lia.
  change (bv_wrap 64 26) with 26%Z.
  destruct (Z_lt_le_dec c 65) as [Hlo|Hlo].
  - rewrite (bv_swrap_small 32 (c + -65)) by (rewrite half_modulus_32; lia).
    replace (bv_unsigned (Z_to_bv 64 (c + -65)) <? 26)%Z with false.
    2:{ symmetry. apply Z.ltb_ge. rewrite Z_to_bv_unsigned. unfold bv_wrap.
        change (bv_modulus 64) with (2^64)%Z.
        replace (c + -65)%Z with ((2^64 + c - 65) + (-1) * 2^64)%Z by lia.
        rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia. }
    rewrite (u_Z2bv 0) by lia. rewrite Z.shiftl_0_l. rewrite (u_Z2bv 0) by lia. rewrite Z.lor_0_r.
    replace ((65 <=? c) && (c <=? 90))%Z with false by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia).
    reflexivity.
  - rewrite (bv_swrap_small 32 (c + -65)) by (rewrite half_modulus_32; lia).
    rewrite (u_Z2bv (c + -65)) by lia.
    destruct (Z_lt_le_dec 90 c) as [Hhi|Hhi].
    + replace (c + -65 <? 26)%Z with false by (symmetry; apply Z.ltb_ge; lia).
      rewrite (u_Z2bv 0) by lia. rewrite Z.shiftl_0_l. rewrite (u_Z2bv 0) by lia. rewrite Z.lor_0_r.
      replace ((65 <=? c) && (c <=? 90))%Z with false by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
      reflexivity.
    + replace (c + -65 <? 26)%Z with true by (symmetry; apply Z.ltb_lt; lia).
      rewrite (u_Z2bv 1) by lia. change (Z.shiftl 1 5) with 32%Z. rewrite (u_Z2bv 32) by lia.
      replace ((65 <=? c) && (c <=? 90))%Z with true by (symmetry; apply andb_true_iff; split; apply Z.leb_le; lia).
      f_equal. apply lor_32_add; [lia|].
      apply Z.testbit_false; [lia|]. change (2 ^ 5)%Z with 32%Z.
      replace (c / 32)%Z with 2%Z; [reflexivity|]. apply (Z.div_unique c 32 2 (c - 64)); lia.
Qed.

Lemma tolower_Z_range : forall c, (0 <= c <= 255)%Z -> (0 <= tolower_Z c <= 255)%Z.
Proof. intros c Hc. unfold tolower_Z. destruct ((65 <=? c) && (c <=? 90))%Z eqn:E; [|lia].
  apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. lia. Qed.


Definition tolower_clob : list reg := [10; 11]%list.

