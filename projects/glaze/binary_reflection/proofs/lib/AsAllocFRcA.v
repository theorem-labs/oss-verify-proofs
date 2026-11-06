(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AsAinvDefs3.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
#[local] Abbreviation U := bv_unsigned.

(* [comment removed for export] *)
Lemma cls_of_off : forall c d, 0 <= c < 32 -> 0 <= d < 2 ^ 32 ->
  v_srli (v_slli (Z_to_bv 64 (c * 2 ^ 32 + d)) 27) 59 = Z_to_bv 64 c.
Proof.
  intros c d Hc Hd. (lazymatch goal with |- ?G => let G' := eval unfold v_srli, v_slli in G in change_no_check G' end). rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  rewrite (u_Z2bv (c * 2 ^ 32 + d)) by lia. rewrite u_Z2bv by lia. f_equal.
  assert (E : (c * 2 ^ 32 + d) * 2 ^ 27 = c * 2 ^ 59 + d * 2 ^ 27) by lia. rewrite E.
  rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
Qed.
(* [comment removed for export] *)
Lemma cls_of_off2 : forall c d, 0 <= c < 32 -> 0 <= d < 2 ^ 32 ->
  v_srli (Z_to_bv 64 (c * 2 ^ 32 + d)) 32 = Z_to_bv 64 c.
Proof.
  intros c d Hc Hd. (lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end). rewrite Z.shiftr_div_pow2 by lia. rewrite u_Z2bv by lia. f_equal.
  rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma csize_small : forall c, 1 <= c <= 16 -> v_slli (Z_to_bv 64 c) 5 = Z_to_bv 64 (csize c).
Proof.
  intros c Hc. (lazymatch goal with |- ?G => let G' := eval unfold v_slli, csize in G in change_no_check G' end). rewrite Z.shiftl_mul_pow2 by lia. rewrite u_Z2bv by lia.
  replace (c <=? 16) with true by (symmetry; apply Z.leb_le; lia). f_equal. lia.
Qed.
(* [comment removed for export] *)
Lemma csize_big : forall c, 17 <= c <= 30 ->
  let t := v_sll (Z_to_bv 64 512) (v_srli (v_addi (Z_to_bv 64 c) (-16)) 1) in
  v_add (v_and (v_srai (v_slli (Z_to_bv 64 c) 63) 63) (v_srli t 1)) t = Z_to_bv 64 (csize c).
Proof.
  intros c Hc.
  assert (E : c = 17 \/ c = 18 \/ c = 19 \/ c = 20 \/ c = 21 \/ c = 22 \/ c = 23 \/ c = 24 \/ c = 25 \/ c = 26 \/ c = 27 \/ c = 28 \/ c = 29 \/ c = 30) by lia.
  repeat (destruct E as [E | E]; [subst c; apply bv_eq; vm_compute; reflexivity |]). subst c. apply bv_eq. vm_compute. reflexivity.
Qed.
Lemma csize_pos : forall c, 1 <= c <= 30 -> 32 <= csize c <= 65536 /\ csize c mod 16 = 0.
Proof.
  intros c Hc.
  assert (E : c = 1 \/ c = 2 \/ c = 3 \/ c = 4 \/ c = 5 \/ c = 6 \/ c = 7 \/ c = 8 \/ c = 9 \/ c = 10 \/ c = 11 \/ c = 12 \/ c = 13 \/ c = 14 \/ c = 15
              \/ c = 16 \/ c = 17 \/ c = 18 \/ c = 19 \/ c = 20 \/ c = 21 \/ c = 22 \/ c = 23 \/ c = 24 \/ c = 25 \/ c = 26 \/ c = 27 \/ c = 28 \/ c = 29 \/ c = 30) by lia.
  repeat (destruct E as [E | E]; [subst c; vm_compute; repeat split; congruence |]). subst c. vm_compute. repeat split; congruence.
Qed.

(* [comment removed for export] *)
Lemma idx_divuw : forall c d cs, 0 <= c < 32 -> 0 <= d < 2 ^ 32 -> 1 <= cs < 2 ^ 31 ->
  v_srli (v_slli (v_divuw (Z_to_bv 64 (c * 2 ^ 32 + d)) (Z_to_bv 64 cs)) 32) 32 = Z_to_bv 64 (d / cs).
Proof.
  intros c d cs Hc Hd Hcs.
  assert (Q : 0 <= d / cs < 2 ^ 32).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia. }
  (lazymatch goal with |- ?G => let G' := eval unfold v_divuw in G in change_no_check G' end). rewrite !u_Z2bv by lia.
  assert (W1 : bv_wrap 32 (c * 2 ^ 32 + d) = d).
  { (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap in G in change_no_check G' end). change (bv_modulus 32) with (2 ^ 32). rewrite Z.add_comm, Z.mod_add by lia. apply Z.mod_small. lia. }
  assert (W2 : bv_wrap 32 cs = cs) by ((lazymatch goal with |- ?G => let G' := eval unfold bv_wrap in G in change_no_check G' end); change (bv_modulus 32) with (2 ^ 32); apply Z.mod_small; lia).
  rewrite W1, W2. replace (cs =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  (lazymatch goal with |- ?G => let G' := eval unfold v_srli, v_slli in G in change_no_check G' end). rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  apply bv_eq. rewrite !Z_to_bv_unsigned.
  (* [comment removed for export] *)
  set (q := d / cs) in *.
  assert (SW : exists k, bv_swrap 32 q = q + k * 2 ^ 32).
  { (lazymatch goal with |- ?G => let G' := eval unfold bv_swrap, bv_wrap in G in change_no_check G' end). change (bv_modulus 32) with (2 ^ 32). change (bv_half_modulus 32) with (2 ^ 31).
    exists (- ((q + 2 ^ 31) / 2 ^ 32)). pose proof (Z.div_mod (q + 2 ^ 31) (2 ^ 32) ltac:(lia)). lia. }
  destruct SW as (k & SW). rewrite SW.
  (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap in G in change_no_check G' end). change (bv_modulus 64) with (2 ^ 64).
  assert (E1 : ((q + k * 2 ^ 32) mod 2 ^ 64 * 2 ^ 32) mod 2 ^ 64 = q * 2 ^ 32).
  { rewrite Z.mul_mod_idemp_l by lia. replace ((q + k * 2 ^ 32) * 2 ^ 32) with (q * 2 ^ 32 + k * 2 ^ 64) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  rewrite E1. rewrite Z.div_mul by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma au_mask : forall au ce, 0 <= ce <= au -> au < 2 ^ 64 ->
  v_addi (v_sltu (Z_to_bv 64 au) (Z_to_bv 64 ce)) (-1) = Z_to_bv 64 18446744073709551615.
Proof.
  intros au ce H1 H2. (lazymatch goal with |- ?G => let G' := eval unfold v_sltu, c_ltu, bv_ltu in G in change_no_check G' end). rewrite !u_Z2bv by lia.
  replace (au <? ce) with false by (symmetry; apply Z.ltb_ge; lia). apply bv_eq. vm_compute. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma andi31 : forall c, 0 <= c < 32 -> v_andi (Z_to_bv 64 c) 31 = Z_to_bv 64 c.
Proof.
  intros c Hc. (lazymatch goal with |- ?G => let G' := eval unfold v_andi in G in change_no_check G' end). rewrite u_Z2bv by lia. f_equal.
  change (bv_wrap 64 31) with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.
(* [comment removed for export] *)
Lemma cls_shl32 : forall c, 0 <= c < 32 -> v_slli (Z_to_bv 64 c) 32 = Z_to_bv 64 (c * 2 ^ 32).
Proof. intros c Hc. (lazymatch goal with |- ?G => let G' := eval unfold v_slli in G in change_no_check G' end). rewrite Z.shiftl_mul_pow2 by lia. rewrite u_Z2bv by lia. reflexivity. Qed.
Lemma cls_shl7 : forall c, 0 <= c < 32 -> v_slli (Z_to_bv 64 c) 7 = Z_to_bv 64 (128 * c).
Proof. intros c Hc. (lazymatch goal with |- ?G => let G' := eval unfold v_slli in G in change_no_check G' end). rewrite Z.shiftl_mul_pow2 by lia. rewrite u_Z2bv by lia. f_equal. lia. Qed.
