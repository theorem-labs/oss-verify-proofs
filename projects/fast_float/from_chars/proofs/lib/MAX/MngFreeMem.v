(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3 SeqExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngWb MngFree AXF_p4z AXF_tfz.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Lemma u_vaddi' : forall (w : word) k, 0 <= bv_unsigned w + k < 2^64 -> bv_unsigned (v_addi w k) = bv_unsigned w + k.
Proof. intros w k H. unfold v_addi. apply u_small. exact H. Qed.

Ltac side := cbn [length word_to_le_bytes Z_to_le_bytes]; (rewrite ?u_vaddi', ?u_wa_small by lia); lia.
Ltac peel := rewrite MngWb.wbytes_out by side.

(* [comment removed for export] *)
Section P4M.
Variables (m : word -> option byte) (regs : bvmap 5 word).
Hypothesis Hsp : 2^20 <= bv_unsigned (getr regs 2) <= 2^47.

#[using="Hsp"] Lemma p4_mem_out : forall x, 0 <= x < 2^64 -> ~ (bv_unsigned (getr regs 2) - 40 <= x < bv_unsigned (getr regs 2)) ->
  p4_mem m regs (wa x) = m (wa x).
Proof. LiaFast.lf_pins (fun (Hsp : LiaFast.U) => LiaFast.u0). intros x Hx H1. unfold p4_mem. do 5 peel. reflexivity. Qed.

#[using="Type"] Lemma p4_mem_grows : mem_grows m (p4_mem m regs).
Proof. LiaFast.lf_pins LiaFast.u0.
  unfold p4_mem. repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl.
Qed.

#[using="Hsp"] Lemma p4_rdn_other : forall a n, 0 <= a -> a + Z.of_nat n <= bv_unsigned (getr regs 2) - 40 ->
  rdn SEGS (p4_mem m regs) (wa a) n = rdn SEGS m (wa a) n.
Proof. LiaFast.lf_pins (fun (Hsp : LiaFast.U) => LiaFast.u0).
  intros a n H1 H2. pose proof (u64_range (getr regs 2)) as R.
  assert (Ha : bv_unsigned (wa a) = a) by (apply u_wa_small; lia).
  unfold p4_mem. do 5 (rewrite rdn_wbytes_below; [| rewrite Ha; cbn [length word_to_le_bytes Z_to_le_bytes]; unfold v_addi; rewrite ?u_small by lia; lia
                                                 | cbn [length word_to_le_bytes Z_to_le_bytes]; unfold v_addi; rewrite ?u_small by lia; lia]).
  reflexivity.
Qed.

#[using="Hsp"] Lemma p4_rdn_save : forall k (r : bvmap 5 word -> word), In (k, r) [(8, fun R => getr R 1); (16, fun R => getr R 8); (24, fun R => getr R 9); (32, fun R => getr R 18); (40, fun R => getr R 19)] ->
  rdn SEGS (p4_mem m regs) (wa (bv_unsigned (getr regs 2) + - k)) 8 = Some (word_to_le_bytes 8 (r regs)).
Proof. LiaFast.lf_pins (fun (Hsp : LiaFast.U) => LiaFast.u0).
  intros k r Hk. pose proof (u64_range (getr regs 2)) as R.
  cbn [In] in Hk. unfold p4_mem.
  destruct Hk as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-.
  - do 4 (rewrite rdn_wbytes_disjoint; [| cbn [length word_to_le_bytes Z_to_le_bytes]; rewrite ?u_vaddi', ?u_wa_small by lia; lia | rewrite ?u_vaddi', ?u_wa_small by lia; lia]).
    replace (wa (bv_unsigned (getr regs 2) + -8)) with (v_addi (getr regs 2) (-8)) by reflexivity.
    apply (rdn_wbytes_hit SEGS (word_to_le_bytes 8 (getr regs 1))). cbn [length word_to_le_bytes Z_to_le_bytes]. unfold v_addi. rewrite ?u_small by lia. lia.
  - do 3 (rewrite rdn_wbytes_disjoint; [| cbn [length word_to_le_bytes Z_to_le_bytes]; rewrite ?u_vaddi', ?u_wa_small by lia; lia | rewrite ?u_vaddi', ?u_wa_small by lia; lia]).
    replace (wa (bv_unsigned (getr regs 2) + -16)) with (v_addi (getr regs 2) (-16)) by reflexivity.
    apply (rdn_wbytes_hit SEGS (word_to_le_bytes 8 (getr regs 8))). cbn [length word_to_le_bytes Z_to_le_bytes]. unfold v_addi. rewrite ?u_small by lia. lia.
  - do 2 (rewrite rdn_wbytes_disjoint; [| cbn [length word_to_le_bytes Z_to_le_bytes]; rewrite ?u_vaddi', ?u_wa_small by lia; lia | rewrite ?u_vaddi', ?u_wa_small by lia; lia]).
    replace (wa (bv_unsigned (getr regs 2) + -24)) with (v_addi (getr regs 2) (-24)) by reflexivity.
    apply (rdn_wbytes_hit SEGS (word_to_le_bytes 8 (getr regs 9))). cbn [length word_to_le_bytes Z_to_le_bytes]. unfold v_addi. rewrite ?u_small by lia. lia.
  - do 1 (rewrite rdn_wbytes_disjoint; [| cbn [length word_to_le_bytes Z_to_le_bytes]; rewrite ?u_vaddi', ?u_wa_small by lia; lia | rewrite ?u_vaddi', ?u_wa_small by lia; lia]).
    replace (wa (bv_unsigned (getr regs 2) + -32)) with (v_addi (getr regs 2) (-32)) by reflexivity.
    apply (rdn_wbytes_hit SEGS (word_to_le_bytes 8 (getr regs 18))). cbn [length word_to_le_bytes Z_to_le_bytes]. unfold v_addi. rewrite ?u_small by lia. lia.
  - replace (wa (bv_unsigned (getr regs 2) + -40)) with (v_addi (getr regs 2) (-40)) by reflexivity.
    apply (rdn_wbytes_hit SEGS (word_to_le_bytes 8 (getr regs 19))). cbn [length word_to_le_bytes Z_to_le_bytes]. unfold v_addi. rewrite ?u_small by lia. lia.
Qed.
End P4M.

(* [comment removed for export] *)
Section TFM.
Variables (m : word -> option byte) (p G fnew : Z).
Hypothesis Hp : 3 <= p <= 2^63.
Hypothesis HG : 0 <= G + 28 <= 2^63.
Hypothesis HpG : p <= G + 28 \/ G + 32 <= p - 3.

#[using="Hp HG"] Lemma tf_mem_out : forall x, 0 <= x < 2^64 -> ~ (p - 3 <= x < p) -> ~ (G + 28 <= x < G + 32) -> tf_mem m p G fnew (wa x) = m (wa x).
Proof. LiaFast.lf_pins (fun (Hp HG : LiaFast.U) => LiaFast.u0). intros x Hx H2 H3. unfold tf_mem. do 3 peel. reflexivity. Qed.

#[using="Hp HG HpG"] Lemma tf_mem_p3 : tf_mem m p G fnew (wa (p - 3)) = Some (Z_to_bv 8 255).
Proof. LiaFast.lf_pins (fun (Hp HG HpG : LiaFast.U) => LiaFast.u0). unfold tf_mem. do 2 peel. rewrite wbytes_at_wa0 by (cbn; lia). reflexivity. Qed.

#[using="Hp HG HpG"] Lemma tf_mem_p2 : forall k, (k < 2)%nat -> tf_mem m p G fnew (wa (p - 2 + Z.of_nat k)) = Some (Z_to_bv 8 0).
Proof. LiaFast.lf_pins (fun (Hp HG HpG : LiaFast.U) => LiaFast.u0). intros k Hk. unfold tf_mem. peel. rewrite wbytes_at_wa by (cbn; lia). destruct k as [|[|k]]; [reflexivity | reflexivity | lia]. Qed.

#[using="HG"] Lemma tf_mem_G28 : forall k, (k < 4)%nat -> tf_mem m p G fnew (wa (G + 28 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 4 (wa fnew)) (Z_to_bv 8 0)).
Proof. LiaFast.lf_pins (fun (HG : LiaFast.U) => LiaFast.u0). intros k Hk. unfold tf_mem. apply wbytes_at_wa; cbn; lia. Qed.
End TFM.

(* [comment removed for export] *)
Lemma p4_tail_pre : forall (regs R : bvmap 5 word) m h3 off16 G avail freed W secret sz B,
  free_pre regs m h3 off16 G avail freed W secret sz B ->
  pro_regs R regs G W (Z.land h3 31) (16 * off16 + B + 16) ->
  tail_pre R (p4_mem m regs) G W (Z.land h3 31) (16 * off16 + B + 16)
    (bv_unsigned (getr regs 1)) (bv_unsigned (getr regs 8)) (bv_unsigned (getr regs 9)) (bv_unsigned (getr regs 18))
    (bv_unsigned (getr regs 19)) (bv_unsigned (getr regs 2)).
Proof.
  intros regs R m h3 off16 G avail freed W secret sz B FP (P8 & P9 & P10 & P11 & P2 & _).
  pose proof (fp_Rsp _ _ _ _ _ _ _ _ _ _ _ FP) as Rsp. pose proof (fp_RPB _ _ _ _ _ _ _ _ _ _ _ FP) as RPB.
  pose proof (fp_Rh3 _ _ _ _ _ _ _ _ _ _ _ FP) as Rh3. pose proof (fp_RG _ _ _ _ _ _ _ _ _ _ _ FP) as RG.
  pose proof (fp_D3 _ _ _ _ _ _ _ _ _ _ _ FP) as D3. pose proof (fp_D5 _ _ _ _ _ _ _ _ _ _ _ FP) as D5.
  pose proof (fp_D7 _ _ _ _ _ _ _ _ _ _ _ FP) as D7. pose proof (fp_HIMG _ _ _ _ _ _ _ _ _ _ _ FP) as HIMG.
  pose proof (fp_GIMG _ _ _ _ _ _ _ _ _ _ _ FP) as GIMG. pose proof (fp_Whdr _ _ _ _ _ _ _ _ _ _ _ FP) as Whdr.
  pose proof (u64_range (getr regs 2)) as U2.
  constructor.
  - exact P8.
  - exact P9.
  - exact P10.
  - exact P11.
  - rewrite P2. reflexivity.
  - exact Rsp.
  - exact (fp_Asp _ _ _ _ _ _ _ _ _ _ _ FP).
  - rewrite wa_u. apply (stk_ok_grows SEGS m). { exact (fp_HSTK _ _ _ _ _ _ _ _ _ _ _ FP). } apply p4_mem_grows.
  - exact RG.
  - exact (fp_AG _ _ _ _ _ _ _ _ _ _ _ FP).
  - pose proof (fp_RW _ _ _ _ _ _ _ _ _ _ _ FP). clear - H. lia.
  - pose proof (land31_bound h3 ltac:(clear - Rh3; lia)). clear - H. lia.
  - clear - RPB D3 Rsp. lia.
  - pose proof (u64_range (getr regs 1)). clear - H. lia.
  - pose proof (u64_range (getr regs 8)). clear - H. lia.
  - pose proof (u64_range (getr regs 9)). clear - H. lia.
  - pose proof (u64_range (getr regs 18)). clear - H. lia.
  - pose proof (u64_range (getr regs 19)). clear - H. lia.
  - rewrite wa_u. apply (p4_rdn_save m regs Rsp 8 (fun R => getr R 1)). left. reflexivity.
  - rewrite wa_u. apply (p4_rdn_save m regs Rsp 16 (fun R => getr R 8)). right. left. reflexivity.
  - rewrite wa_u. apply (p4_rdn_save m regs Rsp 24 (fun R => getr R 9)). right. right. left. reflexivity.
  - rewrite wa_u. apply (p4_rdn_save m regs Rsp 32 (fun R => getr R 18)). right. right. right. left. reflexivity.
  - rewrite wa_u. apply (p4_rdn_save m regs Rsp 40 (fun R => getr R 19)). right. right. right. right. left. reflexivity.
  - intros d k Hd Hk. apply (store_ok_mono SEGS k m); [apply p4_mem_grows|].
    replace (16 * off16 + B + 16 + -3 + d) with (16 * off16 + B + 12 + (1 + d)) by ring. apply Whdr; clear - Hd Hk; lia.
  - clear - D3. lia.
  - clear - D5. lia.
  - clear - HIMG. lia.
  - exact GIMG.
  - clear - D7. lia.
Qed.
