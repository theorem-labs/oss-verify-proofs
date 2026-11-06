(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanHexScan OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs OSSVerify.Proofs.glaze.binary_reflection.lib.AsSInit. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanHexScan OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs.BoSDefs OSSVerify.Proofs.glaze.binary_reflection.lib.AsSInit.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require AzHexZero.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import APC. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma Forall_ivs_of_b : forall (lo hi : Z) (l : list (word * word)),
  forallb (fun iv => (lo <=? bv_unsigned (fst iv)) && (bv_unsigned (fst iv) + bv_unsigned (snd iv) <=? hi))%bool l = true ->
  Forall (fun iv => lo <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= hi) l.
Proof.
  intros lo hi l H. apply Forall_forall. intros iv Hin.
  pose proof (proj1 (forallb_forall _ _) H iv Hin) as B. apply andb_prop in B as [B1 B2].
  apply Z.leb_le in B1. apply Z.leb_le in B2. lia.
Qed.

Lemma both_segs_eq : BSEGS = [AsanUbsan_segment_000; AsanUbsan_segment_001; AsanUbsan_segment_002; AsanUbsan_segment_003].
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma both_S_wx_b : wx_segs_nowrap_b BSEGS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma both_S_wx : wx_segs_nowrap BSEGS.
Proof. apply wx_segs_nowrap_of_b. exact both_S_wx_b. Qed.

Lemma both_segs_in_hull : AzImageAsan.segs_in_hull_b BSEGS (img_lo AT_B) (img_hi AT_B) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma both_S_in_hull : forall a : word,
  APS.in_hull AT_B (bv_unsigned a) = false -> find_segment BSEGS (bv_unsigned a) 1 = None.
Proof.
  intros a H. apply (AzImageAsan.find_segment1_none_outside BSEGS (img_lo AT_B) (img_hi AT_B)); [exact both_segs_in_hull|].
  unfold APS.in_hull in H. apply andb_false_iff in H as [H|H]; [apply Z.leb_gt in H; left | apply Z.ltb_ge in H; right]; lia.
Qed.

Lemma both_S_res_len : APS.res_len_ok BSEGS AT_B.
Proof. vm_compute. reflexivity. Qed.

Lemma both_S_res_hull : Forall (fun iv => img_lo AT_B <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi AT_B)
                               (segments_reserved BSEGS).
Proof. apply Forall_ivs_of_b. vm_compute. reflexivity. Qed.

Lemma both_S_hull_ok : APS.hull_ok AT_B.
Proof. unfold APS.hull_ok. cbn [img_lo img_hi AT_B]. unfold KHI. repeat split; reflexivity || lia. Qed.

Lemma both_S_shadow_ok : APS.shadow_ok AT_B.
Proof. unfold APS.shadow_ok. cbn. lia. Qed.

Lemma both_S_res_sizes : APS.sum_sizes (segments_reserved BSEGS) = 0x653000.
Proof. vm_compute. reflexivity. Qed.

Lemma both_S_hull_ne : img_lo AT_B < img_hi AT_B.
Proof. cbn. lia. Qed.

(* [comment removed for export] *)
Lemma both_S_res_tile : forall z, img_lo AT_B <= z < img_hi AT_B -> APS.in_ivs z (segments_reserved BSEGS) = true.
Proof.
  intros z Hz. cbn [img_lo img_hi AT_B] in Hz.
  replace (segments_reserved BSEGS) with
    [(Z_to_bv 64 0x10000, Z_to_bv 64 0x3b000); (Z_to_bv 64 0x4b000, Z_to_bv 64 0xb7000); (Z_to_bv 64 0x102000, Z_to_bv 64 0x5000); (Z_to_bv 64 0x107000, Z_to_bv 64 0x55c000)]
    by (vm_compute; reflexivity).
  unfold APS.in_ivs. cbn [existsb fst snd]. rewrite !u64_lit by lia.
  destruct (Z_lt_ge_dec z 0x4b000); [|destruct (Z_lt_ge_dec z 0x102000); [|destruct (Z_lt_ge_dec z 0x107000)]].
  - replace (0x10000 <=? z) with true by (symmetry; apply Z.leb_le; lia). replace (z <? 0x10000 + 0x3b000) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  - replace (0x4b000 <=? z) with true by (symmetry; apply Z.leb_le; lia). replace (z <? 0x4b000 + 0xb7000) with true by (symmetry; apply Z.ltb_lt; lia).
    rewrite orb_true_r. reflexivity.
  - replace (0x102000 <=? z) with true by (symmetry; apply Z.leb_le; lia). replace (z <? 0x102000 + 0x5000) with true by (symmetry; apply Z.ltb_lt; lia).
    rewrite !orb_true_r. reflexivity.
  - replace (0x107000 <=? z) with true by (symmetry; apply Z.leb_le; lia). replace (z <? 0x107000 + 0x55c000) with true by (symmetry; apply Z.ltb_lt; lia).
    rewrite !orb_true_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma both_hex2 : scanN AsanUbsan_seg_bytes_002 64 0 0x5000 = true.
Proof. apply AzHexZero.scanN_of_data. vm_compute. reflexivity. Qed.
Lemma both_hex3 : scanN AsanUbsan_seg_bytes_003 64 0 0x55c000 = true.
Proof. apply (AzHexZero.scanN_of_data_zero _ 15104%N). vm_compute. reflexivity. Qed.
Lemma both_len2 : Z.to_N (Uint63.to_Z (PrimString.length AsanUbsan_seg_bytes_002) / 2) = 0x5000%N.
Proof. vm_compute. reflexivity. Qed.
Lemma both_len3 : Z.to_N (Uint63.to_Z (PrimString.length AsanUbsan_seg_bytes_003) / 2) = 0x55c000%N.
Proof. vm_compute. reflexivity. Qed.

Lemma both_rw_window : forall m (x : word),
  0x102000 <= bv_unsigned x < 0x663000 -> wview BSEGS m x <> None.
Proof.
  intros m x Hx. unfold wview. destruct (m x); [discriminate|].
  destruct (find_segment BSEGS (bv_unsigned x) 1) as [seg|] eqn:Hf.
  - apply find_segment_some_spec in Hf as (Hin & Hb & Ht).
    rewrite both_segs_eq in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
      cbn [seg_base seg_size seg_writable seg_perms seg_bytes string_has Ascii.eqb
           AsanUbsan_segment_000 AsanUbsan_segment_001
           AsanUbsan_segment_002 AsanUbsan_segment_003] in Hb, Ht |- *.
    + exfalso. lia.
    + exfalso. lia.
    + cbn -[segment_byte_at]. apply (segment_byte_at_some1 _ 0x5000); [exact both_hex2 | rewrite both_len2; lia | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
    + cbn -[segment_byte_at]. apply (segment_byte_at_some1 _ 0x55c000); [exact both_hex3 | rewrite both_len3; lia | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
  - exfalso. destruct (Z.lt_ge_cases (bv_unsigned x) 0x107000) as [Hl|Hl].
    + apply (find_segment_none_spec _ _ _ Hf AsanUbsan_segment_002);
        [rewrite both_segs_eq; cbn; tauto | cbn; lia].
    + apply (find_segment_none_spec _ _ _ Hf AsanUbsan_segment_003);
        [rewrite both_segs_eq; cbn; tauto | cbn; lia].
Qed.

Definition BPH : PhdrInfo := AsanUbsan.M.phdrs.

Lemma both_img_facts : img_facts BSEGS AT_B BPH.
Proof.
  constructor.
  - repeat split; reflexivity.
  - cbn [img_lo img_hi AT_B]. lia.
  - vm_compute. reflexivity.
  - exact both_S_res_hull.
  - rewrite both_S_res_sizes. reflexivity.
  - cbn [rw_lo rw_len AT_B]. split; [lia|]. intros m x Hx. apply both_rw_window. lia.
  - exact both_S_shadow_ok.
Qed.
