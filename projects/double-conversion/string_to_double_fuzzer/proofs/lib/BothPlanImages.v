(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgB.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec StoreOk AgentLib.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AsanAcct AsanAcctImages AxSymExec3 AsanPlan AsanPlanSound AsanHexScan AsanHexZero AsanPlanImages.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AP.
Open Scope Z_scope.

Definition BSEGS := ImgB.M.loaded_segments.
Definition BITAB : itab := mk_itab BSEGS BOTH_TEXT_LO BOTH_TEXT_N.

Lemma both_IT_ok : itab_sound BSEGS BITAB.
Proof. apply mk_itab_sound. Qed.

Lemma both_wx : wx_segs_nowrap BSEGS.
Proof. exact Both_wx_nowrap. Qed.

Lemma both_segs_in_hull : segs_in_hull_b BSEGS (img_lo BOTH) (img_hi BOTH) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma both_in_hull : forall a : word,
  APS.in_hull BOTH (bv_unsigned a) = false -> find_segment BSEGS (bv_unsigned a) 1 = None.
Proof.
  intros a H. apply (find_segment1_none_outside BSEGS (img_lo BOTH) (img_hi BOTH)); [exact both_segs_in_hull|].
  unfold APS.in_hull in H. apply andb_false_iff in H as [H|H]; [apply Z.leb_gt in H; left | apply Z.ltb_ge in H; right]; lia.
Qed.

Lemma both_res_len : APS.res_len_ok BSEGS BOTH.
Proof. vm_compute. reflexivity. Qed.

Lemma both_res_eq : segments_reserved BSEGS = [(Z_to_bv 64 0x10000, Z_to_bv 64 0x3e000); (Z_to_bv 64 0x4e000, Z_to_bv 64 0xd6000); (Z_to_bv 64 0x124000, Z_to_bv 64 0x8000); (Z_to_bv 64 0x12c000, Z_to_bv 64 0x55d000)].
Proof. vm_compute. reflexivity. Qed.

Lemma both_res_hull : Forall (fun iv => img_lo BOTH <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi BOTH) (segments_reserved BSEGS).
Proof.
  rewrite both_res_eq. cbn [img_lo img_hi BOTH].
  repeat constructor; cbn [fst snd]; rewrite ?u64_lit by lia; lia.
Qed.

(* [comment removed for export] *)
Lemma both_res_chain : (Z.ltb (img_lo BOTH) (img_hi BOTH) && res_chain (segments_reserved BSEGS) (img_lo BOTH) (img_hi BOTH))%bool = true.
Proof. vm_compute. reflexivity. Qed.

Lemma both_hull_ok : APS.hull_ok BOTH.
Proof. unfold APS.hull_ok. cbn [img_lo img_hi BOTH]. unfold KHI. repeat split; reflexivity || lia. Qed.

Lemma both_shadow_ok : APS.shadow_ok BOTH.
Proof. unfold APS.shadow_ok. cbn [shadow_off BOTH]. lia. Qed.

Lemma both_res_sizes : APS.sum_sizes (segments_reserved BSEGS) = 0x679000.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma both_hex2 : scanN ImgB_seg_bytes_002 64 0 32768 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma both_hex3 : scanN ImgB_seg_bytes_003 64 0 5623808 = true.
Proof. (* [comment removed for export] *)
  apply (scanN_prefix_zwin ImgB_seg_bytes_003 20480 5623808 (Uint63.of_Z 40960) (Uint63.of_Z 11206656)).
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - reflexivity.
  - reflexivity.
  - vm_compute. discriminate.
  - vm_compute. discriminate.
Qed.
Lemma both_len2 : Z.to_N (Uint63.to_Z (PrimString.length ImgB_seg_bytes_002) / 2) = 32768%N.
Proof. vm_compute. reflexivity. Qed.
Lemma both_len3 : Z.to_N (Uint63.to_Z (PrimString.length ImgB_seg_bytes_003) / 2) = 5623808%N.
Proof. vm_compute. reflexivity. Qed.

Lemma both_segs_eq : BSEGS = [ImgB_segment_000; ImgB_segment_001; ImgB_segment_002; ImgB_segment_003].
Proof. reflexivity. Qed.

Lemma both_rw_window : forall m (x : word),
  0x124000 <= bv_unsigned x < 0x689000 -> wview BSEGS m x <> None.
Proof.
  intros m x Hx. unfold wview. destruct (m x); [discriminate|].
  destruct (find_segment BSEGS (bv_unsigned x) 1) as [seg|] eqn:Hf.
  - apply find_segment_some_spec in Hf as (Hin & Hb & Ht).
    rewrite both_segs_eq in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
      cbn [seg_base seg_size seg_writable seg_perms seg_bytes string_has Ascii.eqb
           ImgB_segment_000 ImgB_segment_001 ImgB_segment_002 ImgB_segment_003] in Hb, Ht |- *.
    + exfalso. lia.
    + exfalso. lia.
    + cbn -[segment_byte_at]. apply (segment_byte_at_some1 _ 32768); [exact both_hex2 | rewrite both_len2; lia | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
    + cbn -[segment_byte_at]. apply (segment_byte_at_some1 _ 5623808); [exact both_hex3 | rewrite both_len3; lia | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
  - exfalso. destruct (Z.lt_ge_cases (bv_unsigned x) 0x12c000) as [Hl|Hl].
    + apply (find_segment_none_spec _ _ _ Hf ImgB_segment_002);
        [rewrite both_segs_eq; cbn; tauto | cbn; lia].
    + apply (find_segment_none_spec _ _ _ Hf ImgB_segment_003);
        [rewrite both_segs_eq; cbn; tauto | cbn; lia].
Qed.
