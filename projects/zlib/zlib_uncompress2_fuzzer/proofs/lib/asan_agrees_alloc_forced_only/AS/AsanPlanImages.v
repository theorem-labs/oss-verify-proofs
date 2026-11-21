(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.World Require Import Tgt_zlib_uncompress2_fuzzer_asan.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.AS Require Import PropExec StoreOk AgentLib AsanAcct AsanAcctImages AxSymExec3 AsanPlan AsanPlanSound AsanHexScan.
From Stdlib Require Uint63.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.AS Require HexScanFast.
Unset Lia Cache.
Import ListNotations.
Import AX2. Import AP.
Open Scope Z_scope.

Definition ASEGS := Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments.
Definition AITAB : itab := mk_itab ASEGS ASAN_TEXT_LO ASAN_TEXT_N.

Lemma asan_IT_ok : itab_sound ASEGS AITAB.
Proof. apply mk_itab_sound. Qed.

Lemma asan_wx : wx_segs_nowrap ASEGS.
Proof. exact Asan_wx_nowrap. Qed.

Definition segs_in_hull_b (segs : list Segment) (lo hi : Z) : bool :=
  forallb (fun seg => (lo <=? Z.of_N (seg_base seg)) && (Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <=? hi))%bool segs.

Lemma find_segment1_none_outside : forall segs lo hi x,
  segs_in_hull_b segs lo hi = true -> (x < lo \/ hi <= x) -> find_segment segs x 1 = None.
Proof.
  induction segs as [|s l IH]; intros lo hi x Hb Hx; [reflexivity|].
  cbn [segs_in_hull_b forallb] in Hb. apply andb_true_iff in Hb as [Hs Hl].
  apply andb_true_iff in Hs as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  cbn [find_segment].
  replace (Z.leb (Z.of_N (seg_base s)) x && Z.leb (x + 1) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool with false.
  - exact (IH lo hi x Hl Hx).
  - symmetry. apply andb_false_iff. destruct Hx as [Hx|Hx]; [left | right]; apply Z.leb_gt; lia.
Qed.

Lemma asan_segs_in_hull : segs_in_hull_b ASEGS (img_lo ASAN) (img_hi ASAN) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma asan_in_hull : forall a : word,
  APS.in_hull ASAN (bv_unsigned a) = false -> find_segment ASEGS (bv_unsigned a) 1 = None.
Proof.
  intros a H. apply (find_segment1_none_outside ASEGS (img_lo ASAN) (img_hi ASAN)); [exact asan_segs_in_hull|].
  unfold APS.in_hull in H. apply andb_false_iff in H as [H|H]; [apply Z.leb_gt in H; left | apply Z.ltb_ge in H; right]; lia.
Qed.

Lemma asan_res_len : APS.res_len_ok ASEGS ASAN.
Proof. vm_compute. reflexivity. Qed.

Lemma asan_res_hull : Forall (fun iv => img_lo ASAN <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi ASAN) (segments_reserved ASEGS).
Proof.
  assert (E : segments_reserved ASEGS = [(Z_to_bv 64 0x10000, Z_to_bv 64 0x2b000); (Z_to_bv 64 0x3b000, Z_to_bv 64 0x91000);
                                         (Z_to_bv 64 0xcc000, Z_to_bv 64 0x5000); (Z_to_bv 64 0xd1000, Z_to_bv 64 0x5ad000)])
    by (vm_compute; reflexivity).
  rewrite E. cbn [img_lo img_hi ASAN].
  repeat constructor; cbn [fst snd]; rewrite ?u64_lit by lia; lia.
Qed.

Lemma asan_hull_ok : APS.hull_ok ASAN.
Proof. unfold APS.hull_ok. cbn [img_lo img_hi ASAN]. unfold KHI. repeat split; reflexivity || lia. Qed.

Lemma asan_shadow_ok : APS.shadow_ok ASAN.
Proof. unfold APS.shadow_ok. cbn [shadow_off ASAN]. lia. Qed.

Lemma asan_res_sizes : APS.sum_sizes (segments_reserved ASEGS) = 0x66e000.
Proof. vm_compute. reflexivity. Qed.

Lemma asan_hex2 : scanN Tgt_zlib_uncompress2_fuzzer_asan_seg_bytes_002 64 0 20480 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma asan_hex3 : HexScanFast.scanI Tgt_zlib_uncompress2_fuzzer_asan_seg_bytes_003 64 (Uint63.of_Z 0) (Uint63.of_Z (Z.of_N 5951488)) = true.
Proof.
  vm_cast_no_check (@eq_refl bool true).
Qed.
Lemma asan_len2 : Z.to_N (Uint63.to_Z (PrimString.length Tgt_zlib_uncompress2_fuzzer_asan_seg_bytes_002) / 2) = 20480%N.
Proof. vm_compute. reflexivity. Qed.
Lemma asan_len3 : Z.to_N (Uint63.to_Z (PrimString.length Tgt_zlib_uncompress2_fuzzer_asan_seg_bytes_003) / 2) = 5951488%N.
Proof. vm_compute. reflexivity. Qed.

Lemma asan_segs_eq : ASEGS = [Tgt_zlib_uncompress2_fuzzer_asan_segment_000; Tgt_zlib_uncompress2_fuzzer_asan_segment_001;
                              Tgt_zlib_uncompress2_fuzzer_asan_segment_002; Tgt_zlib_uncompress2_fuzzer_asan_segment_003].
Proof. reflexivity. Qed.

Lemma asan_rw_window : forall m (x : word),
  0xcc000 <= bv_unsigned x < 0x67e000 -> wview ASEGS m x <> None.
Proof.
  intros m x Hx. unfold wview. destruct (m x); [discriminate|].
  destruct (find_segment ASEGS (bv_unsigned x) 1) as [seg|] eqn:Hf.
  - apply find_segment_some_spec in Hf as (Hin & Hb & Ht).
    rewrite asan_segs_eq in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
      cbn [seg_base seg_size seg_writable seg_perms seg_bytes string_has Ascii.eqb
           Tgt_zlib_uncompress2_fuzzer_asan_segment_000 Tgt_zlib_uncompress2_fuzzer_asan_segment_001
           Tgt_zlib_uncompress2_fuzzer_asan_segment_002 Tgt_zlib_uncompress2_fuzzer_asan_segment_003] in Hb, Ht |- *.
    + exfalso. lia.
    + exfalso. lia.
    + cbn -[segment_byte_at]. apply (segment_byte_at_some1 _ 20480); [exact asan_hex2 | rewrite asan_len2; lia | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
    + cbn -[segment_byte_at]. apply (HexScanFast.segment_byte_at_some1I _ 5951488); [exact asan_hex3 | vm_compute; reflexivity | rewrite asan_len3; lia | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
  - exfalso. destruct (Z.lt_ge_cases (bv_unsigned x) 0xd1000) as [Hl|Hl].
    + apply (find_segment_none_spec _ _ _ Hf Tgt_zlib_uncompress2_fuzzer_asan_segment_002);
        [rewrite asan_segs_eq; cbn; tauto | cbn; lia].
    + apply (find_segment_none_spec _ _ _ Hf Tgt_zlib_uncompress2_fuzzer_asan_segment_003);
        [rewrite asan_segs_eq; cbn; tauto | cbn; lia].
Qed.

From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.AS Require AsanNodesMmLib.

Lemma asan_hull_cov : AsanNodesMmLib.hull_cov ASEGS ASAN.
Proof.
  split; [cbn; lia|].
  assert (E : segments_reserved ASEGS = [(Z_to_bv 64 0x10000, Z_to_bv 64 0x2b000); (Z_to_bv 64 0x3b000, Z_to_bv 64 0x91000);
                                         (Z_to_bv 64 0xcc000, Z_to_bv 64 0x5000); (Z_to_bv 64 0xd1000, Z_to_bv 64 0x5ad000)])
    by (vm_compute; reflexivity).
  intros z Hz. rewrite E. cbn [img_lo img_hi ASAN] in Hz.
  unfold APS.in_ivs. cbn [existsb fst snd]. rewrite !u64_lit by lia.
  destruct (Z.lt_ge_cases z 0x3b000); [|destruct (Z.lt_ge_cases z 0xcc000); [|destruct (Z.lt_ge_cases z 0xd1000)]];
    repeat (apply orb_true_iff; first [left; apply andb_true_iff; split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia] | right]).
Qed.

From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.AS Require Import AsanInit.
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.

Definition APH : PhdrInfo := Tgt_zlib_uncompress2_fuzzer_asan.M.phdrs.

Lemma asan_img_facts : img_facts ASEGS ASAN APH.
Proof.
  constructor.
  - repeat split; reflexivity.
  - cbn [img_lo img_hi ASAN]. lia.
  - vm_compute. reflexivity.
  - exact asan_res_hull.
  - rewrite asan_res_sizes. reflexivity.
  - cbn [rw_lo rw_len ASAN]. split; [lia|]. intros m x Hx. apply asan_rw_window. lia.
  - exact asan_shadow_ok.
  - (* if_resx, the table's room for the vDSO reservation *)
    split; apply Nat.leb_le; vm_compute; reflexivity.
Qed.
