(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (11 recorded proofs replaced by written proofs (asan_IT_ok, asan_wx, find_segment1_none_outside and 8 more); the image facts' bound on the launch's extra reservations; the port of zstd/zstd_frame_info's same file). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.zstd.huf_decompress.images Require Import AsanUbsan.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import PropExec StoreOk AgentLib AsanAcct AsanAcctImages AxSymExec3 AsanPlan AsanPlanSound AsanHexScan.
(* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Import AX2. Import AP.
Open Scope Z_scope.

Definition ASEGS := AsanUbsan.M.loaded_segments.
Definition AITAB : itab := mk_itab ASEGS BOTH_TEXT_LO BOTH_TEXT_N.

Lemma asan_IT_ok : itab_sound ASEGS AITAB.
Proof. apply mk_itab_sound. Qed.

Lemma asan_wx : wx_segs_nowrap ASEGS.
Proof. exact Both_wx_nowrap. Qed.

(* [comment removed for export] *)
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

Lemma asan_segs_in_hull : segs_in_hull_b ASEGS (img_lo BOTH) (img_hi BOTH) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma asan_in_hull : forall a : word,
  APS.in_hull BOTH (bv_unsigned a) = false -> find_segment ASEGS (bv_unsigned a) 1 = None.
Proof.
  intros a H. apply (find_segment1_none_outside ASEGS (img_lo BOTH) (img_hi BOTH)); [exact asan_segs_in_hull|].
  unfold APS.in_hull in H. apply andb_false_iff in H as [H|H]; [apply Z.leb_gt in H; left | apply Z.ltb_ge in H; right]; lia.
Qed.

Lemma asan_res_len : APS.res_len_ok ASEGS BOTH.
Proof. vm_compute. reflexivity. Qed.

Lemma asan_res_hull : Forall (fun iv => img_lo BOTH <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi BOTH) (segments_reserved ASEGS).
Proof.
  assert (E : segments_reserved ASEGS = [(Z_to_bv 64 0x10000, Z_to_bv 64 0x20000); (Z_to_bv 64 0x30000, Z_to_bv 64 0x81000);
                                         (Z_to_bv 64 0xb1000, Z_to_bv 64 0x2000); (Z_to_bv 64 0xb3000, Z_to_bv 64 0x55c000)])
    by (vm_compute; reflexivity).
  rewrite E. cbn [img_lo img_hi BOTH].
  repeat constructor; cbn [fst snd]; rewrite ?u64_lit by lia; lia.
Qed.

Lemma asan_hull_ok : APS.hull_ok BOTH.
Proof. unfold APS.hull_ok. cbn [img_lo img_hi BOTH]. unfold KHI. repeat split; reflexivity || lia. Qed.

Lemma asan_shadow_ok : APS.shadow_ok BOTH.
Proof. unfold APS.shadow_ok. cbn [shadow_off BOTH]. lia. Qed.

Lemma asan_res_sizes : APS.sum_sizes (segments_reserved ASEGS) = 0x5ff000.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma asan_hex2 : hexscanZ AsanUbsan_seg_bytes_002 0 8192 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma asan_hex3 : hexscanZ AsanUbsan_seg_bytes_003 0 5619712 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma asan_len2 : Z.to_N (Uint63.to_Z (PrimString.length AsanUbsan_seg_bytes_002) / 2) = 8192%N.
Proof. vm_compute. reflexivity. Qed.
Lemma asan_len3 : Z.to_N (Uint63.to_Z (PrimString.length AsanUbsan_seg_bytes_003) / 2) = 5619712%N.
Proof. vm_compute. reflexivity. Qed.

Lemma asan_segs_eq : ASEGS = [AsanUbsan_segment_000; AsanUbsan_segment_001;
                              AsanUbsan_segment_002; AsanUbsan_segment_003].
Proof. reflexivity. Qed.

Lemma asan_rw_window : forall m (x : word),
  0xb1000 <= bv_unsigned x < 0x60f000 -> wview ASEGS m x <> None.
Proof.
  intros m x Hx. unfold wview. destruct (m x); [discriminate|].
  destruct (find_segment ASEGS (bv_unsigned x) 1) as [seg|] eqn:Hf.
  - apply find_segment_some_spec in Hf as (Hin & Hb & Ht).
    rewrite asan_segs_eq in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
      cbn [seg_base seg_size seg_writable seg_perms seg_bytes string_has Ascii.eqb
           AsanUbsan_segment_000 AsanUbsan_segment_001
           AsanUbsan_segment_002 AsanUbsan_segment_003] in Hb, Ht |- *.
    + exfalso. lia.
    + exfalso. lia.
    + cbn -[segment_byte_at]. apply (segment_byte_at_someZ _ 8192); [exact asan_hex2 | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
    + cbn -[segment_byte_at]. apply (segment_byte_at_someZ _ 5619712); [exact asan_hex3 | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
  - exfalso. destruct (Z.lt_ge_cases (bv_unsigned x) 0xb3000) as [Hl|Hl].
    + apply (find_segment_none_spec _ _ _ Hf AsanUbsan_segment_002);
        [rewrite asan_segs_eq; cbn; tauto | cbn; lia].
    + apply (find_segment_none_spec _ _ _ Hf AsanUbsan_segment_003);
        [rewrite asan_segs_eq; cbn; tauto | cbn; lia].
Qed.

(* [comment removed for export] *)
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require AsanNodesMmLib.

Lemma asan_hull_cov : AsanNodesMmLib.hull_cov ASEGS BOTH.
Proof.
  split; [cbn; lia|].
  assert (E : segments_reserved ASEGS = [(Z_to_bv 64 0x10000, Z_to_bv 64 0x20000); (Z_to_bv 64 0x30000, Z_to_bv 64 0x81000);
                                         (Z_to_bv 64 0xb1000, Z_to_bv 64 0x2000); (Z_to_bv 64 0xb3000, Z_to_bv 64 0x55c000)])
    by (vm_compute; reflexivity).
  intros z Hz. rewrite E. cbn [img_lo img_hi BOTH] in Hz.
  unfold APS.in_ivs. cbn [existsb fst snd]. rewrite !u64_lit by lia.
  destruct (Z.lt_ge_cases z 0x30000); [|destruct (Z.lt_ge_cases z 0xb1000); [|destruct (Z.lt_ge_cases z 0xb3000)]];
    repeat (apply orb_true_iff; first [left; apply andb_true_iff; split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia] | right]).
Qed.

(* [comment removed for export] *)
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import AsanInit.
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.

Definition APH : PhdrInfo := AsanUbsan.M.phdrs.

Lemma asan_img_facts : img_facts ASEGS BOTH APH.
Proof.
  constructor.
  - repeat split; reflexivity.
  - cbn [img_lo img_hi BOTH]. lia.
  - vm_compute. reflexivity.
  - exact asan_res_hull.
  - rewrite asan_res_sizes. reflexivity.
  - cbn [rw_lo rw_len BOTH]. split; [lia|]. intros m x Hx. apply asan_rw_window. lia.
  - exact asan_shadow_ok.
  - (* the launch's extra reservations: the vDSO pair, two intervals, at most twenty pages *)
    cbn [n_resx p_resx BOTH]. lia.
Qed.
