(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.zstd.simple_decompress.images Require Import Asan.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AS Require Import PropExec StoreOk AgentLib AsanAcct AsanAcctImages AxSymExec3 AsanPlan AsanPlanSound AsanHexScan.
(* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Import AX2. Import AP.
Open Scope Z_scope.

Definition BSEGS := Asan.M.loaded_segments.
Definition BITAB : itab := mk_itab BSEGS ASAN_TEXT_LO ASAN_TEXT_N.

Lemma both_IT_ok : itab_sound BSEGS BITAB.
Proof. apply mk_itab_sound. Qed.

Lemma both_wx : wx_segs_nowrap BSEGS.
Proof. exact Asan_wx_nowrap. Qed.

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

Lemma both_segs_in_hull : segs_in_hull_b BSEGS (img_lo ASAN) (img_hi ASAN) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma both_in_hull : forall a : word,
  APS.in_hull ASAN (bv_unsigned a) = false -> find_segment BSEGS (bv_unsigned a) 1 = None.
Proof.
  intros a H. apply (find_segment1_none_outside BSEGS (img_lo ASAN) (img_hi ASAN)); [exact both_segs_in_hull|].
  unfold APS.in_hull in H. apply andb_false_iff in H as [H|H]; [apply Z.leb_gt in H; left | apply Z.ltb_ge in H; right]; lia.
Qed.

Lemma both_res_len : APS.res_len_ok BSEGS ASAN.
Proof. vm_compute. reflexivity. Qed.

Lemma both_res_hull : Forall (fun iv => img_lo ASAN <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi ASAN) (segments_reserved BSEGS).
Proof.
  assert (E : segments_reserved BSEGS = [(Z_to_bv 64 0x10000, Z_to_bv 64 0x22000); (Z_to_bv 64 0x32000, Z_to_bv 64 0x94000);
                                         (Z_to_bv 64 0xc6000, Z_to_bv 64 0x3000); (Z_to_bv 64 0xc9000, Z_to_bv 64 0x55c000)])
    by (vm_compute; reflexivity).
  rewrite E. cbn [img_lo img_hi ASAN].
  repeat constructor; cbn [fst snd]; rewrite ?u64_lit by lia; lia.
Qed.

Lemma both_hull_ok : APS.hull_ok ASAN.
Proof. unfold APS.hull_ok. cbn [img_lo img_hi ASAN]. unfold KHI. repeat split; reflexivity || lia. Qed.

Lemma both_shadow_ok : APS.shadow_ok ASAN.
Proof. unfold APS.shadow_ok. cbn [shadow_off ASAN]. lia. Qed.

Lemma both_res_sizes : APS.sum_sizes (segments_reserved BSEGS) = 0x615000.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma both_hex2 : hexscanZ Asan_seg_bytes_002 0 12288 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma both_hex3 : hexscanZ Asan_seg_bytes_003 0 5619712 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma both_len2 : Z.to_N (Uint63.to_Z (PrimString.length Asan_seg_bytes_002) / 2) = 12288%N.
Proof. vm_compute. reflexivity. Qed.
Lemma both_len3 : Z.to_N (Uint63.to_Z (PrimString.length Asan_seg_bytes_003) / 2) = 5619712%N.
Proof. vm_compute. reflexivity. Qed.

Lemma both_segs_eq : BSEGS = [Asan_segment_000; Asan_segment_001;
                              Asan_segment_002; Asan_segment_003].
Proof. reflexivity. Qed.

Lemma both_rw_window : forall m (x : word),
  0xc6000 <= bv_unsigned x < 0x625000 -> wview BSEGS m x <> None.
Proof.
  intros m x Hx. unfold wview. destruct (m x); [discriminate|].
  destruct (find_segment BSEGS (bv_unsigned x) 1) as [seg|] eqn:Hf.
  - apply find_segment_some_spec in Hf as (Hin & Hb & Ht).
    rewrite both_segs_eq in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
      cbn [seg_base seg_size seg_writable seg_perms seg_bytes string_has Ascii.eqb
           Asan_segment_000 Asan_segment_001
           Asan_segment_002 Asan_segment_003] in Hb, Ht |- *.
    + exfalso. lia.
    + exfalso. lia.
    + cbn -[segment_byte_at]. apply (segment_byte_at_someZ _ 12288); [exact both_hex2 | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
    + cbn -[segment_byte_at]. apply (segment_byte_at_someZ _ 5619712); [exact both_hex3 | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
  - exfalso. destruct (Z.lt_ge_cases (bv_unsigned x) 0xc9000) as [Hl|Hl].
    + apply (find_segment_none_spec _ _ _ Hf Asan_segment_002);
        [rewrite both_segs_eq; cbn; tauto | cbn; lia].
    + apply (find_segment_none_spec _ _ _ Hf Asan_segment_003);
        [rewrite both_segs_eq; cbn; tauto | cbn; lia].
Qed.

(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AS Require AsanNodesMmLib.

Lemma both_hull_cov : AsanNodesMmLib.hull_cov BSEGS ASAN.
Proof.
  split; [cbn; lia|].
  assert (E : segments_reserved BSEGS = [(Z_to_bv 64 0x10000, Z_to_bv 64 0x22000); (Z_to_bv 64 0x32000, Z_to_bv 64 0x94000);
                                         (Z_to_bv 64 0xc6000, Z_to_bv 64 0x3000); (Z_to_bv 64 0xc9000, Z_to_bv 64 0x55c000)])
    by (vm_compute; reflexivity).
  intros z Hz. rewrite E. cbn [img_lo img_hi ASAN] in Hz.
  unfold APS.in_ivs. cbn [existsb fst snd]. rewrite !u64_lit by lia.
  destruct (Z.lt_ge_cases z 0x32000); [|destruct (Z.lt_ge_cases z 0xc6000); [|destruct (Z.lt_ge_cases z 0xc9000)]];
    repeat (apply orb_true_iff; first [left; apply andb_true_iff; split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia] | right]).
Qed.

(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AS Require Import AsanInit.
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.

Definition BPH : PhdrInfo := Asan.M.phdrs.

Lemma both_img_facts : img_facts BSEGS ASAN BPH.
Proof.
  constructor.
  - repeat split; reflexivity.
  - cbn [img_lo img_hi ASAN]. lia.
  - vm_compute. reflexivity.
  - exact both_res_hull.
  - rewrite both_res_sizes. reflexivity.
  - cbn [rw_lo rw_len ASAN]. split; [lia|]. intros m x Hx. apply both_rw_window. lia.
  - exact both_shadow_ok.
Qed.
