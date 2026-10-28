(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec StoreOk AgentLib AsanAcct AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums AsanHexScan AsanHexTree AsanInit.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.AsCert Require Import AsImages AsPlanImagesHex AsPlanImagesHex2 AsPlanImagesHexZ.
Import ListNotations.
Import AX2. Import AP.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition ASEGS : list Segment := AsanUbsan.M.loaded_segments.
Definition APH : PhdrInfo := AsanUbsan.M.phdrs.

Lemma asan_wx : wx_segs_nowrap ASEGS.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

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

Lemma asan_segs_in_hull : segs_in_hull_b ASEGS (img_lo ASAN_H) (img_hi ASAN_H) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma asan_in_hull : forall a : word,
  APS.in_hull ASAN_H (bv_unsigned a) = false -> find_segment ASEGS (bv_unsigned a) 1 = None.
Proof.
  intros a H. apply (find_segment1_none_outside ASEGS (img_lo ASAN_H) (img_hi ASAN_H)); [exact asan_segs_in_hull|].
  unfold APS.in_hull in H. apply andb_false_iff in H as [H|H]; [apply Z.leb_gt in H; left | apply Z.ltb_ge in H; right]; lia.
Qed.

Lemma asan_res_len : APS.res_len_ok ASEGS ASAN_H.
Proof. vm_compute. reflexivity. Qed.

Lemma asan_res_hull : Forall (fun iv => img_lo ASAN_H <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi ASAN_H) (segments_reserved ASEGS).
Proof.
  assert (E : segments_reserved ASEGS = [(Z_to_bv 64 0x10000, Z_to_bv 64 0x185000); (Z_to_bv 64 0x195000, Z_to_bv 64 0x3dc000);
                                         (Z_to_bv 64 0x571000, Z_to_bv 64 0x79000); (Z_to_bv 64 0x5ea000, Z_to_bv 64 0x61a000)])
    by (vm_compute; reflexivity).
  rewrite E. cbn [img_lo img_hi ASAN_H].
  repeat constructor; cbn [fst snd]; rewrite ?u64_lit by lia; lia.
Qed.

(* [comment removed for export] *)
Lemma asan_res_cover : img_lo ASAN_H < img_hi ASAN_H /\ forall z, img_lo ASAN_H <= z < img_hi ASAN_H ->
  exists iv, In iv (segments_reserved ASEGS) /\ bv_unsigned (fst iv) <= z < bv_unsigned (fst iv) + bv_unsigned (snd iv).
Proof.
  assert (E : segments_reserved ASEGS = [(Z_to_bv 64 0x10000, Z_to_bv 64 0x185000); (Z_to_bv 64 0x195000, Z_to_bv 64 0x3dc000);
                                         (Z_to_bv 64 0x571000, Z_to_bv 64 0x79000); (Z_to_bv 64 0x5ea000, Z_to_bv 64 0x61a000)])
    by (vm_compute; reflexivity).
  rewrite E. cbn [img_lo img_hi ASAN_H]. split; [lia|]. intros z Hz.
  destruct (Z_lt_le_dec z 0x195000);
    [exists (Z_to_bv 64 0x10000, Z_to_bv 64 0x185000) | destruct (Z_lt_le_dec z 0x571000);
    [exists (Z_to_bv 64 0x195000, Z_to_bv 64 0x3dc000) | destruct (Z_lt_le_dec z 0x5ea000);
    [exists (Z_to_bv 64 0x571000, Z_to_bv 64 0x79000) | exists (Z_to_bv 64 0x5ea000, Z_to_bv 64 0x61a000)]]];
    (split; [cbn [In]; tauto | cbn [fst snd]; rewrite !u64_lit by lia; lia]).
Qed.

Lemma asan_hull_ok : APS.hull_ok ASAN_H.
Proof. unfold APS.hull_ok. cbn [img_lo img_hi ASAN_H]. unfold KHI. repeat split; reflexivity || lia. Qed.

Lemma asan_shadow_ok : APS.shadow_ok ASAN_H.
Proof. unfold APS.shadow_ok. cbn [shadow_off ASAN_H]. lia. Qed.

Lemma asan_res_sizes : APS.sum_sizes (segments_reserved ASEGS) = 0xbf4000.
Proof. vm_compute. reflexivity. Qed.

Lemma asan_segs_wr : APSX.segs_wr_ok ASEGS.
Proof. intros seg Hin Hw. cbn in Hin. destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hw |- *; congruence. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma asan_hex3_pt : forall i, (i < 6397952)%N -> hex_byte_at AsanUbsan_seg_bytes_003 i <> None.
Proof.
  intros i Hi.
  destruct (N.lt_ge_cases i 793344) as [H1|H1]; [exact (asan_hex3a i H1)|].
  destruct (N.lt_ge_cases i 1321776) as [H2|H2].
  { replace i with (793344 + (i - 793344))%N by lia. apply (zpt_vpt _ _ _ asan_ia_zero). lia. }
  destruct (N.lt_ge_cases i 1714136) as [H3|H3].
  { replace i with (1321776 + (i - 1321776))%N by lia. apply asan_hex3b. lia. }
  destruct (N.lt_ge_cases i 5908440) as [H4|H4].
  { replace i with (1714136 + (i - 1714136))%N by lia. apply (zpt_vpt _ _ _ asan_tab_zero). lia. }
  replace i with (5908440 + (i - 5908440))%N by lia. apply asan_hex3c. lia.
Qed.

Lemma asan_segs_eq : ASEGS = [AsanUbsan_segment_000; AsanUbsan_segment_001;
                              AsanUbsan_segment_002; AsanUbsan_segment_003].
Proof. reflexivity. Qed.

Lemma asan_rw_window : forall m (x : word),
  0x571000 <= bv_unsigned x < 0xc04000 -> wview ASEGS m x <> None.
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
    + cbn -[segment_byte_at]. apply (segment_byte_at_some_pt _ 495616); [exact asan_hex2 | rewrite asan_len2; lia | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
    + cbn -[segment_byte_at]. apply (segment_byte_at_some_pt _ 6397952); [exact asan_hex3_pt | rewrite asan_len3; lia | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
  - exfalso. destruct (Z.lt_ge_cases (bv_unsigned x) 0x5ea000) as [Hl|Hl].
    + apply (find_segment_none_spec _ _ _ Hf AsanUbsan_segment_002);
        [rewrite asan_segs_eq; cbn; tauto | cbn; lia].
    + apply (find_segment_none_spec _ _ _ Hf AsanUbsan_segment_003);
        [rewrite asan_segs_eq; cbn; tauto | cbn; lia].
Qed.

(* [comment removed for export] *)
Lemma asan_img_facts : img_facts ASEGS ASAN_H APH.
Proof.
  constructor.
  - repeat split; reflexivity.
  - cbn [img_lo img_hi ASAN_H]. lia.
  - vm_compute. reflexivity.
  - exact asan_res_hull.
  - rewrite asan_res_sizes. reflexivity.
  - cbn [rw_lo rw_len ASAN_H]. split; [lia|]. intros m x Hx. apply asan_rw_window. lia.
  - exact asan_shadow_ok.
Qed.

(* [comment removed for export] *)
Lemma itab_ranges_ok : forall rs, itab_sound ASEGS (mk_itab_ranges ASEGS rs).
Proof. intros rs. apply APS.mk_itab_ranges_sound. Qed.
