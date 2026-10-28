(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec StoreOk AgentLib AsanAcct AxSymExec3K AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanPlanSoundSumsK AsanHexScan AsanInitK.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Export Ba0DefsK_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require FxHexScan.   (* [comment removed for export] *)
Import ListNotations.
Import AX2K. Import APCK. Import APK.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition Asan0_top : Z := 0x696000.

(* [comment removed for export] *)
Lemma Asan0_wx_nowrap : wx_segs_nowrap ASEGS0.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma Asan0_segs_below : segs_below_b ASEGS0 Asan0_top = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Asan0_H_off_above : forall H : word -> bool,
  (forall a, H a = true -> (Asan0_top <= bv_unsigned a)%Z) -> H_off_segments ASEGS0 H.
Proof. intros H Ha. exact (H_off_segments_above _ H _ Asan0_segs_below Ha). Qed.
Lemma Asan0_H_off_mkH : forall L A, ranges_from_b L Asan0_top = true -> H_off_segments ASEGS0 (mkH L A).
Proof. intros L A HL. exact (H_off_segments_mkH _ L A _ Asan0_segs_below HL). Qed.

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

Lemma asan0_segs_in_hull : segs_in_hull_b ASEGS0 (img_lo ASAN0) (img_hi ASAN0) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma asan0_in_hull : forall a : word,
  APSK.in_hull ASAN0 (bv_unsigned a) = false -> find_segment ASEGS0 (bv_unsigned a) 1 = None.
Proof.
  intros a H. apply (find_segment1_none_outside ASEGS0 (img_lo ASAN0) (img_hi ASAN0)); [exact asan0_segs_in_hull|].
  unfold APSK.in_hull in H. apply andb_false_iff in H as [H|H]; [apply Z.leb_gt in H; left | apply Z.ltb_ge in H; right]; lia.
Qed.

Lemma asan0_res_len : APSK.res_len_ok ASEGS0 ASAN0.
Proof. vm_compute. reflexivity. Qed.

Lemma asan0_res_eq : segments_reserved ASEGS0 = [(Z_to_bv 64 0x10000, Z_to_bv 64 0x41000); (Z_to_bv 64 0x51000, Z_to_bv 64 0xe0000);
                                            (Z_to_bv 64 0x131000, Z_to_bv 64 0x8000); (Z_to_bv 64 0x139000, Z_to_bv 64 0x55d000)].
Proof. vm_compute. reflexivity. Qed.

Lemma asan0_res_hull : Forall (fun iv => img_lo ASAN0 <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi ASAN0) (segments_reserved ASEGS0).
Proof.
  rewrite asan0_res_eq. cbn [img_lo img_hi ASAN0].
  repeat constructor; cbn [fst snd]; rewrite ?u64_lit by lia; lia.
Qed.

Lemma asan0_hull_ok : APSK.hull_ok ASAN0.
Proof. unfold APSK.hull_ok. cbn [img_lo img_hi ASAN0]. unfold KHI. repeat split; reflexivity || lia. Qed.

Lemma asan0_shadow_ok : APSK.shadow_ok ASAN0.
Proof. unfold APSK.shadow_ok. cbn [shadow_off ASAN0]. lia. Qed.

Lemma asan0_res_sizes : APSK.sum_sizes (segments_reserved ASEGS0) = 0x686000.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma asan0_hex2 : scanN AsanUbsan_seg_bytes_002 64 0 32768 = true.
Proof. apply FxHexScan.FXH.scan_ok; [vm_cast_no_check (@eq_refl bool true)|vm_compute; discriminate]. Qed.
Lemma asan0_hex3 : scanN AsanUbsan_seg_bytes_003 64 0 5623808 = true.
Proof. apply FxHexScan.FXH.scan_ok; [vm_cast_no_check (@eq_refl bool true)|vm_compute; discriminate]. Qed.
Lemma asan0_len2 : Z.to_N (Uint63.to_Z (PrimString.length AsanUbsan_seg_bytes_002) / 2) = 32768%N.
Proof. vm_compute. reflexivity. Qed.
Lemma asan0_len3 : Z.to_N (Uint63.to_Z (PrimString.length AsanUbsan_seg_bytes_003) / 2) = 5623808%N.
Proof. vm_compute. reflexivity. Qed.

Lemma asan0_segs_eq : ASEGS0 = [AsanUbsan_segment_000; AsanUbsan_segment_001;
                                AsanUbsan_segment_002; AsanUbsan_segment_003].
Proof. reflexivity. Qed.

Lemma asan0_rw_window : forall m (x : word),
  0x131000 <= bv_unsigned x < 0x696000 -> wview ASEGS0 m x <> None.
Proof.
  intros m x Hx. unfold wview. destruct (m x); [discriminate|].
  destruct (find_segment ASEGS0 (bv_unsigned x) 1) as [seg|] eqn:Hf.
  - apply find_segment_some_spec in Hf as (Hin & Hb & Ht).
    rewrite asan0_segs_eq in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
      cbn [seg_base seg_size seg_writable seg_perms seg_bytes string_has Ascii.eqb
           AsanUbsan_segment_000 AsanUbsan_segment_001
           AsanUbsan_segment_002 AsanUbsan_segment_003] in Hb, Ht |- *.
    + exfalso. lia.
    + exfalso. lia.
    + cbn -[segment_byte_at]. apply (segment_byte_at_some1 _ 32768); [exact asan0_hex2 | rewrite asan0_len2; lia | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
    + cbn -[segment_byte_at]. apply (segment_byte_at_some1 _ 5623808); [exact asan0_hex3 | rewrite asan0_len3; lia | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
  - exfalso. destruct (Z.lt_ge_cases (bv_unsigned x) 0x139000) as [Hl|Hl].
    + apply (find_segment_none_spec _ _ _ Hf AsanUbsan_segment_002);
        [rewrite asan0_segs_eq; cbn; tauto | cbn; lia].
    + apply (find_segment_none_spec _ _ _ Hf AsanUbsan_segment_003);
        [rewrite asan0_segs_eq; cbn; tauto | cbn; lia].
Qed.

(* [comment removed for export] *)
Lemma asan0_hull_tiled : forall z, img_lo ASAN0 <= z < img_hi ASAN0 -> APSK.in_ivs z (segments_reserved ASEGS0) = true.
Proof.
  intros z Hz. cbn [img_lo img_hi ASAN0] in Hz. rewrite asan0_res_eq. unfold APSK.in_ivs. cbn [existsb fst snd].
  rewrite !u64_lit by lia.
  destruct (Z.lt_ge_cases z 0x51000) as [H1|H1].
  { apply orb_true_iff. left. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  apply orb_true_iff. right.
  destruct (Z.lt_ge_cases z 0x131000) as [H2|H2].
  { apply orb_true_iff. left. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  apply orb_true_iff. right.
  destruct (Z.lt_ge_cases z 0x139000) as [H3|H3].
  { apply orb_true_iff. left. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  apply orb_true_iff. right.
  apply orb_true_iff. left. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Lemma asan0_hull_lt : img_lo ASAN0 < img_hi ASAN0.
Proof. cbn [img_lo img_hi ASAN0]. lia. Qed.

(* [comment removed for export] *)
Lemma segs_wr_of_forallb : forall segs,
  forallb (fun seg => negb (seg_writable seg) || seg_readable seg)%bool segs = true -> APSXK.segs_wr_ok segs.
Proof.
  intros segs H seg Hin Hw. pose proof (proj1 (forallb_forall _ _) H seg Hin) as Hs. cbn beta in Hs.
  rewrite Hw in Hs. exact Hs.
Qed.

Lemma asan0_segs_wr : APSXK.segs_wr_ok ASEGS0.
Proof. apply segs_wr_of_forallb. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma asan0_img_facts : img_facts ASEGS0 ASAN0 APH0.
Proof.
  constructor.
  - repeat split; reflexivity.
  - cbn [img_lo img_hi ASAN0]. lia.
  - vm_compute. reflexivity.
  - exact asan0_res_hull.
  - rewrite asan0_res_sizes. reflexivity.
  - cbn [rw_lo rw_len ASAN0]. split; [lia|]. intros m x Hx. apply asan0_rw_window. lia.
  - exact asan0_shadow_ok.
Qed.
