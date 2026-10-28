(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.simdjson.fuzz_implementations.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import PropExec StoreOk AgentLib AsanAcct AsanAcctImagesB AxSymExec3 AsanPlan AsanPlanSound AsanHexScan AsanHexZero AsanTablesB.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require AsanNodesMmLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AP.
Open Scope Z_scope.

Definition ASEGS := AsanUbsan.M.loaded_segments.
Definition AITAB : itab := mk_itab ASEGS ASAN_B_TEXT_LO ASAN_B_TEXT_N.

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

Lemma asan_segs_in_hull : segs_in_hull_b ASEGS (img_lo ASAN_B) (img_hi ASAN_B) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma asan_in_hull : forall a : word,
  APS.in_hull ASAN_B (bv_unsigned a) = false -> find_segment ASEGS (bv_unsigned a) 1 = None.
Proof.
  intros a H. apply (find_segment1_none_outside ASEGS (img_lo ASAN_B) (img_hi ASAN_B)); [exact asan_segs_in_hull|].
  unfold APS.in_hull in H. apply andb_false_iff in H as [H|H]; [apply Z.leb_gt in H; left | apply Z.ltb_ge in H; right]; lia.
Qed.

Lemma asan_res_len : APS.res_len_ok ASEGS ASAN_B.
Proof. vm_compute. reflexivity. Qed.

Lemma asan_res_hull : Forall (fun iv => img_lo ASAN_B <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi ASAN_B) (segments_reserved ASEGS).
Proof.
  assert (E : segments_reserved ASEGS = [(Z_to_bv 64 0x10000, Z_to_bv 64 0x4d000); (Z_to_bv 64 0x5d000, Z_to_bv 64 0x11c000);
                                         (Z_to_bv 64 0x179000, Z_to_bv 64 0x8000); (Z_to_bv 64 0x181000, Z_to_bv 64 0x55f000)])
    by (vm_compute; reflexivity).
  rewrite E. cbn [img_lo img_hi ASAN_B].
  repeat constructor; cbn [fst snd]; rewrite ?u64_lit by lia; lia.
Qed.

Lemma asan_hull_cover : AsanNodesMmLib.hull_cover ASEGS ASAN_B.
Proof.
  assert (E : segments_reserved ASEGS = [(Z_to_bv 64 0x10000, Z_to_bv 64 0x4d000); (Z_to_bv 64 0x5d000, Z_to_bv 64 0x11c000);
                                         (Z_to_bv 64 0x179000, Z_to_bv 64 0x8000); (Z_to_bv 64 0x181000, Z_to_bv 64 0x55f000)])
    by (vm_compute; reflexivity).
  unfold AsanNodesMmLib.hull_cover. rewrite E. cbn [img_lo img_hi ASAN_B]. split; [lia|]. intros z Hz.
  destruct (Z_lt_le_dec z 0x5d000); [exists (Z_to_bv 64 0x10000, Z_to_bv 64 0x4d000); split; [left; reflexivity|]|].
  { cbn [fst snd]. rewrite !u64_lit by lia. lia. }
  destruct (Z_lt_le_dec z 0x179000); [exists (Z_to_bv 64 0x5d000, Z_to_bv 64 0x11c000); split; [right; left; reflexivity|]|].
  { cbn [fst snd]. rewrite !u64_lit by lia. lia. }
  destruct (Z_lt_le_dec z 0x181000); [exists (Z_to_bv 64 0x179000, Z_to_bv 64 0x8000); split; [right; right; left; reflexivity|]|].
  { cbn [fst snd]. rewrite !u64_lit by lia. lia. }
  exists (Z_to_bv 64 0x181000, Z_to_bv 64 0x55f000). split; [right; right; right; left; reflexivity|].
  cbn [fst snd]. rewrite !u64_lit by lia. lia.
Qed.

Lemma asan_hull_ok : APS.hull_ok ASAN_B.
Proof. unfold APS.hull_ok. cbn [img_lo img_hi ASAN_B]. unfold KHI. repeat split; reflexivity || lia. Qed.

Lemma asan_shadow_ok : APS.shadow_ok ASAN_B.
Proof. unfold APS.shadow_ok. cbn [shadow_off ASAN_B]. lia. Qed.

Lemma asan_res_sizes : APS.sum_sizes (segments_reserved ASEGS) = 0x6d0000.
Proof. vm_compute. reflexivity. Qed.

Lemma asan_hex2 : scanN AsanUbsan_seg_bytes_002 64 0 32768 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma asan_hex3 : scanN AsanUbsan_seg_bytes_003 64 0 5632000 = true.
Proof.
  apply (scanN_prefix_zwin AsanUbsan_seg_bytes_003 24576 5632000 (Uint63.of_Z 49152) (Uint63.of_Z 11214848)).
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - reflexivity.
  - reflexivity.
  - vm_compute. discriminate.
  - vm_compute. discriminate.
Qed.
Lemma asan_len2 : Z.to_N (Uint63.to_Z (PrimString.length AsanUbsan_seg_bytes_002) / 2) = 32768%N.
Proof. vm_compute. reflexivity. Qed.
Lemma asan_len3 : Z.to_N (Uint63.to_Z (PrimString.length AsanUbsan_seg_bytes_003) / 2) = 5632000%N.
Proof. vm_compute. reflexivity. Qed.

Lemma asan_segs_eq : ASEGS = [AsanUbsan_segment_000; AsanUbsan_segment_001;
                              AsanUbsan_segment_002; AsanUbsan_segment_003].
Proof. reflexivity. Qed.

Lemma asan_rw_window : forall m (x : word),
  0x179000 <= bv_unsigned x < 0x6e0000 -> wview ASEGS m x <> None.
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
    + cbn -[segment_byte_at]. apply (segment_byte_at_some1 _ 32768); [exact asan_hex2 | rewrite asan_len2; lia | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
    + cbn -[segment_byte_at]. apply (segment_byte_at_some1 _ 5632000); [exact asan_hex3 | rewrite asan_len3; lia | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
  - exfalso. destruct (Z.lt_ge_cases (bv_unsigned x) 0x181000) as [Hl|Hl].
    + apply (find_segment_none_spec _ _ _ Hf AsanUbsan_segment_002);
        [rewrite asan_segs_eq; cbn; tauto | cbn; lia].
    + apply (find_segment_none_spec _ _ _ Hf AsanUbsan_segment_003);
        [rewrite asan_segs_eq; cbn; tauto | cbn; lia].
Qed.

From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import AsanInit.
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.

Definition APH : PhdrInfo := AsanUbsan.M.phdrs.

Lemma asan_img_facts : img_facts ASEGS ASAN_B APH.
Proof.
  constructor.
  - repeat split; reflexivity.
  - cbn [img_lo img_hi ASAN_B]. lia.
  - vm_compute. reflexivity.
  - exact asan_res_hull.
  - rewrite asan_res_sizes. reflexivity.
  - cbn [rw_lo rw_len ASAN_B]. split; [lia|]. intros m x Hx. apply asan_rw_window. lia.
  - exact asan_shadow_ok.
Qed.
