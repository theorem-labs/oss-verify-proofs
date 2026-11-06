(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import Uint63.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.coturn.FuzzStunClient.images Require Import AsanUbsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec StoreOk AgentLib AsanAcct.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AsanHexScan3.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AsanAcctImages AxSymExec3 AsanPlan AsanPlanSound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AP.
Open Scope Z_scope.

Definition BSEGS := AsanUbsan.M.loaded_segments.
Definition AITAB : itab := mk_itab BSEGS BOTH_TEXT_LO BOTH_TEXT_N.

Lemma both_IT_ok : itab_sound BSEGS AITAB.
Proof. apply mk_itab_sound. Qed.

Lemma both_wx : wx_segs_nowrap BSEGS.
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

Lemma both_res_hull : Forall (fun iv => img_lo BOTH <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi BOTH) (segments_reserved BSEGS).
Proof.
  assert (E : segments_reserved BSEGS = [(Z_to_bv 64 0x10000, Z_to_bv 64 0x22000); (Z_to_bv 64 0x32000, Z_to_bv 64 0x76000);
                                         (Z_to_bv 64 0xa8000, Z_to_bv 64 0x3000); (Z_to_bv 64 0xab000, Z_to_bv 64 0x55c000)])
    by (vm_compute; reflexivity).
  rewrite E. cbn [img_lo img_hi BOTH].
  repeat constructor; cbn [fst snd]; rewrite ?u64_lit by lia; lia.
Qed.

Lemma both_hull_ok : APS.hull_ok BOTH.
Proof. unfold APS.hull_ok. cbn [img_lo img_hi BOTH]. unfold KHI. repeat split; reflexivity || lia. Qed.

Lemma both_shadow_ok : APS.shadow_ok BOTH.
Proof. unfold APS.shadow_ok. cbn [shadow_off BOTH]. lia. Qed.

Lemma both_res_sizes : APS.sum_sizes (segments_reserved BSEGS) = 0x5f7000.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma both_hex2 : blocks_ok AsanUbsan_seg_bytes_002 64 0 6 = true.   (* [comment removed for export] *)
Proof. vm_compute. reflexivity. Qed.
Lemma both_hex3 : blocks_ok AsanUbsan_seg_bytes_003 64 0 2744 = true.   (* [comment removed for export] *)
Proof. vm_compute. reflexivity. Qed.
Lemma both_len2 : Uint63.to_Z (PrimString.length AsanUbsan_seg_bytes_002) = 24576.
Proof. vm_compute. reflexivity. Qed.
Lemma both_len3 : Uint63.to_Z (PrimString.length AsanUbsan_seg_bytes_003) = 11239424.
Proof. vm_compute. reflexivity. Qed.

Lemma both_segs_eq : BSEGS = [AsanUbsan_segment_000; AsanUbsan_segment_001;
                              AsanUbsan_segment_002; AsanUbsan_segment_003].
Proof. reflexivity. Qed.

Lemma both_rw_window : forall m (x : word),
  0xa8000 <= bv_unsigned x < 0x607000 -> wview BSEGS m x <> None.
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
    + cbn -[segment_byte_at]. apply (segment_byte_at_some3 _ 6%N); [exact both_hex2 | lia | rewrite both_len2; vm_compute; intro HX; discriminate HX | rewrite Z2N.id by lia; cbn in Hb, Ht; change (Z.of_N 6%N) with 6; lia].
    + cbn -[segment_byte_at]. apply (segment_byte_at_some3 _ 2744%N); [exact both_hex3 | lia | rewrite both_len3; vm_compute; intro HX; discriminate HX | rewrite Z2N.id by lia; cbn in Hb, Ht; change (Z.of_N 2744%N) with 2744; lia].
  - exfalso. destruct (Z.lt_ge_cases (bv_unsigned x) 0xab000) as [Hl|Hl].
    + apply (find_segment_none_spec _ _ _ Hf AsanUbsan_segment_002);
        [rewrite both_segs_eq; cbn; tauto | cbn; lia].
    + apply (find_segment_none_spec _ _ _ Hf AsanUbsan_segment_003);
        [rewrite both_segs_eq; cbn; tauto | cbn; lia].
Qed.

(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AsanInit.
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition APH : PhdrInfo := AsanUbsan.M.phdrs.

Lemma both_img_facts : img_facts BSEGS BOTH APH.
Proof.
  constructor.
  - repeat split; reflexivity.
  - cbn [img_lo img_hi BOTH]. lia.
  - vm_compute. reflexivity.
  - exact both_res_hull.
  - rewrite both_res_sizes. reflexivity.
  - cbn [rw_lo rw_len BOTH]. split; [lia|]. intros m x Hx. apply both_rw_window. lia.
  - exact both_shadow_ok.
Qed.
