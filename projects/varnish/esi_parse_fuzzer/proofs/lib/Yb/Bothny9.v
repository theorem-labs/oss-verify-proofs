(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec StoreOk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanAcct AxSyioe Asanhz7.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.AgentLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanAcct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AxSyioe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanhz7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanoq0 AsanPlan Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanPlan.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanoq0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.Asanfbz.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asan672.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
From Stdlib Require Uint63.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AP.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.

Definition BSEGS := AsanUbsan.M.loaded_segments.
Definition BITAB : itab := mk_itab BSEGS BOTH_TEXT_LO BOTH_TEXT_N.

Lemma both_IT_ok : itab_sound BSEGS BITAB.
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
  assert (E : segments_reserved BSEGS = [(Z_to_bv 64 0x10000, Z_to_bv 64 0x25000); (Z_to_bv 64 0x35000, Z_to_bv 64 0x73000);
                                         (Z_to_bv 64 0xa8000, Z_to_bv 64 0x2000); (Z_to_bv 64 0xaa000, Z_to_bv 64 0x560000)])
    by (vm_compute; reflexivity).
  rewrite E. cbn [img_lo img_hi BOTH].
  repeat constructor; cbn [fst snd]; rewrite ?u64_lit by lia; lia.
Qed.

Lemma both_hull_ok : APS.hull_ok BOTH.
Proof. unfold APS.hull_ok. cbn [img_lo img_hi BOTH]. unfold KHI. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity || lia. Qed.

Lemma both_shadow_ok : APS.shadow_ok BOTH.
Proof. unfold APS.shadow_ok. cbn [shadow_off BOTH]. lia. Qed.

Lemma both_res_sizes : APS.sum_sizes (segments_reserved BSEGS) = 0x5fa000.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma both_hex2 : scanN AsanUbsan_seg_bytes_002 64 0 8192 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma both_hex3 : scanN AsanUbsan_seg_bytes_003 64 0 5636096 = true.
Proof. (* [comment removed for export] *)
  apply (Asan672.scanN_prefix_zwin AsanUbsan_seg_bytes_003 32768 5636096 (Uint63.of_Z 65536) (Uint63.of_Z 11206656)).
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - reflexivity.
  - reflexivity.
  - vm_compute. discriminate.
  - vm_compute. discriminate.
Qed.
Lemma both_len2 : Z.to_N (Uint63.to_Z (PrimString.length AsanUbsan_seg_bytes_002) / 2) = 8192%N.
Proof. vm_compute. reflexivity. Qed.
Lemma both_len3 : Z.to_N (Uint63.to_Z (PrimString.length AsanUbsan_seg_bytes_003) / 2) = 5636096%N.
Proof. vm_compute. reflexivity. Qed.

Lemma both_segs_eq : BSEGS = [AsanUbsan_segment_000; AsanUbsan_segment_001;
                              AsanUbsan_segment_002; AsanUbsan_segment_003].
Proof. reflexivity. Qed.

Lemma both_rw_window : forall m (x : word),
  0xa8000 <= bv_unsigned x < 0x60a000 -> wview BSEGS m x <> None.
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
    + cbn -[segment_byte_at]. apply (segment_byte_at_some1 _ 8192); [exact both_hex2 | rewrite both_len2; lia | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
    + cbn -[segment_byte_at]. apply (segment_byte_at_some1 _ 5636096); [exact both_hex3 | rewrite both_len3; lia | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
  - exfalso. destruct (Z.lt_ge_cases (bv_unsigned x) 0xaa000) as [Hl|Hl].
    + apply (find_segment_none_spec _ _ _ Hf AsanUbsan_segment_002);
        [rewrite both_segs_eq; cbn; tauto | cbn; lia].
    + apply (find_segment_none_spec _ _ _ Hf AsanUbsan_segment_003);
        [rewrite both_segs_eq; cbn; tauto | cbn; lia].
Qed.

(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Import AsanInit.
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.

Definition BPH : PhdrInfo := AsanUbsan.M.phdrs.

Lemma both_img_facts : img_facts BSEGS BOTH BPH.
Proof.
  constructor.
  - OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity.
  - cbn [img_lo img_hi BOTH]. lia.
  - vm_compute. reflexivity.
  - exact both_res_hull.
  - rewrite both_res_sizes. reflexivity.
  - cbn [rw_lo rw_len BOTH]. split; [lia|]. intros m x Hx. apply both_rw_window. lia.
  - exact both_shadow_ok.
Qed.

(* [comment removed for export] *)
Lemma both_res_cover : APS.res_cover_ok BSEGS BOTH.
Proof.
  split; [cbn [img_lo img_hi BOTH]; lia|].
  assert (E : segments_reserved BSEGS = [(Z_to_bv 64 0x10000, Z_to_bv 64 0x25000); (Z_to_bv 64 0x35000, Z_to_bv 64 0x73000);
                                         (Z_to_bv 64 0xa8000, Z_to_bv 64 0x2000); (Z_to_bv 64 0xaa000, Z_to_bv 64 0x560000)])
    by (vm_compute; reflexivity).
  rewrite E. cbn [img_lo img_hi BOTH]. intros z Hz. unfold APS.in_ivs. cbn [existsb fst snd]. rewrite !u64_lit by lia.
  destruct (Z.lt_ge_cases z 0x35000); [|destruct (Z.lt_ge_cases z 0xa8000); [|destruct (Z.lt_ge_cases z 0xaa000)]].
  - rewrite (proj2 (Z.leb_le 0x10000 z)), (proj2 (Z.ltb_lt z (0x10000 + 0x25000))) by lia. reflexivity.
  - rewrite (proj2 (Z.leb_le 0x35000 z)), (proj2 (Z.ltb_lt z (0x35000 + 0x73000))) by lia. cbn [andb orb]. rewrite ?orb_true_r. reflexivity.
  - rewrite (proj2 (Z.leb_le 0xa8000 z)), (proj2 (Z.ltb_lt z (0xa8000 + 0x2000))) by lia. cbn [andb orb]. rewrite ?orb_true_r. reflexivity.
  - rewrite (proj2 (Z.leb_le 0xaa000 z)), (proj2 (Z.ltb_lt z (0xaa000 + 0x560000))) by lia. cbn [andb orb]. rewrite ?orb_true_r. reflexivity.
Qed.

Lemma both_shadow_val : APS.shadow_val_ok BOTH.
Proof. reflexivity. Qed.
