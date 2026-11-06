(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.yajl_ruby.json_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import PropExec.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.XQ Require Import StoreOk AgentLib AsanAcct AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanHexScan.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.XQ Require Import AsanNodesMmCs AsanPlanSoundSums AsanInit.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.BS5 Require Import AsanHexB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Import AX2. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition BOTH5 : atable :=
  {| img_lo := 0x10000; img_hi := 0x603000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x317c8; rw_lo := 0xa5000; rw_len := 0x55e000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x65228; x_imemcpy := 0x651ac; x_memset := 0x9ecd0; x_memcpy := 0x9e8cc; x_memiszero := 0x65758;
     x_istrncpy := 0x65654; x_sealed := 0x1187a; x_popfree := 0x37dc0;
     x_sniff := 0; sniff_tab := 0; sniff_cell := 0;                       (* [comment removed for export] *)
     x_envscan := 0x91f1c; x_envscan_k := 0x91f28; x_pnscan := 0x91fe0; x_pnscan_k := 0x91fec;
     x_maxva := 0x66870; x_maxva_k := 0x668e0; z_lo := 0x7fff7000; z_hi := 0x10007fff8000;
     stops_more := [] |}.
(* [comment removed for export] *)
Definition BOTH5_TEXT_LO : Z := 0x317c8.
Definition BOTH5_TEXT_N : nat := 117117.

Definition BSEGS := AsanUbsan.M.loaded_segments.
Definition BPH : PhdrInfo := AsanUbsan.M.phdrs.
Definition BITAB : itab := mk_itab BSEGS BOTH5_TEXT_LO BOTH5_TEXT_N.

Lemma both_IT_ok : itab_sound BSEGS BITAB.
Proof. apply mk_itab_sound. Qed.

Lemma both_wx : wx_segs_nowrap BSEGS.
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

Lemma both_segs_in_hull : segs_in_hull_b BSEGS (img_lo BOTH5) (img_hi BOTH5) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma both_in_hull : forall a : word,
  APS.in_hull BOTH5 (bv_unsigned a) = false -> find_segment BSEGS (bv_unsigned a) 1 = None.
Proof.
  intros a H. apply (find_segment1_none_outside BSEGS (img_lo BOTH5) (img_hi BOTH5)); [exact both_segs_in_hull|].
  unfold APS.in_hull in H. apply andb_false_iff in H as [H|H]; [apply Z.leb_gt in H; left | apply Z.ltb_ge in H; right]; lia.
Qed.

Lemma both_res_len : APS.res_len_ok BSEGS BOTH5.
Proof. vm_compute. reflexivity. Qed.

Lemma both_reserved_eq : segments_reserved BSEGS
  = [(Z_to_bv 64 0x10000, Z_to_bv 64 0x21000); (Z_to_bv 64 0x31000, Z_to_bv 64 0x74000);
     (Z_to_bv 64 0xa5000, Z_to_bv 64 0x2000); (Z_to_bv 64 0xa7000, Z_to_bv 64 0x55c000)].
Proof. vm_compute. reflexivity. Qed.

Lemma both_res_hull : Forall (fun iv => img_lo BOTH5 <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi BOTH5) (segments_reserved BSEGS).
Proof.
  rewrite both_reserved_eq. cbn [img_lo img_hi BOTH5].
  repeat constructor; cbn [fst snd]; rewrite ?u64_lit by lia; lia.
Qed.

Lemma both_hull_ok : APS.hull_ok BOTH5.
Proof. unfold APS.hull_ok. cbn [img_lo img_hi BOTH5]. unfold KHI. repeat split; reflexivity || lia. Qed.

Lemma both_shadow_ok : APS.shadow_ok BOTH5.
Proof. unfold APS.shadow_ok. cbn [shadow_off BOTH5]. lia. Qed.

Lemma both_res_sizes : APS.sum_sizes (segments_reserved BSEGS) = 0x5f3000.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma both_res_cover : res_cover_def BSEGS BOTH5.
Proof.
  split; [cbn; lia|]. intros z Hz. cbn [img_lo img_hi BOTH5] in Hz. rewrite both_reserved_eq.
  unfold APS.in_ivs. cbn [existsb fst snd]. rewrite !u64_lit by lia.
  destruct (Z.lt_ge_cases z 0x31000); [|destruct (Z.lt_ge_cases z 0xa5000); [|destruct (Z.lt_ge_cases z 0xa7000)]].
  - rewrite (proj2 (Z.leb_le 0x10000 z)), (proj2 (Z.ltb_lt z (0x10000 + 0x21000))) by lia. reflexivity.
  - rewrite (proj2 (Z.leb_le 0x31000 z)), (proj2 (Z.ltb_lt z (0x31000 + 0x74000))) by lia. cbn [andb orb]. rewrite ?orb_true_r. reflexivity.
  - rewrite (proj2 (Z.leb_le 0xa5000 z)), (proj2 (Z.ltb_lt z (0xa5000 + 0x2000))) by lia. cbn [andb orb]. rewrite ?orb_true_r. reflexivity.
  - rewrite (proj2 (Z.leb_le 0xa7000 z)), (proj2 (Z.ltb_lt z (0xa7000 + 0x55c000))) by lia. cbn [andb orb]. rewrite ?orb_true_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma both_segs_wr : APSX.segs_wr_ok BSEGS.
Proof.
  intros seg Hin Hw. cbn in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; reflexivity || discriminate Hw.
Qed.

(* [comment removed for export] *)
Lemma both_segs_eq : BSEGS = [AsanUbsan_segment_000; AsanUbsan_segment_001;
                              AsanUbsan_segment_002; AsanUbsan_segment_003].
Proof. reflexivity. Qed.

Lemma both_rw_window : forall m (x : word),
  0xa5000 <= bv_unsigned x < 0x603000 -> wview BSEGS m x <> None.
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
    + cbn -[segment_byte_at]. apply both_seg3_some. rewrite Z2N.id by lia. cbn in Hb, Ht. lia.   (* [comment removed for export] *)
  - exfalso. destruct (Z.lt_ge_cases (bv_unsigned x) 0xa7000) as [Hl|Hl].
    + apply (find_segment_none_spec _ _ _ Hf AsanUbsan_segment_002);
        [rewrite both_segs_eq; cbn; tauto | cbn; lia].
    + apply (find_segment_none_spec _ _ _ Hf AsanUbsan_segment_003);
        [rewrite both_segs_eq; cbn; tauto | cbn; lia].
Qed.

(* [comment removed for export] *)
Lemma both_img_facts : img_facts BSEGS BOTH5 BPH.
Proof.
  constructor.
  - repeat split; reflexivity.
  - cbn [img_lo img_hi BOTH5]. lia.
  - vm_compute. reflexivity.
  - exact both_res_hull.
  - rewrite both_res_sizes. reflexivity.
  - cbn [rw_lo rw_len BOTH5]. split; [lia|]. intros m x Hx. apply both_rw_window. lia.
  - exact both_shadow_ok.
Qed.
