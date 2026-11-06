(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.simdjson.fuzz_utf8.images Require Import Ubsan.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec StoreOk AgentLib AsanAcct AxSymExec3 AsanPlan AsanPlanSound AsanHexScan AsanInit. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import AsanNodesArg AsanNodesRP ImgParams.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition SEGS_utf8_ubsan : list Segment := Ubsan.M.loaded_segments.
Definition PH_utf8_ubsan : PhdrInfo := Ubsan.M.phdrs.
(* [comment removed for export] *)
Definition LIMIT_utf8_ubsan : Z := target_alloc_limit.

Definition AT_utf8_ubsan : atable :=
  {| img_lo := 0x10000; img_hi := 0x10f000; n_res := 4; shadow_off := 0x0;  (* [comment removed for export] *)
     a_entry := 0x3adac; rw_lo := 0xd4000; rw_len := 0x3b000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 10;
     x_imemset := 0x0; x_imemcpy := 0x0; x_memset := 0xce854; x_memcpy := 0xce2d4; x_memiszero := 0x0;
     x_istrncpy := 0x0; x_sealed := 0x0; x_popfree := 0x0; x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
     x_envscan := 0xbcc5c; x_envscan_k := 0xbcc68; x_pnscan := 0xbcd20; x_pnscan_k := 0xbcd2c;
     stops_more := [] |}.
Definition init_utf8_ubsan : acs := init_acs_of AT_utf8_ubsan.
(* [comment removed for export] *)
Definition ARG_utf8_ubsan : AN.argtab :=
  {| AN.g_istrlen := 0x0; AN.g_memchr := 0xce1d8; AN.g_stdio_write := 0xc280c; AN.g_exit := 0xbd58c;
     AN.g_file_lo := 0xdb468; AN.g_file_hi := 0xdb730; AN.g_canary_got := 0xda068; AN.g_canary := 0x10dce8;
     AN.g_ro_lo := 0x134d8; AN.g_ro_hi := 0x134f8 |}.
(* [comment removed for export] *)
Definition MT_utf8_ubsan : mtab :=
  {| mt_enframe := 0xc0df4; mt_getmeta := 0xbfa20; mt_free := 0xbf854; mt_free_k := 0xbf930;
     mt_sct := 0x21550; mt_secret := 0x10de88 |}.
(* [comment removed for export] *)
Definition RPT_utf8_ubsan : RPN.rptab :=
  RPN.RPT 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0.
(* [comment removed for export] *)
Definition IP_utf8_ubsan : imgparams := IP SEGS_utf8_ubsan AT_utf8_ubsan ARG_utf8_ubsan LIMIT_utf8_ubsan MT_utf8_ubsan RPT_utf8_ubsan.
Lemma utf8_ubsan_arg_ro_hull : img_lo AT_utf8_ubsan <= AN.g_ro_lo ARG_utf8_ubsan /\ AN.g_ro_hi ARG_utf8_ubsan <= img_hi AT_utf8_ubsan.
Proof. cbn. lia. Qed.
Lemma utf8_ubsan_arg_file : img_lo AT_utf8_ubsan <= AN.g_file_lo ARG_utf8_ubsan /\ AN.g_file_hi ARG_utf8_ubsan <= img_hi AT_utf8_ubsan
  /\ img_lo AT_utf8_ubsan <= AN.g_canary_got ARG_utf8_ubsan /\ AN.g_canary_got ARG_utf8_ubsan + 8 <= img_hi AT_utf8_ubsan
  /\ img_lo AT_utf8_ubsan <= AN.g_canary ARG_utf8_ubsan /\ AN.g_canary ARG_utf8_ubsan + 8 <= img_hi AT_utf8_ubsan.
Proof. cbn. lia. Qed.
(* [comment removed for export] *)
Definition TEXT_LO_utf8_ubsan : Z := 0x3a000.
Definition TEXT_N_utf8_ubsan : nat := 157696.
Definition IT_utf8_ubsan (rs : list (Z * nat)) : itab := mk_itab_ranges SEGS_utf8_ubsan rs.
Lemma IT_utf8_ubsan_ok : forall rs, itab_sound SEGS_utf8_ubsan (IT_utf8_ubsan rs).
Proof. intros rs. apply APS.mk_itab_ranges_sound. Qed.

(* [comment removed for export] *)
Lemma utf8_ubsan_wx : wx_segs_nowrap SEGS_utf8_ubsan.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

Definition segs_in_hull_b (segs : list Segment) (lo hi : Z) : bool :=
  forallb (fun seg => (lo <=? Z.of_N (seg_base seg)) && (Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <=? hi))%bool segs.

Lemma find_segment1_none_outside_utf8_ubsan : forall segs lo hi x,
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

Lemma utf8_ubsan_segs_in_hull : segs_in_hull_b SEGS_utf8_ubsan (img_lo AT_utf8_ubsan) (img_hi AT_utf8_ubsan) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma utf8_ubsan_in_hull : forall a : word,
  APS.in_hull AT_utf8_ubsan (bv_unsigned a) = false -> find_segment SEGS_utf8_ubsan (bv_unsigned a) 1 = None.
Proof.
  intros a H. apply (find_segment1_none_outside_utf8_ubsan SEGS_utf8_ubsan (img_lo AT_utf8_ubsan) (img_hi AT_utf8_ubsan)); [exact utf8_ubsan_segs_in_hull|].
  unfold APS.in_hull in H. apply andb_false_iff in H as [H|H]; [apply Z.leb_gt in H; left | apply Z.ltb_ge in H; right]; lia.
Qed.

Lemma utf8_ubsan_res_len : APS.res_len_ok SEGS_utf8_ubsan AT_utf8_ubsan.
Proof. vm_compute. reflexivity. Qed.

Lemma utf8_ubsan_res_eq : segments_reserved SEGS_utf8_ubsan = [(Z_to_bv 64 0x10000, Z_to_bv 64 0x2a000); (Z_to_bv 64 0x3a000, Z_to_bv 64 0x9a000); (Z_to_bv 64 0xd4000, Z_to_bv 64 0x7000); (Z_to_bv 64 0xdb000, Z_to_bv 64 0x34000)].
Proof. vm_compute. reflexivity. Qed.

Lemma utf8_ubsan_res_hull : Forall (fun iv => img_lo AT_utf8_ubsan <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi AT_utf8_ubsan)
                             (segments_reserved SEGS_utf8_ubsan).
Proof.
  rewrite utf8_ubsan_res_eq. cbn [img_lo img_hi AT_utf8_ubsan].
  repeat constructor; cbn [fst snd]; rewrite ?u64_lit by lia; lia.
Qed.

Lemma utf8_ubsan_hull_ok : APS.hull_ok AT_utf8_ubsan.
Proof. unfold APS.hull_ok. cbn [img_lo img_hi AT_utf8_ubsan]. unfold KHI. repeat split; reflexivity || lia. Qed.

Lemma utf8_ubsan_shadow_ok : APS.shadow_ok AT_utf8_ubsan.
Proof. unfold APS.shadow_ok. cbn [shadow_off AT_utf8_ubsan]. lia. Qed.

Lemma utf8_ubsan_plain : plain AT_utf8_ubsan = true.
Proof. reflexivity. Qed.

Lemma utf8_ubsan_res_sizes : APS.sum_sizes (segments_reserved SEGS_utf8_ubsan) = 0xff000.
Proof. vm_compute. reflexivity. Qed.

Lemma utf8_ubsan_segs_eq : SEGS_utf8_ubsan = [Ubsan_segment_000; Ubsan_segment_001; Ubsan_segment_002; Ubsan_segment_003].
Proof. reflexivity. Qed.

Lemma utf8_ubsan_hex2 : scanN Ubsan_seg_bytes_002 64 0 28672 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma utf8_ubsan_len2 : Z.to_N (Uint63.to_Z (PrimString.length Ubsan_seg_bytes_002) / 2) = 28672%N.
Proof. vm_compute. reflexivity. Qed.

Lemma utf8_ubsan_hex3 : scanN Ubsan_seg_bytes_003 64 0 212992 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma utf8_ubsan_len3 : Z.to_N (Uint63.to_Z (PrimString.length Ubsan_seg_bytes_003) / 2) = 212992%N.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma utf8_ubsan_rw_window : forall m (x : word),
  0xd4000 <= bv_unsigned x < 0x10f000 -> wview SEGS_utf8_ubsan m x <> None.
Proof.
  intros m x Hx. unfold wview. destruct (m x); [discriminate|].
  destruct (find_segment SEGS_utf8_ubsan (bv_unsigned x) 1) as [seg|] eqn:Hf.
  - apply find_segment_some_spec in Hf as (Hin & Hb & Ht).
    rewrite utf8_ubsan_segs_eq in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
      cbn [seg_base seg_size seg_writable seg_perms seg_bytes string_has Ascii.eqb Ubsan_segment_000 Ubsan_segment_001 Ubsan_segment_002 Ubsan_segment_003] in Hb, Ht |- *.
    + exfalso. lia.
    + exfalso. lia.
    + cbn -[segment_byte_at]. apply (segment_byte_at_some1 _ 28672); [exact utf8_ubsan_hex2 | rewrite utf8_ubsan_len2; lia | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
    + cbn -[segment_byte_at]. apply (segment_byte_at_some1 _ 212992); [exact utf8_ubsan_hex3 | rewrite utf8_ubsan_len3; lia | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
  - exfalso.
    destruct (Z.lt_ge_cases (bv_unsigned x) 0xdb000) as [Hl0|Hl0].
    { apply (find_segment_none_spec _ _ _ Hf Ubsan_segment_002); [rewrite utf8_ubsan_segs_eq; cbn; tauto | cbn; lia]. }
    apply (find_segment_none_spec _ _ _ Hf Ubsan_segment_003); [rewrite utf8_ubsan_segs_eq; cbn; tauto | cbn; lia].
Qed.

(* [comment removed for export] *)
Lemma utf8_ubsan_img_facts : img_facts SEGS_utf8_ubsan AT_utf8_ubsan PH_utf8_ubsan.
Proof.
  constructor.
  - repeat split; reflexivity.
  - cbn [img_lo img_hi AT_utf8_ubsan]. lia.
  - vm_compute. reflexivity.
  - exact utf8_ubsan_res_hull.
  - rewrite utf8_ubsan_res_sizes. reflexivity.
  - cbn [rw_lo rw_len AT_utf8_ubsan]. split; [lia|]. intros m x Hx. apply utf8_ubsan_rw_window. lia.
  - exact utf8_ubsan_shadow_ok.
Qed.
