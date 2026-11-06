(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.simdjson.fuzz_utf8.images Require Import Plain.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec StoreOk AgentLib AsanAcct AxSymExec3 AsanPlan AsanPlanSound AsanHexScan AsanInit. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import AsanNodesArg AsanNodesRP ImgParams.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition SEGS_src13 : list Segment := Plain.M.loaded_segments.
Definition PH_src13 : PhdrInfo := Plain.M.phdrs.
(* [comment removed for export] *)
Definition LIMIT_src13 : Z := source_alloc_limit.

Definition AT_src13 : atable :=
  {| img_lo := 0x10000; img_hi := 0x105000; n_res := 4; shadow_off := 0x0;  (* [comment removed for export] *)
     a_entry := 0x3af4c; rw_lo := 0xca000; rw_len := 0x3b000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 10;
     x_imemset := 0x0; x_imemcpy := 0x0; x_memset := 0xc46a0; x_memcpy := 0xc4120; x_memiszero := 0x0;
     x_istrncpy := 0x0; x_sealed := 0x0; x_popfree := 0x0; x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
     x_envscan := 0xb2aa8; x_envscan_k := 0xb2ab4; x_pnscan := 0xb2b6c; x_pnscan_k := 0xb2b78;
     stops_more := [] |}.
Definition init_src13 : acs := init_acs_of AT_src13.
(* [comment removed for export] *)
Definition ARG_src13 : AN.argtab :=
  {| AN.g_istrlen := 0x0; AN.g_memchr := 0xc4024; AN.g_stdio_write := 0xb8658; AN.g_exit := 0xb33d8;
     AN.g_file_lo := 0xd0fb8; AN.g_file_hi := 0xd1280; AN.g_canary_got := 0xcfeb8; AN.g_canary := 0x103838;
     AN.g_ro_lo := 0x134d8; AN.g_ro_hi := 0x134f8 |}.
(* [comment removed for export] *)
Definition MT_src13 : mtab :=
  {| mt_enframe := 0xb6c40; mt_getmeta := 0xb586c; mt_free := 0xb56a0; mt_free_k := 0xb577c;
     mt_sct := 0x21850; mt_secret := 0x1039d8 |}.
(* [comment removed for export] *)
Definition RPT_src13 : RPN.rptab :=
  RPN.RPT 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0.
(* [comment removed for export] *)
Definition IP_src13 : imgparams := IP SEGS_src13 AT_src13 ARG_src13 LIMIT_src13 MT_src13 RPT_src13.
Lemma src13_arg_ro_hull : img_lo AT_src13 <= AN.g_ro_lo ARG_src13 /\ AN.g_ro_hi ARG_src13 <= img_hi AT_src13.
Proof. cbn. lia. Qed.
Lemma src13_arg_file : img_lo AT_src13 <= AN.g_file_lo ARG_src13 /\ AN.g_file_hi ARG_src13 <= img_hi AT_src13
  /\ img_lo AT_src13 <= AN.g_canary_got ARG_src13 /\ AN.g_canary_got ARG_src13 + 8 <= img_hi AT_src13
  /\ img_lo AT_src13 <= AN.g_canary ARG_src13 /\ AN.g_canary ARG_src13 + 8 <= img_hi AT_src13.
Proof. cbn. lia. Qed.
(* [comment removed for export] *)
Definition TEXT_LO_src13 : Z := 0x3a000.
Definition TEXT_N_src13 : nat := 147456.
Definition IT_src13 (rs : list (Z * nat)) : itab := mk_itab_ranges SEGS_src13 rs.
Lemma IT_src13_ok : forall rs, itab_sound SEGS_src13 (IT_src13 rs).
Proof. intros rs. apply APS.mk_itab_ranges_sound. Qed.

(* [comment removed for export] *)
Lemma src13_wx : wx_segs_nowrap SEGS_src13.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

Definition segs_in_hull_b (segs : list Segment) (lo hi : Z) : bool :=
  forallb (fun seg => (lo <=? Z.of_N (seg_base seg)) && (Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <=? hi))%bool segs.

Lemma find_segment1_none_outside_src13 : forall segs lo hi x,
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

Lemma src13_segs_in_hull : segs_in_hull_b SEGS_src13 (img_lo AT_src13) (img_hi AT_src13) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma src13_in_hull : forall a : word,
  APS.in_hull AT_src13 (bv_unsigned a) = false -> find_segment SEGS_src13 (bv_unsigned a) 1 = None.
Proof.
  intros a H. apply (find_segment1_none_outside_src13 SEGS_src13 (img_lo AT_src13) (img_hi AT_src13)); [exact src13_segs_in_hull|].
  unfold APS.in_hull in H. apply andb_false_iff in H as [H|H]; [apply Z.leb_gt in H; left | apply Z.ltb_ge in H; right]; lia.
Qed.

Lemma src13_res_len : APS.res_len_ok SEGS_src13 AT_src13.
Proof. vm_compute. reflexivity. Qed.

Lemma src13_res_eq : segments_reserved SEGS_src13 = [(Z_to_bv 64 0x10000, Z_to_bv 64 0x2a000); (Z_to_bv 64 0x3a000, Z_to_bv 64 0x90000); (Z_to_bv 64 0xca000, Z_to_bv 64 0x6000); (Z_to_bv 64 0xd0000, Z_to_bv 64 0x35000)].
Proof. vm_compute. reflexivity. Qed.

Lemma src13_res_hull : Forall (fun iv => img_lo AT_src13 <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi AT_src13)
                             (segments_reserved SEGS_src13).
Proof.
  rewrite src13_res_eq. cbn [img_lo img_hi AT_src13].
  repeat constructor; cbn [fst snd]; rewrite ?u64_lit by lia; lia.
Qed.

Lemma src13_hull_ok : APS.hull_ok AT_src13.
Proof. unfold APS.hull_ok. cbn [img_lo img_hi AT_src13]. unfold KHI. repeat split; reflexivity || lia. Qed.

Lemma src13_shadow_ok : APS.shadow_ok AT_src13.
Proof. unfold APS.shadow_ok. cbn [shadow_off AT_src13]. lia. Qed.

Lemma src13_plain : plain AT_src13 = true.
Proof. reflexivity. Qed.

Lemma src13_res_sizes : APS.sum_sizes (segments_reserved SEGS_src13) = 0xf5000.
Proof. vm_compute. reflexivity. Qed.

Lemma src13_segs_eq : SEGS_src13 = [Plain_segment_000; Plain_segment_001; Plain_segment_002; Plain_segment_003].
Proof. reflexivity. Qed.

Lemma src13_hex2 : scanN Plain_seg_bytes_002 64 0 24576 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma src13_len2 : Z.to_N (Uint63.to_Z (PrimString.length Plain_seg_bytes_002) / 2) = 24576%N.
Proof. vm_compute. reflexivity. Qed.

Lemma src13_hex3 : scanN Plain_seg_bytes_003 64 0 217088 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma src13_len3 : Z.to_N (Uint63.to_Z (PrimString.length Plain_seg_bytes_003) / 2) = 217088%N.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma src13_rw_window : forall m (x : word),
  0xca000 <= bv_unsigned x < 0x105000 -> wview SEGS_src13 m x <> None.
Proof.
  intros m x Hx. unfold wview. destruct (m x); [discriminate|].
  destruct (find_segment SEGS_src13 (bv_unsigned x) 1) as [seg|] eqn:Hf.
  - apply find_segment_some_spec in Hf as (Hin & Hb & Ht).
    rewrite src13_segs_eq in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
      cbn [seg_base seg_size seg_writable seg_perms seg_bytes string_has Ascii.eqb Plain_segment_000 Plain_segment_001 Plain_segment_002 Plain_segment_003] in Hb, Ht |- *.
    + exfalso. lia.
    + exfalso. lia.
    + cbn -[segment_byte_at]. apply (segment_byte_at_some1 _ 24576); [exact src13_hex2 | rewrite src13_len2; lia | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
    + cbn -[segment_byte_at]. apply (segment_byte_at_some1 _ 217088); [exact src13_hex3 | rewrite src13_len3; lia | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
  - exfalso.
    destruct (Z.lt_ge_cases (bv_unsigned x) 0xd0000) as [Hl0|Hl0].
    { apply (find_segment_none_spec _ _ _ Hf Plain_segment_002); [rewrite src13_segs_eq; cbn; tauto | cbn; lia]. }
    apply (find_segment_none_spec _ _ _ Hf Plain_segment_003); [rewrite src13_segs_eq; cbn; tauto | cbn; lia].
Qed.

(* [comment removed for export] *)
Lemma src13_img_facts : img_facts SEGS_src13 AT_src13 PH_src13.
Proof.
  constructor.
  - repeat split; reflexivity.
  - cbn [img_lo img_hi AT_src13]. lia.
  - vm_compute. reflexivity.
  - exact src13_res_hull.
  - rewrite src13_res_sizes. reflexivity.
  - cbn [rw_lo rw_len AT_src13]. split; [lia|]. intros m x Hx. apply src13_rw_window. lia.
  - exact src13_shadow_ok.
Qed.
