(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.skcms.iccprofile_info.images Require Import Asan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import PropExec StoreOk AgentLib AsanAcct AsanAcctImages AxSymExec3 AsanPlan AsanPlanSound AsanHexScan AsanHexZero.
Unset Lia Cache. Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AP.
Open Scope Z_scope.

Definition ASEGS := Asan.M.loaded_segments.

(* [comment removed for export] *)
Definition INFO_ASAN : atable :=
  {| img_lo := 0x10000; img_hi := 0x5fc000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x3030c; rw_lo := 0x9e000; rw_len := 0x55e000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x633c0; x_imemcpy := 0x63344; x_memset := 0x98220; x_memcpy := 0x97e1c; x_memiszero := 0x638f0;
     x_istrncpy := 0x637ec; x_sealed := 0x117fe; x_popfree := 0x366f8;
     x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
     x_envscan := 0x8dc24; x_envscan_k := 0x8dc30; x_pnscan := 0x8dce8; x_pnscan_k := 0x8dcf4;
     stops_more := [0x3436c; 0x35990; 0x536cc; 0x59a84; 0x59a98; 0x59aac; 0x5f43c; 0x5f50c; 0x6ca38; 0x6d944; 0x6dad4; 0x7782c; 0x6dc44] |}.

Definition INFO_TEXT_LO : Z := 0x3030c.
Definition INFO_TEXT_N : nat := 111762.
Definition AITAB : itab := mk_itab ASEGS INFO_TEXT_LO INFO_TEXT_N.

Lemma asan_IT_ok : itab_sound ASEGS AITAB.
Proof. apply mk_itab_sound. Qed.

Lemma asan_wx : wx_segs_nowrap ASEGS.
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

Lemma asan_segs_in_hull : segs_in_hull_b ASEGS (img_lo INFO_ASAN) (img_hi INFO_ASAN) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma asan_in_hull : forall a : word,
  APS.in_hull INFO_ASAN (bv_unsigned a) = false -> find_segment ASEGS (bv_unsigned a) 1 = None.
Proof.
  intros a H. apply (find_segment1_none_outside ASEGS (img_lo INFO_ASAN) (img_hi INFO_ASAN)); [exact asan_segs_in_hull|].
  unfold APS.in_hull in H. apply andb_false_iff in H as [H|H]; [apply Z.leb_gt in H; left | apply Z.ltb_ge in H; right]; lia.
Qed.

Lemma asan_res_len : APS.res_len_ok ASEGS INFO_ASAN.
Proof. vm_compute. reflexivity. Qed.

Lemma asan_res_hull : Forall (fun iv => img_lo INFO_ASAN <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi INFO_ASAN) (segments_reserved ASEGS).
Proof.
  assert (E : segments_reserved ASEGS = [(Z_to_bv 64 0x10000, Z_to_bv 64 0x20000); (Z_to_bv 64 0x30000, Z_to_bv 64 0x6e000);
                                         (Z_to_bv 64 0x9e000, Z_to_bv 64 0x2000); (Z_to_bv 64 0xa0000, Z_to_bv 64 0x55c000)])
    by (vm_compute; reflexivity).
  rewrite E. cbn [img_lo img_hi INFO_ASAN].
  repeat constructor; cbn [fst snd]; rewrite ?u64_lit by lia; lia.
Qed.

Lemma asan_hull_ok : APS.hull_ok INFO_ASAN.
Proof. unfold APS.hull_ok. cbn [img_lo img_hi INFO_ASAN]. unfold KHI. repeat split; reflexivity || lia. Qed.

Lemma asan_shadow_ok : APS.shadow_ok INFO_ASAN.
Proof. unfold APS.shadow_ok. cbn [shadow_off INFO_ASAN]. lia. Qed.

Lemma asan_res_sizes : APS.sum_sizes (segments_reserved ASEGS) = 0x5ec000.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma asan_hex2 : scanN Asan_seg_bytes_002 64 0 8192 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma asan_hex3 : scanN Asan_seg_bytes_003 64 0 5619712 = true.
Proof. (* [comment removed for export] *)
  apply (scanN_prefix_zwin Asan_seg_bytes_003 16384 5619712 (Uint63.of_Z 32768) (Uint63.of_Z 11206656)).
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - reflexivity.
  - reflexivity.
  - vm_compute. discriminate.
  - vm_compute. discriminate.
Qed.
Lemma asan_len2 : Z.to_N (Uint63.to_Z (PrimString.length Asan_seg_bytes_002) / 2) = 8192%N.
Proof. vm_compute. reflexivity. Qed.
Lemma asan_len3 : Z.to_N (Uint63.to_Z (PrimString.length Asan_seg_bytes_003) / 2) = 5619712%N.
Proof. vm_compute. reflexivity. Qed.

Lemma asan_segs_eq : ASEGS = [Asan_segment_000; Asan_segment_001;
                              Asan_segment_002; Asan_segment_003].
Proof. reflexivity. Qed.

Lemma asan_rw_window : forall m (x : word),
  0x9e000 <= bv_unsigned x < 0x5fc000 -> wview ASEGS m x <> None.
Proof.
  intros m x Hx. unfold wview. destruct (m x); [discriminate|].
  destruct (find_segment ASEGS (bv_unsigned x) 1) as [seg|] eqn:Hf.
  - apply find_segment_some_spec in Hf as (Hin & Hb & Ht).
    rewrite asan_segs_eq in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
      cbn [seg_base seg_size seg_writable seg_perms seg_bytes string_has Ascii.eqb
           Asan_segment_000 Asan_segment_001
           Asan_segment_002 Asan_segment_003] in Hb, Ht |- *.
    + exfalso. lia.
    + exfalso. lia.
    + cbn -[segment_byte_at]. apply (segment_byte_at_some1 _ 8192); [exact asan_hex2 | rewrite asan_len2; lia | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
    + cbn -[segment_byte_at]. apply (segment_byte_at_some1 _ 5619712); [exact asan_hex3 | rewrite asan_len3; lia | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
  - exfalso. destruct (Z.lt_ge_cases (bv_unsigned x) 0xa0000) as [Hl|Hl].
    + apply (find_segment_none_spec _ _ _ Hf Asan_segment_002);
        [rewrite asan_segs_eq; cbn; tauto | cbn; lia].
    + apply (find_segment_none_spec _ _ _ Hf Asan_segment_003);
        [rewrite asan_segs_eq; cbn; tauto | cbn; lia].
Qed.

(* [comment removed for export] *)
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AsanInit.
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.

Definition APH : PhdrInfo := Asan.M.phdrs.

Lemma asan_img_facts : img_facts ASEGS INFO_ASAN APH.
Proof.
  constructor.
  - repeat split; reflexivity.
  - cbn [img_lo img_hi INFO_ASAN]. lia.
  - vm_compute. reflexivity.
  - exact asan_res_hull.
  - rewrite asan_res_sizes. reflexivity.
  - cbn [rw_lo rw_len INFO_ASAN]. split; [lia|]. intros m x Hx. apply asan_rw_window. lia.
  - exact asan_shadow_ok.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma asan_res_cover : APS.res_cover_ok ASEGS INFO_ASAN.
Proof.
  split; [reflexivity|]. intros z Hz.
  apply (APS.cover_run_sound _ 4 (img_lo INFO_ASAN) (img_hi INFO_ASAN)); [vm_compute; reflexivity | exact Hz].
Qed.
