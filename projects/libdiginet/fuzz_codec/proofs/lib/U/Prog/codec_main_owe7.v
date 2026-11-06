(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColA/W_set0A.v, with its module paths and module names changed; 193 of its 215 lines of code are new or changed and 122 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_agree.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells codec_img
  codec_main_inv codec_main_lib codec_main_owe0.
Import ListNotations.
Open Scope Z_scope.

(** Segment OWE7 of the walk of LLVMFuzzerTestOneInput in the UBSan image: owe()'s cases STRIP_LEDS
    (0x14718-0x14734, addr = k.a) and COUNTER_LEDS (0x14a0c-0x14a1c, addr = d->counter), each through
    the tail they share (0x14a20-0x14a28, 0x14a68-0x14ab0: the range test of b and the inlined
    owe_sysex) and FADER's 0x14ab4-0x14abc to the checks at 0x14a34, or through SPEC_E_RANGE at
    0x14a2c-0x14a30. The null and alignment traps on the desk (0x14724, 0x14a18, 0x14a74) are dead:
    both kinds need a desk, so owe()'s prologue left a0 = 1 and a non-NULL k.desk, which is SPEC_C24
    or SPEC_PC, both 16-aligned. *)

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
  end.

(** ---- the desk bytes the LEDS forms read ---- *)

(** d->device (lbu 8(s7)). *)
Lemma desk_dev_o7 : forall m k d, relro_img m ->
  ((k_desk k = SDESK_C24 /\ d = c24) \/ (k_desk k = SDESK_PC /\ d = pc)) ->
  ov_read_bytes rsegs m (Z_to_bv 64 (k_desk k + 8)) 1 = Some [Z_to_bv 8 (d_dev d)].
Proof.
  intros m k d HR [[E ->] | [E ->]]; rewrite E; unfold SDESK_C24, SDESK_PC.
  - pose proof (codec_SPEC_C24_at m HR) as DK. unfold codec_SPEC_C24_cells in DK.
    exact (ro_cells_read_at rsegs m 0x1f690 _ 8 (C1 (Z_to_bv 8 0x01)) 1 _ DK eq_refl eq_refl eq_refl).
  - pose proof (codec_SPEC_PC_at m HR) as DK. unfold codec_SPEC_PC_cells in DK.
    exact (ro_cells_read_at rsegs m 0x1f6a0 _ 8 (C1 (Z_to_bv 8 0x00)) 1 _ DK eq_refl eq_refl eq_refl).
Qed.

(** d->counter (lbu 0xb(s7)). *)
Lemma desk_counter_o7 : forall m k d, relro_img m ->
  ((k_desk k = SDESK_C24 /\ d = c24) \/ (k_desk k = SDESK_PC /\ d = pc)) ->
  ov_read_bytes rsegs m (Z_to_bv 64 (k_desk k + 11)) 1 = Some [Z_to_bv 8 (d_counter d)].
Proof.
  intros m k d HR [[E ->] | [E ->]]; rewrite E; unfold SDESK_C24, SDESK_PC.
  - pose proof (codec_SPEC_C24_at m HR) as DK. unfold codec_SPEC_C24_cells in DK.
    exact (ro_cells_read_at rsegs m 0x1f690 _ 11 (C1 (Z_to_bv 8 0x19)) 1 _ DK eq_refl eq_refl eq_refl).
  - pose proof (codec_SPEC_PC_at m HR) as DK. unfold codec_SPEC_PC_cells in DK.
    exact (ro_cells_read_at rsegs m 0x1f6a0 _ 11 (C1 (Z_to_bv 8 0x09)) 1 _ DK eq_refl eq_refl eq_refl).
Qed.

Lemma desk_fields_o7 : forall k d,
  ((k_desk k = SDESK_C24 /\ d = c24) \/ (k_desk k = SDESK_PC /\ d = pc)) ->
  0 <= d_dev d <= 1 /\ 9 <= d_counter d <= 25.
Proof. intros k d [[_ ->] | [_ ->]]; cbn; lia. Qed.

(** ---- owe() of kinds 7 and 8 (fuzz_codec.c:202-208, owe_sysex :101-111 with fn 0x20) ---- *)

Lemma owe_k7_ok : forall k d, k_kind k = 7 -> od_of k = Some d -> k_a k < d_strips d -> k_b k <= 0x7f ->
  owe_k k = (0, ([0xf0; 0x13; u8 (d_dev d); 0x20; u8 (k_a k); u8 (k_b k); 0xf7], KEY 5 (k_a k), 0)).
Proof.
  intros k d HK HO Ha Hb. unfold owe_k. rewrite HK, HO. unfold owe_spec. cbv beta iota zeta.
  destruct (Z.leb_spec (d_strips d) (k_a k)); [lia|]. destruct (Z.ltb_spec 0x7f (k_b k)); [lia|].
  reflexivity.
Qed.

Lemma owe_k7_rng : forall k d, k_kind k = 7 -> od_of k = Some d -> d_strips d <= k_a k \/ 0x7f < k_b k ->
  fst (owe_k k) = E_RANGE.
Proof.
  intros k d HK HO H. unfold owe_k. rewrite HK, HO. unfold owe_spec. cbv beta iota zeta.
  destruct (Z.leb_spec (d_strips d) (k_a k)); destruct (Z.ltb_spec 0x7f (k_b k)); try reflexivity; lia.
Qed.

Lemma owe_k8_ok : forall k d, k_kind k = 8 -> od_of k = Some d -> k_b k <= 0x7f ->
  owe_k k = (0, ([0xf0; 0x13; u8 (d_dev d); 0x20; u8 (d_counter d); u8 (k_b k); 0xf7],
                 KEY 5 (d_counter d), 0)).
Proof.
  intros k d HK HO Hb. unfold owe_k. rewrite HK, HO. unfold owe_spec. cbv beta iota zeta.
  destruct (Z.ltb_spec 0x7f (k_b k)); [lia|]. reflexivity.
Qed.

Lemma owe_k8_rng : forall k d, k_kind k = 8 -> od_of k = Some d -> 0x7f < k_b k ->
  fst (owe_k k) = E_RANGE.
Proof.
  intros k d HK HO H. unfold owe_k. rewrite HK, HO. unfold owe_spec. cbv beta iota zeta.
  destruct (Z.ltb_spec 0x7f (k_b k)); [reflexivity | lia].
Qed.

(** addr | 0x50000 (0x14a88-0x14a8c). *)
Lemma key_leds_o7 : forall a, 0 <= a < 65536 -> Z.lor a 327680 = KEY 5 a.
Proof.
  intros a Ha. unfold KEY. change 0xffff with (Z.ones 16). rewrite Z.land_ones by lia.
  rewrite (Z.mod_small a) by lia. rewrite Z.lor_comm. reflexivity.
Qed.

(** ---- the two cases ---- *)

(** STRIP_LEDS, 0x14718-0x14734, then 0x14a20-0x14a28, 0x14a68-0x14abc. *)
Lemma owe_strip_leds_o7 : forall E n, env_ok E -> chk_ok E n ->
  forall k, rec_wf k -> k_kind k = 7 -> owe_ok E n k.
Proof.
  intros [ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p F fc m lo data] n ENV CHK k WF EK.
  unfold owe_ok.
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' s5' t3' t4' t5' t6' cur rem u0 pj tj plj c ops m1
         _ HND HOPS HOPS2 HCUR HC0 HCN FR ST MU WM HMI.
  pose proof (relro_at _ _ ENV MU) as RR.
  unfold chk_ok, fr in CHK. unfold env_ok in ENV. unfold fr in FR. cenv_cbn.
  destruct ENV as (_ & _ & ST0 & LO & _ & _ & _ & _ & _ & _).
  pose proof ST0 as (Hlo0 & _ & _). clear ST0.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof WF as (HK & HDK & HBF & HOUT & HRC & HWRC & HWL & HWK & HWD & HRD).
  pose proof HRD as (Ha & Hb & Hc & Hdl & _ & _ & _ & _).
  destruct (HND ltac:(rewrite EK; reflexivity)) as [-> HDNZ]. clear HND.
  destruct (desk_of_o0 k HDK HDNZ) as (d & OD & HSTR & DKS).
  pose proof (desk_fields_o7 k d DKS) as (HDV & HCT).
  pose proof (desk_strips_o0 m1 k d RR DKS) as RD9.
  pose proof (desk_dev_o7 m1 k d RR DKS) as RD8.
  assert (BS : bv_unsigned (Z_to_bv 8 (d_strips d)) = d_strips d) by (apply b8_small_o0; lia).
  assert (BD : bv_unsigned (Z_to_bv 8 (d_dev d)) = d_dev d) by (apply b8_small_o0; lia).
  pose proof (desk_range_o0 k HDK) as [Rp Rd].
  assert (UD : bv_unsigned (Z_to_bv 64 (k_desk k)) = k_desk k) by (apply unsigned_lit; lia).
  pose proof (sx32_u32_o0 (k_a k) Ha) as SXA. pose proof (sx32_u32_o0 (k_b k) Hb) as SXB.
  destruct FR as (HS & F0 & F8 & FK & FIN & FPD & FTX & FPL & FSV).
  rewrite (kc_run_cells_o0 k HWRC HWL HWK HWD) in FK.
  rewrite EK. replace (pc_owe 7) with 0x14718 by reflexivity.
  (* 0x14718-0x14724: the null and alignment trap on d is dead *)
  zstep. zstep. zstep. zstep.
  if_cases T;
    [ exfalso; clear -T DKS; destruct DKS as [[ED _]|[ED _]]; rewrite ED in T;
      unfold SDESK_C24, SDESK_PC in T; revert T; vm_compute; intros T; discriminate T
    | clear T ].
  (* 0x14728-0x14730: a < d->strips goes on to the shared tail *)
  zstep. zstep. rewrite ?BS. zstep.
  if_cases E1.
  - zify_cond E1. rewrite ?BS in E1.
    assert (Ha' : k_a k < d_strips d) by lia.
    rewrite (sx32_small (k_a k)) by lia.
    (* 0x14a20-0x14a28: b <= 0x7f goes on to 0x14a68 *)
    zstep. zstep. zstep.
    if_cases E2.
    + zify_cond E2.
      assert (Hb' : k_b k <= 0x7f) by lia.
      rewrite (sx32_small (k_b k)) by lia.
      (* 0x14a68-0x14a74: the second trap on d is dead *)
      zstep. zstep. zstep. zstep.
      if_cases T;
        [ exfalso; clear -T DKS; destruct DKS as [[ED _]|[ED _]]; rewrite ED in T;
          unfold SDESK_C24, SDESK_PC in T; revert T; vm_compute; intros T; discriminate T
        | clear T ].
      (* 0x14a78-0x14abc: the inlined owe_sysex, want_len = 7, want_key *)
      zstep. rewrite ?BD. do 17 zstep.
      owed_rec_o0 k FK HWRC.
      go_chk_o0 CHK FRK F0 F8 FIN FPD FTX FPL FSV.
      apply (chk_wf_succ_o0 k [0xf0; 0x13; u8 (d_dev d); 0x20; u8 (k_a k); u8 (k_b k); 0xf7]
                            (KEY 5 (k_a k))).
      * exact WF.
      * apply (owe_k7_ok k d EK OD); lia.
      * cbn [cells_bytes cbytes app firstn length bz map le2 Z_to_le_bytes].
        repeat (apply f_equal2; [ first [ reflexivity | byte_tac2_o0 ] | ]). reflexivity.
      * reflexivity.
      * cbn [length]. lia.
      * first [ apply key_leds_o7; lia | rewrite Z.mod_small by lia; apply key_leds_o7; lia ].
      * apply KEY_range. lia.
    + zify_cond E2.
      zstep. zstep.
      pose proof (kc_rng_o0 _ _ k _ HWL HWK HWD FK ltac:(apply bv_eq; reflexivity)) as FRK.
      go_chk_o0 CHK FRK F0 F8 FIN FPD FTX FPL FSV.
      apply chk_wf_rng_o0; [exact WF|]. apply (owe_k7_rng k d EK OD). lia.
  - zify_cond E1. rewrite ?BS in E1.
    zstep. zstep. zstep.
    pose proof (kc_rng_o0 _ _ k _ HWL HWK HWD FK ltac:(apply bv_eq; reflexivity)) as FRK.
    go_chk_o0 CHK FRK F0 F8 FIN FPD FTX FPL FSV.
    apply chk_wf_rng_o0; [exact WF|]. apply (owe_k7_rng k d EK OD). lia.
Qed.

(** COUNTER_LEDS, 0x14a0c-0x14a1c, then 0x14a20-0x14a28, 0x14a68-0x14abc. *)
Lemma owe_counter_leds_o7 : forall E n, env_ok E -> chk_ok E n ->
  forall k, rec_wf k -> k_kind k = 8 -> owe_ok E n k.
Proof.
  intros [ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p F fc m lo data] n ENV CHK k WF EK.
  unfold owe_ok.
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' s5' t3' t4' t5' t6' cur rem u0 pj tj plj c ops m1
         _ HND HOPS HOPS2 HCUR HC0 HCN FR ST MU WM HMI.
  pose proof (relro_at _ _ ENV MU) as RR.
  unfold chk_ok, fr in CHK. unfold env_ok in ENV. unfold fr in FR. cenv_cbn.
  destruct ENV as (_ & _ & ST0 & LO & _ & _ & _ & _ & _ & _).
  pose proof ST0 as (Hlo0 & _ & _). clear ST0.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof WF as (HK & HDK & HBF & HOUT & HRC & HWRC & HWL & HWK & HWD & HRD).
  pose proof HRD as (Ha & Hb & Hc & Hdl & _ & _ & _ & _).
  destruct (HND ltac:(rewrite EK; reflexivity)) as [-> HDNZ]. clear HND.
  destruct (desk_of_o0 k HDK HDNZ) as (d & OD & HSTR & DKS).
  pose proof (desk_fields_o7 k d DKS) as (HDV & HCT).
  pose proof (desk_counter_o7 m1 k d RR DKS) as RD11.
  pose proof (desk_dev_o7 m1 k d RR DKS) as RD8.
  assert (BC : bv_unsigned (Z_to_bv 8 (d_counter d)) = d_counter d) by (apply b8_small_o0; lia).
  assert (BD : bv_unsigned (Z_to_bv 8 (d_dev d)) = d_dev d) by (apply b8_small_o0; lia).
  pose proof (desk_range_o0 k HDK) as [Rp Rd].
  assert (UD : bv_unsigned (Z_to_bv 64 (k_desk k)) = k_desk k) by (apply unsigned_lit; lia).
  pose proof (sx32_u32_o0 (k_b k) Hb) as SXB.
  destruct FR as (HS & F0 & F8 & FK & FIN & FPD & FTX & FPL & FSV).
  rewrite (kc_run_cells_o0 k HWRC HWL HWK HWD) in FK.
  rewrite EK. replace (pc_owe 8) with 0x14a0c by reflexivity.
  (* 0x14a0c-0x14a18: the null and alignment trap on d is dead *)
  zstep. zstep. zstep. zstep.
  if_cases T;
    [ exfalso; clear -T DKS; destruct DKS as [[ED _]|[ED _]]; rewrite ED in T;
      unfold SDESK_C24, SDESK_PC in T; revert T; vm_compute; intros T; discriminate T
    | clear T ].
  (* 0x14a1c: addr = d->counter *)
  zstep. rewrite ?BC.
  (* 0x14a20-0x14a28: b <= 0x7f goes on to 0x14a68 *)
  zstep. zstep. zstep.
  if_cases E2.
  - zify_cond E2.
    assert (Hb' : k_b k <= 0x7f) by lia.
    rewrite (sx32_small (k_b k)) by lia.
    (* 0x14a68-0x14a74: the second trap on d is dead *)
    zstep. zstep. zstep. zstep.
    if_cases T;
      [ exfalso; clear -T DKS; destruct DKS as [[ED _]|[ED _]]; rewrite ED in T;
        unfold SDESK_C24, SDESK_PC in T; revert T; vm_compute; intros T; discriminate T
      | clear T ].
    (* 0x14a78-0x14abc: the inlined owe_sysex, want_len = 7, want_key *)
    zstep. rewrite ?BD. do 17 zstep.
    owed_rec_o0 k FK HWRC.
    go_chk_o0 CHK FRK F0 F8 FIN FPD FTX FPL FSV.
    apply (chk_wf_succ_o0 k [0xf0; 0x13; u8 (d_dev d); 0x20; u8 (d_counter d); u8 (k_b k); 0xf7]
                          (KEY 5 (d_counter d))).
    + exact WF.
    + apply (owe_k8_ok k d EK OD); lia.
    + cbn [cells_bytes cbytes app firstn length bz map le2 Z_to_le_bytes].
      repeat (apply f_equal2; [ first [ reflexivity | byte_tac2_o0 ] | ]). reflexivity.
    + reflexivity.
    + cbn [length]. lia.
    + rewrite ?BC. first [ apply key_leds_o7; lia | rewrite Z.mod_small by lia; apply key_leds_o7; lia ].
    + apply KEY_range. lia.
  - zify_cond E2.
    zstep. zstep.
    pose proof (kc_rng_o0 _ _ k _ HWL HWK HWD FK ltac:(apply bv_eq; reflexivity)) as FRK.
    go_chk_o0 CHK FRK F0 F8 FIN FPD FTX FPL FSV.
    apply chk_wf_rng_o0; [exact WF|]. apply (owe_k8_rng k d EK OD). lia.
Qed.

(** ---- the segment ---- *)

Lemma codec_main_owe7 : seg_owe7_stmt.
Proof.
  unfold seg_owe7_stmt. intros E n ENV CHK k WF [EK|EK].
  - exact (owe_strip_leds_o7 E n ENV CHK k WF EK).
  - exact (owe_counter_leds_o7 E n ENV CHK k WF EK).
Qed.
