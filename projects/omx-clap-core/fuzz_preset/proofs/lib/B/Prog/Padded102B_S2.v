(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AE2y.v, with its module paths and module names changed; 366 of its 406 lines of code are new or changed and 664 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/Padded102B.v, with its module paths and module names changed; 52 of its 96 lines of code are new or changed and 362 lines of the source are left out. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YGcallx YGcallcf YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG01cf YG00cf YG0ncf YG0dcf YG0sshcf YGcfRoomPre YG0lawscf YGcfApath.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnAlloc PRH_FnReader
  PRH_FnCheck CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Padded102B.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

Section s2. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
Context {PA : PAImg B_prog_listing}.
#[local] Existing Instance prh_img_B.
#[local] Notation CP := CfParams_preset.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation PST := (@prh_pst prh_img_B).
Variable B : asyms.
#[local] Notation ARc := (fun ly S Hp W mem md => ARcf (cp := CP) SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).

Lemma pd_test_fetch : fetch_word SEGS (Z_to_bv 64 (pd_pc PD_TEST)) = Some (Z_to_bv 32 0x2050a63).
Proof.
apply pa_fetch_ok.
pose proof (pi_check_lookup asym (clookup (@pa_tbl _ B_prog_listing PA)) VAL SIGMA B_prog_listing (PD_OFF + PD_TEST)
  (PW 0x2050a63) (@pa_cert _ B_prog_listing PA) ltac:(vm_compute; reflexivity)) as Hck.
unfold pi_slot_check in Hck. unfold pd_pc. rewrite <- Z.add_assoc.
destruct (clookup (@pa_tbl _ B_prog_listing PA) (BASE + (PD_OFF + PD_TEST))) as [wz|] eqn:Hl; [|discriminate Hck].
apply Z.eqb_eq in Hck. subst wz. reflexivity.
Qed.

Lemma pd_s2 : pd_s3_stmt (SK := SK) (PA := PA) B -> pd_s5_stmt (SK := SK) (PA := PA) B ->
  pd_s2_stmt (SK := SK) (PA := PA) B.
Proof.
intros HS3 HS5 HI D ly S Hp W regs mem md k b HT.
pose proof (@pa_wx _ _ PA) as Hwx. pose proof (@pa_segs_low _ _ PA) as Hsegs. pose proof (@pa_B_ok _ _ PA) as HBo.
assert (LAWS : AR_laws_x SEGS B ARc (@cf_head CP))
  by exact (AR_laws_x_xs (cp := CP) SEGS B (AR_laws_ok_cf (cp := CP) SEGS B)).
assert (Hdec : decode_any (Z_to_bv 32 0x2050a63) = Some (Branch BC_EQ 10%bv 0%bv (Z_to_bv 13 52), 4%Z))
  by vm_refl_bv.
assert (Hec : is_ecall (Z_to_bv 32 0x2050a63) = false) by (vm_compute; reflexivity).
assert (EO : PD_OFF = 6620) by reflexivity.
assert (Hpc : 0 <= pd_pc PD_TEST /\ pd_pc PD_TEST + 52 < 2 ^ 64) by (unfold pd_pc, PD_TEST; rewrite EO; lia).
destruct HT as (HB & H10 & HARM).
assert (HBm : forall md', same_but_materialized md md' -> pd_base B D ly S Hp W regs mem md' k b (din_own D)).
{ intros md' Hs. rewrite (same_but_materialized_wvb md md' Hs).
  destruct HB as (H1 & HJ & H3). split; [exact H1|]. split; [|exact H3].
  unfold pd_J in HJ |- *. apply (ajournal_x_materialize (SK := SK) SEGS B PST ARc LAWS Hsegs). exact HJ. }
destruct HARM as [(Eb & HN) | (HOK & HnIn & HAP)].
- subst b.
  eapply (SRr_step SEGS Hwx W); [reflexivity | |].
  + rewrite restrict_mkst_fx. apply (step_beq_tk SEGS _ _ _ _ _ _ _ _ pd_test_fetch Hec Hdec).
    replace (getr regs 10%bv) with (Z_to_bv 64 0) by (symmetry; exact H10).
    change (getr regs 0%bv) with (Z_to_bv 64 0). reflexivity.
  + intros md' Hs. cbn [ms_mem mkst]. rewrite unrestrict_mkst_mrestrict.
    assert (Etk : btgt (Z_to_bv 64 (pd_pc PD_TEST)) (bv_signed (Z_to_bv 13 52)) = Z_to_bv 64 (pd_pc PD_NULL)).
    { unfold btgt, v_addi. rewrite unsigned_lit_small by lia. change (bv_signed (Z_to_bv 13 52)) with 52.
      f_equal. unfold pd_pc, PD_TEST, PD_NULL. lia. }
    rewrite Etk.
    apply (HS5 HI D ly S Hp W regs mem md' k).
    split; [exact (HBm md' Hs)|]. exact HN.
- pose proof HOK as (Hb0 & _ & Hb4 & Hbc & _).
  pose proof (@alloc_ceiling_lt rc) as Hac.
  assert (Hsz : 0 <= pd_size D) by (unfold pd_size; lia).
  eapply (SRr_step SEGS Hwx W); [reflexivity | |].
  + rewrite restrict_mkst_fx. apply (step_beq_ft SEGS _ _ _ _ _ _ _ _ pd_test_fetch Hec Hdec).
    replace (getr regs 10%bv) with (Z_to_bv 64 b) by (symmetry; exact H10).
    change (getr regs 0%bv) with (Z_to_bv 64 0).
    unfold c_eq, bv_eqb. rewrite !unsigned_lit_small by lia. apply Z.eqb_neq. exact Hb0.
  + intros md' Hs. cbn [ms_mem mkst]. rewrite unrestrict_mkst_mrestrict.
    assert (Eft : v_addi (Z_to_bv 64 (pd_pc PD_TEST)) 4 = Z_to_bv 64 (pd_pc PD_OK)).
    { unfold v_addi. rewrite unsigned_lit_small by lia. f_equal. unfold pd_pc, PD_TEST, PD_OK. lia. }
    rewrite Eft.
    apply (HS3 HI D ly S Hp W regs mem md' k b).
    split; [exact (HBm md' Hs)|]. split; [exact HOK|]. split; [exact HnIn | exact HAP].
Qed.
End s2.
