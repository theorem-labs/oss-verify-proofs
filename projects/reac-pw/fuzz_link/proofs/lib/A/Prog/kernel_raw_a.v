(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 609 of its 643 lines of code are new or changed and 1890 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/kernel_exit.v, with its module paths and module names changed; 498 of its 540 lines of code are new or changed and 601 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: the walk of kernel (fuzz_link.asan 0x83d30), the raw path's calls
   (kernel_raw_kit.v's cuts). Listing (internal path) (internal record, sha256 7bc02d6772b3):
     kr_a  kin_raw +0x1f30: a1 := 0x202, a0 := slot KS_W1SH; +0x1f38 jal meta_fill_00 (0x55e74)   -> kr_c1 +0x1f3c
     kr_b  kr_c1 +0x1f3c: a0 := slot KS_W1, a1 := 0, a2 := slot KS_NW; +0x1f48 jal checked_memset -> kr_c2 +0x1f4c
     kr_d  kr_c3 +0x2074: jal checked_memcpy(w1, p', t) (0x52d78)                                -> kr_c4 +0x2078
     kr_f  kr_c5 +0x20b8: jal checked_memcpy(g_nl + 4096 j, w1, t)                              -> kr_c6 +0x20bc
     kr_h  kr_c7 +0x20f8: jal meta_fill_f8(shadow(w1), 0x202) (0x55f94)                          -> kr_c8 +0x20fc
     kr_i  kr_c8 +0x20fc: mv s6, s7                                                             -> kin_latch +0x2100
   THE PROOF of each: the state at the cut (no region, or the slots the run reads as one read-only region), the
   engine to the call, the call lemma (kernel_qmsg_kit.v kq_call_mf over AS00 / ASSF8, kq_call_gcpy; kernel_raw_kit.v
   kr_call_ms, kr_call_icpy), then the cut after it (kq_land_mf + kq_kshadow_w1 for the fills; kernel_kit.v
   kat_frame_w1s with kr_kw_cpy or w1's zero bytes for the copies into w1; kq_kat_g + kq_gnl_keep for the copy into
   g_nl; kat_frame_0 for kr_i).
   Section hypotheses: LAWS, LV, TB, KI, AMEMCPY, AMEMSET, AS00, ASSF8.
   Proves no function (kind: segment lemma of kernel's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit LinkWalk.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkNlw LinkWalkPi LinkWalkSide.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkShadow LinkWalkCall.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_c kernel_img.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro kernel_defs kernel_kit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_msg0_kit kernel_next kernel_qmsg_kit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_qmsg_a kernel_raw_kit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import SetShadowDef.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* the slot KS_W1SH (atom 32 = shadow(w1)) at +0x1f30; the slots KS_W1 (atom 32 = w1) and KS_NW at +0x1f3c *)
Definition ra_ss : sstate :=
  mkSS (kpc KP_RAW) sr_atoms
    [YP09.mkRegion (Some 9%nat) KS_W1SH (KS_W1SH + 8) 0 0 [YP09.mkChunk KS_W1SH (CVal 8 (SOff 32 0))]]
    None (mkFacts [] [] []).
Definition rb_ss : sstate :=
  mkSS (kpc 0x1f3c) sr_atoms
    [YP09.mkRegion (Some 9%nat) KS_W1 (KS_NW + 8) 0 0
       [YP09.mkChunk KS_W1 (CVal 8 (SOff 32 0)); YP09.mkChunk KS_NW (CVal 8 (SLit 4112))]]
    None (mkFacts [] [] []).

(* a zero byte as a value of a wider field *)
Lemma kr_le_byte0 : forall (w k : nat), YO0f.le_byte 0 w k = 0.
Proof. intros w k. unfold YO0f.le_byte. rewrite Z.mod_0_l, Z.shiftr_0_l, Z.mod_0_l by lia. reflexivity. Qed.

Lemma kr_val_zero : forall (segs : list Segment) (H : word -> bool) (m : word -> option byte) a (n : nat),
  (forall i, 0 <= i < Z.of_nat n -> aview segs H m (a + i) = Some 0) -> val_mem segs (mrestrict H m) a n 0.
Proof.
  intros segs H m a n Hz k Hk. specialize (Hz (Z.of_nat k) ltac:(lia)).
  destruct (kr_inbyte segs H m (a + Z.of_nat k) 0 Hz) as (Hv & _).
  specialize (Hv 0%nat ltac:(lia)). rewrite Z.add_0_r in Hv. rewrite Hv. rewrite !kr_le_byte0. reflexivity.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation BASE := (pa_val A_TEXT).
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis LV : LinkVals.
Hypothesis TB : AF0m.PcapSyms B.                                (* AF0m.v; discharged at the frame's B by AD2l.PcapB_syms *)
Hypothesis KI : KernImg pa_segs B.                              (* kernel_img_syms at the image *)
Hypothesis AMEMCPY : aintrin_realizes pa_segs B OCpy 0x52d78.   (* checked_memcpy: AE2q.v asan_memcpy_realizes *)
Hypothesis AMEMSET : aintrin_realizes pa_segs B OSet 0x53214.   (* checked_memset: AE2r.v asan_memset_realizes *)
Hypothesis AS00 : aset_shadow_realizes pa_segs B 0x55e74 0x00.  (* meta_fill_00: SetShadow.v link_set_shadow_00 *)
Hypothesis ASSF8 : aset_shadow_realizes pa_segs B 0x55f94 0xf8. (* meta_fill_f8: SetShadow.v link_set_shadow_f8 *)

(* the regs of a cut after a call: callee-saved, unchanged by the run before it *)
Ltac kr_regs_after HP2 KEEP HRL :=
  unfold kregs_eq; cbn [ms_regs mkst kr_rl3 kr_rl4 kr_rl5 kr_rl6 kr_rl7 kr_rl8 kr_rl0 kregs_chunk app];
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
  rewrite (km_pres _ _ _ HP2) by (vm_compute; reflexivity); rewrite KEEP by (vm_compute; reflexivity);
  apply (kn_reg_of _ _ _ _ HRL); kr_in.
Ltac kr_regs0_after HP2 KEEP HR0 :=
  unfold kregs0; cbn [ms_regs mkst]; pose proof HR0 as (?&?&?&?&?&?&?);
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))));
  rewrite (km_pres _ _ _ HP2) by reflexivity; rewrite KEEP by reflexivity; assumption.

(* the state at a cut with one read-only slot region *)
Lemma kr_seat_sl : forall cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 (E : env) (lo hi : Z) chs,
  kat B cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 ->
  regs_ok E sr_atoms (ms_regs ms3) ->
  region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms3)) (YP09.mkRegion (Some 9%nat) lo hi 0 0 chs) ->
  regions_wf [YP09.mkRegion (Some 9%nat) lo hi 0 0 chs] = true ->
  st_ok_pi SEGS pa_val E (mkSS (kpc pc) sr_atoms [YP09.mkRegion (Some 9%nat) lo hi 0 0 chs] None (mkFacts [] [] []))
    (restrict (w_H W3) ms3).
Proof.
  intros cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 E lo hi chs HK Hrg HR Hwf.
  pose proof HK as (HMS & _). destruct HMS as (Hpc & Hrv & Hsvc & Hrom & Hfr & Hfc).
  rewrite (km_ms_shape ms3 (BASE + kpc pc) Hpc Hrv Hsvc Hrom Hfr Hfc), restrict_mkst_fx.
  apply pa_entry_st_ok_full.
  - exact Hrg.
  - exact Hwf.
  - apply Forall_cons; [exact HR | apply Forall_nil].
  - cbn [pairwise_disjoint all_disjoint]. tauto.
  - split; [exact I | split; [exact I | exact I]].
Qed.

(* ---- kr_a: kin_raw +0x1f30 -> meta_fill_00(shadow(w1), 0x202) -> kr_c1 +0x1f3c ---- *)
Theorem kr_a : forall POST Rc, kfrom SK B POST (kr_c1 B Rc) -> kfrom SK B POST (kin_raw B Rc).
Proof.
  intros POST Rc HNEXT cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ Hfrm HI.
  destruct HI as (c & ci & j & adv & HRcv & Hcr & Hci & Hj & HK).
  pose proof HK as (HMS & HR0 & HRL & _ & _ & HSH & HSL & HJB & _).
  pose proof HR0 as (A2 & A9 & A8 & A3 & A4 & A18 & A20).
  pose proof HB as (HPRE & _). pose proof HPRE as (_ & HGok & _).
  pose proof (kn_sp1 SK B cx HB) as (Hs1a & Hs1b & Hs1c & Hs1d & Hs1e & Hs1f & Hs1g & Hs1h).
  destruct (km_FSH_bound B LAWS cx fpos k2 ly3 S3 md3 HJB) as (FS1 & FS2).
  assert (HSLW : rdword (aview SEGS (w_H W3) (ms_mem ms3)) (ksp1 cx + KS_W1SH) = Some (kFSH cx fpos + 4))
    by (apply (kn_slot_of cx W3 ms3 _ KS_W1SH _ HSL); apply in_or_app; left; unfold kslots_setup; kn_in).
  remember (Eimg (Ereg (ms_regs ms3) [w64 (kFSH cx fpos + 4)])) as E eqn:HEdef.
  assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
  assert (E9 : ew E 9%nat = w64 (ksp1 cx)) by (subst E; rewrite <- A9; apply ew_Eimg_Ereg_nat; reflexivity).
  assert (E32 : ew E 32%nat = w64 (kFSH cx fpos + 4)) by (subst E; apply (kq_E_32 SK B LAWS TB KI AMEMCPY LV)).
  assert (HS : st_ok_pi SEGS pa_val E ra_ss (restrict (w_H W3) ms3)).
  { unfold ra_ss. apply (kr_seat_sl cx fpos KP_RAW _ _ _ true adv (Some j) k2 ly3 S3 W3 ms3 md3 E _ _ _ HK).
    - subst E. apply regs_ok_Eimg_Ereg.
    - unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E9. unfold w64. rewrite unsigned_lit_small by lia.
      split; [unfold KS_W1SH; lia|]. split; [unfold KS_W1SH; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val pa_segs E _ (ksp1 cx) KS_W1SH 8%N (SOff 32 0) (kFSH cx fpos + 4)).
      + exact (sv_off0 E 32 _ E32).
      + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). unfold kHighMemBeg, SHADOW_OFF in *. lia.
      + cbn; lia.
      + exact (val_mem_of_rdword pa_segs (w_H W3) (ms_mem ms3) _ _ HSLW).
    - vm_compute. reflexivity. }
  pose proof HS as HS0.
  assert (SHOK : sh_ok SEGS kq_Bx [] E (mrestrict (w_H W3) (ms_mem ms3))) by (apply Forall_nil).
  pose (RUN := paj_run_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  paj_run_tok RUN HS HJ SHOK kq_span.
  { intros a Ha. exfalso. apply (kq_no_wrange _ _ a Ha). vm_compute. reflexivity. }
  lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into ms1 end.
  lazymatch goal with Hx : frame_of _ _ (ms_mem ms3) (ms_mem ms1) |- _ =>
    assert (HM1 : ms_mem ms1 = ms_mem ms3) by (eapply kq_mem_eq; [exact Hx | vm_compute; reflexivity]) end.
  pose proof (km_reg_same E ra_ss _ (w_H W3) ms3 ms1 km_csz HS0 HS ltac:(vm_compute; reflexivity)) as KEEP.
  prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11. prreg HS (1%bv : bv 5) R1.
  pmkst HS.
  rewrite (lv_sigma LV). change (LinkAddr.link_sigma LS___asan_set_shadow_00) with 0x55e74.
  rewrite HM1. rewrite HM1 in HJ.
  eapply (kq_call_mf SK B LAWS TB KI AMEMCPY LV 0x55e74 0 AS00 cx fpos k2 ly3 S3 W3 (ms_mem ms3) _
            (ms_regs ms1) _ 4 (POST cx) HB HJ);
    [ lia | lia
    | rewrite R10; exact E32
    | rewrite R11; reflexivity
    | rewrite (KEEP 2%bv) by reflexivity; exact A2
    | rewrite (KEEP 3%bv) by reflexivity; exact A3
    | rewrite (KEEP 4%bv) by reflexivity; exact A4
    | exact R1
    | apply ret_ok_codeptr_v; [lia | reflexivity]
    | ].
  intros regs2 mem2 md2 HJ2 HP2 H00 Hkeep Hpres Hsbm.
  apply (HNEXT cx fpos k2 ly3 S3 W3 (mkst regs2 _ mem2 (seg_rom SEGS)) md2 HB HJ2 Hfrm).
  exists c, ci, j, adv. split; [exact HRcv|]. split; [exact Hcr|]. split; [exact Hci|]. split; [exact Hj|].
  apply (kq_land_mf SK B LAWS TB KI AMEMCPY LV 4 cx fpos KP_RAW (kregs_chunk cx fpos ci) (kr_sl cx fpos c)
           (kfsh 0xf8 0xf8 0xf3) (kfsh 0 0xf8 0xf3) adv (Some j) k2 ly3 S3 W3 ms3 md3 _ md2 0x1f3c
           (kregs_chunk cx fpos ci) HB HK (kr_sl_ok cx fpos c) ltac:(lia) ltac:(lia)).
  - intros a Ha Hn. exact (Hkeep a Ha Hn).
  - intros a Ha. exact (Hpres a Ha).
  - apply (kq_kshadow_w1 SK B LAWS TB KI AMEMCPY LV cx fpos W3 ms3 _ 0xf8 0xf8 0xf3 0 HSH).
    + intros i Hi Hn. apply Hkeep; [unfold kHighMemBeg, SHADOW_OFF in *; lia | lia].
    + intros i Hi. exact (H00 i Hi).
  - rewrite (proj1 (kn_sbm_fds_fs _ _ Hsbm)). repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
  - rewrite (proj2 (kn_sbm_fds_fs _ _ Hsbm)). repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
  - unfold kms. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst]. repeat split; reflexivity.
  - kr_regs0_after HP2 KEEP HR0.
  - kr_regs_after HP2 KEEP HRL.
Qed.

(* ---- kr_b: kr_c1 +0x1f3c -> checked_memset(w1, 0, 4112) -> kr_c2 +0x1f4c ---- *)
Theorem kr_b : forall POST Rc, kfrom SK B POST (kr_c2 B Rc) -> kfrom SK B POST (kr_c1 B Rc).
Proof.
  intros POST Rc HNEXT cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ Hfrm HI.
  destruct HI as (c & ci & j & adv & HRcv & Hcr & Hci & Hj & HK).
  pose proof HK as (HMS & HR0 & HRL & _ & HFR & HSH & HSL & HJB & _).
  pose proof HR0 as (A2 & A9 & A8 & A3 & A4 & A18 & A20).
  pose proof HB as (HPRE & _). pose proof HPRE as (_ & HGok & _).
  pose proof (kn_sp1 SK B cx HB) as (Hs1a & Hs1b & Hs1c & Hs1d & Hs1e & Hs1f & Hs1g & Hs1h).
  destruct (kn_F_facts B LAWS cx fpos k2 ly3 S3 md3 HJB) as (F1 & F2 & F3 & F4 & F5 & _).
  rewrite kn_fsb8 in F2, F3. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in F3.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HSLW : rdword (aview SEGS (w_H W3) (ms_mem ms3)) (ksp1 cx + KS_W1) = Some (kW1 cx fpos))
    by (apply (kn_slot_of cx W3 ms3 _ KS_W1 _ HSL); apply in_or_app; left; unfold kslots_setup; kn_in).
  assert (HSLN : rdword (aview SEGS (w_H W3) (ms_mem ms3)) (ksp1 cx + KS_NW) = Some NW_SIZE)
    by (apply (kn_slot_of cx W3 ms3 _ KS_NW _ HSL); apply in_or_app; left; unfold kslots_setup; kn_in).
  remember (Eimg (Ereg (ms_regs ms3) [w64 (kW1 cx fpos)])) as E eqn:HEdef.
  assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
  assert (E9 : ew E 9%nat = w64 (ksp1 cx)) by (subst E; rewrite <- A9; apply ew_Eimg_Ereg_nat; reflexivity).
  assert (E32 : ew E 32%nat = w64 (kW1 cx fpos)) by (subst E; apply (kq_E_32 SK B LAWS TB KI AMEMCPY LV)).
  assert (HS : st_ok_pi SEGS pa_val E rb_ss (restrict (w_H W3) ms3)).
  { unfold rb_ss. apply (kr_seat_sl cx fpos 0x1f3c _ _ _ true adv (Some j) k2 ly3 S3 W3 ms3 md3 E _ _ _ HK).
    - subst E. apply regs_ok_Eimg_Ereg.
    - unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E9. unfold w64. rewrite unsigned_lit_small by lia.
      split; [unfold KS_W1; lia|]. split; [unfold KS_NW; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      + apply (chunk_ok_val pa_segs E _ (ksp1 cx) KS_W1 8%N (SOff 32 0) (kW1 cx fpos)).
        * exact (sv_off0 E 32 _ E32).
        * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). unfold kW1, KN_W1. lia.
        * cbn; lia.
        * exact (val_mem_of_rdword pa_segs (w_H W3) (ms_mem ms3) _ _ HSLW).
      + apply (chunk_ok_val pa_segs E _ (ksp1 cx) KS_NW 8%N (SLit 4112) NW_SIZE).
        * reflexivity.
        * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). unfold NW_SIZE. lia.
        * cbn; lia.
        * exact (val_mem_of_rdword pa_segs (w_H W3) (ms_mem ms3) _ _ HSLN).
    - vm_compute. reflexivity. }
  pose proof HS as HS0.
  assert (SHOK : sh_ok SEGS kq_Bx [] E (mrestrict (w_H W3) (ms_mem ms3))) by (apply Forall_nil).
  pose (RUN := paj_run_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  paj_run_tok RUN HS HJ SHOK kq_span.
  { intros a Ha. exfalso. apply (kq_no_wrange _ _ a Ha). vm_compute. reflexivity. }
  lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into ms1 end.
  lazymatch goal with Hx : frame_of _ _ (ms_mem ms3) (ms_mem ms1) |- _ =>
    assert (HM1 : ms_mem ms1 = ms_mem ms3) by (eapply kq_mem_eq; [exact Hx | vm_compute; reflexivity]) end.
  pose proof (km_reg_same E rb_ss _ (w_H W3) ms3 ms1 km_csz HS0 HS ltac:(vm_compute; reflexivity)) as KEEP.
  prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11. prreg HS (12%bv : bv 5) R12.
  prreg HS (1%bv : bv 5) R1.
  pmkst HS.
  rewrite (lv_sigma LV). change (LinkAddr.link_sigma LS___asan_memset) with 0x53214.
  rewrite HM1. rewrite HM1 in HJ.
  eapply (kr_call_ms SK B LAWS LV TB KI AMEMCPY AMEMSET cx fpos k2 ly3 S3 W3 ms3 _ (ms_regs ms1) _ 0xf8 0xf3
            (POST cx) HB HJ HJB HSH);
    [ rewrite R10; exact E32
    | rewrite R11; reflexivity
    | rewrite R12; reflexivity
    | rewrite (KEEP 2%bv) by reflexivity; exact A2
    | rewrite (KEEP 3%bv) by reflexivity; exact A3
    | rewrite (KEEP 4%bv) by reflexivity; exact A4
    | exact R1
    | apply ret_ok_codeptr_v; [lia | reflexivity]
    | ].
  intros regs2 mem2 md2 HJ2 HP2 Hz Hkeep Hpres Hsbm.
  apply (HNEXT cx fpos k2 ly3 S3 W3 (mkst regs2 _ mem2 (seg_rom SEGS)) md2 HB HJ2 Hfrm).
  exists c, ci, j, adv. split; [exact HRcv|]. split; [exact Hcr|]. split; [exact Hci|]. split; [exact Hj|].
  split.
  - (* w1's fields are 0 *)
    pose proof HFR as (_ & _ & _ & _ & Hpf & _).
    unfold kw_at, nlw_fields. cbn [ms_mem mkst].
    split; [unfold kW1, KN_W1; lia|]. split; [unfold kW1, KN_W1, NW_SIZE; lia|].
    split.
    { intros i Hi. specialize (Hz i Hi). split.
      - unfold aview in Hz. destruct (mbyte SEGS (mrestrict (w_H W3) mem2) (kW1 cx fpos + i)) as [b|];
          [exists b; reflexivity | discriminate].
      - apply apresent_writable. apply Hpres. apply Hpf. rewrite kn_fsb8. unfold kW1, KN_W1, NW_SIZE in *. lia. }
    split; [apply kr_val_zero; intros i Hi; replace (kW1 cx fpos + NW_N + i) with (kW1 cx fpos + (NW_N + i)) by lia;
            apply Hz; unfold NW_N, NW_SIZE; cbn in Hi; lia|].
    split; [apply kr_val_zero; intros i Hi; replace (kW1 cx fpos + NW_FULL + i) with (kW1 cx fpos + (NW_FULL + i)) by lia;
            apply Hz; unfold NW_FULL, NW_SIZE; cbn in Hi; lia|].
    unfold NL_CHUNK_MAX. lia.
  - apply (kat_frame_w1s SK B LAWS 0 NW_SIZE cx fpos 0x1f3c _ _ _ true adv (Some j) k2 ly3 S3 W3 ms3 md3 0x1f4c
             (kregs_chunk cx fpos ci) (kr_sl cx fpos c) W3 _ md2 HB HK); [| | | apply incl_refl | apply kr_sl_ok
             | apply kfsh_fits | | | lia | unfold NW_SIZE; lia | | ].
    + unfold kms. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst]. repeat split; reflexivity.
    + kr_regs0_after HP2 KEEP HR0.
    + kr_regs_after HP2 KEEP HRL.
    + rewrite (proj1 (kn_sbm_fds_fs _ _ Hsbm)). repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
    + rewrite (proj2 (kn_sbm_fds_fs _ _ Hsbm)). repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
    + intros a Ha Hn. cbn [ms_mem mkst].
      apply Hkeep; [exact Ha | intros Hc; apply Hn; left; lia | intros Hc; apply Hn; right; lia].
    + intros a Ha. exact (Hpres a Ha).
Qed.

(* ---- kr_d: kr_c3 +0x2074 -> checked_memcpy(w1, p', t) -> kr_c4 +0x2078 ---- *)
Theorem kr_d : forall POST Rc, kfrom SK B POST (kr_c4 B Rc) -> kfrom SK B POST (kr_c3 B Rc).
Proof.
  intros POST Rc HNEXT cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ Hfrm HI.
  destruct HI as (c & ci & j & adv & t & HRcv & Hcr & Hci & Hj & Ht & Hta & HW & HK).
  pose proof HK as (HMS & HR0 & HRL & _ & _ & HSH & _ & HJB & HKK & HCUR & _).
  pose proof HCUR as (Hadv & _).
  destruct (kr_inp SK B LAWS LV TB KI AMEMCPY AMEMSET cx fpos k2 ly3 S3 W3 ms3 md3 (k_wp cx + adv - t) t
              HB HJ HJB HKK ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & _ & IPR & _ & IWN & ILO).
  pose proof HR0 as (A2 & A9 & A8 & A3 & A4 & A18 & A20).
  pose proof HB as (HPRE & _). pose proof HPRE as (_ & HGok & _).
  remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
  assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
  assert (ER : forall (q : nat) v, In (q, v) (kr_rl3 cx fpos ci t (k_wp cx + adv - t)) ->
            ew E q = Z_to_bv 64 v).
  { intros q v Hin. rewrite HEdef, (ew_Eimg_Ereg_nat (ms_regs ms3) [] q (Z_to_bv 5 (Z.of_nat q))).
    - exact (kn_reg_of ms3 _ q v HRL Hin).
    - unfold kr_rl3, kregs_chunk in Hin. cbn [In app] in Hin.
      assert (Hq32 : (q < 32)%nat)
        by (repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- _; lia|]); destruct Hin).
      rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. reflexivity. }
  pose proof (kq_seat0 B cx fpos 0x2074 _ _ _ true adv (Some j) k2 ly3 S3 W3 ms3 md3 E HEdef HK) as HS.
  pose proof HS as HS0.
  assert (SHOK : sh_ok SEGS kq_Bx [] E (mrestrict (w_H W3) (ms_mem ms3))) by (apply Forall_nil).
  pose (RUN := paj_run_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  paj_run_tok RUN HS HJ SHOK kq_span.
  { intros a Ha. exfalso. apply (kq_no_wrange _ _ a Ha). vm_compute. reflexivity. }
  lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into ms1 end.
  lazymatch goal with Hx : frame_of _ _ (ms_mem ms3) (ms_mem ms1) |- _ =>
    assert (HM1 : ms_mem ms1 = ms_mem ms3) by (eapply kq_mem_eq; [exact Hx | vm_compute; reflexivity]) end.
  pose proof (km_reg_same E (kq_ss0 0x2074) _ (w_H W3) ms3 ms1 km_csz HS0 HS ltac:(vm_compute; reflexivity)) as KEEP.
  prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11. prreg HS (12%bv : bv 5) R12.
  prreg HS (1%bv : bv 5) R1.
  pmkst HS.
  rewrite (lv_sigma LV). change (LinkAddr.link_sigma LS___asan_memcpy) with 0x52d78.
  rewrite HM1. rewrite HM1 in HJ.
  lazymatch type of HJ with ajournal_gx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdR _ =>
    assert (HKR : kat B cx fpos 0x2074 (kr_rl3 cx fpos ci t (k_wp cx + adv - t)) (kr_sl cx fpos c) (kfsh 0 0xf8 0xf3)
                    true adv (Some j) k2 ly3 S3 W3 ms3 mdR)
      by (apply (kat_frame_0 B cx fpos _ _ _ _ _ _ _ k2 ly3 S3 W3 ms3 md3 _ _ _ ms3 mdR HK HMS HR0 HRL eq_refl
                   (incl_refl _));
          [repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity
          | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity]) end.
  eapply (kr_call_icpy SK B LAWS LV TB KI AMEMCPY AMEMSET cx fpos 0x2074 _ _ _ adv (Some j) k2 ly3 S3 W3 ms3 _
            (ms_regs ms1) _ (k_wp cx + adv - t) t (POST cx) HB HJ HKR HSH Ht ltac:(lia) ltac:(lia));
    [ rewrite R10; apply ER; kr_in
    | rewrite R11; apply ER; kr_in
    | rewrite R12; apply ER; kr_in
    | rewrite (KEEP 2%bv) by reflexivity; exact A2
    | rewrite (KEEP 3%bv) by reflexivity; exact A3
    | rewrite (KEEP 4%bv) by reflexivity; exact A4
    | exact R1
    | apply ret_ok_codeptr_v; [lia | reflexivity]
    | ].
  intros regs2 mem2 md2 HJ2 HP2 Hcp Hkeep Hpres Hsbm.
  apply (HNEXT cx fpos k2 ly3 S3 W3 (mkst regs2 _ mem2 (seg_rom SEGS)) md2 HB HJ2 Hfrm).
  exists c, ci, j, adv, t. split; [exact HRcv|]. split; [exact Hcr|]. split; [exact Hci|]. split; [exact Hj|].
  split; [exact Ht|].
  pose proof (kn_sp SK B cx HB) as (S1 & S2 & S3' & S4 & S5 & S6 & S7 & S8 & S9 & _).
  destruct (kn_F_facts B LAWS cx fpos k2 ly3 S3 md3 HJB) as (F1 & F2 & F3 & F4 & F5 & _).
  rewrite kn_fsb8 in F2, F3. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in F3.
  pose proof (kn_F SK B LAWS cx fpos k2 ly3 S3 md3 HB HJB) as (HF4 & HFc & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HK8 : KERNEL_AK = 4640) by reflexivity. assert (HES : ESTACK = 4096) by reflexivity.
  split.
  - apply (kr_kw_cpy SK B LAWS LV TB KI AMEMCPY AMEMSET W3 ms3 _ _ 0 0 t HW ltac:(unfold NW_N; lia)).
    + intros i Hi. cbn [ms_mem mkst]. rewrite (Hcp i Hi). destruct (IPR (k_wp cx + adv - t + i) ltac:(lia)) as (v & Hv).
      rewrite Hv. discriminate.
    + intros i Hi. cbn [ms_mem mkst]. apply Hkeep; [unfold kW1, KN_W1, NW_SIZE in *; lia | lia |].
      rewrite HES. unfold kW1, KN_W1, NW_SIZE in *. lia.
    + intros a Ha. exact (Hpres a Ha).
  - apply (kat_frame_w1s SK B LAWS 0 t cx fpos 0x2074 _ _ _ true adv (Some j) k2 ly3 S3 W3 ms3 md3 0x2078
             (kr_rl4 cx fpos ci t) (kr_sl cx fpos c) W3 _ md2 HB HK); [| | | apply incl_refl | apply kr_sl_ok
             | apply kfsh_fits | | | lia | unfold NW_SIZE; lia | | ].
    + unfold kms. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst]. repeat split; reflexivity.
    + kr_regs0_after HP2 KEEP HR0.
    + kr_regs_after HP2 KEEP HRL.
    + rewrite (proj1 (kn_sbm_fds_fs _ _ Hsbm)). repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
    + rewrite (proj2 (kn_sbm_fds_fs _ _ Hsbm)). repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
    + intros a Ha Hn. cbn [ms_mem mkst].
      apply Hkeep; [exact Ha | intros Hc; apply Hn; left; lia | intros Hc; apply Hn; right; lia].
    + intros a Ha. exact (Hpres a Ha).
Qed.

(* ---- kr_f: kr_c5 +0x20b8 -> checked_memcpy(g_nl + 4096 j, w1, t) -> kr_c6 +0x20bc ---- *)
Theorem kr_f : forall POST Rc, kfrom SK B POST (kr_c6 B Rc) -> kfrom SK B POST (kr_c5 B Rc).
Proof.
  intros POST Rc HNEXT cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ Hfrm HI.
  destruct HI as (c & ci & j & adv & t & HRcv & Hcr & Hci & Hj & Ht & HK).
  pose proof HK as (HMS & HR0 & HRL & _ & HFR & HSH & _ & HJB & _ & _ & HGN & _).
  pose proof HFR as (_ & _ & _ & _ & Hpf & _).
  pose proof (kn_sp1 SK B cx HB) as (Hs1a & Hs1b & Hs1c & Hs1d & Hs1e & Hs1f & Hs1g & Hs1h).
  pose proof HR0 as (A2 & A9 & A8 & A3 & A4 & A18 & A20).
  pose proof HB as (HPRE & _). pose proof HPRE as (_ & HGok & _).
  remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
  assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
  assert (ER : forall (q : nat) v, In (q, v) (kr_rl5 cx fpos ci t j) -> ew E q = Z_to_bv 64 v).
  { intros q v Hin. rewrite HEdef, (ew_Eimg_Ereg_nat (ms_regs ms3) [] q (Z_to_bv 5 (Z.of_nat q))).
    - exact (kn_reg_of ms3 _ q v HRL Hin).
    - unfold kr_rl5, kr_rl0 in Hin. cbn [In app] in Hin.
      assert (Hq32 : (q < 32)%nat)
        by (repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- _; lia|]); destruct Hin).
      rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. reflexivity. }
  assert (HRA : range_addressable (aview SEGS (w_H W3) (ms_mem ms3)) SHADOW_OFF (kW1 cx fpos) t).
  { pose proof (kn_w1_ra B LAWS cx fpos k2 ly3 S3 md3 W3 ms3 0xf8 0xf3 HJB HSH) as HW1.
    intros y Hy. apply HW1. unfold NW_SIZE. lia. }
  pose proof (kq_seat0 B cx fpos 0x20b8 _ _ _ true adv (Some j) k2 ly3 S3 W3 ms3 md3 E HEdef HK) as HS.
  pose proof HS as HS0.
  assert (SHOK : sh_ok SEGS kq_Bx [] E (mrestrict (w_H W3) (ms_mem ms3))) by (apply Forall_nil).
  pose (RUN := paj_run_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  paj_run_tok RUN HS HJ SHOK kq_span.
  { intros a Ha. exfalso. apply (kq_no_wrange _ _ a Ha). vm_compute. reflexivity. }
  lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into ms1 end.
  lazymatch goal with Hx : frame_of _ _ (ms_mem ms3) (ms_mem ms1) |- _ =>
    assert (HM1 : ms_mem ms1 = ms_mem ms3) by (eapply kq_mem_eq; [exact Hx | vm_compute; reflexivity]) end.
  pose proof (km_reg_same E (kq_ss0 0x20b8) _ (w_H W3) ms3 ms1 km_csz HS0 HS ltac:(vm_compute; reflexivity)) as KEEP.
  prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11. prreg HS (12%bv : bv 5) R12.
  prreg HS (1%bv : bv 5) R1.
  pmkst HS.
  rewrite (lv_sigma LV). change (LinkAddr.link_sigma LS___asan_memcpy) with 0x52d78.
  rewrite HM1. rewrite HM1 in HJ.
  lazymatch type of HJ with ajournal_gx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdR _ =>
    assert (HKR : kat B cx fpos 0x20b8 (kr_rl5 cx fpos ci t j) (kr_sl cx fpos c) (kfsh 0 0xf8 0xf3) true adv
                    (Some j) k2 ly3 S3 W3 ms3 mdR)
      by (apply (kat_frame_0 B cx fpos _ _ _ _ _ _ _ k2 ly3 S3 W3 ms3 md3 _ _ _ ms3 mdR HK HMS HR0 HRL eq_refl
                   (incl_refl _));
          [repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity
          | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity]) end.
  eapply (kq_call_gcpy SK B LAWS TB KI AMEMCPY LV cx fpos 0x20b8 (kr_rl5 cx fpos ci t j) (kr_sl cx fpos c)
            (kfsh 0 0xf8 0xf3) adv (Some j) k2 ly3 S3 W3 ms3 _ (ms_regs ms1) _ j t (kW1 cx fpos) (POST cx) HB HJ HKR);
    [ lia | lia | unfold kW1, KN_W1; lia | unfold kW1, KN_W1, KN_FSZ; lia | exact HRA
    | rewrite R10; apply ER; kr_in
    | rewrite R11; apply ER; kr_in
    | rewrite R12; apply ER; kr_in
    | rewrite (KEEP 2%bv) by reflexivity; exact A2
    | rewrite (KEEP 3%bv) by reflexivity; exact A3
    | rewrite (KEEP 4%bv) by reflexivity; exact A4
    | exact R1
    | apply ret_ok_codeptr_v; [lia | reflexivity]
    | ].
  intros regs2 mem2 md2 HJ2 HP2 Hcp Hkeep Hpres Hsbm.
  apply (HNEXT cx fpos k2 ly3 S3 W3 (mkst regs2 _ mem2 (seg_rom SEGS)) md2 HB HJ2 Hfrm).
  exists c, ci, j, adv, t. split; [exact HRcv|]. split; [exact Hcr|]. split; [exact Hci|]. split; [exact Hj|].
  split; [exact Ht|].
  apply (kq_kat_g SK B LAWS TB KI AMEMCPY LV (fun a => ksp1 cx - ESTACK <= a < ksp1 cx)
           (fun a => LA_G_NL + 4096 * j <= a < LA_G_NL + 4096 * j + t) cx fpos 0x20b8 (kr_rl5 cx fpos ci t j)
           (kr_sl cx fpos c) (kfsh 0 0xf8 0xf3) true adv (Some j) k2 ly3 S3 W3 ms3 md3 0x20bc
           (kr_rl6 cx fpos ci t) (kr_sl cx fpos c) (Some j) W3 _ md2 HB HK).
  - unfold kms. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst]. repeat split; reflexivity.
  - kr_regs0_after HP2 KEEP HR0.
  - kr_regs_after HP2 KEEP HRL.
  - apply incl_refl.
  - apply kfsh_fits.
  - rewrite (proj1 (kn_sbm_fds_fs _ _ Hsbm)). repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
  - rewrite (proj2 (kn_sbm_fds_fs _ _ Hsbm)). repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
  - intros a Ha Ho Hg. exact (Hkeep a Ha Hg Ho).
  - intros a Ha. exact (Hpres a Ha).
  - intros a Ha. exact (kX_in_win SK B cx fpos a HB Ha).
  - apply (kX_miss_win SK B LAWS cx fpos k2 ly3 S3 md3 (kr_sl cx fpos c) _ _ HB HJB (kr_sl_ok cx fpos c));
      [rewrite kfsh_length; lia | intros a Ha; exact Ha].
  - intros a Ha. unfold NK_OPEN. lia.
  - apply (kq_gnl_keep SK B LAWS TB KI AMEMCPY LV cx W3 ms3 _ j HGN ltac:(lia)).
    + intros i Hi. cbn [ms_mem mkst].
      pose proof (kq_gnl_vis SK B LAWS TB KI AMEMCPY LV cx W3 ms3 (Some j) HGN i Hi) as Hv3.
      destruct (Z.lt_ge_cases i (4096 * j)) as [H1 | H1];
        [| destruct (Z.lt_ge_cases i (4096 * j + t)) as [H2 | H2]].
      * rewrite Hkeep; [exact Hv3 | unfold LA_G_NL, NK_SIZE in *; lia | lia | unfold ESTACK, LA_G_NL, NK_SIZE in *; lia].
      * replace (LA_G_NL + i) with (LA_G_NL + 4096 * j + (i - 4096 * j)) by lia.
        rewrite (Hcp (i - 4096 * j) ltac:(lia)). apply (kq_aview_some SK B LAWS TB KI AMEMCPY LV). apply Hpf.
        rewrite kn_fsb8. unfold kW1, KN_W1. lia.
      * rewrite Hkeep; [exact Hv3 | unfold LA_G_NL, NK_SIZE in *; lia | lia | unfold ESTACK, LA_G_NL, NK_SIZE in *; lia].
    + intros i Hi. cbn [ms_mem mkst].
      apply Hkeep; [unfold LA_G_NL, NK_SIZE, NK_CHUNK_LEN in *; lia | unfold NK_CHUNK_LEN in Hi; lia
                   | unfold ESTACK, LA_G_NL, NK_SIZE, NK_CHUNK_LEN in *; lia].
Qed.

(* ---- kr_h: kr_c7 +0x20f8 -> meta_fill_f8(shadow(w1), 0x202) -> kr_c8 +0x20fc ---- *)
Theorem kr_h : forall POST Rc, kfrom SK B POST (kr_c8 B Rc) -> kfrom SK B POST (kr_c7 B Rc).
Proof.
  intros POST Rc HNEXT cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ Hfrm HI.
  destruct HI as (c & ci & j & adv & HRcv & Hcr & Hci & Hj & HK).
  pose proof HK as (HMS & HR0 & HRL & _ & _ & HSH & _ & HJB & _).
  pose proof HR0 as (A2 & A9 & A8 & A3 & A4 & A18 & A20).
  pose proof HB as (HPRE & _). pose proof HPRE as (_ & HGok & _).
  remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
  assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
  assert (E10 : ew E 10%nat = w64 (kFSH cx fpos + 4)).
  { rewrite HEdef, (ew_Eimg_Ereg_nat (ms_regs ms3) [] 10 (Z_to_bv 5 (Z.of_nat 10)) eq_refl).
    apply (kn_reg_of ms3 _ 10 _ HRL). kr_in. }
  assert (E11 : ew E 11%nat = w64 0x202).
  { rewrite HEdef, (ew_Eimg_Ereg_nat (ms_regs ms3) [] 11 (Z_to_bv 5 (Z.of_nat 11)) eq_refl).
    apply (kn_reg_of ms3 _ 11 _ HRL). kr_in. }
  pose proof (kq_seat0 B cx fpos 0x20f8 _ _ _ true adv (Some j) k2 ly3 S3 W3 ms3 md3 E HEdef HK) as HS.
  pose proof HS as HS0.
  assert (SHOK : sh_ok SEGS kq_Bx [] E (mrestrict (w_H W3) (ms_mem ms3))) by (apply Forall_nil).
  pose (RUN := paj_run_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  paj_run_tok RUN HS HJ SHOK kq_span.
  { intros a Ha. exfalso. apply (kq_no_wrange _ _ a Ha). vm_compute. reflexivity. }
  lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into ms1 end.
  lazymatch goal with Hx : frame_of _ _ (ms_mem ms3) (ms_mem ms1) |- _ =>
    assert (HM1 : ms_mem ms1 = ms_mem ms3) by (eapply kq_mem_eq; [exact Hx | vm_compute; reflexivity]) end.
  pose proof (km_reg_same E (kq_ss0 0x20f8) _ (w_H W3) ms3 ms1 km_csz HS0 HS ltac:(vm_compute; reflexivity)) as KEEP.
  prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11. prreg HS (1%bv : bv 5) R1.
  pmkst HS.
  rewrite (lv_sigma LV). change (LinkAddr.link_sigma LS___asan_set_shadow_f8) with 0x55f94.
  rewrite HM1. rewrite HM1 in HJ.
  eapply (kq_call_mf SK B LAWS TB KI AMEMCPY LV 0x55f94 0xf8 ASSF8 cx fpos k2 ly3 S3 W3 (ms_mem ms3) _
            (ms_regs ms1) _ 4 (POST cx) HB HJ);
    [ lia | lia
    | rewrite R10; exact E10
    | rewrite R11; exact E11
    | rewrite (KEEP 2%bv) by reflexivity; exact A2
    | rewrite (KEEP 3%bv) by reflexivity; exact A3
    | rewrite (KEEP 4%bv) by reflexivity; exact A4
    | exact R1
    | apply ret_ok_codeptr_v; [lia | reflexivity]
    | ].
  intros regs2 mem2 md2 HJ2 HP2 Hf8 Hkeep Hpres Hsbm.
  apply (HNEXT cx fpos k2 ly3 S3 W3 (mkst regs2 _ mem2 (seg_rom SEGS)) md2 HB HJ2 Hfrm).
  exists c, ci, j, adv. split; [exact HRcv|]. split; [exact Hcr|]. split; [exact Hci|]. split; [exact Hj|].
  apply (kq_land_mf SK B LAWS TB KI AMEMCPY LV 4 cx fpos 0x20f8 (kr_rl7 cx fpos ci) (kr_sl cx fpos c)
           (kfsh 0 0xf8 0xf3) (kfsh 0xf8 0xf8 0xf3) adv (Some j) k2 ly3 S3 W3 ms3 md3 _ md2 0x20fc
           (kr_rl8 cx fpos ci) HB HK (kr_sl_ok cx fpos c) ltac:(lia) ltac:(lia)).
  - intros a Ha Hn. exact (Hkeep a Ha Hn).
  - intros a Ha. exact (Hpres a Ha).
  - apply (kq_kshadow_w1 SK B LAWS TB KI AMEMCPY LV cx fpos W3 ms3 _ 0 0xf8 0xf3 0xf8 HSH).
    + intros i Hi Hn. destruct (km_FSH_bound B LAWS cx fpos k2 ly3 S3 md3 HJB) as (FS1 & FS2).
      apply Hkeep; [unfold kHighMemBeg, SHADOW_OFF in *; lia | lia].
    + intros i Hi. exact (Hf8 i Hi).
  - rewrite (proj1 (kn_sbm_fds_fs _ _ Hsbm)). repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
  - rewrite (proj2 (kn_sbm_fds_fs _ _ Hsbm)). repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
  - unfold kms. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst]. repeat split; reflexivity.
  - kr_regs0_after HP2 KEEP HR0.
  - kr_regs_after HP2 KEEP HRL.
Qed.

(* ---- kr_i: kr_c8 +0x20fc -> mv s6, s7 -> kin_latch +0x2100 ---- *)
Theorem kr_i : forall POST Rc, kfrom SK B POST (kin_latch B Rc) -> kfrom SK B POST (kr_c8 B Rc).
Proof.
  intros POST Rc HNEXT cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ Hfrm HI.
  destruct HI as (c & ci & j & adv & HRcv & Hcr & Hci & Hj & HK).
  pose proof HK as (HMS & HR0 & HRL & _).
  pose proof HB as (HPRE & _). pose proof HPRE as (_ & HGok & _).
  remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
  assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
  assert (HAG : YP06.env_agree 32 (Ereg (ms_regs ms3) []) E)
    by (subst E; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E23 : ew E 23%nat = w64 ci).
  { rewrite HEdef, (ew_Eimg_Ereg_nat (ms_regs ms3) [] 23 (Z_to_bv 5 (Z.of_nat 23)) eq_refl).
    apply (kn_reg_of ms3 _ 23 _ HRL). kr_in. }
  pose proof (kq_seat0 B cx fpos 0x20fc _ _ _ true adv (Some j) k2 ly3 S3 W3 ms3 md3 E HEdef HK) as HS.
  assert (SHOK : sh_ok SEGS kq_Bx [] E (mrestrict (w_H W3) (ms_mem ms3))) by (apply Forall_nil).
  pose (RUNTO := paj_run_to_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  paj_run_to_tok RUNTO HS HJ SHOK kq_span (kpc KP_LATCH).
  { intros a Ha. exfalso. apply (kq_no_wrange _ _ a Ha). vm_compute. reflexivity. }
  lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms1 end.
  lazymatch goal with Hx : frame_of _ _ (ms_mem ms3) (ms_mem ms1) |- _ =>
    assert (HM1 : ms_mem ms1 = ms_mem ms3) by (eapply kq_mem_eq; [exact Hx | vm_compute; reflexivity]) end.
  assert (KEEP : forall r, In r nx_keep0 -> getr (ms_regs ms1) r = getr (ms_regs ms3) r)
    by exact (regs_kept_of_st_ok_pi E _ _ _ _ nx_keep0 HS HAG ltac:(vm_compute; reflexivity)).
  assert (KEEPN : forall r, In r (map (fun q : nat => Z_to_bv 5 (Z.of_nat q)) [19; 21; 24; 25]%nat) ->
            getr (ms_regs ms1) r = getr (ms_regs ms3) r)
    by exact (regs_kept_of_st_ok_pi E _ _ _ _ (map (fun q : nat => Z_to_bv 5 (Z.of_nat q)) [19; 21; 24; 25]%nat)
                HS HAG ltac:(vm_compute; reflexivity)).
  assert (HMS1 : kms KP_LATCH ms1) by (apply (kn_kms_of _ E _ ms1 KP_LATCH HS); vm_compute; reflexivity).
  assert (R22 : getr (ms_regs ms1) (Z_to_bv 5 (Z.of_nat 22)) = w64 ci).
  { rewrite (st_ok_pi_restrict_reg _ E _ ms1 _ HS).
    lazymatch goal with |- sv_denot _ (sr_get ?rs ?r) = _ =>
      let e := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with e end.
    exact (sv_off0 E 23 ci E23). }
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdn) _ => apply (HNEXT cx fpos k2 ly3 S3 W3 ms1 mdn HB HJ Hfrm) end.
  exists c, ci, j, adv. split; [exact HRcv|]. split; [exact Hcr|]. split; [exact Hci|]. split; [exact Hj|].
  apply (kat_frame_0 B cx fpos _ _ _ _ _ _ _ k2 ly3 S3 W3 ms3 md3 _ _ _ ms1 _ HK HMS1).
  - exact (kregs0_keep cx ms3 ms1 KEEP HR0).
  - unfold kregs_eq, kregs_chunk. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    + rewrite (KEEPN _ (kn_in_map5 19 [19; 21; 24; 25]%nat ltac:(kn_in))). apply (kn_reg_of ms3 _ _ _ HRL).
      kr_in.
    + rewrite (KEEPN _ (kn_in_map5 21 [19; 21; 24; 25]%nat ltac:(kn_in))). apply (kn_reg_of ms3 _ _ _ HRL).
      kr_in.
    + exact R22.
    + rewrite (KEEPN _ (kn_in_map5 24 [19; 21; 24; 25]%nat ltac:(kn_in))). apply (kn_reg_of ms3 _ _ _ HRL).
      kr_in.
    + rewrite (KEEPN _ (kn_in_map5 25 [19; 21; 24; 25]%nat ltac:(kn_in))). apply (kn_reg_of ms3 _ _ _ HRL).
      kr_in.
  - exact HM1.
  - intros x Hx. unfold kr_sl. apply in_or_app. left. exact Hx.
  - exact (proj1 (wvb_fds_fs _ _ _)).
  - exact (proj2 (wvb_fds_fs _ _ _)).
Qed.

End b.
End a.
