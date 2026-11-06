(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 609 of its 643 lines of code are new or changed and 1890 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/kernel_exit.v, with its module paths and module names changed; 486 of its 525 lines of code are new or changed and 604 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: the walk of kernel (fuzz_link.asan 0x83d30), the raw path's chunk read
   kr_c2 +0x1f4c -> kr_c3 +0x2074 / kr_c7 +0x20f8 (kernel_raw_c.v states the code), by the bytes left:
     rc_l0 (left = 0), rc_l1 (left = 1): one run to +0x20f8, no chunk (the cursor at p + left, 0 bytes left);
     rc_l2 (left = 2): the run stops at `bltu s11, a0` (+0x2010, a0 = 0): taken is refuted (nl + 1 < 0), not taken
       runs to +0x20f8;
     rc_l3 (left >= 3): `bltu s11, a0` (a0 = left - 2) splits: take = nl + 1 (taken) or left - 2 (not taken); then the
       room test `bltu w1.n + take, 4097` (+0x2050): not taken is refuted (take <= 4096); taken runs to the jal of
       checked_memcpy at +0x2074 (kr_c3).
   Each case is split on j in {0, 1, 2} first (n_chunks is a literal of the state). The cut after a run is
   kernel_raw_c.v rc_land7 / rc_land3; the frames of the runs of one path are chained (the same writable windows).
   kr_c composes the cases.
   Section hypotheses: LAWS, LV, TB, KI, AMEMCPY, AMEMSET.
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_qmsg_a kernel_qmsg_b kernel_raw_kit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_raw_b kernel_raw_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* every lemma of the Section below takes all its hypotheses (one calling convention for the lane) *)
Set Default Proof Using "All".

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

(* two runs' kept bytes, chained *)
Lemma rd_chain : forall (W3 : world SEGS) (m0 m1 m2 : word -> option byte) (Z : Z -> Prop),
  (forall x, 0 <= x < 2 ^ 64 -> ~ Z x -> aview SEGS (w_H W3) m1 x = aview SEGS (w_H W3) m0 x) ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ Z x -> aview SEGS (w_H W3) m2 x = aview SEGS (w_H W3) m1 x) ->
  forall x, 0 <= x < 2 ^ 64 -> ~ Z x -> aview SEGS (w_H W3) m2 x = aview SEGS (w_H W3) m0 x.
Proof. intros W3 m0 m1 m2 Z H1 H2 x Hx Hn. rewrite (H2 x Hx Hn). exact (H1 x Hx Hn). Qed.

(* ---- left = 0 ---- *)
Theorem rc_l0 : forall POST Rc cx fpos k2 ly3 S3 W3 ms3 md3 c ci j adv,
  kfrom SK B POST (kr_c3 B Rc) -> kfrom SK B POST (kr_c7 B Rc) ->
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  frames S3 = (KN_CID, fpos) :: frames (k_Sc cx) ->
  Rc cx (c - ci) -> 1 <= c <= 3 -> 0 <= ci < c -> 0 <= j <= ci ->
  kw_at W3 ms3 (kW1 cx fpos) 0 0 ->
  kat B cx fpos 0x1f4c (kregs_chunk cx fpos ci) (kr_sl cx fpos c) (kfsh 0 0xf8 0xf3) true adv (Some j)
    k2 ly3 S3 W3 ms3 md3 ->
  k_wn cx - adv = 0 ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros POST Rc cx fpos k2 ly3 S3 W3 ms3 md3 c ci j adv HN3 HN7 HB HJ Hfrm HRcv Hcr Hci Hj HW HK Hl.
  pose proof HK as (HMS & HR0 & HRL & _ & _ & HSH & HSL & HJB & HKK & HCUR & HGN & _).
  pose proof HCUR as (Hadv & HCP & HCN & HCW).
  pose proof HB as (HPRE & _). pose proof HPRE as (_ & HGok & _).
  pose proof (kn_apre SK B cx HB) as (_ & _ & _ & _ & HAMR & _).
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & HWPr & HWNr & _).
  assert (Hp : k_wp cx + k_wn cx <= 2 ^ 47 - 1)
    by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAMR; lia).
  destruct (kn_F_facts B LAWS cx fpos k2 ly3 S3 md3 HJB) as (F1 & F2 & _).
  rewrite kn_fsb8 in F2.
  destruct (km_FSH_bound B LAWS cx fpos k2 ly3 S3 md3 HJB) as (FS1 & FS2).
  destruct (km_cur_loc SK B LAWS cx fpos k2 ly3 S3 md3 HB HJB) as (CU0 & CU16 & _).
  pose proof asan_consts as ((C1a & C1b) & _).
  assert (RW2 : 0 <= kW2 cx fpos /\ kW2 cx fpos + NW_N + 8 < 2 ^ 47) by (unfold kW2, KN_W2, NW_N, alloc_ceiling in *; lia).
  assert (RW1 : 0 <= kW1 cx fpos /\ kW1 cx fpos + NW_N + 8 < 2 ^ 47) by (unfold kW1, KN_W1, NW_N, alloc_ceiling in *; lia).
  assert (RFS : 0 <= kFSH cx fpos /\ kFSH cx fpos + 0x208 < 2 ^ 47) by (unfold kHighMemBeg, SHADOW_OFF in *; lia).
  assert (HN4 : NW_N = 4096) by reflexivity.
  destruct (rc_bytes SK B LAWS LV TB KI AMEMCPY AMEMSET cx fpos k2 ly3 S3 W3 ms3 md3 adv 0 HB HJ HJB HKK ltac:(lia)
              ltac:(lia) ltac:(lia)) as (d0 & d1 & Hd0 & Hd1 & Hd0v & Hd1v).
  remember (rc_E ms3 (k_wn cx - adv) (k_wp cx + adv) d0 d1 (kW1 cx fpos + NW_N) (kFSH cx fpos + 4)) as E eqn:HEdef.
  assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
  assert (HAG : YP06.env_agree 32 (Ereg (ms_regs ms3) [w64 (k_wn cx - adv); w64 (k_wp cx + adv); w64 d0; w64 d1;
                  w64 (kW1 cx fpos + NW_N); w64 (kFSH cx fpos + 4)]) E)
    by (subst E; unfold rc_E; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  destruct (rc_U SK B LAWS LV TB KI AMEMCPY AMEMSET cx fpos k2 ly3 S3 md3 ms3 ci adv d0 d1 E HB HJB HR0 HRL ltac:(lia)
              Hadv ltac:(lia) ltac:(lia) Hd0 Hd1 HEdef)
    as (U9 & U18 & U20 & U19 & U21 & U22 & U24 & U25 & U32 & U33 & U34 & U35 & U36 & U37 & U243).
  pose proof (Z.mod_pos_bound d1 16 ltac:(lia)) as Hm16.
  pose (RUN := paj_run_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  pose (RUNTO := paj_run_to_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  pose (BR := paj_branch (PI := PI)).
  assert (Hlv : sv_denot E (SLit 0) = Z_to_bv 64 (k_wn cx - adv)) by (rewrite Hl; reflexivity).
  assert (Hla : afact_ok E 32 (mkAF 0 0 0))
    by (unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U32; change (2 ^ 0) with 1; rewrite Z.mod_1_r; lia).
  assert (Hj2 : j = 0 \/ j = 1 \/ j = 2) by lia.
  destruct Hj2 as [-> | [-> | ->]];
   (lazymatch type of HK with kat _ _ _ _ _ _ _ _ _ (Some ?jv) _ _ _ _ _ _ =>
    destruct (rc_seat SK B LAWS LV TB KI AMEMCPY AMEMSET cx fpos k2 ly3 S3 W3 ms3 md3 c ci jv adv (SLit 0) (mkAF 0 0 0) 0 8 d0 d1 E
                HB HJ HW HK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hd0v Hd1v Hd0 Hd1 HEdef Hlv Hla
                ltac:(vm_compute; reflexivity)) as (HS & SHOK);
    paj_run_to_tok RUNTO HS HJ SHOK kq_span (kpc 0x20f8);
      [ apply (rc_awr SK B LAWS LV TB KI AMEMCPY AMEMSET cx fpos k2 ly3 S3 W3 _ _ md3 _ _ HB HJ HJB);
          [ repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity
          | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity
          | rc_wr ]
        | ];
      lazymatch goal with
      | HS' : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msn),
        HFr' : frame_of _ _ (mrestrict _ _) (mrestrict _ (ms_mem ?msn)),
        HG' : mem_grows _ (mrestrict _ (ms_mem ?msn))
        |- SRr _ _ (mkCfg ?msn ?mdn) _ =>
        let HR1 := fresh "HR1" in spregion HS' 1%nat HR1;
        let HAGx := fresh "HAGx" in
        lazymatch type of HAG with YP06.env_agree 32 ?R _ =>
          assert (HAGx : YP06.env_agree 32 R Ex) by rc_agree HAG end;
        apply (rc_land7 SK B LAWS LV TB KI AMEMCPY AMEMSET POST Rc cx fpos k2 ly3 S3 W3 ms3 md3 c ci jv adv 0 msn mdn
                 HN7 HB Hfrm HJ HRcv Hcr Hci ltac:(lia) HK ltac:(lia));
        [ eapply (field_of_region Ex _ 18 (ka0 cx) _ _ _ _ _ 0 8%N _ (k_wp cx + (adv + 0)));
            [exact HR1 | rc_ea | kn_in | apply kr_denot_of_U; rcU
            | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | change (Z.of_N 8) with 8; lia]
        | eapply (field_of_region Ex _ 18 (ka0 cx) _ _ _ _ _ 8 8%N _ (k_wn cx - (adv + 0)));
            [exact HR1 | rc_ea | kn_in | apply kr_denot_of_U; rcU
            | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | change (Z.of_N 8) with 8; lia]
        | rc_un HFr' (fun x => (ka0 cx <= x < ka0 cx + 16) \/ (kW1 cx fpos + NW_N <= x < kW1 cx fpos + NW_N + 8))
        | exact HG'
        | apply (kn_kms_of _ Ex ssx msn 0x20f8 HS'); vm_compute; reflexivity
        | exact (kregs0_keep cx ms3 msn (regs_kept_of_st_ok_pi Ex ssx _ _ _ nx_keep0 HS' HAGx
                   ltac:(vm_compute; reflexivity)) HR0)
        | unfold kregs_eq; cbn [kr_rl7 kr_rl0 app]; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
          rc_reg HS' Ex ssx msn
        | repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity
        | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity ]
      end
    end).
Qed.

(* ---- left = 1 ---- *)
Theorem rc_l1 : forall POST Rc cx fpos k2 ly3 S3 W3 ms3 md3 c ci j adv,
  kfrom SK B POST (kr_c3 B Rc) -> kfrom SK B POST (kr_c7 B Rc) ->
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  frames S3 = (KN_CID, fpos) :: frames (k_Sc cx) ->
  Rc cx (c - ci) -> 1 <= c <= 3 -> 0 <= ci < c -> 0 <= j <= ci ->
  kw_at W3 ms3 (kW1 cx fpos) 0 0 ->
  kat B cx fpos 0x1f4c (kregs_chunk cx fpos ci) (kr_sl cx fpos c) (kfsh 0 0xf8 0xf3) true adv (Some j)
    k2 ly3 S3 W3 ms3 md3 ->
  k_wn cx - adv = 1 ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros POST Rc cx fpos k2 ly3 S3 W3 ms3 md3 c ci j adv HN3 HN7 HB HJ Hfrm HRcv Hcr Hci Hj HW HK Hl.
  pose proof HK as (HMS & HR0 & HRL & _ & _ & HSH & HSL & HJB & HKK & HCUR & HGN & _).
  pose proof HCUR as (Hadv & HCP & HCN & HCW).
  pose proof HB as (HPRE & _). pose proof HPRE as (_ & HGok & _).
  pose proof (kn_apre SK B cx HB) as (_ & _ & _ & _ & HAMR & _).
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & HWPr & HWNr & _).
  assert (Hp : k_wp cx + k_wn cx <= 2 ^ 47 - 1)
    by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAMR; lia).
  destruct (kn_F_facts B LAWS cx fpos k2 ly3 S3 md3 HJB) as (F1 & F2 & _).
  rewrite kn_fsb8 in F2.
  destruct (km_FSH_bound B LAWS cx fpos k2 ly3 S3 md3 HJB) as (FS1 & FS2).
  destruct (km_cur_loc SK B LAWS cx fpos k2 ly3 S3 md3 HB HJB) as (CU0 & CU16 & _).
  pose proof asan_consts as ((C1a & C1b) & _).
  assert (RW2 : 0 <= kW2 cx fpos /\ kW2 cx fpos + NW_N + 8 < 2 ^ 47) by (unfold kW2, KN_W2, NW_N, alloc_ceiling in *; lia).
  assert (RW1 : 0 <= kW1 cx fpos /\ kW1 cx fpos + NW_N + 8 < 2 ^ 47) by (unfold kW1, KN_W1, NW_N, alloc_ceiling in *; lia).
  assert (RFS : 0 <= kFSH cx fpos /\ kFSH cx fpos + 0x208 < 2 ^ 47) by (unfold kHighMemBeg, SHADOW_OFF in *; lia).
  assert (HN4 : NW_N = 4096) by reflexivity.
  destruct (rc_bytes SK B LAWS LV TB KI AMEMCPY AMEMSET cx fpos k2 ly3 S3 W3 ms3 md3 adv 1 HB HJ HJB HKK ltac:(lia)
              ltac:(lia) ltac:(lia)) as (d0 & d1 & Hd0 & Hd1 & Hd0v & Hd1v).
  remember (rc_E ms3 (k_wn cx - adv) (k_wp cx + adv) d0 d1 (kW1 cx fpos + NW_N) (kFSH cx fpos + 4)) as E eqn:HEdef.
  assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
  assert (HAG : YP06.env_agree 32 (Ereg (ms_regs ms3) [w64 (k_wn cx - adv); w64 (k_wp cx + adv); w64 d0; w64 d1;
                  w64 (kW1 cx fpos + NW_N); w64 (kFSH cx fpos + 4)]) E)
    by (subst E; unfold rc_E; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  destruct (rc_U SK B LAWS LV TB KI AMEMCPY AMEMSET cx fpos k2 ly3 S3 md3 ms3 ci adv d0 d1 E HB HJB HR0 HRL ltac:(lia)
              Hadv ltac:(lia) ltac:(lia) Hd0 Hd1 HEdef)
    as (U9 & U18 & U20 & U19 & U21 & U22 & U24 & U25 & U32 & U33 & U34 & U35 & U36 & U37 & U243).
  pose proof (Z.mod_pos_bound d1 16 ltac:(lia)) as Hm16.
  pose (RUN := paj_run_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  pose (RUNTO := paj_run_to_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  pose (BR := paj_branch (PI := PI)).
  assert (Hlv : sv_denot E (SLit 1) = Z_to_bv 64 (k_wn cx - adv)) by (rewrite Hl; reflexivity).
  assert (Hla : afact_ok E 32 (mkAF 1 1 0))
    by (unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U32; change (2 ^ 0) with 1; rewrite Z.mod_1_r; lia).
  assert (Hj2 : j = 0 \/ j = 1 \/ j = 2) by lia.
  destruct Hj2 as [-> | [-> | ->]];
   (lazymatch type of HK with kat _ _ _ _ _ _ _ _ _ (Some ?jv) _ _ _ _ _ _ =>
    destruct (rc_seat SK B LAWS LV TB KI AMEMCPY AMEMSET cx fpos k2 ly3 S3 W3 ms3 md3 c ci jv adv (SLit 1) (mkAF 1 1 0) 1 8 d0 d1 E
                HB HJ HW HK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hd0v Hd1v Hd0 Hd1 HEdef Hlv Hla
                ltac:(vm_compute; reflexivity)) as (HS & SHOK);
    paj_run_to_tok RUNTO HS HJ SHOK kq_span (kpc 0x20f8);
      [ apply (rc_awr SK B LAWS LV TB KI AMEMCPY AMEMSET cx fpos k2 ly3 S3 W3 _ _ md3 _ _ HB HJ HJB);
          [ repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity
          | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity
          | rc_wr ]
        | ];
      lazymatch goal with
      | HS' : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msn),
        HFr' : frame_of _ _ (mrestrict _ _) (mrestrict _ (ms_mem ?msn)),
        HG' : mem_grows _ (mrestrict _ (ms_mem ?msn))
        |- SRr _ _ (mkCfg ?msn ?mdn) _ =>
        let HR1 := fresh "HR1" in spregion HS' 1%nat HR1;
        let HAGx := fresh "HAGx" in
        lazymatch type of HAG with YP06.env_agree 32 ?R _ =>
          assert (HAGx : YP06.env_agree 32 R Ex) by rc_agree HAG end;
        apply (rc_land7 SK B LAWS LV TB KI AMEMCPY AMEMSET POST Rc cx fpos k2 ly3 S3 W3 ms3 md3 c ci jv adv 1 msn mdn
                 HN7 HB Hfrm HJ HRcv Hcr Hci ltac:(lia) HK ltac:(lia));
        [ eapply (field_of_region Ex _ 18 (ka0 cx) _ _ _ _ _ 0 8%N _ (k_wp cx + (adv + 1)));
            [exact HR1 | rc_ea | kn_in | apply kr_denot_of_U; rcU
            | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | change (Z.of_N 8) with 8; lia]
        | eapply (field_of_region Ex _ 18 (ka0 cx) _ _ _ _ _ 8 8%N _ (k_wn cx - (adv + 1)));
            [exact HR1 | rc_ea | kn_in | apply kr_denot_of_U; rcU
            | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | change (Z.of_N 8) with 8; lia]
        | rc_un HFr' (fun x => (ka0 cx <= x < ka0 cx + 16) \/ (kW1 cx fpos + NW_N <= x < kW1 cx fpos + NW_N + 8))
        | exact HG'
        | apply (kn_kms_of _ Ex ssx msn 0x20f8 HS'); vm_compute; reflexivity
        | exact (kregs0_keep cx ms3 msn (regs_kept_of_st_ok_pi Ex ssx _ _ _ nx_keep0 HS' HAGx
                   ltac:(vm_compute; reflexivity)) HR0)
        | unfold kregs_eq; cbn [kr_rl7 kr_rl0 app]; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
          rc_reg HS' Ex ssx msn
        | repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity
        | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity ]
      end
    end).
Qed.

(* ---- left = 2 ---- *)
Theorem rc_l2 : forall POST Rc cx fpos k2 ly3 S3 W3 ms3 md3 c ci j adv,
  kfrom SK B POST (kr_c3 B Rc) -> kfrom SK B POST (kr_c7 B Rc) ->
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  frames S3 = (KN_CID, fpos) :: frames (k_Sc cx) ->
  Rc cx (c - ci) -> 1 <= c <= 3 -> 0 <= ci < c -> 0 <= j <= ci ->
  kw_at W3 ms3 (kW1 cx fpos) 0 0 ->
  kat B cx fpos 0x1f4c (kregs_chunk cx fpos ci) (kr_sl cx fpos c) (kfsh 0 0xf8 0xf3) true adv (Some j)
    k2 ly3 S3 W3 ms3 md3 ->
  k_wn cx - adv = 2 ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros POST Rc cx fpos k2 ly3 S3 W3 ms3 md3 c ci j adv HN3 HN7 HB HJ Hfrm HRcv Hcr Hci Hj HW HK Hl.
  pose proof HK as (HMS & HR0 & HRL & _ & _ & HSH & HSL & HJB & HKK & HCUR & HGN & _).
  pose proof HCUR as (Hadv & HCP & HCN & HCW).
  pose proof HB as (HPRE & _). pose proof HPRE as (_ & HGok & _).
  pose proof (kn_apre SK B cx HB) as (_ & _ & _ & _ & HAMR & _).
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & HWPr & HWNr & _).
  assert (Hp : k_wp cx + k_wn cx <= 2 ^ 47 - 1)
    by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAMR; lia).
  destruct (kn_F_facts B LAWS cx fpos k2 ly3 S3 md3 HJB) as (F1 & F2 & _).
  rewrite kn_fsb8 in F2.
  destruct (km_FSH_bound B LAWS cx fpos k2 ly3 S3 md3 HJB) as (FS1 & FS2).
  destruct (km_cur_loc SK B LAWS cx fpos k2 ly3 S3 md3 HB HJB) as (CU0 & CU16 & _).
  pose proof asan_consts as ((C1a & C1b) & _).
  assert (RW2 : 0 <= kW2 cx fpos /\ kW2 cx fpos + NW_N + 8 < 2 ^ 47) by (unfold kW2, KN_W2, NW_N, alloc_ceiling in *; lia).
  assert (RW1 : 0 <= kW1 cx fpos /\ kW1 cx fpos + NW_N + 8 < 2 ^ 47) by (unfold kW1, KN_W1, NW_N, alloc_ceiling in *; lia).
  assert (RFS : 0 <= kFSH cx fpos /\ kFSH cx fpos + 0x208 < 2 ^ 47) by (unfold kHighMemBeg, SHADOW_OFF in *; lia).
  assert (HN4 : NW_N = 4096) by reflexivity.
  destruct (rc_bytes SK B LAWS LV TB KI AMEMCPY AMEMSET cx fpos k2 ly3 S3 W3 ms3 md3 adv 2 HB HJ HJB HKK ltac:(lia)
              ltac:(lia) ltac:(lia)) as (d0 & d1 & Hd0 & Hd1 & Hd0v & Hd1v).
  remember (rc_E ms3 (k_wn cx - adv) (k_wp cx + adv) d0 d1 (kW1 cx fpos + NW_N) (kFSH cx fpos + 4)) as E eqn:HEdef.
  assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
  assert (HAG : YP06.env_agree 32 (Ereg (ms_regs ms3) [w64 (k_wn cx - adv); w64 (k_wp cx + adv); w64 d0; w64 d1;
                  w64 (kW1 cx fpos + NW_N); w64 (kFSH cx fpos + 4)]) E)
    by (subst E; unfold rc_E; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  destruct (rc_U SK B LAWS LV TB KI AMEMCPY AMEMSET cx fpos k2 ly3 S3 md3 ms3 ci adv d0 d1 E HB HJB HR0 HRL ltac:(lia)
              Hadv ltac:(lia) ltac:(lia) Hd0 Hd1 HEdef)
    as (U9 & U18 & U20 & U19 & U21 & U22 & U24 & U25 & U32 & U33 & U34 & U35 & U36 & U37 & U243).
  pose proof (Z.mod_pos_bound d1 16 ltac:(lia)) as Hm16.
  pose (RUN := paj_run_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  pose (RUNTO := paj_run_to_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  pose (BR := paj_branch (PI := PI)).
  assert (Hlv : sv_denot E (SLit 2) = Z_to_bv 64 (k_wn cx - adv)) by (rewrite Hl; reflexivity).
  assert (Hla : afact_ok E 32 (mkAF 2 2 0))
    by (unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U32; change (2 ^ 0) with 1; rewrite Z.mod_1_r; lia).
  assert (Hj2 : j = 0 \/ j = 1 \/ j = 2) by lia.
  destruct Hj2 as [-> | [-> | ->]];
   (lazymatch type of HK with kat _ _ _ _ _ _ _ _ _ (Some ?jv) _ _ _ _ _ _ =>
    destruct (rc_seat SK B LAWS LV TB KI AMEMCPY AMEMSET cx fpos k2 ly3 S3 W3 ms3 md3 c ci jv adv (SLit 2) (mkAF 2 2 0) 2 8 d0 d1 E
                HB HJ HW HK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hd0v Hd1v Hd0 Hd1 HEdef Hlv Hla
                ltac:(vm_compute; reflexivity)) as (HS & SHOK);
    paj_run_tok RUN HS HJ SHOK kq_span;
      [ apply (rc_awr SK B LAWS LV TB KI AMEMCPY AMEMSET cx fpos k2 ly3 S3 W3 _ _ md3 _ _ HB HJ HJB);
          [ repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity
          | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity
          | rc_wr ]
        | ];
      lazymatch goal with
      | HFr1 : frame_of _ _ (mrestrict _ (ms_mem ms3)) (mrestrict _ (ms_mem ?m1)),
        HG1 : mem_grows (mrestrict _ (ms_mem ms3)) (mrestrict _ (ms_mem ?m1)) |- _ =>
        assert (HUa : forall x, 0 <= x < 2 ^ 64 -> ~ ((fun x => (ka0 cx <= x < ka0 cx + 16) \/ (kW1 cx fpos + NW_N <= x < kW1 cx fpos + NW_N + 8)) x) ->
                        aview SEGS (w_H W3) (ms_mem m1) x = aview SEGS (w_H W3) (ms_mem ms3) x) by rc_un HFr1 (fun x => (ka0 cx <= x < ka0 cx + 16) \/ (kW1 cx fpos + NW_N <= x < kW1 cx fpos + NW_N + 8));
        rename HG1 into HGa; clear HFr1
      end;
    psrr_branch_tok RUN BR HS SHOK kq_span;
    [ rc_cond Hc; apply Z.ltb_lt in Hc; lia
    | paj_run_to_tok RUNTO HS HJ SHOK kq_span (kpc 0x20f8);
        [ apply (rc_awr SK B LAWS LV TB KI AMEMCPY AMEMSET cx fpos k2 ly3 S3 W3 _ _ md3 _ _ HB HJ HJB);
          [ repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity
          | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity
          | rc_wr ]
        | ];
      lazymatch goal with
      | HS' : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msn),
        HFr' : frame_of _ _ (mrestrict _ _) (mrestrict _ (ms_mem ?msn)),
        HG' : mem_grows _ (mrestrict _ (ms_mem ?msn))
        |- SRr _ _ (mkCfg ?msn ?mdn) _ =>
        let HR1 := fresh "HR1" in spregion HS' 1%nat HR1;
        let HAGx := fresh "HAGx" in
        lazymatch type of HAG with YP06.env_agree 32 ?R _ =>
          assert (HAGx : YP06.env_agree 32 R Ex) by rc_agree HAG end;
        apply (rc_land7 SK B LAWS LV TB KI AMEMCPY AMEMSET POST Rc cx fpos k2 ly3 S3 W3 ms3 md3 c ci jv adv 2 msn mdn
                 HN7 HB Hfrm HJ HRcv Hcr Hci ltac:(lia) HK ltac:(lia));
        [ eapply (field_of_region Ex _ 18 (ka0 cx) _ _ _ _ _ 0 8%N _ (k_wp cx + (adv + 2)));
            [exact HR1 | rc_ea | kn_in | apply kr_denot_of_U; rcU
            | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | change (Z.of_N 8) with 8; lia]
        | eapply (field_of_region Ex _ 18 (ka0 cx) _ _ _ _ _ 8 8%N _ (k_wn cx - (adv + 2)));
            [exact HR1 | rc_ea | kn_in | apply kr_denot_of_U; rcU
            | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | change (Z.of_N 8) with 8; lia]
        | lazymatch type of HUa with forall x, _ -> _ -> aview _ _ (ms_mem ?m1) x = _ =>
            apply (rd_chain W3 (ms_mem ms3) (ms_mem m1) (ms_mem msn) (fun x => (ka0 cx <= x < ka0 cx + 16) \/ (kW1 cx fpos + NW_N <= x < kW1 cx fpos + NW_N + 8)) HUa); rc_un HFr' (fun x => (ka0 cx <= x < ka0 cx + 16) \/ (kW1 cx fpos + NW_N <= x < kW1 cx fpos + NW_N + 8)) end
        | exact (mem_grows_trans _ _ _ HGa HG')
        | apply (kn_kms_of _ Ex ssx msn 0x20f8 HS'); vm_compute; reflexivity
        | exact (kregs0_keep cx ms3 msn (regs_kept_of_st_ok_pi Ex ssx _ _ _ nx_keep0 HS' HAGx
                   ltac:(vm_compute; reflexivity)) HR0)
        | unfold kregs_eq; cbn [kr_rl7 kr_rl0 app]; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
          rc_reg HS' Ex ssx msn
        | repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity
        | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity ]
      end ]
    end).
Qed.

(* ---- left >= 3 ---- *)
Theorem rc_l3 : forall POST Rc cx fpos k2 ly3 S3 W3 ms3 md3 c ci j adv,
  kfrom SK B POST (kr_c3 B Rc) -> kfrom SK B POST (kr_c7 B Rc) ->
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  frames S3 = (KN_CID, fpos) :: frames (k_Sc cx) ->
  Rc cx (c - ci) -> 1 <= c <= 3 -> 0 <= ci < c -> 0 <= j <= ci ->
  kw_at W3 ms3 (kW1 cx fpos) 0 0 ->
  kat B cx fpos 0x1f4c (kregs_chunk cx fpos ci) (kr_sl cx fpos c) (kfsh 0 0xf8 0xf3) true adv (Some j)
    k2 ly3 S3 W3 ms3 md3 ->
  3 <= k_wn cx - adv ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros POST Rc cx fpos k2 ly3 S3 W3 ms3 md3 c ci j adv HN3 HN7 HB HJ Hfrm HRcv Hcr Hci Hj HW HK Hl.
  pose proof HK as (HMS & HR0 & HRL & _ & _ & HSH & HSL & HJB & HKK & HCUR & HGN & _).
  pose proof HCUR as (Hadv & HCP & HCN & HCW).
  pose proof HB as (HPRE & _). pose proof HPRE as (_ & HGok & _).
  pose proof (kn_apre SK B cx HB) as (_ & _ & _ & _ & HAMR & _).
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & HWPr & HWNr & _).
  assert (Hp : k_wp cx + k_wn cx <= 2 ^ 47 - 1)
    by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAMR; lia).
  destruct (kn_F_facts B LAWS cx fpos k2 ly3 S3 md3 HJB) as (F1 & F2 & _).
  rewrite kn_fsb8 in F2.
  destruct (km_FSH_bound B LAWS cx fpos k2 ly3 S3 md3 HJB) as (FS1 & FS2).
  destruct (km_cur_loc SK B LAWS cx fpos k2 ly3 S3 md3 HB HJB) as (CU0 & CU16 & _).
  pose proof asan_consts as ((C1a & C1b) & _).
  assert (RW2 : 0 <= kW2 cx fpos /\ kW2 cx fpos + NW_N + 8 < 2 ^ 47) by (unfold kW2, KN_W2, NW_N, alloc_ceiling in *; lia).
  assert (RW1 : 0 <= kW1 cx fpos /\ kW1 cx fpos + NW_N + 8 < 2 ^ 47) by (unfold kW1, KN_W1, NW_N, alloc_ceiling in *; lia).
  assert (RFS : 0 <= kFSH cx fpos /\ kFSH cx fpos + 0x208 < 2 ^ 47) by (unfold kHighMemBeg, SHADOW_OFF in *; lia).
  assert (HN4 : NW_N = 4096) by reflexivity.
  destruct (rc_bytes SK B LAWS LV TB KI AMEMCPY AMEMSET cx fpos k2 ly3 S3 W3 ms3 md3 adv 2 HB HJ HJB HKK ltac:(lia)
              ltac:(lia) ltac:(lia)) as (d0 & d1 & Hd0 & Hd1 & Hd0v & Hd1v).
  remember (rc_E ms3 (k_wn cx - adv) (k_wp cx + adv) d0 d1 (kW1 cx fpos + NW_N) (kFSH cx fpos + 4)) as E eqn:HEdef.
  assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
  assert (HAG : YP06.env_agree 32 (Ereg (ms_regs ms3) [w64 (k_wn cx - adv); w64 (k_wp cx + adv); w64 d0; w64 d1;
                  w64 (kW1 cx fpos + NW_N); w64 (kFSH cx fpos + 4)]) E)
    by (subst E; unfold rc_E; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  destruct (rc_U SK B LAWS LV TB KI AMEMCPY AMEMSET cx fpos k2 ly3 S3 md3 ms3 ci adv d0 d1 E HB HJB HR0 HRL ltac:(lia)
              Hadv ltac:(lia) ltac:(lia) Hd0 Hd1 HEdef)
    as (U9 & U18 & U20 & U19 & U21 & U22 & U24 & U25 & U32 & U33 & U34 & U35 & U36 & U37 & U243).
  pose proof (Z.mod_pos_bound d1 16 ltac:(lia)) as Hm16.
  pose (RUN := paj_run_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  pose (RUNTO := paj_run_to_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  pose (BR := paj_branch (PI := PI)).
  assert (Hlv : sv_denot E (SOff 32 0) = Z_to_bv 64 (k_wn cx - adv)) by (apply (kr_den_off E 32 0 _ _ U32); lia).
  assert (Hla : afact_ok E 32 (mkAF 3 (2 ^ 47) 0))
    by (unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U32; change (2 ^ 0) with 1; rewrite Z.mod_1_r; lia).
  assert (Hj2 : j = 0 \/ j = 1 \/ j = 2) by lia.
  destruct Hj2 as [-> | [-> | ->]];
   (lazymatch type of HK with kat _ _ _ _ _ _ _ _ _ (Some ?jv) _ _ _ _ _ _ =>
    destruct (rc_seat SK B LAWS LV TB KI AMEMCPY AMEMSET cx fpos k2 ly3 S3 W3 ms3 md3 c ci jv adv (SOff 32 0) (mkAF 3 (2 ^ 47) 0) 2 0 d0 d1 E
                HB HJ HW HK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hd0v Hd1v Hd0 Hd1 HEdef Hlv Hla
                ltac:(vm_compute; reflexivity)) as (HS & SHOK);
    paj_run_tok RUN HS HJ SHOK kq_span;
      [ apply (rc_awr SK B LAWS LV TB KI AMEMCPY AMEMSET cx fpos k2 ly3 S3 W3 _ _ md3 _ _ HB HJ HJB);
          [ repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity
          | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity
          | rc_wr ]
        | ];
      lazymatch goal with
      | HFr1 : frame_of _ _ (mrestrict _ (ms_mem ms3)) (mrestrict _ (ms_mem ?m1)),
        HG1 : mem_grows (mrestrict _ (ms_mem ms3)) (mrestrict _ (ms_mem ?m1)) |- _ =>
        assert (HUa : forall x, 0 <= x < 2 ^ 64 -> ~ ((fun x => ka0 cx <= x < ka0 cx + 16) x) ->
                        aview SEGS (w_H W3) (ms_mem m1) x = aview SEGS (w_H W3) (ms_mem ms3) x) by rc_un HFr1 (fun x => ka0 cx <= x < ka0 cx + 16);
        rename HG1 into HGa; clear HFr1
      end;
    psrr_branch_tok RUN BR HS SHOK kq_span;
    [ rc_cond Hc; apply Z.ltb_lt in Hc; rename Hc into Hb1;
      paj_run_tok RUN HS HJ SHOK kq_span;
        [ apply (rc_awr SK B LAWS LV TB KI AMEMCPY AMEMSET cx fpos k2 ly3 S3 W3 _ _ md3 _ _ HB HJ HJB);
          [ repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity
          | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity
          | rc_wr ]
        | ];
      lazymatch goal with
      | HFr2 : frame_of _ _ (mrestrict _ (ms_mem ?m1)) (mrestrict _ (ms_mem ?m2)),
        HG2 : mem_grows (mrestrict _ (ms_mem ?m1)) (mrestrict _ (ms_mem ?m2)) |- _ =>
        let HUb := fresh "HUb" in let HGb := fresh "HGb" in
        assert (HUb : forall x, 0 <= x < 2 ^ 64 -> ~ ((fun x => ka0 cx <= x < ka0 cx + 16) x) ->
                        aview SEGS (w_H W3) (ms_mem m2) x = aview SEGS (w_H W3) (ms_mem ms3) x)
          by (apply (rd_chain W3 (ms_mem ms3) (ms_mem m1) (ms_mem m2) (fun x => ka0 cx <= x < ka0 cx + 16) HUa); rc_un HFr2 (fun x => ka0 cx <= x < ka0 cx + 16));
        pose proof (mem_grows_trans _ _ _ HGa HG2) as HGb;
        clear HUa HFr2 HG2 HGa; rename HUb into HUa; rename HGb into HGa
      end;
      psrr_branch_tok RUN BR HS SHOK kq_span;
      [ paj_run_to_tok RUNTO HS HJ SHOK kq_span (kpc 0x2074);
          [ apply (rc_awr SK B LAWS LV TB KI AMEMCPY AMEMSET cx fpos k2 ly3 S3 W3 _ _ md3 _ _ HB HJ HJB);
          [ repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity
          | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity
          | rc_wr ]
        | ];
      lazymatch goal with
      | HS' : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msn),
        HFr' : frame_of _ _ (mrestrict _ _) (mrestrict _ (ms_mem ?msn)),
        HG' : mem_grows _ (mrestrict _ (ms_mem ?msn))
        |- SRr _ _ (mkCfg ?msn ?mdn) _ =>
        let HR1 := fresh "HR1" in spregion HS' 1%nat HR1;
        let HAGx := fresh "HAGx" in
        lazymatch type of HAG with YP06.env_agree 32 ?R _ =>
          assert (HAGx : YP06.env_agree 32 R Ex) by rc_agree HAG end;
        apply (rc_land3 SK B LAWS LV TB KI AMEMCPY AMEMSET POST Rc cx fpos k2 ly3 S3 W3 ms3 md3 c ci jv adv (d0 + (d1 mod 16) * 256 + 1) msn mdn
                 HN3 HB Hfrm HJ HRcv Hcr Hci ltac:(lia) HW HK ltac:(lia) ltac:(lia) ltac:(lia));
        [ eapply (field_of_region Ex _ 18 (ka0 cx) _ _ _ _ _ 0 8%N _ (k_wp cx + (adv + 2 + (d0 + (d1 mod 16) * 256 + 1))));
            [exact HR1 | rc_ea | kn_in | apply kr_denot_of_U; rcU
            | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | change (Z.of_N 8) with 8; lia]
        | eapply (field_of_region Ex _ 18 (ka0 cx) _ _ _ _ _ 8 8%N _ (k_wn cx - (adv + 2 + (d0 + (d1 mod 16) * 256 + 1))));
            [exact HR1 | rc_ea | kn_in | apply kr_denot_of_U; rcU
            | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | change (Z.of_N 8) with 8; lia]
        | lazymatch type of HUa with forall x, _ -> _ -> aview _ _ (ms_mem ?m1) x = _ =>
            apply (rd_chain W3 (ms_mem ms3) (ms_mem m1) (ms_mem msn) (fun x => ka0 cx <= x < ka0 cx + 16) HUa); rc_un HFr' (fun x => ka0 cx <= x < ka0 cx + 16) end
        | exact (mem_grows_trans _ _ _ HGa HG')
        | apply (kn_kms_of _ Ex ssx msn 0x2074 HS'); vm_compute; reflexivity
        | exact (kregs0_keep cx ms3 msn (regs_kept_of_st_ok_pi Ex ssx _ _ _ nx_keep0 HS' HAGx
                   ltac:(vm_compute; reflexivity)) HR0)
        | unfold kregs_eq; cbn [kr_rl3 kregs_chunk app]; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
          rc_reg HS' Ex ssx msn
        | repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity
        | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity ]
      end
      | rc_cond Hc; apply Z.ltb_ge in Hc; lia ]
    | rc_cond Hc; apply Z.ltb_ge in Hc; rename Hc into Hb1;
      paj_run_tok RUN HS HJ SHOK kq_span;
        [ apply (rc_awr SK B LAWS LV TB KI AMEMCPY AMEMSET cx fpos k2 ly3 S3 W3 _ _ md3 _ _ HB HJ HJB);
          [ repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity
          | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity
          | rc_wr ]
        | ];
      lazymatch goal with
      | HFr2 : frame_of _ _ (mrestrict _ (ms_mem ?m1)) (mrestrict _ (ms_mem ?m2)),
        HG2 : mem_grows (mrestrict _ (ms_mem ?m1)) (mrestrict _ (ms_mem ?m2)) |- _ =>
        let HUb := fresh "HUb" in let HGb := fresh "HGb" in
        assert (HUb : forall x, 0 <= x < 2 ^ 64 -> ~ ((fun x => ka0 cx <= x < ka0 cx + 16) x) ->
                        aview SEGS (w_H W3) (ms_mem m2) x = aview SEGS (w_H W3) (ms_mem ms3) x)
          by (apply (rd_chain W3 (ms_mem ms3) (ms_mem m1) (ms_mem m2) (fun x => ka0 cx <= x < ka0 cx + 16) HUa); rc_un HFr2 (fun x => ka0 cx <= x < ka0 cx + 16));
        pose proof (mem_grows_trans _ _ _ HGa HG2) as HGb;
        clear HUa HFr2 HG2 HGa; rename HUb into HUa; rename HGb into HGa
      end;
      psrr_branch_tok RUN BR HS SHOK kq_span;
      [ paj_run_to_tok RUNTO HS HJ SHOK kq_span (kpc 0x2074);
          [ apply (rc_awr SK B LAWS LV TB KI AMEMCPY AMEMSET cx fpos k2 ly3 S3 W3 _ _ md3 _ _ HB HJ HJB);
          [ repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity
          | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity
          | rc_wr ]
        | ];
      lazymatch goal with
      | HS' : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msn),
        HFr' : frame_of _ _ (mrestrict _ _) (mrestrict _ (ms_mem ?msn)),
        HG' : mem_grows _ (mrestrict _ (ms_mem ?msn))
        |- SRr _ _ (mkCfg ?msn ?mdn) _ =>
        let HR1 := fresh "HR1" in spregion HS' 1%nat HR1;
        let HAGx := fresh "HAGx" in
        lazymatch type of HAG with YP06.env_agree 32 ?R _ =>
          assert (HAGx : YP06.env_agree 32 R Ex) by rc_agree HAG end;
        apply (rc_land3 SK B LAWS LV TB KI AMEMCPY AMEMSET POST Rc cx fpos k2 ly3 S3 W3 ms3 md3 c ci jv adv (k_wn cx - adv - 2) msn mdn
                 HN3 HB Hfrm HJ HRcv Hcr Hci ltac:(lia) HW HK ltac:(lia) ltac:(lia) ltac:(lia));
        [ eapply (field_of_region Ex _ 18 (ka0 cx) _ _ _ _ _ 0 8%N _ (k_wp cx + (adv + 2 + (k_wn cx - adv - 2))));
            [exact HR1 | rc_ea | kn_in | apply kr_denot_of_U; rcU
            | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | change (Z.of_N 8) with 8; lia]
        | eapply (field_of_region Ex _ 18 (ka0 cx) _ _ _ _ _ 8 8%N _ (k_wn cx - (adv + 2 + (k_wn cx - adv - 2))));
            [exact HR1 | rc_ea | kn_in | apply kr_denot_of_U; rcU
            | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | change (Z.of_N 8) with 8; lia]
        | lazymatch type of HUa with forall x, _ -> _ -> aview _ _ (ms_mem ?m1) x = _ =>
            apply (rd_chain W3 (ms_mem ms3) (ms_mem m1) (ms_mem msn) (fun x => ka0 cx <= x < ka0 cx + 16) HUa); rc_un HFr' (fun x => ka0 cx <= x < ka0 cx + 16) end
        | exact (mem_grows_trans _ _ _ HGa HG')
        | apply (kn_kms_of _ Ex ssx msn 0x2074 HS'); vm_compute; reflexivity
        | exact (kregs0_keep cx ms3 msn (regs_kept_of_st_ok_pi Ex ssx _ _ _ nx_keep0 HS' HAGx
                   ltac:(vm_compute; reflexivity)) HR0)
        | unfold kregs_eq; cbn [kr_rl3 kregs_chunk app]; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
          rc_reg HS' Ex ssx msn
        | repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity
        | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity ]
      end
      | rc_cond Hc; apply Z.ltb_ge in Hc; lia ] ]
    end).
Qed.

(* ---- kr_c2 +0x1f4c -> kr_c3 +0x2074 / kr_c7 +0x20f8 ---- *)
Theorem kr_c : forall POST Rc, kfrom SK B POST (kr_c3 B Rc) -> kfrom SK B POST (kr_c7 B Rc) ->
  kfrom SK B POST (kr_c2 B Rc).
Proof.
  intros POST Rc HN3 HN7 cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ Hfrm HI.
  destruct HI as (c & ci & j & adv & HRcv & Hcr & Hci & Hj & HW & HK).
  pose proof HK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (Hadv & _) & _).
  destruct (Z.lt_ge_cases (k_wn cx - adv) 3) as [Hl | Hl].
  - assert (Hl3 : k_wn cx - adv = 0 \/ k_wn cx - adv = 1 \/ k_wn cx - adv = 2) by lia.
    destruct Hl3 as [Hl0 | [Hl1 | Hl2]].
    + exact (rc_l0 POST Rc cx fpos k2 ly3 S3 W3 ms3 md3 c ci j adv HN3 HN7 HB HJ Hfrm HRcv Hcr Hci Hj HW HK Hl0).
    + exact (rc_l1 POST Rc cx fpos k2 ly3 S3 W3 ms3 md3 c ci j adv HN3 HN7 HB HJ Hfrm HRcv Hcr Hci Hj HW HK Hl1).
    + exact (rc_l2 POST Rc cx fpos k2 ly3 S3 W3 ms3 md3 c ci j adv HN3 HN7 HB HJ Hfrm HRcv Hcr Hci Hj HW HK Hl2).
  - exact (rc_l3 POST Rc cx fpos k2 ly3 S3 W3 ms3 md3 c ci j adv HN3 HN7 HB HJ Hfrm HRcv Hcr Hci Hj HW HK Hl).
Qed.

End b.
End a.
