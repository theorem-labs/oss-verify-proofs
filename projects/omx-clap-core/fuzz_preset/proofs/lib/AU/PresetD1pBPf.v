(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from the proof of tfib_drv_main, proofs/cgif/cgif_file_fuzzer/lib/YD1p.v
   :40-83 (its Lets: the driver's leaves) and :97-119 (its proof), for fuzz_preset's ASan image. It proves
   tfib_drv_main_B (lib/AU/PresetD1pB.v) from the leaves, which the other lanes state and prove: here every leaf is a
   Section hypothesis by its owner's statement name, so this file type-checks against the leaf STATEMENTS alone and
   tfib_drv_main_B_of_leaves takes the leaves as arguments. lib/AU/PresetD1pBPfC.v instantiates it with the owners'
   pushed theorems (tfib_drv_main_B_holds). Nothing in this file is a proof of a function (rule 24: no function
   proved; composition / driver layer of a port).
   Changes from the donor's proof:
   (1) the allocator switch: where the donor has cgif's AR at init_state (YD1p.v:100, tfib_AR), a Theorem Labs lane's
       ARcf_nil_init (lib/Reusable/YGcfNilInit.v, combine6's EXPOSE form) gives, from AR and AI at the start-up world
       W1, a wider world Wc (wle W1 Wc: class 1's shadow band exposed) with AI and ARcf at Hp = []; every leaf from
       there on is over ARcf at Wc (parent's design change, 2026-10-28 22:44Z). The start-up facts at W1 pass to Wc
       by wle (section 0: st_ok by YA0o.st_ok_wle, the runs, PINV, and the live stack by PresetStkUpB.stk_up_wle):
       each reads only bytes W1 already shows. This is the ONE start-up conversion of a8's in-place edit (2)
       (a Theorem Labs lane's note, the internal file real-edits.md);
   (1a) the room: the run-level start-up room (a8's ROOM_cf_init_k at 4 * N_LLVMF + 24, from the deleted premise
       NLB) is GONE, with every headroom number (port/resume-brief.md, design change 1); nothing is discharged from
       it. The driver's states carry only the interface's non-primary room NP := iface_room_np (owner ruling
       2026-10-29 04:5xZ): the arms take it at init_state from NPI and across their mallocs / frees from NPS, the
       sites take their one-call ROOM_cf_k S 2 from NPT; the primary room (P8's iface_room_at) is derived by the
       leaves at the loop entry (CwRunqm) and carried by the slot's post (CwLoopA);
   (1b) a8's in-place edit (1), the NULL arm of tfib_malloc_site (ml_malloc_ns_cf: malloc_cf's class-full arm
       returns PNull), is CARRIED, not assumed away: CwPreA's malloc_site_tfa_cf hands every outcome of the call,
       PNull included, to its continuation (PresetD1preB.v change (3)), and each consumer that needs a block refutes
       PNull from its own room (CwRunqm's RUNQM, CwRunqA's arms, CwPinvA's grow). This file passes MSITE through
       unchanged and adds no no-NULL premise;
   (2) the FINV handoff (YD1p.v:102, tfib_finv_handoff) is CwPinvA's PINV handoff at the start-up ledger;
   (3) the input predicate NR of tfib_drv_main_B is threaded as NR en_p, and the payload-room bridge PROOM is handed
       to the loop at it;
   (4) the LIB Let is gone: the loop takes the program interface LIBC directly (parent's ruling);
   (5) cgif's model_laws argument ML is gone from every leaf (the cf leaves cite a8's laws in their own proofs);
   (6) the post-call leaves (free sites, exit leaf) are built at every FP state, since a harness call returns at the
       callee's fx';
   (7) memnorm (the interface's header item (8), a working branch 446222ec0601; lane MnPrefix): the
       loop's named premise H_memnorm_drv_B is the THEOREM PresetD1rBmn.H_memnorm_drv_B_holds (no statement premise
       any more). Memnorm of the full overlay at main is seeded here from the start-up invariant: SINV0 ends in
       memnorm (core YA02.v SINV0_mn), and YA0j.ho_memnorm reads it at the hand-off from HC; arm_argv2 takes it (its
       statement's memnorm premise) and the prefix leaves carry it to the loop head (RUNQM and run_Q apply LOOPL).
   (8) the live real stack (the interface's header item (13), #102): the loop takes the stack above usp as its
       invariant (PresetD1rB.v header item (11)) and every prefix leaf carries it from main (lane StackDrv). It is
       seeded here at main's entry by H_stackup_main_B (lib/AU/PresetD1pB.v section 3, a Section hypothesis here like
       every leaf; lib/AU/PresetD1pBPfC.v proves it by stack_up_main_W1_B), at the start-up world W1 and YD1g.ly0, whose
       top is page aligned (layout_ok) and within top_ok of usp (YD1f.tfib_top_ok);
   a8's malloc_cf_keeps_pristine_except is a theorem (YGcfPristine.v:381), so no leaf takes it as a premise any more
   (CwRunqA 508a56e69bef). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Shapes.
From OSSVerify.omx_clap_core.fuzz_preset Require Images.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import AsanUbsan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK15 YK18 YK0c YK0e YK09 YA0c YA0e YA01 YA02 YA00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB12 YB1h YB01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK00 YK0s YP0n YM02 YP0m YP09 YP0l YP06 YP08 YP03 YN3q YN3v YK04 YA0i YA0n YA0o YA0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0k YG0f YG0v YG0n YG0d YCe5 YL02 YG08.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YF0l YF0m YD2j YD1t YD20 YD1v YD2h YD2f YD1w YD1x YCeg YD1i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YD1g YD1f YD2i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0j YAkMemnorm YGcfMallocComposeKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallStackUp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PresetStkUpB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG0ncf YG0dcf YG0d2cf YGcfRoomPre YGcfNilInit YG0lawscf YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import PresetCfnB PresetD1pB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import PresetD1sitesB PresetD1preB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PresetD1rB PresetD1rBmn PresetD2eB PresetD2runB PresetD2runQB PresetPinvB PresetPinvBcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PWorldH8 CfAroPresetB.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Import AX2. Import AX2S. Import APG. Import APSG.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.
#[local] Existing Instance CfImg_B.

(* ---------------------------------------------------------------------- *)
(* 0. The start-up facts at W1 pass to a wider world (wle: a subset hidden), header item (1). *)
Lemma runs_at_wle_drv : forall (W W' : world tfibsegs) spv m l,
  wle W W' -> runs_at spv (mrestrict (w_H W) m) l -> runs_at spv (mrestrict (w_H W') m) l.
Proof.
intros W W' spv m l Hs HR. unfold runs_at, bytes_at in *. eapply Forall_impl; [|exact HR].
intros [a bs] (X1 & X2 & X3). cbn [fst snd] in *. split; [exact X1|]. split; [exact X2|].
intros j Hj. pose proof (X3 j Hj) as Xj. rewrite <- Xj.
assert (NN : nth_error bs j <> None) by (apply nth_error_Some; exact Hj).
destruct (mrestrict (w_H W) m (Z_to_bv 64 (a + Z.of_nat j))) as [b|] eqn:Eb; [|congruence].
eapply mrestrict_hsub; [exact Hs | exact Eb].
Qed.
Lemma pinv_wle_drv : forall (W W' : world tfibsegs) mem cnt ran,
  wle W W' -> PINV (aview tfibsegs (w_H W) mem) cnt ran -> PINV (aview tfibsegs (w_H W') mem) cnt ran.
Proof.
intros W W' mem cnt ran Hs HP.
pose proof (aview_ext tfibsegs (w_H W) (w_H W') mem (w_Hoff W) Hs) as X.
set (rd := aview tfibsegs (w_H W) mem) in *. set (rd' := aview tfibsegs (w_H W') mem) in *.
assert (K : forall a n v, (forall k, (k < n)%nat -> rd (a + Z.of_nat k) = Some (le_byte v n k)) ->
  forall k, (k < n)%nat -> rd' (a + Z.of_nat k) = Some (le_byte v n k)) by (intros a n v Hr k Hk; apply X, Hr, Hk).
destruct HP as ((L1 & (pk & Pk & L2) & C1 & L3 & L4 & R1 & L5 & (mo & Mo & L6) & (o & Oo & L7)) & (S1 & S2 & S3 & S4)).
unfold rd64, rd32, rd8 in *.
split; [|split; [apply X, S1 | split; [apply X, S2 | split; [exact (K _ _ _ S3) | exact (K _ _ _ S4)]]]].
split; [exact (K _ _ _ L1)|]. split; [exists pk; split; [exact Pk | exact (K _ _ _ L2)]|].
split; [exact C1|]. split; [exact (K _ _ _ L3)|]. split; [exact (K _ _ _ L4)|]. split; [exact R1|].
split; [exact (K _ _ _ L5)|]. split; [exists mo; split; [exact Mo | exact (K _ _ _ L6)]|].
exists o. split; [exact Oo | exact (K _ _ _ L7)].
Qed.

Section pf.
(* ---------------------------------------------------------------------- *)
(* 1. The leaves, by their owners' statement names (each a closed Prop). *)
(* CwPreA (lib/AU/PresetD1preB.v): YD1n.v:25, YD1i.v:106 / :112, YD27.v:405 / :411 / :465 / :568 / :862 / :870. *)
Hypothesis Hmalloc_site : PresetD1preB.tfib_malloc_site_cf_B.
Hypothesis Hmemcpy_site : PresetD1preB.tfib_memcpy_site_cf_B.
Hypothesis Hread_check : PresetD1preB.tfib_read_check_cf_B.
Hypothesis Hrderr_leaf : PresetD1preB.tfib_rderr_leaf_cf_B.
Hypothesis Hrefused_leaf : PresetD1preB.tfib_refused_leaf_cf_B.
Hypothesis Hcannot_open : PresetD1preB.tfib_cannot_open_cf_B.
Hypothesis Husage : PresetD1preB.tfib_usage_cf_B.
Hypothesis Hshort_leaf : PresetD1preB.tfib_short_leaf_cf_B.
Hypothesis Hoverrun_leaf : PresetD1preB.tfib_overrun_leaf_cf_B.
(* CwSites (lib/AU/PresetD1sitesB.v): YD1i.v:62 / :79, YD27.v:672. *)
Hypothesis Hfree_site : PresetD1sitesB.free_site_cf_B.
Hypothesis Hfree_null_site : PresetD1sitesB.free_null_site_cf_B.
(* the same two sites over drv_pre_cf without memnorm, for the short / overrun leaves' free after the fwrite diagnostic
   and the exit path's frees after the last harness call (the driver carries no memnorm there) *)
Hypothesis Hfree_nomn_site : PresetD1sitesB.free_site_nomn_cf_B.
Hypothesis Hfree_null_nomn_site : PresetD1sitesB.free_null_site_nomn_cf_B.
Hypothesis Hexit_leaf : PresetD1sitesB.exit_leaf_cf_B.
(* CwLoopA (lib/AU/PresetD1rB.v): YD1r.v:1054 tfib_loop_L. *)
Hypothesis Hloop_L_x : PresetD1rB.loop_L_x_B.
(* CwRunqm (lib/AU/PresetD2eB.v): YD2e.v:655 tfib_run_QM. *)
Hypothesis Hrunqm : PresetD2eB.runqm_cf_B.
(* CwRunqA (lib/AU/PresetD2runQB.v, PresetD2runB.v): YD2d.v:388, YD2c.v:159, YD2g.v:235, YD22.v:45, YD1z.v:479,
   YD26.v:320 / :326. *)
Hypothesis Hrun_Q : PresetD2runQB.tfib_run_Q_cf_B.
Hypothesis Hpost_P : PresetD2runB.tfib_post_P_cf_B.
Hypothesis Hhdr : PresetD2runB.tfib_hdr_cf_B.
Hypothesis Hrd0_dir : PresetD2runB.tfib_rd0_dir_cf_B.
Hypothesis Hrd0_file : PresetD2runB.tfib_rd0_file_cf_B.
Hypothesis Hfile_arm : PresetD2runB.tfib_file_arm_cf_B.
Hypothesis Hdir_arm : PresetD2runB.tfib_dir_arm_cf_B.
(* CwPinvA (lib/AU/PresetPinvB.v, PresetPinvBcf.v): YD2k.v:113 tfib_finv_handoff, YD2a.v:386 tfib_arm_argv2, and the
   three PINV frame results RUNQM takes. *)
Hypothesis Hhandoff : PresetPinvB.tfib_finv_handoff_pinv_B.
Hypothesis Harm_argv2 : PresetPinvBcf.tfib_arm_argv2_cf_B.
Hypothesis Hfinv_run : PresetPinvB.finv_run_pinv_B.
Hypothesis Hfinv_site : PresetPinvB.finv_site_pinv_B.
Hypothesis Hfinv_icpt : PresetPinvB.finv_icpt_pinv_B.
(* the main-entry presence premise H_stackup_main_B (lib/AU/PresetD1pB.v section 3): every byte of [usp - 64 KiB,
   ly_top) is present at main's entry. Proved by stack_up_main_W1_B (lib/AU/PresetD1pBPfC.v H_stackup_main_B_holds). *)
Hypothesis H_stackup_main_B : PresetD1pB.H_stackup_main_B.
(* the allocator switch's start-up premises (lib/AU/PresetD1pB.v section 4), by name: the init model's lazy maps, the
   two start witnesses (supplied by: start-up rows (the kit owner)) and the two image rows (supplied by: image rows (a Theorem Labs lane)) *)
Hypothesis H_start_lazy_B : PresetD1pB.H_start_lazy_B.
Hypothesis H_start_cells_B : PresetD1pB.H_start_cells_B.
Hypothesis H_start_pf_B : PresetD1pB.H_start_pf_B.
Hypothesis H_errb_rows_B : PresetD1pB.H_errb_rows_B.
Hypothesis H_pf_rows_B : PresetD1pB.H_pf_rows_B.

(* ---------------------------------------------------------------------- *)
(* 2. The driver walk. Donor: YD1p.v:97-119. *)
Theorem tfib_drv_main_B_of_leaves : tfib_drv_main_B.
Proof.
intros rc L PA sm NP NPI NPS NPT B HB AMALLOC AFREE AICPY ARDCHK
MT XM_LIB XN_LIB MT_FREE RO_IN PAYLOAD_ROOM NR PROOM LIBC UNIV HWMAX HSIG xst XFR PF1 PFN est ESTI ESTF FWS RFS FPO FPR FPU EXS.
intros sp rdraw brk inp en_p h ch E R FULL model Hsp Hbrk Hfit Hinp HNR Hceil Hch HC HE HM.
pose proof Hinp as (Hva & Hve & Hvfs & _).
set (LS := ZTraceSpec.checksum_shape).
(* the input predicate at this entry, which the leaves on the file arm carry, and the payload-room bridge at it *)
set (NRp := NR en_p).
assert (PBR : forall i a0 p data, NRp i -> in_argv i = [a0; p] -> fs_lookup (in_fs i) p = Some data -> PAYLOAD_ROOM (payload data))
  by (intros i a0 p data Hi; exact (PROOM en_p i a0 p data Hi)).
(* a8's laws *)
pose proof (AR_laws_ok_cf (cp := CfParams_preset) tfibsegs B) as ARL.
(* the leaves: the donor's Lets, in its order *)
(* drv_pre_cf's two links at the instance (PresetD1sitesB.v section 1): the hull field at CfParams_preset is itself,
   and the reader form of the read-only bytes gives arodata_ok_cf at CfImg_B (CfAroPresetB.v) *)
assert (HLINK : drv_hull_link (cp := CfParams_preset)) by (intros S0 H0; exact H0).
assert (ALINK : drv_aro_link (ci := CfImg_B) B)
  by (intros W0 m0 H0; exact (CfAroPresetB.arodata_ok_cf_preset_AU B W0 m0 HB H0)).
pose proof (Hmalloc_site YK11.fx0 rc CfImg_B CfParams_preset B NP NPT HLINK ALINK AMALLOC) as MSITE.
pose proof (Hread_check YK11.fx0 rc CfImg_B CfParams_preset B ARDCHK) as RCHK.
pose proof (Hmemcpy_site YK11.fx0 rc CfImg_B CfParams_preset B AICPY) as MCPY.
pose proof (fun fx => Hfree_site fx rc CfImg_B CfParams_preset B NP NPT NPS HLINK ALINK (AFREE fx)) as FREE.
pose proof (fun fx => Hfree_null_site fx rc CfImg_B CfParams_preset B NP NPT NPS HLINK ALINK
  (YGcfMallocComposeKeep.afree_realizes_cf_rh_of_keep tfibsegs B (AFREE fx))) as FREEN.
pose proof (Hrderr_leaf YK11.fx0 rc CfImg_B CfParams_preset B xst est HB XFR ESTF FPR (EXS YK11.fx0)) as RDERR.
pose proof (Hrefused_leaf YK11.fx0 rc CfImg_B CfParams_preset B xst est HB XFR ESTF RFS (EXS YK11.fx0)) as REFUSED.
pose proof (fun fx => conj (Hfree_nomn_site fx rc CfImg_B CfParams_preset B NP NPT NPS HLINK ALINK (AFREE fx))
  (Hfree_null_nomn_site fx rc CfImg_B CfParams_preset B NP NPT NPS HLINK ALINK
    (YGcfMallocComposeKeep.afree_realizes_cf_rh_of_keep tfibsegs B (AFREE fx)))) as FREE_NOMN.
pose proof (Hshort_leaf YK11.fx0 rc CfImg_B CfParams_preset B NP xst est HB XFR ESTF FWS (EXS YK11.fx0)
  (proj1 (FREE_NOMN YK11.fx0))) as SHORT.
pose proof (Hoverrun_leaf YK11.fx0 rc CfImg_B CfParams_preset B NP xst est HB XFR ESTF FWS (EXS YK11.fx0)
  (proj1 (FREE_NOMN YK11.fx0))) as OVERRUN.
pose proof (fun fx => Hexit_leaf fx rc CfImg_B CfParams_preset B xst est HB XFR ESTI ESTF (EXS fx)) as EXITL.
pose proof (Hcannot_open YK11.fx0 rc CfImg_B CfParams_preset B xst est HB XFR ESTF FPO (EXS YK11.fx0)) as HCO.
pose proof (Husage YK11.fx0 rc CfImg_B CfParams_preset B xst est HB XFR ESTF FPU (EXS YK11.fx0)) as USAGE.
(* the loop's named premise H_memnorm_drv_B is a theorem (lane MnPrefix, lib/AU/PresetD1rBmn.v) *)
pose proof (Hloop_L_x rc LS CfImg_B L PA B xst NRp sm NP MT XM_LIB XN_LIB PAYLOAD_ROOM
  HB ARL MT_FREE RO_IN PBR LIBC UNIV HSIG PF1 PFN (fun fx => proj1 (FREE_NOMN fx)) (fun fx => proj2 (FREE_NOMN fx))
  EXITL XFR NPT PresetD1rBmn.H_memnorm_drv_B_holds) as LOOPL.
pose proof (Hrunqm YK11.fx0 rc LS CfImg_B B NRp xst NP sm NPT NPS Hfinv_run Hfinv_site Hfinv_icpt
  YK0o.fp_frm_zero_fx0 HB MSITE MCPY LOOPL HWMAX) as RUNQM.
pose proof (Hrun_Q YK11.fx0 rc LS CfImg_B B NP xst NRp sm YK0o.fp_frm_zero_fx0 HB LOOPL HWMAX RUNQM) as RUNQ.
pose proof (Hpost_P YK11.fx0 rc LS CfImg_B CfParams_preset B NP NRp HB RUNQ) as POSTP.
pose proof (Hhdr YK11.fx0 rc LS CfImg_B CfParams_preset B NP NRp HB SHORT OVERRUN POSTP) as HDR.
pose proof (Hrd0_dir YK11.fx0 rc LS CfImg_B CfParams_preset B NP HB RDERR) as RDD.
(* the read loop's grows request at most 2 ^ 26 bytes; preset's malloc ceiling is 2 ^ 29 - 2 ^ 20 (CfParamsPreset.v) *)
assert (HMAX : 2 ^ 26 < @cf_malloc_max CfParams_preset) by (vm_compute; reflexivity).
pose proof (Hrd0_file YK11.fx0 rc LS CfImg_B CfParams_preset B NP NRp HB NPS NPT HMAX MSITE RCHK MCPY (FREE YK11.fx0) REFUSED HDR) as RDF.
(* the arms carry the non-primary room from init_state by the interface's PROVISIONAL laws NPI / NPS *)
pose proof (Hfile_arm YK11.fx0 rc LS CfImg_B CfParams_preset B NP NRp HB NPI NPS MSITE RDF) as HFILE.
pose proof (Hdir_arm YK11.fx0 rc LS CfImg_B CfParams_preset B NP HB NPI NPS MSITE RDD) as HDIR.
(* the walk, as the donor's *)
(* the W8 core's w_H8 proof of the start-up world W1 (as the core's own callers pass it) *)
pose (H8 := PWorldH8.H1_H8 sp rdraw brk inp Hsp Hva Hve Hfit h ch E R FULL model Hch HC).
pose proof (tfib_main_entry sp rdraw brk inp Hsp Hva Hve Hfit h ch E R FULL model Hch HC HE HM
  (sliver_allowed sp rdraw brk inp Hsp Hva Hve Hfit h ch E R FULL model Hch HC Hceil) H8) as (Hpc & HST & HAI & Hfs & Hfds & _).
set (ly := YD1g.ly0 ch E model).
assert (HAR : AR TSEGS B ly init_state (YD2i.W1 sp rdraw inp Hsp Hva ch E model H8) FULL model) by (eapply (tfib_AR B HB); eassumption).
(* the allocator switch (a8's YGcfNilInit.v ARcf_nil_init, combine6's EXPOSE form), once, at the allocator's initial
   state: the start-up world W1 widens to Wc (class 1's band exposed), where AI and ARcf hold *)
destruct (ARcf_nil_init (cp := CfParams_preset) tfibsegs B ly
  (YD2i.W1 sp rdraw inp Hsp Hva ch E model H8) FULL model HAR HAI
  (H_start_lazy_B sp rdraw brk inp h ch E R FULL model Hch HC)
  (H_start_cells_B rc sp rdraw brk inp Hsp Hva h ch E R FULL model Hch HC H8 B HB)
  (H_start_pf_B rc sp rdraw brk inp Hsp Hva h ch E R FULL model Hch HC H8 B HB)
  (H_errb_rows_B B HB) (H_pf_rows_B B HB)) as (Wc & HWle & HAIc & HARc).
assert (HTOP : YD1v.top_ok (bv_unsigned sp) ly) by (eapply tfib_top_ok; eassumption).
(* #102 (lane StackDrv): the live real stack above usp at main, from H_stackup_main_B at the start-up world W1 and
   ly (its top page aligned by layout_ok, within top_ok of usp) *)
assert (HUP0 : YGcallStackUp.astack_up_x tfibsegs ly (YD2i.W1 sp rdraw inp Hsp Hva ch E model H8) (bv_unsigned sp) FULL).
{ pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR))) as (_ & _ & HPA & _). unfold YG0f.page_aligned in HPA.
  intros a Ha.
  exact (H_stackup_main_B rc sp rdraw brk inp Hsp Hva Hve Hfit h ch E R FULL model Hch HC HE HM H8 ly HPA HTOP a ltac:(lia)). }
pose proof (PresetStkUpB.stk_up_wle ly _ Wc FULL (bv_unsigned sp) HWle HUP0) as HUPc.
pose proof (Hhandoff YK11.fx0 rc sp rdraw brk inp Hsp Hva h ch E R FULL model H8 Hch HC) as HPI.
pose proof (pinv_wle_drv _ Wc FULL 0 0 HWle HPI) as HPIc.
(* memnorm of the full overlay at main: the start-up invariant SINV0 carries it (core YA02.v SINV0_mn), read at the
   hand-off by YA0j.ho_memnorm from HC (lib/Reusable/YjMemnormMainB.v's route, in the YAkMemnorm form directly) *)
assert (HMN0 : YAkMemnorm.memnorm AsanUbsan.M.loaded_segments FULL).
{ eapply YA0j.ho_memnorm;
    [exact (YA02.SINV0_mn AsanUbsan.M.loaded_segments AsanUbsan.M.phdrs sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
    | exact HC]. }
rewrite Hpc. change (cfg_of AsanUbsan.M.loaded_segments R TFIB_MAIN FULL model) with (mkCfg (mkst R (Z_to_bv 64 TFIB_MAIN) FULL (seg_rom tfibsegs)) model).
change TSEGS with tfibsegs in HST, HAI |- *. unfold CLOSEDX.
destruct (Nat.eq_dec (length (in_argv inp)) 2) as [Hlen|Hlen].
- assert (Hargv : exists a0 p, in_argv inp = [a0; p]).
  { clear -Hlen. destruct (in_argv inp) as [|a0 [|p [|x r]]]; try (cbn in Hlen; lia). exists a0, p. reflexivity. }
  destruct Hargv as (a0 & p & Hargv).
  destruct (HST true ltac:(unfold two_ok; rewrite Hargv; cbn; lia)) as [HS HR].
  pose proof (st_ok_wle tfibsegs _ Wc _ _ _ HWle HS) as HSc. pose proof (runs_at_wle_drv _ Wc _ _ _ HWle HR) as HRc.
  replace (CLOSEDX_args (in_argv inp) (in_fs inp)) with (CLOSEDX_args [a0; p] (in_fs inp)) by (rewrite Hargv; reflexivity).
  exact (Harm_argv2 YK11.fx0 rc LS CfImg_B CfParams_preset B NRp HB HCO HFILE HDIR sp inp (xwE E R) (xdE inp)
    Wc (mkst R (Z_to_bv 64 TFIB_MAIN) FULL (seg_rom tfibsegs)) model ly a0 p
    Hargv Hsp Hva Hve Hfit Hvfs HNR HSc HRc HAIc HARc HTOP HPIc HMN0 HUPc Hfs Hfds).
- destruct (HST false I) as [HS HR].
  pose proof (st_ok_wle tfibsegs _ Wc _ _ _ HWle HS) as HSc. pose proof (runs_at_wle_drv _ Wc _ _ _ HWle HR) as HRc.
  replace (CLOSEDX_args (in_argv inp) (in_fs inp)) with (diag (msg_usage (nth 0 (in_argv inp) [])) (in_fs inp)).
  2:{ clear -Hlen. unfold CLOSEDX_args. destruct (in_argv inp) as [|x [|y [|z r]]]; try reflexivity. cbn in Hlen. lia. }
  exact (USAGE sp inp (xwE E R) (xdE inp) Wc
    (mkst R (Z_to_bv 64 TFIB_MAIN) FULL (seg_rom tfibsegs)) model ly Hsp Hva Hve Hfit Hlen HSc HRc HAIc HARc HTOP Hfs Hfds).
Qed.
End pf.
