(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: tfib_drv_main_B_holds, the driver walk of fuzz_preset's ASan image (lib/AU/PresetD1pB.v),
   from the composition lib/AU/PresetD1pBPf.v (tfib_drv_main_B_of_leaves) and the leaf THEOREMS their owners pushed,
   cited by name (parent's order 2026-10-29 05:5xZ: a pushed theorem is cited, never kept as a hypothesis).
   Nothing in this file is a proof of a function (rule 24: no function proved; composition / driver layer of a port).
   MEMNORM (lane MnPrefix, a Theorem Labs lane, 2026-10-29): the prefix leaves (arm_argv2, file_arm, rd0_file with the read loop
   and gr_grow, hdr, post_P, run_Q, RUNQM) take memnorm of the full overlay at entry and keep it across their runner
   segments (lib/Reusable/YD2mnSeg.v twins of the core segments, in-place re-runs of the lane segments) and call sites (the
   malloc / free leaves' keep, memcpy's AICPY in the keep form, the read check's keep in ARDCHK); the composition
   seeds it at main from SINV0 (PresetD1pBPf.v) and the loop's named premise H_memnorm_drv_B is a theorem
   (lib/AU/PresetD1rBmn.v). rd0_dir / rd0_file are cited from lib/AU/PresetD2runBRd0mnPf.v, the memnorm twin of
   WalkMain's lib/AU/PresetD2runBRd0Pf.v (which proves the earlier statements).
   THE LIVE REAL STACK (#102; the interface's header item (13)): the prefix leaves and the loop carry the stack above
   usp from main's entry to each harness call (lane StackDrv); at main it is PresetD1pB.H_stackup_main_B, PROVED here
   (H_stackup_main_B_holds) by the start-up lane's stack_up_main_W1_B (lib/AU/Prog/StackUpMainB.v, over the kit's argH0,
   a working branch 87cf0d0d06f6).
   THE ALLOCATOR SWITCH'S START-UP PREMISES (cf layer field rounds 2-3; lib/AU/PresetD1pB.v section 4): the two image
   rows H_errb_rows_B / H_pf_rows_B are PROVED here (H_errb_rows_B_holds / H_pf_rows_B_holds) from the image's rows
   at CfImg_B (lib/A/CfIalApartPreset.v); the three start-up rows H_start_lazy_B / H_start_cells_B / H_start_pf_B are
   PROVED here (H_start_lazy_B_holds / H_start_cells_B_holds / H_start_pf_B_holds) from the B start-up table
   (lib/Reusable/YB01.v) and CfImg_B (lib/AU/CfImgB.v) by lib/AU/PresetStartRowsB.v; tfib_drv_main_B_holds carries none.
   CITED (lane, branch sha, file):
     CwPreA  a working branch  f26d81679efe  lib/AU/PresetD1preBPf.v   (the nine pre-loop sites and leaves)
     CwSites a working branch c5750d597271  lib/AU/PresetD1sitesBPf.v (free_site, free_null_site, exit_leaf)
     CwLoopA a working branch (this branch)  lib/AU/PresetD1rBPf.v (loop_L_x_B on the memnorm interface;
                                                        led_L closed by vm_compute on the ledger-cut YD2j)
     CwRunqm a working branch f43397621393  lib/AU/PresetD2eBPf.v     (runqm_cf_B; the proof moved byte for
                                                        byte out of lib/AU/PresetD2eB.v on a working branch)
     CwRunqA a working branch 8608f6e0e524  lib/AU/PresetD2runQBPf.v (run_Q), PresetD2runBPfQ.v (post_P),
                                                        PresetD2runBPfH.v (hdr), PresetD2runBPfM.v (file_arm, dir_arm)
     CwPinvA a working branch f50b650085f0  lib/AU/PresetPinvBPf.v (handoff, finv_run / _site / _icpt),
                                                        lib/AU/PresetPinvB2aPf.v (arm_argv2)
     MnPrefix a working branch             lib/AU/PresetD2runBRd0mnPf.v (rd0_dir, rd0_file: the memnorm
                                                        twin of WalkMain's lib/AU/PresetD2runBRd0Pf.v, a Theorem Labs lane) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PresetD1pB PresetD1pBPf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PresetD1rB PresetD1rBPf PresetD2eB PresetD2eBPf PresetD2runB PresetD2runQB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PresetD1preBPf PresetD1sitesBPf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PresetD2runQBPf PresetD2runBPfQ PresetD2runBPfH PresetD2runBPfM.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PresetPinvB PresetPinvBPf PresetPinvB2aPf PresetD2runBRd0mnPf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YK11.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.Prog Require StackUpMainB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfIalApartPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PresetStartRowsB.

(* A cited theorem proved under CwPinvA's frame results (its file's Section hypotheses): apply it to CwPinvA's
   theorems, whichever of the three it takes. *)
Ltac cite_pinv H :=
  repeat match type of H with
  | ?A -> _ =>
      let X := fresh "X" in
      assert (X : A) by first [ exact PresetPinvBPf.finv_run_pinv_B_holds | exact PresetPinvBPf.finv_site_pinv_B_holds
                              | exact PresetPinvBPf.finv_icpt_pinv_B_holds ];
      specialize (H X); clear X
  end.

(* THE MAIN-ENTRY PRESENCE (lib/AU/PresetD1pB.v section 3): the start-up lane's stack_up_main_W1_B at the driver's
   binders *)
Section stackup.
#[local] Existing Instance YK11.fx0.
Theorem H_stackup_main_B_holds : PresetD1pB.H_stackup_main_B.
Proof.
intros rc sp rdraw brk inp Hsp Hva Hve Hfit h ch E R FULL model Hch HC HE HM H1_8 ly Hal Htop a Ha.
eapply StackUpMainB.stack_up_main_W1_B; eassumption.
Qed.
End stackup.

(* THE IMAGE ROWS (lib/AU/PresetD1pB.v section 4) at CfImg_B: EXH_OFF_t, errb_obj_owned_t, errb_ial_apart_t and
   pf_cells_owned_t from the image's rows (lib/A/CfIalApartPreset.v) *)
Theorem H_errb_rows_B_holds : PresetD1pB.H_errb_rows_B.
Proof.
intros B HB. exact (conj CfIalApartPreset.exh_off_B
  (conj (CfIalApartPreset.errb_obj_owned_B B HB) (CfIalApartPreset.errb_ial_apart_B B HB))).
Qed.
Theorem H_pf_rows_B_holds : PresetD1pB.H_pf_rows_B.
Proof. intros B HB. exact (CfIalApartPreset.pf_cells_owned_B B HB). Qed.

(* THE START-UP ROWS (lib/AU/PresetD1pB.v section 4): the init model's lazy maps, the start witness of the two machine
   cells and the start witness of Printf's two cells, from the B start-up table and CfImg_B
   (lib/AU/PresetStartRowsB.v) *)
Theorem H_start_lazy_B_holds : PresetD1pB.H_start_lazy_B.
Proof. exact PresetStartRowsB.start_lazy_B. Qed.
Theorem H_start_cells_B_holds : PresetD1pB.H_start_cells_B.
Proof. exact PresetStartRowsB.start_cells_B. Qed.
Theorem H_start_pf_B_holds : PresetD1pB.H_start_pf_B.
Proof. exact PresetStartRowsB.start_pf_B. Qed.

Theorem tfib_drv_main_B_holds : PresetD1pB.tfib_drv_main_B.
Proof.
pose proof PresetD1rBPf.loop_L_x_B_holds as Hloop_L_x. cite_pinv Hloop_L_x.
pose proof PresetD2eBPf.runqm_cf_B_holds as Hrunqm. cite_pinv Hrunqm.
pose proof PresetD2runQBPf.tfib_run_Q_cf_B_holds as Hrun_Q. cite_pinv Hrun_Q.
pose proof PresetD2runBPfQ.tfib_post_P_cf_B_holds as Hpost_P. cite_pinv Hpost_P.
pose proof PresetD2runBPfH.tfib_hdr_cf_B_holds as Hhdr. cite_pinv Hhdr.
pose proof PresetD2runBPfM.tfib_file_arm_cf_B_holds as Hfile_arm. cite_pinv Hfile_arm.
pose proof PresetD2runBPfM.tfib_dir_arm_cf_B_holds as Hdir_arm. cite_pinv Hdir_arm.
pose proof PresetD2runBRd0mnPf.tfib_rd0_dir_cf_B_holds as Hrd0_dir. cite_pinv Hrd0_dir.
pose proof PresetD2runBRd0mnPf.tfib_rd0_file_cf_B_holds as Hrd0_file. cite_pinv Hrd0_file.
exact (PresetD1pBPf.tfib_drv_main_B_of_leaves
  PresetD1preBPf.tfib_malloc_site_cf_B_holds PresetD1preBPf.tfib_memcpy_site_cf_B_holds
  PresetD1preBPf.tfib_read_check_cf_B_holds PresetD1preBPf.tfib_rderr_leaf_cf_B_holds
  PresetD1preBPf.tfib_refused_leaf_cf_B_holds PresetD1preBPf.tfib_cannot_open_cf_B_holds
  PresetD1preBPf.tfib_usage_cf_B_holds PresetD1preBPf.tfib_short_leaf_cf_B_holds
  PresetD1preBPf.tfib_overrun_leaf_cf_B_holds
  PresetD1sitesBPf.free_site_cf_B_holds PresetD1sitesBPf.free_null_site_cf_B_holds
  PresetD1sitesBPf.free_site_nomn_cf_B_holds PresetD1sitesBPf.free_null_site_nomn_cf_B_holds
  PresetD1sitesBPf.exit_leaf_cf_B_holds
  Hloop_L_x Hrunqm Hrun_Q Hpost_P Hhdr Hrd0_dir Hrd0_file Hfile_arm Hdir_arm
  PresetPinvBPf.tfib_finv_handoff_pinv_B_holds PresetPinvB2aPf.tfib_arm_argv2_cf_B_holds
  PresetPinvBPf.finv_run_pinv_B_holds PresetPinvBPf.finv_site_pinv_B_holds PresetPinvBPf.finv_icpt_pinv_B_holds
  H_stackup_main_B_holds H_start_lazy_B_holds H_start_cells_B_holds H_start_pf_B_holds H_errb_rows_B_holds
  H_pf_rows_B_holds).
Qed.

Print Assumptions tfib_drv_main_B_holds.
Print Assumptions H_start_lazy_B_holds.
Print Assumptions H_start_cells_B_holds.
Print Assumptions H_start_pf_B_holds.
