(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: tfib_drv_main_A_holds, the driver walk of fuzz_preset's ASan image (lib/A/PresetD1pA.v),
   from the composition lib/A/PresetD1pAPf.v (tfib_drv_main_A_of_leaves) and the leaf THEOREMS their owners pushed,
   cited by name (parent's order 2026-10-29 05:5xZ: a pushed theorem is cited, never kept as a hypothesis).
   Nothing in this file is a proof of a function (rule 24: no function proved; composition / driver layer of a port).
   MEMNORM (lane MnPrefix, a Theorem Labs lane, 2026-10-29): the prefix leaves (arm_argv2, file_arm, rd0_file with the read loop
   and gr_grow, hdr, post_P, run_Q, RUNQM) take memnorm of the full overlay at entry and keep it across their runner
   segments (lib/A/AD2mnSeg.v twins of the core segments, in-place re-runs of the lane segments) and call sites (the
   malloc / free leaves' keep, memcpy's AICPY in the keep form, the read check's keep in ARDCHK); the composition
   seeds it at main from SINV0 (PresetD1pAPf.v) and the loop's named premise H_memnorm_drv_A is a theorem
   (lib/A/PresetD1rAmn.v). rd0_dir / rd0_file are cited from lib/A/PresetD2runARd0mnPf.v, the memnorm twin of
   WalkMain's lib/A/PresetD2runARd0Pf.v (which proves the earlier statements).
   THE LIVE REAL STACK (#102; the interface's header item (13)): the prefix leaves and the loop carry the stack above
   usp from main's entry to each harness call (lane StackDrv); at main it is PresetD1pA.H_stackup_main_A, PROVED here
   (H_stackup_main_A_holds) by the start-up lane's stack_up_main_W1_A (lib/A/Prog/StackUpMainA.v, over the kit's argH0,
   a working branch 87cf0d0d06f6).
   THE ALLOCATOR SWITCH'S START-UP PREMISES (cf layer field rounds 2-3; lib/A/PresetD1pA.v section 4): the two image
   rows H_errb_rows_A / H_pf_rows_A are PROVED here (H_errb_rows_A_holds / H_pf_rows_A_holds) from the image's rows
   at CfImg_A (lib/A/CfIalApartPreset.v); the three start-up rows H_start_lazy_A / H_start_cells_A / H_start_pf_A are
   PROVED here (H_start_lazy_A_holds / H_start_cells_A_holds / H_start_pf_A_holds) from the kit's start-up facts at the
   driver's binders: the lazy maps from cs_ok's field co_lzsub (lib/Reusable/YCsokLazyMaps.v cs_ok_lazy_in_maps_cf),
   the two machine cells and Printf's two cells from the 50 hand-off states of lib/A/AB01.v (lib/A/AD2iExhErrb.v
   main_exh_errb_cells_A with YGcfInstBase.exh_cell_cf_init / errb_cells_cf_init; lib/A/AD2iPfCells.v
   main_pf_cells_A). So tfib_drv_main_A_holds has no start-up premise left.
   CITED (lane, branch sha, file):
     CwPreA  a working branch  f26d81679efe  lib/A/PresetD1preAPf.v   (the nine pre-loop sites and leaves)
     CwSites a working branch c5750d597271  lib/A/PresetD1sitesAPf.v (free_site, free_null_site, exit_leaf)
     CwLoopA a working branch (this branch)  lib/A/PresetD1rAPf.v (loop_L_x_A on the memnorm interface;
                                                        led_L closed by vm_compute on the ledger-cut AD2j)
     CwRunqm a working branch f43397621393  lib/A/PresetD2eAPf.v     (runqm_cf_A; the proof moved byte for
                                                        byte out of lib/A/PresetD2eA.v on a working branch)
     CwRunqA a working branch 8608f6e0e524  lib/A/PresetD2runQAPf.v (run_Q), PresetD2runAPfQ.v (post_P),
                                                        PresetD2runAPfH.v (hdr), PresetD2runAPfM.v (file_arm, dir_arm)
     CwPinvA a working branch f50b650085f0  lib/A/PresetPinvAPf.v (handoff, finv_run / _site / _icpt),
                                                        lib/A/PresetPinvA2aPf.v (arm_argv2)
     MnPrefix a working branch             lib/A/PresetD2runARd0mnPf.v (rd0_dir, rd0_file: the memnorm
                                                        twin of WalkMain's lib/A/PresetD2runARd0Pf.v, a Theorem Labs lane) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetD1pA PresetD1pAPf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetD1rA PresetD1rAPf PresetD2eA PresetD2eAPf PresetD2runA PresetD2runQA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetD1preAPf PresetD1sitesAPf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetD2runQAPf PresetD2runAPfQ PresetD2runAPfH PresetD2runAPfM.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetPinvA PresetPinvAPf PresetPinvA2aPf PresetD2runARd0mnPf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YK11.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require StackUpMainA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfIalApartPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCsokLazyMaps YGcfInstBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AD2iExhErrb AD2iPfCells.

(* A cited theorem proved under CwPinvA's frame results (its file's Section hypotheses): apply it to CwPinvA's
   theorems, whichever of the three it takes. *)
Ltac cite_pinv H :=
  repeat match type of H with
  | ?A -> _ =>
      let X := fresh "X" in
      assert (X : A) by first [ exact PresetPinvAPf.finv_run_pinv_A_holds | exact PresetPinvAPf.finv_site_pinv_A_holds
                              | exact PresetPinvAPf.finv_icpt_pinv_A_holds ];
      specialize (H X); clear X
  end.

(* THE MAIN-ENTRY PRESENCE (lib/A/PresetD1pA.v section 3): the start-up lane's stack_up_main_W1_A at the driver's
   binders *)
Section stackup.
#[local] Existing Instance YK11.fx0.
Theorem H_stackup_main_A_holds : PresetD1pA.H_stackup_main_A.
Proof.
intros rc sp rdraw brk inp Hsp Hva Hve Hfit h ch E R FULL model Hch HC HE HM H1_8 ly Hal Htop a Ha.
eapply StackUpMainA.stack_up_main_W1_A; eassumption.
Qed.
End stackup.

(* THE IMAGE ROWS (lib/A/PresetD1pA.v section 4) at CfImg_A: EXH_OFF_t, errb_obj_owned_t, errb_ial_apart_t and
   pf_cells_owned_t from the image's rows (lib/A/CfIalApartPreset.v) *)
Theorem H_errb_rows_A_holds : PresetD1pA.H_errb_rows_A.
Proof.
intros B HB. exact (conj CfIalApartPreset.exh_off_A
  (conj (CfIalApartPreset.errb_obj_owned_A B HB) (CfIalApartPreset.errb_ial_apart_A B HB))).
Qed.
Theorem H_pf_rows_A_holds : PresetD1pA.H_pf_rows_A.
Proof. intros B HB. exact (CfIalApartPreset.pf_cells_owned_A B HB). Qed.

(* THE START-UP ROWS (lib/A/PresetD1pA.v section 4) at the driver's binders: the init model's lazy and noaccess maps
   lie in its maps (cs_ok's co_lzsub and co_nasub, lib/Reusable/YCsokLazyMaps.v); the start witnesses of the two
   machine cells and of Printf's two cells at W1, from the 50 hand-off states of lib/A/AB01.v (lib/A/AD2iExhErrb.v,
   lib/A/AD2iPfCells.v), the cells put in the field form by the draft's YGcfInstBase.exh_cell_cf_init /
   errb_cells_cf_init *)
Section startrows.
#[local] Existing Instance YK11.fx0.
Theorem H_start_lazy_A_holds : PresetD1pA.H_start_lazy_A.
Proof.
intros sp rdraw brk inp h ch E R FULL model Hch HC.
exact (YCsokLazyMaps.cs_ok_lazy_in_maps_cf _ _ _ _ _ _ _ _ _ _ _ _ HC).
Qed.
Theorem H_start_cells_A_holds : PresetD1pA.H_start_cells_A.
Proof.
intros rc sp rdraw brk inp Hsp Hva h ch E R FULL model Hch HC H1_8 B HB W' L.
destruct (AD2iExhErrb.main_exh_errb_cells_A B HB sp rdraw brk inp Hsp Hva h ch E R FULL model Hch HC H1_8 W' L)
  as (X & P & M & D & C & S).
split; [apply YGcfInstBase.exh_cell_cf_init; exact X | apply YGcfInstBase.errb_cells_cf_init; assumption].
Qed.
Theorem H_start_pf_A_holds : PresetD1pA.H_start_pf_A.
Proof.
intros rc sp rdraw brk inp Hsp Hva h ch E R FULL model Hch HC H1_8 B HB W' L.
exact (AD2iPfCells.main_pf_cells_A B HB sp rdraw brk inp Hsp Hva h ch E R FULL model Hch HC H1_8 W' L).
Qed.
End startrows.

Theorem tfib_drv_main_A_holds : PresetD1pA.tfib_drv_main_A.
Proof.
pose proof PresetD1rAPf.loop_L_x_A_holds as Hloop_L_x. cite_pinv Hloop_L_x.
pose proof PresetD2eAPf.runqm_cf_A_holds as Hrunqm. cite_pinv Hrunqm.
pose proof PresetD2runQAPf.tfib_run_Q_cf_A_holds as Hrun_Q. cite_pinv Hrun_Q.
pose proof PresetD2runAPfQ.tfib_post_P_cf_A_holds as Hpost_P. cite_pinv Hpost_P.
pose proof PresetD2runAPfH.tfib_hdr_cf_A_holds as Hhdr. cite_pinv Hhdr.
pose proof PresetD2runAPfM.tfib_file_arm_cf_A_holds as Hfile_arm. cite_pinv Hfile_arm.
pose proof PresetD2runAPfM.tfib_dir_arm_cf_A_holds as Hdir_arm. cite_pinv Hdir_arm.
pose proof PresetD2runARd0mnPf.tfib_rd0_dir_cf_A_holds as Hrd0_dir. cite_pinv Hrd0_dir.
pose proof PresetD2runARd0mnPf.tfib_rd0_file_cf_A_holds as Hrd0_file. cite_pinv Hrd0_file.
exact (PresetD1pAPf.tfib_drv_main_A_of_leaves
  PresetD1preAPf.tfib_malloc_site_cf_A_holds PresetD1preAPf.tfib_memcpy_site_cf_A_holds
  PresetD1preAPf.tfib_read_check_cf_A_holds PresetD1preAPf.tfib_rderr_leaf_cf_A_holds
  PresetD1preAPf.tfib_refused_leaf_cf_A_holds PresetD1preAPf.tfib_cannot_open_cf_A_holds
  PresetD1preAPf.tfib_usage_cf_A_holds PresetD1preAPf.tfib_short_leaf_cf_A_holds
  PresetD1preAPf.tfib_overrun_leaf_cf_A_holds
  PresetD1sitesAPf.free_site_cf_A_holds PresetD1sitesAPf.free_null_site_cf_A_holds
  PresetD1sitesAPf.free_site_nomn_cf_A_holds PresetD1sitesAPf.free_null_site_nomn_cf_A_holds
  PresetD1sitesAPf.exit_leaf_cf_A_holds
  Hloop_L_x Hrunqm Hrun_Q Hpost_P Hhdr Hrd0_dir Hrd0_file Hfile_arm Hdir_arm
  PresetPinvAPf.tfib_finv_handoff_pinv_A_holds PresetPinvA2aPf.tfib_arm_argv2_cf_A_holds
  PresetPinvAPf.finv_run_pinv_A_holds PresetPinvAPf.finv_site_pinv_A_holds PresetPinvAPf.finv_icpt_pinv_A_holds
  H_stackup_main_A_holds H_start_lazy_A_holds H_start_cells_A_holds H_start_pf_A_holds
  H_errb_rows_A_holds H_pf_rows_A_holds).
Qed.

Print Assumptions H_start_lazy_A_holds.
Print Assumptions H_start_cells_A_holds.
Print Assumptions H_start_pf_A_holds.
Print Assumptions tfib_drv_main_A_holds.
