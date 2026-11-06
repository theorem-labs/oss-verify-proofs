(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List.
Require LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Require LinuxProcessSemantics.EquivalenceDefinition.MustExit.
Require LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType StackLayout Fs State Run.
Require OSSVerify.yajl_ruby.json_fuzzer.images.Plain.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling Nodes NodesCfg Images RunInit.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import RawAlloc MSuccRaw.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks MallocKown.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require RAlloc_rz RYajl_iface RYajl_asm RY_buf_small RY_lex_top RY_parse_asm
     RDrv_iface RDrv_run RDrv_yadapt RDrv_E RDrv_spec RDrv_inst.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Import SpecT GlueCfg R_TopCfg HaltsGen HaltsSpec HaltsGlue.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

(* [comment removed for export] *)
Module PlainSide.
  Import RAlloc_rz RYajl_iface RYajl_asm RY_buf_small RY_lex_top RY_parse_asm
         RDrv_iface RDrv_run RDrv_yadapt RDrv_E RDrv_spec RDrv_inst.
  Section WithRC.
    Context {RC__ : RunCeiling}.
    Variable FS0 : Fs.Fs.
    Let HK := RHKG (G_fs FS0).
    Let HKS : HK_silent_stmt HK := RHKG_silent (G_fs FS0).
    Let HKP : HK_perm_stmt HK := RHKG_perm (G_fs FS0).
    Let HKF : HK_frame_stmt HK := RHKG_frame (G_fs FS0).
    Let HKB : HK_blocks_stmt HK := RHKG_blocks (G_fs FS0).
    Let RM := rmalloc_rz (G_fs FS0) (frame_ok_G_fs FS0).
    Let RF := rfree_rz (G_fs FS0) (frame_ok_G_fs FS0).
    Let RRN := rrealloc_null_rz (G_fs FS0) (frame_ok_G_fs FS0).
    Let RR := rrealloc_rz (G_fs FS0) (frame_ok_G_fs FS0).

    Lemma ylex_lex_R : ylex_lex_stmt HK.
    Proof. exact (ylex_lex_spec HK HKS HKP HKF HKB (ybuf_append_closed HK HKS HKP HKF HKB RM RR) ybuf_err_spec). Qed.

    Lemma yfuzz_R : yfuzz_stmt HK.
    Proof. exact (yfuzz_closed_lex HK HKS HKP HKF HKB RM RF RR RRN ylex_lex_R). Qed.

    Lemma yfuzz_rz_R : yfuzz_rz_stmt HK.
    Proof. exact (yfuzz_rz_of RHKG drv_iface_R FS0 yfuzz_R). Qed.
  End WithRC.

  (* [comment removed for export] *)
  Definition RRZ_lim := R_realizes_cfg_lim DRV DRV_spec
     (fun RC__ sp0 argv envp uid hw rnd VSP RCSP RCS EFIT VA VE FS0 MO =>
        @rz_main_drv RC__ sp0 argv envp uid hw rnd VSP RCSP RCS EFIT VA VE RHKG FS0 drv_iface_R (yfuzz_rz_R FS0) MO).
End PlainSide.

Lemma R_realizes_16 : forall en inp,
  valid_entry (mkImage rsegs r_init_pc r_phdrs) en inp -> valid_input inp ->
  realizes_cfg acfg rsegs (mkCfg (ms0 rsegs r_init_pc r_phdrs en inp) (mo0 rsegs source_alloc_limit en inp))
               (spec (in_argv inp) (in_fs inp)).
Proof. exact (PlainSide.RRZ_lim source_alloc_limit VMINc_le_source). Qed.

Theorem halts_plain :
  LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.halts_allowed_T_scfg_budgets
    LinuxProcessSemantics.LinuxProcessSem.Run.forced_only_cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    [Z_to_bv 64 0; Z_to_bv 64 2]
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.yajl_ruby.json_fuzzer.images.Plain.M.loaded_segments OSSVerify.yajl_ruby.json_fuzzer.images.Plain.M.init_pc OSSVerify.yajl_ruby.json_fuzzer.images.Plain.M.phdrs).
Proof.
  apply (halts_allowed_of_realizes_ms0 acfg rsegs r_init_pc r_phdrs source_alloc_limit halts_codes
           (fun inp => spec (in_argv inp) (in_fs inp))).
  - exact R_realizes_16.
  - intros inp _. apply spec_exits_in.
Qed.
