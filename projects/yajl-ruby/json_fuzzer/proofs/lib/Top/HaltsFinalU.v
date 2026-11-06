(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List.
Require LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Require LinuxProcessSemantics.EquivalenceDefinition.MustExit.
Require LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType StackLayout Fs State Run.
Require OSSVerify.yajl_ruby.json_fuzzer.images.Ubsan.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling Nodes NodesCfg Images RunInit.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import RawAlloc MSuccRaw.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks MallocKown.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require UAlloc_rz UMalloc_iface UYajl_iface UYajl_asm UY_buf_small UY_lex_top UY_parse_asm
     UDrv_iface UDrv_run UDrv_yadapt UDrv_E UDrv_spec UDrv_inst.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Import SpecT GlueCfg U_TopCfg HaltsGen HaltsSpec HaltsGlue.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

(* [comment removed for export] *)
Module UbsanSide.
  Import UAlloc_rz UMalloc_iface UYajl_iface UYajl_asm UY_buf_small UY_lex_top UY_parse_asm
         UDrv_iface UDrv_run UDrv_yadapt UDrv_E UDrv_spec UDrv_inst.
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

    Lemma ylex_lex_U : ylex_lex_stmt HK.
    Proof. exact (ylex_lex_spec HK HKS HKP HKF HKB (ybuf_append_closed HK HKS HKP HKF HKB RM RR) ybuf_err_spec). Qed.

    Lemma yfuzz_U : yfuzz_stmt HK.
    Proof. exact (yfuzz_closed_lex HK HKS HKP HKF HKB RM RF RR RRN ylex_lex_U). Qed.

    Lemma yfuzz_rz_U : yfuzz_rz_stmt HK.
    Proof. exact (yfuzz_rz_of RHKG drv_iface_U FS0 yfuzz_U). Qed.
  End WithRC.

  Lemma RHKG_intro : forall (RC__ : RunCeiling) (G : PState -> Model -> Prop) s LB m mo,
    RHEAP s LB m -> KOWN G s mo -> HEADc (map U_TopCfg.sigb LB) s mo -> RHKG G s LB m mo.
  Proof. intros RC__ G s LB m mo A B C. exact (conj A (conj B C)). Qed.

  Definition URZ_lim := U_realizes_cfg_lim (@RHKG) RHKG_intro DRV DRV_spec
     (fun RC__ sp0 argv envp uid hw rnd VSP RCSP RCS EFIT VA VE FS0 MO =>
        @rz_main_drv RC__ sp0 argv envp uid hw rnd VSP RCSP RCS EFIT VA VE RHKG FS0 drv_iface_U (yfuzz_rz_U FS0) MO).
End UbsanSide.

Lemma U_realizes_16 : forall en inp,
  valid_entry (mkImage usegs u_init_pc u_phdrs) en inp -> valid_input inp ->
  realizes_cfg acfg usegs (mkCfg (ms0 usegs u_init_pc u_phdrs en inp) (mo0 usegs source_alloc_limit en inp))
               (spec (in_argv inp) (in_fs inp)).
Proof. exact (UbsanSide.URZ_lim source_alloc_limit VMINc_le_source). Qed.

Theorem halts_ubsan :
  LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.halts_allowed_T_scfg_budgets
    LinuxProcessSemantics.LinuxProcessSem.Run.forced_only_cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    [Z_to_bv 64 0; Z_to_bv 64 2]
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.yajl_ruby.json_fuzzer.images.Ubsan.M.loaded_segments OSSVerify.yajl_ruby.json_fuzzer.images.Ubsan.M.init_pc OSSVerify.yajl_ruby.json_fuzzer.images.Ubsan.M.phdrs).
Proof.
  apply (halts_allowed_of_realizes_ms0 acfg usegs u_init_pc u_phdrs source_alloc_limit halts_codes
           (fun inp => spec (in_argv inp) (in_fs inp))).
  - exact U_realizes_16.
  - intros inp _. apply spec_exits_in.
Qed.
