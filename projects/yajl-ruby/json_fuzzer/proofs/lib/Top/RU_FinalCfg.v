(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List.
Require LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Require LinuxProcessSemantics.EquivalenceDefinition.MustExit.
Require LinuxProcessSemantics.EquivalenceDefinition.FinInput.
Require LinuxProcessSemantics.EquivalenceDefinition.Classifier.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType StackLayout Fs State Run.
Require OSSVerify.yajl_ruby.json_fuzzer.images.Plain.
Require OSSVerify.yajl_ruby.json_fuzzer.images.Ubsan.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling Nodes NodesCfg Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import RawAlloc MSuccRaw.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks MallocKown.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require RAlloc_rz RYajl_iface RYajl_asm RY_buf_small RY_lex_top RY_parse_asm
     RDrv_iface RDrv_run RDrv_yadapt RDrv_E RDrv_spec RDrv_inst.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require UAlloc_rz UMalloc_iface UYajl_iface UYajl_asm UY_buf_small UY_lex_top UY_parse_asm
     UDrv_iface UDrv_run UDrv_yadapt UDrv_E UDrv_spec UDrv_inst.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Import SpecT GlueCfg R_TopCfg U_TopCfg RU_EquivCfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Module SpuriousCfgM <: LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SPURIOUS_CFG.
  Definition cfg := LinuxProcessSemantics.LinuxProcessSem.Run.mkSpuriousCfg false true true true true true.
End SpuriousCfgM.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Module RSide.
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

  Definition RSPEC := R_realizes_spec_cfg DRV DRV_spec
     (fun RC__ sp0 argv envp uid hw rnd VSP RCSP RCS EFIT VA VE FS0 MO =>
        @rz_main_drv RC__ sp0 argv envp uid hw rnd VSP RCSP RCS EFIT VA VE RHKG FS0 drv_iface_R (yfuzz_rz_R FS0) MO).

  (* [comment removed for export] *)
  Definition RSPEC_lim := R_realizes_spec_cfg_lim DRV DRV_spec
     (fun RC__ sp0 argv envp uid hw rnd VSP RCSP RCS EFIT VA VE FS0 MO =>
        @rz_main_drv RC__ sp0 argv envp uid hw rnd VSP RCSP RCS EFIT VA VE RHKG FS0 drv_iface_R (yfuzz_rz_R FS0) MO).
End RSide.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Module USide.
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

  Definition USPEC := U_realizes_spec_cfg (@RHKG) RHKG_intro DRV DRV_spec
     (fun RC__ sp0 argv envp uid hw rnd VSP RCSP RCS EFIT VA VE FS0 MO =>
        @rz_main_drv RC__ sp0 argv envp uid hw rnd VSP RCSP RCS EFIT VA VE RHKG FS0 drv_iface_U (yfuzz_rz_U FS0) MO).

  (* [comment removed for export] *)
  Definition USPEC_lim := U_realizes_spec_cfg_lim (@RHKG) RHKG_intro DRV DRV_spec
     (fun RC__ sp0 argv envp uid hw rnd VSP RCSP RCS EFIT VA VE FS0 MO =>
        @rz_main_drv RC__ sp0 argv envp uid hw rnd VSP RCSP RCS EFIT VA VE RHKG FS0 drv_iface_U (yfuzz_rz_U FS0) MO).
End USide.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem R_realizes_spec_final :
  realizes_spec_cfg acfg rsegs r_init_pc r_phdrs source_alloc_limit (fun inp => spec (in_argv inp) (in_fs inp)).
Proof. exact RSide.RSPEC. Qed.

Theorem U_realizes_spec_final :
  realizes_spec_cfg acfg usegs u_init_pc u_phdrs target_alloc_limit (fun inp => spec (in_argv inp) (in_fs inp)).
Proof. exact USide.USPEC. Qed.

(* [comment removed for export] *)
Theorem R_realizes_spec_final_lim : forall lim : Z, VMINc <= lim ->
  realizes_spec_cfg acfg rsegs r_init_pc r_phdrs lim (fun inp => spec (in_argv inp) (in_fs inp)).
Proof. exact RSide.RSPEC_lim. Qed.

Theorem U_realizes_spec_final_lim : forall lim : Z, VMINc <= lim ->
  realizes_spec_cfg acfg usegs u_init_pc u_phdrs lim (fun inp => spec (in_argv inp) (in_fs inp)).
Proof. exact USide.USPEC_lim. Qed.

Theorem R_realizes_spec_final_2G :
  realizes_spec_cfg acfg rsegs r_init_pc r_phdrs LinuxProcessSemantics.EquivalenceDefinition.Equivalence.sanitizer_source_limit
                    (fun inp => spec (in_argv inp) (in_fs inp)).
Proof. exact (R_realizes_spec_final_lim _ VMINc_le_2G). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem strong_universal_error_free_json_fuzzer_ubsan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg
    SpuriousCfgM.cfg
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.yajl_ruby.json_fuzzer.images.Plain.M.loaded_segments OSSVerify.yajl_ruby.json_fuzzer.images.Plain.M.init_pc OSSVerify.yajl_ruby.json_fuzzer.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.yajl_ruby.json_fuzzer.images.Ubsan.M.loaded_segments OSSVerify.yajl_ruby.json_fuzzer.images.Ubsan.M.init_pc OSSVerify.yajl_ruby.json_fuzzer.images.Ubsan.M.phdrs).
Proof. exact (RU_EquivCfg.strong_universal_error_free_json_fuzzer_ubsan RSide.RSPEC USide.USPEC). Qed.

