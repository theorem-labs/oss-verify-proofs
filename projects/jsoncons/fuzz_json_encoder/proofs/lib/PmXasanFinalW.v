(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import ShapeAlg DivergeSim SpinAlg SpinAlgX Spec BigintSpec HeapIface LibIface VmLimitFrame.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import AsanAcct HeapIfaceA PmHeapIfaceA IcptIfaceA PmIcptIfaceA Pm4IcptLayout PmLibIfaceA PmLibIfaceAW AsanInitK Pm4DefsK
  Pm4ArtFsInv Pm4ArtIfaceInst Pm4ArtIfaceInstX Pm4DrvG Pm4DrvLibL Pm4DrvLibLW Pm4DrvLibInit Pm4MainPhaseA Pm4MainPhaseAW Pm4InstA Pm4DrvMain Pm4DrvMainW Pm4DiagArms Pm4UsageEntry Pm4UsageArm
  Pm4DrvC Pm4DrvD HeapIfaceN Pm4ArtIfaceInstN Pm4Drv_defs.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require PropExec.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition cfg0 : SpuriousCfg := mkSpuriousCfg false true true true true true.

(* [comment removed for export] *)
Definition art_IL : icpt_layout :=
  ICL 0x6b918 2304 0x103c0 0x103e0 ART_GLOBALS ART_POISON 0x8023c 0x80238 0x6bf488 0x6b990 4320 [(0x69dfa0, 8, 0x6be298); (0x6be2c0, 8, 0)] 0x10000 0x162000.
Lemma art_IL_ok : as0_icpt_layout art_IL.
Proof. constructor; reflexivity. Qed.
Definition art_ILX : icpt_layout_x := ICLX 0x6b930 8192 0x6b9f8 512 0x6be020 0x76048 512 0x84028 0x6be263 0x6b92c 0x80234 0x83db0 0x83eb8 0x83ed0 256.
Lemma art_ILX_ok : pm_icpt_layout_x art_ILX.
Proof. constructor; reflexivity. Qed.

(* [comment removed for export] *)
Definition BUDGET0 : Z := 2 ^ 39 - 2 ^ 35.
(* [comment removed for export] *)
Theorem as0_instN_ok : forall scfg BUDGET, sc_alloc scfg = false -> instN_ok_stmt scfg art_L art_IL BUDGET.
Proof.
  intros scfg BUDGET Halloc MAPS0 RESV0 NOACC0 BASE rn BS ROK Htp Hkey Htsd Hloff.
  exact (art_pm_instN MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg art_IL Halloc Pm4Drv_defs.asegs_wx BS art_IL_ok Htp Hkey Htsd Hloff).
Qed.
Lemma BUDGET0_lo : 2 ^ 34 <= BUDGET0.  Proof. unfold BUDGET0. lia. Qed.
Lemma BUDGET0_hi : BUDGET0 <= 2 ^ 39 - 2 ^ 35.  Proof. unfold BUDGET0. lia. Qed.

Abbreviation IMG_tgt :=
  (mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs).

Section FPX_1.
#[local] Existing Instance PropExec.fx0.

(* [comment removed for export] *)
Definition pm_xasan_tgt_stmtW (scfg : SpuriousCfg) (PHI : list byte -> Prop) : Prop :=
  forall sp brk mbase (rdraw : EntryDraw) (inp : ProcInput),
    valid_sp sp -> valid_brk Asan.M.loaded_segments brk -> valid_mmap_base mbase ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) -> valid_creds inp -> valid_hwcap (in_hwcap inp) ->
    in_va_size inp = Sv48 ->
    (forall a0s path, in_argv inp = [a0s; path] -> phi_okD PHI path (in_fs inp)) ->
    srealizes Asan.M.loaded_segments scfg
      (init_config Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs sp brk mbase rdraw target_alloc_limit inp)
      (spec (in_argv inp) (in_fs inp)).

Section Hyps.
  Variable PHI : list byte -> Prop.
  Variable LayA : lib_layoutA.
  Variable LStA : asan_run -> lib_statics.
  Hypothesis DLLA : drv_lib_layoutA LayA art_L.
  Hypothesis DLCA : drv_lib_cellsA LayA.
  Hypothesis BUDA : drv_budgetA art_L LayA BUDGET0.
  Hypothesis LIBA : lib_ok_stmtW cfg0 art_L art_LX art_C art_IL art_ILX LayA LStA PHI.

  Let ICPTX : icptx_stmt cfg0 art_ILX BUDGET0 := as0_icptx cfg0 art_ILX BUDGET0 art_ILX_ok.

  Theorem pm_xasan_tgt : pm_xasan_tgt_stmtW cfg0 PHI.
  Proof.
    intros sp brk mbase rdraw inp Hsp Hbrk Hmb Hfit Hva Hve Hvfs Hcreds Hhw Hsv PHIOK.
    destruct inp as [argv envp ifs0 stdin0 uid gid groups net nofile sigmask hw abt va urnd tmp0].
    unfold in_fs in *. cbn [in_argv in_envp in_image_fs in_tmp in_uid in_hwcap in_va_size] in *. subst va.
    destruct Hcreds as [Hu _]. cbn [in_uid] in Hu.
    exact (as0_realizes_spec_run cfg0 eq_refl eq_refl art_L art_C art_IL art_LX art_ILX LayA LStA BUDGET0 BUDGET0_lo BUDGET0_hi
             (as0_inst_ok cfg0 BUDGET0 eq_refl) (as0_instN_ok cfg0 BUDGET0 eq_refl) (as0_free_null cfg0 BUDGET0) (as0_h4e BUDGET0)
             (as0_icpt_ok cfg0 art_IL art_ILX BUDGET0 art_IL_ok art_ILX_ok ICPTX) (as0_sfree_ok cfg0 BUDGET0 eq_refl) PHI LIBA
             (as0_dla_ok cfg0 art_IL art_IL_ok) (as0_drv_consts art_IL art_IL_ok)
             (as0_drv_mainW cfg0 PHI art_L art_C art_IL LayA LStA BUDGET0 DLLA DLCA BUDA
                (dg_openerr_ok cfg0 art_L art_C art_IL) (dg_short_ok cfg0 art_L art_C art_IL) (dg_overrun_ok cfg0 art_L art_C art_IL) (dg_refuse_ok cfg0 art_L art_C art_IL)
                (dg_nofile_of_openerrW cfg0 PHI art_L art_C art_IL LayA LStA BUDGET0 (dg_openerr_ok cfg0 art_L art_C art_IL))
                (dg_dot_ofW cfg0 PHI art_L art_C art_IL LayA LStA BUDGET0 DLLA BUDA (dg_openerr_ok cfg0 art_L art_C art_IL) (dg_readerr_ok cfg0 art_L art_C art_IL)))
             (as0_usage_closed cfg0 art_L art_C art_IL art_ILX BUDGET0 BUDGET0_lo BUDGET0_hi (as0_inst_ok cfg0 BUDGET0 eq_refl) (as0_free_null cfg0 BUDGET0) (as0_h4e BUDGET0)
                (as0_icpt_ok cfg0 art_IL art_ILX BUDGET0 art_IL_ok art_ILX_ok ICPTX) (as0_dla_ok cfg0 art_IL art_IL_ok) (as0_drv_consts art_IL art_IL_ok))
             sp brk mbase rdraw argv envp (fs_seed_tmp ifs0 tmp0) stdin0 uid gid hw groups net nofile sigmask abt ifs0 urnd tmp0 Hsp Hbrk Hva Hve Hfit Hu Hhw Hvfs eq_refl PHIOK).
  Qed.
End Hyps.
End FPX_1.
