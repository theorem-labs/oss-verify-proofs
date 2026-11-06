(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import ShapeAlg DivergeSim SpinAlg SpinAlgX Spec BigintSpec HeapIface LibIface VmLimitFrame.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import AsanAcct HeapIfaceA PmHeapIfaceA IcptIfaceA PmIcptIfaceA Pm5IcptLayout PmLibIfaceA PmLibIfaceAW AsanInitK Pm5DefsK
  Pm5ArtFsInv Pm5ArtIfaceInst Pm5ArtIfaceInstX Pm5DrvG Pm5DrvLibL Pm5DrvLibLW Pm5DrvLibInit Pm5MainPhaseA Pm5MainPhaseAW Pm5InstA Pm5DrvMain Pm5DrvMainW Pm5DiagArms Pm5UsageEntry Pm5UsageArm
  Pm5DrvC Pm5DrvD HeapIfaceN Pm5ArtIfaceInstN Pm5Drv_defs.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require PropExec.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition cfg0 : SpuriousCfg := mkSpuriousCfg false true true true true true.

(* [comment removed for export] *)
Definition art_IL : icpt_layout :=
  ICL 0x6c1e8 2304 0x103d0 0x103f0 ART_GLOBALS ART_POISON 0x80b0c 0x80b08 0x6c2d48 0x6c260 4320 [(0x6a1860, 8, 0x6c1b58); (0x6c1b80, 8, 0)] 0x10000 0x166000.
Lemma art_IL_ok : as0_icpt_layout art_IL.
Proof. constructor; reflexivity. Qed.
Definition art_ILX : icpt_layout_x := ICLX 0x6c200 8192 0x6c2c8 512 0x6c18e0 0x76918 512 0x848f8 0x6c1b23 0x6c1fc 0x80b04 0x84680 0x84788 0x847a0 256.
Lemma art_ILX_ok : pm_icpt_layout_x art_ILX.
Proof. constructor; reflexivity. Qed.

(* [comment removed for export] *)
Definition BUDGET0 : Z := 2 ^ 39 - 2 ^ 35.
(* [comment removed for export] *)
Theorem as0_instN_ok : forall scfg BUDGET, sc_alloc scfg = false -> instN_ok_stmt scfg art_L art_IL BUDGET.
Proof.
  intros scfg BUDGET Halloc MAPS0 RESV0 NOACC0 BASE rn BS ROK Htp Hkey Htsd Hloff.
  exact (art_pm_instN MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg art_IL Halloc Pm5Drv_defs.asegs_wx BS art_IL_ok Htp Hkey Htsd Hloff).
Qed.
Lemma BUDGET0_lo : 2 ^ 34 <= BUDGET0.  Proof. unfold BUDGET0. lia. Qed.
Lemma BUDGET0_hi : BUDGET0 <= 2 ^ 39 - 2 ^ 35.  Proof. unfold BUDGET0. lia. Qed.

Abbreviation IMG_tgt :=
  (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs).

Section FPX_1.
#[local] Existing Instance PropExec.fx0.

(* [comment removed for export] *)
Definition pm_xboth_tgt_stmtW (scfg : SpuriousCfg) (PHI : list byte -> Prop) : Prop :=
  forall sp brk mbase (rdraw : EntryDraw) (inp : ProcInput),
    valid_sp sp -> valid_brk AsanUbsan.M.loaded_segments brk -> valid_mmap_base mbase ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) -> valid_creds inp -> valid_hwcap (in_hwcap inp) ->
    in_va_size inp = Sv48 ->
    (forall a0s path, in_argv inp = [a0s; path] -> phi_okD PHI path (in_fs inp)) ->
    srealizes AsanUbsan.M.loaded_segments scfg
      (init_config AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs sp brk mbase rdraw target_alloc_limit inp)
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

  Theorem pm_xboth_tgt : pm_xboth_tgt_stmtW cfg0 PHI.
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
