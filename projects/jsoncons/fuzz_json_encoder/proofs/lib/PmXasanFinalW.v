(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the SIGPIPE disposition left free): changed pm_xasan_tgt, pm_xasan_tgt_stmtW. *)
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

(* STATEMENT CHANGED, old beside new (tree-local; no Statements.v closure names it):
     OLD  .. valid_sp sp -> valid_brk .. -> valid_mmap_base mbase -> entry_stack_fits .. ->
          valid_argv -> valid_envp -> valid_fs -> valid_creds -> valid_hwcap -> in_va_size inp = Sv48 ->
          (forall a0s path, .. -> phi_okD PHI path (in_fs inp)) -> ..
     NEW  the same, plus the facts [Run.valid_input_abort] and [Run.valid_entry] give at
          LPS 727298f3 and the asan lane's start-up reads: [valid_launch inp],
          [entry_launch_ok_va Sv48 ..], the input's fixed flags channel_reader / sigpipe_terminal
          and [in_kernel inp = recorded_kernel (in_kernel inp)], which make [inp] an
          [AsanInitK.inp] instance at the input's own SIGPIPE disposition (left free by
          [Run.valid_input_abort]).  The conclusion is unchanged. *)
Definition pm_xasan_tgt_stmtW (scfg : SpuriousCfg) (PHI : list byte -> Prop) : Prop :=
  forall sp brk mbase (rdraw : EntryDraw) (inp : ProcInput),
    valid_sp sp -> valid_brk Asan.M.loaded_segments brk -> valid_mmap_base mbase ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) -> valid_creds inp -> valid_hwcap (in_hwcap inp) ->
    in_va_size inp = Sv48 ->
    valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp ->
    in_channel_reader inp = true -> in_sigpipe_terminal inp = false ->
    in_kernel inp = recorded_kernel (in_kernel inp) ->
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

  (* Proof, old beside new: the input is destructured at its 20 fields (was 15) and shown to
     be [AsanInitK.inp] at kernel build [kk] and SIGPIPE disposition [sd] (the record stores
     [recorded_kernel kk], equal to [kk] by the last premise); [Pm4MainPhaseAW.as0_realizes_spec_run]
     is restated over that input and [apc], so it is reached by [eapply .. with]. *)
  Theorem pm_xasan_tgt : pm_xasan_tgt_stmtW cfg0 PHI.
  Proof.
    intros sp brk mbase rdraw inp Hsp Hbrk Hmb Hfit Hva Hve Hvfs Hcreds Hhw Hsv Hvl Hlau Hcr Hst Hrk PHIOK.
    destruct inp as [argv envp ifs0 stdin0 uid gid groups net nofile sigmask hw abt va urnd tmp0 kk execfn cr sd st].
    unfold in_fs in *.
    cbn [in_argv in_envp in_image_fs in_tmp in_uid in_hwcap in_va_size in_channel_reader in_sigpipe_terminal in_kernel] in *.
    subst va cr st.
    destruct Hcreds as [Hu _]. cbn [in_uid] in Hu.
    assert (EI : mkProcInput_full argv envp ifs0 stdin0 uid gid groups net nofile sigmask hw abt Sv48 urnd tmp0 kk execfn true sd false
                 = AsanInitK.inp argv envp ifs0 stdin0 uid gid hw groups net nofile sigmask abt urnd tmp0 kk execfn sd)
      by (unfold AsanInitK.inp; rewrite <- Hrk; reflexivity).
    rewrite EI in *.
    eapply as0_realizes_spec_run with (L := art_L) (C := art_C) (IL := art_IL) (LX := art_LX) (ILX := art_ILX)
                                      (Lay := LayA) (LSt := LStA) (BUDGET := BUDGET0) (PHI := PHI) (fs := fs_seed_tmp ifs0 tmp0);
      first [ reflexivity | exact BUDGET0_lo | exact BUDGET0_hi | eassumption
            | exact (as0_inst_ok cfg0 BUDGET0 eq_refl) | exact (as0_instN_ok cfg0 BUDGET0 eq_refl)
            | exact (as0_free_null cfg0 BUDGET0) | exact (as0_h4e BUDGET0)
            | exact (as0_icpt_ok cfg0 art_IL art_ILX BUDGET0 art_IL_ok art_ILX_ok ICPTX) | exact (as0_sfree_ok cfg0 BUDGET0 eq_refl) | exact LIBA
            | exact (as0_dla_ok cfg0 art_IL art_IL_ok) | exact (as0_drv_consts art_IL art_IL_ok)
            | exact (as0_drv_mainW cfg0 PHI art_L art_C art_IL LayA LStA BUDGET0 DLLA DLCA BUDA
                       (dg_openerr_ok cfg0 art_L art_C art_IL) (dg_short_ok cfg0 art_L art_C art_IL) (dg_overrun_ok cfg0 art_L art_C art_IL) (dg_refuse_ok cfg0 art_L art_C art_IL)
                       (dg_nofile_of_openerrW cfg0 PHI art_L art_C art_IL LayA LStA BUDGET0 (dg_openerr_ok cfg0 art_L art_C art_IL))
                       (dg_dot_ofW cfg0 PHI art_L art_C art_IL LayA LStA BUDGET0 DLLA BUDA (dg_openerr_ok cfg0 art_L art_C art_IL) (dg_readerr_ok cfg0 art_L art_C art_IL)))
            | exact (as0_usage_closed cfg0 art_L art_C art_IL art_ILX BUDGET0 BUDGET0_lo BUDGET0_hi (as0_inst_ok cfg0 BUDGET0 eq_refl) (as0_free_null cfg0 BUDGET0) (as0_h4e BUDGET0)
                       (as0_icpt_ok cfg0 art_IL art_ILX BUDGET0 art_IL_ok art_ILX_ok ICPTX) (as0_dla_ok cfg0 art_IL art_IL_ok) (as0_drv_consts art_IL art_IL_ok))
            | exact PHIOK
            | (vm_compute; reflexivity) ].
  Qed.
End Hyps.
End FPX_1.
