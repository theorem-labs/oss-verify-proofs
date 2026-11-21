(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the SIGPIPE disposition as a launch variable; the new launch (process input, auxv, group id, exec file name); the read-only-backing form of the system-call steps; the run over the run's segments; the channel-reader premise of writev; the BMode context; imports. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import NArith ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec StoreOk AsanAcct HeapIface HeapIfaceA IcptIfaceA LibIface LibIfaceAB LibIfaceAE L5Defs L5Core L5DefsA HeapIfaceAEx HeapIfaceAExI HeapIfaceAEr HandoffBridgeK ArtRuns ArtBridge EarInv EarFsInv EarIfaceInst EarIfaceLayoutPM EarIfaceMcmp EarFam EarFamTop EraMainPhaseA EraInstA EraInstAX EraDiagArms EraUsageArm EraDrvMain Ea0Drv_defs Ea0DrvLibL Ea0DrvLibInit Ea0DrvG Ea0ExitCells.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PmModel PmStatics PmStaticsA PmSpecs PmSpecsA PeSpecsAa PeSpecsAmc.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout PeCLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeCSinkA PeCSpecsA PeCSpecsAa PeCStaticsA PeTopAL PeTopALChkA PeCTopA PeCTopAsmA PeALayFacts PeAExitCells UbjEncPmAsanLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import BMode ShapeAlg SpinAlg Spec BigintSpec KillFree HaltsKit UbjEncShapes FrmInit AsanInitK Ea0DefsK.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require SRomStable.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition cfg0 : SpuriousCfg := mkSpuriousCfg false true true true true true.
#[local] Instance ScfgP_cfg0 : ScfgP := {| SCFG := cfg0 |}.
Import PEALF.
Module EA := Asan.M.

Lemma LIMIT_is_lim_source : AsanInitK.LIMIT = ShippedBudgets.lim_source.
Proof. reflexivity. Qed.

Lemma fork_mode_on : bm_on = true.
Proof. reflexivity. Qed.

Definition P_SA : PESKA.sink_policyA := UbjEncPmAsanLib.P_SA art_L.
Lemma tk_SA : PECASMA.tk P_SA = 1304.
Proof. exact (proj1 (P_SA_credit art_L art_C art_pma_layout)). Qed.
Lemma tb_SA : PECASMA.tb P_SA = 107447582717.
Proof. exact (proj2 (P_SA_credit art_L art_C art_pma_layout)). Qed.

Lemma ea0_inst : inst_ok_stmt cfg0 art_L art_C BUDGET0.           Proof. exact (as0_inst_ok cfg0 BUDGET0 eq_refl). Qed.
Lemma ea0_free_null : free_null_stmt cfg0 art_L BUDGET0.           Proof. exact (as0_free_null cfg0 BUDGET0). Qed.
Lemma ea0_h4e : h4e_stmt BUDGET0.                                  Proof. exact (as0_h4e BUDGET0). Qed.
Lemma ea0_icpt : icpt_ok_stmt cfg0 art_L art_IL BUDGET0.           Proof. exact (as0_icpt_ok cfg0 art_IL BUDGET0 art_IL_ok). Qed.
Lemma ea0_ext : ext_ok_stmt cfg0 art_L PMA.EXT BUDGET0.            Proof. exact (as0_ext_ok_pma cfg0 BUDGET0 eq_refl). Qed.
Lemma ea0_gap : gap_ok_stmt BUDGET0.                               Proof. exact (as0_gap_ok BUDGET0). Qed.
Lemma ea0_dla : dla_ok_stmt cfg0 art_L art_C art_IL.               Proof. exact (as0_dla_ok cfg0 art_IL art_IL_ok). Qed.
Lemma ea0_consts : drv_consts_stmt art_L art_C art_IL.             Proof. exact (as0_drv_consts art_IL art_IL_ok). Qed.
Lemma ea0_usage : usage_stmt cfg0.
Proof. exact (as0_usage_closed cfg0 art_L art_C art_IL BUDGET0 BUDGET0_lo40 BUDGET0_hi ea0_inst ea0_free_null ea0_h4e ea0_icpt ea0_dla ea0_consts). Qed.

Lemma ea0_fam : forall MAPS0 RESV0 NOACC0 BASE rn,
    bridge_static Asan.M.loaded_segments MAPS0 RESV0 NOACC0 (art_RES rn) (rn_HI rn) BUDGET0 EarInv.LENMAX EarInv.KMAX ->
    art_run_ok rn -> rn_tp rn = 0x675a80 -> rn_key rn = 0 -> rn_tsd rn = 0x696f38 -> rn_loff rn = 0x10 ->
    @PECASMA.fam_ok ScfgP_cfg0 art_L art_C art_IL art_LR (rn_ar rn) (fun D => art_iface art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET0 art_fsinv (art_rn_k rn D)).
Proof.
  intros MAPS0 RESV0 NOACC0 BASE rn STATIC ROK Htp Hkey0 Htsd Hloff.
  exact (art_fam_top MAPS0 RESV0 NOACC0 BASE BUDGET0 rn cfg0 art_IL eq_refl asegs_wx STATIC Htp Hkey0 Htsd Hloff art_IL_ok).
Qed.

Lemma ea0_lay : drv_lib_layoutA (PECASMA.LayA art_L P_SA) art_L.
Proof. unfold PECASMA.LayA. apply PECTA.lib_layout; [rewrite tk_SA| rewrite tb_SA]; lia. Qed.
Lemma ea0_cells : drv_lib_cellsA (PECASMA.LayA art_L P_SA).
Proof. unfold PECASMA.LayA. apply PECTA.lib_cells; [rewrite tk_SA| rewrite tb_SA]; lia. Qed.
Lemma ea0_budget : drv_budgetA art_L (PECASMA.LayA art_L P_SA).
Proof.
  intros n Hn. unfold credA, CAPk, adebit. unfold PECASMA.LayA. rewrite PECTA.LayA_credit, tk_SA, tb_SA.
  destruct (PMA.ly_cost art_L art_C art_pma_layout) as (HK & HL & HO). rewrite HK, HL, HO. cbn [fst snd]. lia.
Qed.

Lemma ea0_lsxfa : forall (ar : asan_run) (g : PMST.st) (M : word -> option byte),
  LibIface.ls_ok ((fun _ : asan_run => PECASMA.TopLSA) ar) g M -> exists ax : axv, atexit_cellsA M ax.
Proof. intros ar g M H. exact (PEAXC.lsx_atexit g M H). Qed.

#[local] Notation PTrue := (fun _ : list byte => True).
Lemma ea0_drv : drv_main_stmt cfg0 art_L art_C art_IL (PECASMA.LayA art_L P_SA) (fun _ => PECASMA.TopLSA) PTrue PTrue.
Proof. exact (as0_drv_main_closed cfg0 art_L art_C art_IL (PECASMA.LayA art_L P_SA) _ PTrue PTrue ea0_lay ea0_cells ea0_budget). Qed.

Lemma LIBAh : lib_ok_stmtFX (@PECASMA.fam_ok ScfgP_cfg0 art_L art_C art_IL art_LR) art_L (PECASMA.LayA art_L P_SA) PECASMA.TopLSA PTrue PTrue.
Proof. exact (lib_okFX_SA art_L art_C art_IL art_LR art_pma_layout art_IL_ok EarIfaceMcmp.art_mcmp_cells). Qed.

Theorem ea0_run_on : forall sp brk0 mbase (rdraw : EntryDraw) (argv envp : list (list byte)) (fs : Fs.Fs) (stdin : InputStream) (uid gid hw : word) (groups : list word)
                         (net : NetQueue) (nofile sigmask : word) (abrt : bool) (ur : InputStream) (kb : KernelBuild) (execfn : list byte) (sdf : bool),
  valid_sp sp -> valid_brk EA.loaded_segments brk0 -> valid_mmap_base mbase -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
  entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf) ->
  valid_launch (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf) ->
  valid_id uid -> valid_hwcap hw -> valid_fs fs ->
  srealizes EA.loaded_segments cfg0 (init_config EA.loaded_segments EA.init_pc EA.phdrs sp brk0 mbase rdraw AsanInitK.LIMIT
                                         (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf))
            (spec argv fs).
Proof.
  intros sp brk0 mbase rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf
         Hsp Hbrk Hmb Hva Hve Hfit Hlau Hvl Huid Hhw Hvfs.
  assert (HPO : ue_reach_ok PTrue (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf))
    by (intros a0s path fdata _ _ _ _ _ _; exact I).
  (* the main phase's section binds the CONFIG_RSEQ flag [r] and ties it by [HRZ]; the run's own flag discharges it *)
  eapply (as0_realizes_spec_run cfg0 eq_refl eq_refl art_L art_C art_IL (PECASMA.LayA art_L P_SA) (fun _ => PECASMA.TopLSA) PMA.EXT BUDGET0 BUDGET0_lo40 BUDGET0_hi
            ea0_inst ea0_free_null ea0_h4e ea0_icpt ea0_ext ea0_gap PTrue PTrue
            (@PECASMA.fam_ok ScfgP_cfg0 art_L art_C art_IL art_LR) LIBAh ea0_fam ea0_dla ea0_consts ea0_drv ea0_usage ea0_lsxfa);
    first [eassumption | reflexivity].
Qed.

Theorem ue_halts_asan :
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source codes02 (mkImage EA.loaded_segments EA.init_pc EA.phdrs).
Proof.
  intros [sp brk mb rnd] inp Hen Hvalid Hsw.
  (* LPS 727298f3: [valid_entry]'s fifth conjunct is the launch; the input facts are read through the
     model's named accessors, never by position *)
  pose proof (valid_input_va_size _ Hvalid) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen.
  destruct Hen as [Hsp [Hbrk [Hmb [Hfit Hlau]]]].
  pose proof (valid_input_argv _ Hvalid) as Hargv. pose proof (valid_input_envp _ Hvalid) as Henvp.
  pose proof (valid_input_fs _ Hvalid) as Hfs. pose proof (valid_input_creds _ Hvalid) as Hcreds.
  pose proof (valid_input_hwcap _ Hvalid) as Hhw. pose proof (valid_input_launch _ Hvalid) as Hvl.
  pose proof (valid_input_channel_reader _ Hvalid) as Hrd. pose proof (valid_input_sigpipe_terminal _ Hvalid) as Hspt.
  pose proof (valid_input_recorded_kernel _ Hvalid) as Hker. clear Hvalid.
  destruct inp as [argv envp fs0 stdin0 uid gid groups net nofile sigmask hw abt va ur tmp kb exfn chrd spd spt].
  cbn [in_argv in_envp in_uid in_hwcap in_va_size in_fs in_image_fs in_tmp in_kernel
       in_channel_reader in_sigpipe_default in_sigpipe_terminal] in *.
  subst va chrd spt.
  destruct Hcreds as [Hu _]. cbn [in_uid] in Hu.
  (* the kernel of record is the sixteenth field [AsanInitK.inp] writes; the SIGPIPE disposition [spd]
     is free and is the launch's [sdf] *)
  rewrite Hker in Hlau, Hvl, Hsw |- *.
  pose proof (ea0_run_on sp brk mb rnd argv envp (fs_seed_tmp fs0 tmp) stdin0 uid gid hw groups net nofile sigmask abt ur kb exfn spd
                Hsp Hbrk Hmb Hargv Henvp Hfit Hlau Hvl Hu Hhw Hfs) as RUN.
  set (inp' := AsanInitK.inp argv envp (fs_seed_tmp fs0 tmp) stdin0 uid gid hw groups net nofile sigmask abt ur kb exfn spd) in *.
  (* the run reads the binary's segments with the run's vDSO appended ([Run.run_segments]) *)
  pose proof (SRomStable.srun_init cfg0 EA.loaded_segments inp' sp mb _ _ _ _ _ _ eq_refl RUN) as RUNr.
  pose proof (top_of_guarded (bmK := bm_on_inst) _ _ _ _ _ _ _ _ _ _ _ (SRomStable.frm_safe_run_segments _ inp' sp mb frm_safe_Ma0) RUNr) as RUN0.
  change (must_exit_in_scfg forced_only_cfg codes02 (mkImage EA.loaded_segments EA.init_pc EA.phdrs) AsanInitK.LIMIT (mkEntry sp brk mb rnd) inp').
  change (~ run_scfg_budget_refused forced_only_cfg (mkImage EA.loaded_segments EA.init_pc EA.phdrs) AsanInitK.LIMIT (mkEntry sp brk mb rnd) inp') in Hsw.
  eapply (srealizes_init_must_exit (bmK := bm_on_inst) eq_refl cfg0).
  - exact RUN0.
  - apply exit_codes_in_spec.
  - apply kill_free_spec.
  - exact Hsw.
Qed.
