(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import NArith ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec StoreOk AsanAcct HeapIface HeapIfaceA IcptIfaceAB0 LibIface LibIfaceAB LibIfaceAE L5Defs L5Core L5DefsAB0 HeapIfaceAEx HeapIfaceAExI HeapIfaceAEr HandoffBridgeK ArtRuns ArtBridge EbrInv EbrFsInv EbrIfaceInst EbrIfaceLayoutPM EbrIfaceMcmp EbrFam EbrFamTop ErbMainPhaseA ErbInstA ErbInstAX ErbDiagArms ErbUsageArm ErbDrvMain Eb0Drv_defs Eb0DrvLibL Eb0DrvLibInit Eb0DrvG Eb0ExitCells.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PmStatics PmStaticsA PmSpecs PmSpecsA PeSpecsAb PeSpecsAmc.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout PeCLayoutB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeCSinkA PeCSpecsA PeCSpecsAb PeCStaticsA PeTopAL PeTopALChkB PeCTopB PeCTopAsmB PeBLayFacts PeBExitCells UbjEncPmAsanLibB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import BMode ShapeAlg SpinAlg Spec BigintSpec KillFree HaltsKit UbjEncShapes FrmInitB AsanInitK Eb0DefsK.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition cfg0 : SpuriousCfg := mkSpuriousCfg false true true true true true.
#[local] Instance ScfgP_cfg0 : ScfgP := {| SCFG := cfg0 |}.
Import PEBLF.
Module EB := AsanUbsan.M.

Lemma LIMIT_is_lim_source : AsanInitK.LIMIT = ShippedBudgets.lim_source.
Proof. reflexivity. Qed.

Lemma fork_mode_on : bm_on = true.
Proof. reflexivity. Qed.

Definition P_SB : PESKA.sink_policyA := UbjEncPmAsanLibB.P_SB art_L.
Lemma tk_SB : PECASMB.tk P_SB = 1304.
Proof. exact (proj1 (P_SB_credit art_L art_C art_pma_layout)). Qed.
Lemma tb_SB : PECASMB.tb P_SB = 107447582717.
Proof. exact (proj2 (P_SB_credit art_L art_C art_pma_layout)). Qed.

Lemma eb0_inst : inst_ok_stmt cfg0 art_L art_C BUDGET0.           Proof. exact (as0_inst_ok cfg0 BUDGET0 eq_refl). Qed.
Lemma eb0_free_null : free_null_stmt cfg0 art_L BUDGET0.           Proof. exact (as0_free_null cfg0 BUDGET0). Qed.
Lemma eb0_h4e : h4e_stmt BUDGET0.                                  Proof. exact (as0_h4e BUDGET0). Qed.
Lemma eb0_icpt : icpt_ok_stmt cfg0 art_L art_IL BUDGET0.           Proof. exact (as0_icpt_ok cfg0 art_IL BUDGET0 art_IL_ok). Qed.
Lemma eb0_ext : ext_ok_stmt cfg0 art_L PMB.EXT BUDGET0.            Proof. exact (as0_ext_ok_pma cfg0 BUDGET0 eq_refl). Qed.
Lemma eb0_gap : gap_ok_stmt BUDGET0.                               Proof. exact (as0_gap_ok BUDGET0). Qed.
Lemma eb0_dla : dla_ok_stmt cfg0 art_L art_C art_IL.               Proof. exact (as0_dla_ok cfg0 art_IL art_IL_ok). Qed.
Lemma eb0_consts : drv_consts_stmt art_L art_C art_IL.             Proof. exact (as0_drv_consts art_IL art_IL_ok). Qed.
Lemma eb0_usage : usage_stmt cfg0.
Proof. exact (as0_usage_closed cfg0 art_L art_C art_IL BUDGET0 BUDGET0_lo40 BUDGET0_hi eb0_inst eb0_free_null eb0_h4e eb0_icpt eb0_dla eb0_consts). Qed.

Lemma eb0_fam : forall MAPS0 RESV0 NOACC0 BASE rn,
    bridge_static AsanUbsan.M.loaded_segments MAPS0 RESV0 NOACC0 (art_RES rn) (rn_HI rn) BUDGET0 EbrInv.LENMAX EbrInv.KMAX ->
    art_run_ok rn -> rn_tp rn = 0x67a180 -> rn_key rn = 0 -> rn_tsd rn = 0x69b638 -> rn_loff rn = 0x10 ->
    @PECASMB.fam_ok ScfgP_cfg0 art_L art_C art_IL art_LR (rn_ar rn) (fun D => art_iface art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET0 art_fsinv (art_rn_k rn D)).
Proof.
  intros MAPS0 RESV0 NOACC0 BASE rn STATIC ROK Htp Hkey0 Htsd Hloff.
  exact (art_fam_top MAPS0 RESV0 NOACC0 BASE BUDGET0 rn cfg0 art_IL eq_refl asegs_wx STATIC Htp Hkey0 Htsd Hloff art_IL_ok).
Qed.

Lemma eb0_lay : drv_lib_layoutA (PECASMB.LayA art_L P_SB) art_L.
Proof. unfold PECASMB.LayA. apply PECTB.lib_layout; [rewrite tk_SB| rewrite tb_SB]; lia. Qed.
Lemma eb0_cells : drv_lib_cellsA (PECASMB.LayA art_L P_SB).
Proof. unfold PECASMB.LayA. apply PECTB.lib_cells; [rewrite tk_SB| rewrite tb_SB]; lia. Qed.
Lemma eb0_budget : drv_budgetA art_L (PECASMB.LayA art_L P_SB).
Proof.
  intros n Hn. unfold credA, CAPk, adebit. unfold PECASMB.LayA. rewrite PECTB.LayA_credit, tk_SB, tb_SB.
  destruct (PMB.ly_cost art_L art_C art_pma_layout) as (HK & HL & HO). rewrite HK, HL, HO. cbn [fst snd]. lia.
Qed.

Lemma eb0_lsxfa : forall (ar : asan_run) (g : PMST.st) (M : word -> option byte),
  LibIface.ls_ok ((fun _ : asan_run => PECASMB.TopLSA) ar) g M -> exists ax : axv, atexit_cellsA M ax.
Proof. intros ar g M H. exact (PEBXC.lsx_atexit g M H). Qed.

#[local] Notation PTrue := (fun _ : list byte => True).
Lemma eb0_drv : drv_main_stmt cfg0 art_L art_C art_IL (PECASMB.LayA art_L P_SB) (fun _ => PECASMB.TopLSA) PTrue PTrue.
Proof. exact (as0_drv_main_closed cfg0 art_L art_C art_IL (PECASMB.LayA art_L P_SB) _ PTrue PTrue eb0_lay eb0_cells eb0_budget). Qed.

Lemma LIBBh : lib_ok_stmtFX (@PECASMB.fam_ok ScfgP_cfg0 art_L art_C art_IL art_LR) art_L (PECASMB.LayA art_L P_SB) PECASMB.TopLSA PTrue PTrue.
Proof. exact (lib_okFX_SB art_L art_C art_IL art_LR art_pma_layout art_IL_ok EbrIfaceMcmp.art_mcmp_cells). Qed.

Theorem eb0_run_on : forall sp brk0 mbase (rdraw : EntryDraw) (argv envp : list (list byte)) (fs : Fs.Fs) (stdin : InputStream) (uid gid hw : word) (groups : list word)
                         (net : NetQueue) (nofile sigmask : word) (abrt : bool) (ur : InputStream),
  valid_sp sp -> valid_brk EB.loaded_segments brk0 -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp -> valid_id uid -> valid_hwcap hw -> valid_fs fs ->
  srealizes EB.loaded_segments cfg0 (init_config EB.loaded_segments EB.init_pc EB.phdrs sp brk0 mbase rdraw AsanInitK.LIMIT
                                         (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur))
            (spec argv fs).
Proof.
  intros sp brk0 mbase rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur Hsp Hbrk Hva Hve Hfit Huid Hhw Hvfs.
  assert (HPO : ue_reach_ok PTrue (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur)) by (intros a0s path fdata _ _ _ _ _ _; exact I).
  exact (as0_realizes_spec_run cfg0 eq_refl eq_refl art_L art_C art_IL (PECASMB.LayA art_L P_SB) (fun _ => PECASMB.TopLSA) PMB.EXT BUDGET0 BUDGET0_lo40 BUDGET0_hi
           eb0_inst eb0_free_null eb0_h4e eb0_icpt eb0_ext eb0_gap PTrue PTrue
           (@PECASMB.fam_ok ScfgP_cfg0 art_L art_C art_IL art_LR) LIBBh eb0_fam eb0_dla eb0_consts eb0_drv eb0_usage eb0_lsxfa
           sp brk0 mbase rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur Hsp Hbrk Hva Hve Hfit Huid Hhw Hvfs HPO).
Qed.

Theorem ue_halts_both :
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source codes02 (mkImage EB.loaded_segments EB.init_pc EB.phdrs).
Proof.
  intros [sp brk mb rnd] inp Hen Hvalid Hsw.
  pose proof (valid_input_va_size _ Hvalid) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen.
  destruct Hen as [Hsp [Hbrk [Hmb Hfit]]].
  destruct Hvalid as (Hargv & Henvp & Hfs & _ & Hcreds & _ & _ & Hhw & _ & Hva & _).
  destruct inp as [argv envp fs0 stdin0 uid gid groups net nofile sigmask hw abt va ur tmp].
  cbn [in_argv in_envp in_uid in_hwcap in_va_size] in *. subst va.
  destruct Hcreds as [Hu _]. cbn [in_uid] in Hu.
  pose proof (eb0_run_on sp brk mb rnd argv envp (in_fs (mkProcInput_full argv envp fs0 stdin0 uid gid groups net nofile sigmask hw abt Sv48 ur tmp))
                stdin0 uid gid hw groups net nofile sigmask abt ur Hsp Hbrk Hargv Henvp Hfit Hu Hhw Hfs) as RUN.
  pose proof (top_of_guarded (bmK := bm_on_inst) _ _ _ _ _ _ _ _ _ _ _ frm_safe_Mb0 RUN) as RUN0.

  set (inp' := AsanInitK.inp argv envp (in_fs (mkProcInput_full argv envp fs0 stdin0 uid gid groups net nofile sigmask hw abt Sv48 ur tmp))
                             stdin0 uid gid hw groups net nofile sigmask abt ur) in *.
  change (must_exit_in_scfg forced_only_cfg codes02 (mkImage EB.loaded_segments EB.init_pc EB.phdrs) AsanInitK.LIMIT (mkEntry sp brk mb rnd) inp').
  change (~ run_scfg_budget_refused forced_only_cfg (mkImage EB.loaded_segments EB.init_pc EB.phdrs) AsanInitK.LIMIT (mkEntry sp brk mb rnd) inp') in Hsw.
  eapply (srealizes_init_must_exit (bmK := bm_on_inst) eq_refl cfg0).
  - exact RUN0.
  - apply exit_codes_in_spec.
  - apply kill_free_spec.
  - exact Hsw.
Qed.
