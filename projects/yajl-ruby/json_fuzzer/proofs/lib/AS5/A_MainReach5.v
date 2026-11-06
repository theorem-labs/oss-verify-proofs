(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import base.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.yajl_ruby.json_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import PropExec CatExec ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.XQ Require Import
  StoreOk AgentLib AsanAcct BackingAlgebra AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit AsanNodesMmLib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.AS5 Require Import
  AsanPlanImages5 HS2Asan RegsEquiv0 RegsEquiv0Cfg AsanStartup5 A_MainFacts A_ImgZero5 A_MainCells5 A_MainInit5 A_MainBridge5 A_MainRep5.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require RunCeiling MState Mem Cells Step InitMem Arr Frame FP.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require AImages AImageFacts NodesA.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanRep AsanRepInit AsanFakeStack AsanDepot AsanKern.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require AF_fakestack_rep AF_statics A_benv5 A_slack5 A_init5 ADrv_ctx AI_at_main AX_Exit AI_shadow AI_globals2 AI_lowshadow AYajlRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.TopA Require A_MainMS.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require R_TopCfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Reach.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 : word.
  Variable hw : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable uid : word.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Variable E : env.
  Variable R : bvmap 5 word.
  Variable FULL : word -> option byte.
  Variable model : Model.
  Variable hs : acs.
  Hypothesis Hhs : HS_MAIN hs.
  Hypothesis HC : cs_ok ASEGS ASAN5 AsanInit.LIMIT (SINV0 APH sp rdraw brk0 argv envp uid hw) (argH0 APH sp rdraw argv envp uid hw) fs E hs R FULL model.
  Context {RC__ : RunCeiling.RunCeiling}.
  Hypothesis RCSP : RunCeiling.rc_sp = bv_unsigned sp.

  #[local] Notation E0m := (aenv_of hs E).
  (* [comment removed for export] *)
  #[local] Notation SX X := (X sp rdraw brk0 hw argv envp fs uid E R FULL model hs Hhs HC).                          (* [comment removed for export] *)
  #[local] Notation SXV X := (X sp rdraw brk0 hw argv envp fs uid Hsp Hva Hve Hfit E R FULL model hs Hhs HC).         (* [comment removed for export] *)
  #[local] Notation SXR X := (X sp rdraw brk0 hw argv envp fs uid Hsp Hva Hve Hfit E R FULL model hs Hhs HC RCSP). (* [comment removed for export] *)
  #[local] Notation SXH X := (X sp rdraw brk0 hw argv envp fs uid Hsp Hva Hve Hfit E R FULL model hs Hhs HC).          (* [comment removed for export] *)
  Let usp := bv_unsigned sp.
  Let argc := Z.of_nat (length argv).
  (* [comment removed for export] *)
  #[local] Ltac by_cert X := first [ exact (SXR X) | exact (SXV X) | exact (SX X) | exact (SXH X) | (eapply X; eassumption) ].

  (* [comment removed for export] *)
  Theorem main_facts_of_cert :
    A_init5.main_facts5 FULL model E0m (fsbase_of E) (plumb_of E) (hr0_of sp E) (l0_of E) (segments_reserved ASEGS) A_EB0.
  Proof.
    constructor.
    - (* [comment removed for export] *) exact (hr0_ok sp E).
    - (* [comment removed for export] *) unfold A_EB0. lia.
    - (* [comment removed for export] *) by_cert init_envdepot.
    - (* [comment removed for export] *) by_cert init_hstot.
    - (* [comment removed for export] *) by_cert init_arep.
    - (* [comment removed for export] *) by_cert init_wf_env.
    - (* [comment removed for export] *) by_cert init_keys0.
    - (* [comment removed for export] *) by_cert init_akern.
    - (* [comment removed for export] *) by_cert init_kvm.
    - (* [comment removed for export] *) by_cert init_fsrep.
    - (* [comment removed for export] *) by_cert AI_at_main.at_main_icp.
    - (* [comment removed for export] *) by_cert AI_at_main.at_main_yst.
    - (* [comment removed for export] *) by_cert AI_at_main.at_main_low.
    - (* [comment removed for export] *) split; [by_cert AI_at_main.at_main_icp2|]. split; [by_cert AI_at_main.at_main_exit|].
      split; [by_cert init_fsenv|]. split; [by_cert init_amalloc_statics| by_cert init_athr5].
    - (* [comment removed for export] *) by_cert AI_at_main.at_main_stdio.
    - (* [comment removed for export] *) by_cert AI_at_main.at_main_ycl.
    - (* [comment removed for export] *) exact (A_MainFacts.main_halted sp rdraw brk0 hw argv envp fs uid E R FULL model hs HC).
    - (* [comment removed for export] *) by_cert init_minvA.
    - (* [comment removed for export] *) rewrite (A_MainFacts.main_limit sp rdraw brk0 hw argv envp fs uid E R FULL model hs HC). reflexivity.
    - (* [comment removed for export] *) by_cert main_mem_inv.
    - (* [comment removed for export] *) by_cert init_mat.
    - (* [comment removed for export] *) by_cert init_eager.
    - (* [comment removed for export] *) by_cert init_envok.
    - (* [comment removed for export] *) by_cert init_l0_ok.
  Qed.

  (* [comment removed for export] *)
  #[local] Notation gr n := (PropExec.getr R n%bv).
  Definition msR : machine_state :=
    MState.MS (Frame.mkR (Z_to_bv 64 0x91610) (Z_to_bv 64 (usp + -48)) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x5e0b10) (gr 5) (gr 6) (gr 7)
                         (Z_to_bv 64 (usp + 8)) (Z_to_bv 64 argc) (Z_to_bv 64 argc) (Z_to_bv 64 (usp + 8)) (Z_to_bv 64 (ADrv_ctx.envp_addr sp argv))
                         (gr 13) (gr 14) (gr 15) (gr 16) (gr 17) (Z_to_bv 64 0x81aa4) (Z_to_bv 64 (ADrv_ctx.envp_addr sp argv))
                         (gr 20) (gr 21) (gr 22) (gr 23) (gr 24) (gr 25) (gr 26) (gr 27) (gr 28) (gr 29) (gr 30) (gr 31))
              bvmap_empty (Z_to_bv 64 0x81aa4) (Z_to_bv 32 0) None FULL (PropExec.seg_rom AImages.asegs).

  Theorem main_ms_of_cert : A_MainMS.main_ms sp argv envp uid hw rdraw FULL msR.
  Proof.
    unfold A_MainMS.main_ms.
    exists (gr 5), (gr 6), (gr 7), (gr 13), (gr 14), (gr 15), (gr 16), (gr 17), (gr 20), (gr 21), (gr 22), (gr 23), (gr 24), (gr 25), (gr 26), (gr 27), (gr 28), (gr 29), (gr 30), (gr 31).
    exists bvmap_empty, (Z_to_bv 32 0).
    split; [reflexivity|].
    split; [unfold ADrv_ctx.LO; by_cert main_stk|].
    split; [by_cert main_mem_inv|].
    split; [by_cert main_aimg|].
    split; [by_cert main_astat| reflexivity].
  Qed.

  #[local] Ltac reg X := first [ exact (X sp rdraw brk0 hw argv envp fs uid E R FULL model hs Hhs HC) | exact (X sp rdraw brk0 hw argv envp fs uid Hva E R FULL model hs Hhs HC)
                               | exact (X sp rdraw brk0 hw argv envp fs uid Hsp Hva Hve Hfit E R FULL model hs Hhs HC) | exact (X sp rdraw brk0 hw argv envp fs uid Hsp Hva Hve Hfit E R FULL model hs HC) ].
  #[local] Ltac regr X := first [ rewrite (X sp rdraw brk0 hw argv envp fs uid E R FULL model hs Hhs HC) | rewrite (X sp rdraw brk0 hw argv envp fs uid Hva E R FULL model hs Hhs HC)
                                | rewrite (X sp rdraw brk0 hw argv envp fs uid Hsp Hva Hve Hfit E R FULL model hs Hhs HC) | rewrite (X sp rdraw brk0 hw argv envp fs uid Hsp Hva Hve Hfit E R FULL model hs HC) ].
  (* [comment removed for export] *)
  Lemma cfg_eqv_of_cert : cfg_eqv (mkCfg msR model) (cfg_of ASEGS R A_MAIN FULL model).
  Proof.
    rewrite A_MainFacts.LibBridge.cfg_of_MS. split; [| reflexivity]. cbn [cfg_ms].
    unfold msR, MState.MS. repeat split; cbn; try reflexivity.
    (* [comment removed for export] *)
    replace (Frame.mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) with (canonR R); [apply canonR_eqv0|].
    unfold canonR. f_equal.
    - reg A_MainFacts.main_ra.
    - reg A_MainFacts.main_sp.
    - reg A_MainFacts.main_gp.
    - reg A_MainFacts.main_tp.
    - reg A_MainFacts.main_s0.
    - reg A_MainFacts.main_s1.
    - reg A_MainFacts.main_a0.
    - reg A_MainFacts.main_a1.
    - transitivity (Z_to_bv 64 (bv_unsigned sp + 8 * Z.of_nat (length argv) + 16)); [reg A_MainFacts.main_a2 | unfold ADrv_ctx.envp_addr, InitMem.argc; f_equal; lia].
    - reg A_MainFacts.main_s2.
    - transitivity (Z_to_bv 64 (bv_unsigned sp + 8 * Z.of_nat (length argv) + 16)); [reg A_MainFacts.main_s3 | unfold ADrv_ctx.envp_addr, InitMem.argc; f_equal; lia].
  Qed.
End Reach.

(* [comment removed for export] *)
Theorem a_main_reach : forall (en : ExecEntry) (inp : ProcInput) (T : TSet),
    let RC := R_TopCfg.rc_of en in
    valid_entry (mkImage AImages.asegs AImages.a_init_pc AImages.a_phdrs) en inp -> valid_input inp -> T [] ->
    (forall (E0 : AsanState.aenv) (FSB0 : Z) (PL0 : AF_fakestack_rep.fs_plumb) (HR0 : list (Z * Z)) (L0 RES0 : list (word * word)) (EB0 : Z)
            (FULL : word -> option byte) (model : Model) (ms : machine_state),
        A_benv5.env0_ok5 E0 -> A_benv5.pl0_ok5 E0 PL0 -> A_init5.main_facts5 FULL model E0 FSB0 PL0 HR0 L0 RES0 EB0 ->
        m_fs model = in_fs inp -> m_fds model = ADrv_ctx.dfds_std ->
        A_MainMS.main_ms (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) FULL ms ->
        realizes_cfg (alloc_only_cfg false) AImages.asegs (mkCfg ms model) T) ->
    realizes_cfg (alloc_only_cfg false) AImages.asegs
      (init_config AImages.asegs AImages.a_init_pc AImages.a_phdrs (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) target_alloc_limit inp) T.
Proof.
  intros en inp T RC HE HI HT MAIN.
  apply (a_startup en inp T HE HI HT).
  intros hs Hhs E R FULL model HC.
  destruct en as [sp brk0 mbase rdraw]. destruct inp as [argv envp ifs stdin uid gid groups net nofile sigmask hw abrt va urnd tmp]. pose (fs := fs_seed_tmp ifs tmp).
  cbn [en_sp en_brk en_mmap_base en_draw in_argv in_envp in_fs in_image_fs in_tmp in_uid in_hwcap] in *.
  pose proof HE as (Hsp & Hbrk & Hmb & Hfit0).
  pose proof HI as (Hva & Hve & _ & _ & [Huid _] & _ & _ & _ & Habrt & Hva48 & _). cbn [in_argv in_envp in_uid in_gid in_abort_terminal in_va_size] in *.
  subst abrt va.
  assert (Hfit : entry_stack_fits sp argv envp) by exact Hfit0.
  assert (RCSP : @RunCeiling.rc_sp RC = bv_unsigned sp) by reflexivity.
  apply (realizes_cfg_eqv ASEGS (alloc_only_cfg false) (mkCfg (msR sp argv R FULL) model) T).
  - apply (MAIN (aenv_of hs E) (fsbase_of E) (plumb_of E) (hr0_of sp E) (l0_of E) (segments_reserved ASEGS) A_EB0 FULL model (msR sp argv R FULL)).
    + exact (init_env0_ok sp rdraw brk0 hw argv envp fs uid Hsp Hva Hve Hfit E R FULL model hs Hhs HC RCSP).
    + exact (init_pl0_ok sp rdraw brk0 hw argv envp fs uid Hsp Hva Hve Hfit E R FULL model hs Hhs HC RCSP).
    + exact (main_facts_of_cert sp rdraw brk0 hw argv envp fs uid Hsp Hva Hve Hfit E R FULL model hs Hhs HC RCSP).
    + exact (A_MainFacts.main_fs sp rdraw brk0 hw argv envp fs uid E R FULL model hs HC).
    + rewrite (A_MainFacts.main_fds sp rdraw brk0 hw argv envp fs uid E R FULL model hs Hhs HC). reflexivity.
    + exact (main_ms_of_cert sp rdraw brk0 hw argv envp fs uid Hsp Hva Hve Hfit E R FULL model hs Hhs HC RCSP).
  - exact (cfg_eqv_of_cert sp rdraw brk0 hw argv envp fs uid Hsp Hva Hve Hfit E R FULL model hs Hhs HC).
Qed.
