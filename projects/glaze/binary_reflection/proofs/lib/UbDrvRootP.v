(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Open.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.glaze.binary_reflection.images Require Import Ubsan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.UbStartup1 OSSVerify.Proofs.glaze.binary_reflection.lib.UbStartup OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS0Dir OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.TopProof4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ShapeHalts OSSVerify.Proofs.glaze.binary_reflection.lib.TopHalts OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocR0 OSSVerify.Proofs.glaze.binary_reflection.lib.GlzClosureUbsanInst OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvHooks OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS3Plan OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvSSound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS2Plan OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS2Sound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS2Glue OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS1Plan OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS1Sound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvInstP OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS0Plan. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.ArgvEnv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.RefLayout OSSVerify.Proofs.glaze.binary_reflection.lib.UbStartup1.UbStartupDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbStartup OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS0Dir.UbStartupFacts OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.ShapeLaws OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRoot OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzEntry OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs.UbImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.Spec4KF OSSVerify.Proofs.glaze.binary_reflection.lib.TopProof4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ShapeHalts OSSVerify.Proofs.glaze.binary_reflection.lib.TopHalts OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhIface3.UbMhSpec3 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.MhKInst OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocR0.UbMhMSpecI OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocR0 OSSVerify.Proofs.glaze.binary_reflection.lib.GlzClosureUbsanInst.UbMhMalloc3 OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvHooks.GuFuzzT OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvHooks.UbDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.UbDrvNodes OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvHooks OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS3Plan.UbDrvHooksS OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvSSound.UbDrvTSound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvSSound.UbDrvTInst OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS3Plan OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS2Plan OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvSSound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS2Sound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS2Glue OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS1Plan OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS1Sound.UbDrvGSound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS1Sound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS0Dir.UbDrvS0Sound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS0Dir.UbDrvS1Open OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvInstP OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.UbDrvNodes2 OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS0Dir.UbDrvNodes2Sound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS0Plan OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS0Dir.UbDrvESound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS0Dir.UbDrvS0Glue OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS0Dir.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.

#[local] Notation RSEGS := USEGS.
(* [comment removed for export] *)
Ltac lia ::= Zify.zify; xlia zchecker.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition RC_of (sp : word) (Hsp : valid_sp sp) : run_ceil :=
  run_ceil_of_top (bv_unsigned sp - stack_max_size) (alloc_top_rng_of_valid_sp sp Hsp).

(* [comment removed for export] *)
Definition MDL (tid : word) (brk mbase sp : word) (lim : Z) (inp : ProcInput) : Model :=
  with_tid tid (init_model (segments_reserved RSEGS) brk mbase sp lim inp).

Lemma MDL_facts : forall tid brk mbase sp lim inp,
  m_halted (MDL tid brk mbase sp lim inp) = None /\ m_vm_lazy (MDL tid brk mbase sp lim inp) = [] /\
  m_vm_materialized (MDL tid brk mbase sp lim inp) = [] /\ m_fds (MDL tid brk mbase sp lim inp) = fds_std /\
  m_fs (MDL tid brk mbase sp lim inp) = in_fs inp /\
  m_vmmaps (MDL tid brk mbase sp lim inp) = mkVmMapsFull (segments_reserved RSEGS) [] [] brk brk lim mbase sp.
Proof. intros. repeat split; reflexivity. Qed.

Lemma VM0_init : forall (lim : Z) tid brk mbase sp inp (Hsp : valid_sp sp),
  VMLIM <= lim ->
  valid_brk RSEGS brk ->
  @VM0 (RC_of sp Hsp) (MDL tid brk mbase sp lim inp).
Proof.
  intros lim tid brk mbase sp inp Hsp HL (B1 & B2 & B3).
  pose proof (@ceil_rng (RC_of sp Hsp)) as CR.
  assert (RT : reserved_top (segments_reserved RSEGS) = 704512) by (vm_compute; reflexivity).
  assert (BA : brk_aslr_max = 1073741824) by reflexivity.   (* [comment removed for export] *)
  assert (PS : page_size = 4096) by reflexivity.
  rewrite RT in B1, B2. rewrite BA in B2. rewrite PS in B3.
  unfold VM0. rewrite (proj2 (proj2 (proj2 (proj2 (proj2 (MDL_facts tid brk mbase sp lim inp)))))).
  cbn [vm_maps vm_noaccess vm_brk vm_start_brk vm_reserved vm_limit alloc_top vm_init_sp].
  split; [reflexivity|]. split; [reflexivity|].
  split. { split; [reflexivity|]. split; [exact B3|]. split; lia. }
  split; [reflexivity|]. split; [reflexivity|].
  exact HL.
Qed.

Lemma CEIL_init : forall sp (Hsp : valid_sp sp), @GlzConst.RunCeil.CEIL (RC_of sp Hsp) <= bv_unsigned sp - 8388608.
Proof. intros sp Hsp. cbn [GlzConst.RunCeil.CEIL RC_of run_ceil_of_top]. rewrite <- stack_max_size_val. apply page_floor_le. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Root.

(* [comment removed for export] *)
Theorem main_sound : forall (RC : run_ceil) sp0 av ev uid hw rdraw tid regs mem model,
  valid_argv av -> valid_envp ev -> valid_sp sp0 -> entry_stack_fits sp0 av ev -> 0 < bv_unsigned tid < 4194304 ->
  main_entry sp0 av ev uid hw rdraw tid regs mem ->
  m_halted model = None -> m_vm_lazy model = [] -> m_vm_materialized model = [] -> m_fds model = fds_std ->
  @VM0 RC model -> @GlzConst.RunCeil.CEIL RC <= bv_unsigned sp0 - 8388608 ->
  realizes RSEGS (cfgF RSEGS fx0 regs P_MAIN mem model) (spec av (m_fs model)).
Proof.
  intros RC sp0 av ev uid hw rdraw tid regs mem model Hva Hve Hvsp Hfits Htid ME Mh Ml Mm Mfd MV MC.
  apply (proj1 (SRP_rel _ _)).
  destruct av as [|a0 [|p [|x l]]].
  1,2,4: change (spec ?a (m_fs model)) with (t_die (msg_usage (nth 0 a [])) (m_fs model));
         apply (usage_sound (SRP) SRXP sp0 _ ev uid hw rdraw tid regs mem model Hva Hve Hvsp Hfits Htid ME Mh Ml Mm Mfd MC); cbn; lia.
  unfold spec.
  destruct (Nat.leb_spec 4096 (length p)) as [HL|HL].
  { exact (main_toolong_sound (SRP) SRXP sp0 [a0; p] ev uid hw rdraw tid regs mem model Hva Hve Hvsp Hfits Htid ME Mh Ml Mm Mfd MV MC a0 p eq_refl HL). }
  destruct (path_eqb p []) eqn:HE.
  { exact (main_noent_sound (SRP) SRXP sp0 [a0; p] ev uid hw rdraw tid regs mem model Hva Hve Hvsp Hfits Htid ME Mh Ml Mm Mfd MV MC a0 p eq_refl ltac:(lia) (or_introl HE)). }
  destruct (path_is_dirref p) eqn:HD.
  { exact (main_dir_sound (SRP) SRXP (fun fx => @malloc_first_alt RC fx) sp0 [a0; p] ev uid hw rdraw tid regs mem model Hva Hve Hvsp Hfits Htid ME Mh Ml Mm Mfd MV MC
             a0 p eq_refl ltac:(lia) HD). }
  assert (Hplain : openat_plain_name p = true).
  { apply (valid_argv_str_plain [a0; p] 0 Hva ltac:(cbn; lia)). unfold path_is_dirref in HD. apply Bool.orb_false_iff in HD as [HD _]. exact HD. }
  destruct (fs_lookup (m_fs model) p) as [data|] eqn:Hfs.
  2: { exact (main_noent_sound (SRP) SRXP sp0 [a0; p] ev uid hw rdraw tid regs mem model Hva Hve Hvsp Hfits Htid ME Mh Ml Mm Mfd MV MC a0 p eq_refl ltac:(lia)
                (or_intror (conj Hplain Hfs))). }
  (* [comment removed for export] *)
  pose proof (valid_argv_str_nz [a0; p] 1 Hva ltac:(cbn; lia)) as Hp0. cbn [nth] in Hp0.
  pose proof (valid_argv_str_nz [a0; p] 0 Hva ltac:(cbn; lia)) as Ha0. cbn [nth] in Ha0.
  exact (main_file_sound (SRP) SRXP HFRP (fun fx => @malloc_big_r RC fx) (fun fx => @malloc_alt_f RC fx) (fun fx => @malloc_first_alt RC fx)
           (GC_TP (fun fx => @malloc_katw RC fx)) (FZNP (fun fx => @malloc_katw RC fx)) (FZEP (fun fx => @malloc_katw RC fx))
           sp0 [a0; p] ev uid hw rdraw tid regs mem model Hva Hve Hvsp Hfits Htid ME Mh Ml Mm Mfd MV MC a0 p data eq_refl
           Hp0 ltac:(lia) HE Hplain Hfs
           (fun M1 len E fx R M model' HC => refused_sound (SRP) SRXP p data (TOPm sp0) M1 len E fx R M model' HC)
           (fun E fx R M model' e HC He => cantopen_sound (SRP) SRXP p a0 data (TOPm sp0) mem Hp0 Ha0 E fx R M model' e HC He)).
Qed.

(* [comment removed for export] *)
Theorem U_root_f_at : forall lim : Z, VMLIM <= lim -> root_obligation_core_f UIMG lim spec_of.
Proof.
  intros lim HL. unfold root_obligation_core_f. cbn [img_segments img_init_pc img_phdrs UIMG]. intros sp brk0 mb rnd inp He Hc.
  apply (proj1 (valid_entry_unfold _ _ _ _ _ _ _ _ Hc)) in He. destruct He as (Hsp & Hbrk & Hmb & Hfits).
  pose proof Hc as (Hva & Hve & _).
  apply (ref_startup_realizes sp brk0 mb rnd lim inp _ Hsp Hva Hve).
  intros tid regs mem Htid ME.
  pose proof (MDL_facts tid brk0 mb sp lim inp) as (Mh & Ml & Mm & Mfd & Mfs & _).
  pose proof (main_sound (RC_of sp Hsp) sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rnd tid regs mem
                (MDL tid brk0 mb sp lim inp) Hva Hve Hsp Hfits ltac:(unfold PID_MAX_ENVELOPE in Htid; lia) ME Mh Ml Mm Mfd
                (VM0_init lim tid brk0 mb sp inp Hsp HL Hbrk) (CEIL_init sp Hsp)) as X.
  rewrite Mfs in X. unfold cfgF, mkstF, MDL, P_MAIN in X.
  match goal with |- realizes _ (mkCfg (mkst _ ?pcw _ _) _) _ => replace pcw with (Z_to_bv 64 191300) by (apply bv_eq; reflexivity) end.
  exact X.
Qed.

(* [comment removed for export] *)
Theorem U_root_f_holds : U_root_f.
Proof. exact (U_root_f_at source_alloc_limit (proj1 (Z.leb_le VMLIM source_alloc_limit) ltac:(vm_compute; reflexivity))). Qed.

(* [comment removed for export] *)
Theorem U_root_holds : U_root.
Proof. exact (root_obligation_core_of_f UIMG target_alloc_limit spec_of (U_root_f_at target_alloc_limit (proj1 (Z.leb_le VMLIM target_alloc_limit) ltac:(vm_compute; reflexivity)))). Qed.
End Root.
