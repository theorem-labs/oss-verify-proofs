(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import
  PropExec ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctImages AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanCertDefs AsanPlanImages. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AsanInit
  AsanExtNodes AsanNoReplaceNode AsanExtNodesSound
  AsanNodesIface AsanNodesMmA AsanNodesMmB. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import SumsAsanClose AsanStartup. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import PlanCut.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AsanMainEntry () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.ABoot.AxSymExec3.AX2.env"; "LinuxProcessSemantics.LinuxProcessSem.Fs.Fs"; "RocqVerifyHarness.AgentSubmission.ABoot.ShapeAlg.TSet"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.shape"; "Corelib.Init.Datatypes.nil"; "LinuxProcessSemantics.LinuxProcessSem.State.event"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "only_holes"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlanSound.APS.sd"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.ABoot.ShapeAlg.t_nil"; "has_hole_all"; "RocqVerifyHarness.AgentSubmission.ABoot.ShapeAlg.t_eq"; "RocqVerifyHarness.AgentSubmission.ABoot.AxSymRun3.env_agree"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlanSound.APS.cs_ok"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanCertDefs.ASEGS"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.BOTH"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanCertDefs.ALIMIT"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanInit.SINV0"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanPlanImages.APH"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanInit.argH0"; "RocqVerifyHarness.AgentSubmission.ABoot.SpinAlg.srealizes"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlanSound.APS.cfg_of"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.pc"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fs"; "LinuxProcessSemantics.LinuxProcessSem.Run.init_config"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_both.M.init_pc"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanInit.LIMIT"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanInit.inp"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanInit.E0"; "Corelib.Init.Datatypes.prod"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.acs"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.pair"; "Piece.from_state"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlanSound.APS.holes_stmt"; "RocqVerifyHarness.AgentSubmission.ABoot.PlanCut.hs_tab"; "Corelib.Init.Datatypes.Some"].


(* [comment removed for export] *)
Fixpoint only_holes (s : shape) : bool :=
  match s with
  | SHole _ => true
  | SNil => true
  | SAlt2 a b => only_holes a && only_holes b
  | SCase _ _ a b => only_holes a && only_holes b
  | _ => false
  end.

Lemma sd_only_holes : ltac2:(CDefT.buildp (gd_tbl_AsanMainEntry ()) "PMAIN,P,$0.P,$1.$2.Ps,$3.PE,$0.Pfs',$1.P,PE,$0.Pfs',$1.A3.R6.R2.R1.(4.$5.)P,(6.$7.(8.R4.)$9.)Ptr,(:.$5.)P,(;.L,$<.R8.$=.R5.R4.R6.R1.)A3.R8.R6.R5.R2.")
(* [comment removed for export] *).
Proof.
  intros MAIN s E fs' Hnil.
  induction s as [| c | fd ps s IH | a IHa b IHb | e mid a IHa b IHb | h | ]; intros H tr X; cbn [only_holes] in H; try discriminate; cbn [sd] in X.
  - unfold t_nil in X. subst tr. apply Hnil.
  - apply andb_prop in H as [Ha Hb]. destruct X as [X|X]; [exact (IHa Ha tr X) | exact (IHb Hb tr X)].
  - apply andb_prop in H as [Ha Hb]. destruct (_ <=? _); [exact (IHa Ha tr X) | exact (IHb Hb tr X)].
  - exact X.
Qed.

(* [comment removed for export] *)
Fixpoint has_hole_all (s : shape) : bool :=
  match s with
  | SHole _ => true
  | SAlt2 a b => has_hole_all a || has_hole_all b
  | SCase _ _ a b => has_hole_all a && has_hole_all b
  | _ => false
  end.

Lemma sd_has_hole_all : ltac2:(CDefT.buildp (gd_tbl_AsanMainEntry ()) "PMAIN,P,$0.P,$1.$2.Ps,$3.PE,$0.Pfs',$1.P,(6.$7.(>.R3.)$9.)Ptr,(:.$5.)P,A3.R6.R4.R3.R1.(;.L,$<.R8.$=.R5.R4.R6.R2.)")
(* [comment removed for export] *).
Proof.
  intros MAIN s E fs'.
  induction s as [| c | fd ps s IH | a IHa b IHb | e mid a IHa b IHb | h | ]; intros H tr X; cbn [has_hole_all] in H; try discriminate; cbn [sd].
  - apply orb_prop in H as [H|H]; [left; exact (IHa H tr X) | right; exact (IHb H tr X)].
  - apply andb_prop in H as [Ha Hb]. destruct (_ <=? _); [exact (IHa Ha tr X) | exact (IHb Hb tr X)].
  - exact X.
Qed.

Lemma sd_main_eq : ltac2:(CDefT.buildp (gd_tbl_AsanMainEntry ()) "PMAIN,P,$0.P,$1.$2.Ps,$3.PE,$0.Pfs',$1.P,PE,$0.Pfs',$1.A3.R6.R2.R1.(4.$5.)P,(6.$7.(8.R4.)$9.)P,(6.$7.(>.R5.)$9.)(?.(;.L,$<.R8.$=.R5.R4.R6.)A2.R7.R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros MAIN s E fs' Hnil H1 H2 tr. split; [apply sd_only_holes; assumption | apply sd_has_hole_all; assumption].
Qed.

Section MainEntry.
  (* [comment removed for export] *)
  Variable sp brk0 mbase : word.
  Variable rdraw : EntryDraw.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variables uid gid hw : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nofile sigmask : word.   (* [comment removed for export] *)
  Variable urandom : InputStream.   (* [comment removed for export] *)
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk ASEGS brk0.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.

  #[local] Notation SINV := (SINV0 APH sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 APH sp rdraw argv envp uid hw).
  #[local] Notation E0a := (E0 APH sp rdraw brk0 argv envp uid hw).
  #[local] Notation SP0 := (bv_unsigned sp).

  (* [comment removed for export] *)
  Variable IT0 : itab.
  Hypothesis IT0_ok : itab_sound ASEGS IT0.
  Variable HS_asan : nat -> option acs.
  Variable HS0 : acs.
  Hypothesis HS_asan_only0 : forall h ch, HS_asan h = Some ch -> ch = HS0.
  Variable startup_plan : plan.
  Variable startup_shape : shape.
  Hypothesis startup_cert : s1_check IT0 HS_asan startup_plan = COk startup_shape.
  Hypothesis startup_guard : spin_guarded startup_plan = true.   (* [comment removed for export] *)
  Hypothesis startup_shape_holes : only_holes startup_shape = true.
  Hypothesis startup_shape_hole : has_hole_all startup_shape = true.

  (* [comment removed for export] *)
  Variable NX1 : nat.
  Hypothesis HNX1 : (NX0 <= NX1)%nat.
  Variable IT1 : itab.
  Hypothesis IT1_ok : itab_sound ASEGS IT1.
  Variable HS_main : nat -> option acs.
  Variable mainentry_plan : plan.
  Variable mainentry_shape : shape.
  Hypothesis mainentry_cert : s2_check NX1 IT1 HS_main HS0 mainentry_plan = COk mainentry_shape.
  Hypothesis mainentry_guard : spin_guarded mainentry_plan = true.   (* [comment removed for export] *)
  Hypothesis mainentry_shape_holes : only_holes mainentry_shape = true.
  Hypothesis mainentry_shape_hole : has_hole_all mainentry_shape = true.

  (* [comment removed for export] *)
  Variable MAIN : env -> Fs.Fs -> TSet.
  Hypothesis MAIN_agree : forall E E' fs', env_agree NX0 E E' -> MAIN E fs' = MAIN E' fs'.
  Hypothesis MAIN_nil : forall E fs', MAIN E fs' [].
  (* [comment removed for export] *)
  Hypothesis MAIN_sound : holes_stmt ASEGS BOTH ALIMIT HS_main SP0 SINV argH (fun _ => MAIN) fs.

  Let SP0_ok := sp0_ok_usp sp Hsp.
  Let AH := argH0_high APH sp rdraw argv envp uid hw Hva.
  Let AA1 := argH0_agreeN NX1 sp rdraw argv envp uid hw.
  Let SF := SINV0_frame APH sp rdraw brk0 argv envp uid hw.
  Let SA := SINV0_agree APH sp rdraw brk0 argv envp uid hw.
  Let SA1 : forall E E' M, env_agree NX1 E E' -> SINV E M -> SINV E' M := SINV_agreeN NX1 HNX1 SINV SA.
  Let SS := SINV0_sp APH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit.
  #[using="HNX1 MAIN_agree"] Lemma MAIN_agree1 : ltac2:(CDefT.buildp (gd_tbl_AsanMainEntry ()) "Ph,$<.PE,$0.PE',$0.Pfs',$1.P,(10.VNX1,R3.R2.)(6.$2.A3.L,$<.VMAIN,R5.R4.R2.A3.L,$<.VMAIN,R5.R3.R2.)")
(* [comment removed for export] *).
  Proof. intros h E E' fs' Hag. apply MAIN_agree. exact (env_agree_le _ _ _ _ Hag HNX1). Qed.
  #[using="MAIN_nil"] Lemma MAIN_nil1 : forall (h : nat) E fs', (fun _ : nat => MAIN) h E fs' [].
  Proof. intros. apply MAIN_nil. Qed.

  (* [comment removed for export] *)
  #[using="Hsp Hva Hve Hfit NX1 HNX1 IT1 IT1_ok HS_main mainentry_plan mainentry_cert mainentry_guard MAIN_agree MAIN_nil MAIN_sound SP0_ok AH AA1 SF SA SA1 SS"] Theorem mainentry_sound : ltac2:(CDefT.buildp (gd_tbl_AsanMainEntry ()) "PE,$0.PR,(11.&5.(12.&40.))PFULL,P,(12.&40.)(13.(12.&8.))Pmodel,$14.P,(15.$16.$17.$18.(19.&40.Vsp,)(1:.$1;.Vsp,Vrdraw,Vbrk0,Vargv,Venvp,Vuid,Vhw,)(1<.$1;.Vsp,Vrdraw,Vargv,Venvp,Vuid,Vhw,)Vfs,R4.VHS0,R3.R2.R1.)(1=.$16.(1>.$16.R4.(1?.VHS0,)R3.R2.)(;.L,$<.VMAIN,$=.R5.(20.R2.)Vmainentry_shape,))")
(* [comment removed for export] *).
  Proof.
    intros E R FULL model HC.
    pose proof (check_sound ASEGS IT1 IT1_ok BOTH NX1 ALIMIT HS_main (XN_A NX1) XE0 XB_A
              asan_wx asan_in_hull asan_hull_ok asan_shadow_ok SP0 SP0_ok SINV argH AH AA1 SF SA1
              (fun _ => MAIN) MAIN_agree1 MAIN_nil1 fs KC0) as C1.
    pose proof (C1
              (AsanNodesMmB.node_sys_sound ASEGS BOTH NX1 ALIMIT SINV argH fs asan_res_len asan_hull_ok asan_shadow_ok SP0 SP0_ok AH AA1 SF SA1)
              (AsanNodesMmB.node_brk2_sound ASEGS BOTH NX1 ALIMIT SINV argH fs asan_in_hull asan_res_len asan_hull_ok asan_hull_cov asan_shadow_ok SP0 SP0_ok AH SF SS)
              (node_mmap2_sound_OBL ASEGS BOTH NX1 ALIMIT SP0 SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_hull_cov SP0_ok AH AA1 SF SA1 SS)
              (node_mmapin_sound_OBL ASEGS BOTH NX1 ALIMIT SP0 SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_hull_cov SP0_ok AH AA1 SF SA1 SS)
              (node_mprotect2_sound_OBL ASEGS BOTH NX1 ALIMIT SP0 SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_hull_cov SP0_ok AH AA1 SF SA1 SS)
              (AsanNodesMmB.node_exit_sound ASEGS BOTH ALIMIT SINV argH fs SP0)) as C2.
    pose proof (C2 (asan_node_x_sound_allN NX1 HNX1 sp brk0 rdraw argv envp fs Hsp Hva Hve uid hw Hfit SINV (fun E M H => H) SF SA)
                   (asan_node_x_sound0_all NX1 ALIMIT SINV argH SP0 SP0_ok AH AA1 SF SA1 fs)) as C3.   (* [comment removed for export] *)
    pose proof (C3 (node_join_sound ASEGS BOTH NX1 ALIMIT SP0 SINV argH fs)) as C4.
    pose proof (C4 (node_ext_sound_OBL ASEGS BOTH NX1 ALIMIT SP0 SINV argH fs AA1 SA1) (XE0_sound _ _ _ _ _ _ _ _)
                   (node_noreplace_sound_OBL ASEGS BOTH NX1 ALIMIT SP0 SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_hull_cov SP0_ok AH AA1 SF SA1 SS)
                   MAIN_sound) as C5.
    pose proof (C5 FUEL BFUEL None mainentry_plan HS0 mainentry_shape mainentry_cert mainentry_guard E R FULL model t_nil HC I eq_refl) as R6.
    exact R6.
  Qed.

  (* [comment removed for export] *)
  #[using="Hsp Hva Hve Hfit HS0 HS_asan_only0 NX1 HNX1 IT1 IT1_ok HS_main mainentry_plan mainentry_shape mainentry_cert mainentry_guard mainentry_guard mainentry_shape_holes mainentry_shape_hole MAIN_agree MAIN_nil MAIN_sound SP0_ok AH AA1 SF SA SA1 SS"] Theorem startup_holes_sound : holes_stmt ASEGS BOTH ALIMIT HS_asan SP0 SINV argH (fun _ => MAIN) fs.
  Proof.
    intros h ch Hh E R FULL model HC. rewrite (HS_asan_only0 h ch Hh) in HC |- *.
    apply (srz_conseq ASEGS _ _ _ (mainentry_sound E R FULL model HC)).
    apply sd_main_eq; [exact MAIN_nil | exact mainentry_shape_holes | exact mainentry_shape_hole].
  Qed.

  (* [comment removed for export] *)
  #[using="Hsp Hbrk Hva Hve Hfit Huid IT0 IT0_ok HS_asan HS0 HS_asan_only0 startup_plan startup_cert startup_guard NX1 HNX1 IT1 IT1_ok HS_main mainentry_plan mainentry_shape mainentry_cert mainentry_guard mainentry_shape_holes mainentry_shape_hole MAIN_agree MAIN_nil MAIN_sound SP0_ok AH AA1 SF SA SA1 SS"] Theorem asan_boot_shape : ltac2:(CDefT.buildp (gd_tbl_AsanMainEntry ()) "(1=.$16.(21.$16.$22.$1;.Vsp,Vbrk0,Vmbase,Vrdraw,$23.(24.Vargv,Venvp,Vfs,Vstdin,Vuid,Vgid,Vhw,Vgroups,Vnet,Vnofile,Vsigmask,Vurandom,))(;.L,$<.VMAIN,$=.(25.$1;.Vsp,Vrdraw,Vbrk0,Vargv,Venvp,Vuid,Vhw,)Vfs,Vstartup_shape,))")
(* [comment removed for export] *).
  Proof.
    exact (asan_startup sp brk0 mbase rdraw argv envp fs stdin uid gid hw groups net nofile sigmask urandom Hsp Hbrk Hva Hve Hfit Huid
             IT0 IT0_ok HS_asan startup_plan startup_shape startup_cert startup_guard (fun _ => MAIN)
             (fun h E E' fs' Hag => MAIN_agree E E' fs' Hag) (fun h E fs' => MAIN_nil E fs') startup_holes_sound).
  Qed.

  #[using="Hsp Hbrk Hva Hve Hfit Huid IT0 IT0_ok HS_asan HS0 HS_asan_only0 startup_plan startup_shape startup_cert startup_guard startup_shape_holes startup_shape_hole NX1 HNX1 IT1 IT1_ok HS_main mainentry_plan mainentry_shape mainentry_cert mainentry_guard mainentry_shape_holes mainentry_shape_hole MAIN_agree MAIN_nil MAIN_sound SP0_ok AH AA1 SF SA SA1 SS"] Theorem asan_boot : ltac2:(CDefT.buildp (gd_tbl_AsanMainEntry ()) "(1=.$16.(21.$16.$22.$1;.Vsp,Vbrk0,Vmbase,Vrdraw,$23.(24.Vargv,Venvp,Vfs,Vstdin,Vuid,Vgid,Vhw,Vgroups,Vnet,Vnofile,Vsigmask,Vurandom,))A2.VMAIN,(25.$1;.Vsp,Vrdraw,Vbrk0,Vargv,Venvp,Vuid,Vhw,)Vfs,)")
(* [comment removed for export] *).
  Proof.
    apply (srz_conseq ASEGS _ _ _ asan_boot_shape).
    apply sd_main_eq; [exact MAIN_nil | exact startup_shape_holes | exact startup_shape_hole].
  Qed.
End MainEntry.

(* [comment removed for export] *)
Section Boot1.
  Variable sp brk0 mbase : word.
  Variable rdraw : EntryDraw.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variables uid gid hw : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nofile sigmask : word.   (* [comment removed for export] *)
  Variable urandom : InputStream.   (* [comment removed for export] *)
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk ASEGS brk0.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  #[local] Notation SINV := (SINV0 APH sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 APH sp rdraw argv envp uid hw).
  #[local] Notation E0a := (E0 APH sp rdraw brk0 argv envp uid hw).
  #[local] Notation SP0 := (bv_unsigned sp).

  Variable IT0 : itab.
  Hypothesis IT0_ok : itab_sound ASEGS IT0.
  Variable HS_asan : nat -> option acs.
  Variable startup_plan : plan.
  Variable startup_shape : shape.
  Hypothesis startup_cert : s1_check IT0 HS_asan startup_plan = COk startup_shape.
  Hypothesis startup_guard : spin_guarded startup_plan = true.   (* [comment removed for export] *)
  Hypothesis startup_shape_holes : only_holes startup_shape = true.
  Hypothesis startup_shape_hole : has_hole_all startup_shape = true.

  Variable MAIN : env -> Fs.Fs -> TSet.
  Hypothesis MAIN_agree : forall E E' fs', env_agree NX0 E E' -> MAIN E fs' = MAIN E' fs'.
  Hypothesis MAIN_nil : forall E fs', MAIN E fs' [].
  (* [comment removed for export] *)
  Hypothesis MAIN_sound : holes_stmt ASEGS BOTH ALIMIT HS_asan SP0 SINV argH (fun _ => MAIN) fs.

  #[using="Hsp Hbrk Hva Hve Hfit Huid IT0 IT0_ok HS_asan startup_plan startup_shape startup_cert startup_guard startup_shape_holes startup_shape_hole MAIN_agree MAIN_nil MAIN_sound"] Theorem asan_boot1 : ltac2:(CDefT.buildp (gd_tbl_AsanMainEntry ()) "(1=.$16.(21.$16.$22.$1;.Vsp,Vbrk0,Vmbase,Vrdraw,$23.(24.Vargv,Venvp,Vfs,Vstdin,Vuid,Vgid,Vhw,Vgroups,Vnet,Vnofile,Vsigmask,Vurandom,))A2.VMAIN,(25.$1;.Vsp,Vrdraw,Vbrk0,Vargv,Venvp,Vuid,Vhw,)Vfs,)")
(* [comment removed for export] *).
  Proof.
    apply (srz_conseq ASEGS _ _ _
             (asan_startup sp brk0 mbase rdraw argv envp fs stdin uid gid hw groups net nofile sigmask urandom Hsp Hbrk Hva Hve Hfit Huid
                IT0 IT0_ok HS_asan startup_plan startup_shape startup_cert startup_guard (fun _ => MAIN)
                (fun h E E' fs' Hag => MAIN_agree E E' fs' Hag) (fun h E fs' => MAIN_nil E fs') MAIN_sound)).
    apply sd_main_eq; [exact MAIN_nil | exact startup_shape_holes | exact startup_shape_hole].
  Qed.
End Boot1.

(* [comment removed for export] *)
Section Piece.
  Variable sp brk0 : word.
  Variable rdraw : EntryDraw.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variables uid hw : word.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.

  #[local] Notation SINV := (SINV0 APH sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 APH sp rdraw argv envp uid hw).
  #[local] Notation SP0 := (bv_unsigned sp).

  Variable MAIN : env -> Fs.Fs -> TSet.
  Hypothesis MAIN_agree : forall E E' fs', env_agree NX0 E E' -> MAIN E fs' = MAIN E' fs'.
  Hypothesis MAIN_nil : forall E fs', MAIN E fs' [].

  (* [comment removed for export] *)
  Definition from_state (cs : acs) : Prop := ltac2:(CDefT.buildp (gd_tbl_AsanMainEntry ()) "PE,$0.PR,(11.&5.(12.&40.))PFULL,P,(12.&40.)(13.(12.&8.))Pmodel,$14.P,(15.$16.$17.$18.(19.&40.Vsp,)(1:.$1;.Vsp,Vrdraw,Vbrk0,Vargv,Venvp,Vuid,Vhw,)(1<.$1;.Vsp,Vrdraw,Vargv,Venvp,Vuid,Vhw,)Vfs,R4.O1.R3.R2.R1.)(1=.$16.(1>.$16.R4.(1?.O1.)R3.R2.)A2.VMAIN,R5.(20.R2.))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Lemma hs_tab_holes : ltac2:(CDefT.buildp (gd_tbl_AsanMainEntry ()) "Pl,(:.(26.$<.$27.))P,Ph,$<.Pcs,$27.P,(28.(26.$<.$27.)(29.$<.$27.R2.R1.)R3.)(2:.R2.)(2;.$16.$17.$18.(2<.R2.)(19.&40.Vsp,)(1:.$1;.Vsp,Vrdraw,Vbrk0,Vargv,Venvp,Vuid,Vhw,)(1<.$1;.Vsp,Vrdraw,Vargv,Venvp,Vuid,Vhw,)L,$<.VMAIN,Vfs,)")
(* [comment removed for export] *).
  Proof.
    intros l Hl. induction l as [|[h0 cs0] l IH]; intros h ch Hh E R FULL model HC; cbn [hs_tab] in Hh; [discriminate Hh|].
    destruct (Nat.eqb h h0) eqn:He.
    - injection Hh as <-. exact (Hl h0 cs0 (or_introl eq_refl) E R FULL model HC).
    - exact (IH (fun h' cs' Hin => Hl h' cs' (or_intror Hin)) h ch Hh E R FULL model HC).
  Qed.

  (* [comment removed for export] *)
  Lemma hs_const_holes : ltac2:(CDefT.buildp (gd_tbl_AsanMainEntry ()) "PHS,P,$<.(13.$27.)Pcs0,$27.P,Ph,$<.Pch,$27.P,(6.(13.$27.)A1.R4.R2.(2=.$27.R1.))(6.$27.R2.R4.)P,(2:.R2.)(2;.$16.$17.$18.R4.(19.&40.Vsp,)(1:.$1;.Vsp,Vrdraw,Vbrk0,Vargv,Venvp,Vuid,Vhw,)(1<.$1;.Vsp,Vrdraw,Vargv,Venvp,Vuid,Vhw,)L,$<.VMAIN,Vfs,)")
(* [comment removed for export] *).
  Proof. intros HS cs0 Honly H0 h ch Hh E R FULL model HC. rewrite (Honly h ch Hh) in HC |- *. exact (H0 E R FULL model HC). Qed.

  Variable nx : nat.
  Hypothesis Hnx : (NX0 <= nx)%nat.
  Variable IT : itab.
  Hypothesis IT_ok : itab_sound ASEGS IT.
  Variable HS : nat -> option acs.
  Variable cs0 : acs.
  Variable p : plan.
  Variable s : shape.
  Hypothesis cert : s2_check nx IT HS cs0 p = COk s.
  Hypothesis cert_guard : spin_guarded p = true.   (* [comment removed for export] *)
  Hypothesis s_holes : only_holes s = true.
  Hypothesis s_hole : has_hole_all s = true.
  Hypothesis HS_sound : holes_stmt ASEGS BOTH ALIMIT HS SP0 SINV argH (fun _ => MAIN) fs.

  Let SP0_ok := sp0_ok_usp sp Hsp.
  Let AH := argH0_high APH sp rdraw argv envp uid hw Hva.
  Let AA1 := argH0_agreeN nx sp rdraw argv envp uid hw.
  Let SF := SINV0_frame APH sp rdraw brk0 argv envp uid hw.
  Let SA := SINV0_agree APH sp rdraw brk0 argv envp uid hw.
  Let SA1 : forall E E' M, env_agree nx E E' -> SINV E M -> SINV E' M := SINV_agreeN nx Hnx SINV SA.
  Let SS := SINV0_sp APH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit.
  Lemma MAIN_agreeP : ltac2:(CDefT.buildp (gd_tbl_AsanMainEntry ()) "Ph,$<.PE,$0.PE',$0.Pfs',$1.P,(10.Vnx,R3.R2.)(6.$2.A3.L,$<.VMAIN,R5.R4.R2.A3.L,$<.VMAIN,R5.R3.R2.)")
(* [comment removed for export] *).
  Proof. intros h E E' fs' Hag. apply MAIN_agree. exact (env_agree_le _ _ _ _ Hag Hnx). Qed.
  Lemma MAIN_nilP : forall (h : nat) E fs', (fun _ : nat => MAIN) h E fs' [].
  Proof. intros. apply MAIN_nil. Qed.

  Theorem piece_shape_sound : ltac2:(CDefT.buildp (gd_tbl_AsanMainEntry ()) "PE,$0.PR,(11.&5.(12.&40.))PFULL,P,(12.&40.)(13.(12.&8.))Pmodel,$14.P,(15.$16.$17.$18.(19.&40.Vsp,)(1:.$1;.Vsp,Vrdraw,Vbrk0,Vargv,Venvp,Vuid,Vhw,)(1<.$1;.Vsp,Vrdraw,Vargv,Venvp,Vuid,Vhw,)Vfs,R4.Vcs0,R3.R2.R1.)(1=.$16.(1>.$16.R4.(1?.Vcs0,)R3.R2.)(;.L,$<.VMAIN,$=.R5.(20.R2.)Vs,))")
(* [comment removed for export] *).
  Proof.
    intros E R FULL model HC.
    pose proof (check_sound ASEGS IT IT_ok BOTH nx ALIMIT HS (XN_A nx) XE0 XB_A
              asan_wx asan_in_hull asan_hull_ok asan_shadow_ok SP0 SP0_ok SINV argH AH AA1 SF SA1
              (fun _ => MAIN) MAIN_agreeP MAIN_nilP fs KC0) as C1.
    pose proof (C1
              (AsanNodesMmB.node_sys_sound ASEGS BOTH nx ALIMIT SINV argH fs asan_res_len asan_hull_ok asan_shadow_ok SP0 SP0_ok AH AA1 SF SA1)
              (AsanNodesMmB.node_brk2_sound ASEGS BOTH nx ALIMIT SINV argH fs asan_in_hull asan_res_len asan_hull_ok asan_hull_cov asan_shadow_ok SP0 SP0_ok AH SF SS)
              (node_mmap2_sound_OBL ASEGS BOTH nx ALIMIT SP0 SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_hull_cov SP0_ok AH AA1 SF SA1 SS)
              (node_mmapin_sound_OBL ASEGS BOTH nx ALIMIT SP0 SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_hull_cov SP0_ok AH AA1 SF SA1 SS)
              (node_mprotect2_sound_OBL ASEGS BOTH nx ALIMIT SP0 SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_hull_cov SP0_ok AH AA1 SF SA1 SS)
              (AsanNodesMmB.node_exit_sound ASEGS BOTH ALIMIT SINV argH fs SP0)) as C2.
    pose proof (C2 (asan_node_x_sound_allN nx Hnx sp brk0 rdraw argv envp fs Hsp Hva Hve uid hw Hfit SINV (fun E M H => H) SF SA)
                   (asan_node_x_sound0_all nx ALIMIT SINV argH SP0 SP0_ok AH AA1 SF SA1 fs)) as C3.   (* [comment removed for export] *)
    pose proof (C3 (node_join_sound ASEGS BOTH nx ALIMIT SP0 SINV argH fs)) as C4.
    pose proof (C4 (node_ext_sound_OBL ASEGS BOTH nx ALIMIT SP0 SINV argH fs AA1 SA1) (XE0_sound _ _ _ _ _ _ _ _)
                   (node_noreplace_sound_OBL ASEGS BOTH nx ALIMIT SP0 SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_hull_cov SP0_ok AH AA1 SF SA1 SS)
                   HS_sound) as C5.
    exact (C5 FUEL BFUEL None p cs0 s cert cert_guard E R FULL model t_nil HC I eq_refl).
  Qed.

  Theorem piece_sound : from_state cs0.
  Proof.
    intros E R FULL model HC.
    apply (srz_conseq ASEGS _ _ _ (piece_shape_sound E R FULL model HC)).
    apply sd_main_eq; [exact MAIN_nil | exact s_holes | exact s_hole].
  Qed.
End Piece.
