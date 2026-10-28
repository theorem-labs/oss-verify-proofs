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
  AsanNodesAux AsanNodesIface AsanNodesMmA AsanNodesMmB AsanNodesStartX AsanNodesStartXInit. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import SumsAsanClose AsanNodesStartXAsan Asan_code_startx.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AsanStartup () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.atable"; "Corelib.Init.Datatypes.nat"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.ABoot.AxSymExec3.AX2.env"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.Fs.Fs"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.x_sniff"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlanSound.APS.x_stmt"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.XSniff"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanInit.argH0"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanPlanImages.APH"; "Corelib.Init.Datatypes.true"; "Stdlib.ZArith.BinInt.Z.le"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Logic.not"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.ABoot.SpinAlg.srealizes"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanCertDefs.ASEGS"; "LinuxProcessSemantics.LinuxProcessSem.Run.init_config"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_both.M.init_pc"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanInit.LIMIT"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanInit.inp"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlanSound.APS.sd"; "RocqVerifyHarness.AgentSubmission.ABoot.ShapeAlg.t_nil"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanInit.E0"].


(* [comment removed for export] *)
Lemma XE0_sound : forall SEGS A nx0 LIMIT SP0 SINV argH FS0, emit_stmt SEGS A nx0 LIMIT XE0 SP0 SINV argH FS0.
Proof. intros ? ? ? ? ? ? ? ?. intros id args cs fd ps cs' E R FULL model T _ H _. discriminate H. Qed.

(* [comment removed for export] *)
Definition XN_A_STMT (SP0 : Z) (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (FS0 : Fs.Fs) : Prop :=
  ext_stmt ASEGS BOTH NX0 ALIMIT (XN_A NX0) SP0 SINV argH FS0.
Definition XB_A_STMT (SP0 : Z) (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (FS0 : Fs.Fs) : Prop :=
  ext2_stmt ASEGS BOTH NX0 ALIMIT XB_A SP0 SINV argH FS0.

(* [comment removed for export] *)
Lemma x_stmt_XSniff_vacuous : ltac2:(CDefT.buildp (gd_tbl_AsanStartup ()) "PSEGS,(0.$1.)PA,$2.Pnx0,$3.PLIMIT,$4.PSP0,$4.PSINV,P,$5.P,P,(6.&40.)(7.(6.&8.))SpPargH,P,$5.P,(6.&40.)$8.PFS0,$9.P,(:.$4.(;.R7.)=)(<.R9.R8.R7.R6.R5.R4.R3.R2.$=.)")
(* [comment removed for export] *).
Proof.
  intros SEGS A nx0 LIMIT SP0 SINV argH FS0 H0 args cs cs' E R FULL model T HC Hpre Hn Hk.
  cbn [node_x] in Hn. rewrite H0 in Hn. cbn in Hn. discriminate Hn.
Qed.

(* [comment removed for export] *)
Section XAll.
  Variable sp brk0 : word.
  Variable rdraw : EntryDraw.
  Variable argv envp : list (list byte).
  Variable FS0 : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Variable uid hw : word.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  #[local] Notation SINV0a := (SINV0 APH sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH0a := (argH0 APH sp rdraw argv envp uid hw).
  Variable SINV : env -> (word -> option byte) -> Prop.
  Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0a E M.
  Hypothesis SINV_frame : ltac2:(CDefT.buildp (gd_tbl_AsanStartup ()) "PE,$5.PM,Px,(6.&40.)(7.(6.&8.))PM',Px,(6.&40.)(7.(6.&8.))P,Pa,(6.&40.)P,(:.$8.(>.$?.Vsp,Vrdraw,Vargv,Venvp,Vuid,Vhw,R4.R1.)$10.)(:.(7.(6.&8.))A1.R3.R2.A1.R4.R2.)P,Pa,(6.&40.)P,(11.(12.&40.Vsp,)(12.&40.R1.))P,(13.(:.(7.(6.&8.))A1.R5.R2.(14.(6.&8.))))(13.(:.(7.(6.&8.))A1.R5.R3.(14.(6.&8.))))P,A2.VSINV,R5.R4.A2.VSINV,R6.R4.")
(* [comment removed for export] *).   (* [comment removed for export] *)
  Hypothesis SINV_agree : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.

  Let SP0 := bv_unsigned sp.
  Let SP0_ok := sp0_ok_usp sp Hsp.
  Let AH := argH0_high APH sp rdraw argv envp uid hw Hva.
  Let AA := argH0_agree APH sp rdraw argv envp uid hw.
  #[using="brk0 rdraw argv envp Hsp Hva Hve uid hw Hfit SINV_SINV0"] Lemma SINV_sp : forall E M, SINV E M -> uE_sp0 E = SP0.
  Proof. intros E M H. exact (SINV0_sp APH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit E M (SINV_SINV0 E M H)). Qed.

  #[using="brk0 Hsp Hva Hve Hfit SINV_SINV0 SINV_frame SINV_agree SP0_ok AH AA"] Theorem asan_node_x_sound_all : forall x, x_stmt ASEGS BOTH NX0 ALIMIT SP0 SINV argH0a FS0 x.
  Proof.
    intros [ | | | | | | | | | | ].
    - apply (asan_node_x_sound_XIMemset NX0 ALIMIT SINV _ SP0 SP0_ok AH AA SINV_frame SINV_agree FS0).
    - apply (asan_node_x_sound_XIMemcpy NX0 ALIMIT SINV _ SP0 SP0_ok AH AA SINV_frame SINV_agree FS0).
    - apply (asan_node_x_sound_XMemset NX0 ALIMIT SINV _ SP0 SP0_ok AH AA SINV_frame SINV_agree FS0).
    - apply (asan_node_x_sound_XMemcpy NX0 ALIMIT SINV _ SP0 SP0_ok AH AA SINV_frame SINV_agree FS0).
    - apply (asan_node_x_sound_XMemIsZero NX0 ALIMIT SINV _ SP0 SP0_ok AH AA SINV_frame SINV_agree FS0).
    - apply (node_x_sound_XEnvScan_asan_gen sp brk0 rdraw argv envp FS0 Hsp Hva Hve uid hw Hfit SINV SINV_SINV0 SINV_frame).
    - apply (node_x_sound_XPnScan_asan_gen sp brk0 rdraw argv envp FS0 Hsp Hva Hve uid hw Hfit SINV SINV_SINV0 SINV_frame SINV_agree).
    - apply x_sound_layout.
    - apply (asan_node_x_sound_XIStrncpy NX0 ALIMIT SINV _ SP0 SP0_ok AH AA SINV_frame SINV_agree FS0).
    - apply (asan_node_x_sound_XPopFree NX0 ALIMIT SINV _ SP0 SP0_ok AH AA SINV_frame SINV_agree FS0).
    - apply x_stmt_XSniff_vacuous. reflexivity.
  Qed.
End XAll.

(* [comment removed for export] *)
Section XAllN.
  Variable nx : nat.
  Hypothesis Hnx : (NX0 <= nx)%nat.
  Variable sp brk0 : word.
  Variable rdraw : EntryDraw.
  Variable argv envp : list (list byte).
  Variable FS0 : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Variable uid hw : word.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  #[local] Notation SINV0a := (SINV0 APH sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH0a := (argH0 APH sp rdraw argv envp uid hw).
  Variable SINV : env -> (word -> option byte) -> Prop.
  Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0a E M.
  Hypothesis SINV_frame : ltac2:(CDefT.buildp (gd_tbl_AsanStartup ()) "PE,$5.PM,Px,(6.&40.)(7.(6.&8.))PM',Px,(6.&40.)(7.(6.&8.))P,Pa,(6.&40.)P,(:.$8.(>.$?.Vsp,Vrdraw,Vargv,Venvp,Vuid,Vhw,R4.R1.)$10.)(:.(7.(6.&8.))A1.R3.R2.A1.R4.R2.)P,Pa,(6.&40.)P,(11.(12.&40.Vsp,)(12.&40.R1.))P,(13.(:.(7.(6.&8.))A1.R5.R2.(14.(6.&8.))))(13.(:.(7.(6.&8.))A1.R5.R3.(14.(6.&8.))))P,A2.VSINV,R5.R4.A2.VSINV,R6.R4.")
(* [comment removed for export] *).   (* [comment removed for export] *)
  Hypothesis SINV_agree : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.

  Let SP0 := bv_unsigned sp.
  Let SP0_ok := sp0_ok_usp sp Hsp.
  Let AH := argH0_high APH sp rdraw argv envp uid hw Hva.
  #[using="Type"] Lemma argH0_agreeN : forall E E' (a : word), env_agree nx E E' -> argH0a E a = argH0a E' a.
  Proof. intros. reflexivity. Qed.
  #[using="Hnx SINV_agree"] Lemma SINV_agreeN : forall E E' M, env_agree nx E E' -> SINV E M -> SINV E' M.
  Proof. intros E E' M Hag. apply SINV_agree. exact (env_agree_le _ _ _ _ Hag Hnx). Qed.
  Let AA := argH0_agreeN.
  Let SA := SINV_agreeN.
  Let SS : forall E M, SINV E M -> uE_sp0 E = SP0 :=
    fun E M H => SINV0_sp APH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit E M (SINV_SINV0 E M H).

  #[using="Hnx brk0 Hsp Hva Hve Hfit SINV_SINV0 SINV_frame SINV_agree SP0_ok AH AA SA"] Theorem asan_node_x_sound_allN : forall x, x_stmt ASEGS BOTH nx ALIMIT SP0 SINV argH0a FS0 x.
  Proof.
    intros [ | | | | | | | | | | ].
    - apply (asan_node_x_sound_XIMemset nx ALIMIT SINV _ SP0 SP0_ok AH AA SINV_frame SA FS0).
    - apply (asan_node_x_sound_XIMemcpy nx ALIMIT SINV _ SP0 SP0_ok AH AA SINV_frame SA FS0).
    - apply (asan_node_x_sound_XMemset nx ALIMIT SINV _ SP0 SP0_ok AH AA SINV_frame SA FS0).
    - apply (asan_node_x_sound_XMemcpy nx ALIMIT SINV _ SP0 SP0_ok AH AA SINV_frame SA FS0).
    - apply (asan_node_x_sound_XMemIsZero nx ALIMIT SINV _ SP0 SP0_ok AH AA SINV_frame SA FS0).
    - exact (x_sound_envscan ASEGS BOTH nx ALIMIT SINV argH0a FS0 asan_wx asan_in_hull asan_hull_ok SP0 SINV_frame
               W_dd408 W_dd40c W_dd410
               ltac:(cbn [x_envscan x_envscan_k BOTH]; lia)
               (fetch_lit _ _ _ _ eq_refl F_dd408) (fetch_lit _ _ _ _ eq_refl F_dd40c) (fetch_lit _ _ _ _ eq_refl F_dd410)
               ltac:(repeat split; reflexivity)
               D_dd408 D_dd40c D_dd410
               APH sp rdraw argv envp uid hw Hva Hve (sp_lo sp Hsp) (sp_hi sp Hsp) eq_refl
               (SINV0_vals APH sp rdraw brk0 argv envp Hsp Hva Hve uid hw Hfit SINV SINV_SINV0)
               (SINV0_envp APH sp rdraw brk0 argv envp uid hw SINV SINV_SINV0)).
    - exact (x_sound_pnscan ASEGS BOTH nx ALIMIT SINV argH0a FS0 asan_wx asan_in_hull asan_hull_ok SP0 AH AA SINV_frame SA
               W_dd4c4 W_dd4c8 W_dd4cc W_dd4d0 W_dd4d4
               ltac:(cbn [x_pnscan x_pnscan_k BOTH]; lia)
               (fetch_lit _ _ _ _ eq_refl F_dd4c4) (fetch_lit _ _ _ _ eq_refl F_dd4c8) (fetch_lit _ _ _ _ eq_refl F_dd4cc)
               (fetch_lit _ _ _ _ eq_refl F_dd4d0) (fetch_lit _ _ _ _ eq_refl F_dd4d4)
               ltac:(repeat split; reflexivity)
               D_dd4c4 D_dd4c8 D_dd4cc D_dd4d0 D_dd4d4
               APH sp rdraw argv envp uid hw Hva Hve (sp_lo sp Hsp) (sp_hi sp Hsp) eq_refl
               (SINV0_vals APH sp rdraw brk0 argv envp Hsp Hva Hve uid hw Hfit SINV SINV_SINV0)
               (SINV0_str0 APH sp rdraw brk0 argv envp Hva Hve uid hw Hfit SINV SINV_SINV0 SINV_frame)).
    - apply x_sound_layout.
    - apply (asan_node_x_sound_XIStrncpy nx ALIMIT SINV _ SP0 SP0_ok AH AA SINV_frame SA FS0).
    - apply (asan_node_x_sound_XPopFree nx ALIMIT SINV _ SP0 SP0_ok AH AA SINV_frame SA FS0).
    - apply x_stmt_XSniff_vacuous. reflexivity.
  Qed.
End XAllN.

Section Startup.
  (* [comment removed for export] *)
  Variable sp brk0 mbase : word.
  Variable rdraw : EntryDraw.            (* [comment removed for export] *)
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variables uid gid hw : word.           (* [comment removed for export] *)
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
  (* [comment removed for export] *)
  #[local] Notation SP0 := (bv_unsigned sp).

  (* [comment removed for export] *)
  Variable IT0 : itab.
  Hypothesis IT0_ok : itab_sound ASEGS IT0.
  (* [comment removed for export] *)
  Variable HS_asan : nat -> option acs.     (* [comment removed for export] *)
  Variable startup_plan : plan.
  Variable startup_shape : shape.
  Hypothesis startup_cert : s1_check IT0 HS_asan startup_plan = COk startup_shape.
  (* [comment removed for export] *)
  Hypothesis startup_guard : spin_guarded startup_plan = true.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Variable HOLES : nat -> env -> Fs.Fs -> TSet.
  Hypothesis HOLES_agree : forall h E E' fs', env_agree NX0 E E' -> HOLES h E fs' = HOLES h E' fs'.
  Hypothesis HOLES_nil : forall h E fs', HOLES h E fs' [].
  Hypothesis HOLES_sound : holes_stmt ASEGS BOTH ALIMIT HS_asan SP0 SINV argH HOLES fs.


  (* [comment removed for export] *)
  Let SP0_ok := sp0_ok_usp sp Hsp.
  Let AH := argH0_high APH sp rdraw argv envp uid hw Hva.
  Let AA := argH0_agree APH sp rdraw argv envp uid hw.
  Let SF := SINV0_frame APH sp rdraw brk0 argv envp uid hw.
  Let SA := SINV0_agree APH sp rdraw brk0 argv envp uid hw.
  Let SS := SINV0_sp APH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit.
  (* [comment removed for export] *)
  Let XN_sound : XN_A_STMT SP0 SINV argH fs := node_ext_sound_OBL ASEGS BOTH NX0 ALIMIT SP0 SINV argH fs AA SA.
  Let XB_sound : XB_A_STMT SP0 SINV argH fs :=
    node_noreplace_sound_OBL ASEGS BOTH NX0 ALIMIT SP0 SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_hull_cov SP0_ok AH AA SF SA SS.

  #[using="Hsp Hbrk Hva Hve Hfit Huid IT0 IT0_ok HS_asan startup_plan startup_cert startup_guard HOLES_agree HOLES_nil HOLES_sound SP0_ok AH AA SF SA SS XN_sound XB_sound"] Theorem asan_startup : ltac2:(CDefT.buildp (gd_tbl_AsanStartup ()) "(15.$16.(17.$16.$18.$?.Vsp,Vbrk0,Vmbase,Vrdraw,$19.(1:.Vargv,Venvp,Vfs,Vstdin,Vuid,Vgid,Vhw,Vgroups,Vnet,Vnofile,Vsigmask,Vurandom,))(1;.VHOLES,$1<.(1=.$?.Vsp,Vrdraw,Vbrk0,Vargv,Venvp,Vuid,Vhw,)Vfs,Vstartup_shape,))")
(* [comment removed for export] *).
  Proof.
    pose proof asan_img_facts as IMG.
    rewrite (init_cfg_eq ASEGS BOTH APH sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urandom AsanUbsan.M.init_pc eq_refl).
    pose proof (init_cs_ok ASEGS BOTH APH sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net IMG Hsp Hbrk Hva Hve Hfit Huid nofile sigmask urandom) as HC.   (* [comment removed for export] *)
    pose proof (check_sound ASEGS IT0 IT0_ok BOTH NX0 ALIMIT HS_asan (XN_A NX0) XE0 XB_A
              asan_wx asan_in_hull asan_hull_ok asan_shadow_ok SP0 SP0_ok SINV argH AH AA SF SA
              HOLES HOLES_agree HOLES_nil fs KC0) as C1.
    pose proof (C1 
              (AsanNodesMmB.node_sys_sound ASEGS BOTH NX0 ALIMIT SINV argH fs asan_res_len asan_hull_ok asan_shadow_ok SP0 SP0_ok AH AA SF SA)
              (AsanNodesMmB.node_brk2_sound ASEGS BOTH NX0 ALIMIT SINV argH fs asan_in_hull asan_res_len asan_hull_ok asan_hull_cov asan_shadow_ok SP0 SP0_ok AH SF SS)
              (node_mmap2_sound_OBL ASEGS BOTH NX0 ALIMIT SP0 SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_hull_cov SP0_ok AH AA SF SA SS)
              (node_mmapin_sound_OBL ASEGS BOTH NX0 ALIMIT SP0 SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_hull_cov SP0_ok AH AA SF SA SS)
              (node_mprotect2_sound_OBL ASEGS BOTH NX0 ALIMIT SP0 SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_hull_cov SP0_ok AH AA SF SA SS)
              (AsanNodesMmB.node_exit_sound ASEGS BOTH ALIMIT SINV argH fs SP0)) as C2.
    pose proof (C2 (asan_node_x_sound_all sp brk0 rdraw argv envp fs Hsp Hva Hve uid hw Hfit SINV (fun E M H => H) SF SA)
                   (asan_node_x_sound0_all NX0 ALIMIT SINV argH SP0 SP0_ok AH AA SF SA fs)) as C3.   (* [comment removed for export] *)
    pose proof (C3 (node_join_sound ASEGS BOTH NX0 ALIMIT SP0 SINV argH fs)) as C4.
    pose proof (C4 XN_sound (XE0_sound _ _ _ _ _ _ _ _) XB_sound HOLES_sound) as C5.
    pose proof (C5 FUEL BFUEL None startup_plan both_init startup_shape) as C6.
    pose proof (C6 startup_cert startup_guard) as C7.
    pose proof (C7 _ _ _ _ t_nil HC I eq_refl) as R.
    exact R.
  Qed.
End Startup.
