(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.simdjson.fuzz_implementations.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import PropExec.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import
  ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctImagesB AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2 AsanPlanImagesB AsanInit AsanTablesB
  AsanNodesIface AsanNodesMmA AsanNodesMmB SumsBothClose AsanNodesStartX AsanNodesStartXBoth AsanSmearB AsanHeapSortB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

Definition XN0 (id : nat) (args : list expr) (cs : acs) : option acs := None.
Definition XE0 (id : nat) (args : list expr) (cs : acs) : option (Z * list spiece * acs) := None.
Definition XB0 (id : nat) (args : list expr) (cs : acs) : option (acs * acs) := None.

Lemma XN0_sound : forall SEGS A nx0 LIMIT SINV argH FS0, ext_stmt SEGS A nx0 LIMIT XN0 SINV argH FS0.
Proof. intros ? ? ? ? ? ? ?. intros id args cs cs' E R FULL model T _ _ H. discriminate H. Qed.
Lemma XE0_sound : forall SEGS A nx0 LIMIT SINV argH FS0, emit_stmt SEGS A nx0 LIMIT XE0 SINV argH FS0.
Proof. intros ? ? ? ? ? ? ?. intros id args cs fd ps cs' E R FULL model T _ H _. discriminate H. Qed.
Lemma XB0_sound : forall SEGS A nx0 LIMIT SINV argH FS0, ext2_stmt SEGS A nx0 LIMIT XB0 SINV argH FS0.
Proof. intros ? ? ? ? ? ? ?. intros id args cs csa csb E R FULL model TA TB _ H. discriminate H. Qed.

Section XAll.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 : word.
  Variables argv envp : list (list byte).
  Variable FS0 : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Variables uid hw : word.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0 APH sp rdraw brk0 argv envp uid hw E M.
  Hypothesis SINV_frame : forall E M M', (forall a, argH0 APH sp rdraw argv envp uid hw E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Hypothesis SINV_agree : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.

  Theorem asan_node_x_sound_all : forall x, x_stmt ASEGS ASAN_B NX0 AsanInit.LIMIT SINV (argH0 APH sp rdraw argv envp uid hw) FS0 x.
  Proof.
    pose proof (argH0_high APH sp rdraw argv envp uid hw Hsp Hva) as AH. pose proof (argH0_agree APH sp rdraw argv envp uid hw) as AA.
    intros [ | | | | | | | | | | | ].
    - exact (asan_node_x_sound_XIMemset NX0 AsanInit.LIMIT SINV _ AH AA SINV_frame SINV_agree FS0).
    - exact (asan_node_x_sound_XIMemcpy NX0 AsanInit.LIMIT SINV _ AH AA SINV_frame SINV_agree FS0).
    - exact (asan_node_x_sound_XMemset NX0 AsanInit.LIMIT SINV _ AH AA SINV_frame SINV_agree FS0).
    - exact (asan_node_x_sound_XMemcpy NX0 AsanInit.LIMIT SINV _ AH AA SINV_frame SINV_agree FS0).
    - exact (asan_node_x_sound_XMemIsZero NX0 AsanInit.LIMIT SINV _ AH AA SINV_frame SINV_agree FS0).
    - exact (node_x_sound_XEnvScan_asan_gen sp rdraw brk0 argv envp FS0 Hsp Hva Hve uid hw Hfit SINV SINV_SINV0 SINV_frame).
    - exact (node_x_sound_XPnScan_asan_gen sp rdraw brk0 argv envp FS0 Hsp Hva Hve uid hw Hfit SINV SINV_SINV0 SINV_frame SINV_agree).
    - apply x_sound_layout.
    - exact (asan_node_x_sound_XIStrncpy NX0 AsanInit.LIMIT SINV _ AH AA SINV_frame SINV_agree FS0).
    - exact (asan_node_x_sound_XPopFree NX0 AsanInit.LIMIT SINV _ AH AA SINV_frame SINV_agree FS0).
    - exact (asan_node_x_sound_XSniff NX0 AsanInit.LIMIT SINV _ FS0 asan_wx asan_in_hull asan_hull_ok AH SINV_frame).
    - eapply asan_node_x_sound_XHeapSort; eassumption.
  Qed.
End XAll.

Section Startup.

  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variables brk0 mbase : word.
  Variables argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variables uid gid hw : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk ASEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.

  #[local] Notation SINV := (SINV0 APH sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 APH sp rdraw argv envp uid hw).
  #[local] Notation E0a := (E0 APH sp rdraw brk0 argv envp uid hw).
  #[local] Notation LIM := AsanInit.LIMIT.

  Variable IT0 : itab.
  Hypothesis IT0_ok : itab_sound ASEGS IT0.

  Variable HS_asan : nat -> option acs.
  Variable startup_plan : plan.
  Variable startup_shape : shape.
  Variables KC0 BFUEL FUEL : nat.
  Hypothesis startup_cert :
    check ASEGS IT0 ASAN_B NX0 LIM XN0 XE0 XB0 HS_asan KC0 BFUEL FUEL None asan_b_init startup_plan = COk startup_shape.

  Variable HOLES : nat -> env -> Fs.Fs -> TSet.
  Hypothesis HOLES_agree : forall h E E' fs', env_agree NX0 E E' -> HOLES h E fs' = HOLES h E' fs'.
  Hypothesis HOLES_nil : forall h E fs', HOLES h E fs' [].
  Hypothesis HOLES_sound : holes_stmt ASEGS ASAN_B NX0 LIM HS_asan SINV argH HOLES fs.

  Let AH := argH0_high APH sp rdraw argv envp uid hw Hsp Hva.
  Let AA := argH0_agree APH sp rdraw argv envp uid hw.
  Let SF := SINV0_frame APH sp rdraw brk0 argv envp uid hw.
  Let SA := SINV0_agree APH sp rdraw brk0 argv envp uid hw.

  Theorem asan_startup :
    srealizes ASEGS (init_config ASEGS AsanUbsan.M.init_pc APH sp brk0 mbase rdraw LIM
                                 (AsanInit.inp argv envp fs stdin uid gid hw groups net))
              (sd HOLES t_nil E0a fs startup_shape).
  Proof.
    pose proof asan_img_facts as IMG.
    rewrite (init_cfg_eq ASEGS ASAN_B APH sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net AsanUbsan.M.init_pc eq_refl).
    pose proof (init_cs_ok ASEGS ASAN_B APH sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net IMG Hsp Hbrk Hmb Hva Hve Hfit Huid) as HC.
    exact (check_sound ASEGS IT0 IT0_ok ASAN_B NX0 LIM HS_asan XN0 XE0 XB0
              asan_wx asan_in_hull asan_hull_ok asan_shadow_ok SINV argH AH AA SF SA
              HOLES HOLES_agree HOLES_nil fs KC0
              (AsanNodesMmB.node_sys_sound ASEGS ASAN_B NX0 LIM SINV argH fs asan_res_len asan_hull_ok asan_shadow_ok AA SF SA)
              (AsanNodesMmB.node_brk2s_sound ASEGS ASAN_B NX0 LIM SINV argH fs asan_in_hull asan_res_hull asan_hull_ok asan_shadow_ok AH SF)
              (node_mmap2_sound_OBL ASEGS ASAN_B NX0 LIM SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok AH AA SF SA asan_hull_cover)
              (node_mmapin_sound_OBL ASEGS ASAN_B NX0 LIM SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok AH AA SF SA asan_hull_cover)
              (node_mprotect2_sound_OBL ASEGS ASAN_B NX0 LIM SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok AH AA SF SA asan_hull_cover)
              (AsanNodesMmB.node_exit_sound ASEGS ASAN_B NX0 LIM SINV argH fs)
              (asan_node_x_sound_all sp rdraw brk0 argv envp fs Hsp Hva Hve uid hw Hfit SINV (fun E M H => H) SF SA)
              (node_join_sound ASEGS ASAN_B NX0 LIM SINV argH fs)
              (XN0_sound _ _ _ _ _ _ _) (XE0_sound _ _ _ _ _ _ _) (XB0_sound _ _ _ _ _ _ _)
              HOLES_sound FUEL BFUEL None startup_plan asan_b_init startup_shape startup_cert
              _ _ _ _ t_nil HC I eq_refl).
  Qed.
End Startup.
