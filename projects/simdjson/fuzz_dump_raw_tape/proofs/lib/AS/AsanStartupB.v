(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the start-up soundness is stated over the run's whole launch input and its kernel's CONFIG_RSEQ flag, with the launch premises the start state needs; taken in part from projects/simdjson/fuzz_ondemand/proofs/lib/AS/AsanStartupB.v, 83 lines within its lines 17-185. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.simdjson.fuzz_dump_raw_tape.images Require Import AsanUbsan.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import PropExec.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import
  ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctImagesB AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2 AsanPlanImagesB AsanInit AsanTablesB
  AsanNodesIface AsanNodesMmA AsanNodesMmB SumsBothClose AsanNodesStartX AsanNodesStartXBoth AsanSmearB AsanHeapSortB.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require AsanCeil.
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
  (* LPS 727298f3: the run, as AS/AsanInit.v's Section Init and AS/AsanNodesStartXBoth.v name it --
     the run's whole launch input [inp], whose kernel build carries
     CONFIG_RSEQ, and the launch hypotheses those sections read.  The rseq
     flag is no longer a variable of its own: it is [kb_rseq] of the run's
     kernel, free in [valid_input], so neither launch is excluded. *)
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variables brk0 mbase : word.
  Variable FS0 : Fs.Fs.
  (* the run's whole launch input, as AS/AsanInit.v's Section Init takes it *)
  Variable inp : ProcInput.
  #[local] Notation INP := inp.
  #[local] Notation argv := (in_argv inp).
  #[local] Notation envp := (in_envp inp).
  #[local] Notation uid := (in_uid inp).
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk ASEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hzr : AsanCeil.zero_random_draw (ed_random rdraw).
  Hypothesis Hlaunch : valid_launch INP.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.
  #[local] Notation RZ := (rseq_z (kb_rseq (in_kernel INP))).
  #[local] Notation SINV0a := (SINV0 ASAN_B APH sp rdraw brk0 mbase inp).
  #[local] Notation argH0a := (argH0 sp rdraw inp).
  Variable SINV : env -> (word -> option byte) -> Prop.
  Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0a E M.
  Hypothesis SINV_frame : forall E M M', (forall a, argH0a E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Hypothesis SINV_agree : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.

  Theorem asan_node_x_sound_all : forall x, x_stmt ASEGS ASAN_B NX0 AsanInit.LIMIT RZ SINV argH0a FS0 x.
  Proof.
    assert (AH : forall E (a : word), argH0a E a = true -> CEIL <= bv_unsigned a)
      by (intros E a H; eapply argH0_high; eassumption).
    assert (AA : forall E E' (a : word), env_agree NX0 E E' -> argH0a E a = argH0a E' a)
      by (intros E E' a _; reflexivity).
    intros [ | | | | | | | | | | | ].
    - exact (asan_node_x_sound_XIMemset NX0 AsanInit.LIMIT RZ SINV _ AH AA SINV_frame SINV_agree FS0).
    - exact (asan_node_x_sound_XIMemcpy NX0 AsanInit.LIMIT RZ SINV _ AH AA SINV_frame SINV_agree FS0).
    - exact (asan_node_x_sound_XMemset NX0 AsanInit.LIMIT RZ SINV _ AH AA SINV_frame SINV_agree FS0).
    - exact (asan_node_x_sound_XMemcpy NX0 AsanInit.LIMIT RZ SINV _ AH AA SINV_frame SINV_agree FS0).
    - exact (asan_node_x_sound_XMemIsZero NX0 AsanInit.LIMIT RZ SINV _ AH AA SINV_frame SINV_agree FS0).
    - eapply node_x_sound_XEnvScan_asan_gen; eassumption.
    - eapply node_x_sound_XPnScan_asan_gen; eassumption.
    - apply x_sound_layout.
    - exact (asan_node_x_sound_XIStrncpy NX0 AsanInit.LIMIT RZ SINV _ AH AA SINV_frame SINV_agree FS0).
    - exact (asan_node_x_sound_XPopFree NX0 AsanInit.LIMIT RZ SINV _ AH AA SINV_frame SINV_agree FS0).
    - exact (asan_node_x_sound_XSniff NX0 AsanInit.LIMIT RZ SINV _ FS0 asan_wx asan_in_hull asan_hull_ok AH SINV_frame).
    - eapply asan_node_x_sound_XHeapSort; eassumption.
  Qed.
End XAll.

Section Startup.

  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variables brk0 mbase : word.
  (* LPS 727298f3: the run's whole launch input, as AS/AsanInit.v's Section Init
     takes it; its kernel's CONFIG_RSEQ flag sizes the auxv *)
  Variable inp : ProcInput.
  #[local] Notation INP := inp.
  #[local] Notation argv := (in_argv inp).
  #[local] Notation envp := (in_envp inp).
  #[local] Notation uid := (in_uid inp).
  (* the launch's filesystem with [/tmp] seeded: the run's [m_fs] *)
  #[local] Notation fs := (in_fs inp).
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk ASEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hzr : AsanCeil.zero_random_draw (ed_random rdraw).
  Hypothesis Hlaunch : valid_launch INP.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.
  Hypothesis Hrdr : in_channel_reader INP = true.
  Hypothesis Hkb : in_kernel INP = recorded_kernel (in_kernel INP).

  #[local] Notation SINV := (SINV0 ASAN_B APH sp rdraw brk0 mbase inp).
  #[local] Notation argH := (argH0 sp rdraw inp).
  #[local] Notation E0a := (E0 sp rdraw brk0 inp).
  #[local] Notation LIM := AsanInit.LIMIT.
  (* The CONFIG_RSEQ bit of the launch this section is about.  [asan_b_init]
     takes it because the revision's auxv vector puts AT_NULL at 26 + 2 * r
     (AsanPlanCore.v:3496).  Written through [kb_rseq], never as a literal: the flag
     stays free in [valid_input]'s conjunct 17. *)
  #[local] Notation RSEQB := (kb_rseq (in_kernel INP)).
  #[local] Notation RSEQZ := (rseq_z RSEQB).


  Variable IT0 : itab.
  Hypothesis IT0_ok : itab_sound ASEGS IT0.

  Variable HS_asan : nat -> option acs.
  Variable startup_plan : plan.
  Variable startup_shape : shape.
  Variables KC0 BFUEL FUEL : nat.
  Hypothesis startup_cert :
    check ASEGS IT0 ASAN_B NX0 LIM RSEQZ XN0 XE0 XB0 HS_asan KC0 BFUEL FUEL None (asan_b_init RSEQZ) startup_plan = COk startup_shape.

  Variable HOLES : nat -> env -> Fs.Fs -> TSet.
  Hypothesis HOLES_agree : forall h E E' fs', env_agree NX0 E E' -> HOLES h E fs' = HOLES h E' fs'.
  Hypothesis HOLES_nil : forall h E fs', HOLES h E fs' [].
  Hypothesis HOLES_sound : holes_stmt ASEGS ASAN_B NX0 LIM HS_asan SINV argH HOLES fs.

  Lemma startup_AH : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
  Proof. intros E a H. eapply argH0_high; eassumption. Qed.
  Lemma startup_AA : forall E E' (a : word), env_agree NX0 E E' -> argH E a = argH E' a.
  Proof. intros E E' a _. reflexivity. Qed.
  Lemma startup_SF : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Proof. intros E M M' Hf HS. eapply SINV0_frame; eassumption. Qed.
  Lemma startup_SA : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.
  Proof. intros E E' M Hag HS. eapply SINV0_agree; eassumption. Qed.
  Lemma startup_xall : forall x, x_stmt ASEGS ASAN_B NX0 LIM RSEQZ SINV argH fs x.
  Proof.
    intros x. eapply asan_node_x_sound_all;
      first [ exact (fun E M H => H) | exact startup_SF | exact startup_SA | eassumption ].
  Qed.

  Let AH := startup_AH.
  Let AA := startup_AA.
  Let SF := startup_SF.
  Let SA := startup_SA.

  Theorem asan_startup :
    srealizes ASEGS (init_config ASEGS AsanUbsan.M.init_pc APH sp brk0 mbase rdraw LIM INP)
              (sd HOLES t_nil E0a fs startup_shape).
  Proof.
    pose proof asan_img_facts as IMG.
    (* [init_cfg_eq]'s table [A] appears only on its right side and in its pc premise, so it is
       named: an evar there leaves [Z.of_N _ = a_entry ?A] for [reflexivity] *)
    erewrite (init_cfg_eq ASEGS ASAN_B) by first [reflexivity | eassumption].
    eassert (HC : cs_ok ASEGS ASAN_B NX0 LIM SINV argH fs E0a _ _ _ _)
      by (eapply init_cs_ok; first [eassumption | (split; vm_compute; lia)]).
    exact (check_sound ASEGS IT0 IT0_ok ASAN_B NX0 LIM RSEQZ HS_asan XN0 XE0 XB0
              asan_wx asan_in_hull asan_hull_ok asan_shadow_ok SINV argH AH AA SF SA
              HOLES HOLES_agree HOLES_nil fs KC0
              (AsanNodesMmB.node_sys_sound ASEGS ASAN_B NX0 LIM SINV argH fs asan_res_len asan_hull_ok asan_shadow_ok AA SF SA)
              (AsanNodesMmB.node_brk2s_sound ASEGS ASAN_B NX0 LIM SINV argH fs asan_in_hull asan_res_hull asan_hull_ok asan_shadow_ok AH SF)
              (node_mmap2_sound_OBL ASEGS ASAN_B NX0 LIM SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok AH AA SF SA asan_hull_cover)
              (node_mmapin_sound_OBL ASEGS ASAN_B NX0 LIM SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok AH AA SF SA asan_hull_cover)
              (node_mprotect2_sound_OBL ASEGS ASAN_B NX0 LIM SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok AH AA SF SA asan_hull_cover)
              (AsanNodesMmB.node_exit_sound ASEGS ASAN_B NX0 LIM SINV argH fs)
              startup_xall
              (node_join_sound ASEGS ASAN_B NX0 LIM SINV argH fs)
              (XN0_sound _ _ _ _ _ _ _) (XE0_sound _ _ _ _ _ _ _) (XB0_sound _ _ _ _ _ _ _)
              HOLES_sound FUEL BFUEL None startup_plan (asan_b_init RSEQZ) startup_shape startup_cert
              _ _ _ _ t_nil HC I eq_refl).
  Qed.
End Startup.
