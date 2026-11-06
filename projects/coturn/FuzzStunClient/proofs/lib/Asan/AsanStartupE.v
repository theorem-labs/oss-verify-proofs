(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.coturn.FuzzStunClient.images Require Import Asan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec ShapeAlg SpinAlg AgentLib AsanAcct.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import
  AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2 AsanInit
  AsanNodesMmLib AsanNodesMmA AsanNodesMmB AsanPlanImages SumsAsanClose AsanNodesStartX AsanNodesStartXInit AsanNodesDepot AsanNodesDepotAsan
  StartupHooks StartupPlanAsan StartupHSAsan PostPlanAsan StartupHSMainAsan AsanStartupCert AsanPostCert.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

#[local] Notation LIM := target_alloc_limit.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Lemma asan_hull_res : hull_res_ok ASEGS ASAN.
Proof. apply hull_res_of_b. vm_compute. reflexivity. Qed.

Lemma asan_nx0_ok : APS.nx0_ok NX0.
Proof. unfold APS.nx0_ok, NX0. lia. Qed.

(* [comment removed for export] *)
Lemma asan_fe1 : fetch_word ASEGS (Z_to_bv 64 (x_envscan ASAN)) = Some (Z_to_bv 32 0x0004b503). Proof. vm_compute. reflexivity. Qed.
Lemma asan_fe2 : fetch_word ASEGS (Z_to_bv 64 (x_envscan ASAN + 4)) = Some (Z_to_bv 32 0x00848493). Proof. vm_compute. reflexivity. Qed.
Lemma asan_fe3 : fetch_word ASEGS (Z_to_bv 64 (x_envscan ASAN + 8)) = Some (Z_to_bv 32 0xfe051ce3). Proof. vm_compute. reflexivity. Qed.
Lemma asan_fp0 : fetch_word ASEGS (Z_to_bv 64 (x_pnscan ASAN - 8)) = Some (Z_to_bv 32 0x00b53023). Proof. vm_compute. reflexivity. Qed.
Lemma asan_fp1 : fetch_word ASEGS (Z_to_bv 64 (x_pnscan ASAN - 4)) = Some (Z_to_bv 32 0x00158593). Proof. vm_compute. reflexivity. Qed.
Lemma asan_fp2 : fetch_word ASEGS (Z_to_bv 64 (x_pnscan ASAN)) = Some (Z_to_bv 32 0xfff5c683). Proof. vm_compute. reflexivity. Qed.
Lemma asan_fp3 : fetch_word ASEGS (Z_to_bv 64 (x_pnscan ASAN + 4)) = Some (Z_to_bv 32 0xfec68ae3). Proof. vm_compute. reflexivity. Qed.
Lemma asan_fp4 : fetch_word ASEGS (Z_to_bv 64 (x_pnscan ASAN + 8)) = Some (Z_to_bv 32 0xfe069ae3). Proof. vm_compute. reflexivity. Qed.

Lemma asan_env_x : 0 <= x_envscan ASAN /\ x_envscan ASAN + 12 < 2 ^ 64 /\ x_envscan_k ASAN = x_envscan ASAN + 12.
Proof. cbn [x_envscan x_envscan_k ASAN]. lia. Qed.
Lemma asan_pn_x : 8 <= x_pnscan ASAN /\ x_pnscan ASAN + 12 < 2 ^ 64 /\ x_pnscan_k ASAN = x_pnscan ASAN + 12.
Proof. cbn [x_pnscan x_pnscan_k ASAN]. lia. Qed.
Lemma asan_env_e : is_ecall (Z_to_bv 32 0x0004b503) = false /\ is_ecall (Z_to_bv 32 0x00848493) = false /\ is_ecall (Z_to_bv 32 0xfe051ce3) = false.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma asan_pn_e : is_ecall (Z_to_bv 32 0x00b53023) = false /\ is_ecall (Z_to_bv 32 0x00158593) = false /\ is_ecall (Z_to_bv 32 0xfff5c683) = false
  /\ is_ecall (Z_to_bv 32 0xfec68ae3) = false /\ is_ecall (Z_to_bv 32 0xfe069ae3) = false.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Lemma XN0_sound : forall SEGS A nx0 LIMIT SINV argH FS0, ext_stmt SEGS A nx0 LIMIT XN0 SINV argH FS0.
Proof. intros ? ? ? ? ? ? ?. intros id args cs cs' E R FULL model T _ _ H. discriminate H. Qed.
Lemma XE0_sound : forall SEGS A nx0 LIMIT SINV argH FS0, emit_stmt SEGS A nx0 LIMIT XE0 SINV argH FS0.
Proof. intros ? ? ? ? ? ? ?. intros id args cs fd ps cs' E R FULL model T _ H _. discriminate H. Qed.
Lemma XB0_sound : forall SEGS A nx0 LIMIT SINV argH FS0, ext2_stmt SEGS A nx0 LIMIT XB0 SINV argH FS0.
Proof. intros ? ? ? ? ? ? ?. intros id args cs csa csb E R FULL model TA TB _ H. discriminate H. Qed.

Lemma startup_asan_IT_ok : itab_sound ASEGS startup_asan_IT.
Proof. apply APS.mk_itab_ranges_sound. Qed.
Lemma post_asan_IT_ok : itab_sound ASEGS post_asan_IT.
Proof. apply APS.mk_itab_ranges_sound. Qed.

Section Startup.
  (* [comment removed for export] *)
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variables uid gid hw : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nofile sigmask : word.   (* [comment removed for export] *)
  Variable urnd : InputStream.   (* [comment removed for export] *)
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

  (* [comment removed for export] *)
  Variable HOLESM : nat -> env -> Fs.Fs -> TSet.
  Hypothesis HOLESM_agree : forall h E E' fs', env_agree NX0 E E' -> HOLESM h E fs' = HOLESM h E' fs'.
  Hypothesis HOLESM_nil : forall h E fs', HOLESM h E fs' [].
  Hypothesis HOLESM_sound : holes_stmt ASEGS ASAN LIM HS_mainA SINV argH HOLESM fs.

  Let AH := argH0_high APH sp rdraw argv envp uid hw Hsp Hva.
  Let AA := argH0_agree APH sp rdraw argv envp uid hw.
  Let SF := SINV0_frame APH sp rdraw brk0 argv envp uid hw.
  Let SA := SINV0_agree APH sp rdraw brk0 argv envp uid hw.

  Lemma AT : forall E M (a : word), SINV E M -> argH E a = true -> uE E e_sp0 <= bv_unsigned a.
  Proof. intros E M a HS Ha. eapply argH0_top; eauto. Qed.

  Hint Resolve asan_wx asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_nx0_ok asan_hull_res AT : asanimg.

  Theorem asan_x_sound : forall x, x_stmt ASEGS ASAN NX0 LIM SINV argH fs x.
  Proof.
    intros [ | | | | | | | | | | ].
    - eapply asan_node_x_sound_XIMemset; eauto with asanimg.
    - eapply asan_node_x_sound_XIMemcpy; eauto with asanimg.
    - eapply asan_node_x_sound_XMemset; eauto with asanimg.
    - eapply asan_node_x_sound_XMemcpy; eauto with asanimg.
    - eapply asan_node_x_sound_XMemIsZero; eauto with asanimg.
    - exact (init_x_sound_envscan ASEGS ASAN APH asan_wx asan_in_hull asan_hull_ok
               (Z_to_bv 32 0x0004b503) (Z_to_bv 32 0x00848493) (Z_to_bv 32 0xfe051ce3) asan_env_x asan_fe1 asan_fe2 asan_fe3 asan_env_e
               ltac:(vm_refl) ltac:(vm_refl) ltac:(vm_refl) sp rdraw brk0 argv envp fs Hsp Hva Hve uid hw Hfit SINV (fun E M H => H) SF).
    - exact (init_x_sound_pnscan ASEGS ASAN APH asan_wx asan_in_hull asan_hull_ok
               (Z_to_bv 32 0x00b53023) (Z_to_bv 32 0x00158593) (Z_to_bv 32 0xfff5c683) (Z_to_bv 32 0xfec68ae3) (Z_to_bv 32 0xfe069ae3)
               asan_pn_x asan_fp0 asan_fp1 asan_fp2 asan_fp3 asan_fp4 asan_pn_e ltac:(vm_refl) ltac:(vm_refl) ltac:(vm_refl) ltac:(vm_refl) ltac:(vm_refl)
               sp rdraw brk0 argv envp fs Hsp Hva Hve uid hw Hfit SINV (fun E M H => H) SF SA).
    - apply x_sound_layout.
    - eapply asan_node_x_sound_XIStrncpy; eauto with asanimg.
    - eapply asan_node_x_sound_XPopFree; eauto with asanimg.
    - intros args cs cs' E R FULL model T _ _ H. discriminate H.
  Qed.

  (* [comment removed for export] *)
  Lemma XNdA_ext : ext_stmt ASEGS ASAN NX0 LIM XNdA SINV argH fs.
  Proof.
    intros id args. unfold XNdA. destruct (Nat.leb 113 id).
    - eapply asan_dpn_ext_sound; eauto with asanimg.
    - intros cs cs' E R FULL model T _ _ H. discriminate H.
  Qed.

  Theorem asan_post_realizes : forall E R FULL model,
    cs_ok ASEGS ASAN LIM SINV argH fs E HS_asan_0 R FULL model ->
    srealizes ASEGS (cfg_of ASEGS R (pc HS_asan_0) FULL model) (sd HOLESM t_nil E (m_fs model) post_asan_shape).
  Proof.
    intros E R FULL model HC.
    refine (APS.check_sound ASEGS post_asan_IT post_asan_IT_ok ASAN NX0 LIM HS_mainA XNdA XE0 XB0
              asan_wx asan_in_hull asan_hull_ok asan_shadow_ok asan_nx0_ok SINV argH AH _ AA SF SA
              HOLESM HOLESM_agree HOLESM_nil fs 0%nat _ _ _ _ _ _ _ _ _ _ _ _ _ HOLESM_sound
              3000%nat 400000%nat None post_plan HS_asan_0 post_asan_shape post_asan_cert E R FULL model t_nil HC I eq_refl).
    all: try solve [intros E' M a HS Ha; eapply argH0_top; eauto].
    all: try solve [eapply AsanNodesMmB.node_sys_sound; eauto with asanimg].
    all: try solve [eapply AsanNodesMmB.node_brk2_sound; eauto with asanimg].
    all: try solve [eapply AsanNodesMmB.node_brk2s_sound; eauto with asanimg].
    all: try solve [eapply AsanNodesMmA.node_mmap2_sound_OBL; eauto with asanimg].
    all: try solve [eapply AsanNodesMmA.node_mmapin_sound_OBL; eauto with asanimg].
    all: try solve [eapply AsanNodesMmA.node_mprotect2_sound_OBL; eauto with asanimg].
    all: try solve [eapply AsanNodesMmB.node_exit_sound; eauto with asanimg].
    all: try solve [eapply AsanPlanSound2.node_join_sound; eauto with asanimg].
    all: try solve [eapply AsanPlanSound2.node_join_ok; eauto with asanimg].
    all: try solve [apply XNdA_ext | apply XN0_sound | apply XE0_sound | apply XB0_sound].
    all: try solve [eapply AsanNodesMmB.node_sys_sound; eauto with asanimg].
    all: try solve [eapply AsanNodesMmB.node_brk2_sound; eauto with asanimg].
    all: try solve [eapply AsanNodesMmB.node_brk2s_sound; eauto with asanimg].
    all: try solve [eapply AsanNodesMmA.node_mmap2_sound_OBL; eauto with asanimg].
    all: try solve [eapply AsanNodesMmA.node_mmapin_sound_OBL; eauto with asanimg].
    all: try solve [eapply AsanNodesMmA.node_mprotect2_sound_OBL; eauto with asanimg].
    all: apply asan_x_sound.
  Qed.
  (* [comment removed for export] *)
  Definition HOLES_E (h : nat) (E : env) (fs' : Fs.Fs) : TSet := sd HOLESM t_nil E fs' post_asan_shape.

  Lemma HOLES_E_agree : forall h E E' fs', env_agree NX0 E E' -> HOLES_E h E fs' = HOLES_E h E' fs'.
  Proof. intros h E E' fs' Hag. unfold HOLES_E, post_asan_shape. cbn [sd]. apply HOLESM_agree. exact Hag. Qed.
  Lemma HOLES_E_nil : forall h E fs', HOLES_E h E fs' [].
  Proof. intros h E fs'. unfold HOLES_E, post_asan_shape. cbn [sd]. apply HOLESM_nil. Qed.
  Lemma HOLES_E_sound : holes_stmt ASEGS ASAN LIM HS_asan SINV argH HOLES_E fs.
  Proof.
    intros h ch Hh E R FULL model HC. unfold HS_asan in Hh.
    destruct h as [|h]; [|discriminate Hh]. injection Hh as <-.
    exact (asan_post_realizes E R FULL model HC).
  Qed.

  Theorem asan_startup :
    srealizes ASEGS (init_config ASEGS Asan.M.init_pc APH sp brk0 mbase rdraw LIM
                                 (AsanInit.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd))
              (sd HOLES_E t_nil E0a fs startup_asan_shape).
  Proof.
    assert (Hpc : Z.of_N Asan.M.init_pc = a_entry ASAN) by (vm_compute; reflexivity).
    change (init_config ASEGS Asan.M.init_pc APH sp brk0 mbase rdraw LIM (AsanInit.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd))
      with (init_config ASEGS Asan.M.init_pc APH sp brk0 mbase rdraw AsanInit.LIMIT (AsanInit.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd)).
    rewrite (init_cfg_eq ASEGS ASAN APH sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd _ Hpc).
    pose proof (init_cs_ok ASEGS ASAN APH sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd
                  asan_img_facts Hsp Hbrk Hva Hve Hfit Huid) as HC.
    refine (APS.check_sound ASEGS startup_asan_IT startup_asan_IT_ok ASAN NX0 LIM HS_asan XN0 XE0 XB0
              asan_wx asan_in_hull asan_hull_ok asan_shadow_ok asan_nx0_ok SINV argH AH AT AA SF SA
              HOLES_E HOLES_E_agree HOLES_E_nil fs 0%nat _ _ _ _ _ _ _ asan_x_sound _ _
              (XN0_sound _ _ _ _ _ _ _) (XE0_sound _ _ _ _ _ _ _) (XB0_sound _ _ _ _ _ _ _) HOLES_E_sound
              3000%nat 400000%nat None startup_plan asan_init startup_asan_shape startup_asan_cert _ _ _ _ t_nil HC I eq_refl).
    all: try solve [eapply AsanNodesMmB.node_sys_sound; eauto with asanimg].
    all: try solve [eapply AsanNodesMmB.node_brk2_sound; eauto with asanimg].
    all: try solve [eapply AsanNodesMmB.node_brk2s_sound; eauto with asanimg].
    all: try solve [eapply AsanNodesMmA.node_mmap2_sound_OBL; eauto with asanimg].
    all: try solve [eapply AsanNodesMmA.node_mmapin_sound_OBL; eauto with asanimg].
    all: try solve [eapply AsanNodesMmA.node_mprotect2_sound_OBL; eauto with asanimg].
    all: try solve [eapply AsanNodesMmB.node_exit_sound; eauto with asanimg].
    all: try solve [eapply AsanPlanSound2.node_join_sound; eauto with asanimg].
    all: try solve [eapply AsanPlanSound2.node_join_ok; eauto with asanimg].
  Qed.
End Startup.
