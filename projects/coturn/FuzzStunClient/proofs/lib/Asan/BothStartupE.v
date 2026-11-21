(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the start-up takes AsanInit's LPS 727298f3 launch and is realized at a flag of SpinAlg.srealizesM, the entry facts hold for the shadow table of the launch kernel's rseq layout, and the start-up and post plans pass the dead-arm check. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.coturn.FuzzStunClient.images Require Import AsanUbsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec ShapeAlg SpinAlg AgentLib AsanAcct.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import
  AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2 AsanInit
  AsanNodesMmLib AsanNodesMmA AsanNodesMmB BothPlanImages SumsBothClose AsanNodesStartX AsanNodesStartXInit AsanNodesDepot AsanNodesDepotBoth
  StartupHooks StartupPlanBoth StartupHSBoth PostPlanBoth StartupHSMainBoth BothStartupCert BothPostCert DeadArm.
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
Lemma both_hull_res {rsb : bool} : hull_res_ok BSEGS (BOTH_at (rseq_z rsb)).
Proof. apply hull_res_of_b. vm_compute. reflexivity. Qed.

Lemma both_nx0_ok : APS.nx0_ok NX0.
Proof. unfold APS.nx0_ok, NX0. lia. Qed.

(* [comment removed for export] *)
Lemma both_fe1 {rsb : bool} : fetch_word BSEGS (Z_to_bv 64 (x_envscan (BOTH_at (rseq_z rsb)))) = Some (Z_to_bv 32 0x0004b503). Proof. vm_compute. reflexivity. Qed.
Lemma both_fe2 {rsb : bool} : fetch_word BSEGS (Z_to_bv 64 (x_envscan (BOTH_at (rseq_z rsb)) + 4)) = Some (Z_to_bv 32 0x00848493). Proof. vm_compute. reflexivity. Qed.
Lemma both_fe3 {rsb : bool} : fetch_word BSEGS (Z_to_bv 64 (x_envscan (BOTH_at (rseq_z rsb)) + 8)) = Some (Z_to_bv 32 0xfe051ce3). Proof. vm_compute. reflexivity. Qed.
Lemma both_fp0 {rsb : bool} : fetch_word BSEGS (Z_to_bv 64 (x_pnscan (BOTH_at (rseq_z rsb)) - 8)) = Some (Z_to_bv 32 0x00b53023). Proof. vm_compute. reflexivity. Qed.
Lemma both_fp1 {rsb : bool} : fetch_word BSEGS (Z_to_bv 64 (x_pnscan (BOTH_at (rseq_z rsb)) - 4)) = Some (Z_to_bv 32 0x00158593). Proof. vm_compute. reflexivity. Qed.
Lemma both_fp2 {rsb : bool} : fetch_word BSEGS (Z_to_bv 64 (x_pnscan (BOTH_at (rseq_z rsb)))) = Some (Z_to_bv 32 0xfff5c683). Proof. vm_compute. reflexivity. Qed.
Lemma both_fp3 {rsb : bool} : fetch_word BSEGS (Z_to_bv 64 (x_pnscan (BOTH_at (rseq_z rsb)) + 4)) = Some (Z_to_bv 32 0xfec68ae3). Proof. vm_compute. reflexivity. Qed.
Lemma both_fp4 {rsb : bool} : fetch_word BSEGS (Z_to_bv 64 (x_pnscan (BOTH_at (rseq_z rsb)) + 8)) = Some (Z_to_bv 32 0xfe069ae3). Proof. vm_compute. reflexivity. Qed.

Lemma both_env_x {rsb : bool} : 0 <= x_envscan (BOTH_at (rseq_z rsb)) /\ x_envscan (BOTH_at (rseq_z rsb)) + 12 < 2 ^ 64 /\ x_envscan_k (BOTH_at (rseq_z rsb)) = x_envscan (BOTH_at (rseq_z rsb)) + 12.
Proof. cbn [x_envscan x_envscan_k BOTH_at]. lia. Qed.
Lemma both_pn_x {rsb : bool} : 8 <= x_pnscan (BOTH_at (rseq_z rsb)) /\ x_pnscan (BOTH_at (rseq_z rsb)) + 12 < 2 ^ 64 /\ x_pnscan_k (BOTH_at (rseq_z rsb)) = x_pnscan (BOTH_at (rseq_z rsb)) + 12.
Proof. cbn [x_pnscan x_pnscan_k BOTH_at]. lia. Qed.
Lemma both_env_e : is_ecall (Z_to_bv 32 0x0004b503) = false /\ is_ecall (Z_to_bv 32 0x00848493) = false /\ is_ecall (Z_to_bv 32 0xfe051ce3) = false.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma both_pn_e : is_ecall (Z_to_bv 32 0x00b53023) = false /\ is_ecall (Z_to_bv 32 0x00158593) = false /\ is_ecall (Z_to_bv 32 0xfff5c683) = false
  /\ is_ecall (Z_to_bv 32 0xfec68ae3) = false /\ is_ecall (Z_to_bv 32 0xfe069ae3) = false.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Lemma XN0_sound : forall SEGS A nx0 LIMIT SINV argH FS0 fl, ext_stmt SEGS A nx0 LIMIT XN0 SINV argH FS0 fl.
Proof. intros ? ? ? ? ? ? ? ?. intros id args cs cs' E R FULL model T _ _ H. discriminate H. Qed.
Lemma XE0_sound : forall SEGS A nx0 LIMIT SINV argH FS0 fl, emit_stmt SEGS A nx0 LIMIT XE0 SINV argH FS0 fl.
Proof. intros ? ? ? ? ? ? ? ?. intros id args cs fd ps cs' E R FULL model T _ H _. discriminate H. Qed.
Lemma XB0_sound : forall SEGS A nx0 LIMIT SINV argH FS0 fl, ext2_stmt SEGS A nx0 LIMIT XB0 SINV argH FS0 fl.
Proof. intros ? ? ? ? ? ? ? ?. intros id args cs csa csb E R FULL model TA TB _ H. discriminate H. Qed.

(* The start-up and post plans pass the dead-arm check with every hole live. *)
Lemma startup_both_dead : forall b : bool, dead_ok hf_all (startup_plan (rseq_z b)) = true.
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma post_both_dead : forall b : bool, dead_ok hf_all (post_plan (rseq_z b)) = true.
Proof. intros [|]; vm_compute; reflexivity. Qed.

Lemma startup_both_IT_ok : itab_sound BSEGS startup_both_IT.
Proof. apply APS.mk_itab_ranges_sound. Qed.
Lemma post_both_IT_ok : itab_sound BSEGS post_both_IT.
Proof. apply APS.mk_itab_ranges_sound. Qed.

Section Startup.
  Context {rsb : bool}.   (* the launch's kb_rseq; the table is ASAN_at/BOTH_at (rseq_z rsb) *)
  (* [comment removed for export] *)
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable imgfs : Fs.Fs.   (* [comment removed for export] *)
  Variable stdin : InputStream.
  Variables uid gid hw : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nofile sigmask : word.   (* [comment removed for export] *)
  Variable urnd : InputStream.   (* [comment removed for export] *)
  Variable tmp : Fs.Fs.
  Variable kb : KernelBuild.
  Variable execfn : list byte.
  Context {sigpipe_default : bool}.   (* AsanInit's: the launch's SIGPIPE disposition at entry *)
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk BSEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.

  (** AsanInit's launch, in its section order.  The run's filesystem is [in_fs INP] = the image fs
      seeded with [tmp], NOT the bare image fs, so [fs] abbreviates it. *)
  #[local] Notation INP := (@AsanInit.inp argv envp imgfs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sigpipe_default).
  #[local] Notation fs := (in_fs INP).
  Hypothesis Hlaunch : valid_launch INP.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.
  (** this launch's kernel is the table's r *)
  Hypothesis Hkb : kb_rseq kb = rsb.

  #[local] Notation SINV := (@SINV0 APH AsanUbsan.M.init_pc sp rdraw brk0 mbase argv envp imgfs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sigpipe_default).
  #[local] Notation argH := (argH0 sp rdraw argv envp kb execfn).
  #[local] Notation E0a := (E0 sp rdraw brk0 argv envp uid gid kb execfn).

  Lemma Hapc : Z.of_N AsanUbsan.M.init_pc = a_entry (BOTH_at (rseq_z rsb)).
  Proof. vm_compute. reflexivity. Qed.
  Lemma Hrs : a_rseq (BOTH_at (rseq_z rsb)) = rseq_z (kb_rseq kb).
  Proof. rewrite Hkb. reflexivity. Qed.

  (* [comment removed for export] *)
  (* the flag of [SpinAlg.srealizesM] the start-up is realized at; every hole is at the same flag *)
  Variable sfl : bool.
  Variable HOLESM : nat -> env -> Fs.Fs -> TSet.
  Hypothesis HOLESM_agree : forall h E E' fs', env_agree NX0 E E' -> HOLESM h E fs' = HOLESM h E' fs'.
  Hypothesis HOLESM_nil : forall h E fs', HOLESM h E fs' [].
  Hypothesis HOLESM_sound : holes_stmt BSEGS (BOTH_at (rseq_z rsb)) LIM (HS_mainB (rseq_z rsb)) SINV argH HOLESM fs (fun _ => sfl).

  (** [apply] the WHOLE statement, never [eapply] the conclusion: these
      Section lemmas carry every variable their proof mentions, and the
      conclusion alone leaves some of them as evars no [eassumption] fills.
      [argH0_high] moreover begins with an ANONYMOUS [N] (AsanInit's [apc],
      discharged but unused in its statement), which is a goal of its own. *)
  Local Ltac st_arg := first [ assumption | exact both_img_facts | exact Hapc | exact Hrs | exact 0%N ].

  Lemma bsu_AH : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
  Proof. apply argH0_high; st_arg. Qed.
  Lemma bsu_AA : forall E E' (a : word), env_agree NX0 E E' -> argH E a = argH E' a.
  Proof. apply argH0_agree; st_arg. Qed.
  Lemma bsu_SF : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Proof. apply SINV0_frame; st_arg. Qed.
  Lemma bsu_SA : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.
  Proof. apply SINV0_agree; st_arg. Qed.

  Lemma bsu_AT : forall E M (a : word), SINV E M -> argH E a = true -> uE E e_sp0 <= bv_unsigned a.
  Proof. apply argH0_top; st_arg. Qed.

  (** [node_munmap2_sound] asks for [hull_ok]/[shadow_ok] UNFOLDED, so their
      head is [and] and a [Hint Resolve] on the folded name never fires. *)
  Lemma bsu_hullP : 0 <= img_lo (BOTH_at (rseq_z rsb))
    /\ img_lo (BOTH_at (rseq_z rsb)) mod 4096 = 0
    /\ img_hi (BOTH_at (rseq_z rsb)) mod 4096 = 0
    /\ img_hi (BOTH_at (rseq_z rsb)) <= KHI.
  Proof. exact both_hull_ok. Qed.
  Lemma bsu_shadP : 0 <= shadow_off (BOTH_at (rseq_z rsb)) <= 2 ^ 47.
  Proof. exact both_shadow_ok. Qed.

  Hint Resolve both_wx both_in_hull both_res_len both_res_hull both_hull_ok both_shadow_ok both_nx0_ok both_hull_res bsu_AT bsu_AH bsu_AA bsu_SF bsu_SA bsu_hullP bsu_shadP : bothimg.

  Theorem both_x_sound : forall fl x, x_stmt BSEGS (BOTH_at (rseq_z rsb)) NX0 LIM SINV argH fs fl x.
  Proof.
    intros fl [ | | | | | | | | | | ].
    - eapply both_node_x_sound_XIMemset; eauto with bothimg.
    - eapply both_node_x_sound_XIMemcpy; eauto with bothimg.
    - eapply both_node_x_sound_XMemset; eauto with bothimg.
    - eapply both_node_x_sound_XMemcpy; eauto with bothimg.
    - eapply both_node_x_sound_XMemIsZero; eauto with bothimg.
    - eapply init_x_sound_envscan; try eassumption;
        first [ exact both_wx | exact both_in_hull | exact both_hull_ok | exact both_img_facts
              | exact Hapc | exact Hrs | exact bsu_SF | exact bsu_SA | exact (fun E M H => H)
              | exact both_env_x | exact both_fe1 | exact both_fe2 | exact both_fe3 | exact both_env_e
              | vm_refl ].
      Unshelve. all: try first [ exact APH | exact AsanUbsan.M.init_pc | assumption ].
    - eapply init_x_sound_pnscan; try eassumption;
        first [ exact both_wx | exact both_in_hull | exact both_hull_ok | exact both_img_facts
              | exact Hapc | exact Hrs | exact bsu_SF | exact bsu_SA | exact (fun E M H => H)
              | exact both_pn_x | exact both_fp0 | exact both_fp1 | exact both_fp2 | exact both_fp3 | exact both_fp4 | exact both_pn_e
              | vm_refl ].
      Unshelve. all: try first [ exact APH | exact AsanUbsan.M.init_pc | assumption ].
    - apply x_sound_layout.
    - eapply both_node_x_sound_XIStrncpy; eauto with bothimg.
    - eapply both_node_x_sound_XPopFree; eauto with bothimg.
    - intros args cs cs' E R FULL model T _ _ H. discriminate H.
  Qed.

  (* [comment removed for export] *)
  Lemma XNdB_ext : forall fl, ext_stmt BSEGS (BOTH_at (rseq_z rsb)) NX0 LIM XNdB SINV argH fs fl.
  Proof.
    intros fl id args. unfold XNdB. destruct (Nat.leb 113 id).
    - eapply both_dpn_ext_sound; eauto with bothimg.
    - intros cs cs' E R FULL model T _ _ H. discriminate H.
  Qed.

  Lemma post_dead_at : sfl = true -> dead_ok (fun _ => sfl) (post_plan (rseq_z rsb)) = true.
  Proof. intros ->. exact (post_both_dead _). Qed.
  Lemma startup_dead_at : sfl = true -> dead_ok (fun _ => sfl) (startup_plan (rseq_z rsb)) = true.
  Proof. intros ->. exact (startup_both_dead _). Qed.

  Theorem both_post_realizes : forall E R FULL model,
    cs_ok BSEGS (BOTH_at (rseq_z rsb)) LIM SINV argH fs E (HS_both_0 (rseq_z rsb)) R FULL model ->
    srealizesM BSEGS sfl (cfg_of BSEGS R (pc (HS_both_0 (rseq_z rsb))) FULL model) (sd HOLESM t_nil E (m_fs model) post_both_shape).
  Proof.
    intros E R FULL model HC.
    refine (APS.check_sound BSEGS post_both_IT post_both_IT_ok (BOTH_at (rseq_z rsb)) NX0 LIM (HS_mainB (rseq_z rsb)) XNdB XE0 XB0
              both_wx both_in_hull both_hull_ok both_shadow_ok both_nx0_ok SINV argH bsu_AH bsu_AT bsu_AA bsu_SF bsu_SA
              HOLESM HOLESM_agree HOLESM_nil fs 0%nat (fun _ => sfl) _ _ _ _ _ _ _ _ _ _ _ _ _ _ HOLESM_sound
              3000%nat 400000%nat None (post_plan (rseq_z rsb)) (HS_both_0 (rseq_z rsb)) post_both_shape post_both_cert
              sfl post_dead_at E R FULL model t_nil HC I eq_refl).
    all: try solve [exact bsu_AT].
    all: try solve [apply XNdB_ext | apply XN0_sound | apply XE0_sound | apply XB0_sound | apply both_x_sound].
    all: try solve [eapply AsanNodesMmA.node_mmap2_sound_OBL; eauto with bothimg].
    all: try solve [eapply AsanNodesMmA.node_mmapin_sound_OBL; eauto with bothimg].
    all: try solve [eapply AsanNodesMmA.node_mprotect2_sound_OBL; eauto with bothimg].
    all: try solve [eapply AsanPlanSound2.node_join_ok; eauto with bothimg].
    all: intros fl; first
      [ solve [eapply AsanNodesMmB.node_sys_sound; eauto with bothimg]
      | solve [eapply AsanNodesMmB.node_brk2_sound; eauto with bothimg]
      | solve [eapply AsanNodesMmB.node_munmap2_sound; eauto with bothimg]
      | solve [eapply AsanNodesMmB.node_brk2s_sound; eauto with bothimg]
      | solve [eapply AsanNodesMmB.node_exit_sound; eauto with bothimg]
      | solve [eapply AsanPlanSound2.node_join_sound; eauto with bothimg] ].
  Qed.
  (* [comment removed for export] *)
  Definition HOLES_E (h : nat) (E : env) (fs' : Fs.Fs) : TSet := sd HOLESM t_nil E fs' post_both_shape.

  Lemma HOLES_E_agree : forall h E E' fs', env_agree NX0 E E' -> HOLES_E h E fs' = HOLES_E h E' fs'.
  Proof. intros h E E' fs' Hag. unfold HOLES_E, post_both_shape. cbn [sd]. apply HOLESM_agree. exact Hag. Qed.
  Lemma HOLES_E_nil : forall h E fs', HOLES_E h E fs' [].
  Proof. intros h E fs'. unfold HOLES_E, post_both_shape. cbn [sd]. apply HOLESM_nil. Qed.
  Lemma HOLES_E_sound : holes_stmt BSEGS (BOTH_at (rseq_z rsb)) LIM (HS_both (rseq_z rsb)) SINV argH HOLES_E fs (fun _ => sfl).
  Proof.
    intros h ch Hh E R FULL model HC. unfold HS_both in Hh.
    destruct h as [|h]; [|discriminate Hh]. injection Hh as <-.
    exact (both_post_realizes E R FULL model HC).
  Qed.

  Theorem both_startup :
    srealizesM BSEGS sfl (init_config BSEGS AsanUbsan.M.init_pc APH sp brk0 mbase rdraw LIM INP)
              (sd HOLES_E t_nil E0a fs startup_both_shape).
  Proof.
    change (init_config BSEGS AsanUbsan.M.init_pc APH sp brk0 mbase rdraw LIM INP)
      with (init_config BSEGS AsanUbsan.M.init_pc APH sp brk0 mbase rdraw AsanInit.LIMIT INP).
    rewrite (init_cfg_eq BSEGS (BOTH_at (rseq_z rsb)))
      by first [ exact both_img_facts | exact Hapc | exact Hrs | eassumption ].
    refine (APS.check_sound BSEGS startup_both_IT startup_both_IT_ok (BOTH_at (rseq_z rsb)) NX0 LIM (HS_both (rseq_z rsb)) XN0 XE0 XB0
              both_wx both_in_hull both_hull_ok both_shadow_ok both_nx0_ok SINV argH bsu_AH bsu_AT bsu_AA bsu_SF bsu_SA
              HOLES_E HOLES_E_agree HOLES_E_nil fs 0%nat (fun _ => sfl) _ _ _ _ _ _ _ _ both_x_sound _ _
              (XN0_sound _ _ _ _ _ _ _) (XE0_sound _ _ _ _ _ _ _) (XB0_sound _ _ _ _ _ _ _) HOLES_E_sound
              3000%nat 400000%nat None (startup_plan (rseq_z rsb)) (both_init (rseq_z rsb)) startup_both_shape startup_both_cert
              sfl startup_dead_at _ _ _ _ t_nil _ I eq_refl).
    all: try solve [eapply AsanInit.init_cs_ok; first [ exact both_img_facts | exact Hapc | exact Hrs | eassumption ]].
    all: try solve [eapply AsanNodesMmA.node_mmap2_sound_OBL; eauto with bothimg].
    all: try solve [eapply AsanNodesMmA.node_mmapin_sound_OBL; eauto with bothimg].
    all: try solve [eapply AsanNodesMmA.node_mprotect2_sound_OBL; eauto with bothimg].
    all: try solve [eapply AsanPlanSound2.node_join_ok; eauto with bothimg].
    all: intros fl; first
      [ solve [eapply AsanNodesMmB.node_sys_sound; eauto with bothimg]
      | solve [eapply AsanNodesMmB.node_brk2_sound; eauto with bothimg]
      | solve [eapply AsanNodesMmB.node_munmap2_sound; eauto with bothimg]
      | solve [eapply AsanNodesMmB.node_brk2s_sound; eauto with bothimg]
      | solve [eapply AsanNodesMmB.node_exit_sound; eauto with bothimg]
      | solve [eapply AsanPlanSound2.node_join_sound; eauto with bothimg] ].
  Qed.
End Startup.
