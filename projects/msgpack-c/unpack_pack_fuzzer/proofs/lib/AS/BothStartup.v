(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's whole ProcInput and its kernel build in the start-up sections, and the CONFIG_RSEQ flag the start-up certificate is checked at). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require Import
  PropExec ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctImages AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2 BothPlanImages AsanInit
  AsanNodesIface AsanNodesMmA AsanNodesMmB SumsBothClose AsanNodesStartX AsanNodesStartXBoth AsanMaxVA AsanNodesMaxVA AsanNodesWJoin.
Unset Nia Cache. Unset Nra Cache.

Unset Lia Cache.
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

Lemma both_maxva_code : forall i, (i < 45)%nat ->
  fetch_word BSEGS (Z_to_bv 64 (x_maxva BOTH + 4 * Z.of_nat i)) = Some (nth i MAXVA_WORDS W0).
Proof.
  intros i Hi. cbn [x_maxva BOTH].
  do 45 (destruct i as [|i];
    [cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Z.add Pos.mul Pos.add nth MAXVA_WORDS];
     lazymatch goal with |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true) end |]).
  exfalso. lia.
Qed.

Lemma both_maxva_range : 0 < x_maxva BOTH /\ x_maxva BOTH + 180 < 2 ^ 64.
Proof. cbn [x_maxva BOTH]. lia. Qed.


Section XAll.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variables uid gid : word.
  Variable hw : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nof sigm : word.
  Variable abt : bool.
  Variable urnd : InputStream.
  Variable tmpf : Fs.Fs.
  Variable kb : KernelBuild.
  Variable execfn : list byte.
  Variables chrdr sigdef sigterm : bool.
  Variable FS0 : Fs.Fs.
  #[local] Notation INP := (inp argv envp fs stdin uid gid hw groups net nof sigm abt urnd tmpf kb execfn chrdr sigdef sigterm).
  #[local] Notation RZ := (rseq_z (kb_rseq kb)).
  #[local] Notation argH0a := (argH0 sp rdraw argv envp kb execfn).
  #[local] Notation SINV0a := (SINV0 BOTH BPH sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt urnd tmpf kb execfn chrdr sigdef sigterm).
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Hlaunch : valid_launch INP.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0a E M.
  Hypothesis SINV_frame : forall E M M', (forall a, argH0a E a = true -> M' a = M a) -> SINV E M -> SINV E M'.

  Variable nx0 : nat.
  Hypothesis Hnx0 : (NX0 <= nx0)%nat.
  Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

  Theorem both_node_x_sound_all : forall x, x_stmt BSEGS BOTH nx0 AsanInit.LIMIT RZ SINV argH0a FS0 x.
  Proof.
    assert (AH : forall E (a : word), argH0a E a = true -> CEIL <= bv_unsigned a)
      by (intros E a H; eapply argH0_high; eassumption).
    assert (AA : forall E E' (a : word), env_agree nx0 E E' -> argH0a E a = argH0a E' a).
    { intros E E' a [Hag Hb]. apply argH0_agree. split; [|exact Hb]. intros n Hn. apply Hag. lia. }
    intros [ | | | | | | | | | | ].
    - apply (both_node_x_sound_XIMemset nx0 AsanInit.LIMIT RZ SINV _ AH AA SINV_frame SINV_agree FS0).
    - apply (both_node_x_sound_XIMemcpy nx0 AsanInit.LIMIT RZ SINV _ AH AA SINV_frame SINV_agree FS0).
    - apply (both_node_x_sound_XMemset nx0 AsanInit.LIMIT RZ SINV _ AH AA SINV_frame SINV_agree FS0).
    - apply (both_node_x_sound_XMemcpy nx0 AsanInit.LIMIT RZ SINV _ AH AA SINV_frame SINV_agree FS0).
    - apply (both_node_x_sound_XMemIsZero nx0 AsanInit.LIMIT RZ SINV _ AH AA SINV_frame SINV_agree FS0).
    - eapply node_x_sound_XEnvScan_asan_gen; eassumption.
    - eapply node_x_sound_XPnScan_asan_gen; eassumption.
    - apply x_sound_layout.
    - apply (both_node_x_sound_XIStrncpy nx0 AsanInit.LIMIT RZ SINV _ AH AA SINV_frame SINV_agree FS0).
    - apply (both_node_x_sound_XPopFree nx0 AsanInit.LIMIT RZ SINV _ AH AA SINV_frame SINV_agree FS0).
    - apply (x_sound_maxva BSEGS BOTH nx0 AsanInit.LIMIT RZ SINV _ FS0 both_wx both_in_hull both_hull_ok SINV_frame both_maxva_range both_maxva_code).
  Qed.
End XAll.

Section Startup.

  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variables uid gid : word.
  Variable hw : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nof sigm : word.
  Variable abt : bool.
  Variable urnd : InputStream.
  Variable tmpf : Fs.Fs.
  Variable kb : KernelBuild.
  Variable execfn : list byte.
  Variables chrdr sigdef sigterm : bool.
  #[local] Notation INP := (AsanInit.inp argv envp fs stdin uid gid hw groups net nof sigm abt urnd tmpf kb execfn chrdr sigdef sigterm).
  #[local] Notation FS := (in_fs INP).
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk BSEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.
  Hypothesis Hlaunch : valid_launch INP.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.
  Hypothesis Hrdr : in_channel_reader INP = true.

  #[local] Notation SINV := (SINV0 BOTH BPH sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt urnd tmpf kb execfn chrdr sigdef sigterm).
  #[local] Notation argH := (argH0 sp rdraw argv envp kb execfn).
  #[local] Notation E0a := (AsanInit.E0 sp rdraw brk0 argv envp uid gid hw kb execfn).
  #[local] Notation LIM := AsanInit.LIMIT.
  (** the run's CONFIG_RSEQ flag as the plan's 0 or 1: the certificate is checked at it *)
  #[local] Notation RZ := (rseq_z (kb_rseq kb)).

  Variable IT0 : itab.
  Hypothesis IT0_ok : itab_sound BSEGS IT0.

  Variable HS_both : nat -> option acs.
  Variable startup_plan : plan.
  Variable startup_shape : shape.
  Variables KC0 BFUEL FUEL : nat.
  Hypothesis startup_cert :
    check BSEGS IT0 BOTH NX0 LIM RZ (XNS BSEGS BOTH NX0 LIM) XE0 XB0 HS_both KC0 BFUEL FUEL None (both_init RZ) startup_plan = COk startup_shape.

  Variable HOLES : nat -> env -> Fs.Fs -> TSet.
  Hypothesis HOLES_agree : forall h E E' fs', env_agree NX0 E E' -> HOLES h E fs' = HOLES h E' fs'.
  Hypothesis HOLES_nil : forall h E fs', HOLES h E fs' [].
  Hypothesis HOLES_sound : holes_stmt BSEGS BOTH LIM HS_both SINV argH HOLES FS.

  Let AH : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
  Proof. intros E a H. eapply argH0_high; eassumption. Qed.
  Let AH2 : forall E M (a : word), SINV E M -> argH E a = true -> uE E e_sp0 <= bv_unsigned a.
  Proof. intros E M a HS H. eapply argH0_high2; eassumption. Qed.
  Let AA : forall E E' (a : word), env_agree NX0 E E' -> argH E a = argH E' a.
  Proof. intros E E' a H. eapply argH0_agree; exact H. Qed.
  Let SF : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Proof. intros E M M' H1 H2. eapply SINV0_frame; eassumption. Qed.
  Let SA : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.
  Proof. intros E E' M H1 H2. eapply SINV0_agree; eassumption. Qed.

  Theorem both_startup :
    srealizes BSEGS (init_config BSEGS AsanUbsan.M.init_pc BPH sp brk0 mbase rdraw LIM INP)
              (sd HOLES t_nil E0a FS startup_shape).
  Proof.
    pose proof both_img_facts as IMG.
    rewrite (init_cfg_eq BSEGS BOTH BPH) by reflexivity.
    pose proof (init_cs_ok BSEGS BOTH BPH sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net IMG Hsp Hbrk Hmb Hva Hve Huid Hhw
                  nof sigm abt urnd tmpf kb execfn chrdr sigdef sigterm Hlaunch Hlau Hrdr) as HC.
    pose proof (check_sound BSEGS IT0 IT0_ok BOTH NX0 (le_n NX0) LIM RZ HS_both (XNS BSEGS BOTH NX0 LIM) XE0 XB0
              both_wx both_in_hull both_hull_ok both_shadow_ok SINV argH AH AA SF SA
              HOLES HOLES_agree HOLES_nil FS KC0
              (AsanNodesMmB.node_sys_sound BSEGS BOTH NX0 LIM SINV argH FS both_res_len both_hull_ok both_shadow_ok AH2 AA SF SA)
              (AsanNodesMmB.node_brk2_sound BSEGS BOTH NX0 LIM SINV argH FS both_in_hull both_res_len both_hull_ok both_shadow_ok AH AH2 SF)
              (node_mmap2_sound_OBL BSEGS BOTH NX0 LIM SINV argH FS both_in_hull both_res_len both_res_hull both_hull_ok both_shadow_ok both_hull_cov AH AH2 AA SF SA)
              (node_mmapin_sound_OBL BSEGS BOTH NX0 LIM SINV argH FS both_in_hull both_res_len both_res_hull both_hull_ok both_shadow_ok both_hull_cov AH AH2 AA SF SA)
              (node_mprotect2_sound_OBL BSEGS BOTH NX0 LIM SINV argH FS both_in_hull both_res_len both_res_hull both_hull_ok both_shadow_ok both_hull_cov AH AH2 AA SF SA)
              (AsanNodesMmB.node_exit_sound BSEGS BOTH LIM SINV argH FS)
              (both_node_x_sound_all sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt urnd tmpf kb execfn chrdr sigdef sigterm
                 FS Hsp Hva Hve Hfit Hlaunch Hlau SINV (fun E M H => H) SF NX0 (le_n NX0) SA)
              (node_join_sound BSEGS BOTH NX0 LIM SINV argH FS)
              (XNS_sound BSEGS BOTH NX0 LIM SINV argH FS AA SA both_in_hull both_hull_ok both_shadow_ok AH AH2) (XE0_sound _ _ _ _ _ _ _) (XB0_sound _ _ _ _ _ _ _)
              HOLES_sound FUEL BFUEL None startup_plan (both_init RZ) startup_shape startup_cert
              _ _ _ _ t_nil HC I eq_refl) as R.
    exact R.
  Qed.
End Startup.
