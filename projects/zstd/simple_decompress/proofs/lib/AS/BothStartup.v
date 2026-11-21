(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the start-up over the launch's ProcInput, kernel build, exec file name and SIGPIPE disposition, its certificate checked at the run's CONFIG_RSEQ flag; AH, the hidden argument block's bound, passes argH0_high the image's entry pc (apc := APC)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.zstd.simple_decompress.images Require Import AsanUbsan.
From OSSVerify.Proofs.zstd.simple_decompress.lib.AS Require Import
  PropExec ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctImages AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2 BothPlanImages AsanInit
  AsanNodesIface AsanNodesMmA AsanNodesMmB SumsBothClose AsanNodesStartX AsanNodesStartXBoth AsanMaxVA AsanNodesMaxVA AsanNodesWJoin.
(* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition XN0 (id : nat) (args : list expr) (cs : acs) : option acs := None.
Definition XE0 (id : nat) (args : list expr) (cs : acs) : option (Z * list spiece * acs) := None.
Definition XB0 (id : nat) (args : list expr) (cs : acs) : option (acs * acs) := None.

Lemma XN0_sound : forall SEGS A nx0 LIMIT SINV argH FS0, ext_stmt SEGS A nx0 LIMIT XN0 SINV argH FS0.
Proof. intros ? ? ? ? ? ? ?. intros id args cs cs' E R FULL model T _ _ H. discriminate H. Qed.
Lemma XE0_sound : forall SEGS A nx0 LIMIT SINV argH FS0, emit_stmt SEGS A nx0 LIMIT XE0 SINV argH FS0.
Proof. intros ? ? ? ? ? ? ?. intros id args cs fd ps cs' E R FULL model T _ H _. discriminate H. Qed.
Lemma XB0_sound : forall SEGS A nx0 LIMIT SINV argH FS0, ext2_stmt SEGS A nx0 LIMIT XB0 SINV argH FS0.
Proof. intros ? ? ? ? ? ? ?. intros id args cs csa csb E R FULL model TA TB _ H. discriminate H. Qed.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Section XAll.
  Variable apc : N.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variable FS0 : Fs.Fs.
  Variable uid gid : word.
  Variable hw : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nof sigm : word.
  Variable abt : bool.
  Variable urnd : InputStream.
  Variable tmp : Fs.Fs.
  (* the kernel build, the exec file name and the SIGPIPE disposition, free as in AsanInit
     (LPS 727298f3) *)
  Variable kb : KernelBuild.
  Variable execfn : list byte.
  Variable sdef : bool.
  Let INP := inp argv envp fs stdin uid gid hw groups net nof sigm abt urnd tmp kb execfn sdef.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Hlaunch : valid_launch INP.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Hypothesis SINV_SINV0 : forall E M, SINV E M ->
    SINV0 BPH apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt urnd tmp kb execfn sdef E M.
  Hypothesis SINV_frame : forall E M M', (forall a, argH0 sp rdraw argv envp kb execfn E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  (* [comment removed for export] *)
  Variable nx0 : nat.
  Hypothesis Hnx0 : (NX0 <= nx0)%nat.
  Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
  (* the run's CONFIG_RSEQ flag as the plan's 0 or 1 (model commit 0c15dd4) *)
  #[local] Notation RZ := (rseq_z (kb_rseq kb)).

  Theorem both_node_x_sound_all : forall x, x_stmt BSEGS BOTH nx0 AsanInit.LIMIT RZ SINV (argH0 sp rdraw argv envp kb execfn) FS0 x.
  Proof.
    assert (AH : forall E (a : word), argH0 sp rdraw argv envp kb execfn E a = true -> CEIL <= bv_unsigned a)
      by (intros E a H; eapply argH0_high; eassumption).
    assert (AA : forall E E' (a : word), env_agree nx0 E E' -> argH0 sp rdraw argv envp kb execfn E a = argH0 sp rdraw argv envp kb execfn E' a).
    { intros E E' a [Hag Hb]. apply (argH0_agree sp rdraw argv envp kb execfn). split; [|exact Hb]. intros n Hn. apply Hag. lia. }
    intros [ | | | | | | | | | | ].
    - eapply both_node_x_sound_XIMemset; eassumption.
    - eapply both_node_x_sound_XIMemcpy; eassumption.
    - eapply both_node_x_sound_XMemset; eassumption.
    - eapply both_node_x_sound_XMemcpy; eassumption.
    - eapply both_node_x_sound_XMemIsZero; eassumption.
    - eapply node_x_sound_XEnvScan_asan_gen; eassumption.
    - eapply node_x_sound_XPnScan_asan_gen; eassumption.
    - apply x_sound_layout.
    - eapply both_node_x_sound_XIStrncpy; eassumption.
    - eapply both_node_x_sound_XPopFree; eassumption.
    - eapply (x_sound_maxva BSEGS BOTH nx0 AsanInit.LIMIT RZ SINV _ FS0);
        first [ exact both_wx | exact both_in_hull | exact both_hull_ok | exact SINV_frame
              | exact both_maxva_range | exact both_maxva_code | eassumption ].
  Qed.
End XAll.

Section Startup.
  (* [comment removed for export] *)
  Variable sp : word.
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variables uid gid : word.
  Variable hw : word.           (* [comment removed for export] *)
  Variable groups : list word.
  Variable net : NetQueue.
  (* [comment removed for export] *)
  Variables nof sigm : word.   (* [comment removed for export] *)
  Variable abt : bool.
  Variable urnd : InputStream.   (* [comment removed for export] *)
  Variable tmp : Fs.Fs.          (* [comment removed for export] *)
  (* the kernel build, the exec file name and the SIGPIPE disposition, free as in AsanInit
     (LPS 727298f3) *)
  Variable kb : KernelBuild.
  Variable execfn : list byte.
  Variable sdef : bool.
  Let INP := AsanInit.inp argv envp fs stdin uid gid hw groups net nof sigm abt urnd tmp kb execfn sdef.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk BSEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.
  (* [comment removed for export] *)
  Hypothesis Hlaunch : valid_launch INP.
  (* [comment removed for export] *)
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.

  #[local] Notation APC := AsanUbsan.M.init_pc.
  #[local] Notation SINV := (SINV0 BPH APC sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt urnd tmp kb execfn sdef).
  #[local] Notation argH := (argH0 sp rdraw argv envp kb execfn).
  #[local] Notation E0a := (AsanInit.E0 sp rdraw brk0 argv envp uid gid hw kb execfn).
  #[local] Notation LIM := AsanInit.LIMIT.
  (* the run's CONFIG_RSEQ flag as the plan's 0 or 1: the certificate is checked at it
     (model commit 0c15dd4) *)
  #[local] Notation RZ := (rseq_z (kb_rseq kb)).
  (* [comment removed for export] *)
  Variable IT0b : itab.
  Hypothesis IT0b_ok : itab_sound BSEGS IT0b.
  (* [comment removed for export] *)
  Variable HS_both : nat -> option acs.     (* [comment removed for export] *)
  Variable startup_plan_both : plan.
  Variable startup_shape_both : shape.
  Variables KC0 BFUEL FUEL : nat.
  Hypothesis startup_cert_both :
    check BSEGS IT0b BOTH NX0 LIM RZ (XNS BSEGS BOTH NX0 LIM) XE0 XB0 HS_both KC0 BFUEL FUEL None (both_init RZ) startup_plan_both = COk startup_shape_both.

  (* [comment removed for export] *)
  Variable HOLES : nat -> env -> Fs.Fs -> TSet.
  Hypothesis HOLES_agree : forall h E E' fs', env_agree NX0 E E' -> HOLES h E fs' = HOLES h E' fs'.
  Hypothesis HOLES_nil : forall h E fs', HOLES h E fs' [].
  Hypothesis HOLES_sound : holes_stmt BSEGS BOTH LIM HS_both SINV argH HOLES (fs_seed_tmp fs tmp).

  Theorem both_startup :
    srealizes BSEGS (init_config BSEGS APC BPH sp brk0 mbase rdraw LIM INP)
              (sd HOLES t_nil E0a (fs_seed_tmp fs tmp) startup_shape_both).
  Proof.
    pose proof both_img_facts as IMG.
    assert (Hapc : Z.of_N APC = a_entry BOTH) by reflexivity.
    assert (AH : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a)
      by (intros E a H; eapply argH0_high with (apc := APC); eassumption).
    assert (AH2 : forall E M (a : word), SINV E M -> argH E a = true -> uE E e_sp0 <= bv_unsigned a)
      by (intros E M a HS H; eapply argH0_high2; eassumption).
    assert (AA : forall E E' (a : word), env_agree NX0 E E' -> argH E a = argH E' a)
      by (intros E E' a HE; exact (argH0_agree sp rdraw argv envp kb execfn E E' a HE)).
    assert (SF : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M')
      by (intros E M M' Hf HS; eapply SINV0_frame; eassumption).
    assert (SA : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M)
      by (intros E E' M HE HS; eapply SINV0_agree; eassumption).
    assert (XALL : forall x, x_stmt BSEGS BOTH NX0 LIM RZ SINV argH (fs_seed_tmp fs tmp) x)
      by (eapply both_node_x_sound_all; first [eassumption | exact (fun E M H => H) | exact (le_n NX0)]).
    (* the launch's configuration is the plan's initial state: [AsanInit.init_cfg_eq] *)
    assert (Ecfg : init_config BSEGS APC BPH sp brk0 mbase rdraw LIM INP
                   = cfg_of BSEGS (R0 sp) (a_entry BOTH)
                       (FULL0 BPH APC sp rdraw mbase argv envp fs stdin uid gid hw groups net nof sigm abt urnd tmp kb execfn sdef)
                       (model0 BSEGS sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt urnd tmp kb execfn sdef))
      by (eapply init_cfg_eq; eassumption).
    rewrite Ecfg.
    assert (HC : cs_ok BSEGS BOTH LIM SINV argH (fs_seed_tmp fs tmp) E0a (both_init RZ) (R0 sp)
                   (FULL0 BPH APC sp rdraw mbase argv envp fs stdin uid gid hw groups net nof sigm abt urnd tmp kb execfn sdef)
                   (model0 BSEGS sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt urnd tmp kb execfn sdef))
      by (eapply init_cs_ok; eassumption).
    pose proof (check_sound BSEGS IT0b IT0b_ok BOTH NX0 (le_n NX0) LIM RZ HS_both (XNS BSEGS BOTH NX0 LIM) XE0 XB0
              both_wx both_in_hull both_hull_ok both_shadow_ok SINV argH AH AA SF SA
              HOLES HOLES_agree HOLES_nil (fs_seed_tmp fs tmp) KC0
              (AsanNodesMmB.node_sys_sound BSEGS BOTH NX0 LIM SINV argH (fs_seed_tmp fs tmp) both_res_len both_hull_ok both_shadow_ok AH2 AA SF SA)
              (AsanNodesMmB.node_brk2_sound BSEGS BOTH NX0 LIM SINV argH (fs_seed_tmp fs tmp) both_in_hull both_res_len both_hull_ok both_shadow_ok AH AH2 SF)
              (node_mmap2_sound_OBL BSEGS BOTH NX0 LIM SINV argH (fs_seed_tmp fs tmp) both_in_hull both_res_len both_res_hull both_hull_ok both_shadow_ok both_hull_cov AH AH2 AA SF SA)
              (node_mmapin_sound_OBL BSEGS BOTH NX0 LIM SINV argH (fs_seed_tmp fs tmp) both_in_hull both_res_len both_res_hull both_hull_ok both_shadow_ok both_hull_cov AH AH2 AA SF SA)
              (node_mprotect2_sound_OBL BSEGS BOTH NX0 LIM SINV argH (fs_seed_tmp fs tmp) both_in_hull both_res_len both_res_hull both_hull_ok both_shadow_ok both_hull_cov AH AH2 AA SF SA)
              (AsanNodesMmB.node_exit_sound BSEGS BOTH LIM SINV argH (fs_seed_tmp fs tmp))
              XALL
              (node_join_sound BSEGS BOTH NX0 LIM SINV argH (fs_seed_tmp fs tmp))
              (XNS_sound BSEGS BOTH NX0 LIM SINV argH (fs_seed_tmp fs tmp) AA SA both_in_hull both_hull_ok both_shadow_ok AH AH2) (XE0_sound _ _ _ _ _ _ _) (XB0_sound _ _ _ _ _ _ _)
              HOLES_sound FUEL BFUEL None startup_plan_both (both_init RZ) startup_shape_both startup_cert_both
              _ _ _ _ t_nil HC I eq_refl) as R.
    exact R.
  Qed.
End Startup.
