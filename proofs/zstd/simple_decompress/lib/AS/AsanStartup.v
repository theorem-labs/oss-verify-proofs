(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.zstd.simple_decompress.images Require Import Asan.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AS Require Import
  PropExec ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctImages AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2 AsanPlanImages AsanInit
  AsanNodesIface AsanNodesMmA AsanNodesMmB SumsAsanClose AsanNodesStartX AsanNodesStartXAsan AsanMaxVA AsanNodesMaxVA AsanNodesWJoin.
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
  fetch_word BSEGS (Z_to_bv 64 (x_maxva ASAN + 4 * Z.of_nat i)) = Some (nth i MAXVA_WORDS W0).
Proof.
  intros i Hi. cbn [x_maxva ASAN].
  do 45 (destruct i as [|i];
    [cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Z.add Pos.mul Pos.add nth MAXVA_WORDS];
     lazymatch goal with |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true) end |]).
  exfalso. lia.
Qed.

Lemma both_maxva_range : 0 < x_maxva ASAN /\ x_maxva ASAN + 180 < 2 ^ 64.
Proof. cbn [x_maxva ASAN]. lia. Qed.

(* [comment removed for export] *)
Section XAll.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 : word.
  Variable argv envp : list (list byte).
  Variable FS0 : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Variable uid hw : word.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0 BPH sp rdraw brk0 argv envp uid hw E M.
  Hypothesis SINV_frame : forall E M M', (forall a, argH0 BPH sp rdraw argv envp uid hw E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  (* [comment removed for export] *)
  Variable nx0 : nat.
  Hypothesis Hnx0 : (NX0 <= nx0)%nat.
  Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

  Theorem both_node_x_sound_all : forall x, x_stmt BSEGS ASAN nx0 AsanInit.LIMIT SINV (argH0 BPH sp rdraw argv envp uid hw) FS0 x.
  Proof.
    pose proof (argH0_high BPH sp rdraw argv envp uid hw Hsp Hva) as AH.
    assert (AA : forall E E' (a : word), env_agree nx0 E E' -> argH0 BPH sp rdraw argv envp uid hw E a = argH0 BPH sp rdraw argv envp uid hw E' a).
    { intros E E' a [Hag Hb]. apply (argH0_agree BPH sp rdraw argv envp uid hw). split; [|exact Hb]. intros n Hn. apply Hag. lia. }
    intros [ | | | | | | | | | | ].
    - apply (both_node_x_sound_XIMemset nx0 AsanInit.LIMIT SINV _ AH AA SINV_frame SINV_agree FS0).
    - apply (both_node_x_sound_XIMemcpy nx0 AsanInit.LIMIT SINV _ AH AA SINV_frame SINV_agree FS0).
    - apply (both_node_x_sound_XMemset nx0 AsanInit.LIMIT SINV _ AH AA SINV_frame SINV_agree FS0).
    - apply (both_node_x_sound_XMemcpy nx0 AsanInit.LIMIT SINV _ AH AA SINV_frame SINV_agree FS0).
    - apply (both_node_x_sound_XMemIsZero nx0 AsanInit.LIMIT SINV _ AH AA SINV_frame SINV_agree FS0).
    - apply (node_x_sound_XEnvScan_asan_gen sp rdraw brk0 argv envp FS0 Hsp Hva Hve uid hw Hfit SINV SINV_SINV0 SINV_frame nx0 Hnx0).
    - apply (node_x_sound_XPnScan_asan_gen sp rdraw brk0 argv envp FS0 Hsp Hva Hve uid hw Hfit SINV SINV_SINV0 SINV_frame nx0 Hnx0 SINV_agree).
    - apply x_sound_layout.
    - apply (both_node_x_sound_XIStrncpy nx0 AsanInit.LIMIT SINV _ AH AA SINV_frame SINV_agree FS0).
    - apply (both_node_x_sound_XPopFree nx0 AsanInit.LIMIT SINV _ AH AA SINV_frame SINV_agree FS0).
    - apply (x_sound_maxva BSEGS ASAN nx0 AsanInit.LIMIT SINV _ FS0 both_wx both_in_hull both_hull_ok SINV_frame both_maxva_range both_maxva_code).
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
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk BSEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.

  #[local] Notation SINV := (SINV0 BPH sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 BPH sp rdraw argv envp uid hw).
  #[local] Notation E0a := (AsanInit.E0 BPH sp rdraw brk0 argv envp uid hw).
  #[local] Notation LIM := AsanInit.LIMIT.

  (* [comment removed for export] *)
  Variable IT0b : itab.
  Hypothesis IT0b_ok : itab_sound BSEGS IT0b.
  (* [comment removed for export] *)
  Variable HS_both : nat -> option acs.     (* [comment removed for export] *)
  Variable startup_plan_both : plan.
  Variable startup_shape_both : shape.
  Variables KC0 BFUEL FUEL : nat.
  Hypothesis startup_cert_both :
    check BSEGS IT0b ASAN NX0 LIM (XNS BSEGS ASAN NX0 LIM) XE0 XB0 HS_both KC0 BFUEL FUEL None asan_init startup_plan_both = COk startup_shape_both.

  (* [comment removed for export] *)
  Variable HOLES : nat -> env -> Fs.Fs -> TSet.
  Hypothesis HOLES_agree : forall h E E' fs', env_agree NX0 E E' -> HOLES h E fs' = HOLES h E' fs'.
  Hypothesis HOLES_nil : forall h E fs', HOLES h E fs' [].
  Hypothesis HOLES_sound : holes_stmt BSEGS ASAN LIM HS_both SINV argH HOLES (fs_seed_tmp fs tmp).

  (* [comment removed for export] *)
  Let AH := argH0_high BPH sp rdraw argv envp uid hw Hsp Hva.
  Let AH2 := argH0_high2 BPH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit.
  Let AA := argH0_agree BPH sp rdraw argv envp uid hw.
  Let SF := SINV0_frame BPH sp rdraw brk0 argv envp uid hw.
  Let SA := SINV0_agree BPH sp rdraw brk0 argv envp uid hw.

  Theorem both_startup :
    srealizes BSEGS (init_config BSEGS Asan.M.init_pc BPH sp brk0 mbase rdraw LIM
                                 (AsanInit.inp argv envp fs stdin uid gid hw groups net nof sigm abt urnd tmp))
              (sd HOLES t_nil E0a (fs_seed_tmp fs tmp) startup_shape_both).
  Proof.
    pose proof both_img_facts as IMG.
    rewrite (init_cfg_eq BSEGS ASAN BPH sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt urnd tmp Asan.M.init_pc eq_refl).
    pose proof (init_cs_ok BSEGS ASAN BPH sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net IMG Hsp Hbrk Hva Hve Hfit Huid Hhw nof sigm abt urnd tmp) as HC.
    pose proof (check_sound BSEGS IT0b IT0b_ok ASAN NX0 (le_n NX0) LIM HS_both (XNS BSEGS ASAN NX0 LIM) XE0 XB0
              both_wx both_in_hull both_hull_ok both_shadow_ok SINV argH AH AA SF SA
              HOLES HOLES_agree HOLES_nil (fs_seed_tmp fs tmp) KC0
              (AsanNodesMmB.node_sys_sound BSEGS ASAN NX0 LIM SINV argH (fs_seed_tmp fs tmp) both_res_len both_hull_ok both_shadow_ok AH2 AA SF SA)
              (AsanNodesMmB.node_brk2_sound BSEGS ASAN NX0 LIM SINV argH (fs_seed_tmp fs tmp) both_in_hull both_res_len both_hull_ok both_shadow_ok AH AH2 SF)
              (node_mmap2_sound_OBL BSEGS ASAN NX0 LIM SINV argH (fs_seed_tmp fs tmp) both_in_hull both_res_len both_res_hull both_hull_ok both_shadow_ok both_hull_cov AH AH2 AA SF SA)
              (node_mmapin_sound_OBL BSEGS ASAN NX0 LIM SINV argH (fs_seed_tmp fs tmp) both_in_hull both_res_len both_res_hull both_hull_ok both_shadow_ok both_hull_cov AH AH2 AA SF SA)
              (node_mprotect2_sound_OBL BSEGS ASAN NX0 LIM SINV argH (fs_seed_tmp fs tmp) both_in_hull both_res_len both_res_hull both_hull_ok both_shadow_ok both_hull_cov AH AH2 AA SF SA)
              (AsanNodesMmB.node_exit_sound BSEGS ASAN LIM SINV argH (fs_seed_tmp fs tmp))
              (both_node_x_sound_all sp rdraw brk0 argv envp (fs_seed_tmp fs tmp) Hsp Hva Hve uid hw Hfit SINV (fun E M H => H) SF NX0 (le_n NX0) SA)
              (node_join_sound BSEGS ASAN NX0 LIM SINV argH (fs_seed_tmp fs tmp))
              (XNS_sound BSEGS ASAN NX0 LIM SINV argH (fs_seed_tmp fs tmp) AA SA both_in_hull both_hull_ok both_shadow_ok AH AH2) (XE0_sound _ _ _ _ _ _ _) (XB0_sound _ _ _ _ _ _ _)
              HOLES_sound FUEL BFUEL None startup_plan_both asan_init startup_shape_both startup_cert_both
              _ _ _ _ t_nil HC I eq_refl) as R.
    exact R.
  Qed.
End Startup.
