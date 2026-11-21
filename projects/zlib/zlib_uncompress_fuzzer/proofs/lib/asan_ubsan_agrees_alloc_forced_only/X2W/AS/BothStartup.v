(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.World Require Import TgtO_zlib_uncompress_fuzzer_both.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.AS Require Import PropExec ShapeAlg SpinAlg AgentLib AsanAcct. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.X2W.AS Require Import AsanAcctImages. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.AS Require Import AxSymExec3 AxSymExec3Sound AxSymRun3. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.AS Require Import AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.X2W.AS Require Import BothPlanImages. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.AS Require Import AsanInit AsanNodesIface AsanNodesMmA AsanNodesMmB. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.X2W.AS Require Import SumsBothClose. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.AS Require Import AsanNodesStartX. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.X2W.AS Require Import AsanNodesStartXBoth. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.AS Require Import AsanMaxVA. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.AS Require Import AsanNodesMaxVA AsanNodesWJoin.
(* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition XN0 (id : nat) (args : list expr) (cs : acs) : option acs := None.
Definition XE0 (id : nat) (args : list expr) (cs : acs) : option (Z * list spiece * acs) := None.
Definition XB0 (id : nat) (args : list expr) (cs : acs) : option (acs * acs) := None.

Lemma XN0_sound : forall SEGS VSEGS A nx0 LIMIT SINV argH FS0, ext_stmt SEGS VSEGS A nx0 LIMIT XN0 SINV argH FS0.
Proof. intros ? ? ? ? ? ? ? ?. intros id args cs cs' E R FULL model T _ _ H. discriminate H. Qed.
Lemma XE0_sound : forall SEGS VSEGS A nx0 LIMIT SINV argH FS0, emit_stmt SEGS VSEGS A nx0 LIMIT XE0 SINV argH FS0.
Proof. intros ? ? ? ? ? ? ? ?. intros id args cs fd ps cs' E R FULL model T _ H _. discriminate H. Qed.
Lemma XB0_sound : forall SEGS VSEGS A nx0 LIMIT SINV argH FS0, ext2_stmt SEGS VSEGS A nx0 LIMIT XB0 SINV argH FS0.
Proof. intros ? ? ? ? ? ? ? ?. intros id args cs csa csb E R FULL model TA TB _ H. discriminate H. Qed.

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
  (* a worker : the launch, as AsanInit takes it *)
  Variable mbase : word.
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variable apc : N.
  Variable gid : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variable kb : KernelBuild.
  Variables nof sigm : word.
  Variable abt : bool.
  Variable urnd : InputStream.
  Variable efn : list byte.
  Variable sigdef : bool.
  Hypothesis Hlaunch : valid_launch (AsanInit.inp argv envp fs stdin uid gid hw groups net nof sigm abt urnd kb efn sigdef).
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw)
                      (AsanInit.inp argv envp fs stdin uid gid hw groups net nof sigm abt urnd kb efn sigdef).
  Variable SINV : env -> (word -> option byte) -> Prop.
  Hypothesis SINV_SINV0 : forall E M, SINV E M ->
    SINV0 BPH apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt urnd kb efn sigdef E M.
  Hypothesis SINV_frame : forall E M M', (forall a, argH0 sp rdraw argv envp kb efn E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  (* [comment removed for export] *)
  Variable nx0 : nat.
  Hypothesis Hnx0 : (NX0 <= nx0)%nat.
  Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
  (* a worker A1: the run reads ASEGS ++ VSEGS (declared last, so callers append it) *)
  Variable VSEGS : list Segment.
  Hypothesis VSEGS_nx : Forall (fun s => seg_executable s = false) VSEGS.

  Theorem both_node_x_sound_all : forall x,
    x_stmt BSEGS VSEGS BOTH nx0 AsanInit.LIMIT (rseq_z (kb_rseq kb)) SINV (argH0 sp rdraw argv envp kb efn) FS0 x.
  Proof.
    pose proof (argH0_high apc sp rdraw argv envp Hsp Hva kb efn) as AH.
    assert (AA : forall E E' (a : word), env_agree nx0 E E' ->
                   argH0 sp rdraw argv envp kb efn E a = argH0 sp rdraw argv envp kb efn E' a).
    { intros E E' a [Hag Hb]. apply (argH0_agree sp rdraw argv envp kb efn). split; [|exact Hb]. intros n Hn. apply Hag. lia. }
    intros [ | | | | | | | | | | ].
    - apply (both_node_x_sound_XIMemset nx0 AsanInit.LIMIT _ SINV _ AH AA SINV_frame SINV_agree FS0 VSEGS VSEGS_nx).
    - apply (both_node_x_sound_XIMemcpy nx0 AsanInit.LIMIT _ SINV _ AH AA SINV_frame SINV_agree FS0 VSEGS VSEGS_nx).
    - apply (both_node_x_sound_XMemset nx0 AsanInit.LIMIT _ SINV _ AH AA SINV_frame SINV_agree FS0 VSEGS VSEGS_nx).
    - apply (both_node_x_sound_XMemcpy nx0 AsanInit.LIMIT _ SINV _ AH AA SINV_frame SINV_agree FS0 VSEGS VSEGS_nx).
    - apply (both_node_x_sound_XMemIsZero nx0 AsanInit.LIMIT _ SINV _ AH AA SINV_frame SINV_agree FS0 VSEGS VSEGS_nx).
    - apply (node_x_sound_XEnvScan_asan_gen sp rdraw brk0 mbase argv envp fs stdin FS0 Hsp Hva Hve uid hw Hfit
               apc gid groups net kb nof sigm abt urnd efn sigdef Hlaunch Hlau VSEGS VSEGS_nx SINV SINV_SINV0 SINV_frame nx0 Hnx0).
    - apply (node_x_sound_XPnScan_asan_gen sp rdraw brk0 mbase argv envp fs stdin FS0 Hsp Hva Hve uid hw Hfit
               apc gid groups net kb nof sigm abt urnd efn sigdef Hlau VSEGS VSEGS_nx SINV SINV_SINV0 SINV_frame nx0 Hnx0 SINV_agree).
    - apply x_sound_layout.
    - apply (both_node_x_sound_XIStrncpy nx0 AsanInit.LIMIT _ SINV _ AH AA SINV_frame SINV_agree FS0 VSEGS VSEGS_nx).
    - apply (both_node_x_sound_XPopFree nx0 AsanInit.LIMIT _ SINV _ AH AA SINV_frame SINV_agree FS0 VSEGS VSEGS_nx).
    - apply (x_sound_maxva BSEGS VSEGS VSEGS_nx BOTH nx0 AsanInit.LIMIT _ SINV _ FS0 both_wx both_in_hull both_hull_ok SINV_frame both_maxva_range both_maxva_code).
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
  Variable lim : Z.   (* [comment removed for export] *)
  Hypothesis Hlim : AsanInit.LIMIT <= lim.
  (* a worker : the kernel build, the AT_EXECFN string and the SIGPIPE default are launch inputs *)
  Variable kb : KernelBuild.
  Variable efn : list byte.
  Variable sigdef : bool.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk BSEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.
  #[local] Notation APC := TgtO_zlib_uncompress_fuzzer_both.M.init_pc.
  #[local] Notation INP := (AsanInit.inp argv envp fs stdin uid gid hw groups net nof sigm abt urnd kb efn sigdef).
  Hypothesis Hlaunch : valid_launch INP.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.

  #[local] Notation SINV := (SINV0 BPH APC sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt urnd kb efn sigdef).
  #[local] Notation argH := (argH0 sp rdraw argv envp kb efn).
  #[local] Notation E0a := (AsanInit.E0 sp rdraw brk0 mbase argv envp uid gid hw kb efn).
  #[local] Notation LIM := AsanInit.LIMIT.
  #[local] Notation RZK := (rseq_z (kb_rseq kb)).

  (* [comment removed for export] *)
  Variable IT0b : itab.
  Hypothesis IT0b_ok : itab_sound BSEGS IT0b.
  (* [comment removed for export] *)
  Variable HS_both : nat -> option acs.     (* [comment removed for export] *)
  Variable startup_plan_both : plan.
  Variable startup_shape_both : shape.
  Variables KC0 BFUEL FUEL : nat.
  Hypothesis startup_cert_both :
    check BSEGS IT0b BOTH NX0 LIM RZK (XNS BSEGS BOTH NX0 LIM) XE0 XB0 HS_both KC0 BFUEL FUEL None (both_init RZK) startup_plan_both
    = COk startup_shape_both.

  (* [comment removed for export] *)
  (* a worker A1: the run reads ASEGS ++ VSEGS (Run.run_segments; VSEGS = the vDSO pair, which is not
     executable and reserves nothing: TopLevel.vdso_nonexec / run_segments_reserved) *)
  Variable VSEGS : list Segment.
  Hypothesis VSEGS_nx : Forall (fun s => seg_executable s = false) VSEGS.
  Hypothesis VSEGS_res : segments_reserved VSEGS = [].
  Variable HOLES : nat -> env -> Fs.Fs -> TSet.
  Hypothesis HOLES_agree : forall h E E' fs', env_agree NX0 E E' -> HOLES h E fs' = HOLES h E' fs'.
  Hypothesis HOLES_nil : forall h E fs', HOLES h E fs' [].
  Hypothesis HOLES_sound : holes_stmt BSEGS VSEGS BOTH LIM HS_both SINV argH HOLES fs.

  (* [comment removed for export] *)
  Let AH := argH0_high APC sp rdraw argv envp Hsp Hva kb efn.
  Let AH2 := argH0_high2 BPH APC sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net Hsp Hva Hve Hfit
               nof sigm abt urnd kb efn sigdef Hlau.
  Let AA := argH0_agree sp rdraw argv envp kb efn.
  Let SF := SINV0_frame BPH APC sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt urnd kb efn sigdef.
  Let SA := SINV0_agree BPH APC sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt urnd kb efn sigdef.

  Theorem both_startup :
    srealizes (BSEGS ++ VSEGS) (init_config (BSEGS ++ VSEGS) APC BPH sp brk0 mbase rdraw lim INP)
              (sd HOLES t_nil E0a fs startup_shape_both).
  Proof.
    pose proof both_img_facts as IMG.
    rewrite (init_cfg_eq_run BSEGS BOTH BPH APC sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net eq_refl
               nof sigm abt urnd lim kb efn sigdef VSEGS VSEGS_res).
    pose proof (init_cs_ok BSEGS BOTH BPH APC sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net
                  IMG eq_refl Hsp Hbrk Hmb Hva Hve Hfit Huid Hhw nof sigm abt urnd lim Hlim kb efn sigdef Hlaunch Hlau) as HC.
    pose proof (check_sound BSEGS VSEGS VSEGS_nx IT0b IT0b_ok BOTH NX0 (le_n NX0) LIM RZK HS_both (XNS BSEGS BOTH NX0 LIM) XE0 XB0
              both_wx both_in_hull both_hull_ok both_shadow_ok SINV argH AH AA SF SA
              HOLES HOLES_agree HOLES_nil fs KC0
              (AsanNodesMmB.node_sys_sound BSEGS VSEGS VSEGS_nx BOTH NX0 LIM SINV argH fs both_res_len both_hull_ok both_shadow_ok AH2 AA SF SA)
              (AsanNodesMmB.node_brk2_sound BSEGS VSEGS VSEGS_nx BOTH NX0 LIM SINV argH fs both_in_hull both_res_len both_hull_ok both_shadow_ok AH AH2 SF)
              (node_mmap2_sound_OBL BSEGS VSEGS VSEGS_nx BOTH NX0 LIM SINV argH fs both_in_hull both_res_len both_res_hull both_hull_ok both_shadow_ok both_hull_cov AH AH2 AA SF SA)
              (node_mmapin_sound_OBL BSEGS VSEGS VSEGS_nx BOTH NX0 LIM SINV argH fs both_in_hull both_res_len both_res_hull both_hull_ok both_shadow_ok both_hull_cov AH AH2 AA SF SA)
              (node_mprotect2_sound_OBL BSEGS VSEGS VSEGS_nx BOTH NX0 LIM SINV argH fs both_in_hull both_res_len both_res_hull both_hull_ok both_shadow_ok both_hull_cov AH AH2 AA SF SA)
              (AsanNodesMmB.node_exit_sound BSEGS VSEGS VSEGS_nx BOTH LIM SINV argH fs)
              (both_node_x_sound_all sp rdraw brk0 argv envp fs Hsp Hva Hve uid hw Hfit mbase fs stdin APC gid groups net kb
                 nof sigm abt urnd efn sigdef Hlaunch Hlau SINV (fun E M H => H) SF NX0 (le_n NX0) SA VSEGS VSEGS_nx)
              (node_join_sound BSEGS VSEGS BOTH NX0 LIM SINV argH fs)
              (XNS_sound BSEGS VSEGS BOTH NX0 LIM SINV argH fs AA SA both_in_hull both_hull_ok both_shadow_ok AH AH2) (XE0_sound _ _ _ _ _ _ _ _) (XB0_sound _ _ _ _ _ _ _ _)
              HOLES_sound FUEL BFUEL None startup_plan_both (both_init RZK) startup_shape_both startup_cert_both
              _ _ _ _ t_nil HC I eq_refl) as R.
    exact R.
  Qed.
End Startup.
