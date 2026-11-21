(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* AS/AsanStartup = our text + 's own edits to theories/Common/AsanStartup.v, 3-way merged (proposal md5 ); the old text is kept aside *)
(* A1 split: XAll and Startup gain VSEGS + VSEGS_nx (+ VSEGS_res); asan_startup is stated over the run's list ASEGS ++ VSEGS (init_cfg_eq_run) *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.World Require Import Tgt_zlib_uncompress2_fuzzer_asan.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.AS Require Import
  PropExec ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctImages AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2 AsanPlanImages AsanInit
  AsanNodesIface AsanNodesMmA AsanNodesMmB SumsAsanClose AsanNodesStartX AsanNodesStartXAsan AsanMaxVA AsanNodesMaxVA AsanNodesWJoin.
Unset Lia Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

Definition XN0 (id : nat) (args : list expr) (cs : acs) : option acs := None.
Definition XE0 (id : nat) (args : list expr) (cs : acs) : option (Z * list spiece * acs) := None.
Definition XB0 (id : nat) (args : list expr) (cs : acs) : option (acs * acs) := None.

Lemma XN0_sound : forall SEGS VSEGS A nx0 LIMIT SINV argH FS0, ext_stmt SEGS VSEGS A nx0 LIMIT XN0 SINV argH FS0.
Proof. intros ? ? ? ? ? ? ? ?. intros id args cs cs' E R FULL model T _ _ H. discriminate H. Qed.
Lemma XE0_sound : forall SEGS VSEGS A nx0 LIMIT SINV argH FS0, emit_stmt SEGS VSEGS A nx0 LIMIT XE0 SINV argH FS0.
Proof. intros ? ? ? ? ? ? ? ?. intros id args cs fd ps cs' E R FULL model T _ H _. discriminate H. Qed.
Lemma XB0_sound : forall SEGS VSEGS A nx0 LIMIT SINV argH FS0, ext2_stmt SEGS VSEGS A nx0 LIMIT XB0 SINV argH FS0.
Proof. intros ? ? ? ? ? ? ? ?. intros id args cs csa csb E R FULL model TA TB _ H. discriminate H. Qed.

Lemma asan_maxva_code : forall i, (i < 45)%nat ->
  fetch_word ASEGS (Z_to_bv 64 (x_maxva ASAN + 4 * Z.of_nat i)) = Some (nth i MAXVA_WORDS W0).
Proof.
  intros i Hi. cbn [x_maxva ASAN].
  do 45 (destruct i as [|i];
    [cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Z.add Pos.mul Pos.add nth MAXVA_WORDS];
     lazymatch goal with |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true) end |]).
  exfalso. lia.
Qed.

Lemma asan_maxva_range : 0 < x_maxva ASAN /\ x_maxva ASAN + 180 < 2 ^ 64.
Proof. cbn [x_maxva ASAN]. lia. Qed.

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
  (* the launch, as AsanInit takes it *)
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
    SINV0 APH apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt urnd kb efn sigdef E M.
  Hypothesis SINV_frame : forall E M M', (forall a, argH0 sp rdraw argv envp kb efn E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Variable nx0 : nat.
  Hypothesis Hnx0 : (NX0 <= nx0)%nat.
  Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
  (* the run reads ASEGS ++ VSEGS (declared last, so callers append it) *)
  Variable VSEGS : list Segment.
  Hypothesis VSEGS_nx : Forall (fun s => seg_executable s = false) VSEGS.

  Theorem asan_node_x_sound_all : forall x,
    x_stmt ASEGS VSEGS ASAN nx0 AsanInit.LIMIT (rseq_z (kb_rseq kb)) SINV (argH0 sp rdraw argv envp kb efn) FS0 x.
  Proof.
    pose proof (argH0_high apc sp rdraw argv envp Hsp Hva kb efn) as AH.
    assert (AA : forall E E' (a : word), env_agree nx0 E E' ->
                   argH0 sp rdraw argv envp kb efn E a = argH0 sp rdraw argv envp kb efn E' a).
    { intros E E' a [Hag Hb]. apply (argH0_agree sp rdraw argv envp kb efn). split; [|exact Hb]. intros n Hn. apply Hag. lia. }
    intros [ | | | | | | | | | | ].
    - apply (asan_node_x_sound_XIMemset nx0 AsanInit.LIMIT _ SINV _ AH AA SINV_frame SINV_agree FS0 VSEGS VSEGS_nx).
    - apply (asan_node_x_sound_XIMemcpy nx0 AsanInit.LIMIT _ SINV _ AH AA SINV_frame SINV_agree FS0 VSEGS VSEGS_nx).
    - apply (asan_node_x_sound_XMemset nx0 AsanInit.LIMIT _ SINV _ AH AA SINV_frame SINV_agree FS0 VSEGS VSEGS_nx).
    - apply (asan_node_x_sound_XMemcpy nx0 AsanInit.LIMIT _ SINV _ AH AA SINV_frame SINV_agree FS0 VSEGS VSEGS_nx).
    - apply (asan_node_x_sound_XMemIsZero nx0 AsanInit.LIMIT _ SINV _ AH AA SINV_frame SINV_agree FS0 VSEGS VSEGS_nx).
    - apply (node_x_sound_XEnvScan_asan_gen sp rdraw brk0 mbase argv envp fs stdin FS0 Hsp Hva Hve uid hw Hfit
               apc gid groups net kb nof sigm abt urnd efn sigdef Hlaunch Hlau VSEGS VSEGS_nx SINV SINV_SINV0 SINV_frame nx0 Hnx0).
    - apply (node_x_sound_XPnScan_asan_gen sp rdraw brk0 mbase argv envp fs stdin FS0 Hsp Hva Hve uid hw Hfit
               apc gid groups net kb nof sigm abt urnd efn sigdef Hlau VSEGS VSEGS_nx SINV SINV_SINV0 SINV_frame nx0 Hnx0 SINV_agree).
    - apply x_sound_layout.
    - apply (asan_node_x_sound_XIStrncpy nx0 AsanInit.LIMIT _ SINV _ AH AA SINV_frame SINV_agree FS0 VSEGS VSEGS_nx).
    - apply (asan_node_x_sound_XPopFree nx0 AsanInit.LIMIT _ SINV _ AH AA SINV_frame SINV_agree FS0 VSEGS VSEGS_nx).
    - apply (x_sound_maxva ASEGS VSEGS VSEGS_nx ASAN nx0 AsanInit.LIMIT _ SINV _ FS0 asan_wx asan_in_hull asan_hull_ok SINV_frame asan_maxva_range asan_maxva_code).
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
  Variable lim : Z.
  Hypothesis Hlim : AsanInit.LIMIT <= lim.
  (* the kernel build, the AT_EXECFN string and the SIGPIPE default are launch inputs *)
  Variable kb : KernelBuild.
  Variable efn : list byte.
  Variable sigdef : bool.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk ASEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.
  #[local] Notation APC := Tgt_zlib_uncompress2_fuzzer_asan.M.init_pc.
  #[local] Notation INP := (AsanInit.inp argv envp fs stdin uid gid hw groups net nof sigm abt urnd kb efn sigdef).
  Hypothesis Hlaunch : valid_launch INP.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.

  #[local] Notation SINV := (SINV0 APH APC sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt urnd kb efn sigdef).
  #[local] Notation argH := (argH0 sp rdraw argv envp kb efn).
  #[local] Notation E0a := (AsanInit.E0 sp rdraw brk0 mbase argv envp uid gid hw kb efn).
  #[local] Notation LIM := AsanInit.LIMIT.
  #[local] Notation RZK := (rseq_z (kb_rseq kb)).

  Variable IT0 : itab.
  Hypothesis IT0_ok : itab_sound ASEGS IT0.
  Variable HS_asan : nat -> option acs.
  Variable startup_plan : plan.
  Variable startup_shape : shape.
  Variables KC0 BFUEL FUEL : nat.
  Hypothesis startup_cert :
    check ASEGS IT0 ASAN NX0 LIM RZK (XNS ASEGS ASAN NX0 LIM) XE0 XB0 HS_asan KC0 BFUEL FUEL None (asan_init RZK) startup_plan
    = COk startup_shape.

  (* the run reads ASEGS ++ VSEGS (Run.run_segments; VSEGS = the vDSO pair, which is not
     executable and reserves nothing: TopLevel.vdso_nonexec / run_segments_reserved) *)
  Variable VSEGS : list Segment.
  Hypothesis VSEGS_nx : Forall (fun s => seg_executable s = false) VSEGS.
  Hypothesis VSEGS_res : segments_reserved VSEGS = [].
  Variable HOLES : nat -> env -> Fs.Fs -> TSet.
  Hypothesis HOLES_agree : forall h E E' fs', env_agree NX0 E E' -> HOLES h E fs' = HOLES h E' fs'.
  Hypothesis HOLES_nil : forall h E fs', HOLES h E fs' [].
  Hypothesis HOLES_sound : holes_stmt ASEGS VSEGS ASAN LIM HS_asan SINV argH HOLES fs.

  Let AH := argH0_high APC sp rdraw argv envp Hsp Hva kb efn.
  Let AH2 := argH0_high2 APH APC sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net Hsp Hva Hve Hfit
               nof sigm abt urnd kb efn sigdef Hlau.
  Let AA := argH0_agree sp rdraw argv envp kb efn.
  Let SF := SINV0_frame APH APC sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt urnd kb efn sigdef.
  Let SA := SINV0_agree APH APC sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt urnd kb efn sigdef.

  Theorem asan_startup :
    srealizes (ASEGS ++ VSEGS) (init_config (ASEGS ++ VSEGS) APC APH sp brk0 mbase rdraw lim INP)
              (sd HOLES t_nil E0a fs startup_shape).
  Proof.
    pose proof asan_img_facts as IMG.
    rewrite (init_cfg_eq_run ASEGS ASAN APH APC sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net eq_refl
               nof sigm abt urnd lim kb efn sigdef VSEGS VSEGS_res).
    pose proof (init_cs_ok ASEGS ASAN APH APC sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net
                  IMG eq_refl Hsp Hbrk Hmb Hva Hve Hfit Huid Hhw nof sigm abt urnd lim Hlim kb efn sigdef Hlaunch Hlau) as HC.
    pose proof (check_sound ASEGS VSEGS VSEGS_nx IT0 IT0_ok ASAN NX0 (le_n NX0) LIM RZK HS_asan (XNS ASEGS ASAN NX0 LIM) XE0 XB0
              asan_wx asan_in_hull asan_hull_ok asan_shadow_ok SINV argH AH AA SF SA
              HOLES HOLES_agree HOLES_nil fs KC0
              (AsanNodesMmB.node_sys_sound ASEGS VSEGS VSEGS_nx ASAN NX0 LIM SINV argH fs asan_res_len asan_hull_ok asan_shadow_ok AH2 AA SF SA)
              (AsanNodesMmB.node_brk2_sound ASEGS VSEGS VSEGS_nx ASAN NX0 LIM SINV argH fs asan_in_hull asan_res_len asan_hull_ok asan_shadow_ok AH AH2 SF)
              (node_mmap2_sound_OBL ASEGS VSEGS VSEGS_nx ASAN NX0 LIM SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_hull_cov AH AH2 AA SF SA)
              (node_mmapin_sound_OBL ASEGS VSEGS VSEGS_nx ASAN NX0 LIM SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_hull_cov AH AH2 AA SF SA)
              (node_mprotect2_sound_OBL ASEGS VSEGS VSEGS_nx ASAN NX0 LIM SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_hull_cov AH AH2 AA SF SA)
              (AsanNodesMmB.node_exit_sound ASEGS VSEGS VSEGS_nx ASAN LIM SINV argH fs)
              (asan_node_x_sound_all sp rdraw brk0 argv envp fs Hsp Hva Hve uid hw Hfit mbase fs stdin APC gid groups net kb
                 nof sigm abt urnd efn sigdef Hlaunch Hlau SINV (fun E M H => H) SF NX0 (le_n NX0) SA VSEGS VSEGS_nx)
              (node_join_sound ASEGS VSEGS ASAN NX0 LIM SINV argH fs)
              (XNS_sound ASEGS VSEGS ASAN NX0 LIM SINV argH fs AA SA asan_in_hull asan_hull_ok asan_shadow_ok AH AH2) (XE0_sound _ _ _ _ _ _ _ _) (XB0_sound _ _ _ _ _ _ _ _)
              HOLES_sound FUEL BFUEL None startup_plan (asan_init RZK) startup_shape startup_cert
              _ _ _ _ t_nil HC I eq_refl) as R.
    exact R.
  Qed.
End Startup.
