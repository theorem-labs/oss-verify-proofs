(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: Sections XAll and Startup take the entry address apc, the mmap base, the launch's whole input with its executable name and kernel build, and the valid_launch and entry_launch_ok_va premises; asan_node_x_sound_all is stated at the run's rseq flag; and startup_cert, startup2_cert and startup_certB hold for both values of the flag; the launch's SIGPIPE disposition sgd is a Section variable, passed after kb. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Monad.
From LinuxProcessSemantics.LinuxProcessSem Require Specs.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From OSSVerify.cjson.cjson_read_fuzzer.images Require Asan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require SpinAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require MemSplit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanAcct.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanAcctImages.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AxSymExec3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AxSymExec3Sound.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AxSymRun3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanPlanCore.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanPlan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanPlanSound.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanPlanSound2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanPlanImages.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanInit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanNodesIface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanNodesMmA.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanNodesMmB.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require SumsAsanClose.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanNodesStartX.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanNodesStartXAsan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanMaxVA.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanNodesMaxVA.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanNodesWJoin.
Module AsanStartup.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.cjson.cjson_read_fuzzer.images.Asan.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.ShapeAlg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.SpinAlg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.MemSplit.AgentLib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanAcct OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanAcctImages OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AxSymExec3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AxSymExec3Sound OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AxSymRun3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanCore OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanSound OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanSound2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanImages OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanInit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanNodesIface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanNodesMmA OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanNodesMmB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.SumsAsanClose OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanNodesStartX OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanNodesStartXAsan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanMaxVA OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanNodesMaxVA OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanNodesWJoin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

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

(* [comment removed for export] *)
Section XAll.
  Variable apc : N.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable stdin : InputStream.
  Variable FS0 : Fs.Fs.
  Variable uid gid : word.
  Variable hw : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nof sigm : word.
  Variable abt : bool.
  Variable ifs : Fs.Fs.
  Variable urnd : InputStream.
  Variable tmp : Fs.Fs.
  Variable xfn : list byte.
  (* the kernel build: AsanInit's Section declares it right after xfn, so it is the argument after xfn at
     every AsanInit export below; it is never instantiated here. *)
  Variable kb : KernelBuild.
  (* the launch's SIGPIPE disposition (in_sigpipe_default), which Run.valid_input leaves free *)
  Variable sgd : bool.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  (* the launch's validity: AsanInit's Section takes it right after kb, and the _asan_gen applications below
     pass it in that place. A Section hypothesis carries it without changing any record a replay reads; it is
     discharged at the top by Run.valid_input_launch (A/ATop.v). *)
  Hypothesis Hlaunch : valid_launch (AsanInit.inp argv envp stdin uid gid hw groups net nof sigm abt ifs urnd tmp xfn kb sgd).
  (* the launch placement: AsanInit declares it right after Hlaunch and its exports take the pair in that
     order; it is discharged at the top from valid_entry (A/ATop.v). *)
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw)
                      (AsanInit.inp argv envp stdin uid gid hw groups net nof sigm abt ifs urnd tmp xfn kb sgd).
  Variable SINV : env -> (word -> option byte) -> Prop.
  Hypothesis SINV_SINV0 : forall E M, SINV E M ->
    SINV0 APH apc sp rdraw brk0 mbase argv envp stdin uid gid hw groups net nof sigm abt ifs urnd tmp xfn kb sgd E M.
  Hypothesis SINV_frame : forall E M M', (forall a, argH0 sp rdraw argv envp xfn kb E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  (* [comment removed for export] *)
  Variable nx0 : nat.
  Hypothesis Hnx0 : (NX0 <= nx0)%nat.
  Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

  (* [rz] is NOT a new Section variable: writing it inline as (rseq_z (kb_rseq kb)) adds no
     binder, so no positional application of this Section's own exports shifts.  AsanPlanSound
     declares rz at :102, immediately after LIMIT (:98) and before HS (:108), so rz goes
     immediately after LIMIT at every site below, exactly as kb goes immediately after xfn. *)
  Theorem asan_node_x_sound_all : forall x, x_stmt ASEGS ASAN nx0 AsanInit.LIMIT (rseq_z (kb_rseq kb)) SINV (argH0 sp rdraw argv envp xfn kb) FS0 x.
  Proof.
    pose proof (argH0_high apc sp rdraw argv envp Hsp Hva xfn kb) as AH.
    assert (AA : forall E E' (a : word), env_agree nx0 E E' -> argH0 sp rdraw argv envp xfn kb E a = argH0 sp rdraw argv envp xfn kb E' a).
    { intros E E' a [Hag Hb]. apply (argH0_agree sp rdraw argv envp xfn kb). split; [|exact Hb]. intros n Hn. apply Hag. lia. }
    intros [ | | | | | | | | | | ].
    - apply (asan_node_x_sound_XIMemset nx0 AsanInit.LIMIT (rseq_z (kb_rseq kb)) SINV _ AH AA SINV_frame SINV_agree FS0).
    - apply (asan_node_x_sound_XIMemcpy nx0 AsanInit.LIMIT (rseq_z (kb_rseq kb)) SINV _ AH AA SINV_frame SINV_agree FS0).
    - apply (asan_node_x_sound_XMemset nx0 AsanInit.LIMIT (rseq_z (kb_rseq kb)) SINV _ AH AA SINV_frame SINV_agree FS0).
    - apply (asan_node_x_sound_XMemcpy nx0 AsanInit.LIMIT (rseq_z (kb_rseq kb)) SINV _ AH AA SINV_frame SINV_agree FS0).
    - apply (asan_node_x_sound_XMemIsZero nx0 AsanInit.LIMIT (rseq_z (kb_rseq kb)) SINV _ AH AA SINV_frame SINV_agree FS0).
    (* Hlaunch goes between Hfit and SINV, where AsanInit declares it relative to kb. *)
    - apply (node_x_sound_XEnvScan_asan_gen apc sp rdraw brk0 mbase argv envp stdin FS0 uid gid hw groups net nof sigm abt ifs urnd tmp xfn kb sgd Hsp Hva Hve Hfit Hlaunch Hlau SINV SINV_SINV0 SINV_frame nx0 Hnx0).
    (* XPnScan takes Hlau but not Hlaunch, and XEnvScan above takes both: Rocq abstracts a definition over the
       Section variables it uses, so two exports of one Section can differ in arity, and the argument lists of
       the twin nodes are not interchangeable. *)
    - apply (node_x_sound_XPnScan_asan_gen apc sp rdraw brk0 mbase argv envp stdin FS0 uid gid hw groups net nof sigm abt ifs urnd tmp xfn kb sgd Hsp Hva Hve Hfit Hlau SINV SINV_SINV0 SINV_frame nx0 Hnx0 SINV_agree).
    - apply x_sound_layout.
    - apply (asan_node_x_sound_XIStrncpy nx0 AsanInit.LIMIT (rseq_z (kb_rseq kb)) SINV _ AH AA SINV_frame SINV_agree FS0).
    - apply (asan_node_x_sound_XPopFree nx0 AsanInit.LIMIT (rseq_z (kb_rseq kb)) SINV _ AH AA SINV_frame SINV_agree FS0).
    - apply (x_sound_maxva ASEGS ASAN nx0 AsanInit.LIMIT (rseq_z (kb_rseq kb)) SINV _ FS0 asan_wx asan_in_hull asan_hull_ok SINV_frame asan_maxva_range asan_maxva_code).
  Qed.
End XAll.

Section Startup.
  (* [comment removed for export] *)
  Variable apc : N.
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
  (* [comment removed for export] *)
  Variable ifs : Fs.Fs.
  Variable urnd : InputStream.
  Variable tmp : Fs.Fs.
  Variable xfn : list byte.
  (* see the note in Section XAll: kb sits immediately after xfn in every AsanInit export *)
  Variable kb : KernelBuild.
  (* the launch's SIGPIPE disposition (in_sigpipe_default), which Run.valid_input leaves free *)
  Variable sgd : bool.
  Hypothesis Hfs : fs = fs_seed_tmp ifs tmp.
  Hypothesis Hapc : Z.of_N apc = a_entry ASAN.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk ASEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.
  Hypothesis Hlaunch : valid_launch (AsanInit.inp argv envp stdin uid gid hw groups net nof sigm abt ifs urnd tmp xfn kb sgd).
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw)
                      (AsanInit.inp argv envp stdin uid gid hw groups net nof sigm abt ifs urnd tmp xfn kb sgd).

  #[local] Notation SINV := (SINV0 APH apc sp rdraw brk0 mbase argv envp stdin uid gid hw groups net nof sigm abt ifs urnd tmp xfn kb sgd).
  #[local] Notation argH := (argH0 sp rdraw argv envp xfn kb).
  #[local] Notation E0a := (AsanInit.E0 sp rdraw brk0 argv envp uid gid hw xfn kb).
  #[local] Notation LIM := AsanInit.LIMIT.

  (* [comment removed for export] *)
  Variable IT0 : itab.
  Hypothesis IT0_ok : itab_sound ASEGS IT0.
  (* [comment removed for export] *)
  Variable HS_asan : nat -> option acs.     (* [comment removed for export] *)
  Variable startup_plan : plan.
  Variable startup_shape : shape.
  Variables KC0 BFUEL FUEL : nat.
  (* AsanPlan's Section WithSegs declares rz between LIMIT and Section Check, so the discharged check takes
     segs IT A nx0 LIMIT rz XN XE XB HS KC bfuel fuel lc cs p. rz is the run's own flag, rseq_z (kb_rseq kb),
     as check_sound below takes it, never a literal. *)
  Hypothesis startup_cert :
    check ASEGS IT0 ASAN NX0 LIM (rseq_z (kb_rseq kb)) (XNS ASEGS ASAN NX0 LIM) XE0 XB0 HS_asan KC0 BFUEL FUEL None (asan_init (rseq_z (kb_rseq kb))) startup_plan = COk startup_shape.

  (* [comment removed for export] *)
  Variable HOLES : nat -> env -> Fs.Fs -> TSet.
  Hypothesis HOLES_agree : forall h E E' fs', env_agree NX0 E E' -> HOLES h E fs' = HOLES h E' fs'.
  Hypothesis HOLES_nil : forall h E fs', HOLES h E fs' [].
  Hypothesis HOLES_sound : holes_stmt ASEGS ASAN LIM HS_asan SINV argH HOLES fs.

  (* [comment removed for export] *)
  Let AH := argH0_high apc sp rdraw argv envp Hsp Hva xfn kb.
  Let AH2 := argH0_high2 APH apc sp rdraw brk0 mbase argv envp stdin uid gid hw groups net Hsp Hva Hve Hfit nof sigm abt ifs urnd tmp xfn kb sgd Hlau.
  Let AA := argH0_agree sp rdraw argv envp xfn kb.
  Let SF := SINV0_frame APH apc sp rdraw brk0 mbase argv envp stdin uid gid hw groups net nof sigm abt ifs urnd tmp xfn kb sgd.
  Let SA := SINV0_agree APH apc sp rdraw brk0 mbase argv envp stdin uid gid hw groups net nof sigm abt ifs urnd tmp xfn kb sgd.

  Theorem asan_startup :
    srealizes ASEGS (init_config ASEGS apc APH sp brk0 mbase rdraw LIM
                                 (AsanInit.inp argv envp stdin uid gid hw groups net nof sigm abt ifs urnd tmp xfn kb sgd))
              (sd HOLES t_nil E0a fs startup_shape).
  Proof.
    pose proof asan_img_facts as IMG.
    rewrite (init_cfg_eq ASEGS ASAN APH apc sp rdraw brk0 mbase argv envp stdin uid gid hw groups net Hapc nof sigm abt ifs urnd tmp xfn kb sgd).
    pose proof (init_cs_ok ASEGS ASAN APH apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net IMG Hapc Hsp Hbrk Hmb Hva Hve Hfit Huid Hhw nof sigm abt ifs urnd tmp Hfs xfn kb sgd Hlaunch Hlau) as HC.
    pose proof (check_sound ASEGS IT0 IT0_ok ASAN NX0 (le_n NX0) LIM (rseq_z (kb_rseq kb)) HS_asan (XNS ASEGS ASAN NX0 LIM) XE0 XB0
              asan_wx asan_in_hull asan_hull_ok asan_shadow_ok SINV argH AH AA SF SA
              HOLES HOLES_agree HOLES_nil fs KC0
              (AsanNodesMmB.node_sys_sound ASEGS ASAN NX0 LIM SINV argH fs asan_res_len asan_hull_ok asan_shadow_ok AH2 AA SF SA)
              (AsanNodesMmB.node_brk2_sound ASEGS ASAN NX0 LIM SINV argH fs asan_in_hull asan_res_len asan_hull_ok asan_shadow_ok AH AH2 SF)
              (node_mmap2_sound_OBL ASEGS ASAN NX0 LIM SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_hull_cov AH AH2 AA SF SA)
              (node_mmapin_sound_OBL ASEGS ASAN NX0 LIM SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_hull_cov AH AH2 AA SF SA)
              (node_mprotect2_sound_OBL ASEGS ASAN NX0 LIM SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_hull_cov AH AH2 AA SF SA)
              (AsanNodesMmB.node_exit_sound ASEGS ASAN LIM SINV argH fs)
              (* asan_node_x_sound_all abstracts over Section XAll's Hlaunch and Hlau (its XEnvScan arm uses
                 both), so they go here in that order; Section Startup declares both. *)
              (asan_node_x_sound_all apc sp rdraw brk0 mbase argv envp stdin fs uid gid hw groups net nof sigm abt ifs urnd tmp xfn kb sgd Hsp Hva Hve Hfit Hlaunch Hlau SINV (fun E M H => H) SF NX0 (le_n NX0) SA)
              (node_join_sound ASEGS ASAN NX0 LIM SINV argH fs)
              (XNS_sound ASEGS ASAN NX0 LIM SINV argH fs AA SA asan_in_hull asan_hull_ok asan_shadow_ok AH AH2) (XE0_sound _ _ _ _ _ _ _) (XB0_sound _ _ _ _ _ _ _)
              HOLES_sound FUEL BFUEL None startup_plan (asan_init (rseq_z (kb_rseq kb))) startup_shape startup_cert
              _ _ _ _ t_nil HC I eq_refl) as R.
    (* [comment removed for export] *)
    assert (EF : m_fs (model0 ASEGS sp rdraw brk0 mbase argv envp stdin uid gid hw groups net nof sigm abt ifs urnd tmp xfn kb sgd) = fs) by (rewrite Hfs; reflexivity).
    rewrite EF in R. exact R.
  Qed.
End Startup.
End AsanStartup.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require StartupPlanAsan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require StartupHSAsan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanStartupCertDefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require PlanRegen.
From Ltac2 Require Ltac2.
From Ltac2 Require Constr.
From Ltac2 Require Std.
From Ltac2 Require Control.
Module AsanStartupCert.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AxSymExec3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanCore OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanSound OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanImages OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanInit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanNodesWJoin AsanStartup OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.StartupPlanAsan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.StartupHSAsan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanStartupCertDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition IT0 : itab := mk_itab_ranges ASEGS [(0x30cb0, 20%nat); (0x37a50, 16%nat); (0x37b00, 12%nat); (0x38000, 36%nat); (0x380d0, 16%nat); (0x3d8e0, 880%nat); (0x3e6e0, 16%nat); (0x3e760, 36%nat); (0x3e810, 8%nat); (0x53130, 8%nat); (0x53810, 20%nat); (0x538e0, 24%nat); (0x53b00, 24%nat); (0x53c30, 28%nat); (0x5a580, 12%nat); (0x5ad10, 32%nat); (0x5b1d0, 48%nat); (0x5b6f0, 36%nat); (0x5bd20, 108%nat); (0x60050, 76%nat); (0x61840, 12%nat); (0x61ef0, 32%nat); (0x621a0, 44%nat); (0x63160, 88%nat); (0x635f0, 1208%nat); (0x64d70, 32%nat); (0x64e00, 32%nat); (0x64f00, 48%nat); (0x64fd0, 20%nat); (0x65080, 24%nat); (0x65160, 16%nat); (0x651c0, 68%nat); (0x65450, 20%nat); (0x654b0, 20%nat); (0x65790, 16%nat); (0x65800, 8%nat); (0x65970, 24%nat); (0x65bc0, 16%nat); (0x65c30, 36%nat); (0x66000, 20%nat); (0x662f0, 28%nat); (0x66e30, 80%nat); (0x676e0, 68%nat); (0x683d0, 24%nat); (0x68520, 16%nat); (0x6ef90, 8%nat); (0x7bde0, 272%nat); (0x7eca0, 12%nat); (0x81d30, 104%nat); (0x82530, 8%nat); (0x8d5c0, 32%nat); (0x8d660, 28%nat); (0x8d7c0, 96%nat); (0x8da00, 68%nat); (0x8dbe0, 100%nat); (0x8dd90, 97%nat); (0x9d864, 12%nat)]%Z.
Lemma IT0_ok : itab_sound ASEGS IT0.
Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition startup_shape : shape := SHole 10.
Import Ltac2.Ltac2 Ltac2.Constr Ltac2.Std Ltac2.Control.
Ltac2 vm_cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).
(* check takes the rseq flag rz after LIMIT (AsanPlan.v), and asan_init takes it too (asan_init rz :=
   init_acs_of rz ASAN). The certificate is quantified over the flag: intros [|] splits on the bool before any
   reduction, leaving two closed goals vm_cert_refl discharges one at a time, and the consumer takes it as
   startup_cert (kb_rseq kb). The shape is the same at both values. *)
(* LPS 727298f3 gives the launch two more variables (V_G and V_GID: NX0 11 -> 13) and a longer auxv walk, so
   the run numbers its fresh variables differently. The recorded plan is renumbered where it is checked: old
   78 is new 82 (the plan's first map base 4096 * EVar 78 is the run's 4096 * EVar 82), so every old variable
   from 13 up (the first fresh variable; V_G 11 and V_GID 12 are launch variables and keep their numbers)
   moves by 4. The hand-off state at 10 is computed here, per rz, by the plan's own run (collect_handoffs),
   and the certificate re-checks the plan against it. *)
Definition T_S1 : list (nat * nat) := [(13%nat, 4%nat)].
Definition startup_plan_k : plan := PlanRegen.psh (PlanRegen.tshift T_S1) startup_plan.
Definition run_S1 (b : bool) (js : nat -> option acs) : cres :=
  check ASEGS IT0 ASAN NX0 AsanInit.LIMIT (rseq_z b) (XNS ASEGS ASAN NX0 AsanInit.LIMIT) XE0 XB0 js KC0 BFUEL FUEL None
        (asan_init (rseq_z b)) startup_plan_k.
Definition HSL_S1_0 : list (nat * acs) := Eval vm_compute in PlanRegen.collect_handoffs 16 (run_S1 false) [].
Definition HSL_S1_1 : list (nat * acs) := Eval vm_compute in PlanRegen.collect_handoffs 16 (run_S1 true) [].
Definition HSA_10 (b : bool) : acs := PlanRegen.hstate (if b then HSL_S1_1 else HSL_S1_0) (asan_init (rseq_z b)) 10.
Definition HSA (b : bool) (h : nat) : option acs := if Nat.eqb h 10 then Some (HSA_10 b) else None.
(* The statement quantifies over the rseq flag (never pinned); `intros [|]` leaves two closed goals. *)
Lemma startup_cert : forall b : bool,
  check ASEGS IT0 ASAN NX0 AsanInit.LIMIT (rseq_z b) (XNS ASEGS ASAN NX0 AsanInit.LIMIT) XE0 XB0 (HSA b) KC0 BFUEL FUEL None (asan_init (rseq_z b)) startup_plan_k = COk startup_shape.
Proof.
  intros [|].
  (vm_cert_refl constr:(COk startup_shape)).
  (vm_cert_refl constr:(COk startup_shape)).
Qed.
End AsanStartupCert.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require StartupPlan2Asan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require StartupHS2Asan.
Module AsanStartupCert2.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AxSymExec3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanCore OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanSound OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanImages OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanInit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanNodesWJoin AsanStartup OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.StartupPlanAsan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.StartupHSAsan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanStartupCertDefs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.StartupPlan2Asan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.StartupHS2Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition IT2 : itab := mk_itab_ranges ASEGS startup2_plan_ranges.
Lemma IT2_ok : itab_sound ASEGS IT2.
Proof. apply APS.mk_itab_ranges_sound. Qed.
(* LPS 727298f3: startup2_cert starts from the hand-off 0 that segment D computes, so it lives in
   AsanBoot.v after segment D; IT2 stays here. *)
End AsanStartupCert2.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanImages AsanInit AsanNodesWJoin.
Import AsanStartup.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require Import StartupPlanAsan StartupHSAsan AsanStartupCertDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ITB : itab := mk_itab_ranges ASEGS [(0x30df0, 20%nat); (0x30f90, 88%nat); (0x331b0, 16%nat); (0x33200, 12%nat); (0x332d0, 12%nat); (0x333e0, 12%nat); (0x33420, 36%nat); (0x33540, 52%nat); (0x33690, 12%nat); (0x336e0, 24%nat); (0x33780, 24%nat); (0x343c0, 28%nat); (0x344b0, 16%nat); (0x41840, 16%nat); (0x42520, 8%nat); (0x483e0, 40%nat); (0x49480, 12%nat); (0x494c0, 40%nat); (0x53050, 64%nat); (0x53810, 28%nat); (0x538a0, 20%nat); (0x539b0, 8%nat); (0x539f0, 16%nat); (0x54130, 12%nat); (0x54bd0, 8%nat); (0x55670, 44%nat); (0x557d0, 12%nat); (0x558a0, 36%nat); (0x559d0, 24%nat); (0x55b70, 32%nat); (0x55ff0, 80%nat); (0x56160, 20%nat); (0x56760, 20%nat); (0x567d0, 32%nat); (0x5b330, 48%nat); (0x5b490, 20%nat); (0x5b960, 12%nat); (0x5bf00, 40%nat); (0x5c180, 20%nat); (0x5ce50, 24%nat); (0x5d6f0, 8%nat); (0x5d880, 52%nat); (0x5d960, 44%nat); (0x5dc90, 12%nat); (0x5e130, 20%nat); (0x5e190, 16%nat); (0x5e520, 24%nat); (0x5e660, 32%nat); (0x5e770, 32%nat); (0x5f870, 48%nat); (0x5f980, 84%nat); (0x60050, 76%nat); (0x60230, 8%nat); (0x61ef0, 16%nat); (0x65790, 8%nat); (0x65d50, 8%nat); (0x66000, 20%nat); (0x66f50, 8%nat); (0x67270, 28%nat); (0x67490, 8%nat); (0x676e0, 68%nat); (0x67870, 32%nat); (0x67d30, 72%nat); (0x683d0, 24%nat); (0x68520, 16%nat); (0x6b2f0, 12%nat); (0x6b340, 12%nat); (0x6b3c0, 60%nat); (0x6b4c0, 12%nat); (0x6b580, 40%nat); (0x6b6a0, 24%nat); (0x6b950, 96%nat); (0x6bb20, 8%nat); (0x6bb60, 140%nat); (0x6be10, 16%nat); (0x6ca60, 52%nat); (0x6d310, 12%nat); (0x6d360, 8%nat); (0x6dc40, 40%nat); (0x6e420, 40%nat); (0x6e690, 8%nat); (0x6e6d0, 8%nat); (0x6e710, 20%nat); (0x6e810, 24%nat); (0x6ecc0, 8%nat); (0x6ef90, 120%nat); (0x6f4e0, 16%nat); (0x6f540, 8%nat); (0x6f5d0, 8%nat); (0x6f760, 44%nat); (0x6f860, 12%nat); (0x6fe70, 16%nat); (0x6fed0, 24%nat); (0x700c0, 12%nat); (0x718c0, 28%nat); (0x8d5c0, 32%nat); (0x8d660, 28%nat); (0x8d7c0, 12%nat); (0x8e0f4, 56%nat); (0x8e594, 88%nat); (0x8e704, 20%nat); (0x9b5e4, 8%nat); (0x9bb14, 8%nat); (0x9bd04, 8%nat); (0x9bd94, 12%nat); (0x9be34, 16%nat); (0x9cee4, 16%nat); (0x9d294, 60%nat); (0x9d604, 32%nat); (0x9d6a4, 24%nat); (0x9d7a4, 28%nat); (0x9d824, 20%nat)]%Z.
Lemma ITB_ok : itab_sound ASEGS ITB.
Proof. apply APS.mk_itab_ranges_sound. Qed.
(* LPS 727298f3: startup_certB starts from the hand-off 13 that segment B1 computes, so it lives in
   AsanBoot.v (Module AsanStartupCertSB) after segment B1; ITB stays here. *)
