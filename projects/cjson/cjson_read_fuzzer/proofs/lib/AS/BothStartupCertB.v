(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: Sections XAll and Startup take the entry address apc, the mmap base, the launch's whole input with its executable name and kernel build, and the valid_launch and entry_launch_ok_va premises; both_node_x_sound_all is stated at the run's rseq flag; and startup_cert, startup2_cert and startup_certB hold for both values of the flag; the launch's SIGPIPE disposition sgd is a Section variable, passed after kb. *)
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
From OSSVerify.cjson.cjson_read_fuzzer.images Require AsanUbsan.
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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require BothPlanImages.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanInit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanNodesIface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanNodesMmA.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanNodesMmB.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require SumsBothClose.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanNodesStartX.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanNodesStartXBoth.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanMaxVA.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanNodesMaxVA.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanNodesWJoin.
Module BothStartup.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.cjson.cjson_read_fuzzer.images.AsanUbsan.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.ShapeAlg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.SpinAlg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.MemSplit.AgentLib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanAcct OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanAcctImages OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AxSymExec3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AxSymExec3Sound OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AxSymRun3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanCore OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanSound OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanSound2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.BothPlanImages OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanInit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanNodesIface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanNodesMmA OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanNodesMmB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.SumsBothClose OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanNodesStartX OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanNodesStartXBoth OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanMaxVA OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanNodesMaxVA OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanNodesWJoin.
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
  (* the launch's validity and placement, as in AS/AsanStartupCertB.v: AsanInit's Section takes Hlaunch right
     after kb and Hlau right after Hlaunch, and the _asan_gen applications below pass them in those places.
     Section hypotheses carry them without changing any record a replay reads; they are discharged at the top
     by Run.valid_input_launch and from valid_entry (A/ATop.v). This file's callees are
     AS/AsanNodesStartXBoth.v, which declare the same pair in the same order against INPb. *)
  Hypothesis Hlaunch : valid_launch (AsanInit.inp argv envp stdin uid gid hw groups net nof sigm abt ifs urnd tmp xfn kb sgd).
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw)
                      (AsanInit.inp argv envp stdin uid gid hw groups net nof sigm abt ifs urnd tmp xfn kb sgd).
  Variable SINV : env -> (word -> option byte) -> Prop.
  Hypothesis SINV_SINV0 : forall E M, SINV E M ->
    SINV0 BPH apc sp rdraw brk0 mbase argv envp stdin uid gid hw groups net nof sigm abt ifs urnd tmp xfn kb sgd E M.
  Hypothesis SINV_frame : forall E M M', (forall a, argH0 sp rdraw argv envp xfn kb E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  (* [comment removed for export] *)
  Variable nx0 : nat.
  Hypothesis Hnx0 : (NX0 <= nx0)%nat.
  Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

  (* [rz] is NOT a new Section variable: writing it inline as (rseq_z (kb_rseq kb)) adds no
     binder, so no positional application of this Section's own exports shifts.  AsanPlanSound
     declares rz at :102, immediately after LIMIT (:98) and before HS (:108), so rz goes
     immediately after LIMIT at every site below, exactly as kb goes immediately after xfn. *)
  Theorem both_node_x_sound_all : forall x, x_stmt BSEGS BOTH nx0 AsanInit.LIMIT (rseq_z (kb_rseq kb)) SINV (argH0 sp rdraw argv envp xfn kb) FS0 x.
  Proof.
    pose proof (argH0_high apc sp rdraw argv envp Hsp Hva xfn kb) as AH.
    assert (AA : forall E E' (a : word), env_agree nx0 E E' -> argH0 sp rdraw argv envp xfn kb E a = argH0 sp rdraw argv envp xfn kb E' a).
    { intros E E' a [Hag Hb]. apply (argH0_agree sp rdraw argv envp xfn kb). split; [|exact Hb]. intros n Hn. apply Hag. lia. }
    intros [ | | | | | | | | | | ].
    - apply (both_node_x_sound_XIMemset nx0 AsanInit.LIMIT (rseq_z (kb_rseq kb)) SINV _ AH AA SINV_frame SINV_agree FS0).
    - apply (both_node_x_sound_XIMemcpy nx0 AsanInit.LIMIT (rseq_z (kb_rseq kb)) SINV _ AH AA SINV_frame SINV_agree FS0).
    - apply (both_node_x_sound_XMemset nx0 AsanInit.LIMIT (rseq_z (kb_rseq kb)) SINV _ AH AA SINV_frame SINV_agree FS0).
    - apply (both_node_x_sound_XMemcpy nx0 AsanInit.LIMIT (rseq_z (kb_rseq kb)) SINV _ AH AA SINV_frame SINV_agree FS0).
    - apply (both_node_x_sound_XMemIsZero nx0 AsanInit.LIMIT (rseq_z (kb_rseq kb)) SINV _ AH AA SINV_frame SINV_agree FS0).
    (* the two arms take different hypothesis sets: Rocq abstracts only the Section variables a proof uses,
       and AsanNodesStartXBoth.v closes both theorems with the same solve, of which different arms fire.
       XEnvScan abstracts over Hlaunch and Hlau, XPnScan over Hlau alone, so each theorem's argument list is
       its own. *)
    - apply (node_x_sound_XEnvScan_asan_gen apc sp rdraw brk0 mbase argv envp stdin FS0 uid gid hw groups net nof sigm abt ifs urnd tmp xfn kb sgd Hsp Hva Hve Hfit Hlaunch Hlau SINV SINV_SINV0 SINV_frame nx0 Hnx0).
    - apply (node_x_sound_XPnScan_asan_gen apc sp rdraw brk0 mbase argv envp stdin FS0 uid gid hw groups net nof sigm abt ifs urnd tmp xfn kb sgd Hsp Hva Hve Hfit Hlau SINV SINV_SINV0 SINV_frame nx0 Hnx0 SINV_agree).
    - apply x_sound_layout.
    - apply (both_node_x_sound_XIStrncpy nx0 AsanInit.LIMIT (rseq_z (kb_rseq kb)) SINV _ AH AA SINV_frame SINV_agree FS0).
    - apply (both_node_x_sound_XPopFree nx0 AsanInit.LIMIT (rseq_z (kb_rseq kb)) SINV _ AH AA SINV_frame SINV_agree FS0).
    - apply (x_sound_maxva BSEGS BOTH nx0 AsanInit.LIMIT (rseq_z (kb_rseq kb)) SINV _ FS0 both_wx both_in_hull both_hull_ok SINV_frame both_maxva_range both_maxva_code).
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
  (* see the note in the node Section: kb sits immediately after xfn in every AsanInit export *)
  Variable kb : KernelBuild.
  (* the launch's SIGPIPE disposition (in_sigpipe_default), which Run.valid_input leaves free *)
  Variable sgd : bool.
  Hypothesis Hfs : fs = fs_seed_tmp ifs tmp.
  Hypothesis Hapc : Z.of_N apc = a_entry BOTH.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk BSEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.
  Hypothesis Hlaunch : valid_launch (AsanInit.inp argv envp stdin uid gid hw groups net nof sigm abt ifs urnd tmp xfn kb sgd).
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw)
                      (AsanInit.inp argv envp stdin uid gid hw groups net nof sigm abt ifs urnd tmp xfn kb sgd).

  #[local] Notation SINV := (SINV0 BPH apc sp rdraw brk0 mbase argv envp stdin uid gid hw groups net nof sigm abt ifs urnd tmp xfn kb sgd).
  #[local] Notation argH := (argH0 sp rdraw argv envp xfn kb).
  #[local] Notation E0a := (AsanInit.E0 sp rdraw brk0 argv envp uid gid hw xfn kb).
  #[local] Notation LIM := AsanInit.LIMIT.

  (* [comment removed for export] *)
  Variable IT0 : itab.
  Hypothesis IT0_ok : itab_sound BSEGS IT0.
  (* [comment removed for export] *)
  Variable HS_both : nat -> option acs.     (* [comment removed for export] *)
  Variable startup_plan : plan.
  Variable startup_shape : shape.
  Variables KC0 BFUEL FUEL : nat.
  (* AsanPlan's Section WithSegs declares rz between LIMIT and Section Check, so the discharged check takes
     segs IT A nx0 LIMIT rz XN XE XB HS KC bfuel fuel lc cs p. rz is the run's own flag, rseq_z (kb_rseq kb),
     as check_sound below takes it, never a literal. *)
  Hypothesis startup_cert :
    check BSEGS IT0 BOTH NX0 LIM (rseq_z (kb_rseq kb)) (XNS BSEGS BOTH NX0 LIM) XE0 XB0 HS_both KC0 BFUEL FUEL None (both_init (rseq_z (kb_rseq kb))) startup_plan = COk startup_shape.

  (* [comment removed for export] *)
  Variable HOLES : nat -> env -> Fs.Fs -> TSet.
  Hypothesis HOLES_agree : forall h E E' fs', env_agree NX0 E E' -> HOLES h E fs' = HOLES h E' fs'.
  Hypothesis HOLES_nil : forall h E fs', HOLES h E fs' [].
  Hypothesis HOLES_sound : holes_stmt BSEGS BOTH LIM HS_both SINV argH HOLES fs.

  (* [comment removed for export] *)
  Let AH := argH0_high apc sp rdraw argv envp Hsp Hva xfn kb.
  Let AH2 := argH0_high2 BPH apc sp rdraw brk0 mbase argv envp stdin uid gid hw groups net Hsp Hva Hve Hfit nof sigm abt ifs urnd tmp xfn kb sgd Hlau.
  Let AA := argH0_agree sp rdraw argv envp xfn kb.
  Let SF := SINV0_frame BPH apc sp rdraw brk0 mbase argv envp stdin uid gid hw groups net nof sigm abt ifs urnd tmp xfn kb sgd.
  Let SA := SINV0_agree BPH apc sp rdraw brk0 mbase argv envp stdin uid gid hw groups net nof sigm abt ifs urnd tmp xfn kb sgd.

  Theorem both_startup :
    srealizes BSEGS (init_config BSEGS apc BPH sp brk0 mbase rdraw LIM
                                 (AsanInit.inp argv envp stdin uid gid hw groups net nof sigm abt ifs urnd tmp xfn kb sgd))
              (sd HOLES t_nil E0a fs startup_shape).
  Proof.
    pose proof both_img_facts as IMG.
    rewrite (init_cfg_eq BSEGS BOTH BPH apc sp rdraw brk0 mbase argv envp stdin uid gid hw groups net Hapc nof sigm abt ifs urnd tmp xfn kb sgd).
    pose proof (init_cs_ok BSEGS BOTH BPH apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net IMG Hapc Hsp Hbrk Hmb Hva Hve Hfit Huid Hhw nof sigm abt ifs urnd tmp Hfs xfn kb sgd Hlaunch Hlau) as HC.
    pose proof (check_sound BSEGS IT0 IT0_ok BOTH NX0 (le_n NX0) LIM (rseq_z (kb_rseq kb)) HS_both (XNS BSEGS BOTH NX0 LIM) XE0 XB0
              both_wx both_in_hull both_hull_ok both_shadow_ok SINV argH AH AA SF SA
              HOLES HOLES_agree HOLES_nil fs KC0
              (AsanNodesMmB.node_sys_sound BSEGS BOTH NX0 LIM SINV argH fs both_res_len both_hull_ok both_shadow_ok AH2 AA SF SA)
              (AsanNodesMmB.node_brk2_sound BSEGS BOTH NX0 LIM SINV argH fs both_in_hull both_res_len both_hull_ok both_shadow_ok AH AH2 SF)
              (node_mmap2_sound_OBL BSEGS BOTH NX0 LIM SINV argH fs both_in_hull both_res_len both_res_hull both_hull_ok both_shadow_ok both_hull_cov AH AH2 AA SF SA)
              (node_mmapin_sound_OBL BSEGS BOTH NX0 LIM SINV argH fs both_in_hull both_res_len both_res_hull both_hull_ok both_shadow_ok both_hull_cov AH AH2 AA SF SA)
              (node_mprotect2_sound_OBL BSEGS BOTH NX0 LIM SINV argH fs both_in_hull both_res_len both_res_hull both_hull_ok both_shadow_ok both_hull_cov AH AH2 AA SF SA)
              (AsanNodesMmB.node_exit_sound BSEGS BOTH LIM SINV argH fs)
              (* both_node_x_sound_all now abstracts over Section XAll's two new hypotheses,
                 in the same slot: Rocq abstracts the variables a proof USES, and the arms
                 above use both.  Section Startup already declares them at :181-183. *)
              (both_node_x_sound_all apc sp rdraw brk0 mbase argv envp stdin fs uid gid hw groups net nof sigm abt ifs urnd tmp xfn kb sgd Hsp Hva Hve Hfit Hlaunch Hlau SINV (fun E M H => H) SF NX0 (le_n NX0) SA)
              (node_join_sound BSEGS BOTH NX0 LIM SINV argH fs)
              (XNS_sound BSEGS BOTH NX0 LIM SINV argH fs AA SA both_in_hull both_hull_ok both_shadow_ok AH AH2) (XE0_sound _ _ _ _ _ _ _) (XB0_sound _ _ _ _ _ _ _)
              HOLES_sound FUEL BFUEL None startup_plan (both_init (rseq_z (kb_rseq kb))) startup_shape startup_cert
              _ _ _ _ t_nil HC I eq_refl) as R.
    (* [comment removed for export] *)
    assert (EF : m_fs (model0 BSEGS sp rdraw brk0 mbase argv envp stdin uid gid hw groups net nof sigm abt ifs urnd tmp xfn kb sgd) = fs) by (rewrite Hfs; reflexivity).
    rewrite EF in R. exact R.
  Qed.
End Startup.
End BothStartup.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require StartupPlanBoth.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require StartupHSBoth.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require BothStartupCertDefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require PlanRegen.
From Ltac2 Require Ltac2.
From Ltac2 Require Constr.
From Ltac2 Require Std.
From Ltac2 Require Control.
Module BothStartupCert.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AxSymExec3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanCore OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanSound OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.BothPlanImages OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanInit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanNodesWJoin BothStartup OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.StartupPlanBoth OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.StartupHSBoth OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.BothStartupCertDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition IT0 : itab := mk_itab_ranges BSEGS [(0x30cd0, 24%nat); (0x37a80, 16%nat); (0x37b30, 12%nat); (0x38030, 36%nat); (0x38100, 12%nat); (0x3d900, 884%nat); (0x3e700, 20%nat); (0x3e790, 36%nat); (0x3e840, 8%nat); (0x53150, 12%nat); (0x53840, 20%nat); (0x53900, 28%nat); (0x53b30, 24%nat); (0x53c60, 28%nat); (0x5a5a0, 16%nat); (0x5ad40, 32%nat); (0x5b200, 44%nat); (0x5b720, 36%nat); (0x5bd40, 112%nat); (0x60070, 80%nat); (0x61870, 12%nat); (0x61f10, 36%nat); (0x621d0, 44%nat); (0x63190, 88%nat); (0x63620, 1208%nat); (0x64da0, 32%nat); (0x64e30, 28%nat); (0x64f20, 48%nat); (0x64ff0, 24%nat); (0x650b0, 24%nat); (0x65190, 16%nat); (0x651f0, 68%nat); (0x65470, 48%nat); (0x657b0, 16%nat); (0x65830, 8%nat); (0x659a0, 24%nat); (0x65bf0, 16%nat); (0x65c60, 36%nat); (0x66030, 16%nat); (0x66310, 28%nat); (0x66e60, 68%nat); (0x66f80, 8%nat); (0x67710, 68%nat); (0x68400, 24%nat); (0x68550, 16%nat); (0x6efc0, 8%nat); (0x7be10, 272%nat); (0x7ecd0, 12%nat); (0x81d50, 108%nat); (0x825d0, 8%nat); (0x8cd40, 32%nat); (0x8cde0, 28%nat); (0x8cf40, 96%nat); (0x8d180, 68%nat); (0x8d360, 100%nat); (0x8d510, 97%nat); (0x9cfe4, 12%nat)]%Z.
Lemma IT0_ok : itab_sound BSEGS IT0.
Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition startup_shape : shape := SHole 10.
Import Ltac2.Ltac2 Ltac2.Constr Ltac2.Std Ltac2.Control.
Ltac2 vm_cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).
(* check takes the rseq flag rz after LIMIT (AsanPlan.v), and both_init takes it too (both_init rz :=
   init_acs_of rz BOTH). The certificate is quantified over the flag: intros [|] splits on the bool before any
   reduction, leaving two closed goals vm_cert_refl discharges one at a time, and the consumer takes it as
   startup_cert (kb_rseq kb). The shape is the same at both values. *)
(* LPS 727298f3 gives the launch two more variables (V_G and V_GID: NX0 11 -> 13) and a longer auxv walk, so
   the run numbers its fresh variables differently. The recorded plan is renumbered where it is checked: old
   78 is new 82 in this build too, so every old variable from 13 up (the first fresh variable; V_G 11 and
   V_GID 12 are launch variables and keep their numbers) moves by 4. The hand-off state at 10 is computed
   here, per rz, by the plan's own run (collect_handoffs), and the certificate re-checks the plan against it. *)
Definition T_S1 : list (nat * nat) := [(13%nat, 4%nat)].
Definition startup_plan_k : plan := PlanRegen.psh (PlanRegen.tshift T_S1) startup_plan_both.
Definition run_S1 (b : bool) (js : nat -> option acs) : cres :=
  check BSEGS IT0 BOTH NX0 AsanInit.LIMIT (rseq_z b) (XNS BSEGS BOTH NX0 AsanInit.LIMIT) XE0 XB0 js KC0 BFUEL FUEL None
        (both_init (rseq_z b)) startup_plan_k.
Definition HSL_S1_0 : list (nat * acs) := Eval vm_compute in PlanRegen.collect_handoffs 16 (run_S1 false) [].
Definition HSL_S1_1 : list (nat * acs) := Eval vm_compute in PlanRegen.collect_handoffs 16 (run_S1 true) [].
Definition HSA_10 (b : bool) : acs := PlanRegen.hstate (if b then HSL_S1_1 else HSL_S1_0) (both_init (rseq_z b)) 10.
Definition HSA (b : bool) (h : nat) : option acs := if Nat.eqb h 10 then Some (HSA_10 b) else None.
(* The statement quantifies over the rseq flag (never pinned); `intros [|]` leaves two closed goals. *)
Lemma startup_cert : forall b : bool,
  check BSEGS IT0 BOTH NX0 AsanInit.LIMIT (rseq_z b) (XNS BSEGS BOTH NX0 AsanInit.LIMIT) XE0 XB0 (HSA b) KC0 BFUEL FUEL None (both_init (rseq_z b)) startup_plan_k = COk startup_shape.
Proof.
  intros [|].
  (vm_cert_refl constr:(COk startup_shape)).
  (vm_cert_refl constr:(COk startup_shape)).
Qed.
End BothStartupCert.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require StartupPlan2Both.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require StartupHS2Both.
Module BothStartupCert2.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AxSymExec3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanCore OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanPlanSound OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.BothPlanImages OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanInit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanNodesWJoin BothStartup OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.StartupPlanBoth OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.StartupHSBoth OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.BothStartupCertDefs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.StartupPlan2Both OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.StartupHS2Both.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition IT2 : itab := mk_itab_ranges BSEGS startup2_plan_both_ranges.
Lemma IT2_ok : itab_sound BSEGS IT2.
Proof. apply APS.mk_itab_ranges_sound. Qed.
(* LPS 727298f3: startup2_cert starts from the hand-off 0 that segment D computes, so it lives in
   BothBoot.v after segment D; IT2 stays here. *)
End BothStartupCert2.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound BothPlanImages AsanInit AsanNodesWJoin.
Import BothStartup.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require Import StartupPlanBoth StartupHSBoth BothStartupCertDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ITB : itab := mk_itab_ranges BSEGS [(0x30e10, 24%nat); (0x30fc0, 88%nat); (0x331e0, 16%nat); (0x33230, 12%nat); (0x33300, 12%nat); (0x33410, 12%nat); (0x33450, 36%nat); (0x33570, 52%nat); (0x336b0, 16%nat); (0x33700, 28%nat); (0x337b0, 24%nat); (0x343f0, 24%nat); (0x344e0, 16%nat); (0x41860, 20%nat); (0x42560, 4%nat); (0x48410, 36%nat); (0x494b0, 12%nat); (0x494f0, 40%nat); (0x53070, 64%nat); (0x53840, 28%nat); (0x538d0, 20%nat); (0x539e0, 8%nat); (0x53a20, 16%nat); (0x54160, 12%nat); (0x54bf0, 8%nat); (0x556a0, 44%nat); (0x55800, 12%nat); (0x558d0, 36%nat); (0x55a00, 20%nat); (0x55b90, 36%nat); (0x56020, 80%nat); (0x56180, 24%nat); (0x56780, 24%nat); (0x56800, 12%nat); (0x56840, 16%nat); (0x5b360, 48%nat); (0x5b4b0, 20%nat); (0x5b990, 8%nat); (0x5bf20, 44%nat); (0x5c1b0, 20%nat); (0x5ce80, 20%nat); (0x5d720, 8%nat); (0x5d8a0, 56%nat); (0x5d990, 44%nat); (0x5dcb0, 16%nat); (0x5e160, 16%nat); (0x5e1b0, 16%nat); (0x5e550, 24%nat); (0x5e690, 28%nat); (0x5e7a0, 32%nat); (0x5f8a0, 44%nat); (0x5f9b0, 84%nat); (0x60080, 76%nat); (0x60250, 12%nat); (0x61f10, 20%nat); (0x657b0, 8%nat); (0x65d80, 8%nat); (0x66030, 20%nat); (0x66f80, 8%nat); (0x67290, 32%nat); (0x674c0, 8%nat); (0x67710, 68%nat); (0x678a0, 32%nat); (0x67d60, 72%nat); (0x68400, 24%nat); (0x68550, 16%nat); (0x6b310, 16%nat); (0x6b360, 16%nat); (0x6b3e0, 80%nat); (0x6b5b0, 40%nat); (0x6b6d0, 24%nat); (0x6b980, 92%nat); (0x6bb50, 8%nat); (0x6bb90, 68%nat); (0x6bcb0, 64%nat); (0x6be40, 16%nat); (0x6ca90, 52%nat); (0x6d340, 12%nat); (0x6d380, 12%nat); (0x6dc60, 40%nat); (0x6e450, 36%nat); (0x6e6c0, 8%nat); (0x6e6f0, 12%nat); (0x6e730, 24%nat); (0x6e840, 24%nat); (0x6ecf0, 8%nat); (0x6efc0, 120%nat); (0x6f510, 12%nat); (0x6f560, 12%nat); (0x6f600, 8%nat); (0x6f790, 44%nat); (0x6f890, 12%nat); (0x6fea0, 16%nat); (0x6fef0, 28%nat); (0x700f0, 12%nat); (0x718e0, 28%nat); (0x8cd40, 32%nat); (0x8cde0, 28%nat); (0x8cf40, 12%nat); (0x8d874, 56%nat); (0x8dd14, 88%nat); (0x8de84, 20%nat); (0x9ad64, 8%nat); (0x9b294, 8%nat); (0x9b484, 8%nat); (0x9b514, 12%nat); (0x9b5b4, 16%nat); (0x9c664, 16%nat); (0x9ca14, 60%nat); (0x9cd84, 32%nat); (0x9ce24, 24%nat); (0x9cf24, 28%nat); (0x9cfa4, 20%nat)]%Z.
Lemma ITB_ok : itab_sound BSEGS ITB.
Proof. apply APS.mk_itab_ranges_sound. Qed.
(* LPS 727298f3: startup_certB starts from the hand-off 13 that segment B1 computes, so it lives in
   BothBoot.v (Module BothStartupCertSB) after segment B1; ITB stays here. *)
