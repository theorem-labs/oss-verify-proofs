(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.simdjson.fuzz_utf8.images Require Import Plain.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec ShapeAlg SpinAlg AgentLib. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import Spec. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import AsanAcct AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2 AsanInit. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import AsanNodesArg AsanMainLib ImgParams MainDefs MainTree MainAsm MallocSpec AsanNodesRP MallocNodes2 SlotProp. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import AsanNodesMmLib. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import Img_src13 Sums_src13 StartX_src13 ArgClose_src13 MallocClose_src13.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

(* [comment removed for export] *)

Lemma LIM_ok_src13 : LIMIT_MIN <= LIMIT_src13.
Proof. unfold LIMIT_MIN, LIMIT_src13, source_alloc_limit, target_alloc_limit. lia. Qed.

Section Main.
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
  Variable nofile sigmask : word.   (* [comment removed for export] *)
  Variable abt : bool.   (* [comment removed for export] *)
  Variable urnd : InputStream.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk SEGS_src13 brk0.
  (* [comment removed for export] *)
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.

  (* [comment removed for export] *)
  Lemma HULL_tight_src13 : AsanNodesMmLib.hull_tight_b (segments_reserved SEGS_src13) (img_lo AT_src13) (img_hi AT_src13) = true
                           /\ img_lo AT_src13 < img_hi AT_src13.
  Proof. split; [vm_compute; reflexivity | vm_compute; reflexivity]. Qed.
  (* [comment removed for export] *)
  Variable CC : certs IP_src13.

  (* [comment removed for export] *)
  Lemma src13_MX : forall SINV : env -> (word -> option byte) -> Prop,
    (forall E M, SINV E M -> SINV0 PH_src13 sp rdraw brk0 argv envp uid hw E M) ->
    (forall E M M', (forall a, argH0 PH_src13 sp rdraw argv envp uid hw E a = true -> M' a = M a) -> SINV E M -> SINV E M') ->
    (forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M) ->
    forall (fy : FPState) x, x_stmt (fx:=fy) SEGS_src13 AT_src13 NX0 LIMIT_src13 SINV (argH0 PH_src13 sp rdraw argv envp uid hw) fs x.
  Proof.
    intros SINV S0 SF SA.
    pose proof (argH0_high PH_src13 sp rdraw argv envp uid hw Hsp Hva) as AHh. pose proof (argH0_agree PH_src13 sp rdraw argv envp uid hw) as AAg.
    pose proof APC_NX0_min as NXm.   (* [comment removed for export] *)
    intros fy [ | | | | | | | | | | ].
    - eapply src13_x_sound_XIMemset; eauto.
    - eapply src13_x_sound_XIMemcpy; eauto.
    - eapply src13_x_sound_XMemset; eauto.
    - eapply src13_x_sound_XMemcpy; eauto.
    - eapply src13_x_sound_XMemIsZero; eauto.
    - eapply src13_x_sound_XEnvScan; eauto.
    - eapply src13_x_sound_XPnScan; eauto.
    - eapply src13_x_sound_XLayout; eauto.
    - eapply src13_x_sound_XIStrncpy; eauto.
    - eapply src13_x_sound_XPopFree; eauto.
    - eapply src13_x_sound_XSniff; eauto.
  Qed.

  (* [comment removed for export] *)
  Lemma src13_MXW : forall SINV : env -> (word -> option byte) -> Prop,
    (forall E M, SINV E M -> SINV0 PH_src13 sp rdraw brk0 argv envp uid hw E M) ->
    (forall E M M', (forall a, argH0 PH_src13 sp rdraw argv envp uid hw E a = true -> M' a = M a) -> SINV E M -> SINV E M') ->
    (forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M) ->
    forall (fy : FPState) x args cs ws, AP.x_ws_std x args cs = Some ws ->
      node1_stmtW_at (fx:=fy) SEGS_src13 AT_src13 NX0 LIMIT_src13 SINV (argH0 PH_src13 sp rdraw argv envp uid hw) fs always (node_x SEGS_src13 AT_src13 NX0 x args) cs ws.
  Proof.
    intros SINV S0 SF SA.
    pose proof (argH0_high PH_src13 sp rdraw argv envp uid hw Hsp Hva) as AHh. pose proof (argH0_agree PH_src13 sp rdraw argv envp uid hw) as AAg.
    pose proof APC_NX0_min as NXm.   (* [comment removed for export] *)
    intros fy. eapply src13_xW_sound; eauto.
  Qed.

  (* [comment removed for export] *)
  Lemma src13_MRP : RPN.rp_entry (ip_RP IP_src13) <> 0 ->
    forall SINV : env -> (word -> option byte) -> Prop,
    (forall E M, SINV E M -> SINV0 PH_src13 sp rdraw brk0 argv envp uid hw E M) ->
    (forall E M M', (forall a, argH0 PH_src13 sp rdraw argv envp uid hw E a = true -> M' a = M a) -> SINV E M -> SINV E M') ->
    (forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M) ->
    forall (fy : FPState), ext_stmt (fx:=fy) SEGS_src13 AT_src13 NX0 LIMIT_src13 (RPN.xn SEGS_src13 NX0 (ip_RP IP_src13)) SINV (argH0 PH_src13 sp rdraw argv envp uid hw) fs.
  Proof.
    intros H. exfalso. apply H. reflexivity.
  Qed.

  Theorem realizes_spec_src13 :
    srealizes SEGS_src13 (init_config SEGS_src13 Plain.M.init_pc PH_src13 sp brk0 mbase rdraw LIMIT_src13
                                      (AsanInit.inp argv envp fs stdin uid gid hw groups net nofile sigmask abt urnd))
              (spec argv fs).
  Proof.
    destruct (arg_hooks_src13 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit) as [MAN MXE].
    exact (realizes_spec IP_src13 PH_src13 src13_wx src13_in_hull src13_res_len src13_res_hull src13_hull_ok src13_shadow_ok
             src13_img_facts LIM_ok_src13
             sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abt urnd Hsp Hbrk Hva Hve Hfit Huid Hhw HULL_tight_src13 src13_segs_wr
             src13_MX MAN MXE (fun fy => enframe_src13 (fx:=fy)) (fun fy => freepro_src13 (fx:=fy)) src13_MRP src13_MXW CC Plain.M.init_pc eq_refl).
  Qed.
End Main.
