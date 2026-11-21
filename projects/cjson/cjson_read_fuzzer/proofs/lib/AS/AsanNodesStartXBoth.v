(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: Section AsanInstance takes the entry address and the launch's whole input (AsanInit.inp with the executable name and kernel build) with the valid_launch and entry_launch_ok_va premises, and states the BOTH build's XEnvScan, XPnScan and XLayout soundness theorems at the run's rseq flag over the new SINV0 and argH0; the launch's SIGPIPE disposition sgd is a Section variable, passed after kb. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.cjson.cjson_read_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require Import PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require SymStepR.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.SymStepR.CatExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require Import CatSim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require SymStepR.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.SymStepR.SeqExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require MemSplit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.MemSplit.StoreOk.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require Import ShapeAlg SpinAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require MemSplit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.MemSplit.AgentLib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require Import AsanAcct AsanAcctShape AsanAcctImages.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit BothPlanImages.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require Import AsanNodesAux AsanStartLoops AsanNodesStartX AsanNodesStartXInit Both_code_startx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Unset Lia Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

Section AsanInstance.
  Variable apc : N.
  Variable sp : word.
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable stdin : InputStream.
  Variable FS0 : Fs.Fs.
  Variable uid gid : word.
  Variable hw : word.   (* [comment removed for export] *)
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nof sigm : word.
  Variable abt : bool.
  Variable ifs : Fs.Fs.
  Variable urnd : InputStream.
  Variable tmp : Fs.Fs.
  Variable xfn : list byte.
  (* AsanInit.v:134 declares kb between xfn (:128) and Hlaunch (:140), so it is the argument
     immediately after xfn at every AsanInit export applied below.  Never instantiated here. *)
  Variable kb : KernelBuild.
  (* the launch's SIGPIPE disposition (in_sigpipe_default), which Run.valid_input leaves free *)
  Variable sgd : bool.
  #[local] Notation INPb :=
    (AsanInit.inp argv envp stdin uid gid hw groups net nof sigm abt ifs urnd tmp xfn kb sgd).
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.   (* [comment removed for export] *)
  Hypothesis Hlaunch : valid_launch INPb.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INPb.

  Section AnySINV.
    (* [comment removed for export] *)
    Variable SINV : env -> (word -> option byte) -> Prop.
    Hypothesis SINV_SINV0 : forall E M, SINV E M ->
      SINV0 BPH apc sp rdraw brk0 mbase argv envp stdin uid gid hw groups net nof sigm abt ifs urnd tmp xfn kb sgd E M.
    Hypothesis SINV_frame : forall E M M', (forall a, argH0 sp rdraw argv envp xfn kb E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
    (* [comment removed for export] *)
    Variable nx0 : nat.
    Hypothesis Hnx0 : (NX0 <= nx0)%nat.
    Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

    Theorem node_x_sound_XEnvScan_asan_gen : x_stmt BSEGS BOTH nx0 LIMIT (rseq_z (kb_rseq kb)) SINV (argH0 sp rdraw argv envp xfn kb) FS0 XEnvScan.
    Proof.
      eapply (init_x_sound_envscan BSEGS BOTH BPH both_wx both_in_hull both_hull_ok
                W_8cfb4 W_8cfb8 W_8cfbc
                ltac:(cbn [x_envscan x_envscan_k BOTH]; lia)
                (fetch_lit _ _ _ _ eq_refl F_8cfb4) (fetch_lit _ _ _ _ eq_refl F_8cfb8) (fetch_lit _ _ _ _ eq_refl F_8cfbc)
                ltac:(repeat split; reflexivity)
                D_8cfb4 D_8cfb8 D_8cfbc);
        solve [ exact Hsp | exact Hva | exact Hve | exact Hfit | exact Hlaunch | exact Hlau
              | exact SINV_SINV0 | exact SINV_frame | exact Hnx0 | exact SINV_agree | assumption ].
    Qed.

    Theorem node_x_sound_XPnScan_asan_gen : x_stmt BSEGS BOTH nx0 LIMIT (rseq_z (kb_rseq kb)) SINV (argH0 sp rdraw argv envp xfn kb) FS0 XPnScan.
    Proof.
      eapply (init_x_sound_pnscan BSEGS BOTH BPH both_wx both_in_hull both_hull_ok
                W_8d070 W_8d074 W_8d078 W_8d07c W_8d080
                ltac:(cbn [x_pnscan x_pnscan_k BOTH]; lia)
                (fetch_lit _ _ _ _ eq_refl F_8d070) (fetch_lit _ _ _ _ eq_refl F_8d074) (fetch_lit _ _ _ _ eq_refl F_8d078)
                (fetch_lit _ _ _ _ eq_refl F_8d07c) (fetch_lit _ _ _ _ eq_refl F_8d080)
                ltac:(repeat split; reflexivity)
                D_8d070 D_8d074 D_8d078 D_8d07c D_8d080);
        solve [ exact Hsp | exact Hva | exact Hve | exact Hfit | exact Hlaunch | exact Hlau
              | exact SINV_SINV0 | exact SINV_frame | exact Hnx0 | exact SINV_agree | assumption ].
    Qed.

    Theorem node_x_sound_XLayout_asan_gen : x_stmt BSEGS BOTH nx0 LIMIT (rseq_z (kb_rseq kb)) SINV (argH0 sp rdraw argv envp xfn kb) FS0 XLayout.
    Proof. apply x_sound_layout. Qed.
  End AnySINV.

  (* [comment removed for export] *)
  Theorem node_x_sound_XEnvScan_asan :
    x_stmt BSEGS BOTH NX0 LIMIT (rseq_z (kb_rseq kb)) (SINV0 BPH apc sp rdraw brk0 mbase argv envp stdin uid gid hw groups net nof sigm abt ifs urnd tmp xfn kb sgd) (argH0 sp rdraw argv envp xfn kb) FS0 XEnvScan.
  Proof. apply node_x_sound_XEnvScan_asan_gen; [auto | apply SINV0_frame | apply le_n]. Qed.

  Theorem node_x_sound_XPnScan_asan :
    x_stmt BSEGS BOTH NX0 LIMIT (rseq_z (kb_rseq kb)) (SINV0 BPH apc sp rdraw brk0 mbase argv envp stdin uid gid hw groups net nof sigm abt ifs urnd tmp xfn kb sgd) (argH0 sp rdraw argv envp xfn kb) FS0 XPnScan.
  Proof. apply (node_x_sound_XPnScan_asan_gen _ (fun E M H => H) (SINV0_frame BPH apc sp rdraw brk0 mbase argv envp stdin uid gid hw groups net nof sigm abt ifs urnd tmp xfn kb sgd) NX0 (le_n NX0) (SINV0_agree BPH apc sp rdraw brk0 mbase argv envp stdin uid gid hw groups net nof sigm abt ifs urnd tmp xfn kb sgd)). Qed.

  Theorem node_x_sound_XLayout_asan :
    x_stmt BSEGS BOTH NX0 LIMIT (rseq_z (kb_rseq kb)) (SINV0 BPH apc sp rdraw brk0 mbase argv envp stdin uid gid hw groups net nof sigm abt ifs urnd tmp xfn kb sgd) (argH0 sp rdraw argv envp xfn kb) FS0 XLayout.
  Proof. apply x_sound_layout. Qed.
End AsanInstance.
