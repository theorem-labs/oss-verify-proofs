(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (section AsanInstance over the launch input, its launch facts and the entry pc apc, with Hfit removed; the FPState instance qualified as K5.AS.PropExec where a twin module shadows it). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.leptonica.pix1_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.AS Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctShape.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.AS22 Require Import AsanAcctImages.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.AS Require Import PropExec.  (* [comment removed for export] *)
Local Instance asanreflect_fx : K5.AS.PropExec.FPState := K5.AS.PropExec.fx0.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.AS Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.AS22 Require Import AsanPlanImages.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.AS22 Require Import AsanTablesA.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.AS Require Import AsanNodesAux AsanStartLoops AsanNodesStartX AsanNodesStartXInit.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.AS22 Require Import Asan_code_startx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

Section AsanInstance.
  Variable apc : N.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 mbase : word.
  Variable inp : ProcInput.
  Variable FS0 : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hlaunch : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.

  Section AnySINV.
    (* [comment removed for export] *)
    Variable SINV : env -> (word -> option byte) -> Prop.
    Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0 APH apc sp rdraw brk0 mbase inp E M.
    Hypothesis SINV_frame : forall E M M', (forall a, argH0 sp rdraw inp E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
    Hypothesis SINV_agree : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.

    Theorem node_x_sound_XEnvScan_asan_gen : x_stmt ASEGS ASAN_A NX0 LIMIT SINV (argH0 sp rdraw inp) FS0 XEnvScan.
    Proof.
      eapply (init_x_sound_envscan ASEGS ASAN_A APH asan_wx asan_in_hull asan_hull_ok
                W_b43f8 W_b43fc W_b4400
                ltac:(cbn [x_envscan x_envscan_k ASAN_A]; lia)
                (fetch_lit _ _ _ _ eq_refl F_b43f8) (fetch_lit _ _ _ _ eq_refl F_b43fc) (fetch_lit _ _ _ _ eq_refl F_b4400)
                ltac:(repeat split; reflexivity)
                D_b43f8 D_b43fc D_b4400); eassumption.
    Qed.

    Theorem node_x_sound_XPnScan_asan_gen : x_stmt ASEGS ASAN_A NX0 LIMIT SINV (argH0 sp rdraw inp) FS0 XPnScan.
    Proof.
      eapply (init_x_sound_pnscan ASEGS ASAN_A APH asan_wx asan_in_hull asan_hull_ok
                W_b44b4 W_b44b8 W_b44bc W_b44c0 W_b44c4
                ltac:(cbn [x_pnscan x_pnscan_k ASAN_A]; lia)
                (fetch_lit _ _ _ _ eq_refl F_b44b4) (fetch_lit _ _ _ _ eq_refl F_b44b8) (fetch_lit _ _ _ _ eq_refl F_b44bc)
                (fetch_lit _ _ _ _ eq_refl F_b44c0) (fetch_lit _ _ _ _ eq_refl F_b44c4)
                ltac:(repeat split; reflexivity)
                D_b44b4 D_b44b8 D_b44bc D_b44c0 D_b44c4); eassumption.
    Qed.

    Theorem node_x_sound_XLayout_asan_gen : x_stmt ASEGS ASAN_A NX0 LIMIT SINV (argH0 sp rdraw inp) FS0 XLayout.
    Proof. apply x_sound_layout. Qed.
  End AnySINV.

  (* [comment removed for export] *)
  Theorem node_x_sound_XEnvScan_asan :
    x_stmt ASEGS ASAN_A NX0 LIMIT (SINV0 APH apc sp rdraw brk0 mbase inp) (argH0 sp rdraw inp) FS0 XEnvScan.
  Proof. apply node_x_sound_XEnvScan_asan_gen; [auto | apply SINV0_frame]. Qed.

  Theorem node_x_sound_XPnScan_asan :
    x_stmt ASEGS ASAN_A NX0 LIMIT (SINV0 APH apc sp rdraw brk0 mbase inp) (argH0 sp rdraw inp) FS0 XPnScan.
  Proof. apply node_x_sound_XPnScan_asan_gen; [auto | apply SINV0_frame | apply SINV0_agree]. Qed.

  Theorem node_x_sound_XLayout_asan :
    x_stmt ASEGS ASAN_A NX0 LIMIT (SINV0 APH apc sp rdraw brk0 mbase inp) (argH0 sp rdraw inp) FS0 XLayout.
  Proof. apply x_sound_layout. Qed.
End AsanInstance.
