(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the asan image's instances of the start-up scan nodes take the run's whole launch input and its launch hypotheses in place of argv, envp, uid and hw, and the run's CONFIG_RSEQ flag as the plan's rz. *)
(* [comment removed for export] *)
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
From OSSVerify.simdjson.fuzz_parser.images Require Import Asan.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib
  AsanAcct AsanAcctShape AsanAcctImages.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit AsanPlanImages.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AsanNodesAux AsanStartLoops AsanNodesStartX AsanNodesStartXInit Asan_code_startx.
(* [comment removed for export] *)
Unset Lia Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

Section AsanInstance.
  (* LPS 727298f3: the run's whole launch input, as AS/AsanInit.v's Section Init takes it *)
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
  #[local] Notation RZ := (rseq_z (kb_rseq (in_kernel inp))).
  #[local] Notation SINV0a := (SINV0 APH Asan.M.init_pc sp rdraw brk0 mbase inp).
  #[local] Notation argH0a := (argH0 sp rdraw inp).

  Section AnySINV.
    (* [comment removed for export] *)
    Variable SINV : env -> (word -> option byte) -> Prop.
    Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0a E M.
    Hypothesis SINV_frame : forall E M M', (forall a, argH0a E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
    (* [comment removed for export] *)
    Variable nx0 : nat.
    Hypothesis Hnx0 : (NX0 <= nx0)%nat.
    Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

    Theorem node_x_sound_XEnvScan_asan_gen : x_stmt ASEGS ASAN nx0 LIMIT RZ SINV argH0a FS0 XEnvScan.
    Proof.
      eapply (init_x_sound_envscan ASEGS ASAN APH asan_wx asan_in_hull asan_hull_ok
                W_ee2a8 W_ee2ac W_ee2b0
                ltac:(cbn [x_envscan x_envscan_k ASAN]; lia)
                (fetch_lit _ _ _ _ eq_refl F_ee2a8) (fetch_lit _ _ _ _ eq_refl F_ee2ac) (fetch_lit _ _ _ _ eq_refl F_ee2b0)
                ltac:(repeat split; reflexivity)
                D_ee2a8 D_ee2ac D_ee2b0
                _ sp rdraw brk0 mbase inp FS0); solve [eassumption].
    Qed.

    Theorem node_x_sound_XPnScan_asan_gen : x_stmt ASEGS ASAN nx0 LIMIT RZ SINV argH0a FS0 XPnScan.
    Proof.
      eapply (init_x_sound_pnscan ASEGS ASAN APH asan_wx asan_in_hull asan_hull_ok
                W_ee364 W_ee368 W_ee36c W_ee370 W_ee374
                ltac:(cbn [x_pnscan x_pnscan_k ASAN]; lia)
                (fetch_lit _ _ _ _ eq_refl F_ee364) (fetch_lit _ _ _ _ eq_refl F_ee368) (fetch_lit _ _ _ _ eq_refl F_ee36c)
                (fetch_lit _ _ _ _ eq_refl F_ee370) (fetch_lit _ _ _ _ eq_refl F_ee374)
                ltac:(repeat split; reflexivity)
                D_ee364 D_ee368 D_ee36c D_ee370 D_ee374
                _ sp rdraw brk0 mbase inp FS0); solve [eassumption].
    Qed.

    Theorem node_x_sound_XLayout_asan_gen : x_stmt ASEGS ASAN nx0 LIMIT RZ SINV argH0a FS0 XLayout.
    Proof. apply x_sound_layout. Qed.
  End AnySINV.

  (* [comment removed for export] *)
  Theorem node_x_sound_XEnvScan_asan :
    x_stmt ASEGS ASAN NX0 LIMIT RZ SINV0a argH0a FS0 XEnvScan.
  Proof. apply node_x_sound_XEnvScan_asan_gen with (nx0 := NX0); first [exact (fun E M H => H) | apply SINV0_frame | apply le_n | apply SINV0_agree]. Qed.

  Theorem node_x_sound_XPnScan_asan :
    x_stmt ASEGS ASAN NX0 LIMIT RZ SINV0a argH0a FS0 XPnScan.
  Proof. apply node_x_sound_XPnScan_asan_gen with (nx0 := NX0); first [exact (fun E M H => H) | apply SINV0_frame | apply le_n | apply SINV0_agree]. Qed.

  Theorem node_x_sound_XLayout_asan :
    x_stmt ASEGS ASAN NX0 LIMIT RZ SINV0a argH0a FS0 XLayout.
  Proof. apply x_sound_layout. Qed.
End AsanInstance.
