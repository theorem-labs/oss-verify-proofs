(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the asan+ubsan image's instances of the start-up scan nodes take the run's whole launch input and its launch hypotheses in place of argv, envp, uid and hw, and the run's CONFIG_RSEQ flag as the plan's rz. *)
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
From OSSVerify.simdjson.fuzz_parser.images Require Import AsanUbsan.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib
  AsanAcct AsanAcctShape AsanAcctImages.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit BothPlanImages.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AsanNodesAux AsanStartLoops AsanNodesStartX AsanNodesStartXInit Both_code_startx.
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
  #[local] Notation SINV0a := (SINV0 BPH AsanUbsan.M.init_pc sp rdraw brk0 mbase inp).
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

    Theorem node_x_sound_XEnvScan_asan_gen : x_stmt BSEGS BOTH nx0 LIMIT RZ SINV argH0a FS0 XEnvScan.
    Proof.
      eapply (init_x_sound_envscan BSEGS BOTH BPH both_wx both_in_hull both_hull_ok
                W_f9a28 W_f9a2c W_f9a30
                ltac:(cbn [x_envscan x_envscan_k BOTH]; lia)
                (fetch_lit _ _ _ _ eq_refl F_f9a28) (fetch_lit _ _ _ _ eq_refl F_f9a2c) (fetch_lit _ _ _ _ eq_refl F_f9a30)
                ltac:(repeat split; reflexivity)
                D_f9a28 D_f9a2c D_f9a30
                _ sp rdraw brk0 mbase inp FS0); solve [eassumption].
    Qed.

    Theorem node_x_sound_XPnScan_asan_gen : x_stmt BSEGS BOTH nx0 LIMIT RZ SINV argH0a FS0 XPnScan.
    Proof.
      eapply (init_x_sound_pnscan BSEGS BOTH BPH both_wx both_in_hull both_hull_ok
                W_f9ae4 W_f9ae8 W_f9aec W_f9af0 W_f9af4
                ltac:(cbn [x_pnscan x_pnscan_k BOTH]; lia)
                (fetch_lit _ _ _ _ eq_refl F_f9ae4) (fetch_lit _ _ _ _ eq_refl F_f9ae8) (fetch_lit _ _ _ _ eq_refl F_f9aec)
                (fetch_lit _ _ _ _ eq_refl F_f9af0) (fetch_lit _ _ _ _ eq_refl F_f9af4)
                ltac:(repeat split; reflexivity)
                D_f9ae4 D_f9ae8 D_f9aec D_f9af0 D_f9af4
                _ sp rdraw brk0 mbase inp FS0); solve [eassumption].
    Qed.

    Theorem node_x_sound_XLayout_asan_gen : x_stmt BSEGS BOTH nx0 LIMIT RZ SINV argH0a FS0 XLayout.
    Proof. apply x_sound_layout. Qed.
  End AnySINV.

  (* [comment removed for export] *)
  Theorem node_x_sound_XEnvScan_asan :
    x_stmt BSEGS BOTH NX0 LIMIT RZ SINV0a argH0a FS0 XEnvScan.
  Proof. apply node_x_sound_XEnvScan_asan_gen with (nx0 := NX0); first [exact (fun E M H => H) | apply SINV0_frame | apply le_n | apply SINV0_agree]. Qed.

  Theorem node_x_sound_XPnScan_asan :
    x_stmt BSEGS BOTH NX0 LIMIT RZ SINV0a argH0a FS0 XPnScan.
  Proof. apply node_x_sound_XPnScan_asan_gen with (nx0 := NX0); first [exact (fun E M H => H) | apply SINV0_frame | apply le_n | apply SINV0_agree]. Qed.

  Theorem node_x_sound_XLayout_asan :
    x_stmt BSEGS BOTH NX0 LIMIT RZ SINV0a argH0a FS0 XLayout.
  Proof. apply x_sound_layout. Qed.
End AsanInstance.
