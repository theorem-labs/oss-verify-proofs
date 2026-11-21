(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the asan+ubsan image's instances of the start-up scan nodes take the run's whole launch input and its launch hypotheses, and the run's CONFIG_RSEQ flag as the plan's rz; taken in part from projects/simdjson/fuzz_ondemand/proofs/lib/AS/AsanNodesStartXBoth.v, 34 lines within its lines 18-96. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.simdjson.fuzz_element.images Require Import AsanUbsan.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.AS Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib
  AsanAcct AsanAcctShape AsanAcctImagesB.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.AS Require Import PropExec.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.AS Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit AsanPlanImagesB.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.AS Require Import AsanTablesB.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.AS Require Import AsanNodesAux AsanStartLoops AsanNodesStartX AsanNodesStartXInit Asan_code_startxB.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.AS Require AsanCeil.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

Section AsanInstance.
  (* LPS 727298f3: the run, as AS/AsanNodesStartXInit.v's Section GenericInit (and AS/AsanInit.v's
     Section Init) names it: the run's whole launch input [inp], and every
     launch hypothesis those sections read.  [eassumption] places each where
     the instances need it. *)
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 mbase : word.
  Variable FS0 : Fs.Fs.
  Variable inp : ProcInput.
  #[local] Notation INP := inp.
  #[local] Notation argv := (in_argv inp).
  #[local] Notation envp := (in_envp inp).
  #[local] Notation uid := (in_uid inp).
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk ASEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hzr : AsanCeil.zero_random_draw (ed_random rdraw).
  Hypothesis Hlaunch : valid_launch INP.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.
  (* the launch's CONFIG_RSEQ flag, read off the kernel build: never pinned *)
  #[local] Notation RZ := (rseq_z (kb_rseq (in_kernel INP))).
  #[local] Notation SINV0a := (SINV0 ASAN_B APH sp rdraw brk0 mbase inp).
  #[local] Notation argH0a := (argH0 sp rdraw inp).

  Section AnySINV.

    Variable SINV : env -> (word -> option byte) -> Prop.
    Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0a E M.
    Hypothesis SINV_frame : forall E M M', (forall a, argH0a E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
    Hypothesis SINV_agree : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.

    Theorem node_x_sound_XEnvScan_asan_gen : x_stmt ASEGS ASAN_B NX0 LIMIT RZ SINV argH0a FS0 XEnvScan.
    Proof.
      pose proof asan_img_facts as IMG.
      eapply (init_x_sound_envscan ASEGS ASAN_B APH asan_wx asan_in_hull asan_hull_ok
                W_88d40 W_88d44 W_88d48
                ltac:(cbn [x_envscan x_envscan_k ASAN_B]; lia)
                (fetch_lit _ _ _ _ eq_refl F_88d40) (fetch_lit _ _ _ _ eq_refl F_88d44) (fetch_lit _ _ _ _ eq_refl F_88d48)
                ltac:(repeat split; reflexivity)
                D_88d40 D_88d44 D_88d48); eassumption.
    Qed.

    Theorem node_x_sound_XPnScan_asan_gen : x_stmt ASEGS ASAN_B NX0 LIMIT RZ SINV argH0a FS0 XPnScan.
    Proof.
      pose proof asan_img_facts as IMG.
      eapply (init_x_sound_pnscan ASEGS ASAN_B APH asan_wx asan_in_hull asan_hull_ok
                W_88dfc W_88e00 W_88e04 W_88e08 W_88e0c
                ltac:(cbn [x_pnscan x_pnscan_k ASAN_B]; lia)
                (fetch_lit _ _ _ _ eq_refl F_88dfc) (fetch_lit _ _ _ _ eq_refl F_88e00) (fetch_lit _ _ _ _ eq_refl F_88e04)
                (fetch_lit _ _ _ _ eq_refl F_88e08) (fetch_lit _ _ _ _ eq_refl F_88e0c)
                ltac:(repeat split; reflexivity)
                D_88dfc D_88e00 D_88e04 D_88e08 D_88e0c); eassumption.
    Qed.

    Theorem node_x_sound_XLayout_asan_gen : x_stmt ASEGS ASAN_B NX0 LIMIT RZ SINV argH0a FS0 XLayout.
    Proof. apply x_sound_layout. Qed.
  End AnySINV.

  Theorem node_x_sound_XEnvScan_asan :
    x_stmt ASEGS ASAN_B NX0 LIMIT RZ SINV0a argH0a FS0 XEnvScan.
  Proof. apply node_x_sound_XEnvScan_asan_gen; first [exact (fun E M H => H) | apply SINV0_frame | apply SINV0_agree]. Qed.

  Theorem node_x_sound_XPnScan_asan :
    x_stmt ASEGS ASAN_B NX0 LIMIT RZ SINV0a argH0a FS0 XPnScan.
  Proof. apply node_x_sound_XPnScan_asan_gen; first [exact (fun E M H => H) | apply SINV0_frame | apply SINV0_agree]. Qed.

  Theorem node_x_sound_XLayout_asan :
    x_stmt ASEGS ASAN_B NX0 LIMIT RZ SINV0a argH0a FS0 XLayout.
  Proof. apply x_sound_layout. Qed.
End AsanInstance.
