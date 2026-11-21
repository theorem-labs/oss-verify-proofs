(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: changed Hva, Hve, SINV_SINV0 and 4 more; added Hapc, Hbrk, Hhw and 7 more; removed Hfit, argv, envp and 7 more. *)
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
From OSSVerify.simdjson.fuzz_utf8.images Require Import Asan.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.AS Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib
  AsanAcct AsanAcctShape AsanAcctImages.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.AS Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit AsanPlanImages.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.AS Require Import AsanNodesAux AsanStartLoops AsanNodesStartX AsanNodesStartXInit Asan_code_startx.
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
  Variable inp : ProcInput.
  Variable FS0 : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hapc : Z.of_N apc = a_entry ASAN.
  Hypothesis Hbrk : valid_brk ASEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Huid : valid_id (in_uid inp).
  Hypothesis Hlaunch : valid_launch inp.
  Hypothesis Hrdr : in_channel_reader inp = true.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.
  Hypothesis Hhw : valid_hwcap (in_hwcap inp).

  Section AnySINV.
    (* [comment removed for export] *)
    Variable SINV : env -> (word -> option byte) -> Prop.
    Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0 APH apc sp rdraw brk0 mbase inp E M.
    Hypothesis SINV_frame : forall E M M', (forall a, argH0 sp rdraw inp E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
    (* [comment removed for export] *)
    Variable nx0 : nat.
    Hypothesis Hnx0 : (NX0 <= nx0)%nat.
    Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

    Theorem node_x_sound_XEnvScan_asan_gen :
      x_stmt ASEGS ASAN nx0 LIMIT (rseq_z (kb_rseq (in_kernel inp))) SINV (argH0 sp rdraw inp) FS0 XEnvScan.
    Proof.
      eapply (init_x_sound_envscan ASEGS ASAN APH asan_wx asan_in_hull asan_hull_ok
                W_146024 W_146028 W_14602c
                ltac:(cbn [x_envscan x_envscan_k ASAN]; lia)
                (fetch_lit _ _ _ _ eq_refl F_146024) (fetch_lit _ _ _ _ eq_refl F_146028) (fetch_lit _ _ _ _ eq_refl F_14602c)
                ltac:(repeat split; reflexivity)
                D_146024 D_146028 D_14602c); first [eassumption | exact asan_img_facts].
    Qed.

    Theorem node_x_sound_XPnScan_asan_gen :
      x_stmt ASEGS ASAN nx0 LIMIT (rseq_z (kb_rseq (in_kernel inp))) SINV (argH0 sp rdraw inp) FS0 XPnScan.
    Proof.
      eapply (init_x_sound_pnscan ASEGS ASAN APH asan_wx asan_in_hull asan_hull_ok
                W_1460e0 W_1460e4 W_1460e8 W_1460ec W_1460f0
                ltac:(cbn [x_pnscan x_pnscan_k ASAN]; lia)
                (fetch_lit _ _ _ _ eq_refl F_1460e0) (fetch_lit _ _ _ _ eq_refl F_1460e4) (fetch_lit _ _ _ _ eq_refl F_1460e8)
                (fetch_lit _ _ _ _ eq_refl F_1460ec) (fetch_lit _ _ _ _ eq_refl F_1460f0)
                ltac:(repeat split; reflexivity)
                D_1460e0 D_1460e4 D_1460e8 D_1460ec D_1460f0); first [eassumption | exact asan_img_facts].
    Qed.

    Theorem node_x_sound_XLayout_asan_gen :
      x_stmt ASEGS ASAN nx0 LIMIT (rseq_z (kb_rseq (in_kernel inp))) SINV (argH0 sp rdraw inp) FS0 XLayout.
    Proof. apply x_sound_layout. Qed.
  End AnySINV.
End AsanInstance.
