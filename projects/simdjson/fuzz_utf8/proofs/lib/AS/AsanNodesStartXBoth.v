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

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.simdjson.fuzz_utf8.images Require Import AsanUbsan.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.AS Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib
  AsanAcct AsanAcctShape AsanAcctImages.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.AS Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit BothPlanImages.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.AS Require Import AsanNodesAux AsanStartLoops AsanNodesStartX AsanNodesStartXInit Both_code_startx.
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
  Hypothesis Hapc : Z.of_N apc = a_entry BOTH.
  Hypothesis Hbrk : valid_brk BSEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Huid : valid_id (in_uid inp).
  Hypothesis Hlaunch : valid_launch inp.
  Hypothesis Hrdr : in_channel_reader inp = true.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.
  Hypothesis Hhw : valid_hwcap (in_hwcap inp).

  Section AnySINV.
    (* [comment removed for export] *)
    Variable SINV : env -> (word -> option byte) -> Prop.
    Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0 BPH apc sp rdraw brk0 mbase inp E M.
    Hypothesis SINV_frame : forall E M M', (forall a, argH0 sp rdraw inp E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
    (* [comment removed for export] *)
    Variable nx0 : nat.
    Hypothesis Hnx0 : (NX0 <= nx0)%nat.
    Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

    Theorem node_x_sound_XEnvScan_asan_gen :
      x_stmt BSEGS BOTH nx0 LIMIT (rseq_z (kb_rseq (in_kernel inp))) SINV (argH0 sp rdraw inp) FS0 XEnvScan.
    Proof.
      eapply (init_x_sound_envscan BSEGS BOTH BPH both_wx both_in_hull both_hull_ok
                W_151f5c W_151f60 W_151f64
                ltac:(cbn [x_envscan x_envscan_k BOTH]; lia)
                (fetch_lit _ _ _ _ eq_refl F_151f5c) (fetch_lit _ _ _ _ eq_refl F_151f60) (fetch_lit _ _ _ _ eq_refl F_151f64)
                ltac:(repeat split; reflexivity)
                D_151f5c D_151f60 D_151f64); first [eassumption | exact both_img_facts].
    Qed.

    Theorem node_x_sound_XPnScan_asan_gen :
      x_stmt BSEGS BOTH nx0 LIMIT (rseq_z (kb_rseq (in_kernel inp))) SINV (argH0 sp rdraw inp) FS0 XPnScan.
    Proof.
      eapply (init_x_sound_pnscan BSEGS BOTH BPH both_wx both_in_hull both_hull_ok
                W_152018 W_15201c W_152020 W_152024 W_152028
                ltac:(cbn [x_pnscan x_pnscan_k BOTH]; lia)
                (fetch_lit _ _ _ _ eq_refl F_152018) (fetch_lit _ _ _ _ eq_refl F_15201c) (fetch_lit _ _ _ _ eq_refl F_152020)
                (fetch_lit _ _ _ _ eq_refl F_152024) (fetch_lit _ _ _ _ eq_refl F_152028)
                ltac:(repeat split; reflexivity)
                D_152018 D_15201c D_152020 D_152024 D_152028); first [eassumption | exact both_img_facts].
    Qed.

    Theorem node_x_sound_XLayout_asan_gen :
      x_stmt BSEGS BOTH nx0 LIMIT (rseq_z (kb_rseq (in_kernel inp))) SINV (argH0 sp rdraw inp) FS0 XLayout.
    Proof. apply x_sound_layout. Qed.
  End AnySINV.
End AsanInstance.
