(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the start nodes over the launch input ProcInput, the CONFIG_RSEQ flag and the channel-reader premise). *)
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
From OSSVerify.bzip2.bzip2_compress_target.images Require Import AsanUbsan.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib
  AsanAcct AsanAcctShape AsanAcctImagesB.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import PropExec.  (* [comment removed for export] *)
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit AsanPlanImagesB.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import AsanTablesB.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import AsanNodesAux AsanStartLoops AsanNodesStartX AsanNodesStartXInit Asan_code_startxB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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
  Hypothesis Hapc : Z.of_N apc = a_entry ASAN_B.
  Hypothesis Hbrk : valid_brk ASEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Huid : valid_id (in_uid inp).
  Hypothesis Hlaunch : valid_launch inp.
  Hypothesis Hrdr : in_channel_reader inp = true.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.

  Section AnySINV.
    (* [comment removed for export] *)
    Variable SINV : env -> (word -> option byte) -> Prop.
    Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0 APH apc sp rdraw brk0 mbase inp E M.
    Hypothesis SINV_frame : forall E M M', (forall a, argH0 sp rdraw inp E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
    Hypothesis SINV_agree : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.

    Theorem node_x_sound_XEnvScan_asan_gen :
      x_stmt ASEGS ASAN_B NX0 LIMIT (rseq_z (kb_rseq (in_kernel inp))) SINV (argH0 sp rdraw inp) FS0 XEnvScan.
    Proof.
      eapply (init_x_sound_envscan ASEGS ASAN_B APH asan_wx asan_in_hull asan_hull_ok
                W_bbc10 W_bbc14 W_bbc18
                ltac:(cbn [x_envscan x_envscan_k ASAN_B]; lia)
                (fetch_lit _ _ _ _ eq_refl F_bbc10) (fetch_lit _ _ _ _ eq_refl F_bbc14) (fetch_lit _ _ _ _ eq_refl F_bbc18)
                ltac:(repeat split; reflexivity)
                D_bbc10 D_bbc14 D_bbc18); first [eassumption | exact asan_img_facts].
    Qed.

    Theorem node_x_sound_XPnScan_asan_gen :
      x_stmt ASEGS ASAN_B NX0 LIMIT (rseq_z (kb_rseq (in_kernel inp))) SINV (argH0 sp rdraw inp) FS0 XPnScan.
    Proof.
      eapply (init_x_sound_pnscan ASEGS ASAN_B APH asan_wx asan_in_hull asan_hull_ok
                W_bbccc W_bbcd0 W_bbcd4 W_bbcd8 W_bbcdc
                ltac:(cbn [x_pnscan x_pnscan_k ASAN_B]; lia)
                (fetch_lit _ _ _ _ eq_refl F_bbccc) (fetch_lit _ _ _ _ eq_refl F_bbcd0) (fetch_lit _ _ _ _ eq_refl F_bbcd4)
                (fetch_lit _ _ _ _ eq_refl F_bbcd8) (fetch_lit _ _ _ _ eq_refl F_bbcdc)
                ltac:(repeat split; reflexivity)
                D_bbccc D_bbcd0 D_bbcd4 D_bbcd8 D_bbcdc); first [eassumption | exact asan_img_facts].
    Qed.

    (* [comment removed for export] *)
  End AnySINV.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
End AsanInstance.
