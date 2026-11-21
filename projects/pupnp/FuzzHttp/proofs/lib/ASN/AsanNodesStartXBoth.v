(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's input, mmap base and entry draw; the CONFIG_RSEQ value). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.pupnp.FuzzHttp.images Require Import AsanUbsan.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib
  AsanAcct AsanAcctShape AsanAcctImages.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit BothPlanImages.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import AsanNodesAux AsanStartLoops AsanNodesStartX AsanNodesStartXInit Both_code_startx.

Unset Lia Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
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
  Hypothesis HL : launch_ok BSEGS BOTH BPH apc sp rdraw brk0 mbase inp.

  Section AnySINV.

    Variable SINV : env -> (word -> option byte) -> Prop.
    Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0 BPH apc sp rdraw brk0 mbase inp E M.
    Hypothesis SINV_frame : forall E M M', (forall a, argH0 sp rdraw inp E a = true -> M' a = M a) -> SINV E M -> SINV E M'.

    Variable nx0 : nat.
    Hypothesis Hnx0 : (NX0 <= nx0)%nat.
    Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

    Theorem node_x_sound_XEnvScan_asan_gen :
      x_stmt BSEGS BOTH nx0 LIMIT (rseq_z (kb_rseq (in_kernel inp))) SINV (argH0 sp rdraw inp) FS0 XEnvScan.
    Proof.
      exact (init_x_sound_envscan BSEGS BOTH BPH both_wx both_in_hull both_hull_ok
                W_94a40 W_94a44 W_94a48 W_94afc W_94b00 W_94b04 W_94b08 W_94b0c
                ltac:(cbn [x_envscan x_envscan_k BOTH]; lia)
                (fetch_lit _ _ _ _ eq_refl F_94a40) (fetch_lit _ _ _ _ eq_refl F_94a44) (fetch_lit _ _ _ _ eq_refl F_94a48)
                ltac:(repeat split; reflexivity)
                D_94a40 D_94a44 D_94a48
                ltac:(cbn [x_pnscan x_pnscan_k BOTH]; lia)
                (fetch_lit _ _ _ _ eq_refl F_94afc) (fetch_lit _ _ _ _ eq_refl F_94b00) (fetch_lit _ _ _ _ eq_refl F_94b04)
                (fetch_lit _ _ _ _ eq_refl F_94b08) (fetch_lit _ _ _ _ eq_refl F_94b0c)
                ltac:(repeat split; reflexivity)
                D_94afc D_94b00 D_94b04 D_94b08 D_94b0c
                apc sp rdraw brk0 mbase inp FS0 HL SINV SINV_SINV0 SINV_frame nx0 Hnx0 SINV_agree).
    Qed.

    Theorem node_x_sound_XPnScan_asan_gen :
      x_stmt BSEGS BOTH nx0 LIMIT (rseq_z (kb_rseq (in_kernel inp))) SINV (argH0 sp rdraw inp) FS0 XPnScan.
    Proof.
      exact (init_x_sound_pnscan BSEGS BOTH BPH both_wx both_in_hull both_hull_ok
                W_94a40 W_94a44 W_94a48 W_94afc W_94b00 W_94b04 W_94b08 W_94b0c
                ltac:(cbn [x_envscan x_envscan_k BOTH]; lia)
                (fetch_lit _ _ _ _ eq_refl F_94a40) (fetch_lit _ _ _ _ eq_refl F_94a44) (fetch_lit _ _ _ _ eq_refl F_94a48)
                ltac:(repeat split; reflexivity)
                D_94a40 D_94a44 D_94a48
                ltac:(cbn [x_pnscan x_pnscan_k BOTH]; lia)
                (fetch_lit _ _ _ _ eq_refl F_94afc) (fetch_lit _ _ _ _ eq_refl F_94b00) (fetch_lit _ _ _ _ eq_refl F_94b04)
                (fetch_lit _ _ _ _ eq_refl F_94b08) (fetch_lit _ _ _ _ eq_refl F_94b0c)
                ltac:(repeat split; reflexivity)
                D_94afc D_94b00 D_94b04 D_94b08 D_94b0c
                apc sp rdraw brk0 mbase inp FS0 HL SINV SINV_SINV0 SINV_frame nx0 Hnx0 SINV_agree).
    Qed.

    Theorem node_x_sound_XLayout_asan_gen :
      x_stmt BSEGS BOTH nx0 LIMIT (rseq_z (kb_rseq (in_kernel inp))) SINV (argH0 sp rdraw inp) FS0 XLayout.
    Proof. apply x_sound_layout. Qed.
  End AnySINV.
End AsanInstance.
