(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Mem Cells Frame RunConst.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.AS Require Import MainExport MainFactsBoth MainEntryBoth.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import AsanProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.BothW Require Import BImg ABase AU_kit AU_iface AU_consts AHarnessU_iface AAtexit_iface F_module_dtor_pre
     AD_handoff_md AD_hokit AD_handoff_exit AD_handoff0 ADriver_iface.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {XP : ExitParams}.
Section Handoff.
  Variables (V : nat -> Z) (m : word -> option byte).
  Hypothesis HM : Forall (mfact_ok bsegs V m) both_mem_facts.
  Ltac go := repeat match goal with |- _ /\ _ => split end; ho_cells V m HM.

  Lemma client_img_init : client_img m.
  Proof. unfold client_img, AGOT_SUAR, ASUAR, AVTAB_SRS, AVTAB_VU8, ASRS_FN, AVU8_FN. go. Qed.

  (* [comment removed for export] *)
  Ltac sh0 :=
    match goal with |- m (wa ?A) = _ =>
      let a := eval vm_compute in A in change A with a; replace a with (a + 0) by lia;
      first [ apply (mzero_cover V m both_mem_facts a 1 HM); [vm_compute; reflexivity | lia]
            | apply (zchunk_pointwise m a 1); [apply rw_C1_CB; ho_cells V m HM | lia | lia] ] end.
  Lemma client_sh_init : client_sh m.
  Proof.
    intros X HX. unfold client_sh_addrs in HX. cbn [In] in HX.
    repeat (destruct HX as [<-|HX]; [sh0|]). destruct HX.
  Qed.

  Lemma harness_invA_init : harness_invA m.
  Proof. split; [exact client_img_init | exact client_sh_init]. Qed.

  Lemma client_static0_init : client_static0 m.
  Proof.
    unfold client_static0.
    split. { unfold atexit_rt. split; [ho_cells V m HM|]. exists (Z_to_bv 8 1), (Z_to_bv 8 0), (Z_to_bv 8 0), (Z_to_bv 64 0). ho_cells V m HM. }
    split; [exact (atexit_main_init V m HM)|].
    unfold AVEC, AVEC_GUARD, AFALLBACK, guard0, w0.
    repeat match goal with |- rw_cells _ _ _ _ /\ _ => split; [ho_cells V m HM|] end.
    destruct (sh_chunk V m both_mem_facts (shad 0x6ad740, 8) HM ltac:(vm_compute; reflexivity)) as [j H].
    exact (proj2 H).
  Qed.

  Lemma harness_inv0_init : harness_inv0 m.
  Proof. split; [exact harness_invA_init | exact client_static0_init]. Qed.
End Handoff.
End CANSEC1.
