(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec RzCPS.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.A17 Require Import RT_iface RT_vis RT_frmkit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section Kit2.
Variable segs : list Segment.
Variable segtop : Z.

(* [comment removed for export] *)
Lemma astf_allow_x : forall A X Pm PM,
  A_wf X ->
  (forall mo, PM mo -> (eager_used mo + A_bytes X + A_bytes A <= vm_limit (m_vmmaps mo))%Z) ->
  cps segs (AST segtop A (frmW Pm) PM)
    (AST segtop (X ++ A) (frmW (fun ms => exists ms0 mo, PM mo /\ Pm ms0 /\ revealed A (X ++ A) mo ms0 ms
                                     /\ (forall a, HID A mo a = true -> ms_mem ms0 a = None /\ segtop <= bv_unsigned a)
                                     /\ (forall a, HID (X ++ A) mo a = true -> ms_mem ms a = None))) PM).
Proof.
  intros A X Pm PM HX Hb T c Hc Hk. apply (ast_allow_x segs segtop A X (frmW Pm) PM HX Hb T c Hc).
  intros c' Hc'. apply Hk. eapply AST_conseq; [exact Hc' | | intros mo Hmo; exact Hmo].
  intros ms (ms0 & mo & HPM & [HP HF] & HR & HH & HH'). split; [exists ms0, mo; auto|].
  destruct HR as (E & _). rewrite E, set_mem_fcsr. exact HF.
Qed.

End Kit2.
