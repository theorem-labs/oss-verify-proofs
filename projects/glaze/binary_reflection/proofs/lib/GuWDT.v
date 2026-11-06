(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import GuCommon.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition ENTRY : Z := 0x3a48c.
Definition RETPC : Z := 0x3ac48.
Definition IT : itab := mk_itab_ranges USEGS [(ENTRY, 681%nat); (0x3a3b0, 28%nat); (0x3a420, 27%nat)].
Lemma IT_ok : itab_sound USEGS IT. Proof. apply APS.mk_itab_ranges_sound. Qed.

Definition NXF : nat := 31.
Definition e_buf := e_a0.
Definition K : Z := 38.
Definition FR : Z := 96.         (* [comment removed for export] *)
Definition WS : list (expr * expr) := [(e_buf, ELit K)].
(* [comment removed for export] *)
Definition YLO : Z := 112.
Definition kn_in : list kentry :=
  [ KRange e_buf PTRLO (objhi K); KDisj (SA e_buf 0) (ELit K) (SA e_sp (- YLO)) (ELit YLO); KWr (SA e_buf 0) (ELit K); KUnk (SA e_buf 0) (ELit K); KWr (SA e_sp (- FR)) (ELit FR) ]
  ++ sp_facts YLO ++ [ img_apart (e_buf) 0 (ELit K); KImg 0x10000 0x75000 ].
Definition tin : acs := mkcs YLO WS ENTRY regs0 kn_in NXF.

Definition MMAX : Z := 36.
Definition M : nat := 120.
Definition LO : nat := 121.
Definition js_regs : list expr :=
  sr_havoc (sr_upd (sr_upd regs0 10 (eadd e_buf (EVar M))) 11 (EVar LO)) caller_saved_but_a01 (S LO).
Definition kn_out : list kentry :=
  [ KRange (EVar M) 0 MMAX; KWr (SA e_buf 0) (ELit K); KUnk (SA e_buf 0) (ELit K); KWr (SA e_sp (- FR)) (ELit FR) ] ++ sp_facts YLO.
Definition tout : acs := mkcs YLO WS RETPC js_regs kn_out (LO + 14)%nat.
Definition ce : gcallee := GCE NXF tin [tout] 0 0.
