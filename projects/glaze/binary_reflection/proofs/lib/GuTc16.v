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

Definition ENTRY : Z := 0x3c588.
Definition RET1 : Z := 0x3c5dc.  Definition RET2 : Z := 0x3c6a0.  Definition RET3 : Z := 0x3c758.
Definition IT : itab := mk_itab_ranges USEGS [(ENTRY, 118%nat)].
Lemma IT_ok : itab_sound USEGS IT. Proof. apply APS.mk_itab_ranges_sound. Qed.

Definition NXF : nat := 31.
Definition e_p : expr := e_a0.   Definition e_v : expr := e_a1.
Definition VMAX : Z := 65535.
Definition WSZ : Z := 5.
Definition WS : list (expr * expr) := [(e_p, ELit WSZ)].
(* [comment removed for export] *)
Definition YLO : Z := 0.
Definition kn_in : list kentry :=
  [ KRange e_v 0 VMAX; KRange e_p PTRLO (objhi WSZ); KWr (SA e_p 0) (ELit WSZ) ] ++ sp_facts YLO ++ [ img_apart (e_p) 0 (ELit WSZ); KImg 0x10000 0x75000 ].
Definition tin : acs := mkcs YLO WS ENTRY regs0 kn_in NXF.

(* [comment removed for export] *)
Definition M : nat := 60.
Definition LO : nat := 61.
Definition js_regs : list expr := sr_havoc (sr_upd (sr_upd regs0 10 (eadd e_p (EVar M))) 11 (EVar LO)) caller_saved_but_a01 (S LO).
Definition kn_out : list kentry := [ KRange (EVar M) 1 WSZ; KWr (SA e_p 0) (ELit WSZ) ] ++ sp_facts YLO.
Definition tout (ret : Z) : acs := mkcs YLO WS ret js_regs kn_out (LO + 14)%nat.
Definition ce : gcallee := GCE NXF tin [tout RET1; tout RET2; tout RET3] 0 0.

(* [comment removed for export] *)
Fixpoint xloads (n : nat) (k : plan) : plan :=
  match n with O => k | S n' => PRun [] (PExt 0 [] (xloads n' k)) end.
Definition tail (h : nat) : plan :=
  PRun [] (PBump M (PFresh 10 0 (Some e_p) (PFact (KRange (EVar M) 1 WSZ) (PHandoff h)))).
Definition armA : plan := xloads 2 (tail 0).
(* [comment removed for export] *)
Definition armB : plan := divfactU e_v (q100 e_v) 100 (zfact e_v (q100 e_v) 100 (xloads 3 (tail 1))).
(* [comment removed for export] *)
Definition qs : expr := EAlu ALU_SRL (escale 839 (EAlu ALU_SRL e_v (ELit 4))) (ELit 19).
Definition r4 : expr := rem e_v qs 10000.
Definition armC : plan :=
  PExt 41 [r4; e_v] (divfactU r4 (q100w r4) 100 (zfact r4 (q100w r4) 100 (xloads 2 (tail 2)))).
Definition plan_tc16 : plan :=
  PCase2 e_v 9 armA (PCase2 e_v 99 armA (PCase2 e_v 999 armB (PCase2 e_v 9999 armB armC))).
Definition SHAPE : shape := SHole 0.

Lemma cert : check USEGS IT AUBSAN NXF LIMIT (XN IT NXF) XE0 XB0 XC0 (HSce ce) 0%nat BFUEL FUEL None (ce_tin ce) plan_tc16 = COk SHAPE.
Proof. vm_cast_no_check (@eq_refl cres (COk SHAPE)). Qed.
Lemma gplan : gplan_ok plan_tc16 = true. Proof. vm_compute. reflexivity. Qed.
Lemma hshape : holes_only SHAPE = true. Proof. reflexivity. Qed.
