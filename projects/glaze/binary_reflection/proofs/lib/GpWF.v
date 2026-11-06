(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import GpCommon.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Export GpWFT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition e_lo : expr := EExt false 0 4 (EVar 31).
Definition e_x : expr := EExt true 0 4 e_lo.

Definition e_exp : expr := EAlu ALU_SRL (EMd M_MUL (ELit 8589934592) e_x) (ELit 56).
Definition e_mant : expr := EAlu ALU_SRL (EMd M_MUL (ELit 2199023255552) e_x) (ELit 41).

(* [comment removed for export] *)
Definition P_SPEC : Z := 0x36dd0.   (* [comment removed for export] *)
Definition P_LD1 : Z := 0x36e44.    (* [comment removed for export] *)
Definition P_DIA1 : Z := 0x36e8c.   (* [comment removed for export] *)
Definition P_SIG : Z := 0x36eb4.    (* [comment removed for export] *)
Definition P_HL : Z := 0x36edc.     (* [comment removed for export] *)
Definition P_T3 : Z := 0x36fd0.     (* [comment removed for export] *)
Definition P_POP : Z := 0x37008.    (* [comment removed for export] *)
Definition A1 : Z := 0x370b8.  Definition A2 : Z := 0x37140.  Definition A3 : Z := 0x37144.  Definition A4 : Z := 0x37264.
Definition B1 : Z := 0x37220.       (* [comment removed for export] *)
Definition P_ILD1 : Z := 0x37340.  Definition P_ILD2 : Z := 0x37344.  Definition P_IDIA : Z := 0x373c0. (* [comment removed for export] *)
Definition P_SUB : Z := 0x37484.    (* [comment removed for export] *)

Definition X42 (k : AP.plan) : AP.plan := PExt 42 [] k.
Definition V_SIG : nat := 50.  Definition V_HL : nat := 51.

(* [comment removed for export] *)
Definition tail : AP.plan :=
  PBump M (PFresh 10 0 (Some e_buf) (PFact (KRange (EVar M) 0 MMAX) (PMerge 0))).
Definition X44 (r : Z) (k : AP.plan) : AP.plan := PExt 44 [ELit r] k.
Definition P_NUM : Z := 0x37068.    (* [comment removed for export] *)
Definition V_N : nat := 56.
(* [comment removed for export] *)
Definition P_IDX : Z := 0x370ac.
Fixpoint creg (r : nat) (lo : Z) (n : nat) (k : AP.plan) : AP.plan :=
  match n with O => k | Datatypes.S n' => PCaseReg r lo k (creg r (lo + 1) n' k) end.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition LOJ : nat := 32.
Definition J_HL : nat := 43.  Definition J_EF : nat := 44.  Definition J_E4 : nat := 45.
Definition deadF : list nat := [1; 5; 6; 7; 8; 12; 15; 16; 17; 19; 21]%nat.   (* [comment removed for export] *)
Definition e_s1 : expr := EAlu ALU_ADD e_buf (EAluw ALU_SRL e_x (ELit 31)).
Definition regsF : list expr :=
  sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_havoc regs0 deadF LOJ)
    2 (eadd e_sp (ELit (-64))))
    9 e_s1)
    10 (EVar J_HL))
    11 (EVar J_EF))
    13 (EVar J_EF))
    14 (eadd (EVar J_E4) (ELit (-400))))
    18 (ELit 0x13380))
    20 e_x.
Definition frameF : list kentry :=
  [ KWord (SA e_sp (-8)) 8 (EVar 0); KWord (SA e_sp (-16)) 8 (EVar 7); KWord (SA e_sp (-24)) 8 (EVar 8);
    KWord (SA e_sp (-32)) 8 (EVar 17); KWord (SA e_sp (-40)) 8 (EVar 18); KWord (SA e_sp (-48)) 8 (EVar 19);
    KWord (SA e_sp (-56)) 8 (EVar 20) ].
Definition knF : list kentry :=
  [ KRange (EVar J_HL) 0 1; KRange (EVar J_EF) 0 1; KRange (EVar J_E4) 355 439; KWord (SA e_buf 0) 1 (ELit 45) ]
  ++ frameF ++ kn_in.
Definition jsF : acs := mkcs YLO WS P_HL regsF knF 46.
(* [comment removed for export] *)
Definition ESPLIT (k : AP.plan) : AP.plan :=
  PCaseReg 11 0 (PRespell 11 (ELit 0) (PRespell 13 (ELit 0) k)) (PRespell 11 (ELit 1) (PRespell 13 (ELit 1) k)).
Definition TAILF : AP.plan := PRun [A4] (X42 (PRun [] tail)).
Definition FIX0 : AP.plan := PRun [A2] (X42 (PRun [A3] (X42 (PRun [0x3719c] (PCase2 (EVar V_N) 0 TAILF TAILF))))).
Definition FIX1 : AP.plan := PRun [A2] (X42 (PRun [A3] (X42 TAILF))).
Definition FIXL : AP.plan := PRun [P_IDX] (creg 16 0 10 (ESPLIT (PRun [A1] (X42 (PRun [0x37130] (PCase2 (EVar J_HL) 0 FIX0 FIX1)))))).
Definition SCI0 : AP.plan := PRun [B1] (X42 (PRun [] tail)).
Definition SCIL : AP.plan := ESPLIT (PRun [0x371ec] (PCase2 (EVar J_HL) 0 (PRun [0x371f4] (PCase2 (EVar V_N) 0 SCI0 SCI0)) SCI0)).
Definition WRL : AP.plan := PCase2 (EVar J_E4) 395 SCIL (PCase2 (EVar J_E4) 406 FIXL SCIL).
Definition kF : AP.plan :=
  PRun [P_T3] (X44 28 (PRun [P_POP] (X44 15 (PExt 43 [ELit 15] (PRun [P_NUM] (PBump V_N (PFresh 15 0 None WRL))))))).

(* [comment removed for export] *)
Definition hlJ : AP.plan := PRun [P_HL] (PBump V_HL (PFresh 10 0 None (PMerge 1))).
Definition sigJ : AP.plan :=
  PRun [P_SIG] (PBump V_SIG (PExt 44 [ELit 15] (PCase2 (EVar V_SIG) 999999 hlJ (PCase2 (EVar V_SIG) 9999999 hlJ hlJ)))).
Definition regJ : AP.plan := PRun [P_LD1; P_DIA1] (X42 (PRun [P_DIA1] (PDiamond 0x36ea4 [12%nat] sigJ))).
Definition irrJ : AP.plan := PRun [P_ILD1] (X42 (PRun [P_ILD2] (X42 (PRun [P_IDIA] (PDiamond 0x373c8 [12%nat] sigJ))))).
(* [comment removed for export] *)
Definition armReg : AP.plan :=
  PCase2 e_exp 110 regJ (PCase2 e_exp 113 regJ (PCase2 e_exp 116 regJ (PCase2 e_exp 146 regJ (PCase2 e_exp 149 regJ (PCase2 e_exp 153 regJ regJ))))).
Definition armIrr : AP.plan :=
  PCase2 e_exp 110 irrJ (PCase2 e_exp 113 irrJ (PCase2 e_exp 117 irrJ (PCase2 e_exp 147 irrJ (PCase2 e_exp 150 irrJ (PCase2 e_exp 153 irrJ irrJ))))).
(* [comment removed for export] *)
Definition decades : AP.plan :=
  PCase2 (EVar V_SIG) 9 hlJ (PCase2 (EVar V_SIG) 99 hlJ (PCase2 (EVar V_SIG) 999 hlJ (PCase2 (EVar V_SIG) 9999 hlJ
  (PCase2 (EVar V_SIG) 99999 hlJ (PCase2 (EVar V_SIG) 999999 hlJ (PCase2 (EVar V_SIG) 9999999 hlJ hlJ)))))).
Definition armSub2 : AP.plan := PRun [P_SUB] (PBump V_SIG (PFresh 16 0 None decades)).
(* [comment removed for export] *)
Definition armSub1 : AP.plan := PRun [0x37454] (PBump 48 (PFresh 17 0 None (PCase2 (EVar 48) 0 armSub2 armSub2))).
Definition armSub : AP.plan := PCase2 e_mant 7 armSub1 armSub1.
(* [comment removed for export] *)
Definition tailH : AP.plan :=
  PBump M (PFresh 10 0 (Some e_buf) (PFact (KRange (EVar M) 0 MMAX) (PHandoffW 0 []))).
Definition armInfH : AP.plan := PCase2 e_lo (2 ^ 31 - 1) (PRun [] tailH) (PRun [] tailH).
Definition karms : AP.plan :=
  PRun [P_SPEC] (PVia 1 jsF LOJ (PCase2 e_exp 0 (PCase2 e_mant 0 (PRun [] tailH) armSub)
                                (PCase2 e_exp 254 (PCase2 e_mant 0 armIrr armReg) armInfH)) kF).
Definition plan_wf : AP.plan := PVia 0 tout LO karms (PHandoff 0).

Lemma cert : check PSEGS IT APLAIN NXF LIMIT (XN IT NXF) XE0 XB0 XC0 (HSce ce) 0%nat BFUEL FUEL None (ce_tin ce) plan_wf = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.   (* [comment removed for export] *)
Lemma gplan : gplan_ok plan_wf = true. Proof. vm_compute. reflexivity. Qed.
Lemma hshape : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
