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
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Export GuWFT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition e_lo : expr := EExt false 0 4 (EVar 31).
Definition e_x : expr := EExt true 0 4 e_lo.
Definition e_exp : expr := EAlu ALU_SRL (EMd M_MUL (ELit 8589934592) e_x) (ELit 56).
Definition e_mant : expr := EAlu ALU_SRL (EMd M_MUL (ELit 2199023255552) e_x) (ELit 41).

(* [comment removed for export] *)
Definition P_SPEC : Z := 0x39ad0.   (* [comment removed for export] *)
Definition LDA : Z := 0x3a47c.      (* [comment removed for export] *)
Definition LDB : Z := 0x3a480.      (* [comment removed for export] *)
Definition P_DIA1 : Z := 0x39bb4.   (* [comment removed for export] *)
Definition J_DIA1 : Z := 0x39bcc.
Definition P_SIG : Z := 0x39bec.    (* [comment removed for export] *)
Definition P_HL : Z := 0x39c1c.     (* [comment removed for export] *)
Definition P_T3 : Z := 0x39d10.     (* [comment removed for export] *)
Definition P_POP : Z := 0x39d48.    (* [comment removed for export] *)
Definition P_NUM : Z := 0x39da8.    (* [comment removed for export] *)
Definition P_IDX : Z := 0x39dc8.    (* [comment removed for export] *)
Definition A1 : Z := 0x39dec.  Definition A2 : Z := 0x39ec0.  Definition A3 : Z := 0x39ec8.  Definition A4 : Z := 0x3a080.
Definition B1 : Z := 0x3a020.       (* [comment removed for export] *)
Definition P_IDIA : Z := 0x3a218.   (* [comment removed for export] *)
Definition J_IDIA : Z := 0x3a220.
Definition SUB_RU : Z := 0x3a2bc.   (* [comment removed for export] *)
Definition P_SUB : Z := 0x3a2e8.    (* [comment removed for export] *)

Definition X42 (k : AP.plan) : AP.plan := PExt 42 [] k.
Definition X44 (r : Z) (k : AP.plan) : AP.plan := PExt 44 [ELit r] k.
Definition V_SIG : nat := 50.  Definition V_W : nat := 51.  Definition V_N : nat := 70.   (* [comment removed for export] *)
Definition P_Q : Z := 0x3a348.      (* [comment removed for export] *)
Definition M10 : Z := 0x199999999999999a.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition tail : AP.plan :=
  PBump M (PFresh 10 0 (Some e_buf) (PFact (KRange (EVar M) 0 MMAX) (PMerge 0))).
Fixpoint creg (r : nat) (lo : Z) (n : nat) (k : AP.plan) : AP.plan :=
  match n with O => k | Datatypes.S n' => PCaseReg r lo k (creg r (lo + 1) n' k) end.

(* [comment removed for export] *)
Definition LOJ : nat := 32.
Definition J_HL : nat := 50.  Definition J_D : nat := 51.  Definition J_Q : nat := 52.  Definition J_SIG : nat := 53.
Definition J_E4 : nat := 54.  Definition J_SGN : nat := 55.
Definition deadF : list nat := [1; 5; 6; 7; 8; 9; 15; 16; 17; 18; 20; 21; 22; 28; 29; 30; 31]%nat.   (* [comment removed for export] *)
Definition regsF : list expr :=
  sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_havoc regs0 deadF LOJ)
    2 (eadd e_sp (ELit (-64))))
    10 (EVar J_HL))
    11 (EAlu ALU_SLTU (ELit 9999999) (EVar J_SIG)))        (* [comment removed for export] *)
    12 (eadd (EVar J_D) (escale (2 ^ 32) (EVar J_Q))))
    13 (EVar J_SIG))
    14 (eadd (EVar J_E4) (ELit (-400))))
    19 (eadd e_buf (EVar J_SGN)).
Definition frameF : list kentry :=
  [ KWord (SA e_sp (-8)) 8 (EVar 0); KWord (SA e_sp (-16)) 8 (EVar 7); KWord (SA e_sp (-24)) 8 (EVar 8);
    KWord (SA e_sp (-32)) 8 (EVar 17); KWord (SA e_sp (-40)) 8 (EVar 18); KWord (SA e_sp (-48)) 8 (EVar 19);
    KWord (SA e_sp (-56)) 8 (EVar 20); KWord (SA e_sp (-64)) 8 (EVar 21) ].
(* [comment removed for export] *)
Definition YLO : Z := 80.
Definition knF : list kentry :=
  [ KRange (EVar J_HL) 0 1; KRange (EVar J_D) 0 10; KRange (EVar J_SIG) 0 (2 ^ 64 - 1); KRange (EVar J_E4) 355 439;
    KRange (EVar J_SGN) 0 1 ]
  ++ frameF ++ [ KRange e_buf PTRLO (objhi K); KDisj (SA e_buf 0) (ELit K) (SA e_sp (- YLO)) (ELit YLO);
                 KWr (SA e_buf 0) (ELit K); KUnk (SA e_buf 0) (ELit K); KWr (SA e_sp (- FR)) (ELit FR) ]
  ++ sp_facts YLO ++ [ img_apart (e_buf) 0 (ELit K); KImg 0x10000 0x75000 ].
Definition jsF : acs := mkcs YLO WS P_HL regsF knF 56.
(* [comment removed for export] *)
Definition ncls (k : AP.plan) : AP.plan := PCase2 (EVar V_N) 0 k (PCase2 (EVar V_N) 1 k (PCase2 (EVar V_N) 2 k k)).
Definition ESPL (k : AP.plan) : AP.plan := PCase2 (EVar J_SIG) 9999999 k k.
Definition TAILF : AP.plan := PRun [A4] (X42 (PRun [] tail)).
Definition FIX0 : AP.plan := PRun [A2] (X42 (PRun [A3] (X42 (PRun [0x39f24] (ncls TAILF))))).
Definition FIX1 : AP.plan := PRun [A2] (X42 (PRun [A3] (X42 TAILF))).
Definition FIXL : AP.plan := PRun [P_IDX] (creg 16 0 10 (PRun [A1] (X42 (PRun [0x39e34] (ESPL (PCase2 (EVar J_HL) 0 FIX0 FIX1)))))).
Definition SCI0 : AP.plan := PRun [B1] (X42 (PRun [] tail)).
Definition SCIL : AP.plan := ESPL (PRun [0x39f98] (PCase2 (EVar J_HL) 0 (PRun [0x39fa0] (ncls SCI0)) SCI0)).
Definition WRL : AP.plan := PCase2 (EVar J_E4) 395 SCIL (PCase2 (EVar J_E4) 406 FIXL SCIL).
Definition kF : AP.plan :=
  PExt 44 [ELit 15] (PRun [P_T3] (X44 28 (PRun [P_POP] (X44 15 (PExt 43 [ELit 15] (PRun [P_NUM] (PBump V_N (PFresh 15 0 None WRL)))))))).

(* [comment removed for export] *)
Definition hlJ : AP.plan := PRun [P_HL] (PBump 60 (PFresh 12 0 None (PMergeW 1 [(J_D, EVar 60); (J_Q, ELit 0)]))).
Definition sig : AP.plan :=
  PRun [P_SIG] (PBump V_SIG (PExt 44 [ELit 13]
    (PCase2 (EVar V_SIG) 999999 hlJ (PCase2 (EVar V_SIG) 9999999 hlJ hlJ)))).
(* [comment removed for export] *)
Definition reg : AP.plan :=
  PRun [LDA; P_DIA1] (X42 (PRun [LDB; P_DIA1] (X42 (PRun [P_DIA1] (PBranch (PRun [J_DIA1] sig) (PRun [J_DIA1] sig)))))).
Definition irr : AP.plan :=
  PRun [LDA; P_IDIA] (X42 (PRun [LDB; P_IDIA] (X42 (PRun [P_IDIA] (PBranch (PRun [J_IDIA] sig) (PRun [J_IDIA] sig)))))).
(* [comment removed for export] *)
Definition armReg : AP.plan :=
  PCase2 e_exp 110 reg (PCase2 e_exp 113 reg (PCase2 e_exp 116 reg (PCase2 e_exp 146 reg (PCase2 e_exp 149 reg (PCase2 e_exp 153 reg reg))))).
Definition armIrr : AP.plan :=
  PCase2 e_exp 110 irr (PCase2 e_exp 113 irr (PCase2 e_exp 117 irr (PCase2 e_exp 147 irr (PCase2 e_exp 150 irr (PCase2 e_exp 153 irr irr))))).
(* [comment removed for export] *)
Definition QW : expr := EMd M_MULHU (EVar V_W) (ELit M10).
Definition subtail : AP.plan :=
  PRun [P_Q] (PBump V_W (PFresh 14 0 None (divfact (EVar V_W) QW 10
    (PRun [P_HL] (PMergeW 1 [(J_D, esub (EVar V_W) (escale 10 QW)); (J_Q, QW)]))))).
Definition decades : AP.plan :=
  PCase2 (EVar V_SIG) 9 subtail (PCase2 (EVar V_SIG) 99 subtail (PCase2 (EVar V_SIG) 999 subtail (PCase2 (EVar V_SIG) 9999 subtail
  (PCase2 (EVar V_SIG) 99999 subtail (PCase2 (EVar V_SIG) 999999 subtail (PCase2 (EVar V_SIG) 9999999 subtail subtail)))))).
Definition armSub2 : AP.plan := PRun [P_SUB] (PBump V_SIG (PFresh 14 0 None decades)).
Definition armSub1 : AP.plan := PRun [SUB_RU] (PBump 48 (PFresh 5 0 None (PCase2 (EVar 48) 0 armSub2 armSub2))).
Definition armSub : AP.plan := PCase2 e_mant 7 armSub1 armSub1.


(* [comment removed for export] *)
Definition tailH : AP.plan :=
  PBump M (PFresh 10 0 (Some e_buf) (PFact (KRange (EVar M) 0 MMAX) (PHandoffW 0 []))).
Definition armInfH : AP.plan := PCase2 e_lo (2 ^ 31 - 1) (PRun [] tailH) (PRun [] tailH).
Definition karms : AP.plan :=
  PRun [P_SPEC] (PVia 1 jsF LOJ (PCase2 e_exp 0 (PCase2 e_mant 0 (PRun [] tailH) armSub)
                                (PCase2 e_exp 254 (PCase2 e_mant 0 armIrr armReg) armInfH)) kF).
Definition plan_wf : AP.plan := PVia 0 tout LO karms (PHandoff 0).

Lemma cert : check USEGS IT AUBSAN NXF LIMIT (XN IT NXF) XE0 XB0 XC0 (HSce ce) 0%nat BFUEL FUEL None (ce_tin ce) plan_wf = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma gplan : gplan_ok plan_wf = true. Proof. vm_compute. reflexivity. Qed.
Lemma hshape : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
