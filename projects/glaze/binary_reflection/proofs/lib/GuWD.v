(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzDev.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import GuCommon.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Export GuWDT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition e_x : expr := EExt false 0 8 (EVar 31).
Definition e_exp : expr := EAlu ALU_AND (EAlu ALU_SRL e_x (ELit 52)) (ELit 2047).
Definition e_mant : expr := EAlu ALU_AND e_x (ELit 4503599627370495).
Definition two52 : Z := 2 ^ 52.  Definition two63 : Z := 2 ^ 63.

(* [comment removed for export] *)
Definition P_SPEC : Z := 0x3a4fc.
Definition P_SH : Z := 0x3a55c.     (* [comment removed for export] *)
Definition LDA : Z := 0x3a47c.  Definition LDB : Z := 0x3a480.      (* [comment removed for export] *)
Definition P_DIA1 : Z := 0x3a5c8.  Definition J_DIA1 : Z := 0x3a5f0.
Definition P_IDIA : Z := 0x3ad80.  Definition J_IDIA : Z := 0x3ad88.
Definition P_J : Z := 0x3a618.      (* [comment removed for export] *)
Definition P_T6 : Z := 0x3a72c.
Definition P_POPA : Z := 0x3a824.  Definition P_POPB : Z := 0x3a8bc.
Definition P_N : Z := 0x3a910.      (* [comment removed for export] *)
Definition P_IDX : Z := 0x3a93c.
Definition A1 : Z := 0x3a960.  Definition A2 : Z := 0x3aa3c.  Definition A3 : Z := 0x3aa44.  Definition A4 : Z := 0x3aa9c.
Definition B1 : Z := 0x3abd0.
Definition P_SDIA : Z := 0x3ae38.   (* [comment removed for export] *)
Definition P_SUB : Z := 0x3ae7c.    (* [comment removed for export] *)
Definition P_Q : Z := 0x3aecc.      (* [comment removed for export] *)
Definition M10 : Z := 0x199999999999999a.

Definition X42 (k : AP.plan) : AP.plan := PExt 42 [] k.
Definition X44 (r : Z) (k : AP.plan) : AP.plan := PExt 44 [ELit r] k.
Definition MEMMOVE (k : AP.plan) : AP.plan := PExt 3 [] k.
Definition V_W : nat := 49.

  Definition V_T6 : nat := 70.  Definition V_N : nat := 80.   (* [comment removed for export] *)

Definition tail : AP.plan :=
  PBump M (PFresh 10 0 (Some e_buf) (PFact (KRange (EVar M) 0 MMAX) (PMerge 0))).
Fixpoint creg (r : nat) (lo : Z) (n : nat) (k : AP.plan) : AP.plan :=
  match n with O => k | Datatypes.S n' => PCaseReg r lo k (creg r (lo + 1) n' k) end.



(* [comment removed for export] *)
Definition LOJ : nat := 32.
Definition J_E : nat := 52.  Definition J_SIG : nat := 53.  Definition J_HL : nat := 54.  Definition J_SGN : nat := 55.
Definition J_D : nat := 56.  Definition J_Q : nat := 57.
Definition deadJ : list nat := [1; 5; 6; 7; 8; 11; 12; 13; 14; 15; 16; 17; 21; 22; 23; 24; 28; 29; 30; 31]%nat.   (* [comment removed for export] *)
Definition regsJ : list expr :=
  sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_havoc regs0 deadJ LOJ)
    2 (eadd e_sp (ELit (-80))))
    9 (eadd (EVar J_E) (ELit (-340))))          (* [comment removed for export] *)
    10 (EVar J_SIG))
    18 (EVar J_HL))
    19 (eadd e_buf (EVar J_SGN)))
    20 (eadd (EVar J_D) (escale (2 ^ 32) (EVar J_Q))).   (* [comment removed for export] *)
Definition frameJ : list kentry :=
  [ KWord (SA e_sp (-8)) 8 (EVar 0); KWord (SA e_sp (-16)) 8 (EVar 7); KWord (SA e_sp (-24)) 8 (EVar 8);
    KWord (SA e_sp (-32)) 8 (EVar 17); KWord (SA e_sp (-40)) 8 (EVar 18); KWord (SA e_sp (-48)) 8 (EVar 19);
    KWord (SA e_sp (-56)) 8 (EVar 20); KWord (SA e_sp (-64)) 8 (EVar 21); KWord (SA e_sp (-72)) 8 (EVar 22);
    KWord (SA e_sp (-80)) 8 (EVar 23) ].
(* [comment removed for export] *)
Definition YLO : Z := 112.
Definition knJ : list kentry :=
  [ KRange (EVar J_E) 18 649; KRange (EVar J_SIG) 0 (2 ^ 64 - 1); KRange (EVar J_HL) 0 1; KRange (EVar J_SGN) 0 1; KRange (EVar J_D) 0 10 ]
  ++ frameJ ++ [ KRange e_buf PTRLO (objhi K); KDisj (SA e_buf 0) (ELit K) (SA e_sp (- YLO)) (ELit YLO); KWr (SA e_buf 0) (ELit K); KUnk (SA e_buf 0) (ELit K); KWr (SA e_sp (- FR)) (ELit FR) ]
  ++ sp_facts YLO ++ [ img_apart (e_buf) 0 (ELit K); KImg 0x10000 0x75000 ].
Definition jsJ : acs := mkcs YLO WS P_J regsJ knJ 58.



Definition ncls (k : AP.plan) : AP.plan := PCase2 (EVar V_N) 0 k (PCase2 (EVar V_N) 1 k (PCase2 (EVar V_N) 2 k k)).
  (* [comment removed for export] *)
(* [comment removed for export] *)
Definition P_SHLU : Z := 0x3ab48.   (* [comment removed for export] *)
Definition LTU : AP.plan := PRun [A4] (X42 (PRun [] tail)).
Definition T1U : AP.plan := PRun [A2] (X42 (PRun [A3] (X42 (PRun [] (MEMMOVE LTU))))).
Definition T0U : AP.plan := PRun [A2] (X42 (PRun [A3] (X42 (PRun [] (MEMMOVE (ncls LTU)))))).
Definition FIXLU : AP.plan :=
  PRun [P_IDX] (creg 15 0 19 (PRun [A1] (X42 (PRun [] (MEMMOVE (PCaseReg 18 0 (PRespell 18 (ELit 0) T0U) (PRespell 18 (ELit 1) T1U))))))).
Definition SCU : AP.plan := PRun [B1] (X42 (PRun [] tail)).
Definition SCILU : AP.plan := PRun [P_SHLU] (PCaseReg 18 0 (ncls SCU) SCU).
Definition WRJLU (b : Z) : AP.plan := PCase2 (EVar J_E) (b - 1) SCILU (PCase2 (EVar J_E) (b + 19) FIXLU SCILU).
Definition outsJL : AP.plan :=
  PCase2 (EVar J_SIG) 999999999999999 (PRespell 21 (ELit 0) (WRJLU 338)) (PRespell 21 (ELit 1) (WRJLU 337)).
Definition numtailJ : AP.plan := X44 13 (X44 14 (PBump V_N (PFresh 22 0 None (PForget [1%nat] outsJL)))).
Definition lo1J : AP.plan :=
  PRun [0x3a744] (X44 30 (PRun [0x3a764] (X44 6 (PRun [0x3a77c] (X44 14
    (PRun [P_POPA] (X44 15 (PExt 43 [ELit 15] (PRun [P_N] numtailJ))))))))).
Definition lo0J : AP.plan := PRun [P_POPB] (X44 14 (PExt 43 [ELit 14] (PRun [P_N] numtailJ))).
Definition kJ : AP.plan :=
  PRun [0x3a694] (X44 12 (PRun [0x3a6a8] (X44 12 (PRun [0x3a6bc] (X44 8
    (PRun [P_T6] (X44 13 (PBump V_T6 (X44 31 (PCase2 (EVar V_T6) 0 lo0J lo1J)))))))))).

(* [comment removed for export] *)
Definition MR : AP.plan :=     (* [comment removed for export] *)
  PRun [P_J] (X44 10 (PBump 60 (PFresh 20 0 None (PMergeW 1 [(J_D, EVar 60); (J_Q, ELit 0)])))).
Definition regpre (k : AP.plan) : AP.plan :=
  PRun [P_SH] (X42 (PRun [LDA; P_DIA1] (X42 (PRun [LDB; P_DIA1] (X42 (PRun [P_DIA1] (PBranch (PRun [J_DIA1] k) (PRun [J_DIA1] k)))))))).
Definition irrpre (k : AP.plan) : AP.plan :=
  PRun [LDA; P_IDIA] (X42 (PRun [LDB; P_IDIA] (X42 (PRun [P_IDIA] (PBranch (PRun [J_IDIA] k) (PRun [J_IDIA] k)))))).
Definition armReg : AP.plan :=
  PCase2 e_exp 1008 (regpre MR) (PCase2 e_exp 1011 (regpre MR) (PCase2 e_exp 1074 (regpre MR) (PCase2 e_exp 1078 (regpre MR) (regpre MR)))).
Definition armIrr : AP.plan :=
  PCase2 e_exp 1008 (irrpre MR) (PCase2 e_exp 1012 (irrpre MR) (PCase2 e_exp 1075 (irrpre MR) (PCase2 e_exp 1078 (irrpre MR) (irrpre MR)))).

(* [comment removed for export] *)
Definition QW : expr := EMd M_MULHU (EVar V_W) (ELit M10).
Definition subtail : AP.plan :=
  PRun [P_Q] (PBump V_W (PFresh 11 0 None (divfact (EVar V_W) QW 10 (PRun [P_J] (X44 10 (PMergeW 1 [(J_D, esub (EVar V_W) (escale 10 QW)); (J_Q, QW)])))))).
Fixpoint decs (ts : list Z) : AP.plan :=
  match ts with [] => subtail | t :: r => PCase2 (EVar 48) t subtail (decs r) end.
Definition decades : AP.plan :=
  decs [9; 99; 999; 9999; 99999; 999999; 9999999; 99999999; 999999999; 9999999999; 99999999999; 999999999999;
        9999999999999; 99999999999999; 999999999999999].
Definition subL2 : AP.plan := PRun [P_SUB] (PBump 48 (PFresh 11 0 None (PForget [1%nat] decades))).
Definition subLarge : AP.plan :=
  PRun [P_SDIA] (PBump 46 (X44 12 (PCase2 (EVar 46) (2 ^ 62 - 1) subL2 (PCase2 (EVar 46) (2 ^ 62) subL2 subL2)))).
Definition subSmall : AP.plan :=
  PRun [P_SUB] (PExt 45 [ELit 11; e_x] (PBump 48 (PFresh 11 0 None (PForget [1%nat; 2%nat] decades)))).




(* [comment removed for export] *)
Definition tailH : AP.plan :=
  PBump M (PFresh 10 0 (Some e_buf) (PFact (KRange (EVar M) 0 MMAX) (PHandoffW 0 []))).

(* [comment removed for export] *)
Definition DPS (st : list dstep) : acs := snd (dpath USEGS IT AUBSAN (XN IT NXF) XB0 BFUEL NXF tin (DRun [P_SPEC] :: st) 0).
Definition hsg (b : Z) : dstep := if Z.eqb b 0 then DLo e_x (two63 - 1) else DHi e_x (two63 - 1).
Definition pre (b : Z) : list dstep := [hsg b; DHi e_x b; DLo e_x (b + 2047 * two52 - 1)].
Definition S_small0 : acs := Eval vm_compute in DPS (pre 0 ++ [DLo e_x 63]).
Definition S_small1 : acs := Eval vm_compute in DPS (pre two63 ++ [DLo e_x (two63 + 63)]).
Definition S_large0 : acs := Eval vm_compute in DPS (pre 0 ++ [DHi e_x 63; DLo e_x (two52 - 1)]).
Definition S_irr0 : acs := Eval vm_compute in DPS (pre 0 ++ [DHi e_x 63; DHi e_x (two52 - 1); DLo e_mant 0]).
Definition S_reg0 : acs := Eval vm_compute in DPS (pre 0 ++ [DHi e_x 63; DHi e_x (two52 - 1); DHi e_mant 0]).
Definition is_xr (K : kentry) : bool :=
  match K with KRange e lo hi => (expr_eqb e e_x && negb (Z.eqb lo 0 && Z.eqb hi (2 ^ 64 - 1)))%bool | _ => false end.
Definition gen (st : acs) (extra : list kentry) : acs := set_kn st (extra ++ filter (fun K => negb (is_xr K)) (kn st)).
Definition TGL : acs := gen S_large0 [KRange e_exp 0 0; KRange e_mant 64 (two52 - 1)].
Definition TGI : acs := gen S_irr0 [KRange e_exp 1 2046].
Definition TGR : acs := gen S_reg0 [KRange e_exp 1 2046; KRange e_mant 1 (two52 - 1)].
Definition LOG : nat := nxt S_large0.
Definition halfG (b : Z) : AP.plan :=
  PCase2 e_x b (PRun [] tailH) (PCase2 e_x (b + 2047 * two52 - 1)
     (PCase2 e_x (b + 63) (PMerge 2) (PCase2 e_x (b + two52 - 1) (PMerge 2) (PCase2 e_mant 0 (PMerge 2) (PMerge 2))))
     (PRun [] tailH)).
Definition karms : AP.plan :=
  PRun [P_SPEC] (PVia 1 jsJ LOJ (PViaM 2 [(S_small0, subSmall); (S_small1, subSmall); (TGL, subLarge); (TGI, armIrr); (TGR, armReg)] LOG
                                    (PCase2 e_x (two63 - 1) (halfG 0) (halfG two63))) kJ).
Definition plan_wd : AP.plan := PVia 0 tout LO karms (PHandoff 0).

Lemma cert : check USEGS IT AUBSAN NXF LIMIT (XN IT NXF) XE0 XB0 XC0 (HSce ce) 0%nat BFUEL FUEL None (ce_tin ce) plan_wd = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma gplan : gplan_ok plan_wd = true. Proof. vm_compute. reflexivity. Qed.
Lemma hshape : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
