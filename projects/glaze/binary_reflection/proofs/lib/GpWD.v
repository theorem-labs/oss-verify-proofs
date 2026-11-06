(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzDev.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import GpCommon.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Export GpWDT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition e_x : expr := EExt false 0 8 (EVar 31).
Definition e_exp : expr := EAlu ALU_AND (EAlu ALU_SRL e_x (ELit 52)) (ELit 2047).
Definition e_mant : expr := EAlu ALU_AND e_x (ELit 4503599627370495).
Definition two52 : Z := 2 ^ 52.  Definition two63 : Z := 2 ^ 63.

(* [comment removed for export] *)
Definition P_SPEC : Z := 0x37600.
Definition P_SH : Z := 0x3763c.     (* [comment removed for export] *)
Definition P_LD1 : Z := 0x37670.  Definition P_LD2 : Z := 0x37674.   (* [comment removed for export] *)
Definition P_DIA1 : Z := 0x376bc.  Definition J_DIA1 : Z := 0x376e4.
Definition P_ILD1 : Z := 0x37cf8. Definition P_ILD2 : Z := 0x37cfc.  (* [comment removed for export] *)
Definition P_IDIA : Z := 0x37d70.  Definition J_IDIA : Z := 0x37d78.
Definition P_J : Z := 0x376f4.      (* [comment removed for export] *)
Definition P_T6 : Z := 0x37808.     (* [comment removed for export] *)
Definition P_POPA : Z := 0x37900.  Definition P_POPB : Z := 0x37998.
Definition P_N : Z := 0x379ec.      (* [comment removed for export] *)
Definition A1 : Z := 0x37a6c.  Definition A2 : Z := 0x37af0.  Definition A3 : Z := 0x37af4.  Definition A4 : Z := 0x37b24.
Definition B1 : Z := 0x37be8.
Definition P_SDIA : Z := 0x37e10.
   (* [comment removed for export] *)
Definition P_SUB : Z := 0x37e54.    (* [comment removed for export] *)

Definition X42 (k : AP.plan) : AP.plan := PExt 42 [] k.
Definition X44 (r : Z) (k : AP.plan) : AP.plan := PExt 44 [ELit r] k.
Definition MEMMOVE (k : AP.plan) : AP.plan := PExt 3 [] k.
Definition V_T6 : nat := 70.  Definition V_N : nat := 80.   (* [comment removed for export] *)

Definition tail : AP.plan :=
  PBump M (PFresh 10 0 (Some e_buf) (PFact (KRange (EVar M) 0 MMAX) (PMerge 0))).
(* [comment removed for export] *)
Definition P_IDX : Z := 0x37a30.
Fixpoint creg (r : nat) (lo : Z) (n : nat) (k : AP.plan) : AP.plan :=
  match n with O => k | Datatypes.S n' => PCaseReg r lo k (creg r (lo + 1) n' k) end.



(* [comment removed for export] *)
Definition LOJ : nat := 32.
Definition J_E : nat := 53.  Definition J_SIG : nat := 54.  Definition J_HL : nat := 55.  Definition J_SGN : nat := 56.  Definition J_D : nat := 57.
Definition deadJ : list nat := [1; 5; 6; 7; 8; 12; 13; 14; 15; 16; 17; 20; 21; 22; 23; 24; 25; 28; 29; 30; 31]%nat.   (* [comment removed for export] *)
Definition regsJ : list expr :=
  sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_havoc regs0 deadJ LOJ)
    2 (eadd e_sp (ELit (-96))))
    9 (eadd e_buf (EVar J_SGN)))
    10 (eadd (EVar J_E) (ELit (-340))))
    11 (EVar J_SIG))
    18 (EVar J_HL))
    19 (EVar J_D).
Definition frameJ : list kentry :=
  [ KWord (SA e_sp (-8)) 8 (EVar 0); KWord (SA e_sp (-16)) 8 (EVar 7); KWord (SA e_sp (-24)) 8 (EVar 8);
    KWord (SA e_sp (-32)) 8 (EVar 17); KWord (SA e_sp (-40)) 8 (EVar 18); KWord (SA e_sp (-48)) 8 (EVar 19);
    KWord (SA e_sp (-56)) 8 (EVar 20); KWord (SA e_sp (-64)) 8 (EVar 21); KWord (SA e_sp (-72)) 8 (EVar 22);
    KWord (SA e_sp (-80)) 8 (EVar 23); KWord (SA e_sp (-88)) 8 (EVar 24) ].
(* [comment removed for export] *)
Definition YLO : Z := 128.
Definition knJ : list kentry :=
  [ KRange (EVar J_E) 1 632; KRange (EVar J_SIG) 0 (2 ^ 64 - 1); KRange (EVar J_HL) 0 1; KRange (EVar J_SGN) 0 1;
    KRange (EVar J_D) 0 (2 ^ 64 - 1) ]
  ++ frameJ ++ [ KRange e_buf PTRLO (objhi K); KDisj (SA e_buf 0) (ELit K) (SA e_sp (- YLO)) (ELit YLO); KWr (SA e_buf 0) (ELit K); KUnk (SA e_buf 0) (ELit K); KWr (SA e_sp (- FR)) (ELit FR) ]
  ++ sp_facts YLO ++ [ img_apart (e_buf) 0 (ELit K); KImg 0x10000 0x71000 ].
Definition jsJ : acs := mkcs YLO WS P_J regsJ knJ 58.



(* [comment removed for export] *)
Definition P_SHLP : Z := 0x37bb4.   (* [comment removed for export] *)
Definition LTP : AP.plan := PRun [A4] (X42 (PRun [] tail)).
Definition T1P : AP.plan := PRun [A2] (X42 (PRun [A3] (X42 (PRun [] (MEMMOVE LTP))))).
Definition T0P : AP.plan := PRun [A2] (X42 (PRun [A3] (X42 (PRun [] (MEMMOVE (PCase2 (EVar V_N) 0 LTP LTP)))))).
Definition FIXLP : AP.plan :=
  PRun [P_IDX] (creg 15 0 19 (PRun [A1] (X42 (PRun [] (MEMMOVE (PCaseReg 18 0 (PRespell 18 (ELit 0) T0P) (PRespell 18 (ELit 1) T1P))))))).
Definition SCP : AP.plan := PRun [B1] (X42 (PRun [] tail)).
Definition SCILP : AP.plan := PRun [P_SHLP] (PCaseReg 18 0 (PCase2 (EVar V_N) 0 SCP SCP) SCP).
Definition WRJLP (b : Z) : AP.plan := PCase2 (EVar J_E) (b - 1) SCILP (PCase2 (EVar J_E) (b + 19) FIXLP SCILP).
Definition outsJL : AP.plan :=
  PCase2 (EVar J_SIG) 999999999999999 (PRespell 20 (ELit 0) (WRJLP 321)) (PRespell 20 (ELit 1) (WRJLP 320)).
Definition numtailJ : AP.plan :=
  X44 13 (X44 14 (PBump V_N (PFresh 21 0 None (PForget [1%nat] outsJL)))).
(* [comment removed for export] *)
Definition lo1J : AP.plan :=
  PRun [0x37820] (X44 30 (PRun [0x37840] (X44 6 (PRun [0x37858] (X44 14
    (PRun [P_POPA] (X44 15 (PExt 43 [ELit 15] (PRun [P_N] numtailJ))))))))).
Definition lo0J : AP.plan := PRun [P_POPB] (X44 14 (PExt 43 [ELit 14] (PRun [P_N] numtailJ))).
Definition kJ : AP.plan :=
  PRun [0x37770] (X44 12 (PRun [0x37784] (X44 12 (PRun [0x37798] (X44 8
    (PRun [P_T6] (X44 13 (PBump V_T6 (X44 31 (PCase2 (EVar V_T6) 0 lo0J lo1J)))))))))).

(* [comment removed for export] *)
Definition MR : AP.plan := PRun [P_J] (X44 11 (X44 19 (PMerge 1))).
Definition regpre (k : AP.plan) : AP.plan :=
  PRun [P_SH] (X42 (PRun [P_LD1] (X42 (PRun [P_LD2] (X42 (PRun [P_DIA1] (PDiamond J_DIA1 [19%nat] k))))))).
Definition irrpre (k : AP.plan) : AP.plan :=
  PRun [P_ILD1] (X42 (PRun [P_ILD2] (X42 (PRun [P_IDIA] (PDiamond J_IDIA [19%nat] k))))).
(* [comment removed for export] *)
Definition armReg : AP.plan :=
  PCase2 e_exp 1008 (regpre MR) (PCase2 e_exp 1011 (regpre MR) (PCase2 e_exp 1074 (regpre MR) (PCase2 e_exp 1078 (regpre MR) (regpre MR)))).
Definition armIrr : AP.plan :=
  PCase2 e_exp 1008 (irrpre MR) (PCase2 e_exp 1012 (irrpre MR) (PCase2 e_exp 1075 (irrpre MR) (PCase2 e_exp 1078 (irrpre MR) (irrpre MR)))).

         (* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint decs (ts : list Z) : AP.plan :=
  match ts with [] => MR | t :: r => PCase2 (EVar 48) t MR (decs r) end.
Definition decades : AP.plan :=
  decs [9; 99; 999; 9999; 99999; 999999; 9999999; 99999999; 999999999; 9999999999; 99999999999; 999999999999;
        9999999999999; 99999999999999; 999999999999999].
(* [comment removed for export] *)
Definition subL2 : AP.plan := PRun [P_SUB] (PBump 48 (PFresh 12 0 None (PForget [1%nat] decades))).
Definition subLarge : AP.plan :=
  PRun [P_SDIA] (PBump 46 (X44 13 (PCase2 (EVar 46) (2 ^ 62 - 1) subL2 (PCase2 (EVar 46) (2 ^ 62) subL2 subL2)))).
Definition subSmall : AP.plan :=
  PRun [P_SUB] (PExt 45 [ELit 12; e_x] (PBump 48 (PFresh 12 0 None (PForget [1%nat; 2%nat] decades)))).



(* [comment removed for export] *)
Definition tailH : AP.plan :=
  PBump M (PFresh 10 0 (Some e_buf) (PFact (KRange (EVar M) 0 MMAX) (PHandoffW 0 []))).

(* [comment removed for export] *)
Definition DPS (st : list dstep) : acs := snd (dpath PSEGS IT APLAIN (XN IT NXF) XB0 BFUEL NXF tin (DRun [P_SPEC] :: st) 0).
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

Lemma cert : check PSEGS IT APLAIN NXF LIMIT (XN IT NXF) XE0 XB0 XC0 (HSce ce) 0%nat BFUEL FUEL None (ce_tin ce) plan_wd = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.   (* [comment removed for export] *)
Lemma gplan : gplan_ok plan_wd = true. Proof. vm_compute. reflexivity. Qed.
Lemma hshape : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
