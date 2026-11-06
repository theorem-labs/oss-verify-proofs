(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.AzDev OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.AzDev OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvNodesP OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition P_AFTER_CLOSE : Z := 0x9c6bc.

     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition BUF : expr := EVar 1.
Definition CAP : expr := EVar 2.
Definition LEN : expr := EVar 3.
(* [comment removed for export] *)
Definition B0 : expr := EBlob false 3 0 1.
Definition B1sx : expr := EBlob true 3 1 1.
Definition B2 : expr := EBlob false 3 2 1.
Definition NXC : nat := 27.
Definition MTR : expr := EVar 5.             (* [comment removed for export] *)              (* [comment removed for export] *)
Definition BLEN : expr := K 16.             (* [comment removed for export] *)
Definition M63 : Z := 2 ^ 63 - 1.
(* [comment removed for export] *)
Definition CFGX : expr := EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) B1sx) (ELit 49)) B0.
Definition PAYX : expr := esub LEN (eadd CFGX (ELit 6)).
Definition CALLSB : expr := eaddz (EAlu Instr.ALU_AND B2 (ELit 3)) 1.
Definition B1S : expr := B1sx.

(* [comment removed for export] *)
Definition regsC : list expr :=
  [ELit 0; K 0; eaddz SP0 (-80); ELit GP; ELit TP;
   K 1; K 2; K 3;
   ELit 2;                 (* [comment removed for export] *)
   BUF;                    (* [comment removed for export] *)
   ELit 0; K 4; K 5; K 6; K 7; K 8; K 9; K 10;   (* [comment removed for export] *)
   K 11;                   (* [comment removed for export] *)
   LEN;                    (* [comment removed for export] *)
   ELit 3;                 (* [comment removed for export] *)
   CAP;                    (* [comment removed for export] *)
   ELit READ_STAGE;        (* [comment removed for export] *)
   ELit 0;                 (* [comment removed for export] *)
   ELit 0; ELit 0; ELit 0; ELit 0;
   K 12; K 13; K 14; K 15].

(* [comment removed for export] *)
Definition FW_b : saddr := SA SP0 (- YLO).
Definition FW_n : expr := ELit (YLO + WSTK).
Definition blockA (h L : expr) (Llo : Z) : list kentry :=
  [KRange h 4112 (PTRHI - Llo); KRange (eadd h L) (4112 + Llo) PTRHI; KAlign h 16;
   KWr (SA h 0) L; KUnk (SA h 0) L; KShOk (SA h 0) L;
   KDisj (SA h 0) L FW_b FW_n; KDisj (SA h 0) L (SA (ELit 0) 0x10000) (ELit 0x64d000);
   KDisj (SA h 0) L (SA (ELit 0) SHMAPLO) (ELit SHMAPLEN)]
  ++ map (fun w => KDisj (SA h 0) L (SA (fst w) 0) (snd w)) PERM_A.
(* [comment removed for export] *)
Definition KIMG_C : list kentry := List.filter (fun K : kentry => match K with KImg lo _ => negb (Z.eqb lo READ_STAGE) | _ => true end) KIMG_A.
(* [comment removed for export] *)
Definition knC : list kentry :=
  [ KRange SP0 (CEIL + YLO) (HI47 - 48); KAlign SP0 16;
    KRange MTR 0 DMTRHI; KRange LEN 0 (2 ^ 26 - 1); KRange CAP 65536 (2 ^ 26); KRange (esub CAP LEN) 0 (2 ^ 26); KRange CFGX 0 32767;   (* [comment removed for export] *)
    KRange B0 0 255; KRange B2 0 255; KRange B1S 0 (2 ^ 64 - 1); KRange TID 1 4194303;
    KRange BLEN 3 65536; KBlob (SA BUF 0) BLEN 3;                 (* [comment removed for export] *)
    KWord (SA (ELit 0) TID_CELL) 4 TID; KWord (SA (ELit 0) CANARY) 8 CAN;
    KWr (SA SP0 (- YLO)) (ELit YLO); KUnk (SA SP0 (- YLO)) (ELit YLO); KShOk (SA SP0 (- YLO)) (ELit (YLO + 48));
    KWord (SA SP0 (-8)) 8 (ELit RA_MAIN) ]
  ++ map (fun w => KWr (SA (fst w) 0) (snd w)) PERM_A
  ++ blockA BUF CAP 65536 ++ RTCELLS ++ LOWSH ++ GLZSH ++ KIMG_C.
Definition mkT (p : Z) (regs : list expr) (k : list kentry) (nx : nat) (vis : list (expr * expr)) : acs :=
  ACS (mk_ss p regs k nx) [] 0 YLO 0 vis PERM_A 0 (eaddz SP0 0) FdStd false MTR [] (ELit FMIN).
Definition tinC : acs := mkT P_AFTER_CLOSE regsC knC NXC [(BUF, CAP)].
(* [comment removed for export] *)
Definition tinC3 : acs := add_kn tinC [KRange LEN 6 (2 ^ 26 - 1); KRange PAYX 0 (2 ^ 26)].

(* [comment removed for export] *)
Definition planC3 : plan :=
  R (PSplit CFGX 0
    (R (PSplit PAYX 0 (R (PHandoffW 1 [])) (R (PHandoffW 2 []))))
    (R (PFact (KRange CALLSB 1 4) (PSplit PAYX 0 (R (PHandoffW 3 [])) (R (PHandoffW 4 [])))))).

(* [comment removed for export] *)
Definition CHKS (hs : nat -> option acs) : acs -> plan -> cres := CHKz hs BF FUEL.   (* [comment removed for export] *)
Definition holeEA_def : acs := hole_of tinC (CHKS HS0 tinC3 planC3).
Definition holeEA : acs := Eval vm_compute in holeEA_def.
Definition HS1 (h : nat) : option acs := match h with 1%nat => Some holeEA | _ => None end.
Definition holePA_def : acs := hole_of tinC (CHKS HS1 tinC3 planC3).
Definition holePA : acs := Eval vm_compute in holePA_def.
Definition HS2 (h : nat) : option acs := match h with 1%nat => Some holeEA | 2%nat => Some holePA | _ => None end.
Definition holeEB_def : acs := hole_of tinC (CHKS HS2 tinC3 planC3).
Definition holeEB : acs := Eval vm_compute in holeEB_def.
Definition HS3 (h : nat) : option acs := match h with 1%nat => Some holeEA | 2%nat => Some holePA | 3%nat => Some holeEB | _ => None end.
Definition holePB_def : acs := hole_of tinC (CHKS HS3 tinC3 planC3).
Definition holePB : acs := Eval vm_compute in holePB_def.
Definition HSC (h : nat) : option acs :=
  match h with 1%nat => Some holeEA | 2%nat => Some holePA | 3%nat => Some holeEB | 4%nat => Some holePB | _ => None end.

Definition shapeC3 : shape := SCase CFGX 0 (SCase PAYX 0 (SHole 1) (SHole 2)) (SCase PAYX 0 (SHole 3) (SHole 4)).

(* [comment removed for export] *)
Definition noblob (K : kentry) : bool := match K with KBlob _ _ _ => false | KRange e _ _ => negb (expr_eqb e BLEN) | _ => true end.
Definition tinC1n : acs := add_kn (set_kn tinC (filter noblob (kn tinC))) [KRange LEN 0 5].
(* [comment removed for export] *)
Definition OVX : expr := esub (eadd CFGX (ELit 5)) LEN.
Definition tinC2 : acs := add_kn tinC [KRange LEN 6 (2 ^ 26 - 1); KRange OVX 0 32767].
Definition planD : plan := W (X 11 pEXIT).
Definition shapeD (msg : list Z) : shape := SEmitP 2 [SPLit msg] (SEmitP 1 [] (SExit 2)).
Definition zmsg_short : list Z := [99; 108; 105; 58; 32; 105; 110; 112; 117; 116; 32; 115; 104; 111; 114; 116; 101; 114; 32; 116; 104; 97; 110; 32; 104; 101; 97; 100; 101; 114; 10].
Definition zmsg_overrun : list Z := [99; 108; 105; 58; 32; 99; 111; 110; 102; 105; 103; 95; 108; 101; 110; 32; 111; 118; 101; 114; 114; 117; 110; 115; 32; 105; 110; 112; 117; 116; 10].

(* [comment removed for export] *)
Lemma certC3 : CHKS HSC tinC3 planC3 = COk shapeC3. Proof. vmc. Qed.
Lemma planC3_ok : gplan_ok planC3 = true. Proof. reflexivity. Qed.

Lemma certC1n : CHKS HS0 tinC1n planD = COk (shapeD zmsg_short). Proof. vmc. Qed.
Lemma certC2 : CHKS HS0 tinC2 planD = COk (shapeD zmsg_overrun). Proof. vmc. Qed.
Lemma planD_ok : gplan_ok planD = true. Proof. reflexivity. Qed.
(* [comment removed for export] *)
