(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr OSSVerify.glaze.binary_reflection.images.AsanUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBoth OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.AzDev OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvS3A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoDrvS1A.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBoth OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.AzDev OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoDrvNodesP OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvS3A.BoDrvS0A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition FLEN : expr := EVar 4.         (* [comment removed for export] *)
Definition FLENHI : Z := 2 ^ 26.
Definition P_ECALL : Z := 0xfcc58.


(* [comment removed for export] *)
Definition tMf : acs := add_kn tMo [KRange L1 1 4095; KRange FLEN 0 FLENHI].

(* [comment removed for export] *)
Definition planF0 : plan := PRun SU (PAlt2 602 [STR1; FLEN] pCO_err (PRun SU (PHandoffW 1 []))).
Definition hM1f_def : acs := hole_of tMf (CHKa HS0 BF FUEL tMf planF0).
Definition hM1f : acs := Eval vm_compute in hM1f_def.
Definition shapeF0 : shape := SAlt2 shapeCOa (SHole 1).

(* [comment removed for export] *)
Definition hN1f_def : acs := match M12 hM1f with Some (_, cb) => cb | None => hM1f end.
Definition hN1f : acs := Eval vm_compute in hN1f_def.
Definition hZ1f_def : acs := match M12 hM1f with Some (ca, _) => ca | None => hM1f end.
Definition hZ1f : acs := Eval vm_compute in hZ1f_def.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hZ1d_def : acs := match M12 hM1d with Some (ca, _) => ca | None => hM1d end.
Definition hZ1d : acs := Eval vm_compute in hZ1d_def.

(* [comment removed for export] *)
Lemma certF0 : CHKz (HSof1 hM1f) BF FUEL tMf planF0 = COk shapeF0.   (* [comment removed for export] *) Proof. vmc. Qed.

(* [comment removed for export] *)
End BoDrvS1A.
Module BoDrvK0A.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBoth OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.AzDev OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoDrvNodesP OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvS3A.BoDrvS0A OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvS3A BoDrvS1A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition PAYXb : expr := esub FLEN (eadd CFGX (ELit 6)).
Definition OVXb : expr := esub (eadd CFGX (ELit 5)) FLEN.

Definition tK0s : acs := add_kn hN1f [KRange FLEN 0 5].
Definition tK0o : acs := add_kn hN1f [KRange FLEN 6 65535; KRange OVXb 0 32767; KRange CFGX 0 32767; KRange B0 0 255; KRange B2 0 255; KRange B1S 0 (2 ^ 64 - 1)].
Definition tK0c : acs := add_kn hN1f [KRange FLEN 6 65535; KRange PAYXb 0 (2 ^ 26); KRange CFGX 0 32767; KRange B0 0 255; KRange B2 0 255; KRange B1S 0 (2 ^ 64 - 1)].

(* [comment removed for export] *)
Definition SUC : list Z := P_AFTER_CLOSE :: SU.
Definition RC (k : plan) : plan := PRun SUC k.
Definition XC (id : nat) (k : plan) : plan := PRun SUC (PExt id [] k).
(* [comment removed for export] *)
Definition pREST (h : nat) : plan := XC 1 (XC 61 (XC 62 (RC (PHandoffW h [])))).
Definition pSHORT (h1 h2 : nat) : plan := PSplit FLEN 64 (pREST h1) (XC 69 (pREST h2)).
(* [comment removed for export] *)
Definition planK0s : plan := RC (PSplit FLEN 0 (XC 61 (XC 62 (RC (PHandoffW 1 [])))) (XC 61 (pSHORT 2 3))).   (* [comment removed for export] *)
Definition planK0 : plan := RC (XC 61 (pSHORT 1 2)).

(* [comment removed for export] *)
Definition HS12 (a b : acs) (h : nat) : option acs := match h with 1%nat => Some a | 2%nat => Some b | _ => None end.
Definition hK0s_def : acs := hole_of tK0s (CHKa HS0 BF FUEL tK0s planK0s).          (* [comment removed for export] *)
Definition hK0s : acs := Eval vm_compute in hK0s_def.
Definition hK0s2_def : acs := hole_of tK0s (CHKa (HSof1 hK0s) BF FUEL tK0s planK0s). (* [comment removed for export] *)
Definition hK0s2 : acs := Eval vm_compute in hK0s2_def.
Definition hK0o_def : acs := hole_of tK0o (CHKa HS0 BF FUEL tK0o planK0).           (* [comment removed for export] *)
Definition hK0o : acs := Eval vm_compute in hK0o_def.
Definition hK0o2_def : acs := hole_of tK0o (CHKa (HSof1 hK0o) BF FUEL tK0o planK0). (* [comment removed for export] *)
Definition hK0o2 : acs := Eval vm_compute in hK0o2_def.
Definition hK0c_def : acs := hole_of tK0c (CHKa HS0 BF FUEL tK0c planK0).
Definition hK0c : acs := Eval vm_compute in hK0c_def.
Definition hK0c2_def : acs := hole_of tK0c (CHKa (HSof1 hK0c) BF FUEL tK0c planK0).
Definition hK0c2 : acs := Eval vm_compute in hK0c2_def.
(* [comment removed for export] *)
Definition ENT (h T : acs) : bool := entails_tw ABOTH 0 NXC [(25%nat, FLEN)] h T.

(* [comment removed for export] *)
Lemma certK0s : CHKz (HS12 hK0s hK0s2) BF FUEL tK0s planK0s = COk (SCase FLEN 0 (SHole 1) (SHole 2)). Proof. vmc. Qed.
Lemma certK0o : CHKz (HS12 hK0o hK0o2) BF FUEL tK0o planK0 = COk (SCase FLEN 64 (SHole 1) (SHole 2)). Proof. vmc. Qed.
Lemma certK0c : CHKz (HS12 hK0c hK0c2) BF FUEL tK0c planK0 = COk (SCase FLEN 64 (SHole 1) (SHole 2)). Proof. vmc. Qed.
(* [comment removed for export] *)
Lemma entK0s : ENT hK0s tinC1n = true. Proof. vmc. Qed.
Lemma entK0s2 : ENT hK0s2 tinC1n = true. Proof. vmc. Qed.
Lemma entK0o : ENT hK0o tinC2 = true. Proof. vmc. Qed.
Lemma entK0o2 : ENT hK0o2 tinC2 = true. Proof. vmc. Qed.
Lemma entK0c : ENT hK0c tinC3 = true. Proof. vmc. Qed.
Lemma entK0c2 : ENT hK0c2 tinC3 = true. Proof. vmc. Qed.
(* [comment removed for export] *)
End BoDrvK0A.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBoth OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.AzDev OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvS3A. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBoth OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.AzDev OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoDrvNodesP OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvS3A.BoDrvS0A OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvS3A BoDrvS1A BoDrvK0A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition NXR : nat := 28.

(* [comment removed for export] *)
Definition tR1F : acs := add_kn hN1f [KRange FLEN 65536 FLENHI].
(* [comment removed for export] *)
Definition planR1F : plan := RC (XC 61 (XC 69 (XC 1 (RC (PHandoffW 1 []))))).
Definition hG1_def : acs := hole_of tR1F (CHKa HS0 BF FUEL tR1F planR1F).
Definition hG1 : acs := Eval vm_compute in hG1_def.
(* [comment removed for export] *)
Lemma certR1F : CHKz (HSof1 hG1) BF FUEL tR1F planR1F = COk (SHole 1).   (* [comment removed for export] *) Proof. vmc. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hG1ok : acs := Eval vm_compute in (match M12 hG1 with Some (_, cb) => cb | None => hG1 end).
Definition hG1z : acs := Eval vm_compute in (match M12 hG1 with Some (ca, _) => ca | None => hG1 end).
(* [comment removed for export] *)
Definition planG : plan := X 1 (X 11 (R (PHandoffW 1 []))).
Definition hRD2_def : acs := hole_of hG1ok (CHKa HS0 BF FUEL hG1ok planG).
Definition hRD2 : acs := Eval vm_compute in hRD2_def.
(* [comment removed for export] *)
Lemma certG1 : CHKz (HSof1 hRD2) BF FUEL hG1ok planG = COk (SHole 1). Proof. vmc. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition RA_ICPT : Z := 0x5ecd0.        (* [comment removed for export] *)
Definition RA_RDMAIN : Z := 0x9d118.      (* [comment removed for export] *)
Definition RA_CP : Z := 0x10179c.          (* [comment removed for export] *)
Definition regsTR : list expr :=
  [ELit 0; ELit RA_CP; eaddz SP0 (-2224); ELit GP; ELit TP;
   K 1; K 2; K 3;
   eaddz SP0 (-80); ELit READ_STAGE;                                  (* [comment removed for export] *)
   ELit 3; ELit READ_STAGE; ELit 65536; ELit 0; ELit 0; ELit 0; ELit 0; ELit 63;   (* [comment removed for export] *)
   ELit 65536; ELit 3; ELit 1; CAP; ELit READ_STAGE; K 4;             (* [comment removed for export] *)
   ELit 0; ELit 0; ELit 0; ELit 0;
   K 12; K 13; K 14; K 15].
(* [comment removed for export] *)
Definition frameTR : list kentry :=
  [KWord (SA SP0 (-2216)) 8 (ELit RA_ICPT); KWord (SA SP0 (-2224)) 8 (eaddz SP0 (-80));
   KWord (SA SP0 (-128)) 8 (ELit 3); KWord (SA SP0 (-120)) 8 LEN; KWord (SA SP0 (-112)) 8 (K 5); KWord (SA SP0 (-104)) 8 BUF;
   KWord (SA SP0 (-96)) 8 (ELit 2); KWord (SA SP0 (-88)) 8 (ELit RA_RDMAIN);
   KWord (SA SP0 (-8)) 8 (ELit RA_MAIN)].
Definition knTR : list kentry :=
  [ KRange SP0 (CEIL + YLO) (HI47 - 48); KAlign SP0 16; KRange TID 1 4194303;
    KRange CAP 131072 (2 ^ 26); KRange LEN 65536 (2 ^ 26 - 65536); KRange (esub CAP LEN) 65536 (2 ^ 26); KRange FLEN 0 FLENHI;
    KRange MTR 0 DMTRHI ] ++ drv_ladder CAP MTR ++ [          (* [comment removed for export] *)
    KWord (SA (ELit 0) TID_CELL) 4 TID; KWord (SA (ELit 0) CANARY) 8 CAN;
    KWr (SA SP0 (- YLO)) (ELit YLO); KUnk (SA SP0 (- YLO)) (ELit YLO); KShOk (SA SP0 (- YLO)) (ELit (YLO + 48));
    KAlign BUF 2048; KBlob (SA BUF 0) (ELit 65536) 3 ]      (* [comment removed for export] *)
  ++ frameTR ++ map (fun w => KWr (SA (fst w) 0) (snd w)) PERM_A
  ++ blockA BUF CAP 131072 ++ RTCELLS ++ LOWSH ++ GLZSH ++ KIMG_C.
Definition mkTR (k : list kentry) : acs :=
  ACS (mk_ss P_ECALL regsTR k NXR) [] 0 YLO 0 [(BUF, CAP)] PERM_A 0 (eaddz SP0 0) (FdFile 3%nat FLEN LEN) false MTR [] (ELit FMIN).
Definition TR : acs := mkTR knTR.
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition REMX : expr := esub FLEN LEN.          (* [comment removed for export] *)
Definition ROOMX : expr := esub CAP LEN.         (* [comment removed for export] *)
(* [comment removed for export] *)
Definition WANT : expr := K 16.                  (* [comment removed for export] *)
Definition regsTRw : list expr := sr_upd (sr_upd regsTR 12 WANT) 18 WANT.
Definition knTRw : list kentry :=
  [ KRange SP0 (CEIL + YLO) (HI47 - 48); KAlign SP0 16; KRange TID 1 4194303;
    KRange CAP 131072 (2 ^ 26); KRange LEN 65536 (2 ^ 26 - 1); KRange ROOMX 1 65535; KRange WANT 1 65535; KRange (esub WANT ROOMX) 0 0; KRange FLEN 0 FLENHI;
    KRange MTR 0 DMTRHI ] ++ drv_ladder CAP MTR ++ [          (* [comment removed for export] *)
    KWord (SA (ELit 0) TID_CELL) 4 TID; KWord (SA (ELit 0) CANARY) 8 CAN;
    KWr (SA SP0 (- YLO)) (ELit YLO); KUnk (SA SP0 (- YLO)) (ELit YLO); KShOk (SA SP0 (- YLO)) (ELit (YLO + 48));
    KAlign BUF 2048; KBlob (SA BUF 0) (ELit 65536) 3 ]
  ++ [KWord (SA SP0 (-2216)) 8 (ELit RA_ICPT); KWord (SA SP0 (-2224)) 8 (eaddz SP0 (-80));
      KWord (SA SP0 (-128)) 8 (ELit 3); KWord (SA SP0 (-120)) 8 LEN; KWord (SA SP0 (-112)) 8 (K 5); KWord (SA SP0 (-104)) 8 BUF;
      KWord (SA SP0 (-96)) 8 (ELit 2); KWord (SA SP0 (-88)) 8 (ELit RA_RDMAIN); KWord (SA SP0 (-8)) 8 (ELit RA_MAIN)]
  ++ map (fun w => KWr (SA (fst w) 0) (snd w)) PERM_A
  ++ blockA BUF CAP 131072 ++ RTCELLS ++ LOWSH ++ GLZSH ++ KIMG_C.
Definition TRw : acs := ACS (mk_ss P_ECALL regsTRw knTRw NXR) [] 0 YLO 0 [(BUF, CAP)] PERM_A 0 (eaddz SP0 0) (FdFile 3%nat FLEN LEN) false MTR [] (ELit FMIN).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition tVP : acs := add_kn TR [KRange REMX 65536 FLENHI; KRange ROOMX 65537 (2 ^ 26)].
Definition planVP : plan := PExt 61 [] (X 69 (X 1 (R (PBranch (R (PHandoffW 1 [])) (R (PHandoffW 2 [])))))).
(* [comment removed for export] *)
Definition LENX' : expr := eaddz LEN 65536.
Definition tVF : acs := add_kn TR [KRange REMX 65536 FLENHI; KRange ROOMX 65536 65536; KRange CAP 131072 (2 ^ 25)].
Definition planVF : plan := PExt 61 [] (X 69 (X 1 (PFactVia LENX' CAP 131072 (2 ^ 25) (R (PHandoffW 1 []))))).
(* [comment removed for export] *)
Definition tVR : acs := add_kn TR [KRange REMX 65536 FLENHI; KRange ROOMX 65536 65536; KRange CAP (2 ^ 26) (2 ^ 26)].
(* [comment removed for export] *)
Definition pRF : plan := X 68 (R (R (X 1 (X 1 (X 1 (X 1 (X 1 (W pEXIT)))))))).
Definition planVR : plan := PExt 61 [] (X 69 (X 1 (PFactVia LENX' CAP (2 ^ 26) (2 ^ 26) pRF))).
Definition MSG_RF : list Z := [99; 108; 105; 58; 32; 105; 110; 112; 117; 116; 32; 62; 61; 32; 54; 55; 49; 48; 56; 56; 54; 52; 32;
                              98; 121; 116; 101; 115; 44; 32; 114; 101; 102; 117; 115; 101; 100; 10].  (* [comment removed for export] *)
Definition shapeRF : shape := SEmitP 2 [SPLit MSG_RF] (SEmitP 1 [] (SExit 2)).
(* [comment removed for export] *)
Definition pSREST (h1 h2 : nat) : plan := XC 1 (RC (PBranch (XC 61 (XC 62 (RC (PHandoffW h1 [])))) (XC 61 (XC 62 (RC (PHandoffW h2 [])))))).
Definition planVS : plan := PExt 61 [] (PSplit REMX 64 (pSREST 1 2) (XC 69 (pSREST 3 4))).
Definition tVS : acs := add_kn TR [KRange REMX 1 65535].
(* [comment removed for export] *)
Definition tV0 : acs := add_kn TR [KRange REMX 0 0].
Definition planV0 : plan := PExt 61 [] (XC 62 (RC (PHandoffW 1 []))).
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition factsC : list kentry := [KRange PAYXb 0 (2 ^ 26); KRange CFGX 0 32767; KRange B0 0 255; KRange B2 0 255; KRange B1S 0 (2 ^ 64 - 1)].
Definition tVSc : acs := add_kn tVS factsC.
Definition tV0c : acs := add_kn tV0 factsC.

(* [comment removed for export] *)
Definition HS4 (a b c d : acs) (h : nat) : option acs := match h with 1%nat => Some a | 2%nat => Some b | 3%nat => Some c | 4%nat => Some d | _ => None end.
Definition CH (hs : nat -> option acs) (t : acs) (p : plan) : cres := CHKz hs BF FUEL t p.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition hVP1 : acs := Eval vm_compute in hole_of tVP (CH HS0 tVP planVP).
Definition hVP2 : acs := Eval vm_compute in hole_of tVP (CH (HSof1 hVP1) tVP planVP).
(* [comment removed for export] *)
Definition hVF : acs := Eval vm_compute in hole_of tVF (CH HS0 tVF planVF).
Definition hVFok : acs := Eval vm_compute in (match M12 hVF with Some (_, cb) => cb | None => hVF end).
Definition hVFz : acs := Eval vm_compute in (match M12 hVF with Some (ca, _) => ca | None => hVF end).
Definition hVG : acs := Eval vm_compute in hole_of hVFok (CH HS0 hVFok planG).
(* [comment removed for export] *)
Definition h4 (t : acs) (p : plan) : acs * acs * acs * acs :=
  let a := hole_of t (CH HS0 t p) in let b := hole_of t (CH (HSof1 a) t p) in
  let c := hole_of t (CH (HS4 a b a a) t p) in let d := hole_of t (CH (HS4 a b c a) t p) in (a, b, c, d).
Definition hVSc : acs * acs * acs * acs := Eval vm_compute in h4 tVSc planVS.
Definition hV0c : acs := Eval vm_compute in hole_of tV0c (CH HS0 tV0c planV0).
Definition HSq (q : acs * acs * acs * acs) : nat -> option acs := let '(a, b, c, d) := q in HS4 a b c d.

(* [comment removed for export] *)
Lemma certVP : CH (HS12 hVP1 hVP2) tVP planVP = COk (SHole 1). Proof. vmc. Qed.
Lemma certVF : CH (HSof1 hVF) tVF planVF = COk (SHole 1). Proof. vmc. Qed.
Lemma certVG : CH (HSof1 hVG) hVFok planG = COk (SHole 1). Proof. vmc. Qed.
Lemma certVR : CH HS0 tVR planVR = COk shapeRF. Proof. vmc. Qed.
Lemma certVSc : CH (HSq hVSc) tVSc planVS = COk (SCase REMX 64 (SHole 1) (SHole 3)). Proof. vmc. Qed.
Lemma certV0c : CH (HSof1 hV0c) tV0c planV0 = COk (SHole 1). Proof. vmc. Qed.
(* [comment removed for export] *)
Definition ENTR (h T : acs) : bool := entails_tw ABOTH 0 NXR [] h T.   (* [comment removed for export] *)
Lemma entVP1 : ENTR hVP1 TR = true. Proof. vmc. Qed.
Lemma entVP2 : ENTR hVP2 TRw = true. Proof. vmc. Qed.
Lemma entVG : ENTR hVG TR = true. Proof. vmc. Qed.
Lemma entG1 : ENTR hRD2 TR = true. Proof. vmc. Qed.      (* [comment removed for export] *)
Definition ENTC (h T : acs) : bool := entails_tw ABOTH 0 NXC [(25%nat, ELit 65536)] h T.   (* [comment removed for export] *)
Lemma entVSc : let '(a, b, c, d) := hVSc in (ENTC a tinC3 && ENTC b tinC3 && ENTC c tinC3 && ENTC d tinC3)%bool = true. Proof. vmc. Qed.
Lemma entV0c : ENTC hV0c tinC3 = true. Proof. vmc. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
