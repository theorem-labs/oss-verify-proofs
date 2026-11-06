(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.DrvHooks OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS3Plan. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs.RefImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.DrvHooks.GpFuzzT OSSVerify.Proofs.glaze.binary_reflection.lib.DrvHooks.DrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.DrvNodes OSSVerify.Proofs.glaze.binary_reflection.lib.DrvHooks OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS3Plan.DrvHooksS OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS3Plan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition P_ECALL : Z := 0x6f7c4.        (* [comment removed for export] *)
Definition P_AFTER_ECALL : Z := 0x6f7c8.
Definition P_RET_READ : Z := 0x70328.     (* [comment removed for export] *)
Definition P_RET_CLOSE : Z := 0x702cc.    (* [comment removed for export] *)
Definition P_MAIN_AFTER_READ : Z := 0x2e474.
Definition FLEN : expr := EVar 4.         (* [comment removed for export] *)
Definition NXR : nat := 28.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition knS : list kentry :=
  [ KRange SP0 (CEIL + YLO) (HI47 - 48); KAlign SP0 16; KRange TID 1 4194303;
    KWord (SA (ELit 0) TID_CELL) 4 TID; KWord (SA (ELit 0) CANARY) 8 CAN;
    KWord (SA (ELit 0) NEWH_GOT) 8 (ELit NEWH_CELL);
    KWr (SA SP0 (- YLO)) (ELit YLO); KUnk (SA SP0 (- YLO)) (ELit YLO);
    KWord (SA SP0 (-8)) 8 (ELit 0x611f4);
    KWr (SA (ELit 0) FILE1) (ELit 232); KWr (SA (ELit 0) FILE2) (ELit 232); KWr (SA (ELit 0) SBUF0) (ELit 0x408);
    KWr (SA (ELit 0) INIT_BYTE) (ELit 8); KWr (SA (ELit 0) NEWH_CELL) (ELit 8);
    KWr (SA (ELit 0) COMPLETED) (ELit 1); KWr (SA (ELit 0) ATEXIT_LO) (ELit ATEXIT_WLEN) ]     (* [comment removed for export] *)
  ++ KIMG_C.
(* [comment removed for export] *)
Definition knB : list kentry :=
  [ KRange LEN 3 (2 ^ 26 - 1); KRange CAP 65536 (2 ^ 26); KRange (esub CAP LEN) 1 (2 ^ 26);
    KBlob (SA BUF 0) (ELit 3) 7 ] ++ heapT BUF CAP 65536 ++ knS.
(* [comment removed for export] *)
Definition knN : list kentry :=
  [ KRange LEN 1 2; KRange CAP 65536 65536; KRange (esub CAP LEN) 65534 65535 ] ++ heapT BUF CAP 65536 ++ knS.
(* [comment removed for export] *)
Definition kn1 : list kentry := heapT BUF (ELit 65536) 65536 ++ knS.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition regsE (ra : Z) (a0 a1 a2 : expr) (a7 : Z) (s3 s5 s7 : expr) : list expr :=   (* [comment removed for export] *)
  [ELit 0; ELit ra; eaddz SP0 (-96); ELit 0x10800; ELit 0x86520;
   K 1; K 2; K 3;
   ELit 2; BUF;
   a0; a1; a2; ELit 0; ELit 0; ELit 0; ELit 0; ELit a7;
   K 11; s3; ELit 3; s5; ELit READ_STAGE; s7;
   ELit 0; ELit 0; ELit 0; ELit 0;
   K 12; K 13; K 14; K 15].
Definition mkE (p : Z) (regs : list expr) (k : list kentry) (vis : list (expr * expr)) : acs :=
  ACS (mk_ss p regs k NXR) [] 0 YLO 0 vis PERM_T 0 (eaddz SP0 0) FdStd false.
Definition RA_READ : kentry := KWord (SA SP0 (-88)) 8 (ELit P_MAIN_AFTER_READ).

(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive want := WA | WB.
Definition factsW (w : want) : list kentry :=
  match w with
  | WA => [KRange (K 16) 65536 65536; KRange (esub CAP LEN) 65536 (2 ^ 26)]
  | WB => [KRange (esub (K 16) (esub CAP LEN)) 0 0; KRange (esub CAP LEN) 1 65535]
  end.
Definition T_RDb (w : want) : acs := mkE P_ECALL (regsE P_RET_READ (ELit 3) (ELit READ_STAGE) (K 16) 63 LEN CAP (K 17)) (factsW w ++ RA_READ :: knB) [(BUF, CAP)].
Definition T_RDn : acs := mkE P_ECALL (regsE P_RET_READ (ELit 3) (ELit READ_STAGE) (K 16) 63 LEN CAP (K 17)) (factsW WB ++ RA_READ :: knN) [(BUF, CAP)].
Definition T_RD1 : acs := mkE P_ECALL (regsE P_RET_READ (ELit 3) (ELit READ_STAGE) (K 16) 63 (ELit 0) (ELit 65536) BUF) (KRange (K 16) 65536 65536 :: RA_READ :: kn1) [(BUF, ELit 65536)].

(* [comment removed for export] *)
Definition RSBLOB : kentry := KBlob (SA (ELit 0) READ_STAGE) (ELit 3) 7.
Definition RSW : kentry := KWr (SA (ELit 0) READ_STAGE) (ELit 65536).
Definition T_AR (rv : expr) (facts : list kentry) (base : list kentry) (s3 s5 s7 : expr) (vis : list (expr * expr)) : acs :=
  mkE P_AFTER_ECALL (regsE P_RET_READ rv (ELit READ_STAGE) (K 16) 63 s3 s5 s7) (facts ++ RSW :: RA_READ :: base) vis.
(* [comment removed for export] *)
Definition tV0b : acs := T_AR (ELit 0) [] knB LEN CAP (K 17) [(BUF, CAP)].
Definition tVSb : acs := T_AR (esub FLEN LEN) [KRange FLEN 4 (2 ^ 26); KRange (esub FLEN LEN) 1 65535; KRange (esub CAP FLEN) 1 (2 ^ 26)] knB LEN CAP (K 17) [(BUF, CAP)].
Definition tVPb : acs := T_AR (ELit 65536) [KRange (esub CAP LEN) 65537 (2 ^ 26)] knB LEN CAP (K 17) [(BUF, CAP)].
Definition tVFb : acs := T_AR (esub CAP LEN) [KRange (esub CAP LEN) 1 65536; KRange CAP 65536 (2 ^ 25)] knB LEN CAP (K 17) [(BUF, CAP)].
(* [comment removed for export] *)
Definition tVRb : acs := T_AR (esub CAP LEN) [KRange (esub CAP LEN) 1 65536; KRange CAP (2 ^ 26) (2 ^ 26)] knB LEN CAP (K 17) [(BUF, CAP)].
Definition tV0n : acs := T_AR (ELit 0) [] knN LEN CAP (K 17) [(BUF, CAP)].
(* [comment removed for export] *)
Definition tV1_0 : acs := T_AR (ELit 0) [] kn1 (ELit 0) (ELit 65536) BUF [(BUF, ELit 65536)].
Definition tV1_Sn : acs := T_AR FLEN [KRange FLEN 1 2] kn1 (ELit 0) (ELit 65536) BUF [(BUF, ELit 65536)].
Definition tV1_Sb : acs := T_AR FLEN [KRange FLEN 3 65535; RSBLOB] kn1 (ELit 0) (ELit 65536) BUF [(BUF, ELit 65536)].
Definition tV1_F : acs := T_AR (ELit 65536) [RSBLOB] kn1 (ELit 0) (ELit 65536) BUF [(BUF, ELit 65536)].

(* [comment removed for export] *)
Definition SR : list Z := [P_ECALL; P_MEMCPY; P_MALLOC_T; P_FREE_T; P_STDIO_WRITE; P_EXIT; 0x2e424].
(* [comment removed for export] *)
Definition planV0 : plan := PRun SR (PHandoffW 1 []).
(* [comment removed for export] *)
Definition planVS : plan := PRun SR (PExt 1 [] (PRun SR (PBranch (PRun SR (PHandoffW 1 [])) (PRun SR (PHandoffW 2 []))))).
(* [comment removed for export] *)
Definition planVF : plan :=
  PRun SR (PExt 1 [] (PRun SR (PFactR 19 0 65536 (2 ^ 25) (PRun SR
    (PExt 13 [ELit 131052]
       (PRun SR (PExt 1 [] (PRun SR (PExt 11 [] (PRun SR (PHandoffW 1 []))))))))))).
(* [comment removed for export] *)
Definition SR1 : list Z := [P_ECALL; P_MEMCPY; P_MALLOC_T; P_FREE_T; P_STDIO_WRITE; P_EXIT].
Definition planV1F : plan :=
  PRun SR1 (PExt 1 [] (PRun SR1
    (PExt 13 [ELit 131052]
       (PRun SR (PExt 1 [] (PRun SR (PExt 11 [] (PRun SR (PHandoffW 1 []))))))))).
(* [comment removed for export] *)
Definition planV1S : plan := PRun SR (PExt 1 [] (PRun SR (PHandoffW 1 []))).


(* [comment removed for export] *)
Definition CHKR (hs : nat -> option acs) : acs -> plan -> cres := CHKs hs BF FUEL.
Definition HSof1 (a : acs) (h : nat) : option acs := match h with 1%nat => Some a | _ => None end.
Definition HSof2 (a b : acs) (h : nat) : option acs := match h with 1%nat => Some a | 2%nat => Some b | _ => None end.

(* [comment removed for export] *)
Definition hV0b : acs := hole_of tV0b (CHKR HS0 tV0b planV0).
Lemma certV0b : CHKs (HSof1 hV0b) BF FUEL tV0b planV0 = COk (SHole 1). Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Definition hVSb1 : acs := hole_of tVSb (CHKR HS0 tVSb planVS).
Definition hVSb2 : acs := hole_of tVSb (CHKR (HSof1 hVSb1) tVSb planVS).
Lemma certVSb : CHKs (HSof2 hVSb1 hVSb2) BF FUEL tVSb planVS = COk (SHole 1). Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Definition hVPb1 : acs := hole_of tVPb (CHKR HS0 tVPb planVS).
Definition hVPb2 : acs := hole_of tVPb (CHKR (HSof1 hVPb1) tVPb planVS).
Lemma certVPb : CHKs (HSof2 hVPb1 hVPb2) BF FUEL tVPb planVS = COk (SHole 1). Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Definition hVFb : acs := hole_of tVFb (CHKR HS0 tVFb planVF).
Lemma certVFb : CHKs (HSof1 hVFb) BF FUEL tVFb planVF = COk (SHole 1). Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Definition hV0n : acs := hole_of tV0n (CHKR HS0 tV0n planV0).
Lemma certV0n : CHKs (HSof1 hV0n) BF FUEL tV0n planV0 = COk (SHole 1). Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Definition hV1_0 : acs := hole_of tV1_0 (CHKR HS0 tV1_0 planV0).
Lemma certV1_0 : CHKs (HSof1 hV1_0) BF FUEL tV1_0 planV0 = COk (SHole 1). Proof. vm_compute. reflexivity. Qed.
Definition hV1_Sn : acs := hole_of tV1_Sn (CHKR HS0 tV1_Sn planV1S).
Lemma certV1_Sn : CHKs (HSof1 hV1_Sn) BF FUEL tV1_Sn planV1S = COk (SHole 1). Proof. vm_compute. reflexivity. Qed.
Definition hV1_Sb : acs := hole_of tV1_Sb (CHKR HS0 tV1_Sb planV1S).
Lemma certV1_Sb : CHKs (HSof1 hV1_Sb) BF FUEL tV1_Sb planV1S = COk (SHole 1). Proof. vm_compute. reflexivity. Qed.
Definition hV1_F : acs := hole_of tV1_F (CHKR HS0 tV1_F planV1F).
Lemma certV1_F : CHKs (HSof1 hV1_F) BF FUEL tV1_F planV1F = COk (SHole 1). Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition RA_CLOSE : kentry := KWord (SA SP0 (-88)) 8 (ELit P_AFTER_CLOSE).
Definition knNC : list kentry := [ KRange LEN 0 2; KRange CAP 65536 65536 ] ++ heapT BUF CAP 65536 ++ knS.
Definition T_CLb : acs := mkE P_ECALL (regsE P_RET_CLOSE (ELit 3) (ELit 0) (ELit 0) 57 LEN CAP (ELit 0)) (RA_CLOSE :: knB) [(BUF, CAP)].
Definition T_CLn : acs := mkE P_ECALL (regsE P_RET_CLOSE (ELit 3) (ELit 0) (ELit 0) 57 LEN CAP (ELit 0)) (RA_CLOSE :: knNC) [(BUF, CAP)].

(* [comment removed for export] *)
Definition ENT (h T : acs) (w : tbind) : bool := entails_tw ADRV 0 NXR w h T.
Definition TH (h T : acs) (w : tbind) : list expr := infer_th 0 NXR w h T.
(* [comment removed for export] *)
Definition P_AFTER_MALLOC1 : Z := 0x2e3e0.
Definition regsR0 : list expr :=
  [ELit 0; K 0; eaddz SP0 (-80); ELit 0x10800; ELit 0x86520;
   K 1; K 2; K 3;
   ELit 2; K 16;
   BUF; K 4; K 5; K 6; K 7; K 8; K 9; K 10;
   K 11; K 18; ELit 3; ELit 65536; K 19; K 17;
   ELit 0; ELit 0; ELit 0; ELit 0;
   K 12; K 13; K 14; K 15].
Definition tR0 : acs := ACS (mk_ss P_AFTER_MALLOC1 regsR0 kn1 29%nat) [] 0 YLO 0 [(BUF, ELit 65536)] PERM_T 0 (eaddz SP0 0) FdStd false.
Definition planR0 : plan := PRun SR (PHandoffW 1 []).
Definition hR0 : acs := hole_of tR0 (CHKR HS0 tR0 planR0).
Lemma certR0 : CHKs (HSof1 hR0) BF FUEL tR0 planR0 = COk (SHole 1). Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition knHDR : list kentry :=
  [KRange B0 0 255; KRange B1 0 255; KRange B2 0 255; KRange B1S 0 (2 ^ 64 - 1);
   KWord (SA BUF 0) 1 B0; KWord (SA BUF 1) 1 B1; KWord (SA BUF 2) 1 B2].
Definition T_ACL (facts base : list kentry) : acs :=
  mkE P_AFTER_ECALL (regsE P_RET_CLOSE (ELit 0) (ELit 0) (ELit 0) 57 LEN CAP (ELit 0)) (facts ++ knHDR ++ RSW :: RA_CLOSE :: base) [(BUF, CAP)].
(* [comment removed for export] *)
Definition knBC : list kentry := heapT BUF CAP 65536 ++ knS.
Definition tCL1 : acs := mkE P_AFTER_ECALL (regsE P_RET_CLOSE (ELit 0) (ELit 0) (ELit 0) 57 LEN CAP (ELit 0))
  ([KRange LEN 0 5; KRange CAP 65536 (2 ^ 26)] ++ RSW :: RA_CLOSE :: knBC) [(BUF, CAP)].
Definition tCL2 : acs := T_ACL [KRange LEN 6 (2 ^ 26 - 1); KRange OVX 0 32767] knB.
Definition tCL3 : acs := T_ACL [KRange LEN 6 (2 ^ 26 - 1); KRange PAYX 0 (2 ^ 26)] knB.
(* [comment removed for export] *)
Definition planCL : plan :=
  PRun [P_AFTER_CLOSE] (PFact (KRange CFGX 0 32767) (PHandoffW 1 [])).
Definition planCL1 : plan := PRun [P_AFTER_CLOSE] (PHandoffW 1 []).
Lemma certCL1 : CHKs (HSof1 tinC1n) BF FUEL tCL1 planCL1 = COk (SHole 1). Proof. vm_compute. reflexivity. Qed.
Lemma certCL2 : CHKs (HSof1 tinC2) BF FUEL tCL2 planCL = COk (SHole 1). Proof. vm_compute. reflexivity. Qed.
Lemma certCL3 : CHKs (HSof1 tinC3) BF FUEL tCL3 planCL = COk (SHole 1). Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition W1S : tbind := [(2%nat, ELit 65536); (3%nat, FLEN)].
Lemma entR0 : ENT hR0 T_RD1 [] = true. Proof. vm_compute. reflexivity. Qed.
Lemma entV0b : ENT hV0b T_CLb [] = true. Proof. vm_compute. reflexivity. Qed.
Lemma entV0n : ENT hV0n T_CLn [] = true. Proof. vm_compute. reflexivity. Qed.
Lemma entV1_0 : ENT hV1_0 T_CLn [] = true. Proof. vm_compute. reflexivity. Qed.
Lemma entVSb1 : ENT hVSb1 (T_RDb WA) [] = true. Proof. vm_compute. reflexivity. Qed.
Lemma entVSb2 : ENT hVSb2 (T_RDb WB) [] = true. Proof. vm_compute. reflexivity. Qed.
Lemma entVPb1 : ENT hVPb1 (T_RDb WA) [] = true. Proof. vm_compute. reflexivity. Qed.
Lemma entVPb2 : ENT hVPb2 (T_RDb WB) [] = true. Proof. vm_compute. reflexivity. Qed.
Lemma entVFb : ENT hVFb (T_RDb WA) [] = true. Proof. vm_compute. reflexivity. Qed.
Lemma entV1_Sn : ENT hV1_Sn T_RDn W1S = true. Proof. vm_compute. reflexivity. Qed.
Lemma entV1_Sb : ENT hV1_Sb (T_RDb WB) W1S = true. Proof. vm_compute. reflexivity. Qed.
Lemma entV1_F : ENT hV1_F (T_RDb WA) [] = true. Proof. vm_compute. reflexivity. Qed.
