(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.MemImageType OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvHooks OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module UbDrvHooksS.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs.UbImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvHooks.UbDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.UbDrvNodes OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvHooks.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition MMAP_TH : Z := 131052.
Definition XNs (id : nat) (args : list expr) (cs : acs) : option acs :=
  match id with
  | 63%nat => DN.node_ioctl USEGS cs
  | 1%nat => node_memcpy USEGS ADRV NXD GDRV cs
  | 11%nat => node_free NXD GDRV cs
  | 13%nat => match args with
             | [ELit nmin] => if Z.leb MMAP_TH nmin then node_malloc1 NXD GDRV BCAP CCAP args cs else None
             | _ => None
             end
  | _ => None
  end.
(* [comment removed for export] *)
Definition XCs (id : nat) (args : list expr) (cs : acs) : option (acs * acs) := None.
Definition XEs := DN.XEd USEGS NXD.

Definition CHKs (hs : nat -> option acs) (bf fuel : nat) (cs : acs) (p : plan) : cres :=
  check USEGS ITD ADRV NXD LIMIT XNs XEs XB0 XCs hs 0%nat bf fuel None cs p.
End UbDrvHooksS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvHooks OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs.UbImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvHooks.GuFuzzT OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvHooks.UbDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.UbDrvNodes OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvHooks.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition P_AFTER_CLOSE : Z := 0x2ec40.

(* [comment removed for export] *)
Definition regsC : list expr :=
  [ELit 0; K 0; eaddz SP0 (-80); ELit 0x10800; ELit 0x8ab90;
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
Definition KIMG_C : list kentry :=
  [KImg 0x10000 0x79fd0; KImg 0x79fd1 0x7a019; KImg 0x8a019 0x8a058; KImg 0xaabd4 0xaadf8; KImg 0xaadf8 0xaae00; KImg 0xaae08 0xaae10;   (* [comment removed for export] *)
   KImg 0xaae21 0xaae28; KImg 0xaae30 0xaae38; KImg 0xaae48 0xaae50; KImg 0xaae58 0xaae88; KImg 0xab240 0xac000; KImg 0x10000 0x75000].
(* [comment removed for export] *)
Definition knC : list kentry :=
  [ KRange SP0 (CEIL + YLO) (HI47 - 48); KAlign SP0 16;
    KRange LEN 0 (2 ^ 26 - 1); KRange CAP 65536 (2 ^ 26); KRange (esub CAP LEN) 0 (2 ^ 26); KRange CFGX 0 32767;
    KRange B0 0 255; KRange B1 0 255; KRange B2 0 255; KRange B1S 0 (2 ^ 64 - 1); KRange TID 1 4194303;
    KWord (SA BUF 0) 1 B0; KWord (SA BUF 1) 1 B1; KWord (SA BUF 2) 1 B2;
    KWord (SA (ELit 0) TID_CELL) 4 TID; KWord (SA (ELit 0) CANARY) 8 CAN;
    KWord (SA (ELit 0) NEWH_GOT) 8 (ELit NEWH_CELL);
    KWr (SA (ELit 0) READ_STAGE) (ELit 65536);     (* [comment removed for export] *)
    KWr (SA SP0 (- YLO)) (ELit YLO); KUnk (SA SP0 (- YLO)) (ELit YLO);
    KWord (SA SP0 (-8)) 8 (ELit 0x65864);
    KWr (SA (ELit 0) FILE1) (ELit 232); KWr (SA (ELit 0) FILE2) (ELit 232); KWr (SA (ELit 0) SBUF0) (ELit 0x408);
    KWr (SA (ELit 0) INIT_BYTE) (ELit 8); KWr (SA (ELit 0) NEWH_CELL) (ELit 8);
    KWr (SA (ELit 0) COMPLETED) (ELit 1); KWr (SA (ELit 0) ATEXIT_LO) (ELit ATEXIT_WLEN) ]     (* [comment removed for export] *)
  ++ heapT BUF CAP 65536 ++ KIMG_C.
Definition tinC : acs := mkT P_AFTER_CLOSE regsC knC NXC [(BUF, CAP)].
(* [comment removed for export] *)
Definition tinC3 : acs := add_kn tinC [KRange LEN 6 (2 ^ 26 - 1); KRange PAYX 0 (2 ^ 26)].

(* [comment removed for export] *)
Definition S3 : list Z := [P_TR_LOOP; P_MALLOC_T; P_STDIO_WRITE; P_FREE_T; P_EXIT].
Definition planC3 : plan :=
  PRun S3 (PSplit CFGX 0
    (PRun S3 (PSplit PAYX 0 (PRun S3 (PHandoffW 1 [])) (PRun S3 (PHandoffW 2 []))))
    (PRun S3 (PFact (KRange CALLSB 1 4) (PSplit PAYX 0 (PRun S3 (PHandoffW 3 [])) (PRun S3 (PHandoffW 4 [])))))).

(* [comment removed for export] *)
Definition CHKS (hs : nat -> option acs) : acs -> plan -> cres := CHKf hs BF FUEL.
Definition holeEA : acs := hole_of tinC (CHKS HS0 tinC3 planC3).
Definition HS1 (h : nat) : option acs := match h with 1%nat => Some holeEA | _ => None end.
Definition holePA : acs := hole_of tinC (CHKS HS1 tinC3 planC3).
Definition HS2 (h : nat) : option acs := match h with 1%nat => Some holeEA | 2%nat => Some holePA | _ => None end.
Definition holeEB : acs := hole_of tinC (CHKS HS2 tinC3 planC3).
Definition HS3 (h : nat) : option acs := match h with 1%nat => Some holeEA | 2%nat => Some holePA | 3%nat => Some holeEB | _ => None end.
Definition holePB : acs := hole_of tinC (CHKS HS3 tinC3 planC3).
Definition HSC (h : nat) : option acs :=
  match h with 1%nat => Some holeEA | 2%nat => Some holePA | 3%nat => Some holeEB | 4%nat => Some holePB | _ => None end.

Definition shapeC3 : shape := SCase CFGX 0 (SCase PAYX 0 (SHole 1) (SHole 2)) (SCase PAYX 0 (SHole 3) (SHole 4)).

Lemma planC3_ok : GPS.gplan_ok planC3 = true. Proof. reflexivity. Qed.


(* [comment removed for export] *)
Definition kvars (K : kentry) : list nat :=
  match K with
  | KWord a _ v => expr_vars (a_base a) (expr_vars v [])
  | KZero a n | KBlob a n _ | KWr a n | KFill a n _ | KUnk a n => expr_vars (a_base a) (expr_vars n [])
  | KImg _ _ => []
  | KAlign e _ => expr_vars e []
  | KRange e _ _ => expr_vars e []
  | KDisj a1 n1 a2 n2 => expr_vars (a_base a1) (expr_vars n1 (expr_vars (a_base a2) (expr_vars n2 [])))
  end.
Definition mentions456 (K : kentry) : bool := existsb (fun v => Nat.eqb v 4 || Nat.eqb v 5 || Nat.eqb v 6)%bool (kvars K).
Definition tinC1n : acs := add_kn (set_kn tinC (filter (fun K => negb (mentions456 K)) (kn tinC))) [KRange LEN 0 5].
(* [comment removed for export] *)
Definition OVX : expr := esub (eadd CFGX (ELit 5)) LEN.
Definition tinC2 : acs := add_kn tinC [KRange LEN 6 (2 ^ 26 - 1); KRange OVX 0 32767].
Definition planD : plan := PRun S3 (PEmit 64 [] (PRun S3 (PExt 11 [] (PRun S3 (PEmit 65 [] PExit))))).
Definition shapeD (msg : list Z) : shape := SEmitP 2 [SPLit msg] (SEmitP 1 [] (SExit 2)).
Definition zmsg_short : list Z := [99; 108; 105; 58; 32; 105; 110; 112; 117; 116; 32; 115; 104; 111; 114; 116; 101; 114; 32; 116; 104; 97; 110; 32; 104; 101; 97; 100; 101; 114; 10].
Definition zmsg_overrun : list Z := [99; 108; 105; 58; 32; 99; 111; 110; 102; 105; 103; 95; 108; 101; 110; 32; 111; 118; 101; 114; 114; 117; 110; 115; 32; 105; 110; 112; 117; 116; 10].
