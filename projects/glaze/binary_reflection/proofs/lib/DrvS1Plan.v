(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.DrvHooks OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS3Plan OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS2Plan. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs.RefImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.DrvHooks.GpFuzzT OSSVerify.Proofs.glaze.binary_reflection.lib.DrvHooks.DrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.DrvNodes OSSVerify.Proofs.glaze.binary_reflection.lib.DrvHooks OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS3Plan.DrvHooksS OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS3Plan OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS2Plan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesBlob.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition P_MAIN : Z := 0x2e38c.
Definition P_AFTER_MALLOC1' : Z := 0x2e3e0.
Definition ARGC : expr := EVar 1.
Definition D0 : expr := EVar 2.
Definition L0 : expr := EVar 3.
Definition ENVP : expr := K 16.     (* [comment removed for export] *)
Definition D1 : expr := EVar 5.
Definition L1 : expr := EVar 6.
Definition STR0 : expr := EAlu Instr.ALU_ADD SP0 D0.
Definition STR1 : expr := EAlu Instr.ALU_ADD SP0 D1.
(* [comment removed for export] *)
Definition END0 : expr := EAlu Instr.ALU_ADD SP0 (EAlu Instr.ALU_ADD D0 L0).
Definition END1 : expr := EAlu Instr.ALU_ADD SP0 (EAlu Instr.ALU_ADD D1 L1).

(* [comment removed for export] *)
Definition regsM : list expr :=
  [ELit 0; ELit 0x611f4; SP0; ELit 0x10800; ELit 0x86520;
   K 1; K 2; K 3;
   eaddz SP0 56; ARGC;
   ARGC; eaddz SP0 56; ENVP; K 6; K 7; K 8; K 9; K 10;
   ELit 0x2e38c; ENVP; ELit 0; ELit 0; ELit 0; ELit 0;
   ELit 0; ELit 0; ELit 0; ELit 0;
   K 12; K 13; K 14; K 15].
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition KIMG_M : list kentry :=
  [KImg 0x10000 0x75960; KImg 0x75961 0x859e8; KImg 0x8647c 0x86480; KImg 0xa6564 0xa6788; KImg 0xa6788 0xa6790; KImg 0xa6798 0xa67a0;   (* [comment removed for export] *)
   KImg 0xa67b1 0xa67b8; KImg 0xa67c0 0xa67c8; KImg 0xa67d8 0xa67e0; KImg 0xa67e8 0xa6818; KImg 0xa6820 0xa6bd0; KImg 0xa6bd0 0xa7000;
   KImg 0x10000 0x71000].
Definition knM : list kentry :=
  [ KRange SP0 (CEIL + YLO) (HI47 - 48); KAlign SP0 16; KRange TID 1 4194303;
    KRange ARGC 1 1024; KRange D0 64 4194304; KRange L0 0 131071;
    KWord (SA SP0 48) 8 ARGC; KWord (SA SP0 56) 8 STR0;
    KWord (SA END0 0) 1 (ELit 0); KBlob (SA STR0 0) L0 1;
    KWord (SA (ELit 0) TID_CELL) 4 TID; KWord (SA (ELit 0) CANARY) 8 CAN;
    KWord (SA (ELit 0) NEWH_GOT) 8 (ELit NEWH_CELL);
    KWr (SA SP0 (- YLO)) (ELit YLO); KUnk (SA SP0 (- YLO)) (ELit YLO);
    KWr (SA (ELit 0) FILE1) (ELit 232); KWr (SA (ELit 0) FILE2) (ELit 232); KWr (SA (ELit 0) SBUF0) (ELit 0x408);
    KWr (SA (ELit 0) INIT_BYTE) (ELit 8); KWr (SA (ELit 0) NEWH_CELL) (ELit 8);
    KWr (SA (ELit 0) COMPLETED) (ELit 1); KWr (SA (ELit 0) ATEXIT_LO) (ELit ATEXIT_WLEN) ]     (* [comment removed for export] *)
  ++ KIMG_M.
Definition mkM (p : Z) (regs : list expr) (k : list kentry) : acs := ACS (mk_ss p regs k 29%nat) [] 0 YLO 0 [] PERM_T 0 (eaddz SP0 0) FdStd false.
Definition tM : acs := mkM P_MAIN regsM knM.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition END1' : expr := EAlu Instr.ALU_ADD STR1 L1.
Definition knO : list kentry :=
  [KRange ARGC 2 2; KRange D1 64 4194304; KRange L1 0 131071; KWord (SA SP0 64) 8 STR1; KWord (SA END1 0) 1 (ELit 0); KBlob (SA STR1 0) L1 2;
   KRange END1' 0 (HI47 - 9);                                  (* [comment removed for export] *)
   KUnk (SA STR1 0) (EAlu Instr.ALU_ADD L1 (ELit 8))].        (* [comment removed for export] *)
Definition tMo : acs := add_kn tM knO.

(* [comment removed for export] *)
Definition XNd (id : nat) (args : list expr) (cs : acs) : option acs :=
  match id with
  | 63%nat => DN.node_ioctl PSEGS cs
  | 1%nat => node_memcpy PSEGS ADRV NXD GDRV cs
  | 5%nat => GNB.node_memcpy_blob ADRV NXD GDRV cs
  | _ => None
  end.
Definition CHKd (hs : nat -> option acs) (bf fuel : nat) (cs : acs) (p : plan) : cres :=
  check PSEGS ITD ADRV NXD LIMIT XNd XEs XB0 XC0 hs 0%nat bf fuel None cs p.

(* [comment removed for export] *)
Definition SO : list Z := [P_ECALL; P_MALLOC_T; P_STDIO_WRITE; P_EXIT; P_MEMCPY].
Definition planH : plan := PRun SO (PHandoffW 1 []).
(* [comment removed for export] *)
Definition hOPEN : acs := hole_of tMo (CHKd HS0 BF FUEL tMo planH).
Lemma certO : CHKd (HSof1 hOPEN) BF FUEL tMo planH = COk (SHole 1). Proof. match goal with |- @eq ?A ?l ?r => vm_cast_no_check (@eq_refl A r) end. Qed.
(* [comment removed for export] *)
Definition tAO : acs := set_pc (set_reg hOPEN 10 (ELit 3)) P_AFTER_ECALL.
Definition hM1 : acs := hole_of tAO (CHKd HS0 BF FUEL tAO planH).
Lemma certAO : CHKd (HSof1 hM1) BF FUEL tAO planH = COk (SHole 1). Proof. match goal with |- @eq ?A ?l ?r => vm_cast_no_check (@eq_refl A r) end. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hN1 : acs := match node_alloc NXD GDRV BCAP CCAP P_MALLOC_T hM1 return acs with Some c => c | None => hM1 end.
Lemma hM1_call_ok : call_ok NXD GDRV P_MALLOC_T hM1 = Some P_AFTER_MALLOC1'. Proof. match goal with |- @eq ?A ?l ?r => vm_cast_no_check (@eq_refl A r) end. Qed.
Lemma hM1_alloc : node_alloc NXD GDRV BCAP CCAP P_MALLOC_T hM1 = Some hN1. Proof. match goal with |- @eq ?A ?l ?r => vm_cast_no_check (@eq_refl A r) end. Qed.

Lemma hM1_parts : reg hM1 10 = ELit 65536 /\ reg hM1 2 = eaddz SP0 (-80) /\ a_vis hM1 = [] /\ reg hM1 1 = ELit P_AFTER_MALLOC1'.
Proof. vm_compute. repeat split; reflexivity. Qed.
(* [comment removed for export] *)
Definition ENT29 (h T : acs) (w : tbind) : bool := entails_tw ADRV 0 29 w h T.
Definition TH29 (h T : acs) (w : tbind) : list expr := infer_th 0 29 w h T.
Lemma entN1 : ENT29 hN1 tR0 [] = true. Proof. match goal with |- @eq ?A ?l ?r => vm_cast_no_check (@eq_refl A r) end. Qed.
Lemma thN1 : nth_error (TH29 hN1 tR0 []) 4 = Some FLEN /\ nth_error (TH29 hN1 tR0 []) 0 = Some SP0. Proof. vm_compute. split; reflexivity. Qed.


