(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.MemImageType OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module DrvIT.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs.RefImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition DRANGES : list (Z * nat) :=
  [ (0x2e2fc, 332%nat)    (* [comment removed for export] *)
  ; (0x611f4, 1%nat)      (* [comment removed for export] *)
  ; (0x61594, 150%nat)    (* [comment removed for export] *)
  ; (0x617ec, 97%nat)     (* [comment removed for export] *)
  ; (0x61b20, 1%nat)      (* [comment removed for export] *)
  ; (0x61c60, 1%nat)      (* [comment removed for export] *)
  ; (0x61f44, 4%nat)      (* [comment removed for export] *)
  ; (0x64268, 1774%nat)   (* [comment removed for export] *)
  ; (0x69698, 7%nat)      (* [comment removed for export] *)
  ; (0x6ec40, 257%nat)    (* [comment removed for export] *)
  ; (0x6f1c0, 62%nat)     (* [comment removed for export] *)
  ; (0x6f2f0, 36%nat)     (* [comment removed for export] *)
  ; (0x6f4ac, 3%nat)      (* [comment removed for export] *)
  ; (0x6f6a4, 1%nat)      (* [comment removed for export] *)
  ; (0x6f734, 3%nat)      (* [comment removed for export] *)
  ; (0x6f7a8, 12%nat)     (* [comment removed for export] *)
  ; (0x702a0, 37%nat)     (* [comment removed for export] *)
  ].
Definition ITD : itab := mk_itab_ranges PSEGS DRANGES.
Lemma ITD_ok : itab_sound PSEGS ITD.
Proof. apply APS.mk_itab_ranges_sound. Qed.
End DrvIT.
Require Stdlib.micromega.Lia LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GpCommon.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GpFuzzT.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GpCommon.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Module FuzzN.
Definition ENTRY : Z := 0x2e82c.
Definition RETPC : Z := 0x2e9c4.
Definition NINSTR : nat := 117%nat.            (* [comment removed for export] *)

Definition SZHI : Z := 2 ^ 26 - 1.
Definition FR : Z := 176.                       (* [comment removed for export] *)
Definition B2JYLO : Z := 57696.                 (* [comment removed for export] *)
Definition YLO : Z := FR + B2JYLO.              (* [comment removed for export] *)

(* [comment removed for export] *)
Definition TP : expr := ELit (g_tp GPLAIN).
Definition DUM : expr := ELit 0.
Definition regsT : list expr := sr_upd regs0 4 TP.    (* [comment removed for export] *)
Definition DATA : expr := EVar 9.      (* [comment removed for export] *)
Definition SIZE : expr := EVar 10.     (* [comment removed for export] *)
Definition NXF : nat := 31.


     (* [comment removed for export] *)
Definition HEL : expr := eaddz e_sp (-96).    (* [comment removed for export] *)

(* [comment removed for export] *)
Definition newh_facts : list kentry := [].

Definition kn_base : list kentry :=
  [ KRange SIZE 1 SZHI; KRange (eaddz (escale 2 SIZE) (-2)) 0 (2 * SZHI - 2);   (* [comment removed for export] *)
    KRange DATA PTRLO (PTRHI - 1); KRange (eadd DATA SIZE) (PTRLO + 1) PTRHI; KAlign DATA 16;
    KWr (SA DATA 0) SIZE; KUnk (SA DATA 0) SIZE;
    KAlign e_sp 16; KRange e_sp (CEIL + YLO) HI47; KWr (SA e_sp (- YLO)) (ELit YLO);
    KDisj (SA DATA 0) SIZE (SA e_sp (- YLO)) (ELit (YLO + WSTK));                (* [comment removed for export] *)
    img_apart DATA 0 SIZE ]                                                     (* [comment removed for export] *)
  ++ newh_facts ++ [ KImg 0x10000 0x71000 ].
(* [comment removed for export] *)
Definition kn_fixed : list kentry := kn_base ++ [ KUnk (SA e_sp (- YLO)) (ELit YLO) ].
Definition mkcs (p : Z) (regs : list expr) (k : list kentry) (nx : nat) (vis : list (expr * expr)) : acs :=
  ACS (mk_ss p regs k nx) [] 0 YLO 0 vis [] 0 e_sp FdStd false.
Definition tin : acs := mkcs ENTRY regsT kn_fixed NXF [(DATA, SIZE)].

(* [comment removed for export] *)
Definition XLO : nat := 31.
Definition clobbered : list nat := [5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
Definition regs_out : list expr := sr_havoc (sr_upd regsT 10 (ELit 0)) clobbered XLO.
Definition tout : acs := mkcs RETPC regs_out kn_base (XLO + 14)%nat [(DATA, SIZE)].
Definition BCAP : Z := 11 * 2 ^ 30.
Definition CCAP : Z := 12.
Definition ce : gcallee := GCE NXF tin [tout] BCAP CCAP.
End FuzzN.

Module FuzzE.
Import FuzzN.
Definition kn_base : list kentry :=
  [ KRange SIZE 0 0;
    KAlign e_sp 16; KRange e_sp (CEIL + YLO) HI47; KWr (SA e_sp (- YLO)) (ELit YLO) ]
  ++ newh_facts ++ [ KImg 0x10000 0x71000 ].
Definition kn_fixed : list kentry := kn_base ++ [ KUnk (SA e_sp (- YLO)) (ELit YLO) ].
Definition tin : acs := mkcs ENTRY regsT kn_fixed NXF [].
Definition tout : acs := mkcs RETPC regs_out kn_base (XLO + 14)%nat [].
Definition BCAP : Z := 2 ^ 30.
Definition CCAP : Z := 10.
Definition ce : gcallee := GCE NXF tin [tout] BCAP CCAP.
End FuzzE.
End GpFuzzT.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs.RefImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain GpFuzzT DrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.DrvNodes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
Abbreviation GDRV := GPLAIN.
Abbreviation ADRV := APLAIN.
Definition IMG_LO : Z := 0x10000.
Definition IMG_SZ : Z := 0x97000.

(* [comment removed for export] *)
Definition P_TR_LOOP : Z := 0x2e714.      (* [comment removed for export] *)
Definition P_TR_AFTERM : Z := 0x2e6c0.    (* [comment removed for export] *)
Definition P_FZ : Z := 0x2e82c.
       (* [comment removed for export] *)
Definition P_STDIO_WRITE : Z := 0x649a0.

Definition P_EXIT : Z := 0x617e0.

Definition P_MALLOC_T : Z := 0x61c60.
Definition P_FREE_T : Z := 0x61b20.
Definition P_MEMCPY : Z := 0x6ec40.
Definition FILE1 : Z := 0x75858.          (* [comment removed for export] *)
Definition FILE2 : Z := 0x75768.          (* [comment removed for export] *)
Definition SBUF0 : Z := 0xa6bf0.          (* [comment removed for export] *)
Definition READ_STAGE : Z := 0x759a9.
Definition INIT_BYTE : Z := 0x859b0.


Definition COMPLETED : Z := 0x759a8.      (* [comment removed for export] *)
Definition ATEXIT_LO : Z := 0xa6568.

Definition ATEXIT_WLEN : Z := 0x224.      (* [comment removed for export] *)
Definition NEWH_GOT : Z := 0x74630.
Definition NEWH_CELL : Z := 0x859e0.
Definition ERRNO : Z := 0x8647c.
Definition TID_CELL : Z := 0x86478.
Definition CANARY : Z := 0xa6790.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SP0 : expr := EVar 0.
Definition BUF : expr := EVar 1.
Definition CAP : expr := EVar 2.
Definition LEN : expr := EVar 3.
Definition B0 : expr := EVar 4.
Definition B1 : expr := EVar 5.
Definition B2 : expr := EVar 6.
Definition TID : expr := EVar 7.
Definition CAN : expr := EVar 8.
Definition K (i : nat) : expr := EVar (9 + i)%nat.   (* [comment removed for export] *)
Definition NXD : nat := 9.
Definition NXC : nat := 27.            (* [comment removed for export] *)
Definition YLO : Z := 8388608 - 48.    (* [comment removed for export] *)
Definition BCAP : Z := GBUDGET.
Definition CCAP : Z := GCOUNT.
Definition LIMIT : Z := 2 ^ 34.
Definition FUEL : nat := 2000.
Definition BF : nat := 3000.
Definition M63 : Z := 2 ^ 63 - 1.

(* [comment removed for export] *)
Definition CFGX : expr := EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EExt true 0 1 B1)) (ELit 49)) B0.
Definition PAYX : expr := esub LEN (eadd CFGX (ELit 6)).        (* [comment removed for export] *)
Definition CALLSB : expr := eaddz (EAlu Instr.ALU_AND B2 (ELit 3)) 1.
Definition B1S : expr := EExt true 0 1 B1.


(* [comment removed for export] *)
Definition FW_b : saddr := SA SP0 (- YLO).
Definition FW_n : expr := ELit (YLO + WSTK).
Definition heapT (h L : expr) (Llo : Z) : list kentry :=
  [KRange h PTRLO (PTRHI - Llo); KRange (eadd h L) (PTRLO + Llo) PTRHI; KAlign h 16; KWr (SA h 0) L; KUnk (SA h 0) L;
   KDisj (SA h 0) L FW_b FW_n; KDisj (SA h 0) L (SA (ELit 0) IMG_LO) (ELit IMG_SZ)].

(* [comment removed for export] *)
Definition PERM_T : list (expr * expr) :=
  [(ELit FILE1, ELit 232); (ELit FILE2, ELit 232); (ELit SBUF0, ELit 0x408); (ELit INIT_BYTE, ELit 8); (ELit NEWH_CELL, ELit 8);
   (ELit COMPLETED, ELit 1); (ELit ATEXIT_LO, ELit ATEXIT_WLEN)].

Definition mkT (p : Z) (regs : list expr) (k : list kentry) (nx : nat) (vis : list (expr * expr)) : acs :=
  ACS (mk_ss p regs k nx) [] 0 YLO 0 vis PERM_T 0 (eaddz SP0 0) FdStd false.

(* [comment removed for export] *)
Definition CT (id : nat) : option gcallee :=
  match id with 120%nat => Some FuzzN.ce | 121%nat => Some FuzzE.ce | _ => None end.
Definition XNt (id : nat) (args : list expr) (cs : acs) : option acs :=
  match id with
  | 63%nat => DN.node_ioctl PSEGS cs
  | _ => XNc PSEGS ITD ADRV NXD GDRV BCAP CCAP CT id args cs
  end.
Definition XEt := DN.XEd PSEGS NXD.


(* [comment removed for export] *)
Definition CHKf (hs : nat -> option acs) (bf fuel : nat) (cs : acs) (p : plan) : cres :=
  check PSEGS ITD ADRV NXD LIMIT XNt XEt XB0 XC0 hs 0%nat bf fuel None cs p.
Definition HS0 (h : nat) : option acs := None.

(* [comment removed for export] *)
Definition hole_of (d : acs) (r : cres) : acs := match r with CErr _ _ cs => cs | COk _ => d end.
