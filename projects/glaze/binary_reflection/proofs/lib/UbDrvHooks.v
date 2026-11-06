(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.MemImageType OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module UbDrvIT.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs.UbImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition DRANGES : list (Z * nat) :=
  [ (0x2eab4, 332%nat)    (* [comment removed for export] *)
  ; (0x65864, 1%nat)      (* [comment removed for export] *)
  ; (0x65c04, 150%nat)    (* [comment removed for export] *)
  ; (0x65e5c, 97%nat)     (* [comment removed for export] *)
  ; (0x66190, 1%nat)      (* [comment removed for export] *)
  ; (0x662d0, 1%nat)      (* [comment removed for export] *)
  ; (0x665b4, 4%nat)      (* [comment removed for export] *)
  ; (0x688d8, 1774%nat)   (* [comment removed for export] *)
  ; (0x6dd08, 7%nat)      (* [comment removed for export] *)
  ; (0x732b0, 257%nat)    (* [comment removed for export] *)
  ; (0x73830, 62%nat)     (* [comment removed for export] *)
  ; (0x73960, 36%nat)     (* [comment removed for export] *)
  ; (0x73b1c, 3%nat)      (* [comment removed for export] *)
  ; (0x73d14, 1%nat)      (* [comment removed for export] *)
  ; (0x73da4, 3%nat)      (* [comment removed for export] *)
  ; (0x73e18, 12%nat)     (* [comment removed for export] *)
  ; (0x74910, 37%nat)     (* [comment removed for export] *)
  ].
Definition ITD : itab := mk_itab_ranges USEGS DRANGES.
Lemma ITD_ok : itab_sound USEGS ITD.
Proof. apply APS.mk_itab_ranges_sound. Qed.
End UbDrvIT.
Require Stdlib.micromega.Lia LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GuFuzzT.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Module FuzzN.
Definition ENTRY : Z := 0x2efe4.
Definition RETPC : Z := 0x2f1f8.
Definition NINSTR : nat := 159%nat.            (* [comment removed for export] *)

Definition SZHI : Z := 2 ^ 26 - 1.
Definition FR : Z := 224.                       (* [comment removed for export] *)
Definition B2JYLO : Z := 57696.                 (* [comment removed for export] *)
Definition YLO : Z := FR + B2JYLO.              (* [comment removed for export] *)

(* [comment removed for export] *)
Definition TP : expr := ELit (g_tp GUBSAN).
Definition DUM : expr := ELit 0.
Definition regsT : list expr := sr_upd regs0 4 TP.    (* [comment removed for export] *)
Definition DATA : expr := EVar 9.      (* [comment removed for export] *)
Definition SIZE : expr := EVar 10.     (* [comment removed for export] *)
Definition NXF : nat := 31.
(* [comment removed for export] *)
Definition SX : expr := eaddz e_sp (-224).    (* [comment removed for export] *)
Definition HV : expr := eaddz e_sp (-160).


      (* [comment removed for export] *)
Definition HEL : expr := eaddz e_sp (-80).    (* [comment removed for export] *)

(* [comment removed for export] *)
Definition newh_facts : list kentry := [].

Definition kn_base : list kentry :=
  [ KRange SIZE 1 SZHI; KRange (eaddz (escale 2 SIZE) (-2)) 0 (2 * SZHI - 2);   (* [comment removed for export] *)
    KRange DATA PTRLO (PTRHI - 1); KRange (eadd DATA SIZE) (PTRLO + 1) PTRHI; KAlign DATA 16;
    KWr (SA DATA 0) SIZE; KUnk (SA DATA 0) SIZE;
    KAlign e_sp 16; KRange e_sp (CEIL + YLO) HI47; KWr (SA e_sp (- YLO)) (ELit YLO);
    KDisj (SA DATA 0) SIZE (SA e_sp (- YLO)) (ELit (YLO + WSTK));                (* [comment removed for export] *)
    img_apart DATA 0 SIZE ]                                                     (* [comment removed for export] *)
  ++ newh_facts ++ [ KImg 0x10000 0x75000 ].
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
  [ KRange SIZE 0 0; KRange DATA 1 CEIL;      (* [comment removed for export] *)
    KAlign e_sp 16; KRange e_sp (CEIL + YLO) HI47; KWr (SA e_sp (- YLO)) (ELit YLO) ]
  ++ newh_facts ++ [ KImg 0x10000 0x75000 ].
Definition kn_fixed : list kentry := kn_base ++ [ KUnk (SA e_sp (- YLO)) (ELit YLO) ].
Definition tin : acs := mkcs ENTRY regsT kn_fixed NXF [].
Definition tout : acs := mkcs RETPC regs_out kn_base (XLO + 14)%nat [].
Definition BCAP : Z := 2 ^ 30.
Definition CCAP : Z := 10.
Definition ce : gcallee := GCE NXF tin [tout] BCAP CCAP.
End FuzzE.
End GuFuzzT.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs.UbImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan GuFuzzT UbDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.UbDrvNodes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
Abbreviation GDRV := GUBSAN.
Abbreviation ADRV := AUBSAN.
Definition IMG_LO : Z := 0x10000.
Definition IMG_SZ : Z := 0x9c000.

(* [comment removed for export] *)
Definition P_TR_LOOP : Z := 0x2eecc.      (* [comment removed for export] *)
Definition P_TR_AFTERM : Z := 0x2ee78.    (* [comment removed for export] *)
Definition P_FZ : Z := 0x2efe4.
       (* [comment removed for export] *)
Definition P_STDIO_WRITE : Z := 0x69010.

Definition P_EXIT : Z := 0x65e50.

Definition P_MALLOC_T : Z := 0x662d0.
Definition P_FREE_T : Z := 0x66190.
Definition P_MEMCPY : Z := 0x732b0.
Definition FILE1 : Z := 0x79ec8.          (* [comment removed for export] *)
Definition FILE2 : Z := 0x79dd8.          (* [comment removed for export] *)
Definition SBUF0 : Z := 0xab260.          (* [comment removed for export] *)
Definition READ_STAGE : Z := 0x7a019.
Definition INIT_BYTE : Z := 0x8a020.


Definition COMPLETED : Z := 0x7a018.      (* [comment removed for export] *)
Definition ATEXIT_LO : Z := 0xaabd8.

Definition ATEXIT_WLEN : Z := 0x224.      (* [comment removed for export] *)
Definition NEWH_GOT : Z := 0x78ca0.
Definition NEWH_CELL : Z := 0x8a050.
Definition ERRNO : Z := 0x8aaec.
Definition TID_CELL : Z := 0x8aae8.
Definition CANARY : Z := 0xaae00.

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
  | 63%nat => DN.node_ioctl USEGS cs
  | _ => XNc USEGS ITD ADRV NXD GDRV BCAP CCAP CT id args cs
  end.
Definition XEt := DN.XEd USEGS NXD.


(* [comment removed for export] *)
Definition CHKf (hs : nat -> option acs) (bf fuel : nat) (cs : acs) (p : plan) : cres :=
  check USEGS ITD ADRV NXD LIMIT XNt XEt XB0 XC0 hs 0%nat bf fuel None cs p.
Definition HS0 (h : nat) : option acs := None.

(* [comment removed for export] *)
Definition hole_of (d : acs) (r : cres) : acs := match r with CErr _ _ cs => cs | COk _ => d end.
