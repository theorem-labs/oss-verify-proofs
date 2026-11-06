(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Instr.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert OSSVerify.Proofs.glaze.binary_reflection.lib.BgWN OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC OSSVerify.Proofs.glaze.binary_reflection.lib.BgWDT. Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPw OSSVerify.Proofs.glaze.binary_reflection.lib.BgWN.BgJT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgWDT OSSVerify.Proofs.glaze.binary_reflection.lib.BgWN.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition BU : Z := 0xb9dec.  Definition BI : Z := 0xc4738.
Definition cfg : ncfg := {| n_ninstr := 255; n_K := 8; n_hr := 38; n_wmx := 36; n_vhi := 0; n_join1 := 0x1f4; n_ret := 0x2e4; n_stix := 0x27c; n_ixreg := 10; n_more := [] |}.
Definition CT (id : nat) : option gcallee := if Nat.eqb id 137 then Some BgWDT.ce else None.
Definition XN (B : Z) : nat -> list expr -> acs -> option acs := BgWN.XNg cfg CT B.
Definition BMP : nat := 170.   (* [comment removed for export] *)
Definition wwin (m : smode) : expr := match m with ML => eadd D1 IX | MS => eadd (eaddz OBJ 1) IX end.
Definition elem (m : smode) (k : plan) : plan := PFact (KRange (wwin m) PTRLO (HI47 - 38)) (PRun [] (PBump BMP (PExt 137 [ELit 0; MTR1; e_fb] k))).   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition RM : list expr := Eval vm_compute in BgWN.RM cfg BU (XN BU).
Definition FW : list kentry := Eval vm_compute in BgWN.FW cfg BU (XN BU).
Definition PLANt (m : smode) (B : Z) : plan := BgWN.PLAN cfg elem RM FW B m.

#[local] Notation CHK m B := (check BSEGS (BgWN.IT cfg B) ABOTH BgWN.NXF LIMIT ISP0 (XN B) XE0 BgWN.XB (HSce (BgWN.ce cfg m B)) 0%nat BFUEL FUEL16 None).
#[local] Notation CHK1 B := (check BSEGS (BgWN.IT cfg B) ABOTH BgWN.NXF LIMIT ISP0 (XN B) XE0 BgWN.XB (HSce (BgWN.ceL1 cfg B)) 0%nat BFUEL FUEL16 None).
(* [comment removed for export] *)
Lemma certU_S : CHK MS BU (BgWN.tin MS BU) (PLANt MS BU) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma certI_S : CHK MS BI (BgWN.tin MS BI) (PLANt MS BI) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma certU_L1 : CHK1 BU (BgWN.tin ML BU) (PLANt ML BU) = COk (SHole 1).   (* [comment removed for export] *)
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma certI_L1 : CHK1 BI (BgWN.tin ML BI) (PLANt ML BI) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
(* [comment removed for export] *)
Lemma gplan : forall m B, gplan_ok (PLANt m B) = true. Proof. intros [|] B; reflexivity. Qed.
Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.
