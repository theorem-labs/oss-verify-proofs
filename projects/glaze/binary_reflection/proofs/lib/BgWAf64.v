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
From LinuxProcessSemantics.Riscv Require Import Instr.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC OSSVerify.Proofs.glaze.binary_reflection.lib.BgWDT. Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgWDT.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert OSSVerify.Proofs.glaze.binary_reflection.lib.BgWA. Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPw OSSVerify.Proofs.glaze.binary_reflection.lib.BgWA.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition cfg : acfg :=
  {| c_entry := 0xb3c60; c_ninstr := 602; c_fr := 160; c_K := 8; c_hr := 38; c_wmx := 36;
     c_js0 := 0xb3f00; c_treg := 6; c_vreg := 12;
     c_head := 0xb3f50; c_join1 := 0xb40d4; c_ret := 0xb43dc; c_jreg := 27; c_vol0 := []; c_vol1 := [];
     c_vw := 8; c_vhi := 2 ^ 64 - 1; c_ixpc := 0xb4164; c_ixreg := 10; c_ix2pc := 0xb42e0; c_ix2reg := 10 |}.
Definition CT (id : nat) : option gcallee := if Nat.eqb id 137 then Some BgWDT.ce else None.
Definition XN : nat -> list expr -> acs -> option acs := BgReadCert.BgPw.XNw (XNc BSEGS (BgWA.IT cfg) ABOTH BgWA.NXF GBOTH BCAP CCAP CT).   (* [comment removed for export] *)
Definition BMP : nat := 220.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition wwin (m : smode) : expr := match m with ML => eadd D1 IXv | MS => eadd (eaddz OBJ 1) IXv end.
Definition wfact (m : smode) (k : plan) : plan := PFact (KRange (wwin m) PTRLO (HI47 - c_hr cfg)) k.
Definition elem (m : smode) (k : plan) : plan := wfact m (PRun [] (PBump BMP (PExt 137 [ELit 0; MTR1; e_fb] (PRun [c_ixpc cfg] k)))).   (* [comment removed for export] *)
Definition epaths (m : smode) (d ix mtr : expr) : list (list dstep) :=
  [ [DFact (KRange (eadd d ix) PTRLO (HI47 - c_hr cfg)); DRun []; DExt 137 [ELit 0; mtr; e_fb]; DRun [c_ixpc cfg]] ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ITc : itab := Eval vm_compute in (BgWA.IT cfg).
Lemma IT_eq : BgWA.IT cfg = ITc.   (* [comment removed for export] *)
Proof. vm_cast_no_check (@eq_refl itab ITc). Qed.
Definition SJ0_L : list acs := Eval vm_compute in (S_js0s_I cfg ITc XN ML).
Definition SJ0_S : list acs := Eval vm_compute in (S_js0s_I cfg ITc XN MS).
Definition SJ0 (m : smode) : list acs := match m with ML => SJ0_L | MS => SJ0_S end.
Definition JS0_L : acs := Eval vm_compute in (JS0 cfg SJ0 ML).
Definition JS0_S : acs := Eval vm_compute in (JS0 cfg SJ0 MS).
Definition JS0m (m : smode) : acs := match m with ML => JS0_L | MS => JS0_S end.
Definition SH_L : acs := Eval vm_compute in (S_head_I cfg ITc XN JS0m ML).
Definition SH_S : acs := Eval vm_compute in (S_head_I cfg ITc XN JS0m MS).
Definition SH (m : smode) : acs := match m with ML => SH_L | MS => SH_S end.
Definition SJ1z : acs := Eval vm_compute in (S_j1z_I cfg ITc XN JS0m SH).
Definition SJ2az : acs := Eval vm_compute in (S_j2z_I cfg ITc XN JS0m SH false).
Definition SJ2bz : acs := Eval vm_compute in (S_j2z_I cfg ITc XN JS0m SH true).
Definition SJ2z (g : bool) : acs := if g then SJ2bz else SJ2az.
Definition SH2s : list acs := Eval vm_compute in (S_head2s_I cfg ITc XN epaths JS0m SH SJ1z SJ2z).
Definition INV_L : acs := Eval vm_compute in (INV cfg JS0m SH SH2s ML).
Definition INV_S : acs := Eval vm_compute in (INV cfg JS0m SH SH2s MS).
Definition INVm (m : smode) : acs := match m with ML => INV_L | MS => INV_S end.
Definition SJ1_L : acs := Eval vm_compute in (S_j1_I cfg ITc XN INVm ML).
Definition SJ1_S : acs := Eval vm_compute in (S_j1_I cfg ITc XN INVm MS).
Definition SJ2a : acs := Eval vm_compute in (S_j2_I cfg ITc XN INVm ML false).
Definition SJ2b : acs := Eval vm_compute in (S_j2_I cfg ITc XN INVm ML true).
Definition SJ1 (m : smode) : acs := match m with ML => SJ1_L | MS => SJ1_S end.
Definition SJ2 (m : smode) (g : bool) : acs := match m with ML => if g then SJ2b else SJ2a | MS => SJ1_S end.
Definition JS1_L : acs := Eval vm_compute in (JS1 cfg INVm SJ1 SJ2 ML).
Definition JS1_S : acs := Eval vm_compute in (JS1 cfg INVm SJ1 SJ2 MS).
Definition JS1m (m : smode) : acs := match m with ML => JS1_L | MS => JS1_S end.


#[local] Notation CHK m := (check BSEGS (BgWA.IT cfg) ABOTH BgWA.NXF LIMIT ISP0 XN XE0 BgWA.XB (HSce (BgWA.ce cfg m)) 0%nat BFUEL FUELA None).
#[local] Notation CHK1 := (check BSEGS (BgWA.IT cfg) ABOTH BgWA.NXF LIMIT ISP0 XN XE0 BgWA.XB (HSce (BgWA.ceL1 cfg)) 0%nat BFUEL FUELA None).

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.
