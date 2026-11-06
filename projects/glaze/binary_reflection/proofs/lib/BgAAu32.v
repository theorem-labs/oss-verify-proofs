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
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC OSSVerify.Proofs.glaze.binary_reflection.lib.BgU32. Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgU32.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert OSSVerify.Proofs.glaze.binary_reflection.lib.BgAA. Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPw OSSVerify.Proofs.glaze.binary_reflection.lib.BgAA.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition cfg : acfg :=
  {| c_entry := 0xb267c; c_ninstr := 398; c_fr := 192; c_K := 4; c_hr := 16; c_wmx := 10;
     c_head := 0xb2770; c_join1 := 0xb28d0; c_ret := 0xb2bb8; c_jreg := 20; c_vol0 := []; c_vol1 := [];
     c_vw := 4; c_vhi := 0; c_ixpc := 0xb28e8; c_ixreg := 10; c_ix2pc := 0xb2aac; c_ix2reg := 10 |}.
Definition CT (id : nat) : option gcallee := if Nat.eqb id 133 then Some BgU32.ce else if Nat.eqb id 143 then Some BgU32.ceS else None.
Definition XN : nat -> list expr -> acs -> option acs := BgReadCert.BgPw.XNw (XNc BSEGS (BgAA.IT cfg) ABOTH BgAA.NXF GBOTH BCAP CCAP CT).   (* [comment removed for export] *)
Definition BMP : nat := 200.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition wwin (m : smode) : expr := match m with ML => eadd D1 IXv | MS => eadd (eaddz OBJ 1) IXv end.
Definition wfact (m : smode) (k : plan) : plan := PFact (KRange (wwin m) PTRLO (HI47 - c_hr cfg)) k.
Definition elem (m : smode) (k : plan) : plan :=
  wfact m (PRun [] (PBump BMP (match m with ML => PExt 133 [VAL; A1; S1; D1; IXv; MTR1; e_fb] k | MS => PExt 143 [VAL; ELit 0; S1; ELit 0; IXv; MTR1; e_fb] k end))).
Definition epaths (m : smode) (d ix mtr : expr) : list (list dstep) :=        (* [comment removed for export] *)
  [ [DFact (KRange (eadd d ix) PTRLO (HI47 - c_hr cfg)); DRun []; DExtA 133 [] C 56 (c_vw cfg) [A1; S1; D1; IXv; MTR1; e_fb]] ].   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ITc : itab := Eval vm_compute in (BgAA.IT cfg).
Lemma IT_eq : BgAA.IT cfg = ITc.   (* [comment removed for export] *)
Proof. vm_cast_no_check (@eq_refl itab ITc). Qed.
Definition SH_L : acs := Eval vm_compute in (S_head_I cfg ITc XN ML).
Definition SH_S : acs := Eval vm_compute in (S_head_I cfg ITc XN MS).
Definition SH (m : smode) : acs := match m with ML => SH_L | MS => SH_S end.
Definition SJ1z : acs := Eval vm_compute in (S_j1z_I cfg ITc XN SH).
Definition SJ2az : acs := Eval vm_compute in (S_j2z_I cfg ITc XN SH false).
Definition SJ2bz : acs := Eval vm_compute in (S_j2z_I cfg ITc XN SH true).
Definition SJ2z (g : bool) : acs := if g then SJ2bz else SJ2az.
Definition SH2s : list acs := Eval vm_compute in (S_head2s_I cfg ITc XN epaths SH SJ1z SJ2z).
Definition INV_L : acs := Eval vm_compute in (INV cfg SH SH2s ML).
Definition INV_S : acs := Eval vm_compute in (INV cfg SH SH2s MS).
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


#[local] Notation CHK m := (check BSEGS (BgAA.IT cfg) ABOTH BgAA.NXF LIMIT ISP0 XN XE0 BgAA.XB (HSce (BgAA.ce cfg m)) 0%nat BFUEL FUELA None).
#[local] Notation CHK1 := (check BSEGS (BgAA.IT cfg) ABOTH BgAA.NXF LIMIT ISP0 XN XE0 BgAA.XB (HSce (BgAA.ceL1 cfg)) 0%nat BFUEL FUELA None).

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.
