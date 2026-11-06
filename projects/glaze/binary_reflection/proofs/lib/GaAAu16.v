(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import GaCommon AzStrResizeT AzStrResizeA.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GaNumT OSSVerify.Proofs.glaze.binary_reflection.lib.GaAA. Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaNumT.GaPw OSSVerify.Proofs.glaze.binary_reflection.lib.GaAA.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition cfg : acfg :=
  {| c_entry := 0xae2f4; c_ninstr := 663; c_fr := 192; c_K := 2; c_hr := 8; c_wmx := 5;
     c_head := 0xae3f8; c_join1 := 0xae4f8; c_ret := 0xaeb94; c_jreg := 26; c_vol0 := []; c_vol1 := [];
     c_vw := 2; c_vhi := 65535; c_ixpc := 0xae7ec; c_ixreg := 11; c_ix2pc := 0xae91c; c_ix2reg := 10 |}.
Definition CT (id : nat) : option gcallee := None.
Definition XN : nat -> list expr -> acs -> option acs := GaNumT.GaPw.XNw (XNc ASEGS (GaAA.IT cfg) AASAN GaAA.NXF GASAN BCAP CCAP CT).
   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition wwin (m : smode) : expr := match m with ML => eadd D1 IXv | MS => eadd (eaddz OBJ 1) IXv end.
Definition wfact (m : smode) (k : plan) : plan := PFact (KRange (wwin m) PTRLO (HI47 - c_hr cfg)) k.
Definition fin (k : plan) : plan := PRun [c_ixpc cfg] k.
Definition xl (k : plan) : plan := PRun [] (PExt 0 [] k).
Definition q4 : expr := EMd Instr.M_MULHU VAL (ELit 0x68db8bac710cc).              (* [comment removed for export] *)
Definition r4 : expr := rem VAL q4 10000.
Definition armA (k : plan) : plan := xl (xl (fin k)).                                                                  (* [comment removed for export] *)
Definition armB (k : plan) : plan := divfact VAL (q100 VAL) 100 (zfact VAL (q100 VAL) 100 (xl (xl (xl (fin k))))).     (* [comment removed for export] *)
Definition armC (k : plan) : plan := divfact VAL q4 10000 (divfact r4 (q100w r4) 100 (zfact r4 (q100w r4) 100 (xl (xl (fin k))))).  (* [comment removed for export] *)
Definition elem (m : smode) (k : plan) : plan := wfact m (PCase2 VAL 9 (armA k) (PCase2 VAL 99 (armA k) (PCase2 VAL 999 (armB k) (PCase2 VAL 9999 (armB k) (armC k))))).
Definition epaths (m : smode) (d ix mtr : expr) : list (list dstep) :=
  let w := DFact (KRange (eadd d ix) PTRLO (HI47 - c_hr cfg)) in
  let xl2 := [DRun []; DExt 0 []; DRun []; DExt 0 []; DRun [c_ixpc cfg]] in
  [ [w; DRun [0xae544]; DExt 44 [ELit 11]; DRLo 11 9] ++ xl2;
    [w; DRun [0xae544]; DExt 44 [ELit 11]; DRHi 11 9; DRLo 11 99] ++ xl2 ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ITc : itab := Eval vm_compute in (GaAA.IT cfg).
Lemma IT_eq : GaAA.IT cfg = ITc.   (* [comment removed for export] *)
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


#[local] Notation CHK m := (check ASEGS (GaAA.IT cfg) AASAN GaAA.NXF LIMIT ISP0 XN XE0 GaAA.XB (HSce (GaAA.ce cfg m)) 0%nat BFUEL FUELA None).
#[local] Notation CHK1 := (check ASEGS (GaAA.IT cfg) AASAN GaAA.NXF LIMIT ISP0 XN XE0 GaAA.XB (HSce (GaAA.ceL1 cfg)) 0%nat BFUEL FUELA None).

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.
