(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.Riscv.Instr OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BgNumT.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPw.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition BNU : Z := 0xae57c.    (* [comment removed for export] *)
Definition BNI : Z := 0xb9094.    (* [comment removed for export] *)
Definition is_int (B : Z) : bool := Z.eqb B BNI.
Definition NINSTR (B : Z) : nat := if is_int B then 605%nat else 604%nat.
(* [comment removed for export] *)
Definition IT_def (B : Z) : itab := mk_itab_ranges BSEGS [(B, NINSTR B)].
Definition IT_U : itab := Eval vm_compute in IT_def BNU.
Definition IT_I : itab := Eval vm_compute in IT_def BNI.
Lemma IT_U_eq : IT_U = IT_def BNU. Proof. vm_cast_no_check (@eq_refl itab (IT_def BNU)). Qed.
Lemma IT_I_eq : IT_I = IT_def BNI. Proof. vm_cast_no_check (@eq_refl itab (IT_def BNI)). Qed.
Definition IT (B : Z) : itab := if Z.eqb B BNU then IT_U else if Z.eqb B BNI then IT_I else IT_def B.
Lemma IT_eq : forall B, IT B = IT_def B.
Proof.
  intro B. unfold IT. destruct (Z.eqb_spec B BNU) as [->|_]; [exact IT_U_eq|]. destruct (Z.eqb_spec B BNI) as [->|_]; [exact IT_I_eq | reflexivity].
Qed.
Lemma IT_ok : forall B, itab_sound BSEGS (IT B). Proof. intro. rewrite IT_eq. apply APS.mk_itab_ranges_sound. Qed.
(* [comment removed for export] *)
Definition at_ (B off : Z) : Z := B + off + (if (is_int B && Z.leb 0x7e4 off)%bool then 4 else 0).   (* [comment removed for export] *)
Definition RETPC (B : Z) : Z := at_ B 0x6f8.        (* [comment removed for export] *)

(* [comment removed for export] *)
Definition regsW : list expr := sr_upd regs0 4 (ELit (g_tp GBOTH)).   (* [comment removed for export] *)
Definition TP : expr := EVar 9.    Definition G : expr := EVar 10.    Definition PIT : expr := EVar 11.
Definition PEND : expr := EVar 12. Definition OBJ : expr := EVar 13.  Definition PIX : expr := EVar 14.
Definition ITO : expr := EVar 31.       (* [comment removed for export] *)
Definition REM : expr := EVar 32.  Definition IX : expr := EVar 33.
Definition D : expr := EVar 34.    Definition S : expr := EVar 35.    Definition A : expr := EVar 36.   (* [comment removed for export] *)
Definition ERR : expr := EVar 37.
Definition INLO : expr := EVar 38.      (* [comment removed for export] *)
Definition TAGV : expr := EVar 39.
Definition e_mtr : expr := EVar 40.     (* [comment removed for export] *)
Definition e_fb : expr := EVar 41.      (* [comment removed for export] *)
Definition NXF : nat := 42.
Definition IT0 : expr := eadd INLO ITO. (* [comment removed for export] *)
Definition BLEN : expr := eadd ITO REM.
Definition INSZ : Z := 2 ^ 26.
Definition BIG : Z := 24 * INSZ.
Definition REMHI : Z := INSZ.
Definition IXHI : Z := BIG.
Definition CAPK : Z := 1040.
Definition CAPHI : Z := 4 * IXHI + 8 * INSZ + CAPK.
Definition AHI : Z := CAPHI / 8.
Definition two62 : Z := 2 ^ 62.
Definition FR : Z := 96.
Definition FRK : Z := FR + 3776.        (* [comment removed for export] *)
Definition flo (x : expr) (n : expr) : kentry := KDisj (SA x 0) n (SA e_sp (- FRK)) (ELit (FRK + WSTK)).   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition NBW : Z := 3 * 2^30 + 16.       (* [comment removed for export] *)
Definition NBN : Z := 3 * 2^30 + 80.       (* [comment removed for export] *)
Definition GEV : Z := 2 * EVT + 8.
Definition MTRJ : Z := MTRMAX NBW.
(* [comment removed for export] *)
Definition CPW : expr := EVar 3.
Definition CMAX : Z := MTRJ - pwtop (8 * AHI).   (* [comment removed for export] *)
Definition MTRIN : Z := MTRJ.

(* [comment removed for export] *)
Definition szin (m0 : smode) : expr := match m0 with MS => EVar 34 | ML => S end.

Definition capexpr (ix it inlo a : expr) : expr := esub (eaddz (eadd (escale 4 ix) (escale 8 (esub it inlo))) CAPK) (escale 8 a).
Definition capfact (ix it inlo a : expr) : kentry := KRange (capexpr ix it inlo a) 0 CAPHI.
Definition strL (ix it d s a : expr) : list kentry :=
  [ KWord (SA OBJ 0) 8 (eaddz (escale 8 a) 1); KWord (SA OBJ 8) 8 s; KWord (SA OBJ 16) 8 d;
    KRange a 3 AHI; capfact ix it INLO a;
    KRange s 0 (8 * AHI); KRange (esub (escale 8 a) s) 1 (8 * AHI);
    KRange d PTRLO (PTRHI - 24); KRange (eadd d (escale 8 a)) (PTRLO + 24) PTRHI; KAlign d 16;
    KWr (SA d 0) (escale 8 a); KUnk (SA d 0) (escale 8 a); KShOk (SA d 0) (escale 8 a);                 (* [comment removed for export] *)
    KDisj (SA d 0) (escale 8 a) (SA G 0) (ELit 4); KDisj (SA d 0) (escale 8 a) (SA PEND 0) (ELit 8);
    KDisj (SA d 0) (escale 8 a) (SA PIT 0) (ELit 8); KDisj (SA d 0) (escale 8 a) (SA PIX 0) (ELit 8);
    KDisj (SA d 0) (escale 8 a) (SA OBJ 0) (ELit 24); KDisj (SA d 0) (escale 8 a) (SA INLO 0) BLEN;
    flo d (escale 8 a); img_apart d 0 (escale 8 a); shmap_apart d 0 (escale 8 a) ].
Definition str (m : smode) (ix it : expr) (v : nat) : list kentry :=
  match m with MS => strS OBJ (EVar v) | ML => strL ix it (EVar v) (EVar (1 + v)) (EVar (2 + v)) end.
Definition vis (m : smode) (v : nat) : list (expr * expr) :=
  match m with MS => [] | ML => [(EVar v, escale 8 (EVar (2 + v)))] end.
Definition tbl_shadow : list kentry := GLZ_LOWSH.   (* [comment removed for export] *)
Definition TAGSZ (B : Z) : Z := if is_int B then 4 else 1.
(* [comment removed for export] *)
Definition tp_facts (B : Z) : list kentry :=
  [ KRange TP (CEIL + FRK) (HI47 - 8); KRange (esub TP e_sp) 0 (2 ^ 46); KShOk (SA TP 0) (ELit (TAGSZ B)); img_apart TP 0 (ELit (TAGSZ B));
    KDisj (SA TP 0) (ELit (TAGSZ B)) (SA OBJ 0) (ELit 24); KDisj (SA TP 0) (ELit (TAGSZ B)) (SA G 0) (ELit 4);
    KDisj (SA TP 0) (ELit (TAGSZ B)) (SA PIT 0) (ELit 8); KDisj (SA TP 0) (ELit (TAGSZ B)) (SA PIX 0) (ELit 8) ].
Definition kn_fixed : list kentry :=
  [ KRange G PTRLO (objhi 4); KWr (SA G 0) (ELit 4); KShOk (SA G 0) (ELit 4); KAlign G 8;
    KRange PEND PTRLO (objhi 8); KWord (SA PEND 0) 8 (eadd IT0 REM); KShOk (SA PEND 0) (ELit 8); KAlign PEND 8;
    KRange PIT PTRLO (objhi 8); KWr (SA PIT 0) (ELit 8); KShOk (SA PIT 0) (ELit 8); KAlign PIT 8;
    KRange PIX PTRLO (objhi 8); KWr (SA PIX 0) (ELit 8); KShOk (SA PIX 0) (ELit 8); KAlign PIX 8;
    KRange OBJ PTRLO (objhi 24); KWr (SA OBJ 0) (ELit 24); KShOk (SA OBJ 0) (ELit 24); KAlign OBJ 8; KUnk (SA OBJ 0) (ELit 24);
    KRange INLO PTRLO PTRHI; KRange ITO 1 INSZ; KRange REM 0 REMHI; KRange BLEN 1 INSZ;
    KUnk (SA INLO 0) BLEN; KShOk (SA INLO 0) BLEN; KRange (eadd INLO BLEN) (PTRLO + 1) PTRHI;
    KDisj (SA G 0) (ELit 4) (SA OBJ 0) (ELit 24); KDisj (SA PEND 0) (ELit 8) (SA OBJ 0) (ELit 24);
    KDisj (SA PIT 0) (ELit 8) (SA OBJ 0) (ELit 24); KDisj (SA PIX 0) (ELit 8) (SA OBJ 0) (ELit 24);
    KDisj (SA G 0) (ELit 4) (SA PIT 0) (ELit 8); KDisj (SA G 0) (ELit 4) (SA PIX 0) (ELit 8); KDisj (SA G 0) (ELit 4) (SA PEND 0) (ELit 8);
    KDisj (SA PIT 0) (ELit 8) (SA PIX 0) (ELit 8); KDisj (SA PEND 0) (ELit 8) (SA PIT 0) (ELit 8); KDisj (SA PEND 0) (ELit 8) (SA PIX 0) (ELit 8);
    KDisj (SA INLO 0) BLEN (SA G 0) (ELit 4); KDisj (SA INLO 0) BLEN (SA OBJ 0) (ELit 24);
    KDisj (SA INLO 0) BLEN (SA PEND 0) (ELit 8); KDisj (SA INLO 0) BLEN (SA PIT 0) (ELit 8); KDisj (SA INLO 0) BLEN (SA PIX 0) (ELit 8);
    KAlign e_sp 16; KRange e_sp (CEIL + FRK + 416) (two47 - 16); KWr (SA e_sp (- FRK)) (ELit FRK);
    KRange e_mtr 0 MTRIN; KRange CPW 0 CMAX;
    flo G (ELit 4); flo PEND (ELit 8); flo PIT (ELit 8); flo PIX (ELit 8); flo OBJ (ELit 24); flo INLO BLEN;
    img_apart G 0 (ELit 4); shmap_apart G 0 (ELit 4); img_apart PIT 0 (ELit 8); shmap_apart PIT 0 (ELit 8);
    img_apart PIX 0 (ELit 8); shmap_apart PIX 0 (ELit 8); img_apart OBJ 0 (ELit 24); shmap_apart OBJ 0 (ELit 24);
    img_apart PEND 0 (ELit 8); img_apart INLO 0 BLEN; shmap_apart INLO 0 BLEN;
    KIMGA; fb_fact e_fb ] ++ NEWH ++ RTC ++ tbl_shadow.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition stk_shok : kentry := KShOk (SA e_sp (- FRK)) (ELit FRK).
Definition kn_in (m : smode) (B : Z) : list kentry :=
  [ KWord (SA TP 0) (if is_int B then 4%nat else 1%nat) TAGV; KRange TAGV 0 255;
    KWord (SA G 0) 4 ERR; KRange ERR 0 0; KWord (SA PIT 0) 8 IT0; KWord (SA PIX 0) 8 IX; KRange IX 0 BIG;
    KRange (esub (escale 24 (esub IT0 INLO)) IX) 0 BIG; stk_shok ]
  ++ pw_facts CPW (szin m) e_mtr ++ str m IX IT0 34 ++ tp_facts B ++ kn_fixed.
Definition WS : list (expr * expr) := [(G, ELit 4); (PEND, ELit 8); (PIT, ELit 8); (PIX, ELit 8); (OBJ, ELit 24); (INLO, BLEN)].   (* [comment removed for export] *)
Definition mkcsV (p : Z) (regs : list expr) (k : list kentry) (nx : nat) (vis : list (expr * expr)) (mtr : expr) : acs :=
  ACS (mk_ss p regs k nx) [] 0 FRK 0 vis WS 0 e_sp FdStd false mtr [] e_fb.
Definition regs_in : list expr := regsW.
Definition tin (m : smode) (B : Z) : acs := mkcsV B regs_in (kn_in m B) NXF (vis m 34) e_mtr.

(* [comment removed for export] *)
Definition xERR := EVar 42. Definition xDI := EVar 43. Definition xIX := EVar 44.
 Definition xS := EVar 46.

Definition xMTR := EVar 48.
Definition XLO : nat := 49.
Definition clobbered : list nat := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
Definition regs_out : list expr := sr_havoc regsW clobbered XLO.
Definition szx (m : smode) : expr := match m with MS => EVar 45 | ML => xS end.   (* [comment removed for export] *)
Definition kn_out (m0 m : smode) (B : Z) : list kentry :=
  [ KWord (SA G 0) 4 xERR; KRange xERR 0 24; KWord (SA PIT 0) 8 (eadd IT0 xDI); KRange xDI 0 8; KRange (esub REM xDI) 0 REMHI;
    KWord (SA PIX 0) 8 xIX; KRange xIX 0 IXHI; KRange (esub xIX IX) 0 two62;
    KRange (esub (escale 24 (esub (eadd IT0 xDI) INLO)) xIX) 0 BIG;
    KRange (esub (eadd IT0 xDI) INLO) 0 INSZ ;
    relx xDI xERR xIX IX 8                                                            (* [comment removed for export] *)
    ] ++ pw_facts CPW (szx m) xMTR ++ [                       (* [comment removed for export] *)
    KRange (esub xMTR e_mtr) 0 MTRJ; KRange xMTR 0 MTRJ ]
  ++ str m xIX (eadd IT0 xDI) 45 ++ no_cbound CPW kn_fixed.
(* [comment removed for export] *)
Definition tout (m0 m : smode) (B : Z) : acs := mkcsV (RETPC B) regs_out (kn_out m0 m B) (XLO + 15)%nat (vis m 45) xMTR.
Definition BCAP : Z := 10 * 2 ^ 30.  Definition CCAP : Z := 2.
(* [comment removed for export] *)
Definition ce2 (m : smode) (B : Z) : gcallee2 := GCE2 NXF (tin m B) [tout m MS B] [tout m ML B] BCAP CCAP.
Definition ce (m : smode) (B : Z) : gcallee := c2_merged (ce2 m B).
(* [comment removed for export] *)
Definition ceL1 (B : Z) : gcallee := GCE NXF (tin ML B) [tout ML ML B; tout ML ML B] BCAP CCAP.
End BgNumT.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC OSSVerify.Proofs.glaze.binary_reflection.lib.BgU32 OSSVerify.Proofs.glaze.binary_reflection.lib.BgI32 OSSVerify.Proofs.glaze.binary_reflection.lib.BgU64 OSSVerify.Proofs.glaze.binary_reflection.lib.BgI64 OSSVerify.Proofs.glaze.binary_reflection.lib.BgWN OSSVerify.Proofs.glaze.binary_reflection.lib.BgWNf32 OSSVerify.Proofs.glaze.binary_reflection.lib.BgWNf64 OSSVerify.Proofs.glaze.binary_reflection.lib.BgWNi8 OSSVerify.Proofs.glaze.binary_reflection.lib.BgWNi16 OSSVerify.Proofs.glaze.binary_reflection.lib.BgWNu8 OSSVerify.Proofs.glaze.binary_reflection.lib.BgWNu16. Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPw OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgU32 OSSVerify.Proofs.glaze.binary_reflection.lib.BgI32 OSSVerify.Proofs.glaze.binary_reflection.lib.BgU64 OSSVerify.Proofs.glaze.binary_reflection.lib.BgI64 OSSVerify.Proofs.glaze.binary_reflection.lib.BgWN OSSVerify.Proofs.glaze.binary_reflection.lib.BgWNf32 OSSVerify.Proofs.glaze.binary_reflection.lib.BgWNf64 OSSVerify.Proofs.glaze.binary_reflection.lib.BgWNi8 OSSVerify.Proofs.glaze.binary_reflection.lib.BgWNi16 OSSVerify.Proofs.glaze.binary_reflection.lib.BgWNu8 OSSVerify.Proofs.glaze.binary_reflection.lib.BgWNu16.
Export BgNumT.   (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition CT (id : nat) : option gcallee :=
  if Nat.eqb id 132 then Some BgI32.ce else if Nat.eqb id 133 then Some BgU32.ce
  else if Nat.eqb id 134 then Some BgI64.ce else if Nat.eqb id 135 then Some BgU64.ce
  else if Nat.eqb id 142 then Some BgI32.ceS else if Nat.eqb id 143 then Some BgU32.ceS else None.
Definition lamB (bu bi : Z) (B : Z) : Z := if is_int B then bi else bu.
Definition CT2w (B : Z) (id : nat) : option gcallee2 :=
  if Nat.eqb id 150 then Some (BgWN.ce2 BgWNf32.cfg ML (lamB BgWNf32.BU BgWNf32.BI B))
  else if Nat.eqb id 151 then Some (BgWN.ce2 BgWNf32.cfg MS (lamB BgWNf32.BU BgWNf32.BI B))
  else if Nat.eqb id 152 then Some (BgWN.ce2 BgWNf64.cfg ML (lamB BgWNf64.BU BgWNf64.BI B))
  else if Nat.eqb id 153 then Some (BgWN.ce2 BgWNf64.cfg MS (lamB BgWNf64.BU BgWNf64.BI B))
  else if Nat.eqb id 154 then Some (BgWN.ce2 BgWNi8.cfg ML (lamB BgWNi8.BU BgWNi8.BI B))
  else if Nat.eqb id 155 then Some (BgWN.ce2 BgWNi8.cfg MS (lamB BgWNi8.BU BgWNi8.BI B))
  else if Nat.eqb id 156 then Some (BgWN.ce2 BgWNi16.cfg ML (lamB BgWNi16.BU BgWNi16.BI B))
  else if Nat.eqb id 157 then Some (BgWN.ce2 BgWNi16.cfg MS (lamB BgWNi16.BU BgWNi16.BI B))
  else if Nat.eqb id 158 then Some (BgWN.ce2 BgWNu8.cfg ML (lamB BgWNu8.BU BgWNu8.BI B))
  else if Nat.eqb id 159 then Some (BgWN.ce2 BgWNu8.cfg MS (lamB BgWNu8.BU BgWNu8.BI B))
  else if Nat.eqb id 160 then Some (BgWN.ce2 BgWNu16.cfg ML (lamB BgWNu16.BU BgWNu16.BI B))
  else if Nat.eqb id 161 then Some (BgWN.ce2 BgWNu16.cfg MS (lamB BgWNu16.BU BgWNu16.BI B))
  else None.
Definition CT2 (B : Z) : nat -> option gcallee2 := ct2_or (CT2w B) CT2_resize.
Definition XN (B : Z) : nat -> list expr -> acs -> option acs := XNw (XNc BSEGS (IT B) ABOTH NXF GBOTH BCAP CCAP CT).   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition CT1 (B : Z) (id : nat) : option gcallee :=
  if Nat.eqb id 170 then Some (BgWN.ceL1 BgWNf32.cfg (lamB BgWNf32.BU BgWNf32.BI B))
  else if Nat.eqb id 171 then Some (BgWN.ceL1 BgWNf64.cfg (lamB BgWNf64.BU BgWNf64.BI B))
  else if Nat.eqb id 172 then Some (BgWN.ceL1 BgWNi8.cfg (lamB BgWNi8.BU BgWNi8.BI B))
  else if Nat.eqb id 173 then Some (BgWN.ceL1 BgWNi16.cfg (lamB BgWNi16.BU BgWNi16.BI B))
  else if Nat.eqb id 174 then Some (BgWN.ceL1 BgWNu8.cfg (lamB BgWNu8.BU BgWNu8.BI B))
  else if Nat.eqb id 175 then Some (BgWN.ceL1 BgWNu16.cfg (lamB BgWNu16.BU BgWNu16.BI B))
  else CT id.
Definition XN1 (B : Z) : nat -> list expr -> acs -> option acs := XNw (XNc BSEGS (IT B) ABOTH NXF GBOTH BCAP CCAP (CT1 B)).
Definition XB (B : Z) : nat -> list expr -> acs -> option (acs * acs) := XBc BSEGS ABOTH NXF GBOTH BCAP CCAP (CT2 B).
Definition FUELN : nat := 4000.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition RSZID (m : smode) : nat := match m with MS => 105%nat | ML => 115%nat end.
Definition RSZ (m : smode) (d s a : expr) : list expr :=
  match m with MS => resize_args_S d e_mtr e_fb | ML => resize_args_L d s a e_mtr e_fb end.
Definition B2 : nat := 130.           (* [comment removed for export] *)
Definition BMP : nat := 170.          (* [comment removed for export] *)

(* [comment removed for export] *)
Definition exitD (m : smode) (K : Z) (XI a : expr) : plan :=
  let it' := eaddz IT0 K in let cons' := esub it' INLO in
  PFactLe cons' (eadd (esub IT0 INLO) REM) INSZ
  (PFact (KRange ITO 1 (INSZ - K))                   (* [comment removed for export] *)
  (PFactLe XI (escale 24 cons') IXHI
  (PFactLe (esub (escale 24 cons') XI) (escale 24 cons') BIG
  (match m with                  (* [comment removed for export] *)
   | ML => PFactLe (capexpr XI it' INLO a) (eaddz (escale 104 cons') CAPK) CAPHI (PHandoffW 1 [(43%nat, ELit K)])
   | MS => PHandoffW 0 [(43%nat, ELit K)]
   end)))).
(* [comment removed for export] *)
Definition pre (k : plan) : plan := PRun [] (PExt 42 [] (PRun [] k)).
Definition ERRX (m : smode) : plan := PRun [] (PHandoffW (hole m) [(43%nat, ELit 0)]).      (* [comment removed for export] *)
Definition EXITERR (m : smode) : plan := pre (ERRX m).                                        (* [comment removed for export] *)

(* [comment removed for export] *)
Definition grown (k : plan) : plan := PExt 13 [EVar B2] k.
(* [comment removed for export] *)
Definition NSZ (hr : Z) : expr := eaddz (escale 2 IX) (2 * hr).
(* [comment removed for export] *)
Definition MGROWN : expr := eadd e_mtr (EVar 132).
Definition PWK (m : smode) (hr : Z) (k : plan) : plan := PExt 49 [e_mtr; szin m; NSZ hr; CPW; ELit 1] k.    (* [comment removed for export] *)
Definition PWG (m : smode) (hr : Z) (k : plan) : plan := PExt 49 [e_mtr; szin m; NSZ hr; CPW; ELit 0] k.    (* [comment removed for export] *)
Definition diamond (m : smode) (hr : Z) (cont : smode -> expr -> expr -> expr -> expr -> plan) : plan :=
  match m with
  | ML => PBranch (cont ML D S A e_mtr)
                  (PRun [] (PBump B2 (PExt2 (RSZID ML) (RSZ ML D S A) (PWK ML hr (cont ML D (NSZ hr) A e_mtr)) (PWG ML hr (grown (cont ML (EVar 130) (NSZ hr) (EVar 131) MGROWN))))))
  | MS => if Z.leb 23 hr then PBump B2 (PExt2 (RSZID MS) (RSZ MS D D A) (PContraH 0) (PWG MS hr (grown (cont ML (EVar 130) (NSZ hr) (EVar 131) MGROWN))))
          else PBranch (cont MS D D A e_mtr)
                       (PRun [] (PBump B2 (PExt2 (RSZID MS) (RSZ MS D D A)
                                   (if Z.leb 12 hr then PContraH 0
                                    else PCase2 IX (11 - hr) (PWK MS hr (cont MS D (NSZ hr) A e_mtr)) PContra)   (* [comment removed for export] *)
                                   (PWG MS hr (grown (cont ML (EVar 130) (NSZ hr) (EVar 131) MGROWN))))))
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition JLO : nat := 121.
Definition D1 : expr := EVar 121.  Definition S1 : expr := EVar 122.  Definition A1 : expr := EVar 123.  Definition MTR1 : expr := EVar 124.
Definition JRS : nat := 125.        (* [comment removed for export] *)
Definition JNX : nat := 150.
Definition GROWMAXN : Z := kcost (2 * NBN + 8) + KFREE.
Definition roomJ (m : smode) (hr : Z) : list kentry :=
  match m with MS => [KRange (esub D1 IX) hr (2 ^ 40)] | ML => [KRange (esub S1 IX) hr (2 ^ 37)] end.
Definition sz1 (m : smode) : expr := match m with MS => D1 | ML => S1 end.
Definition mfacts1 (m : smode) : list kentry :=
  [ ] ++ pw_facts CPW (sz1 m) MTR1 ++ [ KRange (esub MTR1 e_mtr) 0 GROWMAXN; KRange MTR1 0 MTRJ ].
Definition mkcsJ (p : Z) (regs : list expr) (k : list kentry) (vis : list (expr * expr)) : acs :=
  ACS (mk_ss p regs k JNX) [] 0 FRK 0 vis WS 0 e_sp FdStd false MTR1 [] e_fb.
(* [comment removed for export] *)
Definition csregs_ra : list nat := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
(* [comment removed for export] *)
Fixpoint ehas (lo hi : nat) (e : expr) : bool :=
  match e with
  | EVar n => (Nat.leb lo n && Nat.ltb n hi)%bool
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => (ehas lo hi a || ehas lo hi b)%bool
  | EExt _ _ _ a => ehas lo hi a
  | _ => false
  end.
Definition ahas (lo hi : nat) (a : saddr) : bool := ehas lo hi (a_base a).
Definition khas (lo hi : nat) (K : kentry) : bool :=
  match K with
  | KWord a _ v => ahas lo hi a || ehas lo hi v
  | KZero a n | KWr a n | KUnk a n | KShOk a n | KBlob a n _ | KFill a n _ => ahas lo hi a || ehas lo hi n
  | KImg _ _ => false
  | KAlign x _ | KRange x _ _ => ehas lo hi x
  | KDisj a1 n1 a2 n2 => ahas lo hi a1 || ehas lo hi n1 || ahas lo hi a2 || ehas lo hi n2
  | KFpc v l _ => ehas lo hi v || ehas lo hi l
  end%bool.
(* [comment removed for export] *)
Inductive jstep : Type := JD (d : dstep) | JB (n : nat).
Fixpoint jpath (B : Z) (cs : acs) (l : list jstep) : acs :=
  match l with
  | [] => cs
  | JD d :: r => match dgo BSEGS (IT B) ABOTH (XN B) (XB B) BFUEL NXF cs d with Some c => jpath B c r | None => cs end
  | JB n :: r => match APC.node_bump cs n with Some c => jpath B c r | None => cs end
  end.
(* [comment removed for export] *)
Definition JSJ (r0 : acs) (J hr : Z) (m : smode) : acs :=
  mkcsJ J (sr_havoc (s_regs (a_ss r0)) csregs_ra JRS)
        (roomJ m hr ++ mfacts1 m ++ str m IX IT0 121 ++ filter (fun K => negb (khas 34 37 K)) (kn r0)) (vis m 121).
(* [comment removed for export] *)
Definition mrgJ (J : Z) : plan := PRun [J] (PMerge 1).
Definition diamondJ (m : smode) (hr J : Z) : plan :=
  match m with
  | ML => PBranch (mrgJ J) (PRun [] (PBump B2 (PExt2 (RSZID ML) (RSZ ML D S A) (PWK ML hr (mrgJ J)) (PWG ML hr (grown (mrgJ J))))))
  | MS => PBranch (mrgJ J)
                  (PRun [] (PBump B2 (PExt2 (RSZID MS) (RSZ MS D D A)
                              (if Z.leb 12 hr then PContraH 0 else PCase2 IX (11 - hr) (PWK MS hr (mrgJ J)) PContra)
                              (PWG MS hr (grown (mrgJ J))))))
  end.
(* [comment removed for export] *)
Definition tagsteps (k : Z) : list jstep := (if Z.eqb k 0 then [] else [JD (DHi TAGV (8 * k - 1))]) ++ [JD (DLo TAGV (8 * k + 7))].
Definition pre3 : list jstep := [JD (DRun []); JD (DExt 42 []); JD (DRun [])].
Definition intpre (B stpc K : Z) : list jstep := [JD (DHi REM (K - 1)); JD (DRun [at_ B stpc]); JB 120; JD (DExt 44 [ELit 10]); JD (DRun [])].
Definition armpre (B k : Z) : list jstep :=
  tagsteps k ++ pre3 ++
  match k with
  | 9 => intpre B 0x518 4 | 10 => intpre B 0x45c 4 | 13 => intpre B 0x300 8 | 14 => intpre B 0x204 8   (* [comment removed for export] *)
  | _ => []
  end.
(* [comment removed for export] *)
Definition JR0 (B : Z) (m : smode) (k : Z) : Z * acs :=
  let s := jpath B (tin m B) (armpre B k) in let J := pc s + 4 in (J, set_kn (jpath B s [JD DBrF; JD (DRun [J])]) (kn s)).
  (* [comment removed for export] *)
Definition DARMS : list Z := [9; 10; 13; 14].
Definition JR0_UL : list (Z * (Z * acs)) := Eval vm_compute in map (fun k => (k, JR0 BNU ML k)) DARMS.
Definition JR0_US : list (Z * (Z * acs)) := Eval vm_compute in map (fun k => (k, JR0 BNU MS k)) DARMS.
Definition JR0_IL : list (Z * (Z * acs)) := Eval vm_compute in map (fun k => (k, JR0 BNI ML k)) DARMS.
Definition JR0_IS : list (Z * (Z * acs)) := Eval vm_compute in map (fun k => (k, JR0 BNI MS k)) DARMS.
Definition JR0L (B : Z) (m : smode) : list (Z * (Z * acs)) :=
  if Z.eqb B BNU then match m with ML => JR0_UL | MS => JR0_US end else match m with ML => JR0_IL | MS => JR0_IS end.
Definition jr0 (B : Z) (m : smode) (k : Z) : Z * acs :=
  match find (fun p => Z.eqb (fst p) k) (JR0L B m) with Some (_, x) => x | None => (0, tin m B) end.
(* [comment removed for export] *)
Definition joinJ (B : Z) (m : smode) (k : Z) (hr : Z) (cont : smode -> expr -> expr -> expr -> expr -> plan) : plan :=
  (* [comment removed for export] *)
  match m with
  | MS => if Z.leb 23 hr then diamond m hr cont else
      PViaM 1 [(JSJ (snd (jr0 B MS k)) (fst (jr0 B MS k)) hr MS, cont MS D1 D1 A1 MTR1); (JSJ (snd (jr0 B MS k)) (fst (jr0 B MS k)) hr ML, cont ML D1 S1 A1 MTR1)]
              JLO (diamondJ MS hr (fst (jr0 B MS k)))
  | ML => PViaM 1 [(JSJ (snd (jr0 B ML k)) (fst (jr0 B ML k)) hr ML, cont ML D1 S1 A1 MTR1)] JLO (diamondJ ML hr (fst (jr0 B ML k)))
  end.

(* [comment removed for export] *)
Definition room (m : smode) (hr : Z) (s a : expr) (k : plan) : plan :=
  match m with ML => PFactVia (esub (escale 8 a) IX) (esub s IX) (hr + 1) (2 ^ 40) k | MS => k end.
(* [comment removed for export] *)
Definition bufx (m : smode) (d : expr) : expr := match m with ML => eadd d IX | MS => eadd (eaddz OBJ 1) IX end.
Definition bufimg (m : smode) (d a : expr) (w : Z) (k : plan) : plan :=
  let buf := bufx m d in
  let k' := PFact (img_apart buf 0 (ELit w)) (PFact (shmap_apart buf 0 (ELit w)) k) in   (* [comment removed for export] *)
  match m with ML => PFactLe buf (eaddz (eadd d (escale 8 a)) (- w)) (PTRHI - w) k' | MS => k' end.   (* [comment removed for export] *)

Section Arms.
Variable B : Z.
Definition o (x : Z) : Z := at_ B x.

Definition HV : expr := EVar 120.
Definition X44 (r : Z) (k : plan) : plan := PExt 44 [ELit r] k.
(* [comment removed for export] *)
Definition WNARGS : list expr := [CPW; ELit 0; G; OBJ; ITO; REM; IX; D; S; A; ERR; INLO; PEND; PIT; PIX; e_mtr; e_fb].
Definition arm_lam (idL : nat) (m : smode) : plan :=
  pre (PBump BMP (PExt2 (match m with ML => idL | MS => Datatypes.S idL end) WNARGS
         (PRun [] (PHandoff 0)) (PRun [] (PExt 13 [EVar (BMP + 3)] (PHandoff 1))))).   (* [comment removed for export] *)
Definition arm_lamL1 (id1 : nat) (m : smode) : plan :=
  pre (PBump BMP (PExt id1 WNARGS (PRun [] (PExt 13 [EVar (BMP + 3)] (PHandoff 1))))).
(* [comment removed for export] *)
Definition int_cont (cid cidS : nat) (K hr w : Z) (m : smode) (d s a mtr : expr) : plan :=
  room m hr s a (PRun [] (bufimg m d a w (PBump BMP (PExt (match m with ML => cid | MS => cidS end)
                                         (match m with ML => [HV; a; s; d; IX; mtr; e_fb] | MS => [HV; ELit 0; s; ELit 0; IX; mtr; e_fb] end)
                                         (PRun [] (exitD m K (eadd IX (EVar 192)) a)))))).
Definition arm_int (k : Z) (stpc : Z) (cid cidS : nat) (K hr w : Z) (m : smode) : plan :=
  pre (PCase2 REM (K - 1) (ERRX m) (PRun [o stpc] (PBump 120 (X44 10 (PRun [] (joinJ B m k hr (int_cont cid cidS K hr w))))))).
(* [comment removed for export] *)
Definition arm_of (m : smode) (k : Z) : plan :=
  match k with
  | 1 => arm_lam 154 m | 2 => arm_lam 158 m | 5 => arm_lam 156 m | 6 => arm_lam 160 m
  | 8 => arm_lam 150 m | 9 => arm_int 9 0x518 132 142 4 16 11 m | 10 => arm_int 10 0x45c 133 143 4 16 10 m
  | 12 => arm_lam 152 m | 13 => arm_int 13 0x300 134 134 8 24 20 m | 14 => arm_int 14 0x204 135 135 8 24 20 m
  | _ => EXITERR m
  end.


(* [comment removed for export] *)
Definition arm_ofL1 (m : smode) (k : Z) : plan :=
  match k with
  | 1 => arm_lamL1 172 m | 2 => arm_lamL1 174 m | 5 => arm_lamL1 173 m | 6 => arm_lamL1 175 m
  | 8 => arm_lamL1 170 m | 9 => arm_int 9 0x518 132 142 4 16 11 m | 10 => arm_int 10 0x45c 133 143 4 16 10 m
  | 12 => arm_lamL1 171 m | 13 => arm_int 13 0x300 134 134 8 24 20 m | 14 => arm_int 14 0x204 135 135 8 24 20 m
  | _ => EXITERR m
  end.

   (* [comment removed for export] *)
End Arms.



Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint classes_rng (arm : smode -> Z -> plan) (m : smode) (k : Z) (n : nat) : plan :=
  match n with
  | O => arm m k
  | Datatypes.S n' => PCase2 TAGV (8 * k + 7) (arm m k) (classes_rng arm m (k + 1) n')
  end.
(* [comment removed for export] *)
Definition QS : list (Z * nat) := [(0, 3%nat); (4, 3%nat); (8, 3%nat); (12, 3%nat); (16, 15%nat)].
Definition plan_top : plan :=
  PCase2 TAGV 31 (PHandoffW 2 []) (PCase2 TAGV 63 (PHandoffW 3 []) (PCase2 TAGV 95 (PHandoffW 4 []) (PCase2 TAGV 127 (PHandoffW 5 []) (PHandoffW 6 [])))).
Lemma top_gplan : gplan_ok plan_top = true. Proof. reflexivity. Qed.
Section Cuts.
Variable B : Z.
Variable m : smode.                                   (* [comment removed for export] *)
Variable CE : gcallee.                                (* [comment removed for export] *)
Variable XNV : nat -> list expr -> acs -> option acs. (* [comment removed for export] *)
Variable ARM : smode -> Z -> plan.                    (* [comment removed for export] *)
(* [comment removed for export] *)
Definition cutT (steps : list dstep) : acs := snd (dpath BSEGS (IT B) ABOTH XNV (XB B) BFUEL (ce_nxf CE) (tin m B) steps 0).
(* [comment removed for export] *)
Definition cut_of (q : Z * nat) : acs * plan :=
  let lo := 8 * fst q in let hi := 8 * (fst q + Z.of_nat (snd q)) + 7 in
  (cutT ((if Z.eqb lo 0 then [] else [DHi TAGV (lo - 1)]) ++ (if Z.eqb hi 255 then [] else [DLo TAGV hi])), classes_rng ARM m (fst q) (snd q)).
Definition CUTS : list (acs * plan) := map cut_of QS.
Definition NCUTS : nat := 5.
Lemma CUTS_len : length CUTS = NCUTS. Proof. reflexivity. Qed.
Definition cut_stmt (i : nat) : Prop :=
  match nth_error CUTS i with
  | Some (T, k) => exists sh, gplan_ok k = true /\ holes_only sh = true /\
      check BSEGS (IT B) ABOTH (ce_nxf CE) LIMIT ISP0 XNV XE0 (XB B) (HScut CE CUTS (Datatypes.S i)) 0%nat BFUEL FUELN None T k = COk sh
  | None => True
  end.
Definition cut_ok (i : nat) : bool :=
  match nth_error CUTS i with
  | Some (T, k) => match check BSEGS (IT B) ABOTH (ce_nxf CE) LIMIT ISP0 XNV XE0 (XB B) (HScut CE CUTS (Datatypes.S i)) 0%nat BFUEL FUELN None T k with
                 | COk sh => (holes_only sh && gplan_ok k)%bool | _ => false end
  | None => false
  end.
Lemma cut_ok_sound : forall i, cut_ok i = true -> cut_stmt i.
Proof.
  intros i H. unfold cut_ok in H. unfold cut_stmt. destruct (nth_error CUTS i) as [[T k]|]; [|exact I].
  destruct (check BSEGS (IT B) ABOTH (ce_nxf CE) LIMIT ISP0 XNV XE0 (XB B) (HScut CE CUTS (Datatypes.S i)) 0%nat BFUEL FUELN None T k) as [sh|c w cs]; try discriminate.
  apply andb_prop in H as [H1 H2]. exists sh. split; [exact H2|]. split; [exact H1|]. reflexivity.
Qed.
(* [comment removed for export] *)
Definition top_stmt : Prop :=
  check BSEGS (IT B) ABOTH (ce_nxf CE) LIMIT ISP0 XNV XE0 (XB B) (HScut CE CUTS 0) 0%nat BFUEL FUELN None (ce_tin CE) plan_top = COk (SHole 2).
End Cuts.
