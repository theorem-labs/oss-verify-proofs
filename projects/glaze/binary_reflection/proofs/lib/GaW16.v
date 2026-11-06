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
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GaNumT OSSVerify.Proofs.glaze.binary_reflection.lib.AzStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.AzStrResizeA. Import OSSVerify.Proofs.glaze.binary_reflection.lib.GaCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GaNumT.GaPw OSSVerify.Proofs.glaze.binary_reflection.lib.AzStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.AzStrResizeA.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition B16U : Z := 0xb66ac.   (* [comment removed for export] *)
Definition B16I : Z := 0xbe8a4.   (* [comment removed for export] *)
Definition NINSTR : nat := 467.
Definition IT (B : Z) : itab := mk_itab_ranges ASEGS [(B, NINSTR)].
Lemma IT_ok : forall B, itab_sound ASEGS (IT B). Proof. intro. apply APS.mk_itab_ranges_sound. Qed.
Definition RETPC (B : Z) : Z := B + 0x4cc.
Definition JOIN1 (B : Z) : Z := B + 0x16c.      (* [comment removed for export] *)
Definition STIX (B : Z) : Z := B + 0x478.       (* [comment removed for export] *)

(* [comment removed for export] *)
Definition regsW : list expr := sr_upd regs0 4 (ELit (g_tp GASAN)).    (* [comment removed for export] *)
Definition C : expr := EVar 9.           (* [comment removed for export] *)
Definition T : expr := eaddz C (-8).
Definition G : expr := EVar 31.          (* [comment removed for export] *)
Definition OBJ : expr := EVar 32.        (* [comment removed for export] *)
Definition ITO : expr := EVar 33.        (* [comment removed for export] *)
Definition REM : expr := EVar 34.        (* [comment removed for export] *)
Definition IX : expr := EVar 35.         (* [comment removed for export] *)
Definition D : expr := EVar 36.  Definition S : expr := EVar 37.  Definition A : expr := EVar 38.   (* [comment removed for export] *)
Definition ERR : expr := EVar 39.        (* [comment removed for export] *)
Definition INLO : expr := EVar 40.       (* [comment removed for export] *)
Definition PEND : expr := EVar 41.       (* [comment removed for export] *)
Definition PIT : expr := EVar 42.        (* [comment removed for export] *)
Definition PIX : expr := EVar 43.        (* [comment removed for export] *)
Definition e_mtr : expr := EVar 44.      (* [comment removed for export] *)
Definition e_fb : expr := EVar 45.       (* [comment removed for export] *)
Definition IT0 : expr := eadd INLO ITO.  (* [comment removed for export] *)
Definition BLEN : expr := eadd ITO REM.
Definition NXF : nat := 46.

Definition INSZ : Z := 2 ^ 26.
Definition BIG : Z := 24 * INSZ.
Definition REMHI : Z := INSZ.
Definition IXHI : Z := BIG.
Definition CAPK : Z := 1040.
Definition AHI : Z := (4 * IXHI + 8 * INSZ + CAPK) / 8.
Definition FRK : Z := 80 + 3680.         (* [comment removed for export] *)
Definition RFRK : Z := 3680.
Definition flo (x : expr) (n : expr) : kentry := KDisj (SA x 0) n (SA e_sp (- FRK)) (ELit (FRK + WSTK)).   (* [comment removed for export] *)
Definition NB : Z := 3 * 2^30 + 16.

Definition MTRJ : Z := MTRMAX NB.
(* [comment removed for export] *)
Definition CPW : expr := EVar 3.
Definition CMAX : Z := MTRJ - pwtop (8 * AHI).   (* [comment removed for export] *)
Definition MTRIN : Z := MTRJ.
Definition GROWMAX : Z := kcost (2 * NB + 8) + KFREE.

(* [comment removed for export] *)
Definition szin (m0 : smode) : expr := match m0 with MS => EVar 36 | ML => S end.
(* [comment removed for export] *)
Definition capexpr (ix it inlo a : expr) : expr := esub (eaddz (eadd (escale 4 ix) (escale 8 (esub it inlo))) CAPK) (escale 8 a).
Definition capfact (ix it inlo a : expr) : kentry := KRange (capexpr ix it inlo a) 0 (4 * IXHI + 8 * INSZ + CAPK).
Definition strL (ix it d s a : expr) : list kentry :=
  [ KWord (SA OBJ 0) 8 (eaddz (escale 8 a) 1); KWord (SA OBJ 8) 8 s; KWord (SA OBJ 16) 8 d;
    KRange a 3 AHI; capfact ix it INLO a;
    KRange s 0 (8 * AHI); KRange (esub (escale 8 a) s) 1 (8 * AHI);
    KRange d PTRLO (PTRHI - 24); KRange (eadd d (escale 8 a)) (PTRLO + 24) PTRHI; KAlign d 16;
    KWr (SA d 0) (escale 8 a); KUnk (SA d 0) (escale 8 a); KShOk (SA d 0) (escale 8 a);                 (* [comment removed for export] *)
    KDisj (SA d 0) (escale 8 a) (SA C (-8)) (ELit 48); KDisj (SA d 0) (escale 8 a) (SA G 0) (ELit 4);
    KDisj (SA d 0) (escale 8 a) (SA PEND 0) (ELit 8); KDisj (SA d 0) (escale 8 a) (SA PIT 0) (ELit 8); KDisj (SA d 0) (escale 8 a) (SA PIX 0) (ELit 8);
    KDisj (SA d 0) (escale 8 a) (SA OBJ 0) (ELit 24); KDisj (SA d 0) (escale 8 a) (SA INLO 0) BLEN;
    KDisj (SA d 0) (escale 8 a) (SA e_sp (- FRK)) (ELit (RFRK + WSTK)); img_apart d 0 (escale 8 a); shmap_apart d 0 (escale 8 a) ].


Definition tbl_shadow : list kentry := GLZ_LOWSH.   (* [comment removed for export] *)
Definition kn_fixed : list kentry :=
  [ KRange C (CEIL + 16) (HI47 - 40); KAlign C 8; KShOk (SA C (-8)) (ELit 48); KWord (SA C 0) 8 PEND; KWord (SA C 8) 8 PIT; KWord (SA C 16) 8 G;
    KWord (SA C 24) 8 OBJ; KWord (SA C 32) 8 PIX; KWr (SA C (-8)) (ELit 2);
    KRange G PTRLO (objhi 4); KWr (SA G 0) (ELit 4); KShOk (SA G 0) (ELit 4); KAlign G 4;
    KRange PEND PTRLO (objhi 8); KWord (SA PEND 0) 8 (eadd IT0 REM); KShOk (SA PEND 0) (ELit 8); KAlign PEND 8;
    KRange PIT PTRLO (objhi 8); KWr (SA PIT 0) (ELit 8); KShOk (SA PIT 0) (ELit 8); KAlign PIT 8;
    KRange PIX PTRLO (objhi 8); KWr (SA PIX 0) (ELit 8); KShOk (SA PIX 0) (ELit 8); KAlign PIX 8;
    KRange OBJ PTRLO (objhi 24); KWr (SA OBJ 0) (ELit 24); KShOk (SA OBJ 0) (ELit 24); KAlign OBJ 8;
    KRange INLO PTRLO PTRHI; KRange ITO 1 INSZ; KRange REM 0 REMHI; KRange BLEN 1 INSZ;
    KUnk (SA INLO 0) BLEN; KShOk (SA INLO 0) BLEN; KRange (eadd INLO BLEN) (PTRLO + 1) PTRHI;
    KDisj (SA C (-8)) (ELit 48) (SA OBJ 0) (ELit 24); KDisj (SA e_sp (- FRK)) (ELit FRK) (SA OBJ 0) (ELit 24);   (* [comment removed for export] *)
    KDisj (SA G 0) (ELit 4) (SA OBJ 0) (ELit 24); KDisj (SA PEND 0) (ELit 8) (SA OBJ 0) (ELit 24);
    KDisj (SA PIT 0) (ELit 8) (SA OBJ 0) (ELit 24); KDisj (SA PIX 0) (ELit 8) (SA OBJ 0) (ELit 24);
    KDisj (SA G 0) (ELit 4) (SA PIT 0) (ELit 8); KDisj (SA G 0) (ELit 4) (SA PIX 0) (ELit 8); KDisj (SA G 0) (ELit 4) (SA PEND 0) (ELit 8);
    KDisj (SA PIT 0) (ELit 8) (SA PIX 0) (ELit 8); KDisj (SA PEND 0) (ELit 8) (SA PIT 0) (ELit 8); KDisj (SA PEND 0) (ELit 8) (SA PIX 0) (ELit 8);
    KDisj (SA INLO 0) BLEN (SA G 0) (ELit 4); KDisj (SA INLO 0) BLEN (SA OBJ 0) (ELit 24);
    KDisj (SA INLO 0) BLEN (SA PEND 0) (ELit 8); KDisj (SA INLO 0) BLEN (SA PIT 0) (ELit 8); KDisj (SA INLO 0) BLEN (SA PIX 0) (ELit 8);
    KUnk (SA OBJ 0) (ELit 24);
    KAlign e_sp 16; KRange e_sp (CEIL + 4176) (two47 - 16); KWr (SA e_sp (- FRK)) (ELit FRK);
    KRange (esub C e_sp) 16 (2 ^ 63); KDisj (SA e_sp (- FRK)) (ELit FRK) (SA C (-8)) (ELit 48);   (* [comment removed for export] *)
    KRange e_mtr 0 MTRIN; KRange CPW 0 CMAX;
    flo G (ELit 4); flo PEND (ELit 8); flo PIT (ELit 8); flo PIX (ELit 8); flo OBJ (ELit 24); flo INLO BLEN;
    img_apart G 0 (ELit 4); shmap_apart G 0 (ELit 4); img_apart PIT 0 (ELit 8); shmap_apart PIT 0 (ELit 8);
    img_apart PIX 0 (ELit 8); shmap_apart PIX 0 (ELit 8); img_apart OBJ 0 (ELit 24); shmap_apart OBJ 0 (ELit 24);
    img_apart PEND 0 (ELit 8); img_apart INLO 0 BLEN; shmap_apart INLO 0 BLEN;
    KDisj (SA C (-8)) (ELit 48) (SA G 0) (ELit 4); KDisj (SA C (-8)) (ELit 48) (SA PEND 0) (ELit 8); KDisj (SA C (-8)) (ELit 48) (SA PIT 0) (ELit 8);
    KDisj (SA C (-8)) (ELit 48) (SA PIX 0) (ELit 8); KDisj (SA C (-8)) (ELit 48) (SA INLO 0) BLEN;   (* [comment removed for export] *)
    KIMGA; fb_fact e_fb ] ++ NEWH ++ RTC ++ tbl_shadow.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition str (m : smode) (ix it : expr) (v : nat) : list kentry :=
  match m with MS => strS OBJ (EVar v) | ML => strL ix it (EVar v) (EVar (1 + v)) (EVar (2 + v)) end.
Definition vis (m : smode) (v : nat) : list (expr * expr) :=
  match m with MS => [] | ML => [(EVar v, escale 8 (EVar (2 + v)))] end.
Definition kn_in (m : smode) : list kentry :=
  [ KWord (SA G 0) 4 ERR; KRange ERR 0 0; KWord (SA PIT 0) 8 IT0; KWord (SA PIX 0) 8 IX; KRange IX 0 BIG;
    KRange (esub (escale 24 (esub IT0 INLO)) IX) 0 BIG ]                          (* [comment removed for export] *)
  ++ pw_facts CPW (szin m) e_mtr ++ str m IX IT0 36 ++ kn_fixed.
Definition WS : list (expr * expr) := [(eaddz C (-8), ELit 48); (G, ELit 4); (PEND, ELit 8); (PIT, ELit 8); (PIX, ELit 8); (OBJ, ELit 24); (INLO, BLEN)].   (* [comment removed for export] *)
Definition mkcsV (p : Z) (regs : list expr) (k : list kentry) (nx : nat) (vis : list (expr * expr)) : acs :=
  ACS (mk_ss p regs k nx) [] 0 FRK 0 vis WS 0 e_sp FdStd false e_mtr [] e_fb.
Definition regs_in : list expr := sr_upd regsW 11 T.
Definition tin (m : smode) (B : Z) : acs := mkcsV B regs_in (kn_in m) NXF (vis m 36).

(* [comment removed for export] *)
Definition xERR := EVar 46. Definition xDI := EVar 47. Definition xIX := EVar 48.
 Definition xS := EVar 50.

Definition xMTR := EVar 52.
Definition XLO : nat := 53.
Definition clobbered : list nat := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
Definition regs_out : list expr := sr_havoc regsW clobbered XLO.
Definition szx (m : smode) : expr := match m with MS => EVar 49 | ML => xS end.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition kn_out (m0 m : smode) : list kentry :=
  [ KWord (SA G 0) 4 xERR; KRange xERR 0 24; KWord (SA PIT 0) 8 (eadd IT0 xDI); KRange xDI 0 2; KRange (esub REM xDI) 0 REMHI;
    KWord (SA PIX 0) 8 xIX; KRange xIX 0 IXHI; KRange (esub xIX IX) 0 5;
    KRange (esub (escale 24 (esub (eadd IT0 xDI) INLO)) xIX) 0 BIG;                   (* [comment removed for export] *)
    KRange (esub (eadd IT0 xDI) INLO) 0 INSZ                                         (* [comment removed for export] *)
    ] ++ pw_facts CPW (szx m) xMTR ++ [                       (* [comment removed for export] *)
    KRange (esub xMTR e_mtr) 0 MTRJ; KRange xMTR 0 MTRJ;
    relx xDI xERR xIX IX 8 ]                                                          (* [comment removed for export] *)
  ++ str m xIX (eadd IT0 xDI) 49 ++ no_cbound CPW kn_fixed.
Definition mkcsX (p : Z) (regs : list expr) (k : list kentry) (nx : nat) (vis : list (expr * expr)) : acs :=
  ACS (mk_ss p regs k nx) [] 0 FRK 0 vis WS 0 e_sp FdStd false xMTR [] e_fb.
Definition tout (m0 m : smode) (B : Z) : acs := mkcsX (RETPC B) regs_out (kn_out m0 m) (XLO + 15)%nat (vis m 49).
Definition BCAP : Z := 10 * 2 ^ 30.  Definition CCAP : Z := 2.
(* [comment removed for export] *)
Definition ce2 (m : smode) (B : Z) : gcallee2 := GCE2 NXF (tin m B) [tout m MS B] [tout m ML B] BCAP CCAP.
Definition ce (m : smode) (B : Z) : gcallee := c2_merged (ce2 m B).
(* [comment removed for export] *)
Definition ceL1 (B : Z) : gcallee := GCE NXF (tin ML B) [tout ML ML B; tout ML ML B] BCAP CCAP.

(* [comment removed for export] *)
Definition XN (B : Z) : nat -> list expr -> acs -> option acs := XNw (XNc ASEGS (IT B) AASAN NXF GASAN BCAP CCAP CT0).   (* [comment removed for export] *)
Definition XB : nat -> list expr -> acs -> option (acs * acs) := XBc ASEGS AASAN NXF GASAN BCAP CCAP CT2_resize.
Definition FUEL16 : nat := 4000.

(* [comment removed for export] *)
Definition frame : list kentry :=
  [ KWord (SA e_sp (-8)) 8 (EVar 0); KWord (SA e_sp (-16)) 8 (EVar 7); KWord (SA e_sp (-24)) 8 (EVar 8);
    KWord (SA e_sp (-32)) 8 (EVar 17); KWord (SA e_sp (-40)) 8 (EVar 18); KWord (SA e_sp (-48)) 8 (EVar 19);
    KWord (SA e_sp (-56)) 8 (EVar 20); KWord (SA e_sp (-64)) 8 (EVar 21); KWord (SA e_sp (-72)) 8 (EVar 22); KWord (SA e_sp (-80)) 8 (EVar 23) ].

(* [comment removed for export] *)
Definition D1 := EVar 100. Definition S1 := EVar 101. Definition A1 := EVar 102. Definition BV := EVar 103. Definition MTR1 := EVar 104.
Definition csregs_ra : list nat := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
Definition srl3 (e : expr) : expr := EAlu ALU_SRL e (ELit 3).
(* [comment removed for export] *)
Definition regs_mid (v : nat) : list expr :=
  sr_havoc (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd regsW
    2 (eaddz e_sp (-80))) 8 (eaddz C 8)) 9 PIX) 18 T) 19 OBJ) 20 (ELit SB))
    21 (eaddz (srl3 C) (SB + 1))) 22 (eaddz (srl3 PIX) SB)) 23 (eaddz (srl3 C) (SB - 1))) 24 (eaddz (srl3 OBJ) SB)) csregs_ra v.
(* [comment removed for export] *)
Definition room (m : smode) : list kentry :=
  match m with MS => [KRange (esub (EVar 100) IX) 8 (2 ^ 40)] | ML => [KRange (esub S1 IX) 8 (2 ^ 37)] end.
(* [comment removed for export] *)
Definition sz1 (m : smode) : expr := match m with MS => EVar 100 | ML => S1 end.
Definition mfacts1 (m0 m : smode) : list kentry :=
  [ ] ++ pw_facts CPW (sz1 m) MTR1 ++ [
    KRange (esub MTR1 e_mtr) 0 GROWMAX; KRange MTR1 0 MTRJ ].
Definition mkcsJ (p : Z) (regs : list expr) (k : list kentry) (nx : nat) (vis : list (expr * expr)) : acs :=
  ACS (mk_ss p regs k nx) [] 0 FRK 0 vis WS 0 e_sp FdStd false MTR1 [] e_fb.
Definition JS1 (m0 m : smode) (B : Z) : acs :=
  mkcsJ (JOIN1 B) (regs_mid 105)
       (room m ++ mfacts1 m0 m ++ [KWord (SA C (-8)) 2 BV; KRange BV 0 65535; KRange REM 2 REMHI] ++ frame
        ++ [KWord (SA G 0) 4 ERR; KRange ERR 0 0; KWord (SA PIT 0) 8 IT0; KWord (SA PIX 0) 8 IX; KRange IX 0 BIG;
            KRange (esub (escale 24 (esub IT0 INLO)) IX) 0 BIG]
        ++ str m IX IT0 100 ++ kn_fixed)
       140 (vis m 100).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition PH : nat := 255.   (* [comment removed for export] *)
Definition XPH : expr := EVar PH.
(* [comment removed for export] *)
Definition RSZID (m : smode) : nat := match m with MS => 104%nat | ML => 114%nat end.
Definition RSZ (m : smode) : list expr :=
  match m with MS => resize_args_S D e_mtr e_fb | ML => resize_args_L D S A e_mtr e_fb end.

(* [comment removed for export] *)
Definition exit_chain (m : smode) (k : plan) : plan :=
  let cons' := esub (eaddz IT0 2) INLO in
  PFactLe cons' (eadd (esub IT0 INLO) REM) INSZ
  (PFact (KRange ITO 1 (INSZ - 2))
  (PFactLeX 11 PH XPH (escale 24 cons') IXHI
  (PFactLeX 11 PH (esub (escale 24 cons') XPH) (escale 24 cons') BIG
  (match m with
   | ML => PFactLeX 11 PH (capexpr XPH (eaddz IT0 2) INLO A1) (eaddz (escale 104 cons') CAPK) (4 * IXHI + 8 * INSZ + CAPK) k
   | MS => k end)))).
Definition NEWSZ : expr := eaddz (escale 2 IX) 16.        (* [comment removed for export] *)
Definition EXITOK (m : smode) : plan := exit_chain m (PRun [] (PHandoffW (hole m) [(47%nat, ELit 2)])).
Definition EXITERR (m : smode) : plan := PRun [] (PHandoffW (hole m) [(47%nat, ELit 0)]).       (* [comment removed for export] *)

Definition xl (k : plan) : plan := PRun [] (PExt 0 [] k).         (* [comment removed for export] *)
Definition fin (B : Z) (m : smode) : plan := PRun [STIX B] (EXITOK m).     (* [comment removed for export] *)
Section Arms.
Variable B : Z.
Definition armA (m : smode) : plan := xl (xl (fin B m)).                                                           (* [comment removed for export] *)
Definition armB (m : smode) : plan := divfact BV (q100 BV) 100 (zfact BV (q100 BV) 100 (xl (xl (xl (fin B m))))).  (* [comment removed for export] *)
Definition q4 : expr := EMd M_MULHU BV (ELit 0x68db8bac710cc).
Definition r4 : expr := rem BV q4 10000.
Definition armC (m : smode) : plan :=                                                                            (* [comment removed for export] *)
  divfact BV q4 10000 (divfact r4 (q100w r4) 100 (zfact r4 (q100w r4) 100 (xl (xl (fin B m))))).
Definition digits (m : smode) : plan :=
  PCase2 BV 9 (armA m) (PCase2 BV 99 (armA m) (PCase2 BV 999 (armB m) (PCase2 BV 9999 (armB m) (armC m)))).
Definition after1 (m : smode) : plan :=
  match m with ML => PFactVia (esub (escale 8 A1) IX) (esub S1 IX) 9 (2 ^ 40) (digits ML) | MS => digits MS end.
(* [comment removed for export] *)
Definition okArm (m : smode) : plan :=
  PRun [] (PRun [] (PViaM 1 (match m with MS => [(JS1 MS MS B, after1 MS); (JS1 MS ML B, after1 ML)] | ML => [(JS1 ML ML B, after1 ML)] end) 100
     (PBranch (PRun [JOIN1 B] (PMerge 1))                                                        (* [comment removed for export] *)
              (PRun [] (PExt2 (RSZID m) (RSZ m)
                          (PExt 49 [e_mtr; szin m; NEWSZ; CPW; ELit 1] (PRun [JOIN1 B] (PMerge 1)))          (* [comment removed for export] *)
                          (PExt 49 [e_mtr; szin m; NEWSZ; CPW; ELit 0] (PRun [JOIN1 B] (PMerge 1)))))))).     (* [comment removed for export] *)
Definition PLAN (m : smode) : plan := PCase2 REM 1 (EXITERR m) (okArm m).
End Arms.

Lemma w16_gplan : forall B m, gplan_ok (PLAN B m) = true. Proof. intros B [|]; reflexivity. Qed.

