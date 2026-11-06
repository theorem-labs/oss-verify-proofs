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

Definition ENTRY : Z := 0xbe088.
Definition RETPC : Z := 0xbe760.
Definition AFTER : Z := 0xbe164.      (* [comment removed for export] *)
Definition BRSZ : Z := 0xbe160.       (* [comment removed for export] *)
Definition HEAD1 : Z := 0xbe288.      (* [comment removed for export] *)
Definition MID : Z := 0xbe570.        (* [comment removed for export] *)
Definition HEAD2 : Z := 0xbe594.
       (* [comment removed for export] *)
Definition NINSTR : nat := 519%nat.
Definition IT : itab := mk_itab_ranges ASEGS [(ENTRY, NINSTR)].
Lemma IT_ok : itab_sound ASEGS IT. Proof. apply APS.mk_itab_ranges_sound. Qed.

(* [comment removed for export] *)
Definition regsW : list expr := sr_upd regs0 4 (ELit (g_tp GASAN)).
Definition SV : expr := EVar 9.         (* [comment removed for export] *)
Definition G : expr := EVar 10.         (* [comment removed for export] *)
Definition OBJ : expr := EVar 11.       (* [comment removed for export] *)
Definition PIX : expr := EVar 12.       (* [comment removed for export] *)
Definition ITO : expr := EVar 31.       (* [comment removed for export] *)
Definition N : expr := EVar 32.         (* [comment removed for export] *)
Definition BSZ : expr := EVar 33.       (* [comment removed for export] *)
Definition IX : expr := EVar 34.        (* [comment removed for export] *)
Definition INLO : expr := EVar 35.      (* [comment removed for export] *)
Definition IT0 : expr := eadd INLO ITO.
Definition Ss : expr := EVar 36.        (* [comment removed for export] *)
Definition D : expr := EVar 36.  Definition S : expr := EVar 37.  Definition A : expr := EVar 38.
Definition e_mtr : expr := EVar 39.
Definition e_fb : expr := EVar 40.
Definition NXF : nat := 41.
Definition INSZ : Z := 2 ^ 26.
Definition BIG : Z := 24 * INSZ.
Definition REMHI : Z := INSZ.
Definition IXHI : Z := BIG.
Definition CAPK : Z := 1040.
Definition AHI : Z := (4 * IXHI + 8 * INSZ + CAPK) / 8.
Definition FR : Z := 144.
Definition FRK : Z := FR + AzStrResizeT.FRK.          (* [comment removed for export] *)
Definition flo (x : expr) (n : expr) : kentry := KDisj (SA x 0) n (SA e_sp (- FRK)) (ELit (FRK + WSTK)).
Definition NBE : Z := 13 * 2^28 + 80.                 (* [comment removed for export] *)
Definition GEV : Z := 2 * EVT + 8.
Definition MTRJ : Z := MTRMAX NBE.
Definition GROWMAX : Z := kcost (2 * NBE + 8) + KFREE.  (* [comment removed for export] *)
(* [comment removed for export] *)
Definition CPW : expr := EVar 3.
Definition CMAX : Z := MTRJ - pwtop NBE - pwtop (8 * AHI).   (* [comment removed for export] *)
Definition MTRIN : Z := MTRJ.

Definition IXHI2 : Z := IXHI + 2 * REMHI + 64.
Definition CAPHI : Z := 4 * IXHI2 + 8 * INSZ + CAPK.
Definition capexpr (ix it inlo a : expr) : expr := esub (eaddz (eadd (escale 4 ix) (escale 8 (esub it inlo))) CAPK) (escale 8 a).
Definition capfact (ix it inlo a : expr) : kentry := KRange (capexpr ix it inlo a) 0 CAPHI.
Definition strL (ix it d s a : expr) : list kentry :=
  [ KWord (SA OBJ 0) 8 (eaddz (escale 8 a) 1); KWord (SA OBJ 8) 8 s; KWord (SA OBJ 16) 8 d;
    KRange a 3 AHI; capfact ix it INLO a;
    KRange s 0 (8 * AHI); KRange (esub (escale 8 a) s) 1 (8 * AHI);
    KRange d PTRLO (PTRHI - 24); KRange (eadd d (escale 8 a)) (PTRLO + 24) PTRHI; KAlign d 16;
    KWr (SA d 0) (escale 8 a); KUnk (SA d 0) (escale 8 a); KShOk (SA d 0) (escale 8 a);
    KDisj (SA d 0) (escale 8 a) (SA G 0) (ELit 4); KDisj (SA d 0) (escale 8 a) (SA OBJ 0) (ELit 24);
    KDisj (SA d 0) (escale 8 a) (SA PIX 0) (ELit 8); KDisj (SA d 0) (escale 8 a) (SA INLO 0) BSZ;
    KDisj (SA d 0) (escale 8 a) (SA e_sp (- FRK)) (ELit (AzStrResizeT.FRK + WSTK));   (* [comment removed for export] *)
    img_apart d 0 (escale 8 a); shmap_apart d 0 (escale 8 a) ].
Definition str (m : smode) (ix it : expr) (v : nat) : list kentry :=
  match m with MS => strS OBJ (EVar v) | ML => strL ix it (EVar v) (EVar (1 + v)) (EVar (2 + v)) end.
Definition vis (m : smode) (v : nat) : list (expr * expr) :=
  match m with MS => [] | ML => [(EVar v, escale 8 (EVar (2 + v)))] end.
(* [comment removed for export] *)
Definition TBL : Z := 0x310d0.
Definition CTZ : Z := 0x22acc.

   (* [comment removed for export] *)
Definition tbl_shadow : list kentry := GLZ_LOWSH.   (* [comment removed for export] *)
Definition kn_fixed : list kentry :=
  [ KRange G PTRLO (objhi 4); KWr (SA G 0) (ELit 4); KShOk (SA G 0) (ELit 4); KAlign G 4;
    KRange OBJ PTRLO (objhi 24); KWr (SA OBJ 0) (ELit 24); KUnk (SA OBJ 0) (ELit 24); KShOk (SA OBJ 0) (ELit 24); KAlign OBJ 8;
    KRange PIX PTRLO (objhi 8); KWr (SA PIX 0) (ELit 8); KShOk (SA PIX 0) (ELit 8); KAlign PIX 8;
    KRange INLO PTRLO PTRHI; KRange BSZ 1 INSZ; KRange (eadd INLO BSZ) (PTRLO + 1) PTRHI; KUnk (SA INLO 0) BSZ; KShOk (SA INLO 0) BSZ;
    KRange ITO 0 INSZ; KRange N 0 REMHI; KRange (esub BSZ (eadd ITO N)) 0 INSZ;                 (* [comment removed for export] *)
    KDisj (SA G 0) (ELit 4) (SA OBJ 0) (ELit 24); KDisj (SA G 0) (ELit 4) (SA PIX 0) (ELit 8); KDisj (SA PIX 0) (ELit 8) (SA OBJ 0) (ELit 24);
    KDisj (SA INLO 0) BSZ (SA G 0) (ELit 4); KDisj (SA INLO 0) BSZ (SA OBJ 0) (ELit 24); KDisj (SA INLO 0) BSZ (SA PIX 0) (ELit 8);
    KAlign e_sp 16; KRange e_sp (CEIL + 8192) (two47 - 16); KWr (SA e_sp (- FRK)) (ELit FRK);
    KRange e_mtr 0 MTRIN; KRange CPW 0 CMAX;
    flo G (ELit 4); flo OBJ (ELit 24); flo PIX (ELit 8); flo INLO BSZ;
    img_apart G 0 (ELit 4); shmap_apart G 0 (ELit 4); img_apart OBJ 0 (ELit 24); shmap_apart OBJ 0 (ELit 24);
    img_apart PIX 0 (ELit 8); shmap_apart PIX 0 (ELit 8); img_apart INLO 0 BSZ; shmap_apart INLO 0 BSZ;
    KIMGA; fb_fact e_fb ] ++ NEWH ++ RTC ++ tbl_shadow.   (* [comment removed for export] *)
Definition stk_shok : kentry := KShOk (SA e_sp (- FRK)) (ELit FRK).   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sv_facts : list kentry :=
  [ KRange SV (CEIL + FRK) (HI47 - 16); KRange (esub SV e_sp) 0 (2 ^ 46); KWord (SA SV 0) 8 IT0; KWord (SA SV 8) 8 N; KShOk (SA SV 0) (ELit 16); KAlign SV 8;
    img_apart SV 0 (ELit 16) ].
Definition kn_in (m : smode) : list kentry :=
  [ KWord (SA G 0) 4 (ELit 0); KWord (SA PIX 0) 8 IX; KRange IX 0 BIG; stk_shok ] ++ pw_facts CPW (match m with MS => EVar 36 | ML => S end) e_mtr ++ sv_facts ++ str m IX IT0 36 ++ kn_fixed.
Definition WS : list (expr * expr) := [(G, ELit 4); (PIX, ELit 8); (OBJ, ELit 24); (INLO, BSZ)].
Definition mkcs (p : Z) (regs : list expr) (k : list kentry) (nx : nat) (vs : list (expr * expr)) (mtr : expr) : acs :=
  ACS (mk_ss p regs k nx) [] 0 FRK 0 vs WS 0 e_sp FdStd false mtr [] e_fb.
Definition tin (m : smode) : acs := mkcs ENTRY regsW (kn_in m) NXF (vis m 36) e_mtr.

(* [comment removed for export] *)
Definition frame : list kentry :=
  [ KWord (SA e_sp (-8)) 8 (EVar 0); KWord (SA e_sp (-16)) 8 (EVar 7); KWord (SA e_sp (-24)) 8 (EVar 8);
    KWord (SA e_sp (-32)) 8 (EVar 17); KWord (SA e_sp (-40)) 8 (EVar 18); KWord (SA e_sp (-48)) 8 (EVar 19);
    KWord (SA e_sp (-56)) 8 (EVar 20); KWord (SA e_sp (-64)) 8 (EVar 21); KWord (SA e_sp (-72)) 8 (EVar 22);
    KWord (SA e_sp (-80)) 8 (EVar 23); KWord (SA e_sp (-88)) 8 (EVar 24); KWord (SA e_sp (-96)) 8 (EVar 25); KWord (SA e_sp (-104)) 8 (EVar 26) ].

(* [comment removed for export] *)
Definition xERR := EVar 41. Definition xIX := EVar 42.
Definition XSTR : nat := 43. Definition xMTR := EVar 46. Definition XLO : nat := 47.
Definition clobbered : list nat := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
Definition regs_out : list expr := sr_havoc regsW clobbered XLO.
Definition szin (m : smode) : expr := match m with MS => EVar 36 | ML => S end.
Definition szx (m : smode) : expr := match m with MS => EVar 43 | ML => EVar 44 end.
Definition kn_out (m0 m : smode) : list kentry :=
  [ KWord (SA G 0) 4 xERR; KRange xERR 0 70; KWord (SA PIX 0) 8 xIX; KRange xIX 0 IXHI2;
    KRange (esub (eaddz (eadd IX (escale 2 N)) 2) xIX) 0 IXHI2                              (* [comment removed for export] *)
    ] ++ pw_facts CPW (szx m) xMTR ++ [                       (* [comment removed for export] *)
    KRange (esub xMTR e_mtr) 0 MTRJ; KRange xMTR 0 MTRJ ]
  ++ str m xIX (eadd IT0 N) XSTR ++ no_cbound CPW kn_fixed.
Definition tout (m0 m : smode) : acs := mkcs RETPC regs_out (kn_out m0 m) (XLO + 15)%nat (vis m XSTR) xMTR.
Definition BCAP : Z := 10 * 2 ^ 30.  Definition CCAP : Z := 2.
Definition ce2 (m : smode) : gcallee2 := GCE2 NXF (tin m) [tout m MS] [tout m ML] BCAP CCAP.
Definition ce (m : smode) : gcallee := c2_merged (ce2 m).
Definition ceL1 : gcallee := GCE NXF (tin ML) [tout ML ML; tout ML ML] BCAP CCAP.
Definition XN : nat -> list expr -> acs -> option acs := XNw (XNc ASEGS IT AASAN NXF GASAN BCAP CCAP CT0).   (* [comment removed for export] *)
Definition XB : nat -> list expr -> acs -> option (acs * acs) := XBc ASEGS AASAN NXF GASAN BCAP CCAP CT2_resize.
Definition FUEL : nat := 4000.
Definition DPATH (m : smode) := dpath ASEGS IT AASAN XN XB BFUEL NXF (tin m).

(* [comment removed for export] *)
Definition REQ : expr := eaddz (eadd IX (escale 2 N)) 10.          (* [comment removed for export] *)
Definition JLO : nat := 60.
Definition MTR1 : expr := EVar 63.
Definition srl3 (e : expr) : expr := EAlu ALU_SRL e (ELit 3).
Definition shad (x : expr) : expr := eaddz (srl3 x) SB.            (* [comment removed for export] *)
Definition cl_after : list nat := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
Definition regs_base : list expr :=
  sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd regsW
    2 (eaddz e_sp (- FR))) 8 PIX) 9 OBJ) 19 IT0) 20 (ELit SB)) 21 (shad PIX)) 22 (shad OBJ)) 23 N.
Definition regs_after (v : nat) : list expr := sr_havoc regs_base cl_after v.
Definition room (m : smode) (v : nat) : list kentry :=
  match m with
  | MS => [KRange (esub (EVar v) REQ) 0 22]                                   (* [comment removed for export] *)
  | ML => [KRange (esub (escale 8 (EVar (2 + v))) (eaddz REQ 1)) 0 (8 * AHI);  (* [comment removed for export] *)
           KRange (esub (EVar (1 + v)) REQ) 0 (8 * AHI)]                      (* [comment removed for export] *)
  end.
(* [comment removed for export] *)
Definition sz1 (m : smode) : expr := match m with MS => EVar 60 | ML => EVar 61 end.
Definition mfacts1 (m0 m : smode) : list kentry :=
  [ ] ++ pw_facts CPW (sz1 m) MTR1 ++ [
    KRange (esub MTR1 e_mtr) 0 GROWMAX; KRange MTR1 0 MTRJ ].
Definition spillG : list kentry := [KWord (SA e_sp (-120)) 8 G].           (* [comment removed for export] *)
Definition kn_after (m0 m : smode) (v : nat) : list kentry :=
  frame ++ spillG ++ [KWord (SA G 0) 4 (ELit 0); KWord (SA PIX 0) 8 IX; KRange IX 0 BIG] ++ str m IX (eadd IT0 N) v ++ room m v ++ mfacts1 m0 m ++ kn_fixed.
Definition JSA (m0 m : smode) : acs := mkcs AFTER (regs_after 64) (kn_after m0 m JLO) 80 (vis m JLO) MTR1.

(* [comment removed for export] *)
Definition SD : expr := EVar 60.
  Definition SA8 : expr := EVar 62.   (* [comment removed for export] *)
Definition DATA (m : smode) : expr := match m with MS => eaddz OBJ 1 | ML => SD end.
Definition P0 (m : smode) : expr := eaddz (eadd (DATA m) IX) 1.        (* [comment removed for export] *)
Definition EEND : expr := eadd IT0 N.                                    (* [comment removed for export] *)
(* [comment removed for export] *)
Definition GK3 : expr := eaddz (EAlu ALU_AND G (ELit 7)) 3.
Definition spills0 (m : smode) : list kentry := spillG ++ [KWord (SA e_sp (-112)) 8 (P0 m)].                 (* [comment removed for export] *)
Definition spills (m : smode) : list kentry := spills0 m ++ [KWord (SA e_sp (-128)) 8 (shad G); KWord (SA e_sp (-136)) 8 GK3].   (* [comment removed for export] *)
Definition kn_post (m0 m : smode) (err : expr) : list kentry :=             (* [comment removed for export] *)
  frame ++ [KWord (SA G 0) 4 err; KRange err 0 70; KWord (SA PIX 0) 8 (eaddz IX 1); KRange IX 0 BIG]
  ++ str m IX EEND JLO ++ room m JLO ++ mfacts1 m0 m ++ kn_fixed.
(* [comment removed for export] *)
Definition K_T0 : Z := 9187201950435737471.  Definition K_T1 : Z := 2459565876494606882.  Definition K_T2 : Z := 6655295901103053916.
Definition K_A7 : Z := 9259542123273814144.  Definition K_T3 : Z := 6944656592455360608.  Definition K_T4 : Z := 151050438420815295.

(* [comment removed for export] *)
Definition J1 : expr := EVar 90.
Definition DC := EVar 91. Definition DP := EVar 92. Definition ERR1 := EVar 93.
Definition ROOMP (m : smode) : expr := match m with MS => esub (ELit 21) IX | ML => esub (eaddz (escale 8 SA8) (-2)) IX end.
Definition regs_l1 : list expr :=
  sr_havoc (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd regs_base
    5 (ELit K_T0)) 6 (ELit K_T1)) 7 (ELit K_T2)) 10 (eadd (P0 ML) DP)) 14 EEND) 15 (ELit TBL)) 16 (eaddz EEND (-7)))
    17 (ELit K_A7)) 19 (eadd IT0 DC)) 28 (ELit K_T3)) 29 (ELit K_T4)) 30 (ELit CTZ))
   [1; 11; 12; 13; 18; 23; 24; 25; 26; 27; 31]%nat 94.
Definition facts1 (dc dp : expr) : list kentry :=
  [ KRange dc 0 REMHI; KRange (esub dc J1) 0 REMHI; KRange (esub N dc) 8 REMHI; KRange (esub (eaddz N (-7)) J1) 1 REMHI;
    KRange (esub (escale 2 dc) dp) 0 (2 * REMHI); KRange dp 0 (2 * REMHI + 16);
    KRange (eaddz (esub (esub (ROOMP ML) dp) (escale 2 (esub N dc))) (-8)) 0 (8 * AHI) ].

  (* [comment removed for export] *)
Definition INV1m (m0 : smode) : acs := mkcs HEAD1 regs_l1 (facts1 DC DP ++ spills ML ++ kn_post m0 ML ERR1) 105 (vis ML JLO) MTR1.

(* [comment removed for export] *)
Definition J2 : expr := EVar 150.
Definition DC2 := EVar 151. Definition DP2 := EVar 152. Definition ERR2 := EVar 153.
Definition regs_l2 (m : smode) : list expr :=
  sr_havoc (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd regs_base
    5 GK3) 6 (ELit 70)) 10 (eadd (P0 m) DP2)) 11 (eadd IT0 DC2)) 14 EEND) 15 (ELit TBL)) 16 (ELit 31)) 17 (shad G)) 19 (eadd IT0 DC2))
   [1; 7; 12; 13; 18; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat 154.
Definition facts2 (m : smode) (dc dp : expr) : list kentry :=
  [ KRange dc 0 REMHI; KRange (esub dc J2) 0 REMHI; KRange (esub N dc) 1 REMHI; KRange (esub N J2) 1 REMHI;
    KRange (esub (escale 2 dc) dp) 0 (2 * REMHI); KRange dp 0 (2 * REMHI + 16);
    KRange (esub (esub (ROOMP m) dp) (escale 2 (esub N dc))) 0 (8 * AHI) ].
Definition INV2 (m0 m : smode) : acs := mkcs HEAD2 (regs_l2 m) (facts2 m DC2 DP2 ++ spills0 m ++ kn_post m0 m ERR2) 168 (vis m JLO) MTR1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition EXIT (m : smode) : plan := PRun [] (PHandoffW (match m with MS => 0 | ML => 1 end) []).
(* [comment removed for export] *)
Definition tail2 (m0 m : smode) : plan := PRun [0xbe634] (PCase2 (esub N (eaddz DC2 1)) 0 (EXIT m) (PRun [HEAD2] PNext)).
Definition body2 (m0 m : smode) : plan :=
  PRun [0xbe5c0] (PExt 42 [] (PRun [0xbe5c4] (PBranch
     (tail2 m0 m)                                                              (* [comment removed for export] *)
     (PRun [0xbe600] (PBranch (tail2 m0 m) (tail2 m0 m)))))).                   (* [comment removed for export] *)
Definition loop2 (m0 m : smode) : plan := PLoop 150 N (INV2 m0 m) [] (body2 m0 m) (PContraH 0).
Definition at_mid (m0 m : smode) : plan := PRun [MID] (PBranch (PRun [HEAD2] (loop2 m0 m)) (EXIT m)).
Definition tail1 (m0 : smode) : plan := PRun [0xbe488] (PExt 42 [] (PRun [0xbe4b8] (PBranch (at_mid m0 ML) (PRun [HEAD1] PNext)))).
Definition body1 (m0 : smode) : plan :=
  PRun [0xbe3e8] (PBranch
    (PRun [0xbe3f4] (PBranch (at_mid m0 ML) (PRun [HEAD1] PNext)))           (* [comment removed for export] *)
    (PRun [0xbe414] (PExt 42 [] (PRun [0xbe44c] (PExt 42 [] (PRun [0xbe450] (PBranch (tail1 m0) (tail1 m0)))))))).  (* [comment removed for export] *)
Definition loop1 (m0 : smode) : plan := PLoop 90 (eaddz N (-7)) (INV1m m0) [] (body1 m0) (PContraH 0).
Definition afterA (m0 m : smode) : plan :=
  match m with
  | MS => PFact (KRange N 0 6) (at_mid m0 MS)
  | ML => PRun [0xbe220] (PBranch (PRun [HEAD1] (loop1 m0)) (at_mid m0 ML))
  end.
Definition NEWSZ : expr := eaddz (eadd (escale 2 IX) (escale 4 N)) 20.      (* [comment removed for export] *)
Definition RSZID (m : smode) : nat := match m with MS => 106%nat | ML => 116%nat end.
Definition RSZ (m : smode) : list expr := match m with MS => resize_args_S Ss e_mtr e_fb | ML => resize_args_L D S A e_mtr e_fb end.
Definition plan (m : smode) : plan :=
  PViaM 0 (match m with MS => [(JSA MS MS, afterA MS MS); (JSA MS ML, afterA MS ML)] | ML => [(JSA ML ML, afterA ML ML)] end) JLO
    (PRun [BRSZ] (PBranch
       (PRun [AFTER] (PMerge 0))                                                        (* [comment removed for export] *)
       (PRun [] (PExt2 (RSZID m) (RSZ m)
                   (PExt 49 [e_mtr; szin m; NEWSZ; CPW; ELit 1] (PRun [AFTER] (PMerge 0)))              (* [comment removed for export] *)
                   (PExt 49 [e_mtr; szin m; NEWSZ; CPW; ELit 0] (PRun [AFTER] (PMerge 0))))))).

(* [comment removed for export] *)
Definition CUTE (t : acs) (k : AP.plan) : AP.plan := PViaM 199 [(t, k)] (nxt t) (PMerge 199).
Definition CUTS_E : list (acs * AP.plan) := [(JSA ML ML, CUTE (JSA ML ML) (afterA ML ML))].
Definition HC : nat := 2.
Definition diamondX (m : smode) (kroom kkept kgrown : AP.plan) : AP.plan :=
  PRun [BRSZ] (PBranch
     (PRun [AFTER] kroom)
     (PRun [] (PExt2 (RSZID m) (RSZ m)
                 (PExt 49 [e_mtr; szin m; NEWSZ; CPW; ELit 1] (PRun [AFTER] kkept))
                 (PExt 49 [e_mtr; szin m; NEWSZ; CPW; ELit 0] (PRun [AFTER] kgrown))))).
Definition planX (m : smode) : AP.plan :=
  match m with
  | MS => PViaM 0 [(JSA MS MS, afterA MS MS)] JLO (diamondX MS (PMerge 0) (PMerge 0) (PHandoffW HC []))
  | ML => diamondX ML (PHandoffW HC []) (PHandoffW HC []) (PHandoffW HC [])
  end.
Lemma esc_gplanX : forall m, gplan_ok (planX m) = true. Proof. intros [|]; reflexivity. Qed.
Lemma esc_gplanC : gplan_ok (CUTE (JSA ML ML) (afterA ML ML)) = true. Proof. reflexivity. Qed.
Lemma tout_L : tout MS ML = tout ML ML. Proof. reflexivity. Qed.

