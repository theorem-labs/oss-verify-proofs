(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzDev OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition img_apart (x : expr) (k : Z) (n : expr) : kentry := KDisj (SA x k) n (SA (ELit 0) 0x10000) (ELit 0x97000).

Definition ENTRY : Z := 0x39a28.
Definition RETPC : Z := 0x39d60.
Definition AFTER : Z := 0x39a98.      (* [comment removed for export] *)
Definition HEAD1 : Z := 0x39b38.      (* [comment removed for export] *)
Definition MID : Z := 0x39c84.        (* [comment removed for export] *)
Definition HEAD2 : Z := 0x39c9c.      (* [comment removed for export] *)
Definition DONE : Z := 0x39cf0.       (* [comment removed for export] *)
Definition IT : itab := mk_itab_ranges PSEGS [(ENTRY, 214%nat)].
Lemma IT_ok : itab_sound PSEGS IT. Proof. apply APS.mk_itab_ranges_sound. Qed.

(* [comment removed for export] *)
Definition regs0 : list expr := sr_upd (ELit 0 :: map EVar (seq 0 31)) 4 (ELit (g_tp GPLAIN)).
Definition e_sp : expr := EVar 1.
Definition SV : expr := EVar 9.         (* [comment removed for export] *)
Definition G : expr := EVar 10.         (* [comment removed for export] *)
Definition OBJ : expr := EVar 11.       (* [comment removed for export] *)
Definition ITO : expr := EVar 31.       (* [comment removed for export] *)
Definition N : expr := EVar 32.         (* [comment removed for export] *)
Definition BSZ : expr := EVar 33.       (* [comment removed for export] *)
Definition IX : expr := EVar 34.        (* [comment removed for export] *)
Definition INLO : expr := EVar 35.      (* [comment removed for export] *)
Definition IT0 : expr := eadd INLO ITO.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition Ss : expr := EVar 36.
Definition D : expr := EVar 36.  Definition S : expr := EVar 37.  Definition A : expr := EVar 38.
Definition NXF : nat := 39.
Definition PTRHI : Z := GlzConst.HI47.   (* [comment removed for export] *)
Definition INSZ : Z := 2 ^ 26.
Definition BIG : Z := 24 * INSZ.
Definition REMHI : Z := INSZ.
Definition IXHI : Z := BIG.
Definition CAPK : Z := 1040.
Definition AHI : Z := (4 * IXHI + 8 * INSZ + CAPK) / 8.
Definition FR : Z := 96.                         (* [comment removed for export] *)
Definition FRS : Z := FR + MSTK.                 (* [comment removed for export] *)

Definition IXHI2 : Z := IXHI + 2 * REMHI + 64.         (* [comment removed for export] *)
Definition CAPHI : Z := 4 * IXHI2 + 8 * INSZ + CAPK.
Definition capexpr (ix it inlo a : expr) : expr := esub (eaddz (eadd (escale 4 ix) (escale 8 (esub it inlo))) CAPK) (escale 8 a).
Definition capfact (ix it inlo a : expr) : kentry := KRange (capexpr ix it inlo a) 0 CAPHI.

(* [comment removed for export] *)
Definition strL (ix it d s a : expr) : list kentry :=
  [ KWord (SA OBJ 0) 8 (eaddz (escale 8 a) 1); KWord (SA OBJ 8) 8 s; KWord (SA OBJ 16) 8 d;
    KRange a 3 AHI; capfact ix it INLO a;
    KRange s 0 (8 * AHI); KRange (esub (escale 8 a) s) 1 (8 * AHI);
    KRange d PTRLO (PTRHI - 24); KRange (eadd d (escale 8 a)) (PTRLO + 24) PTRHI; KAlign d 16;
    KWr (SA d 0) (escale 8 a); KUnk (SA d 0) (escale 8 a);
    KDisj (SA d 0) (escale 8 a) (SA G 0) (ELit 112); KDisj (SA d 0) (escale 8 a) (SA OBJ 0) (ELit 24);
    KDisj (SA d 0) (escale 8 a) (SA SV 0) (ELit 16); KDisj (SA d 0) (escale 8 a) (SA INLO 0) BSZ;
    KDisj (SA d 0) (escale 8 a) (SA e_sp (- FRS)) (ELit (FRS + WSTK)); img_apart d 0 (escale 8 a) ].
Definition strS (s : expr) : list kentry :=
  [ KWord (SA OBJ 0) 1 (escale 2 s); KRange s 0 22 ].
Definition str (m : smode) (ix it : expr) (v : nat) : list kentry :=
  match m with MS => strS (EVar v) | ML => strL ix it (EVar v) (EVar (1 + v)) (EVar (2 + v)) end.
Definition vis (m : smode) (v : nat) : list (expr * expr) :=
  match m with MS => [] | ML => [(EVar v, escale 8 (EVar (2 + v)))] end.

Definition kn_fixed : list kentry :=
  [ KRange G CEIL PTRHI; KWr (SA G 0) (ELit 4); KWr (SA G 104) (ELit 8);
    KRange OBJ CEIL PTRHI; KWr (SA OBJ 0) (ELit 24); KUnk (SA OBJ 0) (ELit 24);
    KRange SV CEIL PTRHI; KWord (SA SV 0) 8 IT0; KWord (SA SV 8) 8 N;
    KRange INLO PTRLO PTRHI; KRange BSZ 1 INSZ; KRange (eadd INLO BSZ) (PTRLO + 1) PTRHI; KUnk (SA INLO 0) BSZ; KDisj (SA INLO 0) BSZ (SA e_sp (- FRS)) (ELit (FRS + WSTK)); img_apart INLO 0 BSZ;   (* [comment removed for export] *)
    KRange ITO 0 INSZ; KRange N 0 REMHI; KRange (esub BSZ (eadd ITO N)) 0 INSZ;                               (* [comment removed for export] *)
    KDisj (SA G 0) (ELit 112) (SA OBJ 0) (ELit 24); KDisj (SA G 0) (ELit 112) (SA SV 0) (ELit 16);
    KDisj (SA OBJ 0) (ELit 24) (SA SV 0) (ELit 16);
    KDisj (SA INLO 0) BSZ (SA G 0) (ELit 112); KDisj (SA INLO 0) BSZ (SA OBJ 0) (ELit 24); KDisj (SA INLO 0) BSZ (SA SV 0) (ELit 16);
                                                      (* [comment removed for export] *)
    KAlign e_sp 16; KRange e_sp (CEIL + 8192) PTRHI; KWr (SA e_sp (- FRS)) (ELit FRS);
    KRange (esub G e_sp) 0 (2 ^ 47); KRange (esub OBJ e_sp) 0 (2 ^ 47); KRange (esub SV e_sp) 0 (2 ^ 47);
    KDisj (SA e_sp (- FRS)) (ELit FRS) (SA G 0) (ELit 112); KDisj (SA e_sp (- FRS)) (ELit FRS) (SA OBJ 0) (ELit 24);
    KDisj (SA e_sp (- FRS)) (ELit FRS) (SA SV 0) (ELit 16);
    KWr (SA G 0) (ELit 112); KWr (SA SV 0) (ELit 16);    (* [comment removed for export] *)
    KImg 0x10000 0x71000 ].
Definition kn_in (m : smode) : list kentry :=
  [ KWord (SA G 0) 4 (ELit 0); KWord (SA G 104) 8 IX; KRange IX 0 BIG ] ++ str m IX IT0 36 ++ kn_fixed.

Definition WS : list (expr * expr) := [(G, ELit 4); (eaddz G 104, ELit 8); (OBJ, ELit 24); (INLO, BSZ)].   (* [comment removed for export] *)
Definition mkcs (p : Z) (regs : list expr) (k : list kentry) (nx : nat) (vs : list (expr * expr)) : acs :=
  ACS (mk_ss p regs k nx) [] 0 FRS 0 vs WS 0 e_sp FdStd false.
Definition regs_in : list expr := sr_upd regs0 13 (eaddz G 104).     (* [comment removed for export] *)
Definition tin (m : smode) : acs := mkcs ENTRY regs_in (kn_in m) NXF (vis m 36).

(* [comment removed for export] *)
Fixpoint sr_havoc (sr : list expr) (ixs : list nat) (v : nat) : list expr :=
  match ixs with [] => sr | i :: t => sr_havoc (sr_upd sr i (EVar v)) t (Datatypes.S v) end.
Definition frame : list kentry :=
  [ KWord (SA e_sp (-8)) 8 (EVar 0); KWord (SA e_sp (-16)) 8 (EVar 7); KWord (SA e_sp (-24)) 8 (EVar 8);
    KWord (SA e_sp (-32)) 8 (EVar 17); KWord (SA e_sp (-40)) 8 (EVar 18); KWord (SA e_sp (-48)) 8 (EVar 19);
    KWord (SA e_sp (-56)) 8 (EVar 20); KWord (SA e_sp (-64)) 8 (EVar 21); KWord (SA e_sp (-72)) 8 (EVar 22);
    KWord (SA e_sp (-80)) 8 (EVar 23); KWord (SA e_sp (-88)) 8 (EVar 24) ].

(* [comment removed for export] *)
Definition xERR := EVar 39. Definition xIX := EVar 40.
Definition XSTR : nat := 41. Definition XLO : nat := 44.
Definition clobbered : list nat := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.  (* [comment removed for export] *)
Definition regs_out : list expr := sr_havoc regs0 clobbered XLO.
Definition kn_out (m : smode) : list kentry :=
  [ KWord (SA G 0) 4 xERR; KRange xERR 0 70; KWord (SA G 104) 8 xIX; KRange xIX 0 IXHI2;
    KRange (esub (eaddz (eadd IX (escale 2 N)) 2) xIX) 0 IXHI2 ]        (* [comment removed for export] *)
  ++ str m xIX (eadd IT0 N) XSTR ++ kn_fixed.
Definition tout (m : smode) : acs := mkcs RETPC regs_out (kn_out m) (XLO + 15)%nat (vis m XSTR).
Definition BCAP : Z := 10 * 2 ^ 30.  Definition CCAP : Z := 2.
(* [comment removed for export] *)
Definition ce2 (m : smode) : gcallee2 := GCE2 NXF (tin m) [tout MS] [tout ML] BCAP CCAP.
Definition ce (m : smode) : gcallee := c2_merged (ce2 m).

(* [comment removed for export] *)
Definition CT (id : nat) : option gcallee := None.
Definition XN : nat -> list expr -> acs -> option acs := XNc PSEGS IT APLAIN NXF GPLAIN BCAP CCAP CT.
Definition CT2 (id : nat) : option gcallee2 := None.
Definition XB : nat -> list expr -> acs -> option (acs * acs) := XBc PSEGS APLAIN NXF GPLAIN BCAP CCAP CT2.
Definition LIMIT : Z := 2 ^ 34.
Definition FUEL : nat := 4000.
Definition BFUEL : nat := 1000.

Definition DPATH := dpath PSEGS IT APLAIN XN XB BFUEL.

(* [comment removed for export] *)
Definition REQ : expr := eaddz (eadd IX (escale 2 N)) 10.          (* [comment removed for export] *)
Definition JLO : nat := 60.
Definition cl_after : list nat := [1; 5; 6; 7; 10; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
Definition regs_after (v : nat) : list expr :=
  sr_havoc (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd regs0
    2 (eaddz e_sp (- FR))) 8 (eaddz G 104)) 9 OBJ) 18 G) 19 IT0) 20 N) 11 IX) cl_after v.
Definition room (m : smode) (v : nat) : list kentry :=
  match m with
  | MS => [KRange (esub (EVar v) REQ) 0 22]                                   (* [comment removed for export] *)
  | ML => [KRange (esub (escale 8 (EVar (2 + v))) (eaddz REQ 1)) 0 (8 * AHI);  (* [comment removed for export] *)
           KRange (esub (EVar (1 + v)) REQ) 0 (8 * AHI)]                      (* [comment removed for export] *)
  end.
Definition kn_after (m : smode) (v : nat) : list kentry :=
  frame ++ [KWord (SA G 0) 4 (ELit 0); KWord (SA G 104) 8 IX; KRange IX 0 BIG] ++ str m IX (eadd IT0 N) v ++ room m v ++ kn_fixed.
Definition JSA (m : smode) : acs := mkcs AFTER (regs_after 63) (kn_after m JLO) 78 (vis m JLO).

(* [comment removed for export] *)
Definition SD : expr := EVar 60.
  Definition SA8 : expr := EVar 62.   (* [comment removed for export] *)
Definition DATA (m : smode) : expr := match m with MS => eaddz OBJ 1 | ML => SD end.
   (* [comment removed for export] *)
Definition P0 (m : smode) : expr := eaddz (eadd (DATA m) IX) 1.        (* [comment removed for export] *)
Definition EEND : expr := eadd IT0 N.                                    (* [comment removed for export] *)
Definition kn_post (m : smode) (err : expr) : list kentry :=             (* [comment removed for export] *)
  frame ++ [KWord (SA G 0) 4 err; KRange err 0 70; KWord (SA G 104) 8 (eaddz IX 1); KRange IX 0 BIG]
  ++ str m IX EEND JLO ++ room m JLO ++ kn_fixed.
Definition TBL : Z := 0x21590.   (* [comment removed for export] *)
Definition CTZ : Z := 0x131d0.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition J1 : expr := EVar 90.
Definition DC := EVar 91. Definition DP := EVar 92. Definition ERR1 := EVar 93.
Definition ROOMP (m : smode) : expr := match m with MS => esub (ELit 21) IX | ML => esub (eaddz (escale 8 SA8) (-2)) IX end.
   (* [comment removed for export] *)
Definition regs_l1 : list expr :=
  sr_havoc (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd
   (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd regs0
    1 (EVar 63)) 2 (eaddz e_sp (- FR))) 5 (ELit 6944656592455360608)) 6 (ELit 151050438420815295)) 7 (ELit CTZ))
    8 (eaddz G 104)) 9 OBJ) 10 (P0 ML)) 11 (eadd (P0 ML) DP)) 12 EEND) 13 (eaddz EEND (-7)))
    14 (ELit 9259542123273814144)) 15 (ELit 9187201950435737471)) 16 (ELit 2459565876494606882)) 17 (ELit 6655295901103053916))
    18 G) 19 (eadd IT0 DC)) 28 (ELit TBL)) 29 (ELit 70))
   [20; 21; 22; 23; 24; 25; 30; 31]%nat 94.
Definition facts1 (dc dp : expr) : list kentry :=
  [ KRange dc 0 REMHI; KRange (esub dc J1) 0 REMHI;                       (* [comment removed for export] *)
    KRange (esub N dc) 8 REMHI;                                            (* [comment removed for export] *)
    KRange (esub (eaddz N (-7)) J1) 1 REMHI;                               (* [comment removed for export] *)
    KRange (esub (escale 2 dc) dp) 0 (2 * REMHI);                          (* [comment removed for export] *)
    KRange dp 0 (2 * REMHI + 16);                                          (* [comment removed for export] *)
    KRange (eaddz (esub (esub (ROOMP ML) dp) (escale 2 (esub N dc))) (-8)) 0 (8 * AHI) ].   (* [comment removed for export] *)
Definition INV1 : acs := mkcs HEAD1 regs_l1 (facts1 DC DP ++ kn_post ML ERR1) 102 (vis ML JLO).

(* [comment removed for export] *)
Definition J2 : expr := EVar 150.
Definition DC2 := EVar 151. Definition DP2 := EVar 152. Definition ERR2 := EVar 153.
Definition regs_l2 (m : smode) : list expr :=
  sr_havoc (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd regs0
    2 (eaddz e_sp (- FR))) 8 (eaddz G 104)) 9 OBJ) 10 (P0 m)) 11 (eadd (P0 m) DP2)) 12 (esub N DC2)) 13 (ELit 31)) 14 (ELit TBL)) 15 (ELit 70))
    18 G) 19 (eadd IT0 DC2))
   [1; 5; 6; 7; 16; 17; 20; 21; 22; 23; 24; 25; 28; 29; 30; 31]%nat 154.
Definition facts2 (m : smode) (dc dp : expr) : list kentry :=
  [ KRange dc 0 REMHI; KRange (esub dc J2) 0 REMHI;                       (* [comment removed for export] *)
    KRange (esub N dc) 1 REMHI;                                            (* [comment removed for export] *)
    KRange (esub N J2) 1 REMHI;                                            (* [comment removed for export] *)
    KRange (esub (escale 2 dc) dp) 0 (2 * REMHI);                          (* [comment removed for export] *)
    KRange dp 0 (2 * REMHI + 16);                                          (* [comment removed for export] *)
    KRange (esub (esub (ROOMP m) dp) (escale 2 (esub N dc))) 0 (8 * AHI) ]. (* [comment removed for export] *)
Definition INV2 (m : smode) : acs := mkcs HEAD2 (regs_l2 m) (facts2 m DC2 DP2 ++ kn_post m ERR2) 170 (vis m JLO).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition EXIT (m : smode) : plan := PRun [] (PHandoffW (match m with MS => 0 | ML => 1 end) []).
(* [comment removed for export] *)
Definition tail2 (m : smode) : plan := PRun [0x39cdc] (PBranch (EXIT m) (PRun [HEAD2] PNext)).
Definition body2 (m : smode) : plan :=
  PRun [0x39ca8] (PExt 42 [] (PRun [0x39cac] (PBranch
     (tail2 m)                                                              (* [comment removed for export] *)
     (PRun [0x39cc4] (PBranch (tail2 m)                                     (* [comment removed for export] *)
                              (PRun [0x39cc8] (tail2 m))))))).              (* [comment removed for export] *)
Definition loop2 (m : smode) : plan := PLoop 150 N (INV2 m) [] (body2 m) (PContraH 0).
(* [comment removed for export] *)
Definition at_mid (m : smode) : plan := PRun [MID] (PBranch (PRun [HEAD2] (loop2 m)) (EXIT m)).
(* [comment removed for export] *)
Definition tail1 : plan := PRun [0x39c60; 0x39c08] (PBranch (at_mid ML) (PRun [HEAD1] PNext)).
Definition body1 : plan :=
  PRun [0x39bfc] (PBranch
    (PRun [0x39c08] (PBranch (at_mid ML) (PRun [HEAD1] PNext)))             (* [comment removed for export] *)
    (PRun [0x39c28] (PExt 42 [] (PRun [0x39c40] (PExt 42 [] (PRun [0x39c44] (PBranch
        tail1                                                               (* [comment removed for export] *)
        (PRun [0x39c78] (PExt 42 [] tail1))))))))).                         (* [comment removed for export] *)
Definition loop1 : plan := PLoop 90 (eaddz N (-7)) INV1 [] body1 (PContraH 0).
(* [comment removed for export] *)
Definition afterA (m : smode) : plan :=
  match m with
  | MS => PFact (KRange N 0 6) (at_mid MS)
  | ML => PRun [0x39ae4] (PBranch (PRun [HEAD1] loop1) (at_mid ML))
  end.
Definition RSZ (m : smode) : list expr := match m with MS => [ELit 0; Ss] | ML => [ELit 1; D; A; S] end.
Definition plan (m : smode) : plan :=
  PViaM 0 (match m with MS => [(JSA MS, afterA MS); (JSA ML, afterA ML)] | ML => [(JSA ML, afterA ML)] end) JLO
    (PRun [0x39a94] (PBranch
       (PRun [AFTER] (PMerge 0))                                                        (* [comment removed for export] *)
       (PRun [] (PExt2 31 (RSZ m) (PRun [AFTER] (PMerge 0)) (PRun [AFTER] (PMerge 0)))))).

Definition SHAPE : shape := SHole 0.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition CUTE (t : acs) (k : AP.plan) : AP.plan := PViaM 199 [(t, k)] (nxt t) (PMerge 199).
Definition CUTS_E : list (acs * AP.plan) := [(JSA ML, CUTE (JSA ML) (afterA ML))].
Definition HC : nat := 2.
Definition diamondX (m : smode) (kroom kkept kgrown : AP.plan) : AP.plan :=
  PRun [0x39a94] (PBranch (PRun [AFTER] kroom) (PRun [] (PExt2 31 (RSZ m) (PRun [AFTER] kkept) (PRun [AFTER] kgrown)))).
Definition planX (m : smode) : AP.plan :=
  match m with
  | MS => PViaM 0 [(JSA MS, afterA MS)] JLO (diamondX MS (PMerge 0) (PMerge 0) (PHandoffW HC []))
  | ML => diamondX ML (PHandoffW HC []) (PHandoffW HC []) (PHandoffW HC [])
  end.
Lemma esc_gplanX : forall m, gplan_ok (planX m) = true. Proof. intros [|]; reflexivity. Qed.
Lemma esc_gplanC : gplan_ok (CUTE (JSA ML) (afterA ML)) = true. Proof. reflexivity. Qed.
Lemma esc_cert_S : check PSEGS IT APLAIN NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HScut (ce MS) CUTS_E 0) 0%nat BFUEL FUEL None (tin MS) (planX MS) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ceL1 : gcallee := GCE NXF (tin ML) [tout ML; tout ML] BCAP CCAP.
Lemma esc_cert_L1 : check PSEGS IT APLAIN NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HScut ceL1 CUTS_E 0) 0%nat BFUEL FUEL None (tin ML) (planX ML) = COk (SHole 2).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 2))). Qed.
Lemma esc_cut_L : check PSEGS IT APLAIN NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HScut ceL1 CUTS_E 1) 0%nat BFUEL FUEL None (JSA ML) (CUTE (JSA ML) (afterA ML)) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
