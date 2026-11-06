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
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC. Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.BgPrune OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgReadCert.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition ENTRY : Z := 0xa214c.  Definition RET : Z := 0xa2628.  Definition NINSTR : nat := 486.
Definition IT : itab := mk_itab_ranges BSEGS [(ENTRY, NINSTR)].
Lemma IT_ok : itab_sound BSEGS IT. Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition BUFMAX : Z := 2 ^ 26.
Definition RFRK : Z := BgStrResizeT.FRK.            (* [comment removed for export] *)
Definition FRK : Z := 80 + RFRK.                     (* [comment removed for export] *)
Definition MTRIN : Z := GKCAP - 2 ^ 33.              (* [comment removed for export] *)
(* [comment removed for export] *)
Definition NXF (m : smode) : nat := match m with MS => 44 | ML => 46 end.
Definition regsT : list expr := sr_upd regs0 4 (ELit (g_tp GBOTH)).
Definition CL : expr := EVar 9.
Definition KLP : expr := EVar 31. Definition SVP : expr := EVar 32. Definition V : expr := EVar 33. Definition C : expr := EVar 34.
Definition Q : expr := EVar 35. Definition EP : expr := EVar 36. Definition KLN : expr := EVar 37. Definition IB : expr := EVar 38.
Definition KO : expr := EVar 39. Definition EE : expr := EVar 40.
Definition DL : expr := EVar 43.
 Definition AL : expr := EVar 45.   (* [comment removed for export] *)
Definition e_mtr : expr := EVar 41.  Definition e_fb : expr := EVar 42.
Definition KP : expr := eadd IB KO.             (* [comment removed for export] *)
Definition IT0 : expr := eadd KP KLN.           (* [comment removed for export] *)
Definition BLEN : expr := esub EE IB.
Definition flo (x : expr) (k : Z) (n : expr) : kentry := KDisj (SA x k) n (SA e_sp (- FRK)) (ELit (FRK + WSTK)).
Definition fobj (x : expr) (n : Z) : list kentry :=
  [KRange x PTRLO (objhi (n + 8)); KAlign x 8; KShOk (SA x 0) (ELit n); flo x 0 (ELit n); img_apart x 0 (ELit n); shmap_apart x 0 (ELit n)].
Definition dj (x : expr) (k n : Z) (y : expr) (j m : Z) : kentry := KDisj (SA x k) (ELit n) (SA y j) (ELit m).
Definition djb (x : expr) (k n : Z) : kentry := KDisj (SA x k) (ELit n) (SA IB 0) BLEN.
(* [comment removed for export] *)
Definition blk (d a : expr) : list kentry :=
  [KRange d PTRLO (PTRHI - 24); KRange (eadd d (escale 8 a)) (PTRLO + 24) PTRHI; KAlign d 16;
   KWr (SA d 0) (escale 8 a); KUnk (SA d 0) (escale 8 a); KShOk (SA d 0) (escale 8 a);
   KDisj (SA d 0) (escale 8 a) (SA e_sp (- FRK)) (ELit (RFRK + WSTK)); img_apart d 0 (escale 8 a); shmap_apart d 0 (escale 8 a);
   KDisj (SA d 0) (escale 8 a) (SA V 16) (ELit 24);
   KDisj (SA d 0) (escale 8 a) (SA CL 0) (ELit 48); KDisj (SA d 0) (escale 8 a) (SA KLP 0) (ELit 8); KDisj (SA d 0) (escale 8 a) (SA SVP 0) (ELit 16);
   KDisj (SA d 0) (escale 8 a) (SA EP 0) (ELit 8); KDisj (SA d 0) (escale 8 a) (SA C 0) (ELit 8); KDisj (SA d 0) (escale 8 a) (SA Q 0) (ELit 8);
   KDisj (SA d 0) (escale 8 a) (SA IB 0) BLEN].
Definition AHI : Z := 2 ^ 24 + 2.        (* [comment removed for export] *)
Definition NB : Z := 2 ^ 26.               (* [comment removed for export] *)
Definition strS (s : expr) : list kentry := [KWord (SA V 16) 1 (escale 2 s); KRange s 0 22].
(* [comment removed for export] *)
Definition strLg (alo : Z) (d s a : expr) : list kentry :=
  [KWord (SA V 16) 8 (eaddz (escale 8 a) 1); KWord (SA V 24) 8 s; KWord (SA V 32) 8 d;
   KRange a alo AHI; KRange s 0 (8 * AHI); KRange (esub (escale 8 a) s) 1 (8 * AHI)] ++ blk d a.
Definition strL (d s a : expr) : list kentry := strLg 3 d s a.
Definition str (m : smode) (v : nat) : list kentry :=
  match m with MS => strS (EVar v) | ML => strL (EVar v) (EVar (1 + v)) (EVar (2 + v)) end.
Definition vis (m : smode) (v : nat) : list (expr * expr) := match m with MS => [] | ML => [(EVar v, escale 8 (EVar (2 + v)))] end.
Definition kn_mem : list kentry :=
  [KWord (SA CL 0) 8 KLP; KWord (SA CL 8) 8 SVP; KWord (SA CL 16) 8 V; KWord (SA CL 24) 8 C; KWord (SA CL 32) 8 Q; KWord (SA CL 40) 8 EP;
   KWord (SA KLP 0) 8 KLN; KWord (SA SVP 0) 8 KP; KWord (SA EP 0) 8 EE;
   KShOk (SA CL 0) (ELit 48);
   KUnk (SA IB 0) BLEN; KWr (SA IB 0) BLEN; KShOk (SA IB 0) BLEN;
   KWr (SA V 16) (ELit 24); KUnk (SA V 16) (ELit 24); KShOk (SA V 16) (ELit 24);
   KWr (SA C 0) (ELit 4); KWr (SA Q 0) (ELit 8); KIMGA] ++ RTC ++ GLZ_LOWSH ++ NEWH.
Definition kn_pure : list kentry :=
  [KRange CL (CEIL + FRK) (HI47 - 48); KAlign CL 8; KRange (esub CL e_sp) 0 (2^46); KDisj (SA e_sp (- FRK)) (ELit FRK) (SA CL 0) (ELit 48);
   KRange KLN 1 5; KRange KO 0 BUFMAX;
   KRange IB PTRLO PTRHI; KRange EE PTRLO PTRHI; KRange BLEN 1 BUFMAX; KRange (esub EE IT0) 0 BUFMAX;
   img_apart IB 0 BLEN; shmap_apart IB 0 BLEN; flo IB 0 BLEN]
  ++ fobj KLP 8 ++ fobj SVP 16 ++ fobj EP 8 ++ fobj C 8 ++ fobj Q 8
  ++ [KRange (eaddz V 16) PTRLO (objhi 24); KAlign V 8; flo V 16 (ELit 24); img_apart V 16 (ELit 24); shmap_apart V 16 (ELit 24)]
  ++ (* [comment removed for export] *)
     [dj Q 0 8 KLP 0 8; dj Q 0 8 SVP 0 16; dj Q 0 8 EP 0 8; dj Q 0 8 C 0 8; dj Q 0 8 CL 0 48; dj Q 0 8 V 16 24; djb Q 0 8;
      dj C 0 8 KLP 0 8; dj C 0 8 SVP 0 16; dj C 0 8 EP 0 8; dj C 0 8 CL 0 48; dj C 0 8 V 16 24; djb C 0 8;
      dj V 16 24 KLP 0 8; dj V 16 24 SVP 0 16; dj V 16 24 EP 0 8; dj V 16 24 CL 0 48; djb V 16 24;
      djb KLP 0 8; djb SVP 0 16; djb EP 0 8; djb CL 0 48;
      fb_fact e_fb].
Definition sp_in : list kentry := [KWr (SA e_sp (- FRK)) (ELit FRK); KAlign e_sp 16; KRange e_sp (CEIL + FRK) HI47].
Definition kn0 (m : smode) : list kentry :=
  [KWord (SA Q 0) 8 IT0; KWord (SA C 0) 4 (ELit 0); KRange e_mtr 0 MTRIN] ++ str m 43 ++ sp_in ++ kn_mem ++ kn_pure.
Definition WS : list (expr * expr) :=
  [(eaddz V 16, ELit 24); (C, ELit 8); (Q, ELit 8); (IB, BLEN); (CL, ELit 48); (KLP, ELit 8); (SVP, ELit 16); (EP, ELit 8)].
Definition mkcsH (p : Z) (regs : list expr) (k : list kentry) (nx : nat) (vs : list (expr * expr)) (mtr : expr) : acs :=
  ACS (mk_ss p regs k nx) [] 0 FRK 0 vs WS 0 e_sp FdStd false mtr [] e_fb.
Definition tin (m : smode) : acs := mkcsH ENTRY regsT (kn0 m) (NXF m) (vis m 43) e_mtr.

(* [comment removed for export] *)
Definition X0 (m : smode) : nat := NXF m.
Definition D (m : smode) : expr := EVar (X0 m).  Definition ER (m : smode) : expr := EVar (1 + X0 m).  Definition M' (m : smode) : expr := EVar (2 + X0 m).
Definition clobbered : list nat := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
Definition x_regs (m : smode) : list expr := sr_havoc regsT clobbered (6 + X0 m).
Definition NXOUT (m : smode) : nat := (6 + X0 m + 15)%nat.
Definition DMAX : Z := BUFMAX + 16.
(* [comment removed for export] *)
Definition GM (m : smode) : Z := match m with MS => kcost (2 * BUFMAX + 8) | ML => kcost (2 * BUFMAX + 8) + KFREE end.

Definition x_common (m : smode) : list kentry :=
  [KWord (SA Q 0) 8 (eadd IT0 (D m)); KRange (D m) 0 DMAX; KRange (esub EE (eadd IT0 (D m))) 0 BUFMAX; KWord (SA C 0) 4 (ER m); KRange (ER m) 0 255].
(* [comment removed for export] *)
Definition str0 (m : smode) : list kentry :=
  match m with MS => strS (EVar (3 + X0 m)) | ML => strL DL (EVar (4 + X0 m)) AL end.
Definition vis0 (m : smode) : list (expr * expr) := match m with MS => [] | ML => [(DL, escale 8 AL)] end.
Definition x_kn0 (m : smode) : list kentry := x_common m ++ str0 m ++ kn_mem.
Definition tout0 (m : smode) : acs := mkcsH RET (x_regs m) (x_kn0 m) (NXOUT m) (vis0 m) e_mtr.
(* [comment removed for export] *)
Definition A' (m : smode) : expr := EVar (5 + X0 m).
Definition dbl (m : smode) : list kentry :=
  match m with MS => [] | ML => [KRange (esub (escale 8 (A' m)) (escale 2 (escale 8 AL))) 0 (2 * NB + 16)] end.
Definition x_kn1 (m : smode) : list kentry :=
  x_common m ++ [KRange (M' m) (GM m) (GM m)] ++ dbl m ++ strLg 6 (EVar (3 + X0 m)) (EVar (4 + X0 m)) (A' m) ++ kn_mem.
Definition tout1 (m : smode) : acs := mkcsH RET (x_regs m) (x_kn1 m) (NXOUT m) (vis ML (3 + X0 m)) (eadd e_mtr (M' m)).
Definition BCAP : Z := 2 ^ 28.  Definition CCAP : Z := 8.
Definition ce2 (m : smode) : gcallee2 := GCE2 (NXF m) (tin m) [tout0 m] [tout1 m] BCAP CCAP.
Definition ce (m : smode) : gcallee := c2_merged (ce2 m).

(* [comment removed for export] *)
Definition XN (m : smode) : nat -> list expr -> acs -> option acs := XNp (XNc BSEGS IT ABOTH (NXF m) GBOTH BCAP CCAP CT0).
Definition XB (m : smode) : nat -> list expr -> acs -> option (acs * acs) := XBc BSEGS ABOTH (NXF m) GBOTH BCAP CCAP CT2_resize.




