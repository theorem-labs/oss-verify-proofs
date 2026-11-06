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
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import BgCommon.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition BUFMAX : Z := 2 ^ 26.
Definition FR : Z := 384.     (* [comment removed for export] *)
Definition YLO : Z := FR.
(* [comment removed for export] *)
Definition NXF : nat := 43.
Definition regsT : list expr := sr_upd regs0 4 (ELit (g_tp GBOTH)).
Definition CL : expr := EVar 9.
Definition KLP : expr := EVar 31. Definition SVP : expr := EVar 32. Definition V : expr := EVar 33. Definition C : expr := EVar 34.
Definition Q : expr := EVar 35. Definition EP : expr := EVar 36. Definition KLN : expr := EVar 37. Definition KP : expr := EVar 38.
Definition IT0 : expr := eadd KP KLN.   (* [comment removed for export] *)
Definition EE : expr := EVar 40.
Definition e_mtr : expr := EVar 41.  Definition e_fb : expr := EVar 42.
(* [comment removed for export] *)
Definition fobj (x : expr) (n : Z) : list kentry :=
  [KRange x PTRLO (objhi (n + 8)); KAlign x 8; KShOk (SA x 0) (ELit n);
   KDisj (SA x 0) (ELit n) (SA e_sp (- FR)) (ELit (FR + WSTK)); img_apart x 0 (ELit n); shmap_apart x 0 (ELit n)].
Definition disj (x : expr) (n : Z) (y : expr) (m : Z) : kentry := KDisj (SA x 0) (ELit n) (SA y 0) (ELit m).
(* [comment removed for export] *)
Section Lam.
Variable ENTRY RET : Z.
Variable VOFF : Z.
Definition kn_mem : list kentry :=
  [KWord (SA CL 0) 8 KLP; KWord (SA CL 8) 8 SVP; KWord (SA CL 16) 8 V; KWord (SA CL 24) 8 C; KWord (SA CL 32) 8 Q; KWord (SA CL 40) 8 EP;
   KWord (SA KLP 0) 8 KLN; KWord (SA SVP 0) 8 KP; KWord (SA EP 0) 8 EE;
   KShOk (SA CL 0) (ELit 48);
   KUnk (SA KP 0) (esub EE KP); KShOk (SA KP 0) (esub EE KP);
   KWr (SA V VOFF) (ELit 8); KWr (SA C 0) (ELit 4); KWr (SA Q 0) (ELit 8); KShOk (SA V VOFF) (ELit 8); KIMGA] ++ RTC ++ GLZ_LOWSH.
Definition kn_pure : list kentry :=
  [KRange CL (CEIL + FR) (HI47 - 48); KAlign CL 8; KRange (esub CL e_sp) 0 (2^46);
   KRange KLN 1 5;
   KRange KP PTRLO PTRHI; KRange EE PTRLO PTRHI; KRange (esub EE IT0) 0 BUFMAX; KRange (esub EE KP) 1 BUFMAX;
   img_apart KP 0 (esub EE KP); shmap_apart KP 0 (esub EE KP);
   KDisj (SA KP 0) (esub EE KP) (SA e_sp (- FR)) (ELit (FR + WSTK))]
  ++ fobj KLP 8 ++ fobj SVP 16 ++ fobj EP 8 ++ fobj C 8 ++ fobj Q 8
  ++ [KRange (eaddz V VOFF) PTRLO (objhi 16); KAlign V 8; KDisj (SA V VOFF) (ELit 8) (SA e_sp (- FR)) (ELit (FR + WSTK));
      img_apart V VOFF (ELit 8); shmap_apart V VOFF (ELit 8)]
  ++ (* [comment removed for export] *)
     [disj Q 8 KLP 8; disj Q 8 SVP 16; disj Q 8 EP 8; disj Q 8 C 8; KDisj (SA Q 0) (ELit 8) (SA CL 0) (ELit 48);
      KDisj (SA Q 0) (ELit 8) (SA KP 0) (esub EE KP); KDisj (SA Q 0) (ELit 8) (SA V VOFF) (ELit 8);
      disj C 8 KLP 8; disj C 8 SVP 16; disj C 8 EP 8; KDisj (SA C 0) (ELit 8) (SA CL 0) (ELit 48); KDisj (SA C 0) (ELit 8) (SA V VOFF) (ELit 8);
      KDisj (SA C 0) (ELit 8) (SA KP 0) (esub EE KP);
      KDisj (SA V VOFF) (ELit 8) (SA CL 0) (ELit 48); KDisj (SA V VOFF) (ELit 8) (SA EP 0) (ELit 8); KDisj (SA V VOFF) (ELit 8) (SA KLP 0) (ELit 8);
      KDisj (SA V VOFF) (ELit 8) (SA SVP 0) (ELit 16); KDisj (SA V VOFF) (ELit 8) (SA KP 0) (esub EE KP)].
Definition sp_in : list kentry := [KShOk (SA e_sp (- FR)) (ELit FR); KWr (SA e_sp (- FR)) (ELit FR); KAlign e_sp 32; KRange e_sp (CEIL + FR) HI47].
   (* [comment removed for export] *)
Definition kn0 : list kentry :=
  [KWord (SA Q 0) 8 IT0; KWord (SA C 0) 4 (ELit 0); KRange e_mtr 0 GKCAP; fb_fact e_fb] ++ sp_in ++ kn_mem ++ kn_pure.
Definition WS : list (expr * expr) := [(eaddz V VOFF, ELit 8); (C, ELit 8); (Q, ELit 8); (CL, ELit 48); (KLP, ELit 8); (SVP, ELit 16); (EP, ELit 8); (KP, esub EE KP)].
Definition mkcsM (p : Z) (regs : list expr) (k : list kentry) (nx : nat) : acs :=
  ACS (mk_ss p regs k nx) [] 0 YLO 0 [] WS 0 e_sp FdStd false e_mtr [] e_fb.
Definition tin : acs := mkcsM ENTRY regsT kn0 NXF.
(* [comment removed for export] *)
Definition D : expr := EVar 43.  Definition ER : expr := EVar 44.
Definition clobbered : list nat := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
Definition x_regs : list expr := sr_havoc regsT clobbered 45.
Definition x_kn : list kentry :=
  [KWord (SA Q 0) 8 (eadd IT0 D); KRange D 0 10; KRange (esub EE (eadd IT0 D)) 0 BUFMAX; KWord (SA C 0) 4 ER; KRange ER 0 255] ++ kn_mem.
Definition tout : acs := mkcsM RET x_regs x_kn 60.
Definition ce : gcallee := GCE NXF tin [tout] 0 0.
End Lam.

Definition LAM_I : Z := 0xa14a8.  Definition RET_I : Z := 0xa18a4.  Definition N_I : nat := 401.
Definition LAM_D : Z := 0xa1aec.  Definition RET_D : Z := 0xa1f1c.  Definition N_D : nat := 408.
Definition ceI : gcallee := ce LAM_I RET_I 0.
Definition ceD : gcallee := ce LAM_D RET_D 8.
Definition IT_I : itab := mk_itab_ranges BSEGS [(LAM_I, N_I); (0xa28f4, 113%nat); (0xa2ab8, 130%nat); (0xa2cc0, 134%nat); (0xa2ed8, 143%nat); (0xa3114, 111%nat); (0xa32d0, 128%nat); (0xa34d0, 134%nat); (0xa36e8, 143%nat)].
Definition IT_D : itab := mk_itab_ranges BSEGS [(LAM_D, N_D); (0xa3924, 133%nat); (0xa3b38, 140%nat); (0xa3d68, 111%nat); (0xa3f24, 128%nat); (0xa4124, 132%nat); (0xa4334, 141%nat); (0xa4568, 109%nat); (0xa471c, 126%nat); (0xa4914, 132%nat); (0xa4b24, 141%nat)].
Lemma IT_I_ok : itab_sound BSEGS IT_I. Proof. apply APS.mk_itab_ranges_sound. Qed.
Lemma IT_D_ok : itab_sound BSEGS IT_D. Proof. apply APS.mk_itab_ranges_sound. Qed.




