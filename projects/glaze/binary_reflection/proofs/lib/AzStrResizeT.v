(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import GaCommon.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition RESIZE : Z := 0xdcc10.
Definition APPEND : Z := 0xdca38.
Definition RET_S : Z := 0xdcc3c.      (* [comment removed for export] *)
Definition RET_L : Z := 0xdcc60.      (* [comment removed for export] *)
Definition RET_A : Z := 0xdcc08.      (* [comment removed for export] *)
Definition THUNK_MEMSET : Z := 0x6c760.





Definition IT : itab := mk_itab_ranges ASEGS [(APPEND, 118%nat); (RESIZE, 21%nat); (THUNK_MEMSET, 2%nat)].
Lemma IT_ok : itab_sound ASEGS IT. Proof. apply APS.mk_itab_ranges_sound. Qed.

(* [comment removed for export] *)
Section WithNB.
Variable NB : Z.

(* [comment removed for export] *)
Definition TP : Z := g_tp GASAN.
Definition regs_in : list expr := sr_upd (sr_upd regs0 4 (ELit TP)) 12 (ELit 0).
Definition e_obj : expr := e_a0.           (* [comment removed for export] *)
Definition e_n : expr := e_a1.             (* [comment removed for export] *)
(* [comment removed for export] *)
Definition NXF (m : smode) : nat := match m with MS => 34%nat | ML => 36%nat end.
Definition e_s : expr := EVar 31.
Definition e_d : expr := EVar 31.  Definition e_sz : expr := EVar 32.  Definition e_A : expr := EVar 33.
Definition e_mtr (m : smode) : expr := match m with MS => EVar 32 | ML => EVar 34 end.
Definition e_fb (m : smode) : expr := match m with MS => EVar 33 | ML => EVar 35 end.
Definition e_len : expr := escale 8 e_A.

(* [comment removed for export] *)
Definition FRK : Z := 80 + MSTK_N.
Definition MTRMAX : Z := GKCAP - kcost (2 * NB + 8) - KFREE.

(* [comment removed for export] *)
Definition AMAX : Z := 2 ^ 37.
(* [comment removed for export] *)
Definition obj_facts : list kentry :=
  [ KRange e_obj PTRLO (objhi 24); KAlign e_obj 8;
    KWr (SA e_obj 0) (ELit 24); KUnk (SA e_obj 0) (ELit 24); KShOk (SA e_obj 0) (ELit 24);
    KDisj (SA e_obj 0) (ELit 24) (SA e_sp (- FRK)) (ELit (FRK + WSTK)); img_apart e_obj 0 (ELit 24); shmap_apart e_obj 0 (ELit 24) ]
  ++ NEWH.
Definition stk_facts : list kentry :=
  [ KAlign e_sp 16; KRange e_sp (CEIL + FRK) HI47; KWr (SA e_sp (- FRK)) (ELit FRK) ].
(* [comment removed for export] *)
Definition blk_facts (b len : expr) (nlo : Z) : list kentry :=
  [ KRange b PTRLO (PTRHI - nlo); KRange (eadd b len) (PTRLO + nlo) PTRHI; KAlign b 16;
    KWr (SA b 0) len; KUnk (SA b 0) len; KShOk (SA b 0) len;
    KDisj (SA b 0) len (SA e_sp (- FRK)) (ELit (FRK + WSTK)); img_apart b 0 len; shmap_apart b 0 len;
    KDisj (SA b 0) len (SA e_obj 0) (ELit 24) ].
Definition hdr_facts (m : smode) : list kentry :=
  match m with
  | MS => [ KWord (SA e_obj 0) 1 (escale 2 e_s); KRange e_s 0 22 ]
  | ML => [ KWord (SA e_obj 0) 8 (eaddz e_len 1); KWord (SA e_obj 8) 8 e_sz; KWord (SA e_obj 16) 8 e_d;
            KRange e_A 3 AMAX; KRange e_sz 0 (8 * AMAX); KRange (esub e_len e_sz) 1 (8 * AMAX) ]
          ++ blk_facts e_d e_len 24
  end.
(* [comment removed for export] *)
Definition opnew_facts (m : smode) : list kentry := RTC ++ [ KIMGA; GLZ_SH0; fb_fact (e_fb m) ].
Definition kn_in (m : smode) : list kentry :=
  obj_facts ++ hdr_facts m ++ [ KRange e_n 0 NB; KRange (e_mtr m) 0 MTRMAX ] ++ stk_facts ++ opnew_facts m.
Definition WS : list (expr * expr) := [(e_obj, ELit 24)].
Definition vis_in (m : smode) : list (expr * expr) := match m with MS => [] | ML => [(e_d, e_len)] end.
Definition mkcsV (vis : list (expr * expr)) (mtr fb : expr) (p : Z) (regs : list expr) (k : list kentry) (nx : nat) : acs :=
  ACS (mk_ss p regs k nx) [] 0 FRK 0 vis WS 0 e_sp FdStd false mtr [] fb.     (* [comment removed for export] *)
Definition tin (m : smode) : acs := mkcsV (vis_in m) (e_mtr m) (e_fb m) RESIZE regs_in (kn_in m) (NXF m).

(* [comment removed for export] *)
Definition X0 (m : smode) : nat := NXF m.
Definition e_d' (m : smode) : expr := EVar (X0 m).
Definition e_A' (m : smode) : expr := EVar (1 + X0 m).
Definition e_m' (m : smode) : expr := EVar (2 + X0 m).
Definition e_len' (m : smode) : expr := escale 8 (e_A' m).
Definition caller_saved_but_a0 : list nat := [5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
Definition regs_out (m : smode) : list expr := sr_havoc (sr_upd regs_in 12 (EVar 11)) caller_saved_but_a0 (3 + X0 m).
Definition NXOUT (m : smode) : nat := (3 + X0 m + 14)%nat.

(* [comment removed for export] *)
Definition kn_keep (m : smode) : list kentry :=
  obj_facts ++
  match m with
  | MS => [ KWord (SA e_obj 0) 1 (escale 2 e_n); KWord (SA (eadd (eaddz e_obj 1) e_n) 0) 1 (ELit 0); KRange e_n 0 22 ]
  | ML => [ KWord (SA e_obj 0) 8 (eaddz e_len 1); KWord (SA e_obj 8) 8 e_n; KWord (SA e_obj 16) 8 e_d;
            KWord (SA (eadd e_d e_n) 0) 1 (ELit 0); KRange (esub e_len e_n) 1 (8 * AMAX) ]
          ++ blk_facts e_d e_len 24
  end ++ stk_facts.
(* [comment removed for export] *)
Definition kn_grown (m : smode) : list kentry :=
  let d' := e_d' m in let len' := e_len' m in
  obj_facts ++
  [ KRange (e_A' m) 6 (NB / 4 + 2); KRange (esub len' e_n) 1 (match m with MS => 52 | ML => 2 * NB + 16 end) ]
  ++ blk_facts d' len' 48 ++
  [ KWord (SA (eadd d' e_n) 0) 1 (ELit 0);
    KWord (SA e_obj 0) 8 (eaddz len' 1); KWord (SA e_obj 8) 8 e_n; KWord (SA e_obj 16) 8 d';
    (* [comment removed for export] *)
    KRange (e_m' m) (match m with MS => EVT | ML => EVT + KFREE end) (match m with MS => EVT | ML => EVT + KFREE end) ]
  ++ match m with
     | MS => [ KRange e_n 23 NB; KRange (esub (eaddz e_n 52) len') 0 52 ]
     | ML => [ KRange (esub e_n e_len) 0 NB; KRange (esub (eaddz (eadd e_n (escale 16 e_A)) 6) len') 0 (5 * NB);
               KRange (esub (eaddz (escale 2 e_n) 8) len') 0 (2 * NB + 8);
               KRange (esub len' (escale 2 e_len)) 0 (2 * NB + 16) ]   (* [comment removed for export] *)
     end ++ stk_facts.
Definition tout_keep (m : smode) (p : Z) : acs := mkcsV (vis_in m) (e_mtr m) (e_fb m) p (regs_out m) (kn_keep m) (NXOUT m).
Definition tout_grown (m : smode) : acs :=
  mkcsV [(e_d' m, e_len' m)] (eadd (e_mtr m) (e_m' m)) (e_fb m) RET_A (regs_out m) (kn_grown m) (NXOUT m).
Definition touts0 (m : smode) : list acs := [tout_keep m (match m with MS => RET_S | ML => RET_L end); tout_keep m RET_A].
Definition touts1 (m : smode) : list acs := [tout_grown m].
Definition BCAP : Z := 3 * NB + 2 * MBLK + 24.
Definition CCAP : Z := 2.
Definition ce2 (m : smode) : gcallee2 := GCE2 (NXF m) (tin m) (touts0 m) (touts1 m) BCAP CCAP.
Definition ce (m : smode) : gcallee := c2_merged (ce2 m).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition H_KEEP0 : nat := 0.  Definition H_KEEPA : nat := 1.  Definition H_GROWN : nat := 2.

(* [comment removed for export] *)
Definition memsetK (h : nat) : plan := PRun [] (PExt 2 [] (PRun [] (PHandoff h))).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PH : nat := 999.   (* [comment removed for export] *)
Definition endfact (k : plan) : plan := PFactX 10 PH (eadd (EVar PH) e_n) PTRLO PTRHI k.
(* [comment removed for export] *)
Definition srl3 (e : expr) : expr := EAlu ALU_SRL e (ELit 3).
Definition resfact (e : expr) (k : plan) : plan := PFact (KRange (esub e (escale 8 (srl3 e))) 0 7) k.
Definition growS_tail : plan :=
  resfact e_n (PRun [] (PExt 20 [] (endfact (PCase2 e_s 0
     (PRun [] (memsetK H_GROWN))
     (PRun [] (PExt 3 [] (PRun [] (memsetK H_GROWN)))))))).
Definition planS : plan :=
  PCase2 e_n 22
    (* [comment removed for export] *)
    (PRun [] (PBranch
       (* [comment removed for export] *)
       (memsetK H_KEEPA)
       (* [comment removed for export] *)
       (PRun [] (PHandoff H_KEEP0))))
    (* [comment removed for export] *)
    (PRun [] (PCase2 e_n 44 growS_tail growS_tail)).

(* [comment removed for export] *)
Definition endfactL (k : plan) : plan :=
  PFactX 10 PH (eadd (EVar PH) e_n) PTRLO PTRHI (PFactX 10 PH (eadd (EVar PH) e_sz) PTRLO PTRHI k).
Definition growL_tail : plan :=
  PRun [] (PExt 20 [] (endfactL (PCase2 e_sz 0
     (PRun [] (PExt 22 [] (PRun [] (memsetK H_GROWN))))
     (PRun [] (PExt 3 [] (PRun [] (PExt 22 [] (PRun [] (memsetK H_GROWN))))))))).
Definition planL : plan :=
  resfact e_n (PRun [] (PBranch
    (* [comment removed for export] *)
    (PRun [] (PHandoff H_KEEP0))
    (* [comment removed for export] *)
    (PRun [] (PBranch
       (* [comment removed for export] *)
       (PFact (KRange e_A 3 (NB / 8)) (PFact (KRange (eadd e_d e_sz) PTRLO PTRHI) (PRun [] (PBranch growL_tail growL_tail))))
       (* [comment removed for export] *)
       (PFact (KRange (eadd e_d e_n) PTRLO PTRHI) (memsetK H_KEEPA)))))).

End WithNB.

Definition ceS (NB : Z) : gcallee2 := ce2 NB MS.
Definition ceL (NB : Z) : gcallee2 := ce2 NB ML.
(* [comment removed for export] *)
Definition CLASSES : list Z := [2^16; 2^22; 2^26; 2^28; 3 * 2^30 + 16; 3 * 2^30 + 80; 13 * 2^28 + 80].   (* [comment removed for export] *)

