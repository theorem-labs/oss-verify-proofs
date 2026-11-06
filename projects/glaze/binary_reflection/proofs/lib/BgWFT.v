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
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import BgCommon.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition ENTRY : Z := 0xbb34c.
Definition RETPC : Z := 0xbbc00.
Definition CDE : Z := 0xbc150.      (* [comment removed for export] *)
Definition PTI : Z := 0xbc1d8.      (* [comment removed for export] *)
Definition IT : itab := mk_itab_ranges BSEGS [(ENTRY, 897%nat); (CDE, 34%nat); (PTI, 46%nat)].
Lemma IT_ok : itab_sound BSEGS IT. Proof. apply APS.mk_itab_ranges_sound. Qed.

(* [comment removed for export] *)
Definition NXF : nat := 33.
Definition e_buf := e_a0.
Definition e_mtr : expr := EVar 31.  Definition e_fb : expr := EVar 32.
Definition K : Z := 17.          (* [comment removed for export] *)
Definition FR : Z := 96.         (* [comment removed for export] *)
Definition YLO : Z := FR.         (* [comment removed for export] *)
Definition WS : list (expr * expr) := [(e_buf, ELit K)].
(* [comment removed for export] *)
Definition TBL : Z := 0x22d00.

Definition tbl_shadow : list kentry := GLZ_LOWSH.   (* [comment removed for export] *)
Definition kn_in : list kentry :=
  [ KRange e_buf PTRLO (objhi K); KDisj (SA e_buf 0) (ELit K) (SA e_sp (- FR)) (ELit FR);   (* [comment removed for export] *)
    KWr (SA e_buf 0) (ELit K); KUnk (SA e_buf 0) (ELit K); KShOk (SA e_buf 0) (ELit K); KWr (SA e_sp (- FR)) (ELit FR) ]
  ++ sp_facts YLO ++ [ KIMGA ] ++ RTC ++ tbl_shadow
  ++ [img_apart e_buf 0 (ELit K); shmap_apart e_buf 0 (ELit K)].   (* [comment removed for export] *)
Definition tin : acs := mkcs YLO WS e_mtr e_fb ENTRY regs0 kn_in NXF.

(* [comment removed for export] *)
Definition MMAX : Z := 16.       (* [comment removed for export] *)
Definition M : nat := 140.
Definition LO : nat := 141.
Definition js_regs : list expr :=
  sr_havoc (sr_upd (sr_upd regs0 10 (eadd e_buf (EVar M))) 11 (EVar LO)) caller_saved_but_a01 (S LO).
Definition kn_out : list kentry :=
  [ KRange (EVar M) 0 MMAX; KWr (SA e_buf 0) (ELit K); KUnk (SA e_buf 0) (ELit K); KShOk (SA e_buf 0) (ELit K); KWr (SA e_sp (- FR)) (ELit FR) ] ++ sp_facts YLO.
Definition tout : acs := mkcs YLO WS e_mtr e_fb RETPC js_regs kn_out (LO + 14)%nat.
Definition ce : gcallee := GCE NXF tin [tout] 0 0.
