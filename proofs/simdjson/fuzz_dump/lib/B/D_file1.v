(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac ImageA Nodes RzCPS NodesA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim Canon Stdio Prog.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface D_iface D_defs D_kit D_auxv D_aex D_libiface D_clx D_usage D_open D_read D_rlkit D_loopdefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Section File1.
Variable RT : rt_sig.
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Variable XENV : mem -> Prop.
Variable XENV_FP : list (Z * Z).
Variable LIB : mem -> Prop.
Variable argvb : list (list byte).
Variable fs : Fs.
Variable data : list byte.
Hypothesis AF : art_facts RT.
Hypothesis MAL : malloc_contract RT.
Hypothesis VARGV : valid_argv argvb.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis XENV_loc : xenv_laws XENV XENV_FP.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis IO_img : forall x, in_ranges IO_FP x -> client_static x /\ ~ drv_cell x /\ outside LIB_FP x.
Hypothesis XENV_img : forall x, in_ranges XENV_FP x -> client_static x /\ ~ drv_cell x /\ outside IO_FP x /\ outside LIB_FP x.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, g_read_stage in *; lia.

Lemma cap_ok_65536 : cap_ok 65536.
Proof. exists 0%nat. split; [lia| reflexivity]. Qed.

Theorem file_start : Z.of_nat (length argvb) = 2 -> open_class (nth 1 (argv_Z argvb) []) fs = OCFile data ->
  cps bsegs (OPENED RT OUT_rep ERR_rep XENV LIB argvb fs) (RL RT OUT_rep ERR_rep XENV LIB argvb fs data 0 65536).
Proof using AF MAL VARGV OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img.
  intros HL HCL T c HO Hk.
  destruct HO as (Σ & usp & ap & path & gp & s1 & s3 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7
                  & m & ent & HA & HCTX & HSIG & HB & Hap & Hhi & HENT & _).
  rewrite nth1_argv_Z in HCL. pose proof (oc_file _ _ _ HCL) as (HD & _). unfold path_b in HENT. rewrite HD in HENT.
  injection HENT as <-.
  pose proof HCTX as (ART0 & MI0 & CLX0 & ARGV0 & FR0 & ST0 & B16 & UA & ULO & USP0).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  pose proof HSIG as (LV & FRS & CR & USP0' & SPW).
  set (lo := rt_sp0 RT Σ - STACK_WIN) in *.

  destruct (ASTA_unpack RT Σ _ _ c HA) as (ms0 & RS0 & HA').
  destruct RS0 as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & -> & FRM).
  rewrite (ret_pc_even RET_OPEN) in HA' by (unfold RET_OPEN; lia).
  pose proof (opened_walk usp gp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 path) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m MI0) as W1.
  lazymatch type of W1 with evt bsegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes bsegs _ _ _ c (asta_evt RT AF Σ _ fs _ _ W1') HA').
  intros cf1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ cf1 Hc1) as (ms1 & <- & Hc1').
  assert (EU : bv_unsigned (Z_to_bv 64 (usp - 80)) = usp - 80) by (apply unsigned_lit; ul).
  apply (MAL Σ (PMfd (FD argvb 0) fs) (Z_to_bv 64 0xae1fc) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2) s1
           (Z_to_bv 64 65536) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 path) s3 (Z_to_bv 64 3) (Z_to_bv 64 65536) s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 F fc m 65536 lo); try reflexivity; try assumption.
  - apply PMfd_fdfs_only.
  - apply PMfd_mat_stable.
  - lia.
  - rewrite LV. reflexivity.
  - unfold mcost, DCOST, CREDIT_DRV in *. cbn. lia.
  - unfold call_ok. rewrite EU. split; [exact ST0|]. ul.
  - unfold unwind_ok. rewrite EU, !unsigned_lit by lia. left. ul.
  - intros cf2 (Σ' & p & Hc2 & LV' & FRS' & SP' & CR' & Pp & Pal & Ptop).
    destruct (ASTA_unpack RT Σ' _ _ cf2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WR2 & ACC2) & Hc2').
    destruct RS2 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & ->). pose (fc' := fc).
    rewrite EU in ST2, PRES2.
    pose proof (af_live_range RT AF Σ' m2 p 65536 ART2 ltac:(rewrite LV'; left; reflexivity)) as (PR1 & PR2 & PR3).
    assert (CLX2 : CLX OUT_rep ERR_rep XENV LIB stdout_init m2)
      by exact (CLX_pres OUT_rep ERR_rep IO_FP XENV XENV_FP LIB OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img
                  _ m m2 _ _ _ CLX0 PRES2 WM2).
    pose proof (agree_stack_pres _ _ _ _ _ PRES2) as AG2.
    assert (HD0 : DCTX RT OUT_rep ERR_rep XENV LIB argvb Σ usp ap path c0 c1 c2 c3 c4 c5 c6 c7 m)
      by (split; [exact HCTX| tauto]).
    assert (HD2 : DCTX RT OUT_rep ERR_rep XENV LIB argvb Σ' usp ap path c0 c1 c2 c3 c4 c5 c6 c7 m2)
      by exact (DCTX_agree RT OUT_rep ERR_rep XENV LIB argvb AF Σ Σ' usp ap path c0 c1 c2 c3 c4 c5 c6 c7 m m2 HD0 ART2 MI2 WM2 ST2
                  SP' CLX2 AG2 (auxc_of_pres _ _ _ _ _ PRES2)).

    pose proof (first_read_walk usp p gp t0' t1' t2' s1 a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 path) s3 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6' F' fc' m2 ltac:(ul) MI2) as W2.
    rewrite (ret_pc_even 0xae1fc) in Hc2' by lia.
    lazymatch type of W2 with evt bsegs _ ?X =>
      assert (W2' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W2) end.
    clear W2.
    apply (cps_realizes bsegs _ _ _ _ (asta_evt RT AF Σ' _ fs _ _ W2') Hc2').
    intros cf3 Hc3. apply Hk.
    destruct (ASTA_unpack RT Σ' _ _ cf3 Hc3) as (ms3 & <- & Hc3').
    exists Σ', usp, ap, path, p, gp, t0', t1', t2', a3', a4', a5', a6', a7', (Z_to_bv 64 p), s8, s9, s10, s11, t3', t4', t5', t6'.
    exists c0, c1, c2, c3, c4, c5, c6, c7, F', fc', m2. split; [exact FRM|].
    change (Z.min (65536 - 0) 65536) with 65536.
    split; [exact Hc3'|]. split; [exact HD2|].
    split; [split; [rewrite LV', LV; reflexivity|]; split; [rewrite FRS'; exact FRS|]; split; [rewrite CR'; unfold mcost, DCOST, CREDIT_DRV in *; cbn; lia|
             rewrite SP'; exact USP0']|].
    split; [apply bytes_at_nil; ul|]. split; [lia|]. split; [lia| exact cap_ok_65536].
Qed.

End File1.
