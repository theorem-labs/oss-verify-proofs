(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.B08 Require Import ImageA.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Lib Require Import Nodes RzCPS NodesA.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Spec Require Import Prelim Canon Stdio Prog.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.B08 Require Import Layout.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.B08 Require Import RT_iface D_iface D_defs D_kit D_libiface D_clx D_rlkit D_hdr D_trdefs D_tr1 D_file3.
Import ListNotations.
Open Scope Z_scope.

Section Tr4.
Variable RT : rt_sig.
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Variable XENV1 : mem -> Prop.
Variable XENV_FP : list (Z * Z).
(* [comment removed for export] *)
Variable XENV1x : mem -> Prop.
Variable LIB : mem -> Prop.
Variable fs : Fs.
Hypothesis AF : art_facts RT.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis FRE : free_contract RT.
Hypothesis EXC1 : exit_contract RT XENV1x OUT_rep ERR_rep.
Hypothesis XENV1x_of : forall m, XENV1 m -> rw_cells asegs m TR_INIT [C1 (Z_to_bv 8 0)] -> XENV1x m.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis XENV1_loc : fp_local XENV_FP XENV1.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis IO_img : forall x, in_ranges IO_FP x -> client_static x /\ ~ drv_cell x /\ outside LIB_FP x.
Hypothesis XENV_img : forall x, in_ranges XENV_FP x -> client_static x /\ ~ drv_cell x /\ outside IO_FP x /\ outside LIB_FP x.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, FUZZ_STACK, FUZZ_COST, CREDIT_DRV, g_read_stage in *; lia.

(* [comment removed for export] *)
Theorem ret_tail1_cpsE : forall (Σ : rts RT) (so : stdout_st) (code usp buf cap : Z)
    (gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (c0 c1 c2 c3 c4 c5 c6 c7 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  FCTX RT OUT_rep ERR_rep XENV1 LIB Σ so usp buf cap c0 c1 c2 c3 c4 c5 c6 c7 m -> rw_cells asegs m TR_INIT [C1 (Z_to_bv 8 0)] ->
  0 <= code < 256 -> (so = stdout_init \/ exists k, (k < 500)%nat /\ so = so_lines k) ->
  cpsE asegs (ASTA RT Σ (PMfd fds0 fs)
               (eq (entry_st (Z_to_bv 64 0x8d314) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 code)
                     (Z_to_bv 64 buf) (Z_to_bv 64 buf) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_free m)))
    (evw 1 (so_buf so)) (EXIT fs code).
Proof using All.
  intros Σ so code usp buf cap gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c6 c7
    F fc m HF FL0 Hcode Hso T c HA Hk.
  destruct HF as (ART0 & MI0 & CLX0 & FR0 & ST0 & B16 & ULO & USP0 & SPW & LV & FRS & UT0).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  set (lo := rt_sp0 RT Σ - STACK_WIN) in *.
  assert (EU : bv_unsigned (Z_to_bv 64 (usp - 80)) = usp - 80) by (apply unsigned_lit; ul).
  apply (FRE Σ (PMfd fds0 fs) (Z_to_bv 64 0x8d314) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 code)
           (Z_to_bv 64 buf) (Z_to_bv 64 buf) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m buf cap lo);
    try reflexivity; try assumption.
  - apply PMfd_fdfs_only.
  - apply PMfd_mat_stable.
  - rewrite LV. left. reflexivity.
  - unfold call_ok. rewrite EU. split; [exact ST0|]. ul.
  - unfold unwind_ok. rewrite EU, !unsigned_lit by ul. split; [cbn; tauto|]. left. ul.
  - intros cf1 (Σ1 & v & Hc1 & LV1 & FRS1 & SP1 & CR1).
    destruct (ASTA_unpack RT Σ1 _ _ cf1 Hc1) as (ms1 & (m1 & RS1 & (ART1 & MI1 & ST1) & PRES1) & Hc1').
    destruct RS1 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & ->).
    rewrite EU in ST1, PRES1.
    rewrite (ret_pc_even 0x8d314) in Hc1' by lia.
    assert (CLX1 : CLX OUT_rep ERR_rep XENV1 LIB so m1)
      by exact (CLX_pres_nw OUT_rep ERR_rep IO_FP XENV1 XENV_FP LIB OUT_loc ERR_loc XENV1_loc LIB_loc IO_img XENV_img _ m m1 _ _ _ CLX0 PRES1).
    pose proof CLX1 as (OUT1 & ERR1 & XE1 & _).
    assert (FL1 : rw_cells asegs m1 TR_INIT [C1 (Z_to_bv 8 0)]).
    { apply (rw_cells_agree_nw asegs m m1 _ _ FL0). apply (agree_of_pres _ _ _ _ _ _ PRES1). intros x Hx.
      cbn [cells_size csize Nat.add] in Hx. right; left. apply flag_static. lia. }
    destruct FR0 as (junk & FR0).
    assert (FR1 : rw_cells asegs m1 (usp - 80) [CB 8 junk; C8 c7; C8 c6; C8 c5; C8 c4; C8 c3; C8 c2; C8 c1; C8 c0; C8 (Z_to_bv 64 MAIN_RA)]).
    { apply (rw_cells_agree_nw asegs m m1 _ _ FR0). apply (agree_of_pres _ _ _ _ _ _ PRES1).
      intros x Hx. cbn [cells_size csize Nat.add] in Hx. left. ul. }
    pose proof (main_ret_walk usp gp (Z_to_bv 64 code) (Z_to_bv 64 buf) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v u0 u1 u2 b1 b2 b3 b4 b5 b6
                  b7 u3 u4 u5 u6 F1 fc1 m1 lo c0 c1 c2 c3 c4 c5 c6 c7 junk ST1 ltac:(ul) ltac:(ul) B16 ltac:(ul) FR1 MI1) as W1.
    lazymatch type of W1 with evt asegs _ ?X =>
      assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
    clear W1.
    apply (cps_realizes asegs _ _ _ _ (asta_evt RT AF Σ1 _ fs _ _ W1') Hc1').
    intros cf2 Hc2.
    destruct (ASTA_unpack RT Σ1 _ _ cf2 Hc2) as (ms2 & (-> & ST2) & Hc2').
    apply (EXC1 Σ1 fds0 fs (Z_to_bv 64 0xb897c) (Z_to_bv 64 usp) gp (Z_to_bv 64 TP_A) u0 u1 u2 c0 c1 (Z_to_bv 64 code) b1 b2 b3
             b4 b5 b6 b7 c2 c3 c4 c5 c6 c7 s8 s9 s10 s11 u3 u4 u5 u6 F1 fc1 m1 so code lo); try reflexivity; try assumption.
    + exact (XENV1x_of m1 XE1 FL1).
    + unfold call_ok. rewrite unsigned_lit by ul. rewrite SP1. split; [exact ST2|]. ul.
    + io_ssp_tac AF_DRV.
Qed.

End Tr4.
