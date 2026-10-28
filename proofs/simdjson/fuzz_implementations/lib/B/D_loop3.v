(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac ImageA Nodes RzCPS NodesA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim Canon Stdio Prog.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_iface D_defs D_kit D_auxv D_aex D_libiface D_clx D_usage D_open D_read D_rlkit D_loopdefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma live_remove_second : forall nb n1 buf n2, nb <> buf -> live_remove buf [(nb, n1); (buf, n2)] = [(nb, n1)].
Proof.
  intros nb n1 buf n2 H. unfold live_remove. cbn. apply Z.eqb_neq in H. rewrite H. cbn. rewrite Z.eqb_refl. reflexivity.
Qed.

Section Loop3.
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
Hypothesis FRE : free_contract RT.
Hypothesis MCP : memcpy_icontract RT e_memcpy.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis XENV_loc : xenv_laws XENV XENV_FP.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis IO_img : forall x, in_ranges IO_FP x -> client_static x /\ ~ drv_cell x /\ outside LIB_FP x.
Hypothesis XENV_img : forall x, in_ranges XENV_FP x -> client_static x /\ ~ drv_cell x /\ outside IO_FP x /\ outside LIB_FP x.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, g_read_stage in *; lia.
Local Notation CLXp := (CLX_pres OUT_rep ERR_rep IO_FP XENV XENV_FP LIB OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img).
Local Notation CLXx := (CLX_pres_ex OUT_rep ERR_rep IO_FP XENV XENV_FP LIB OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img).

Theorem seg_grow : forall len cap,
  cps bsegs (RGROW RT OUT_rep ERR_rep XENV LIB argvb fs data len cap) (RL RT OUT_rep ERR_rep XENV LIB argvb fs data cap (2 * cap)).
Proof using AF MAL FRE MCP OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img.
  intros len cap T c HR Hk.
  destruct HR as (Σ & usp & ap & path & buf & gp & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6
                  & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & F & fc & m & FRM & HA & HD & HLS & HBUF & Hlc & Hcd & Htop & HCAP).
  pose proof HD as ((ART0 & MI0 & CLX0 & ARGV0 & FR0 & ST0 & B16 & UA & ULO & USP0) & HB & Hap & Hhi & SPW).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  pose proof HLS as (LV & FRS & CR & USP0').
  pose proof (cap_ok_range cap HCAP) as CAPR.
  pose proof (cap_ok_double cap HCAP Htop) as HCAP2. pose proof (cap_ok_range _ HCAP2) as CAPR2.
  assert (INB : In (buf, cap) (rt_live RT Σ)) by (rewrite LV; left; reflexivity).
  pose proof (af_live_range RT AF Σ m buf cap ART0 INB) as (PR1 & PR2 & PR3).
  set (lo := rt_sp0 RT Σ - STACK_WIN) in *.
  assert (EU : bv_unsigned (Z_to_bv 64 (usp - 80)) = usp - 80) by (apply unsigned_lit; ul).

  apply (MAL Σ (PMfd (FD argvb cap) fs) (Z_to_bv 64 0xb4640) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2)
           (Z_to_bv 64 buf) (Z_to_bv 64 (2 * cap)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 path) (Z_to_bv 64 cap) (Z_to_bv 64 3)
           (Z_to_bv 64 (2 * cap)) (Z_to_bv 64 g_read_stage) (Z_to_bv 64 buf) s8 s9 s10 s11 t3 t4 t5 t6 F fc m (2 * cap) lo);
    try reflexivity; try assumption.
  - apply PMfd_fdfs_only.
  - apply PMfd_mat_stable.
  - lia.
  - rewrite LV. reflexivity.
  - unfold mcost, DCOST, CREDIT_DRV in *. destruct (Z.leb_spec (2 * cap) 64512); lia.
  - unfold call_ok. rewrite EU. split; [exact ST0|]. ul.
  - unfold unwind_ok. rewrite EU, !unsigned_lit by lia. left. ul.
  - intros cf1 (Σ1 & nb & Hc1 & LV1 & FRS1 & SP1 & CR1 & Pnb & Pal & Ptop).
    destruct (ASTA_unpack RT Σ1 _ _ cf1 Hc1) as (ms1 & (m1 & RS1 & (ART1 & MI1 & WM1 & ST1) & PRES1 & WR1 & ACC1) & Hc1').
    destruct RS1 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & ->). pose (fc' := fc).
    rewrite EU in ST1, PRES1.
    rewrite (ret_pc_even 0xb4640) in Hc1' by lia.
    assert (CLX1 : CLX OUT_rep ERR_rep XENV LIB stdout_init m1) by exact (CLXp _ m m1 _ _ _ CLX0 PRES1 WM1).
    pose proof (agree_stack_pres _ _ _ _ _ PRES1) as AG1.
    assert (HD1 : DCTX RT OUT_rep ERR_rep XENV LIB argvb Σ1 usp ap path c0 c1 c2 c3 c4 c5 c6 c7 m1)
      by exact (DCTX_agree RT OUT_rep ERR_rep XENV LIB argvb AF Σ Σ1 usp ap path c0 c1 c2 c3 c4 c5 c6 c7 m m1 HD ART1 MI1 WM1 ST1
                  SP1 CLX1 AG1 (auxc_of_pres _ _ _ _ _ PRES1)).
    assert (HBUF1 : bytes_at bsegs m1 buf (firstn (Z.to_nat cap) data)).
    { apply (bytes_at_agree bsegs m m1 _ _ HBUF). apply (agree_of_pres _ _ _ _ _ _ PRES1).
      intros x Hx. rewrite length_firstn in Hx. right; right; left. exists buf, cap. split; [exact INB| lia]. }
    assert (INN1 : In (nb, 2 * cap) (rt_live RT Σ1)) by (rewrite LV1; left; reflexivity).
    assert (INB1 : In (buf, cap) (rt_live RT Σ1)) by (rewrite LV1, LV; right; left; reflexivity).
    assert (DISJ : nb + 2 * cap <= buf \/ buf + cap <= nb).
    { apply (af_live_disj RT AF Σ1 m1 nb (2 * cap) buf cap [] [(buf, cap)] ART1); [rewrite LV1, LV; reflexivity| left; reflexivity]. }
    pose proof (af_live_range RT AF Σ1 m1 nb (2 * cap) ART1 INN1) as (NR1 & NR2 & NR3).

    pose proof (grow_ret_walk1 usp buf cap nb gp t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 path) (Z_to_bv 64 buf)
                  (Z_to_bv 64 3) (Z_to_bv 64 (2 * cap)) (Z_to_bv 64 g_read_stage) s8 s9 s10 s11 t3' t4' t5' t6' F' fc' m1
                  ltac:(ul) ltac:(lia) MI1) as W1.
    lazymatch type of W1 with evt bsegs _ ?X =>
      assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
    clear W1.
    apply (cps_realizes bsegs _ _ _ _ (asta_evt RT AF Σ1 _ fs _ _ W1') Hc1').
    intros cf2 Hc2.
    destruct (ASTA_unpack RT Σ1 _ _ cf2 Hc2) as (ms2 & <- & Hc2').
    set (bs := firstn (Z.to_nat cap) data) in *.
    assert (LBS : Z.of_nat (length bs) = cap) by (unfold bs; rewrite length_firstn; lia).
    apply (MCP Σ1 (PMfd (FD argvb cap) fs) (Z_to_bv 64 0xb465c) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0' t1' t2'
             (Z_to_bv 64 2) (Z_to_bv 64 nb) (Z_to_bv 64 nb) (Z_to_bv 64 buf) (Z_to_bv 64 cap) a3' a4' a5' a6' a7' (Z_to_bv 64 path)
             (Z_to_bv 64 cap) (Z_to_bv 64 3) (Z_to_bv 64 (2 * cap)) (Z_to_bv 64 g_read_stage) (Z_to_bv 64 buf) s8 s9 s10 s11
             t3' t4' t5' t6' F' fc' m1 nb buf bs lo); try reflexivity; try assumption.
    + apply PMfd_fdfs_only.
    + apply PMfd_mat_stable.
    + rewrite LBS. reflexivity.
    + ul.
    + ul.
    + lia.
    + rewrite LBS. exact (checked_src_live RT AF Σ1 m1 _ lo buf cap buf cap ART1 INB1 ltac:(lia) ltac:(lia) ltac:(rewrite SP1; lia)).
    + rewrite LBS. exact (checked_dst_live RT AF Σ1 m1 _ nb (2 * cap) nb cap ART1 INN1 ltac:(lia) ltac:(lia) ltac:(lia)).
    + rewrite LBS. lia.
    + unfold call_ok. rewrite EU, SP1. split; [exact ST1|]. ul.
    + intros cf3 Hc3.
      destruct (ASTA_unpack RT Σ1 _ _ cf3 Hc3) as (ms3 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & BS2) & Hc3').
      destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & ->). pose (fc2 := fc').
      rewrite EU in ST2, PRES2. rewrite LBS in PRES2.
      rewrite (ret_pc_even 0xb465c) in Hc3' by lia.
      assert (CLX2 : CLX OUT_rep ERR_rep XENV LIB stdout_init m2)
        by exact (CLXx _ m1 m2 _ _ _ _ _ CLX1 PRES2 WM2 ltac:(intros x Hx; unfold SEGTOP_A in *; lia)).
      pose proof (agree_stack_pres_ex _ _ _ _ _ _ _ PRES2 ltac:(ul)) as AG2.
      assert (HD2 : DCTX RT OUT_rep ERR_rep XENV LIB argvb Σ1 usp ap path c0 c1 c2 c3 c4 c5 c6 c7 m2).
      { apply (DCTX_agree RT OUT_rep ERR_rep XENV LIB argvb AF Σ1 Σ1 usp ap path c0 c1 c2 c3 c4 c5 c6 c7 m1 m2 HD1 ART2 MI2 WM2);
          [rewrite SP1; exact ST2| reflexivity| exact CLX2| exact AG2| exact (auxc_of_pres_ex _ _ _ _ _ _ _ PRES2 ltac:(unfold EL_AUXV_CELL, SEGTOP_A in *; lia))]. }

      pose proof (grow_ret_walk2 usp buf gp u0 u1 u2 (Z_to_bv 64 nb) b1 b2 b3 b4 b5 b6 b7 (Z_to_bv 64 path) (Z_to_bv 64 nb)
                    (Z_to_bv 64 cap) (Z_to_bv 64 3) (Z_to_bv 64 (2 * cap)) (Z_to_bv 64 g_read_stage) s8 s9 s10 s11 u3 u4 u5 u6
                    F2 fc2 m2 MI2) as W2.
      lazymatch type of W2 with evt bsegs _ ?X =>
        assert (W2' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W2) end.
      clear W2.
      apply (cps_realizes bsegs _ _ _ _ (asta_evt RT AF Σ1 _ fs _ _ W2') Hc3').
      intros cf4 Hc4.
      destruct (ASTA_unpack RT Σ1 _ _ cf4 Hc4) as (ms4 & <- & Hc4').
      apply (FRE Σ1 (PMfd (FD argvb cap) fs) (Z_to_bv 64 0xb4664) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) u0 u1 u2
               (Z_to_bv 64 2) (Z_to_bv 64 nb) (Z_to_bv 64 buf) b1 b2 b3 b4 b5 b6 b7 (Z_to_bv 64 path) (Z_to_bv 64 cap)
               (Z_to_bv 64 3) (Z_to_bv 64 (2 * cap)) (Z_to_bv 64 g_read_stage) (Z_to_bv 64 buf) s8 s9 s10 s11 u3 u4 u5 u6
               F2 fc2 m2 buf cap lo); try reflexivity; try assumption.
      * apply PMfd_fdfs_only.
      * apply PMfd_mat_stable.
      * unfold call_ok. rewrite EU, SP1. split; [exact ST2|]. ul.
      * unfold unwind_ok. rewrite EU, !unsigned_lit by lia. left. ul.
      * intros cf5 (Σ2 & v & Hc5 & LV2 & FRS2 & SP2 & CR2).
        destruct (ASTA_unpack RT Σ2 _ _ cf5 Hc5) as (ms5 & (m3 & RS3 & (ART3 & MI3 & ST3) & PRES3) & Hc5').
        destruct RS3 as (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & F3 & ->). pose (fc3 := fc2).
        rewrite EU in ST3, PRES3.
        rewrite (ret_pc_even 0xb4664) in Hc5' by lia.
        rewrite LV1, LV, live_remove_second in LV2 by lia.
        assert (CLX3 : CLX OUT_rep ERR_rep XENV LIB stdout_init m3)
          by exact (CLX_pres_nw OUT_rep ERR_rep IO_FP XENV XENV_FP LIB OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img _ m2 m3 _ _ _ CLX2 PRES3).
        pose proof (agree_stack_pres _ _ _ _ _ PRES3) as AG3.
        assert (HD3 : DCTX RT OUT_rep ERR_rep XENV LIB argvb Σ2 usp ap path c0 c1 c2 c3 c4 c5 c6 c7 m3).
        { apply (DCTX_agree_nw RT OUT_rep ERR_rep XENV LIB argvb AF Σ1 Σ2 usp ap path c0 c1 c2 c3 c4 c5 c6 c7 m2 m3 HD2 ART3 MI3);
            [rewrite SP1; exact ST3| rewrite SP2, SP1; reflexivity| exact CLX3| exact AG3| exact (auxc_of_pres _ _ _ _ _ PRES3)]. }
        assert (HBUF3 : bytes_at bsegs m3 nb (firstn (Z.to_nat cap) data)).
        { apply (bytes_at_agree bsegs m2 m3 _ _ BS2). apply (agree_of_pres _ _ _ _ _ _ PRES3).
          intros x Hx. rewrite LBS in Hx. right; right; left. exists nb, (2 * cap). rewrite LV2. split; [left; reflexivity| lia]. }

        pose proof (grow_ret_walk3 usp nb cap gp w0 w1 w2 v d1 d2 d3 d4 d5 d6 d7 (Z_to_bv 64 path) (Z_to_bv 64 3)
                      (Z_to_bv 64 g_read_stage) (Z_to_bv 64 buf) s8 s9 s10 s11 w3 w4 w5 w6 F3 fc3 m3 ltac:(lia) MI3) as W3.
        lazymatch type of W3 with evt bsegs _ ?X =>
          assert (W3' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W3) end.
        clear W3.
        apply (cps_realizes bsegs _ _ _ _ (asta_evt RT AF Σ2 _ fs _ _ W3') Hc5').
        intros cf6 Hc6. apply Hk.
        destruct (ASTA_unpack RT Σ2 _ _ cf6 Hc6) as (ms6 & <- & Hc6').
        exists Σ2, usp, ap, path, nb, gp, w0, w1, w2, d3, d4, d5, d6, d7, (Z_to_bv 64 buf), s8, s9, s10, s11, w3, w4, w5, w6.
        exists c0, c1, c2, c3, c4, c5, c6, c7, F3, fc3, m3. split; [exact FRM|].
        split; [exact Hc6'|]. split; [exact HD3|].
        split; [split; [exact LV2|]; split; [rewrite FRS2, FRS1; exact FRS|]; split; [rewrite CR2, CR1; unfold mcost, DCOST, CREDIT_DRV in *;
                 destruct (Z.leb_spec (2 * cap) 64512); lia| rewrite SP2, SP1; exact USP0']|].
        split; [exact HBUF3|]. split; [lia|]. split; [lia| exact HCAP2].
Qed.

End Loop3.
