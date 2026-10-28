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

Section Loop2.
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
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis MCP : memcpy_icontract RT e_memcpy.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis XENV_loc : xenv_laws XENV XENV_FP.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis IO_img : forall x, in_ranges IO_FP x -> client_static x /\ ~ drv_cell x /\ outside LIB_FP x.
Hypothesis XENV_img : forall x, in_ranges XENV_FP x -> client_static x /\ ~ drv_cell x /\ outside IO_FP x /\ outside LIB_FP x.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, g_read_stage in *; lia.

Theorem seg_mem : forall len cap,
  cps bsegs (RMEM RT OUT_rep ERR_rep XENV LIB argvb fs data len cap)
            (fun c => (exists len', len < len' /\ RL RT OUT_rep ERR_rep XENV LIB argvb fs data len' cap c)
                      \/ RTOOBIG RT OUT_rep ERR_rep XENV LIB argvb fs data c
                      \/ RGROW RT OUT_rep ERR_rep XENV LIB argvb fs data len cap c).
Proof using AF AF_DRV MCP OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img.
  intros len cap T c HR Hk.
  destruct HR as (Σ & usp & ap & path & buf & n & gp & t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6
                  & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & F & fc & m & FRM & HA & HD & HLS & HBUF & HSTG & Hn & Hl & Hlc & Hld & HCAP).
  pose proof HD as ((ART0 & MI0 & CLX0 & ARGV0 & FR0 & ST0 & B16 & UA & ULO & USP0) & HB & Hap & Hhi & SPW).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  pose proof HLS as (LV & FRS & CR & USP0').
  pose proof (cap_ok_range cap HCAP) as CAPR.
  assert (INB : In (buf, cap) (rt_live RT Σ)) by (rewrite LV; left; reflexivity).
  pose proof (af_live_range RT AF Σ m buf cap ART0 INB) as (PR1 & PR2 & PR3).
  set (lo := rt_sp0 RT Σ - STACK_WIN) in *.
  set (bs := firstn (Z.to_nat n) (skipn (Z.to_nat len) data)) in *.
  assert (LBS : Z.of_nat (length bs) = n) by (unfold bs; rewrite length_firstn, length_skipn; lia).
  assert (EU : bv_unsigned (Z_to_bv 64 (usp - 80)) = usp - 80) by (apply unsigned_lit; ul).
  apply (MCP Σ (PMfd (FD argvb (len + n)) fs) (Z_to_bv 64 0xb4618) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2
           (Z_to_bv 64 2) (Z_to_bv 64 buf) (Z_to_bv 64 (buf + len)) (Z_to_bv 64 g_read_stage) (Z_to_bv 64 n) a3 a4 a5 a6 a7
           (Z_to_bv 64 path) (Z_to_bv 64 len) (Z_to_bv 64 3) (Z_to_bv 64 cap) (Z_to_bv 64 g_read_stage) (Z_to_bv 64 n)
           s8 s9 s10 s11 t3 t4 t5 t6 F fc m (buf + len) g_read_stage bs lo); try reflexivity; try assumption.
  - apply PMfd_fdfs_only.
  - apply PMfd_mat_stable.
  - rewrite LBS. reflexivity.
  - ul.
  - ul.
  - lia.
  - rewrite LBS. exact (checked_src_stage RT AF Σ m _ lo n ART0 ltac:(lia) ltac:(ul)).
  - rewrite LBS. exact (checked_dst_live RT AF Σ m _ buf cap (buf + len) n ART0 INB ltac:(lia) ltac:(lia) ltac:(lia)).
  - rewrite LBS. unfold g_read_stage, SEGTOP_A in *. lia.
  - unfold call_ok. rewrite EU. split; [exact ST0|]. ul.
  - intros cf1 Hc1.
    destruct (ASTA_unpack RT Σ _ _ cf1 Hc1) as (ms1 & (m1 & RS1 & (ART1 & MI1 & WM1 & ST1) & PRES1 & BS1) & Hc1').
    destruct RS1 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & ->). pose (fc' := fc).
    rewrite EU in ST1, PRES1. rewrite LBS in PRES1.
    rewrite (ret_pc_even 0xb4618) in Hc1' by lia.
    assert (CLX1 : CLX OUT_rep ERR_rep XENV LIB stdout_init m1)
      by exact (CLX_pres_ex OUT_rep ERR_rep IO_FP XENV XENV_FP LIB OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img
                  _ m m1 _ _ _ _ _ CLX0 PRES1 WM1 ltac:(intros x Hx; unfold SEGTOP_A in *; lia)).
    pose proof (agree_stack_pres_ex _ _ _ _ _ _ _ PRES1 ltac:(ul)) as AG1.
    assert (HD1 : DCTX RT OUT_rep ERR_rep XENV LIB argvb Σ usp ap path c0 c1 c2 c3 c4 c5 c6 c7 m1)
      by exact (DCTX_agree RT OUT_rep ERR_rep XENV LIB argvb AF Σ Σ usp ap path c0 c1 c2 c3 c4 c5 c6 c7 m m1 HD ART1 MI1 WM1 ST1
                  eq_refl CLX1 AG1 (auxc_of_pres_ex _ _ _ _ _ _ _ PRES1 ltac:(unfold EL_AUXV_CELL, SEGTOP_A in *; lia))).
    assert (HBUF1 : bytes_at bsegs m1 buf (firstn (Z.to_nat (len + n)) data)).
    { replace (Z.to_nat (len + n)) with (Z.to_nat len + Z.to_nat n)%nat by lia.
      rewrite <- firstn_app_skipn' by lia. apply bytes_at_app. split.
      - apply (bytes_at_agree bsegs m m1 _ _ HBUF). apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES1).
        intros x Hx. rewrite length_firstn in Hx. split; [| lia].
        right; right; left. exists buf, cap. split; [exact INB| lia].
      - rewrite length_firstn. replace (buf + Z.of_nat (Init.Nat.min (Z.to_nat len) (length data))) with (buf + len) by lia.
        exact BS1. }
    pose proof (AF_DRV Σ m1 ART1) as (SC1 & _).
    destruct (Z.ltb_spec (len + n) cap) as [LT|GE].
    +
      pose proof (cont_walk usp buf len n cap gp t0' t1' t2' (Z_to_bv 64 (buf + len)) a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 path)
                    (Z_to_bv 64 3) (Z_to_bv 64 g_read_stage) s8 s9 s10 s11 t3' t4' t5' t6' F' fc' m1 ltac:(lia) ltac:(lia) LT
                    ltac:(lia) MI1) as W1.
      lazymatch type of W1 with evt bsegs _ ?X =>
        assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
      clear W1.
      apply (cps_realizes bsegs _ _ _ _ (asta_evt RT AF Σ _ fs _ _ W1') Hc1').
      intros cf2 Hc2. apply Hk. left. exists (len + n). split; [lia|].
      destruct (ASTA_unpack RT Σ _ _ cf2 Hc2) as (ms2 & <- & Hc2').
      exists Σ, usp, ap, path, buf, gp, t0', t1', t2', a3', a4', a5', a6', a7', (Z_to_bv 64 buf), s8, s9, s10, s11, t3', t4', t5', t6'.
      exists c0, c1, c2, c3, c4, c5, c6, c7, F', fc', m1. split; [exact FRM|].
      split; [exact Hc2'|]. split; [exact HD1|]. split; [exact HLS|]. split; [exact HBUF1|].
      split; [lia|]. split; [lia| exact HCAP].
    + destruct (Z.eq_dec cap 67108864) as [ETOP|NTOP].
      *
        subst cap.
        pose proof (toobig_walk usp buf len n gp t0' t1' t2' (Z_to_bv 64 (buf + len)) a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 path)
                      (Z_to_bv 64 3) (Z_to_bv 64 g_read_stage) s8 s9 s10 s11 t3' t4' t5' t6' F' fc' m1 ltac:(lia) ltac:(lia)
                      ltac:(lia) SC1 MI1) as W1.
        lazymatch type of W1 with evt bsegs _ ?X =>
          assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
        clear W1.
        apply (cps_realizes bsegs _ _ _ _ (asta_evt RT AF Σ _ fs _ _ W1') Hc1').
        intros cf2 Hc2. apply Hk. right. left.
        destruct (ASTA_unpack RT Σ _ _ cf2 Hc2) as (ms2 & <- & Hc2').
        exists Σ, usp, ap, path, buf, gp, t0', t1', t2', a3', a4', a5', a6', a7', s8, s9, s10, s11, t3', t4', t5', t6'.
        exists c0, c1, c2, c3, c4, c5, c6, c7, F', fc', m1. split; [exact FRM|].
        replace (len + n) with 67108864 in Hc2' by lia.
        split; [exact Hc2'|]. split; [exact HD1|]. split; [exact HLS|]. lia.
      *
        pose proof (grow_walk usp buf len n cap gp t0' t1' t2' (Z_to_bv 64 (buf + len)) a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 path)
                      (Z_to_bv 64 3) (Z_to_bv 64 g_read_stage) s8 s9 s10 s11 t3' t4' t5' t6' F' fc' m1 ltac:(lia) ltac:(lia)
                      ltac:(lia) ltac:(lia) MI1) as W1.
        lazymatch type of W1 with evt bsegs _ ?X =>
          assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
        clear W1.
        apply (cps_realizes bsegs _ _ _ _ (asta_evt RT AF Σ _ fs _ _ W1') Hc1').
        intros cf2 Hc2. apply Hk. right. right.
        destruct (ASTA_unpack RT Σ _ _ cf2 Hc2) as (ms2 & <- & Hc2').
        exists Σ, usp, ap, path, buf, gp, t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', s8, s9, s10, s11, t3', t4', t5', t6'.
        exists c0, c1, c2, c3, c4, c5, c6, c7, F', fc', m1. split; [exact FRM|].
        replace (len + n) with cap in Hc2', HBUF1 by lia.
        split; [exact Hc2'|]. split; [exact HD1|]. split; [exact HLS|]. split; [exact HBUF1|].
        split; [lia|]. split; [lia|]. split; [lia| exact HCAP].
Qed.

End Loop2.
