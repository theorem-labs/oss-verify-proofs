(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac ImageA Nodes RzCPS NodesA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim Canon Stdio Prog.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface D_iface D_defs D_kit D_auxv D_aex D_libiface D_clx. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import D_usage D_open D_read. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_rlkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import D_loopdefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma file_read_firstn : forall data len count, 0 <= len < 2^64 -> 0 <= count < 2^64 ->
  file_read data (Z_to_bv 64 len) (Z_to_bv 64 count) = firstn (Z.to_nat count) (skipn (Z.to_nat len) data).
Proof. intros data len count H1 H2. rewrite file_read_unguarded. unfold word_to_nat. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma length_firstn_skipn : forall {X} (l : list X) len count, 0 <= len <= Z.of_nat (length l) -> 0 <= count ->
  Z.of_nat (length (firstn (Z.to_nat count) (skipn (Z.to_nat len) l))) = Z.min count (Z.of_nat (length l) - len).
Proof. intros X l len count H1 H2. rewrite length_firstn, length_skipn. lia. Qed.

Lemma firstn_len_firstn : forall {X} (l : list X) k, firstn (length (firstn k l)) l = firstn k l.
Proof. intros X l k. revert l. induction k as [|k IH]; intros [|x l]; cbn; auto. f_equal. apply IH. Qed.

Lemma FD_step : forall argvb len k, 0 <= len -> 0 <= k -> len + k < 2^64 ->
  fd_insert (FD argvb len) (Z_to_bv 64 3) (FdFile (path_b argvb) (Z_to_bv 64 len + Z_to_bv 64 k)%bv) = FD argvb (len + k).
Proof.
  intros argvb len k H1 H2 H3. unfold FD. rewrite fd_insert_twice. f_equal. f_equal. apply lit_add_lit.
Qed.

Section Loop1.
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
Hypothesis HDATA : fs_lookup fs (path_b argvb) = Some data.
Hypothesis AF : art_facts RT.
Hypothesis RFILE : read_icontract_file RT.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis XENV_loc : xenv_laws XENV XENV_FP.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis IO_img : forall x, in_ranges IO_FP x -> client_static x /\ ~ drv_cell x /\ outside LIB_FP x.
Hypothesis XENV_img : forall x, in_ranges XENV_FP x -> client_static x /\ ~ drv_cell x /\ outside IO_FP x /\ outside LIB_FP x.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, g_read_stage in *; lia.

Theorem seg_read : forall len cap,
  cps asegs (RL RT OUT_rep ERR_rep XENV LIB argvb fs data len cap)
            (fun c => RDONE RT OUT_rep ERR_rep XENV LIB argvb fs data c \/ RMEM RT OUT_rep ERR_rep XENV LIB argvb fs data len cap c).
Proof using HDATA AF RFILE OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img.
  intros len cap T c HR Hk.
  destruct HR as (Σ & usp & ap & path & buf & gp & t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6
                  & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & F & fc & m & FRM & HA & HD & HLS & HBUF & Hlen & Hld & HCAP).
  pose proof HD as ((ART0 & MI0 & CLX0 & ARGV0 & FR0 & ST0 & B16 & UA & ULO & USP0) & HB & Hap & Hhi & SPW).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  pose proof HLS as (LV & FRS & CR & USP0').
  pose proof (cap_ok_range cap HCAP) as CAPR.
  pose proof (af_live_range RT AF Σ m buf cap ART0 ltac:(rewrite LV; left; reflexivity)) as (PR1 & PR2 & PR3).
  set (lo := rt_sp0 RT Σ - STACK_WIN) in *.
  set (count := Z.min (cap - len) 65536) in *.
  assert (CNT : 0 < count <= 65536) by lia.
  assert (EU : bv_unsigned (Z_to_bv 64 (usp - 80)) = usp - 80) by (apply unsigned_lit; ul).
  pose proof CLX0 as (_ & _ & _ & _ & _ & _ & RS0).
  apply (RFILE Σ (FD argvb len) fs (Z_to_bv 64 0xb1250) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2)
           (Z_to_bv 64 buf) (Z_to_bv 64 3) (Z_to_bv 64 g_read_stage) (Z_to_bv 64 count) a3 a4 a5 a6 a7 (Z_to_bv 64 path)
           (Z_to_bv 64 len) (Z_to_bv 64 3) (Z_to_bv 64 cap) (Z_to_bv 64 g_read_stage) s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
           3 g_read_stage count (path_b argvb) (Z_to_bv 64 len) data lo); try reflexivity; try assumption.
  - lia.
  - ul.
  - exact (checked_dst_stage RT AF Σ m _ count ART0 RS0 ltac:(lia)).
  - unfold call_ok. rewrite EU. split; [exact ST0|]. ul.
  - intros cf1 Hc1.
    rewrite (file_read_firstn data len count) in Hc1 by ul.
    set (bs := firstn (Z.to_nat count) (skipn (Z.to_nat len) data)) in *.
    assert (LBS : Z.of_nat (length bs) = Z.min count (Z.of_nat (length data) - len)) by (apply length_firstn_skipn; lia).
    destruct (ASTA_unpack RT Σ _ _ cf1 Hc1) as (ms1 & (m1 & RS1 & (ART1 & MI1 & WM1 & ST1) & PRES1 & BS1) & Hc1').
    destruct RS1 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & ->). pose (fc' := fc).
    rewrite EU in ST1, PRES1.
    rewrite (ret_pc_even 0xb1250) in Hc1' by lia.
    rewrite (FD_step argvb len (Z.of_nat (length bs))) in Hc1' by lia.
    assert (CLX1 : CLX OUT_rep ERR_rep XENV LIB stdout_init m1)
      by exact (CLX_read OUT_rep ERR_rep IO_FP XENV XENV_FP LIB OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img
                  _ m m1 _ _ _ bs CLX0 PRES1 WM1 BS1 ltac:(lia)).
    pose proof (agree_stack_pres_fp _ _ _ _ _ _ PRES1 ltac:(intros x Hx; cbn; split; [ul| exact I])) as AG1.
    assert (HD1 : DCTX RT OUT_rep ERR_rep XENV LIB argvb Σ usp ap path c0 c1 c2 c3 c4 c5 c6 c7 m1)
      by exact (DCTX_agree RT OUT_rep ERR_rep XENV LIB argvb AF Σ Σ usp ap path c0 c1 c2 c3 c4 c5 c6 c7 m m1 HD ART1 MI1 WM1 ST1
                  eq_refl CLX1 AG1 (auxc_of_pres_fp _ _ _ _ _ _ PRES1 ltac:(intros x Hx; pose proof (auxc_range x Hx); cbn; split; [ul| exact I]))).
    assert (HBUF1 : bytes_at asegs m1 buf (firstn (Z.to_nat len) data)).
    { apply (bytes_at_agree asegs m m1 _ _ HBUF). apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES1).
      intros x Hx. rewrite length_firstn in Hx. split.
      - right; right; left. exists buf, cap. rewrite LV. split; [left; reflexivity| lia].
      - cbn. split; [| exact I]. unfold g_read_stage, SEGTOP_A in *. lia. }
    destruct (Z.eq_dec (Z.of_nat (length bs)) 0) as [Z0|NZ].
    +
      assert (EL : len = Z.of_nat (length data)) by lia.
      replace (len_word bs) with (Z_to_bv 64 0) in Hc1' by (unfold len_word; rewrite Z0; reflexivity).
      pose proof (eof_walk usp gp t0' t1' t2' (Z_to_bv 64 buf) a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 path) (Z_to_bv 64 len)
                    (Z_to_bv 64 cap) (Z_to_bv 64 g_read_stage) s7 s8 s9 s10 s11 t3' t4' t5' t6' F' fc' m1 MI1) as W1.
      lazymatch type of W1 with evt asegs _ ?X =>
        assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
      clear W1.
      apply (cps_realizes asegs _ _ _ _ (asta_evt RT AF Σ _ fs _ _ W1') Hc1').
      intros cf2 Hc2. apply Hk. left.
      destruct (ASTA_unpack RT Σ _ _ cf2 Hc2) as (ms2 & <- & Hc2').
      exists Σ, usp, ap, path, buf, cap, gp, t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', s8, s9, s10, s11, t3', t4', t5', t6'.
      exists c0, c1, c2, c3, c4, c5, c6, c7, F', fc', m1. split; [exact FRM|].
      rewrite Z0, Z.add_0_r, EL in Hc2'.
      split; [exact Hc2'|]. split; [exact HD1|]. split; [exact HLS|].
      split; [| split; [lia| exact HCAP]].
      rewrite EL, Nat2Z.id, firstn_all in HBUF1. exact HBUF1.
    +
      pose proof (read_ok_walk usp buf len (Z.of_nat (length bs)) gp t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 path)
                    (Z_to_bv 64 3) (Z_to_bv 64 cap) s7 s8 s9 s10 s11 t3' t4' t5' t6' F' fc' m1 ltac:(lia) ltac:(lia) ltac:(lia)
                    ltac:(ul) MI1) as W1.
      lazymatch type of W1 with evt asegs _ ?X =>
        assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
      clear W1.
      apply (cps_realizes asegs _ _ _ _ (asta_evt RT AF Σ _ fs _ _ W1') Hc1').
      intros cf2 Hc2. apply Hk. right.
      destruct (ASTA_unpack RT Σ _ _ cf2 Hc2) as (ms2 & <- & Hc2').
      exists Σ, usp, ap, path, buf, (Z.of_nat (length bs)), gp, t0', t1', t2', a3', a4', a5', a6', a7', s8, s9, s10, s11, t3', t4', t5', t6'.
      exists c0, c1, c2, c3, c4, c5, c6, c7, F', fc', m1. split; [exact FRM|].
      split; [exact Hc2'|]. split; [exact HD1|]. split; [exact HLS|]. split; [exact HBUF1|].
      split; [rewrite Nat2Z.id; unfold bs; rewrite firstn_len_firstn; exact BS1|].
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia| exact HCAP].
Qed.

End Loop1.
