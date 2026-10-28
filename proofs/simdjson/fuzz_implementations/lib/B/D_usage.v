(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac ImageA Nodes RzCPS NodesA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim Canon Stdio Prog.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_iface D_defs D_kit D_aex D_libiface D_clx X_aexdefs X_vecxdefs X_xdefs X_xiface Imp_libifaceA D_impkit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Lemma usage_walk : forall (usp ap : Z) (gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : word -> option byte) (lo argc : Z) (ptrs : list word) (p0 : word),
  argc <> 2 -> 0 <= argc <= 1024 ->
  stk bsegs m lo usp -> SEGTOP_A <= lo -> lo + 0x100000 <= usp -> usp mod 16 = 0 -> usp < 2^47 ->
  u64arr bsegs m ap ptrs -> nth_error ptrs 0 = Some p0 -> usp < ap -> ap + 8 <= 2^47 ->
  stderr_cells m -> mem_inv bsegs m ->
  evt bsegs (fun ms' => exists m', ms' = entry_st (Z_to_bv 64 0xb474c) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2
                                    (Z_to_bv 64 2) s1 (Z_to_bv 64 STDERR_FILE) (Z_to_bv 64 FMT_usage) p0 a3 a4 a5 a6 a7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_fprintf m'
       /\ munch [(usp - 80, usp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
       /\ (exists junk, rw_cells bsegs m' (usp - 80) [CB 8 junk; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 (Z_to_bv 64 MAIN_RA)])
       /\ stk bsegs m' lo (usp - 80))
    (entry_st (Z_to_bv 64 MAIN_RA) (Z_to_bv 64 usp) gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 (Z_to_bv 64 argc) (Z_to_bv 64 ap)
       a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc a_main m).
Proof.
  intros until p0. intros HA HAr ST SL LO U16 UT ARR Hp0 UA AT [SC1 SC2] MI.
  unfold entry_st, a_main. cbv [Z.of_nat] in *.
  pose proof (munch_refl [(usp - 80, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof ST as (STa & STb & _).
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  carve_frame 80%nat ST.
  unfold SEGTOP_A in SL. unfold GOT_STDERR, STDERR_VAR in SC1, SC2.
  assert (EA : bv_unsigned (Z_to_bv 64 argc) = argc) by (apply unsigned_lit; lia).
  do 12 step.
  if_true.
  do 3 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
    pose proof (u64arr_read bsegs mf ap ptrs 0 p0 (wa ap) ARR Hp0 ltac:(lia) ltac:(f_equal; lia)) as RD end.
  step. clear RD.
  do 3 step.
  apply evt_done. eexists. split.
  { unfold entry_st. reflexivity. }
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [eexists; exact FR| exact ST].
Qed.

Lemma usage_ret_walk : forall (usp : Z) (gp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v : word)
    (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : word -> option byte) (lo : Z)
    (c0 c1 c2 c3 c4 c5 c6 c7 : word) junk,
  stk bsegs m lo (usp - 80) -> SEGTOP_A <= lo -> lo + 0x100000 <= usp -> usp mod 16 = 0 -> usp < 2^47 ->
  rw_cells bsegs m (usp - 80) [CB 8 junk; C8 c7; C8 c6; C8 c5; C8 c4; C8 c3; C8 c2; C8 c1; C8 c0; C8 (Z_to_bv 64 MAIN_RA)] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms' => ms' = entry_st (Z_to_bv 64 0x15ff94) (Z_to_bv 64 usp) gp (Z_to_bv 64 TP_A) t0 t1 t2
                                    c0 c1 (Z_to_bv 64 2) a1 a2 a3 a4 a5 a6 a7
                                    c2 c3 c4 c5 c6 c7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_exit m
       /\ stk bsegs m lo usp)
    (MS (mkR (Z_to_bv 64 0xb474c) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2) s1 v a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb474c) fc None m (seg_rom bsegs)).
Proof.
  intros until junk. intros ST SL LO U16 UT FR MI.
  pose proof ST as (STa & STb & _). unfold SEGTOP_A in SL.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 (usp - 80)) = usp - 80) by (apply unsigned_lit; lia).
  do 13 step.
  rewrite (ret_pc_even MAIN_RA) by (unfold MAIN_RA; lia).
  unfold MAIN_RA. step.
  release_frame FR ST usp.
  apply evt_done. split; [| exact ST].
  unfold entry_st. replace (usp - 80 + 80) with usp by lia. reflexivity.
Qed.

Lemma nth0_argv_Z : forall (argv : list (list byte)) a0, nth_error argv 0 = Some a0 -> nth 0 (argv_Z argv) [] = map bv_unsigned a0.
Proof. intros [|x l] a0 H; cbn in H; [discriminate|]. injection H as ->. reflexivity. Qed.

Lemma fds0_lookup2 : fd_lookup fds0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
Proof. reflexivity. Qed.
Lemma fds0_lookup1 : fd_lookup fds0 (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)).
Proof. reflexivity. Qed.

Lemma outside_of_not_in_ranges : forall W x, ~ in_ranges W x -> outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x H; [exact I|]. cbn [outside]. split.
  - intros Hx. apply H. exists lo, hi. split; [left; reflexivity| exact Hx].
  - apply IH. intros (l & h & Hin & Hx). apply H. exists l, h. split; [right; exact Hin| exact Hx].
Qed.

Section Usage.
Variable RT : rt_sig.
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Variable XENV : mem -> Prop.
Variable XENV_FP : list (Z * Z).
Variable LIB : mem -> Prop.
Variable argvb : list (list byte).
Variable fs : Fs.
Hypothesis AF : art_facts RT.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis FPR : fprintf_stderr_icontract RT OUT_rep ERR_rep IO_FP.
Hypothesis EXC : exit_contract0 RT XENV LIB OUT_rep ERR_rep.
Hypothesis VARGV : valid_argv argvb.

Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis XENV_loc : xenv_laws XENV XENV_FP.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis IO_img : forall x, in_ranges IO_FP x -> client_static x /\ ~ drv_cell x /\ outside LIB_FP x.
Hypothesis XENV_img : forall x, in_ranges XENV_FP x -> client_static x /\ ~ drv_cell x /\ outside IO_FP x /\ outside LIB_FP x.

Theorem usage_cpsE : Z.of_nat (length argvb) <> 2 ->
  cpsE bsegs (START RT OUT_rep ERR_rep XENV LIB argvb fs) (evw 2 (msg_usage (nth 0 (argv_Z argvb) []))) (EXIT fs 2).
Proof using AF AF_DRV FPR EXC VARGV OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img.
  intros HL T c HS Hk.
  destruct HS as (Σ & usp & ap & gp & t0 & t1 & t2 & s0 & s1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & s5 & s6 & s7
                  & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & m & FRM & HA & HART & HMI & HCLX & HARGV & HAUX & HST & HSIG
                  & U16 & UA & ULO).
  destruct VARGV as (VA1 & VA2 & VA3 & VA4 & VA5).
  destruct HARGV as (ptrs & ARR & Lptrs & STR & SLKS).
  destruct (nth_error argvb 0) as [arg0|] eqn:Ha0; [| apply nth_error_None in Ha0; lia].
  destruct (nth_error ptrs 0) as [p0|] eqn:Hp0; [| apply nth_error_None in Hp0; lia].
  destruct (STR 0%nat arg0 p0 Ha0 Hp0) as (B0 & P0lo & P0hi).
  destruct (SLKS 0%nat arg0 p0 Ha0 Hp0) as (slack0 & SLK0 & SLKM0 & SLKB0).
  pose proof (proj1 (Forall_forall _ _) VA4 arg0 (nth_error_In _ _ Ha0)) as NZ0.
  pose proof (proj1 (Forall_forall _ _) VA3 arg0 (nth_error_In _ _ Ha0)) as LN0. cbv beta in NZ0, LN0.
  pose proof (af_sp0_range RT AF Σ m HART) as SP0R. unfold SEGTOP_A, STACK_WIN, USTACK_TOP in *.
  destruct HSIG as (LV & FRS & CR & USP0 & SPW).
  pose proof (AF_DRV Σ m HART) as (SC0 & _).
  pose proof (u64arr_bound bsegs m ap ptrs ARR) as ARB.
  set (lo := rt_sp0 RT Σ - 8388608) in *.
  rewrite (nth0_argv_Z argvb arg0 Ha0).
  replace (evw 2 (msg_usage (map bv_unsigned arg0))) with (evw 2 (fp_msg (FPusage (bv_unsigned p0) arg0)) ++ evw 1 (so_buf stdout_init))
    by (cbn [fp_msg so_buf stdout_init]; rewrite app_nil_r; reflexivity).

  pose proof (usage_walk usp ap gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
             (Z.of_nat (length argvb)) ptrs p0) as W1.
  lazymatch type of W1 with _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> evt bsegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; apply W1; try assumption; unfold SEGTOP_A; lia) end.
  clear W1.
  apply (cps_realizes bsegs _ _ _ c (asta_evt RT AF Σ fds0 fs _ _ W1') HA).
  intros c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1').

  assert (ART1 : ART RT Σ m1).
  { apply (af_frame RT AF Σ m m1 (usp - 80) HART); [unfold STACK_WIN; lia| |exact WM1].
    intros a Ha. apply MU1. cbn [outside]. split; [|exact I]. intros Hin. apply Ha. left. unfold USTACK_TOP. lia. }
  assert (AG1 : forall x, x < SEGTOP_A \/ ap <= x -> outside [(usp - 80, usp)] x) by (intros x Hx; cbn; unfold SEGTOP_A in *; split; [lia| exact I]).
  assert (CLX1 : CLX OUT_rep ERR_rep XENV LIB stdout_init m1).
  { apply (CLX_munch OUT_rep ERR_rep IO_FP XENV XENV_FP LIB OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img _ m m1 _ HCLX MU1 WM1).
    intros x Hx. apply AG1. left. unfold SEGTOP_A in *. lia. }
  pose proof CLX1 as (OUT1 & ERR1 & XE1 & _).
  assert (B1 : bytes_at bsegs m1 (bv_unsigned p0) (arg0 ++ [Z_to_bv 8 0])).
  { apply (bytes_at_agree bsegs m m1 _ _ B0). apply (agree_of_munch _ _ _ _ MU1). intros x Hx. apply AG1. right.
    rewrite length_app in Hx. cbn in Hx. lia. }

  eapply rz_conseq; [| apply t_eq_sym, t_emit_app].
  apply (FPR Σ fds0 fs (Z_to_bv 64 0xb474c) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2) s1
           (Z_to_bv 64 STDERR_FILE) (Z_to_bv 64 FMT_usage) p0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m1 (FPusage (bv_unsigned p0) arg0) STDERR_FILE lo); try reflexivity; try assumption.
  - unfold fp_arg. symmetry. apply Z_to_bv_bv_unsigned.
  - intros a s Hs. cbn [fp_str] in Hs. injection Hs as <- <-. split; [exact B1|]. split; [exact NZ0|].
    split; [lia|]. split; [split|].
    + intros _. split.
      * apply (af_acc_stack RT AF Σ m1 _ _ ART1); unfold STACK_WIN, USTACK_TOP; lia.
      * right. right. left. unfold STACK_WIN, USTACK_TOP. lia.
    + right. rewrite unsigned_lit by lia. lia.
    + split; [rewrite unsigned_lit by lia; lia|]. exists slack0. split; [| split; assumption].
      apply (bytes_at_agree bsegs m m1 _ _ SLK0). apply (agree_of_munch _ _ _ _ MU1). intros x Hx. apply AG1. right. lia.
  - io_ssp_tac AF_DRV.
  - unfold call_ok. rewrite unsigned_lit by lia. split; [exact ST1|]. unfold RT_STACK, STACK_WIN, USTACK_TOP. lia.
  - intros c2 Hc2.
    destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (v & m2 & RS & (ART2 & MI2 & WM2 & ST2) & PRES2 & ERR2 & OUTP2) & Hc2').
    destruct RS as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & ->).
    rewrite unsigned_lit in ST2, PRES2 by lia.
    assert (OUTS : forall x, SEGTOP_A <= x -> outside IO_FP x).
    { intros x Hx. apply outside_of_not_in_ranges. intros Hin. pose proof (client_static_range _ (proj1 (IO_img _ Hin))).
      unfold SEGTOP_A in *. lia. }
    destruct FR1 as (junk & FR1).
    assert (FR2 : rw_cells bsegs m2 (usp - 80) [CB 8 junk; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 (Z_to_bv 64 MAIN_RA)]).
    { apply (rw_cells_agree bsegs m1 m2 _ _ FR1); [| exact WM2]. apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES2).
      intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; unfold USTACK_TOP; lia| apply OUTS; unfold SEGTOP_A; lia]. }
    pose proof (OUTP2 stdout_init OUT1) as OUT2.
    assert (XL2 : XENV m2 /\ LIB m2).
    { pose proof (CLX_io OUT_rep ERR_rep IO_FP XENV XENV_FP LIB OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img
                    _ _ m1 m2 _ _ _ CLX1 PRES2 WM2 OUT2 ERR2) as (_ & _ & XE2 & LI2 & _). exact (conj XE2 LI2). }
    destruct XL2 as [XE2 LI2].

    pose proof (usage_ret_walk usp gp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
                  F' fc' m2 lo s0 s1 s2 s3 s4 s5 s6 s7 junk ST2 ltac:(unfold SEGTOP_A; lia) ltac:(lia) U16 ltac:(lia) FR2 MI2) as W2.
    rewrite (ret_pc_even 0xb474c) in Hc2' by lia.
    lazymatch type of W2 with evt bsegs _ ?X =>
      assert (W2' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W2) end.
    clear W2.
    apply (cps_realizes bsegs _ _ _ _ (asta_evt RT AF Σ fds0 fs _ _ W2') Hc2').
    intros c3 Hc3.
    destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & (-> & ST3) & Hc3').

    apply (EXC Σ fds0 fs (Z_to_bv 64 0x15ff94) (Z_to_bv 64 usp) gp (Z_to_bv 64 TP_A) t0' t1' t2' s0 s1 (Z_to_bv 64 2) a1' a2' a3'
             a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6' F' fc' m2 stdout_init 2 lo);
      try reflexivity; try assumption.
    + lia.
    + left. reflexivity.
    + unfold call_ok. rewrite unsigned_lit by lia. split; [exact ST3|]. unfold RT_STACK, STACK_WIN, USTACK_TOP. lia.
    + rewrite unsigned_lit by lia. unfold X_DEPTH, RT_STACK, STACK_WIN, USTACK_TOP in *. try unfold VECX_DEPTH in *. lia.
    + eapply (io_ssp_pres_fp IO_FP _ _ _ m1 m2); [| io_ssp_tac AF_DRV| exact (AF_DRV _ _ ART2)| exact PRES2].
      intros x Hx. apply outside_of_not_in_ranges'. intros Hin. apply (proj1 (proj2 (IO_img x Hin))). unfold drv_cell. right; left; exact Hx.
Qed.

End Usage.
