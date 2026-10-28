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
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_iface D_defs D_kit D_auxv D_libiface D_clx D_rlkit X_aexdefs D_aex D_trpro D_trwalk X_xdefs Imp_libifaceA D_impkit D_trdefs D_tr1 D_tr2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma live_remove_head : forall owned n buf cap, owned <> buf -> live_remove owned [(owned, n); (buf, cap)] = [(buf, cap)].
Proof.
  intros owned n buf cap H. unfold live_remove. cbn. rewrite Z.eqb_refl. cbn.
  replace (buf =? owned) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.

Section Tr3.
Variable RT : rt_sig.
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Variable fs : Fs.
Hypothesis AF : art_facts RT.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis MAL : malloc_contract RT.
Hypothesis FRE : free_contract RT.
Hypothesis FRN : free_null_contract RT.
Hypothesis MCP : memcpy_icontract RT e_memcpy.
Hypothesis FUZZ : fuzz_one_cps_imp RT imp_libA.
Hypothesis VPR : vprintf_emit0_icontract RT OUT_rep ERR_rep IO_FP.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis IO_img : forall x, in_ranges IO_FP x -> client_static x /\ ~ drv_cell x /\ outside LIB_FP x.
Hypothesis IO_img2 : forall x, in_ranges IO_FP x -> outside IMP_FP_A x /\ ~ in_ranges AEX_FPA x.
Hypothesis XENV_img : forall x, in_ranges XENV_FP0 x -> client_static x /\ ~ drv_cell x /\ outside IO_FP x /\ outside LIB_FP x.
Notation CLXv := (CLXv OUT_rep ERR_rep).

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, FUZZ_STACK_IMP, FUZZ_STACK, FUZZ_COST_IMP, CREDIT_DRV, g_read_stage in *; lia.

Lemma tr_later : forall n k j A8 usp buf cap x0 x1 x2 x3 x4 x5 x6 x7, Z.to_nat k = n -> 1 <= k <= 4 -> (j + n < 499)%nat ->
  cpsE bsegs (TLOOP RT OUT_rep ERR_rep fs k (Some A8) (so_lines j) usp buf cap x0 x1 x2 x3 x4 x5 x6 x7) []
             (TFREE RT OUT_rep ERR_rep fs A8 (so_lines (j + n)) usp buf cap x0 x1 x2 x3 x4 x5 x6 x7).
Proof using AF AF_DRV FUZZ VPR OUT_loc ERR_loc IO_img IO_img2 XENV_img.
  induction n as [|n IH]; intros k j A8 usp buf cap x0 x1 x2 x3 x4 x5 x6 x7 Hn Hk Hj; [lia|].
  change ([] : list event) with (evw 1 (emit0_out (so_lines j)) ++ []).
  eapply cpsE_seq; [apply (tr_iter RT OUT_rep ERR_rep IO_FP fs AF AF_DRV FUZZ VPR OUT_loc ERR_loc IO_img IO_img2 XENV_img); right; exists j; split; [lia| reflexivity]|].
  rewrite emit0_next_lines.
  intros T c (B & EQB & HC) Hk'. pose proof (EQB A8 eq_refl) as EB. subst B. destruct HC as [(K1 & HL)|(K1 & HF)].
  - replace (j + S n)%nat with (S j + n)%nat in Hk' by lia.
    exact (IH (k - 1) (S j) A8 usp buf cap x0 x1 x2 x3 x4 x5 x6 x7 ltac:(lia) ltac:(lia) ltac:(lia) T c HL Hk').
  - assert (n = 0%nat) by lia. subst n. replace (j + 1)%nat with (S j) in Hk' by lia.
    exact (cpsE_nil bsegs _ _ (cps_refl bsegs _) T c HF Hk').
Qed.

Lemma live_remove_head3 : forall A8 owned n buf cap, owned <> A8 -> owned <> buf ->
  live_remove owned [(A8, 8); (owned, n); (buf, cap)] = [(A8, 8); (buf, cap)].
Proof.
  intros A8 owned n buf cap H1 H2. unfold live_remove. cbn.
  replace (A8 =? owned) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Z.eqb_refl. cbn.
  replace (buf =? owned) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.

Lemma tr_end : forall A8 so usp buf cap x0 x1 x2 x3 x4 x5 x6 x7,
  cps bsegs (TFREE RT OUT_rep ERR_rep fs A8 so usp buf cap x0 x1 x2 x3 x4 x5 x6 x7)
            (TRET RT OUT_rep ERR_rep fs A8 so usp buf cap x0 x1 x2 x3 x4 x5).
Proof using AF FRE FRN OUT_loc ERR_loc IO_img XENV_img.
  intros A8 so usp buf cap x0 x1 x2 x3 x4 x5 x6 x7 T c HF Hk.
  destruct HF as (Σ & plen & d & owned & payload & gp & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s3 & s7 & s8 & s9 & s10 & s11
                  & t3 & t4 & t5 & t6 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & F & fc & m & HA & HT).
  pose proof HT as (ART0 & MI0 & CLX0 & FR0 & TF0 & ST0 & B16 & ULO & USP0 & SPW & LV & FRS & PL & PB & BD & P0 & P1 & CAP0 & UT0).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  set (lo := rt_sp0 RT Σ - STACK_WIN) in *.
  cbn [xchunk app] in LV.
  assert (XIN : In (A8, 8) (rt_live RT Σ)) by (rewrite LV; left; reflexivity).
  assert (EU : bv_unsigned (Z_to_bv 64 (usp - 160)) = usp - 160) by (apply unsigned_lit; ul).
  assert (B16' : (usp - 80) mod 16 = 0) by (apply Z.mod_divide; [lia|]; apply Z.mod_divide in B16; [| lia]; destruct B16 as (q & ->); exists (q - 5); lia).

  assert (TAIL : forall (Σ' : rts RT) (m' : mem) (v : word) (t0' t1' t2' b1 b2 b3 b4 b5 b6 b7 t3' t4' t5' t6' : word) F' fc' cf,
            ASTA RT Σ' (PMfd fds0 fs)
              (eq (MS (mkR (Z_to_bv 64 0xb4960) (Z_to_bv 64 (usp - 160)) gp (Z_to_bv 64 TP_A) t0' t1' t2' (Z_to_bv 64 plen)
                           (Z_to_bv 64 d) v b1 b2 b3 b4 b5 b6 b7 (Z_to_bv 64 owned) s3 (Z_to_bv 64 TR_LATCH) (Z_to_bv 64 0) (Z_to_bv 64 0)
                           s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc (Z_to_bv 64 0xb4960)) fc' None m'
                      (seg_rom bsegs))) cf ->
            ART RT Σ' m' -> mem_inv bsegs m' -> stk bsegs m' lo (usp - 160) ->
            rt_sp0 RT Σ' = rt_sp0 RT Σ -> rt_live RT Σ' = [(A8, 8); (buf, cap)] -> rt_frames RT Σ' = [] ->
            CLXv (Some A8) so m' -> agree_on (fun x => usp - 160 <= x < USTACK_TOP) m m' -> agree_on auxc m m' ->
            realizes bsegs cf T).
  { intros Σ' m' v t0' t1' t2' b1 b2 b3 b4 b5 b6 b7 t3' t4' t5' t6' F' fc' cf Hc ART1 MI1 ST1 SP1 LV1 FRS1 CLX1 AG1 AGC1.
    rewrite (ret_pc_even 0xb4960) in Hc by lia.
    assert (TF1 : tr_frame m' (usp - 80) (Z_to_bv 64 0xb470c) x0 x1 x2 x3 x4 x5 x6 x7).
    { apply (tr_frame_agree_nw m m' _ _ _ _ _ _ _ _ _ _ TF0); eapply agree_sub; [exact AG1|]; intros x Hx; cbv beta in *; ul. }
    pose proof (tr_free_ret_walk (usp - 80) gp t0' t1' t2' (Z_to_bv 64 plen) (Z_to_bv 64 d) v b1 b2 b3 b4 b5 b6 b7 (Z_to_bv 64 owned)
                  s3 (Z_to_bv 64 TR_LATCH) (Z_to_bv 64 0) s7 s8 s9 s10 s11 t3' t4' t5' t6' x0 x1 x2 x3 x4 x5 x6 x7 F' fc' m' lo
                  ltac:(replace (usp - 80 - 80) with (usp - 160) by lia; exact ST1) ltac:(ul) ltac:(ul) B16' ltac:(ul) TF1 MI1) as W1.
    replace (usp - 80 - 80) with (usp - 160) in W1 by lia.
    lazymatch type of W1 with evt bsegs _ ?X =>
      assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
    clear W1.
    apply (cps_realizes bsegs _ _ _ _ (asta_evt RT AF Σ' _ fs _ _ W1') Hc).
    intros cf2 Hc2. apply Hk.
    destruct (ASTA_unpack RT Σ' _ _ cf2 Hc2) as (ms2 & (-> & ST2) & Hc2').
    exists Σ', gp, t0', t1', t2', b1, b2, b3, b4, b5, b6, b7, x6, x7, s8, s9, s10, s11, t3', t4', t5', t6'.
    exists c0, c1, c2, c3, c4, c5, c6, c7, F', fc', m'.
    split; [exact Hc2'|]. split; [exact ART1|]. split; [exact MI1|]. split; [exact CLX1|].
    split; [apply (main_frame_agree_nw m m' usp _ _ _ _ _ _ _ _ FR0); [eapply agree_sub; [exact AG1|]; intros x Hx; cbv beta in *; ul| exact AGC1]|].
    rewrite SP1. split; [exact ST2|]. split; [exact B16|]. split; [exact ULO|]. split; [exact USP0|]. split; [exact SPW|].
    split; [exact LV1|]. split; [exact FRS1|]. split; [exact CAP0| exact UT0]. }
  destruct (Z.eq_dec plen 0) as [Z0|NZ].
  -
    destruct (P0 Z0) as [-> ->].
    apply (FRN Σ (PMfd fds0 fs) (Z_to_bv 64 0xb4960) (Z_to_bv 64 (usp - 160)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 plen)
             (Z_to_bv 64 TR_EMPTY) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) s3 (Z_to_bv 64 TR_LATCH) (Z_to_bv 64 0) (Z_to_bv 64 0)
             s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo); try reflexivity; try assumption.
    + apply PMfd_fdfs_only.
    + apply PMfd_mat_stable.
    + unfold call_ok. rewrite EU. split; [exact ST0|]. ul.
    + unfold unwind_ok. rewrite EU, !unsigned_lit by ul. left. ul.
    + intros cf1 (v & Hc1).
      destruct (ASTA_unpack RT Σ _ _ cf1 Hc1) as (ms1 & (m1 & RS1 & (ART1 & MI1 & WM1 & ST1) & PRES1 & _) & Hc1').
      destruct RS1 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & ->). pose (fc1 := fc).
      rewrite EU in ST1, PRES1.
      apply (TAIL Σ m1 v u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F1 fc1 cf1 Hc1' ART1 MI1 ST1 eq_refl); try assumption.
      * rewrite LV. unfold tr_live. rewrite (proj2 (Z.eqb_eq plen 0) Z0). reflexivity.
      * apply (CLXv_pres_nw OUT_rep ERR_rep IO_FP OUT_loc ERR_loc IO_img XENV_img (Some A8) _ m m1 (rt_live RT Σ) (rt_frames RT Σ) (usp - 160) CLX0);
          [intros a Ha; apply PRES1; [exact Ha| lia]| intros B EB; injection EB as <-; exact XIN].
      * apply (agree_stack_pres_ex _ _ _ _ _ _ _ PRES1). ul.
      * apply (auxc_of_pres_ex _ _ _ _ _ _ _ PRES1). unfold EL_AUXV_CELL. lia.
  -
    pose proof (P1 ltac:(lia)) as ->.
    assert (INO : In (owned, plen) (rt_live RT Σ)) by (rewrite LV; right; unfold tr_live; rewrite (proj2 (Z.eqb_neq plen 0) NZ); left; reflexivity).
    assert (DISJ : owned + plen <= buf \/ buf + cap <= owned).
    { apply (af_live_disj RT AF Σ m owned plen buf cap [(A8, 8)] [(buf, cap)] ART0); [rewrite LV; unfold tr_live; rewrite (proj2 (Z.eqb_neq plen 0) NZ); reflexivity| right; left; reflexivity]. }
    assert (DISJA : owned + plen <= A8 \/ A8 + 8 <= owned).
    { apply (af_live_disj RT AF Σ m owned plen A8 8 [(A8, 8)] [(buf, cap)] ART0); [rewrite LV; unfold tr_live; rewrite (proj2 (Z.eqb_neq plen 0) NZ); reflexivity| left; reflexivity]. }
    apply (FRE Σ (PMfd fds0 fs) (Z_to_bv 64 0xb4960) (Z_to_bv 64 (usp - 160)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 plen)
             (Z_to_bv 64 owned) (Z_to_bv 64 owned) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 owned) s3 (Z_to_bv 64 TR_LATCH) (Z_to_bv 64 0) (Z_to_bv 64 0)
             s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m owned plen lo); try reflexivity; try assumption.
    + apply PMfd_fdfs_only.
    + apply PMfd_mat_stable.
    + unfold call_ok. rewrite EU. split; [exact ST0|]. ul.
    + unfold unwind_ok. rewrite EU, !unsigned_lit by ul. left. ul.
    + intros cf1 (Σ1 & v & Hc1 & LV1 & FRS1 & SP1 & CR1).
      destruct (ASTA_unpack RT Σ1 _ _ cf1 Hc1) as (ms1 & (m1 & RS1 & (ART1 & MI1 & ST1) & PRES1) & Hc1').
      destruct RS1 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & ->). pose (fc1 := fc).
      rewrite EU in ST1, PRES1.
      rewrite LV in LV1. unfold tr_live in LV1. rewrite (proj2 (Z.eqb_neq plen 0) NZ) in LV1. cbn [app] in LV1.
      rewrite live_remove_head3 in LV1 by lia.
      apply (TAIL Σ1 m1 v u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F1 fc1 cf1 Hc1' ART1 MI1); try assumption.
      * rewrite FRS1. exact FRS.
      * apply (CLXv_pres_nw OUT_rep ERR_rep IO_FP OUT_loc ERR_loc IO_img XENV_img (Some A8) _ m m1 _ _ _ CLX0 PRES1).
        intros B EB. injection EB as <-. rewrite LV1. left. reflexivity.
      * exact (agree_stack_pres _ _ _ _ _ PRES1).
      * exact (auxc_of_pres _ _ _ _ _ PRES1).
Qed.

Theorem target_run_cpsE : forall (Σ : rts RT) (usp buf cap cp L pp plen : Z) (c0b : byte) (payload : list byte)
    (gp t0 t1 t2 a4 a5 a6 a7 x0 x1 x2 x3 x4 x5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (c0 c1 c2 c3 c4 c5 c6 c7 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  frm0 fc -> TPRE RT OUT_rep ERR_rep Σ usp buf cap cp L pp plen c0b payload c0 c1 c2 c3 c4 c5 c6 c7 m ->
  cpsE bsegs (ASTA RT Σ (PMfd fds0 fs)
               (eq (entry_st (Z_to_bv 64 0xb470c) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 x0 x1
                     (Z_to_bv 64 cp) (Z_to_bv 64 L) (Z_to_bv 64 pp) (Z_to_bv 64 plen) a4 a5 a6 a7 x2 x3 x4 x5 s6 s7 s8 s9 s10 s11
                     t3 t4 t5 t6 F fc e_target_run m)))
    (evw 1 [48; 10])
    (fun c => exists A8, TRET RT OUT_rep ERR_rep fs A8 (so_lines (Z.to_nat (tr_calls L c0b) - 1)) usp buf cap x0 x1 x2 x3 x4 x5 c).
Proof using AF AF_DRV MAL FRE FRN MCP FUZZ VPR OUT_loc ERR_loc IO_img IO_img2 XENV_img.
  intros Σ usp buf cap cp L pp plen c0b payload gp t0 t1 t2 a4 a5 a6 a7 x0 x1 x2 x3 x4 x5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    c0 c1 c2 c3 c4 c5 c6 c7 F fc m FRM HP.
  pose proof (tr_calls_range L c0b) as TCR.
  eapply cps_cpsE; [exact (tr_start RT OUT_rep ERR_rep IO_FP fs AF AF_DRV MAL MCP OUT_loc ERR_loc IO_img XENV_img Σ usp buf cap cp L pp plen c0b payload gp t0 t1 t2 a4 a5 a6 a7 x0 x1 x2 x3 x4 x5
                              s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c6 c7 F fc m FRM HP)|].
  change (evw 1 [48; 10]) with (evw 1 (emit0_out stdout_init) ++ []).
  eapply cpsE_seq; [apply (tr_iter RT OUT_rep ERR_rep IO_FP fs AF AF_DRV FUZZ VPR OUT_loc ERR_loc IO_img IO_img2 XENV_img); left; reflexivity|].
  change (emit0_next stdout_init) with (so_lines 0).
  intros T c (A8 & _ & [(K1 & HL)|(K1 & HF)]) Hk.
  - eapply (tr_later (Z.to_nat (tr_calls L c0b - 1)) (tr_calls L c0b - 1) 0 A8 usp buf cap x0 x1 x2 x3 x4 x5 s6 s7 eq_refl ltac:(lia) ltac:(lia)
              T c HL).
    intros c' Hc'.
    replace (0 + Z.to_nat (tr_calls L c0b - 1))%nat with (Z.to_nat (tr_calls L c0b) - 1)%nat in Hc' by lia.
    exact (tr_end A8 _ usp buf cap x0 x1 x2 x3 x4 x5 s6 s7 T c' Hc' (fun c2 H2 => Hk c2 (ex_intro _ A8 H2))).
  - rewrite K1 in Hk. change (Z.to_nat 1 - 1)%nat with 0%nat in Hk.
    exact (cpsE_nil bsegs _ _ (tr_end A8 (so_lines 0) usp buf cap x0 x1 x2 x3 x4 x5 s6 s7) T c HF (fun c2 H2 => Hk c2 (ex_intro _ A8 H2))).
Qed.

End Tr3.
