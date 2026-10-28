(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac ImageA Nodes RzCPS NodesA.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import Prelim Canon Stdio Prog.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface D_iface D_defs D_kit D_libiface D_clx D_libkit D_rlkit D_trpro D_trwalk D_trdefs D_tr1 RT_client_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Section Tr2.
Variable RT : rt_sig.
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Variable XENV : mem -> Prop.             (* [comment removed for export] *)
Variable XENV_FP : list (Z * Z).
Variable LIBA : rts RT -> list (Z * Z) -> mem -> Prop.
Variable fs : Fs.
Hypothesis AF : art_facts RT.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis FUZZ : fuzz_one_cps' RT LIBA.
Hypothesis LFR : liba_frame RT LIBA.
Hypothesis LEX : liba_exit RT LIBA.
Hypothesis VPR : vprintf_emit0_icontract RT OUT_rep ERR_rep IO_FP.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis XENV_loc : fp_local XENV_FP XENV.
Hypothesis IO_img : forall x, in_ranges IO_FP x -> client_static x /\ ~ drv_cell x /\ outside LIB_FP x.
Hypothesis XENV_img : forall x, in_ranges XENV_FP x -> client_static x /\ ~ drv_cell x /\ outside IO_FP x /\ outside LIB_FP x.
Hypothesis INCB_off : forall x, TR_INIT + 1 <= x < TR_INIT + 5 -> outside IO_FP x /\ outside XENV_FP x.
#[local] Notation LIB := lib_exit_cells.
#[local] Notation LIB_loc := lib_exit_loc.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, FUZZ_STACK, FUZZ_LIVE, LIVE_MAX, g_read_stage in *; lia.

Lemma outside_image_ranges : forall (W : list (Z * Z)), (forall x, in_ranges W x -> client_static x) ->
  forall x, SEGTOP_A <= x -> outside W x.
Proof.
  intros W HW x Hx. apply outside_of_not_in_ranges'. intros Hin. pose proof (client_static_range x (HW x Hin)). lia.
Qed.

Lemma IO_outside_hi : forall x, SEGTOP_A <= x -> outside IO_FP x.
Proof using IO_img. apply outside_image_ranges. intros x Hx. exact (proj1 (IO_img x Hx)). Qed.

(* [comment removed for export] *)
Lemma chunk_outside : forall (W : list (Z * Z)) Σ m p n x, (forall y, in_ranges W y -> client_static y) ->
  ART RT Σ m -> In (p, n) (rt_live RT Σ) -> p <= x < p + n -> outside W x.
Proof using AF.
  intros W Σ m p n x HW HA Hin Hx. pose proof (af_live_range RT AF Σ m p n HA Hin) as (R1 & R2 & R3).
  apply outside_of_not_in_ranges'. intros Hi. pose proof (client_static_range x (HW x Hi)). unfold SEGTOP_A in *. lia.
Qed.

Lemma LIB_FPE_static : forall y, in_ranges LIB_FPE y -> client_static y.
Proof.
  intros y (lo & hi & Hin & Hy). unfold LIB_FPE in Hin. destruct Hin as [E|Hin].
  - injection E as <- <-. apply client_static_intro. lia.
  - exact (proj1 (LIB_img y (ex_intro _ lo (ex_intro _ hi (conj Hin Hy))))).
Qed.

Theorem tr_iter : forall k so usp buf cap x0 x1 x2 x3 x4 x5 x6 x7, (so = stdout_init \/ exists j, (j < 499)%nat /\ so = so_lines j) ->
  cpsE bsegs (TLOOP RT OUT_rep ERR_rep XENV LIBA fs k so usp buf cap x0 x1 x2 x3 x4 x5 x6 x7) (evw 1 (emit0_out so))
    (fun c => (1 < k /\ TLOOP RT OUT_rep ERR_rep XENV LIBA fs (k - 1) (emit0_next so) usp buf cap x0 x1 x2 x3 x4 x5 x6 x7 c)
              \/ (k = 1 /\ TFREE RT OUT_rep ERR_rep XENV LIBA fs (emit0_next so) usp buf cap x0 x1 x2 x3 x4 x5 x6 x7 c)).
Proof using AF AF_DRV FUZZ LFR LEX VPR OUT_loc ERR_loc XENV_loc IO_img XENV_img INCB_off.
  intros k so usp buf cap x0 x1 x2 x3 x4 x5 x6 x7 Hso T c HL Hk.
  destruct HL as (Σ & LW & plen & d & owned & payload & gp & t0 & t1 & t2 & a2 & a3 & a4 & a5 & a6 & a7 & s3
                  & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7
                  & F & fc & m & HA & HT & Hk14 & HCR & HLN).
  pose proof HT as (ART0 & MI0 & CLX0 & FR0 & TF0 & ST0 & B16 & ULO & USP0 & SPW & LV & FRS & PL & PB & BD & P0 & P1 & CAP0 & UT0 & LB0 & IC0).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  set (lo := rt_sp0 RT Σ - STACK_WIN) in *.
  set (CL := tr_live plen owned buf cap) in *.
  assert (EU : bv_unsigned (Z_to_bv 64 (usp - 160)) = usp - 160) by (apply unsigned_lit; ul).
  assert (B16'' : (usp - 160) mod 16 = 0) by (apply Z.mod_divide; [lia|]; apply Z.mod_divide in B16; [| lia]; destruct B16 as (q & ->); exists (q - 10); lia).
  assert (INO : plen <> 0 -> In (owned, plen) CL) by (intros NZ; unfold CL, tr_live; rewrite (proj2 (Z.eqb_neq plen 0) NZ); left; reflexivity).
  assert (ICS : forall x, TR_INIT + 1 <= x < TR_INIT + 5 -> client_static x) by (intros x Hx; apply client_static_intro; unfold TR_INIT in Hx; lia).
  assert (ICL : forall x, TR_INIT + 1 <= x < TR_INIT + 5 -> outside LIB_FPE x)
    by (intros x Hx; unfold LIB_FPE, LIB_FP; cbn [outside]; unfold TR_INIT in Hx; repeat split; try exact I; lia).
  assert (DPOS : (0 < d < 2^64 /\ d <= lo) /\ ((exists p n, In (p, n) CL /\ p <= d /\ d + Z.of_nat (length payload) <= p + n) \/ payload = [])).
  { destruct (Z.eq_dec plen 0) as [Z0|NZ].
    - destruct (P0 Z0) as [-> _]. split; [unfold TR_EMPTY; split; [split; [lia| reflexivity]| ul]|]. right. destruct payload; [reflexivity| cbn in PL; lia].
    - rewrite (P1 ltac:(lia)).
      pose proof (af_live_range RT AF Σ m owned plen ART0 (tr_live_in RT Σ LW _ _ _ _ _ LV (INO NZ))) as (R1 & R2 & _).
      split; [split; [split; [lia| change (2^64) with 18446744073709551616; ul]| unfold lo; lia]|]. left. exists owned, plen. split; [exact (INO NZ)| lia]. }
  apply (FUZZ Σ (PMfd fds0 fs) (Z_to_bv 64 0x1ee254) (Z_to_bv 64 (usp - 160)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 plen)
           (Z_to_bv 64 d) (Z_to_bv 64 d) (Z_to_bv 64 plen) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 owned) s3 (Z_to_bv 64 TR_INIT)
           (Z_to_bv 64 k) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) s8 s9 s10 s11 t3 t4 t5 t6 F fc m d payload lo LW CL); try reflexivity; try assumption.
  - apply PMfd_fdfs_only.
  - apply PMfd_mat_stable.
  - rewrite <- PL. reflexivity.
  - exact (proj1 (proj1 DPOS)).
  - exact (proj2 (proj1 DPOS)).
  - lia.
  - exact (proj2 DPOS).
  - intros p n Hin. unfold CL, tr_live in Hin. destruct (Z.eqb_spec plen 0) as [E|E]; cbn [app In] in Hin.
    + destruct Hin as [Hin|[]]. injection Hin as <- <-. exact CAP0.
    + destruct Hin as [Hin|[Hin|[]]]; injection Hin as <- <-; [lia| exact CAP0].
  - ul.
  - unfold FUZZ_COST in *. nia.
  - left. rewrite unsigned_lit by lia. ul.
  - rewrite EU. exact ST0.
  - rewrite EU. ul.
  - rewrite EU. ul.
  - rewrite EU. exact B16''.
  - rewrite EU. lia.
  - intros cf1 (Σ1 & LW1 & Hc1 & LV1 & FRS1 & SP1 & CR1 & LN1).
    destruct (ASTA_unpack RT Σ1 _ _ cf1 Hc1) as (ms1 & (m1 & RS1 & (ART1 & MI1 & ST1) & PRES1 & LB1) & Hc1').
    destruct RS1 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & ->).
    rewrite EU in ST1, PRES1.
    rewrite (ret_pc_even 0x1ee254) in Hc1' by lia.
    assert (CLX1 : CLX OUT_rep ERR_rep XENV LIB so m1)
      by exact (CLX_libE OUT_rep ERR_rep IO_FP XENV XENV_FP LIB LIB OUT_loc ERR_loc XENV_loc IO_img XENV_img
                  _ m m1 _ _ _ CLX0 PRES1 (LEX Σ1 LW1 m1 LB1)).
    pose proof (agree_stack_pres_fp _ _ _ _ _ _ PRES1 ltac:(intros x Hx; apply LIB_FPE_outside_hi; ul)) as AG1.
    assert (AGD1 : agree_on (fun x => d <= x < d + plen) m m1).
    { destruct (Z.eq_dec plen 0) as [Z0|NZ]; [intros a Ha; lia|].
      rewrite (P1 ltac:(lia)) in *. apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES1). intros x Hx.
      split; [right; right; left; exists owned, plen; split; [exact (INO NZ)| lia]|].
      exact (chunk_outside LIB_FPE Σ m owned plen x LIB_FPE_static ART0 (tr_live_in RT Σ LW _ _ _ _ _ LV (INO NZ)) Hx). }
    assert (IC1 : incb 1 m1).
    { apply (incb_agree 1 m m1 IC0). apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES1). intros x Hx.
      split; [right; left; exact (ICS x Hx)| exact (ICL x Hx)]. }
    assert (HT1 : TCTX RT OUT_rep ERR_rep XENV LIBA Σ1 LW1 so 1 usp buf cap plen d owned payload c0 c1 c2 c3 c4 c5 c6 c7 x0 x1 x2 x3 x4 x5 x6 x7 m1)
      by exact (TCTX_agree_nw RT OUT_rep ERR_rep XENV LIBA AF Σ Σ1 LW LW1 so so 1 usp buf cap plen d owned payload c0 c1 c2 c3 c4 c5 c6 c7
                  x0 x1 x2 x3 x4 x5 x6 x7 m m1 HT ART1 MI1 ST1 SP1 LV1 FRS1 CLX1 AG1 AGD1 LB1 IC1).
    (* [comment removed for export] *)
    destruct (incb_cells 1 m1 IC1) as (l1 & p1 & TC1).
    pose proof (tr_fuzz_ret_walk (usp - 160) l1 (Z_to_bv 8 1) p1 gp t0' t1' t2' (Z_to_bv 64 plen) (Z_to_bv 64 d) a1' a2' a3' a4' a5' a6' a7'
                  (Z_to_bv 64 owned) s3 (Z_to_bv 64 k) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) s8 s9 s10 s11 t3' t4' t5' t6' F' fc' m1 lo ST1
                  ltac:(ul) ltac:(ul) B16'' ltac:(ul) TC1 MI1) as W1.
    lazymatch type of W1 with evt bsegs _ ?X =>
      assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
    clear W1.
    apply (cps_realizes bsegs _ _ _ _ (asta_evt RT AF Σ1 _ fs _ _ W1') Hc1').
    intros cf2 Hc2.
    destruct (ASTA_unpack RT Σ1 _ _ cf2 Hc2) as (ms2 & (m2 & junk & -> & MU2 & WM2 & MI2 & EF1 & EF2 & EF3 & ST2 & TC2) & Hc2').
    assert (OFF2 : forall x, ~ (usp - 160 - 80 <= x < usp - 160) -> ~ (TR_INIT + 1 <= x < TR_INIT + 5) ->
              outside [(usp - 160 - 80, usp - 160); (AEF_INCB, AEF_INCB + 1)] x)
      by (intros x H1 H2; unfold AEF_INCB, TR_INIT in *; cbn [outside]; split; [lia| split; [lia| exact I]]).
    assert (CLX2 : CLX OUT_rep ERR_rep XENV LIB so m2).
    { apply (CLX_incb_munch OUT_rep ERR_rep IO_FP XENV XENV_FP OUT_loc ERR_loc XENV_loc IO_img XENV_img INCB_off
               _ LIB m1 m2 _ LIB_loc CLX1 MU2 WM2). intros x Hx Hn. apply OFF2; [ul| exact Hn]. }
    pose proof CLX2 as (OUT2 & ERR2 & _).
    assert (ART2 : ART RT Σ1 m2).
    { apply (af_frame RT AF Σ1 m1 m2 (usp - 160 - 80) ART1); [rewrite SP1; ul| |exact WM2].
      intros a Ha. apply MU2. apply OFF2; [intros Hin; apply Ha; left; ul| intros Hr; apply Ha; right; left; exact (ICS _ Hr)]. }
    assert (IC2 : incb 0 m2) by (exists p1; exact (tr_cells_split m2 l1 p1 _ TC2)).
    assert (EU2 : bv_unsigned (Z_to_bv 64 (usp - 160 - 80)) = usp - 160 - 80) by (apply unsigned_lit; ul).
    apply (VPR Σ1 fds0 fs (Z_to_bv 64 0x1ee34c) (Z_to_bv 64 (usp - 160 - 80)) gp (Z_to_bv 64 TP_A) t0' t1' t2' (Z_to_bv 64 plen)
             (Z_to_bv 64 d) (Z_to_bv 64 FMT_emit) (Z_to_bv 64 (usp - 160 - 80 + 24)) a2' a3' a4' a5' a6' a7' (Z_to_bv 64 owned)
             (Z_to_bv 64 0) (Z_to_bv 64 TR_INIT) (Z_to_bv 64 k) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) s8 s9 s10 s11 t3' t4' t5' t6' F' fc' m2 so
             (usp - 160 - 80 + 24) lo); try reflexivity; try assumption.
    + rewrite EU2. reflexivity.
    + destruct Hso as [->|(j & Hj & ->)]; [left; reflexivity| right; exists j; split; [lia| reflexivity]].
    + io_ssp_tac AF_DRV.
    + unfold call_ok. rewrite EU2, SP1. split; [exact ST2|]. ul.
    + intros cf3 Hc3.
      destruct (ASTA_unpack RT Σ1 _ _ cf3 Hc3) as (ms3 & (v & m3 & RS3 & (ART3 & MI3 & WM3 & ST3) & PRES3 & OUT3 & ERRP3) & Hc3').
      destruct RS3 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F3 & fc3 & ->).
      rewrite EU2 in ST3, PRES3.
      rewrite (ret_pc_even 0x1ee34c) in Hc3' by lia.
      assert (CLX3 : CLX OUT_rep ERR_rep XENV LIB (emit0_next so) m3)
        by exact (CLX_io OUT_rep ERR_rep IO_FP XENV XENV_FP LIB OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img
                    _ _ m2 m3 _ _ _ CLX2 PRES3 WM3 OUT3 (ERRP3 ERR2)).
      pose proof (agree_stack_pres_fp _ _ _ _ _ _ PRES3 ltac:(intros x Hx; apply IO_outside_hi; ul)) as AG3.
      assert (IC3 : incb 0 m3).
      { apply (incb_agree 0 m2 m3 IC2). apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES3). intros x Hx.
        split; [right; left; exact (ICS x Hx)| exact (proj1 (INCB_off x Hx))]. }
      assert (EF1' : rw_cells bsegs m3 (usp - 160 - 80) [C8 (Z_to_bv 64 (usp - 160 - 80 + 24)); C8 (Z_to_bv 64 0x1ee264); CB 8 junk]).
      { apply (rw_cells_agree bsegs m2 m3 _ _ EF1); [| exact WM3]. eapply agree_sub; [exact AG3|]. intros x Hx.
        cbn [cells_size csize Nat.add] in Hx. cbv beta. ul. }
      assert (EF2' : rw_cells bsegs m3 (usp - 160 - 80 + 24) [C8 (Z_to_bv 64 0)]).
      { apply (rw_cells_agree bsegs m2 m3 _ _ EF2); [| exact WM3]. eapply agree_sub; [exact AG3|]. intros x Hx.
        cbn [cells_size csize Nat.add] in Hx. cbv beta. ul. }
      assert (EF3' : rw_cells bsegs m3 (usp - 160 - 80 + 32) [C8 a2'; C8 a3'; C8 a4'; C8 a5'; C8 a6'; C8 a7']).
      { apply (rw_cells_agree bsegs m2 m3 _ _ EF3); [| exact WM3]. eapply agree_sub; [exact AG3|]. intros x Hx.
        cbn [cells_size csize Nat.add] in Hx. cbv beta. ul. }
      (* [comment removed for export] *)
      destruct (incb_cells 0 m3 IC3) as (l3 & p3 & TC3).
      pose proof (tr_emit_ret_walk (usp - 160) k l3 (Z_to_bv 8 0) p3 gp u0 u1 u2 (Z_to_bv 64 plen) (Z_to_bv 64 d) v b1 b2 b3 b4 b5 b6 b7
                    (Z_to_bv 64 owned) (Z_to_bv 64 0) s8 s9 s10 s11 u3 u4 u5 u6 a2' a3' a4' a5' a6' a7'
                    F3 fc3 m3 lo junk ST3 ltac:(ul) ltac:(ul) B16'' ltac:(ul) ltac:(lia) EF1' EF2' EF3' TC3 MI3) as W3.
      lazymatch type of W3 with evt bsegs _ ?X =>
        assert (W3' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W3) end.
      clear W3.
      apply (cps_realizes bsegs _ _ _ _ (asta_evt RT AF Σ1 _ fs _ _ W3') Hc3').
      intros cf4 Hc4. apply Hk.
      destruct (ASTA_unpack RT Σ1 _ _ cf4 Hc4) as (ms4 & (m4 & Hcase & MU4 & WM4 & MI4 & ST4) & Hc4').
      pose proof HT1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LV1' & _).
      assert (OFF4 : forall x, ~ (TR_INIT + 1 <= x < TR_INIT + 5) -> outside [(AEF_INCB, AEF_INCB + 1)] x)
        by (intros x Hx; unfold AEF_INCB, TR_INIT in *; cbn [outside]; split; [lia| exact I]).
      assert (AG34 : agree_on (fun x => ~ (TR_INIT + 1 <= x < TR_INIT + 5)) m3 m4).
      { apply (agree_of_munch _ _ _ _ MU4). intros x Hx. exact (OFF4 x Hx). }
      assert (ART4 : ART RT Σ1 m4).
      { apply (af_frame RT AF Σ1 m3 m4 (usp - 160) ART3); [rewrite SP1; ul| |exact WM4].
        intros a Ha. apply MU4. apply OFF4. intros Hr. apply Ha. right; left. exact (ICS _ Hr). }
      assert (CLX4 : CLX OUT_rep ERR_rep XENV LIB (emit0_next so) m4)
        by exact (CLX_incb_munch OUT_rep ERR_rep IO_FP XENV XENV_FP OUT_loc ERR_loc XENV_loc IO_img XENV_img INCB_off
                    _ LIB m3 m4 _ LIB_loc CLX3 MU4 WM4 ltac:(intros x _ Hx; exact (OFF4 x Hx))).
      assert (AG14 : agree_on (fun x => usp - 160 <= x < USTACK_TOP) m1 m4).
      { apply (agree_trans _ m1 m2 m4).
        - apply (agree_of_munch _ _ _ _ MU2). intros x Hx. apply OFF2; [lia| unfold TR_INIT; ul].
        - apply (agree_trans _ m2 m3 m4); [eapply agree_sub; [exact AG3|]; intros x Hx; cbv beta in *; lia|].
          eapply agree_sub; [exact AG34|]. intros x Hx. cbv beta in *. unfold TR_INIT. ul. }
      (* [comment removed for export] *)
      assert (AGC14 : forall p n, In (p, n) (rt_live RT Σ1) -> agree_on (fun x => p <= x < p + n) m1 m4).
      { intros p n Hin. pose proof (af_live_range RT AF Σ1 m1 p n ART1 Hin) as (R1 & R2 & R3). apply (agree_trans _ m1 m2 m4).
        - apply (agree_of_munch _ _ _ _ MU2). intros x Hx. apply OFF2; [rewrite SP1 in R2; ul| unfold TR_INIT; unfold SEGTOP_A in *; lia].
        - apply (agree_trans _ m2 m3 m4).
          + apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES3). intros x Hx.
            split; [right; right; left; exists p, n; split; [exact Hin| lia]|].
            exact (chunk_outside IO_FP Σ1 m1 p n x (fun y Hy => proj1 (IO_img y Hy)) ART1 Hin Hx).
          + eapply agree_sub; [exact AG34|]. intros x Hx. cbv beta in *. unfold TR_INIT. unfold SEGTOP_A in *. lia. }
      assert (AGD14 : agree_on (fun x => d <= x < d + plen) m1 m4).
      { destruct (Z.eq_dec plen 0) as [Z0|NZ]; [intros a Ha; lia|].
        rewrite (P1 ltac:(lia)) in *. exact (AGC14 owned plen (tr_live_in RT Σ1 LW1 _ _ _ _ _ LV1' (INO NZ))). }
      assert (LB4 : LIBA Σ1 LW1 m4).
      { apply (LFR Σ1 Σ1 LW1 m1 m4 LB1). intros a [Ha|(p & n & Hin & Hx)].
        - pose proof (LIB_FP_range _ Ha) as R.
          assert (NR : ~ (TR_INIT + 1 <= bv_unsigned a < TR_INIT + 5)) by (intros Hr; exact (not_in_ranges_of_outside LIB_FP _ (proj2 (ICL _ Hr)) Ha)).
          rewrite (AG34 a NR). rewrite (PRES3 a).
          + apply MU2. apply OFF2; [ul| exact NR].
          + right; left. exact (proj1 (LIB_img _ Ha)).
          + apply outside_of_not_in_ranges'. intros Hin. exact (not_in_ranges_of_outside _ _ (proj2 (proj2 (IO_img _ Hin))) Ha).
        - exact (AGC14 p n (tr_live_in_lw RT Σ1 LW1 _ _ _ _ _ LV1' Hin) a Hx). }
      assert (HT4 : forall icb, incb icb m4 -> TCTX RT OUT_rep ERR_rep XENV LIBA Σ1 LW1 (emit0_next so) icb usp buf cap plen d owned payload
                      c0 c1 c2 c3 c4 c5 c6 c7 x0 x1 x2 x3 x4 x5 x6 x7 m4).
      { intros icb IC4.
        destruct HT1 as (_ & _ & _ & FR1 & TF1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & BD1 & _).
        split; [exact ART4|]. split; [exact MI4|]. split; [exact CLX4|].
        split; [apply (main_frame_agree_nw m1 m4 usp _ _ _ _ _ _ _ _ FR1); eapply agree_sub; [exact AG14|]; intros x Hx; cbv beta in *; ul|].
        split; [apply (tr_frame_agree_nw m1 m4 _ _ _ _ _ _ _ _ _ _ TF1); eapply agree_sub; [exact AG14|]; intros x Hx; cbv beta in *; lia|].
        rewrite SP1. split; [exact ST4|].
        split; [exact B16|]. split; [exact ULO|]. split; [exact USP0|]. split; [exact SPW|]. split; [exact LV1'|]. split; [exact FRS1|].
        split; [exact PL|]. split; [exact PB|].
        split; [apply (bytes_at_agree bsegs m1 m4 _ _ BD1); rewrite <- PL; exact AGD14|].
        split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [exact LB4| exact IC4]. }
      destruct Hcase as [(K1 & -> & TC4)|(K1 & -> & TC4)].
      * left. split; [exact K1|].
        exists Σ1, LW1, plen, d, owned, payload, gp, u0, u1, u2, b2, b3, b4, b5, b6, b7, (Z_to_bv 64 (-1)), s8, s9, s10, s11.
        exists u3, u4, u5, u6, c0, c1, c2, c3, c4, c5, c6, c7, F3, fc3, m4.
        split; [exact Hc4'|]. split; [apply (HT4 1); exists p3; exact (tr_cells_split m4 l3 p3 _ TC4)|]. split; [lia|].
        split; [unfold FUZZ_COST in *; nia| ul].
      * right. split; [exact K1|].
        exists Σ1, LW1, plen, d, owned, payload, gp, u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, s8, s9, s10, s11.
        exists u3, u4, u5, u6, c0, c1, c2, c3, c4, c5, c6, c7, F3, fc3, m4.
        split; [exact Hc4'|]. split; [apply (HT4 0); exists p3; exact (tr_cells_split m4 l3 p3 _ TC4)| ul].
Qed.

End Tr2.
