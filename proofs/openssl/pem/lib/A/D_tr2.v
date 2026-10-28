(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA Nodes RzCPS NodesA.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim Canon Stdio Prog.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_iface D_defs D_kit D_agree D_libiface D_clx D_rlkit D_libiface_pem X_ax D_trpro D_trwalk D_trdefs D_tr1.
From Stdlib Require Import Permutation.
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
Variable XENV : mem -> Prop.
Variable XENV_FP : list (Z * Z).
Variable CG : cgraph.
(* [comment removed for export] *)
Variable LIBP : list (Z * Z) -> mem -> Prop.
Variables FZ_SITES FZ_CALLS : list (Z * Z).
Variable fs : Fs.
Hypothesis AF : art_facts RT.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis FUZZC : fuzz_one_cps RT LIBP FZ_SITES FZ_CALLS.
Hypothesis VPR : vprintf_emit0_icontract RT OUT_rep ERR_rep IO_FP.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis XENV_loc : fp_local XENV_FP XENV.
Hypothesis IO_img : forall x, in_ranges IO_FP x -> client_static x /\ ~ drv_cell x /\ outside LIB_FP x.
Hypothesis XENV_img : forall x, in_ranges XENV_FP x -> client_static x /\ ~ drv_cell x /\ outside IO_FP x /\ outside LIB_FP x.
(* [comment removed for export] *)
Hypothesis XENV_ax : forall m, XENV m -> exists fin p1 p2, ax_chunks true fin p1 p2 m.
Hypothesis XENV_incb : forall m, XENV m -> rw_cells asegs m TR_INCB [C1 (Z_to_bv 8 0)].
Hypothesis XENV_upd : forall m m', XENV m ->
  agree_on (fun x => in_ranges XENV_FP x /\ ~ (0xbc3f40 <= x < 0xbc3f70) /\ ~ (0xbc4060 <= x < 0xbc4070) /\ x <> TR_INCB) m m' ->
  (exists fin p1 p2, ax_chunks true fin p1 p2 m') -> rw_cells asegs m' TR_INCB [C1 (Z_to_bv 8 0)] -> XENV m'.
Hypothesis XENV_fp_ax : forall x, (0xbc3f40 <= x < 0xbc3f70 \/ 0xbc4060 <= x < 0xbc4070 \/ x = TR_INCB) -> in_ranges XENV_FP x.
Hypothesis LOCP : lib_local_d LIBP.
Hypothesis CGH : cg_has CG FZ_SITES FZ_CALLS.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, FUZZ_STACK, LIVE_MAX, CLI_MAX, FUZZ_LIVE, g_read_stage in *; lia.

Lemma outside_image_ranges : forall (W : list (Z * Z)), (forall x, in_ranges W x -> client_static x) ->
  forall x, SEGTOP_A <= x -> outside W x.
Proof.
  intros W HW x Hx. apply outside_of_not_in_ranges'. intros Hin. pose proof (client_static_range x (HW x Hin)). lia.
Qed.
Lemma outside_image_ranges_lo : forall (W : list (Z * Z)), (forall x, in_ranges W x -> client_static x) ->
  forall x, x < 0x10000 -> outside W x.
Proof.
  intros W HW x Hx. apply outside_of_not_in_ranges'. intros Hin. pose proof (client_static_range x (HW x Hin)). lia.
Qed.

Lemma LIB_outside_hi : forall x, SEGTOP_A <= x -> outside LIB_FP x.
Proof. apply outside_image_ranges. intros x Hx. exact (proj1 (LIB_img x Hx)). Qed.

Lemma IO_outside_hi : forall x, SEGTOP_A <= x -> outside IO_FP x.
Proof using IO_img. apply outside_image_ranges. intros x Hx. exact (proj1 (IO_img x Hx)). Qed.
Lemma IO_outside_lo : forall x, x < 0x10000 -> outside IO_FP x.
Proof using IO_img. apply outside_image_ranges_lo. intros x Hx. exact (proj1 (IO_img x Hx)). Qed.

(* [comment removed for export] *)
Lemma LIBD_in_FP : forall x, in_ranges LIB_D x -> in_ranges LIB_FP x.
Proof.
  intros x (lo & hi & Hin & Hx). exists lo, hi. split; [| exact Hx]. unfold LIB_D in Hin. unfold LIB_FP. cbn [In] in *. tauto.
Qed.
Lemma LIBD_outside_IO : forall x, in_ranges LIB_D x -> outside IO_FP x.
Proof using IO_img.
  intros x Hx. apply outside_of_not_in_ranges'. intros Hin.
  exact (not_in_ranges_of_outside _ _ (proj2 (proj2 (IO_img x Hin))) (LIBD_in_FP x Hx)).
Qed.

(* [comment removed for export] *)
Lemma INCB_static : client_static TR_INCB.
Proof. apply client_static_intro. unfold TR_INCB. lia. Qed.
Lemma INCB_not_io : ~ in_ranges IO_FP TR_INCB.
Proof using XENV_img XENV_fp_ax.
  apply not_in_ranges_of_outside. exact (proj1 (proj2 (proj2 (XENV_img _ (XENV_fp_ax _ ltac:(right; right; reflexivity)))))).
Qed.
Lemma INCB_not_drv : ~ drv_cell TR_INCB.
Proof. unfold drv_cell, ERRNO_A, TP_A, SSP_GUARD, g_read_stage, TR_INIT, TR_INCB. lia. Qed.
Lemma INCB_outside_W : outside LIB_W TR_INCB.
Proof. unfold LIB_W, TR_INCB. cbn [outside]. repeat split; try exact I; lia. Qed.
Lemma AX_static : forall x, (0xbc3f40 <= x < 0xbc3f70 \/ 0xbc4060 <= x < 0xbc4070 \/ x = TR_INCB) -> client_static x /\ outside IO_FP x /\ outside LIB_FP x.
Proof using XENV_img XENV_fp_ax. intros x Hx. destruct (XENV_img x (XENV_fp_ax x Hx)) as (C & _ & O & L). split; [exact C| split; assumption]. Qed.

(* [comment removed for export] *)
Lemma CLX_T_bracket : forall so m m0 m1 m2 DRV sp,
  CLX OUT_rep ERR_rep XENV LIBT so m ->
  agree_on (fun x => client_static x /\ x <> TR_INCB) m m0 ->
  cli_pres DRV sp m0 m1 -> (exists v, rw_cells asegs m2 ERRNO_A [C4 v]) ->
  agree_on (fun x => client_static x /\ x <> TR_INCB) m1 m2 ->
  rw_cells asegs m2 TR_INCB [C1 (Z_to_bv 8 0)] ->
  CLX OUT_rep ERR_rep XENV LIBT so m2.
Proof using OUT_loc ERR_loc XENV_loc IO_img XENV_img XENV_ax XENV_upd XENV_fp_ax.
  intros so m m0 m1 m2 DRV sp (H1 & H2 & H3 & _ & (g & SG) & _ & RS & (l & LT)) A01 PR ER2 A23 IC2.
  assert (A12 : agree_on (fun x => client_static x /\ outside LIB_W x) m0 m1).
  { intros a [C O]. apply PR; [right; left; exact C| exact O]. }
  assert (A02 : agree_on (fun x => client_static x /\ outside LIB_W x /\ x <> TR_INCB) m m2).
  { apply (agree_trans _ m m0 m2); [eapply agree_sub; [exact A01|]; intros x Hx; tauto|].
    apply (agree_trans _ m0 m1 m2); [eapply agree_sub; [exact A12|]; intros x Hx; tauto|].
    eapply agree_sub; [exact A23|]; intros x Hx; tauto. }
  assert (AIO : agree_on (fun x => in_ranges IO_FP x) m m2).
  { eapply agree_sub; [exact A02|]. intros x Hx. destruct (IO_img x Hx) as (C & ND & L). split; [exact C|]. split.
    - apply outside_LIB_W; [exact L|]. intros Hn. apply ND. left. exact Hn.
    - intros ->. exact (INCB_not_io Hx). }
  split; [exact (OUT_loc so m m2 H1 AIO)|]. split; [exact (ERR_loc m m2 H2 AIO)|].
  split.
  { apply (XENV_upd m m2 H3).
    - eapply agree_sub; [exact A02|]. intros x (Hx & _ & _ & N3). destruct (XENV_img x Hx) as (C & ND & _ & L). split; [exact C|]. split; [| exact N3].
      apply outside_LIB_W; [exact L|]. intros Hn. apply ND. left. exact Hn.
    - destruct (XENV_ax m H3) as (fin & p1 & p2 & X1 & X2). exists fin, p1, p2.
      assert (AAX : agree_on (fun x => 0xbc3f40 <= x < 0xbc3f70 \/ 0xbc4060 <= x < 0xbc4070) m m2).
      { eapply agree_sub; [exact A02|]. intros x Hx. destruct (AX_static x ltac:(tauto)) as (C & _ & L). split; [exact C|]. split.
        - apply outside_LIB_W; [exact L|]. unfold ERRNO_A, TP_A. lia.
        - unfold TR_INCB. lia. }
      split.
      + apply (rw_cells_agree_nw asegs m m2 _ _ X1). eapply agree_sub; [exact AAX|]. intros x Hx. cbn [cells_size csize ax_cells Nat.add length] in Hx. cbv beta. lia.
      + apply (rw_cells_agree_nw asegs m m2 _ _ X2). eapply agree_sub; [exact AAX|]. intros x Hx. cbn [cells_size csize ax_acells Nat.add length] in Hx. cbv beta. lia.
    - exact IC2. }
  split; [exact I|].
  assert (AGD : forall lo n, (forall x, lo <= x < lo + n -> drv_cell x /\ ~ (ERRNO_A <= x < ERRNO_A + 4)) -> agree_on (fun x => lo <= x < lo + n) m m2).
  { intros lo n Hd. eapply agree_sub; [exact A02|]. intros x Hx. destruct (Hd x Hx) as [D NE].
    split; [exact (drv_cell_static x D)|]. split; [| intros ->; exact (INCB_not_drv D)].
    unfold LIB_W. unfold drv_cell, ERRNO_A, TP_A, SSP_GUARD, g_read_stage, TR_INIT in *. cbn [outside]. repeat split; try exact I; lia. }
  unfold drv_cell in AGD. unfold ERRNO_A, TP_A, SSP_GUARD, g_read_stage, TR_INIT in AGD.
  split; [exists g; apply (ro_cells_agree asegs m m2 _ _ SG); apply AGD; cbn; unfold SSP_GUARD; lia|].
  split; [exact ER2|].
  split; [apply (stk_agree_nw asegs m m2 _ _ RS); eapply agree_sub; [apply (AGD g_read_stage 65536); unfold g_read_stage; lia| cbv beta; lia]|].
  exists l. apply (rw_cells_agree_nw asegs m m2 _ _ LT); apply AGD; cbn; unfold TR_INIT; lia.
Qed.

Theorem tr_iter : forall k so usp buf cap x0 x1 x2 x3 x4 x5, (so = stdout_init \/ exists j, (j < 499)%nat /\ so = so_lines j) ->
  cpsE asegs (TLOOP RT OUT_rep ERR_rep XENV LIBP CG fs k so usp buf cap x0 x1 x2 x3 x4 x5) (evw 1 (emit0_out so))
    (fun c => (1 < k /\ TLOOP RT OUT_rep ERR_rep XENV LIBP CG fs (k - 1) (emit0_next so) usp buf cap x0 x1 x2 x3 x4 x5 c)
              \/ (k = 1 /\ TFREE RT OUT_rep ERR_rep XENV LIBP CG fs (emit0_next so) usp buf cap x0 x1 x2 x3 x4 x5 c)).
Proof using AF AF_DRV FUZZC VPR OUT_loc ERR_loc XENV_loc IO_img XENV_img LOCP CGH XENV_ax XENV_incb XENV_upd XENV_fp_ax.
  intros k so usp buf cap x0 x1 x2 x3 x4 x5 Hso T c HL Hk.
  destruct HL as (Σ & CL & plen & d & owned & payload & ra & gp & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s3
                  & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7
                  & F & fc & m & HA & HT & Hk14 & HCR).
  pose proof HT as (ART0 & MI0 & CLX0 & FR0 & TF0 & ST0 & B16 & ULO & USP0 & SPW & (LVP & LIBc & LVN & LVS & LCG) & FRS & PL & PB & BD & P0 & P1 & CAP0 & UT0).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  set (lo := rt_sp0 RT Σ - STACK_WIN) in *.
  set (DRV := tr_live plen owned buf cap) in *.
  assert (EU : bv_unsigned (Z_to_bv 64 (usp - 160)) = usp - 160) by (apply unsigned_lit; ul).
  assert (INB : In (buf, cap) (rt_live RT Σ)).
  { apply (Permutation_in _ (Permutation_sym LVP)). apply in_or_app. left. unfold DRV, tr_live. apply in_or_app. right. left. reflexivity. }
  assert (INO : 0 < plen -> In (owned, plen) DRV).
  { intros Hp. unfold DRV, tr_live. rewrite (proj2 (Z.eqb_neq plen 0) ltac:(lia)). left. reflexivity. }
  assert (DRVIN : forall p n, In (p, n) DRV -> In (p, n) (rt_live RT Σ)).
  { intros p n Hin. apply (Permutation_in _ (Permutation_sym LVP)). apply in_or_app. left. exact Hin. }
  assert (CLIN : forall p n, In (p, n) CL -> In (p, n) (rt_live RT Σ)).
  { intros p n Hin. apply (Permutation_in _ (Permutation_sym LVP)). apply in_or_app. right. exact Hin. }
  assert (DPOS : 0 < d /\ ((exists p n, In (p, n) DRV /\ p <= d /\ d + Z.of_nat (length payload) <= p + n) \/ (payload = [] /\ d = FZ_EMPTY))).
  { destruct (Z.eq_dec plen 0) as [Z0|NZ].
    - destruct (P0 Z0) as [-> _]. split; [unfold TR_EMPTY; lia|]. right. split; [destruct payload; [reflexivity| cbn in PL; lia] | reflexivity].
    - rewrite (P1 ltac:(lia)).
      pose proof (af_live_range RT AF Σ m owned plen ART0 (DRVIN _ _ (INO ltac:(lia)))) as (R1 & _).
      split; [lia|]. left. exists owned, plen. split; [exact (INO ltac:(lia))| lia]. }
  pose proof CLX0 as (_ & _ & XE0 & _ & (g0 & SG0) & (ev & ER0) & _).
  pose proof (XENV_incb m XE0) as IC0.
  (* [comment removed for export] *)
  pose proof (tr_loop_head_walk (usp - 160) d plen (Z_to_bv 8 0) ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 owned) s3
                (Z_to_bv 64 k) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) s8 s9 s10 s11 t3 t4 t5 t6 F fc m IC0 MI0) as W0.
  lazymatch type of W0 with evt asegs _ ?X =>
    assert (W0' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W0) end.
  clear W0.
  apply (cps_realizes asegs _ _ _ c (asta_evt RT AF Σ _ fs _ _ W0') HA).
  intros cf0 Hc0.
  destruct (ASTA_unpack RT Σ _ _ cf0 Hc0) as (ms0 & (m0 & -> & MU0 & WM0 & MI0' & IC1) & Hc0').
  assert (A01 : agree_on (fun x => client_static x /\ x <> TR_INCB) m m0).
  { apply (agree_of_munch _ _ _ _ MU0). intros x [_ Hx]. cbn. split; [unfold TR_INCB in *; lia| exact I]. }
  assert (AS0 : agree_on (fun x => usp - 160 <= x < USTACK_TOP) m m0).
  { apply (agree_of_munch _ _ _ _ MU0). intros x Hx. cbn. split; [unfold TR_INCB; ul| exact I]. }
  assert (ART0' : ART RT Σ m0).
  { apply (af_frame RT AF Σ m m0 (usp - 160) ART0); [ul| |exact WM0].
    intros a Ha. apply MU0. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. right; left. apply client_static_intro. unfold TR_INCB in Hin. lia. }
  assert (LIB0' : LIBP CL m0).
  { apply (LOCP CL m m0 LIBc). intros a Ha. apply MU0. cbn [outside]. split; [| exact I]. destruct Ha as [Ha|(p & n & Hin & Hr)].
    - intros Hx. destruct Ha as (l1 & h1 & Hin & Hlh). unfold LIB_D in Hin. unfold TR_INCB in Hx.
      repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
    - pose proof (af_live_range RT AF Σ m p n ART0 (CLIN _ _ Hin)) as (R1 & R2 & R3). unfold TR_INCB. ul. }
  assert (SG0' : ro_cells asegs m0 SSP_GUARD [C8 g0]).
  { apply (ro_cells_agree asegs m m0 _ _ SG0). eapply agree_sub; [exact A01|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx.
    split; [apply client_static_intro; unfold SSP_GUARD in Hx; lia| unfold SSP_GUARD, TR_INCB in *; lia]. }
  assert (ER0' : rw_cells asegs m0 ERRNO_A [C4 ev]).
  { apply (rw_cells_agree_nw asegs m m0 _ _ ER0). eapply agree_sub; [exact A01|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx.
    split; [apply client_static_intro; unfold ERRNO_A, TP_A in Hx; lia| unfold ERRNO_A, TP_A, TR_INCB in *; lia]. }
  assert (ST0' : stk asegs m0 lo (usp - 160)).
  { apply (stk_agree asegs m m0 _ _ ST0); [| exact WM0]. apply (agree_of_munch _ _ _ _ MU0). intros x Hx. cbn. split; [unfold TR_INCB; ul| exact I]. }
  assert (BD0 : bytes_at asegs m0 d payload).
  { apply (bytes_at_agree asegs m m0 _ _ BD). apply (agree_of_munch _ _ _ _ MU0). intros x Hx. cbn.
    destruct DPOS as [_ [(p & n & Hin & Hp & Hn)|[-> ->]]]; [| cbn in Hx; lia].
    pose proof (af_live_range RT AF Σ m p n ART0 (DRVIN _ _ Hin)) as (R1 & R2 & R3). unfold TR_INCB. split; [destruct R3; ul| exact I]. }
  apply (FUZZC Σ (PMfd fds0 fs) (Z_to_bv 64 RA_FUZZ) (Z_to_bv 64 (usp - 160)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 plen)
           (Z_to_bv 64 d) (Z_to_bv 64 d) (Z_to_bv 64 plen) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 owned) s3 (Z_to_bv 64 TR_INIT)
           (Z_to_bv 64 k) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 d payload CL DRV lo); try reflexivity; try assumption.
  - apply PMfd_fdfs_only.
  - apply PMfd_mat_stable.
  - rewrite <- PL. reflexivity.
  - exact (proj1 DPOS).
  - lia.
  - exact (proj2 DPOS).
  - exact (Permutation_trans LVP (Permutation_app_comm _ _)).
  - intros p n Hin. apply (Permutation_in _ LVP) in Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin]; [| exact (LVS p n Hin)].
    unfold DRV, tr_live in Hin. destruct (Z.eqb_spec plen 0) as [E|E]; cbn [app In] in Hin.
    + destruct Hin as [Hin|[]]. injection Hin as <- <-. exact CAP0.
    + destruct Hin as [Hin|[Hin|[]]]; injection Hin as <- <-; [lia| exact CAP0].
  - unfold DRV, tr_live. destruct (plen =? 0); cbn; ul.
  - unfold FUZZ_COST in *. nia.
  - unfold fp_invalid. rewrite EU, unsigned_lit by lia. left. ul.
  - rewrite LCG. exact CGH.
  - exact (drv_ssp m0 g0 (AF_DRV Σ m0 ART0') SG0').
  - rewrite errno_A'. exists ev. exact ER0'.
  - rewrite EU. exact ST0'.
  - rewrite EU. ul.
  - rewrite EU. ul.
  - rewrite EU. apply Z.mod_divide; [lia|]. apply Z.mod_divide in B16; [| lia]. destruct B16 as (q & ->). exists (q - 10). lia.
  - rewrite EU. lia.
  - intros cf1 (Σ1 & CL' & Hc1 & PERM1 & LEN1 & POS1 & FRS1 & SP1 & CR1 & CG1).
    destruct (ASTA_unpack RT Σ1 _ _ cf1 Hc1) as (ms1 & (m1 & RS1 & (ART1 & MI1 & ST1) & PRES1 & LIB1 & ERR1) & Hc1').
    destruct RS1 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & ->).
    rewrite EU in ST1, PRES1. rewrite errno_A' in ERR1.
    rewrite (ret_pc_even RA_FUZZ) in Hc1' by (unfold RA_FUZZ; lia).
    pose proof PRES1 as PRES1c. unfold cli_pres in PRES1.
    assert (IC1' : rw_cells asegs m1 TR_INCB [C1 (Z_to_bv 8 1)]).
    { apply (rw_cells_agree_nw asegs m0 m1 _ _ IC1). intros a Ha. cbn [cells_size csize Nat.add] in Ha. assert (EA : bv_unsigned a = TR_INCB) by lia.
      apply PRES1; rewrite EA; [right; left; exact INCB_static| exact INCB_outside_W]. }
    pose proof (agree_stack_pres_fp _ _ _ _ _ _ PRES1 ltac:(intros x Hx; apply LIBW_outside_hi; ul)) as AG1.
    assert (AGD1 : agree_on (fun x => d <= x < d + plen) m0 m1).
    { destruct (Z.eq_dec plen 0) as [Z0|NZ]; [intros a Ha; lia|].
      rewrite (P1 ltac:(lia)) in *. apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES1). intros x Hx.
      pose proof (af_live_range RT AF Σ m owned plen ART0 (DRVIN _ _ (INO ltac:(lia)))) as (R1 & R2 & R3).
      split; [right; right; left; exists owned, plen; split; [exact (INO ltac:(lia))| lia]|].
      destruct R3 as [R3|R3]; [apply LIBW_outside_lo; lia| apply LIBW_outside_hi; lia]. }
    assert (PERM1' : Permutation (rt_live RT Σ1) (DRV ++ CL')) by exact (Permutation_trans PERM1 (Permutation_app_comm _ _)).
    assert (CL1IN : forall p n, In (p, n) CL' -> In (p, n) (rt_live RT Σ1)).
    { intros p n Hin. apply (Permutation_in _ (Permutation_sym PERM1)). apply in_or_app. left. exact Hin. }
    (* [comment removed for export] *)
    pose proof (tr_fuzz_ret_walk (usp - 160) (Z_to_bv 8 1) gp t0' t1' t2' (Z_to_bv 64 plen) (Z_to_bv 64 d) a1' a2' a3' a4' a5' a6' a7'
                  (Z_to_bv 64 owned) s3 (Z_to_bv 64 k) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) s8 s9 s10 s11 t3' t4' t5' t6' F' fc' m1 lo ST1
                  ltac:(ul) ltac:(ul) ltac:(apply Z.mod_divide; [lia|]; apply Z.mod_divide in B16; [| lia]; destruct B16 as (q & ->); exists (q - 10); lia)
                  ltac:(ul) IC1' MI1) as W1.
    lazymatch type of W1 with evt asegs _ ?X =>
      assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
    clear W1.
    apply (cps_realizes asegs _ _ _ _ (asta_evt RT AF Σ1 _ fs _ _ W1') Hc1').
    intros cf2 Hc2.
    destruct (ASTA_unpack RT Σ1 _ _ cf2 Hc2) as (ms2 & (m2 & junk & -> & MU2 & WM2 & MI2 & EF1 & EF2 & EF3 & ST2 & IC2) & Hc2').
    assert (A23 : agree_on (fun x => client_static x /\ x <> TR_INCB) m1 m2).
    { apply (agree_of_munch _ _ _ _ MU2). intros x [Hx Hn]. pose proof (client_static_range x Hx). cbn. split; [ul|]. split; [unfold TR_INCB in *; lia| exact I]. }
    assert (ER2 : exists v, rw_cells asegs m2 ERRNO_A [C4 v]).
    { destruct ERR1 as [v1 ERR1]. exists v1. apply (rw_cells_agree_nw asegs m1 m2 _ _ ERR1). eapply agree_sub; [exact A23|]. intros x Hx.
      cbn [cells_size csize Nat.add] in Hx. split; [apply client_static_intro; unfold ERRNO_A, TP_A in Hx; lia| unfold ERRNO_A, TP_A, TR_INCB in *; lia]. }
    assert (CLX2 : CLX OUT_rep ERR_rep XENV LIBT so m2) by exact (CLX_T_bracket so m m0 m1 m2 DRV (usp - 160) CLX0 A01 PRES1c ER2 A23 IC2).
    pose proof CLX2 as (OUT2 & ERRP2 & _).
    assert (ART2 : ART RT Σ1 m2).
    { apply (af_frame RT AF Σ1 m1 m2 (usp - 160 - 80) ART1); [rewrite SP1; ul| |exact WM2].
      intros a Ha. apply MU2. cbn [outside]. split; [intros Hin; apply Ha; left; ul|]. split; [| exact I].
      intros Hin. apply Ha. right; left. apply client_static_intro. unfold TR_INCB in Hin. lia. }
    assert (LIB2 : LIBP CL' m2).
    { apply (LOCP CL' m1 m2 LIB1). intros a Ha. apply MU2. cbn [outside]. destruct Ha as [Ha|(p & n & Hin & Hr)].
      - pose proof (client_static_range _ (proj1 (LIBD_static _ Ha))). split; [ul|]. split; [| exact I].
        intros Hx. destruct Ha as (l1 & h1 & Hin & Hlh). unfold LIB_D in Hin. unfold TR_INCB in Hx.
        repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
      - pose proof (af_live_range RT AF Σ1 m1 p n ART1 (CL1IN _ _ Hin)) as (R1 & R2 & R3). rewrite SP1 in R2. unfold TR_INCB. split; [ul|]. split; [ul| exact I]. }
    assert (EU2 : bv_unsigned (Z_to_bv 64 (usp - 160 - 80)) = usp - 160 - 80) by (apply unsigned_lit; ul).
    apply (VPR Σ1 fds0 fs (Z_to_bv 64 0x1f3030) (Z_to_bv 64 (usp - 160 - 80)) gp (Z_to_bv 64 TP_A) t0' t1' t2' (Z_to_bv 64 plen)
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
      rewrite (ret_pc_even 0x1f3030) in Hc3' by lia.
      assert (CLX3 : CLX OUT_rep ERR_rep XENV LIBT (emit0_next so) m3)
        by exact (CLX_io OUT_rep ERR_rep IO_FP XENV XENV_FP LIBT OUT_loc ERR_loc XENV_loc LIBT_loc IO_img XENV_img
                    _ _ m2 m3 _ _ _ CLX2 PRES3 WM3 OUT3 (ERRP3 ERRP2)).
      pose proof (agree_stack_pres_fp _ _ _ _ _ _ PRES3 ltac:(intros x Hx; apply IO_outside_hi; ul)) as AG3.
      assert (LIB3 : LIBP CL' m3).
      { apply (LOCP CL' m2 m3 LIB2). intros a Ha. apply PRES3.
        - destruct Ha as [Ha|(p & n & Hin & Hr)]; [right; left; exact (proj1 (LIBD_static _ Ha))|].
          right; right; left. exists p, n. split; [exact (CL1IN _ _ Hin)| exact Hr].
        - destruct Ha as [Ha|(p & n & Hin & Hr)]; [exact (LIBD_outside_IO _ Ha)|].
          pose proof (af_live_range RT AF Σ1 m2 p n ART2 (CL1IN _ _ Hin)) as (R1 & R2 & R3).
          destruct R3 as [R3|R3]; [apply IO_outside_lo; lia| apply IO_outside_hi; lia]. }
      assert (EF1' : rw_cells asegs m3 (usp - 160 - 80) [C8 (Z_to_bv 64 (usp - 160 - 80 + 24)); C8 (Z_to_bv 64 0x1f2f48); CB 8 junk]).
      { apply (rw_cells_agree asegs m2 m3 _ _ EF1); [| exact WM3]. eapply agree_sub; [exact AG3|]. intros x Hx.
        cbn [cells_size csize Nat.add] in Hx. cbv beta. ul. }
      assert (EF2' : rw_cells asegs m3 (usp - 160 - 80 + 24) [C8 (Z_to_bv 64 0)]).
      { apply (rw_cells_agree asegs m2 m3 _ _ EF2); [| exact WM3]. eapply agree_sub; [exact AG3|]. intros x Hx.
        cbn [cells_size csize Nat.add] in Hx. cbv beta. ul. }
      assert (EF3' : rw_cells asegs m3 (usp - 160 - 80 + 32) [C8 a2'; C8 a3'; C8 a4'; C8 a5'; C8 a6'; C8 a7']).
      { apply (rw_cells_agree asegs m2 m3 _ _ EF3); [| exact WM3]. eapply agree_sub; [exact AG3|]. intros x Hx.
        cbn [cells_size csize Nat.add] in Hx. cbv beta. ul. }
      (* [comment removed for export] *)
      pose proof (tr_emit_ret_walk (usp - 160) k gp u0 u1 u2 (Z_to_bv 64 plen) (Z_to_bv 64 d) v b1 b2 b3 b4 b5 b6 b7
                    (Z_to_bv 64 owned) s8 s9 s10 s11 u3 u4 u5 u6 a2' a3' a4' a5' a6' a7'
                    F3 fc3 m3 lo junk ST3 ltac:(ul) ltac:(ul)
                    ltac:(apply Z.mod_divide; [lia|]; apply Z.mod_divide in B16; [| lia]; destruct B16 as (q & ->); exists (q - 10); lia)
                    ltac:(ul) ltac:(lia) EF1' EF2' EF3' MI3) as W3.
      lazymatch type of W3 with evt asegs _ ?X =>
        assert (W3' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W3) end.
      clear W3.
      apply (cps_realizes asegs _ _ _ _ (asta_evt RT AF Σ1 _ fs _ _ W3') Hc3').
      intros cf4 Hc4. apply Hk.
      destruct (ASTA_unpack RT Σ1 _ _ cf4 Hc4) as (ms4 & (Hcase & ST4) & Hc4').
      assert (AG03 : agree_on (fun x => usp - 160 <= x < USTACK_TOP) m m3).
      { apply (agree_trans _ m m0 m3); [exact AS0|]. apply (agree_trans _ m0 m1 m3); [eapply agree_sub; [exact AG1|]; intros x Hx; cbv beta in *; lia|].
        apply (agree_trans _ m1 m2 m3).
        - apply (agree_of_munch _ _ _ _ MU2). intros x Hx. cbn. split; [lia|]. split; [unfold TR_INCB; ul| exact I].
        - eapply agree_sub; [exact AG3|]. intros x Hx. cbv beta in *. lia. }
      assert (AGD03 : agree_on (fun x => d <= x < d + plen) m m3).
      { destruct (Z.eq_dec plen 0) as [Z0|NZ]; [intros a Ha; lia|].
        assert (IN1 : In (owned, plen) (rt_live RT Σ1)).
        { apply (Permutation_in _ (Permutation_sym PERM1')). apply in_or_app. left. exact (INO ltac:(lia)). }
        pose proof (af_live_range RT AF Σ m owned plen ART0 (DRVIN _ _ (INO ltac:(lia)))) as (R1 & R2 & R3).
        rewrite (P1 ltac:(lia)) in *.
        apply (agree_trans _ m m0 m3).
        { apply (agree_of_munch _ _ _ _ MU0). intros x Hx. cbn. unfold TR_INCB. split; [destruct R3; ul| exact I]. }
        apply (agree_trans _ m0 m1 m3); [exact AGD1|].
        apply (agree_trans _ m1 m2 m3).
        - apply (agree_of_munch _ _ _ _ MU2). intros x Hx. cbn. unfold TR_INCB. split; [ul|]. split; [destruct R3; ul| exact I].
        - apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES3). intros x Hx.
          split; [right; right; left; exists owned, plen; split; [exact IN1| lia]|].
          destruct R3 as [R3|R3]; [apply IO_outside_lo; lia| apply IO_outside_hi; lia]. }
      assert (HT3 : TCTX RT OUT_rep ERR_rep XENV LIBP CG Σ1 CL' (emit0_next so) usp buf cap plen d owned payload
                      c0 c1 c2 c3 c4 c5 c6 c7 x0 x1 x2 x3 x4 x5 m3).
      { apply (TCTX_agree_nw RT OUT_rep ERR_rep XENV LIBP CG AF Σ Σ1 CL CL' so (emit0_next so) usp buf cap plen d owned payload
                 c0 c1 c2 c3 c4 c5 c6 c7 x0 x1 x2 x3 x4 x5 m m3 HT ART3 MI3); try assumption; try (rewrite SP1; exact ST4).
        split; [exact PERM1'|]. split; [exact LIB3|]. split; [exact LEN1|]. split; [exact POS1| rewrite CG1; exact LCG]. }
      destruct Hcase as [(K1 & ->)|(K1 & ->)].
      * left. split; [exact K1|].
        exists Σ1, CL', plen, d, owned, payload, (Z_to_bv 64 0x1f2f48), gp, u0, u1, u2, v, b1, b2, b3, b4, b5, b6, b7, (Z_to_bv 64 (-1)), s8, s9, s10, s11.
        exists u3, u4, u5, u6, c0, c1, c2, c3, c4, c5, c6, c7, F3, fc3, m3.
        split; [exact Hc4'|]. split; [exact HT3|]. split; [lia|]. unfold FUZZ_COST in *. nia.
      * right. split; [exact K1|].
        exists Σ1, CL', plen, d, owned, payload, gp, u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, s8, s9, s10, s11.
        exists u3, u4, u5, u6, c0, c1, c2, c3, c4, c5, c6, c7, F3, fc3, m3.
        split; [exact Hc4'| exact HT3].
Qed.

End Tr2.
