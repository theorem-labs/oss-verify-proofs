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
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import Tac ImageA Nodes RzCPS NodesA.
From OSSVerify.Proofs.openssl.punycode.lib.Spec Require Import Prelim Canon Stdio Prog.
From OSSVerify.Proofs.openssl.punycode.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.punycode.lib.B Require Import Layout RT_iface D_iface D_defs D_kit D_libiface D_clx D_rlkit X_ax D_trpro D_trwalk D_trdefs.
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
Variable LIB : mem -> Prop.
Variable fs : Fs.
Hypothesis AF : art_facts RT.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis FUZZ : fuzz_one_cps RT LIB.
Hypothesis VPR : vprintf_emit0_icontract RT OUT_rep ERR_rep IO_FP.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis XENV_loc : fp_local XENV_FP XENV.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis IO_img : forall x, in_ranges IO_FP x -> client_static x /\ ~ drv_cell x /\ outside LIB_FP x.
Hypothesis XENV_img : forall x, in_ranges XENV_FP x -> client_static x /\ ~ drv_cell x /\ outside IO_FP x /\ outside LIB_FP x.
(* [comment removed for export] *)
Hypothesis XENV_ax : forall m, XENV m -> exists k fin p1 p2, AXA k fin p1 p2 m.
Hypothesis XENV_libc : forall m, XENV m -> libc_cells m.
Hypothesis XENV_incb : forall m, XENV m -> rw_cells bsegs m TR_INCB [C1 (Z_to_bv 8 0)].
Hypothesis XENV_upd : forall m m', XENV m ->
  agree_on (fun x => in_ranges XENV_FP x /\ ~ (0xbfae60 <= x < 0xbfae90) /\ ~ (0xbfaf80 <= x < 0xbfaf90) /\ x <> TR_INIT /\ x <> TR_INCB) m m' ->
  (exists k fin p1 p2, AXA k fin p1 p2 m') -> rw_cells bsegs m' TR_INCB [C1 (Z_to_bv 8 0)] -> XENV m'.
Hypothesis XENV_fp_ax : forall x, (0xbfae60 <= x < 0xbfae90 \/ 0xbfaf80 <= x < 0xbfaf90 \/ x = TR_INIT \/ x = TR_INCB) -> in_ranges XENV_FP x.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, FUZZ_STACK, g_read_stage in *; lia.

Lemma outside_image_ranges : forall (W : list (Z * Z)), (forall x, in_ranges W x -> client_static x) ->
  forall x, SEGTOP_A <= x -> outside W x.
Proof.
  intros W HW x Hx. apply outside_of_not_in_ranges'. intros Hin. pose proof (client_static_range x (HW x Hin)). lia.
Qed.

Lemma LIB_outside_hi : forall x, SEGTOP_A <= x -> outside LIB_FP x.
Proof. apply outside_image_ranges. intros x Hx. exact (proj1 (LIB_img x Hx)). Qed.

Lemma IO_outside_hi : forall x, SEGTOP_A <= x -> outside IO_FP x.
Proof using IO_img. apply outside_image_ranges. intros x Hx. exact (proj1 (IO_img x Hx)). Qed.

(* [comment removed for export] *)
Lemma INCB_static : client_static TR_INCB.
Proof. apply client_static_intro. unfold TR_INCB. lia. Qed.
Lemma INCB_not_lib : outside LIB_FP TR_INCB.
Proof using XENV_img XENV_fp_ax. exact (proj2 (proj2 (proj2 (XENV_img _ (XENV_fp_ax _ ltac:(right; right; right; reflexivity)))))). Qed.
Lemma INCB_not_io : ~ in_ranges IO_FP TR_INCB.
Proof using XENV_img XENV_fp_ax.
  apply not_in_ranges_of_outside. exact (proj1 (proj2 (proj2 (XENV_img _ (XENV_fp_ax _ ltac:(right; right; right; reflexivity)))))).
Qed.
Lemma INCB_not_drv : ~ drv_cell TR_INCB.
Proof. unfold drv_cell, ERRNO_A, TP_A, SSP_GUARD, g_read_stage, TR_INCB. lia. Qed.
Lemma AX_static : forall x, (0xbfae60 <= x < 0xbfae90 \/ 0xbfaf80 <= x < 0xbfaf90 \/ x = TR_INIT \/ x = TR_INCB) -> client_static x /\ outside LIB_FP x.
Proof using XENV_img XENV_fp_ax. intros x Hx. destruct (XENV_img x (XENV_fp_ax x Hx)) as (C & _ & _ & L). split; assumption. Qed.

(* [comment removed for export] *)
Lemma CLX_bracket : forall so m m0 m1 m2,
  CLX OUT_rep ERR_rep XENV LIB so m ->
  agree_on (fun x => client_static x /\ x <> TR_INCB) m m0 ->
  agree_on (fun x => client_static x /\ outside LIB_FP x) m0 m1 -> LIB m1 ->
  agree_on (fun x => client_static x /\ x <> TR_INCB) m1 m2 ->
  rw_cells bsegs m2 TR_INCB [C1 (Z_to_bv 8 0)] ->
  CLX OUT_rep ERR_rep XENV LIB so m2.
Proof using OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img XENV_ax XENV_upd XENV_fp_ax.
  intros so m m0 m1 m2 (H1 & H2 & H3 & H4 & (g & SG) & (v & ER) & RS & _) A01 A12 L1 A23 IC2.
  assert (A02 : agree_on (fun x => client_static x /\ outside LIB_FP x /\ x <> TR_INCB) m m2).
  { apply (agree_trans _ m m0 m2); [eapply agree_sub; [exact A01|]; intros x Hx; tauto|].
    apply (agree_trans _ m0 m1 m2); [eapply agree_sub; [exact A12|]; intros x Hx; tauto|].
    eapply agree_sub; [exact A23|]; intros x Hx; tauto. }
  assert (AIO : agree_on (fun x => in_ranges IO_FP x) m m2).
  { eapply agree_sub; [exact A02|]. intros x Hx. destruct (IO_img x Hx) as (C & _ & L). split; [exact C|]. split; [exact L|].
    intros ->. exact (INCB_not_io Hx). }
  split; [exact (OUT_loc so m m2 H1 AIO)|]. split; [exact (ERR_loc m m2 H2 AIO)|].
  split.
  { apply (XENV_upd m m2 H3).
    - eapply agree_sub; [exact A02|]. intros x (Hx & _ & _ & _ & N4). destruct (XENV_img x Hx) as (C & _ & _ & L). tauto.
    - destruct (XENV_ax m H3) as (k & fin & p1 & p2 & X1 & X2 & X3). exists k, fin, p1, p2.
      assert (AAX : agree_on (fun x => 0xbfae60 <= x < 0xbfae90 \/ 0xbfaf80 <= x < 0xbfaf90 \/ x = TR_INIT) m m2).
      { eapply agree_sub; [exact A02|]. intros x Hx. destruct (AX_static x ltac:(tauto)) as [C L]. split; [exact C|]. split; [exact L|].
        unfold TR_INIT, TR_INCB in *. lia. }
      split; [| split].
      + apply (rw_cells_agree_nw bsegs m m2 _ _ X1). eapply agree_sub; [exact AAX|]. intros x Hx. cbn [cells_size csize ax_cells Nat.add length] in Hx. cbv beta. lia.
      + apply (rw_cells_agree_nw bsegs m m2 _ _ X2). eapply agree_sub; [exact AAX|]. intros x Hx. cbn [cells_size csize ax_acells Nat.add length] in Hx. cbv beta. lia.
      + apply (rw_cells_agree_nw bsegs m m2 _ _ X3). eapply agree_sub; [exact AAX|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. unfold AX_LATCH, TR_INIT in *. lia.
    - exact IC2. }
  split.
  { apply (LIB_loc m1 m2 L1). eapply agree_sub; [exact A23|]. intros x Hx. destruct (LIB_img x Hx) as [C _]. split; [exact C|].
    intros ->. exact (not_in_ranges_of_outside _ _ INCB_not_lib Hx). }
  assert (AGD : forall lo n, (forall x, lo <= x < lo + n -> drv_cell x) -> agree_on (fun x => lo <= x < lo + n) m m2).
  { intros lo n Hd. eapply agree_sub; [exact A02|]. intros x Hx. pose proof (Hd x Hx) as D.
    split; [exact (drv_cell_static x D)|]. split; [exact (drv_cell_not_lib x D)|]. intros ->. exact (INCB_not_drv D). }
  unfold drv_cell in AGD.
  split; [exists g; apply (ro_cells_agree bsegs m m2 _ _ SG); apply AGD; cbn; lia|].
  split; [exists v; apply (rw_cells_agree_nw bsegs m m2 _ _ ER); apply AGD; cbn; lia|].
  split; [apply (stk_agree_nw bsegs m m2 _ _ RS); eapply agree_sub; [apply (AGD g_read_stage 65536); lia| cbv beta; lia]| exact I].
Qed.

Theorem tr_iter : forall k so usp buf cap x0 x1 x2 x3 x4 x5, (so = stdout_init \/ exists j, (j < 499)%nat /\ so = so_lines j) ->
  cpsE bsegs (TLOOP RT OUT_rep ERR_rep XENV LIB fs k so usp buf cap x0 x1 x2 x3 x4 x5) (evw 1 (emit0_out so))
    (fun c => (1 < k /\ TLOOP RT OUT_rep ERR_rep XENV LIB fs (k - 1) (emit0_next so) usp buf cap x0 x1 x2 x3 x4 x5 c)
              \/ (k = 1 /\ TFREE RT OUT_rep ERR_rep XENV LIB fs (emit0_next so) usp buf cap x0 x1 x2 x3 x4 x5 c)).
Proof using AF AF_DRV FUZZ VPR OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img XENV_ax XENV_libc XENV_incb XENV_upd XENV_fp_ax.
  intros k so usp buf cap x0 x1 x2 x3 x4 x5 Hso T c HL Hk.
  destruct HL as (Σ & plen & d & owned & payload & ra & gp & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s3
                  & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7
                  & F & fc & m & HA & HT & Hk14 & HCR).
  pose proof HT as (ART0 & MI0 & CLX0 & FR0 & TF0 & ST0 & B16 & ULO & USP0 & SPW & LV & FRS & PL & PB & BD & P0 & P1 & CAP0 & UT0).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  set (lo := rt_sp0 RT Σ - STACK_WIN) in *.
  assert (EU : bv_unsigned (Z_to_bv 64 (usp - 160)) = usp - 160) by (apply unsigned_lit; ul).
  assert (DPOS : 0 < d /\ ((exists p n, In (p, n) (rt_live RT Σ) /\ p <= d /\ d + Z.of_nat (length payload) <= p + n) \/ (payload = [] /\ d = FZ_EMPTY))).
  { destruct (Z.eq_dec plen 0) as [Z0|NZ].
    - destruct (P0 Z0) as [-> _]. split; [unfold TR_EMPTY; lia|]. right. split; [destruct payload; [reflexivity| cbn in PL; lia] | reflexivity].
    - rewrite (P1 ltac:(lia)).
      assert (IN : In (owned, plen) (rt_live RT Σ)) by (rewrite LV; unfold tr_live; rewrite (proj2 (Z.eqb_neq plen 0) NZ); left; reflexivity).
      pose proof (af_live_range RT AF Σ m owned plen ART0 IN) as (R1 & _).
      split; [lia|]. left. exists owned, plen. split; [exact IN| lia]. }
  pose proof CLX0 as (_ & _ & XE0 & LIB0 & (g0 & SG0) & _).
  pose proof (XENV_incb m XE0) as IC0.
  (* [comment removed for export] *)
  pose proof (tr_loop_head_walk (usp - 160) d plen (Z_to_bv 8 0) ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 owned) s3
                (Z_to_bv 64 k) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) s8 s9 s10 s11 t3 t4 t5 t6 F fc m IC0 MI0) as W0.
  lazymatch type of W0 with evt bsegs _ ?X =>
    assert (W0' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W0) end.
  clear W0.
  apply (cps_realizes bsegs _ _ _ c (asta_evt RT AF Σ _ fs _ _ W0') HA).
  intros cf0 Hc0.
  destruct (ASTA_unpack RT Σ _ _ cf0 Hc0) as (ms0 & (m0 & -> & MU0 & WM0 & MI0' & IC1) & Hc0').
  assert (A01 : agree_on (fun x => client_static x /\ x <> TR_INCB) m m0).
  { apply (agree_of_munch _ _ _ _ MU0). intros x [_ Hx]. cbn. split; [unfold TR_INCB in *; lia| exact I]. }
  assert (AS0 : agree_on (fun x => usp - 160 <= x < USTACK_TOP) m m0).
  { apply (agree_of_munch _ _ _ _ MU0). intros x Hx. cbn. split; [unfold TR_INCB; ul| exact I]. }
  assert (ART0' : ART RT Σ m0).
  { apply (af_frame RT AF Σ m m0 (usp - 160) ART0); [ul| |exact WM0].
    intros a Ha. apply MU0. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. right; left. apply client_static_intro. unfold TR_INCB in Hin. lia. }
  assert (LIB0' : LIB m0).
  { apply (LIB_loc m m0 LIB0). eapply agree_sub; [exact A01|]. intros x Hx. destruct (LIB_img x Hx) as [C _]. split; [exact C|].
    intros ->. exact (not_in_ranges_of_outside _ _ INCB_not_lib Hx). }
  assert (SG0' : ro_cells bsegs m0 SSP_GUARD [C8 g0]).
  { apply (ro_cells_agree bsegs m m0 _ _ SG0). eapply agree_sub; [exact A01|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx.
    split; [apply client_static_intro; unfold SSP_GUARD in Hx; lia| unfold SSP_GUARD, TR_INCB in *; lia]. }
  assert (ST0' : stk bsegs m0 lo (usp - 160)).
  { apply (stk_agree bsegs m m0 _ _ ST0); [| exact WM0]. apply (agree_of_munch _ _ _ _ MU0). intros x Hx. cbn. split; [unfold TR_INCB; ul| exact I]. }
  apply (FUZZ Σ (PMfd fds0 fs) (Z_to_bv 64 RA_FUZZ) (Z_to_bv 64 (usp - 160)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 plen)
           (Z_to_bv 64 d) (Z_to_bv 64 d) (Z_to_bv 64 plen) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 owned) s3 (Z_to_bv 64 TR_INIT)
           (Z_to_bv 64 k) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 d payload lo); try reflexivity; try assumption.
  - apply PMfd_fdfs_only.
  - apply PMfd_mat_stable.
  - rewrite <- PL. reflexivity.
  - exact (proj1 DPOS).
  - lia.
  - apply (bytes_at_agree bsegs m m0 _ _ BD). apply (agree_of_munch _ _ _ _ MU0). intros x Hx. cbn.
    pose proof (proj1 DPOS). destruct DPOS as [_ [(p & n & Hin & Hp & Hn)|[-> ->]]]; [| cbn in Hx; lia].
    pose proof (af_live_range RT AF Σ m p n ART0 Hin) as (R1 & R2 & R3). rewrite <- PL in Hn. unfold TR_INCB. split; [destruct R3; ul| exact I].
  - exact (proj2 DPOS).
  - intros p n Hin. rewrite LV in Hin. unfold tr_live in Hin. destruct (Z.eqb_spec plen 0) as [E|E]; cbn [app In] in Hin.
    + destruct Hin as [Hin|[]]. injection Hin as <- <-. exact CAP0.
    + destruct Hin as [Hin|[Hin|[]]]; injection Hin as <- <-; [lia| exact CAP0].
  - rewrite LV. unfold tr_live, LIVE_MAX, FUZZ_LIVE. destruct (plen =? 0); cbn; lia.
  - unfold FUZZ_COST in *. nia.
  - left. rewrite EU, unsigned_lit by lia. ul.
  - exact (drv_ssp m0 g0 (AF_DRV Σ m0 ART0') SG0').
  - rewrite EU. exact ST0'.
  - rewrite EU. ul.
  - rewrite EU. ul.
  - rewrite EU. apply Z.mod_divide; [lia|]. apply Z.mod_divide in B16; [| lia]. destruct B16 as (q & ->). exists (q - 10). lia.
  - rewrite EU. lia.
  - intros cf1 (Σ1 & Hc1 & LV1 & FRS1 & SP1 & CR1).
    destruct (ASTA_unpack RT Σ1 _ _ cf1 Hc1) as (ms1 & (m1 & RS1 & (ART1 & MI1 & ST1) & PRES1 & LIB1) & Hc1').
    destruct RS1 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & ->).
    rewrite EU in ST1, PRES1.
    rewrite (ret_pc_even RA_FUZZ) in Hc1' by (unfold RA_FUZZ; lia).
    assert (A12 : agree_on (fun x => client_static x /\ outside LIB_FP x) m0 m1).
    { apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES1). intros x [C L]. split; [right; left; exact C| exact L]. }
    assert (IC1' : rw_cells bsegs m1 TR_INCB [C1 (Z_to_bv 8 1)]).
    { apply (rw_cells_agree_nw bsegs m0 m1 _ _ IC1). eapply agree_sub; [exact A12|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx.
      replace x with TR_INCB by lia. split; [exact INCB_static| exact INCB_not_lib]. }
    pose proof (agree_stack_pres_fp _ _ _ _ _ _ PRES1 ltac:(intros x Hx; apply LIB_outside_hi; ul)) as AG1.
    assert (AGD1 : agree_on (fun x => d <= x < d + plen) m0 m1).
    { destruct (Z.eq_dec plen 0) as [Z0|NZ]; [intros a Ha; lia|].
      rewrite (P1 ltac:(lia)) in *. apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES1). intros x Hx.
      assert (IN : In (owned, plen) (rt_live RT Σ)) by (rewrite LV; unfold tr_live; rewrite (proj2 (Z.eqb_neq plen 0) NZ); left; reflexivity).
      pose proof (af_live_range RT AF Σ m owned plen ART0 IN) as (R1 & R2 & R3).
      split; [right; right; left; exists owned, plen; split; [exact IN| lia]|].
      destruct R3 as [R3|R3]; [| apply LIB_outside_hi; lia].
      apply outside_of_not_in_ranges'. intros (lo1 & hi1 & Hin & Hx1). unfold LIB_FP in Hin.
      destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia. }
    (* [comment removed for export] *)
    pose proof (tr_fuzz_ret_walk (usp - 160) (Z_to_bv 8 1) gp t0' t1' t2' (Z_to_bv 64 plen) (Z_to_bv 64 d) a1' a2' a3' a4' a5' a6' a7'
                  (Z_to_bv 64 owned) s3 (Z_to_bv 64 k) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) s8 s9 s10 s11 t3' t4' t5' t6' F' fc' m1 lo ST1
                  ltac:(ul) ltac:(ul) ltac:(apply Z.mod_divide; [lia|]; apply Z.mod_divide in B16; [| lia]; destruct B16 as (q & ->); exists (q - 10); lia)
                  ltac:(ul) IC1' MI1) as W1.
    lazymatch type of W1 with evt bsegs _ ?X =>
      assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
    clear W1.
    apply (cps_realizes bsegs _ _ _ _ (asta_evt RT AF Σ1 _ fs _ _ W1') Hc1').
    intros cf2 Hc2.
    destruct (ASTA_unpack RT Σ1 _ _ cf2 Hc2) as (ms2 & (m2 & junk & -> & MU2 & WM2 & MI2 & EF1 & EF2 & EF3 & ST2 & IC2) & Hc2').
    assert (A23 : agree_on (fun x => client_static x /\ x <> TR_INCB) m1 m2).
    { apply (agree_of_munch _ _ _ _ MU2). intros x [Hx Hn]. pose proof (client_static_range x Hx). cbn. split; [ul|]. split; [unfold TR_INCB in *; lia| exact I]. }
    assert (CLX2 : CLX OUT_rep ERR_rep XENV LIB so m2) by exact (CLX_bracket so m m0 m1 m2 CLX0 A01 A12 LIB1 A23 IC2).
    pose proof CLX2 as (OUT2 & ERR2 & _).
    assert (ART2 : ART RT Σ1 m2).
    { apply (af_frame RT AF Σ1 m1 m2 (usp - 160 - 80) ART1); [rewrite SP1; ul| |exact WM2].
      intros a Ha. apply MU2. cbn [outside]. split; [intros Hin; apply Ha; left; ul|]. split; [| exact I].
      intros Hin. apply Ha. right; left. apply client_static_intro. unfold TR_INCB in Hin. lia. }
    assert (EU2 : bv_unsigned (Z_to_bv 64 (usp - 160 - 80)) = usp - 160 - 80) by (apply unsigned_lit; ul).
    apply (VPR Σ1 fds0 fs (Z_to_bv 64 0x1edf9c) (Z_to_bv 64 (usp - 160 - 80)) gp (Z_to_bv 64 TP_A) t0' t1' t2' (Z_to_bv 64 plen)
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
      rewrite (ret_pc_even 0x1edf9c) in Hc3' by lia.
      assert (CLX3 : CLX OUT_rep ERR_rep XENV LIB (emit0_next so) m3)
        by exact (CLX_io OUT_rep ERR_rep IO_FP XENV XENV_FP LIB OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img
                    _ _ m2 m3 _ _ _ CLX2 PRES3 WM3 OUT3 (ERRP3 ERR2)).
      pose proof (agree_stack_pres_fp _ _ _ _ _ _ PRES3 ltac:(intros x Hx; apply IO_outside_hi; ul)) as AG3.
      assert (EF1' : rw_cells bsegs m3 (usp - 160 - 80) [C8 (Z_to_bv 64 (usp - 160 - 80 + 24)); C8 (Z_to_bv 64 0x1edeb4); CB 8 junk]).
      { apply (rw_cells_agree bsegs m2 m3 _ _ EF1); [| exact WM3]. eapply agree_sub; [exact AG3|]. intros x Hx.
        cbn [cells_size csize Nat.add] in Hx. cbv beta. ul. }
      assert (EF2' : rw_cells bsegs m3 (usp - 160 - 80 + 24) [C8 (Z_to_bv 64 0)]).
      { apply (rw_cells_agree bsegs m2 m3 _ _ EF2); [| exact WM3]. eapply agree_sub; [exact AG3|]. intros x Hx.
        cbn [cells_size csize Nat.add] in Hx. cbv beta. ul. }
      assert (EF3' : rw_cells bsegs m3 (usp - 160 - 80 + 32) [C8 a2'; C8 a3'; C8 a4'; C8 a5'; C8 a6'; C8 a7']).
      { apply (rw_cells_agree bsegs m2 m3 _ _ EF3); [| exact WM3]. eapply agree_sub; [exact AG3|]. intros x Hx.
        cbn [cells_size csize Nat.add] in Hx. cbv beta. ul. }
      (* [comment removed for export] *)
      pose proof (tr_emit_ret_walk (usp - 160) k gp u0 u1 u2 (Z_to_bv 64 plen) (Z_to_bv 64 d) v b1 b2 b3 b4 b5 b6 b7
                    (Z_to_bv 64 owned) s8 s9 s10 s11 u3 u4 u5 u6 a2' a3' a4' a5' a6' a7'
                    F3 fc3 m3 lo junk ST3 ltac:(ul) ltac:(ul)
                    ltac:(apply Z.mod_divide; [lia|]; apply Z.mod_divide in B16; [| lia]; destruct B16 as (q & ->); exists (q - 10); lia)
                    ltac:(ul) ltac:(lia) EF1' EF2' EF3' MI3) as W3.
      lazymatch type of W3 with evt bsegs _ ?X =>
        assert (W3' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W3) end.
      clear W3.
      apply (cps_realizes bsegs _ _ _ _ (asta_evt RT AF Σ1 _ fs _ _ W3') Hc3').
      intros cf4 Hc4. apply Hk.
      destruct (ASTA_unpack RT Σ1 _ _ cf4 Hc4) as (ms4 & (Hcase & ST4) & Hc4').
      assert (WM13 : wmono bsegs m1 m3) by exact (wmono_trans bsegs m1 m2 m3 WM2 WM3).
      assert (AG03 : agree_on (fun x => usp - 160 <= x < USTACK_TOP) m m3).
      { apply (agree_trans _ m m0 m3); [exact AS0|]. apply (agree_trans _ m0 m1 m3); [eapply agree_sub; [exact AG1|]; intros x Hx; cbv beta in *; lia|].
        apply (agree_trans _ m1 m2 m3).
        - apply (agree_of_munch _ _ _ _ MU2). intros x Hx. cbn. split; [lia|]. split; [unfold TR_INCB; ul| exact I].
        - eapply agree_sub; [exact AG3|]. intros x Hx. cbv beta in *. lia. }
      assert (AGD03 : agree_on (fun x => d <= x < d + plen) m m3).
      { destruct (Z.eq_dec plen 0) as [Z0|NZ]; [intros a Ha; lia|].
        assert (IN : In (owned, plen) (rt_live RT Σ)) by (rewrite LV; unfold tr_live; rewrite (proj2 (Z.eqb_neq plen 0) NZ); left; reflexivity).
        pose proof (af_live_range RT AF Σ m owned plen ART0 IN) as (R1 & R2 & R3).
        rewrite (P1 ltac:(lia)) in *.
        apply (agree_trans _ m m0 m3).
        { apply (agree_of_munch _ _ _ _ MU0). intros x Hx. cbn. unfold TR_INCB. split; [destruct R3; ul| exact I]. }
        apply (agree_trans _ m0 m1 m3); [exact AGD1|].
        apply (agree_trans _ m1 m2 m3).
        - apply (agree_of_munch _ _ _ _ MU2). intros x Hx. cbn. unfold TR_INCB. split; [ul|]. split; [destruct R3; ul| exact I].
        - apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES3). intros x Hx.
          assert (IN1 : In (owned, plen) (rt_live RT Σ1)) by (rewrite LV1; exact IN).
          split; [right; right; left; exists owned, plen; split; [exact IN1| lia]|].
          destruct R3 as [R3|R3]; [| apply IO_outside_hi; lia].
          apply outside_of_not_in_ranges'. intros Hin. pose proof (client_static_range _ (proj1 (IO_img _ Hin))). lia. }
      assert (HT3 : TCTX RT OUT_rep ERR_rep XENV LIB Σ1 (emit0_next so) usp buf cap plen d owned payload
                      c0 c1 c2 c3 c4 c5 c6 c7 x0 x1 x2 x3 x4 x5 m3).
      { apply (TCTX_agree_nw RT OUT_rep ERR_rep XENV LIB AF Σ Σ1 so (emit0_next so) usp buf cap plen d owned payload
                 c0 c1 c2 c3 c4 c5 c6 c7 x0 x1 x2 x3 x4 x5 m m3 HT ART3 MI3); try assumption; rewrite SP1; exact ST4. }
      destruct Hcase as [(K1 & ->)|(K1 & ->)].
      * left. split; [exact K1|].
        exists Σ1, plen, d, owned, payload, (Z_to_bv 64 0x1edeb4), gp, u0, u1, u2, v, b1, b2, b3, b4, b5, b6, b7, (Z_to_bv 64 (-1)), s8, s9, s10, s11.
        exists u3, u4, u5, u6, c0, c1, c2, c3, c4, c5, c6, c7, F3, fc3, m3.
        split; [exact Hc4'|]. split; [exact HT3|]. split; [lia|]. unfold FUZZ_COST in *. nia.
      * right. split; [exact K1|].
        exists Σ1, plen, d, owned, payload, gp, u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, s8, s9, s10, s11.
        exists u3, u4, u5, u6, c0, c1, c2, c3, c4, c5, c6, c7, F3, fc3, m3.
        split; [exact Hc4'| exact HT3].
Qed.

End Tr2.
