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
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import ImageA.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import Nodes RzCPS NodesA.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Spec Require Import Prelim Canon Stdio Prog.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import Layout.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import RT_iface D_iface D_defs D_kit D_libiface D_clx D_rlkit X_atexit D_trpro D_trwalk D_trdefs D_tr1.
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
Variable XENV1 : mem -> Prop.
Variable XENV_FP : list (Z * Z).
Variable LIB : mem -> Prop.
Variable fs : Fs.
Hypothesis AF : art_facts RT.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis FUZZ : fuzz_one_cps RT LIB.
Hypothesis VPR : vprintf_emit0_icontract RT OUT_rep ERR_rep IO_FP.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis XENV1_loc : fp_local XENV_FP XENV1.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis IO_img : forall x, in_ranges IO_FP x -> client_static x /\ ~ drv_cell x /\ outside LIB_FP x.
Hypothesis XENV_img : forall x, in_ranges XENV_FP x -> client_static x /\ ~ drv_cell x /\ outside IO_FP x /\ outside LIB_FP x.

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

Lemma flag_outside_lib : forall x, TR_INIT <= x < TR_INIT + 1 -> outside LIB_FP x.
Proof. intros x Hx. apply drv_cell_not_lib. right; right; right. exact Hx. Qed.

Lemma flag_outside_io : forall x, TR_INIT <= x < TR_INIT + 1 -> outside IO_FP x.
Proof using IO_img.
  intros x Hx. apply outside_of_not_in_ranges'. intros Hin. apply (proj1 (proj2 (IO_img x Hin))). right; right; right. exact Hx.
Qed.

Theorem tr_iter : forall k so usp buf cap x0 x1 x2 x3 x4 x5 x6 x7, (so = stdout_init \/ exists j, (j < 499)%nat /\ so = so_lines j) ->
  cpsE asegs (TLOOP RT OUT_rep ERR_rep XENV1 LIB fs k so usp buf cap x0 x1 x2 x3 x4 x5 x6 x7) (evw 1 (emit0_out so))
    (fun c => (1 < k /\ TLOOP RT OUT_rep ERR_rep XENV1 LIB fs (k - 1) (emit0_next so) usp buf cap x0 x1 x2 x3 x4 x5 x6 x7 c)
              \/ (k = 1 /\ TFREE RT OUT_rep ERR_rep XENV1 LIB fs (emit0_next so) usp buf cap x0 x1 x2 x3 x4 x5 x6 x7 c)).
Proof using AF AF_DRV FUZZ VPR OUT_loc ERR_loc XENV1_loc LIB_loc IO_img XENV_img.
  intros k so usp buf cap x0 x1 x2 x3 x4 x5 x6 x7 Hso T c HL Hk.
  destruct HL as (Σ & plen & d & owned & payload & gp & t0 & t1 & t2 & a2 & a3 & a4 & a5 & a6 & a7 & s3 & s8 & s9 & s10 & s11
                  & t3 & t4 & t5 & t6 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & F & fc & m & HA & HT & Hk14 & HCR).
  pose proof HT as (ART0 & MI0 & CLX0 & FR0 & TF0 & ST0 & B16 & ULO & USP0 & SPW & LV & FRS & PL & PB & BD & P0 & P1 & CAP0 & UT0 & FL0).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  set (lo := rt_sp0 RT Σ - STACK_WIN) in *.
  assert (EU : bv_unsigned (Z_to_bv 64 (usp - 160)) = usp - 160) by (apply unsigned_lit; ul).
  assert (DPOS : 0 < d /\ ((exists p n, In (p, n) (rt_live RT Σ) /\ p <= d /\ d + Z.of_nat (length payload) <= p + n /\ d mod 8 = 0) \/ payload = [])).
  { destruct (Z.eq_dec plen 0) as [Z0|NZ].
    - destruct (P0 Z0) as [-> _]. split; [unfold TR_EMPTY; lia|]. right. destruct payload; [reflexivity| cbn in PL; lia].
    - rewrite (P1 ltac:(lia)).
      assert (IN : In (owned, plen) (rt_live RT Σ)) by (rewrite LV; unfold tr_live; rewrite (proj2 (Z.eqb_neq plen 0) NZ); left; reflexivity).
      pose proof (af_live_range RT AF Σ m owned plen ART0 IN) as (R1 & _).
      pose proof (af_live_align RT AF Σ m owned plen ART0 IN) as AL16.
      split; [lia|]. left. exists owned, plen. split; [exact IN|]. split; [lia|]. split; [lia|]. clear - AL16. Z.div_mod_to_equations. lia. }
  apply (FUZZ Σ (PMfd fds0 fs) (Z_to_bv 64 0x90d44) (Z_to_bv 64 (usp - 160)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 plen)
           (Z_to_bv 64 d) (Z_to_bv 64 d) (Z_to_bv 64 plen) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 owned) s3 (Z_to_bv 64 TR_BASE)
           (Z_to_bv 64 k) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) s8 s9 s10 s11 t3 t4 t5 t6 F fc m d payload lo); try reflexivity; try assumption.
  - apply PMfd_fdfs_only.
  - apply PMfd_mat_stable.
  - rewrite <- PL. reflexivity.
  - exact (proj1 DPOS).
  - lia.
  - exact (proj2 DPOS).
  - intros p n Hin. rewrite LV in Hin. unfold tr_live in Hin. destruct (Z.eqb_spec plen 0) as [E|E]; cbn [app In] in Hin.
    + destruct Hin as [Hin|[]]. injection Hin as <- <-. exact CAP0.
    + destruct Hin as [Hin|[Hin|[]]]; injection Hin as <- <-; [lia| exact CAP0].
  - rewrite LV. unfold tr_live, LIVE_MAX, FUZZ_LIVE. destruct (plen =? 0); cbn; lia.
  - unfold FUZZ_COST in *. nia.
  - left. rewrite EU, unsigned_lit by lia. ul.
  - exact (proj1 (proj2 (proj2 (proj2 CLX0)))).
  - io_ssp_tac AF_DRV.
  - rewrite EU. exact ST0.
  - rewrite EU. ul.
  - rewrite EU. ul.
  - rewrite EU. apply Z.mod_divide; [lia|]. apply Z.mod_divide in B16; [| lia]. destruct B16 as (q & ->). exists (q - 10). lia.
  - rewrite EU. lia.
  - intros cf1 (Σ1 & Hc1 & LV1 & FRS1 & SP1 & CR1).
    destruct (ASTA_unpack RT Σ1 _ _ cf1 Hc1) as (ms1 & (m1 & RS1 & (ART1 & MI1 & ST1) & PRES1 & LIB1) & Hc1').
    destruct RS1 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & ->).
    rewrite EU in ST1, PRES1.
    rewrite (ret_pc_even 0x90d44) in Hc1' by lia.
    assert (CLX1 : CLX OUT_rep ERR_rep XENV1 LIB so m1)
      by exact (CLX_lib_nw OUT_rep ERR_rep IO_FP XENV1 XENV_FP LIB OUT_loc ERR_loc XENV1_loc LIB_loc IO_img XENV_img
                  _ m m1 _ _ _ CLX0 PRES1 LIB1).
    pose proof (agree_stack_pres_fp _ _ _ _ _ _ PRES1 ltac:(intros x Hx; apply LIB_outside_hi; ul)) as AG1.
    assert (AGD1 : agree_on (fun x => d <= x < d + plen) m m1).
    { destruct (Z.eq_dec plen 0) as [Z0|NZ]; [intros a Ha; lia|].
      rewrite (P1 ltac:(lia)) in *. apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES1). intros x Hx.
      assert (IN : In (owned, plen) (rt_live RT Σ)) by (rewrite LV; unfold tr_live; rewrite (proj2 (Z.eqb_neq plen 0) NZ); left; reflexivity).
      pose proof (af_live_range RT AF Σ m owned plen ART0 IN) as (R1 & R2 & R3).
      split; [right; right; left; exists owned, plen; split; [exact IN| lia]|].
      destruct R3 as [R3|R3]; [| apply LIB_outside_hi; lia].
      apply outside_of_not_in_ranges'. intros (lo1 & hi1 & Hin & Hx1). unfold LIB_FP in Hin.
      destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-; lia. }
    assert (FL1 : rw_cells asegs m1 TR_INIT [C1 (Z_to_bv 8 1)]).
    { apply (rw_cells_agree_nw asegs m m1 _ _ FL0). apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES1). intros x Hx.
      cbn [cells_size csize Nat.add] in Hx. split; [right; left; apply flag_static; lia| apply flag_outside_lib; lia]. }
    assert (HT1 : TCTX RT OUT_rep ERR_rep XENV1 LIB Σ1 so 1 usp buf cap plen d owned payload c0 c1 c2 c3 c4 c5 c6 c7 x0 x1 x2 x3 x4 x5 x6 x7 m1)
      by exact (TCTX_agree_nw RT OUT_rep ERR_rep XENV1 LIB AF Σ Σ1 so so 1 1 usp buf cap plen d owned payload c0 c1 c2 c3 c4 c5 c6 c7
                  x0 x1 x2 x3 x4 x5 x6 x7 m m1 HT ART1 MI1 ST1 SP1 LV1 FRS1 CLX1 AG1 AGD1 FL1).
    (* [comment removed for export] *)
    pose proof (tr_fuzz_ret_walk (usp - 160) gp t0' t1' t2' (Z_to_bv 64 plen) (Z_to_bv 64 d) a1' a2' a3' a4' a5' a6' a7'
                  (Z_to_bv 64 owned) s3 (Z_to_bv 64 k) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) s8 s9 s10 s11 t3' t4' t5' t6' F' fc' m1 lo
                  (Z_to_bv 8 1) ST1 ltac:(ul) ltac:(ul)
                  ltac:(apply Z.mod_divide; [lia|]; apply Z.mod_divide in B16; [| lia]; destruct B16 as (q & ->); exists (q - 10); lia)
                  ltac:(ul) FL1 MI1) as W1.
    lazymatch type of W1 with evt asegs _ ?X =>
      assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
    clear W1.
    apply (cps_realizes asegs _ _ _ _ (asta_evt RT AF Σ1 _ fs _ _ W1') Hc1').
    intros cf2 Hc2.
    destruct (ASTA_unpack RT Σ1 _ _ cf2 Hc2) as (ms2 & (m2 & junk & -> & MU2 & WM2 & MI2 & EF1 & EF2 & EF3 & ST2 & FL2) & Hc2').
    assert (HW2 : forall x, (usp - 240 <= x < usp - 160 -> False) -> (TR_INIT <= x < TR_INIT + 1 -> False) ->
                  outside [(usp - 160 - 80, usp - 160); (TR_INIT, TR_INIT + 1)] x).
    { intros x X1 X2. cbn [outside]. repeat split; try exact I; intros Hx; [apply X1| apply X2]; lia. }
    assert (CLX2 : CLX OUT_rep ERR_rep XENV1 LIB so m2).
    { apply (CLX_munch_latch OUT_rep ERR_rep IO_FP XENV1 XENV_FP LIB OUT_loc ERR_loc XENV1_loc LIB_loc IO_img XENV_img _ m1 m2 _ CLX1 MU2 WM2);
        [| eexists; exact FL2]. intros x Hx Hne. apply HW2; intros Hx'; [ul| lia]. }
    pose proof CLX2 as (OUT2 & ERR2 & _).
    assert (ART2 : ART RT Σ1 m2).
    { apply (af_frame RT AF Σ1 m1 m2 (usp - 160 - 80) ART1); [rewrite SP1; ul| |exact WM2].
      intros a Ha. apply MU2. apply HW2; intros Hx; apply Ha; [left; ul| right; left; apply flag_static; exact Hx]. }
    assert (EU2 : bv_unsigned (Z_to_bv 64 (usp - 160 - 80)) = usp - 160 - 80) by (apply unsigned_lit; ul).
    apply (VPR Σ1 fds0 fs (Z_to_bv 64 0x90e3c) (Z_to_bv 64 (usp - 160 - 80)) gp (Z_to_bv 64 TP_A) t0' t1' t2' (Z_to_bv 64 plen)
             (Z_to_bv 64 d) (Z_to_bv 64 FMT_emit) (Z_to_bv 64 (usp - 160 - 80 + 24)) a2' a3' a4' a5' a6' a7' (Z_to_bv 64 owned)
             (Z_to_bv 64 0) (Z_to_bv 64 TR_BASE) (Z_to_bv 64 k) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) s8 s9 s10 s11 t3' t4' t5' t6' F' fc' m2 so
             (usp - 160 - 80 + 24) lo); try reflexivity; try assumption.
    + rewrite EU2. reflexivity.
    + destruct Hso as [->|(j & Hj & ->)]; [left; reflexivity| right; exists j; split; [lia| reflexivity]].
    + io_ssp_tac AF_DRV.
    + unfold call_ok. rewrite EU2, SP1. split; [exact ST2|]. ul.
    + intros cf3 Hc3.
      destruct (ASTA_unpack RT Σ1 _ _ cf3 Hc3) as (ms3 & (v & m3 & RS3 & (ART3 & MI3 & WM3 & ST3) & PRES3 & OUT3 & ERRP3) & Hc3').
      destruct RS3 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F3 & fc3 & ->).
      rewrite EU2 in ST3, PRES3.
      rewrite (ret_pc_even 0x90e3c) in Hc3' by lia.
      assert (CLX3 : CLX OUT_rep ERR_rep XENV1 LIB (emit0_next so) m3)
        by exact (CLX_io OUT_rep ERR_rep IO_FP XENV1 XENV_FP LIB OUT_loc ERR_loc XENV1_loc LIB_loc IO_img XENV_img
                    _ _ m2 m3 _ _ _ CLX2 PRES3 WM3 OUT3 (ERRP3 ERR2)).
      pose proof (agree_stack_pres_fp _ _ _ _ _ _ PRES3 ltac:(intros x Hx; apply IO_outside_hi; ul)) as AG3.
      assert (EF1' : rw_cells asegs m3 (usp - 160 - 80) [C8 (Z_to_bv 64 (usp - 160 - 80 + 24)); C8 (Z_to_bv 64 0x90d54); CB 8 junk]).
      { apply (rw_cells_agree asegs m2 m3 _ _ EF1); [| exact WM3]. eapply agree_sub; [exact AG3|]. intros x Hx.
        cbn [cells_size csize Nat.add] in Hx. cbv beta. ul. }
      assert (EF2' : rw_cells asegs m3 (usp - 160 - 80 + 24) [C8 (Z_to_bv 64 0)]).
      { apply (rw_cells_agree asegs m2 m3 _ _ EF2); [| exact WM3]. eapply agree_sub; [exact AG3|]. intros x Hx.
        cbn [cells_size csize Nat.add] in Hx. cbv beta. ul. }
      assert (EF3' : rw_cells asegs m3 (usp - 160 - 80 + 32) [C8 a2'; C8 a3'; C8 a4'; C8 a5'; C8 a6'; C8 a7']).
      { apply (rw_cells_agree asegs m2 m3 _ _ EF3); [| exact WM3]. eapply agree_sub; [exact AG3|]. intros x Hx.
        cbn [cells_size csize Nat.add] in Hx. cbv beta. ul. }
      assert (FL3 : rw_cells asegs m3 TR_INIT [C1 (Z_to_bv 8 0)]).
      { apply (rw_cells_agree asegs m2 m3 _ _ FL2); [| exact WM3]. apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES3). intros x Hx.
        cbn [cells_size csize Nat.add] in Hx. split; [right; left; apply flag_static; lia| apply flag_outside_io; lia]. }
      (* [comment removed for export] *)
      pose proof (tr_emit_ret_walk (usp - 160) k gp u0 u1 u2 (Z_to_bv 64 plen) (Z_to_bv 64 d) v b1 b2 b3 b4 b5 b6 b7
                    (Z_to_bv 64 owned) s8 s9 s10 s11 u3 u4 u5 u6 a2' a3' a4' a5' a6' a7'
                    F3 fc3 m3 lo junk ST3 ltac:(ul) ltac:(ul)
                    ltac:(apply Z.mod_divide; [lia|]; apply Z.mod_divide in B16; [| lia]; destruct B16 as (q & ->); exists (q - 10); lia)
                    ltac:(ul) ltac:(lia) EF1' EF2' EF3' FL3 MI3) as W3.
      lazymatch type of W3 with evt asegs _ ?X =>
        assert (W3' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W3) end.
      clear W3.
      apply (cps_realizes asegs _ _ _ _ (asta_evt RT AF Σ1 _ fs _ _ W3') Hc3').
      intros cf4 Hc4. apply Hk.
      destruct (ASTA_unpack RT Σ1 _ _ cf4 Hc4) as (ms4 & (m4 & s3' & Hcase & MU4 & WM4 & MI4 & ST4) & Hc4').
      assert (HW4 : forall x, (TR_INIT <= x < TR_INIT + 1 -> False) -> outside [(TR_INIT, TR_INIT + 1)] x).
      { intros x X1. cbn [outside]. split; [| exact I]. intros Hx. apply X1. lia. }
      assert (ART4 : ART RT Σ1 m4).
      { apply (af_frame RT AF Σ1 m3 m4 (usp - 160) ART3); [rewrite SP1; ul| |exact WM4].
        intros a Ha. apply MU4. apply HW4. intros Hx. apply Ha. right; left. apply flag_static. exact Hx. }
      assert (CLX4 : forall fl, rw_cells asegs m4 TR_INIT [C1 fl] -> CLX OUT_rep ERR_rep XENV1 LIB (emit0_next so) m4).
      { intros fl FL4.
        apply (CLX_munch_latch OUT_rep ERR_rep IO_FP XENV1 XENV_FP LIB OUT_loc ERR_loc XENV1_loc LIB_loc IO_img XENV_img _ m3 m4 _ CLX3 MU4 WM4);
          [| eexists; exact FL4]. intros x Hx Hne. apply HW4. intros Hx'. lia. }
      assert (WM13 : wmono asegs m1 m3) by exact (wmono_trans asegs m1 m2 m3 WM2 WM3).
      assert (AG13 : agree_on (fun x => usp - 160 <= x < USTACK_TOP) m1 m3).
      { apply (agree_trans _ m1 m2 m3).
        - apply (agree_of_munch _ _ _ _ MU2). intros x Hx. apply HW2; intros Hx'; [lia| unfold TR_INIT in Hx'; ul].
        - eapply agree_sub; [exact AG3|]. intros x Hx. cbv beta in *. lia. }
      assert (AG34 : agree_on (fun x => outside [(TR_INIT, TR_INIT + 1)] x) m3 m4) by (apply (agree_of_munch _ _ _ _ MU4); intros x Hx; exact Hx).
      assert (AG14 : agree_on (fun x => usp - 160 <= x < USTACK_TOP) m1 m4).
      { apply (agree_trans _ m1 m3 m4); [exact AG13|]. eapply agree_sub; [exact AG34|]. intros x Hx. apply HW4. intros Hx'. unfold TR_INIT in Hx'. ul. }
      assert (AGD14 : agree_on (fun x => d <= x < d + plen) m1 m4).
      { destruct (Z.eq_dec plen 0) as [Z0|NZ]; [intros a Ha; lia|].
        pose proof HT1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LV1' & _).
        assert (IN : In (owned, plen) (rt_live RT Σ1)) by (rewrite LV1'; unfold tr_live; rewrite (proj2 (Z.eqb_neq plen 0) NZ); left; reflexivity).
        pose proof (af_live_range RT AF Σ1 m1 owned plen ART1 IN) as (R1 & R2 & R3).
        rewrite (P1 ltac:(lia)) in *. apply (agree_trans _ m1 m2 m4); [| apply (agree_trans _ m2 m3 m4)].
        - apply (agree_of_munch _ _ _ _ MU2). intros x Hx. apply HW2; intros Hx'; [ul| unfold TR_INIT, SEGTOP_A in *; lia].
        - apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES3). intros x Hx.
          split; [right; right; left; exists owned, plen; split; [exact IN| lia]|].
          destruct R3 as [R3|R3]; [| apply IO_outside_hi; lia].
          apply outside_of_not_in_ranges'. intros Hin. pose proof (client_static_range _ (proj1 (IO_img _ Hin))). lia.
        - eapply agree_sub; [exact AG34|]. intros x Hx. apply HW4. intros Hx'. unfold TR_INIT, SEGTOP_A in *. lia. }
      assert (HT4 : forall fl, rw_cells asegs m4 TR_INIT [C1 (Z_to_bv 8 fl)] ->
                TCTX RT OUT_rep ERR_rep XENV1 LIB Σ1 (emit0_next so) fl usp buf cap plen d owned payload
                     c0 c1 c2 c3 c4 c5 c6 c7 x0 x1 x2 x3 x4 x5 x6 x7 m4).
      { intros fl FL4.
        apply (TCTX_agree RT OUT_rep ERR_rep XENV1 LIB AF Σ1 Σ1 so (emit0_next so) 1 fl usp buf cap plen d owned payload
                 c0 c1 c2 c3 c4 c5 c6 c7 x0 x1 x2 x3 x4 x5 x6 x7 m1 m4 HT1 ART4 MI4 (wmono_trans asegs m1 m3 m4 WM13 WM4));
          try reflexivity; try assumption.
        - rewrite SP1. exact ST4.
        - exact (CLX4 _ FL4). }
      destruct Hcase as [(K1 & -> & FL4)|(K1 & -> & FL4)].
      * left. split; [exact K1|].
        exists Σ1, plen, d, owned, payload, gp, u0, u1, u2, b2, b3, b4, b5, b6, b7, s3', s8, s9, s10, s11.
        exists u3, u4, u5, u6, c0, c1, c2, c3, c4, c5, c6, c7, F3, fc3, m4.
        split; [exact Hc4'|]. split; [exact (HT4 1 FL4)|]. split; [lia|]. unfold FUZZ_COST in *. nia.
      * right. split; [exact K1|].
        exists Σ1, plen, d, owned, payload, gp, u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, s3', s8, s9, s10, s11.
        exists u3, u4, u5, u6, c0, c1, c2, c3, c4, c5, c6, c7, F3, fc3, m4.
        split; [exact Hc4'| exact (HT4 0 FL4)].
Qed.

End Tr2.
