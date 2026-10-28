(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac ImageA Nodes RzCPS NodesA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim Canon Stdio Prog.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface D_iface D_defs D_kit D_auxv D_libiface D_clx D_rlkit X_aexdefs D_aex D_trpro D_trwalk D_trdefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

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
Hypothesis XENV_loc : xenv_laws XENV XENV_FP.
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

Theorem tr_iter : forall k so usp buf cap x0 x1 x2 x3 x4 x5 x6 x7, (so = stdout_init \/ exists j, (j < 499)%nat /\ so = so_lines j) ->
  cpsE bsegs (TLOOP RT OUT_rep ERR_rep XENV LIB fs k so usp buf cap x0 x1 x2 x3 x4 x5 x6 x7) (evw 1 (emit0_out so))
    (fun c => (1 < k /\ TLOOP RT OUT_rep ERR_rep XENV LIB fs (k - 1) (emit0_next so) usp buf cap x0 x1 x2 x3 x4 x5 x6 x7 c)
              \/ (k = 1 /\ TFREE RT OUT_rep ERR_rep XENV LIB fs (emit0_next so) usp buf cap x0 x1 x2 x3 x4 x5 x6 x7 c)).
Proof using AF AF_DRV FUZZ VPR OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img.
  intros k so usp buf cap x0 x1 x2 x3 x4 x5 x6 x7 Hso T c HL Hk.
  destruct HL as (Σ & plen & d & owned & payload & x1r & gp & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s3
                  & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7
                  & F & fc & m & FRM & HA & HT & Hk14 & HCR).
  pose proof HT as (ART0 & MI0 & CLX0 & FR0 & TF0 & ST0 & B16 & ULO & USP0 & SPW & LV & FRS & PL & PB & BD & P0 & P1 & CAP0 & UT0).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  set (lo := rt_sp0 RT Σ - STACK_WIN) in *.
  assert (EU : bv_unsigned (Z_to_bv 64 (usp - 160)) = usp - 160) by (apply unsigned_lit; ul).
  assert (DPOS : 0 < d /\ ((exists p n, In (p, n) (rt_live RT Σ) /\ p <= d /\ d + Z.of_nat (length payload) <= p + n) \/ (payload = [] /\ d < SEGTOP_A))).
  { destruct (Z.eq_dec plen 0) as [Z0|NZ].
    - destruct (P0 Z0) as [-> _]. split; [unfold TR_EMPTY; lia|]. right. split; [destruct payload; [reflexivity| cbn in PL; lia]| unfold TR_EMPTY, SEGTOP_A; lia].
    - rewrite (P1 ltac:(lia)).
      assert (IN : In (owned, plen) (rt_live RT Σ)) by (rewrite LV; unfold tr_live; rewrite (proj2 (Z.eqb_neq plen 0) NZ); left; reflexivity).
      pose proof (af_live_range RT AF Σ m owned plen ART0 IN) as (R1 & _).
      split; [lia|]. left. exists owned, plen. split; [exact IN| lia]. }

  assert (DOUT : forall x, d <= x < d + plen -> in_live (rt_live RT Σ) x /\ ~ (0x10000 <= x < SEGTOP_A)).
  { intros x Hx. destruct (Z.eq_dec plen 0) as [Z0|NZ]; [lia|]. rewrite (P1 ltac:(lia)) in Hx.
    assert (IN : In (owned, plen) (rt_live RT Σ)) by (rewrite LV; unfold tr_live; rewrite (proj2 (Z.eqb_neq plen 0) NZ); left; reflexivity).
    pose proof (af_live_range RT AF Σ m owned plen ART0 IN) as (R1 & R2 & R3).
    split; [exists owned, plen; split; [exact IN| lia]| unfold SEGTOP_A in *; lia]. }

  pose proof CLX0 as (OUT0 & ERR0 & XE0 & LIB0 & _).
  destruct (xenv_open XENV XENV_FP XENV_loc m XE0) as [CORE0 AEX0].
  pose proof (aexA_flag0 m AEX0) as FL0.
  assert (INCBX : in_ranges XENV_FP AEF_INCB) by (apply (xl_aex_in XENV_loc); rewrite in_AEX_FPA_iff; right; right; right; reflexivity).
  pose proof (XENV_img _ INCBX) as (INCB_cs & INCB_nd & INCB_nio & INCB_nlib).

  pose proof (tr_head_walk (usp - 160) x1r gp t0 t1 t2 (Z_to_bv 64 plen) (Z_to_bv 64 d) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 owned) s3 (Z_to_bv 64 k)
                (Z_to_bv 64 0) (Z_to_bv 64 (-2)) s8 s9 s10 s11 t3 t4 t5 t6 F fc m 0 FL0 MI0) as W0.
  lazymatch type of W0 with evt bsegs _ ?X =>
    assert (W0' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W0) end.
  clear W0.
  apply (cps_realizes bsegs _ _ _ c (asta_evt RT AF Σ _ fs _ _ W0') HA).
  intros cf0 Hc0.
  destruct (ASTA_unpack RT Σ _ _ cf0 Hc0) as (ms0 & (m1 & -> & MUh & WMh & MIh & FL1) & Hc0').
  assert (ART1 : ART RT Σ m1).
  { apply (af_frame RT AF Σ m m1 (usp - 160) ART0); [ul| |exact WMh].
    intros a Ha. apply MUh. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. right; left.
    replace (bv_unsigned a) with AEF_INCB by (unfold AEF_INCB in *; lia). exact INCB_cs. }
  assert (LIB1 : LIB m1).
  { apply (LIB_loc m m1 LIB0). apply (agree_ranges_sub _ _ _ _ (agree_of_munch _ _ _ (fun x => in_ranges LIB_FP x) MUh ltac:(intros x Hx; cbn; split; [| exact I];
      intros Hin; apply (not_in_ranges_of_outside _ _ INCB_nlib); replace AEF_INCB with x by (unfold AEF_INCB in *; lia); exact Hx))). intros x Hx; exact Hx. }
  assert (SSP1 : io_ssp m1).
  { pose proof CLX0 as (_ & _ & _ & _ & (g & SG) & _). exists g. split; [exact (proj1 (proj2 (AF_DRV Σ m1 ART1)))|].
    apply (ro_cells_agree bsegs m m1 _ _ SG). apply (agree_of_munch _ _ _ _ MUh). intros x Hx. cbn in Hx |- *. split; [| exact I].
    intros Hin. apply INCB_nd. unfold drv_cell. replace AEF_INCB with x by (unfold AEF_INCB in *; lia). right; left. exact Hx. }
  assert (NL1 : libc_nl m1).
  { destruct (xl_libc XENV_loc m CORE0) as (cdt & thr & sec & tm1 & LC).
    apply (libc_nl_agree m m1 (libc_nl_of_libc m cdt thr sec tm1 LC)). apply (agree_of_munch _ _ _ _ MUh).
    intros x Hx. cbn in Hx |- *. split; [| exact I]. intros Hin. exfalso. unfold AEF_INCB, LIBC_NL in *. lia. }
  assert (ST1 : stk bsegs m1 lo (usp - 160)).
  { apply (stk_agree bsegs m m1 _ _ ST0); [| exact WMh]. apply (agree_of_munch _ _ _ _ MUh). intros x Hx. cbn. split; [unfold AEF_INCB; ul| exact I]. }
  assert (BD1 : bytes_at bsegs m1 d payload).
  { apply (bytes_at_agree bsegs m m1 _ _ BD). apply (agree_of_munch _ _ _ _ MUh). intros x Hx. rewrite <- PL in Hx. cbn. split; [| exact I].
    pose proof (DOUT x Hx) as [_ NO]. pose proof (client_static_range _ INCB_cs). unfold AEF_INCB in *. lia. }

  assert (AGCh : agree_on auxc m m1).
  { apply (auxc_of_munch _ _ _ MUh). intros x Hx. pose proof (auxc_range x Hx). cbn. split; [unfold AEF_INCB; lia| exact I]. }
  assert (AUX1 : el_auxvA (bv_unsigned (Z_to_bv 64 (usp - 160))) m1).
  { rewrite EU. destruct FR0 as [_ AUX0]. apply (el_auxv_weaken usp); [| lia].
    apply (el_auxv_agree usp m m1 AUX0 AGCh). apply (agree_of_munch _ _ _ _ MUh). intros x Hx. cbn. split; [unfold AEF_INCB; ul| exact I]. }
  assert (GAP1 : rt_sp0 RT Σ <= bv_unsigned (Z_to_bv 64 (usp - 160)) + FUZZ_SP0GAP) by (rewrite EU; unfold FUZZ_SP0GAP in *; lia).
  assert (XD1 : el_xdataA m1).
  { apply (el_xdata_agree m m1 (xl_xdata XENV_loc m CORE0)). apply (agree_of_munch _ _ _ _ MUh).
    intros x Hx. cbv beta in Hx. cbn. split; [unfold AEF_INCB; lia| exact I]. }
  unfold entry_st in Hc0'.
  apply (FUZZ Σ (PMfd fds0 fs) (Z_to_bv 64 0xae544) (Z_to_bv 64 (usp - 160)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 plen)
           (Z_to_bv 64 d) (Z_to_bv 64 d) (Z_to_bv 64 plen) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 owned) s3 (Z_to_bv 64 TR_LATCH)
           (Z_to_bv 64 k) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 d payload lo); try reflexivity; try assumption.
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
  - rewrite EU. exact ST1.
  - rewrite EU. ul.
  - rewrite EU. ul.
  - rewrite EU. apply Z.mod_divide; [lia|]. apply Z.mod_divide in B16; [| lia]. destruct B16 as (q & ->). exists (q - 10). lia.
  - rewrite EU. lia.
  - split; [exact Hc0'| exact (asta_cfrm0 RT Σ _ _ cf0 Hc0' ltac:(intros ms0 <-; exact FRM))].
  - intros cf1 ((Σ1 & Hc1 & LV1 & FRS1 & SP1 & CR1) & FC1).
    destruct (ASTA_unpack RT Σ1 _ _ cf1 Hc1) as (ms1 & (m2 & RS1 & (ART2 & MI2 & ST2) & PRES2 & LIB2) & Hc1').
    destruct RS1 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & ->).
    assert (FRM' : frm0 fc') by (pose proof (asta_eq_fcsr RT Σ1 _ _ cf1 Hc1') as EFC; change (ms_fcsr (cfg_ms cf1) = fc') in EFC; rewrite <- EFC; exact FC1).
    rewrite EU in ST2, PRES2.
    rewrite (ret_pc_even 0xae544) in Hc1' by lia.
    assert (FL2 : rw_cells bsegs m2 AEF_INCB [C1 (Z_to_bv 8 1)]).
    { apply (rw_cells_agree_nw bsegs m1 m2 _ _ FL1). apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES2). intros x Hx. cbn in Hx.
      replace x with AEF_INCB by (unfold AEF_INCB in *; lia). split; [right; left; exact INCB_cs| exact INCB_nlib]. }

    pose proof (tr_fuzz_ret_walk (usp - 160) gp t0' t1' t2' (Z_to_bv 64 plen) (Z_to_bv 64 d) a1' a2' a3' a4' a5' a6' a7'
                  (Z_to_bv 64 owned) s3 (Z_to_bv 64 k) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) s8 s9 s10 s11 t3' t4' t5' t6' F' fc' m2 lo 1 ST2
                  ltac:(ul) ltac:(ul) ltac:(apply Z.mod_divide; [lia|]; apply Z.mod_divide in B16; [| lia]; destruct B16 as (q & ->); exists (q - 10); lia)
                  ltac:(ul) FL2 MI2) as W1.
    lazymatch type of W1 with evt bsegs _ ?X =>
      assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
    clear W1.
    apply (cps_realizes bsegs _ _ _ _ (asta_evt RT AF Σ1 _ fs _ _ W1') Hc1').
    intros cf2 Hc2.
    destruct (ASTA_unpack RT Σ1 _ _ cf2 Hc2) as (ms2 & (m3 & junk & -> & MU3 & WM3 & MI3 & EF1 & EF2 & EF3 & ST3 & FL3) & Hc2').

    assert (CLX3 : CLX OUT_rep ERR_rep XENV LIB so m3).
    { apply (CLX_lib_flag OUT_rep ERR_rep IO_FP XENV XENV_FP LIB OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img so m m3 CLX0); [| | exact FL3].
      - apply (agree_trans _ m m1 m3); [| apply (agree_trans _ m1 m2 m3)].
        + apply (agree_of_munch _ _ _ _ MUh). intros x [_ NE]. cbn. split; [unfold AEF_INCB in *; lia| exact I].
        + apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES2). intros x [[Hx|[Hx|Hx]] _].
          * split; [right; left; exact (proj1 (IO_img x Hx))| exact (proj2 (proj2 (IO_img x Hx)))].
          * split; [right; left; exact (proj1 (XENV_img x Hx))| exact (proj2 (proj2 (proj2 (XENV_img x Hx))))].
          * split; [right; left; exact (drv_cell_static x Hx)| exact (drv_cell_not_lib x Hx)].
        + apply (agree_of_munch _ _ _ _ MU3). intros x [Hx NE]. cbn.
          assert (CS : 0x10000 <= x < SEGTOP_A).
          { destruct Hx as [Hx|[Hx|Hx]]; [exact (client_static_range _ (proj1 (IO_img x Hx)))| exact (client_static_range _ (proj1 (XENV_img x Hx)))| exact (client_static_range _ (drv_cell_static x Hx))]. }
          split; [ul|]. split; [unfold AEF_INCB in *; lia| exact I].
      - apply (LIB_loc m2 m3 LIB2). intros a Ha. apply MU3. cbn. pose proof (client_static_range _ (proj1 (LIB_img _ Ha))) as CS.
        split; [ul|]. split; [| exact I]. intros Hin. apply (not_in_ranges_of_outside _ _ INCB_nlib). replace AEF_INCB with (bv_unsigned a) by (unfold AEF_INCB in *; lia). exact Ha. }
    pose proof CLX3 as (OUT3 & ERR3 & _).
    assert (ART3 : ART RT Σ1 m3).
    { apply (af_frame RT AF Σ1 m2 m3 (usp - 160 - 80) ART2); [rewrite SP1; ul| |exact WM3].
      intros a Ha. apply MU3. cbn [outside]. split; [intros Hin; apply Ha; left; ul|]. split; [| exact I].
      intros Hin. apply Ha. right; left. replace (bv_unsigned a) with AEF_INCB by (unfold AEF_INCB in *; lia). exact INCB_cs. }
    assert (EU2 : bv_unsigned (Z_to_bv 64 (usp - 160 - 80)) = usp - 160 - 80) by (apply unsigned_lit; ul).
    apply (VPR Σ1 fds0 fs (Z_to_bv 64 0xae63c) (Z_to_bv 64 (usp - 160 - 80)) gp (Z_to_bv 64 TP_A) t0' t1' t2' (Z_to_bv 64 plen)
             (Z_to_bv 64 d) (Z_to_bv 64 FMT_emit) (Z_to_bv 64 (usp - 160 - 80 + 24)) a2' a3' a4' a5' a6' a7' (Z_to_bv 64 owned)
             (Z_to_bv 64 0) (Z_to_bv 64 TR_LATCH) (Z_to_bv 64 k) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) s8 s9 s10 s11 t3' t4' t5' t6' F' fc' m3 so
             (usp - 160 - 80 + 24) lo); try reflexivity; try assumption.
    + rewrite EU2. reflexivity.
    + destruct Hso as [->|(j & Hj & ->)]; [left; reflexivity| right; exists j; split; [lia| reflexivity]].
    + io_ssp_tac AF_DRV.
    + unfold call_ok. rewrite EU2, SP1. split; [exact ST3|]. ul.
    + intros cf3 Hc3.
      destruct (ASTA_unpack RT Σ1 _ _ cf3 Hc3) as (ms3 & (v & m4 & RS3 & (ART4 & MI4 & WM4 & ST4) & PRES4 & OUT4 & ERRP4) & Hc3').
      destruct RS3 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F3 & fc3 & -> & FRM3).
      rewrite EU2 in ST4, PRES4.
      rewrite (ret_pc_even 0xae63c) in Hc3' by lia.
      assert (CLX4 : CLX OUT_rep ERR_rep XENV LIB (emit0_next so) m4)
        by exact (CLX_io OUT_rep ERR_rep IO_FP XENV XENV_FP LIB OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img
                    _ _ m3 m4 _ _ _ CLX3 PRES4 WM4 OUT4 (ERRP4 ERR3)).
      pose proof (agree_stack_pres_fp _ _ _ _ _ _ PRES4 ltac:(intros x Hx; apply IO_outside_hi; ul)) as AG4.
      assert (EF1' : rw_cells bsegs m4 (usp - 160 - 80) [C8 (Z_to_bv 64 (usp - 160 - 80 + 24)); C8 (Z_to_bv 64 0xae554); CB 8 junk]).
      { apply (rw_cells_agree bsegs m3 m4 _ _ EF1); [| exact WM4]. eapply agree_sub; [exact AG4|]. intros x Hx.
        cbn [cells_size csize Nat.add] in Hx. cbv beta. ul. }
      assert (EF2' : rw_cells bsegs m4 (usp - 160 - 80 + 24) [C8 (Z_to_bv 64 0)]).
      { apply (rw_cells_agree bsegs m3 m4 _ _ EF2); [| exact WM4]. eapply agree_sub; [exact AG4|]. intros x Hx.
        cbn [cells_size csize Nat.add] in Hx. cbv beta. ul. }
      assert (EF3' : rw_cells bsegs m4 (usp - 160 - 80 + 32) [C8 a2'; C8 a3'; C8 a4'; C8 a5'; C8 a6'; C8 a7']).
      { apply (rw_cells_agree bsegs m3 m4 _ _ EF3); [| exact WM4]. eapply agree_sub; [exact AG4|]. intros x Hx.
        cbn [cells_size csize Nat.add] in Hx. cbv beta. ul. }

      pose proof (tr_emit_ret_walk (usp - 160) k gp u0 u1 u2 (Z_to_bv 64 plen) (Z_to_bv 64 d) v b1 b2 b3 b4 b5 b6 b7
                    (Z_to_bv 64 owned) (Z_to_bv 64 0) s8 s9 s10 s11 u3 u4 u5 u6 a2' a3' a4' a5' a6' a7'
                    F3 fc3 m4 lo junk ST4 ltac:(ul) ltac:(ul)
                    ltac:(apply Z.mod_divide; [lia|]; apply Z.mod_divide in B16; [| lia]; destruct B16 as (q & ->); exists (q - 10); lia)
                    ltac:(ul) ltac:(lia) EF1' EF2' EF3' MI4) as W3.
      lazymatch type of W3 with evt bsegs _ ?X =>
        assert (W3' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W3) end.
      clear W3.
      apply (cps_realizes bsegs _ _ _ _ (asta_evt RT AF Σ1 _ fs _ _ W3') Hc3').
      intros cf4 Hc4. apply Hk.
      destruct (ASTA_unpack RT Σ1 _ _ cf4 Hc4) as (ms4 & (Hcase & ST5) & Hc4').
      assert (AG04 : agree_on (fun x => usp - 160 <= x < USTACK_TOP) m m4).
      { apply (agree_trans _ m m1 m4); [| apply (agree_trans _ m1 m2 m4); [| apply (agree_trans _ m2 m3 m4)]].
        - apply (agree_of_munch _ _ _ _ MUh). intros x Hx. cbn. split; [unfold AEF_INCB; ul| exact I].
        - apply (agree_stack_pres_fp _ _ _ _ _ _ PRES2). intros x Hx. apply LIB_outside_hi. ul.
        - apply (agree_of_munch _ _ _ _ MU3). intros x Hx. cbn. split; [lia|]. split; [unfold AEF_INCB; ul| exact I].
        - eapply agree_sub; [exact AG4|]. intros x Hx. cbv beta in *. lia. }
      assert (AGD04 : agree_on (fun x => d <= x < d + plen) m m4).
      { destruct (Z.eq_dec plen 0) as [Z0|NZ]; [intros a Ha; lia|].
        assert (IN : In (owned, plen) (rt_live RT Σ)) by (rewrite LV; unfold tr_live; rewrite (proj2 (Z.eqb_neq plen 0) NZ); left; reflexivity).
        pose proof (af_live_range RT AF Σ m owned plen ART0 IN) as (R1 & R2 & R3).
        rewrite (P1 ltac:(lia)) in *.
        apply (agree_trans _ m m1 m4); [| apply (agree_trans _ m1 m2 m4); [| apply (agree_trans _ m2 m3 m4)]].
        - apply (agree_of_munch _ _ _ _ MUh). intros x Hx. cbn. split; [| exact I]. pose proof (DOUT x Hx) as [_ NO]. pose proof (client_static_range _ INCB_cs). unfold AEF_INCB in *. lia.
        - apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES2). intros x Hx.
          split; [right; right; left; exists owned, plen; split; [exact IN| lia]|].
          destruct R3 as [R3|R3]; [| apply LIB_outside_hi; lia].
          apply outside_of_not_in_ranges'. intros (lo1 & hi1 & Hin & Hx1). unfold LIB_FP in Hin.
          repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
        - apply (agree_of_munch _ _ _ _ MU3). intros x Hx. cbn. split; [ul|]. split; [| exact I]. pose proof (DOUT x Hx) as [_ NO]. pose proof (client_static_range _ INCB_cs). unfold AEF_INCB in *. lia.
        - apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES4). intros x Hx. rewrite LV1.
          split; [right; right; left; exists owned, plen; split; [exact IN| lia]|].
          destruct R3 as [R3|R3]; [| apply IO_outside_hi; lia].
          apply outside_of_not_in_ranges'. intros Hin. pose proof (client_static_range _ (proj1 (IO_img _ Hin))). lia. }
      assert (AGC04 : agree_on auxc m m4).
      { apply (agree_on_auxc_trans m m1 m4 AGCh). apply (agree_on_auxc_trans m1 m2 m4); [| apply (agree_on_auxc_trans m2 m3 m4)].
        - exact (auxc_of_pres_fp _ _ _ _ _ _ PRES2 auxc_outside_LIB).
        - apply (auxc_of_munch _ _ _ MU3). intros x Hx. pose proof (auxc_range x Hx). cbn. repeat split; try exact I; unfold AEF_INCB in *; ul.
        - apply (auxc_of_pres_fp _ _ _ _ _ _ PRES4). intros x Hx. apply outside_of_not_in_ranges'. intros Hin. exact (proj1 (proj2 (IO_img x Hin)) (auxc_drv x Hx)). }
      assert (HT4 : TCTX RT OUT_rep ERR_rep XENV LIB Σ1 (emit0_next so) usp buf cap plen d owned payload
                      c0 c1 c2 c3 c4 c5 c6 c7 x0 x1 x2 x3 x4 x5 x6 x7 m4).
      { apply (TCTX_agree_nw RT OUT_rep ERR_rep XENV LIB AF Σ Σ1 so (emit0_next so) usp buf cap plen d owned payload
                 c0 c1 c2 c3 c4 c5 c6 c7 x0 x1 x2 x3 x4 x5 x6 x7 m m4 HT ART4 MI4); try reflexivity; try assumption; rewrite ?SP1; assumption. }
      destruct Hcase as [(K1 & ->)|(K1 & ->)].
      * left. split; [exact K1|].
        exists Σ1, plen, d, owned, payload, (Z_to_bv 64 0xae554), gp, u0, u1, u2, v, b1, b2, b3, b4, b5, b6, b7, (Z_to_bv 64 (-1)), s8, s9, s10, s11.
        exists u3, u4, u5, u6, c0, c1, c2, c3, c4, c5, c6, c7, F3, fc3, m4. split; [exact FRM3|].
        split; [exact Hc4'|]. split; [exact HT4|]. split; [lia|]. unfold FUZZ_COST in *. nia.
      * right. split; [exact K1|].
        exists Σ1, plen, d, owned, payload, gp, u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, (Z_to_bv 64 (-1)), (Z_to_bv 64 (-2)), s8, s9, s10, s11.
        exists u3, u4, u5, u6, c0, c1, c2, c3, c4, c5, c6, c7, F3, fc3, m4.
        split; [exact Hc4'| exact HT4].
Qed.

End Tr2.
