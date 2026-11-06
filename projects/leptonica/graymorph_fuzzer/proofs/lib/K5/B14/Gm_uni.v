(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import Tac RzCPS NodesA SysStep Arr StoreFast.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.B14 Require Import ImageA Layout RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit D_iface D_defs
  Lept_iface Lept_lits Lept_env LeptC_kit LeptL_kit Gm_iface Gm_ropkit LeptB_guard LeptB_guard2 GmB_kit GmB_uni_loop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
(* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
(* [comment removed for export] *)
Local Ltac tlia ::= sf_clear_big;
              first [ sf_unhide; unpark_all; zify_prune_sub; Zify.zify; xlia zchecker
                    | Zify.zify; xlia zchecker
                    | sf_unhide;
                      first [ zify_prune_neg; Zify.zify; xlia zchecker
                            | zify_prune_plain; Zify.zify; xlia zchecker
                            | Zify.zify; xlia zchecker ] ].
Ltac dedup_ro := repeat match goal with H1 : ro_cells asegs ?m ?a ?c, H2 : ro_cells asegs ?m ?a ?c |- _ => clear H2 end.
Ltac drop_acc a := repeat match goal with H : acc asegs _ a _ |- _ => clear H end.
Section UNI.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis GM : gm_gaps RT.
Hypothesis RC : rt_contracts RT.

Theorem rasteropUniLow_ok : rasteropUniLow_cps RT.
Proof using AF GP GM.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    datad w h wpl dx dy dw dh op
    FDO MST -> -> -> -> -> -> -> -> -> SARGS OP RD RCD ENV.
  unfold lpost, lenv, keeps, keepsL, raster8, rect_in, chunk in *.
  destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RD as ((DIN & D0 & D16 & DSZ) & DW & DH & DWPL & DCAP).
  destruct RCD as (RD1 & RD2 & RD3 & RD4 & RD5 & RD6).
  pose proof (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_rasteropUniLow, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a /\ outside [(datad, datad + 4 * (wpl * h))] a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  pose proof ST as (STa & STb & _).
  chunk_facts RT AF GP datad (4 * (wpl * h)).
  pose proof (gm_acc_lmask32 RT GM Σ m ART0) as ACCL. unfold GM_LMASK32 in ACCL.
  pose proof (gm_acc_rmask32 RT GM Σ m ART0) as ACCR. unfold GM_RMASK32 in ACCR.
  refresh RT AF. unfold shad, SHB in *. park_disj.
  assert (BD : 0 <= dx /\ 0 <= dy /\ 0 < dw /\ 0 < dh /\ dx + dw <= w /\ dy + dh <= h /\ w <= 20000 /\ h <= 20000) by lia.
  hide BD.
  dedup_ro. drop_acc datad.
  unfold hid in BD.
  walk_to AF MST [(usp - 64, usp); (datad, datad + 4 * (wpl * h))] [0xa2690].
  rewrite ?Z.add_0_r.
  lstep.
  change 31 with (Z.ones 5). rewrite (Z.land_ones (dx * 8) 5) by lia. change (2^5) with 32.
  set (xb := (dx * 8) mod 32) in *.
  assert (XBR : 0 <= xb < 32) by (unfold xb; apply Z.mod_pos_bound; lia).
  lstep.
  brfork XB0.
  - (* [comment removed for export] *)
    lstep.
    change 31 with (Z.ones 5). rewrite (Z.land_ones (dw * 8) 5) by lia. change (2^5) with 32.
    set (lw := (dw * 8) mod 32) in *.
    assert (LWR : 0 <= lw < 32) by (unfold lw; apply Z.mod_pos_bound; lia).
    lstep.
    merge3 0xa27c4 (Z_to_bv 5 7) (Z_to_bv 5 12) (Z_to_bv 5 29).
    { brfork LW0.
      - merge_done.
      - awalk [0xa27a0].
        lazymatch goal with MIx : mem_inv asegs ?mm |- evt _ _ (MS ?R _ _ _ _ ?mm _) =>
          destruct (lmask_bytes mm MIx) as (rbs & RB & RBL);
          destruct (bytes_at_read4w mm 0x26460 rbs (lw * 4) RB ltac:(clear - LWR; lia) ltac:(rewrite RBL; clear - LWR; lia)) as (wm & RM) end.
        lstep. clear RM RB.
        awalk [0xa27c4]. merge_done. }
    assert (WPLB : 0 < wpl <= 5001) by (clear - BD DWPL; subst wpl; Z.div_mod_to_equations; lia).
    assert (BD2 : 0 <= dy * wpl /\ dy * wpl + dh * wpl <= wpl * h /\ wpl * h <= 16777216).
    { clear - BD WPLB DCAP.
      pose proof (Z.mul_nonneg_nonneg dy wpl ltac:(lia) ltac:(lia)) as N1.
      pose proof (Z.mul_le_mono_nonneg_r (dy + dh) h wpl ltac:(lia) ltac:(lia)) as N3.
      rewrite Z.mul_add_distr_r in N3. rewrite (Z.mul_comm h wpl) in N3. lia. }
    assert (FWD : 0 <= dx * 8 / 32 <= 5000 /\ 0 <= dw * 8 / 32 <= 5000) by (clear - BD; split; split; try (apply Z.div_pos; lia); apply Z.div_le_upper_bound; lia).
    assert (NB : (0 <= dx /\ 0 <= dy /\ 0 < dw /\ 0 < dh /\ dx + dw <= w /\ dy + dh <= h /\ w <= 20000 /\ h <= 20000)
              /\ (0 <= dy * wpl /\ dy * wpl + dh * wpl <= wpl * h /\ wpl * h <= 16777216) /\ 0 < wpl <= 5001
              /\ (0 <= dx * 8 / 32 <= 5000 /\ 0 <= dw * 8 / 32 <= 5000) /\ 0 < datad /\ datad + 4 * (wpl * h) <= 140737488355328).
    { repeat split; try (clear - BD; lia); try (clear - BD2; lia); try (clear - WPLB; lia); try (clear - FWD; lia); try assumption; lia. }
    hide NB.
    bwalk [0xa281c] NB.
    destruct OP as [OP0|OP15]; subst op.
    2:{ (* [comment removed for export] *)
      bwalk [0xa2e94] NB.
      cnb NB.
      rewrite !(srliw5_small (dw * 8)) by (clear - NB; unfold hid in *; lia).
      set (nfw := dw * 8 / 32) in *.
      replace (Z.land datad 3) with 0 by (symmetry; change 3 with (Z.ones 2); rewrite Z.land_ones by lia; change (2 ^ 2) with 4; clear - D16; Z.div_mod_to_equations; lia).
      (* [comment removed for export] *)
      lazymatch goal with MUx : munch ?W m ?mm, WMx : wmono asegs m ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (ARTn : ART RT Σ mm)
          by (apply (art_client_writes RT AF Σ m mm lo W ART0 MUx WMx); [unfold STACK_WIN; lia|
              cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists datad, (4 * (wpl * h)); split; [exact DIN| lia]| exact I]]]);
        pose proof (af_acc_live RT AF Σ mm datad (4 * (wpl * h)) ARTn DIN) as (WRD & ACCD) end.
      apply wr_at_rw_CB in WRD; [| clear - DSZ; lia]. destruct WRD as (dbs & DBC).
      pose proof DBC as [[[DBL _] _] _]. cbn in DBL. apply u8arr_of_rw_cells in DBC.
      lazymatch type of DBC with u8arr _ ?mm _ _ =>
        destruct (u8arr_u32arr mm datad dbs (wpl * h) DBC ltac:(rewrite DBL; clear - DSZ; lia)) as (wsd & UAD & UADL) end.
      clear DBC DBL.
      assert (HD0 : lw = 0 -> dx * 8 / 32 + dw * 8 / 32 <= wpl) by (clear - BD DWPL XB0; unfold lw, xb in *; subst wpl; intros; Z.div_mod_to_equations; lia).
      assert (HD1 : lw <> 0 -> dx * 8 / 32 + dw * 8 / 32 + 1 <= wpl) by (clear - BD DWPL XB0; unfold lw, xb in *; subst wpl; intros; Z.div_mod_to_equations; lia).
      assert (PRD : dy * wpl + (dh - 1) * wpl + wpl <= wpl * h) by (clear - BD2; rewrite Z.mul_sub_distr_r; lia).
      eapply evt_cut.
      { eapply (usr_rows (Z.to_nat dh) 0) with (datad := datad) (ld := wpl * h) (wpl := wpl) (doff := dy * wpl + dx * 8 / 32) (dh := dh) (dwb := dw * 8) (nfw := nfw) (lw := lw) (ws := wsd).
        all: lazymatch goal with
             | |- u32arr _ _ _ _ => eassumption
             | |- mem_inv _ _ => assumption
             | |- acc _ _ _ _ => assumption
             | |- Z.of_nat (length _) = _ => assumption
             | |- _ => idtac
             end.
        all: unfold parked in *.
        all: lazymatch goal with
             | |- _ = (_ * 8) mod 32 => reflexivity
             | |- _ = _ / 32 => reflexivity
             | |- _ mod 8 = 0 => clear - D16; Z.div_mod_to_equations; lia
             | |- _ => idtac
             end.
        all: unfold SEGTOP_A, nfw in *; clear - BD BD2 WPLB HD0 HD1 PRD FWD LWR D0 D16 CKR CKS CKH SP0R SP0W LOW LOR USP SPT; intros; lia. }

      intros ms' PO. unfold usr_exit in PO.
      destruct PO as (ra' & t0' & t1' & t2' & s0' & s1' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & s3' & s4' & s5' & s6'
                      & t3' & t4' & t5' & t6' & m' & ws' & -> & MU' & WM' & MI' & UAD' & UADL').
      clear ARTn ACCD.
      loop_art RT AF Σ m' lo MU'
        ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists datad, (4 * (wpl * h)); split; [solve [in_live_tac]| lia]| exact I]]).
      clear UAD' UADL' UAD UADL.
      lazymatch type of MU' with munch _ ?mm m' =>
        loop_transport mm m' MU' ltac:(fun Hx => clear - Hx CKR CKS CKH LOW LOR SPT SPB STa USP SP0R SP0W; unfold parked in *; lia) end.
      clear MU' WM'.
      cwalk (@nil Z).
      cps_stop.
      agf_munch AGF MU ltac:(fun Hx => cbn [outside]; let P := fresh "P" in pose proof (PFS _ Hx) as P; destruct Hx as [_ HxO]; cbn [outside] in HxO;
                                       clear - P HxO LOR; split; [lia| split; [tauto| exact I]]).
      apply cps_finish. intros c Hc. subst QF. cbv beta.
      exists Σ. eexists.
      split; [| repeat split; first [reflexivity | lia]].
      eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists. split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
      split; [split; [split; [exact ARTl| split; [exact MI'| split; [| assumption]]]| split; assumption]|].
      - repeat match goal with H : wmono asegs _ _ |- _ => revert H end. clear. intros. eauto using wmono_trans.
      - intros a Ha Ho. exact (AGF a (conj Ha Ho)).
    }
    { (* [comment removed for export] *)
      bwalk [0xa2f98] NB.
      cnb NB.
      rewrite !(srliw5_small (dw * 8)) by (clear - NB; unfold hid in *; lia).
      set (nfw := dw * 8 / 32) in *.
      replace (Z.land datad 3) with 0 by (symmetry; change 3 with (Z.ones 2); rewrite Z.land_ones by lia; change (2 ^ 2) with 4; clear - D16; Z.div_mod_to_equations; lia).
      (* [comment removed for export] *)
      lazymatch goal with MUx : munch ?W m ?mm, WMx : wmono asegs m ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (ARTn : ART RT Σ mm)
          by (apply (art_client_writes RT AF Σ m mm lo W ART0 MUx WMx); [unfold STACK_WIN; lia|
              cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists datad, (4 * (wpl * h)); split; [exact DIN| lia]| exact I]]]);
        pose proof (af_acc_live RT AF Σ mm datad (4 * (wpl * h)) ARTn DIN) as (WRD & ACCD) end.
      apply wr_at_rw_CB in WRD; [| clear - DSZ; lia]. destruct WRD as (dbs & DBC).
      pose proof DBC as [[[DBL _] _] _]. cbn in DBL. apply u8arr_of_rw_cells in DBC.
      lazymatch type of DBC with u8arr _ ?mm _ _ =>
        destruct (u8arr_u32arr mm datad dbs (wpl * h) DBC ltac:(rewrite DBL; clear - DSZ; lia)) as (wsd & UAD & UADL) end.
      clear DBC DBL.
      assert (HD0 : lw = 0 -> dx * 8 / 32 + dw * 8 / 32 <= wpl) by (clear - BD DWPL XB0; unfold lw, xb in *; subst wpl; intros; Z.div_mod_to_equations; lia).
      assert (HD1 : lw <> 0 -> dx * 8 / 32 + dw * 8 / 32 + 1 <= wpl) by (clear - BD DWPL XB0; unfold lw, xb in *; subst wpl; intros; Z.div_mod_to_equations; lia).
      assert (PRD : dy * wpl + (dh - 1) * wpl + wpl <= wpl * h) by (clear - BD2; rewrite Z.mul_sub_distr_r; lia).
      eapply evt_cut.
      { eapply (ucr_rows (Z.to_nat dh) 0) with (datad := datad) (ld := wpl * h) (wpl := wpl) (doff := dy * wpl + dx * 8 / 32) (dh := dh) (dwb := dw * 8) (nfw := nfw) (lw := lw) (ws := wsd).
        all: lazymatch goal with
             | |- u32arr _ _ _ _ => eassumption
             | |- mem_inv _ _ => assumption
             | |- acc _ _ _ _ => assumption
             | |- Z.of_nat (length _) = _ => assumption
             | |- _ => idtac
             end.
        all: unfold parked in *.
        all: lazymatch goal with
             | |- _ = (_ * 8) mod 32 => reflexivity
             | |- _ = _ / 32 => reflexivity
             | |- _ mod 8 = 0 => clear - D16; Z.div_mod_to_equations; lia
             | |- _ => idtac
             end.
        all: unfold SEGTOP_A, nfw in *; clear - BD BD2 WPLB HD0 HD1 PRD FWD LWR D0 D16 CKR CKS CKH SP0R SP0W LOW LOR USP SPT; intros; lia. }
      intros ms' PO. unfold ucr_exit in PO.
      destruct PO as (ra' & t0' & t1' & t2' & s0' & s1' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & s3' & s4' & s5' & s6'
                      & t3' & t4' & t5' & t6' & m' & ws' & -> & MU' & WM' & MI' & UAD' & UADL').
      clear ARTn ACCD.
      loop_art RT AF Σ m' lo MU'
        ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists datad, (4 * (wpl * h)); split; [solve [in_live_tac]| lia]| exact I]]).
      clear UAD' UADL' UAD UADL.
      lazymatch type of MU' with munch _ ?mm m' =>
        loop_transport mm m' MU' ltac:(fun Hx => clear - Hx CKR CKS CKH LOW LOR SPT SPB STa USP SP0R SP0W; unfold parked in *; lia) end.
      clear MU' WM'.
      cwalk (@nil Z).
      cps_stop.
      agf_munch AGF MU ltac:(fun Hx => cbn [outside]; let P := fresh "P" in pose proof (PFS _ Hx) as P; destruct Hx as [_ HxO]; cbn [outside] in HxO;
                                       clear - P HxO LOR; split; [lia| split; [tauto| exact I]]).
      apply cps_finish. intros c Hc. subst QF. cbv beta.
      exists Σ. eexists.
      split; [| repeat split; first [reflexivity | lia]].
      eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists. split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
      split; [split; [split; [exact ARTl| split; [exact MI'| split; [| assumption]]]| split; assumption]|].
      - repeat match goal with H : wmono asegs _ _ |- _ => revert H end. clear. intros. eauto using wmono_trans.
      - intros a Ha Ho. exact (AGF a (conj Ha Ho)).


    }
  - (* [comment removed for export] *)
    assert (XBN : 1 <= xb <= 31) by (clear - XBR XB0; lia).
    assert (WPLB : 0 < wpl <= 5001) by (clear - BD DWPL; subst wpl; Z.div_mod_to_equations; lia).
    assert (BD2 : 0 <= dy * wpl /\ dy * wpl + dh * wpl <= wpl * h /\ wpl * h <= 16777216).
    { clear - BD WPLB DCAP.
      pose proof (Z.mul_nonneg_nonneg dy wpl ltac:(lia) ltac:(lia)) as N1.
      pose proof (Z.mul_le_mono_nonneg_r (dy + dh) h wpl ltac:(lia) ltac:(lia)) as N3.
      rewrite Z.mul_add_distr_r in N3. rewrite (Z.mul_comm h wpl) in N3. lia. }
    assert (FWD : 0 <= dx * 8 / 32 <= 5000 /\ 0 <= dw * 8 / 32 <= 5000) by (clear - BD; split; split; try (apply Z.div_pos; lia); apply Z.div_le_upper_bound; lia).
    assert (NB : (0 <= dx /\ 0 <= dy /\ 0 < dw /\ 0 < dh /\ dx + dw <= w /\ dy + dh <= h /\ w <= 20000 /\ h <= 20000)
              /\ (0 <= dy * wpl /\ dy * wpl + dh * wpl <= wpl * h /\ wpl * h <= 16777216) /\ 0 < wpl <= 5001
              /\ (0 <= dx * 8 / 32 <= 5000 /\ 0 <= dw * 8 / 32 <= 5000) /\ 0 < datad /\ datad + 4 * (wpl * h) <= 140737488355328 /\ 1 <= xb <= 31).
    { repeat split; try (clear - BD; lia); try (clear - BD2; lia); try (clear - WPLB; lia); try (clear - FWD; lia); try (clear - XBN; lia); try assumption; lia. }
    hide NB.
    bwalk [0xa271c] NB.
    lazymatch goal with MIx : mem_inv asegs ?mm |- evt _ _ (MS ?R _ _ _ _ ?mm _) =>
      destruct (rmask32_bytes mm MIx) as (rbs & RB & RBL);
      destruct (bytes_at_read4w mm 0x263a0 rbs ((32 - xb) * 4) RB ltac:(clear - XBN; lia) ltac:(rewrite RBL; clear - XBN; lia)) as (fm & RM) end.
    lstep. clear RM RB RBL rbs.
    bwalk [0xa2724] NB.
    cnb NB.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ ?F0 _ ?fc0 None ?mcur _) =>
      assert (EPI : forall (ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' t3' t4' t5' t6' : word) (mE : mem),
        munch [(datad, datad + 4 * (wpl * h))] mcur mE -> wmono asegs mcur mE -> mem_inv asegs mE ->
        evt asegs (fun ms' => cps asegs (ASTA RT Σ PMc (eq ms')) QF)
          (MS (mkR ra' (Z_to_bv 64 (usp + -64)) gp (Z_to_bv 64 TP_A) t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7'
                   s2' s3' s4' s5' s6' s7 s8 s9 s10 s11 t3' t4' t5' t6')
              F0 (Z_to_bv 64 0xa2e30) fc0 None mE (seg_rom asegs))) end.
    { intros ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' t3' t4' t5' t6' mE MUE WME MIE.
      loop_art RT AF Σ mE lo MUE
        ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists datad, (4 * (wpl * h)); split; [solve [in_live_tac]| lia]| exact I]]).
      lazymatch type of MUE with munch _ ?mm mE =>
        loop_transport mm mE MUE ltac:(fun Hx => clear - Hx CKR CKS CKH LOW LOR SPT SPB STa USP SP0R SP0W; unfold parked in *; lia) end.
      clear MUE WME.
      cwalk (@nil Z).
      cps_stop.
      agf_munch AGF MU ltac:(fun Hx => cbn [outside]; let P := fresh "P" in pose proof (PFS _ Hx) as P; destruct Hx as [_ HxO]; cbn [outside] in HxO;
                                       clear - P HxO LOR; split; [lia| split; [tauto| exact I]]).
      apply cps_finish. intros c Hc. subst QF. cbv beta.
      exists Σ. eexists.
      split; [| repeat split; first [reflexivity | lia]].
      eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists. split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
      split; [split; [split; [exact ARTl| split; [exact MIE| split; [| assumption]]]| split; assumption]|].
      - repeat match goal with H : wmono asegs _ _ |- _ => revert H end. clear. intros. eauto using wmono_trans.
      - intros a Ha Ho. exact (AGF a (conj Ha Ho)). }
    pose (dnf := (dw * 8 - (32 - xb)) / 32). pose (dlw := (dw * 8 + dx * 8) mod 32). pose (fw := dx * 8 / 32).
    assert (GF1 : fw + 1 <= wpl) by (clear - BD DWPL; unfold fw; subst wpl; Z.div_mod_to_equations; lia).
    assert (GF2 : 32 - xb <= dw * 8 -> fw + 1 + dnf <= wpl) by (clear - BD DWPL XBN; unfold fw, dnf, xb in *; subst wpl; intros; Z.div_mod_to_equations; lia).
    assert (GF2b : 32 - xb <= dw * 8 -> 0 <= dnf <= 5000) by (clear - BD XBN; unfold dnf, xb in *; intros; Z.div_mod_to_equations; lia).
    assert (GF3 : 32 - xb <= dw * 8 -> dlw <> 0 -> fw + 1 + dnf + 1 <= wpl) by (clear - BD DWPL XBN; unfold fw, dnf, dlw, xb in *; subst wpl; intros; Z.div_mod_to_equations; lia).
    assert (DLWR : 0 <= dlw < 32) by (unfold dlw; apply Z.mod_pos_bound; lia).
    (* [comment removed for export] *)
    lazymatch goal with MUx : munch ?W m ?mm, WMx : wmono asegs m ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (ARTn : ART RT Σ mm)
        by (apply (art_client_writes RT AF Σ m mm lo W ART0 MUx WMx); [unfold STACK_WIN; lia|
            cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists datad, (4 * (wpl * h)); split; [exact DIN| lia]| exact I]]]);
      pose proof (af_acc_live RT AF Σ mm datad (4 * (wpl * h)) ARTn DIN) as (WRD & ACCD) end.
    apply wr_at_rw_CB in WRD; [| clear - DSZ; lia]. destruct WRD as (dbs & DBC).
    pose proof DBC as [[[DBL _] _] _]. cbn in DBL. apply u8arr_of_rw_cells in DBC.
    lazymatch type of DBC with u8arr _ ?mm _ _ =>
      destruct (u8arr_u32arr mm datad dbs (wpl * h) DBC ltac:(rewrite DBL; clear - DSZ; lia)) as (wsd & UAD & UADL) end.
    clear DBC DBL.
    destruct OP as [OP0|OP15]; subst op.
    2:{ (* [comment removed for export] *)
      lstep.
      lazymatch goal with |- evt _ _ (MS _ ?F0 _ ?fc0 None ?mm _) =>
        eapply (evt_cut asegs (fun ms' => exists (v_t0 v_s0 v_a2 v_a5 v_a6 v_a7 v_t4 v_t5 : word),
          ms' = MS (mkR ra (Z_to_bv 64 (usp + -64)) gp (Z_to_bv 64 TP_A) v_t0 (Z_to_bv 64 2147450880) (Z_to_bv 64 dh) v_s0 s1
                        (Z_to_bv 64 (dx * 8 / 32 * 4 + (wpl * dy * 4 + datad))) (Z_to_bv 64 (wpl * 4)) v_a2 (Z_to_bv 64 dh) (Z_to_bv 64 0) v_a5 v_a6 v_a7
                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (dx * 8 / 32 * 4 + (wpl * dy * 4 + datad))) v_t4 v_t5 (Z_to_bv 64 dh))
                   F0 (Z_to_bv 64 0xa2a50) fc0 None mm (seg_rom asegs)
          /\ (v_t5 = Z_to_bv 64 1 \/ (v_t5 = Z_to_bv 64 0 /\ v_a6 = Z_to_bv 64 dnf /\ v_a7 = Z_to_bv 64 (dx * 8 / 32 * 4 + (wpl * dy * 4 + datad) + 4) /\ 32 <= dw * 8 - (32 - xb)))
          /\ (v_t0 = Z_to_bv 64 1 \/ (v_t0 = Z_to_bv 64 0 /\ v_a2 = Z_to_bv 64 (dx * 8 / 32 * 4 + (wpl * dy * 4 + datad) + 4 + dnf * 4) /\ dlw <> 0 /\ 32 - xb <= dw * 8)))) end.
      {
        destruct (Z.ltb_spec (dw * 8) (32 - xb)) as [DP|NDP].
        { (* [comment removed for export] *)
          brF.
          lstep.
          rewrite (swrap32_modadd (dw * 8 - (32 - xb)) 32) by (clear - NB DP; unfold hid in *; lia).
          bwalk [0xa2764] NB. cnb NB.
          lazymatch goal with MIx : mem_inv asegs ?mm |- evt _ _ (MS ?R _ _ _ _ ?mm _) =>
            reg_val (Z_to_bv 5 10) ltac:(fun v => lazymatch v with Z_to_bv 64 (156768 + ?kk) =>
              destruct (lmask_bytes mm MIx) as (rbs & RB & RBL);
              destruct (bytes_at_read4w mm 0x26460 rbs kk RB ltac:(clear - NB DP; unfold hid in *; lia) ltac:(rewrite RBL; clear - NB DP; unfold hid in *; lia)) as (lm & RM) end) end.
          lstep. clear RM RB RBL rbs.
          bwalk [0xa2950] NB. cnb NB.
          replace (Z.b2z (dw * 8 <? 32 - xb)) with 1 by (symmetry; destruct (Z.ltb_spec (dw * 8) (32 - xb)); [reflexivity| lia]).
          lazymatch goal with |- context [Z.lor 1 (Z.b2z ?c)] => replace (Z.lor 1 (Z.b2z c)) with 1 by (destruct c; reflexivity) end.
          lstep. brF.
          bwalk [0xa2a50] NB. cnb NB.
          rewrite ?(slt0_nonneg wpl) by (clear - WPLB; lia). cbn [Z.b2z].
          apply evt_done. do 8 eexists. split; [reflexivity|]. split; [left; reflexivity| left; reflexivity].
        }
        brT.
        bwalk [0xa27ac] NB. cnb NB.
        rewrite !(srliw5_small (dw * 8 - (32 - xb))) by (clear - NB NDP; unfold hid in *; lia).
        fold dnf.
        lstep.
        destruct (Z.ltb_spec (dw * 8 - (32 - xb)) 32) as [NOFULL|FULL].
        { (* [comment removed for export] *)
          assert (DNF0 : dnf = 0) by (unfold dnf; apply Z.div_small; lia).
          brT.
          bwalk [0xa2950] NB. cnb NB.
          replace (Z.land (dx * 8 + dw * 8) 31) with dlw by (unfold dlw; change 31 with (Z.ones 5); rewrite Z.land_ones by lia; f_equal; lia).
          replace (Z.b2z (dw * 8 <? 32 - xb)) with 0 by (symmetry; destruct (Z.ltb_spec (dw * 8) (32 - xb)); [lia| reflexivity]).
          destruct (Z.eq_dec dlw 0) as [DLW0|DLWN].
          { replace (Z.b2z (dlw <? 1)) with 1 by (symmetry; destruct (Z.ltb_spec dlw 1); [reflexivity| lia]).
            change (Z.lor 0 1) with 1.
            lstep. brF.
            bwalk [0xa2a50] NB. cnb NB.
            rewrite ?(slt0_nonneg wpl) by (clear - WPLB; lia). cbn [Z.b2z].
            apply evt_done. do 8 eexists. split; [reflexivity|]. split; [left; reflexivity| left; reflexivity].
          }
          replace (Z.b2z (dlw <? 1)) with 0 by (symmetry; destruct (Z.ltb_spec dlw 1); [lia| reflexivity]).
          change (Z.lor 0 0) with 0.
          lstep. brT.
          bwalk [0xa2a24] NB. cnb NB.
          lazymatch goal with MIx : mem_inv asegs ?mm |- evt _ _ (MS ?R _ _ _ _ ?mm _) =>
            destruct (lmask_bytes mm MIx) as (rbs & RB & RBL);
            destruct (bytes_at_read4w mm 0x26460 rbs (dlw * 4) RB ltac:(clear - DLWR; lia) ltac:(rewrite RBL; clear - DLWR; lia)) as (lm & RM) end.
          lstep. clear RM RB RBL rbs.
          bwalk [0xa2a50] NB. cnb NB.
          rewrite ?(slt0_nonneg wpl) by (clear - WPLB; lia). cbn [Z.b2z].
          apply evt_done. do 8 eexists. split; [reflexivity|]. split; [left; reflexivity| right; split; [reflexivity| split; [reflexivity| split; [exact DLWN| exact NDP]]]].
        }
        assert (DNF1 : 1 <= dnf <= 5000) by (pose proof (GF2b NDP); unfold dnf in *; split; [apply Z.div_le_lower_bound; lia| lia]).
        brF.
        bwalk [0xa2950] NB. cnb NB.
        replace (Z.land (dx * 8 + dw * 8) 31) with dlw by (unfold dlw; change 31 with (Z.ones 5); rewrite Z.land_ones by lia; f_equal; lia).
        replace (Z.b2z (dw * 8 <? 32 - xb)) with 0 by (symmetry; destruct (Z.ltb_spec (dw * 8) (32 - xb)); [lia| reflexivity]).
        destruct (Z.eq_dec dlw 0) as [DLW0|DLWN].
        { replace (Z.b2z (dlw <? 1)) with 1 by (symmetry; destruct (Z.ltb_spec dlw 1); [reflexivity| lia]).
          change (Z.lor 0 1) with 1.
          lstep. brF.
          bwalk [0xa2a50] NB. cnb NB.
          rewrite ?(slt0_nonneg wpl) by (clear - WPLB; lia). cbn [Z.b2z].
          apply evt_done. do 8 eexists. split; [reflexivity|]. split; [right; split; [reflexivity| split; [reflexivity| split; [reflexivity| exact FULL]]]| left; reflexivity].
        }
        replace (Z.b2z (dlw <? 1)) with 0 by (symmetry; destruct (Z.ltb_spec dlw 1); [lia| reflexivity]).
        change (Z.lor 0 0) with 0.
        lstep. brT.
        bwalk [0xa2a24] NB. cnb NB.
        lazymatch goal with MIx : mem_inv asegs ?mm |- evt _ _ (MS ?R _ _ _ _ ?mm _) =>
          destruct (lmask_bytes mm MIx) as (rbs & RB & RBL);
          destruct (bytes_at_read4w mm 0x26460 rbs (dlw * 4) RB ltac:(clear - DLWR; lia) ltac:(rewrite RBL; clear - DLWR; lia)) as (lm & RM) end.
        lstep. clear RM RB RBL rbs.
        bwalk [0xa2a50] NB. cnb NB.
        rewrite ?(slt0_nonneg wpl) by (clear - WPLB; lia). cbn [Z.b2z].
        apply evt_done. do 8 eexists. split; [reflexivity|]. split; [right; split; [reflexivity| split; [reflexivity| split; [reflexivity| exact FULL]]]| right; split; [reflexivity| split; [reflexivity| split; [exact DLWN| exact NDP]]]].
      }
      intros ms' (v_t0 & v_s0 & v_a2 & v_a5 & v_a6 & v_a7 & v_t4 & v_t5 & -> & GC & GL).
      eapply evt_cut.
      { eapply (ug1s_rows (Z.to_nat dh) (dy * wpl + fw)) with (datad := datad) (ws := wsd) (ld := wpl * h) (wpl := wpl); try eassumption.
        all: unfold parked in *.
        all: try assumption.
        all: rewrite ?Z2Nat.id by (clear - BD; lia); rewrite ?Z.mul_sub_distr_r;
             unfold fw in *; clear - BD BD2 FWD GF1 D16 CKR SP0R WPLB; first [lia | (Z.div_mod_to_equations; lia)]. }
      intros ms' PO1. unfold ug1s_exit in PO1.
      destruct PO1 as (x1 & x2 & x3 & x4 & x5 & mA & wsA & -> & MU1 & WM1 & MI1 & UAD1 & UADL1 & ACCD1).
      unfold SHB in *.
      lstep.
      destruct GC as [V5|(V5 & V6 & V7 & FULL)].
      { (* [comment removed for export] *)
        subst v_t5. brT.
        (* [comment removed for export] *)
        lstep.
        destruct GL as [V0|(V0 & V2 & DLWN & NDPL)].
        { subst v_t0. brT.
          bwalk [0xa2e30] NB.
          eapply EPI; [exact MU1| exact WM1| exact MI1]. }
        subst v_t0 v_a2.
        first [brT | brF].
        bwalk [0xa2d28] NB. cnb NB.
        eapply evt_cut.
        { eapply (ug3s_rows (Z.to_nat dh) (dy * wpl + fw + 1 + dnf)) with (datad := datad) (ws := wsA) (ld := wpl * h) (wpl := wpl); try eassumption.
          all: unfold parked in *.
          all: try assumption.
          all: rewrite ?Z2Nat.id by (clear - BD; lia); rewrite ?Z.mul_sub_distr_r;
               pose proof (GF2 NDPL) as GF2'; pose proof (GF3 NDPL DLWN) as GF3'; pose proof (GF2b NDPL) as GF2b';
               unfold fw in *; clear - BD BD2 FWD GF1 GF2' GF3' GF2b' D16 CKR SP0R WPLB; first [lia | (Z.div_mod_to_equations; lia)]. }
        intros ms' PO3. unfold ug3s_exit in PO3.
        destruct PO3 as (z1 & z2 & z3 & z4 & z5 & mC & wsC & -> & MU3 & WM3 & MI3 & UAD3 & UADL3 & ACCD3).
        eapply EPI; [exact (munch_trans _ _ _ _ MU1 MU3)| exact (wmono_trans asegs _ _ _ WM1 WM3)| exact MI3].
      }
      (* [comment removed for export] *)
      subst v_t5 v_a6 v_a7. brF.
      assert (NDP : 32 - xb <= dw * 8) by (clear - FULL; lia).
      assert (DNF1 : 1 <= dnf <= 5000) by (pose proof (GF2b NDP); unfold dnf in *; split; [apply Z.div_le_lower_bound; lia| lia]).
      bwalk [0xa2c84] NB. cnb NB.
      replace (Z.land (dx * 8 / 32 * 4 + (wpl * dy * 4 + datad) + 4) 3) with 0
        by (symmetry; change 3 with (Z.ones 2); rewrite Z.land_ones by lia; change (2 ^ 2) with 4; clear - D16; Z.div_mod_to_equations; lia).
      change (Z.b2z (0 <? 1)) with 1. cbn [Z.b2z Z.ltb Z.eqb Z.compare].
      eapply evt_cut.
      { eapply (ug2s_rows (Z.to_nat dh) (dy * wpl + fw + 1)) with (datad := datad) (ws := wsA) (ld := wpl * h) (wpl := wpl) (n := dnf) (dh := dh); try eassumption.
        all: unfold parked in *.
        all: try assumption.
        all: rewrite ?Z2Nat.id by (clear - BD; lia); rewrite ?Z.mul_sub_distr_r;
             pose proof (GF2 NDP) as GF2';
             unfold fw in *; clear - BD BD2 FWD GF1 GF2' DNF1 D16 CKR SP0R WPLB; first [lia | (Z.div_mod_to_equations; lia)]. }
      intros ms' PO2. unfold ug2s_exit in PO2.
      destruct PO2 as (y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & mB & wsB & -> & MU2 & WM2 & MI2 & UAD2 & UADL2 & ACCD2).
      unfold SHB in *.
      pose proof (munch_trans _ _ _ _ MU1 MU2) as MU12. pose proof (wmono_trans asegs _ _ _ WM1 WM2) as WM12.
      (* [comment removed for export] *)
      lstep.
      destruct GL as [V0|(V0 & V2 & DLWN & NDPL)].
      { subst v_t0. brT.
        bwalk [0xa2e30] NB.
        eapply EPI; [exact MU12| exact WM12| exact MI2]. }
      subst v_t0 v_a2.
      first [brT | brF].
      bwalk [0xa2d28] NB. cnb NB.
      eapply evt_cut.
      { eapply (ug3s_rows (Z.to_nat dh) (dy * wpl + fw + 1 + dnf)) with (datad := datad) (ws := wsB) (ld := wpl * h) (wpl := wpl); try eassumption.
        all: unfold parked in *.
        all: try assumption.
        all: rewrite ?Z2Nat.id by (clear - BD; lia); rewrite ?Z.mul_sub_distr_r;
             pose proof (GF2 NDPL) as GF2'; pose proof (GF3 NDPL DLWN) as GF3'; pose proof (GF2b NDPL) as GF2b';
             unfold fw in *; clear - BD BD2 FWD GF1 GF2' GF3' GF2b' D16 CKR SP0R WPLB; first [lia | (Z.div_mod_to_equations; lia)]. }
      intros ms' PO3. unfold ug3s_exit in PO3.
      destruct PO3 as (z1 & z2 & z3 & z4 & z5 & mC & wsC & -> & MU3 & WM3 & MI3 & UAD3 & UADL3 & ACCD3).
      eapply EPI; [exact (munch_trans _ _ _ _ MU12 MU3)| exact (wmono_trans asegs _ _ _ WM12 WM3)| exact MI3].
    }
    { (* [comment removed for export] *)
      lstep.
      lazymatch goal with |- evt _ _ (MS _ ?F0 _ ?fc0 None ?mm _) =>
        eapply (evt_cut asegs (fun ms' => exists (v_t0 v_s0 v_a2 v_a5 v_a6 v_a7 v_t4 v_t5 : word),
          ms' = MS (mkR ra (Z_to_bv 64 (usp + -64)) gp (Z_to_bv 64 TP_A) v_t0 (Z_to_bv 64 2147450880) (Z_to_bv 64 dh) v_s0 s1
                        (Z_to_bv 64 (dx * 8 / 32 * 4 + (wpl * dy * 4 + datad))) (Z_to_bv 64 (wpl * 4)) v_a2 (Z_to_bv 64 dh) (Z_to_bv 64 0) v_a5 v_a6 v_a7
                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (dx * 8 / 32 * 4 + (wpl * dy * 4 + datad))) v_t4 v_t5 (Z_to_bv 64 dh))
                   F0 (Z_to_bv 64 0xa2988) fc0 None mm (seg_rom asegs)
          /\ (v_t5 = Z_to_bv 64 1 \/ (v_t5 = Z_to_bv 64 0 /\ v_a6 = Z_to_bv 64 dnf /\ v_a7 = Z_to_bv 64 (dx * 8 / 32 * 4 + (wpl * dy * 4 + datad) + 4) /\ 32 <= dw * 8 - (32 - xb)))
          /\ (v_t0 = Z_to_bv 64 1 \/ (v_t0 = Z_to_bv 64 0 /\ v_a2 = Z_to_bv 64 (dx * 8 / 32 * 4 + (wpl * dy * 4 + datad) + 4 + dnf * 4) /\ dlw <> 0 /\ 32 - xb <= dw * 8)))) end.
      {
        destruct (Z.ltb_spec (dw * 8) (32 - xb)) as [DP|NDP].
        { (* [comment removed for export] *)
          brF.
          lstep.
          rewrite (swrap32_modadd (dw * 8 - (32 - xb)) 32) by (clear - NB DP; unfold hid in *; lia).
          bwalk [0xa2764] NB. cnb NB.
          lazymatch goal with MIx : mem_inv asegs ?mm |- evt _ _ (MS ?R _ _ _ _ ?mm _) =>
            reg_val (Z_to_bv 5 10) ltac:(fun v => lazymatch v with Z_to_bv 64 (156768 + ?kk) =>
              destruct (lmask_bytes mm MIx) as (rbs & RB & RBL);
              destruct (bytes_at_read4w mm 0x26460 rbs kk RB ltac:(clear - NB DP; unfold hid in *; lia) ltac:(rewrite RBL; clear - NB DP; unfold hid in *; lia)) as (lm & RM) end) end.
          lstep. clear RM RB RBL rbs.
          bwalk [0xa2950] NB. cnb NB.
          replace (Z.b2z (dw * 8 <? 32 - xb)) with 1 by (symmetry; destruct (Z.ltb_spec (dw * 8) (32 - xb)); [reflexivity| lia]).
          lazymatch goal with |- context [Z.lor 1 (Z.b2z ?c)] => replace (Z.lor 1 (Z.b2z c)) with 1 by (destruct c; reflexivity) end.
          lstep. brF.
          bwalk [0xa2988] NB. cnb NB.
          rewrite ?(slt0_nonneg wpl) by (clear - WPLB; lia). cbn [Z.b2z].
          apply evt_done. do 8 eexists. split; [reflexivity|]. split; [left; reflexivity| left; reflexivity].
        }
        brT.
        bwalk [0xa27ac] NB. cnb NB.
        rewrite !(srliw5_small (dw * 8 - (32 - xb))) by (clear - NB NDP; unfold hid in *; lia).
        fold dnf.
        lstep.
        destruct (Z.ltb_spec (dw * 8 - (32 - xb)) 32) as [NOFULL|FULL].
        { (* [comment removed for export] *)
          assert (DNF0 : dnf = 0) by (unfold dnf; apply Z.div_small; lia).
          brT.
          bwalk [0xa2950] NB. cnb NB.
          replace (Z.land (dx * 8 + dw * 8) 31) with dlw by (unfold dlw; change 31 with (Z.ones 5); rewrite Z.land_ones by lia; f_equal; lia).
          replace (Z.b2z (dw * 8 <? 32 - xb)) with 0 by (symmetry; destruct (Z.ltb_spec (dw * 8) (32 - xb)); [lia| reflexivity]).
          destruct (Z.eq_dec dlw 0) as [DLW0|DLWN].
          { replace (Z.b2z (dlw <? 1)) with 1 by (symmetry; destruct (Z.ltb_spec dlw 1); [reflexivity| lia]).
            change (Z.lor 0 1) with 1.
            lstep. brF.
            bwalk [0xa2988] NB. cnb NB.
            rewrite ?(slt0_nonneg wpl) by (clear - WPLB; lia). cbn [Z.b2z].
            apply evt_done. do 8 eexists. split; [reflexivity|]. split; [left; reflexivity| left; reflexivity].
          }
          replace (Z.b2z (dlw <? 1)) with 0 by (symmetry; destruct (Z.ltb_spec dlw 1); [lia| reflexivity]).
          change (Z.lor 0 0) with 0.
          lstep. brT.
          bwalk [0xa2a24] NB. cnb NB.
          lazymatch goal with MIx : mem_inv asegs ?mm |- evt _ _ (MS ?R _ _ _ _ ?mm _) =>
            destruct (lmask_bytes mm MIx) as (rbs & RB & RBL);
            destruct (bytes_at_read4w mm 0x26460 rbs (dlw * 4) RB ltac:(clear - DLWR; lia) ltac:(rewrite RBL; clear - DLWR; lia)) as (lm & RM) end.
          lstep. clear RM RB RBL rbs.
          bwalk [0xa2988] NB. cnb NB.
          rewrite ?(slt0_nonneg wpl) by (clear - WPLB; lia). cbn [Z.b2z].
          apply evt_done. do 8 eexists. split; [reflexivity|]. split; [left; reflexivity| right; split; [reflexivity| split; [reflexivity| split; [exact DLWN| exact NDP]]]].
        }
        assert (DNF1 : 1 <= dnf <= 5000) by (pose proof (GF2b NDP); unfold dnf in *; split; [apply Z.div_le_lower_bound; lia| lia]).
        brF.
        bwalk [0xa2950] NB. cnb NB.
        replace (Z.land (dx * 8 + dw * 8) 31) with dlw by (unfold dlw; change 31 with (Z.ones 5); rewrite Z.land_ones by lia; f_equal; lia).
        replace (Z.b2z (dw * 8 <? 32 - xb)) with 0 by (symmetry; destruct (Z.ltb_spec (dw * 8) (32 - xb)); [lia| reflexivity]).
        destruct (Z.eq_dec dlw 0) as [DLW0|DLWN].
        { replace (Z.b2z (dlw <? 1)) with 1 by (symmetry; destruct (Z.ltb_spec dlw 1); [reflexivity| lia]).
          change (Z.lor 0 1) with 1.
          lstep. brF.
          bwalk [0xa2988] NB. cnb NB.
          rewrite ?(slt0_nonneg wpl) by (clear - WPLB; lia). cbn [Z.b2z].
          apply evt_done. do 8 eexists. split; [reflexivity|]. split; [right; split; [reflexivity| split; [reflexivity| split; [reflexivity| exact FULL]]]| left; reflexivity].
        }
        replace (Z.b2z (dlw <? 1)) with 0 by (symmetry; destruct (Z.ltb_spec dlw 1); [lia| reflexivity]).
        change (Z.lor 0 0) with 0.
        lstep. brT.
        bwalk [0xa2a24] NB. cnb NB.
        lazymatch goal with MIx : mem_inv asegs ?mm |- evt _ _ (MS ?R _ _ _ _ ?mm _) =>
          destruct (lmask_bytes mm MIx) as (rbs & RB & RBL);
          destruct (bytes_at_read4w mm 0x26460 rbs (dlw * 4) RB ltac:(clear - DLWR; lia) ltac:(rewrite RBL; clear - DLWR; lia)) as (lm & RM) end.
        lstep. clear RM RB RBL rbs.
        bwalk [0xa2988] NB. cnb NB.
        rewrite ?(slt0_nonneg wpl) by (clear - WPLB; lia). cbn [Z.b2z].
        apply evt_done. do 8 eexists. split; [reflexivity|]. split; [right; split; [reflexivity| split; [reflexivity| split; [reflexivity| exact FULL]]]| right; split; [reflexivity| split; [reflexivity| split; [exact DLWN| exact NDP]]]].
      }
      intros ms' (v_t0 & v_s0 & v_a2 & v_a5 & v_a6 & v_a7 & v_t4 & v_t5 & -> & GC & GL).
      eapply evt_cut.
      { eapply (ug1c_rows (Z.to_nat dh) (dy * wpl + fw)) with (datad := datad) (ws := wsd) (ld := wpl * h) (wpl := wpl); try eassumption.
        all: unfold parked in *.
        all: try assumption.
        all: rewrite ?Z2Nat.id by (clear - BD; lia); rewrite ?Z.mul_sub_distr_r;
             unfold fw in *; clear - BD BD2 FWD GF1 D16 CKR SP0R WPLB; first [lia | (Z.div_mod_to_equations; lia)]. }
      intros ms' PO1. unfold ug1c_exit in PO1.
      destruct PO1 as (x1 & x2 & x3 & x4 & x5 & mA & wsA & -> & MU1 & WM1 & MI1 & UAD1 & UADL1 & ACCD1).
      unfold SHB in *.
      lstep.
      destruct GC as [V5|(V5 & V6 & V7 & FULL)].
      { (* [comment removed for export] *)
        subst v_t5. brT.
        (* [comment removed for export] *)
        lstep.
        destruct GL as [V0|(V0 & V2 & DLWN & NDPL)].
        { subst v_t0. brF.
          bwalk [0xa2e30] NB.
          eapply EPI; [exact MU1| exact WM1| exact MI1]. }
        subst v_t0 v_a2.
        first [brT | brF].
        bwalk [0xa3070] NB. cnb NB.
        eapply evt_cut.
        { eapply (ug3c_rows (Z.to_nat dh) (dy * wpl + fw + 1 + dnf)) with (datad := datad) (ws := wsA) (ld := wpl * h) (wpl := wpl); try eassumption.
          all: unfold parked in *.
          all: try assumption.
          all: rewrite ?Z2Nat.id by (clear - BD; lia); rewrite ?Z.mul_sub_distr_r;
               pose proof (GF2 NDPL) as GF2'; pose proof (GF3 NDPL DLWN) as GF3'; pose proof (GF2b NDPL) as GF2b';
               unfold fw in *; clear - BD BD2 FWD GF1 GF2' GF3' GF2b' D16 CKR SP0R WPLB; first [lia | (Z.div_mod_to_equations; lia)]. }
        intros ms' PO3. unfold ug3c_exit in PO3.
        destruct PO3 as (z1 & z2 & z3 & z4 & z5 & mC & wsC & -> & MU3 & WM3 & MI3 & UAD3 & UADL3 & ACCD3).
        eapply EPI; [exact (munch_trans _ _ _ _ MU1 MU3)| exact (wmono_trans asegs _ _ _ WM1 WM3)| exact MI3].
      }
      (* [comment removed for export] *)
      subst v_t5 v_a6 v_a7. brF.
      assert (NDP : 32 - xb <= dw * 8) by (clear - FULL; lia).
      assert (DNF1 : 1 <= dnf <= 5000) by (pose proof (GF2b NDP); unfold dnf in *; split; [apply Z.div_le_lower_bound; lia| lia]).
      bwalk [0xa2d98] NB. cnb NB.
      replace (Z.land (dx * 8 / 32 * 4 + (wpl * dy * 4 + datad) + 4) 3) with 0
        by (symmetry; change 3 with (Z.ones 2); rewrite Z.land_ones by lia; change (2 ^ 2) with 4; clear - D16; Z.div_mod_to_equations; lia).
      change (Z.b2z (0 <? 1)) with 1. cbn [Z.b2z Z.ltb Z.eqb Z.compare].
      eapply evt_cut.
      { eapply (ug2c_rows (Z.to_nat dh) (dy * wpl + fw + 1)) with (datad := datad) (ws := wsA) (ld := wpl * h) (wpl := wpl) (n := dnf) (dh := dh); try eassumption.
        all: unfold parked in *.
        all: try assumption.
        all: rewrite ?Z2Nat.id by (clear - BD; lia); rewrite ?Z.mul_sub_distr_r;
             pose proof (GF2 NDP) as GF2';
             unfold fw in *; clear - BD BD2 FWD GF1 GF2' DNF1 D16 CKR SP0R WPLB; first [lia | (Z.div_mod_to_equations; lia)]. }
      intros ms' PO2. unfold ug2c_exit in PO2.
      destruct PO2 as (y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & mB & wsB & -> & MU2 & WM2 & MI2 & UAD2 & UADL2 & ACCD2).
      unfold SHB in *.
      pose proof (munch_trans _ _ _ _ MU1 MU2) as MU12. pose proof (wmono_trans asegs _ _ _ WM1 WM2) as WM12.
      (* [comment removed for export] *)
      lstep.
      destruct GL as [V0|(V0 & V2 & DLWN & NDPL)].
      { subst v_t0. brF.
        bwalk [0xa2e30] NB.
        eapply EPI; [exact MU12| exact WM12| exact MI2]. }
      subst v_t0 v_a2.
      first [brT | brF].
      bwalk [0xa3070] NB. cnb NB.
      eapply evt_cut.
      { eapply (ug3c_rows (Z.to_nat dh) (dy * wpl + fw + 1 + dnf)) with (datad := datad) (ws := wsB) (ld := wpl * h) (wpl := wpl); try eassumption.
        all: unfold parked in *.
        all: try assumption.
        all: rewrite ?Z2Nat.id by (clear - BD; lia); rewrite ?Z.mul_sub_distr_r;
             pose proof (GF2 NDPL) as GF2'; pose proof (GF3 NDPL DLWN) as GF3'; pose proof (GF2b NDPL) as GF2b';
             unfold fw in *; clear - BD BD2 FWD GF1 GF2' GF3' GF2b' D16 CKR SP0R WPLB; first [lia | (Z.div_mod_to_equations; lia)]. }
      intros ms' PO3. unfold ug3c_exit in PO3.
      destruct PO3 as (z1 & z2 & z3 & z4 & z5 & mC & wsC & -> & MU3 & WM3 & MI3 & UAD3 & UADL3 & ACCD3).
      eapply EPI; [exact (munch_trans _ _ _ _ MU12 MU3)| exact (wmono_trans asegs _ _ _ WM12 WM3)| exact MI3].
    }
Qed.
End UNI.
