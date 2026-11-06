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
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.A14 Require Import ImageA Layout RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit D_iface D_defs
  Lept_iface Lept_lits Lept_env LeptC_kit LeptL_kit Gm_iface Gm_ropkit Gm_uni_loop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
(* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Ltac nwalk1 BD :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => first [ shbr | shbr0 | shbr_inv | shbr_x3 | br ]
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) =>
      first [ shload; lstep; clear_shl | special_step | frame_step | lstep; try sb_fix; try fix_land32; shnorm ]; cn BD
  end.
Ltac nwalk stops BD := repeat (tryif at_stop stops then fail else nwalk1 BD).
Section UNI.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis GM : gm_gaps RT.
Hypothesis RC : rt_contracts RT.

Theorem rasteropUniLow_ok : rasteropUniLow_cps RT.
Proof using AF GP GM RC.
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
  walk_to AF MST [(usp - 128, usp); (datad, datad + 4 * (wpl * h))] [0xa0434].
  cn BD.
  nwalk [0xa04c0] BD.
  (* [comment removed for export] *)
  assert (EPI : forall (ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6' : word)
                       (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (pre : list cell),
    ART RT Σ m' -> mem_inv asegs m' -> stk asegs m' lo (usp + -128) -> LIBH m' -> io_ssp m' -> agree_on PF m m' -> wmono asegs m m' ->
    rw_cells asegs m' (usp + -128) pre -> cells_size pre = 24%nat ->
    rw_cells asegs m' (usp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    cps asegs (ASTA RT Σ PMc (eq (MS (mkR ra' (Z_to_bv 64 (usp + -128)) gp (Z_to_bv 64 TP_A) t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7'
                                          s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6')
                                     F' (Z_to_bv 64 0xa08c4) fc' None m' (seg_rom asegs)))) QF).
  { clear - AF MST USP ESP PFS STa STb LOW LOR SPT SPA SPB SP0R SP0W CKR CKS CKH DIN.
    intros ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6' F' fc' m' pre
      ARTe MIe STe LHe SSPe AGF WMe FRlo PRE FRe.
    walk_to AF MST [(usp - 128, usp)] (@nil Z).
    cps_stop.
    agf_munch AGF MU ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
    apply cps_finish. intros c Hc. subst QF. cbv beta.
    exists Σ. eexists.
    split; [| repeat split; first [reflexivity | lia]].
    eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists. split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
    split; [split; [split; [exact ARTe| split; [exact MIe| split; [exact WMe|]]]| split; assumption]|].
    - eapply stk_release in FRlo; [| exact STe| lia]. rewrite PRE in FRlo.
      eapply stk_release in FRe; [| replace (usp + -104) with (usp + -128 + Z.of_nat 24) by lia; exact FRlo| lia].
      cbn [cells_size csize Nat.add] in FRe. replace (usp + -104 + Z.of_nat 104) with usp in FRe by lia. exact FRe.
    - intros a Ha Ho. exact (AGF a (conj Ha Ho)). }
  nwalk [0xa04c8] BD.
  change 31 with (Z.ones 5). rewrite (Z.land_ones (dx * 8) 5) by (clear - BD; unfold hid in *; lia). change (2^5) with 32.
  set (xb := (dx * 8) mod 32) in *.
  assert (XBR : 0 <= xb < 32) by (unfold xb; apply Z.mod_pos_bound; lia). hide XBR.
  lstep.
  brfork XB0.
  2:{ (* [comment removed for export] *)
    assert (XBN : 1 <= xb <= 31) by (clear - XBR XB0; unfold hid in *; lia). hide XBN.
    nwalk [0xa04f4] BD.
    lazymatch goal with MIx : mem_inv asegs ?mm |- evt _ _ (MS ?R _ _ _ _ ?mm _) =>
      destruct (rmask32_bytes mm MIx) as (rbs & RB & RBL);
      destruct (bytes_at_read4w mm 0x26340 rbs ((32 - xb) * 4) RB ltac:(clear - XBN; unfold hid in *; lia) ltac:(rewrite RBL; clear - XBN; unfold hid in *; lia)) as (fm & RM) end.
    lstep. clear RM RB RBL rbs.
    nwalk [0xa0510] BD.
    assert (WPLB : 0 < wpl <= 5001) by (clear - BD DWPL; unfold hid in *; subst wpl; Z.div_mod_to_equations; lia).
    assert (BD2 : 0 <= dy * wpl /\ dy * wpl + dh * wpl <= wpl * h /\ wpl * h <= 16777216).
    { clear - BD WPLB DCAP. unfold hid in *.
      pose proof (Z.mul_nonneg_nonneg dy wpl ltac:(lia) ltac:(lia)) as N1.
      pose proof (Z.mul_le_mono_nonneg_r (dy + dh) h wpl ltac:(lia) ltac:(lia)) as N3.
      rewrite Z.mul_add_distr_r in N3. rewrite (Z.mul_comm h wpl) in N3. lia. }
    assert (BD3 : dy * wpl <= 16777216 /\ 0 <= dh * wpl /\ wpl <= dh * wpl).
    { clear - BD WPLB BD2. unfold hid in *. pose proof (Z.mul_nonneg_nonneg dh wpl ltac:(lia) ltac:(lia)).
      pose proof (Z.mul_le_mono_nonneg_r 1 dh wpl ltac:(lia) ltac:(lia)). lia. }
    assert (SRL : forall j, 0 <= j < 2^31 -> bv_swrap 32 (bv_wrap 32 j / 32) = j / 32).
    { intros j Hj. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small j) by lia.
      apply bv_swrap_small. change (bv_half_modulus 32) with (2^31). split; [apply Z.le_trans with 0; [lia| apply Z.div_pos; lia]| apply Z.div_lt_upper_bound; lia]. }
    rewrite !(SRL (dx * 8)) by (clear - BD; unfold hid in *; lia).
    set (fw := dx * 8 / 32) in *.
    assert (FWD : 0 <= fw <= 5000) by (clear - BD; unfold hid in *; unfold fw; split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
    repeat match goal with |- context [bv_swrap 32 ?z] =>
      rewrite (bv_swrap_small 32 z) by (change (bv_half_modulus 32) with (2^31); clear - BD BD2 BD3; unfold hid in *; lia) end.
    repeat match goal with |- context [?E mod 18446744073709551616] =>
      rewrite (Z.mod_small E 18446744073709551616) by (clear - BD BD2 BD3 FWD; unfold hid in *; lia) end.
    pose (dnf := (dw * 8 - (32 - xb)) / 32). pose (dlw := (dw * 8 + dx * 8) mod 32). pose (pfull := datad + dy * wpl * 4 + fw * 4 + 4).
    assert (GF1 : fw + 1 <= wpl) by (clear - BD DWPL; unfold hid in *; unfold fw; subst wpl; Z.div_mod_to_equations; lia).
    assert (GF2 : 32 - xb <= dw * 8 -> fw + 1 + dnf <= wpl) by (clear - BD DWPL XBN; unfold hid in *; unfold fw, dnf, xb in *; subst wpl; intros; Z.div_mod_to_equations; lia).
    assert (GF2b : 32 - xb <= dw * 8 -> 0 <= dnf <= 5000) by (clear - BD XBN; unfold hid in *; unfold dnf, xb in *; intros; Z.div_mod_to_equations; lia).
    assert (GF3 : 32 - xb <= dw * 8 -> dlw <> 0 -> fw + 1 + dnf + 1 <= wpl) by (clear - BD DWPL XBN; unfold hid in *; unfold fw, dnf, dlw, xb in *; subst wpl; intros; Z.div_mod_to_equations; lia).
    assert (PFR0 : 0 < pfull) by (clear - BD2 FWD D0; unfold hid in *; unfold pfull; lia).
    assert (PFR1 : pfull <= datad + 4 * (wpl * h)) by (clear - GF1 BD2 BD3 FWD; unfold hid in *; unfold pfull; lia).
    assert (PFR2 : pfull <= 140737488355328) by (clear - PFR1 CKR SP0R; lia).
    assert (DLWR : 0 <= dlw < 32) by (unfold dlw; apply Z.mod_pos_bound; lia). hide DLWR.
    hide WPLB. hide BD2. hide BD3. hide FWD.
    destruct OP as [OP0|OP15]; subst op.
    2:{ (* [comment removed for export] *)
      (* [comment removed for export] *)
      assert (AFTER2 : forall (ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s7' s9' s10' s11' t3' t4' t5' t6' v5 vs6 v8 : word)
                              (F' : bvmap 5 word) (fc' : bv 32) (mc : mem) (j16 : list byte),
        (v8 = Z_to_bv 64 1 \/ (v8 = Z_to_bv 64 0 /\ v5 = Z_to_bv 64 (pfull + dnf * 4) /\ dlw <> 0 /\ 32 - xb <= dw * 8)) ->
        ART RT Σ mc -> mem_inv asegs mc -> stk asegs mc lo (usp + -128) -> LIBH mc -> io_ssp mc -> agree_on PF m mc -> wmono asegs m mc ->
        rw_cells asegs mc (usp + -128) [CB 16 j16; C8 (Z_to_bv 64 wpl)] ->
        rw_cells asegs mc (usp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
        cps asegs (ASTA RT Σ PMc (eq (MS (mkR ra' (Z_to_bv 64 (usp + -128)) gp (Z_to_bv 64 TP_A) t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7'
                                              s2' (Z_to_bv 64 2147450880) (Z_to_bv 64 dh) v5 vs6 s7' v8 s9' s10' s11' (Z_to_bv 64 wpl) t4' t5' t6')
                                         F' (Z_to_bv 64 0xa0634) fc' None mc (seg_rom asegs)))) QF).
      { clear FR MU WM ST MI LH SSP AGF ACC ACCL ACCR G0 G3 G4 G5 SARGS.
        intros ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s7' s9' s10' s11' t3' t4' t5' t6' v5 vs6 v8 F' fc' mc j16
          GL ARTc MI ST LH SSP AGF WMc FRlo FRe.
        refresh RT AF. unfold shad, SHB in *. park_disj.
        destruct GL as [V8|(V8 & V5 & DLWN & NDP)].
        - (* [comment removed for export] *)
          subst v8.
          walk_to AF MST [(usp - 128, usp); (datad, datad + 4 * (wpl * h))] [0xa08c4].
          cps_stop.
          art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists datad, (4 * (wpl * h)); split; [solve [in_live_tac]| lia]| exact I]]).
          lazymatch goal with AGFx : agree_on PF m ?mx, MUx : munch _ ?mx _ |- _ =>
            agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct Hx as [_ HxO]; cbn [outside] in HxO; split; [lia| split; [tauto| exact I]]) end.
          eapply EPI; try eassumption; try reflexivity.
        - (* [comment removed for export] *)
          subst v8 v5.
          walk_to AF MST [(usp - 128, usp); (datad, datad + 4 * (wpl * h))] [0xa0640].
          lazymatch goal with A : ART RT Σ ?mx, WMx : wmono asegs ?mx ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
            pose proof (wr_at_transport asegs mx mm datad (4 * (wpl * h)) (proj1 (af_acc_live RT AF Σ mx datad (4 * (wpl * h)) A DIN)) WMx) as WRD end.
          apply wr_at_rw_CB in WRD; [| clear - DSZ; lia]. destruct WRD as (dbs & DBC).
          pose proof DBC as [[[DBL _] _] _]. cbn in DBL. apply u8arr_of_rw_cells in DBC.
          lazymatch type of DBC with u8arr _ ?mm _ _ =>
            destruct (u8arr_u32arr mm datad dbs (wpl * h) DBC ltac:(rewrite DBL; clear - DSZ; lia)) as (wsd & UAD & UADL) end.
          clear DBC DBL.
          replace (pfull + dnf * 4) with (datad + 4 * (dy * wpl + fw + 1 + dnf)) by (unfold pfull; clear; lia).
          eapply evt_cut.
          { eapply (pw3s_rows (Z.to_nat dh) (dy * wpl + fw + 1 + dnf) dh) with (ld := wpl * h) (ws := wsd); try eassumption.
            all: unfold parked in *.
            all: try assumption.
            all: rewrite ?Z2Nat.id by (clear - BD; unfold hid in *; lia); rewrite ?Z.mul_sub_distr_r;
                 pose proof (GF2 NDP) as GF2'; pose proof (GF3 NDP DLWN) as GF3';
                 clear - BD BD2 BD3 FWD GF1 GF2' GF3' D16 CKR SP0R; unfold hid in *; first [lia | (Z.div_mod_to_equations; lia)]. }
          intros ms' PO. unfold pw3s_exit in PO.
          destruct PO as (x1 & x2 & x3 & x4 & x5 & m' & ws' & -> & MU' & WM' & MI' & UAD' & UADL').
          loop_art RT AF Σ m' lo MU'
            ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists datad, (4 * (wpl * h)); split; [solve [in_live_tac]| lia]| exact I]]).
          clear UAD' UADL' UAD UADL.
          lazymatch type of MU' with munch _ ?mm m' =>
            loop_transport mm m' MU' ltac:(fun Hx => clear - Hx CKR CKS CKH LOW LOR SPT SPB STa USP SP0R SP0W; unfold parked in *; lia) end.
          clear MU' WM'.
          cps_stop.
          lazymatch goal with AGFx : agree_on PF m ?mx, MUx : munch _ ?mx _ |- _ =>
            agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct Hx as [_ HxO]; cbn [outside] in HxO; split; [lia| split; [tauto| exact I]]) end.
          eapply EPI; try eassumption; try reflexivity. }
      (* [comment removed for export] *)
      assert (MLOOP : forall (k : nat) (q : Z) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s10' s11' t4' t5' t6' v5 vs6 v8 : word)
                             (F' : bvmap 5 word) (fc' : bv 32) (mc : mem) (j16 : list byte),
        (1 <= k)%nat -> Z.of_nat k <= 20000 -> 0 <= q -> q + (Z.of_nat k - 1) * wpl + dnf <= wpl * h -> 1 <= dnf -> dnf <= 5000 ->
        (v8 = Z_to_bv 64 1 \/ (v8 = Z_to_bv 64 0 /\ v5 = Z_to_bv 64 (pfull + dnf * 4) /\ dlw <> 0 /\ 32 - xb <= dw * 8)) ->
        ART RT Σ mc -> mem_inv asegs mc -> stk asegs mc lo (usp + -128) -> LIBH mc -> io_ssp mc -> agree_on PF m mc -> wmono asegs m mc ->
        rw_cells asegs mc (usp + -128) [CB 16 j16; C8 (Z_to_bv 64 wpl)] ->
        rw_cells asegs mc (usp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
        cps asegs (ASTA RT Σ PMc (eq (MS (mkR ra' (Z_to_bv 64 (usp + -128)) gp (Z_to_bv 64 TP_A) t0' t1' t2' (Z_to_bv 64 (wpl * 4)) (Z_to_bv 64 (datad + 4 * q))
                                              a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (dnf * 4)) (Z_to_bv 64 2147450880) (Z_to_bv 64 dh) v5 vs6
                                              (Z_to_bv 64 dnf) v8 (Z_to_bv 64 (Z.of_nat k)) s10' s11' (Z_to_bv 64 wpl) t4' t5' t6')
                                         F' (Z_to_bv 64 0xa0ae4) fc' None mc (seg_rom asegs)))) QF).
      { clear FR MU WM ST MI LH SSP AGF ACC ACCL ACCR G0 G3 G4 G5 SARGS.
        induction k as [|k IH]; intros q ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s10' s11' t4' t5' t6' v5 vs6 v8 F' fc' mc j16
          HK1 KB Q0 QB DNF1 DNF2 GL ARTc MI ST LH SSP AGF WMc FRlo FRe.
        { lia. }
        assert (PQ : 0 <= Z.of_nat k * wpl) by (clear - WPLB; unfold hid in *; apply Z.mul_nonneg_nonneg; lia).
        assert (RNG : datad <= datad + 4 * q /\ datad + 4 * q + dnf * 4 <= datad + 4 * (wpl * h) /\ 0 < dnf * 4 <= 20000).
        { clear - Q0 QB DNF1 DNF2 PQ WPLB. unfold hid in *. rewrite Z.mul_sub_distr_r in QB. lia. }
        assert (APD : datad + 4 * q + dnf * 4 <= 65536 \/ SEGTOP_A <= datad + 4 * q) by (clear - RNG CKS; unfold hid, parked, SEGTOP_A in *; lia).
        unfold SEGTOP_A in APD.
        assert (APL : datad + 4 * q + dnf * 4 <= lo) by (clear - RNG CKR LOW; unfold hid in *; lia).
        refresh RT AF. unfold shad, SHB in *. park_disj.
        walk_to AF MST [(usp - 128, usp); (datad, datad + 4 * (wpl * h))] [0x607d0].
        at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists datad, (4 * (wpl * h)); split; [solve [in_live_tac]| lia]| exact I]])
                      ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct Hx as [_ HxO]; cbn [outside] in HxO; split; [lia| split; [tauto| exact I]]).
        hide RNG. hide HK1.
        eapply cps_seq.
        { pose proof (rc_asan_memset RT RC) as MS0; unfold memset_icontract in MS0;
          eapply MS0 with (lo := lo) (d := datad + 4 * q) (n := dnf * 4) (c := Z_to_bv 8 255); rt_side idtac.
          - clear - RNG D0 CKR SP0R. unfold hid in *. lia.
          - unfold checked_dst. rewrite ?unsigned_lit by lia.
            lazymatch goal with A : ART RT Σ ?mx |- context [acc asegs ?mx _ _] =>
              pose proof (af_acc_live RT AF Σ mx datad (4 * (wpl * h)) A DIN) as (WRD & _) end.
            split; [intros _; split; [eapply (acc_sub asegs _ datad (4 * (wpl * h))); [eassumption| clear - RNG; unfold hid in *; lia| clear - RNG; unfold hid in *; lia]
                                     | left; exists datad, (4 * (wpl * h)); split; [solve [in_live_tac]| clear - RNG; unfold hid in *; lia]]|].
            split; [intros j Hj; right; right; left; exists datad, (4 * (wpl * h)); split; [solve [in_live_tac]| clear - RNG Hj; unfold hid in *; lia]|].
            eapply wr_at_sub; [exact WRD| clear - RNG; unfold hid in *; lia| clear - RNG; unfold hid in *; lia| clear - RNG; unfold hid in *; lia]. }
        after_call RT AF.
        fold_ag ltac:(fun Hx => destruct Hx as [HxA HxO]; cbn [outside] in HxO; split;
                      [apply (aclient_mono _ _ usp _ _ _ _ HxA); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| clear - HxO RNG; unfold hid in *; lia]).
        refresh RT AF. unfold shad, SHB in *. park_disj.
        walk_to AF MST [(usp - 128, usp); (datad, datad + 4 * (wpl * h))] [0xa0ae0].
        rewrite (bv_swrap_small 32 (Z.of_nat (S k) + -1)) by (change (bv_half_modulus 32) with (2^31); clear - KB; lia).
        replace (Z.of_nat (S k) + -1) with (Z.of_nat k) by (clear; lia).
        replace (datad + 4 * q + wpl * 4) with (datad + 4 * (q + wpl)) by (clear; lia).
        lstep.
        destruct k as [|k].
        - brT.
          cps_stop.
          art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists datad, (4 * (wpl * h)); split; [solve [in_live_tac]| lia]| exact I]]).
          lazymatch goal with AGFx : agree_on PF m ?mx, MUx : munch _ ?mx _ |- _ =>
            agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct Hx as [_ HxO]; cbn [outside] in HxO; split; [lia| split; [tauto| exact I]]) end.
          eapply AFTER2; try eassumption; try reflexivity.
        - brF.
          cps_stop.
          art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists datad, (4 * (wpl * h)); split; [solve [in_live_tac]| lia]| exact I]]).
          lazymatch goal with AGFx : agree_on PF m ?mx, MUx : munch _ ?mx _ |- _ =>
            agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct Hx as [_ HxO]; cbn [outside] in HxO; split; [lia| split; [tauto| exact I]]) end.
          eapply (IH (q + wpl)); try eassumption; try reflexivity; clear - Q0 QB WPLB KB; unfold hid in *; lia. }
      (* [comment removed for export] *)
      lstep.
      lazymatch goal with |- evt _ _ (MS _ ?F0 _ ?fc0 None ?mm _) =>
        eapply (evt_cut asegs (fun ms' => exists (v5 v6 v7 v9 v14 v15 v21 v22 v23 v24 : word),
          ms' = MS (mkR ra (Z_to_bv 64 (usp + -128)) gp (Z_to_bv 64 TP_A) v5 v6 v7 s0 v9 (Z_to_bv 64 (datad + fw * 4 + dy * wpl * 4)) (Z_to_bv 64 (wpl * 4)) (Z_to_bv 64 dh)
                        (Z_to_bv 64 (datad + dy * wpl * 4 + fw * 4)) v14 v15 (Z_to_bv 64 (dy * wpl * 4)) (Z_to_bv 64 (fw * 4)) s2 (Z_to_bv 64 2147450880) (Z_to_bv 64 dh)
                        v21 v22 v23 v24 s9 s10 s11 (Z_to_bv 64 wpl) t4 t5 t6)
                   F0 (Z_to_bv 64 0xa05f0) fc0 None mm (seg_rom asegs)
          /\ (v15 = Z_to_bv 64 1 \/ (v15 = Z_to_bv 64 0 /\ v23 = Z_to_bv 64 dnf /\ v9 = Z_to_bv 64 pfull /\ 32 <= dw * 8 - (32 - xb)))
          /\ (v24 = Z_to_bv 64 1 \/ (v24 = Z_to_bv 64 0 /\ v21 = Z_to_bv 64 (pfull + dnf * 4) /\ dlw <> 0 /\ 32 - xb <= dw * 8)))) end.
      {
        destruct (Z.ltb_spec (dw * 8) (32 - xb)) as [DP|NDP].
        - (* [comment removed for export] *)
          brF.
          nwalk [0xa0544] BD.
          repeat match goal with |- context [bv_swrap 32 ?z] =>
            rewrite (bv_swrap_small 32 z) by (change (bv_half_modulus 32) with (2^31); clear - BD XBN DP; unfold hid in *; lia) end.
          lazymatch goal with MIx : mem_inv asegs ?mm |- evt _ _ (MS ?R _ _ _ _ ?mm _) =>
            destruct (lmask_bytes mm MIx) as (rbs & RB & RBL);
            destruct (bytes_at_read4w mm 0x26400 rbs ((dw * 8 + xb) * 4) RB ltac:(clear - BD XBN DP; unfold hid in *; lia) ltac:(rewrite RBL; clear - BD XBN DP; unfold hid in *; lia)) as (lm & RM) end.
          lstep. clear RM RB RBL rbs.
          nwalk [0xa05f0] BD.
          apply evt_done. do 10 eexists. split; [reflexivity|]. split; left; reflexivity.
        - brT.
          nwalk [0xa05a4] BD.
          change 31 with (Z.ones 5). rewrite (Z.land_ones (dw * 8 + dx * 8) 5) by (clear - BD; unfold hid in *; lia). change (2^5) with 32.
          fold dlw.
          rewrite !(SRL (dw * 8 - (32 - xb))) by (clear - BD NDP XBN; unfold hid in *; lia).
          fold dnf. fold pfull.
          lstep.
          destruct (Z.ltb_spec (dw * 8 - (32 - xb)) 32) as [NOFULL|FULL]; cbn [Z.b2z].
          + (* [comment removed for export] *)
            destruct (Z.eq_dec dlw 0) as [DLW0|DLWN].
            * rewrite DLW0. brT. nwalk [0xa05f0] BD.
              apply evt_done. do 10 eexists. split; [reflexivity|]. split; left; reflexivity.
            * brF. nwalk [0xa05cc] BD.
              lazymatch goal with MIx : mem_inv asegs ?mm |- evt _ _ (MS ?R _ _ _ _ ?mm _) =>
                destruct (lmask_bytes mm MIx) as (rbs & RB & RBL);
                destruct (bytes_at_read4w mm 0x26400 rbs (dlw * 4) RB ltac:(clear - DLWR; unfold hid in *; lia) ltac:(rewrite RBL; clear - DLWR; unfold hid in *; lia)) as (lm & RM) end.
              lstep. clear RM RB RBL rbs.
              nwalk [0xa05f0] BD.
              apply evt_done. do 10 eexists. split; [reflexivity|]. split; [left; reflexivity| right; split; [reflexivity| split; [reflexivity| split; [exact DLWN| exact NDP]]]].
          + (* [comment removed for export] *)
            change ((0 + -1) mod 18446744073709551616) with 18446744073709551615.
            rewrite ?(Z.mod_small pfull) by (clear - PFR0 PFR2; lia). rewrite (land_ones64 pfull) by (clear - PFR0 PFR2; lia).
            destruct (Z.eq_dec dlw 0) as [DLW0|DLWN].
            * rewrite DLW0. brT. nwalk [0xa05f0] BD.
              apply evt_done. do 10 eexists. split; [reflexivity|]. split; [right; split; [reflexivity| split; [reflexivity| split; [reflexivity| exact FULL]]]| left; reflexivity].
            * brF. nwalk [0xa05cc] BD.
              lazymatch goal with MIx : mem_inv asegs ?mm |- evt _ _ (MS ?R _ _ _ _ ?mm _) =>
                destruct (lmask_bytes mm MIx) as (rbs & RB & RBL);
                destruct (bytes_at_read4w mm 0x26400 rbs (dlw * 4) RB ltac:(clear - DLWR; unfold hid in *; lia) ltac:(rewrite RBL; clear - DLWR; unfold hid in *; lia)) as (lm & RM) end.
              lstep. clear RM RB RBL rbs.
              nwalk [0xa05f0] BD.
              apply evt_done. do 10 eexists. split; [reflexivity|].
              split; [right; split; [reflexivity| split; [reflexivity| split; [reflexivity| exact FULL]]]| right; split; [reflexivity| split; [reflexivity| split; [exact DLWN| exact NDP]]]].
      }
      intros ms' (v5 & v6 & v7 & v9 & v14 & v15 & v21 & v22 & v23 & v24 & -> & GC & GL).
      lazymatch goal with A : ART RT Σ ?mx, WMx : wmono asegs ?mx ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (wr_at_transport asegs mx mm datad (4 * (wpl * h)) (proj1 (af_acc_live RT AF Σ mx datad (4 * (wpl * h)) A DIN)) WMx) as WRD end.
      apply wr_at_rw_CB in WRD; [| clear - DSZ; lia]. destruct WRD as (dbs & DBC).
      pose proof DBC as [[[DBL _] _] _]. cbn in DBL. apply u8arr_of_rw_cells in DBC.
      lazymatch type of DBC with u8arr _ ?mm _ _ =>
        destruct (u8arr_u32arr mm datad dbs (wpl * h) DBC ltac:(rewrite DBL; clear - DSZ; lia)) as (wsd & UAD & UADL) end.
      clear DBC DBL.
      replace (datad + fw * 4 + dy * wpl * 4) with (datad + 4 * (dy * wpl + fw)) by (clear; lia).
      replace (datad + dy * wpl * 4 + fw * 4) with (datad + 4 * (dy * wpl + fw)) by (clear; lia).
      eapply evt_cut.
      { eapply (pw1s_rows (Z.to_nat dh) (dy * wpl + fw) dh) with (ld := wpl * h) (ws := wsd); try eassumption.
        all: unfold parked in *.
        all: try assumption.
        all: rewrite ?Z2Nat.id by (clear - BD; unfold hid in *; lia); rewrite ?Z.mul_sub_distr_r;
             clear - BD BD2 BD3 FWD GF1 D16 CKR SP0R; unfold hid in *; first [lia | (Z.div_mod_to_equations; lia)]. }
      intros ms' PO. unfold pw1s_exit in PO.
      destruct PO as (x1 & x2 & x3 & x4 & x5 & m' & ws' & -> & MU' & WM' & MI' & UAD' & UADL').
      loop_art RT AF Σ m' lo MU'
        ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists datad, (4 * (wpl * h)); split; [solve [in_live_tac]| lia]| exact I]]).
      clear UAD' UADL' UAD UADL.
      lazymatch type of MU' with munch _ ?mm m' =>
        loop_transport mm m' MU' ltac:(fun Hx => clear - Hx CKR CKS CKH LOW LOR SPT SPB STa USP SP0R SP0W; unfold parked in *; lia) end.
      clear MU' WM'.
      lstep.
      destruct GC as [V15|(V15 & V23 & V9 & FULL)].
      - (* [comment removed for export] *)
        subst v15. brF.
        cps_stop.
        lazymatch goal with AGFx : agree_on PF m ?mx, MUx : munch _ ?mx _ |- _ =>
          agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct Hx as [_ HxO]; cbn [outside] in HxO; split; [lia| split; [tauto| exact I]]) end.
        split_at FR 2%nat FRe.
        eapply AFTER2; try eassumption; try reflexivity.
      - (* [comment removed for export] *)
        subst v15 v23 v9. brT.
        nwalk [0xa0ae4] BD.
        cps_stop.
        lazymatch goal with AGFx : agree_on PF m ?mx, MUx : munch _ ?mx _ |- _ =>
          agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct Hx as [_ HxO]; cbn [outside] in HxO; split; [lia| split; [tauto| exact I]]) end.
        split_at FR 2%nat FRe.
        replace pfull with (datad + 4 * (dy * wpl + fw + 1)) at 1 by (unfold pfull; clear; lia).
        pose proof (MLOOP (Z.to_nat dh) (dy * wpl + fw + 1)) as ML. rewrite Z2Nat.id in ML by (clear - BD; unfold hid in *; lia).
        eapply ML; try eassumption; try reflexivity.
        + clear - BD. unfold hid in *. lia.
        + clear - BD. unfold hid in *. lia.
        + clear - BD2 FWD. unfold hid in *. lia.
        + pose proof (GF2 ltac:(clear - FULL; lia)) as GF2'. clear - GF2' BD2 BD BD3. unfold hid in *. rewrite Z.mul_sub_distr_r. lia.
        + clear - FULL. unfold dnf. apply Z.div_le_lower_bound; lia.
        + pose proof (GF2b ltac:(clear - FULL; lia)) as GF2'. clear - GF2'. lia.
    }
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (AFTER2C : forall (ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s7' s9' s10' s11' t3' t4' t5' t6' v5 vs6 v8 : word)
                             (F' : bvmap 5 word) (fc' : bv 32) (mc : mem) (j16 : list byte),
      (v8 = Z_to_bv 64 1 \/ (v8 = Z_to_bv 64 0 /\ v5 = Z_to_bv 64 (pfull + dnf * 4) /\ dlw <> 0 /\ 32 - xb <= dw * 8)) ->
      ART RT Σ mc -> mem_inv asegs mc -> stk asegs mc lo (usp + -128) -> LIBH mc -> io_ssp mc -> agree_on PF m mc -> wmono asegs m mc ->
      rw_cells asegs mc (usp + -128) [CB 16 j16; C8 (Z_to_bv 64 wpl)] ->
      rw_cells asegs mc (usp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      cps asegs (ASTA RT Σ PMc (eq (MS (mkR ra' (Z_to_bv 64 (usp + -128)) gp (Z_to_bv 64 TP_A) t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7'
                                            (Z_to_bv 64 (wpl * 4)) (Z_to_bv 64 2147450880) (Z_to_bv 64 dh) v5 vs6 s7' v8 s9' s10' s11' t3' t4' t5' t6')
                                       F' (Z_to_bv 64 0xa08c0) fc' None mc (seg_rom asegs)))) QF).
    { clear FR MU WM ST MI LH SSP AGF ACC ACCL ACCR G0 G3 G4 G5 SARGS.
      intros ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s7' s9' s10' s11' t3' t4' t5' t6' v5 vs6 v8 F' fc' mc j16
        GL ARTc MI ST LH SSP AGF WMc FRlo FRe.
      refresh RT AF. unfold shad, SHB in *. park_disj.
      destruct GL as [V8|(V8 & V5 & DLWN & NDP)].
      - (* [comment removed for export] *)
        subst v8.
        walk_to AF MST [(usp - 128, usp); (datad, datad + 4 * (wpl * h))] [0xa08c4].
        cps_stop.
        art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists datad, (4 * (wpl * h)); split; [solve [in_live_tac]| lia]| exact I]]).
        lazymatch goal with AGFx : agree_on PF m ?mx, MUx : munch _ ?mx _ |- _ =>
          agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct Hx as [_ HxO]; cbn [outside] in HxO; split; [lia| split; [tauto| exact I]]) end.
        eapply EPI; try eassumption; try reflexivity.
      - (* [comment removed for export] *)
        subst v8 v5.
        walk_to AF MST [(usp - 128, usp); (datad, datad + 4 * (wpl * h))] [0xa0b38].
        lazymatch goal with A : ART RT Σ ?mx, WMx : wmono asegs ?mx ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          pose proof (wr_at_transport asegs mx mm datad (4 * (wpl * h)) (proj1 (af_acc_live RT AF Σ mx datad (4 * (wpl * h)) A DIN)) WMx) as WRD end.
        apply wr_at_rw_CB in WRD; [| clear - DSZ; lia]. destruct WRD as (dbs & DBC).
        pose proof DBC as [[[DBL _] _] _]. cbn in DBL. apply u8arr_of_rw_cells in DBC.
        lazymatch type of DBC with u8arr _ ?mm _ _ =>
          destruct (u8arr_u32arr mm datad dbs (wpl * h) DBC ltac:(rewrite DBL; clear - DSZ; lia)) as (wsd & UAD & UADL) end.
        clear DBC DBL.
        replace (pfull + dnf * 4) with (datad + 4 * (dy * wpl + fw + 1 + dnf)) by (unfold pfull; clear; lia).
        eapply evt_cut.
        { eapply (pw3c_rows (Z.to_nat dh) (dy * wpl + fw + 1 + dnf) dh) with (ld := wpl * h) (ws := wsd); try eassumption.
          all: unfold parked in *.
          all: try assumption.
          all: rewrite ?Z2Nat.id by (clear - BD; unfold hid in *; lia); rewrite ?Z.mul_sub_distr_r;
               pose proof (GF2 NDP) as GF2'; pose proof (GF3 NDP DLWN) as GF3';
               clear - BD BD2 BD3 FWD GF1 GF2' GF3' D16 CKR SP0R; unfold hid in *; first [lia | (Z.div_mod_to_equations; lia)]. }
        intros ms' PO. unfold pw3c_exit in PO.
        destruct PO as (x1 & x2 & x3 & x4 & x5 & m' & ws' & -> & MU' & WM' & MI' & UAD' & UADL').
        loop_art RT AF Σ m' lo MU'
          ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists datad, (4 * (wpl * h)); split; [solve [in_live_tac]| lia]| exact I]]).
        clear UAD' UADL' UAD UADL.
        lazymatch type of MU' with munch _ ?mm m' =>
          loop_transport mm m' MU' ltac:(fun Hx => clear - Hx CKR CKS CKH LOW LOR SPT SPB STa USP SP0R SP0W; unfold parked in *; lia) end.
        clear MU' WM'.
        cps_stop.
        lazymatch goal with AGFx : agree_on PF m ?mx, MUx : munch _ ?mx _ |- _ =>
          agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct Hx as [_ HxO]; cbn [outside] in HxO; split; [lia| split; [tauto| exact I]]) end.
        eapply EPI; try eassumption; try reflexivity. }
    (* [comment removed for export] *)
    assert (MLOOPC : forall (k : nat) (q : Z) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s10' s11' t3' t4' t5' t6' v5 vs6 v8 : word)
                            (F' : bvmap 5 word) (fc' : bv 32) (mc : mem) (j16 : list byte),
      (1 <= k)%nat -> Z.of_nat k <= 20000 -> 0 <= q -> q + (Z.of_nat k - 1) * wpl + dnf <= wpl * h -> 1 <= dnf -> dnf <= 5000 ->
      (v8 = Z_to_bv 64 1 \/ (v8 = Z_to_bv 64 0 /\ v5 = Z_to_bv 64 (pfull + dnf * 4) /\ dlw <> 0 /\ 32 - xb <= dw * 8)) ->
      ART RT Σ mc -> mem_inv asegs mc -> stk asegs mc lo (usp + -128) -> LIBH mc -> io_ssp mc -> agree_on PF m mc -> wmono asegs m mc ->
      rw_cells asegs mc (usp + -128) [CB 16 j16; C8 (Z_to_bv 64 wpl)] ->
      rw_cells asegs mc (usp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      cps asegs (ASTA RT Σ PMc (eq (MS (mkR ra' (Z_to_bv 64 (usp + -128)) gp (Z_to_bv 64 TP_A) t0' t1' t2' (Z_to_bv 64 (dnf * 4)) (Z_to_bv 64 (datad + 4 * q))
                                            a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (wpl * 4)) (Z_to_bv 64 2147450880) (Z_to_bv 64 dh) v5 vs6
                                            (Z_to_bv 64 dnf) v8 (Z_to_bv 64 (Z.of_nat k)) s10' s11' t3' t4' t5' t6')
                                       F' (Z_to_bv 64 0xa0b18) fc' None mc (seg_rom asegs)))) QF).
    { clear FR MU WM ST MI LH SSP AGF ACC ACCL ACCR G0 G3 G4 G5 SARGS.
      induction k as [|k IH]; intros q ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s10' s11' t3' t4' t5' t6' v5 vs6 v8 F' fc' mc j16
        HK1 KB Q0 QB DNF1 DNF2 GL ARTc MI ST LH SSP AGF WMc FRlo FRe.
      { lia. }
      assert (PQ : 0 <= Z.of_nat k * wpl) by (clear - WPLB; unfold hid in *; apply Z.mul_nonneg_nonneg; lia).
      assert (RNG : datad <= datad + 4 * q /\ datad + 4 * q + dnf * 4 <= datad + 4 * (wpl * h) /\ 0 < dnf * 4 <= 20000).
      { clear - Q0 QB DNF1 DNF2 PQ WPLB. unfold hid in *. rewrite Z.mul_sub_distr_r in QB. lia. }
      assert (APD : datad + 4 * q + dnf * 4 <= 65536 \/ SEGTOP_A <= datad + 4 * q) by (clear - RNG CKS; unfold hid, parked, SEGTOP_A in *; lia).
      unfold SEGTOP_A in APD.
      assert (APL : datad + 4 * q + dnf * 4 <= lo) by (clear - RNG CKR LOW; unfold hid in *; lia).
      refresh RT AF. unfold shad, SHB in *. park_disj.
      walk_to AF MST [(usp - 128, usp); (datad, datad + 4 * (wpl * h))] [0x607d0].
      at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists datad, (4 * (wpl * h)); split; [solve [in_live_tac]| lia]| exact I]])
                    ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct Hx as [_ HxO]; cbn [outside] in HxO; split; [lia| split; [tauto| exact I]]).
      hide RNG. hide HK1.
      eapply cps_seq.
      { pose proof (rc_asan_memset RT RC) as MS0; unfold memset_icontract in MS0;
        eapply MS0 with (lo := lo) (d := datad + 4 * q) (n := dnf * 4) (c := Z_to_bv 8 0); rt_side idtac.
        - clear - RNG D0 CKR SP0R. unfold hid in *. lia.
        - unfold checked_dst. rewrite ?unsigned_lit by lia.
          lazymatch goal with A : ART RT Σ ?mx |- context [acc asegs ?mx _ _] =>
            pose proof (af_acc_live RT AF Σ mx datad (4 * (wpl * h)) A DIN) as (WRD & _) end.
          split; [intros _; split; [eapply (acc_sub asegs _ datad (4 * (wpl * h))); [eassumption| clear - RNG; unfold hid in *; lia| clear - RNG; unfold hid in *; lia]
                                   | left; exists datad, (4 * (wpl * h)); split; [solve [in_live_tac]| clear - RNG; unfold hid in *; lia]]|].
          split; [intros j Hj; right; right; left; exists datad, (4 * (wpl * h)); split; [solve [in_live_tac]| clear - RNG Hj; unfold hid in *; lia]|].
          eapply wr_at_sub; [exact WRD| clear - RNG; unfold hid in *; lia| clear - RNG; unfold hid in *; lia| clear - RNG; unfold hid in *; lia]. }
      after_call RT AF.
      fold_ag ltac:(fun Hx => destruct Hx as [HxA HxO]; cbn [outside] in HxO; split;
                    [apply (aclient_mono _ _ usp _ _ _ _ HxA); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| clear - HxO RNG; unfold hid in *; lia]).
      refresh RT AF. unfold shad, SHB in *. park_disj.
      walk_to AF MST [(usp - 128, usp); (datad, datad + 4 * (wpl * h))] [0xa0b14].
      rewrite (bv_swrap_small 32 (Z.of_nat (S k) + -1)) by (change (bv_half_modulus 32) with (2^31); clear - KB; lia).
      replace (Z.of_nat (S k) + -1) with (Z.of_nat k) by (clear; lia).
      replace (datad + 4 * q + wpl * 4) with (datad + 4 * (q + wpl)) by (clear; lia).
      lstep.
      destruct k as [|k].
      - brT.
        cps_stop.
        art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists datad, (4 * (wpl * h)); split; [solve [in_live_tac]| lia]| exact I]]).
        lazymatch goal with AGFx : agree_on PF m ?mx, MUx : munch _ ?mx _ |- _ =>
          agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct Hx as [_ HxO]; cbn [outside] in HxO; split; [lia| split; [tauto| exact I]]) end.
        eapply AFTER2C; try eassumption; try reflexivity.
      - brF.
        cps_stop.
        art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists datad, (4 * (wpl * h)); split; [solve [in_live_tac]| lia]| exact I]]).
        lazymatch goal with AGFx : agree_on PF m ?mx, MUx : munch _ ?mx _ |- _ =>
          agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct Hx as [_ HxO]; cbn [outside] in HxO; split; [lia| split; [tauto| exact I]]) end.
        eapply (IH (q + wpl)); try eassumption; try reflexivity; clear - Q0 QB WPLB KB; unfold hid in *; lia. }
    (* [comment removed for export] *)
    lstep.
    lazymatch goal with |- evt _ _ (MS _ ?F0 _ ?fc0 None ?mm _) =>
      eapply (evt_cut asegs (fun ms' => exists (v5 v6 v7 v9 v14 v15 v21 v22 v23 v24 : word),
        ms' = MS (mkR ra (Z_to_bv 64 (usp + -128)) gp (Z_to_bv 64 TP_A) v5 v6 v7 s0 v9 (Z_to_bv 64 (datad + fw * 4 + dy * wpl * 4)) v14 (Z_to_bv 64 (wpl * 4))
                      (Z_to_bv 64 (datad + dy * wpl * 4 + fw * 4)) (Z_to_bv 64 dh) v15 (Z_to_bv 64 (dy * wpl * 4)) (Z_to_bv 64 (fw * 4)) s2 (Z_to_bv 64 2147450880) (Z_to_bv 64 dh)
                      v21 v22 v23 v24 s9 s10 s11 (Z_to_bv 64 wpl) t4 t5 t6)
                 F0 (Z_to_bv 64 0xa0794) fc0 None mm (seg_rom asegs)
        /\ (v15 = Z_to_bv 64 1 \/ (v15 = Z_to_bv 64 0 /\ v23 = Z_to_bv 64 dnf /\ v9 = Z_to_bv 64 pfull /\ 32 <= dw * 8 - (32 - xb)))
        /\ (v24 = Z_to_bv 64 1 \/ (v24 = Z_to_bv 64 0 /\ v21 = Z_to_bv 64 (pfull + dnf * 4) /\ dlw <> 0 /\ 32 - xb <= dw * 8)))) end.
    {
      destruct (Z.ltb_spec (dw * 8) (32 - xb)) as [DP|NDP].
      - (* [comment removed for export] *)
        brF.
        nwalk [0xa0544] BD.
        repeat match goal with |- context [bv_swrap 32 ?z] =>
          rewrite (bv_swrap_small 32 z) by (change (bv_half_modulus 32) with (2^31); clear - BD XBN DP; unfold hid in *; lia) end.
        lazymatch goal with MIx : mem_inv asegs ?mm |- evt _ _ (MS ?R _ _ _ _ ?mm _) =>
          destruct (lmask_bytes mm MIx) as (rbs & RB & RBL);
          destruct (bytes_at_read4w mm 0x26400 rbs ((dw * 8 + xb) * 4) RB ltac:(clear - BD XBN DP; unfold hid in *; lia) ltac:(rewrite RBL; clear - BD XBN DP; unfold hid in *; lia)) as (lm & RM) end.
        lstep. clear RM RB RBL rbs.
        nwalk [0xa0794] BD.
        apply evt_done. do 10 eexists. split; [reflexivity|]. split; left; reflexivity.
      - brT.
        nwalk [0xa05a4] BD.
        change 31 with (Z.ones 5). rewrite (Z.land_ones (dw * 8 + dx * 8) 5) by (clear - BD; unfold hid in *; lia). change (2^5) with 32.
        fold dlw.
        rewrite !(SRL (dw * 8 - (32 - xb))) by (clear - BD NDP XBN; unfold hid in *; lia).
        fold dnf. fold pfull.
        lstep.
        destruct (Z.ltb_spec (dw * 8 - (32 - xb)) 32) as [NOFULL|FULL]; cbn [Z.b2z].
        + (* [comment removed for export] *)
          destruct (Z.eq_dec dlw 0) as [DLW0|DLWN].
          * rewrite DLW0. brT. nwalk [0xa0794] BD.
            apply evt_done. do 10 eexists. split; [reflexivity|]. split; left; reflexivity.
          * brF. nwalk [0xa05cc] BD.
            lazymatch goal with MIx : mem_inv asegs ?mm |- evt _ _ (MS ?R _ _ _ _ ?mm _) =>
              destruct (lmask_bytes mm MIx) as (rbs & RB & RBL);
              destruct (bytes_at_read4w mm 0x26400 rbs (dlw * 4) RB ltac:(clear - DLWR; unfold hid in *; lia) ltac:(rewrite RBL; clear - DLWR; unfold hid in *; lia)) as (lm & RM) end.
            lstep. clear RM RB RBL rbs.
            nwalk [0xa0794] BD.
            apply evt_done. do 10 eexists. split; [reflexivity|]. split; [left; reflexivity| right; split; [reflexivity| split; [reflexivity| split; [exact DLWN| exact NDP]]]].
        + (* [comment removed for export] *)
          change ((0 + -1) mod 18446744073709551616) with 18446744073709551615.
          rewrite ?(Z.mod_small pfull) by (clear - PFR0 PFR2; lia). rewrite (land_ones64 pfull) by (clear - PFR0 PFR2; lia).
          destruct (Z.eq_dec dlw 0) as [DLW0|DLWN].
          * rewrite DLW0. brT. nwalk [0xa0794] BD.
            apply evt_done. do 10 eexists. split; [reflexivity|]. split; [right; split; [reflexivity| split; [reflexivity| split; [reflexivity| exact FULL]]]| left; reflexivity].
          * brF. nwalk [0xa05cc] BD.
            lazymatch goal with MIx : mem_inv asegs ?mm |- evt _ _ (MS ?R _ _ _ _ ?mm _) =>
              destruct (lmask_bytes mm MIx) as (rbs & RB & RBL);
              destruct (bytes_at_read4w mm 0x26400 rbs (dlw * 4) RB ltac:(clear - DLWR; unfold hid in *; lia) ltac:(rewrite RBL; clear - DLWR; unfold hid in *; lia)) as (lm & RM) end.
            lstep. clear RM RB RBL rbs.
            nwalk [0xa0794] BD.
            apply evt_done. do 10 eexists. split; [reflexivity|].
            split; [right; split; [reflexivity| split; [reflexivity| split; [reflexivity| exact FULL]]]| right; split; [reflexivity| split; [reflexivity| split; [exact DLWN| exact NDP]]]].
    }
    intros ms' (v5 & v6 & v7 & v9 & v14 & v15 & v21 & v22 & v23 & v24 & -> & GC & GL).
    lazymatch goal with A : ART RT Σ ?mx, WMx : wmono asegs ?mx ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (wr_at_transport asegs mx mm datad (4 * (wpl * h)) (proj1 (af_acc_live RT AF Σ mx datad (4 * (wpl * h)) A DIN)) WMx) as WRD end.
    apply wr_at_rw_CB in WRD; [| clear - DSZ; lia]. destruct WRD as (dbs & DBC).
    pose proof DBC as [[[DBL _] _] _]. cbn in DBL. apply u8arr_of_rw_cells in DBC.
    lazymatch type of DBC with u8arr _ ?mm _ _ =>
      destruct (u8arr_u32arr mm datad dbs (wpl * h) DBC ltac:(rewrite DBL; clear - DSZ; lia)) as (wsd & UAD & UADL) end.
    clear DBC DBL.
    replace (datad + fw * 4 + dy * wpl * 4) with (datad + 4 * (dy * wpl + fw)) by (clear; lia).
    replace (datad + dy * wpl * 4 + fw * 4) with (datad + 4 * (dy * wpl + fw)) by (clear; lia).
    eapply evt_cut.
    { eapply (pw1c_rows (Z.to_nat dh) (dy * wpl + fw) dh) with (ld := wpl * h) (ws := wsd); try eassumption.
      all: unfold parked in *.
      all: try assumption.
      all: rewrite ?Z2Nat.id by (clear - BD; unfold hid in *; lia); rewrite ?Z.mul_sub_distr_r;
           clear - BD BD2 BD3 FWD GF1 D16 CKR SP0R; unfold hid in *; first [lia | (Z.div_mod_to_equations; lia)]. }
    intros ms' PO. unfold pw1c_exit in PO.
    destruct PO as (x1 & x2 & x3 & x4 & x5 & m' & ws' & -> & MU' & WM' & MI' & UAD' & UADL').
    loop_art RT AF Σ m' lo MU'
      ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists datad, (4 * (wpl * h)); split; [solve [in_live_tac]| lia]| exact I]]).
    clear UAD' UADL' UAD UADL.
    lazymatch type of MU' with munch _ ?mm m' =>
      loop_transport mm m' MU' ltac:(fun Hx => clear - Hx CKR CKS CKH LOW LOR SPT SPB STa USP SP0R SP0W; unfold parked in *; lia) end.
    clear MU' WM'.
    nwalk [0xa08bc] BD. lstep.
    destruct GC as [V15|(V15 & V23 & V9 & FULL)].
    - (* [comment removed for export] *)
      subst v15. brF.
      cps_stop.
      lazymatch goal with AGFx : agree_on PF m ?mx, MUx : munch _ ?mx _ |- _ =>
        agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct Hx as [_ HxO]; cbn [outside] in HxO; split; [lia| split; [tauto| exact I]]) end.
      split_at FR 2%nat FRe.
      eapply AFTER2C; try eassumption; try reflexivity.
    - (* [comment removed for export] *)
      subst v15 v23 v9. brT.
      nwalk [0xa0b18] BD.
      cps_stop.
      lazymatch goal with AGFx : agree_on PF m ?mx, MUx : munch _ ?mx _ |- _ =>
        agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct Hx as [_ HxO]; cbn [outside] in HxO; split; [lia| split; [tauto| exact I]]) end.
      split_at FR 2%nat FRe.
      replace pfull with (datad + 4 * (dy * wpl + fw + 1)) at 1 by (unfold pfull; clear; lia).
      pose proof (MLOOPC (Z.to_nat dh) (dy * wpl + fw + 1)) as ML. rewrite Z2Nat.id in ML by (clear - BD; unfold hid in *; lia).
      eapply ML; try eassumption; try reflexivity.
      + clear - BD. unfold hid in *. lia.
      + clear - BD. unfold hid in *. lia.
      + clear - BD2 FWD. unfold hid in *. lia.
      + pose proof (GF2 ltac:(clear - FULL; lia)) as GF2'. clear - GF2' BD2 BD BD3. unfold hid in *. rewrite Z.mul_sub_distr_r. lia.
      + clear - FULL. unfold dnf. apply Z.div_le_lower_bound; lia.
      + pose proof (GF2b ltac:(clear - FULL; lia)) as GF2'. clear - GF2'. lia.
  }
  (* [comment removed for export] *)
  nwalk [0xa0558] BD.
  change 31 with (Z.ones 5). rewrite (Z.land_ones (dw * 8) 5) by (clear - BD; unfold hid in *; lia). change (2^5) with 32.
  set (lw := (dw * 8) mod 32) in *.
  assert (LWR : 0 <= lw < 32) by (unfold lw; apply Z.mod_pos_bound; lia). hide LWR.
  lstep.
  merge4 0xa0680 (Z_to_bv 5 24) (Z_to_bv 5 12) (Z_to_bv 5 14) (Z_to_bv 5 16).
  { brfork LW0.
    - merge_done4.
    - nwalk [0xa057c] BD.
      lazymatch goal with MIx : mem_inv asegs ?mm |- evt _ _ (MS ?R _ _ _ _ ?mm _) =>
        destruct (lmask_bytes mm MIx) as (rbs & RB & RBL);
        destruct (bytes_at_read4w mm 0x26400 rbs (lw * 4) RB ltac:(clear - LWR; unfold hid in *; lia) ltac:(rewrite RBL; clear - LWR; unfold hid in *; lia)) as (wm & RM) end.
      lstep. clear RM RB.
      nwalk [0xa0680] BD. merge_done4. }
  nwalk [0xa069c] BD.
  assert (WPLB : 0 < wpl <= 5001) by (clear - BD DWPL; unfold hid in *; subst wpl; Z.div_mod_to_equations; lia).
  assert (BD2 : 0 <= dy * wpl /\ dy * wpl + dh * wpl <= wpl * h /\ wpl * h <= 16777216).
  { clear - BD WPLB DCAP. unfold hid in *.
    pose proof (Z.mul_nonneg_nonneg dy wpl ltac:(lia) ltac:(lia)) as N1.
    pose proof (Z.mul_le_mono_nonneg_r (dy + dh) h wpl ltac:(lia) ltac:(lia)) as N3.
    rewrite Z.mul_add_distr_r in N3. rewrite (Z.mul_comm h wpl) in N3. lia. }
  assert (SRL : forall j, 0 <= j < 2^31 -> bv_swrap 32 (bv_wrap 32 j / 32) = j / 32).
  { intros j Hj. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small j) by lia.
    apply bv_swrap_small. change (bv_half_modulus 32) with (2^31). split; [apply Z.le_trans with 0; [lia| apply Z.div_pos; lia]| apply Z.div_lt_upper_bound; lia]. }
  rewrite !(SRL (dx * 8)) by (clear - BD; unfold hid in *; lia). rewrite !(SRL (dw * 8)) by (clear - BD; unfold hid in *; lia). clear SRL.
  repeat match goal with |- context [bv_swrap 32 ?z] =>
    rewrite (bv_swrap_small 32 z) by (change (bv_half_modulus 32) with (2^31); clear - BD BD2; unfold hid in *; lia) end.
  assert (FWD : 0 <= dx * 8 / 32 <= 5000 /\ 0 <= dw * 8 / 32 <= 5000) by (clear - BD; unfold hid in *; split; split; try (apply Z.div_pos; lia); apply Z.div_le_upper_bound; lia).
  repeat match goal with |- context [?E mod 18446744073709551616] =>
    rewrite (Z.mod_small E 18446744073709551616) by (clear - BD BD2 FWD; unfold hid in *; lia) end.
  assert (BD3 : dy * wpl <= 16777216 /\ 0 <= dh * wpl).
  { clear - BD WPLB BD2. unfold hid in *. pose proof (Z.mul_nonneg_nonneg dh wpl ltac:(lia) ltac:(lia)). lia. }
  repeat match goal with |- context [bv_swrap 32 ?z] =>
    rewrite (bv_swrap_small 32 z) by (change (bv_half_modulus 32) with (2^31); clear - BD BD2 BD3; unfold hid in *; lia) end.
  repeat match goal with |- context [?E mod 18446744073709551616] =>
    rewrite (Z.mod_small E 18446744073709551616) by (clear - BD BD2 BD3 FWD; unfold hid in *; lia) end.
  hide WPLB. hide BD2. hide BD3. hide FWD.
  destruct OP as [OP0|OP15].
  2:{ (* [comment removed for export] *)
    subst op. nwalk [0xa0958] BD.
    rewrite !(Z.div_mul dh 4294967296) by lia.
    set (nfw := dw * 8 / 32) in *. set (fw := dx * 8 / 32) in *.
    repeat match goal with |- context [?E mod 18446744073709551616] =>
      rewrite (Z.mod_small E 18446744073709551616) by (clear - BD BD2 BD3 FWD; unfold hid in *; unfold fw, nfw in *; lia) end.
    set (base0 := datad + (fw + dy * wpl) * 4) in *.
    assert (HD0 : lw = 0 -> fw + nfw <= wpl) by (clear - BD DWPL XB0; unfold hid in *; unfold lw, fw, nfw, xb in *; subst wpl; intros; Z.div_mod_to_equations; lia).
    assert (HD1 : lw <> 0 -> fw + nfw + 1 <= wpl) by (clear - BD DWPL XB0; unfold hid in *; unfold lw, fw, nfw, xb in *; subst wpl; intros; Z.div_mod_to_equations; lia).
    assert (FW0 : 0 <= fw) by (clear - FWD; unfold hid in *; unfold fw; lia).
    assert (LOOPS : forall (k : nat) (i : Z) (ra' t0' t1' t2' a0' a1' a3' a4' a5' a6' a7' s2' t4' t5' t6' : word)
                           (F' : bvmap 5 word) (fc' : bv 32) (mc : mem) (j16 : list byte) (nb : Z),
      Z.of_nat k = dh - i -> 0 <= i -> (1 <= k)%nat -> (32 <= dw * 8 -> nb = 4 * nfw) ->
      ART RT Σ mc -> mem_inv asegs mc -> stk asegs mc lo (usp + -128) -> LIBH mc -> io_ssp mc -> agree_on PF m mc -> wmono asegs m mc ->
      rw_cells asegs mc (usp + -128) [CB 16 j16; C8 (Z_to_bv 64 wpl)] ->
      rw_cells asegs mc (usp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      cps asegs (ASTA RT Σ PMc (eq (MS (mkR ra' (Z_to_bv 64 (usp + -128)) gp (Z_to_bv 64 TP_A) t0' t1' t2'
                                            (Z_to_bv 64 (nb + base0)) (Z_to_bv 64 nb) a0' a1' (Z_to_bv 64 32) a3' a4' a5' a6' a7'
                                            s2' (Z_to_bv 64 2147450880) (Z_to_bv 64 (wpl * 4)) (Z_to_bv 64 (dw * 8)) (Z_to_bv 64 lw)
                                            (Z_to_bv 64 (base0 + 4 * (i * wpl))) u (Z_to_bv 64 (i * wpl)) (Z_to_bv 64 base0)
                                            (Z_to_bv 64 (i - dh)) (Z_to_bv 64 wpl) t4' t5' t6')
                                       F' (Z_to_bv 64 0xa0958) fc' None mc (seg_rom asegs)))) QF).
    { clear FR MU WM ST MI LH SSP AGF ACC ACCL ACCR G0 G3 G4 G5 SARGS.
      induction k as [|k IH]; intros i ra' t0' t1' t2' a0' a1' a3' a4' a5' a6' a7' s2' t4' t5' t6' F' fc' mc j16 nb
        HK HI HK1 NB ARTc MI ST LH SSP AGF WMc FRlo FRe.
      { lia. }
      assert (PI : 0 <= i * wpl /\ i * wpl + wpl <= dh * wpl /\ i * wpl <= 16777216).
      { clear - HK HI WPLB BD2 BD3. unfold hid in *. pose proof (Z.mul_nonneg_nonneg i wpl ltac:(lia) ltac:(lia)).
        pose proof (Z.mul_le_mono_nonneg_r (i + 1) dh wpl ltac:(lia) ltac:(lia)) as N. rewrite Z.mul_add_distr_r in N. lia. }
      assert (NFW0 : 0 <= nfw <= 5000) by (clear - FWD; unfold hid in *; unfold nfw; lia).
      assert (RNG : datad <= base0 + i * wpl * 4 /\ base0 + i * wpl * 4 + 4 * nfw + 4 <= datad + 4 * (wpl * h) + 4
                    /\ (lw <> 0 -> base0 + i * wpl * 4 + 4 * nfw + 4 <= datad + 4 * (wpl * h))
                    /\ base0 + i * wpl * 4 + 4 * nfw <= datad + 4 * (wpl * h)).
      { clear - HD0 HD1 FW0 PI BD2 NFW0 HK HI. unfold hid in *. unfold base0. destruct (Z.eq_dec lw 0) as [E|E]; [specialize (HD0 E)| specialize (HD1 E)]; repeat split; intros; try lia. }
      refresh RT AF. unfold shad, SHB in *. park_disj.
      destruct (Z.ltb_spec (dw * 8) 32) as [WLT|WGE].
      { (* [comment removed for export] *)
        assert (NF0 : nfw = 0) by (clear - WLT BD; unfold hid in *; unfold nfw; apply Z.div_small; lia).
        assert (LWN : lw <> 0) by (clear - WLT BD; unfold hid in *; unfold lw; rewrite Z.mod_small by lia; lia).
        walk_to AF MST [(usp - 128, usp); (datad, datad + 4 * (wpl * h))] [0xa0980].
        lstep. brF.
        (* [comment removed for export] *)
        assert (PAE : base0 + 4 * (i * wpl) = datad + 4 * (fw + dy * wpl + i * wpl + nfw)) by (clear - NF0; unfold hid in *; unfold base0; lia).
        assert (PW : datad <= base0 + 4 * (i * wpl) /\ base0 + 4 * (i * wpl) + 4 <= datad + 4 * (wpl * h)) by (clear - RNG LWN NFW0 NF0; unfold hid in *; lia).
        lazymatch goal with A : ART RT Σ ?mx, WMx : wmono asegs ?mx ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          pose proof (wr_at_transport asegs mx mm datad (4 * (wpl * h)) (proj1 (af_acc_live RT AF Σ mx datad (4 * (wpl * h)) A DIN)) WMx) as WRD end.
        apply wr_at_rw_CB in WRD; [| clear - DSZ; lia]. destruct WRD as (dbs & DBC).
        pose proof DBC as [[[DBL _] _] _]. cbn in DBL. apply u8arr_of_rw_cells in DBC.
        lazymatch type of DBC with u8arr _ ?mm _ _ =>
          destruct (u8arr_u32arr mm datad dbs (wpl * h) DBC ltac:(rewrite DBL; clear - DSZ; lia)) as (wsd & UAD & UADL) end.
        clear DBC DBL.
        assert (APS : base0 + 4 * (i * wpl) + 4 <= 65536 \/ SEGTOP_A <= base0 + 4 * (i * wpl)) by (clear - PW CKS; unfold parked, SEGTOP_A in *; lia).
        unfold SEGTOP_A in APS.
        assert (APH : base0 + 4 * (i * wpl) + 4 <= 2147446784 \/ 17594333495296 <= base0 + 4 * (i * wpl)) by (clear - PW CKH; unfold parked in *; lia).
        park APS. park APH.
        lwalk [0xa093c].
        destruct (u32arr_nth wsd (fw + dy * wpl + i * wpl + nfw) ltac:(rewrite UADL; clear - PW PAE FW0 PI BD2 NFW0; unfold hid in *; lia)) as (wv & NTH).
        pose proof (u32arr_read asegs _ datad wsd (fw + dy * wpl + i * wpl + nfw) wv (wa (base0 + 4 * (i * wpl))) UAD NTH
                      ltac:(clear - FW0 PI BD2 NFW0; unfold hid in *; lia) ltac:(f_equal; clear - PAE; lia)) as R.
        lstep. clear R NTH.
        lwalk [0xa0944].
        arr_sw datad (fw + dy * wpl + i * wpl + nfw) (base0 + 4 * (i * wpl)).
        lwalk [0xa0948].
        (* [comment removed for export] *)
        lwalk [0xa0954].
        rewrite (bv_swrap_small 32 (i * wpl + wpl)) by (change (bv_half_modulus 32) with (2^31); clear - PI BD2 BD3 WPLB; unfold hid in *; lia).
        replace (base0 + 4 * (i * wpl) + wpl * 4) with (base0 + 4 * ((i + 1) * wpl)) by (clear; lia).
        replace (i * wpl + wpl) with ((i + 1) * wpl) by (clear; lia).
        replace (i - dh + 1) with (i + 1 - dh) by (clear; lia).
        lstep.
        destruct k as [|k].
        - replace (i + 1 - dh) with 0 by (clear - HK; lia). brT.
          cps_stop.
          art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists datad, (4 * (wpl * h)); split; [solve [in_live_tac]| lia]| exact I]]).
          lazymatch goal with AGFx : agree_on PF m ?mx, MUx : munch _ ?mx _ |- _ =>
            agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct Hx as [_ HxO]; cbn [outside] in HxO; split; [lia| split; [tauto| exact I]]) end.
          eapply EPI; try eassumption; try reflexivity.
        - brF.
          cps_stop.
          art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists datad, (4 * (wpl * h)); split; [solve [in_live_tac]| lia]| exact I]]).
          lazymatch goal with AGFx : agree_on PF m ?mx, MUx : munch _ ?mx _ |- _ =>
            agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct Hx as [_ HxO]; cbn [outside] in HxO; split; [lia| split; [tauto| exact I]]) end.
          eapply (IH (i + 1)); try eassumption; try reflexivity; try (intros; reflexivity); clear - HK HI; lia.
      }
      specialize (NB WGE). subst nb.
      (* [comment removed for export] *)
      assert (NF1 : 1 <= nfw <= 5000) by (clear - WGE BD; unfold hid in *; unfold nfw; split; [apply Z.div_le_lower_bound; lia| apply Z.div_le_upper_bound; lia]).
      assert (APD : base0 + i * wpl * 4 + 4 * nfw <= 65536 \/ SEGTOP_A <= base0 + i * wpl * 4) by (clear - RNG CKS NF1; unfold hid, parked, SEGTOP_A in *; lia).
      unfold SEGTOP_A in APD.
      assert (APL : base0 + i * wpl * 4 + 4 * nfw <= lo) by (clear - RNG CKR LOW; unfold hid in *; lia).
      walk_to AF MST [(usp - 128, usp); (datad, datad + 4 * (wpl * h))] [0x607d0].
      at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists datad, (4 * (wpl * h)); split; [solve [in_live_tac]| lia]| exact I]])
                    ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct Hx as [_ HxO]; cbn [outside] in HxO; split; [lia| split; [tauto| exact I]]).
      hide PI. hide NF1. hide NFW0. hide RNG. hide HK1.
      eapply cps_seq.
      { pose proof (rc_asan_memset RT RC) as MS0; unfold memset_icontract in MS0;
        eapply MS0 with (lo := lo) (d := base0 + i * wpl * 4) (n := 4 * nfw) (c := Z_to_bv 8 255); rt_side idtac.
        - clear - RNG D0 CKR SP0R NF1. unfold hid in *. lia.
        - unfold checked_dst. rewrite ?unsigned_lit by lia.
          lazymatch goal with A : ART RT Σ ?mx |- context [acc asegs ?mx _ _] =>
            pose proof (af_acc_live RT AF Σ mx datad (4 * (wpl * h)) A DIN) as (WRD & _) end.
          split; [intros _; split; [eapply (acc_sub asegs _ datad (4 * (wpl * h))); [eassumption| clear - RNG; unfold hid in *; lia| clear - RNG; unfold hid in *; lia]
                                   | left; exists datad, (4 * (wpl * h)); split; [solve [in_live_tac]| clear - RNG; unfold hid in *; lia]]|].
          split; [intros j Hj; right; right; left; exists datad, (4 * (wpl * h)); split; [solve [in_live_tac]| clear - RNG Hj; unfold hid in *; lia]|].
          eapply wr_at_sub; [exact WRD| clear - RNG; unfold hid in *; lia| clear - RNG; unfold hid in *; lia| clear - NF1; unfold hid in *; lia]. }
      after_call RT AF.
      fold_ag ltac:(fun Hx => destruct Hx as [HxA HxO]; cbn [outside] in HxO; split;
                    [apply (aclient_mono _ _ usp _ _ _ _ HxA); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| clear - HxO RNG; unfold hid in *; lia]).
      unfold hid in PI, NF1, NFW0.
      refresh RT AF. unfold shad, SHB in *. park_disj.
      walk_to AF MST [(usp - 128, usp); (datad, datad + 4 * (wpl * h))] [0xa0980].
      lstep.
      destruct (Z.eq_dec lw 0) as [LW0|LWN].
      { brT.
        (* [comment removed for export] *)
        lwalk [0xa0954].
        rewrite (bv_swrap_small 32 (i * wpl + wpl)) by (change (bv_half_modulus 32) with (2^31); clear - PI BD2 BD3 WPLB; unfold hid in *; lia).
        replace (base0 + 4 * (i * wpl) + wpl * 4) with (base0 + 4 * ((i + 1) * wpl)) by (clear; lia).
        replace (i * wpl + wpl) with ((i + 1) * wpl) by (clear; lia).
        replace (i - dh + 1) with (i + 1 - dh) by (clear; lia).
        lstep.
        destruct k as [|k].
        - replace (i + 1 - dh) with 0 by (clear - HK; lia). brT.
          cps_stop.
          art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists datad, (4 * (wpl * h)); split; [solve [in_live_tac]| lia]| exact I]]).
          lazymatch goal with AGFx : agree_on PF m ?mx, MUx : munch _ ?mx _ |- _ =>
            agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct Hx as [_ HxO]; cbn [outside] in HxO; split; [lia| split; [tauto| exact I]]) end.
          eapply EPI; try eassumption; try reflexivity.
        - brF.
          cps_stop.
          art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists datad, (4 * (wpl * h)); split; [solve [in_live_tac]| lia]| exact I]]).
          lazymatch goal with AGFx : agree_on PF m ?mx, MUx : munch _ ?mx _ |- _ =>
            agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct Hx as [_ HxO]; cbn [outside] in HxO; split; [lia| split; [tauto| exact I]]) end.
          eapply (IH (i + 1)); try eassumption; try reflexivity; try (intros; reflexivity); clear - HK HI; lia.
      }
      brF.
      (* [comment removed for export] *)
      assert (PAE : 4 * nfw + base0 + i * wpl * 4 = datad + 4 * (fw + dy * wpl + i * wpl + nfw)) by (clear - NF1; unfold hid in *; unfold base0; lia).
      assert (PW : datad <= 4 * nfw + base0 + i * wpl * 4 /\ 4 * nfw + base0 + i * wpl * 4 + 4 <= datad + 4 * (wpl * h)) by (clear - RNG LWN NFW0 NF1; unfold hid in *; lia).
      lazymatch goal with A : ART RT Σ ?mx, WMx : wmono asegs ?mx ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (wr_at_transport asegs mx mm datad (4 * (wpl * h)) (proj1 (af_acc_live RT AF Σ mx datad (4 * (wpl * h)) A DIN)) WMx) as WRD end.
      apply wr_at_rw_CB in WRD; [| clear - DSZ; lia]. destruct WRD as (dbs & DBC).
      pose proof DBC as [[[DBL _] _] _]. cbn in DBL. apply u8arr_of_rw_cells in DBC.
      lazymatch type of DBC with u8arr _ ?mm _ _ =>
        destruct (u8arr_u32arr mm datad dbs (wpl * h) DBC ltac:(rewrite DBL; clear - DSZ; lia)) as (wsd & UAD & UADL) end.
      clear DBC DBL.
      assert (APS : 4 * nfw + base0 + i * wpl * 4 + 4 <= 65536 \/ SEGTOP_A <= 4 * nfw + base0 + i * wpl * 4) by (clear - PW CKS; unfold parked, SEGTOP_A in *; lia).
      unfold SEGTOP_A in APS.
      assert (APH : 4 * nfw + base0 + i * wpl * 4 + 4 <= 2147446784 \/ 17594333495296 <= 4 * nfw + base0 + i * wpl * 4) by (clear - PW CKH; unfold parked in *; lia).
      park APS. park APH.
      lwalk [0xa093c].
      destruct (u32arr_nth wsd (fw + dy * wpl + i * wpl + nfw) ltac:(rewrite UADL; clear - PW PAE FW0 PI BD2 NFW0; unfold hid in *; lia)) as (wv & NTH).
      pose proof (u32arr_read asegs _ datad wsd (fw + dy * wpl + i * wpl + nfw) wv (wa (4 * nfw + base0 + i * wpl * 4)) UAD NTH
                    ltac:(clear - FW0 PI BD2 NFW0; unfold hid in *; lia) ltac:(f_equal; clear - PAE; lia)) as R.
      lstep. clear R NTH.
      lwalk [0xa0944].
      arr_sw datad (fw + dy * wpl + i * wpl + nfw) (4 * nfw + base0 + i * wpl * 4).
      lwalk [0xa0948].
      (* [comment removed for export] *)
      lwalk [0xa0954].
      rewrite (bv_swrap_small 32 (i * wpl + wpl)) by (change (bv_half_modulus 32) with (2^31); clear - PI BD2 BD3 WPLB; unfold hid in *; lia).
      replace (base0 + 4 * (i * wpl) + wpl * 4) with (base0 + 4 * ((i + 1) * wpl)) by (clear; lia).
      replace (i * wpl + wpl) with ((i + 1) * wpl) by (clear; lia).
      replace (i - dh + 1) with (i + 1 - dh) by (clear; lia).
      lstep.
      destruct k as [|k].
      - replace (i + 1 - dh) with 0 by (clear - HK; lia). brT.
        cps_stop.
        art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists datad, (4 * (wpl * h)); split; [solve [in_live_tac]| lia]| exact I]]).
        lazymatch goal with AGFx : agree_on PF m ?mx, MUx : munch _ ?mx _ |- _ =>
          agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct Hx as [_ HxO]; cbn [outside] in HxO; split; [lia| split; [tauto| exact I]]) end.
        eapply EPI; try eassumption; try reflexivity.
      - brF.
        cps_stop.
        art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists datad, (4 * (wpl * h)); split; [solve [in_live_tac]| lia]| exact I]]).
        lazymatch goal with AGFx : agree_on PF m ?mx, MUx : munch _ ?mx _ |- _ =>
          agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct Hx as [_ HxO]; cbn [outside] in HxO; split; [lia| split; [tauto| exact I]]) end.
        eapply (IH (i + 1)); try eassumption; try reflexivity; try (intros; reflexivity); clear - HK HI; lia.
    }
    (* [comment removed for export] *)
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists datad, (4 * (wpl * h)); split; [solve [in_live_tac]| lia]| exact I]]).
    lazymatch goal with AGFx : agree_on PF m ?mx, MUx : munch _ ?mx _ |- _ =>
      agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct Hx as [_ HxO]; cbn [outside] in HxO; split; [lia| split; [tauto| exact I]]) end.
    split_at FR 2%nat FRe.
    replace (datad + dy * wpl * 4 + fw * 4) with (base0 + 4 * (0 * wpl)) by (unfold base0; clear; lia).
    eapply (LOOPS (Z.to_nat dh) 0); try eassumption; try reflexivity.
    + clear - BD. unfold hid in *. lia.
    + clear - BD. unfold hid in *. lia.
    + intros WGE. assert (NF1 : 1 <= nfw <= 5000) by (clear - WGE BD; unfold hid in *; unfold nfw; split; [apply Z.div_le_lower_bound; lia| apply Z.div_le_upper_bound; lia]).
      clear - NF1. rewrite (Z.mod_small (nfw + -1)) by lia. rewrite Z.mod_small by lia. Z.div_mod_to_equations. lia.
  }
  (* [comment removed for export] *)
  subst op. nwalk [0xa0a0c] BD.
  rewrite !(Z.div_mul dh 4294967296) by lia.
  set (nfw := dw * 8 / 32) in *. set (fw := dx * 8 / 32) in *.
  repeat match goal with |- context [?E mod 18446744073709551616] =>
    rewrite (Z.mod_small E 18446744073709551616) by (clear - BD BD2 BD3 FWD; unfold hid in *; unfold fw, nfw in *; lia) end.
  set (base0 := datad + (fw + dy * wpl) * 4) in *.
  assert (HD0 : lw = 0 -> fw + nfw <= wpl) by (clear - BD DWPL XB0; unfold hid in *; unfold lw, fw, nfw, xb in *; subst wpl; intros; Z.div_mod_to_equations; lia).
  assert (HD1 : lw <> 0 -> fw + nfw + 1 <= wpl) by (clear - BD DWPL XB0; unfold hid in *; unfold lw, fw, nfw, xb in *; subst wpl; intros; Z.div_mod_to_equations; lia).
  assert (FW0 : 0 <= fw) by (clear - FWD; unfold hid in *; unfold fw; lia).
  assert (LOOPC : forall (k : nat) (i : Z) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' t4' t5' t6' : word)
                         (F' : bvmap 5 word) (fc' : bv 32) (mc : mem) (j8 : list byte) (nb : Z),
    Z.of_nat k = dh - i -> 0 <= i -> (1 <= k)%nat -> (32 <= dw * 8 -> nb = 4 * nfw) ->
    ART RT Σ mc -> mem_inv asegs mc -> stk asegs mc lo (usp + -128) -> LIBH mc -> io_ssp mc -> agree_on PF m mc -> wmono asegs m mc ->
    rw_cells asegs mc (usp + -128) [CB 8 j8; C8 (Z_to_bv 64 (Z.lxor (bv_unsigned u) 18446744073709551615)); C8 (Z_to_bv 64 wpl)] ->
    rw_cells asegs mc (usp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    cps asegs (ASTA RT Σ PMc (eq (MS (mkR ra' (Z_to_bv 64 (usp + -128)) gp (Z_to_bv 64 TP_A) t0' t1' t2'
                                          (Z_to_bv 64 (i - dh)) (Z_to_bv 64 nb) a0' a1' a2' a3' a4' a5' a6' a7'
                                          s2' (Z_to_bv 64 2147450880) (Z_to_bv 64 (wpl * 4)) (Z_to_bv 64 (dw * 8)) (Z_to_bv 64 lw)
                                          (Z_to_bv 64 (base0 + 4 * (i * wpl))) (Z_to_bv 64 32) (Z_to_bv 64 (i * wpl)) (Z_to_bv 64 base0)
                                          (Z_to_bv 64 (nb + base0)) (Z_to_bv 64 wpl) t4' t5' t6')
                                     F' (Z_to_bv 64 0xa0a0c) fc' None mc (seg_rom asegs)))) QF).
  { clear FR MU WM ST MI LH SSP AGF ACC ACCL ACCR G0 G3 G4 G5 SARGS.
    induction k as [|k IH]; intros i ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' t4' t5' t6' F' fc' mc j8 nb
      HK HI HK1 NB ARTc MI ST LH SSP AGF WMc FRlo FRe.
    { lia. }
    assert (PI : 0 <= i * wpl /\ i * wpl + wpl <= dh * wpl /\ i * wpl <= 16777216).
    { clear - HK HI WPLB BD2 BD3. unfold hid in *. pose proof (Z.mul_nonneg_nonneg i wpl ltac:(lia) ltac:(lia)).
      pose proof (Z.mul_le_mono_nonneg_r (i + 1) dh wpl ltac:(lia) ltac:(lia)) as N. rewrite Z.mul_add_distr_r in N. lia. }
    assert (NFW0 : 0 <= nfw <= 5000) by (clear - FWD; unfold hid in *; unfold nfw; lia).
    assert (RNG : datad <= base0 + i * wpl * 4 /\ base0 + i * wpl * 4 + 4 * nfw + 4 <= datad + 4 * (wpl * h) + 4
                  /\ (lw <> 0 -> base0 + i * wpl * 4 + 4 * nfw + 4 <= datad + 4 * (wpl * h))
                  /\ base0 + i * wpl * 4 + 4 * nfw <= datad + 4 * (wpl * h)).
    { clear - HD0 HD1 FW0 PI BD2 NFW0 HK HI. unfold hid in *. unfold base0. destruct (Z.eq_dec lw 0) as [E|E]; [specialize (HD0 E)| specialize (HD1 E)]; repeat split; intros; try lia. }
    refresh RT AF. unfold shad, SHB in *. park_disj.
    destruct (Z.ltb_spec (dw * 8) 32) as [WLT|WGE].
    { (* [comment removed for export] *)
      assert (NF0 : nfw = 0) by (clear - WLT BD; unfold hid in *; unfold nfw; apply Z.div_small; lia).
      assert (LWN : lw <> 0) by (clear - WLT BD; unfold hid in *; unfold lw; rewrite Z.mod_small by lia; lia).
      walk_to AF MST [(usp - 128, usp); (datad, datad + 4 * (wpl * h))] [0xa0a30].
      lstep. brF.
      (* [comment removed for export] *)
      assert (PAE : base0 + 4 * (i * wpl) = datad + 4 * (fw + dy * wpl + i * wpl + nfw)) by (clear - NF0; unfold hid in *; unfold base0; lia).
      assert (PW : datad <= base0 + 4 * (i * wpl) /\ base0 + 4 * (i * wpl) + 4 <= datad + 4 * (wpl * h)) by (clear - RNG LWN NFW0 NF0; unfold hid in *; lia).
      lazymatch goal with A : ART RT Σ ?mx, WMx : wmono asegs ?mx ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (wr_at_transport asegs mx mm datad (4 * (wpl * h)) (proj1 (af_acc_live RT AF Σ mx datad (4 * (wpl * h)) A DIN)) WMx) as WRD end.
      apply wr_at_rw_CB in WRD; [| clear - DSZ; lia]. destruct WRD as (dbs & DBC).
      pose proof DBC as [[[DBL _] _] _]. cbn in DBL. apply u8arr_of_rw_cells in DBC.
      lazymatch type of DBC with u8arr _ ?mm _ _ =>
        destruct (u8arr_u32arr mm datad dbs (wpl * h) DBC ltac:(rewrite DBL; clear - DSZ; lia)) as (wsd & UAD & UADL) end.
      clear DBC DBL.
      assert (APS : base0 + 4 * (i * wpl) + 4 <= 65536 \/ SEGTOP_A <= base0 + 4 * (i * wpl)) by (clear - PW CKS; unfold parked, SEGTOP_A in *; lia).
      unfold SEGTOP_A in APS.
      assert (APH : base0 + 4 * (i * wpl) + 4 <= 2147446784 \/ 17594333495296 <= base0 + 4 * (i * wpl)) by (clear - PW CKH; unfold parked in *; lia).
      park APS. park APH.
      lwalk [0xa09ec].
      destruct (u32arr_nth wsd (fw + dy * wpl + i * wpl + nfw) ltac:(rewrite UADL; clear - PW PAE FW0 PI BD2 NFW0; unfold hid in *; lia)) as (wv & NTH).
      pose proof (u32arr_read asegs _ datad wsd (fw + dy * wpl + i * wpl + nfw) wv (wa (base0 + 4 * (i * wpl))) UAD NTH
                    ltac:(clear - FW0 PI BD2 NFW0; unfold hid in *; lia) ltac:(f_equal; clear - PAE; lia)) as R.
      lstep. clear R NTH.
      lwalk [0xa09f8].
      arr_sw datad (fw + dy * wpl + i * wpl + nfw) (base0 + 4 * (i * wpl)).
      lwalk [0xa09fc].
      (* [comment removed for export] *)
      lwalk [0xa0a08].
      rewrite (bv_swrap_small 32 (i * wpl + wpl)) by (change (bv_half_modulus 32) with (2^31); clear - PI BD2 BD3 WPLB; unfold hid in *; lia).
      replace (base0 + 4 * (i * wpl) + wpl * 4) with (base0 + 4 * ((i + 1) * wpl)) by (clear; lia).
      replace (i * wpl + wpl) with ((i + 1) * wpl) by (clear; lia).
      replace (i - dh + 1) with (i + 1 - dh) by (clear; lia).
      lstep.
      destruct k as [|k].
      - replace (i + 1 - dh) with 0 by (clear - HK; lia). brT.
        cps_stop.
        art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists datad, (4 * (wpl * h)); split; [solve [in_live_tac]| lia]| exact I]]).
        lazymatch goal with AGFx : agree_on PF m ?mx, MUx : munch _ ?mx _ |- _ =>
          agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct Hx as [_ HxO]; cbn [outside] in HxO; split; [lia| split; [tauto| exact I]]) end.
        eapply EPI; try eassumption; try reflexivity.
      - brF.
        cps_stop.
        art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists datad, (4 * (wpl * h)); split; [solve [in_live_tac]| lia]| exact I]]).
        lazymatch goal with AGFx : agree_on PF m ?mx, MUx : munch _ ?mx _ |- _ =>
          agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct Hx as [_ HxO]; cbn [outside] in HxO; split; [lia| split; [tauto| exact I]]) end.
        eapply (IH (i + 1)); try eassumption; try reflexivity; try (intros; reflexivity); clear - HK HI; lia.
    }
    specialize (NB WGE). subst nb.
    (* [comment removed for export] *)
    assert (NF1 : 1 <= nfw <= 5000) by (clear - WGE BD; unfold hid in *; unfold nfw; split; [apply Z.div_le_lower_bound; lia| apply Z.div_le_upper_bound; lia]).
    assert (APD : base0 + i * wpl * 4 + 4 * nfw <= 65536 \/ SEGTOP_A <= base0 + i * wpl * 4) by (clear - RNG CKS NF1; unfold hid, parked, SEGTOP_A in *; lia).
    unfold SEGTOP_A in APD.
    assert (APL : base0 + i * wpl * 4 + 4 * nfw <= lo) by (clear - RNG CKR LOW; unfold hid in *; lia).
    walk_to AF MST [(usp - 128, usp); (datad, datad + 4 * (wpl * h))] [0x607d0].
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists datad, (4 * (wpl * h)); split; [solve [in_live_tac]| lia]| exact I]])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct Hx as [_ HxO]; cbn [outside] in HxO; split; [lia| split; [tauto| exact I]]).
    hide PI. hide NF1. hide NFW0. hide RNG. hide HK1.
    eapply cps_seq.
    { pose proof (rc_asan_memset RT RC) as MS0; unfold memset_icontract in MS0;
      eapply MS0 with (lo := lo) (d := base0 + i * wpl * 4) (n := 4 * nfw) (c := Z_to_bv 8 0); rt_side idtac.
      - clear - RNG D0 CKR SP0R NF1. unfold hid in *. lia.
      - unfold checked_dst. rewrite ?unsigned_lit by lia.
        lazymatch goal with A : ART RT Σ ?mx |- context [acc asegs ?mx _ _] =>
          pose proof (af_acc_live RT AF Σ mx datad (4 * (wpl * h)) A DIN) as (WRD & _) end.
        split; [intros _; split; [eapply (acc_sub asegs _ datad (4 * (wpl * h))); [eassumption| clear - RNG; unfold hid in *; lia| clear - RNG; unfold hid in *; lia]
                                 | left; exists datad, (4 * (wpl * h)); split; [solve [in_live_tac]| clear - RNG; unfold hid in *; lia]]|].
        split; [intros j Hj; right; right; left; exists datad, (4 * (wpl * h)); split; [solve [in_live_tac]| clear - RNG Hj; unfold hid in *; lia]|].
        eapply wr_at_sub; [exact WRD| clear - RNG; unfold hid in *; lia| clear - RNG; unfold hid in *; lia| clear - NF1; unfold hid in *; lia]. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => destruct Hx as [HxA HxO]; cbn [outside] in HxO; split;
                  [apply (aclient_mono _ _ usp _ _ _ _ HxA); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| clear - HxO RNG; unfold hid in *; lia]).
    unfold hid in PI, NF1, NFW0.
    refresh RT AF. unfold shad, SHB in *. park_disj.
    walk_to AF MST [(usp - 128, usp); (datad, datad + 4 * (wpl * h))] [0xa0a30].
    lstep.
    destruct (Z.eq_dec lw 0) as [LW0|LWN].
    { brT.
      (* [comment removed for export] *)
      lwalk [0xa0a08].
      rewrite (bv_swrap_small 32 (i * wpl + wpl)) by (change (bv_half_modulus 32) with (2^31); clear - PI BD2 BD3 WPLB; unfold hid in *; lia).
      replace (base0 + 4 * (i * wpl) + wpl * 4) with (base0 + 4 * ((i + 1) * wpl)) by (clear; lia).
      replace (i * wpl + wpl) with ((i + 1) * wpl) by (clear; lia).
      replace (i - dh + 1) with (i + 1 - dh) by (clear; lia).
      lstep.
      destruct k as [|k].
      - replace (i + 1 - dh) with 0 by (clear - HK; lia). brT.
        cps_stop.
        art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists datad, (4 * (wpl * h)); split; [solve [in_live_tac]| lia]| exact I]]).
        lazymatch goal with AGFx : agree_on PF m ?mx, MUx : munch _ ?mx _ |- _ =>
          agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct Hx as [_ HxO]; cbn [outside] in HxO; split; [lia| split; [tauto| exact I]]) end.
        eapply EPI; try eassumption; try reflexivity.
      - brF.
        cps_stop.
        art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists datad, (4 * (wpl * h)); split; [solve [in_live_tac]| lia]| exact I]]).
        lazymatch goal with AGFx : agree_on PF m ?mx, MUx : munch _ ?mx _ |- _ =>
          agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct Hx as [_ HxO]; cbn [outside] in HxO; split; [lia| split; [tauto| exact I]]) end.
        eapply (IH (i + 1)); try eassumption; try reflexivity; try (intros; reflexivity); clear - HK HI; lia.
    }
    brF.
    (* [comment removed for export] *)
    assert (PAE : 4 * nfw + base0 + i * wpl * 4 = datad + 4 * (fw + dy * wpl + i * wpl + nfw)) by (clear - NF1; unfold hid in *; unfold base0; lia).
    assert (PW : datad <= 4 * nfw + base0 + i * wpl * 4 /\ 4 * nfw + base0 + i * wpl * 4 + 4 <= datad + 4 * (wpl * h)) by (clear - RNG LWN NFW0 NF1; unfold hid in *; lia).
    lazymatch goal with A : ART RT Σ ?mx, WMx : wmono asegs ?mx ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (wr_at_transport asegs mx mm datad (4 * (wpl * h)) (proj1 (af_acc_live RT AF Σ mx datad (4 * (wpl * h)) A DIN)) WMx) as WRD end.
    apply wr_at_rw_CB in WRD; [| clear - DSZ; lia]. destruct WRD as (dbs & DBC).
    pose proof DBC as [[[DBL _] _] _]. cbn in DBL. apply u8arr_of_rw_cells in DBC.
    lazymatch type of DBC with u8arr _ ?mm _ _ =>
      destruct (u8arr_u32arr mm datad dbs (wpl * h) DBC ltac:(rewrite DBL; clear - DSZ; lia)) as (wsd & UAD & UADL) end.
    clear DBC DBL.
    assert (APS : 4 * nfw + base0 + i * wpl * 4 + 4 <= 65536 \/ SEGTOP_A <= 4 * nfw + base0 + i * wpl * 4) by (clear - PW CKS; unfold parked, SEGTOP_A in *; lia).
    unfold SEGTOP_A in APS.
    assert (APH : 4 * nfw + base0 + i * wpl * 4 + 4 <= 2147446784 \/ 17594333495296 <= 4 * nfw + base0 + i * wpl * 4) by (clear - PW CKH; unfold parked in *; lia).
    park APS. park APH.
    lwalk [0xa09ec].
    destruct (u32arr_nth wsd (fw + dy * wpl + i * wpl + nfw) ltac:(rewrite UADL; clear - PW PAE FW0 PI BD2 NFW0; unfold hid in *; lia)) as (wv & NTH).
    pose proof (u32arr_read asegs _ datad wsd (fw + dy * wpl + i * wpl + nfw) wv (wa (4 * nfw + base0 + i * wpl * 4)) UAD NTH
                  ltac:(clear - FW0 PI BD2 NFW0; unfold hid in *; lia) ltac:(f_equal; clear - PAE; lia)) as R.
    lstep. clear R NTH.
    lwalk [0xa09f8].
    arr_sw datad (fw + dy * wpl + i * wpl + nfw) (4 * nfw + base0 + i * wpl * 4).
    lwalk [0xa09fc].
    (* [comment removed for export] *)
    lwalk [0xa0a08].
    rewrite (bv_swrap_small 32 (i * wpl + wpl)) by (change (bv_half_modulus 32) with (2^31); clear - PI BD2 BD3 WPLB; unfold hid in *; lia).
    replace (base0 + 4 * (i * wpl) + wpl * 4) with (base0 + 4 * ((i + 1) * wpl)) by (clear; lia).
    replace (i * wpl + wpl) with ((i + 1) * wpl) by (clear; lia).
    replace (i - dh + 1) with (i + 1 - dh) by (clear; lia).
    lstep.
    destruct k as [|k].
    - replace (i + 1 - dh) with 0 by (clear - HK; lia). brT.
      cps_stop.
      art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists datad, (4 * (wpl * h)); split; [solve [in_live_tac]| lia]| exact I]]).
      lazymatch goal with AGFx : agree_on PF m ?mx, MUx : munch _ ?mx _ |- _ =>
        agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct Hx as [_ HxO]; cbn [outside] in HxO; split; [lia| split; [tauto| exact I]]) end.
      eapply EPI; try eassumption; try reflexivity.
    - brF.
      cps_stop.
      art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists datad, (4 * (wpl * h)); split; [solve [in_live_tac]| lia]| exact I]]).
      lazymatch goal with AGFx : agree_on PF m ?mx, MUx : munch _ ?mx _ |- _ =>
        agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct Hx as [_ HxO]; cbn [outside] in HxO; split; [lia| split; [tauto| exact I]]) end.
      eapply (IH (i + 1)); try eassumption; try reflexivity; try (intros; reflexivity); clear - HK HI; lia.
  }
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists datad, (4 * (wpl * h)); split; [solve [in_live_tac]| lia]| exact I]]).
  lazymatch goal with AGFx : agree_on PF m ?mx, MUx : munch _ ?mx _ |- _ =>
    agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct Hx as [_ HxO]; cbn [outside] in HxO; split; [lia| split; [tauto| exact I]]) end.
  split_at FR 3%nat FRe.
  replace (datad + dy * wpl * 4 + fw * 4) with (base0 + 4 * (0 * wpl)) by (unfold base0; clear; lia).
  eapply (LOOPC (Z.to_nat dh) 0); try eassumption; try reflexivity.
  + clear - BD. unfold hid in *. lia.
  + clear - BD. unfold hid in *. lia.
  + intros WGE. assert (NF1 : 1 <= nfw <= 5000) by (clear - WGE BD; unfold hid in *; unfold nfw; split; [apply Z.div_le_lower_bound; lia| apply Z.div_le_upper_bound; lia]).
    clear - NF1. rewrite (Z.mod_small (nfw + -1)) by lia. rewrite Z.mod_small by lia. Z.div_mod_to_equations. lia.
Qed.
End UNI.
