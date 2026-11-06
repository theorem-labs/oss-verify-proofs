(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import Tac RzCPS NodesA SysStep Arr StoreFast.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import ImageA Layout RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit D_iface D_defs
  Lept_iface Lept_lits Lept_env LeptC_kit LeptL_kit Gm_iface Gm_ropkit LeptB_guard LeptB_guard2 GmB_kit GmB_roplow_loop Fh_rop_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
(* [comment removed for export] *)
Local Ltac tlia ::= sf_clear_big;   (* [comment removed for export] *)
              first [ xlia zchecker
                    | zn_lits; xlia zchecker
                    | zn_lits; zdiv_lits; xlia zchecker
                    | sf_unhide; unpark_all; zify_prune_sub;
                      first [ zn_lits; xlia zchecker
                            | zn_lits; zdiv_lits; xlia zchecker
                            | zn_lits; Z.div_mod_to_equations; xlia zchecker
                            | Zify.zify; xlia zchecker ]
                    | Zify.zify; xlia zchecker
                    | sf_unhide;
                      first [ zify_prune_neg; Zify.zify; xlia zchecker
                            | zify_prune_plain; Zify.zify; xlia zchecker
                            | Zify.zify; xlia zchecker ] ].
Ltac dedup_ro := repeat match goal with H1 : ro_cells asegs ?m ?a ?c, H2 : ro_cells asegs ?m ?a ?c |- _ => clear H2 end.
Ltac drop_acc a := repeat match goal with H : acc asegs _ a _ |- _ => clear H end.

Section ROPLOW1.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis GM : gm_gaps RT.

Theorem rasteropLow_src1_ok : rasteropLow_src1_cps RT.
Proof using AF GP GM.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    datad dpw dph dwpl dx dy dw dh datas spw sph swpl sx sy
    FDO MST -> -> -> -> -> -> -> -> -> SARGS RD RS DNE RCD RCS DX4 SX4 ENV.
  unfold lpost, lenv, keeps, keepsL, raster1, rect_in, chunk in *.
  destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RD as ((DIN & D0 & D16 & DSZ) & DW & DH & DWPL & DCAP).
  destruct RS as ((SIN & S0 & S16 & SSZ) & SW & SH & SWPL & SCAP).
  destruct RCD as (RD1 & RD2 & RD3 & RD4 & RD5 & RD6). destruct RCS as (RS1 & RS2 & _ & _ & RS5 & RS6).
  pose proof (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_rasteropLow, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a /\ outside [(datad, datad + 4 * (dwpl * dph))] a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  pose proof ST as (STa & STb & _).
  pose proof (live_apart RT AF Σ m datad (4 * (dwpl * dph)) datas (4 * (swpl * sph)) ART0 DIN SIN DNE) as DSAP.
  chunk_facts RT AF GP datad (4 * (dwpl * dph)).
  chunk_facts RT AF GP datas (4 * (swpl * sph)).
  pose proof (gm_acc_lmask32 RT GM Σ m ART0) as ACCL. unfold GM_LMASK32 in ACCL.
  refresh RT AF. unfold shad, SHB in *. park_disj.
  dedup_ro. drop_acc datad. drop_acc datas.
  (* [comment removed for export] *)
  assert (BD : 0 <= dx /\ 0 <= dy /\ 0 < dw /\ 0 < dh /\ dx + dw <= dpw /\ dy + dh <= dph /\ 0 <= sx /\ 0 <= sy /\ sx + dw <= spw /\ sy + dh <= sph
               /\ dpw <= 20000 /\ dph <= 20000 /\ spw <= 20000 /\ sph <= 20000) by lia.
  walk_to AF MST [(usp - 256, usp); (datad, datad + 4 * (dwpl * dph))] [0xa3640].
  lstep. lstep.
  assert (L31 : Z.land (Z.lor (dx) (sx)) 31 = 0).
  { rewrite Z.land_lor_distr_l. change 31 with (Z.ones 5). rewrite !Z.land_ones by lia. change (2^5) with 32.
    replace ((dx) mod 32) with 0 by (clear - DX4 BD; Z.div_mod_to_equations; lia).
    replace ((sx) mod 32) with 0 by (clear - SX4 BD; Z.div_mod_to_equations; lia). reflexivity. }
  rewrite L31. clear L31. lstep. brT.
  rewrite ?Z.add_0_r.
  lstep.
  change 31 with (Z.ones 5). rewrite (Z.land_ones (dw) 5) by lia. change (2^5) with 32.
  set (lw := (dw) mod 32) in *.
  assert (LWR : 0 <= lw < 32) by (unfold lw; apply Z.mod_pos_bound; lia).
  lstep.
  (* [comment removed for export] *)
  merge4 0xa3a48 (Z_to_bv 5 10) (Z_to_bv 5 12) (Z_to_bv 5 13) (Z_to_bv 5 18).
  { brfork LW0.
    - merge_done4.
    - awalk [0xa382c].
      lazymatch goal with MIx : mem_inv asegs ?mm |- evt _ _ (MS ?R _ _ _ _ ?mm _) =>
        destruct (lmask_bytes mm MIx) as (rbs & RB & RBL);
        destruct (bytes_at_read4w mm 0x26480 rbs (lw * 4) RB ltac:(clear - LWR; lia) ltac:(rewrite RBL; clear - LWR; lia)) as (wm & RM) end.
      lstep. clear RM RB.
      awalk [0xa3a48]. merge_done4. }
  (* [comment removed for export] *)
  assert (WPLB : 0 < dwpl <= 5001 /\ 0 < swpl <= 5001) by (clear - BD DWPL SWPL; subst dwpl swpl; Z.div_mod_to_equations; lia).
  assert (BD2 : 0 <= dy * dwpl /\ dy * dwpl + dh * dwpl <= dwpl * dph /\ 0 <= sy * swpl /\ sy * swpl + dh * swpl <= swpl * sph
                /\ 0 < dwpl <= 5001 /\ 0 < swpl <= 5001 /\ dwpl * dph <= 16777216 /\ swpl * sph <= 16777216).
  { clear - BD WPLB DCAP SCAP.
    pose proof (Z.mul_nonneg_nonneg dy dwpl ltac:(lia) ltac:(lia)) as N1.
    pose proof (Z.mul_nonneg_nonneg sy swpl ltac:(lia) ltac:(lia)) as N2.
    pose proof (Z.mul_le_mono_nonneg_r (dy + dh) dph dwpl ltac:(lia) ltac:(lia)) as N3.
    pose proof (Z.mul_le_mono_nonneg_r (sy + dh) sph swpl ltac:(lia) ltac:(lia)) as N4.
    rewrite Z.mul_add_distr_r in N3, N4. rewrite (Z.mul_comm dph dwpl) in N3. rewrite (Z.mul_comm sph swpl) in N4. lia. }
  assert (BD3 : 0 <= dh * dwpl /\ 0 <= dh * swpl) by (clear - BD WPLB; split; apply Z.mul_nonneg_nonneg; lia).
  assert (FWD : 0 <= dx / 32 <= 5000 /\ 0 <= sx / 32 <= 5000 /\ 0 <= dw / 32 <= 5000)
    by (clear - BD; repeat split; first [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (NB : (0 <= dx /\ 0 <= dy /\ 0 < dw /\ 0 < dh /\ dx + dw <= dpw /\ dy + dh <= dph /\ 0 <= sx /\ 0 <= sy /\ sx + dw <= spw /\ sy + dh <= sph
               /\ dpw <= 20000 /\ dph <= 20000 /\ spw <= 20000 /\ sph <= 20000)
            /\ (0 <= dy * dwpl /\ dy * dwpl + dh * dwpl <= dwpl * dph /\ 0 <= sy * swpl /\ sy * swpl + dh * swpl <= swpl * sph
                /\ 0 < dwpl <= 5001 /\ 0 < swpl <= 5001 /\ dwpl * dph <= 16777216 /\ swpl * sph <= 16777216)
            /\ (0 <= dh * dwpl /\ 0 <= dh * swpl)
            /\ (0 <= dx / 32 <= 5000 /\ 0 <= sx / 32 <= 5000 /\ 0 <= dw / 32 <= 5000)
            /\ 0 < datad /\ 0 < datas /\ datad + 4 * (dwpl * dph) <= 140737488355328 /\ datas + 4 * (swpl * sph) <= 140737488355328).
  { repeat split; try (clear - BD; lia); try (clear - BD2; lia); try (clear - BD3; lia); try (clear - FWD; lia); try assumption; lia. }
  hide NB.
  (* [comment removed for export] *)
  bwalk [0xa3b74] NB.
  lstep.
  bwalk2 [0xa5f80; 0xa5efc] NB.
  replace (Z.land datad 3) with 0 by (symmetry; change 3 with (Z.ones 2); rewrite Z.land_ones by lia; change (2 ^ 2) with 4; clear - D16; Z.div_mod_to_equations; lia).
  bwalk2 [0xa5f80] NB.
  cnb NB. cn NB.
  replace (spw - sx + (sx + dpw - dx + (dx + dw - dpw) - spw)) with (dw) by (clear; lia).
  set (nfw := dw / 32) in *.
  (* [comment removed for export] *)
  set (doff := dy * dwpl + dx / 32). set (soff := sy * swpl + sx / 32).
  replace (dwpl * dy * 4 + datad + dx / 32 * 4) with (datad + 4 * doff) by (unfold doff; clear; lia).
  replace (datas + (sx / 32 * 4 + swpl * sy * 4)) with (datas + 4 * soff) by (unfold soff; clear; lia).
  replace (swpl * sy * 4 + datas + sx / 32 * 4) with (datas + 4 * soff) by (unfold soff; clear; lia).
  (* [comment removed for export] *)
  lazymatch goal with FRx : rw_cells asegs _ (usp + -256) _ |- _ => pose proof FRx as FRc end.
  replace (datad + (dx / 32 * 4 + dwpl * dy * 4)) with (datad + 4 * doff) in FRc by (unfold doff; clear; lia).
  replace (Z.land datas 3) with 0 in FRc by (symmetry; change 3 with (Z.ones 2); rewrite Z.land_ones by lia; change (2 ^ 2) with 4; clear - S16; Z.div_mod_to_equations; lia).
  split_at FRc 4%nat FRA. split_at FRA 2%nat FRA2. split_at FRA2 6%nat FRB. split_at FRB 2%nat FRB2. clear FRc FRA2 FRB2.
  (* [comment removed for export] *)
  lazymatch goal with MUx : munch ?W m ?mm, WMx : wmono asegs m ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (ARTn : ART RT Σ mm)
      by (apply (art_client_writes RT AF Σ m mm lo W ART0 MUx WMx); [unfold STACK_WIN; lia|
          cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists datad, (4 * (dwpl * dph)); split; [exact DIN| lia]| exact I]]]);
    pose proof (af_acc_live RT AF Σ mm datad (4 * (dwpl * dph)) ARTn DIN) as (WRD & ACCD);
    pose proof (af_acc_live RT AF Σ mm datas (4 * (swpl * sph)) ARTn SIN) as (WRS & ACCS) end.
  apply wr_at_rw_CB in WRD; [| clear - DSZ; lia]. destruct WRD as (dbs & DBC).
  pose proof DBC as [[[DBL _] _] _]. cbn in DBL. apply u8arr_of_rw_cells in DBC.
  apply wr_at_rw_CB in WRS; [| clear - SSZ; lia]. destruct WRS as (sbs & SBC).
  pose proof SBC as [[[SBL _] _] _]. cbn in SBL. apply u8arr_of_rw_cells in SBC.
  lazymatch type of DBC with u8arr _ ?mm _ _ =>
    destruct (u8arr_u32arr mm datad dbs (dwpl * dph) DBC ltac:(rewrite DBL; clear - DSZ; lia)) as (wsd & UAD & UADL);
    destruct (u8arr_u32arr mm datas sbs (swpl * sph) SBC ltac:(rewrite SBL; clear - SSZ; lia)) as (wss & UAS & UASL) end.
  clear DBC SBC DBL SBL.
  assert (HD0 : lw = 0 -> dx / 32 + dw / 32 <= dwpl) by (clear - BD DWPL DX4; unfold lw; subst dwpl; intros; Z.div_mod_to_equations; lia).
  assert (HD1 : lw <> 0 -> dx / 32 + dw / 32 + 1 <= dwpl) by (clear - BD DWPL DX4; unfold lw; subst dwpl; intros; Z.div_mod_to_equations; lia).
  assert (HS0 : lw = 0 -> sx / 32 + dw / 32 <= swpl) by (clear - BD SWPL SX4; unfold lw; subst swpl; intros; Z.div_mod_to_equations; lia).
  assert (HS1 : lw <> 0 -> sx / 32 + dw / 32 + 1 <= swpl) by (clear - BD SWPL SX4; unfold lw; subst swpl; intros; Z.div_mod_to_equations; lia).
  assert (PRD : dy * dwpl + (dh - 1) * dwpl + dwpl <= dwpl * dph) by (clear - BD2; rewrite Z.mul_sub_distr_r; lia).
  assert (PRS : sy * swpl + (dh - 1) * swpl + swpl <= swpl * sph) by (clear - BD2; rewrite Z.mul_sub_distr_r; lia).
  eapply evt_cut.
  { eapply (bw_rows (Z.to_nat dh) 0) with (spz := usp + -256) (datad := datad) (datas := datas) (ld := dwpl * dph) (ls := swpl * sph) (dwpl := dwpl) (swpl := swpl)
      (doff := doff) (soff := soff) (dh := dh) (dwb := dw) (nfw := nfw) (lw := lw) (wsd := wsd) (wss := wss).
    all: lazymatch goal with
         | |- u32arr _ _ _ _ => eassumption
         | |- mem_inv _ _ => assumption
         | |- acc _ _ _ _ => assumption
         | |- Z.of_nat (length _) = _ => assumption
         | |- rw_cells _ _ _ _ => first [ replace (usp + -256 + 72) with (usp + -184) by (clear; lia); exact FRA
                                        | replace (usp + -256 + 136) with (usp + -120) by (clear; lia); exact FRB ]
         | |- _ => idtac
         end.
    all: unfold parked in *.
    all: lazymatch goal with
         | |- _ = _ mod 32 => reflexivity
         | |- _ = _ / 32 => reflexivity
         | |- _ mod 8 = 0 => clear - D16 S16; Z.div_mod_to_equations; lia
         | |- _ => idtac
         end.
    all: unfold SEGTOP_A, doff, soff, nfw in *; clear - BD BD2 WPLB HD0 HD1 HS0 HS1 PRD PRS FWD LWR D0 D16 S0 S16 CKR CKR0 CKS CKS0 CKH CKH0 DSAP SP0R SP0W LOW LOR USP SPT;
         intros; lia.
  }
  intros ms' PO. unfold bw_rows_exit in PO.
  destruct PO as (ra' & t0' & t1' & t2' & s0' & s1' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & s3' & s4' & s5' & s6' & s7' & s8'
                  & s9' & s10' & s11' & t3' & t4' & t5' & t6' & m' & wsd' & -> & MU' & WM' & MI' & UAD' & UADL' & UAS').
  clear ARTn ACCD ACCS FRA FRB.
  loop_art RT AF Σ m' lo MU'
    ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists datad, (4 * (dwpl * dph)); split; [solve [in_live_tac]| lia]| exact I]]).
  clear UAD' UADL' UAS' UAD UADL UAS UASL.
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
Qed.
End ROPLOW1.
