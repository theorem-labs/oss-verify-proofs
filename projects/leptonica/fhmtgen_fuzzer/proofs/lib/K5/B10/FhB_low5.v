(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import ImageA.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import Layout.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit D_iface D_defs D_libiface Gm_iface Fh_iface LeptB_guard LeptB_guard2 Fh_lowkit FhB_guard FhB_low5_loop.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac subfp_tac ::= clear; let z := fresh "z" in let Hz := fresh "Hz" in intros z Hz; cbn [outside] in Hz |- *; first [tauto | lia].

Section K5.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.

Lemma fhl5_ok : fhl_case RT 5.
Proof using AF GP.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    rd rs w h wpl FDO MST -> -> -> -> -> -> -> -> WP HP WCAP HCAP WPL CHD CHS DNE ENV.
  unfold lpost, lenv, keeps, keepsL, chunk in *.
  destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct CHD as (DIN & D0 & D16 & DSZ). destruct CHS as (SIN & S0 & S16 & SSZ).
  pose proof (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_fhmtgen_low_1, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  set (ld := wpl * (h + 64)) in *.
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a /\ outside [(rd, rd + 4 * ld)] a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  pose proof ST as (STa & STb & _).
  pose proof (live_apart RT AF Σ m rd (4 * ld) rs (4 * ld) ART0 DIN SIN DNE) as DSAP.
  chunk_facts RT AF GP rd (4 * ld).
  chunk_facts RT AF GP rs (4 * ld).
  refresh RT AF. unfold shad, SHB in *. park_disj.
  (* [comment removed for export] *)
  walk_to AF MST [(usp - 304, usp); (rd, rd + 4 * ld)] [0xb3038].
  assert (WPLB : 0 < wpl <= 627) by (clear - WPL WP WCAP; subst wpl; Z.div_mod_to_equations; lia).
  assert (BD : 0 < w /\ w + 64 <= 20000 /\ 0 < h /\ h + 64 <= 20000 /\ 0 < wpl <= 627) by lia.
  awalk [0xb3240].
  lazymatch goal with H : rw_cells asegs _ (usp + -304) _ |- _ => rename H into FR end.
  repeat match goal with |- context [bv_swrap 32 ?z] =>
    rewrite (bv_swrap_small 32 z) by (change (bv_half_modulus 32) with (2^31); clear - BD; lia) end.
  repeat match goal with |- context [?E mod 18446744073709551616] =>
    rewrite (Z.mod_small E 18446744073709551616) by (clear - BD; lia) end.
  rewrite ?(bv_swrap_small 32 (w + 31)) in FR by (change (bv_half_modulus 32) with (2^31); clear - BD; lia).
  rewrite ?(Z.mod_small (w + 31) 18446744073709551616) in FR by (clear - BD; lia).
  assert (EPW : bv_swrap 32 (bv_wrap 32 (w + 31) / 32) = (w + 31) / 32).
  { unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with (2^32). rewrite (Z.mod_small (w + 31)) by (clear - BD; lia).
    apply bv_swrap_small. change (bv_half_modulus 32) with (2^31). clear - BD.
    split; [apply Z.le_trans with 0; [lia| apply Z.div_pos; lia] | apply Z.div_lt_upper_bound; lia]. }
  rewrite ?EPW in FR. rewrite ?EPW. clear EPW.
  repeat match type of FR with context [bv_swrap 32 ?z] =>
    rewrite (bv_swrap_small 32 z) in FR by (change (bv_half_modulus 32) with (2^31); clear - BD; lia) end.
  repeat match type of FR with context [?E mod 18446744073709551616] =>
    rewrite (Z.mod_small E 18446744073709551616) in FR by (clear - BD; lia) end.
  set (pw := (w + 31) / 32) in *.
  assert (PWB : 1 <= pw /\ pw + 2 <= wpl) by (clear - BD WPL; unfold pw; subst wpl; Z.div_mod_to_equations; lia).
  set (q0 := 32 * wpl + 1) in *.
  (* [comment removed for export] *)
  canon_regz 5 (6 * wpl).
  canon_regz 10 (- (rs + 4 * (q0 + 0 + 2 * wpl))).
  canon_regz 13 (rd + 4 * (q0 + 0)).
  canon_regz 21 (- (rs + 4 * (q0 + 0 - 2 * wpl))).
  canon_regz 22 (rs + 4 * (q0 + 0 - 6 * wpl)).
  canon_regz 23 (- (rs + 4 * (q0 + 0 + 6 * wpl))).
  canon_regz 24 (rs + 4 * (q0 + 0 + 2 * wpl)).
  canon_regz 25 (rs + 4 * (q0 + 0 - 2 * wpl)).
  canon_regz 26 (- (rs + 4 * (q0 + 0 - 6 * wpl))).
  canon_regz 31 (2 * wpl).
  split_at FR 1%nat FRB. split_at FRB 22%nat FRC.
  lazymatch goal with H : rw_cells ?sg ?mm (usp + -280) [C8 ?c0; C8 ?c1; C8 ?c2; C8 ?c3; C8 ?c4; C8 ?c5; C8 ?c6; C8 ?c7; C8 ?c8; C8 ?c9; C8 ?c10; C8 ?c11; C8 ?c12; C8 ?c13; C8 ?c14; C8 ?c15; C8 ?c16; C8 ?c17; C8 ?c18; C8 ?c19; C8 ?c20; C8 ?c21] |- _ =>
    let N := fresh "CAN" in
    assert (N : rw_cells sg mm (usp + -280) [C8 (Z_to_bv 64 (- (rs + 4 * (q0 - 2 * wpl)))); C8 (Z_to_bv 64 (- (rs + 4 * (q0 + 2 * wpl)))); C8 (Z_to_bv 64 (rs + 4 * (q0 - 2 * wpl))); C8 (Z_to_bv 64 (rs + 4 * (q0 + 2 * wpl))); C8 (Z_to_bv 64 (- (rs + 4 * (q0 - 6 * wpl)))); C8 (Z_to_bv 64 (- (rs + 4 * (q0 + 6 * wpl)))); C8 (Z_to_bv 64 (rs + 4 * (q0 - 6 * wpl))); C8 (Z_to_bv 64 (rs + 4 * (q0 + 6 * wpl))); C8 c8; C8 (Z_to_bv 64 (wpl)); C8 c10; C8 c11; C8 c12; C8 c13; C8 c14; C8 (Z_to_bv 64 (0)); C8 (Z_to_bv 64 (0)); C8 (Z_to_bv 64 (wpl)); C8 (Z_to_bv 64 (rd + 4 * q0)); C8 (Z_to_bv 64 (rs + 4 * q0)); C8 (Z_to_bv 64 (rs + 4 * (q0 + 0 + 6 * wpl))); C8 (Z_to_bv 64 (rs + 4 * (q0 + 0)))])
      by (replace [C8 (Z_to_bv 64 (- (rs + 4 * (q0 - 2 * wpl)))); C8 (Z_to_bv 64 (- (rs + 4 * (q0 + 2 * wpl)))); C8 (Z_to_bv 64 (rs + 4 * (q0 - 2 * wpl))); C8 (Z_to_bv 64 (rs + 4 * (q0 + 2 * wpl))); C8 (Z_to_bv 64 (- (rs + 4 * (q0 - 6 * wpl)))); C8 (Z_to_bv 64 (- (rs + 4 * (q0 + 6 * wpl)))); C8 (Z_to_bv 64 (rs + 4 * (q0 - 6 * wpl))); C8 (Z_to_bv 64 (rs + 4 * (q0 + 6 * wpl))); C8 c8; C8 (Z_to_bv 64 (wpl)); C8 c10; C8 c11; C8 c12; C8 c13; C8 c14; C8 (Z_to_bv 64 (0)); C8 (Z_to_bv 64 (0)); C8 (Z_to_bv 64 (wpl)); C8 (Z_to_bv 64 (rd + 4 * q0)); C8 (Z_to_bv 64 (rs + 4 * q0)); C8 (Z_to_bv 64 (rs + 4 * (q0 + 0 + 6 * wpl))); C8 (Z_to_bv 64 (rs + 4 * (q0 + 0)))] with [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c7; C8 c8; C8 c9; C8 c10; C8 c11; C8 c12; C8 c13; C8 c14; C8 c15; C8 c16; C8 c17; C8 c18; C8 c19; C8 c20; C8 c21]; [exact H| cells_eq]);
    clear H end.
  (* [comment removed for export] *)
  lazymatch goal with WMx : wmono asegs m ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (wr_at_transport asegs m mm rd (4 * ld) (proj1 (af_acc_live RT AF Σ m rd (4 * ld) ART0 DIN)) WMx) as WRD;
    pose proof (wr_at_transport asegs m mm rs (4 * ld) (proj1 (af_acc_live RT AF Σ m rs (4 * ld) ART0 SIN)) WMx) as WRS end.
  apply wr_at_rw_CB in WRD; [| clear - DSZ; lia]. destruct WRD as (dbs & DBC).
  pose proof DBC as [[[DBL _] _] _]. cbn in DBL. apply u8arr_of_rw_cells in DBC.
  apply wr_at_rw_CB in WRS; [| clear - SSZ; lia]. destruct WRS as (sbs & SBC).
  pose proof SBC as [[[SBL _] _] _]. cbn in SBL. apply u8arr_of_rw_cells in SBC.
  lazymatch type of DBC with u8arr _ ?mm _ _ =>
    destruct (u8arr_u32arr mm rd dbs ld DBC ltac:(rewrite DBL; clear - DSZ; lia)) as (wsd & UAD & UADL);
    destruct (u8arr_u32arr mm rs sbs ld SBC ltac:(rewrite SBL; clear - SSZ; lia)) as (wss & UAS & UASL) end.
  clear DBC SBC DBL SBL.
  assert (LDE : ld = wpl * h + 64 * wpl) by (unfold ld; clear; lia).
  assert (HW : 0 <= (h - 1) * wpl /\ (h - 1) * wpl + wpl = wpl * h) by (clear - BD; split; [apply Z.mul_nonneg_nonneg; lia| lia]).
  eapply evt_cut.
  { eapply (fb5_rows (Z.to_nat h) 0) with (rs := rs) (rd := rd) (q0 := q0) (wpl := wpl) (pw := pw) (w31 := w + 31) (h := h) (iw := 0) (ls := ld) (ld := ld)
      (fb := usp + -304) (wss := wss) (wsd := wsd).
    all: lazymatch goal with
         | |- u32arr _ _ _ _ => eassumption
         | |- mem_inv _ _ => assumption
         | |- Z.of_nat (length _) = _ => assumption
         | |- _ = Z_to_bv 64 _ => reflexivity
         | |- rw_cells _ _ _ _ => replace (usp + -304 + 24) with (usp + -280) by (clear; lia); eassumption
         | |- _ => idtac
         end.
    all: unfold parked in *.
    all: lazymatch goal with
         | |- acc _ _ _ _ => assumption
         | |- _ => idtac
         end.
    all: try (unfold SEGTOP_A, q0 in *; clear - BD PWB HW LDE WPLB D0 D16 S0 S16 DSZ SSZ CKR CKR0 CKS CKS0 CKH CKH0 DSAP SP0R SP0W LOW LOR USP SPT SPA SPB STa STb;
              first [lia | Z.div_mod_to_equations; lia]).
    all: unfold ld; clear - BD; nia. }
  intros ms' PO. unfold fb5_exit in PO.
  destruct PO as (ra' & t0' & t1' & t2' & s0' & s1' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & s3' & s4' & s5' & s6' & s7' & s8' & s9' & s10' & s11' & t3' & t4' & t5' & t6' & x24' & x32' & x40' & x48' & x56' & x64' & x72' & x80' & x88' & x96' & x104' & x112' & x120' & x128' & x136' & x144' & x152' & x160' & x168' & x176' & x184' & x192' & m' & -> & MU' & WM' & MI' & SL').
  repeat match goal with H : rw_cells asegs _ (usp + -280) _ |- _ => clear H end. clear UAD UADL UAS UASL.
  loop_art RT AF Σ m' lo MU'
    ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists rd, (4 * ld); split; [solve [in_live_tac]| lia]| exact I]]).
  lazymatch type of MU' with munch _ ?mm m' =>
    loop_transport mm m' MU' ltac:(fun Hx => clear - Hx CKR CKS CKH CKR0 CKS0 CKH0 LOW LOR SPT SPB STa USP SP0R SP0W; unfold parked in *; lia) end.
  clear MU' WM'.
  replace (usp + -304 + 24) with (usp + -280) in SL' by (clear; lia).
  join_cells FR SL'. join_cells FR FRC.
  cwalk (@nil Z).
  cps_stop.
  agf_munch AGF MU ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct Hx as [_ HxO]; cbn [outside] in HxO;
                                   split; [lia| split; [tauto| exact I]]).
  apply cps_finish. intros c Hc. subst QF. cbv beta.
  exists Σ. eexists.
  split; [| repeat split; first [reflexivity | lia]].
  eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists. split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
  split; [split; [split; [exact ARTl| split; [exact MI'| split; [| assumption]]]| split; assumption]|].
  - repeat match goal with H : wmono asegs _ _ |- _ => revert H end. clear. intros. eauto using wmono_trans.
  - intros a Ha Ho. exact (AGF a (conj Ha Ho)).
Qed.
End K5.
