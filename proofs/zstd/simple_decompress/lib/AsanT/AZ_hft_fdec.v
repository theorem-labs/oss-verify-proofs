(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufFse.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree FseWalkKit FseRdKit FseRdKit2 ZdWalkKit ZdCellKit SepHide.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AProto AMalloc_iface AProg_kit AFake_iface AFakeK_iface FsKit
     AZ_kit AZ_globals AZ_globalsR AZ_fkit AZ_huf_iface AZ_hft_iface AZ_fserd_iface AF_fse_rd_base AF_fse_rd_mem
     AZ_hft_rstats_a AZ_hft_fdec_defs AZ_hft_fdec_epi AZ_hft_fdec_pro AZ_hft_fdec_close AZ_hft_fdec_open AZ_hft_fdec_call
     AZ_hft_initds AZ_hft_initds_fin AZ_hft_dsym AZ_hft_fdec_mid AZ_hft_fdec_fz AZ_hft_fdec_nzf.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.
Notation FB0 F := (mkABlock (ABFake 0) F 64).

Section Asm.
Variable AI : AMallocIface.
Variable fflag : alayout -> Z -> Z -> Z.
Variable rng_fs : alayout -> footprint -> Prop.
Hypothesis FFLAG : fake_flag_law AI fflag.
Hypothesis FREL : fake_release_law AI fflag.
Hypothesis SM0K : forall k, Z.of_nat k < 16384 -> stack_malloc_0k_stmt AI fflag rng_fs k.
Hypothesis FHL : fake_heap_law AI.
Hypothesis READ : fse_read_any_stmtA AI rng_fs.
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem fse_dec_proofA : fse_dec_stmtA AI rng_fs.
Proof.
  unfold fse_dec_stmtA.
  intros L RNG st LB ra gp tp t0 t1 t2 s0 s1 bmi2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SPV DST cap SRC n ml WK wksz lo src.
  intros AFP AZS TP AROC ADST INDST ASRC HULLS INSRC WKA AWK HULLW INWK MI STK LO0 LOS SPR SD DSTL CAPR DSTH SB LSB SRCL NH SRCH SW WKL WR WKH MLR
         OFFDST OFFWK OFFSRC DSTWK DSTSRC WKSRC.
  destruct AFP as (AH & ASH & ART & (KLO & RSTK & RI) & RFS & BOT & SPT & SP16 & RSTK2 & LBH).
  pose proof (ashort_fake_le LB 3 0 ASH ltac:(clear; lia)) as FLE. change (Z.to_nat (4096 - 3)) with 4093%nat in FLE.
  destruct ASRC as (ABS & USRC & RSRC & RSSRC).
  pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & LY4 & _).
  pose proof atop_range as ATR.
  pose proof (fspb_props SPV SP16) as (SPAB & SPA32).
  assert (UD : 0 < cap -> unpoisoned m DST (DST + cap)) by (intros CP; destruct (ADST CP) as (_ & U & _); exact U).
  assert (UW : 0 < wksz -> unpoisoned m WK (WK + wksz)) by (intros WP; destruct (AWK WP) as (_ & U & _); exact U).
  assert (US : 0 < n -> unpoisoned m SRC (SRC + n)) by (intros _; exact USRC).
  assert (N0 : 0 <= n) by (clear - LSB; lia).
  eapply evtF_cut; [| intros ms' H; exact H].
  eapply (fd_openZ AI fflag rng_fs SM0K FHL 4093%nat L RNG st LB ra gp tp t0 t1 t2 s0 s1 bmi2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
            SPV DST cap SRC n ml WK wksz lo src (fun ms => evtF bsegs RNG _ ms)).
  all: lazymatch goal with
       | |- Z.of_nat _ < _ => clear; cbn; lia
       | |- forall FF m3, _ => idtac
       | |- 0 < _ -> ainimg _ _ _ => intros _; exact INSRC
       | |- _ => first [assumption | exact UD | exact UW | exact US | lia | lazymatch goal with |- ?G => idtac "OPEN-LEFT:" G end]
       end.
  - (* [comment removed for export] *)
    intros FF m3 jA' w8 w16 w24 j32 j48 j64 j80 j24 tlw j36 j52 y1 y5 y6 y7 y10 y11 y12 y13 y14 y16 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31
           F64 FH FC RFF RSFF FFD FFA1 FFA2 AH3 MU03 WM03 FFR03 MI3 FRB3 FRA3 FFC3 SHF3 STL3 STG3 SD3 UD3 SW3 UW3 SB3 US3 WLT.
    pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in FHa.
    unfold FDHDR in FFC3. unfold FDFRAME in FRA3.
    pose proof (proj1 (rd_rw_cells_appA bsegs m3 FF [C8 (Z_to_bv 64 0x41b58ab3)] _) FFC3) as [FF03 _].
    pose proof (proj1 (rd_rw_cells_appA bsegs m3 FF [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x1d982); C8 (Z_to_bv 64 0xabea0); CB 8 j24; C4 tlw; CB 12 j36; C4 (Z_to_bv 64 255); CB 4 j52] _) FFC3) as [_ FF563].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FF563.
    lazymatch type of FF563 with rw_cells _ _ ?a _ => replace a with (FF + 56) in FF563 by (cbn; lia) end.
    assert (STA3 : stk bsegs m3 lo (SPV + -104)).
    { pose proof FRA3 as X. apply stk_of_rw_cells in X. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in X.
      lazymatch type of X with stk _ _ _ ?e => replace e with (FSPB SPV + 120) in X by (cbn; lia) end.
      apply (stk_merge bsegs m3 lo (FSPB SPV) (SPV + -104) STL3); [| clear - SPAB LOS LO0; lia].
      apply (stk_merge bsegs m3 (FSPB SPV) (FSPB SPV + 120) (SPV + -104) X); [exact STG3| clear - SPAB; lia]. }
    assert (MU03' : munch ([(DST, DST + cap); (WK, WK + wksz); (SPV - 4992, SPV)] ++ fake_area L) m m3).
    { eapply munch_weaken; [| exact MU03]. intros x Hx. cbn [outside app fake_area] in *. clear - Hx. tauto. }
    assert (FFR03' : ffr_pres [(DST, DST + cap); (WK, WK + wksz)] LB m m3) by (apply fd_ffr_pres_mono_nil; exact FFR03).
    eapply fd_exit_gen.
    all: lazymatch goal with
         | |- fake_flag_law _ _ => exact FFLAG
         | |- fake_release_law _ _ => exact FREL
         | |- forall b, In b _ -> _ => exact FFD
         | |- zd_is_error _ = true \/ _ => left; reflexivity
         | |- rw_cells _ _ _ _ => eassumption
         | |- stk _ _ _ (_ + -104) => exact STA3
         | |- munch _ _ _ => exact MU03'
         | |- ffr_pres _ _ _ _ => exact FFR03'
         | |- _ => first [assumption | lia | unfold KHIGH; lia | lazymatch goal with |- ?G => idtac "EXIT-LEFT:" G end]
         end.
  - (* [comment removed for export] *)
    intros FF m3 jA' j32 j48 j64 j80 j24 tlw j36 j52 y5 y6 y7 y16 y28 y29 y30 y31
           F64 FH FC RFF RSFF FFD FFA1 FFA2 AH3 MU03 WM03 FFR03 MI3 FRB3 FRA3 FFC3 SHF3 STL3 STG3 SD3 UD3 SW3 UW3 SB3 US3 WGE.
    destruct (AWK ltac:(clear - WGE; lia)) as (ABW & _ & RWK & RSWK).
    eapply fd_kcall.
    all: lazymatch goal with
         | |- fake_flag_law _ _ => exact FFLAG
         | |- fake_release_law _ _ => exact FREL
         | |- fake_heap_law _ => exact FHL
         | |- fse_read_any_stmtA _ _ => exact READ
         | |- forall b, In b _ -> _ => exact FFD
         | |- 0 < _ -> rng _ (shad _) _ => first [assumption | intros CP; destruct (ADST CP) as (_ & _ & _ & R); exact R]
         | |- 0 < _ -> rng _ _ _ => first [assumption | intros CP; destruct (ADST CP) as (_ & _ & R & _); exact R]
         | |- rw_cells _ _ _ _ => eassumption
         | |- zlen _ = _ => exact LSB
         | |- bytes_at _ _ _ _ => exact SB3
         (* [comment removed for export] *)
         | |- forall mA hs tl fast tb, _ -> _ -> fast = 1 -> _ =>
             intros mA hs tl fast tb HYx ANx F1;
             eapply fd_fast_half;
             first [exact HYx | exact ANx | exact F1 | apply fd_qx | apply fd_qxc | exact fse_initds_proofA]
         | |- forall mA hs tl fast tb, _ -> _ -> fast = 0 -> _ => intros mA hs tl fast tb HYx ANx F0; exact (nonfh RNG mA SPV (FSPB SPV) lo DST cap SRC n WK wksz hs tl fast FF tb src gp tp F fc HYx ANx F0)
         | |- _ => first [assumption | lia | lazymatch goal with |- ?G => idtac "KCALL-LEFT:" G end]
         end.
Qed.
End Asm.
End CANSEC1.
