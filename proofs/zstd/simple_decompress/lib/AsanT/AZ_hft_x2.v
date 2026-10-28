(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufStats ZdHufX1 ZdHufX2.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree FseWalkKit FseRdKit FseRdKit2 ZdWalkKit ZdCellKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AProto AMalloc_iface AProg_kit AFake_iface AFakeK_iface
     AZ_kit AZ_globals AZ_globalsR AZ_fkit AZ_huf_iface AZ_hft_iface AZ_hft_rs_iface AF_fse_rd_base AF_fse_rd_mem AF_fse_rd_seg AF_fse_rd_asm
     AZ_libc_iface AZ_libc AZ_hft_x1_seg AZ_hft_x1_env AZ_hft_x1_call AZ_hft_x1_defs AZ_hft_x2_geo AZ_hft_x2_seg AZ_hft_x2_env AZ_hft_x2_call
     AZ_hft_x2_kit AZ_hft_x2h_defs AZ_hft_x2_defs AZ_hft_x2_facts AZ_hft_x2_l2i AZ_hft_x2_body AZ_hft_x2_k4 AZ_hft_x2_w2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RZ_hft_x1_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKitF.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

(* [comment removed for export] *)
Lemma x2pref_tbl : forall T dt, x2pref T (2^T) dt -> zlen dt = 16388 -> Forall (fun v : Z => 0 <= v < 256) dt -> 11 <= T <= 12 ->
  Znth 0 dt = 12 -> Znth 1 dt = 1 -> Znth 2 dt = T ->
  huf_hdr_ok (map (Z_to_bv 8) dt) /\ huf_tbl_ok (map (Z_to_bv 8) dt) /\ nth_error (map (Z_to_bv 8) dt) 1 = Some (Z_to_bv 8 1).
Proof.
  intros T dt PC L BY TR P0 P1 P2.
  assert (P2TL : 2^T <= 4096) by (change 4096 with (2^12); apply Z.pow_le_mono_r; lia).
  assert (NE : forall i, 0 <= i < zlen dt -> nth_error (map (Z_to_bv 8) dt) (Z.to_nat i) = Some (Z_to_bv 8 (Znth i dt))) by (intros i Hi; apply nth_error_map_Znth; lia).
  assert (HDR : huf_hdr_ok (map (Z_to_bv 8) dt)).
  { split; [unfold HUF_DTABLE_BYTES; rewrite length_map; exact L|]. change 0%nat with (Z.to_nat 0). rewrite NE by lia. rewrite P0. reflexivity. }
  split; [exact HDR|]. split.
  - split; [exact HDR|]. exists (Z_to_bv 8 1), T. split; [change 1%nat with (Z.to_nat 1); rewrite NE by lia; rewrite P1; reflexivity|].
    split; [change 2%nat with (Z.to_nat 2); rewrite NE by lia; rewrite P2; reflexivity|]. split; [lia|].
    split.
    + intros _ i Hi. exists (Z_to_bv 8 (Znth (4 * i + 7) dt)). split; [apply NE; lia|].
      pose proof (PC i Hi) as [_ B]. pose proof (Forall_Znth _ dt (4 * i + 7) BY ltac:(lia)) as R. cbv beta in R.
      rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_small by lia. lia.
    + replace (negb (bv_unsigned (Z_to_bv 8 1) =? 0)) with true by reflexivity.
      intros i Hi. exists (Z_to_bv 8 (Znth (4 * i + 6) dt)). split; [apply NE; lia|].
      pose proof (PC i Hi) as [B _]. pose proof (Forall_Znth _ dt (4 * i + 6) BY ltac:(lia)) as R. cbv beta in R.
      rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_small by lia. lia.
  - change 1%nat with (Z.to_nat 1). rewrite NE by lia. rewrite P1. reflexivity.
Qed.

Section CANSEC1. Context {rc : runConstT}.
Section Asm.
Variable AI : AMallocIface.
Variable fflag : alayout -> Z -> Z -> Z.
Variable rng_fs : alayout -> footprint -> Prop.
Hypothesis FFLAG : AFakeK_iface.fake_flag_law AI fflag.
Hypothesis FREL : AFakeK_iface.fake_release_law AI fflag.
Hypothesis SM0K : forall k, Z.of_nat k < 16384 -> stack_malloc_0k_stmt AI fflag rng_fs k.
Hypothesis FHL : fake_heap_law AI.
Hypothesis RS : huf_rstats_stmtA AI rng_fs.
Notation FB0 F := (mkABlock (ABFake 0) F 64).
Theorem huf_rdx2_proofA : huf_rdx2_stmtA AI rng_fs.
Proof.
  unfold huf_rdx2_stmtA, huf_rd_stmtA_at.
  intros L RNG st LB ra gp tp t0 t1 t2 s0 s1 flags a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FRm fc m SPV SRC n DT WK wksz lo src dtb
         MI ST LO0 LOS SPR SB LSB SRCL NR SRH TB HDR DTL DTH DT4 WKS WKL WR WKH WK4 SDS SWS SSS DTWK DTSRC WKSRC AFP AZS TP ARO ASRC INS HSRC ADT HDT IND AWK HWK INW.
  destruct AFP as (AH & ASH & ART & (KLO & RSTK & RI) & RFS & BOT & SPT & SP16 & RSTK2 & LBH).
  pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & LY4 & _).
  pose proof (ashort_fake_le LB 4 0 ASH ltac:(clear; lia)) as FLE. change (Z.to_nat (4096 - 4)) with 4092%nat in FLE.
  pose proof HDR as [LTB DT0].
  destruct (ADT ltac:(unfold HUF_DTABLE_BYTES; clear; lia)) as (ABD & UD & RDT & RSDT).
  assert (RSD1 : rng RNG (shad DT) 1) by (eapply rng_sub'; [exact RSDT| unfold shspan, HUF_DTABLE_BYTES; rewrite !shad_div; unfold ASHOFF; clear; Z.div_mod_to_equations; lia]).
  destruct (stk_open bsegs m WK (WK + wksz) WK (Z.to_nat wksz) WKS ltac:(lia) ltac:(lia)) as (jw & WC & _ & _).
  eapply evtF_cut; [| cbv beta; intros ms' HQ; exact HQ].
  eapply (x2_openZ AI fflag rng_fs SM0K FHL 4092%nat L RNG st LB ra gp tp t0 t1 t2 s0 s1 flags a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FRm fc m
            SPV DT WK wksz SRC n lo dtb src jw
            (fun ms => evtF bsegs RNG (huf_rd_postA AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FRm fc SPV DT WK wksz lo true m) ms));
    first [ exact AH| exact FLE| exact LBH| exact RI| exact RSTK2| exact RFS| exact BOT| exact LOS| exact SP16| exact ST| exact MI| exact TP| exact TB| exact DT0| exact IND| exact UD
          | exact SDS| exact DTL| exact DTH| exact DT4| exact RDT| exact RSD1| exact WC| exact INW| exact SWS| exact WKH| exact WK4| exact WKL| exact SB| exact LSB| exact INS| exact SSS
          | intros NP; destruct (AWK NP) as (_ & U & _); exact U
          | intros NP; destruct (ASRC NP) as (_ & U & _); exact U
          | clear - LY3 SPT; lia | clear; cbn; lia | clear - LTB; unfold HUF_DTABLE_BYTES in *; lia | clear - WR; lia | clear - NR LSB; lia
          | clear - WKL; lia | clear - SRCL; lia | clear - SRH; lia
          | lazymatch goal with |- ?G => idtac "LEFT:" G end ].
  - (* [comment removed for export] *)
    intros FF m3 j3 y5 y6 y7 y12 y28 y29 y30 y31
           F64 FH FC RFF RSFF FFD FFA1 FFA2 AH3 MU03 WM03 FFR03 MI3 FRB3 FA2 STL3 STG3 FFC3 SHF3 TB3 UD3 WC3 UW3 SB3 US3 WSMALL.
    pose proof (spa2_props SPV SP16) as (SPAB & SPA32 & _).
    unfold X2FFHDR in FFC3.
    pose proof (proj1 (rw_cells_app bsegs _ _ [C8 (Z_to_bv 64 X2_MAGIC_LIVE)] _) FFC3) as [FH0 FH1].
    pose proof (proj2 (proj1 (rw_cells_app bsegs _ _ [C8 (Z_to_bv 64 X2_MAGIC_LIVE); C8 (Z_to_bv 64 X2_DESC); C8 (Z_to_bv 64 0x97374); CB 32 j3] _) FFC3)) as FH5.
    cbn [cells_size csize Nat.add] in FH5.
    apply stk_of_rw_cells in WC3. cbn [cells_size csize Nat.add] in WC3.
    eapply (x2_closeZ AI fflag FFLAG FREL L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FRm fc m m3 SPV DT WK wksz lo FF 18446744073709551615 dtb);
      first [ exact AH3| exact LBH| exact F64| exact FH| exact FC| exact RFF| exact RSFF| exact FFD| exact FFA1| exact FFA2| exact WM03| exact MI3| exact SHF3| exact FH0| exact FRB3
            | exact FA2| exact STL3| exact STG3| exact BOT| exact LOS| exact SP16| exact RSTK2| exact RI| exact IND| exact INW| exact TB3| exact HDR
            | eapply munch_weaken; [| exact MU03]; intros x Hx; cbn [outside app fake_area] in *; clear - Hx; lia
            | apply AZ_hft_x1_env.ffr_pres_mono_nil1; exact FFR03
            | match type of FH5 with rw_cells _ _ ?a _ => replace a with (FF + 56) in FH5 by lia end; exact FH5
            | match type of WC3 with stk _ _ _ ?h => replace h with (WK + wksz) in WC3 by lia end; exact WC3
            | clear - LY3 SPT; lia | clear - DTH; unfold HUF_DTABLE_BYTES in *; lia | clear - WKH; lia | clear - WR; lia | clear; lia
            | intros E; exfalso; clear - E; cbv in E; discriminate E
            | lazymatch goal with |- ?G => idtac "LEFT:" G end ].
  - (* [comment removed for export] *)
    intros FF m3 jA jB jC jD j3 y5 y6 y7 y28 y29 y30 y31 hdw
           F64 FH FC RFF RSFF FFD FFA1 FFA2 AH3 MU03 WM03 FFR03 MI3 FRB3 FRA3 FFC3 SHF3 STG3 TB3 UD3 WC3 UW3 SB3 US3 WBIG HM HR HLE4 STL3.
    pose proof (spa2_props SPV SP16) as (SPAB & SPA32 & _).
    destruct (AWK ltac:(lia)) as (ABW & _ & RW & RSW).
    cbv beta. eapply evtF_cut; [| cbv beta; intros ms' HQ; exact HQ].
    eapply (x2_callZ AI fflag rng_fs FHL RS L RNG st LB ra gp tp s0 s1 flags s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FRm fc m m3 SPV DT WK wksz SRC n lo FF hdw dtb src jw jA jB jC jD j3
              y5 y6 y7 y28 y29 y30 y31 (fun ms => evtF bsegs RNG (huf_rd_postA AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FRm fc SPV DT WK wksz lo true m) ms));
      first [ exact ASH| exact LBH| exact RI| exact RSTK2| exact RFS| exact KLO| exact BOT| exact LOS| exact SP16| exact TP| exact ARO| exact AZS| exact ABW| exact RW| exact RSW
            | exact HWK| exact INW| exact WK4| exact SWS| exact LSB| exact SSS| exact WKSRC| exact ASRC| exact INS| exact HSRC| exact LTB| exact IND| exact SDS| exact DTWK
            | exact F64| exact FH| exact FC| exact RFF| exact RSFF| exact FFD| exact FFA1| exact FFA2| exact HR| exact HM| exact AH3| exact MU03| exact WM03| exact FFR03| exact MI3
            | exact FRB3| exact FRA3| exact FFC3| exact SHF3| exact STG3| exact TB3| exact UD3| exact WC3| exact SB3| exact US3| exact STL3
            | apply UW3; clear - WBIG; lia
            | clear - LY3 SPT; lia | clear - WKL; lia | clear - WKH; lia | clear - WR WBIG; lia | clear - SRCL; lia | clear - NR LSB; lia | clear - SRH; lia
            | clear - DTH; unfold HUF_DTABLE_BYTES in *; lia
            | intros NP; destruct (ASRC NP) as (A1 & _ & A2 & A3); split; [exact A1| split; [exact A2| exact A3]]
            | lazymatch goal with |- ?G => idtac "LEFT:" G end ].
    + (* [comment removed for export] *)
      intros m5 r z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z18 z19 z20 z21 z22 z23 z24 z25 z27 z28 z29 z30 z31 ERR Hr AH5 MU05 WM05 MI5 FFR05 SHF5 FH05 FH565 FRB5 FA5 STL5 STG5 TB5 STW5.
      cbv beta.
      eapply (x2_closeZ AI fflag FFLAG FREL L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FRm fc m m5 SPV DT WK wksz lo FF r dtb);
        first [ exact AH5| exact LBH| exact F64| exact FH| exact FC| exact RFF| exact RSFF| exact FFD| exact FFA1| exact FFA2| exact MU05| exact WM05| exact MI5| exact FFR05
              | exact SHF5| exact FH05| exact FH565| exact FRB5| exact FA5| exact STL5| exact STG5| exact BOT| exact LOS| exact SP16| exact RSTK2| exact RI| exact IND| exact INW
              | exact TB5| exact HDR| exact STW5| exact Hr
              | clear - LY3 SPT; lia | clear - DTH; unfold HUF_DTABLE_BYTES in *; lia | clear - WKH; lia | clear - WR; lia
              | intros E; rewrite ERR in E; discriminate E
              | lazymatch goal with |- ?G => idtac "LEFT:" G end ].
    + (* [comment removed for export] *)
      intros m5 r nbs tl hw rank j4 j5 j6 z1 z5 z6 z7 z14 z15 z16 z17 z28 z29 z30 z31
             NER RR HR5 HM5 AH5 MU05 WM05 MI5 FFR05 FRB5 FRA5 LJA LJB LJC LJD FFC5 SHF5 STG5 STL5 TB5 UD5 HW5 LHW BHW RK5 RS05 W15 W25 WKR5 UW5 STATS NBSR.
      cbv beta.
      pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in FHa.
      pose proof (fk_inblk_apart AI _ _ _ _ _ _ _ _ WK wksz AH3 INW ltac:(lia)) as DFW.
      pose proof (fk_inblk_apart AI _ _ _ _ _ _ _ _ DT HUF_DTABLE_BYTES AH3 IND ltac:(unfold HUF_DTABLE_BYTES; lia)) as DFD.
      assert (ART5 : art m5) by (apply AZ_hft_x1_call.artcells_art; exact (AI_rtcells AI _ _ _ _ _ AH5)).
      assert (HY : x2A_hyps RNG SPV (SPA2 SPV) lo DT WK wksz FF).
      { unfold x2A_hyps. unfold HUF_DTABLE_BYTES in *. pose proof atop_range as ATR.
        repeat match goal with |- _ /\ _ => split end;
        first [ exact ABD| exact RDT| exact RSDT| exact ABW| exact RW| exact RSW| exact RFF| exact RI| exact F64| exact FC| exact FH| exact DFD| exact DFW| exact WK4| exact DT4| exact SP16| exact SPA32| exact KLO| exact BOT
              | eapply rng_sub'; [exact RSTK2| clear - LY3 SPT LOS LO0; lia]
              | clear - DTL DTH WKL WKH WR WBIG LOS SPT LY3 SPAB SDS SWS DTWK FHa FHb FHc DFD DFW; lia
              | lazymatch goal with |- ?G => idtac "HYLEFT:" G end ]. }
      (* [comment removed for export] *)
      destruct (X2FRA_as_F m5 (SPA2 SPV) FF DT WK hdw jA jB jC jD FRA5)
        as (k0 & k8 & k16 & k24 & k32 & k40 & k48 & k72 & k80 & k88 & k104 & k144 & k152 & k160 & k168 & k176 & k184 & k192 & k200 & k208 & k216 & k224 & k232 & k240 & k248 & k256 & k264 & k272 & k280 & k288 & k296 & k304 & k312 & k320 & k328 & k336 & k344 & k352 & k360 & k368 & k376 & k384
            & k392 & k400 & k408 & k416 & k424 & k432 & k440 & k448 & k456 & k464 & k472 & k480 & k488 & k496 & k504 & k512 & k520 & k528 & k536 & k544 & k552 & k560 & k568 & k576 & k584 & k592 & k600 & k608 & k616 & k624 & k632 & k640 & k648 & k656 & k664 & k672 & k680 & k688 & k696 & k704 & k712 & FRX).
      pose proof FFC5 as FFC5'. unfold X2FFB in FFC5'.
      pose proof (proj2 (proj1 (rw_cells_app bsegs _ _ [C8 (Z_to_bv 64 X2_MAGIC_LIVE); C8 (Z_to_bv 64 X2_DESC); C8 (Z_to_bv 64 0x97374); CB 8 j4; C4 (Z_to_bv 64 tl); CB 12 j5] _) FFC5')) as NBC0.
      pose proof (proj1 (proj1 (rw_cells_app bsegs _ _ [C4 (Z_to_bv 64 nbs)] _) NBC0)) as NBC. clear NBC0 FFC5'.
      cbn [cells_size csize Nat.add] in NBC. match type of NBC with rw_cells _ _ ?a _ => replace a with (FF + 48) in NBC by lia end.
      pose proof STATS as (TLR0 & _ & _ & LRK & _). unfold FseNCount.Zlength in LRK.
      assert (Hr5 : 0 <= r < 2^32) by (clear - RR NR LSB; lia).
      eapply (x2_bodyA RNG gp tp FRm fc m5 SPV (SPA2 SPV) lo DT WK wksz FF hdw r HY UD5 UW5 ART5 Hr5 HM5 HR5 TP
                (huf_rd_postA AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FRm fc SPV DT WK wksz lo true m)
                hw rank nbs tl STATS NBSR LHW LRK k0 k8 k16 k24 k32 k40 k48 k72 k80 k88 k104 k144 k152 k160 k168 k176 k184 k192 k200 k208 k216 k224 k232 k240 k248 k256 k264 k272 k280 k288 k296 k304 k312 k320 k328 k336 k344 k352 k360 k368
                k376 k384 k392 k400 k408 k416 k424 k432 k440 k448 k456 k464 k472 k480 k488 k496 k504 k512 k520 k528 k536 k544 k552 k560 k568 k576 k584 k592 k600 k608 k616 k624 k632 k640 k648 k656 k664 k672 k680 k688 k696 k704 k712 (Z_to_bv 64 n) flags
                (fun maxW HMW HIGH rs0 rv syb RSFX RVXX => @AZ_hft_x2_k4.x2_skA _ RNG gp tp FRm fc m5 SPV (SPA2 SPV) lo DT WK wksz FF hdw r HY UD5 UW5 ART5 Hr5 HR5 _ hw rank nbs tl STATS NBSR LHW LRK k0 k8 k704 k712 maxW HMW HIGH rs0 rv syb RVXX)
                (fun maxW HMW HIGH rs0 rv syb RSFX RVXX => @AZ_hft_x2_w2.x2_jnA _ RNG gp tp FRm fc m5 SPV (SPA2 SPV) lo DT WK wksz FF hdw r HY UD5 UW5 ART5 Hr5 HR5 TP _ hw rank nbs tl STATS NBSR LHW LRK k0 k8 k704 k712 maxW HMW HIGH rs0 rv syb RSFX RVXX)
                (fun maxW HMW HIGH rs0 rv syb RSFX RVXX => @AZ_hft_x2_w2.x2_slA _ RNG gp tp FRm fc m5 SPV (SPA2 SPV) lo DT WK wksz FF hdw r HY UD5 UW5 ART5 Hr5 HR5 _ hw rank nbs tl STATS NBSR LHW LRK k0 k8 k704 k712 maxW HMW HIGH rs0 rv syb) dtb);
        first [ exact MI5| exact STL5| exact FRX| exact NBC| exact TB5| exact HW5| exact RK5| exact RS05| exact W15| exact W25| exact WKR5
              | clear - LTB; unfold HUF_DTABLE_BYTES in *; lia
              | lazymatch goal with |- ?G => idtac "LEFT" end ].
      (* [comment removed for export] *)
      intros maxW rs0 rv dt syb m6 q0 q8 q16 q24 q32 q40 q48 q64 q72 q80 q88 q104 q144 q152 q160 q168 q176 q184 q192 q200 q208 q216 q224 q232 q240 q248 q256 q264 q272 q280 q288 q296 q304 q312 q320 q328 q336 q344 q352 q360 q368 q376
             q384 q392 q400 q408 q416 q424 q432 q440 q448 q456 q464 q472 q480 q488 q496 q504 q512 q520 q528 q536 q544 q552 q560 q568 q576 q584 q592 q600 q608 q616 q624 q632 q640 q648 q656 q664 q672 q680 q688 q696 q704 q712 yra w5 w6 w7 wa1 wa2 wa3 wa4 wa5 wa6 wa7 ws2 ws4 ws5 ws6 ws7 ws8 ws9 ws11 w28 w29 w30 w31 HMW I PF Z0 Z1 Z2.
      clear MI; try clear NBC. open_xb I.
      assert (TTR : tl <= AZ_hft_x2_defs.TT tl <= 12 /\ 11 <= AZ_hft_x2_defs.TT tl) by (clear - TLR0; unfold AZ_hft_x2_defs.TT; destruct (Z.ltb_spec tl 12); lia).
      pose proof (x2pref_tbl (AZ_hft_x2_defs.TT tl) dt PF DTLEN DTBY ltac:(clear - TTR; lia) Z0 Z1 Z2) as (HOK & TOK & TY1).
      assert (BLO : forall b, In b LB -> ab_addr b + ab_size b <= ATOP).
      { intros b Hb. pose proof (ablk_lin _ _ (LBH b Hb)) as (_ & _ & L3 & _). exact L3. }
      pose proof atop_range as ATR.
      pose proof (x2_bands _ _ _ _ _ _ _ _ HY) as (BDT & BWK & BSP & BSP2 & B5 & B6 & B7 & B8).
      eapply (x2_closeZ AI fflag FFLAG FREL L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FRm fc m m6 SPV DT WK wksz lo FF r (map (Z_to_bv 8) dt)) with (j0 := Z_to_bv 64 X2_MAGIC_LIVE);
        first [ exact LBH| exact F64| exact FH| exact FC| exact RFF| exact RSFF| exact FFD| exact FFA1| exact FFA2| exact MI| exact BOT| exact LOS| exact SP16| exact RSTK2| exact RI
              | exact IND| exact INW| exact DTC| exact HOK
              | eapply wmono_trans; [exact WM05| exact WM]
              | clear - LY3 SPT; lia | clear - DTH; unfold HUF_DTABLE_BYTES in *; lia | clear - WKH; lia | clear - WR; lia | clear - RR NR LSB; lia
              | intros _; split; [exact TOK| exists (Z_to_bv 8 1); split; [exact TY1| split; intros HH; [reflexivity| cbv; discriminate]]]
              | lazymatch goal with |- ?G => idtac "LEFT" G end ].
      11: { apply rw_cells_of_u8arr in RV; apply stk_of_rw_cells in RV. apply rw_cells_of_u8arr in RK; apply stk_of_rw_cells in RK.
            apply rw_cells_of_u8arr in RS0; apply stk_of_rw_cells in RS0. apply rw_cells_of_u8arr in SYC; apply stk_of_rw_cells in SYC.
            apply rw_cells_of_u8arr in HWC; apply stk_of_rw_cells in HWC.
            cbn [cells_size csize Nat.add] in RV, RK, RS0, SYC, HWC. rewrite length_map, u32b_length in RV, RK, RS0. rewrite length_map in HWC.
            match type of RV with stk _ _ _ ?h => replace h with (WK + 624) in RV by lia end.
            match type of RK with stk _ _ _ ?h => replace h with (WK + 676) in RK by lia end.
            match type of RS0 with stk _ _ _ ?h => replace h with (WK + 736) in RS0 by lia end.
            match type of SYC with stk _ _ _ ?h => replace h with (WK + 992) in SYC by lia end.
            match type of HWC with stk _ _ _ ?h => replace h with (WK + 1248) in HWC by lia end.
            pose proof (stk_merge bsegs m6 WK (WK + 624) (WK + 676) RV RK ltac:(lia)) as M1.
            pose proof (stk_merge bsegs m6 WK (WK + 676) (WK + 736) M1 RS0 ltac:(lia)) as M2.
            pose proof (stk_merge bsegs m6 WK (WK + 736) (WK + 992) M2 SYC ltac:(lia)) as M3.
            pose proof (stk_merge bsegs m6 WK (WK + 992) (WK + 1248) M3 HWC ltac:(lia)) as M4.
            exact (stk_merge bsegs m6 WK (WK + 1248) (WK + wksz) M4 WKR ltac:(clear - WBIG; lia)). }
      10: { pose proof (proj2 (proj1 (rw_cells_app bsegs _ _ [C8 q0; C8 q8; C8 q16; C8 q24; C8 q32; C8 q40; C8 q48;
               C8 (Z_to_bv 64 (Z.shiftr DT 3 + 2147450880)); C8 q64; C8 q72; C8 q80; C8 q88;
               C8 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)); C8 q104; C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF)] _) FR)) as T1.
            apply stk_of_rw_cells in T1. cbn [cells_size csize Nat.add] in T1.
            match type of T1 with stk _ _ ?a ?h => replace h with (SPA2 SPV + 728) in T1 by lia; replace a with (SPA2 SPV + 128) in T1 by lia end.
            assert (STG6 : stk bsegs m6 (SPA2 SPV + 728) (SPV + -104)).
            { eapply stk_transport_disjoint; [exact STG5| exact MU| exact WM|]. cbn [disjoint_from]. unfold HUF_DTABLE_BYTES in *.
              clear - SPAB SDS SWS LOS WKL DTL WR. repeat split; lia. }
            exact (stk_merge bsegs m6 (SPA2 SPV + 128) (SPA2 SPV + 728) (SPV + -104) T1 STG6 ltac:(clear - SPAB; lia)). }
      9: { pose proof (proj1 (proj1 (rw_cells_app bsegs _ _ [C8 q0; C8 q8; C8 q16; C8 q24; C8 q32; C8 q40; C8 q48;
               C8 (Z_to_bv 64 (Z.shiftr DT 3 + 2147450880)); C8 q64; C8 q72; C8 q80; C8 q88;
               C8 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)); C8 q104] _) FR)) as T0.
           apply stk_of_rw_cells in T0. cbn [cells_size csize Nat.add] in T0.
           match type of T0 with stk _ _ _ ?h => replace h with (SPA2 SPV + 112) in T0 by lia end.
           exact (stk_merge bsegs m6 lo (SPA2 SPV) (SPA2 SPV + 112) STK T0 ltac:(clear - SPAB LOS; lia)). }
      8: { pose proof (proj2 (proj1 (rw_cells_app bsegs _ _ [C8 q0; C8 q8; C8 q16; C8 q24; C8 q32; C8 q40; C8 q48;
               C8 (Z_to_bv 64 (Z.shiftr DT 3 + 2147450880)); C8 q64; C8 q72; C8 q80; C8 q88;
               C8 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)); C8 q104] _) FR)) as T2.
           pose proof (proj1 (proj1 (rw_cells_app bsegs _ _ [C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF)] _) T2)) as T3.
           cbn [cells_size csize Nat.add] in T3. match type of T3 with rw_cells _ _ ?a _ => replace a with (SPA2 SPV + 112) in T3 by lia end. exact T3. }
      7: { eapply rw_cells_transport; [exact FRB5| exact MU| exact WM|]. unfold X2SAVED. cbn [disjoint_from cells_size csize Nat.add]. unfold HUF_DTABLE_BYTES in *.
           clear - SPAB SDS SWS LOS WKL DTL WR. repeat split; lia. }
      6: { unfold X2FFB in FFC5.
           pose proof (proj2 (proj1 (rw_cells_app bsegs _ _ [C8 (Z_to_bv 64 X2_MAGIC_LIVE); C8 (Z_to_bv 64 X2_DESC); C8 (Z_to_bv 64 0x97374); CB 8 j4; C4 (Z_to_bv 64 tl); CB 12 j5; C4 (Z_to_bv 64 nbs); CB 4 j6] _) FFC5)) as G5.
           cbn [cells_size csize Nat.add] in G5. match type of G5 with rw_cells _ _ ?a _ => replace a with (FF + 56) in G5 by lia end.
           eapply rw_cells_transport; [exact G5| exact MU| exact WM|]. cbn [disjoint_from cells_size csize Nat.add]. unfold HUF_DTABLE_BYTES in *.
           clear - FHc BOT LOS SPAB DFD DFW WR. repeat split; lia. }
      5: { unfold X2FFB in FFC5.
           pose proof (proj1 (proj1 (rw_cells_app bsegs _ _ [C8 (Z_to_bv 64 X2_MAGIC_LIVE)] _) FFC5)) as G0.
           eapply rw_cells_transport; [exact G0| exact MU| exact WM|]. cbn [disjoint_from cells_size csize Nat.add]. unfold HUF_DTABLE_BYTES in *.
           clear - FHc BOT LOS SPAB DFD DFW WR. repeat split; lia. }
      4: { eapply rw_cells_transport; [exact SHF5| exact MU| exact WM|]. unfold X2SH. cbn [disjoint_from cells_size csize Nat.add]. unfold HUF_DTABLE_BYTES in *.
           rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold KHIGH in *.
           clear - FHb FHd BDT BWK KLO LOS SPAB WR WKL DTL. repeat split; Z.div_mod_to_equations; lia. }
      3: { eapply ffr_pres_trans.
           - eapply magree_mono; [exact FFR05|]. intros a [[HF HO]|HS]; [left; split; [exact HF|]| right; exact HS]. cbn [outside] in *. clear - HO. tauto.
           - eapply magree_mono; [eapply magree_of_munch; [exact MU| exact WM]|].
             intros a [[(c & A & k & Hb & Ha) HO]|(a' & (c & A & k & Hb & Ha') & ->)];
               pose proof (BLO _ Hb) as B1; cbn [ab_addr ab_size] in B1; cbn [outside] in *; unfold HUF_DTABLE_BYTES in *.
             + clear - HO B1 Ha BOT LOS SPAB. repeat split; try exact I; lia.
             + rewrite shad_div. unfold ASHOFF. pose proof (ablk_lin _ _ (LBH _ Hb)) as (B0 & B2 & _). cbn [ab_addr ab_size] in B0, B2. unfold AIMG_HI in B0.
               unfold KHIGH in *. clear - B1 B0 B2 Ha' BOT LOS SPAB BDT BWK ATR KLO. unfold ATOP_MIN, ATOP_MAX in ATR.
               repeat split; try exact I; Z.div_mod_to_equations; lia. }
      2: { eapply munch_trans; [eapply munch_weaken; [| exact MU05]; intros x Hx; cbn [outside app fake_area] in *; clear - Hx; lia|].
           eapply munch_weaken; [| exact MU]. intros x Hx. cbn [outside app fake_area] in *. unfold HUF_DTABLE_BYTES in *. clear - Hx SPAB. lia. }
      1: { eapply (AI_frame AI); [exact AH5| exact MU| exact WM|].
           constructor; [| constructor; [| constructor; [| constructor]]]; cbn [fst snd].
           - right; left. destruct IND as (b & Hb & B1 & B2). exists b. split; [right; exact Hb| unfold HUF_DTABLE_BYTES in *; lia].
           - right; left. destruct INW as (b & Hb & B1 & B2). exists b. split; [right; exact Hb| lia].
           - left; left. clear - BOT LOS SPAB LY3 SPT. lia. }
Qed.
End Asm.
End CANSEC1.
