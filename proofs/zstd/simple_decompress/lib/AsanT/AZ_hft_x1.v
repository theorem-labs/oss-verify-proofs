(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufStats ZdHufX1.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree FseWalkKit FseRdKit FseRdKit2 ZdWalkKit ZdCellKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AProto AMalloc_iface AProg_kit AFake_iface AFakeK_iface
     FsKit AZ_kit AZ_globals AZ_globalsR AZ_fkit AZ_huf_iface AZ_hft_iface AZ_hft_rs_iface AF_fse_rd_base AF_fse_rd_mem AF_fse_rd_seg AF_fse_rd_asm
     AZ_hft_x1_seg AZ_hft_x1_env AZ_hft_x1_call AZ_hft_x1_defs AZ_hft_x1_fk AZ_hft_x1_wl AZ_hft_x1_body.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RZ_hft_x1_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKitF.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

(* [comment removed for export] *)
Lemma x1pref_tbl : forall tl dt, x1pref tl (2^tl) dt -> zlen dt = 16388 -> Forall (fun v : Z => 0 <= v < 256) dt -> 11 <= tl <= 12 ->
  huf_hdr_ok (map (Z_to_bv 8) dt) /\ huf_tbl_ok (map (Z_to_bv 8) dt) /\ nth_error (map (Z_to_bv 8) dt) 1 = Some (Z_to_bv 8 0).
Proof.
  intros tl dt (P0 & P1 & P2 & PC) L BY TLR.
  assert (P2TL : 2^tl <= 4096) by (change 4096 with (2^12); apply Z.pow_le_mono_r; lia).
  assert (NE : forall i, 0 <= i < zlen dt -> nth_error (map (Z_to_bv 8) dt) (Z.to_nat i) = Some (Z_to_bv 8 (Znth i dt))) by (intros i Hi; apply nth_error_map_Znth; lia).
  assert (HDR : huf_hdr_ok (map (Z_to_bv 8) dt)).
  { split; [unfold HUF_DTABLE_BYTES; rewrite length_map; exact L|]. change 0%nat with (Z.to_nat 0). rewrite NE by lia. rewrite P0. reflexivity. }
  split; [exact HDR|]. split.
  - split; [exact HDR|]. exists (Z_to_bv 8 0), tl. split; [change 1%nat with (Z.to_nat 1); rewrite NE by lia; rewrite P1; reflexivity|].
    split; [change 2%nat with (Z.to_nat 2); rewrite NE by lia; rewrite P2; reflexivity|]. split; [lia|].
    split; [intros NZ; exfalso; apply NZ; reflexivity|].
    intros i Hi. exists (Z_to_bv 8 (Znth (4 + 2 * i) dt)). split.
    + replace (2 * i + 4) with (4 + 2 * i) by lia. apply NE. lia.
    + pose proof (PC i Hi) as B. pose proof (Forall_Znth _ dt (4 + 2 * i) BY ltac:(lia)) as R. cbv beta in R.
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
Theorem huf_rdx1_proofA : huf_rdx1_stmtA AI rng_fs.
Proof.
  unfold huf_rdx1_stmtA, huf_rd_stmtA_at.
  intros L RNG st LB ra gp tp t0 t1 t2 s0 s1 flags a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m SPV SRC n DT WK wksz lo src dtb
         MI ST LO0 LOS SPR SB LSB SRCL NR SRH TB HDR DTL DTH DT4 WKS WKL WR WKH WK4 SDS SWS SSS DTWK DTSRC WKSRC AFP AZS TP ARO ASRC INS HSRC ADT HDT IND AWK HWK INW.
  destruct AFP as (AH & ASH & ART & (KLO & RSTK & RI) & RFS & BOT & SPT & SP16 & RSTK2 & LBH).
  pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & LY4 & _).
  pose proof (ashort_fake_le LB 4 0 ASH ltac:(clear; lia)) as FLE. change (Z.to_nat (4096 - 4)) with 4092%nat in FLE.
  pose proof HDR as [LTB DT0].
  destruct (ADT ltac:(unfold HUF_DTABLE_BYTES; clear; lia)) as (ABD & UD & RDT & RSDT).
  destruct (stk_open bsegs m WK (WK + wksz) WK (Z.to_nat wksz) WKS ltac:(lia) ltac:(lia)) as (jw & WC & _ & _).
  eapply evtF_cut; [| cbv beta; intros ms' HQ; exact HQ].
  eapply (x1_openZ AI fflag rng_fs SM0K FHL 4092%nat L RNG st LB ra gp tp t0 t1 t2 s0 s1 flags a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m
            SPV DT WK wksz SRC n lo dtb src jw
            (fun ms => evtF bsegs RNG (huf_rd_postA AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV DT WK wksz lo false m) ms));
    first [ exact AH| exact FLE| exact LBH| exact RI| exact RSTK2| exact RFS| exact BOT| exact LOS| exact SP16| exact ST| exact MI| exact TP| exact TB| exact IND| exact UD
          | exact SDS| exact WC| exact INW| exact SWS| exact SB| exact LSB| exact INS| exact SSS| exact DTL| exact WK4| exact WKL
          | intros NP; destruct (AWK NP) as (_ & U & _); exact U
          | intros NP; destruct (ASRC NP) as (_ & U & _); exact U
          | clear - LY3 SPT; lia | clear; cbn; lia | clear - LTB; unfold HUF_DTABLE_BYTES in *; lia | clear - WR; lia | clear - NR LSB; lia | clear - DTH; unfold HUF_DTABLE_BYTES in *; lia
          | clear - WKL; lia | clear - WKH; lia | clear - WKH WR; lia | clear - SRCL; lia | clear - SRH; lia
          | lazymatch goal with |- ?G => idtac "LEFT:" G end ].
  - (* [comment removed for export] *)
    intros FF m3 jA jC jD jB jE j3 j5 j6 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31
           F64 FH FC RFF RSFF FFD FFA1 FFA2 AH3 MU03 WM03 FFR03 MI3 FRB3 FRA3 FFC3 SHF3 STG3 TB3 UD3 WC3 UW3 SB3 US3 WSMALL STL3.
    pose proof (spa1_props SPV SP16) as (SPAB & SPA32 & _).
    unfold X1FRA in FRA3. unfold X1FFHDR in FFC3.
    pose proof (proj1 (rw_cells_app bsegs _ _ [CB 80 jA] _) FRA3) as [FA0 FA1].
    pose proof (proj1 (rw_cells_app bsegs _ _ [C8 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF)] _) FA1) as [FA2 FA3].
    cbn [cells_size csize Nat.add] in FA2, FA3. apply stk_of_rw_cells in FA0. apply stk_of_rw_cells in FA3. cbn [cells_size csize Nat.add] in FA0, FA3.
    pose proof (proj1 (rw_cells_app bsegs _ _ [C8 (Z_to_bv 64 X1_MAGIC_LIVE)] _) FFC3) as [FH0 FH1].
    pose proof (proj2 (proj1 (rw_cells_app bsegs _ _ [C8 (Z_to_bv 64 X1_MAGIC_LIVE); C8 (Z_to_bv 64 X1_DESC); C8 (Z_to_bv 64 0x96138); CB 8 j3; C4 (Z_to_bv 64 0); CB 12 j5; C4 (Z_to_bv 64 0); CB 4 j6] _) FFC3)) as FH5.
    cbn [cells_size csize Nat.add] in FH5.
    apply stk_of_rw_cells in WC3. cbn [cells_size csize Nat.add] in WC3.
    eapply (x1_closeZ AI fflag FFLAG FREL L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m m3 SPV DT WK wksz lo FF 18446744073709551572 dtb);
      first [ exact AH3| exact LBH| exact F64| exact FH| exact FC| exact RFF| exact RSFF| exact FFD| exact FFA1| exact FFA2| exact WM03| exact MI3| exact SHF3| exact FH0| exact FRB3
            | exact BOT| exact LOS| exact SP16| exact RSTK2| exact RI| exact IND| exact INW| exact TB3| exact HDR
            | eapply munch_weaken; [| exact MU03]; intros x Hx; cbn [outside app fake_area] in *; clear - Hx; lia
            | apply ffr_pres_mono_nil1; exact FFR03
            | match type of FH5 with rw_cells _ _ ?a _ => replace a with (FF + 56) in FH5 by lia end; exact FH5
            | match type of FA2 with rw_cells _ _ ?a _ => replace a with (SPA1 SPV + 80) in FA2 by lia end; exact FA2
            | match type of FA0 with stk _ _ _ ?h => replace h with (SPA1 SPV + 80) in FA0 by lia end; exact (stk_merge bsegs m3 lo (SPA1 SPV) (SPA1 SPV + 80) STL3 FA0 ltac:(lia))
            | match type of FA3 with stk _ _ ?a ?h => replace h with (SPA1 SPV + 312) in FA3 by lia; replace a with (SPA1 SPV + 104) in FA3 by lia end;
              exact (stk_merge bsegs m3 (SPA1 SPV + 104) (SPA1 SPV + 312) (SPV + -104) FA3 STG3 ltac:(lia))
            | match type of WC3 with stk _ _ _ ?h => replace h with (WK + wksz) in WC3 by lia end; exact WC3
            | clear - LY3 SPT; lia | clear - DTH; unfold HUF_DTABLE_BYTES in *; lia | clear - WKH; lia | clear - WR; lia | clear; lia
            | intros E; exfalso; clear - E; cbv in E; discriminate E
            | lazymatch goal with |- ?G => idtac "LEFT:" G end ].
  - (* [comment removed for export] *)
    intros FF m3 jA jC jD jB jE j3 j5 j6 y5 y6 y7 y28 y29 y30 y31
           F64 FH FC RFF RSFF FFD FFA1 FFA2 AH3 MU03 WM03 FFR03 MI3 FRB3 FRA3 FFC3 SHF3 STG3 TB3 UD3 WC3 UW3 SB3 US3 WBIG STL3 ARG3.
    pose proof (spa1_props SPV SP16) as (SPAB & SPA32 & _).
    destruct (AWK ltac:(lia)) as (ABW & _ & RW & RSW).
    cbv beta. eapply evtF_cut; [| cbv beta; intros ms' HQ; exact HQ].
    eapply (x1_callZ AI fflag rng_fs FHL RS L RNG st LB ra gp tp s0 s1 flags s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m m3 SPV DT WK wksz SRC n lo FF dtb src jw jA jC jD jB jE j3 j5 j6
              y5 y6 y7 y28 y29 y30 y31 (fun ms => evtF bsegs RNG (huf_rd_postA AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV DT WK wksz lo false m) ms));
      first [ exact ASH| exact LBH| exact RI| exact RSTK2| exact RFS| exact KLO| exact BOT| exact LOS| exact SP16| exact TP| exact ARO| exact AZS| exact ABW| exact RW| exact RSW
            | exact HWK| exact INW| exact WK4| exact SWS| exact LSB| exact SSS| exact WKSRC| exact ASRC| exact INS| exact HSRC| exact LTB| exact IND| exact SDS| exact DTWK
            | exact F64| exact FH| exact FC| exact RFF| exact RSFF| exact FFD| exact FFA1| exact FFA2| exact AH3| exact MU03| exact WM03| exact FFR03| exact MI3
            | exact FRB3| exact FRA3| exact FFC3| exact SHF3| exact STG3| exact TB3| exact UD3| exact WC3| exact SB3| exact US3| exact STL3| exact ARG3| exact WKL
            | apply UW3; clear - WBIG; lia
            | clear - LY3 SPT; lia | clear - WKL; lia | clear - WKH; lia | clear - WR WBIG; lia | clear - SRCL; lia | clear - NR LSB; lia | clear - SRH; lia
            | clear - DTH; unfold HUF_DTABLE_BYTES in *; lia
            | intros NP; destruct (ASRC NP) as (A1 & _ & A2 & A3); split; [exact A1| split; [exact A2| exact A3]]
            | lazymatch goal with |- ?G => idtac "LEFT:" G end ].
    + (* [comment removed for export] *)
      intros m5 r z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 ERR Hr AH5 MU05 WM05 MI5 FFR05 SHF5 FH05 FH565 FRB5 FRA5 STL5 STG5 TB5 STW5.
      cbv beta.
      eapply (x1_closeZ AI fflag FFLAG FREL L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m m5 SPV DT WK wksz lo FF r dtb);
        first [ exact AH5| exact LBH| exact F64| exact FH| exact FC| exact RFF| exact RSFF| exact FFD| exact FFA1| exact FFA2| exact MU05| exact WM05| exact MI5| exact FFR05
              | exact SHF5| exact FH05| exact FH565| exact FRB5| exact FRA5| exact STL5| exact STG5| exact BOT| exact LOS| exact SP16| exact RSTK2| exact RI| exact IND| exact INW
              | exact TB5| exact HDR| exact STW5| exact Hr
              | clear - LY3 SPT; lia | clear - DTH; unfold HUF_DTABLE_BYTES in *; lia | clear - WKH; lia | clear - WR; lia
              | intros E; rewrite ERR in E; discriminate E
              | lazymatch goal with |- ?G => idtac "LEFT:" G end ].
    + (* [comment removed for export] *)
      intros m5 r nbs tl hw rank jA5 z5 z6 z7 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31
             NER RR AH5 MU05 WM05 MI5 FFR05 FRB5 FRA5 R565 FFC5 SHF5 STG5 STL5 TB5 UD5 HW5 LHW BHW RK5 SG15 SG35 UW5 STATS NBSR.
      cbv beta. unfold X1FRA in FRA5.
      pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in FHa.
      pose proof (fk_inblk_apart AI _ _ _ _ _ _ _ _ WK wksz AH3 INW ltac:(lia)) as DFW.
      pose proof (fk_inblk_apart AI _ _ _ _ _ _ _ _ DT HUF_DTABLE_BYTES AH3 IND ltac:(unfold HUF_DTABLE_BYTES; lia)) as DFD.
      assert (ART5 : art m5) by (apply artcells_art; exact (AI_rtcells AI _ _ _ _ _ AH5)).
      assert (HULW5 : ahull RNG m5 WK wksz) by (eapply fk_ahull_pres; [exact WM05| exact HWK]).
      assert (HY : x1A_hyps RNG SPV (SPA1 SPV) lo DT WK wksz FF).
      { unfold x1A_hyps. unfold HUF_DTABLE_BYTES in *. pose proof atop_range as ATR.
        repeat match goal with |- _ /\ _ => split end;
        first [ exact ABD| exact RDT| exact RSDT| exact ABW| exact RW| exact RSW| exact RFF| exact RI| exact F64| exact FC| exact FH| exact DT4| exact WK4| exact SP16| exact SPA32| exact KLO| exact BOT
              | eapply rng_sub'; [exact RSTK2| clear - LY3 SPT LOS LO0; lia]
              | clear - DTL DTH WKL WKH WR WBIG LOS SPT LY3 SPAB SDS SWS DTWK FHa FHb FHc DFD DFW; lia
              | lazymatch goal with |- ?G => idtac "LEFT HY:" G end ]. }
      assert (Hr32 : 0 <= r < 2^32) by (clear - RR NR LSB; lia).
      assert (BLO : forall b, In b LB -> ab_addr b + ab_size b <= ATOP).
      { intros b Hb. pose proof (ablk_lin _ _ (LBH b Hb)) as (_ & _ & L3 & _). exact L3. }
      pose proof atop_range as ATR.
      pose proof (x1_bands _ _ _ _ _ _ _ _ HY) as (BDT & BWK & BSP & BSP2 & B5 & B6 & B7 & BFF).
      (* [comment removed for export] *)
      assert (KX : forall (hw6 rank6 : list Z) (tl6 : Z) m6 (j0 j192 : list byte) (dt rst : list Z) (syb : list byte) (rsacc sym : Z)
          (xra w5 w6 w7 wa0 wa1 wa2 wa3 wa4 wa5 wa6 wa7 ws2 ws3 ws5 ws7 ws8 ws9 ws10 ws11 w28 w29 w30 w31 : word),
        XF m5 SPV (SPA1 SPV) lo DT WK wksz FF r hw6 rank6 tl6 j0 j192 dt rst syb rsacc sym m6 -> x1pref tl6 (2^tl6) dt -> 11 <= tl6 <= 12 -> zlen hw6 = 256 -> zlen rank6 = 13 ->
        evtF bsegs RNG (huf_rd_postA AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV DT WK wksz lo false m)
             (MS (mkR xra (Z_to_bv 64 (SPA1 SPV)) gp tp w5 w6 w7 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPA1 SPV)) wa0 wa1 wa2 wa3 wa4 wa5 wa6 wa7 ws2 ws3 (Z_to_bv 64 0x7fff8000)
                      ws5 (Z_to_bv 64 r) ws7 ws8 ws9 ws10 ws11 w28 w29 w30 w31)
                 FR (Z_to_bv 64 0x970d8) fc None m6 (seg_rom bsegs))).
      { intros hw6 rank6 tl6 m6 j0 j192 dt rst syb rsacc sym xra w5 w6 w7 wa0 wa1 wa2 wa3 wa4 wa5 wa6 wa7 ws2 ws3 ws5 ws7 ws8 ws9 ws10 ws11 w28 w29 w30 w31 I PF TLR0 LHW0 LRK0.
        clear MI. open_xf I.
        pose proof (x1pref_tbl tl6 dt PF DTLEN DTBY TLR0) as (HOK & TOK & TY0).
        (* [comment removed for export] *)
        eapply (x1_closeZ AI fflag FFLAG FREL L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m m6 SPV DT WK wksz lo FF r (map (Z_to_bv 8) dt)) with (j0 := Z_to_bv 64 X1_MAGIC_LIVE);
          first [ exact LBH| exact F64| exact FH| exact FC| exact RFF| exact RSFF| exact FFD| exact FFA1| exact FFA2| exact MI| exact BOT| exact LOS| exact SP16| exact RSTK2| exact RI
                | exact IND| exact INW| exact DTC| exact HOK
                | eapply wmono_trans; [exact WM05| exact WM]
                | clear - LY3 SPT; lia | clear - DTH; unfold HUF_DTABLE_BYTES in *; lia | clear - WKH; lia | clear - WR; lia | clear - RR NR LSB; lia
                | intros _; split; [exact TOK| exists (Z_to_bv 8 0); split; [exact TY0| split; intros HH; [exfalso; apply HH; reflexivity| discriminate HH]]]
                | lazymatch goal with |- ?G => idtac "LEFT" end ].
        11: { apply rw_cells_of_u8arr in RK; apply stk_of_rw_cells in RK. apply rw_cells_of_u8arr in RST; apply stk_of_rw_cells in RST.
              apply rw_cells_of_u8arr in SYC; apply stk_of_rw_cells in SYC. apply rw_cells_of_u8arr in HWC; apply stk_of_rw_cells in HWC.
              cbn [cells_size csize Nat.add] in RK, RST, SYC, HWC. rewrite length_map, u32b_length in RK, RST. rewrite length_map in HWC.
              match type of RK with stk _ _ _ ?h => replace h with (WK + 52) in RK by lia end.
              match type of RST with stk _ _ _ ?h => replace h with (WK + 104) in RST by lia end.
              match type of SYC with stk _ _ _ ?h => replace h with (WK + 1236) in SYC by lia end.
              match type of HWC with stk _ _ _ ?h => replace h with (WK + 1492) in HWC by lia end.
              pose proof (stk_merge bsegs m6 WK (WK + 52) (WK + 104) RK RST ltac:(lia)) as M1.
              pose proof (stk_merge bsegs m6 WK (WK + 104) (WK + 980) M1 STS ltac:(lia)) as M2.
              pose proof (stk_merge bsegs m6 WK (WK + 980) (WK + 1236) M2 SYC ltac:(lia)) as M3.
              pose proof (stk_merge bsegs m6 WK (WK + 1236) (WK + 1492) M3 HWC ltac:(lia)) as M4.
              exact (stk_merge bsegs m6 WK (WK + 1492) (WK + wksz) M4 WKR ltac:(clear - WBIG; lia)). }
        10: { pose proof (proj2 (proj1 (rw_cells_app bsegs _ _ [CB 8 j0; C8 (Z_to_bv 64 (DT + 27)); C8 (Z_to_bv 64 (DT + 20)); C8 (Z_to_bv 64 (DT + 19)); C8 (Z_to_bv 64 (DT + 35));
                                                             C8 (Z_to_bv 64 (DT + 28)); C8 (Z_to_bv 64 (DT + 11)); C8 (Z_to_bv 64 r); C8 (Z_to_bv 64 (DT + 12)); C8 (Z_to_bv 64 (DT + 4));
                                                             C8 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF)] _) FR1)) as T1.
              apply stk_of_rw_cells in T1. apply stk_of_rw_cells in FR2. apply stk_of_rw_cells in FR4.
              cbn [cells_size csize Nat.add] in T1, FR2, FR4.
              match type of T1 with stk _ _ ?a ?h => replace h with (SPA1 SPV + 136) in T1 by lia; replace a with (SPA1 SPV + 104) in T1 by lia end.
              match type of FR2 with stk _ _ _ ?h => replace h with (SPA1 SPV + 296) in FR2 by lia end.
              match type of FR4 with stk _ _ _ ?h => replace h with (SPA1 SPV + 312) in FR4 by lia end.
              assert (STG6 : stk bsegs m6 (SPA1 SPV + 312) (SPV + -104)).
              { eapply stk_transport_disjoint; [exact STG5| exact MU| exact WM|]. cbn [disjoint_from]. unfold HUF_DTABLE_BYTES in *.
                clear - SPAB SDS SWS LOS WKL DTL WR FHc BOT B7. repeat split; lia. }
              pose proof (stk_merge bsegs m6 (SPA1 SPV + 104) (SPA1 SPV + 136) (SPA1 SPV + 296) T1 FR2 ltac:(lia)) as M1.
              pose proof (stk_merge bsegs m6 (SPA1 SPV + 104) (SPA1 SPV + 296) (SPA1 SPV + 312) M1 FR4 ltac:(lia)) as M2.
              exact (stk_merge bsegs m6 (SPA1 SPV + 104) (SPA1 SPV + 312) (SPV + -104) M2 STG6 ltac:(clear - SPAB; lia)). }
        9: { pose proof (proj1 (proj1 (rw_cells_app bsegs _ _ [CB 8 j0; C8 (Z_to_bv 64 (DT + 27)); C8 (Z_to_bv 64 (DT + 20)); C8 (Z_to_bv 64 (DT + 19)); C8 (Z_to_bv 64 (DT + 35));
                                                            C8 (Z_to_bv 64 (DT + 28)); C8 (Z_to_bv 64 (DT + 11)); C8 (Z_to_bv 64 r); C8 (Z_to_bv 64 (DT + 12)); C8 (Z_to_bv 64 (DT + 4))] _) FR1)) as T0.
             apply stk_of_rw_cells in T0. cbn [cells_size csize Nat.add] in T0.
             match type of T0 with stk _ _ _ ?h => replace h with (SPA1 SPV + 80) in T0 by lia end.
             exact (stk_merge bsegs m6 lo (SPA1 SPV) (SPA1 SPV + 80) STK T0 ltac:(clear - SPAB LOS; lia)). }
        8: { pose proof (proj2 (proj1 (rw_cells_app bsegs _ _ [CB 8 j0; C8 (Z_to_bv 64 (DT + 27)); C8 (Z_to_bv 64 (DT + 20)); C8 (Z_to_bv 64 (DT + 19)); C8 (Z_to_bv 64 (DT + 35));
                                                            C8 (Z_to_bv 64 (DT + 28)); C8 (Z_to_bv 64 (DT + 11)); C8 (Z_to_bv 64 r); C8 (Z_to_bv 64 (DT + 12)); C8 (Z_to_bv 64 (DT + 4))] _) FR1)) as T2.
             pose proof (proj1 (proj1 (rw_cells_app bsegs _ _ [C8 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF)] _) T2)) as T3.
             cbn [cells_size csize Nat.add] in T3. match type of T3 with rw_cells _ _ ?a _ => replace a with (SPA1 SPV + 80) in T3 by lia end. exact T3. }
        7: { eapply rw_cells_transport; [exact FRB5| exact MU| exact WM|]. unfold X1SAVED. cbn [disjoint_from cells_size csize Nat.add]. unfold HUF_DTABLE_BYTES in *.
             clear - SPAB SDS SWS LOS WKL DTL WR FHc BOT B7. repeat split; lia. }
        6: { unfold X1FFHDR in FFC5.
             pose proof (proj2 (proj1 (rw_cells_app bsegs _ _ [C8 (Z_to_bv 64 X1_MAGIC_LIVE); C8 (Z_to_bv 64 X1_DESC); C8 (Z_to_bv 64 0x96138); CB 8 j3; C4 (Z_to_bv 64 tl); CB 12 j5; C4 (Z_to_bv 64 nbs); CB 4 j6] _) FFC5)) as G5.
             cbn [cells_size csize Nat.add] in G5. match type of G5 with rw_cells _ _ ?a _ => replace a with (FF + 56) in G5 by lia end.
             eapply rw_cells_transport; [exact G5| exact MU| exact WM|]. cbn [disjoint_from cells_size csize Nat.add]. unfold HUF_DTABLE_BYTES in *.
             clear - FHc BOT LOS SPAB DFD DFW WR. repeat split; lia. }
        5: { unfold X1FFHDR in FFC5.
             pose proof (proj1 (proj1 (rw_cells_app bsegs _ _ [C8 (Z_to_bv 64 X1_MAGIC_LIVE)] _) FFC5)) as G0.
             eapply rw_cells_transport; [exact G0| exact MU| exact WM|]. cbn [disjoint_from cells_size csize Nat.add]. unfold HUF_DTABLE_BYTES in *.
             clear - FHc BOT LOS SPAB DFD DFW WR. repeat split; lia. }
        4: { eapply rw_cells_transport; [exact SHF5| exact MU| exact WM|]. unfold X1SH. cbn [disjoint_from cells_size csize Nat.add]. unfold HUF_DTABLE_BYTES in *.
             rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold KHIGH in *.
             clear - FHb FHd BDT BWK BFF KLO LOS SPAB WR WKL DTL. repeat split; Z.div_mod_to_equations; lia. }
        3: { eapply ffr_pres_trans.
             - eapply magree_mono; [exact FFR05|]. intros a [[HF HO]|HS]; [left; split; [exact HF|]| right; exact HS]. cbn [outside] in *. clear - HO. tauto.
             - eapply magree_mono; [eapply magree_of_munch; [exact MU| exact WM]|].
               intros a [[(c & A & k & Hb & Ha) HO]|(a' & (c & A & k & Hb & Ha') & ->)];
                 pose proof (BLO _ Hb) as B1; cbn [ab_addr ab_size] in B1; cbn [outside] in *; unfold HUF_DTABLE_BYTES in *.
               + pose proof (FFD _ Hb) as BF. cbn [ab_addr ab_size] in BF. clear - HO B1 BF Ha BOT LOS SPAB FHc. repeat split; try exact I; lia.
               + rewrite shad_div. unfold ASHOFF. pose proof (ablk_lin _ _ (LBH _ Hb)) as (B0 & B2 & _). cbn [ab_addr ab_size] in B0, B2. unfold AIMG_HI in B0.
                 unfold KHIGH in *. clear - B1 B0 B2 Ha' BOT LOS SPAB BDT BWK BFF ATR KLO FHa FHc. unfold ATOP_MIN, ATOP_MAX in ATR.
                 repeat split; try exact I; Z.div_mod_to_equations; lia. }
        2: { eapply munch_trans; [eapply munch_weaken; [| exact MU05]; intros x Hx; cbn [outside app fake_area] in *; clear - Hx; lia|].
             eapply munch_weaken; [| exact MU]. intros x Hx. cbn [outside app fake_area] in *. unfold HUF_DTABLE_BYTES in *. clear - Hx SPAB FFA1 FFA2. lia. }
        1: { eapply (AI_frame AI); [exact AH5| exact MU| exact WM|].
             constructor; [| constructor; [| constructor; [| constructor; [| constructor]]]]; cbn [fst snd].
             - right; left. destruct IND as (b & Hb & B1 & B2). exists b. split; [right; exact Hb| unfold HUF_DTABLE_BYTES in *; lia].
             - right; left. destruct INW as (b & Hb & B1 & B2). exists b. split; [right; exact Hb| lia].
             - left; left. clear - BOT LOS SPAB LY3 SPT. lia.
             - right; left. exists (FB0 FF). split; [left; reflexivity| cbn [ab_addr ab_size]; lia]. } }
      eapply (x1_bodyA RNG gp tp FR fc m5 SPV (SPA1 SPV) lo DT WK wksz FF r HY UD5 UW5 ART5 Hr32
                (huf_rd_postA AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV DT WK wksz lo false m));
        first [ exact STATS| exact NBSR| exact LHW| exact BHW| exact MI5| exact STL5| exact FRA5| exact R565| exact FFC5| exact TB5| exact HDR| exact HW5| exact RK5| exact SG15| exact SG35| exact HULW5
              | exact KX
              | lazymatch goal with |- ?G => idtac "LEFT" end ].
      (* [comment removed for export] *)
      intros hw6 rank6 nbs6 tl6 m6 dt rst syb jA6 jA2 jC6 jD6 jB6 jE6 w1 w5 w6 wa0 wa1 wa2 wa3 wa4 wa5 wa6 wa7 ws2 ws3 ws5 ws6 ws7 ws8 ws9 ws10 ws11 w28 w29 w30 w31
             ST6 TL6 NB6 LH6 BH6 LR6 I6 PF6.
      (eapply (x1_fillA RNG gp tp FR fc m5 SPV (SPA1 SPV) lo DT WK wksz FF r) with (hw := hw6) (rank := rank6) (nbs := nbs6) (tl := tl6);
        first [ exact HY| exact UD5| exact UW5| exact ART5| exact Hr32| exact ST6| exact TL6| exact NB6| exact LH6| exact BH6| exact LR6| exact I6| exact PF6| idtac ]).
      intros; eapply KX; [eassumption| eassumption| exact TL6| exact LH6| exact LR6].
Qed.
End Asm.
End CANSEC1.
