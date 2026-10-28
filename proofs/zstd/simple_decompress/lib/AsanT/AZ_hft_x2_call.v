(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufStats.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree FseWalkKit FseRdKit FseRdKit2 ZdWalkKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AProto AMalloc_iface AProg_kit AFake_iface AFakeK_iface
     AZ_kit AZ_globals AZ_globalsR AZ_fkit AZ_huf_iface AZ_hft_iface AZ_hft_rs_iface AF_fse_rd_base AF_fse_rd_mem AF_fse_rd_seg AF_fse_rd_asm
     AZ_libc_iface AZ_libc AZ_hft_x1_seg AZ_hft_x1_env AZ_hft_x1_call AZ_hft_x2_geo AZ_hft_x2_seg AZ_hft_x2_env.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKitF.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition X2FFB (FLG : Z) (j4 j5 j6 : list byte) (tlw nbw : word) : list cell :=
  [C8 (Z_to_bv 64 X2_MAGIC_LIVE); C8 (Z_to_bv 64 X2_DESC); C8 (Z_to_bv 64 0x97374); CB 8 j4; C4 tlw; CB 12 j5; C4 nbw; CB 4 j6; C8 (Z_to_bv 64 FLG)].

(* [comment removed for export] *)
Lemma X2FRA_lens : forall m A FF DT WK hdw jA jB jC jD, rw_cells bsegs m A (X2FRA FF DT WK hdw jA jB jC jD) ->
  length jA = 56%nat /\ length jB = 24%nat /\ length jC = 8%nat /\ length jD = 576%nat.
Proof.
  intros m A FF DT WK hdw jA jB jC jD [[WF _] _]. unfold X2FRA in WF. cbn [cells_wf cell_wf] in WF.
  destruct WF as (LA & _ & _ & LB & _ & LC & _ & _ & _ & _ & LD & _ & _). repeat split; assumption.
Qed.

Section Asm.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Variable fflag : alayout -> Z -> Z -> Z.
Variable rng_fs : alayout -> footprint -> Prop.
Hypothesis FFLAG : AFakeK_iface.fake_flag_law AI fflag.
Hypothesis FREL : AFakeK_iface.fake_release_law AI fflag.
Hypothesis SM0K : forall k, Z.of_nat k < 16384 -> stack_malloc_0k_stmt AI fflag rng_fs k.
Hypothesis FHL : fake_heap_law AI.
Hypothesis RS : huf_rstats_stmtA AI rng_fs.
Notation FB0 F := (mkABlock (ABFake 0) F 64).
Notation SW := 5920 (only parsing).     (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma x2_callZ : forall (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
    (ra gp tp s0 s1 flags s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m m3 : amem)
    (SPV DT WK wksz SRC n lo FF hdw : Z) (dtb src jw jA jB jC jD j3 : list byte) (y5 y6 y7 y28 y29 y30 y31 : word) (Q : machine_state -> Prop),
  ashort LB HUF_TBL_DEPTH -> ablkLB LB -> rng_aimg RNG -> rng RNG lo (al_top L - lo) -> rng_fs L RNG -> KHIGH <= lo ->
  ATOP + 4096 <= lo -> lo <= SPV - HUF_TBL_STACK_A -> SPV + 16 < al_top L -> SPV mod 16 = 0 -> tp = Z_to_bv 64 ATP ->
  aro_client RNG m -> azstk RNG m lo SPV ->
  ablk WK (WK + wksz) -> rng RNG WK wksz -> rng RNG (shad WK) (shspan WK wksz) -> ahull RNG m WK wksz -> ainblk LB WK wksz ->
  4096 <= WK -> WK + wksz < 2^47 -> WK mod 4 = 0 -> 2124 <= wksz < 2^32 -> (WK + wksz <= lo \/ SPV <= WK) ->
  zlen src = n -> 4096 <= SRC -> 0 <= n < 2^32 -> SRC + n < 2^47 -> (SRC + n <= lo \/ SPV <= SRC) -> (WK + wksz <= SRC \/ SRC + n <= WK) ->
  (0 < n -> ablk SRC (SRC + n) /\ rng RNG SRC n /\ rng RNG (shad SRC) (shspan SRC n)) -> (0 < n -> ainimg LB SRC n) -> (0 < n -> ahull RNG m SRC n) ->
  zlen dtb = HUF_DTABLE_BYTES -> ainblk LB DT HUF_DTABLE_BYTES -> (DT + HUF_DTABLE_BYTES <= lo \/ SPV <= DT) -> DT + HUF_DTABLE_BYTES <= 2^47 ->
  (DT + HUF_DTABLE_BYTES <= WK \/ WK + wksz <= DT) ->
  (* [comment removed for export] *)
  FF mod 64 = 0 -> ablk FF (FF + 64) -> FF + 64 <= ATOP -> rng RNG FF 64 -> rng RNG (shad FF) 8 ->
  (forall b, In b LB -> FF + 64 <= ab_addr b \/ ab_addr b + ab_size b <= FF) ->
  al_fake L <= FF -> FF + 64 <= al_fake L + FAKESZ -> 0 <= hdw < 2^32 -> hdw mod 256 = 12 ->
  AHEAP AI L RNG st (FB0 FF :: LB) m3 ->
  munch ([(SPV - SW, SPV)] ++ fake_area L) m m3 -> wmono bsegs m m3 -> ffr_pres [] LB m m3 -> mem_inv bsegs m3 ->
  rw_cells bsegs m3 (SPV + -104) (X2SAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  rw_cells bsegs m3 (SPA2 SPV) (X2FRA0 FF DT WK hdw jA jB jC jD) ->
  rw_cells bsegs m3 FF (X2FFHDR (fflag L 0 FF) j3) -> rw_cells bsegs m3 (Z.shiftr FF 3 + 2147450880) X2SH ->
  stk bsegs m3 (SPA2 SPV + 728) (SPV + -104) ->
  u8arr bsegs m3 DT dtb -> unpoisoned m3 DT (DT + HUF_DTABLE_BYTES) ->
  rw_cells bsegs m3 WK [CB (Z.to_nat wksz) jw] -> unpoisoned m3 WK (WK + wksz) ->
  bytes_at bsegs m3 SRC src -> (0 < n -> unpoisoned m3 SRC (SRC + n)) ->
  stk bsegs m3 lo (SPA2 SPV) ->
  (* [comment removed for export] *)
  (forall (m5 : amem) (r : Z) (z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z18 z19 z20 z21 z22 z23 z24 z25 z27 z28 z29 z30 z31 : word),
     zd_is_error r = true -> 0 <= r < 2^64 ->
     AHEAP AI L RNG st (FB0 FF :: LB) m5 ->
     munch ([(DT, DT + HUF_DTABLE_BYTES); (WK, WK + wksz); (SPV - SW, SPV)] ++ fake_area L) m m5 -> wmono bsegs m m5 -> mem_inv bsegs m5 ->
     ffr_pres [(DT, DT + HUF_DTABLE_BYTES); (WK, WK + wksz)] LB m m5 ->
     rw_cells bsegs m5 (Z.shiftr FF 3 + 2147450880) X2SH ->
     rw_cells bsegs m5 FF [C8 (Z_to_bv 64 X2_MAGIC_LIVE)] -> rw_cells bsegs m5 (FF + 56) [C8 (Z_to_bv 64 (fflag L 0 FF))] ->
     rw_cells bsegs m5 (SPV + -104) (X2SAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
     rw_cells bsegs m5 (SPA2 SPV + 112) [C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF)] ->
     stk bsegs m5 lo (SPA2 SPV + 112) -> stk bsegs m5 (SPA2 SPV + 128) (SPV + -104) ->
     u8arr bsegs m5 DT dtb -> stk bsegs m5 WK (WK + wksz) ->
     Q (MS (mkR z1 (Z_to_bv 64 (SPA2 SPV)) gp tp z5 z6 z7 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPA2 SPV)) z10 z11 z12 z13 z14 z15 z16 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880))
              z18 z19 z20 z21 z22 z23 z24 z25 (Z_to_bv 64 r) z27 z28 z29 z30 z31)
           FR (Z_to_bv 64 0x99470) fc None m5 (seg_rom bsegs))) ->
  (* [comment removed for export] *)
  (forall (m5 : amem) (r nbs tl : Z) (hw rank : list Z) (j4 j5 j6 : list byte) (z1 z5 z6 z7 z12 z13 z14 z15 z16 z29 z30 z31 : word),
     zd_is_error r = false -> 1 <= r <= n -> 0 <= hdw < 2^32 -> hdw mod 256 = 12 ->
     AHEAP AI L RNG st (FB0 FF :: LB) m5 ->
     munch ([(WK, WK + wksz); (SPV - SW, SPV)] ++ fake_area L) m m5 -> wmono bsegs m m5 -> mem_inv bsegs m5 ->
     ffr_pres [(WK, WK + wksz)] LB m m5 ->
     rw_cells bsegs m5 (SPV + -104) (X2SAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
     rw_cells bsegs m5 (SPA2 SPV) (X2FRA FF DT WK hdw jA jB jC jD) ->
     length jA = 56%nat -> length jB = 24%nat -> length jC = 8%nat -> length jD = 576%nat ->
     rw_cells bsegs m5 FF (X2FFB (fflag L 0 FF) j4 j5 j6 (Z_to_bv 64 tl) (Z_to_bv 64 nbs)) -> rw_cells bsegs m5 (Z.shiftr FF 3 + 2147450880) X2SH ->
     stk bsegs m5 (SPA2 SPV + 728) (SPV + -104) -> stk bsegs m5 lo (SPA2 SPV) ->
     u8arr bsegs m5 DT dtb -> unpoisoned m5 DT (DT + HUF_DTABLE_BYTES) ->
     u8arr bsegs m5 (WK + 992) (map (Z_to_bv 8) hw) -> zlen hw = 256 -> Forall (fun v => 0 <= v < 256) hw ->
     u32arr bsegs m5 (WK + 624) (map (Z_to_bv 64) rank) ->
     rw_cells bsegs m5 (WK + 676) [CB 60 (repeat (Z_to_bv 8 0) 60)] ->
     stk bsegs m5 WK (WK + 624) -> stk bsegs m5 (WK + 736) (WK + 992) -> stk bsegs m5 (WK + 1248) (WK + wksz) ->
     unpoisoned m5 WK (WK + wksz) ->
     huf_stats_ok (firstn (Z.to_nat nbs) hw) rank tl -> 2 <= nbs <= 256 ->
     Q (MS (mkR z1 (Z_to_bv 64 (SPA2 SPV)) gp tp z5 z6 z7 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPA2 SPV))
              (Z_to_bv 64 r) (Z_to_bv 64 18446744073709551496) z12 z13 z14 z15 z16 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880))
              (Z_to_bv 64 SRC) (Z_to_bv 64 (WK + 992)) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 12) (Z_to_bv 64 n) (Z_to_bv 64 2147450880) flags
              (Z_to_bv 64 18446744073709551572) (Z_to_bv 64 (WK + 624)) (Z_to_bv 64 tl) z29 z30 z31)
           FR (Z_to_bv 64 0x97570) fc None m5 (seg_rom bsegs))) ->
  evtF bsegs RNG Q
    (MS (mkR (Z_to_bv 64 0x974fc) (Z_to_bv 64 (SPA2 SPV)) gp tp y5 y6 y7 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPA2 SPV))
              (Z_to_bv 64 (WK + 624)) (Z_to_bv 64 0) (Z_to_bv 64 112) (Z_to_bv 64 WK) (Z_to_bv 64 (Z.shiftr DT 3 + 2147450880)) (Z_to_bv 64 18446744073709551603) (Z_to_bv 64 18446744073709551602)
              (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880))
              (Z_to_bv 64 SRC) (Z_to_bv 64 FF) s4 (Z_to_bv 64 WK) (Z_to_bv 64 12) (Z_to_bv 64 n) (Z_to_bv 64 2147450880) flags s10 (Z_to_bv 64 (WK + 624)) y28 y29 y30 y31)
        FR (Z_to_bv 64 0x53ca0) fc None m3 (seg_rom bsegs)).
Proof.
  intros L RNG st LB ra gp tp s0 s1 flags s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m m3 SPV DT WK wksz SRC n lo FF hdw dtb src jw jA jB jC jD j3 y5 y6 y7 y28 y29 y30 y31 Q
         ASH LBH RI RSTK RFS KLO BOT LO SPT SP16 TP ARO AZS ABW RW RSW HWK INW WKL WKH WK4 WR SWS LSB SRCL NR SRH SSS WSRC ASRC INS HSRC
         LTB IND SDS DHI DTWK F64 FH FC RFF RSFF FFD FFA1 FFA2 HR HM AH3 MU03 WM03 FFR03 MI3 FRB3 FRA3 FFC3 SHF3 STG3 TB3 UD3 WC3 UW3 SB3 US3 STL3
         KERR KOK.
  pose proof atop_range as ATR.
  pose proof (spa2_props SPV SP16) as (SPAB & SPA32 & _).
  pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in FHa.
  pose proof (AI_layout AI _ _ _ _ _ AH3) as (LY1 & LY2 & LY3 & LY4 & _).
  destruct (FHL _ _ _ _ _ AH3) as [FAB FABD].
  pose proof (ablk_lin _ _ FAB) as (FA1 & FA2 & FA3 & FA4).
  assert (BSF : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 8 <= 17594333495296)
    by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
  assert (LBH' : ablkLB (FB0 FF :: LB)) by (apply ablkLB_cons; [exact FH| exact LBH]).
  assert (ART3 : art m3) by (apply artcells_art; exact (AI_rtcells AI _ _ _ _ _ AH3)).
  pose proof (fk_inblk_apart AI _ _ _ _ _ _ _ _ WK wksz AH3 INW ltac:(lia)) as DFW.
  pose proof (ablk_disj_band _ _ ABW) as DBW. pose proof (ablk_disj_band _ _ FH) as DBF.
  assert (INCONS : forall X k, ainblk LB X k -> ainblk (FB0 FF :: LB) X k)
    by (intros X k (b & Hb & H1 & H2); exists b; split; [right; exact Hb| split; [exact H1| exact H2]]).
  (* [comment removed for export] *)
  apply stk_of_rw_cells in WC3. cbn [cells_size csize Nat.add] in WC3. rewrite Nat.add_0_r, Z2Nat.id in WC3 by lia.
  destruct (stk_split bsegs _ WK (WK + 736) (WK + wksz) WC3 ltac:(lia)) as [W01 W2].
  destruct (stk_carve bsegs _ WK (WK + 736) 112 W01 ltac:(cbn; lia)) as [W0 [jz WZ3]]. clear W01.
  change (Z.of_nat 112) with 112 in W0, WZ3. replace (WK + 736 - 112) with (WK + 624) in W0, WZ3 by lia.
  (* [comment removed for export] *)
  assert (APPR : app_blk (WK + 624) (WK + 624 + 112)) by (apply ablk_app_blk; [eapply ablk_sub; [exact ABW| clear; lia| clear - WR; lia]| clear; lia]).
  assert (AROR : aro RNG m3 (WK + 624) 112).
  { split; [eapply unpoisoned_sub; [exact UW3| clear; lia| clear - WR; lia]|].
    split; [eapply rng_sub'; [exact RW| clear - WR; lia]|].
    destruct (shspan_sub WK wksz (WK + 624) 112 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - WR; lia)) as [S1 S2].
    eapply rng_sub'; [exact RSW| clear - S1 S2; unfold shspan in *; lia]. }
  assert (HULLR : ahull RNG m3 (WK + 624) 112).
  { destruct (fk_ahull_pres RNG m m3 WK wksz WM03 HWK) as (RLO & RHI & H1 & H2 & H3 & H4 & H5 & H6 & W6 & R6).
    exists RLO, RHI. split; [clear - H1; lia|]. split; [clear - H2 WR; lia|]. repeat (split; [assumption|]). exact R6. }
  assert (ASTK : astk RNG lo (SPA2 SPV)) by (split; [exact KLO|]; split; [eapply rng_sub'; [exact RSTK| clear - LO SPAB LY3 SPT; lia]| exact RI]).
  assert (SRLO : WK + 624 + 112 <= lo \/ SPA2 SPV <= WK + 624) by (clear - SWS LO SPAB WR; lia).
  eapply evtF_cut.
  { eapply (zd_memsetZ_proofA RNG (WK + 624) 112 0 (SPA2 SPV));
      first [exact WZ3| exact STL3| exact APPR| exact AROR| exact HULLR| exact ART3| exact ASTK| exact MI3| exact SRLO| reflexivity| clear; lia| clear - LO SPAB; lia
            | clear - SPAB SPT LY3; lia
            | lazymatch goal with |- ?G => idtac "LEFT:" G end]. }
  cbv beta. intros ms' PO.
  destruct PO as (w0 & w1 & w2 & e11 & e12 & e13 & e14 & e15 & e16 & e17 & w3 & w4 & w5 & w6 & m4 & -> & MU4 & WM4 & MI4 & STL4 & WZ4).
  rd_retlit.
  (* [comment removed for export] *)
  assert (DSTK3 : forall X k, SPA2 SPV <= X -> X + k <= SPV -> 0 <= k -> disjoint_from [(SPA2 SPV - 2208, SPA2 SPV); (WK + 624, WK + 624 + 112)] X k).
  { intros X k H1 H2 Hk. cbn [disjoint_from]. clear - H1 H2 Hk SWS SPAB WR LO. repeat split; lia. }
  pose proof (rw_cells_transport _ _ _ _ _ _ FRA3 MU4 WM4 ltac:(apply DSTK3; [unfold X2FRA0; cbn; lia| unfold X2FRA0; cbn; lia| cbn; lia])) as FRA4.
  eapply evtF_cut; [| cbv beta; intros ms' HQ; exact HQ].
  eapply x2_hdr2 with (lo := lo); first [exact STL4| exact MI4| exact FRA4| exact SP16| exact RI| eapply rng_sub'; [exact RSTK| clear - LO LY3 SPT; lia]
                        | clear - LO; lia | clear - BOT; lia | unfold KEND; clear - SPT LY3; lia | idtac].
  intros m5 MU45 WM45 MI5 STL5 ARG5 FRA5. cbv beta.
  assert (MU35 : munch [(SPA2 SPV - 2208, SPA2 SPV); (WK + 624, WK + 624 + 112)] m3 m5).
  { eapply munch_trans; [exact MU4|]. eapply munch_weaken; [| exact MU45]. intros x Hx. cbn [outside] in *. clear - Hx. lia. }
  assert (WM35 : wmono bsegs m3 m5) by (eapply wmono_trans; [exact WM4| exact WM45]).
  (* [comment removed for export] *)
  assert (DSTK4 : forall X k, SPA2 SPV <= X -> X + k <= SPV -> 0 <= k -> disjoint_from [(SPA2 SPV - 2208, SPA2 SPV); (WK + 624, WK + 624 + 112)] X k).
  { intros X k H1 H2 Hk. cbn [disjoint_from]. clear - H1 H2 Hk SWS SPAB WR LO. repeat split; lia. }
  pose proof (rw_cells_transport _ _ _ _ _ _ FRB3 MU35 WM35 ltac:(apply DSTK4; cbn; lia)) as FRB5.
  pose proof (stk_transport_disjoint _ _ _ _ _ _ STG3 MU35 WM35 ltac:(apply DSTK4; lia)) as STG5.
  assert (DFF4 : forall X k, FF <= X -> X + k <= FF + 64 -> 0 <= k -> disjoint_from [(SPA2 SPV - 2208, SPA2 SPV); (WK + 624, WK + 624 + 112)] X k).
  { intros X k H1 H2 Hk. cbn [disjoint_from]. clear - H1 H2 Hk DFW FHa FHb FHc BOT LO SPAB WR. repeat split; lia. }
  pose proof (rw_cells_transport _ _ _ _ _ _ FFC3 MU35 WM35 ltac:(apply DFF4; unfold X2FFHDR; cbn; lia)) as FFC5.
  assert (DSH4 : disjoint_from [(SPA2 SPV - 2208, SPA2 SPV); (WK + 624, WK + 624 + 112)] (Z.shiftr FF 3 + 2147450880) 8).
  { cbn [disjoint_from]. unfold KLS, KHIGH in *. clear - BSF DBW KLO LO SPAB WR FHa FHc ATR. rewrite Z.shiftr_div_pow2 in * by lia. change (2^3) with 8 in *.
    repeat split; Z.div_mod_to_equations; lia. }
  pose proof (rw_cells_transport _ _ _ _ _ _ SHF3 MU35 WM35 ltac:(unfold X2SH; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; exact DSH4)) as SHF5.
  assert (DDT4 : disjoint_from [(SPA2 SPV - 2208, SPA2 SPV); (WK + 624, WK + 624 + 112)] DT (zlen dtb)).
  { rewrite LTB. cbn [disjoint_from]. unfold HUF_DTABLE_BYTES in *. clear - DTWK SDS SPAB WR LO. repeat split; lia. }
  pose proof (u8arr_transport _ _ _ _ _ _ TB3 MU35 WM35 DDT4) as TB5.
  pose proof (stk_transport_disjoint _ _ _ _ _ _ W0 MU35 WM35 ltac:(cbn [disjoint_from]; clear - SWS SPAB WR LO; repeat split; lia)) as W05.
  pose proof (stk_transport_disjoint _ _ _ _ _ _ W2 MU35 WM35 ltac:(cbn [disjoint_from]; clear - SWS SPAB WR LO; repeat split; lia)) as W25.
  assert (DSRC4 : disjoint_from [(SPA2 SPV - 2208, SPA2 SPV); (WK + 624, WK + 624 + 112)] SRC (zlen src)).
  { rewrite LSB. cbn [disjoint_from]. clear - WSRC SSS SPAB WR LO NR. repeat split; lia. }
  pose proof (bytes_at_transport _ _ _ _ _ _ SB3 MU35 DSRC4) as SB5.
  (* [comment removed for export] *)
  assert (AW4 : aappW [(SPA2 SPV - 2208, SPA2 SPV); (WK + 624, WK + 624 + 112)]).
  { unfold aappW. unfold KLS, KLOW, KHIGH in *. apply Forall_cons; [cbn [fst snd]; clear - KLO LO SPAB; lia|].
    apply Forall_cons; [cbn [fst snd]; clear - DBW WR; lia| apply Forall_nil]. }
  assert (USH4 : forall X k, 0 <= X -> 0 < k -> X + k <= KEND -> unpoisoned m3 X (X + k) -> unpoisoned m5 X (X + k)).
  { intros X k X0 Hk XH U. eapply unpoisoned_munch; [exact U| exact MU35|].
    apply aappW_shadow_disjoint; [exact AW4| | | |]; rewrite ?shad_div; unfold ASHOFF, KEND in *; clear - X0 Hk XH; Z.div_mod_to_equations; lia. }
  assert (DT0 : 0 <= DT) by (destruct UD3 as (U & _); exact U).
  pose proof (USH4 DT HUF_DTABLE_BYTES ltac:(lia) ltac:(unfold HUF_DTABLE_BYTES; lia) ltac:(unfold KEND; lia) UD3) as UD5.
  pose proof (USH4 WK wksz ltac:(lia) ltac:(lia) ltac:(unfold KEND; lia) UW3) as UW5.
  assert (US5 : 0 < n -> unpoisoned m5 SRC (SRC + n)) by (intros NP; exact (USH4 SRC n ltac:(lia) NP ltac:(unfold KEND; lia) (US3 NP))).
  (* [comment removed for export] *)
  assert (AH5 : AHEAP AI L RNG st (FB0 FF :: LB) m5).
  { eapply (AI_frame AI); [exact AH3| exact MU35| exact WM35|].
    constructor; [cbn; left; left; clear - BOT LO SPAB SPT LY3; lia|].
    constructor; [| constructor]. cbn. right; left. destruct INW as (b & Hb & B1 & B2). exists b. split; [right; exact Hb| clear - B1 B2 WR; lia]. }
  assert (MU05 : munch ([(WK, WK + wksz); (SPV - SW, SPV)] ++ fake_area L) m m5).
  { eapply munch_trans; [eapply munch_weaken; [| exact MU03]; intros x Hx; cbn [outside app fake_area] in *; clear - Hx; lia|].
    eapply munch_weaken; [| exact MU35]. intros x Hx. cbn [outside app fake_area] in *. clear - Hx SPAB WR. lia. }
  assert (WM05 : wmono bsegs m m5) by (eapply wmono_trans; [exact WM03| exact WM35]).
  assert (FFR35 : ffr_pres [(WK + 624, WK + 624 + 112)] LB m3 m5).
  { eapply (fk_ffr_fin AI L RNG st LB m3 m3 m5 0 FF 64 (shad FF) 0 [(WK + 624, WK + 624 + 112)] [(SPA2 SPV - 2208, SPA2 SPV)]);
      [exact AH3| exact LBH| exact FH| clear - F64; Z.div_mod_to_equations; lia| reflexivity| clear; lia| clear; lia| | | apply ffr_pres_refl| | exact WM35].
    - constructor; [cbn; split; [clear; lia| left; clear - BOT LO SPAB SPT LY3; lia]| constructor].
    - constructor; [cbn; split; [exists WK, (WK + wksz); split; [exact ABW| clear - WR; lia]| clear; lia]| constructor].
    - eapply munch_weaken; [| exact MU35]. intros x Hx. cbn [outside app] in *. clear - Hx. lia. }
  assert (FFR05 : ffr_pres [(WK, WK + wksz)] LB m m5).
  { eapply ffr_pres_trans; [apply ffr_pres_mono_nil1; exact FFR03|].
    intros a Ha HP. apply (FFR35 a Ha). destruct HP as [[HF HO]|HS]; [left; split; [exact HF|]| right; exact HS].
    cbn [outside] in *. clear - HO WR. lia. }
  pose proof (rw_cells_transport _ _ _ _ _ _ WZ4 MU45 WM45 ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; split; [clear - SWS SPAB WR LO; lia| exact I])) as WZ5.
  clear DSTK3 DSTK4 DFF4 DSH4 DDT4 DSRC4 USH4 FRB3 FRA3 FRA4 STG3 FFC3 SHF3 TB3 UD3 UW3 US3 SB3 STL3 W0 W2 WZ3 WZ4 MI3 MU4 WM4 MI4 STL4 MU45 WM45.
  (* [comment removed for export] *)
  assert (ASH' : ashort (FB0 FF :: LB) HUF_RSTATS_DEPTH) by (apply ashort_push; [exact ASH| lia]).
  assert (ART5 : art m5) by (apply artcells_art; exact (AI_rtcells AI _ _ _ _ _ AH5)).
  assert (AFP : afpre AI rng_fs L RNG st (FB0 FF :: LB) m5 lo (SPA2 SPV - 16) HUF_RSTATS_DEPTH).
  { unfold afpre, astk. split; [exact AH5|]. split; [exact ASH'|]. split; [exact ART5|].
    split; [split; [exact KLO| split; [eapply rng_sub'; [exact RSTK| clear - LO SPAB LY3 SPT; lia]| exact RI]]|].
    split; [exact RFS|]. split; [exact BOT|]. split; [clear - SPT SPAB; lia|]. split; [clear - SPA32; Z.div_mod_to_equations; lia|]. split; [exact RSTK| exact LBH']. }
  assert (AW5 : aappW [(WK, WK + wksz); (SPV - SW, SPV)]).
  { unfold aappW. unfold KLS, KLOW, KHIGH in *. apply Forall_cons; [cbn [fst snd]; clear - DBW WR; lia|].
    apply Forall_cons; [cbn [fst snd]; clear - KLO LO; lia| apply Forall_nil]. }
  assert (AZS5 : azstk RNG m5 lo (SPA2 SPV - 16)).
  { eapply azstk_transport_F; [eapply azstk_sub; [exact AZS| clear; lia| clear - LO SPAB; lia| clear - SPAB; lia]| exact MU05| exact WM05| exact AW5| exact FAB
                              | unfold al_fake; clear - LY1 LY2 LY3 LY4; Z.div_mod_to_equations; lia| clear - FA3 BOT; lia| clear - LO SPAB; lia]. }
  assert (ARO5 : aro_client RNG m5) by (eapply aro_client_transport_F; [exact ARO| exact MU05| exact WM05| exact AW5| exact FAB]).
  (* [comment removed for export] *)
  unfold X2SH in SHF5.
  destruct (x1sh_unp m5 FF SHF5 F64 ltac:(clear - FHa FHb; lia) ltac:(clear - FHc ATR; lia)) as [UTL UNB].
  unfold X2FFHDR in FFC5.
  apply (rw_cells_split_CB bsegs _ _ [C8 (Z_to_bv 64 X2_MAGIC_LIVE); C8 (Z_to_bv 64 X2_DESC); C8 (Z_to_bv 64 0x97374)] 32 j3 [C8 (Z_to_bv 64 (fflag L 0 FF))] [8; 4; 12; 4; 4]%nat) in FFC5; [| reflexivity].
  cbn [mk_CB_cells app] in FFC5.
  lazymatch type of FFC5 with rw_cells _ _ _ [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8] =>
    pose proof (proj1 (rd_rw_cells_appA bsegs m5 FF [c0; c1; c2; c3] [c4; c5; c6; c7; c8]) FFC5) as [FH0 FH1];
    pose proof (proj1 (rd_rw_cells_appA bsegs m5 _ [c4] [c5; c6; c7; c8]) FH1) as [FTL FH2];
    pose proof (proj1 (rd_rw_cells_appA bsegs m5 _ [c5] [c6; c7; c8]) FH2) as [FH3 FH4];
    pose proof (proj1 (rd_rw_cells_appA bsegs m5 _ [c6] [c7; c8]) FH4) as [FNB FH5]; clear FH1 FH2 FH4 end.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul app] in FTL, FH3, FNB, FH5.
  match type of FTL with rw_cells _ _ ?a _ => replace a with (FF + 32) in FTL by lia end.
  match type of FH3 with rw_cells _ _ ?a _ => replace a with (FF + 36) in FH3 by lia end.
  match type of FNB with rw_cells _ _ ?a _ => replace a with (FF + 48) in FNB by lia end.
  match type of FH5 with rw_cells _ _ ?a _ => replace a with (FF + 52) in FH5 by lia end.
  apply stk_of_rw_cells in FTL. apply stk_of_rw_cells in FNB. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FTL, FNB.
  match type of FNB with stk _ _ _ ?h => replace h with (FF + 48 + 4) in FNB by lia end.
  match type of FTL with stk _ _ _ ?h => replace h with (FF + 32 + 4) in FTL by lia end.
  (* [comment removed for export] *)
  lazymatch type of WZ5 with rw_cells _ _ _ [CB ?k ?zs] =>
    apply (rw_cells_split_CB bsegs _ _ [] k zs [] [52; 60]%nat) in WZ5; [| reflexivity] end.
  cbn [mk_CB_cells app] in WZ5.
  lazymatch type of WZ5 with rw_cells _ _ _ [?c0; ?c1] =>
    pose proof (proj1 (rd_rw_cells_appA bsegs m5 _ [c0] [c1]) WZ5) as [ZRS ZR0]; clear WZ5 end.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul app] in ZR0.
  match type of ZR0 with rw_cells _ _ ?a _ => replace a with (WK + 676) in ZR0 by lia end.
  lazymatch type of ZR0 with rw_cells _ _ _ [CB 60 ?z] => replace z with (repeat (Z_to_bv 8 0) 60) in ZR0 by (vm_compute; reflexivity) end.
  apply stk_of_rw_cells in ZRS. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul] in ZRS.
  match type of ZRS with stk _ _ _ ?h => replace h with (WK + 624 + 52) in ZRS by lia end.
  destruct (stk_split bsegs _ (WK + 736) (WK + 992) (WK + wksz) W25 ltac:(lia)) as [SG1 W3].
  destruct (stk_split bsegs _ (WK + 992) (WK + 1248) (WK + wksz) W3 ltac:(lia)) as [SHW W4].
  destruct (stk_split bsegs _ (WK + 1248) (WK + 2124) (WK + wksz) W4 ltac:(lia)) as [SWK SG3]. clear W25 W3 W4.
  (* [comment removed for export] *)
  pose proof (proj1 (rd_rw_cells_appA bsegs m5 _ [C8 (Z_to_bv 64 876)] [C8 flags]) ARG5) as [ARGA _].
  destruct ARGA as [[_ ARGB] _]. cbn [cells_bytes cbytes app] in ARGB. rewrite app_nil_r in ARGB.
  assert (DFS : 0 < n -> FF + 64 <= SRC \/ SRC + n <= FF).
  { intros NP. destruct (INS NP) as [IB|[IM1 IM2]]; [| unfold AIMG_HI in IM2; lia].
    pose proof (fk_inblk_apart AI _ _ _ _ _ _ _ _ SRC n AH3 IB ltac:(lia)). lia. }
  eapply evtF_cut.
  { eapply (RS L RNG st (FB0 FF :: LB)) with (lo := lo) (B := WK) (bsz := wksz) (wksz := 876) (src := src);
    first [ exact AFP | exact AZS5 | exact TP | exact ARO5 | exact MI5 | exact STL5 | exact ARGB | exact SB5 | exact LSB
          | exact SHW | exact ZRS | exact FNB | exact FTL
          | replace (WK + 992 + 256) with (WK + 1248) by lia; exact SHW | replace (FF + 48 + 4) with (FF + 52) by lia; exact FNB
          | replace (WK + 1248 + 876) with (WK + 2124) by lia; exact SWK
          | intros _; split; [exact ABW| split; [exact UW5| split; [exact RW| exact RSW]]]
          | eapply fk_ahull_pres; [exact WM05| exact HWK]
          | apply INCONS; exact INW
          | split; [exact UNB| split; [eapply rng_sub'; [exact RFF| lia]| eapply rng_sub'; [exact RSFF| unfold shspan; rewrite !shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia]]]
          | split; [exact UTL| split; [eapply rng_sub'; [exact RFF| lia]| eapply rng_sub'; [exact RSFF| unfold shspan; rewrite !shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia]]]
          | exists (FB0 FF); split; [left; reflexivity| cbn; lia]
          | intros NP; destruct (ASRC NP) as (A1 & A2 & A3); split; [exact A1| split; [exact (US5 NP)| split; [exact A2| exact A3]]]
          | intros NP; destruct (INS NP) as [IB|IMG]; [left; apply INCONS; exact IB| right; exact IMG]
          | intros NP; eapply fk_ahull_pres; [exact WM05| exact (HSRC NP)]
          | unfold KHIGH in *; lia
          | clear - WK4; Z.div_mod_to_equations; lia
          | clear - F64 FHa FHb FHc; Z.div_mod_to_equations; lia
          | lazymatch goal with |- ?G => idtac "LEFT:" G end ]. }
  all: cbv beta.
  intros ms' PO.
  destruct PO as (w0' & w1' & w2' & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3' & w4' & w5' & w6' & m6 & r & -> & MU6 & WM6 & MI6 & ST6 & FFR6 & AH6 & SWK6 & Hr & RES).
  rd_retlit.
  (* [comment removed for export] *)
  assert (BLO : forall b, In b LB -> ab_addr b + ab_size b <= lo).
  { intros b Hb. pose proof (ablk_lin _ _ (LBH b Hb)) as (_ & _ & L3 & _). lia. }
  set (W6 := [(WK + 992, WK + 992 + 256); (WK + 624, WK + 624 + 52); (FF + 48, FF + 48 + 4); (FF + 32, FF + 32 + 4); (WK + 1248, WK + 1248 + 876);
              (SPA2 SPV - 16 - HUF_RSTATS_STACK_A, SPA2 SPV - 16)]) in MU6.
  set (W6f := [(WK + 992, WK + 992 + 256); (WK + 624, WK + 624 + 52); (FF + 48, FF + 48 + 4); (FF + 32, FF + 32 + 4); (WK + 1248, WK + 1248 + 876)]) in FFR6.
  assert (FFR6' : ffr_pres W6 (FB0 FF :: LB) m5 m6).
  { eapply magree_mono; [exact FFR6|]. intros a [[HF HO]|HS]; [| right; exact HS]. left; split; [exact HF|].
    subst W6 W6f; cbn [outside app] in HO |- *. destruct HO as (O1 & O2 & O3 & O4 & O5 & _). exact (conj O1 (conj O2 (conj O3 (conj O4 (conj O5 I))))). }
  assert (AW6 : aappW W6).
  { subst W6. unfold aappW. unfold KLS, KLOW, KHIGH in *.
    repeat (apply Forall_cons; [cbn [fst snd]; clear - DBW DBF WKH WR KLO LO SPAB FHa FHb FHc; unfold KHIGH in *; lia|]). apply Forall_nil. }
  (* [comment removed for export] *)
  assert (DSTK : forall X k, SPA2 SPV - 16 <= X -> X + k <= SPV -> 0 <= k -> disjoint_from (W6 ++ fake_area L) X k).
  { intros X k H1 H2 Hk. subst W6. unfold AIMG_HI in FA1.
    cbn [disjoint_from app fake_area]. rewrite !shad_div. unfold FAKESZ, ASHOFF in *.
    clear - H1 H2 Hk SWS SPAB FHa FHb FHc FC BOT FA1 FA3 LO WR WKH ATR. repeat split; Z.div_mod_to_equations; lia. }
  pose proof (rw_cells_transport _ _ _ _ _ _ FRB5 MU6 WM6 ltac:(apply DSTK; cbn; lia)) as FRB6.
  pose proof (rw_cells_transport _ _ _ _ _ _ FRA5 MU6 WM6 ltac:(apply DSTK; [unfold X2FRA0; cbn; lia| unfold X2FRA0; cbn; lia| cbn; lia])) as FRA6.
  pose proof (rw_cells_transport _ _ _ _ _ _ ARG5 MU6 WM6 ltac:(apply DSTK; cbn; lia)) as ARG6.
  pose proof (stk_transport_disjoint _ _ _ _ _ _ STG5 MU6 WM6 ltac:(apply DSTK; lia)) as STG6.
  apply stk_of_rw_cells in ARG6. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in ARG6.
  match type of ARG6 with stk _ _ _ ?h => replace h with (SPA2 SPV) in ARG6 by lia end.
  pose proof (stk_merge bsegs m6 lo (SPA2 SPV - 16) (SPA2 SPV) ST6 ARG6 ltac:(lia)) as STL6.
  (* [comment removed for export] *)
  assert (PFF : forall a, FF <= a < FF + 64 -> ~ (FF + 32 <= a < FF + 36) -> ~ (FF + 48 <= a < FF + 52) ->
            (in_fake (FB0 FF :: LB) a /\ outside W6f a) \/ (exists a', in_fake (FB0 FF :: LB) a' /\ a = shad a')).
  { intros a Ha N1 N2. left. split; [exists 0, FF, 64; split; [left; reflexivity| lia]|].
    subst W6f. cbn [outside]. unfold KLS in DBF. clear - Ha N1 N2 DFW WKH WR FC BOT SPAB LO. repeat split; lia. }
  assert (PSH : forall a, Z.shiftr FF 3 + 2147450880 <= a < Z.shiftr FF 3 + 2147450880 + 8 ->
            (in_fake (FB0 FF :: LB) a /\ outside W6f a) \/ (exists a', in_fake (FB0 FF :: LB) a' /\ a = shad a')).
  { intros a Ha. right. exists (8 * (a - 2147450880)). split; [exists 0, FF, 64; split; [left; reflexivity| rewrite Z.shiftr_div_pow2 in Ha by lia; Z.div_mod_to_equations; lia]|].
    rewrite shad_div. unfold ASHOFF. rewrite Z.shiftr_div_pow2 in Ha by lia. Z.div_mod_to_equations. lia. }
  pose proof (rw_cells_magree _ _ _ _ _ _ FFR6 FH0 ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; intros a Ha; apply PFF; lia)) as FH0'.
  pose proof (rw_cells_magree _ _ _ _ _ _ FFR6 FH3 ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; intros a Ha; apply PFF; lia)) as FH3'.
  pose proof (rw_cells_magree _ _ _ _ _ _ FFR6 FH5 ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; intros a Ha; apply PFF; lia)) as FH5'.
  pose proof (rw_cells_magree _ _ _ _ _ _ FFR6 SHF5 ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; intros a Ha; apply PSH; lia)) as SHF6.
  (* [comment removed for export] *)
  pose proof (fk_inblk_apart AI _ _ _ _ _ _ _ _ DT HUF_DTABLE_BYTES AH3 IND ltac:(unfold HUF_DTABLE_BYTES; lia)) as DFD.
  assert (DDT : disjoint_from W6 DT (zlen dtb)).
  { subst W6. rewrite LTB. cbn [disjoint_from]. unfold HUF_DTABLE_BYTES in *. clear - DTWK DFD SDS SPAB WKH WR LO. repeat split; try exact I; lia. }
  pose proof (fcall_u8arr_pres AI FHL _ _ _ _ _ _ _ _ _ _ AH5 ltac:(apply INCONS; rewrite LTB; exact IND) DDT MU6 WM6 FFR6' TB5) as TB6.
  pose proof (fcall_unp_pres AI FHL _ _ _ _ _ _ _ _ _ _ AH5 ltac:(apply INCONS; exact IND) ltac:(unfold HUF_DTABLE_BYTES; lia) ltac:(unfold KEND; lia) AW6 MU6 FFR6' UD5) as UD6.
  pose proof (fcall_unp_pres AI FHL _ _ _ _ _ _ _ _ _ _ AH5 ltac:(apply INCONS; exact INW) ltac:(lia) ltac:(unfold KEND; lia) AW6 MU6 FFR6' UW5) as UW6.
  assert (WSUB : forall a k, WK <= a -> a + k <= WK + wksz -> 0 <= k -> ainblk (FB0 FF :: LB) a k).
  { intros a k H1 H2 Hk. destruct INW as (b & Hb & B1 & B2). exists b. split; [right; exact Hb| lia]. }
  pose proof (fcall_stk_pres AI FHL L RNG st (FB0 FF :: LB) m5 m5 m6 W6 WK (WK + 624) AH5 ltac:(apply WSUB; lia) ltac:(subst W6; cbn [disjoint_from]; clear - DFW WKH WR SPAB SWS LO; repeat split; try exact I; lia) MU6 WM6 FFR6' W05) as W06.
  pose proof (fcall_stk_pres AI FHL L RNG st (FB0 FF :: LB) m5 m5 m6 W6 (WK + 736) (WK + 992) AH5 ltac:(apply WSUB; lia) ltac:(subst W6; cbn [disjoint_from]; clear - DFW WKH WR SPAB SWS LO; repeat split; try exact I; lia) MU6 WM6 FFR6' SG1) as SG1'.
  pose proof (fcall_stk_pres AI FHL L RNG st (FB0 FF :: LB) m5 m5 m6 W6 (WK + 2124) (WK + wksz) AH5 ltac:(apply WSUB; lia) ltac:(subst W6; cbn [disjoint_from]; clear - DFW WKH WR SPAB SWS LO; repeat split; try exact I; lia) MU6 WM6 FFR6' SG3) as SG3'.
  pose proof (fcall_cells_pres AI FHL L RNG st (FB0 FF :: LB) m5 m5 m6 W6 (WK + 676) [CB 60 (repeat (Z_to_bv 8 0) 60)] AH5 ltac:(apply WSUB; cbn; lia) ltac:(subst W6; cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; clear - DFW WKH WR SPAB SWS LO; repeat split; try exact I; lia) MU6 WM6 FFR6' ZR0) as ZR06.
  (* [comment removed for export] *)
  assert (MU06 : munch ([(WK, WK + wksz); (SPV - SW, SPV)] ++ fake_area L) m m6).
  { eapply munch_trans; [exact MU05|].
    eapply munch_weaken; [| exact MU6]. intros x Hx. subst W6. cbn [outside app fake_area] in *. unfold FAKESZ in *.
    clear - Hx FFA1 FFA2 SPAB WR. lia. }
  assert (WM06 : wmono bsegs m m6) by (eapply wmono_trans; [exact WM05| exact WM6]).
  assert (FFR06 : ffr_pres [(WK, WK + wksz)] LB m m6).
  { eapply ffr_pres_trans; [exact FFR05|].
    eapply magree_mono; [exact FFR6|]. intros a [[(c & A & k & Hb & Ha) HO]|(a' & (c & A & k & Hb & Ha) & ->)].
    - left. split; [exists c, A, k; split; [right; exact Hb| exact Ha]|].
      pose proof (FFD _ Hb) as D1. pose proof (BLO _ Hb) as D2. cbn [ab_addr ab_size] in D1, D2.
      subst W6f. cbn [outside] in *. clear - HO D1 D2 Ha SPAB WR. repeat split; try exact I; lia.
    - right. exists a'. split; [exists c, A, k; split; [right; exact Hb| exact Ha]| reflexivity]. }
  (* [comment removed for export] *)
  zstep. zstep. replace (Z_to_bv 64 (-120)) with (Z_to_bv 64 18446744073709551496) by (apply Z_to_bv_eqm; reflexivity).
  replace (SPA2 SPV - 16 + 16) with (SPA2 SPV) by lia.
  unfold X2FRA0 in FRA6.
  (* [comment removed for export] *)
  clear SSS WSRC DFD DFS INS HSRC ASRC SB5 US5 UD5 UW5 TB5 ST6 ARG6 FFR6 FFR6' PFF PSH DDT WSUB AW6 DSTK BLO INCONS MU6 AW5 AW4 AZS5 ARO5 AFP AZS ARO MU05 MU35 MU03
        APPR AROR HULLR ASTK.
  zstep. bcase KI.
  - (* [comment removed for export] *)
    assert (ERR : zd_is_error r = true) by (unfold zd_is_error, ZE_maxCode; apply Z.ltb_lt; rewrite ?unsigned_lit in KI by lia; lia).
    destruct RES as [(NE & _)|(_ & SHW6 & SRS6 & SNB6 & STL6')]; [rewrite ERR in NE; discriminate|].
    zstep. zstep. zstep.
    apply evtF_done. eapply KERR; try eassumption.
    + eapply munch_weaken; [| exact MU06]. intros x Hx. cbn [outside app fake_area] in *. clear - Hx. lia.
    + intros a Ha HP. apply (FFR06 a Ha). destruct HP as [[HF HO]|HS]; [left; split; [exact HF|]| right; exact HS].
      cbn [outside] in *. clear - HO. lia.
    + exact (proj1 (proj1 (rd_rw_cells_appA bsegs m6 FF [C8 (Z_to_bv 64 X2_MAGIC_LIVE)] _) FH0')).
    + pose proof (proj2 (proj1 (rd_rw_cells_appA bsegs m6 _ [CB 4 _] _) FH5')) as G4. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in G4.
      match type of G4 with rw_cells _ _ ?a _ => replace a with (FF + 56) in G4 by lia end. exact G4.
    + lazymatch type of FRA6 with rw_cells _ _ _ [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8; ?c9; ?c10; ?c11] =>
        pose proof (proj1 (proj1 (rd_rw_cells_appA bsegs m6 _ [c6; c7] [c8; c9; c10; c11]) (proj2 (proj1 (rd_rw_cells_appA bsegs m6 _ [c0; c1; c2; c3; c4; c5] _) FRA6)))) as G5 end.
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul app] in G5.
      match type of G5 with rw_cells _ _ ?a _ => replace a with (SPA2 SPV + 112) in G5 by lia end. exact G5.
    + lazymatch type of FRA6 with rw_cells _ _ _ [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8; ?c9; ?c10; ?c11] =>
        pose proof (proj1 (proj1 (rd_rw_cells_appA bsegs m6 _ [c0; c1; c2; c3; c4; c5] _) FRA6)) as G6 end.
      apply stk_of_rw_cells in G6. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul] in G6.
      match type of G6 with stk _ _ _ ?h => replace h with (SPA2 SPV + 112) in G6 by lia end.
      exact (stk_merge bsegs m6 lo (SPA2 SPV) (SPA2 SPV + 112) STL6 G6 ltac:(lia)).
    + lazymatch type of FRA6 with rw_cells _ _ _ [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8; ?c9; ?c10; ?c11] =>
        pose proof (proj2 (proj1 (rd_rw_cells_appA bsegs m6 _ [c0; c1; c2; c3; c4; c5; c6; c7] [c8; c9; c10; c11]) FRA6)) as G7 end.
      apply stk_of_rw_cells in G7. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul] in G7.
      match type of G7 with stk _ _ ?a _ => replace a with (SPA2 SPV + 128) in G7 by lia end.
      match type of G7 with stk _ _ _ ?h => replace h with (SPA2 SPV + 728) in G7 by lia end.
      exact (stk_merge bsegs m6 (SPA2 SPV + 128) (SPA2 SPV + 728) (SPV + -104) G7 STG6 ltac:(lia)).
    + match type of SHW6 with stk _ _ _ ?h => replace h with (WK + 1248) in SHW6 by lia end.
      match type of SRS6 with stk _ _ _ ?h => replace h with (WK + 676) in SRS6 by lia end.
      apply stk_of_rw_cells in ZR06. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul] in ZR06.
      match type of ZR06 with stk _ _ _ ?h => replace h with (WK + 736) in ZR06 by lia end.
      match type of SWK6 with stk _ _ _ ?h => replace h with (WK + 2124) in SWK6 by lia end.
      pose proof (stk_merge bsegs m6 WK (WK + 624) (WK + 676) W06 SRS6 ltac:(lia)) as M1.
      pose proof (stk_merge bsegs m6 WK (WK + 676) (WK + 736) M1 ZR06 ltac:(lia)) as M2.
      pose proof (stk_merge bsegs m6 WK (WK + 736) (WK + 992) M2 SG1' ltac:(lia)) as M3.
      pose proof (stk_merge bsegs m6 WK (WK + 992) (WK + 1248) M3 SHW6 ltac:(lia)) as M4.
      pose proof (stk_merge bsegs m6 WK (WK + 1248) (WK + 2124) M4 SWK6 ltac:(lia)) as M5.
      exact (stk_merge bsegs m6 WK (WK + 2124) (WK + wksz) M5 SG3' ltac:(lia)).
  - (* [comment removed for export] *)
    assert (NER : zd_is_error r = false) by (unfold zd_is_error, ZE_maxCode; apply Z.ltb_ge; rewrite ?unsigned_lit in KI by lia; lia).
    destruct RES as [(_ & RR & hw & rank & tl & nbs & HW6 & LHW & BHW & RK6 & CNB & CTL & STATS & NBSR)|(EE & _)]; [| rewrite NER in EE; discriminate].
    pose proof STATS as (T1 & T2 & T3 & T4 & T5 & T6).
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    rewrite (sx32w_small tl) by (clear - T1; lia).   (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch type of MU06 with ?T => change T with (bx T) in MU06 end.   (* [comment removed for export] *)
    lazymatch type of RK6 with ?T => change T with (bx T) in RK6 end.   (* [comment removed for export] *)
    zstep. bcase KT; [| exfalso; rewrite ?unsigned_lit in KT by (clear - T1; lia); clear - KT T1; lia].   (* [comment removed for export] *)
    unfold bx in MU06, RK6.
    apply evtF_done.
    assert (FRA7 : rw_cells bsegs m6 (SPA2 SPV) (X2FRA FF DT WK hdw jA jB jC jD)) by (unfold X2FRA; exact FRA6).
    pose proof (X2FRA_lens _ _ _ _ _ _ _ _ _ _ FRA7) as (LNA & LNB & LNC & LND).
    eapply KOK; try eassumption.
    + unfold X2FFB. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in FH3', FH5'.
      lazymatch type of FH0' with rw_cells _ _ _ [?c0; ?c1; ?c2; ?c3] =>
        apply (proj2 (rd_rw_cells_appA bsegs _ FF [c0; c1; c2; c3] _)) end.
      split; [eassumption|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add].
      apply (proj2 (rd_rw_cells_appA bsegs _ _ [C4 (Z_to_bv 64 tl)] _)).
      split; [lazymatch type of CTL with rw_cells _ _ ?a _ => lazymatch goal with |- rw_cells _ _ ?b _ => replace b with a by lia end end; eassumption|].
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add].
      lazymatch type of FH3' with rw_cells _ _ _ [?c] => apply (proj2 (rd_rw_cells_appA bsegs _ _ [c] _)) end.
      split; [lazymatch type of FH3' with rw_cells _ _ ?a _ => lazymatch goal with |- rw_cells _ _ ?b _ => replace b with a by lia end end; eassumption|].
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add].
      apply (proj2 (rd_rw_cells_appA bsegs _ _ [C4 (Z_to_bv 64 nbs)] _)).
      split; [lazymatch type of CNB with rw_cells _ _ ?a _ => lazymatch goal with |- rw_cells _ _ ?b _ => replace b with a by lia end end; eassumption|].
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add].
      first [ eassumption | lazymatch type of FH5' with rw_cells _ _ ?a _ => lazymatch goal with |- rw_cells _ _ ?b _ => replace b with a by lia end end; eassumption ].
    + match type of SWK6 with stk _ _ _ ?h => replace h with (WK + 2124) in SWK6 by lia end.
      lazymatch goal with |- stk _ ?mq _ _ => exact (stk_merge bsegs mq (WK + 1248) (WK + 2124) (WK + wksz) ltac:(eassumption) ltac:(eassumption) ltac:(lia)) end.
Qed.
End Asm.
End CANSEC1.
