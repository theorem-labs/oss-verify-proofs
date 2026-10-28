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
     FsKit AZ_kit AZ_globals AZ_globalsR AZ_fkit AZ_huf_iface AZ_hft_iface AZ_hft_rs_iface AF_fse_rd_base AF_fse_rd_mem AF_fse_rd_seg AF_fse_rd_asm AZ_hft_x1_seg AZ_hft_x1_env.
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
Lemma artcells_art : forall m, artcells m -> art m.
Proof.
  intros m (C0 & GOT & RIC & REAL & SHB & SUA & INI & LAY & _). unfold art.
  split; [exact GOT|]. split; [exact RIC|]. split; [exact SHB|]. split; [exact INI|]. split; [exact LAY| exact REAL].
Qed.

(* [comment removed for export] *)
Lemma x1sh_unp : forall m FF, rw_cells bsegs m (Z.shiftr FF 3 + 2147450880) X1SH -> FF mod 64 = 0 -> 0 <= FF -> FF + 64 <= 2^47 ->
  unpoisoned m (FF + 32) (FF + 32 + 4) /\ unpoisoned m (FF + 48) (FF + 48 + 4).
Proof.
  intros m FF H F64 F0 FH. unfold X1SH in H. rewrite Z.shiftr_div_pow2 in H by lia. change (2^3) with 8 in H.
  pose proof (proj1 (rd_rw_cells_appA bsegs m _ [C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601);
                                            C1 (Z_to_bv 8 18446744073709551601)] _) H) as [_ H4]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in H4.
  pose proof (proj1 (rd_rw_cells_appA bsegs m _ [C1 (Z_to_bv 8 4)] _) H4) as [H4a H5]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in H5.
  pose proof (proj1 (rd_rw_cells_appA bsegs m _ [C1 (Z_to_bv 8 18446744073709551602)] _) H5) as [_ H6]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in H6.
  pose proof (proj1 (rd_rw_cells_appA bsegs m _ [C1 (Z_to_bv 8 4)] _) H6) as [H6a _].
  assert (R4 : m (wa (FF / 8 + 2147450880 + 4)) = Some (Z_to_bv 8 4)) by (apply (rw_C1_high m _ _ H4a); lia).
  assert (R6 : m (wa (FF / 8 + 2147450880 + 4 + 1 + 1)) = Some (Z_to_bv 8 4)) by (apply (rw_C1_high m _ _ H6a); lia).
  split; (split; [lia|]; split; [lia|]; intros G HG H1 H2; exists (Z_to_bv 8 4); split;
    [ unfold ASHOFF | right; change (sval (Z_to_bv 8 4)) with 4; lia ]).
  - replace G with (FF / 8 + 4) by (Z.div_mod_to_equations; lia). replace (2147450880 + (FF / 8 + 4)) with (FF / 8 + 2147450880 + 4) by lia. exact R4.
  - replace G with (FF / 8 + 6) by (Z.div_mod_to_equations; lia). replace (2147450880 + (FF / 8 + 6)) with (FF / 8 + 2147450880 + 4 + 1 + 1) by lia. exact R6.
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
Notation SW := 5520 (only parsing).     (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma x1_callZ : forall (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
    (ra gp tp s0 s1 flags s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m m3 : amem)
    (SPV DT WK wksz SRC n lo FF : Z) (dtb src jw jA jC jD jB jE j3 j5 j6 : list byte) (y5 y6 y7 y28 y29 y30 y31 : word) (Q : machine_state -> Prop),
  ashort LB HUF_TBL_DEPTH -> ablkLB LB -> rng_aimg RNG -> rng RNG lo (al_top L - lo) -> rng_fs L RNG -> KHIGH <= lo ->
  ATOP + 4096 <= lo -> lo <= SPV - HUF_TBL_STACK_A -> SPV + 16 < al_top L -> SPV mod 16 = 0 -> tp = Z_to_bv 64 ATP ->
  aro_client RNG m -> azstk RNG m lo SPV ->
  ablk WK (WK + wksz) -> rng RNG WK wksz -> rng RNG (shad WK) (shspan WK wksz) -> ahull RNG m WK wksz -> ainblk LB WK wksz ->
  4096 <= WK -> WK + wksz < 2^47 -> WK mod 4 = 0 -> 1492 <= wksz < 2^32 -> (WK + wksz <= lo \/ SPV <= WK) ->
  zlen src = n -> 4096 <= SRC -> 0 <= n < 2^32 -> SRC + n < 2^47 -> (SRC + n <= lo \/ SPV <= SRC) -> (WK + wksz <= SRC \/ SRC + n <= WK) ->
  (0 < n -> ablk SRC (SRC + n) /\ rng RNG SRC n /\ rng RNG (shad SRC) (shspan SRC n)) -> (0 < n -> ainimg LB SRC n) -> (0 < n -> ahull RNG m SRC n) ->
  zlen dtb = HUF_DTABLE_BYTES -> ainblk LB DT HUF_DTABLE_BYTES -> (DT + HUF_DTABLE_BYTES <= lo \/ SPV <= DT) -> DT + HUF_DTABLE_BYTES <= 2^47 ->
  (DT + HUF_DTABLE_BYTES <= WK \/ WK + wksz <= DT) ->
  (* [comment removed for export] *)
  FF mod 64 = 0 -> ablk FF (FF + 64) -> FF + 64 <= ATOP -> rng RNG FF 64 -> rng RNG (shad FF) 8 ->
  (forall b, In b LB -> FF + 64 <= ab_addr b \/ ab_addr b + ab_size b <= FF) ->
  al_fake L <= FF -> FF + 64 <= al_fake L + FAKESZ ->
  AHEAP AI L RNG st (FB0 FF :: LB) m3 ->
  munch ([(SPV - SW, SPV)] ++ fake_area L) m m3 -> wmono bsegs m m3 -> ffr_pres [] LB m m3 -> mem_inv bsegs m3 ->
  rw_cells bsegs m3 (SPV + -104) (X1SAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  rw_cells bsegs m3 (SPA1 SPV) (X1FRA FF DT WK jA jC jD jB jE) ->
  rw_cells bsegs m3 FF (X1FFHDR (fflag L 0 FF) j3 j5 j6 (Z_to_bv 64 0) (Z_to_bv 64 0)) -> rw_cells bsegs m3 (Z.shiftr FF 3 + 2147450880) X1SH ->
  stk bsegs m3 (SPA1 SPV + 312) (SPV + -104) ->
  u8arr bsegs m3 DT dtb -> unpoisoned m3 DT (DT + HUF_DTABLE_BYTES) ->
  rw_cells bsegs m3 WK [CB (Z.to_nat wksz) jw] -> unpoisoned m3 WK (WK + wksz) ->
  bytes_at bsegs m3 SRC src -> (0 < n -> unpoisoned m3 SRC (SRC + n)) ->
  stk bsegs m3 lo (SPA1 SPV - 16) -> rw_cells bsegs m3 (SPA1 SPV - 16) [C8 (Z_to_bv 64 876); C8 flags] ->
  (* [comment removed for export] *)
  (forall (m5 : amem) (r : Z) (z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 : word),
     zd_is_error r = true -> 0 <= r < 2^64 ->
     AHEAP AI L RNG st (FB0 FF :: LB) m5 ->
     munch ([(DT, DT + HUF_DTABLE_BYTES); (WK, WK + wksz); (SPV - SW, SPV)] ++ fake_area L) m m5 -> wmono bsegs m m5 -> mem_inv bsegs m5 ->
     ffr_pres [(DT, DT + HUF_DTABLE_BYTES); (WK, WK + wksz)] LB m m5 ->
     rw_cells bsegs m5 (Z.shiftr FF 3 + 2147450880) X1SH ->
     rw_cells bsegs m5 FF [C8 (Z_to_bv 64 X1_MAGIC_LIVE)] -> rw_cells bsegs m5 (FF + 56) [C8 (Z_to_bv 64 (fflag L 0 FF))] ->
     rw_cells bsegs m5 (SPV + -104) (X1SAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
     rw_cells bsegs m5 (SPA1 SPV + 80) [C8 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF)] ->
     stk bsegs m5 lo (SPA1 SPV + 80) -> stk bsegs m5 (SPA1 SPV + 104) (SPV + -104) ->
     u8arr bsegs m5 DT dtb -> stk bsegs m5 WK (WK + wksz) ->
     Q (MS (mkR z1 (Z_to_bv 64 (SPA1 SPV)) gp tp z5 z6 z7 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPA1 SPV)) z10 z11 z12 z13 z14 z15 z16 z17
              (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (WK + 1236)) (Z_to_bv 64 r)
              (Z_to_bv 64 n) (Z_to_bv 64 SRC) flags (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 (FF + 48)) z28 z29 z30 z31)
           FR (Z_to_bv 64 0x970d8) fc None m5 (seg_rom bsegs))) ->
  (* [comment removed for export] *)
  (forall (m5 : amem) (r nbs tl : Z) (hw rank : list Z) (jA' : list byte) (z5 z6 z7 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 : word),
     zd_is_error r = false -> 1 <= r <= n ->
     AHEAP AI L RNG st (FB0 FF :: LB) m5 ->
     munch ([(WK, WK + wksz); (SPV - SW, SPV)] ++ fake_area L) m m5 -> wmono bsegs m m5 -> mem_inv bsegs m5 ->
     ffr_pres [(WK, WK + wksz)] LB m m5 ->
     rw_cells bsegs m5 (SPV + -104) (X1SAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
     rw_cells bsegs m5 (SPA1 SPV) (X1FRA FF DT WK jA' jC jD jB jE) ->
     rw_cells bsegs m5 (SPA1 SPV + 56) [C8 (Z_to_bv 64 r)] ->
     rw_cells bsegs m5 FF (X1FFHDR (fflag L 0 FF) j3 j5 j6 (Z_to_bv 64 tl) (Z_to_bv 64 nbs)) -> rw_cells bsegs m5 (Z.shiftr FF 3 + 2147450880) X1SH ->
     stk bsegs m5 (SPA1 SPV + 312) (SPV + -104) -> stk bsegs m5 lo (SPA1 SPV) ->
     u8arr bsegs m5 DT dtb -> unpoisoned m5 DT (DT + HUF_DTABLE_BYTES) ->
     u8arr bsegs m5 (WK + 1236) (map (Z_to_bv 8) hw) -> zlen hw = 256 -> Forall (fun v => 0 <= v < 256) hw ->
     u32arr bsegs m5 WK (map (Z_to_bv 64) rank) -> stk bsegs m5 (WK + 52) (WK + 1236) -> stk bsegs m5 (WK + 1492) (WK + wksz) ->
     unpoisoned m5 WK (WK + wksz) ->
     huf_stats_ok (firstn (Z.to_nat nbs) hw) rank tl -> 2 <= nbs <= 256 ->
     Q (MS (mkR (Z_to_bv 64 0x962bc) (Z_to_bv 64 (SPA1 SPV)) gp tp z5 z6 z7 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPA1 SPV))
              (Z_to_bv 64 r) (Z_to_bv 64 18446744073709551496) z12 z13 z14 z15 z16 z17
              (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (WK + 1236)) (Z_to_bv 64 18446744073709551572)
              (Z_to_bv 64 n) (Z_to_bv 64 SRC) flags (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 (FF + 48)) z28 z29 z30 z31)
           FR (Z_to_bv 64 0x962cc) fc None m5 (seg_rom bsegs))) ->
  evtF bsegs RNG Q
    (MS (mkR (Z_to_bv 64 0x962bc) (Z_to_bv 64 (SPA1 SPV - 16)) gp tp y5 y6 y7 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPA1 SPV))
             (Z_to_bv 64 (WK + 1236)) (Z_to_bv 64 256) (Z_to_bv 64 WK) (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 SRC) (Z_to_bv 64 n) (Z_to_bv 64 (WK + 104))
             (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (WK + 1236)) (Z_to_bv 64 18446744073709551572)
             (Z_to_bv 64 n) (Z_to_bv 64 SRC) flags (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 (FF + 48)) y28 y29 y30 y31)
        FR (Z_to_bv 64 0xab294) fc None m3 (seg_rom bsegs)).
Proof.
  intros L RNG st LB ra gp tp s0 s1 flags s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m m3 SPV DT WK wksz SRC n lo FF dtb src jw jA jC jD jB jE j3 j5 j6 y5 y6 y7 y28 y29 y30 y31 Q
         ASH LBH RI RSTK RFS KLO BOT LO SPT SP16 TP ARO AZS ABW RW RSW HWK INW WKL WKH WK4 WR SWS LSB SRCL NR SRH SSS WSRC ASRC INS HSRC
         LTB IND SDS DHI DTWK F64 FH FC RFF RSFF FFD FFA1 FFA2 AH3 MU03 WM03 FFR03 MI3 FRB3 FRA3 FFC3 SHF3 STG3 TB3 UD3 WC3 UW3 SB3 US3 STL3 ARG3
         KERR KOK.
  pose proof atop_range as ATR.
  pose proof (spa1_props SPV SP16) as (SPAB & SPA32 & _).
  pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in FHa.
  pose proof (AI_layout AI _ _ _ _ _ AH3) as (LY1 & LY2 & LY3 & LY4 & _).
  destruct (FHL _ _ _ _ _ AH3) as [FAB FABD].
  assert (BSF : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 8 <= 17594333495296)
    by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  assert (LBH' : ablkLB (FB0 FF :: LB)) by (apply ablkLB_cons; [exact FH| exact LBH]).
  assert (ASH' : ashort (FB0 FF :: LB) HUF_RSTATS_DEPTH) by (apply ashort_push; [exact ASH| lia]).
  assert (ART3 : art m3) by (apply artcells_art; exact (AI_rtcells AI _ _ _ _ _ AH3)).
  assert (AFP : afpre AI rng_fs L RNG st (FB0 FF :: LB) m3 lo (SPA1 SPV - 16) HUF_RSTATS_DEPTH).
  { unfold afpre, astk. split; [exact AH3|]. split; [exact ASH'|]. split; [exact ART3|].
    split; [split; [exact KLO| split; [eapply rng_sub'; [exact RSTK| lia]| exact RI]]|].
    split; [exact RFS|]. split; [exact BOT|]. split; [lia|]. split; [clear - SPA32; Z.div_mod_to_equations; lia|]. split; [exact RSTK| exact LBH']. }
  (* [comment removed for export] *)
  assert (AZS3 : azstk RNG m3 lo (SPA1 SPV - 16)).
  { pose proof (ablk_lin _ _ FAB) as (FA1 & FA2 & FA3 & FA4).
    eapply azstk_transport_F; [eapply azstk_sub; [exact AZS| lia| lia| lia]| exact MU03| exact WM03| | exact FAB| unfold al_fake; Z.div_mod_to_equations; lia| | lia].
    - unfold aappW. apply Forall_cons; [cbn [fst snd]; unfold KLS, KLOW, KHIGH in *; lia| apply Forall_nil].
    - clear - FA3 BOT; lia. }
  assert (ARO3 : aro_client RNG m3).
  { eapply aro_client_transport_F; [exact ARO| exact MU03| exact WM03| | exact FAB].
    constructor; [cbn; right; unfold KHIGH in *; lia| constructor]. }
  (* [comment removed for export] *)
  destruct (x1sh_unp m3 FF SHF3 F64 ltac:(lia) ltac:(lia)) as [UTL UNB].
  unfold X1FFHDR in FFC3.
  pose proof (proj1 (rd_rw_cells_appA bsegs m3 FF [C8 (Z_to_bv 64 X1_MAGIC_LIVE); C8 (Z_to_bv 64 X1_DESC); C8 (Z_to_bv 64 0x96138); CB 8 j3] _) FFC3) as [FH0 FH1].
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FH1.
  pose proof (proj1 (rd_rw_cells_appA bsegs m3 _ [C4 (Z_to_bv 64 0)] _) FH1) as [FTL FH2]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FH2.
  pose proof (proj1 (rd_rw_cells_appA bsegs m3 _ [CB 12 j5] _) FH2) as [FH3 FH4]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FH4.
  pose proof (proj1 (rd_rw_cells_appA bsegs m3 _ [C4 (Z_to_bv 64 0)] _) FH4) as [FNB FH5]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FH5.
  replace (FF + 32 + 4 + 12) with (FF + 48) in FNB, FH5 by lia. replace (FF + 48 + 4) with (FF + 52) in FH5 by lia.
  apply stk_of_rw_cells in FTL. apply stk_of_rw_cells in FNB. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FTL, FNB.
  match type of FNB with stk _ _ ?l ?h => replace l with (FF + 48) in FNB by lia; replace h with (FF + 48 + 4) in FNB by lia end.
  match type of FTL with stk _ _ ?l ?h => replace h with (FF + 32 + 4) in FTL by lia end.
  (* [comment removed for export] *)
  apply stk_of_rw_cells in WC3. cbn [cells_size csize Nat.add] in WC3. rewrite Nat.add_0_r, Z2Nat.id in WC3 by lia.
  destruct (stk_split bsegs _ WK (WK + 52) (WK + wksz) WC3 ltac:(lia)) as [SRS W1].
  destruct (stk_split bsegs _ (WK + 52) (WK + 104) (WK + wksz) W1 ltac:(lia)) as [SG1 W2].
  destruct (stk_split bsegs _ (WK + 104) (WK + 980) (WK + wksz) W2 ltac:(lia)) as [SWK W3].
  destruct (stk_split bsegs _ (WK + 980) (WK + 1236) (WK + wksz) W3 ltac:(lia)) as [SG2 W4].
  destruct (stk_split bsegs _ (WK + 1236) (WK + 1492) (WK + wksz) W4 ltac:(lia)) as [SHW SG3]. clear W1 W2 W3 W4.
  (* [comment removed for export] *)
  pose proof (proj1 (rd_rw_cells_appA bsegs m3 _ [C8 (Z_to_bv 64 876)] [C8 flags]) ARG3) as [ARGA _].
  destruct ARGA as [[_ ARGB] _]. cbn [cells_bytes cbytes app] in ARGB. rewrite app_nil_r in ARGB.
  assert (INCONS : forall X k, ainblk LB X k -> ainblk (FB0 FF :: LB) X k)
    by (intros X k (b & Hb & H1 & H2); exists b; split; [right; exact Hb| split; [exact H1| exact H2]]).
  pose proof (fk_inblk_apart AI _ _ _ _ _ _ _ _ WK wksz AH3 INW ltac:(lia)) as DFW.
  assert (DFS : 0 < n -> FF + 64 <= SRC \/ SRC + n <= FF).
  { intros NP. destruct (INS NP) as [IB|[IM1 IM2]]; [| unfold AIMG_HI in IM2; lia].
    pose proof (fk_inblk_apart AI _ _ _ _ _ _ _ _ SRC n AH3 IB ltac:(lia)). lia. }
  eapply evtF_cut.
  { eapply (RS L RNG st (FB0 FF :: LB)) with (lo := lo) (B := WK) (bsz := wksz) (wksz := 876) (src := src);
    first [ exact AFP | exact AZS3 | exact TP | exact ARO3 | exact MI3 | exact STL3 | exact ARGB | exact SB3 | exact LSB
          | exact SHW | exact SRS | exact FNB | exact FTL
          | replace (WK + 1236 + 256) with (WK + 1492) by lia; exact SHW | replace (FF + 48 + 4) with (FF + 52) by lia; exact FNB
          | replace (WK + 104 + 876) with (WK + 980) by lia; exact SWK
          | intros _; split; [exact ABW| split; [exact UW3| split; [exact RW| exact RSW]]]
          | eapply fk_ahull_pres; [exact WM03| exact HWK]
          | apply INCONS; exact INW
          | split; [exact UNB| split; [eapply rng_sub'; [exact RFF| lia]| eapply rng_sub'; [exact RSFF| unfold shspan; rewrite !shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia]]]
          | split; [exact UTL| split; [eapply rng_sub'; [exact RFF| lia]| eapply rng_sub'; [exact RSFF| unfold shspan; rewrite !shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia]]]
          | exists (FB0 FF); split; [left; reflexivity| cbn; lia]
          | intros NP; destruct (ASRC NP) as (A1 & A2 & A3); split; [exact A1| split; [exact (US3 NP)| split; [exact A2| exact A3]]]
          | intros NP; destruct (INS NP) as [IB|IMG]; [left; apply INCONS; exact IB| right; exact IMG]
          | intros NP; eapply fk_ahull_pres; [exact WM03| exact (HSRC NP)]
          | unfold KHIGH in *; lia
          | clear - WK4; Z.div_mod_to_equations; lia
          | clear - F64 FHa FHb FHc; Z.div_mod_to_equations; lia
          | lazymatch goal with |- ?G => idtac "LEFT:" G end ]. }
  all: cbv beta.
  intros ms' PO.
  destruct PO as (w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & m5 & r & -> & MU5 & WM5 & MI5 & ST5 & FFR5 & AH5 & SWK5 & Hr & RES).
  rd_retlit.
  (* [comment removed for export] *)
  assert (BLO : forall b, In b LB -> ab_addr b + ab_size b <= lo).
  { intros b Hb. pose proof (ablk_lin _ _ (LBH b Hb)) as (_ & _ & L3 & _). lia. }
  set (W5 := [(WK + 1236, WK + 1236 + 256); (WK, WK + 52); (FF + 48, FF + 48 + 4); (FF + 32, FF + 32 + 4); (WK + 104, WK + 104 + 876);
              (SPA1 SPV - 16 - HUF_RSTATS_STACK_A, SPA1 SPV - 16)]) in MU5.
  set (W5f := [(WK + 1236, WK + 1236 + 256); (WK, WK + 52); (FF + 48, FF + 48 + 4); (FF + 32, FF + 32 + 4); (WK + 104, WK + 104 + 876)]) in FFR5.
  assert (FFR5' : ffr_pres W5 (FB0 FF :: LB) m3 m5).
  { eapply magree_mono; [exact FFR5|]. intros a [[HF HO]|HS]; [| right; exact HS]. left; split; [exact HF|].
    subst W5 W5f; cbn [outside app] in HO |- *. destruct HO as (O1 & O2 & O3 & O4 & O5 & _). exact (conj O1 (conj O2 (conj O3 (conj O4 (conj O5 I))))). }
  assert (AW5 : aappW W5).
  { subst W5. unfold aappW. pose proof (ablk_disj_band _ _ ABW) as DBW. pose proof (ablk_disj_band _ _ FH) as DBF. unfold KLS, KLOW, KHIGH in *.
    repeat (apply Forall_cons; [cbn [fst snd]; clear - DBW DBF WKH WR KLO LO SPAB FHa FHb FHc; unfold KHIGH in *; lia|]). apply Forall_nil. }
  (* [comment removed for export] *)
  assert (DSTK : forall X k, SPA1 SPV - 16 <= X -> X + k <= SPV -> 0 <= k -> disjoint_from (W5 ++ fake_area L) X k).
  { intros X k H1 H2 Hk. subst W5. pose proof (ablk_lin _ _ FAB) as (FA1 & FA2 & FA3 & FA4). unfold AIMG_HI in FA1.
    cbn [disjoint_from app fake_area]. rewrite !shad_div. unfold FAKESZ, ASHOFF in *.
    clear - H1 H2 Hk SWS SPAB FHa FHb FHc FC BOT FA1 FA3 LO WR WKH ATR. repeat split; Z.div_mod_to_equations; lia. }
  pose proof (rw_cells_transport _ _ _ _ _ _ FRB3 MU5 WM5 ltac:(apply DSTK; cbn; lia)) as FRB5.
  pose proof (rw_cells_transport _ _ _ _ _ _ FRA3 MU5 WM5 ltac:(apply DSTK; cbn; lia)) as FRA5.
  pose proof (rw_cells_transport _ _ _ _ _ _ ARG3 MU5 WM5 ltac:(apply DSTK; cbn; lia)) as ARG5.
  pose proof (stk_transport_disjoint _ _ _ _ _ _ STG3 MU5 WM5 ltac:(apply DSTK; lia)) as STG5.
  apply stk_of_rw_cells in ARG5. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in ARG5.
  match type of ARG5 with stk _ _ _ ?h => replace h with (SPA1 SPV) in ARG5 by lia end.
  pose proof (stk_merge bsegs m5 lo (SPA1 SPV - 16) (SPA1 SPV) ST5 ARG5 ltac:(lia)) as STL5.
  (* [comment removed for export] *)
  assert (PFF : forall a, FF <= a < FF + 64 -> ~ (FF + 32 <= a < FF + 36) -> ~ (FF + 48 <= a < FF + 52) ->
            (in_fake (FB0 FF :: LB) a /\ outside W5f a) \/ (exists a', in_fake (FB0 FF :: LB) a' /\ a = shad a')).
  { intros a Ha N1 N2. left. split; [exists 0, FF, 64; split; [left; reflexivity| lia]|].
    subst W5f. cbn [outside]. pose proof (ablk_disj_band _ _ FH) as DBF. unfold KLS in DBF. clear - Ha N1 N2 DFW WKH WR FC BOT SPAB LO. repeat split; lia. }
  assert (PSH : forall a, Z.shiftr FF 3 + 2147450880 <= a < Z.shiftr FF 3 + 2147450880 + 8 ->
            (in_fake (FB0 FF :: LB) a /\ outside W5f a) \/ (exists a', in_fake (FB0 FF :: LB) a' /\ a = shad a')).
  { intros a Ha. right. exists (8 * (a - 2147450880)). split; [exists 0, FF, 64; split; [left; reflexivity| rewrite Z.shiftr_div_pow2 in Ha by lia; Z.div_mod_to_equations; lia]|].
    rewrite shad_div. unfold ASHOFF. rewrite Z.shiftr_div_pow2 in Ha by lia. Z.div_mod_to_equations. lia. }
  pose proof (rw_cells_magree _ _ _ _ _ _ FFR5 FH0 ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; intros a Ha; apply PFF; lia)) as FH0'.
  pose proof (rw_cells_magree _ _ _ _ _ _ FFR5 FH3 ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; intros a Ha; apply PFF; lia)) as FH3'.
  pose proof (rw_cells_magree _ _ _ _ _ _ FFR5 FH5 ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; intros a Ha; apply PFF; lia)) as FH5'.
  pose proof (rw_cells_magree _ _ _ _ _ _ FFR5 SHF3 ltac:(unfold X1SH; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; intros a Ha; apply PSH; lia)) as SHF5.
  (* [comment removed for export] *)
  pose proof (fk_inblk_apart AI _ _ _ _ _ _ _ _ DT HUF_DTABLE_BYTES AH3 IND ltac:(unfold HUF_DTABLE_BYTES; lia)) as DFD.
  assert (DDT : disjoint_from W5 DT (zlen dtb)).
  { subst W5. rewrite LTB. cbn [disjoint_from]. unfold HUF_DTABLE_BYTES in *. clear - DTWK DFD SDS SPAB WKH WR LO. repeat split; try exact I; lia. }
  pose proof (fcall_u8arr_pres AI FHL _ _ _ _ _ _ _ _ _ _ AH3 ltac:(apply INCONS; rewrite LTB; exact IND) DDT MU5 WM5 FFR5' TB3) as TB5.
  pose proof (fcall_unp_pres AI FHL _ _ _ _ _ _ _ _ _ _ AH3 ltac:(apply INCONS; exact IND) ltac:(unfold HUF_DTABLE_BYTES; lia) ltac:(unfold KEND; lia) AW5 MU5 FFR5' UD3) as UD5.
  pose proof (fcall_unp_pres AI FHL _ _ _ _ _ _ _ _ _ _ AH3 ltac:(apply INCONS; exact INW) ltac:(lia) ltac:(unfold KEND; lia) AW5 MU5 FFR5' UW3) as UW5.
  assert (WSUB : forall a k, WK <= a -> a + k <= WK + wksz -> 0 <= k -> ainblk (FB0 FF :: LB) a k).
  { intros a k H1 H2 Hk. destruct INW as (b & Hb & B1 & B2). exists b. split; [right; exact Hb| lia]. }
  pose proof (fcall_stk_pres AI FHL L RNG st (FB0 FF :: LB) m3 m3 m5 W5 (WK + 52) (WK + 104) AH3 ltac:(apply WSUB; lia) ltac:(subst W5; cbn [disjoint_from]; clear - DFW WKH WR SPAB SWS LO; repeat split; try exact I; lia) MU5 WM5 FFR5' SG1) as SG1'.
  pose proof (fcall_stk_pres AI FHL L RNG st (FB0 FF :: LB) m3 m3 m5 W5 (WK + 980) (WK + 1236) AH3 ltac:(apply WSUB; lia) ltac:(subst W5; cbn [disjoint_from]; clear - DFW WKH WR SPAB SWS LO; repeat split; try exact I; lia) MU5 WM5 FFR5' SG2) as SG2'.
  pose proof (fcall_stk_pres AI FHL L RNG st (FB0 FF :: LB) m3 m3 m5 W5 (WK + 1492) (WK + wksz) AH3 ltac:(apply WSUB; lia) ltac:(subst W5; cbn [disjoint_from]; clear - DFW WKH WR SPAB SWS LO; repeat split; try exact I; lia) MU5 WM5 FFR5' SG3) as SG3'.
  (* [comment removed for export] *)
  assert (MU05 : munch ([(WK, WK + wksz); (SPV - 5520, SPV)] ++ fake_area L) m m5).
  { eapply munch_trans; [eapply munch_weaken; [| exact MU03]; intros x Hx; cbn [outside app fake_area] in *; clear - Hx; lia|].
    eapply munch_weaken; [| exact MU5]. intros x Hx. subst W5. cbn [outside app fake_area] in *. unfold FAKESZ in *.
    clear - Hx FFA1 FFA2 SPAB WR. lia. }
  assert (WM05 : wmono bsegs m m5) by (eapply wmono_trans; [exact WM03| exact WM5]).
  assert (FFR05 : ffr_pres [(WK, WK + wksz)] LB m m5).
  { eapply ffr_pres_trans; [apply ffr_pres_mono_nil1; exact FFR03|].
    eapply magree_mono; [exact FFR5|]. intros a [[(c & A & k & Hb & Ha) HO]|(a' & (c & A & k & Hb & Ha) & ->)].
    - left. split; [exists c, A, k; split; [right; exact Hb| exact Ha]|].
      pose proof (FFD _ Hb) as D1. pose proof (BLO _ Hb) as D2. cbn [ab_addr ab_size] in D1, D2.
      subst W5f. cbn [outside] in *. clear - HO D1 D2 Ha SPAB WR. repeat split; try exact I; lia.
    - right. exists a'. split; [exists c, A, k; split; [right; exact Hb| exact Ha]| reflexivity]. }
  (* [comment removed for export] *)
  zstep. zstep. replace (Z_to_bv 64 (-120)) with (Z_to_bv 64 18446744073709551496) by (apply Z_to_bv_eqm; reflexivity).
  zstep. bcase KI.
  - (* [comment removed for export] *)
    zstep. zstep.
    assert (ERR : zd_is_error r = true) by (unfold zd_is_error, ZE_maxCode; apply Z.ltb_lt; rewrite ?unsigned_lit in KI by lia; lia).
    destruct RES as [(NE & _)|(_ & SHW5 & SRS5 & SNB5 & STL5')]; [rewrite ERR in NE; discriminate|].
    replace (SPA1 SPV - 16 + 16) with (SPA1 SPV) by lia.
    apply evtF_done. eapply KERR; try eassumption.
    + eapply munch_weaken; [| exact MU05]. intros x Hx. cbn [outside app fake_area] in *. clear - Hx. lia.
    + intros a Ha HP. apply (FFR05 a Ha). destruct HP as [[HF HO]|HS]; [left; split; [exact HF|]| right; exact HS].
      cbn [outside] in *. clear - HO. lia.
    + exact (proj1 (proj1 (rd_rw_cells_appA bsegs m5 FF [C8 (Z_to_bv 64 X1_MAGIC_LIVE)] _) FH0')).
    + pose proof (proj2 (proj1 (rd_rw_cells_appA bsegs m5 _ [CB 4 j6] _) FH5')) as G4. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in G4.
      match type of G4 with rw_cells _ _ ?a _ => replace a with (FF + 56) in G4 by lia end. exact G4.
    + unfold X1FRA in FRA5. pose proof (proj2 (proj1 (rd_rw_cells_appA bsegs m5 _ [CB 80 jA] _) FRA5)) as G5. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in G5.
      exact (proj1 (proj1 (rd_rw_cells_appA bsegs m5 _ [C8 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF)] _) G5)).
    + unfold X1FRA in FRA5. pose proof (proj1 (proj1 (rd_rw_cells_appA bsegs m5 _ [CB 80 jA] _) FRA5)) as G6. apply stk_of_rw_cells in G6.
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in G6.
      match type of G6 with stk _ _ _ ?h => replace h with (SPA1 SPV + 80) in G6 by lia end.
      exact (stk_merge bsegs m5 lo (SPA1 SPV) (SPA1 SPV + 80) STL5 G6 ltac:(lia)).
    + unfold X1FRA in FRA5.
      pose proof (proj2 (proj1 (rd_rw_cells_appA bsegs m5 _ [CB 80 jA; C8 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF)] _) FRA5)) as G7.
      apply stk_of_rw_cells in G7. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in G7.
      match type of G7 with stk _ _ ?a _ => replace a with (SPA1 SPV + 104) in G7 by lia end.
      match type of G7 with stk _ _ _ ?h => replace h with (SPA1 SPV + 312) in G7 by lia end.
      exact (stk_merge bsegs m5 (SPA1 SPV + 104) (SPA1 SPV + 312) (SPV + -104) G7 STG5 ltac:(lia)).
    + match type of SHW5 with stk _ _ _ ?h => replace h with (WK + 1492) in SHW5 by lia end.
      pose proof (stk_merge bsegs m5 WK (WK + 52) (WK + 104) SRS5 SG1' ltac:(lia)) as M1.
      match type of SWK5 with stk _ _ _ ?h => replace h with (WK + 980) in SWK5 by lia end.
      pose proof (stk_merge bsegs m5 WK (WK + 104) (WK + 980) M1 SWK5 ltac:(lia)) as M2.
      pose proof (stk_merge bsegs m5 WK (WK + 980) (WK + 1236) M2 SG2' ltac:(lia)) as M3.
      pose proof (stk_merge bsegs m5 WK (WK + 1236) (WK + 1492) M3 SHW5 ltac:(lia)) as M4.
      exact (stk_merge bsegs m5 WK (WK + 1492) (WK + wksz) M4 SG3' ltac:(lia)).
  - (* [comment removed for export] *)
    assert (NER : zd_is_error r = false) by (unfold zd_is_error, ZE_maxCode; apply Z.ltb_ge; rewrite ?unsigned_lit in KI by lia; lia).
    destruct RES as [(_ & RR & hw & rank & tl & nbs & HW5 & LHW & BHW & RK5 & CNB & CTL & STATS & NBSR)|(EE & _)]; [| rewrite NER in EE; discriminate].
    replace (SPA1 SPV - 16 + 16) with (SPA1 SPV) by lia.
    clear MU5. unfold X1SH in SHF5.
    pose proof STATS as (T1 & T2 & T3 & T4 & T5 & T6).
    assert (LRK : Z.of_nat (length (map (Z_to_bv 64) rank)) = 13) by (rewrite length_map; unfold FseNCount.Zlength in T4; lia).
    assert (LHW' : Z.of_nat (length (map (Z_to_bv 8) hw)) = 256) by (rewrite length_map; exact LHW).
    pose proof (munch_refl [(SPV - 5520, SPV)] m5) as MUS.
    pose proof (wmono_refl bsegs m5) as WMS.
    (* [comment removed for export] *)
    clear SSS WSRC DTWK DFD DFW DFS INS HSRC ASRC SB3 US3 UD3 UW3 TB3 WC3 ST5 ARG5 FFR5 FFR5' PFF PSH DDT WSUB AW5 DSTK INCONS.
    assert (LTB' : Z.of_nat (length dtb) = HUF_DTABLE_BYTES) by exact LTB.
    assert (KHI : 17594333495296 <= lo) by (unfold KHIGH in KLO; lia).
    unfold X1FRA in FRA5. lazymatch type of MU05 with ?T => change T with (bx T) in MU05 end.
    zstep.                                        (* [comment removed for export] *)
    lazymatch type of MUS with munch _ _ ?mm => rename mm into m6 end.
    unfold bx in MU05.
    assert (AH6 : AHEAP AI L RNG st (FB0 FF :: LB) m6).
    { eapply (AI_frame AI); [exact AH5| exact MUS| exact WMS|]. constructor; [| constructor]. left; left. cbn. lia. }
    assert (MU06 : munch ([(WK, WK + wksz); (SPV - 5520, SPV)] ++ fake_area L) m m6).
    { eapply munch_trans; [exact MU05|]. eapply munch_weaken; [| exact MUS]. intros x Hx. cbn [outside app fake_area] in Hx |- *. tauto. }
    assert (FFR06 : ffr_pres [(WK, WK + wksz)] LB m m6).
    { eapply ffr_pres_trans; [exact FFR05|]. eapply magree_mono; [eapply magree_of_munch; [exact MUS| exact WMS]|].
      intros a [[(c & A & k & Hb & Ha) _]|(a' & (c & A & k & Hb & Ha) & ->)]; pose proof (BLO _ Hb) as HL; cbn [ab_addr ab_size outside] in HL |- *.
      - clear - Ha HL LO. split; [lia| exact I].
      - rewrite shad_div. unfold ASHOFF. clear - Ha HL LO KHI. split; [| exact I]. Z.div_mod_to_equations. lia. }
    assert (UD6 : unpoisoned m6 DT (DT + HUF_DTABLE_BYTES)).
    { eapply unpoisoned_munch; [exact UD5| exact MUS|]. cbn [disjoint_from]. rewrite !shad_div.
      clear - DHI KHI LO. unfold ASHOFF, HUF_DTABLE_BYTES in *. split; [| exact I]. left. Z.div_mod_to_equations. lia. }
    assert (UW6 : unpoisoned m6 WK (WK + wksz)).
    { eapply unpoisoned_munch; [exact UW5| exact MUS|]. cbn [disjoint_from]. rewrite !shad_div.
      clear - WKH WR KHI LO. unfold ASHOFF. split; [| exact I]. left. Z.div_mod_to_equations. lia. }
    assert (F56 : rw_cells bsegs m6 (SPA1 SPV + 56) [C8 (Z_to_bv 64 r)]).
    { lazymatch type of FRA5 with rw_cells _ _ _ (?c0 :: ?rest) =>
        pose proof (proj2 (proj1 (rd_rw_cells_appA bsegs m6 _ [c0] rest) FRA5)) as G8 end.
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in G8.
      exact (proj1 (proj1 (rd_rw_cells_appA bsegs m6 _ [C8 (Z_to_bv 64 r)] _) G8)). }
    lazymatch type of FRA5 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?rest) =>
      pose proof (rw_cells_merge bsegs m6 (SPA1 SPV) [] [c0; c1; c2] rest FRA5) as FRA6 end.
    cbn [cells_size csize Nat.add app] in FRA6.
    lazymatch type of FRA6 with rw_cells _ _ _ (CB 80 ?jj :: _) =>
      assert (FRA7 : rw_cells bsegs m6 (SPA1 SPV) (X1FRA FF DT WK jj jC jD jB jE)) by (unfold X1FRA; exact FRA6) end.
    apply evtF_done. eapply KOK; try eassumption.
    + unfold X1FFHDR. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in FH3', FH5'.
      apply (proj2 (rd_rw_cells_appA bsegs m6 FF [C8 (Z_to_bv 64 X1_MAGIC_LIVE); C8 (Z_to_bv 64 X1_DESC); C8 (Z_to_bv 64 0x96138); CB 8 j3] _)).
      split; [exact FH0'|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add].
      apply (proj2 (rd_rw_cells_appA bsegs m6 _ [C4 (Z_to_bv 64 tl)] _)). split; [exact CTL|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add].
      apply (proj2 (rd_rw_cells_appA bsegs m6 _ [CB 12 j5] _)). split; [exact FH3'|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add].
      apply (proj2 (rd_rw_cells_appA bsegs m6 _ [C4 (Z_to_bv 64 nbs)] _)).
      split; [lazymatch type of CNB with rw_cells _ _ ?a _ => lazymatch goal with |- rw_cells _ _ ?b _ => replace b with a by lia end end; exact CNB|].
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add].
      first [ exact FH5' | lazymatch type of FH5' with rw_cells _ _ ?a _ => lazymatch goal with |- rw_cells _ _ ?b _ => replace b with a by lia end end; exact FH5' ].
    + match type of SWK5 with stk _ _ _ ?h => replace h with (WK + 980) in SWK5 by lia end.
      exact (stk_merge bsegs m6 (WK + 52) (WK + 980) (WK + 1236) (stk_merge bsegs m6 (WK + 52) (WK + 104) (WK + 980) SG1' SWK5 ltac:(lia)) SG2' ltac:(lia)).
Qed.
End Asm.
End CANSEC1.
