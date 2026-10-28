(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree FseWalkKit FseRdKit FseRdKit2 ZdWalkKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AProto AMalloc_iface AProg_kit AFake_iface AFakeK_iface
     AZ_kit AZ_globals AZ_globalsR AZ_fkit AZ_huf_iface AZ_hft_iface AF_fse_rd_base AF_fse_rd_mem AF_fse_rd_seg AF_fse_rd_asm
     AZ_hft_fdec_epi AZ_hft_fdec_pro.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKitF.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.

Section CANSEC1. Context {rc : runConstT}.
Notation FB0 F := (mkABlock (ABFake 0) F 64).
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma fd_bytes_at_nil1 : forall (m m' : amem) A, bytes_at bsegs m A [] -> bytes_at bsegs m' A [].
Proof. intros m m' A (H0 & H1 & _). split; [exact H0|]. split; [exact H1|]. intros i Hi. cbn [length] in Hi. lia. Qed.

(* [comment removed for export] *)
Section FC.
Variable AI : AMallocIface.
Hypothesis FHL : fake_heap_law AI.

Lemma fd_disjoint_from_sub1 : forall W a n a' n', disjoint_from W a n -> a <= a' -> a' + n' <= a + n -> disjoint_from W a' n'.
Proof.
  induction W as [|[x y] W IH]; intros a n a' n' D H1 H2; cbn [disjoint_from] in *; [exact I|].
  destruct D as [D1 D2]. split; [lia| eapply IH; [exact D2| lia| lia]].
Qed.

Lemma fd_fcall_bytes_pres : forall L RNG st LB m0 (m m' : amem) W X bs,
  AHEAP AI L RNG st LB m0 -> ainblk LB X (zlen bs) -> disjoint_from W X (zlen bs) ->
  munch (W ++ fake_area L) m m' -> ffr_pres W LB m m' -> bytes_at bsegs m X bs -> bytes_at bsegs m' X bs.
Proof.
  intros L RNG st LB m0 m m' W X bs AH (b & Hb & H1 & H2) DJ MU FP B.
  destruct b as [[p|c] A n]; cbn [ab_addr ab_size] in H1, H2.
  - destruct (fake_area_block AI _ _ _ _ _ p A n FHL AH Hb) as [DF _].
    eapply bytes_at_transport; [exact B| exact MU|]. apply disjoint_from_app2; [exact DJ| eapply fd_disjoint_from_sub1; [exact DF| lia| lia]].
  - eapply bytes_at_magree; [exact FP| exact B|]. intros a Ha. left. split.
    + exists c, A, n. split; [exact Hb| lia].
    + eapply disjoint_outside; [exact DJ| lia].
Qed.

Lemma fd_fcall_cells_pres : forall L RNG st LB m0 (m m' : amem) W X cs,
  AHEAP AI L RNG st LB m0 -> ainblk LB X (Z.of_nat (cells_size cs)) -> disjoint_from W X (Z.of_nat (cells_size cs)) ->
  munch (W ++ fake_area L) m m' -> wmono bsegs m m' -> ffr_pres W LB m m' -> rw_cells bsegs m X cs -> rw_cells bsegs m' X cs.
Proof.
  intros L RNG st LB m0 m m' W X cs AH IB DJ MU WM FP [[Hwf HB] HW]. split; [split; [exact Hwf|]|].
  - eapply fd_fcall_bytes_pres; [exact AH| rewrite cells_bytes_length by assumption; exact IB| rewrite cells_bytes_length by assumption; exact DJ| exact MU| exact FP| exact HB].
  - eapply wr_at_transport; [exact HW| exact WM].
Qed.

Lemma fd_fcall_u8arr_pres : forall L RNG st LB m0 (m m' : amem) W X bs,
  AHEAP AI L RNG st LB m0 -> ainblk LB X (zlen bs) -> disjoint_from W X (zlen bs) ->
  munch (W ++ fake_area L) m m' -> wmono bsegs m m' -> ffr_pres W LB m m' -> u8arr bsegs m X bs -> u8arr bsegs m' X bs.
Proof.
  intros L RNG st LB m0 m m' W X bs AH IB DJ MU WM FP [HB HW]. split.
  - eapply fd_fcall_bytes_pres; [exact AH| exact IB| exact DJ| exact MU| exact FP| exact HB].
  - eapply wr_at_transport; [exact HW| exact WM].
Qed.

Lemma fd_fcall_stk_pres : forall L RNG st LB m0 (m m' : amem) W lo hi,
  AHEAP AI L RNG st LB m0 -> ainblk LB lo (hi - lo) -> disjoint_from W lo (hi - lo) ->
  munch (W ++ fake_area L) m m' -> wmono bsegs m m' -> ffr_pres W LB m m' -> stk bsegs m lo hi -> stk bsegs m' lo hi.
Proof.
  intros L RNG st LB m0 m m' W lo hi AH (b & Hb & H1 & H2) DJ MU WM FP ST.
  destruct b as [[p|c] A n]; cbn [ab_addr ab_size] in H1, H2.
  - destruct (fake_area_block AI _ _ _ _ _ p A n FHL AH Hb) as [DF _].
    eapply stk_transport_disjoint; [exact ST| exact MU| exact WM|]. apply disjoint_from_app2; [exact DJ| eapply fd_disjoint_from_sub1; [exact DF| lia| lia]].
  - eapply stk_magree; [exact FP| exact ST|]. intros a Ha. left. split.
    + exists c, A, n. split; [exact Hb| lia].
    + eapply disjoint_outside; [exact DJ| lia].
Qed.

(* [comment removed for export] *)
Lemma fd_fcall_unp_pres : forall L RNG st LB m0 (m m' : amem) W X k,
  AHEAP AI L RNG st LB m0 -> ainblk LB X k -> 0 < k -> X + k <= KEND -> aappW W ->
  munch (W ++ fake_area L) m m' -> ffr_pres W LB m m' -> unpoisoned m X (X + k) -> unpoisoned m' X (X + k).
Proof.
  intros L RNG st LB m0 m m' W X k AH (b & Hb & H1 & H2) Hk XH HW MU FP U.
  pose proof U as (U0 & U1 & _).
  destruct b as [[p|c] A n]; cbn [ab_addr ab_size] in H1, H2.
  - destruct (fake_area_block AI _ _ _ _ _ p A n FHL AH Hb) as [_ DSF].
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH Hb) as (N & (BR & _) & _). pose proof (ablk_lin _ _ BR) as (L1 & L2 & L3 & L4).
    eapply unpoisoned_munch; [exact U| exact MU|]. apply disjoint_from_app2.
    + apply aappW_shadow_disjoint; [exact HW| | | |]; rewrite ?shad_div; unfold ASHOFF, KEND in *; Z.div_mod_to_equations; lia.
    + eapply fd_disjoint_from_sub1; [exact DSF| |]; unfold shspan; rewrite ?shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia.
  - eapply unpoisoned_agree; [exact U|]. intros s Hs.
    set (a' := Z.max X (8 * (s - ASHOFF))).
    assert (Ra : X <= a' < X + k).
    { subst a'. rewrite !shad_div in Hs. unfold ASHOFF in *. destruct (Z.max_spec X (8 * (s - 2147450880))) as [[Hm ->]|[Hm ->]]; Z.div_mod_to_equations; lia. }
    assert (Ea : shad a' = s).
    { subst a'. rewrite !shad_div in Hs. rewrite shad_div. unfold ASHOFF in *. destruct (Z.max_spec X (8 * (s - 2147450880))) as [[Hm ->]|[Hm ->]]; Z.div_mod_to_equations; lia. }
    destruct (FP s ltac:(rewrite !shad_div in Hs; unfold ASHOFF in Hs; unfold KEND in XH; Z.div_mod_to_equations; lia)
                 ltac:(right; exists a'; split; [exists c, A, n; split; [exact Hb| lia]| symmetry; exact Ea])) as [E _].
    exact E.
Qed.
End FC.


(* [comment removed for export] *)
Definition FSPB (SPV : Z) : Z := (SPV + -224) - (SPV + -224) mod 2^5.
Lemma fspb_props : forall SPV, SPV mod 16 = 0 -> SPV - 240 <= FSPB SPV <= SPV - 224 /\ FSPB SPV mod 32 = 0.
Proof. intros SPV H. unfold FSPB. change (2^5) with 32. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Lemma fd_stk_pres : forall AI LB SP (m m' : amem) lo hi,
  aheap_pres (aci AI) LB SP m m' -> ainblk LB lo (hi - lo) -> stk bsegs m lo hi -> stk bsegs m' lo hi.
Proof.
  intros AI LB SP m m' lo hi HP (b & Hb & H1 & H2) (A0 & A1 & HW). split; [exact A0|]. split; [exact A1|].
  intros i Hi. destruct (HP i ltac:(clear - Hi A0 A1; lia) ltac:(right; right; left; exists b; split; [exact Hb| clear - Hi H1 H2; lia])) as [E W].
  destruct (HW i Hi) as [W0 [bb Hbb]]. split; [apply W, W0|]. exists bb. unfold mrd in *. rewrite E. exact Hbb.
Qed.

Lemma fd_got_cells : forall m, (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) ->
  rw_cells bsegs m AGOT_SUAR_D [C8 (Z_to_bv 64 0xcfd00)] /\ rw_cells bsegs m AGOT_FDPC [C8 (Z_to_bv 64 0xabea0)].
Proof.
  intros m R. unfold AGOT_SUAR_D, AGOT_FDPC. split;
    (apply relro_wordA; [exact R| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity]).
Qed.

Section Asm.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Variable fflag : alayout -> Z -> Z -> Z.
Variable rng_fs : alayout -> footprint -> Prop.
Hypothesis SM0K : forall k, Z.of_nat k < 16384 -> stack_malloc_0k_stmt AI fflag rng_fs k.
Hypothesis FHL : fake_heap_law AI.

(* [comment removed for export] *)
Lemma fd_openZ : forall (k : nat) (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
    (ra gp tp t0 t1 t2 s0 s1 bmi2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem)
    (SPV DST cap SRC n ml WK wksz lo : Z) (src : list byte) (Q : machine_state -> Prop),
  Z.of_nat k < 16384 ->
  AHEAP AI L RNG st LB m -> fake_le 0 k LB -> ablkLB LB ->
  rng_aimg RNG -> rng RNG lo (al_top L - lo) -> rng_fs L RNG ->
  ATOP + 4096 <= lo -> lo <= SPV - 4992 -> SPV + 16 < al_top L -> SPV mod 16 = 0 ->
  stk bsegs m lo SPV -> mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
  0 <= cap <= 65536 -> 0 <= n <= 65536 -> 0 <= ml <= 9 -> 0 <= wksz < 2^32 ->
  (* [comment removed for export] *)
  stk bsegs m DST (DST + cap) -> ainblk LB DST cap -> (0 < cap -> unpoisoned m DST (DST + cap)) -> 4096 <= DST ->
  (DST + cap <= lo \/ SPV <= DST) -> DST + cap < 2^47 ->
  stk bsegs m WK (WK + wksz) -> ainblk LB WK wksz -> (0 < wksz -> unpoisoned m WK (WK + wksz)) -> 4096 <= WK ->
  (WK + wksz <= lo \/ SPV <= WK) -> WK + wksz < 2^47 -> WK mod 4 = 0 ->
  bytes_at bsegs m SRC src -> zlen src = n -> (0 < n -> ainimg LB SRC n) -> (0 < n -> unpoisoned m SRC (SRC + n)) -> 4096 <= SRC ->
  (SRC + n <= lo \/ SPV <= SRC) -> SRC + n < 2^47 ->
  (* [comment removed for export] *)
  (forall (FF : Z) (m3 : amem) (jA' : list byte) (w8 w16 w24 : word) (j32 j48 j64 j80 j24 : list byte) (tlw : word) (j36 j52 : list byte)
          (y1 y5 y6 y7 y10 y11 y12 y13 y14 y16 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
     FF mod 64 = 0 -> ablk FF (FF + 64) -> FF + 64 <= ATOP -> rng RNG FF 64 -> rng RNG (shad FF) 8 ->
     (forall b, In b LB -> FF + 64 <= ab_addr b \/ ab_addr b + ab_size b <= FF) ->
     al_fake L <= FF -> FF + 64 <= al_fake L + FAKESZ ->
     AHEAP AI L RNG st (FB0 FF :: LB) m3 ->
     munch ([(SPV - 4992, SPV)] ++ fake_area L) m m3 -> wmono bsegs m m3 -> ffr_pres [] LB m m3 -> mem_inv bsegs m3 ->
     rw_cells bsegs m3 (SPV + -104) (FDRB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
     rw_cells bsegs m3 (FSPB SPV) (FDFRAME jA' w8 w16 w24 j32 FF j48 j64 j80) ->
     rw_cells bsegs m3 FF (FDHDR FF (fflag L 0 FF) j24 tlw j36 j52) -> rw_cells bsegs m3 (Z.shiftr FF 3 + 2147450880) FDSH ->
     stk bsegs m3 lo (FSPB SPV) -> stk bsegs m3 (FSPB SPV + 120) (SPV + -104) ->
     stk bsegs m3 DST (DST + cap) -> (0 < cap -> unpoisoned m3 DST (DST + cap)) ->
     stk bsegs m3 WK (WK + wksz) -> (0 < wksz -> unpoisoned m3 WK (WK + wksz)) ->
     bytes_at bsegs m3 SRC src -> (0 < n -> unpoisoned m3 SRC (SRC + n)) ->
     wksz < 512 ->
     Q (MS (mkR y1 (Z_to_bv 64 (FSPB SPV)) gp tp y5 y6 y7 (Z_to_bv 64 SPV) (Z_to_bv 64 (FSPB SPV))
              y10 y11 y12 y13 y14 (Z_to_bv 64 18446744073709551615) y16 (Z_to_bv 64 FF)
              (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
           FR (Z_to_bv 64 0xac20c) fc None m3 (seg_rom bsegs))) ->
  (* [comment removed for export] *)
  (forall (FF : Z) (m3 : amem) (jA' : list byte) (j32 j48 j64 j80 j24 : list byte) (tlw : word) (j36 j52 : list byte)
          (y5 y6 y7 y16 y28 y29 y30 y31 : word),
     FF mod 64 = 0 -> ablk FF (FF + 64) -> FF + 64 <= ATOP -> rng RNG FF 64 -> rng RNG (shad FF) 8 ->
     (forall b, In b LB -> FF + 64 <= ab_addr b \/ ab_addr b + ab_size b <= FF) ->
     al_fake L <= FF -> FF + 64 <= al_fake L + FAKESZ ->
     AHEAP AI L RNG st (FB0 FF :: LB) m3 ->
     munch ([(SPV - 4992, SPV)] ++ fake_area L) m m3 -> wmono bsegs m m3 -> ffr_pres [] LB m m3 -> mem_inv bsegs m3 ->
     rw_cells bsegs m3 (SPV + -104) (FDRB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
     rw_cells bsegs m3 (FSPB SPV) (FDFRAME jA' (Z_to_bv 64 DST) (Z_to_bv 64 2147450880) (Z_to_bv 64 FF) j32 FF j48 j64 j80) ->
     rw_cells bsegs m3 FF (FDHDR FF (fflag L 0 FF) j24 tlw j36 j52) -> rw_cells bsegs m3 (Z.shiftr FF 3 + 2147450880) FDSH ->
     stk bsegs m3 lo (FSPB SPV) -> stk bsegs m3 (FSPB SPV + 120) (SPV + -104) ->
     stk bsegs m3 DST (DST + cap) -> (0 < cap -> unpoisoned m3 DST (DST + cap)) ->
     stk bsegs m3 WK (WK + wksz) -> (0 < wksz -> unpoisoned m3 WK (WK + wksz)) ->
     bytes_at bsegs m3 SRC src -> (0 < n -> unpoisoned m3 SRC (SRC + n)) ->
     512 <= wksz ->
     Q (MS (mkR (Z_to_bv 64 0xac008) (Z_to_bv 64 (FSPB SPV)) gp tp y5 y6 y7 (Z_to_bv 64 SPV) (Z_to_bv 64 (FSPB SPV))
              (Z_to_bv 64 WK) (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 SRC) (Z_to_bv 64 n) (Z_to_bv 64 0) y16 (Z_to_bv 64 FF)
              (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 cap) (Z_to_bv 64 ml) (Z_to_bv 64 n) (Z_to_bv 64 SRC)
              (Z_to_bv 64 WK) (Z_to_bv 64 wksz) (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 (FF + 32)) y28 y29 y30 y31)
           FR (Z_to_bv 64 0xaaac0) fc None m3 (seg_rom bsegs))) ->
  evtF bsegs RNG Q
    (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DST) (Z_to_bv 64 cap) (Z_to_bv 64 SRC) (Z_to_bv 64 n)
             (Z_to_bv 64 ml) (Z_to_bv 64 WK) (Z_to_bv 64 wksz) bmi2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 APFSE_DEC) fc None m (seg_rom bsegs)).
Proof.
  intros k L RNG st LB ra gp tp t0 t1 t2 s0 s1 bmi2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m SPV DST cap SRC n ml WK wksz lo src Q
         HK AH FLE LBH RI RSTK RFS BOT LO SPT SP16 ST MI TP CAPR NR MLR WR
         SD IND UD DSTL SDS DHI SW INW UW WKL SWS WHI WKA SB LSB INS US SRCL SSS SHI KEXIT KCALL.
  pose proof atop_range as ATR. unfold APFSE_DEC.
  pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & LY4 & _).
  pose proof (fspb_props SPV SP16) as (SPAB & SPA32). set (SPB := FSPB SPV) in *.
  assert (ESPB : (SPV + -224) - (SPV + -224) mod 2^5 = SPB) by reflexivity.
  pose proof (AI_aci_img AI) as HCI. pose proof (AI_aci_lo AI) as HCI0.
  assert (LOC : ATOP <= lo) by lia.
  assert (SPK : SPV + 16 < KEND) by (unfold KEND; lia).
  (* [comment removed for export] *)
  pose proof (AI_rtcells AI _ _ _ _ _ AH) as RTC. unfold artcells in RTC.
  destruct RTC as (C0 & GOT & RIC & REAL & SHB & SUA & INI & LAY & _).
  destruct (fd_got_cells m (AI_relro AI _ _ _ _ _ AH)) as [GSU _].
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (fd_pro ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV SPB lo);
      first [exact SP16| exact SPK| exact LO| exact LOC| exact ESPB| exact ST| exact MI| exact GOT| exact SHB| exact GSU| exact SUA| eapply rng_sub'; [exact RSTK| lia] | exact RI| lia]. }
  cbv beta. intros ms' (m1 & jA & -> & MU1 & WM1 & MI1 & FRB1 & FRA1 & STL1 & STG1).
  clear C0 GOT RIC REAL SHB SUA INI LAY GSU.
  assert (AH1 : AHEAP AI L RNG st LB m1).
  { eapply (AI_frame AI); [exact AH| exact MU1| exact WM1|]. constructor; [| constructor]. left; left. cbn. lia. }
  (* [comment removed for export] *)
  assert (D1 : forall X n, (X + n <= lo \/ SPV <= X) -> 0 <= n -> disjoint_from [(SPV - 240, SPV)] X n).
  { intros X nn HX Hn. cbn [disjoint_from]. split; [lia| exact I]. }
  assert (DS1 : forall X n, 0 <= X -> 0 <= n -> X + n <= 2^47 ->
             disjoint_from [(SPV - 240, SPV)] (shad X) (shad (X + n - 1) + 1 - shad X)).
  { intros X nn X0 Hn Hb. cbn [disjoint_from]. split; [| exact I]. left. rewrite !shad_div. unfold ASHOFF in *.
    clear - X0 Hn Hb ATR BOT LO. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  eapply evtF_cut.
  { pose proof (SM0K k HK) as SMC. unfold stack_malloc_0k_stmt in SMC. eapply SMC with (lo := lo); clear SMC;
      rewrite ?(unsigned_lit SPB) by lia;
      first [exact AH1| exact FLE| exact MI1| exact STL1| exact TP| reflexivity| exact RSTK| exact RI| exact RFS| lia| unfold SMK_STACK; lia]. }
  cbv beta. intros ms' PO.
  destruct PO as (FF & z5 & z6 & z7 & e11 & e12 & e13 & e14 & e15 & e16 & e17 & z28 & z29 & z30 & z31 & m2 & j0 & j1 & j2 & junk
                  & -> & MI2 & ST2 & HPR2 & AH2 & F64 & FH & FC & FFC2 & SHF2 & RFF & RSFF & MUF2 & WM2 & FFA1 & FFA2).
  rewrite ?(unsigned_lit SPB) in ST2, HPR2, MUF2 by lia.
  rd_retlit.
  pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in FHa.
  pose proof (fk_frame_apart AI _ _ _ _ _ _ _ _ AH2) as FFD.
  pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR2 FRB1 ltac:(left; left; cbn; lia)) as FRB2.
  pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR2 FRA1 ltac:(left; left; cbn; lia)) as FRA2.
  pose proof (aheap_pres_stk _ _ _ _ _ _ _ HPR2 STG1 ltac:(lia) ltac:(lia)) as STG2.
  (* [comment removed for export] *)
  destruct (fd_got_cells m2 (AI_relro AI _ _ _ _ _ AH2)) as [_ GPC2].
  eapply evtF_cut.
  { eapply (fd_hdr gp tp FR fc SPV SPB lo);
      first [exact SP16| exact SPK| exact LO| exact LOC| exact ESPB| exact FRA2| exact FFC2| exact SHF2| exact GPC2| exact MI2| exact FH| exact FC| exact F64
            | exact RFF| exact RSFF| exact RI| exact WKA| eapply rng_sub'; [exact RSTK| lia] | lia]. }
  cbv beta. intros ms' (m3 & jA' & w8 & w16 & w24 & j32 & j48 & j64 & j80 & j24 & tlw & j36 & j52 & MU3 & WM3 & MI3 & FFC3 & SHF3 & ALT).
  assert (BSF : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 8 <= 17594333495296)
    by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
  assert (AH3 : AHEAP AI L RNG st (FB0 FF :: LB) m3).
  { eapply (AI_frame AI); [exact AH2| exact MU3| exact WM3|].
    constructor; [cbn; left; left; lia|].
    constructor; [cbn; right; left; exists (FB0 FF); split; [left; reflexivity| cbn; lia]|].
    constructor; [cbn; right; left; exists (FB0 FF); split; [left; reflexivity| cbn; lia]|].
    constructor; [cbn; right; right; right; right; exists 0, FF, 64; split; [left; reflexivity| rewrite Z.shiftr_div_pow2 by lia;
                  change (2 ^ 3) with 8; unfold ASHOFF; Z.div_mod_to_equations; lia]| constructor]. }
  pose proof (rw_cells_transport _ _ _ _ _ _ FRB2 MU3 WM3 ltac:(cbn; lia)) as FRB3.
  assert (STL3 : stk bsegs m3 lo SPB)
    by (eapply stk_transport; [exact ST2| exact MU3| exact WM3| intros x Hx; left; cbn; lia]).
  assert (STG3 : stk bsegs m3 (SPB + 120) (SPV + -104))
    by (eapply stk_transport; [exact STG2| exact MU3| exact WM3| intros x Hx; left; cbn; lia]).
  (* [comment removed for export] *)
  assert (MU03 : munch ([(SPV - 4992, SPV)] ++ fake_area L) m m3).
  { eapply munch_trans; [eapply munch_weaken; [| exact MU1]; intros x Hx; cbn [outside app fake_area] in *; lia|].
    eapply munch_trans; [eapply munch_weaken; [| exact MUF2]; intros x Hx; cbn [outside app fake_area] in *; unfold SMK_STACK; lia|].
    eapply munch_weaken; [| exact MU3]. intros x Hx. cbn [outside app fake_area] in *.
    rewrite ?shad_div in *. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold FAKESZ, ASHOFF in *.
    clear - Hx FFA1 FFA2 SPAB LO BOT F64. Z.div_mod_to_equations. lia. }
  assert (WM03 : wmono bsegs m m3) by (eapply wmono_trans; [exact WM1| eapply wmono_trans; [exact WM2| exact WM3]]).
  assert (FFR02 : ffr_pres [] LB m m2).
  { eapply ffr_pres_trans; [eapply (fk_ffr_stack AI); [exact AH| exact MU1| exact WM1| constructor; [cbn; lia| constructor]]|].
    eapply (fk_ffr_of_pres AI); exact HPR2. }
  assert (FFR03 : ffr_pres [] LB m m3).
  { eapply (fk_ffr_fin AI L RNG st LB m m2 m3 0 FF 64 (shad FF) 8 [] [(SPB, SPB + 48); (FF, FF + 24); (FF + 48, FF + 52)]);
      [exact AH2| exact LBH| exact FH| clear - F64; Z.div_mod_to_equations; lia| reflexivity| lia| lia| | constructor| exact FFR02| | exact WM3].
    - constructor; [cbn; split; [lia| left; lia]|].
      constructor; [cbn; split; [lia| right; split; [intros b Hb; destruct (FFD b Hb); lia| exists FF, (FF+64); split; [exact FH| lia]]]|].
      constructor; [cbn; split; [lia| right; split; [intros b Hb; destruct (FFD b Hb); lia| exists FF, (FF+64); split; [exact FH| lia]]]| constructor].
    - eapply munch_weaken; [| exact MU3]. intros x Hx. cbn [outside app] in *. rewrite ?shad_div in *.
      rewrite ?Z.shiftr_div_pow2 in * by lia. change (2^3) with 8 in *. unfold ASHOFF in *. clear - Hx. lia. }
  (* [comment removed for export] *)
  destruct (FHL _ _ _ _ _ AH) as [FAB _]. pose proof (ablk_disj_band _ _ FAB) as FABD. pose proof (ablk_lin _ _ FAB) as (FABa & _).
  unfold AIMG_HI in FABa. unfold FAKESZ in *.
  set (W3 := [(SPB, SPB + 48); (FF, FF + 24); (FF + 48, FF + 52); (Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450880 + 8)]) in MU3.
  (* [comment removed for export] *)
  assert (TBL : forall X n, ainblk LB X n -> 0 <= n -> (X + n <= lo \/ SPV <= X) -> X + n <= 2^47 ->
            disjoint_from W3 X n /\ (0 < n -> disjoint_from W3 (shad X) (shad (X + n - 1) + 1 - shad X))).
  { intros X nn IB Hn HS HH.
    destruct (fk_inblk_ablk LB X nn LBH IB Hn) as (AX & BX & ABX0 & AX1 & AX2).
    pose proof (ablk_lin _ _ ABX0) as (LX1 & LX2 & LX3 & LX4). pose proof (ablk_disj_band _ _ ABX0) as DBX. unfold AIMG_HI, KLS in LX1, DBX.
    pose proof (fk_inblk_apart AI _ _ _ _ _ _ _ _ X nn AH2 IB Hn) as DFX.
    pose proof (ablk_disj_band _ _ FH) as DBF. unfold KLS in DBF.
    subst W3. cbn [disjoint_from]. rewrite !shad_div. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold ASHOFF.
    clear - Hn HS HH DFX DBX DBF LX1 AX1 AX2 SPAB LO BOT FHa FHb FHc FHd F64 ATR.
    split; [| intros Hp]; (split; [Z.div_mod_to_equations; lia|]; split; [Z.div_mod_to_equations; lia|]; split; [Z.div_mod_to_equations; lia|];
                           split; [Z.div_mod_to_equations; lia| exact I]). }
  (* [comment removed for export] *)
  assert (TI : forall X n, 0 <= X -> X + n <= AIMG_HI -> 0 < n ->
            disjoint_from (fake_area L ++ [(SPB - SMK_STACK, SPB)]) X n
            /\ disjoint_from (fake_area L ++ [(SPB - SMK_STACK, SPB)]) (shad X) (shad (X + n - 1) + 1 - shad X)
            /\ disjoint_from W3 X n /\ disjoint_from W3 (shad X) (shad (X + n - 1) + 1 - shad X)).
  { intros X nn X0 XH Hp. unfold AIMG_HI in XH. pose proof (ablk_disj_band _ _ FH) as DBF. unfold KLS in DBF, FABD.
    subst W3. cbn [disjoint_from fake_area app]. rewrite !shad_div. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    unfold ASHOFF, SMK_STACK, FAKESZ. clear - X0 XH Hp FABa FABD SPAB LO BOT FHa FHb FHc FHd F64 DBF ATR.
    repeat split; Z.div_mod_to_equations; lia. }
  destruct (TBL DST cap IND ltac:(lia) SDS ltac:(lia)) as [DN DSN].
  destruct (TBL WK wksz INW ltac:(lia) SWS ltac:(lia)) as [DW DSW].
  assert (SD3 : stk bsegs m3 DST (DST + cap)).
  { eapply stk_transport_disjoint; [| exact MU3| exact WM3| replace (DST + cap - DST) with cap by lia; exact DN].
    eapply (fd_stk_pres AI); [exact HPR2| replace (DST + cap - DST) with cap by lia; exact IND|].
    eapply stk_transport_disjoint; [exact SD| exact MU1| exact WM1| apply D1; lia]. }
  assert (SW3 : stk bsegs m3 WK (WK + wksz)).
  { eapply stk_transport_disjoint; [| exact MU3| exact WM3| replace (WK + wksz - WK) with wksz by lia; exact DW].
    eapply (fd_stk_pres AI); [exact HPR2| replace (WK + wksz - WK) with wksz by lia; exact INW|].
    eapply stk_transport_disjoint; [exact SW| exact MU1| exact WM1| apply D1; lia]. }
  assert (UD3 : 0 < cap -> unpoisoned m3 DST (DST + cap)).
  { intros CP. eapply unpoisoned_munch; [| exact MU3| apply DSN; lia].
    eapply (fk_unp_pres AI); [exact AH2| intros b Hb; right; exact Hb| exact HPR2| exact IND| lia|].
    eapply unpoisoned_munch; [exact (UD CP)| exact MU1| apply DS1; lia]. }
  assert (UW3 : 0 < wksz -> unpoisoned m3 WK (WK + wksz)).
  { intros WP. eapply unpoisoned_munch; [| exact MU3| apply DSW; lia].
    eapply (fk_unp_pres AI); [exact AH2| intros b Hb; right; exact Hb| exact HPR2| exact INW| lia|].
    eapply unpoisoned_munch; [exact (UW WP)| exact MU1| apply DS1; lia]. }
  (* [comment removed for export] *)
  assert (HB3 : bytes_at bsegs m3 SRC src /\ (0 < n -> unpoisoned m3 SRC (SRC + n))).
  { destruct (Z.eq_dec n 0) as [E0|NZ].
    { rewrite E0 in *. destruct src; [| cbn [length] in LSB; lia]. split; [exact (fd_bytes_at_nil1 _ _ _ SB)| intros; lia]. }
    destruct (INS ltac:(lia)) as [IBB | [IB1 IB2]].
    - destruct (TBL SRC n IBB ltac:(lia) SSS ltac:(lia)) as [DB DSB]. split.
      + eapply bytes_at_transport; [| exact MU3| rewrite LSB; exact DB]. eapply (fk_bytes_pres AI); [exact HPR2| rewrite LSB; exact IBB|].
        eapply bytes_at_transport; [exact SB| exact MU1| apply D1; [rewrite LSB; exact SSS| lia]].
      + intros NP. eapply unpoisoned_munch; [| exact MU3| apply DSB; lia].
        eapply (fk_unp_pres AI); [exact AH2| intros b Hb; right; exact Hb| exact HPR2| exact IBB| lia|].
        eapply unpoisoned_munch; [exact (US NP)| exact MU1| apply DS1; lia].
    - destruct (TI SRC n ltac:(lia) IB2 ltac:(lia)) as (DB2 & DSB2 & DB3 & DSB3). split.
      + eapply bytes_at_transport; [| exact MU3| rewrite LSB; exact DB3].
        eapply bytes_at_transport; [| exact MUF2| rewrite LSB; exact DB2].
        eapply bytes_at_transport; [exact SB| exact MU1| apply D1; [rewrite LSB; exact SSS| lia]].
      + intros NP. eapply unpoisoned_munch; [| exact MU3| apply DSB3].
        eapply unpoisoned_munch; [| exact MUF2| apply DSB2].
        eapply unpoisoned_munch; [exact (US NP)| exact MU1| apply DS1; lia]. }
  destruct HB3 as [SB3 US3].
  subst W3.
  destruct ALT as [(WGE & -> & -> & -> & FRA3 & ->) | (WLT & FRA3 & y10 & y11 & y12 & y13 & y14 & y16 & y20 & y21 & y22 & y23 & y24 & y25 & y26 & y27 & ->)].
  - apply evtF_done. eapply KCALL; eassumption.
  - apply evtF_done. eapply KEXIT; eassumption.
Qed.
End Asm.
End CANSEC1.
