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
     AZ_kit AZ_globals AZ_globalsR AZ_fkit AZ_huf_iface AZ_hft_iface AZ_hft_rs_iface AF_fse_rd_base AF_fse_rd_mem AF_fse_rd_seg AF_fse_rd_asm
     AZ_hft_x1_seg AZ_hft_x1_env AZ_hft_x2_geo AZ_hft_x2_seg.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKitF.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.

Section CANSEC1. Context {rc : runConstT}.

Section Asm.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Variable fflag : alayout -> Z -> Z -> Z.
Variable rng_fs : alayout -> footprint -> Prop.
Hypothesis FFLAG : AFakeK_iface.fake_flag_law AI fflag.
Hypothesis FREL : AFakeK_iface.fake_release_law AI fflag.
Hypothesis SM0K : forall k, Z.of_nat k < 16384 -> stack_malloc_0k_stmt AI fflag rng_fs k.
Hypothesis FHL : fake_heap_law AI.
Notation FB0 F := (mkABlock (ABFake 0) F 64).
Notation SW := 5920 (only parsing).     (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma x2_closeZ : forall (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
    (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (m m4 : amem) (SPV DT WK wksz lo FF r : Z) (dtb' : list byte) (j0 : word)
    (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x18 x19 x20 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31 : word),
  AHEAP AI L RNG st (FB0 FF :: LB) m4 -> ablkLB LB ->
  FF mod 64 = 0 -> ablk FF (FF + 64) -> FF + 64 <= ATOP -> rng RNG FF 64 -> rng RNG (shad FF) 8 ->
  (forall b, In b LB -> FF + 64 <= ab_addr b \/ ab_addr b + ab_size b <= FF) ->
  al_fake L <= FF -> FF + 64 <= al_fake L + FAKESZ ->
  munch ([(DT, DT + HUF_DTABLE_BYTES); (WK, WK + wksz); (SPV - SW, SPV)] ++ fake_area L) m m4 ->
  wmono bsegs m m4 -> mem_inv bsegs m4 ->
  ffr_pres [(DT, DT + HUF_DTABLE_BYTES); (WK, WK + wksz)] LB m m4 ->
  rw_cells bsegs m4 (Z.shiftr FF 3 + 2147450880) X2SH ->
  rw_cells bsegs m4 FF [C8 j0] -> rw_cells bsegs m4 (FF + 56) [C8 (Z_to_bv 64 (fflag L 0 FF))] ->
  rw_cells bsegs m4 (SPV + -104) (X2SAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  rw_cells bsegs m4 (SPA2 SPV + 112) [C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF)] ->
  stk bsegs m4 lo (SPA2 SPV + 112) -> stk bsegs m4 (SPA2 SPV + 128) (SPV + -104) ->
  ATOP + 4096 <= lo -> lo <= SPV - HUF_TBL_STACK_A -> SPV + 16 < al_top L -> SPV mod 16 = 0 -> rng RNG lo (al_top L - lo) -> rng_aimg RNG ->
  ainblk LB DT HUF_DTABLE_BYTES -> ainblk LB WK wksz -> DT + HUF_DTABLE_BYTES <= 2^47 -> WK + wksz <= 2^47 -> 0 <= wksz ->
  u8arr bsegs m4 DT dtb' -> huf_hdr_ok dtb' -> stk bsegs m4 WK (WK + wksz) ->
  0 <= r < 2^64 ->
  (zd_is_error r = false -> huf_tbl_ok dtb' /\ exists ty, nth_error dtb' 1 = Some ty /\ (bv_unsigned ty <> 0 <-> true = true)) ->
  evtF bsegs RNG (huf_rd_postA AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV DT WK wksz lo true m)
    (MS (mkR x1 (Z_to_bv 64 (SPA2 SPV)) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPA2 SPV)) x10 x11 x12 x13 x14 x15 x16 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880))
             x18 x19 x20 x21 x22 x23 x24 x25 (Z_to_bv 64 r) x27 x28 x29 x30 x31)
        FR (Z_to_bv 64 0x99470) fc None m4 (seg_rom bsegs)).
Proof.
  intros L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m m4 SPV DT WK wksz lo FF r dtb' j0
         x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x18 x19 x20 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31
         AH4 LBH F64 FH FC RFF RSFF FFD FFA1 FFA2 MU04 WM04 MI4 FFR04 SHF4 FF04 FF564 FRB4 FRA4 STL4 STG4 BOT LO SPT SP16 RSTK RI
         IND INW DHI WHI WK0 TB4 HOK STW4 Hr RES.
  pose proof atop_range as ATR.
  pose proof (AI_layout AI _ _ _ _ _ AH4) as (LY1 & LY2 & LY3 & LY4 & _).
  pose proof (spa2_props SPV SP16) as (SPAB & SPA32 & _).
  pose proof (AI_aci_img AI) as HCI. pose proof (AI_aci_lo AI) as HCI0.
  pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in FHa.
  destruct (FFLAG _ _ _ _ _ _ _ _ AH4 ltac:(left; reflexivity)) as (FLC & RG & GH & GC & GBL & GCI & GFA).
  pose proof (GBL _ ltac:(left; reflexivity)) as GF. cbn [ab_addr ab_size] in GF.
  pose proof (ablk_lin _ _ GH) as (GHa & GHb & GHc & GHd). unfold AIMG_HI in GHa.
  assert (BSF : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 8 <= 17594333495296)
    by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
  assert (DT0 : 0 <= DT).
  { destruct (fk_inblk_ablk LB DT HUF_DTABLE_BYTES LBH IND ltac:(unfold HUF_DTABLE_BYTES in *; lia)) as (A0 & N0 & AB0 & A1 & A2).
    pose proof (ablk_lin _ _ AB0) as (L1 & _). unfold AIMG_HI in L1. lia. }
  assert (WKp : 0 <= WK).
  { destruct (fk_inblk_ablk LB WK wksz LBH INW WK0) as (A0 & N0 & AB0 & A1 & A2).
    pose proof (ablk_lin _ _ AB0) as (L1 & _). unfold AIMG_HI in L1. lia. }
  eapply evtF_cut.
  { eapply (x2_epi ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV lo);
      first [exact SHF4| exact FF04| exact FF564| exact FLC| exact FRB4| exact FRA4| exact STL4| exact STG4| exact MI4
            | exact FH| exact FC| exact F64| exact GH| exact GC| exact GF| exact RFF| exact RSFF| exact RG| exact SP16| exact RI
            | eapply rng_sub'; [exact RSTK| lia]| exact Hr | unfold KEND; lia | lia]. }
  cbv beta. intros ms' (mp & m5 & x11' & x12' & x13' & -> & MU1 & WM1 & MIp & MU2 & WM2 & MI5 & ST5 & FLC5).
  assert (AHp : AHEAP AI L RNG st (FB0 FF :: LB) mp).
  { eapply (AI_frame AI); [exact AH4| exact MU1| exact WM1|].
    constructor; [| constructor; [| constructor]]; cbn.
    - right; right. right; right. exists 0, FF, 64. split; [left; reflexivity|].
      rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold ASHOFF. Z.div_mod_to_equations. lia.
    - right; left. exists (FB0 FF). split; [left; reflexivity| cbn; lia]. }
  assert (AH5 : AHEAP AI L RNG st LB m5).
  { eapply (fk_release AI fflag); [exact FREL| exact AHp| lia| lia| lia| exact MU2| exact FLC5]. }
  (* [comment removed for export] *)
  assert (TC : forall X n, ainblk LB X n -> 0 <= n -> X + n <= 2^47 ->
            disjoint_from [(Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450880 + 8); (FF, FF + 8)] X n
            /\ disjoint_from [(fflag L 0 FF, fflag L 0 FF + 1)] X n).
  { intros X n (b & Hb & Hb1 & Hb2) Hn HH.
    pose proof (FFD b Hb) as D1. pose proof (GBL b ltac:(right; exact Hb)) as D2. pose proof (ablk_disj_band _ _ (LBH b Hb)) as D3.
    unfold KLS in D3. cbn [disjoint_from]. clear - Hb1 Hb2 Hn HH D1 D2 D3 BSF. repeat split; lia. }
  destruct (TC DT HUF_DTABLE_BYTES IND ltac:(unfold HUF_DTABLE_BYTES in *; lia) DHI) as [DN1 DN2].
  destruct (TC WK wksz INW WK0 WHI) as [DW1 DW2].
  pose proof HOK as (LTB & _).
  apply evtF_done. unfold huf_rd_postA. do 14 eexists. exists m5, r, dtb'.
  split; [reflexivity|].
  split.
  { eapply munch_trans; [eapply munch_weaken; [| exact MU04]; intros x Hx; cbn [outside app fake_area] in *; clear - Hx; lia|]. eapply munch_trans.
    - eapply munch_weaken; [| exact MU1]. intros x Hx. cbn [outside app fake_area] in *.
      rewrite ?shad_div in *. rewrite ?Z.shiftr_div_pow2 in * by lia. change (2^3) with 8 in *. unfold FAKESZ, ASHOFF in *.
      clear - Hx FFA1 FFA2 F64. Z.div_mod_to_equations. lia.
    - eapply munch_weaken; [| exact MU2]. intros x Hx. cbn [outside app fake_area] in *. unfold FAKESZ in *. clear - Hx GFA. lia. }
  split; [eapply wmono_trans; [exact WM04| eapply wmono_trans; [exact WM1| exact WM2]]|].
  split; [exact MI5|]. split; [exact ST5|].
  split.
  { eapply stk_transport_disjoint; [eapply stk_transport_disjoint; [exact STW4| exact MU1| exact WM1| replace (WK + wksz - WK) with wksz by lia; exact DW1]
                                   | exact MU2| exact WM2| replace (WK + wksz - WK) with wksz by lia; exact DW2]. }
  split.
  { eapply ffr_pres_trans; [exact FFR04|]. apply ffr_pres_mono_nil1.
    eapply (fk_ffr_fin AI L RNG st LB m4 m4 m5 0 FF 64 (shad FF) 8 [] [(FF, FF + 8); (fflag L 0 FF, fflag L 0 FF + 1)]);
      [exact AH4| exact LBH| exact FH| clear - F64; Z.div_mod_to_equations; lia| reflexivity| lia| lia| | constructor| apply ffr_pres_refl| |
       eapply wmono_trans; [exact WM1| exact WM2]].
    - constructor; [cbn; split; [lia| right; split; [intros b Hb; destruct (FFD b Hb); lia| exists FF, (FF + 64); split; [exact FH| lia]]]|].
      constructor; [cbn; split; [lia| right; split; [intros b Hb; exact (GBL b ltac:(right; exact Hb))| exists (fflag L 0 FF), (fflag L 0 FF + 1); split; [exact GH| lia]]]| constructor].
    - eapply munch_trans.
      + eapply munch_weaken; [| exact MU1]. intros x Hx. cbn [outside app] in *. rewrite ?shad_div in *.
        rewrite ?Z.shiftr_div_pow2 in * by lia. change (2^3) with 8 in *. unfold ASHOFF in *. clear - Hx. lia.
      + eapply munch_weaken; [| exact MU2]. intros x Hx. cbn [outside app] in *. clear - Hx. lia. }
  split; [exact AH5|].
  split.
  { eapply u8arr_transport; [eapply u8arr_transport; [exact TB4| exact MU1| exact WM1| rewrite LTB; exact DN1]| exact MU2| exact WM2| rewrite LTB; exact DN2]. }
  split; [exact HOK|]. split; [exact Hr| exact RES].
Qed.
(* [comment removed for export] *)
Lemma x2_got_cells : forall m, (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) ->
  rw_cells bsegs m AGOT_SUAR_R [C8 (Z_to_bv 64 0xcfd00)] /\ rw_cells bsegs m AGOT_X2PC [C8 (Z_to_bv 64 0x97374)].
Proof.
  intros m R. unfold AGOT_SUAR_R, AGOT_X2PC. split;
    (apply relro_wordA; [exact R| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity]).
Qed.

(* [comment removed for export] *)
Lemma x2_openZ : forall (k : nat) (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
    (ra gp tp t0 t1 t2 s0 s1 flags a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem)
    (SPV DT WK wksz SRC n lo : Z) (dtb src jw : list byte) (Q : machine_state -> Prop),
  Z.of_nat k < 16384 ->
  AHEAP AI L RNG st LB m -> fake_le 0 k LB -> ablkLB LB ->
  rng_aimg RNG -> rng RNG lo (al_top L - lo) -> rng_fs L RNG ->
  ATOP + 4096 <= lo -> lo <= SPV - HUF_TBL_STACK_A -> SPV + 16 < al_top L -> SPV mod 16 = 0 ->
  stk bsegs m lo SPV -> mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
  0 <= wksz < 2^32 -> 0 <= n < 2^32 ->
  (* [comment removed for export] *)
  u8arr bsegs m DT dtb -> zlen dtb = HUF_DTABLE_BYTES -> nth_error dtb 0 = Some (Z_to_bv 8 12) -> ainblk LB DT HUF_DTABLE_BYTES -> unpoisoned m DT (DT + HUF_DTABLE_BYTES) ->
  (DT + HUF_DTABLE_BYTES <= lo \/ SPV <= DT) -> 4096 <= DT -> DT + HUF_DTABLE_BYTES < 2^47 -> DT mod 4 = 0 ->
  rng RNG DT HUF_DTABLE_BYTES -> rng RNG (shad DT) 1 ->
  rw_cells bsegs m WK [CB (Z.to_nat wksz) jw] -> ainblk LB WK wksz -> (0 < wksz -> unpoisoned m WK (WK + wksz)) -> 4096 <= WK -> WK mod 4 = 0 ->
  (WK + wksz <= lo \/ SPV <= WK) -> WK + wksz < 2^47 ->
  bytes_at bsegs m SRC src -> zlen src = n -> (0 < n -> ainimg LB SRC n) -> (0 < n -> unpoisoned m SRC (SRC + n)) -> 0 <= SRC ->
  (SRC + n <= lo \/ SPV <= SRC) -> SRC + n <= 2^47 ->
  (* [comment removed for export] *)
  (forall (FF : Z) (m3 : amem) (j3 : list byte) (y5 y6 y7 y12 y28 y29 y30 y31 : word),
     FF mod 64 = 0 -> ablk FF (FF + 64) -> FF + 64 <= ATOP -> rng RNG FF 64 -> rng RNG (shad FF) 8 ->
     (forall b, In b LB -> FF + 64 <= ab_addr b \/ ab_addr b + ab_size b <= FF) ->
     al_fake L <= FF -> FF + 64 <= al_fake L + FAKESZ ->
     AHEAP AI L RNG st (FB0 FF :: LB) m3 ->
     munch ([(SPV - SW, SPV)] ++ fake_area L) m m3 -> wmono bsegs m m3 -> ffr_pres [] LB m m3 -> mem_inv bsegs m3 ->
     rw_cells bsegs m3 (SPV + -104) (X2SAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
     rw_cells bsegs m3 (SPA2 SPV + 112) [C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF)] ->
     stk bsegs m3 lo (SPA2 SPV + 112) -> stk bsegs m3 (SPA2 SPV + 128) (SPV + -104) ->
     rw_cells bsegs m3 FF (X2FFHDR (fflag L 0 FF) j3) -> rw_cells bsegs m3 (Z.shiftr FF 3 + 2147450880) X2SH ->
     u8arr bsegs m3 DT dtb -> unpoisoned m3 DT (DT + HUF_DTABLE_BYTES) ->
     rw_cells bsegs m3 WK [CB (Z.to_nat wksz) jw] -> (0 < wksz -> unpoisoned m3 WK (WK + wksz)) ->
     bytes_at bsegs m3 SRC src -> (0 < n -> unpoisoned m3 SRC (SRC + n)) ->
     wksz < 2124 ->
     Q (MS (mkR (Z_to_bv 64 0x973f8) (Z_to_bv 64 (SPA2 SPV)) gp tp y5 y6 y7 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPA2 SPV))
              (Z_to_bv 64 DT) (Z_to_bv 64 531) y12 (Z_to_bv 64 WK) (Z_to_bv 64 (Z.shiftr DT 3 + 2147450880)) (Z_to_bv 64 18446744073709551603) (Z_to_bv 64 18446744073709551602)
              (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880))
              (Z_to_bv 64 SRC) (Z_to_bv 64 FF) s4 (Z_to_bv 64 wksz) s6 (Z_to_bv 64 n) (Z_to_bv 64 2147450880) flags (Z_to_bv 64 18446744073709551615) s11 y28 y29 y30 y31)
           FR (Z_to_bv 64 0x99470) fc None m3 (seg_rom bsegs))) ->
  (* [comment removed for export] *)
  (forall (FF : Z) (m3 : amem) (jA jB jC jD j3 : list byte) (y5 y6 y7 y28 y29 y30 y31 : word) (hdw : Z),
     FF mod 64 = 0 -> ablk FF (FF + 64) -> FF + 64 <= ATOP -> rng RNG FF 64 -> rng RNG (shad FF) 8 ->
     (forall b, In b LB -> FF + 64 <= ab_addr b \/ ab_addr b + ab_size b <= FF) ->
     al_fake L <= FF -> FF + 64 <= al_fake L + FAKESZ ->
     AHEAP AI L RNG st (FB0 FF :: LB) m3 ->
     munch ([(SPV - SW, SPV)] ++ fake_area L) m m3 -> wmono bsegs m m3 -> ffr_pres [] LB m m3 -> mem_inv bsegs m3 ->
     rw_cells bsegs m3 (SPV + -104) (X2SAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
     rw_cells bsegs m3 (SPA2 SPV) (X2FRA0 FF DT WK hdw jA jB jC jD) ->
     rw_cells bsegs m3 FF (X2FFHDR (fflag L 0 FF) j3) -> rw_cells bsegs m3 (Z.shiftr FF 3 + 2147450880) X2SH ->
     stk bsegs m3 (SPA2 SPV + 728) (SPV + -104) ->
     u8arr bsegs m3 DT dtb -> unpoisoned m3 DT (DT + HUF_DTABLE_BYTES) ->
     rw_cells bsegs m3 WK [CB (Z.to_nat wksz) jw] -> (0 < wksz -> unpoisoned m3 WK (WK + wksz)) ->
     bytes_at bsegs m3 SRC src -> (0 < n -> unpoisoned m3 SRC (SRC + n)) ->
     2124 <= wksz -> hdw mod 256 = 12 -> 0 <= hdw < 2^32 -> firstn 4 dtb = le4 (Z_to_bv 64 hdw) -> stk bsegs m3 lo (SPA2 SPV) ->
     Q (MS (mkR (Z_to_bv 64 0x974fc) (Z_to_bv 64 (SPA2 SPV)) gp tp y5 y6 y7 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPA2 SPV))
              (Z_to_bv 64 (WK + 624)) (Z_to_bv 64 0) (Z_to_bv 64 112) (Z_to_bv 64 WK) (Z_to_bv 64 (Z.shiftr DT 3 + 2147450880)) (Z_to_bv 64 18446744073709551603) (Z_to_bv 64 18446744073709551602)
              (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880))
              (Z_to_bv 64 SRC) (Z_to_bv 64 FF) s4 (Z_to_bv 64 WK) (Z_to_bv 64 12) (Z_to_bv 64 n) (Z_to_bv 64 2147450880) flags s10 (Z_to_bv 64 (WK + 624)) y28 y29 y30 y31)
           FR (Z_to_bv 64 0x53ca0) fc None m3 (seg_rom bsegs))) ->
  evtF bsegs RNG Q
    (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DT) (Z_to_bv 64 SRC) (Z_to_bv 64 n) (Z_to_bv 64 WK)
             (Z_to_bv 64 wksz) flags a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 APHUF_RDX2) fc None m (seg_rom bsegs)).
Proof.
  intros k L RNG st LB ra gp tp t0 t1 t2 s0 s1 flags a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m SPV DT WK wksz SRC n lo dtb src jw Q
         HK AH FLE LBH RI RSTK RFS BOT LO SPT SP16 ST MI TP WR NR
         TB LTB HDR0 IND UD SDS DTL DTH DT4 RDT RSD1 WC INW UW WKL WK4 SWS WHI SB LSB INS US SRC0 SSS SHI KEXIT KCALL.
  assert (WK0 : 0 <= WK) by lia.
  pose proof atop_range as ATR. unfold APHUF_RDX2.
  pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & LY4 & _).
  pose proof (spa2_props SPV SP16) as (SPAB & SPA32 & _).
  pose proof (AI_aci_img AI) as HCI. pose proof (AI_aci_lo AI) as HCI0.
  assert (LOS : lo <= SPV - 848 - 4096 - 16) by lia.
  assert (LOC : ATOP <= lo) by lia.
  assert (SPK : SPV + 16 < KEND) by (unfold KEND; lia).
  assert (DT0 : 0 <= DT) by (destruct UD as (U & _); exact U).
  assert (DHI : DT + HUF_DTABLE_BYTES <= 2^47) by lia.
  assert (ABD : ablk DT (DT + HUF_DTABLE_BYTES)).
  { destruct (fk_inblk_ablk LB DT HUF_DTABLE_BYTES LBH IND ltac:(unfold HUF_DTABLE_BYTES; lia)) as (A0 & N0 & AB0 & A1 & A2).
    eapply ablk_sub; [exact AB0| exact A1| exact A2]. }
  (* [comment removed for export] *)
  pose proof (AI_rtcells AI _ _ _ _ _ AH) as RTC. unfold artcells in RTC.
  destruct RTC as (C0 & GOT & RIC & REAL & SHB & SUA & INI & LAY & _).
  destruct (x2_got_cells m (AI_relro AI _ _ _ _ _ AH)) as [GSU _].
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply x2_pro; first [exact ST| exact MI| exact GOT| exact SHB| exact GSU| exact SUA| exact SP16| eapply rng_sub'; [exact RSTK| lia]
            | exact RI| exact LOS | exact LOC | exact SPK]. }
  cbv beta. intros ms' (m1 & jA & jB & -> & MU1 & WM1 & MI1 & FRB1 & FRA1 & STL1 & STG1).
  clear C0 GOT RIC REAL SHB SUA INI LAY GSU.
  assert (AH1 : AHEAP AI L RNG st LB m1).
  { eapply (AI_frame AI); [exact AH| exact MU1| exact WM1|]. constructor; [| constructor]. left; left. cbn. lia. }
  (* [comment removed for export] *)
  assert (D1 : forall X n, (X + n <= lo \/ SPV <= X) -> 0 <= n -> disjoint_from [(SPV - 848, SPV)] X n).
  { intros X nn HX Hn. cbn [disjoint_from]. split; [lia| exact I]. }
  assert (DS1 : forall X n, 0 <= X -> 0 <= n -> X + n <= 2^47 ->
             disjoint_from [(SPV - 848, SPV)] (shad X) (shad (X + n - 1) + 1 - shad X)).
  { intros X nn X0 Hn Hb. cbn [disjoint_from]. split; [| exact I]. left. rewrite !shad_div. unfold ASHOFF in *.
    clear - X0 Hn Hb ATR BOT LO. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  eapply evtF_cut.
  { pose proof (SM0K k HK) as SMC. unfold stack_malloc_0k_stmt in SMC. eapply SMC with (lo := lo); clear SMC;
      rewrite ?(unsigned_lit (SPA2 SPV)) by lia;
      first [exact AH1| exact FLE| exact MI1| exact STL1| exact TP| reflexivity| exact RSTK| exact RI| exact RFS| lia| unfold SMK_STACK; lia]. }
  cbv beta. intros ms' PO.
  destruct PO as (FF & z5 & z6 & z7 & e11 & e12 & e13 & e14 & e15 & e16 & e17 & z28 & z29 & z30 & z31 & m2 & j0 & j1 & j2 & junk
                  & -> & MI2 & ST2 & HPR2 & AH2 & F64 & FH & FC & FFC2 & SHF2 & RFF & RSFF & MUF2 & WM2 & FFA1 & FFA2).
  rewrite ?(unsigned_lit (SPA2 SPV)) in ST2, HPR2, MUF2 by lia.
  rd_retlit.
  pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in FHa.
  pose proof (fk_frame_apart AI _ _ _ _ _ _ _ _ AH2) as FFD.
  pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR2 FRB1 ltac:(left; left; cbn; lia)) as FRB2.
  pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR2 FRA1 ltac:(left; left; cbn; lia)) as FRA2.
  pose proof (aheap_pres_stk _ _ _ _ _ _ _ HPR2 STG1 ltac:(lia) ltac:(lia)) as STG2.
  assert (BSF : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 8 <= 17594333495296)
    by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
  destruct (FHL _ _ _ _ _ AH) as [FAB _]. pose proof (ablk_disj_band _ _ FAB) as FABD. pose proof (ablk_lin _ _ FAB) as (FABa & _).
  unfold AIMG_HI in FABa. unfold FAKESZ in *.
  (* [comment removed for export] *)
  assert (TB2 : u8arr bsegs m2 DT dtb).
  { assert (ARR1 : u8arr bsegs m1 DT dtb) by (eapply u8arr_transport; [exact TB| exact MU1| exact WM1| apply D1; rewrite LTB; [exact SDS| unfold HUF_DTABLE_BYTES in *; lia]]).
    destruct ARR1 as [BA WA]; split; [eapply (fk_bytes_pres AI); [exact HPR2| rewrite LTB; exact IND| exact BA] | eapply wr_at_transport; [exact WA| exact WM2]]. }
  assert (WC2 : rw_cells bsegs m2 WK [CB (Z.to_nat wksz) jw]).
  { eapply (fk_cells_pres AI); [exact HPR2| cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by lia; exact INW|].
    eapply rw_cells_transport; [exact WC| exact MU1| exact WM1| apply D1; [cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by lia; exact SWS| lia]]. }
  assert (UD2 : unpoisoned m2 DT (DT + HUF_DTABLE_BYTES)).
  { eapply (fk_unp_pres AI); [exact AH2| intros b Hb; right; exact Hb| exact HPR2| exact IND| unfold HUF_DTABLE_BYTES in *; lia|].
    eapply unpoisoned_munch; [exact UD| exact MU1| apply DS1; unfold HUF_DTABLE_BYTES in *; lia]. }
  assert (UW2 : 0 < wksz -> unpoisoned m2 WK (WK + wksz)).
  { intros WP. eapply (fk_unp_pres AI); [exact AH2| intros b Hb; right; exact Hb| exact HPR2| exact INW| lia|].
    eapply unpoisoned_munch; [exact (UW WP)| exact MU1| apply DS1; lia]. }
  (* [comment removed for export] *)
  assert (TI : forall X n, 0 <= X -> X + n <= AIMG_HI -> 0 < n ->
            disjoint_from (fake_area L ++ [(SPA2 SPV - SMK_STACK, SPA2 SPV)]) X n
            /\ disjoint_from (fake_area L ++ [(SPA2 SPV - SMK_STACK, SPA2 SPV)]) (shad X) (shad (X + n - 1) + 1 - shad X)).
  { intros X nn X0 XH Hp; unfold AIMG_HI in XH; unfold KLS in FABD;
    cbn [disjoint_from fake_area app]; rewrite !shad_div; unfold ASHOFF, SMK_STACK, FAKESZ; clear - X0 XH Hp FABa FABD SPAB LO BOT ATR;
    repeat split; Z.div_mod_to_equations; lia. }
  assert (HB2 : bytes_at bsegs m2 SRC src /\ (0 < n -> unpoisoned m2 SRC (SRC + n))).
  { destruct (Z.eq_dec n 0) as [E0|NZ];
    [ rewrite E0 in *; destruct src; [| cbn [length] in LSB; lia]; split; [exact (bytes_at_nil1 _ _ _ SB)| intros; lia]
    | destruct (INS ltac:(lia)) as [IBB | [IB1 IB2]];
      [ split;
        [ eapply (fk_bytes_pres AI); [exact HPR2| rewrite LSB; exact IBB|];
          eapply bytes_at_transport; [exact SB| exact MU1| apply D1; [rewrite LSB; exact SSS| lia]]
        | intros NP; eapply (fk_unp_pres AI); [exact AH2| intros b Hb; right; exact Hb| exact HPR2| exact IBB| lia|];
          eapply unpoisoned_munch; [exact (US NP)| exact MU1| apply DS1; lia] ]
      | destruct (TI SRC n SRC0 IB2 ltac:(lia)) as (DB2 & DSB2); split;
        [ eapply bytes_at_transport; [| exact MUF2| rewrite LSB; exact DB2];
          eapply bytes_at_transport; [exact SB| exact MU1| apply D1; [rewrite LSB; exact SSS| lia]]
        | intros NP; eapply unpoisoned_munch; [| exact MUF2| apply DSB2];
          eapply unpoisoned_munch; [exact (US NP)| exact MU1| apply DS1; lia] ] ] ]. }
  destruct HB2 as [SB2 US2].
  assert (DFD : DT + 16388 <= FF \/ FF + 64 <= DT).
  { pose proof (fk_inblk_apart AI _ _ _ _ _ _ _ _ DT HUF_DTABLE_BYTES AH2 IND ltac:(unfold HUF_DTABLE_BYTES; lia)) as D. unfold HUF_DTABLE_BYTES in D. lia. }
  (* [comment removed for export] *)
  destruct (x2_got_cells m2 (AI_relro AI _ _ _ _ _ AH2)) as [_ GPC2].
  eapply x2_hdr1; first [exact FRA2| exact ST2| exact FFC2| exact SHF2| exact GPC2| exact MI2| exact FH| exact FC| exact F64
                       | exact RFF| exact RSFF| exact TB2| exact HDR0| exact UD2| exact ABD | exact DT4 | exact DFD | exact RSD1 | exact WR | exact WKL | exact WK4
                       | exact SP16| exact RI| eapply rng_sub'; [exact RSTK| lia]
                       | unfold HUF_DTABLE_BYTES in *; first [exact LTB | exact SDS | exact RDT | lia]
                       | exact LOS | exact LOC | exact SPK | lia | idtac].
  all: intros m3.
  1: intros j3 y12 HW MU3 WM3 MI3 FRA3 STL3 STM3 FFC3 SHF3 TB3'.
  2: intros j3 jA' jB' jC jD hdw HW HM HR E4 MU3 WM3 MI3 FRA3 STL3 FFC3 SHF3 TB3'.
  all: assert (AH3 : AHEAP AI L RNG st (FB0 FF :: LB) m3).
  1,3: eapply (AI_frame AI); [exact AH2| exact MU3| exact WM3|];
    (constructor; [cbn; left; left; lia|]);
    (constructor; [cbn; right; left; exists (FB0 FF); split; [left; reflexivity| cbn; lia]|]);
    (constructor; [cbn; right; right; right; right; exists 0, FF, 64; split; [left; reflexivity| rewrite Z.shiftr_div_pow2 by lia;
                  change (2 ^ 3) with 8; unfold ASHOFF; Z.div_mod_to_equations; lia]| constructor]).
  all: pose proof (rw_cells_transport _ _ _ _ _ _ FRB2 MU3 WM3 ltac:(cbn; lia)) as FRB3.
  all: assert (STG3 : stk bsegs m3 (SPA2 SPV + 728) (SPV + -104))
    by (eapply stk_transport; [exact STG2| exact MU3| exact WM3| intros x Hx; left; cbn; lia]).
  (* [comment removed for export] *)
  all: assert (MU03 : munch ([(SPV - SW, SPV)] ++ fake_area L) m m3).
  1,3: eapply munch_trans; [eapply munch_weaken; [| exact MU1]; intros x Hx; cbn [outside app fake_area] in *; lia|];
       eapply munch_trans; [eapply munch_weaken; [| exact MUF2]; intros x Hx; cbn [outside app fake_area] in *; unfold SMK_STACK; lia|];
       eapply munch_weaken; [| exact MU3]; intros x Hx; cbn [outside app fake_area] in *;
       rewrite ?shad_div in *; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; unfold FAKESZ, ASHOFF in *;
       clear - Hx FFA1 FFA2 SPAB LO BOT F64; Z.div_mod_to_equations; lia.
  all: assert (WM03 : wmono bsegs m m3) by (eapply wmono_trans; [exact WM1| eapply wmono_trans; [exact WM2| exact WM3]]).
  all: assert (FFR02 : ffr_pres [] LB m m2)
    by (eapply ffr_pres_trans; [eapply (fk_ffr_stack AI); [exact AH| exact MU1| exact WM1| constructor; [cbn; lia| constructor]]|];
        eapply (fk_ffr_of_pres AI); exact HPR2).
  all: assert (FFR03 : ffr_pres [] LB m m3).
  1,3: eapply (fk_ffr_fin AI L RNG st LB m m2 m3 0 FF 64 (shad FF) 8 [] [(SPA2 SPV, SPA2 SPV + 728); (FF, FF + 24)]);
       [exact AH2| exact LBH| exact FH| clear - F64; Z.div_mod_to_equations; lia| reflexivity| lia| lia| | constructor| exact FFR02| | exact WM3];
       [ constructor; [cbn; split; [lia| left; lia]|];
         constructor; [cbn; split; [lia| right; split; [intros b Hb; destruct (FFD b Hb); lia| exists FF, (FF+64); split; [exact FH| lia]]]| constructor]
       | eapply munch_weaken; [| exact MU3]; intros x Hx; cbn [outside app] in *; rewrite ?shad_div in *;
         rewrite ?Z.shiftr_div_pow2 in * by lia; change (2^3) with 8 in *; unfold ASHOFF in *; clear - Hx; lia ].
  (* [comment removed for export] *)
  all: set (W3 := [(SPA2 SPV, SPA2 SPV + 728); (FF, FF + 24); (Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450880 + 8)]) in MU3.
  all: assert (TBL : forall X n, ainblk LB X n -> 0 <= n -> (X + n <= lo \/ SPV <= X) -> X + n <= 2^47 ->
            disjoint_from W3 X n /\ (0 < n -> disjoint_from W3 (shad X) (shad (X + n - 1) + 1 - shad X))).
  1,3: intros X nn IB Hn HS HH;
    destruct (fk_inblk_ablk LB X nn LBH IB Hn) as (AX & BX & ABX0 & AX1 & AX2);
    pose proof (ablk_lin _ _ ABX0) as (LX1 & LX2 & LX3 & LX4); pose proof (ablk_disj_band _ _ ABX0) as DBX; unfold AIMG_HI, KLS in LX1, DBX;
    pose proof (fk_inblk_apart AI _ _ _ _ _ _ _ _ X nn AH2 IB Hn) as DFX;
    pose proof (ablk_disj_band _ _ FH) as DBF; unfold KLS in DBF;
    subst W3; cbn [disjoint_from]; rewrite !shad_div; rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; unfold ASHOFF;
    clear - Hn HS HH DFX DBX DBF LX1 AX1 AX2 SPAB LO BOT FHa FHb FHc FHd F64 ATR;
    split; [| intros Hp]; (split; [Z.div_mod_to_equations; lia|]; split; [Z.div_mod_to_equations; lia|]; split; [Z.div_mod_to_equations; lia| exact I]).
  all: assert (TI3 : forall X n, 0 <= X -> X + n <= AIMG_HI -> 0 < n ->
            disjoint_from W3 X n /\ disjoint_from W3 (shad X) (shad (X + n - 1) + 1 - shad X)).
  1,3: intros X nn X0 XH Hp; unfold AIMG_HI in XH; pose proof (ablk_disj_band _ _ FH) as DBF; unfold KLS in DBF, FABD;
    subst W3; cbn [disjoint_from fake_area app]; rewrite !shad_div; rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8;
    unfold ASHOFF, SMK_STACK, FAKESZ; clear - X0 XH Hp FABa FABD SPAB LO BOT FHa FHb FHc FHd F64 DBF ATR;
    repeat split; Z.div_mod_to_equations; lia.
  all: destruct (TBL DT HUF_DTABLE_BYTES IND ltac:(unfold HUF_DTABLE_BYTES in *; lia) SDS DHI) as [DN DSN].
  all: destruct (TBL WK wksz INW ltac:(lia) SWS ltac:(lia)) as [DW DSW].
  all: assert (TB3 : u8arr bsegs m3 DT dtb) by (eapply u8arr_transport; [exact TB2| exact MU3| exact WM3| rewrite LTB; exact DN]).
  all: assert (WC3 : rw_cells bsegs m3 WK [CB (Z.to_nat wksz) jw])
    by (eapply rw_cells_transport; [exact WC2| exact MU3| exact WM3| cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by lia; exact DW]).
  all: assert (UD3 : unpoisoned m3 DT (DT + HUF_DTABLE_BYTES)) by (eapply unpoisoned_munch; [exact UD2| exact MU3| apply DSN; unfold HUF_DTABLE_BYTES in *; lia]).
  all: assert (UW3 : 0 < wksz -> unpoisoned m3 WK (WK + wksz)) by (intros WP; eapply unpoisoned_munch; [exact (UW2 WP)| exact MU3| apply DSW; lia]).
  (* [comment removed for export] *)
  all: assert (HB3 : bytes_at bsegs m3 SRC src /\ (0 < n -> unpoisoned m3 SRC (SRC + n))).
  1,3: destruct (Z.eq_dec n 0) as [E0|NZ];
    [ rewrite E0 in *; destruct src; [| cbn [length] in LSB; lia]; split; [exact (bytes_at_nil1 _ _ _ SB)| intros; lia]
    | destruct (INS ltac:(lia)) as [IBB | [IB1 IB2]];
      [ destruct (TBL SRC n IBB ltac:(lia) SSS SHI) as [DB DSB]; split;
        [ eapply bytes_at_transport; [exact SB2| exact MU3| rewrite LSB; exact DB]
        | intros NP; eapply unpoisoned_munch; [exact (US2 NP)| exact MU3| apply DSB; lia] ]
      | destruct (TI3 SRC n SRC0 IB2 ltac:(lia)) as (DB3 & DSB3); split;
        [ eapply bytes_at_transport; [exact SB2| exact MU3| rewrite LSB; exact DB3]
        | intros NP; eapply unpoisoned_munch; [exact (US2 NP)| exact MU3| apply DSB3] ] ] ].
  all: destruct HB3 as [SB3 US3].
  - eapply KEXIT; try eassumption. exact (stk_merge bsegs m3 (SPA2 SPV + 128) (SPA2 SPV + 728) (SPV + -104) STM3 STG3 ltac:(lia)).
  - eapply KCALL; eassumption.
Qed.
End Asm.
End CANSEC1.
