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
     AZ_kit AZ_globals AZ_globalsR AZ_fkit AZ_huf_iface AZ_hft_iface AZ_hft_rs_iface AF_fse_rd_base AF_fse_rd_mem AF_fse_rd_seg AF_fse_rd_asm AZ_hft_x1_seg.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKitF.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.

Section CANSEC1. Context {rc : runConstT}.

Lemma ffr_pres_mono_nil1 : forall W LB (m m' : amem), ffr_pres [] LB m m' -> ffr_pres W LB m m'.
Proof.
  intros W LB m m' H a Ha HP. apply (H a Ha). destruct HP as [[HF _]|HS]; [left; split; [exact HF| exact I]| right; exact HS].
Qed.

(* [comment removed for export] *)
Lemma bytes_at_nil1 : forall (m m' : amem) A, bytes_at bsegs m A [] -> bytes_at bsegs m' A [].
Proof. intros m m' A (H0 & H1 & _). split; [exact H0|]. split; [exact H1|]. intros i Hi. cbn [length] in Hi. lia. Qed.

(* [comment removed for export] *)
Section FC.
Variable AI : AMallocIface.
Hypothesis FHL : fake_heap_law AI.

Lemma disjoint_from_sub1 : forall W a n a' n', disjoint_from W a n -> a <= a' -> a' + n' <= a + n -> disjoint_from W a' n'.
Proof.
  induction W as [|[x y] W IH]; intros a n a' n' D H1 H2; cbn [disjoint_from] in *; [exact I|].
  destruct D as [D1 D2]. split; [lia| eapply IH; [exact D2| lia| lia]].
Qed.

Lemma fcall_bytes_pres : forall L RNG st LB m0 (m m' : amem) W X bs,
  AHEAP AI L RNG st LB m0 -> ainblk LB X (zlen bs) -> disjoint_from W X (zlen bs) ->
  munch (W ++ fake_area L) m m' -> ffr_pres W LB m m' -> bytes_at bsegs m X bs -> bytes_at bsegs m' X bs.
Proof.
  intros L RNG st LB m0 m m' W X bs AH (b & Hb & H1 & H2) DJ MU FP B.
  destruct b as [[p|c] A n]; cbn [ab_addr ab_size] in H1, H2.
  - destruct (fake_area_block AI _ _ _ _ _ p A n FHL AH Hb) as [DF _].
    eapply bytes_at_transport; [exact B| exact MU|]. apply disjoint_from_app2; [exact DJ| eapply disjoint_from_sub1; [exact DF| lia| lia]].
  - eapply bytes_at_magree; [exact FP| exact B|]. intros a Ha. left. split.
    + exists c, A, n. split; [exact Hb| lia].
    + eapply disjoint_outside; [exact DJ| lia].
Qed.

Lemma fcall_cells_pres : forall L RNG st LB m0 (m m' : amem) W X cs,
  AHEAP AI L RNG st LB m0 -> ainblk LB X (Z.of_nat (cells_size cs)) -> disjoint_from W X (Z.of_nat (cells_size cs)) ->
  munch (W ++ fake_area L) m m' -> wmono bsegs m m' -> ffr_pres W LB m m' -> rw_cells bsegs m X cs -> rw_cells bsegs m' X cs.
Proof.
  intros L RNG st LB m0 m m' W X cs AH IB DJ MU WM FP [[Hwf HB] HW]. split; [split; [exact Hwf|]|].
  - eapply fcall_bytes_pres; [exact AH| rewrite cells_bytes_length by assumption; exact IB| rewrite cells_bytes_length by assumption; exact DJ| exact MU| exact FP| exact HB].
  - eapply wr_at_transport; [exact HW| exact WM].
Qed.

Lemma fcall_u8arr_pres : forall L RNG st LB m0 (m m' : amem) W X bs,
  AHEAP AI L RNG st LB m0 -> ainblk LB X (zlen bs) -> disjoint_from W X (zlen bs) ->
  munch (W ++ fake_area L) m m' -> wmono bsegs m m' -> ffr_pres W LB m m' -> u8arr bsegs m X bs -> u8arr bsegs m' X bs.
Proof.
  intros L RNG st LB m0 m m' W X bs AH IB DJ MU WM FP [HB HW]. split.
  - eapply fcall_bytes_pres; [exact AH| exact IB| exact DJ| exact MU| exact FP| exact HB].
  - eapply wr_at_transport; [exact HW| exact WM].
Qed.

Lemma fcall_stk_pres : forall L RNG st LB m0 (m m' : amem) W lo hi,
  AHEAP AI L RNG st LB m0 -> ainblk LB lo (hi - lo) -> disjoint_from W lo (hi - lo) ->
  munch (W ++ fake_area L) m m' -> wmono bsegs m m' -> ffr_pres W LB m m' -> stk bsegs m lo hi -> stk bsegs m' lo hi.
Proof.
  intros L RNG st LB m0 m m' W lo hi AH (b & Hb & H1 & H2) DJ MU WM FP ST.
  destruct b as [[p|c] A n]; cbn [ab_addr ab_size] in H1, H2.
  - destruct (fake_area_block AI _ _ _ _ _ p A n FHL AH Hb) as [DF _].
    eapply stk_transport_disjoint; [exact ST| exact MU| exact WM|]. apply disjoint_from_app2; [exact DJ| eapply disjoint_from_sub1; [exact DF| lia| lia]].
  - eapply stk_magree; [exact FP| exact ST|]. intros a Ha. left. split.
    + exists c, A, n. split; [exact Hb| lia].
    + eapply disjoint_outside; [exact DJ| lia].
Qed.

(* [comment removed for export] *)
Lemma fcall_unp_pres : forall L RNG st LB m0 (m m' : amem) W X k,
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
    + eapply disjoint_from_sub1; [exact DSF| |]; unfold shspan; rewrite ?shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia.
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
Lemma x1_closeZ : forall (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
    (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (m m4 : amem) (SPV DT WK wksz lo FF r : Z) (dtb' : list byte) (j0 : word)
    (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  AHEAP AI L RNG st (FB0 FF :: LB) m4 -> ablkLB LB ->
  FF mod 64 = 0 -> ablk FF (FF + 64) -> FF + 64 <= ATOP -> rng RNG FF 64 -> rng RNG (shad FF) 8 ->
  (forall b, In b LB -> FF + 64 <= ab_addr b \/ ab_addr b + ab_size b <= FF) ->
  al_fake L <= FF -> FF + 64 <= al_fake L + FAKESZ ->
  munch ([(DT, DT + HUF_DTABLE_BYTES); (WK, WK + wksz); (SPV - SW, SPV)] ++ fake_area L) m m4 ->
  wmono bsegs m m4 -> mem_inv bsegs m4 ->
  ffr_pres [(DT, DT + HUF_DTABLE_BYTES); (WK, WK + wksz)] LB m m4 ->
  rw_cells bsegs m4 (Z.shiftr FF 3 + 2147450880) X1SH ->
  rw_cells bsegs m4 FF [C8 j0] -> rw_cells bsegs m4 (FF + 56) [C8 (Z_to_bv 64 (fflag L 0 FF))] ->
  rw_cells bsegs m4 (SPV + -104) (X1SAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  rw_cells bsegs m4 (SPA1 SPV + 80) [C8 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF)] ->
  stk bsegs m4 lo (SPA1 SPV + 80) -> stk bsegs m4 (SPA1 SPV + 104) (SPV + -104) ->
  ATOP + 4096 <= lo -> lo <= SPV - HUF_TBL_STACK_A -> SPV + 16 < al_top L -> SPV mod 16 = 0 -> rng RNG lo (al_top L - lo) -> rng_aimg RNG ->
  ainblk LB DT HUF_DTABLE_BYTES -> ainblk LB WK wksz -> DT + HUF_DTABLE_BYTES <= 2^47 -> WK + wksz <= 2^47 -> 0 <= wksz ->
  u8arr bsegs m4 DT dtb' -> huf_hdr_ok dtb' -> stk bsegs m4 WK (WK + wksz) ->
  0 <= r < 2^64 ->
  (zd_is_error r = false -> huf_tbl_ok dtb' /\ exists ty, nth_error dtb' 1 = Some ty /\ (bv_unsigned ty <> 0 <-> false = true)) ->
  evtF bsegs RNG (huf_rd_postA AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV DT WK wksz lo false m)
    (MS (mkR x1 (Z_to_bv 64 (SPA1 SPV)) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPA1 SPV)) x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 (Z_to_bv 64 r) x23 x24 x25 x26 x27 x28 x29 x30 x31)
        FR (Z_to_bv 64 0x970d8) fc None m4 (seg_rom bsegs)).
Proof.
  intros L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m m4 SPV DT WK wksz lo FF r dtb' j0
         x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31
         AH4 LBH F64 FH FC RFF RSFF FFD FFA1 FFA2 MU04 WM04 MI4 FFR04 SHF4 FF04 FF564 FRB4 FRA4 STL4 STG4 BOT LO SPT SP16 RSTK RI
         IND INW DHI WHI WK0 TB4 HOK STW4 Hr RES.
  pose proof atop_range as ATR.
  pose proof (spa1_props SPV SP16) as (SPAB & SPA32 & _).
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
  { eapply (x1_epi ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV lo);
      first [exact SHF4| exact FF04| exact FF564| exact FLC| exact FRB4| exact FRA4| exact STL4| exact STG4| exact MI4
            | exact FH| exact FC| exact F64| exact GH| exact GC| exact GF| exact RFF| exact RSFF| exact RG| exact SP16| exact RI
            | eapply rng_sub'; [exact RSTK| lia]| exact Hr | unfold KEND; lia | lia]. }
  cbv beta. intros ms' (mp & m5 & x10' & x12' & -> & MU1 & WM1 & MIp & MU2 & WM2 & MI5 & ST5 & FLC5).
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
Lemma x1_got_cells : forall m, (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) ->
  rw_cells bsegs m AGOT_SUAR_R [C8 (Z_to_bv 64 0xcfd00)] /\ rw_cells bsegs m AGOT_X1PC [C8 (Z_to_bv 64 0x96138)].
Proof.
  intros m R. unfold AGOT_SUAR_R, AGOT_X1PC. split;
    (apply relro_wordA; [exact R| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity]).
Qed.

(* [comment removed for export] *)
Lemma x1_openZ : forall (k : nat) (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
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
  u8arr bsegs m DT dtb -> zlen dtb = HUF_DTABLE_BYTES -> ainblk LB DT HUF_DTABLE_BYTES -> unpoisoned m DT (DT + HUF_DTABLE_BYTES) ->
  (DT + HUF_DTABLE_BYTES <= lo \/ SPV <= DT) -> DT + HUF_DTABLE_BYTES <= 2^47 ->
  rw_cells bsegs m WK [CB (Z.to_nat wksz) jw] -> ainblk LB WK wksz -> (0 < wksz -> unpoisoned m WK (WK + wksz)) -> 4096 <= WK -> WK < 2^47 -> WK mod 4 = 0 -> 4096 <= DT ->
  (WK + wksz <= lo \/ SPV <= WK) -> WK + wksz <= 2^47 ->
  bytes_at bsegs m SRC src -> zlen src = n -> (0 < n -> ainimg LB SRC n) -> (0 < n -> unpoisoned m SRC (SRC + n)) -> 0 <= SRC ->
  (SRC + n <= lo \/ SPV <= SRC) -> SRC + n <= 2^47 ->
  (forall (FF : Z) (m3 : amem) (jA jC jD jB jE j3 j5 j6 : list byte) (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
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
     rw_cells bsegs m3 WK [CB (Z.to_nat wksz) jw] -> (0 < wksz -> unpoisoned m3 WK (WK + wksz)) ->
     bytes_at bsegs m3 SRC src -> (0 < n -> unpoisoned m3 SRC (SRC + n)) ->
     wksz < 1492 -> stk bsegs m3 lo (SPA1 SPV) ->
     Q (MS (mkR (Z_to_bv 64 0x961bc) (Z_to_bv 64 (SPA1 SPV)) gp tp y5 y6 y7 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPA1 SPV))
              y10 y11 y12 y13 y14 y15 y16 y17
              (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 wksz) (Z_to_bv 64 18446744073709551572)
              (Z_to_bv 64 n) (Z_to_bv 64 SRC) flags s10 s11 y28 y29 y30 y31)
           FR (Z_to_bv 64 0x970d8) fc None m3 (seg_rom bsegs))) ->
  (forall (FF : Z) (m3 : amem) (jA jC jD jB jE j3 j5 j6 : list byte) (y5 y6 y7 y28 y29 y30 y31 : word),
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
     rw_cells bsegs m3 WK [CB (Z.to_nat wksz) jw] -> (0 < wksz -> unpoisoned m3 WK (WK + wksz)) ->
     bytes_at bsegs m3 SRC src -> (0 < n -> unpoisoned m3 SRC (SRC + n)) ->
     1492 <= wksz -> stk bsegs m3 lo (SPA1 SPV - 16) -> rw_cells bsegs m3 (SPA1 SPV - 16) [C8 (Z_to_bv 64 876); C8 flags] ->
     Q (MS (mkR (Z_to_bv 64 0x962bc) (Z_to_bv 64 (SPA1 SPV - 16)) gp tp y5 y6 y7 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPA1 SPV))
              (Z_to_bv 64 (WK + 1236)) (Z_to_bv 64 256) (Z_to_bv 64 WK) (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 SRC) (Z_to_bv 64 n) (Z_to_bv 64 (WK + 104))
              (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (WK + 1236)) (Z_to_bv 64 18446744073709551572)
              (Z_to_bv 64 n) (Z_to_bv 64 SRC) flags (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 (FF + 48)) y28 y29 y30 y31)
           FR (Z_to_bv 64 0xab294) fc None m3 (seg_rom bsegs))) ->
  evtF bsegs RNG Q
    (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DT) (Z_to_bv 64 SRC) (Z_to_bv 64 n) (Z_to_bv 64 WK)
             (Z_to_bv 64 wksz) flags a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 APHUF_RDX1) fc None m (seg_rom bsegs)).
Proof.
  intros k L RNG st LB ra gp tp t0 t1 t2 s0 s1 flags a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m SPV DT WK wksz SRC n lo dtb src jw Q
         HK AH FLE LBH RI RSTK RFS BOT LO SPT SP16 ST MI TP WR NR
         TB LTB IND UD SDS DHI WC INW UW WKL WKH WK4 DTL SWS WHI SB LSB INS US SRC0 SSS SHI KEXIT KCALL.
  assert (WK0 : 0 <= WK) by (clear - WKL; lia).
  pose proof atop_range as ATR. unfold APHUF_RDX1.
  pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & LY4 & _).
  pose proof (spa1_props SPV SP16) as (SPAB & SPA32 & _).
  pose proof (AI_aci_img AI) as HCI. pose proof (AI_aci_lo AI) as HCI0.
  assert (LOS : lo <= SPV - 448 - 4096 - 16) by lia.
  assert (LOC : ATOP <= lo) by lia.
  assert (SPK : SPV + 16 < KEND) by (unfold KEND; lia).
  assert (DT0 : 0 <= DT) by (destruct UD as (U & _); exact U).
  (* [comment removed for export] *)
  pose proof (AI_rtcells AI _ _ _ _ _ AH) as RTC. unfold artcells in RTC.
  destruct RTC as (C0 & GOT & RIC & REAL & SHB & SUA & INI & LAY & _).
  destruct (x1_got_cells m (AI_relro AI _ _ _ _ _ AH)) as [GSU _].
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply x1_pro; first [exact ST| exact MI| exact GOT| exact SHB| exact GSU| exact SUA| exact SP16| eapply rng_sub'; [exact RSTK| lia]
            | exact RI| exact LOS | exact LOC | exact SPK]. }
  cbv beta. intros ms' (m1 & jA & jB & -> & MU1 & WM1 & MI1 & FRB1 & FRA1 & STL1 & STG1).
  clear C0 GOT RIC REAL SHB SUA INI LAY GSU.
  assert (AH1 : AHEAP AI L RNG st LB m1).
  { eapply (AI_frame AI); [exact AH| exact MU1| exact WM1|]. constructor; [| constructor]. left; left. cbn. lia. }
  (* [comment removed for export] *)
  assert (D1 : forall X n, (X + n <= lo \/ SPV <= X) -> 0 <= n -> disjoint_from [(SPV - 448, SPV)] X n).
  { intros X nn HX Hn. cbn [disjoint_from]. split; [lia| exact I]. }
  assert (DS1 : forall X n, 0 <= X -> 0 <= n -> X + n <= 2^47 ->
             disjoint_from [(SPV - 448, SPV)] (shad X) (shad (X + n - 1) + 1 - shad X)).
  { intros X nn X0 Hn Hb. cbn [disjoint_from]. split; [| exact I]. left. rewrite !shad_div. unfold ASHOFF in *.
    clear - X0 Hn Hb ATR BOT LO. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  eapply evtF_cut.
  { pose proof (SM0K k HK) as SMC. unfold stack_malloc_0k_stmt in SMC. eapply SMC with (lo := lo); clear SMC;
      rewrite ?(unsigned_lit (SPA1 SPV)) by lia;
      first [exact AH1| exact FLE| exact MI1| exact STL1| exact TP| reflexivity| exact RSTK| exact RI| exact RFS| lia| unfold SMK_STACK; lia]. }
  cbv beta. intros ms' PO.
  destruct PO as (FF & z5 & z6 & z7 & e11 & e12 & e13 & e14 & e15 & e16 & e17 & z28 & z29 & z30 & z31 & m2 & j0 & j1 & j2 & junk
                  & -> & MI2 & ST2 & HPR2 & AH2 & F64 & FH & FC & FFC2 & SHF2 & RFF & RSFF & MUF2 & WM2 & FFA1 & FFA2).
  rewrite ?(unsigned_lit (SPA1 SPV)) in ST2, HPR2, MUF2 by lia.
  rd_retlit.
  pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in FHa.
  pose proof (fk_frame_apart AI _ _ _ _ _ _ _ _ AH2) as FFD.
  pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR2 FRB1 ltac:(left; left; cbn; lia)) as FRB2.
  pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR2 FRA1 ltac:(left; left; cbn; lia)) as FRA2.
  pose proof (aheap_pres_stk _ _ _ _ _ _ _ HPR2 STG1 ltac:(lia) ltac:(lia)) as STG2.
  (* [comment removed for export] *)
  destruct (x1_got_cells m2 (AI_relro AI _ _ _ _ _ AH2)) as [_ GPC2].
  eapply x1_hdr; first [exact FRA2| exact ST2| exact FFC2| exact SHF2| exact GPC2| exact MI2| exact FH| exact FC| exact F64
                       | exact RFF| exact RSFF| exact SP16| exact RI| eapply rng_sub'; [exact RSTK| lia]
                       | exact LOS | exact LOC | exact SPK | exact WKL | exact WK4 | exact DTL | unfold HUF_DTABLE_BYTES in *; lia | idtac].
  all: intros m3 jA' jC jD jB' jE j3 j5 j6.
  1: intros y5 y10 y11 y12 y13 y14 y15 y16 y17 HW MU3 WM3 MI3 FRA3 STL3 FFC3 SHF3.
  2: intros y5 HW MU3 WM3 MI3 FRA3 STL3 ARG3 FFC3 SHF3.
  all: assert (BSF : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 8 <= 17594333495296)
    by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
  all: assert (AH3 : AHEAP AI L RNG st (FB0 FF :: LB) m3).
  1,3: eapply (AI_frame AI); [exact AH2| exact MU3| exact WM3|];
    (constructor; [cbn; left; left; lia|]);
    (constructor; [cbn; right; left; exists (FB0 FF); split; [left; reflexivity| cbn; lia]|]);
    (constructor; [cbn; right; right; right; right; exists 0, FF, 64; split; [left; reflexivity| rewrite Z.shiftr_div_pow2 by lia;
                  change (2 ^ 3) with 8; unfold ASHOFF; Z.div_mod_to_equations; lia]| constructor]).
  all: pose proof (rw_cells_transport _ _ _ _ _ _ FRB2 MU3 WM3 ltac:(cbn; lia)) as FRB3.
  all: assert (STG3 : stk bsegs m3 (SPA1 SPV + 312) (SPV + -104))
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
  1,3: eapply (fk_ffr_fin AI L RNG st LB m m2 m3 0 FF 64 (shad FF) 8 [] [(SPA1 SPV - 16, SPA1 SPV + 312); (FF, FF + 56)]);
       [exact AH2| exact LBH| exact FH| clear - F64; Z.div_mod_to_equations; lia| reflexivity| lia| lia| | constructor| exact FFR02| | exact WM3];
       [ constructor; [cbn; split; [lia| left; lia]|];
         constructor; [cbn; split; [lia| right; split; [intros b Hb; destruct (FFD b Hb); lia| exists FF, (FF+64); split; [exact FH| lia]]]| constructor]
       | eapply munch_weaken; [| exact MU3]; intros x Hx; cbn [outside app] in *; rewrite ?shad_div in *;
         rewrite ?Z.shiftr_div_pow2 in * by lia; change (2^3) with 8 in *; unfold ASHOFF in *; clear - Hx; lia ].
  (* [comment removed for export] *)
  all: destruct (FHL _ _ _ _ _ AH) as [FAB _]; pose proof (ablk_disj_band _ _ FAB) as FABD; pose proof (ablk_lin _ _ FAB) as (FABa & _).
  all: unfold AIMG_HI in FABa; unfold FAKESZ in *.
  all: set (W3 := [(SPA1 SPV - 16, SPA1 SPV + 312); (FF, FF + 56); (Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450880 + 8)]) in MU3.
  (* [comment removed for export] *)
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
  (* [comment removed for export] *)
  all: assert (TI : forall X n, 0 <= X -> X + n <= AIMG_HI -> 0 < n ->
            disjoint_from (fake_area L ++ [(SPA1 SPV - SMK_STACK, SPA1 SPV)]) X n
            /\ disjoint_from (fake_area L ++ [(SPA1 SPV - SMK_STACK, SPA1 SPV)]) (shad X) (shad (X + n - 1) + 1 - shad X)
            /\ disjoint_from W3 X n /\ disjoint_from W3 (shad X) (shad (X + n - 1) + 1 - shad X)).
  1,3: intros X nn X0 XH Hp; unfold AIMG_HI in XH; pose proof (ablk_disj_band _ _ FH) as DBF; unfold KLS in DBF, FABD;
    subst W3; cbn [disjoint_from fake_area app]; rewrite !shad_div; rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8;
    unfold ASHOFF, SMK_STACK, FAKESZ; clear - X0 XH Hp FABa FABD SPAB LO BOT FHa FHb FHc FHd F64 DBF ATR;
    repeat split; Z.div_mod_to_equations; lia.
  all: destruct (TBL DT HUF_DTABLE_BYTES IND ltac:(unfold HUF_DTABLE_BYTES in *; lia) SDS DHI) as [DN DSN].
  all: destruct (TBL WK wksz INW ltac:(lia) SWS WHI) as [DW DSW].
  all: assert (TB3 : u8arr bsegs m3 DT dtb).
  1,3: eapply u8arr_transport; [| exact MU3| exact WM3| rewrite LTB; exact DN];
    assert (ARR1 : u8arr bsegs m1 DT dtb) by (eapply u8arr_transport; [exact TB| exact MU1| exact WM1| apply D1; rewrite LTB; [exact SDS| unfold HUF_DTABLE_BYTES in *; lia]]);
    destruct ARR1 as [BA WA]; split; [eapply (fk_bytes_pres AI); [exact HPR2| rewrite LTB; exact IND| exact BA] | eapply wr_at_transport; [exact WA| exact WM2]].
  all: assert (WC3 : rw_cells bsegs m3 WK [CB (Z.to_nat wksz) jw]).
  1,3: eapply rw_cells_transport; [| exact MU3| exact WM3| cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by lia; exact DW];
    eapply (fk_cells_pres AI); [exact HPR2| cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by lia; exact INW|];
    eapply rw_cells_transport; [exact WC| exact MU1| exact WM1| apply D1; [cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by lia; exact SWS| lia]].
  all: assert (UD3 : unpoisoned m3 DT (DT + HUF_DTABLE_BYTES)).
  1,3: eapply unpoisoned_munch; [| exact MU3| apply DSN; unfold HUF_DTABLE_BYTES in *; lia];
    eapply (fk_unp_pres AI); [exact AH2| intros b Hb; right; exact Hb| exact HPR2| exact IND| unfold HUF_DTABLE_BYTES in *; lia|];
    eapply unpoisoned_munch; [exact UD| exact MU1| apply DS1; unfold HUF_DTABLE_BYTES in *; lia].
  all: assert (UW3 : 0 < wksz -> unpoisoned m3 WK (WK + wksz)).
  1,3: intros WP; eapply unpoisoned_munch; [| exact MU3| apply DSW; lia];
    eapply (fk_unp_pres AI); [exact AH2| intros b Hb; right; exact Hb| exact HPR2| exact INW| lia|];
    eapply unpoisoned_munch; [exact (UW WP)| exact MU1| apply DS1; lia].
  (* [comment removed for export] *)
  all: assert (HB3 : bytes_at bsegs m3 SRC src /\ (0 < n -> unpoisoned m3 SRC (SRC + n))).
  1,3: destruct (Z.eq_dec n 0) as [E0|NZ];
    [ rewrite E0 in *; destruct src; [| cbn [length] in LSB; lia]; split; [exact (bytes_at_nil1 _ _ _ SB)| intros; lia]
    | destruct (INS ltac:(lia)) as [IBB | [IB1 IB2]];
      [ destruct (TBL SRC n IBB ltac:(lia) SSS SHI) as [DB DSB]; split;
        [ eapply bytes_at_transport; [| exact MU3| rewrite LSB; exact DB]; eapply (fk_bytes_pres AI); [exact HPR2| rewrite LSB; exact IBB|];
          eapply bytes_at_transport; [exact SB| exact MU1| apply D1; [rewrite LSB; exact SSS| lia]]
        | intros NP; eapply unpoisoned_munch; [| exact MU3| apply DSB; lia];
          eapply (fk_unp_pres AI); [exact AH2| intros b Hb; right; exact Hb| exact HPR2| exact IBB| lia|];
          eapply unpoisoned_munch; [exact (US NP)| exact MU1| apply DS1; lia] ]
      | destruct (TI SRC n SRC0 IB2 ltac:(lia)) as (DB2 & DSB2 & DB3 & DSB3); split;
        [ eapply bytes_at_transport; [| exact MU3| rewrite LSB; exact DB3];
          eapply bytes_at_transport; [| exact MUF2| rewrite LSB; exact DB2];
          eapply bytes_at_transport; [exact SB| exact MU1| apply D1; [rewrite LSB; exact SSS| lia]]
        | intros NP; eapply unpoisoned_munch; [| exact MU3| apply DSB3];
          eapply unpoisoned_munch; [| exact MUF2| apply DSB2];
          eapply unpoisoned_munch; [exact (US NP)| exact MU1| apply DS1; lia] ] ] ].
  all: destruct HB3 as [SB3 US3].
  - eapply KEXIT; eassumption.
  - eapply KCALL; eassumption.
Qed.
End Asm.
End CANSEC1.
