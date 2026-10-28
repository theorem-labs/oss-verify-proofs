From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree FseRdKit FseRdKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase RtCells AProto AMalloc_iface AFake0k_iface AProg_kit
     AFake_arep FsKit AF_fse_rd_iface AF_fse_rd_base AF_fse_rd_mem AF_fse_rd_seg AF_fse_rd_asm AH_huf_kit AH_huf_iface
     AH_huf_rdt2 AF_huf_dec_iface AF_huf_x1t_top AF_huf_x1t_bseg.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import ZdHufStats ZdHufX1 HufPure_HufX1.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require HufHarness.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_tbl_iface AF_huf_tbl_iface3 AH_huf_iface AH_huf_rdt2 AF_huf_dec_iface
  AF_fse_rd_iface AF_fse_rd_asm AFake0k_iface AF_huf_x1t_top AF_huf_x1t_bdefs AF_huf_x1t_bpure AF_huf_x1t_bseg AF_huf_x1t_bstat
  AF_huf_x1t_benv AF_huf_x1t_bbody.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Startup_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_tbl_iface2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require AHarness_bm.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import Stdio_kit AHarness_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require AF_huf_fdw_seg AF_huf_fdw_top1.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_x1t_btop AF_huf_rstats_ok.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import HufPure_HufStats HufPure_HufStatsRT.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require FseWalkKit.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.

Lemma rwc_take : forall m A cs k, rw_cells bsegs m A cs -> rw_cells bsegs m A (firstn k cs).
Proof.
  intros m A cs k H. rewrite <- (firstn_skipn k cs) in H. exact (proj1 (proj1 (Startup_kit.rw_cells_app _ _ _ _ _) H)).
Qed.

Lemma rwc_skip : forall m A cs k, rw_cells bsegs m A cs -> rw_cells bsegs m (A + Z.of_nat (cells_size (firstn k cs))) (skipn k cs).
Proof.
  intros m A cs k H. rewrite <- (firstn_skipn k cs) in H. exact (proj2 (proj1 (Startup_kit.rw_cells_app _ _ _ _ _) H)).
Qed.

Lemma rwc_app : forall m A cs1 cs2, rw_cells bsegs m A cs1 -> rw_cells bsegs m (A + Z.of_nat (cells_size cs1)) cs2 ->
  rw_cells bsegs m A (cs1 ++ cs2).
Proof. intros m A cs1 cs2 H1 H2. apply Startup_kit.rw_cells_app. split; assumption. Qed.

Lemma rwc_u8 : forall m A cs, rw_cells bsegs m A cs -> u8arr bsegs m A (cells_bytes cs).
Proof.
  intros m A cs ((WF & BA) & WA). split; [exact BA|].
  assert (L : forall cs0, cells_wf cs0 -> length (cells_bytes cs0) = cells_size cs0).
  { induction cs0 as [|c cs0 IH]; cbn [cells_bytes cells_size cells_wf length]; [reflexivity|].
    intros (W1 & W2). rewrite app_length, (cbytes_length c W1), (IH W2). reflexivity. }
  rewrite (L cs WF). exact WA.
Qed.

Lemma x1_wr_stkB : forall m A n, wr_at bsegs m A n -> AIMG_HI <= A -> 0 <= n -> A + n <= 2^47 -> stk bsegs m A (A + n).
Proof.
  intros m A n (A0 & A1 & WR) HA N0 N1. split; [lia|]. split; [lia|].
  intros a Ha. specialize (WR (a - A) ltac:(lia)). replace (A + (a - A)) with a in WR by lia.
  pose proof WR as WR'. unfold wa in WR'.
  rewrite ref_wview_overlay in WR' by (rewrite unsigned_lit by lia; right; unfold AIMG_HI in HA; lia).
  split; [exact WR|]. unfold mrd, wa. destruct (m (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity| congruence].
Qed.

Lemma x1_bytes_map : forall (l : list byte), map (Z_to_bv 8) (map bv_unsigned l) = l.
Proof.
  intros l. rewrite map_map. erewrite map_ext; [apply map_id|]. intros b. apply FseWalkKit.byte_of_unsigned.
Qed.

Lemma x1_bytes_isbyte : forall (l : list byte), Forall (fun v : Z => 0 <= v < 256) (map bv_unsigned l).
Proof.
  intros l. apply Forall_forall. intros x Hx. apply in_map_iff in Hx as (b & <- & _).
  pose proof (bv_unsigned_in_range _ b) as R. unfold bv_modulus in R. cbn in R. lia.
Qed.

Section Asm.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Variable fflag : alayout -> Z -> Z -> Z.
Variable rng_fs : alayout -> footprint -> Prop.
Hypothesis FFLAG : fake_flag_law AI fflag.
Hypothesis FREL : fake_release_law AI fflag.
Hypothesis SM0K : stack_malloc_0k_stmt AI fflag rng_fs 0.
Notation FB0 F := (mkABlock (ABFake 0) F 64).

Lemma x1_aclB : forall LB SP SP' F a, SP' <= SP -> aclient_addr CI LB SP a -> aclient_addr CI (F :: LB) SP' a.
Proof.
  intros LB SP SP' F a HS H. unfold aclient_addr in *.
  destruct H as [H|[H|[(b & Hb & Hr)|(a' & H & ->)]]].
  - left. lia.
  - right; left; exact H.
  - right; right; left. exists b. split; [right; exact Hb| exact Hr].
  - right; right; right. exists a'. split; [|reflexivity].
    destruct H as [H|[H|(cls & A & n & Hb & Hr)]].
    + left; exact H.
    + right; left; exact H.
    + right; right. exists cls, A, n. split; [right; exact Hb| exact Hr].
Qed.

Section CMP.
Variables (L : alayout) (RNG : footprint) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word)
  (fc : bv 32) (m m3 m' : amem) (st : astate) (LB : list ablock) (SPV DT W SA flags lo FF mtl r : Z) (pdt pw : aptr)
  (src : list Z) (jdt jA jC jD jB jE j3 j5 j6 : list byte).
Hypothesis AH0 : AHEAP AI L RNG st LB m.
Hypothesis LBH : forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b).
Hypothesis HMTL : 1 <= mtl <= 12.
Hypothesis HDT : In (HB pdt DT (DTABLE_BYTES mtl)) LB.
Hypothesis DTC : rw_cells bsegs m DT [C4 (Z_to_bv 64 (mtl * 0x01000001)); CB (Z.to_nat (4 * 2^mtl)) jdt].
Hypothesis HBW : In (HB pw W 8704) LB.
Hypothesis LO1 : ATOP + 4096 <= lo.
Hypothesis LO : lo <= SPV - HUF_RDT_STACK_A2.
Hypothesis SPT : SPV + 16 < al_top L.
Hypothesis SP16 : SPV mod 16 = 0.
Hypothesis RSTK : rng RNG lo (al_top L - lo).
Hypothesis RAI : rng_aimg RNG.
Hypothesis SRCB : Forall (fun c => 0 <= c < 256) src.
Hypothesis FRM : x1_frameB AI L RNG st LB m m3 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SPV lo FF.
Hypothesis C876 : rw_cells bsegs m3 (SPA1 SPV - 16) [C8 (Z_to_bv 64 876); C8 (Z_to_bv 64 flags)].
Hypothesis FRA : rw_cells bsegs m3 (SPA1 SPV) (X1FRA FF DT W jA jC jD jB jE).
Hypothesis FFH : rw_cells bsegs m3 FF (X1FFHDR (fflag L 0 FF) j3 j5 j6 (Z_to_bv 64 0) (Z_to_bv 64 0)).
Hypothesis MI' : mem_inv bsegs m'.
Hypothesis STK' : stk bsegs m' lo (SPA1 SPV - 16).
Hypothesis MG' : magree bsegs (fun a => aclient_addr CI (FB0 FF :: LB) (SPA1 SPV - 16) a /\ ~ (W + 1236 <= a < W + 1236 + 256)
                                /\ ~ (W <= a < W + 52) /\ ~ (FF + 48 <= a < FF + 48 + 4) /\ ~ (FF + 32 <= a < FF + 32 + 4)
                                /\ ~ (W + 104 <= a < W + 104 + 876)) m3 m'.
Hypothesis AH' : AHEAP AI L RNG st (FB0 FF :: LB) m'.
Hypothesis HR : 0 <= r < 2^64.
Notation POST := (huf_rdt_postA AI huf_dt_okA L RNG ra (Z_to_bv 64 SPV) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB DT W mtl lo m).

Ltac x1szl := cbn [firstn skipn cells_size csize X1FFHDR X1FRA X1SAVED app]; lia.

Lemma x1_fftB : forall A cs, rw_cells bsegs m3 A cs -> FF <= A -> A + Z.of_nat (cells_size cs) <= FF + 64 ->
  A + Z.of_nat (cells_size cs) <= FF + 32 \/ (FF + 36 <= A /\ A + Z.of_nat (cells_size cs) <= FF + 48) \/ FF + 52 <= A ->
  rw_cells bsegs m' A cs.
Proof.
  intros A cs HC H1 H2 H3.
  destruct FRM as (F64 & FH & FC & RF & RSF & FFD & _).
  pose proof (FFD _ HBW) as FWD. cbn [ab_addr ab_size] in FWD.
  eapply rw_cells_magree; [exact MG'| exact HC|]. intros a Ha. cbv beta.
  split; [unfold aclient_addr; right; right; left; exists (FB0 FF); split; [left; reflexivity| cbn [ab_addr ab_size]; lia]|].
  lia.
Qed.

Lemma x1_m5B : magree bsegs (PAGx AI LB SPV DT mtl W) m m'
  /\ rw_cells bsegs m' (shad FF) X1SH /\ rw_cells bsegs m' FF [C8 (Z_to_bv 64 X1_MAGIC_LIVE)]
  /\ rw_cells bsegs m' (FF + 56) [C8 (Z_to_bv 64 (fflag L 0 FF))]
  /\ rw_cells bsegs m' (SPV + -104) (X1SAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
  /\ stk bsegs m' (SPA1 SPV + 216) (SPV + -104)
  /\ x1A_hyps RNG SPV (SPA1 SPV) lo DT (DTABLE_BYTES mtl) W 8704 FF
  /\ stk bsegs m' lo (SPA1 SPV) /\ rw_cells bsegs m' (SPA1 SPV) (X1FRA FF DT W jA jC jD jB jE).
Proof.
  pose proof FRM as (F64 & FH & FC & RF & RSF & FFD & AH3 & MG3 & MI3 & SV3 & SH3 & STL3 & STG3).
  pose proof (spa1_props SPV SP16) as (SPA_lo & _).
  pose proof (AI_layout AI _ _ _ _ _ AH0) as (_ & _ & ALT & _).
  pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd).
  pose proof (LBH _ HBW) as WH. cbn [ab_addr ab_size] in WH. pose proof (ablk_lin _ _ WH) as (WHa & WHb & WHc & WHd).
  pose proof (FFD _ HBW) as FWD. cbn [ab_addr ab_size] in FWD.
  assert (SPA0 : ATOP + 4096 <= SPA1 SPV - 16) by (unfold HUF_RDT_STACK_A2 in LO; lia).
  assert (LOS : lo <= SPA1 SPV - 16) by (unfold HUF_RDT_STACK_A2 in LO; lia).
  assert (TR : forall A cs, rw_cells bsegs m3 A cs -> SPA1 SPV - 16 <= A -> A + Z.of_nat (cells_size cs) <= SPV ->
            rw_cells bsegs m' A cs).
  { intros A cs HC H1 H2. eapply rw_cells_magree; [exact MG'| exact HC|]. intros a Ha. cbv beta.
    split; [unfold aclient_addr; left; lia|]. lia. }
  assert (MG5 : magree bsegs (PAGx AI LB SPV DT mtl W) m m').
  { apply magree_trans with m3.
    - eapply magree_mono; [exact MG3|]. intros a (Ha & _ & _). exact Ha.
    - eapply magree_mono; [exact MG'|]. intros a (Ha & ND & NW). cbv beta.
      assert (NF : ~ (FF <= a < FF + 64)).
      { intro HF. exact (x1b_ff_not_client AI LB SPV FF a LBH FFD F64 FH ltac:(lia) (or_introl HF) Ha). }
      split; [eapply x1_aclB; [|exact Ha]; lia|]. lia. }
  assert (C876' : rw_cells bsegs m' (SPA1 SPV - 16) [C8 (Z_to_bv 64 876); C8 (Z_to_bv 64 flags)])
    by (apply TR; [exact C876| lia| x1szl]).
  split; [exact MG5|]. split.
  { assert (SH3' : rw_cells bsegs m3 (shad FF) X1SH) by (eapply rwc_at; [exact SH3| unfold shad, ASHOFF; lia]).
    eapply rw_cells_magree; [exact MG'| exact SH3'|]. intros a Ha. cbn [cells_size csize X1SH] in Ha. cbv beta.
    set (a' := FF + 8 * (a - shad FF)).
    assert (SA8 : a = shad a')
      by (clear - Ha F64 FHb; unfold a', shad in *; rewrite !Z.shiftr_div_pow2 in * by lia; Z.div_mod_to_equations; lia).
    pose proof (x1b_shad8_disj FF W 8704 F64 FHb ltac:(lia) WH) as D1.
    pose proof (x1b_shad8_disj FF FF 64 F64 FHb ltac:(lia) FH) as D2.
    split; [|lia].
    unfold aclient_addr. right; right; right. exists a'. split; [|exact SA8]. right; right. exists 0, FF, 64.
    split; [left; reflexivity| unfold a'; lia]. }
  split; [apply x1_fftB; [exact (rwc_hd _ _ _ _ FFH)| lia| x1szl| left; x1szl]|].
  split.
  { eapply rwc_at; [apply x1_fftB; [exact (rwc_skip _ _ _ 8 FFH)| x1szl| x1szl| right; right; x1szl]| x1szl]. }
  split; [apply TR; [exact SV3| lia| x1szl]|].
  split; [eapply stk_magree; [exact MG'| exact STG3|]; intros a Ha; cbv beta; split; [unfold aclient_addr; left; lia| lia]|].
  split; [eapply (x1_hyB AI L RNG st LB m SPV DT W mtl lo FF pdt pw); eassumption|].
  split; [eapply stk_cells; [exact STK'| exact C876'| x1szl| lia]|].
  apply TR; [exact FRA| lia| x1szl].
Qed.

Lemma x1_ffhB : forall tw nw, rw_cells bsegs m' (FF + 32) [C4 tw] -> rw_cells bsegs m' (FF + 48) [C4 nw] ->
  rw_cells bsegs m' FF (X1FFHDR (fflag L 0 FF) j3 j5 j6 tw nw).
Proof.
  intros tw nw TW NW.
  change (rw_cells bsegs m' FF (firstn 4 (X1FFHDR (fflag L 0 FF) j3 j5 j6 (Z_to_bv 64 0) (Z_to_bv 64 0)) ++ [C4 tw]
            ++ firstn 1 (skipn 5 (X1FFHDR (fflag L 0 FF) j3 j5 j6 (Z_to_bv 64 0) (Z_to_bv 64 0))) ++ [C4 nw]
            ++ skipn 7 (X1FFHDR (fflag L 0 FF) j3 j5 j6 (Z_to_bv 64 0) (Z_to_bv 64 0)))).
  apply rwc_app; [apply x1_fftB; [exact (rwc_take _ _ _ 4 FFH)| lia| x1szl| left; x1szl]|].
  apply rwc_app; [eapply rwc_at; [exact TW| x1szl]|].
  apply rwc_app; [eapply rwc_at; [apply x1_fftB; [exact (rwc_take _ _ _ 1 (rwc_skip _ _ _ 5 FFH))| x1szl| x1szl| right; left; x1szl]| x1szl]|].
  apply rwc_app; [eapply rwc_at; [exact NW| x1szl]|].
  eapply rwc_at; [apply x1_fftB; [exact (rwc_skip _ _ _ 7 FFH)| x1szl| x1szl| right; right; x1szl]| x1szl].
Qed.

Lemma x1_errB : 2^64 - 120 < r ->
  forall (xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x19 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  evtF bsegs RNG POST (MS (mkR xra (Z_to_bv 64 (SPA1 SPV)) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPA1 SPV))
                              xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 FF) x19 x20 x21 (Z_to_bv 64 r) x23 x24 x25 x26 x27
                              x28 x29 x30 x31)
                          FR (Z_to_bv 64 0x80618) fc None m' (seg_rom bsegs)).
Proof.
  intros HE xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x19 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31.
  pose proof x1_m5B as (MG5 & SH5 & FF05 & FF565 & SV5 & STG5 & HY & STKA & FRA5).
  pose proof FRM as (F64 & FH & FC & RF & RSF & FFD & _).
  assert (KERR : x1_kerrX RNG gp tp FR fc m' SPV (SPA1 SPV) lo DT (DTABLE_BYTES mtl) W 8704 FF POST)
    by (eapply x1_kerrB; eassumption).
  eapply KERR; [lia| exact MI'| apply munch_refl| apply wmono_refl| exact STKA| exact FRA5].
Qed.

Lemma x1_okB : forall (h : hstats) (jrest : list byte),
  read_stats src = Ok h -> r = hs_ret h ->
  u8arr bsegs m' (W + 1236) (map (Z_to_bv 8) (hs_weights h) ++ jrest) -> zlen jrest = 256 - hs_nbSymbols h ->
  u32arr bsegs m' W (map (Z_to_bv 64) (hs_rank h)) ->
  rw_cells bsegs m' (FF + 48) [C4 (Z_to_bv 64 (hs_nbSymbols h))] ->
  rw_cells bsegs m' (FF + 32) [C4 (Z_to_bv 64 (hs_tableLog h))] ->
  forall (x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31 : word),
  evtF bsegs RNG POST (MS (mkR (Z_to_bv 64 0x80454) (Z_to_bv 64 (SPA1 SPV)) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPA1 SPV))
                              xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 FF) (Z_to_bv 64 2147450880) (Z_to_bv 64 r)
                              (Z_to_bv 64 (W + 1236)) (Z_to_bv 64 18446744073709551572) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 (zlen src))
                              (Z_to_bv 64 SA) (Z_to_bv 64 flags) (Z_to_bv 64 (FF + 48)) x28 x29 x30 x31)
                          FR (Z_to_bv 64 0x80464) fc None m' (seg_rom bsegs)).
Proof.
  intros h jrest RSE RR HWA ZJR RKA NBC TLC x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31.
  pose proof x1_m5B as (MG5 & SH5 & FF05 & FF565 & SV5 & STG5 & HY & STKA & FRA5).
  pose proof FRM as (F64 & FH & FC & RF & RSF & FFD & AH3 & MG3 & _).
  pose proof (read_stats_okB src h SRCB RSE) as (HSO & NBL).
  pose proof (read_stats_ret src h (all_bytes_of_Forall src SRCB) RSE) as RRET.
  pose proof HSO as (TLR & NBR & WSB & RKL & _).
  unfold FseNCount.Zlength in NBR, RKL.
  assert (HR32 : 0 <= r < 2^32) by lia.
  assert (NBS : 2 <= hs_nbSymbols h <= 256) by lia.
  (* [comment removed for export] *)
  pose proof (AI_block AI _ _ _ _ _ _ _ _ AH' (in_cons _ _ _ HDT)) as (_ & (DR1 & DR2 & DR3 & DR4) & _ & _ & DSDW & DWR & _).
  pose proof (AI_block AI _ _ _ _ _ _ _ _ AH' (in_cons _ _ _ HBW)) as (_ & (WR1 & WR2 & WR3 & WR4) & _ & _ & WSDW & WWR & _).
  pose proof (ablk_lin _ _ DR1) as (DLa & DLb & DLc & DLd).
  pose proof (ablk_lin _ _ WR1) as (WLa & WLb & WLc & WLd).
  pose proof (Z.pow_pos_nonneg 2 mtl ltac:(lia) ltac:(lia)) as P2.
  assert (DTBE : DTABLE_BYTES mtl = 4 + 4 * 2 ^ mtl) by (unfold DTABLE_BYTES, HufHarness.DT_BYTES; lia).
  pose proof (ablock_unpoisoned m' DT (DTABLE_BYTES mtl) DSDW ltac:(clear - DR4; Z.div_mod_to_equations; lia) ltac:(lia) ltac:(lia) ltac:(lia)) as UDT.
  pose proof (ablock_unpoisoned m' W 8704 WSDW ltac:(clear - WR4; Z.div_mod_to_equations; lia) ltac:(lia) ltac:(lia) ltac:(lia)) as UW.
  pose proof (AI_rtcells AI _ _ _ _ _ AH') as ART0.
  pose proof (x1_wr_stkB m' W 8704 WWR WLa ltac:(lia) ltac:(lia)) as WSTK.
  destruct (stk_split bsegs m' W (W + 52) (W + 8704) WSTK ltac:(lia)) as (_ & WSTK1).
  destruct (stk_split bsegs m' (W + 52) (W + 1236) (W + 8704) WSTK1 ltac:(lia)) as (WS1 & WSTK2).
  destruct (stk_split bsegs m' (W + 1236) (W + 1492) (W + 8704) WSTK2 ltac:(lia)) as (_ & WS2).
  (* [comment removed for export] *)
  assert (DTN : HB pdt DT (DTABLE_BYTES mtl) <> HB pw W 8704).
  { intro E. apply (f_equal ab_size) in E. cbn [ab_size] in E. rewrite DTBE in E.
    assert (P2E : 2 ^ mtl = 2 * 2 ^ (mtl - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
    pose proof (Z.pow_pos_nonneg 2 (mtl - 1) ltac:(lia) ltac:(lia)). lia. }
  pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH0 HDT HBW DTN) as DWD. cbn [ab_addr ab_size] in DWD.
  pose proof (FFD _ HDT) as FDD. cbn [ab_addr ab_size] in FDD.
  assert (DTSZ : Z.of_nat (cells_size [C4 (Z_to_bv 64 (mtl * 0x01000001)); CB (Z.to_nat (4 * 2^mtl)) jdt]) = DTABLE_BYTES mtl).
  { cbn [cells_size csize]. lia. }
  assert (DTC' : rw_cells bsegs m' DT [C4 (Z_to_bv 64 (mtl * 0x01000001)); CB (Z.to_nat (4 * 2^mtl)) jdt]).
  { eapply rw_cells_magree; [exact MG'| eapply rw_cells_magree; [exact MG3| exact DTC|]|].
    - intros a Ha. rewrite DTSZ in Ha. unfold aclient_addr. right; right; left. exists (HB pdt DT (DTABLE_BYTES mtl)).
      split; [exact HDT| cbn [ab_addr ab_size]; lia].
    - intros a Ha. rewrite DTSZ in Ha. cbv beta. split; [|lia].
      unfold aclient_addr. right; right; left. exists (HB pdt DT (DTABLE_BYTES mtl)).
      split; [right; exact HDT| cbn [ab_addr ab_size]; lia]. }
  pose proof DTC' as ((DWF & _) & _). cbn [cells_wf cell_wf] in DWF. destruct DWF as (_ & LJ & _).
  set (dt := zle4 (mtl * 0x01000001) ++ map bv_unsigned jdt).
  assert (DTE : map (Z_to_bv 8) dt = cells_bytes [C4 (Z_to_bv 64 (mtl * 0x01000001)); CB (Z.to_nat (4 * 2^mtl)) jdt]).
  { unfold dt. rewrite map_app, x1_bytes_map. cbn [cells_bytes cbytes]. rewrite app_nil_r.
    rewrite (le4_Z (mtl * 0x01000001) (mtl * 0x01000001) eq_refl). reflexivity. }
  assert (DTU : u8arr bsegs m' DT (map (Z_to_bv 8) dt)) by (rewrite DTE; exact (rwc_u8 _ _ _ DTC')).
  assert (DTL : zlen dt = DTABLE_BYTES mtl).
  { change (zlen dt) with (Z.of_nat (length dt)). unfold dt. rewrite app_length, map_length, LJ.
    change (length (zle4 (mtl * 0x01000001))) with 4%nat. lia. }
  assert (DTB : Forall (fun v : Z => 0 <= v < 256) dt).
  { unfold dt. apply Forall_app. split; [|apply x1_bytes_isbyte].
    unfold zle4. repeat (apply Forall_cons; [apply Z.mod_pos_bound; lia|]). apply Forall_nil. }
  assert (DT0 : Znth 0 dt = mtl).
  { change (Znth 0 dt) with ((mtl * 0x01000001) mod 256). clear - HMTL. Z.div_mod_to_equations. lia. }
  assert (DT3 : Znth 3 dt = mtl).
  { change (Znth 3 dt) with (((mtl * 0x01000001) / 16777216) mod 256). clear - HMTL. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  set (hw := hs_weights h ++ map bv_unsigned jrest).
  assert (HWU : u8arr bsegs m' (W + 1236) (map (Z_to_bv 8) hw)) by (unfold hw; rewrite map_app, x1_bytes_map; exact HWA).
  assert (HWL : zlen hw = 256).
  { change (zlen hw) with (Z.of_nat (length hw)). change (zlen jrest) with (Z.of_nat (length jrest)) in ZJR.
    unfold hw. rewrite app_length, map_length. lia. }
  assert (HWB : Forall (fun v : Z => 0 <= v < 256) hw).
  { unfold hw. apply Forall_app. split; [|apply x1_bytes_isbyte].
    eapply Forall_impl; [|exact WSB]. intros w Hw. cbv beta in Hw |- *. lia. }
  assert (HWF : firstn (Z.to_nat (hs_nbSymbols h)) hw = hs_weights h).
  { unfold hw. rewrite firstn_app. replace (Z.to_nat (hs_nbSymbols h) - length (hs_weights h))%nat with 0%nat by lia.
    rewrite firstn_O, app_nil_r. apply firstn_all2. lia. }
  assert (HSO' : huf_stats_ok (firstn (Z.to_nat (hs_nbSymbols h)) hw) (hs_rank h) (hs_tableLog h)) by (rewrite HWF; exact HSO).
  assert (RKL' : zlen (hs_rank h) = 13) by (change (zlen (hs_rank h)) with (Z.of_nat (length (hs_rank h))); lia).
  assert (FFC : rw_cells bsegs m' FF (X1FFHDR (fflag L 0 FF) j3 j5 j6 (Z_to_bv 64 (hs_tableLog h)) (Z_to_bv 64 (hs_nbSymbols h))))
    by (apply x1_ffhB; assumption).
  assert (DTB2 : 4 + 2 * 2 ^ (mtl + 1) <= DTABLE_BYTES mtl) by (rewrite Z.pow_add_r by lia; lia).
  assert (KERR : x1_kerrX RNG gp tp FR fc m' SPV (SPA1 SPV) lo DT (DTABLE_BYTES mtl) W 8704 FF POST)
    by (eapply x1_kerrB; eassumption).
  assert (KEND : x1_kendX RNG gp tp FR fc m' SPV (SPA1 SPV) lo DT (DTABLE_BYTES mtl) W 8704 FF r POST mtl)
    by (eapply x1_kendB; try eassumption; lia).
  pose proof (x1_fillX_ok RNG gp tp FR fc m' SPV (SPA1 SPV) lo DT (DTABLE_BYTES mtl) W 8704 FF r HY UDT UW ART0 HR32 POST
                (zlen src) SA (Z_to_bv 64 flags) mtl KEND) as FILLX.
  eapply (x1_bodyA RNG gp tp FR fc m' SPV (SPA1 SPV) lo DT (DTABLE_BYTES mtl) W 8704 FF r HY UDT UW ART0 HR32 POST
            (zlen src) SA (Z_to_bv 64 flags) mtl HMTL DTB2 KEND KERR FILLX hw (hs_rank h) (hs_nbSymbols h) (hs_tableLog h) dt
            (fflag L 0 FF) jA jC jD jB jE j3 j5 j6); eassumption.
Qed.

End CMP.

Hypothesis RSB : x1_rsB_stmt AI fflag rng_fs.

Theorem x1_topB : huf_rdt_stmtA2 AI rng_fs huf_dt_okA AHUF_RDT_X1.
Proof using FFLAG FREL SM0K RSB.
  unfold huf_rdt_stmtA2.
  intros L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m st LB
    DT W SA mtl flags pdt pw src jdt lo rstk
    AH NOF LBH HMTL HDT DTC HBW SRCB0 SRCF SRCL S16 SRCIN DDT DW STK LO1 LO RCL RLO RHI RRLO SPT SP16 MI TPE FLG HINVA
    HBM HCI RSTK RAI RAIS RFS RRNG E0 E1 E2 E3 E4 E5.
  subst a0 a1 a2 a3 a4 a5.
  rewrite <- (Z_to_bv_bv_unsigned sp).
  set (SPV := bv_unsigned sp) in *.
  pose proof (AI_block AI _ _ _ _ _ _ _ _ AH HBW) as (_ & (WR1 & WR2 & _ & WR4) & _).
  pose proof (AI_block AI _ _ _ _ _ _ _ _ AH HDT) as (_ & (DR1 & DR2 & _ & DR4) & _).
  pose proof (ablk_lin _ _ WR1) as (WLa & WLb & WLc & WLd).
  pose proof (ablk_lin _ _ DR1) as (DLa & DLb & DLc & DLd).
  assert (AIMG4 : 4096 <= AIMG_HI) by (unfold AIMG_HI; lia).
  pose proof (AI_layout AI _ _ _ _ _ AH) as (_ & _ & ALT & _).
  pose proof (spa1_props SPV SP16) as (SPA_lo & _).
  eapply x1_openB; try eassumption; try (clear - WR4 DR2 WLa WLd DLa DLd AIMG4; Z.div_mod_to_equations; lia).
  intros FF m3 jA jC jD jB jE j3 j5 j6 y6 y7 y28 y29 y30 y31 FRM C876 FRA FFH.
  eapply RSB; try eassumption.
  intros ms' PS.
  destruct PS as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & r & m' & -> & MI' & STK' & MG' & AH'
                  & HR & RS).
  rewrite ret_pc_even by (try reflexivity; lia).
  eapply x1_statB; [unfold HUF_RDT_STACK_A2 in LO; lia| exact HR| |].
  - intros HE. eapply x1_errB; eassumption.
  - intros HO. destruct (read_stats src) eqn:RSE; try contradiction.
    all: try (destruct RS as (RE & RB); lia).
    destruct RS as (RR & (jrest & HWA & ZJR) & RKA & NBC & TLC).
    eapply x1_okB; eassumption.
Qed.
End Asm.
End CANSEC1.
