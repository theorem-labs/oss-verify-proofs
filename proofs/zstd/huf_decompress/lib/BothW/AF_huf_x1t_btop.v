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

Fixpoint x1_pairs (l : list Z) : list deltX1 :=
  match l with a :: b :: r => mkX1 a b :: x1_pairs r | _ => [] end.

Lemma x1_pairs_bytes : forall n l, length l = (2 * n)%nat -> x1_bytes (x1_pairs l) = map (Z_to_bv 8) l.
Proof.
  induction n as [|n IH]; intros l HL.
  - destruct l; [reflexivity| cbn in HL; lia].
  - destruct l as [|a [|b r]]; cbn [length] in HL; try lia.
    unfold x1_bytes in *. cbn [x1_pairs map concat app x1_nbBits x1_byte]. rewrite (IH r) by lia. reflexivity.
Qed.

Lemma x1_pairs_length : forall n l, length l = (2 * n)%nat -> length (x1_pairs l) = n.
Proof.
  induction n as [|n IH]; intros l HL.
  - destruct l; [reflexivity| cbn in HL; lia].
  - destruct l as [|a [|b r]]; cbn [length] in HL; try lia. cbn [x1_pairs length]. rewrite (IH r) by lia. reflexivity.
Qed.

Lemma x1_pairs_nth : forall n l i, length l = (2 * n)%nat -> (i < n)%nat ->
  nth i (x1_pairs l) x1_default = mkX1 (nth (2 * i) l 0) (nth (S (2 * i)) l 0).
Proof.
  induction n as [|n IH]; intros l i HL Hi; [lia|].
  destruct l as [|a [|b r]]; cbn [length] in HL; try lia.
  destruct i as [|i]; [reflexivity|]. cbn [x1_pairs nth]. rewrite (IH r i) by lia.
  replace (2 * S i)%nat with (S (S (2 * i))) by lia. reflexivity.
Qed.

Section CANSEC1. Context {rc : runConstT}.

Lemma x1_dt_okB : forall m DT mtl tl dt, 1 <= mtl <= 12 -> 1 <= tl <= mtl + 1 -> tl <= 12 ->
  x1pref mtl tl (2 ^ tl) dt -> zlen dt = DTABLE_BYTES mtl -> Forall isbyte dt ->
  u8arr bsegs m DT (map (Z_to_bv 8) dt) -> huf_dt_okA m DT mtl.
Proof.
  intros m DT mtl tl dt HM HT T12 (P0 & P1 & P2 & P3 & PC) HL HB HU.
  unfold DTABLE_BYTES, HufHarness.DT_BYTES in HL.
  assert (P2M : 2 ^ (mtl + 1) = 2 * 2 ^ mtl) by (rewrite Z.pow_add_r by lia; lia).
  assert (P2T : 2 ^ tl <= 2 ^ (mtl + 1)) by (apply Z.pow_le_mono_r; lia).
  assert (P2P : 0 < 2 ^ tl) by (apply Z.pow_pos_nonneg; lia).
  assert (P2Q : 0 < 2 ^ mtl) by (apply Z.pow_pos_nonneg; lia).
  destruct dt as [|d0 [|d1 [|d2 [|d3 r]]]]; cbn [length] in HL; try lia.
  unfold Znth in P0, P1, P2, P3. change (Z.to_nat 0) with 0%nat in P0. change (Z.to_nat 1) with 1%nat in P1.
  change (Z.to_nat 2) with 2%nat in P2. change (Z.to_nat 3) with 3%nat in P3. cbn [nth] in P0, P1, P2, P3. subst d0 d1 d2 d3.
  set (n := Z.to_nat (2 ^ (mtl + 1))).
  assert (HR : length r = (2 * n)%nat) by (unfold n; lia).
  destruct HU as [HB0 _].
  destruct (proj1 (bytes_at_app bsegs m DT [Z_to_bv 8 mtl; Z_to_bv 8 0; Z_to_bv 8 tl; Z_to_bv 8 mtl] (map (Z_to_bv 8) r)) HB0)
    as [H4 HR4].
  change (Z.of_nat (length [Z_to_bv 8 mtl; Z_to_bv 8 0; Z_to_bv 8 tl; Z_to_bv 8 mtl])) with 4 in HR4.
  rewrite <- (firstn_skipn (Z.to_nat (2 * 2 ^ tl)) (map (Z_to_bv 8) r)) in HR4.
  destruct (proj1 (bytes_at_app bsegs m (DT + 4) _ _) HR4) as [HT4 _].
  exists 0, tl. split.
  - exact H4.
  - left. split; [reflexivity|]. exists (x1_pairs r).
    split; [rewrite (x1_pairs_length n r HR); unfold n; lia|].
    split.
    + unfold x1_table_ok, HUF_TABLELOG_MAX. split; [lia|]. split.
      { unfold FseNCount.Zlength. rewrite (x1_pairs_length n r HR). unfold n. lia. }
      intros i Hi. rewrite (x1_pairs_nth n r (Z.to_nat i) HR) by (unfold n; lia).
      unfold x1_cell_ok. cbn [x1_nbBits x1_byte]. split.
      * pose proof (PC i Hi) as B. unfold Znth in B.
        replace (Z.to_nat (4 + 2 * i)) with (S (S (S (S (2 * Z.to_nat i))))) in B by lia. cbn [nth] in B. exact B.
      * apply Forall_inv_tail, Forall_inv_tail, Forall_inv_tail, Forall_inv_tail in HB.
        apply (Forall_nth (fun v : Z => 0 <= v < 256) r) with (i := S (2 * Z.to_nat i)) (d := 0) in HB; [exact HB| lia].
    + split; [lia|]. rewrite (x1_pairs_bytes n r HR). exact HT4.
Qed.

Lemma rwc_at : forall m A A' cs, rw_cells bsegs m A cs -> A = A' -> rw_cells bsegs m A' cs.
Proof. intros m A A' cs H E. subst A'. exact H. Qed.

Lemma rwc_tl : forall m A c cs, rw_cells bsegs m A (c :: cs) -> rw_cells bsegs m (A + Z.of_nat (cells_size [c])) cs.
Proof. intros m A c cs H. exact (proj2 (proj1 (Startup_kit.rw_cells_app bsegs m A [c] cs) H)). Qed.

Lemma rwc_hd : forall m A c cs, rw_cells bsegs m A (c :: cs) -> rw_cells bsegs m A [c].
Proof. intros m A c cs H. exact (proj1 (proj1 (Startup_kit.rw_cells_app bsegs m A [c] cs) H)). Qed.

Lemma rwc_hd2 : forall m A c1 c2 cs, rw_cells bsegs m A (c1 :: c2 :: cs) -> rw_cells bsegs m A [c1; c2].
Proof. intros m A c1 c2 cs H. exact (proj1 (proj1 (Startup_kit.rw_cells_app bsegs m A [c1; c2] cs) H)). Qed.

Lemma rwc_hd3 : forall m A c1 c2 c3 cs, rw_cells bsegs m A (c1 :: c2 :: c3 :: cs) -> rw_cells bsegs m A [c1; c2; c3].
Proof. intros m A c1 c2 c3 cs H. exact (proj1 (proj1 (Startup_kit.rw_cells_app bsegs m A [c1; c2; c3] cs) H)). Qed.

Lemma stk_cells : forall m lo A cs hi, stk bsegs m lo A -> rw_cells bsegs m A cs -> hi = A + Z.of_nat (cells_size cs) ->
  lo <= A -> stk bsegs m lo hi.
Proof.
  intros m lo A cs hi S1 H E LA. subst hi. eapply stk_merge; [exact S1| exact (stk_of_rw_cells bsegs m A cs H)| lia].
Qed.

Lemma stk_at : forall m a b a' b', stk bsegs m a b -> a = a' -> b = b' -> stk bsegs m a' b'.
Proof. intros m a b a' b' H E1 E2. subst. exact H. Qed.

Section Asm.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Variable fflag : alayout -> Z -> Z -> Z.
Variable rng_fs : alayout -> footprint -> Prop.
Hypothesis FFLAG : fake_flag_law AI fflag.
Hypothesis FREL : fake_release_law AI fflag.
Hypothesis SM0K : stack_malloc_0k_stmt AI fflag rng_fs 0.
Notation FB0 F := (mkABlock (ABFake 0) F 64).

Lemma x1_hyB : forall (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock) (m : amem) (SPV DT W mtl lo FF : Z)
    (pdt pw : aptr),
  AHEAP AI L RNG st LB m -> 1 <= mtl <= 12 -> In (HB pdt DT (DTABLE_BYTES mtl)) LB -> In (HB pw W 8704) LB ->
  ATOP + 4096 <= lo -> lo <= SPV - HUF_RDT_STACK_A2 -> SPV + 16 < al_top L -> SPV mod 16 = 0 ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG ->
  FF mod 64 = 0 -> ablk FF (FF + 64) -> FF + 64 <= ATOP -> rng RNG FF 64 ->
  (forall b, In b LB -> FF + 64 <= ab_addr b \/ ab_addr b + ab_size b <= FF) ->
  x1A_hyps RNG SPV (SPA1 SPV) lo DT (DTABLE_BYTES mtl) W 8704 FF.
Proof.
  intros L RNG st LB m SPV DT W mtl lo FF pdt pw AH HMTL HDT HBW BOT LO SPT SP16 RSTK RI F64 FH FC RF FFD.
  pose proof atop_range as ATR.
  pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & _).
  pose proof (spa1_props SPV SP16) as (SPAB & SPA32 & _).
  pose proof (ablk_lin _ _ FH) as (FH1 & FH2 & FH3 & FH4).
  destruct (AI_block AI _ _ _ _ _ _ _ _ AH HDT) as (NBD & (BLD & _ & TOPD & D16) & RD & RSD & _).
  destruct (AI_block AI _ _ _ _ _ _ _ _ AH HBW) as (NBW & (BLW & _ & TOPW & W16) & RW & RSW & _).
  pose proof (ablk_lin _ _ BLD) as (D1 & D2 & D3 & D4).
  pose proof (ablk_lin _ _ BLW) as (W1 & W2 & W3 & W4).
  assert (NE : HB pdt DT (DTABLE_BYTES mtl) <> HB pw W 8704).
  { intros E. apply (f_equal ab_size) in E. cbn in E. unfold DTABLE_BYTES, HufHarness.DT_BYTES in E.
    replace mtl with (Z.succ (mtl - 1)) in E by lia. rewrite Z.pow_succ_r in E by lia. lia. }
  assert (DWD : DT + DTABLE_BYTES mtl <= W \/ W + 8704 <= DT).
  { destruct (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH HDT HBW NE) as [X|X]; cbn in X; lia. }
  pose proof (FFD _ HDT) as FD. pose proof (FFD _ HBW) as FW. cbn in FD, FW.
  assert (SPN : forall A n, A mod 16 = 0 -> 0 <= n -> shspan A n = shlen (n + 7)).
  { intros A n HA Hn. unfold shspan, shlen. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    Z.div_mod_to_equations. lia. }
  unfold x1A_hyps, HUF_RDT_STACK_A2 in *.
  repeat match goal with |- _ /\ _ => split end.
  all: first [assumption | lia | (rewrite SPN by lia; assumption) | (eapply rng_sub'; [exact RSTK| lia])
             | (unfold AIMG_HI, KHIGH in *; lia)].
Qed.

Lemma u8arr_stkB : forall m A bs, u8arr bsegs m A bs -> stk bsegs m A (A + Z.of_nat (length bs)).
Proof.
  intros m A bs [(HA0 & HA1 & HB) (_ & _ & HW)]. split; [lia|]. split; [lia|].
  intros a Ha. split.
  - replace a with (A + (a - A)) by lia. apply HW. lia.
  - pose proof (HB (Z.to_nat (a - A)) ltac:(lia)) as E. rewrite Z2Nat.id in E by lia.
    replace (A + (a - A)) with a in E by lia.
    destruct (nth_error bs (Z.to_nat (a - A))) as [b|] eqn:N; [exists b; exact E|].
    apply nth_error_None in N. lia.
Qed.

Lemma x1_zmaskB : forall m, AHarness_bm.hinv_bm m -> zshadow m ABIT_MASK 128.
Proof.
  intros m H a Ha. apply (AHarness_bm.hinv_bm_zero m a H). unfold ABIT_MASK, AHarness_bm.AHBM_LO, AHarness_bm.AHBM_HI in *. lia.
Qed.

Lemma x1_mask_ciB : forall CI : list (Z * Z), (forall a, AHarness_bm.AHBM_LO <= a < AHarness_bm.AHBM_HI -> in_ranges CI a) ->
  forall a, ABIT_MASK <= a < ABIT_MASK + 128 -> in_ranges CI a.
Proof.
  intros CI H a Ha. apply H. unfold ABIT_MASK, AHarness_bm.AHBM_LO, AHarness_bm.AHBM_HI in *. lia.
Qed.

Lemma x1_u8wB : forall m A n X k, wr_at bsegs m A n -> AIMG_HI <= A -> A <= X -> X + k <= A + n -> 0 <= k ->
  exists bs, u8arr bsegs m X bs /\ zlen bs = k.
Proof.
  intros m A n X k WR LO AX XK K0.
  assert (WX : wr_at bsegs m X k) by (eapply AProg_kit.wr_at_sub; [exact WR | lia..]).
  assert (NI : no_image bsegs X (X + k)) by (apply no_image_asan; unfold AIMG_HI in *; lia).
  destruct (rw_cells_of_wr_at bsegs m X k WX NI K0) as (bs & BL & RC).
  exists bs. split; [exact (u8arr_of_rw_cells bsegs _ _ _ _ RC)|]. rewrite BL, Z2Nat.id by lia. reflexivity.
Qed.

Definition x1_rsB_stmt : Prop := forall (L : alayout) (RNG : footprint) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m m3 : amem) (st : astate) (LB : list ablock) (SPV DT W S flags lo FF : Z)
    (pw : aptr) (src : list Z) (rstk : region) (y6 y7 y28 y29 y30 y31 : word) (jA jC jD jB jE j3 j5 j6 : list byte)
    (Q : machine_state -> Prop),
  x1_frameB AI L RNG st LB m m3 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SPV lo FF ->
  rw_cells bsegs m3 (SPA1 SPV - 16) [C8 (Z_to_bv 64 876); C8 (Z_to_bv 64 flags)] ->
  rw_cells bsegs m3 (SPA1 SPV) (X1FRA FF DT W jA jC jD jB jE) ->
  rw_cells bsegs m3 FF (X1FFHDR (fflag L 0 FF) j3 j5 j6 (Z_to_bv 64 0) (Z_to_bv 64 0)) ->
  (forall F k, ~ In (mkABlock (ABFake 0) F k) LB) ->
  (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) -> In (HB pw W 8704) LB ->
  bytes_at bsegs m S (map (Z_to_bv 8) src) -> Forall (fun c => 0 <= c < 256) src -> zlen src < 2^26 -> 16 <= S ->
  src_inA LB S src -> (W + 8704 <= S \/ S + zlen src <= W) ->
  ATOP + 4096 <= lo -> lo <= SPV - HUF_RDT_STACK_A2 -> SPV + 16 < al_top L -> SPV mod 16 = 0 ->
  rclean m rstk -> r_lo rstk <= lo -> SPV <= r_hi rstk -> ATOP <= r_rlo rstk -> tp = Z_to_bv 64 ATP ->
  AHarness_bm.hinv_bm m -> (forall a, AHarness_bm.AHBM_LO <= a < AHarness_bm.AHBM_HI -> in_ranges CI a) ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_fs L RNG -> rrng RNG rstk ->
  (forall ms', huf_rstats_postA AI L RNG (Z_to_bv 64 0x80454) gp tp (Z_to_bv 64 SPV) (Z_to_bv 64 (SPA1 SPV)) (Z_to_bv 64 FF)
                 (Z_to_bv 64 2147450880) s4 (Z_to_bv 64 (W + 1236)) (Z_to_bv 64 18446744073709551572) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 (zlen src))
                 (Z_to_bv 64 S) (Z_to_bv 64 flags) (Z_to_bv 64 (FF + 48)) FR fc st (FB0 FF :: LB)
                 (SPA1 SPV - 16) (W + 1236) W (FF + 48) (FF + 32) (W + 104) src lo m3 ms' ->
               evtF bsegs RNG Q ms') ->
  evtF bsegs RNG Q
       (MS (mkR (Z_to_bv 64 0x80454) (Z_to_bv 64 (SPA1 SPV - 16)) gp tp (Z_to_bv 64 FF) y6 y7 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPA1 SPV))
                (Z_to_bv 64 (W + 1236)) (Z_to_bv 64 256) (Z_to_bv 64 W) (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 (FF + 32))
                (Z_to_bv 64 S) (Z_to_bv 64 (zlen src)) (Z_to_bv 64 (W + 104))
                (Z_to_bv 64 FF) (Z_to_bv 64 2147450880) s4 (Z_to_bv 64 (W + 1236)) (Z_to_bv 64 18446744073709551572)
                (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 (zlen src)) (Z_to_bv 64 S) (Z_to_bv 64 flags) (Z_to_bv 64 (FF + 48)) y28 y29 y30 y31)
           FR (Z_to_bv 64 0x9733c) fc None m3 (seg_rom bsegs)).

Lemma x1_rsB : huf_rstats_stmtA AI rng_fs 1 -> x1_rsB_stmt.
Proof.
  intros RSK. unfold x1_rsB_stmt.
  intros L RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m m3 st LB SPV DT W S flags lo FF pw src rstk
    y6 y7 y28 y29 y30 y31 jA jC jD jB jE j3 j5 j6 Q FRM HSF HFRA HFF NOF LBH HBW BS SRCB SRCL S16 SRCA SWD BOT LO SPT SP16
    RCL RLO RHI RRLO TP HINV HCI RLOW RAI RAISH RFS RRS K.
  unfold x1_frameB in FRM.
  destruct FRM as (F64 & FH & FC & RF & RSF & FFD & AH3 & MG & MI3 & SV3 & SH3 & STK1 & STK2).
  pose proof atop_range as ATR.
  pose proof (spa1_props SPV SP16) as (SPAB & SPA32 & _).
  pose proof (ablk_lin _ _ FH) as (FH1 & FH2 & FH3 & FH4).
  assert (HBW' : In (HB pw W 8704) (FB0 FF :: LB)) by (right; exact HBW).
  destruct (AI_block AI _ _ _ _ _ _ _ _ AH3 HBW') as (NBW & (BLW & _ & TOPW & W16) & RW & RSW & SDW & WRW & _).
  pose proof (ablk_lin _ _ BLW) as (W1 & W2 & W3 & W4).
  destruct (x1_u8wB m3 W 8704 (W + 1236) 256 WRW ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (jh & UH & LH).
  destruct (x1_u8wB m3 W 8704 W 52 WRW ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (jr & UR & LR).
  destruct (x1_u8wB m3 W 8704 (W + 104) 876 WRW ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (jw & UW & LW).
  unfold X1FFHDR in HFF.
  assert (TL0 : rw_cells bsegs m3 (FF + 32) [C4 (Z_to_bv 64 0)]).
  { eapply rwc_at; [exact (rwc_hd _ _ _ _ (rwc_tl _ _ _ _ (rwc_tl _ _ _ _ (rwc_tl _ _ _ _ (rwc_tl _ _ _ _ HFF))))) | cbn; lia]. }
  assert (NS0 : rw_cells bsegs m3 (FF + 48) [C4 (Z_to_bv 64 0)]).
  { eapply rwc_at; [exact (rwc_hd _ _ _ _ (rwc_tl _ _ _ _ (rwc_tl _ _ _ _ (rwc_tl _ _ _ _ (rwc_tl _ _ _ _
      (rwc_tl _ _ _ _ (rwc_tl _ _ _ _ HFF))))))) | cbn; lia]. }
  assert (SHF : rw_cells bsegs m3 (shad FF) AF_huf_fdw_seg.FDSH) by (eapply rwc_at; [exact SH3 | unfold shad, ASHOFF; lia]).
  destruct (AF_huf_fdw_top1.fdsh_unp m3 FF SHF F64 ltac:(lia) ltac:(lia)) as (UT & UN).
  assert (LBH' : forall b, In b (FB0 FF :: LB) -> ablk (ab_addr b) (ab_addr b + ab_size b))
    by (intros b [<-|Hb]; [exact FH | exact (LBH b Hb)]).
  assert (BS3 : bytes_at bsegs m3 S (map (Z_to_bv 8) src)).
  { eapply bytes_at_magree; [exact MG | exact BS |]. rewrite length_map. intros a Ha.
    destruct (SRCA ltac:(lia)) as (p & A & n & HIn & HA1 & HA2).
    unfold aclient_addr. right; right; left. exists (HB p A n). split; [exact HIn | cbn; lia]. }
  assert (BUF : 0 < zlen src -> bufH (FB0 FF :: LB) S (zlen src)).
  { intros Hz. destruct (SRCA Hz) as (p & A & n & HIn & HA1 & HA2). exists p, A, n. split; [right; exact HIn | lia]. }
  assert (HBK : forall X n, W <= X -> X + n <= W + 8704 -> hblk8 (FB0 FF :: LB) X n).
  { intros X n H1 H2. unfold hblk8. exists pw, W, 8704. split; [right; exact HBW|]. split; [reflexivity | lia]. }
  assert (FCN : fcellA m3 (FB0 FF :: LB) (FF + 48) 4).
  { unfold fcellA. split; [|exact UN]. do 3 eexists. split; [left; reflexivity|].
    repeat match goal with |- _ /\ _ => split end; [lia | lia | exact FH | Z.div_mod_to_equations; lia]. }
  assert (FCT : fcellA m3 (FB0 FF :: LB) (FF + 32) 4).
  { unfold fcellA. split; [|exact UT]. do 3 eexists. split; [left; reflexivity|].
    repeat match goal with |- _ /\ _ => split end; [lia | lia | exact FH | Z.div_mod_to_equations; lia]. }
  assert (RCL3 : rclean m3 rstk).
  { eapply (rclean_magreeA (aclient_addr CI LB SPV) m m3 rstk RCL MG); [|exact RRLO].
    intros a Ha. unfold aclient_addr. right; right; right. exists a. split; [left; exact Ha | reflexivity]. }
  assert (HB3 : AHarness_bm.hinv_bm m3).
  { eapply (AHarness_bm.hinv_bm_magree (aclient_addr CI LB SPV) m m3 MG); [|exact HINV].
    intros a Ha. exact (AHarness_bm.hinv_bm_client _ LB SPV a HCI Ha). }
  pose proof (x1_zmaskB m3 HB3) as ZM.
  pose proof (x1_mask_ciB _ HCI) as ZC.
  assert (SH48 : shad (FF + 48) = shad FF + 6).
  { unfold shad. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations; lia. }
  assert (SH32 : shad (FF + 32) = shad FF + 4).
  { unfold shad. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations; lia. }
  pose proof (rwc_hd _ _ _ _ HSF) as HSZ.
  pose proof (fake0_lek_push0_none FF 64 LB NOF) as FK1.
  pose proof RSK as R. unfold huf_rstats_stmtA in R.
  eapply evtF_cut; [|exact K].
  eapply R with (jh := jh) (jr := jr) (jw := jw) (nsv := Z_to_bv 64 0) (tlv := Z_to_bv 64 0) (rstk := rstk).
  all: unfold AHUF_RSTATS_STACK, HUF_RDT_STACK_A2 in *.
  all: first [ eassumption | (apply HBK; lia) | lia | (Z.div_mod_to_equations; lia)
             | (eapply rng_sub'; [exact RF | lia]) | (eapply rng_sub'; [exact RSF | rewrite ?SH48, ?SH32; lia]) ].
Qed.

Section M5.
Variables (L : alayout) (RNG : footprint) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
          (m m5 : amem) (st : astate) (LB : list ablock) (SPV DT W mtl lo FF : Z) (pdt pw : aptr) (j0 : word).
Hypothesis AH5 : AHEAP AI L RNG st (FB0 FF :: LB) m5.
Hypothesis LBH : forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b).
Hypothesis F64 : FF mod 64 = 0.
Hypothesis FH : ablk FF (FF + 64).
Hypothesis FC : FF + 64 <= ATOP.
Hypothesis RF : rng RNG FF 64.
Hypothesis RSF : rng RNG (shad FF) 8.
Hypothesis FFD : forall b, In b LB -> FF + 64 <= ab_addr b \/ ab_addr b + ab_size b <= FF.
Hypothesis MG5 : magree bsegs (PAGx AI LB SPV DT mtl W) m m5.
Hypothesis SH5 : rw_cells bsegs m5 (shad FF) X1SH.
Hypothesis FF05 : rw_cells bsegs m5 FF [C8 j0].
Hypothesis FF565 : rw_cells bsegs m5 (FF + 56) [C8 (Z_to_bv 64 (fflag L 0 FF))].
Hypothesis SV5 : rw_cells bsegs m5 (SPV + -104) (X1SAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
Hypothesis STG5 : stk bsegs m5 (SPA1 SPV + 216) (SPV + -104).
Hypothesis HY : x1A_hyps RNG SPV (SPA1 SPV) lo DT (DTABLE_BYTES mtl) W 8704 FF.
Hypothesis LO : lo <= SPV - HUF_RDT_STACK_A2.
Hypothesis SPT : SPV + 16 < al_top L.
Hypothesis RSTK : rng RNG lo (al_top L - lo).
Hypothesis HMTL : 1 <= mtl <= 12.
Hypothesis HDT : In (HB pdt DT (DTABLE_BYTES mtl)) LB.
Hypothesis HBW : In (HB pw W 8704) LB.
Notation POST := (huf_rdt_postA AI huf_dt_okA L RNG ra (Z_to_bv 64 SPV) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB DT W mtl lo m).
Notation XW := [(DT, DT + DTABLE_BYTES mtl); (W, W + 8704); (SPV - 5440, SPA1 SPV + 216); (FF + 32, FF + 36)] (only parsing).

Lemma x1m5_win : forall m2, munch XW m5 m2 -> wmono bsegs m5 m2 ->
  magree bsegs (fun a => outside XW a) m5 m2 /\ magree bsegs (PAGx AI LB SPV DT mtl W) m m2 /\ AHEAP AI L RNG st (FB0 FF :: LB) m2.
Proof.
  intros m2 MU WM.
  pose proof HY as H. unfold x1A_hyps in H.
  destruct H as (DTL & DTH & DT4 & WKL & WKH & WK4 & WSZ & KLO & BOT & LOS & SPTT & SP16 & SPAR & SPA32 & DSTK & WSTK
                 & DTWK & FF64 & FFL & FFT & ABF & DFD & DFW & ABD & RD & RSD & ABW & RW & RSW & RFF & RSTK' & RI).
  pose proof (AI_aci_img AI) as HCI. pose proof (AI_aci_lo AI) as HCI0.
  assert (MGX : magree bsegs (fun a => outside XW a) m5 m2) by (apply magree_of_munch; [exact MU| exact WM]).
  split; [exact MGX|]. split.
  - eapply magree_trans; [exact MG5|]. eapply magree_mono; [exact MGX|].
    intros a (Ha & HnD & HnW). cbn [outside]. split; [|split; [|split; [|split; [|exact I]]]].
    + exact HnD.
    + exact HnW.
    + intros HIN. exact (stack_not_client CI LB SPV (SPV - 5440) a HCI HCI0 LBH ltac:(lia) ltac:(lia) Ha).
    + intros HIN. exact (x1b_ff_not_client AI LB SPV FF a LBH FFD F64 FH ltac:(lia) ltac:(left; lia) Ha).
  - eapply (AI_frame AI); [exact AH5| exact MU| exact WM|].
    constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
    + right; left. exists (HB pdt DT (DTABLE_BYTES mtl)). split; [right; exact HDT| cbn; lia].
    + right; left. exists (HB pw W 8704). split; [right; exact HBW| cbn; lia].
    + left; left. cbn. lia.
    + right; left. exists (FB0 FF). split; [left; reflexivity| cbn; lia].
Qed.

Ltac x1hy := let H := fresh "H" in pose proof HY as H; unfold x1A_hyps in H;
  destruct H as (DTL & DTH & DT4 & WKL & WKH & WK4 & WSZ & KLO & BOT & LOS & SPTT & SP16 & SPAR & SPA32 & DSTK & WSTK
                 & DTWK & FF64 & FFL & FFT & ABF & DFD & DFW & ABD & RD & RSD & ABW & RW & RSW & RFF & RSTK' & RI).

Ltac x1sh := intros ?a ?Ha; unfold X1SH in Ha; simpl in Ha;
  pose proof (ablk_lin _ _ FH) as ?FHL;
  match goal with D : ablk DT _, Wb : ablk W _ |- _ => pose proof (ablk_lin _ _ D); pose proof (ablk_lin _ _ Wb) end;
  unfold shad in Ha; try unfold ASHOFF in Ha; rewrite ?Z.shiftr_div_pow2 in Ha by lia; try change (2^3) with 8 in Ha;
  unfold ablk, DTABLE_BYTES, HufHarness.DT_BYTES in *; try unfold AIMG_HI in *; try unfold KLS in *; try unfold KHIGH in *;
  cbn [outside]; Z.div_mod_to_equations; lia.

Ltac x1out := intros ?a ?Ha; cbn in *; unfold DTABLE_BYTES, HufHarness.DT_BYTES in *; lia.

Lemma x1_kerrB : x1_kerrX RNG gp tp FR fc m5 SPV (SPA1 SPV) lo DT (DTABLE_BYTES mtl) W 8704 FF POST.
Proof.
  unfold x1_kerrX. intros m2 jA jC jD jB jE rv xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x19 x20 x21 x23 x24 x25 x26 x27
    x28 x29 x30 x31 RV MI2 MU2 WM2 STL2 FRA2.
  destruct (x1m5_win m2 MU2 WM2) as (MGX & MG2 & AH2).
  x1hy. unfold X1FRA in FRA2.
  pose proof (rwc_hd _ _ _ _ FRA2) as FA0.
  pose proof (rwc_tl _ _ _ _ FRA2) as FA1. pose proof (rwc_hd2 _ _ _ _ _ FA1) as FA24.
  pose proof (rwc_tl _ _ _ _ (rwc_tl _ _ _ _ FA1)) as FA40.
  eapply x1_closeB with (pdt := pdt) (j0 := j0) (m := m);
    first [exact AH2| exact LBH| exact F64| exact FH| exact FC| exact RF| exact RSF| exact FFD| exact MG2| exact MI2
          | exact FFLAG| exact FREL| exact SM0K| exact HMTL| exact HDT| exact LO| exact SPT| exact RSTK| exact BOT| exact SP16
          | exact RI| idtac].
  all: match goal with
  | |- rw_cells _ _ FF _ => eapply rw_cells_magree; [exact MGX| exact FF05| x1out]
  | |- rw_cells _ _ (FF + 56) _ => eapply rw_cells_magree; [exact MGX| exact FF565| x1out]
  | |- rw_cells _ _ (SPV + -104) _ => eapply rw_cells_magree; [exact MGX| exact SV5| x1out]
  | |- rw_cells _ _ (SPA1 SPV + 24) _ => eapply rwc_at; [exact FA24| cbn; lia]
  | |- rw_cells _ _ _ X1SH => eapply rwc_at; [eapply rw_cells_magree; [exact MGX| exact SH5| x1sh]| unfold shad, ASHOFF; lia]
  | |- stk _ _ lo _ => eapply stk_cells; [exact STL2| exact FA0| cbn; lia| lia]
  | |- stk _ _ _ (SPV + -104) =>
      eapply (stk_merge bsegs m2 _ (SPA1 SPV + 216));
        [eapply stk_cells; [apply stk_empty; lia| eapply rwc_at; [exact FA40| cbn; lia]| cbn; lia| lia]
        | eapply stk_magree; [exact MGX| exact STG5| x1out]
        | lia]
  | |- 0 <= _ < _ => lia
  | |- _ -> huf_dt_okA _ _ _ => intros; lia
  | _ => idtac
  end.
Qed.

Lemma x1_kendB : forall r, 0 <= r < 2^64 - 119 ->
  x1_kendX RNG gp tp FR fc m5 SPV (SPA1 SPV) lo DT (DTABLE_BYTES mtl) W 8704 FF r POST mtl.
Proof.
  intros r HR. unfold x1_kendX. intros hw rank tl m2 j0' j192 dt rst syb rsacc sym xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
    x19 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 HXF HPF HTL HT12 HZW HZR.
  destruct HXF as (DTF & UDT2 & ZDT & BDT & UHW & URK & URS & ZRS & SK1 & USY & ZSY & SK2 & STL2 & MI2 & MU2 & WM2 & FR1 & FR2 & FR4).
  destruct FR2 as (k104 & k112 & k120 & k128 & k136 & k144 & k152 & FR2).
  destruct (x1m5_win m2 MU2 WM2) as (MGX & MG2 & AH2).
  x1hy. unfold X1FR1 in FR1. unfold X1FR4 in FR4.
  pose proof (rwc_hd3 _ _ _ _ _ _ FR1) as FA0.
  pose proof (rwc_tl _ _ _ _ (rwc_tl _ _ _ _ (rwc_tl _ _ _ _ FR1))) as FA24'. pose proof (rwc_hd2 _ _ _ _ _ FA24') as FA24.
  pose proof (rwc_tl _ _ _ _ (rwc_tl _ _ _ _ FA24')) as FA40.
  eapply x1_closeB with (pdt := pdt) (j0 := j0) (m := m);
    first [exact AH2| exact LBH| exact F64| exact FH| exact FC| exact RF| exact RSF| exact FFD| exact MG2| exact MI2
          | exact FFLAG| exact FREL| exact SM0K| exact HMTL| exact HDT| exact LO| exact SPT| exact RSTK| exact BOT| exact SP16
          | exact RI| idtac].
  all: match goal with
  | |- rw_cells _ _ FF _ => eapply rw_cells_magree; [exact MGX| exact FF05| x1out]
  | |- rw_cells _ _ (FF + 56) _ => eapply rw_cells_magree; [exact MGX| exact FF565| x1out]
  | |- rw_cells _ _ (SPV + -104) _ => eapply rw_cells_magree; [exact MGX| exact SV5| x1out]
  | |- rw_cells _ _ (SPA1 SPV + 24) _ => eapply rwc_at; [exact FA24| cbn; lia]
  | |- rw_cells _ _ _ X1SH => eapply rwc_at; [eapply rw_cells_magree; [exact MGX| exact SH5| x1sh]| unfold shad, ASHOFF; lia]
  | |- stk _ _ lo _ => eapply stk_cells; [exact STL2| exact FA0| cbn; lia| lia]
  | |- stk _ _ _ (SPV + -104) =>
      eapply (stk_merge bsegs m2 _ (SPA1 SPV + 216));
        [eapply stk_cells with (A := SPA1 SPV + 160);
           [eapply stk_cells with (A := SPA1 SPV + 80);
              [eapply stk_cells with (A := SPA1 SPV + 40);
                 [apply stk_empty; lia| eapply rwc_at; [exact FA40| cbn; lia]| cbn; lia| lia]
              | exact FR2| cbn; lia| lia]
           | exact FR4| cbn; lia| lia]
        | eapply stk_magree; [exact MGX| exact STG5| x1out]
        | lia]
  | |- 0 <= _ < _ => lia
  | |- _ -> huf_dt_okA _ _ _ => intros; exact (x1_dt_okB m2 DT mtl tl dt HMTL ltac:(lia) HT12 HPF ZDT BDT UDT2)
  | _ => idtac
  end.
Qed.

End M5.
End Asm.

End CANSEC1.
