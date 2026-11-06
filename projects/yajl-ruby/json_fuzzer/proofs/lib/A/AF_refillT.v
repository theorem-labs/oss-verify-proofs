(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr Nodes NodesCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages AImageFacts ExecA LazyModel NodesA ImplRzA NodesA_mm NodesA_mmW SysStepA StepA StepA2 Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA.examples Require Import X_mmap_fixed.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import
  AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanHoare AsanPS AsanRep AsanKern AsanClient AsanWf1 AsanWf2 AsanWf3 AsanWf4 AsanWf5
  AsanBudget AsanBudget2 AsanDepot AsanRepFrame AsanRepFrame2 AsanHit AsanRepHit AsanRepCa AsanRepX AsanRealloc AsanRepRefill AsanRefillM AsanSlack.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import
  A_iface AF_place AF_fakestack_rep AF_kit AF_kit2 AF_kit3 AF_unwind A_policy5 A_slack5 A_budget5 A_live A_bundle A_benv5 A_init5
  A_instD5 A_balloc5 A_bpolicy5 A_rtok5 A_bevents5 AF_alloc_iface AF_ca_iface AF_tkit AF_ainv_kit AF_caT AX_unreg AX_Exit AF_statics AF_poison AF_premap2
  AF_pop0 AF_popT AF_populate_iface AF_refill1 AF_refill1b AF_refill2 AF_refill2b AF_refill3 AF_refill_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).
#[warnings="-notation-for-abbreviation"] Notation wz := (fun z : Z => Z_to_bv 64 z).

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LiaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac lia ::= LiaA.liaA.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma AKern_ext2 : forall E s s' mo,
  (forall c, rg_mapped_user (get_region s' c) = rg_mapped_user (get_region s c)) ->
  (forall c, rg_mapped_fa (get_region s' c) = rg_mapped_fa (get_region s c)) ->
  as_ptr_committed s' = as_ptr_committed s -> as_sec s' = as_sec s ->
  as_node_blocks s' = as_node_blocks s -> as_store_blocks s' = as_store_blocks s ->
  AKern E s mo -> AKern E s' mo.
Proof.
  intros E s s' mo GU GF P S NB SB K.
  destruct K; constructor; rewrite ?GU, ?GF, ?P, ?S, ?NB, ?SB; auto.
  - intros c Hc. rewrite GU. auto.
  - intros c Hc. rewrite GF. auto.
  - intros e He. destruct (ak_lazy e He) as [X|[X|[X|[X|X]]]]; [left| right; left| right; right; left| right; right; right; left| right; right; right; right]; try exact X.
    destruct X as (X1 & X2 & X3 & X4). split; [exact X1|]. split; [exact X2|]. split; intros c Hc; rewrite ?GU, ?GF; auto.
Qed.

(* [comment removed for export] *)
Lemma blocks_sep_ofG : forall E (Pq : list Z) (Dq : list batch) a mo, env0_ok5 E -> AWf E Pq Dq a -> AKern E a mo -> blocks_sep E a.
Proof.
  intros E Pq Dq a mo ENV WF K. pose proof alloc_ceiling_range as CR.
  pose proof ENV as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & _).
  destruct WF as (WE & _ & _ & _ & _ & WS & _). destruct WS as (_ & _ & WS3 & _).
  assert (SECR : forall sc r, In sc (as_sec a) -> In r (ae_reserved E) -> sc_map_beg sc + sc_map_size sc <= fst r \/ fst r + snd r <= sc_map_beg sc).
  { intros sc r Hsc Hr. destruct (WS3 sc Hsc) as (_ & _ & _ & _ & _ & _ & RSV). exact (RSV _ Hr). }
  pose proof (ak_store_sep _ _ _ K) as (S1 & S2 & S3 & S4 & S5).
  unfold placed, A_IMG_END, A_LOWAPP_END, A_HIGH_BEG in N3, N4.
  intros b len [[Hb ->]|[Hb ->]].
  - destruct Hb as [<-|Hb].
    + split; [unfold app_mem; rewrite kHighMemBeg_val, kLowAppEnd_val; unfold kDepotNodeBlockBytes in *; clear -N3 CR; lia|].
      split; [unfold kDepotNodeBlockBytes in *; clear -N3; lia|]. split; [exact N7|]. split; [| split; [exact N8| exact N5]].
      intros sc Hsc. destruct (SECR sc _ Hsc N1); cbn [fst snd] in *; [right| left]; lia.
    + destruct (ak_blocks_sep _ _ _ K b kDepotNodeBlockBytes (or_introl (conj Hb eq_refl))) as (B1 & B2 & _ & B3 & B4 & B5).
      destruct WE as (_ & _ & _ & _ & _ & _ & _ & _ & WEfs & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WEimg & _).
      split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|].
      split; [destruct (B5 _ WEfs); cbn [fst snd] in *; [left| right]; lia|].
      unfold img_sep. destruct (B5 _ WEimg) as [X|X]; [left; exact X| right]. destruct (ae_img E); cbn [fst snd] in *; lia.
  - destruct Hb as [<-|Hb].
    + split; [unfold app_mem; rewrite kHighMemBeg_val, kLowAppEnd_val; unfold kStoreBlockBytes in *; clear -N4 CR; lia|].
      split; [unfold kStoreBlockBytes in *; clear -N4; lia|]. unfold kStoreBlockBytes. split; [exact S1|]. split; [exact S2|]. split; [exact N9| exact N6].
    + destruct (ak_blocks_sep _ _ _ K b kStoreBlockBytes (or_intror (conj Hb eq_refl))) as (B1 & B2 & _ & B3 & B4 & B5).
      destruct WE as (_ & _ & _ & _ & _ & _ & _ & _ & WEfs & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WEimg & _).
      split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|].
      split; [destruct (B5 _ WEfs); cbn [fst snd] in *; [left| right]; lia|].
      unfold img_sep. destruct (B5 _ WEimg) as [X|X]; [left; exact X| right]. destruct (ae_img E); cbn [fst snd] in *; lia.
Qed.

(* [comment removed for export] *)
Lemma outside_app : forall W1 W2 x, outside (W1 ++ W2) x <-> outside W1 x /\ outside W2 x.
Proof. induction W1 as [|[lo hi] W1 IH]; intros W2 x; cbn; [tauto|]. rewrite IH. tauto. Qed.
Lemma munch_app : forall W1 W2 m1 m2 m3, munch W1 m1 m2 -> munch W2 m2 m3 -> munch (W1 ++ W2) m1 m3.
Proof.
  intros W1 W2 m1 m2 m3 H1 H2 x Hx. apply outside_app in Hx as [X1 X2]. rewrite (H2 x X2). exact (H1 x X1).
Qed.

(* [comment removed for export] *)
Lemma nth_error_ext' : forall {X} (l1 l2 : list X), (forall i, nth_error l1 i = nth_error l2 i) -> l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros l2 H.
  - destruct l2 as [|y l2]; [reflexivity|]. specialize (H 0%nat). cbn in H. discriminate.
  - destruct l2 as [|y l2]; [specialize (H 0%nat); cbn in H; discriminate|].
    pose proof (H 0%nat) as H0. cbn in H0. injection H0 as ->. f_equal. apply IH. intros i. exact (H (Datatypes.S i)).
Qed.

(* [comment removed for export] *)
Lemma zw_mod_add : forall x k, Z_to_bv 64 (x mod 2^64 + k) = Z_to_bv 64 (x + k).
Proof.
  intros x k. rewrite <- (ZBridge.Z_to_bv_mod64 (x mod 2^64 + k)), <- (ZBridge.Z_to_bv_mod64 (x + k)).
  rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma live_block_whereG : forall E (Pq : list Z) (Dq : list batch) a blo bsz, AWf E Pq Dq a -> In (blo, bsz) (live_blocks a) ->
  1 <= bsz /\ blo + bsz <= alloc_ceiling /\ (blo + bsz <= kLowAppEnd \/ kHighMemBeg <= blo)
  /\ ((ae_space_beg E <= blo /\ blo + bsz <= ae_space_beg E + kSpaceSize)
      \/ (exists sc, In sc (as_sec a) /\ sc_map_beg sc <= blo /\ blo + bsz <= sc_map_beg sc + sc_map_size sc)).
Proof.
  intros E Pq Dq a blo bsz WF LIVE. pose proof WF as (WE & WR & _ & _ & _ & (_ & _ & WS3 & _) & _).
  destruct (live_block_loc E Pq Dq a blo bsz WF LIVE) as (k & cm & Hk & _ & _ & POS & L1 & L2 & LOC).
  pose proof WE as (E1 & E2 & E3 & E4 & E5 & _).
  destruct (cm_prim cm) as [c'|].
  - destruct LOC as (Hc' & R1 & R2). unfold region_beg in R1, R2.
    destruct (proj2 WR c' Hc') as ((_ & _) & _ & R3 & _). unfold region_of in R3.
    unfold kFreeArrayOffset, kRegionSize, kSpaceSize, kLargestClassID in *. rewrite kHighMemBeg_val in *.
    split; [exact POS|]. split; [clear -L1 L2 R1 R2 R3 Hc' E3 E4 E5; nia|]. split; [right; clear -L1 R1 R2 R3 Hc' E2 E3; nia|].
    left. clear -L1 L2 R1 R2 R3 Hc' E3 E4. split; nia.
  - destruct LOC as (sc & Hsc & R1 & R2). destruct (WS3 sc Hsc) as (_ & AM & CE & _). unfold app_mem in AM.
    split; [exact POS|]. split; [clear -L2 R2 CE; lia|]. split; [unfold kPageSize in R1; clear -L1 L2 R1 R2 AM POS; lia|].
    right. exists sc. split; [exact Hsc|]. unfold kPageSize in R1. clear -L1 L2 R1 R2. lia.
Qed.
Lemma live_block_off_threadG : forall E (Pq : list Z) (Dq : list batch) a blo bsz, AWf E Pq Dq a -> In (blo, bsz) (live_blocks a) ->
  blo + bsz <= alloc_ceiling /\ (blo + bsz <= ae_thread E \/ ae_thread E + 4096 <= blo).
Proof.
  intros E Pq Dq a blo bsz WF LIVE. pose proof WF as (WE & WR & _ & _ & _ & (_ & _ & WS3 & _) & _).
  destruct (live_block_loc E Pq Dq a blo bsz WF LIVE) as (k & cm & Hk & _ & _ & _ & L1 & L2 & LOC).
  rewrite blk_hi_span in L2. unfold blk_lo in L1.
  destruct WE as (E1 & E2 & E3 & E4 & E5 & _ & _ & _ & _ & _ & _ & _ & E13 & _ & E15 & _ & _ & _ & E19 & _).
  destruct (cm_prim cm) as [c'|].
  - destruct LOC as (Hc' & R1 & R2). rewrite blk_hi_span in R2. unfold blk_lo, region_beg in R1, R2.
    destruct (proj2 WR c' Hc') as ((_ & _) & _ & R3 & _). unfold region_of in R3.
    unfold kFreeArrayOffset, kRegionSize, kSpaceSize, kLargestClassID in *. clear -L1 L2 R1 R2 R3 Hc' E3 E4 E5 E19. split; nia.
  - destruct LOC as (sc & Hsc & R1 & R2). rewrite blk_hi_span in R2. unfold blk_lo in R1.
    destruct (WS3 sc Hsc) as (_ & _ & CE & _ & _ & _ & RSV). pose proof (RSV _ E13) as X. cbn [fst snd] in X.
    unfold kPageSize in *. clear -L1 L2 R1 R2 CE X. split; lia.
Qed.

(* [comment removed for export] *)
Lemma same_fp_inited : forall a, same_fp a (upd_cache_inited true a).
Proof. intros a. unfold same_fp, regions_bytes, get_region. destruct a; cbn; repeat split; reflexivity. Qed.

Lemma fin_same_fp : forall (E : aenv) c n a2, 1 <= c <= 30 -> same_fp a2 (refill_fin c n a2).
Proof.
  intros E c n a2 Hc. unfold same_fp.
  split; [| rewrite fin_sec, fin_ptr, fin_residue, fin_node_blocks, fin_store_blocks; repeat split; reflexivity].
  rewrite (regions_bytes_upd E a2 (refill_fin c n a2) c 0 0 Hc); [clear; lia| | |].
  - intros c' NE. rewrite fin_get_region. destruct (decide (c' = c)) as [->|NE']; [exfalso; exact (NE eq_refl)| reflexivity].
  - rewrite fin_get_region. destruct (decide (c = c)) as [_|NE]; [cbn; clear; lia| exfalso; exact (NE eq_refl)].
  - rewrite fin_get_region. destruct (decide (c = c)) as [_|NE]; [cbn; clear; lia| exfalso; exact (NE eq_refl)].
Qed.

Lemma fin_AKern : forall E c n a2 mo, AKern E a2 mo -> AKern E (refill_fin c n a2) mo.
Proof.
  intros E c n a2 mo K. eapply AKern_ext2; [| | apply fin_ptr| apply fin_sec| apply fin_node_blocks| apply fin_store_blocks| exact K];
    intros c'; rewrite fin_get_region; destruct (decide (c' = c)) as [->|NE]; reflexivity.
Qed.

Lemma fin_zlen_cache : forall c n a2, 0 <= n -> (Z.to_nat n <= length (rg_free (get_region a2 c)))%nat -> zlen (get_cache (refill_fin c n a2) c) = n.
Proof.
  intros c n a2 Hn Hl. rewrite fin_get_cache. destruct (decide (c = c)) as [_|NE]; [| exfalso; exact (NE eq_refl)].
  unfold gfa_hi, gfa_keep, zlen. rewrite length_skipn. clear -Hn Hl. lia.
Qed.

Lemma inited_AKern : forall E a mo, AKern E a mo -> AKern E (upd_cache_inited true a) mo.
Proof. intros E a mo K. eapply AF_tkit.AKern_ext; [| | | | | exact K]; destruct a; reflexivity. Qed.

(* [comment removed for export] *)
Section RfT.
Variable E0 : aenv.
Variable FSB0 : Z.
Variable HR0 : list (Z * Z).
Variables L0 RES0 : list (word * word).
Variable EB0 : Z.
Variable PL0 : fs_plumb.
Hypothesis HR0_ok : Forall (fun iv => fst iv <= snd iv) HR0 /\ A0_pages HR0 <= 8192.
Hypothesis EB0_ok : 0 <= EB0 <= 2^32.
Hypothesis ENV_depot : zlen (ae_keys0 E0) <= 1000 /\ 0 <= ae_frames0 E0 <= 4096.
Hypothesis ENV0 : env0_ok5 E0.
Hypothesis PL0OK : pl0_ok5 E0 PL0.
Hypothesis L0OK : l0_ok5 E0 L0 RES0.

#[local] Notation RTOKc := (RTOK E0 FSB0 HR0 L0 RES0 EB0).
#[local] Notation ATOKc := (ATOK E0 FSB0 HR0 L0 RES0 EB0).
#[local] Notation PP := (AF_caT.PP E0 FSB0 HR0).
#[local] Notation aSc := (A_bundle.aS E0 FSB0 HR0).
#[local] Notation aNc := (A_bundle.aN E0 FSB0 HR0).
#[local] Notation aEBc := (A_bundle.aEB EB0).
#[local] Notation SB := (ae_space_beg E0).
#[local] Notation T := (ae_thread E0).
#[local] Notation RI := (ae_region_info E0).
#[local] Notation CA := (ae_thread E0 + 208).

(* [comment removed for export] *)
Lemma pop_statics_of : forall a m, ae_ic E0 = asan_ic ->
  ARep asegs E0 (DepotR asegs E0) a m -> rt_misc5 FSB0 PL0 E0 m -> pop_statics m.
Proof.
  intros a m IC0 Hrep Hrt.
  destruct Hrt as (_ & [t XS] & _ & AMS & _).
  assert (US : unreg_statics m) by (unfold exit_statics in XS; decompose [and] XS; assumption).
  unreg_statics_open US.
  destruct AMS as (_ & _ & _ & GPAIR & MML & DPM & CFF & _).
  destruct Hrep as (_ & _ & _ & _ & _ & _ & _ & _ & Rglob & _).
  pose proof Rglob as (Gfl & Gfu & Gth & Gdd & Gsh & Ghe & Gcp & Gai & Gmcs & Gps & Gdy & Ganc & Grm & _).
  rewrite IC0 in Gps, Gdy, Ghe, Grm. cbn [aic_page_size_cached aic_dying_flag aic_kHighMemEnd aic_REAL_memcpy_var aic_musl_memcpy aic_musl_memset asan_ic] in Gps, Gdy, Ghe, Grm.
  split.
  - unfold statics, GOT_PAGESIZE, GOT_CFLAGS, GOT_PAIR, V_PAGESIZE, V_CFLAGS, V_MMAP_LIMIT, V_DPM, V_ABORTFLAG.
    split; [exact GPSC|]. split; [exact GCF|]. split; [exact GPAIR|]. split; [exact Gps|]. split; [exact MML|]. split; [exact DPM| exact Gdy].
  - unfold poison_globals. split.
    { pose proof (AF_kit3.rwc_join_at asegs m _ _ _ _ GHE GRSP ltac:(reflexivity)) as X4.
      pose proof (AF_kit3.rwc_join_at asegs m _ _ _ _ GME X4 ltac:(reflexivity)) as X3.
      pose proof (AF_kit3.rwc_join_at asegs m _ _ _ _ GMB X3 ltac:(reflexivity)) as X2.
      pose proof (AF_kit3.rwc_join_at asegs m _ _ _ _ GSBP X2 ltac:(reflexivity)) as X1. cbn [app] in X1. exact X1. }
    split; [exact GCF|]. split; [exact GSB|]. split; [exact Ghe|]. split; [exact Grm|]. split; [exact GCPM| exact GTHR].
Qed.
(* [comment removed for export] *)
Lemma pop_statics_agree : forall m m', pop_statics m -> (forall z, 0x10000 <= z < 0x603000 -> m' (wa z) = m (wa z)) -> pop_statics m'.
Proof.
  intros m m' [(S1 & S2 & S3 & S4 & S5 & S6 & S7) (G1 & G2 & G3 & G4 & G5 & G6 & G7)] AG.
  unfold pop_statics, statics, poison_globals, GOT_PAGESIZE, GOT_CFLAGS, GOT_PAIR, V_PAGESIZE, V_CFLAGS, V_MMAP_LIMIT, V_DPM, V_ABORTFLAG in *.
  Ltac trs AG H := eapply rw_cells_agree; [| exact H]; cbn; intros z Hz; apply AG; clear -Hz; lia.
  (* [comment removed for export] *)
  split.
  - split; [trs AG S1|]. split; [trs AG S2|]. split; [trs AG S3|]. split; [trs AG S4|]. split; [trs AG S5|]. split; [trs AG S6| trs AG S7].
  - split; [trs AG G1|]. split; [trs AG G2|]. split; [trs AG G3|]. split; [trs AG G4|]. split; [trs AG G5|]. split; [trs AG G6| trs AG G7].
Qed.

Theorem refill_srz : refill_srz_stmt E0 FSB0 HR0 L0 RES0 EB0 PL0.
Proof.
  unfold refill_srz_stmt. intros until K. cbv zeta. intros KN TOK RIV HCc CE ROOM NPE SK LOC LO SPA SPH TP CONT.
  pose proof alloc_ceiling_range as CR. pose proof A_bundle.kHighMemBeg_val as KHB. pose proof kLowAppEnd_val as KLE.
  pose proof RIV as RIV0. destruct RIV as (Hrep & Hwf & Hkern & Hres & Hqb & Hdi & Hmi & Hrt & Hss & Hcs).
  destruct (RTOK_elim _ _ _ _ _ _ _ _ _ _ TOK) as (R0 & R0' & ATK & HCR & HCR' & GR0 & GD0 & RLE).
  assert (ENV : ENVOK E0 FSB0 s) by exact (ATOK_ENVOK _ _ _ _ _ _ _ _ _ _ ATK).
  pose proof ENV as ENV'. destruct ENV' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EE & EFS & [EI1 EI2]). rewrite EE in EI1, EI2.
  pose proof L0OK as (LS_L0 & GS_L0 & HS_L0 & RES0_low & RES0_cover & RSVD & RSVD_pos).
  set (a := aps_alloc s) in *.
  remember (bv_unsigned sp) as usp eqn:Husp.
  assert (Esp : sp = Z_to_bv 64 usp) by (rewrite Husp; symmetry; apply Z_to_bv_bv_unsigned).
  assert (USPR : 0 <= usp < 2^64) by (rewrite Husp; pose proof (bv_unsigned_in_range 64 sp) as BR; unfold bv_modulus in BR; clear -BR; lia).
  rewrite Esp in CONT |- *. clear Esp Husp. unfold K_REFILL in LO.
  pose proof HCc as HC30. unfold kLargestClassID in HC30. pose proof (hint_range c HC30) as HR. set (n := hint c) in *.
  (* [comment removed for export] *)
  pose proof ENV0 as ENV0'. destruct ENV0' as (D0a & D0b & _ & _ & _ & _ & _ & _ & _ & _ & _ & IMGR & _ & _ & _ & _ & _ & IC0 & TDN & DNP).
  pose proof Hrep as (Rins & Rri & Rrm & Rthr & Rsec & Rch & Rbat & Rdep & Rglob & Rsh).
  pose proof Rthr as (Ttop & T40 & Tq & Tcache & Tcst & Tst & Tby & Tunw).
  pose proof Rins as (I1 & I2 & _).
  pose proof (pop_statics_of a m IC0 Hrep Hrt) as PST.
  unfold ae_instance in I1, I2. rewrite IC0 in I1, I2. cbn [aic_instance asan_ic kInsSpaceBeg kInsSecondary Z.add] in I1, I2.
  pose proof Hwf as (WE & WR & WC & WK & WQ & WS & WD). pose proof WS as (WS1 & WS2 & WS3 & WS4 & WS5). pose proof WC as (WC1 & WC2 & WC3).
  pose proof WE as (WE1 & WE2 & WE3 & WE4 & WE5 & WE6 & WE7 & WE8 & WE9 & WE10 & WE11 & WE12 & WE13 & WE14 & WE15 & WE16 & WE17 & WE18 & WE19 & WE20 &
                    WE21 & WE22 & WE23 & WE24 & WE25 & WE26 & _).
  unfold app_mem in WE14, WE16. rewrite KHB, KLE in WE14, WE16.
  (* [comment removed for export] *)
  pose proof PL0OK as ((c0 & cl & CR0 & CC1 & CC2) & (d0 & dl & DR0 & DD1 & DD2) & TR & CT & DT & CD & CIA).
  pose proof TR as (TR1 & TR2 & _). pose proof TR2 as (Tlo & Thi & Timg & Tband). unfold A_IMG_END, A_LOWAPP_END, A_HIGH_BEG in Timg, Tband.
  pose proof (rt_misc5_fsenv _ _ _ _ Hrt) as FSE.
  assert (T8 : T mod 8 = 0) by (unfold FSEnv in FSE; decompose [and] FSE; assumption).
  assert (TC : thread_cells m tp 0x601eb8 (fp_ctx PL0) T).
  { pose proof FSE as FSE'. unfold FSEnv in FSE'. pose proof FSE' as (_ & _ & _ & _ & _ & _ & FKI & FKEY & FTSD & FTSD0 & FCTXT & _). clear FSE'.
    split; [exact FKI|]. split; [exact FKEY|]. split; [| split; [exact FTSD0| exact FCTXT]].
    rewrite TP. rewrite unsigned_lit by (clear; lia). exact FTSD. }
  (* [comment removed for export] *)
  destruct (proj2 WR c HCc) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12). cbv zeta in A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12.
  assert (CI_rows : forall i, 1 <= i <= 31 -> rw_cells asegs m (CA + 80 * i)
            [C4 (wz (zlen (get_cache a i))); C4 (wz (if as_cache_inited a then ic_max_count i else 0)); C8 (wz (if as_cache_inited a then ic_class_size i else 0))]).
  { intros i Hi. destruct (Tcache i ltac:(unfold kNumClasses; clear -Hi; lia)) as [X _]. unfold percls_cells in X. unfold kThrCache, kPerClassSize in X.
    replace (T + 208 + 80 * i) with (CA + 80 * i) in X by (clear; lia).
    unfold row_max_count, row_class_size in X. unfold ic_max_count, ic_class_size. exact X. }
  assert (CNT : forall i, 0 <= zlen (get_cache a i) < 2^32).
  { intros i. unfold zlen. destruct (as_cache a !! i) as [l|] eqn:L.
    - pose proof (WC1 i l L) as Hi. destruct (WC3 i Hi) as (LE & _). unfold get_cache in LE |- *. rewrite L in LE |- *. unfold zlen in LE.
      pose proof (hint_range i ltac:(unfold kLargestClassID in Hi; clear -Hi; lia)) as HRi. unfold max_count in LE. clear -LE HRi. lia.
    - unfold get_cache. rewrite L. cbn. clear. lia. }
  assert (HCA : (0x1000 <= CA /\ (CA + 2584 <= 0x10000 \/ 0x603000 <= CA)) /\ CA + 2584 <= alloc_ceiling /\ CA mod 8 = 0).
  { clear -Tlo Thi Timg T8. split; [| split; [lia| Z.div_mod_to_equations; lia]]. lia. }
  (* [comment removed for export] *)
  set (P := PP s mo).
  assert (PSTK : forall y k, lo <= y -> y + Z.of_nat k <= usp + 48 -> P (Z_to_bv 64 y, k)).
  { intros y k H1 H2. unfold P, AF_caT.PP. apply (pol_stack' E0 FSB0 HR0 s mo Hkern WE ENV0); clear -H1 H2 LOC SPH CR; lia. }
  assert (PCA : forall y k, CA <= y -> y + Z.of_nat k <= CA + 2584 -> P (Z_to_bv 64 y, k)).
  { intros y k H1 H2. unfold P, AF_caT.PP. apply (pol_thread' E0 FSB0 HR0 s mo Hkern WE); clear -H1 H2; lia. }
  pose proof (AF_caT.PP_KIP E0 FSB0 HR0 L0 RES0 EB0 s mo R0 R0' ATK) as KIP0.
  eapply (rzA_seg_cfg asegs (aSc s) (aNc s) (aEBc s) P).
  { unfold A_REFILL, kThrCache, kPerClassSize. replace (T + 208 + 80 * c) with (CA + 80 * c) by (clear; lia).
    eapply (refill_front P gp tp F fc lo usp CA c A_INST (CA + 80 * c) (fun i => zlen (get_cache a i)) eq_refl LOC
              ltac:(clear -LO; lia) SPH ltac:(clear -SPA; Z.div_mod_to_equations; lia)
              HC30 HCA CNT ltac:(cbv beta; rewrite CE; reflexivity) PSTK PCA (as_cache_inited a));
      [exact Hmi| exact SK| intros i Hi; exact (CI_rows i Hi)]. }
  { exact KIP0. }
  intros ms1 mo1 HQ1 AG1 KIP1.
  destruct HQ1 as (yt0 & yt1 & yt2 & ya5 & ya6 & ya7 & yt3 & yt4 & yt5 & m1 & j8 & -> & MU1 & WM1 & MI1 & SK1 & FR1 & ROWS1).
  pose proof (magree_frame _ _ AG1) as (Ffds1 & Fvm1 & Flz1 & Ffs1 & Fh1 & Ftid1 & _).
  destruct KIP1 as [KIA1 _].
  pose proof (ATOK_magree _ _ _ _ _ _ _ _ _ _ _ ATK AG1 KIA1) as ATK1.
  pose proof (AKern_frame _ _ _ _ Fvm1 Flz1 Hkern) as AK1.
  set (usp1 := usp - 32) in *.
  assert (U1 : bv_unsigned (Z_to_bv 64 (usp + -32)) = usp1) by (subst usp1; rewrite unsigned_lit; clear -USPR SPA LO LOC CR; lia).
  assert (AGB1 : forall z, 0 <= z < 2^64 -> ~ (usp1 <= z < usp) -> (forall i, 1 <= i <= 31 -> ~ (CA + 80 * i + 4 <= z < CA + 80 * i + 16)) -> m1 (wa z) = m (wa z)).
  { intros z Hz N1 N2. apply MU1. rewrite wa_unsigned by exact Hz. unfold ic_W. cbn [outside]. subst usp1.
    split; [clear -N1; lia|].
    Ltac icw N2 i := split; [let C := fresh in intros C; apply (N2 i); [clear; lia| clear -C; lia]|].
    icw N2 1. icw N2 2. icw N2 3. icw N2 4. icw N2 5. icw N2 6. icw N2 7. icw N2 8. icw N2 9. icw N2 10.
    icw N2 11. icw N2 12. icw N2 13. icw N2 14. icw N2 15. icw N2 16. icw N2 17. icw N2 18. icw N2 19. icw N2 20.
    icw N2 21. icw N2 22. icw N2 23. icw N2 24. icw N2 25. icw N2 26. icw N2 27. icw N2 28. icw N2 29. icw N2 30.
    split; [let C := fresh in intros C; apply (N2 31); [clear; lia| clear -C; lia]| exact I]. }
  (* [comment removed for export] *)
  assert (OFFT : forall z, ~ (T <= z < T + 4096) -> forall i, 1 <= i <= 31 -> ~ (CA + 80 * i + 4 <= z < CA + 80 * i + 16)).
  { intros z Hz i Hi Ci. apply Hz. clear -Hi Ci. lia. }
  (* [comment removed for export] *)
  set (r := region_of a c) in *.
  set (RP := RI + kRegSize * c). set (FA := free_array SB c). set (CH := CA + 80 * c + 16).
  assert (HRI : RI = SB + 2^37) by reflexivity.
  assert (HRP' : RP = SB + 2^37 + 128 * c) by (subst RP; rewrite HRI; reflexivity).
  assert (IROW1 : rw_cells asegs m1 (A_INST + 32) [C8 (wz SB); C4 (wz 0xffffffff); C4 (wz 0); C8 (wz RI)]).
  { pose proof (AF_kit3.rwc_split asegs m _ [C8 (wz SB); C4 (wz 0xffffffff); C4 (wz 0); C8 (wz RI)] [C1 (Z_to_bv 8 0)] I1) as [X _].
    eapply rw_cells_agree; [| exact X]. cbn. intros z Hz. unfold A_INST in Hz. apply AGB1; [clear -Hz; lia| clear -Hz LOC LO CR; lia| apply OFFT; clear -Hz Timg; lia]. }
  set (na := rg_n_allocated r mod 2 ^ 64).
  assert (NA : 0 <= na < 2^64) by (subst na; apply Z.mod_pos_bound; clear; lia).
  assert (RROW1 : rw_cells asegs m1 RP (rrow 0 (rg_num_freed r) (rg_mapped_fa r) (rg_alloc_user r) (rg_mapped_user r) na (rg_n_freed r))).
  { pose proof (Rri c ltac:(unfold kNumClasses; clear -HC30; lia)) as X. fold r in X. unfold region_cells, AsanRep.zw, AsanRep.zb, zeros in X. cbn [repeat] in X.
    rewrite <- (ZBridge.Z_to_bv_mod64 (rg_n_allocated r)) in X. fold na in X.
    fold RP in X. eapply rw_cells_agree; [| exact X]. unfold rrow. cbn [cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]. intros z Hz.
    apply AGB1; [clear -Hz HRP' HC30 WE2 WE3 WE4 WE5 CR KHB; rewrite KHB in WE2; unfold kSpaceSize in WE4; lia| clear -Hz HRP' HC30 WE2 WE3 WE4 WE5 CR LOC LO KHB; rewrite KHB in WE2; unfold kSpaceSize in WE4; lia|].
    apply OFFT. clear -Hz HRP' HC30 WE3 WE4 WE19. unfold kSpaceSize in WE4. lia. }
  (* [comment removed for export] *)
  set (P1 := PP s mo1).
  assert (PSTK1 : forall y k, lo <= y -> y + Z.of_nat k <= bv_unsigned (Z_to_bv 64 (usp + -32)) -> P1 (Z_to_bv 64 y, k)).
  { intros y k H1 H2. rewrite U1 in H2. unfold P1, AF_caT.PP. apply (pol_stack' E0 FSB0 HR0 s mo1 AK1 WE ENV0); clear -H1 H2 LOC SPH CR; lia. }
  assert (PDAT1 : forall y k, 0xa4000 <= y -> y + Z.of_nat k <= 0x603000 -> P1 (Z_to_bv 64 y, k)).
  { intros y k H1 H2. unfold P1, AF_caT.PP. apply (pol_img' E0 FSB0 HR0 s mo1 AK1 WE ENV ENV0); clear -H1 H2; lia. }
  assert (PRI1 : forall y k, RI <= y -> y + Z.of_nat k <= RI + 4096 -> P1 (Z_to_bv 64 y, k)).
  { intros y k H1 H2. rewrite HRI in H1, H2. unfold P1, AF_caT.PP. apply (pol_reginfo' E0 FSB0 HR0 s mo1 WE); clear -H1 H2; lia. }
  assert (PCH1 : forall y k, CH <= y -> y + Z.of_nat k <= CH + 64 -> P1 (Z_to_bv 64 y, k)).
  { intros y k H1 H2. subst CH. unfold P1, AF_caT.PP. apply (pol_thread' E0 FSB0 HR0 s mo1 AK1 WE); clear -H1 H2 HC30; lia. }
  assert (PRO1 : forall y k, 0x10000 <= y -> y + Z.of_nat k <= 0x31000 -> P1 (Z_to_bv 64 y, k)).
  { intros y k H1 H2. unfold P1, AF_caT.PP. apply (pol_img' E0 FSB0 HR0 s mo1 AK1 WE ENV ENV0); clear -H1 H2; lia. }
  assert (HINST : 0xa4000 <= A_INST /\ A_INST + 64 <= 0x603000) by (unfold A_INST; clear; lia).
  assert (HSB : 0x10007fff8000 <= SB /\ SB + 2^37 + 4096 <= alloc_ceiling /\ SB mod 4096 = 0).
  { rewrite KHB in WE2. unfold kSpaceSize in WE4. clear -WE1 WE2 WE3 WE4 WE5. split; [lia|]. split; [lia|]. Z.div_mod_to_equations. lia. }
  assert (HCH : (0x1000 <= CH /\ (CH + 64 <= 0x10000 \/ 0x603000 <= CH)) /\ CH + 64 <= alloc_ceiling /\ CH mod 4 = 0).
  { subst CH. clear -Tlo Thi Timg T8 HC30. split; [lia|]. split; [lia|]. Z.div_mod_to_equations. lia. }
  assert (HCS : CH + 64 <= SB \/ SB + 2^37 + 4096 <= CH).
  { subst CH. unfold kSpaceSize in WE4. clear -WE3 WE4 WE19 HC30. lia. }
  pose proof (AF_caT.PP_KIP E0 FSB0 HR0 L0 RES0 EB0 s mo1 R0 R0' ATK1) as KIP1'.
  (* [comment removed for export] *)
  assert (LOCKSTEP : forall Q,
    (forall m2 fj,
       munch [(bv_unsigned (Z_to_bv 64 (usp + -32)) - 128, bv_unsigned (Z_to_bv 64 (usp + -32))); (RP, RP + 8)] m1 m2 -> wmono asegs m1 m2 -> mem_inv asegs m2 ->
       stk asegs m2 lo (bv_unsigned (Z_to_bv 64 (usp + -32)) + -128) ->
       rw_cells asegs m2 (bv_unsigned (Z_to_bv 64 (usp + -32)) + -128)
         [CB 24 fj; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 (CA + 80 * c)); C8 (Z_to_bv 64 0x37a30)] ->
       rw_cells asegs m2 RP (rrow kMtxWriter (rg_num_freed r) (rg_mapped_fa r) (rg_alloc_user r) (rg_mapped_user r) na (rg_n_freed r)) ->
       evtA asegs P1 Q
         (MS (mkR (Z_to_bv 64 0x37a30) (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (usp + -32)) + -128)) gp tp (Z_to_bv 64 0) (Z_to_bv 64 kMtxWriter) (Z_to_bv 64 0)
                  (Z_to_bv 64 RP) (Z_to_bv 64 A_INST) (Z_to_bv 64 (RP + 8)) (Z_to_bv 64 (CA + 2560)) (Z_to_bv 64 c) (Z_to_bv 64 CH) (Z_to_bv 64 n)
                  (Z_to_bv 64 0) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) s2 (Z_to_bv 64 0x2000000000000000) (Z_to_bv 64 FA) (Z_to_bv 64 0x10000000000)
                  (Z_to_bv 64 0x10000000000fffff) (Z_to_bv 64 kMtxWriter) (Z_to_bv 64 1500) (Z_to_bv 64 0xdfffffffffffffff) s10 s11 yt3 yt4 yt5 t6)
             F (Z_to_bv 64 0x37c40) fc None m2 (seg_rom asegs))) ->
    evtA asegs P1 Q
      (MS (mkR (Z_to_bv 64 0x37a30) (Z_to_bv 64 (usp + -32)) gp tp yt0 yt1 yt2 (Z_to_bv 64 (CA + 80 * c)) (Z_to_bv 64 n) (Z_to_bv 64 A_INST)
               (Z_to_bv 64 (CA + 2560)) (Z_to_bv 64 c) (Z_to_bv 64 (CA + 80 * c + 16)) (Z_to_bv 64 n) ya5 ya6 ya7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 yt3 yt4 yt5 t6)
          F (Z_to_bv 64 0x37af0) fc None m1 (seg_rom asegs))).
  { intros Q KQ. replace (Z_to_bv 64 (CA + 80 * c + 16)) with (Z_to_bv 64 CH) by reflexivity.
    eapply evtA_cut.
    { eapply (gfa_lock P1 (Z_to_bv 64 0x37a30) (Z_to_bv 64 (usp + -32)) gp tp F fc lo A_INST (CA + 2560) c CH n SB RI RP FA
                eq_refl eq_refl LOC ltac:(rewrite U1; subst usp1; clear -LO; lia) ltac:(rewrite U1; subst usp1; clear -SPH; lia) HC30 HINST HSB HRI HCH PSTK1 PDAT1 PRI1);
        [rewrite U1; subst usp1; replace (usp - 32) with (usp + -32) by (clear; lia); exact SK1| exact MI1| exact IROW1| exact RROW1]. }
    cbv beta. intros ms2 (m2 & fj & -> & MUL & WML & MI2 & SK2 & FRL & RROWL). exact (KQ m2 fj MUL WML MI2 SK2 FRL RROWL). }
  (* [comment removed for export] *)
  destruct (Rrm c ltac:(unfold kNumClasses; clear -HC30; lia)) as [UMAP (fjunk & FARR & FAL)]. fold r in UMAP, FARR, FAL. fold FA in FARR.
  set (ws := map wz (rg_free r) ++ fjunk) in FARR.
  assert (LWS : 4 * Z.of_nat (length ws) = rg_mapped_fa r) by (subst ws; rewrite length_app, length_map; exact FAL).
  destruct (Tcache c ltac:(unfold kNumClasses; clear -HC30; lia)) as [_ (cjunk & CARR & CLEN)]. rewrite CE in CARR, CLEN. cbn [map app length Nat.add] in CARR, CLEN.
  unfold kThrCache, kPerClassSize in CARR. replace (T + 208 + 80 * c + 16) with CH in CARR by (subst CH; clear; lia).
  assert (FARR1 : u32arr asegs m1 FA ws).
  { eapply u32arr_agree; [| exact FARR]. intros z Hz. rewrite (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 WR'))))))))) in Hz || idtac.
    apply AGB1; subst FA; unfold free_array, region_beg, kRegionSize, kFreeArrayOffset, kFreeArraySize, kSpaceSize in *;
      [clear -Hz LWS A5 A7 HC30 WE2 WE3 WE4 WE5 CR KHB; rewrite KHB in WE2; lia| clear -Hz LWS A5 A7 HC30 WE3 WE4 WE5 LOC LO; lia| apply OFFT; clear -Hz LWS A5 A7 HC30 WE3 WE4 WE19; lia]. }
  assert (CARR1 : u32arr asegs m1 CH cjunk).
  { eapply u32arr_agree; [| exact CARR]. rewrite CLEN. intros z Hz. apply AGB1; subst CH; [clear -Hz Tlo Thi CR HC30; lia| clear -Hz Thi LOC LO HC30; lia|].
    (* [comment removed for export] *)
    intros i Hi Ci. clear -Hz Hi Ci HC30. lia. }
  assert (PFA1 : forall y k, FA <= y -> y + Z.of_nat k <= FA + 4 * Z.of_nat (length ws) -> P1 (Z_to_bv 64 y, k)).
  { intros y k H1 H2. rewrite LWS in H2. destruct k as [|k]; [apply AF_popT.acc_ok_empty|].
    unfold P1, AF_caT.PP. apply (pol_fa E0 FSB0 HR0 s mo1 Pq Dq AK1 Hwf c); [exact HCc| exact H1| exact H2| clear; lia]. }
  assert (NFW : rg_num_freed r <= Z.of_nat (length ws)) by (subst ws; rewrite length_app, length_map; unfold rg_num_freed; clear; lia).
  assert (LWS29 : 4 * Z.of_nat (length ws) <= 2^29) by (rewrite LWS; unfold kFreeArraySize in A7; clear -A7; lia).
  destruct (Z_lt_le_dec (rg_num_freed r) n) as [LTn|GEn].
  2:{ (* [comment removed for export] *)
  set (Q2 := fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' : word) (ds : list word) (m4 : mem),
    ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' yt4 yt5 t6) F (ret_pc ra) fc None m4 (seg_rom asegs)
    /\ munch [(usp - 160, usp); (RP, RP + 24); (RP + 72, RP + 80); (CH, CH + 4 * n); (CA + 80 * c, CA + 80 * c + 4)] m1 m4 /\ wmono asegs m1 m4
    /\ mem_inv asegs m4 /\ stk asegs m4 lo usp
    /\ rw_cells asegs m4 RP (rrow 0 (rg_num_freed r - n) (rg_mapped_fa r) (rg_alloc_user r) (rg_mapped_user r) (na + n) (rg_n_freed r))
    /\ u32arr asegs m4 FA ws /\ u32arr asegs m4 CH ds /\ length ds = 16%nat
    /\ (forall j, (j < Z.to_nat n)%nat -> nth_error ds j = nth_error ws (Z.to_nat (rg_num_freed r - n) + j)%nat)
    /\ rw_cells asegs m4 (CA + 80 * c) [C4 (Z_to_bv 64 n); C4 (Z_to_bv 64 (ic_max_count c)); C8 (Z_to_bv 64 (ic_class_size c))]).
  eapply (rzA_seg_cfg asegs (aSc s) (aNc s) (aEBc s) P1 Q2); [| exact KIP1'|].
  { apply LOCKSTEP. intros m2 fj MUL WML MI2 SK2 FRL RROWL.
    assert (FARR2 : u32arr asegs m2 FA ws).
    { eapply u32arr_transport; [exact FARR1| exact MUL| exact WML|]. rewrite U1. cbn [disjoint_from]. subst FA usp1. rewrite HRP'.
      unfold free_array, region_beg, kRegionSize, kFreeArrayOffset, kFreeArraySize, kSpaceSize in *. rewrite KHB in WE2. clear -LWS A5 A7 HC30 WE2 WE3 WE4 WE5 LOC LO CR. repeat split; try exact I; lia. }
    assert (CARR2 : u32arr asegs m2 CH cjunk).
    { eapply u32arr_transport; [exact CARR1| exact MUL| exact WML|]. rewrite U1, CLEN. cbn [disjoint_from]. subst CH usp1. rewrite HRP'.
      unfold kSpaceSize in WE4. clear -HC30 WE3 WE4 WE19 Thi LOC LO. repeat split; try exact I; lia. }
    eapply evtA_cut.
    { eapply (gfa_direct P1 (Z_to_bv 64 0x37a30) (Z_to_bv 64 (usp + -32)) gp tp F fc lo A_INST (CA + 2560) c CH n SB RI RP FA
                eq_refl eq_refl LOC ltac:(rewrite U1; subst usp1; clear -LO; lia) HC30 ltac:(clear -HR; lia) HSB HRI HCH HCS PSTK1 PRO1 PRI1 PCH1
                s2 s10 s11 yt3 yt4 yt5 t6 (Z_to_bv 64 (CA + 80 * c)) (Z_to_bv 64 n) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 fj m2
                (rg_num_freed r) (rg_mapped_fa r) (rg_alloc_user r) (rg_mapped_user r) na (rg_n_freed r) ws cjunk
                MI2 SK2 FRL RROWL FARR2 GEn NFW LWS29 PFA1 CARR2 CLEN NA). }
    cbv beta. intros ms3 (zt0 & zt1 & zt2 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & zt3 & m3 & ds & -> & MU3 & WM3 & MI3 & SK3 & RROW3 & FARR3 & CARR3 & LDS & DSlo & DShi).
    (* [comment removed for export] *)
    assert (FR3 : rw_cells asegs m3 (usp + -32) [CB 8 j8; C8 s1; C8 s0; C8 ra]).
    { eapply rw_cells_transport; [eapply rw_cells_transport; [exact FR1| exact MUL| exact WML|]| exact MU3| exact WM3|];
        rewrite ?U1; unfold gfa_W; rewrite ?U1; cbn [disjoint_from cells_size csize Nat.add Nat.mul]; subst usp1 CH; rewrite HRP';
        unfold kSpaceSize in WE4; clear -HC30 HR WE3 WE4 WE5 WE19 Thi LOC LO; repeat split; try exact I; lia. }
    assert (PCB3 : rw_cells asegs m3 (CA + 80 * c) [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 (ic_max_count c)); C8 (Z_to_bv 64 (ic_class_size c))]).
    { pose proof (ROWS1 c ltac:(clear -HC30; lia)) as X. cbv beta in X. rewrite CE in X. cbn [zlen length Z.of_nat] in X.
      eapply rw_cells_transport; [eapply rw_cells_transport; [exact X| exact MUL| exact WML|]| exact MU3| exact WM3|];
        rewrite ?U1; unfold gfa_W; rewrite ?U1; cbn [disjoint_from cells_size csize Nat.add Nat.mul]; subst usp1 CH; rewrite HRP';
        unfold kSpaceSize in WE4; clear -HC30 HR WE3 WE4 WE5 WE19 Thi LOC LO; repeat split; try exact I; lia. }
    assert (PSTK1' : forall y k, lo <= y -> y + Z.of_nat k <= usp + 48 -> P1 (Z_to_bv 64 y, k)).
    { intros y k H1 H2. unfold P1, AF_caT.PP. apply (pol_stack' E0 FSB0 HR0 s mo1 AK1 WE ENV0); clear -H1 H2 LOC SPH CR; lia. }
    assert (PCA1 : forall y k, CA <= y -> y + Z.of_nat k <= CA + 2584 -> P1 (Z_to_bv 64 y, k)).
    { intros y k H1 H2. unfold P1, AF_caT.PP. apply (pol_thread' E0 FSB0 HR0 s mo1 AK1 WE); clear -H1 H2; lia. }
    replace (ret_pc (Z_to_bv 64 0x37a30)) with (Z_to_bv 64 227888) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    eapply evtA_cut.
    { eapply (refill_back P1 gp tp F fc lo usp CA c (CA + 80 * c) eq_refl LOC ltac:(clear -LO; lia) HC30 HCA PSTK1' PCA1 1);
      [exact MI3| rewrite U1 in SK3; subst usp1; replace (usp + -32) with (usp - 32) by (clear; lia); exact SK3| exact FR3| exact PCB3| right; reflexivity]. }
    cbv beta. intros ms4 (wt0 & wt1 & wt2 & wa1 & wa2' & wa3 & wa4 & wa5 & wa6 & wa7 & wt3 & m4 & -> & MU4 & WM4 & MI4 & SK4 & PCB4).
    apply evtA_done. unfold Q2. do 13 eexists. split; [reflexivity|].
    assert (MU14 : munch [(usp - 160, usp); (RP, RP + 24); (RP + 72, RP + 80); (CH, CH + 4 * n); (CA + 80 * c, CA + 80 * c + 4)] m1 m4).
    { rewrite ?U1 in MUL. unfold gfa_W in MU3. rewrite ?U1 in MU3. subst usp1.
      eapply munch_trans; [eapply munch_weaken; [| exact MUL]| eapply munch_trans; [eapply munch_weaken; [| exact MU3]| eapply munch_weaken; [| exact MU4]]];
        unfold sub_fp; cbn [outside]; clear -HR; intros x Hx; repeat split; try exact I; lia. }
    assert (WM14 : wmono asegs m1 m4) by (eapply wmono_trans; [exact WML| eapply wmono_trans; [exact WM3| exact WM4]]).
    split; [exact MU14|]. split; [exact WM14|]. split; [exact MI4|]. split; [exact SK4|].
    split.
    { eapply rw_cells_transport; [exact RROW3| exact MU4| exact WM4|]. unfold rrow. cbn [disjoint_from cells_size csize Nat.add Nat.mul]. rewrite HRP'.
      unfold kSpaceSize in WE4. clear -HC30 WE3 WE4 WE5 WE19 Thi LOC LO. repeat split; try exact I; lia. }
    split.
    { eapply u32arr_transport; [exact FARR3| exact MU4| exact WM4|]. cbn [disjoint_from]. subst FA.
      unfold free_array, region_beg, kRegionSize, kFreeArrayOffset, kFreeArraySize, kSpaceSize in *. clear -LWS A5 A7 HC30 WE3 WE4 WE5 WE19 Thi LOC LO. repeat split; try exact I; lia. }
    split.
    { eapply u32arr_transport; [exact CARR3| exact MU4| exact WM4|]. rewrite LDS. cbn [disjoint_from]. subst CH. clear -HC30 Thi LOC LO. repeat split; try exact I; lia. }
    split; [exact LDS|]. split; [exact DSlo|]. change (1 =? 1) with true in PCB4. cbv iota in PCB4. exact PCB4. }
  (* [comment removed for export] *)
  intros ms4 mo4 HQ4 AG4 KIP4.
  destruct HQ4 as (wt0 & wt1 & wt2 & wa1 & wa2' & wa3 & wa4 & wa5 & wa6 & wa7 & wt3 & ds & m4 & -> & MU14 & WM14 & MI4 & SK4 & RROW4 & FARR4 & CARR4 & LDS & DSlo & PCB4).
  pose proof (magree_frame _ _ AG4) as (Ffds4 & Fvm4 & Flz4 & Ffs4 & Fh4 & Ftid4 & _).
  destruct KIP4 as [KIA4 _].
  pose proof (ATOK_magree _ _ _ _ _ _ _ _ _ _ _ ATK1 AG4 KIA4) as ATK4.
  pose proof (AKern_frame _ _ _ _ Fvm4 Flz4 AK1) as AK4.
  set (a1 := upd_cache_inited true a). set (a' := refill_fin c n a1).
  assert (GR1 : forall c', get_region a1 c' = get_region a c') by (intros c'; apply get_region_upd_cache_inited).
  assert (NFn : (Z.to_nat n <= length (rg_free (get_region a1 c)))%nat) by (rewrite GR1; fold (region_of a c); fold r; unfold rg_num_freed in GEn; clear -GEn HR; lia).
  apply (CONT wt0 wt1 wt2 wa1 wa2' wa3 wa4 wa5 wa6 wa7 wt3 yt4 yt5 t6 m4 mo4 a').
  unfold refill_post. cbv zeta.
  split; [exact SK4|].
  split; [exact (wmono_trans _ _ _ _ WM1 WM14)|].
  split.
  { (* [comment removed for export] *)
    exists (((usp - 32, usp) :: ic_W CA) ++ [(usp - 160, usp); (RP, RP + 24); (RP + 72, RP + 80); (CH, CH + 4 * n); (CA + 80 * c, CA + 80 * c + 4)]).
    split; [eapply munch_app; [exact MU1| exact MU14]|].
    assert (ICW : Forall (fun iv => CA + 84 <= fst iv /\ snd iv <= CA + 2496) (ic_W CA)) by (unfold ic_W; repeat (constructor; [cbn [fst snd]; clear; lia|]); constructor).
    Ltac thrW := right; right; left; exists (T + kThrCache, kPerClassSize * kNumClasses); split;
                 [unfold arep_thr_ranges; do 3 right; left; reflexivity| cbn [fst snd]; unfold kThrCache, kPerClassSize, kNumClasses].
    Ltac rsvW HRP' WE3 WE4 HC30 := do 3 right; left; cbn [fst snd]; rewrite HRP'; unfold kResvLen, kSpaceSize in *; clear -WE3 WE4 HC30; lia.
    split.
    { apply Forall_app. split.
      - constructor; [left; cbn [fst snd]; clear -LO; lia|]. eapply Forall_impl; [| exact ICW]. intros iv [H1 H2]. thrW; clear -H1 H2; lia.
      - constructor; [left; cbn [fst snd]; clear -LO; lia|]. constructor; [rsvW HRP' WE3 WE4 HC30|]. constructor; [rsvW HRP' WE3 WE4 HC30|].
        constructor; [thrW; subst CH; clear -HC30 HR; lia|]. constructor; [thrW; clear -HC30; lia| constructor]. }
    assert (LV : forall blo bsz, In (blo, bsz) (live_blocks a) -> blo + bsz <= lo /\ (blo + bsz <= T \/ T + 4096 <= blo) /\ (blo + bsz <= RP \/ RP + 128 <= blo)).
    { intros blo bsz Hin. pose proof (live_block_off_threadG E0 Pq Dq a blo bsz Hwf Hin) as [L1 L2]. pose proof (live_block_whereG E0 Pq Dq a blo bsz Hwf Hin) as (L3 & _ & _ & L4).
      split; [clear -L1 LOC; lia|]. split; [exact L2|]. rewrite HRP'. destruct L4 as [[L5 L6]|(sc & Hsc & L5 & L6)].
      - left. unfold kSpaceSize in L6. clear -L6 HC30. lia.
      - destruct (WS3 sc Hsc) as (_ & _ & _ & _ & _ & _ & RSV). pose proof (RSV _ WE7) as X. cbn [fst snd] in X. unfold kSpaceSize in *. clear -X L3 L5 L6 WE3 WE4 HC30. lia. }
    apply Forall_forall. intros iv Hiv blo bsz Hin. destruct (LV blo bsz Hin) as (L1 & L2 & L3).
    apply in_app_iff in Hiv. destruct Hiv as [Hiv|Hiv].
    - destruct Hiv as [<-|Hiv]; [cbn [fst snd]; clear -L1 LO; lia|].
      pose proof (proj1 (Forall_forall _ _) ICW iv Hiv) as [H1 H2]. clear -L2 H1 H2. destruct iv; cbn [fst snd] in *. lia.
    - cbn in Hiv. subst CH. destruct Hiv as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd]; [clear -L1 LO; lia| clear -L3; lia| clear -L3; lia| clear -L2 HC30 HR; lia| clear -L2 HC30; lia]. }
  split.
  { (* [comment removed for export] *)
    exists 0%nat, [], [], []. subst a' a1 n. apply (arun_refill_direct E0 c a []). unfold rg_num_freed in GEn |- *. subst r. exact GEn. }
  (* [comment removed for export] *)
  assert (AG14 : forall z, 0 <= z < 2^64 -> ~ (usp - 160 <= z < usp) -> (forall i, 1 <= i <= 31 -> ~ (CA + 80 * i + 4 <= z < CA + 80 * i + 16)) ->
                 ~ (CH <= z < CH + 4 * n) -> ~ (CA + 80 * c <= z < CA + 80 * c + 4) -> ~ (RP <= z < RP + 24) -> ~ (RP + 72 <= z < RP + 80) ->
                 m4 (wa z) = m (wa z)).
  { intros z Hz N1 N2 N3 N4 N5 N6. rewrite <- (AGB1 z Hz ltac:(subst usp1; clear -N1; lia) N2). apply MU14. rewrite wa_unsigned by exact Hz.
    cbn [outside]. clear -N1 N3 N4 N5 N6. tauto. }
  assert (ARUN : arun 0%nat (refill E0 c a) [] = Some (a', ONorm true, [], [])).
  { subst a' a1 n. apply (arun_refill_direct E0 c a []). unfold rg_num_freed in GEn |- *. subst r. exact GEn. }
  assert (ROOM1 : room a c) by exact (proj1 ROOM).
  pose proof (hoare_arun _ _ _ a 0%nat [] a' true [] [] (refill_spec E0 Pq Dq a c HCc Hwf CE ROOM1) eq_refl ARUN) as (WF' & CI' & PF' & CV' & GC' & NE').
  (* [comment removed for export] *)
  Ltac to4 AG14 H := eapply rw_cells_agree; [| exact H]; cbn [cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul length];
                     intros z Hz; apply AG14.
  split.
  { (* [comment removed for export] *)
    unfold RINV.
    assert (Tfacts : forall z, T <= z < T + 4096 -> 0 <= z < 2^64 /\ ~ (usp - 160 <= z < usp) /\ ~ (RP <= z < RP + 24) /\ ~ (RP + 72 <= z < RP + 80)).
    { intros z Hz. rewrite HRP'. unfold kSpaceSize in WE4. clear -Hz Tlo Thi WE3 WE4 WE5 WE19 LOC LO CR HC30. repeat split; lia. }
    assert (AGT4 : forall z, T <= z < T + 4096 -> (forall i, 1 <= i <= 31 -> ~ (CA + 80 * i + 4 <= z < CA + 80 * i + 16)) ->
                   ~ (CH <= z < CH + 4 * n) -> ~ (CA + 80 * c <= z < CA + 80 * c + 4) -> m4 (wa z) = m (wa z)).
    { intros z Hz N2 N3 N4. pose proof (Tfacts z Hz) as (B1 & B2 & B3 & B4). exact (AG14 z B1 B2 N2 N3 N4 B3 B4). }
    Ltac toT AGT4 H := eapply rw_cells_agree; [| exact H]; cbn [cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul length];
                       intros z Hz; apply AGT4.
    split.
    { (* [comment removed for export] *)
      unshelve eapply (ARep_refill asegs E0 Pq Dq a a' m m4 lo c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (gfa_keep c n a1)); try (subst a' a1; first
        [ rewrite fin_chunks | rewrite fin_tq | rewrite fin_gq | rewrite fin_sec | rewrite fin_sec_stats | rewrite fin_ptr | rewrite fin_keys | rewrite fin_frames
        | rewrite fin_node_blocks | rewrite fin_store_blocks | rewrite fin_store_stored | rewrite fin_ndepot | rewrite fin_ia | rewrite fin_cache_allocated
        | rewrite fin_glob_allocated | rewrite fin_glob_mapped | rewrite fin_sec_stale | rewrite fin_oom | rewrite fin_dead ]; reflexivity).
      - intros c' NE. subst a' a1. unfold region_of. rewrite fin_get_region. destruct (decide (c' = c)) as [E|_]; [exfalso; exact (NE E)| apply get_region_upd_cache_inited].
      - intros c' NE. subst a' a1. rewrite fin_get_cache. destruct (decide (c' = c)) as [E|_]; [exfalso; exact (NE E)| apply get_cache_upd_cache_inited].
      - subst a' a1. unfold region_of. rewrite fin_get_region. destruct (decide (c = c)) as [_|NE]; [| exfalso; exact (NE eq_refl)]. cbn [gfa_reg rg_mapped_user]. rewrite GR1. clear; lia.
      - subst a' a1. unfold region_of. rewrite fin_get_region. destruct (decide (c = c)) as [_|NE]; [| exfalso; exact (NE eq_refl)]. cbn [gfa_reg rg_mapped_fa]. rewrite GR1. clear; lia.
      - (* [comment removed for export] *)
        subst a' a1. unfold region_of. rewrite fin_get_region. destruct (decide (c = c)) as [_|NE]; [| exfalso; exact (NE eq_refl)].
        unfold gfa_reg. cbn [rg_free]. rewrite GR1. fold (region_of a c). fold r. unfold gfa_keep. rewrite GR1. fold (region_of a c). fold r.
        rewrite firstn_firstn, Nat.min_id, length_firstn. clear -NFn GR1. split; [reflexivity|]. rewrite GR1 in NFn. fold (region_of a c) in NFn. fold r in NFn. split; lia.
      - exact HCc.
      - exact Hwf.
      - exact WF'.
      - exact (wmono_trans _ _ _ _ WM1 WM14).
      - (* [comment removed for export] *)
        intros z Hz NF. apply AG14; [exact Hz| intros X| intros i Hi X| intros X| intros X| intros X| intros X]; apply NF; unfold FPWref.
        + left. clear -X LO. lia.
        + do 2 right; left. exists i. split; [clear -Hi; unfold kNumClasses; lia| unfold kThrCache, kPerClassSize; clear -X; lia].
        + do 3 right; left. subst CH. unfold kThrCache, kPerClassSize. clear -X HR. lia.
        + do 3 right; left. unfold kThrCache, kPerClassSize. clear -X. lia.
        + right; left. subst RP. unfold kRegSize in *. clear -X. lia.
        + right; left. subst RP. unfold kRegSize in *. clear -X. lia.
      - exact LOC.
      - exact Hrep.
      - exact (blocks_sep_ofG E0 Pq Dq a mo ENV0 Hwf Hkern).
      - clear -Tlo Thi Timg. repeat split; lia.
      - intros x Hx. pose proof (IMGR x Hx) as X. rewrite EI1. clear -X EI2. lia.
      - rewrite EI1. clear; lia.
      - exact IMGR.
      - exists mo. exact Hkern.
      - exact TDN.
      - (* [comment removed for export] *)
        subst a' a1. unfold region_of. rewrite fin_get_region. destruct (decide (c = c)) as [_|NE]; [| exfalso; exact (NE eq_refl)].
        unfold gfa_reg, region_cells. cbn [rg_mapped_fa rg_alloc_user rg_mapped_user rg_n_allocated rg_n_freed rg_free]. unfold rg_num_freed. cbn [rg_free].
        rewrite GR1. fold (region_of a c). fold r. unfold gfa_keep. rewrite GR1. fold (region_of a c). fold r. rewrite length_firstn.
        replace (Z.of_nat ((length (rg_free r) - Z.to_nat n) `min` length (rg_free r))) with (rg_num_freed r - n) by (unfold rg_num_freed in *; clear -GEn HR; lia).
        fold RP. unfold rrow in RROW4. subst na. rewrite (zw_mod_add (rg_n_allocated r) n) in RROW4. unfold rrow, AsanRep.zw, AsanRep.zb, zeros. cbn [repeat]. exact RROW4.
      - (* [comment removed for export] *)
        intros i Hi NE. subst a' a1. unfold percls_cells. rewrite fin_get_cache, fin_cache_inited. destruct (decide (i = c)) as [E|_]; [exfalso; exact (NE E)|].
        rewrite get_cache_upd_cache_inited. cbn [as_cache_inited upd_cache_inited]. unfold kNumClasses in Hi.
        destruct (Z.eq_dec i 0) as [->|NZ].
        + (* [comment removed for export] *)
          destruct (Tcache 0 ltac:(unfold kNumClasses; clear; lia)) as [X0 _]. unfold percls_cells in X0.
          replace (row_max_count 0) with 0 in X0 |- * by reflexivity. replace (row_class_size 0) with 0 in X0 |- * by reflexivity.
          replace (if as_cache_inited a then 0 else 0) with 0 in X0 by (destruct (as_cache_inited a); reflexivity).
          unfold kThrCache, kPerClassSize in X0 |- *. toT AGT4 X0; [clear -Hz; lia| intros j Hj Cj; clear -Hz Hj Cj; lia| subst CH; clear -Hz HC30 HR; lia| clear -Hz HC30; lia].
        + pose proof (ROWS1 i ltac:(clear -Hi NZ; lia)) as X. cbv beta in X. rewrite get_cache_upd_cache_inited || idtac.
          unfold row_max_count, row_class_size. unfold ic_max_count, ic_class_size in X. unfold kThrCache, kPerClassSize. replace (T + 208 + 80 * i) with (CA + 80 * i) by (clear; lia).
          eapply rw_cells_transport; [exact X| exact MU14| exact WM14|]. cbn [disjoint_from cells_size csize Nat.add Nat.mul]. subst CH. rewrite HRP'.
          unfold kSpaceSize in WE4. clear -Hi NZ NE HC30 HR Tlo Thi WE3 WE4 WE5 WE19 LOC LO. repeat split; try exact I; lia.
      - (* [comment removed for export] *)
        subst a' a1. unfold percls_cells. rewrite fin_get_cache, fin_cache_inited. destruct (decide (c = c)) as [_|NE]; [| exfalso; exact (NE eq_refl)].
        cbn [as_cache_inited upd_cache_inited]. unfold row_max_count, row_class_size. unfold ic_max_count, ic_class_size in PCB4.
        replace (zlen (gfa_hi c n (upd_cache_inited true a))) with n by (unfold gfa_hi, gfa_keep, zlen; rewrite length_skipn, GR1; fold (region_of a c); fold r; unfold rg_num_freed in GEn; clear -GEn HR; lia).
        unfold kThrCache, kPerClassSize. replace (T + 208 + 80 * c) with (CA + 80 * c) by (clear; lia). split; [exact PCB4|].
        exists (skipn (Z.to_nat n) ds). split.
        + replace (CA + 80 * c + 16) with CH by (subst CH; clear; lia).
          replace (map AsanRep.zw (gfa_hi c n (upd_cache_inited true a)) ++ skipn (Z.to_nat n) ds) with ds; [exact CARR4|].
          rewrite <- (firstn_skipn (Z.to_nat n) ds) at 1. f_equal. unfold gfa_hi, gfa_keep. rewrite GR1. fold (region_of a c). fold r.
          apply nth_error_ext'. intros j. destruct (Nat.lt_ge_cases j (Z.to_nat n)) as [LT|GE].
          * rewrite nth_error_firstn. replace (j <? Z.to_nat n)%nat with true by (symmetry; apply Nat.ltb_lt; exact LT). cbv iota.
            rewrite (DSlo j LT). subst ws. rewrite nth_error_map, nth_error_skipn.
            rewrite nth_error_app1 by (rewrite length_map; unfold rg_num_freed in *; clear -GEn HR LT; lia). rewrite nth_error_map.
            replace (Z.to_nat (rg_num_freed r - n) + j)%nat with (length (rg_free r) - Z.to_nat n + j)%nat by (unfold rg_num_freed in *; clear -GEn HR; lia). reflexivity.
          * rewrite (proj2 (nth_error_None _ _)) by (rewrite length_firstn, LDS; clear -GE HR; lia).
            symmetry. apply (proj2 (nth_error_None _ _)). rewrite length_map, length_skipn. unfold rg_num_freed in GEn. clear -GE GEn HR. lia.
        + unfold gfa_hi, gfa_keep. rewrite length_skipn, length_skipn, GR1, LDS. fold (region_of a c). fold r. clear -NFn GR1 HR GEn. unfold rg_num_freed in GEn. lia.
      - (* [comment removed for export] *)
        subst a' a1. rewrite fin_cache_mapped. cbn [as_cache_mapped upd_cache_inited].
        pose proof (AF_kit3.rwc_split asegs m _ [C8 (AsanRep.zw (as_cache_allocated a))] [C8 (AsanRep.zw (as_cache_mapped a))] Tcst) as [_ X].
        cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in X. unfold kThrCacheStats in X |- *. replace (T + (208 + 2560) + 16 + 8) with (T + (208 + 2560) + 24) in X by (clear; lia).
        toT AGT4 X; [clear -Hz; lia| intros j Hj Cj; clear -Hz Hj Cj; lia| subst CH; clear -Hz HC30 HR; lia| clear -Hz HC30; lia].
      - (* [comment removed for export] *)
        subst a' a1. rewrite fin_ts. cbn [as_ts upd_cache_inited].
        pose proof (AF_tkit.u64arr_cell m _ _ 9 _ Tst eq_refl) as X9. pose proof (AF_tkit.u64arr_cell m _ _ 10 _ Tst eq_refl) as X10.
        pose proof (AF_kit3.rwc_join_at asegs m _ _ _ _ X9 X10 ltac:(cbn; clear; lia)) as X. cbn [app] in X. unfold kThrStats in X |- *.
        replace (T + 2800 + 8 * Z.of_nat 9) with (T + 2800 + 72) in X by (clear; lia).
        toT AGT4 X; [clear -Hz; lia| intros j Hj Cj; clear -Hz Hj Cj; lia| subst CH; clear -Hz HC30 HR; lia| clear -Hz HC30; lia].
      - subst a' a1. rewrite fin_ts. apply ts_nomap_agree_refl.
      - (* [comment removed for export] *)
        subst a' a1. unfold region_of. rewrite fin_get_region. destruct (decide (c = c)) as [_|NE]; [| exfalso; exact (NE eq_refl)]. cbn [gfa_reg rg_mapped_user]. rewrite GR1.
        eapply wr_at_transport; [exact UMAP| exact (wmono_trans _ _ _ _ WM1 WM14)].
      - (* [comment removed for export] *)
        subst a' a1. unfold region_of. rewrite fin_get_region. destruct (decide (c = c)) as [_|NE]; [| exfalso; exact (NE eq_refl)].
        unfold gfa_reg. cbn [rg_free rg_mapped_fa]. rewrite GR1. fold (region_of a c). fold r. unfold gfa_keep. rewrite GR1. fold (region_of a c). fold r.
        exists (map AsanRep.zw (skipn (length (rg_free r) - Z.to_nat n) (rg_free r)) ++ fjunk). split.
        + rewrite app_assoc, <- map_app, firstn_skipn. fold FA. exact FARR4.
        + rewrite length_app, length_map, length_skipn, length_firstn. rewrite <- FAL. clear -GEn HR. unfold rg_num_freed in GEn. lia.
      - (* [comment removed for export] *)
        subst a' a1. unfold region_of. rewrite fin_get_region. destruct (decide (c = c)) as [_|NE]; [| exfalso; exact (NE eq_refl)]. cbn [gfa_reg rg_mapped_user]. rewrite GR1.
        fold (region_of a c). fold r. rewrite Z.sub_diag. cbn [Z.div Z.to_nat repeat]. apply AF_popT.rw_cells_CB0; unfold kShadowBase; clear -WE2 WE3 WE4 WE5 A1 A3 A5 A7 HC30 CR KHB; unfold free_array, region_beg, kRegionSize, kFreeArrayOffset, kFreeArraySize, kSpaceSize in *; rewrite ?KHB in *; Z.div_mod_to_equations; lia.
      - subst a' a1. unfold region_of. rewrite fin_get_region. destruct (decide (c = c)) as [_|NE]; [| exfalso; exact (NE eq_refl)]. cbn [gfa_reg rg_mapped_fa]. rewrite GR1.
        fold (region_of a c). fold r. rewrite Z.sub_diag. cbn [Z.div Z.to_nat repeat]. apply AF_popT.rw_cells_CB0; unfold kShadowBase; clear -WE2 WE3 WE4 WE5 A1 A3 A5 A7 HC30 CR KHB; unfold free_array, region_beg, kRegionSize, kFreeArrayOffset, kFreeArraySize, kSpaceSize in *; rewrite ?KHB in *; Z.div_mod_to_equations; lia. }
    split; [exact WF'|].
    split; [subst a' a1; apply fin_AKern; apply inited_AKern; exact AK4|].
    split; [subst a' a1; unfold res_ok in *; rewrite fin_residue, fin_sec; cbn [as_residue as_sec upd_cache_inited]; exact Hres|].
    split; [subst a' a1; unfold AQbound in *; rewrite tq_bytes_fin, gq_bytes_fin; exact Hqb|].
    split; [subst a' a1; unfold depot_inv, depot_n_ids, dphi in *; rewrite ?fin_keys, ?fin_frames, ?fin_ndepot, ?fin_node_blocks, ?fin_store_blocks, ?fin_store_stored; exact Hdi|].
    split; [exact MI4|].
    split.
    { eapply rt_misc5_agree; [exact Hrt|]. intros z Hz.
      pose proof (resv_range_num E0 c0 cl CR0 ltac:(clear -CC1 CC2; lia)) as (CQ1 & CQ2 & CQ3 & CQ4).
      pose proof (resv_range_num E0 d0 dl DR0 ltac:(clear -DD1 DD2; lia)) as (DQ1 & DQ2 & DQ3 & DQ4).
      pose proof CR0 as (_ & _ & _ & CQ5 & _). pose proof DR0 as (_ & _ & _ & DQ5 & _).
      destruct (rt_fpc_where E0 FSB0 PL0 z Hz) as [(Z1 & _ & _ & _)|RH].
      - apply AG14; [clear -Z1; lia| clear -Z1 LOC LO CR; lia| apply OFFT; clear -Z1 Timg; lia| subst CH; clear -Z1 Timg HC30 HR; lia| clear -Z1 Timg HC30; lia
               | rewrite HRP'; rewrite KHB in WE2; clear -Z1 WE2 WE3 HC30; lia| rewrite HRP'; rewrite KHB in WE2; clear -Z1 WE2 WE3 HC30; lia].
      - unfold rt_high2 in RH. apply AG14.
        + clear -RH Tlo Thi CQ1 CQ2 DQ1 DQ2 CC1 CC2 DD1 DD2 CR; lia.
        + clear -RH Thi CQ2 DQ2 CC1 CC2 DD1 DD2 LOC LO; lia.
        + intros i Hi Ci. clear -RH Hi Ci CT DT CC1 CC2 DD1 DD2; lia.
        + subst CH; clear -RH HC30 HR CT DT CC1 CC2 DD1 DD2; lia.
        + clear -RH HC30 CT DT CC1 CC2 DD1 DD2; lia.
        + rewrite HRP'. unfold kResvLen, kSpaceSize in *. clear -RH WE3 WE4 WE19 CQ5 DQ5 CC1 CC2 DD1 DD2 HC30; lia.
        + rewrite HRP'. unfold kResvLen, kSpaceSize in *. clear -RH WE3 WE4 WE19 CQ5 DQ5 CC1 CC2 DD1 DD2 HC30; lia. }
    split; [subst a' a1; unfold sstats_ok, sec_bytes in *; rewrite fin_sec_stats, fin_sec; exact Hss|].
    subst a' a1; unfold csmall in *. rewrite fin_chunks. exact Hcs. }
  split.
  { (* [comment removed for export] *)
    rewrite <- (sA_self s) in TOK. fold a in TOK.
    pose proof (RTOK_magree _ _ _ _ _ _ _ _ _ _ _ TOK (magree_trans _ _ _ AG1 AG4) KIA4) as TOK4.
    apply (RTOK_same_fp E0 FSB0 HR0 L0 RES0 EB0 C C' s a a' mo4 TOK4).
    - eapply same_fp_trans; [apply same_fp_inited| apply (fin_same_fp E0 c n a1 HC30)].
    - subst a' a1. rewrite fin_nprim. reflexivity.
    - subst a' a1. rewrite fin_ndepot. reflexivity. }
  split; [rewrite Ffs4, Ffs1; reflexivity|]. split; [rewrite Ffds4, Ffds1; reflexivity|]. split; [rewrite Ftid4, Ftid1; reflexivity|].
  split.
  { (* [comment removed for export] *)
    subst a' a1. unfold refill_same.
    rewrite fin_chunks, fin_dead, fin_tq, fin_gq, fin_sec, fin_sec_stale, fin_sec_stats, fin_ptr, fin_keys, fin_frames, fin_ndepot, fin_nprim, fin_residue,
            fin_node_blocks, fin_store_blocks, fin_store_stored, fin_ia, fin_cache_allocated, fin_everc, fin_glob_allocated, fin_glob_mapped, fin_oom.
    destruct a; repeat split; reflexivity. }
  split.
  { intros c' NE. subst a' a1. rewrite fin_get_cache, fin_get_region. destruct (decide (c' = c)) as [E|_]; [exfalso; exact (NE E)|].
    split; [apply get_cache_upd_cache_inited| apply get_region_upd_cache_inited]. }
  split; [subst a' a1; rewrite fin_cache_inited; reflexivity|].
  subst a' a1. apply fin_zlen_cache; [clear -HR; lia| exact NFn]. }
  (* [comment removed for export] *)
  set (req := n - rg_num_freed r).
  assert (NF0 : 0 <= rg_num_freed r) by (unfold rg_num_freed; clear; lia).
  (* [comment removed for export] *)
  set (Q2 := fun ms' => exists (m2 : mem) (fj : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x37dac) (Z_to_bv 64 (usp - 160)) gp tp (Z_to_bv 64 0) (Z_to_bv 64 kMtxWriter) (Z_to_bv 64 0) (Z_to_bv 64 RP) (Z_to_bv 64 A_INST)
                  (Z_to_bv 64 A_INST) (Z_to_bv 64 (CA + 2560)) (Z_to_bv 64 c) (Z_to_bv 64 RP) (Z_to_bv 64 req) (Z_to_bv 64 (rg_num_freed r)) (Z_to_bv 64 (-1)) (Z_to_bv 64 0)
                  (Z_to_bv 64 (RP + 8)) (Z_to_bv 64 0x2000000000000000) (Z_to_bv 64 FA) (Z_to_bv 64 CH) (Z_to_bv 64 n)
                  (Z_to_bv 64 kMtxWriter) (Z_to_bv 64 1500) (Z_to_bv 64 0xdfffffffffffffff) s10 s11 yt3 yt4 yt5 t6)
             F (Z_to_bv 64 A_POPULATE) fc None m2 (seg_rom asegs)
    /\ munch [(usp - 160, usp - 32); (RP, RP + 8)] m1 m2 /\ wmono asegs m1 m2 /\ mem_inv asegs m2 /\ stk asegs m2 lo (usp - 160)
    /\ rw_cells asegs m2 (usp - 160) [CB 24 fj; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 (CA + 80 * c)); C8 (Z_to_bv 64 0x37a30)]
    /\ rw_cells asegs m2 RP (rrow kMtxWriter (rg_num_freed r) (rg_mapped_fa r) (rg_alloc_user r) (rg_mapped_user r) na (rg_n_freed r))).
  eapply (rzA_seg_cfg asegs (aSc s) (aNc s) (aEBc s) P1 Q2); [| exact KIP1'|].
  { apply LOCKSTEP. intros m2 fj MUL WML MI2 SK2 FRL RROWL.
    eapply evtA_cut.
    { eapply (gfa_to_pop P1 (Z_to_bv 64 0x37a30) (Z_to_bv 64 (usp + -32)) gp tp F fc lo A_INST (CA + 2560) c CH n SB RI RP FA eq_refl eq_refl LOC HC30 ltac:(clear -HR; lia) HSB HRI HCH PRI1
                s2 s10 s11 yt3 yt4 yt5 t6 m2 (rg_num_freed r) (rg_mapped_fa r) (rg_alloc_user r) (rg_mapped_user r) na (rg_n_freed r)
                MI2 RROWL (conj NF0 LTn)). }
    cbv beta. intros ms3 ->. apply evtA_done. unfold Q2. exists m2, fj.
    rewrite U1 in MUL, SK2, FRL |- *. subst usp1. replace (usp - 32 - 128) with (usp - 160) in MUL by (clear; lia). replace (usp - 32 + -128) with (usp - 160) in SK2, FRL |- * by (clear; lia).
    split; [unfold A_POPULATE, gfa_at_pop; subst req; reflexivity|].
    split; [exact MUL|]. split; [exact WML|]. split; [exact MI2|]. split; [exact SK2|]. split; [exact FRL| exact RROWL]. }
  intros ms2 mo2 HQ2 AG2 KIP2.
  destruct HQ2 as (m2 & fj & -> & MUL & WML & MI2 & SK2 & FRL & RROWL).
  pose proof (magree_frame _ _ AG2) as (Ffds2 & Fvm2 & Flz2 & Ffs2 & Fh2 & Ftid2 & _).
  destruct KIP2 as [KIA2 _].
  pose proof (ATOK_magree _ _ _ _ _ _ _ _ _ _ _ ATK1 AG2 KIA2) as ATK2.
  pose proof (AKern_frame _ _ _ _ Fvm2 Flz2 AK1) as AK2.
  set (a1 := upd_cache_inited true a).
  assert (GR1 : forall c', get_region a1 c' = get_region a c') by (intros c'; apply get_region_upd_cache_inited).
  assert (AGB2 : forall z, 0 <= z < 2^64 -> ~ (usp - 160 <= z < usp) -> (forall i, 1 <= i <= 31 -> ~ (CA + 80 * i + 4 <= z < CA + 80 * i + 16)) -> ~ (RP <= z < RP + 8) ->
                 m2 (wa z) = m (wa z)).
  { intros z Hz N1 N2 N3. rewrite <- (AGB1 z Hz ltac:(subst usp1; clear -N1; lia) N2). apply MUL. rewrite wa_unsigned by exact Hz. cbn [outside]. split; [clear -N1; lia| split; [exact N3| exact I]]. }
  (* [comment removed for export] *)
  pose proof (populate_srz E0 FSB0 HR0 L0 RES0 EB0 PL0 HR0_ok ENV0 PL0OK RES0_low) as POP. unfold populate_srz_stmt in POP.
  assert (TOK2 : RTOKc C C' (sA a1 s) mo2).
  { rewrite <- (sA_self s) in TOK. fold a in TOK.
    apply (RTOK_same_fp E0 FSB0 HR0 L0 RES0 EB0 C C' s a a1 mo2); [| apply same_fp_inited| subst a1; reflexivity| subst a1; reflexivity].
    exact (RTOK_magree _ _ _ _ _ _ _ _ _ _ _ TOK (magree_trans _ _ _ AG1 AG2) KIA2). }
  assert (WF1 : AWf E0 Pq Dq a1) by (subst a1; apply init_cache_wf; exact Hwf).
  assert (AK2' : AKern E0 a1 mo2) by (subst a1; apply inited_AKern; exact AK2).
  pose proof ROOM as (RM1 & RM2 & RM3 & RM4 & RM5).
  (* [comment removed for export] *)
  assert (Tfacts2 : forall z, T <= z < T + 4096 -> 0 <= z < 2^64 /\ ~ (usp - 160 <= z < usp) /\ ~ (RP <= z < RP + 8)).
  { intros z Hz. rewrite HRP'. unfold kSpaceSize in WE4. clear -Hz Tlo Thi WE3 WE4 WE5 WE19 LOC LO CR HC30. repeat split; lia. }
  assert (IMGfacts2 : forall z, 0x10000 <= z < 0x603000 -> m2 (wa z) = m (wa z)).
  { intros z Hz. apply AGB2; [clear -Hz; lia| clear -Hz LOC LO CR; lia| apply OFFT; clear -Hz Timg; lia| rewrite HRP'; rewrite KHB in WE2; clear -Hz WE2 WE3 HC30; lia]. }
  assert (TC2 : thread_cells m2 tp 0x601eb8 (fp_ctx PL0) T).
  { pose proof (resv_range_num E0 c0 cl CR0 ltac:(clear -CC1 CC2; lia)) as (CQ1 & CQ2 & CQ3 & CQ4).
    destruct TC as (X1 & X2 & X3 & X4 & X5). unfold thread_cells. rewrite TP in X3 |- *. rewrite unsigned_lit in X3 |- * by (clear; lia).
    split; [eapply rw_cells_agree; [| exact X1]; cbn; intros z Hz; apply IMGfacts2; clear -Hz; lia|].
    split; [eapply rw_cells_agree; [| exact X2]; cbn; intros z Hz; apply IMGfacts2; clear -Hz; lia|].
    split; [eapply rw_cells_agree; [| exact X3]; cbn; intros z Hz; apply IMGfacts2; clear -Hz; lia|].
    split; [eapply rw_cells_agree; [| exact X4]; cbn; intros z Hz; apply IMGfacts2; clear -Hz; lia|].
    eapply rw_cells_agree; [| exact X5]; cbn; intros z Hz. apply AGB2; [clear -Hz CQ1 CQ2 CR CC1 CC2; lia| clear -Hz CQ2 CC1 CC2 LOC LO; lia| apply OFFT; clear -Hz CT CC1 CC2; lia|].
    rewrite HRP'. pose proof CR0 as (_ & _ & _ & CQ5 & _). unfold kResvLen, kSpaceSize in *. clear -Hz CC1 CC2 CQ5 WE3 WE4 HC30. lia. }
  assert (PC2 : pop_cells E0 a1 c m2 fjunk (repeat (Z_to_bv 8 0) (Z.to_nat (kUserMapSize / 8))) (repeat (Z_to_bv 8 0) (Z.to_nat (kFreeArrayMapSize / 8)))).
  { unfold pop_cells. cbv zeta. rewrite !GR1. fold (region_of a c). fold r.
    split.
    { eapply rw_cells_agree; [| exact I1]. cbn. intros z Hz. unfold A_INST in Hz. apply IMGfacts2. clear -Hz; lia. }
    split.
    { fold RP. unfold region_cells, AsanRep.zw, AsanRep.zb, zeros. cbn [List.tl repeat]. rewrite <- (ZBridge.Z_to_bv_mod64 (rg_n_allocated r)). fold na.
      unfold rrow, kMtxWriter in RROWL. exact RROWL. }
    split; [eapply wr_at_transport; [exact UMAP| exact (wmono_trans _ _ _ _ WM1 WML)]|].
    split.
    { fold FA. fold ws.
      eapply u32arr_transport; [exact FARR1| exact MUL| exact WML|]. cbn [disjoint_from]. subst FA usp1. rewrite HRP'.
      unfold free_array, region_beg, kRegionSize, kFreeArrayOffset, kFreeArraySize, kSpaceSize in *. rewrite KHB in WE2. clear -LWS A5 A7 HC30 WE2 WE3 WE4 WE5 LOC LO CR. repeat split; try exact I; lia. }
    split; [unfold zlen; rewrite <- Nat2Z.inj_add; exact FAL|].
    split.
    { (* [comment removed for export] *)
      eapply rw_cells_agree; [| apply (AF_tkit.shadow_join m kShadowBase ((region_beg SB c + rg_mapped_user r) / 8)); [| clear; unfold kUserMapSize; cbn; lia]].
      - cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by (clear; unfold kUserMapSize; cbn; lia). intros z Hz.
        unfold kShadowBase, kUserMapSize, region_beg, kRegionSize, kFreeArrayOffset in *. rewrite KHB in WE2.
        unfold kSpaceSize in *.
        apply AGB2; [clear -Hz WE2 WE3 WE4 WE5 A1 A3 HC30 CR; Z.div_mod_to_equations; lia| clear -Hz WE2 WE3 WE4 WE5 A1 A3 HC30 CR LOC LO; Z.div_mod_to_equations; lia
                    | apply OFFT; clear -Hz WE2 WE3 WE4 WE5 A1 A3 HC30 Tband Tlo CR; Z.div_mod_to_equations; lia| rewrite HRP'; clear -Hz WE2 WE3 WE4 WE5 A1 A3 HC30 CR; Z.div_mod_to_equations; lia].
      - intros g Hg. apply (Rsh g 0). apply (Sh_beyond_user E0 Pq Dq a Hwf c (8 * g) HCc); [| exact RM1]. fold (region_of a c). fold r.
        unfold kUserMapSize, region_beg, kRegionSize in *. clear -Hg A2 WE1 HC30. Z.div_mod_to_equations. lia. }
    split.
    { eapply rw_cells_agree; [| apply (AF_tkit.shadow_join m kShadowBase ((free_array SB c + rg_mapped_fa r) / 8)); [| clear; unfold kFreeArrayMapSize; cbn; lia]].
      - cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by (clear; unfold kFreeArrayMapSize; cbn; lia). intros z Hz.
        unfold kShadowBase, kFreeArrayMapSize, free_array, region_beg, kRegionSize, kFreeArrayOffset, kFreeArraySize in *. rewrite KHB in WE2.
        unfold kSpaceSize in *.
        apply AGB2; [clear -Hz WE2 WE3 WE4 WE5 A5 A7 HC30 CR; Z.div_mod_to_equations; lia| clear -Hz WE2 WE3 WE4 WE5 A5 A7 HC30 CR LOC LO; Z.div_mod_to_equations; lia
                    | apply OFFT; clear -Hz WE2 WE3 WE4 WE5 A5 A7 HC30 Tband Tlo CR; Z.div_mod_to_equations; lia| rewrite HRP'; clear -Hz WE2 WE3 WE4 WE5 A5 A7 HC30 CR; Z.div_mod_to_equations; lia].
      - intros g Hg. apply (Rsh g 0). apply (Sh_beyond_fa E0 Pq Dq a Hwf c (8 * g) HCc); [| exact RM5]. fold (region_of a c). fold r.
        unfold kFreeArrayMapSize, free_array, region_beg, kRegionSize, kFreeArrayOffset in *. clear -Hg A6 WE1 HC30. Z.div_mod_to_equations. lia. }
    split.
    { pose proof (AF_tkit.u64arr_cell m _ _ 9 _ Tst eq_refl) as X9. pose proof (AF_tkit.u64arr_cell m _ _ 10 _ Tst eq_refl) as X10.
      pose proof (AF_kit3.rwc_join_at asegs m _ _ _ _ X9 X10 ltac:(cbn; clear; lia)) as X. cbn [app] in X. unfold kThrStats in X |- *.
      replace (T + 2800 + 8 * Z.of_nat 9) with (T + 2800 + 72) in X by (clear; lia). subst a1. cbn [as_ts upd_cache_inited].
      eapply rw_cells_agree; [| exact X]. cbn. intros z Hz. pose proof (Tfacts2 z ltac:(clear -Hz Tlo; lia)) as (B1 & B2 & B3).
      apply AGB2; [exact B1| exact B2| intros i Hi Ci; clear -Hz Hi Ci; lia| exact B3]. }
    pose proof (AF_kit3.rwc_split asegs m _ [C8 (AsanRep.zw (as_cache_allocated a))] [C8 (AsanRep.zw (as_cache_mapped a))] Tcst) as [_ X].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in X. unfold kThrCacheStats in X |- *. subst a1. cbn [as_cache_mapped upd_cache_inited].
    replace (T + (208 + 2560) + 16 + 8) with (T + (208 + 2560) + 24) in X by (clear; lia).
    eapply rw_cells_agree; [| exact X]. cbn. intros z Hz. pose proof (Tfacts2 z ltac:(clear -Hz Tlo; lia)) as (B1 & B2 & B3).
    apply AGB2; [exact B1| exact B2| intros i Hi Ci; clear -Hz Hi Ci; lia| exact B3]. }
  assert (PST2 : pop_statics m2) by (apply (pop_statics_agree m m2 PST IMGfacts2)).
  replace (Z_to_bv 64 (CA + 2560)) with (Z_to_bv 64 (T + kThrCacheStats)) by (unfold kThrCacheStats; apply f_equal; clear; lia).
  change (Z_to_bv 64 RP) with (Z_to_bv 64 (RI + kRegSize * c)).
  eapply (POP _ (Z_to_bv 64 (usp - 160)) gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 mo2 (sA a1 s) Pq Dq c req lo C C' fjunk _ _ K KN);
    rewrite ?aps_alloc_sA, ?unsigned_lit by (clear -USPR SPA LO LOC CR; lia);
    [ exact TOK2 | exact AK2' | exact WF1 | exact HCc | subst req; clear -LTn NF0 HR; lia
    | rewrite GR1; exact RM1 | rewrite GR1; exact RM2 | rewrite GR1; exact RM3 | unfold gapR; subst a1; cbn [as_nprim_ever upd_cache_inited]; rewrite (regions_bytes_same a (upd_cache_inited true a) GR1) || idtac; exact RM4
    | exact SK2 | exact LOC | unfold K_POP; clear -LO; lia | clear -SPA; Z.div_mod_to_equations; lia | clear -SPH; lia | exact MI2 | exact TP | exact T8
    | exact TC2 | exact PC2 | exact PST2 | ].
  (* [comment removed for export] *)
  intros zt0 zt1 zt2 za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 m3 mo3 a2 POST.
  destruct POST as (RUNP & AK3 & TOK3 & Ffs3 & Ffds3 & Ftid3 & SK3 & MI3 & WM23 & MU23 & (fjunk' & PCO) & PST3 & SHU3 & SHF3).
  rewrite ?aps_alloc_sA in RUNP, AK3, SHU3, SHF3, PCO, MU23. rewrite sA_sA in TOK3.
  destruct RUNP as (fuelP & orcP & evsP & orcP' & RUNP).
  pose proof (hoareW_arun _ _ _ a1 _ _ a2 true _ _ (popf_populate E0 c req a1) eq_refl RUNP) as PF. cbv beta in PF.
  pose proof (hoareW_arun _ _ _ a1 _ _ a2 true _ _ (pop_lb_populate E0 c (rg_mapped_user r) (rg_mapped_fa r) req ltac:(subst req; clear -LTn; lia) HCc) ltac:(unfold pop_lb; rewrite GR1; fold (region_of a c) r; clear; split; lia) RUNP) as [GRU GRF]. cbv beta in GRU, GRF.
  destruct (hoare_arun _ _ _ a1 _ _ a2 true _ _ (populate_free_array_spec E0 Pq Dq a1 c req HCc ltac:(subst req; clear -LTn NF0 HR; lia) WF1 eq_refl ltac:(unfold room; rewrite GR1; exact RM1)) eq_refl RUNP)
    as (WF2 & CI2 & (fresh & GROWS) & NFB). specialize (NFB eq_refl). rewrite GR1 in NFB. fold (region_of a c) in NFB. fold r in NFB.
  assert (NFn : n <= rg_num_freed (get_region a2 c)) by (subst req; clear -NFB; lia).
  set (r2 := get_region a2 c) in *.
  pose proof PF as (Pci & Pca & Pcst & Pcal & Pptr & Psec & Psst & Pss & Pga & Pgm & Poom & Pch & Pdd & Ptq & Pgq & Pky & Pfr & Pia & Prs & Pnp & Pnb & Psb & Pstd & Pnd & Pev & Preg & Pts).
  (* [comment removed for export] *)
  destruct (RTOK_elim _ _ _ _ _ _ _ _ _ _ TOK3) as (R3 & R3' & ATK3 & _).
  assert (ENV3 : ENVOK E0 FSB0 (sA a2 s)) by exact (ATOK_ENVOK _ _ _ _ _ _ _ _ _ _ ATK3).
  assert (AK3' : AKern E0 (aps_alloc (sA a2 s)) mo3) by (rewrite aps_alloc_sA; exact AK3).
  set (P3 := PP (sA a2 s) mo3).
  assert (PSTK3 : forall y k, lo <= y -> y + Z.of_nat k <= bv_unsigned (Z_to_bv 64 (usp + -32)) -> P3 (Z_to_bv 64 y, k)).
  { intros y k H1 H2. rewrite U1 in H2. unfold P3, AF_caT.PP. apply (pol_stack' E0 FSB0 HR0 (sA a2 s) mo3 AK3' WE ENV0); clear -H1 H2 LOC SPH CR; subst usp1; lia. }
  assert (PSTK3' : forall y k, lo <= y -> y + Z.of_nat k <= usp + 48 -> P3 (Z_to_bv 64 y, k)).
  { intros y k H1 H2. unfold P3, AF_caT.PP. apply (pol_stack' E0 FSB0 HR0 (sA a2 s) mo3 AK3' WE ENV0); clear -H1 H2 LOC SPH CR; lia. }
  assert (PRO3 : forall y k, 0x10000 <= y -> y + Z.of_nat k <= 0x31000 -> P3 (Z_to_bv 64 y, k)).
  { intros y k H1 H2. unfold P3, AF_caT.PP. apply (pol_img' E0 FSB0 HR0 (sA a2 s) mo3 AK3' WE ENV3 ENV0); clear -H1 H2; lia. }
  assert (PRI3 : forall y k, RI <= y -> y + Z.of_nat k <= RI + 4096 -> P3 (Z_to_bv 64 y, k)).
  { intros y k H1 H2. rewrite HRI in H1, H2. unfold P3, AF_caT.PP. apply (pol_reginfo' E0 FSB0 HR0 (sA a2 s) mo3 WE); clear -H1 H2; lia. }
  assert (PCH3 : forall y k, CH <= y -> y + Z.of_nat k <= CH + 64 -> P3 (Z_to_bv 64 y, k)).
  { intros y k H1 H2. subst CH. unfold P3, AF_caT.PP. apply (pol_thread' E0 FSB0 HR0 (sA a2 s) mo3 AK3' WE); clear -H1 H2 HC30; lia. }
  assert (PCA3 : forall y k, CA <= y -> y + Z.of_nat k <= CA + 2584 -> P3 (Z_to_bv 64 y, k)).
  { intros y k H1 H2. unfold P3, AF_caT.PP. apply (pol_thread' E0 FSB0 HR0 (sA a2 s) mo3 AK3' WE); clear -H1 H2; lia. }
  destruct PCO as (PI3 & PRW3 & PUM3 & PFA3 & PFL3 & PTS3 & PCM3). rewrite ?GR1 in PI3, PRW3, PUM3, PFA3, PFL3. fold r2 in PRW3, PUM3, PFA3, PFL3.
  set (ws2 := map wz (rg_free r2) ++ fjunk') in PFA3.
  assert (LWS2 : 4 * Z.of_nat (length ws2) = rg_mapped_fa r2) by (subst ws2; rewrite length_app, length_map; unfold zlen in PFL3; rewrite <- Nat2Z.inj_add in PFL3; exact PFL3).
  pose proof (proj2 (proj1 (proj2 WF2)) c HCc) as WR2. cbv zeta in WR2. unfold region_of in WR2. fold r2 in WR2.
  destruct WR2 as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12).
  assert (PFA3' : forall y k, FA <= y -> y + Z.of_nat k <= FA + 4 * Z.of_nat (length ws2) -> P3 (Z_to_bv 64 y, k)).
  { intros y k H1 H2. rewrite LWS2 in H2. destruct k as [|k]; [apply AF_popT.acc_ok_empty|].
    unfold P3, AF_caT.PP. apply (pol_fa E0 FSB0 HR0 (sA a2 s) mo3 Pq Dq AK3' ltac:(rewrite aps_alloc_sA; exact WF2) c); rewrite ?aps_alloc_sA; [exact HCc| exact H1| exact H2| clear; lia]. }
  (* [comment removed for export] *)
  assert (AGP : forall z, 0 <= z < 2^64 -> ~ (usp - 160 - K_POP <= z < usp - 160) -> ~ (RP <= z < RP + kRegSize) ->
                ~ (SB <= z < SB + 2^37) -> ~ (kLowAppEnd < z < kHighMemBeg) -> ~ (T + kThrStats + 72 <= z < T + kThrStats + 88) -> ~ (T + kThrCacheStats + 24 <= z < T + kThrCacheStats + 32) ->
                m3 (wa z) = m2 (wa z)).
  { intros z Hz N1 N2 N3 N4 N5 N6. apply MU23. rewrite wa_unsigned by exact Hz. unfold pop_W. cbv zeta. cbn [outside].
    pose proof (RG_any E0 Pq Dq a2 WF2 c ltac:(clear -HC30; lia)) as [[G1 G2] [G3 G4]]. unfold region_of in G1, G2, G3, G4. fold r2 in G1, G2, G3, G4.
    rewrite ?GR1. fold r2. fold (region_of a c). fold r. fold RP.
    unfold free_array, region_beg, kRegionSize, kFreeArrayOffset, kFreeArraySize, kShadowBase in *. rewrite KHB, KLE in N4. rewrite KHB in WE2. unfold kSpaceSize in *.
    split; [clear -N1; lia|]. split; [exact N2|].
    split; [clear -N3 G1 G2 A1 A3 HC30; lia|]. split; [unfold zlen; clear -N3 G3 G4 A5 A7 HC30; lia|].
    split; [clear -N4 G1 G2 A1 A3 HC30 WE2 WE3 WE4 WE5 CR; Z.div_mod_to_equations; lia|].
    split; [clear -N4 G3 G4 A5 A7 HC30 WE2 WE3 WE4 WE5 CR; Z.div_mod_to_equations; lia|].
    split; [exact N5|]. split; [exact N6| exact I]. }
  assert (FR3' : rw_cells asegs m3 (bv_unsigned (Z_to_bv 64 (usp + -32)) + -128)
            [CB 24 fj; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 (CA + 80 * c)); C8 (Z_to_bv 64 0x37a30)]).
  { rewrite U1. subst usp1. replace (usp - 32 + -128) with (usp - 160) by (clear; lia). eapply rw_cells_agree; [| exact FRL].
    cbn [cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul length]. intros z Hz. rewrite HRP' in *.
    apply AGP; [clear -Hz LOC LO CR USPR; lia| unfold K_POP; clear -Hz; lia| unfold kRegSize; clear -Hz WE2 WE3 WE4 WE5 LOC LO CR HC30; unfold kSpaceSize in *; lia
              | clear -Hz WE2 WE3 WE4 WE5 LOC LO CR; unfold kSpaceSize in *; lia| rewrite KHB, KLE; clear -Hz LOC LO CR; lia| unfold kThrStats; clear -Hz Thi LOC LO; lia| unfold kThrCacheStats; clear -Hz Thi LOC LO; lia]. }
  assert (CARR3 : u32arr asegs m3 CH cjunk).
  { assert (CARR2 : u32arr asegs m2 CH cjunk).
    { eapply u32arr_transport; [exact CARR1| exact MUL| exact WML|]. rewrite CLEN. cbn [disjoint_from]. subst CH. rewrite HRP'.
      unfold kSpaceSize in WE4. clear -HC30 WE3 WE4 WE5 WE19 Thi LOC LO. repeat split; try exact I; lia. }
    eapply u32arr_agree; [| exact CARR2]. rewrite CLEN. intros z Hz. subst CH. destruct (Tfacts2 z ltac:(clear -Hz Tlo HC30; lia)) as (B1' & _ & _).
    apply AGP; [exact B1'| unfold K_POP; clear -Hz Thi LOC LO HC30; lia| rewrite HRP'; unfold kRegSize, kSpaceSize in *; clear -Hz WE3 WE4 WE19 HC30; lia
              | unfold kSpaceSize in *; clear -Hz WE3 WE4 WE19 HC30; lia| rewrite KHB, KLE; clear -Hz Tband Tlo HC30; lia| unfold kThrStats; clear -Hz HC30; lia| unfold kThrCacheStats; clear -Hz HC30; lia]. }
  set (na2 := rg_n_allocated r2 mod 2 ^ 64).
  assert (NA2 : 0 <= na2 < 2^64) by (subst na2; apply Z.mod_pos_bound; clear; lia).
  assert (RROW3 : rw_cells asegs m3 RP (rrow kMtxWriter (rg_num_freed r2) (rg_mapped_fa r2) (rg_alloc_user r2) (rg_mapped_user r2) na2 (rg_n_freed r2))).
  { fold RP in PRW3. unfold region_cells, AsanRep.zw, AsanRep.zb, zeros in PRW3. cbn [List.tl repeat] in PRW3. rewrite <- (ZBridge.Z_to_bv_mod64 (rg_n_allocated r2)) in PRW3. fold na2 in PRW3. exact PRW3. }
  assert (NFW2 : rg_num_freed r2 <= Z.of_nat (length ws2)) by (subst ws2; rewrite length_app, length_map; unfold rg_num_freed; clear; lia).
  assert (LWS29' : 4 * Z.of_nat (length ws2) <= 2^29) by (rewrite LWS2; unfold kFreeArraySize in B7; clear -B7; lia).
  set (Q3 := fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' : word) (ds : list word) (m5 : mem),
    ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' zt4 zt5 zt6) F (ret_pc ra) fc None m5 (seg_rom asegs)
    /\ munch [(usp - 160, usp); (RP, RP + 24); (RP + 72, RP + 80); (CH, CH + 4 * n); (CA + 80 * c, CA + 80 * c + 4)] m3 m5 /\ wmono asegs m3 m5
    /\ mem_inv asegs m5 /\ stk asegs m5 lo usp
    /\ rw_cells asegs m5 RP (rrow 0 (rg_num_freed r2 - n) (rg_mapped_fa r2) (rg_alloc_user r2) (rg_mapped_user r2) (na2 + n) (rg_n_freed r2))
    /\ u32arr asegs m5 FA ws2 /\ u32arr asegs m5 CH ds /\ length ds = 16%nat
    /\ (forall j, (j < Z.to_nat n)%nat -> nth_error ds j = nth_error ws2 (Z.to_nat (rg_num_freed r2 - n) + j)%nat)
    /\ rw_cells asegs m5 (CA + 80 * c) [C4 (Z_to_bv 64 n); C4 (Z_to_bv 64 (ic_max_count c)); C8 (Z_to_bv 64 (ic_class_size c))]).
  pose proof (AF_caT.PP_KIP E0 FSB0 HR0 L0 RES0 EB0 (sA a2 s) mo3 R3 R3' ATK3) as KIP3.
  eapply (rzA_seg_cfg asegs (aSc (sA a2 s)) (aNc (sA a2 s)) (aEBc (sA a2 s)) P3 Q3); [| exact KIP3|].
  { replace (ret_pc (Z_to_bv 64 0x37dac)) with (Z_to_bv 64 0x37dac) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    replace (Z_to_bv 64 (usp - 160)) with (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (usp + -32)) + -128)) by (rewrite U1; subst usp1; apply f_equal; clear; lia).
    eapply evtA_cut.
    { eapply (gfa_pop_ok P3 (Z_to_bv 64 0x37a30) (Z_to_bv 64 (usp + -32)) gp tp F fc lo A_INST c CH n SB RI RP FA
                eq_refl eq_refl LOC ltac:(rewrite U1; subst usp1; clear -LO; lia) HC30 ltac:(clear -HR; lia) HSB HRI HCH HCS PSTK3 PRO3 PRI3 PCH3
                _ _ _ _ _ _ _ _ _ _ _ s10 s11 _ _ _ _ (Z_to_bv 64 (CA + 80 * c)) (Z_to_bv 64 n) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 fj m3 m3
                (rg_num_freed r2) (rg_mapped_fa r2) (rg_alloc_user r2) (rg_mapped_user r2) na2 (rg_n_freed r2) ws2 cjunk
                MI3 ltac:(rewrite U1; subst usp1; replace (usp - 32 + -128) with (usp - 160) by (clear; lia); exact SK3)
                (munch_refl _ _) (wmono_refl _ _) FR3' RROW3 PFA3 NFn NFW2 LWS29' PFA3' CARR3 CLEN NA2). }
    cbv beta. intros ms4 (wt0 & wt1 & wt2 & wa1 & wa2' & wa3 & wa4 & wa5 & wa6 & wa7 & wt3 & m4 & ds & -> & MU4 & WM4 & MI4 & SK4 & RROW4 & FARR4 & CARR4 & LDS & DSlo & DShi).
    (* [comment removed for export] *)
    assert (FRr : rw_cells asegs m4 (usp + -32) [CB 8 j8; C8 s1; C8 s0; C8 ra]).
    { assert (FR2 : rw_cells asegs m2 (usp + -32) [CB 8 j8; C8 s1; C8 s0; C8 ra]).
      { eapply rw_cells_transport; [exact FR1| exact MUL| exact WML|]. cbn [disjoint_from cells_size csize Nat.add Nat.mul]. rewrite HRP'.
        unfold kSpaceSize in WE4; clear -HC30 HR WE3 WE4 WE5 WE19 Thi LOC LO; repeat split; try exact I; lia. }
      eapply rw_cells_transport; [| exact MU4| exact WM4|].
      2:{ rewrite ?U1; unfold gfa_W; rewrite ?U1; cbn [disjoint_from cells_size csize Nat.add Nat.mul]; subst usp1 CH; rewrite HRP';
          unfold kSpaceSize in WE4; clear -HC30 HR WE3 WE4 WE5 WE19 Thi LOC LO; repeat split; try exact I; lia. }
      eapply rw_cells_agree; [| exact FR2]. cbn [cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul length]. intros z Hz. rewrite HRP' in *.
      apply AGP; [clear -Hz LOC LO CR USPR; lia| unfold K_POP; clear -Hz; lia| unfold kRegSize; clear -Hz WE2 WE3 WE4 WE5 LOC LO CR HC30; unfold kSpaceSize in *; lia
                | clear -Hz WE2 WE3 WE4 WE5 LOC LO CR; unfold kSpaceSize in *; lia| rewrite KHB, KLE; clear -Hz LOC LO CR; lia| unfold kThrStats; clear -Hz Thi LOC LO; lia| unfold kThrCacheStats; clear -Hz Thi LOC LO; lia]. }
    assert (PCBr : rw_cells asegs m4 (CA + 80 * c) [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 (ic_max_count c)); C8 (Z_to_bv 64 (ic_class_size c))]).
    { pose proof (ROWS1 c ltac:(clear -HC30; lia)) as X. cbv beta in X. rewrite CE in X. cbn [zlen length Z.of_nat] in X.
      assert (X2 : rw_cells asegs m2 (CA + 80 * c) [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 (ic_max_count c)); C8 (Z_to_bv 64 (ic_class_size c))]).
      { eapply rw_cells_transport; [exact X| exact MUL| exact WML|]. cbn [disjoint_from cells_size csize Nat.add Nat.mul]. rewrite HRP'.
        unfold kSpaceSize in WE4; clear -HC30 HR WE3 WE4 WE5 WE19 Thi LOC LO; repeat split; try exact I; lia. }
      eapply rw_cells_transport; [| exact MU4| exact WM4|].
      2:{ rewrite ?U1; unfold gfa_W; rewrite ?U1; cbn [disjoint_from cells_size csize Nat.add Nat.mul]; subst usp1 CH; rewrite HRP';
          unfold kSpaceSize in WE4; clear -HC30 HR WE3 WE4 WE5 WE19 Thi LOC LO; repeat split; try exact I; lia. }
      eapply rw_cells_agree; [| exact X2]. cbn [cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul length]. intros z Hz.
      destruct (Tfacts2 z ltac:(clear -Hz Tlo HC30; lia)) as (B1' & _ & _).
      apply AGP; [exact B1'| unfold K_POP; clear -Hz Thi LOC LO HC30; lia| rewrite HRP'; unfold kRegSize, kSpaceSize in *; clear -Hz WE3 WE4 WE19 HC30; lia
                | unfold kSpaceSize in *; clear -Hz WE3 WE4 WE19 HC30; lia| rewrite KHB, KLE; clear -Hz Tband Tlo HC30; lia| unfold kThrStats; clear -Hz HC30; lia| unfold kThrCacheStats; clear -Hz HC30; lia]. }
    replace (ret_pc (Z_to_bv 64 0x37a30)) with (Z_to_bv 64 227888) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    eapply evtA_cut.
    { eapply (refill_back P3 gp tp F fc lo usp CA c (CA + 80 * c) eq_refl LOC ltac:(clear -LO; lia) HC30 HCA PSTK3' PCA3 1);
      [exact MI4| rewrite U1 in SK4; subst usp1; replace (usp + -32) with (usp - 32) by (clear; lia); exact SK4| exact FRr| exact PCBr| right; reflexivity]. }
    cbv beta. intros ms5 (vt0 & vt1 & vt2 & va1 & va2 & va3 & va4 & va5 & va6 & va7 & vt3 & m5 & -> & MU5 & WM5 & MI5 & SK5 & PCB5).
    apply evtA_done. unfold Q3. do 13 eexists. split; [reflexivity|].
    assert (MU35 : munch [(usp - 160, usp); (RP, RP + 24); (RP + 72, RP + 80); (CH, CH + 4 * n); (CA + 80 * c, CA + 80 * c + 4)] m3 m5).
    { unfold gfa_W in MU4. rewrite ?U1 in MU4. subst usp1.
      eapply munch_trans; [eapply munch_weaken; [| exact MU4]| eapply munch_weaken; [| exact MU5]];
        unfold sub_fp; cbn [outside]; clear -HR; intros x Hx; repeat split; try exact I; lia. }
    assert (WM35 : wmono asegs m3 m5) by (eapply wmono_trans; [exact WM4| exact WM5]).
    split; [exact MU35|]. split; [exact WM35|]. split; [exact MI5|]. split; [exact SK5|].
    split.
    { eapply rw_cells_transport; [exact RROW4| exact MU5| exact WM5|]. unfold rrow. cbn [disjoint_from cells_size csize Nat.add Nat.mul]. rewrite HRP'.
      unfold kSpaceSize in WE4. clear -HC30 WE3 WE4 WE5 WE19 Thi LOC LO. repeat split; try exact I; lia. }
    split.
    { eapply u32arr_transport; [exact FARR4| exact MU5| exact WM5|]. cbn [disjoint_from]. subst FA.
      unfold free_array, region_beg, kRegionSize, kFreeArrayOffset, kFreeArraySize, kSpaceSize in *. clear -LWS2 B5 B7 HC30 WE3 WE4 WE5 WE19 Thi LOC LO. repeat split; try exact I; lia. }
    split.
    { eapply u32arr_transport; [exact CARR4| exact MU5| exact WM5|]. rewrite LDS. cbn [disjoint_from]. subst CH. clear -HC30 Thi LOC LO. repeat split; try exact I; lia. }
    split; [exact LDS|]. split; [exact DSlo|]. change (1 =? 1) with true in PCB5. cbv iota in PCB5. exact PCB5. }
  (* [comment removed for export] *)
  intros ms5 mo5 HQ5 AG5 KIP5.
  destruct HQ5 as (wt0 & wt1 & wt2 & wa1 & wa2' & wa3 & wa4 & wa5 & wa6 & wa7 & wt3 & ds & m5 & -> & MU35 & WM35 & MI5 & SK5 & RROW5 & FARR5 & CARR5 & LDS & DSlo & PCB5).
  pose proof (magree_frame _ _ AG5) as (Ffds5 & Fvm5 & Flz5 & Ffs5 & Fh5 & Ftid5 & _).
  destruct KIP5 as [KIA5 _].
  pose proof (AKern_frame _ _ _ _ Fvm5 Flz5 AK3) as AK5.
  set (a' := refill_fin c n a2).
  assert (NFn' : (Z.to_nat n <= length (rg_free (get_region a2 c)))%nat) by (fold r2; unfold rg_num_freed in NFn; clear -NFn HR; lia).
  destruct GROWS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GAU & GFR & _). rewrite GR1 in GFR. fold (region_of a c) in GFR. fold r in GFR. fold r2 in GFR.
  set (keep2 := gfa_keep c n a2). set (keep := Nat.min (length (rg_free r)) keep2).
  assert (K2L : (keep2 <= length (rg_free r2))%nat) by (subst keep2; unfold gfa_keep; fold r2; clear; lia).
  assert (ARUN : arun fuelP (refill E0 c a) orcP = Some (a', ONorm true, evsP, orcP')).
  { subst a' n. apply (arun_refill_pop E0 c a fuelP orcP a2 evsP orcP'); [unfold rg_num_freed in *; subst r; exact LTn| exact RUNP| fold r2; exact NFn]. }
  assert (ROOM1 : room a c) by exact (proj1 ROOM).
  pose proof (hoare_arun _ _ _ a fuelP orcP a' true evsP orcP' (refill_spec E0 Pq Dq a c HCc Hwf CE ROOM1) eq_refl ARUN) as (WF' & CI' & PF' & CV' & GC' & NE').
  (* [comment removed for export] *)
  assert (AG15 : forall z, 0 <= z < 2^64 -> ~ (usp - 1696 <= z < usp) -> (forall i, 1 <= i <= 31 -> ~ (CA + 80 * i + 4 <= z < CA + 80 * i + 16)) ->
                 ~ (CH <= z < CH + 4 * n) -> ~ (CA + 80 * c <= z < CA + 80 * c + 4) -> ~ (RP <= z < RP + kRegSize) ->
                 ~ (region_beg SB c + rg_mapped_user r <= z < region_beg SB c + rg_mapped_user r2) ->
                 ~ (FA + 4 * zlen (rg_free r) <= z < FA + rg_mapped_fa r2) ->
                 ~ (kShadowBase + (region_beg SB c + rg_mapped_user r) / 8 <= z < kShadowBase + (region_beg SB c + rg_mapped_user r2) / 8) ->
                 ~ (kShadowBase + (FA + rg_mapped_fa r) / 8 <= z < kShadowBase + (FA + rg_mapped_fa r2) / 8) ->
                 ~ (T + kThrStats + 72 <= z < T + kThrStats + 88) -> ~ (T + kThrCacheStats + 24 <= z < T + kThrCacheStats + 32) ->
                 m5 (wa z) = m (wa z)).
  { intros z Hz N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11.
    rewrite <- (AGB2 z Hz ltac:(clear -N1; lia) N2 ltac:(clear -N5; unfold kRegSize in *; lia)).
    rewrite <- (MU23 (wa z)).
    2:{ rewrite wa_unsigned by exact Hz. unfold pop_W. cbv zeta. cbn [outside]. rewrite ?GR1. fold r2. fold (region_of a c). fold r. fold RP. fold FA.
        split; [unfold K_POP; clear -N1; lia|]. split; [exact N5|]. split; [exact N6|]. split; [exact N7|]. split; [exact N8|]. split; [exact N9|]. split; [exact N10|]. split; [exact N11| exact I]. }
    apply MU35. rewrite wa_unsigned by exact Hz. cbn [outside]. split; [clear -N1; lia|]. split; [clear -N5; unfold kRegSize in *; lia|]. split; [clear -N5; unfold kRegSize in *; lia|].
    split; [exact N3|]. split; [exact N4| exact I]. }
  apply (CONT wt0 wt1 wt2 wa1 wa2' wa3 wa4 wa5 wa6 wa7 wt3 zt4 zt5 zt6 m5 mo5 a').
  unfold refill_post. cbv zeta.
  split; [exact SK5|].
  split; [exact (wmono_trans _ _ _ _ WM1 (wmono_trans _ _ _ _ WML (wmono_trans _ _ _ _ WM23 WM35)))|].
  split.
  { (* [comment removed for export] *)
    exists ((((usp - 32, usp) :: ic_W CA) ++ [(usp - 160, usp - 32); (RP, RP + 8)]) ++ (pop_W E0 a1 a2 c (usp - 160) ++ [(usp - 160, usp); (RP, RP + 24); (RP + 72, RP + 80); (CH, CH + 4 * n); (CA + 80 * c, CA + 80 * c + 4)])).
    split; [eapply munch_app; [eapply munch_app; [exact MU1| exact MUL]| eapply munch_app; [exact MU23| exact MU35]]|].
    assert (ICW : Forall (fun iv => CA + 84 <= fst iv /\ snd iv <= CA + 2496) (ic_W CA)) by (unfold ic_W; repeat (constructor; [cbn [fst snd]; clear; lia|]); constructor).
    Ltac thrW3 := right; right; left; eexists; split; [unfold arep_thr_ranges; do 3 right; left; reflexivity| cbn [fst snd]; unfold kThrCache, kPerClassSize, kNumClasses, kThrCacheStats, kThrStats].
    Ltac thrW4 := right; right; left; eexists; split; [unfold arep_thr_ranges; do 4 right; left; reflexivity| cbn [fst snd]; unfold kThrCache, kPerClassSize, kNumClasses, kThrCacheStats, kThrStats].
    Ltac thrW5 := right; right; left; eexists; split; [unfold arep_thr_ranges; do 5 right; left; reflexivity| cbn [fst snd]; unfold kThrCache, kPerClassSize, kNumClasses, kThrCacheStats, kThrStats].
    Ltac rsvW' HRP' WE3 WE4 HC30 := do 3 right; left; cbn [fst snd]; rewrite ?HRP'; unfold kResvLen, kSpaceSize in *; clear -WE3 WE4 HC30; lia.
    pose proof (RG_any E0 Pq Dq a2 WF2 c ltac:(clear -HC30; lia)) as [[G1 G2] [G3 G4]]. unfold region_of in G1, G2, G3, G4. fold r2 in G1, G2, G3, G4.
    assert (SHX : forall x, SB <= x < SB + kSpaceSize -> sh_excluded E0 x = false).
    { intros x Hx. pose proof WE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E11 & E12 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E27 & _).
      unfold sh_excluded, in_fakestack, in_iarena, in_reginfo. unfold kIArenaLen, kSpaceSize, kPageSize in *.
      replace (x <? ae_fs_beg E0 + ae_fs_len E0) with (negb (ae_fs_beg E0 <=? x)).
      2:{ destruct (Z.leb_spec (ae_fs_beg E0) x); cbn; symmetry; [apply Z.ltb_ge| apply Z.ltb_lt]; clear -Hx H WE3 WE4 E11 E12; lia. }
      replace (x <? ae_iarena E0 + 65536) with (negb (ae_iarena E0 <=? x)).
      2:{ destruct (Z.leb_spec (ae_iarena E0) x); cbn; symmetry; [apply Z.ltb_ge| apply Z.ltb_lt]; clear -Hx H WE3 WE4 E27; lia. }
      replace (SB + 137438953472 <=? x) with false by (symmetry; apply Z.leb_gt; clear -Hx; lia).
      rewrite !Bool.andb_negb_r. reflexivity. }
    unfold pop_W. cbv zeta. rewrite ?GR1. fold r2. fold (region_of a c). fold r. fold RP. fold FA.
    split.
    { apply Forall_app. split; [apply Forall_app; split|apply Forall_app; split].
      - constructor; [left; cbn [fst snd]; clear -LO; lia|]. eapply Forall_impl; [| exact ICW]. intros iv [H1 H2]. thrW3; clear -H1 H2; lia.
      - constructor; [left; cbn [fst snd]; clear -LO; lia|]. constructor; [rsvW' HRP' WE3 WE4 HC30| constructor].
      - constructor; [left; cbn [fst snd]; unfold K_POP; clear -LO; lia|].
        constructor; [do 3 right; left; cbn [fst snd]; rewrite ?HRP', ?HRI; unfold kRegSize, kResvLen, kSpaceSize in *; clear -WE3 WE4 HC30; lia|].
        constructor; [do 3 right; left; cbn [fst snd]; unfold region_beg, kRegionSize, kFreeArrayOffset, kResvLen, kSpaceSize in *; clear -WE3 WE4 HC30 A1 A3 G1 G2; lia|].
        constructor; [do 3 right; left; cbn [fst snd]; subst FA; unfold free_array, region_beg, kRegionSize, kFreeArrayOffset, kFreeArraySize, kResvLen, kSpaceSize, zlen in *; clear -WE3 WE4 HC30 A5 A7 G3 G4; lia|].
        constructor.
        { do 8 right. cbn [fst snd]. split.
          - right. unfold A_base.A_SB, kShadowBase, region_beg, kRegionSize, kFreeArrayOffset, kSpaceSize in *. rewrite KHB in WE2 |- *. clear -WE2 WE3 WE4 WE5 CR HC30 A1 A3 G1 G2. Z.div_mod_to_equations. lia.
          - intros z Hz. apply SHX. unfold A_base.A_SB, kShadowBase, region_beg, kRegionSize, kFreeArrayOffset, kSpaceSize in *. clear -Hz HC30 A1 A3 G1 G2. Z.div_mod_to_equations. lia. }
        constructor.
        { do 8 right. cbn [fst snd]. split.
          - right. subst FA. unfold A_base.A_SB, kShadowBase, free_array, region_beg, kRegionSize, kFreeArrayOffset, kFreeArraySize, kSpaceSize in *. rewrite KHB in WE2 |- *. clear -WE2 WE3 WE4 WE5 CR HC30 A5 A7 G3 G4. Z.div_mod_to_equations. lia.
          - intros z Hz. apply SHX. subst FA. unfold A_base.A_SB, kShadowBase, free_array, region_beg, kRegionSize, kFreeArrayOffset, kFreeArraySize, kSpaceSize in *. clear -Hz HC30 A5 A7 G3 G4. Z.div_mod_to_equations. lia. }
        constructor; [thrW5; clear; lia|]. constructor; [thrW4; clear; lia| constructor].
      - constructor; [left; cbn [fst snd]; clear -LO; lia|]. constructor; [rsvW' HRP' WE3 WE4 HC30|]. constructor; [rsvW' HRP' WE3 WE4 HC30|].
        constructor; [thrW3; subst CH; clear -HC30 HR; lia|]. constructor; [thrW3; clear -HC30; lia| constructor]. }
    assert (LV : forall blo bsz, In (blo, bsz) (live_blocks a) ->
              blo + bsz <= lo /\ (blo + bsz <= T \/ T + 4096 <= blo) /\ (blo + bsz <= RP \/ RP + 128 <= blo)
              /\ (blo + bsz <= region_beg SB c + rg_mapped_user r \/ region_beg SB c + rg_mapped_user r2 <= blo)
              /\ (blo + bsz <= FA + 4 * zlen (rg_free r) \/ FA + rg_mapped_fa r2 <= blo)
              /\ (blo + bsz <= kLowAppEnd \/ kHighMemBeg <= blo)).
    { intros blo bsz Hin. pose proof (live_block_off_threadG E0 Pq Dq a blo bsz Hwf Hin) as [L1 L2]. pose proof (live_block_whereG E0 Pq Dq a blo bsz Hwf Hin) as (L3 & _ & BND & L4).
      destruct (live_block_loc E0 Pq Dq a blo bsz Hwf Hin) as (k & cm & Hk & _ & _ & _ & M1 & M2 & LOCm).
      split; [clear -L1 LOC; lia|]. split; [exact L2|]. split.
      { rewrite HRP'. destruct L4 as [[L5 L6]|(sc & Hsc & L5 & L6)].
        - left. unfold kSpaceSize in L6. clear -L6 HC30. lia.
        - destruct (WS3 sc Hsc) as (_ & _ & _ & _ & _ & _ & RSV). pose proof (RSV _ WE7) as X. cbn [fst snd] in X. unfold kSpaceSize in *. clear -X L3 L5 L6 WE3 WE4 HC30. lia. }
      split; [| split; [| exact BND]].
      - destruct (cm_prim cm) as [c'|].
        + destruct LOCm as (Hc' & R1 & R2). pose proof (RG_any E0 Pq Dq a Hwf c' ltac:(unfold kLargestClassID in Hc'; clear -Hc'; lia)) as [[F1 F2] _]. unfold region_of in F1, F2.
          unfold region_beg, kRegionSize, kFreeArrayOffset, kLargestClassID in *.
          destruct (Z.eq_dec c' c) as [->|NE]; [left; fold (region_of a c) in R2; fold r in R2; clear -M1 M2 R2; lia| clear -M1 M2 R1 R2 F1 F2 G1 G2 A1 A3 Hc' HC30 NE; lia].
        + destruct LOCm as (sc & Hsc & R1 & R2). destruct (WS3 sc Hsc) as (_ & _ & _ & _ & _ & _ & RSV). pose proof (RSV _ WE7) as X. cbn [fst snd] in X.
          unfold region_beg, kRegionSize, kFreeArrayOffset, kPageSize, kSpaceSize in *. clear -X M1 M2 R1 R2 L3 WE3 WE4 HC30 G1 G2 A1 A3. lia.
      - subst FA. destruct (cm_prim cm) as [c'|].
        + destruct LOCm as (Hc' & R1 & R2). pose proof (RG_any E0 Pq Dq a Hwf c' ltac:(unfold kLargestClassID in Hc'; clear -Hc'; lia)) as [[F1 F2] _]. unfold region_of in F1, F2.
          unfold free_array, region_beg, kRegionSize, kFreeArrayOffset, kFreeArraySize, kLargestClassID, zlen in *.
          destruct (Z_le_gt_dec c' c) as [LE|GT]; [left; clear -M1 M2 R1 R2 F1 F2 Hc' HC30 LE; nia| right; clear -M1 M2 R1 R2 G3 G4 Hc' HC30 GT; nia].
        + destruct LOCm as (sc & Hsc & R1 & R2). destruct (WS3 sc Hsc) as (_ & _ & _ & _ & _ & _ & RSV). pose proof (RSV _ WE7) as X. cbn [fst snd] in X.
          unfold free_array, region_beg, kRegionSize, kFreeArrayOffset, kFreeArraySize, kPageSize, kSpaceSize, zlen in *. clear -X M1 M2 R1 R2 L3 WE3 WE4 HC30 G3 G4 A5 A7. lia. }
    apply Forall_forall. intros iv Hiv blo bsz Hin. destruct (LV blo bsz Hin) as (L1 & L2 & L3 & L4 & L5 & L6). rewrite KLE, KHB in L6.
    rewrite !in_app_iff in Hiv. destruct Hiv as [[Hiv|Hiv]|[Hiv|Hiv]].
    - destruct Hiv as [<-|Hiv]; [cbn [fst snd]; clear -L1 LO; lia|].
      pose proof (proj1 (Forall_forall _ _) ICW iv Hiv) as [H1 H2]. clear -L2 H1 H2. destruct iv; cbn [fst snd] in *. lia.
    - cbn in Hiv. destruct Hiv as [<-|[<-|[]]]; cbn [fst snd]; [clear -L1 LO; lia| clear -L3; lia].
    - cbn in Hiv. destruct Hiv as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; cbn [fst snd].
      + unfold K_POP. clear -L1 LO; lia.
      + unfold kRegSize in *. clear -L3; lia.
      + clear -L4; lia.
      + clear -L5; lia.
      + unfold kShadowBase, region_beg, kRegionSize, kFreeArrayOffset, kSpaceSize in *. rewrite KHB in WE2. clear -L6 WE2 WE3 WE4 WE5 CR HC30 A1 A3 G1 G2. Z.div_mod_to_equations. lia.
      + subst FA. unfold kShadowBase, free_array, region_beg, kRegionSize, kFreeArrayOffset, kFreeArraySize, kSpaceSize in *. rewrite KHB in WE2. clear -L6 WE2 WE3 WE4 WE5 CR HC30 A5 A7 G3 G4. Z.div_mod_to_equations. lia.
      + unfold kThrStats. clear -L2; lia.
      + unfold kThrCacheStats. clear -L2; lia.
    - cbn in Hiv. subst CH. destruct Hiv as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd]; [clear -L1 LO; lia| clear -L3; lia| clear -L3; lia| clear -L2 HC30 HR; lia| clear -L2 HC30; lia]. }
  split; [exists fuelP, orcP, evsP, orcP'; exact ARUN|].
  Ltac toT5 AGT H := eapply rw_cells_agree; [| exact H]; cbn [cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul length];
                      intros z Hz; apply AGT.
  split.
  { (* [comment removed for export] *)
    unfold RINV.
    assert (Tfacts : forall z, T <= z < T + 4096 -> 0 <= z < 2^64 /\ ~ (usp - 1696 <= z < usp) /\ ~ (RP <= z < RP + kRegSize)
              /\ ~ (region_beg SB c + rg_mapped_user r <= z < region_beg SB c + rg_mapped_user r2) /\ ~ (FA + 4 * zlen (rg_free r) <= z < FA + rg_mapped_fa r2)
              /\ ~ (kShadowBase + (region_beg SB c + rg_mapped_user r) / 8 <= z < kShadowBase + (region_beg SB c + rg_mapped_user r2) / 8)
              /\ ~ (kShadowBase + (FA + rg_mapped_fa r) / 8 <= z < kShadowBase + (FA + rg_mapped_fa r2) / 8)).
    { intros z Hz.
      pose proof (RG_any E0 Pq Dq a2 WF2 c ltac:(clear -HC30; lia)) as [[G1 G2] [G3 G4]]. unfold region_of in G1, G2, G3, G4. fold r2 in G1, G2, G3, G4.
      rewrite HRP'. subst FA. unfold free_array, region_beg, kRegionSize, kFreeArrayOffset, kFreeArraySize, kShadowBase, kRegSize, kSpaceSize in *. rewrite KHB in WE2.
      clear -Hz Tlo Thi Tband WE2 WE3 WE4 WE5 WE19 LOC LO CR HC30 G1 G2 G3 G4 A1 A3 A5 A7. unfold zlen. repeat split; try lia; Z.div_mod_to_equations; lia. }
    assert (AGT5 : forall z, T <= z < T + 4096 -> (forall i, 1 <= i <= 31 -> ~ (CA + 80 * i + 4 <= z < CA + 80 * i + 16)) ->
                   ~ (CH <= z < CH + 4 * n) -> ~ (CA + 80 * c <= z < CA + 80 * c + 4) ->
                   ~ (T + kThrStats + 72 <= z < T + kThrStats + 88) -> ~ (T + kThrCacheStats + 24 <= z < T + kThrCacheStats + 32) -> m5 (wa z) = m (wa z)).
    { intros z Hz N2 N3 N4 N10 N11. pose proof (Tfacts z Hz) as (B1' & B2' & B5' & B6' & B7' & B8' & B9'). exact (AG15 z B1' B2' N2 N3 N4 B5' B6' B7' B8' B9' N10 N11). }
    Ltac EQS a' := subst a'; first
        [ rewrite fin_chunks | rewrite fin_tq | rewrite fin_gq | rewrite fin_sec | rewrite fin_sec_stats | rewrite fin_ptr | rewrite fin_keys | rewrite fin_frames
        | rewrite fin_node_blocks | rewrite fin_store_blocks | rewrite fin_store_stored | rewrite fin_ndepot | rewrite fin_ia | rewrite fin_cache_allocated
        | rewrite fin_glob_allocated | rewrite fin_glob_mapped | rewrite fin_sec_stale | rewrite fin_oom | rewrite fin_dead ].
    split.
    { (* [comment removed for export] *)
      unshelve eapply (ARep_refill asegs E0 Pq Dq a a' m m5 lo c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ keep);
        try (EQS a'; first [rewrite Pch| rewrite Ptq| rewrite Pgq| rewrite Psec| rewrite Pss| rewrite Pptr| rewrite Pky| rewrite Pfr| rewrite Pnb| rewrite Psb| rewrite Pstd
                          | rewrite Pnd| rewrite Pia| rewrite Pcal| rewrite Pga| rewrite Pgm| rewrite Psst| rewrite Poom| rewrite Pdd]; reflexivity).
      - intros c' NE. subst a'. unfold region_of. rewrite fin_get_region. destruct (decide (c' = c)) as [E|_]; [exfalso; exact (NE E)|]. rewrite (Preg c' NE). apply GR1.
      - intros c' NE. subst a'. rewrite fin_get_cache. destruct (decide (c' = c)) as [E|_]; [exfalso; exact (NE E)|]. unfold get_cache. rewrite Pca. apply (get_cache_upd_cache_inited true a c').
      - subst a'. unfold region_of at 2. rewrite fin_get_region. destruct (decide (c = c)) as [_|NE]; [| exfalso; exact (NE eq_refl)]. cbn [gfa_reg rg_mapped_user]. fold r2. exact GRU.
      - subst a'. unfold region_of at 2. rewrite fin_get_region. destruct (decide (c = c)) as [_|NE]; [| exfalso; exact (NE eq_refl)]. cbn [gfa_reg rg_mapped_fa]. fold r2. exact GRF.
      - (* [comment removed for export] *)
        subst a'. unfold region_of. rewrite !fin_get_region. destruct (decide (c = c)) as [_|NE]; [| exfalso; exact (NE eq_refl)].
        unfold gfa_reg. cbn [rg_free]. fold r2. fold keep2. fold (region_of a c). fold r. rewrite length_firstn. rewrite GFR.
        rewrite firstn_firstn. replace (Nat.min keep keep2) with keep by (subst keep; clear; lia).
        rewrite firstn_app. replace (keep - length (rg_free r))%nat with 0%nat by (subst keep; clear; lia). cbn [firstn]. rewrite app_nil_r.
        split; [reflexivity|]. split; [subst keep; clear; lia|]. rewrite <- GFR. subst keep. clear -K2L. lia.
      - exact HCc.
      - exact Hwf.
      - exact WF'.
      - exact (wmono_trans _ _ _ _ WM1 (wmono_trans _ _ _ _ WML (wmono_trans _ _ _ _ WM23 WM35))).
      - (* [comment removed for export] *)
        intros z Hz NF. unfold FPWref in NF. subst a'. unfold region_of in NF. rewrite !fin_get_region in NF.
        destruct (decide (c = c)) as [_|NE]; [| exfalso; exact (NE eq_refl)]. cbn [gfa_reg rg_mapped_user rg_mapped_fa rg_free] in NF. fold r2 in NF. fold (region_of a c) in NF. fold r in NF.
        apply AG15; [exact Hz| intros X| intros i Hi X| intros X| intros X| intros X| intros X| intros X| intros X| intros X| intros X| intros X]; apply NF.
        + left. clear -X LO. lia.
        + do 2 right; left. exists i. split; [clear -Hi; unfold kNumClasses; lia| unfold kThrCache, kPerClassSize; clear -X; lia].
        + do 3 right; left. subst CH. unfold kThrCache, kPerClassSize. clear -X HR. lia.
        + do 3 right; left. unfold kThrCache, kPerClassSize. clear -X. lia.
        + right; left. subst RP. clear -X. lia.
        + do 6 right; left. exact X.
        + do 7 right; left. subst FA. unfold zlen in X. clear -X. subst keep. lia.
        + do 8 right; left. exact X.
        + do 9 right. subst FA. exact X.
        + do 5 right; left. exact X.
        + do 4 right; left. exact X.
      - exact LOC.
      - exact Hrep.
      - exact (blocks_sep_ofG E0 Pq Dq a mo ENV0 Hwf Hkern).
      - clear -Tlo Thi Timg. repeat split; lia.
      - intros x Hx. pose proof (IMGR x Hx) as X. rewrite EI1. clear -X EI2. lia.
      - rewrite EI1. clear; lia.
      - exact IMGR.
      - exists mo. exact Hkern.
      - exact TDN.
      - (* [comment removed for export] *)
        subst a'. unfold region_of. rewrite fin_get_region. destruct (decide (c = c)) as [_|NE]; [| exfalso; exact (NE eq_refl)].
        unfold gfa_reg, region_cells. cbn [rg_mapped_fa rg_alloc_user rg_mapped_user rg_n_allocated rg_n_freed rg_free]. unfold rg_num_freed at 1. cbn [rg_free].
        fold r2. fold keep2. rewrite length_firstn.
        replace (Z.of_nat (keep2 `min` length (rg_free r2))) with (rg_num_freed r2 - n) by (subst keep2; unfold gfa_keep; fold r2; unfold rg_num_freed in *; clear -NFn HR; lia).
        fold RP. unfold rrow in RROW5. subst na2. rewrite (zw_mod_add (rg_n_allocated r2) n) in RROW5. unfold rrow, AsanRep.zw, AsanRep.zb, zeros. cbn [repeat]. exact RROW5.
      - (* [comment removed for export] *)
        intros i Hi NE. subst a'. unfold percls_cells. rewrite fin_get_cache, fin_cache_inited. destruct (decide (i = c)) as [E|_]; [exfalso; exact (NE E)|].
        unfold get_cache. rewrite Pca, Pci. fold (get_cache a1 i). rewrite get_cache_upd_cache_inited. cbn [as_cache_inited upd_cache_inited]. unfold kNumClasses in Hi.
        destruct (Z.eq_dec i 0) as [->|NZ].
        + destruct (Tcache 0 ltac:(unfold kNumClasses; clear; lia)) as [X0 _]. unfold percls_cells in X0.
          replace (row_max_count 0) with 0 in X0 |- * by reflexivity. replace (row_class_size 0) with 0 in X0 |- * by reflexivity.
          replace (if as_cache_inited a then 0 else 0) with 0 in X0 by (destruct (as_cache_inited a); reflexivity).
          unfold kThrCache, kPerClassSize in X0 |- *. toT5 AGT5 X0; [clear -Hz; lia| intros j Hj Cj; clear -Hz Hj Cj; lia| subst CH; clear -Hz HC30 HR; lia| clear -Hz HC30; lia
            | unfold kThrStats; clear -Hz; lia| unfold kThrCacheStats; clear -Hz; lia].
        + pose proof (ROWS1 i ltac:(clear -Hi NZ; lia)) as X. cbv beta in X.
          unfold row_max_count, row_class_size. unfold ic_max_count, ic_class_size in X. unfold kThrCache, kPerClassSize. replace (T + 208 + 80 * i) with (CA + 80 * i) by (clear; lia).
          assert (X2 : rw_cells asegs m2 (CA + 80 * i) [C4 (Z_to_bv 64 (zlen (get_cache a i))); C4 (Z_to_bv 64 (if i =? 31 then 16 else max_count i)); C8 (Z_to_bv 64 (if i =? 31 then 64 else class_size i))]).
          { eapply rw_cells_transport; [exact X| exact MUL| exact WML|]. cbn [disjoint_from cells_size csize Nat.add Nat.mul]. rewrite HRP'.
            unfold kSpaceSize in WE4. clear -Hi NZ HC30 WE3 WE4 WE5 WE19 Thi LOC LO. repeat split; try exact I; lia. }
          assert (X3 : rw_cells asegs m3 (CA + 80 * i) [C4 (Z_to_bv 64 (zlen (get_cache a i))); C4 (Z_to_bv 64 (if i =? 31 then 16 else max_count i)); C8 (Z_to_bv 64 (if i =? 31 then 64 else class_size i))]).
          { eapply rw_cells_agree; [| exact X2]. cbn [cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul length]. intros z Hz.
            destruct (Tfacts2 z ltac:(clear -Hz Tlo Hi; lia)) as (B1' & _ & _).
            apply AGP; [exact B1'| unfold K_POP; clear -Hz Thi LOC LO Hi; lia| rewrite HRP'; unfold kRegSize, kSpaceSize in *; clear -Hz WE3 WE4 WE19 Hi HC30; lia
                      | unfold kSpaceSize in *; clear -Hz WE3 WE4 WE19 Hi HC30; lia| rewrite KHB, KLE; clear -Hz Tband Tlo Hi; lia| unfold kThrStats; clear -Hz Hi; lia| unfold kThrCacheStats; clear -Hz Hi; lia]. }
          eapply rw_cells_transport; [exact X3| exact MU35| exact WM35|]. cbn [disjoint_from cells_size csize Nat.add Nat.mul]. subst CH. rewrite HRP'.
          unfold kSpaceSize in WE4. clear -Hi NZ NE HC30 HR Tlo Thi WE3 WE4 WE5 WE19 LOC LO. repeat split; try exact I; lia.
      - (* [comment removed for export] *)
        subst a'. unfold percls_cells. rewrite fin_get_cache, fin_cache_inited. destruct (decide (c = c)) as [_|NE]; [| exfalso; exact (NE eq_refl)].
        rewrite Pci. cbn [as_cache_inited upd_cache_inited]. unfold row_max_count, row_class_size. unfold ic_max_count, ic_class_size in PCB5.
        replace (zlen (gfa_hi c n a2)) with n by (unfold gfa_hi, gfa_keep, zlen; rewrite length_skipn; fold r2; unfold rg_num_freed in NFn; clear -NFn HR; lia).
        unfold kThrCache, kPerClassSize. replace (T + 208 + 80 * c) with (CA + 80 * c) by (clear; lia). split; [exact PCB5|].
        exists (skipn (Z.to_nat n) ds). split.
        + replace (CA + 80 * c + 16) with CH by (subst CH; clear; lia).
          replace (map AsanRep.zw (gfa_hi c n a2) ++ skipn (Z.to_nat n) ds) with ds; [exact CARR5|].
          rewrite <- (firstn_skipn (Z.to_nat n) ds) at 1. f_equal. unfold gfa_hi, gfa_keep. fold r2.
          apply nth_error_ext'. intros j. destruct (Nat.lt_ge_cases j (Z.to_nat n)) as [LT|GE].
          * rewrite nth_error_firstn. replace (j <? Z.to_nat n)%nat with true by (symmetry; apply Nat.ltb_lt; exact LT). cbv iota.
            rewrite (DSlo j LT). subst ws2. rewrite nth_error_map, nth_error_skipn.
            rewrite nth_error_app1 by (rewrite length_map; unfold rg_num_freed in *; clear -NFn HR LT; lia). rewrite nth_error_map.
            replace (Z.to_nat (rg_num_freed r2 - n) + j)%nat with (length (rg_free r2) - Z.to_nat n + j)%nat by (unfold rg_num_freed in *; clear -NFn HR; lia). reflexivity.
          * rewrite (proj2 (nth_error_None _ _)) by (rewrite length_firstn, LDS; clear -GE HR; lia).
            symmetry. apply (proj2 (nth_error_None _ _)). rewrite length_map, length_skipn. unfold rg_num_freed in NFn. clear -GE NFn HR. lia.
        + unfold gfa_hi, gfa_keep. rewrite length_skipn, length_skipn, LDS. fold r2. unfold rg_num_freed in NFn. clear -NFn HR. lia.
      - (* [comment removed for export] *)
        subst a'. rewrite fin_cache_mapped. eapply rw_cells_transport; [exact PCM3| exact MU35| exact WM35|]. cbn [disjoint_from cells_size csize Nat.add Nat.mul]. subst CH. rewrite HRP'.
        unfold kThrCacheStats, kSpaceSize in *. clear -HC30 HR Tlo Thi WE3 WE4 WE5 WE19 LOC LO. repeat split; try exact I; lia.
      - subst a'. rewrite fin_ts. eapply rw_cells_transport; [exact PTS3| exact MU35| exact WM35|]. cbn [disjoint_from cells_size csize Nat.add Nat.mul]. subst CH. rewrite HRP'.
        unfold kThrStats, kSpaceSize in *. clear -HC30 HR Tlo Thi WE3 WE4 WE5 WE19 LOC LO. repeat split; try exact I; lia.
      - subst a'. rewrite fin_ts. exact Pts.
      - subst a'. unfold region_of. rewrite fin_get_region. destruct (decide (c = c)) as [_|NE]; [| exfalso; exact (NE eq_refl)]. cbn [gfa_reg rg_mapped_user]. fold r2.
        eapply wr_at_transport; [exact PUM3| exact WM35].
      - subst a'. unfold region_of. rewrite fin_get_region. destruct (decide (c = c)) as [_|NE]; [| exfalso; exact (NE eq_refl)].
        unfold gfa_reg. cbn [rg_free rg_mapped_fa]. fold r2. fold keep2.
        exists (map AsanRep.zw (skipn keep2 (rg_free r2)) ++ fjunk'). split.
        + rewrite app_assoc, <- map_app, firstn_skipn. fold FA. exact FARR5.
        + rewrite length_app, length_map, length_skipn, length_firstn, <- LWS2. subst ws2. rewrite length_app, length_map. clear -K2L. lia.
      - subst a'. unfold region_of. rewrite fin_get_region. destruct (decide (c = c)) as [_|NE]; [| exfalso; exact (NE eq_refl)]. cbn [gfa_reg rg_mapped_user]. fold r2.
        rewrite GR1 in SHU3. fold (region_of a c) in SHU3. fold r in SHU3. fold r2 in SHU3.
        eapply rw_cells_transport; [exact SHU3| exact MU35| exact WM35|].
        cbn [disjoint_from cells_size csize Nat.add Nat.mul]. fold (region_of a c). fold r. rewrite Nat.add_0_r, Z2Nat.id by (clear -GRU; Z.div_mod_to_equations; lia).
        subst CH. rewrite HRP'. unfold kShadowBase, region_beg, kRegionSize, kFreeArrayOffset, kSpaceSize in *. rewrite KHB in WE2.
        clear -GRU A1 A3 B1 B3 HC30 HR Tband Tlo Thi WE2 WE3 WE4 WE5 LOC LO CR. repeat split; try exact I; Z.div_mod_to_equations; lia.
      - subst a'. unfold region_of. rewrite fin_get_region. destruct (decide (c = c)) as [_|NE]; [| exfalso; exact (NE eq_refl)]. cbn [gfa_reg rg_mapped_fa]. fold r2.
        rewrite GR1 in SHF3. fold (region_of a c) in SHF3. fold r in SHF3. fold r2 in SHF3.
        eapply rw_cells_transport; [exact SHF3| exact MU35| exact WM35|].
        cbn [disjoint_from cells_size csize Nat.add Nat.mul]. fold (region_of a c). fold r. rewrite Nat.add_0_r, Z2Nat.id by (clear -GRF; Z.div_mod_to_equations; lia).
        subst CH FA. rewrite HRP'. unfold kShadowBase, free_array, region_beg, kRegionSize, kFreeArrayOffset, kFreeArraySize, kSpaceSize in *. rewrite KHB in WE2.
        clear -GRF A5 A7 B5 B7 HC30 HR Tband Tlo Thi WE2 WE3 WE4 WE5 LOC LO CR. repeat split; try exact I; Z.div_mod_to_equations; lia. }
    split; [exact WF'|].
    split; [subst a'; apply fin_AKern; exact AK5|].
    split; [subst a'; unfold res_ok in *; rewrite fin_residue, fin_sec, Prs, Psec; cbn [as_residue as_sec upd_cache_inited]; exact Hres|].
    split; [subst a'; unfold AQbound, tq_bytes, gq_bytes in *; rewrite fin_tq, fin_gq, Ptq, Pgq; cbn [as_tq as_gq upd_cache_inited]; exact Hqb|].
    split; [subst a'; unfold depot_inv, depot_n_ids, dphi in *; rewrite ?fin_keys, ?fin_frames, ?fin_ndepot, ?fin_node_blocks, ?fin_store_blocks, ?fin_store_stored, ?Pky, ?Pfr, ?Pnd, ?Pnb, ?Psb, ?Pstd;
           cbn [as_keys as_frames as_ndepot_ins as_node_blocks as_store_blocks as_store_stored upd_cache_inited]; exact Hdi|].
    split; [exact MI5|].
    split.
    { eapply rt_misc5_agree; [exact Hrt|]. intros z Hz.
      pose proof (resv_range_num E0 c0 cl CR0 ltac:(clear -CC1 CC2; lia)) as (CQ1 & CQ2 & CQ3 & CQ4).
      pose proof (resv_range_num E0 d0 dl DR0 ltac:(clear -DD1 DD2; lia)) as (DQ1 & DQ2 & DQ3 & DQ4).
      pose proof CR0 as (_ & _ & _ & CQ5 & _). pose proof DR0 as (_ & _ & _ & DQ5 & _).
      pose proof (RG_any E0 Pq Dq a2 WF2 c ltac:(clear -HC30; lia)) as [[G1 G2] [G3 G4]]. unfold region_of in G1, G2, G3, G4. fold r2 in G1, G2, G3, G4.
      subst FA. unfold free_array, region_beg, kRegionSize, kFreeArrayOffset, kFreeArraySize, kShadowBase, kRegSize, kResvLen, kSpaceSize, kThrStats, kThrCacheStats in *. rewrite KHB in WE2.
      destruct (rt_fpc_where E0 FSB0 PL0 z Hz) as [(Z1 & _ & _ & _)|RH].
      - apply AG15; [clear -Z1; lia| clear -Z1 LOC LO CR; lia| apply OFFT; clear -Z1 Timg; lia| subst CH; clear -Z1 Timg HC30 HR; lia| clear -Z1 Timg HC30; lia
               | rewrite HRP'; clear -Z1 WE2 WE3 HC30; lia| clear -Z1 WE2 WE3 HC30 A1; lia| clear -Z1 WE2 WE3 HC30 A5; unfold zlen; lia
               | rewrite KLE in *; clear -Z1 WE2 WE3 HC30 A1 KLE; Z.div_mod_to_equations; lia| clear -Z1 WE2 WE3 HC30 A5; Z.div_mod_to_equations; lia| clear -Z1 Timg; lia| clear -Z1 Timg; lia].
      - unfold rt_high2 in RH. apply AG15.
        + clear -RH Tlo Thi CQ1 CQ2 DQ1 DQ2 CC1 CC2 DD1 DD2 CR; lia.
        + clear -RH Thi CQ2 DQ2 CC1 CC2 DD1 DD2 LOC LO; lia.
        + intros i Hi Ci. clear -RH Hi Ci CT DT CC1 CC2 DD1 DD2; lia.
        + subst CH; clear -RH HC30 HR CT DT CC1 CC2 DD1 DD2; lia.
        + clear -RH HC30 CT DT CC1 CC2 DD1 DD2; lia.
        + rewrite HRP'. clear -RH WE3 WE4 WE19 CQ5 DQ5 CC1 CC2 DD1 DD2 HC30; lia.
        + clear -RH WE3 WE4 WE19 CQ5 DQ5 CC1 CC2 DD1 DD2 HC30 A1 G1 G2; lia.
        + clear -RH WE3 WE4 WE19 CQ5 DQ5 CC1 CC2 DD1 DD2 HC30 A5 G3 G4; unfold zlen; lia.
        + rewrite KLE in *. clear -RH Tband CQ4 DQ4 CC1 CC2 DD1 DD2 WE2 WE3 WE4 WE5 CR HC30 A1 A3 G1 G2; Z.div_mod_to_equations; lia.
        + rewrite KLE in *. clear -RH Tband CQ4 DQ4 CC1 CC2 DD1 DD2 WE2 WE3 WE4 WE5 CR HC30 A5 A7 G3 G4; Z.div_mod_to_equations; lia.
        + clear -RH CT DT CC1 CC2 DD1 DD2; lia.
        + clear -RH CT DT CC1 CC2 DD1 DD2; lia. }
    split; [subst a'; unfold sstats_ok, sec_bytes in *; rewrite fin_sec_stats, fin_sec, Pss, Psec; cbn [as_sec_stats as_sec upd_cache_inited]; exact Hss|].
    subst a'. unfold csmall in *. rewrite fin_chunks, Pch. cbn [as_chunks upd_cache_inited]. exact Hcs. }
  split.
  { (* [comment removed for export] *)
    pose proof (RTOK_magree _ _ _ _ _ _ _ _ _ _ _ TOK3 AG5 KIA5) as TOK5.
    apply (RTOK_same_fp E0 FSB0 HR0 L0 RES0 EB0 C C' s a2 a' mo5 TOK5); subst a'; [apply (fin_same_fp E0 c n a2 HC30)| rewrite fin_nprim; reflexivity| rewrite fin_ndepot; reflexivity]. }
  split; [rewrite Ffs5, Ffs3, Ffs2, Ffs1; reflexivity|]. split; [rewrite Ffds5, Ffds3, Ffds2, Ffds1; reflexivity|]. split; [rewrite Ftid5, Ftid3, Ftid2, Ftid1; reflexivity|].
  split.
  { subst a'. unfold refill_same.
    rewrite fin_chunks, fin_dead, fin_tq, fin_gq, fin_sec, fin_sec_stale, fin_sec_stats, fin_ptr, fin_keys, fin_frames, fin_ndepot, fin_nprim, fin_residue,
            fin_node_blocks, fin_store_blocks, fin_store_stored, fin_ia, fin_cache_allocated, fin_everc, fin_glob_allocated, fin_glob_mapped, fin_oom.
    rewrite Pch, Pdd, Ptq, Pgq, Psec, Psst, Pss, Pptr, Pky, Pfr, Pnd, Pnp, Prs, Pnb, Psb, Pstd, Pia, Pcal, Pev, Pga, Pgm, Poom.
    subst a1. clear. destruct a; repeat split; reflexivity. }
  split.
  { intros c' NE. subst a'. rewrite fin_get_cache, fin_get_region. destruct (decide (c' = c)) as [E|_]; [exfalso; exact (NE E)|].
    unfold get_cache at 1. rewrite Pca, (Preg c' NE), GR1. split; [apply (get_cache_upd_cache_inited true a c')| reflexivity]. }
  split; [subst a'; rewrite fin_cache_inited, Pci; reflexivity|].
  subst a'. apply fin_zlen_cache; [clear -HR; lia| exact NFn'].
Qed.
End RfT.


End RC__1.
