(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Mem Cells Step Frame Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanHoare AsanRep AsanKern AsanDepot
  AsanWf1 AsanWf3 AsanWf4 AsanWf5 AsanClient AsanRepFrame AsanBudget AsanHit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma cache_block_clear : forall E (P : list Z) (D : list batch) s c x k cm,
  AWf E P D s -> 1 <= c <= kLargestClassID -> In x (get_cache s c) -> as_chunks s !! k = Some cm ->
  blk_hi s cm <= chunk_of_compact (ae_space_beg E) c x \/ chunk_of_compact (ae_space_beg E) c x + class_size c <= blk_lo cm.
Proof.
  intros E P D s c x k cm WF Hc Hx Hk.
  destruct (cache_entry_untracked E P D s c x WF Hc Hx) as [_ [NCB _]].
  pose proof WF as (WE & WR & (_ & _ & WC3) & [K1 _] & WQ & (_ & _ & WS3 & _) & _).
  destruct (WC3 c Hc) as (_ & _ & Cx). destruct (Cx x Hx) as (CV & _ & _).
  destruct (K1 k cm Hk) as (A & B & C & D0 & _). unfold blk_lo, blk_hi.
  destruct (cm_prim cm) as [c'|].
  - destruct D0 as (D1 & D2 & D3 & _).
    assert (Hc' : 1 <= c' <= kLargestClassID) by (subst c'; apply malloc_class_ok; pose proof (proj1 (from_primary_iff (cm_n cm) ltac:(lia)) D1); lia).
    destruct (carved_blocks_disjoint E s c (chunk_of_compact (ae_space_beg E) c x) c' (cm_alloc_beg cm) Hc Hc' WR CV D3) as [[_ EQ]|[X|X]].
    + exfalso. apply NCB. exists k, cm. split; [exact Hk| symmetry; exact EQ].
    + right. exact X.
    + left. exact X.
  - destruct D0 as (D1 & sc & Hsc & Hab & Hms & _). destruct (WS3 sc Hsc) as (_ & _ & _ & _ & _ & OUT & _).
    pose proof (carved_in_space E s c _ Hc WR CV) as [I1 I2]. rewrite Hab, <- Hms. unfold kRegionSize, kSpaceSize, kPageSize in *.
    pose proof (class_size_mod c Hc) as [_ SZ]. lia.
Qed.

Lemma cache_block_fresh : forall E (P : list Z) (D : list batch) s c x n,
  AWf E P D s -> 1 <= c <= kLargestClassID -> In x (get_cache s c) -> 0 <= n <= 64512 -> c = malloc_class n ->
  as_chunks s !! (chunk_of_compact (ae_space_beg E) c x + rz_size n - kChunkHeaderSize) = None.
Proof.
  intros E P D s c x n WF Hc Hx Hn Ec.
  set (ab0 := chunk_of_compact (ae_space_beg E) c x). set (k := ab0 + rz_size n - kChunkHeaderSize).
  destruct (as_chunks s !! k) as [cm|] eqn:Hk; [| reflexivity]. exfalso.
  pose proof (cache_block_clear E P D s c x k cm WF Hc Hx Hk) as CL. fold ab0 in CL.
  pose proof (chunk_beg_loc E P D s k cm WF Hk) as LOC. pose proof (rz_lt_class n Hn) as RZC. rewrite <- Ec in RZC. pose proof (rz_size_pos n) as RP.
  pose proof WF as (WE & WR & (_ & _ & WC3) & _). destruct (WC3 c Hc) as (_ & _ & Cx). destruct (Cx x Hx) as (CV & _ & _). fold ab0 in CV.
  pose proof (carved_in_space E s c _ Hc WR CV) as [I1 I2].
  unfold blk_lo, blk_hi in CL. unfold kChunkHeaderSize in k.
  destruct (cm_prim cm) as [c'|].
  - destruct LOC as (Hc' & _ & L1 & L2). subst k. lia.
  - destruct LOC as (sc & Hsc & L1 & L2 & OUT). subst k. unfold kRegionSize, kSpaceSize in *. lia.
Qed.

Section RH.
Variable segs : list Segment.
Variable E : aenv.
Hypothesis ICL : ae_ic E = asan_ic.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).
#[warnings="-notation-for-abbreviation"] Notation RW := (rw_cells segs).
#[warnings="-notation-for-abbreviation"] Notation SB := (ae_space_beg E).
#[warnings="-notation-for-abbreviation"] Notation T := (ae_thread E).
Definition TD : Z := 0x18fa58.   (* [comment removed for export] *)
Definition SS : Z := 0x17fa48.   (* [comment removed for export] *)
Definition INS : Z := 0xaa518.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition IMG : Z * Z := (0x10000, 0x5f5000).   (* [comment removed for export] *)
Hypothesis IMGE : fst (ae_img E) = 0x10000 /\ 0x5f3000 <= snd (ae_img E).
(* [comment removed for export] *)
Definition APPR (X L : Z) : Prop :=
  (0 < X /\ X + L <= kLowAppEnd /\ (X + L <= 0x10000 \/ 0x603000 <= X)) \/ kHighMemBeg <= X.
(* [comment removed for export] *)
Lemma APP_APPR : forall X L, app_mem X L -> img_sep E X L -> APPR X L.
Proof. intros X L A B. unfold APPR. unfold app_mem in A. unfold img_sep in B. destruct IMGE as [I1 I2]. rewrite I1 in B. lia. Qed.

Variables (s : astate) (key : list Z) (n : Z) (m m' : mem) (mo : Model) (lo : Z).
#[warnings="-notation-for-abbreviation"] Notation s' := (amalloc_hit_st E key n s).
#[warnings="-notation-for-abbreviation"] Notation c := (hc n).
Definition ab : Z := hab E n s.
Definition rz : Z := rz_size n.
Definition ub : Z := ab + rz.
Definition cb : Z := ub - 16.
Definition N : Z := zlen (depot_keys E s).
Definition HS : list Z := depot_hashes E s.
Definition NB : list Z := node_blocks E s.
Definition fr : Z := as_frames s.
Definition b : Z := fr / kStoreBlockFrames.
Definition sb : Z := nthz (store_blocks E s) b.
Definition h : Z := depot_hash key.
Definition bk : Z := bucket_of h.
Definition len : Z := zlen key.
Definition NAv : Z := node_addr E s (N + 1).
Definition id : Z := hid E key s.

(* [comment removed for export] *)
Definition FPW (z : Z) : Prop :=
     lo <= z
  \/ z = T + kThrUnwinding
  \/ (T + kThrCache + kPerClassSize * c <= z < T + kThrCache + kPerClassSize * c + 4)
  \/ (T + kThrCacheStats + 16 <= z < T + kThrCacheStats + 24)
  \/ (ab <= z < ub + n)
  \/ (kShadowBase + ab / 8 + rz / 8 <= z < kShadowBase + ab / 8 + rz / 8 + (n + 7) / 8)
  \/ (TD + 4 * bk <= z < TD + 4 * bk + 4)
  \/ (TD + 0x400000 <= z < TD + 0x400000 + 4)
  \/ (NAv <= z < NAv + 16)
  \/ (SS <= z < SS + 8)
  \/ (SS + 24 + 16 * b <= z < SS + 28 + 16 * b)
  \/ (sb + 8 * (fr mod kStoreBlockFrames) <= z < sb + 8 * (fr mod kStoreBlockFrames) + 8 * (len + 1))
  \/ (T + kThrStats <= z < T + kThrStats + 24)
  \/ (T + kThrStats + 112 + 8 * c <= z < T + kThrStats + 112 + 8 * c + 8).

Hypothesis WM : wmono segs m m'.
Hypothesis AG : forall z, 0 <= z < 2^64 -> ~ FPW z -> m' (wa z) = m (wa z).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis REP : ARep segs E (DepotR segs E) s m.
Hypothesis WF : AWf E [] [] s.
Hypothesis WF' : AWf E [] [] s'.
Hypothesis HOK : hit_ok E key n s.
Hypothesis CI : as_cache_inited s = true.
Hypothesis AK : AKern E s mo.
Hypothesis HLEN : 0 <= len <= 30.
(* [comment removed for export] *)
Hypothesis TDN : T + 4096 <= ae_depot_nodes E \/ ae_depot_nodes E + kDepotNodeBlockBytes <= T.
Hypothesis DN0 : APPR (ae_depot_nodes E) kDepotNodeBlockBytes /\ ae_depot_nodes E + kDepotNodeBlockBytes <= alloc_ceiling
                 /\ (ae_depot_nodes E + kDepotNodeBlockBytes <= ae_resv_beg E \/ ae_resv_beg E + kResvLen <= ae_depot_nodes E)
                 /\ (ae_depot_nodes E + kDepotNodeBlockBytes <= ae_ptr_array E \/ ae_ptr_array E + kPtrArrayLen <= ae_depot_nodes E)
                 /\ In (ae_depot_nodes E, kDepotNodeBlockBytes) (ae_reserved E).
Hypothesis ST0 : APPR (ae_store_blk E) kStoreBlockBytes /\ ae_store_blk E + kStoreBlockBytes <= alloc_ceiling /\ In (ae_store_blk E, kStoreBlockBytes) (ae_reserved E).
Hypothesis KSEP : (forall i j, 0 <= i < zlen (as_node_blocks s) -> 0 <= j < zlen (as_node_blocks s) -> i <> j ->
                     nthz (as_node_blocks s) i + kDepotNodeBlockBytes <= nthz (as_node_blocks s) j \/ nthz (as_node_blocks s) j + kDepotNodeBlockBytes <= nthz (as_node_blocks s) i)
               /\ (forall nb sk, In nb (as_node_blocks s) -> In sk (as_store_blocks s) -> nb + kDepotNodeBlockBytes <= sk \/ sk + kStoreBlockBytes <= nb).

(* [comment removed for export] *)
Lemma Hn : 1 <= n <= 448. Proof. exact (proj1 HOK). Qed.
Lemma HCc : 1 <= c <= 16.
Proof.
  clear -HOK. pose proof Hn as H. unfold hc, class_id, needed1, rounded, rz_size, rz_log, round_up, kChunkHeader2Size, kMidSize, kMinSize.
  destruct (n <=? 64 - 16) eqn:C1; [apply Z.leb_le in C1| apply Z.leb_gt in C1];
  [| destruct (n <=? 128 - 32) eqn:C2; [apply Z.leb_le in C2| apply Z.leb_gt in C2];
     [| destruct (n <=? 512 - 64) eqn:C3; [apply Z.leb_le in C3| apply Z.leb_gt in C3]; [| lia]]];
  cbn [Z.pow Z.pow_pos Pos.iter Z.mul];
  match goal with |- context [if ?cnd then _ else _] => replace cnd with true by (symmetry; apply Z.leb_le; Z.div_mod_to_equations; lia) end;
  Z.div_mod_to_equations; lia.
Qed.


Lemma CS32 : class_size c = 32 * c.
Proof. pose proof HCc. unfold class_size, kMidClass, kMinSize. replace (c <=? 16) with true by (symmetry; apply Z.leb_le; lia). reflexivity. Qed.
Lemma RZ : (rz = 16 \/ rz = 32 \/ rz = 64) /\ rz + 8 <= class_size c /\ rz + n <= class_size c /\ rz = 16 * 2 ^ rz_log n.
Proof.
  pose proof Hn as H. unfold rz. pose proof (malloc_class_ok n ltac:(lia)) as [_ M]. unfold malloc_class in M. fold (hc n) in M.
  pose proof (rounded_ge n) as (R1 & _). unfold needed1 in M.
  assert (X : rz_size n = 16 \/ rz_size n = 32 \/ rz_size n = 64).
  { unfold rz_size, rz_log. destruct (n <=? 64 - 16); [left; reflexivity|]. destruct (n <=? 128 - 32); [right; left; reflexivity|].
    destruct (n <=? 512 - 64) eqn:C3; [right; right; reflexivity|]. apply Z.leb_gt in C3. lia. }
  split; [exact X|]. split; [lia|]. split; [lia| reflexivity].
Qed.

(* [comment removed for export] *)
Lemma XIN : In (hx n s) (get_cache s c).
Proof. unfold hx. fold (hc n). destruct (get_cache s c) as [|y l] eqn:EL; [exfalso; exact (proj1 (proj2 HOK) EL)|]. rewrite (app_removelast_last (l:=y::l) 0 ltac:(discriminate)) at 2. apply in_app_iff. right. left. reflexivity. Qed.
Lemma CARVED : carved E s c ab /\ (16 * hx n s) mod class_size c = 0 /\ ~ In (hx n s) (rg_free (get_region s c)).
Proof.
  pose proof WF as (_ & _ & (_ & _ & C3) & _). pose proof HCc. destruct (C3 c ltac:(unfold kLargestClassID; lia)) as (_ & _ & Cx).
  destruct (Cx _ XIN) as (A & B & C). unfold ab, hab. split; [exact A| split; [exact B| exact C]].
Qed.
Lemma ABR : SB + c * kRegionSize <= ab /\ ab + class_size c <= SB + c * kRegionSize + rg_mapped_user (get_region s c)
            /\ rg_mapped_user (get_region s c) <= kFreeArrayOffset /\ ab mod 16 = 0.
Proof.
  pose proof CARVED as ((k & Hk & Hab & Hk1) & _). pose proof WF as (WE & [_ WR] & _). pose proof HCc as Hc.
  destruct (WR c ltac:(unfold kLargestClassID; lia)) as (R1 & R2 & R3 & _). unfold region_of, region_beg in *.
  pose proof (class_size_mod c ltac:(lia)) as [CM CSB]. pose proof (proj1 WE) as SBA.
  rewrite Hab. split; [clear -Hk CSB; nia|]. split; [clear -Hk1 R1 CSB; nia|]. split; [exact R3|].
  rewrite CS32. rewrite CS32 in CM. unfold kRegionSize. apply Z.mod_divide in SBA; [| lia]. destruct SBA as [q Hq]. rewrite Hq.
  apply Z.mod_divide; [lia|]. exists (q * 2^12 + c * 2^28 + k * 2 * c). lia.
Qed.

(* [comment removed for export] *)
Lemma GEO :
     kHighMemBeg <= ae_resv_beg E /\ ae_resv_beg E <= SB /\ SB + kSpaceSize + 4096 <= ae_resv_beg E + kResvLen /\ ae_resv_beg E + kResvLen <= alloc_ceiling
  /\ APPR T 4096 /\ T + 4096 <= alloc_ceiling /\ (T + 4096 <= ae_resv_beg E \/ ae_resv_beg E + kResvLen <= T)
  /\ In (T, 4096) (ae_reserved E) /\ In (ae_resv_beg E, kResvLen) (ae_reserved E) /\ In (ae_ptr_array E, 0x800000) (ae_reserved E)
  /\ APPR (ae_ptr_array E) 0x800000 /\ ae_ptr_array E + 0x800000 <= alloc_ceiling
  /\ (ae_ptr_array E + 0x800000 <= ae_resv_beg E \/ ae_resv_beg E + kResvLen <= ae_ptr_array E).
Proof.
  pose proof WF as (WE & _). destruct WE as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12 & W13 & W14 & W15 & W16 & W17 & W18 & W19 & W20
     & W21 & W22 & W23 & W24 & W25 & W26 & W27 & W28 & IMG1 & IMG2 & IMG3 & IST & ISP & ISF & ISI).
  pose proof (APP_APPR _ _ W14 IST) as AT. pose proof (APP_APPR _ _ W16 ISP) as AP.
  pose proof (ak_resv_geom _ _ _ AK) as (G1 & _ & G3). unfold kResvLen, kPageSize in *. repeat split; try assumption; lia.
Qed.
(* [comment removed for export] *)
Lemma img_sep_of_reserved : forall X L, (forall r, In r (ae_reserved E) -> X + L <= fst r \/ fst r + snd r <= X) -> img_sep E X L.
Proof.
  intros X L H. pose proof WF as (WE & _).
  destruct WE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IMG1 & _).
  unfold img_sep. destruct (ae_img E) as [ib il] eqn:EI. cbn [fst snd]. apply (H (ib, il)). first [exact IMG1| rewrite <- EI; exact IMG1].
Qed.

(* [comment removed for export] *)
Lemma NBfacts : forall blk, In blk NB ->
  APPR blk kDepotNodeBlockBytes /\ blk + kDepotNodeBlockBytes <= alloc_ceiling
  /\ (blk + kDepotNodeBlockBytes <= ae_resv_beg E \/ ae_resv_beg E + kResvLen <= blk)
  /\ (blk + kDepotNodeBlockBytes <= T \/ T + 4096 <= blk)
  /\ (blk + kDepotNodeBlockBytes <= ae_ptr_array E \/ ae_ptr_array E + kPtrArrayLen <= blk)
  /\ (forall sc, In sc (as_sec s) -> blk + kDepotNodeBlockBytes <= sc_map_beg sc \/ sc_map_beg sc + sc_map_size sc <= blk).
Proof.
  intros blk [<-|Hb].
  - destruct DN0 as (A1 & A2 & A3 & A4 & A5). repeat split; try assumption; [clear -TDN; destruct TDN; [right|left]; assumption|].
    intros sc Hsc. pose proof WF as (_ & _ & _ & _ & _ & (_ & _ & S3 & _) & _). destruct (S3 sc Hsc) as (_ & _ & _ & _ & _ & _ & R). destruct (R _ A5); cbn in *; lia.
  - destruct (ak_blocks_sep _ _ _ AK blk kDepotNodeBlockBytes (or_introl (conj Hb eq_refl))) as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof GEO as (_ & _ & _ & _ & _ & _ & _ & RT & _ & RP & _). apply (APP_APPR _ _) in B1; [| exact (img_sep_of_reserved _ _ B6)].
    repeat split; try assumption.
    + destruct (B6 _ RT); cbn in *; lia.
    + destruct (B6 _ RP); cbn in *; unfold kPtrArrayLen; lia.
Qed.
Lemma SBfacts : forall blk, In blk (store_blocks E s) ->
  APPR blk kStoreBlockBytes /\ blk + kStoreBlockBytes <= alloc_ceiling
  /\ (blk + kStoreBlockBytes <= ae_resv_beg E \/ ae_resv_beg E + kResvLen <= blk)
  /\ (blk + kStoreBlockBytes <= T \/ T + 4096 <= blk)
  /\ (blk + kStoreBlockBytes <= ae_ptr_array E \/ ae_ptr_array E + kPtrArrayLen <= blk)
  /\ (forall sc, In sc (as_sec s) -> blk + kStoreBlockBytes <= sc_map_beg sc \/ sc_map_beg sc + sc_map_size sc <= blk)
  /\ (forall nb, In nb NB -> nb + kDepotNodeBlockBytes <= blk \/ blk + kStoreBlockBytes <= nb).
Proof.
  intros blk [<-|Hb].
  - pose proof (ak_store_sep _ _ _ AK) as (S1 & S2 & S3 & S4 & S5). destruct ST0 as (A1 & A2 & A5). unfold kStoreBlockBytes, kPageSize in *.
    repeat split; try assumption; try lia.
    intros nb [<-|Hnb]; [unfold kDepotNodeBlockBytes; lia|].
    destruct (ak_blocks_sep _ _ _ AK nb kDepotNodeBlockBytes (or_introl (conj Hnb eq_refl))) as (_ & _ & _ & _ & _ & B6). destruct (B6 _ A5); cbn in *; lia.
  - destruct (ak_blocks_sep _ _ _ AK blk kStoreBlockBytes (or_intror (conj Hb eq_refl))) as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof GEO as (_ & _ & _ & _ & _ & _ & _ & RT & _ & RP & _). apply (APP_APPR _ _) in B1; [| exact (img_sep_of_reserved _ _ B6)].
    repeat split; try assumption.
    + destruct (B6 _ RT); cbn in *; lia.
    + destruct (B6 _ RP); cbn in *; unfold kPtrArrayLen; lia.
    + intros nb [<-|Hnb]; [| exact (proj2 KSEP nb blk Hnb Hb)]. destruct DN0 as (_ & _ & _ & _ & A5). destruct (B6 _ A5); cbn in *; lia.
Qed.

Hypothesis BLT : 0 <= b < kStoreBlockCount.   (* [comment removed for export] *)
Hypothesis TPA : T + 4096 <= ae_ptr_array E \/ ae_ptr_array E + kPtrArrayLen <= T.

Lemma BKR : 0 <= bk < kTabSize.
Proof. unfold bk, bucket_of. apply Z.mod_pos_bound. unfold kTabSize. lia. Qed.
Lemma NAVin : exists blk, In blk NB /\ blk <= NAv /\ NAv + 16 <= blk + kDepotNodeBlockBytes.
Proof.
  unfold NAv, NB. apply node_addr_in_block; [unfold N, zlen; lia|].
  pose proof REP as (_ & _ & _ & _ & _ & _ & _ & [DI _] & _). destruct DI as (_ & _ & _ & _ & D5 & _). pose proof (proj1 (proj2 (proj2 HOK))) as HNB.
  unfold N. unfold node_blocks. unfold zlen in *. cbn [length]. unfold depot_keys. rewrite length_app. unfold depot_n_ids in D5, HNB. unfold kDepotNodesPerBlock in *.
  apply Z.div_lt_upper_bound; [lia|].
  destruct (Z.eq_dec (Z.of_nat (length (ae_keys0 E) + length (as_keys s)) + 1) (65536 * (Z.of_nat (length (as_node_blocks s)) + 1))) as [EQ|NE]; [| lia].
  exfalso. apply HNB. rewrite EQ, Z.mul_comm. apply Z_mod_mult.
Qed.
Lemma SBin : In sb (store_blocks E s).
Proof.
  unfold sb, nthz. pose proof HOK as (_ & _ & _ & _ & _ & HSB & HF & _). fold fr in HSB, HF. fold b in HSB.
  assert (0 <= b) by (unfold b; apply Z.div_pos; [exact HF| unfold kStoreBlockFrames; lia]).
  replace ((0 <=? b) && (b <? zlen (store_blocks E s))) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
  apply nth_In. unfold zlen in HSB. lia.
Qed.

(* [comment removed for export] *)
Ltac peel D := first [destruct D as [D|D]; [| peel D] | idtac].
Ltac consts := unfold APPR in *; rewrite ?kHighMemBeg_val, ?kLowAppEnd_val in *; unfold alloc_ceiling, kResvLen, kSpaceSize, kRegionSize, kFreeArrayOffset, kFreeArraySize, kTabSize, kStoreBlockCount, kPtrArrayLen,
              kDepotNodeBlockBytes, kStoreBlockBytes, kStoreBlockFrames, kShadowBase, kThrUnwinding, kThrCache, kThrCacheStats, kThrStats, kPerClassSize, kRegSize, TD, SS in *;
              change (2^37) with 137438953472 in *; change (2^32) with 4294967296 in *; change (2^29) with 536870912 in *; change (2^23) with 8388608 in *;
              change (2^20) with 1048576 in *; change (2^18) with 262144 in *.
(* [comment removed for export] *)
Lemma FPWfacts :
     alloc_ceiling <= lo /\ APPR T 4096 /\ T + 4096 <= alloc_ceiling /\ kHighMemBeg <= ab /\ ub + n <= alloc_ceiling /\ ub + n <= ab + class_size c
  /\ 0 <= bk < kTabSize /\ 0 <= b < kStoreBlockCount /\ APPR NAv 16 /\ NAv + 16 <= alloc_ceiling /\ APPR sb kStoreBlockBytes /\ sb + kStoreBlockBytes <= alloc_ceiling
  /\ 0 <= fr mod kStoreBlockFrames /\ fr mod kStoreBlockFrames + (len + 1) <= kStoreBlockFrames /\ 0 <= len /\ 1 <= c <= 16
  /\ kShadowBase + kHighMemBeg / 8 <= kShadowBase + ab / 8 /\ kShadowBase + ab / 8 + rz / 8 + (n + 7) / 8 <= kHighMemBeg /\ 0 <= rz.
Proof.
  pose proof GEO as (G1 & G2 & G3 & G4 & G5 & G6 & _). pose proof ABR as (A1 & A2 & A3 & A4). pose proof RZ as (R1 & R2 & R3 & R4). pose proof HCc as HC. pose proof CS32 as CS. pose proof Hn as HN.
  destruct NAVin as (blk & Hb & NV1 & NV2). pose proof (NBfacts blk Hb) as (NB1 & NB2 & _). pose proof (SBfacts sb SBin) as (SB1 & SB2 & _).
  pose proof HOK as (_ & _ & _ & HNS & HK & _). fold fr len in HNS. pose proof (Z.mod_pos_bound fr kStoreBlockFrames ltac:(unfold kStoreBlockFrames; lia)) as FM.
  pose proof BKR. pose proof BLT. pose proof LO. unfold ub. fold len in HK.
  assert (APN : APPR NAv 16) by (clear -NB1 NV1 NV2; unfold APPR, kDepotNodeBlockBytes in *; lia).
  clear REP AG WM WF WF' HOK AK KSEP CI TDN DN0 ST0 TPA Hb.   (* [comment removed for export] *)
  repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
  - consts. clear -A1 G1 G2 HC. nia.
  - consts. clear -A2 A3 HC CS G2 G3 G4 R3. nia.
  - consts. assert (HAB : 17594333495296 <= ab) by (clear -A1 G1 G2 HC; nia). clear -HAB. change (17594333495296 / 8) with 2199291686912. Z.div_mod_to_equations. lia.
  - consts. assert (HAB : ab + class_size c <= SB + 137438953472) by (clear -A2 A3 HC CS; nia). clear -HAB R1 R3 HN A4 G3 G4. change (17594333495296 / 8) with 2199291686912 in *. Z.div_mod_to_equations. lia.
Qed.

Lemma AGR_img : forall A k, 0x10000 <= A -> A + k <= 0x603000 ->
  (A + k <= TD + 4 * bk \/ TD + 4 * bk + 4 <= A) -> (A + k <= TD + 0x400000 \/ TD + 0x400004 <= A) ->
  (A + k <= SS \/ SS + 8 <= A) -> (A + k <= SS + 24 + 16 * b \/ SS + 28 + 16 * b <= A) -> agree_on m m' A k.
Proof.
  intros A k Hnn H0 H1 H2 H3 H4 z Hz. apply AG; [clear -Hnn H0 Hz; lia|]. intros D. pose proof alloc_ceiling_range as CR.
  pose proof FPWfacts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 & F19). unfold FPW in D. consts.
  (* [comment removed for export] *)
  destruct D as [D|[D|[D|[D|[D|[D|[D|[D|[D|[D|[D|[D|[D|D]]]]]]]]]]]]].
  - clear -D Hz H0 F1 CR. lia. - clear -D Hz Hnn H0 F2. lia. - clear -D Hz Hnn H0 F2 F16. lia. - clear -D Hz Hnn H0 F2. lia.
  - clear -D Hz H0 F4. lia. - clear -D Hz H0 F4 F17 F19. lia. - clear -D Hz H1. lia. - clear -D Hz H2. lia.
  - clear -D Hz Hnn H0 F9. lia. - clear -D Hz H3. lia. - clear -D Hz H4. lia. - clear -D Hz Hnn H0 F11 F13 F14 F15. lia.
  - clear -D Hz Hnn H0 F2. lia. - clear -D Hz Hnn H0 F2 F16. lia.
Qed.
Lemma AGR_high : forall A k, APPR A k -> A + k <= alloc_ceiling ->
  (A + k <= T \/ T + 4096 <= A) -> (A + k <= ab \/ ub + n <= A) -> (A + k <= NAv \/ NAv + 16 <= A) -> (A + k <= sb \/ sb + kStoreBlockBytes <= A) ->
  agree_on m m' A k.
Proof.
  intros A k H0 H00 H1 H2 H3 H4 z Hz. apply AG; [clear -H0 H00 Hz; unfold APPR in *; rewrite kHighMemBeg_val, kLowAppEnd_val in *; unfold alloc_ceiling in *; lia|]. intros D.
  pose proof alloc_ceiling_range as CR. pose proof BKR as F7'. pose proof BLT as F8'.
  pose proof FPWfacts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 & F19). unfold FPW in D. consts.
  destruct D as [D|[D|[D|[D|[D|[D|[D|[D|[D|[D|[D|[D|[D|D]]]]]]]]]]]]].
  - clear -D Hz H00 F1. lia. - clear -D Hz H1. lia. - clear -D Hz H1 F16. lia. - clear -D Hz H1. lia.
  - clear -D Hz H2. lia. - clear -D Hz H0 F4 F17 F18 F19. lia. - clear -D Hz H0 H00 F7' CR. lia. - clear -D Hz H0 H00 CR. lia.
  - clear -D Hz H3. lia. - clear -D Hz H0 H00 CR. lia. - clear -D Hz H0 H00 F8' CR. lia. - clear -D Hz H4 F13 F14 F15. lia.
  - clear -D Hz H1. lia. - clear -D Hz H1 F16. lia.
Qed.
Lemma AGR_thr : forall A k, T <= A -> A + k <= T + 4096 ->
  (A + k <= T + kThrUnwinding \/ T + kThrUnwinding + 1 <= A) ->
  (A + k <= T + kThrCache + kPerClassSize * c \/ T + kThrCache + kPerClassSize * c + 4 <= A) ->
  (A + k <= T + kThrCacheStats + 16 \/ T + kThrCacheStats + 24 <= A) ->
  (A + k <= T + kThrStats \/ T + kThrStats + 24 <= A) ->
  (A + k <= T + kThrStats + 112 + 8 * c \/ T + kThrStats + 112 + 8 * c + 8 <= A) -> agree_on m m' A k.
Proof.
  intros A k H0 H00 H1 H2 H3 H4 H5 z Hz. pose proof GEO as (Ga & Gb & Gc & Gd & Ge & Gf & _).
  apply AG; [clear -H0 H00 Hz Ge Gf; unfold APPR in *; rewrite kHighMemBeg_val, kLowAppEnd_val in *; unfold alloc_ceiling in *; lia|]. clear Ga Gb Gc Gd Ge Gf. intros D.
  pose proof alloc_ceiling_range as CR.
  destruct NAVin as (blk & Hb & NV1 & NV2). pose proof (NBfacts blk Hb) as (_ & _ & _ & NBT & _). pose proof (SBfacts sb SBin) as (_ & _ & _ & SBT & _).
  pose proof GEO as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & _). pose proof ABR as (A1 & A2 & A3 & A4).
  pose proof FPWfacts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 & F19). unfold FPW in D. consts.
  destruct D as [D|[D|[D|[D|[D|[D|[D|[D|[D|[D|[D|[D|[D|D]]]]]]]]]]]]].
  - clear -D Hz H00 F1 F3. lia. - clear -D Hz H0 H00 H1. lia. - clear -D Hz H0 H00 H2. lia. - clear -D Hz H0 H00 H3. lia.
  - clear -D Hz H0 H00 A1 A2 A3 G2 G3 G7 F6 F16. nia. - clear -D Hz H0 H00 F2 F4 F17 F18 F19. lia. - clear -D Hz H0 H00 F2 F7 CR. lia. - clear -D Hz H0 H00 F2 CR. lia.
  - clear -D Hz H0 H00 NV1 NV2 NBT. lia. - clear -D Hz H0 H00 F2 CR. lia. - clear -D Hz H0 H00 F2 F8 CR. lia. - clear -D Hz H0 H00 SBT F13 F14 F15. lia.
  - clear -D Hz H0 H00 H4. lia. - clear -D Hz H0 H00 H5. lia.
Qed.
Lemma AGR_shadow : forall A k, kShadowBase <= A -> A + k <= kHighMemBeg ->
  (A + k <= kShadowBase + ab / 8 + rz / 8 \/ kShadowBase + ab / 8 + rz / 8 + (n + 7) / 8 <= A) -> agree_on m m' A k.
Proof.
  intros A k H0 H00 H1 z Hz. apply AG; [clear -H0 H00 Hz; rewrite kHighMemBeg_val in *; unfold kShadowBase in *; lia|]. intros D.
  pose proof alloc_ceiling_range as CR.
  destruct NAVin as (blk & Hb & NV1 & NV2). pose proof (NBfacts blk Hb) as (NB1 & _). pose proof (SBfacts sb SBin) as (SB1 & _).
  pose proof FPWfacts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 & F19). unfold FPW in D. consts.
  destruct D as [D|[D|[D|[D|[D|[D|[D|[D|[D|[D|[D|[D|[D|D]]]]]]]]]]]]].
  - clear -D Hz H00 F1 CR. lia. - clear -D Hz H0 H00 F2 CR. lia. - clear -D Hz H0 H00 F2 F16 CR. lia. - clear -D Hz H0 H00 F2 CR. lia.
  - clear -D Hz H00 F4. lia. - clear -D Hz H1. lia. - clear -D Hz H0 H00 F7 CR. lia. - clear -D Hz H0 H00 CR. lia.
  - clear -D Hz H0 H00 NB1 NV1 NV2 CR. lia. - clear -D Hz H0 H00 CR. lia. - clear -D Hz H0 H00 F8 CR. lia. - clear -D Hz H0 H00 SB1 F13 F14 F15 CR. lia.
  - clear -D Hz H0 H00 F2 CR. lia. - clear -D Hz H0 H00 F2 F16 CR. lia.
Qed.

(* [comment removed for export] *)
Ltac lits := rewrite ICL; cbn [aic_instance aic_asan_flags aic_common_flags aic_shadow_dyn_addr aic_kHighMemEnd aic_can_poison_memory aic_asan_inited aic_malloc_context_size
       aic_page_size_cached aic_dying_flag aic_stack_anchor aic_REAL_memcpy_var aic_malloc_hook_table aic_internal_alloc_initialized aic_internal_allocator_instance
       aic_theDepot aic_stackStore asan_ic].
Ltac img := let HBK := fresh in let HBL := fresh in pose proof BKR as HBK; pose proof BLT as HBL; apply AGR_img; clear -HBK HBL; consts; lia.

Lemma repA : arep_instance segs E s' m'.
Proof.
  pose proof REP as (RA & _). destruct RA as (X1 & X2 & X3 & X4 & (bsl & X5 & L5) & X6 & X7 & X8 & X9 & X10 & X11 & X12).
  unfold arep_instance. rewrite hit_ptr, hit_sec_stats, hit_gq, (proj1 (hit_glob E key n s)), (proj2 (hit_glob E key n s)). unfold n_chunks, gq_bytes. rewrite hit_sec, hit_gq.
  unfold ae_instance in *. unfold n_chunks, gq_bytes in *.
  unfold kInsSpaceBeg, kInsSecondary, kInsNReserved, kInsSecStats, kInsSecMutex, kInsGlobalStats, kInsQuarantine, kInsQMutex, kInsQGlobal, kInsFallbackMutex, kInsMaxUserDefined in *.
  revert X1 X2 X3 X4 X5 L5 X6 X7 X8 X9 X10 X11 X12. lits. intros.
  Ltac rwA H := eapply rw_cells_agree'; [| exact H]; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ]; img.
  split; [rwA X1|]. split; [rwA X2|]. split; [rwA X3|]. split; [rwA X4|].
  split; [exists bsl; split; [| exact L5]; eapply u64arr_agree; [| exact X5]; rewrite L5; cbn [length ziota Z.of_nat Pos.of_succ_nat Pos.succ Nat.add]; img|].
  split; [rwA X6|]. split; [rwA X7|]. split; [rwA X8|]. split; [rwA X9|]. split; [rwA X10|]. split; [rwA X11| rwA X12].
Qed.

Lemma repI : arep_globals segs E s' m'.
Proof.
  pose proof REP as (_ & _ & _ & _ & _ & _ & _ & _ & RI' & _).
  destruct RI' as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & I12 & I13 & I14 & I15 & I16 & I17 & I18). unfold arep_globals.
  rewrite hit_ia. unfold kIaPageSizeOff, kIaChunksPtrOff in *.
  revert I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 I15 I16 I17 I18. lits. intros.
  (* [comment removed for export] *)
  Ltac rwI H := eapply rw_cells_agree'; [| exact H]; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ]; img.
  split; [eapply u8arr_agree; [| exact I1]; rewrite length_map; cbn [length asan_flags_bytes]; img|].
  split; [rwI I2|]. split; [rwI I3|]. split; [rwI I4|]. split; [rwI I5|]. split; [rwI I6|]. split; [rwI I7|]. split; [rwI I8|].
  split; [rwI I9|]. split; [rwI I10|]. split; [rwI I11|]. split; [rwI I12|]. split; [rwI I13|].
  split; [eapply u64arr_agree; [| exact I14]; rewrite length_map, repeat_length; img|].
  split; [rwI I15|].
  split; [intros Hia; rwI (I16 Hia)|].
  split; [eapply u8arr_agree; [| exact I17]; rewrite zeros_ia_len; img|].
  eapply wr_at_transport; [exact I18| exact WM].
Qed.

Lemma repB : arep_regioninfo segs E s' m'.
Proof.
  pose proof REP as (_ & RB & _). unfold arep_regioninfo in *. intros c' Hc'.
  unfold region_of, get_region in *. rewrite hit_regions. eapply rw_cells_agree'; [| exact (RB c' Hc')]. unfold kNumClasses in Hc'.
  unfold ae_region_info. cbn [cells_size region_cells csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ Pos.add].
  pose proof GEO as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & _). pose proof ABR as (A1 & A2 & A3 & _). pose proof HCc. pose proof CS32.
  destruct NAVin as (blk & Hb & NV1 & NV2). pose proof (NBfacts blk Hb) as (_ & _ & NBR & _). pose proof (SBfacts sb SBin) as (_ & _ & SBR & _).
  pose proof RZ as (_ & _ & R3 & _). apply AGR_high; unfold ub; consts.
  - clear -G1 G2 Hc'. lia. - clear -G3 G4 Hc'. lia. - clear -G7 G2 G3 Hc'. lia. - clear -A2 A3 H H0 R3 Hc'. nia.
  - clear -NBR NV1 NV2 G2 G3 Hc'. lia. - clear -SBR G2 G3 Hc'. lia.
Qed.

Lemma repC : arep_region_mem segs E s' m'.
Proof.
  pose proof REP as (_ & _ & RC & _). unfold arep_region_mem in *. intros c' Hc'. destruct (RC c' Hc') as (W & junk & U & L). unfold kNumClasses in Hc'.
  unfold region_of, get_region in *. rewrite hit_regions. split.
  - eapply wr_at_transport; [exact W| exact WM].
  - exists junk. split; [| exact L]. eapply u32arr_agree; [| exact U]. rewrite length_app, length_map.
    pose proof WF as (_ & [_ WR] & _).
    assert (FA : 0 <= rg_mapped_fa match as_regions s !! c' with Some r => r | None => region0 end <= kFreeArraySize).
    { destruct (Z_lt_le_dec 0 c') as [P|P].
      - destruct (Z_lt_le_dec kLargestClassID c') as [Q|Q].
        + destruct (as_regions s !! c') as [r|] eqn:R; [exfalso; pose proof (proj1 (proj1 (proj2 WF)) c' r R); lia| cbn; unfold kFreeArraySize; lia].
        + destruct (WR c' ltac:(lia)) as (_ & _ & _ & _ & F1 & _ & F2 & _). unfold region_of, get_region in F1, F2. lia.
      - destruct (as_regions s !! c') as [r|] eqn:R; [exfalso; pose proof (proj1 (proj1 (proj2 WF)) c' r R); lia| cbn; unfold kFreeArraySize; lia]. }
    pose proof GEO as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & _). pose proof ABR as (A1 & A2 & A3 & _). pose proof HCc. pose proof CS32. pose proof RZ as (_ & _ & R3 & _).
    destruct NAVin as (blk & Hb & NV1 & NV2). pose proof (NBfacts blk Hb) as (_ & _ & NBR & _). pose proof (SBfacts sb SBin) as (_ & _ & SBR & _).
    unfold free_array, region_beg. apply AGR_high; unfold ub, kFreeArraySize in *; consts.
    + clear -G1 G2 Hc'. lia. + clear -G3 G4 Hc' FA L. lia. + clear -G7 G2 G3 Hc' FA L. lia.
    + (* [comment removed for export] *)
      clear -A1 A2 A3 H H0 R3 Hc' FA L. destruct (Z_lt_le_dec c' c); [left; nia|]. right; nia.
    + clear -NBR NV1 NV2 G2 G3 Hc' FA L. lia. + clear -SBR G2 G3 Hc' FA L. lia.
Qed.

Lemma repE : arep_secondary segs E s' m'.
Proof.
  pose proof REP as (_ & _ & _ & _ & RE & _). destruct RE as [E1 E2]. unfold arep_secondary. rewrite hit_ptr, hit_sec.
  pose proof GEO as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13). pose proof ABR as (A1 & A2 & A3 & _). pose proof HCc. pose proof CS32. pose proof RZ as (_ & _ & R3 & _).
  destruct NAVin as (blk & Hb & NV1 & NV2). pose proof (NBfacts blk Hb) as (_ & _ & NBR & _ & NBP & NBS). pose proof (SBfacts sb SBin) as (_ & _ & SBR & _ & SBP & SBS & _).
  pose proof WF as (_ & _ & _ & _ & _ & (_ & _ & WS3 & _) & _).
  split.
  - destruct E1 as [E1|(E11 & junk & U & L)]; [left; exact E1| right]. split; [exact E11|]. exists junk. split; [| exact L].
    eapply u64arr_agree; [| exact U].
    pose proof (f_equal Z.of_nat L) as L'. rewrite Z2Nat.id in L' by (cbv; discriminate). clear L. rewrite length_app, length_map. unfold kChunksBlockCount in L'.
    apply AGR_high; unfold ub; consts.
    + clear -G11 L'. lia. + clear -G12 L'. lia. + clear -TPA L'. lia. + clear -G13 G2 G3 A1 A2 A3 H H0 R3 L'. nia. + clear -NBP NV1 NV2 L'. lia. + clear -SBP L'. lia.
  - intros i sc Hi. destruct (E2 i sc Hi) as [X1 X2]. split; [| eapply wr_at_transport; [exact X2| exact WM]].
    eapply rw_cells_agree'; [| exact X1]. cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ Pos.add].
    pose proof (nth_error_In _ _ Hi) as IN. destruct (WS3 sc IN) as (S1 & S2 & S3 & S4 & S5 & S6 & S7). pose proof (S7 _ G8) as S8. cbn [fst snd] in S8.
    pose proof (NBS sc IN) as S9. pose proof (SBS sc IN) as S10.
    assert (S45 : 4096 <= sc_map_size sc) by (clear -S4 S5; unfold kPageSize in S5; Z.div_mod_to_equations; lia).
    pose proof (APP_APPR _ _ S2 (img_sep_of_reserved _ _ S7)) as S2'.
    apply AGR_high; unfold ub; consts.
    + clear -S2' S45. lia. + clear -S3 S45. lia. + clear -S8 S45. lia. + clear -S6 S45 G2 G3 A1 A2 A3 H H0 R3. nia. + clear -S9 NV1 NV2 S45. lia. + clear -S10 S45. lia.
Qed.

Lemma CS24 : class_size kBatchClass = 8192. Proof. reflexivity. Qed.
Lemma repG : arep_batches segs s' m'.
Proof.
  pose proof REP as (_ & _ & _ & _ & _ & _ & RG & _).
  pose proof GEO as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & _). pose proof ABR as (A1 & A2 & A3 & _). pose proof HCc. pose proof CS32. pose proof RZ as (_ & _ & R3 & _).
  destruct NAVin as (blk & Hb & NV1 & NV2). pose proof (NBfacts blk Hb) as (_ & _ & NBR & _). pose proof (SBfacts sb SBin) as (_ & _ & SBR & _).
  pose proof WF as (_ & [_ WR] & _ & _ & (WQ1 & _) & _).
  destruct (WR kBatchClass ltac:(unfold kBatchClass, kLargestClassID; lia)) as (Q1 & Q2 & Q3 & _). unfold region_of in Q1, Q2, Q3. rewrite ?CS24 in *.
  assert (BA : forall ba, In ba (as_tq s ++ as_gq s) -> SB + 24 * kRegionSize <= b_addr ba /\ b_addr ba + 8192 <= SB + 24 * kRegionSize + kFreeArrayOffset).
  { intros ba Hba. destruct (WQ1 ba Hba) as [((k & Hk & Hab & Hk1) & _) _]. unfold region_beg, region_of in *. rewrite Hab. rewrite ?CS24 in *. unfold kBatchClass in *. change (class_size 24) with 8192 in *. clear -Hk Hk1 Q1 Q2 Q3. nia. }
  assert (BL : forall l, (forall ba, In ba l -> In ba (as_tq s ++ as_gq s)) -> arep_batch_list segs s l m -> arep_batch_list segs s' l m').
  { induction l as [|ba l IH]; intros SUB HBL; [exact I|]. destruct HBL as [[X1 (junk & X2 & L)] H2]. split; [| apply IH; [intros b' Hb'; apply SUB; right; exact Hb'| exact H2]].
    pose proof (BA ba ltac:(apply SUB; left; reflexivity)) as [BA1 BA2].
    pose proof (f_equal Z.of_nat L) as L'. rewrite Z2Nat.id in L' by (cbv; discriminate). unfold kBatchCap in L'.
    split.
    - eapply rw_cells_agree'; [| exact X1]. cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ Pos.add].
      apply AGR_high; unfold ub; consts.
      + clear -G1 G2 BA1. lia. + clear -G3 G4 BA2. lia. + clear -G7 G2 G3 BA1 BA2. lia. + clear -A2 A3 H H0 R3 BA1. right. nia. + clear -NBR NV1 NV2 G2 G3 BA1 BA2. lia. + clear -SBR G2 G3 BA1 BA2. lia.
    - exists junk. split; [| exact L].
      eapply u64arr_agree; [| exact X2]. rewrite length_app, length_map.
      apply AGR_high; unfold ub; consts.
      + clear -G1 G2 BA1. lia. + clear -G3 G4 BA2 L'. lia. + clear -G7 G2 G3 BA1 BA2 L'. lia. + clear -A2 A3 H H0 R3 BA1. right. nia. + clear -NBR NV1 NV2 G2 G3 BA1 BA2 L'. lia. + clear -SBR G2 G3 BA1 BA2 L'. lia. }
  destruct RG as [RG1 RG2]. unfold arep_batches. rewrite hit_tq, hit_gq. split; (apply BL; [| assumption]); intros ba Hba; apply in_app_iff; [left| right]; exact Hba.
Qed.

(* [comment removed for export] *)
Lemma wr_at_sub : forall mm a nn a' n', wr_at segs mm a nn -> a <= a' -> a' + n' <= a + nn -> wr_at segs mm a' n'.
Proof. clear. intros mm a nn a' n' (W0 & W1 & WR) H1 H2. split; [lia|]. split; [lia|]. intros i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply WR. lia. Qed.
Lemma rh_split : forall mm A cs1 cs2,
  rw_cells segs mm A (cs1 ++ cs2) -> rw_cells segs mm A cs1 /\ rw_cells segs mm (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  clear. intros mm A cs1 cs2 [[WF0 B] W]. apply cells_wf_app in WF0. destruct WF0 as [W1 W2].
  rewrite cells_bytes_app in B. apply bytes_at_app in B. destruct B as [B1 B2]. rewrite (cells_bytes_length _ W1) in B2.
  rewrite cells_size_app in W. destruct W as (Wa & Wb & Wr).
  split; split; try (split; assumption).
  - split; [lia|]. split; [lia|]. intros i Hi. apply Wr. lia.
  - split; [lia|]. split; [lia|]. intros i Hi. replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply Wr. lia.
Qed.
Lemma rh_join : forall mm A cs1 cs2,
  rw_cells segs mm A cs1 -> rw_cells segs mm (A + Z.of_nat (cells_size cs1)) cs2 -> rw_cells segs mm A (cs1 ++ cs2).
Proof.
  clear. intros mm A cs1 cs2 [[W1 B1] (Wa & Wb & Wr)] [[W2 B2] (Va & Vb & Vr)]. split; [split|].
  - apply cells_wf_app. auto.
  - rewrite cells_bytes_app. apply bytes_at_app. rewrite (cells_bytes_length _ W1). auto.
  - rewrite cells_size_app. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z_lt_le_dec i (Z.of_nat (cells_size cs1))); [apply Wr; lia|].
    replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia. apply Vr. lia.
Qed.
Lemma rh_join_at : forall mm A A2 cs1 cs2,
  rw_cells segs mm A cs1 -> rw_cells segs mm A2 cs2 -> A2 = A + Z.of_nat (cells_size cs1) -> rw_cells segs mm A (cs1 ++ cs2).
Proof. clear. intros mm A A2 cs1 cs2 H1 H2 ->. apply rh_join; assumption. Qed.

Lemma u64arr_cell : forall mm A ws i w, u64arr segs mm A ws -> nth_error ws i = Some w -> rw_cells segs mm (A + 8 * Z.of_nat i) [C8 w].
Proof.
  clear. intros mm A ws i w [Hb Hw] Hn. pose proof (nth_error_split ws i w Hn) as (l1 & l2 & -> & L1).
  rewrite u64s_app in Hb. apply bytes_at_app in Hb. destruct Hb as [_ Hb]. cbn [u64s] in Hb.
  apply bytes_at_app in Hb. destruct Hb as [Hb _].
  rewrite u64s_length, L1 in Hb. replace (Z.of_nat (8 * i)) with (8 * Z.of_nat i) in Hb by lia.
  split; [split; [cbn; auto| cbn [cells_bytes cbytes]; rewrite app_nil_r; exact Hb]|].
  cbn [cells_size csize]. eapply wr_at_sub; [exact Hw| lia|]. rewrite length_app, <- L1. cbn [length]. lia.
Qed.
Lemma u64arr_of_cells : forall mm A ws, wr_at segs mm A (8 * Z.of_nat (length ws)) ->
  (forall i w, nth_error ws i = Some w -> rw_cells segs mm (A + 8 * Z.of_nat i) [C8 w]) -> u64arr segs mm A ws.
Proof.
  clear. intros mm A ws W H. split; [| exact W]. destruct W as (W0 & W1 & _).
  assert (G : forall k l, (forall i w, nth_error l i = Some w -> rw_cells segs mm (A + 8 * Z.of_nat (k + i)) [C8 w]) ->
              A + 8 * Z.of_nat (k + length l) <= 2^64 -> bytes_at segs mm (A + 8 * Z.of_nat k) (u64s l)).
  { intros k l. revert k. induction l as [|w l IH]; intros k Hc Hb.
    - cbn [u64s]. split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. cbn in Hi. lia.
    - cbn [u64s]. apply bytes_at_app. split.
      + pose proof (Hc 0%nat w eq_refl) as X. destruct X as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r, Nat.add_0_r in B. exact B.
      + rewrite length_le8. replace (A + 8 * Z.of_nat k + Z.of_nat 8) with (A + 8 * Z.of_nat (S k)) by lia.
        apply IH; [| cbn [length] in Hb; lia]. intros i w' Hi. replace (S k + i)%nat with (k + S i)%nat by lia. apply Hc. exact Hi. }
  pose proof (G 0%nat ws ltac:(intros i w Hi; apply H; exact Hi) ltac:(lia)) as X. rewrite Z.mul_0_r, Z.add_0_r in X. exact X.
Qed.
Lemma nth_error_ziota : forall k a i, (i < k)%nat -> nth_error (ziota a k) i = Some (a + Z.of_nat i).
Proof. clear. induction k as [|k IH]; intros a i Hi; [lia|]. destruct i as [|i]; cbn; [f_equal; lia|]. rewrite IH by lia. f_equal. lia. Qed.
(* [comment removed for export] *)
Lemma CB_byte : forall mm A k (v : byte) i, rw_cells segs mm A [CB k (repeat v k)] -> 0 <= i < Z.of_nat k -> rw_cells segs mm (A + i) [C1 v].
Proof.
  clear. intros mm A k v i [[_ B] W] Hi. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. cbn [cells_size csize] in W. rewrite Nat.add_0_r in W.
  destruct B as (B0 & B1 & BR). rewrite repeat_length in B1.
  split; [split; [cbn; auto|]|].
  - cbn [cells_bytes cbytes]. split; [lia|]. split; [cbn [length app]; lia|]. intros j Hj. cbn [length app] in Hj.
    replace (A + i + Z.of_nat j) with (A + Z.of_nat (Z.to_nat i)) by lia. rewrite (BR (Z.to_nat i)) by (rewrite repeat_length; lia).
    rewrite nth_error_repeat by lia. destruct j; [reflexivity| lia].
  - cbn [cells_size csize]. eapply wr_at_sub; [exact W| lia| lia].
Qed.

(* [comment removed for export] *)
Lemma chunk_cells_in_block : forall cb cm, as_chunks s !! cb = Some cm ->
  blk_lo cm + 16 <= cm_user_beg cm /\ cm_user_beg cm + 8 <= blk_hi s cm /\ cm_chunk_beg cm = cm_user_beg cm - 16.
Proof.
  intros cb0 cm Hcm. pose proof WF as X. destruct X as (WE & WR & WC & [K1 _] & _).
  destruct (K1 _ _ Hcm) as (A & B & C & D0 & _).
  unfold blk_lo, blk_hi, cm_chunk_beg, cm_user_beg, kChunkHeaderSize in *. rewrite C in *.
  change (16 * 2 ^ rz_log (cm_n cm)) with (rz_size (cm_n cm)) in *.
  pose proof (rz_size_pos (cm_n cm)) as RP.
  split; [lia|]. split; [| reflexivity].
  destruct (cm_prim cm) as [c0|].
  - destruct D0 as (D1 & D2 & _). pose proof (proj1 (from_primary_iff (cm_n cm) ltac:(lia)) D1) as LE.
    pose proof (rz_lt_class (cm_n cm) ltac:(lia)) as RZC. rewrite <- D2 in RZC. lia.
  - destruct D0 as (D1 & _). pose proof (map_size_facts (cm_n cm)) as (_ & MG & _). pose proof (needed_ge (cm_n cm)).
    assert (64512 < cm_n cm) by (destruct (Z.le_gt_cases (cm_n cm) 64512) as [LE|GT]; [| exact GT]; pose proof (proj2 (from_primary_iff (cm_n cm) ltac:(lia)) LE); congruence).
    unfold kPageSize in *. lia.
Qed.

(* [comment removed for export] *)
Lemma FRESH : as_chunks s !! cb = None.
Proof. pose proof HOK as (_ & _ & _ & _ & _ & _ & _ & _ & X). exact X. Qed.
Lemma Ecb : hcb E n s = cb. Proof. reflexivity. Qed.
Lemma NEWC : as_chunks s' !! cb = Some (hcm E key n s).
Proof. rewrite hit_chunks. fold ab. apply lookup_insert_eq. Qed.
Lemma OLDC : forall k cm, k <> cb -> as_chunks s !! k = Some cm <-> as_chunks s' !! k = Some cm.
Proof. intros k cm Hk. rewrite hit_chunks. rewrite lookup_insert_ne; [tauto| exact (fun H => Hk (eq_sym H))]. Qed.
Lemma OLD_blk : forall k cm, as_chunks s !! k = Some cm ->
  blk_hi s cm <= ab \/ ab + class_size c <= blk_lo cm.
Proof.
  intros k cm Hk. assert (NE : k <> cb) by (intros ->; rewrite FRESH in Hk; discriminate).
  pose proof (proj1 (OLDC k cm NE) Hk) as Hk'.
  destruct (chunks_disjoint E [] [] s' k cm cb (hcm E key n s) WF' Hk' NEWC NE) as [X|X]; unfold blk_hi, blk_lo in *; cbn [hcm cm_prim cm_alloc_beg] in X.
  - left. destruct (cm_prim cm); exact X.
  - right. exact X.
Qed.
(* [comment removed for export] *)
Lemma AGR_chunk : forall k cm A kk, as_chunks s !! k = Some cm -> blk_lo cm <= A -> A + kk <= blk_hi s cm -> agree_on m m' A kk.
Proof.
  intros k cm A kk Hk HA HB.
  pose proof GEO as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _). pose proof (OLD_blk k cm Hk) as OB.
  destruct NAVin as (blk & Hb & NV1 & NV2). pose proof (NBfacts blk Hb) as (_ & _ & NBR & _ & _ & NBS). pose proof (SBfacts sb SBin) as (_ & _ & SBR & _ & _ & SBS & _).
  pose proof (chunk_block_committed E [] [] s k cm WF Hk) as CBm. pose proof WF as (_ & [_ WR] & _ & _ & _ & (_ & _ & WS3 & _) & _).
  unfold blk_lo, blk_hi in *. pose proof RZ as (_ & _ & R3 & _). pose proof CS32. pose proof HCc.
  destruct (cm_prim cm) as [c0|].
  - destruct CBm as (Hc0 & L1 & L2). destruct (WR c0 Hc0) as (Q1 & Q2 & Q3 & _). unfold region_of, region_beg in *.
    pose proof (class_size_mod c0 ltac:(unfold kLargestClassID in Hc0; lia)) as [_ SZ0]. unfold kLargestClassID in Hc0.
    apply AGR_high; unfold ub; consts.
    + clear -G1 G2 L1 HA Hc0 SZ0. nia. + clear -G3 G4 L2 Q3 HB Hc0. nia. + clear -G7 G2 G3 L1 L2 Q3 HA HB Hc0. nia.
    + clear -OB HA HB R3. lia. + clear -NBR NV1 NV2 G2 G3 L1 L2 Q3 HA HB Hc0. nia. + clear -SBR G2 G3 L1 L2 Q3 HA HB Hc0. nia.
  - destruct CBm as (sc & Hsc & L1 & L2). destruct (WS3 sc Hsc) as (S1 & S2 & S3 & S4 & S5 & S6 & S7). pose proof (S7 _ G8) as S8. cbn [fst snd] in S8.
    pose proof (NBS sc Hsc) as S9. pose proof (SBS sc Hsc) as S10. unfold kPageSize in *.
    pose proof (APP_APPR _ _ S2 (img_sep_of_reserved _ _ S7)) as S2'.
    apply AGR_high; unfold ub; consts.
    + clear -S2' L1 L2 HA HB. lia. + clear -S3 L2 HB. lia. + clear -S8 L1 L2 HA HB. lia. + clear -OB HA HB R3. lia.
    + clear -S9 NV1 NV2 L1 L2 HA HB. lia. + clear -S10 L1 L2 HA HB. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Variable hb1 : Z.
Hypothesis NC_row : rw_cells segs m' (T + kThrCache + kPerClassSize * c) [C4 (zw (zlen (get_cache s c) - 1))].
Hypothesis NC_cst : rw_cells segs m' (T + kThrCacheStats + 16) [C8 (zw (as_cache_allocated s + class_size c))].
Hypothesis NC_st : rw_cells segs m' (T + kThrStats)
  [C8 (zw (ts_mallocs (as_ts s) + 1)); C8 (zw (ts_malloced (as_ts s) + n)); C8 (zw (ts_malloced_redzones (as_ts s) + (needed1 n - n)))].
Hypothesis NC_by : rw_cells segs m' (T + kThrStats + 112 + 8 * c) [C8 (zw (match ts_by_size (as_ts s) !! c with Some v => v | None => 0 end + 1))].
Hypothesis NC_unw : rw_cells segs m' (T + kThrUnwinding) [C1 (zb 0)].
Hypothesis NC_hdr : rw_cells segs m' cb [C1 (zb 2); C1 (zb hb1); C2 (zw 0); C4 (zw n); C8 (zw id)].
Hypothesis NC_b1 : Z.land hb1 127 = 0x11.
Hypothesis NC_mag : rz = 16 \/ rw_cells segs m' ab [C8 (zw kAllocBegMagicVal); C8 (zw cb)].
Hypothesis NC_sh0 : rw_cells segs m' (kShadowBase + ab / 8 + rz / 8) [CB (Z.to_nat (n / 8)) (repeat (zb 0) (Z.to_nat (n / 8)))].
Hypothesis NC_shp : 8 * (n / 8) < n -> rw_cells segs m' (kShadowBase + ab / 8 + rz / 8 + n / 8) [C1 (zb (n - 8 * (n / 8)))].
Hypothesis NC_dep :
  match depot_lookup E s key with
  | Some _ =>
       rw_cells segs m' (TD + 4 * bk) [C4 (zw (bucket_head HS bk))]
    /\ rw_cells segs m' (TD + 0x400000) [C4 (zw N)]
    /\ rw_cells segs m' SS [C8 (zw fr)]
    /\ rw_cells segs m' (SS + 16 + 16 * b) [C8 (zw sb); C4 (zw (stored_of fr b))]
    /\ (exists mx : word, rw_cells segs m' (SS + 28 + 16 * b) [C4 mx])
    /\ (exists bs, u8arr segs m' sb bs /\ Z.of_nat (length bs) = kStoreBlockBytes)
  | None =>
       rw_cells segs m' (TD + 4 * bk) [C4 (zw (N + 1))]
    /\ rw_cells segs m' (TD + 0x400000) [C4 (zw (N + 1))]
    /\ (exists sid : word, rw_cells segs m' NAv [C8 (zw h); C4 (zw (bucket_head HS bk)); C4 sid])
    /\ rw_cells segs m' SS [C8 (zw (fr + (len + 1)))]
    /\ rw_cells segs m' (SS + 16 + 16 * b) [C8 (zw sb); C4 (zw (stored_of fr b + (len + 1)))]
    /\ (exists mx : word, rw_cells segs m' (SS + 28 + 16 * b) [C4 mx])
    /\ (exists bs, u8arr segs m' sb bs /\ Z.of_nat (length bs) = kStoreBlockBytes)
  end.
(* [comment removed for export] *)
Hypothesis NC_mu : rw_cells segs m' (TD + 0x400008) [C4 (zw 0)].
Hypothesis NC_mtx : forall k, 0 <= k < kStoreBlockCount -> rw_cells segs m' (SS + 28 + 16 * k) [C4 (zw 0)].
Hypothesis DI' : depot_inv E s'.
(* [comment removed for export] *)
Hypothesis WRB : forall mm a nn, wr_at segs mm a nn -> 0 <= nn -> exists bs, length bs = Z.to_nat nn /\ bytes_at segs mm a bs.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma Hl : get_cache s c <> []. Proof. exact (proj1 (proj2 HOK)). Qed.
Lemma removelast_facts : forall (l0 : list Z), l0 <> [] ->
  l0 = removelast l0 ++ [List.last l0 0] /\ length (removelast l0) = Nat.pred (length l0).
Proof.
  clear. intros l0 H. split; [rewrite removelast_eq; apply app_removelast_last; exact H|].
  unfold removelast. rewrite length_firstn. lia.
Qed.

(* [comment removed for export] *)
Ltac thr_prep :=
  apply AGR_thr; unfold kThrUnwinding, kThrCache, kThrCacheStats, kThrStats, kPerClassSize, kThrStackTop, kThrQCache, kNumClasses in *;
  cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul].
Ltac thr_ag :=
  let HC := fresh in let CS := fresh in pose proof HCc as HC; pose proof CS32 as CS; thr_prep; clear -HC CS; try lia.
Tactic Notation "thr_agk" ne_hyp_list(l) :=
  let HC := fresh in let CS := fresh in pose proof HCc as HC; pose proof CS32 as CS; thr_prep; clear - HC CS l; try lia.

Lemma repD : arep_thread segs E s' m'.
Proof.
  pose proof REP as (_ & _ & _ & RD & _). destruct RD as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8).
  pose proof HCc as HC. pose proof CS32 as CS. pose proof Hn as HN.
  unfold arep_thread. rewrite hit_tq, hit_cache_allocated, hit_cache_mapped, (hit_tstats E key n s Hn). fold c.
  assert (TQB : tq_bytes s' = tq_bytes s) by (unfold tq_bytes; rewrite hit_tq; reflexivity). rewrite TQB.
  split; [eapply rw_cells_agree'; [| exact D1]; thr_ag|].
  split; [eapply rw_cells_agree'; [| exact D2]; thr_ag|].
  split; [eapply rw_cells_agree'; [| exact D3]; thr_ag|].
  split.
  { (* [comment removed for export] *)
    intros c' Hc'. destruct (D4 c' Hc') as (X1 & junk & X2 & L). rewrite (hit_get_cache E key n s c').
    unfold percls_cells. rewrite (hit_get_cache E key n s c'), hit_cache_inited. fold c. unfold kNumClasses in Hc'.
    destruct (decide (c' = c)) as [->|NE].
    - destruct (removelast_facts (get_cache s c) Hl) as [EL LL]. rewrite CI.
      split.
      + (* [comment removed for export] *)
        unfold percls_cells in X1. rewrite CI in X1. apply rh_split with (cs1 := [C4 (zw (zlen (get_cache s c)))]) in X1. destruct X1 as [_ X1].
        apply (rh_join_at m' _ (T + kThrCache + kPerClassSize * c + 4) [C4 (zw (zlen (removelast (get_cache s c))))]).
        * replace (zlen (removelast (get_cache s c))) with (zlen (get_cache s c) - 1); [exact NC_row|]. unfold zlen. rewrite LL.
          destruct (get_cache s c) eqn:GC; [exfalso; exact (Hl GC)| cbn [length Nat.pred]; lia].
        * eapply rw_cells_agree'; [| exact X1]. thr_ag.
        * cbn. lia.
      + exists (zw (List.last (get_cache s c) 0) :: junk). split.
        * replace (map zw (removelast (get_cache s c)) ++ zw (List.last (get_cache s c) 0) :: junk) with (map zw (get_cache s c) ++ junk).
          2:{ rewrite EL at 1. rewrite map_app. cbn [map]. rewrite <- app_assoc. reflexivity. }
          eapply u32arr_agree; [| exact X2]. rewrite length_app, length_map. thr_agk L.
        * cbn [length]. rewrite LL. destruct (get_cache s c) eqn:GC; [exfalso; exact (Hl GC)| cbn [length Nat.pred] in *; lia].
    - split.
      + eapply rw_cells_agree'; [| exact X1]. unfold percls_cells. thr_agk Hc' NE.
      + exists junk. split; [| exact L]. eapply u32arr_agree; [| exact X2]. rewrite length_app, length_map. thr_agk L Hc' NE. }
  split.
  { apply rh_split with (cs1 := [C8 (zw (as_cache_allocated s))]) in D5. destruct D5 as [_ D5].
    apply (rh_join_at m' _ (T + kThrCacheStats + 16 + 8) [C8 (zw (as_cache_allocated s + class_size c))]); [exact NC_cst| | cbn; lia].
    eapply rw_cells_agree'; [| exact D5]. thr_ag. }
  split.
  { (* [comment removed for export] *)
    apply u64arr_of_cells.
    - eapply wr_at_transport; [| exact WM]. destruct D6 as [_ W6]. exact W6.
    - intros i w Hi. apply rh_split with (cs1 := [C8 (zw (ts_mallocs (as_ts s) + 1))]) in NC_st as X. destruct X as [Y0 X].
      apply rh_split with (cs1 := [C8 (zw (ts_malloced (as_ts s) + n))]) in X. destruct X as [Y1 Y2]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Y1, Y2.
      destruct i as [|[|[|i]]].
      + cbn in Hi. injection Hi as <-. rewrite Z.mul_0_r, Z.add_0_r. exact Y0.
      + cbn in Hi. injection Hi as <-. exact Y1.
      + cbn in Hi. injection Hi as <-. replace (T + kThrStats + 8 * Z.of_nat 2) with (T + kThrStats + 8 + 8) by lia. exact Y2.
      + assert (OLD : nth_error (tstats_words (as_ts s)) (S (S (S i))) = Some w) by exact Hi.
        eapply rw_cells_agree'; [| exact (u64arr_cell m _ _ _ _ D6 OLD)]. pose proof (nth_error_lt _ _ _ OLD) as IL.
        unfold tstats_words in IL. rewrite length_map in IL. cbn [length] in IL. thr_agk IL. }
  split.
  { (* [comment removed for export] *)
    apply u64arr_of_cells.
    - eapply wr_at_transport; [| exact WM]. destruct D7 as [_ W7]. rewrite length_map in *. exact W7.
    - intros i w Hi. rewrite nth_error_map in Hi.
      assert (IL : (i < 32)%nat) by (destruct (Nat.lt_ge_cases i 32) as [L|L]; [exact L|]; rewrite (proj2 (nth_error_None _ _)) in Hi; [discriminate|]; rewrite ziota_length || idtac; cbn; lia).
      rewrite nth_error_ziota in Hi by exact IL. cbn [option_map] in Hi. injection Hi as <-. rewrite Z.add_0_l.
      destruct (decide (Z.of_nat i = c)) as [EQ|NE].
      + rewrite EQ. rewrite lookup_insert_eq. replace (match ts_by_size (as_ts s) !! c with Some k => k + 1 | None => 1 end) with (match ts_by_size (as_ts s) !! c with Some v => v | None => 0 end + 1) by (destruct (ts_by_size (as_ts s) !! c); lia). exact NC_by.
      + rewrite lookup_insert_ne by congruence.
        pose proof (u64arr_cell m _ _ i _ D7 ltac:(rewrite nth_error_map, nth_error_ziota by exact IL; reflexivity)) as X. rewrite Z.add_0_l in X.
        eapply rw_cells_agree'; [| exact X]. thr_agk IL NE. }
  exact NC_unw.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma repF : arep_chunks segs s' m'.
Proof.
  pose proof REP as (_ & _ & _ & _ & _ & RF & _). pose proof RZ as (R1 & R2 & R3 & R4). pose proof Hn as HN.
  intros k cm Hk. destruct (decide (k = cb)) as [->|NE].
  - rewrite NEWC in Hk. injection Hk as <-.
    assert (UB : cm_user_beg (hcm E key n s) = ub) by (unfold cm_user_beg, ub, ab, rz; cbn [hcm cm_alloc_beg cm_rz_log]; unfold rz in R4; rewrite <- R4; reflexivity).
    assert (CBE : cm_chunk_beg (hcm E key n s) = cb) by (unfold cm_chunk_beg, cb, kChunkHeaderSize; rewrite UB; reflexivity).
    split; [symmetry; exact CBE|]. unfold arep_chunk. rewrite CBE, UB. cbn [hcm cm_state cm_n cm_rz_log cm_alloc_beg hdr_state hdr_alloc_id].
    pose proof (small_primary n HN) as (_ & _ & P3 & _). rewrite P3.
    split; [| split; [| exact I]].
    + exists hb1. split; [exact NC_b1|]. unfold kChunkAllocated. rewrite Z.div_small by (clear -HN; lia). fold id. exact NC_hdr.
    + intros H16. fold ab. destruct NC_mag as [E16|X]; [| exact X]. exfalso. unfold rz in E16, R4. rewrite R4 in E16. clear -H16 E16. lia.
  - pose proof (proj2 (OLDC k cm NE) Hk) as Hk0. destruct (RF k cm Hk0) as [E1 (HB & HM & HQ)]. split; [exact E1|].
    pose proof (chunk_cells_in_block k cm Hk0) as (G1 & G2 & G3).
    split; [| split].
    + destruct HB as (b1' & Hb1 & X). exists b1'. split; [exact Hb1|]. eapply rw_cells_agree'; [| exact X].
      cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]. eapply AGR_chunk; [exact Hk0| rewrite G3; clear -G1; lia| rewrite G3; clear -G2; lia].
    + intros H16. eapply rw_cells_agree'; [| exact (HM H16)].
      cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]. eapply AGR_chunk; [exact Hk0| unfold blk_lo; lia| clear -G1 G2; unfold blk_lo in *; lia].
    + destruct (cm_state cm) as [i0|i0 fid]; [exact I|]. eapply rw_cells_agree'; [| exact HQ].
      cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]. eapply AGR_chunk; [exact Hk0| clear -G1; lia| clear -G2; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma NB_nthz : forall r, 1 <= r < zlen NB -> nthz NB r = nthz (as_node_blocks s) (r - 1) /\ In (nthz NB r) (as_node_blocks s).
Proof.
  intros r Hr. unfold NB, node_blocks, nthz, zlen in *. cbn [length] in Hr |- *.
  replace ((0 <=? r) && (r <? Z.of_nat (S (length (as_node_blocks s))))) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
  replace ((0 <=? r - 1) && (r - 1 <? Z.of_nat (length (as_node_blocks s)))) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
  replace (Z.to_nat r) with (S (Z.to_nat (r - 1))) by lia. cbn [nth]. split; [reflexivity|]. apply nth_In. lia.
Qed.
Lemma NB_nthz0 : nthz NB 0 = ae_depot_nodes E.
Proof. unfold NB, node_blocks, nthz, zlen. cbn [length]. replace ((0 <=? 0) && (0 <? Z.of_nat (S (length (as_node_blocks s))))) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; lia). reflexivity. Qed.
Lemma NB_disj : forall p q, 0 <= p < zlen NB -> 0 <= q < zlen NB -> p <> q ->
  nthz NB p + kDepotNodeBlockBytes <= nthz NB q \/ nthz NB q + kDepotNodeBlockBytes <= nthz NB p.
Proof.
  intros p q Hp Hq NE. pose proof DN0 as (_ & _ & _ & _ & RD).
  assert (DYN0 : forall r, 1 <= r < zlen NB -> nthz NB r + kDepotNodeBlockBytes <= nthz NB 0 \/ nthz NB 0 + kDepotNodeBlockBytes <= nthz NB r).
  { intros r Hr. destruct (NB_nthz r Hr) as [_ IN]. rewrite NB_nthz0.
    destruct (ak_blocks_sep _ _ _ AK (nthz NB r) kDepotNodeBlockBytes (or_introl (conj IN eq_refl))) as (_ & _ & _ & _ & _ & B6).
    destruct (B6 _ RD) as [X|X]; cbn [fst snd] in X; [left| right]; exact X. }
  destruct (Z.eq_dec p 0) as [->|P0]; destruct (Z.eq_dec q 0) as [->|Q0]; [lia| |  |].
  - destruct (DYN0 q ltac:(lia)); [right| left]; assumption.
  - destruct (DYN0 p ltac:(lia)); [left| right]; assumption.
  - destruct (NB_nthz p ltac:(lia)) as [-> _]. destruct (NB_nthz q ltac:(lia)) as [-> _].
    unfold NB, node_blocks, zlen in Hp, Hq. cbn [length] in Hp, Hq. apply (proj1 KSEP); unfold zlen; lia.
Qed.
Lemma node_sep : forall i j, 1 <= i -> 1 <= j -> i / kDepotNodesPerBlock < zlen NB -> j / kDepotNodesPerBlock < zlen NB -> i <> j ->
  node_addr E s i + 16 <= node_addr E s j \/ node_addr E s j + 16 <= node_addr E s i.
Proof.
  intros i j Hi Hj Bi Bj NE. unfold node_addr. fold NB.
  pose proof (Z.div_pos i kDepotNodesPerBlock ltac:(lia) ltac:(unfold kDepotNodesPerBlock; lia)) as DP1.
  pose proof (Z.div_pos j kDepotNodesPerBlock ltac:(lia) ltac:(unfold kDepotNodesPerBlock; lia)) as DP2.
  pose proof (Z.mod_pos_bound i kDepotNodesPerBlock ltac:(unfold kDepotNodesPerBlock; lia)) as MP1.
  pose proof (Z.mod_pos_bound j kDepotNodesPerBlock ltac:(unfold kDepotNodesPerBlock; lia)) as MP2.
  destruct (Z.eq_dec (i / kDepotNodesPerBlock) (j / kDepotNodesPerBlock)) as [EQ|NEQ].
  - rewrite EQ. assert (MNE : i mod kDepotNodesPerBlock <> j mod kDepotNodesPerBlock).
    { intros EM. apply NE. rewrite (Z.div_mod i kDepotNodesPerBlock), (Z.div_mod j kDepotNodesPerBlock) by (unfold kDepotNodesPerBlock; lia). rewrite EQ, EM. reflexivity. }
    (* [comment removed for export] *)
    revert MNE MP1 MP2. clear. generalize (i mod kDepotNodesPerBlock) (j mod kDepotNodesPerBlock) (nthz NB (j / kDepotNodesPerBlock)). intros u v w MNE MP1 MP2. lia.
  - destruct (NB_disj (i / kDepotNodesPerBlock) (j / kDepotNodesPerBlock) ltac:(split; [assumption| exact Bi]) ltac:(split; [assumption| exact Bj]) NEQ); unfold kDepotNodeBlockBytes, kDepotNodesPerBlock in *; lia.
Qed.

Lemma repH : DepotR segs E s' m'.
Proof.
  split; [exact DI'|].
  pose proof REP as (_ & _ & _ & _ & _ & _ & _ & [_ RH] & _). destruct RH as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11).
  pose proof FPWfacts as FF. pose proof BKR as HBK. pose proof BLT as HBL. pose proof Hn as HN. pose proof HLEN as HL.
  pose proof HOK as (_ & _ & HNB & HNS & HK & HSB & HF & HID & _). fold fr in HNS, HSB, HF. fold len in HNS. fold b in HSB.
  assert (EN : zlen (depot_keys E s) = N) by reflexivity.
  assert (EHS : zlen HS = N) by (unfold HS, N, depot_hashes, zlen; rewrite length_map; reflexivity).
  assert (HB : fr = b * kStoreBlockFrames + fr mod kStoreBlockFrames /\ 0 <= fr mod kStoreBlockFrames < kStoreBlockFrames).
  { unfold b. split; [rewrite Z.mul_comm; apply Z.div_mod| apply Z.mod_pos_bound]; unfold kStoreBlockFrames; lia. }
  destruct HB as [FRE FRM].
  (* [comment removed for export] *)
  assert (PK : depot_keys E s' = match depot_lookup E s key with Some _ => depot_keys E s | None => depot_keys E s ++ [key] end) by apply hit_depot_keys.
  assert (PH : depot_hashes E s' = match depot_lookup E s key with Some _ => HS | None => HS ++ [h] end).
  { unfold depot_hashes at 1. rewrite PK. unfold HS, h. destruct (depot_lookup E s key); [reflexivity| rewrite map_app; reflexivity]. }
  assert (PF : as_frames s' = match depot_lookup E s key with Some _ => fr | None => fr + (len + 1) end) by apply hit_frames.
  pose proof (hit_node_blocks' E key n s) as PNB. pose proof (hit_store_blocks' E key n s) as PSB.
  assert (PNA : forall i, node_addr E s' i = node_addr E s i) by (intros i; unfold node_addr; rewrite PNB; reflexivity).
  unfold DepotRep. rewrite PH, PK, PF, PNB, PSB. lits.
  change (aic_theDepot asan_ic) with TD in *. change (aic_stackStore asan_ic) with SS in *.
  clear R10 R11. revert R1 R2 R3 R4 R5 R6 R7 R8 R9. lits. fold TD SS. intros.
  (* [comment removed for export] *)
  assert (OLDN : forall i, 1 <= i <= N -> agree_on m m' (node_addr E s i) 16).
  { intros i Hi. pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj1 REP)))))))) as X || idtac.
    assert (Bi : i / kDepotNodesPerBlock < zlen NB).
    { unfold NB. apply (Z.le_lt_trans _ ((N + 1) / kDepotNodesPerBlock)); [apply Z.div_le_mono; unfold kDepotNodesPerBlock; lia|].
      destruct NAVin as (blk & Hb & _). revert Hb. unfold NAv, N, node_addr. intros _.
      pose proof (node_addr_in_block E s (zlen (depot_keys E s) + 1) ltac:(unfold zlen; lia)) as Y.
      (* [comment removed for export] *)
      pose proof REP as (_ & _ & _ & _ & _ & _ & _ & [DI _] & _). destruct DI as (_ & _ & _ & _ & D5 & _).
      unfold node_blocks, zlen in *. cbn [length]. unfold depot_keys in *. rewrite length_app in *. unfold depot_n_ids in D5, HNB. unfold kDepotNodesPerBlock in *.
      apply Z.div_lt_upper_bound; [lia|].
      destruct (Z.eq_dec (Z.of_nat (length (ae_keys0 E) + length (as_keys s)) + 1) (65536 * (Z.of_nat (length (as_node_blocks s)) + 1))) as [EQ|NE2]; [| clear -D5 NE2; lia].
      exfalso. apply HNB. rewrite EQ, Z.mul_comm. apply Z_mod_mult. }
    destruct (node_addr_in_block E s i ltac:(lia) Bi) as (blk & Hblk & L1 & L2). fold NB in Hblk.
    pose proof (NBfacts blk Hblk) as (N1 & N2 & N3 & N4 & N5 & N6). pose proof (SBfacts sb SBin) as (_ & _ & _ & _ & _ & _ & S7). pose proof (S7 blk Hblk) as S8.
    pose proof GEO as (G1 & G2 & G3 & G4 & _). pose proof ABR as (A1 & A2 & A3 & _). pose proof HCc. pose proof CS32. pose proof RZ as (_ & _ & Q3 & _).
    assert (NS : node_addr E s i + 16 <= NAv \/ NAv + 16 <= node_addr E s i).
    { unfold NAv. change (nthz NB ((N + 1) / kDepotNodesPerBlock) + 16 * ((N + 1) mod kDepotNodesPerBlock)) with (node_addr E s (N + 1)).
      apply node_sep; [lia| lia| exact Bi| | lia].
      pose proof REP as (_ & _ & _ & _ & _ & _ & _ & [DI _] & _). destruct DI as (_ & _ & _ & _ & D5 & _).
      unfold NB, N, node_blocks, zlen in *. cbn [length]. unfold depot_keys in *. rewrite length_app in *. unfold depot_n_ids in D5, HNB. unfold kDepotNodesPerBlock in *.
      apply Z.div_lt_upper_bound; [lia|].
      destruct (Z.eq_dec (Z.of_nat (length (ae_keys0 E) + length (as_keys s)) + 1) (65536 * (Z.of_nat (length (as_node_blocks s)) + 1))) as [EQ|NE2]; [| clear -D5 NE2; lia].
      exfalso. apply HNB. rewrite EQ, Z.mul_comm. apply Z_mod_mult. }
    apply AGR_high; unfold ub; consts.
    - clear -N1 L1 L2. lia. - clear -N2 L2. lia. - clear -N4 L1 L2. lia. - clear -N3 L1 L2 G2 G3 A1 A2 A3 H H0 Q3. nia. - clear -NS. lia. - clear -S8 L1 L2. lia. }
  (* [comment removed for export] *)
  assert (A3 : forall k, 0 <= k < kNodesMap1 -> rw_cells segs m' (TD + 0x400010 + 8 * k) [C8 (zw (nthz NB k))]).
  { intros k Hk. eapply rw_cells_agree'; [| exact (R3 k Hk)]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add].
    unfold kNodesMap1 in Hk. apply AGR_img; consts; clear -Hk HBK HBL; lia. }
  assert (A5 : forall b0, In b0 NB -> wr_at segs m' b0 kDepotNodeBlockBytes) by (intros b0 Hb0; eapply wr_at_transport; [exact (R5 b0 Hb0)| exact WM]).
  assert (A7 : exists al, rw_cells segs m' (SS + 8) [C8 al]).
  { destruct R7 as [al X]. exists al. eapply rw_cells_agree'; [| exact X]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]. apply AGR_img; consts; clear -HBK HBL; lia. }
  assert (A9 : forall b0, In b0 (store_blocks E s) -> exists bs', u8arr segs m' b0 bs' /\ Z.of_nat (length bs') = kStoreBlockBytes).
  { intros b0 Hb0. destruct (R9 b0 Hb0) as (bs0 & [_ W] & L0). rewrite L0 in W.
    destruct (WRB m' b0 kStoreBlockBytes ltac:(eapply wr_at_transport; [exact W| exact WM]) ltac:(unfold kStoreBlockBytes; lia)) as (bs' & L' & B').
    exists bs'. split; [split; [exact B'|]|]; rewrite L', Z2Nat.id by (unfold kStoreBlockBytes; lia); [eapply wr_at_transport; [exact W| exact WM]| reflexivity]. }
  assert (STO : forall k, k <> b -> stored_of (fr + (len + 1)) k = stored_of fr k).
  { intros k Hk. unfold stored_of. unfold kStoreBlockFrames in *. clear -Hk FRE FRM HNS HL. destruct (Z_lt_le_dec k b); [nia| nia]. }
  assert (STB : stored_of fr b = fr mod kStoreBlockFrames /\ stored_of (fr + (len + 1)) b = fr mod kStoreBlockFrames + (len + 1)).
  { unfold stored_of. unfold kStoreBlockFrames in *. clear -FRE FRM HNS HL. lia. }
  assert (A8 : forall k, 0 <= k < 0x1000 -> k <> b ->
            rw_cells segs m' (SS + 16 + 16 * k) [C8 (zw (nthz (store_blocks E s) k)); C4 (zw (stored_of fr k))] /\ exists mx, rw_cells segs m' (SS + 28 + 16 * k) [C4 mx]).
  { intros k Hk NE. destruct (R8 k ltac:(unfold kStoreBlockCount; exact Hk)) as (X1 & mx & X2). split; [| exists mx].
    - eapply rw_cells_agree'; [| exact X1]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]. apply AGR_img; consts; clear -Hk NE HBK HBL; lia.
    - eapply rw_cells_agree'; [| exact X2]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]. apply AGR_img; consts; clear -Hk NE HBK HBL; lia. }
  assert (A4 : forall i, 1 <= i <= N -> exists sid, rw_cells segs m' (node_addr E s i) [C8 (zw (nth_hash HS i)); C4 (zw (node_link HS i)); C4 sid]).
  { intros i Hi. destruct (R4 i ltac:(rewrite EN; exact Hi)) as [sid X]. exists sid. eapply rw_cells_agree'; [| exact X]. exact (OLDN i Hi). }
  assert (A1 : forall b0, 0 <= b0 < kTabSize -> b0 <> bk -> rw_cells segs m' (TD + 4 * b0) [C4 (zw (bucket_head HS b0))]).
  { intros b0 Hb0 NE. eapply rw_cells_agree'; [| exact (R1 b0 Hb0)]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add].
    unfold kTabSize in Hb0. apply AGR_img; consts; clear -Hb0 NE HBK HBL; lia. }
  revert NC_dep. destruct (depot_lookup E s key) as [id0|] eqn:DL; intros NC.
  - (* [comment removed for export] *)
    destruct NC as (N1 & N2 & N3 & N4 & N5 & _).
    split; [intros b0 Hb0; destruct (Z.eq_dec b0 bk) as [->|NE]; [exact N1| exact (A1 b0 Hb0 NE)]|].
    split; [rewrite EN; exact N2|]. split; [exact A3|]. split; [rewrite EN; intros i Hi; rewrite PNA; exact (A4 i Hi)|]. split; [exact A5|]. split; [exact N3|]. split; [exact A7|].
    split; [| split; [exact A9| split; [exact NC_mu| exact NC_mtx]]]. intros k Hk. destruct (Z.eq_dec k b) as [->|NE]; [| exact (A8 k Hk NE)]. split; [| exact N5]. unfold sb in N4. exact N4.
  - (* [comment removed for export] *)
    destruct NC as (N1 & N2 & N3 & N4 & N5 & N6 & _).
    assert (EB : bucket_of h = bk) by reflexivity.
    split.
    { intros b0 Hb0. rewrite bucket_head_app1, EHS. destruct (Z.eq_dec b0 bk) as [->|NE].
      - rewrite EB, Z.eqb_refl. exact N1.
      - replace (bucket_of h =? b0) with false by (symmetry; apply Z.eqb_neq; rewrite EB; congruence). exact (A1 b0 Hb0 NE). }
    split; [unfold zlen in *; rewrite length_app; cbn [length]; rewrite Nat2Z.inj_add; cbn; rewrite EN; exact N2|].
    split; [exact A3|].
    split.
    { intros i Hi. unfold zlen in Hi; rewrite length_app in Hi; cbn [length] in Hi. rewrite Nat2Z.inj_add in Hi. change (zlen (depot_keys E s)) with N in Hi || idtac.
      assert (Hi' : 1 <= i <= N \/ i = N + 1) by (unfold N, zlen; lia). rewrite PNA.
      destruct Hi' as [Hold| ->].
      - rewrite nth_hash_app_old, node_link_app_old by (rewrite EHS; exact Hold). exact (A4 i Hold).
      - rewrite <- EHS. rewrite nth_hash_app_new, node_link_app_new, EB, ?EHS.
        destruct N3 as [sid X]. exists sid. unfold NAv in X. unfold node_addr. fold NB. exact X. }
    split; [exact A5|]. split; [exact N4|]. split; [exact A7|].
    split; [| split; [exact A9| split; [exact NC_mu| exact NC_mtx]]]. intros k Hk. destruct (Z.eq_dec k b) as [->|NE].
    + split; [| exact N6]. destruct STB as [S1 S2]. rewrite S2, <- S1. unfold sb in N5. exact N5.
    + rewrite (STO k NE). exact (A8 k Hk NE).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma Sh_some_range : forall x v, Sh E s x = Some v -> 0 <= x < kLowAppEnd \/ kHighMemBeg <= x <= kHighMemEnd.
Proof.
  intros x v H. unfold Sh in H. pose proof GEO as (G1 & G2 & G3 & G4 & _).
  destruct (in_some_region_map E s x) eqn:RM.
  - pose proof (region_map_in_space E [] [] s x WF RM) as X. unfold alloc_ceiling, kResvLen, kHighMemEnd in *. clear -X G1 G2 G3 G4. lia.
  - destruct (in_some_sec_map s x) eqn:SM.
    + unfold in_some_sec_map in SM. apply existsb_exists in SM as (sc & Hsc & Hb). apply andb_true_iff in Hb as [B1 B2]. apply Z.leb_le in B1. apply Z.ltb_lt in B2.
      pose proof WF as (_ & _ & _ & _ & _ & (_ & _ & WS3 & _) & _). destruct (WS3 sc Hsc) as (_ & S2 & S3 & _). unfold app_mem, alloc_ceiling, kHighMemEnd in *. clear -B1 B2 S2 S3. lia.
    + cbn [orb] in H. destruct (sh_default_dom E x && negb (sh_excluded E x)) eqn:C; [| discriminate].
      apply andb_true_iff in C as [C _]. unfold sh_default_dom in C. apply orb_true_iff in C as [C|C].
      * apply andb_true_iff in C as [C _]. apply andb_true_iff in C as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2. lia.
      * apply andb_true_iff in C as [C1 C2]. apply Z.leb_le in C1. apply Z.leb_le in C2. lia.
Qed.

(* [comment removed for export] *)
Lemma Sh_avail : forall x, ab <= x < ab + class_size c -> Sh E s x = Some kAsanHeapLeftRedzoneMagic.
Proof.
  intros x Hx. unfold Sh. pose proof ABR as (A1 & A2 & A3 & _). pose proof HCc as HC.
  assert (RM : in_some_region_map E s x = true).
  { unfold in_some_region_map. apply orb_true_iff. left. apply (existsb_In _ _ c); [apply In_ziota; lia|].
    apply andb_true_iff. unfold region_beg, region_of. split; [apply Z.leb_le| apply Z.ltb_lt]; clear -Hx A1 A2; lia. }
  rewrite RM. cbn [orb]. destruct (find_chunk s x) as [cm|] eqn:FC; [| reflexivity].
  exfalso. destruct (find_chunk_some s x cm FC) as (k & Hk & R). pose proof (OLD_blk k cm Hk) as OB. rewrite blk_hi_span in OB. unfold blk_lo in OB. clear -Hx R OB. lia.
Qed.

Lemma UBv : cm_user_beg (hcm E key n s) = ub.
Proof. pose proof RZ as (_ & _ & _ & R4). unfold cm_user_beg, ub, ab, rz. cbn [hcm cm_alloc_beg cm_rz_log]. unfold rz in R4. rewrite <- R4. reflexivity. Qed.

Lemma repJ : arep_shadow segs E s' m'.
Proof.
  pose proof REP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & RJ). pose proof RZ as (R1 & R2 & R3 & R4). pose proof Hn as HN. pose proof ABR as (A1 & A2 & A3 & A4). pose proof HCc as HC. pose proof CS32 as CS.
  pose proof (class_size_mod c ltac:(clear -HC; lia)) as [CM _].
  pose proof (small_primary n HN) as (_ & _ & P3 & _).
  intros g v Hg. rewrite (Sh_hit E [] [] key n s (8 * g) WF WF' HN FRESH) in Hg. fold ab c in Hg.
  assert (RGv : forall v', Sh E s (8 * g) = Some v' -> kShadowBase <= kShadowBase + g /\ kShadowBase + g + 1 <= kHighMemBeg).
  { intros v' H'. pose proof (Sh_some_range _ _ H') as X. rewrite kHighMemBeg_val, kLowAppEnd_val in *. unfold kHighMemEnd, kShadowBase in *. clear -X. lia. }
  destruct ((ab <=? 8 * g) && (8 * g <? ab + class_size c)) eqn:IN.
  - apply andb_true_iff in IN as [I1 I2]. apply Z.leb_le in I1. apply Z.ltb_lt in I2.
    pose proof (Sh_avail (8 * g) ltac:(clear -I1 I2; lia)) as OLD. pose proof (RGv _ OLD) as [K1 K2].
    injection Hg as Hv. unfold chunk_shadow in Hv. rewrite UBv in Hv. cbn [hcm cm_state cm_n] in Hv. rewrite P3 in Hv.
    destruct (8 * g <? ub) eqn:C1; [apply Z.ltb_lt in C1| apply Z.ltb_ge in C1].
    + (* [comment removed for export] *) subst v. eapply rw_cells_agree'; [| exact (RJ g _ OLD)]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
      apply AGR_shadow; [exact K1| exact K2|]. left. unfold ub, rz in *. clear -C1 A4 R1. Z.div_mod_to_equations. lia.
    + destruct (8 * g <? ub + n / 8 * 8) eqn:C2; [apply Z.ltb_lt in C2| apply Z.ltb_ge in C2].
      * (* [comment removed for export] *) subst v. replace (kShadowBase + g) with (kShadowBase + ab / 8 + rz / 8 + (g - ub / 8)) by (unfold ub, rz in *; clear -A4 R1; Z.div_mod_to_equations; lia).
        apply (CB_byte m' _ (Z.to_nat (n / 8)) (zb 0)); [exact NC_sh0|]. unfold ub, rz in *. clear -C1 C2 A4 R1 HN. Z.div_mod_to_equations. nia.
      * destruct (8 * g <? ub + n) eqn:C3; [apply Z.ltb_lt in C3| apply Z.ltb_ge in C3].
        -- (* [comment removed for export] *) subst v.
           assert (G : g = ub / 8 + n / 8 /\ 8 * (n / 8) < n) by (unfold ub, rz in *; clear -C2 C3 A4 R1 HN; Z.div_mod_to_equations; nia). destruct G as [G1 G2].
           replace (kShadowBase + g) with (kShadowBase + ab / 8 + rz / 8 + n / 8) by (rewrite G1; unfold ub, rz in *; clear -A4 R1; Z.div_mod_to_equations; lia).
           replace (n mod 8) with (n - 8 * (n / 8)) by (clear -HN; Z.div_mod_to_equations; lia). exact (NC_shp G2).
        -- (* [comment removed for export] *) subst v. eapply rw_cells_agree'; [| exact (RJ g _ OLD)]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
           apply AGR_shadow; [exact K1| exact K2|]. right. unfold ub, rz in *. clear -C3 A4 R1 HN. Z.div_mod_to_equations. lia.
  - (* [comment removed for export] *)
    pose proof (RGv _ Hg) as [K1 K2]. eapply rw_cells_agree'; [| exact (RJ g v Hg)]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
    apply AGR_shadow; [exact K1| exact K2|].
    assert (OUT : 8 * g < ab \/ ab + class_size c <= 8 * g).
    { destruct (Z_lt_le_dec (8 * g) ab) as [X|X]; [left; exact X| right]. destruct (Z_lt_le_dec (8 * g) (ab + class_size c)) as [Y|Y]; [| exact Y].
      exfalso. assert (C' : (ab <=? 8 * g) && (8 * g <? ab + class_size c) = true) by (apply andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia). rewrite C' in IN. discriminate. }
    unfold rz in *. rewrite CS in *. clear -OUT A4 R1 R3 HN CM. destruct OUT as [O|O]; [left| right]; Z.div_mod_to_equations; nia.
Qed.

(* [comment removed for export] *)
Theorem ARep_hit : ARep segs E (DepotR segs E) s' m'.
Proof.
  split; [exact repA|]. split; [exact repB|]. split; [exact repC|]. split; [exact repD|]. split; [exact repE|].
  split; [exact repF|]. split; [exact repG|]. split; [exact repH|]. split; [exact repI| exact repJ].
Qed.

End RH.
End RC__1.
