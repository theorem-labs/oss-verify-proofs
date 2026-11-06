(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages AImageFacts.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanOps AsanRep AsanKern.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanLayout AsanSlack.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BF_place B_slack5 B_mmchk5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac lia ::=
  first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | LiaTuning.zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SecRanges.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= force_section_ranges.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac aceil :=
  lazymatch goal with
  | H : _ <= alloc_ceiling <= _ |- _ => idtac
  | |- context [alloc_ceiling] => repeat match goal with H : True |- _ => clear H end; pose proof alloc_ceiling_range as CEILB
  | H : context [alloc_ceiling] |- _ => repeat match goal with H' : True |- _ => clear H' end; pose proof alloc_ceiling_range as CEILB
  | _ => first [ pose proof I as CEILB | idtac ]
  end.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma iv_disjoint_true : forall a n b m, a + n <= b \/ b + m <= a -> iv_disjoint a n b m = true.
Proof. aceil. intros a n b m H. unfold iv_disjoint. apply orb_true_intro. destruct H; [left| right]; apply Z.leb_le; lia. Qed.

Section G.
Variable E0 : aenv.
Variables L0 RES0 : list (word * word).

(* [comment removed for export] *)
Theorem grant_known_free : forall (Pq : list Z) (Dq : list batch) (mo : Model) (a : astate) (r : word) (L : Z),
  KVM L0 RES0 mo a -> AKern E0 a mo -> AWf E0 Pq Dq a ->
  region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) r (Z_to_bv 64 L) = true ->
  0 < bv_unsigned r -> bv_unsigned r + L <= alloc_ceiling -> 0 < L ->
  (forall rr, In rr (ae_reserved E0) -> bv_unsigned r + L <= fst rr \/ fst rr + snd rr <= bv_unsigned r) ->
     ranges_free (known_ranges E0 a) (bv_unsigned r) L = true
  /\ in_primary (ae_space_beg E0) (bv_unsigned r) = false
  /\ in_primary (ae_space_beg E0) (bv_unsigned r + L - 1) = false.
Proof. aceil.
  intros Pq Dq mo a r L (KR & (fog & PM & _) & MW & _) K WF RF RH RC LP RSV.
  set (rZ := bv_unsigned r) in *.
  pose proof kHighMemBeg_val as KHB. pose proof kLowAppEnd_val as KLE.
  pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. fold rZ in Rr.
  (* [comment removed for export] *)
  assert (DJ : forall e, In e (vm_maps (m_vmmaps mo)) -> ehi e <= rZ \/ rZ + L <= elo e).
  { intros [b0 sz] Hm. pose proof (State.region_free_In _ _ _ _ _ RF ltac:(apply in_app_iff; right; exact Hm)) as OV.
    unfold iv_overlap in OV. unfold elo, ehi in *. cbn [fst snd] in *. fold rZ in OV. pose proof (bv_unsigned_in_range 64 sz). pose proof (bv_unsigned_in_range 64 b0).
    rewrite (u64_small L) in OV by lia. apply Bool.andb_false_iff in OV. destruct OV as [OV|OV]; apply Z.ltb_ge in OV; lia. }
  assert (INP : forall e, In e (L0 ++ fog ++ amaps a) -> In e (vm_maps (m_vmmaps mo))).
  { intros e He. eapply Permutation_in; [apply Permutation_sym; exact PM| exact He]. }
  assert (EL : forall b0 len, 0 <= b0 -> 0 <= len -> b0 + len < 2^64 -> elo (went b0 len) = b0 /\ ehi (went b0 len) = b0 + len).
  { intros b0 len H1 H2 H3. unfold elo, ehi, went, kwz. cbn [fst snd]. rewrite !u64_small by lia. lia. }
  (* [comment removed for export] *)
  assert (DJW : forall b0 len, In (went b0 len) (vm_maps (m_vmmaps mo)) -> 0 <= b0 -> 0 <= len -> b0 + len < 2^64 -> rZ + L <= b0 \/ b0 + len <= rZ).
  { intros b0 len Hin H1 H2 H3. destruct (EL b0 len H1 H2 H3) as [E1 E2]. pose proof (DJ _ Hin) as X. rewrite E1, E2 in X. lia. }
  destruct WF as (WE & _ & _ & _ & _ & WS & _). destruct WS as (_ & _ & WS3 & _).
  split; [| split].
  - unfold ranges_free. apply forallb_forall. intros [b0 len] Hin. cbn [fst snd]. apply iv_disjoint_true.
    unfold known_ranges in Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; [| apply in_app_iff in Hin; destruct Hin as [Hin|Hin]; [| apply in_app_iff in Hin; destruct Hin as [Hin|Hin]]].
    + (* [comment removed for export] *)
      pose proof (RSV _ Hin) as X. cbn [fst snd] in X. fold rZ in X. clear -X. lia.
    + (* [comment removed for export] *)
      apply in_map_iff in Hin. destruct Hin as (sc & E & Hsc). injection E as <- <-.
      destruct (WS3 sc Hsc) as (M1 & M2 & M3 & M4 & _). unfold app_mem in M2. rewrite KHB, KLE in M2. aceil.
      apply (DJW (sc_map_beg sc) (sc_map_size sc)); [| clear -CEILB M2; lia| clear -CEILB M4; lia| clear -CEILB M2 M3 M4; lia]. apply INP. apply in_app_iff; right. apply in_app_iff; right.
      unfold amaps. apply in_app_iff; left. apply in_map_iff. exists sc. auto.
    + (* [comment removed for export] *)
      apply in_map_iff in Hin. destruct Hin as (nb & E & Hnb). injection E as <- <-.
      destruct (ak_blocks_sep _ _ _ K nb kDepotNodeBlockBytes (or_introl (conj Hnb eq_refl))) as (B1 & B2 & _).
      unfold app_mem in B1. rewrite KHB, KLE in B1. aceil. unfold kDepotNodeBlockBytes in *.
      apply (DJW nb (2^20)); [| lia| lia| lia]. apply INP. apply in_app_iff; right. apply in_app_iff; right.
      unfold amaps. apply in_app_iff; right. apply in_app_iff; left. apply in_map_iff. exists nb. auto.
    + (* [comment removed for export] *)
      apply in_map_iff in Hin. destruct Hin as (sb & E & Hsb). injection E as <- <-.
      destruct (ak_blocks_sep _ _ _ K sb kStoreBlockBytes (or_intror (conj Hsb eq_refl))) as (B1 & B2 & _).
      unfold app_mem in B1. rewrite KHB, KLE in B1. aceil. unfold kStoreBlockBytes in *.
      apply (DJW sb (2^23)); [| lia| lia| lia]. apply INP. apply in_app_iff; right. apply in_app_iff; right.
      unfold amaps. apply in_app_iff; right. apply in_app_iff; right. apply in_map_iff. exists sb. auto.
  - (* [comment removed for export] *)
    pose proof (ak_resv _ _ _ K) as IR. pose proof (ak_resv_geom _ _ _ K) as (G1 & G2 & G3).
    pose proof WE as (_ & E2 & _ & _ & E5 & _). rewrite KHB in E2. aceil.
    unfold kResvLen, kSpaceSize, kPageSize in *.
    pose proof (DJW (ae_resv_beg E0) 0x2000011000 IR ltac:(lia) ltac:(lia) ltac:(lia)) as X.
    unfold in_primary. apply Bool.andb_false_iff. unfold kSpaceSize. destruct X as [X|X]; [left; apply Z.leb_gt| right; apply Z.ltb_ge]; lia.
  - pose proof (ak_resv _ _ _ K) as IR. pose proof (ak_resv_geom _ _ _ K) as (G1 & G2 & G3).
    pose proof WE as (_ & E2 & _ & _ & E5 & _). rewrite KHB in E2. aceil.
    unfold kResvLen, kSpaceSize, kPageSize in *.
    pose proof (DJW (ae_resv_beg E0) 0x2000011000 IR ltac:(lia) ltac:(lia) ltac:(lia)) as X.
    unfold in_primary. apply Bool.andb_false_iff. unfold kSpaceSize. destruct X as [X|X]; [left; apply Z.leb_gt| right; apply Z.ltb_ge]; lia.
Qed.

(* [comment removed for export] *)
Corollary grant_validates : forall (Pq : list Z) (Dq : list batch) (mo : Model) (a : astate) (r : word) (L : Z),
  KVM L0 RES0 mo a -> AKern E0 a mo -> AWf E0 Pq Dq a ->
  region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) r (Z_to_bv 64 L) = true ->
  bv_unsigned r mod kPageSize = 0 -> placed (bv_unsigned r) L -> 0 < L ->
  (forall rr, In rr (ae_reserved E0) -> bv_unsigned r + L <= fst rr \/ fst rr + snd rr <= bv_unsigned r) ->
     (bv_unsigned r mod kPageSize =? 0) && (0 <? bv_unsigned r) && (bv_unsigned r + L <=? alloc_ceiling) && ranges_free (known_ranges E0 a) (bv_unsigned r) L = true
  /\ app_mem_b (bv_unsigned r) L && negb (in_primary (ae_space_beg E0) (bv_unsigned r)) && negb (in_primary (ae_space_beg E0) (bv_unsigned r + L - 1))
      && (bv_unsigned r + L <=? kHighMemEnd + 1) = true.
Proof. aceil.
  intros Pq Dq mo a r L KV K WF RF RA PL LP RSV. pose proof PL as (P1 & P2 & P3). unfold A_IMG_END, A_LOWAPP_END, A_HIGH_BEG in *. aceil.
  pose proof alloc_ceiling_le_high_end as CH.
  destruct (grant_known_free Pq Dq mo a r L KV K WF RF ltac:(clear -P1; lia) P2 LP RSV) as (G1 & G2 & G3).
  rewrite G1, G2, G3, RA. cbn [negb andb Z.eqb].
  split.
  - rewrite (proj2 (Z.ltb_lt _ _)) by (clear -P1; lia). rewrite (proj2 (Z.leb_le _ _)) by exact P2. reflexivity.
  - rewrite (proj2 (app_mem_b_iff _ _)) by (unfold app_mem; rewrite kLowAppEnd_val, kHighMemBeg_val; clear -CEILB P1 P2 P3; lia).
    rewrite (proj2 (Z.leb_le _ _)) by (clear -CEILB P2 CH; lia). reflexivity.
Qed.
End G.
End RC__1.
