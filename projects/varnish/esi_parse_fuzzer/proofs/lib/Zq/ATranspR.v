(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ATransp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import AInvWfp.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.  (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Notation wz z := (Z_to_bv 64 z) (only parsing).
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kSpaceReserve, kMaxSize in *.


(* [comment removed for export] *)
(* [comment removed for export] *)
Section WFTdef.
Context {Clg : Ceiling}.
  (* [comment removed for export] *)
  Definition wf_batch0T_ (reg : Z -> region) (sec : secreg) (b : batch) : Prop :=
    Z.of_nat (length (ba_entries b)) <= kQuarantineBatchCount /\
    0 <= ba_idx b < carved_count_ reg kQuarantineBatchClass /\
    Forall (wf_qentry_ reg sec) (ba_entries b).
  Record WFT (A : AState) : Prop := {
    wtP : wf_place AL_pboth (a_pl A);
    wtM : wf_bigmaps_ (a_pl A) (a_sec A);
    wtR : wf_regions_ (a_reg A) (a_paid A) (a_cache_inited A);   (* [comment removed for export] *)
    wtC : wf_caches_ (a_reg A) (a_cache A) (a_cache_inited A);
    wtX : wf_partition_ (a_reg A) (a_cache A) (a_livemap A) (a_qthread A) (a_qglobal A ++ a_qlimbo A);
    wtV : wf_live_ (a_sb A) (a_reg A) (a_livemap A) (a_sec A);
    wtQ : Forall (wf_batch0T_ (a_reg A) (a_sec A)) (a_qthread A) /\ Forall (wf_batch0T_ (a_reg A) (a_sec A)) (a_qglobal A ++ a_qlimbo A) /\ True /\ True /\ True /\
          NoDup (batch_indices_ (a_qthread A) (a_qglobal A ++ a_qlimbo A)) /\ NoDup (quarantined_chunks_ (a_qthread A) (a_qglobal A ++ a_qlimbo A)) /\
          (forall u li, a_livemap A !! u = Some li -> ~ In (li_chunk li) (quarantined_chunks_ (a_qthread A) (a_qglobal A ++ a_qlimbo A)));
    wtS : wf_sec_ AL_pboth (a_livemap A) (a_qthread A) (a_qglobal A ++ a_qlimbo A) (a_sec A);
    wtD : wf_depot_ (p_dkeys (a_pl A)) (a_depot A);
    wtF : wf_fstack_ (a_fs A) (a_fhint A) (a_fframes A);
    wtB : wf_budget_ (a_tiny A) (a_livemap A) (a_qthread A) (a_qglobal A ++ a_qlimbo A) }.

  Lemma WFT_of_WF : forall A, WF AL_pboth A -> WFT A.
  Proof.
    intros A W. destruct W as [wP wM wR wC wX wV wQ wS wD wF wB wI wE wJ].
    (first [ dand8 wQ as Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 | destruct wQ as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8) ]).
    assert (B0 : forall l, Forall (wf_batch_ (a_reg A) (a_sec A)) l -> Forall (wf_batch0T_ (a_reg A) (a_sec A)) l).
    { intros l F. eapply Forall_impl; [| exact F]. (intros b; (first [ intro dR_161; dand3 dR_161 as H1 H2 H3 | intros (H1 & H2 & H3) ])). split; [lia|]. split; [exact H2| exact H3]. }
    constructor; rewrite ?wI, ?app_nil_r; try assumption. split; [apply B0; exact Q1|]. split; [apply B0; exact Q2|]. repeat (split; [exact I|]). exact (conj Q6 (conj Q7 Q8)).
  Qed.
End WFTdef.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Twins.
Context {Clg : Ceiling}.
Lemma sb_factsT : forall A, WFT A ->
  a_sb A = space_beg_of (a_b6 A) /\ a_sb A mod 0x10000 = 0 /\ kHighMemBeg <= a_b6 A /\ a_b6 A < a_sb A <= a_b6 A + 0x10000 /\
  a_sb A + kSpaceSize + 4096 <= alloc_ceiling.
Proof.
  intros A W. (first [ pose proof ((wtP A W)) as dR_2; dand5 dR_2 as Hb6 Hhi Hsb Hce _ | destruct (wtP A W) as (Hb6 & Hhi & Hsb & Hce & _) ]).
  pose proof (space_beg_aligned (a_b6 A) Hb6). pose proof (space_beg_range (a_b6 A) Hb6).
  unfold a_sb, a_b6, p_sb in *. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia.
Qed.

Lemma region_piece_boundsT : forall A c, WFT A -> 1 <= c <= 30 ->
  let R := a_reg A c in let rb := region_beg (a_sb A) c in
  kHighMemBeg <= rb /\ a_sb A <= rb /\ 0 <= rg_allocated_user R <= rg_mapped_user R /\ rb + rg_mapped_user R <= rb + kFreeArrayOffset /\
  0 <= rg_mapped_fa R /\ rb + kFreeArrayOffset + rg_mapped_fa R <= rb + kRegionSize /\
  rb + kRegionSize <= a_sb A + kSpaceSize /\ a_sb A + kSpaceSize + 4096 <= alloc_ceiling /\ rb mod 0x10000 = 0 /\
  rg_mapped_user R mod 8 = 0 /\ rg_allocated_user R mod 8 = 0 /\ rg_mapped_fa R mod 8 = 0.
Proof.
  intros A c W Hc. (first [ pose proof ((sb_factsT A W)) as dR_3; dand5 dR_3 as E AL HB RG CE | pose proof (sb_factsT A W) as (E & AL & HB & RG & CE) ]). set (sb := a_sb A) in *.
  (first [ pose proof ((wtR A W)) as dR_4; dand3 dR_4 as WR _ _ | destruct (wtR A W) as (WR & _ & _) ]). specialize (WR c Hc). (first [ dand8 WR as A1 A2 A3 A4 A5 A6 A7 _ | destruct WR as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _) ]).
  pose proof (class_size_mod32 c Hc) as CM. pose proof (class_size_range c Hc) as CR.
  cbv zeta. unfold region_beg, kRegionSize, kSpaceSize, kFreeArrayOffset, kFreeArraySize, kHighMemBeg, kUserMapSize, kFreeArrayMapSize in *.
  assert (M1 : (sb + c * 2 ^ 32) mod 0x10000 = 0) by
    (rewrite Z.add_mod, AL by lia; replace (c * 2^32) with ((c * 2^16) * 0x10000) by lia; rewrite Z_mod_mult; reflexivity).
  assert (M2 : rg_mapped_user (a_reg A c) mod 8 = 0) by (apply (mod0_down _ (2^18) 8); [exists (2^15); reflexivity| exact A3]).
  assert (M3 : rg_allocated_user (a_reg A c) mod 8 = 0).
  { apply (mod0_down _ (class_size c) 8); [|exact A4]. apply (Z.divide_trans _ 32); [exists 4; reflexivity|]. apply Z.mod_divide; [lia| exact CM]. }
  assert (M4 : rg_mapped_fa (a_reg A c) mod 8 = 0) by (apply (mod0_down _ (2^18) 8); [exists (2^15); reflexivity| exact A6]).
  OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia; try nia; assumption.
Qed.

Lemma carved_chunk_boundsT : forall A c k, WFT A -> 1 <= c <= 30 -> 0 <= k < carved_count A c ->
  let rb := region_beg (a_sb A) c in
  rb <= chunk_addr (a_sb A) c k /\ chunk_addr (a_sb A) c k + class_size c <= rb + rg_allocated_user (a_reg A c) /\
  chunk_addr (a_sb A) c k mod 32 = 0 /\ 32 <= class_size c <= kMaxSize.
Proof.
  intros A c k W Hc Hk. pose proof (class_size_range c Hc) as CS. (first [ pose proof ((sb_factsT A W)) as dR_6; dand3 dR_6 as _ AL _ | pose proof (sb_factsT A W) as (_ & AL & _) ]).
  (first [ pose proof ((wtR A W)) as dR_7; dand3 dR_7 as WR _ _ | destruct (wtR A W) as (WR & _ & _) ]). (first [ pose proof ((WR c Hc)) as dR_8; dand5 dR_8 as A1 _ _ A4 _ | destruct (WR c Hc) as (A1 & _ & _ & A4 & _) ]).
  cbv zeta. unfold carved_count, carved_count_ in Hk. unfold chunk_addr.
  pose proof (Z_div_mod_eq_full (rg_allocated_user (a_reg A c)) (class_size c)) as DM. rewrite A4, Z.add_0_r in DM.
  split; [nia|]. split; [nia|]. split; [apply chunk_addr_mod32; [exact Hc|lia|exact AL]| lia].
Qed.

Lemma sec_chunk_boundsT : forall A s, WFT A -> In s (sr_chunks (a_sec A)) ->
  kMaxPrimaryUser < cs_n s < REQ_MAX /\ cs_map s mod 4096 = 0 /\ app_rangeA AL_pboth (cs_map s) (map_size (cs_n s)) /\ cs_map s + map_size (cs_n s) <= alloc_ceiling /\
  needed_size2 (cs_n s) + kPageSize <= map_size (cs_n s).   (* [comment removed for export] *)
Proof.
  intros A s W Hin. (first [ pose proof ((wtS A W)) as dR_9; dand5 dR_9 as _ _ _ WS _ | destruct (wtS A W) as (_ & _ & _ & WS & _) ]). (first [ pose proof ((WS s Hin)) as dR_10; dand4 dR_10 as B1 B2 B3 B4 | destruct (WS s Hin) as (B1 & B2 & B3 & B4) ]).
  pose proof (map_size_room (cs_n s)). OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia. exact B3.
Qed.
(* [comment removed for export] *)
Lemma ahull_coverT : forall A md, WFT A -> aledger_ AL_pboth (a_pl A) (a_reg A) (a_sec A) md ->
  hull_cover (pa_hull A) (pa_lhull A) (m_vm_lazy md).
Proof.
  intros A md W LED. destruct LED as (_ & _ & _ & _ & _ & L6 & _ & _ & Z9).
  unfold pa_hull, ahull_of, pa_lhull, alhull_of. apply (ahull_cover_ _ _ _ _ md Z9 L6).
  intros sc Hsc. (first [ pose proof ((sec_chunk_boundsT A sc W Hsc)) as dR; dand5 dR as B1 _ B3 B4 _ | pose proof (sec_chunk_boundsT A sc W Hsc) as (B1 & _ & B3 & B4 & _) ]).
  apply app_facts in B3. pose proof alloc_ceiling_val as CE. clear - B1 B3 CE. Zify.zify; xlia zchecker.
Qed.

Lemma bm_sepT : forall A i j bi si bj sj, WFT A ->
  nth_error (big_maps A) i = Some (bi, si) -> nth_error (big_maps A) j = Some (bj, sj) -> i <> j ->
  bi + si <= bj \/ bj + sj <= bi.
Proof. intros A i j bi si bj sj W Hi Hj NE. destruct (wtM A W) as [D _]. exact (D i j bi si bj sj Hi Hj NE). Qed.

Lemma bm_boundsT : forall A b s, WFT A -> In (b, s) (big_maps A) -> 0 <= b /\ 0 < s /\ b + s <= 2^47.
Proof. intros A b s W H. destruct (wtM A W) as [_ B]. apply B. exact H. Qed.

Lemma primary_in_b6T : forall A a, WFT A -> a_sb A <= a < a_sb A + kSpaceSize + 4096 -> a_b6 A <= a < a_b6 A + kSpaceReserve.
Proof. intros A a W H. (first [ pose proof ((sb_factsT A W)) as dR_11; dand5 dR_11 as _ _ _ R _ | pose proof (sb_factsT A W) as (_ & _ & _ & R & _) ]). unfold kSpaceReserve, kSpaceSize in *. lia. Qed.

Lemma live_user_whereT : forall A u li a, WFT A -> a_livemap A !! u = Some li -> u <= a < u + li_n li ->
  match li_chunk li with
  | ChP (CP c k) => 1 <= c <= 30 /\ 0 <= k < carved_count A c /\ 1 <= li_n li <= kMaxPrimaryUser /\ c = class_of (li_n li) /\
                   u = user_of (a_sb A) (ChP (CP c k)) (li_n li) /\
                   chunk_addr (a_sb A) c k + 16 <= a < chunk_addr (a_sb A) c k + class_size c /\
                   region_beg (a_sb A) c <= chunk_addr (a_sb A) c k /\
                   chunk_addr (a_sb A) c k + class_size c <= region_beg (a_sb A) c + rg_allocated_user (a_reg A c) /\
                   a_sb A <= a < a_sb A + kSpaceSize
  | ChS s => In s (sr_chunks (a_sec A)) /\ kMaxPrimaryUser < li_n li /\ cs_n s = li_n li /\ u = cs_map s + 6144 /\
             cs_map s + 6144 <= a < cs_map s + map_size (cs_n s)
  end.
Proof.
  intros A u li a W Hl Ha. (first [ pose proof ((wtV A W)) as dR_12; dand3 dR_12 as V1 _ _ | destruct (wtV A W) as (V1 & _ & _) ]). specialize (V1 u li Hl). cbv zeta in V1.
  (first [ dand3 V1 as N U C | destruct V1 as (N & U & C) ]). destruct li as [[[c k]|[mb n0]] n]; cbn [li_chunk li_n] in *.
  - (first [ dand3 C as N2 Hc Hk | destruct C as (N2 & Hc & Hk) ]). pose proof (class_of_range n ltac:(lia)) as CR. rewrite <- Hc in CR.
    (first [ pose proof ((primary_layout (a_sb A) c k n CR ltac:(lia) Hc)) as dR_15; dand5 dR_15 as L1 L2 L3 L5 L4 | pose proof (primary_layout (a_sb A) c k n CR ltac:(lia) Hc) as (L1 & L2 & L3 & L5 & L4) ]).
    unfold carved_count. (first [ pose proof ((carved_chunk_boundsT A c k W CR Hk)) as dR_16; dand4 dR_16 as B1 B2 B3 B4 | pose proof (carved_chunk_boundsT A c k W CR Hk) as (B1 & B2 & B3 & B4) ]).
    pose proof (region_piece_boundsT A c W CR) as RB. cbv zeta in RB.
    rewrite U in Ha. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia; try assumption.
    all: unfold kFreeArrayOffset, kRegionSize in *; lia.
  - (first [ dand3 C as N2 -> Hin | destruct C as (N2 & -> & Hin) ]). (first [ pose proof ((secondary_layout mb n N2)) as dR_18; dand7 dR_18 as S1 S2 S3 S4 S5 S6 S7 | pose proof (secondary_layout mb n N2) as (S1 & S2 & S3 & S4 & S5 & S6 & S7) ]).
    cbn [user_of] in U. cbn [cs_map cs_n]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try assumption; lia.
Qed.

Lemma live_user_zoneT : forall A a, WFT A -> in_live_user A a ->
  (a_b6 A <= a < a_b6 A + kSpaceReserve /\ a_sb A <= a < a_sb A + kSpaceSize) \/
  (exists i s, nth_error (sr_chunks (a_sec A)) i = Some s /\ cs_map s + 6144 <= a < cs_map s + map_size (cs_n s)).
Proof.
  (intros A a W; (first [ intro dR_162; dex2 dR_162 as u li; destruct dR_162 as [Hl Ha] | intro dR_162; dand4 dR_162 as u li Hl Ha | intros (u & li & Hl & Ha) ])). pose proof (live_user_whereT A u li a W Hl Ha) as LW.
  destruct (li_chunk li) as [[c k]|s].
  - left. (first [ dand9 LW as _ _ _ _ _ _ _ _ SB | destruct LW as (_ & _ & _ & _ & _ & _ & _ & _ & SB) ]). split; [apply primary_in_b6T; [exact W| lia]| exact SB].
  - right. (first [ dand5 LW as Hin _ _ _ R | destruct LW as (Hin & _ & _ & _ & R) ]). destruct (In_nth_error' _ _ Hin) as [i Hi]. exists i, s. split; assumption.
Qed.

Lemma live_frame_whereT : forall A ff f a, WFT A -> a_fframes A !! ff = Some f -> ff <= a < ff + fsize (ff_class f) ->
  0 <= ff_class f <= 10 /\ ff = fframe_addr (a_fs A) (ff_class f) (ff_pos (a_fhint A (ff_class f)) (ff_class f) (ff_age f)) /\
  a_fs A + kFakeFramesOffset <= ff /\ ff + fsize (ff_class f) <= a_fs A + kFakeStackBytes.
Proof.
  intros A ff f a W Hf Ha. (first [ pose proof ((wtF A W)) as dR_21; dand3 dR_21 as F1 _ _ | destruct (wtF A W) as (F1 & _ & _) ]). (first [ pose proof ((F1 ff f Hf)) as dR_22; dand3 dR_22 as K E AG | destruct (F1 ff f Hf) as (K & E & AG) ]). cbv zeta in *.
  unfold ff_addr_of_ in E. pose proof (ff_pos_range (a_fhint A (ff_class f)) (ff_class f) (ff_age f) K) as PR.
  (first [ pose proof ((fframe_addr_range (a_fs A) (ff_class f) _ K PR)) as dR_23; dand3 dR_23 as R1 R2 R3 | pose proof (fframe_addr_range (a_fs A) (ff_class f) _ K PR) as (R1 & R2 & R3) ]). unfold a_fs in *. rewrite <- E in *.
  OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
Qed.

Lemma live_frame_zoneT : forall A a, WFT A -> in_live_frame A a -> a_fs A + kFakeFramesOffset <= a < a_fs A + kFakeStackBytes.
Proof.
  (intros A a W; (first [ intro dR_163; dex2 dR_163 as ff f; destruct dR_163 as [Hf Ha] | intro dR_163; dand4 dR_163 as ff f Hf Ha | intros (ff & f & Hf & Ha) ])). pose proof (fsize_pos (ff_class f)).
  (first [ pose proof ((live_frame_whereT A ff f a W Hf ltac:(lia))) as dR_24; dand4 dR_24 as K _ R1 R2 | destruct (live_frame_whereT A ff f a W Hf ltac:(lia)) as (K & _ & R1 & R2) ]). lia.
Qed.

Lemma fixed_bm_no_live_userT : forall A i b s a, WFT A -> (1 <= i <= 14)%nat ->
  nth_error (big_maps A) i = Some (b, s) -> b <= a < b + s -> ~ in_live_user A a.
Proof.
  intros A i b s a W Hi Hn Ha LU. pose proof (bm_nth_fixed A) as (E0 & _).
  destruct (live_user_zoneT A a W LU) as [[B6 _]|(j & sc & Hj & R)].
  - destruct (bm_sepT A i 0 b s _ _ W Hn E0 ltac:(lia)); lia.
  - pose proof (bm_nth_sec A j sc Hj) as Ej. destruct (bm_sepT A i (15 + j) b s _ _ W Hn Ej ltac:(lia)); lia.
Qed.

Lemma fixed_bm_no_live_frameT : forall A i b s a, WFT A -> (i <= 14)%nat -> i <> 6%nat ->
  nth_error (big_maps A) i = Some (b, s) -> b <= a < b + s -> ~ in_live_frame A a.
Proof.
  intros A i b s a W Hi N6 Hn Ha LF. (first [ pose proof ((bm_nth_fixed A)) as dR_25; dand8 dR_25 as _ _ _ _ _ _ E6 _ | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & _ & _ & E6 & _) ]).
  pose proof (live_frame_zoneT A a W LF). destruct (bm_sepT A i 6 b s _ _ W Hn E6 ltac:(lia)); unfold kFakeFramesOffset in *; lia.
Qed.

Lemma b6_no_live_frameT : forall A a, WFT A -> a_b6 A <= a < a_b6 A + kSpaceReserve -> ~ in_live_frame A a.
Proof.
  intros A a W Ha LF. (first [ pose proof ((bm_nth_fixed A)) as dR_26; dand8 dR_26 as E0 _ _ _ _ _ E6 _ | pose proof (bm_nth_fixed A) as (E0 & _ & _ & _ & _ & _ & E6 & _) ]).
  pose proof (live_frame_zoneT A a W LF). destruct (bm_sepT A 0 6 _ _ _ _ W E0 E6 ltac:(lia)); unfold kFakeFramesOffset in *; lia.
Qed.

Lemma sec_no_live_frameT : forall A i sc a, WFT A -> nth_error (sr_chunks (a_sec A)) i = Some sc ->
  cs_map sc <= a < cs_map sc + map_size (cs_n sc) -> ~ in_live_frame A a.
Proof.
  intros A i sc a W Hi Ha LF. (first [ pose proof ((bm_nth_fixed A)) as dR_27; dand8 dR_27 as _ _ _ _ _ _ E6 _ | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & _ & _ & E6 & _) ]). pose proof (bm_nth_sec A i sc Hi) as Ei.
  pose proof (live_frame_zoneT A a W LF). destruct (bm_sepT A (15 + i) 6 _ _ _ _ W Ei E6 ltac:(lia)); unfold kFakeFramesOffset in *; lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma heap_shadow_strictT : forall A a, WFT A -> heap_shadow A a -> in_shadow_strict a.
Proof.
  intros A a W HS. pose proof alloc_ceiling_val as CE. unfold heap_shadow, heap_shadow_ in HS. change (p_sb (a_pl A)) with (a_sb A) in HS.
  destruct HS as [(c & Hc & R)|[(c & Hc & R)|(sc & Hsc & R)]]; cbv zeta in R.
  - pose proof (region_piece_boundsT A c W Hc) as RB. cbv zeta in RB.
    destruct (Z.eq_dec (rg_mapped_user (a_reg A c)) 0) as [E|NE]; [rewrite E in R; change (0/8) with 0 in R; lia|].
    (first [ dand11 RB as R1 R2 R3 R4 R5 R6 R7 R8 AL MU _ | destruct RB as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & AL & MU & _) ]).
    apply (sh_iv_strict (region_beg (a_sb A) c) (rg_mapped_user (a_reg A c)) a);
      [apply (mod0_down _ 0x10000 8); [exists 8192; reflexivity| exact AL] | exact MU | lia | | exact R].
    right. unfold kRegionSize, kSpaceSize, kFreeArrayOffset in *. lia.
  - pose proof (region_piece_boundsT A c W Hc) as RB. cbv zeta in RB.
    destruct (Z.eq_dec (rg_mapped_fa (a_reg A c)) 0) as [E|NE]; [rewrite E in R; change (0/8) with 0 in R; lia|].
    (first [ dand12 RB as R1 R2 R3 R4 R5 R6 R7 R8 AL _ _ MF | destruct RB as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & AL & _ & _ & MF) ]).
    apply (sh_iv_strict (region_beg (a_sb A) c + kFreeArrayOffset) (rg_mapped_fa (a_reg A c)) a);
      [rewrite Z.add_mod by lia; rewrite (mod0_down _ 0x10000 8 ltac:(exists 8192; reflexivity) AL); reflexivity | exact MF | lia | | exact R].
    right. unfold kRegionSize, kSpaceSize, kFreeArrayOffset in *. lia.
  - (first [ pose proof ((sec_chunk_boundsT A sc W Hsc)) as dR_39; dand5 dR_39 as B1 B2 B3 B4 B5 | pose proof (sec_chunk_boundsT A sc W Hsc) as (B1 & B2 & B3 & B4 & B5) ]). pose proof (map_size_room (cs_n sc)). pose proof (map_size_page (cs_n sc)) as MP.
    apply app_facts in B3.
    apply (sh_iv_strict (cs_map sc) (map_size (cs_n sc)) a);
      [apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact B2] | apply (mod0_down _ kPageSize 8); [exists 512; reflexivity| exact MP] | unfold kPageSize in *; lia | | exact R].
    unfold kPageSize in *. lia.
Qed.

Lemma heap_shadow_rangeT : forall A a, WFT A -> heap_shadow A a -> in_shadow_maps a.
Proof. intros A a W HS. apply strict_in_maps. exact (heap_shadow_strictT A a W HS). Qed.

Lemma runtime_maps_rangeT : forall A b s a, WFT A -> In (b, s) (runtime_maps A) -> b <= a < b + s ->
  (kHighMemBeg <= a < alloc_ceiling) \/ (4096 <= a < kLowShadowMapBeg /\ (a < al_image_lo AL_pboth \/ al_image_hi AL_pboth <= a)).
Proof.
  intros A b s a W Hin Ha. pose proof alloc_ceiling_val as CE. pose proof (wtP A W) as P. apply wf_place_cheap in P.
  (first [ pose proof ((sb_factsT A W)) as dR_40; dand5 dR_40 as _ _ HB RG SCE | pose proof (sb_factsT A W) as (_ & _ & HB & RG & SCE) ]). cbn [al_image_lo al_image_hi AL_pboth].
  (first [ dand36 P as _ _ _ _ Apa _ _ Athr _ _ Actx _ _ Anod _ _ Afr _ _ Afs _ _ Aitab _ _ Am64 _ _ Agv _ _ Adv _ _ Am11 dR_P_t0; dand4 dR_P_t0 as _ _ Adtls _ | destruct P as (_ & _ & _ & _ & Apa & _ & _ & Athr & _ & _ & Actx & _ & _ & Anod & _ & _ & Afr & _ & _ & Afs & _ & _ &
                 Aitab & _ & _ & Am64 & _ & _ & Agv & _ & _ & Adv & _ & _ & Am11 & _ & _ & Adtls & _) ]).
  apply app_facts in Apa. apply app_facts in Athr. apply app_facts in Actx. apply app_facts in Anod. apply app_facts in Afr.
  apply app_facts in Afs. apply app_facts in Aitab. apply app_facts in Am64. apply app_facts in Agv. apply app_facts in Adv.
  apply app_facts in Am11. apply app_facts in Adtls.
  unfold runtime_maps, runtime_maps_ in Hin. apply in_app_iff in Hin as [Hin|Hin]; [|apply in_app_iff in Hin as [Hin|Hin]].
  - unfold a_b6, a_sb, p_ri in *.
    destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]]; injection E as <- <-.
    + clear - CE Athr Ha. unfold kLowShadowMapBeg, kHighMemBeg in *. lia.
    + clear - CE Actx Ha. unfold kLowShadowMapBeg, kHighMemBeg in *. lia.
    + clear - CE HB RG SCE Ha. unfold kSpaceSize, kHighMemBeg in *. lia.
    + clear - CE Afs Ha. unfold kLowShadowMapBeg, kHighMemBeg in *. lia.
    + clear - CE Anod Ha. unfold kLowShadowMapBeg, kHighMemBeg in *. lia.
    + clear - CE Afr Ha. unfold kLowShadowMapBeg, kHighMemBeg in *. lia.
    + clear - CE Apa Ha. unfold kChunksBlockCount, kPtrArrayReserve, kLowShadowMapBeg, kHighMemBeg in *. lia.
    + clear - CE Aitab Ha. unfold kLowShadowMapBeg, kHighMemBeg in *. lia.
    + clear - CE Am64 Ha. unfold kLowShadowMapBeg, kHighMemBeg in *. lia.
    + clear - CE Adtls Ha. unfold kLowShadowMapBeg, kHighMemBeg in *. lia.
    + clear - CE Agv Ha. unfold kLowShadowMapBeg, kHighMemBeg in *. lia.
    + clear - CE Adv Ha. unfold kLowShadowMapBeg, kHighMemBeg in *. lia.
    + clear - CE Am11 Ha. unfold kLowShadowMapBeg, kHighMemBeg in *. lia.
  - left. apply in_flat_map in Hin as (c & Hc & Hin). apply in_map_iff in Hc as (cn & <- & Hcn). apply in_seq in Hcn.
    pose proof (region_piece_boundsT A (Z.of_nat cn) W ltac:(lia)) as RB. cbv zeta in RB. change (p_sb (a_pl A)) with (a_sb A) in Hin.
    clear Apa Athr Actx Anod Afr Afs Aitab Am64 Agv Adv Am11 Adtls.
    unfold kHighMemBeg, kFreeArrayOffset, kRegionSize, kSpaceSize in *.
    destruct Hin as [E|[E|[]]]; injection E as <- <-; lia.
  - apply in_map_iff in Hin as (sc & E & Hsc). injection E as <- <-.
    (first [ pose proof ((sec_chunk_boundsT A sc W Hsc)) as dR_42; dand5 dR_42 as _ _ B3 B4 _ | pose proof (sec_chunk_boundsT A sc W Hsc) as (_ & _ & B3 & B4 & _) ]). apply app_facts in B3.
    clear - CE B3 B4 Ha. unfold kLowShadowMapBeg, kHighMemBeg in *. lia.
Qed.

(* [comment removed for export] *)

Lemma fs_shadow_strictT : forall A a, WFT A -> sh (a_fs A) <= a < sh (a_fs A) + kFakeStackBytes / 8 -> in_shadow_strict a.
Proof.
  intros A a W Ha. pose proof alloc_ceiling_val as CE. pose proof (wtP A W) as P. apply wf_place_cheap in P.
  assert (F3 : p_fs (a_pl A) mod 4096 = 0) by tauto. assert (F1 : app_rangeA AL_pboth (p_fs (a_pl A)) kFakeStackBytes) by tauto.
  apply app_facts in F1. clear P. unfold a_fs in *.
  apply (sh_iv_strict (p_fs (a_pl A)) kFakeStackBytes a); [apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact F3] | reflexivity | reflexivity | | exact Ha].
  unfold kFakeStackBytes, kLowShadowMapBeg, kHighMemBeg in *. lia.
Qed.

Lemma fs_shadow_in_mapsT : forall A a, WFT A -> sh (a_fs A) <= a < sh (a_fs A) + kFakeStackBytes / 8 -> in_shadow_maps a.
Proof. intros A a W Ha. apply strict_in_maps. exact (fs_shadow_strictT A a W Ha). Qed.

Lemma place_factsT : forall A, WFT A -> let P := a_pl A in
  (app_rangeA AL_pboth (p_thr P) 4096 /\ p_thr P + 4096 <= alloc_ceiling /\ p_thr P mod 4096 = 0) /\
  (app_rangeA AL_pboth (p_ctx P) 0x10000 /\ p_ctx P + 0x10000 <= alloc_ceiling /\ p_ctx P mod 4096 = 0) /\
  (app_rangeA AL_pboth (p_nodes0 P) kDepotNodesBlock /\ p_nodes0 P + kDepotNodesBlock <= alloc_ceiling /\ p_nodes0 P mod 4096 = 0) /\
  (app_rangeA AL_pboth (p_frames0 P) kStackStoreBlockBytes /\ p_frames0 P + kStackStoreBlockBytes <= alloc_ceiling /\ p_frames0 P mod 4096 = 0) /\
  (app_rangeA AL_pboth (p_fs P) kFakeStackBytes /\ p_fs P + kFakeStackBytes <= alloc_ceiling /\ p_fs P mod 4096 = 0) /\
  (app_rangeA AL_pboth (p_itab P) 0x38e000 /\ p_itab P + 0x38e000 <= alloc_ceiling /\ p_itab P mod 4096 = 0) /\
  (app_rangeA AL_pboth (p_m64k P) 0x10000 /\ p_m64k P + 0x10000 <= alloc_ceiling /\ p_m64k P mod 4096 = 0) /\
  (app_rangeA AL_pboth (p_gvec P) 4096 /\ p_gvec P + 4096 <= alloc_ceiling /\ p_gvec P mod 4096 = 0) /\
  (app_rangeA AL_pboth (p_dvec P) 4096 /\ p_dvec P + 4096 <= alloc_ceiling /\ p_dvec P mod 4096 = 0) /\
  (app_rangeA AL_pboth (p_m11 P) 4096 /\ p_m11 P + 4096 <= alloc_ceiling /\ p_m11 P mod 4096 = 0) /\
  (app_rangeA AL_pboth (p_dtls P) 4096 /\ p_dtls P + 4096 <= alloc_ceiling /\ p_dtls P mod 4096 = 0) /\
  (app_rangeA AL_pboth (p_pa P) kPtrArrayReserve /\ p_pa P + kPtrArrayReserve <= alloc_ceiling /\ p_pa P mod 4096 = 0) /\
  (alloc_ceiling + 0x800000 <= p_sp0 P <= 2^47 /\ 0 <= p_stk_span P <= 0x240000 /\ p_sp0 P mod 16 = 0) /\
  (0 <= p_stk_top P < 2^64 /\ 0 <= p_stk_bot P < 2^64).
Proof. intros A W. pose proof (wtP A W) as P. apply wf_place_cheap in P. cbv zeta in *. tauto. Qed.

Lemma place_fsT : forall A, WFT A -> app_rangeA AL_pboth (a_fs A) kFakeStackBytes /\ a_fs A + kFakeStackBytes <= alloc_ceiling /\ a_fs A mod 4096 = 0.
Proof. intros A W. pose proof (place_factsT A W) as P. cbv zeta in P. unfold a_fs. tauto. Qed.
End Twins.

(* [comment removed for export] *)
Section TransportR.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Context {DR : DepotRep}.
  Variables (A : AState) (v v' : mem) (held : list Z).
  Hypothesis AR : WFT A /\ arepr LPA AL_pboth held A v.
  Let WF0 : WFT A. Proof. exact (proj1 AR). Qed.
  Let R : arepr LPA AL_pboth held A v. Proof. exact (proj2 AR). Qed.
  Local Notation thr := (p_thr (a_pl A)).
  Local Notation sb := (a_sb A).
  (* [comment removed for export] *)
  Hypothesis NN : forall a, 0 <= a -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> a < 2^64 -> v (Z_to_bv 64 a) <> None -> v' (Z_to_bv 64 a) <> None.

  (* [comment removed for export] *)
  Local Notation QGL := (a_qglobal A ++ a_qlimbo A).
  Lemma b_in_big : forall b, In b (a_qthread A ++ a_qglobal A) -> In b (a_qthread A ++ QGL).
  Proof. intros b Hb. rewrite app_assoc. apply in_or_app. left. exact Hb. Qed.
  Lemma q_in_big : forall e, In e (q_entries (a_qthread A ++ a_qglobal A)) -> In e (q_entries (a_qthread A ++ QGL)).
  Proof. intros e He. unfold q_entries in *. rewrite app_assoc, flat_map_app, in_app_iff. left. exact He. Qed.
  Lemma bi_in_big : forall k, In k (batch_indices_ (a_qthread A) (a_qglobal A)) -> In k (batch_indices_ (a_qthread A) QGL).
  Proof. intros k Hk. unfold batch_indices_ in *. rewrite app_assoc, map_app, in_app_iff. left. exact Hk. Qed.

  Lemma TPV : bv_unsigned (cl_tp LPA) = 0x5e7bd8.
  Proof. cbn [cl_tp LPA]. rewrite unsigned_lit by lia. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma mapped_N : forall a k, 0 <= a -> (a + k <= 0x10000 \/ 0x60a000 <= a) -> a + k <= 2^64 -> mapped v a k -> mapped v' a k.
  Proof. intros a k H0 H1 H2 M. eapply mapped_mono; [exact M|]. intros i Hi. apply NN; lia. Qed.
  Lemma junk_N : forall a k, 0 <= a -> (a + k <= 0x10000 \/ 0x60a000 <= a) -> junk_at rsegs v a k -> junk_at rsegs v' a k.
  Proof.
    (intros a k H0 H1; (first [ intro dR_164; dex1 dR_164 as bs; destruct dR_164 as [L B] | intro dR_164; dand3 dR_164 as bs L B | intros (bs & L & B) ])). pose proof (bytes_at_bound _ _ _ _ B) as BB. rewrite L in BB.
    apply junk_at_of_mapped; [lia| lia| lia|]. apply mapped_N; [lia| lia| lia|]. rewrite <- L. eapply bytes_at_mapped_off; [exact B| lia| lia].
  Qed.

  (* [comment removed for export] *)
  Ltac trim := repeat match goal with H : _ /\ _ /\ _ |- _ => clear H | H : Forall _ _ |- _ => clear H | H : arepr _ _ _ _ _ |- _ => clear H
                                    | H : _ \/ _ |- _ => clear H end.
  Ltac leaf H AG :=
    lazymatch type of H with
    | u64_at _ _ _ _ => eapply u64_at_agree; [exact H|]; intros i__ Hi__; AG
    | u32_at _ _ _ _ => eapply u32_at_agree; [exact H|]; intros i__ Hi__; AG
    | u16_at _ _ _ _ => eapply u16_at_agree; [exact H|]; intros i__ Hi__; AG
    | u8_at _ _ _ _ => eapply u8_at_agree;  [exact H|]; AG
    | fill_at _ _ _ _ _ => eapply fill_at_agree; [exact H|]; intros i__ Hi__; offs_h Hi__; AG
    | junk_at _ _ _ _ => eapply junk_at_agree; [exact H|]; intros i__ Hi__; offs_h Hi__; AG
    end.
  Ltac walk H AG :=
    lazymatch goal with
    | |- _ /\ _ => let H1 := fresh "L" in let H2 := fresh "L" in destruct H as [H1 H2]; split; [walk H1 AG | walk H2 AG]
    | |- _ => leaf H AG
    end.

  (* [comment removed for export] *)
  Lemma consts_P :
    (forall cst a, In cst (cl_consts LPA) -> fst cst <= a < fst cst + Z.of_nat (length (snd cst)) -> v' (wz a) = v (wz a)) ->
    (forall a, cl_shared LPA a -> v' (wz a) = v (wz a)) ->
    (forall a, cfoot_stat a -> v' (wz a) = v (wz a)) ->
    (forall a, cfoot_thr thr a -> v' (wz a) = v (wz a)) ->
    (forall a, cfoot_misc (a_pl A) a -> v' (wz a) = v (wz a)) ->
    consts_repr_ LPA AL_pboth (a_pl A) v'.
  Proof.
    intros AGconst AGshared AGs AGt AGm.
    pose proof (ar_consts _ _ _ _ _ R) as C. pose proof TPV as TP.
    unfold consts_repr_ in *. cbv zeta in *. destruct C as (CF & C).
    split.
    { apply Forall_forall. intros cst Hc. pose proof (proj1 (Forall_forall _ _) CF cst Hc) as B.
      eapply bytes_at_agree_gen; [exact B|]. intros i Hi. apply (AGconst cst); [exact Hc| lia]. }
    do 17 (let L := fresh "L" in destruct C as [L C]; split; [leaf L ltac:(apply AGs; trim; unfold cfoot_stat; offs; lia) |]).
    (first [ dand7 C as K1 K2 K3 KS KE1 KE2 C | destruct C as (K1 & K2 & K3 & KS & KE1 & KE2 & C) ]).
    split; [leaf K1 ltac:(apply AGshared; apply KS; lia)|]. split; [leaf K2 ltac:(apply AGshared; rewrite KE1; rewrite <- Z.add_assoc; apply KS; lia)|].
    split; [leaf K3 ltac:(apply AGshared; rewrite KE2; rewrite <- Z.add_assoc; apply KS; lia)|].
    split; [exact KS|]. split; [exact KE1|]. split; [exact KE2|].
    do 7 (let L := fresh "L" in destruct C as [L C]; split; [leaf L ltac:(apply AGs; trim; unfold cfoot_stat; offs; lia) |]).
    do 5 (let L := fresh "L" in destruct C as [L C]; split; [leaf L ltac:(apply AGt; trim; unfold cfoot_thr; offs; lia) |]).
    do 2 (let L := fresh "L" in destruct C as [L C]; split; [leaf L ltac:(apply AGm; trim; unfold cfoot_misc; offs; lia) |]).
    destruct C as [(tsd & T1 & T2 & T3) C]. split.
    - exists tsd. split; [|split; [exact T2|]].
      + leaf T1 ltac:(apply AGm; trim; unfold cfoot_misc; offs; lia).
      + leaf T3 ltac:(apply AGshared; apply T2; lia).
    - (first [ dand5 C as C D1 D2 D3 D4 | destruct C as (C & D1 & D2 & D3 & D4) ]). split; [leaf C ltac:(apply AGm; trim; unfold cfoot_misc; offs; lia)|].
      split; [leaf D1 ltac:(apply AGm; trim; unfold cfoot_misc; offs; lia)|].
      split; [leaf D2 ltac:(apply AGm; trim; unfold cfoot_misc; offs; lia)|].
      split; [leaf D3 ltac:(apply AGt; trim; unfold cfoot_thr; offs; lia)| leaf D4 ltac:(apply AGt; trim; unfold cfoot_thr; offs; lia)].
  Qed.

  (* [comment removed for export] *)
  Lemma locks_P : (forall a, lfoot (a_pl A) a -> v' (wz a) = v (wz a)) -> locks_repr_ LPA AL_pboth (a_pl A) held v'.
  Proof.
    intros AG. pose proof (ar_locks _ _ _ _ _ R) as C. unfold locks_repr_ in *. cbv zeta in *. destruct C as (C0 & C).
    split.
    - intros c' Hc. destruct (C0 c' Hc) as [X Y].
      split; [leaf X ltac:(apply AG; trim; unfold lfoot; offs; lia) | leaf Y ltac:(apply AG; trim; unfold lfoot; offs; lia)].
    - walk C ltac:(apply AG; trim; unfold lfoot; offs; lia).
  Qed.

  (* [comment removed for export] *)
  Lemma consts_P2 :
    (forall cst, In cst (cl_consts LPA) ->
       (forall a, fst cst <= a < fst cst + Z.of_nat (length (snd cst)) -> v' (wz a) = v (wz a)) \/ bytes_at rsegs v' (fst cst) (snd cst)) ->
    (forall a, cl_shared LPA a -> v' (wz a) = v (wz a)) ->
    (forall a, cfoot_stat a -> v' (wz a) = v (wz a)) ->
    (forall a, cfoot_thr thr a -> v' (wz a) = v (wz a)) ->
    (forall a, cfoot_misc (a_pl A) a -> v' (wz a) = v (wz a)) ->
    consts_repr_ LPA AL_pboth (a_pl A) v'.
  Proof.
    intros AGconst AGshared AGs AGt AGm.
    pose proof (ar_consts _ _ _ _ _ R) as C. pose proof TPV as TP.
    unfold consts_repr_ in *. cbv zeta in *. destruct C as (CF & C).
    split.
    { apply Forall_forall. intros cst Hc. pose proof (proj1 (Forall_forall _ _) CF cst Hc) as B.
      destruct (AGconst cst Hc) as [AG|B']; [| exact B'].
      eapply bytes_at_agree_gen; [exact B|]. intros i Hi. apply AG. lia. }
    do 17 (let L := fresh "L" in destruct C as [L C]; split; [leaf L ltac:(apply AGs; trim; unfold cfoot_stat; offs; lia) |]).
    (first [ dand7 C as K1 K2 K3 KS KE1 KE2 C | destruct C as (K1 & K2 & K3 & KS & KE1 & KE2 & C) ]).
    split; [leaf K1 ltac:(apply AGshared; apply KS; lia)|]. split; [leaf K2 ltac:(apply AGshared; rewrite KE1; rewrite <- Z.add_assoc; apply KS; lia)|].
    split; [leaf K3 ltac:(apply AGshared; rewrite KE2; rewrite <- Z.add_assoc; apply KS; lia)|].
    split; [exact KS|]. split; [exact KE1|]. split; [exact KE2|].
    do 7 (let L := fresh "L" in destruct C as [L C]; split; [leaf L ltac:(apply AGs; trim; unfold cfoot_stat; offs; lia) |]).
    do 5 (let L := fresh "L" in destruct C as [L C]; split; [leaf L ltac:(apply AGt; trim; unfold cfoot_thr; offs; lia) |]).
    do 2 (let L := fresh "L" in destruct C as [L C]; split; [leaf L ltac:(apply AGm; trim; unfold cfoot_misc; offs; lia) |]).
    destruct C as [(tsd & T1 & T2 & T3) C]. split.
    - exists tsd. split; [|split; [exact T2|]].
      + leaf T1 ltac:(apply AGm; trim; unfold cfoot_misc; offs; lia).
      + leaf T3 ltac:(apply AGshared; apply T2; lia).
    - (first [ dand5 C as C D1 D2 D3 D4 | destruct C as (C & D1 & D2 & D3 & D4) ]). split; [leaf C ltac:(apply AGm; trim; unfold cfoot_misc; offs; lia)|].
      split; [leaf D1 ltac:(apply AGm; trim; unfold cfoot_misc; offs; lia)|].
      split; [leaf D2 ltac:(apply AGm; trim; unfold cfoot_misc; offs; lia)|].
      split; [leaf D3 ltac:(apply AGt; trim; unfold cfoot_thr; offs; lia)| leaf D4 ltac:(apply AGt; trim; unfold cfoot_thr; offs; lia)].
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma region_P : forall c', 1 <= c' <= 30 -> (forall a, rfoot sb (a_reg A c') c' a -> v' (wz a) = v (wz a)) ->
    region_repr_ LPA sb (a_reg A c') v' c'.
  Proof.
    intros c' Hc AG. pose proof (ar_regions _ _ _ _ _ R c' Hc) as C. pose proof alloc_ceiling_val as CE.
    pose proof (region_piece_boundsT A c' WF0 Hc) as RB. cbv zeta in RB. (first [ pose proof ((wtR A WF0)) as dR_49; dand3 dR_49 as WR _ _ | destruct (wtR A WF0) as (WR & _ & _) ]). (first [ pose proof ((WR c' Hc)) as dR_50; dand8 dR_50 as Q1 Q2 Q3 Q4 Q5 Q6 Q7 _ | pose proof (WR c' Hc) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & _) ]).
    unfold region_repr_ in *. cbv zeta in *.
    assert (AGri' : forall x, region_info_addr sb c' <= x < region_info_addr sb c' + 128 -> v' (wz x) = v (wz x)).
    { intros x Hx. apply AG. unfold rfoot, kRegionInfoSize. left. exact Hx. }
    assert (AGfa' : forall x, free_array_beg sb c' <= x < free_array_beg sb c' + rg_mapped_fa (a_reg A c') -> v' (wz x) = v (wz x)).
    { intros x Hx. apply AG. unfold rfoot. right. exact Hx. }
    clear AG.
    do 10 (let L := fresh "L" in destruct C as [L C]; split; [leaf L ltac:(apply AGri'; offs; lia) |]).
    (first [ dand3 C as CF M1 M2 | destruct C as (CF & M1 & M2) ]). split; [|split].
    - intros i k E. pose proof (CF i k E) as LF. assert (Z.of_nat i < Z.of_nat (length (rg_free (a_reg A c')))) by (pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite E; discriminate)); lia).
      leaf LF ltac:(apply AGfa'; offs; lia).
    - unfold free_array_beg in *. apply mapped_N; [unfold kHighMemBeg, kFreeArrayOffset in *; lia| right; unfold kHighMemBeg, kFreeArrayOffset in *; lia| unfold kRegionSize, kSpaceSize, kFreeArrayOffset in *; lia| exact M1].
    - apply mapped_N; [unfold kHighMemBeg in *; lia| right; unfold kHighMemBeg in *; lia| unfold kRegionSize, kSpaceSize, kFreeArrayOffset in *; lia| exact M2].
  Qed.

  (* [comment removed for export] *)
  Lemma sec_P :
    (forall a, sfoot_stat a -> v' (wz a) = v (wz a)) ->
    (forall a, p_pa (a_pl A) <= a < p_pa (a_pl A) + 8 * Z.of_nat (length (sr_chunks (a_sec A))) -> v' (wz a) = v (wz a)) ->
    (forall sc a, In sc (sr_chunks (a_sec A)) -> cs_map sc <= a < cs_map sc + kSecondaryHeaderSize -> v' (wz a) = v (wz a)) ->
    sec_repr_ LPA AL_pboth (a_pl A) (a_sec A) v'.
  Proof.
    intros AGs AGpa AGsec.
    pose proof (ar_sec _ _ _ _ _ R) as C. pose proof alloc_ceiling_val as CE. (first [ pose proof ((place_factsT A WF0)) as dR_52; dand13 dR_52 as _ _ _ _ _ _ _ _ _ _ _ Ppa _ | pose proof (place_factsT A WF0) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ppa & _) ]). cbv zeta in Ppa.
    (first [ dand3 Ppa as Ppa1 Ppa2 Ppa3 | destruct Ppa as (Ppa1 & Ppa2 & Ppa3) ]). apply app_facts in Ppa1.
    (first [ pose proof ((wtS A WF0)) as dR_54; dand4 dR_54 as _ LEN RES _ | destruct (wtS A WF0) as (_ & LEN & RES & _) ]). unfold kChunksBlockCount in RES. unfold sec_repr_ in *. cbv zeta in *.
    (first [ dand7 C as X1 X2 J1 J2 J3 CH M | destruct C as (X1 & X2 & J1 & J2 & J3 & CH & M) ]).
    split; [leaf X1 ltac:(apply AGs; trim; unfold sfoot_stat; offs; lia)|]. split; [leaf X2 ltac:(apply AGs; trim; unfold sfoot_stat; offs; lia)|].
    split; [leaf J1 ltac:(apply AGs; trim; unfold sfoot_stat; offs; lia)|]. split; [leaf J2 ltac:(apply AGs; trim; unfold sfoot_stat; offs; lia)|].
    split; [leaf J3 ltac:(apply AGs; trim; unfold sfoot_stat; offs; lia)|]. split.
    - intros i sc E. destruct (CH i sc E) as [X Y]. pose proof (nth_error_In _ _ E) as Hin.
      assert (Z.of_nat i < Z.of_nat (length (sr_chunks (a_sec A)))) by (pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite E; discriminate)); lia).
      split.
      + leaf X ltac:(apply AGpa; lia).
      + eapply rw_cells_agree; [exact Y|]. rewrite sec_hdr_size. intros j Hj. apply (AGsec sc); [exact Hin| unfold kSecondaryHeaderSize; lia].
    - apply mapped_N; [clear - Ppa1; lia| clear - Ppa1 LEN RES; ALogic2.kun; unfold kPtrArrayReserve in *; lia| clear - Ppa1 Ppa2 LEN RES CE; ALogic2.kun; unfold kPtrArrayReserve in *; lia| exact M].
  Qed.

  (* [comment removed for export] *)
  Lemma ia_P : (forall a, iafoot a -> v' (wz a) = v (wz a)) -> ia_repr_ LPA AL_pboth (a_ia_inited A) v'.
  Proof.
    intros AG. pose proof (ar_ia _ _ _ _ _ R) as C. unfold ia_repr_ in *. cbv zeta in *. destruct C as [C0 C]. split.
    - intros i Hi. pose proof (C0 i Hi) as L. unfold kDepotNodesL1 in Hi. leaf L ltac:(apply AG; trim; unfold iafoot; offs; lia).
    - destruct (a_ia_inited A); walk C ltac:(apply AG; trim; unfold iafoot; offs; lia).
  Qed.

  (* [comment removed for export] *)
  Lemma fsbase_P : (forall a, a_fs A <= a < a_fs A + kFakeFlagsOffset -> v' (wz a) = v (wz a)) -> fs_base_ LPA (a_pl A) (a_fhint A) v'.
  Proof.
    intros AGfs. pose proof (ar_fsbase _ _ _ _ _ R) as C. pose proof alloc_ceiling_val as CE. (first [ pose proof ((place_fsT A WF0)) as dR_56; dand3 dR_56 as FS1 FS2 FSM | pose proof (place_fsT A WF0) as (FS1 & FS2 & FSM) ]). unfold a_fs in FS1, FS2, FSM, AGfs.
    unfold fs_base_ in *. cbv zeta in *. (first [ dand5 C as H0 H1 H2 M1 M2 | destruct C as (H0 & H1 & H2 & M1 & M2) ]).
    split; [|split; [leaf H1 ltac:(apply AGfs; unfold kFakeFlagsOffset; offs; lia)| split; [leaf H2 ltac:(apply AGfs; unfold kFakeFlagsOffset; offs; lia)| split]]].
    - intros k Hk. pose proof (H0 k Hk) as L. leaf L ltac:(apply AGfs; unfold kFakeFlagsOffset; offs; lia).
    - apply app_facts in FS1. apply mapped_N; [lia| unfold kFakeStackBytes in *; lia| lia| exact M1].
    - pose proof (fs_shadow_strictT A (sh (p_fs (a_pl A))) WF0 ltac:(unfold a_fs, kFakeStackBytes; lia)) as X1.
      pose proof (fs_shadow_strictT A (sh (p_fs (a_pl A)) + (kFakeStackBytes / 8 - 1)) WF0 ltac:(unfold a_fs, kFakeStackBytes; lia)) as X2.
      unfold in_shadow_strict, kLowShadowBeg, kShadowGapBeg, kHighShadowMapBeg, kHighMemBeg in X1, X2.
      apply mapped_N; [lia| right; lia| lia| exact M2].
  Qed.

  Lemma fsptrs_P : (forall a, a_fs A + kFakeFramesOffset <= a < a_fs A + kFakeStackBytes -> v' (wz a) = v (wz a)) ->
    fs_ptrs_ LPA (a_fs A) (a_fhint A) (a_fframes A) v'.
  Proof.
    intros AGfs ff f Hf. pose proof (ar_fsptrs _ _ _ _ _ R ff f Hf) as L.
    destruct (wtF A WF0) as (F1 & _). destruct (F1 ff f Hf) as (K0 & _). pose proof (fsize_pos _ K0) as FS.
    (first [ pose proof ((live_frame_whereT A ff f ff WF0 Hf ltac:(lia))) as dR_58; dand4 dR_58 as K _ R1 R2 | destruct (live_frame_whereT A ff f ff WF0 Hf ltac:(lia)) as (K & _ & R1 & R2) ]).
    leaf L ltac:(apply AGfs; unfold saved_flag_ptr, kFakeFramesOffset in *; lia).
  Qed.

  Lemma fsflags_P : (forall a, a_fs A + kFakeFlagsOffset <= a < a_fs A + kFakeFramesOffset -> v' (wz a) = v (wz a)) ->
    fs_flags_ LPA (a_fs A) (a_fhint A) (a_fframes A) v'.
  Proof.
    intros AGfs k pos Hk Hpos. (first [ pose proof ((ar_fsflags _ _ _ _ _ R k pos Hk Hpos)) as dR_59; dex1 dR_59 as b; destruct dR_59 as [U D] | pose proof ((ar_fsflags _ _ _ _ _ R k pos Hk Hpos)) as dR_59; dand3 dR_59 as b U D | destruct (ar_fsflags _ _ _ _ _ R k pos Hk Hpos) as (b & U & D) ]). exists b. split; [| exact D].
    pose proof (fflag_addr_range (a_fs A) k pos Hk Hpos).
    leaf U ltac:(apply AGfs; unfold kFakeFlagsOffset, kFakeFramesOffset, kFakeStackBytes in *; lia).
  Qed.

  (* [comment removed for export] *)
  Lemma maps_P : maps_repr_ AL_pboth (a_pl A) v'.
  Proof.
    (first [ pose proof ((ar_maps _ _ _ _ _ R)) as dR_60; dand4 dR_60 as M1 M2 M3 M4 | pose proof (ar_maps _ _ _ _ _ R) as (M1 & M2 & M3 & M4) ]). pose proof alloc_ceiling_val as CE.
    (first [ pose proof ((place_factsT A WF0)) as dR_61; dand14 dR_61 as _ _ _ _ _ _ _ _ _ _ _ _ Psp0 _ | pose proof (place_factsT A WF0) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Psp0 & _) ]). cbv zeta in Psp0.
    (first [ pose proof ((sb_factsT A WF0)) as dR_62; dand5 dR_62 as _ _ HB6 RSB SCE | pose proof (sb_factsT A WF0) as (_ & _ & HB6 & RSB & SCE) ]). unfold maps_repr_. unfold a_sb, a_b6, p_ri in *.
    cbn [al_image_lo al_image_hi AL_pboth] in M4 |- *.
    change (shadow_region 65536 (6332416 - 65536)) with (0x7fffa000, 0xbf400) in M4 |- *. cbn [fst snd] in M4 |- *.
    (first [ pose proof (stack_shadow_iv_facts) as dR_63; dand4 dR_63 as SF1 SF2 SF3 SF4 | pose proof stack_shadow_iv_facts as (SF1 & SF2 & SF3 & SF4) ]).
    ALogic2.kun.
    split; [apply mapped_N; [lia| right; lia| lia| exact M1]|]. split; [apply mapped_N; [lia| right; lia| lia| exact M2]|].
    split; [apply mapped_N; [lia| right; lia| lia| exact M3]| apply mapped_N; [lia| right; lia| lia| exact M4]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma cache_line_P : forall (cache : Z -> pcache) c', 0 <= c' < 32 -> pk_chunks (cache c') = pk_chunks (a_cache A c') ->
    (forall a, thr + off_th_per_class c' <= a < thr + off_th_per_class c' + 80 -> v' (wz a) = v (wz a)) ->
    let e := thr + off_th_per_class c' in let ks := pk_chunks (cache c') in
    Z.of_nat (length ks) <= 16 /\
    u32_at rsegs v' (e + off_pc_count) (Z.of_nat (length ks)) /\
    (if a_cache_inited A && negb (c' =? 0) then u32_at rsegs v' (e + off_pc_max_count) (max_count c') /\ u64_at rsegs v' (e + off_pc_class_size) (class_size c')
     else u32_at rsegs v' (e + off_pc_max_count) 0 /\ u64_at rsegs v' (e + off_pc_class_size) 0) /\
    (forall i k, nth_error ks i = Some k -> u32_at rsegs v' (e + off_pc_chunk (Z.of_nat i)) (k * class_size c' / kCompactPtrScale)) /\
    junk_at rsegs v' (e + off_pc_chunk (Z.of_nat (length ks))) (4 * (16 - Z.of_nat (length ks))).
  Proof.
    intros cache c' Hc' EQ AGe. cbv zeta. rewrite EQ. pose proof (ar_cache _ _ _ _ _ R) as (C0 & _). pose proof alloc_ceiling_val as CE.
    pose proof (place_factsT A WF0) as (Pthr & _). cbv zeta in Pthr. (first [ dand3 Pthr as Pthr1 Pthr2 Pthr3 | destruct Pthr as (Pthr1 & Pthr2 & Pthr3) ]). apply app_facts in Pthr1.
    (first [ pose proof ((C0 c' Hc')) as dR_65; dand5 dR_65 as LEN X1 X2 X3 X4 | destruct (C0 c' Hc') as (LEN & X1 & X2 & X3 & X4) ]). split; [exact LEN|].
    split; [leaf X1 ltac:(apply AGe; offs; lia)|]. split; [|split].
    - destruct (a_cache_inited A && negb (c' =? 0)); destruct X2 as [Y1 Y2]; split; first [leaf Y1 ltac:(apply AGe; offs; lia) | leaf Y2 ltac:(apply AGe; offs; lia)].
    - intros i k E. pose proof (X3 i k E) as L.
      assert (Z.of_nat i < Z.of_nat (length (pk_chunks (a_cache A c')))) by (pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite E; discriminate)); lia).
      leaf L ltac:(apply AGe; offs; lia).
    - apply junk_N; [clear - Pthr1 Hc' LEN; kung_all; offs; lia| clear - Pthr1 Hc' LEN; kung_all; offs; lia| exact X4].
  Qed.

  (* [comment removed for export] *)
  Lemma cache_P : forall (cache : Z -> pcache),
    (forall c', 0 <= c' < 32 ->
      let e := thr + off_th_per_class c' in let ks := pk_chunks (cache c') in
      Z.of_nat (length ks) <= 16 /\
      u32_at rsegs v' (e + off_pc_count) (Z.of_nat (length ks)) /\
      (if a_cache_inited A && negb (c' =? 0) then u32_at rsegs v' (e + off_pc_max_count) (max_count c') /\ u64_at rsegs v' (e + off_pc_class_size) (class_size c')
       else u32_at rsegs v' (e + off_pc_max_count) 0 /\ u64_at rsegs v' (e + off_pc_class_size) 0) /\
      (forall i k, nth_error ks i = Some k -> u32_at rsegs v' (e + off_pc_chunk (Z.of_nat i)) (k * class_size c' / kCompactPtrScale)) /\
      junk_at rsegs v' (e + off_pc_chunk (Z.of_nat (length ks))) (4 * (16 - Z.of_nat (length ks)))) ->
    cache_repr_ LPA (a_pl A) cache (a_cache_inited A) v'.
  Proof.
    intros cache LINES. (first [ pose proof ((ar_cache _ _ _ _ _ R)) as dR_66; dand5 dR_66 as _ J1 J2 M1 M2 | pose proof (ar_cache _ _ _ _ _ R) as (_ & J1 & J2 & M1 & M2) ]). pose proof alloc_ceiling_val as CE.
    (first [ pose proof ((place_factsT A WF0)) as dR_67; dand3 dR_67 as Pthr Pctx _ | pose proof (place_factsT A WF0) as (Pthr & Pctx & _) ]). cbv zeta in Pthr, Pctx.
    (first [ dand3 Pthr as Pthr1 Pthr2 Pthr3 | destruct Pthr as (Pthr1 & Pthr2 & Pthr3) ]). apply app_facts in Pthr1. (first [ dand3 Pctx as Pctx1 Pctx2 Pctx3 | destruct Pctx as (Pctx1 & Pctx2 & Pctx3) ]). apply app_facts in Pctx1.
    unfold cache_repr_. cbv zeta. split; [exact LINES|].
    split; [apply junk_N; [clear - Pthr1; offs; lia| clear - Pthr1; kung_all; offs; lia| exact J1]
          | split; [apply junk_N; [clear - Pthr1; offs; lia| clear - Pthr1; kung_all; offs; lia| exact J2]
          | split; apply mapped_N; try assumption; clear - Pthr1 Pthr2 Pctx1 Pctx2 CE; kung_all; lia]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition known (ch : chunk) (n1 : Z) : Prop :=
    match ch with ChP (CP c' k') => 1 <= c' <= 30 /\ 0 <= k' < carved_count A c' /\ 0 <= n1 <= kMaxPrimaryUser /\ c' = class_of n1
             | ChS (CS mb n0') => In (CS mb n0') (sr_chunks (a_sec A)) /\ kMaxPrimaryUser < n1 /\ n0' = n1 end.

  Lemma known_live : forall u li, a_livemap A !! u = Some li -> known (li_chunk li) (li_n li).
  Proof.
    intros u li Hl. destruct (wtV A WF0) as (V1 & _). (first [ pose proof ((V1 u li Hl)) as dR_70; dand3 dR_70 as N U C | pose proof (V1 u li Hl) as (N & U & C) ]). cbv zeta in C. unfold known.
    destruct (li_chunk li) as [[c' k']|[mb n0']].
    - (first [ dand3 C as N2 Hc Hk | destruct C as (N2 & Hc & Hk) ]). pose proof (class_of_range (li_n li) ltac:(lia)). rewrite <- Hc in *. unfold carved_count. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia; assumption.
    - (first [ dand3 C as N2 -> Hin | destruct C as (N2 & -> & Hin) ]). OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; [exact Hin| exact N2].
  Qed.

  Lemma qentry_wf : forall e, In e (q_entries (a_qthread A ++ QGL)) -> wf_qentry_ (a_reg A) (a_sec A) e.
  Proof.
    intros e He. (first [ pose proof ((wtQ A WF0)) as dR_73; dand3 dR_73 as Q1 Q2 _ | destruct (wtQ A WF0) as (Q1 & Q2 & _) ]).
    unfold q_entries in He. apply in_flat_map in He as (b & Hb & Heb). apply in_app_iff in Hb as [Hb|Hb];
      [pose proof (proj1 (Forall_forall _ _) Q1 b Hb) as WB| pose proof (proj1 (Forall_forall _ _) Q2 b Hb) as WB];
      (first [ dand3 WB as _ _ WB | destruct WB as (_ & _ & WB) ]); exact (proj1 (Forall_forall _ _) WB _ Heb).
  Qed.

  Lemma known_quar : forall e, In e (q_entries (a_qthread A ++ QGL)) -> known (qe_chunk e) (qe_n e).
  Proof.
    intros e He. destruct (qentry_wf e He) as (N & C). unfold known. destruct e as [ch n1]. cbn [qe_chunk qe_n] in *.
    destruct ch as [[c' k']|[mb n0']].
    - (first [ dand3 C as N2 Hc Hk | destruct C as (N2 & Hc & Hk) ]). pose proof (class_of_range n1 ltac:(lia)). rewrite <- Hc in *. unfold carved_count. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia; assumption.
    - (first [ dand3 C as N2 -> Hin | destruct C as (N2 & -> & Hin) ]). OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; [exact Hin| exact N2].
  Qed.

  (* [comment removed for export] *)
  Lemma known_range : forall ch n1, known ch n1 -> 0x60a000 <= chunk_lo sb ch /\ chunk_hi sb ch <= alloc_ceiling.
  Proof.
    intros ch n1 CL. unfold known in CL. destruct ch as [[c' k']|[mb n0']].
    - (first [ dand3 CL as Hc Hk _ | destruct CL as (Hc & Hk & _) ]). (first [ pose proof ((carved_chunk_boundsT A c' k' WF0 Hc Hk)) as dR_78; dand3 dR_78 as B1 B2 _ | pose proof (carved_chunk_boundsT A c' k' WF0 Hc Hk) as (B1 & B2 & _) ]). pose proof (region_piece_boundsT A c' WF0 Hc) as RB. cbv zeta in *.
      cbn [chunk_lo chunk_hi alloc_beg]. kung_all. lia.
    - destruct CL as (Hin & _). (first [ pose proof ((sec_chunk_boundsT A _ WF0 Hin)) as dR_79; dand5 dR_79 as B1 _ B3 B4 B5 | pose proof (sec_chunk_boundsT A _ WF0 Hin) as (B1 & _ & B3 & B4 & B5) ]). cbn [chunk_lo chunk_hi cs_map cs_n] in *.
      apply app_facts in B3. pose proof (needed_size_ge n0'). rewrite needed_size2_secondary in B5 by lia. pose proof (rounded_size_ge n0').
      unfold kMaxPrimaryUser, kPageSize, kSecondaryHeaderSize in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma batch_known : forall b, In b (a_qthread A ++ QGL) -> 0 <= ba_idx b < carved_count A kQuarantineBatchClass /\ Z.of_nat (length (ba_entries b)) <= kQuarantineBatchCount.
  Proof.
    intros b Hb. (first [ pose proof ((wtQ A WF0)) as dR_80; dand3 dR_80 as Q1 Q2 _ | destruct (wtQ A WF0) as (Q1 & Q2 & _) ]).
    assert (WB : wf_batch0T_ (a_reg A) (a_sec A) b).
    { apply in_app_iff in Hb as [Hb|Hb]; [exact (proj1 (Forall_forall _ _) Q1 b Hb)| exact (proj1 (Forall_forall _ _) Q2 b Hb)]. }
    (first [ dand3 WB as LEN Hk _ | destruct WB as (LEN & Hk & _) ]). split; [exact Hk| lia].
  Qed.

  Lemma batch_range : forall b, In b (a_qthread A ++ QGL) ->
    kHighMemBeg <= batch_addr sb b /\ batch_addr sb b + kQuarantineBatchBytes <= alloc_ceiling /\ batch_addr sb b mod 32 = 0.
  Proof.
    intros b Hb. destruct (batch_known b Hb) as [Hk _].
    assert (C24 : 1 <= kQuarantineBatchClass <= 30) by (unfold kQuarantineBatchClass; lia).
    (first [ pose proof ((carved_chunk_boundsT A _ _ WF0 C24 Hk)) as dR_82; dand4 dR_82 as B1 B2 B3 _ | pose proof (carved_chunk_boundsT A _ _ WF0 C24 Hk) as (B1 & B2 & B3 & _) ]). pose proof (region_piece_boundsT A _ WF0 C24) as RB. cbv zeta in *.
    unfold batch_addr. rewrite <- class_size_24. unfold kQuarantineBatchClass in *. kung_all. lia.
  Qed.

  Lemma batch_idx_range : forall k, In k (batch_indices_ (a_qthread A) QGL) -> 0 <= k < carved_count A kQuarantineBatchClass.
  Proof. intros k Hk. unfold batch_indices_ in Hk. apply in_map_iff in Hk as (b & <- & Hb). exact (proj1 (batch_known b Hb)). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition carved (ch : chunk) : Prop :=
    match ch with ChP (CP c' k') => 1 <= c' <= 30 /\ 0 <= k' < carved_count A c' | ChS s => In s (sr_chunks (a_sec A)) end.
  Lemma known_carved : forall ch n1, known ch n1 -> carved ch.
  Proof. intros ch n1 K. unfold known, carved in *. destruct ch as [[c' k']|[mb n0']]; tauto. Qed.
  Lemma batch_carved : forall b, In b (a_qthread A ++ QGL) -> carved (ChP (CP kQuarantineBatchClass (ba_idx b))).
  Proof. intros b Hb. unfold carved. split; [unfold kQuarantineBatchClass; lia| exact (proj1 (batch_known b Hb))]. Qed.
  Lemma cached_carved : forall c' k, 1 <= c' <= 30 -> p_cached_ (a_cache A) c' k -> carved (ChP (CP c' k)).
  Proof. intros c' k Hc C. unfold carved. split; [exact Hc|]. (first [ pose proof ((wtC A WF0)) as dR_83; dand3 dR_83 as WC _ _ | destruct (wtC A WF0) as (WC & _ & _) ]). (first [ pose proof ((WC c' ltac:(lia))) as dR_84; dand4 dR_84 as _ _ CR' _ | destruct (WC c' ltac:(lia)) as (_ & _ & CR' & _) ]). exact (CR' k C). Qed.
  Lemma free_carved : forall c' k, 1 <= c' <= 30 -> p_free_ (a_reg A) c' k -> carved (ChP (CP c' k)).
  Proof. intros c' k Hc F. unfold carved. split; [exact Hc|]. (first [ pose proof ((wtR A WF0)) as dR_85; dand3 dR_85 as WR _ _ | destruct (wtR A WF0) as (WR & _ & _) ]). (first [ pose proof ((WR c' Hc)) as dR_86; dand10 dR_86 as _ _ _ _ _ _ _ _ FR _ | destruct (WR c' Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & FR & _) ]). exact (FR k F). Qed.

  (* [comment removed for export] *)
  Lemma carved_prim_where : forall c' k, carved (ChP (CP c' k)) ->
    region_beg sb c' <= chunk_addr sb c' k /\ chunk_addr sb c' k + class_size c' <= region_beg sb c' + rg_allocated_user (a_reg A c') /\
    rg_allocated_user (a_reg A c') <= rg_mapped_user (a_reg A c') /\ region_beg sb c' + rg_mapped_user (a_reg A c') <= region_beg sb c' + kFreeArrayOffset /\
    region_beg sb c' + kRegionSize <= a_sb A + kSpaceSize /\ a_sb A <= region_beg sb c' /\
    a_b6 A <= a_sb A /\ a_sb A + kSpaceSize + 4096 <= a_b6 A + kSpaceReserve /\
    kHighMemBeg <= a_b6 A /\ a_sb A + kSpaceSize + 4096 <= alloc_ceiling /\ 32 <= class_size c'.
  Proof.
    intros c' k [Hc Hk]. (first [ pose proof ((carved_chunk_boundsT A c' k WF0 Hc Hk)) as dR_87; dand4 dR_87 as B1 B2 _ B4 | pose proof (carved_chunk_boundsT A c' k WF0 Hc Hk) as (B1 & B2 & _ & B4) ]). pose proof (region_piece_boundsT A c' WF0 Hc) as RB. cbv zeta in *.
    (first [ pose proof ((sb_factsT A WF0)) as dR_88; dand5 dR_88 as _ _ HB6 RSB SCE | pose proof (sb_factsT A WF0) as (_ & _ & HB6 & RSB & SCE) ]). change (a_sb A) with sb in *. unfold kSpaceReserve, kSpaceSize in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma carved_range : forall ch, carved ch -> 0x60a000 <= chunk_lo sb ch /\ chunk_hi sb ch <= alloc_ceiling /\ chunk_lo sb ch < chunk_hi sb ch.
  Proof.
    intros ch C. destruct ch as [[c' k']|[mb n0']].
    - pose proof (carved_prim_where c' k' C) as W. cbn [chunk_lo chunk_hi alloc_beg]. change (a_sb A) with sb in W. kung_all. lia.
    - unfold carved in C. (first [ pose proof ((sec_chunk_boundsT A _ WF0 C)) as dR_89; dand5 dR_89 as B1 _ B3 B4 B5 | pose proof (sec_chunk_boundsT A _ WF0 C) as (B1 & _ & B3 & B4 & B5) ]). cbn [chunk_lo chunk_hi cs_map cs_n] in *.
      apply app_facts in B3. pose proof (needed_size_ge n0').
      pose proof (needed_size2_secondary n0' ltac:(lia)). pose proof (rounded_size_ge n0'). unfold kMaxPrimaryUser, kPageSize in *. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma carved_app : forall ch, carved ch -> app_rangeA AL_pboth (chunk_lo sb ch) (chunk_hi sb ch - chunk_lo sb ch).
  Proof.
    intros ch C. destruct ch as [[c' k']|[mb n0']].
    - pose proof (carved_prim_where c' k' C) as W. cbn [chunk_lo chunk_hi alloc_beg]. change (a_sb A) with sb in W.
      apply app_rangeA_hi; kung_all; lia.
    - unfold carved in C. (first [ pose proof ((sec_chunk_boundsT A _ WF0 C)) as dR_90; dand5 dR_90 as B1 _ B3 B4 B5 | pose proof (sec_chunk_boundsT A _ WF0 C) as (B1 & _ & B3 & B4 & B5) ]). cbn [chunk_lo chunk_hi cs_map cs_n] in *.
      replace (mb + map_size n0' - mb) with (map_size n0') by lia. exact B3.
  Qed.

  (* [comment removed for export] *)
  Lemma carved_apart_bm : forall ch i bi si, carved ch -> nth_error (big_maps A) i = Some (bi, si) ->
    (forall p', ch = ChP p' -> i <> 0%nat) ->
    (forall j s, ch = ChS s -> nth_error (sr_chunks (a_sec A)) j = Some s -> i <> (15 + j)%nat) ->
    chunk_hi sb ch <= bi \/ bi + si <= chunk_lo sb ch.
  Proof.
    intros ch i bi si C Hi NP NS. destruct ch as [[c' k']|s].
    - pose proof (carved_prim_where c' k' C) as W. pose proof (proj1 (bm_nth_fixed A)) as E0. change (a_sb A) with sb in W.
      destruct (bm_sepT A 0%nat i _ _ _ _ WF0 E0 Hi ltac:(intros E; exact (NP _ eq_refl (eq_sym E)))) as [D|D]; cbn [chunk_lo chunk_hi alloc_beg]; [left| right]; kung_all; lia.
    - unfold carved in C. destruct (In_nth_error' _ _ C) as [j Hj]. pose proof (bm_nth_sec A j s Hj) as Ej.
      destruct (bm_sepT A (15 + j)%nat i _ _ _ _ WF0 Ej Hi ltac:(intros E; exact (NS j s eq_refl Hj (eq_sym E)))) as [D|D];
        destruct s as [mb n1]; cbn [chunk_lo chunk_hi cs_map cs_n] in *; [left| right]; lia.
  Qed.

  Lemma carved_apart_thr : forall ch, carved ch -> chunk_hi sb ch <= thr \/ thr + 4096 <= chunk_lo sb ch.
  Proof. intros ch C. apply (carved_apart_bm ch 4%nat); [exact C| reflexivity| intros; lia| intros; lia]. Qed.
  Lemma carved_apart_ctx : forall ch, carved ch -> chunk_hi sb ch <= p_ctx (a_pl A) \/ p_ctx (a_pl A) + 0x10000 <= chunk_lo sb ch.
  Proof. intros ch C. apply (carved_apart_bm ch 5%nat); [exact C| reflexivity| intros; lia| intros; lia]. Qed.
  Lemma carved_apart_fs : forall ch, carved ch -> chunk_hi sb ch <= p_fs (a_pl A) \/ p_fs (a_pl A) + kFakeStackBytes <= chunk_lo sb ch.
  Proof. intros ch C. apply (carved_apart_bm ch 6%nat); [exact C| reflexivity| intros; lia| intros; lia]. Qed.
  Lemma carved_apart_n0 : forall ch, carved ch -> chunk_hi sb ch <= p_nodes0 (a_pl A) \/ p_nodes0 (a_pl A) + kDepotNodesBlock <= chunk_lo sb ch.
  Proof. intros ch C. apply (carved_apart_bm ch 7%nat); [exact C| reflexivity| intros; lia| intros; lia]. Qed.
  Lemma carved_apart_f0 : forall ch, carved ch -> chunk_hi sb ch <= p_frames0 (a_pl A) \/ p_frames0 (a_pl A) + kStackStoreBlockBytes <= chunk_lo sb ch.
  Proof. intros ch C. apply (carved_apart_bm ch 8%nat); [exact C| reflexivity| intros; lia| intros; lia]. Qed.
  (* [comment removed for export] *)
  Lemma carved_apart_pa : forall ch, carved ch -> chunk_hi sb ch <= p_pa (a_pl A) \/ p_pa (a_pl A) + kPtrArrayReserve <= chunk_lo sb ch.
  Proof. intros ch C. apply (carved_apart_bm ch 1%nat); [exact C| reflexivity| intros; lia| intros; lia]. Qed.

  (* [comment removed for export] *)
  Lemma sec_apart_b6 : forall s, In s (sr_chunks (a_sec A)) -> cs_map s + map_size (cs_n s) <= a_b6 A \/ a_b6 A + kSpaceReserve <= cs_map s.
  Proof.
    intros s Hin. destruct (carved_apart_bm (ChS s) 0%nat (a_b6 A) kSpaceReserve Hin (proj1 (bm_nth_fixed A)) ltac:(intros p' E; discriminate) ltac:(intros; lia)) as [D|D];
      destruct s as [mb n1]; cbn [chunk_lo chunk_hi cs_map cs_n] in *; [left| right]; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma carved_apart_fa : forall ch c'', carved ch -> 1 <= c'' <= 30 ->
    chunk_hi sb ch <= free_array_beg sb c'' \/ free_array_beg sb c'' + rg_mapped_fa (a_reg A c'') <= chunk_lo sb ch.
  Proof.
    intros ch c'' C Hc''. (first [ pose proof ((sb_factsT A WF0)) as dR_92; dand5 dR_92 as _ _ HB6 RSB SCE | pose proof (sb_factsT A WF0) as (_ & _ & HB6 & RSB & SCE) ]). pose proof (region_piece_boundsT A c'' WF0 Hc'') as RB''. cbv zeta in RB''.
    change (a_sb A) with sb in *. unfold free_array_beg. destruct ch as [[c' k']|s].
    - pose proof (carved_prim_where c' k' C) as W. destruct C as [Hc' _]. change (a_sb A) with sb in *. cbn [chunk_lo chunk_hi alloc_beg].
      destruct (Z.eq_dec c' c'') as [->|NC]; [left; lia|]. destruct (regions_disjoint sb c' c'' NC ltac:(lia) ltac:(lia)); [left| right]; kung_all; lia.
    - unfold carved in C. destruct (sec_apart_b6 s C) as [D|D]; destruct s as [mb n1]; cbn [chunk_lo chunk_hi cs_map cs_n] in *;
        unfold a_b6, a_sb in *; [left| right]; kung_all; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma carved_disjoint : forall ch1 ch2, carved ch1 -> carved ch2 -> ch1 <> ch2 ->
    chunk_hi sb ch1 <= chunk_lo sb ch2 \/ chunk_hi sb ch2 <= chunk_lo sb ch1.
  Proof.
    intros ch1 ch2 C1 C2 NE. destruct ch1 as [[c1 k1]|s1]; destruct ch2 as [[c2 k2]|s2].
    - destruct C1 as [H1 K1]. destruct C2 as [H2 K2]. cbn [chunk_lo chunk_hi alloc_beg].
      destruct (Z.eq_dec c1 c2) as [->|NC].
      + assert (NK : k1 <> k2) by (intros ->; apply NE; reflexivity). exact (carved_chunks_disjoint sb c2 k1 k2 H2 ltac:(lia) ltac:(lia) NK).
      + pose proof (carved_prim_where c1 k1 (conj H1 K1)) as W1. pose proof (carved_prim_where c2 k2 (conj H2 K2)) as W2. change (a_sb A) with sb in *.
        destruct (regions_disjoint sb c1 c2 NC ltac:(lia) ltac:(lia)); [left| right]; kung_all; lia.
    - unfold carved in C2. destruct (In_nth_error' _ _ C2) as [j Hj].
      destruct (carved_apart_bm (ChP (CP c1 k1)) (15 + j)%nat _ _ C1 (bm_nth_sec A j s2 Hj) ltac:(intros; lia) ltac:(intros j0 s0 E; discriminate)) as [D|D];
        destruct s2 as [mb n1]; cbn [chunk_lo chunk_hi cs_map cs_n] in *; [left| right]; lia.
    - unfold carved in C1. destruct (In_nth_error' _ _ C1) as [j Hj].
      destruct (carved_apart_bm (ChP (CP c2 k2)) (15 + j)%nat _ _ C2 (bm_nth_sec A j s1 Hj) ltac:(intros; lia) ltac:(intros j0 s0 E; discriminate)) as [D|D];
        destruct s1 as [mb n1]; cbn [chunk_lo chunk_hi cs_map cs_n] in *; [right| left]; lia.
    - unfold carved in C1, C2. destruct (In_nth_error' _ _ C1) as [j1 Hj1]. destruct (In_nth_error' _ _ C2) as [j2 Hj2].
      assert (NJ : j1 <> j2) by (intros ->; rewrite Hj1 in Hj2; injection Hj2 as ->; apply NE; reflexivity).
      destruct (bm_sepT A (15 + j1)%nat (15 + j2)%nat _ _ _ _ WF0 (bm_nth_sec A j1 s1 Hj1) (bm_nth_sec A j2 s2 Hj2) ltac:(lia)) as [D|D];
        destruct s1 as [mb1 n1]; destruct s2 as [mb2 n2]; cbn [chunk_lo chunk_hi cs_map cs_n] in *; [left| right]; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma live_not_quar_chunk : forall u li e, a_livemap A !! u = Some li -> In e (q_entries (a_qthread A ++ QGL)) -> li_chunk li <> qe_chunk e.
  Proof.
    intros u li e Hl He E. (first [ pose proof ((wtQ A WF0)) as dR_93; dand8 dR_93 as _ _ _ _ _ _ _ NLQ | destruct (wtQ A WF0) as (_ & _ & _ & _ & _ & _ & _ & NLQ) ]). apply (NLQ u li Hl).
    unfold quarantined_chunks_. rewrite E. apply in_map. exact He.
  Qed.
  Lemma live_not_batch : forall u li b, a_livemap A !! u = Some li -> In b (a_qthread A ++ QGL) -> li_chunk li <> ChP (CP kQuarantineBatchClass (ba_idx b)).
  Proof.
    intros u li b Hl Hb E. pose proof (batch_known b Hb) as [Hk _].
    pose proof (wtX A WF0 kQuarantineBatchClass (ba_idx b) ltac:(unfold kQuarantineBatchClass; lia) Hk) as X. cbv zeta in X.
    (first [ dand11 X as _ _ _ _ _ _ _ _ _ NVB _ | destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & NVB & _) ]). apply NVB. split.
    - exists u, (li_n li). rewrite <- E. destruct li; exact Hl.
    - split; [reflexivity|]. unfold batch_indices_. apply in_map. exact Hb.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma quar_not_batch : forall e b, In e (q_entries (a_qthread A ++ QGL)) -> In b (a_qthread A ++ QGL) -> qe_chunk e <> ChP (CP kQuarantineBatchClass (ba_idx b)).
  Proof.
    intros e b He Hb E. pose proof (batch_known b Hb) as [Hk _].
    pose proof (wtX A WF0 kQuarantineBatchClass (ba_idx b) ltac:(unfold kQuarantineBatchClass; lia) Hk) as X. cbv zeta in X.
    (first [ dand11 X as _ _ _ _ _ _ _ _ _ _ NQB | destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NQB) ]). apply NQB. split.
    - exists (qe_n e). rewrite <- E. destruct e; exact He.
    - split; [reflexivity|]. unfold batch_indices_. apply in_map. exact Hb.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma batches_nodup : NoDup (map ba_idx (a_qthread A ++ QGL)).
  Proof. (first [ pose proof ((wtQ A WF0)) as dR_101; dand7 dR_101 as _ _ _ _ _ ND _ | destruct (wtQ A WF0) as (_ & _ & _ & _ & _ & ND & _) ]). exact ND. Qed.

  (* [comment removed for export] *)
  Lemma thr_owned : forall a, thr <= a < thr + 4096 -> pa_owned A a.
  Proof.
    intros a Ha. (first [ pose proof ((bm_nth_fixed A)) as dR_102; dand6 dR_102 as _ _ _ _ E4 _ | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & E4 & _) ]).
    apply (owned_rt A a thr 4096); [apply rt_fixed_in; cbn; tauto| exact Ha
      | eapply (fixed_bm_no_live_userT A 4); [exact WF0| lia| exact E4| exact Ha]
      | eapply (fixed_bm_no_live_frameT A 4); [exact WF0| lia| lia| exact E4| exact Ha]].
  Qed.
  Lemma n0_owned : forall a, p_nodes0 (a_pl A) <= a < p_nodes0 (a_pl A) + kDepotNodesBlock -> pa_owned A a.
  Proof.
    intros a Ha. (first [ pose proof ((bm_nth_fixed A)) as dR_103; dand9 dR_103 as _ _ _ _ _ _ _ E7 _ | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & _ & _ & _ & E7 & _) ]).
    apply (owned_rt A a (p_nodes0 (a_pl A)) kDepotNodesBlock); [apply rt_fixed_in; cbn; tauto| exact Ha
      | eapply (fixed_bm_no_live_userT A 7); [exact WF0| lia| exact E7| exact Ha]
      | eapply (fixed_bm_no_live_frameT A 7); [exact WF0| lia| lia| exact E7| exact Ha]].
  Qed.
  Lemma f0_owned : forall a, p_frames0 (a_pl A) <= a < p_frames0 (a_pl A) + kStackStoreBlockBytes -> pa_owned A a.
  Proof.
    intros a Ha. (first [ pose proof ((bm_nth_fixed A)) as dR_104; dand10 dR_104 as _ _ _ _ _ _ _ _ E8 _ | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & _ & _ & _ & _ & E8 & _) ]).
    apply (owned_rt A a (p_frames0 (a_pl A)) kStackStoreBlockBytes); [apply rt_fixed_in; cbn; tauto| exact Ha
      | eapply (fixed_bm_no_live_userT A 8); [exact WF0| lia| exact E8| exact Ha]
      | eapply (fixed_bm_no_live_frameT A 8); [exact WF0| lia| lia| exact E8| exact Ha]].
  Qed.
  Lemma dstat_owned : forall a, 0x186a88 <= a < 0x5d6aa8 -> pa_owned A a.
  Proof. intros a Ha. apply asI_static_owned. cbn [cl_static LPA]. apply depot_static. cbn. unfold kDepotNodesL1. lia. Qed.

  (* [comment removed for export] *)
  Lemma hdr_foot_in : forall ch n1 a, known ch n1 ->
    hdr_foot sb ch n1 a \/ (user_of sb ch n1 <= a < user_of sb ch n1 + 8) -> chunk_lo sb ch <= a < chunk_hi sb ch.
  Proof.
    intros ch n1 a CL Ha. unfold known in CL. unfold hdr_foot in Ha. destruct ch as [[c' k']|[mb n0']].
    - (first [ dand4 CL as Hc Hk Hn Hcl | destruct CL as (Hc & Hk & Hn & Hcl) ]). (first [ pose proof ((primary_layout sb c' k' n1 Hc Hn Hcl)) as dR_106; dand5 dR_106 as L1 L2 L3 L5 L4 | pose proof (primary_layout sb c' k' n1 Hc Hn Hcl) as (L1 & L2 & L3 & L5 & L4) ]). cbv zeta in *.
      cbn [chunk_lo chunk_hi alloc_beg user_of] in *. lia.
    - (first [ dand3 CL as Hin Hn -> | destruct CL as (Hin & Hn & ->) ]). (first [ pose proof ((secondary_layout mb n1 Hn)) as dR_108; dand7 dR_108 as S1 S2 S3 S4 S5 S6 S7 | pose proof (secondary_layout mb n1 Hn) as (S1 & S2 & S3 & S4 & S5 & S6 & S7) ]).
      cbn [chunk_lo chunk_hi alloc_beg user_of cs_map cs_n] in *. unfold kSecondaryHeaderSize in *. lia.
  Qed.

  Lemma user_in : forall ch n1, known ch n1 -> chunk_lo sb ch <= user_of sb ch n1 /\ user_of sb ch n1 + n1 <= chunk_hi sb ch.
  Proof.
    intros ch n1 CL. unfold known in CL. destruct ch as [[c' k']|[mb n0']].
    - (first [ dand4 CL as Hc Hk Hn Hcl | destruct CL as (Hc & Hk & Hn & Hcl) ]). (first [ pose proof ((primary_layout sb c' k' n1 Hc Hn Hcl)) as dR_110; dand3 dR_110 as L1 L2 _ | pose proof (primary_layout sb c' k' n1 Hc Hn Hcl) as (L1 & L2 & _) ]). cbv zeta in *. cbn [chunk_lo chunk_hi alloc_beg user_of] in *. lia.
    - (first [ dand3 CL as Hin Hn -> | destruct CL as (Hin & Hn & ->) ]). (first [ pose proof ((secondary_layout mb n1 Hn)) as dR_112; dand4 dR_112 as S1 S2 S3 _ | pose proof (secondary_layout mb n1 Hn) as (S1 & S2 & S3 & _) ]). cbn [chunk_lo chunk_hi alloc_beg user_of cs_map cs_n] in *. unfold kSecondaryHeaderSize in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma live_user_in_carved : forall ch a u li, carved ch -> chunk_lo sb ch <= a < chunk_hi sb ch ->
    a_livemap A !! u = Some li -> u <= a < u + li_n li -> li_chunk li = ch.
  Proof.
    intros ch a u li C Ha Hl Hu. pose proof (known_carved _ _ (known_live u li Hl)) as C'.
    destruct (chunk_eq_dec (li_chunk li) ch) as [E|NE]; [exact E|]. exfalso.
    pose proof (user_in _ _ (known_live u li Hl)) as UR. destruct (wtV A WF0) as (V1 & _). (first [ pose proof ((V1 u li Hl)) as dR_113; dand3 dR_113 as _ U _ | pose proof (V1 u li Hl) as (_ & U & _) ]). rewrite <- U in UR.
    destruct (carved_disjoint _ _ C' C NE); lia.
  Qed.

  (* [comment removed for export] *)
  Lemma carved_in_rt : forall ch a, carved ch -> chunk_lo sb ch <= a < chunk_hi sb ch ->
    in_regions (runtime_maps A) a /\ ~ in_live_frame A a.
  Proof.
    intros ch a C Ha. destruct ch as [[c' k']|s].
    - pose proof (carved_prim_where c' k' C) as W. destruct C as [Hc Hk]. cbn [chunk_lo chunk_hi alloc_beg] in Ha. change (a_sb A) with sb in W.
      split.
      + exists (region_beg sb c'), (rg_mapped_user (a_reg A c')). split; [exact (proj1 (rt_class_in A c' Hc))| lia].
      + apply b6_no_live_frameT; [exact WF0|]. kung_all. lia.
    - unfold carved in C. destruct (In_nth_error' _ _ C) as [i Hi]. destruct s as [mb n1]. cbn [chunk_lo chunk_hi cs_map cs_n] in Ha.
      split; [exists mb, (map_size n1); split; [exact (rt_sec_in A _ C)| exact Ha]|]. exact (sec_no_live_frameT A i _ a WF0 Hi Ha).
  Qed.

  (* [comment removed for export] *)
  Lemma carved_owned : forall ch a, carved ch -> chunk_lo sb ch <= a < chunk_hi sb ch ->
    (forall u li, a_livemap A !! u = Some li -> li_chunk li = ch -> ~ (u <= a < u + li_n li)) -> pa_owned A a.
  Proof.
    intros ch a C Ha NU. destruct (carved_in_rt ch a C Ha) as [(b & s & Hin & Hb) NF].
    apply (owned_rt A a b s Hin Hb); [| exact NF].
    ((first [ intro dR_165; dex2 dR_165 as u li; destruct dR_165 as [Hl Hu] | intro dR_165; dand4 dR_165 as u li Hl Hu | intros (u & li & Hl & Hu) ])). exact (NU u li Hl (live_user_in_carved ch a u li C Ha Hl Hu) Hu).
  Qed.


  (* [comment removed for export] *)
  Lemma hdr_P : forall ch n1 st, (forall a, hdr_foot sb ch n1 a -> v' (wz a) = v (wz a)) ->
    hdr_repr_ LPA sb v ch n1 st -> hdr_repr_ LPA sb v' ch n1 st.
  Proof.
    intros ch n1 st AG [(id0 & b1 & Hid & Hb1 & Hb1m & RC) LH]. split.
    - exists id0, b1. split; [exact Hid|]. split; [exact Hb1|]. split; [exact Hb1m|].
      eapply rw_cells_agree; [exact RC|]. rewrite chunk_hdr_size. intros i Hi. apply AG. unfold hdr_foot. left. lia.
    - intros NE16. destruct (LH NE16) as [X Y]. split; [leaf X ltac:(apply AG; unfold hdr_foot; right; lia) | leaf Y ltac:(apply AG; unfold hdr_foot; right; lia)].
  Qed.

  (* [comment removed for export] *)
  Lemma live_entry_P : forall u li, a_livemap A !! u = Some li ->
    (forall a, chunk_lo sb (li_chunk li) <= a < chunk_hi sb (li_chunk li) -> v' (wz a) = v (wz a)) ->
    hdr_repr_ LPA sb v' (li_chunk li) (li_n li) CHUNK_ALLOCATED /\
    mapped v' u (li_n li) /\ mapped v' (chunk_lo sb (li_chunk li)) (chunk_hi sb (li_chunk li) - chunk_lo sb (li_chunk li)).
  Proof.
    intros u li Hl AG. (first [ pose proof ((ar_live _ _ _ _ _ R u li Hl)) as dR_114; dand3 dR_114 as HR MU0 MC | destruct (ar_live _ _ _ _ _ R u li Hl) as (HR & MU0 & MC) ]). pose proof alloc_ceiling_val as CE.
    pose proof (known_live u li Hl) as CL. pose proof (known_range _ _ CL) as RNG.
    destruct (wtV A WF0) as (V1 & _). (first [ pose proof ((V1 u li Hl)) as dR_115; dand3 dR_115 as N U _ | pose proof (V1 u li Hl) as (N & U & _) ]).
    pose proof (user_in _ _ CL) as UR. rewrite <- U in UR.
    split; [|split].
    - apply hdr_P; [| exact HR]. intros a Ha. apply AG. apply (hdr_foot_in _ (li_n li)); [exact CL| left; exact Ha].
    - apply mapped_N; [lia| right; lia| lia| exact MU0].
    - apply mapped_N; [lia| right; lia| lia| exact MC].
  Qed.

  (* [comment removed for export] *)
  Lemma live_sub_P : forall lm', (forall u li, lm' !! u = Some li -> a_livemap A !! u = Some li) ->
    (forall u li a, lm' !! u = Some li -> chunk_lo sb (li_chunk li) <= a < chunk_hi sb (li_chunk li) -> v' (wz a) = v (wz a)) ->
    live_repr_ LPA sb lm' v'.
  Proof. intros lm' SUB AG u li Hl. apply live_entry_P; [exact (SUB u li Hl)|]. intros a Ha. exact (AG u li a Hl Ha). Qed.

  (* [comment removed for export] *)
  Lemma quar_entry_P : forall e, In e (q_entries (a_qthread A ++ a_qglobal A)) ->
    (forall a, chunk_lo sb (qe_chunk e) <= a < chunk_hi sb (qe_chunk e) -> v' (wz a) = v (wz a)) ->
    hdr_repr_ LPA sb v' (qe_chunk e) (qe_n e) CHUNK_QUARANTINE /\
    junk_at rsegs v' (user_of sb (qe_chunk e) (qe_n e)) 8 /\
    mapped v' (chunk_lo sb (qe_chunk e)) (chunk_hi sb (qe_chunk e) - chunk_lo sb (qe_chunk e)).
  Proof.
    intros e He AG. (first [ pose proof ((ar_quar _ _ _ _ _ R)) as dR_116; dand3 dR_116 as _ _ QR | pose proof (ar_quar _ _ _ _ _ R) as (_ & _ & QR) ]). (first [ pose proof ((QR e He)) as dR_117; dand3 dR_117 as HR J MC | destruct (QR e He) as (HR & J & MC) ]). pose proof alloc_ceiling_val as CE.
    pose proof (known_quar e (q_in_big e He)) as CL. pose proof (known_range _ _ CL) as RNG.
    pose proof (hdr_foot_in (qe_chunk e) (qe_n e) (user_of sb (qe_chunk e) (qe_n e)) CL ltac:(right; lia)) as UR.
    split; [|split].
    - apply hdr_P; [| exact HR]. intros a Ha. apply AG. apply (hdr_foot_in _ (qe_n e)); [exact CL| left; exact Ha].
    - apply junk_N; [lia| right; lia| exact J].
    - apply mapped_N; [lia| right; lia| lia| exact MC].
  Qed.

  Lemma batches_P : forall bs, (forall b, In b bs -> In b (a_qthread A ++ QGL)) ->
    (forall b a, In b bs -> batch_addr sb b <= a < batch_addr sb b + kQuarantineBatchBytes -> v' (wz a) = v (wz a)) ->
    batches_repr LPA v sb bs -> batches_repr LPA v' sb bs.
  Proof.
    induction bs as [|b bs IH]; intros SUB AG BR; [exact I|]. pose proof alloc_ceiling_val as CE.
    cbn [batches_repr] in *. (first [ dand6 BR as X1 X2 X3 X4 M BR | destruct BR as (X1 & X2 & X3 & X4 & M & BR) ]).
    assert (INb : In b (a_qthread A ++ QGL)) by (apply SUB; left; reflexivity).
    destruct (batch_known b INb) as [Hk LEN]. (first [ pose proof ((batch_range b INb)) as dR_119; dand3 dR_119 as R1 R2 R3 | pose proof (batch_range b INb) as (R1 & R2 & R3) ]).
    assert (AGb : forall x, batch_addr sb b <= x < batch_addr sb b + kQuarantineBatchBytes -> v' (wz x) = v (wz x)).
    { intros x Hx. apply (AG b x); [left; reflexivity| exact Hx]. }
    split; [leaf X1 ltac:(apply AGb; offs; lia)|]. split; [leaf X2 ltac:(apply AGb; offs; lia)|]. split; [leaf X3 ltac:(apply AGb; offs; lia)|].
    split; [|split].
    - intros i e E. pose proof (X4 i e E) as L.
      assert (Z.of_nat i < Z.of_nat (length (ba_entries b))) by (pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite E; discriminate)); lia).
      leaf L ltac:(apply AGb; unfold kQuarantineBatchCount in *; offs; lia).
    - apply mapped_N; [| right| | exact M]; unfold kQuarantineBatchBytes in *; kung_all; lia.
    - apply IH; [| | exact BR]. { intros b' Hb'. apply SUB. right. exact Hb'. } { intros b' a Hb' Ha. apply (AG b' a); [right; exact Hb'| exact Ha]. }
  Qed.

  (* [comment removed for export] *)
  Lemma qcache_head_P : forall qc bs,
    (forall a, qc <= a < qc + 32 -> v' (wz a) = v (wz a)) ->
    u64_at rsegs v (qc + 0) (Z.of_nat (length bs)) /\
    u64_at rsegs v (qc + 8) (match bs with [] => 0 | b :: _ => batch_addr sb b end) /\
    u64_at rsegs v (qc + 16) (match bs with [] => 0 | _ => batch_addr sb (last bs (BA 0 [])) end) /\
    u64_at rsegs v (qc + 24) (q_bytes bs) ->
    u64_at rsegs v' (qc + 0) (Z.of_nat (length bs)) /\
    u64_at rsegs v' (qc + 8) (match bs with [] => 0 | b :: _ => batch_addr sb b end) /\
    u64_at rsegs v' (qc + 16) (match bs with [] => 0 | _ => batch_addr sb (last bs (BA 0 [])) end) /\
    u64_at rsegs v' (qc + 24) (q_bytes bs).
  Proof.
    (intros qc bs AG; (first [ intro dR_166; dand4 dR_166 as X1 X2 X3 X4 | intros (X1 & X2 & X3 & X4) ])).
    split; [leaf X1 ltac:(apply AG; lia)|]. split; [leaf X2 ltac:(apply AG; lia)|]. split; [leaf X3 ltac:(apply AG; lia)| leaf X4 ltac:(apply AG; lia)].
  Qed.

  (* [comment removed for export] *)
  Lemma quar_P :
    (forall a, thr + off_th_qcache <= a < thr + off_th_qcache + 32 -> v' (wz a) = v (wz a)) ->
    (forall a, al_instance AL_pboth + off_q_cache_list_size <= a < al_instance AL_pboth + off_q_cache_list_size + 32 -> v' (wz a) = v (wz a)) ->
    (forall b a, In b (a_qthread A ++ a_qglobal A) -> batch_addr sb b <= a < batch_addr sb b + kQuarantineBatchBytes -> v' (wz a) = v (wz a)) ->
    (forall e a, In e (q_entries (a_qthread A ++ a_qglobal A)) -> chunk_lo sb (qe_chunk e) <= a < chunk_hi sb (qe_chunk e) -> v' (wz a) = v (wz a)) ->
    quarantine_repr_ LPA AL_pboth (a_pl A) (a_qthread A) (a_qglobal A) v'.
  Proof.
    intros AGt AGg AGb AGe. (first [ pose proof ((ar_quar _ _ _ _ _ R)) as dR_120; dand3 dR_120 as QT QG QR | pose proof (ar_quar _ _ _ _ _ R) as (QT & QG & QR) ]). unfold quarantine_repr_. change (p_sb (a_pl A)) with sb in *.
    pose proof (place_factsT A WF0) as (Pthr & _). cbv zeta in Pthr. pose proof alloc_ceiling_val as CE.
    split; [|split].
    - (first [ dand5 QT as X1 X2 X3 X4 BR | destruct QT as (X1 & X2 & X3 & X4 & BR) ]). unfold qcache_repr.
      (first [ pose proof ((qcache_head_P (thr + off_th_qcache) (a_qthread A) AGt (conj X1 (conj X2 (conj X3 X4))))) as dR_122; dand4 dR_122 as Y1 Y2 Y3 Y4 | pose proof (qcache_head_P (thr + off_th_qcache) (a_qthread A) AGt (conj X1 (conj X2 (conj X3 X4)))) as (Y1 & Y2 & Y3 & Y4) ]).
      split; [exact Y1|]. split; [exact Y2|]. split; [exact Y3|]. split; [exact Y4|].
      apply batches_P; [intros b Hb; apply b_in_big; apply in_or_app; left; exact Hb| | exact BR]. intros b a Hb Ha. apply (AGb b a); [apply in_or_app; left; exact Hb| exact Ha].
    - (first [ dand5 QG as X1 X2 X3 X4 BR | destruct QG as (X1 & X2 & X3 & X4 & BR) ]). unfold qcache_repr.
      (first [ pose proof ((qcache_head_P (al_instance AL_pboth + off_q_cache_list_size) (a_qglobal A) AGg (conj X1 (conj X2 (conj X3 X4))))) as dR_124; dand4 dR_124 as Y1 Y2 Y3 Y4 | pose proof (qcache_head_P (al_instance AL_pboth + off_q_cache_list_size) (a_qglobal A) AGg (conj X1 (conj X2 (conj X3 X4)))) as (Y1 & Y2 & Y3 & Y4) ]).
      split; [exact Y1|]. split; [exact Y2|]. split; [exact Y3|]. split; [exact Y4|].
      apply batches_P; [intros b Hb; apply b_in_big; apply in_or_app; right; exact Hb| | exact BR]. intros b a Hb Ha. apply (AGb b a); [apply in_or_app; right; exact Hb| exact Ha].
    - intros e He. apply quar_entry_P; [exact He|]. intros a Ha. exact (AGe e a He Ha).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma depot_P : forall D' (md0 : mem),
    depot_rep AL_pboth rsegs D' (p_nodes0 (a_pl A)) (p_frames0 (a_pl A)) md0 ->
    (forall a, depot_foot AL_pboth (p_nodes0 (a_pl A)) (p_frames0 (a_pl A)) a -> v' (wz a) = md0 (wz a)) ->
    depot_repr_ LPA AL_pboth (a_pl A) D' v'.
  Proof. intros D' md0 HD AG. unfold depot_repr_. eapply depot_rep_agree; [exact HD| exact AG]. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma chunk_shadow : forall c' k, 1 <= c' <= 30 -> 0 <= k < carved_count A c' ->
    sh (chunk_addr sb c' k + class_size c') = sh (chunk_addr sb c' k) + class_size c' / 8 /\
    (forall z, sh (chunk_addr sb c' k) <= z < sh (chunk_addr sb c' k) + class_size c' / 8 -> heap_shadow A z) /\
    kHighShadowMapBeg <= sh (chunk_addr sb c' k) /\ sh (chunk_addr sb c' k + class_size c') <= sh alloc_ceiling.
  Proof.
    intros c' k Hc Hk. pose proof alloc_ceiling_val as CE.
    (first [ pose proof ((carved_chunk_boundsT A c' k WF0 Hc Hk)) as dR_125; dand4 dR_125 as B1 B2 B3 B4 | pose proof (carved_chunk_boundsT A c' k WF0 Hc Hk) as (B1 & B2 & B3 & B4) ]). pose proof (region_piece_boundsT A c' WF0 Hc) as RB. cbv zeta in *.
    change (a_sb A) with sb in *.
    (first [ dand12 RB as Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10 Q11 Q12 | destruct RB as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12) ]).
    pose proof (class_size_mod32 c' Hc) as CM. pose proof (class_size_range c' Hc) as CSR'.
    assert (ABM : chunk_addr sb c' k mod 8 = 0) by (apply (mod0_down _ 32 8); [exists 4; reflexivity| exact B3]).
    assert (CSM : class_size c' mod 8 = 0) by (apply (mod0_down _ 32 8); [exists 4; reflexivity| exact CM]).
    pose proof (sh_add (chunk_addr sb c' k) (class_size c') ABM CSM) as E.
    assert (RBM : region_beg sb c' mod 8 = 0) by (apply (mod0_down _ 0x10000 8); [exists 8192; reflexivity| exact Q9]).
    pose proof (sh_add (region_beg sb c') (rg_mapped_user (a_reg A c')) RBM Q10) as E2.
    pose proof (sh_mono (region_beg sb c') (chunk_addr sb c' k) ltac:(lia)) as M1.
    pose proof (sh_mono (chunk_addr sb c' k + class_size c') (region_beg sb c' + rg_mapped_user (a_reg A c')) ltac:(lia)) as M2.
    pose proof (sh_mono (chunk_addr sb c' k + class_size c') (@alloc_ceiling Clg) ltac:(lia)) as M3.
    pose proof (sh_high_range (chunk_addr sb c' k) ltac:(kung_all; lia)) as [HR _].
    split; [exact E|]. split; [| split; [exact HR| exact M3]].
    intros z Hz. unfold heap_shadow, heap_shadow_. left. exists c'. split; [exact Hc|]. cbv zeta. change (p_sb (a_pl A)) with sb. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma chunk_shadow_P : forall c' k bs, 1 <= c' <= 30 -> 0 <= k < carved_count A c' ->
    (forall z, sh (chunk_addr sb c' k) <= z < sh (chunk_addr sb c' k) + class_size c' / 8 -> v' (wz z) = v (wz z)) ->
    Z.of_nat (length bs) = class_size c' / 8 ->
    bytes_at rsegs v (sh (chunk_addr sb c' k)) bs -> bytes_at rsegs v' (sh (chunk_addr sb c' k)) bs.
  Proof. intros c' k bs Hc Hk AG L B. eapply bytes_at_agree_gen; [exact B|]. intros i Hi. apply AG. lia. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma sec_shadow : forall sc, In sc (sr_chunks (a_sec A)) ->
    sh (cs_map sc + map_size (cs_n sc)) = sh (cs_map sc) + map_size (cs_n sc) / 8 /\
    (forall z, sh (cs_map sc) <= z < sh (cs_map sc) + map_size (cs_n sc) / 8 -> heap_shadow A z) /\
    0x7fff8200 <= sh (cs_map sc).
  Proof.
    intros sc Hin. pose proof alloc_ceiling_val as CE. (first [ pose proof ((sec_chunk_boundsT A _ WF0 Hin)) as dR_131; dand5 dR_131 as B1 B2 B3 B4 B5 | pose proof (sec_chunk_boundsT A _ WF0 Hin) as (B1 & B2 & B3 & B4 & B5) ]).
    pose proof (map_size_page (cs_n sc)) as MP. unfold kPageSize in MP.
    assert (M8 : cs_map sc mod 8 = 0) by (apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact B2]).
    assert (S8 : map_size (cs_n sc) mod 8 = 0) by (apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact MP]).
    pose proof (sh_add _ _ M8 S8) as E. pose proof (needed_size2_secondary (cs_n sc) ltac:(lia)) as NS2. pose proof (rounded_size_ge (cs_n sc)) as RG.
    pose proof (app_facts _ _ B3) as AF.
    assert (HR : 0x7fff8200 <= sh (cs_map sc)).
    { (first [ dand5 AF as G1 G2 G3 G4 [LO|HI] | destruct AF as (G1 & G2 & G3 & G4 & [LO|HI]) ]); [pose proof (sh_lowapp_range (cs_map sc) ltac:(unfold kPageSize in *; lia)); lia|].
      pose proof (sh_high_range (cs_map sc) ltac:(unfold kPageSize in *; lia)). unfold kHighShadowMapBeg in *. lia. }
    split; [exact E|]. split; [| exact HR].
    intros z Hz. unfold heap_shadow, heap_shadow_. right. right. exists sc. split; [exact Hin|]. destruct sc as [mb n1]; cbn [cs_map cs_n] in *. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma carved_shadow : forall ch, carved ch ->
    sh (chunk_hi sb ch) = sh (chunk_lo sb ch) + (chunk_hi sb ch - chunk_lo sb ch) / 8 /\
    (forall z, sh (chunk_lo sb ch) <= z < sh (chunk_hi sb ch) -> heap_shadow A z) /\
    0x7fff8200 <= sh (chunk_lo sb ch) /\ chunk_lo sb ch mod 8 = 0 /\ chunk_hi sb ch mod 8 = 0.
  Proof.
    intros ch C. destruct ch as [[c' k']|[mb n1]].
    - destruct C as [Hc Hk]. (first [ pose proof ((chunk_shadow c' k' Hc Hk)) as dR_133; dand4 dR_133 as E HS HR _ | pose proof (chunk_shadow c' k' Hc Hk) as (E & HS & HR & _) ]). cbn [chunk_lo chunk_hi alloc_beg].
      (first [ pose proof ((carved_chunk_boundsT A c' k' WF0 Hc Hk)) as dR_134; dand4 dR_134 as _ _ B3 _ | pose proof (carved_chunk_boundsT A c' k' WF0 Hc Hk) as (_ & _ & B3 & _) ]). pose proof (class_size_mod32 c' Hc) as CM.
      assert (ABM : chunk_addr sb c' k' mod 8 = 0) by (apply (mod0_down _ 32 8); [exists 4; reflexivity| exact B3]).
      assert (CSM : class_size c' mod 8 = 0) by (apply (mod0_down _ 32 8); [exists 4; reflexivity| exact CM]).
      replace (chunk_addr sb c' k' + class_size c' - chunk_addr sb c' k') with (class_size c') by lia.
      split; [exact E|]. split; [intros z Hz; apply HS; lia|]. split; [unfold kHighShadowMapBeg in HR; lia|]. split; [exact ABM|]. rewrite Z.add_mod, ABM, CSM by lia. reflexivity.
    - unfold carved in C. (first [ pose proof ((sec_shadow _ C)) as dR_135; dand3 dR_135 as E HS HR | pose proof (sec_shadow _ C) as (E & HS & HR) ]). cbn [chunk_lo chunk_hi cs_map cs_n] in *.
      (first [ pose proof ((sec_chunk_boundsT A _ WF0 C)) as dR_136; dand3 dR_136 as _ B2 _ | pose proof (sec_chunk_boundsT A _ WF0 C) as (_ & B2 & _) ]). cbn [cs_map cs_n] in B2. pose proof (map_size_page n1) as MP. unfold kPageSize in MP.
      assert (M8 : mb mod 8 = 0) by (apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact B2]).
      assert (S8 : map_size n1 mod 8 = 0) by (apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact MP]).
      replace (mb + map_size n1 - mb) with (map_size n1) by lia.
      split; [exact E|]. split; [intros z Hz; apply HS; lia|]. split; [exact HR|]. split; [exact M8|]. rewrite Z.add_mod, M8, S8 by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma region_tail_shadow : forall c', 1 <= c' <= 30 ->
    let rb := region_beg sb c' in let Rg := a_reg A c' in
    sh (rb + rg_allocated_user Rg) + (rg_mapped_user Rg - rg_allocated_user Rg) / 8 = sh (rb + rg_mapped_user Rg) /\
    sh rb + rg_allocated_user Rg / 8 = sh (rb + rg_allocated_user Rg) /\
    sh (rb + kFreeArrayOffset) + rg_mapped_fa Rg / 8 = sh (rb + kFreeArrayOffset + rg_mapped_fa Rg) /\
    (forall z, sh (rb + rg_allocated_user Rg) <= z < sh (rb + rg_mapped_user Rg) -> heap_shadow A z) /\
    (forall z, sh (rb + kFreeArrayOffset) <= z < sh (rb + kFreeArrayOffset) + rg_mapped_fa Rg / 8 -> heap_shadow A z) /\
    (forall k, 0 <= k < carved_count A c' -> sh (chunk_addr sb c' k) + class_size c' / 8 <= sh (rb + rg_allocated_user Rg)) /\
    sh (rb + rg_mapped_user Rg) <= sh (rb + kFreeArrayOffset).
  Proof.
    intros c' Hc. cbv zeta. pose proof (region_piece_boundsT A c' WF0 Hc) as RB. cbv zeta in RB. change (a_sb A) with sb in *.
    (first [ dand12 RB as R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 | destruct RB as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12) ]).
    assert (RBM : region_beg sb c' mod 8 = 0) by (apply (mod0_down _ 0x10000 8); [exists 8192; reflexivity| exact R9]).
    pose proof (sh_add _ _ RBM R11) as E1. pose proof (sh_add _ _ RBM R10) as E2.
    assert (FAM : (region_beg sb c' + kFreeArrayOffset) mod 8 = 0) by (rewrite Z.add_mod, RBM by lia; reflexivity).
    pose proof (sh_add _ _ FAM R12) as E3.
    assert (DQ : (rg_mapped_user (a_reg A c') - rg_allocated_user (a_reg A c')) / 8 = rg_mapped_user (a_reg A c') / 8 - rg_allocated_user (a_reg A c') / 8).
    { pose proof (Z_div_exact_full_2 _ 8 ltac:(lia) R10). pose proof (Z_div_exact_full_2 _ 8 ltac:(lia) R11). symmetry. apply (Z.div_unique_exact _ _ _); lia. }
    pose proof (sh_mono (region_beg sb c' + rg_mapped_user (a_reg A c')) (region_beg sb c' + kFreeArrayOffset) ltac:(lia)) as M4.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia.
    - intros z Hz. unfold heap_shadow, heap_shadow_. left. exists c'. split; [exact Hc|]. cbv zeta. change (p_sb (a_pl A)) with sb. lia.
    - intros z Hz. unfold heap_shadow, heap_shadow_. right. left. exists c'. split; [exact Hc|]. cbv zeta. change (p_sb (a_pl A)) with sb. lia.
    - intros k Hk. (first [ pose proof ((carved_chunk_boundsT A c' k WF0 Hc Hk)) as dR_138; dand4 dR_138 as B1 B2 B3 _ | pose proof (carved_chunk_boundsT A c' k WF0 Hc Hk) as (B1 & B2 & B3 & _) ]). cbv zeta in *. change (a_sb A) with sb in *.
      pose proof (chunk_shadow c' k Hc Hk) as (E & _). rewrite <- E. apply sh_mono. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma shadow_free_P : forall c' k, 1 <= c' <= 30 ->
    (p_free_ (a_reg A) c' k \/ p_cached_ (a_cache A) c' k \/ p_batch_ (a_qthread A) (a_qglobal A) c' k) ->
    (forall z, sh (chunk_addr sb c' k) <= z < sh (chunk_addr sb c' k) + class_size c' / 8 -> v' (wz z) = v (wz z)) ->
    bytes_at rsegs v' (sh (chunk_addr sb c' k)) (pshadow_free c').
  Proof.
    intros c' k Hc ST AG. pose proof (ar_shadow _ _ _ _ _ R) as (S1 & _).
    assert (Hk : 0 <= k < carved_count A c').
    { destruct ST as [F|[C|[E B]]].
      - (first [ pose proof ((wtR A WF0)) as dR_139; dand3 dR_139 as WR _ _ | destruct (wtR A WF0) as (WR & _ & _) ]). (first [ pose proof ((WR c' Hc)) as dR_140; dand10 dR_140 as _ _ _ _ _ _ _ _ FR _ | destruct (WR c' Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & FR & _) ]). exact (FR k F).
      - (first [ pose proof ((wtC A WF0)) as dR_141; dand3 dR_141 as WC _ _ | destruct (wtC A WF0) as (WC & _ & _) ]). (first [ pose proof ((WC c' ltac:(lia))) as dR_142; dand4 dR_142 as _ _ CR' _ | destruct (WC c' ltac:(lia)) as (_ & _ & CR' & _) ]). exact (CR' k C).
      - subst c'. exact (batch_idx_range k (bi_in_big k B)). }
    apply chunk_shadow_P; [exact Hc| exact Hk| exact AG| | exact (S1 c' k Hc ST)].
    unfold pshadow_free, fa8. rewrite repeat_length. pose proof (class_size_range c' Hc). rewrite Z2Nat.id by (apply Z.div_pos; lia). reflexivity.
  Qed.

  Lemma shadow_live_P : forall u c' k n1, a_livemap A !! u = Some (LI (ChP (CP c' k)) n1) ->
    (forall z, sh (chunk_addr sb c' k) <= z < sh (chunk_addr sb c' k) + class_size c' / 8 -> v' (wz z) = v (wz z)) ->
    bytes_at rsegs v' (sh (chunk_addr sb c' k)) (pshadow_live c' n1).
  Proof.
    intros u c' k n1 Hl AG. (first [ pose proof ((ar_shadow _ _ _ _ _ R)) as dR_143; dand3 dR_143 as _ S2 _ | pose proof (ar_shadow _ _ _ _ _ R) as (_ & S2 & _) ]).
    pose proof (known_live u _ Hl) as CL. unfold known in CL. cbn [li_chunk li_n] in CL. (first [ dand4 CL as Hc Hk Hn Hcl | destruct CL as (Hc & Hk & Hn & Hcl) ]).
    apply chunk_shadow_P; [exact Hc| exact Hk| exact AG| apply pshadow_live_length; [lia| exact Hcl]| exact (S2 u c' k n1 Hl)].
  Qed.

  Lemma shadow_quar_P : forall c' k n1, In (QE (ChP (CP c' k)) n1) (q_entries (a_qthread A ++ a_qglobal A)) ->
    (forall z, sh (chunk_addr sb c' k) <= z < sh (chunk_addr sb c' k) + class_size c' / 8 -> v' (wz z) = v (wz z)) ->
    bytes_at rsegs v' (sh (chunk_addr sb c' k)) (pshadow_quar c' n1).
  Proof.
    intros c' k n1 He AG. (first [ pose proof ((ar_shadow _ _ _ _ _ R)) as dR_145; dand4 dR_145 as _ _ S3 _ | pose proof (ar_shadow _ _ _ _ _ R) as (_ & _ & S3 & _) ]).
    pose proof (known_quar _ (q_in_big _ He)) as CL. unfold known in CL. cbn [qe_chunk qe_n] in CL. (first [ dand4 CL as Hc Hk Hn Hcl | destruct CL as (Hc & Hk & Hn & Hcl) ]).
    apply chunk_shadow_P; [exact Hc| exact Hk| exact AG| apply pshadow_quar_length; [lia| exact Hcl]| exact (S3 c' k n1 He)].
  Qed.

  Lemma shadow_tails_P : forall c', 1 <= c' <= 30 ->
    let Rg := a_reg A c' in let rb := region_beg sb c' in
    (forall z, sh (rb + rg_allocated_user Rg) <= z < sh (rb + rg_mapped_user Rg) -> v' (wz z) = v (wz z)) ->
    (forall z, sh (rb + kFreeArrayOffset) <= z < sh (rb + kFreeArrayOffset) + rg_mapped_fa Rg / 8 -> v' (wz z) = v (wz z)) ->
    fill_at rsegs v' (sh (rb + rg_allocated_user Rg)) ((rg_mapped_user Rg - rg_allocated_user Rg) / 8) kAsanHeapLeftRedzoneMagic /\
    fill_at rsegs v' (sh (rb + kFreeArrayOffset)) (rg_mapped_fa Rg / 8) kAsanHeapLeftRedzoneMagic.
  Proof.
    intros c' Hc. cbv zeta. intros AG1 AG2. (first [ pose proof ((ar_shadow _ _ _ _ _ R)) as dR_147; dand5 dR_147 as _ _ _ S4 _ | pose proof (ar_shadow _ _ _ _ _ R) as (_ & _ & _ & S4 & _) ]). destruct (S4 c' Hc) as [X Y]. cbv zeta in X, Y.
    change (a_sb A) with sb in *. (first [ pose proof ((region_tail_shadow c' Hc)) as dR_148; dand4 dR_148 as E1 E1' E2 _ | pose proof (region_tail_shadow c' Hc) as (E1 & E1' & E2 & _) ]). cbv zeta in E1, E2.
    (first [ pose proof ((region_piece_boundsT A c' WF0 Hc)) as dR_149; dand6 dR_149 as _ _ R3 _ R5 _ | pose proof (region_piece_boundsT A c' WF0 Hc) as (_ & _ & R3 & _ & R5 & _) ]).
    split.
    - eapply fill_at_agree; [exact X|]. intros i Hi. apply AG1. lia.
    - eapply fill_at_agree; [exact Y|]. intros i Hi. apply AG2. pose proof (Z.div_pos (rg_mapped_fa (a_reg A c')) 8). lia.
  Qed.

  Lemma shadow_seclive_P : forall u mb n1, a_livemap A !! u = Some (LI (ChS (CS mb n1)) n1) ->
    (forall z, sh mb <= z < sh mb + map_size n1 / 8 -> v' (wz z) = v (wz z)) ->
    bytes_at rsegs v' (sh mb) (sshadow_live n1).
  Proof.
    intros u mb n1 Hl AG. (first [ pose proof ((ar_shadow _ _ _ _ _ R)) as dR_150; dand6 dR_150 as _ _ _ _ S5 _ | pose proof (ar_shadow _ _ _ _ _ R) as (_ & _ & _ & _ & S5 & _) ]).
    pose proof (known_live u _ Hl) as CL. unfold known in CL. cbn [li_chunk li_n] in CL. (first [ dand3 CL as Hin Hn _ | destruct CL as (Hin & Hn & _) ]).
    eapply bytes_at_agree_gen; [exact (S5 u mb n1 Hl)|]. rewrite sshadow_live_length by lia. intros i Hi. apply AG. lia.
  Qed.

  Lemma shadow_secquar_P : forall mb n2 n1, In (QE (ChS (CS mb n2)) n1) (q_entries (a_qthread A ++ a_qglobal A)) ->
    (forall z, sh mb <= z < sh mb + map_size n1 / 8 -> v' (wz z) = v (wz z)) ->
    bytes_at rsegs v' (sh mb) (sshadow_quar n1).
  Proof.
    intros mb n2 n1 He AG. (first [ pose proof ((ar_shadow _ _ _ _ _ R)) as dR_152; dand6 dR_152 as _ _ _ _ _ S6 | pose proof (ar_shadow _ _ _ _ _ R) as (_ & _ & _ & _ & _ & S6) ]).
    pose proof (known_quar _ (q_in_big _ He)) as CL. unfold known in CL. cbn [qe_chunk qe_n] in CL. (first [ dand3 CL as Hin Hn -> | destruct CL as (Hin & Hn & ->) ]).
    eapply bytes_at_agree_gen; [exact (S6 mb n1 n1 He)|]. rewrite sshadow_quar_length by lia. intros i Hi. apply AG. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma shadow_P0 : (forall z, heap_shadow A z -> v' (wz z) = v (wz z)) ->
    shadow_repr_ LPA sb (a_reg A) (a_cache A) (a_livemap A) (a_qthread A) (a_qglobal A) v'.
  Proof.
    intros AG. split; [|split; [|split; [|split; [|split]]]].
    - intros c' k Hc ST. apply shadow_free_P; [exact Hc| exact ST|].
      assert (Hk : 0 <= k < carved_count A c').
      { destruct ST as [F|[C|[E B]]].
        - (first [ pose proof ((wtR A WF0)) as dR_154; dand3 dR_154 as WR _ _ | destruct (wtR A WF0) as (WR & _ & _) ]). (first [ pose proof ((WR c' Hc)) as dR_155; dand10 dR_155 as _ _ _ _ _ _ _ _ FR _ | destruct (WR c' Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & FR & _) ]). exact (FR k F).
        - (first [ pose proof ((wtC A WF0)) as dR_156; dand3 dR_156 as WC _ _ | destruct (wtC A WF0) as (WC & _ & _) ]). (first [ pose proof ((WC c' ltac:(lia))) as dR_157; dand4 dR_157 as _ _ CR' _ | destruct (WC c' ltac:(lia)) as (_ & _ & CR' & _) ]). exact (CR' k C).
        - subst c'. exact (batch_idx_range k (bi_in_big k B)). }
      intros z Hz. apply AG. exact (proj1 (proj2 (chunk_shadow c' k Hc Hk)) z Hz).
    - intros u c' k n1 Hl. apply (shadow_live_P u); [exact Hl|].
      pose proof (known_live u _ Hl) as CL. unfold known in CL. cbn [li_chunk li_n] in CL. (first [ dand3 CL as Hc Hk _ | destruct CL as (Hc & Hk & _) ]).
      intros z Hz. apply AG. exact (proj1 (proj2 (chunk_shadow c' k Hc Hk)) z Hz).
    - intros c' k n1 He. apply shadow_quar_P; [exact He|].
      pose proof (known_quar _ (q_in_big _ He)) as CL. unfold known in CL. cbn [qe_chunk qe_n] in CL. (first [ dand3 CL as Hc Hk _ | destruct CL as (Hc & Hk & _) ]).
      intros z Hz. apply AG. exact (proj1 (proj2 (chunk_shadow c' k Hc Hk)) z Hz).
    - intros c' Hc. apply shadow_tails_P; [exact Hc| |]; intros z Hz; apply AG.
      + exact (proj1 (proj2 (proj2 (proj2 (region_tail_shadow c' Hc)))) z Hz).
      + exact (proj1 (proj2 (proj2 (proj2 (proj2 (region_tail_shadow c' Hc))))) z Hz).
    - intros u mb n1 Hl. apply (shadow_seclive_P u); [exact Hl|].
      pose proof (known_live u _ Hl) as CL. unfold known in CL. cbn [li_chunk li_n] in CL. destruct CL as (Hin & _).
      intros z Hz. apply AG. exact (proj1 (proj2 (sec_shadow _ Hin)) z Hz).
    - intros mb n2 n1 He. apply (shadow_secquar_P mb n2); [exact He|].
      pose proof (known_quar _ (q_in_big _ He)) as CL. unfold known in CL. cbn [qe_chunk qe_n] in CL. (first [ dand3 CL as Hin _ -> | destruct CL as (Hin & _ & ->) ]).
      intros z Hz. apply AG. exact (proj1 (proj2 (sec_shadow _ Hin)) z Hz).
  Qed.
End TransportR.
