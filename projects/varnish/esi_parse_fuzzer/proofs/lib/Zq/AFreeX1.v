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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts ARtSrgm AMallocI AMalmys ATransp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeB1 ASecComb ASecB1 ANodijx.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AQWf.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSrgm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecComb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ANodijx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AQWf.AQOps.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
#[local] Notation WF := (WF AL_pboth).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Notation wz z := (Z_to_bv 64 z) (only parsing).
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kHighShadowMapSize, kSpaceReserve, kMaxSize, kLowShadowMapBeg, kLowShadowBeg, kShadowGapBeg,
                        kPtrArrayReserve, kChunksBlockCount, kFakeStackBytes, kPageSize, kSecondaryHeaderSize, kMaxPrimaryUser in *.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma bytes_at_u64s : forall (m : mem) a (ws : list word),
  0 <= a -> a + 8 * Z.of_nat (length ws) <= 2^64 ->
  (forall j w, nth_error ws j = Some w -> bytes_at rsegs m (a + 8 * Z.of_nat j) (le8 w)) ->
  bytes_at rsegs m a (u64s ws).
Proof.
  intros m a ws. revert a. induction ws as [|w ws IH]; intros a Ha Hb H.
  - cbn [u64s]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - cbn [u64s]. apply bytes_at_app. split.
    + specialize (H 0%nat w eq_refl). rewrite Z.mul_0_r, Z.add_0_r in H. exact H.
    + rewrite length_le8. apply IH; [lia| cbn [length] in Hb; lia|].
      intros j w' E. replace (a + Z.of_nat 8 + 8 * Z.of_nat j) with (a + 8 * Z.of_nat (S j)) by lia. apply H. exact E.
Qed.

(* [comment removed for export] *)
Lemma nearest_spec : forall (hs : list word) (m h : Z),
  0 < h <= m ->
  (exists w, In w hs /\ bv_unsigned w = h) ->
  (forall w, In w hs -> bv_unsigned w <= m -> bv_unsigned w <= h) ->
  nearest hs m = h.
Proof.
  (intros hs m h Hh; (first [ intro dR_43; dex1 dR_43 as w0; destruct dR_43 as [Hin Hw0] | intro dR_43; dand3 dR_43 as w0 Hin Hw0 | intros (w0 & Hin & Hw0) ]); intros ALL). unfold nearest.
  assert (INV : forall l acc, incl l hs -> 0 <= acc <= h -> (acc = h \/ In w0 l) ->
            fold_left (fun acc0 h0 => nearest_step m acc0 (bv_unsigned h0)) l acc = h).
  { induction l as [|x l IH]; intros acc INC R C.
    - destruct C as [C|C]; [exact C| destruct C].
    - cbn [fold_left]. pose proof (bv_unsigned_in_range _ x) as XR.
      assert (XLE : bv_unsigned x <= m -> bv_unsigned x <= h) by (intros LE; apply ALL; [apply INC; left; reflexivity| exact LE]).
      apply IH.
      + intros y Hy. apply INC. right. exact Hy.
      + unfold nearest_step. destruct (Z.ltb_spec m (bv_unsigned x)); [exact R|].
        destruct (Z.ltb_spec (m - bv_unsigned x) (m - acc)); [| exact R]. split; [lia| apply XLE; lia].
      + unfold nearest_step. destruct C as [C|[C|C]].
        * left. destruct (Z.ltb_spec m (bv_unsigned x)); [exact C|].
          destruct (Z.ltb_spec (m - bv_unsigned x) (m - acc)); [| exact C]. pose proof (XLE ltac:(lia)). lia.
        * left. subst x. rewrite Hw0. destruct (Z.ltb_spec m h); [lia|]. destruct (Z.ltb_spec (m - h) (m - acc)); [reflexivity| lia].
        * right. exact C. }
  apply INV; [intros y Hy; exact Hy| lia| right; exact Hin].
Qed.

Lemma nth_error_last_ : forall {X} (l : list X) d, l <> [] -> nth_error l (length l - 1) = Some (last l d).
Proof.
  intros X l d NE. induction l as [|a r IH]; [congruence|]. destruct r as [|b r']; [reflexivity|].
  specialize (IH ltac:(discriminate)).
  cbn [length] in IH |- *. replace (S (S (length r')) - 1)%nat with (S (S (length r') - 1))%nat by lia.
  cbn [nth_error]. cbn [nth_error] in IH. rewrite IH. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ro_join2 : forall (m : mem) A c1 c2, ro_cells rsegs m A [c1] -> ro_cells rsegs m (A + Z.of_nat (csize c1)) [c2] -> ro_cells rsegs m A [c1; c2].
Proof.
  intros m A c1 c2 [W1 B1] [W2 B2]. cbn in W1, W2. split; [cbn; tauto|].
  cbn [cells_bytes]. cbn [cells_bytes] in B1, B2. rewrite app_nil_r in B1.
  apply bytes_at_app. split; [exact B1|]. rewrite (cbytes_length c1) by tauto. exact B2.
Qed.

(* [comment removed for export] *)
Lemma canary_cell : forall (m : mem), exists canary : word, ro_cells rsegs m SSP_CELL [C8 canary].
Proof.
  intros m. (first [ pose proof ((img_rw_words m SSP_CELL 1 ltac:(unfold SSP_CELL; lia) ltac:(unfold SSP_CELL; cbn; lia))) as dR_1; dex1 dR_1 as ws; destruct dR_1 as [L R] | pose proof ((img_rw_words m SSP_CELL 1 ltac:(unfold SSP_CELL; lia) ltac:(unfold SSP_CELL; cbn; lia))) as dR_1; dand3 dR_1 as ws L R | destruct (img_rw_words m SSP_CELL 1 ltac:(unfold SSP_CELL; lia) ltac:(unfold SSP_CELL; cbn; lia)) as (ws & L & R) ]).
  destruct ws as [|w [|]]; cbn in L; try lia. exists w. exact (proj1 R).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section SecKit.
Context {Clg : Ceiling}.
  Variables (A : AState) (m : mem) (md : Model) (p n0 : Z).
  Hypothesis AI : @pa_ainv _ DepotRepL A m md.
  Hypothesis HL : as_live A p = Some n0.
  Hypothesis NQB : kMaxPrimaryUser < n0.

  #[warnings="-notation-for-abbreviation"] Local Notation v := (aview_of (pa_hull A) m).
  #[warnings="-notation-for-abbreviation"] Local Notation P := (a_pl A).
  #[warnings="-notation-for-abbreviation"] Local Notation chunks := (sr_chunks (a_sec A)).
  #[warnings="-notation-for-abbreviation"] Local Notation nch := (Z.of_nat (length (sr_chunks (a_sec A)))).
  #[warnings="-notation-for-abbreviation"] Local Notation h := (p - 6144).
  #[warnings="-notation-for-abbreviation"] Local Notation msz := (map_size n0).
  #[warnings="-notation-for-abbreviation"] Local Notation sb := (a_sb A).
  #[warnings="-notation-for-abbreviation"] Local Notation pa := (p_pa (a_pl A)).
  #[warnings="-notation-for-abbreviation"] Local Notation thr := (p_thr (a_pl A)).

  (* [comment removed for export] *)
  Definition sec_words : list word := map (fun c => Z_to_bv 64 (cs_map c)) chunks.
  Definition sec_last : chunkS := last chunks (CS 0 0).

  Let W : WF A. Proof. exact (ai_wf _ _ _ _ _ _ _ AI). Qed.
  Let AR : WF A /\ @arepr _ DepotRepL LPA AL_pboth [] A v. Proof. exact (conj W (ai_repr _ _ _ _ _ _ _ AI)). Qed.
  Let SR : sec_repr_ LPA AL_pboth (a_pl A) (a_sec A) v. Proof. exact (ar_sec _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI)). Qed.
  Let CFA : Forall (fun c => bytes_at rsegs v (fst c) (snd c)) (cl_consts LPA).
  Proof. exact (proj1 (ar_consts _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI))). Qed.
  Ltac cell H a bs := pose proof (consts_cell _ a bs CFA eq_refl) as H.

  (* [comment removed for export] *)
  Lemma sk_live : exists li, a_livemap A !! p = Some li /\ li_n li = n0 /\ li_chunk li = ChS (CS h n0) /\ In (CS h n0) chunks.
  Proof.
    (first [ pose proof ((free_li A p n0 HL)) as dR_2; dex1 dR_2 as li; destruct dR_2 as [Hl Hn] | pose proof ((free_li A p n0 HL)) as dR_2; dand3 dR_2 as li Hl Hn | destruct (free_li A p n0 HL) as (li & Hl & Hn) ]).
    (first [ pose proof ((wfV A W)) as dR_3; dand3 dR_3 as V1 _ _ | destruct (wfV A W) as (V1 & _ & _) ]). (first [ pose proof ((V1 p li Hl)) as dR_4; dand3 dR_4 as N U C | pose proof (V1 p li Hl) as (N & U & C) ]). cbv zeta in U, C.
    exists li. split; [exact Hl|]. split; [exact Hn|].
    destruct (li_chunk li) as [[c k]|[mb n1]] eqn:EC.
    - exfalso. destruct C as (C1 & _). rewrite Hn in C1. unfold kMaxPrimaryUser in *. lia.
    - (first [ dand3 C as C1 C2 C3 | destruct C as (C1 & C2 & C3) ]). rewrite Hn in C2. subst n1.
      cbn [user_of] in U. unfold sec_user_beg, kPageSize in U. rewrite Hn in C3.
      assert (E : mb = p - 6144) by lia. subst mb. split; [reflexivity| exact C3].
  Qed.

  Lemma sk_In : In (CS h n0) chunks.
  Proof. (first [ dex1 sk_live as li; dand4 sk_live as _ _ _ Hin | dand5 sk_live as li _ _ _ Hin | destruct sk_live as (li & _ & _ & _ & Hin) ]). exact Hin. Qed.

  Lemma sk_li : a_livemap A !! p = Some (LI (ChS (CS h n0)) n0).
  Proof. (first [ dex1 sk_live as li; dand4 sk_live as Hl Hn Hc _ | dand5 sk_live as li Hl Hn Hc _ | destruct sk_live as (li & Hl & Hn & Hc & _) ]). destruct li as [ch n]. cbn [li_n li_chunk] in Hn, Hc. subst. exact Hl. Qed.

  Lemma sk_idx : exists i, nth_error chunks i = Some (CS h n0).
  Proof. apply In_nth_error'. exact sk_In. Qed.

  Lemma sk_known : known A (ChS (CS h n0)) n0.
  Proof. cbn. split; [exact sk_In| split; [exact NQB| reflexivity]]. Qed.

  (* [comment removed for export] *)
  Lemma sk_geo : aobj h msz /\ h mod 4096 = 0 /\ 4096 + 32 <= msz /\ msz mod 4096 = 0 /\ h + msz <= alloc_ceiling /\
                 p = h + 6144 /\ p + 8 * ((n0 + 7) / 8) <= h + msz /\ n0 + 6144 <= msz /\ kMaxPrimaryUser < n0 < REQ_MAX /\
                 0x60a000 <= h /\ p mod 16 = 0.
  Proof.
    (first [ pose proof ((sec_chunk_bounds A _ W sk_In)) as dR_8; dand5 dR_8 as B1 B2 B3 B4 B5 | pose proof (sec_chunk_bounds A _ W sk_In) as (B1 & B2 & B3 & B4 & B5) ]). cbn [cs_map cs_n] in *.
    (first [ pose proof ((secondary_layout h n0 NQB)) as dR_9; dand7 dR_9 as S1 S2 S3 S4 S5 S6 S7 | pose proof (secondary_layout h n0 NQB) as (S1 & S2 & S3 & S4 & S5 & S6 & S7) ]).
    pose proof (map_size_page n0) as MP. pose proof (needed_size_ge n0) as NG. rewrite needed_size2_secondary in B5 by lia.
    pose proof (rounded_size_ge n0) as RG. destruct (free_n0 A m md p n0 AI HL) as [NR US]. rewrite US in S4.
    pose proof (app_facts _ _ B3) as AF. destruct (free_geom A m md p n0 AI HL) as (PM & _).
    unfold sec_user_beg, kPageSize in S3, S4, S7.
    assert (R8 : p + 8 * ((n0 + 7) / 8) <= h + msz).
    { apply (roundup8_le p n0 (h + msz)); [| | lia].
      - apply (mod0_down _ 16 8); [exists 2; reflexivity| exact PM].
      - rewrite Z.add_mod by lia. rewrite (mod0_down _ 4096 8 ltac:(exists 512; reflexivity) B2), (mod0_down _ kPageSize 8 ltac:(exists 512; reflexivity) MP). reflexivity. }
    split; [apply (proj1 (aobj_app_rangeA _ _)); exact B3|]. split; [exact B2|]. split; [kung_all; lia|]. split; [exact MP|].
    split; [exact B4|]. split; [lia|]. split; [exact R8|]. split; [lia|]. split; [lia|]. split; [| exact PM].
    pose proof (known_range A v AR (ChS (CS h n0)) n0 sk_known) as [KR _]. cbn [chunk_lo] in KR. exact KR.
  Qed.

  (* [comment removed for export] *)
  Lemma sk_shr : sh (h + msz) = sh h + msz / 8 /\ (sh h) mod 512 = 0 /\ (msz / 8) mod 512 = 0 /\
                 ((kHighShadowMapBeg <= sh h /\ sh h + msz / 8 <= kHighMemBeg /\ kHighMemBeg <= h) \/
                  (kLowShadowBeg + 0x200 <= sh h /\ sh h + msz / 8 < kShadowGapBeg /\ h + msz <= kLowShadowMapBeg)).
  Proof.
    (first [ pose proof (sk_geo) as dR_10; dand11 dR_10 as HLO HAL MSZ MSZAL HHI _ _ _ _ H5 _ | pose proof sk_geo as (HLO & HAL & MSZ & MSZAL & HHI & _ & _ & _ & _ & H5 & _) ]). (first [ pose proof ((aobj_facts _ _ HLO)) as dR_11; dand5 dR_11 as F1 F2 F3 F4 F5 | pose proof (aobj_facts _ _ HLO) as (F1 & F2 & F3 & F4 & F5) ]).
    pose proof alloc_ceiling_val as CE.
    assert (SHA : sh (h + msz) = sh h + msz / 8).
    { apply sh_add; [apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact HAL]| apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact MSZAL]]. }
    pose proof (Z_div_mod_eq_full h 4096) as XH. rewrite HAL, Z.add_0_r in XH.
    pose proof (Z_div_mod_eq_full msz 4096) as XM. rewrite MSZAL, Z.add_0_r in XM.
    assert (D1 : h / 8 = 512 * (h / 4096)) by (rewrite XH at 1; replace (4096 * (h / 4096)) with ((512 * (h / 4096)) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
    assert (D2 : msz / 8 = 512 * (msz / 4096)) by (rewrite XM at 1; replace (4096 * (msz / 4096)) with ((512 * (msz / 4096)) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
    split; [exact SHA|]. split.
    { unfold sh, kShadowOffset. rewrite D1. replace (512 * (h / 4096) + 2147450880) with ((h / 4096 + 4194240) * 512) by lia. apply Z_mod_mult. }
    split; [rewrite D2; replace (512 * (msz / 4096)) with ((msz / 4096) * 512) by lia; apply Z_mod_mult|].
    unfold sh, kShadowOffset in *. kung_all.
    destruct F5 as [LOW|HIGH].
    - right. pose proof (Z.div_le_mono (h + msz) 0x7fff7000 8 ltac:(lia) ltac:(lia)) as U. change (0x7fff7000 / 8) with 268430848 in U.
      pose proof (Z.div_le_mono 0x60a000 h 8 ltac:(lia) ltac:(lia)) as L. change (0x60a000 / 8) with 791552 in L.
      rewrite Z.add_comm in SHA |- *. lia.
    - left. pose proof (Z.div_le_mono 0x10007fff8000 h 8 ltac:(lia) ltac:(lia)) as L. change (0x10007fff8000 / 8) with 0x2000ffff000 in L.
      pose proof (Z.div_le_mono (h + msz) 0x7fffff800000 8 ltac:(lia) ltac:(lia)) as U. change (0x7fffff800000 / 8) with 0xffffff00000 in U.
      lia.
  Qed.

  Lemma sk_sb : kHighMemBeg <= sb /\ sb + 2^37 <= alloc_ceiling /\ apart h msz sb (2^37) /\ (p + -16 < sb \/ sb + 2^37 <= p + -16).
  Proof.
    (first [ pose proof ((sb_facts A W)) as dR_12; dand5 dR_12 as _ _ HB6 RSB SCE | pose proof (sb_facts A W) as (_ & _ & HB6 & RSB & SCE) ]). pose proof (sec_apart_b6 A v AR _ sk_In) as D. cbn [cs_map cs_n] in D.
    (first [ pose proof (sk_geo) as dR_13; dand10 dR_13 as HLO _ MSZ _ _ PH _ N6 NR _ | pose proof sk_geo as (HLO & _ & MSZ & _ & _ & PH & _ & N6 & NR & _) ]). unfold a_b6, a_sb in *. unfold apart. kung_all. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma sk_nch : 1 <= nch < 2^20 /\ nch <= sr_reserved (a_sec A) /\ sr_reserved (a_sec A) = kChunksBlockCount /\ chunks <> [].
  Proof.
    (first [ pose proof ((sec_nch A m md AI)) as dR_14; dand4 dR_14 as N1 N2 N3 N4 | pose proof (sec_nch A m md AI) as (N1 & N2 & N3 & N4) ]).
    assert (NE : chunks <> []) by (intros E; pose proof sk_In as X; rewrite E in X; destruct X).
    assert (NZ : (0 < length chunks)%nat) by (destruct (sr_chunks (a_sec A)); [congruence| cbn; lia]).
    unfold kChunksBlockCount in *. destruct N3 as [N3|N3]; [lia|]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia. exact NE.
  Qed.

  Lemma sk_pa : aobj pa (8 * nch) /\ pa + 8 * nch <= alloc_ceiling /\ pa mod 8 = 0 /\ aobj pa kPtrArrayReserve /\ 8 * nch <= kPtrArrayReserve.
  Proof.
    (first [ pose proof ((sec_pa A m md AI)) as dR_15; dand3 dR_15 as A1 A2 A3 | pose proof (sec_pa A m md AI) as (A1 & A2 & A3) ]). (first [ pose proof (sk_nch) as dR_16; dand4 dR_16 as N1 N2 N3 _ | pose proof sk_nch as (N1 & N2 & N3 & _) ]). unfold kPtrArrayReserve, kChunksBlockCount in *.
    split; [apply (aobj_sub _ _ _ _ A1); lia|]. split; [lia|]. split; [apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact A3]|]. split; [exact A1| lia].
  Qed.

  Lemma sec_words_length : length sec_words = length chunks.
  Proof. unfold sec_words. apply length_map. Qed.
  Lemma sec_words_nth : forall j c, nth_error chunks j = Some c -> nth_error sec_words j = Some (Z_to_bv 64 (cs_map c)).
  Proof. intros j c E. unfold sec_words. rewrite nth_error_map, E. reflexivity. Qed.
  Lemma sec_words_In : forall w, In w sec_words -> exists c, In c chunks /\ w = Z_to_bv 64 (cs_map c).
  Proof. intros w Hw. unfold sec_words in Hw. apply in_map_iff in Hw as (c & <- & Hc). exists c. split; [exact Hc| reflexivity]. Qed.

  Lemma sk_arr : u64arr rsegs v pa sec_words.
  Proof.
    pose proof SR as S. unfold sec_repr_ in S. cbv zeta in S. (first [ dand7 S as _ _ _ _ _ CH PM | destruct S as (_ & _ & _ & _ & _ & CH & PM) ]).
    (first [ pose proof (sk_pa) as dR_18; dand5 dR_18 as A1 A2 A3 A4 A5 | pose proof sk_pa as (A1 & A2 & A3 & A4 & A5) ]). pose proof (aobj_facts _ _ A1) as AF. pose proof alloc_ceiling_val as CE.
    (first [ pose proof (sk_nch) as dR_19; dand4 dR_19 as N1 N2 N3 _ | pose proof sk_nch as (N1 & N2 & N3 & _) ]).
    split.
    - apply bytes_at_u64s; [lia| rewrite sec_words_length; lia|].
      intros j w E. unfold sec_words in E. rewrite nth_error_map in E. destruct (nth_error chunks j) as [c|] eqn:Ec; [| discriminate].
      cbn in E. injection E as <-. destruct (CH j c Ec) as [U _]. exact U.
    - rewrite sec_words_length. apply mapped_wr_at; [| lia| lia]. intros k Hk. apply PM. unfold kChunksBlockCount in N3. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma sk_hdr_at : forall j c, nth_error chunks j = Some c ->
    rw_cells rsegs v (cs_map c) [C8 (wz (cs_map c)); C8 (wz (map_size (cs_n c))); C8 (wz (needed_size2 (cs_n c))); C8 (wz (Z.of_nat j))].
  Proof.
    intros j c E. pose proof SR as S. unfold sec_repr_ in S. cbv zeta in S. (first [ dand7 S as _ _ _ _ _ CH _ | destruct S as (_ & _ & _ & _ & _ & CH & _) ]).
    destruct (CH j c E) as [_ R]. exact R.
  Qed.

  (* [comment removed for export] *)
  Lemma sk_sep_chunks : forall j k c d, nth_error chunks j = Some c -> nth_error chunks k = Some d -> j <> k ->
    apart (cs_map c) (map_size (cs_n c)) (cs_map d) (map_size (cs_n d)).
  Proof.
    intros j k c d Ej Ek NE. unfold apart.
    exact (bm_sep A (15 + j) (15 + k) _ _ _ _ W (bm_nth_sec A j c Ej) (bm_nth_sec A k d Ek) ltac:(lia)).
  Qed.
  Lemma sk_sep_fixed : forall j c, nth_error chunks j = Some c ->
    apart (cs_map c) (map_size (cs_n c)) pa kPtrArrayReserve /\ apart (cs_map c) (map_size (cs_n c)) thr 4096 /\
    apart (cs_map c) (map_size (cs_n c)) (p_ctx P) 0x10000 /\ apart (cs_map c) (map_size (cs_n c)) (p_nodes0 P) kDepotNodesBlock /\
    apart (cs_map c) (map_size (cs_n c)) (p_frames0 P) kStackStoreBlockBytes.
  Proof.
    intros j c E. (first [ pose proof ((bm_nth_fixed A)) as dR_21; dand10 dR_21 as E0 E1 E2 E3 E4 E5 E6 E7 E8 _ | pose proof (bm_nth_fixed A) as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & _) ]). pose proof (bm_nth_sec A j c E) as Es.
    unfold a_pa, a_thr, a_ctx, a_nodes0, a_frames0 in *. unfold apart.
    split; [exact (bm_sep A _ _ _ _ _ _ W Es E1 ltac:(lia))|]. split; [exact (bm_sep A _ _ _ _ _ _ W Es E4 ltac:(lia))|].
    split; [exact (bm_sep A _ _ _ _ _ _ W Es E5 ltac:(lia))|]. split; [exact (bm_sep A _ _ _ _ _ _ W Es E7 ltac:(lia))| exact (bm_sep A _ _ _ _ _ _ W Es E8 ltac:(lia))].
  Qed.
  Lemma sk_sep_pa : apart pa kPtrArrayReserve thr 4096 /\ apart pa kPtrArrayReserve (p_ctx P) 0x10000 /\
                    apart pa kPtrArrayReserve (p_nodes0 P) kDepotNodesBlock /\ apart pa kPtrArrayReserve (p_frames0 P) kStackStoreBlockBytes /\
                    apart (p_ctx P) 0x10000 thr 4096.
  Proof.
    (first [ pose proof ((bm_nth_fixed A)) as dR_22; dand10 dR_22 as E0 E1 E2 E3 E4 E5 E6 E7 E8 _ | pose proof (bm_nth_fixed A) as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & _) ]).
    unfold a_pa, a_thr, a_ctx, a_nodes0, a_frames0 in *. unfold apart.
    split; [exact (bm_sep A _ _ _ _ _ _ W E1 E4 ltac:(lia))|]. split; [exact (bm_sep A _ _ _ _ _ _ W E1 E5 ltac:(lia))|].
    split; [exact (bm_sep A _ _ _ _ _ _ W E1 E7 ltac:(lia))|]. split; [exact (bm_sep A _ _ _ _ _ _ W E1 E8 ltac:(lia))| exact (bm_sep A _ _ _ _ _ _ W E5 E4 ltac:(lia))].
  Qed.

  (* [comment removed for export] *)
  Lemma sk_chunk : forall c, In c chunks ->
    aobj (cs_map c) (map_size (cs_n c)) /\ cs_map c mod 4096 = 0 /\ cs_map c + map_size (cs_n c) <= alloc_ceiling /\
    4096 + 32 <= map_size (cs_n c) /\ 0x60a000 <= cs_map c /\ kMaxPrimaryUser < cs_n c < REQ_MAX /\ 0 <= needed_size2 (cs_n c) < 2^64.
  Proof.
    intros c Hc. (first [ pose proof ((sec_chunk_bounds A _ W Hc)) as dR_23; dand5 dR_23 as B1 B2 B3 B4 B5 | pose proof (sec_chunk_bounds A _ W Hc) as (B1 & B2 & B3 & B4 & B5) ]). pose proof alloc_ceiling_val as CE.
    pose proof (needed_size_ge (cs_n c)) as NG. rewrite needed_size2_secondary in B5 |- * by lia. pose proof (rounded_size_ge (cs_n c)) as RG.
    destruct c as [mb n1]. cbn [cs_map cs_n] in *.
    pose proof (known_range A v AR (ChS (CS mb n1)) n1 ltac:(cbn; split; [exact Hc| split; [lia| reflexivity]])) as [KR _]. cbn [chunk_lo] in KR.
    split; [apply (proj1 (aobj_app_rangeA _ _)); exact B3|]. split; [exact B2|]. split; [exact B4|]. split; [kung_all; lia|]. split; [exact KR|]. split; [lia|].
    unfold needed_size, REQ_MAX in *. kung_all. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma sk_nearest : nearest sec_words (p + -16) = h.
  Proof.
    (first [ pose proof (sk_geo) as dR_24; dand11 dR_24 as HLO HAL MSZ MSZAL HHI PH PIN N6 NR H5 PM | pose proof sk_geo as (HLO & HAL & MSZ & MSZAL & HHI & PH & PIN & N6 & NR & H5 & PM) ]). destruct sk_idx as [i NTH].
    pose proof alloc_ceiling_val as CE.
    apply nearest_spec.
    - lia.
    - exists (Z_to_bv 64 h). split; [unfold sec_words; apply in_map_iff; exists (CS h n0); split; [reflexivity| exact sk_In]|].
      apply unsigned_lit. lia.
    - intros w Hw LE. (first [ pose proof ((sec_words_In w Hw)) as dR_25; dex1 dR_25 as c; destruct dR_25 as [Hc ->] | pose proof ((sec_words_In w Hw)) as dR_25; dand3 dR_25 as c Hc -> | destruct (sec_words_In w Hw) as (c & Hc & ->) ]). (first [ pose proof ((sk_chunk c Hc)) as dR_26; dand7 dR_26 as C1 C2 C3 C4 C5 C6 _ | pose proof (sk_chunk c Hc) as (C1 & C2 & C3 & C4 & C5 & C6 & _) ]).
      rewrite unsigned_lit in LE |- * by lia.
      destruct (In_nth_error' _ _ Hc) as [j Ej].
      destruct (Nat.eq_dec j i) as [->|NE]; [rewrite NTH in Ej; injection Ej as <-; cbn [cs_map]; lia|].
      pose proof (sk_sep_chunks j i c (CS h n0) Ej NTH NE) as D. cbn [cs_map cs_n] in D. unfold apart in D. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma sk_last : nth_error chunks (Z.to_nat (nch - 1)) = Some sec_last /\ In sec_last chunks /\
                  nth_error sec_words (Z.to_nat (nch - 1)) = Some (Z_to_bv 64 (cs_map sec_last)) /\
                  bv_unsigned (Z_to_bv 64 (cs_map sec_last)) = cs_map sec_last.
  Proof.
    (first [ pose proof (sk_nch) as dR_27; dand4 dR_27 as N1 _ _ NE | pose proof sk_nch as (N1 & _ & _ & NE) ]). pose proof alloc_ceiling_val as CE.
    assert (E1 : nth_error chunks (Z.to_nat (nch - 1)) = Some sec_last).
    { replace (Z.to_nat (nch - 1)) with (length chunks - 1)%nat by lia. unfold sec_last. apply nth_error_last_. exact NE. }
    assert (IN : In sec_last chunks) by (eapply nth_error_In; exact E1).
    (first [ pose proof ((sk_chunk _ IN)) as dR_28; dand6 dR_28 as C1 _ C3 C4 C5 _ | pose proof (sk_chunk _ IN) as (C1 & _ & C3 & C4 & C5 & _) ]).
    split; [exact E1|]. split; [exact IN|]. split; [apply sec_words_nth; exact E1| apply unsigned_lit; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma sk_regs : exists (srt nf ca gA gM : Z),
    0 <= srt < 256 /\ 0 <= nf < 2^64 /\ 0 <= ca < 2^64 /\ 0 <= gA < 2^64 /\ 0 <= gM < 2^64 /\
    rw_cells rsegs v 0xb15d0 [C8 (wz nch); C1 (Z_to_bv 8 srt)] /\
    rw_cells rsegs v 0xb15e8 [C8 (wz nf); C8 (wz ca)] /\
    rw_cells rsegs v 0xb1800 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C2 (wz 0)] /\
    rw_cells rsegs v 0xb1818 [C8 (wz gA); C8 (wz gM)].
  Proof.
    pose proof (sec_LREG A m md AI) as LREG. destruct (sec_LCS A m) as [cs LCS].
    (first [ pose proof ((sec_LSTA A m)) as dR_29; dex5 dR_29 as na nf ca mx bsl; destruct dR_29 as [LSTA _] | pose proof ((sec_LSTA A m)) as dR_29; dand7 dR_29 as na nf ca mx bsl LSTA _ | destruct (sec_LSTA A m) as (na & nf & ca & mx & bsl & LSTA & _) ]). (first [ pose proof ((sec_GST A m)) as dR_30; dex2 dR_30 as sta stm; rename dR_30 into GST | pose proof ((sec_GST A m)) as dR_30; dand3 dR_30 as sta stm GST | destruct (sec_GST A m) as (sta & stm & GST) ]).
    pose proof (sec_LMTX A m md AI) as LMTX. unfold ASecComb.LMA, ASecComb.LSTAT in *.
    exists (bv_unsigned cs), (bv_unsigned nf), (bv_unsigned ca), (bv_unsigned sta), (bv_unsigned stm).
    assert (Hcs : 0 <= bv_unsigned cs < 256) by (pose proof (bv_unsigned_in_range _ cs) as X; unfold bv_modulus in X; cbn in X; lia). pose proof (zr_word nf). pose proof (zr_word ca). pose proof (zr_word sta). pose proof (zr_word stm). unfold inr64 in *.
    rewrite !Z_to_bv_bv_unsigned. replace (Z_to_bv 8 (bv_unsigned cs)) with cs by (symmetry; exact (definitions.Z_to_bv_bv_unsigned _ cs)).
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split.
    { apply (rw_cells_app_split _ _ [C8 (wz (sr_reserved (a_sec A)))] [C8 (wz nch)]) in LREG as [_ LREG]. cbn [cells_size csize Nat.add] in LREG.
      change (0xb1598 + 48 + Z.of_nat 8) with 0xb15d0 in LREG. change (0xb1598 + 64) with (0xb15d0 + Z.of_nat (cells_size [C8 (wz nch)])) in LCS.
      exact (rw_cells_app_join _ _ [C8 (wz nch)] [C1 cs] LREG LCS). }
    split.
    { apply (rw_cells_app_split _ _ [C8 na] [C8 nf; C8 ca; C8 mx; CB 512 (u64s bsl)]) in LSTA as [_ LSTA]. cbn [cells_size csize Nat.add] in LSTA.
      apply (rw_cells_app_split _ _ [C8 nf; C8 ca] [C8 mx; CB 512 (u64s bsl)]) in LSTA as [LSTA _].
      change (0xb1598 + 72 + Z.of_nat 8) with 0xb15e8 in LSTA. exact LSTA. }
    split; [exact LMTX| exact GST].
  Qed.

  (* [comment removed for export] *)
  Lemma sk_consts : ro_cells rsegs v LMA_L [C8 (wz 4096); C8 (wz pa)] /\ ro_cells rsegs v 0xa8bb0 [C8 (wz 1)] /\
                    ro_cells rsegs v 0xb1578 [C8 (wz sb)] /\ ro_cells rsegs v 0xa8b60 [C8 (wz CF)].
  Proof.
    split; [| split; [| split]].
    - unfold LMA_L. pose proof (sec_LMA0 A m md AI) as X. pose proof (sec_LPA8 A m md AI) as Y. unfold ASecComb.LMA in X, Y.
      exact (ro_join2 v 0xb1598 _ _ X Y).
    - cell Hx 0xa8bb0 (le8 (Z_to_bv 64 1)). apply bytes_ro_C8. exact Hx.
    - exact (hit_SBc A m md AI).
    - cell Hx 0xa8b60 (le8 (Z_to_bv 64 0x1466e8)). unfold CF. apply bytes_ro_C8. exact Hx.
  Qed.

  Lemma sk_a8 : exists canary : word, a8_consts v canary.
  Proof.
    destruct (canary_cell v) as [canary CAN]. exists canary. unfold a8_consts.
    cell HCF 0x1466e8 pa_common_flags_bytes.
    split; [unfold CF; apply bytes_ro_C8; apply (bytes_at_as v _ _ _ (bytes_at_mid v 0x1466e8 pa_common_flags_bytes 144 8 HCF ltac:(cbn; lia))); byteseq|].
    split; [unfold CF; apply bytes_ro_C1; apply (bytes_at_as v _ _ _ (bytes_at_mid v 0x1466e8 pa_common_flags_bytes 219 1 HCF ltac:(cbn; lia))); byteseq|].
    split; [unfold CF; apply bytes_ro_C1; apply (bytes_at_as v _ _ _ (bytes_at_mid v 0x1466e8 pa_common_flags_bytes 244 1 HCF ltac:(cbn; lia))); byteseq|].
    split; [unfold CF; apply bytes_ro_C1; apply (bytes_at_as v _ _ _ (bytes_at_mid v 0x1466e8 pa_common_flags_bytes 260 1 HCF ltac:(cbn; lia))); byteseq|].
    split; [cell Hx 0xa9818 (le8 (Z_to_bv 64 0x607c18)); unfold SSP_GOT, SSP_CELL; apply bytes_ro_C8; exact Hx|].
    split; [exact CAN|].
    split; [cell Hx 0x607e98 (le8 (Z_to_bv 64 4096)); unfold LIBC_PAGESIZE; apply bytes_ro_C8; exact Hx|].
    split; [cell Hx 0xa8bb0 (le8 (Z_to_bv 64 1)); unfold SEALED_GOT; apply bytes_ro_C8; exact Hx|].
    split; [cell Hx 0xa8bb8 (le8 (Z_to_bv 64 0x1466dc)); unfold DYING_GOT, DYING; apply bytes_ro_C8; exact Hx|].
    cell Hx 0x1466dc (le4 (Z_to_bv 64 0)). unfold DYING. apply bytes_ro_C4. exact Hx.
  Qed.

  (* [comment removed for export] *)
  Lemma sk_thr_stats : exists rf rfd mu mdv : Z,
    0 <= rf < 2^64 /\ 0 <= rfd < 2^64 /\ 0 <= mu < 2^64 /\ 0 <= mdv < 2^64 /\
    rw_cells rsegs v (thr + 2840) [C8 (wz rf); C8 (wz rfd)] /\ rw_cells rsegs v (thr + 2888) [C8 (wz mu); C8 (wz mdv)].
  Proof.
    (first [ pose proof ((thr_words A m md AI (thr + 2840) 2 ltac:(unfold off_th_stats; lia) ltac:(unfold off_th_stats; cbn; lia))) as dR_31; dex1 dR_31 as ws1; destruct dR_31 as [L1 R1] | pose proof ((thr_words A m md AI (thr + 2840) 2 ltac:(unfold off_th_stats; lia) ltac:(unfold off_th_stats; cbn; lia))) as dR_31; dand3 dR_31 as ws1 L1 R1 | destruct (thr_words A m md AI (thr + 2840) 2 ltac:(unfold off_th_stats; lia) ltac:(unfold off_th_stats; cbn; lia)) as (ws1 & L1 & R1) ]).
    (first [ pose proof ((thr_words A m md AI (thr + 2888) 2 ltac:(unfold off_th_stats; lia) ltac:(unfold off_th_stats; cbn; lia))) as dR_32; dex1 dR_32 as ws2; destruct dR_32 as [L2 R2] | pose proof ((thr_words A m md AI (thr + 2888) 2 ltac:(unfold off_th_stats; lia) ltac:(unfold off_th_stats; cbn; lia))) as dR_32; dand3 dR_32 as ws2 L2 R2 | destruct (thr_words A m md AI (thr + 2888) 2 ltac:(unfold off_th_stats; lia) ltac:(unfold off_th_stats; cbn; lia)) as (ws2 & L2 & R2) ]).
    destruct ws1 as [|a1 [|b1 [|]]]; cbn in L1; try lia. destruct ws2 as [|a2 [|b2 [|]]]; cbn in L2; try lia. cbn [map] in R1, R2.
    exists (bv_unsigned a1), (bv_unsigned b1), (bv_unsigned a2), (bv_unsigned b2).
    pose proof (zr_word a1). pose proof (zr_word b1). pose proof (zr_word a2). pose proof (zr_word b2). unfold inr64 in *.
    rewrite !Z_to_bv_bv_unsigned. repeat (split; [lia|]). exact (conj R1 R2).
  Qed.

  (* [comment removed for export] *)
  Lemma sk_shadow : bytes_at rsegs v (sh h) (sshadow_live n0) /\ length (sshadow_live n0) = Z.to_nat (msz / 8) /\
                    rw_cells rsegs v (sh h) [CB (Z.to_nat (msz / 8)) (sshadow_live n0)].
  Proof.
    (first [ pose proof (sk_geo) as dR_33; dand11 dR_33 as HLO HAL MSZ MSZAL HHI PH PIN N6 NR H5 PM | pose proof sk_geo as (HLO & HAL & MSZ & MSZAL & HHI & PH & PIN & N6 & NR & H5 & PM) ]). (first [ pose proof (sk_shr) as dR_34; dand4 dR_34 as SHA _ _ SIDE | pose proof sk_shr as (SHA & _ & _ & SIDE) ]).
    (first [ pose proof ((ar_shadow _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI))) as dR_35; dand6 dR_35 as _ _ _ _ SS _ | destruct (ar_shadow _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI)) as (_ & _ & _ & _ & SS & _) ]).
    pose proof (SS p h n0 sk_li) as B. change (p_sb (a_pl A)) with sb in B.
    destruct (free_n0 A m md p n0 AI HL) as [_ US].
    pose proof (Z_div_mod_eq_full msz 4096) as XM. rewrite MSZAL, Z.add_0_r in XM.
    unfold kMaxPrimaryUser, REQ_MAX in NR.
    assert (LEN : length (sshadow_live n0) = Z.to_nat (msz / 8)).
    { unfold sshadow_live, fa8. rewrite !length_app, !repeat_length, US. rewrite (shpat_length_nat n0) by lia.
      pose proof (Z_div_mod_eq_full (n0 + 7) 8). pose proof (Z.mod_pos_bound (n0 + 7) 8 ltac:(lia)). lia. }
    split; [exact B|]. split; [exact LEN|].
    apply (bytes_rw_CB v (sh h) (sshadow_live n0) (Z.to_nat (msz / 8)) B LEN). unfold sh. kung_all. lia.
  Qed.

  (* [comment removed for export] *)
  Section AtIndex.
    Variable i : nat.
    Hypothesis NTH : nth_error chunks i = Some (CS h n0).

    Lemma sk_i : 0 <= Z.of_nat i < nch /\ nth_error sec_words (Z.to_nat (Z.of_nat i)) = Some (Z_to_bv 64 h).
    Proof.
      split; [pose proof (nth_error_Some_lt _ _ _ NTH); lia|]. rewrite Nat2Z.id. exact (sec_words_nth i _ NTH).
    Qed.

    Lemma sk_hdr : rw_cells rsegs v h [C8 (wz h); C8 (wz msz); C8 (wz (needed_size2 n0)); C8 (wz (Z.of_nat i))] /\ 0 <= needed_size2 n0 < 2^64.
    Proof.
      split; [exact (sk_hdr_at i _ NTH)|]. (first [ pose proof ((sk_chunk _ sk_In)) as dR_36; dand7 dR_36 as _ _ _ _ _ _ X | pose proof (sk_chunk _ sk_In) as (_ & _ & _ & _ & _ & _ & X) ]). exact X.
    Qed.

    (* [comment removed for export] *)
    Lemma sk_sep_h : apart h msz pa (8 * nch) /\ apart h msz thr 4096 /\ apart h msz (p_ctx P) 0x10000 /\
                     apart h msz (p_nodes0 P) kDepotNodesBlock /\ apart h msz (p_frames0 P) kStackStoreBlockBytes.
    Proof.
      (first [ pose proof ((sk_sep_fixed i _ NTH)) as dR_37; dand5 dR_37 as D1 D2 D3 D4 D5 | pose proof (sk_sep_fixed i _ NTH) as (D1 & D2 & D3 & D4 & D5) ]). cbn [cs_map cs_n] in *. (first [ pose proof (sk_pa) as dR_38; dand5 dR_38 as _ _ _ _ LE | pose proof sk_pa as (_ & _ & _ & _ & LE) ]).
      pose proof sk_nch as (N1 & _). unfold apart in *. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try assumption. lia.
    Qed.

    (* [comment removed for export] *)
    Lemma sk_hl : let hl := Z_to_bv 64 (cs_map sec_last) in let hla := cs_map sec_last in
      aobj hla 32 /\ hla + 32 <= alloc_ceiling /\ hla mod 8 = 0 /\ bv_unsigned hl = hla /\
      (hla = h \/ apart hla 32 h msz) /\
      (hla = h \/ rw_cells rsegs v hla [C8 (wz hla); C8 (wz (map_size (cs_n sec_last))); C8 (wz (needed_size2 (cs_n sec_last))); C8 (wz (nch - 1))]) /\
      apart hla 32 pa (8 * nch) /\ apart hla 32 thr 4096 /\ apart hla 32 (p_ctx P) 0x10000 /\
      apart hla 32 (p_nodes0 P) kDepotNodesBlock /\ apart hla 32 (p_frames0 P) kStackStoreBlockBytes.
    Proof.
      cbv zeta. (first [ pose proof (sk_last) as dR_39; dand4 dR_39 as E1 IN E2 E3 | pose proof sk_last as (E1 & IN & E2 & E3) ]). (first [ pose proof ((sk_chunk _ IN)) as dR_40; dand7 dR_40 as C1 C2 C3 C4 C5 C6 _ | pose proof (sk_chunk _ IN) as (C1 & C2 & C3 & C4 & C5 & C6 & _) ]).
      (first [ pose proof ((sk_sep_fixed _ _ E1)) as dR_41; dand5 dR_41 as D1 D2 D3 D4 D5 | pose proof (sk_sep_fixed _ _ E1) as (D1 & D2 & D3 & D4 & D5) ]). (first [ pose proof (sk_pa) as dR_42; dand5 dR_42 as _ _ _ _ LE | pose proof sk_pa as (_ & _ & _ & _ & LE) ]). pose proof sk_nch as (N1 & _).
      split; [apply (aobj_sub _ _ _ _ C1); lia|]. split; [lia|]. split; [apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact C2]|]. split; [exact E3|].
      assert (CASE : cs_map sec_last = h \/ (Z.to_nat (nch - 1) <> i)).
      { destruct (Nat.eq_dec (Z.to_nat (nch - 1)) i) as [EQ|NE]; [left| right; exact NE]. rewrite EQ, NTH in E1. injection E1 as <-. reflexivity. }
      split.
      { destruct CASE as [EQ|NE]; [left; exact EQ| right]. pose proof (sk_sep_chunks _ _ _ _ E1 NTH NE) as D. cbn [cs_map cs_n] in D. unfold apart in *. lia. }
      split.
      { destruct CASE as [EQ|NE]; [left; exact EQ| right]. pose proof (sk_hdr_at _ _ E1) as R.
        replace (Z.of_nat (Z.to_nat (nch - 1))) with (nch - 1) in R by lia. exact R. }
      unfold apart in *. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
    Qed.
  End AtIndex.
End SecKit.
