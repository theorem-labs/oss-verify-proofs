(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic AMal9l1 ATransp ABudget.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
#[local] Notation WF := (WF AL_pasan).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Notation wz z := (Z_to_bv 64 z) (only parsing).
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kSpaceReserve, kMaxSize in *.

(* [comment removed for export] *)
Definition secA (A : AState) (mb n : Z) (key : list Z) (nres' : Z) : AState :=
  mkA (a_pl A) (a_reg A) (a_cache_inited A) (a_cache A)
      (<[ sec_user_beg mb := LI (ChS (CS mb n)) n ]> (a_livemap A))
      (a_qthread A) (a_qglobal A) (SR (sr_chunks (a_sec A) ++ [CS mb n]) nres') (fst (depot_putC (a_depot A) key))
      (a_fhint A) (a_fframes A) (a_ia_inited A) (a_oom A) (a_tiny A - is_tiny n)
      (a_qlimbo A) (a_scred A - 1) (a_deadsh A) (a_pcred A) (a_paid A).   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma nth_error_snoc_inv : forall {X} (l : list X) x i y, nth_error (l ++ [x]) i = Some y -> nth_error l i = Some y \/ (i = length l /\ y = x).
Proof.
  intros X l x i y H. destruct (Nat.lt_ge_cases i (length l)) as [L|G].
  - left. rewrite nth_error_app1 in H by exact L. exact H.
  - right. rewrite nth_error_app2 in H by exact G. destruct (i - length l)%nat as [|k] eqn:E; cbn in H; [| destruct k; discriminate].
    injection H as <-. split; [lia| reflexivity].
Qed.
Lemma big_maps_secA : forall A mb n key nres',
  big_maps (secA A mb n key nres') = big_maps A ++ [(mb, map_size n)].
Proof. intros. unfold big_maps, big_maps_, secA. cbn [a_pl a_sec sr_chunks]. rewrite map_app, app_assoc. reflexivity. Qed.
(* [comment removed for export] *)

Section WFsec.
Context {Clg : Ceiling}.
  Context {DR : DepotRep}.
  Variables (A : AState) (v : mem) (mb n : Z) (key : list Z) (nres' : Z).
  Hypothesis AR : WF A /\ arepr LPA AL_pasan [] A v.
  Let W : WF A. Proof. exact (proj1 AR). Qed.
  Hypothesis NR : kMaxPrimaryUser < n < 2^30 + 1.
  Hypothesis MBA : mb mod 4096 = 0.
  Hypothesis MBAPP : app_rangeA AL_pasan mb (map_size n).
  Hypothesis MBC : mb + map_size n <= alloc_ceiling.
  (* [comment removed for export] *)
  Hypothesis APART : forall i b s, nth_error (big_maps A) i = Some (b, s) -> b + s <= mb \/ mb + map_size n <= b.
  Hypothesis NRES : nres' = kChunksBlockCount.
  Hypothesis KEYU : In key (p_dkeys (a_pl A)).
  Hypothesis LIM : as_livebytes A + n <= LIVE_MAX.
  Hypothesis NLV : as_nlive A + 1 <= NLIVE_MAX.
  Hypothesis SCRED : 1 <= as_seccred A.
  Local Notation u := (sec_user_beg mb).
  Local Notation lm := (a_livemap A).
  Local Notation ms := (map_size n).

  Lemma sec_ms_ge : n + 4096 <= ms. Proof. apply map_size_ge. unfold kMaxPrimaryUser in NR. lia. Qed.
  Lemma sec_u_range : mb + 4096 + 16 <= u /\ u + n <= mb + ms /\ u = mb + 6144.
  Proof.
    pose proof (sec_user_end_fits mb n ltac:(lia)) as [F1 F2]. pose proof (needed_size2_secondary n ltac:(lia)).
    pose proof (rounded_size_ge n). unfold sec_user_beg, sec_alloc_beg, kPageSize in *. lia.
  Qed.
  Lemma is_tiny_sec : is_tiny n = 0. Proof. unfold is_tiny, kMaxPrimaryUser in *. destruct (Z.ltb_spec n 16); lia. Qed.

  (* [comment removed for export] *)
  Lemma sec_fresh_chunk : forall s, In s (sr_chunks (a_sec A)) -> cs_map s + map_size (cs_n s) <= mb \/ mb + ms <= cs_map s.
  Proof. intros s Hs. apply In_nth_error' in Hs as [i Hi]. exact (APART _ _ _ (bm_nth_sec A i s Hi)). Qed.
  Lemma sec_fresh_map : ~ In mb (map cs_map (sr_chunks (a_sec A))).
  Proof.
    intros Hin. apply in_map_iff in Hin as (s & E & Hs). pose proof (sec_fresh_chunk s Hs) as D. rewrite E in D.
    pose proof (sec_chunk_bounds A s W Hs) as (B1 & _). pose proof (map_size_ge (cs_n s) ltac:(unfold kMaxPrimaryUser in B1; lia)). pose proof sec_ms_ge. unfold kMaxPrimaryUser in *. lia.
  Qed.
  Lemma sec_fresh_carved : forall ch a, carved A ch -> chunk_lo (a_sb A) ch <= a < chunk_hi (a_sb A) ch -> ~ (mb <= a < mb + ms).
  Proof.
    intros ch a C Ha Hm. destruct ch as [[c' k']|[mb' n0']].
    - pose proof (carved_prim_where A v AR c' k' C) as X. cbn [chunk_lo chunk_hi alloc_beg] in Ha.
      pose proof (proj1 (bm_nth_fixed A)) as E0. pose proof (APART _ _ _ E0) as D. change (a_sb A) with (p_sb (a_pl A)) in *.
      unfold a_b6, a_sb in *. kung_all. lia.
    - unfold carved in C. pose proof (sec_fresh_chunk _ C) as D. cbn [chunk_lo chunk_hi cs_map cs_n] in Ha, D. lia.
  Qed.
  Lemma sec_u_fresh : lm !! u = None.
  Proof.
    destruct (lm !! u) as [li|] eqn:E; [| reflexivity]. exfalso.
    pose proof (known_live A v AR u li E) as K. pose proof (user_in A _ _ K) as [U1 U2].
    destruct (wfV A W) as (V1 & _). (first [ pose proof ((V1 u li E)) as dR_1; dand3 dR_1 as N1 UE _ | pose proof (V1 u li E) as (N1 & UE & _) ]). cbv zeta in UE, N1. rewrite <- UE in U1, U2.
    (first [ pose proof (sec_u_range) as dR_2; dand3 dR_2 as R1 R2 _ | pose proof sec_u_range as (R1 & R2 & _) ]).
    unfold kMaxPrimaryUser in *. apply (sec_fresh_carved (li_chunk li) u (known_carved A v AR _ _ K)); lia.
  Qed.
  Lemma sec_not_live : forall u' li, lm !! u' = Some li -> li_chunk li <> ChS (CS mb n).
  Proof.
    intros u' li Hl E. destruct (wfV A W) as (V1 & _). (first [ pose proof ((V1 u' li Hl)) as dR_3; dand3 dR_3 as _ _ M | pose proof (V1 u' li Hl) as (_ & _ & M) ]). rewrite E in M. cbn in M.
    (first [ dand3 M as _ _ IN | destruct M as (_ & _ & IN) ]). exact (sec_fresh_map (in_map _ _ _ IN)).
  Qed.
  Lemma sec_not_quar : ~ In (ChS (CS mb n)) (quarantined_chunks_ (a_qthread A) (a_qglobal A)).
  Proof.
    intros Hin. unfold quarantined_chunks_ in Hin. apply in_map_iff in Hin as (e & E & He).
    pose proof (qentry_wf A v AR e He) as Q. unfold wf_qentry_ in Q. rewrite E in Q. (first [ dand4 Q as _ _ _ IN | destruct Q as (_ & _ & _ & IN) ]).
    exact (sec_fresh_map (in_map _ _ _ IN)).
  Qed.

  Theorem sec_WF : WF (secA A mb n key nres').
  Proof.
    pose proof sec_u_fresh as FR. (first [ pose proof (sec_u_range) as dR_6; dand3 dR_6 as UR1 UR2 UE | pose proof sec_u_range as (UR1 & UR2 & UE) ]). pose proof is_tiny_sec as IT0. pose proof sec_ms_ge as MSG.
    pose proof (wf_sec_eager A W) as [_ L8]. unfold kMaxPrimaryUser in NR.
    destruct W as [wP wM wR wC wX wV wQ wS wD wF wB wI wE wJ wN] eqn:EW. clear EW.
    constructor; cbn [secA a_pl a_reg a_cache_inited a_cache a_livemap a_qthread a_qglobal a_sec a_depot a_fhint a_fframes a_ia_inited a_oom a_tiny a_qlimbo a_scred a_deadsh a_pcred a_paid a_sb a_fs sr_chunks sr_reserved].
    - exact wP.
    - (* [comment removed for export] *)
      unfold wf_bigmaps_. pose proof (big_maps_secA A mb n key nres') as BE. unfold big_maps in BE. cbn [secA a_pl a_sec] in BE. rewrite BE. clear BE.
      destruct wM as [D B]. fold (big_maps A) in D, B |- *. split.
      + intros i j bi si bj sj Hi Hj NE.
        apply nth_error_snoc_inv in Hi. apply nth_error_snoc_inv in Hj.
        destruct Hi as [Hi|[-> Ei]]; destruct Hj as [Hj|[-> Ej]].
        * exact (D i j bi si bj sj Hi Hj NE).
        * injection Ej as E1 E2. subst bj sj. destruct (APART _ _ _ Hi); lia.
        * injection Ei as E1 E2. subst bi si. destruct (APART _ _ _ Hj); lia.
        * exfalso. exact (NE eq_refl).
      + intros b s Hin. apply in_app_iff in Hin as [Hin|[E|[]]]; [exact (B b s Hin)|]. injection E as E1 E2. subst b s.
        apply app_rangeA_arith in MBAPP. pose proof alloc_ceiling_val. lia.
    - exact wR.
    - exact wC.
    - (* [comment removed for export] *)
      intros c' k Hc' Hk. pose proof (wX c' k Hc' Hk) as X. cbv zeta in *.
      assert (VV : p_live_ (<[u:=LI (ChS (CS mb n)) n]> lm) c' k <-> p_live_ lm c' k).
      { unfold p_live_. split.
        - ((first [ intro dR_16; dex2 dR_16 as u0 n0; rename dR_16 into Hu0 | intro dR_16; dand3 dR_16 as u0 n0 Hu0 | intros (u0 & n0 & Hu0) ])). destruct (decide (u0 = u)) as [->|NEu].
          + rewrite lookup_insert_eq in Hu0. discriminate.
          + rewrite lookup_insert_ne in Hu0 by (intros E; apply NEu; symmetry; exact E). exists u0, n0. exact Hu0.
        - ((first [ intro dR_17; dex2 dR_17 as u0 n0; rename dR_17 into Hu0 | intro dR_17; dand3 dR_17 as u0 n0 Hu0 | intros (u0 & n0 & Hu0) ])). exists u0, n0. rewrite lookup_insert_ne; [exact Hu0|]. intros E. rewrite <- E in Hu0. rewrite FR in Hu0. discriminate. }
      rewrite VV. exact X.
    - (* [comment removed for export] *) (first [ dand3 wV as V1 V2 V3 | destruct wV as (V1 & V2 & V3) ]). split; [| split].
      + intros u0 li Hl. destruct (decide (u0 = u)) as [->|NEu].
        * rewrite lookup_insert_eq in Hl. injection Hl as <-. cbv zeta. cbn [li_n li_chunk].
          split; [unfold REQ_MAX, kMaxPrimaryUser in *; lia|]. split; [reflexivity|]. split; [unfold kMaxPrimaryUser; lia|]. split; [reflexivity|].
          apply in_app_iff. right. left. reflexivity.
        * rewrite lookup_insert_ne in Hl by congruence. (first [ pose proof ((V1 u0 li Hl)) as dR_8; dand3 dR_8 as N1 N2 N3 | pose proof (V1 u0 li Hl) as (N1 & N2 & N3) ]). cbv zeta. split; [exact N1|]. split; [exact N2|].
          destruct (li_chunk li) as [[c' k']|[mb' n0']]; [exact N3|]. (first [ dand3 N3 as A1 A2 A3 | destruct N3 as (A1 & A2 & A3) ]). split; [exact A1|]. split; [exact A2|].
          apply in_app_iff. left. exact A3.
      + intros u1 u2 li1 li2 H1 H2 NEQ.
        destruct (decide (u1 = u)) as [->|N1]; destruct (decide (u2 = u)) as [->|N2]; try congruence.
        * rewrite lookup_insert_eq in H1. injection H1 as <-. rewrite lookup_insert_ne in H2 by congruence. cbn [li_chunk].
          intros E. exact (sec_not_live _ _ H2 (eq_sym E)).
        * rewrite lookup_insert_eq in H2. injection H2 as <-. rewrite lookup_insert_ne in H1 by congruence. cbn [li_chunk].
          exact (sec_not_live _ _ H1).
        * rewrite lookup_insert_ne in H1 by congruence. rewrite lookup_insert_ne in H2 by congruence. exact (V2 _ _ _ _ H1 H2 NEQ).
      + rewrite as_livebytes_insert by exact FR. cbn [li_n]. unfold as_livebytes, as_livebytes_ in LIM. unfold as_livebytes_. lia.
    - (* [comment removed for export] *) (first [ dand8 wQ as Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 | destruct wQ as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8) ]).
      assert (WB : forall b, wf_batch_ (a_reg A) (a_sec A) b -> wf_batch_ (a_reg A) (SR (sr_chunks (a_sec A) ++ [CS mb n]) nres') b).
      { (intros b; (first [ intro dR_18; dand3 dR_18 as X1 X2 X3 | intros (X1 & X2 & X3) ])). split; [exact X1|]. split; [exact X2|]. apply Forall_forall. intros e He.
        pose proof (proj1 (Forall_forall _ _) X3 e He) as Y. unfold wf_qentry_ in *. destruct Y as [Y1 Y2]. split; [exact Y1|].
        destruct (qe_chunk e) as [[c' k']|[mb' n0']]; [exact Y2|]. (first [ dand3 Y2 as Z1 Z2 Z3 | destruct Y2 as (Z1 & Z2 & Z3) ]). cbn [sr_chunks].
        split; [exact Z1|]. split; [exact Z2|]. apply in_app_iff. left. exact Z3. }
      split; [apply Forall_forall; intros b Hb; apply WB; exact (proj1 (Forall_forall _ _) Q1 b Hb)|].
      split; [apply Forall_forall; intros b Hb; apply WB; exact (proj1 (Forall_forall _ _) Q2 b Hb)|].
      repeat (split; [assumption|]).
      intros u0 li Hl. destruct (decide (u0 = u)) as [->|NEu].
      + rewrite lookup_insert_eq in Hl. injection Hl as <-. cbn [li_chunk]. exact sec_not_quar.
      + rewrite lookup_insert_ne in Hl by congruence. exact (Q8 _ _ Hl).
    - (* [comment removed for export] *) (first [ dand5 wS as S1 S2 S3 S4 S5 | destruct wS as (S1 & S2 & S3 & S4 & S5) ]). unfold wf_sec_. cbn [sr_chunks sr_reserved]. split; [| split; [| split; [| split]]].
      + rewrite map_app. cbn [map cs_map]. apply NoDup_List. apply List.NoDup_app; [apply NoDup_List; exact S1| constructor; [intros []| constructor]|].
        intros x Hx [<-|[]]. exact (sec_fresh_map Hx).
      + rewrite app_length. cbn [length]. rewrite NRES. unfold kChunksBlockCount. lia.
      + right. exact NRES.
      + intros s Hs. apply in_app_iff in Hs as [Hs|[<-|[]]]; [exact (S4 s Hs)|]. cbn [cs_n cs_map].
        split; [unfold REQ_MAX, kMaxPrimaryUser in *; lia|]. split; [exact MBA|]. split; [exact MBAPP| exact MBC].
      + intros s Hs. apply in_app_iff in Hs as [Hs|[<-|[]]].
        * destruct (S5 s Hs) as [(u0 & Hu0)|Hq]; [left| right; exact Hq]. exists u0.
          rewrite lookup_insert_ne; [exact Hu0|]. intros E. rewrite <- E in Hu0. rewrite FR in Hu0. discriminate.
        * left. exists u. cbn [cs_n]. rewrite lookup_insert_eq. reflexivity.
    - (* [comment removed for export] *) (first [ dand3 wD as INC ND NN | destruct wD as (INC & ND & NN) ]). split; [| split; [apply depot_putC_nodup; exact ND| apply depot_putC_nonnil; exact NN]].
      apply Forall_forall. intros k Hk. assert (INC' : incl (a_depot A) (p_dkeys (a_pl A))) by (intros x Hx; exact (proj1 (Forall_forall _ _) INC x Hx)).
      exact (depot_putC_incl _ _ _ INC' KEYU k Hk).
    - exact wF.
    - (* [comment removed for export] *) (first [ dand5 wB as B1 B2 B3 B4 B5 | destruct wB as (B1 & B2 & B3 & B4 & B5) ]). unfold as_nlive, as_tinycred in NLV.
      unfold wf_budget_. rewrite as_livebytes_insert, as_nlive_insert, tiny_live_insert by exact FR. cbn [li_n]. rewrite IT0 in *.
      OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
    - exact wI.
    - (* [comment removed for export] *)
      (first [ dand4 wE as E1 E2 E3 E4 | destruct wE as (E1 & E2 & E3 & E4) ]). unfold as_seccred in SCRED. unfold wf_dead_. cbn [sr_chunks]. rewrite app_length. cbn [length]. rewrite Nat2Z.inj_add. cbn [Z.of_nat Pos.of_succ_nat].
      split; [lia|]. split; [exact E2|]. split; [lia|]. unfold kDeadShadowBytes in *. lia.
    - exact wJ.
    - (* [comment removed for export] *)
      apply (wf_prim_mono lm _ (a_qthread A) (a_qthread A) (a_qglobal A) (a_qglobal A) (a_paid A) (a_pcred A)); [| exact wN].
      intros c k Hc [V|Q]; [| right; exact Q]. destruct (p_live_insert_inv lm u _ c k FR V) as [V0|E]; [left; exact V0| cbn [li_chunk] in E; discriminate E].
  Qed.

  (* [comment removed for export] *)
  Lemma sec_live_new : as_live (secA A mb n key nres') u = Some n.
  Proof. unfold as_live, as_live_. cbn [secA a_livemap]. rewrite lookup_insert_eq. reflexivity. Qed.
  Lemma sec_live_old : as_live A u = None.
  Proof. unfold as_live, as_live_. rewrite sec_u_fresh. reflexivity. Qed.
  Lemma sec_live_other : forall q, q <> u -> as_live (secA A mb n key nres') q = as_live A q.
  Proof. intros q Hq. unfold as_live, as_live_. cbn [secA a_livemap]. rewrite lookup_insert_ne by congruence. reflexivity. Qed.
  Lemma sec_livebytes : as_livebytes (secA A mb n key nres') = as_livebytes A + n.
  Proof. unfold as_livebytes. cbn [secA a_livemap]. rewrite (as_livebytes_insert _ _ _ sec_u_fresh). cbn [li_n]. lia. Qed.
  Lemma sec_nlive : as_nlive (secA A mb n key nres') = as_nlive A + 1.
  Proof. unfold as_nlive. cbn [secA a_livemap]. rewrite (as_nlive_insert _ _ _ sec_u_fresh). reflexivity. Qed.
  Lemma sec_seccred : as_seccred (secA A mb n key nres') = as_seccred A - (if Z.ltb kMaxPrimaryUser n then 1 else 0).
  Proof. unfold as_seccred. cbn [secA a_scred]. destruct (Z.ltb_spec kMaxPrimaryUser n); lia. Qed.
  Lemma sec_tinycred : as_tinycred (secA A mb n key nres') = as_tinycred A - (if Z.ltb n 16 then 1 else 0).
  Proof. unfold as_tinycred. cbn [secA a_tiny]. unfold is_tiny. reflexivity. Qed.
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma sec_hull : pa_hull (secA A mb n key nres') =
    pa_image_ivs ++ (hull_of (fixed_regions_ AL_pasan (a_pl A) ++ classes_regions_ (a_sb A) (a_reg A) 31 ++ sec_regions_ (sr_chunks (a_sec A)))
                     ++ hull_of [(mb, ms); shadow_region mb ms]) ++ a_deadsh A ++ p_extra (a_pl A).
  Proof.
    unfold pa_hull, ahull_of, ahull_of_, aregions_. cbn [secA a_pl a_reg a_sec a_deadsh sr_chunks].
    unfold sec_regions_. rewrite flat_map_app. cbn [flat_map]. rewrite app_nil_r. rewrite <- hull_of_app. rewrite !app_assoc. reflexivity.
  Qed.
  Lemma sec_hull_le : hull_le (pa_hull A) (pa_hull (secA A mb n key nres')).
  Proof.
    rewrite sec_hull. unfold pa_hull, ahull_of, ahull_of_, aregions_. change (p_sb (a_pl A)) with (a_sb A).
    apply hull_le_incl. intros x Hx. rewrite !in_app_iff in Hx. rewrite !in_app_iff.
    destruct Hx as [Hx|[Hx|Hx]]; [left; exact Hx| right; left; left; exact Hx| right; right; exact Hx].
  Qed.
  (* [comment removed for export] *)
  Lemma sec_lhull : pa_lhull (secA A mb n key nres') =
    (hull_of (lfixed_regions_ AL_pasan (a_pl A) ++ lclasses_regions_ (a_sb A) (a_reg A) 31 ++ lsec_regions_ (sr_chunks (a_sec A)))
       ++ hull_of [shadow_region mb ms]) ++ a_deadsh A ++ p_extra (a_pl A).
  Proof.
    unfold pa_lhull, alhull_of, alhull_of_, alregions_. cbn [secA a_pl a_reg a_sec a_deadsh sr_chunks].
    unfold lsec_regions_. rewrite map_app. cbn [map]. rewrite <- hull_of_app. rewrite !app_assoc. reflexivity.
  Qed.
  Lemma sec_lhull_le : hull_le (pa_lhull A) (pa_lhull (secA A mb n key nres')).
  Proof.
    rewrite sec_lhull. unfold pa_lhull, alhull_of, alhull_of_, alregions_. change (p_sb (a_pl A)) with (a_sb A).
    apply hull_le_incl. intros x Hx. rewrite !in_app_iff in Hx. rewrite !in_app_iff.
    destruct Hx as [Hx|Hx]; [left; left; exact Hx| right; exact Hx].
  Qed.
  Lemma sec_eager : pa_eager (secA A mb n key nres') = pa_eager A + ms + 8 * (nres' - sr_reserved (a_sec A)).
  Proof.
    unfold pa_eager, aeager_of, aeager_of_. cbn [secA a_pl a_reg a_sec sr_chunks sr_reserved]. unfold sec_eager_.
    rewrite fold_right_app. cbn [fold_right cs_n].
    assert (E : forall l z, fold_right (fun s acc => map_size (cs_n s) + acc) z l = fold_right (fun s acc => map_size (cs_n s) + acc) 0 l + z).
    { induction l as [|s l IH]; intros z; cbn; [lia|]. rewrite IH. lia. }
    rewrite E. lia.
  Qed.
End WFsec.
