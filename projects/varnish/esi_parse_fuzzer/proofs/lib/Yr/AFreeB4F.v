(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts AMalmys.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeB1 AFreeB2 ATransp AFreeB3 AFreeB4 AFreeB4c.

Module AFreeB3F.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts AMalmys.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeB1 AFreeB2 ATransp AFreeB3.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.  (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Stdlib.omega.PreOmega.Z.euclidean_division_equations_cleanup; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Stdlib.micromega.Zify.zify_internal_to_euclidean_division_equations ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_fast_euclid.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac hot2_mid := match goal with H : context [Z.modulo _ _] |- _ => idtac | H : context [Z.div _ _] |- _ => idtac end;
  (repeat match goal with H : context [Z.modulo _ _] |- _ => clear H | H : context [Z.div _ _] |- _ => clear H end); Zify.zify; xlia zchecker.
Local Ltac lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dl_first | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Zify.zify; xlia zchecker | hot2_mid | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
#[local] Notation WF := (WF AL_pasan).   (* [comment removed for export] *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Notation wz z := (Z_to_bv 64 z) (only parsing).
Ltac alc_h H := cbn [al_instance al_kHighMemEnd_var al_kMidMemBeg_var al_kMidMemEnd_var al_malloc_context_size al_can_poison_memory al_page_size_cache
       al_may_return_null al_rss_limit_exceeded al_dying_flag al_malloc_hooks al_internal_alloc_inited al_internal_allocator_inst
       al_theDepot al_depot_n_uniq_ids al_depot_nodes_map1 al_stackStore al_tp AL_pasan cl_tp cl_shared cl_consts cl_segs LPA] in H.
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kSpaceReserve, kMaxSize in *.

(* [comment removed for export] *)
Definition freeA3 (A : AState) (p : Z) (qt' qg' : list batch) (cache' : Z -> pcache) (D' : list (list Z)) (ia' : bool) (reg' : Z -> region) : AState :=
  mkA (a_pl A) reg' (a_cache_inited A) cache'
      (free_lm A p) qt' qg' (a_sec A) D'
      (a_fhint A) (a_fframes A) ia' (a_oom A) (a_tiny A) (a_qlimbo A) (a_scred A) (a_deadsh A) (a_pcred A) (a_paid A).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rr24 (ri a : Z) : Prop :=
  (ri + 3072 <= a < ri + 3080) \/ (ri + 3088 <= a < ri + 3096) \/ (ri + 3144 <= a < ri + 3152).
Lemma rr24_in : forall ri a, rr24 ri a -> ri + 3072 <= a < ri + 3152.
Proof. intros ri a [H|[H|H]]; lia. Qed.
Lemma nth_error_firstn_SomeF : forall {X} (l : list X) m i x, nth_error (firstn m l) i = Some x -> nth_error l i = Some x.
Proof. intros X l m. revert l. induction m as [|m IH]; intros [|y l] [|i] x H; cbn in *; try discriminate; eauto. Qed.

Section FreeRepr3.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (A : AState) (v : mem) (p n0 : Z) (li : liveinfo) (sp : word) (v' : mem) (lo : Z).
  Hypothesis AR : WF A /\ @arepr _ DepotRepL LPA AL_pasan [] A v.
  Hypothesis LU : a_livemap A !! p = Some li.
  Hypothesis LN : li_n li = n0.
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp.
  Local Notation thr := (p_thr (a_pl A)).
  Local Notation sb := (a_sb A).
  Local Notation ch := (li_chunk li).
  Local Notation r8 := ((n0 + 7) / 8).
  Local Notation n0a := (p_nodes0 (a_pl A)).
  Local Notation f0 := (p_frames0 (a_pl A)).
  Local Notation qt := (a_qthread A).
  Local Notation qg := (a_qglobal A).

  (* [comment removed for export] *)
  Variables (qt' qg' : list batch) (cache' : Z -> pcache) (D' : list (list Z)) (ia' : bool).
  Variable reg' : Z -> region.
  (* [comment removed for export] *)
  Definition cf24 (k : Z) : Prop := p_cached_ (a_cache A) kQuarantineBatchClass k \/ p_free_ (a_reg A) kQuarantineBatchClass k.
  (* [comment removed for export] *)
  Variable BX : Z -> Prop.
  Hypothesis BXW : forall a, BX a ->
       (exists b, In b (qt ++ qg) /\ batch_addr sb b <= a < batch_addr sb b + kQuarantineBatchBytes)
    \/ (thr + 2128 <= a < thr + 2208)      (* [comment removed for export] *)
    \/ (thr + 2784 <= a < thr + 2792)      (* [comment removed for export] *)
    \/ (exists k, cf24 k /\
                  chunk_addr sb kQuarantineBatchClass k <= a < chunk_addr sb kQuarantineBatchClass k + kQuarantineBatchBytes)
    \/ xblk a
    \/ rr24 (a_ri A) a.                 (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis MU : forall a, 0 <= a < 2^64 -> ~ W0 lo (bv_unsigned sp) thr p r8 n0a f0 a -> ~ BX a -> v' (wz a) = v (wz a).
  (* [comment removed for export] *)
  Hypothesis NN : forall a, 0 <= a -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> a < 2^64 -> v (Z_to_bv 64 a) <> None -> v' (Z_to_bv 64 a) <> None.
  Let WF0 : WF A. Proof. exact (proj1 AR). Qed.
  Let R : @arepr _ DepotRepL LPA AL_pasan [] A v. Proof. exact (proj2 AR). Qed.

  (* [comment removed for export] *)
  #[using="LN LU AR p v Clg"] Lemma KN : known A ch n0. Proof. rewrite <- LN. exact (known_live A v AR p li LU). Qed.
  #[using="LN LU AR n0 p v Clg"] Lemma CV : carved A ch. Proof. exact (known_carved A v AR _ _ KN). Qed.
  Let CQB : 1 <= kQuarantineBatchClass <= 30. Proof. unfold kQuarantineBatchClass. lia. Qed.
  #[using="CQB AR v Clg"] Lemma cf_carved : forall k, cf24 k -> carved A (ChP (CP kQuarantineBatchClass k)).
  Proof. intros k [C|F]; [exact (cached_carved A v AR _ k CQB C)| exact (free_carved A v AR _ k CQB F)]. Qed.
  #[using="CQB AR v Clg"] Lemma live_not_cf : forall u li' k, a_livemap A !! u = Some li' -> cf24 k -> li_chunk li' <> ChP (CP kQuarantineBatchClass k).
  Proof. intros u li' k Hl [C|F]; [exact (live_not_cached A v AR u li' _ k Hl CQB C)| exact (live_not_free A v AR u li' _ k Hl CQB F)]. Qed.
  #[using="CQB WF0 AR v Clg"] Lemma quar_not_cf : forall e k, In e (q_entries (qt ++ qg)) -> cf24 k -> qe_chunk e <> ChP (CP kQuarantineBatchClass k).
  Proof.
    intros e k He [C|F]; [exact (quar_not_cached A v AR e _ k He CQB C)|].
    intros E. pose proof (free_carved A v AR _ k CQB F) as [_ Hk].
    pose proof (wfX A WF0 kQuarantineBatchClass k CQB Hk) as X. cbv zeta in X. (first [ dand5 X as _ _ _ NFQ _ | destruct X as (_ & _ & _ & NFQ & _) ]). apply NFQ. split; [exact F|].
    exists (qe_n e). rewrite <- E. destruct e; exact He.
  Qed.

  #[using="WF0 LN LU AR v"] Lemma GEO :
    p mod 16 = 0 /\ 0x60a000 <= chunk_lo sb ch /\ chunk_lo sb ch <= p + -16 /\ p + 8 * r8 <= chunk_hi sb ch /\ chunk_hi sb ch <= alloc_ceiling /\
    1 <= n0 < REQ_MAX /\ n0 <= 8 * r8 < n0 + 8 /\ p = user_of sb ch n0 /\
    4096 <= thr /\ thr + 4096 <= alloc_ceiling /\
    4096 <= n0a /\ n0a + kDepotNodesBlock <= alloc_ceiling /\ 4096 <= f0 /\ f0 + kStackStoreBlockBytes <= alloc_ceiling /\
    0x7fff8200 <= sh p /\ sh p + r8 <= kHighMemBeg /\
    (140735332483072 <= alloc_ceiling <= 140737479966720) /\ bv_unsigned sp < 2^64.
  (* [comment removed for export] *)
  Proof.
    (first [ pose proof ((wfV A WF0)) as dR_2; dand3 dR_2 as V1 _ _ | destruct (wfV A WF0) as (V1 & _ & _) ]). (first [ pose proof ((V1 p li LU)) as dR_3; dand3 dR_3 as N U C | pose proof (V1 p li LU) as (N & U & C) ]). cbv zeta in N, U, C. rewrite LN in N, U, C.
    (first [ pose proof ((place_facts A WF0)) as dR_4; dand5 dR_4 as Pthr _ Pn0 Pf0 _ | pose proof (place_facts A WF0) as (Pthr & _ & Pn0 & Pf0 & _) ]). cbv zeta in Pthr, Pn0, Pf0. pose proof alloc_ceiling_val as CE.
    (first [ dand3 Pthr as Pthr PthrC _ | destruct Pthr as (Pthr & PthrC & _) ]). (first [ dand3 Pn0 as Pn0 Pn0C _ | destruct Pn0 as (Pn0 & Pn0C & _) ]). (first [ dand3 Pf0 as Pf0 Pf0C _ | destruct Pf0 as (Pf0 & Pf0C & _) ]).
    apply app_facts in Pthr. apply app_facts in Pn0. apply app_facts in Pf0.
    pose proof (Z_div_mod_eq_full (n0 + 7) 8) as D1. pose proof (Z.mod_pos_bound (n0 + 7) 8 ltac:(lia)) as D2.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    assert (CH : p mod 16 = 0 /\ 0x60a000 <= chunk_lo sb ch /\ chunk_lo sb ch <= p + -16 /\ p + 8 * r8 <= chunk_hi sb ch /\ chunk_hi sb ch <= alloc_ceiling).
    { (first [ pose proof ((carved_range A v AR ch CV)) as dR_8; dand3 dR_8 as CL1 CL2 CL3 | pose proof (carved_range A v AR ch CV) as (CL1 & CL2 & CL3) ]). destruct (li_chunk li) as [[c k]|[mb nn]]; cbn [chunk_lo chunk_hi alloc_beg user_of] in *.
      - (first [ dand3 C as N2 Hc Hk | destruct C as (N2 & Hc & Hk) ]). pose proof (class_of_range n0 ltac:(lia)) as CR. rewrite <- Hc in CR.
        (first [ pose proof ((primary_layout sb c k n0 CR ltac:(lia) Hc)) as dR_10; dand5 dR_10 as L1 L2 L3 L5 L4 | pose proof (primary_layout sb c k n0 CR ltac:(lia) Hc) as (L1 & L2 & L3 & L5 & L4) ]). cbn [user_of alloc_beg] in *.
        (first [ pose proof ((carved_chunk_bounds A c k WF0 CR Hk)) as dR_11; dand4 dR_11 as B1 B2 B3 B4 | pose proof (carved_chunk_bounds A c k WF0 CR Hk) as (B1 & B2 & B3 & B4) ]). pose proof (class_size_mod32 c CR) as CM.
        assert (PM : p mod 16 = 0) by (rewrite U; apply user_beg_mod16; exact B3). rewrite <- U in *.
        split; [exact PM|]. split; [lia|]. split; [lia|]. split; [| lia].
        apply roundup8_le; [apply (mod0_down _ 16 8); [exists 2; reflexivity| exact PM] | | exact L2].
        rewrite Z.add_mod by lia. rewrite (mod0_down _ 32 8 ltac:(exists 4; reflexivity) B3), (mod0_down _ 32 8 ltac:(exists 4; reflexivity) CM). reflexivity.
      - (first [ dand3 C as N2 -> Hin | destruct C as (N2 & -> & Hin) ]). (first [ pose proof ((secondary_layout mb n0 N2)) as dR_13; dand7 dR_13 as S1 S2 S3 S4 S5 S6 S7 | pose proof (secondary_layout mb n0 N2) as (S1 & S2 & S3 & S4 & S5 & S6 & S7) ]). cbn [user_of alloc_beg] in *.
        (first [ pose proof ((sec_chunk_bounds A _ WF0 Hin)) as dR_14; dand5 dR_14 as B1 B2 B3 B4 B5 | pose proof (sec_chunk_bounds A _ WF0 Hin) as (B1 & B2 & B3 & B4 & B5) ]). cbn [cs_map cs_n] in *.
        pose proof (map_size_page n0) as MP.
        assert (PM : p mod 16 = 0). { rewrite U, S6. rewrite Z.add_mod by lia. rewrite (mod0_down mb 4096 16 ltac:(exists 256; reflexivity) B2). reflexivity. }
        rewrite <- U in *.
        split; [exact PM|]. split; [lia|]. split; [unfold kPageSize in *; lia|]. split; [| lia].
        apply roundup8_le; [apply (mod0_down _ 16 8); [exists 2; reflexivity| exact PM] | | lia].
        rewrite Z.add_mod by lia. rewrite (mod0_down _ 4096 8 ltac:(exists 512; reflexivity) B2), (mod0_down _ kPageSize 8 ltac:(exists 512; reflexivity) MP). reflexivity. }
    (first [ dand5 CH as PM H1 H2 H3 H4 | destruct CH as (PM & H1 & H2 & H3 & H4) ]).
    assert (SE : sh (p + 8 * r8) = sh p + r8).
    { unfold sh. rewrite (Z.mul_comm 8 r8), Z.div_add by lia. lia. }
    pose proof (carved_app A v AR ch CV) as CA. (first [ pose proof ((app_facts _ _ CA)) as dR_16; dand5 dR_16 as CA1 CA2 CA3 CA4 [CA5|CA5] | pose proof (app_facts _ _ CA) as (CA1 & CA2 & CA3 & CA4 & [CA5|CA5]) ]).
    - pose proof (sh_lowapp_range p ltac:(kung_all; unfold kLowShadowMapBeg in *; lia)) as [S1 S2]. pose proof (sh_lowapp_range (p + 8 * r8 - 8) ltac:(kung_all; unfold kLowShadowMapBeg in *; lia)) as [S3 S4].
      assert (SE' : sh (p + 8 * r8 - 8) = sh p + r8 - 1) by (unfold sh; replace (p + 8 * r8 - 8) with (p + (r8 - 1) * 8) by lia; rewrite Z.div_add by lia; lia).
      OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try assumption; try (kung_all; lia).
    - pose proof (sh_high_range p ltac:(kung_all; lia)) as [S1 S2]. pose proof (sh_high_range (p + 8 * r8) ltac:(kung_all; lia)) as [S3 S4].
      OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try assumption; try (kung_all; lia).
  Qed.

  (* [comment removed for export] *)
  #[using="WF0 LN LU AR n0 p v"] Lemma GEOP : aobj (chunk_lo sb ch) (chunk_hi sb ch - chunk_lo sb ch) /\ aobj thr 4096 /\ aobj n0a kDepotNodesBlock /\ aobj f0 kStackStoreBlockBytes.
  Proof.
    (first [ pose proof ((place_facts A WF0)) as dR_17; dand5 dR_17 as Pthr _ Pn0 Pf0 _ | pose proof (place_facts A WF0) as (Pthr & _ & Pn0 & Pf0 & _) ]). cbv zeta in Pthr, Pn0, Pf0.
    destruct Pthr as (Pthr & _). destruct Pn0 as (Pn0 & _). destruct Pf0 as (Pf0 & _).
    split; [| split; [| split]]; apply (proj1 (aobj_app_rangeA _ _)); [exact (carved_app A v AR ch CV)| exact Pthr| exact Pn0| exact Pf0].
  Qed.
  (* [comment removed for export] *)
  #[using="WF0 LN LU AR sp v Clg"] Lemma GEOS : (chunk_hi sb ch <= kLowShadowMapBeg /\ 0x7fff8200 <= sh p /\ sh p + r8 <= 0x8fff6e00)
               \/ (kHighMemBeg <= chunk_lo sb ch /\ kHighShadowMapBeg <= sh p /\ sh p + r8 <= kHighMemBeg).
  Proof.
    (first [ pose proof (GEO) as dR_18; dand9 dR_18 as PM H1 H2 H3 H4 N1 N2 PU _ | pose proof GEO as (PM & H1 & H2 & H3 & H4 & N1 & N2 & PU & _) ]). pose proof alloc_ceiling_val as CE.
    pose proof (carved_app A v AR ch CV) as CA. (first [ pose proof ((app_facts _ _ CA)) as dR_19; dand5 dR_19 as CA1 CA2 CA3 CA4 [CA5|CA5] | pose proof (app_facts _ _ CA) as (CA1 & CA2 & CA3 & CA4 & [CA5|CA5]) ]).
    - left. pose proof (sh_lowapp_range p ltac:(kung_all; unfold kLowShadowMapBeg in *; lia)) as [S1 S2].
      pose proof (sh_lowapp_range (p + 8 * r8 - 8) ltac:(kung_all; unfold kLowShadowMapBeg in *; lia)) as [S3 S4].
      assert (SE' : sh (p + 8 * r8 - 8) = sh p + r8 - 1) by (unfold sh; replace (p + 8 * r8 - 8) with (p + (r8 - 1) * 8) by lia; rewrite Z.div_add by lia; lia).
      kung_all. lia.
    - right. pose proof (sh_high_range p ltac:(kung_all; lia)) as [S1 S2]. pose proof (sh_high_range (p + 8 * r8) ltac:(kung_all; lia)) as [S3 S4].
      assert (SE : sh (p + 8 * r8) = sh p + r8) by (unfold sh; rewrite (Z.mul_comm 8 r8), Z.div_add by lia; lia).
      kung_all. lia.
  Qed.
  Ltac geop := let Gc := fresh "Gc" in let Gt := fresh "Gt" in let Gn := fresh "Gn" in let Gf := fresh "Gf" in let Gs := fresh "Gs" in
    (first [ pose proof (GEOP) as dR_20; dand4 dR_20 as Gc Gt Gn Gf | pose proof GEOP as (Gc & Gt & Gn & Gf) ]); aobj_lin1 Gc; aobj_lin1 Gt; aobj_lin1 Gn; aobj_lin1 Gf;
    pose proof GEOS as Gs; unfold kLowShadowMapBeg, kHighShadowMapBeg, kHighMemBeg in Gs.

  (* [comment removed for export] *)
  #[using="WF0 LN LU AR n0 p v"] Lemma RIW : kHighMemBeg <= a_ri A /\ a_ri A + 4096 <= alloc_ceiling /\ a_ri A = sb + kSpaceSize /\
              (a_ri A + 4096 <= thr \/ thr + 4096 <= a_ri A) /\
              (a_ri A + 4096 <= n0a \/ n0a + kDepotNodesBlock <= a_ri A) /\
              (a_ri A + 4096 <= f0 \/ f0 + kStackStoreBlockBytes <= a_ri A) /\
              (chunk_hi sb ch <= a_ri A \/ a_ri A + 4096 <= chunk_lo sb ch).
  Proof.
    (first [ pose proof ((sb_facts A WF0)) as dR_21; dand5 dR_21 as _ _ HB6 RSB SCE | pose proof (sb_facts A WF0) as (_ & _ & HB6 & RSB & SCE) ]). (first [ pose proof ((bm_nth_fixed A)) as dR_22; dand10 dR_22 as E0 _ _ _ E4 _ _ E7 E8 _ | pose proof (bm_nth_fixed A) as (E0 & _ & _ & _ & E4 & _ & _ & E7 & E8 & _) ]).
    pose proof (bm_sep A 0 4 _ _ _ _ WF0 E0 E4 ltac:(lia)) as D4. pose proof (bm_sep A 0 7 _ _ _ _ WF0 E0 E7 ltac:(lia)) as D7.
    pose proof (bm_sep A 0 8 _ _ _ _ WF0 E0 E8 ltac:(lia)) as D8.
    pose proof (carved_apart_ri A v AR ch CV) as DC.
    unfold a_ri, p_ri, a_b6, a_sb, a_thr, a_nodes0, a_frames0 in *. kung_all. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="WF0 MU BXW BX LO LN LU AR Clg"] Lemma AG_gen : forall a, 0 <= a < 2^64 ->
    ~ (lo <= a < bv_unsigned sp) -> ~ (thr <= a < thr + 4096) ->
    ~ (chunk_lo sb ch <= a < chunk_hi sb ch) ->
    ~ (0x187288 <= a < 0x5d72a8) -> ~ (n0a <= a < n0a + 0x100000) -> ~ (f0 <= a < f0 + 0x800000) -> ~ (sh p <= a < sh p + r8) ->
    ~ (exists b, In b (qt ++ qg) /\ batch_addr sb b <= a < batch_addr sb b + kQuarantineBatchBytes) ->
    ~ (exists k, cf24 k /\ chunk_addr sb kQuarantineBatchClass k <= a < chunk_addr sb kQuarantineBatchClass k + kQuarantineBatchBytes) ->
    ~ xblk a -> ~ rr24 (a_ri A) a ->
    v' (wz a) = v (wz a).
  Proof.
    intros a Ha X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11. pose proof GEO as G. geop. apply MU; [exact Ha| |].
    - unfold W0. intros [H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]; try lia.
    - intros HB. destruct (BXW a HB) as [H|[H|[H|[H|[H|H]]]]]; [exact (X8 H)| lia| lia| exact (X9 H)| exact (X10 H)| exact (X11 H)].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="CQB WF0 MU BXW BX LO LN LU AR lo sp li A Clg"] Lemma AGlow : forall a, kLowShadowMapBeg <= a < kHighShadowMapBeg -> ~ (sh p <= a < sh p + r8) -> v' (wz a) = v (wz a).
  Proof.
    intros a Ha Hsp. pose proof GEO as G. geop. (first [ pose proof ((carved_range A v AR ch CV)) as dR_23; dand3 dR_23 as CL1 CL2 CL3 | pose proof (carved_range A v AR ch CV) as (CL1 & CL2 & CL3) ]). unfold kLowShadowMapBeg, kHighShadowMapBeg in Ha.
    assert (NRR : ~ rr24 (a_ri A) a) by (intros RR; apply rr24_in in RR; pose proof RIW as (RW1 & _); clear -Ha RW1 RR; kung_all; lia).
    apply AG_gen; try exact NRR; try (kung_all; lia); [| | unfold xblk, ia_blk, gq_blk; kung_all; lia].
    - ((first [ intro dR_95; dex1 dR_95 as b; destruct dR_95 as [Hb Rb] | intro dR_95; dand3 dR_95 as b Hb Rb | intros (b & Hb & Rb) ])). pose proof (batch_range A v AR b Hb). kung_all. lia.
    - ((first [ intro dR_96; dex1 dR_96 as k; destruct dR_96 as [Ck Rk] | intro dR_96; dand3 dR_96 as k Ck Rk | intros (k & Ck & Rk) ])). pose proof (carved_prim_where A v AR _ _ (cf_carved k Ck)). kung_all. lia.
  Qed.
  #[using="CQB WF0 MU BXW BX LO LN LU AR lo sp li n0 p A Clg"] Lemma AGimg : forall a, 0x10000 <= a < 0x60a000 -> ~ (0x187288 <= a < 0x5d72a8) -> ~ xblk a -> v' (wz a) = v (wz a).
  Proof.
    intros a Ha Hd Hia. pose proof GEO as G. geop. (first [ pose proof ((carved_range A v AR ch CV)) as dR_24; dand3 dR_24 as CL1 CL2 CL3 | pose proof (carved_range A v AR ch CV) as (CL1 & CL2 & CL3) ]).
    assert (NRR : ~ rr24 (a_ri A) a) by (intros RR; apply rr24_in in RR; pose proof RIW as (RW1 & _); clear -Ha RW1 RR; kung_all; lia).
    apply AG_gen; try exact NRR; try (kung_all; lia); [| | exact Hia].
    - ((first [ intro dR_97; dex1 dR_97 as b; destruct dR_97 as [Hb Rb] | intro dR_97; dand3 dR_97 as b Hb Rb | intros (b & Hb & Rb) ])). pose proof (batch_range A v AR b Hb). kung_all. lia.
    - ((first [ intro dR_98; dex1 dR_98 as k; destruct dR_98 as [Ck Rk] | intro dR_98; dand3 dR_98 as k Ck Rk | intros (k & Ck & Rk) ])). pose proof (carved_prim_where A v AR _ _ (cf_carved k Ck)). kung_all. lia.
  Qed.
  #[using="CQB WF0 MU BXW BX LO LN LU AR lo sp li n0 p A Clg"] Lemma AGshared : forall a, cl_shared LPA a -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof. intros a H. cbn [cl_shared LPA] in H. unfold pa_shared in H. apply AGimg; unfold xblk, ia_blk, gq_blk; lia. Qed.
  #[using="CQB WF0 MU BXW BX LO LN LU AR lo sp li n0 p A Clg"] Lemma AGconst : forall cst a, In cst (cl_consts LPA) -> cst <> ia_pad -> cst <> q_pad -> fst cst <= a < fst cst + Z.of_nat (length (snd cst)) -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof.
    intros cst a Hin NP NQ Ha. cbn [cl_consts LPA] in Hin.
    pose proof pa_consts_nodepot as OK. rewrite forallb_forall in OK. specialize (OK cst Hin). unfold const_nodepot in OK.
    apply orb_true_iff in OK. rewrite !Z.leb_le in OK.
    pose proof pa_consts_noia as OK2. rewrite forallb_forall in OK2. specialize (OK2 cst Hin). cbv beta in OK2.
    apply orb_true_iff in OK2 as [OK2|OK2]; [| exfalso; apply NQ; apply (proj1 (bool_decide_eq_true _)) in OK2; exact OK2].
    apply orb_true_iff in OK2 as [OK2|OK2]; [| exfalso; apply NP; apply (proj1 (bool_decide_eq_true _)) in OK2; exact OK2].
    unfold const_noia in OK2.
    apply andb_true_iff in OK2 as [OK2 OK5]. apply andb_true_iff in OK2 as [OK2 OK4]. apply andb_true_iff in OK2 as [OK2 OK3].
    apply orb_true_iff in OK2. apply orb_true_iff in OK3. apply orb_true_iff in OK4. apply orb_true_iff in OK5. rewrite !Z.leb_le in OK2, OK3, OK4, OK5.
    assert (NIA : ~ xblk a) by (unfold xblk, ia_blk, gq_blk; lia).
    destruct (pa_consts_where cst a Hin Ha) as [S|[S|S]].
    - apply AGimg; [unfold pa_shared in S; lia| lia| exact NIA].
    - unfold pa_image_shadow, sh in S. pose proof GEO as G. geop.
      replace (0x10000 / 8) with 8192 in S by reflexivity. replace (0x60a000 / 8) with 791552 in S by reflexivity.
      apply AGlow; unfold kLowShadowMapBeg, kHighShadowMapBeg, kShadowOffset in *; [lia|].
      (* [comment removed for export] *)
      intros X. unfold sh in *. kung_all. lia.
    - pose proof (pa_static_low a S). apply AGimg; [unfold pa_static in S; lia| lia| exact NIA].
  Qed.

  (* [comment removed for export] *)
  #[using="CQB WF0 MU BXW BX LO LN LU AR lo sp li n0 p Clg"] Lemma AGthr : forall a, thr <= a < thr + 4096 -> a <> thr + 3168 -> ~ (thr + 2824 <= a < thr + 2840) -> ~ (thr + 80 <= a < thr + 112) ->
    ~ (thr + 2128 <= a < thr + 2208) -> ~ (thr + 2784 <= a < thr + 2792) ->
    v' (wz a) = v (wz a).
  Proof.
    intros a Ha X1 X2 X3 X4 X5. pose proof GEO as G. geop. pose proof (carved_apart_thr A v AR ch CV) as CT. (first [ pose proof ((carved_range A v AR ch CV)) as dR_25; dand3 dR_25 as CL1 CL2 CL3 | pose proof (carved_range A v AR ch CV) as (CL1 & CL2 & CL3) ]).
    apply MU; [kung_all; lia| |].
    - unfold W0. pose proof (proj1 (proj2 (proj2 (bm_nth_fixed A)))) as E2.
      assert (D4 : n0a + 0x100000 <= thr \/ thr + 4096 <= n0a).
      { destruct (bm_sep A 7 4 _ _ _ _ WF0 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (bm_nth_fixed A))))))))) (proj1 (proj2 (proj2 (proj2 (proj2 (bm_nth_fixed A)))))) ltac:(lia)); unfold a_nodes0, a_thr in *; kung_all; lia. }
      assert (D5 : f0 + 0x800000 <= thr \/ thr + 4096 <= f0).
      { destruct (bm_sep A 8 4 _ _ _ _ WF0 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (bm_nth_fixed A)))))))))) (proj1 (proj2 (proj2 (proj2 (proj2 (bm_nth_fixed A)))))) ltac:(lia)); unfold a_frames0, a_thr in *; kung_all; lia. }
      intros [H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]; try (kung_all; lia).
    - intros HB. destruct (BXW a HB) as [(b & Hb & Rb)|[H|[H|[(k & Ck & Rk)|[H|H]]]]]; [| exact (X4 H)| exact (X5 H)| | unfold xblk, ia_blk, gq_blk in H; kung_all; lia| (first [ pose proof (RIW) as dR_26; dand5 dR_26 as _ _ _ Rt _ | pose proof RIW as (_ & _ & _ & Rt & _) ]); apply rr24_in in H; clear -H Rt Ha; lia].
      + pose proof (carved_apart_thr A v AR _ (batch_carved A v AR b Hb)) as D. cbn [chunk_lo chunk_hi alloc_beg] in D.
        unfold batch_addr in Rb. rewrite class_size_24 in D. lia.
      + pose proof (carved_apart_thr A v AR _ (cf_carved k Ck)) as D. cbn [chunk_lo chunk_hi alloc_beg] in D.
        rewrite class_size_24 in D. lia.
  Qed.

  Lemma c24_range : forall k, chunk_lo sb (ChP (CP kQuarantineBatchClass k)) = chunk_addr sb kQuarantineBatchClass k /\
                              chunk_hi sb (ChP (CP kQuarantineBatchClass k)) = chunk_addr sb kQuarantineBatchClass k + kQuarantineBatchBytes.
  Proof. intros k. cbn [chunk_lo chunk_hi alloc_beg]. rewrite class_size_24. split; reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="CQB WF0 MU BXW BX LO LN LU AR lo sp n0 p Clg"] Lemma AGch : forall ch', carved A ch' -> ch' <> ch ->
    (forall b, In b (qt ++ qg) -> ch' <> ChP (CP kQuarantineBatchClass (ba_idx b))) ->
    (forall k, cf24 k -> ch' <> ChP (CP kQuarantineBatchClass k)) ->
    forall a, chunk_lo sb ch' <= a < chunk_hi sb ch' -> v' (wz a) = v (wz a).
  Proof.
    intros ch' C' NE NB NC a Ha. pose proof GEO as G. geop. pose proof (carved_apart_ri A v AR ch' C') as Dri.
    (first [ pose proof ((carved_range A v AR ch' C')) as dR_27; dand3 dR_27 as R1 R2 R3 | pose proof (carved_range A v AR ch' C') as (R1 & R2 & R3) ]).
    pose proof (carved_apart_thr A v AR ch' C') as Dt. pose proof (carved_apart_n0 A v AR ch' C') as Dn. pose proof (carved_apart_f0 A v AR ch' C') as Df.
    pose proof (carved_disjoint A v AR ch' ch C' CV NE) as Dc.
    pose proof (carved_app A v AR ch' C') as CA'. apply (proj1 (aobj_app_rangeA _ _)) in CA'. aobj_lin1 CA'.
    assert (NRR : ~ rr24 (a_ri A) a) by (intros RR; apply rr24_in in RR; clear -Ha Dri RR; lia). clear Dri.
    apply AG_gen; try exact NRR; try (unfold xblk, ia_blk, gq_blk; kung_all; lia).
    - ((first [ intro dR_99; dex1 dR_99 as b; destruct dR_99 as [Hb Rb] | intro dR_99; dand3 dR_99 as b Hb Rb | intros (b & Hb & Rb) ])). pose proof (carved_disjoint A v AR ch' _ C' (batch_carved A v AR b Hb) (NB b Hb)) as D.
      rewrite (proj1 (c24_range (ba_idx b))), (proj2 (c24_range (ba_idx b))) in D. unfold batch_addr in Rb. lia.
    - ((first [ intro dR_100; dex1 dR_100 as k; destruct dR_100 as [Ck Rk] | intro dR_100; dand3 dR_100 as k Ck Rk | intros (k & Ck & Rk) ])). pose proof (carved_disjoint A v AR ch' _ C' (cf_carved k Ck) (NC k Ck)) as D.
      rewrite (proj1 (c24_range k)), (proj2 (c24_range k)) in D. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="CQB WF0 MU BXW BX LO LN LU AR lo sp li Clg"] Lemma AGhs : forall z, heap_shadow A z -> ~ (sh p <= z < sh p + r8) -> v' (wz z) = v (wz z).
  Proof.
    intros z Hz Nz. pose proof GEO as G. geop. pose proof (heap_shadow_range A z WF0 Hz) as HZ. unfold in_shadow_maps, kLowShadowMapBeg, kHighShadowMapBeg, kHighShadowMapSize in HZ.
    (first [ pose proof ((carved_range A v AR ch CV)) as dR_28; dand3 dR_28 as CL1 CL2 CL3 | pose proof (carved_range A v AR ch CV) as (CL1 & CL2 & CL3) ]).
    assert (NRR : ~ rr24 (a_ri A) z) by (intros RR; apply rr24_in in RR; pose proof RIW as (RW1 & _); clear -HZ RW1 RR; kung_all; lia).
    apply AG_gen; try exact NRR; try (unfold xblk, ia_blk, gq_blk; kung_all; lia).
    - ((first [ intro dR_101; dex1 dR_101 as b; destruct dR_101 as [Hb Rb] | intro dR_101; dand3 dR_101 as b Hb Rb | intros (b & Hb & Rb) ])). pose proof (batch_range A v AR b Hb). kung_all. lia.
    - ((first [ intro dR_102; dex1 dR_102 as k; destruct dR_102 as [Ck Rk] | intro dR_102; dand3 dR_102 as k Ck Rk | intros (k & Ck & Rk) ])). pose proof (carved_prim_where A v AR _ _ (cf_carved k Ck)). kung_all. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="CQB WF0 MU BXW BX LO LN LU AR lo sp li n0 p"] Lemma AGhigh : forall b s a, aobj b s -> b <= a < b + s ->
    (b + s <= thr \/ thr + 4096 <= b) -> (b + s <= n0a \/ n0a + kDepotNodesBlock <= b) -> (b + s <= f0 \/ f0 + kStackStoreBlockBytes <= b) ->
    (forall ch', carved A ch' -> chunk_hi sb ch' <= b \/ b + s <= chunk_lo sb ch') ->
    ~ rr24 (a_ri A) a ->
    v' (wz a) = v (wz a).
  Proof.
    intros b s a Hb Ha Dt Dn Df DC NR. pose proof GEO as G. geop. aobj_lin1 Hb. pose proof (DC ch CV) as D0.
    apply AG_gen; try exact NR; try (unfold xblk, ia_blk, gq_blk; kung_all; lia).
    - ((first [ intro dR_103; dex1 dR_103 as b'; destruct dR_103 as [Hb' Rb'] | intro dR_103; dand3 dR_103 as b' Hb' Rb' | intros (b' & Hb' & Rb') ])). pose proof (DC _ (batch_carved A v AR b' Hb')) as D.
      rewrite (proj1 (c24_range (ba_idx b'))), (proj2 (c24_range (ba_idx b'))) in D. unfold batch_addr in Rb'. lia.
    - ((first [ intro dR_104; dex1 dR_104 as k; destruct dR_104 as [Ck Rk] | intro dR_104; dand3 dR_104 as k Ck Rk | intros (k & Ck & Rk) ])). pose proof (DC _ (cf_carved k Ck)) as D.
      rewrite (proj1 (c24_range k)), (proj2 (c24_range k)) in D. lia.
  Qed.

  Local Ltac bm i := let H := fresh in pose proof (bm_nth_fixed A) as H;
    lazymatch i with
    | 0%nat => exact (proj1 H)
    | 1%nat => exact (proj1 (proj2 H)) | 4%nat => exact (proj1 (proj2 (proj2 (proj2 (proj2 H)))))
    | 5%nat => exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))
    | 6%nat => exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))
    | 7%nat => exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))))
    | 8%nat => exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))))
    | 14%nat => exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))))))))))
    end.

  #[using="CQB WF0 MU BXW BX LO LN LU AR lo sp li n0 p Clg"] Lemma AGctx : forall a, p_ctx (a_pl A) <= a < p_ctx (a_pl A) + 0x10000 -> v' (wz a) = v (wz a).
  Proof.
    intros a Ha. (first [ pose proof ((place_facts A WF0)) as dR_29; dand3 dR_29 as _ Pctx _ | pose proof (place_facts A WF0) as (_ & Pctx & _) ]). cbv zeta in Pctx.
    (first [ dand3 Pctx as PctxA Pctx PctxM | destruct Pctx as (PctxA & Pctx & PctxM) ]). apply (AGhigh (p_ctx (a_pl A)) 0x10000 a); [apply (proj1 (aobj_app_rangeA _ _)); exact PctxA| exact Ha| | | | |].
    - destruct (bm_sep A 5 4 _ _ _ _ WF0 ltac:(bm 5%nat) ltac:(bm 4%nat) ltac:(lia)); unfold a_ctx, a_thr in *; [left| right]; lia.
    - destruct (bm_sep A 5 7 _ _ _ _ WF0 ltac:(bm 5%nat) ltac:(bm 7%nat) ltac:(lia)); unfold a_ctx, a_nodes0 in *; [left| right]; lia.
    - destruct (bm_sep A 5 8 _ _ _ _ WF0 ltac:(bm 5%nat) ltac:(bm 8%nat) ltac:(lia)); unfold a_ctx, a_frames0 in *; [left| right]; lia.
    - intros ch' C'. exact (carved_apart_ctx A v AR ch' C').
    - intros RR. apply rr24_in in RR. (first [ pose proof (RIW) as dR_31; dand4 dR_31 as _ _ RI3 _ | pose proof RIW as (_ & _ & RI3 & _) ]). (first [ pose proof ((sb_facts A WF0)) as dR_32; dand5 dR_32 as _ _ _ RSB _ | pose proof (sb_facts A WF0) as (_ & _ & _ & RSB & _) ]).
      destruct (bm_sep A 5 0 _ _ _ _ WF0 ltac:(bm 5%nat) ltac:(bm 0%nat) ltac:(lia)); unfold a_ctx, a_b6, a_sb in *; kung_all; lia.
  Qed.
  #[using="CQB WF0 MU BXW BX LO LN LU AR lo sp li n0 p Clg"] Lemma AGdtls : forall a, p_dtls (a_pl A) <= a < p_dtls (a_pl A) + 4096 -> v' (wz a) = v (wz a).
  Proof.
    intros a Ha. (first [ pose proof ((place_facts A WF0)) as dR_33; dand12 dR_33 as _ _ _ _ _ _ _ _ _ _ Pd _ | pose proof (place_facts A WF0) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Pd & _) ]). cbv zeta in Pd.
    (first [ dand3 Pd as PdA Pd PdM | destruct Pd as (PdA & Pd & PdM) ]). apply (AGhigh (p_dtls (a_pl A)) 4096 a); [apply (proj1 (aobj_app_rangeA _ _)); exact PdA| exact Ha| | | | |].
    - destruct (bm_sep A 14 4 _ _ _ _ WF0 ltac:(bm 14%nat) ltac:(bm 4%nat) ltac:(lia)); unfold a_thr in *; [left| right]; lia.
    - destruct (bm_sep A 14 7 _ _ _ _ WF0 ltac:(bm 14%nat) ltac:(bm 7%nat) ltac:(lia)); unfold a_nodes0 in *; [left| right]; lia.
    - destruct (bm_sep A 14 8 _ _ _ _ WF0 ltac:(bm 14%nat) ltac:(bm 8%nat) ltac:(lia)); unfold a_frames0 in *; [left| right]; lia.
    - intros ch' C'. exact (carved_apart_dtls A v AR ch' C').
    - intros RR. apply rr24_in in RR. (first [ pose proof (RIW) as dR_35; dand4 dR_35 as _ _ RI3 _ | pose proof RIW as (_ & _ & RI3 & _) ]). (first [ pose proof ((sb_facts A WF0)) as dR_36; dand5 dR_36 as _ _ _ RSB _ | pose proof (sb_facts A WF0) as (_ & _ & _ & RSB & _) ]).
      destruct (bm_sep A 14 0 _ _ _ _ WF0 ltac:(bm 14%nat) ltac:(bm 0%nat) ltac:(lia)); unfold  a_b6, a_sb in *; kung_all; lia.
  Qed.
  #[using="CQB WF0 MU BXW BX LO LN LU AR lo sp li n0 p Clg"] Lemma AGfs : forall a, a_fs A <= a < a_fs A + kFakeStackBytes -> v' (wz a) = v (wz a).
  Proof.
    intros a Ha. (first [ pose proof ((place_fs A WF0)) as dR_37; dand3 dR_37 as F1 F2 _ | pose proof (place_fs A WF0) as (F1 & F2 & _) ]). unfold a_fs in *.
    apply (AGhigh (p_fs (a_pl A)) kFakeStackBytes a); [apply (proj1 (aobj_app_rangeA _ _)); exact F1| exact Ha| | | | |].
    all: apply app_facts in F1.
    - destruct (bm_sep A 6 4 _ _ _ _ WF0 ltac:(bm 6%nat) ltac:(bm 4%nat) ltac:(lia)); unfold a_fs, a_thr in *; [left| right]; lia.
    - destruct (bm_sep A 6 7 _ _ _ _ WF0 ltac:(bm 6%nat) ltac:(bm 7%nat) ltac:(lia)); unfold a_fs, a_nodes0 in *; [left| right]; lia.
    - destruct (bm_sep A 6 8 _ _ _ _ WF0 ltac:(bm 6%nat) ltac:(bm 8%nat) ltac:(lia)); unfold a_fs, a_frames0 in *; [left| right]; lia.
    - intros ch' C'. exact (carved_apart_fs A v AR ch' C').
    - intros RR. apply rr24_in in RR. (first [ pose proof (RIW) as dR_38; dand4 dR_38 as _ _ RI3 _ | pose proof RIW as (_ & _ & RI3 & _) ]). (first [ pose proof ((sb_facts A WF0)) as dR_39; dand5 dR_39 as _ _ _ RSB _ | pose proof (sb_facts A WF0) as (_ & _ & _ & RSB & _) ]).
      destruct (bm_sep A 6 0 _ _ _ _ WF0 ltac:(bm 6%nat) ltac:(bm 0%nat) ltac:(lia)); unfold a_fs, a_b6, a_sb in *; kung_all; lia.
  Qed.
  #[using="CQB WF0 MU BXW BX LO LN LU AR lo sp li n0 p Clg"] Lemma AGpa : forall a, p_pa (a_pl A) <= a < p_pa (a_pl A) + kPtrArrayReserve -> v' (wz a) = v (wz a).
  Proof.
    intros a Ha. (first [ pose proof ((place_facts A WF0)) as dR_40; dand13 dR_40 as _ _ _ _ _ _ _ _ _ _ _ Ppa _ | pose proof (place_facts A WF0) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ppa & _) ]). cbv zeta in Ppa.
    (first [ dand3 Ppa as PpaA Ppa PpaM | destruct Ppa as (PpaA & Ppa & PpaM) ]). apply (AGhigh (p_pa (a_pl A)) kPtrArrayReserve a); [apply (proj1 (aobj_app_rangeA _ _)); exact PpaA| exact Ha| | | | |].
    - destruct (bm_sep A 1 4 _ _ _ _ WF0 ltac:(bm 1%nat) ltac:(bm 4%nat) ltac:(lia)); unfold a_pa, a_thr in *; [left| right]; lia.
    - destruct (bm_sep A 1 7 _ _ _ _ WF0 ltac:(bm 1%nat) ltac:(bm 7%nat) ltac:(lia)); unfold a_pa, a_nodes0 in *; [left| right]; lia.
    - destruct (bm_sep A 1 8 _ _ _ _ WF0 ltac:(bm 1%nat) ltac:(bm 8%nat) ltac:(lia)); unfold a_pa, a_frames0 in *; [left| right]; lia.
    - intros ch' C'. exact (carved_apart_pa A v AR ch' C').
    - intros RR. apply rr24_in in RR. (first [ pose proof (RIW) as dR_42; dand4 dR_42 as _ _ RI3 _ | pose proof RIW as (_ & _ & RI3 & _) ]). (first [ pose proof ((sb_facts A WF0)) as dR_43; dand5 dR_43 as _ _ _ RSB _ | pose proof (sb_facts A WF0) as (_ & _ & _ & RSB & _) ]).
      destruct (bm_sep A 1 0 _ _ _ _ WF0 ltac:(bm 1%nat) ltac:(bm 0%nat) ltac:(lia)); unfold a_pa, a_b6, a_sb in *; kung_all; lia.
  Qed.
  (* [comment removed for export] *)
  #[using="WF0 AR n0 v Clg"] Lemma b6_apart : forall i bi si, nth_error (big_maps A) i = Some (bi, si) -> (i <> 0)%nat ->
    a_b6 A + kSpaceReserve <= bi \/ bi + si <= a_b6 A.
  Proof. intros i bi si Hi NZ. destruct (bm_sep A 0 i _ _ _ _ WF0 (proj1 (bm_nth_fixed A)) Hi ltac:(lia)); [left| right]; lia. Qed.
  #[using="CQB WF0 MU BXW BX LO LN LU AR lo sp li n0 p Clg"] Lemma AGri : forall a, a_ri A <= a < a_ri A + 4096 -> ~ rr24 (a_ri A) a -> v' (wz a) = v (wz a).
  Proof.
    intros a Ha NR. (first [ pose proof ((sb_facts A WF0)) as dR_44; dand5 dR_44 as _ _ HB6 RSB SCE | pose proof (sb_facts A WF0) as (_ & _ & HB6 & RSB & SCE) ]). unfold a_ri, p_ri in *. change (p_sb (a_pl A)) with sb in *.
    pose proof (b6_apart 4 _ _ ltac:(bm 4%nat) ltac:(lia)) as D4. pose proof (b6_apart 7 _ _ ltac:(bm 7%nat) ltac:(lia)) as D7. pose proof (b6_apart 8 _ _ ltac:(bm 8%nat) ltac:(lia)) as D8.
    unfold a_thr, a_nodes0, a_frames0 in *.
    pose proof GEO as G. geop.
    apply (AGhigh (sb + kSpaceSize) 4096 a); [apply aobj_hi; kung_all; lia| exact Ha| kung_all; lia| kung_all; lia| kung_all; lia| | exact NR].
    intros ch' C'. pose proof (carved_apart_ri A v AR ch' C') as D. unfold a_ri, p_ri in D. exact D.
  Qed.
  #[using="CQB WF0 MU BXW BX LO LN LU AR lo sp li n0 p Clg"] Lemma AGfa : forall c' a, 1 <= c' <= 30 -> free_array_beg sb c' <= a < free_array_beg sb c' + rg_mapped_fa (a_reg A c') -> v' (wz a) = v (wz a).
  Proof.
    intros c' a Hc Ha. (first [ pose proof ((sb_facts A WF0)) as dR_45; dand5 dR_45 as _ _ HB6 RSB SCE | pose proof (sb_facts A WF0) as (_ & _ & HB6 & RSB & SCE) ]). pose proof (region_piece_bounds A c' WF0 Hc) as RB. cbv zeta in RB. change (a_sb A) with sb in *.
    pose proof (b6_apart 4 _ _ ltac:(bm 4%nat) ltac:(lia)) as D4. pose proof (b6_apart 7 _ _ ltac:(bm 7%nat) ltac:(lia)) as D7. pose proof (b6_apart 8 _ _ ltac:(bm 8%nat) ltac:(lia)) as D8.
    unfold a_thr, a_nodes0, a_frames0, free_array_beg in *.
    pose proof GEO as G. geop.
    (first [ pose proof (RIW) as dR_46; dand4 dR_46 as _ _ RI3 _ | pose proof RIW as (_ & _ & RI3 & _) ]).
    apply (AGhigh (region_beg sb c' + kFreeArrayOffset) (rg_mapped_fa (a_reg A c')) a); [apply aobj_hi; kung_all; lia| exact Ha| kung_all; lia| kung_all; lia| kung_all; lia| |
      intros RR; apply rr24_in in RR; unfold a_ri, p_ri, region_beg in *; change (p_sb (a_pl A)) with sb in *; kung_all; lia].
    intros ch' C'. pose proof (carved_apart_fa A v AR ch' c' C' Hc) as D. unfold free_array_beg in D. exact D.
  Qed.

  (* [comment removed for export] *)
  #[using="R WF0 NN MU LO LN LU AR lo sp li n0 p v Clg"] Lemma global_untouched : (forall a, BX a -> ~ gq_blk a) ->
    (forall b a, In b qg -> batch_addr sb b <= a < batch_addr sb b + kQuarantineBatchBytes -> ~ BX a) ->
    (let I := al_instance AL_pasan + off_q_cache_list_size in
     u64_at rsegs v' (I + 0) (Z.of_nat (length qg)) /\
     u64_at rsegs v' (I + 8) (match qg with [] => 0 | b :: _ => batch_addr sb b end) /\
     u64_at rsegs v' (I + 16) (match qg with [] => 0 | _ => batch_addr sb (last qg (BA 0 [])) end) /\
     u64_at rsegs v' (I + 24) (q_bytes qg)) /\
    batches_repr LPA v' sb qg.
  Proof.
    intros NGQ NBX. (first [ pose proof ((ar_quar _ _ _ _ _ R)) as dR_47; dand3 dR_47 as _ QG _ | pose proof (ar_quar _ _ _ _ _ R) as (_ & QG & _) ]). change (p_sb (a_pl A)) with sb in QG. (first [ dand5 QG as X1 X2 X3 X4 BR | destruct QG as (X1 & X2 & X3 & X4 & BR) ]).
    split.
    - refine (qcache_head_P A v v' (al_instance AL_pasan + off_q_cache_list_size) qg _ (conj X1 (conj X2 (conj X3 X4)))).
      intros a Ha. offs_h Ha. alc_h Ha. pose proof GEO as G. geop. (first [ pose proof ((carved_range A v AR ch CV)) as dR_49; dand3 dR_49 as CL1 CL2 CL3 | pose proof (carved_range A v AR ch CV) as (CL1 & CL2 & CL3) ]).
      apply MU; [kung_all; lia| |].
      + unfold W0. kung_all. intros [H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]; lia.
      + intros HB. exact (NGQ a HB ltac:(unfold gq_blk; lia)).
    - apply (batches_P A v v' AR NN); [intros b Hb; apply in_or_app; right; exact Hb| | exact BR].
      intros b a Hb Ha. pose proof GEO as G. geop. assert (INb : In b (qt ++ qg)) by (apply in_or_app; right; exact Hb).
      pose proof (batch_carved A v AR b INb) as Cb.
      pose proof (carved_apart_thr A v AR _ Cb) as Dt. pose proof (carved_apart_n0 A v AR _ Cb) as Dn. pose proof (carved_apart_f0 A v AR _ Cb) as Df.
      pose proof (carved_disjoint A v AR _ _ Cb CV (fun E => live_not_batch A v AR p li b LU INb (eq_sym E))) as Dp.
      rewrite (proj1 (c24_range (ba_idx b))), (proj2 (c24_range (ba_idx b))) in Dt, Dn, Df, Dp.
      (first [ pose proof ((batch_range A v AR b INb)) as dR_50; dand3 dR_50 as R1 R2 _ | pose proof (batch_range A v AR b INb) as (R1 & R2 & _) ]). unfold batch_addr in *.
      apply MU; [kung_all; unfold kQuarantineBatchBytes in *; lia| | exact (NBX b a Hb Ha)].
      unfold W0. unfold kQuarantineBatchBytes in *. kung_all. intros [X|[X|[X|[X|[X|[X|[X|[X|[X|X]]]]]]]]]; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="CQB WF0 MU BXW BX LO LN LU AR lo sp n0 Clg"] Lemma AGown : forall a, chunk_lo sb ch <= a < chunk_hi sb ch -> ~ (p + -16 <= a < p + -12) -> ~ (p <= a < p + 8) -> v' (wz a) = v (wz a).
  Proof.
    intros a Ha X1 X2. pose proof GEO as G. geop. (first [ pose proof ((carved_range A v AR ch CV)) as dR_51; dand3 dR_51 as CL1 CL2 CL3 | pose proof (carved_range A v AR ch CV) as (CL1 & CL2 & CL3) ]).
    pose proof (carved_apart_thr A v AR ch CV) as Dt. pose proof (carved_apart_n0 A v AR ch CV) as Dn. pose proof (carved_apart_f0 A v AR ch CV) as Df.
    apply MU; [kung_all; lia| |].
    - unfold W0. intros [H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]; kung_all; try lia.
    - intros HB. destruct (BXW a HB) as [(b & Hb & Rb)|[H|[H|[(k & Ck & Rk)|[H|H]]]]]; [| lia| lia| | unfold xblk, ia_blk, gq_blk in H; kung_all; lia| (first [ pose proof (RIW) as dR_52; dand7 dR_52 as _ _ _ _ _ _ Rc | pose proof RIW as (_ & _ & _ & _ & _ & _ & Rc) ]); apply rr24_in in H; clear -H Rc Ha; lia].
      + pose proof (carved_disjoint A v AR ch _ CV (batch_carved A v AR b Hb) (live_not_batch A v AR p li b LU Hb)) as D.
        rewrite (proj1 (c24_range (ba_idx b))), (proj2 (c24_range (ba_idx b))) in D. unfold batch_addr in *. lia.
      + pose proof (carved_disjoint A v AR ch _ CV (cf_carved k Ck) (live_not_cf p li k LU Ck)) as D.
        rewrite (proj1 (c24_range k)), (proj2 (c24_range k)) in D. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="CQB WF0 MU BXW BX LO LN LU AR lo sp n0 p Clg"] Lemma AGsh : forall ch', carved A ch' -> ch' <> ch -> forall z, sh (chunk_lo sb ch') <= z < sh (chunk_hi sb ch') -> v' (wz z) = v (wz z).
  Proof.
    intros ch' C' NE z Hz. pose proof GEO as G. geop. (first [ pose proof ((carved_shadow A v AR ch' C')) as dR_53; dand3 dR_53 as E' HS' _ | pose proof (carved_shadow A v AR ch' C') as (E' & HS' & _) ]).
    (first [ pose proof ((carved_shadow A v AR ch CV)) as dR_54; dand5 dR_54 as E _ _ M1 M2 | pose proof (carved_shadow A v AR ch CV) as (E & _ & _ & M1 & M2) ]).
    apply AGhs; [exact (HS' z Hz)|].
    (first [ dand5 G as PM _ L1 L2 _ | destruct G as (PM & _ & L1 & L2 & _) ]).
    pose proof (sh_mono _ _ L1) as S1. pose proof (sh_mono _ _ L2) as S2.
    assert (SE : sh (p + 8 * r8) = sh p + r8) by (unfold sh; rewrite (Z.mul_comm 8 r8), Z.div_add by lia; lia).
    pose proof (sh_mono (p + -16) p ltac:(lia)) as S3.
    destruct (carved_shadows_disjoint A v AR ch' ch C' CV NE) as [D|D]; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Variables (b1 fid : Z).
  Hypothesis B1R : 0 <= b1 < 256.
  Hypothesis B1M : Z.land b1 0x7f = kHdrByte1Malloc.
  Hypothesis FIDR : 0 <= fid < 2^32.
  Hypothesis P_unw : rw_cells rsegs v' (thr + off_th_unwinding) [C1 (Z_to_bv 8 0)].
  Hypothesis P_hdr : rw_cells rsegs v' (p + -16) [C1 (Z_to_bv 8 CHUNK_QUARANTINE); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n0)); C4 (wz n0)].
  Hypothesis P_ctx : rw_cells rsegs v' p [C8 (wz fid)].
  Hypothesis P_sh : bytes_at rsegs v' (sh p) (repeat (Z_to_bv 8 0xfd) (Z.to_nat r8)).
  Hypothesis P_dr : depot_repL AL_pasan rsegs D' n0a f0 v'.
  Hypothesis P_qc : rw_cells rsegs v' (thr + 80)
     [C8 (wz (Z.of_nat (length qt'))); C8 (wz (qc_first A qt')); C8 (wz (qc_last A qt')); C8 (wz (q_bytes qt'))].
  Hypothesis P_br : batches_repr LPA v' sb qt'.
  Hypothesis P_qcg : let I := al_instance AL_pasan + off_q_cache_list_size in
    u64_at rsegs v' (I + 0) (Z.of_nat (length qg')) /\
    u64_at rsegs v' (I + 8) (match qg' with [] => 0 | b :: _ => batch_addr sb b end) /\
    u64_at rsegs v' (I + 16) (match qg' with [] => 0 | _ => batch_addr sb (last qg' (BA 0 [])) end) /\
    u64_at rsegs v' (I + 24) (q_bytes qg').
  Hypothesis P_brg : batches_repr LPA v' sb qg'.
  Hypothesis P_l24 :
    let e := thr + off_th_per_class kQuarantineBatchClass in let ks := pk_chunks (cache' kQuarantineBatchClass) in
    Z.of_nat (length ks) <= 16 /\
    u32_at rsegs v' (e + off_pc_count) (Z.of_nat (length ks)) /\
    (if a_cache_inited A && negb (kQuarantineBatchClass =? 0) then u32_at rsegs v' (e + off_pc_max_count) (max_count kQuarantineBatchClass) /\ u64_at rsegs v' (e + off_pc_class_size) (class_size kQuarantineBatchClass)
     else u32_at rsegs v' (e + off_pc_max_count) 0 /\ u64_at rsegs v' (e + off_pc_class_size) 0) /\
    (forall i k, nth_error ks i = Some k -> u32_at rsegs v' (e + off_pc_chunk (Z.of_nat i)) (k * class_size kQuarantineBatchClass / kCompactPtrScale)) /\
    junk_at rsegs v' (e + off_pc_chunk (Z.of_nat (length ks))) (4 * (16 - Z.of_nat (length ks))).
  (* [comment removed for export] *)
  Hypothesis IAH : (ia' = a_ia_inited A /\ (forall a, iafoot a -> v' (wz a) = v (wz a))) \/ (ia' = true /\ ia_repr_ LPA AL_pasan true v').
  (* [comment removed for export] *)
  Hypothesis IAL : u8_at rsegs v' 0x144e49 0.
  Hypothesis IAP : bytes_at rsegs v' 0x144e4a [Z_to_bv 8 0; Z_to_bv 8 0].
  (* [comment removed for export] *)
  Hypothesis QLK : u8_at rsegs v' 0xb20c8 0.
  Hypothesis QPD : bytes_at rsegs v' 0xb20ca [Z_to_bv 8 0; Z_to_bv 8 0].
  (* [comment removed for export] *)
  Hypothesis QT'E : forall e, In e (q_entries (qt' ++ qg')) -> In e (q_entries (qt ++ qg)) \/ e = QE ch n0.
  Hypothesis QT'B : forall b, In b (qt' ++ qg') -> In (ba_idx b) (map ba_idx (qt ++ qg)) \/ cf24 (ba_idx b).
  Hypothesis C'O : forall c, c <> kQuarantineBatchClass -> cache' c = a_cache A c.
  Hypothesis C'S : forall k, p_cached_ cache' kQuarantineBatchClass k -> p_cached_ (a_cache A) kQuarantineBatchClass k \/ p_free_ (a_reg A) kQuarantineBatchClass k.
  (* [comment removed for export] *)
  Hypothesis R'O : forall c, c <> kQuarantineBatchClass -> reg' c = a_reg A c.
  Hypothesis R'E : rg_mapped_user (reg' kQuarantineBatchClass) = rg_mapped_user (a_reg A kQuarantineBatchClass) /\
                   rg_allocated_user (reg' kQuarantineBatchClass) = rg_allocated_user (a_reg A kQuarantineBatchClass) /\
                   rg_mapped_fa (reg' kQuarantineBatchClass) = rg_mapped_fa (a_reg A kQuarantineBatchClass).
  Hypothesis R'F : forall k, p_free_ reg' kQuarantineBatchClass k -> p_free_ (a_reg A) kQuarantineBatchClass k.
  Hypothesis RG24 : exists n', rg_free (reg' kQuarantineBatchClass) = firstn n' (rg_free (a_reg A kQuarantineBatchClass)).
  (* [comment removed for export] *)
  Hypothesis P_mx24 : u64_at rsegs v' (a_ri A + 3072) 0.
  Hypothesis P_nf24 : u64_at rsegs v' (a_ri A + 3088) (Z.of_nat (length (rg_free (reg' kQuarantineBatchClass)))).

  (* [comment removed for export] *)
  #[using="QPD IAP P_unw FIDR B1R fid b1 CQB R WF0 NN MU BXW BX cache' LO LN LU AR lo sp li n0 p v Clg"] Lemma consts_P' : consts_repr_ LPA AL_pasan (a_pl A) v'.
  Proof.
    pose proof GEO as G. geop. pose proof TPV as TP.
    apply (consts_P2 A v v' AR).
    - intros cst Hin. destruct (decide (cst = ia_pad)) as [->|NP]; [right; exact IAP|]. destruct (decide (cst = q_pad)) as [->|NQ]; [right; exact QPD|].
      left; intros a Ha; exact (AGconst cst a Hin NP NQ Ha).
    - exact AGshared.
    - intros a H. apply AGimg; unfold cfoot_stat in H; offs_h H; alc_h H; unfold xblk, ia_blk, gq_blk; lia.
    - intros a H. unfold cfoot_thr in H. offs_h H.
      destruct (Z.eq_dec a (thr + 3168)) as [->|NE].
      + (* [comment removed for export] *)
        pose proof (ar_consts _ _ _ _ _ R) as C. unfold consts_repr_ in C. cbv zeta in C.
        (first [ dand36 C as _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dR_C_t0; destruct dR_C_t0 as [UNW _] | destruct C as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & UNW & _) ]).
        (first [ dand3 UNW as _ _ U | destruct UNW as (_ & _ & U) ]). destruct P_unw as [[_ (_ & _ & U')] _]. cbn [cells_bytes cbytes app length] in U'.
        specialize (U 0%nat ltac:(cbn; lia)). specialize (U' 0%nat ltac:(cbn; lia)). cbn [nth_error Z.of_nat] in U, U'. offs_h U. offs_h U'.
        rewrite Z.add_0_r in U, U'.
        assert (Vn : v (wz (thr + 3168)) <> None).
        { (first [ pose proof ((ar_cache _ _ _ _ _ R)) as dR_58; dand5 dR_58 as _ _ _ MT _ | pose proof (ar_cache _ _ _ _ _ R) as (_ & _ & _ & MT & _) ]). apply (MT 3168). lia. }
        assert (V'n : v' (wz (thr + 3168)) <> None) by (apply NN; [kung_all; lia| kung_all; lia| kung_all; lia| exact Vn]).
        rewrite (mrd_some_eq v _ _ Vn U), (mrd_some_eq v' _ _ V'n U'). reflexivity.
      + apply AGthr; lia.
    - intros a H. unfold cfoot_misc in H. rewrite TP in H.
      destruct H as [H|[H|[H|[H|[H|H]]]]]; first [apply AGctx; lia | apply AGimg; unfold xblk, ia_blk, gq_blk; lia | apply AGdtls; lia].
  Qed.

  #[using="FIDR B1R fid b1 CQB WF0 MU BXW BX LO LN LU AR lo sp li n0 p A Clg"] Lemma AGstat_all : forall a, 0x10000 <= a < 0x187288 -> ~ xblk a -> v' (wz a) = v (wz a).
  Proof. intros a Ha Hia. apply AGimg; [lia| lia| exact Hia]. Qed.

  (* [comment removed for export] *)
  #[using="P_mx24 QLK IAL FIDR B1R fid b1 CQB R WF0 MU BXW BX cache' LO LN LU AR lo sp li n0 p v Clg"] Lemma locks_P'h : forall (held : list Z) (rl : Z), u8_at rsegs v' 0xb20c9 rl ->
    (forall x, lockb held x = if Z.eqb x 0xb20c9 then rl else 0) ->
    locks_repr_ LPA AL_pasan (a_pl A) held v'.
  Proof.
    intros held rl QRL HLD.
    pose proof (ar_locks _ _ _ _ _ R) as C. unfold locks_repr_ in *. cbv zeta in *. destruct C as (C0 & C).
    (first [ pose proof ((sb_facts A WF0)) as dR_59; dand5 dR_59 as _ _ HB6 RSB SCE | pose proof (sb_facts A WF0) as (_ & _ & HB6 & RSB & SCE) ]). unfold a_sb, a_b6 in HB6, RSB, SCE.
    change (al_internal_alloc_inited AL_pasan) with 0x144e48 in *. change (al_instance AL_pasan) with 0xb1d58 in *.
    rewrite lockb_nil in *. rewrite !HLD. cbn [Z.eqb Pos.eqb].
    unfold off_sec_mutex, off_q_cache_mutex, off_q_recycle_mutex, off_fallback_mutex. cbn [Z.add Pos.add Pos.succ Z.eqb Pos.eqb].
    split.
    - intros c' Hc. destruct (C0 c' Hc) as [X Y]. unfold p_ri in *.
      split.
      + destruct (Z.eq_dec c' kQuarantineBatchClass) as [->|NE].
        * match goal with |- u64_at _ _ ?x _ => replace x with (a_ri A + 3072) by (unfold a_ri, p_ri, kRegionInfoSize, kQuarantineBatchClass; lia) end. exact P_mx24.
        * eapply u64_at_agree; [exact X|]; intros i Hi; apply AGri; unfold a_ri, p_ri, rr24; unfold kHighMemBeg, kSpaceSize, kRegionInfoSize, kQuarantineBatchClass in *; [lia|].
          assert (c' <= 23 \/ 25 <= c') as [Z1|Z1] by lia; lia.
      + eapply u64_at_agree; [exact Y|]; intros i Hi; apply AGri; unfold a_ri, p_ri, rr24; unfold kHighMemBeg, kSpaceSize, kRegionInfoSize, kQuarantineBatchClass in *; [lia|].
        destruct (Z.eq_dec c' 24) as [->|NE]; [lia|]. assert (c' <= 23 \/ 25 <= c') as [Z1|Z1] by lia; lia.
    - (first [ dand5 C as L1 L2 L3 L4 L5 | destruct C as (L1 & L2 & L3 & L4 & L5) ]). unfold off_sec_mutex, off_q_cache_mutex, off_q_recycle_mutex, off_fallback_mutex in *.
      split; [eapply u8_at_agree; [exact L1|]; apply AGstat_all; unfold xblk, ia_blk, gq_blk in *; lia|].
      split; [exact QLK|]. split; [exact QRL|].
      split; [eapply u8_at_agree; [exact L4|]; apply AGstat_all; unfold xblk, ia_blk, gq_blk in *; lia| exact IAL].
  Qed.
  #[using="P_mx24 QLK IAL FIDR B1R fid b1 CQB R WF0 MU BXW BX cache' LO LN LU AR lo sp li n0 p v Clg"] Lemma locks_P' : u8_at rsegs v' 0xb20c9 0 -> locks_repr_ LPA AL_pasan (a_pl A) [] v'.
  Proof. intros QRL. apply (locks_P'h [] 0 QRL). intros x. rewrite lockb_nil. destruct (Z.eqb x 0xb20c9); reflexivity. Qed.
  #[using="P_mx24 QLK IAL FIDR B1R fid b1 CQB R WF0 MU BXW BX cache' LO LN LU AR lo sp li n0 p v Clg"] Lemma locks_P'R : u8_at rsegs v' 0xb20c9 1 -> locks_repr_ LPA AL_pasan (a_pl A) [al_instance AL_pasan + off_q_recycle_mutex] v'.
  Proof.
    intros QRL. apply (locks_P'h _ 1 QRL). intros x. unfold lockb. cbn [al_instance AL_pasan]. unfold off_q_recycle_mutex.
    change (728408 + 881) with 0xb20c9. destruct (in_dec Z.eq_dec x [0xb20c9]) as [I|NI].
    - destruct I as [<-|[]]. rewrite Z.eqb_refl. reflexivity.
    - destruct (Z.eqb_spec x 0xb20c9) as [->|NE]; [exfalso; apply NI; left; reflexivity| reflexivity].
  Qed.

  #[using="P_nf24 RG24 R'E R'O FIDR B1R fid b1 CQB R WF0 NN MU BXW BX cache' LO LN LU AR lo sp li n0 p v Clg"] Lemma regions_P' : forall c', 1 <= c' <= 30 -> region_repr_ LPA sb (reg' c') v' c'.
  Proof.
    intros c' Hc. (first [ pose proof (RIW) as dR_61; dand4 dR_61 as RI1 RI2 RI3 _ | pose proof RIW as (RI1 & RI2 & RI3 & _) ]).
    destruct (Z.eq_dec c' kQuarantineBatchClass) as [->|NE].
    - (* [comment removed for export] *)
      pose proof (ar_regions _ _ _ _ _ R kQuarantineBatchClass Hc) as C. pose proof alloc_ceiling_val as CE.
      pose proof (region_piece_bounds A kQuarantineBatchClass WF0 Hc) as RB. cbv zeta in RB. change (a_sb A) with sb in RB.
      (first [ pose proof ((wfR A WF0)) as dR_62; dand3 dR_62 as WR _ _ | destruct (wfR A WF0) as (WR & _ & _) ]). (first [ pose proof ((WR kQuarantineBatchClass Hc)) as dR_63; dand8 dR_63 as Q1 Q2 Q3 Q4 Q5 Q6 Q7 _ | pose proof (WR kQuarantineBatchClass Hc) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & _) ]).
      unfold region_repr_ in *. cbv zeta in *. change (p_sb (a_pl A)) with sb in *.
      destruct R'E as (EMU & EAL & EFA). rewrite EMU, EAL, EFA. destruct RG24 as [n' RG].
      unfold region_info_addr, free_array_beg in *. unfold kRegionInfoSize, kQuarantineBatchClass in *.
      assert (AGR : forall x, sb + kSpaceSize + 3072 <= x < sb + kSpaceSize + 3200 -> ~ rr24 (a_ri A) x -> v' (wz x) = v (wz x)).
      { intros x Hx NRx. apply AGri; [| exact NRx]. rewrite RI3. lia. }
      unfold off_ri_num_freed, off_ri_mapped_free_array, off_ri_allocated_user, off_ri_allocated_meta, off_ri_mapped_user, off_ri_mapped_meta,
             off_ri_exhausted, off_ri_n_allocated, off_ri_rtoi in *.
      (first [ dand13 C as Hnf Hfa Hal Ham Hmu Hmm Hex J64 Jna Jrt CF M1 M2 | destruct C as (Hnf & Hfa & Hal & Ham & Hmu & Hmm & Hex & J64 & Jna & Jrt & CF & M1 & M2) ]).
      split. { match goal with |- u64_at _ _ ?x _ => replace x with (a_ri A + 3088) by (rewrite RI3; unfold kRegionInfoSize, kQuarantineBatchClass; lia) end. exact P_nf24. }
      split; [eapply u64_at_agree; [exact Hfa|]; intros i Hi; apply AGR; [unfold kRegionInfoSize, kQuarantineBatchClass in *; lia| unfold rr24; rewrite RI3; unfold kRegionInfoSize, kQuarantineBatchClass; lia] |]. split; [eapply u64_at_agree; [exact Hal|]; intros i Hi; apply AGR; [unfold kRegionInfoSize, kQuarantineBatchClass in *; lia| unfold rr24; rewrite RI3; unfold kRegionInfoSize, kQuarantineBatchClass; lia] |]. split; [eapply u64_at_agree; [exact Ham|]; intros i Hi; apply AGR; [unfold kRegionInfoSize, kQuarantineBatchClass in *; lia| unfold rr24; rewrite RI3; unfold kRegionInfoSize, kQuarantineBatchClass; lia] |]. split; [eapply u64_at_agree; [exact Hmu|]; intros i Hi; apply AGR; [unfold kRegionInfoSize, kQuarantineBatchClass in *; lia| unfold rr24; rewrite RI3; unfold kRegionInfoSize, kQuarantineBatchClass; lia] |]. split; [eapply u64_at_agree; [exact Hmm|]; intros i Hi; apply AGR; [unfold kRegionInfoSize, kQuarantineBatchClass in *; lia| unfold rr24; rewrite RI3; unfold kRegionInfoSize, kQuarantineBatchClass; lia] |].
      split; [eapply u8_at_agree; [exact Hex|]; apply AGR; [unfold kRegionInfoSize, kQuarantineBatchClass in *; lia| unfold rr24; rewrite RI3; unfold kRegionInfoSize, kQuarantineBatchClass; lia] |].
      split; [apply (junk_N v v' NN); [kung_all; lia| right; kung_all; lia| exact J64] |].
      split; [apply (junk_N v v' NN); [kung_all; lia| right; kung_all; lia| exact Jna] |].
      split; [apply (junk_N v v' NN); [kung_all; lia| right; kung_all; lia| exact Jrt] |].
      split; [|split].
      + intros i k E. rewrite RG in E. apply nth_error_firstn_SomeF in E. pose proof (CF i k E) as LF.
        assert (Hi : Z.of_nat i < Z.of_nat (length (rg_free (a_reg A 24)))) by (pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite E; discriminate)); lia).
        eapply u32_at_agree; [exact LF|]. intros j Hj. apply (AGfa 24); [exact Hc|]. unfold free_array_beg, region_beg in *. clear -Hj Hi Q7. lia.
      + apply (mapped_N v v' NN); [kung_all; lia| right; kung_all; lia| kung_all; lia| exact M1].
      + apply (mapped_N v v' NN); [kung_all; lia| right; kung_all; lia| kung_all; lia| exact M2].
    - rewrite (R'O c' NE). apply (region_P A v v' AR NN c' Hc). intros a H. unfold rfoot in H. destruct H as [H|H].
      + apply AGri; [unfold a_ri, p_ri, region_info_addr in *; change (p_sb (a_pl A)) with sb; unfold kRegionInfoSize in *; lia|].
        unfold rr24. rewrite RI3. unfold region_info_addr, kRegionInfoSize, kQuarantineBatchClass in *.
        assert (c' <= 23 \/ 25 <= c') as [Z1|Z1] by lia; lia.
      + exact (AGfa c' a Hc H).
  Qed.

  #[using="FIDR B1R fid b1 WF0 cache' AR n0 v Clg"] Lemma sec_map_big : forall sc, In sc (sr_chunks (a_sec A)) -> 8192 <= map_size (cs_n sc).
  Proof.
    intros sc Hin. (first [ pose proof ((sec_chunk_bounds A _ WF0 Hin)) as dR_65; dand5 dR_65 as SB1 _ _ _ SB5 | pose proof (sec_chunk_bounds A _ WF0 Hin) as (SB1 & _ & _ & _ & SB5) ]).
    pose proof (needed_size2_secondary (cs_n sc) ltac:(lia)) as NS2. pose proof (rounded_size_ge (cs_n sc)) as RG. unfold kPageSize, kMaxPrimaryUser in *. lia.
  Qed.

  #[using="FIDR B1R fid b1 CQB WF0 NN MU BXW BX cache' LO LN LU AR lo sp li n0 p v Clg"] Lemma sec_P' : sec_repr_ LPA AL_pasan (a_pl A) (a_sec A) v'.
  Proof.
    (first [ pose proof ((wfS A WF0)) as dR_66; dand4 dR_66 as _ LEN RES _ | destruct (wfS A WF0) as (_ & LEN & RES & _) ]). unfold kChunksBlockCount in RES.
    apply (sec_P A v v' AR NN).
    - intros a H. unfold sfoot_stat in H. offs_h H. alc_h H. apply AGstat_all; unfold xblk, ia_blk, gq_blk; lia.
    - intros a Ha. apply AGpa. unfold kPtrArrayReserve. lia.
    - intros sc a Hin Ha. pose proof GEO as G. geop. unfold kSecondaryHeaderSize in Ha.
      destruct (chunk_eq_dec (ChS sc) ch) as [E|NE].
      + (* [comment removed for export] *)
        pose proof G as G'. (first [ dand9 G' as _ _ _ _ _ _ _ PU _ | destruct G' as (_ & _ & _ & _ & _ & _ & _ & PU & _) ]). rewrite <- E in PU. destruct sc as [mb n1]. cbn [user_of] in PU. unfold sec_user_beg, kPageSize in PU.
        (first [ pose proof ((carved_range A v AR _ CV)) as dR_68; dand3 dR_68 as CL1 CL2 CL3 | pose proof (carved_range A v AR _ CV) as (CL1 & CL2 & CL3) ]). rewrite <- E in CL1, CL2, CL3. cbn [chunk_lo chunk_hi cs_map cs_n] in *.
        pose proof (carved_apart_thr A v AR _ CV) as Dt. pose proof (carved_apart_n0 A v AR _ CV) as Dn. pose proof (carved_apart_f0 A v AR _ CV) as Df.
        rewrite <- E in Dt, Dn, Df. cbn [chunk_lo chunk_hi cs_map cs_n] in Dt, Dn, Df.
        rewrite <- E in Gc, Gs. cbn [chunk_lo chunk_hi cs_map cs_n] in Gc, Gs.   (* [comment removed for export] *)
        (first [ pose proof ((sec_chunk_bounds A _ WF0 Hin)) as dR_69; dand5 dR_69 as SB1 _ _ _ SB5 | pose proof (sec_chunk_bounds A _ WF0 Hin) as (SB1 & _ & _ & _ & SB5) ]). cbn [cs_map cs_n] in SB1, SB5.
        pose proof (needed_size2_secondary n1 ltac:(lia)) as NS2. pose proof (rounded_size_ge n1) as RG. unfold kPageSize in SB5.
        apply MU; [kung_all; lia| |].
        * unfold W0. intros [H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]; kung_all; try lia.
        * intros HB. destruct (BXW a HB) as [(b & Hb & Rb)|[H|[H|[(k & Ck & Rk)|[H|H]]]]]; [| lia| lia| | unfold xblk, ia_blk, gq_blk in H; kung_all; lia| (first [ pose proof (RIW) as dR_70; dand7 dR_70 as _ _ _ _ _ _ Rc | pose proof RIW as (_ & _ & _ & _ & _ & _ & Rc) ]); rewrite <- E in Rc; cbn [chunk_lo chunk_hi cs_map cs_n] in Rc; apply rr24_in in H; pose proof (sec_map_big _ Hin) as MB'; cbn [cs_n] in MB'; clear -H Rc Ha MB'; lia].
          -- pose proof (carved_disjoint A v AR ch _ CV (batch_carved A v AR b Hb) (live_not_batch A v AR p li b LU Hb)) as D.
             rewrite <- E in D. rewrite (proj1 (c24_range (ba_idx b))), (proj2 (c24_range (ba_idx b))) in D. cbn [chunk_lo chunk_hi cs_map cs_n] in D. unfold batch_addr in *. lia.
          -- pose proof (carved_disjoint A v AR ch _ CV (cf_carved k Ck) (live_not_cf p li k LU Ck)) as D.
             rewrite <- E in D. rewrite (proj1 (c24_range k)), (proj2 (c24_range k)) in D. cbn [chunk_lo chunk_hi cs_map cs_n] in D. lia.
      + apply (AGch (ChS sc) Hin NE).
        * intros b Hb E. discriminate.
        * intros k Ck E. discriminate.
        * pose proof (sec_map_big sc Hin) as MB. destruct sc as [mb n1]. cbn [chunk_lo chunk_hi cs_map cs_n] in *. lia.
  Qed.

  #[using="IAH AR v A Clg"] Lemma ia_P' : ia_repr_ LPA AL_pasan ia' v'.
  Proof. destruct IAH as [[-> AG]|[-> IR]]; [| exact IR]. apply (ia_P A v v' AR). exact AG. Qed.

  #[using="FIDR B1R fid b1 CQB WF0 NN MU BXW BX cache' LO LN LU AR lo sp li n0 p v Clg"] Lemma fsbase_P' : fs_base_ LPA (a_pl A) (a_fhint A) v'.
  Proof. apply (fsbase_P A v v' AR NN). intros a Ha. apply AGfs. unfold kFakeFlagsOffset, kFakeStackBytes in *. lia. Qed.
  #[using="FIDR B1R fid b1 CQB WF0 MU BXW BX cache' LO LN LU AR lo sp li n0 p v Clg"] Lemma fsptrs_P' : fs_ptrs_ LPA (a_fs A) (a_fhint A) (a_fframes A) v'.
  Proof. apply (fsptrs_P A v v' AR). intros a Ha. apply AGfs. unfold kFakeFramesOffset, kFakeStackBytes in *. lia. Qed.
  #[using="FIDR B1R fid b1 CQB WF0 MU BXW BX cache' LO LN LU AR lo sp li n0 p v Clg"] Lemma fsflags_P' : fs_flags_ LPA (a_fs A) (a_fhint A) (a_fframes A) v'.
  Proof. apply (fsflags_P A v v' AR). intros a Ha. apply AGfs. unfold kFakeFlagsOffset, kFakeFramesOffset, kFakeStackBytes in *. lia. Qed.
  #[using="NN AR v"] Lemma maps_P' : maps_repr_ AL_pasan (a_pl A) v'.
  Proof. exact (maps_P A v v' AR NN). Qed.

  #[using="C'O P_l24 FIDR B1R fid b1 CQB WF0 NN MU BXW BX LO LN LU AR lo sp li n0 p v Clg"] Lemma cache_P' : cache_repr_ LPA (a_pl A) cache' (a_cache_inited A) v'.
  Proof.
    apply (cache_P A v v' AR NN). intros c' Hc'.
    destruct (Z.eq_dec c' kQuarantineBatchClass) as [->|NE]; [exact P_l24|].
    apply (cache_line_P A v v' AR NN cache' c' Hc'); [rewrite (C'O c' NE); reflexivity|].
    intros a Ha. pose proof GEO as G. geop. offs_h Ha. cbv beta in Ha. unfold kQuarantineBatchClass in NE. apply AGthr; lia.
  Qed.

  #[using="CQB WF0 NN MU BXW BX LO LN LU AR lo sp li n0 v Clg"] Lemma live_P' : live_repr_ LPA sb (free_lm A p) v'.
  Proof.
    apply (live_sub_P A v v' AR NN).
    - intros u li' Hl. unfold free_lm in Hl. rewrite lookup_delete_Some in Hl. exact (proj2 Hl).
    - intros u li' a Hl Ha. unfold free_lm in Hl. rewrite lookup_delete_Some in Hl. destruct Hl as [NEu Hl].
      apply (AGch (li_chunk li') (known_carved A v AR _ _ (known_live A v AR u li' Hl))).
      + intros E. exact (live_live_chunk A v AR u p li' li Hl LU ltac:(congruence) E).
      + intros b Hb. exact (live_not_batch A v AR u li' b Hl Hb).
      + intros k Ck. exact (live_not_cf u li' k Hl Ck).
      + exact Ha.
  Qed.

  (* [comment removed for export] *)

  #[using="QT'E P_brg P_qcg P_br P_qc P_ctx P_hdr FIDR B1M B1R fid b1 CQB R WF0 NN MU BXW BX cache' LO LN LU AR lo sp li n0 p v Clg"] Lemma quar_P' : quarantine_repr_ LPA AL_pasan (a_pl A) qt' qg' v'.
  Proof.
    (first [ pose proof ((ar_quar _ _ _ _ _ R)) as dR_71; dand3 dR_71 as QT QG QR | pose proof (ar_quar _ _ _ _ _ R) as (QT & QG & QR) ]). unfold quarantine_repr_. change (p_sb (a_pl A)) with sb in *. pose proof GEO as G. geop.
    split; [|split].
    - (* [comment removed for export] *)
      unfold qcache_repr. offs. (first [ pose proof ((u64x4_of_rw v' _ _ _ _ _ P_qc)) as dR_72; dand4 dR_72 as Y1 Y2 Y3 Y4 | destruct (u64x4_of_rw v' _ _ _ _ _ P_qc) as (Y1 & Y2 & Y3 & Y4) ]).
      replace (thr + 80 + 0) with (thr + 80) by lia.
      split; [rewrite Z.add_0_r in Y1; exact Y1|]. split; [exact Y2|]. split; [exact Y3|]. split; [exact Y4| exact P_br].
    - (* [comment removed for export] *)
      unfold qcache_repr. pose proof P_qcg as X. cbv zeta in X. (first [ dand4 X as Y1 Y2 Y3 Y4 | destruct X as (Y1 & Y2 & Y3 & Y4) ]).
      split; [exact Y1|]. split; [exact Y2|]. split; [exact Y3|]. split; [exact Y4| exact P_brg].
    - (* [comment removed for export] *)
      intros e He. destruct (QT'E e He) as [Hold| ->].
      + apply (quar_entry_P A v v' AR NN e Hold). intros a Ha.
        apply (AGch (qe_chunk e) (known_carved A v AR _ _ (known_quar A v AR e Hold))).
        * intros E. exact (live_not_quar_chunk A v AR p li e LU Hold (eq_sym E)).
        * intros b Hb. exact (quar_not_batch A v AR e b Hold Hb).
        * intros k Ck. exact (quar_not_cf e k Hold Ck).
        * exact Ha.
      + cbn [qe_chunk qe_n]. (first [ pose proof ((ar_live _ _ _ _ _ R p li LU)) as dR_74; dand3 dR_74 as HR MUo MC | destruct (ar_live _ _ _ _ _ R p li LU) as (HR & MUo & MC) ]). rewrite LN in HR, MUo. change (p_sb (a_pl A)) with sb in HR, MC.
        (first [ dand9 G as PM CL1 L1 L2 CL2 NR R8 PU G' | destruct G as (PM & CL1 & L1 & L2 & CL2 & NR & R8 & PU & G') ]).
        assert (US : user_size n0 = n0) by (exact (proj2 (proj2 (user_size_pos n0 ltac:(lia))) ltac:(lia))).
        split; [|split].
        * (* [comment removed for export] *)
          destruct HR as [(ido & b10 & IDoR & Hb1 & Hb1m & RC) LH]. unfold hdr_repr_. cbv zeta. rewrite <- PU.
          pose proof RC as CTXo. unfold chunk_hdr_cells in CTXo. cbn [ch_state ch_b1 ch_size ch_ctx] in CTXo. rewrite US, <- PU in CTXo.
          apply (rw_cells_app_split _ _ [C1 (Z_to_bv 8 CHUNK_ALLOCATED); C1 (Z_to_bv 8 b10); C2 (wz (size_hi n0)); C4 (wz n0)] [C8 (wz ido)]) in CTXo as [_ CTXo].
          cbn [cells_size csize Nat.add] in CTXo. replace (p - 16 + Z.of_nat 8) with (p + -8) in CTXo by lia.
          split.
          -- exists ido, b1. split; [exact IDoR|]. split; [exact B1R|]. split; [exact B1M|].
             unfold chunk_hdr_cells. cbn [ch_state ch_b1 ch_size ch_ctx]. rewrite US.
             apply (rw_cells_app_join _ _ [C1 (Z_to_bv 8 CHUNK_QUARANTINE); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n0)); C4 (wz n0)] [C8 (wz ido)]).
             ++ replace (p - 16) with (p + -16) by lia. exact P_hdr.
             ++ cbn [cells_size csize Nat.add]. replace (p - 16 + Z.of_nat 8) with (p + -8) by lia.
                eapply rw_cells_agree; [exact CTXo|]. cbn [cells_size csize Nat.add]. intros i Hi. apply AGown; lia.
          -- intros NE16. pose proof NE16 as NE16'. rewrite PU in NE16'. destruct (LH NE16') as [X Y]. rewrite <- PU in Y.
             assert (AB16 : alloc_beg sb ch + 16 <= p - 16).
             { pose proof KN as K. unfold known in K. destruct (li_chunk li) as [[c' k']|[mb n0']] eqn:EC.
               - (first [ dand4 K as Hc Hk Hn Hcl | destruct K as (Hc & Hk & Hn & Hcl) ]). (first [ pose proof ((primary_layout sb c' k' n0 Hc Hn Hcl)) as dR_77; dand5 dR_77 as _ _ _ _ L4 | pose proof (primary_layout sb c' k' n0 Hc Hn Hcl) as (_ & _ & _ & _ & L4) ]). cbv zeta in L4.
                 cbn [alloc_beg user_of] in *. pose proof (L4 NE16') as L4'. rewrite <- PU in L4'. exact L4'.
               - (first [ dand3 K as Hin Hn -> | destruct K as (Hin & Hn & ->) ]). (first [ pose proof ((secondary_layout mb n0 Hn)) as dR_79; dand7 dR_79 as _ S2 _ _ S5 S6 _ | pose proof (secondary_layout mb n0 Hn) as (_ & S2 & _ & _ & S5 & S6 & _) ]). cbn [alloc_beg user_of] in *.
                 unfold sec_alloc_beg, sec_user_beg, kPageSize in *. lia. }
             assert (ABlo : chunk_lo sb ch <= alloc_beg sb ch).
             { destruct (li_chunk li) as [[c' k']|[mb n0']]; cbn [chunk_lo alloc_beg]; [lia|]. unfold sec_alloc_beg, kPageSize. lia. }
             split; [eapply u64_at_agree; [exact X|] | eapply u64_at_agree; [exact Y|]]; intros i Hi; apply AGown; lia.
        * destruct P_ctx as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exists (le8 (wz fid)). split; [rewrite length_le8; reflexivity| rewrite <- PU; exact B].
        * apply (mapped_N v v' NN); [kung_all; lia| kung_all; lia| lia| exact MC].
  Qed.

  #[using="P_dr"] Lemma depot_P' : depot_repr_ LPA AL_pasan (a_pl A) D' v'.
  Proof. unfold depot_repr_. cbn [depot_rep DepotRepL]. exact P_dr. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="P_sh FIDR B1R fid b1 WF0 LN LU AR sp li A Clg"] Lemma requar : forall base L rest, 0 <= L ->
    bytes_at rsegs v base (fa8 L ++ shpat n0 ++ rest) -> sh p = base + L ->
    (forall z, base <= z < base + L -> v' (wz z) = v (wz z)) ->
    (forall z, base + L + r8 <= z < base + L + r8 + Z.of_nat (length rest) -> v' (wz z) = v (wz z)) ->
    bytes_at rsegs v' base (fa8 L ++ fd8 r8 ++ rest).
  Proof.
    intros base L rest L0 B SP AG1 AG2. pose proof GEO as G. geop.
    assert (LF : Z.of_nat (length (fa8 L)) = L) by (unfold fa8; rewrite repeat_length; lia).
    assert (LS : Z.of_nat (length (shpat n0)) = r8) by (rewrite shpat_length; lia).
    assert (LD : Z.of_nat (length (fd8 r8)) = r8) by (unfold fd8; rewrite repeat_length; lia).
    apply bytes_at_app in B as [B1 B]. apply bytes_at_app in B as [B2 B3]. rewrite LF in B, B2, B3 |- * || rewrite LF in B2, B3. rewrite LS in B3.
    apply bytes_at_app. split.
    - eapply bytes_at_agree_gen; [exact B1|]. intros i Hi. apply AG1. lia.
    - replace (base + Z.of_nat (length (fa8 L))) with (base + L) by lia. apply bytes_at_app. split.
      + unfold fd8, kAsanHeapFreeMagic. rewrite <- SP. exact P_sh.
      + replace (base + L + Z.of_nat (length (fd8 r8))) with (base + L + r8) by lia.
        eapply bytes_at_agree_gen; [exact B3|]. intros i Hi. apply AG2. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="R'F R'O C'S C'O QT'B LU AR p v Clg"] Lemma old_state : forall c k, 1 <= c <= 30 ->
    (p_free_ reg' c k \/ p_cached_ cache' c k \/ p_batch_ qt' qg' c k) ->
    (p_free_ (a_reg A) c k \/ p_cached_ (a_cache A) c k \/ p_batch_ qt qg c k) /\ carved A (ChP (CP c k)) /\ ChP (CP c k) <> ch.
  Proof.
    intros c k Hc ST.
    assert (ST0 : p_free_ (a_reg A) c k \/ p_cached_ (a_cache A) c k \/ p_batch_ qt qg c k).
    { destruct ST as [F|[C|[E B]]].
      - destruct (Z.eq_dec c kQuarantineBatchClass) as [->|NE]; [left; exact (R'F k F)|]. unfold p_free_ in *. rewrite (R'O c NE) in F. left. exact F.
      - destruct (Z.eq_dec c kQuarantineBatchClass) as [->|NE]; [destruct (C'S k C) as [C0|F0]; [right; left; exact C0| left; exact F0]|].
        unfold p_cached_ in *. rewrite (C'O c NE) in C. right; left. exact C.
      - subst c. unfold batch_indices_ in B. apply in_map_iff in B as (b & <- & Hb). destruct (QT'B b Hb) as [O|[C|F]]; [| right; left; exact C| left; exact F].
        right; right. split; [reflexivity|]. exact O. }
    split; [exact ST0|].
    destruct ST0 as [F|[C|[E B]]].
    - split; [exact (free_carved A v AR c k Hc F)|]. intros EQ. exact (live_not_free A v AR p li c k LU Hc F (eq_sym EQ)).
    - split; [exact (cached_carved A v AR c k Hc C)|]. intros EQ. exact (live_not_cached A v AR p li c k LU Hc C (eq_sym EQ)).
    - subst c. unfold batch_indices_ in B. apply in_map_iff in B as (b & <- & Hb).
      split; [exact (batch_carved A v AR b Hb)|]. intros EQ. exact (live_not_batch A v AR p li b LU Hb (eq_sym EQ)).
  Qed.

  (* [comment removed for export] *)
  #[using="QT'E FIDR B1R fid b1 WF0 cache' qg' qt' LN LU AR n0 p v Clg"] Lemma tails_apart : forall c', 1 <= c' <= 30 ->
    chunk_hi sb ch <= region_beg sb c' + rg_allocated_user (a_reg A c') \/ region_beg sb c' + kRegionSize <= chunk_lo sb ch.
  Proof.
    intros c' Hc'. pose proof (region_piece_bounds A c' WF0 Hc') as RB'. cbv zeta in RB'. change (a_sb A) with sb in *.
    (first [ pose proof ((sb_facts A WF0)) as dR_80; dand5 dR_80 as _ _ HB6 RSB SCE | pose proof (sb_facts A WF0) as (_ & _ & HB6 & RSB & SCE) ]). change (a_sb A) with sb in *.
    pose proof CV as C. destruct (li_chunk li) as [[c k]|s] eqn:EC.
    - pose proof (carved_prim_where A v AR c k C) as W. change (a_sb A) with sb in W. destruct C as [Hc _]. cbn [chunk_lo chunk_hi alloc_beg].
      destruct (Z.eq_dec c c') as [->|NC]; [left; lia|]. destruct (regions_disjoint sb c c' NC ltac:(lia) ltac:(lia)); [left| right]; kung_all; lia.
    - unfold carved in C. destruct (sec_apart_b6 A v AR s C) as [D|D]; destruct s as [mb n1]; cbn [chunk_lo chunk_hi cs_map cs_n] in *;
        unfold a_b6 in *; [left| right]; kung_all; lia.
  Qed.

  #[using="R'F R'E R'O C'S C'O QT'B QT'E P_sh P_ctx P_hdr FIDR B1R fid b1 CQB R WF0 MU BXW BX LO LN LU AR lo sp li n0 v Clg"] Lemma shadow_P' : shadow_repr_ LPA sb reg' cache' (free_lm A p) qt' qg' v'.
  Proof.
    (first [ pose proof ((ar_shadow _ _ _ _ _ R)) as dR_81; dand6 dR_81 as S1 S2 S3 S4 S5 S6 | pose proof (ar_shadow _ _ _ _ _ R) as (S1 & S2 & S3 & S4 & S5 & S6) ]). pose proof GEO as G. geop. change (a_sb A) with sb in *.
    (first [ pose proof ((carved_shadow A v AR ch CV)) as dR_82; dand5 dR_82 as CE CHS CHR CM1 CM2 | pose proof (carved_shadow A v AR ch CV) as (CE & CHS & CHR & CM1 & CM2) ]).
    (first [ dand9 G as PM CL1 L1 L2 CL2 NR R8 PU G' | destruct G as (PM & CL1 & L1 & L2 & CL2 & NR & R8 & PU & G') ]).
    assert (SE : sh (p + 8 * r8) = sh p + r8) by (unfold sh; rewrite (Z.mul_comm 8 r8), Z.div_add by lia; lia).
    pose proof (sh_mono _ _ L1) as SM1. pose proof (sh_mono _ _ L2) as SM2. pose proof (sh_mono (p + -16) p ltac:(lia)) as SM3.
    assert (US : user_size n0 = n0) by (exact (proj2 (proj2 (user_size_pos n0 ltac:(lia))) ltac:(lia))).
    split; [|split; [|split; [|split; [|split]]]].
    - (* [comment removed for export] *)
      intros c k Hc ST. (first [ pose proof ((old_state c k Hc ST)) as dR_84; dand3 dR_84 as ST0 CK NEQ | destruct (old_state c k Hc ST) as (ST0 & CK & NEQ) ]).
      apply (shadow_free_P A v v' AR c k Hc ST0). intros z Hz.
      pose proof (carved_shadow A v AR _ CK) as (E & _). cbn [chunk_lo chunk_hi alloc_beg] in E.
      apply (AGsh (ChP (CP c k)) CK NEQ). cbn [chunk_lo chunk_hi alloc_beg]. lia.
    - (* [comment removed for export] *)
      intros u c k n1 Hl. unfold free_lm in Hl. rewrite lookup_delete_Some in Hl. destruct Hl as [NEu Hl].
      apply (shadow_live_P A v v' AR u c k n1 Hl). intros z Hz.
      pose proof (known_carved A v AR _ _ (known_live A v AR u _ Hl)) as CK. cbn [li_chunk] in CK.
      pose proof (carved_shadow A v AR _ CK) as (E & _). cbn [chunk_lo chunk_hi alloc_beg] in E.
      apply (AGsh (ChP (CP c k)) CK); [| cbn [chunk_lo chunk_hi alloc_beg]; lia].
      intros EQ. exact (live_live_chunk A v AR u p _ li Hl LU (fun H => NEu (eq_sym H)) EQ).
    - (* [comment removed for export] *)
      intros c k n1 He. destruct (QT'E _ He) as [Hold|EQ].
      + apply (shadow_quar_P A v v' AR c k n1 Hold). intros z Hz.
        pose proof (known_carved A v AR _ _ (known_quar A v AR _ Hold)) as CK. cbn [qe_chunk] in CK.
        pose proof (carved_shadow A v AR _ CK) as (E & _). cbn [chunk_lo chunk_hi alloc_beg] in E.
        apply (AGsh (ChP (CP c k)) CK); [| cbn [chunk_lo chunk_hi alloc_beg]; lia].
        intros EQ. exact (live_not_quar_chunk A v AR p li _ LU Hold (eq_sym EQ)).
      + injection EQ as EC En. subst n1.
        assert (Hl : a_livemap A !! p = Some (LI (ChP (CP c k)) n0)) by (rewrite LU; destruct li; cbn in EC, LN; subst; reflexivity).
        pose proof (S2 p c k n0 Hl) as B. pose proof KN as K. rewrite <- EC in K. unfold known in K. (first [ dand4 K as Hc Hk Hn Hcl | destruct K as (Hc & Hk & Hn & Hcl) ]).
        (first [ pose proof ((chunk_shadow A v AR c k Hc Hk)) as dR_86; dand4 dR_86 as E HS HR _ | pose proof (chunk_shadow A v AR c k Hc Hk) as (E & HS & HR & _) ]).
        rewrite <- EC in CE, CHS, CL1, CL2, L1, L2, SM1, SM2, PU. cbn [chunk_lo chunk_hi alloc_beg user_of] in CE, CHS, CL1, CL2, L1, L2, SM1, SM2, PU. unfold user_beg in PU.
        (first [ pose proof ((carved_chunk_bounds A c k WF0 Hc Hk)) as dR_87; dand4 dR_87 as _ _ B3 _ | pose proof (carved_chunk_bounds A c k WF0 Hc Hk) as (_ & _ & B3 & _) ]). pose proof (rz_size_range n0) as RZ.
        assert (ABM : chunk_addr sb c k mod 8 = 0) by (apply (mod0_down _ 32 8); [exists 4; reflexivity| exact B3]).
        assert (RZM : rz_size n0 mod 8 = 0) by (apply Z.mod_divide; [lia|]; exists (rz_size n0 / 8); lia).
        pose proof (sh_add (chunk_addr sb c k) (rz_size n0) ABM RZM) as SHP. rewrite <- PU in SHP.
        pose proof (pshadow_live_length c n0 ltac:(lia) Hcl) as PL. unfold pshadow_live in PL. rewrite !length_app, !Nat2Z.inj_add in PL.
        unfold pshadow_quar. unfold pshadow_live in B. rewrite US in B, PL |- *.
        unfold fa8 in PL. rewrite !repeat_length in PL. rewrite shpat_length in PL by lia.
        apply (requar (sh (chunk_addr sb c k)) (rz_size n0 / 8)); [lia| exact B| lia| |].
        * intros z Hz. apply AGhs; [apply HS; lia| lia].
        * intros z Hz. unfold fa8 in Hz. rewrite !repeat_length in Hz. apply AGhs; [apply HS; lia| lia].
    - (* [comment removed for export] *)
      intros c' Hc'.
      assert (EX : rg_allocated_user (reg' c') = rg_allocated_user (a_reg A c') /\ rg_mapped_user (reg' c') = rg_mapped_user (a_reg A c') /\
                   rg_mapped_fa (reg' c') = rg_mapped_fa (a_reg A c')).
      { destruct (Z.eq_dec c' kQuarantineBatchClass) as [->|NEc]; [destruct R'E as (EMU & EAL & EFA); exact (conj EAL (conj EMU EFA))| rewrite (R'O c' NEc); OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity]. }
      cbv zeta. (first [ dand3 EX as EX1 EX2 EX3 | destruct EX as (EX1 & EX2 & EX3) ]). rewrite EX1, EX2, EX3.
      (first [ pose proof ((region_tail_shadow A v AR c' Hc')) as dR_89; dand7 dR_89 as E1 E1' E2 HS1 HS2 _ M4 | pose proof (region_tail_shadow A v AR c' Hc') as (E1 & E1' & E2 & HS1 & HS2 & _ & M4) ]). cbv zeta in E1, E1', E2, HS1, HS2, M4.
      change (a_sb A) with sb in *. pose proof (region_piece_bounds A c' WF0 Hc') as RB'. cbv zeta in RB'. change (a_sb A) with sb in RB'.
      (first [ dand12 RB' as Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10 Q11 Q12 | destruct RB' as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12) ]).
      pose proof (tails_apart c' Hc') as TA.
      pose proof (sh_mono (chunk_hi sb ch) (region_beg sb c' + rg_allocated_user (a_reg A c'))) as T1.
      pose proof (sh_mono (region_beg sb c' + kRegionSize) (chunk_lo sb ch)) as T2.
      pose proof (sh_mono (region_beg sb c' + rg_mapped_user (a_reg A c')) (region_beg sb c' + kRegionSize) ltac:(kung_all; lia)) as T3.
      pose proof (sh_mono (region_beg sb c' + kFreeArrayOffset + rg_mapped_fa (a_reg A c')) (region_beg sb c' + kRegionSize) ltac:(kung_all; lia)) as T4.
      pose proof (sh_mono (region_beg sb c' + rg_allocated_user (a_reg A c')) (region_beg sb c' + kFreeArrayOffset) ltac:(kung_all; lia)) as T5.
      apply (shadow_tails_P A v v' AR c' Hc'); intros z Hz; apply AGhs.
      + apply HS1. exact Hz.
      + destruct TA as [TA|TA]; [specialize (T1 TA)| specialize (T2 TA)]; lia.
      + apply HS2. exact Hz.
      + destruct TA as [TA|TA]; [specialize (T1 TA)| specialize (T2 TA)]; lia.
    - (* [comment removed for export] *)
      intros u mb n1 Hl. unfold free_lm in Hl. rewrite lookup_delete_Some in Hl. destruct Hl as [NEu Hl].
      apply (shadow_seclive_P A v v' AR u mb n1 Hl). intros z Hz.
      pose proof (known_carved A v AR _ _ (known_live A v AR u _ Hl)) as CK. cbn [li_chunk] in CK.
      pose proof (carved_shadow A v AR _ CK) as (E & _). cbn [chunk_lo chunk_hi cs_map cs_n] in E.
      apply (AGsh (ChS (CS mb n1)) CK); [| cbn [chunk_lo chunk_hi cs_map cs_n]; lia].
      intros EQ. exact (live_live_chunk A v AR u p _ li Hl LU (fun H => NEu (eq_sym H)) EQ).
    - (* [comment removed for export] *)
      intros mb n2 n1 He. destruct (QT'E _ He) as [Hold|EQ].
      + apply (shadow_secquar_P A v v' AR mb n2 n1 Hold). intros z Hz.
        pose proof (known_quar A v AR _ Hold) as K. pose proof (known_carved A v AR _ _ K) as CK. cbn [qe_chunk qe_n] in CK, K. unfold known in K. (first [ dand3 K as _ _ -> | destruct K as (_ & _ & ->) ]).
        pose proof (carved_shadow A v AR _ CK) as (E & _). cbn [chunk_lo chunk_hi cs_map cs_n] in E.
        apply (AGsh (ChS (CS mb n1)) CK); [| cbn [chunk_lo chunk_hi cs_map cs_n]; lia].
        intros EQ. exact (live_not_quar_chunk A v AR p li _ LU Hold (eq_sym EQ)).
      + injection EQ as EC En. subst n1. pose proof KN as K. rewrite <- EC in K. unfold known in K. (first [ dand3 K as Hin Hn -> | destruct K as (Hin & Hn & ->) ]).
        assert (Hl : a_livemap A !! p = Some (LI (ChS (CS mb n0)) n0)) by (rewrite LU; destruct li; cbn in EC, LN; subst; reflexivity).
        pose proof (S5 p mb n0 Hl) as B.
        (first [ pose proof ((sec_shadow A v AR _ Hin)) as dR_93; dand3 dR_93 as E HS HR | pose proof (sec_shadow A v AR _ Hin) as (E & HS & HR) ]). cbn [cs_map cs_n] in E, HS, HR.
        rewrite <- EC in PU. cbn [user_of] in PU. unfold sec_user_beg, kPageSize in PU. replace (mb + 4096 + 2048) with (mb + 6144) in PU by lia.
        (first [ pose proof ((sec_chunk_bounds A _ WF0 Hin)) as dR_94; dand3 dR_94 as _ MB2 _ | pose proof (sec_chunk_bounds A _ WF0 Hin) as (_ & MB2 & _) ]). cbn [cs_map] in MB2.
        assert (M8 : mb mod 8 = 0) by (apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact MB2]).
        pose proof (sh_add mb 6144 M8 eq_refl) as SHP. change (6144 / 8) with 768 in SHP. rewrite <- PU in SHP.
        pose proof (sshadow_live_length n0 Hn) as PL. unfold sshadow_live in PL. rewrite !length_app, !Nat2Z.inj_add in PL.
        unfold sshadow_quar. unfold sshadow_live in B. rewrite US in B, PL |- *.
        unfold fa8 in PL. rewrite !repeat_length in PL. rewrite shpat_length in PL by lia. pose proof (sec_map_big _ Hin) as MB. cbn [cs_n] in MB.
        apply (requar (sh mb) 768); [lia| exact B| lia| |].
        * intros z Hz. apply AGhs; [apply HS; lia| lia].
        * intros z Hz. unfold fa8 in Hz. rewrite !repeat_length in Hz. apply AGhs; [apply HS; lia| lia].
  Qed.

  (* [comment removed for export] *)
  #[using="P_nf24 P_mx24 RG24 R'F R'E R'O C'S C'O QT'B QT'E QPD QLK IAP IAL IAH P_l24 P_brg P_qcg P_br P_qc P_dr P_sh P_ctx P_hdr P_unw FIDR B1M B1R fid b1 CQB R WF0 NN MU BXW BX LO LN LU AR lo sp li n0 v"] Theorem free_arepr3 : u8_at rsegs v' 0xb20c9 0 -> @arepr _ DepotRepL LPA AL_pasan [] (freeA3 A p qt' qg' cache' D' ia' reg') v'.
  Proof.
    intros QRL.
    constructor; cbn [freeA3 a_pl a_sb a_reg a_cache a_cache_inited a_livemap a_qthread a_qglobal a_sec a_depot a_ia_inited a_fhint a_fs a_fframes a_qlimbo a_scred a_deadsh].
    - exact consts_P'. - exact (locks_P' QRL). - exact regions_P'. - exact cache_P'. - exact live_P'. - exact quar_P'. - exact sec_P'.
    - exact depot_P'. - exact ia_P'. - exact fsbase_P'. - exact fsptrs_P'. - exact fsflags_P'. - exact maps_P'. - exact shadow_P'.
  Qed.
  (* [comment removed for export] *)
  #[using="P_nf24 P_mx24 RG24 R'F R'E R'O C'S C'O QT'B QT'E QPD QLK IAP IAL IAH P_l24 P_brg P_qcg P_br P_qc P_dr P_sh P_ctx P_hdr P_unw FIDR B1M B1R fid b1 CQB R WF0 NN MU BXW BX LO LN LU AR lo sp li n0 v"] Theorem free_arepr3R : u8_at rsegs v' 0xb20c9 1 -> @arepr _ DepotRepL LPA AL_pasan [al_instance AL_pasan + off_q_recycle_mutex] (freeA3 A p qt' qg' cache' D' ia' reg') v'.
  Proof.
    intros QRL.
    constructor; cbn [freeA3 a_pl a_sb a_reg a_cache a_cache_inited a_livemap a_qthread a_qglobal a_sec a_depot a_ia_inited a_fhint a_fs a_fframes a_qlimbo a_scred a_deadsh].
    - exact consts_P'. - exact (locks_P'R QRL). - exact regions_P'. - exact cache_P'. - exact live_P'. - exact quar_P'. - exact sec_P'.
    - exact depot_P'. - exact ia_P'. - exact fsbase_P'. - exact fsptrs_P'. - exact fsflags_P'. - exact maps_P'. - exact shadow_P'.
  Qed.
End FreeRepr3.
End AFreeB3F.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB4c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB4F.AFreeB3F.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.  (* [comment removed for export] *)
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
#[local] Notation WF := (WF AL_pasan).   (* [comment removed for export] *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Notation wz z := (Z_to_bv 64 z) (only parsing).
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kSpaceReserve, kMaxSize in *.

(* [comment removed for export] *)
Section ExtF.
Context {Clg : Ceiling}.
Lemma runtime_maps_extF : forall P reg reg' sec,
  (forall c, 1 <= c <= 30 -> rg_mapped_user (reg' c) = rg_mapped_user (reg c) /\ rg_mapped_fa (reg' c) = rg_mapped_fa (reg c)) ->
  runtime_maps_ P reg' sec = runtime_maps_ P reg sec.
Proof.
  intros P reg reg' sec E. unfold runtime_maps_. f_equal. f_equal. rewrite !flat_map_concat_map. f_equal.
  apply map_ext_in. intros c Hc. apply in_map_iff in Hc as (n & <- & Hn). apply in_seq in Hn.
  destruct (E (Z.of_nat n) ltac:(lia)) as [E1 E2]. cbv zeta. rewrite E1, E2. reflexivity.
Qed.
Lemma heap_shadow_extF : forall sb reg reg' sec a,
  (forall c, 1 <= c <= 30 -> rg_mapped_user (reg' c) = rg_mapped_user (reg c) /\ rg_mapped_fa (reg' c) = rg_mapped_fa (reg c)) ->
  heap_shadow_ sb reg' sec a <-> heap_shadow_ sb reg sec a.
Proof.
  intros sb reg reg' sec a E. unfold heap_shadow_. cbv zeta.
  split; intros [(c & Hc & X)|[(c & Hc & X)|X]];
    first [ left; exists c; split; [exact Hc|]; destruct (E c Hc) as [E1 E2]; rewrite <- ?E1, <- ?E2; exact X
          | left; exists c; split; [exact Hc|]; destruct (E c Hc) as [E1 E2]; rewrite ?E1, ?E2; exact X
          | right; left; exists c; split; [exact Hc|]; destruct (E c Hc) as [E1 E2]; rewrite <- ?E1, <- ?E2; exact X
          | right; left; exists c; split; [exact Hc|]; destruct (E c Hc) as [E1 E2]; rewrite ?E1, ?E2; exact X
          | right; right; exact X ].
Qed.
Lemma owned_iff_extF : forall A A' a,
  a_pl A' = a_pl A -> a_livemap A' = a_livemap A -> a_sec A' = a_sec A -> a_fframes A' = a_fframes A ->
  (forall c, 1 <= c <= 30 -> rg_mapped_user (a_reg A' c) = rg_mapped_user (a_reg A c) /\ rg_mapped_fa (a_reg A' c) = rg_mapped_fa (a_reg A c)) ->
  pa_owned A' a <-> pa_owned A a.
Proof.
  intros A A' a EP EL ES EF ER. unfold pa_owned, aowned, aowned_, runtime_maps, a_sb, a_fs. rewrite EP, EL, ES, EF.
  rewrite (runtime_maps_extF (a_pl A) (a_reg A) (a_reg A') (a_sec A) ER).
  pose proof (heap_shadow_extF (p_sb (a_pl A)) (a_reg A) (a_reg A') (a_sec A) a ER) as HS. tauto.
Qed.
End ExtF.

Section FreeOwnC3.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (A : AState) (m : mem) (md : Model) (p n0 : Z) (li : liveinfo) (sp : word) (v' : mem) (lo : Z).
  Hypothesis AI : @pa_ainv _ DepotRepL A m md.
  Hypothesis LU : a_livemap A !! p = Some li.
  Hypothesis LN : li_n li = n0.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LOS : lo <= bv_unsigned sp.
  Local Notation v := (aview_of (pa_hull A) m).
  Local Notation thr := (p_thr (a_pl A)).
  Local Notation sb := (a_sb A).
  Local Notation ch := (li_chunk li).
  Local Notation r8 := ((n0 + 7) / 8).
  Local Notation n0a := (p_nodes0 (a_pl A)).
  Local Notation f0 := (p_frames0 (a_pl A)).
  Local Notation qt := (a_qthread A).
  Local Notation qg := (a_qglobal A).
  Variables (qt' qg' : list batch) (cache' : Z -> pcache) (D' : list (list Z)) (ia' : bool).
  Variable reg' : Z -> region.
  (* [comment removed for export] *)
  Hypothesis R'X : forall c, 1 <= c <= 30 -> rg_mapped_user (reg' c) = rg_mapped_user (a_reg A c) /\ rg_mapped_fa (reg' c) = rg_mapped_fa (a_reg A c).
  Variable BX : Z -> Prop.
  Hypothesis BXW : forall a, BX a ->
       (exists b, In b (qt ++ qg) /\ batch_addr sb b <= a < batch_addr sb b + kQuarantineBatchBytes)
    \/ (thr + 2128 <= a < thr + 2208)
    \/ (thr + 2784 <= a < thr + 2792)
    \/ (exists k, cf24 A k /\
                  chunk_addr sb kQuarantineBatchClass k <= a < chunk_addr sb kQuarantineBatchClass k + kQuarantineBatchBytes)
    \/ xblk a
    \/ rr24 (a_ri A) a.
  Hypothesis MU : forall a, 0 <= a < 2^64 -> ~ W0 lo (bv_unsigned sp) thr p r8 n0a f0 a -> ~ BX a -> v' (wz a) = v (wz a).
  Hypothesis WMv : wmono rsegs v v'.
  Hypothesis SM : mapped v lo (bv_unsigned sp - lo).
  Local Notation A' := (freeA3 A p qt' qg' cache' D' ia' reg').
  (* [comment removed for export] *)
  Local Notation A1 := (freeA A p qt' qg' cache' D' ia').
  Lemma owned_A' : forall a, pa_owned A' a <-> pa_owned A1 a.
  Proof. intros a. apply owned_iff_extF; [reflexivity| reflexivity| reflexivity| reflexivity|]. cbn [a_reg freeA3 freeA]. exact R'X. Qed.

  Let WF0 : WF A. Proof. exact (ai_wf _ _ _ _ _ _ _ AI). Qed.
  Let AR : WF A /\ @arepr _ DepotRepL LPA AL_pasan [] A v. Proof. exact (conj (ai_wf _ _ _ _ _ _ _ AI) (ai_repr _ _ _ _ _ _ _ AI)). Qed.

  Lemma wmono_NNF : forall (w w' : mem) a, wmono rsegs w w' -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> 0 <= a < 2^64 ->
    w (wz a) <> None -> w' (wz a) <> None.
  Proof.
    intros w w' a WM Ha Hr Hv. specialize (WM (wz a)). unfold wview in WM.
    rewrite unsigned_lit in WM by lia. rewrite (pa_find_segment_none a 1 ltac:(lia) Ha) in WM.
    destruct (w (wz a)); [| congruence]. destruct (w' (wz a)); [congruence|]. exfalso. apply WM; [discriminate| reflexivity].
  Qed.
  Lemma NNoF : forall a, 0 <= a -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> a < 2^64 -> v (Z_to_bv 64 a) <> None -> v' (Z_to_bv 64 a) <> None.
  Proof. intros a H0 H1 H2. apply (wmono_NNF _ _ a WMv); lia. Qed.

  (* [comment removed for export] *)
  Ltac geopF := let Gc := fresh "Gc" in let Gt := fresh "Gt" in let Gn := fresh "Gn" in let Gf := fresh "Gf" in let Gs := fresh "Gs" in
    (first [ pose proof ((GEOP A v p n0 li AR LU LN)) as dR_1; dand4 dR_1 as Gc Gt Gn Gf | pose proof (GEOP A v p n0 li AR LU LN) as (Gc & Gt & Gn & Gf) ]); aobj_lin1 Gc; aobj_lin1 Gt; aobj_lin1 Gn; aobj_lin1 Gf;
    pose proof (GEOS A v p n0 li sp AR LU LN) as Gs; unfold kLowShadowMapBeg, kHighShadowMapBeg, kHighMemBeg in Gs.
  Lemma CVoF : carved A ch. Proof. exact (known_carved A v AR _ _ (KN A v p n0 li AR LU LN)). Qed.

  (* [comment removed for export] *)
  Lemma chunk_owned_oldF : forall a, chunk_lo sb ch <= a < chunk_hi sb ch -> ~ (p <= a < p + n0) -> pa_owned A a.
  Proof.
    intros a Ha NU. apply (carved_owned A v AR ch a CVoF Ha). intros u li' Hl E Hu.
    destruct (Z.eq_dec u p) as [->|NE].
    - rewrite LU in Hl. injection Hl as <-. rewrite LN in Hu. exact (NU Hu).
    - exact (live_live_chunk A v AR u p li' li Hl LU NE E).
  Qed.

  (* [comment removed for export] *)
  Lemma batch_ownedF : forall b a, In b (qt ++ qg) -> batch_addr sb b <= a < batch_addr sb b + kQuarantineBatchBytes -> pa_owned A a.
  Proof.
    intros b a Hb Ha. apply (carved_owned A v AR _ a (batch_carved A v AR b Hb)).
    - rewrite (proj1 (c24_range A b.(ba_idx))), (proj2 (c24_range A (ba_idx b))). unfold batch_addr in Ha. exact Ha.
    - intros u li' Hl E _. exact (live_not_batch A v AR u li' b Hl Hb E).
  Qed.
  Lemma cached_ownedF : forall k a, cf24 A k ->
    chunk_addr sb kQuarantineBatchClass k <= a < chunk_addr sb kQuarantineBatchClass k + kQuarantineBatchBytes -> pa_owned A a.
  Proof.
    intros k a Ck Ha.
    apply (carved_owned A v AR _ a (cf_carved A v AR k Ck)).
    - rewrite (proj1 (c24_range A k)), (proj2 (c24_range A k)). exact Ha.
    - intros u li' Hl E _. exact (live_not_cf A v AR u li' k Hl Ck E).
  Qed.
  (* [comment removed for export] *)
  Lemma rr_ownedF : forall a, rr24 (a_ri A) a -> pa_owned A a.
  Proof.
    intros a H. apply rr24_in in H. (first [ pose proof ((sb_facts A WF0)) as dR_2; dand5 dR_2 as _ _ HB6 RSB SCE | pose proof (sb_facts A WF0) as (_ & _ & HB6 & RSB & SCE) ]).
    (first [ pose proof ((bm_nth_fixed A)) as dR_3; dand8 dR_3 as E0 _ _ _ _ _ E6 _ | pose proof (bm_nth_fixed A) as (E0 & _ & _ & _ & _ & _ & E6 & _) ]). pose proof (bm_sep A 0 6 _ _ _ _ WF0 E0 E6 ltac:(lia)) as D6.
    apply (owned_rt A a (a_ri A) 4096); [apply rt_fixed_in; cbn; tauto| unfold a_ri, p_ri in *; lia| |].
    - intros LUa. destruct (live_user_zone A a WF0 LUa) as [[_ SB]|(i & s & Hi & Rg)].
      + unfold a_ri, p_ri, a_sb in *. lia.
      + pose proof (sec_apart_b6 A v AR s ltac:(eapply nth_error_In; exact Hi)) as D. unfold a_ri, p_ri, a_sb, a_b6 in *. kung_all. lia.
    - intros LF. pose proof (live_frame_zone A a WF0 LF) as FZ. unfold a_ri, p_ri, a_sb, a_b6, a_fs in *. kung_all. unfold kFakeStackBytes, kFakeFramesOffset in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ia_ownedF : forall a, xblk a -> pa_owned A a.
  Proof. intros a H. apply asI_static_owned. cbn [cl_static LPA]. unfold xblk, ia_blk, gq_blk in H. unfold pa_static. lia. Qed.

  (* [comment removed for export] *)
  Lemma frame1F : forall a, 0 <= a < 2^64 -> ~ pa_owned A a -> ~ (lo <= a < bv_unsigned sp) -> ~ newblk p n0 a ->
    v' (wz a) = v (wz a).
  Proof.
    intros a Ha NO NW NB. pose proof (GEO A v p n0 li sp AR LU LN) as G. geopF. unfold newblk, blk in NB.
    apply MU; [exact Ha| |].
    - unfold W0. intros [H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]].
      + exact (NW H).
      + apply NO. apply (thr_owned A v AR). lia.
      + apply NO. apply chunk_owned_oldF; lia.
      + destruct (Z_lt_dec a (p + n0)); [apply NB; left; split; [kung_all; lia| lia]|]. apply NO. apply chunk_owned_oldF; lia.
      + apply NO. apply (thr_owned A v AR). lia.
      + apply NO. apply (dstat_owned A). exact H.
      + apply NO. apply (n0_owned A v AR). kung_all. lia.
      + apply NO. apply (f0_owned A v AR). kung_all. lia.
      + apply NB. right. split; [kung_all; lia| exact H].
      + apply NO. apply (thr_owned A v AR). lia.
    - intros HB. destruct (BXW a HB) as [(b & Hb & Rb)|[H|[H|[(k & Ck & Rk)|[H|H]]]]].
      + apply NO. exact (batch_ownedF b a Hb Rb).
      + apply NO. apply (thr_owned A v AR). lia.
      + apply NO. apply (thr_owned A v AR). lia.
      + apply NO. exact (cached_ownedF k a Ck Rk).
      + apply NO. exact (ia_ownedF a H).
      + apply NO. exact (rr_ownedF a H).
  Qed.

  (* [comment removed for export] *)
  Lemma owned_monoF : forall a, pa_owned A a -> pa_owned A' a.
  Proof.
    intros a H. apply (proj2 (owned_A' a)). unfold pa_owned, aowned, aowned_ in *. cbn [freeA a_pl a_reg a_livemap a_sec a_fframes].
    destruct H as [[S|[[(R1 & NU & NF)|HS]|GH]]|I]; [left; left; exact S| | left; right; left; right; exact HS| left; right; right; exact GH| right; exact I].
    left. right. left. left. split; [exact R1|]. split; [| exact NF]. ((first [ intro dR_9; dex2 dR_9 as u li'; destruct dR_9 as [Hl Hu] | intro dR_9; dand4 dR_9 as u li' Hl Hu | intros (u & li' & Hl & Hu) ])). apply NU. exists u, li'. split; [| exact Hu].
    unfold free_lm in Hl. rewrite lookup_delete_Some in Hl. exact (proj2 Hl).
  Qed.
  (* [comment removed for export] *)
  Lemma owned_newF : forall a, pa_owned A' a -> pa_owned A a \/ newblk p n0 a.
  Proof.
    intros a H. apply (proj1 (owned_A' a)) in H. pose proof (GEO A v p n0 li sp AR LU LN) as G. geopF.
    destruct (decide (p <= a < p + n0)) as [Y|X]; [right; left; split; [kung_all; lia| exact Y]|]. left.
    unfold pa_owned, aowned, aowned_ in *. cbn [freeA a_pl a_reg a_livemap a_sec a_fframes] in H.
    destruct H as [[S|[[(R1 & NU & NF)|HS]|GH]]|I]; [left; left; exact S| | left; right; left; right; exact HS| left; right; right; exact GH| right; exact I].
    left. right. left. left. split; [exact R1|]. split; [| exact NF]. ((first [ intro dR_10; dex2 dR_10 as u li'; destruct dR_10 as [Hl Hu] | intro dR_10; dand4 dR_10 as u li' Hl Hu | intros (u & li' & Hl & Hu) ])). 
    destruct (Z.eq_dec u p) as [->|NE].
    - rewrite LU in Hl. injection Hl as <-. rewrite LN in Hu. exact (X Hu).
    - apply NU. exists u, li'. split; [| exact Hu]. unfold free_lm. rewrite lookup_delete_Some. split; [congruence| exact Hl].
  Qed.
  (* [comment removed for export] *)
  Lemma victim_ownedF : forall a, newblk p n0 a -> pa_owned A' a.
  Proof.
    intros a NB. pose proof (GEO A v p n0 li sp AR LU LN) as G. geopF. (first [ pose proof ((carved_shadow A v AR ch CVoF)) as dR_4; dand3 dR_4 as CE CHS _ | pose proof (carved_shadow A v AR ch CVoF) as (CE & CHS & _) ]).
    (first [ dand8 G as PM CL1 L1 L2 CL2 NR R8 _ | destruct G as (PM & CL1 & L1 & L2 & CL2 & NR & R8 & _) ]).
    unfold newblk, blk in NB. destruct NB as [[_ Ha]|[_ Ha]].
    - (* [comment removed for export] *)
      destruct (carved_in_rt A v AR ch a CVoF ltac:(lia)) as [RIN NF].
      apply (proj2 (owned_A' a)). unfold pa_owned, aowned, aowned_. cbn [freeA a_pl a_reg a_livemap a_sec a_fframes].
      left. right. left. left. split; [exact RIN|]. split; [| exact NF].
      ((first [ intro dR_11; dex2 dR_11 as u li'; destruct dR_11 as [Hl Hu] | intro dR_11; dand4 dR_11 as u li' Hl Hu | intros (u & li' & Hl & Hu) ])). unfold free_lm in Hl. rewrite lookup_delete_Some in Hl. destruct Hl as [NE Hl].
      pose proof (live_user_in_carved A v AR ch a u li' CVoF ltac:(lia) Hl Hu) as E. exact (live_live_chunk A v AR u p li' li Hl LU (fun H => NE (eq_sym H)) E).
    - (* [comment removed for export] *)
      apply owned_monoF. left. right. left. right. left.
      assert (SE : sh (p + 8 * r8) = sh p + r8) by (unfold sh; rewrite (Z.mul_comm 8 r8), Z.div_add by lia; lia).
      pose proof (sh_mono _ _ L1) as SMa. pose proof (sh_mono _ _ L2) as SMb. pose proof (sh_mono (p + -16) p ltac:(lia)) as SMc.
      exact (CHS a ltac:(lia)).
  Qed.

  Theorem free_frame_okF : frame_ok LPA (pa_owned A) (pa_owned A') (bv_unsigned sp) (bv_unsigned sp - lo) (newblk p n0) nowhere v v'.
  Proof.
    pose proof alloc_ceiling_val as CE. unfold frame_ok. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits.
    - intros a Ha NO NO' NW NE' NB _. apply frame1F; [assumption| assumption| replace (bv_unsigned sp - (bv_unsigned sp - lo)) with lo in NW by lia; exact NW| assumption].
    - intros a Ha NI Hv. right. right. apply (wmono_NNF _ _ a WMv); [| exact Ha| exact Hv]. unfold in_image in NI. cbn [cl_image_lo cl_image_hi LPA] in NI. lia.
    - replace (bv_unsigned sp - (bv_unsigned sp - lo)) with lo by lia. eapply mapped_mono; [exact SM|]. intros i Hi. pose proof (zr_word sp) as R; unfold inr64 in R. pose proof alloc_ceiling_val. apply NNoF; lia.
    - intros a Ha F. destruct F.
    - intros a Ha O'. destruct (owned_newF a O'); [left| right; left]; assumption.
    - intros a Ha O NO'. exfalso. exact (NO' (owned_monoF a O)).
    - intros a Ha NB. left. exact (victim_ownedF a NB).
  Qed.

  (* [comment removed for export] *)
  Theorem free_hiddenF : hidden_repr (a_pl A) (a_reg A) (a_sec A) m ->
    hidden_repr (a_pl A) (a_reg A) (a_sec A) (munrestrict (hidc (pa_hull A)) m v').
  Proof.
    intros [H1 H2]. unfold hidden_repr. unfold munrestrict.
    assert (VIS : forall z, 0x60a000 <= z < 2^64 -> m (wz z) <> None -> hidc (pa_hull A) (wz z) = false -> v' (wz z) <> None).
    { intros z Hz Hm E. apply NNoF; [lia| lia| lia|]. unfold aview_of, mrestrict. rewrite E. exact Hm. }
    split.
    - intros z GZ. destruct (H1 z GZ) as [P1 P2]. pose proof GZ as [Hz _].
      destruct (hidc (pa_hull A) (wz z)) eqn:E; [exact (conj P1 P2)|]. split.
      + apply VIS; [unfold in_shadow_maps, kLowShadowMapBeg, kHighShadowMapSize in Hz; kung_all; lia| exact P1| exact E].
      + intros NHS. rewrite <- (P2 NHS).
        transitivity (aview_of (pa_hull A) m (wz z)); [| unfold aview_of, mrestrict; rewrite E; reflexivity].
        pose proof (GEO A v p n0 li sp AR LU LN) as G. geopF. (first [ pose proof ((carved_shadow A v AR ch CVoF)) as dR_6; dand3 dR_6 as CE' CHS _ | pose proof (carved_shadow A v AR ch CVoF) as (CE' & CHS & _) ]).
        (first [ dand18 G as PM CL1 L1 L2 CL2 NR R8 PU T1 T2 N1 N2 F1 F2 S1 S2 CEQ SPR | destruct G as (PM & CL1 & L1 & L2 & CL2 & NR & R8 & PU & T1 & T2 & N1 & N2 & F1 & F2 & S1 & S2 & CEQ & SPR) ]).
        assert (SE : sh (p + 8 * r8) = sh p + r8) by (unfold sh; rewrite (Z.mul_comm 8 r8), Z.div_add by lia; lia).
        pose proof (sh_mono _ _ L1) as SMa. pose proof (sh_mono _ _ L2) as SMb. pose proof (sh_mono (p + -16) p ltac:(lia)) as SMc.
        unfold in_shadow_maps, kLowShadowMapBeg, kHighShadowMapSize in Hz. unfold ASTK in *.
        apply MU; [kung_all; lia| |].
        * unfold W0. intros [H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]; try (kung_all; lia).
          apply NHS. exact (CHS z ltac:(lia)).
        * intros HB. destruct (BXW z HB) as [(b & Hb & Rb)|[H|[H|[(k & Ck & Rk)|[H|H]]]]]; [| kung_all; lia| kung_all; lia| | unfold xblk, ia_blk, gq_blk in H; kung_all; lia|].
          -- pose proof (batch_range A v AR b Hb). kung_all. lia.
          -- pose proof (carved_prim_where A v AR _ _ (cf_carved A v AR k Ck)). kung_all. lia.
          -- apply rr24_in in H. (first [ pose proof ((sb_facts A WF0)) as dR_8; dand5 dR_8 as _ _ HB6 RSB _ | pose proof (sb_facts A WF0) as (_ & _ & HB6 & RSB & _) ]). unfold a_ri, p_ri, a_sb, a_b6 in *. clear -H Hz HB6 RSB. kung_all. lia.
    - intros z Hz NB. destruct (hidc (pa_hull A) (wz z)) eqn:E; [exact (H2 z Hz NB)|]. apply VIS; [unfold kLowShadowMapBeg in Hz; lia| exact (H2 z Hz NB)| exact E].
  Qed.
End FreeOwnC3.
