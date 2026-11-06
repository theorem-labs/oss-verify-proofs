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
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict Refund.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Export ACells.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.  (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).
Notation b8 z := (Z_to_bv 8 z) (only parsing).

(* [comment removed for export] *)
Definition TLIM_MIN : Z := 2^34.   (* [comment removed for export] *)
Lemma TLIM_MIN_eq : TLIM_MIN = 2^34.
Proof. reflexivity. Qed.
#[global] Opaque TLIM_MIN.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Inv.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {DR : DepotRep} (cl : clayout) (L : alayout) (image_ivs : hull) (site_pcs : list Z).
  Let segs := cl_segs cl.
  #[local] Notation u64_at := (u64_at segs).
  #[local] Notation u32_at := (u32_at segs).
  #[local] Notation u16_at := (u16_at segs).
  #[local] Notation u8_at := (u8_at segs).
  #[local] Notation junk_at := (junk_at segs).
  #[local] Notation fill_at := (fill_at segs).

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition wf_place (P : aplace) : Prop :=
    let sb := p_sb P in
    (* [comment removed for export] *)
    0 <= p_b6 P /\ kHighMemBeg <= p_b6 P /\ sb = space_beg_of (p_b6 P) /\
    sb + kSpaceSize + 4096 <= alloc_ceiling /\
    app_rangeA L (p_pa P) kPtrArrayReserve /\ p_pa P + kPtrArrayReserve <= alloc_ceiling /\ p_pa P mod 4096 = 0 /\
    app_rangeA L (p_thr P) 4096 /\ p_thr P + 4096 <= alloc_ceiling /\ p_thr P mod 4096 = 0 /\
    app_rangeA L (p_ctx P) 0x10000 /\ p_ctx P + 0x10000 <= alloc_ceiling /\ p_ctx P mod 4096 = 0 /\
    app_rangeA L (p_nodes0 P) kDepotNodesBlock /\ p_nodes0 P + kDepotNodesBlock <= alloc_ceiling /\ p_nodes0 P mod 4096 = 0 /\
    app_rangeA L (p_frames0 P) kStackStoreBlockBytes /\ p_frames0 P + kStackStoreBlockBytes <= alloc_ceiling /\ p_frames0 P mod 4096 = 0 /\
    app_rangeA L (p_fs P) kFakeStackBytes /\ p_fs P + kFakeStackBytes <= alloc_ceiling /\ p_fs P mod 4096 = 0 /\
    app_rangeA L (p_itab P) 0x38e000 /\ p_itab P + 0x38e000 <= alloc_ceiling /\ p_itab P mod 4096 = 0 /\
    app_rangeA L (p_m64k P) 0x10000 /\ p_m64k P + 0x10000 <= alloc_ceiling /\ p_m64k P mod 4096 = 0 /\
    app_rangeA L (p_gvec P) 4096 /\ p_gvec P + 4096 <= alloc_ceiling /\ p_gvec P mod 4096 = 0 /\
    app_rangeA L (p_dvec P) 4096 /\ p_dvec P + 4096 <= alloc_ceiling /\ p_dvec P mod 4096 = 0 /\
    app_rangeA L (p_m11 P) 4096 /\ p_m11 P + 4096 <= alloc_ceiling /\ p_m11 P mod 4096 = 0 /\
    app_rangeA L (p_dtls P) 4096 /\ p_dtls P + 4096 <= alloc_ceiling /\ p_dtls P mod 4096 = 0 /\
    0 <= p_tlsb P < 2^64 /\ 0 <= p_tlse P < 2^64 /\
    (* [comment removed for export] *)
    Forall (fun k => (1 <= length k <= 255)%nat) (p_dkeys P) /\ NoDup (map depot_hashC (p_dkeys P)) /\
    (length (p_dkeys P) <= 2048)%nat /\
    (* [comment removed for export] *)
    alloc_ceiling + 0x800000 <= p_sp0 P <= 2^47 /\ 0 <= p_stk_span P <= 0x240000 /\ p_sp0 P mod 16 = 0 /\
    p_sp0 P + p_stk_span P <= 2^47 /\   (* [comment removed for export] *)
    0 <= p_stk_top P < 2^64 /\ 0 <= p_stk_bot P < 2^64 /\
    0 <= p_eager0 P /\
    (* [comment removed for export] *)
    p_eager0 P <= 2^25.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition wf_extra (P : aplace) : Prop :=
    Forall (fun lh => 0 <= fst lh /\ fst lh <= snd lh <= 2^47) (p_extra P) /\
    (forall lo hi a, In (lo, hi) (p_extra P) -> lo <= a < hi ->
        (0 <= a <= kLowMemEnd \/ kHighMemBeg <= a < alloc_ceiling) ->
        forall z, sh a - sh a mod 8 <= z < sh a - sh a mod 8 + 8 -> exists lo' hi', In (lo', hi') (p_extra P) /\ lo' <= z < hi') /\
    (* [comment removed for export] *)
    (forall lo hi, In (lo, hi) (p_extra P) -> lo mod 4096 = 0 /\ hi mod 4096 = 0) /\
    cl_image_hi cl <= p_brk P <= cl_image_hi cl + 2^31 /\   (* [comment removed for export] *)
    (* [comment removed for export] *)
    (forall pc ra, In pc site_pcs -> In ra (cl_sites cl) -> In [pc; ra] (p_dkeys P) /\ In [pc] (p_dkeys P)) /\
    (* [comment removed for export] *)
    hull_bytes (p_extra P) <= 2^28 + 2^26 /\   (* [comment removed for export] *)
    (* [comment removed for export] *)
    (forall lo hi a, In (lo, hi) (p_extra P) -> lo <= a < hi -> ~ (p_sb P <= a < p_sb P + kSpaceSize)) /\
    (* [comment removed for export] *)
    TLIM_MIN <= p_tlim P.

  (* [comment removed for export] *)
  Definition big_maps_ (P : aplace) (sec : secreg) : list (Z * Z) :=
    [ (p_b6 P, kSpaceReserve); (p_pa P, kPtrArrayReserve); (kHighShadowMapBeg, kHighShadowMapSize); (kLowShadowMapBeg, 0x10000000);
      (p_thr P, 4096); (p_ctx P, 0x10000); (p_fs P, kFakeStackBytes); (p_nodes0 P, kDepotNodesBlock);
      (p_frames0 P, kStackStoreBlockBytes); (p_itab P, 0x38e000); (p_m64k P, 0x10000);
      (p_gvec P, 4096); (p_dvec P, 4096); (p_m11 P, 4096); (p_dtls P, 4096) ]
    ++ map (fun s => (cs_map s, map_size (cs_n s))) (sr_chunks sec).
  Definition big_maps (A : AState) : list (Z * Z) := big_maps_ (a_pl A) (a_sec A).
  (* [comment removed for export] *)
  Definition wf_bigmaps_ (P : aplace) (sec : secreg) : Prop :=
    (forall i j bi si bj sj, nth_error (big_maps_ P sec) i = Some (bi, si) -> nth_error (big_maps_ P sec) j = Some (bj, sj) ->
        i <> j -> bi + si <= bj \/ bj + sj <= bi) /\
    (forall b s, In (b, s) (big_maps_ P sec) -> 0 <= b /\ 0 < s /\ b + s <= 2^47).

  (* [comment removed for export] *)
  Definition kAuCap : Z := 3750000000.
  (* [comment removed for export] *)
  Definition class_slack (c : Z) : Z := if Z.eqb c kQuarantineBatchClass then kQuarantineMaxSize + kQuarantineCacheSize else 0.
  Lemma class_slack_range : forall c, 0 <= class_slack c <= kQuarantineMaxSize + kQuarantineCacheSize.
  Proof. intros c. unfold class_slack, kQuarantineMaxSize, kQuarantineCacheSize. destruct (Z.eqb c kQuarantineBatchClass); lia. Qed.
  (* [comment removed for export] *)
  Definition wf_region (c : Z) (R : region) (na : Z) : Prop :=   (* [comment removed for export] *)
    (0 <= rg_allocated_user R <= rg_mapped_user R /\ rg_mapped_user R < rg_allocated_user R + 9 * class_size c + kUserMapSize) /\ rg_mapped_user R <= kFreeArrayOffset /\
    rg_mapped_user R mod kUserMapSize = 0 /\ rg_allocated_user R mod class_size c = 0 /\
    0 <= rg_mapped_fa R <= kFreeArraySize /\ rg_mapped_fa R mod kFreeArrayMapSize = 0 /\
    4 * Z.of_nat (length (rg_free R)) <= rg_mapped_fa R /\
    NoDup (rg_free R) /\ (forall k, In k (rg_free R) -> 0 <= k < rg_allocated_user R / class_size c) /\
    (rg_mapped_user R = 0 -> rg_mapped_fa R = 0 /\ rg_free R = []) /\
    (* [comment removed for export] *)
    rg_allocated_user R <= class_size c * (na + 17) + kUserMapSize + class_slack c /\
    rg_mapped_fa R <= 4 * (rg_allocated_user R / class_size c) + kFreeArrayMapSize.
  Definition wf_regions_ (reg : Z -> region) (paid : Z -> list Z) (ci : bool) : Prop :=
    (forall c, 1 <= c <= 30 -> wf_region c (reg c) (Z.of_nat (length (paid c)))) /\
    (forall c, ~ (1 <= c <= 30) -> reg c = region_zero) /\
    ((exists c, 1 <= c <= 30 /\ rg_mapped_user (reg c) <> 0) -> ci = true).

  Definition wf_caches_ (reg : Z -> region) (cache : Z -> pcache) (ci : bool) : Prop :=
    (forall c, 1 <= c <= 31 -> let ks := pk_chunks (cache c) in
        Z.of_nat (length ks) <= max_count c /\ NoDup ks /\
        (forall k, In k ks -> 0 <= k < carved_count_ reg c) /\ (ci = false -> ks = [])) /\
    pk_chunks (cache 31) = [] /\ pk_chunks (cache 0) = [].

  (* [comment removed for export] *)
  Definition p_free_ (reg : Z -> region) (c k : Z) : Prop := In k (rg_free (reg c)).
  Definition p_cached_ (cache : Z -> pcache) (c k : Z) : Prop := In k (pk_chunks (cache c)).
  Definition p_live_ (lm : gmap Z liveinfo) (c k : Z) : Prop := exists u n, lm !! u = Some (LI (ChP (CP c k)) n).
  Definition p_quar_ (qt qg : list batch) (c k : Z) : Prop := exists n, In (QE (ChP (CP c k)) n) (q_entries (qt ++ qg)).
  Definition p_batch_ (qt qg : list batch) (c k : Z) : Prop := c = kQuarantineBatchClass /\ In k (batch_indices_ qt qg).
  Definition wf_partition_ (reg : Z -> region) (cache : Z -> pcache) (lm : gmap Z liveinfo) (qt qg : list batch) : Prop :=
    forall c k, 1 <= c <= 30 -> 0 <= k < carved_count_ reg c ->
      let F := p_free_ reg c k in let C := p_cached_ cache c k in let V := p_live_ lm c k in
      let Q := p_quar_ qt qg c k in let B := p_batch_ qt qg c k in
      (F \/ C \/ V \/ Q \/ B) /\
      ~ (F /\ C) /\ ~ (F /\ V) /\ ~ (F /\ Q) /\ ~ (F /\ B) /\ ~ (C /\ V) /\ ~ (C /\ Q) /\ ~ (C /\ B) /\
      ~ (V /\ Q) /\ ~ (V /\ B) /\ ~ (Q /\ B).

  (* [comment removed for export] *)
  Definition wf_live_ (sb : Z) (reg : Z -> region) (lm : gmap Z liveinfo) (sec : secreg) : Prop :=
    (forall u li, lm !! u = Some li ->
       let n := li_n li in 1 <= n < REQ_MAX /\ u = user_of sb (li_chunk li) n /\
       match li_chunk li with
       | ChP (CP c k) => n <= kMaxPrimaryUser /\ c = class_of n /\ 0 <= k < carved_count_ reg c
       | ChS (CS mb n0) => kMaxPrimaryUser < n /\ n0 = n /\ In (CS mb n) (sr_chunks sec)
       end) /\
    (* [comment removed for export] *)
    (forall u u' li li', lm !! u = Some li -> lm !! u' = Some li' -> u <> u' -> li_chunk li <> li_chunk li') /\
    as_livebytes_ lm <= LIVE_MAX.

  (* [comment removed for export] *)
  Definition wf_qentry_ (reg : Z -> region) (sec : secreg) (e : qentry) : Prop :=
    0 <= qe_n e < REQ_MAX /\
    match qe_chunk e with
    | ChP (CP c k) => qe_n e <= kMaxPrimaryUser /\ c = class_of (qe_n e) /\ 0 <= k < carved_count_ reg c
    | ChS (CS mb n0) => kMaxPrimaryUser < qe_n e /\ n0 = qe_n e /\ In (CS mb n0) (sr_chunks sec)
    end.
  Definition wf_batch_ (reg : Z -> region) (sec : secreg) (b : batch) : Prop :=
    1 <= Z.of_nat (length (ba_entries b)) <= kQuarantineBatchCount /\
    0 <= ba_idx b < carved_count_ reg kQuarantineBatchClass /\
    Forall (wf_qentry_ reg sec) (ba_entries b).
  Definition wf_quarantine_ (reg : Z -> region) (lm : gmap Z liveinfo) (qt qg : list batch) (sec : secreg) : Prop :=
    Forall (wf_batch_ reg sec) qt /\ Forall (wf_batch_ reg sec) qg /\
    (* [comment removed for export] *)
    (forall b, In b (removelast qt) -> Z.of_nat (length (ba_entries b)) = kQuarantineBatchCount) /\
    q_bytes qt <= kQuarantineCacheSize /\ q_bytes qg <= kQuarantineMaxSize /\
    NoDup (batch_indices_ qt qg) /\ NoDup (quarantined_chunks_ qt qg) /\
    (forall u li, lm !! u = Some li -> ~ In (li_chunk li) (quarantined_chunks_ qt qg)).

  (* [comment removed for export] *)
  Definition wf_sec_ (lm : gmap Z liveinfo) (qt qg : list batch) (sec : secreg) : Prop :=
    NoDup (map cs_map (sr_chunks sec)) /\ Z.of_nat (length (sr_chunks sec)) <= sr_reserved sec /\
    (sr_reserved sec = 0 \/ sr_reserved sec = kChunksBlockCount) /\
    (forall s, In s (sr_chunks sec) -> kMaxPrimaryUser < cs_n s < REQ_MAX /\ cs_map s mod 4096 = 0 /\
        app_rangeA L (cs_map s) (map_size (cs_n s)) /\ cs_map s + map_size (cs_n s) <= alloc_ceiling) /\   (* [comment removed for export] *)
    (* [comment removed for export] *)
    (forall s, In s (sr_chunks sec) ->
        (exists u, lm !! u = Some (LI (ChS s) (cs_n s))) \/ In (ChS s) (quarantined_chunks_ qt qg)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition wf_depot_ (dk : list (list Z)) (D : list (list Z)) : Prop :=
    Forall (fun k => In k dk) D /\ NoDup D /\ D <> [].

  (* [comment removed for export] *)
  Definition wf_fframe_ (fs : Z) (fhint : Z -> Z) (ff : Z) (f : fframe) : Prop :=
    let k := ff_class f in 0 <= k <= 10 /\ ff = ff_addr_of_ fs fhint k (ff_age f) /\ Z.of_nat (ff_age f) < fslots k.
  Definition wf_fstack_ (fs : Z) (fhint : Z -> Z) (ffs : gmap Z fframe) : Prop :=
    (forall ff f, ffs !! ff = Some f -> wf_fframe_ fs fhint ff f) /\
    (forall k, 0 <= fhint k < 2^64) /\   (* [comment removed for export] *)
    (* [comment removed for export] *)
    (forall ff ff' f f', ffs !! ff = Some f -> ffs !! ff' = Some f' -> ff <> ff' ->
        ff_class f = ff_class f' -> ff_age f <> ff_age f').

  (* [comment removed for export] *)
  Definition tiny_quar_ (qt qg : list batch) : Z := Z.of_nat (length (filter (fun e => Z.ltb (qe_n e) 16) (q_entries (qt ++ qg)))).
  Definition wf_budget_ (tiny : Z) (lm : gmap Z liveinfo) (qt qg : list batch) : Prop :=
    0 <= tiny <= TINYCRED0 /\ 0 <= as_livebytes_ lm /\ as_nlive_ lm <= NLIVE_MAX /\
    0 <= tiny_live_ lm /\ tiny_live_ lm + tiny_quar_ qt qg + tiny <= TINYCRED0.

  (* [comment removed for export] *)
  Fixpoint paid_sum_ (paid : Z -> list Z) (n : nat) : Z :=
    match n with O => 0 | S n' => paid_sum_ paid n' + class_size (Z.of_nat n) * Z.of_nat (length (paid (Z.of_nat n))) end.
  Definition wf_prim_ (lm : gmap Z liveinfo) (qt qg : list batch) (paid : Z -> list Z) (pcred : Z) : Prop :=
    0 <= pcred /\ paid_sum_ paid 30 <= PRIMCRED0 - pcred /\
    (forall c k, 1 <= c <= 30 -> p_live_ lm c k \/ p_quar_ qt qg c k -> In k (paid c)).

  (* [comment removed for export] *)
  Definition kDeadShadowBytes : Z := 8192.    (* [comment removed for export] *)
  Definition wf_dead_ (seccred : Z) (dead : list (Z * Z)) (nsec : Z) : Prop :=
    0 <= seccred <= SECCRED0 /\
    (* [comment removed for export] *)
    Forall (fun lh => ((kHighShadowMapBeg <= fst lh /\ snd lh <= kHighMemBeg) \/ (kLowShadowBeg <= fst lh /\ snd lh <= kShadowGapBeg))
                      /\ fst lh <= snd lh <= fst lh + kDeadShadowBytes /\
                      (* [comment removed for export] *)
                      fst lh mod 8 = 0 /\ snd lh mod 8 = 0) dead /\
    Z.of_nat (length dead) + 2 * nsec <= 2 * (SECCRED0 - seccred) /\
    hull_bytes dead + kDeadShadowBytes * nsec <= kDeadShadowBytes * (SECCRED0 - seccred).

  (* [comment removed for export] *)
  Definition bcredit (b : batch) : Z := batch_bytes b - 16384.
  Definition lcredit (bs : list batch) : Z := fold_right (fun b acc => bcredit b + acc) 0 bs.
  (* [comment removed for export] *)
  Definition wf_qcredit_ (qg : list batch) : Prop :=
       (forall i, -8192 <= lcredit (skipn i qg))
    /\ (q_bytes qg <= kQuarantineMinSize \/ 0 <= lcredit qg).
  Lemma wf_qcredit_nil : wf_qcredit_ [].
  Proof. split; [intros i; rewrite skipn_nil; cbn; lia| left; cbn; unfold kQuarantineMinSize; lia]. Qed.

  Record WF (A : AState) : Prop := {
    wfP : wf_place (a_pl A);
    wfM : wf_bigmaps_ (a_pl A) (a_sec A);
    wfR : wf_regions_ (a_reg A) (a_paid A) (a_cache_inited A);   (* [comment removed for export] *)
    wfC : wf_caches_ (a_reg A) (a_cache A) (a_cache_inited A);
    wfX : wf_partition_ (a_reg A) (a_cache A) (a_livemap A) (a_qthread A) (a_qglobal A);
    wfV : wf_live_ (a_sb A) (a_reg A) (a_livemap A) (a_sec A);
    wfQ : wf_quarantine_ (a_reg A) (a_livemap A) (a_qthread A) (a_qglobal A) (a_sec A);
    wfS : wf_sec_ (a_livemap A) (a_qthread A) (a_qglobal A) (a_sec A);
    wfD : wf_depot_ (p_dkeys (a_pl A)) (a_depot A);
    wfF : wf_fstack_ (a_fs A) (a_fhint A) (a_fframes A);
    wfB : wf_budget_ (a_tiny A) (a_livemap A) (a_qthread A) (a_qglobal A);
    (* [comment removed for export] *)
    wfI : a_qlimbo A = [];                          (* [comment removed for export] *)
    wfE : wf_dead_ (a_scred A) (a_deadsh A) (Z.of_nat (length (sr_chunks (a_sec A))));
    wfJ : wf_qcredit_ (a_qglobal A);               (* [comment removed for export] *)
    (* [comment removed for export] *)
    wfN : wf_prim_ (a_livemap A) (a_qthread A) (a_qglobal A) (a_paid A) (a_pcred A) }.

  (* [comment removed for export] *)
  Record WF_busy (A : AState) : Prop := {
    wbP : wf_place (a_pl A);
    wbM : wf_bigmaps_ (a_pl A) (a_sec A);
    wbR : wf_regions_ (a_reg A) (a_paid A) (a_cache_inited A);
    wbC : wf_caches_ (a_reg A) (a_cache A) (a_cache_inited A);
    wbX : wf_partition_ (a_reg A) (a_cache A) (a_livemap A) (a_qthread A) (a_qglobal A);
    wbV : wf_live_ (a_sb A) (a_reg A) (a_livemap A) (a_sec A);
    wbQ : wf_quarantine_ (a_reg A) (a_livemap A) (a_qthread A) (a_qglobal A) (a_sec A);
    wbS : wf_sec_ (a_livemap A) (a_qthread A) (a_qglobal A) (a_sec A);
    wbD : wf_depot_ (p_dkeys (a_pl A)) (a_depot A);
    wbF : wf_fstack_ (a_fs A) (a_fhint A) (a_fframes A);
    wbB : wf_budget_ (a_tiny A) (a_livemap A) (a_qthread A) (a_qglobal A);
    wbE : wf_dead_ (a_scred A) (a_deadsh A) (Z.of_nat (length (sr_chunks (a_sec A))));
    wbJ : wf_qcredit_ (a_qglobal A);
    wbN : wf_prim_ (a_livemap A) (a_qthread A) (a_qglobal A) (a_paid A) (a_pcred A) }.
  Lemma WF_split : forall A, WF A <-> WF_busy A /\ a_qlimbo A = [].
  Proof.
    intros A. split.
    - intros W. split; [| exact (wfI A W)]. destruct W; constructor; assumption.
    - intros [W I]. destruct W; constructor; assumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition rt_statics (a : Z) : Prop :=
       (al_instance L <= a < al_instance L + 3632)
    \/ (al_malloc_context_size L <= a < al_malloc_context_size L + 4)
    \/ (al_can_poison_memory L <= a < al_can_poison_memory L + 1) \/ (al_page_size_cache L <= a < al_page_size_cache L + 8)
    \/ (al_may_return_null L <= a < al_may_return_null L + 1) \/ (al_rss_limit_exceeded L <= a < al_rss_limit_exceeded L + 1)
    \/ (al_dying_flag L <= a < al_dying_flag L + 4) \/ (al_malloc_hooks L <= a < al_malloc_hooks L + 80)
    \/ (al_internal_alloc_inited L <= a < al_internal_alloc_inited L + 2)
    \/ (al_internal_allocator_inst L <= a < al_internal_allocator_inst L + 0x81030).

  (* [comment removed for export] *)
  Definition consts_repr_ (P : aplace) (m : mem) : Prop :=
    let I := al_instance L in let sb := p_sb P in let t := p_thr P in let tp := bv_unsigned (cl_tp cl) in
    Forall (fun c => bytes_at segs m (fst c) (snd c)) (cl_consts cl) /\
    u64_at m (I + off_primary_reserved_base) (p_b6 P) /\ u64_at m (I + off_primary_reserved_size) kSpaceReserve /\
    u64_at m (I + off_SpaceBeg) sb /\ u32_at m (I + off_release_interval) 0xffffffff /\
    u64_at m (I + off_RegionInfo_ptr) (p_ri P) /\ u8_at m (I + off_PremappedHeap) 0 /\
    u64_at m (I + off_sec_page_size) 4096 /\ u64_at m (I + off_sec_chunks) (p_pa P) /\
    u64_at m (I + off_sec_ptr_array_base) (p_pa P) /\ u64_at m (I + off_sec_ptr_array_size) kPtrArrayReserve /\
    u64_at m (I + off_q_max_size) kQuarantineMaxSize /\ u64_at m (I + off_q_min_size) kQuarantineMinSize /\
    u64_at m (I + off_q_max_cache_size) kQuarantineCacheSize /\
    u64_at m (I + off_max_user_malloc) kMaxUserDefinedMallocSize /\
    u16_at m (I + off_min_redzone) kMinRedzone /\ u16_at m (I + off_max_redzone) kMaxRedzone /\ u8_at m (I + off_alloc_dealloc_mismatch) 1 /\
    u64_at m (al_kHighMemEnd_var L) kHighMemEnd /\ u64_at m (al_kMidMemBeg_var L) 0 /\ u64_at m (al_kMidMemEnd_var L) 0 /\
    (forall i, 0 <= i < 24 -> cl_shared cl (al_kHighMemEnd_var L + i)) /\ al_kMidMemBeg_var L = al_kHighMemEnd_var L + 8 /\ al_kMidMemEnd_var L = al_kHighMemEnd_var L + 16 /\
    u32_at m (al_malloc_context_size L) kMallocContextSize /\ u8_at m (al_can_poison_memory L) 1 /\
    u64_at m (al_page_size_cache L) 4096 /\ u8_at m (al_may_return_null L) 1 /\ u8_at m (al_rss_limit_exceeded L) 0 /\
    u32_at m (al_dying_flag L) 0 /\ fill_at m (al_malloc_hooks L) 80 0 /\
    (* [comment removed for export] *)
    u64_at m (t + off_th_context) (p_ctx P) /\ u64_at m (t + off_th_stack_top) (p_stk_top P) /\
    u64_at m (t + off_th_stack_bottom) (p_stk_bot P) /\ u8_at m (t + off_th_stack_switching) 0 /\
    u8_at m (t + off_th_unwinding) 0 /\ u32_at m (p_ctx P + 8) kMainTid /\ u64_at m (p_ctx P + 152) t /\
    (exists tsd, u64_at m (tp - 88) tsd /\ (forall i, 0 <= i < 8 -> cl_shared cl (tsd + i)) /\ u64_at m tsd (p_ctx P)) /\
    u64_at m tp (p_fs P) /\
    (* [comment removed for export] *)
    u64_at m (tp + 8) (p_dtls P) /\ u64_at m (p_dtls P + 24) tp /\
    u64_at m (t + 48) (p_tlsb P) /\ u64_at m (t + 56) (p_tlse P).

  (* [comment removed for export] *)
  Definition lockb (held : list Z) (x : Z) : Z := if in_dec Z.eq_dec x held then 1 else 0.
  Definition locks_repr_ (P : aplace) (held : list Z) (m : mem) : Prop :=
    let I := al_instance L in
    (forall c, 0 <= c < 32 -> u64_at m (p_ri P + kRegionInfoSize * c + 0) 0 /\ u64_at m (p_ri P + kRegionInfoSize * c + 8) 0) /\
    u8_at m (I + off_sec_mutex) (lockb held (I + off_sec_mutex)) /\ u8_at m (I + off_q_cache_mutex) (lockb held (I + off_q_cache_mutex)) /\
    u8_at m (I + off_q_recycle_mutex) (lockb held (I + off_q_recycle_mutex)) /\
    u8_at m (I + off_fallback_mutex) (lockb held (I + off_fallback_mutex)) /\
    u8_at m (al_internal_alloc_inited L + 1) (lockb held (al_internal_alloc_inited L + 1)).
  Lemma lockb_nil : forall x, lockb [] x = 0.
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition region_repr_ (sb : Z) (R : region) (m : mem) (c : Z) : Prop :=
    let ri := region_info_addr sb c in let fa := free_array_beg sb c in
    u64_at m (ri + off_ri_num_freed) (Z.of_nat (length (rg_free R))) /\
    u64_at m (ri + off_ri_mapped_free_array) (rg_mapped_fa R) /\
    u64_at m (ri + off_ri_allocated_user) (rg_allocated_user R) /\ u64_at m (ri + off_ri_allocated_meta) 0 /\
    u64_at m (ri + off_ri_mapped_user) (rg_mapped_user R) /\ u64_at m (ri + off_ri_mapped_meta) 0 /\
    u8_at m (ri + off_ri_exhausted) 0 /\
    junk_at m (ri + 64) 4 /\ junk_at m (ri + off_ri_n_allocated) 16 /\ junk_at m (ri + off_ri_rtoi) 40 /\
    (forall i k, nth_error (rg_free R) i = Some k -> u32_at m (fa + 4 * Z.of_nat i) (k * class_size c / kCompactPtrScale)) /\
    (* [comment removed for export] *)
    mapped m fa (rg_mapped_fa R) /\ mapped m (region_beg sb c) (rg_mapped_user R).

  (* [comment removed for export] *)
  Definition cache_repr_ (P : aplace) (cache : Z -> pcache) (ci : bool) (m : mem) : Prop :=
    let t := p_thr P in
    (forall c, 0 <= c < 32 ->
       let e := t + off_th_per_class c in let ks := pk_chunks (cache c) in
       Z.of_nat (length ks) <= 16 /\
       u32_at m (e + off_pc_count) (Z.of_nat (length ks)) /\
       (if ci && negb (c =? 0) then u32_at m (e + off_pc_max_count) (max_count c) /\ u64_at m (e + off_pc_class_size) (class_size c)
        else u32_at m (e + off_pc_max_count) 0 /\ u64_at m (e + off_pc_class_size) 0) /\
       (forall i k, nth_error ks i = Some k -> u32_at m (e + off_pc_chunk (Z.of_nat i)) (k * class_size c / kCompactPtrScale)) /\
       junk_at m (e + off_pc_chunk (Z.of_nat (length ks))) (4 * (16 - Z.of_nat (length ks)))) /\
    junk_at m (t + off_th_cache_stats) 32 /\ junk_at m (t + off_th_stats) (112 + 8 * 32) /\
    (* [comment removed for export] *)
    mapped m t 4096 /\ mapped m (p_ctx P) 0x10000.

  (* [comment removed for export] *)
  Definition hdr_repr_ (sb : Z) (m : mem) (ch : chunk) (n st : Z) : Prop :=
    let u := user_of sb ch n in let ab := alloc_beg sb ch in
    (* [comment removed for export] *)
    (exists id b1, 0 <= id < 2^32 /\ 0 <= b1 < 256 /\ Z.land b1 0x7f = kHdrByte1Malloc /\
                  rw_cells segs m (u - 16) (chunk_hdr_cells (CH st b1 (user_size n) id))) /\
    (ab <> u - 16 -> u64_at m ab kAllocBegMagic /\ u64_at m (ab + 8) (u - 16)).
  Definition live_repr_ (sb : Z) (lm : gmap Z liveinfo) (m : mem) : Prop :=
    forall u li, lm !! u = Some li ->
      hdr_repr_ sb m (li_chunk li) (li_n li) CHUNK_ALLOCATED /\
      mapped m u (li_n li) /\ mapped m (chunk_lo sb (li_chunk li)) (chunk_hi sb (li_chunk li) - chunk_lo sb (li_chunk li)).
  (* [comment removed for export] *)
  Definition quar_repr_ (sb : Z) (qt qg : list batch) (m : mem) : Prop :=
    forall e, In e (q_entries (qt ++ qg)) ->
      hdr_repr_ sb m (qe_chunk e) (qe_n e) CHUNK_QUARANTINE /\
      junk_at m (user_of sb (qe_chunk e) (qe_n e)) 8 /\
      mapped m (chunk_lo sb (qe_chunk e)) (chunk_hi sb (qe_chunk e) - chunk_lo sb (qe_chunk e)).

  (* [comment removed for export] *)
  Fixpoint batches_repr (m : mem) (sb : Z) (bs : list batch) : Prop :=
    match bs with
    | [] => True
    | b :: bs' =>
        let a := batch_addr sb b in
        u64_at m (a + off_qb_next) (match bs' with [] => 0 | b' :: _ => batch_addr sb b' end) /\
        u64_at m (a + off_qb_size) (batch_bytes b) /\
        u64_at m (a + off_qb_count) (Z.of_nat (length (ba_entries b))) /\
        (forall i e, nth_error (ba_entries b) i = Some e -> u64_at m (a + off_qb_batch (Z.of_nat i)) (hdr_of sb (qe_chunk e) (qe_n e))) /\
        mapped m a kQuarantineBatchBytes /\
        batches_repr m sb bs'
    end.
  Definition qcache_repr (m : mem) (sb : Z) (qc : Z) (bs : list batch) : Prop :=
    u64_at m (qc + 0) (Z.of_nat (length bs)) /\
    u64_at m (qc + 8) (match bs with [] => 0 | b :: _ => batch_addr sb b end) /\
    u64_at m (qc + 16) (match bs with [] => 0 | _ => batch_addr sb (last bs (BA 0 [])) end) /\
    u64_at m (qc + 24) (q_bytes bs) /\
    batches_repr m sb bs.
  Definition quarantine_repr_ (P : aplace) (qt qg : list batch) (m : mem) : Prop :=
    qcache_repr m (p_sb P) (p_thr P + off_th_qcache) qt /\
    qcache_repr m (p_sb P) (al_instance L + off_q_cache_list_size) qg /\
    quar_repr_ (p_sb P) qt qg m.

  (* [comment removed for export] *)
  Definition sec_repr_ (P : aplace) (sec : secreg) (m : mem) : Prop :=
    let I := al_instance L in
    u64_at m (I + off_sec_n_reserved) (sr_reserved sec) /\ u64_at m (I + off_sec_n_chunks) (Z.of_nat (length (sr_chunks sec))) /\
    junk_at m (I + off_sec_chunks_sorted) 1 /\ junk_at m (I + off_sec_stat_n_allocs) (680 - off_sec_stat_n_allocs) /\
    junk_at m (I + off_global_stats) 32 /\
    (forall i s, nth_error (sr_chunks sec) i = Some s ->
        u64_at m (p_pa P + 8 * Z.of_nat i) (cs_map s) /\
        rw_cells segs m (cs_map s) (sec_hdr_cells (SH (cs_map s) (map_size (cs_n s)) (needed_size2 (cs_n s)) (Z.of_nat i)))) /\
    mapped m (p_pa P) (8 * sr_reserved sec).

  (* [comment removed for export] *)
  Definition depot_repr_ (P : aplace) (D : list (list Z)) (m : mem) : Prop := depot_rep L segs D (p_nodes0 P) (p_frames0 P) m.

  (* [comment removed for export] *)
  Definition ia_repr_ (ia : bool) (m : mem) : Prop :=
    let B := al_internal_allocator_inst L in
    (forall i, 0 <= i < kDepotNodesL1 -> u64_at m (B + 8 + 8 * i) 0) /\
    if ia then u8_at m (al_internal_alloc_inited L) 1 /\ u64_at m (B + 0x40dc0) 4096 /\ u64_at m (B + 0x40dc8) (B + 0x40dd0)
    else u8_at m (al_internal_alloc_inited L) 0 /\ fill_at m B 0x81030 0.

  (* [comment removed for export] *)
  Definition fs_base_ (P : aplace) (fhint : Z -> Z) (m : mem) : Prop :=
    let fs := p_fs P in
    (forall k, 0 <= k <= 10 -> u64_at m (fs + 8 * k) (fhint k mod 2^64)) /\
    u64_at m (fs + 88) kFakeStackSizeLog /\ u8_at m (fs + 96) 0 /\
    mapped m fs kFakeStackBytes /\
    (* [comment removed for export] *)
    mapped m (sh fs) (kFakeStackBytes / 8).
  Definition fs_ptrs_ (fs : Z) (fhint : Z -> Z) (ffs : gmap Z fframe) (m : mem) : Prop :=
    forall ff f, ffs !! ff = Some f ->
      u64_at m (saved_flag_ptr ff (ff_class f)) (fflag_addr fs (ff_class f) (ff_pos (fhint (ff_class f)) (ff_class f) (ff_age f))).
  (* [comment removed for export] *)
  Definition slot_live_ (fhint : Z -> Z) (ffs : gmap Z fframe) (k pos : Z) : Prop :=
    exists ff f, ffs !! ff = Some f /\ ff_class f = k /\ ff_pos (fhint k) k (ff_age f) = pos.
  Definition fs_flags_ (fs : Z) (fhint : Z -> Z) (ffs : gmap Z fframe) (m : mem) : Prop :=
    forall k pos, 0 <= k <= 10 -> 0 <= pos < fslots k ->
      exists b, u8_at m (fflag_addr fs k pos) b /\
        ((b = 1 /\ slot_live_ fhint ffs k pos) \/ (b = 0 /\ ~ slot_live_ fhint ffs k pos)).

  (* [comment removed for export] *)
  Definition maps_repr_ (P : aplace) (m : mem) : Prop :=
    mapped m (p_sp0 P - 0x800000) 0x800000 /\ mapped m (p_ri P) 4096 /\
    mapped m (fst stack_shadow_iv) (snd stack_shadow_iv) /\
    mapped m (fst (shadow_region (al_image_lo L) (al_image_hi L - al_image_lo L))) (snd (shadow_region (al_image_lo L) (al_image_hi L - al_image_lo L))).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition hidden_repr (P : aplace) (reg : Z -> region) (sec : secreg) (m : mem) : Prop :=
       (* [comment removed for export] *)
       (forall z, ghost_hs_ P z -> m (wz z) <> None /\ (~ heap_shadow_ (p_sb P) reg sec z -> m (wz z) = Some (b8 0)))
    /\ (* [comment removed for export] *)
       (forall z, kLowShadowMapBeg <= z < kLowShadowMapBeg + 0x10000000 -> ~ in_vis_shadow (VIS0 P) z -> m (wz z) <> None).

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition fa8 (n : Z) : list byte := repeat (b8 kAsanHeapLeftRedzoneMagic) (Z.to_nat n).
  Definition fd8 (n : Z) : list byte := repeat (b8 kAsanHeapFreeMagic) (Z.to_nat n).
  (* [comment removed for export] *)
  Definition pshadow_free (c : Z) : list byte := fa8 (class_size c / 8).
  Definition pshadow_live (c n : Z) : list byte :=
    fa8 (rz_size n / 8) ++ shpat (user_size n) ++ fa8 (class_size c / 8 - rz_size n / 8 - (user_size n + 7) / 8).
  Definition pshadow_quar (c n : Z) : list byte :=
    fa8 (rz_size n / 8) ++ fd8 ((user_size n + 7) / 8) ++ fa8 (class_size c / 8 - rz_size n / 8 - (user_size n + 7) / 8).
  (* [comment removed for export] *)
  Definition sshadow_live (n : Z) : list byte :=
    fa8 768 ++ shpat (user_size n) ++ fa8 (map_size n / 8 - 768 - (user_size n + 7) / 8).
  Definition sshadow_quar (n : Z) : list byte :=
    fa8 768 ++ fd8 ((user_size n + 7) / 8) ++ fa8 (map_size n / 8 - 768 - (user_size n + 7) / 8).

  Definition shadow_repr_ (sb : Z) (reg : Z -> region) (cache : Z -> pcache) (lm : gmap Z liveinfo) (qt qg : list batch) (m : mem) : Prop :=
    (* [comment removed for export] *)
    (forall c k, 1 <= c <= 30 -> (p_free_ reg c k \/ p_cached_ cache c k \/ p_batch_ qt qg c k) ->
        bytes_at segs m (sh (chunk_addr sb c k)) (pshadow_free c)) /\
    (forall u c k n, lm !! u = Some (LI (ChP (CP c k)) n) -> bytes_at segs m (sh (chunk_addr sb c k)) (pshadow_live c n)) /\
    (forall c k n, In (QE (ChP (CP c k)) n) (q_entries (qt ++ qg)) -> bytes_at segs m (sh (chunk_addr sb c k)) (pshadow_quar c n)) /\
    (forall c, 1 <= c <= 30 -> let R := reg c in let rb := region_beg sb c in
        fill_at m (sh (rb + rg_allocated_user R)) ((rg_mapped_user R - rg_allocated_user R) / 8) kAsanHeapLeftRedzoneMagic /\
        fill_at m (sh (rb + kFreeArrayOffset)) (rg_mapped_fa R / 8) kAsanHeapLeftRedzoneMagic) /\
    (* [comment removed for export] *)
    (forall u mb n, lm !! u = Some (LI (ChS (CS mb n)) n) -> bytes_at segs m (sh mb) (sshadow_live n)) /\
    (forall mb n0 n, In (QE (ChS (CS mb n0)) n) (q_entries (qt ++ qg)) -> bytes_at segs m (sh mb) (sshadow_quar n)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Record arepr (held : list Z) (A : AState) (m : mem) : Prop := {
    ar_consts : consts_repr_ (a_pl A) m;
    ar_locks : locks_repr_ (a_pl A) held m;
    ar_regions : forall c, 1 <= c <= 30 -> region_repr_ (a_sb A) (a_reg A c) m c;
    ar_cache : cache_repr_ (a_pl A) (a_cache A) (a_cache_inited A) m;
    ar_live : live_repr_ (a_sb A) (a_livemap A) m;
    ar_quar : quarantine_repr_ (a_pl A) (a_qthread A) (a_qglobal A) m;
    ar_sec : sec_repr_ (a_pl A) (a_sec A) m;
    ar_depot : depot_repr_ (a_pl A) (a_depot A) m;
    ar_ia : ia_repr_ (a_ia_inited A) m;
    ar_fsbase : fs_base_ (a_pl A) (a_fhint A) m;
    ar_fsptrs : fs_ptrs_ (a_fs A) (a_fhint A) (a_fframes A) m;
    ar_fsflags : fs_flags_ (a_fs A) (a_fhint A) (a_fframes A) m;
    ar_maps : maps_repr_ (a_pl A) m;
    ar_shadow : shadow_repr_ (a_sb A) (a_reg A) (a_cache A) (a_livemap A) (a_qthread A) (a_qglobal A) m }.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition alzfree_ (P : aplace) (reg : Z -> region) (md : Model) : Prop :=
    let lz := m_vm_lazy md in let sb := p_sb P in
    lazy_free lz (al_image_lo L) (al_image_hi L) /\
    lazy_free lz (p_sp0 P - 0x800000) (p_sp0 P + p_stk_span P) /\
    (forall c, 1 <= c <= 31 ->
        lazy_free lz (region_beg sb c) (region_beg sb c + rg_mapped_user (reg c)) /\
        lazy_free lz (region_beg sb c + kFreeArrayOffset) (region_beg sb c + kFreeArrayOffset + rg_mapped_fa (reg c))).
  Lemma alzfree_lazy_eq : forall P reg md md', m_vm_lazy md' = m_vm_lazy md -> alzfree_ P reg md -> alzfree_ P reg md'.
  Proof. intros P reg md md' E Z9. unfold alzfree_ in *. rewrite E. exact Z9. Qed.
  (* [comment removed for export] *)
  Lemma sbm_lazy : forall md md', same_but_materialized md md' -> m_vm_lazy md' = m_vm_lazy md.
  Proof. intros md md' SB. rewrite SB. apply m_vm_lazy_wvb. Qed.
  Lemma lazy_free_sbm : forall md md' lo hi, same_but_materialized md md' -> lazy_free (m_vm_lazy md) lo hi -> lazy_free (m_vm_lazy md') lo hi.
  Proof. intros md md' lo hi SB Z0. rewrite (sbm_lazy md md' SB). exact Z0. Qed.

  (* [comment removed for export] *)
  Lemma lazy_free_join : forall lz a b c, lazy_free lz a b -> lazy_free lz b c -> lazy_free lz a c.
  Proof. intros lz a b c H1 H2 x Hx. destruct (Z_lt_le_dec x b); [apply H1| apply H2]; lia. Qed.
  (* [comment removed for export] *)
  Lemma alzfree_upd : forall P reg reg' md c0,
    alzfree_ P reg md ->
    (forall c, 1 <= c <= 31 -> c <> c0 -> rg_mapped_user (reg' c) = rg_mapped_user (reg c) /\ rg_mapped_fa (reg' c) = rg_mapped_fa (reg c)) ->
    lazy_free (m_vm_lazy md) (region_beg (p_sb P) c0) (region_beg (p_sb P) c0 + rg_mapped_user (reg' c0)) ->
    lazy_free (m_vm_lazy md) (region_beg (p_sb P) c0 + kFreeArrayOffset) (region_beg (p_sb P) c0 + kFreeArrayOffset + rg_mapped_fa (reg' c0)) ->
    alzfree_ P reg' md.
  Proof.
    intros P reg reg' md c0 (Z1 & Z2 & Z3) E NU NF. refine (conj Z1 (conj Z2 _)). intros c Hc.
    destruct (Z.eq_dec c c0) as [->|NE]; [exact (conj NU NF)|].
    destruct (E c Hc NE) as [E1 E2]. rewrite E1, E2. exact (Z3 c Hc).
  Qed.
  Definition aledger_ (P : aplace) (reg : Z -> region) (sec : secreg) (md : Model) : Prop :=   (* [comment removed for export] *)
    let h := m_vmmaps md in
    (forall b s, In (b, s) (big_maps_ P sec) -> In (wz b, wz s) (vm_maps h)) /\
    region_free (vm_reserved h) (wz (p_b6 P)) (wz kSpaceReserve) = true /\
    region_free (vm_reserved h) (wz (p_pa P)) (wz kPtrArrayReserve) = true /\
    region_free (vm_reserved h) (wz kHighShadowMapBeg) (wz kHighShadowMapSize) = true /\
    vm_limit h = p_tlim P /\     (* [comment removed for export] *)
    Forall (fun sc => eager_map (wz (cs_map sc)) (wz (map_size (cs_n sc))) md) (sr_chunks sec) /\
    (* [comment removed for export] *)
    cuts_covered md /\
    (* [comment removed for export] *)
    (region_free (vm_noaccess h) (wz kLowShadowMapBeg) (wz (kShadowGapBeg - kLowShadowMapBeg)) = true /\
     region_free (vm_noaccess h) (wz kHighShadowMapBeg) (wz kHighShadowMapSize) = true) /\
    (* [comment removed for export] *)
    alzfree_ P reg md.
  Definition aledger (A : AState) : Model -> Prop := aledger_ (a_pl A) (a_reg A) (a_sec A).
  (* [comment removed for export] *)
  Lemma aledger_vm : forall P reg sec md md', m_vm md' = m_vm md -> aledger_ P reg sec md -> aledger_ P reg sec md'.
  Proof.
    (intros P reg sec md md' E; (first [ intro dR_1; dand9 dR_1 as L1 L2 L3 L4 L5 L6 L7 L8 L9 | intros (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9) ])). unfold aledger_. cbv zeta. unfold m_vmmaps in *. rewrite E.
    repeat (split; [assumption|]). split; [| split; [exact (cuts_covered_m_vm md md' E L7)| split; [exact L8| apply (alzfree_lazy_eq P reg md md'); [unfold m_vm_lazy; rewrite E; reflexivity| exact L9]]]].
    apply Forall_forall. intros sc Hsc. apply (eager_map_m_vm _ _ md md' E). exact (proj1 (Forall_forall _ _) L6 sc Hsc).
  Qed.
  Lemma aledger_sbm : forall P reg sec md md', same_but_materialized md md' -> aledger_ P reg sec md -> aledger_ P reg sec md'.
  Proof.
    (intros P reg sec md md' SB; (first [ intro dR_2; dand9 dR_2 as L1 L2 L3 L4 L5 L6 L7 L8 L9 | intros (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9) ])). unfold aledger_. cbv zeta. rewrite (same_but_materialized_vmmaps _ _ SB).
    repeat (split; [assumption|]). split; [| split; [exact (cuts_covered_sbm md md' SB L7)| split; [exact L8| apply (alzfree_lazy_eq P reg md md'); [rewrite SB; apply m_vm_lazy_wvb| exact L9]]]].
    apply Forall_forall. intros sc Hsc. apply (eager_map_sbm _ _ md md' SB). exact (proj1 (Forall_forall _ _) L6 sc Hsc).
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma aledger_upd : forall P reg reg' sec md, aledger_ P reg sec md -> alzfree_ P reg' md -> aledger_ P reg' sec md.
  Proof.
    intros P reg reg' sec md (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & _) Z9.
    exact (conj L1 (conj L2 (conj L3 (conj L4 (conj L5 (conj L6 (conj L7 (conj L8 Z9)))))))).
  Qed.
  Lemma aledger_lzfree : forall P reg sec md, aledger_ P reg sec md -> alzfree_ P reg md.
  Proof. intros P reg sec md LED. do 8 (apply proj2 in LED). exact LED. Qed.
  (* [comment removed for export] *)
  Lemma aledger_reg : forall P reg reg' sec md,
    (forall c, 1 <= c <= 31 -> rg_mapped_user (reg' c) = rg_mapped_user (reg c) /\ rg_mapped_fa (reg' c) = rg_mapped_fa (reg c)) ->
    aledger_ P reg sec md -> aledger_ P reg' sec md.
  Proof.
    intros P reg reg' sec md E (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & (Z1 & Z2 & Z3)).
    refine (conj L1 (conj L2 (conj L3 (conj L4 (conj L5 (conj L6 (conj L7 (conj L8 (conj Z1 (conj Z2 _)))))))))).
    intros c Hc. destruct (E c Hc) as [E1 E2]. rewrite E1, E2. exact (Z3 c Hc).
  Qed.

  (* [comment removed for export] *)
  Definition acover_ (P : aplace) (sec : secreg) (h : VmMaps) : Prop :=
       (exists fog : list (Z * Z),
           Z.of_nat (length fog) <= 2 /\ Forall (fun bs => 0 <= fst bs /\ 0 < snd bs <= 8192 /\ fst bs + snd bs <= 2^47) fog /\
           (forall e, In e (vm_maps h) ->
              let bs := (bv_unsigned (fst e), bv_unsigned (snd e)) in
              In bs (big_maps_ P sec) \/ In bs fog \/ bs = (kShadowGapBeg, kHighShadowMapBeg - kShadowGapBeg)) /\
           (* [comment removed for export] *)
           (forall bs, In bs fog -> In (wz (fst bs), wz (snd bs)) (vm_maps h)) /\
           (* [comment removed for export] *)
           (forall lo hi a, In (lo, hi) (p_extra P) -> lo <= a < hi -> 0 <= a < alloc_ceiling ->
               ~ (kLowShadowMapBeg <= a < kHighMemBeg) ->
               (cl_image_lo cl <= a < cl_image_hi cl) \/ in_regions (big_maps_ P (SR [] 0)) a \/ in_regions fog a))
    /\ (* [comment removed for export] *)
       In (wz kShadowGapBeg, wz (kHighShadowMapBeg - kShadowGapBeg)) (vm_maps h)
    /\ (* [comment removed for export] *)
       vm_reserved h = segments_reserved (cl_segs cl).
    (* [comment removed for export] *)
  Lemma acover_vmmaps : forall P sec h h', vm_maps h' = vm_maps h -> vm_reserved h' = vm_reserved h ->
    acover_ P sec h -> acover_ P sec h'.
  Proof. intros P sec h h' E1 E2 C. unfold acover_ in *. rewrite E1, E2. exact C. Qed.

  (* [comment removed for export] *)
  Record ainv_ (A : AState) (m : mem) (md : Model) : Prop := {
    ai_wf : WF A;
    ai_repr : arepr [] A (aview_of (ahull_of image_ivs L A) m);
    ai_hidden : hidden_repr (a_pl A) (a_reg A) (a_sec A) m;
    ai_extra : wf_extra (a_pl A);
    ai_ledger : aledger_ (a_pl A) (a_reg A) (a_sec A) md;           (* [comment removed for export] *)
    ai_minv : MInv (ahull_of image_ivs L A) (alhull_of L A) (aeager_of A) md;   (* [comment removed for export] *)
    ai_halted : m_halted md = None;
    ai_cover : acover_ (a_pl A) (a_sec A) (m_vmmaps md);       (* [comment removed for export] *)
    ai_ceil : alloc_top (m_vmmaps md) = alloc_ceiling }.       (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition hdr_foot (sb : Z) (ch : chunk) (n : Z) (a : Z) : Prop :=
    let u := user_of sb ch n in let ab := alloc_beg sb ch in
    (u - 16 <= a < u) \/ (ab <> u - 16 /\ ab <= a < ab + 16).

  Definition afoot_ (P : aplace) (reg : Z -> region) (lm : gmap Z liveinfo) (qt qg : list batch) (sec : secreg)
                    (ffs : gmap Z fframe) (a : Z) : Prop :=
    let sb := p_sb P in let tp := bv_unsigned (cl_tp cl) in
       rt_statics a
    \/ cl_shared cl a
    \/ (exists c, In c (cl_consts cl) /\ fst c <= a < fst c + Z.of_nat (length (snd c)))
    \/ (tp - 88 <= a < tp - 80) \/ (tp <= a < tp + 8)
    \/ (p_thr P <= a < p_thr P + 4096) \/ (p_ctx P <= a < p_ctx P + 0x10000) \/ (p_ri P <= a < p_ri P + 4096)
    \/ (exists c, 1 <= c <= 30 /\ free_array_beg sb c <= a < free_array_beg sb c + rg_mapped_fa (reg c))
    \/ (exists u li, lm !! u = Some li /\ hdr_foot sb (li_chunk li) (li_n li) a)
    \/ (exists e, In e (q_entries (qt ++ qg)) /\
          (hdr_foot sb (qe_chunk e) (qe_n e) a \/ user_of sb (qe_chunk e) (qe_n e) <= a < user_of sb (qe_chunk e) (qe_n e) + 8))
    \/ (exists b, In b (qt ++ qg) /\ batch_addr sb b <= a < batch_addr sb b + kQuarantineBatchBytes)
    \/ (p_pa P <= a < p_pa P + 8 * kChunksBlockCount)
    \/ (exists s, In s (sr_chunks sec) /\ cs_map s <= a < cs_map s + kSecondaryHeaderSize)
    \/ (p_fs P <= a < p_fs P + kFakeFlagsOffset)
    \/ (exists ff f, ffs !! ff = Some f /\ saved_flag_ptr ff (ff_class f) <= a < saved_flag_ptr ff (ff_class f) + 8)
    \/ heap_shadow_ sb reg sec a
    \/ depot_foot L (p_nodes0 P) (p_frames0 P) a
    (* [comment removed for export] *)
    \/ (tp + 8 <= a < tp + 16) \/ (p_dtls P <= a < p_dtls P + 4096).   (* [comment removed for export] *)
  Definition afoot (A : AState) : Z -> Prop :=
    afoot_ (a_pl A) (a_reg A) (a_livemap A) (a_qthread A) (a_qglobal A) (a_sec A) (a_fframes A).
  (* [comment removed for export] *)
  Definition flags_area (fs : Z) (a : Z) : Prop := fs + kFakeFlagsOffset <= a < fs + kFakeFramesOffset.

End Inv.
(* [comment removed for export] *)
Arguments wfP {_} {_} _ _.  Arguments wfM {_} {_} _ _.  Arguments wfR {_} {_} _ _.  Arguments wfC {_} {_} _ _.
Arguments wfX {_} {_} _ _.  Arguments wfV {_} {_} _ _.  Arguments wfQ {_} {_} _ _.  Arguments wfS {_} {_} _ _.
Arguments wfD {_} {_} _ _.  Arguments wfF {_} {_} _ _.  Arguments wfB {_} {_} _ _.  Arguments wfI {_} {_} _ _.
Arguments wfE {_} {_} _ _.  Arguments wfJ {_} {_} _ _.  Arguments wfN {_} {_} _ _.
Arguments wbP {_} {_} _ _.  Arguments wbM {_} {_} _ _.  Arguments wbR {_} {_} _ _.  Arguments wbC {_} {_} _ _.
Arguments wbX {_} {_} _ _.  Arguments wbV {_} {_} _ _.  Arguments wbQ {_} {_} _ _.  Arguments wbS {_} {_} _ _.
Arguments wbD {_} {_} _ _.  Arguments wbF {_} {_} _ _.  Arguments wbB {_} {_} _ _.  Arguments wbE {_} {_} _ _.  Arguments wbJ {_} {_} _ _.  Arguments wbN {_} {_} _ _.
Arguments WF_split {_} {_} _.

(* [comment removed for export] *)
#[warnings="-notation-for-abbreviation"] Notation VIS0 := AState.VIS0 (only parsing).
#[warnings="-notation-for-abbreviation"] Notation in_vis_shadow := AState.in_vis_shadow (only parsing).


(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import LayoutPA.

Section Pasan.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {DR : DepotRep}.
  Definition pa_hull (A : AState) : hull := ahull_of pa_image_ivs AL_pasan A.
  Definition pa_lhull (A : AState) : hull := alhull_of AL_pasan A.     (* [comment removed for export] *)
  Definition pa_eager (A : AState) : Z := aeager_of A.
  (* [comment removed for export] *)
  Definition pa_image_shadow (a : Z) : Prop := sh 0x10000 <= a < sh 0x60a000.
  Definition pa_owned (A : AState) (a : Z) : Prop := aowned LPA A a \/ pa_image_shadow a.
  Definition pa_ainv (A : AState) (m : mem) (md : Model) : Prop := ainv_ LPA AL_pasan pa_image_ivs pa_site_pcs A m md.
End Pasan.
