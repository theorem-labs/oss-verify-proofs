(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.  (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.

Module APopCap.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA AInv ALogic1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
#[local] Notation WF := (WF AL_pboth).
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma covered_length : forall (l : list Z) (n : Z), 0 <= n -> (forall k, 0 <= k < n -> In k l) -> n <= Z.of_nat (length l).
Proof.
  intros l n Hn COV.
  enough (L : (length (map Z.of_nat (seq 0 (Z.to_nat n))) <= length l)%nat) by (rewrite length_map, length_seq in L; lia).
  apply NoDup_incl_length.
  - apply (Finite.Injective_map_NoDup_in Z.of_nat); [intros x y _ _; lia| apply seq_NoDup].
  - intros x Hx. apply in_map_iff in Hx as (i & <- & Hi). apply in_seq in Hi. apply COV. lia.
Qed.

(* [comment removed for export] *)
Definition chunkP_idx (c : Z) (ch : chunk) : option Z :=
  match ch with ChP (CP c' k) => if Z.eqb c' c then Some k else None | ChS _ => None end.
Definition live_idx (c : Z) (lm : gmap Z liveinfo) : list Z :=
  omap (fun p : Z * liveinfo => chunkP_idx c (li_chunk (snd p))) (map_to_list lm).
Definition quar_idx (c : Z) (E : list qentry) : list Z := omap (fun e => chunkP_idx c (qe_chunk e)) E.

Lemma length_omap_le : forall {X Y} (f : X -> option Y) (l : list X), (length (omap f l) <= length l)%nat.
Proof. intros X Y f l. induction l as [|x l IH]; cbn; [lia|]. destruct (f x); cbn; lia. Qed.

Lemma in_omap : forall {X Y} (f : X -> option Y) (l : list X) x y, In x l -> f x = Some y -> In y (omap f l).
Proof.
  intros X Y f l x y Hx Hf. induction l as [|x0 l IH]; [destruct Hx|]. cbn.
  destruct Hx as [->|Hx]; [rewrite Hf; left; reflexivity|]. destruct (f x0); [right|]; apply IH; exact Hx.
Qed.

Lemma live_idx_in : forall c lm k, p_live_ lm c k -> In k (live_idx c lm).
Proof.
  intros c lm k (u & n & Hu). unfold live_idx.
  apply (in_omap _ _ (u, LI (ChP (CP c k)) n)); [| cbn; rewrite Z.eqb_refl; reflexivity].
  apply (proj1 (list_elem_of_In _ _)). apply elem_of_map_to_list. exact Hu.
Qed.
Lemma live_idx_len : forall c (lm : gmap Z liveinfo), Z.of_nat (length (live_idx c lm)) <= as_nlive_ lm.
Proof. intros c lm. unfold live_idx, as_nlive_. rewrite <- length_map_to_list. pose proof (length_omap_le (fun p : Z * liveinfo => chunkP_idx c (li_chunk (snd p))) (map_to_list lm)). lia. Qed.

Lemma quar_idx_in : forall c E k n, In (QE (ChP (CP c k)) n) E -> In k (quar_idx c E).
Proof. intros c E k n H. unfold quar_idx. apply (in_omap _ _ _ _ H). cbn. rewrite Z.eqb_refl. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ebytes (E : list qentry) : Z := fold_right (fun e acc => qe_bytes e + acc) 0 E.
Lemma ebytes_cons : forall e E, ebytes (e :: E) = qe_bytes e + ebytes E. Proof. reflexivity. Qed.
Lemma ebytes_app : forall E1 E2, ebytes (E1 ++ E2) = ebytes E1 + ebytes E2.
Proof. intros E1 E2. induction E1 as [|e E1 IH]; [reflexivity|]. cbn [app]. rewrite !ebytes_cons, IH. lia. Qed.
Lemma qe_bytes_nonneg : forall e, 0 <= qe_n e -> 0 <= qe_bytes e.
Proof. intros e H. unfold qe_bytes, user_size. destruct (Z.eqb_spec (qe_n e) 0); lia. Qed.
Lemma ebytes_nonneg : forall E, (forall e, In e E -> 0 <= qe_n e) -> 0 <= ebytes E.
Proof.
  intros E H. induction E as [|e E IH]; [cbn; lia|]. rewrite ebytes_cons.
  pose proof (qe_bytes_nonneg e (H e (or_introl eq_refl))). specialize (IH (fun e' He' => H e' (or_intror He'))). lia.
Qed.
Lemma q_bytes_cons : forall b bs, q_bytes (b :: bs) = batch_bytes b + q_bytes bs. Proof. reflexivity. Qed.
Lemma batch_bytes_eq : forall b, batch_bytes b = kQuarantineBatchBytes + ebytes (ba_entries b). Proof. reflexivity. Qed.
Lemma q_entries_cons : forall b bs, q_entries (b :: bs) = ba_entries b ++ q_entries bs. Proof. reflexivity. Qed.
Lemma q_bytes_entries : forall bs, q_bytes bs = kQuarantineBatchBytes * Z.of_nat (length bs) + ebytes (q_entries bs).
Proof.
  intros bs. induction bs as [|b bs IH]; [reflexivity|].
  rewrite q_bytes_cons, q_entries_cons, ebytes_app, batch_bytes_eq, IH. cbn [length]. lia.
Qed.
Lemma q_entries_app : forall b1 b2, q_entries (b1 ++ b2) = q_entries b1 ++ q_entries b2.
Proof. intros. unfold q_entries. rewrite flat_map_app. reflexivity. Qed.
Lemma q_bytes_app : forall b1 b2, q_bytes (b1 ++ b2) = q_bytes b1 + q_bytes b2.
Proof. intros b1 b2. induction b1 as [|b b1 IH]; [reflexivity|]. cbn [app]. rewrite !q_bytes_cons, IH. lia. Qed.

(* [comment removed for export] *)
Fixpoint zseq (a : Z) (k : nat) : list Z := match k with O => [] | S k' => a :: zseq (Z.succ a) k' end.
Lemma in_zseq : forall k a x, a <= x < a + Z.of_nat k -> In x (zseq a k).
Proof.
  induction k as [|k IH]; intros a x H; [lia|]. cbn [zseq]. destruct (Z.eq_dec a x) as [->|NE]; [left; reflexivity| right]. apply IH. lia.
Qed.
Lemma class_size_le4n : forall n, 16 <= n <= kMaxPrimaryUser -> class_size (class_of n) <= 4 * n.
Proof.
  assert (C : forallb (fun n => Z.leb (class_size (class_of n)) (4 * n)) (zseq 16 (Z.to_nat 64497)) = true) by (vm_cast_no_check (@eq_refl bool true)).
  intros n Hn. unfold kMaxPrimaryUser in Hn.
  pose proof (proj1 (forallb_forall _ _) C n) as X. cbv beta in X. apply Z.leb_le. apply X. apply in_zseq. lia.
Qed.
Lemma quar_idx_cons : forall c e E,
  quar_idx c (e :: E) = match chunkP_idx c (qe_chunk e) with Some k => k :: quar_idx c E | None => quar_idx c E end.
Proof. intros. unfold quar_idx. cbn. destruct (chunkP_idx c (qe_chunk e)); reflexivity. Qed.
Lemma filter_cons_len : forall (f : qentry -> bool) e E,
  length (filter f (e :: E)) = if f e then S (length (filter f E)) else length (filter f E).
Proof. intros. cbn. destruct (f e); reflexivity. Qed.

Lemma quar_idx_bytes : forall reg sec c E, 1 <= c <= 30 -> (forall e, In e E -> wf_qentry_ reg sec e) ->
  class_size c * Z.of_nat (length (quar_idx c E)) <=
  4 * ebytes E + class_size c * Z.of_nat (length (filter (fun e => Z.ltb (qe_n e) 16) E)).
Proof.
  intros reg sec c E Hc WQ. pose proof (class_size_range c Hc) as CSR.
  induction E as [|e E IH]; [cbn; lia|].
  specialize (IH (fun e' He' => WQ e' (or_intror He'))).
  pose proof (WQ e (or_introl eq_refl)) as We. unfold wf_qentry_ in We. destruct We as [N0 CH].
  pose proof (qe_bytes_nonneg e ltac:(lia)) as B0.
  rewrite quar_idx_cons, ebytes_cons, filter_cons_len. unfold chunkP_idx.
  destruct (qe_chunk e) as [[c' k]|s].
  - destruct (Z.eqb_spec c' c) as [->|NE].
    + destruct CH as (NP & CL & _). cbn [length]. destruct (Z.ltb_spec (qe_n e) 16) as [T|T].
      * rewrite !Nat2Z.inj_succ. lia.
      * rewrite Nat2Z.inj_succ. pose proof (class_size_le4n (qe_n e) ltac:(lia)) as L4. rewrite <- CL in L4.
        assert (QB : qe_bytes e = qe_n e) by (unfold qe_bytes, user_size; destruct (Z.eqb_spec (qe_n e) 0); lia). lia.
    + destruct (Z.ltb (qe_n e) 16); rewrite ?Nat2Z.inj_succ; lia.
  - destruct (Z.ltb (qe_n e) 16); rewrite ?Nat2Z.inj_succ; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Cap.
Context {Clg : Ceiling}.
  Context {DR : DepotRep}.
  Variables (A : AState) (c : Z).
  Hypothesis W : WF A.
  Hypothesis HC : 1 <= c <= 30.
  Hypothesis EMP : pk_chunks (a_cache A c) = [].
  Hypothesis SHORT : Z.of_nat (length (rg_free (a_reg A c))) < refill_count c.

  Let R := a_reg A c.
  Let qt := a_qthread A. Let qg := a_qglobal A.
  (* [comment removed for export] *)
  Let holders : list Z :=
    rg_free R ++ pk_chunks (a_cache A c) ++ a_paid A c ++
    (if Z.eqb c kQuarantineBatchClass then batch_indices_ qt qg else []).

  Lemma holders_cover : forall k, 0 <= k < carved_count A c -> In k holders.
  Proof.
    intros k Hk. pose proof (wfX A W c k HC Hk) as X. cbv zeta in X. destruct X as [X _]. subst holders.
    destruct (wfN A W) as (_ & _ & PD).
    destruct X as [F|[C|[V|[Q|B]]]]; rewrite !in_app_iff.
    - left. exact F.
    - right; left. exact C.
    - right; right; left. exact (PD c k HC (or_introl V)).
    - right; right; left. exact (PD c k HC (or_intror Q)).
    - right; right; right. destruct B as [-> Hb]. rewrite Z.eqb_refl. exact Hb.
  Qed.

  (* [comment removed for export] *)
  Theorem pop_cap : rg_allocated_user (a_reg A c) <= class_size c * (Z.of_nat (length (a_paid A c)) + 7) + class_slack c.
  Proof.
    pose proof (class_size_range c HC) as CSR. pose proof (max_count_range c HC) as (_ & _ & KR).
    destruct (wfR A W) as (WR & _ & _). pose proof (WR c HC) as WRc. unfold wf_region in WRc.
    destruct WRc as (AU & _ & _ & AMOD & _ & _ & _ & ND & _).
    pose proof (wfQ A W) as WQ. unfold wf_quarantine_ in WQ. destruct WQ as (WQt & WQg & _ & QBt & QBg & _).
    assert (CC : rg_allocated_user R = class_size c * carved_count A c).
    { unfold carved_count, carved_count_. subst R. pose proof (Z_div_mod_eq_full (rg_allocated_user (a_reg A c)) (class_size c)). lia. }
    pose proof (covered_length holders (carved_count A c) ltac:(unfold carved_count, carved_count_; apply Z.div_pos; lia) holders_cover) as CL.
    subst holders. rewrite !length_app, EMP in CL. cbn [length] in CL.
    pose proof (q_bytes_entries (qt ++ qg)) as QE. rewrite q_bytes_app, q_entries_app in QE.
    assert (WQE : forall e, In e (q_entries qt ++ q_entries qg) -> 0 <= qe_n e).
    { intros e He. apply in_app_iff in He. 
      assert (X : exists b, (In b qt \/ In b qg) /\ In e (ba_entries b)).
      { destruct He as [He|He]; unfold q_entries in He; apply in_flat_map in He as (b & Hb & Heb); exists b; tauto. }
      destruct X as (b & Hb & Heb).
      assert (WBb : wf_batch_ (a_reg A) (a_sec A) b).
      { destruct Hb as [Hb|Hb]; [exact (proj1 (Forall_forall _ _) WQt b Hb)| exact (proj1 (Forall_forall _ _) WQg b Hb)]. }
      destruct WBb as (_ & _ & FE). exact (proj1 (proj1 (proj1 (Forall_forall _ _) FE e Heb))). }
    pose proof (ebytes_nonneg (q_entries qt ++ q_entries qg) WQE) as EB0.
    assert (L3 : class_size c * Z.of_nat (length (if c =? kQuarantineBatchClass then batch_indices_ qt qg else [])) <= class_slack c).
    { unfold class_slack. destruct (Z.eqb_spec c kQuarantineBatchClass) as [->|NE].
      - unfold batch_indices_. rewrite length_map. change (class_size kQuarantineBatchClass) with kQuarantineBatchBytes.
        subst qt qg. unfold kQuarantineBatchBytes, kQuarantineMaxSize, kQuarantineCacheSize in *. lia.
      - cbn [length]. lia. }
    subst R qt qg. rewrite !Nat2Z.inj_add in CL. cbn [Z.of_nat] in CL. rewrite Z.add_0_r in CL || idtac.
    assert (P1 : class_size c * Z.of_nat (length (rg_free (a_reg A c))) <= class_size c * 7) by (apply Z.mul_le_mono_nonneg_l; lia).
    nia.
  Qed.
End Cap.
End APopCap.

   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Notation wz z := (Z_to_bv 64 z) (only parsing).
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kSpaceReserve, kMaxSize in *.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition cfoot_stat (a : Z) : Prop :=
  let I := al_instance AL_pboth in
     (I + off_primary_reserved_base <= a < I + off_primary_reserved_base + 8)
  \/ (I + off_primary_reserved_size <= a < I + off_primary_reserved_size + 8)
  \/ (I + off_SpaceBeg <= a < I + off_SpaceBeg + 8)
  \/ (I + off_release_interval <= a < I + off_release_interval + 4)
  \/ (I + off_RegionInfo_ptr <= a < I + off_RegionInfo_ptr + 8)
  \/ (I + off_PremappedHeap <= a < I + off_PremappedHeap + 1)
  \/ (I + off_sec_page_size <= a < I + off_sec_page_size + 8)
  \/ (I + off_sec_chunks <= a < I + off_sec_chunks + 8)
  \/ (I + off_sec_ptr_array_base <= a < I + off_sec_ptr_array_base + 8)
  \/ (I + off_sec_ptr_array_size <= a < I + off_sec_ptr_array_size + 8)
  \/ (I + off_q_max_size <= a < I + off_q_max_size + 8)
  \/ (I + off_q_min_size <= a < I + off_q_min_size + 8)
  \/ (I + off_q_max_cache_size <= a < I + off_q_max_cache_size + 8)
  \/ (I + off_max_user_malloc <= a < I + off_max_user_malloc + 8)
  \/ (I + off_min_redzone <= a < I + off_min_redzone + 2)
  \/ (I + off_max_redzone <= a < I + off_max_redzone + 2)
  \/ (I + off_alloc_dealloc_mismatch <= a < I + off_alloc_dealloc_mismatch + 1)
  \/ (al_malloc_context_size AL_pboth <= a < al_malloc_context_size AL_pboth + 4)
  \/ (al_can_poison_memory AL_pboth <= a < al_can_poison_memory AL_pboth + 1)
  \/ (al_page_size_cache AL_pboth <= a < al_page_size_cache AL_pboth + 8)
  \/ (al_may_return_null AL_pboth <= a < al_may_return_null AL_pboth + 1)
  \/ (al_rss_limit_exceeded AL_pboth <= a < al_rss_limit_exceeded AL_pboth + 1)
  \/ (al_dying_flag AL_pboth <= a < al_dying_flag AL_pboth + 4)
  \/ (al_malloc_hooks AL_pboth <= a < al_malloc_hooks AL_pboth + 80).

(* [comment removed for export] *)
Definition cfoot_thr (t a : Z) : Prop :=
     (t + off_th_context <= a < t + off_th_context + 8)
  \/ (t + off_th_stack_top <= a < t + off_th_stack_top + 8)
  \/ (t + off_th_stack_bottom <= a < t + off_th_stack_bottom + 8)
  \/ (t + off_th_stack_switching <= a < t + off_th_stack_switching + 1)
  \/ (t + off_th_unwinding <= a < t + off_th_unwinding + 1)
  \/ (t + 48 <= a < t + 64).

(* [comment removed for export] *)
Definition cfoot_misc (P : aplace) (a : Z) : Prop :=
  let tp := bv_unsigned (cl_tp LPA) in
     (p_ctx P + 8 <= a < p_ctx P + 12) \/ (p_ctx P + 152 <= a < p_ctx P + 160)
  \/ (tp - 88 <= a < tp - 80) \/ (tp <= a < tp + 8) \/ (tp + 8 <= a < tp + 16)
  \/ (p_dtls P + 24 <= a < p_dtls P + 32).

(* [comment removed for export] *)
Definition lfoot (P : aplace) (a : Z) : Prop :=
  let I := al_instance AL_pboth in
     (p_ri P <= a < p_ri P + kRegionInfoSize * 32)
  \/ (I + off_sec_mutex <= a < I + off_sec_mutex + 1)
  \/ (I + off_q_cache_mutex <= a < I + off_q_cache_mutex + 1)
  \/ (I + off_q_recycle_mutex <= a < I + off_q_recycle_mutex + 1)
  \/ (I + off_fallback_mutex <= a < I + off_fallback_mutex + 1)
  \/ (al_internal_alloc_inited AL_pboth + 1 <= a < al_internal_alloc_inited AL_pboth + 2).

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Definition rfoot (sb : Z) (R : region) (c a : Z) : Prop :=
     (region_info_addr sb c <= a < region_info_addr sb c + kRegionInfoSize)
  \/ (free_array_beg sb c <= a < free_array_beg sb c + rg_mapped_fa R).

End CEIL.

(* [comment removed for export] *)
Definition sfoot_stat (a : Z) : Prop :=
  let I := al_instance AL_pboth in
     (I + off_sec_n_reserved <= a < I + off_sec_n_reserved + 8)
  \/ (I + off_sec_n_chunks <= a < I + off_sec_n_chunks + 8)
  \/ (I + off_sec_chunks_sorted <= a < I + off_sec_chunks_sorted + 1)
  \/ (I + off_sec_stat_n_allocs <= a < I + 680)
  \/ (I + off_global_stats <= a < I + off_global_stats + 32).

(* [comment removed for export] *)
Definition iafoot (a : Z) : Prop :=
  let B := al_internal_allocator_inst AL_pboth in
     (B <= a < B + 0x81030) \/ (al_internal_alloc_inited AL_pboth <= a < al_internal_alloc_inited AL_pboth + 1).

Lemma NoDup_app_In : forall {X} (l1 l2 : list X) x, NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
  induction l1 as [|y l1 IH]; intros l2 x ND H1 H2; [destruct H1|]. cbn in ND. inversion ND as [|y' l' NI ND']; subst.
  destruct H1 as [E|H1]; [subst y; apply NI; apply list_elem_of_In; apply in_or_app; right; exact H2| exact (IH l2 x ND' H1 H2)].
Qed.

(* [comment removed for export] *)
Lemma bytes_at_mapped_off : forall (m : mem) a bs, bytes_at rsegs m a bs -> 0 <= a ->
  (a + Z.of_nat (length bs) <= 0x10000 \/ 0x60a000 <= a) -> mapped m a (Z.of_nat (length bs)).
Proof.
  (intros m a bs; (first [ intro dR_119; dand3 dR_119 as Ha Hn B | intros (Ha & Hn & B) ]); intros NNa LO i Hi E). specialize (B (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in B by lia.
  unfold mrd, wa in B. rewrite E in B. rewrite pa_seg_rom_none in B by (rewrite unsigned_lit by lia; lia).
  destruct (nth_error bs (Z.to_nat i)) eqn:N; [discriminate|]. apply nth_error_None in N. lia.
Qed.

(* [comment removed for export] *)
Section Transport.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Context {DR : DepotRep}.
  Variables (A : AState) (v v' : mem).
  Hypothesis AR : WF AL_pboth A /\ arepr LPA AL_pboth [] A v.
  Let WF0 : WF AL_pboth A. Proof. exact (proj1 AR). Qed.
  Let R : arepr LPA AL_pboth [] A v. Proof. exact (proj2 AR). Qed.
  Local Notation thr := (p_thr (a_pl A)).
  Local Notation sb := (a_sb A).
  (* [comment removed for export] *)
  Hypothesis NN : forall a, 0 <= a -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> a < 2^64 -> v (Z_to_bv 64 a) <> None -> v' (Z_to_bv 64 a) <> None.

  Lemma TPV : bv_unsigned (cl_tp LPA) = 0x5e7bd8.
  Proof. cbn [cl_tp LPA]. rewrite unsigned_lit by lia. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma mapped_N : forall a k, 0 <= a -> (a + k <= 0x10000 \/ 0x60a000 <= a) -> a + k <= 2^64 -> mapped v a k -> mapped v' a k.
  Proof. intros a k H0 H1 H2 M. eapply mapped_mono; [exact M|]. intros i Hi. apply NN; lia. Qed.
  Lemma junk_N : forall a k, 0 <= a -> (a + k <= 0x10000 \/ 0x60a000 <= a) -> junk_at rsegs v a k -> junk_at rsegs v' a k.
  Proof.
    (intros a k H0 H1; (first [ intro dR_120; dex1 dR_120 as bs; destruct dR_120 as [L B] | intro dR_120; dand3 dR_120 as bs L B | intros (bs & L & B) ])). pose proof (bytes_at_bound _ _ _ _ B) as BB. rewrite L in BB.
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
  Lemma locks_P : (forall a, lfoot (a_pl A) a -> v' (wz a) = v (wz a)) -> locks_repr_ LPA AL_pboth (a_pl A) [] v'.
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

  Lemma locks_P2 : (forall a, lfoot (a_pl A) a -> a <> al_internal_alloc_inited AL_pboth + 1 -> v' (wz a) = v (wz a)) ->
    u8_at rsegs v' (al_internal_alloc_inited AL_pboth + 1) 0 ->
    locks_repr_ LPA AL_pboth (a_pl A) [] v'.
  Proof.
    intros AG IAL. pose proof (ar_locks _ _ _ _ _ R) as C. unfold locks_repr_ in *. cbv zeta in *. destruct C as (C0 & C).
    (first [ pose proof ((sb_facts A WF0)) as dR_5; dand5 dR_5 as _ _ HB6 RSB SCE | pose proof (sb_facts A WF0) as (_ & _ & HB6 & RSB & SCE) ]). unfold a_sb, a_b6 in HB6, RSB, SCE.
    change (al_internal_alloc_inited AL_pboth) with 0x144648 in *. change (al_instance AL_pboth) with 0xb1558 in *.
    split.
    - intros c' Hc. destruct (C0 c' Hc) as [X Y]. unfold p_ri in *.
      split; [leaf X ltac:(apply AG; trim; unfold lfoot, p_ri; offs; unfold kHighMemBeg, kSpaceSize, kRegionInfoSize in *; lia)
           | leaf Y ltac:(apply AG; trim; unfold lfoot, p_ri; offs; unfold kHighMemBeg, kSpaceSize, kRegionInfoSize in *; lia)].
    - (first [ dand5 C as L1 L2 L3 L4 L5 | destruct C as (L1 & L2 & L3 & L4 & L5) ]). rewrite lockb_nil in *.
      split; [leaf L1 ltac:(apply AG; trim; unfold lfoot; offs; lia)|].
      split; [leaf L2 ltac:(apply AG; trim; unfold lfoot; offs; lia)|].
      split; [leaf L3 ltac:(apply AG; trim; unfold lfoot; offs; lia)|].
      split; [leaf L4 ltac:(apply AG; trim; unfold lfoot; offs; lia)| exact IAL].
  Qed.

  (* [comment removed for export] *)
  Lemma region_P : forall c', 1 <= c' <= 30 -> (forall a, rfoot sb (a_reg A c') c' a -> v' (wz a) = v (wz a)) ->
    region_repr_ LPA sb (a_reg A c') v' c'.
  Proof.
    intros c' Hc AG. pose proof (ar_regions _ _ _ _ _ R c' Hc) as C. pose proof alloc_ceiling_val as CE.
    pose proof (region_piece_bounds A c' WF0 Hc) as RB. cbv zeta in RB. (first [ pose proof ((wfR A WF0)) as dR_7; dand3 dR_7 as WR _ _ | destruct (wfR A WF0) as (WR & _ & _) ]). (first [ pose proof ((WR c' Hc)) as dR_8; dand8 dR_8 as Q1 Q2 Q3 Q4 Q5 Q6 Q7 _ | pose proof (WR c' Hc) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & _) ]).
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
    pose proof (ar_sec _ _ _ _ _ R) as C. pose proof alloc_ceiling_val as CE. (first [ pose proof ((place_facts A WF0)) as dR_10; dand13 dR_10 as _ _ _ _ _ _ _ _ _ _ _ Ppa _ | pose proof (place_facts A WF0) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ppa & _) ]). cbv zeta in Ppa.
    (first [ dand3 Ppa as Ppa1 Ppa2 Ppa3 | destruct Ppa as (Ppa1 & Ppa2 & Ppa3) ]). apply app_facts in Ppa1.
    (first [ pose proof ((wfS A WF0)) as dR_12; dand4 dR_12 as _ LEN RES _ | destruct (wfS A WF0) as (_ & LEN & RES & _) ]). unfold kChunksBlockCount in RES. unfold sec_repr_ in *. cbv zeta in *.
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
    intros AGfs. pose proof (ar_fsbase _ _ _ _ _ R) as C. pose proof alloc_ceiling_val as CE. (first [ pose proof ((place_fs A WF0)) as dR_14; dand3 dR_14 as FS1 FS2 FSM | pose proof (place_fs A WF0) as (FS1 & FS2 & FSM) ]). unfold a_fs in FS1, FS2, FSM, AGfs.
    unfold fs_base_ in *. cbv zeta in *. (first [ dand5 C as H0 H1 H2 M1 M2 | destruct C as (H0 & H1 & H2 & M1 & M2) ]).
    split; [|split; [leaf H1 ltac:(apply AGfs; unfold kFakeFlagsOffset; offs; lia)| split; [leaf H2 ltac:(apply AGfs; unfold kFakeFlagsOffset; offs; lia)| split]]].
    - intros k Hk. pose proof (H0 k Hk) as L. leaf L ltac:(apply AGfs; unfold kFakeFlagsOffset; offs; lia).
    - apply app_facts in FS1. apply mapped_N; [lia| unfold kFakeStackBytes in *; lia| lia| exact M1].
    - pose proof (fs_shadow_strict A (sh (p_fs (a_pl A))) WF0 ltac:(unfold a_fs, kFakeStackBytes; lia)) as X1.
      pose proof (fs_shadow_strict A (sh (p_fs (a_pl A)) + (kFakeStackBytes / 8 - 1)) WF0 ltac:(unfold a_fs, kFakeStackBytes; lia)) as X2.
      unfold in_shadow_strict, kLowShadowBeg, kShadowGapBeg, kHighShadowMapBeg, kHighMemBeg in X1, X2.
      apply mapped_N; [lia| right; lia| lia| exact M2].
  Qed.

  Lemma fsptrs_P : (forall a, a_fs A + kFakeFramesOffset <= a < a_fs A + kFakeStackBytes -> v' (wz a) = v (wz a)) ->
    fs_ptrs_ LPA (a_fs A) (a_fhint A) (a_fframes A) v'.
  Proof.
    intros AGfs ff f Hf. pose proof (ar_fsptrs _ _ _ _ _ R ff f Hf) as L.
    destruct (wfF A WF0) as (F1 & _). destruct (F1 ff f Hf) as (K0 & _). pose proof (fsize_pos _ K0) as FS.
    (first [ pose proof ((live_frame_where A ff f ff WF0 Hf ltac:(lia))) as dR_16; dand4 dR_16 as K _ R1 R2 | destruct (live_frame_where A ff f ff WF0 Hf ltac:(lia)) as (K & _ & R1 & R2) ]).
    leaf L ltac:(apply AGfs; unfold saved_flag_ptr, kFakeFramesOffset in *; lia).
  Qed.

  Lemma fsflags_P : (forall a, a_fs A + kFakeFlagsOffset <= a < a_fs A + kFakeFramesOffset -> v' (wz a) = v (wz a)) ->
    fs_flags_ LPA (a_fs A) (a_fhint A) (a_fframes A) v'.
  Proof.
    intros AGfs k pos Hk Hpos. (first [ pose proof ((ar_fsflags _ _ _ _ _ R k pos Hk Hpos)) as dR_17; dex1 dR_17 as b; destruct dR_17 as [U D] | pose proof ((ar_fsflags _ _ _ _ _ R k pos Hk Hpos)) as dR_17; dand3 dR_17 as b U D | destruct (ar_fsflags _ _ _ _ _ R k pos Hk Hpos) as (b & U & D) ]). exists b. split; [| exact D].
    pose proof (fflag_addr_range (a_fs A) k pos Hk Hpos).
    leaf U ltac:(apply AGfs; unfold kFakeFlagsOffset, kFakeFramesOffset, kFakeStackBytes in *; lia).
  Qed.

  (* [comment removed for export] *)
  Lemma maps_P : maps_repr_ AL_pboth (a_pl A) v'.
  Proof.
    (first [ pose proof ((ar_maps _ _ _ _ _ R)) as dR_18; dand4 dR_18 as M1 M2 M3 M4 | pose proof (ar_maps _ _ _ _ _ R) as (M1 & M2 & M3 & M4) ]). pose proof alloc_ceiling_val as CE.
    (first [ pose proof ((place_facts A WF0)) as dR_19; dand14 dR_19 as _ _ _ _ _ _ _ _ _ _ _ _ Psp0 _ | pose proof (place_facts A WF0) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Psp0 & _) ]). cbv zeta in Psp0.
    (first [ pose proof ((sb_facts A WF0)) as dR_20; dand5 dR_20 as _ _ HB6 RSB SCE | pose proof (sb_facts A WF0) as (_ & _ & HB6 & RSB & SCE) ]). unfold maps_repr_. unfold a_sb, a_b6, p_ri in *.
    cbn [al_image_lo al_image_hi AL_pboth] in M4 |- *.
    change (shadow_region 65536 (6332416 - 65536)) with (0x7fffa000, 0xbf400) in M4 |- *. cbn [fst snd] in M4 |- *.
    (first [ pose proof (stack_shadow_iv_facts) as dR_21; dand4 dR_21 as SF1 SF2 SF3 SF4 | pose proof stack_shadow_iv_facts as (SF1 & SF2 & SF3 & SF4) ]).
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
    pose proof (place_facts A WF0) as (Pthr & _). cbv zeta in Pthr. (first [ dand3 Pthr as Pthr1 Pthr2 Pthr3 | destruct Pthr as (Pthr1 & Pthr2 & Pthr3) ]). apply app_facts in Pthr1.
    (first [ pose proof ((C0 c' Hc')) as dR_23; dand5 dR_23 as LEN X1 X2 X3 X4 | destruct (C0 c' Hc') as (LEN & X1 & X2 & X3 & X4) ]). split; [exact LEN|].
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
    intros cache LINES. (first [ pose proof ((ar_cache _ _ _ _ _ R)) as dR_24; dand5 dR_24 as _ J1 J2 M1 M2 | pose proof (ar_cache _ _ _ _ _ R) as (_ & J1 & J2 & M1 & M2) ]). pose proof alloc_ceiling_val as CE.
    (first [ pose proof ((place_facts A WF0)) as dR_25; dand3 dR_25 as Pthr Pctx _ | pose proof (place_facts A WF0) as (Pthr & Pctx & _) ]). cbv zeta in Pthr, Pctx.
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
    intros u li Hl. destruct (wfV A WF0) as (V1 & _). (first [ pose proof ((V1 u li Hl)) as dR_28; dand3 dR_28 as N U C | pose proof (V1 u li Hl) as (N & U & C) ]). cbv zeta in C. unfold known.
    destruct (li_chunk li) as [[c' k']|[mb n0']].
    - (first [ dand3 C as N2 Hc Hk | destruct C as (N2 & Hc & Hk) ]). pose proof (class_of_range (li_n li) ltac:(lia)). rewrite <- Hc in *. unfold carved_count. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia; assumption.
    - (first [ dand3 C as N2 -> Hin | destruct C as (N2 & -> & Hin) ]). OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; [exact Hin| exact N2].
  Qed.

  Lemma qentry_wf : forall e, In e (q_entries (a_qthread A ++ a_qglobal A)) -> wf_qentry_ (a_reg A) (a_sec A) e.
  Proof.
    intros e He. (first [ pose proof ((wfQ A WF0)) as dR_31; dand3 dR_31 as Q1 Q2 _ | destruct (wfQ A WF0) as (Q1 & Q2 & _) ]).
    unfold q_entries in He. apply in_flat_map in He as (b & Hb & Heb). apply in_app_iff in Hb as [Hb|Hb];
      [pose proof (proj1 (Forall_forall _ _) Q1 b Hb) as WB| pose proof (proj1 (Forall_forall _ _) Q2 b Hb) as WB];
      (first [ dand3 WB as _ _ WB | destruct WB as (_ & _ & WB) ]); exact (proj1 (Forall_forall _ _) WB _ Heb).
  Qed.

  Lemma known_quar : forall e, In e (q_entries (a_qthread A ++ a_qglobal A)) -> known (qe_chunk e) (qe_n e).
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
    - (first [ dand3 CL as Hc Hk _ | destruct CL as (Hc & Hk & _) ]). (first [ pose proof ((carved_chunk_bounds A c' k' WF0 Hc Hk)) as dR_36; dand3 dR_36 as B1 B2 _ | pose proof (carved_chunk_bounds A c' k' WF0 Hc Hk) as (B1 & B2 & _) ]). pose proof (region_piece_bounds A c' WF0 Hc) as RB. cbv zeta in *.
      cbn [chunk_lo chunk_hi alloc_beg]. kung_all. lia.
    - destruct CL as (Hin & _). (first [ pose proof ((sec_chunk_bounds A _ WF0 Hin)) as dR_37; dand5 dR_37 as B1 _ B3 B4 B5 | pose proof (sec_chunk_bounds A _ WF0 Hin) as (B1 & _ & B3 & B4 & B5) ]). cbn [chunk_lo chunk_hi cs_map cs_n] in *.
      apply app_facts in B3. pose proof (needed_size_ge n0'). rewrite needed_size2_secondary in B5 by lia. pose proof (rounded_size_ge n0').
      unfold kMaxPrimaryUser, kPageSize, kSecondaryHeaderSize in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma batch_known : forall b, In b (a_qthread A ++ a_qglobal A) -> 0 <= ba_idx b < carved_count A kQuarantineBatchClass /\ Z.of_nat (length (ba_entries b)) <= kQuarantineBatchCount.
  Proof.
    intros b Hb. (first [ pose proof ((wfQ A WF0)) as dR_38; dand3 dR_38 as Q1 Q2 _ | destruct (wfQ A WF0) as (Q1 & Q2 & _) ]).
    assert (WB : wf_batch_ (a_reg A) (a_sec A) b).
    { apply in_app_iff in Hb as [Hb|Hb]; [exact (proj1 (Forall_forall _ _) Q1 b Hb)| exact (proj1 (Forall_forall _ _) Q2 b Hb)]. }
    (first [ dand3 WB as LEN Hk _ | destruct WB as (LEN & Hk & _) ]). split; [exact Hk| lia].
  Qed.

  Lemma batch_range : forall b, In b (a_qthread A ++ a_qglobal A) ->
    kHighMemBeg <= batch_addr sb b /\ batch_addr sb b + kQuarantineBatchBytes <= alloc_ceiling /\ batch_addr sb b mod 32 = 0.
  Proof.
    intros b Hb. destruct (batch_known b Hb) as [Hk _].
    assert (C24 : 1 <= kQuarantineBatchClass <= 30) by (unfold kQuarantineBatchClass; lia).
    (first [ pose proof ((carved_chunk_bounds A _ _ WF0 C24 Hk)) as dR_40; dand4 dR_40 as B1 B2 B3 _ | pose proof (carved_chunk_bounds A _ _ WF0 C24 Hk) as (B1 & B2 & B3 & _) ]). pose proof (region_piece_bounds A _ WF0 C24) as RB. cbv zeta in *.
    unfold batch_addr. rewrite <- class_size_24. unfold kQuarantineBatchClass in *. kung_all. lia.
  Qed.

  Lemma batch_idx_range : forall k, In k (batch_indices_ (a_qthread A) (a_qglobal A)) -> 0 <= k < carved_count A kQuarantineBatchClass.
  Proof. intros k Hk. unfold batch_indices_ in Hk. apply in_map_iff in Hk as (b & <- & Hb). exact (proj1 (batch_known b Hb)). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition carved (ch : chunk) : Prop :=
    match ch with ChP (CP c' k') => 1 <= c' <= 30 /\ 0 <= k' < carved_count A c' | ChS s => In s (sr_chunks (a_sec A)) end.
  Lemma known_carved : forall ch n1, known ch n1 -> carved ch.
  Proof. intros ch n1 K. unfold known, carved in *. destruct ch as [[c' k']|[mb n0']]; tauto. Qed.
  Lemma batch_carved : forall b, In b (a_qthread A ++ a_qglobal A) -> carved (ChP (CP kQuarantineBatchClass (ba_idx b))).
  Proof. intros b Hb. unfold carved. split; [unfold kQuarantineBatchClass; lia| exact (proj1 (batch_known b Hb))]. Qed.
  Lemma cached_carved : forall c' k, 1 <= c' <= 30 -> p_cached_ (a_cache A) c' k -> carved (ChP (CP c' k)).
  Proof. intros c' k Hc C. unfold carved. split; [exact Hc|]. (first [ pose proof ((wfC A WF0)) as dR_41; dand3 dR_41 as WC _ _ | destruct (wfC A WF0) as (WC & _ & _) ]). (first [ pose proof ((WC c' ltac:(lia))) as dR_42; dand4 dR_42 as _ _ CR' _ | destruct (WC c' ltac:(lia)) as (_ & _ & CR' & _) ]). exact (CR' k C). Qed.
  Lemma free_carved : forall c' k, 1 <= c' <= 30 -> p_free_ (a_reg A) c' k -> carved (ChP (CP c' k)).
  Proof. intros c' k Hc F. unfold carved. split; [exact Hc|]. (first [ pose proof ((wfR A WF0)) as dR_43; dand3 dR_43 as WR _ _ | destruct (wfR A WF0) as (WR & _ & _) ]). (first [ pose proof ((WR c' Hc)) as dR_44; dand10 dR_44 as _ _ _ _ _ _ _ _ FR _ | destruct (WR c' Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & FR & _) ]). exact (FR k F). Qed.

  (* [comment removed for export] *)
  Lemma carved_prim_where : forall c' k, carved (ChP (CP c' k)) ->
    region_beg sb c' <= chunk_addr sb c' k /\ chunk_addr sb c' k + class_size c' <= region_beg sb c' + rg_allocated_user (a_reg A c') /\
    rg_allocated_user (a_reg A c') <= rg_mapped_user (a_reg A c') /\ region_beg sb c' + rg_mapped_user (a_reg A c') <= region_beg sb c' + kFreeArrayOffset /\
    region_beg sb c' + kRegionSize <= a_sb A + kSpaceSize /\ a_sb A <= region_beg sb c' /\
    a_b6 A <= a_sb A /\ a_sb A + kSpaceSize + 4096 <= a_b6 A + kSpaceReserve /\
    kHighMemBeg <= a_b6 A /\ a_sb A + kSpaceSize + 4096 <= alloc_ceiling /\ 32 <= class_size c'.
  Proof.
    intros c' k [Hc Hk]. (first [ pose proof ((carved_chunk_bounds A c' k WF0 Hc Hk)) as dR_45; dand4 dR_45 as B1 B2 _ B4 | pose proof (carved_chunk_bounds A c' k WF0 Hc Hk) as (B1 & B2 & _ & B4) ]). pose proof (region_piece_bounds A c' WF0 Hc) as RB. cbv zeta in *.
    (first [ pose proof ((sb_facts A WF0)) as dR_46; dand5 dR_46 as _ _ HB6 RSB SCE | pose proof (sb_facts A WF0) as (_ & _ & HB6 & RSB & SCE) ]). change (a_sb A) with sb in *. unfold kSpaceReserve, kSpaceSize in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma carved_range : forall ch, carved ch -> 0x60a000 <= chunk_lo sb ch /\ chunk_hi sb ch <= alloc_ceiling /\ chunk_lo sb ch < chunk_hi sb ch.
  Proof.
    intros ch C. destruct ch as [[c' k']|[mb n0']].
    - pose proof (carved_prim_where c' k' C) as W. cbn [chunk_lo chunk_hi alloc_beg]. change (a_sb A) with sb in W. kung_all. lia.
    - unfold carved in C. (first [ pose proof ((sec_chunk_bounds A _ WF0 C)) as dR_47; dand5 dR_47 as B1 _ B3 B4 B5 | pose proof (sec_chunk_bounds A _ WF0 C) as (B1 & _ & B3 & B4 & B5) ]). cbn [chunk_lo chunk_hi cs_map cs_n] in *.
      apply app_facts in B3. pose proof (needed_size_ge n0').
      pose proof (needed_size2_secondary n0' ltac:(lia)). pose proof (rounded_size_ge n0'). unfold kMaxPrimaryUser, kPageSize in *. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma carved_app : forall ch, carved ch -> app_rangeA AL_pboth (chunk_lo sb ch) (chunk_hi sb ch - chunk_lo sb ch).
  Proof.
    intros ch C. destruct ch as [[c' k']|[mb n0']].
    - pose proof (carved_prim_where c' k' C) as W. cbn [chunk_lo chunk_hi alloc_beg]. change (a_sb A) with sb in W.
      apply app_rangeA_hi; kung_all; lia.
    - unfold carved in C. (first [ pose proof ((sec_chunk_bounds A _ WF0 C)) as dR_48; dand5 dR_48 as B1 _ B3 B4 B5 | pose proof (sec_chunk_bounds A _ WF0 C) as (B1 & _ & B3 & B4 & B5) ]). cbn [chunk_lo chunk_hi cs_map cs_n] in *.
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
      destruct (bm_sep A 0%nat i _ _ _ _ WF0 E0 Hi ltac:(intros E; exact (NP _ eq_refl (eq_sym E)))) as [D|D]; cbn [chunk_lo chunk_hi alloc_beg]; [left| right]; kung_all; lia.
    - unfold carved in C. destruct (In_nth_error' _ _ C) as [j Hj]. pose proof (bm_nth_sec A j s Hj) as Ej.
      destruct (bm_sep A (15 + j)%nat i _ _ _ _ WF0 Ej Hi ltac:(intros E; exact (NS j s eq_refl Hj (eq_sym E)))) as [D|D];
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
  Lemma carved_apart_dtls : forall ch, carved ch -> chunk_hi sb ch <= p_dtls (a_pl A) \/ p_dtls (a_pl A) + 4096 <= chunk_lo sb ch.
  Proof. intros ch C. apply (carved_apart_bm ch 14%nat); [exact C| reflexivity| intros; lia| intros; lia]. Qed.
  Lemma carved_apart_pa : forall ch, carved ch -> chunk_hi sb ch <= p_pa (a_pl A) \/ p_pa (a_pl A) + kPtrArrayReserve <= chunk_lo sb ch.
  Proof. intros ch C. apply (carved_apart_bm ch 1%nat); [exact C| reflexivity| intros; lia| intros; lia]. Qed.

  (* [comment removed for export] *)
  Lemma sec_apart_b6 : forall s, In s (sr_chunks (a_sec A)) -> cs_map s + map_size (cs_n s) <= a_b6 A \/ a_b6 A + kSpaceReserve <= cs_map s.
  Proof.
    intros s Hin. destruct (carved_apart_bm (ChS s) 0%nat (a_b6 A) kSpaceReserve Hin (proj1 (bm_nth_fixed A)) ltac:(intros p' E; discriminate) ltac:(intros; lia)) as [D|D];
      destruct s as [mb n1]; cbn [chunk_lo chunk_hi cs_map cs_n] in *; [left| right]; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma carved_apart_ri : forall ch, carved ch -> chunk_hi sb ch <= a_ri A \/ a_ri A + 4096 <= chunk_lo sb ch.
  Proof.
    intros ch C. (first [ pose proof ((sb_facts A WF0)) as dR_49; dand5 dR_49 as _ _ HB6 RSB SCE | pose proof (sb_facts A WF0) as (_ & _ & HB6 & RSB & SCE) ]). destruct ch as [[c' k']|s].
    - pose proof (carved_prim_where c' k' C) as W. left. cbn [chunk_hi]. unfold a_ri, p_ri. change (p_sb (a_pl A)) with sb. change (a_sb A) with sb in *. kung_all. lia.
    - unfold carved in C. destruct (sec_apart_b6 s C) as [D|D]; destruct s as [mb n1]; cbn [chunk_lo chunk_hi cs_map cs_n] in *;
        unfold a_ri, p_ri, a_b6, a_sb in *; change (p_sb (a_pl A)) with sb in *; [left| right]; kung_all; lia.
  Qed.
  Lemma carved_apart_fa : forall ch c'', carved ch -> 1 <= c'' <= 30 ->
    chunk_hi sb ch <= free_array_beg sb c'' \/ free_array_beg sb c'' + rg_mapped_fa (a_reg A c'') <= chunk_lo sb ch.
  Proof.
    intros ch c'' C Hc''. (first [ pose proof ((sb_facts A WF0)) as dR_50; dand5 dR_50 as _ _ HB6 RSB SCE | pose proof (sb_facts A WF0) as (_ & _ & HB6 & RSB & SCE) ]). pose proof (region_piece_bounds A c'' WF0 Hc'') as RB''. cbv zeta in RB''.
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
      destruct (bm_sep A (15 + j1)%nat (15 + j2)%nat _ _ _ _ WF0 (bm_nth_sec A j1 s1 Hj1) (bm_nth_sec A j2 s2 Hj2) ltac:(lia)) as [D|D];
        destruct s1 as [mb1 n1]; destruct s2 as [mb2 n2]; cbn [chunk_lo chunk_hi cs_map cs_n] in *; [left| right]; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma live_not_quar_chunk : forall u li e, a_livemap A !! u = Some li -> In e (q_entries (a_qthread A ++ a_qglobal A)) -> li_chunk li <> qe_chunk e.
  Proof.
    intros u li e Hl He E. (first [ pose proof ((wfQ A WF0)) as dR_51; dand8 dR_51 as _ _ _ _ _ _ _ NLQ | destruct (wfQ A WF0) as (_ & _ & _ & _ & _ & _ & _ & NLQ) ]). apply (NLQ u li Hl).
    unfold quarantined_chunks_. rewrite E. apply in_map. exact He.
  Qed.
  Lemma live_not_batch : forall u li b, a_livemap A !! u = Some li -> In b (a_qthread A ++ a_qglobal A) -> li_chunk li <> ChP (CP kQuarantineBatchClass (ba_idx b)).
  Proof.
    intros u li b Hl Hb E. pose proof (batch_known b Hb) as [Hk _].
    pose proof (wfX A WF0 kQuarantineBatchClass (ba_idx b) ltac:(unfold kQuarantineBatchClass; lia) Hk) as X. cbv zeta in X.
    (first [ dand11 X as _ _ _ _ _ _ _ _ _ NVB _ | destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & NVB & _) ]). apply NVB. split.
    - exists u, (li_n li). rewrite <- E. destruct li; exact Hl.
    - split; [reflexivity|]. unfold batch_indices_. apply in_map. exact Hb.
  Qed.
  Lemma live_not_free : forall u li c' k, a_livemap A !! u = Some li -> 1 <= c' <= 30 -> p_free_ (a_reg A) c' k -> li_chunk li <> ChP (CP c' k).
  Proof.
    intros u li c' k Hl Hc F E. pose proof (free_carved c' k Hc F) as [_ Hk].
    pose proof (wfX A WF0 c' k Hc Hk) as X. cbv zeta in X. (first [ dand4 X as _ _ NFV _ | destruct X as (_ & _ & NFV & _) ]). apply NFV. split; [exact F|].
    exists u, (li_n li). rewrite <- E. destruct li; exact Hl.
  Qed.
  Lemma live_not_cached : forall u li c' k, a_livemap A !! u = Some li -> 1 <= c' <= 30 -> p_cached_ (a_cache A) c' k -> li_chunk li <> ChP (CP c' k).
  Proof.
    intros u li c' k Hl Hc C E. pose proof (cached_carved c' k Hc C) as [_ Hk].
    pose proof (wfX A WF0 c' k Hc Hk) as X. cbv zeta in X. (first [ dand7 X as _ _ _ _ _ NCV _ | destruct X as (_ & _ & _ & _ & _ & NCV & _) ]). apply NCV. split; [exact C|].
    exists u, (li_n li). rewrite <- E. destruct li; exact Hl.
  Qed.
  Lemma quar_not_batch : forall e b, In e (q_entries (a_qthread A ++ a_qglobal A)) -> In b (a_qthread A ++ a_qglobal A) -> qe_chunk e <> ChP (CP kQuarantineBatchClass (ba_idx b)).
  Proof.
    intros e b He Hb E. pose proof (batch_known b Hb) as [Hk _].
    pose proof (wfX A WF0 kQuarantineBatchClass (ba_idx b) ltac:(unfold kQuarantineBatchClass; lia) Hk) as X. cbv zeta in X.
    (first [ dand11 X as _ _ _ _ _ _ _ _ _ _ NQB | destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NQB) ]). apply NQB. split.
    - exists (qe_n e). rewrite <- E. destruct e; exact He.
    - split; [reflexivity|]. unfold batch_indices_. apply in_map. exact Hb.
  Qed.
  Lemma quar_not_cached : forall e c' k, In e (q_entries (a_qthread A ++ a_qglobal A)) -> 1 <= c' <= 30 -> p_cached_ (a_cache A) c' k -> qe_chunk e <> ChP (CP c' k).
  Proof.
    intros e c' k He Hc C E. pose proof (cached_carved c' k Hc C) as [_ Hk].
    pose proof (wfX A WF0 c' k Hc Hk) as X. cbv zeta in X. (first [ dand8 X as _ _ _ _ _ _ NCQ _ | destruct X as (_ & _ & _ & _ & _ & _ & NCQ & _) ]). apply NCQ. split; [exact C|].
    exists (qe_n e). rewrite <- E. destruct e; exact He.
  Qed.
  Lemma batch_not_cached : forall b c' k, In b (a_qthread A ++ a_qglobal A) -> 1 <= c' <= 30 -> p_cached_ (a_cache A) c' k ->
    ChP (CP kQuarantineBatchClass (ba_idx b)) <> ChP (CP c' k).
  Proof.
    intros b c' k Hb Hc C E. injection E as <- <-. pose proof (batch_known b Hb) as [Hk _].
    pose proof (wfX A WF0 kQuarantineBatchClass (ba_idx b) ltac:(unfold kQuarantineBatchClass; lia) Hk) as X. cbv zeta in X.
    (first [ dand9 X as _ _ _ _ _ _ _ NCB _ | destruct X as (_ & _ & _ & _ & _ & _ & _ & NCB & _) ]). apply NCB. split; [exact C|]. split; [reflexivity|]. unfold batch_indices_. apply in_map. exact Hb.
  Qed.
  Lemma live_live_chunk : forall u u' li li', a_livemap A !! u = Some li -> a_livemap A !! u' = Some li' -> u <> u' -> li_chunk li <> li_chunk li'.
  Proof. intros. (first [ pose proof ((wfV A WF0)) as dR_58; dand3 dR_58 as _ UQ _ | destruct (wfV A WF0) as (_ & UQ & _) ]). eapply UQ; eassumption. Qed.
  (* [comment removed for export] *)
  Lemma batches_nodup : NoDup (map ba_idx (a_qthread A ++ a_qglobal A)).
  Proof. (first [ pose proof ((wfQ A WF0)) as dR_59; dand7 dR_59 as _ _ _ _ _ ND _ | destruct (wfQ A WF0) as (_ & _ & _ & _ & _ & ND & _) ]). exact ND. Qed.

  (* [comment removed for export] *)
  Lemma thr_owned : forall a, thr <= a < thr + 4096 -> pa_owned A a.
  Proof.
    intros a Ha. (first [ pose proof ((bm_nth_fixed A)) as dR_60; dand6 dR_60 as _ _ _ _ E4 _ | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & E4 & _) ]).
    apply (owned_rt A a thr 4096); [apply rt_fixed_in; cbn; tauto| exact Ha
      | eapply (fixed_bm_no_live_user A 4); [exact WF0| lia| exact E4| exact Ha]
      | eapply (fixed_bm_no_live_frame A 4); [exact WF0| lia| lia| exact E4| exact Ha]].
  Qed.
  Lemma n0_owned : forall a, p_nodes0 (a_pl A) <= a < p_nodes0 (a_pl A) + kDepotNodesBlock -> pa_owned A a.
  Proof.
    intros a Ha. (first [ pose proof ((bm_nth_fixed A)) as dR_61; dand9 dR_61 as _ _ _ _ _ _ _ E7 _ | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & _ & _ & _ & E7 & _) ]).
    apply (owned_rt A a (p_nodes0 (a_pl A)) kDepotNodesBlock); [apply rt_fixed_in; cbn; tauto| exact Ha
      | eapply (fixed_bm_no_live_user A 7); [exact WF0| lia| exact E7| exact Ha]
      | eapply (fixed_bm_no_live_frame A 7); [exact WF0| lia| lia| exact E7| exact Ha]].
  Qed.
  Lemma f0_owned : forall a, p_frames0 (a_pl A) <= a < p_frames0 (a_pl A) + kStackStoreBlockBytes -> pa_owned A a.
  Proof.
    intros a Ha. (first [ pose proof ((bm_nth_fixed A)) as dR_62; dand10 dR_62 as _ _ _ _ _ _ _ _ E8 _ | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & _ & _ & _ & _ & E8 & _) ]).
    apply (owned_rt A a (p_frames0 (a_pl A)) kStackStoreBlockBytes); [apply rt_fixed_in; cbn; tauto| exact Ha
      | eapply (fixed_bm_no_live_user A 8); [exact WF0| lia| exact E8| exact Ha]
      | eapply (fixed_bm_no_live_frame A 8); [exact WF0| lia| lia| exact E8| exact Ha]].
  Qed.
  Lemma dstat_owned : forall a, 0x186a88 <= a < 0x5d6aa8 -> pa_owned A a.
  Proof. intros a Ha. apply asI_static_owned. cbn [cl_static LPA]. apply depot_static. cbn. unfold kDepotNodesL1. lia. Qed.

  (* [comment removed for export] *)
  Lemma hdr_foot_in : forall ch n1 a, known ch n1 ->
    hdr_foot sb ch n1 a \/ (user_of sb ch n1 <= a < user_of sb ch n1 + 8) -> chunk_lo sb ch <= a < chunk_hi sb ch.
  Proof.
    intros ch n1 a CL Ha. unfold known in CL. unfold hdr_foot in Ha. destruct ch as [[c' k']|[mb n0']].
    - (first [ dand4 CL as Hc Hk Hn Hcl | destruct CL as (Hc & Hk & Hn & Hcl) ]). (first [ pose proof ((primary_layout sb c' k' n1 Hc Hn Hcl)) as dR_64; dand5 dR_64 as L1 L2 L3 L5 L4 | pose proof (primary_layout sb c' k' n1 Hc Hn Hcl) as (L1 & L2 & L3 & L5 & L4) ]). cbv zeta in *.
      cbn [chunk_lo chunk_hi alloc_beg user_of] in *. lia.
    - (first [ dand3 CL as Hin Hn -> | destruct CL as (Hin & Hn & ->) ]). (first [ pose proof ((secondary_layout mb n1 Hn)) as dR_66; dand7 dR_66 as S1 S2 S3 S4 S5 S6 S7 | pose proof (secondary_layout mb n1 Hn) as (S1 & S2 & S3 & S4 & S5 & S6 & S7) ]).
      cbn [chunk_lo chunk_hi alloc_beg user_of cs_map cs_n] in *. unfold kSecondaryHeaderSize in *. lia.
  Qed.

  Lemma user_in : forall ch n1, known ch n1 -> chunk_lo sb ch <= user_of sb ch n1 /\ user_of sb ch n1 + n1 <= chunk_hi sb ch.
  Proof.
    intros ch n1 CL. unfold known in CL. destruct ch as [[c' k']|[mb n0']].
    - (first [ dand4 CL as Hc Hk Hn Hcl | destruct CL as (Hc & Hk & Hn & Hcl) ]). (first [ pose proof ((primary_layout sb c' k' n1 Hc Hn Hcl)) as dR_68; dand3 dR_68 as L1 L2 _ | pose proof (primary_layout sb c' k' n1 Hc Hn Hcl) as (L1 & L2 & _) ]). cbv zeta in *. cbn [chunk_lo chunk_hi alloc_beg user_of] in *. lia.
    - (first [ dand3 CL as Hin Hn -> | destruct CL as (Hin & Hn & ->) ]). (first [ pose proof ((secondary_layout mb n1 Hn)) as dR_70; dand4 dR_70 as S1 S2 S3 _ | pose proof (secondary_layout mb n1 Hn) as (S1 & S2 & S3 & _) ]). cbn [chunk_lo chunk_hi alloc_beg user_of cs_map cs_n] in *. unfold kSecondaryHeaderSize in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma live_user_in_carved : forall ch a u li, carved ch -> chunk_lo sb ch <= a < chunk_hi sb ch ->
    a_livemap A !! u = Some li -> u <= a < u + li_n li -> li_chunk li = ch.
  Proof.
    intros ch a u li C Ha Hl Hu. pose proof (known_carved _ _ (known_live u li Hl)) as C'.
    destruct (chunk_eq_dec (li_chunk li) ch) as [E|NE]; [exact E|]. exfalso.
    pose proof (user_in _ _ (known_live u li Hl)) as UR. destruct (wfV A WF0) as (V1 & _). (first [ pose proof ((V1 u li Hl)) as dR_71; dand3 dR_71 as _ U _ | pose proof (V1 u li Hl) as (_ & U & _) ]). rewrite <- U in UR.
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
      + apply b6_no_live_frame; [exact WF0|]. kung_all. lia.
    - unfold carved in C. destruct (In_nth_error' _ _ C) as [i Hi]. destruct s as [mb n1]. cbn [chunk_lo chunk_hi cs_map cs_n] in Ha.
      split; [exists mb, (map_size n1); split; [exact (rt_sec_in A _ C)| exact Ha]|]. exact (sec_no_live_frame A i _ a WF0 Hi Ha).
  Qed.

  (* [comment removed for export] *)
  Lemma carved_owned : forall ch a, carved ch -> chunk_lo sb ch <= a < chunk_hi sb ch ->
    (forall u li, a_livemap A !! u = Some li -> li_chunk li = ch -> ~ (u <= a < u + li_n li)) -> pa_owned A a.
  Proof.
    intros ch a C Ha NU. destruct (carved_in_rt ch a C Ha) as [(b & s & Hin & Hb) NF].
    apply (owned_rt A a b s Hin Hb); [| exact NF].
    ((first [ intro dR_121; dex2 dR_121 as u li; destruct dR_121 as [Hl Hu] | intro dR_121; dand4 dR_121 as u li Hl Hu | intros (u & li & Hl & Hu) ])). exact (NU u li Hl (live_user_in_carved ch a u li C Ha Hl Hu) Hu).
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
    intros u li Hl AG. (first [ pose proof ((ar_live _ _ _ _ _ R u li Hl)) as dR_72; dand3 dR_72 as HR MU0 MC | destruct (ar_live _ _ _ _ _ R u li Hl) as (HR & MU0 & MC) ]). pose proof alloc_ceiling_val as CE.
    pose proof (known_live u li Hl) as CL. pose proof (known_range _ _ CL) as RNG.
    destruct (wfV A WF0) as (V1 & _). (first [ pose proof ((V1 u li Hl)) as dR_73; dand3 dR_73 as N U _ | pose proof (V1 u li Hl) as (N & U & _) ]).
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
    intros e He AG. (first [ pose proof ((ar_quar _ _ _ _ _ R)) as dR_74; dand3 dR_74 as _ _ QR | pose proof (ar_quar _ _ _ _ _ R) as (_ & _ & QR) ]). (first [ pose proof ((QR e He)) as dR_75; dand3 dR_75 as HR J MC | destruct (QR e He) as (HR & J & MC) ]). pose proof alloc_ceiling_val as CE.
    pose proof (known_quar e He) as CL. pose proof (known_range _ _ CL) as RNG.
    pose proof (hdr_foot_in (qe_chunk e) (qe_n e) (user_of sb (qe_chunk e) (qe_n e)) CL ltac:(right; lia)) as UR.
    split; [|split].
    - apply hdr_P; [| exact HR]. intros a Ha. apply AG. apply (hdr_foot_in _ (qe_n e)); [exact CL| left; exact Ha].
    - apply junk_N; [lia| right; lia| exact J].
    - apply mapped_N; [lia| right; lia| lia| exact MC].
  Qed.

  Lemma batches_P : forall bs, (forall b, In b bs -> In b (a_qthread A ++ a_qglobal A)) ->
    (forall b a, In b bs -> batch_addr sb b <= a < batch_addr sb b + kQuarantineBatchBytes -> v' (wz a) = v (wz a)) ->
    batches_repr LPA v sb bs -> batches_repr LPA v' sb bs.
  Proof.
    induction bs as [|b bs IH]; intros SUB AG BR; [exact I|]. pose proof alloc_ceiling_val as CE.
    cbn [batches_repr] in *. (first [ dand6 BR as X1 X2 X3 X4 M BR | destruct BR as (X1 & X2 & X3 & X4 & M & BR) ]).
    assert (INb : In b (a_qthread A ++ a_qglobal A)) by (apply SUB; left; reflexivity).
    destruct (batch_known b INb) as [Hk LEN]. (first [ pose proof ((batch_range b INb)) as dR_77; dand3 dR_77 as R1 R2 R3 | pose proof (batch_range b INb) as (R1 & R2 & R3) ]).
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
    (intros qc bs AG; (first [ intro dR_122; dand4 dR_122 as X1 X2 X3 X4 | intros (X1 & X2 & X3 & X4) ])).
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
    intros AGt AGg AGb AGe. (first [ pose proof ((ar_quar _ _ _ _ _ R)) as dR_78; dand3 dR_78 as QT QG QR | pose proof (ar_quar _ _ _ _ _ R) as (QT & QG & QR) ]). unfold quarantine_repr_. change (p_sb (a_pl A)) with sb in *.
    pose proof (place_facts A WF0) as (Pthr & _). cbv zeta in Pthr. pose proof alloc_ceiling_val as CE.
    split; [|split].
    - (first [ dand5 QT as X1 X2 X3 X4 BR | destruct QT as (X1 & X2 & X3 & X4 & BR) ]). unfold qcache_repr.
      (first [ pose proof ((qcache_head_P (thr + off_th_qcache) (a_qthread A) AGt (conj X1 (conj X2 (conj X3 X4))))) as dR_80; dand4 dR_80 as Y1 Y2 Y3 Y4 | pose proof (qcache_head_P (thr + off_th_qcache) (a_qthread A) AGt (conj X1 (conj X2 (conj X3 X4)))) as (Y1 & Y2 & Y3 & Y4) ]).
      split; [exact Y1|]. split; [exact Y2|]. split; [exact Y3|]. split; [exact Y4|].
      apply batches_P; [intros b Hb; apply in_or_app; left; exact Hb| | exact BR]. intros b a Hb Ha. apply (AGb b a); [apply in_or_app; left; exact Hb| exact Ha].
    - (first [ dand5 QG as X1 X2 X3 X4 BR | destruct QG as (X1 & X2 & X3 & X4 & BR) ]). unfold qcache_repr.
      (first [ pose proof ((qcache_head_P (al_instance AL_pboth + off_q_cache_list_size) (a_qglobal A) AGg (conj X1 (conj X2 (conj X3 X4))))) as dR_82; dand4 dR_82 as Y1 Y2 Y3 Y4 | pose proof (qcache_head_P (al_instance AL_pboth + off_q_cache_list_size) (a_qglobal A) AGg (conj X1 (conj X2 (conj X3 X4)))) as (Y1 & Y2 & Y3 & Y4) ]).
      split; [exact Y1|]. split; [exact Y2|]. split; [exact Y3|]. split; [exact Y4|].
      apply batches_P; [intros b Hb; apply in_or_app; right; exact Hb| | exact BR]. intros b a Hb Ha. apply (AGb b a); [apply in_or_app; right; exact Hb| exact Ha].
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
    (first [ pose proof ((carved_chunk_bounds A c' k WF0 Hc Hk)) as dR_83; dand4 dR_83 as B1 B2 B3 B4 | pose proof (carved_chunk_bounds A c' k WF0 Hc Hk) as (B1 & B2 & B3 & B4) ]). pose proof (region_piece_bounds A c' WF0 Hc) as RB. cbv zeta in *.
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
    intros sc Hin. pose proof alloc_ceiling_val as CE. (first [ pose proof ((sec_chunk_bounds A _ WF0 Hin)) as dR_89; dand5 dR_89 as B1 B2 B3 B4 B5 | pose proof (sec_chunk_bounds A _ WF0 Hin) as (B1 & B2 & B3 & B4 & B5) ]).
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
    - destruct C as [Hc Hk]. (first [ pose proof ((chunk_shadow c' k' Hc Hk)) as dR_91; dand4 dR_91 as E HS HR _ | pose proof (chunk_shadow c' k' Hc Hk) as (E & HS & HR & _) ]). cbn [chunk_lo chunk_hi alloc_beg].
      (first [ pose proof ((carved_chunk_bounds A c' k' WF0 Hc Hk)) as dR_92; dand4 dR_92 as _ _ B3 _ | pose proof (carved_chunk_bounds A c' k' WF0 Hc Hk) as (_ & _ & B3 & _) ]). pose proof (class_size_mod32 c' Hc) as CM.
      assert (ABM : chunk_addr sb c' k' mod 8 = 0) by (apply (mod0_down _ 32 8); [exists 4; reflexivity| exact B3]).
      assert (CSM : class_size c' mod 8 = 0) by (apply (mod0_down _ 32 8); [exists 4; reflexivity| exact CM]).
      replace (chunk_addr sb c' k' + class_size c' - chunk_addr sb c' k') with (class_size c') by lia.
      split; [exact E|]. split; [intros z Hz; apply HS; lia|]. split; [unfold kHighShadowMapBeg in HR; lia|]. split; [exact ABM|]. rewrite Z.add_mod, ABM, CSM by lia. reflexivity.
    - unfold carved in C. (first [ pose proof ((sec_shadow _ C)) as dR_93; dand3 dR_93 as E HS HR | pose proof (sec_shadow _ C) as (E & HS & HR) ]). cbn [chunk_lo chunk_hi cs_map cs_n] in *.
      (first [ pose proof ((sec_chunk_bounds A _ WF0 C)) as dR_94; dand3 dR_94 as _ B2 _ | pose proof (sec_chunk_bounds A _ WF0 C) as (_ & B2 & _) ]). cbn [cs_map cs_n] in B2. pose proof (map_size_page n1) as MP. unfold kPageSize in MP.
      assert (M8 : mb mod 8 = 0) by (apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact B2]).
      assert (S8 : map_size n1 mod 8 = 0) by (apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact MP]).
      replace (mb + map_size n1 - mb) with (map_size n1) by lia.
      split; [exact E|]. split; [intros z Hz; apply HS; lia|]. split; [exact HR|]. split; [exact M8|]. rewrite Z.add_mod, M8, S8 by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma carved_shadows_disjoint : forall ch1 ch2, carved ch1 -> carved ch2 -> ch1 <> ch2 ->
    sh (chunk_hi sb ch1) <= sh (chunk_lo sb ch2) \/ sh (chunk_hi sb ch2) <= sh (chunk_lo sb ch1).
  Proof.
    intros ch1 ch2 C1 C2 NE. destruct (carved_disjoint ch1 ch2 C1 C2 NE) as [D|D]; [left| right]; apply sh_mono; exact D.
  Qed.

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
    intros c' Hc. cbv zeta. pose proof (region_piece_bounds A c' WF0 Hc) as RB. cbv zeta in RB. change (a_sb A) with sb in *.
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
    - intros k Hk. (first [ pose proof ((carved_chunk_bounds A c' k WF0 Hc Hk)) as dR_96; dand4 dR_96 as B1 B2 B3 _ | pose proof (carved_chunk_bounds A c' k WF0 Hc Hk) as (B1 & B2 & B3 & _) ]). cbv zeta in *. change (a_sb A) with sb in *.
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
      - (first [ pose proof ((wfR A WF0)) as dR_97; dand3 dR_97 as WR _ _ | destruct (wfR A WF0) as (WR & _ & _) ]). (first [ pose proof ((WR c' Hc)) as dR_98; dand10 dR_98 as _ _ _ _ _ _ _ _ FR _ | destruct (WR c' Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & FR & _) ]). exact (FR k F).
      - (first [ pose proof ((wfC A WF0)) as dR_99; dand3 dR_99 as WC _ _ | destruct (wfC A WF0) as (WC & _ & _) ]). (first [ pose proof ((WC c' ltac:(lia))) as dR_100; dand4 dR_100 as _ _ CR' _ | destruct (WC c' ltac:(lia)) as (_ & _ & CR' & _) ]). exact (CR' k C).
      - subst c'. exact (batch_idx_range k B). }
    apply chunk_shadow_P; [exact Hc| exact Hk| exact AG| | exact (S1 c' k Hc ST)].
    unfold pshadow_free, fa8. rewrite repeat_length. pose proof (class_size_range c' Hc). rewrite Z2Nat.id by (apply Z.div_pos; lia). reflexivity.
  Qed.

  Lemma shadow_live_P : forall u c' k n1, a_livemap A !! u = Some (LI (ChP (CP c' k)) n1) ->
    (forall z, sh (chunk_addr sb c' k) <= z < sh (chunk_addr sb c' k) + class_size c' / 8 -> v' (wz z) = v (wz z)) ->
    bytes_at rsegs v' (sh (chunk_addr sb c' k)) (pshadow_live c' n1).
  Proof.
    intros u c' k n1 Hl AG. (first [ pose proof ((ar_shadow _ _ _ _ _ R)) as dR_101; dand3 dR_101 as _ S2 _ | pose proof (ar_shadow _ _ _ _ _ R) as (_ & S2 & _) ]).
    pose proof (known_live u _ Hl) as CL. unfold known in CL. cbn [li_chunk li_n] in CL. (first [ dand4 CL as Hc Hk Hn Hcl | destruct CL as (Hc & Hk & Hn & Hcl) ]).
    apply chunk_shadow_P; [exact Hc| exact Hk| exact AG| apply pshadow_live_length; [lia| exact Hcl]| exact (S2 u c' k n1 Hl)].
  Qed.

  Lemma shadow_quar_P : forall c' k n1, In (QE (ChP (CP c' k)) n1) (q_entries (a_qthread A ++ a_qglobal A)) ->
    (forall z, sh (chunk_addr sb c' k) <= z < sh (chunk_addr sb c' k) + class_size c' / 8 -> v' (wz z) = v (wz z)) ->
    bytes_at rsegs v' (sh (chunk_addr sb c' k)) (pshadow_quar c' n1).
  Proof.
    intros c' k n1 He AG. (first [ pose proof ((ar_shadow _ _ _ _ _ R)) as dR_103; dand4 dR_103 as _ _ S3 _ | pose proof (ar_shadow _ _ _ _ _ R) as (_ & _ & S3 & _) ]).
    pose proof (known_quar _ He) as CL. unfold known in CL. cbn [qe_chunk qe_n] in CL. (first [ dand4 CL as Hc Hk Hn Hcl | destruct CL as (Hc & Hk & Hn & Hcl) ]).
    apply chunk_shadow_P; [exact Hc| exact Hk| exact AG| apply pshadow_quar_length; [lia| exact Hcl]| exact (S3 c' k n1 He)].
  Qed.

  Lemma shadow_tails_P : forall c', 1 <= c' <= 30 ->
    let Rg := a_reg A c' in let rb := region_beg sb c' in
    (forall z, sh (rb + rg_allocated_user Rg) <= z < sh (rb + rg_mapped_user Rg) -> v' (wz z) = v (wz z)) ->
    (forall z, sh (rb + kFreeArrayOffset) <= z < sh (rb + kFreeArrayOffset) + rg_mapped_fa Rg / 8 -> v' (wz z) = v (wz z)) ->
    fill_at rsegs v' (sh (rb + rg_allocated_user Rg)) ((rg_mapped_user Rg - rg_allocated_user Rg) / 8) kAsanHeapLeftRedzoneMagic /\
    fill_at rsegs v' (sh (rb + kFreeArrayOffset)) (rg_mapped_fa Rg / 8) kAsanHeapLeftRedzoneMagic.
  Proof.
    intros c' Hc. cbv zeta. intros AG1 AG2. (first [ pose proof ((ar_shadow _ _ _ _ _ R)) as dR_105; dand5 dR_105 as _ _ _ S4 _ | pose proof (ar_shadow _ _ _ _ _ R) as (_ & _ & _ & S4 & _) ]). destruct (S4 c' Hc) as [X Y]. cbv zeta in X, Y.
    change (a_sb A) with sb in *. (first [ pose proof ((region_tail_shadow c' Hc)) as dR_106; dand4 dR_106 as E1 E1' E2 _ | pose proof (region_tail_shadow c' Hc) as (E1 & E1' & E2 & _) ]). cbv zeta in E1, E2.
    (first [ pose proof ((region_piece_bounds A c' WF0 Hc)) as dR_107; dand6 dR_107 as _ _ R3 _ R5 _ | pose proof (region_piece_bounds A c' WF0 Hc) as (_ & _ & R3 & _ & R5 & _) ]).
    split.
    - eapply fill_at_agree; [exact X|]. intros i Hi. apply AG1. lia.
    - eapply fill_at_agree; [exact Y|]. intros i Hi. apply AG2. pose proof (Z.div_pos (rg_mapped_fa (a_reg A c')) 8). lia.
  Qed.

  Lemma shadow_seclive_P : forall u mb n1, a_livemap A !! u = Some (LI (ChS (CS mb n1)) n1) ->
    (forall z, sh mb <= z < sh mb + map_size n1 / 8 -> v' (wz z) = v (wz z)) ->
    bytes_at rsegs v' (sh mb) (sshadow_live n1).
  Proof.
    intros u mb n1 Hl AG. (first [ pose proof ((ar_shadow _ _ _ _ _ R)) as dR_108; dand6 dR_108 as _ _ _ _ S5 _ | pose proof (ar_shadow _ _ _ _ _ R) as (_ & _ & _ & _ & S5 & _) ]).
    pose proof (known_live u _ Hl) as CL. unfold known in CL. cbn [li_chunk li_n] in CL. (first [ dand3 CL as Hin Hn _ | destruct CL as (Hin & Hn & _) ]).
    eapply bytes_at_agree_gen; [exact (S5 u mb n1 Hl)|]. rewrite sshadow_live_length by lia. intros i Hi. apply AG. lia.
  Qed.

  Lemma shadow_secquar_P : forall mb n2 n1, In (QE (ChS (CS mb n2)) n1) (q_entries (a_qthread A ++ a_qglobal A)) ->
    (forall z, sh mb <= z < sh mb + map_size n1 / 8 -> v' (wz z) = v (wz z)) ->
    bytes_at rsegs v' (sh mb) (sshadow_quar n1).
  Proof.
    intros mb n2 n1 He AG. (first [ pose proof ((ar_shadow _ _ _ _ _ R)) as dR_110; dand6 dR_110 as _ _ _ _ _ S6 | pose proof (ar_shadow _ _ _ _ _ R) as (_ & _ & _ & _ & _ & S6) ]).
    pose proof (known_quar _ He) as CL. unfold known in CL. cbn [qe_chunk qe_n] in CL. (first [ dand3 CL as Hin Hn -> | destruct CL as (Hin & Hn & ->) ]).
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
        - (first [ pose proof ((wfR A WF0)) as dR_112; dand3 dR_112 as WR _ _ | destruct (wfR A WF0) as (WR & _ & _) ]). (first [ pose proof ((WR c' Hc)) as dR_113; dand10 dR_113 as _ _ _ _ _ _ _ _ FR _ | destruct (WR c' Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & FR & _) ]). exact (FR k F).
        - (first [ pose proof ((wfC A WF0)) as dR_114; dand3 dR_114 as WC _ _ | destruct (wfC A WF0) as (WC & _ & _) ]). (first [ pose proof ((WC c' ltac:(lia))) as dR_115; dand4 dR_115 as _ _ CR' _ | destruct (WC c' ltac:(lia)) as (_ & _ & CR' & _) ]). exact (CR' k C).
        - subst c'. exact (batch_idx_range k B). }
      intros z Hz. apply AG. exact (proj1 (proj2 (chunk_shadow c' k Hc Hk)) z Hz).
    - intros u c' k n1 Hl. apply (shadow_live_P u); [exact Hl|].
      pose proof (known_live u _ Hl) as CL. unfold known in CL. cbn [li_chunk li_n] in CL. (first [ dand3 CL as Hc Hk _ | destruct CL as (Hc & Hk & _) ]).
      intros z Hz. apply AG. exact (proj1 (proj2 (chunk_shadow c' k Hc Hk)) z Hz).
    - intros c' k n1 He. apply shadow_quar_P; [exact He|].
      pose proof (known_quar _ He) as CL. unfold known in CL. cbn [qe_chunk qe_n] in CL. (first [ dand3 CL as Hc Hk _ | destruct CL as (Hc & Hk & _) ]).
      intros z Hz. apply AG. exact (proj1 (proj2 (chunk_shadow c' k Hc Hk)) z Hz).
    - intros c' Hc. apply shadow_tails_P; [exact Hc| |]; intros z Hz; apply AG.
      + exact (proj1 (proj2 (proj2 (proj2 (region_tail_shadow c' Hc)))) z Hz).
      + exact (proj1 (proj2 (proj2 (proj2 (proj2 (region_tail_shadow c' Hc))))) z Hz).
    - intros u mb n1 Hl. apply (shadow_seclive_P u); [exact Hl|].
      pose proof (known_live u _ Hl) as CL. unfold known in CL. cbn [li_chunk li_n] in CL. destruct CL as (Hin & _).
      intros z Hz. apply AG. exact (proj1 (proj2 (sec_shadow _ Hin)) z Hz).
    - intros mb n2 n1 He. apply (shadow_secquar_P mb n2); [exact He|].
      pose proof (known_quar _ He) as CL. unfold known in CL. cbn [qe_chunk qe_n] in CL. (first [ dand3 CL as Hin _ -> | destruct CL as (Hin & _ & ->) ]).
      intros z Hz. apply AG. exact (proj1 (proj2 (sec_shadow _ Hin)) z Hz).
  Qed.
End Transport.
