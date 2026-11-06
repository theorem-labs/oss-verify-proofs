(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocInv_defs MallocInv_heap MallocInv_word MallocInv_sep MallocInv_wf
  MallocInv_steps MallocInv_repw MallocInv_env MallocInv_vm MallocInv_coh MallocInv_ops MallocInv_live MallocInv_ameta_iface MallocInv_ntfree.
Import ListNotations.
Local Open Scope Z_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record ntframe (A : astate) (s s' : mstate) : Prop := {
  nf_lo : ms_lo s' = ms_lo s;
  nf_hi : ms_hi s' = ms_hi s;
  nf_vm : ms_vm s' = ms_vm s;
  nf_mem : forall a : word, ~ owned_of A (bv_unsigned a) -> ms_mem s' a = ms_mem s a;
  nf_live : forall p n (a : word), a_live A p = Some n -> p <= bv_unsigned a < p + n -> ms_mem s' a = ms_mem s a;
  nf_mapped : forall a : word, ms_mem s a <> None -> ms_mem s' a <> None
}.

Lemma ntframe_refl : forall A s, ntframe A s s.
Proof. intros A s. constructor; auto. Qed.

Lemma ntframe_trans : forall A A' s s' s'',
  ntframe A s s' -> ntframe A' s' s'' ->
  (forall x, owned_of A' x -> owned_of A x) -> a_live A' = a_live A ->
  ntframe A s s''.
Proof.
  intros A A' s s' s'' [L1 H1 V1 M1 P1 Q1] [L2 H2 V2 M2 P2 Q2] Ho Hl. constructor.
  - rewrite L2. exact L1.
  - rewrite H2. exact H1.
  - rewrite V2. exact V1.
  - intros a Ha. rewrite M2 by (intros Ho'; exact (Ha (Ho _ Ho'))). apply M1. exact Ha.
  - intros p n a Hp Hi. rewrite (P2 p n a ltac:(rewrite Hl; exact Hp) Hi). exact (P1 p n a Hp Hi).
  - intros a Ha. apply Q2. apply Q1. exact Ha.
Qed.

(* [comment removed for export] *)
Record ntrel (A A' : astate) (ma : Z) (slots : list slot_st) (i : Z) : Prop := {
  nr_live : a_live A' = a_live A;
  nr_areas : a_areas A' = a_areas A;
  nr_pages : a_pages A' = a_pages A;
  nr_mblocks : a_mblocks A' = a_mblocks A;
  nr_ctx : forall k, nt_ctx_kept k -> a_ctx A' k = a_ctx A k;
  nr_act : forall c, ~ (0 <= c < 48) -> a_active A' c = a_active A c;
  nr_groups : nt_groups A A' ma slots i;
  nr_dom : forall x, dom A' x -> dom A x;
  (* [comment removed for export] *)
  nr_fl : exists l, a_freelist A' = a_freelist A ++ l
}.

(* [comment removed for export] *)
Record fgrel (A1 A' : astate) (ma : Z) : Prop := {
  fg_live : a_live A' = a_live A1;
  fg_areas : a_areas A' = a_areas A1;
  fg_pages : a_pages A' = a_pages A1;
  fg_mblocks : a_mblocks A' = a_mblocks A1;
  fg_ctx : forall k, nt_ctx_kept k -> a_ctx A' k = a_ctx A1 k;
  fg_act : forall c, ~ (0 <= c < 48) -> a_active A' c = a_active A1 c;
  fg_groups : forall x mtx aibx slx, a_meta A' x = Some mtx -> mt_role mtx = RGroup aibx slx ->
     x <> ma /\ exists mt0 sl0, a_meta A1 x = Some mt0 /\ mt_role mt0 = RGroup aibx sl0 /\
       mt_w32 mt0 = mt_w32 mtx /\ mt_mem mt0 = mt_mem mtx /\
       (slx = sl0 \/ exists j ch, nth_error sl0 j = Some (SNested ch) /\ slx = list_set sl0 j SIdle);
  fg_dom : forall x, dom A' x -> dom A1 x;
  fg_fl : exists l, a_freelist A' = a_freelist A1 ++ l
}.

(* [comment removed for export] *)
Definition nt_res (A A' : astate) (h : VmMaps) (r : word * word) : Prop :=
  (r = (w0, w0) /\ a_xmaps A' = a_xmaps A /\ (forall x, dom A x -> dom A' x))
  \/ (exists B L, r = (Z_to_bv 64 B, Z_to_bv 64 L) /\ 0 < L /\ page_aligned B /\ L mod 4096 = 0 /\
        heap_range B (B + L) /\
        a_xmaps A' = (B, L) :: a_xmaps A /\
        In (Z_to_bv 64 B, Z_to_bv 64 L) (vm_maps h) /\
        (forall x, dom A x <-> dom A' x \/ B <= x < B + L) /\
        (forall x, B <= x < B + L -> ~ dom A' x) /\
        (forall f x, has A' f -> f_a f <= x < f_a f + f_n f -> ~ (B <= x < B + L)) /\
        WF (set_xmaps A' (a_xmaps A)) /\
        VMok (set_xmaps A' (a_xmaps A)) (vm_munmap (Z_to_bv 64 B) (Z_to_bv 64 L) h)).

Definition ntpost (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (D : list Z)
    (A : astate) (s : mstate) (ma : Z) (slots : list slot_st) (i : Z) : word * word -> mstate -> Prop :=
  fun r s' => exists A', II sp0 argv envp cb D A' s' /\ ntframe A s s' /\ ntrel A A' ma slots i /\ nt_res A A' (ms_vm s) r.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wfree_dec : forall ws x, wfree ws x \/ exists w, In w ws /\ f_a w <= x < f_a w + f_n w.
Proof.
  intros ws x. induction ws as [|w ws IH].
  - left. apply wfree_nil.
  - destruct (Z.lt_ge_cases x (f_a w)) as [H | H].
    + destruct IH as [IH | (w' & Hin & Hr)]; [left; apply wfree_cons; [llia | exact IH] | right; exists w'; split; [right; exact Hin | exact Hr]].
    + destruct (Z.lt_ge_cases x (f_a w + f_n w)) as [H' | H'].
      * right. exists w. split; [left; reflexivity | llia].
      * destruct IH as [IH | (w' & Hin & Hr)]; [left; apply wfree_cons; [llia | exact IH] | right; exists w'; split; [right; exact Hin | exact Hr]].
Qed.

Lemma dom_mzone : forall A x, WF A -> dom A x -> mzone x.
Proof.
  intros A x HW Hd. destruct (dom_heap A x HW Hd) as (lo & hi & Hh & Hx). unfold heap_range in Hh. unfold mzone. llia.
Qed.

Lemma ctx_mzone : forall k x, cvalid k -> caddr k <= x < caddr k + clen k -> mzone x.
Proof.
  intros k x Hk Hx. pose proof (ctx_slot_range k Hk) as (C1 & C2 & C3). unfold mzone, CTX, CTX_END in *. llia.
Qed.

(* [comment removed for export] *)
Definition writes_ok (A : astate) (ws : list fct) : Prop :=
  forall w x, In w ws -> f_a w <= x < f_a w + f_n w ->
    (dom A x \/ exists k, cvalid k /\ caddr k <= x < caddr k + clen k) /\
    (forall p n, a_live A p = Some n -> ~ (p <= x < p + n)).

Lemma writes_ok_nil : forall A, writes_ok A [].
Proof. intros A w x []. Qed.

Lemma writes_ok_cons : forall A w ws, writes_ok A ws ->
  (forall x, f_a w <= x < f_a w + f_n w ->
     (dom A x \/ exists k, cvalid k /\ caddr k <= x < caddr k + clen k) /\
     (forall p n, a_live A p = Some n -> ~ (p <= x < p + n))) ->
  writes_ok A (w :: ws).
Proof. intros A w ws H Hw w' x [<- | Hin] Hx; [apply Hw; exact Hx | apply (H w' x Hin Hx)]. Qed.

Lemma writes_ok_app : forall A ws1 ws2, writes_ok A ws1 -> writes_ok A ws2 -> writes_ok A (ws1 ++ ws2).
Proof. intros A ws1 ws2 H1 H2 w x Hin Hx. apply in_app_iff in Hin. destruct Hin as [Hin | Hin]; [apply (H1 w x Hin Hx) | apply (H2 w x Hin Hx)]. Qed.

(* [comment removed for export] *)
Lemma live_payload_dom : forall A ma mt aib slots j off n x, WF A ->
  a_meta A ma = Some mt -> mt_role mt = RGroup aib slots -> 0 <= j -> nth_error slots (Z.to_nat j) = Some (SLive off n) ->
  slot_start mt j + 16 * off <= x < slot_start mt j + 16 * off + n -> dom A x.
Proof.
  intros A ma mt aib slots j off n x HW Hma Hr Hj0 Hj Hx.
  destruct (live_geom A HW ma mt aib slots j off n Hma Hr Hj0 Hj) as (q & _ & Hn & _ & _ & _ & _ & G1 & G2 & G3 & G4 & _).
  pose proof (round16_ge n). apply (grp_dom A ma mt aib slots x HW Hma Hr). llia.
Qed.

Lemma live_dom : forall A p n x, WF A -> a_live A p = Some n -> p <= x < p + n -> dom A x.
Proof.
  intros A p n x HW Hp Hx. apply (proj1 (wf_live_map A HW p n)) in Hp.
  destruct Hp as (ma & mt & aib & slots & j & off & Hma & Hr & Hj0 & Hj & ->).
  exact (live_payload_dom A ma mt aib slots j off n x HW Hma Hr Hj0 Hj Hx).
Qed.

(* [comment removed for export] *)
Lemma writes_ok_ctx : forall A ws k v, WF A -> writes_ok A ws -> cvalid k -> writes_ok A (FCT (caddr k) (clen k) v :: ws).
Proof.
  intros A ws k v HW H Hk. apply writes_ok_cons; [exact H|]. cbn [f_a f_n]. intros x Hx. split; [right; exists k; auto|].
  intros p n Hp Hin. pose proof (live_dom A p n x HW Hp Hin) as Hd.
  pose proof (ctx_slot_range k Hk) as (C1 & C2 & C3).
  destruct (dom_heap A x HW Hd) as (lo & hi & Hh & Hlx). unfold heap_range, CTX_END in *. llia.
Qed.

Lemma IS_commit : forall sp0 argv envp cb A A' s ws m,
  IS sp0 argv envp cb A s -> RepW A (ms_mem s) ws m -> writes_ok A ws -> WF A' -> Rep A' m ->
  IS sp0 argv envp cb A' (upd s m (ms_vm s)).
Proof.
  intros sp0 argv envp cb A A' s ws m HI RW WO HW' HR'. pose proof (is_wf _ _ _ _ _ _ HI) as HW. pose proof (is_rep _ _ _ _ _ _ HI) as HR.
  apply (IS_mem sp0 argv envp cb A A' s m HI HW' HR').
  - intros a. destruct (wfree_dec ws (bv_unsigned a)) as [Hf | (w & Hin & Hx)].
    + left. exact (rw_frame A (ms_mem s) ws m RW a Hf).
    + right. destruct (proj1 (WO w (bv_unsigned a) Hin Hx)) as [Hd | (k & Hk & Hkx)]; [exact (dom_mzone A _ HW Hd) | exact (ctx_mzone k _ Hk Hkx)].
  - intros a Ha. destruct (wfree_dec ws (bv_unsigned a)) as [Hf | (w & Hin & Hx)].
    + left. rewrite <- (rw_frame A (ms_mem s) ws m RW a Hf). exact Ha.
    + destruct (proj1 (WO w (bv_unsigned a) Hin Hx)) as [Hd | (k & Hk & Hkx)].
      * left. rewrite <- (Z_to_bv_bv_unsigned 64 a). exact (rep_dom A (ms_mem s) HR _ Hd).
      * right; left. pose proof (ctx_slot_range k Hk) as (C1 & C2 & C3). pose proof ctx_block_rw. llia.
Qed.

Lemma ntframe_commit : forall A s ws m,
  WF A -> RepW A (ms_mem s) ws m -> writes_ok A ws -> ntframe A s (upd s m (ms_vm s)).
Proof.
  intros A s ws m HW RW WO. constructor; cbn [ms_lo ms_hi ms_vm ms_mem upd]; try reflexivity.
  - intros a Ho. apply (rw_frame A (ms_mem s) ws m RW a). destruct (wfree_dec ws (bv_unsigned a)) as [Hf | (w & Hin & Hx)]; [exact Hf|].
    exfalso. apply Ho. destruct (proj1 (WO w (bv_unsigned a) Hin Hx)) as [Hd | (k & Hk & Hkx)]; [right; exact Hd | left].
    pose proof (ctx_slot_range k Hk) as (C1 & C2 & C3). llia.
  - intros p n a Hp Hi. apply (rw_frame A (ms_mem s) ws m RW a). destruct (wfree_dec ws (bv_unsigned a)) as [Hf | (w & Hin & Hx)]; [exact Hf|].
    exfalso. exact (proj2 (WO w (bv_unsigned a) Hin Hx) p n Hp Hi).
  - intros a Ha. exact (rw_mapped A (ms_mem s) ws m RW a Ha).
Qed.

(* [comment removed for export] *)
Lemma meta_dom_nolive : forall A x mt y, WF A -> a_meta A x = Some mt -> x <= y < x + 40 ->
  dom A y /\ (forall p n, a_live A p = Some n -> ~ (p <= y < p + n)).
Proof.
  intros A x mt y HW Hx Hy.
  destruct (proj1 (wf_meta_dom A HW x) ltac:(rewrite Hx; discriminate)) as (pg & k & Hpg & Hk & ->).
  pose proof (meta_addr_range pg k Hk) as Hmr.
  split; [left; exists pg; split; [exact Hpg | llia]|].
  intros p n Hp Hin. apply (proj1 (wf_live_map A HW p n)) in Hp.
  destruct Hp as (ma & mta & aib & slots & j & off & Hma & Hr & Hj0 & Hj & ->).
  destruct (live_geom A HW ma mta aib slots j off n Hma Hr Hj0 Hj) as (q & _ & Hn & _ & _ & _ & _ & G1 & G2 & G3 & G4 & _).
  pose proof (round16_ge n).
  destruct (wf_grp_root A HW ma mta aib slots Hma Hr) as (mr & mtr & aibr & slr & Hmr' & Hrr & Hml & Hlo & Hhi & _).
  destruct (wf_disj_area_grp A HW pg mr mtr aibr slr Hpg Hmr' Hrr Hml); llia.
Qed.

Lemma writes_ok_meta : forall A ws x mt d n v, WF A -> writes_ok A ws -> a_meta A x = Some mt -> 0 <= d -> d + n <= 40 ->
  writes_ok A (FCT (x + d) n v :: ws).
Proof.
  intros A ws x mt d n v HW H Hx Hd Hn. apply writes_ok_cons; [exact H|]. cbn [f_a f_n]. intros y Hy.
  destruct (meta_dom_nolive A x mt y HW Hx ltac:(llia)) as [H1 H2]. split; [left; exact H1 | exact H2].
Qed.

Lemma wlook_some_cov : forall ws x b, wlook ws x = Some b -> exists w, In w ws /\ f_a w <= x < f_a w + f_n w.
Proof.
  intros ws x b. induction ws as [|w ws IH]; [discriminate|]. cbn. destruct (wcov w x) eqn:E.
  - intros _. exists w. split; [left; reflexivity | apply wcov_spec; exact E].
  - intros H. destruct (IH H) as (w' & Hin & Hr). exists w'. split; [right; exact Hin | exact Hr].
Qed.

Lemma wlook_cov_some : forall ws w x, In w ws -> f_a w <= x < f_a w + f_n w -> wlook ws x <> None.
Proof.
  intros ws w x. induction ws as [|w' ws IH]; [intros [] |]. intros Hin Hx. cbn. destruct (wcov w' x) eqn:E; [discriminate|].
  destruct Hin as [<- | Hin]; [| exact (IH Hin Hx)]. apply wcov_false in E. exfalso. lia.
Qed.

(* [comment removed for export] *)
Lemma repw_commit2 : forall A A' m0 ws m,
  WF A' -> RepW A m0 ws m ->
  (forall f, has A' f -> has A f \/ (forall x, f_a f <= x < f_a f + f_n f -> wlook ws x <> None)) ->
  (forall x b, wlook ws x = Some b ->
      (exists y mt fl, a_meta A' y = Some mt /\ y + moff fl <= x < y + moff fl + mlen fl /\ b = byte_of (mt_f mt fl) (x - (y + moff fl))) \/
      (exists k, cvalid k /\ caddr k <= x < caddr k + clen k /\ b = byte_of (a_ctx A' k) (x - caddr k)) \/
      (forall f, has A' f -> ~ (f_a f <= x < f_a f + f_n f))) ->
  (forall x, dom A' x -> dom A x) ->
  Rep A' m.
Proof.
  intros A A' m0 ws m HW' RW Hf Hw Hd. apply (repw_final A A' m0 ws m RW); [| exact Hd].
  intros x b (f & Hfa & [Hx ->]). destruct (wlook ws x) as [b'|] eqn:E.
  - left. f_equal. destruct (Hw x b' E) as [(y & mt & fl & Hy & Hr & ->) | [(k & Hk & Hr & ->) | Hno]].
    + rewrite (fact_at_meta A' HW' f y mt fl x Hfa Hy Hx Hr). reflexivity.
    + rewrite (fact_at_ctx A' HW' f k x Hfa Hk Hx Hr). reflexivity.
    + exfalso. exact (Hno f Hfa Hx).
  - right. split; [reflexivity|]. destruct (Hf f Hfa) as [H | H]; [exists f; split; [exact H | split; [exact Hx | reflexivity]] |].
    exfalso. exact (H x Hx E).
Qed.

(* [comment removed for export] *)
Lemma II_intro : forall sp0 argv envp cb D A s,
  IS sp0 argv envp cb A s -> VMok A (ms_vm s) -> AvOK A -> UsOK A -> deads A D -> II sp0 argv envp cb D A s.
Proof. intros. constructor; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma AvOK_transfer : forall A A', AvOK A ->
  a_areas A' = a_areas A -> a_ctx A' KAmc = a_ctx A KAmc ->
  (forall x mt', a_meta A' x = Some mt' -> mt_role mt' = RAvail -> exists mt, a_meta A x = Some mt /\ mt_role mt = RAvail) ->
  AvOK A'.
Proof.
  intros A A' HA Ea Ec Hb x mt' Hx Hr. rewrite Ea, Ec. destruct (Hb x mt' Hx Hr) as (mt & Hx0 & Hr0). exact (HA x mt Hx0 Hr0).
Qed.

Lemma deads_transfer : forall A A' D, deads A D ->
  (forall x, (exists mt', a_meta A' x = Some mt' /\ mt_role mt' = RDead) <-> (exists mt, a_meta A x = Some mt /\ mt_role mt = RDead)) ->
  deads A' D.
Proof. intros A A' D HD H x. rewrite (H x). apply HD. Qed.

(* [comment removed for export] *)
Lemma UsOK_transfer : forall A A', UsOK A -> a_areas A' = a_areas A ->
  (forall sc, 0 <= sc < 48 -> a_ctx A' (KUsage sc) = a_ctx A (KUsage sc)) ->
  (forall sc x, meta_usage A' sc x = meta_usage A sc x) ->
  UsOK A'.
Proof.
  intros A A' HU Ea Hc Hm sc Hsc. rewrite (Hc sc Hsc), (usage_of_ext A A' sc Ea (Hm sc)). exact (HU sc Hsc).
Qed.

End WithLayout.
