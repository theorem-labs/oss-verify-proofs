(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState ITree RelSpec Nodes Decode.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim Monad MSafe STree Malloc Prog KInv KRemapDef.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Export KStep.
Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.

Ltac kl_open HK := destruct HK as [Kminv Kceil Khalt Kwf Kresv Krt Kstart Kgr Kme Kdis Kreg Kph Kgrv Kna].

Ltac nores := intros ? ? ? ? E__; first [discriminate E__ | inversion E__; subst; reflexivity].
Lemma minv_preserved' : forall n mo eff mo' evs,
  minv mo -> m_halted mo = None -> nstep n mo eff mo' evs ->
  (forall addr len prot flags, n = NMmap addr len prot flags -> mmap_noreserve_b (Z_to_bv 64 flags) = false) ->
  m_halted mo' = None /\ minv mo'.
Proof. intros. eapply minv_preserved; eauto. Qed.
Ltac splits := repeat match goal with |- _ /\ _ => split end.

Lemma nstep_brk_inv : forall req mo rsp mo' evs,
  nstep (NBrk req) mo rsp mo' evs ->
  let h := m_vmmaps mo in
  exists r, brk_r_ok mo (Z_to_bv 64 req) r = true
    /\ m_vmmaps mo' = brk_model_next h (Z_to_bv 64 req) r
    /\ mm_frame mo mo'
    /\ Nodes.strip rsp = mkEffectU r [] (brk_zeros (Z_to_bv 64 req) r (vm_brk h)) (brk_unmaps r (vm_brk h)) [] []
    /\ evs = [].
Proof.
  intros req mo rsp mo' evs (-> & (r & Hr & Hs & ->) & _) h. exists r. split; [exact Hr|]. split.
  - unfold with_brk_next. rewrite m_vmmaps_forget_vm_ranges, m_vmmaps_with_vmmaps. reflexivity.
  - split; [apply mm_frame_with_brk_next|]. auto.
Qed.

Lemma maps_subtract_ranges_nil : forall na, maps_subtract_ranges na [] = na.
Proof. reflexivity. Qed.

Lemma brk_model_next_query : forall h,
  let h' := brk_model_next h (Z_to_bv 64 0) (vm_brk h) in
  vm_reserved h' = vm_reserved h /\ vm_maps h' = vm_maps h /\ vm_noaccess h' = vm_noaccess h
  /\ vm_start_brk h' = vm_start_brk h /\ vm_brk h' = vm_brk h.
Proof.
  intros h. cbn [brk_model_next vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk].
  unfold brk_maps_next. rewrite Z.ltb_irrefl, andb_false_r. unfold brk_grants, brk_is_grow.
  change (w_is0 (Z_to_bv 64 0)) with true. cbn [negb andb app].
  rewrite brk_unmaps_same, maps_subtract_ranges_nil. repeat split; reflexivity.
Qed.

Lemma brk_r_ok_query : forall m r, brk_r_ok m (Z_to_bv 64 0) r = true -> r = vm_brk (m_vmmaps m).
Proof. intros m r H. unfold brk_r_ok in H. change (w_is0 (Z_to_bv 64 0)) with true in H. cbn [orb] in H. apply bv_eqb_eq in H. exact H. Qed.

Lemma brk_model_next_same : forall h req,
  let h' := brk_model_next h req (vm_brk h) in
  vm_reserved h' = vm_reserved h /\ vm_maps h' = vm_maps h /\ vm_noaccess h' = vm_noaccess h
  /\ vm_start_brk h' = vm_start_brk h /\ vm_brk h' = vm_brk h.
Proof.
  intros h req. cbn [brk_model_next vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk].
  unfold brk_maps_next. rewrite Z.ltb_irrefl, andb_false_r. unfold brk_grants, brk_is_grow. rewrite Z.ltb_irrefl, andb_false_r. cbn [app].
  rewrite brk_unmaps_same, maps_subtract_ranges_nil. repeat split; reflexivity.
Qed.

Lemma brk_model_next_grown : forall h req,
  let b := bv_unsigned (vm_brk h) in
  0 < b -> b < req < 2^64 ->
  let h' := brk_model_next h (Z_to_bv 64 req) (Z_to_bv 64 req) in
  vm_reserved h' = vm_reserved h
  /\ vm_maps h' = (vm_brk h, Z_to_bv 64 (req - b)) :: vm_maps h
  /\ vm_noaccess h' = vm_noaccess h
  /\ vm_start_brk h' = vm_start_brk h /\ vm_brk h' = Z_to_bv 64 req.
Proof.
  intros h req b Hb Hreq h'. subst h'. cbn [brk_model_next vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk].
  unfold brk_maps_next. rewrite unsigned_lit by lia. fold b.
  replace (0 <? b) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (req <? b) with false by (symmetry; apply Z.ltb_ge; lia). cbn [andb].
  unfold brk_grants, brk_is_grow. rewrite w_is0_lit by lia. replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite unsigned_lit by lia. fold b. replace (0 <? b) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (b <? req) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb andb app].
  unfold brk_unmaps, brk_page_range. rewrite unsigned_lit by lia. fold b.
  replace (page_round_up_Z req <? page_round_up_Z b) with false.
  2:{ symmetry. apply Z.ltb_ge. apply page_round_up_Z_mono. lia. }
  assert (Hsub : (Z_to_bv 64 req - vm_brk h)%bv = Z_to_bv 64 (req - b)).
  { apply bv_eq. rewrite bv_sub_unsigned, unsigned_lit by lia. fold b. rewrite Z_to_bv_unsigned. reflexivity. }
  rewrite Hsub. destruct (0 <? b); rewrite maps_subtract_ranges_nil; repeat split; reflexivity.
Qed.

Lemma brk_r_ok_grow : forall m req r,
  let h := m_vmmaps m in
  let b := bv_unsigned (vm_brk h) in
  bv_unsigned (vm_start_brk h) <= b -> b < req < 2^64 ->
  brk_r_ok m (Z_to_bv 64 req) r = true ->
  (r = vm_brk h) \/ (r = Z_to_bv 64 req /\ brk_grow_ok m (Z_to_bv 64 req) (Z_to_bv 64 req) = true).
Proof.
  intros m req r h b Hs Hreq H. pose proof (bv_unsigned_in_range 64 (vm_brk h)) as Hr0. unfold bv_modulus in Hr0. fold b in Hr0.
  unfold brk_r_ok in H. fold h in H. rewrite w_is0_lit in H by lia.
  replace (req =? 0) with false in H by (symmetry; apply Z.eqb_neq; lia).
  unfold min_brk in H. rewrite unsigned_lit in H by lia.
  replace (req <? bv_unsigned (vm_start_brk h)) with false in H by (symmetry; apply Z.ltb_ge; lia).
  fold b in H. replace (req <? b) with false in H by (symmetry; apply Z.ltb_ge; lia). cbn [orb] in H.
  apply andb_prop in H as [H1 H2]. apply orb_prop in H1 as [H1|H1]; apply bv_eqb_eq in H1; subst r; [right|left]; auto.
Qed.

Lemma brk_grow_ok_facts : forall m req,
  let h := m_vmmaps m in
  let b := bv_unsigned (vm_brk h) in
  0 < b -> b < req < 2^64 -> b mod 4096 = 0 -> req mod 4096 = 0 ->
  brk_grow_ok m (Z_to_bv 64 req) (Z_to_bv 64 req) = true ->
  req <= alloc_top h /\ region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 b) (Z_to_bv 64 (req + 4096 - b)) = true.
Proof.
  intros m req h b Hb Hreq Hba Hra H. unfold brk_grow_ok, brk_budget_ok in H. fold h in H. rewrite unsigned_lit in H by lia. fold b in H.
  replace (0 <? b) with true in H by (symmetry; apply Z.ltb_lt; lia).
  replace (b <? req) with true in H by (symmetry; apply Z.ltb_lt; lia). cbn [andb] in H.
  unfold page_round_up_Z in H. rewrite page_size_eq in H.
  replace ((b + 4096 - 1) / 4096 * 4096) with b in H.
  2:{ pose proof (Z_div_mod_eq_full b 4096). pose proof (Z_div_mod_eq_full (b+4096-1) 4096). pose proof (Z.mod_pos_bound (b+4096-1) 4096). nia. }
  replace ((req + 4096 - 1) / 4096 * 4096) with req in H.
  2:{ pose proof (Z_div_mod_eq_full req 4096). pose proof (Z_div_mod_eq_full (req+4096-1) 4096). pose proof (Z.mod_pos_bound (req+4096-1) 4096). nia. }
  replace (b <? req) with true in H by (symmetry; apply Z.ltb_lt; lia).
  apply andb_prop in H as [H _]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. split; [exact H1|].
  match type of H2 with region_free _ _ (Z_to_bv 64 ?x) = true => replace x with (req + 4096 - b) in H2 by (rewrite ?page_size_eq; lia) end. exact H2.
Qed.

Lemma nstep_mmap_fixed_inv : forall a mo rsp mo' evs,
  let h := m_vmmaps mo in
  let aw := Z_to_bv 64 a in let n := Z_to_bv 64 PGSZ in
  0 <= a -> a + PGSZ <= alloc_top h -> a mod 4096 = 0 ->
  region_free (vm_reserved h) aw n = true -> map_contains (vm_maps h) aw n = true ->
  nstep (NMmap a PGSZ PROT_NONE MAPFX) mo rsp mo' evs ->
  evs = [] /\ mm_frame mo mo' /\
  exists x, dec_mmap_fixed a PGSZ rsp = Some x /\
  match x with
  | FxKept e => False
  | FxDone => m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (vm_maps h) ((aw, n) :: maps_subtract (vm_noaccess h) (bv_unsigned aw) (bv_unsigned aw + bv_unsigned n))
                                         (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
  | FxLost e => False
  end.
Proof.
  intros a mo rsp mo' evs h aw n Ha Hc Hal Hrf Hmc H.
  pose proof (alloc_top_lt64 h) as Hcl.
  assert (NR : forall addr len prot flags, NMmap a PGSZ PROT_NONE MAPFX = NMmap addr len prot flags -> mmap_noreserve_b (Z_to_bv 64 flags) = false).
  { intros ? ? ? ? E. inversion E; subst. reflexivity. }
  pose proof (nstep_mm_frame (NMmap a PGSZ PROT_NONE MAPFX) mo rsp mo' evs I) as MMF.
  destruct H as [-> H]. split; [reflexivity|]. cbv zeta in H.
  rewrite (unsigned_lit PGSZ) in H by (unfold PGSZ; lia). change (page_round_up_Z PGSZ) with PGSZ in H. fold aw n h in H.
  destruct H as [(e & He & Hs & ->)|[(Hm & _)|[(_ & Hm & _)|(_ & _ & _ & HX)]]].
  - exfalso. apply mmap_errnos_when_In in He as [He _]. revert He. unfold nmmap_refusable. vm_compute. discriminate.
  - exfalso. revert Hm. vm_compute. discriminate.
  - exfalso. revert Hm. vm_compute. discriminate.
  - destruct HX as [(Hs & ->)|(e & He & Hs & ->)].
    + split. { apply mm_frame_with_mmap_replacement; [reflexivity| apply mm_frame_with_vmmaps; reflexivity]. }
      exists FxDone. split.
      * destruct rsp as [r ws zs us cs ci]. rewrite strip_mk in Hs. inversion Hs; subst. unfold dec_mmap_fixed.
        change (mmap_len PGSZ) with PGSZ. subst aw n. rewrite !bv_eqb_refl. cbn [andb].
        rewrite errno_of_lit by (unfold PGSZ in *; lia). reflexivity.
      * unfold with_mmap_replacement. rewrite with_mmap_backing_noreserve_false by reflexivity.
        rewrite m_vmmaps_vm_forget_range, m_vmmaps_with_vmmaps. reflexivity.
    + exfalso. exact (mmap_destructive_errnos_In _ He).
Qed.

Lemma iv_subtract_piece : forall a sz lo hi e, In e (iv_subtract a sz lo hi) ->
  bv_unsigned a < bv_unsigned a + bv_unsigned sz <= 2^64 ->
  bv_unsigned a <= elo e /\ ehi e <= bv_unsigned a + bv_unsigned sz /\ elo e < ehi e /\ (ehi e <= lo \/ hi <= elo e)
  /\ (elo e = bv_unsigned a \/ elo e = hi).
Proof.
  intros a sz lo hi e Hin WF. unfold elo, ehi. pose proof (bv_unsigned_in_range 64 a) as Ha. pose proof (bv_unsigned_in_range 64 sz) as Hs.
  unfold bv_modulus in *. change (2 ^ Z.of_N 64) with (2^64) in *.
  unfold iv_subtract in Hin. destruct (Z.ltb_spec (bv_unsigned a) lo); destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); cbn [app] in Hin;
    repeat (destruct Hin as [<-|Hin]); try contradiction; cbn [fst snd];
    try (pose proof (Z.le_max_l (bv_unsigned a) hi); pose proof (Z.le_max_r (bv_unsigned a) hi); pose proof (Z.max_spec (bv_unsigned a) hi));
    try (pose proof (Z.le_min_l (bv_unsigned sz) (lo - bv_unsigned a)); pose proof (Z.le_min_r (bv_unsigned sz) (lo - bv_unsigned a)); pose proof (Z.min_spec (bv_unsigned sz) (lo - bv_unsigned a)));
    rewrite ?unsigned_lit; lia.
Qed.

Lemma maps_subtract_piece : forall l lo hi e, (forall e0, In e0 l -> elo e0 < ehi e0 <= 2^64) -> In e (maps_subtract l lo hi) ->
  exists e0, In e0 l /\ elo e0 <= elo e /\ ehi e <= ehi e0 /\ elo e < ehi e /\ (ehi e <= lo \/ hi <= elo e) /\ (elo e = elo e0 \/ elo e = hi).
Proof.
  intros l lo hi e WF Hin. destruct (maps_subtract_In _ _ _ _ Hin) as ([a sz] & H0 & H1).
  pose proof (WF _ H0) as W0. unfold elo, ehi in W0. cbn [fst snd] in W0.
  destruct (iv_subtract_piece a sz lo hi e H1 W0) as (P1 & P2 & P3 & P4 & P5).
  exists (a, sz). unfold elo at 1 3. unfold ehi at 2. cbn [fst snd]. repeat split; auto; lia.
Qed.

Lemma kl_noacc_wf : forall L pbrk mo, KL L pbrk mo -> forall e, In e (vm_noaccess (m_vmmaps mo)) -> elo e < ehi e <= 2^64.
Proof.
  intros L pbrk mo HK e He. destruct (kl_noacc _ _ _ HK e He) as (NZ & e' & He' & A & B & _).
  pose proof (proj1 (kl_wf _ _ _ HK) e' He'). lia.
Qed.

Lemma KL_vm_eq : forall L pbrk mo mo',
  KL L pbrk mo -> minv mo' -> m_halted mo' = None ->
  vm_reserved (m_vmmaps mo') = vm_reserved (m_vmmaps mo) ->
  vm_maps (m_vmmaps mo') = vm_maps (m_vmmaps mo) ->
  vm_noaccess (m_vmmaps mo') = vm_noaccess (m_vmmaps mo) ->
  vm_start_brk (m_vmmaps mo') = vm_start_brk (m_vmmaps mo) ->
  vm_brk (m_vmmaps mo') = vm_brk (m_vmmaps mo) ->
  vm_init_sp (m_vmmaps mo') = vm_init_sp (m_vmmaps mo) ->
  KL L pbrk mo'.
Proof.
  intros L pbrk mo mo' K Hmi Hh H1 H2 H3 H4 H5 H6. kl_open K; constructor; unfold alloc_top in *; rewrite ?H1, ?H2, ?H3, ?H4, ?H5, ?H6; auto.
Qed.

Definition phase_inv (ph : brk_phase) (L : mled) (pbrk : Z) (mo : Model) : Prop :=
  match ph with
  | BPUntried => vm_brk (m_vmmaps mo) = vm_start_brk (m_vmmaps mo) /\ ld_brkreg L = None
  | BPQueried cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo))
      /\ bv_unsigned (vm_brk (m_vmmaps mo)) = cur /\ pbrk = cur /\ ld_brkreg L = None
  | BPGuard cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo))
      /\ bv_unsigned (vm_brk (m_vmmaps mo)) = cur + 2 * PGSZ /\ pbrk = cur + 2 * PGSZ
      /\ ld_brkreg L = None /\ cur + 2 * PGSZ <= ld_ceil L
      /\ (exists e, In e (vm_maps (m_vmmaps mo)) /\ elo e <= cur /\ cur + 2 * PGSZ <= ehi e)
      /\ (forall b l, In (b, l) (ld_groups L) -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
      /\ (forall b l k, In (b, l, k) (ld_metas L) -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
  | BPLive => exists b l, ld_brkreg L = Some (b, l) /\ bv_unsigned (vm_brk (m_vmmaps mo)) = b + l /\ pbrk = b + l
  | BPDead => True
  end.

Lemma KL_rephase : forall L ph pbrk pbrk' mo,
  KL L pbrk mo -> phase_inv ph L pbrk' mo -> KL (set_brkph ph L) pbrk' mo.
Proof. intros L ph pbrk pbrk' mo K Hph. kl_open K; constructor; cbn; auto. Qed.

Lemma KL_dead : forall L pbrk pbrk' mo, KL L pbrk mo -> KL (set_brkph BPDead L) pbrk' mo.
Proof. intros. eapply KL_rephase; [eassumption| exact I]. Qed.

Lemma ev_brk0_ok : forall L G s0, frame_ok G -> ld_brk L = BPUntried ->
  mspec (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ G s mo)
        (r <- msys (NBrk 0) dec_brk0 ;; mupd (set_brk_ps r) ;;; mret r)
        (ev_step_post L (EBrk 0) G s0).
Proof.
  intros L G s0 HG Hph.
  eapply mspec_bind.
  { apply (mspec_sys (NBrk 0) dec_brk0 _ (fun r s mo => s = s0 /\ G s mo /\ brk0_answer_ok r = true /\ KL (set_brkph (BPQueried r) L) r mo)).
    intros s mo (-> & HK & HGs). pose proof (KL_ceil_lt63 _ _ _ HK) as Hcl. split; [exact I|].
    intros rsp mo' evs Hst.
    pose proof (minv_preserved' _ _ _ _ _ (kl_minv _ _ _ HK) (kl_halt _ _ _ HK) Hst ltac:(nores)) as [Hh' Hmi'].
    pose proof (nstep_dec_brk0 _ _ _ _ Hst) as (_ & Hdec & Hvo & Hbrk).
    pose proof (nstep_brk_inv _ _ _ _ _ Hst) as (r & Hr & Emo' & _ & _).
    apply brk_r_ok_query in Hr. subst r.
    pose proof (brk_model_next_query (m_vmmaps mo)) as (E1 & E2 & E3 & E4 & E5).
    exists (bv_unsigned (vm_brk (m_vmmaps mo))). split; [exact Hdec|].
    assert (HK' : KL L (ps_brk s0) mo').
    { eapply KL_vm_eq; [exact HK| exact Hmi'| exact Hh'| | | | | |]; rewrite Emo'; cbn [m_vmmaps with_vmmaps]; first [assumption| reflexivity]. }
    pose proof (kl_phase _ _ _ HK') as Kph. rewrite Hph in Kph. destruct Kph as [Ebrk Ereg].
    pose proof (kl_start _ _ _ HK') as (S1 & S2 & S3 & S4).
    splits.
    - reflexivity.
    - eapply HG; [reflexivity|reflexivity| exact Hvo| exact HGs].
    - unfold brk0_answer_ok. rewrite <- Hbrk, Ebrk. pose proof (bv_unsigned_in_range 64 (vm_start_brk (m_vmmaps mo'))) as R. unfold bv_modulus in R.
      unfold TWO64. rewrite (proj2 (Z.ltb_lt 0 _)) by lia. rewrite S2, Z.eqb_refl. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
    - eapply KL_rephase; [exact HK'|]. cbn [phase_inv]. rewrite <- Hbrk, Ebrk. splits; auto. }
  intros r. cbn beta. eapply mspec_bind.
  { apply mspec_upd. }
  intros []. apply mspec_ret. intros s mo (s1 & -> & -> & HGs & Hans & HK). unfold ev_step_post. cbn [ps_brk set_brk_ps ps_m ps_fa ps_so answer_ok event_post Z.eqb].
  splits; auto. eapply (HG s0); [reflexivity|reflexivity| apply mm_frame_refl| exact HGs].
Qed.

Lemma mspec_get_bind_eq {St A} (s0 : St) (P : assn St) (f : St -> Monad.M St A) Q :
  mspec (fun s mo => s = s0 /\ P s mo) (f s0) Q -> mspec (fun s mo => s = s0 /\ P s mo) (x <- mget ;; f x) Q.
Proof. intros H s mo [-> HP]. unfold mbind, mget. cbn. apply H. auto. Qed.

Lemma elo_pair : forall a n, elo (a, n) = bv_unsigned a. Proof. reflexivity. Qed.
Lemma ehi_pair : forall a n, ehi (a, n) = bv_unsigned a + bv_unsigned n. Proof. reflexivity. Qed.

Lemma went_In_bounds : forall L pbrk mo b l, KL L pbrk mo ->
  (In (b, l) (ld_groups L) \/ exists k, In (b, l, k) (ld_metas L)) ->
  0 < b /\ 0 < mmap_len l /\ b + mmap_len l <= ld_ceil L /\ In (went b (mmap_len l)) (vm_maps (m_vmmaps mo))
  /\ elo (went b (mmap_len l)) = b /\ ehi (went b (mmap_len l)) = b + mmap_len l.
Proof.
  intros L pbrk mo b l K Hin. pose proof (KL_ceil_lt63 _ _ _ K).
  assert (0 < l < LEN_MAX /\ 0 < b /\ b + mmap_len l <= ld_ceil L /\ In (went b (mmap_len l)) (vm_maps (m_vmmaps mo))) as (Hl & Hb & Hc & Hm).
  { destruct Hin as [Hin|[k Hin]]; [pose proof (kl_groups _ _ _ K _ _ Hin)| pose proof (kl_metas _ _ _ K _ _ _ Hin)]; tauto. }
  pose proof (mmap_len_ge l ltac:(lia)). splits; auto; try lia.
  - apply elo_went. lia.
  - apply ehi_went; lia.
Qed.

Lemma In_lranges : forall L x, In x (lranges L) ->
  In x (ld_resv L)
  \/ (exists b l, In (b, l) (ld_groups L) /\ x = (b, round_up_pg l))
  \/ (exists b l k, In (b, l, k) (ld_metas L) /\ x = (b, round_up_pg l))
  \/ (exists b l, ld_brkreg L = Some (b, l) /\ x = (b + PGSZ, round_up_pg l - PGSZ)).
Proof.
  intros L x Hin. unfold lranges in Hin. rewrite !in_app_iff in Hin. destruct Hin as [H|[H|[H|H]]].
  - left; exact H.
  - right; left. apply in_map_iff in H as ([b l] & <- & H). exists b, l. auto.
  - right; right; left. apply in_map_iff in H as ([[b l] k] & <- & H). exists b, l, k. auto.
  - right; right; right. destruct (ld_brkreg L) as [[b l]|]; [|destruct H]. destruct H as [<-|[]]. exists b, l. auto.
Qed.

Lemma KL_lbrk_pages_ok : forall L pbrk mo lo len,
  KL L pbrk mo ->
  let h := m_vmmaps mo in
  0 < lo -> 0 < len -> lo + len <= ld_ceil L ->
  region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 lo) (Z_to_bv 64 len) = true ->
  (forall b l, ld_brkreg L = Some (b, l) -> l mod PGSZ = 0 /\ (b + l <= lo \/ lo + len <= b + PGSZ)) ->
  lbrk_pages_ok L lo len = true.
Proof.
  intros L pbrk mo lo len HK h Hlo Hlen Hceil Hrf Hbrk. pose proof (KL_ceil_lt63 _ _ _ HK) as Hcl.
  assert (Ulo : bv_unsigned (Z_to_bv 64 lo) = lo) by (apply unsigned_lit; lia).
  assert (Ulen : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
  pose proof (region_free_app_r _ _ _ _ Hrf) as Hrfm.
  unfold lbrk_pages_ok. rewrite (proj2 (Z.ltb_lt 0 lo)) by lia. rewrite (proj2 (Z.leb_le _ _) Hceil). cbn [andb].
  unfold ranges_free. apply List.forallb_forall. intros [b0 m0] Hin. cbn [fst snd]. unfold iv_disjoint.
  enough (lo + len <= b0 \/ b0 + m0 <= lo) as D.
  { destruct D as [D|D]; [rewrite (proj2 (Z.leb_le _ _) D); reflexivity| rewrite (proj2 (Z.leb_le _ _) D); apply orb_true_r]. }
  apply In_lranges in Hin as [H|[(b1 & l1 & H & E)|[(b1 & l1 & k & H & E)|(b1 & l1 & H & E)]]].
  - rewrite (kl_resv _ _ _ HK) in H. apply in_map_iff in H as ([e sz] & E & H). unfold wwZ in E. cbn [fst snd] in E. injection E as <- <-.
    pose proof (region_free_In _ _ _ _ _ Hrf (in_or_app _ _ _ (or_introl H))) as D. rewrite Ulo, Ulen in D. exact D.
  - injection E as -> ->. pose proof (went_In_bounds _ _ _ b1 l1 HK (or_introl H)) as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (region_free_disj _ _ _ _ Hrfm B4) as D. rewrite B5, B6, Ulo, Ulen in D. rewrite round_up_pg_eq. fold (mmap_len l1). exact D.
  - injection E as -> ->. pose proof (went_In_bounds _ _ _ b1 l1 HK (or_intror (ex_intro _ k H))) as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (region_free_disj _ _ _ _ Hrfm B4) as D. rewrite B5, B6, Ulo, Ulen in D. rewrite round_up_pg_eq. fold (mmap_len l1). exact D.
  - injection E as -> ->. destruct (Hbrk b1 l1 H) as [Al D]. rewrite round_up_pg_aligned by (unfold PGSZ in Al; exact Al). lia.
Qed.

Lemma ev_brk_grow1_ok : forall L G s0 cur, frame_ok G -> ld_brk L = BPQueried cur ->
  let req := round_up_pg cur + 2 * PGSZ in
  mspec (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ G s mo)
        (s <- mget ;; a <- msys (NBrk req) (dec_brk (ps_brk s) req) ;;
         match a with BrkGrown => mupd (set_brk_ps req) ;;; mret req | BrkSame => mret (ps_brk s) end)
        (ev_step_post L (EBrk req) G s0).
Proof.
  intros L G s0 cur HG Hph req.
  apply mspec_get_bind_eq.
  eapply mspec_bind.
  { apply (mspec_sys (NBrk req) (dec_brk (ps_brk s0) req) _
             (fun a s mo => s = s0 /\ G s mo /\ (req <> cur /\ 0 < req) /\ ps_brk s0 = cur /\
                match a with
                | BrkGrown => KL (set_brkph (BPGuard cur) L) req mo /\ lbrk_pages_ok L (round_up_pg cur) (2 * PGSZ) = true
                | BrkSame => KL (set_brkph BPDead L) cur mo
                end)).
    intros s mo (-> & HK & HGs). pose proof (KL_ceil_lt63 _ _ _ HK) as Hcl. split; [exact I|].
    intros rsp mo' evs Hst.
    pose proof (minv_preserved' _ _ _ _ _ (kl_minv _ _ _ HK) (kl_halt _ _ _ HK) Hst ltac:(nores)) as [Hh' Hmi'].
    pose proof (kl_phase _ _ _ HK) as Kph. rewrite Hph in Kph. destruct Kph as (Ecur & Ebrk & Epbrk & Ereg).
    pose proof (kl_start _ _ _ HK) as (S1 & S2 & S3 & S4).
    assert (Hreq : req = cur + 2 * PGSZ). { subst req. rewrite round_up_pg_aligned; [reflexivity|]. rewrite Ecur. exact S2. }
    pose proof (nstep_brk_inv _ _ _ _ _ Hst) as (r & Hr & Emo' & _ & _).
    pose proof (nstep_dec_brk req mo rsp mo' evs ltac:(lia) ltac:(lia) ltac:(unfold PGSZ in *; lia) Hst) as (_ & Hvo & a & Hdec & Ha).
    set (h := m_vmmaps mo) in *.
    rewrite Ebrk in Hdec. rewrite Epbrk. exists a. split; [exact Hdec|].
    split; [reflexivity|]. split; [eapply HG; [reflexivity|reflexivity| exact Hvo| exact HGs]|].
    split; [unfold PGSZ in *; lia|]. split; [reflexivity|].
    apply brk_r_ok_grow in Hr; fold h in Hr; [| fold h; lia| fold h; unfold PGSZ in *; lia].
    pose proof (brk_model_next_same h (Z_to_bv 64 req)) as (Q1 & Q2 & Q3 & Q4 & Q5).
    pose proof (brk_model_next_grown h req ltac:(lia) ltac:(unfold PGSZ in *; lia)) as (P1 & P2 & P3 & P4 & P5).
    destruct a.
    -
      destruct Hr as [-> | [-> Hgo]].
      { exfalso. rewrite Emo' in Ha. cbn [m_vmmaps with_vmmaps] in Ha. rewrite Q5 in Ha.
        apply (f_equal bv_unsigned) in Ha. rewrite unsigned_lit in Ha by (unfold PGSZ in *; lia). lia. }
      apply brk_grow_ok_facts in Hgo; fold h in Hgo; [| fold h; lia| fold h; unfold PGSZ in *; lia| fold h; rewrite Ebrk, Ecur; exact S2| rewrite Hreq, Ecur; unfold PGSZ in *; rewrite Z.add_mod, S2 by lia; reflexivity].
      destruct Hgo as [Hceil Hrf].
      replace (alloc_top h) with (ld_ceil L) in Hceil by (exact (kl_ceil _ _ _ HK)).
      apply (region_free_shrink _ _ _ (Z_to_bv 64 (req - bv_unsigned (vm_brk h)))) in Hrf; [| rewrite !unsigned_lit by (unfold PGSZ in *; lia); lia].
      assert (HPG : lbrk_pages_ok L (round_up_pg cur) (2 * PGSZ) = true).
      { rewrite round_up_pg_aligned by (rewrite Ecur; unfold PGSZ in S2; exact S2).
        apply (KL_lbrk_pages_ok L (ps_brk s0) mo cur (2 * PGSZ) HK); [lia| unfold PGSZ; lia| lia| | intros b l Hb; rewrite Ereg in Hb; discriminate].
        replace cur with (bv_unsigned (vm_brk h)) at 1 by exact Ebrk. replace (Z_to_bv 64 (2 * PGSZ)) with (Z_to_bv 64 (req - bv_unsigned (vm_brk h))) by (f_equal; lia). exact Hrf. }
      rewrite Z_to_bv_bv_unsigned in Hrf.
      assert (Hn : bv_unsigned (Z_to_bv 64 (req - bv_unsigned (vm_brk h))) = 2 * PGSZ) by (rewrite unsigned_lit; unfold PGSZ in *; lia).
      split; [|exact HPG].
      kl_open HK. constructor; rewrite ?Emo'; cbn [m_vmmaps with_vmmaps set_brkph ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live ld_ceil];
        rewrite ?P1, ?P2, ?P3, ?P4, ?P5; auto; try kl_ceil_close Kceil.
      + apply vmwf_cons; [exact Kwf| rewrite Hn; unfold PGSZ in *; lia| eapply region_free_app_r; exact Hrf].
      + rewrite unsigned_lit by (unfold PGSZ in *; lia). splits; try lia; auto.
      + intros b l Hin. specialize (Kgr b l Hin). unfold brk_disj in *. cbn. intuition auto with datatypes.
      + intros b l k Hin. specialize (Kme b l k Hin). unfold brk_disj in *. cbn. intuition auto with datatypes.
      + intros b l Hb. rewrite Ereg in Hb. discriminate.
      + rewrite unsigned_lit by (unfold PGSZ in *; lia). splits; auto; try lia.
        * exists (vm_brk h, Z_to_bv 64 (req - bv_unsigned (vm_brk h))). split; [left; reflexivity|]. rewrite elo_pair, ehi_pair, Hn. lia.
        * intros b l Hin. pose proof (went_In_bounds _ _ _ b l (mkKL _ _ _ Kminv Kceil Khalt Kwf Kresv Krt Kstart Kgr Kme Kdis Kreg Kph Kgrv Kna) (or_introl Hin)) as (B1 & B2 & B3 & B4 & B5 & B6).
          pose proof (region_free_disj _ _ _ _ (region_free_app_r _ _ _ _ Hrf) B4) as D. rewrite B5, B6, Hn in D. lia.
        * intros b l k Hin. pose proof (went_In_bounds _ _ _ b l (mkKL _ _ _ Kminv Kceil Khalt Kwf Kresv Krt Kstart Kgr Kme Kdis Kreg Kph Kgrv Kna) (or_intror (ex_intro _ k Hin))) as (B1 & B2 & B3 & B4 & B5 & B6).
          pose proof (region_free_disj _ _ _ _ (region_free_app_r _ _ _ _ Hrf) B4) as D. rewrite B5, B6, Hn in D. lia.
      + intros ee Hee. destruct (Kna ee Hee) as (Knz & ee' & Hee' & Kna1 & Kna2 & Kna3). split; [exact Knz|]. exists ee'. split; [right; exact Hee'|]. auto.
    -
      destruct Hr as [-> | [-> Hgo]].
      2:{ exfalso. rewrite Emo' in Ha. cbn [m_vmmaps with_vmmaps] in Ha. rewrite P5 in Ha.
          apply (f_equal bv_unsigned) in Ha. rewrite unsigned_lit in Ha by (unfold PGSZ in *; lia). lia. }
      apply KL_dead with (pbrk := ps_brk s0). eapply KL_vm_eq; [exact HK| exact Hmi'| exact Hh'| | | | | |]; rewrite Emo'; cbn [m_vmmaps with_vmmaps]; first [assumption| reflexivity]. }
  intros a. cbn beta. destruct a.
  - eapply mspec_bind; [apply mspec_upd|]. intros []. apply mspec_ret.
    intros s mo (s1 & -> & -> & HGs & [Hne Hpos] & Ecur & [HK HPG]). unfold ev_step_post.
    cbn [ps_brk set_brk_ps ps_m ps_fa ps_so answer_ok event_post].
    replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Hph, Z.eqb_refl.
    splits; auto.
    + unfold brk_answer_ok. rewrite Z.eqb_refl, HPG. reflexivity.
    + eapply (HG s0); [reflexivity|reflexivity| apply mm_frame_refl| exact HGs].
  - apply mspec_ret. intros s mo (-> & HGs & [Hne Hpos] & Ecur & HK). unfold ev_step_post.
    cbn [answer_ok event_post].
    replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Hph, Ecur.
    replace (cur =? req) with false by (symmetry; apply Z.eqb_neq; lia).
    splits; auto. unfold brk_answer_ok. rewrite Z.eqb_refl, orb_true_r. reflexivity.
Qed.

Lemma ev_brk_grow2_ok : forall L G s0 b l, frame_ok G -> ld_brk L = BPLive -> ld_brkreg L = Some (b, l) ->
  let req := b + l + PGSZ in
  mspec (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ G s mo)
        (s <- mget ;; a <- msys (NBrk req) (dec_brk (ps_brk s) req) ;;
         match a with BrkGrown => mupd (set_brk_ps req) ;;; mret req | BrkSame => mret (ps_brk s) end)
        (ev_step_post L (EBrk req) G s0).
Proof.
  intros L G s0 b l HG Hph Ereg req.
  apply mspec_get_bind_eq.
  eapply mspec_bind.
  { apply (mspec_sys (NBrk req) (dec_brk (ps_brk s0) req) _
             (fun a s mo => s = s0 /\ G s mo /\ (req <> b + l /\ 0 < req) /\ ps_brk s0 = b + l /\
                match a with
                | BrkGrown => KL (set_brkreg (Some (b, l + PGSZ)) L) req mo /\ lbrk_pages_ok L (b + l) PGSZ = true
                | BrkSame => KL (set_brkph BPDead L) (b + l) mo
                end)).
    intros s mo (-> & HK & HGs). pose proof (KL_ceil_lt63 _ _ _ HK) as Hcl. split; [exact I|].
    intros rsp mo' evs Hst.
    pose proof (minv_preserved' _ _ _ _ _ (kl_minv _ _ _ HK) (kl_halt _ _ _ HK) Hst ltac:(nores)) as [Hh' Hmi'].
    pose proof (kl_phase _ _ _ HK) as Kph. rewrite Hph in Kph. destruct Kph as (b' & l' & Ereg' & Ebrk & Epbrk).
    rewrite Ereg in Ereg'. injection Ereg' as <- <-.
    pose proof (kl_brkreg _ _ _ HK b l Ereg) as (R1 & R2 & R3 & R4 & R5 & Rcov).
    pose proof (kl_start _ _ _ HK) as (S1 & S2 & S3 & S4).
    pose proof (nstep_brk_inv _ _ _ _ _ Hst) as (r & Hr & Emo' & _ & _).
    pose proof (nstep_dec_brk req mo rsp mo' evs ltac:(lia) ltac:(lia) ltac:(unfold PGSZ in *; lia) Hst) as (_ & Hvo & a & Hdec & Ha).
    set (h := m_vmmaps mo) in *.
    rewrite Ebrk in Hdec. rewrite Epbrk. exists a. split; [exact Hdec|].
    split; [reflexivity|]. split; [eapply HG; [reflexivity|reflexivity| exact Hvo| exact HGs]|].
    split; [unfold PGSZ in *; lia|]. split; [reflexivity|].
    apply brk_r_ok_grow in Hr; fold h in Hr; [| fold h; lia| fold h; unfold PGSZ in *; lia].
    pose proof (brk_model_next_same h (Z_to_bv 64 req)) as (Q1 & Q2 & Q3 & Q4 & Q5).
    pose proof (brk_model_next_grown h req ltac:(lia) ltac:(unfold PGSZ in *; lia)) as (P1 & P2 & P3 & P4 & P5).
    destruct a.
    -
      destruct Hr as [-> | [-> Hgo]].
      { exfalso. rewrite Emo' in Ha. cbn [m_vmmaps with_vmmaps] in Ha. rewrite Q5 in Ha.
        apply (f_equal bv_unsigned) in Ha. rewrite unsigned_lit in Ha by (unfold PGSZ in *; lia). lia. }
      apply brk_grow_ok_facts in Hgo; fold h in Hgo; [| fold h; lia| fold h; unfold PGSZ in *; lia| fold h; rewrite Ebrk; unfold PGSZ in *; rewrite Z.add_mod, R2, R4 by lia; reflexivity| subst req; unfold PGSZ in *; rewrite Z.add_mod, (Z.add_mod b l), R2, R4 by lia; reflexivity].
      destruct Hgo as [Hceil Hrf].
      replace (alloc_top h) with (ld_ceil L) in Hceil by (exact (kl_ceil _ _ _ HK)).
      apply (region_free_shrink _ _ _ (Z_to_bv 64 (req - bv_unsigned (vm_brk h)))) in Hrf; [| rewrite !unsigned_lit by (unfold PGSZ in *; lia); lia].
      assert (HPG : lbrk_pages_ok L (b + l) PGSZ = true).
      { apply (KL_lbrk_pages_ok L (ps_brk s0) mo (b + l) PGSZ HK); [lia| unfold PGSZ; lia| subst req; lia| |].
        - replace (b + l) with (bv_unsigned (vm_brk h)) at 1 by exact Ebrk. replace (Z_to_bv 64 PGSZ) with (Z_to_bv 64 (req - bv_unsigned (vm_brk h))) by (f_equal; lia). exact Hrf.
        - intros b1 l1 E. rewrite Ereg in E. injection E as <- <-. split; [exact R4| left; lia]. }
      rewrite Z_to_bv_bv_unsigned in Hrf.
      assert (Hn : bv_unsigned (Z_to_bv 64 (req - bv_unsigned (vm_brk h))) = PGSZ) by (rewrite unsigned_lit; unfold PGSZ in *; lia).
      pose proof (fun b0 l0 H => went_In_bounds _ _ _ b0 l0 HK H) as WB.
      split; [|exact HPG].
      kl_open HK. constructor; rewrite ?Emo'; cbn [m_vmmaps with_vmmaps set_brkreg ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live ld_ceil];
        rewrite ?P1, ?P2, ?P3, ?P4, ?P5; auto; try kl_ceil_close Kceil.
      + apply vmwf_cons; [exact Kwf| rewrite Hn; unfold PGSZ in *; lia| eapply region_free_app_r; exact Hrf].
      + rewrite unsigned_lit by (unfold PGSZ in *; lia). splits; try lia; auto.
      + intros b0 l0 Hin. pose proof (WB b0 l0 (or_introl Hin)) as (B1 & B2 & B3 & B4 & B5 & B6).
        pose proof (region_free_disj _ _ _ _ (region_free_app_r _ _ _ _ Hrf) B4) as D. rewrite B5, B6, Hn in D.
        specialize (Kgr b0 l0 Hin). destruct Kgr as ([G0 G1] & G2 & G3 & G4 & G5 & G6). splits; try assumption; try (right; assumption).
        unfold brk_disj in *. cbn. intros b1 l1 E. injection E as <- <-. specialize (G6 b l Ereg). clear -G6 D Ebrk B2. lia.
      + intros b0 l0 k Hin. pose proof (WB b0 l0 (or_intror (ex_intro _ k Hin))) as (B1 & B2 & B3 & B4 & B5 & B6).
        pose proof (region_free_disj _ _ _ _ (region_free_app_r _ _ _ _ Hrf) B4) as D. rewrite B5, B6, Hn in D.
        specialize (Kme b0 l0 k Hin). destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). splits; try assumption; try (right; assumption).
        unfold brk_disj in *. cbn. intros b1 l1 E. injection E as <- <-. specialize (G8 b l Ereg). clear -G8 D Ebrk B2. lia.
      + intros b1 l1 E. injection E as <- <-. splits; auto.
        * clear -R3. unfold PGSZ in *; lia.
        * unfold PGSZ in *. rewrite Z.add_mod, R4 by lia. reflexivity.
        * clear -Hceil. subst req. lia.
        * intros x Hx. destruct (Z_lt_le_dec x (b + l)) as [Hlt|Hge].
          -- destruct (Rcov x ltac:(lia)) as (e & He & Hr'). exists e. split; [right; exact He| exact Hr'].
          -- exists (vm_brk h, Z_to_bv 64 (req - bv_unsigned (vm_brk h))). split; [left; reflexivity|]. rewrite elo_pair, ehi_pair, Hn. lia.
      + rewrite Hph. exists b, (l + PGSZ). rewrite unsigned_lit by (unfold PGSZ in *; lia). splits; auto; lia.
      + intros ee Hee. destruct (Kna ee Hee) as (Knz & ee' & Hee' & Kna1 & Kna2 & Kna3). split; [exact Knz|]. exists ee'. split; [right; exact Hee'|]. auto.
    -
      destruct Hr as [-> | [-> Hgo]].
      2:{ exfalso. rewrite Emo' in Ha. cbn [m_vmmaps with_vmmaps] in Ha. rewrite P5 in Ha.
          apply (f_equal bv_unsigned) in Ha. rewrite unsigned_lit in Ha by (unfold PGSZ in *; lia). lia. }
      apply KL_dead with (pbrk := ps_brk s0). eapply KL_vm_eq; [exact HK| exact Hmi'| exact Hh'| | | | | |]; rewrite Emo'; cbn [m_vmmaps with_vmmaps]; first [assumption| reflexivity]. }
  intros a. cbn beta. destruct a.
  - eapply mspec_bind; [apply mspec_upd|]. intros []. apply mspec_ret.
    intros s mo (s1 & -> & -> & HGs & [Hne Hpos] & Ecur & HK). unfold ev_step_post.
    cbn [ps_brk set_brk_ps ps_m ps_fa ps_so answer_ok event_post].
    replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Hph, Ereg, Z.eqb_refl.
    destruct HK as [HK HPG].
    splits; auto.
    + unfold brk_answer_ok. rewrite Z.eqb_refl, HPG. reflexivity.
    + eapply (HG s0); [reflexivity|reflexivity| apply mm_frame_refl| exact HGs].
  - apply mspec_ret. intros s mo (-> & HGs & [Hne Hpos] & Ecur & HK). unfold ev_step_post.
    cbn [answer_ok event_post].
    replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Hph, Ereg, Ecur.
    replace (b + l =? req) with false by (symmetry; apply Z.eqb_neq; lia).
    splits; auto. unfold brk_answer_ok. rewrite Z.eqb_refl, orb_true_r. reflexivity.
Qed.

Lemma wcov_rf_disj : forall maps lo hi aw nw,
  wcov maps lo hi -> region_free maps aw nw = true -> 0 < bv_unsigned nw -> lo < hi ->
  bv_unsigned aw + bv_unsigned nw <= lo \/ hi <= bv_unsigned aw.
Proof.
  intros maps lo hi aw nw Hc Hrf Hn Hlh.
  destruct (Z_le_gt_dec (bv_unsigned aw + bv_unsigned nw) lo) as [|H1]; [left; assumption|].
  destruct (Z_le_gt_dec hi (bv_unsigned aw)) as [|H2]; [right; assumption|]. exfalso.
  destruct (Hc (Z.max (bv_unsigned aw) lo) ltac:(lia)) as (e & He & Hr).
  pose proof (region_free_disj _ _ _ _ Hrf He). lia.
Qed.

Lemma mmap_len_pos_pg : forall l, 0 < l -> PGSZ <= mmap_len l.
Proof.
  intros l Hl. pose proof (mmap_len_ge l Hl). pose proof (mmap_len_aligned l).
  pose proof (Z_div_mod_eq_full (mmap_len l) 4096). unfold PGSZ. nia.
Qed.

Lemma KL_mmap_new : forall L pbrk mo mo' a len (isnone : bool),
  KL L pbrk mo -> brk_quiet L -> 0 < len < LEN_MAX ->
  let h := m_vmmaps mo in let n := mmap_len len in
  mmap_addr_ok len [] a = true ->
  a + n <= alloc_top h ->
  region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 a) (Z_to_bv 64 n) = true ->
  minv mo' -> m_halted mo' = None ->
  m_vmmaps mo' = mkVmMapsFull (vm_reserved h) ((Z_to_bv 64 a, Z_to_bv 64 n) :: vm_maps h)
                 (if isnone then (Z_to_bv 64 a, Z_to_bv 64 n) :: vm_noaccess h else vm_noaccess h)
                 (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) ->
  KL (if isnone then set_metas ((a, len, 0) :: ld_metas L) L else set_groups ((a, len) :: ld_groups L) L) pbrk mo'
  /\ mmap_answer_ok (ld_ceil L) (lranges L) len a = true /\ is_err a = false.
Proof.
  intros L pbrk mo mo' a len isnone HK Hq Hlen h n Hok Htop Hrf Hmi' Hh' Evm. pose proof (KL_ceil_lt63 _ _ _ HK) as Hcl.
  apply mmap_addr_ok_true in Hok as [(A1 & A2 & _) _]. rewrite page_size_eq in A1.
  assert (A3 : a + n <= ld_ceil L) by (rewrite (kl_ceil _ _ _ HK); exact Htop).
  pose proof (mmap_len_ge len ltac:(lia)) as Hn1. pose proof (mmap_len_pos_pg len ltac:(lia)) as Hn2. fold n in Hn1, Hn2.
  assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit; lia).
  assert (Un : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  pose proof (region_free_app_r _ _ _ _ Hrf) as Hrfm.
  pose proof (fun b0 l0 H => went_In_bounds _ _ _ b0 l0 HK H) as WB.
  assert (Hround : round_up_pg len = n) by (subst n; apply round_up_pg_eq).

  assert (Dgm : forall b0 l0, (In (b0, l0) (ld_groups L) \/ exists k, In (b0, l0, k) (ld_metas L)) ->
                 a + n <= b0 \/ b0 + mmap_len l0 <= a).
  { intros b0 l0 H. pose proof (WB b0 l0 H) as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (region_free_disj _ _ _ _ Hrfm B4) as D. rewrite B5, B6, Ua, Un in D. exact D. }
  assert (Dbrk : forall b0 l0, ld_brkreg L = Some (b0, l0) -> a + n <= b0 + PGSZ \/ b0 + l0 <= a).
  { intros b0 l0 E. pose proof (kl_brkreg _ _ _ HK b0 l0 E) as (R1 & R2 & R3 & R4 & R5 & Rcov).
    pose proof (wcov_rf_disj _ _ _ _ _ Rcov Hrfm ltac:(rewrite Un; lia) ltac:(clear -R3; unfold PGSZ in *; lia)) as D. rewrite Ua, Un in D. exact D. }
  split; [|split].
  2:{ unfold mmap_answer_ok. apply orb_true_intro. right. rewrite Hround.
      rewrite (proj2 (Z.ltb_lt 0 a)) by lia. unfold PGSZ at 1. rewrite A1, Z.eqb_refl. rewrite (proj2 (Z.leb_le _ _) A3). cbn [andb].
      unfold ranges_free. apply List.forallb_forall. intros [lo m] Hin. cbn [fst snd]. unfold iv_disjoint.
      enough (a + n <= lo \/ lo + m <= a) as D.
      { destruct D as [D|D]; [rewrite (proj2 (Z.leb_le _ _) D); reflexivity| rewrite (proj2 (Z.leb_le _ _) D); apply orb_true_r]. }
      apply In_lranges in Hin as [H|[(b0 & l0 & H & E)|[(b0 & l0 & k & H & E)|(b0 & l0 & H & E)]]].
      - rewrite (kl_resv _ _ _ HK) in H. apply in_map_iff in H as ([e sz] & E & H). unfold wwZ in E. cbn [fst snd] in E. injection E as <- <-.
        pose proof (region_free_In _ _ _ _ _ Hrf (in_or_app _ _ _ (or_introl H))) as D. rewrite Ua, Un in D. exact D.
      - injection E as -> ->. rewrite round_up_pg_eq. fold (mmap_len l0). apply Dgm. left; exact H.
      - injection E as -> ->. rewrite round_up_pg_eq. fold (mmap_len l0). apply Dgm. right; exists k; exact H.
      - injection E as -> ->. pose proof (kl_brkreg _ _ _ HK b0 l0 H) as (R1 & R2 & R3 & R4 & R5 & _).
        rewrite round_up_pg_aligned by (unfold PGSZ in R4; exact R4). pose proof (Dbrk b0 l0 H). lia. }
  2:{ unfold is_err, TWO64. apply Z.ltb_ge. lia. }
  assert (Hnotin : ~ In a (map fst (ld_groups L) ++ map (fun m => fst (fst m)) (ld_metas L))).
  { intros Hin. apply in_app_or in Hin as [Hin|Hin].
    - apply in_map_iff in Hin as ([b0 l0] & E & Hin). cbn in E. subst b0.
      pose proof (WB a l0 (or_introl Hin)) as (B1 & B2 & _). pose proof (Dgm a l0 (or_introl Hin)). lia.
    - apply in_map_iff in Hin as ([[b0 l0] k] & E & Hin). cbn in E. subst b0.
      pose proof (WB a l0 (or_intror (ex_intro _ k Hin))) as (B1 & B2 & _). pose proof (Dgm a l0 (or_intror (ex_intro _ k Hin))). lia. }
  kl_open HK.
  assert (Hph' : forall L', ld_brk L' = ld_brk L -> ld_brkreg L' = ld_brkreg L ->
            match ld_brk L' with
            | BPUntried => vm_brk (m_vmmaps mo') = vm_start_brk (m_vmmaps mo') /\ ld_brkreg L' = None
            | BPQueried cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo')) /\ bv_unsigned (vm_brk (m_vmmaps mo')) = cur /\ pbrk = cur /\ ld_brkreg L' = None
            | BPGuard cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo'))
                /\ bv_unsigned (vm_brk (m_vmmaps mo')) = cur + 2 * PGSZ /\ pbrk = cur + 2 * PGSZ
                /\ ld_brkreg L' = None /\ cur + 2 * PGSZ <= ld_ceil L'
                /\ (exists e, In e (vm_maps (m_vmmaps mo')) /\ elo e <= cur /\ cur + 2 * PGSZ <= ehi e)
                /\ (forall b l, In (b, l) (ld_groups L') -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
                /\ (forall b l k, In (b, l, k) (ld_metas L') -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
            | BPLive => exists b l, ld_brkreg L' = Some (b, l) /\ bv_unsigned (vm_brk (m_vmmaps mo')) = b + l /\ pbrk = b + l
            | BPDead => True
            end).
  { intros L' E1 E2. rewrite E1, E2, Evm. cbn [vm_brk vm_start_brk]. unfold brk_quiet in Hq.
    destruct (ld_brk L); try contradiction; auto. }
  destruct isnone; constructor;
    first [ apply (Hph' (set_metas _ L)); reflexivity
          | apply (Hph' (set_groups _ L)); reflexivity
          | rewrite ?Evm; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk set_metas set_groups ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live ld_ceil]; auto ].
  - apply vmwf_cons; [exact Kwf| rewrite Ua, Un; lia| exact Hrfm].
  - intros b0 l0 Hin. specialize (Kgr b0 l0 Hin). unfold brk_disj in *; cbn. intuition auto with datatypes.
  - intros b0 l0 k [E|Hin].
    + injection E as <- <- <-. unfold brk_disj; cbn. splits; try lia.
      * unfold PGSZ; exact A1.
      * left; reflexivity.
      * exact Dbrk.
      * intros q Hq1 Hq2. exists (Z_to_bv 64 a, Z_to_bv 64 n). split; [left; reflexivity|]. rewrite elo_pair, ehi_pair, Ua, Un. fold n in Hq2. lia.
    + specialize (Kme b0 l0 k Hin). destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). unfold brk_disj in *; cbn. splits; try assumption; try (right; assumption).
      intros q Hq1 Hq2. destruct (G9 q Hq1 Hq2) as (e & He & Hr). exists e. split; [right; exact He| exact Hr].
  - cbn [map fst app]. eapply Permutation_NoDup; [apply Permutation_middle|]. constructor; [exact Hnotin| exact Kdis].
  - intros b0 l0 E. specialize (Kreg b0 l0 E). destruct Kreg as (R1 & R2 & R3 & R4 & R5 & Rcov). splits; auto. eapply wcov_mono; [|exact Rcov]. intros e He; right; exact He.
  -
    intros ee [<-|Hee].
    + rewrite !elo_pair, !ehi_pair, Ua, Un. split; [lia|].
      exists (Z_to_bv 64 a, Z_to_bv 64 n). split; [left; reflexivity|]. rewrite !elo_pair, !ehi_pair, Ua, Un. split; [lia|]. split; [lia|].
      intros b0 l0 Hin E0. pose proof (Dgm b0 l0 (or_introl Hin)) as D. pose proof (WB b0 l0 (or_introl Hin)) as (_ & B2 & _). lia.
    + destruct (Kna ee Hee) as (Knz & ee' & Hee' & Kna1 & Kna2 & Kna3). split; [exact Knz|]. exists ee'. split; [right; exact Hee'|]. auto.
  - apply vmwf_cons; [exact Kwf| rewrite Ua, Un; lia| exact Hrfm].
  - intros b0 l0 [E|Hin].
    + injection E as <- <-. unfold brk_disj; cbn. splits; try lia.
      * unfold PGSZ; exact A1.
      * left; reflexivity.
      * exact Dbrk.
    + specialize (Kgr b0 l0 Hin). unfold brk_disj in *; cbn. intuition auto with datatypes.
  - intros b0 l0 k Hin. specialize (Kme b0 l0 k Hin). destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). unfold brk_disj in *; cbn. splits; try assumption; try (right; assumption).
  - cbn [map fst app]. constructor; [exact Hnotin| exact Kdis].
  - intros b0 l0 E. specialize (Kreg b0 l0 E). destruct Kreg as (R1 & R2 & R3 & R4 & R5 & Rcov). splits; auto. eapply wcov_mono; [|exact Rcov]. intros e He; right; exact He.
  -
    intros b0 l0 [E|Hin]; [| exact (Kgrv b0 l0 Hin)]. injection E as <- <-. intros [e sz] He.
    pose proof (region_free_In _ _ _ _ _ Hrf (in_or_app _ _ _ (or_introl He))) as D. rewrite Ua, Un in D. unfold elo, ehi; cbn [fst snd]. fold n. exact D.
  -
    intros ee Hee. destruct (Kna ee Hee) as (Knz & ee' & Hee' & Kna1 & Kna2 & Kna3). split; [exact Knz|]. exists ee'. split; [right; exact Hee'|]. split; [exact Kna1|]. split; [exact Kna2|].
    intros b0 l0 [E|Hin]; [| exact (Kna3 b0 l0 Hin)]. injection E as <- <-. intros E0.
    pose proof (region_free_disj _ _ _ _ Hrfm Hee') as D. rewrite Ua, Un in D. pose proof (proj1 Kwf ee' Hee'). lia.
Qed.

Lemma is_errno_form_neg : forall e, 1 <= e <= 4095 -> is_errno_form (neg_errno e) = true.
Proof. intros e He. unfold is_errno_form, neg_errno, TWO64. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. Qed.
Lemma is_err_neg : forall e, 1 <= e <= 4095 -> is_err (neg_errno e) = true.
Proof. intros e He. unfold is_err, neg_errno, TWO64. apply Z.ltb_lt. lia. Qed.

Lemma ev_mmap_core : forall L G s0 len (isnone : bool), frame_ok G -> brk_quiet L -> 0 < len < LEN_MAX ->
  let prot := if isnone then PROT_NONE else PROT_RW in
  let dec := if isnone then dec_mmap_none len [] else dec_mmap len [] in
  mspec (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ G s mo)
        (a <- msys (NMmap 0 len prot MAPF) dec ;; mret match a with MmErr e => neg_errno e | MmOk x => x end)
        (ev_step_post L (EMmap 0 len prot MAPF) G s0).
Proof.
  intros L G s0 len isnone HG Hq Hlen prot dec.
  pose proof (mmap_len_ge len ltac:(lia)) as Hn1.
  eapply mspec_bind.
  { apply (mspec_sys (NMmap 0 len prot MAPF) dec _
             (fun x s mo => s = s0 /\ G s mo /\
                match x with
                | MmErr e => e = ENOMEM /\ KL L (ps_brk s0) mo
                | MmOk a => KL (if isnone then set_metas ((a, len, 0) :: ld_metas L) L else set_groups ((a, len) :: ld_groups L) L) (ps_brk s0) mo
                            /\ mmap_answer_ok (ld_ceil L) (lranges L) len a = true /\ is_err a = false
                end)).
    intros s mo (-> & HK & HGs). pose proof (KL_ceil_lt63 _ _ _ HK) as Hcl. split.
    { subst prot. destruct isnone; [apply nsafe_mmap_none| apply nsafe_mmap_rw]. }
    intros rsp mo' evs Hst.
    pose proof (minv_preserved' _ _ _ _ _ (kl_minv _ _ _ HK) (kl_halt _ _ _ HK) Hst ltac:(nores)) as [Hh' Hmi'].
    assert (Hcase : mm_frame mo mo' /\ exists x, dec rsp = Some x /\
              match x with
              | MmErr e => e = ENOMEM /\ mo' = mo
              | MmOk a => mmap_addr_ok len [] a = true
                  /\ a + mmap_len len <= alloc_top (m_vmmaps mo)
                  /\ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (Z_to_bv 64 a) (Z_to_bv 64 (mmap_len len)) = true
                  /\ m_vmmaps mo' = mkVmMapsFull (vm_reserved (m_vmmaps mo)) ((Z_to_bv 64 a, Z_to_bv 64 (mmap_len len)) :: vm_maps (m_vmmaps mo))
                       (if isnone then (Z_to_bv 64 a, Z_to_bv 64 (mmap_len len)) :: vm_noaccess (m_vmmaps mo) else vm_noaccess (m_vmmaps mo))
                       (vm_start_brk (m_vmmaps mo)) (vm_brk (m_vmmaps mo)) (vm_limit (m_vmmaps mo)) (vm_mmap_base (m_vmmaps mo)) (vm_init_sp (m_vmmaps mo))
              end).
    { pose proof (fun P => nstep_mmap0_top len prot mo rsp mo' evs ltac:(lia) ltac:(unfold LEN_MAX in *; lia) P Hst) as TOP.
      subst prot dec. destruct isnone.
      - specialize (TOP (or_introl eq_refl)).
        pose proof (nstep_dec_mmap_none len [] mo rsp mo' evs ltac:(lia) ltac:(unfold LEN_MAX in *; lia) (Forall_nil _) Hst) as (_ & Hvo & x & Hd & Hx).
        split; [exact Hvo|]. exists x. split; [exact Hd|]. destruct x as [e|a]; [exact Hx|].
        destruct Hx as (X1 & X2 & X3). split; [exact X1|]. split; [| split; [exact X2| exact X3]].
        pose proof (dec_mmap_none_Some _ _ _ _ Hd) as [Hs _]. destruct rsp as [r0 ws0 zs0 us0 cs0 ci0]. rewrite strip_mk in Hs.
        injection Hs as E1 E2 E3 E4 E5. subst r0. cbn [eff_ret] in TOP. rewrite unsigned_lit in TOP by (apply mmap_addr_ok_true in X1; unfold alloc_ceiling_max in X1; lia).
        apply TOP. rewrite errno_of_lit; [reflexivity| apply mmap_addr_ok_true in X1; unfold alloc_ceiling_max in X1; lia].
      - specialize (TOP (or_intror eq_refl)).
        pose proof (nstep_dec_mmap len [] mo rsp mo' evs ltac:(lia) ltac:(unfold LEN_MAX in *; lia) (Forall_nil _) Hst) as (_ & Hvo & x & Hd & Hx).
        split; [exact Hvo|]. exists x. split; [exact Hd|]. destruct x as [e|a]; [exact Hx|].
        destruct Hx as (X1 & X2 & X3). split; [exact X1|]. split; [| split; [exact X2| exact X3]].
        pose proof (dec_mmap_Some _ _ _ _ Hd) as [Hs _]. destruct rsp as [r0 ws0 zs0 us0 cs0 ci0]. rewrite strip_mk in Hs.
        injection Hs as E1 E2 E3 E4 E5. subst r0. cbn [eff_ret] in TOP. rewrite unsigned_lit in TOP by (apply mmap_addr_ok_true in X1; unfold alloc_ceiling_max in X1; lia).
        apply TOP. rewrite errno_of_lit; [reflexivity| apply mmap_addr_ok_true in X1; unfold alloc_ceiling_max in X1; lia]. }
    destruct Hcase as (Hvo & x & Hd & Hx). exists x. split; [exact Hd|].
    split; [reflexivity|]. split; [eapply HG; [reflexivity|reflexivity| exact Hvo| exact HGs]|].
    destruct x as [e|a].
    - destruct Hx as [-> ->]. split; [reflexivity| exact HK].
    - destruct Hx as (Hok & Htop & Hrf & Evm). apply (KL_mmap_new L (ps_brk s0) mo mo' a len isnone HK Hq Hlen Hok Htop Hrf Hmi' Hh' Evm). }
  intros x. cbn beta. apply mspec_ret. intros s mo (-> & HGs & Hx). unfold ev_step_post.
  cbn [answer_ok event_post]. change (Z.land MAPF MAP_FIXED =? 0) with true. cbv iota.
  destruct x as [e|a].
  - destruct Hx as [-> HK]. rewrite is_err_neg by (unfold ENOMEM; lia).
    unfold mmap_answer_ok. rewrite is_errno_form_neg by (unfold ENOMEM; lia). splits; auto.
  - destruct Hx as (HK & Hans & Herr). rewrite Herr. subst prot. destruct isnone.
    + change (PROT_NONE =? PROT_NONE) with true. cbv iota. splits; auto.
    + change (PROT_RW =? PROT_NONE) with false. cbv iota. splits; auto.
Qed.

Lemma ev_mmap_ok : forall L G s0 len prot, frame_ok G -> brk_quiet L -> (prot = PROT_NONE \/ prot = PROT_RW) -> 0 < len < LEN_MAX ->
  mspec (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ G s mo)
        (ev_step (EMmap 0 len prot MAPF))
        (ev_step_post L (EMmap 0 len prot MAPF) G s0).
Proof.
  intros L G s0 len prot HG Hq Hprot Hlen. unfold ev_step.
  change (Z.land MAPF MAP_FIXED_Z =? 0) with true. cbn [negb].
  destruct Hprot as [-> | ->].
  - change (PROT_NONE =? 0) with true. cbv iota. apply (ev_mmap_core L G s0 len true HG Hq Hlen).
  - change (PROT_RW =? 0) with false. cbv iota. apply (ev_mmap_core L G s0 len false HG Hq Hlen).
Qed.

Lemma region_free_above : forall maps aw nw, (forall e, In e maps -> ehi e <= bv_unsigned aw) -> region_free maps aw nw = true.
Proof.
  induction maps as [|[e sz] maps IH]; intros aw nw H; [reflexivity|]. cbn [region_free].
  rewrite IH by (intros e' He'; apply H; right; exact He'). unfold iv_overlap.
  specialize (H (e, sz) (or_introl eq_refl)). unfold ehi in H; cbn in H.
  replace (bv_unsigned aw <? bv_unsigned e + bv_unsigned sz) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma ev_mmap_fixed_ok : forall L G s0 cur, frame_ok G -> ld_brk L = BPGuard cur ->
  let a := round_up_pg cur in
  mspec (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ G s mo)
        (ev_step (EMmap a PGSZ PROT_NONE MAPFX))
        (ev_step_post L (EMmap a PGSZ PROT_NONE MAPFX) G s0).
Proof.
  intros L G s0 cur HG Hph a. unfold ev_step.
  change (Z.land MAPFX MAP_FIXED_Z =? 0) with false. cbn [negb].
  set (L' := set_brkph BPLive (set_brkreg (Some (a, 2 * PGSZ)) L)).
  eapply mspec_bind.
  { apply (mspec_sys (NMmap a PGSZ PROT_NONE MAPFX) (dec_mmap_fixed a PGSZ) _
             (fun x s mo => s = s0 /\ G s mo /\ KL L' (ps_brk s0) mo /\ match x with FxKept e => e = ENOMEM | FxDone => True | FxLost e => e = ENOMEM end)).
    intros s mo (-> & HK & HGs). pose proof (KL_ceil_lt63 _ _ _ HK) as Hcl.
    pose proof (kl_phase _ _ _ HK) as Kph. rewrite Hph in Kph. destruct Kph as (Ecur & Ebrk & Epbrk & Ereg & Hceil & (e0 & He0 & He0l & He0h) & Dg & Dm).
    pose proof (kl_start _ _ _ HK) as (S1 & S2 & S3 & S4).
    assert (Ha : a = cur). { subst a. apply round_up_pg_aligned. rewrite Ecur. exact S2. }
    set (h := m_vmmaps mo) in *. set (aw := Z_to_bv 64 a). set (nw := Z_to_bv 64 PGSZ).
    assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; unfold PGSZ in *; lia).
    assert (Un : bv_unsigned nw = PGSZ) by (subst nw; apply unsigned_lit; unfold PGSZ; lia).
    assert (Uhi : bv_unsigned (aw + nw)%bv = a + PGSZ).
    { rewrite bv_add_unsigned, Ua, Un. apply bv_wrap_small. unfold bv_modulus, PGSZ in *. lia. }
    assert (Hrf : region_free (vm_reserved h) aw nw = true).
    { apply region_free_above. intros e He. rewrite Ua, Ha, Ecur. apply (kl_resv_top _ _ _ HK). exact He. }
    assert (Hmc : map_contains (vm_maps h) aw nw = true).
    { unfold map_contains. apply existsb_exists. exists e0. split; [exact He0|]. rewrite Ua, Un. unfold elo, ehi in *.
      rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by (unfold PGSZ in *; lia). reflexivity. }
    assert (Htop : a + PGSZ <= alloc_top h).
    { pose proof (kl_ceil _ _ _ HK) as KC. change (m_vmmaps mo) with h in KC. rewrite <- KC. lia. }
    split.
    { unfold nsafe. intros _. cbv zeta. fold aw h. rewrite (unsigned_lit PGSZ) by (unfold PGSZ; lia).
      change (page_round_up_Z PGSZ) with PGSZ. fold nw. rewrite Ua.
      split; [exact Htop|]. split; [rewrite page_size_eq, Ha, Ecur; exact S2|]. split; [lia|]. split; [exact Hrf| exact Hmc]. }
    intros rsp mo' evs Hst.
    pose proof (minv_preserved' _ _ _ _ _ (kl_minv _ _ _ HK) (kl_halt _ _ _ HK) Hst ltac:(nores)) as [Hh' Hmi'].
    pose proof (nstep_mmap_fixed_inv a mo rsp mo' evs ltac:(lia) Htop ltac:(rewrite Ha, Ecur; exact S2) Hrf Hmc Hst) as (_ & Hvo & x & Hd & Hx).
    fold h aw nw in Hx.
    exists x. split; [exact Hd|]. split; [reflexivity|]. split; [eapply HG; [reflexivity|reflexivity| exact Hvo| exact HGs]|].

    pose proof (fun b0 l0 H => went_In_bounds _ _ _ b0 l0 HK H) as WB.
    assert (Dgm : forall b0 l0, (In (b0, l0) (ld_groups L) \/ exists k, In (b0, l0, k) (ld_metas L)) ->
                   b0 + mmap_len l0 <= a \/ a + 2 * PGSZ <= b0).
    { intros b0 l0 [H|[k H]]; rewrite Ha; [apply (Dg _ _ H)| apply (Dm _ _ _ H)]. }
    assert (KLnew : forall maps' noacc',
              vmwf maps' ->
              (forall e, In e (vm_maps h) -> (ehi e <= a \/ a + PGSZ <= elo e) -> In e maps') ->
              (forall e, In e maps' -> In e (vm_maps h) \/ In e (maps_subtract (vm_maps h) (bv_unsigned aw) (bv_unsigned aw + bv_unsigned nw))) ->
              (forall e x y, In e (vm_noaccess h) -> elo e <= x -> x < y -> y <= ehi e -> y <= 2^64 -> (y <= a \/ a + PGSZ <= x) ->
                  exists e', In e' noacc' /\ elo e' <= x /\ y <= ehi e') ->
              (exists e', In e' maps' /\ elo e' <= a + PGSZ /\ a + 2 * PGSZ <= ehi e') ->
              (forall e, In e noacc' -> elo e < ehi e /\ exists e', In e' maps' /\ elo e' <= elo e /\ ehi e <= ehi e'
                                                          /\ (forall b l, In (b, l) (ld_groups L) -> elo e' <> b)) ->
              m_vmmaps mo' = mkVmMapsFull (vm_reserved h) maps' noacc' (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) ->
              KL L' (ps_brk s0) mo').
    { intros maps' noacc' Hwf' Hkeep Hback Hna Hcov' Hna2 Evm. subst L'.
      kl_open HK. constructor; rewrite ?Evm; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk set_brkph set_brkreg ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live ld_ceil]; auto; try kl_ceil_close Kceil.
      - intros b0 l0 Hin. pose proof (WB b0 l0 (or_introl Hin)) as (B1 & B2 & B3 & B4 & B5 & B6). pose proof (Dgm b0 l0 (or_introl Hin)) as D.
        specialize (Kgr b0 l0 Hin). destruct Kgr as ([G0 G1] & G2 & G3 & G4 & G5 & G6). splits; try assumption.
        + apply Hkeep; [exact B4|]. rewrite B5, B6. clear -D. unfold PGSZ in *. lia.
        + unfold brk_disj; cbn. intros b1 l1 E. injection E as <- <-. clear -D. unfold PGSZ in *. lia.
      - intros b0 l0 k Hin. pose proof (WB b0 l0 (or_intror (ex_intro _ k Hin))) as (B1 & B2 & B3 & B4 & B5 & B6). pose proof (Dgm b0 l0 (or_intror (ex_intro _ k Hin))) as D.
        specialize (Kme b0 l0 k Hin). destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). splits; try assumption.
        + apply Hkeep; [exact B4|]. rewrite B5, B6. clear -D. unfold PGSZ in *. lia.
        + unfold brk_disj; cbn. intros b1 l1 E. injection E as <- <-. clear -D. unfold PGSZ in *. lia.
        + intros q Hq1 Hq2. destruct (G9 q Hq1 Hq2) as (e & He & Hel & Heh).
          apply (Hna e (b0 + q * PGSZ) (b0 + q * PGSZ + PGSZ) He Hel ltac:(unfold PGSZ; lia) Heh ltac:(unfold PGSZ in *; lia)). clear -D Hq1 Hq2 G5. unfold PGSZ in *. nia.
      - intros b1 l1 E. injection E as <- <-. splits.
        + lia.
        + rewrite Ha, Ecur. exact S2.
        + lia.
        + reflexivity.
        + lia.
        + intros z Hz. destruct Hcov' as (e' & He' & H1 & H2). exists e'. split; [exact He'|]. lia.
      - exists a, (2 * PGSZ). splits; [reflexivity| lia| lia]. }
    assert (Hlohi : 0 <= bv_unsigned aw < bv_unsigned aw + bv_unsigned nw) by (rewrite Ua, Un; unfold PGSZ in *; lia).
    destruct x as [e| |e].
    - destruct Hx.
    - split; [|exact I].
      apply (KLnew (vm_maps h) ((aw, nw) :: maps_subtract (vm_noaccess h) (bv_unsigned aw) (bv_unsigned aw + bv_unsigned nw))); auto.
      + exact (kl_wf _ _ _ HK).
      + intros e x y He H1 H2 H3 HY H4. destruct (iv_subtract_contains (fst e) (snd e) (bv_unsigned aw) (bv_unsigned aw + bv_unsigned nw) x y (proj2 Hlohi) HY H1 H2 H3 ltac:(rewrite Ua, Un; exact H4)) as (e' & He' & Hr).
        exists e'. split; [right; eapply maps_subtract_In_intro; eauto| exact Hr].
      + exists e0. split; [exact He0|]. unfold PGSZ in *; lia.
      +
        intros e1 [<-|He1].
        * rewrite !elo_pair, !ehi_pair, Ua, Un. split; [unfold PGSZ; lia|].
          exists e0. split; [exact He0|]. split; [unfold elo in *; lia|]. split; [unfold ehi in *; unfold PGSZ in *; lia|].
          intros b0 l0 Hin E0. pose proof (Dg b0 l0 Hin) as D. pose proof (WB b0 l0 (or_introl Hin)) as (B1 & B2 & B3 & B4 & B5 & B6).
          pose proof (proj1 (kl_wf _ _ _ HK) e0 He0) as W0.
          destruct (pwdisj_In _ _ _ (proj2 (kl_wf _ _ _ HK)) He0 B4) as [EQ|DJ].
          -- rewrite EQ in He0l, He0h. rewrite B5 in He0l. rewrite B6 in He0h. clear -D He0l He0h B2. unfold PGSZ in *. lia.
          -- unfold edisj in DJ. rewrite B5, B6 in DJ. lia.
        * destruct (maps_subtract_piece _ _ _ _ (kl_noacc_wf _ _ _ HK) He1) as (e2 & He2 & Q1 & Q2 & Q3 & Q4 & Q5).
          destruct (kl_noacc _ _ _ HK e2 He2) as (_ & e3 & He3 & U1 & U2 & U3). split; [exact Q3|]. exists e3. split; [exact He3|]. split; [lia|]. split; [lia|]. exact U3.
    - destruct Hx.     }
  intros x. cbn beta. apply mspec_ret. intros s mo (-> & HGs & HK & Hx). unfold ev_step_post.
  cbn [answer_ok event_post]. change (Z.land MAPFX MAP_FIXED =? 0) with false. cbv iota. fold L'.
  splits; auto. unfold mmap_fixed_answer_ok. destruct x as [e| |e]; try subst e.
  - rewrite is_errno_form_neg by (unfold ENOMEM; lia). reflexivity.
  - rewrite Z.eqb_refl. apply orb_true_r.
  - rewrite is_errno_form_neg by (unfold ENOMEM; lia). reflexivity.
Qed.

Lemma g_remove_split : forall a l0 (l : list (Z * Z)) (M : list Z), In (a, l0) l -> List.NoDup (map fst l ++ M) ->
  exists l1 l2, l = l1 ++ (a, l0) :: l2 /\ g_remove a l = l1 ++ l2.
Proof.
  intros a l0 l M. induction l as [|[x1 x2] l IH]; intros Hin Hnd; [destruct Hin|]. cbn [g_remove fst snd].
  cbn [map fst app] in Hnd. inversion Hnd as [|? ? Hni Hnd']; subst.
  destruct (Z.eqb_spec x1 a) as [->|Hne].
  - destruct Hin as [E|Hin]; [injection E as ->; exists [], l; split; reflexivity|].
    exfalso. apply Hni. apply in_or_app. left. apply in_map_iff. exists (a, l0). split; [reflexivity| exact Hin].
  - destruct Hin as [E|Hin]; [injection E; intros; subst; contradiction|]. destruct (IH Hin Hnd') as (l1 & l2 & -> & E).
    exists ((x1, x2) :: l1), l2. rewrite E. split; reflexivity.
Qed.

Lemma phase_quiet : forall L L' pbrk mo mo',
  KL L pbrk mo -> brk_quiet L -> ld_brk L' = ld_brk L -> ld_brkreg L' = ld_brkreg L ->
  vm_start_brk (m_vmmaps mo') = vm_start_brk (m_vmmaps mo) -> vm_brk (m_vmmaps mo') = vm_brk (m_vmmaps mo) ->
  phase_inv (ld_brk L') L' pbrk mo'.
Proof.
  intros L L' pbrk mo mo' HK Hq E1 E2 E3 E4. pose proof (kl_phase _ _ _ HK) as Kph. unfold brk_quiet in Hq. unfold phase_inv.
  rewrite E1, E2, E3, E4. destruct (ld_brk L); try contradiction; auto.
Qed.

Lemma ev_munmap_ok : forall L G s0 a l0 len, frame_ok G -> brk_quiet L -> In (a, l0) (ld_groups L) ->
  (len = l0 \/ len = round_up_pg l0) ->
  mspec (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ G s mo)
        (ev_step (EMunmap a len))
        (ev_step_post L (EMunmap a len) G s0).
Proof.
  intros L G s0 a l0 len HG Hq Hin Hlen. unfold ev_step.
  rewrite round_up_pg_eq in Hlen. fold (mmap_len l0) in Hlen.
  set (L' := set_groups (g_remove a (ld_groups L)) L).
  eapply mspec_bind.
  { apply (mspec_sys (NMunmap a len) (dec_munmap a len) _
             (fun x s mo => s = s0 /\ G s mo /\ KL L' (ps_brk s0) mo /\ match x with RgErr e => e = EINVAL | RgDone _ => True end)).
    intros s mo (-> & HK & HGs). pose proof (KL_ceil_lt63 _ _ _ HK) as Hcl.
    pose proof (kl_groups _ _ _ HK a l0 Hin) as (A1 & A2 & A3 & A4 & A5 & A6).
    pose proof (went_In_bounds _ _ _ a l0 HK (or_introl Hin)) as (_ & B2 & _ & _ & B5 & B6).
    set (n := mmap_len l0) in *. set (h := m_vmmaps mo) in *. set (aw := Z_to_bv 64 a) in *. set (nw := Z_to_bv 64 n) in *.
    assert (Hnn : mmap_len n = n) by (subst n; apply mmap_len_of_aligned; [lia| apply mmap_len_aligned]).
    assert (Hlen3 : 0 < len < 2^64 /\ mmap_len len = n).
    { destruct Hlen as [-> | ->]; [unfold LEN_MAX in A1; split; [lia| reflexivity]| split; [lia| exact Hnn]]. }
    destruct Hlen3 as [Hlen1 Hlen2].
    assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; lia).
    assert (Un : bv_unsigned nw = n) by (subst nw; apply unsigned_lit; lia).
    assert (Uhi : bv_unsigned (aw + nw)%bv = a + n).
    { rewrite bv_add_unsigned, Ua, Un. apply bv_wrap_small. unfold bv_modulus. lia. }
    assert (Hhas : map_has (vm_maps h) aw nw = true).
    { unfold map_has. apply existsb_exists. exists (went a n). split; [exact A5|]. unfold went, wz. fold aw nw. cbn [fst snd]. rewrite !bv_eqb_refl. reflexivity. }
    split.
    { unfold nsafe. fold h aw. rewrite (unsigned_lit len) by lia. change (page_round_up_Z len) with (mmap_len len). rewrite Hlen2. change (Z_to_bv 64 n) with nw. exact Hhas. }
    intros rsp mo' evs Hst.
    pose proof (minv_preserved' _ _ _ _ _ (kl_minv _ _ _ HK) (kl_halt _ _ _ HK) Hst ltac:(nores)) as [Hh' Hmi'].
    pose proof (nstep_dec_munmap a len mo rsp mo' evs ltac:(lia) ltac:(lia) Hst) as (_ & Hvo & Hd & EvmU).
    rewrite Hlen2 in EvmU. fold h aw nw in EvmU.
    exists (RgDone true). split; [exact Hd|]. split; [reflexivity|]. split; [eapply HG; [reflexivity|reflexivity| exact Hvo| exact HGs]|].

    pose proof (kl_distinct _ _ _ HK) as Kd.
    destruct (g_remove_split a l0 (ld_groups L) _ Hin Kd) as (g1 & g2 & Eg & Ezz).
    rewrite Eg, map_app in Kd. cbn [map fst] in Kd. rewrite <- app_assoc in Kd. cbn [app] in Kd.
    pose proof (List.NoDup_remove_1 _ _ _ Kd) as Kd1. pose proof (List.NoDup_remove_2 _ _ _ Kd) as Kd2.
    assert (Hg' : forall b l, In (b, l) (g_remove a (ld_groups L)) -> In (b, l) (ld_groups L) /\ b <> a).
    { intros b l H. rewrite Ezz in H. rewrite Eg. split; [apply in_app_or in H as [H|H]; apply in_or_app; [left; exact H| right; right; exact H]|].
      intros ->. apply Kd2. rewrite app_assoc, <- map_app. apply in_or_app. left. apply in_map_iff. exists (a, l). split; [reflexivity| exact H]. }
    assert (Hm' : forall b l k, In (b, l, k) (ld_metas L) -> b <> a).
    { intros b l k H ->. apply Kd2. apply in_or_app. right. apply in_or_app. right. apply in_map_iff. exists (a, l, k). split; [reflexivity| exact H]. }

    assert (Dother : forall b l, (In (b, l) (ld_groups L) \/ exists k, In (b, l, k) (ld_metas L)) -> b <> a ->
                     b + mmap_len l <= a \/ a + n <= b).
    { intros b l H Hne. pose proof (went_In_bounds _ _ _ b l HK H) as (C1 & C2 & C3 & C4 & C5 & C6).
      destruct (pwdisj_In _ _ _ (proj2 (kl_wf _ _ _ HK)) C4 A5) as [E|D].
      - exfalso. apply Hne. apply (f_equal elo) in E. rewrite C5, B5 in E. exact E.
      - unfold edisj in D. rewrite C5, C6, B5, B6 in D. lia. }
    assert (KLnew : forall maps' noacc',
              vmwf maps' ->
              (forall e, In e (vm_maps h) -> fst e <> aw -> In e maps') ->
              (forall e x y, In e (vm_noaccess h) -> elo e <= x -> x < y -> y <= ehi e -> y <= 2^64 -> (y <= a \/ a + n <= x) ->
                  exists e', In e' noacc' /\ elo e' <= x /\ y <= ehi e') ->
              (forall e, In e noacc' -> elo e < ehi e /\ exists e', In e' maps' /\ elo e' <= elo e /\ ehi e <= ehi e'
                                                          /\ (forall b l, In (b, l) (ld_groups L) -> b <> a -> elo e' <> b)) ->
              m_vmmaps mo' = mkVmMapsFull (vm_reserved h) maps' noacc' (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) ->
              KL L' (ps_brk s0) mo').
    { intros maps' noacc' Hwf' Hkeep Hna Hna2 Evm.
      assert (Hph' : phase_inv (ld_brk L') L' (ps_brk s0) mo') by (eapply phase_quiet; [exact HK| exact Hq| reflexivity| reflexivity| rewrite Evm; reflexivity| rewrite Evm; reflexivity]).
      assert (Kfst : forall b l, b <> a -> 0 < b < 2^64 -> fst (went b (mmap_len l)) <> aw).
      { intros b l Hne Hb E. apply Hne. apply (f_equal bv_unsigned) in E. cbn [fst went] in E. rewrite unsigned_wz, Ua in E by lia. exact E. }
      subst L'. kl_open HK. constructor; try exact Hph'; rewrite ?Evm; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk set_groups ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live ld_ceil]; auto; try kl_ceil_close Kceil.
      - intros b0 l1 Hin0. destruct (Hg' b0 l1 Hin0) as [Hin1 Hne]. specialize (Kgr b0 l1 Hin1). destruct Kgr as ([G0 G1] & G2 & G3 & G4 & G5 & G6). splits; try assumption.
        apply Hkeep; [exact G5|]. apply Kfst; auto. pose proof (mmap_len_ge l1 G0). lia.
      - intros b0 l1 k Hin0. pose proof (Hm' b0 l1 k Hin0) as Hne. specialize (Kme b0 l1 k Hin0). destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). splits; try assumption.
        + apply Hkeep; [exact G7|]. apply Kfst; auto. pose proof (mmap_len_ge l1 G0). lia.
        + intros q Hq1 Hq2. destruct (G9 q Hq1 Hq2) as (e & He & Hel & Heh).
          pose proof (Dother b0 l1 (or_intror (ex_intro _ k Hin0)) Hne) as D.
          apply (Hna e (b0 + q * PGSZ) (b0 + q * PGSZ + PGSZ) He Hel ltac:(unfold PGSZ; lia) Heh ltac:(unfold PGSZ in *; lia)). clear -D Hq1 Hq2 G5. unfold PGSZ in *. nia.
      - rewrite Ezz, map_app, <- app_assoc. exact Kd1.
      - intros b0 l1 E. specialize (Kreg b0 l1 E). destruct Kreg as (R1 & R2 & R3 & R4 & R5 & Rcov). splits; auto.
        intros z Hz. destruct (Rcov z Hz) as (e & He & Hr). exists e. split; [|exact Hr]. apply Hkeep; [exact He|].
        intros Efst. unfold brk_disj in A6. specialize (A6 b0 l1 E).
        destruct (pwdisj_In _ _ _ (proj2 Kwf) He A5) as [->|D].
        + rewrite B5, B6 in Hr. clear -Hr A6 Hz R3. unfold PGSZ in *. lia.
        + pose proof (proj1 Kwf e He) as W. unfold edisj, elo, ehi in D, W. rewrite Efst in D, W. cbn [fst snd went] in D. unfold wz in D. fold aw nw in D. rewrite Un in D. lia.
      - intros b0 l1 Hin0. destruct (Hg' b0 l1 Hin0) as [Hin1 _]. exact (Kgrv b0 l1 Hin1).
      - intros ee Hee. destruct (Hna2 ee Hee) as (Knz & ee' & Hee' & U1 & U2 & U3). split; [exact Knz|]. exists ee'. split; [exact Hee'|]. split; [exact U1|]. split; [exact U2|].
        intros b0 l1 Hin0. destruct (Hg' b0 l1 Hin0) as [Hin1 Hne]. exact (U3 b0 l1 Hin1 Hne). }
    assert (Hlohi : 0 <= bv_unsigned aw < bv_unsigned aw + bv_unsigned nw) by (rewrite Ua, Un; lia).
    split; [|exact I]. apply (KLnew (map_remove (vm_maps h) aw) (maps_subtract (vm_noaccess h) (bv_unsigned aw) (bv_unsigned aw + bv_unsigned nw))).
    + apply vmwf_remove. exact (kl_wf _ _ _ HK).
    + intros e He Hne. unfold map_remove. apply filter_In. split; [exact He|]. destruct (bv_eqb (fst e) aw) eqn:E; [|reflexivity]. apply bv_eqb_eq in E. contradiction.
    + intros e x y He H1 H2 H3 HY H4. destruct (iv_subtract_contains (fst e) (snd e) (bv_unsigned aw) (bv_unsigned aw + bv_unsigned nw) x y (proj2 Hlohi) HY H1 H2 H3 ltac:(rewrite Ua, Un; exact H4)) as (e' & He' & Hr).
      exists e'. split; [eapply maps_subtract_In_intro; eauto| exact Hr].
    + intros e1 He1. destruct (maps_subtract_piece _ _ _ _ (kl_noacc_wf _ _ _ HK) He1) as (e2 & He2 & Q1 & Q2 & Q3 & Q4 & Q5).
      destruct (kl_noacc _ _ _ HK e2 He2) as (_ & e3 & He3 & U1 & U2 & U3). split; [exact Q3|].
      exists e3. split.
      * unfold map_remove. apply filter_In. split; [exact He3|]. destruct (bv_eqb (fst e3) aw) eqn:E; [|reflexivity]. exfalso.
        apply bv_eqb_eq in E. apply (U3 a l0 Hin). unfold elo. rewrite E. exact Ua.
      * split; [lia|]. split; [lia|]. intros b0 l1 Hin0 _. exact (U3 b0 l1 Hin0).
    + exact EvmU. }
  intros x. cbn beta. apply mspec_ret. intros s mo (-> & HGs & HK & Hx). unfold ev_step_post.
  cbn [answer_ok event_post]. fold L'.
  splits; auto. unfold munmap_answer_ok. destruct x as [e|b]; try subst e.
  - rewrite is_errno_form_neg by (unfold EINVAL; lia). apply orb_true_r.
  - reflexivity.
Qed.

Lemma nodup_map_inj : forall {A B} (f : A -> B) l x y, List.NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof.
  induction l as [|z l IH]; intros x y Hnd Hx Hy E; [destruct Hx|]. cbn in Hnd. inversion Hnd; subst.
  destruct Hx as [<-|Hx], Hy as [<-|Hy]; [reflexivity| | | apply IH; auto].
  - exfalso. apply H1. rewrite E. apply in_map. exact Hy.
  - exfalso. apply H1. rewrite <- E. apply in_map. exact Hx.
Qed.

Lemma map_base_bump : forall a ms, map (fun m : Z * Z * Z => fst (fst m)) (map (bump_meta a) ms) = map (fun m => fst (fst m)) ms.
Proof.
  intros a ms. rewrite map_map. apply map_ext. intros [[b l] k]. unfold bump_meta. destruct (_ =? _); reflexivity.
Qed.

Lemma map_contains_not_free : forall maps a n, (0 < bv_unsigned n)%Z ->
  map_contains maps a n = true -> region_free maps a n = true -> False.
Proof.
  intros maps a n Hn Hc Hf. unfold map_contains in Hc. apply existsb_exists in Hc as ([e sz] & Hin & Hb).
  cbn [fst snd] in Hb. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (region_free_In _ _ _ _ _ Hf Hin). lia.
Qed.

Lemma nstep_mprotect_rgfalse : forall addr len mo rsp mo' evs,
  let h := m_vmmaps mo in
  let a := Z_to_bv 64 addr in let n := Z_to_bv 64 (mmap_len len) in
  (0 <= addr < 2^64)%Z -> (0 < len)%Z -> (mmap_len len < 2^64)%Z ->
  map_contains (vm_noaccess h) a n = true ->
  nstep (NMprotect addr len (PROT_READ + PROT_WRITE)) mo rsp mo' evs ->
  dec_mprotect addr len rsp = Some (RgDone false) -> False.
Proof.
  intros addr len mo rsp mo' evs h a n Ha Hlen Hlen2 Hcn H Hd.
  pose proof (mmap_len_bound len Hlen) as Hb.
  destruct (nstep_dec_mprotect addr len (PROT_READ + PROT_WRITE) mo rsp mo' evs ltac:(lia) ltac:(lia) H) as (_ & _ & x & Hx & HX).
  rewrite Hd in Hx. inversion Hx; subst. exact HX.
Qed.

Lemma ev_mprotect_ok : forall L G s0 b l k, frame_ok G -> brk_quiet L -> In (b, l, k) (ld_metas L) ->
  (2 + k) * PGSZ <= round_up_pg l ->
  let a := b + (1 + k) * PGSZ in
  mspec (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ G s mo)
        (ev_step (EMprotect a PGSZ PROT_RW))
        (ev_step_post L (EMprotect a PGSZ PROT_RW) G s0).
Proof.
  intros L G s0 b l k HG Hq Hin Hk2 a. unfold ev_step.
  rewrite round_up_pg_eq in Hk2. fold (mmap_len l) in Hk2.
  set (L' := set_metas (map (bump_meta a) (ld_metas L)) L).
  eapply mspec_bind.
  { apply (mspec_sys (NMprotect a PGSZ PROT_RW) (dec_mprotect_rw a PGSZ) _
             (fun x s mo => s = s0 /\ G s mo /\ match x with RgErr e => (e = EINVAL \/ e = ENOMEM) /\ KL L (ps_brk s0) mo | RgDone _ => KL L' (ps_brk s0) mo end)).
    intros s mo (-> & HK & HGs). pose proof (KL_ceil_lt63 _ _ _ HK) as Hcl.
    pose proof (kl_metas _ _ _ HK b l k Hin) as (A1 & A2 & A3 & A4 & Ak & Ak1 & A5 & A6 & Ana).
    pose proof (went_In_bounds _ _ _ b l HK (or_intror (ex_intro _ k Hin))) as (_ & B2 & _ & _ & B5 & B6).
    set (nb := mmap_len l) in *. set (h := m_vmmaps mo) in *. set (aw := Z_to_bv 64 a) in *. set (nw := Z_to_bv 64 PGSZ) in *.
    assert (Hab : b + PGSZ <= a /\ a + PGSZ <= b + nb) by (subst a; unfold PGSZ in *; nia).
    assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; unfold PGSZ in *; lia).
    assert (Un : bv_unsigned nw = PGSZ) by (subst nw; apply unsigned_lit; unfold PGSZ; lia).
    assert (Uhi : bv_unsigned (aw + nw)%bv = a + PGSZ).
    { rewrite bv_add_unsigned, Ua, Un. apply bv_wrap_small. unfold bv_modulus, PGSZ in *. lia. }
    assert (Hamod : a mod 4096 = 0). { subst a. unfold PGSZ in *. rewrite Z.add_mod, A3, Z.mod_mul by lia. reflexivity. }
    assert (Hcn : map_contains (vm_noaccess h) aw nw = true).
    { destruct (Ana (1 + k) ltac:(lia) ltac:(lia)) as (e & He & Hel & Heh). unfold map_contains. apply existsb_exists. exists e. split; [exact He|].
      rewrite Ua, Un. unfold elo, ehi in Hel, Heh. subst a. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
    assert (Hcm : map_contains (vm_maps h) aw nw = true).
    { unfold map_contains. apply existsb_exists. exists (went b nb). split; [exact A5|]. rewrite Ua, Un. unfold elo, ehi in B5, B6. rewrite B5.
      replace (bv_unsigned (fst (went b nb)) + bv_unsigned (snd (went b nb))) with (b + nb) by (symmetry; exact B6).
      rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
    split.
    { unfold nsafe. cbv zeta. fold h aw nw. rewrite Un. change (page_round_up_Z PGSZ) with PGSZ. fold nw. split; [exact Hcn| exact Hcm]. }
    intros rsp mo' evs Hst.
    pose proof (minv_preserved' _ _ _ _ _ (kl_minv _ _ _ HK) (kl_halt _ _ _ HK) Hst ltac:(nores)) as [Hh' Hmi'].
    pose proof (nstep_dec_mprotect a PGSZ PROT_RW mo rsp mo' evs ltac:(unfold PGSZ in *; lia) ltac:(unfold PGSZ; lia) Hst) as (_ & Hvo & x & Hd & Hx).
    change (mmap_len PGSZ) with PGSZ in Hx. fold h aw nw in Hx.
    assert (HdRW : dec_mprotect_rw a PGSZ rsp = Some x).
    { destruct x as [e|[|]].
      - destruct Hx as [He _]. unfold dec_mprotect_rw. rewrite Hd.
        replace (e =? ENOSYS) with false by (symmetry; apply Z.eqb_neq; subst e; unfold EINVAL, ENOMEM, ENOSYS; lia). reflexivity.
      - unfold dec_mprotect_rw. rewrite Hd. reflexivity.
      - exfalso. apply (nstep_mprotect_rgfalse a PGSZ mo rsp mo' evs ltac:(unfold PGSZ in *; lia) ltac:(unfold PGSZ; lia) ltac:(change (mmap_len PGSZ) with PGSZ; unfold PGSZ; lia)); [| exact Hst | exact Hd].
        change (mmap_len PGSZ) with PGSZ. exact Hcn. }
    exists x. split; [exact HdRW|]. split; [reflexivity|]. split; [eapply HG; [reflexivity|reflexivity| exact Hvo| exact HGs]|].
    pose proof (kl_distinct _ _ _ HK) as Kd. pose proof (List.NoDup_app_remove_l _ _ Kd) as Kdm.

    assert (Dother : forall b0 l0, (In (b0, l0) (ld_groups L) \/ exists k0, In (b0, l0, k0) (ld_metas L)) -> b0 <> b ->
                     b0 + mmap_len l0 <= b \/ b + nb <= b0).
    { intros b0 l0 H Hne. pose proof (went_In_bounds _ _ _ b0 l0 HK H) as (C1 & C2 & C3 & C4 & C5 & C6).
      destruct (pwdisj_In _ _ _ (proj2 (kl_wf _ _ _ HK)) C4 A5) as [E|D].
      - exfalso. apply Hne. apply (f_equal elo) in E. rewrite C5, B5 in E. exact E.
      - unfold edisj in D. rewrite C5, C6, B5, B6 in D. lia. }
    assert (KLnew : forall noacc',
              (forall e x y, In e (vm_noaccess h) -> elo e <= x -> x < y -> y <= ehi e -> y <= 2^64 -> (y <= a \/ a + PGSZ <= x) ->
                  exists e', In e' noacc' /\ elo e' <= x /\ y <= ehi e') ->
              (forall e, In e noacc' -> elo e < ehi e /\ exists e', In e' (vm_maps h) /\ elo e' <= elo e /\ ehi e <= ehi e'
                                                          /\ (forall b l, In (b, l) (ld_groups L) -> elo e' <> b)) ->
              m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (vm_maps h) noacc' (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) ->
              KL L' (ps_brk s0) mo').
    { intros noacc' Hna Hna2 Evm.
      assert (Hph' : phase_inv (ld_brk L') L' (ps_brk s0) mo') by (eapply phase_quiet; [exact HK| exact Hq| reflexivity| reflexivity| rewrite Evm; reflexivity| rewrite Evm; reflexivity]).
      subst L'. kl_open HK. constructor; try exact Hph'; rewrite ?Evm; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk set_metas ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live ld_ceil]; auto; try kl_ceil_close Kceil.
      - intros b0 l0 k0' Hin0. apply in_map_iff in Hin0 as ([[b1 l1] k0] & Eb & Hin1).
        specialize (Kme b1 l1 k0 Hin1). destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
        unfold bump_meta in Eb. destruct (Z.eqb_spec (b1 + (1 + k0) * PGSZ) a) as [Ea|Na]; injection Eb as -> -> <-.
        +
          assert (Eb0 : b0 = b).
          { destruct (Z.eq_dec b0 b) as [E|Hne]; [exact E|]. exfalso.
            pose proof (Dother b0 l0 (or_intror (ex_intro _ k0 Hin1)) Hne) as D. pose proof (mmap_len_ge l0 G0). clear -D Ea Hab G5 G6 H. unfold PGSZ in *. nia. }
          subst b0. pose proof (nodup_map_inj _ _ _ _ Kdm Hin1 Hin (eq_refl b)) as E. injection E as -> ->.
          splits; try assumption; try lia.
          intros q Hq1 Hq2. destruct (G9 q ltac:(lia) Hq2) as (e & He & Hel & Heh).
          apply (Hna e (b + q * PGSZ) (b + q * PGSZ + PGSZ) He Hel ltac:(unfold PGSZ; lia) Heh ltac:(unfold PGSZ in *; lia)). right. subst a. clear -Hq1. unfold PGSZ in *. nia.
        + splits; try assumption.
          intros q Hq1 Hq2. destruct (G9 q Hq1 Hq2) as (e & He & Hel & Heh).
          apply (Hna e (b0 + q * PGSZ) (b0 + q * PGSZ + PGSZ) He Hel ltac:(unfold PGSZ; lia) Heh ltac:(unfold PGSZ in *; lia)).
          destruct (Z.eq_dec b0 b) as [->|Hne].
          { pose proof (nodup_map_inj _ _ _ _ Kdm Hin1 Hin (eq_refl b)) as E. injection E as -> ->. exfalso. apply Na. reflexivity. }
          pose proof (Dother b0 l0 (or_intror (ex_intro _ k0 Hin1)) Hne) as D. clear -D Hab Hq1 Hq2 G5. unfold PGSZ in *. nia.
      - rewrite map_base_bump. exact Kd. }
    destruct x as [e|[|]].
    - destruct Hx as [He ->]. split; [right; exact He| exact HK].
    - destruct Hx as (_ & Evm). apply (KLnew (maps_subtract (vm_noaccess h) (bv_unsigned aw) (bv_unsigned aw + bv_unsigned nw))); [| |exact Evm].
      2:{ intros e1 He1. destruct (maps_subtract_piece _ _ _ _ (kl_noacc_wf _ _ _ HK) He1) as (e2 & He2 & Q1 & Q2 & Q3 & Q4 & Q5).
          destruct (kl_noacc _ _ _ HK e2 He2) as (_ & e3 & He3 & U1 & U2 & U3). split; [exact Q3|].
          exists e3. split; [exact He3|]. split; [lia|]. split; [lia| exact U3]. }
      assert (Hlohi : 0 <= bv_unsigned aw < bv_unsigned aw + bv_unsigned nw) by (rewrite Ua, Un; unfold PGSZ in *; lia).
      intros e x y He H1 H2 H3 HY H4. destruct (iv_subtract_contains (fst e) (snd e) (bv_unsigned aw) (bv_unsigned aw + bv_unsigned nw) x y (proj2 Hlohi) HY H1 H2 H3 ltac:(rewrite Ua, Un; exact H4)) as (e' & He' & Hr).
      exists e'. split; [eapply maps_subtract_In_intro; eauto| exact Hr].
    - destruct Hx. }
  intros x. cbn beta. apply mspec_ret. intros s mo (-> & HGs & Hx). unfold ev_step_post.
  cbn [answer_ok event_post]. fold L'. unfold mprotect_answer_ok.
  destruct x as [e|bb].
  - destruct Hx as [He HK]. rewrite is_errno_form_neg by (destruct He as [-> | ->]; unfold EINVAL, ENOMEM; lia).
    replace (neg_errno e =? 0) with false by (symmetry; apply Z.eqb_neq; unfold neg_errno; destruct He as [-> | ->]; unfold EINVAL, ENOMEM; lia).
    replace (neg_errno e =? TWO64 - ENOSYS) with false by (symmetry; apply Z.eqb_neq; unfold neg_errno, TWO64, ENOSYS; destruct He as [-> | ->]; unfold EINVAL, ENOMEM; lia).
    cbn [orb]. splits; auto.
  - cbn [Z.eqb orb]. splits; auto.
Qed.

Lemma round_up_pg_ge : forall x, x <= round_up_pg x.
Proof. intros x. unfold round_up_pg. pose proof (Z.land_nonneg (-x) (PGSZ - 1)). unfold PGSZ in *. lia. Qed.

Lemma ev_step_spec : forall L e (G : PState -> Model -> Prop) s0,
  frame_ok G -> event_pre L e ->
  mspec (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ G s mo) (ev_step e) (ev_step_post L e G s0).
Proof.
  intros L e G s0 HG Hpre. destruct e as [req|addr len prot flags|addr len|addr len prot|? ? ?|?]; cbn [event_pre] in Hpre; try contradiction.
  - destruct Hpre as [[-> Hph]|[(cur & Hph & ->)|(b & l & Hph & Hreg & ->)]].
    + unfold ev_step. cbn [Z.eqb]. apply ev_brk0_ok; assumption.
    + destruct (Z.eqb_spec (round_up_pg cur + 2 * PGSZ) 0) as [E|NE].
      * intros s mo (-> & HK & _). exfalso. pose proof (kl_phase _ _ _ HK) as Kph. rewrite Hph in Kph. destruct Kph as (Ecur & _).
        pose proof (kl_start _ _ _ HK) as (S1 & _). pose proof (round_up_pg_ge cur). unfold PGSZ in *. lia.
      * unfold ev_step. rewrite (proj2 (Z.eqb_neq _ _) NE). apply ev_brk_grow1_ok; assumption.
    + destruct (Z.eqb_spec (b + l + PGSZ) 0) as [E|NE].
      * intros s mo (-> & HK & _). exfalso. pose proof (kl_brkreg _ _ _ HK b l Hreg) as (R1 & R2 & R3 & _). unfold PGSZ in *. lia.
      * unfold ev_step. rewrite (proj2 (Z.eqb_neq _ _) NE). apply ev_brk_grow2_ok; assumption.
  - destruct Hpre as [(Hq & -> & -> & Hprot & Hlen)|(cur & Hph & -> & -> & -> & ->)].
    + apply ev_mmap_ok; assumption.
    + apply ev_mmap_fixed_ok; assumption.
  - destruct Hpre as (Hq & l0 & Hin & Hlen). apply (ev_munmap_ok L G s0 addr l0 len); assumption.
  - destruct Hpre as (Hq & -> & -> & b & l & k & Hin & -> & Hk). apply (ev_mprotect_ok L G s0 b l k); assumption.
Qed.

Lemma membed_spec {R} : forall (t : stree ev Z R) (Post : mled -> R -> Prop) (G : PState -> Model -> Prop) L s0,
  frame_ok G -> ctree_ok L t Post ->
  mspec (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ G s mo) (membed t)
        (fun r s mo => exists L', cpath L t L' r /\ Post L' r /\ KL L' (ps_brk s) mo /\ G s mo
                       /\ ps_m s = ps_m s0 /\ ps_fa s = ps_fa s0 /\ ps_so s = ps_so s0).
Proof.
  intros t. induction t as [r|e k IH]; intros Post G L s0 HG Hok.
  - cbn [membed]. apply mspec_ret. intros s mo (-> & HK & HGs). pose proof (KL_ceil_lt63 _ _ _ HK) as Hcl. exists L.
    split; [constructor|]. cbn in Hok. splits; auto.
  - cbn [membed]. cbn in Hok. destruct Hok as [Hpre Hk].
    eapply mspec_bind; [apply (ev_step_spec L e G s0 HG Hpre)|].
    intros z. unfold ev_step_post. apply mspec_pointwise. intros s1 mo1 (Hans & HK1 & HG1 & Hm & Hfa & Hso).
    eapply mspec_conseq; [apply (IH z Post G (event_post L e z) s1 HG (Hk z Hans))| |].
    + intros s mo [-> ->]. auto.
    + intros r s mo (L' & Hp & HP & HK & HG' & Hm' & Hfa' & Hso'). exists L'. split; [econstructor; eauto|].
      splits; auto; congruence.
Qed.

Definition OWN (X : list bptr) (G : PState -> Model -> Prop) : assn PState := fun s mo =>
  (exists L, creach2 (ps_m s) L /\ KL L (ps_brk s) mo /\ incl (map fst X) (ld_live L))
  /\ List.NoDup (map fst X) /\ G s mo.

Lemma OWN_G : forall X G s mo, OWN X G s mo -> G s mo.
Proof. intros X G s mo [_ [_ H]]. exact H. Qed.

Lemma OWN_perm : forall X Y G s mo, Permutation X Y -> OWN X G s mo -> OWN Y G s mo.
Proof.
  intros X Y G s mo HP [(L & Hc & HK & Hi) [Hnd HG]].
  assert (HP' : Permutation (map fst X) (map fst Y)) by (apply Permutation_map; exact HP).
  split; [|split; [|exact HG]].
  - exists L. split; [exact Hc|]. split; [exact HK|]. intros c Hc'. apply Hi.
    eapply Permutation_in; [apply Permutation_sym; exact HP'| exact Hc'].
  - eapply Permutation_NoDup; [exact HP'| exact Hnd].
Qed.

Lemma OWN_weakG : forall X G G' s mo, OWN X G s mo -> (G s mo -> G' s mo) -> OWN X G' s mo.
Proof. intros X G G' s mo [A [B C]] H. split; [exact A|]. split; [exact B|]. auto. Qed.

Lemma OWN_other : forall X G s s' mo, OWN X G s mo -> ps_m s' = ps_m s -> ps_brk s' = ps_brk s -> G s' mo -> OWN X G s' mo.
Proof.
  intros X G s s' mo [(L & Hc & HK & Hi) [Hnd HG]] Hm Hb HG'. split; [|split; [exact Hnd|exact HG']].
  exists L. rewrite Hm, Hb. auto.
Qed.

Lemma OWN_nodup : forall X G s mo, OWN X G s mo -> List.NoDup (map fst X).
Proof. intros X G s mo [_ [H _]]. exact H. Qed.

Lemma KL_set_live : forall L v pbrk mo, KL L pbrk mo -> KL (set_live v L) pbrk mo.
Proof. intros L v pbrk mo K. destruct K; constructor; cbn; auto. Qed.

Lemma event_post_live : forall L e z, ld_live (event_post L e z) = ld_live L.
Proof.
  intros L e z. destruct e; cbn; repeat (destruct (_ =? _)); try reflexivity;
  try (destruct (ld_brk L); try reflexivity; destruct (ld_brkreg L) as [[? ?]|]; reflexivity);
  try (destruct (is_err z); reflexivity); try (destruct (_ || _); reflexivity).
Qed.

Lemma cpath_live {R} : forall L (t : stree ev Z R) L' r, cpath L t L' r -> ld_live L' = ld_live L.
Proof. intros L t L' r H. induction H; [reflexivity|]. rewrite IHcpath. apply event_post_live. Qed.

Lemma aptr_eqb_eq : forall a b, aptr_eqb a b = true <-> a = b.
Proof.
  intros [a1 a2] [b1 b2]. unfold aptr_eqb. cbn. rewrite andb_true_iff, N.eqb_eq, Z.eqb_eq.
  split; [intros [-> ->]; reflexivity| intros H; inversion H; auto].
Qed.

Lemma in_ap_remove : forall x c l, In x l -> x <> c -> In x (ap_remove c l).
Proof.
  intros x c l. induction l as [|y l IH]; intros Hin Hne; [destruct Hin|].
  cbn. destruct (aptr_eqb y c) eqn:E.
  - apply aptr_eqb_eq in E. subst y. destruct Hin as [->|Hin]; [congruence| exact Hin].
  - destruct Hin as [->|Hin]; [left; reflexivity| right; apply IH; assumption].
Qed.

Lemma cmalloc_overflow : forall cs n, size_overflows n = true -> cmalloc cs n = SRet (strip cs, None).
Proof. intros cs n H. unfold cmalloc, malloc_core. rewrite H. reflexivity. Qed.

