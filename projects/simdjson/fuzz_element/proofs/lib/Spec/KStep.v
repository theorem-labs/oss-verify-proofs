(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim Monad MSafe STree Malloc Prog KInv.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
Section WithCeiling. Context {CE__ : Ceiling}.

Lemma PGSZ_eq : PGSZ = 4096. Proof. reflexivity. Qed.
Lemma page_size_eq : page_size = 4096. Proof. reflexivity. Qed.

Lemma land_4095 : forall x, Z.land x 4095 = x mod 4096.
Proof. intros x. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma round_up_pg_aligned : forall x, x mod 4096 = 0 -> round_up_pg x = x.
Proof.
  intros x Hx. unfold round_up_pg. rewrite PGSZ_eq. change (4096 - 1) with 4095. rewrite land_4095.
  assert ((- x) mod 4096 = 0). { apply Z.mod_opp_l_z; lia. } lia.
Qed.

Lemma round_up_pg_eq : forall x, round_up_pg x = page_round_up_Z x.
Proof.
  intros x. unfold round_up_pg, page_round_up_Z. rewrite PGSZ_eq, page_size_eq. change (4096 - 1) with 4095. rewrite land_4095.
  pose proof (Z.mod_pos_bound (-x) 4096 ltac:(lia)) as H1.
  pose proof (Z_div_mod_eq_full (-x) 4096) as H2.
  pose proof (Z_div_mod_eq_full (x + 4095) 4096) as H3.
  pose proof (Z.mod_pos_bound (x + 4095) 4096 ltac:(lia)) as H4.
  nia.
Qed.

Lemma mmap_len_ge : forall l, 0 < l -> l <= mmap_len l < l + 4096.
Proof. intros. apply mmap_len_bound. assumption. Qed.

Lemma mmap_len_aligned : forall l, (mmap_len l) mod 4096 = 0.
Proof. intros. unfold mmap_len, page_round_up_Z. rewrite page_size_eq. apply Z_mod_mult. Qed.

Lemma mmap_len_of_aligned : forall l, 0 <= l -> l mod 4096 = 0 -> mmap_len l = l.
Proof. intros l Hl Ha. unfold mmap_len, page_round_up_Z. rewrite page_size_eq. pose proof (Z_div_mod_eq_full l 4096). pose proof (Z_div_mod_eq_full (l + 4095) 4096). pose proof (Z.mod_pos_bound (l+4095) 4096). nia. Qed.

Lemma unsigned_wz : forall z, 0 <= z < 2^64 -> bv_unsigned (wz z) = z.
Proof. intros. unfold wz. apply unsigned_lit. assumption. Qed.

Lemma alloc_ceiling_lt : alloc_ceiling < 2^63.
Proof. apply alloc_ceiling_lt_2p63. Qed.

Lemma elo_went : forall b n, 0 <= b < 2^64 -> elo (went b n) = b.
Proof. intros. unfold elo, went. cbn [fst]. apply unsigned_wz. assumption. Qed.
Lemma ehi_went : forall b n, 0 <= b < 2^64 -> 0 <= n < 2^64 -> ehi (went b n) = b + n.
Proof. intros. unfold ehi, went. cbn [fst snd]. rewrite !unsigned_wz by assumption. reflexivity. Qed.

Lemma pwdisj_In : forall l e1 e2, pwdisj l -> In e1 l -> In e2 l -> e1 = e2 \/ edisj e1 e2.
Proof.
  induction l as [|e l IH]; intros e1 e2 Hp H1 H2; [destruct H1|].
  inversion Hp; subst. destruct H1 as [<-|H1], H2 as [<-|H2].
  - left; reflexivity.
  - right. apply H3. exact H2.
  - right. pose proof (H3 _ H1) as D. unfold edisj in *. lia.
  - apply IH; assumption.
Qed.

Lemma region_free_app_r : forall l1 l2 a n, region_free (l1 ++ l2) a n = true -> region_free l2 a n = true.
Proof. induction l1 as [|[e sz] l1 IH]; intros l2 a n H; [exact H|]. cbn in H. apply andb_prop in H as [_ H]. apply IH. exact H. Qed.

Lemma region_free_shrink : forall maps a n n',
  region_free maps a n' = true -> bv_unsigned n <= bv_unsigned n' -> region_free maps a n = true.
Proof.
  induction maps as [|[e sz] maps IH]; intros a n n' H Hle; [reflexivity|].
  cbn [region_free] in *. apply andb_prop in H as [H1 H2]. rewrite (IH _ _ _ H2 Hle), andb_true_r.
  unfold iv_overlap in *. apply Bool.negb_true_iff in H1. apply Bool.negb_true_iff.
  apply Bool.andb_false_iff in H1. apply Bool.andb_false_iff.
  destruct H1 as [H1|H1]; [left; exact H1| right]. apply Z.ltb_ge in H1. apply Z.ltb_ge. lia.
Qed.

Lemma region_free_disj : forall maps a n e, region_free maps a n = true -> In e maps ->
  bv_unsigned a + bv_unsigned n <= elo e \/ ehi e <= bv_unsigned a.
Proof. intros maps a n [e sz] H Hin. unfold elo, ehi. cbn. eapply region_free_In; eauto. Qed.

Lemma vmwf_cons : forall maps a n, vmwf maps ->
  bv_unsigned a < bv_unsigned a + bv_unsigned n <= 2^64 ->
  region_free maps a n = true ->
  vmwf ((a, n) :: maps).
Proof.
  intros maps a n [Hb Hp] Hn Hrf. split.
  - intros e [<-|Hin]; [unfold elo, ehi; cbn; lia| apply Hb; exact Hin].
  - constructor; [|exact Hp]. intros e' Hin. pose proof (region_free_disj _ _ _ _ Hrf Hin). unfold edisj, elo, ehi in *. cbn. lia.
Qed.

Lemma pwdisj_filter : forall (f : word * word -> bool) l, pwdisj l -> pwdisj (List.filter f l).
Proof.
  induction l as [|e l IH]; intros Hp; [constructor|]. inversion Hp; subst. cbn. destruct (f e).
  - constructor; [|apply IH; assumption]. intros e' Hin. apply List.filter_In in Hin as [Hin _]. auto.
  - apply IH; assumption.
Qed.

Lemma vmwf_remove : forall maps a, vmwf maps -> vmwf (map_remove maps a).
Proof.
  intros maps a [Hb Hp]. unfold map_remove. split.
  - intros e Hin. apply List.filter_In in Hin as [Hin _]. auto.
  - apply pwdisj_filter. exact Hp.
Qed.

Lemma iv_subtract_sub : forall a sz lo hi e, 0 <= lo -> 0 < bv_unsigned sz -> bv_unsigned a + bv_unsigned sz <= 2^64 ->
  In e (iv_subtract a sz lo hi) -> bv_unsigned a <= elo e /\ ehi e <= bv_unsigned a + bv_unsigned sz /\ elo e < ehi e.
Proof.
  intros a sz lo hi e Hlo Hsz Hwf Hin. unfold iv_subtract in Hin.
  pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 sz). unfold bv_modulus in *.
  apply in_app_or in Hin as [Hin|Hin].
  - destruct (Z.ltb_spec (bv_unsigned a) lo); [|destruct Hin].
    destruct Hin as [<-|[]]. unfold elo, ehi. cbn. rewrite unsigned_lit by lia. lia.
  - destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); [|destruct Hin].
    destruct Hin as [<-|[]]. unfold elo, ehi. cbn. rewrite !unsigned_lit by lia. lia.
Qed.

Lemma maps_subtract_In : forall maps lo hi e, In e (maps_subtract maps lo hi) ->
  exists e0, In e0 maps /\ In e (iv_subtract (fst e0) (snd e0) lo hi).
Proof.
  induction maps as [|[a sz] maps IH]; intros lo hi e Hin; [destruct Hin|].
  cbn in Hin. apply in_app_or in Hin as [Hin|Hin].
  - exists (a, sz). split; [left; reflexivity| exact Hin].
  - destruct (IH _ _ _ Hin) as (e0 & H0 & H1). exists e0. split; [right; exact H0| exact H1].
Qed.

Lemma iv_subtract_disjoint : forall a sz lo hi,
  bv_unsigned a < bv_unsigned a + bv_unsigned sz <= 2^64 -> lo < hi ->
  (bv_unsigned a + bv_unsigned sz <= lo \/ hi <= bv_unsigned a) ->
  iv_subtract a sz lo hi = [(a, sz)].
Proof.
  intros a sz lo hi Hwf Hlh Hd. unfold iv_subtract.
  pose proof (bv_unsigned_in_range 64 a). unfold bv_modulus in *.
  destruct Hd as [Hd|Hd].
  - replace (bv_unsigned a <? lo) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (hi <? bv_unsigned a + bv_unsigned sz) with false by (symmetry; apply Z.ltb_ge; lia).
    cbn. rewrite Z.min_l by lia. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - replace (bv_unsigned a <? lo) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (hi <? bv_unsigned a + bv_unsigned sz) with true by (symmetry; apply Z.ltb_lt; lia).
    cbn. rewrite Z.max_l by lia. replace (bv_unsigned a + bv_unsigned sz - bv_unsigned a) with (bv_unsigned sz) by lia.
    rewrite !Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma maps_subtract_keep : forall maps lo hi e, vmwf maps -> lo < hi ->
  In e maps -> (ehi e <= lo \/ hi <= elo e) -> In e (maps_subtract maps lo hi).
Proof.
  induction maps as [|[a sz] maps IH]; intros lo hi e Hwf Hlh Hin Hd; [destruct Hin|].
  destruct Hwf as [Hb Hp]. cbn. apply in_or_app. destruct Hin as [<-|Hin].
  - left. rewrite iv_subtract_disjoint; [left; reflexivity| | exact Hlh|].
    + specialize (Hb (a, sz) (or_introl eq_refl)). unfold elo, ehi in Hb. cbn in Hb. lia.
    + unfold elo, ehi in Hd. cbn in Hd. lia.
  - right. apply IH; auto. split; [intros e' H'; apply Hb; right; exact H'| inversion Hp; assumption].
Qed.

Lemma iv_subtract_contains : forall a sz lo hi x y,
  0 <= lo -> lo < hi < 2^64 ->
  bv_unsigned a <= x -> x < y -> y <= bv_unsigned a + bv_unsigned sz ->
  (y <= lo \/ hi <= x) ->
  exists e, In e (iv_subtract a sz lo hi) /\ elo e <= x /\ y <= ehi e.
Proof.
  intros a sz lo hi x y Hlo Hlh Hax Hxy Hy Hd. unfold iv_subtract.
  pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 sz). unfold bv_modulus in *.
  destruct Hd as [Hd|Hd].
  - replace (bv_unsigned a <? lo) with true by (symmetry; apply Z.ltb_lt; lia).
    eexists. split; [apply in_or_app; left; left; reflexivity|]. unfold elo, ehi; cbn. rewrite unsigned_lit by lia. lia.
  - replace (hi <? bv_unsigned a + bv_unsigned sz) with true by (symmetry; apply Z.ltb_lt; lia).
    eexists. split; [apply in_or_app; right; left; reflexivity|]. unfold elo, ehi; cbn. rewrite !unsigned_lit by lia. lia.
Qed.

Lemma maps_subtract_In_intro : forall maps lo hi e e', In e maps -> In e' (iv_subtract (fst e) (snd e) lo hi) ->
  In e' (maps_subtract maps lo hi).
Proof.
  induction maps as [|[a sz] maps IH]; intros lo hi e e' Hin H'; [destruct Hin|].
  cbn. apply in_or_app. destruct Hin as [<-|Hin]; [left; exact H'| right; eapply IH; eauto].
Qed.

Lemma pwdisj_app : forall P R, pwdisj P -> pwdisj R -> (forall p r, In p P -> In r R -> edisj p r) -> pwdisj (P ++ R).
Proof.
  induction P as [|p P IH]; intros R HP HR Hx; [exact HR|]. inversion HP; subst. cbn. constructor.
  - intros e' He'. apply in_app_or in He' as [He'|He']; [auto|]. apply Hx; [left; reflexivity| exact He'].
  - apply IH; auto. intros p' r Hp' Hr. apply Hx; [right; exact Hp'| exact Hr].
Qed.

Lemma iv_subtract_pwdisj : forall a sz lo hi, 0 <= lo -> lo < hi <= 2^64 -> bv_unsigned a + bv_unsigned sz <= 2^64 ->
  pwdisj (iv_subtract a sz lo hi).
Proof.
  intros a sz lo hi Hlo Hlh Hasz. unfold iv_subtract.
  pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 sz). unfold bv_modulus in *.
  destruct (Z.ltb_spec (bv_unsigned a) lo); destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); cbn [app].
  - constructor; [|constructor; [intros e' []| constructor]]. intros e' [<-|[]].
    unfold edisj, elo, ehi; cbn. rewrite !unsigned_lit by lia. left. lia.
  - constructor; [intros e' []| constructor].
  - constructor; [intros e' []| constructor].
  - constructor.
Qed.

Lemma vmwf_subtract : forall maps lo hi, 0 <= lo -> lo < hi <= 2^64 -> vmwf maps -> vmwf (maps_subtract maps lo hi).
Proof.
  induction maps as [|[a sz] maps IH]; intros lo hi Hlo Hlh [Hb Hp]; [split; [intros e []| constructor]|].
  inversion Hp; subst. assert (Hwf' : vmwf maps) by (split; [intros e He; apply Hb; right; exact He| assumption]).
  specialize (IH lo hi Hlo Hlh Hwf'). destruct IH as [IHb IHp].
  assert (Ha : elo (a, sz) < ehi (a, sz) <= 2^64) by (apply Hb; left; reflexivity). unfold elo, ehi in Ha; cbn in Ha.
  cbn. split.
  - intros e Hin. apply in_app_or in Hin as [Hin|Hin]; [|apply IHb; exact Hin].
    pose proof (iv_subtract_sub a sz lo hi e Hlo ltac:(lia) ltac:(lia) Hin). lia.
  - apply pwdisj_app; [apply iv_subtract_pwdisj; [exact Hlo| exact Hlh| lia]| exact IHp|].
    intros e e' He He'. pose proof (iv_subtract_sub a sz lo hi e Hlo ltac:(lia) ltac:(lia) He) as S1.
    destruct (maps_subtract_In _ _ _ _ He') as (e0 & H0 & H0').
    assert (W0 : elo e0 < ehi e0 <= 2^64) by (apply Hb; right; exact H0). destruct e0 as [a0 s0]. unfold elo, ehi in W0; cbn in W0.
    pose proof (iv_subtract_sub a0 s0 lo hi e' Hlo ltac:(lia) ltac:(lia) H0') as S2.
    pose proof (H1 _ H0) as D. unfold edisj, elo, ehi in *. cbn in *. lia.
Qed.

Lemma wcov_mono : forall maps maps' lo hi, (forall e, In e maps -> In e maps') -> wcov maps lo hi -> wcov maps' lo hi.
Proof. intros maps maps' lo hi Hs Hc x Hx. destruct (Hc x Hx) as (e & He & Hr). exists e. auto. Qed.

Lemma nstep_brk_inv : forall req mo rsp mo' evs,
  nstep (NBrk req) mo rsp mo' evs ->
  let h := m_vmmaps mo in
  exists r, brk_r_ok mo (Z_to_bv 64 req) r = true
    /\ mo' = with_brk_next mo (Z_to_bv 64 req) r
    /\ rsp = mkEffectU r [] (brk_zeros (Z_to_bv 64 req) r (vm_brk h)) (brk_unmaps r (vm_brk h)) [] []
    /\ evs = [].
Proof.
  intros req mo rsp mo' evs Step h.
  destruct (proj1 (nstep_brk_spec req mo rsp mo' evs) Step) as (NoEvents & Outcome & _).
  destruct (proj1 (brk_outcome _ _ _ _) Outcome) as (ret & RetOk & Same).
  injection Same as SameRsp SameModel SameEvs.
  exists ret. refine (conj RetOk (conj SameModel (conj SameRsp NoEvents))).
Qed.

Lemma m_vmmaps_with_brk_next' : forall mo req r,
  m_vmmaps (with_brk_next mo req r) = brk_model_next (m_vmmaps mo) req r.
Proof. intros. apply m_vmmaps_with_brk_next. Qed.

Lemma maps_subtract_ranges_nil : forall maps, maps_subtract_ranges maps [] = maps.
Proof. reflexivity. Qed.

Lemma brk_model_next_query : forall h,
  let h' := brk_model_next h (Z_to_bv 64 0) (vm_brk h) in
  vm_reserved h' = vm_reserved h /\ vm_maps h' = vm_maps h /\ vm_noaccess h' = vm_noaccess h
  /\ vm_start_brk h' = vm_start_brk h /\ vm_brk h' = vm_brk h.
Proof.
  intros h. cbn [brk_model_next vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk].
  unfold brk_maps_next. rewrite Z.ltb_irrefl, andb_false_r. unfold brk_grants, brk_is_grow. change (w_is0 (Z_to_bv 64 0)) with true. cbn [negb andb app].
  unfold brk_unmaps, brk_page_range. rewrite Z.ltb_irrefl. destruct (0 <? _); cbn; repeat split; reflexivity.
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
  unfold brk_unmaps, brk_page_range. rewrite Z.ltb_irrefl. destruct (0 <? _); cbn; repeat split; reflexivity.
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
  rewrite Hsub. destruct (0 <? b); cbn; repeat split; reflexivity.
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
  alloc_top h = alloc_ceiling ->
  0 < b -> b < req < 2^64 -> b mod 4096 = 0 -> req mod 4096 = 0 ->
  brk_grow_ok m (Z_to_bv 64 req) (Z_to_bv 64 req) = true ->
  req <= alloc_ceiling /\ region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 b) (Z_to_bv 64 (req - b)) = true.
Proof.
  intros m req h b Htop Hb Hreq Hba Hra H. pose proof alloc_ceiling_lt as Hcl.
  unfold brk_grow_ok, brk_budget_ok in H. fold h in H. rewrite unsigned_lit in H by lia. fold b in H.
  replace (0 <? b) with true in H by (symmetry; apply Z.ltb_lt; lia).
  replace (b <? req) with true in H by (symmetry; apply Z.ltb_lt; lia). cbn [andb] in H.
  unfold page_round_up_Z in H. rewrite page_size_eq in H.
  replace ((b + 4096 - 1) / 4096 * 4096) with b in H.
  2:{ pose proof (Z_div_mod_eq_full b 4096). pose proof (Z_div_mod_eq_full (b+4096-1) 4096). pose proof (Z.mod_pos_bound (b+4096-1) 4096). nia. }
  replace ((req + 4096 - 1) / 4096 * 4096) with req in H.
  2:{ pose proof (Z_div_mod_eq_full req 4096). pose proof (Z_div_mod_eq_full (req+4096-1) 4096). pose proof (Z.mod_pos_bound (req+4096-1) 4096). nia. }
  replace (b <? req) with true in H by (symmetry; apply Z.ltb_lt; lia).
  apply andb_prop in H as [H _]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1.
  rewrite Htop in H1. split; [exact H1|].
  apply (region_free_shrink _ _ _ _ H2). rewrite !unsigned_lit; lia.
Qed.

Lemma nstep_mmap_fixed_inv : forall a mo rsp mo' evs,
  let h := m_vmmaps mo in
  let aw := Z_to_bv 64 a in let n := Z_to_bv 64 PGSZ in
  alloc_top h = alloc_ceiling ->
  0 < a -> a + PGSZ <= alloc_ceiling -> a mod 4096 = 0 ->
  region_free (vm_reserved h) aw n = true -> map_contains (vm_maps h) aw n = true ->
  nstep (NMmap a PGSZ PROT_NONE MAPFX) mo rsp mo' evs ->
  evs = [] /\ vm_only mo mo' /\
  exists x, dec_mmap_fixed a PGSZ rsp = Some x /\
  match x with
  | FxKept e => False
  | FxDone => m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (vm_maps h) ((aw, n) :: maps_subtract (vm_noaccess h) a (a + PGSZ))
                                         (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
  | FxLost e => False
  end.
Proof.
  intros a mo rsp mo' evs h aw n AtTop APos AFits AAligned ResvFree MapsHave Step.
  pose proof alloc_ceiling_lt as CeilBound.
  assert (AwVal : bv_unsigned aw = a) by (apply unsigned_lit; unfold PGSZ in AFits; lia).
  assert (NoRes : mmap_noreserve_b (Z_to_bv 64 MAPFX) = false) by reflexivity.
  destruct (nstep_mm_vm_only (NMmap a PGSZ PROT_NONE MAPFX) mo rsp mo' evs NoRes Step) as (Shape & NoEvents & _).
  assert (NWidth : bv_unsigned n = 4096) by reflexivity.
  assert (Rounded : page_round_up_Z (bv_unsigned n) = 4096) by (rewrite NWidth; reflexivity).
  assert (OffOk : mmap_off_aligned_b (Z_to_bv 64 0) = true) by reflexivity.
  assert (AnonOk : mmap_anon_b (Z_to_bv 64 MAPFX) = true) by reflexivity.
  assert (LenNonzero : w_is0 n = false) by reflexivity.
  assert (NotPlain : mmap_modeled_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 MAPFX) (Z_to_bv 64 0) = false) by reflexivity.
  assert (NotFloating : mmap_noaccess_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 MAPFX) (Z_to_bv 64 0) = false) by reflexivity.
  assert (FixedNone : mmap_fixed_noaccess_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 MAPFX) (Z_to_bv 64 0) = true) by reflexivity.
  assert (NoWrap : (two_pow_64 <=? a + 4096) = false) by (apply Z.leb_gt; unfold two_pow_64; unfold PGSZ in AFits; lia).
  assert (BelowTop : (a + 4096 <=? alloc_top h) = true) by (apply Z.leb_le; rewrite AtTop; unfold PGSZ in AFits; lia).
  assert (PageAligned : (a mod page_size =? 0) = true) by (apply Z.eqb_eq; exact AAligned).
  assert (NonNull : (0 <? a) = true) by (apply Z.ltb_lt; exact APos).
  assert (Placeable : region_free (vm_reserved h) aw n && map_contains (vm_maps h) aw n = true)
    by (rewrite ResvFree, MapsHave; reflexivity).
  set (Mrep := with_mmap_replacement (Z_to_bv 64 MAPFX) aw n
         (with_vmmaps (mkVmMapsFull (vm_reserved h) (vm_maps h) ((aw, n) :: maps_subtract (vm_noaccess h) a (a + 4096))
                         (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) mo)).
  assert (Exact : forall eff mo2 evs2, errno_ret_in mmap_errnos (eff_ret eff) = false ->
    check_mmap aw n (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 MAPFX) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eff mo = CheckOk mo2 evs2 <->
    eff = mkEffectU aw [] [] [(aw, n)] [] [] /\ mo2 = Mrep /\ evs2 = []).
  { intros eff mo2 evs2 Clean.
    unfold check_mmap. cbv zeta. fold h.
    rewrite OffOk, AnonOk, LenNonzero, NotPlain, NotFloating, FixedNone, Rounded, AwVal.
    change (Z_to_bv 64 4096) with n. cbn [negb].
    rewrite NoWrap, BelowTop, PageAligned, NonNull, Placeable, NWidth. cbn [negb].
    destruct eff as [ret writes zeros unmaps copies copyins]. cbn [eff_ret] in Clean.
    split.
    - intros Accepted.
      destruct writes; [|discriminate Accepted]. destruct zeros; [|discriminate Accepted].
      destruct copies; [|discriminate Accepted]. destruct copyins; [|discriminate Accepted].
      rewrite Clean in Accepted.
      destruct (bv_eqb ret aw && listNN_eqb unmaps [(aw, n)]) eqn:Hit; [|discriminate Accepted].
      apply andb_prop in Hit as [RetHit UnmapHit].
      apply bv_eqb_eq in RetHit. apply listNN_eqb_eq in UnmapHit. subst ret unmaps.
      injection Accepted as ModelIs EventsAre. subst mo2 evs2. repeat split.
    - intros (EffIs & ModelIs & EventsAre). subst mo2 evs2.
      injection EffIs as RetIs WritesAre ZerosAre UnmapsAre CopiesAre CopyinsAre.
      subst ret writes zeros unmaps copies copyins.
      rewrite Clean. cbn [listNN_eqb]. rewrite !bv_eqb_refl. reflexivity. }
  assert (AwClean : errno_ret_in mmap_errnos aw = false).
  { apply errno_ret_in_below; [reflexivity|]. rewrite AwVal. unfold two_pow_64. unfold PGSZ in AFits. lia. }
  pose proof (proj2 (Exact (mkEffectU aw [] [] [(aw, n)] [] []) Mrep [] AwClean) (conj eq_refl (conj eq_refl eq_refl))) as Granted.
  pose proof (nstep_mmap_nonrefusal_of_grant _ _ _ _ _ _ _ _ _ _ _ Step Granted AwClean) as RspClean.
  destruct (proj1 (Exact rsp mo' evs RspClean) (nstep_mmap_check _ _ _ _ _ _ _ _ NoRes Step)) as (RspIs & Mo'Is & _).
  assert (AwNoErrno : errno_of aw = None).
  { unfold errno_of. rewrite AwVal. destruct (Z.leb_spec0 (2^64 - 4095) a) as [Big|Small]; [lia| reflexivity]. }
  refine (conj NoEvents (conj Shape (ex_intro _ FxDone (conj _ _)))).
  - rewrite RspIs. unfold dec_mmap_fixed. cbv beta iota.
    change (Z_to_bv 64 (mmap_len PGSZ)) with n. change (Z_to_bv 64 a) with aw.
    rewrite AwNoErrno, !bv_eqb_refl. reflexivity.
  - cbv beta iota. rewrite Mo'Is. reflexivity.
Qed.

End WithCeiling.
Ltac kl_open HK := destruct HK as [Kminv Khalt Kwf Kresv Krt Kstart Kgr Kme Kdis Kreg Kph Ktop].
Section WithCeiling. Context {CE__ : Ceiling}.

Lemma KL_vm_eq : forall L pbrk mo mo',
  KL L pbrk mo -> minv mo' -> m_halted mo' = None ->
  vm_reserved (m_vmmaps mo') = vm_reserved (m_vmmaps mo) ->
  vm_maps (m_vmmaps mo') = vm_maps (m_vmmaps mo) ->
  vm_noaccess (m_vmmaps mo') = vm_noaccess (m_vmmaps mo) ->
  vm_start_brk (m_vmmaps mo') = vm_start_brk (m_vmmaps mo) ->
  vm_brk (m_vmmaps mo') = vm_brk (m_vmmaps mo) ->
  alloc_top (m_vmmaps mo') = alloc_top (m_vmmaps mo) ->
  KL L pbrk mo'.
Proof.
  intros L pbrk mo mo' K Hmi Hh H1 H2 H3 H4 H5 H6. kl_open K; constructor; rewrite ?H1, ?H2, ?H3, ?H4, ?H5, ?H6; auto.
Qed.

Definition phase_inv (ph : brk_phase) (L : mled) (pbrk : Z) (mo : Model) : Prop :=
  match ph with
  | BPUntried => vm_brk (m_vmmaps mo) = vm_start_brk (m_vmmaps mo) /\ ld_brkreg L = None
  | BPQueried cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo))
      /\ bv_unsigned (vm_brk (m_vmmaps mo)) = cur /\ pbrk = cur /\ ld_brkreg L = None
  | BPGuard cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo))
      /\ bv_unsigned (vm_brk (m_vmmaps mo)) = cur + 2 * PGSZ /\ pbrk = cur + 2 * PGSZ
      /\ ld_brkreg L = None /\ cur + 2 * PGSZ <= alloc_ceiling
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
    intros s mo (-> & HK & HGs). split; [exact I|].
    intros rsp mo' evs Hst.
    unshelve epose proof (minv_preserved _ _ _ _ _ (kl_minv _ _ _ HK) (kl_halt _ _ _ HK) _ Hst) as [Hh' Hmi']; [exact I|].
    pose proof (nstep_dec_brk0 _ _ _ _ Hst) as (_ & Hdec & Hvo & Hbrk).
    pose proof (nstep_brk_inv _ _ _ _ _ Hst) as (r & Hr & Emo' & _ & _).
    apply brk_r_ok_query in Hr. subst r.
    pose proof (brk_model_next_query (m_vmmaps mo)) as (E1 & E2 & E3 & E4 & E5).
    exists (bv_unsigned (vm_brk (m_vmmaps mo))). split; [exact Hdec|].
    assert (HK' : KL L (ps_brk s0) mo').
    { eapply KL_vm_eq; [exact HK| exact Hmi'| exact Hh'| | | | | | eapply vm_only_alloc_top; eassumption]; rewrite Emo', m_vmmaps_with_brk_next; assumption. }
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
  splits; auto. eapply (HG s0); [reflexivity|reflexivity| apply vm_only_refl| exact HGs].
Qed.

Lemma mspec_get_bind_eq {St A} (s0 : St) (P : assn St) (f : St -> Monad.M St A) Q :
  mspec (fun s mo => s = s0 /\ P s mo) (f s0) Q -> mspec (fun s mo => s = s0 /\ P s mo) (x <- mget ;; f x) Q.
Proof. intros H s mo [-> HP]. unfold mbind, mget. cbn. apply H. auto. Qed.

Lemma elo_pair : forall a n, elo (a, n) = bv_unsigned a. Proof. reflexivity. Qed.
Lemma ehi_pair : forall a n, ehi (a, n) = bv_unsigned a + bv_unsigned n. Proof. reflexivity. Qed.

Lemma went_In_bounds : forall L pbrk mo b l, KL L pbrk mo ->
  (In (b, l) (ld_groups L) \/ exists k, In (b, l, k) (ld_metas L)) ->
  0 < b /\ 0 < mmap_len l /\ b + mmap_len l <= alloc_ceiling /\ In (went b (mmap_len l)) (vm_maps (m_vmmaps mo))
  /\ elo (went b (mmap_len l)) = b /\ ehi (went b (mmap_len l)) = b + mmap_len l.
Proof.
  intros L pbrk mo b l K Hin. pose proof alloc_ceiling_lt.
  assert (0 < l < LEN_MAX /\ 0 < b /\ b + mmap_len l <= alloc_ceiling /\ In (went b (mmap_len l)) (vm_maps (m_vmmaps mo))) as (Hl & Hb & Hc & Hm).
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
  0 < lo -> 0 < len -> lo + len <= alloc_ceiling ->
  region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 lo) (Z_to_bv 64 len) = true ->
  (forall b l, ld_brkreg L = Some (b, l) -> l mod PGSZ = 0 /\ (b + l <= lo \/ lo + len <= b + PGSZ)) ->
  lbrk_pages_ok L lo len = true.
Proof.
  intros L pbrk mo lo len HK h Hlo Hlen Hceil Hrf Hbrk. pose proof alloc_ceiling_lt as Hcl.
  assert (Ulo : bv_unsigned (Z_to_bv 64 lo) = lo) by (apply unsigned_lit; lia).
  assert (Ulen : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
  pose proof (region_free_app_r _ _ _ _ Hrf) as Hrfm.
  unfold lbrk_pages_ok. rewrite (proj2 (Z.ltb_lt 0 lo)) by lia.
  pose proof ceil_le_MCEIL as HleM.
  rewrite (proj2 (Z.leb_le (lo + len) MCEIL)) by lia. cbn [andb].
  unfold ranges_free. apply forallb_forall. intros [b0 m0] Hin. cbn [fst snd]. unfold iv_disjoint.
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
  intros L G s0 cur HG Hph req. pose proof alloc_ceiling_lt as Hcl.
  apply mspec_get_bind_eq.
  eapply mspec_bind.
  { apply (mspec_sys (NBrk req) (dec_brk (ps_brk s0) req) _
             (fun a s mo => s = s0 /\ G s mo /\ (req <> cur /\ 0 < req) /\ ps_brk s0 = cur /\
                match a with
                | BrkGrown => KL (set_brkph (BPGuard cur) L) req mo /\ lbrk_pages_ok L (round_up_pg cur) (2 * PGSZ) = true
                | BrkSame => KL (set_brkph BPDead L) cur mo
                end)).
    intros s mo (-> & HK & HGs). split; [exact I|].
    intros rsp mo' evs Hst.
    unshelve epose proof (minv_preserved _ _ _ _ _ (kl_minv _ _ _ HK) (kl_halt _ _ _ HK) _ Hst) as [Hh' Hmi']; [exact I|].
    pose proof (kl_phase _ _ _ HK) as Kph. rewrite Hph in Kph. destruct Kph as (Ecur & Ebrk & Epbrk & Ereg).
    pose proof (kl_start _ _ _ HK) as (S1 & S2 & S3 & S4).
    assert (Hreq : req = cur + 2 * PGSZ). { subst req. rewrite round_up_pg_aligned; [reflexivity|]. rewrite Ecur. exact S2. }
    pose proof (nstep_brk_inv _ _ _ _ _ Hst) as (r & Hr & Emo' & _ & _).
    pose proof (nstep_dec_brk req mo rsp mo' evs ltac:(lia) ltac:(lia) ltac:(unfold PGSZ in *; lia) (kl_top _ _ _ HK)
                  ltac:(unfold PGSZ in *; lia) ltac:(unfold PGSZ in *; lia) Hst) as (_ & Hvo & a & Hdec & Ha).
    set (h := m_vmmaps mo) in *.
    rewrite Ebrk in Hdec. rewrite Epbrk. exists a. split; [exact Hdec|].
    split; [reflexivity|]. split; [eapply HG; [reflexivity|reflexivity| exact Hvo| exact HGs]|].
    split; [unfold PGSZ in *; lia|]. split; [reflexivity|].
    apply brk_r_ok_grow in Hr; [| fold h; lia| fold h; unfold PGSZ in *; lia]. fold h in Hr.
    pose proof (brk_model_next_same h (Z_to_bv 64 req)) as (Q1 & Q2 & Q3 & Q4 & Q5).
    pose proof (brk_model_next_grown h req ltac:(lia) ltac:(unfold PGSZ in *; lia)) as (P1 & P2 & P3 & P4 & P5).
    destruct a.
    -
      destruct Hr as [-> | [-> Hgo]].
      { exfalso. rewrite Emo', m_vmmaps_with_brk_next in Ha. rewrite Q5 in Ha.
        apply (f_equal bv_unsigned) in Ha. rewrite unsigned_lit in Ha by (unfold PGSZ in *; lia). lia. }
      apply brk_grow_ok_facts in Hgo; fold h in Hgo; [| exact (kl_top _ _ _ HK) | fold h; lia| fold h; unfold PGSZ in *; lia| fold h; rewrite Ebrk, Ecur; exact S2| rewrite Hreq, Ecur; unfold PGSZ in *; rewrite Z.add_mod, S2 by lia; reflexivity].
      destruct Hgo as [Hceil Hrf].
      assert (HPG : lbrk_pages_ok L (round_up_pg cur) (2 * PGSZ) = true).
      { rewrite round_up_pg_aligned by (rewrite Ecur; unfold PGSZ in S2; exact S2).
        apply (KL_lbrk_pages_ok L (ps_brk s0) mo cur (2 * PGSZ) HK); [lia| unfold PGSZ; lia| lia| | intros b l Hb; rewrite Ereg in Hb; discriminate].
        replace cur with (bv_unsigned (vm_brk h)) at 1 by exact Ebrk. replace (Z_to_bv 64 (2 * PGSZ)) with (Z_to_bv 64 (req - bv_unsigned (vm_brk h))) by (f_equal; lia). exact Hrf. }
      rewrite Z_to_bv_bv_unsigned in Hrf.
      assert (Hn : bv_unsigned (Z_to_bv 64 (req - bv_unsigned (vm_brk h))) = 2 * PGSZ) by (rewrite unsigned_lit; unfold PGSZ in *; lia).
      split; [|exact HPG].
      kl_open HK. constructor; try exact Hmi'; try exact Hh'; rewrite ?Emo', ?m_vmmaps_with_brk_next; cbn [set_brkph ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live];
        rewrite ?P1, ?P2, ?P3, ?P4, ?P5; auto.
      + apply vmwf_cons; [exact Kwf| rewrite Hn; unfold PGSZ in *; lia| eapply region_free_app_r; exact Hrf].
      + rewrite unsigned_lit by (unfold PGSZ in *; lia). splits; try lia; auto.
      + intros b l Hin. specialize (Kgr b l Hin). unfold brk_disj in *. cbn. intuition auto with datatypes.
      + intros b l k Hin. specialize (Kme b l k Hin). unfold brk_disj in *. cbn. intuition auto with datatypes.
      + intros b l Hb. rewrite Ereg in Hb. discriminate.
      + rewrite unsigned_lit by (unfold PGSZ in *; lia). splits; auto; try lia.
        * exists (vm_brk h, Z_to_bv 64 (req - bv_unsigned (vm_brk h))). split; [left; reflexivity|]. rewrite elo_pair, ehi_pair, Hn. lia.
        * intros b l Hin. pose proof (went_In_bounds _ _ _ b l (mkKL _ _ _ Kminv Khalt Kwf Kresv Krt Kstart Kgr Kme Kdis Kreg Kph Ktop) (or_introl Hin)) as (B1 & B2 & B3 & B4 & B5 & B6).
          pose proof (region_free_disj _ _ _ _ (region_free_app_r _ _ _ _ Hrf) B4) as D. rewrite B5, B6, Hn in D. lia.
        * intros b l k Hin. pose proof (went_In_bounds _ _ _ b l (mkKL _ _ _ Kminv Khalt Kwf Kresv Krt Kstart Kgr Kme Kdis Kreg Kph Ktop) (or_intror (ex_intro _ k Hin))) as (B1 & B2 & B3 & B4 & B5 & B6).
          pose proof (region_free_disj _ _ _ _ (region_free_app_r _ _ _ _ Hrf) B4) as D. rewrite B5, B6, Hn in D. lia.
    -
      destruct Hr as [-> | [-> Hgo]].
      2:{ exfalso. rewrite Emo', m_vmmaps_with_brk_next in Ha. rewrite P5 in Ha.
          apply (f_equal bv_unsigned) in Ha. rewrite unsigned_lit in Ha by (unfold PGSZ in *; lia). lia. }
      apply KL_dead with (pbrk := ps_brk s0). eapply KL_vm_eq; [exact HK| exact Hmi'| exact Hh'| | | | | | eapply vm_only_alloc_top; eassumption]; rewrite Emo', m_vmmaps_with_brk_next; assumption. }
  intros a. cbn beta. destruct a.
  - eapply mspec_bind; [apply mspec_upd|]. intros []. apply mspec_ret.
    intros s mo (s1 & -> & -> & HGs & [Hne Hpos] & Ecur & [HK HPG]). unfold ev_step_post.
    cbn [ps_brk set_brk_ps ps_m ps_fa ps_so answer_ok event_post].
    replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Hph, Z.eqb_refl.
    splits; auto.
    + unfold brk_answer_ok. rewrite Z.eqb_refl, HPG. reflexivity.
    + eapply (HG s0); [reflexivity|reflexivity| apply vm_only_refl| exact HGs].
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
  intros L G s0 b l HG Hph Ereg req. pose proof alloc_ceiling_lt as Hcl.
  apply mspec_get_bind_eq.
  eapply mspec_bind.
  { apply (mspec_sys (NBrk req) (dec_brk (ps_brk s0) req) _
             (fun a s mo => s = s0 /\ G s mo /\ (req <> b + l /\ 0 < req) /\ ps_brk s0 = b + l /\
                match a with
                | BrkGrown => KL (set_brkreg (Some (b, l + PGSZ)) L) req mo /\ lbrk_pages_ok L (b + l) PGSZ = true
                | BrkSame => KL (set_brkph BPDead L) (b + l) mo
                end)).
    intros s mo (-> & HK & HGs). split; [exact I|].
    intros rsp mo' evs Hst.
    unshelve epose proof (minv_preserved _ _ _ _ _ (kl_minv _ _ _ HK) (kl_halt _ _ _ HK) _ Hst) as [Hh' Hmi']; [exact I|].
    pose proof (kl_phase _ _ _ HK) as Kph. rewrite Hph in Kph. destruct Kph as (b' & l' & Ereg' & Ebrk & Epbrk).
    rewrite Ereg in Ereg'. injection Ereg' as <- <-.
    pose proof (kl_brkreg _ _ _ HK b l Ereg) as (R1 & R2 & R3 & R4 & R5 & Rcov).
    pose proof (kl_start _ _ _ HK) as (S1 & S2 & S3 & S4).
    pose proof (nstep_brk_inv _ _ _ _ _ Hst) as (r & Hr & Emo' & _ & _).
    pose proof (nstep_dec_brk req mo rsp mo' evs ltac:(lia) ltac:(lia) ltac:(unfold PGSZ in *; lia) (kl_top _ _ _ HK)
                  ltac:(unfold PGSZ in *; lia) ltac:(unfold PGSZ in *; lia) Hst) as (_ & Hvo & a & Hdec & Ha).
    set (h := m_vmmaps mo) in *.
    rewrite Ebrk in Hdec. rewrite Epbrk. exists a. split; [exact Hdec|].
    split; [reflexivity|]. split; [eapply HG; [reflexivity|reflexivity| exact Hvo| exact HGs]|].
    split; [unfold PGSZ in *; lia|]. split; [reflexivity|].
    apply brk_r_ok_grow in Hr; [| fold h; lia| fold h; unfold PGSZ in *; lia]. fold h in Hr.
    pose proof (brk_model_next_same h (Z_to_bv 64 req)) as (Q1 & Q2 & Q3 & Q4 & Q5).
    pose proof (brk_model_next_grown h req ltac:(lia) ltac:(unfold PGSZ in *; lia)) as (P1 & P2 & P3 & P4 & P5).
    destruct a.
    -
      destruct Hr as [-> | [-> Hgo]].
      { exfalso. rewrite Emo', m_vmmaps_with_brk_next in Ha. rewrite Q5 in Ha.
        apply (f_equal bv_unsigned) in Ha. rewrite unsigned_lit in Ha by (unfold PGSZ in *; lia). lia. }
      apply brk_grow_ok_facts in Hgo; fold h in Hgo; [| exact (kl_top _ _ _ HK) | fold h; lia| fold h; unfold PGSZ in *; lia| fold h; rewrite Ebrk; unfold PGSZ in *; rewrite Z.add_mod, R2, R4 by lia; reflexivity| subst req; unfold PGSZ in *; rewrite Z.add_mod, (Z.add_mod b l), R2, R4 by lia; reflexivity].
      destruct Hgo as [Hceil Hrf].
      assert (HPG : lbrk_pages_ok L (b + l) PGSZ = true).
      { apply (KL_lbrk_pages_ok L (ps_brk s0) mo (b + l) PGSZ HK); [lia| unfold PGSZ; lia| subst req; lia| |].
        - replace (b + l) with (bv_unsigned (vm_brk h)) at 1 by exact Ebrk. replace (Z_to_bv 64 PGSZ) with (Z_to_bv 64 (req - bv_unsigned (vm_brk h))) by (f_equal; lia). exact Hrf.
        - intros b1 l1 E. rewrite Ereg in E. injection E as <- <-. split; [exact R4| left; lia]. }
      rewrite Z_to_bv_bv_unsigned in Hrf.
      assert (Hn : bv_unsigned (Z_to_bv 64 (req - bv_unsigned (vm_brk h))) = PGSZ) by (rewrite unsigned_lit; unfold PGSZ in *; lia).
      pose proof (fun b0 l0 H => went_In_bounds _ _ _ b0 l0 HK H) as WB.
      split; [|exact HPG].
      kl_open HK. constructor; try exact Hmi'; try exact Hh'; rewrite ?Emo', ?m_vmmaps_with_brk_next; cbn [set_brkreg ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live];
        rewrite ?P1, ?P2, ?P3, ?P4, ?P5; auto.
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
    -
      destruct Hr as [-> | [-> Hgo]].
      2:{ exfalso. rewrite Emo', m_vmmaps_with_brk_next in Ha. rewrite P5 in Ha.
          apply (f_equal bv_unsigned) in Ha. rewrite unsigned_lit in Ha by (unfold PGSZ in *; lia). lia. }
      apply KL_dead with (pbrk := ps_brk s0). eapply KL_vm_eq; [exact HK| exact Hmi'| exact Hh'| | | | | | eapply vm_only_alloc_top; eassumption]; rewrite Emo', m_vmmaps_with_brk_next; assumption. }
  intros a. cbn beta. destruct a.
  - eapply mspec_bind; [apply mspec_upd|]. intros []. apply mspec_ret.
    intros s mo (s1 & -> & -> & HGs & [Hne Hpos] & Ecur & HK). unfold ev_step_post.
    cbn [ps_brk set_brk_ps ps_m ps_fa ps_so answer_ok event_post].
    replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Hph, Ereg, Z.eqb_refl.
    destruct HK as [HK HPG].
    splits; auto.
    + unfold brk_answer_ok. rewrite Z.eqb_refl, HPG. reflexivity.
    + eapply (HG s0); [reflexivity|reflexivity| apply vm_only_refl| exact HGs].
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
  region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 a) (Z_to_bv 64 n) = true ->
  minv mo' -> m_halted mo' = None ->
  m_vmmaps mo' = mkVmMapsFull (vm_reserved h) ((Z_to_bv 64 a, Z_to_bv 64 n) :: vm_maps h)
                 (if isnone then (Z_to_bv 64 a, Z_to_bv 64 n) :: vm_noaccess h else vm_noaccess h)
                 (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) ->
  KL (if isnone then set_metas ((a, len, 0) :: ld_metas L) L else set_groups ((a, len) :: ld_groups L) L) pbrk mo'
  /\ mmap_answer_ok (lranges L) len a = true /\ is_err a = false.
Proof.
  intros L pbrk mo mo' a len isnone HK Hq Hlen h n Hok Hrf Hmi' Hh' Evm. pose proof alloc_ceiling_lt as Hcl.
  apply mmap_addr_ok_true in Hok as [(A1 & A2 & A3) _]. rewrite page_size_eq in A1. fold n in A3.
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
      rewrite (proj2 (Z.ltb_lt 0 a)) by lia. unfold PGSZ at 1. rewrite A1, Z.eqb_refl.
      pose proof ceil_le_MCEIL as HleM. rewrite (proj2 (Z.leb_le (a + n) MCEIL)) by lia. cbn [andb].
      unfold ranges_free. apply forallb_forall. intros [lo m] Hin. cbn [fst snd]. unfold iv_disjoint.
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
                /\ ld_brkreg L' = None /\ cur + 2 * PGSZ <= alloc_ceiling
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
          | rewrite ?Evm; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk set_metas set_groups ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; auto ].
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
                            /\ mmap_answer_ok (lranges L) len a = true /\ is_err a = false
                end)).
    intros s mo (-> & HK & HGs).
    lazymatch goal with |- ?P /\ _ => assert (Hsafe : P); [| split; [exact Hsafe|]] end.
    { subst prot. destruct isnone; [apply nsafe_mmap_none| apply nsafe_mmap_rw]. }
    intros rsp mo' evs Hst.
    pose proof (minv_preserved _ _ _ _ _ (kl_minv _ _ _ HK) (kl_halt _ _ _ HK) Hsafe Hst) as [Hh' Hmi'].
    assert (Hcase : vm_only mo mo' /\ exists x, dec rsp = Some x /\
              match x with
              | MmErr e => e = ENOMEM /\ mo' = mo
              | MmOk a => mmap_addr_ok len [] a = true
                  /\ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (Z_to_bv 64 a) (Z_to_bv 64 (mmap_len len)) = true
                  /\ m_vmmaps mo' = mkVmMapsFull (vm_reserved (m_vmmaps mo)) ((Z_to_bv 64 a, Z_to_bv 64 (mmap_len len)) :: vm_maps (m_vmmaps mo))
                       (if isnone then (Z_to_bv 64 a, Z_to_bv 64 (mmap_len len)) :: vm_noaccess (m_vmmaps mo) else vm_noaccess (m_vmmaps mo))
                       (vm_start_brk (m_vmmaps mo)) (vm_brk (m_vmmaps mo)) (vm_limit (m_vmmaps mo)) (vm_mmap_base (m_vmmaps mo)) (vm_init_sp (m_vmmaps mo))
              end).
    { subst prot dec. destruct isnone.
      - pose proof (nstep_dec_mmap_none len [] mo rsp mo' evs ltac:(lia) ltac:(unfold LEN_MAX in *; lia) (kl_top _ _ _ HK) (Forall_nil _) Hst) as (_ & Hvo & x & Hd & Hx).
        split; [exact Hvo|]. exists x. split; [exact Hd|]. exact Hx.
      - pose proof (nstep_dec_mmap len [] mo rsp mo' evs ltac:(lia) ltac:(unfold LEN_MAX in *; lia) (kl_top _ _ _ HK) (Forall_nil _) Hst) as (_ & Hvo & x & Hd & Hx).
        split; [exact Hvo|]. exists x. split; [exact Hd|]. destruct x as [e|a']; [exact Hx|].
        destruct Hx as (Hx1 & Hx2 & _ & Hx4). split; [exact Hx1| split; [exact Hx2| exact Hx4]]. }
    destruct Hcase as (Hvo & x & Hd & Hx). exists x. split; [exact Hd|].
    split; [reflexivity|]. split; [eapply HG; [reflexivity|reflexivity| exact Hvo| exact HGs]|].
    destruct x as [e|a].
    - destruct Hx as [-> ->]. split; [reflexivity| exact HK].
    - destruct Hx as (Hok & Hrf & Evm). apply (KL_mmap_new L (ps_brk s0) mo mo' a len isnone HK Hq Hlen Hok Hrf Hmi' Hh' Evm). }
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
  intros L G s0 cur HG Hph a. pose proof alloc_ceiling_lt as Hcl. unfold ev_step.
  change (Z.land MAPFX MAP_FIXED_Z =? 0) with false. cbn [negb].
  set (L' := set_brkph BPLive (set_brkreg (Some (a, 2 * PGSZ)) L)).
  eapply mspec_bind.
  { apply (mspec_sys (NMmap a PGSZ PROT_NONE MAPFX) (dec_mmap_fixed a PGSZ) _
             (fun x s mo => s = s0 /\ G s mo /\ KL L' (ps_brk s0) mo /\ match x with FxKept e => e = ENOMEM | FxDone => True | FxLost e => e = ENOMEM end)).
    intros s mo (-> & HK & HGs).
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
    lazymatch goal with |- ?P /\ _ => assert (Hsafe : P); [| split; [exact Hsafe|]] end.
    { unfold nsafe, mmap_safe_b. fold aw nw.
      change (mmap_off_aligned_b (Z_to_bv 64 0)) with true.
      change (mmap_anon_b (Z_to_bv 64 MAPFX)) with true.
      change (mmap_modeled_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 MAPFX) (Z_to_bv 64 0)) with false.
      change (mmap_noaccess_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 MAPFX) (Z_to_bv 64 0)) with false.
      change (mmap_fixed_noaccess_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 MAPFX) (Z_to_bv 64 0)) with true.
      change (mmap_noreserve_b (Z_to_bv 64 MAPFX)) with false.
      change (w_is0 nw) with false. cbn [orb negb andb]. cbv iota. rewrite Un. change (page_round_up_Z PGSZ) with PGSZ. cbv zeta. rewrite Ua.
      replace (two_pow_64 <=? a + PGSZ) with false by (symmetry; apply Z.leb_gt; unfold two_pow_64, PGSZ in *; lia).
      fold h. rewrite (kl_top _ _ _ HK). replace (a + PGSZ <=? alloc_ceiling) with true by (symmetry; apply Z.leb_le; lia). cbn [negb].
      rewrite page_size_eq. replace (a mod 4096 =? 0) with true by (symmetry; apply Z.eqb_eq; rewrite Ha, Ecur; exact S2). cbn [negb].
      fold h. change (Z_to_bv 64 PGSZ) with nw. rewrite Hrf, Hmc.
      replace (0 <? a) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb andb orb]. reflexivity. }
    intros rsp mo' evs Hst.
    pose proof (minv_preserved _ _ _ _ _ (kl_minv _ _ _ HK) (kl_halt _ _ _ HK) Hsafe Hst) as [Hh' Hmi'].
    pose proof (nstep_mmap_fixed_inv a mo rsp mo' evs (kl_top _ _ _ HK) ltac:(lia) ltac:(lia) ltac:(rewrite Ha, Ecur; exact S2) Hrf Hmc Hst) as (_ & Hvo & x & Hd & Hx).
    fold h aw nw in Hx.
    exists x. split; [exact Hd|]. split; [reflexivity|]. split; [eapply HG; [reflexivity|reflexivity| exact Hvo| exact HGs]|].

    pose proof (fun b0 l0 H => went_In_bounds _ _ _ b0 l0 HK H) as WB.
    assert (Dgm : forall b0 l0, (In (b0, l0) (ld_groups L) \/ exists k, In (b0, l0, k) (ld_metas L)) ->
                   b0 + mmap_len l0 <= a \/ a + 2 * PGSZ <= b0).
    { intros b0 l0 [H|[k H]]; rewrite Ha; [apply (Dg _ _ H)| apply (Dm _ _ _ H)]. }
    assert (KLnew : forall maps' noacc',
              vmwf maps' ->
              (forall e, In e (vm_maps h) -> (ehi e <= a \/ a + PGSZ <= elo e) -> In e maps') ->
              (forall e, In e maps' -> In e (vm_maps h) \/ In e (maps_subtract (vm_maps h) a (a + PGSZ))) ->
              (forall e x y, In e (vm_noaccess h) -> elo e <= x -> x < y -> y <= ehi e -> (y <= a \/ a + PGSZ <= x) ->
                  exists e', In e' noacc' /\ elo e' <= x /\ y <= ehi e') ->
              (exists e', In e' maps' /\ elo e' <= a + PGSZ /\ a + 2 * PGSZ <= ehi e') ->
              m_vmmaps mo' = mkVmMapsFull (vm_reserved h) maps' noacc' (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) ->
              KL L' (ps_brk s0) mo').
    { intros maps' noacc' Hwf' Hkeep Hback Hna Hcov' Evm. subst L'.
      kl_open HK. constructor; try exact Hmi'; try exact Hh'; rewrite ?Evm; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk set_brkph set_brkreg ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; auto.
      - intros b0 l0 Hin. pose proof (WB b0 l0 (or_introl Hin)) as (B1 & B2 & B3 & B4 & B5 & B6). pose proof (Dgm b0 l0 (or_introl Hin)) as D.
        specialize (Kgr b0 l0 Hin). destruct Kgr as ([G0 G1] & G2 & G3 & G4 & G5 & G6). splits; try assumption.
        + apply Hkeep; [exact B4|]. rewrite B5, B6. clear -D. unfold PGSZ in *. lia.
        + unfold brk_disj; cbn. intros b1 l1 E. injection E as <- <-. clear -D. unfold PGSZ in *. lia.
      - intros b0 l0 k Hin. pose proof (WB b0 l0 (or_intror (ex_intro _ k Hin))) as (B1 & B2 & B3 & B4 & B5 & B6). pose proof (Dgm b0 l0 (or_intror (ex_intro _ k Hin))) as D.
        specialize (Kme b0 l0 k Hin). destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). splits; try assumption.
        + apply Hkeep; [exact B4|]. rewrite B5, B6. clear -D. unfold PGSZ in *. lia.
        + unfold brk_disj; cbn. intros b1 l1 E. injection E as <- <-. clear -D. unfold PGSZ in *. lia.
        + intros q Hq1 Hq2. destruct (G9 q Hq1 Hq2) as (e & He & Hel & Heh).
          apply (Hna e (b0 + q * PGSZ) (b0 + q * PGSZ + PGSZ) He Hel ltac:(unfold PGSZ; lia) Heh). clear -D Hq1 Hq2 G5. unfold PGSZ in *. nia.
      - intros b1 l1 E. injection E as <- <-. splits.
        + lia.
        + rewrite Ha, Ecur. exact S2.
        + lia.
        + reflexivity.
        + lia.
        + intros z Hz. destruct Hcov' as (e' & He' & H1 & H2). exists e'. split; [exact He'|]. lia.
      - exists a, (2 * PGSZ). splits; [reflexivity| lia| lia]. }
    assert (Hlo0 : 0 <= a) by lia.
    assert (Hlohi : a < a + PGSZ < 2^64) by (unfold PGSZ in *; lia).
    assert (Hlohi' : a < a + PGSZ <= 2^64) by lia.
    destruct x as [e| |e].
    - destruct Hx.
    - split; [|exact I].
      apply (KLnew (vm_maps h) ((aw, nw) :: maps_subtract (vm_noaccess h) a (a + PGSZ))); auto.
      + exact (kl_wf _ _ _ HK).
      + intros e x y He H1 H2 H3 H4. destruct (iv_subtract_contains (fst e) (snd e) a (a + PGSZ) x y Hlo0 Hlohi H1 H2 H3 H4) as (e' & He' & Hr).
        exists e'. split; [right; eapply maps_subtract_In_intro; eauto| exact Hr].
      + exists e0. split; [exact He0|]. unfold PGSZ in *; lia.
    - destruct Hx. }
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
  intros L G s0 a l0 len HG Hq Hin Hlen. pose proof alloc_ceiling_lt as Hcl. unfold ev_step.
  rewrite round_up_pg_eq in Hlen. fold (mmap_len l0) in Hlen.
  set (L' := set_groups (g_remove a (ld_groups L)) L).
  eapply mspec_bind.
  { apply (mspec_sys (NMunmap a len) (dec_munmap a len) _
             (fun x s mo => s = s0 /\ G s mo /\ KL L' (ps_brk s0) mo /\ match x with RgErr e => e = EINVAL | RgDone _ => True end)).
    intros s mo (-> & HK & HGs).
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
    lazymatch goal with |- ?P /\ _ => assert (Hsafe : P); [| split; [exact Hsafe|]] end.
    { unfold nsafe, munmap_safe_b. fold h aw. rewrite Ua, page_size_eq. unfold PGSZ in A3. rewrite A3. rewrite w_is0_lit by lia.
      replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb orb Z.eqb]. cbv zeta.
      rewrite (unsigned_lit len) by lia. fold (mmap_len len). rewrite Hlen2. change (Z_to_bv 64 n) with nw.
      rewrite Hhas. destruct (TASK_SIZE <? a + n); reflexivity. }
    intros rsp mo' evs Hst.
    pose proof (minv_preserved _ _ _ _ _ (kl_minv _ _ _ HK) (kl_halt _ _ _ HK) Hsafe Hst) as [Hh' Hmi'].
    pose proof (nstep_dec_munmap a len mo rsp mo' evs ltac:(lia) ltac:(lia) ltac:(rewrite Hlen2; lia) Hst) as (_ & Hvo & x & Hd & Hx).
    rewrite Hlen2 in Hx. fold h aw nw in Hx.
    exists x. split; [exact Hd|]. split; [reflexivity|]. split; [eapply HG; [reflexivity|reflexivity| exact Hvo| exact HGs]|].

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
              (forall e x y, In e (vm_noaccess h) -> elo e <= x -> x < y -> y <= ehi e -> (y <= a \/ a + n <= x) ->
                  exists e', In e' noacc' /\ elo e' <= x /\ y <= ehi e') ->
              m_vmmaps mo' = mkVmMapsFull (vm_reserved h) maps' noacc' (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) ->
              KL L' (ps_brk s0) mo').
    { intros maps' noacc' Hwf' Hkeep Hna Evm.
      assert (Hph' : phase_inv (ld_brk L') L' (ps_brk s0) mo') by (eapply phase_quiet; [exact HK| exact Hq| reflexivity| reflexivity| rewrite Evm; reflexivity| rewrite Evm; reflexivity]).
      assert (Kfst : forall b l, b <> a -> 0 < b < 2^64 -> fst (went b (mmap_len l)) <> aw).
      { intros b l Hne Hb E. apply Hne. apply (f_equal bv_unsigned) in E. cbn [fst went] in E. rewrite unsigned_wz, Ua in E by lia. exact E. }
      subst L'. kl_open HK. constructor; try exact Hph'; try exact Hmi'; try exact Hh'; rewrite ?Evm; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk set_groups ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; auto.
      - intros b0 l1 Hin0. destruct (Hg' b0 l1 Hin0) as [Hin1 Hne]. specialize (Kgr b0 l1 Hin1). destruct Kgr as ([G0 G1] & G2 & G3 & G4 & G5 & G6). splits; try assumption.
        apply Hkeep; [exact G5|]. apply Kfst; auto. pose proof (mmap_len_ge l1 G0). lia.
      - intros b0 l1 k Hin0. pose proof (Hm' b0 l1 k Hin0) as Hne. specialize (Kme b0 l1 k Hin0). destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). splits; try assumption.
        + apply Hkeep; [exact G7|]. apply Kfst; auto. pose proof (mmap_len_ge l1 G0). lia.
        + intros q Hq1 Hq2. destruct (G9 q Hq1 Hq2) as (e & He & Hel & Heh).
          pose proof (Dother b0 l1 (or_intror (ex_intro _ k Hin0)) Hne) as D.
          apply (Hna e (b0 + q * PGSZ) (b0 + q * PGSZ + PGSZ) He Hel ltac:(unfold PGSZ; lia) Heh). clear -D Hq1 Hq2 G5. unfold PGSZ in *. nia.
      - rewrite Ezz, map_app, <- app_assoc. exact Kd1.
      - intros b0 l1 E. specialize (Kreg b0 l1 E). destruct Kreg as (R1 & R2 & R3 & R4 & R5 & Rcov). splits; auto.
        intros z Hz. destruct (Rcov z Hz) as (e & He & Hr). exists e. split; [|exact Hr]. apply Hkeep; [exact He|].
        intros Efst. unfold brk_disj in A6. specialize (A6 b0 l1 E).
        destruct (pwdisj_In _ _ _ (proj2 Kwf) He A5) as [->|D].
        + rewrite B5, B6 in Hr. clear -Hr A6 Hz R3. unfold PGSZ in *. lia.
        + pose proof (proj1 Kwf e He) as W. unfold edisj, elo, ehi in D, W. rewrite Efst in D, W. cbn [fst snd went] in D. unfold wz in D. fold aw nw in D. rewrite Un in D. lia. }
    assert (Hlo0 : 0 <= a) by lia.
    assert (Hlohi : a < a + n < 2^64) by lia.
    destruct x as [e|[|]].
    - destruct Hx as [-> ->]. split; [|reflexivity]. apply (KLnew (vm_maps h) (vm_noaccess h)).
      + exact (kl_wf _ _ _ HK).
      + auto.
      + intros e x y He H1 H2 H3 H4. exists e. auto.
      + subst h. destruct (m_vmmaps mo); reflexivity.
    - destruct Hx as [_ Evm]. rewrite Ua, Un in Evm. split; [|exact I]. apply (KLnew (map_remove (vm_maps h) aw) (maps_subtract (vm_noaccess h) a (a + n))).
      + apply vmwf_remove. exact (kl_wf _ _ _ HK).
      + intros e He Hne. unfold map_remove. apply filter_In. split; [exact He|]. destruct (bv_eqb (fst e) aw) eqn:E; [|reflexivity]. apply bv_eqb_eq in E. contradiction.
      + intros e x y He H1 H2 H3 H4. destruct (iv_subtract_contains (fst e) (snd e) a (a + n) x y Hlo0 Hlohi H1 H2 H3 H4) as (e' & He' & Hr).
        exists e'. split; [eapply maps_subtract_In_intro; eauto| exact Hr].
      + exact Evm.
    - destruct Hx as [-> _]. split; [|exact I]. apply (KLnew (vm_maps h) (vm_noaccess h)).
      + exact (kl_wf _ _ _ HK).
      + auto.
      + intros e x y He H1 H2 H3 H4. exists e. auto.
      + subst h. destruct (m_vmmaps mo); reflexivity. }
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
  intros addr len mo rsp mo' evs h a n AddrRange LenPos LenFits NoAccessHas Step Decoded.
  pose proof (mmap_len_ge len LenPos) as LenBelow.
  destruct (proj1 (nstep_mprotect_iff _ _ _ _ _ _ _) Step) as [Checked NotRefused].
  assert (LenVal : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
  assert (NoConflict : mprotect_grows_conflict_b (Z_to_bv 64 (PROT_READ + PROT_WRITE)) = false) by reflexivity.
  assert (RwModeled : mprotect_modeled_b (Z_to_bv 64 (PROT_READ + PROT_WRITE)) = true) by reflexivity.
  assert (LenNonzero : w_is0 (Z_to_bv 64 len) = false) by (apply w_is0_pos; lia).
  unfold check_mprotect in Checked.
  rewrite NoConflict, RwModeled, LenNonzero, LenVal in Checked. cbv zeta in Checked.
  fold (mmap_len len) in Checked. fold h a n in Checked.
  destruct (bv_unsigned a mod page_size =? 0) eqn:Aligned; cbn [negb] in Checked.
  2: { apply check_ret_only_ok_iff in Checked as (RspIs & _ & _). rewrite RspIs in Decoded.
       unfold dec_mprotect in Decoded. cbv beta iota zeta in Decoded.
       change (errno_of (errno_ret EINVAL)) with (Some EINVAL) in Decoded. discriminate Decoded. }
  destruct (two_pow_64 <=? bv_unsigned a + mmap_len len) eqn:Overflow.
  { apply check_ret_only_ok_iff in Checked as (RspIs & _ & _). rewrite RspIs in NotRefused.
    cbn [eff_ret] in NotRefused. rewrite ret_in_errnos_errno in NotRefused; [discriminate NotRefused| apply in_eq]. }
  rewrite NoAccessHas in Checked.
  destruct (map_contains (vm_maps h) a n) eqn:MapsHas; cbn [andb] in Checked; [|discriminate Checked].
  destruct rsp as [ret writes zeros unmaps copies copyins]. cbn [eff_ret] in NotRefused.
  destruct writes; [|discriminate Checked]. destruct unmaps; [|discriminate Checked].
  destruct copies; [|discriminate Checked]. destruct copyins; [|discriminate Checked].
  change (errno_ret_in mprotect_errnos ret) with (ret_in_errnos mprotect_errnos ret) in Checked.
  rewrite NotRefused in Checked.
  destruct (mprotect_budget_ok mo a n && w_is0 ret && listNN_eqb zeros [(a, n)]) eqn:Granted; [|discriminate Checked].
  apply andb_prop in Granted as [Granted ZerosHit]. apply andb_prop in Granted as [_ RetZero].
  apply bv_eqb_eq in RetZero. apply listNN_eqb_eq in ZerosHit. subst ret zeros.
  unfold dec_mprotect in Decoded. cbv beta iota zeta in Decoded.
  change (errno_of (Z_to_bv 64 0)) with (@None Z) in Decoded.
  change (Z_to_bv 64 addr) with a in Decoded. change (Z_to_bv 64 (mmap_len len)) with n in Decoded.
  rewrite !bv_eqb_refl in Decoded. discriminate Decoded.
Qed.

Lemma ev_mprotect_ok : forall L G s0 b l k, frame_ok G -> brk_quiet L -> In (b, l, k) (ld_metas L) ->
  (2 + k) * PGSZ <= round_up_pg l ->
  let a := b + (1 + k) * PGSZ in
  mspec (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ G s mo)
        (ev_step (EMprotect a PGSZ PROT_RW))
        (ev_step_post L (EMprotect a PGSZ PROT_RW) G s0).
Proof.
  intros L G s0 b l k HG Hq Hin Hk2 a. pose proof alloc_ceiling_lt as Hcl. unfold ev_step.
  rewrite round_up_pg_eq in Hk2. fold (mmap_len l) in Hk2.
  set (L' := set_metas (map (bump_meta a) (ld_metas L)) L).
  eapply mspec_bind.
  { apply (mspec_sys (NMprotect a PGSZ PROT_RW) (dec_mprotect_rw a PGSZ) _
             (fun x s mo => s = s0 /\ G s mo /\ match x with RgErr e => (e = EINVAL \/ e = ENOMEM) /\ KL L (ps_brk s0) mo | RgDone _ => KL L' (ps_brk s0) mo end)).
    intros s mo (-> & HK & HGs).
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
    lazymatch goal with |- ?P /\ _ => assert (Hsafe : P); [| split; [exact Hsafe|]] end.
    { unfold nsafe, mprotect_safe_b. fold h aw nw.
      change (mprotect_grows_conflict_b (Z_to_bv 64 PROT_RW)) with false. change (mprotect_modeled_b (Z_to_bv 64 PROT_RW)) with true.
      rewrite Ua, page_size_eq, Hamod. change (w_is0 nw) with false. cbv iota. cbn [Z.eqb negb]. rewrite Un. change (page_round_up_Z PGSZ) with PGSZ.
      replace (two_pow_64 <=? a + PGSZ) with false by (symmetry; apply Z.leb_gt; unfold two_pow_64, PGSZ in *; lia). cbv zeta. fold nw. rewrite Hcn, Hcm. reflexivity. }
    intros rsp mo' evs Hst.
    pose proof (minv_preserved _ _ _ _ _ (kl_minv _ _ _ HK) (kl_halt _ _ _ HK) Hsafe Hst) as [Hh' Hmi'].
    pose proof (nstep_dec_mprotect a PGSZ mo rsp mo' evs ltac:(unfold PGSZ in *; lia) ltac:(unfold PGSZ; lia) ltac:(change (mmap_len PGSZ) with PGSZ; unfold PGSZ; lia) Hst) as (_ & Hvo & x & Hd & Hx).
    change (mmap_len PGSZ) with PGSZ in Hx. fold h aw nw in Hx.
    assert (HdRW : dec_mprotect_rw a PGSZ rsp = Some x).
    { destruct x as [e|[|]].
      - destruct Hx as [He _]. unfold dec_mprotect_rw. rewrite Hd.
        replace (e =? ENOSYS) with false by (symmetry; apply Z.eqb_neq; destruct He as [-> | ->]; unfold EINVAL, ENOMEM, ENOSYS; lia). reflexivity.
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
              (forall e x y, In e (vm_noaccess h) -> elo e <= x -> x < y -> y <= ehi e -> (y <= a \/ a + PGSZ <= x) ->
                  exists e', In e' noacc' /\ elo e' <= x /\ y <= ehi e') ->
              m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (vm_maps h) noacc' (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) ->
              KL L' (ps_brk s0) mo').
    { intros noacc' Hna Evm.
      assert (Hph' : phase_inv (ld_brk L') L' (ps_brk s0) mo') by (eapply phase_quiet; [exact HK| exact Hq| reflexivity| reflexivity| rewrite Evm; reflexivity| rewrite Evm; reflexivity]).
      subst L'. kl_open HK. constructor; try exact Hph'; try exact Hmi'; try exact Hh'; rewrite ?Evm; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk set_metas ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; auto.
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
          apply (Hna e (b + q * PGSZ) (b + q * PGSZ + PGSZ) He Hel ltac:(unfold PGSZ; lia) Heh). right. subst a. clear -Hq1. unfold PGSZ in *. nia.
        + splits; try assumption.
          intros q Hq1 Hq2. destruct (G9 q Hq1 Hq2) as (e & He & Hel & Heh).
          apply (Hna e (b0 + q * PGSZ) (b0 + q * PGSZ + PGSZ) He Hel ltac:(unfold PGSZ; lia) Heh).
          destruct (Z.eq_dec b0 b) as [->|Hne].
          { pose proof (nodup_map_inj _ _ _ _ Kdm Hin1 Hin (eq_refl b)) as E. injection E as -> ->. exfalso. apply Na. reflexivity. }
          pose proof (Dother b0 l0 (or_intror (ex_intro _ k0 Hin1)) Hne) as D. clear -D Hab Hq1 Hq2 G5. unfold PGSZ in *. nia.
      - rewrite map_base_bump. exact Kd. }
    destruct x as [e|[|]].
    - destruct Hx as [He ->]. split; [exact He| exact HK].
    - destruct Hx as (_ & _ & _ & Evm). rewrite Ua, Un in Evm. apply (KLnew (maps_subtract (vm_noaccess h) a (a + PGSZ))); [|exact Evm].
      assert (Hlohi : a < a + PGSZ < 2^64) by (unfold PGSZ in *; lia).
      intros e x y He H1 H2 H3 H4. destruct (iv_subtract_contains (fst e) (snd e) a (a + PGSZ) x y ltac:(lia) Hlohi H1 H2 H3 H4) as (e' & He' & Hr).
      exists e'. split; [eapply maps_subtract_In_intro; eauto| exact Hr].
    - subst mo'. apply (KLnew (vm_noaccess h)).
      + intros e x y He H1 H2 H3 H4. exists e. auto.
      + subst h. destruct (m_vmmaps mo); reflexivity. }
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
  - cbn [membed]. apply mspec_ret. intros s mo (-> & HK & HGs). exists L.
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
  (exists L, creach (ps_m s) L /\ KL L (ps_brk s) mo /\ incl (map fst X) (ld_live L))
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

End WithCeiling.
