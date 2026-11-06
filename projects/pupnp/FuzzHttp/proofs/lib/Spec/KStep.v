(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim Monad MSafe STree Malloc Prog KInv.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

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

Lemma alloc_top_facts : forall mo, minv mo ->
  0x7FFF7F800000 <= alloc_top (m_vmmaps mo) <= 0x7FFFFF800000 /\ alloc_top (m_vmmaps mo) < 2^63.
Proof. intros mo H. pose proof (minv_alloc_top mo H) as B. unfold alloc_floor, alloc_ceiling_max in B. lia. Qed.
Lemma KL_top_lt63 : forall L pbrk mo, KL L pbrk mo -> alloc_top (m_vmmaps mo) < 2^63.
Proof. intros L pbrk mo K. exact (proj2 (alloc_top_facts mo (kl_minv _ _ _ K))). Qed.
Lemma KL_top_bracket : forall L pbrk mo, KL L pbrk mo -> 0x7FFF7F800000 <= alloc_top (m_vmmaps mo) <= 0x7FFFFF800000.
Proof. intros L pbrk mo K. exact (proj1 (alloc_top_facts mo (kl_minv _ _ _ K))). Qed.
Lemma KL_ld_ceil : forall L pbrk mo, KL L pbrk mo -> ld_ceil L = alloc_top (m_vmmaps mo).
Proof. intros L pbrk mo K. exact (kl_ceil _ _ _ K). Qed.
Lemma alloc_top_lt64 : forall h, alloc_top h < 2^64.
Proof. intros h. unfold alloc_top. pose proof (bv_unsigned_in_range 64 (vm_init_sp h)) as R. unfold bv_modulus, stack_max_size in *. lia. Qed.
Lemma KL_ceil_lt63 : forall L pbrk mo, KL L pbrk mo -> ld_ceil L < 2^63.
Proof. intros L pbrk mo K. rewrite (kl_ceil _ _ _ K). exact (KL_top_lt63 _ _ _ K). Qed.
Lemma KL_ceil_bracket : forall L pbrk mo, KL L pbrk mo -> 0x7FFF7F800000 <= ld_ceil L <= 0x7FFFFF800000.
Proof. intros L pbrk mo K. rewrite (kl_ceil _ _ _ K). exact (KL_top_bracket _ _ _ K). Qed.

Lemma alloc_top_mk : forall r m na sb b lim mb h,
  alloc_top (mkVmMapsFull r m na sb b lim mb (vm_init_sp h)) = alloc_top h.
Proof. reflexivity. Qed.

Lemma nstep_mmap0_top : forall len prot mo rsp mo' evs,
  0 < len -> mmap_len len < 2^64 -> (prot = PROT_NONE \/ prot = PROT_RW) ->
  nstep (NMmap 0 len prot MAPF) mo rsp mo' evs ->
  errno_of (eff_ret rsp) = None ->
  bv_unsigned (eff_ret rsp) + mmap_len len <= alloc_top (m_vmmaps mo).
Proof.
  intros len prot mo rsp mo' evs Hlen Hlen2 Hprot H Hne.
  pose proof (mmap_len_bound len Hlen) as Hb.
  destruct H as [_ H]. cbv zeta in H. rewrite (unsigned_lit len) in H by lia. fold (mmap_len len) in H.
  assert (SR : forall r ws zs us cs, Nodes.strip rsp = mkEffectU r ws zs us cs [] -> eff_ret rsp = r).
  { intros r ws zs us cs E. destruct rsp as [r0 ws0 zs0 us0 cs0 ci0]. rewrite strip_mk in E. injection E. auto. }
  destruct H as [(e & He & Hs & _)|[(_ & a & (Q1 & Q2 & Q3 & Q4 & Q5) & _ & Hs & _)|[(_ & _ & a & (Q1 & Q2 & Q3 & Q4 & Q5) & Hs & _)|(_ & _ & Hm & _)]]].
  - exfalso. unfold efferr, eff0 in Hs. rewrite (SR _ _ _ _ _ Hs) in Hne.
    apply mmap_errnos_ENOMEM in He. subst e. rewrite errno_of_errno_ret in Hne by (unfold ENOMEM; lia). discriminate.
  - rewrite (SR _ _ _ _ _ Hs). rewrite (unsigned_lit len) in Q5 by lia. exact Q5.
  - rewrite (SR _ _ _ _ _ Hs). rewrite (unsigned_lit len) in Q5 by lia. exact Q5.
  - exfalso. revert Hm. destruct Hprot as [-> | ->]; vm_compute; discriminate.
Qed.

Lemma alloc_top_brk_model_next : forall h req r, alloc_top (Mmap.brk_model_next h req r) = alloc_top h.
Proof. reflexivity. Qed.

Ltac kl_ceil_close Kceil :=
  cbn [ld_ceil set_brkph set_brkreg set_groups set_metas set_live event_post];
  rewrite ?alloc_top_brk_model_next, ?alloc_top_mk;
  first [ exact Kceil | (etransitivity; [exact Kceil| reflexivity]) | (rewrite Kceil; reflexivity) ].

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

Lemma region_free_disj : forall maps a n e, region_free maps a n = true -> In e maps ->
  bv_unsigned a + bv_unsigned n <= elo e \/ ehi e <= bv_unsigned a.
Proof. intros maps a n [e sz] H Hin. unfold elo, ehi. cbn. eapply region_free_In; eauto. Qed.

Lemma region_free_shrink : forall maps a n n', bv_unsigned n' <= bv_unsigned n ->
  region_free maps a n = true -> region_free maps a n' = true.
Proof.
  intros maps a n n' Hle H. apply region_free_forall. intros e He.
  pose proof (proj1 (region_free_forall maps a n) H e He) as O. unfold iv_overlap in *.
  destruct (Z.ltb_spec0 (bv_unsigned a) (bv_unsigned (fst e) + bv_unsigned (snd e)));
  destruct (Z.ltb_spec0 (bv_unsigned (fst e)) (bv_unsigned a + bv_unsigned n));
  destruct (Z.ltb_spec0 (bv_unsigned (fst e)) (bv_unsigned a + bv_unsigned n')); cbn in *; try reflexivity; try discriminate; lia.
Qed.

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

Lemma iv_subtract_sub : forall a sz lo hi e, 0 < bv_unsigned sz -> bv_unsigned a + bv_unsigned sz <= 2^64 ->
  In e (iv_subtract a sz lo hi) -> bv_unsigned a <= elo e /\ ehi e <= bv_unsigned a + bv_unsigned sz /\ elo e < ehi e.
Proof.
  intros a sz lo hi e Hsz Hwf Hin. unfold iv_subtract in Hin.
  pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 sz).
  unfold bv_modulus in *.
  apply in_app_or in Hin as [Hin|Hin].
  - destruct (Z.ltb_spec (bv_unsigned a) (lo)); [|destruct Hin].
    destruct Hin as [<-|[]]. unfold elo, ehi. cbn. rewrite unsigned_lit by lia. lia.
  - destruct (Z.ltb_spec (hi) (bv_unsigned a + bv_unsigned sz)); [|destruct Hin].
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

Lemma maps_subtract_keep : forall maps lo hi e, vmwf maps -> 0 <= lo < hi ->
  In e maps -> (ehi e <= lo \/ hi <= elo e) -> In e (maps_subtract maps lo hi).
Proof.
  induction maps as [|[a sz] maps IH]; intros lo hi e Hwf Hlh Hin Hd; [destruct Hin|].
  destruct Hwf as [Hb Hp]. cbn. apply in_or_app. destruct Hin as [<-|Hin].
  - left. rewrite iv_subtract_disjoint; [left; reflexivity| | lia|].
    + specialize (Hb (a, sz) (or_introl eq_refl)). unfold elo, ehi in Hb. cbn in Hb. lia.
    + unfold elo, ehi in Hd. cbn in Hd. lia.
  - right. apply IH; auto. split; [intros e' H'; apply Hb; right; exact H'| inversion Hp; assumption].
Qed.

Lemma iv_subtract_contains : forall a sz lo hi x y,
  lo < hi -> y <= 2^64 ->
  bv_unsigned a <= x -> x < y -> y <= bv_unsigned a + bv_unsigned sz ->
  (y <= lo \/ hi <= x) ->
  exists e, In e (iv_subtract a sz lo hi) /\ elo e <= x /\ y <= ehi e.
Proof.
  intros a sz lo hi x y Hlh Hhi Hax Hxy Hy Hd. unfold iv_subtract.
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

Lemma iv_subtract_pwdisj : forall a sz lo hi, 0 <= lo < hi -> bv_unsigned a + bv_unsigned sz <= 2^64 -> pwdisj (iv_subtract a sz lo hi).
Proof.
  intros a sz lo hi Hlh Hasz. unfold iv_subtract.
  pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 sz). unfold bv_modulus in *.
  destruct (Z.ltb_spec (bv_unsigned a) (lo)); destruct (Z.ltb_spec (hi) (bv_unsigned a + bv_unsigned sz)); cbn [app].
  - constructor; [|constructor; [intros e' []| constructor]]. intros e' [<-|[]].
    unfold edisj, elo, ehi; cbn. rewrite !unsigned_lit by lia. left. lia.
  - constructor; [intros e' []| constructor].
  - constructor; [intros e' []| constructor].
  - constructor.
Qed.

Lemma vmwf_subtract : forall maps lo hi, 0 <= lo < hi -> vmwf maps -> vmwf (maps_subtract maps lo hi).
Proof.
  induction maps as [|[a sz] maps IH]; intros lo hi Hlh [Hb Hp]; [split; [intros e []| constructor]|].
  inversion Hp; subst. assert (Hwf' : vmwf maps) by (split; [intros e He; apply Hb; right; exact He| assumption]).
  specialize (IH lo hi Hlh Hwf'). destruct IH as [IHb IHp].
  assert (Ha : elo (a, sz) < ehi (a, sz) <= 2^64) by (apply Hb; left; reflexivity). unfold elo, ehi in Ha; cbn in Ha.
  cbn. split.
  - intros e Hin. apply in_app_or in Hin as [Hin|Hin]; [|apply IHb; exact Hin].
    pose proof (iv_subtract_sub a sz lo hi e ltac:(lia) ltac:(lia) Hin). lia.
  - apply pwdisj_app; [apply iv_subtract_pwdisj; [exact Hlh| lia]| exact IHp|].
    intros e e' He He'. pose proof (iv_subtract_sub a sz lo hi e ltac:(lia) ltac:(lia) He) as S1.
    destruct (maps_subtract_In _ _ _ _ He') as (e0 & H0 & H0').
    assert (W0 : elo e0 < ehi e0 <= 2^64) by (apply Hb; right; exact H0). destruct e0 as [a0 s0]. unfold elo, ehi in W0; cbn in W0.
    pose proof (iv_subtract_sub a0 s0 lo hi e' ltac:(lia) ltac:(lia) H0') as S2.
    pose proof (H1 _ H0) as D. unfold edisj, elo, ehi in *. cbn in *. lia.
Qed.

Lemma wcov_mono : forall maps maps' lo hi, (forall e, In e maps -> In e maps') -> wcov maps lo hi -> wcov maps' lo hi.
Proof. intros maps maps' lo hi Hs Hc x Hx. destruct (Hc x Hx) as (e & He & Hr). exists e. auto. Qed.

