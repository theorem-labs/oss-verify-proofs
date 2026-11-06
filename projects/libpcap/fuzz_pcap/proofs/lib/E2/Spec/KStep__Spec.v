(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap Mprotect Mremap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require PropExec MState ITree Nodes RelSpec RelSpecMm Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad MSafe STree Malloc.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Quant.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Logic.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module KStep.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect Mremap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState ITree Nodes RelSpec RelSpecMm Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad MSafe STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MSafe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KLink.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Export OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KArith.
(* [comment removed for export] *) Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.zify_cheap_cleanup ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.zify_split_ranges; OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.zify_spec_trivial.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CE : CEIL}.
#[using="Type"] Lemma unsigned_wz : forall z, 0 <= z < 2^64 -> bv_unsigned (wz z) = z.
Proof. intros. unfold wz. apply unsigned_lit. assumption. Qed.

#[using="Type"] Lemma elo_went : forall b n, 0 <= b < 2^64 -> elo (went b n) = b.
Proof. intros. unfold elo, went. cbn [fst]. apply unsigned_wz. assumption. Qed.
#[using="Type"] Lemma ehi_went : forall b n, 0 <= b < 2^64 -> 0 <= n < 2^64 -> ehi (went b n) = b + n.
Proof. intros. unfold ehi, went. cbn [fst snd]. rewrite !unsigned_wz by assumption. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma pwdisj_In : forall l e1 e2, pwdisj l -> In e1 l -> In e2 l -> e1 = e2 \/ edisj e1 e2.
Proof.
  induction l as [|e l IH]; intros e1 e2 Hp H1 H2; [destruct H1|].
  inversion Hp; subst. destruct H1 as [<-|H1], H2 as [<-|H2].
  - left; reflexivity.
  - right. apply H3. exact H2.
  - right. pose proof (H3 _ H1) as D. unfold edisj in *. lia.
  - apply IH; assumption.
Qed.

#[using="Type"] Lemma region_free_app_r : forall l1 l2 a n, region_free (l1 ++ l2) a n = true -> region_free l2 a n = true.
Proof. induction l1 as [|[e sz] l1 IH]; intros l2 a n H; [exact H|]. cbn in H. apply andb_prop in H as [_ H]. apply IH. exact H. Qed.

#[using="Type"] Lemma region_free_disj : forall maps a n e, region_free maps a n = true -> In e maps ->
  bv_unsigned a + bv_unsigned n <= elo e \/ ehi e <= bv_unsigned a.
Proof. intros maps a n [e sz] H Hin. unfold elo, ehi. cbn. eapply region_free_In; eauto. Qed.

#[using="Type"] Lemma vmwf_cons : forall maps a n, vmwf maps ->
  bv_unsigned a < bv_unsigned a + bv_unsigned n <= 2^64 ->
  region_free maps a n = true ->
  vmwf ((a, n) :: maps).
Proof.
  intros maps a n [Hb Hp] Hn Hrf. split.
  - intros e [<-|Hin]; [unfold elo, ehi; cbn; lia| apply Hb; exact Hin].
  - constructor; [|exact Hp]. intros e' Hin. pose proof (region_free_disj _ _ _ _ Hrf Hin). unfold edisj, elo, ehi in *. cbn. lia.
Qed.

#[using="Type"] Lemma pwdisj_filter : forall (f : word * word -> bool) l, pwdisj l -> pwdisj (List.filter f l).
Proof.
  induction l as [|e l IH]; intros Hp; [constructor|]. inversion Hp; subst. cbn. destruct (f e).
  - constructor; [|apply IH; assumption]. intros e' Hin. apply List.filter_In in Hin as [Hin _]. auto.
  - apply IH; assumption.
Qed.

#[using="Type"] Lemma vmwf_remove : forall maps a, vmwf maps -> vmwf (map_remove maps a).
Proof.
  intros maps a [Hb Hp]. unfold map_remove. split.
  - intros e Hin. apply List.filter_In in Hin as [Hin _]. auto.
  - apply pwdisj_filter. exact Hp.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma iv_subtract_sub : forall a sz lo hi e, 0 < bv_unsigned sz -> bv_unsigned a + bv_unsigned sz <= 2^64 -> 0 <= lo ->
  In e (iv_subtract a sz lo hi) -> bv_unsigned a <= elo e /\ ehi e <= bv_unsigned a + bv_unsigned sz /\ elo e < ehi e.
Proof.
  intros a sz lo hi e Hsz Hwf Hlo Hin. unfold iv_subtract in Hin.
  pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 sz). unfold bv_modulus in *.
  apply in_app_or in Hin as [Hin|Hin].
  - destruct (Z.ltb_spec (bv_unsigned a) lo); [|destruct Hin].
    destruct Hin as [<-|[]]. unfold elo, ehi. cbn. rewrite unsigned_lit by lia. lia.
  - destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); [|destruct Hin].
    destruct Hin as [<-|[]]. unfold elo, ehi. cbn. rewrite !unsigned_lit by lia. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma iv_subtract_sub' : forall a sz lo hi e, bv_unsigned a + bv_unsigned sz <= 2^64 -> 0 <= hi ->
  In e (iv_subtract a sz lo hi) -> bv_unsigned a <= elo e /\ ehi e <= bv_unsigned a + bv_unsigned sz.
Proof.
  intros a sz lo hi e Hwf Hhi Hin. unfold iv_subtract in Hin.
  pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 sz). unfold bv_modulus in *.
  apply in_app_or in Hin as [Hin|Hin].
  - destruct (Z.ltb_spec (bv_unsigned a) lo); [|destruct Hin].
    destruct Hin as [<-|[]]. unfold elo, ehi. cbn. rewrite unsigned_lit by lia. lia.
  - destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); [|destruct Hin].
    destruct Hin as [<-|[]]. unfold elo, ehi. cbn. rewrite !unsigned_lit by lia. lia.
Qed.

#[using="Type"] Lemma maps_subtract_In : forall maps lo hi e, In e (maps_subtract maps lo hi) ->
  exists e0, In e0 maps /\ In e (iv_subtract (fst e0) (snd e0) lo hi).
Proof.
  induction maps as [|[a sz] maps IH]; intros lo hi e Hin; [destruct Hin|].
  cbn in Hin. apply in_app_or in Hin as [Hin|Hin].
  - exists (a, sz). split; [left; reflexivity| exact Hin].
  - destruct (IH _ _ _ Hin) as (e0 & H0 & H1). exists e0. split; [right; exact H0| exact H1].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma iv_subtract_disjoint : forall a sz lo hi,
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

#[using="Type"] Lemma maps_subtract_keep : forall maps lo hi e, vmwf maps -> lo < hi ->
  In e maps -> (ehi e <= lo \/ hi <= elo e) -> In e (maps_subtract maps lo hi).
Proof.
  induction maps as [|[a sz] maps IH]; intros lo hi e Hwf Hlh Hin Hd; [destruct Hin|].
  destruct Hwf as [Hb Hp]. cbn. apply in_or_app. destruct Hin as [<-|Hin].
  - left. rewrite iv_subtract_disjoint; [left; reflexivity| | exact Hlh|].
    + specialize (Hb (a, sz) (or_introl eq_refl)). unfold elo, ehi in Hb. cbn in Hb. lia.
    + unfold elo, ehi in Hd. cbn in Hd. lia.
  - right. apply IH; auto. split; [intros e' H'; apply Hb; right; exact H'| inversion Hp; assumption].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma iv_subtract_contains : forall a sz lo hi x y,
  0 <= lo -> lo < hi ->
  bv_unsigned a <= x -> x < y -> y <= bv_unsigned a + bv_unsigned sz -> y <= 2^64 ->
  (y <= lo \/ hi <= x) ->
  exists e, In e (iv_subtract a sz lo hi) /\ elo e <= x /\ y <= ehi e.
Proof.
  intros a sz lo hi x y Hlo Hlh Hax Hxy Hy Hy64 Hd. unfold iv_subtract.
  pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 sz). unfold bv_modulus in *.
  destruct Hd as [Hd|Hd].
  - replace (bv_unsigned a <? lo) with true by (symmetry; apply Z.ltb_lt; lia).
    eexists. split; [apply in_or_app; left; left; reflexivity|]. unfold elo, ehi; cbn. rewrite unsigned_lit by lia. lia.
  - replace (hi <? bv_unsigned a + bv_unsigned sz) with true by (symmetry; apply Z.ltb_lt; lia).
    eexists. split; [apply in_or_app; right; left; reflexivity|]. unfold elo, ehi; cbn. rewrite !unsigned_lit by lia. lia.
Qed.

#[using="Type"] Lemma maps_subtract_In_intro : forall maps lo hi e e', In e maps -> In e' (iv_subtract (fst e) (snd e) lo hi) ->
  In e' (maps_subtract maps lo hi).
Proof.
  induction maps as [|[a sz] maps IH]; intros lo hi e e' Hin H'; [destruct Hin|].
  cbn. apply in_or_app. destruct Hin as [<-|Hin]; [left; exact H'| right; eapply IH; eauto].
Qed.

#[using="Type"] Lemma pwdisj_app : forall P R, pwdisj P -> pwdisj R -> (forall p r, In p P -> In r R -> edisj p r) -> pwdisj (P ++ R).
Proof.
  induction P as [|p P IH]; intros R HP HR Hx; [exact HR|]. inversion HP; subst. cbn. constructor.
  - intros e' He'. apply in_app_or in He' as [He'|He']; [auto|]. apply Hx; [left; reflexivity| exact He'].
  - apply IH; auto. intros p' r Hp' Hr. apply Hx; [right; exact Hp'| exact Hr].
Qed.

#[using="Type"] Lemma iv_subtract_pwdisj : forall a sz lo hi, 0 <= lo -> lo < hi -> bv_unsigned a + bv_unsigned sz <= 2^64 ->
  pwdisj (iv_subtract a sz lo hi).
Proof.
  intros a sz lo hi Hlo Hlh Hwf. unfold iv_subtract.
  pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 sz). unfold bv_modulus in *.
  destruct (Z.ltb_spec (bv_unsigned a) lo); destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); cbn [app].
  - constructor; [|constructor; [intros e' []| constructor]]. intros e' [<-|[]].
    unfold edisj, elo, ehi; cbn. rewrite !unsigned_lit by lia. left. lia.
  - constructor; [intros e' []| constructor].
  - constructor; [intros e' []| constructor].
  - constructor.
Qed.

#[using="Type"] Lemma vmwf_subtract : forall maps lo hi, 0 <= lo -> lo < hi -> vmwf maps -> vmwf (maps_subtract maps lo hi).
Proof.
  induction maps as [|[a sz] maps IH]; intros lo hi Hlo Hlh [Hb Hp]; [split; [intros e []| constructor]|].
  inversion Hp; subst. assert (Hwf' : vmwf maps) by (split; [intros e He; apply Hb; right; exact He| assumption]).
  specialize (IH lo hi Hlo Hlh Hwf'). destruct IH as [IHb IHp].
  assert (Ha : elo (a, sz) < ehi (a, sz) <= 2^64) by (apply Hb; left; reflexivity). unfold elo, ehi in Ha; cbn in Ha.
  cbn. split.
  - intros e Hin. apply in_app_or in Hin as [Hin|Hin]; [|apply IHb; exact Hin].
    pose proof (iv_subtract_sub a sz lo hi e ltac:(lia) ltac:(lia) Hlo Hin). lia.
  - apply pwdisj_app; [apply iv_subtract_pwdisj; [exact Hlo| exact Hlh| lia]| exact IHp|].
    intros e e' He He'. pose proof (iv_subtract_sub a sz lo hi e ltac:(lia) ltac:(lia) Hlo He) as S1.
    destruct (maps_subtract_In _ _ _ _ He') as (e0 & H0 & H0').
    assert (W0 : elo e0 < ehi e0 <= 2^64) by (apply Hb; right; exact H0). destruct e0 as [a0 s0]. unfold elo, ehi in W0; cbn in W0.
    pose proof (iv_subtract_sub a0 s0 lo hi e' ltac:(lia) ltac:(lia) Hlo H0') as S2.
    pose proof (H1 _ H0) as D. unfold edisj, elo, ehi in *. cbn in *. lia.
Qed.

#[using="Type"] Lemma wcov_mono : forall maps maps' lo hi, (forall e, In e maps -> In e maps') -> wcov maps lo hi -> wcov maps' lo hi.
Proof. intros maps maps' lo hi Hs Hc x Hx. destruct (Hc x Hx) as (e & He & Hr). exists e. auto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma nstep_brk_inv : forall req mo rsp mo' evs,
  nstep (NBrk req) mo rsp mo' evs ->
  let h := m_vmmaps mo in
  exists r, brk_r_ok mo (Z_to_bv 64 req) r = true
    /\ mo' = with_brk_next mo (Z_to_bv 64 req) r
    /\ rsp = mkEffectU r [] (brk_zeros (Z_to_bv 64 req) r (vm_brk h)) (brk_unmaps r (vm_brk h)) [] []
    /\ evs = [].
Proof.
  intros req mo rsp mo' evs H. apply nstep_brk_iff in H as (-> & r & Hr & -> & -> & _).
  exists r. repeat split; auto.
Qed.

#[using="Type"] Lemma m_vmmaps_brk : forall mo req r, m_vmmaps (with_brk_next mo req r) = brk_model_next (m_vmmaps mo) req r.
Proof. intros. apply m_vmmaps_with_brk_next. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma brk_unmaps_nil : forall r b, bv_unsigned b <= bv_unsigned r -> brk_unmaps r b = [].
Proof.
  intros r b H. unfold brk_unmaps, brk_page_range.
  replace (page_round_up_Z (bv_unsigned r) <? page_round_up_Z (bv_unsigned b)) with false
    by (symmetry; apply Z.ltb_ge; apply page_round_up_Z_mono; lia).
  destruct (0 <? _); reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma brk_model_next_query : forall h,
  let h' := brk_model_next h (Z_to_bv 64 0) (vm_brk h) in
  vm_reserved h' = vm_reserved h /\ vm_maps h' = vm_maps h /\ vm_noaccess h' = vm_noaccess h
  /\ vm_start_brk h' = vm_start_brk h /\ vm_brk h' = vm_brk h.
Proof.
  intros h. cbn [brk_model_next vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk].
  unfold brk_maps_next. rewrite Z.ltb_irrefl, andb_false_r. unfold brk_grants. change (w_is0 (Z_to_bv 64 0)) with true. cbn [negb andb app].
  rewrite brk_unmaps_nil by lia. cbn. repeat split; reflexivity.
Qed.

#[using="Type"] Lemma brk_r_ok_query : forall mo r, brk_r_ok mo (Z_to_bv 64 0) r = true -> r = vm_brk (m_vmmaps mo).
Proof. intros mo r H. unfold brk_r_ok in H. change (w_is0 (Z_to_bv 64 0)) with true in H. cbn [orb] in H. apply bv_eqb_eq in H. exact H. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma brk_model_next_same : forall h req,
  let h' := brk_model_next h req (vm_brk h) in
  vm_reserved h' = vm_reserved h /\ vm_maps h' = vm_maps h /\ vm_noaccess h' = vm_noaccess h
  /\ vm_start_brk h' = vm_start_brk h /\ vm_brk h' = vm_brk h.
Proof.
  intros h req. cbn [brk_model_next vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk].
  unfold brk_maps_next. rewrite Z.ltb_irrefl, andb_false_r. unfold brk_grants, brk_is_grow. rewrite Z.ltb_irrefl, andb_false_r. cbn [app].
  rewrite brk_unmaps_nil by lia. cbn. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma brk_model_next_grown : forall h req,
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
  rewrite brk_unmaps_nil by (rewrite unsigned_lit by lia; lia).
  assert (Hsub : (Z_to_bv 64 req - vm_brk h)%bv = Z_to_bv 64 (req - b)).
  { apply bv_eq. rewrite bv_sub_unsigned, unsigned_lit by lia. fold b. rewrite Z_to_bv_unsigned. reflexivity. }
  rewrite Hsub. cbn. repeat split; reflexivity.
Qed.

#[using="Type"] Lemma brk_r_ok_grow : forall mo req r,
  let h := m_vmmaps mo in
  let b := bv_unsigned (vm_brk h) in
  bv_unsigned (vm_start_brk h) <= b -> b < req < 2^64 ->
  brk_r_ok mo (Z_to_bv 64 req) r = true ->
  (r = vm_brk h) \/ (r = Z_to_bv 64 req /\ brk_grow_ok mo (Z_to_bv 64 req) (Z_to_bv 64 req) = true).
Proof.
  intros mo req r h b Hs Hreq H. pose proof (bv_unsigned_in_range 64 (vm_brk h)) as Hr0. unfold bv_modulus in Hr0. fold b in Hr0.
  unfold brk_r_ok in H. fold h in H. rewrite w_is0_lit in H by lia.
  replace (req =? 0) with false in H by (symmetry; apply Z.eqb_neq; lia).
  unfold min_brk in H. rewrite unsigned_lit in H by lia.
  replace (req <? bv_unsigned (vm_start_brk h)) with false in H by (symmetry; apply Z.ltb_ge; lia).
  fold b in H. replace (req <? b) with false in H by (symmetry; apply Z.ltb_ge; lia). cbn [orb] in H.
  apply andb_prop in H as [H1 H2]. apply orb_prop in H1 as [H1|H1]; apply bv_eqb_eq in H1; subst r; [right|left]; auto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ceil_le_top : forall h, alloc_ceiling = page_round_down_Z (alloc_top h) -> alloc_ceiling <= alloc_top h.
Proof.
  intros h E. rewrite E. unfold page_round_down_Z, page_size.
  pose proof (Z.div_mod (alloc_top h) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (alloc_top h) 4096 ltac:(lia)). lia.
Qed.

#[using="Type"] Lemma top_le_ceil_aligned : forall h x, alloc_ceiling = page_round_down_Z (alloc_top h) ->
  x mod 4096 = 0 -> x <= alloc_top h -> x <= alloc_ceiling.
Proof. intros h x E Hx Hle. rewrite E. apply page_round_down_Z_ge_aligned; assumption. Qed.

#[using="Type"] Lemma band_le_top : forall h, alloc_ceiling = page_round_down_Z (alloc_top h) -> band_ceiling <= alloc_top h.
Proof. intros h E. pose proof (ceil_le_top h E). ceil_bounds. unfold band_ceiling. lia. Qed.

#[using="Type"] Lemma region_free_shrink : forall maps (a : word) n1 n2, 0 <= n2 <= n1 -> n1 < 2^64 ->
  region_free maps a (Z_to_bv 64 n1) = true -> region_free maps a (Z_to_bv 64 n2) = true.
Proof.
  induction maps as [|[e sz] maps IH]; intros a n1 n2 Hn Hn1 H; [reflexivity|].
  cbn [region_free] in H |- *. apply andb_prop in H as [H1 H2]. rewrite (IH a n1 n2 Hn Hn1 H2), andb_true_r.
  apply negb_true_iff in H1. apply negb_true_iff. unfold iv_overlap in *. rewrite unsigned_lit in H1 by lia. rewrite unsigned_lit by lia.
  apply andb_false_iff in H1 as [H1|H1]; apply Z.ltb_ge in H1; apply andb_false_iff; [left|right]; apply Z.ltb_ge; lia.
Qed.

#[using="Type"] Lemma brk_grow_ok_facts : forall mo req,
  let h := m_vmmaps mo in
  let b := bv_unsigned (vm_brk h) in
  alloc_ceiling = page_round_down_Z (alloc_top h) ->      (* [comment removed for export] *)
  0 < b -> b < req < 2^64 -> b mod 4096 = 0 -> req mod 4096 = 0 ->
  brk_grow_ok mo (Z_to_bv 64 req) (Z_to_bv 64 req) = true ->
  req <= alloc_ceiling /\ region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 b) (Z_to_bv 64 (req - b)) = true
  /\ vm_backing_used mo + (req - b) <= vm_limit h.
Proof.
  intros mo req h b Htop Hb Hreq Hba Hra H. unfold brk_grow_ok in H. fold h in H. rewrite unsigned_lit in H by lia. fold b in H.
  replace (0 <? b) with true in H by (symmetry; apply Z.ltb_lt; lia).
  replace (b <? req) with true in H by (symmetry; apply Z.ltb_lt; lia). cbn [andb] in H.
  unfold page_round_up_Z in H. rewrite page_size_eq in H.
  replace ((b + 4096 - 1) / 4096 * 4096) with b in H.
  2:{ pose proof (Z_div_mod_eq_full b 4096). pose proof (Z_div_mod_eq_full (b+4096-1) 4096). pose proof (Z.mod_pos_bound (b+4096-1) 4096). nia. }
  replace ((req + 4096 - 1) / 4096 * 4096) with req in H.
  2:{ pose proof (Z_div_mod_eq_full req 4096). pose proof (Z_div_mod_eq_full (req+4096-1) 4096). pose proof (Z.mod_pos_bound (req+4096-1) 4096). nia. }
  replace (b <? req) with true in H by (symmetry; apply Z.ltb_lt; lia).
  apply andb_prop in H as [H Hbud]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1.
  unfold brk_budget_ok in Hbud. fold h in Hbud. apply Z.leb_le in Hbud.
  assert (Hsub : bv_unsigned (Z_to_bv 64 req - vm_brk h)%bv = req - b).
  { rewrite bv_sub_unsigned, unsigned_lit by lia. fold b. apply bv_wrap_small. unfold bv_modulus. lia. }
  rewrite Hsub in Hbud.
  pose proof (alloc_top_page_lt h) as Htl. unfold two_pow_64 in Htl. rewrite page_size_eq in Htl.
  split; [exact (top_le_ceil_aligned h req Htop Hra H1)|]. split; [|exact Hbud].
  (* [comment removed for export] *)
  apply (region_free_shrink _ _ (req + 4096 - b) (req - b)); [lia|lia|exact H2].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma nstep_mmap_fixed_inv : forall a mo rsp mo' evs,
  let h := m_vmmaps mo in
  let aw := Z_to_bv 64 a in let n := Z_to_bv 64 PGSZ in
  alloc_ceiling = page_round_down_Z (alloc_top h) ->      (* [comment removed for export] *)
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
  intros a mo rsp mo' evs h aw n Htop Ha Hc Hal Hrf Hmc H.
  pose proof alloc_ceiling_lt as Hcl. pose proof (ceil_le_top h Htop) as Hct.
  pose proof (nstep_mm_vm_only (NMmap a PGSZ PROT_NONE MAPFX) mo rsp mo' evs ltac:(reflexivity) H) as (Hv & -> & _). split; [reflexivity|]. split; [exact Hv|].
  assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; unfold PGSZ in *; lia).
  assert (Un : bv_unsigned n = PGSZ) by (subst n; apply unsigned_lit; unfold PGSZ; lia).
  (* [comment removed for export] *)
  apply nstep_mmap_fixed_noaccess_outcome in H;
    [| reflexivity | reflexivity
     | rewrite w_is0_lit by (unfold PGSZ; lia); reflexivity
     | reflexivity | reflexivity | reflexivity
     | fold aw; rewrite Ua, (unsigned_lit PGSZ) by (unfold PGSZ; lia); change (page_round_up_Z PGSZ) with PGSZ; fold h; lia
     | fold aw; rewrite Ua, page_size_eq; exact Hal
     | fold aw; rewrite Ua; exact Ha
     | fold aw; rewrite (unsigned_lit PGSZ) by (unfold PGSZ; lia); change (page_round_up_Z PGSZ) with PGSZ; fold n; exact Hrf
     | fold aw; rewrite (unsigned_lit PGSZ) by (unfold PGSZ; lia); change (page_round_up_Z PGSZ) with PGSZ; fold n; exact Hmc ].
  fold aw h in H. rewrite (unsigned_lit PGSZ) in H by (unfold PGSZ; lia). change (page_round_up_Z PGSZ) with PGSZ in H. fold n in H.
  apply Ok_inj in H as (-> & -> & _).
  exists FxDone. split.
  - unfold dec_mmap_fixed. subst aw n. change (mmap_len PGSZ) with PGSZ. rewrite !bv_eqb_refl. cbn [andb].
    rewrite errno_of_lit by (unfold PGSZ in *; lia). reflexivity.
  - unfold with_mmap_replacement. rewrite with_mmap_backing_id by reflexivity. rewrite m_vmmaps_vm_forget_range, m_vmmaps_with_vmmaps.
    rewrite Ua, Un. reflexivity.
Qed.
End WithCeil.


Ltac kl_open HK := destruct HK as [Kminv Khalt Kwf Kresv Krt Kstart Kgr Kme Kdis Kreg Kph Kgran Kbb Kbhi Kstatic Kgrv Knoacc Ktop].

(* [comment removed for export] *)
Section WithCeil.
Context {CE : CEIL}.
#[using="Type"] Lemma kl_noacc_hi : forall L pbrk mo e, KL L pbrk mo -> In e (vm_noaccess (m_vmmaps mo)) -> ehi e <= alloc_ceiling.
Proof.
  intros L pbrk mo e HK He. destruct (kl_noacc _ _ _ HK e He) as [(b & l & k & Hm & _ & H2)|(b0 & l0 & E & _ & H2)].
  - pose proof (kl_metas _ _ _ HK b l k Hm) as ([_ _] & _ & _ & B & _). lia.
  - pose proof (kl_brkreg _ _ _ HK b0 l0 E) as (_ & _ & R3 & _ & R5 & _). unfold PGSZ in *. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma kl_noacc_piece : forall L pbrk mo lo hi e', KL L pbrk mo -> 0 <= hi ->
  In e' (maps_subtract (vm_noaccess (m_vmmaps mo)) lo hi) ->
  exists e, In e (vm_noaccess (m_vmmaps mo)) /\ elo e <= elo e' /\ ehi e' <= ehi e.
Proof.
  intros L pbrk mo lo hi e' HK Hhi He'. destruct (maps_subtract_In _ _ _ _ He') as (e & He & Hsub).
  pose proof (kl_noacc_hi _ _ _ e HK He) as W. pose proof alloc_ceiling_lt.
  exists e. split; [exact He|]. apply (iv_subtract_sub' (fst e) (snd e) lo hi e'); [unfold ehi in W; lia| exact Hhi| exact Hsub].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma kl_noacc_subtract : forall L pbrk mo lo hi L', KL L pbrk mo -> 0 <= hi ->
  (forall b l k, In (b, l, k) (ld_metas L) -> exists k', In (b, l, k') (ld_metas L')) -> ld_brkreg L' = ld_brkreg L ->
  forall e', In e' (maps_subtract (vm_noaccess (m_vmmaps mo)) lo hi) ->
    (exists b l k, In (b, l, k) (ld_metas L') /\ b <= elo e' /\ ehi e' <= b + mmap_len l)
    \/ (exists b0 l0, ld_brkreg L' = Some (b0, l0) /\ b0 <= elo e' /\ ehi e' <= b0 + PGSZ).
Proof.
  intros L pbrk mo lo hi L' HK Hhi Hme Hreg e' He'. destruct (kl_noacc_piece _ _ _ lo hi e' HK Hhi He') as (e & He & H1 & H2).
  destruct (kl_noacc _ _ _ HK e He) as [(b & l & k & Hm & Hb1 & Hb2)|(b0 & l0 & E & Hb1 & Hb2)].
  - left. destruct (Hme b l k Hm) as [k' Hm']. exists b, l, k'. split; [exact Hm'|]. lia.
  - right. exists b0, l0. rewrite Hreg. split; [exact E|]. lia.
Qed.

(* [comment removed for export] *)
End WithCeil.

Ltac kl_resv_keep Kresv :=
  intros r Hr; destruct (Kresv r Hr) as (e & C1 & C2 & [He|(He & Hfl & C3)]);
  [ exists e; split; [exact C1|]; split; [exact C2|]; left; exact He
  | exists e; split; [exact C1|]; split; [exact C2|]; right; split; [cbn; auto with datatypes|]; split; [exact Hfl|];
    first [exact C3| cbn; intros; eapply C3; eauto] ].

Section WithCeil.
Context {CE : CEIL}.
#[using="Type"] Lemma cover_in_app : forall (e : word * word) resv maps (P : Prop), In e resv \/ (In e maps /\ P) -> In e (resv ++ maps).
Proof. intros e resv maps P [H|[H _]]; apply in_or_app; [left| right]; exact H. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma minv_pres' : forall n mo eff mo' evs, nstep n mo eff mo' evs -> node_static_ok n ->
  minv mo -> m_halted mo = None -> m_halted mo' = None /\ minv mo'.
Proof. intros n mo eff mo' evs Hst Hs Hm Hh. exact (minv_preserved n mo eff mo' evs Hs Hm Hh Hst). Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma KL_vm_eq : forall L pbrk mo mo',
  KL L pbrk mo -> minv mo' -> m_halted mo' = None ->
  vm_reserved (m_vmmaps mo') = vm_reserved (m_vmmaps mo) ->
  vm_maps (m_vmmaps mo') = vm_maps (m_vmmaps mo) ->
  vm_noaccess (m_vmmaps mo') = vm_noaccess (m_vmmaps mo) ->
  vm_start_brk (m_vmmaps mo') = vm_start_brk (m_vmmaps mo) ->
  vm_brk (m_vmmaps mo') = vm_brk (m_vmmaps mo) ->
  vm_limit (m_vmmaps mo') = vm_limit (m_vmmaps mo) ->
  vm_init_sp (m_vmmaps mo') = vm_init_sp (m_vmmaps mo) ->      (* [comment removed for export] *)
  KL L pbrk mo'.
Proof.
  intros L pbrk mo mo' K Hmi Hh H1 H2 H3 H4 H5 H6 H7. kl_open K; constructor; rewrite ?H1, ?H2, ?H3, ?H4, ?H5, ?H6; auto.
  unfold alloc_top. rewrite H7. exact Ktop.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma kl_top_step : forall L pbrk mo n eff mo' evs, KL L pbrk mo ->
  match n with NMmap _ _ _ _ | NBrk _ | NMunmap _ _ | NMprotect _ _ _ | NMremap _ _ _ => True | _ => False end ->
  nstep n mo eff mo' evs -> alloc_ceiling = page_round_down_Z (alloc_top (m_vmmaps mo')).
Proof.
  intros L pbrk mo n eff mo' evs K Hn Hst. rewrite (sp_same_alloc_top _ _ (nstep_mm_sp_same _ _ _ _ _ Hn Hst)). exact (kl_top _ _ _ K).
Qed.

(* [comment removed for export] *)
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

#[using="Type"] Lemma KL_rephase : forall L ph pbrk pbrk' mo,
  KL L pbrk mo -> phase_inv ph L pbrk' mo -> match ph with BPGuard _ => False | _ => True end -> KL (set_brkph ph L) pbrk' mo.
Proof.
  intros L ph pbrk pbrk' mo K Hph Hng. kl_open K; constructor; cbn; auto.
  intros r Hr. destruct (Kresv r Hr) as (e & C1 & C2 & [He|(He & [P1 P2] & C3)]); exists e; (split; [exact C1|]); (split; [exact C2|]); [left; exact He| right].
  split; [exact He|]. split; [| exact C3]. split; [exact P1|]. cbn. intros cur ->. destruct Hng.
Qed.

#[using="Type"] Lemma KL_dead : forall L pbrk pbrk' mo, KL L pbrk mo -> KL (set_brkph BPDead L) pbrk' mo.
Proof. intros. eapply KL_rephase; [eassumption| exact I| exact I]. Qed.

Section Main.
Context {St : Type} {AS : AllocSt St}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma ev_brk0_ok : forall L G s0, frame_ok G -> ld_brk L = BPUntried ->
  mspec (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ G s mo)
        (r <- msys (NBrk 0) dec_brk0 ;; mupd (set_brk_ps r) ;;; mret r)
        (ev_step_post L (EBrk 0) G s0).
Proof.
  intros L G s0 HG Hph.
  eapply mspec_bind.
  { apply (mspec_sys (NBrk 0) dec_brk0 _ (fun r s mo => s = s0 /\ G s mo /\ brk0_answer_ok r = true /\ KL (set_brkph (BPQueried r) L) r mo)).
    intros s mo (-> & HK & HGs). split; [apply nsafe_brk|].
    intros rsp mo' evs Hst.
    pose proof (minv_pres' _ _ _ _ _ Hst ltac:(exact I || reflexivity) (kl_minv _ _ _ HK) (kl_halt _ _ _ HK)) as [Hh' Hmi'].
    pose proof (nstep_dec_brk0 _ _ _ _ Hst) as (_ & Hdec & Hvo & Hbrk).
    pose proof (nstep_brk_inv _ _ _ _ _ Hst) as (r & Hr & Emo' & _ & _).
    apply brk_r_ok_query in Hr. subst r.
    pose proof (brk_model_next_query (m_vmmaps mo)) as (E1 & E2 & E3 & E4 & E5).
    exists (bv_unsigned (vm_brk (m_vmmaps mo))). split; [exact Hdec|].
    assert (HK' : KL L (ps_brk s0) mo').
    { eapply KL_vm_eq; [exact HK| exact Hmi'| exact Hh'| | | | | | |]; rewrite Emo', m_vmmaps_brk; first [assumption| reflexivity]. }
    pose proof (kl_phase _ _ _ HK') as Kph. rewrite Hph in Kph. destruct Kph as [Ebrk Ereg].
    pose proof (kl_start _ _ _ HK') as (S1 & S2 & S3 & S4).
    splits.
    - reflexivity.
    - eapply HG; [reflexivity| exact Hvo| exact HGs].
    - unfold brk0_answer_ok. rewrite <- Hbrk, Ebrk. pose proof (bv_unsigned_in_range 64 (vm_start_brk (m_vmmaps mo'))) as R. unfold bv_modulus in R.
      unfold TWO64. rewrite (proj2 (Z.ltb_lt 0 _)) by lia. rewrite S2, Z.eqb_refl. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
    - eapply KL_rephase; [exact HK'| | exact I]. cbn [phase_inv]. rewrite <- Hbrk, Ebrk. splits; auto. }
  intros r. cbn beta. eapply mspec_bind.
  { apply mspec_upd. }
  intros []. apply mspec_ret. intros s mo (s1 & -> & -> & HGs & Hans & HK). unfold ev_step_post. cbn [answer_ok event_post Z.eqb].
  autorewrite with alloc_lens. splits; auto. eapply (HG s0); [apply ps_rest_set_brk| apply vm_only_refl| exact HGs].
Qed.

#[using="Type"] Lemma mspec_get_bind_eq {A} (s0 : St) (P : assn St) (f : St -> Monad.M St A) Q :
  mspec (fun s mo => s = s0 /\ P s mo) (f s0) Q -> mspec (fun s mo => s = s0 /\ P s mo) (x <- mget ;; f x) Q.
Proof. intros H s mo [-> HP]. unfold mbind, mget. cbn. apply H. auto. Qed.

#[using="Type"] Lemma elo_pair : forall a n, elo (a, n) = bv_unsigned a. Proof. reflexivity. Qed.
#[using="Type"] Lemma ehi_pair : forall a n, ehi (a, n) = bv_unsigned a + bv_unsigned n. Proof. reflexivity. Qed.

#[using="Type"] Lemma went_In_bounds : forall L pbrk mo b l, KL L pbrk mo ->
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

#[using="Type"] Lemma In_lranges : forall L x, In x (lranges L) ->
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

(* [comment removed for export] *)
#[using="Type"] Lemma KL_lbrk_pages_ok : forall L pbrk mo lo len,
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
  unfold lbrk_pages_ok. rewrite (proj2 (Z.ltb_lt 0 lo)) by lia. rewrite (proj2 (Z.leb_le _ _) Hceil). cbn [andb].
  unfold ranges_free. apply forallb_forall. intros [b0 m0] Hin. cbn [fst snd]. unfold iv_disjoint.
  enough (lo + len <= b0 \/ b0 + m0 <= lo) as D.
  { destruct D as [D|D]; [rewrite (proj2 (Z.leb_le _ _) D); reflexivity| rewrite (proj2 (Z.leb_le _ _) D); apply orb_true_r]. }
  apply In_lranges in Hin as [H|[(b1 & l1 & H & E)|[(b1 & l1 & k & H & E)|(b1 & l1 & H & E)]]].
  - destruct (kl_resv _ _ _ HK _ H) as ([e sz] & C1 & C2 & He). apply cover_in_app in He. unfold elo, ehi in C1, C2. cbn [fst snd] in C1, C2.
    pose proof (region_free_In _ _ _ _ _ Hrf He) as D. rewrite Ulo, Ulen in D. lia.
  - injection E as -> ->. pose proof (went_In_bounds _ _ _ b1 l1 HK (or_introl H)) as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (region_free_disj _ _ _ _ Hrfm B4) as D. rewrite B5, B6, Ulo, Ulen in D. rewrite round_up_pg_eq. fold (mmap_len l1). exact D.
  - injection E as -> ->. pose proof (went_In_bounds _ _ _ b1 l1 HK (or_intror (ex_intro _ k H))) as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (region_free_disj _ _ _ _ Hrfm B4) as D. rewrite B5, B6, Ulo, Ulen in D. rewrite round_up_pg_eq. fold (mmap_len l1). exact D.
  - injection E as -> ->. destruct (Hbrk b1 l1 H) as [Al D]. rewrite round_up_pg_aligned by (unfold PGSZ in Al; exact Al). lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma ev_brk_grow1_ok : forall L G s0 cur, frame_ok G -> ld_brk L = BPQueried cur ->
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
    intros s mo (-> & HK & HGs). split; [apply nsafe_brk|].
    intros rsp mo' evs Hst.
    pose proof (minv_pres' _ _ _ _ _ Hst ltac:(exact I || reflexivity) (kl_minv _ _ _ HK) (kl_halt _ _ _ HK)) as [Hh' Hmi'].
    pose proof (kl_phase _ _ _ HK) as Kph. rewrite Hph in Kph. destruct Kph as (Ecur & Ebrk & Epbrk & Ereg).
    pose proof (kl_start _ _ _ HK) as (S1 & S2 & S3 & S4).
    assert (Hreq : req = cur + 2 * PGSZ). { subst req. rewrite round_up_pg_aligned; [reflexivity|]. rewrite Ecur. exact S2. }
    pose proof (nstep_brk_inv _ _ _ _ _ Hst) as (r & Hr & Emo' & _ & _).
    apply brk_r_ok_grow in Hr; [| lia| unfold PGSZ in *; lia].
    assert (Hr' : r = vm_brk (m_vmmaps mo) \/ (r = Z_to_bv 64 req /\ (req <= alloc_ceiling /\ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (Z_to_bv 64 (bv_unsigned (vm_brk (m_vmmaps mo)))) (Z_to_bv 64 (req - bv_unsigned (vm_brk (m_vmmaps mo)))) = true /\ vm_backing_used mo + (req - bv_unsigned (vm_brk (m_vmmaps mo))) <= vm_limit (m_vmmaps mo)))).
    { destruct Hr as [E|[E Hgo]]; [left; exact E| right; split; [exact E|]].
      apply (brk_grow_ok_facts _ _ (kl_top _ _ _ HK)) in Hgo; [exact Hgo| lia| unfold PGSZ in *; lia| rewrite Ebrk, Ecur; exact S2| rewrite Hreq, Ecur; unfold PGSZ in *; rewrite Z.add_mod, S2 by lia; reflexivity]. }
    clear Hr. rename Hr' into Hr.
    pose proof (nstep_dec_brk req mo rsp mo' evs ltac:(lia) ltac:(lia) ltac:(unfold PGSZ in *; lia) Hst) as (_ & Hvo & a & Hdec & Ha).
    set (h := m_vmmaps mo) in *.
    rewrite Ebrk in Hdec. rewrite Epbrk. exists a. split; [exact Hdec|].
    split; [reflexivity|]. split; [eapply HG; [reflexivity| exact Hvo| exact HGs]|].
    split; [unfold PGSZ in *; lia|]. split; [reflexivity|].
    pose proof (brk_model_next_same h (Z_to_bv 64 req)) as (Q1 & Q2 & Q3 & Q4 & Q5).
    pose proof (brk_model_next_grown h req ltac:(lia) ltac:(unfold PGSZ in *; lia)) as (P1 & P2 & P3 & P4 & P5).
    destruct a.
    - (* [comment removed for export] *)
      destruct Hr as [-> | [-> Hgo]].
      { exfalso. rewrite Emo', m_vmmaps_brk in Ha. fold h in Ha. rewrite Q5 in Ha.
        apply (f_equal bv_unsigned) in Ha. rewrite unsigned_lit in Ha by (unfold PGSZ in *; lia). lia. }
      destruct Hgo as (Hceil & Hrf & _).
      assert (HPG : lbrk_pages_ok L (round_up_pg cur) (2 * PGSZ) = true).
      { rewrite round_up_pg_aligned by (rewrite Ecur; unfold PGSZ in S2; exact S2).
        apply (KL_lbrk_pages_ok L (ps_brk s0) mo cur (2 * PGSZ) HK); [lia| unfold PGSZ; lia| lia| | intros b l Hb; rewrite Ereg in Hb; discriminate].
        replace cur with (bv_unsigned (vm_brk h)) at 1 by exact Ebrk. replace (Z_to_bv 64 (2 * PGSZ)) with (Z_to_bv 64 (req - bv_unsigned (vm_brk h))) by (f_equal; lia). exact Hrf. }
      rewrite Z_to_bv_bv_unsigned in Hrf.
      assert (Hn : bv_unsigned (Z_to_bv 64 (req - bv_unsigned (vm_brk h))) = 2 * PGSZ) by (rewrite unsigned_lit; unfold PGSZ in *; lia).
      split; [|exact HPG].
      kl_open HK. constructor; try exact Hmi'; try exact Hh'; rewrite ?Emo', ?m_vmmaps_brk; fold h; cbn [set_brkph ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live];
        rewrite ?P1, ?P2, ?P3, ?P4, ?P5; auto.
      + apply vmwf_cons; [exact Kwf| rewrite Hn; unfold PGSZ in *; lia| eapply region_free_app_r; exact Hrf].
      + intros r Hr. destruct (Kresv r Hr) as ([e sz] & C1 & C2 & [He|(He & [PC1 PC2] & C3)]); exists (e, sz); (split; [exact C1|]); (split; [exact C2|]); [left; exact He| right].
        split; [cbn; right; exact He|]. split; [| exact C3]. split; [exact PC1|]. cbn. intros cur' E'. injection E' as <-.
        pose proof (region_free_In _ _ _ _ _ Hrf (in_or_app _ _ _ (or_intror He))) as D. rewrite Hn, Ebrk in D. unfold elo, ehi. cbn [fst snd]. lia.
      + rewrite unsigned_lit by (unfold PGSZ in *; lia). splits; try lia; auto.
      + intros b l Hin. specialize (Kgr b l Hin). unfold brk_disj in *. cbn. intuition auto with datatypes.
      + intros b l k Hin. specialize (Kme b l k Hin). unfold brk_disj in *. cbn. intuition auto with datatypes.
      + intros b l Hb. rewrite Ereg in Hb. discriminate.
      + rewrite unsigned_lit by (unfold PGSZ in *; lia). splits; auto; try lia.
        * exists (vm_brk h, Z_to_bv 64 (req - bv_unsigned (vm_brk h))). split; [left; reflexivity|]. rewrite elo_pair, ehi_pair, Hn. lia.
        * intros b l Hin. pose proof (went_In_bounds _ _ _ b l (mkKL _ _ _ Kminv Khalt Kwf Kresv Krt Kstart Kgr Kme Kdis Kreg Kph Kgran Kbb Kbhi Kstatic Kgrv Knoacc Ktop) (or_introl Hin)) as (B1 & B2 & B3 & B4 & B5 & B6).
          pose proof (region_free_disj _ _ _ _ (region_free_app_r _ _ _ _ Hrf) B4) as D. rewrite B5, B6, Hn in D. lia.
        * intros b l k Hin. pose proof (went_In_bounds _ _ _ b l (mkKL _ _ _ Kminv Khalt Kwf Kresv Krt Kstart Kgr Kme Kdis Kreg Kph Kgran Kbb Kbhi Kstatic Kgrv Knoacc Ktop) (or_intror (ex_intro _ k Hin))) as (B1 & B2 & B3 & B4 & B5 & B6).
          pose proof (region_free_disj _ _ _ _ (region_free_app_r _ _ _ _ Hrf) B4) as D. rewrite B5, B6, Hn in D. lia.
      + (* [comment removed for export] *) rewrite unsigned_lit by (unfold PGSZ in *; lia). intros e [E|He].
        * subst e. left. rewrite ehi_pair, Hn. unfold PGSZ in *; lia.
        * destruct (Kgran e He) as [Hle|Hg]; [left| right; exact Hg]. subst h. unfold PGSZ in *; lia.
      + (* [comment removed for export] *) rewrite unsigned_lit by (unfold PGSZ in *; lia). rewrite Ereg. subst h. unfold PGSZ in *; lia.
    - (* [comment removed for export] *)
      destruct Hr as [-> | [-> Hgo]].
      2:{ exfalso. rewrite Emo', m_vmmaps_brk in Ha. fold h in Ha. rewrite P5 in Ha.
          apply (f_equal bv_unsigned) in Ha. rewrite unsigned_lit in Ha by (unfold PGSZ in *; lia). lia. }
      apply KL_dead with (pbrk := ps_brk s0). eapply KL_vm_eq; [exact HK| exact Hmi'| exact Hh'| | | | | | |]; rewrite Emo', m_vmmaps_brk; fold h; first [assumption| reflexivity]. }
  intros a. cbn beta. destruct a.
  - eapply mspec_bind; [apply mspec_upd|]. intros []. apply mspec_ret.
    intros s mo (s1 & -> & -> & HGs & [Hne Hpos] & Ecur & [HK HPG]). unfold ev_step_post.
    cbn [answer_ok event_post]. autorewrite with alloc_lens.
    replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Hph, Z.eqb_refl.
    splits; auto.
    + unfold brk_answer_ok. rewrite Z.eqb_refl, HPG. reflexivity.
    + eapply (HG s0); [apply ps_rest_set_brk| apply vm_only_refl| exact HGs].
  - apply mspec_ret. intros s mo (-> & HGs & [Hne Hpos] & Ecur & HK). unfold ev_step_post.
    cbn [answer_ok event_post].
    replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Hph, Ecur.
    replace (cur =? req) with false by (symmetry; apply Z.eqb_neq; lia).
    splits; auto. unfold brk_answer_ok. rewrite Z.eqb_refl, orb_true_r. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma ev_brk_grow2_ok : forall L G s0 b l, frame_ok G -> ld_brk L = BPLive -> ld_brkreg L = Some (b, l) ->
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
    intros s mo (-> & HK & HGs). split; [apply nsafe_brk|].
    intros rsp mo' evs Hst.
    pose proof (minv_pres' _ _ _ _ _ Hst ltac:(exact I || reflexivity) (kl_minv _ _ _ HK) (kl_halt _ _ _ HK)) as [Hh' Hmi'].
    pose proof (kl_phase _ _ _ HK) as Kph. rewrite Hph in Kph. destruct Kph as (b' & l' & Ereg' & Ebrk & Epbrk).
    rewrite Ereg in Ereg'. injection Ereg' as <- <-.
    pose proof (kl_brkreg _ _ _ HK b l Ereg) as (R1 & R2 & R3 & R4 & R5 & Rcov).
    pose proof (kl_start _ _ _ HK) as (S1 & S2 & S3 & S4).
    pose proof (nstep_brk_inv _ _ _ _ _ Hst) as (r & Hr & Emo' & _ & _).
    apply brk_r_ok_grow in Hr; [| lia| unfold PGSZ in *; lia].
    assert (Hr' : r = vm_brk (m_vmmaps mo) \/ (r = Z_to_bv 64 req /\ (req <= alloc_ceiling /\ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (Z_to_bv 64 (bv_unsigned (vm_brk (m_vmmaps mo)))) (Z_to_bv 64 (req - bv_unsigned (vm_brk (m_vmmaps mo)))) = true /\ vm_backing_used mo + (req - bv_unsigned (vm_brk (m_vmmaps mo))) <= vm_limit (m_vmmaps mo)))).
    { destruct Hr as [E|[E Hgo]]; [left; exact E| right; split; [exact E|]].
      apply (brk_grow_ok_facts _ _ (kl_top _ _ _ HK)) in Hgo; [exact Hgo| lia| unfold PGSZ in *; lia| rewrite Ebrk; unfold PGSZ in *; rewrite Z.add_mod, R2, R4 by lia; reflexivity| subst req; unfold PGSZ in *; rewrite Z.add_mod, (Z.add_mod b l), R2, R4 by lia; reflexivity]. }
    clear Hr. rename Hr' into Hr.
    pose proof (nstep_dec_brk req mo rsp mo' evs ltac:(lia) ltac:(lia) ltac:(unfold PGSZ in *; lia) Hst) as (_ & Hvo & a & Hdec & Ha).
    set (h := m_vmmaps mo) in *.
    rewrite Ebrk in Hdec. rewrite Epbrk. exists a. split; [exact Hdec|].
    split; [reflexivity|]. split; [eapply HG; [reflexivity| exact Hvo| exact HGs]|].
    split; [unfold PGSZ in *; lia|]. split; [reflexivity|].
    pose proof (brk_model_next_same h (Z_to_bv 64 req)) as (Q1 & Q2 & Q3 & Q4 & Q5).
    pose proof (brk_model_next_grown h req ltac:(lia) ltac:(unfold PGSZ in *; lia)) as (P1 & P2 & P3 & P4 & P5).
    destruct a.
    - (* [comment removed for export] *)
      destruct Hr as [-> | [-> Hgo]].
      { exfalso. rewrite Emo', m_vmmaps_brk in Ha. fold h in Ha. rewrite Q5 in Ha.
        apply (f_equal bv_unsigned) in Ha. rewrite unsigned_lit in Ha by (unfold PGSZ in *; lia). lia. }
      destruct Hgo as (Hceil & Hrf & _).
      assert (HPG : lbrk_pages_ok L (b + l) PGSZ = true).
      { apply (KL_lbrk_pages_ok L (ps_brk s0) mo (b + l) PGSZ HK); [lia| unfold PGSZ; lia| subst req; lia| |].
        - replace (b + l) with (bv_unsigned (vm_brk h)) at 1 by exact Ebrk. replace (Z_to_bv 64 PGSZ) with (Z_to_bv 64 (req - bv_unsigned (vm_brk h))) by (f_equal; lia). exact Hrf.
        - intros b1 l1 E. rewrite Ereg in E. injection E as <- <-. split; [exact R4| left; lia]. }
      rewrite Z_to_bv_bv_unsigned in Hrf.
      assert (Hn : bv_unsigned (Z_to_bv 64 (req - bv_unsigned (vm_brk h))) = PGSZ) by (rewrite unsigned_lit; unfold PGSZ in *; lia).
      pose proof (fun b0 l0 H => went_In_bounds _ _ _ b0 l0 HK H) as WB.
      split; [|exact HPG].
      kl_open HK. constructor; try exact Hmi'; try exact Hh'; rewrite ?Emo', ?m_vmmaps_brk; fold h; cbn [set_brkreg ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live];
        rewrite ?P1, ?P2, ?P3, ?P4, ?P5; auto.
      + apply vmwf_cons; [exact Kwf| rewrite Hn; unfold PGSZ in *; lia| eapply region_free_app_r; exact Hrf].
      + intros r Hr. destruct (Kresv r Hr) as ([e sz] & C1 & C2 & [He|(He & [PC1 PC2] & C3)]); exists (e, sz); (split; [exact C1|]); (split; [exact C2|]); [left; exact He| right].
        split; [cbn; right; exact He|]. split; [| exact C3]. split; [| cbn; intros cur' E'; rewrite Hph in E'; discriminate].
        cbn. intros b1 l1 E'. injection E' as <- <-. specialize (PC1 b l Ereg).
        pose proof (region_free_In _ _ _ _ _ Hrf (in_or_app _ _ _ (or_intror He))) as D. rewrite Hn, Ebrk in D.
        pose proof (proj1 Kwf _ He) as W. unfold elo, ehi in *. cbn [fst snd] in *. clear - CE b l req mo Kstart h R1 R2 R3 R4 S1 S2 e sz PC1 D W. lia.
      + rewrite unsigned_lit by (unfold PGSZ in *; lia). splits; try (clear - CE b l req mo Kstart h Ebrk R1 R2 R3 R4 S1 S2 S3 S4; lia); auto.
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
      + (* [comment removed for export] *) rewrite unsigned_lit by (unfold PGSZ in *; lia). intros e [E|He].
        * subst e. left. rewrite ehi_pair, Hn. unfold PGSZ in *; lia.
        * destruct (Kgran e He) as [Hle|Hg]; [left| right; exact Hg]. subst h. unfold PGSZ in *; lia.
      + (* [comment removed for export] *) intros b1 l1 E. injection E as <- <-. exact (Kbb b l Ereg).
      + (* [comment removed for export] *) rewrite unsigned_lit by (unfold PGSZ in *; lia). pose proof (Kbb b l Ereg) as Eb. subst h. unfold PGSZ in *; lia.
      + (* [comment removed for export] *) intros e He. destruct (Knoacc e He) as [Hl|(b0 & l0 & E & Hb0)]; [left; exact Hl| right].
        rewrite Ereg in E. injection E as <- <-. exists b, (l + PGSZ). split; [reflexivity| exact Hb0].
    - (* [comment removed for export] *)
      destruct Hr as [-> | [-> Hgo]].
      2:{ exfalso. rewrite Emo', m_vmmaps_brk in Ha. fold h in Ha. rewrite P5 in Ha.
          apply (f_equal bv_unsigned) in Ha. rewrite unsigned_lit in Ha by (unfold PGSZ in *; lia). lia. }
      apply KL_dead with (pbrk := ps_brk s0). eapply KL_vm_eq; [exact HK| exact Hmi'| exact Hh'| | | | | | |]; rewrite Emo', m_vmmaps_brk; fold h; first [assumption| reflexivity]. }
  intros a. cbn beta. destruct a.
  - eapply mspec_bind; [apply mspec_upd|]. intros []. apply mspec_ret.
    intros s mo (s1 & -> & -> & HGs & [Hne Hpos] & Ecur & HK). unfold ev_step_post.
    cbn [answer_ok event_post]. autorewrite with alloc_lens.
    replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Hph, Ereg, Z.eqb_refl.
    destruct HK as [HK HPG].
    splits; auto.
    + unfold brk_answer_ok. rewrite Z.eqb_refl, HPG. reflexivity.
    + eapply (HG s0); [apply ps_rest_set_brk| apply vm_only_refl| exact HGs].
  - apply mspec_ret. intros s mo (-> & HGs & [Hne Hpos] & Ecur & HK). unfold ev_step_post.
    cbn [answer_ok event_post].
    replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Hph, Ereg, Ecur.
    replace (b + l =? req) with false by (symmetry; apply Z.eqb_neq; lia).
    splits; auto. unfold brk_answer_ok. rewrite Z.eqb_refl, orb_true_r. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma wcov_rf_disj : forall maps lo hi aw nw,
  wcov maps lo hi -> region_free maps aw nw = true -> 0 < bv_unsigned nw -> lo < hi ->
  bv_unsigned aw + bv_unsigned nw <= lo \/ hi <= bv_unsigned aw.
Proof.
  intros maps lo hi aw nw Hc Hrf Hn Hlh.
  destruct (Z_le_gt_dec (bv_unsigned aw + bv_unsigned nw) lo) as [|H1]; [left; assumption|].
  destruct (Z_le_gt_dec hi (bv_unsigned aw)) as [|H2]; [right; assumption|]. exfalso.
  destruct (Hc (Z.max (bv_unsigned aw) lo) ltac:(lia)) as (e & He & Hr).
  pose proof (region_free_disj _ _ _ _ Hrf He). lia.
Qed.



#[using="Type"] Lemma KL_mmap_new : forall L pbrk mo mo' a len (isnone : bool),
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
  (* [comment removed for export] *)
  assert (Dgm : forall b0 l0, (In (b0, l0) (ld_groups L) \/ exists k, In (b0, l0, k) (ld_metas L)) ->
                 a + n <= b0 \/ b0 + mmap_len l0 <= a).
  { intros b0 l0 H. pose proof (WB b0 l0 H) as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (region_free_disj _ _ _ _ Hrfm B4) as D. rewrite B5, B6, Ua, Un in D. exact D. }
  assert (Dbrk : forall b0 l0, ld_brkreg L = Some (b0, l0) -> a + n <= b0 \/ b0 + l0 <= a).
  { intros b0 l0 E. pose proof (kl_brkreg _ _ _ HK b0 l0 E) as (R1 & R2 & R3 & R4 & R5 & Rcov).
    pose proof (wcov_rf_disj _ _ _ _ _ Rcov Hrfm ltac:(rewrite Un; lia) ltac:(clear -R3; unfold PGSZ in *; lia)) as D. rewrite Ua, Un in D. exact D. }
  (* [comment removed for export] *)
  assert (Dresv : forall e, In e (vm_reserved h) -> a + n <= elo e \/ ehi e <= a).
  { intros [e sz] He. pose proof (region_free_In _ _ _ _ _ Hrf (in_or_app _ _ _ (or_introl He))) as D. rewrite Ua, Un in D. unfold elo, ehi. cbn [fst snd]. lia. }
  split; [|split].
  2:{ unfold mmap_answer_ok. apply orb_true_intro. right. rewrite Hround.
      rewrite (proj2 (Z.ltb_lt 0 a)) by lia. unfold PGSZ at 1. rewrite A1, Z.eqb_refl. rewrite (proj2 (Z.leb_le _ _) A3). cbn [andb].
      unfold ranges_free. apply forallb_forall. intros [lo m] Hin. cbn [fst snd]. unfold iv_disjoint.
      enough (a + n <= lo \/ lo + m <= a) as D.
      { destruct D as [D|D]; [rewrite (proj2 (Z.leb_le _ _) D); reflexivity| rewrite (proj2 (Z.leb_le _ _) D); apply orb_true_r]. }
      apply In_lranges in Hin as [H|[(b0 & l0 & H & E)|[(b0 & l0 & k & H & E)|(b0 & l0 & H & E)]]].
      - destruct (kl_resv _ _ _ HK _ H) as ([e sz] & C1 & C2 & He). apply cover_in_app in He. unfold elo, ehi in C1, C2. cbn [fst snd] in C1, C2.
        pose proof (region_free_In _ _ _ _ _ Hrf He) as D. rewrite Ua, Un in D. lia.
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
  - intros r Hr. destruct (Kresv r Hr) as ([e sz] & C1 & C2 & He). exists (e, sz). split; [exact C1|]. split; [exact C2|].
    pose proof (region_free_In _ _ _ _ _ Hrf (cover_in_app _ _ _ _ He)) as D. rewrite Ua, Un in D.
    destruct He as [He|(He & Hfl & C3)]; [left; exact He| right]. split; [right; exact He|]. split; [exact Hfl|].
    intros b0 l0 [Hb|[k [E|Hb]]]; [apply C3; left; exact Hb| | apply C3; right; exists k; exact Hb].
    injection E as <- <- <-. unfold elo, ehi. cbn [fst snd]. fold n. lia.
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
  - (* [comment removed for export] *) intros e [E|He]; [| exact (Kgran e He)]. subst e. right. rewrite elo_pair. cbn [snd]. rewrite Ua, Un.
    split; [lia|]. split; [subst n; unfold PGSZ; apply mmap_len_aligned| unfold PGSZ; exact A1].
  - (* [comment removed for export] *) intros b0 l0 [Hb|[k [E|Hb]]] e He; [apply (Kgrv b0 l0 (or_introl Hb)); exact He| | apply (Kgrv b0 l0 (or_intror (ex_intro _ k Hb))); exact He].
    injection E as <- <- <-. fold n. apply Dresv. exact He.
  - (* [comment removed for export] *) intros e [E|He].
    + subst e. left. exists a, len, 0. split; [left; reflexivity|]. rewrite elo_pair, ehi_pair, Ua, Un. fold n. lia.
    + destruct (Knoacc e He) as [(b0 & l0 & k & Hm & Hb)|Hr]; [left; exists b0, l0, k; split; [right; exact Hm| exact Hb]| right; exact Hr].
  - apply vmwf_cons; [exact Kwf| rewrite Ua, Un; lia| exact Hrfm].
  - intros r Hr. destruct (Kresv r Hr) as ([e sz] & C1 & C2 & He). exists (e, sz). split; [exact C1|]. split; [exact C2|].
    pose proof (region_free_In _ _ _ _ _ Hrf (cover_in_app _ _ _ _ He)) as D. rewrite Ua, Un in D.
    destruct He as [He|(He & Hfl & C3)]; [left; exact He| right]. split; [right; exact He|]. split; [exact Hfl|].
    intros b0 l0 [[E|Hb]|[k Hb]]; [| apply C3; left; exact Hb| apply C3; right; exists k; exact Hb].
    injection E as <- <-. unfold elo, ehi. cbn [fst snd]. fold n. lia.
  - intros b0 l0 [E|Hin].
    + injection E as <- <-. unfold brk_disj; cbn. splits; try lia.
      * unfold PGSZ; exact A1.
      * left; reflexivity.
      * exact Dbrk.
    + specialize (Kgr b0 l0 Hin). unfold brk_disj in *; cbn. intuition auto with datatypes.
  - intros b0 l0 k Hin. specialize (Kme b0 l0 k Hin). destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). unfold brk_disj in *; cbn. splits; try assumption; try (right; assumption).
  - cbn [map fst app]. constructor; [exact Hnotin| exact Kdis].
  - intros b0 l0 E. specialize (Kreg b0 l0 E). destruct Kreg as (R1 & R2 & R3 & R4 & R5 & Rcov). splits; auto. eapply wcov_mono; [|exact Rcov]. intros e He; right; exact He.
  - (* [comment removed for export] *) intros e [E|He]; [| exact (Kgran e He)]. subst e. right. rewrite elo_pair. cbn [snd]. rewrite Ua, Un.
    split; [lia|]. split; [subst n; unfold PGSZ; apply mmap_len_aligned| unfold PGSZ; exact A1].
  - (* [comment removed for export] *) intros b0 l0 [[E|Hb]|[k Hb]] e He; [| apply (Kgrv b0 l0 (or_introl Hb)); exact He| apply (Kgrv b0 l0 (or_intror (ex_intro _ k Hb))); exact He].
    injection E as <- <-. fold n. apply Dresv. exact He.
Qed.

#[using="Type"] Lemma is_errno_form_neg : forall e, 1 <= e <= 4095 -> is_errno_form (neg_errno e) = true.
Proof. intros e He. unfold is_errno_form, neg_errno, TWO64. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. Qed.
#[using="Type"] Lemma is_err_neg : forall e, 1 <= e <= 4095 -> is_err (neg_errno e) = true.
Proof. intros e He. unfold is_err, neg_errno, TWO64. apply Z.ltb_lt. lia. Qed.

#[using="Type"] Lemma ev_mmap_core : forall L G s0 len (isnone : bool), frame_ok G -> brk_quiet L -> 0 < len < LEN_MAX ->
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
    intros s mo (-> & HK & HGs). split.
    { subst prot. destruct isnone; [apply (nsafe_mmap_none 0 len mo)| apply (nsafe_mmap_rw 0 len mo)]; unfold LEN_MAX in Hlen; lia. }
    intros rsp mo' evs Hst.
    pose proof (minv_pres' _ _ _ _ _ Hst ltac:(exact I || reflexivity) (kl_minv _ _ _ HK) (kl_halt _ _ _ HK)) as [Hh' Hmi'].
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
      - pose proof (nstep_dec_mmap_none len [] mo rsp mo' evs ltac:(lia) ltac:(unfold LEN_MAX in *; lia) ltac:(rewrite <- (kl_top _ _ _ HK); lia) (Forall_nil _) Hst) as (_ & Hvo & x & Hd & Hx).
        split; [exact Hvo|]. exists x. split; [exact Hd|]. exact Hx.
      - pose proof (nstep_dec_mmap len [] mo rsp mo' evs ltac:(lia) ltac:(unfold LEN_MAX in *; lia) ltac:(rewrite <- (kl_top _ _ _ HK); lia) (Forall_nil _) Hst) as (_ & Hvo & x & Hd & Hx).
        split; [exact Hvo|]. exists x. split; [exact Hd|]. exact Hx. }
    destruct Hcase as (Hvo & x & Hd & Hx). exists x. split; [exact Hd|].
    split; [reflexivity|]. split; [eapply HG; [reflexivity| exact Hvo| exact HGs]|].
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

#[using="Type"] Lemma ev_mmap_ok : forall L G s0 len prot, frame_ok G -> brk_quiet L -> (prot = PROT_NONE \/ prot = PROT_RW) -> 0 < len < LEN_MAX ->
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma region_free_above : forall maps aw nw, (forall e, In e maps -> ehi e <= bv_unsigned aw) -> region_free maps aw nw = true.
Proof.
  induction maps as [|[e sz] maps IH]; intros aw nw H; [reflexivity|]. cbn [region_free].
  rewrite IH by (intros e' He'; apply H; right; exact He'). unfold iv_overlap.
  specialize (H (e, sz) (or_introl eq_refl)). unfold ehi in H; cbn in H.
  replace (bv_unsigned aw <? bv_unsigned e + bv_unsigned sz) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

#[using="Type"] Lemma ev_mmap_fixed_ok : forall L G s0 cur, frame_ok G -> ld_brk L = BPGuard cur ->
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
    assert (Hrf : region_free (vm_reserved h) aw nw = true).
    { apply region_free_above. intros e He. rewrite Ua, Ha, Ecur. apply (kl_resv_top _ _ _ HK). exact He. }
    assert (Hmc : map_contains (vm_maps h) aw nw = true).
    { unfold map_contains. apply existsb_exists. exists e0. split; [exact He0|]. rewrite Ua, Un. unfold elo, ehi in *.
      rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by (unfold PGSZ in *; lia). reflexivity. }
    split.
    { apply (nsafe_mmap_fixed_none a PGSZ mo); [unfold PGSZ; lia| lia| rewrite page_size_eq, Ha, Ecur; exact S2| | |].
      - change (page_round_up_Z PGSZ) with PGSZ. pose proof (ceil_le_top _ (kl_top _ _ _ HK)) as Hct. fold h in Hct |- *. unfold PGSZ in *. lia.
      - change (page_round_up_Z PGSZ) with PGSZ. exact Hrf.
      - change (page_round_up_Z PGSZ) with PGSZ. exact Hmc. }
    intros rsp mo' evs Hst.
    pose proof (minv_pres' _ _ _ _ _ Hst ltac:(exact I || reflexivity) (kl_minv _ _ _ HK) (kl_halt _ _ _ HK)) as [Hh' Hmi'].
    pose proof (nstep_mmap_fixed_inv a mo rsp mo' evs (kl_top _ _ _ HK) ltac:(lia) ltac:(lia) ltac:(rewrite Ha, Ecur; exact S2) Hrf Hmc Hst) as (_ & Hvo & x & Hd & Hx).
    fold h aw nw in Hx.
    exists x. split; [exact Hd|]. split; [reflexivity|]. split; [eapply HG; [reflexivity| exact Hvo| exact HGs]|].
    (* [comment removed for export] *)
    pose proof (fun b0 l0 H => went_In_bounds _ _ _ b0 l0 HK H) as WB.
    assert (Dgm : forall b0 l0, (In (b0, l0) (ld_groups L) \/ exists k, In (b0, l0, k) (ld_metas L)) ->
                   b0 + mmap_len l0 <= a \/ a + 2 * PGSZ <= b0).
    { intros b0 l0 [H|[k H]]; rewrite Ha; [apply (Dg _ _ H)| apply (Dm _ _ _ H)]. }
    assert (KLnew : forall maps' noacc',
              vmwf maps' ->
              (forall e, In e (vm_maps h) -> (ehi e <= a \/ a + PGSZ <= elo e) -> In e maps') ->
              (forall e x y, In e (vm_noaccess h) -> elo e <= x -> x < y -> y <= ehi e -> y <= 2^64 -> (y <= a \/ a + PGSZ <= x) ->
                  exists e', In e' noacc' /\ elo e' <= x /\ y <= ehi e') ->
              (exists e', In e' maps' /\ elo e' <= a /\ a + 2 * PGSZ <= ehi e') ->
              (forall e, In e maps' -> In e (vm_maps h)) ->
              (forall e', In e' noacc' -> (exists e, In e (vm_noaccess h) /\ elo e <= elo e' /\ ehi e' <= ehi e) \/ (elo e' = a /\ ehi e' = a + PGSZ)) ->
              m_vmmaps mo' = mkVmMapsFull (vm_reserved h) maps' noacc' (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) ->
              KL L' (ps_brk s0) mo').
    { intros maps' noacc' Hwf' Hkeep Hna Hcov' Hsub Hna' Evm. subst L'.
      kl_open HK. constructor; try exact Hmi'; try exact Hh'; rewrite ?Evm; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk set_brkph set_brkreg ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; auto.
      - intros r Hr. destruct (Kresv r Hr) as (e & C1 & C2 & [He|(He & [PC1 PC2] & C3)]).
        + exists e. split; [exact C1|]. split; [exact C2|]. left; exact He.
        + pose proof (PC2 cur Hph) as D. rewrite <- Ha in D.
          exists e. split; [exact C1|]. split; [exact C2|]. right. split; [| split; [| exact C3]].
          * apply Hkeep; [exact He|]. unfold PGSZ in *. lia.
          * split; [| cbn; intros; discriminate]. cbn. intros b1 l1 E'. injection E' as <- <-. exact D.
      - intros b0 l0 Hin. pose proof (WB b0 l0 (or_introl Hin)) as (B1 & B2 & B3 & B4 & B5 & B6). pose proof (Dgm b0 l0 (or_introl Hin)) as D.
        specialize (Kgr b0 l0 Hin). destruct Kgr as ([G0 G1] & G2 & G3 & G4 & G5 & G6). splits; try assumption.
        + apply Hkeep; [exact B4|]. rewrite B5, B6. clear -D. unfold PGSZ in *. lia.
        + unfold brk_disj; cbn. intros b1 l1 E. injection E as <- <-. clear -D. unfold PGSZ in *. lia.
      - intros b0 l0 k Hin. pose proof (WB b0 l0 (or_intror (ex_intro _ k Hin))) as (B1 & B2 & B3 & B4 & B5 & B6). pose proof (Dgm b0 l0 (or_intror (ex_intro _ k Hin))) as D.
        specialize (Kme b0 l0 k Hin). destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). splits; try assumption.
        + apply Hkeep; [exact B4|]. rewrite B5, B6. clear -D. unfold PGSZ in *. lia.
        + unfold brk_disj; cbn. intros b1 l1 E. injection E as <- <-. clear -D. unfold PGSZ in *. lia.
        + intros q Hq1 Hq2. destruct (G9 q Hq1 Hq2) as (e & He & Hel & Heh).
          apply (Hna e (b0 + q * PGSZ) (b0 + q * PGSZ + PGSZ) He Hel ltac:(unfold PGSZ; lia) Heh ltac:(clear -Hq1 Hq2 G4 Hcl; unfold PGSZ in *; nia)). clear -D Hq1 Hq2 G5. unfold PGSZ in *. nia.
      - intros b1 l1 E. injection E as <- <-. splits.
        + lia.
        + rewrite Ha, Ecur. exact S2.
        + lia.
        + reflexivity.
        + lia.
        + intros z Hz. destruct Hcov' as (e' & He' & H1 & H2). exists e'. split; [exact He'|]. lia.
      - exists a, (2 * PGSZ). splits; [reflexivity| lia| lia].
      - (* [comment removed for export] *) intros b1 l1 E. injection E as <- <-. rewrite Ha, Ecur. reflexivity.
      - (* [comment removed for export] *) subst h. unfold PGSZ in *; lia.
      - (* [comment removed for export] *) intros e' He'. destruct (Hna' e' He') as [(e & He & H1 & H2)|[H1 H2]].
        + destruct (Knoacc e He) as [(b0 & l0 & k & Hm & Hb1 & Hb2)|(b0 & l0 & E & _)]; [| rewrite Ereg in E; discriminate].
          left. exists b0, l0, k. split; [exact Hm|]. lia.
        + right. exists a, (2 * PGSZ). split; [reflexivity|]. lia. }
    destruct x as [e| |e]; [destruct Hx| | destruct Hx].
    split; [|exact I].
    apply (KLnew (vm_maps h) ((aw, nw) :: maps_subtract (vm_noaccess h) a (a + PGSZ))); auto.
    + exact (kl_wf _ _ _ HK).
    + intros e x y He H1 H2 H3 Hy H4.
      destruct (iv_subtract_contains (fst e) (snd e) a (a + PGSZ) x y ltac:(lia) ltac:(unfold PGSZ; lia) H1 H2 H3 Hy H4) as (e' & He' & Hr).
      exists e'. split; [right; eapply maps_subtract_In_intro; eauto| exact Hr].
    + exists e0. split; [exact He0|]. unfold PGSZ in *; lia.
    + intros e' [<-|He'].
      * right. rewrite elo_pair, ehi_pair, Ua, Un. split; reflexivity.
      * left. exact (kl_noacc_piece _ _ _ a (a + PGSZ) e' HK ltac:(unfold PGSZ; lia) He'). }
  intros x. cbn beta. apply mspec_ret. intros s mo (-> & HGs & HK & Hx). unfold ev_step_post.
  cbn [answer_ok event_post]. change (Z.land MAPFX MAP_FIXED =? 0) with false. cbv iota. fold L'.
  splits; auto. unfold mmap_fixed_answer_ok. destruct x as [e| |e]; try subst e.
  - rewrite is_errno_form_neg by (unfold ENOMEM; lia). reflexivity.
  - rewrite Z.eqb_refl. apply orb_true_r.
  - rewrite is_errno_form_neg by (unfold ENOMEM; lia). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma g_remove_split : forall a l0 (l : list (Z * Z)) (M : list Z), In (a, l0) l -> List.NoDup (map fst l ++ M) ->
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

#[using="Type"] Lemma phase_quiet : forall L L' pbrk mo mo',
  KL L pbrk mo -> brk_quiet L -> ld_brk L' = ld_brk L -> ld_brkreg L' = ld_brkreg L ->
  vm_start_brk (m_vmmaps mo') = vm_start_brk (m_vmmaps mo) -> vm_brk (m_vmmaps mo') = vm_brk (m_vmmaps mo) ->
  phase_inv (ld_brk L') L' pbrk mo'.
Proof.
  intros L L' pbrk mo mo' HK Hq E1 E2 E3 E4. pose proof (kl_phase _ _ _ HK) as Kph. unfold brk_quiet in Hq. unfold phase_inv.
  rewrite E1, E2, E3, E4. destruct (ld_brk L); try contradiction; auto.
Qed.

#[using="Type"] Lemma ev_munmap_ok : forall L G s0 a l0 len, frame_ok G -> brk_quiet L -> In (a, l0) (ld_groups L) ->
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
    assert (Hhas : map_has (vm_maps h) aw nw = true).
    { unfold map_has. apply existsb_exists. exists (went a n). split; [exact A5|]. unfold went, wz. fold aw nw. cbn [fst snd]. rewrite !bv_eqb_refl. reflexivity. }
    split.
    { apply (nsafe_munmap_exact a len mo); [lia| lia| rewrite page_size_eq; unfold PGSZ in A3; exact A3| |].
      - fold (mmap_len len). rewrite Hlen2. ceil_bounds. unfold TASK_SIZE. lia.
      - fold (mmap_len len). rewrite Hlen2. exact Hhas. }
    intros rsp mo' evs Hst.
    pose proof (minv_pres' _ _ _ _ _ Hst ltac:(exact I || reflexivity) (kl_minv _ _ _ HK) (kl_halt _ _ _ HK)) as [Hh' Hmi'].
    pose proof (nstep_dec_munmap a len mo rsp mo' evs ltac:(lia) ltac:(lia) ltac:(rewrite page_size_eq; unfold PGSZ in A3; exact A3) ltac:(rewrite Hlen2; ceil_bounds; unfold TASK_SIZE; lia) ltac:(rewrite Hlen2; exact Hhas) Hst) as (_ & Hvo & Hd & Evm).
    rewrite Hlen2 in Evm. fold h aw nw in Evm. rewrite Ua, Un in Evm.
    exists (RgDone true). split; [exact Hd|]. split; [reflexivity|]. split; [eapply HG; [reflexivity| exact Hvo| exact HGs]|].
    split; [|exact I].
    (* [comment removed for export] *)
    pose proof (kl_distinct _ _ _ HK) as Kd.
    destruct (g_remove_split a l0 (ld_groups L) _ Hin Kd) as (g1 & g2 & Eg & Ezz).
    rewrite Eg, map_app in Kd. cbn [map fst] in Kd. rewrite <- app_assoc in Kd. cbn [app] in Kd.
    pose proof (List.NoDup_remove_1 _ _ _ Kd) as Kd1. pose proof (List.NoDup_remove_2 _ _ _ Kd) as Kd2.
    assert (Hg' : forall b l, In (b, l) (g_remove a (ld_groups L)) -> In (b, l) (ld_groups L) /\ b <> a).
    { intros b l H. rewrite Ezz in H. rewrite Eg. split; [apply in_app_or in H as [H|H]; apply in_or_app; [left; exact H| right; right; exact H]|].
      intros ->. apply Kd2. rewrite app_assoc, <- map_app. apply in_or_app. left. apply in_map_iff. exists (a, l). split; [reflexivity| exact H]. }
    assert (Hm' : forall b l k, In (b, l, k) (ld_metas L) -> b <> a).
    { intros b l k H ->. apply Kd2. apply in_or_app. right. apply in_or_app. right. apply in_map_iff. exists (a, l, k). split; [reflexivity| exact H]. }
    (* [comment removed for export] *)
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
              (forall e, In e maps' -> In e (vm_maps h)) ->
              (forall e', In e' noacc' -> exists e, In e (vm_noaccess h) /\ elo e <= elo e' /\ ehi e' <= ehi e) ->
              m_vmmaps mo' = mkVmMapsFull (vm_reserved h) maps' noacc' (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) ->
              KL L' (ps_brk s0) mo').
    { intros maps' noacc' Hwf' Hkeep Hna Hsub Hna' Evm'.
      assert (Hph' : phase_inv (ld_brk L') L' (ps_brk s0) mo') by (eapply phase_quiet; [exact HK| exact Hq| reflexivity| reflexivity| rewrite Evm'; reflexivity| rewrite Evm'; reflexivity]).
      assert (Kfst : forall b l, b <> a -> 0 < b < 2^64 -> fst (went b (mmap_len l)) <> aw).
      { intros b l Hne Hb E. apply Hne. apply (f_equal bv_unsigned) in E. cbn [fst went] in E. rewrite unsigned_wz, Ua in E by lia. exact E. }
      assert (Hn0 : 0 < n) by (pose proof (mmap_len_ge l0 ltac:(lia)) as Hge; fold n in Hge; lia).
      subst L'. kl_open HK. constructor; try exact Hph'; try exact Hmi'; try exact Hh'; rewrite ?Evm'; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk set_groups ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; auto.
      - intros r Hr. destruct (Kresv r Hr) as (e & C1 & C2 & [He|(He & Hfl & C3)]).
        + exists e. split; [exact C1|]. split; [exact C2|]. left; exact He.
        + exists e. split; [exact C1|]. split; [exact C2|]. right. split; [| split; [exact Hfl|]].
          * apply Hkeep; [exact He|]. intros E. pose proof (C3 a l0 (or_introl Hin)) as D. pose proof (proj1 Kwf e He) as W.
            unfold elo, ehi in D, W. rewrite E, Ua in D, W. lia.
          * intros b0 l1 [Hb|[k Hb]]; [destruct (Hg' b0 l1 Hb) as [Hb1 _]; apply C3; left; exact Hb1| apply C3; right; exists k; exact Hb].
      - intros b0 l1 Hin0. destruct (Hg' b0 l1 Hin0) as [Hin1 Hne]. specialize (Kgr b0 l1 Hin1). destruct Kgr as ([G0 G1] & G2 & G3 & G4 & G5 & G6). splits; try assumption.
        apply Hkeep; [exact G5|]. apply Kfst; auto. pose proof (mmap_len_ge l1 G0). lia.
      - intros b0 l1 k Hin0. pose proof (Hm' b0 l1 k Hin0) as Hne. specialize (Kme b0 l1 k Hin0). destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). splits; try assumption.
        + apply Hkeep; [exact G7|]. apply Kfst; auto. pose proof (mmap_len_ge l1 G0). lia.
        + intros q Hq1 Hq2. destruct (G9 q Hq1 Hq2) as (e & He & Hel & Heh).
          pose proof (Dother b0 l1 (or_intror (ex_intro _ k Hin0)) Hne) as D.
          apply (Hna e (b0 + q * PGSZ) (b0 + q * PGSZ + PGSZ) He Hel ltac:(unfold PGSZ; lia) Heh ltac:(clear -Hq1 Hq2 G4 Hcl; unfold PGSZ in *; nia)). clear -D Hq1 Hq2 G5. unfold PGSZ in *. nia.
      - rewrite Ezz, map_app, <- app_assoc. exact Kd1.
      - intros b0 l1 E. specialize (Kreg b0 l1 E). destruct Kreg as (R1 & R2 & R3 & R4 & R5 & Rcov). splits; auto.
        intros z Hz. destruct (Rcov z Hz) as (e & He & Hr). exists e. split; [|exact Hr]. apply Hkeep; [exact He|].
        intros Efst. unfold brk_disj in A6. specialize (A6 b0 l1 E).
        destruct (pwdisj_In _ _ _ (proj2 Kwf) He A5) as [->|D].
        + rewrite B5, B6 in Hr. clear -Hr A6 Hz R3. unfold PGSZ in *. lia.
        + pose proof (proj1 Kwf e He) as W. unfold edisj, elo, ehi in D, W. rewrite Efst in D, W. cbn [fst snd went] in D. unfold wz in D. fold aw nw in D. rewrite Un in D. clear - a l0 n mo b0 l1 B2 aw e D W. lia.
      - (* [comment removed for export] *) intros b0 l1 [Hb|[k Hb]] e He; [destruct (Hg' b0 l1 Hb) as [Hb1 _]; apply (Kgrv b0 l1 (or_introl Hb1)); exact He| apply (Kgrv b0 l1 (or_intror (ex_intro _ k Hb))); exact He].
      - (* [comment removed for export] *) intros e' He'. destruct (Hna' e' He') as (e & He & H1 & H2).
        destruct (Knoacc e He) as [(b0 & l1 & k & Hm & Hb1 & Hb2)|(b0 & l1 & E & Hb1 & Hb2)]; [left; exists b0, l1, k; split; [exact Hm| lia]| right; exists b0, l1; split; [exact E| lia]].
 }
    apply (KLnew (map_remove (vm_maps h) aw) (maps_subtract (vm_noaccess h) a (a + n))).
    + apply vmwf_remove. exact (kl_wf _ _ _ HK).
    + intros e He Hne. unfold map_remove. apply filter_In. split; [exact He|]. destruct (bv_eqb (fst e) aw) eqn:E; [|reflexivity]. apply bv_eqb_eq in E. contradiction.
    + intros e x y He H1 H2 H3 Hy H4. destruct (iv_subtract_contains (fst e) (snd e) a (a + n) x y ltac:(lia) ltac:(lia) H1 H2 H3 Hy H4) as (e' & He' & Hr).
      exists e'. split; [eapply maps_subtract_In_intro; eauto| exact Hr].
    + intros e He. unfold map_remove in He. apply filter_In in He as [He _]. exact He.
    + intros e' He'. exact (kl_noacc_piece _ _ _ a (a + n) e' HK ltac:(lia) He').
    + exact Evm. }
  intros x. cbn beta. apply mspec_ret. intros s mo (-> & HGs & HK & Hx). unfold ev_step_post.
  cbn [answer_ok event_post]. fold L'.
  splits; auto. unfold munmap_answer_ok. destruct x as [e|b]; try subst e.
  - rewrite is_errno_form_neg by (unfold EINVAL; lia). apply orb_true_r.
  - reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma nodup_map_inj : forall {A B} (f : A -> B) l x y, List.NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof.
  induction l as [|z l IH]; intros x y Hnd Hx Hy E; [destruct Hx|]. cbn in Hnd. inversion Hnd; subst.
  destruct Hx as [<-|Hx], Hy as [<-|Hy]; [reflexivity| | | apply IH; auto].
  - exfalso. apply H1. rewrite E. apply in_map. exact Hy.
  - exfalso. apply H1. rewrite <- E. apply in_map. exact Hx.
Qed.

#[using="Type"] Lemma map_base_bump : forall a ms, map (fun m : Z * Z * Z => fst (fst m)) (map (bump_meta a) ms) = map (fun m => fst (fst m)) ms.
Proof.
  intros a ms. rewrite map_map. apply map_ext. intros [[b l] k]. unfold bump_meta. destruct (_ =? _); reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma map_contains_not_free : forall maps a n, (0 < bv_unsigned n)%Z ->
  map_contains maps a n = true -> region_free maps a n = true -> False.
Proof.
  intros maps a n Hn Hc Hf. unfold map_contains in Hc. apply existsb_exists in Hc as ([e sz] & Hin & Hb).
  cbn [fst snd] in Hb. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (region_free_In _ _ _ _ _ Hf Hin). lia.
Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma ev_mprotect_ok : forall L G s0 b l k, frame_ok G -> brk_quiet L -> In (b, l, k) (ld_metas L) ->
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
    assert (Hamod : a mod 4096 = 0). { subst a. unfold PGSZ in *. rewrite Z.add_mod, A3, Z.mod_mul by lia. reflexivity. }
    assert (Hcn : map_contains (vm_noaccess h) aw nw = true).
    { destruct (Ana (1 + k) ltac:(lia) ltac:(lia)) as (e & He & Hel & Heh). unfold map_contains. apply existsb_exists. exists e. split; [exact He|].
      rewrite Ua, Un. unfold elo, ehi in Hel, Heh. subst a. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
    assert (Hcm : map_contains (vm_maps h) aw nw = true).
    { unfold map_contains. apply existsb_exists. exists (went b nb). split; [exact A5|]. rewrite Ua, Un. unfold elo, ehi in B5, B6. rewrite B5.
      replace (bv_unsigned (fst (went b nb)) + bv_unsigned (snd (went b nb))) with (b + nb) by (symmetry; exact B6).
      rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
    split.
    { apply (nsafe_mprotect_expose a PGSZ mo); [unfold PGSZ in *; lia| unfold PGSZ; lia| rewrite page_size_eq; exact Hamod| | |].
      - change (page_round_up_Z PGSZ) with PGSZ. unfold PGSZ in *; lia.
      - change (page_round_up_Z PGSZ) with PGSZ. exact Hcn.
      - change (page_round_up_Z PGSZ) with PGSZ. exact Hcm. }
    intros rsp mo' evs Hst.
    pose proof (minv_pres' _ _ _ _ _ Hst ltac:(exact I || reflexivity) (kl_minv _ _ _ HK) (kl_halt _ _ _ HK)) as [Hh' Hmi'].
    pose proof (nstep_dec_mprotect a PGSZ mo rsp mo' evs ltac:(unfold PGSZ in *; lia) ltac:(unfold PGSZ; lia) ltac:(rewrite page_size_eq; exact Hamod)
                  ltac:(change (mmap_len PGSZ) with PGSZ; unfold PGSZ in *; lia)
                  ltac:(change (mmap_len PGSZ) with PGSZ; exact Hcn) ltac:(change (mmap_len PGSZ) with PGSZ; exact Hcm) Hst) as (_ & Hvo & x & Hd & Hx).
    change (mmap_len PGSZ) with PGSZ in Hx. fold h aw nw in Hx.
    assert (HdRW : dec_mprotect_rw a PGSZ rsp = Some x /\ match x with RgDone false => False | _ => True end).
    { destruct x as [e|[|]].
      - destruct Hx as [He _]. unfold dec_mprotect_rw. rewrite Hd.
        replace (e =? ENOSYS) with false by (symmetry; apply Z.eqb_neq; subst e; unfold ENOMEM, ENOSYS; lia). split; [reflexivity| exact I].
      - unfold dec_mprotect_rw. rewrite Hd. split; [reflexivity| exact I].
      - destruct Hx. }
    destruct HdRW as [HdRW Hnf].
    exists x. split; [exact HdRW|]. split; [reflexivity|]. split; [eapply HG; [reflexivity| exact Hvo| exact HGs]|].
    pose proof (kl_distinct _ _ _ HK) as Kd. pose proof (List.NoDup_app_remove_l _ _ Kd) as Kdm.
    (* [comment removed for export] *)
    assert (Dother : forall b0 l0, (In (b0, l0) (ld_groups L) \/ exists k0, In (b0, l0, k0) (ld_metas L)) -> b0 <> b ->
                     b0 + mmap_len l0 <= b \/ b + nb <= b0).
    { intros b0 l0 H Hne. pose proof (went_In_bounds _ _ _ b0 l0 HK H) as (C1 & C2 & C3 & C4 & C5 & C6).
      destruct (pwdisj_In _ _ _ (proj2 (kl_wf _ _ _ HK)) C4 A5) as [E|D].
      - exfalso. apply Hne. apply (f_equal elo) in E. rewrite C5, B5 in E. exact E.
      - unfold edisj in D. rewrite C5, C6, B5, B6 in D. lia. }
    assert (KLnew : forall noacc',
              (forall e x y, In e (vm_noaccess h) -> elo e <= x -> x < y -> y <= ehi e -> y <= 2^64 -> (y <= a \/ a + PGSZ <= x) ->
                  exists e', In e' noacc' /\ elo e' <= x /\ y <= ehi e') ->
              (forall e', In e' noacc' -> exists e, In e (vm_noaccess h) /\ elo e <= elo e' /\ ehi e' <= ehi e) ->
              m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (vm_maps h) noacc' (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) ->
              KL L' (ps_brk s0) mo').
    { intros noacc' Hna Hna' Evm.
      assert (Hph' : phase_inv (ld_brk L') L' (ps_brk s0) mo') by (eapply phase_quiet; [exact HK| exact Hq| reflexivity| reflexivity| rewrite Evm; reflexivity| rewrite Evm; reflexivity]).
      subst L'. kl_open HK. constructor; try exact Hph'; try exact Hmi'; try exact Hh'; rewrite ?Evm; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk set_metas ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; auto.
      - intros r Hr. destruct (Kresv r Hr) as (e & C1 & C2 & [He|(He & Hfl & C3)]).
        + exists e. split; [exact C1|]. split; [exact C2|]. left; exact He.
        + exists e. split; [exact C1|]. split; [exact C2|]. right. split; [exact He|]. split; [exact Hfl|].
          intros b0 l0 [Hb|[k0' Hb]]; [apply C3; left; exact Hb|].
          apply in_map_iff in Hb as ([[b1 l1] k0] & Eb & Hin1). unfold bump_meta in Eb.
          destruct (Z.eqb_spec (b1 + (1 + k0) * PGSZ) a); injection Eb as -> -> _; apply C3; right; exists k0; exact Hin1.
      - intros b0 l0 k0' Hin0. apply in_map_iff in Hin0 as ([[b1 l1] k0] & Eb & Hin1).
        specialize (Kme b1 l1 k0 Hin1). destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
        unfold bump_meta in Eb. destruct (Z.eqb_spec (b1 + (1 + k0) * PGSZ) a) as [Ea|Na]; injection Eb as -> -> <-.
        + (* [comment removed for export] *)
          assert (Eb0 : b0 = b).
          { destruct (Z.eq_dec b0 b) as [E|Hne]; [exact E|]. exfalso.
            pose proof (Dother b0 l0 (or_intror (ex_intro _ k0 Hin1)) Hne) as D. pose proof (mmap_len_ge l0 G0). clear -D Ea Hab G5 G6 H. unfold PGSZ in *. nia. }
          subst b0. pose proof (nodup_map_inj _ _ _ _ Kdm Hin1 Hin (eq_refl b)) as E. injection E as -> ->.
          splits; try assumption; try lia.
          intros q Hq1 Hq2. destruct (G9 q ltac:(lia) Hq2) as (e & He & Hel & Heh).
          apply (Hna e (b + q * PGSZ) (b + q * PGSZ + PGSZ) He Hel ltac:(unfold PGSZ; lia) Heh ltac:(clear -Hq1 Hq2 G4 Hcl; unfold PGSZ in *; nia)). right. subst a. clear -Hq1. unfold PGSZ in *. nia.
        + splits; try assumption.
          intros q Hq1 Hq2. destruct (G9 q Hq1 Hq2) as (e & He & Hel & Heh).
          apply (Hna e (b0 + q * PGSZ) (b0 + q * PGSZ + PGSZ) He Hel ltac:(unfold PGSZ; lia) Heh ltac:(clear -Hq1 Hq2 G4 Hcl; unfold PGSZ in *; nia)).
          destruct (Z.eq_dec b0 b) as [->|Hne].
          { pose proof (nodup_map_inj _ _ _ _ Kdm Hin1 Hin (eq_refl b)) as E. injection E as -> ->. exfalso. apply Na. reflexivity. }
          pose proof (Dother b0 l0 (or_intror (ex_intro _ k0 Hin1)) Hne) as D. clear -D Hab Hq1 Hq2 G5. unfold PGSZ in *. nia.
      - rewrite map_base_bump. exact Kd.
      - (* [comment removed for export] *) intros b0 l0 [Hb|[k0' Hb]] e He; [apply (Kgrv b0 l0 (or_introl Hb)); exact He|].
        apply in_map_iff in Hb as ([[b1 l1] k0] & Eb & Hin1). unfold bump_meta in Eb.
        destruct (Z.eqb_spec (b1 + (1 + k0) * PGSZ) a); injection Eb as -> -> _; apply (Kgrv b0 l0 (or_intror (ex_intro _ k0 Hin1))); exact He.
      - (* [comment removed for export] *) intros e' He'. destruct (Hna' e' He') as (e & He & H1 & H2).
        destruct (Knoacc e He) as [(b0 & l1 & k0 & Hm & Hb1 & Hb2)|(b0 & l1 & E & Hb1 & Hb2)]; [| right; exists b0, l1; split; [exact E| lia]].
        left. assert (Hm' : exists k', In (b0, l1, k') (map (bump_meta a) (ld_metas L))).
        { exists (if b0 + (1 + k0) * PGSZ =? a then k0 + 1 else k0). apply in_map_iff. exists (b0, l1, k0). split; [| exact Hm].
          unfold bump_meta. destruct (b0 + (1 + k0) * PGSZ =? a); reflexivity. }
        destruct Hm' as [k' Hm']. exists b0, l1, k'. split; [exact Hm'| lia]. }
    destruct x as [e|[|]].
    - destruct Hx as [He ->]. split; [right; exact He| exact HK].
    - destruct Hx as (_ & Evm). apply (KLnew (maps_subtract (vm_noaccess h) a (a + PGSZ))).
      + intros e x y He H1 H2 H3 Hy H4. destruct (iv_subtract_contains (fst e) (snd e) a (a + PGSZ) x y ltac:(lia) ltac:(unfold PGSZ; lia) H1 H2 H3 Hy H4) as (e' & He' & Hr).
        exists e'. split; [eapply maps_subtract_In_intro; eauto| exact Hr].
      + intros e' He'. exact (kl_noacc_piece _ _ _ a (a + PGSZ) e' HK ltac:(unfold PGSZ in *; lia) He').
      + rewrite Evm. unfold mprotect_model_next. rewrite m_vmmaps_with_vmmaps. fold h aw nw. rewrite Ua, Un. reflexivity.
    - destruct Hnf. }
  intros x. cbn beta. apply mspec_ret. intros s mo (-> & HGs & Hx). unfold ev_step_post.
  cbn [answer_ok event_post]. fold L'. unfold mprotect_answer_ok.
  destruct x as [e|bb].
  - destruct Hx as [He HK]. rewrite is_errno_form_neg by (destruct He as [-> | ->]; unfold EINVAL, ENOMEM; lia).
    replace (neg_errno e =? 0) with false by (symmetry; apply Z.eqb_neq; unfold neg_errno; destruct He as [-> | ->]; unfold EINVAL, ENOMEM; lia).
    replace (neg_errno e =? TWO64 - ENOSYS) with false by (symmetry; apply Z.eqb_neq; unfold neg_errno, TWO64, ENOSYS; destruct He as [-> | ->]; unfold EINVAL, ENOMEM; lia).
    cbn [orb]. splits; auto.
  - cbn [Z.eqb orb]. splits; auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma page_round_up_Z_aligned : forall z, 0 <= z -> z mod 4096 = 0 -> page_round_up_Z z = z.
Proof.
  intros z Hz Hal. unfold page_round_up_Z. rewrite page_size_eq.
  pose proof (Z_div_mod_eq_full z 4096). pose proof (Z_div_mod_eq_full (z + 4096 - 1) 4096). pose proof (Z.mod_pos_bound (z + 4096 - 1) 4096). nia.
Qed.

#[using="Type"] Lemma region_free_of_disj : forall maps aw nw,
  (forall e, In e maps -> bv_unsigned aw + bv_unsigned nw <= elo e \/ ehi e <= bv_unsigned aw) -> region_free maps aw nw = true.
Proof.
  induction maps as [|[e sz] maps IH]; intros aw nw H; [reflexivity|]. cbn [region_free].
  rewrite IH by (intros e' He'; apply H; right; exact He'). unfold iv_overlap.
  specialize (H (e, sz) (or_introl eq_refl)). unfold elo, ehi in H; cbn in H.
  destruct H as [H|H].
  - replace (bv_unsigned e <? bv_unsigned aw + bv_unsigned nw) with false by (symmetry; apply Z.ltb_ge; lia). rewrite andb_false_r. reflexivity.
  - replace (bv_unsigned aw <? bv_unsigned e + bv_unsigned sz) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

#[using="Type"] Lemma map_remove_In : forall maps (a : word) e, In e (map_remove maps a) <-> In e maps /\ fst e <> a.
Proof.
  intros maps a e. unfold map_remove. rewrite filter_In. destruct (bv_eqb (fst e) a) eqn:E; cbn.
  - apply bv_eqb_eq in E. split; [intros [_ H]; discriminate| intros [_ H]; contradiction].
  - split; [intros [H _]; split; [exact H|]; intros E'; rewrite E', bv_eqb_refl in E; discriminate| intros [H _]; auto].
Qed.

#[using="Type"] Lemma nodup_app_disj {A} (l1 l2 : list A) x : List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
  intros ND H1 H2. apply in_split in H1 as (la & lb & ->). rewrite <- app_assoc in ND. cbn in ND.
  apply List.NoDup_remove_2 in ND. apply ND. apply in_or_app. right. apply in_or_app. right. exact H2.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma kl_mremap_src : forall L pbrk mo a l0, KL L pbrk mo -> In (a, l0) (ld_groups L) ->
  let h := m_vmmaps mo in let aw := Z_to_bv 64 a in let nw := Z_to_bv 64 (mmap_len l0) in
  region_free (vm_reserved h) aw nw = true /\ map_has (vm_maps h) aw nw = true /\ region_free (vm_noaccess h) aw nw = true
  /\ (forall b l k, In (b, l, k) (ld_metas L) -> b <> a)
  /\ (forall b l, (In (b, l) (ld_groups L) \/ exists k, In (b, l, k) (ld_metas L)) -> b <> a -> b + mmap_len l <= a \/ a + mmap_len l0 <= b).
Proof.
  intros L pbrk mo a l0 HK Hin h aw nw. pose proof alloc_ceiling_lt as Hcl.
  pose proof (kl_groups _ _ _ HK a l0 Hin) as (A1 & A2 & A3 & A4 & A5 & A6).
  pose proof (went_In_bounds _ _ _ a l0 HK (or_introl Hin)) as (_ & B2 & _ & _ & B5 & B6).
  set (n := mmap_len l0) in *.
  assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; lia).
  assert (Un : bv_unsigned nw = n) by (subst nw; apply unsigned_lit; lia).
  assert (Ewent : went a n = (aw, nw)) by reflexivity.
  pose proof (kl_distinct _ _ _ HK) as Kd.
  assert (Hm' : forall b l k, In (b, l, k) (ld_metas L) -> b <> a).
  { intros b l k H ->. apply (nodup_app_disj _ _ a Kd); [apply in_map_iff; exists (a, l0); auto| apply in_map_iff; exists (a, l, k); auto]. }
  assert (Dother : forall b l, (In (b, l) (ld_groups L) \/ exists k, In (b, l, k) (ld_metas L)) -> b <> a ->
                   b + mmap_len l <= a \/ a + n <= b).
  { intros b l H Hneq. pose proof (went_In_bounds _ _ _ b l HK H) as (C1 & C2 & C3 & C4 & C5 & C6).
    destruct (pwdisj_In _ _ _ (proj2 (kl_wf _ _ _ HK)) C4 A5) as [E|D].
    - exfalso. apply Hneq. apply (f_equal elo) in E. rewrite C5, B5 in E. exact E.
    - unfold edisj in D. rewrite C5, C6, B5, B6 in D. lia. }
  splits.
  - apply region_free_of_disj. intros e He. rewrite Ua, Un. exact (kl_grp_resv _ _ _ HK a l0 (or_introl Hin) e He).
  - unfold map_has. apply existsb_exists. exists (went a n). split; [exact A5|]. rewrite Ewent. cbn [fst snd]. rewrite !bv_eqb_refl. reflexivity.
  - apply region_free_of_disj. intros e He. rewrite Ua, Un.
    destruct (kl_noacc _ _ _ HK e He) as [(b & l & k & Hm & Hb1 & Hb2)|(b0 & l1 & E & Hb1 & Hb2)].
    + pose proof (Dother b l (or_intror (ex_intro _ k Hm)) (Hm' b l k Hm)). lia.
    + pose proof (A6 b0 l1 E). pose proof (kl_brkreg _ _ _ HK b0 l1 E) as (_ & _ & R3 & _). unfold PGSZ in *. lia.
  - exact Hm'.
  - exact Dother.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma nstep_mremap_cases : forall L pbrk mo a l0 newlen rsp mo' evs,
  KL L pbrk mo -> In (a, l0) (ld_groups L) -> 0 < newlen < LEN_MAX -> newlen mod PGSZ = 0 -> mmap_len l0 <> newlen ->
  nstep (NMremap a (mmap_len l0) newlen) mo rsp mo' evs ->
  let n := mmap_len l0 in let h := m_vmmaps mo in let aw := Z_to_bv 64 a in
  evs = [] /\ vm_only mo mo' /\ minv mo' /\ m_halted mo' = None /\
  exists x, dec_mremap a n newlen [] [] rsp = Some x /\
   let z := mremap_val a x in
   ( (z = neg_errno ENOMEM /\ mo' = mo)
   \/ (is_err z = false /\ is_errno_form z = false /\ 0 < z /\ z mod PGSZ = 0 /\ z + newlen <= alloc_ceiling
       /\ m_vmmaps mo' = mkVmMapsFull (vm_reserved h) ((Z_to_bv 64 z, Z_to_bv 64 newlen) :: map_remove (vm_maps h) aw)
                          (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
       /\ (forall e, In e (vm_reserved h) -> z + newlen <= elo e \/ ehi e <= z)
       /\ (forall e, In e (map_remove (vm_maps h) aw) -> z + newlen <= elo e \/ ehi e <= z)
       /\ (z = a \/ (z <> a /\ n < newlen /\ forall e, In e (vm_maps h) -> z + newlen <= elo e \/ ehi e <= z)))).
Proof.
  intros L pbrk mo a l0 newlen rsp mo' evs HK Hin Hnl Hnlal Hne Hst n h aw. pose proof alloc_ceiling_lt as Hcl.
  pose proof (kl_groups _ _ _ HK a l0 Hin) as (A1 & A2 & A3 & A4 & A5 & A6).
  pose proof (went_In_bounds _ _ _ a l0 HK (or_introl Hin)) as (_ & B2 & _ & _ & B5 & B6). fold n in A4, A5, A6, B2, B5, B6.
  destruct (kl_mremap_src L pbrk mo a l0 HK Hin) as (Hrfr & Hhas & Hrfn & Hm' & Dother). fold n h aw in Hrfr, Hhas, Hrfn, Dother.
  assert (Hnal : n mod 4096 = 0) by (subst n; apply mmap_len_aligned).
  assert (En : mmap_len n = n) by (apply mmap_len_of_aligned; [lia| exact Hnal]).
  assert (Enn : mmap_len newlen = newlen) by (apply mmap_len_of_aligned; [lia| unfold PGSZ in Hnlal; exact Hnlal]).
  set (nw := Z_to_bv 64 n) in *.
  assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; lia).
  assert (Un : bv_unsigned nw = n) by (subst nw; apply unsigned_lit; lia).
  assert (Ewent : went a n = (aw, nw)) by reflexivity.
  pose proof (minv_pres' _ _ _ _ _ Hst I (kl_minv _ _ _ HK) (kl_halt _ _ _ HK)) as [Hh' Hmi'].
  pose proof (nstep_dec_mremap a n newlen [] [] mo rsp mo' evs) as ND. cbv zeta in ND. rewrite !En, !Enn in ND. fold h aw nw in ND.
  specialize (ND ltac:(lia) ltac:(rewrite page_size_eq; unfold PGSZ in A3; exact A3) ltac:(lia) ltac:(lia)
                 ltac:(exact A4) ltac:(unfold LEN_MAX in Hnl; lia) (kl_top _ _ _ HK)
                 ltac:(apply minv_nolazy; exact (kl_minv _ _ _ HK)) Hrfr Hhas Hrfn ltac:(constructor) ltac:(constructor) Hst).
  destruct ND as (-> & Hvo & x & Hd & Hx).
  split; [reflexivity|]. split; [exact Hvo|]. split; [exact Hmi'|]. split; [exact Hh'|]. exists x. split; [exact Hd|].
  assert (Hisa : is_errno_form a = false). { unfold is_errno_form, TWO64. apply andb_false_iff. left. apply Z.leb_gt. lia. }
  assert (Hiea : is_err a = false) by (unfold is_err, TWO64; apply Z.ltb_ge; lia).
  (* [comment removed for export] *)
  assert (Dmaps0 : forall e, In e (map_remove (vm_maps h) aw) -> a + n <= elo e \/ ehi e <= a).
  { intros e He. apply map_remove_In in He as [He Hf]. destruct (pwdisj_In _ _ _ (proj2 (kl_wf _ _ _ HK)) He A5) as [E|D]; [exfalso; apply Hf; rewrite E, Ewent; reflexivity|].
    unfold edisj in D. rewrite B5, B6 in D. lia. }
  destruct x as [e| |d]; cbn [mremap_val].
  - (* [comment removed for export] *) destruct Hx as (-> & _ & ->). left. split; reflexivity.
  - (* [comment removed for export] *) right. destruct Hx as [[E _]|[(Hlt & Evm)|(Hlt & Hce' & Hrf2 & Evm)]]; [exfalso; exact (Hne E)| |].
    + (* [comment removed for export] *) rewrite Evm. unfold mremap_maps_next. fold h.
      split; [exact Hiea|]. split; [exact Hisa|]. split; [lia|]. split; [unfold PGSZ in *; exact A3|]. split; [lia|]. split; [reflexivity|].
      split; [intros e He; pose proof (kl_grp_resv _ _ _ HK a l0 (or_introl Hin) e He) as G0; fold n in G0; lia|].
      split; [intros e He; pose proof (Dmaps0 e He); lia|]. left; reflexivity.
    + (* [comment removed for export] *) rewrite Evm. unfold mremap_maps_next. fold h.
      assert (Unn : bv_unsigned (Z_to_bv 64 newlen) = newlen) by (apply unsigned_lit; unfold LEN_MAX in Hnl; lia).
      split; [exact Hiea|]. split; [exact Hisa|]. split; [lia|]. split; [unfold PGSZ in *; exact A3|]. split; [lia|]. split; [reflexivity|].
      split; [intros [e sz] He; pose proof (region_free_In _ _ _ _ _ Hrf2 (in_or_app _ _ _ (or_introl He))) as D; rewrite Ua, Unn in D; unfold elo, ehi; cbn [fst snd]; lia|].
      split; [intros [e sz] He; pose proof (region_free_In _ _ _ _ _ Hrf2 (in_or_app _ _ _ (or_intror He))) as D; rewrite Ua, Unn in D; unfold elo, ehi; cbn [fst snd]; lia|].
      left; reflexivity.
  - (* [comment removed for export] *) right. destruct Hx as (Hlt & Hok & Hda & Hrf2 & Evm). rewrite Evm. unfold mremap_maps_next. fold h.
    apply mmap_addr_ok_true in Hok as [(Hdal & Hd0 & Hce') _]. rewrite page_size_eq in Hdal. rewrite Enn in Hce'.
    assert (Unn : bv_unsigned (Z_to_bv 64 newlen) = newlen) by (apply unsigned_lit; unfold LEN_MAX in Hnl; lia).
    assert (Ud : bv_unsigned (Z_to_bv 64 d) = d) by (apply unsigned_lit; lia).
    assert (Dall : forall e, In e (vm_maps h) -> d + newlen <= elo e \/ ehi e <= d).
    { intros [e sz] He. pose proof (region_free_In _ _ _ _ _ Hrf2 (in_or_app _ _ _ (or_intror He))) as D. rewrite Ud, Unn in D. unfold elo, ehi. cbn [fst snd]. lia. }
    assert (Hisd : is_errno_form d = false). { unfold is_errno_form, TWO64. apply andb_false_iff. left. apply Z.leb_gt. lia. }
    assert (Hied : is_err d = false) by (unfold is_err, TWO64; apply Z.ltb_ge; lia).
    split; [exact Hied|]. split; [exact Hisd|]. split; [lia|]. split; [unfold PGSZ; exact Hdal|]. split; [lia|]. split; [reflexivity|].
    split; [intros [e sz] He; pose proof (region_free_In _ _ _ _ _ Hrf2 (in_or_app _ _ _ (or_introl He))) as D; rewrite Ud, Unn in D; unfold elo, ehi; cbn [fst snd]; lia|].
    split; [intros e He; apply map_remove_In in He as [He _]; exact (Dall e He)|].
    right. split; [exact Hda|]. split; [exact Hlt| exact Dall].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma kl_fresh_noacc : forall L pbrk mo (d nw : word), KL L pbrk mo -> 0 < bv_unsigned nw ->
  region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) d nw = true ->
  region_free (vm_noaccess (m_vmmaps mo)) d nw = true.
Proof.
  intros L pbrk mo d nw HK Hnw Hrf. apply region_free_of_disj. intros e He.
  pose proof (region_free_app_r _ _ _ _ Hrf) as Hm.
  destruct (kl_noacc _ _ _ HK e He) as [(b & l & k & Hin & H1 & H2) | (b0 & l0 & E & H1 & H2)].
  - pose proof (went_In_bounds _ _ _ b l HK (or_intror (ex_intro _ k Hin))) as (_ & _ & _ & C4 & C5 & C6).
    pose proof (region_free_disj _ _ _ _ Hm C4) as D. rewrite C5, C6 in D. lia.
  - pose proof (kl_brkreg _ _ _ HK b0 l0 E) as (R1 & R2 & R3 & R4 & R5 & Rcov).
    destruct (Z_le_gt_dec (bv_unsigned d + bv_unsigned nw) (elo e)) as [|G1]; [left; assumption|].
    destruct (Z_le_gt_dec (ehi e) (bv_unsigned d)) as [|G2]; [right; assumption|]. exfalso.
    assert (Hee : elo e <= ehi e) by (unfold elo, ehi; pose proof (bv_unsigned_in_range 64 (snd e)); lia).
    destruct (Rcov (Z.max (elo e) (bv_unsigned d)) ltac:(unfold PGSZ in *; lia)) as (e' & He' & Hx).
    pose proof (region_free_disj _ _ _ _ Hm He') as D. lia.
Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma ev_mremap_ok : forall L G s0 a l0 newlen, frame_ok G -> brk_quiet L -> In (a, l0) (ld_groups L) ->
  0 < newlen < LEN_MAX -> newlen mod PGSZ = 0 -> mmap_len l0 <> newlen ->
  mspec (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ G s mo)
        (ev_step (EMremap a (mmap_len l0) newlen))
        (ev_step_post L (EMremap a (mmap_len l0) newlen) G s0).
Proof.
  intros L G s0 a l0 newlen HG Hq Hin Hnl Hnlal Hne. pose proof alloc_ceiling_lt as Hcl. unfold ev_step.
  eapply mspec_bind.
  { apply (mspec_sys (NMremap a (mmap_len l0) newlen) (dec_mremap a (mmap_len l0) newlen [] []) _
             (fun x s mo' => s = s0 /\ G s mo' /\ ev_step_post L (EMremap a (mmap_len l0) newlen) G s0 (mremap_val a x) s mo')).
    intros s mo (-> & HK & HGs).
    pose proof (kl_groups _ _ _ HK a l0 Hin) as (A1 & A2 & A3 & A4 & A5 & A6).
    pose proof (went_In_bounds _ _ _ a l0 HK (or_introl Hin)) as (_ & B2 & _ & _ & B5 & B6).
    destruct (kl_mremap_src L (ps_brk s0) mo a l0 HK Hin) as (Hrfr & Hhas & Hrfn & Hm' & Dother).
    set (n := mmap_len l0) in *. set (h := m_vmmaps mo) in *. set (aw := Z_to_bv 64 a) in *. set (nw := Z_to_bv 64 n) in *.
    set (nnw := Z_to_bv 64 newlen).
    assert (Hnal : n mod 4096 = 0) by (subst n; apply mmap_len_aligned).
    assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; lia).
    assert (Un : bv_unsigned nw = n) by (subst nw; apply unsigned_lit; lia).
    assert (Unn : bv_unsigned nnw = newlen) by (subst nnw; apply unsigned_lit; unfold LEN_MAX in Hnl; lia).
    assert (Ewent : went a n = (aw, nw)) by reflexivity.
    split.
    { apply (nsafe_mremap a n newlen mo); [lia| rewrite page_size_eq; unfold PGSZ in A3; exact A3| lia| lia| | | exact (minv_lazyfree _ (kl_minv _ _ _ HK))| | | |];
        rewrite ?(page_round_up_Z_aligned n), ?(page_round_up_Z_aligned newlen) by (unfold PGSZ in *; lia).
      - (* [comment removed for export] *)
        pose proof (kl_top _ _ _ HK) as KT. unfold page_round_down_Z, page_size in KT.
        pose proof (Z.div_mod (alloc_top (m_vmmaps mo)) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (alloc_top (m_vmmaps mo)) 4096 ltac:(lia)).
        unfold h. lia.
      - unfold LEN_MAX in Hnl. lia.
      - exact Hrfr.
      - exact Hhas.
      - exact Hrfn.
      - intros d Hd. apply (kl_fresh_noacc _ _ _ d _ HK); [fold nnw; lia| exact Hd]. }
    intros rsp mo' evs Hst.
    destruct (nstep_mremap_cases L (ps_brk s0) mo a l0 newlen rsp mo' evs HK Hin Hnl Hnlal Hne Hst) as (-> & Hvo & Hmi' & Hh' & x & Hd & CASES).
    fold n h aw in CASES. cbv zeta in CASES.
    exists x. split; [exact Hd|]. split; [reflexivity|]. split; [eapply HG; [reflexivity| exact Hvo| exact HGs]|].
    (* [comment removed for export] *)
    pose proof (kl_distinct _ _ _ HK) as Kd.
    destruct (g_remove_split a l0 (ld_groups L) _ Hin Kd) as (g1 & g2 & Eg & Ezz).
    pose proof Kd as Kd0. rewrite Eg, map_app in Kd. cbn [map fst] in Kd. rewrite <- app_assoc in Kd. cbn [app] in Kd.
    pose proof (List.NoDup_remove_1 _ _ _ Kd) as Kd1. pose proof (List.NoDup_remove_2 _ _ _ Kd) as Kd2.
    assert (Hg' : forall b l, In (b, l) (g_remove a (ld_groups L)) -> In (b, l) (ld_groups L) /\ b <> a).
    { intros b l H. rewrite Ezz in H. rewrite Eg. split; [apply in_app_or in H as [H|H]; apply in_or_app; [left; exact H| right; right; exact H]|].
      intros ->. apply Kd2. rewrite app_assoc, <- map_app. apply in_or_app. left. apply in_map_iff. exists (a, l). split; [reflexivity| exact H]. }
    assert (Kfst : forall b l, b <> a -> 0 < b < 2^64 -> fst (went b (mmap_len l)) <> aw).
    { intros b l Hneq Hb E. apply Hneq. apply (f_equal bv_unsigned) in E. cbn [fst went] in E. rewrite unsigned_wz, Ua in E by lia. exact E. }
    (* [comment removed for export] *)
    assert (Hbase : forall e, In e (vm_maps h) -> fst e = aw -> e = (aw, nw)).
    { intros e He E. destruct (pwdisj_In _ _ _ (proj2 (kl_wf _ _ _ HK)) He A5) as [E'|D]; [rewrite E', Ewent; reflexivity|].
      exfalso. pose proof (proj1 (kl_wf _ _ _ HK) e He) as W. unfold edisj, elo, ehi in D, W. rewrite E, Ewent in D. rewrite E in W. cbn [fst snd] in D. rewrite Ua, Un in *. lia. }
    (* [comment removed for export] *)
    assert (Hcovk : forall b0 l1, ld_brkreg L = Some (b0, l1) -> wcov (map_remove (vm_maps h) aw) b0 (b0 + l1)).
    { intros b0 l1 E x0 Hx. pose proof (kl_brkreg _ _ _ HK b0 l1 E) as (_ & _ & _ & _ & _ & Rcov). destruct (Rcov x0 Hx) as (e & He & Hr).
      exists e. split; [| exact Hr]. apply map_remove_In. split; [exact He|]. intros Ef. pose proof (Hbase e He Ef) as ->.
      pose proof (A6 b0 l1 E) as D. rewrite Ewent in B5, B6. unfold elo, ehi in Hr, B5, B6. rewrite B5 in Hr. cbn [fst snd] in Hr, B6. rewrite Un, Ua in *. clear - a l0 newlen Hnl Hnlal n Hne A2 A3 B2 Hnal x b0 l1 x0 Hx Hr D. lia. }
    (* [comment removed for export] *)
    assert (KLnew : forall (d : Z), 0 < d -> d mod PGSZ = 0 -> d + newlen <= alloc_ceiling ->
       (forall e, In e (vm_reserved h) -> d + newlen <= elo e \/ ehi e <= d) ->
       (forall e, In e (map_remove (vm_maps h) aw) -> d + newlen <= elo e \/ ehi e <= d) ->
       m_vmmaps mo' = mkVmMapsFull (vm_reserved h) ((Z_to_bv 64 d, nnw) :: map_remove (vm_maps h) aw) (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) ->
       KL (set_groups ((d, newlen) :: g_remove a (ld_groups L)) L) (ps_brk s0) mo'
       /\ (forall b l, (In (b, l) (g_remove a (ld_groups L)) \/ exists k, In (b, l, k) (ld_metas L)) -> d + newlen <= b \/ b + mmap_len l <= d)
       /\ (forall b0 l1, ld_brkreg L = Some (b0, l1) -> d + newlen <= b0 \/ b0 + l1 <= d)).
    { intros d Hd0 Hdal Hdce Dresv Dmaps Evm. set (dw := Z_to_bv 64 d) in *.
      assert (Ud : bv_unsigned dw = d) by (subst dw; apply unsigned_lit; lia).
      assert (Hmln : mmap_len newlen = newlen) by (apply mmap_len_of_aligned; [lia| unfold PGSZ in Hnlal; exact Hnlal]).
      assert (Ewent' : went d (mmap_len newlen) = (dw, nnw)) by (rewrite Hmln; reflexivity).
      assert (Hrf' : region_free (map_remove (vm_maps h) aw) dw nnw = true).
      { apply region_free_of_disj. intros e He. rewrite Ud, Unn. exact (Dmaps e He). }
      assert (Dnew : forall b l, (In (b, l) (g_remove a (ld_groups L)) \/ exists k, In (b, l, k) (ld_metas L)) -> d + newlen <= b \/ b + mmap_len l <= d).
      { intros b l H.
        assert (Hb : (In (b, l) (ld_groups L) \/ exists k, In (b, l, k) (ld_metas L)) /\ b <> a).
        { destruct H as [H|[k H]]; [destruct (Hg' b l H) as [H1 H2]; auto| split; [right; exists k; exact H| exact (Hm' b l k H)]]. }
        destruct Hb as [Hb Hneq]. pose proof (went_In_bounds _ _ _ b l HK Hb) as (C1 & C2 & C3 & C4 & C5 & C6).
        specialize (Dmaps (went b (mmap_len l)) ltac:(apply map_remove_In; split; [exact C4| apply Kfst; [exact Hneq| lia]])). rewrite C5, C6 in Dmaps. lia. }
      assert (Dbrk : forall b0 l1, ld_brkreg L = Some (b0, l1) -> d + newlen <= b0 \/ b0 + l1 <= d).
      { intros b0 l1 E. pose proof (kl_brkreg _ _ _ HK b0 l1 E) as (R1 & R2 & R3 & R4 & R5 & _).
        pose proof (wcov_rf_disj _ _ _ _ _ (Hcovk b0 l1 E) Hrf' ltac:(rewrite Unn; lia) ltac:(clear -R3; unfold PGSZ in *; lia)) as D. rewrite Ud, Unn in D. exact D. }
      split; [| split; [exact Dnew| exact Dbrk]].
      assert (Hph' : phase_inv (ld_brk (set_groups ((d, newlen) :: g_remove a (ld_groups L)) L)) (set_groups ((d, newlen) :: g_remove a (ld_groups L)) L) (ps_brk s0) mo')
        by (eapply phase_quiet; [exact HK| exact Hq| reflexivity| reflexivity| rewrite Evm; reflexivity| rewrite Evm; reflexivity]).
      kl_open HK. constructor; try exact Hph'; try exact Hmi'; try exact Hh'; rewrite ?Evm; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit set_groups ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; auto.
      - apply vmwf_cons; [apply vmwf_remove; exact Kwf| rewrite Ud, Unn; lia| exact Hrf'].
      - intros r Hr. destruct (Kresv r Hr) as (e & C1 & C2 & [He|(He & Hpc & C3)]).
        + exists e. split; [exact C1|]. split; [exact C2|]. left; exact He.
        + assert (He' : In e (map_remove (vm_maps h) aw)).
          { apply map_remove_In. split; [exact He|]. intros Ef. pose proof (Hbase e He Ef) as ->.
            pose proof (C3 a l0 (or_introl Hin)) as D. unfold elo, ehi in D. cbn [fst snd] in D. rewrite Ua, Un in D. clear - D B2. lia. }
          exists e. split; [exact C1|]. split; [exact C2|]. right. split; [right; exact He'|]. split; [exact Hpc|].
          intros b l [[E|Hb]|[k Hb]]; [| destruct (Hg' b l Hb) as [Hb1 _]; apply C3; left; exact Hb1| apply C3; right; exists k; exact Hb].
          injection E as <- <-. rewrite Hmln. pose proof (Dmaps e He'). clear - a l0 newlen n Hne mo x d e H. lia.
      - intros b l [E|Hb].
        + injection E as <- <-. rewrite Ewent'. rewrite !Hmln. splits; try (clear - Hnl Hd0 Hdce; lia); try (unfold PGSZ in *; exact Hdal); try (left; reflexivity).
          unfold brk_disj. cbn. intros b0 l1 E. exact (Dbrk b0 l1 E).
        + destruct (Hg' b l Hb) as [Hb1 Hneq]. specialize (Kgr b l Hb1). destruct Kgr as ([G0 G1] & G2 & G3 & G4 & G5 & G6). splits; try assumption.
          right. apply map_remove_In. split; [exact G5|]. apply Kfst; [exact Hneq| pose proof (mmap_len_ge l G0); lia].
      - intros b l k Hb. pose proof (Hm' b l k Hb) as Hneq. specialize (Kme b l k Hb). destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). splits; try assumption.
        right. apply map_remove_In. split; [exact G7|]. apply Kfst; [exact Hneq| pose proof (mmap_len_ge l G0); lia].
      - cbn [map fst app]. constructor.
        + intros Hdd. rewrite Ezz, map_app, <- app_assoc in Hdd. apply in_app_or in Hdd as [Hdd|Hdd]; [| apply in_app_or in Hdd as [Hdd|Hdd]].
          * apply in_map_iff in Hdd as ([b l] & E & Hb). cbn in E. subst b.
            assert (Hgb : In (d, l) (g_remove a (ld_groups L))) by (rewrite Ezz; apply in_or_app; left; exact Hb).
            pose proof (Dnew d l (or_introl Hgb)) as D1. destruct (Hg' d l Hgb) as [Hb1 _]. pose proof (Kgr d l Hb1) as ([G0 _] & _). pose proof (mmap_len_ge l G0) as HML. clear - D1 G0 HML Hnl. lia.
          * apply in_map_iff in Hdd as ([b l] & E & Hb). cbn in E. subst b.
            assert (Hgb : In (d, l) (g_remove a (ld_groups L))) by (rewrite Ezz; apply in_or_app; right; exact Hb).
            pose proof (Dnew d l (or_introl Hgb)) as D1. destruct (Hg' d l Hgb) as [Hb1 _]. pose proof (Kgr d l Hb1) as ([G0 _] & _). pose proof (mmap_len_ge l G0) as HML. clear - D1 G0 HML Hnl. lia.
          * apply in_map_iff in Hdd as ([[b l] k] & E & Hb). cbn in E. subst b. pose proof (Dnew d l (or_intror (ex_intro _ k Hb))) as D1.
            pose proof (Kme d l k Hb) as ([G0 _] & _). pose proof (mmap_len_ge l G0) as HML. clear - D1 G0 HML Hnl. lia.
        + rewrite Ezz, map_app, <- app_assoc. exact Kd1.
      - intros b0 l1 E. specialize (Kreg b0 l1 E). destruct Kreg as (R1 & R2 & R3 & R4 & R5 & Rcov). splits; auto.
        eapply wcov_mono; [| apply Hcovk; exact E]. intros e He. right. exact He.
      - (* [comment removed for export] *) intros e [E|He].
        + subst e. right. rewrite elo_pair. cbn [snd]. rewrite Ud, Unn. split; [lia|]. unfold PGSZ in *. split; [exact Hnlal| exact Hdal].
        + apply map_remove_In in He as [He _]. exact (Kgran e He).
      - (* [comment removed for export] *) intros b l [[E|Hb]|[k Hb]] e He; [| destruct (Hg' b l Hb) as [Hb1 _]; apply (Kgrv b l (or_introl Hb1)); exact He| apply (Kgrv b l (or_intror (ex_intro _ k Hb))); exact He].
        injection E as <- <-. rewrite Hmln. exact (Dresv e He). }
    (* [comment removed for export] *)
    assert (RF : forall (ls : list (Z * Z)) lo m, (forall x0, In x0 ls -> lo + m <= fst x0 \/ fst x0 + snd x0 <= lo) -> ranges_free ls lo m = true).
    { intros ls lo m H. unfold ranges_free. apply forallb_forall. intros [b0 m0] Hx. cbn [fst snd]. unfold iv_disjoint.
      destruct (H _ Hx) as [D|D]; cbn [fst snd] in D; [rewrite (proj2 (Z.leb_le _ _) D); reflexivity| rewrite (proj2 (Z.leb_le _ _) D); apply orb_true_r]. }
    unfold ev_step_post. cbn [answer_ok event_post].
    destruct CASES as [[Ez ->]|(Hie & His & Hz0 & Hzal & Hzce & Evm & Dresv & Dmaps & WHERE)].
    - (* [comment removed for export] *) rewrite Ez. unfold mremap_answer_okL. rewrite is_errno_form_neg by (unfold ENOMEM; lia). cbn [orb]. rewrite is_err_neg by (unfold ENOMEM; lia).
      splits; auto.
    - set (z := mremap_val a x) in *. rewrite Hie.
      destruct (KLnew z Hz0 Hzal Hzce Dresv Dmaps Evm) as (HK' & Dnew & Dbrk).
      split; [| split; [exact HK'| split; [eapply HG; [reflexivity| exact Hvo| exact HGs]| split; reflexivity]]].
      unfold mremap_answer_okL. rewrite His. cbn [orb].
      destruct WHERE as [Ez|(Hza & Hlt & Dall)].
      + (* [comment removed for export] *) rewrite Ez in *. rewrite Z.eqb_refl. cbn [andb negb]. rewrite orb_false_r.
        destruct (Z.leb_spec newlen n) as [Hle|Hgt]; [reflexivity|]. cbn [orb]. rewrite (proj2 (Z.leb_le _ _) Hzce). cbn [andb].
        apply RF. intros x0 Hx. unfold lranges_wo in Hx.
        apply In_lranges in Hx as [H|[(b1 & l1 & H & E)|[(b1 & l1 & k & H & E)|(b1 & l1 & H & E)]]]; cbn [ld_resv ld_groups ld_metas ld_brkreg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.set_groups] in H.
        * destruct (kl_resv _ _ _ HK _ H) as (e & C1 & C2 & He).
          assert (D : a + newlen <= elo e \/ ehi e <= a).
          { destruct He as [He|(He & _ & C3)]; [exact (Dresv e He)|]. apply Dmaps. apply map_remove_In. split; [exact He|].
            intros Ef. pose proof (Hbase e He Ef) as ->. pose proof (C3 a l0 (or_introl Hin)) as D. rewrite Ewent in B5, B6. unfold elo, ehi in D, B5, B6 |- *. cbn [fst snd] in *. rewrite Ua, Un in *. lia. }
          lia.
        * subst x0. cbn [fst snd]. pose proof (Dnew b1 l1 (or_introl H)). rewrite round_up_pg_eq. fold (mmap_len l1). lia.
        * subst x0. cbn [fst snd]. pose proof (Dnew b1 l1 (or_intror (ex_intro _ k H))). rewrite round_up_pg_eq. fold (mmap_len l1). lia.
        * subst x0. cbn [fst snd]. pose proof (Dbrk b1 l1 H). pose proof (kl_brkreg _ _ _ HK b1 l1 H) as (_ & _ & R3 & R4 & _).
          rewrite round_up_pg_aligned by (unfold PGSZ in R4; exact R4). unfold PGSZ in *. lia.
      + (* [comment removed for export] *) replace (z =? a) with false by (symmetry; apply Z.eqb_neq; exact Hza). cbn [andb orb negb].
        rewrite (proj2 (Z.ltb_lt _ _) Hz0). unfold PGSZ at 1. unfold PGSZ in Hzal. rewrite Hzal, Z.eqb_refl. rewrite (proj2 (Z.leb_le _ _) Hzce). cbn [andb].
        apply RF. intros x0 Hx.
        apply In_lranges in Hx as [H|[(b1 & l1 & H & E)|[(b1 & l1 & k & H & E)|(b1 & l1 & H & E)]]].
        * destruct (kl_resv _ _ _ HK _ H) as (e & C1 & C2 & He).
          assert (D : z + newlen <= elo e \/ ehi e <= z) by (destruct He as [He|(He & _)]; [exact (Dresv e He)| exact (Dall e He)]). lia.
        * subst x0. cbn [fst snd]. pose proof (went_In_bounds _ _ _ b1 l1 HK (or_introl H)) as (_ & _ & _ & C4 & C5 & C6).
          pose proof (Dall _ C4) as D. rewrite C5, C6 in D. rewrite round_up_pg_eq. fold (mmap_len l1). lia.
        * subst x0. cbn [fst snd]. pose proof (went_In_bounds _ _ _ b1 l1 HK (or_intror (ex_intro _ k H))) as (_ & _ & _ & C4 & C5 & C6).
          pose proof (Dall _ C4) as D. rewrite C5, C6 in D. rewrite round_up_pg_eq. fold (mmap_len l1). lia.
        * subst x0. cbn [fst snd]. pose proof (Dbrk b1 l1 H). pose proof (kl_brkreg _ _ _ HK b1 l1 H) as (_ & _ & R3 & R4 & _).
          rewrite round_up_pg_aligned by (unfold PGSZ in R4; exact R4). unfold PGSZ in *. lia. }
  intros x. cbn beta. apply mspec_ret. intros s mo' (-> & HGs & HP). exact HP.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


#[using="Type"] Lemma ev_step_spec : forall L e (G : St -> Model -> Prop) s0,
  frame_ok G -> event_pre L e ->
  mspec (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ G s mo) (ev_step e) (ev_step_post L e G s0).
Proof.
  intros L e G s0 HG Hpre. destruct e as [req|addr len prot flags|addr len|addr len prot|? ? ?|?|? ? ?]; cbn [event_pre] in Hpre; try contradiction; try (destruct Hpre as [[] ?]).
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
  - (* [comment removed for export] *) destruct Hpre as (Hq & (l0 & Hin & <-) & Hnl & Hal & Hne). rewrite round_up_pg_eq in Hne |- *. fold (mmap_len l0) in Hne |- *.
    apply (ev_mremap_ok L G s0 _ l0); assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma membed_spec {R} : forall (t : stree ev Z R) (Post : mled -> R -> Prop) (G : St -> Model -> Prop) L s0,
  frame_ok G -> ctree_ok L t Post ->
  mspec (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ G s mo) (membed t)
        (fun r s mo => exists L', cpath L t L' r /\ Post L' r /\ KL L' (ps_brk s) mo /\ G s mo
                       /\ ps_m s = ps_m s0 /\ ps_rest s = ps_rest s0).
Proof.
  intros t. induction t as [r|e k IH]; intros Post G L s0 HG Hok.
  - cbn [membed]. apply mspec_ret. intros s mo (-> & HK & HGs). exists L.
    split; [constructor|]. cbn in Hok. splits; auto.
  - cbn [membed]. cbn in Hok. destruct Hok as [Hpre Hk].
    eapply mspec_bind; [apply (ev_step_spec L e G s0 HG Hpre)|].
    intros z. unfold ev_step_post. apply mspec_pointwise. intros s1 mo1 (Hans & HK1 & HG1 & Hm & Hx1).
    eapply mspec_conseq; [apply (IH z Post G (event_post L e z) s1 HG (Hk z Hans))| |].
    + intros s mo [-> ->]. auto.
    + intros r s mo (L' & Hp & HP & HK & HG' & Hm' & Hx'). exists L'. split; [econstructor; eauto|].
      splits; auto; congruence.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition OWN (X : list bptr) (G : St -> Model -> Prop) : assn St := fun s mo =>
  (exists L, creach (ps_m s) L /\ KL L (ps_brk s) mo /\ incl (map fst X) (ld_live L))
  /\ List.NoDup (map fst X) /\ G s mo.

#[using="Type"] Lemma OWN_G : forall X G s mo, OWN X G s mo -> G s mo.
Proof. intros X G s mo [_ [_ H]]. exact H. Qed.

#[using="Type"] Lemma OWN_perm : forall X Y G s mo, Permutation X Y -> OWN X G s mo -> OWN Y G s mo.
Proof.
  intros X Y G s mo HP [(L & Hc & HK & Hi) [Hnd HG]].
  assert (HP' : Permutation (map fst X) (map fst Y)) by (apply Permutation_map; exact HP).
  split; [|split; [|exact HG]].
  - exists L. split; [exact Hc|]. split; [exact HK|]. intros c Hc'. apply Hi.
    eapply Permutation_in; [apply Permutation_sym; exact HP'| exact Hc'].
  - eapply Permutation_NoDup; [exact HP'| exact Hnd].
Qed.

#[using="Type"] Lemma OWN_weakG : forall X G G' s mo, OWN X G s mo -> (G s mo -> G' s mo) -> OWN X G' s mo.
Proof. intros X G G' s mo [A [B C]] H. split; [exact A|]. split; [exact B|]. auto. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma OWN_other : forall X G s s' mo, OWN X G s mo -> ps_m s' = ps_m s -> ps_brk s' = ps_brk s -> G s' mo -> OWN X G s' mo.
Proof.
  intros X G s s' mo [(L & Hc & HK & Hi) [Hnd HG]] Hm Hb HG'. split; [|split; [exact Hnd|exact HG']].
  exists L. rewrite Hm, Hb. auto.
Qed.

#[using="Type"] Lemma OWN_nodup : forall X G s mo, OWN X G s mo -> List.NoDup (map fst X).
Proof. intros X G s mo [_ [H _]]. exact H. Qed.

#[using="Type"] Lemma KL_set_live : forall L v pbrk mo, KL L pbrk mo -> KL (set_live v L) pbrk mo.
Proof. intros L v pbrk mo K. destruct K; constructor; cbn; auto. Qed.

#[using="Type"] Lemma event_post_live : forall L e z, ld_live (event_post L e z) = ld_live L.
Proof.
  intros L e z. destruct e; cbn; repeat (destruct (_ =? _)); try reflexivity;
  try (destruct (ld_brk L); try reflexivity; destruct (ld_brkreg L) as [[? ?]|]; reflexivity);
  try (destruct (is_err z); reflexivity); try (destruct (_ || _); reflexivity).
Qed.

#[using="Type"] Lemma cpath_live {R} : forall L (t : stree ev Z R) L' r, cpath L t L' r -> ld_live L' = ld_live L.
Proof. intros L t L' r H. induction H; [reflexivity|]. rewrite IHcpath. apply event_post_live. Qed.

#[using="Type"] Lemma aptr_eqb_eq : forall a b, aptr_eqb a b = true <-> a = b.
Proof.
  intros [a1 a2] [b1 b2]. unfold aptr_eqb. cbn. rewrite andb_true_iff, N.eqb_eq, Z.eqb_eq.
  split; [intros [-> ->]; reflexivity| intros H; inversion H; auto].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

End Main.

End WithCeil.
End KStep.

(* [comment removed for export] *)
Module LB_Kernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad MSafe STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MSafe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KLink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KStep__Spec.KStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Export LB_Quant.
(* [comment removed for export] *) Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.zify_cheap_cleanup ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.zify_split_ranges; OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.zify_spec_trivial.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)

Section WithCeil.
Context {CE : CEIL}.
#[using="Type"] Lemma live_bytes_filter_le f l : live_bytes (List.filter f l) <= live_bytes l.
Proof. induction l as [|[a n] l IH]; cbn; [lia|]. pose proof (bv_unsigned_in_range 64 n). destruct (f (a, n)); cbn; lia. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma live_bytes_remove_notin l aw : (forall e', In e' l -> fst e' <> aw) -> live_bytes (map_remove l aw) = live_bytes l.
Proof.
  unfold map_remove. induction l as [|[a n] l IH]; intros NI; [reflexivity|]. cbn [List.filter fst].
  destruct (bv_eqb a aw) eqn:E; [exfalso; apply bv_eqb_eq in E; exact (NI (a, n) (or_introl eq_refl) E)|]. cbn [negb].
  rewrite !live_bytes_cons. rewrite IH; [reflexivity|]. intros e' He'. apply NI. right. exact He'.
Qed.

#[using="Type"] Lemma live_bytes_remove maps aw nw : vmwf maps -> In (aw, nw) maps ->
  live_bytes (map_remove maps aw) = live_bytes maps - bv_unsigned nw.
Proof.
  intros [Hne Hpw] Hin. induction maps as [|e l IH]; [destruct Hin|].
  inversion Hpw as [|e0 l0 Hd Hpw']; subst.
  assert (SAME : forall e', In e' l -> fst e' = fst e -> False).
  { intros e' He' E. specialize (Hd e' He'). unfold edisj, elo, ehi in Hd. rewrite E in Hd.
    pose proof (Hne e (or_introl eq_refl)) as N1. pose proof (Hne e' (or_intror He')) as N2. unfold elo, ehi in N1, N2. rewrite E in N2. lia. }
  unfold map_remove. cbn [List.filter]. destruct Hin as [->|Hin].
  - cbn [fst]. rewrite bv_eqb_refl. cbn [negb]. rewrite live_bytes_cons. cbn [snd].
    fold (map_remove l aw). rewrite live_bytes_remove_notin; [lia|]. intros e' He' E. exact (SAME e' He' E).
  - destruct (bv_eqb (fst e) aw) eqn:E.
    + exfalso. apply bv_eqb_eq in E. exact (SAME _ Hin (eq_sym E)).
    + cbn [negb]. rewrite !live_bytes_cons. fold (map_remove l aw). rewrite IH; [lia| intros x Hx; apply Hne; right; exact Hx| exact Hpw'| exact Hin].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma live_bytes_iv_subtract a sz lo hi : 0 <= lo -> lo <= hi ->
  live_bytes (iv_subtract a sz lo hi) <= bv_unsigned sz.
Proof.
  intros Hlo Hlh. pose proof (bv_unsigned_in_range 64 a) as Ra. pose proof (bv_unsigned_in_range 64 sz) as Rs. unfold bv_modulus in *.
  unfold iv_subtract.
  destruct (Z.ltb_spec (bv_unsigned a) lo); destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); cbn;
    rewrite ?unsigned_lit_wrap;
    try pose proof (Z.mod_le (bv_unsigned sz `min` (lo - bv_unsigned a)) (2^64) ltac:(lia) ltac:(lia));
    try pose proof (Z.mod_le (bv_unsigned a + bv_unsigned sz - bv_unsigned a `max` hi) (2^64) ltac:(lia) ltac:(lia)); lia.
Qed.

#[using="Type"] Lemma live_bytes_subtract maps lo hi : 0 <= lo -> lo <= hi -> live_bytes (maps_subtract maps lo hi) <= live_bytes maps.
Proof.
  intros H0 H. induction maps as [|[a sz] l IH]; cbn; [lia|]. rewrite live_bytes_app. pose proof (live_bytes_iv_subtract a sz lo hi H0 H). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma gm_remove_group L pbrk mo a l0 : KL L pbrk mo -> In (a, l0) (ld_groups L) ->
  gm (set_groups (g_remove a (ld_groups L)) L) = gm L - mmap_len l0.
Proof.
  intros HK Hin. destruct (g_remove_split a l0 (ld_groups L) _ Hin (kl_distinct _ _ _ HK)) as (g1 & g2 & Eg & Ezz).
  unfold gm. cbn [ld_groups ld_metas set_groups]. rewrite Ezz, Eg, !sum_map_app. cbn. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma li_brk0 L pbrk mo rsp mo' evs z : KL L pbrk mo -> LI L mo -> ld_brk L = BPUntried ->
  nstep (NBrk 0) mo rsp mo' evs -> LI (set_brkph (BPQueried z) L) mo'.
Proof.
  intros HK HL Hph Hst. destruct (nstep_brk_inv 0 mo rsp mo' evs Hst) as (r & Hok & -> & _ & _).
  apply brk_r_ok_query in Hok. subst r. destruct (brk_model_next_query (m_vmmaps mo)) as (_ & E2 & _).
  pose proof (kl_phase _ _ _ HK) as P. rewrite Hph in P. destruct P as [_ Hreg].
  apply (LI_same_vm L _ mo); [exact HL| rewrite m_vmmaps_brk; exact E2| reflexivity|]. unfold BB. cbn. rewrite Hreg, Hph. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma li_brk_grow L pbrk mo rsp mo' evs req a :
  KL L pbrk mo -> LI L mo ->
  ((exists cur, ld_brk L = BPQueried cur /\ req = round_up_pg cur + 2 * PGSZ)
   \/ (exists b l, ld_brk L = BPLive /\ ld_brkreg L = Some (b, l) /\ req = b + l + PGSZ)) ->
  nstep (NBrk req) mo rsp mo' evs -> dec_brk pbrk req rsp = Some a ->
  LI (event_post L (EBrk req) (match a with BrkGrown => req | BrkSame => pbrk end)) mo'.
Proof.
  intros HK HL Hpre Hst Hd. pose proof alloc_ceiling_lt as Hcl.
  pose proof (kl_start _ _ _ HK) as (S1 & S2 & S3 & S4). pose proof (kl_phase _ _ _ HK) as P.
  set (h := m_vmmaps mo) in *.
  (* [comment removed for export] *)
  assert (PH : bv_unsigned (vm_brk h) = pbrk /\ 0 < pbrk /\ pbrk < req < 2^64 /\ req <> 0
               /\ BB (set_brkph BPDead L) = BB L
               /\ gm (if req =? req then match ld_brk L with BPQueried cur => set_brkph (BPGuard cur) L | _ => match ld_brkreg L with Some (b, l) => set_brkreg (Some (b, l + PGSZ)) L | None => L end end else set_brkph BPDead L) = gm L
               /\ BB (if req =? req then match ld_brk L with BPQueried cur => set_brkph (BPGuard cur) L | _ => match ld_brkreg L with Some (b, l) => set_brkreg (Some (b, l + PGSZ)) L | None => L end end else set_brkph BPDead L) = BB L + (req - pbrk)).
  { rewrite Z.eqb_refl. destruct Hpre as [(cur & Hph & ->)|(b & l & Hph & Hreg & ->)]; rewrite Hph in P |- *.
    - destruct P as (Ecur & Ebrk & Epbrk & Hreg). unfold BB. cbn. rewrite !Hph, !Hreg. cbn. rewrite ?Hph, ?Hreg.
      rewrite (round_up_pg_aligned cur) by (rewrite Ecur; unfold PGSZ in S2; exact S2). unfold PGSZ in *. repeat split; try reflexivity; lia.
    - destruct P as (b' & l' & Hreg' & Ebrk & Epbrk). rewrite Hreg in Hreg'. inversion Hreg'; subst b' l'.
      pose proof (kl_brkreg _ _ _ HK b l Hreg) as (R1 & R2 & R3 & R4 & R5 & _). unfold BB. cbn. rewrite !Hph, !Hreg. cbn. rewrite ?Hph, ?Hreg. unfold PGSZ in *. repeat split; try reflexivity; lia. }
  destruct PH as (Ebrk & Hp0 & Hreq & NZ & BBd & GMg & BBg).
  destruct (nstep_brk_inv req mo rsp mo' evs Hst) as (r & Hok & Emo' & Ersp & _). fold h in Hok, Emo', Ersp.
  unfold event_post. rewrite (proj2 (Z.eqb_neq _ _) NZ).
  pose proof (dec_brk_Some _ _ _ _ Hd) as SH.
  destruct a.
  - (* [comment removed for export] *)
    rewrite Ersp in SH. assert (Er : r = Z_to_bv 64 req) by (inversion SH; reflexivity). subst r.
    destruct (brk_model_next_grown h req ltac:(lia) ltac:(lia)) as (_ & Emaps & _ & _ & _).
    unfold LI. rewrite GMg, BBg. rewrite Emo', m_vmmaps_brk. fold h. unfold vm_live_bytes.
    rewrite Emaps, live_bytes_cons. cbn [snd]. rewrite unsigned_lit by lia. rewrite Ebrk. apply LI_elim in HL. unfold vm_live_bytes in HL. fold h in HL. lia.
  - (* [comment removed for export] *)
    rewrite Ersp in SH. unfold eff0 in SH. assert (Er : r = Z_to_bv 64 pbrk) by (inversion SH; reflexivity).
    assert (Er' : r = vm_brk h) by (rewrite Er, <- Ebrk; apply Z_to_bv_bv_unsigned). clear Er. subst r.
    destruct (brk_model_next_same h (Z_to_bv 64 req)) as (_ & Emaps & _ & _ & _).
    replace (pbrk =? req) with false by (symmetry; apply Z.eqb_neq; lia).
    apply (LI_same_vm L _ mo); [exact HL| rewrite Emo', m_vmmaps_brk; exact Emaps| reflexivity| exact BBd].
Qed.

Definition mm_val (x : mmap_ans) : Z := match x with MmErr e => neg_errno e | MmOk a => a end.

#[using="Type"] Lemma mm_post_eq L len prot z : prot = PROT_NONE \/ prot = PROT_RW ->
  event_post L (EMmap 0 len prot MAPF) z
  = (if is_err z then L else if prot =? PROT_NONE then set_metas ((z, len, 0) :: ld_metas L) L else set_groups ((z, len) :: ld_groups L) L).
Proof. intros _. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma li_mmap_core L mo mo' len z :
  LI L mo -> 0 < len < LEN_MAX ->
  ((is_err z = true /\ vm_maps (m_vmmaps mo') = vm_maps (m_vmmaps mo))
   \/ (is_err z = false /\ vm_maps (m_vmmaps mo') = (Z_to_bv 64 z, Z_to_bv 64 (mmap_len len)) :: vm_maps (m_vmmaps mo))) ->
  forall prot, prot = PROT_NONE \/ prot = PROT_RW -> LI (event_post L (EMmap 0 len prot MAPF) z) mo'.
Proof.
  intros HL Hlen CASES prot Hprot. rewrite (mm_post_eq L len prot z Hprot).
  pose proof (mmap_len_ge len ltac:(lia)) as ML. unfold LEN_MAX in Hlen.
  destruct CASES as [[-> E]|[-> E]].
  - apply (LI_same_vm L _ mo); [exact HL| exact E| reflexivity| reflexivity].
  - unfold LI, vm_live_bytes in *. rewrite E, live_bytes_cons. cbn [snd]. rewrite unsigned_lit by lia.
    destruct Hprot as [-> | ->]; cbn [Z.eqb PROT_NONE PROT_RW Pos.eqb].
    + rewrite gm_add_meta, BB_set_metas. lia.
    + rewrite gm_add_group, BB_set_groups. lia.
Qed.

#[using="Type"] Lemma mmap_ok_not_err len avoid a : mmap_addr_ok len avoid a = true -> 0 < len -> is_err a = false /\ 0 <= a < 2^64.
Proof.
  intros H Hlen. unfold mmap_addr_ok in H. apply andb_prop in H as [H _]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.ltb_lt in H2. apply Z.leb_le in H3. pose proof alloc_ceiling_lt. pose proof (mmap_len_ge len Hlen).
  unfold is_err, TWO64. split; [apply Z.ltb_ge; lia| lia].
Qed.

#[using="Type"] Lemma li_mmap_rw L pbrk mo rsp mo' evs len x :
  KL L pbrk mo -> LI L mo -> 0 < len < LEN_MAX ->
  nstep (NMmap 0 len PROT_RW MAPF) mo rsp mo' evs -> dec_mmap len [] rsp = Some x ->
  LI (event_post L (EMmap 0 len PROT_RW MAPF) (mm_val x)) mo'.
Proof.
  intros HK HL Hlen Hst Hd. pose proof (mmap_len_ge len ltac:(lia)) as ML. unfold LEN_MAX in Hlen.
  destruct (nstep_dec_mmap len [] mo rsp mo' evs ltac:(lia) ltac:(lia) ltac:(rewrite <- (kl_top _ _ _ HK); lia) ltac:(constructor) Hst) as (_ & _ & x' & Hd' & Hx).
  rewrite Hd in Hd'. assert (x' = x) by congruence. subst x'.
  apply (li_mmap_core L mo mo' len (mm_val x) HL ltac:(unfold LEN_MAX; lia)); [| right; reflexivity].
  destruct x as [e|a]; cbn [mm_val].
  - destruct Hx as [-> ->]. left. split; [apply is_err_neg; unfold ENOMEM; lia| reflexivity].
  - destruct Hx as (Hok & _ & E). right. destruct (mmap_ok_not_err _ _ _ Hok ltac:(lia)) as [NE Ha]. split; [exact NE|]. rewrite E. reflexivity.
Qed.

#[using="Type"] Lemma li_mmap_none L pbrk mo rsp mo' evs len x :
  KL L pbrk mo -> LI L mo -> 0 < len < LEN_MAX ->
  nstep (NMmap 0 len PROT_NONE MAPF) mo rsp mo' evs -> dec_mmap_none len [] rsp = Some x ->
  LI (event_post L (EMmap 0 len PROT_NONE MAPF) (mm_val x)) mo'.
Proof.
  intros HK HL Hlen Hst Hd. pose proof (mmap_len_ge len ltac:(lia)) as ML. unfold LEN_MAX in Hlen.
  destruct (nstep_dec_mmap_none len [] mo rsp mo' evs ltac:(lia) ltac:(lia) ltac:(rewrite <- (kl_top _ _ _ HK); lia) ltac:(constructor) Hst) as (_ & _ & x' & Hd' & Hx).
  rewrite Hd in Hd'. assert (x' = x) by congruence. subst x'.
  apply (li_mmap_core L mo mo' len (mm_val x) HL ltac:(unfold LEN_MAX; lia)); [| left; reflexivity].
  destruct x as [e|a]; cbn [mm_val].
  - destruct Hx as [-> ->]. left. split; [apply is_err_neg; unfold ENOMEM; lia| reflexivity].
  - destruct Hx as (Hok & _ & E). right. destruct (mmap_ok_not_err _ _ _ Hok ltac:(lia)) as [NE Ha]. split; [exact NE|]. rewrite E. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma li_mmap_fixed L pbrk mo rsp mo' evs cur z :
  KL L pbrk mo -> LI L mo -> ld_brk L = BPGuard cur ->
  nstep (NMmap (round_up_pg cur) PGSZ PROT_NONE MAPFX) mo rsp mo' evs ->
  LI (event_post L (EMmap (round_up_pg cur) PGSZ PROT_NONE MAPFX) z) mo'.
Proof.
  intros HK HL Hph Hst. pose proof alloc_ceiling_lt as Hcl.
  pose proof (kl_phase _ _ _ HK) as Kph. rewrite Hph in Kph. destruct Kph as (Ecur & Ebrk & Epbrk & Ereg & Hceil & (e0 & He0 & He0l & He0h) & Dg & Dm).
  pose proof (kl_start _ _ _ HK) as (S1 & S2 & S3 & S4).
  set (a := round_up_pg cur) in *.
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
  pose proof (nstep_mmap_fixed_inv a mo rsp mo' evs (kl_top _ _ _ HK) ltac:(lia) ltac:(lia) ltac:(rewrite Ha, Ecur; exact S2) Hrf Hmc Hst) as (_ & _ & x & Hd & Hx).
  fold h aw nw in Hx.
  assert (POST : event_post L (EMmap a PGSZ PROT_NONE MAPFX) z = set_brkph BPLive (set_brkreg (Some (a, 2 * PGSZ)) L)) by reflexivity.
  rewrite POST. unfold LI. rewrite gm_set_brkph, gm_set_brkreg.
  assert (E2 : BB (set_brkph BPLive (set_brkreg (Some (a, 2 * PGSZ)) L)) = 2 * PGSZ) by reflexivity. rewrite E2.
  apply LI_elim in HL. unfold BB in HL. rewrite Hph in HL.
  assert (LE : vm_live_bytes (m_vmmaps mo') <= vm_live_bytes h).
  { unfold vm_live_bytes. destruct x as [e| |e]; [destruct Hx| | destruct Hx]. rewrite Hx. cbn [vm_maps]. lia. }
  subst h. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma nstep_munmap_exact a len l0 mo rsp mo' evs :
  let h := m_vmmaps mo in let aw := Z_to_bv 64 a in let nw := Z_to_bv 64 (mmap_len l0) in
  0 < a -> a mod PGSZ = 0 -> 0 < l0 -> a + mmap_len l0 <= alloc_ceiling -> 0 < len < 2^64 -> mmap_len len = mmap_len l0 ->
  In (aw, nw) (vm_maps h) ->
  nstep (NMunmap a len) mo rsp mo' evs ->
  vm_maps (m_vmmaps mo') = map_remove (vm_maps h) aw.
Proof.
  intros h aw nw Ha Hal Hl0 Hceil Hlen Hmm Hin Hst. pose proof alloc_ceiling_lt as Hcl. pose proof (mmap_len_ge l0 Hl0) as ML.
  assert (Hhas : map_has (vm_maps h) aw nw = true).
  { unfold map_has. apply existsb_exists. exists (aw, nw). split; [exact Hin|]. cbn [fst snd]. rewrite !bv_eqb_refl. reflexivity. }
  destruct (nstep_dec_munmap a len mo rsp mo' evs ltac:(lia) ltac:(lia) ltac:(rewrite page_size_eq; unfold PGSZ in Hal; exact Hal)
              ltac:(rewrite Hmm; ceil_bounds; unfold TASK_SIZE; lia) ltac:(rewrite Hmm; exact Hhas) Hst) as (_ & _ & _ & E).
  rewrite E. reflexivity.
Qed.

#[using="Type"] Lemma li_munmap L pbrk mo rsp mo' evs a l0 len z :
  KL L pbrk mo -> LI L mo -> In (a, l0) (ld_groups L) -> (len = l0 \/ len = round_up_pg l0) ->
  nstep (NMunmap a len) mo rsp mo' evs ->
  LI (event_post L (EMunmap a len) z) mo'.
Proof.
  intros HK HL Hin Hlen Hst. pose proof alloc_ceiling_lt as Hcl.
  pose proof (kl_groups _ _ _ HK a l0 Hin) as (A1 & A2 & A3 & A4 & A5 & A6). unfold LEN_MAX in A1.
  pose proof (mmap_len_ge l0 ltac:(lia)) as ML.
  assert (Hnn : mmap_len (mmap_len l0) = mmap_len l0) by (apply mmap_len_of_aligned; [lia| apply mmap_len_aligned]).
  rewrite round_up_pg_eq in Hlen. fold (mmap_len l0) in Hlen.
  assert (Hlen3 : 0 < len < 2^64 /\ mmap_len len = mmap_len l0).
  { destruct Hlen as [-> | ->]; [split; [lia| reflexivity]| split; [lia| exact Hnn]]. }
  destruct Hlen3 as [Hlen1 Hlen2].
  pose proof (nstep_munmap_exact a len l0 mo rsp mo' evs A2 ltac:(unfold PGSZ in A3; exact A3) ltac:(lia) A4 Hlen1 Hlen2 A5 Hst) as Emaps.
  unfold went, wz in A5. unfold LI, vm_live_bytes. rewrite Emaps, (live_bytes_remove _ _ _ (kl_wf _ _ _ HK) A5).
  change (event_post L (EMunmap a len) z) with (set_groups (g_remove a (ld_groups L)) L).
  rewrite (gm_remove_group L pbrk mo a l0 HK Hin), BB_set_groups. rewrite unsigned_lit by lia.
  apply LI_elim in HL. unfold vm_live_bytes in HL. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma gm_mremap_group L pbrk mo a l0 z newlen : KL L pbrk mo -> In (a, l0) (ld_groups L) ->
  gm (set_groups ((z, newlen) :: g_remove a (ld_groups L)) L) = gm L - mmap_len l0 + mmap_len newlen.
Proof.
  intros HK Hin. pose proof (gm_remove_group L pbrk mo a l0 HK Hin) as G.
  unfold gm in *. cbn [ld_groups ld_metas set_groups] in *. cbn [map fold_right]. cbn [snd]. lia.
Qed.

#[using="Type"] Lemma li_mremap L pbrk mo rsp mo' evs a l0 newlen x :
  KL L pbrk mo -> LI L mo -> In (a, l0) (ld_groups L) -> 0 < newlen < LEN_MAX -> newlen mod PGSZ = 0 -> mmap_len l0 <> newlen ->
  nstep (NMremap a (mmap_len l0) newlen) mo rsp mo' evs -> dec_mremap a (mmap_len l0) newlen [] [] rsp = Some x ->
  LI (event_post L (EMremap a (mmap_len l0) newlen) (mremap_val a x)) mo'.
Proof.
  intros HK HL Hin Hnl Hal Hne Hst Hd. pose proof alloc_ceiling_lt as Hcl.
  pose proof (kl_groups _ _ _ HK a l0 Hin) as (A1 & A2 & A3 & A4 & A5 & A6). unfold LEN_MAX in A1.
  pose proof (mmap_len_ge l0 ltac:(lia)) as ML.
  destruct (nstep_mremap_cases L pbrk mo a l0 newlen rsp mo' evs HK Hin Hnl Hal Hne Hst) as (_ & _ & _ & _ & x' & Hd' & CASES).
  rewrite Hd in Hd'. injection Hd' as <-. cbv zeta in CASES. set (z := mremap_val a x) in *.
  cbn [event_post]. destruct CASES as [[Ez ->]|(Hie & _ & Hz0 & Hzal & Hce & Evm & _)].
  - rewrite Ez, is_err_neg by (unfold ENOMEM; lia). exact HL.
  - rewrite Hie. unfold LI, vm_live_bytes. rewrite Evm. cbn [vm_maps]. rewrite live_bytes_cons. cbn [snd].
    unfold went, wz in A5. rewrite (live_bytes_remove _ _ _ (kl_wf _ _ _ HK) A5).
    rewrite (gm_mremap_group L pbrk mo a l0 z newlen HK Hin), BB_set_groups.
    rewrite (mmap_len_of_aligned newlen) by (try lia; unfold PGSZ in Hal; exact Hal).
    rewrite !unsigned_lit by (unfold LEN_MAX in Hnl; lia).
    apply LI_elim in HL. unfold vm_live_bytes in HL. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma li_mprotect L pbrk mo rsp mo' evs b l k z :
  KL L pbrk mo -> LI L mo -> In (b, l, k) (ld_metas L) -> (2 + k) * PGSZ <= round_up_pg l ->
  nstep (NMprotect (b + (1 + k) * PGSZ) PGSZ PROT_RW) mo rsp mo' evs ->
  LI (event_post L (EMprotect (b + (1 + k) * PGSZ) PGSZ PROT_RW) z) mo'.
Proof.
  intros HK HL Hin Hk Hst. pose proof alloc_ceiling_lt as Hcl.
  pose proof (kl_metas _ _ _ HK b l k Hin) as (A1 & A2 & A3 & A4 & Ak & Ak1 & A5 & A6 & Ana). unfold LEN_MAX in A1.
  pose proof (went_In_bounds _ _ _ b l HK (or_intror (ex_intro _ k Hin))) as (_ & B2 & _ & _ & B5 & B6).
  rewrite round_up_pg_eq in Hk. fold (mmap_len l) in Hk.
  set (a := b + (1 + k) * PGSZ) in *. set (nb := mmap_len l) in *.
  set (aw := Z_to_bv 64 a). set (nw := Z_to_bv 64 PGSZ).
  assert (Hab : b + PGSZ <= a /\ a + PGSZ <= b + nb) by (subst a; unfold PGSZ in *; nia).
  assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; unfold PGSZ in *; lia).
  assert (Un : bv_unsigned nw = PGSZ) by (subst nw; apply unsigned_lit; unfold PGSZ; lia).
  assert (Hamod : a mod 4096 = 0). { subst a. unfold PGSZ in *. rewrite Z.add_mod, A3, Z.mod_mul by lia. reflexivity. }
  assert (Hcn : map_contains (vm_noaccess (m_vmmaps mo)) aw nw = true).
  { destruct (Ana (1 + k) ltac:(lia) ltac:(lia)) as (e & He & Hel & Heh). unfold map_contains. apply existsb_exists. exists e. split; [exact He|].
    rewrite Ua, Un. unfold elo, ehi in Hel, Heh. subst a. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
  assert (Hcm : map_contains (vm_maps (m_vmmaps mo)) aw nw = true).
  { unfold map_contains. apply existsb_exists. exists (went b nb). split; [exact A5|]. rewrite Ua, Un. unfold elo, ehi in B5, B6. rewrite B5.
    replace (bv_unsigned (fst (went b nb)) + bv_unsigned (snd (went b nb))) with (b + nb) by (symmetry; exact B6).
    rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
  destruct (nstep_dec_mprotect a PGSZ mo rsp mo' evs ltac:(unfold PGSZ in *; lia) ltac:(unfold PGSZ; lia) ltac:(rewrite page_size_eq; exact Hamod)
              ltac:(change (mmap_len PGSZ) with PGSZ; unfold PGSZ in *; lia)
              ltac:(change (mmap_len PGSZ) with PGSZ; exact Hcn) ltac:(change (mmap_len PGSZ) with PGSZ; exact Hcm) Hst) as (_ & _ & x & _ & Hx).
  assert (Emaps : vm_maps (m_vmmaps mo') = vm_maps (m_vmmaps mo)).
  { destruct x as [e|[|]]; [destruct Hx as [_ ->]; reflexivity| destruct Hx as (_ & ->); unfold mprotect_model_next; rewrite m_vmmaps_with_vmmaps; reflexivity| destruct Hx]. }
  apply (LI_same_vm L _ mo); [exact HL| exact Emaps| |]; unfold event_post; destruct ((z =? 0) || (z =? TWO64 - ENOSYS)); rewrite ?gm_bump; reflexivity.
Qed.

End WithCeil.
End LB_Kernel.

(* [comment removed for export] *)
Module LB_Embed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad MSafe STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Logic. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MSafe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KLink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KStep__Spec.KStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Logic OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KStep__Spec.LB_Kernel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Export LB_Quant.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section WithCeil.
Context {CE : CEIL}.
#[using="Type"] Lemma vis_flat_L {A} B n (k : resp -> itree node (exc A)) mo (Q : A -> Model -> Prop) (R : A -> Model -> Prop) :
  (forall rsp, match k rsp with Ret _ => True | Vis _ _ => False end) ->
  etwf (Vis n k) mo Q ->
  (forall rsp mo' evs a, nstep n mo rsp mo' evs -> k rsp = Ret (Ok a) -> Q a mo' -> R a mo' /\ live mo' <= B) ->
  etwl B (Vis n k) mo (fun a mo' => Q a mo' /\ R a mo').
Proof.
  intros Hf H HR. cbn in H |- *. destruct H as [_ Hk]. intros rsp mo' evs Hst. specialize (Hk rsp mo' evs Hst). specialize (Hf rsp).
  destruct (k rsp) as [[|a]|n' k'] eqn:Ek; cbn in Hk |- *; [destruct Hk| | destruct Hf].
  destruct (HR rsp mo' evs a Hst Ek Hk) as [HRa HB]. auto.
Qed.


(* [comment removed for export] *)

Section Embed.
Context {St : Type} {AS : AllocSt St}.

Ltac flat_shape W :=
  unfold mbind, msys, mret, mget, mupd, enode, ebind in W |- *; cbn [ITree.bind fst snd] in W |- *.

(* [comment removed for export] *)
#[using="Type"] Lemma twl_monoB {R} B B' (t : itree node R) : B <= B' -> forall mo (P : R -> Model -> Prop), twl B t mo P -> twl B' t mo P.
Proof.
  intros HB. induction t as [r|n k IH]; intros mo P H; cbn in *; [exact H|].
  intros rsp mo' evs Hst. destruct (H rsp mo' evs Hst) as [H1 H2]. split; [lia| apply IH; exact H2].
Qed.
#[using="Type"] Lemma mspecL_monoB {A} B B' (P : assn St) (m : Monad.M St A) (Q : A -> assn St) : B <= B' -> mspecL B P m Q -> mspecL B' P m Q.
Proof. intros HB H s mo HP. unfold etwl. eapply twl_monoB; [exact HB| exact (H s mo HP)]. Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem ev_step_L B L e G s0 : frame_ok G -> event_pre L e ->
  mspecL (B + PINB) (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ LI L mo /\ G s mo /\ BOUND L e B) (ev_step e)
          (fun z s mo => ev_step_post L e G s0 z s mo /\ LI (event_post L e z) mo).
Proof.
  intros HG Hpre s mo (-> & HK & HLI & HGs & HB).
  pose proof (ev_step_spec L e G s0 HG Hpre s0 mo (conj eq_refl (conj HK HGs))) as W.
  assert (FIN : forall z mo', answer_ok L e z = true -> LI (event_post L e z) mo' -> live mo' <= B + PINB).
  { intros z mo' Ha HL'. apply LI_elim in HL'. unfold live. pose proof (BOUND_post _ _ _ HB z Ha). lia. }
  destruct e as [req|addr len prot flags|addr len|addr len prot|? ? ?|?|ma mol mnl]; cbn [event_pre] in Hpre; try contradiction; try (destruct Hpre as [[] ?]).
  - (* [comment removed for export] *)
    unfold ev_step in W |- *.
    destruct (Z.eqb_spec req 0) as [->|NZ].
    + flat_shape W. eapply vis_flat_L; [| exact W|].
      { intros rsp. destruct (dec_brk0 rsp); reflexivity. }
      intros rsp mo' evs [z s'] Hst Ek [Hans HP]. cbn [fst snd] in *.
      destruct (dec_brk0 rsp) as [x|] eqn:Hd; cbn in Ek; [| discriminate]. assert (Ez : z = x) by congruence. subst x.
      destruct Hpre as [[_ Hph]|[(cur & Hph & E)|(b & l & Hph & Hreg & E)]].
      2:{ exfalso. pose proof (kl_phase _ _ _ HK) as P. rewrite Hph in P. destruct P as (Ecur & _). pose proof (kl_start _ _ _ HK) as (S1 & _). pose proof (round_up_pg_ge cur). unfold PGSZ in *. lia. }
      2:{ exfalso. pose proof (kl_brkreg _ _ _ HK b l Hreg) as (R1 & R2 & R3 & _). unfold PGSZ in *. lia. }
      pose proof (li_brk0 L (ps_brk s0) mo rsp mo' evs z HK HLI Hph Hst) as HL'.
      change (event_post L (EBrk 0) z) with (set_brkph (BPQueried z) L). split; [exact HL'| exact (FIN z mo' Hans HL')].
    + flat_shape W. eapply vis_flat_L; [| exact W|].
      { intros rsp. destruct (dec_brk (ps_brk s0) req rsp) as [[|]|]; reflexivity. }
      intros rsp mo' evs [z s'] Hst Ek [Hans HP]. cbn [fst snd] in *.
      destruct (dec_brk (ps_brk s0) req rsp) as [x|] eqn:Hd; cbn in Ek; [| discriminate].
      assert (Ez : z = match x with BrkGrown => req | BrkSame => ps_brk s0 end) by (destruct x; cbn in Ek; congruence).
      destruct Hpre as [[E _]|Hpre]; [exfalso; exact (NZ E)|].
      pose proof (li_brk_grow L (ps_brk s0) mo rsp mo' evs req x HK HLI Hpre Hst Hd) as HL'. rewrite <- Ez in HL'.
      split; [exact HL'| exact (FIN z mo' Hans HL')].
  - (* [comment removed for export] *)
    unfold ev_step in W |- *.
    destruct Hpre as [(Hq & -> & -> & Hprot & Hlen)|(cur & Hph & -> & -> & -> & ->)].
    + change (negb (Z.land MAPF MAP_FIXED_Z =? 0)) with false in *. cbn iota in W |- *.
      destruct Hprot as [-> | ->].
      * change (PROT_NONE =? 0) with true in *. cbn iota in W |- *. flat_shape W. eapply vis_flat_L; [| exact W|].
        { intros rsp. destruct (dec_mmap_none len [] rsp); reflexivity. }
        intros rsp mo' evs [z s'] Hst Ek [Hans HP]. cbn [fst snd] in *.
        destruct (dec_mmap_none len [] rsp) as [x|] eqn:Hd; cbn in Ek; [| discriminate].
        assert (Ez : z = mm_val x) by (destruct x; cbn; congruence). subst z.
        pose proof (li_mmap_none L (ps_brk s0) mo rsp mo' evs len x HK HLI Hlen Hst Hd) as HL'.
        split; [exact HL'| exact (FIN _ mo' Hans HL')].
      * change (PROT_RW =? 0) with false in *. cbn iota in W |- *. flat_shape W. eapply vis_flat_L; [| exact W|].
        { intros rsp. destruct (dec_mmap len [] rsp); reflexivity. }
        intros rsp mo' evs [z s'] Hst Ek [Hans HP]. cbn [fst snd] in *.
        destruct (dec_mmap len [] rsp) as [x|] eqn:Hd; cbn in Ek; [| discriminate].
        assert (Ez : z = mm_val x) by (destruct x; cbn; congruence). subst z.
        pose proof (li_mmap_rw L (ps_brk s0) mo rsp mo' evs len x HK HLI Hlen Hst Hd) as HL'.
        split; [exact HL'| exact (FIN _ mo' Hans HL')].
    + change (negb (Z.land MAPFX MAP_FIXED_Z =? 0)) with true in *. cbn iota in W |- *. flat_shape W. eapply vis_flat_L; [| exact W|].
      { intros rsp. destruct (dec_mmap_fixed (round_up_pg cur) PGSZ rsp); reflexivity. }
      intros rsp mo' evs [z s'] Hst Ek [Hans HP]. cbn [fst snd] in *.
      pose proof (li_mmap_fixed L (ps_brk s0) mo rsp mo' evs cur z HK HLI Hph Hst) as HL'.
      split; [exact HL'| exact (FIN _ mo' Hans HL')].
  - (* [comment removed for export] *)
    unfold ev_step in W |- *. destruct Hpre as (Hq & l0 & Hin & Hlen). flat_shape W. eapply vis_flat_L; [| exact W|].
    { intros rsp. destruct (dec_munmap addr len rsp); reflexivity. }
    intros rsp mo' evs [z s'] Hst Ek [Hans HP]. cbn [fst snd] in *.
    pose proof (li_munmap L (ps_brk s0) mo rsp mo' evs addr l0 len z HK HLI Hin Hlen Hst) as HL'.
    split; [exact HL'| exact (FIN _ mo' Hans HL')].
  - (* [comment removed for export] *)
    unfold ev_step in W |- *. destruct Hpre as (Hq & -> & -> & b & l & k & Hin & -> & Hk). flat_shape W. eapply vis_flat_L; [| exact W|].
    { intros rsp. destruct (dec_mprotect_rw (b + (1 + k) * PGSZ) PGSZ rsp); reflexivity. }
    intros rsp mo' evs [z s'] Hst Ek [Hans HP]. cbn [fst snd] in *.
    pose proof (li_mprotect L (ps_brk s0) mo rsp mo' evs b l k z HK HLI Hin Hk Hst) as HL'.
    split; [exact HL'| exact (FIN _ mo' Hans HL')].
  - (* [comment removed for export] *)
    unfold ev_step in W |- *. destruct Hpre as (Hq & (l0 & Hin & Hol) & Hnl & Hal & Hne).
    rewrite round_up_pg_eq in Hol. fold (mmap_len l0) in Hol. subst mol.
    flat_shape W. eapply vis_flat_L; [| exact W|].
    { intros rsp. destruct (dec_mremap ma (mmap_len l0) mnl [] [] rsp); reflexivity. }
    intros rsp mo' evs [z s'] Hst Ek [Hans HP]. cbn [fst snd] in *.
    destruct (dec_mremap ma (mmap_len l0) mnl [] [] rsp) as [x|] eqn:Hd; cbn in Ek; [| discriminate].
    assert (Ez : z = mremap_val ma x) by congruence. subst z.
    pose proof (li_mremap L (ps_brk s0) mo rsp mo' evs ma l0 mnl x HK HLI Hin Hnl Hal Hne Hst Hd) as HL'.
    split; [exact HL'| exact (FIN _ mo' Hans HL')].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Theorem membedL {R} B (t : stree ev Z R) : forall (Post : mled -> R -> Prop) (G : St -> Model -> Prop) L s0,
  frame_ok G -> qtree B L t Post ->
  mspecL (B + PINB) (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ LI L mo /\ G s mo) (membed t)
         (fun r s mo => exists L', cpath L t L' r /\ Post L' r /\ KL L' (ps_brk s) mo /\ LI L' mo /\ G s mo
                        /\ ps_m s = ps_m s0 /\ ps_rest s = ps_rest s0).
Proof.
  induction t as [r|e k IH]; intros Post G L s0 HG Hq.
  - cbn [membed]. apply mspecL_ret. intros s mo (-> & HK & HL & HGs). exists L. split; [constructor|]. cbn in Hq. split; [exact Hq|]. split; [exact HK|]. split; [exact HL|]. split; [exact HGs|]. auto.
  - cbn [membed]. cbn in Hq. destruct Hq as (Hpre & HB & Hk).
    eapply mspecL_bind.
    { eapply mspecL_pre; [apply (ev_step_L B L e G s0 HG Hpre)|]. intros s mo (-> & HK & HL & HGs). split; [reflexivity|]. split; [exact HK|]. split; [exact HL|]. split; [exact HGs| exact HB]. }
    intros z. apply mspecL_pointwise. intros s1 mo1 [(Hans & HK1 & HG1 & Hm & Hx1) HL1].
    eapply mspecL_conseq; [apply (IH z Post G (event_post L e z) s1 HG (Hk z Hans))| |].
    + intros s mo [-> ->]. auto.
    + intros r s mo (L' & Hp & HP & HK & HL' & HG' & Hm' & Hx'). exists L'. split; [econstructor; eauto|].
      split; [exact HP|]. split; [exact HK|]. split; [exact HL'|]. split; [exact HG'|]. repeat split; congruence.
Qed.

End Embed.

End WithCeil.
End LB_Embed.
