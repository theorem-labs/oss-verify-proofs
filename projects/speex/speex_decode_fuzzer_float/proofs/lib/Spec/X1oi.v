(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1c5 X1by X1bs X1c2 X1bn X1c7.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1qs X1ra X1qu X1r3 X1r4 X1og X1oh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require X1pi X1q7.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

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

Lemma region_free_app_l : forall l1 l2 a n, region_free (l1 ++ l2) a n = true -> region_free l1 a n = true.
Proof.
induction l1 as [|[e sz] l1 IH]; intros l2 a n H; [reflexivity|]. cbn in H |- *. apply andb_prop in H as [H1 H].
rewrite H1. cbn. eapply IH. exact H.
Qed.

Lemma region_free_shrink : forall maps a n n', region_free maps a (Z_to_bv 64 n') = true ->
0 <= n <= n' -> n' < 2^64 -> region_free maps a (Z_to_bv 64 n) = true.
Proof.
intros maps a n n' H Hn Hn'. apply region_free_intro. intros b sz Hin.
pose proof (region_free_In _ _ _ _ _ H Hin) as D. unfold iv_overlap in *.
rewrite !unsigned_lit in * by lia.
apply Bool.andb_false_iff. apply Bool.andb_false_iff in D. destruct D as [D|D]; [left; exact D| right].
apply Z.ltb_ge. apply Z.ltb_ge in D. lia.
Qed.

Lemma region_free_disj : forall maps a n e, region_free maps a n = true -> In e maps ->
bv_unsigned a + bv_unsigned n <= elo e \/ ehi e <= bv_unsigned a.
Proof.
intros maps a n [e sz] H Hin. unfold elo, ehi. cbn. pose proof (region_free_In _ _ _ _ _ H Hin) as X.
unfold iv_overlap in X. apply andb_false_iff in X. destruct X as [X|X]; apply Z.ltb_ge in X; lia.
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
lo < hi -> y <= 2^64 ->
bv_unsigned a <= x -> x < y -> y <= bv_unsigned a + bv_unsigned sz ->
(y <= lo \/ hi <= x) ->
exists e, In e (iv_subtract a sz lo hi) /\ elo e <= x /\ y <= ehi e.
Proof.
intros a sz lo hi x y Hlh Hy64 Hax Hxy Hy Hd. unfold iv_subtract.
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

Lemma iv_subtract_pwdisj : forall a sz lo hi, lo < hi -> bv_unsigned a + bv_unsigned sz <= 2^64 -> pwdisj (iv_subtract a sz lo hi).
Proof.
intros a sz lo hi Hlh Hwf. unfold iv_subtract.
pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 sz). unfold bv_modulus in *.
destruct (Z.ltb_spec (bv_unsigned a) lo); destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); cbn [app].
- constructor; [|constructor; [intros e' []| constructor]]. intros e' [<-|[]].
unfold edisj, elo, ehi; cbn. rewrite !unsigned_lit by lia. left. lia.
- constructor; [intros e' []| constructor].
- constructor; [intros e' []| constructor].
- constructor.
Qed.

Lemma vmwf_subtract : forall maps lo hi, lo < hi -> vmwf maps -> vmwf (maps_subtract maps lo hi).
Proof.
induction maps as [|[a sz] maps IH]; intros lo hi Hlh [Hb Hp]; [split; [intros e []| constructor]|].
inversion Hp; subst. assert (Hwf' : vmwf maps) by (split; [intros e He; apply Hb; right; exact He| assumption]).
specialize (IH lo hi Hlh Hwf'). destruct IH as [IHb IHp].
assert (Ha : elo (a, sz) < ehi (a, sz) <= 2^64) by (apply Hb; left; reflexivity). unfold elo, ehi in Ha; cbn in Ha.
cbn. split.
- intros e Hin. apply in_app_or in Hin as [Hin|Hin]; [|apply IHb; exact Hin].
pose proof (iv_subtract_sub a sz lo hi e ltac:(lia) ltac:(lia) Hin). lia.
- apply pwdisj_app; [apply iv_subtract_pwdisj; lia| exact IHp|].
intros e e' He He'. pose proof (iv_subtract_sub a sz lo hi e ltac:(lia) ltac:(lia) He) as S1.
destruct (maps_subtract_In _ _ _ _ He') as (e0 & H0 & H0').
assert (W0 : elo e0 < ehi e0 <= 2^64) by (apply Hb; right; exact H0). destruct e0 as [a0 s0]. unfold elo, ehi in W0; cbn in W0.
pose proof (iv_subtract_sub a0 s0 lo hi e' ltac:(lia) ltac:(lia) H0') as S2.
pose proof (H1 _ H0) as D. unfold edisj, elo, ehi in *. cbn in *. lia.
Qed.

Lemma wcov_mono : forall maps maps' lo hi, (forall e, In e maps -> In e maps') -> wcov maps lo hi -> wcov maps' lo hi.
Proof. intros maps maps' lo hi Hs Hc x Hx. destruct (Hc x Hx) as (e & He & Hr). exists e. auto. Qed.

Lemma elo_pair : forall a n, elo (a, n) = bv_unsigned a. Proof. reflexivity. Qed.
Lemma ehi_pair : forall a n, ehi (a, n) = bv_unsigned a + bv_unsigned n. Proof. reflexivity. Qed.

Lemma brk_grants_grow : forall h req,
let b := bv_unsigned (vm_brk h) in
0 < b -> b < req < 2^64 ->
brk_grants (Z_to_bv 64 req) (Z_to_bv 64 req) (vm_brk h) = [(vm_brk h, Z_to_bv 64 (req - b))].
Proof.
intros h req b Hb Hreq. unfold brk_grants, brk_is_grow. rewrite w_is0_lit by lia.
replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
fold b. replace (0 <? b) with true by (symmetry; apply Z.ltb_lt; lia).
rewrite unsigned_lit by lia. replace (b <? req) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb andb].
f_equal. f_equal. apply bv_eq. rewrite bv_sub_unsigned, !unsigned_lit by lia. fold b.
apply bv_wrap_small. unfold bv_modulus. lia.
Qed.

Lemma nstep_brk_grown_facts : forall req mo rsp mo' evs,
let h := m_vmmaps mo in let b := bv_unsigned (vm_brk h) in
0 < b -> bv_unsigned (vm_start_brk h) <= b -> b < req < 2^64 -> b mod 4096 = 0 -> req mod 4096 = 0 ->
nstep (NBrk req) mo rsp mo' evs -> dec_brk b req rsp = Some BrkGrown ->
req <= alloc_top h /\ region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 b) (Z_to_bv 64 (req - b)) = true.

Proof.
intros req mo rsp mo' evs h b Hb Hsb Hreq Hba Hra Hst Hdec.
apply (proj1 (nstep_brk_iff _ _ _ _ _)) in Hst as [_ (r & Hr & _ & -> & _)].
unfold brk_r_ok in Hr. cbv zeta in Hr. fold h in Hr. rewrite w_is0_lit in Hr by lia.
replace (req =? 0) with false in Hr by (symmetry; apply Z.eqb_neq; lia).
unfold min_brk in Hr. rewrite unsigned_lit in Hr by lia.
replace (req <? bv_unsigned (vm_start_brk h)) with false in Hr by (symmetry; apply Z.ltb_ge; lia).
fold b in Hr. replace (req <? b) with false in Hr by (symmetry; apply Z.ltb_ge; lia).
cbn [orb] in Hr. apply andb_prop in Hr as [Hr Hgo].
assert (Hr' : r = Z_to_bv 64 req \/ r = vm_brk h).
{ apply orb_prop in Hr as [E|E]; apply bv_eqb_eq in E; auto. }
assert (Hus : brk_unmaps r (vm_brk h) = []).
{ unfold brk_unmaps. cbv zeta. rewrite brk_page_range_empty; [destruct (0 <? _)%Z; reflexivity|].
apply page_round_up_Z_mono. destruct Hr' as [-> | ->]; [rewrite unsigned_lit by lia|]; lia. }

destruct Hr' as [-> | ->].
2:{ exfalso. unfold dec_brk in Hdec. fold h in Hdec. rewrite Hus in Hdec. fold b in Hdec. rewrite Z.eqb_refl in Hdec.
unfold brk_zeros, brk_is_grow in Hdec. rewrite Z.ltb_irrefl, !andb_false_r in Hdec. cbn in Hdec. discriminate Hdec. }
clear Hdec Hr.
unfold brk_grow_ok in Hgo. fold h in Hgo. fold b in Hgo. rewrite unsigned_lit in Hgo by lia.
replace (0 <? b) with true in Hgo by (symmetry; apply Z.ltb_lt; lia).
replace (b <? req) with true in Hgo by (symmetry; apply Z.ltb_lt; lia). cbn [andb] in Hgo.
unfold page_round_up_Z in Hgo. rewrite page_size_eq in Hgo.
replace ((b + 4096 - 1) / 4096 * 4096) with b in Hgo.
2:{ pose proof (Z_div_mod_eq_full b 4096). pose proof (Z_div_mod_eq_full (b+4096-1) 4096). pose proof (Z.mod_pos_bound (b+4096-1) 4096). nia. }
replace ((req + 4096 - 1) / 4096 * 4096) with req in Hgo.
2:{ pose proof (Z_div_mod_eq_full req 4096). pose proof (Z_div_mod_eq_full (req+4096-1) 4096). pose proof (Z.mod_pos_bound (req+4096-1) 4096). nia. }
replace (b <? req) with true in Hgo by (symmetry; apply Z.ltb_lt; lia).
apply andb_prop in Hgo as [Hgo _]. apply andb_prop in Hgo as [H1 H2]. apply Z.leb_le in H1. split; [exact H1|].
eapply region_free_shrink; [exact H2| lia|]. pose proof (alloc_top_room h). lia.
Qed.

Ltac kl_open HK := destruct HK as [Kminv Khalt Kceil Kwf Kresv Krt Kstart Kgr Kme Kdis Kreg Kph].

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
intros L pbrk mo mo' K Hmi Hh H1 H2 H3 H4 H5 H6. kl_open K; constructor; rewrite ?H1, ?H2, ?H3, ?H4, ?H5; auto.
all: try (unfold alloc_top in *; rewrite ?H6; exact Kceil).
Qed.

Lemma KL_vmmaps_eq : forall L pbrk mo mo',
KL L pbrk mo -> minv mo' -> m_halted mo' = None -> m_vmmaps mo' = m_vmmaps mo -> KL L pbrk mo'.
Proof. intros L pbrk mo mo' K Hmi Hh E. eapply KL_vm_eq; eauto; rewrite E; reflexivity. Qed.

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

Section OK.
Context {ok : node -> resp -> Prop}.
Local Notation mspec := (mspecG ok).

Lemma ev_brk0_ok : forall L G s0, frame_ok G -> ld_brk L = BPUntried ->
mspec (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ G s mo)
(r <- msys (NBrk 0) dec_brk0 ;; mupd (set_brk_ps r) ;;; mret r)
(ev_step_post L (EBrk 0) G s0).
Proof.
intros L G s0 HG Hph.
eapply mspec_bind.
{ apply (mspec_sys (NBrk 0) dec_brk0 _ (fun r s mo => s = s0 /\ G s mo /\ brk0_answer_ok r = true /\ KL (set_brkph (BPQueried r) L) r mo)).
intros s mo (-> & HK & HGs). pose proof (ld_ceil_lt _ _ _ HK) as HcL. split; [apply nsafe_brk|].
intros rsp mo' evs Hst.
pose proof (minv_preserved (NBrk 0) _ _ _ _ I (kl_minv _ _ _ HK) (kl_halt _ _ _ HK) Hst) as [Hh' Hmi'].
pose proof (nstep_dec_brk0 _ _ _ _ Hst) as (_ & Hdec & Hvo & Hvm).
exists (bv_unsigned (vm_brk (m_vmmaps mo))). split; [exact Hdec|].
assert (HK' : KL L (ps_brk s0) mo') by (eapply KL_vmmaps_eq; eauto).
pose proof (kl_phase _ _ _ HK') as Kph. rewrite Hph in Kph. destruct Kph as [Ebrk Ereg].
pose proof (kl_start _ _ _ HK') as (S1 & S2 & S3 & S4).
rewrite <- Hvm.
splits.
- reflexivity.
- eapply HG; [reflexivity|reflexivity| exact Hvo| exact HGs].
- unfold brk0_answer_ok. rewrite Ebrk. pose proof (bv_unsigned_in_range 64 (vm_start_brk (m_vmmaps mo'))) as R. unfold bv_modulus in R.
unfold TWO64. rewrite (proj2 (Z.ltb_lt 0 _)) by lia. rewrite S2, Z.eqb_refl. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
- eapply KL_rephase; [exact HK'|]. cbn [phase_inv]. rewrite Ebrk. splits; auto. }
intros r. cbn beta. eapply mspec_bind.
{ apply mspec_upd. }
intros []. apply mspec_ret. intros s mo (s1 & -> & -> & HGs & Hans & HK). unfold ev_step_post. cbn [ps_brk set_brk_ps ps_m ps_fa ps_so answer_ok event_post Z.eqb].
splits; auto. eapply (HG s0); [reflexivity|reflexivity| apply vm_only_refl| exact HGs].
Qed.

Lemma mspec_get_bind_eq {St A} (s0 : St) (P : assn St) (f : St -> X1qx.M St A) Q :
mspec (fun s mo => s = s0 /\ P s mo) (f s0) Q -> mspec (fun s mo => s = s0 /\ P s mo) (x <- mget ;; f x) Q.
Proof. intros H s mo [-> HP]. unfold mbind, mget. cbn. apply H. auto. Qed.

Lemma went_In_bounds : forall L pbrk mo b l, KL L pbrk mo ->
(In (b, l) (ld_groups L) \/ exists k, In (b, l, k) (ld_metas L)) ->
0 < b /\ 0 < mmap_len l /\ b + mmap_len l <= ld_ceil L /\ In (went b (mmap_len l)) (vm_maps (m_vmmaps mo))
/\ elo (went b (mmap_len l)) = b /\ ehi (went b (mmap_len l)) = b + mmap_len l.
Proof.
intros L pbrk mo b l K Hin. pose proof (ld_ceil_lt _ _ _ K).
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
intros L pbrk mo lo len HK h Hlo Hlen Hceil Hrf Hbrk. pose proof (ld_ceil_lt _ _ _ HK) as Hcl.
assert (Ulo : bv_unsigned (Z_to_bv 64 lo) = lo) by (apply unsigned_lit; lia).
assert (Ulen : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
pose proof (region_free_app_r _ _ _ _ Hrf) as Hrfm.
unfold lbrk_pages_ok. rewrite (proj2 (Z.ltb_lt 0 lo)) by lia. rewrite (proj2 (Z.leb_le _ _) Hceil). cbn [andb].
unfold ranges_free. apply forallb_forall. intros [b0 m0] Hin. cbn [fst snd]. unfold iv_disjoint.
enough (lo + len <= b0 \/ b0 + m0 <= lo) as D.
{ destruct D as [D|D]; [rewrite (proj2 (Z.leb_le _ _) D); reflexivity| rewrite (proj2 (Z.leb_le _ _) D); apply orb_true_r]. }
apply In_lranges in Hin as [H|[(b1 & l1 & H & E)|[(b1 & l1 & k & H & E)|(b1 & l1 & H & E)]]].
- rewrite (kl_resv _ _ _ HK) in H. apply in_map_iff in H as ([e sz] & E & H). unfold wwZ in E. cbn [fst snd] in E. injection E as <- <-.
pose proof (region_free_disj _ _ _ _ Hrf (in_or_app _ _ _ (or_introl H))) as D. rewrite Ulo, Ulen in D. unfold elo, ehi in D. cbn in D. lia.
- injection E as -> ->. pose proof (went_In_bounds _ _ _ b1 l1 HK (or_introl H)) as (B1 & B2 & B3 & B4 & B5 & B6).
pose proof (region_free_disj _ _ _ _ Hrfm B4) as D. rewrite B5, B6, Ulo, Ulen in D. rewrite round_up_pg_eq. fold (mmap_len l1). lia.
- injection E as -> ->. pose proof (went_In_bounds _ _ _ b1 l1 HK (or_intror (ex_intro _ k H))) as (B1 & B2 & B3 & B4 & B5 & B6).
pose proof (region_free_disj _ _ _ _ Hrfm B4) as D. rewrite B5, B6, Ulo, Ulen in D. rewrite round_up_pg_eq. fold (mmap_len l1). lia.
- injection E as -> ->. destruct (Hbrk b1 l1 H) as [Al D]. rewrite round_up_pg_aligned by (unfold PGSZ in Al; exact Al). lia.
Qed.

Lemma ev_brk_grow1_ok : forall L G s0 cur, frame_ok G -> ld_brk L = BPQueried cur ->
let req := round_up_pg cur + 2 * PGSZ in
mspec (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ G s mo)
(s <- mget ;; a <- msys (NBrk req) (dec_brk (ps_brk s) req) ;;
match a with BrkGrown => mupd (set_brk_ps req) ;;; mret req | BrkSame => mret (ps_brk s) end)
(ev_step_post L (EBrk req) G s0).
Proof.
intros L G s0 cur HG Hph req. pose proof alloc_ceiling_hi_lt as Hcl.
apply mspec_get_bind_eq.
eapply mspec_bind.
{ apply (mspec_sys (NBrk req) (dec_brk (ps_brk s0) req) _
(fun a s mo => s = s0 /\ G s mo /\ (req <> cur /\ 0 < req) /\ ps_brk s0 = cur /\
match a with
| BrkGrown => KL (set_brkph (BPGuard cur) L) req mo /\ lbrk_pages_ok L (round_up_pg cur) (2 * PGSZ) = true
| BrkSame => KL (set_brkph BPDead L) cur mo
end)).
intros s mo (-> & HK & HGs). pose proof (ld_ceil_lt _ _ _ HK) as HcL. split; [apply nsafe_brk|].
intros rsp mo' evs Hst.
pose proof (minv_preserved (NBrk req) _ _ _ _ I (kl_minv _ _ _ HK) (kl_halt _ _ _ HK) Hst) as [Hh' Hmi'].
pose proof (kl_phase _ _ _ HK) as Kph. rewrite Hph in Kph. destruct Kph as (Ecur & Ebrk & Epbrk & Ereg).
pose proof (kl_start _ _ _ HK) as (S1 & S2 & S3 & S4).
assert (Hreq : req = cur + 2 * PGSZ). { subst req. rewrite round_up_pg_aligned; [reflexivity|]. rewrite Ecur. exact S2. }
pose proof (nstep_dec_brk req mo rsp mo' evs ltac:(lia) ltac:(lia) ltac:(unfold PGSZ in *; lia) Hst) as (_ & Hvo & a & Hdec & Ha).
set (h := m_vmmaps mo) in *.
exists a. rewrite Epbrk, <- Ebrk. split; [exact Hdec|].
split; [reflexivity|]. split; [eapply HG; [reflexivity|reflexivity| exact Hvo| exact HGs]|].
split; [unfold PGSZ in *; lia|]. split; [reflexivity|].
destruct a.
-
destruct Ha as [Hlt Evm].
assert (F1 : 0 < bv_unsigned (vm_brk h)) by lia.
assert (F2 : bv_unsigned (vm_start_brk h) <= bv_unsigned (vm_brk h)) by lia.
assert (F3 : bv_unsigned (vm_brk h) < req < 2^64) by (unfold PGSZ in *; lia).
assert (F4 : bv_unsigned (vm_brk h) mod 4096 = 0) by (rewrite Ebrk, Ecur; exact S2).
assert (F5 : req mod 4096 = 0) by (rewrite Hreq, Ecur; unfold PGSZ in *; rewrite Z.add_mod, S2 by lia; reflexivity).
pose proof (nstep_brk_grown_facts req mo rsp mo' evs F1 F2 F3 F4 F5 Hst Hdec) as [Hceil Hrf].
fold h in Hrf. rewrite Z_to_bv_bv_unsigned in Hrf.
assert (HPG : lbrk_pages_ok L (round_up_pg (bv_unsigned (vm_brk h))) (2 * PGSZ) = true).
{ rewrite round_up_pg_aligned by (rewrite Ebrk, Ecur; unfold PGSZ in S2; exact S2).
pose proof (proj1 (kl_ceil _ _ _ HK)) as KC; pose proof KC as KC2; fold h in KC2.
apply (KL_lbrk_pages_ok L (ps_brk s0) mo (bv_unsigned (vm_brk h)) (2 * PGSZ) HK); [lia| unfold PGSZ; lia| lia| | intros b l Hb; rewrite Ereg in Hb; discriminate].
rewrite Z_to_bv_bv_unsigned.
replace (Z_to_bv 64 (2 * PGSZ)) with (Z_to_bv 64 (req - bv_unsigned (vm_brk h))) by (f_equal; lia). exact Hrf. }
assert (Hn : bv_unsigned (Z_to_bv 64 (req - bv_unsigned (vm_brk h))) = 2 * PGSZ) by (rewrite unsigned_lit; unfold PGSZ in *; lia).
rewrite (brk_grants_grow h req ltac:(lia) ltac:(unfold PGSZ in *; lia)) in Evm. cbn [app] in Evm.
split; [|exact HPG].
kl_open HK. constructor; rewrite ?Evm; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk set_brkph ld_ceil ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; auto; try (kl_ceil_tac Kceil).
+ apply vmwf_cons; [exact Kwf| rewrite Hn; unfold PGSZ in *; lia| eapply region_free_app_r; exact Hrf].
+ rewrite unsigned_lit by (unfold PGSZ in *; lia). splits; try lia; auto.
+ intros b l Hin. specialize (Kgr b l Hin). unfold brk_disj in *. cbn. intuition auto with datatypes.
+ intros b l k Hin. specialize (Kme b l k Hin). unfold brk_disj in *. cbn. intuition auto with datatypes.
+ intros b l Hb. rewrite Ereg in Hb. discriminate.
+ rewrite unsigned_lit by (unfold PGSZ in *; lia). splits; auto; try lia.
* exists (vm_brk h, Z_to_bv 64 (req - bv_unsigned (vm_brk h))). split; [left; reflexivity|]. rewrite elo_pair, ehi_pair, Hn. lia.
* intros b l Hin. pose proof (went_In_bounds _ _ _ b l (mkKL _ _ _ Kminv Khalt Kceil Kwf Kresv Krt Kstart Kgr Kme Kdis Kreg Kph) (or_introl Hin)) as (B1 & B2 & B3 & B4 & B5 & B6).
pose proof (region_free_disj _ _ _ _ (region_free_app_r _ _ _ _ Hrf) B4) as D. rewrite B5, B6, Hn in D. lia.
* intros b l k Hin. pose proof (went_In_bounds _ _ _ b l (mkKL _ _ _ Kminv Khalt Kceil Kwf Kresv Krt Kstart Kgr Kme Kdis Kreg Kph) (or_intror (ex_intro _ k Hin))) as (B1 & B2 & B3 & B4 & B5 & B6).
pose proof (region_free_disj _ _ _ _ (region_free_app_r _ _ _ _ Hrf) B4) as D. rewrite B5, B6, Hn in D. lia.
-
apply KL_dead with (pbrk := ps_brk s0). eapply KL_vmmaps_eq; [exact HK| exact Hmi'| exact Hh'| exact Ha]. }
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
intros L G s0 b l HG Hph Ereg req. pose proof alloc_ceiling_hi_lt as Hcl.
apply mspec_get_bind_eq.
eapply mspec_bind.
{ apply (mspec_sys (NBrk req) (dec_brk (ps_brk s0) req) _
(fun a s mo => s = s0 /\ G s mo /\ (req <> b + l /\ 0 < req) /\ ps_brk s0 = b + l /\
match a with
| BrkGrown => KL (set_brkreg (Some (b, l + PGSZ)) L) req mo /\ lbrk_pages_ok L (b + l) PGSZ = true
| BrkSame => KL (set_brkph BPDead L) (b + l) mo
end)).
intros s mo (-> & HK & HGs). pose proof (ld_ceil_lt _ _ _ HK) as HcL. split; [apply nsafe_brk|].
intros rsp mo' evs Hst.
pose proof (minv_preserved (NBrk req) _ _ _ _ I (kl_minv _ _ _ HK) (kl_halt _ _ _ HK) Hst) as [Hh' Hmi'].
pose proof (kl_phase _ _ _ HK) as Kph. rewrite Hph in Kph. destruct Kph as (b' & l' & Ereg' & Ebrk & Epbrk).
rewrite Ereg in Ereg'. injection Ereg' as <- <-.
pose proof (kl_brkreg _ _ _ HK b l Ereg) as (R1 & R2 & R3 & R4 & R5 & Rcov).
pose proof (kl_start _ _ _ HK) as (S1 & S2 & S3 & S4).
pose proof (nstep_dec_brk req mo rsp mo' evs ltac:(lia) ltac:(lia) ltac:(unfold PGSZ in *; lia) Hst) as (_ & Hvo & a & Hdec & Ha).
set (h := m_vmmaps mo) in *.
exists a. rewrite Epbrk, <- Ebrk. split; [exact Hdec|].
split; [reflexivity|]. split; [eapply HG; [reflexivity|reflexivity| exact Hvo| exact HGs]|].
split; [unfold PGSZ in *; lia|]. split; [reflexivity|]. rewrite Ebrk.
destruct a.
-
destruct Ha as [Hlt Evm].
assert (F1 : 0 < bv_unsigned (vm_brk h)) by lia.
assert (F2 : bv_unsigned (vm_start_brk h) <= bv_unsigned (vm_brk h)) by lia.
assert (F3 : bv_unsigned (vm_brk h) < req < 2^64) by (unfold PGSZ in *; lia).
assert (F4 : bv_unsigned (vm_brk h) mod 4096 = 0) by (rewrite Ebrk; unfold PGSZ in *; rewrite Z.add_mod, R2, R4 by lia; reflexivity).
assert (F5 : req mod 4096 = 0) by (subst req; unfold PGSZ in *; rewrite Z.add_mod, (Z.add_mod b l), R2, R4 by lia; reflexivity).
pose proof (nstep_brk_grown_facts req mo rsp mo' evs F1 F2 F3 F4 F5 Hst Hdec) as [Hceil Hrf].
fold h in Hrf. rewrite Z_to_bv_bv_unsigned in Hrf.
assert (HPG : lbrk_pages_ok L (b + l) PGSZ = true).
{ pose proof (proj1 (kl_ceil _ _ _ HK)) as KC; pose proof KC as KC2; fold h in KC2.
apply (KL_lbrk_pages_ok L (ps_brk s0) mo (b + l) PGSZ HK); [lia| unfold PGSZ; lia| subst req; lia| |].
- replace (b + l) with (bv_unsigned (vm_brk h)) at 1 by exact Ebrk. rewrite Z_to_bv_bv_unsigned.
replace (Z_to_bv 64 PGSZ) with (Z_to_bv 64 (req - bv_unsigned (vm_brk h))) by (f_equal; lia). exact Hrf.
- intros b1 l1 E. rewrite Ereg in E. injection E as <- <-. split; [exact R4| left; lia]. }
assert (Hn : bv_unsigned (Z_to_bv 64 (req - bv_unsigned (vm_brk h))) = PGSZ) by (rewrite unsigned_lit; unfold PGSZ in *; lia).
rewrite (brk_grants_grow h req ltac:(lia) ltac:(unfold PGSZ in *; lia)) in Evm. cbn [app] in Evm.
pose proof (fun b0 l0 H => went_In_bounds _ _ _ b0 l0 HK H) as WB.
split; [|exact HPG].
kl_open HK. constructor; rewrite ?Evm; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk set_brkreg ld_ceil ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; auto; try (kl_ceil_tac Kceil).
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
* fold h in Hceil. clear -Hceil Kceil. pose proof Kceil as KC3. fold h in KC3. subst req. cbn [ld_ceil set_brkreg set_brkph] in *. lia.
* intros x Hx. destruct (Z_lt_le_dec x (b + l)) as [Hlt'|Hge].
-- destruct (Rcov x ltac:(lia)) as (e & He & Hr'). exists e. split; [right; exact He| exact Hr'].
-- exists (vm_brk h, Z_to_bv 64 (req - bv_unsigned (vm_brk h))). split; [left; reflexivity|]. rewrite elo_pair, ehi_pair, Hn. lia.
+ rewrite Hph. exists b, (l + PGSZ). rewrite unsigned_lit by (unfold PGSZ in *; lia). splits; auto; lia.
-
apply KL_dead with (pbrk := ps_brk s0). eapply KL_vmmaps_eq; [exact HK| exact Hmi'| exact Hh'| exact Ha]. }
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

Lemma noreserve_MAPF : mmap_noreserve_b (Z_to_bv 64 MAPF) = false.
Proof. reflexivity. Qed.
Lemma noreserve_MAPFX : mmap_noreserve_b (Z_to_bv 64 MAPFX) = false.
Proof. reflexivity. Qed.

Lemma KL_mmap_new : forall L pbrk mo mo' a len (isnone : bool),
KL L pbrk mo -> brk_quiet L -> 0 < len < LEN_MAX ->
let h := m_vmmaps mo in let n := mmap_len len in
mmap_addr_ok (ld_ceil L) len [] a = true ->
region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 a) (Z_to_bv 64 n) = true ->
minv mo' -> m_halted mo' = None ->
m_vmmaps mo' = mkVmMapsFull (vm_reserved h) ((Z_to_bv 64 a, Z_to_bv 64 n) :: vm_maps h)
(if isnone then (Z_to_bv 64 a, Z_to_bv 64 n) :: vm_noaccess h else vm_noaccess h)
(vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) ->
KL (if isnone then set_metas ((a, len, 0) :: ld_metas L) L else set_groups ((a, len) :: ld_groups L) L) pbrk mo'
/\ mmap_answer_ok (ld_ceil L) (lranges L) len a = true /\ is_err a = false.
Proof.
intros L pbrk mo mo' a len isnone HK Hq Hlen h n Hok Hrf Hmi' Hh' Evm. pose proof (ld_ceil_lt _ _ _ HK) as Hcl.
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
rewrite (proj2 (Z.ltb_lt 0 a)) by lia. unfold PGSZ at 1. rewrite A1, Z.eqb_refl. rewrite (proj2 (Z.leb_le _ _) A3). cbn [andb].
unfold ranges_free. apply forallb_forall. intros [lo m] Hin. cbn [fst snd]. unfold iv_disjoint.
enough (a + n <= lo \/ lo + m <= a) as D.
{ destruct D as [D|D]; [rewrite (proj2 (Z.leb_le _ _) D); reflexivity| rewrite (proj2 (Z.leb_le _ _) D); apply orb_true_r]. }
apply In_lranges in Hin as [H|[(b0 & l0 & H & E)|[(b0 & l0 & k & H & E)|(b0 & l0 & H & E)]]].
- rewrite (kl_resv _ _ _ HK) in H. apply in_map_iff in H as ([e sz] & E & H). unfold wwZ in E. cbn [fst snd] in E. injection E as <- <-.
pose proof (region_free_disj _ _ _ _ Hrf (in_or_app _ _ _ (or_introl H))) as D. rewrite Ua, Un in D. unfold elo, ehi in D. cbn in D. lia.
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
| rewrite ?Evm; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk set_metas set_groups ld_ceil ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; auto; try (kl_ceil_tac Kceil) ].
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
let dec := if isnone then dec_mmap_none (ld_ceil L) len [] else dec_mmap (ld_ceil L) len [] in
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
intros s mo (-> & HK & HGs). pose proof (ld_ceil_lt _ _ _ HK) as HcL. split.
{ subst prot. destruct isnone; [apply nsafe_mmap_none| apply nsafe_mmap_rw]; unfold LEN_MAX in *; lia. }
intros rsp mo' evs Hst.
pose proof (minv_preserved (NMmap 0 len prot MAPF) _ _ _ _ noreserve_MAPF (kl_minv _ _ _ HK) (kl_halt _ _ _ HK) Hst) as [Hh' Hmi'].
assert (Hcase : vm_only mo mo' /\ exists x, dec rsp = Some x /\
match x with
| MmErr e => e = ENOMEM /\ mo' = mo
| MmOk a => mmap_addr_ok (ld_ceil L) len [] a = true
/\ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (Z_to_bv 64 a) (Z_to_bv 64 (mmap_len len)) = true
/\ m_vmmaps mo' = mkVmMapsFull (vm_reserved (m_vmmaps mo)) ((Z_to_bv 64 a, Z_to_bv 64 (mmap_len len)) :: vm_maps (m_vmmaps mo))
(if isnone then (Z_to_bv 64 a, Z_to_bv 64 (mmap_len len)) :: vm_noaccess (m_vmmaps mo) else vm_noaccess (m_vmmaps mo))
(vm_start_brk (m_vmmaps mo)) (vm_brk (m_vmmaps mo)) (vm_limit (m_vmmaps mo)) (vm_mmap_base (m_vmmaps mo)) (vm_init_sp (m_vmmaps mo))
end).
{ subst prot dec. destruct isnone.

- pose proof (nstep_dec_mmap_none (ld_ceil L) len [] mo rsp mo' evs ltac:(lia) ltac:(unfold LEN_MAX in *; lia) ltac:(pose proof (kl_ceil _ _ _ HK); lia) (Forall_nil _) Hst) as (_ & Hvo & x & Hd & Hx).
split; [exact Hvo|]. exists x. split; [exact Hd|]. destruct x; [destruct Hx as (Hx1 & Hx2 & _); split; assumption| exact Hx].
- pose proof (nstep_dec_mmap (ld_ceil L) len [] mo rsp mo' evs ltac:(lia) ltac:(unfold LEN_MAX in *; lia) ltac:(pose proof (kl_ceil _ _ _ HK); lia) (Forall_nil _) Hst) as (_ & Hvo & x & Hd & Hx).
split; [exact Hvo|]. exists x. split; [exact Hd|]. destruct x; [destruct Hx as (Hx1 & Hx2 & _); split; assumption| exact Hx]. }
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
(ev_step (ld_ceil L) (EMmap 0 len prot MAPF))
(ev_step_post L (EMmap 0 len prot MAPF) G s0).
Proof.
intros L G s0 len prot HG Hq Hprot Hlen. unfold ev_step.
change (Z.land MAPF MAP_FIXED_Z =? 0) with true. cbn [negb].
destruct Hprot as [-> | ->].
- change (PROT_NONE =? 0) with true. cbv iota. apply (ev_mmap_core L G s0 len true HG Hq Hlen).
- change (PROT_RW =? 0) with false. cbv iota. apply (ev_mmap_core L G s0 len false HG Hq Hlen).
Qed.

Lemma nstep_mmap_fixed_done : forall a mo rsp mo' evs,
let h := m_vmmaps mo in
let aw := Z_to_bv 64 a in let n := Z_to_bv 64 PGSZ in
0 < a -> a + PGSZ <= alloc_top h -> a mod 4096 = 0 ->
region_free (vm_reserved h) aw n = true -> map_contains (vm_maps h) aw n = true ->
nstep (NMmap a PGSZ PROT_NONE MAPFX) mo rsp mo' evs ->
evs = [] /\ vm_only mo mo' /\ dec_mmap_fixed a PGSZ rsp = Some FxDone
/\ m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (vm_maps h) ((aw, n) :: maps_subtract (vm_noaccess h) a (a + PGSZ))
(vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).
Proof.
intros a mo rsp mo' evs h aw n Ha Hc Hal Hrf Hmc H.
pose proof (alloc_top_room h) as Hcl. unfold stack_max_size, two_pow_64 in Hcl.
pose proof (nstep_mm_vm_only (NMmap a PGSZ PROT_NONE MAPFX) mo rsp mo' evs noreserve_MAPFX H) as [Hv ->]. split; [reflexivity|]. split; [exact Hv|].
apply (proj1 (nstep_mmap_spec _ _ _ _ _ _ _ _)) in H as [_ H].
assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; unfold PGSZ in *; lia).
assert (Un : bv_unsigned n = PGSZ) by (subst n; apply unsigned_lit; unfold PGSZ; lia).
assert (Epg : page_round_up_Z (bv_unsigned (Z_to_bv 64 PGSZ)) = PGSZ) by (rewrite (unsigned_lit PGSZ) by (unfold PGSZ; lia); reflexivity).
apply (proj1 (mmap_fixed_noaccess_outcome aw (Z_to_bv 64 PGSZ) (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 MAPFX) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) _ _ _
ltac:(rewrite w_is0_lit by (unfold PGSZ; lia); reflexivity) eq_refl eq_refl eq_refl
ltac:(rewrite Epg, Ua; exact Hc) ltac:(rewrite Ua, page_size_eq; exact Hal) ltac:(rewrite Ua; exact Ha)
ltac:(rewrite Epg; exact Hrf) ltac:(rewrite Epg; exact Hmc))) in H.
rewrite Epg in H. fold n h in H. rewrite Ua, Un in H.
apply Ok_inj in H as (-> & -> & _). split.
- unfold dec_mmap_fixed. subst aw n. change (mmap_len PGSZ) with PGSZ. rewrite !bv_eqb_refl. cbn [andb].
rewrite errno_of_lit by (unfold PGSZ in *; lia). reflexivity.
- unfold with_mmap_replacement, with_mmap_backing. rewrite noreserve_MAPFX. unfold vm_forget_range. cbn. reflexivity.
Qed.

Lemma nstep_mmap_fixed_inv : forall a mo rsp mo' evs,
let h := m_vmmaps mo in
let aw := Z_to_bv 64 a in let n := Z_to_bv 64 PGSZ in
0 < a -> a + PGSZ <= alloc_top h -> a mod 4096 = 0 ->
region_free (vm_reserved h) aw n = true -> map_contains (vm_maps h) aw n = true ->
nstep (NMmap a PGSZ PROT_NONE MAPFX) mo rsp mo' evs ->
evs = [] /\ vm_only mo mo' /\
exists x, dec_mmap_fixed a PGSZ rsp = Some x /\
match x with
| FxKept e => e = ENOMEM /\ mo' = mo
| FxDone => m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (vm_maps h) ((aw, n) :: maps_subtract (vm_noaccess h) a (a + PGSZ))
(vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
| FxLost e => e = ENOMEM /\ m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (maps_subtract (vm_maps h) a (a + PGSZ))
(maps_subtract (vm_noaccess h) a (a + PGSZ))
(vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
end.
Proof.
intros a mo rsp mo' evs h aw n Ha Hc Hal Hrf Hmc H.
destruct (nstep_mmap_fixed_done a mo rsp mo' evs Ha Hc Hal Hrf Hmc H) as (E & Hv & Hd & Hm).
split; [exact E|]. split; [exact Hv|]. exists FxDone. split; [exact Hd| exact Hm].
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
(ev_step (ld_ceil L) (EMmap a PGSZ PROT_NONE MAPFX))
(ev_step_post L (EMmap a PGSZ PROT_NONE MAPFX) G s0).
Proof.
intros L G s0 cur HG Hph a. pose proof alloc_ceiling_hi_lt as Hcl. unfold ev_step.
change (Z.land MAPFX MAP_FIXED_Z =? 0) with false. cbn [negb].
set (L' := set_brkph BPLive (set_brkreg (Some (a, 2 * PGSZ)) L)).
eapply mspec_bind.
{ apply (mspec_sys (NMmap a PGSZ PROT_NONE MAPFX) (dec_mmap_fixed a PGSZ) _
(fun x s mo => s = s0 /\ G s mo /\ KL L' (ps_brk s0) mo /\ match x with FxKept e => e = ENOMEM | FxDone => True | FxLost e => e = ENOMEM end)).
intros s mo (-> & HK & HGs). pose proof (ld_ceil_lt _ _ _ HK) as HcL.
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
{ pose proof (nsafe_mmap_fixed_none a PGSZ mo) as NS. cbv zeta in NS. apply NS; fold h.
- unfold PGSZ; lia. - lia. - rewrite page_size_eq, Ha, Ecur. exact S2.
- rewrite (unsigned_lit PGSZ) by (unfold PGSZ; lia). change (page_round_up_Z PGSZ) with PGSZ. pose proof (kl_ceil _ _ _ HK) as KC0; pose proof KC0 as KC1; try fold h in KC1. lia.
- rewrite (unsigned_lit PGSZ) by (unfold PGSZ; lia). change (page_round_up_Z PGSZ) with PGSZ. exact Hrf.
- rewrite (unsigned_lit PGSZ) by (unfold PGSZ; lia). change (page_round_up_Z PGSZ) with PGSZ. exact Hmc. }
intros rsp mo' evs Hst.
pose proof (minv_preserved (NMmap a PGSZ PROT_NONE MAPFX) _ _ _ _ noreserve_MAPFX (kl_minv _ _ _ HK) (kl_halt _ _ _ HK) Hst) as [Hh' Hmi'].
pose proof (nstep_mmap_fixed_inv a mo rsp mo' evs ltac:(lia) ltac:(pose proof (kl_ceil _ _ _ HK) as KC0; pose proof KC0 as KC1; try fold h in KC1; lia) ltac:(rewrite Ha, Ecur; exact S2) Hrf Hmc Hst) as (_ & Hvo & x & Hd & Hx).
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
(forall e x y, In e (vm_noaccess h) -> elo e <= x -> x < y -> y <= ehi e -> y <= 2^64 -> (y <= a \/ a + PGSZ <= x) ->
exists e', In e' noacc' /\ elo e' <= x /\ y <= ehi e') ->
(exists e', In e' maps' /\ elo e' <= a + PGSZ /\ a + 2 * PGSZ <= ehi e') ->
m_vmmaps mo' = mkVmMapsFull (vm_reserved h) maps' noacc' (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) ->
KL L' (ps_brk s0) mo').
{ intros maps' noacc' Hwf' Hkeep Hback Hna Hcov' Evm. subst L'.
kl_open HK. constructor; rewrite ?Evm; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk set_brkph set_brkreg ld_ceil ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; auto; try (kl_ceil_tac Kceil).
- intros b0 l0 Hin. pose proof (WB b0 l0 (or_introl Hin)) as (B1 & B2 & B3 & B4 & B5 & B6). pose proof (Dgm b0 l0 (or_introl Hin)) as D.
specialize (Kgr b0 l0 Hin). destruct Kgr as ([G0 G1] & G2 & G3 & G4 & G5 & G6). splits; try assumption.
+ apply Hkeep; [exact B4|]. rewrite B5, B6. clear -D. unfold PGSZ in *. lia.
+ unfold brk_disj; cbn. intros b1 l1 E. injection E as <- <-. clear -D. unfold PGSZ in *. lia.
- intros b0 l0 k Hin. pose proof (WB b0 l0 (or_intror (ex_intro _ k Hin))) as (B1 & B2 & B3 & B4 & B5 & B6). pose proof (Dgm b0 l0 (or_intror (ex_intro _ k Hin))) as D.
specialize (Kme b0 l0 k Hin). destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). splits; try assumption.
+ apply Hkeep; [exact B4|]. rewrite B5, B6. clear -D. unfold PGSZ in *. lia.
+ unfold brk_disj; cbn. intros b1 l1 E. injection E as <- <-. clear -D. unfold PGSZ in *. lia.
+ intros q Hq1 Hq2. destruct (G9 q Hq1 Hq2) as (e & He & Hel & Heh).
apply (Hna e (b0 + q * PGSZ) (b0 + q * PGSZ + PGSZ) He Hel ltac:(unfold PGSZ; lia) Heh).
* clear -Hq1 Hq2 G5 HcL B3. unfold PGSZ in *. nia.
* clear -D Hq1 Hq2 G5. unfold PGSZ in *. nia.
- intros b1 l1 E. injection E as <- <-. splits.
+ lia.
+ rewrite Ha, Ecur. exact S2.
+ lia.
+ reflexivity.
+ lia.
+ intros z Hz. destruct Hcov' as (e' & He' & H1 & H2). exists e'. split; [exact He'|]. lia.
- exists a, (2 * PGSZ). splits; [reflexivity| lia| lia]. }
assert (Hlohi : a < a + PGSZ) by (unfold PGSZ; lia).
destruct x as [e| |e].
- destruct Hx as [-> ->]. split; [|reflexivity].
apply (KLnew (vm_maps h) (vm_noaccess h)); auto.
+ exact (kl_wf _ _ _ HK).
+ intros e x y He H1 H2 H3 H3' H4. exists e. auto.
+ exists e0. split; [exact He0|]. unfold PGSZ in *; lia.
+ subst h. destruct (m_vmmaps mo); reflexivity.
- split; [|exact I].
apply (KLnew (vm_maps h) ((aw, nw) :: maps_subtract (vm_noaccess h) a (a + PGSZ))); auto.
+ exact (kl_wf _ _ _ HK).
+ intros e x y He H1 H2 H3 H3' H4. destruct (iv_subtract_contains (fst e) (snd e) a (a + PGSZ) x y Hlohi H3' H1 H2 H3 H4) as (e' & He' & Hr).
exists e'. split; [right; eapply maps_subtract_In_intro; eauto| exact Hr].
+ exists e0. split; [exact He0|]. unfold PGSZ in *; lia.
- destruct Hx as [-> Evm]. split; [|reflexivity].
apply (KLnew (maps_subtract (vm_maps h) a (a + PGSZ)) (maps_subtract (vm_noaccess h) a (a + PGSZ))); auto.
+ apply vmwf_subtract; [exact Hlohi| exact (kl_wf _ _ _ HK)].
+ intros e He Hde. apply maps_subtract_keep; [exact (kl_wf _ _ _ HK)| exact Hlohi| exact He| exact Hde].
+ intros e x y He H1 H2 H3 H3' H4. destruct (iv_subtract_contains (fst e) (snd e) a (a + PGSZ) x y Hlohi H3' H1 H2 H3 H4) as (e' & He' & Hr).
exists e'. split; [eapply maps_subtract_In_intro; eauto| exact Hr].
+ destruct (iv_subtract_contains (fst e0) (snd e0) a (a + PGSZ) (a + PGSZ) (a + 2 * PGSZ) Hlohi ltac:(lia) ltac:(unfold elo in He0l; lia) ltac:(unfold PGSZ; lia) ltac:(unfold ehi in He0h; lia) ltac:(right; lia)) as (e' & He' & Hr).
exists e'. split; [eapply maps_subtract_In_intro; eauto| exact Hr]. }
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
(ev_step (ld_ceil L) (EMunmap a len))
(ev_step_post L (EMunmap a len) G s0).
Proof.
intros L G s0 a l0 len HG Hq Hin Hlen. pose proof alloc_ceiling_hi_lt as Hcl. unfold ev_step.
rewrite round_up_pg_eq in Hlen. fold (mmap_len l0) in Hlen.
set (L' := set_groups (g_remove a (ld_groups L)) L).
eapply mspec_bind.
{ apply (mspec_sys (NMunmap a len) (dec_munmap a len) _
(fun x s mo => s = s0 /\ G s mo /\ KL L' (ps_brk s0) mo /\ match x with RgErr e => e = EINVAL | RgDone _ => True end)).
intros s mo (-> & HK & HGs). pose proof (ld_ceil_lt _ _ _ HK) as HcL.
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
{ apply (proj2 (nsafe_munmap_iff a len mo)). unfold munmap_out. fold h aw. rewrite Ua, page_size_eq. unfold PGSZ in A3. rewrite A3. rewrite w_is0_lit by lia.
replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb orb Z.eqb]. cbv zeta.
rewrite (unsigned_lit len) by lia. fold (mmap_len len). rewrite Hlen2. change (Z_to_bv 64 n) with nw.
replace (TASK_SIZE <? a + n) with false by (symmetry; apply Z.ltb_ge; unfold TASK_SIZE; lia). rewrite Hhas.
intros E. exact (Unmodeled_Ok _ _ _ E). }
intros rsp mo' evs Hst.
pose proof (minv_preserved (NMunmap a len) _ _ _ _ I (kl_minv _ _ _ HK) (kl_halt _ _ _ HK) Hst) as [Hh' Hmi'].
pose proof (nstep_dec_munmap a len mo rsp mo' evs ltac:(lia) ltac:(lia) ltac:(rewrite Hlen2; lia) Hst) as (_ & Hvo & x & Hd & Hx).
rewrite Hlen2 in Hx. fold h aw nw in Hx. rewrite Ua, Un in Hx.
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
(forall e x y, In e (vm_noaccess h) -> elo e <= x -> x < y -> y <= ehi e -> y <= 2^64 -> (y <= a \/ a + n <= x) ->
exists e', In e' noacc' /\ elo e' <= x /\ y <= ehi e') ->
m_vmmaps mo' = mkVmMapsFull (vm_reserved h) maps' noacc' (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) ->
KL L' (ps_brk s0) mo').
{ intros maps' noacc' Hwf' Hkeep Hna Evm.
assert (Hph' : phase_inv (ld_brk L') L' (ps_brk s0) mo') by (eapply phase_quiet; [exact HK| exact Hq| reflexivity| reflexivity| rewrite Evm; reflexivity| rewrite Evm; reflexivity]).
assert (Kfst : forall b l, b <> a -> 0 < b < 2^64 -> fst (went b (mmap_len l)) <> aw).
{ intros b l Hne Hb E. apply Hne. apply (f_equal bv_unsigned) in E. cbn [fst went] in E. rewrite unsigned_wz, Ua in E by lia. exact E. }
subst L'. kl_open HK. constructor; try exact Hph'; rewrite ?Evm; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk set_groups ld_ceil ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; auto; try (kl_ceil_tac Kceil).
- intros b0 l1 Hin0. destruct (Hg' b0 l1 Hin0) as [Hin1 Hne]. specialize (Kgr b0 l1 Hin1). destruct Kgr as ([G0 G1] & G2 & G3 & G4 & G5 & G6). splits; try assumption.
apply Hkeep; [exact G5|]. apply Kfst; auto. pose proof (mmap_len_ge l1 G0). lia.
- intros b0 l1 k Hin0. pose proof (Hm' b0 l1 k Hin0) as Hne. specialize (Kme b0 l1 k Hin0). destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). splits; try assumption.
+ apply Hkeep; [exact G7|]. apply Kfst; auto. pose proof (mmap_len_ge l1 G0). lia.
+ intros q Hq1 Hq2. destruct (G9 q Hq1 Hq2) as (e & He & Hel & Heh).
pose proof (Dother b0 l1 (or_intror (ex_intro _ k Hin0)) Hne) as D.
apply (Hna e (b0 + q * PGSZ) (b0 + q * PGSZ + PGSZ) He Hel ltac:(unfold PGSZ; lia) Heh).
* clear -Hq1 Hq2 G5 HcL G4. unfold PGSZ in *. nia.
* clear -D Hq1 Hq2 G5. unfold PGSZ in *. nia.
- rewrite Ezz, map_app, <- app_assoc. exact Kd1.
- intros b0 l1 E. specialize (Kreg b0 l1 E). destruct Kreg as (R1 & R2 & R3 & R4 & R5 & Rcov). splits; auto.
intros z Hz. destruct (Rcov z Hz) as (e & He & Hr). exists e. split; [|exact Hr]. apply Hkeep; [exact He|].
intros Efst. unfold brk_disj in A6. specialize (A6 b0 l1 E).
destruct (pwdisj_In _ _ _ (proj2 Kwf) He A5) as [->|D].
+ rewrite B5, B6 in Hr. clear -Hr A6 Hz R3. unfold PGSZ in *. lia.
+ pose proof (proj1 Kwf e He) as W. unfold edisj, elo, ehi in D, W. rewrite Efst in D, W. cbn [fst snd went] in D. unfold wz in D. fold aw nw in D. rewrite Un in D. lia. }
assert (Hlohi : a < a + n) by lia.
destruct x as [e|[|]].
- destruct Hx as [-> ->]. split; [|reflexivity]. apply (KLnew (vm_maps h) (vm_noaccess h)).
+ exact (kl_wf _ _ _ HK).
+ auto.
+ intros e x y He H1 H2 H3 H3' H4. exists e. auto.
+ subst h. destruct (m_vmmaps mo); reflexivity.
- destruct Hx as [_ Evm]. split; [|exact I]. apply (KLnew (map_remove (vm_maps h) aw) (maps_subtract (vm_noaccess h) a (a + n))).
+ apply vmwf_remove. exact (kl_wf _ _ _ HK).
+ intros e He Hne. unfold map_remove. apply filter_In. split; [exact He|]. destruct (bv_eqb (fst e) aw) eqn:E; [|reflexivity]. apply bv_eqb_eq in E. contradiction.
+ intros e x y He H1 H2 H3 H3' H4. destruct (iv_subtract_contains (fst e) (snd e) a (a + n) x y Hlohi H3' H1 H2 H3 H4) as (e' & He' & Hr).
exists e'. split; [eapply maps_subtract_In_intro; eauto| exact Hr].
+ exact Evm.
- destruct Hx as [-> _]. split; [|exact I]. apply (KLnew (vm_maps h) (vm_noaccess h)).
+ exact (kl_wf _ _ _ HK).
+ auto.
+ intros e x y He H1 H2 H3 H3' H4. exists e. auto.
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

Lemma nstep_mprotect_rgfalse : forall addr len mo rsp mo' evs,
let h := m_vmmaps mo in
let a := Z_to_bv 64 addr in let n := Z_to_bv 64 (mmap_len len) in
(0 <= addr < 2^64)%Z -> (0 < len)%Z -> (mmap_len len < 2^64)%Z ->
map_contains (vm_noaccess h) a n = true -> map_contains (vm_maps h) a n = true ->
nstep (NMprotect addr len (PROT_READ + PROT_WRITE)) mo rsp mo' evs ->
dec_mprotect addr len rsp = Some (RgDone false) -> False.
Proof.
intros addr len mo rsp mo' evs h a n Ha Hlen Hlen2 Hcn Hcm H Hd.
pose proof (mmap_len_bound len Hlen) as Hb.
apply (proj1 (nstep_mprotect_spec _ _ _ _ _ _ _)) in H as [_ H]. apply (proj1 (mprotect_outcome _ _ _ _ _ _)) in H. unfold mprotect_out in H.
fold a h in H. rewrite (unsigned_lit len) in H by lia. fold (mmap_len len) in H. fold n in H. cbv zeta in H.
change (mprotect_grows_conflict_b (Z_to_bv 64 (PROT_READ + PROT_WRITE))) with false in H.
change (mprotect_modeled_b (Z_to_bv 64 (PROT_READ + PROT_WRITE))) with true in H. cbv iota in H.
destruct (negb (bv_unsigned a mod page_size =? 0)%Z).
{ apply Ok_inj in H as (-> & -> & _). unfold dec_mprotect in Hd. cbn in Hd. rewrite errno_of_errno_ret in Hd by (unfold EINVAL; lia). discriminate. }
rewrite w_is0_lit in H by lia. replace (len =? 0)%Z with false in H by (symmetry; apply Z.eqb_neq; lia).
destruct (two_pow_64 <=? _)%Z.
{ apply Ok_inj in H as (-> & -> & _). unfold dec_mprotect in Hd. cbn in Hd. rewrite errno_of_errno_ret in Hd by (unfold ENOMEM; lia). discriminate. }
rewrite Hcn, Hcm in H. cbn [andb] in H.
destruct H as [(_ & e & He & E) | (Hbud & E)]; apply Ok_inj in E as (-> & -> & _).
- cbn in He. destruct He as [<-|[]]. unfold dec_mprotect in Hd. cbn in Hd. rewrite errno_of_errno_ret in Hd by (unfold ENOMEM; lia). discriminate.
- unfold dec_mprotect in Hd. cbn -[Z.eqb bv_eqb bv_unsigned Z_to_bv mmap_len] in Hd.
destruct ((bv_unsigned (Z_to_bv 64 0) =? 0) && bv_eqb a (Z_to_bv 64 addr) && bv_eqb n (Z_to_bv 64 (mmap_len len))); discriminate.
Qed.

Lemma ev_mprotect_ok : forall L G s0 b l k, frame_ok G -> brk_quiet L -> In (b, l, k) (ld_metas L) ->
(2 + k) * PGSZ <= round_up_pg l ->
let a := b + (1 + k) * PGSZ in
mspec (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ G s mo)
(ev_step (ld_ceil L) (EMprotect a PGSZ PROT_RW))
(ev_step_post L (EMprotect a PGSZ PROT_RW) G s0).
Proof.
intros L G s0 b l k HG Hq Hin Hk2 a. pose proof alloc_ceiling_hi_lt as Hcl. unfold ev_step.
rewrite round_up_pg_eq in Hk2. fold (mmap_len l) in Hk2.
set (L' := set_metas (map (bump_meta a) (ld_metas L)) L).
eapply mspec_bind.
{ apply (mspec_sys (NMprotect a PGSZ PROT_RW) (dec_mprotect_rw a PGSZ) _
(fun x s mo => s = s0 /\ G s mo /\ match x with RgErr e => (e = EINVAL \/ e = ENOMEM) /\ KL L (ps_brk s0) mo | RgDone _ => KL L' (ps_brk s0) mo end)).
intros s mo (-> & HK & HGs). pose proof (ld_ceil_lt _ _ _ HK) as HcL.
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
{ apply (proj2 (nsafe_mprotect_iff a PGSZ PROT_RW mo)). unfold mprotect_out. fold h aw.
change (mprotect_grows_conflict_b (Z_to_bv 64 PROT_RW)) with false. change (mprotect_modeled_b (Z_to_bv 64 PROT_RW)) with true.
rewrite Ua, page_size_eq, Hamod. rewrite (unsigned_lit PGSZ) by (unfold PGSZ; lia). change (w_is0 (Z_to_bv 64 PGSZ)) with false. cbv iota. cbn [Z.eqb negb]. change (page_round_up_Z PGSZ) with PGSZ.
replace (two_pow_64 <=? a + PGSZ) with false by (symmetry; apply Z.leb_gt; unfold two_pow_64, PGSZ in *; lia). cbv zeta. fold nw. rewrite Hcn, Hcm. cbn [andb].
intros [(_ & e & _ & E)|(_ & E)]; exact (Unmodeled_Ok _ _ _ E). }
intros rsp mo' evs Hst.
pose proof (minv_preserved (NMprotect a PGSZ PROT_RW) _ _ _ _ I (kl_minv _ _ _ HK) (kl_halt _ _ _ HK) Hst) as [Hh' Hmi'].
pose proof (nstep_dec_mprotect a PGSZ mo rsp mo' evs ltac:(unfold PGSZ in *; lia) ltac:(unfold PGSZ; lia) ltac:(change (mmap_len PGSZ) with PGSZ; unfold PGSZ; lia) Hst) as (_ & Hvo & x & Hd & Hx).
change (mmap_len PGSZ) with PGSZ in Hx. fold h aw nw in Hx.
assert (HdRW : dec_mprotect_rw a PGSZ rsp = Some x).
{ destruct x as [e|[|]].
- destruct Hx as [He _]. unfold dec_mprotect_rw. rewrite Hd.
replace (e =? ENOSYS) with false by (symmetry; apply Z.eqb_neq; destruct He as [-> | ->]; unfold EINVAL, ENOMEM, ENOSYS; lia). reflexivity.
- unfold dec_mprotect_rw. rewrite Hd. reflexivity.
- exfalso. apply (nstep_mprotect_rgfalse a PGSZ mo rsp mo' evs ltac:(unfold PGSZ in *; lia) ltac:(unfold PGSZ; lia) ltac:(change (mmap_len PGSZ) with PGSZ; unfold PGSZ; lia)); [| | exact Hst | exact Hd];
change (mmap_len PGSZ) with PGSZ; [exact Hcn| exact Hcm]. }
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
m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (vm_maps h) noacc' (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) ->
KL L' (ps_brk s0) mo').
{ intros noacc' Hna Evm.
assert (Hph' : phase_inv (ld_brk L') L' (ps_brk s0) mo') by (eapply phase_quiet; [exact HK| exact Hq| reflexivity| reflexivity| rewrite Evm; reflexivity| rewrite Evm; reflexivity]).
subst L'. kl_open HK. constructor; try exact Hph'; rewrite ?Evm; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk set_metas ld_ceil ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; auto; try (kl_ceil_tac Kceil).
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
apply (Hna e (b + q * PGSZ) (b + q * PGSZ + PGSZ) He Hel ltac:(unfold PGSZ; lia) Heh).
* clear -Hq1 Hq2 G5 HcL G4. unfold PGSZ in *. nia.
* right. subst a. clear -Hq1. unfold PGSZ in *. nia.
+ splits; try assumption.
intros q Hq1 Hq2. destruct (G9 q Hq1 Hq2) as (e & He & Hel & Heh).
apply (Hna e (b0 + q * PGSZ) (b0 + q * PGSZ + PGSZ) He Hel ltac:(unfold PGSZ; lia) Heh).
{ clear -Hq1 Hq2 G5 HcL G4. unfold PGSZ in *. nia. }
destruct (Z.eq_dec b0 b) as [->|Hne].
{ pose proof (nodup_map_inj _ _ _ _ Kdm Hin1 Hin (eq_refl b)) as E. injection E as -> ->. exfalso. apply Na. reflexivity. }
pose proof (Dother b0 l0 (or_intror (ex_intro _ k0 Hin1)) Hne) as D. clear -D Hab Hq1 Hq2 G5. unfold PGSZ in *. nia.
- rewrite map_base_bump. exact Kd. }
destruct x as [e|[|]].
- destruct Hx as (He & -> & _). split; [exact He| exact HK].
- destruct Hx as (_ & _ & Evm). rewrite Ua, Un in Evm. apply (KLnew (maps_subtract (vm_noaccess h) a (a + PGSZ))); [|exact Evm].
assert (Hlohi : a < a + PGSZ) by (unfold PGSZ; lia).
intros e x y He H1 H2 H3 H3' H4. destruct (iv_subtract_contains (fst e) (snd e) a (a + PGSZ) x y Hlohi H3' H1 H2 H3 H4) as (e' & He' & Hr).
exists e'. split; [eapply maps_subtract_In_intro; eauto| exact Hr].
- subst mo'. apply (KLnew (vm_noaccess h)).
+ intros e x y He H1 H2 H3 H3' H4. exists e. auto.
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
mspec (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ G s mo) (ev_step (ld_ceil L) e) (ev_step_post L e G s0).
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

End OK.

Lemma membed_spec {R} : forall (t : stree ev Z R) (Post : mled -> R -> Prop) (G : PState -> Model -> Prop) L s0 c,
frame_ok G -> ctree_ok L t Post -> ld_ceil L = c ->
mspec (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ G s mo) (membed c t)
(fun r s mo => exists L', cpath L t L' r /\ Post L' r /\ KL L' (ps_brk s) mo /\ G s mo
/\ ps_m s = ps_m s0 /\ ps_fa s = ps_fa s0 /\ ps_so s = ps_so s0).
Proof.
intros t. induction t as [r|e k IH]; intros Post G L s0 c HG Hok Hc.
- cbn [membed]. apply mspec_ret. intros s mo (-> & HK & HGs). pose proof (ld_ceil_lt _ _ _ HK) as HcL. exists L.
split; [constructor|]. cbn in Hok. splits; auto.
- cbn [membed]. cbn in Hok. destruct Hok as [Hpre Hk]. subst c.
eapply mspec_bind; [apply (ev_step_spec L e G s0 HG Hpre)|].
intros z. unfold ev_step_post. apply mspec_pointwise. intros s1 mo1 (Hans & HK1 & HG1 & Hm & Hfa & Hso).
eapply mspec_conseq; [apply (IH z Post G (event_post L e z) s1 (ld_ceil L) HG (Hk z Hans) (event_post_ld_ceil L e z))| |].
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

Lemma OWN_minv : forall X G s mo, OWN X G s mo -> minv mo /\ m_halted mo = None.
Proof. intros X G s mo [(L & _ & HK & _) _]. split; [exact (kl_minv _ _ _ HK)| exact (kl_halt _ _ _ HK)]. Qed.

Lemma OWN_vmmaps : forall X G s mo mo', OWN X G s mo -> m_vmmaps mo' = m_vmmaps mo -> minv mo' -> m_halted mo' = None ->
G s mo' -> OWN X G s mo'.
Proof.
intros X G s mo mo' [(L & Hc & HK & Hi) [Hnd HG]] Hvm Hmi Hh HG'. split; [|split; [exact Hnd| exact HG']].
exists L. split; [exact Hc|]. split; [| exact Hi]. eapply KL_vmmaps_eq; eauto.
Qed.

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

Definition RBIG : Z := X1q7.RBIG.

Theorem raw_malloc_spec : forall X G n, frame_ok G -> 0 <= n ->
mspec (OWN X G) (raw_malloc n)
(fun r s mo => match r with
| Some p => OWN (p :: X) G s mo /\ n < 2^63 /\ (RBIG <= n -> ptop p = true)
| None => OWN X G s mo
end).
Proof.
intros X G n HG Hn. unfold raw_malloc.
eapply mspec_bind; [apply mspec_get|]. intros s0.
apply mspec_pointwise. intros s1 mo1 [-> [(L & Hc & HK & Hi) [Hnd HGs]]].
eapply mspec_bind.
{ eapply mspec_pre; [apply (membed_spec (cmalloc (ps_m s1) n) _ G L s1 _ HG (X1pi.cmalloc_contract_proof _ _ _ Hc Hn) (X1pi.creach_ceil _ _ Hc))|].
intros s mo [-> ->]. auto. }
intros [st' p]. cbn beta iota.
apply mspec_pointwise. intros s2 mo2 (L' & Hp & HPost & HK' & HG' & Hm & Hfa & Hso).
pose proof (cpath_live _ _ _ _ Hp) as Hlive. cbn [snd] in HPost.
assert (Hcr : creach st' (match p with Some c => set_live (c :: ld_live L') L' | None => L' end)).
{ exact (creach_malloc _ _ _ _ _ _ Hc Hn Hp). }
assert (HGf : forall h st, G (set_hdr_ps h (set_m st s2)) mo2).
{ intros h st. apply (HG s2 _ mo2 _); [reflexivity|reflexivity|apply vm_only_refl| exact HG']. }
assert (OWNc : forall c h, p = Some c ->
OWN ((c, real_off h st' c n) :: X) G (set_hdr_ps (<[c := real_off h st' c n]> h) (set_m st' s2)) mo2
/\ OWN ((c, -1) :: X) G (set_hdr_ps h (set_m st' s2)) mo2).
{ intros c h ->.
assert (K : forall z s', ps_m s' = st' -> ps_brk s' = ps_brk s2 -> G s' mo2 -> OWN ((c, z) :: X) G s' mo2).
{ intros z s' Em Eb Gs'. split; [|split; [|exact Gs']].
- exists (set_live (c :: ld_live L') L'). rewrite Em, Eb. split; [exact Hcr|]. split; [apply KL_set_live; exact HK'|].
cbn. intros x [<-|Hx]; [left; reflexivity| right]. rewrite Hlive. apply Hi. exact Hx.
- cbn. constructor; [|exact Hnd]. intros Hin. apply HPost. rewrite Hlive. apply Hi. exact Hin. }
split; apply K; try reflexivity; apply HGf. }
assert (Hov : forall c, p = Some c -> n < 2^63).
{ intros c ->. destruct (size_overflows n) eqn:E.
- exfalso. rewrite (cmalloc_overflow _ _ E) in Hp. inversion Hp.
- unfold size_overflows in E. apply Z.leb_gt in E. lia. }
destruct p as [c|].
- destruct (slot_top st' c) eqn:Htop.
+ eapply mspec_seq with (R := fun s mo => s = set_hdr_ps (<[c := real_off (hdr_after (ps_m s1) st' (ps_hdr s1)) st' c n]> (hdr_after (ps_m s1) st' (ps_hdr s1))) (set_m st' s2) /\ mo = mo2).
{ apply mspec_upd'. intros s mo [-> ->]. auto. }
intros _. apply mspec_ret. intros s mo [-> ->].
split; [apply (proj1 (OWNc c _ eq_refl))|]. split; [exact (Hov c eq_refl)|].
intros Hbig. destruct (X1q7.cmalloc_big_top _ _ _ _ _ _ Hc Hn Hp Hbig) as (_ & g & i & Hs & Hsl).
unfold ptop. cbn [snd]. apply Z.leb_le. eapply X1q7.real_off_nonneg; [exact Hs| exact Hsl].
+ eapply mspec_seq with (R := fun s mo => s = set_hdr_ps (hdr_after (ps_m s1) st' (ps_hdr s1)) (set_m st' s2) /\ mo = mo2).
{ apply mspec_upd'. intros s mo [-> ->]. auto. }
intros _. apply mspec_ret. intros s mo [-> ->].
split; [apply (proj2 (OWNc c _ eq_refl))|]. split; [exact (Hov c eq_refl)|].
intros Hbig. destruct (X1q7.cmalloc_big_top _ _ _ _ _ _ Hc Hn Hp Hbig) as (Htop' & _). rewrite Htop in Htop'. discriminate Htop'.
- eapply mspec_seq with (R := fun s mo => s = set_hdr_ps (hdr_after (ps_m s1) st' (ps_hdr s1)) (set_m st' s2) /\ mo = mo2).
{ apply mspec_upd'. intros s mo [-> ->]. auto. }
intros _. apply mspec_ret. intros s mo [-> ->].
split; [|split; [exact Hnd| apply HGf]].
exists L'. cbn. split; [exact Hcr|]. split; [exact HK'|]. rewrite Hlive. exact Hi.
Qed.

Theorem raw_free_spec : forall X G p, frame_ok G ->
mspec (OWN (p :: X) G) (raw_free p) (fun _ => OWN X G).
Proof.
intros X G p HG. unfold raw_free.
eapply mspec_bind; [apply mspec_get|]. intros s0.
apply mspec_pointwise. intros s1 mo1 [-> [(L & Hc & HK & Hi) [Hnd HGs]]].
assert (Hin : In (fst p) (ld_live L)) by (apply Hi; left; reflexivity).
eapply mspec_bind.
{ eapply mspec_pre; [apply (membed_spec (cfree (ps_m s1) (Some (fst p))) _ G L s1 _ HG (X1pi.cfree_contract_proof _ _ _ Hc Hin) (X1pi.creach_ceil _ _ Hc))|].
intros s mo [-> ->]. auto. }
intros st'. cbn beta iota.
apply mspec_pointwise. intros s2 mo2 (L' & Hp & _ & HK' & HG' & Hm & Hfa & Hso).
pose proof (cpath_live _ _ _ _ Hp) as Hlive.
apply mspec_upd'. intros s mo [-> ->].
assert (Hcr : creach st' (set_live (ap_remove (fst p) (ld_live L')) L')).
{ exact (creach_free _ _ _ _ _ Hc Hin Hp). }
split; [|split; [inversion Hnd; assumption| apply (HG s2 _ mo2 _); [reflexivity|reflexivity|apply vm_only_refl| exact HG']]].
exists (set_live (ap_remove (fst p) (ld_live L')) L'). split; [exact Hcr|]. split; [apply KL_set_live; exact HK'|].
cbn. intros x Hx. rewrite Hlive. apply in_ap_remove.
- apply Hi. right. exact Hx.
- inversion Hnd; subst. intros ->. apply H1. exact Hx.
Qed.

Theorem raw_free_opt_spec : forall X G (o : option bptr), frame_ok G ->
mspec (OWN (match o with Some p => p :: X | None => X end) G) (raw_free_opt o) (fun _ => OWN X G).
Proof.
intros X G [p|] HG; cbn [raw_free_opt]; [apply raw_free_spec; exact HG|]. apply mspec_ret. intros s mo H. exact H.
Qed.

Theorem raw_calloc_spec : forall X G m n, frame_ok G -> 0 <= m -> 0 <= n ->
mspec (OWN X G) (raw_calloc m n)
(fun r s mo => match r with
| Some p => OWN (p :: X) G s mo /\ n * m < 2^63 /\ (RBIG <= n * m -> ptop p = true)
| None => OWN X G s mo
end).
Proof.
intros X G m n HG Hm Hn. unfold raw_calloc.
destruct (negb (n =? 0) && ((2^64 - 1) / n <? m)); [apply mspec_ret; intros s mo H; exact H|].
apply raw_malloc_spec; [exact HG| nia].
Qed.

Theorem raw_realloc_spec : forall X G p n, frame_ok G -> ptop p = true -> 0 <= n < MMAP_THRESHOLD ->
mspec (OWN (p :: X) G) (raw_realloc p n)
(fun r s mo => match r with
| Some q => OWN (q :: X) G s mo /\ (RBIG <= n -> ptop q = true)
| None => OWN (p :: X) G s mo
end).
Proof.
intros X G p n HG Htop Hn. unfold raw_realloc.
replace (size_overflows n) with false by (symmetry; unfold size_overflows; apply Z.leb_gt; unfold MMAP_THRESHOLD in Hn; lia).
rewrite Htop. cbn [negb].
eapply mspec_bind; [apply mspec_get|]. intros s0.
apply mspec_pointwise. intros s1 mo1 [-> HO]. pose proof HO as [(L & Hc & HK & Hi) [Hnd HGs]].
destruct (X1q7.creach_live_slot _ _ (fst p) Hc ltac:(apply Hi; left; reflexivity)) as (g & i & Hs). rewrite Hs.
destruct ((n <=? _) && (n <? MMAP_THRESHOLD) && (_ <=? size_to_class n + 1)).
{ apply mspec_ret. intros s mo [-> ->]. split; [exact HO| intros _; exact Htop]. }
replace (MMAP_THRESHOLD <=? n) with false by (symmetry; apply Z.leb_gt; lia). rewrite andb_false_r.
eapply mspec_bind.
{ eapply mspec_pre; [apply (raw_malloc_spec (p :: X) G n HG ltac:(lia))|]. intros s mo [-> ->]. exact HO. }
intros [q|]; cbn beta iota.
- apply mspec_pure. intros [_ Hq]. eapply mspec_seq.
+ eapply mspec_pre; [apply (raw_free_spec (q :: X) G p HG)|]. intros s mo H. eapply OWN_perm; [apply perm_swap| exact H].
+ intros _. apply mspec_ret. intros s mo H. split; [exact H| exact Hq].
- apply mspec_ret. intros s mo H. exact H.
Qed.
