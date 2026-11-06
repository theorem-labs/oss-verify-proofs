(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsjA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEpW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEpW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfya.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfya. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYTG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYTG.Mq0.
Import ListNotations.
Open Scope Z_scope.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QxOB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QxOB.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Ltac klia :=
cbv delta [PGSZ LEN_MAX TWO64 alloc_ceiling] in *; rc_lia_prep;
first [ Qo9G.term_slim ltac:(zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker)
| Qo9G.term_slim ltac:(zify_prune; Zify.zify; xlia zchecker)
| Qo9G.term_slim ltac:(Zify.zify; xlia zchecker) ].
Ltac lia ::= klia. Ltac mkr__lia_0 := klia.
Ltac knia := cbv delta [PGSZ LEN_MAX TWO64 alloc_ceiling] in *; Qo9G.term_slim ltac:(rc_lia_prep; Zify.zify; xnia zchecker).
Ltac nia ::= knia. Ltac mkr__nia_1 := knia.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition wz (z : Z) : word := Z_to_bv 64 z.
Definition went (b n : Z) : word * word := (wz b, wz n).
Definition wwZ (e : word * word) : Z * Z := (bv_unsigned (fst e), bv_unsigned (snd e)).
Definition elo (e : word * word) : Z := bv_unsigned (fst e).
Definition ehi (e : word * word) : Z := bv_unsigned (fst e) + bv_unsigned (snd e).

Definition wcov (maps : list (word * word)) (lo hi : Z) : Prop :=
forall x, lo <= x < hi -> exists e, In e maps /\ elo e <= x < ehi e.

Definition edisj (e1 e2 : word * word) : Prop := ehi e1 <= elo e2 \/ ehi e2 <= elo e1.
Inductive pwdisj : list (word * word) -> Prop :=
| pwdisj_nil : pwdisj []
| pwdisj_cons e l : (forall e', In e' l -> edisj e e') -> pwdisj l -> pwdisj (e :: l).
Definition vmwf (maps : list (word * word)) : Prop :=
(forall e, In e maps -> elo e < ehi e <= 2^64) /\ pwdisj maps.

#[using="Type"] Lemma unsigned_wz : forall z, 0 <= z < 2^64 -> bv_unsigned (wz z) = z.
Proof. intros. unfold wz. apply unsigned_lit. assumption. Qed.
#[using="Type"] Lemma elo_went : forall b n, 0 <= b < 2^64 -> elo (went b n) = b.
Proof. intros. unfold elo, went. cbn [fst]. apply unsigned_wz. assumption. Qed.
#[using="Type"] Lemma ehi_went : forall b n, 0 <= b < 2^64 -> 0 <= n < 2^64 -> ehi (went b n) = b + n.
Proof. intros. unfold ehi, went. cbn [fst snd]. rewrite !unsigned_wz by assumption. reflexivity. Qed.
#[using="Type"] Lemma elo_pair : forall a n, elo (a, n) = bv_unsigned a. Proof. reflexivity. Qed.
#[using="Type"] Lemma ehi_pair : forall a n, ehi (a, n) = bv_unsigned a + bv_unsigned n. Proof. reflexivity. Qed.

#[using="Type"] Lemma alloc_ceiling_small : alloc_ceiling + 2^48 < 2^63.
Proof. exact Q6q3.alloc_ceiling_small. Qed.

#[using="Type"] Lemma mmap_len_ge : forall l, 0 < l -> l <= mmap_len l < l + 4096.
Proof. intros. apply mmap_len_bound. assumption. Qed.
#[using="Type"] Lemma mmap_len_pos_pg : forall l, 0 < l -> PGSZ <= mmap_len l.
Proof.
intros l Hl. unfold mmap_len, page_round_up_Z. rewrite page_size_eq, PGSZ_eq.
pose proof (Z_div_mod_eq_full (l + 4095) 4096). pose proof (Z.mod_pos_bound (l + 4095) 4096 ltac:(lia)).
assert (1 <= (l + 4095) / 4096) by (apply Z.div_le_lower_bound; lia). nia.
Qed.

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
#[using="Type"] Lemma region_free_app_l : forall l1 l2 a n, region_free (l1 ++ l2) a n = true -> region_free l1 a n = true.
Proof. induction l1 as [|[e sz] l1 IH]; intros l2 a n H; [reflexivity|]. cbn in H |- *. apply andb_prop in H as [H1 H]. rewrite H1. apply (IH l2). exact H. Qed.

#[using="Type"] Lemma region_free_disj : forall maps a n e, region_free maps a n = true -> In e maps ->
bv_unsigned a + bv_unsigned n <= elo e \/ ehi e <= bv_unsigned a.
Proof. intros maps a n [e sz] H Hin. unfold elo, ehi. cbn. eapply region_free_In; eauto. Qed.

#[using="Type"] Lemma region_free_intro : forall maps a n,
(forall e, In e maps -> bv_unsigned a + bv_unsigned n <= elo e \/ ehi e <= bv_unsigned a) ->
region_free maps a n = true.
Proof.
induction maps as [|[b sz] maps IH]; intros a n H; [reflexivity|]. cbn.
rewrite IH by (intros e He; apply H; right; exact He).
specialize (H (b, sz) (or_introl eq_refl)). unfold elo, ehi in H; cbn in H.
unfold iv_overlap. destruct (Z.ltb_spec (bv_unsigned a) (bv_unsigned b + bv_unsigned sz));
destruct (Z.ltb_spec (bv_unsigned b) (bv_unsigned a + bv_unsigned n)); cbn; try reflexivity. lia.
Qed.

#[using="Type"] Lemma region_free_shrink : forall maps a n n',
region_free maps a n = true -> bv_unsigned n' <= bv_unsigned n -> region_free maps a n' = true.
Proof. intros maps a n n' H Hle. apply region_free_intro. intros e He. pose proof (region_free_disj _ _ _ _ H He). lia. Qed.

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

#[using="Type"] Lemma In_map_remove : forall maps a e, In e (map_remove maps a) <-> In e maps /\ fst e <> a.
Proof.
intros maps a e. unfold map_remove. rewrite List.filter_In. split.
- intros [Hin Hb]. split; [exact Hin|]. intros E. rewrite E, bv_eqb_refl in Hb. discriminate.
- intros [Hin Hne]. split; [exact Hin|]. rewrite (bv_eqb_neq _ _ Hne). reflexivity.
Qed.

#[using="Type"] Lemma iv_subtract_sub : forall a sz lo hi e, 0 < bv_unsigned sz -> bv_unsigned a + bv_unsigned sz <= 2^64 ->
0 <= lo -> hi < 2^64 ->
In e (iv_subtract a sz lo hi) -> bv_unsigned a <= elo e /\ ehi e <= bv_unsigned a + bv_unsigned sz /\ elo e < ehi e.
Proof.
intros a sz lo hi e Hsz Hwf Hlo Hhi Hin. unfold iv_subtract in Hin.
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

#[using="Type"] Lemma iv_subtract_disjoint : forall a sz lo hi,
bv_unsigned a < bv_unsigned a + bv_unsigned sz <= 2^64 -> 0 <= lo < hi ->
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

#[using="Type"] Lemma maps_subtract_keep : forall maps lo hi e, vmwf maps -> 0 <= lo < hi ->
In e maps -> (ehi e <= lo \/ hi <= elo e) -> In e (maps_subtract maps lo hi).
Proof.
induction maps as [|[a sz] maps IH]; intros lo hi e Hwf Hlh Hin Hd; [destruct Hin|].
destruct Hwf as [Hb Hp]. cbn. apply in_or_app. destruct Hin as [<-|Hin].
- left. rewrite iv_subtract_disjoint; [left; reflexivity| | exact Hlh|].
+ specialize (Hb (a, sz) (or_introl eq_refl)). unfold elo, ehi in Hb. cbn in Hb. lia.
+ unfold elo, ehi in Hd. cbn in Hd. lia.
- right. apply IH; auto. split; [intros e' H'; apply Hb; right; exact H'| inversion Hp; assumption].
Qed.

#[using="Type"] Lemma iv_subtract_contains : forall a sz lo hi x y,
0 <= lo < hi -> hi < 2^64 -> bv_unsigned a + bv_unsigned sz <= 2^64 ->
bv_unsigned a <= x -> x < y -> y <= bv_unsigned a + bv_unsigned sz ->
(y <= lo \/ hi <= x) ->
exists e, In e (iv_subtract a sz lo hi) /\ elo e <= x /\ y <= ehi e.
Proof.
intros a sz lo hi x y Hlh Hhi Hwf Hax Hxy Hy Hd. unfold iv_subtract.
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

#[using="Type"] Lemma iv_subtract_pwdisj : forall a sz lo hi, 0 <= lo < hi -> hi < 2^64 -> bv_unsigned a + bv_unsigned sz <= 2^64 ->
pwdisj (iv_subtract a sz lo hi).
Proof.
intros a sz lo hi Hlh Hhi Hwf. unfold iv_subtract.
pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 sz). unfold bv_modulus in *.
destruct (Z.ltb_spec (bv_unsigned a) lo); destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); cbn [app].
- constructor; [|constructor; [intros e' []| constructor]]. intros e' [<-|[]].
unfold edisj, elo, ehi; cbn. rewrite !unsigned_lit by lia. left. lia.
- constructor; [intros e' []| constructor].
- constructor; [intros e' []| constructor].
- constructor.
Qed.

#[using="Type"] Lemma vmwf_subtract : forall maps lo hi, 0 <= lo < hi -> hi < 2^64 -> vmwf maps -> vmwf (maps_subtract maps lo hi).
Proof.
induction maps as [|[a sz] maps IH]; intros lo hi Hlh Hhi [Hb Hp]; [split; [intros e []| constructor]|].
inversion Hp; subst. assert (Hwf' : vmwf maps) by (split; [intros e He; apply Hb; right; exact He| assumption]).
specialize (IH lo hi Hlh Hhi Hwf'). destruct IH as [IHb IHp].
assert (Ha : elo (a, sz) < ehi (a, sz) <= 2^64) by (apply Hb; left; reflexivity). unfold elo, ehi in Ha; cbn in Ha.
cbn. split.
- intros e Hin. apply in_app_or in Hin as [Hin|Hin]; [|apply IHb; exact Hin].
pose proof (iv_subtract_sub a sz lo hi e ltac:(lia) ltac:(lia) ltac:(lia) Hhi Hin). lia.
- apply pwdisj_app; [apply iv_subtract_pwdisj; lia| exact IHp|].
intros e e' He He'. pose proof (iv_subtract_sub a sz lo hi e ltac:(lia) ltac:(lia) ltac:(lia) Hhi He) as S1.
destruct (maps_subtract_In _ _ _ _ He') as (e0 & H0 & H0').
assert (W0 : elo e0 < ehi e0 <= 2^64) by (apply Hb; right; exact H0). destruct e0 as [a0 s0]. unfold elo, ehi in W0; cbn in W0.
pose proof (iv_subtract_sub a0 s0 lo hi e' ltac:(lia) ltac:(lia) ltac:(lia) Hhi H0') as S2.
pose proof (H1 _ H0) as D. unfold edisj, elo, ehi in *. cbn in *. lia.
Qed.

#[using="Type"] Lemma wcov_mono : forall maps maps' lo hi, (forall e, In e maps -> In e maps') -> wcov maps lo hi -> wcov maps' lo hi.
Proof. intros maps maps' lo hi Hs Hc x Hx. destruct (Hc x Hx) as (e & He & Hr). exists e. auto. Qed.

#[using="Type"] Lemma map_contains_intro : forall maps lo n e,
In e maps -> elo e <= bv_unsigned lo -> bv_unsigned lo + bv_unsigned n <= ehi e ->
map_contains maps lo n = true.
Proof.
intros maps lo n e Hin H1 H2. unfold map_contains. apply existsb_exists. exists e. split; [exact Hin|].
unfold elo, ehi in *. rewrite (proj2 (Z.leb_le _ _) H1), (proj2 (Z.leb_le _ _) H2). reflexivity.
Qed.

#[using="Type"] Lemma map_has_intro : forall maps lo n, In (lo, n) maps -> map_has maps lo n = true.
Proof.
intros maps lo n Hin. unfold map_has. apply existsb_exists. exists (lo, n). split; [exact Hin|].
cbn. rewrite !bv_eqb_refl. reflexivity.
Qed.

Definition brk_disj (L : mled) (b n : Z) : Prop :=
forall b0 l0, ld_brkreg L = Some (b0, l0) -> b + n <= b0 + PGSZ \/ b0 + l0 <= b.

Record KL (L : mled) (pbrk : Z) (mo : Model) : Prop := mkKL {
kl_halt : m_halted mo = None;
kl_lazy : m_vm_lazy mo = [];
kl_ceil : alloc_top (m_vmmaps mo) = alloc_ceiling;
kl_wf : vmwf (vm_maps (m_vmmaps mo));
kl_resv : ld_resv L = map wwZ (vm_reserved (m_vmmaps mo));
kl_resv_wf : forall e, In e (vm_reserved (m_vmmaps mo)) -> ehi e <= 2^64;
kl_resv_top : forall e, In e (vm_reserved (m_vmmaps mo)) -> ehi e <= bv_unsigned (vm_start_brk (m_vmmaps mo));
kl_start : 0 < bv_unsigned (vm_start_brk (m_vmmaps mo))
/\ bv_unsigned (vm_start_brk (m_vmmaps mo)) mod PGSZ = 0
/\ bv_unsigned (vm_start_brk (m_vmmaps mo)) <= bv_unsigned (vm_brk (m_vmmaps mo))
/\ bv_unsigned (vm_start_brk (m_vmmaps mo)) + 4 * PGSZ <= alloc_ceiling;
kl_groups : forall b l, In (b, l) (ld_groups L) ->
0 < l < LEN_MAX /\ 0 < b /\ b mod PGSZ = 0 /\ b + mmap_len l <= alloc_ceiling
/\ In (went b (mmap_len l)) (vm_maps (m_vmmaps mo)) /\ brk_disj L b (mmap_len l)
/\ region_free (vm_noaccess (m_vmmaps mo)) (wz b) (wz (mmap_len l)) = true;
kl_gresv : forall b l, In (b, l) (ld_groups L) ->
region_free (vm_reserved (m_vmmaps mo)) (wz b) (wz (mmap_len l)) = true;
kl_metas : forall b l k, In (b, l, k) (ld_metas L) ->
0 < l < LEN_MAX /\ 0 < b /\ b mod PGSZ = 0 /\ b + mmap_len l <= alloc_ceiling
/\ 0 <= k /\ (1 + k) * PGSZ <= mmap_len l
/\ In (went b (mmap_len l)) (vm_maps (m_vmmaps mo)) /\ brk_disj L b (mmap_len l)
/\ (forall q, 1 + k <= q -> (q + 1) * PGSZ <= mmap_len l ->
exists e, In e (vm_noaccess (m_vmmaps mo)) /\ elo e <= b + q * PGSZ /\ b + q * PGSZ + PGSZ <= ehi e);
kl_distinct : List.NoDup (map fst (ld_groups L) ++ map (fun m => fst (fst m)) (ld_metas L));
kl_na : forall e, In e (vm_noaccess (m_vmmaps mo)) ->
elo e < ehi e <= 2^64 /\
( (exists b l k, In (b, l, k) (ld_metas L) /\ b <= elo e /\ ehi e <= b + mmap_len l)
\/ (exists b0 l0, ld_brkreg L = Some (b0, l0) /\ b0 <= elo e /\ ehi e <= b0 + PGSZ
/\ In (went b0 (2 * PGSZ)) (vm_maps (m_vmmaps mo))) );
kl_brkreg : forall b l, ld_brkreg L = Some (b, l) ->
0 < b /\ b mod PGSZ = 0 /\ 2 * PGSZ <= l /\ l mod PGSZ = 0 /\ b + l <= alloc_ceiling
/\ wcov (vm_maps (m_vmmaps mo)) (b + PGSZ) (b + l);
kl_phase : match ld_brk L with
| BPUntried => vm_brk (m_vmmaps mo) = vm_start_brk (m_vmmaps mo) /\ ld_brkreg L = None
| BPQueried cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo))
/\ bv_unsigned (vm_brk (m_vmmaps mo)) = cur /\ pbrk = cur /\ ld_brkreg L = None
| BPGuard cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo))
/\ bv_unsigned (vm_brk (m_vmmaps mo)) = cur + 2 * PGSZ /\ pbrk = cur + 2 * PGSZ
/\ ld_brkreg L = None /\ cur + 2 * PGSZ <= alloc_ceiling
/\ In (went cur (2 * PGSZ)) (vm_maps (m_vmmaps mo))
/\ (forall b l, In (b, l) (ld_groups L) -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
/\ (forall b l k, In (b, l, k) (ld_metas L) -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
| BPLive => exists b l, ld_brkreg L = Some (b, l) /\ bv_unsigned (vm_brk (m_vmmaps mo)) = b + l /\ pbrk = b + l
| BPDead => True
end }.

Definition vm_only (mo mo' : Model) : Prop :=
m_fd mo' = m_fd mo /\ m_io mo' = m_io mo /\ m_fsys mo' = m_fsys mo /\
m_proc mo' = m_proc mo /\ m_lim mo' = m_lim mo /\ m_time mo' = m_time mo /\
vm_init_sp (m_vmmaps mo') = vm_init_sp (m_vmmaps mo).

#[using="Type"] Lemma vm_only_refl : forall mo, vm_only mo mo.
Proof. intros mo. unfold vm_only. repeat split; reflexivity. Qed.
#[using="Type"] Lemma vm_only_trans : forall a b c, vm_only a b -> vm_only b c -> vm_only a c.
Proof. intros a b c H1 H2. unfold vm_only in *. intuition congruence. Qed.
#[using="Type"] Lemma vm_only_with_vmmaps : forall h mo,
vm_init_sp h = vm_init_sp (m_vmmaps mo) -> vm_only mo (with_vmmaps h mo).
Proof. intros h mo E. unfold vm_only, with_vmmaps. cbn. repeat split; try reflexivity. exact E. Qed.
#[using="Type"] Lemma vm_only_alloc_top : forall mo mo', vm_only mo mo' -> alloc_top (m_vmmaps mo') = alloc_top (m_vmmaps mo).
Proof. intros mo mo' H. unfold vm_only in H. unfold alloc_top. destruct H as (_ & _ & _ & _ & _ & _ & ->). reflexivity. Qed.
#[using="Type"] Lemma vm_only_with_vm_backing : forall lz mt mo, vm_only mo (with_vm_backing lz mt mo).
Proof. intros. unfold vm_only, with_vm_backing. cbn. repeat split; reflexivity. Qed.
#[using="Type"] Lemma vm_only_forget : forall lo hi mo, vm_only mo (vm_forget_range lo hi mo).
Proof. intros. unfold vm_forget_range. apply vm_only_with_vm_backing. Qed.

#[using="Type"] Lemma m_vmmaps_with_vmmaps : forall h mo, m_vmmaps (with_vmmaps h mo) = h. Proof. reflexivity. Qed.
#[using="Type"] Lemma m_halted_with_vmmaps : forall h mo, m_halted (with_vmmaps h mo) = m_halted mo. Proof. reflexivity. Qed.
#[using="Type"] Lemma m_vm_lazy_with_vmmaps : forall h mo, m_vm_lazy (with_vmmaps h mo) = m_vm_lazy mo. Proof. reflexivity. Qed.
#[using="Type"] Lemma m_vmmaps_forget : forall lo hi mo, m_vmmaps (vm_forget_range lo hi mo) = m_vmmaps mo. Proof. reflexivity. Qed.
#[using="Type"] Lemma m_halted_forget : forall lo hi mo, m_halted (vm_forget_range lo hi mo) = m_halted mo. Proof. reflexivity. Qed.
#[using="Type"] Lemma m_vm_lazy_forget : forall lo hi mo, m_vm_lazy (vm_forget_range lo hi mo) = maps_subtract (m_vm_lazy mo) lo hi. Proof. reflexivity. Qed.
End RC__1.

Ltac mproj := rewrite ?m_vmmaps_forget, ?m_halted_forget, ?m_vm_lazy_forget,
?m_vmmaps_with_vmmaps, ?m_halted_with_vmmaps, ?m_vm_lazy_with_vmmaps in *;
cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base
set_metas set_groups set_brkph set_brkreg set_live ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live] in *.
Section RC__2. Context {RC__ : Q6q3.RunConsts}.

Definition hidden (P : Prop) : Prop := P.
#[using="Type"] Lemma mod0_lin : forall x, x mod PGSZ = 0 -> exists q, x = 4096 * q.
Proof. intros x H. exists (x / 4096). unfold PGSZ in H. pose proof (Z_div_mod_eq_full x 4096). lia. Qed.
#[using="Type"] Lemma mod0_lin' : forall x, x mod 4096 = 0 -> exists q, x = 4096 * q.
Proof. exact mod0_lin. Qed.
#[using="Type"] Lemma mod0_linp : forall x, x mod page_size = 0 -> exists q, x = 4096 * q.
Proof. exact mod0_lin. Qed.
End RC__2.
Ltac linearize_mods :=
repeat match goal with
| H : ?x mod PGSZ = 0 |- _ =>
let q := fresh "q" in let E := fresh "Hq" in
destruct (mod0_lin x H) as [q E]; change (hidden (x mod PGSZ = 0)) in H
| H : ?x mod 4096 = 0 |- _ =>
let q := fresh "q" in let E := fresh "Hq" in
destruct (mod0_lin' x H) as [q E]; change (hidden (x mod 4096 = 0)) in H
| H : ?x mod page_size = 0 |- _ =>
let q := fresh "q" in let E := fresh "Hq" in
destruct (mod0_linp x H) as [q E]; change (hidden (x mod page_size = 0)) in H
end.
Ltac unhide := unfold hidden in *.

Ltac kl_open HK := destruct HK as [Khalt Klazy Kceil Kwf Kresv Krwf Krt Kstart Kgr Kgrr Kme Kdis Kna Kreg Kph].
Section RC__3. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma KL_model_frame : forall L pbrk mo mo',
KL L pbrk mo -> m_vmmaps mo' = m_vmmaps mo -> m_vm_lazy mo' = m_vm_lazy mo -> m_halted mo' = None ->
KL L pbrk mo'.
Proof.
intros L pbrk mo mo' K E1 E2 Hh. kl_open K; constructor; rewrite ?E1, ?E2; auto.
Qed.

#[using="Type"] Lemma KL_vm_eq : forall L pbrk mo mo',
KL L pbrk mo -> m_halted mo' = None -> m_vm_lazy mo' = [] ->
vm_reserved (m_vmmaps mo') = vm_reserved (m_vmmaps mo) ->
vm_maps (m_vmmaps mo') = vm_maps (m_vmmaps mo) ->
vm_noaccess (m_vmmaps mo') = vm_noaccess (m_vmmaps mo) ->
vm_start_brk (m_vmmaps mo') = vm_start_brk (m_vmmaps mo) ->
vm_brk (m_vmmaps mo') = vm_brk (m_vmmaps mo) ->
vm_init_sp (m_vmmaps mo') = vm_init_sp (m_vmmaps mo) ->
KL L pbrk mo'.
Proof.
intros L pbrk mo mo' K Hh Hl H1 H2 H3 H4 H5 H6. kl_open K; constructor; unfold alloc_top in *; rewrite ?H1, ?H2, ?H3, ?H4, ?H5, ?H6; auto.
Qed.

Definition phase_inv (ph : brk_phase) (L : mled) (pbrk : Z) (mo : Model) : Prop :=
match ph with
| BPUntried => vm_brk (m_vmmaps mo) = vm_start_brk (m_vmmaps mo) /\ ld_brkreg L = None
| BPQueried cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo))
/\ bv_unsigned (vm_brk (m_vmmaps mo)) = cur /\ pbrk = cur /\ ld_brkreg L = None
| BPGuard cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo))
/\ bv_unsigned (vm_brk (m_vmmaps mo)) = cur + 2 * PGSZ /\ pbrk = cur + 2 * PGSZ
/\ ld_brkreg L = None /\ cur + 2 * PGSZ <= alloc_ceiling
/\ In (went cur (2 * PGSZ)) (vm_maps (m_vmmaps mo))
/\ (forall b l, In (b, l) (ld_groups L) -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
/\ (forall b l k, In (b, l, k) (ld_metas L) -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
| BPLive => exists b l, ld_brkreg L = Some (b, l) /\ bv_unsigned (vm_brk (m_vmmaps mo)) = b + l /\ pbrk = b + l
| BPDead => True
end.

#[using="Type"] Lemma KL_rephase : forall L ph pbrk pbrk' mo,
KL L pbrk mo -> phase_inv ph L pbrk' mo -> KL (set_brkph ph L) pbrk' mo.
Proof. intros L ph pbrk pbrk' mo K Hph. kl_open K; constructor; cbn; auto. Qed.

#[using="Type"] Lemma KL_dead : forall L pbrk pbrk' mo, KL L pbrk mo -> KL (set_brkph BPDead L) pbrk' mo.
Proof. intros. eapply KL_rephase; [eassumption| exact I]. Qed.

#[using="Type"] Lemma KL_set_live : forall L v pbrk mo, KL L pbrk mo -> KL (set_live v L) pbrk mo.
Proof. intros L v pbrk mo K. kl_open K; constructor; cbn; auto. Qed.

#[using="Type"] Lemma KL_pbrk_irrel : forall L pbrk pbrk' mo,
KL L pbrk mo -> match ld_brk L with BPUntried | BPDead => True | _ => pbrk' = pbrk end -> KL L pbrk' mo.
Proof.
intros L pbrk pbrk' mo K H. kl_open K; constructor; auto.
destruct (ld_brk L); auto; subst; auto.
Qed.

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

#[using="Type"] Lemma KL_ranges_free : forall L pbrk mo a n,
KL L pbrk mo ->
let h := m_vmmaps mo in
0 < a -> 0 < n -> a + n <= alloc_ceiling ->
region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 a) (Z_to_bv 64 n) = true ->
ranges_free (lranges L) a n = true.
Proof.
intros L pbrk mo a n HK h Ha Hn Hceil Hrf. pose proof alloc_ceiling_lt as Hcl.
assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit; lia).
assert (Un : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
pose proof (region_free_app_r _ _ _ _ Hrf) as Hrfm.
unfold ranges_free. apply forallb_forall. intros [b0 m0] Hin. cbn [fst snd]. unfold iv_disjoint.
enough (a + n <= b0 \/ b0 + m0 <= a) as D.
{ destruct D as [D|D]; [rewrite (proj2 (Z.leb_le _ _) D); reflexivity| rewrite (proj2 (Z.leb_le _ _) D); apply orb_true_r]. }
apply In_lranges in Hin as [H|[(b1 & l1 & H & E)|[(b1 & l1 & k & H & E)|(b1 & l1 & H & E)]]].
- rewrite (kl_resv _ _ _ HK) in H. apply in_map_iff in H as ([e sz] & E & H). unfold wwZ in E. cbn [fst snd] in E. injection E as <- <-.
pose proof (region_free_In _ _ _ _ _ Hrf (in_or_app _ _ _ (or_introl H))) as D.
unfold iv_overlap in D. rewrite Ua, Un in D.
destruct (Z.ltb_spec a (bv_unsigned e + bv_unsigned sz)); destruct (Z.ltb_spec (bv_unsigned e) (a + n)); cbn in D; try discriminate; lia.
- injection E as -> ->. pose proof (went_In_bounds _ _ _ b1 l1 HK (or_introl H)) as (B1 & B2 & B3 & B4 & B5 & B6).
pose proof (region_free_disj _ _ _ _ Hrfm B4) as D. rewrite B5, B6, Ua, Un in D. rewrite round_up_pg_eq. fold (mmap_len l1). exact D.
- injection E as -> ->. pose proof (went_In_bounds _ _ _ b1 l1 HK (or_intror (ex_intro _ k H))) as (B1 & B2 & B3 & B4 & B5 & B6).
pose proof (region_free_disj _ _ _ _ Hrfm B4) as D. rewrite B5, B6, Ua, Un in D. rewrite round_up_pg_eq. fold (mmap_len l1). exact D.
- injection E as -> ->. pose proof (kl_brkreg _ _ _ HK b1 l1 H) as (R1 & R2 & R3 & R4 & R5 & Rcov).
rewrite round_up_pg_aligned by (unfold PGSZ in R4; exact R4).

destruct (Z.le_gt_cases (a + n) (b1 + PGSZ)) as [|C1]; [left; lia|].
destruct (Z.le_gt_cases (b1 + l1) a) as [|C2]; [right; unfold PGSZ in *; lia|].
exfalso.

set (x := Z.max a (b1 + PGSZ)).
assert (Hx : b1 + PGSZ <= x < b1 + l1) by (unfold x, PGSZ in *; lia).
destruct (Rcov x Hx) as (e & He & Hex).
pose proof (region_free_disj _ _ _ _ Hrfm He) as D. rewrite Ua, Un in D. unfold x, PGSZ in *. lia.
Qed.

#[using="Type"] Lemma KL_lbrk_pages_ok : forall L pbrk mo lo len,
KL L pbrk mo ->
let h := m_vmmaps mo in
0 < lo -> 0 < len -> lo + len <= alloc_ceiling ->
region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 lo) (Z_to_bv 64 len) = true ->
lbrk_pages_ok L lo len = true.
Proof.
intros L pbrk mo lo len HK h Hlo Hlen Hceil Hrf.
unfold lbrk_pages_ok. rewrite (proj2 (Z.ltb_lt 0 lo)) by lia. rewrite (proj2 (Z.leb_le _ _) Hceil). cbn [andb].
eapply KL_ranges_free; eauto.
Qed.

End RC__3.
