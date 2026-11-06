(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Bool Lia Permutation.
From stdpp Require gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi QUZl Q7S0 Qfya QPiB Qatc QSfG QdBa QpFQ Ql2m QYTG QjcB QLaA QaiD Q1am QoCS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Qfya QPiB.Mq0 Qatc QSfG.Mq2 Q7S0 QSfG.Mq0 QdBa.Mq1 QdBa.Mq0 QpFQ Ql2m.Mq1 QPiB QdBa.Mq2 Ql2m.Mq2 QYTG.Mq1 QjcB QLaA QaiD QLaA.Mq0 Q1am QoCS.Mq1 Q1am.Mq1.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma res_excl a o : a mod 16 = 0 -> 12 <= o mod 16 -> ~ (a <= o < a + 12).
Proof.
intros Ha Ho [H1 H2]. pose proof (Z.div_mod a 16 ltac:(lia)) as Da. pose proof (Z.div_mod o 16 ltac:(lia)) as Do.
pose proof (Z.mod_pos_bound o 16 ltac:(lia)) as Bo. rewrite Ha in Da.
set (qa := a / 16) in *. set (qo := o / 16) in *. set (r := o mod 16) in *. clearbody qa qo r. lia.
Qed.

#[using="Type"] Lemma one5_iff_create (A B E : Prop) (C D : Prop) : one5 A B False False E -> ~ C -> ~ D -> one5 A B C D E.
Proof. unfold one5. tauto. Qed.

Section CREATE.
Variables (X X' : extras) (st st' : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (m p : aptr) (ai : Z) (mr' : meta).
Hypothesis INV : INVL X st L BL LS.
Hypothesis IDLE : In m (x_idle X).

Let sc' := m_sizeclass mr'.
Let last' := m_last_idx mr'.
Let cnt := last' + 1.
Let stride' := get_stride mr'.
Hypothesis R_prev : m_prev mr' = None.
Hypothesis R_next : m_next mr' = None.
Hypothesis R_mem : m_mem mr' = Some p.
Hypothesis R_freeable : m_freeable mr' = 1.
Hypothesis R_maplen : 0 <= m_maplen mr'.
Hypothesis R_li : 0 <= last' <= 31.
Hypothesis R_ai : 0 <= ai <= last'.
Hypothesis R_full0 : sc' = 0 -> ai = last'.
Hypothesis R_sc : (0 <= sc' < 48 /\ m_maplen mr' <= 256) \/ (sc' = 63 /\ last' = 0 /\ m_maplen mr' <> 0).
Hypothesis R_masks : 0 <= m_avail mr' /\ 0 <= m_freed mr'
/\ (forall i, 0 <= i -> tbit (m_avail mr') i = true -> i <= ai)
/\ (forall i, 0 <= i -> tbit (m_freed mr') i = true -> i <= last')
/\ (forall i, 0 <= i -> tbit (m_avail mr') i = true -> tbit (m_freed mr') i = true -> False)
/\ (forall i, ai < i <= last' -> tbit (m_freed mr') i = true).
Hypothesis R_stride : sc' < 48 ->
(stride' <= UNIT * size_class sc' \/ 28 <= sc') /\ (last' = 0 -> m_maplen mr' <> 0 /\ 27 <= sc') /\ stride' * cnt < 2^20.
Hypothesis R_stride16 : 16 <= stride' /\ stride' mod 16 = 0.
Hypothesis R_align : 0 <= snd p /\ snd p mod UNIT = 0.

Hypothesis X_fresh : x_fresh X' = Some m \/ (sc' = 63 /\ x_fresh X' = x_fresh X).
Hypothesis X_fresh_old : x_fresh X = None.
Hypothesis X_idle : forall x, In x (x_idle X') -> In x (x_idle X) /\ x <> m.
Hypothesis X_zomb : x_zomb X' = x_zomb X.
Hypothesis X_nozomb : x_zomb X = [].
Hypothesis X_part : forall i, 0 <= i <= last' ->
one5 (tbit (m_avail mr') i = true) (tbit (m_freed mr') i = true) False False (x_pend X' = Some (fst p, snd p + UNIT + stride' * i)).
Hypothesis X_pend' : forall s, x_pend X' = Some s -> exists i, 0 <= i <= last' /\ s = (fst p, snd p + UNIT + stride' * i).

Hypothesis NOPART : ai < last' -> LS (LActive sc') = [].

Hypothesis SITE :
(m_maplen mr' <> 0 /\ snd p = 0 /\ x_orph X = Some (fst p) /\ x_orph X' = None /\ x_pend X = None
/\ exists r, s_regions st !! (fst p) = Some r /\ r_kind r = RKGroup /\ m_maplen mr' * 4096 = round_up_pg (r_len r)
/\ snd p + UNIT + stride' * cnt <= m_maplen mr' * 4096)
\/ (m_maplen mr' = 0 /\ x_pend X = Some p /\ x_pend X' = None /\ x_orph X' = x_orph X /\ x_orph X = None
/\ exists pm ip bpm, s_slots st !! p = Some (pm, ip) /\ hosts st bpm pm /\ fst bpm = fst p /\ 0 <= ip <= m_last_idx (MR st pm)
/\ p = (fst bpm, sstart (MR st pm) ip)
/\ snd p + UNIT + stride' * cnt <= sstart (MR st pm) ip + get_stride (MR st pm)
/\ sc' < m_sizeclass (MR st pm) < 48 /\ get_stride (MR st pm) = UNIT * size_class (m_sizeclass (MR st pm))
/\ (exists v3, known st (fst p, snd p - 3) v3 /\ Z.land v3 31 = ip /\ 0 <= v3 < 256)
/\ known st (fst p, snd p - 2) (byte_of ((snd p - snd bpm - UNIT) / UNIT) 0)
/\ known st (fst p, snd p - 1) (byte_of ((snd p - snd bpm - UNIT) / UNIT) 1)
/\ 0 <= (snd p - snd bpm - UNIT) / UNIT < 2^16).

Hypothesis SH_hdr0 : forall i, 0 <= i <= cnt -> known st (fst p, snd p + UNIT + stride' * i - IB) 0.
Hypothesis SH_ghdr : forall o v tk, snd p <= o < snd p + 12 -> r_cells (get_shadow st (fst p)) !! o = Some (v, tk) -> (tk < s_tick st)%N.

Hypothesis E_metas : s_metas st' = <[m := mr']> (s_metas st).
Hypothesis E_groups : s_groups st' = <[p := mkGhdr (Some m) ai]> (s_groups st).
Hypothesis E_slots : forall s, s_slots st' !! s =
if (fst s =? fst p)%N && (0 <=? snd s - snd p - UNIT) && ((snd s - snd p - UNIT) mod stride' =? 0) && ((snd s - snd p - UNIT) / stride' <? cnt)
then Some (m, (snd s - snd p - UNIT) / stride') else s_slots st !! s.
Hypothesis E_shadow : s_shadow st' = s_shadow (hdr_havoc p st).
Hypotheses (E_regions : s_regions st' = s_regions st) (E_areas : s_areas st' = s_areas st) (E_next_rid : s_next_rid st' = s_next_rid st)
(E_tick : s_tick st' = s_tick st) (E_secret : s_secret st' = s_secret st) (E_reserved : s_reserved st' = s_reserved st).
Hypothesis E_ctx :
c_secret (s_ctx st') = c_secret (s_ctx st) /\ c_init_done (s_ctx st') = c_init_done (s_ctx st)
/\ c_free_meta_head (s_ctx st') = c_free_meta_head (s_ctx st) /\ c_avail_meta (s_ctx st') = c_avail_meta (s_ctx st)
/\ c_avail_meta_count (s_ctx st') = c_avail_meta_count (s_ctx st) /\ c_avail_meta_area_count (s_ctx st') = c_avail_meta_area_count (s_ctx st)
/\ c_meta_alloc_shift (s_ctx st') = c_meta_alloc_shift (s_ctx st) /\ c_meta_area_head (s_ctx st') = c_meta_area_head (s_ctx st)
/\ c_meta_area_tail (s_ctx st') = c_meta_area_tail (s_ctx st) /\ c_avail_meta_areas (s_ctx st') = c_avail_meta_areas (s_ctx st)
/\ c_active (s_ctx st') = c_active (s_ctx st) /\ c_unmap_seq (s_ctx st') = c_unmap_seq (s_ctx st)
/\ c_bounces (s_ctx st') = c_bounces (s_ctx st) /\ c_seq (s_ctx st') = c_seq (s_ctx st) /\ c_brk (s_ctx st') = c_brk (s_ctx st).
Hypothesis E_mc : 0 <= c_mmap_counter (s_ctx st') < 2^32.
Hypothesis E_usage : forall sc0, 0 <= sc0 < 48 -> usage st' sc0 = usage st sc0 + (if sc0 =? sc' then cnt else 0).
Hypothesis E_usage_keys : forall sc0 v, c_usage (s_ctx st') !! sc0 = Some v -> 0 <= sc0 < 48.

Let IR := proj1 INV. Let IA := proj1 (proj2 INV). Let IM := proj1 (proj2 (proj2 INV)). Let IL := proj1 (proj2 (proj2 (proj2 INV))).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))). Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Let ISH := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

Ltac slim := try clear SITE; try clear E_ctx; try clear E_slots; try clear X_part; try clear X_pend'; try clear R_masks; try clear R_stride; try clear R_sc;
try clear E_usage; try clear E_usage_keys; try clear SH_hdr0; try clear SH_ghdr; try clear X_idle; try clear NOPART.
Local Tactic Notation "lia" := slim; Lia.lia.
Local Tactic Notation "nia" := slim; Lia.nia.

#[using="RC__ X L BL LS INV IDLE IM"] Lemma m_meta0 : s_metas st !! m = Some meta0. Proof. exact (proj1 (im_idle _ _ _ IM m IDLE)). Qed.
#[using="RC__ X st L BL INV IDLE IM"] Lemma m_unlisted h : ~ In m (LS h). Proof. intros H. apply (proj2 (im_idle _ _ _ IM m IDLE)). exists h. exact H. Qed.
#[using="RC__ X L BL LS INV IDLE IM"] Lemma MRm : MR st m = meta0. Proof. unfold MR, get_meta_rec. rewrite m_meta0. reflexivity. Qed.
#[using="RC__ X L BL LS INV IDLE"] Lemma m_not_live : ~ live_group st m. Proof. exact (idle_not_live _ _ _ _ _ INV m IDLE). Qed.

#[using="E_metas"] Lemma C_MR x : MR st' x = if aptr_eqb x m then mr' else MR st x.
Proof. unfold MR, get_meta_rec. rewrite E_metas. destruct (aptr_eqb_spec x m) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity. Qed.
#[using="mr' E_metas"] Lemma C_MR_other x : x <> m -> MR st' x = MR st x. Proof. intros NE. rewrite C_MR, aptr_eqb_neq by exact NE. reflexivity. Qed.
#[using="st E_metas"] Lemma C_MR_m : MR st' m = mr'. Proof. rewrite C_MR, aptr_eqb_refl. reflexivity. Qed.
#[using="RC__ X X' L BL LS m p ai mr' INV IDLE sc' last' cnt stride' R_li R_ai R_sc R_masks R_stride R_stride16 R_align X_fresh SITE E_metas E_ctx E_mc IM"] Lemma C_keys x : s_metas st' !! x <> None <-> s_metas st !! x <> None.
Proof. rewrite E_metas. destruct (aptr_eq_dec x m) as [->|NE]; [rewrite lookup_insert_eq, m_meta0; split; discriminate| rewrite lookup_insert_ne by congruence; tauto]. Qed.

#[using="RC__ X X' L BL LS mr' INV sc' last' cnt stride' SITE IR IM IS"] Lemma p_free : s_groups st !! p = None.
Proof.
destruct SITE as [(Hml & P0 & HO & _ & _ & r & Hr & Hk & _)|(Hml & HP & _ & _ & _ & pm & ip & bpm & Hs & Hpm & Hf & Hip & Ep & _)].
- destruct (ir_orph _ _ _ IR _ HO) as (r' & _ & _ & NG). apply NG. reflexivity.
- destruct Hpm as [aipm Hpm]. pose proof (is_part _ _ _ IS _ _ _ ip Hpm Hip) as P. cbn zeta in P.
rewrite (slot_start'_eq _ _ _ IM _ _ _ (ex_intro _ aipm Hpm)), <- Ep, HP in P. unfold one5 in P.
destruct (s_groups st !! p) eqn:E; [| reflexivity]. exfalso. destruct P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & nDE). apply nDE. split; [congruence| reflexivity].
Qed.

#[using="E_groups"] Lemma C_groups b : s_groups st' !! b = if aptr_eqb b p then Some (mkGhdr (Some m) ai) else s_groups st !! b.
Proof. rewrite E_groups. destruct (aptr_eqb_spec b p) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity. Qed.
#[using="ai E_groups"] Lemma C_hosts b x : hosts st' b x <-> (b = p /\ x = m) \/ (b <> p /\ hosts st b x).
Proof.
unfold hosts. rewrite C_groups. destruct (aptr_eqb_spec b p) as [->|NE].
- split; [intros [a H]; inversion H; auto| intros [[_ ->]|[NE _]]; [exists ai; reflexivity| congruence]].
- split; [intros H; right; auto| intros [[E _]|[_ H]]; [congruence| exact H]].
Qed.
#[using="RC__ X X' L BL LS m p ai mr' INV sc' last' cnt stride' SITE E_groups IR IM IS"] Lemma C_hosts_old b x : hosts st b x -> hosts st' b x.
Proof. intros H. apply C_hosts. destruct (aptr_eq_dec b p) as [->|NE]; [| right; auto]. destruct H as [a H]. rewrite p_free in H. discriminate. Qed.
#[using="RC__ X L BL LS INV IDLE"] Lemma C_hosts_old_ne b x : hosts st b x -> x <> m.
Proof. intros H ->. exact (m_not_live (ex_intro _ b H)). Qed.
#[using="RC__ X L BL LS m mr' INV IDLE E_metas"] Lemma C_MR_hosted b x : hosts st b x -> MR st' x = MR st x.
Proof. intros H. apply C_MR_other. exact (C_hosts_old_ne b x H). Qed.

#[using="R_mem"] Lemma gbase' : gbase mr' = p. Proof. unfold gbase. rewrite R_mem. reflexivity. Qed.
#[using="R_mem"] Lemma sstart' i : sstart mr' i = snd p + UNIT + stride' * i. Proof. unfold sstart. rewrite gbase'. reflexivity. Qed.
#[using="R_mem"] Lemma slot' i : slot_start' mr' i = (fst p, snd p + UNIT + stride' * i). Proof. rewrite slot_start'_sstart, gbase', sstart'. reflexivity. Qed.

Definition nslot (s : aptr) : Prop := exists j, 0 <= j < cnt /\ s = (fst p, snd p + UNIT + stride' * j).
#[using="R_stride16 E_slots"] Lemma C_slots s : (s_slots st' !! s = s_slots st !! s /\ ~ nslot s) \/ (exists j, 0 <= j < cnt /\ s = (fst p, snd p + UNIT + stride' * j) /\ s_slots st' !! s = Some (m, j)).
Proof.
unfold nslot. pose proof (E_slots s) as ES. destruct R_stride16 as [SP SM]. clear - ES SP SM. subst cnt last'.
rewrite ES. clear ES. set (d := snd s - snd p - UNIT).
destruct ((fst s =? fst p)%N && (0 <=? d) && (d mod stride' =? 0) && (d / stride' <? m_last_idx mr' + 1)) eqn:E.
- right. apply Bool.andb_true_iff in E as [E E4]. apply Bool.andb_true_iff in E as [E E3]. apply Bool.andb_true_iff in E as [E1 E2].
apply N.eqb_eq in E1. apply Z.leb_le in E2. apply Z.eqb_eq in E3. apply Z.ltb_lt in E4.
exists (d / stride'). split; [split; [apply Z.div_pos; lia| exact E4]|]. split; [| reflexivity].
pose proof (Z.div_mod d stride' ltac:(lia)) as DM. rewrite E3, Z.add_0_r in DM.
destruct s as [sr so]. cbn in E1, d |- *. subst sr. f_equal. lia.
- left. split; [reflexivity|]. intros (j & Hj & Es). subst s. cbn in d.
assert (Ed : d = stride' * j) by (unfold d; lia). clearbody d.
rewrite N.eqb_refl in E. cbn in E.
assert (E2 : (0 <=? d) = true) by (apply Z.leb_le; rewrite Ed; nia). rewrite E2 in E. cbn in E.
assert (E3 : (d mod stride' =? 0) = true) by (apply Z.eqb_eq; rewrite Ed, Z.mul_comm; apply Z_mod_mult). rewrite E3 in E. cbn in E.
assert (E4 : (d / stride' <? m_last_idx mr' + 1) = true) by (apply Z.ltb_lt; rewrite Ed, Z.mul_comm, Z_div_mult by lia; lia). rewrite E4 in E. discriminate.
Qed.
#[using="m R_stride16 E_slots"] Lemma C_slots_old s : ~ nslot s -> s_slots st' !! s = s_slots st !! s.
Proof. intros N. destruct (C_slots s) as [[E _]|(j & Hj & Es & _)]; [exact E|]. exfalso. apply N. exists j. auto. Qed.
#[using="st R_stride16 E_slots"] Lemma C_slots_new j : 0 <= j < cnt -> s_slots st' !! (fst p, snd p + UNIT + stride' * j) = Some (m, j).
Proof.
intros Hj. destruct (C_slots (fst p, snd p + UNIT + stride' * j)) as [[_ N]|(j' & Hj' & Es & E)]; [exfalso; apply N; exists j; auto|].
rewrite E. inversion Es. destruct R_stride16 as [SP _]. assert (j' = j) by (clear - H0 SP Hj Hj'; nia). subst. reflexivity.
Qed.

#[using="R_stride16"] Lemma new_key_range j : 0 <= j < cnt -> snd p < snd p + UNIT + stride' * j /\ snd p + UNIT + stride' * j + 16 <= snd p + UNIT + stride' * cnt.
Proof. intros Hj. destruct R_stride16 as [SP _]. clear - Hj SP. subst cnt last'. unfold UNIT. split; [nia|]. assert (stride' * j + stride' <= stride' * (m_last_idx mr' + 1)) by nia. lia. Qed.

#[using="RC__ X X' L BL LS INV sc' R_stride16 SITE IR IM IG IS"] Lemma old_slot_not_new s x i : s_slots st !! s = Some (x, i) -> ~ nslot s.
Proof.
intros Hs (j & Hj & ->). destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bx Hx] & Hi & Es).
rewrite (slot_start'_eq _ _ _ IM _ _ _ Hx) in Es. inversion Es.
destruct (new_key_range j Hj) as [K1 K2].
destruct SITE as [(Hml & P0 & HO & _ & _ & r & Hr & Hk & _)|(Hml & HP & _ & _ & _ & pm & ip & bpm & Hps & Hpm & Hf & Hip & Ep & FIT & _)].
-
destruct (ir_orph _ _ _ IR _ HO) as (r' & _ & _ & NG). destruct Hx as [a Hxx]. rewrite (NG bx) in Hxx; [discriminate|]. rewrite <- H0. reflexivity.
-
destruct Hpm as [aipm Hpm'].
assert (NH : s_groups st !! (fst bpm, sstart (MR st pm) ip) = None) by (rewrite <- Ep; exact p_free).
assert (Hf2 : fst bx = fst bpm) by (rewrite Ep in H0; cbn in H0; congruence).
assert (Hi2 : 0 <= i <= m_last_idx (MR st x) + 1) by (clear - Hi; lia).
pose proof (@sep_hdr0 _ _ _ _ IM IG IS pm bpm ip (ex_intro _ aipm Hpm') Hip NH x bx i Hx Hf2 Hi2) as D.
rewrite sstart_succ in D. rewrite Ep in H1, K1, K2, FIT. cbn in H1, K1, K2, FIT.
assert (NEQ : x <> pm \/ i <> ip).
{ destruct (aptr_eq_dec x pm) as [->|]; [right| left; congruence]. intros ->. clear - H1 K1. lia. }
specialize (D NEQ). clear - D H1 K1 K2 FIT Hj. lia.
Qed.

#[using="RC__ X X' L BL LS INV sc' R_stride16 R_align SITE IR IM IG IS"] Lemma old_hosts_not_new b x : hosts st b x -> ~ nslot b.
Proof.
intros Hx N. destruct (hosts_ok _ _ _ IG _ _ Hx) as (a & Hb & GO).
destruct (Z.eq_dec (m_maplen (MR st x)) 0) as [Hml|Hml].
- destruct (g_nest _ _ _ _ _ _ GO Hml) as (px & ix & Hs & _). exact (old_slot_not_new _ _ _ Hs N).
- destruct (g_top _ _ _ _ _ _ GO Hml) as [B0 _]. destruct N as (j & Hj & ->). cbn in B0. destruct (new_key_range j Hj) as [K1 K2]. destruct R_align as [A0 _]. clear - B0 K1 A0. lia.
Qed.

#[using="R_stride16"] Lemma p_not_new : ~ nslot p.
Proof. intros (j & Hj & E). destruct (new_key_range j Hj) as [K _]. apply (f_equal snd) in E. cbn in E. clear - K E. lia. Qed.

#[using="RC__ X X' st L LS INV sc' R_stride16 SITE IR IM IG IS"] Lemma blk_not_new k : In k BL -> ~ nslot (bslot k).
Proof. intros Hk. destruct (is_blocks _ _ _ IS k Hk) as (x & i & Hs & _). exact (old_slot_not_new _ _ _ Hs). Qed.

#[using="RC__ X X' L BL LS INV sc' R_stride16 R_align SITE IR IM IG IS"] Lemma new_not_group j : 0 <= j < cnt -> s_groups st !! (fst p, snd p + UNIT + stride' * j) = None.
Proof.
intros Hj. destruct (s_groups st !! (fst p, snd p + UNIT + stride' * j)) as [h|] eqn:E; [| reflexivity]. exfalso.
destruct (im_hdr _ _ _ IM _ _ E) as (x & Ex & _). apply (old_hosts_not_new (fst p, snd p + UNIT + stride' * j) x); [| exists j; auto].
destruct h as [hm ha]. cbn in Ex. subst hm. exists ha. exact E.
Qed.

#[using="RC__ X X' L BL LS m p ai INV IDLE stride' SITE E_metas E_groups IR IM IS"] Lemma gcnt_C sc0 : gcnt st' sc0 = (if sc' =? sc0 then cnt else 0) + gcnt st sc0.
Proof.
rewrite !gcnt_unfold, E_groups.
rewrite (zsum_perm _ _ (Permutation_map (gterm st' sc0) (map_to_list_insert (s_groups st) p (mkGhdr (Some m) ai) p_free))). cbn.
unfold gterm at 1. cbn. rewrite C_MR_m. fold sc' cnt. f_equal.
f_equal. apply map_ext_in. intros [b hb] Hin. apply In_map_to_list_regions in Hin || (apply (proj2 (list_elem_of_In _ _)) in Hin; apply elem_of_map_to_list in Hin).
unfold gterm. cbn. destruct (g_meta hb) as [x|] eqn:Ex; [| reflexivity].
rewrite (C_MR_other x); [reflexivity|]. intros ->.
destruct (im_hdr _ _ _ IM _ _ Hin) as (x' & Ex' & Hmem & _). rewrite Ex in Ex'. inversion Ex'. subst x'. rewrite MRm in Hmem. discriminate.
Qed.

#[using="E_ctx"] Lemma C_get_head h : get_head st' h = get_head st h.
Proof.
destruct E_ctx as (_ & _ & F3 & _ & _ & _ & _ & _ & _ & _ & F11 & _). destruct h; cbn; unfold active, ctx; rewrite ?F11, ?F3; reflexivity.
Qed.
#[using="E_ctx"] Lemma C_frontier rid r : frontier st' rid r = frontier st rid r.
Proof. destruct E_ctx as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F10 & _). unfold frontier. rewrite F10. reflexivity. Qed.

#[using="RC__ X L BL LS INV ISH"] Lemma C_TK u hl : r_hav (get_shadow st (fst p)) !! u = Some hl -> hl_ticks hl (s_tick st).
Proof.
intros Hu ch Hin. unfold get_shadow in Hu. destruct (s_shadow st !! fst p) as [sh|] eqn:E; cbn in Hu.
- exact (proj1 (proj2 (ish_ticks _ _ ISH _ _ E)) u hl ch Hu Hin).
- rewrite lookup_empty in Hu. discriminate.
Qed.
#[using="RC__ X L BL LS INV R_align E_shadow ISH"] Lemma C_read_out q : ~ (fst q = fst p /\ snd p <= snd q < snd p + 12) ->
cell_read (get_shadow st' (fst q)) (snd q) = cell_read (get_shadow st (fst q)) (snd q).
Proof. intros Hq. rewrite (get_shadow_ext (hdr_havoc p st) st' (fst q) E_shadow). apply (cell_read_hdr_havoc_out p st (proj2 R_align) C_TK q Hq). Qed.
#[using="RC__ X L BL LS INV R_align E_shadow ISH"] Lemma C_known_out q v : ~ (fst q = fst p /\ snd p <= snd q < snd p + 12) -> known st q v -> known st' q v.
Proof. intros Hq K. unfold known, SHd in *. rewrite C_read_out by exact Hq. exact K. Qed.
#[using="RC__ X L BL LS INV R_align E_shadow ISH"] Lemma C_unknown_out q : ~ (fst q = fst p /\ snd p <= snd q < snd p + 12) -> unknown st q -> unknown st' q.
Proof. intros Hq K. unfold unknown, SHd in *. rewrite C_read_out by exact Hq. exact K. Qed.
#[using="st mr' sc' last' cnt stride' R_align SH_ghdr E_shadow E_next_rid E_tick"] Lemma C_unknown_hdr o : 0 <= o < 12 -> unknown st' (fst p, snd p + o).
Proof.
intros Ho. unfold unknown, SHd. cbn [fst snd]. rewrite (get_shadow_ext (hdr_havoc p st) st' (fst p) E_shadow).
apply (cell_read_hdr_havoc_in p st (proj2 R_align) (fst p, snd p + o)); [reflexivity| cbn; lia|].
cbn [fst snd]. intros v tk H. apply (SH_ghdr (snd p + o) v tk); [clear - Ho; lia| exact H].
Qed.

#[using="RC__ X st' L BL LS p mr' INV sc' last' cnt stride' R_stride16 R_align E_next_rid E_tick IM IG"] Lemma hdr0_res b x i : hosts st b x -> (sstart (MR st x) i - IB) mod 16 = 12.
Proof.
intros Hx. pose proof (stride_ge _ _ _ IG _ _ Hx) as [SG SM]. destruct (hosts_ok _ _ _ IG _ _ Hx) as (a & Hb & GO). pose proof (g_align _ _ _ _ _ _ GO) as [A0 A16].
unfold sstart, IB, UNIT in *. rewrite (hosts_gbase _ _ _ IM _ _ Hx).
pose proof (Z.div_mod (snd b) 16 ltac:(lia)) as D1. rewrite A16 in D1. pose proof (Z.div_mod (get_stride (MR st x)) 16 ltac:(lia)) as D2. rewrite SM in D2.
replace (snd b + 16 + get_stride (MR st x) * i - 4) with (12 + (snd b / 16 + get_stride (MR st x) / 16 * i) * 16) by nia.
rewrite Z_mod_plus_full. reflexivity.
Qed.

#[using="RC__ X X' L BL LS m p ai mr' INV sc' last' cnt stride' R_li R_ai R_sc R_masks R_stride R_stride16 R_align X_fresh SITE SH_ghdr E_shadow E_next_rid E_tick E_ctx E_mc ISH"] Lemma C_unknown_any q : unknown st q -> unknown st' q.
Proof.
intros U. destruct (N.eq_dec (fst q) (fst p)) as [E|NE]; [| apply C_unknown_out; [tauto| exact U]].
destruct (Z.lt_ge_cases (snd q) (snd p)) as [L1|G1]; [apply C_unknown_out; [lia| exact U]|].
destruct (Z.lt_ge_cases (snd q) (snd p + 12)) as [L2|G2]; [| apply C_unknown_out; [lia| exact U]].
replace q with (fst p, snd p + (snd q - snd p)) by (destruct q; cbn in *; subst; f_equal; lia). apply C_unknown_hdr. lia.
Qed.

#[using="RC__ X L BL LS p INV R_align E_shadow ISH"] Lemma C_known_res q v : 12 <= snd q mod 16 -> known st q v -> known st' q v.
Proof. intros R K. apply C_known_out; [| exact K]. intros [_ H]. exact (res_excl _ _ (proj2 R_align) R H). Qed.

#[using="RC__ X X' L LS mr' INV sc' last' cnt stride' SITE IR IM IG IS"] Lemma blk_clear k x i : In k BL -> s_slots st !! bslot k = Some (x, i) -> fst (bslot k) = fst p ->
snd (bslot k) + get_stride (MR st x) - IB <= snd p \/ snd p + 12 <= snd (bslot k) - IB.
Proof.
intros Hk Hs Hf. destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bx Hx] & Hi & Es).
destruct SITE as [(Hml & P0 & HO & _)|(Hml & HP & _ & _ & _ & pm & ip & bpm & Hps & Hpm & Hfp & Hip & Ep & _)].
- exfalso. destruct (ir_orph _ _ _ IR _ HO) as (r' & _ & _ & NG). destruct Hx as [a Hxx].
rewrite (NG bx) in Hxx; [discriminate|]. rewrite (slot_start'_eq _ _ _ IM _ _ _ (ex_intro _ a Hxx)) in Es. rewrite Es in Hf. exact Hf.
- destruct Hpm as [aipm Hpm']. rewrite (slot_start'_eq _ _ _ IM _ _ _ Hx) in Es.
assert (NH : s_groups st !! (fst bpm, sstart (MR st pm) ip) = None) by (rewrite <- Ep; exact p_free).
assert (Hf2 : fst bx = fst bpm) by (rewrite Es, Ep in Hf; cbn in Hf; exact Hf).
pose proof (is_part _ _ _ IS _ _ _ i (proj2 (hosts_ok _ _ _ IG _ _ Hx) ) Hi) as P5 || pose proof I as P5.
destruct (hosts_ok _ _ _ IG _ _ Hx) as (ax & Hbx & GOx).
pose proof (is_part _ _ _ IS _ _ _ i Hbx Hi) as Q5. cbn zeta in Q5. rewrite (slot_start'_eq _ _ _ IM _ _ _ Hx), <- Es in Q5. unfold one5 in Q5.
assert (U : In (bslot k) (map bslot BL)) by (apply in_map; exact Hk).
assert (NH2 : s_groups st !! (fst bx, sstart (MR st x) i) = None).
{ rewrite <- Es. apply none_of. intros Hh. destruct Q5 as (_ & _ & _ & _ & _ & _ & _ & _ & nCD & _). apply nCD. split; [exact U| exact Hh]. }
assert (NE : x <> pm \/ i <> ip).
{ destruct (aptr_eq_dec x pm) as [->|]; [right| left; congruence]. intros ->.
pose proof (is_part _ _ _ IS _ _ _ ip Hpm' Hip) as P. cbn zeta in P. rewrite (slot_start'_eq _ _ _ IM _ _ _ (ex_intro _ aipm Hpm')), <- Ep, HP in P.
unfold one5 in P. destruct P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & nCE & _). apply nCE. split; [| reflexivity].
pose proof (hosts_inj _ _ _ IM _ _ _ Hx (ex_intro _ aipm Hpm')) as Ebx. rewrite Ebx in Es. rewrite Ep, <- Es. exact U. }
pose proof (@sep_ext _ _ _ _ IM IG IS pm bpm ip (ex_intro _ aipm Hpm') Hip NH x bx i Hx Hf2 Hi NE NH2) as D.
rewrite !sstart_succ in D. rewrite Es. cbn [snd]. rewrite Ep. cbn [snd].
pose proof (stride_ge _ _ _ IG _ _ (ex_intro _ aipm Hpm')) as [SGp _]. unfold IB, UNIT in *. clear - D SGp. lia.
Qed.

#[using="X st m p ai mr' INV IDLE sc' last' cnt stride' R_prev R_next R_mem R_freeable R_maplen R_li R_ai R_full0 R_sc R_masks R_stride R_stride16 R_align X_fresh X_fresh_old X_idle X_zomb X_nozomb X_part X_pend' NOPART SITE SH_hdr0 SH_ghdr E_metas E_groups E_slots E_shadow E_regions E_areas E_next_rid E_tick E_secret E_reserved E_ctx E_mc E_usage E_usage_keys IR IA IM IL IG IS ISH"] Theorem INVL_create : INVL X' st' L BL LS.
Proof.
destruct E_ctx as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15).
destruct R_masks as (W1 & W2 & W3 & W4 & W5 & W6). destruct R_stride16 as [SP SM]. destruct R_align as [P0 P16].
assert (XO : forall rid, x_orph X' = Some rid -> x_orph X = Some rid /\ m_maplen mr' = 0).
{ intros rid Ho. destruct SITE as [(_ & _ & _ & HO' & _)|(Hml & _ & _ & HO' & _)]; [rewrite HO' in Ho; discriminate| rewrite HO' in Ho; auto]. }
split; [| split; [| split; [| split; [| split; [| split]]]]].
-  destruct IR; constructor; rewrite ?E_regions, ?E_next_rid, ?E_reserved, ?F6, ?F7, ?F10, ?F15; try assumption.
+ eapply Permutation_trans; [exact ir_metas|]. erewrite map_ext; [apply Permutation_refl|]. intros [rid r]; cbn. rewrite C_frontier. reflexivity.
+ intros rid r H1 H2. rewrite C_frontier. exact (ir_metalen rid r H1 H2).
+ intros rid r H1 H2. rewrite C_frontier. exact (ir_brkfront rid r H1 H2).
+ intros rid Ho. destruct (XO rid Ho) as [Ho' Hml]. destruct (ir_orph rid Ho') as (r & Hr & K & NG). exists r. split; [exact Hr|]. split; [exact K|].
intros b Hb. rewrite C_groups. destruct (aptr_eqb_spec b p) as [->|NE]; [| exact (NG b Hb)]. exfalso.
destruct SITE as [(Hml' & _)|(_ & _ & _ & _ & HO0 & _)]; [exact (Hml' Hml)| rewrite HO0 in Ho'; discriminate].
-  destruct IA; constructor; rewrite ?E_regions, ?E_areas, ?E_secret, ?F1, ?F2, ?F3, ?F4, ?F5, ?F6, ?F7, ?F8, ?F9, ?F10, ?F11, ?F12, ?F13, ?F14; try assumption.
+ destruct ia_ctx as (_ & C2 & C3 & C4). split; [exact E_mc|]. auto.
+ intros a ar Ha. destruct (ia_areas a ar Ha) as ((r & ? & ? & ? & ? & ?) & ? & ? & ?). split; [| auto]. exists r. rewrite C_frontier. auto.
+ intros x mr Hx. assert (K : s_metas st' !! x <> None) by congruence. apply C_keys in K. destruct (s_metas st !! x) as [mr0|] eqn:E; [| congruence]. exact (ia_metas x mr0 E).
+ destruct ia_avail as [A1 A2]. split; [exact A1|]. intros Hc. destruct (A2 Hc) as (a & T & E & Hk). exists a. split; [exact T|]. split; [exact E|].
intros k Hk2. destruct (s_metas st' !! mslot a k) eqn:E2; [| reflexivity]. exfalso.
assert (K : s_metas st' !! mslot a k <> None) by congruence. apply C_keys in K. apply K. apply Hk. exact Hk2.
+ intros sc0 Hsc0. rewrite (E_usage sc0 Hsc0), (ia_usage sc0 Hsc0), gcnt_C. rewrite Z.eqb_sym. destruct (sc' =? sc0); lia.
-  destruct IM as [Q1 Q2 Q3 Q4 Q5] eqn:EIM; constructor.
+ intros x Hx. destruct (aptr_eq_dec x m) as [E|NE]; [subst x; rewrite C_MR_m, R_mem in Hx; discriminate|]. rewrite (C_MR_other x NE) in Hx |- *. exact (Q1 x Hx).
+ intros x b Hx. rewrite X_zomb. destruct (aptr_eq_dec x m) as [E|NE].
* subst x. rewrite C_MR_m, R_mem in Hx. inversion Hx. subst b. left. apply C_hosts. left. auto.
* rewrite (C_MR_other x NE) in Hx. destruct (Q2 x b Hx) as [H|H]; [left; apply C_hosts_old; exact H| right; exact H].
+ intros b h. rewrite C_groups. destruct (aptr_eqb_spec b p) as [->|NE].
* intros E. inversion E. subst h. exists m. cbn. rewrite C_MR_m, R_mem. fold last'. auto.
* intros Hb. destruct (Q3 b h Hb) as (x & Ex & Hmem & Hai). exists x.
assert (NEx : x <> m) by (intros ->; rewrite MRm in Hmem; discriminate). rewrite (C_MR_other x NEx). auto.
+ intros x Hx. destruct (X_idle x Hx) as [Hx' NE]. destruct (Q4 x Hx') as [E NI]. split; [| exact NI]. rewrite E_metas, lookup_insert_ne by congruence. exact E.
+ intros z Hz. rewrite X_zomb, X_nozomb in Hz. destruct Hz.
-  destruct IL as [L1 L2 L3 L4 L5 L6 L7 L9]; constructor; try assumption.
+ intros h. rewrite C_get_head. apply L1.
+ intros h. pose proof (L2 h) as D. destruct (LS h) as [|a l] eqn:E; [exact I|]. cbn [dll] in D |- *.
eapply linked_ext; [| | exact D]; intros x Hx; rewrite C_MR_other; try reflexivity; intros ->; apply (m_unlisted h); rewrite E.
* apply In_removelast in Hx. apply in_app_iff in Hx. cbn in Hx |- *. tauto.
* apply In_tl in Hx. apply in_app_iff in Hx. cbn in Hx |- *. tauto.
+ intros x. destruct (aptr_eqb_spec x m) as [->|NE].
* rewrite C_MR_m, R_next, R_prev. split; [| reflexivity]. split; [intros [h H]; exfalso; exact (m_unlisted h H)| intros H; exfalso; apply H; reflexivity].
* rewrite (C_MR_other x NE). apply L5.
+ intros x Hx. destruct (aptr_eqb_spec x m) as [->|NE]; [exfalso; exact (m_unlisted _ Hx)|]. rewrite (C_MR_other x NE). apply L6. exact Hx.
+ intros sc x Hx. destruct (L7 sc x Hx) as (A1 & [b Hb] & A3).
destruct (aptr_eqb_spec x m) as [->|NE]; [exfalso; exact (m_unlisted _ Hx)|]. rewrite (C_MR_other x NE).
split; [exact A1|]. split; [exists b; apply C_hosts_old; exact Hb| exact A3].
-  destruct IG as [G1 G2 G3 G4 G5] eqn:EIG. constructor.
+ intros x b aix. rewrite C_groups. destruct (aptr_eqb_spec b p) as [->|NEb].
*
intros E. inversion E. subst x aix. constructor; rewrite ?C_MR_m, ?E_regions; fold sc' last' stride'.
-- apply C_keys. rewrite m_meta0. discriminate.
-- exact R_li.
-- exact R_ai.
-- destruct R_sc as [A|(A1 & A2 & A3)]; [left; exact A| right]. split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. intros [h H]. exact (m_unlisted h H).
-- exact R_freeable.
-- exact R_maplen.
-- exact (conj W1 (conj W2 (conj W3 (conj W4 (conj W5 W6))))).
-- intros NF Hlt. exfalso. destruct X_fresh as [XF|[X63 _]]; [exact (NF XF)|]. destruct R_sc as [[A _]|(_ & L0 & _)]; unfold sc' in *; lia.
-- intros NF Hsc NI. exfalso. destruct X_fresh as [XF|[X63 _]]; [exact (NF XF)| unfold sc' in *; lia].
-- intros NF sc Hin Hnh. exfalso. exact (m_unlisted _ Hin).
-- exact R_stride.
-- intros NF Hsc LT. exfalso. destruct X_fresh as [XF|[X63 _]]; [exact (NF XF)| unfold sc' in *; lia].
-- exact (conj P0 P16).
-- intros Hml. destruct SITE as [(_ & B0 & _ & _ & _ & r & Hr & Hk & Hlen & Hend)|(Hml0 & _)]; [| exfalso; exact (Hml Hml0)].
split; [exact B0|]. exists r. split; [exact Hr|]. split; [exact Hk|]. split; [exact Hlen|].
unfold gend, cnt_of. rewrite sstart'. fold last' cnt. exact Hend.
-- intros Hml. destruct SITE as [(Hml1 & _)|(_ & _ & _ & _ & _ & pm & ip & bpm & Hs & Hpm & Hf & Hip & Ep & FIT & Hsc & Hstr & _)]; [exfalso; exact (Hml1 Hml)|].
exists pm, ip. rewrite (C_MR_hosted _ _ Hpm). split; [rewrite C_slots_old; [exact Hs| exact p_not_new]|].
rewrite (hosts_gbase _ _ _ IM _ _ Hpm). split; [exact Hf|]. split; [| split; [exact Hsc| exact Hstr]].
unfold gend, cnt_of. rewrite sstart'. fold last' cnt. exact FIT.
-- exact R_full0.
*
intros Hb. pose proof (G1 x b aix Hb) as GO. assert (Hx : hosts st b x) by (exists aix; exact Hb).
pose proof (C_hosts_old_ne _ _ Hx) as NEx. assert (NF : x_fresh X <> Some x) by (rewrite X_fresh_old; discriminate).
assert (NF' : x_fresh X' <> Some x) by (destruct X_fresh as [XF|[_ XF]]; rewrite XF; [congruence| rewrite X_fresh_old; discriminate]).
destruct GO; constructor; rewrite ?(C_MR_other x NEx), ?E_regions; try assumption.
-- apply C_keys. exact g_present.
-- intros _. exact (g_partial NF).
-- intros _. exact (g_unlisted NF).
-- intros _. exact (g_rest NF).
-- intros _. exact (g_under NF).
-- intros Hml. destruct (g_nest Hml) as (px & ix & Hs & REST). exists px, ix.
destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bpx Hpx] & _ & _). rewrite (C_MR_hosted _ _ Hpx).
split; [rewrite C_slots_old; [exact Hs| exact (old_slot_not_new _ _ _ Hs)]| exact REST].
+ intros b aix. rewrite C_groups. destruct (aptr_eqb_spec b p) as [->|NEb]; [discriminate| exact (G2 b aix)].
+ intros m1 m2 b1 b2 ai1 ai2. rewrite !C_groups.
destruct (aptr_eqb_spec b1 p) as [->|N1]; destruct (aptr_eqb_spec b2 p) as [->|N2].
* intros E1 E2. inversion E1. inversion E2. subst. reflexivity.
* intros E1 H2. inversion E1. subst m1 ai1. rewrite C_MR_m, (C_MR_hosted _ _ (ex_intro _ ai2 H2)). fold last' sc'. intros P1 P2 Esc.
exfalso. pose proof (g_partial _ _ _ _ _ _ (G1 _ _ _ H2) ltac:(rewrite X_fresh_old; discriminate) P2) as IN. rewrite <- Esc, (NOPART P1) in IN. exact IN.
* intros H1 E2. inversion E2. subst m2 ai2. rewrite C_MR_m, (C_MR_hosted _ _ (ex_intro _ ai1 H1)). fold last' sc'. intros P1 P2 Esc.
exfalso. pose proof (g_partial _ _ _ _ _ _ (G1 _ _ _ H1) ltac:(rewrite X_fresh_old; discriminate) P1) as IN. rewrite Esc, (NOPART P2) in IN. exact IN.
* intros H1 H2. rewrite (C_MR_hosted _ _ (ex_intro _ ai1 H1)), (C_MR_hosted _ _ (ex_intro _ ai2 H2)). exact (G3 m1 m2 b1 b2 ai1 ai2 H1 H2).
+ intros rid r Hr Hk Ho. rewrite E_regions in Hr.
destruct (N.eq_dec rid (fst p)) as [->|NE].
* destruct SITE as [(Hml & B0 & HO & _)|(Hml & _ & _ & HO' & HO & _)].
-- exists m. split; [apply C_hosts; left; split; [destruct p; cbn in B0 |- *; subst; reflexivity| reflexivity]|]. rewrite C_MR_m. exact Hml.
-- destruct (G4 (fst p) r Hr Hk ltac:(rewrite HO; discriminate)) as (x & Hx & Hmlx). exists x. split; [apply C_hosts_old; exact Hx| rewrite (C_MR_hosted _ _ Hx); exact Hmlx].
* assert (Ho0 : x_orph X <> Some rid).
{ destruct SITE as [(_ & _ & HO & _)|(_ & _ & _ & HO' & HO & _)]; [rewrite HO; congruence| rewrite HO; discriminate]. }
destruct (G4 rid r Hr Hk Ho0) as (x & Hx & Hmlx). exists x. split; [apply C_hosts_old; exact Hx| rewrite (C_MR_hosted _ _ Hx); exact Hmlx].
+ intros b h. rewrite C_groups, E_regions. destruct (aptr_eqb_spec b p) as [->|NEb]; [| exact (G5 b h)]. intros _.
destruct SITE as [(_ & _ & _ & _ & _ & r & Hr & Hk & _)|(_ & _ & _ & _ & _ & pm & ip & bpm & Hs & Hpm & Hf & _)]; [exists r; auto|].
destruct Hpm as [a Hpm]. destruct (G5 _ _ Hpm) as (r & Hr & Hk). exists r. rewrite <- Hf. auto.
-  destruct IS as [S1' S2 S3 S4 S5 S6] eqn:EIS. constructor.
+ intros s x i Hs. destruct (C_slots s) as [[Es NS]|(j & Hj & -> & Es)].
* rewrite Es in Hs. destruct (S1' s x i Hs) as ([b Hb] & Hi & E). rewrite (C_MR_hosted _ _ Hb). split; [exists b; apply C_hosts_old; exact Hb| auto].
* rewrite Es in Hs. inversion Hs. subst x i. rewrite C_MR_m. fold last'. split; [exists p; apply C_hosts; left; auto|]. split; [lia|]. rewrite slot'. reflexivity.
+ intros b x i Hx Hi. apply C_hosts in Hx as [[-> ->]|[NEb Hx]].
* rewrite C_MR_m in Hi |- *. rewrite slot'. apply C_slots_new. fold last' in Hi. lia.
* rewrite (C_MR_hosted _ _ Hx) in Hi |- *. rewrite C_slots_old; [exact (S2 b x i Hx Hi)|].
apply (old_hosts_not_new_slot b x i Hx Hi) || (intros N; destruct N as (j & Hj & E); exact (old_slot_not_new _ _ _ (S2 b x i Hx Hi) (ex_intro _ j (conj Hj E)))).
+ intros b x aix i. rewrite C_groups. destruct (aptr_eqb_spec b p) as [->|NEb].
* intros E Hi. inversion E. subst x aix. rewrite C_MR_m in Hi |- *. cbn zeta. rewrite slot', C_groups. fold last' in Hi.
pose proof (X_part i Hi) as P5.
eapply one5_iff_create; [exact P5| |]; cbn.
-- intros Hin. apply in_map_iff in Hin as (k & Ek & Hk). apply (blk_not_new k Hk). exists i. split; [clear -Hi; lia| exact Ek].
-- destruct (aptr_eqb_spec (fst p, snd p + UNIT + stride' * i) p) as [Eip|NE]; [exfalso; apply p_not_new; exists i; split; [clear -Hi; lia| symmetry; exact Eip]|].
rewrite (new_not_group i ltac:(clear -Hi; lia)). intros H; apply H; reflexivity.
* intros Hb Hi. assert (Hx : hosts st b x) by (exists aix; exact Hb).
rewrite (C_MR_hosted _ _ Hx) in Hi |- *. cbn zeta. rewrite C_groups.
pose proof (S3 b x aix i Hb Hi) as P5. cbn zeta in P5.
set (s := slot_start' (MR st x) i) in *.
assert (NSs : ~ nslot s) by (apply (old_slot_not_new s x i); exact (S2 b x i Hx Hi)).
destruct (aptr_eqb_spec s p) as [Esp|NEsp].
--
destruct SITE as [(_ & B0 & _ & _ & HPX & _)|(_ & HPX & HPX' & _)].
++ exfalso. rewrite Esp in *. pose proof (S2 b x i Hx Hi) as Hs. fold s in Hs. rewrite Esp in Hs.
destruct (S1' _ _ _ Hs) as ([bb Hbb] & _ & Eps). rewrite (slot_start'_eq _ _ _ IM _ _ _ Hbb) in Eps.
pose proof (sstart0 _ _ _ IM _ _ Hbb). pose proof (sstart_mono _ _ _ IG _ _ 0 i Hbb ltac:(lia)).
destruct (hosts_ok _ _ _ IG _ _ Hbb) as (a0 & _ & GO0). pose proof (g_align _ _ _ _ _ _ GO0) as [A00 _].
apply (f_equal snd) in Eps. cbn in Eps. unfold UNIT in *. clear - B0 Eps H H0 A00. lia.
++ rewrite Esp in P5 |- *. rewrite HPX in P5. rewrite HPX'.
revert P5. unfold one5. clear. intros P5.
assert (NN : ~ (@None aptr = Some p)) by discriminate. assert (SS : Some (mkGhdr (Some m) ai) <> None) by discriminate.
tauto.
-- eapply one5_iff; [reflexivity| reflexivity| reflexivity| reflexivity| | exact P5].
split.
++ intros HPs. exfalso. destruct SITE as [(_ & _ & _ & _ & HPX & _)|(_ & HPX & _)]; rewrite HPX in HPs; [discriminate| inversion HPs; exact (NEsp (eq_sym H0))].
++ intros HPs. exfalso. destruct (X_pend' _ HPs) as (j & Hj & Ej). apply NSs. exists j. split; [fold last' in Hj; lia| exact Ej].
+ intros s Hs. destruct (X_pend' _ Hs) as (j & Hj & ->). rewrite C_slots_new; [discriminate| fold last' in Hj; lia].
+ exact S5.
+ intros k Hk. destruct (S6 k Hk) as (x & i & Hs & REST). exists x, i.
destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bx Hbx] & _). rewrite (C_MR_hosted _ _ Hbx).
split; [rewrite C_slots_old; [exact Hs| exact (blk_not_new k Hk)]| exact REST].
-  destruct ISH as [D1 D2 D3 D4 D5 D6] eqn:EISH.
assert (REGp : exists r, s_regions st !! fst p = Some r /\ r_kind r = RKGroup).
{ destruct SITE as [(_ & _ & _ & _ & _ & r & Hr & Hk & _)|(_ & _ & _ & _ & _ & pm & ip & bpm & Hs & [a Hpm] & Hf & _)]; [exists r; auto|].
destruct (ig_region _ _ _ IG _ _ Hpm) as (r & Hr & Hk). exists r. rewrite <- Hf. auto. }
constructor.
+ intros rid sh. rewrite E_shadow, E_regions. unfold hdr_havoc, upd_shadow. cbn. destruct (N.eqb_spec rid (fst p)) as [->|NE].
* intros _. exact REGp.
* rewrite lookup_insert_ne by congruence. exact (D1 rid sh).
+ intros rid sh Hsh. rewrite E_tick. rewrite E_shadow in Hsh. exact (TKS_hdr_havoc st p D2 rid sh Hsh).
+ intros b x i Hx Hi. apply C_hosts in Hx as [[-> ->]|[NEb Hx]].
* rewrite C_MR_m in Hi |- *. rewrite sstart'. apply C_known_out; [| apply SH_hdr0; unfold cnt_of in Hi; fold last' cnt in Hi; exact Hi].
cbn. intros [_ H]. unfold IB, UNIT in H. destruct (Z.eq_dec i 0) as [->|NZ]; [lia|]. unfold cnt_of in Hi. assert (stride' * 1 <= stride' * i) by nia. lia.
* rewrite (C_MR_hosted _ _ Hx) in Hi |- *. apply C_known_res; [cbn; rewrite (hdr0_res _ _ i Hx); lia| exact (D3 b x i Hx Hi)].
+ intros b x o Hx Ho. apply C_hosts in Hx as [[-> ->]|[NEb Hx]]; [apply C_unknown_hdr; exact Ho| apply C_unknown_any; exact (D4 b x o Hx Ho)].
+ intros b x px ix Hx Hml Hs. apply C_hosts in Hx as [[-> ->]|[NEb Hx]].
*
rewrite C_MR_m in Hml. rewrite (C_slots_old p p_not_new) in Hs.
destruct SITE as [(Hml1 & _)|(_ & _ & _ & _ & _ & pm & ip & bpm & Hs0 & Hpm & Hf & Hip & Ep & _ & _ & _ & (v3 & K3 & E3 & R3) & K2 & K1 & Q)]; [exfalso; exact (Hml1 Hml)|].
rewrite Hs0 in Hs. inversion Hs. subst px ix. rewrite (C_MR_hosted _ _ Hpm), (hosts_gbase _ _ _ IM _ _ Hpm). cbn zeta.
split; [exists v3; split; [apply C_known_out; [cbn; lia| exact K3]| auto]|].
split; [apply C_known_out; [cbn; lia| exact K2]|]. split; [apply C_known_out; [cbn; lia| exact K1]| exact Q].
* rewrite (C_MR_hosted _ _ Hx) in Hml. rewrite (C_slots_old b (old_hosts_not_new _ _ Hx)) in Hs.
destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bpx Hpx] & _ & _). rewrite (C_MR_hosted _ _ Hpx).
destruct (D5 b x px ix Hx Hml Hs) as ((v3 & K3 & E3 & R3) & K2 & K1 & Q). cbn zeta.
destruct (hosts_ok _ _ _ IG _ _ Hx) as (ax & Hbx & GOx). pose proof (g_align _ _ _ _ _ _ GOx) as [A0 A16]. unfold UNIT in A16.
assert (RS : forall d r, 0 <= r < 16 -> d = r - 16 -> 12 <= r -> 12 <= (snd b + d) mod 16).
{ intros d r Hr -> H12. pose proof (Z.div_mod (snd b) 16 ltac:(lia)) as Db. rewrite A16 in Db.
replace (snd b + (r - 16)) with (r + (snd b / 16 - 1) * 16) by lia. rewrite Z_mod_plus_full, Z.mod_small by lia. exact H12. }
split; [exists v3; split; [apply C_known_res; [cbn; replace (snd b - 3) with (snd b + (13 - 16)) by lia; apply (RS _ 13); lia| exact K3]| auto]|].
split; [apply C_known_res; [cbn; replace (snd b - 2) with (snd b + (14 - 16)) by lia; apply (RS _ 14); lia| exact K2]|].
split; [apply C_known_res; [cbn; replace (snd b - 1) with (snd b + (15 - 16)) by lia; apply (RS _ 15); lia| exact K1]| exact Q].
+ intros k x i Hk Hs. rewrite (C_slots_old _ (blk_not_new k Hk)) in Hs.
destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bx Hx] & Hi & Es). rewrite (C_MR_hosted _ _ Hx).
pose proof (D6 k x i Hk Hs) as B. cbn zeta in B |- *. destruct B as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).

assert (OUT : forall o, snd (bslot k) - IB <= o < snd (bslot k) + get_stride (MR st x) - IB -> ~ (fst (bslot k) = fst p /\ snd p <= o < snd p + 12)).
{ intros o Ho [Hf Hin]. pose proof (blk_clear k x i Hk Hs Hf) as D. unfold IB in *. clear - Ho Hin D. lia. }
destruct (is_blocks _ _ _ IS k Hk) as (x' & i' & Hs' & Hoff & Hn & Hfit). rewrite Hs in Hs'. inversion Hs'. subst x' i'.
pose proof (stride_ge _ _ _ IG _ _ Hx) as [SG _]. unfold IB, UNIT in *.
assert (K : forall o v, snd (bslot k) - 4 <= o < snd (bslot k) + get_stride (MR st x) - 4 -> known st (fst (bslot k), o) v -> known st' (fst (bslot k), o) v).
{ intros o v Ho Ko. apply C_known_out; [apply (OUT o Ho)| exact Ko]. }
split; [apply K; [lia| exact A1]|]. split; [apply K; [lia| exact A2]|]. split; [apply K; [lia| exact A3]|]. split; [apply K; [lia| exact A4]|].
split; [exact A5|]. split.
* intros Hr. destruct (A6 Hr) as (B1 & B2 & B3 & B4 & B5 & B6). split; [apply K; [lia| exact B1]|]. split; [apply K; [lia| exact B2]|]. split; [apply K; [lia| exact B3]|].
split; [apply K; [lia| exact B4]|]. split; [apply K; [lia| exact B5]| exact B6].
* split; [intros Hr; apply K; [lia| apply A7; exact Hr]|]. intros a Ha. apply C_unknown_any. apply A8. exact Ha.
Qed.

End CREATE.

End RC__1.
End Mq0.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import stdpp.gmap.
Import QZAi.Mq2 QUZl Qfya QPiB.Mq0 Qatc QSfG.Mq2 Q7S0 QdBa.Mq0 QdBa.Mq1 QpFQ QPiB Ql2m.Mq2 QYTG.Mq1 QdBa.Mq2 QLaA.Mq0 Q1am.Mq1 QSfG QoCS.Mq0.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition fold_f (s : Z) : bool := forallb (fun off => negb (s <? off) || ((0 <=? fold_off off s) && (fold_off off s <=? s))) (zrange 0 256).
#[using="Type"] Lemma fold_all : forallb fold_f (zrange 0 256) = true. Proof. vm_compute. reflexivity. Qed.

#[using="Type"] Lemma fold_off_le off slack : 0 <= off < 256 -> 0 <= slack -> 0 <= fold_off off slack <= slack.
Proof.
intros Ho Hs. destruct (Z.ltb_spec slack off) as [LT|GE].
- pose proof (forallb_zrange fold_f 0 256 slack fold_all ltac:(lia) ltac:(lia)) as H. unfold fold_f in H.
pose proof (forallb_zrange _ 0 256 off H ltac:(lia) ltac:(lia)) as H2. cbn beta in H2.
replace (slack <? off) with true in H2 by (symmetry; apply Z.ltb_lt; exact LT). cbn in H2.
apply andb_true_iff in H2 as [A B]. apply Z.leb_le in A. apply Z.leb_le in B. lia.
- unfold fold_off. replace (slack <? off) with false by (symmetry; apply Z.ltb_ge; exact GE). lia.
Qed.

#[using="Type"] Lemma s_shadow_havoc p n st : 0 < n ->
s_shadow (havoc p n st) = <[fst p := get_shadow (havoc p n st) (fst p)]> (s_shadow st).
Proof.
intros Hn. unfold havoc at 1. replace (n <=? 0) with false by (symmetry; apply Z.leb_gt; lia). unfold upd_shadow. cbn -[havoc get_shadow Z.add Z.mul Z.div Z.ltb].
f_equal. unfold havoc. replace (n <=? 0) with false by (symmetry; apply Z.leb_gt; lia). rewrite get_shadow_upd_shadow, N.eqb_refl. reflexivity.
Qed.

#[using="Type"] Lemma TKS_havoc p n st : snd p mod 16 = 0 -> 0 < n -> TKS st (s_tick st) -> TKS (havoc p n st) (s_tick st).
Proof.
intros Al Hn TK rid sh. rewrite s_shadow_havoc by exact Hn.
destruct (N.eq_dec rid (fst p)) as [->|NE]; [| rewrite lookup_insert_ne by congruence; apply TK].
rewrite lookup_insert_eq. intros E. inversion E. subst sh. clear E.
pose proof (sh_ticks_of st (fst p) TK) as [T1 T2].
destruct (havoc_ticks p n st Hn ltac:(intros u hl Hu ch Hch; exact (T1 u hl ch Hu Hch)) (fst p)
ltac:(intros u hl Hu ch Hch; exact (T1 u hl ch Hu Hch)) T2) as [A B].
split; [| split; [intros u hl ch Hu Hch; exact (A u hl Hu ch Hch)| exact B]].
rewrite havoc_cells by exact Hn. unfold get_shadow. destruct (s_shadow st !! fst p) as [sh0|] eqn:E0; cbn.
- exact (proj1 (TK _ _ E0)).
- intros o w t Ho. rewrite lookup_empty in Ho. discriminate.
Qed.

#[using="Type"] Lemma DOMS_havoc st0 p n st : 0 < n -> DOMS st0 st -> (exists r, s_regions st0 !! fst p = Some r /\ r_kind r = RKGroup) -> DOMS st0 (havoc p n st).
Proof.
intros Hn D Hp rid sh. rewrite s_shadow_havoc by exact Hn.
destruct (N.eq_dec rid (fst p)) as [->|NE]; [intros _; exact Hp|]. rewrite lookup_insert_ne by congruence. apply D.
Qed.

#[using="Type"] Lemma havoc_ctrl p n st : ctrl_eq st (havoc p n st) /\ s_tick (havoc p n st) = s_tick st.
Proof. unfold havoc. destruct (n <=? 0); [split; [apply ctrl_eq_refl| reflexivity]|]. split; [constructor; reflexivity| reflexivity]. Qed.

Section EF.
Variables (st : mstate) (g : aptr) (idx n off : Z).
Let mr := get_meta_rec st g.
Let stride := get_stride mr.
Let gm := default (0%N, 0) (m_mem mr).
Let c : aptr := aadd gm (UNIT + stride * idx).
Let e : aptr := aadd c (stride - IB).
Let p0 : aptr := if off =? 0 then c else aadd c (UNIT * off).
Let res := snd e - snd p0 - n.
Let q := (snd p0 - (snd gm + UNIT)) / UNIT.

Definition ef_list : list (aptr * Z) :=
(if negb (off =? 0) then [(aadd c (-2), off); (aadd (aadd c (-2)) 1, Z.shiftr off 8); (aadd c (-3), 224); (aadd p0 (-4), 0)] else [])
++ [(aadd p0 (-2), q); (aadd (aadd p0 (-2)) 1, Z.shiftr q 8); (aadd p0 (-3), idx)]
++ (if negb (res =? 0) then [(aadd e (- res), 0)] else [])
++ (if 5 <=? res then [(aadd e (-4), res); (aadd (aadd e (-4)) 1, Z.shiftr res 8); (aadd (aadd e (-4)) 2, Z.shiftr res 16); (aadd (aadd e (-4)) 3, Z.shiftr res 24); (aadd e (-5), 0)] else [])
++ [(aadd p0 (-3), Z.land idx 31 + Z.shiftl (if 5 <=? res then 5 else res) 5)].

#[using="Type"] Local Lemma enframe_at_eq_case (b0 b1 b2 : bool) :
(off =? 0) = b0 -> (res =? 0) = b1 -> (5 <=? res) = b2 -> enframe_at st g idx n off = (wrs ef_list st, p0).
Proof.
intros H H1 H2. unfold enframe_at, set_size, ef_list. unfold q, p0, e, c, gm, stride, mr in *. fold res. rewrite H.
destruct b0; cbn beta iota delta [wr16 wr32 wrs app negb]; unfold res in *; unfold p0, e, c, gm, stride, mr in *; rewrite ?H in *;
rewrite H1, H2; destruct b1, b2; cbn beta iota delta [wrs app negb]; reflexivity.
Qed.
#[using="Type"] Lemma enframe_at_eq : enframe_at st g idx n off = (wrs ef_list st, p0).
Proof. exact (enframe_at_eq_case _ _ _ eq_refl eq_refl eq_refl). Qed.

#[using="n e"] Lemma p0_eq : p0 = aadd c (UNIT * off).
Proof. unfold p0. destruct (Z.eqb_spec off 0) as [->|]; [| reflexivity]. unfold c, aadd. cbn. f_equal. lia. Qed.
End EF.

Fixpoint lastw (l : list (aptr * Z)) (r : aptr) (acc : option Z) : option Z :=
match l with
| [] => acc
| (a, v) :: l' => lastw l' r (if aptr_eqb a r then Some v else acc)
end.

#[using="Type"] Lemma lastw_acc l r v : lastw l r (Some v) = match lastw l r None with Some w => Some w | None => Some v end.
Proof.
revert v. induction l as [|[a w] l IH]; intros v; cbn; [reflexivity|].
destruct (aptr_eqb a r); [| apply IH]. rewrite !(IH w). destruct (lastw l r None); reflexivity.
Qed.

#[using="Type"] Lemma wrs_lastw l : forall st r, TKS st (s_tick st) ->
cell_read (get_shadow (wrs l st) (fst r)) (snd r) =
match lastw l r None with Some w => Known (Z.land w 255) | None => cell_read (get_shadow st (fst r)) (snd r) end.
Proof.
induction l as [|[a v] l IH]; intros st r TK; cbn [wrs lastw]; [reflexivity|].
rewrite IH by (apply TKS_wr8; [cbn; lia| exact TK]).
destruct (aptr_eqb_spec a r) as [<-|NE].
- rewrite lastw_acc. destruct (lastw l a None); [reflexivity|]. apply cell_read_wr8_same. apply sh_ticks_of. exact TK.
- destruct (lastw l r None); [reflexivity|]. apply cell_read_wr8_other. congruence.
Qed.

#[using="Type"] Lemma known_range X st L BL LS q v : INVL X st L BL LS -> cell_read (get_shadow st (fst q)) (snd q) = Known v -> 0 <= v < 256.
Proof.
intros INV H. eapply known_byte; [| exact H]. intros sh o' v' t Hs Hc. exact (proj1 (proj1 (TKS_of _ _ _ _ _ INV _ _ Hs) o' v' t Hc)).
Qed.

#[using="Type"] Lemma havoc_0 p st : havoc p 0 st = st.
Proof. reflexivity. Qed.

#[using="Type"] Lemma land255_range a : 0 <= Z.land a 255 < 256.
Proof.
split; [apply Z.land_nonneg; right; lia|].
change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
Qed.

End RC__1.
End Mq1.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Qfya QPiB.Mq0 Qatc QSfG.Mq2 Q7S0 QdBa.Mq1 QdBa.Mq0 QpFQ Ql2m.Mq1 QPiB QdBa.Mq2 Ql2m.Mq2 QYTG.Mq1 QjcB QLaA QaiD QLaA.Mq0 Q1am QoCS.Mq1.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition decodes (T : Type) (st : mstate) (p pm : aptr) (ip : Z) : Prop :=
s_slots st !! p = Some (pm, ip) /\ forall (k : aptr -> Z -> M T) (bail : M T), dec_hdr st p k bail = k pm ip.
Definition DEC_OK (T : Type) (dec : decoder T) : Prop :=
forall st p pm ip (k : aptr -> Z -> M T) (bail : M T), decodes T st p pm ip -> dec st p k bail = k pm ip.
#[using="Type"] Lemma dec_hdr_ok T : DEC_OK T dec_hdr.
Proof. intros st p pm ip k bail [_ H]. apply H. Qed.
#[using="Type"] Lemma dec_slots_ok T : DEC_OK T dec_slots.
Proof. intros st p pm ip k bail [H _]. unfold dec_slots. rewrite H. reflexivity. Qed.

Definition NTF_AT (T : Type) (f : nat) : Prop :=
forall (dec1 dec2 : decoder T), DEC_OK T dec1 -> DEC_OK T dec2 ->
forall X st L BL LS g bg i (k : mstate -> mapinfo -> M T) (bail : M T),
INVL X st L BL LS -> hosts st bg g -> 0 <= i <= m_last_idx (MR st g) ->
x_pend X = Some (fst bg, sstart (MR st g) i) -> x_fresh X = None -> x_orph X = None ->
(1 <= f)%nat -> 49 - m_sizeclass (MR st g) <= Z.of_nat f ->
exists st' mi LS',
nontrivial_free dec1 f st g i k bail = k st' mi /\ nontrivial_free dec2 f st g i k bail = k st' mi /\
(s_regions st' = s_regions st /\ s_secret st' = s_secret st /\ c_init_done (s_ctx st') = c_init_done (s_ctx st)
/\ c_meta_alloc_shift (s_ctx st') = c_meta_alloc_shift (s_ctx st)) /\
match mi with
| None => INVL (xpend X None) st' L BL LS'
| Some (base, len) =>
exists r, snd base = 0 /\ s_regions st' !! (fst base) = Some r /\ r_kind r = RKGroup
/\ len = round_up_pg (r_len r) /\ 0 < len
/\ INVL (xorph (xpend X None) (Some (fst base))) st' L BL LS'
end.

#[using="Type"] Lemma rem_notin g l : ~ In g l -> rem g l = l.
Proof.
induction l as [|x l IH]; cbn; [reflexivity|]. intros H.
unfold rem. cbn. destruct (aptr_eq_dec g x) as [->|NE]; [exfalso; apply H; left; reflexivity|].
cbn. f_equal. apply IH. tauto.
Qed.

#[using="Type"] Lemma regions_fm_st st g : s_regions (fm_st st g) = s_regions st.
Proof. unfold fm_st. destruct (queue_frame LFree g (put_meta g meta0 st)) as (E & _). rewrite E. reflexivity. Qed.

#[using="Type"] Lemma INVL_free_zombie idle zomb pend orph st L BL LS g :
INVL (mkX idle (g :: zomb) pend orph None) st L BL LS ->
~ In g zomb -> ~ In g idle ->
exists LS', INVL (mkX idle zomb pend orph None) (fm_st st g) L BL LS'.
Proof.
intros INV NZ NI.
pose proof (INVL_unzombie _ st L BL LS g INV ltac:(left; reflexivity)) as INV1. cbn in INV1.
unfold xzomb in INV1. cbn in INV1.
unfold rem in INV1. cbn in INV1. destruct (aptr_eq_dec g g) as [_|NE]; [| congruence]. cbn in INV1.
fold (rem g zomb) in INV1. rewrite (rem_notin g zomb NZ) in INV1.
eexists. unfold fm_st.
apply (INVL_queue _ (put_meta g meta0 st) L BL LS g LFree INV1).
- unfold MR. rewrite get_meta_rec_put_same. reflexivity.
- rewrite lookup_metas_put, aptr_eqb_refl. discriminate.
- cbn. split; [unfold MR; rewrite get_meta_rec_put_same; reflexivity|]. split; [exact NI| exact NZ].
Qed.

Section FG.
Variables (T : Type) (f : nat).
Hypothesis IHf : NTF_AT T f.
Variables (dec1 dec2 : decoder T).
Hypothesis D1 : DEC_OK T dec1.
Hypothesis D2 : DEC_OK T dec2.
Variables (idle zomb : list aptr) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (g bg : aptr) (ai i : Z).
Variables (k : mstate -> mapinfo -> M T) (bail : M T).
Let X := mkX idle zomb (Some (fst bg, sstart (MR st g) i)) None (Some g).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hg : s_groups st !! bg = Some (mkGhdr (Some g) ai).
Hypothesis NL : m_next (MR st g) = None.
Hypothesis Hi : 0 <= i <= m_last_idx (MR st g).
Hypothesis ALL : forall j, 0 <= j <= m_last_idx (MR st g) -> j <> i ->
tbit (m_avail (MR st g)) j = true \/ tbit (m_freed (MR st g)) j = true.
Hypothesis FUEL : 49 - m_sizeclass (MR st g) <= Z.of_nat (S f).

#[using="IHf D1 D2 LS bg ai i X INV Hg NL Hi ALL FUEL"] Theorem free_group_ok :
exists st' mi LS', free_group T dec1 (nontrivial_free dec1 f) st g k bail = k st' mi /\
free_group T dec2 (nontrivial_free dec2 f) st g k bail = k st' mi /\
(s_regions st' = s_regions st /\ s_secret st' = s_secret st /\ c_init_done (s_ctx st') = c_init_done (s_ctx st)
/\ c_meta_alloc_shift (s_ctx st') = c_meta_alloc_shift (s_ctx st)) /\
match mi with
| None => INVL (mkX idle zomb None None None) st' L BL LS'
| Some (base, len) =>
exists r, snd base = 0 /\ s_regions st' !! (fst base) = Some r /\ r_kind r = RKGroup
/\ len = round_up_pg (r_len r) /\ 0 < len
/\ INVL (mkX idle zomb None (Some (fst base)) None) st' L BL LS'
end.
Proof.
pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
assert (KSEC : forall U, s_secret (del_slots bg (get_stride (MR st g)) (m_last_idx (MR st g) + 1)
(del_group bg (upd_ctx (fun c => set_usage_map U c) st))) = s_secret st) by (intros; reflexivity).
assert (FMSEC : forall s, s_secret (fm_st s g) = s_secret s).
{ intros s0. unfold fm_st. destruct (queue_frame LFree g (put_meta g meta0 s0)) as (_ & _ & _ & _ & _ & _ & _ & Q8 & _). rewrite Q8. reflexivity. }
assert (KINIT : forall U, c_init_done (s_ctx (del_slots bg (get_stride (MR st g)) (m_last_idx (MR st g) + 1)
(del_group bg (upd_ctx (fun c => set_usage_map U c) st)))) = c_init_done (s_ctx st)) by (intros; reflexivity).
assert (FMINIT : forall s, c_init_done (s_ctx (fm_st s g)) = c_init_done (s_ctx s)).
{ intros s0. unfold fm_st. destruct (queue_frame LFree g (put_meta g meta0 s0)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & QC). rewrite (cb_init _ _ QC). reflexivity. }
assert (KSHIFT : forall U, c_meta_alloc_shift (s_ctx (del_slots bg (get_stride (MR st g)) (m_last_idx (MR st g) + 1)
(del_group bg (upd_ctx (fun c => set_usage_map U c) st)))) = c_meta_alloc_shift (s_ctx st)) by (intros; reflexivity).
assert (FMSHIFT : forall s, c_meta_alloc_shift (s_ctx (fm_st s g)) = c_meta_alloc_shift (s_ctx s)).
{ intros s0. unfold fm_st. destruct (queue_frame LFree g (put_meta g meta0 s0)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & QC). rewrite (cb_shift _ _ QC). reflexivity. }
assert (Hgh : hosts st bg g) by (exists ai; exact Hg).
assert (NZ : ~ In g zomb) by (intros Hz; exact (zomb_not_live _ _ _ _ _ INV g Hz (ex_intro _ bg Hgh))).
assert (NI : ~ In g idle) by (intros Hz; exact (idle_not_live _ _ _ _ _ INV g Hz (ex_intro _ bg Hgh))).
destruct (fg_st1 X st L BL LS g bg ai INV Hg) as (S1 & U1 & U2). cbn zeta in S1, U1, U2.
unfold free_group. fold (MR st g).
set (st1 := if m_sizeclass (MR st g) <? 48 then set_usage (m_sizeclass (MR st g)) (usage st (m_sizeclass (MR st g)) - (m_last_idx (MR st g) + 1)) st else st) in *.
rewrite (hosts_mem _ _ _ IM _ _ Hgh).
set (stk := del_slots bg (get_stride (MR st g)) (m_last_idx (MR st g) + 1) (del_group bg st1)).
pose proof (INVL_kill X st st1 L BL LS g bg ai i INV Hg eq_refl NL eq_refl Hi eq_refl ALL S1 U1 U2) as INVK.
cbn [x_idle x_zomb X] in INVK. fold stk in INVK.
pose proof (K_MR st st1 g bg S1 U1 U2) as KMR. fold stk in KMR.
destruct (Z.eqb_spec (m_maplen (MR st g)) 0) as [Hml|Hml]; cbn [negb].
-
destruct (dec_hdr_eq X st st1 L BL LS g bg ai i INV Hg Hi S1 U1 U2
(fun m idx => nontrivial_free dec1 f stk m idx (fun st3 mi => free_meta g st3 (fun st4 => k st4 mi) bail) bail) bail Hml)
as (pm & ip & bpm & EQ & Hs' & Hpm' & Hf & Hip & Ep & Hsc).
fold stk in EQ, Hs', Hpm'.
assert (DQ : decodes T stk bg pm ip).
{ split; [exact Hs'|]. intros k' bail'.
destruct (dec_hdr_eq X st st1 L BL LS g bg ai i INV Hg Hi S1 U1 U2 k' bail' Hml) as (pm' & ip' & bpm' & EQ' & Hs'' & _).
fold stk in EQ', Hs''. rewrite Hs' in Hs''. inversion Hs''. subst. exact EQ'. }
rewrite (D1 stk bg pm ip _ bail DQ), (D2 stk bg pm ip _ bail DQ).
destruct (IHf dec1 dec2 D1 D2 (mkX idle (g :: zomb) (Some bg) None None) stk L BL LS pm bpm ip
(fun st3 mi => free_meta g st3 (fun st4 => k st4 mi) bail) bail INVK Hpm')
as (st3 & mi & LS3 & EQ3 & EQ3b & REG3 & POST3).
+ rewrite KMR. exact Hip.
+ cbn. rewrite KMR, Ep. reflexivity.
+ reflexivity.
+ reflexivity.
+ lia.
+ rewrite KMR. lia.
+ rewrite EQ3, EQ3b. rewrite !free_meta_eq. exists (fm_st st3 g), mi.
destruct mi as [[base len]|].
* destruct POST3 as (r & B0 & Hr & Hk & Hlen & Hpos & INV3). cbn in INV3.
destruct (INVL_free_zombie idle zomb None (Some (fst base)) st3 L BL LS3 g INV3 NZ NI) as [LS4 INV4].
exists LS4. split; [reflexivity|]. split; [reflexivity|]. rewrite regions_fm_st, FMSEC, FMINIT, FMSHIFT.
split; [destruct REG3 as (R3a & R3b & R3c & R3d); rewrite R3a, R3b, R3c, R3d; split; [exact (K_regions st st1 g bg S1 U1 U2)| destruct S1 as [U ->]; split; [apply KSEC| split; [apply KINIT| apply KSHIFT]]]|]. exists r.
split; [exact B0|]. split; [exact Hr|]. split; [exact Hk|]. split; [exact Hlen|]. split; [exact Hpos| exact INV4].
* cbn in POST3. destruct (INVL_free_zombie idle zomb None None st3 L BL LS3 g POST3 NZ NI) as [LS4 INV4].
exists LS4. split; [reflexivity|]. split; [reflexivity|]. rewrite regions_fm_st, FMSEC, FMINIT, FMSHIFT.
split; [destruct REG3 as (R3a & R3b & R3c & R3d); rewrite R3a, R3b, R3c, R3d; split; [exact (K_regions st st1 g bg S1 U1 U2)| destruct S1 as [U ->]; split; [apply KSEC| split; [apply KINIT| apply KSHIFT]]]| exact INV4].
-
rewrite !free_meta_eq.
destruct (kill_top X st st1 L BL LS g bg ai INV Hg S1 U1 U2 Hml) as (r & B0 & Hr & Hk & Hlen & Hpos).
fold stk in Hr.
assert (INV2 : INVL (mkX idle (g :: zomb) None (Some (fst bg)) None) (record_seq (m_sizeclass (MR st g)) (step_seq stk)) L BL LS).
{ apply INVL_record_seq. apply INVL_step_seq. unfold stk. cbn [negb] in INVK. exact INVK. }
destruct (INVL_free_zombie idle zomb None (Some (fst bg)) _ L BL LS g INV2 NZ NI) as [LS4 INV4].
assert (RS : forall sc s, s_regions (record_seq sc (step_seq s)) = s_regions s).
{ intros sc s. unfold record_seq, step_seq. destruct (sc_in_seq_range sc); destruct (c_seq (ctx s) =? 255); reflexivity. }
assert (RSS : forall sc s, s_secret (record_seq sc (step_seq s)) = s_secret s).
{ intros sc s. unfold record_seq, step_seq. destruct (sc_in_seq_range sc); destruct (c_seq (ctx s) =? 255); reflexivity. }
assert (RSI : forall sc s, c_init_done (s_ctx (record_seq sc (step_seq s))) = c_init_done (s_ctx s)).
{ intros sc s. unfold record_seq, step_seq. destruct (sc_in_seq_range sc); destruct (c_seq (ctx s) =? 255); reflexivity. }
assert (RSH : forall sc s, c_meta_alloc_shift (s_ctx (record_seq sc (step_seq s))) = c_meta_alloc_shift (s_ctx s)).
{ intros sc s. unfold record_seq, step_seq. destruct (sc_in_seq_range sc); destruct (c_seq (ctx s) =? 255); reflexivity. }
eexists _, _, LS4. split; [reflexivity|]. split; [reflexivity|]. rewrite regions_fm_st, RS, FMSEC, RSS, FMINIT, RSI, FMSHIFT, RSH.
split; [split; [exact (K_regions st st1 g bg S1 U1 U2)| destruct S1 as [U ->]; split; [apply KSEC| split; [apply KINIT| apply KSHIFT]]]|]. cbn. exists r. cbn.
split; [exact B0|]. split; [exact Hr|]. split; [exact Hk|]. split; [exact Hlen|]. split; [exact Hpos| exact INV4].
Qed.
End FG.

#[using="Type"] Lemma ntf_unfold {T} dec f st g i (k : mstate -> mapinfo -> M T) bail :
nontrivial_free dec (S f) st g i k bail =
(if (Z.lor (m_freed (MR st g)) (m_avail (MR st g)) + bit i =? mask_upto (m_last_idx (MR st g))) && okay_to_free st g then
match m_next (MR st g) with
| Some _ =>
guard 50 (m_sizeclass (MR st g) <? 48) (
match optr_eqb (active st (m_sizeclass (MR st g))) (Some g), active (dequeue (LActive (m_sizeclass (MR st g))) g st) (m_sizeclass (MR st g)) with
| true, Some a => activate_group a (dequeue (LActive (m_sizeclass (MR st g))) g st)
(fun st2 _ => free_group T dec (nontrivial_free dec f) st2 g k bail) bail
| _, _ => free_group T dec (nontrivial_free dec f) (dequeue (LActive (m_sizeclass (MR st g))) g st) g k bail
end) bail
| None => free_group T dec (nontrivial_free dec f) st g k bail
end
else if Z.lor (m_freed (MR st g)) (m_avail (MR st g)) =? 0 then
guard 51 (m_sizeclass (MR st g) <? 48) (
if negb (optr_eqb (active st (m_sizeclass (MR st g))) (Some g))
then queue (LActive (m_sizeclass (MR st g))) g st (fun st' => k (upd_meta g (fun r => m_set_freed (Z.lor (m_freed r) (bit i)) r) st') None) bail
else k (upd_meta g (fun r => m_set_freed (Z.lor (m_freed r) (bit i)) r) st) None) bail
else
k (upd_meta g (fun r => m_set_freed (Z.lor (m_freed r) (bit i)) r) st) None).
Proof. reflexivity. Qed.

#[using="Type"] Lemma data_same r r' i : data_of r' = data_of r ->
sstart r' i = sstart r i /\ m_last_idx r' = m_last_idx r /\ m_avail r' = m_avail r /\ m_freed r' = m_freed r
/\ m_sizeclass r' = m_sizeclass r /\ m_maplen r' = m_maplen r /\ m_mem r' = m_mem r.
Proof.
intros D. pose proof (proj1 (data_of_eq r' r) D) as (E1 & E2 & E3 & E4 & E5 & E6 & E7).
unfold sstart, gbase. rewrite (get_stride_data _ _ D), E1. repeat split; auto.
Qed.

#[using="Type"] Lemma head_of_eq_app (l1 l2 : list aptr) g : NoDup (l1 ++ g :: l2) -> head_of (l1 ++ g :: l2) = Some g -> l1 = [].
Proof.
intros ND H. destruct l1 as [|a l1']; [reflexivity|]. cbn in H. inversion H. subst a. exfalso.
cbn in ND. apply NoDup_cons in ND as [N _]. apply N. apply elem_of_list_In || apply list_elem_of_In. apply in_app_iff. right. left. reflexivity.
Qed.

#[using="Type"] Theorem ntf_all T : forall f, NTF_AT T f.
Proof.
induction f as [|f IH]; intros dec1 dec2 D1 D2 X st L BL LS g bg i k bail INV Hgh Hi HP HF HO F1 F2; [lia|].
destruct X as [idle zomb pend orph fresh]. cbn in HP, HF, HO. subst pend orph fresh.
pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
pose proof Hgh as [ai Hg].
pose proof (ig_ok _ _ _ IG _ _ _ Hg) as GO. pose proof (g_masks _ _ _ _ _ _ GO) as (M1 & M2 & M3 & M4 & M5 & M6).
pose proof (g_li _ _ _ _ _ _ GO) as LI. pose proof (g_ai _ _ _ _ _ _ GO) as AI.
pose proof (is_part _ _ _ IS _ _ _ i Hg Hi) as Pi. cbn zeta in Pi. rewrite (slot_start'_eq _ _ _ IM _ _ _ Hgh) in Pi. cbn [x_pend] in Pi.
assert (NA : tbit (m_avail (MR st g)) i = false) by (destruct (tbit (m_avail (MR st g)) i) eqn:E; [exfalso; unfold one5 in Pi; tauto| reflexivity]).
assert (NB : tbit (m_freed (MR st g)) i = false) by (destruct (tbit (m_freed (MR st g)) i) eqn:E; [exfalso; unfold one5 in Pi; tauto| reflexivity]).
clear Pi.
rewrite !ntf_unfold.
set (mask := Z.lor (m_freed (MR st g)) (m_avail (MR st g))).
assert (MN : 0 <= mask) by (apply Z.lor_nonneg; auto).
assert (MI : Z.testbit mask i = false) by (unfold mask; rewrite Z.lor_spec; unfold tbit in NA, NB; rewrite NA, NB; reflexivity).
assert (MADD : mask + bit i = Z.lor mask (bit i)) by (rewrite bit_eq; apply add_bit_lor; auto; lia).

assert (NU : okay_to_free st g = false -> m_sizeclass (MR st g) < 48 -> UNIT * size_class (m_sizeclass (MR st g)) <= get_stride (MR st g)).
{ intros OK Hsc. unfold okay_to_free in OK. fold (MR st g) in OK. rewrite (g_freeable _ _ _ _ _ _ GO) in OK. cbn [Z.eqb] in OK.
destruct (Z.ltb_spec (get_stride (MR st g)) (UNIT * size_class (m_sizeclass (MR st g)))); [| lia].
rewrite Bool.orb_true_r in OK. discriminate. }
destruct ((mask + bit i =? mask_upto (m_last_idx (MR st g))) && okay_to_free st g) eqn:C1.
-
apply Bool.andb_true_iff in C1 as [CM COK]. apply Z.eqb_eq in CM.
assert (ALL : forall j, 0 <= j <= m_last_idx (MR st g) -> j <> i -> tbit (m_avail (MR st g)) j = true \/ tbit (m_freed (MR st g)) j = true).
{ intros j Hj NE. assert (T1 : Z.testbit (mask + bit i) j = true) by (rewrite CM, testbit_mask_upto by lia; apply Z.leb_le; lia).
rewrite MADD, Z.lor_spec, testbit_bit in T1 by lia. destruct (Z.eqb_spec i j); [lia|]. rewrite Bool.orb_false_r in T1.
unfold mask in T1. rewrite Z.lor_spec in T1. unfold tbit. destruct (Z.testbit (m_freed (MR st g)) j); [right; reflexivity|]. left. exact T1. }
pose proof (INVL_set_fresh _ st L BL LS (Some g) INV eq_refl) as INVf. cbn in INVf.

assert (FGT : forall st2 LS2,
INVL (mkX idle zomb (Some (fst bg, sstart (MR st g) i)) None (Some g)) st2 L BL LS2 ->
s_groups st2 = s_groups st -> data_of (MR st2 g) = data_of (MR st g) -> m_next (MR st2 g) = None ->
exists st' mi LS', free_group T dec1 (nontrivial_free dec1 f) st2 g k bail = k st' mi /\
free_group T dec2 (nontrivial_free dec2 f) st2 g k bail = k st' mi /\
(s_regions st' = s_regions st2 /\ s_secret st' = s_secret st2 /\ c_init_done (s_ctx st') = c_init_done (s_ctx st2)
/\ c_meta_alloc_shift (s_ctx st') = c_meta_alloc_shift (s_ctx st2)) /\
match mi with
| None => INVL (mkX idle zomb None None None) st' L BL LS'
| Some (base, len) => exists r, snd base = 0 /\ s_regions st' !! (fst base) = Some r /\ r_kind r = RKGroup
/\ len = round_up_pg (r_len r) /\ 0 < len /\ INVL (mkX idle zomb None (Some (fst base)) None) st' L BL LS'
end).
{ intros st2 LS2 INV2 HG2 DD2 NL2. destruct (data_same _ _ i DD2) as (Es & El & Ea & Ef & Esc & Eml & Emem).
rewrite <- Es in INV2.
apply (free_group_ok T f IH dec1 dec2 D1 D2 idle zomb st2 L BL LS2 g bg ai i k bail INV2).
- rewrite HG2. exact Hg.
- exact NL2.
- rewrite El. exact Hi.
- rewrite El, Ea, Ef. exact ALL.
- rewrite Esc. exact F2. }
destruct (m_next (MR st g)) as [nx|] eqn:NX.
+
assert (Lg : in_list LS g) by (apply (proj2 (proj1 (il_link _ _ IL g))); rewrite NX; discriminate).
destruct Lg as [h Hin]. destruct h as [sc|]; [| exfalso; exact (free_not_live _ _ _ _ _ INV g Hin (ex_intro _ bg Hgh))].
destruct (il_active _ _ IL sc g Hin) as (Hsc & _ & Esc). rewrite Esc.
rewrite !(guard_true 50) by (apply Z.ltb_lt; lia).
destruct (in_split _ _ Hin) as (l1 & l2 & HL).
pose proof (il_nodup _ _ IL (LActive sc)) as ND. rewrite HL in ND.
assert (INV1 : INVL (mkX idle zomb (Some (fst bg, sstart (MR st g) i)) None (Some g)) (dequeue (LActive sc) g st) L BL (fupd LS (LActive sc) (l1 ++ l2))).
{ apply (INVL_dequeue _ _ st L BL LS g (LActive sc) l1 l2 INV HL). left. exists sc. auto. }
set (st1 := dequeue (LActive sc) g st) in *. set (LS1 := fupd LS (LActive sc) (l1 ++ l2)) in *.
destruct (dequeue_frame (LActive sc) g st) as (RG1 & _ & _ & _ & G1 & _ & _ & SE1 & _ & CB1). fold st1 in G1, RG1, SE1, CB1.
pose proof (dequeue_data (LActive sc) g st) as DG1. fold st1 in DG1.
assert (NL1 : m_next (MR st1 g) = None) by (unfold st1; rewrite dequeue_next, aptr_eqb_refl; reflexivity).
assert (HD1 : active st1 sc = head_of (l1 ++ l2)).
{ pose proof (il_head _ _ (proj1 (proj2 (proj2 (proj2 INV1)))) (LActive sc)) as H. unfold LS1 in H. rewrite fupd_eq in H. exact H. }
destruct (optr_eqb (active st sc) (Some g)) eqn:AN; [destruct (active st1 sc) as [a|] eqn:A1|].
*
destruct (optr_eqb_spec (active st sc) (Some g)) as [HD|]; [| discriminate].
assert (El1 : l1 = []).
{ apply (head_of_eq_app l1 l2 g ND). rewrite <- HL. rewrite <- (il_head _ _ IL (LActive sc)). exact HD. }
subst l1. cbn in HD1, HL, ND. destruct l2 as [|a' l2']; cbn in HD1; [discriminate|]. inversion HD1. subst a'.
assert (Hain : In a (LS (LActive sc))) by (rewrite HL; right; left; reflexivity).
assert (NEa : a <> g) by (intros ->; apply NoDup_cons in ND as [N _]; apply N; apply list_elem_of_In; left; reflexivity).
destruct (il_active _ _ IL sc a Hain) as (_ & [ba [aia Ha]] & Esca).
pose proof (g_rest _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Ha) ltac:(discriminate) sc Hain ltac:(rewrite HL; cbn; congruence)) as [AZa FZa].
pose proof (dequeue_data (LActive sc) g st a) as Da. fold st1 in Da.
destruct (data_same _ _ 0 Da) as (_ & _ & Eaa & _ & Esa & _).
assert (Ha1 : s_groups st1 !! ba = Some (mkGhdr (Some a) aia)) by (rewrite G1; exact Ha).
assert (AV1 : m_avail (MR st1 a) = 0) by (rewrite Eaa; exact AZa).
assert (HEAD1 : head_of (LS1 (LActive (m_sizeclass (MR st1 a)))) = Some a).
{ rewrite Esa, Esca. unfold LS1. rewrite fupd_eq. reflexivity. }
rewrite !(activate_group_eq _ st1 L BL LS1 a ba aia INV1 Ha1 AV1).
pose proof (INVL_activate _ st1 L BL LS1 a ba aia INV1 Ha1 AV1 HEAD1) as INV2.
set (st2 := upd_meta a _ st1) in INV2 |- *.
destruct (FGT st2 LS1 INV2) as (st' & mi & LS' & EQ & EQb & REG & POST).
-- unfold st2. cbn. exact G1.
-- unfold st2, MR. rewrite get_meta_rec_upd_other by congruence. exact (DG1 g).
-- unfold st2, MR. rewrite get_meta_rec_upd_other by congruence. exact NL1.
-- exists st', mi, LS'. split; [exact EQ|]. split; [exact EQb|].
split; [destruct REG as (RA & RB & RC & RD); rewrite RA, RB, RC, RD; unfold st2; split; [etransitivity; [| exact RG1]; reflexivity| split; [etransitivity; [| exact SE1]; reflexivity| split; [etransitivity; [| exact (cb_init _ _ CB1)]; reflexivity| etransitivity; [| exact (cb_shift _ _ CB1)]; reflexivity]]]| exact POST].
* destruct (FGT st1 LS1 INV1 G1 (DG1 g) NL1) as (st' & mi & LS' & EQ & EQb & REG & POST). exists st', mi, LS'. split; [exact EQ|]. split; [exact EQb|]. split; [destruct REG as (RA & RB & RC & RD); rewrite RA, RB, RC, RD; split; [exact RG1| split; [exact SE1| split; [exact (cb_init _ _ CB1)| exact (cb_shift _ _ CB1)]]]| exact POST].
* destruct (FGT st1 LS1 INV1 G1 (DG1 g) NL1) as (st' & mi & LS' & EQ & EQb & REG & POST). exists st', mi, LS'. split; [exact EQ|]. split; [exact EQb|]. split; [destruct REG as (RA & RB & RC & RD); rewrite RA, RB, RC, RD; split; [exact RG1| split; [exact SE1| split; [exact (cb_init _ _ CB1)| exact (cb_shift _ _ CB1)]]]| exact POST].
+
destruct (FGT st LS INVf eq_refl eq_refl NX) as (st' & mi & LS' & EQ & POST). exists st', mi, LS'. split; [exact EQ| exact POST].
-
assert (OKF : m_last_idx (MR st g) = 0 -> okay_to_free st g = false).
{ intros L0. rewrite L0 in C1. assert (i = 0) by lia. subst i.
assert (mask = 0).
{ apply Z.bits_inj'. intros j Hj. rewrite Z.bits_0. unfold mask. rewrite Z.lor_spec.
destruct (Z.eq_dec j 0) as [->|NE]; [unfold tbit in NA, NB; rewrite NA, NB; reflexivity|].
destruct (Z.testbit (m_freed (MR st g)) j) eqn:EF; [pose proof (M4 j Hj EF); lia|].
destruct (Z.testbit (m_avail (MR st g)) j) eqn:EA; [pose proof (M3 j Hj EA); lia|]. reflexivity. }
rewrite H in C1. cbn in C1. exact C1. }
assert (C3 : m_sizeclass (MR st g) < 48 -> UNIT * size_class (m_sizeclass (MR st g)) <= get_stride (MR st g)).
{ intros Hsc. destruct (Z.eq_dec (m_last_idx (MR st g)) 0) as [L0|L0]; [exact (NU (OKF L0) Hsc)|].
unfold get_stride. destruct (Z.eqb_spec (m_last_idx (MR st g)) 0); [lia|]. cbn. lia. }
destruct (Z.eqb_spec mask 0) as [MZ|MNZ].
+
assert (AZ : m_avail (MR st g) = 0) by (unfold mask in MZ; apply Z.lor_eq_0_iff in MZ; tauto).
assert (FZ : m_freed (MR st g) = 0) by (unfold mask in MZ; apply Z.lor_eq_0_iff in MZ; tauto).
assert (Hsc : 0 <= m_sizeclass (MR st g) < 48).
{ destruct (g_sc _ _ _ _ _ _ GO) as [[H _]|(E63 & L0 & _)]; [exact H|]. exfalso.
rewrite (OKF L0) in NU. unfold okay_to_free in OKF. fold (MR st g) in OKF. rewrite (g_freeable _ _ _ _ _ _ GO), E63 in OKF.
cbn in OKF. discriminate (OKF L0). }
rewrite !(guard_true 51) by (apply Z.ltb_lt; lia).
destruct (optr_eqb_spec (active st (m_sizeclass (MR st g))) (Some g)) as [HD|NHD]; cbn [negb].
*
eexists _, None, LS. split; [reflexivity|]. split; [reflexivity|]. split; [repeat split; reflexivity|]. cbn.
apply (INVL_aor _ st L BL LS g bg ai i INV Hg Hi eq_refl).
-- intros _ sc _ _. exact AZ.
-- intros _ _. exists (LActive (m_sizeclass (MR st g))). apply (head_listed _ _ _ _ _ INV). exact HD.
-- exact C3.
*
assert (NL : m_next (MR st g) = None).
{ destruct (m_next (MR st g)) as [nx|] eqn:NX; [| reflexivity]. exfalso.
assert (Lg : in_list LS g) by (apply (proj1 (proj1 (il_link _ _ IL g))) || apply (proj2 (proj1 (il_link _ _ IL g))); rewrite NX; discriminate).
destruct Lg as [h Hin]. destruct h as [sc|]; [| exact (free_not_live _ _ _ _ _ INV g Hin (ex_intro _ bg Hgh))].
destruct (il_active _ _ IL sc g Hin) as (_ & _ & Esc). subst sc.
apply NHD. rewrite <- Esc at 1 || idtac.
destruct (g_rest _ _ _ _ _ _ GO ltac:(discriminate) _ Hin) as [_ FNZ]; [| exact (FNZ FZ) || congruence].
rewrite <- (il_head _ _ IL (LActive (m_sizeclass (MR st g)))). intros E. apply NHD. exact (eq_sym E) || (symmetry; exact E). }
assert (NP : m_prev (MR st g) = None) by (exact (proj2 (il_link _ _ IL g) NL)).
rewrite !(queue_eq (LActive (m_sizeclass (MR st g))) g st _ bail NL NP).
pose proof (INVL_set_fresh _ st L BL LS (Some g) INV eq_refl) as INVf. cbn in INVf.
pose proof (INVL_queue _ st L BL LS g (LActive (m_sizeclass (MR st g))) INVf NL (g_present _ _ _ _ _ _ GO)) as INVq.
cbn [x_fresh x_idle x_zomb] in INVq. specialize (INVq ltac:(repeat split; auto; lia; fail)) || specialize (INVq (conj Hsc (conj (ex_intro _ bg Hgh) (conj eq_refl eq_refl)))).
set (stq := queue_st (LActive (m_sizeclass (MR st g))) g st) in *.
set (LSq := fupd LS (LActive (m_sizeclass (MR st g))) (LS (LActive (m_sizeclass (MR st g))) ++ [g])) in *.
destruct (queue_frame (LActive (m_sizeclass (MR st g))) g st) as (RGq & _ & _ & _ & Gq & _ & _ & SEq & _ & CBq). fold stq in Gq, RGq, SEq, CBq.
pose proof (queue_data (LActive (m_sizeclass (MR st g))) g st g) as Dq. fold stq in Dq.
destruct (data_same _ _ i Dq) as (Es & El & Ea & Ef & Esc & Eml & Emem).
assert (INVa : INVL (mkX idle zomb None None (Some g)) (upd_meta g (fun r => m_set_freed (Z.lor (m_freed r) (bit i)) r) stq) L BL LSq).
{ apply (INVL_aor (mkX idle zomb (Some (fst bg, sstart (MR st g) i)) None (Some g)) stq L BL LSq g bg ai i INVq).
- rewrite Gq. exact Hg.
- rewrite El. exact Hi.
- cbn. rewrite Es. reflexivity.
- cbn. intros NF. exfalso. apply NF. reflexivity.
- cbn. intros NF. exfalso. apply NF. reflexivity.
- rewrite Esc. unfold stq, MR. rewrite (get_stride_data _ _ Dq). exact C3. }
eexists _, None, LSq. split; [reflexivity|]. split; [reflexivity|]. split; [cbn; rewrite RGq, SEq, (cb_init _ _ CBq), (cb_shift _ _ CBq); repeat split; reflexivity|]. cbn.
apply (INVL_clear_fresh _ _ L BL LSq g INVa eq_refl).
intros b ai' Hb. unfold MR. rewrite get_meta_rec_upd_same. cbn [m_last_idx m_sizeclass m_avail m_freed m_set_freed]. fold (MR stq g). rewrite El, Esc, Ea, Ef.
assert (ING : In g (LSq (LActive (m_sizeclass (MR st g))))) by (unfold LSq; rewrite fupd_eq; apply in_app_iff; right; left; reflexivity).
split; [intros _; exact ING|]. split; [intros _ NI; exfalso; apply NI; eexists; exact ING|].
split; [intros sc _ _; split; [exact AZ|]; rewrite FZ, Z.lor_0_l; unfold bit; pose proof (Z.pow_pos_nonneg 2 i); lia|].
intros Hsc' LT. exfalso. pose proof (C3 Hsc') as GE.
replace (get_stride (m_set_freed (Z.lor (m_freed (MR st g)) (bit i)) (MR stq g))) with (get_stride (MR stq g)) in LT by (destruct (MR stq g); reflexivity).
rewrite (get_stride_data _ _ Dq) in LT. lia.
+
eexists _, None, LS. split; [reflexivity|]. split; [reflexivity|]. split; [repeat split; reflexivity|]. cbn.
apply (INVL_aor _ st L BL LS g bg ai i INV Hg Hi eq_refl).
* intros _ sc Hin Hnh. exact (proj1 (g_rest _ _ _ _ _ _ GO ltac:(discriminate) sc Hin Hnh)).
* intros _ Hsc. destruct (m_next (MR st g)) as [nx|] eqn:NX.
-- apply (proj2 (proj1 (il_link _ _ IL g))). rewrite NX. discriminate.
-- exfalso. destruct (g_unlisted _ _ _ _ _ _ GO ltac:(discriminate) Hsc (fun H => lists_notin st LS (old_lists _ _ _ _ _ INV) g NX _ (proj2 (In_nth _ _ g H) ))) || idtac.
assert (NIL : ~ in_list LS g) by (intros [h Hin]; exact (lists_notin st LS (old_lists _ _ _ _ _ INV) g NX h Hin)).
destruct (g_unlisted _ _ _ _ _ _ GO ltac:(discriminate) Hsc NIL) as [A0 F0]. apply MNZ. unfold mask. rewrite A0, F0. reflexivity.
* exact C3.
Qed.

#[using="Type"] Theorem ntf_spec : NTF_SPEC.
Proof.
intros T f X st L BL LS g bg i k bail INV Hg Hi HP HF HO F1 F2.
destruct (ntf_all T f dec_hdr dec_hdr (dec_hdr_ok T) (dec_hdr_ok T) X st L BL LS g bg i k bail INV Hg Hi HP HF HO F1 F2) as (st' & mi & LS' & EQ & _ & _ & POST).
exists st', mi, LS'. split; [exact EQ| exact POST].
Qed.

#[using="Type"] Theorem ntf_slots_agree T f X st L BL LS g bg i (k : mstate -> mapinfo -> M T) bail :
INVL X st L BL LS -> hosts st bg g -> 0 <= i <= m_last_idx (MR st g) ->
x_pend X = Some (fst bg, sstart (MR st g) i) -> x_fresh X = None -> x_orph X = None ->
(1 <= f)%nat -> 49 - m_sizeclass (MR st g) <= Z.of_nat f ->
nontrivial_free dec_slots f st g i k bail = nontrivial_free dec_hdr f st g i k bail.
Proof.
intros INV Hg Hi HP HF HO F1 F2.
destruct (ntf_all T f dec_hdr dec_slots (dec_hdr_ok T) (dec_slots_ok T) X st L BL LS g bg i k bail INV Hg Hi HP HF HO F1 F2) as (st' & mi & LS' & EQ1 & EQ2 & _).
rewrite EQ1, EQ2. reflexivity.
Qed.

#[using="Type"] Theorem ntf_spec2 T f : NTF_AT T f.
Proof. apply ntf_all. Qed.

#[using="Type"] Theorem free_INVL_closed st L BL LS c off n :
INVL x0 st L BL LS -> In ((c, off), n) BL ->
ftree L (free st (Some (aadd c (UNIT * off))))
(fun L' st' => exists LS', INVL x0 st' L' (bl_remove c BL) LS').
Proof. exact (free_INVL ntf_spec st L BL LS c off n). Qed.

End RC__1.
End Mq2.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Qfya QPiB.Mq0 Qatc QSfG.Mq2 Q7S0 QSfG.Mq0 QdBa.Mq1 QdBa.Mq0 QpFQ Ql2m.Mq1 QPiB QdBa.Mq2 Ql2m.Mq2 QYTG.Mq1 QjcB QLaA QLaA.Mq0 Q1am QoCS.Mq1.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma one5_A_to_E (A B C D E A' E' : Prop) : A -> ~ A' -> E' -> one5 A B C D E -> one5 A' B C D E'.
Proof. unfold one5. tauto. Qed.

Section TAFIN.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (m bm : aptr) (ai : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis HP : x_pend X = None.
Hypothesis HF : x_fresh X = None.
Hypothesis Hm : s_groups st !! bm = Some (mkGhdr (Some m) ai).
Hypothesis HEAD : head_of (LS (LActive (m_sizeclass (MR st m)))) = Some m.
Let mask := m_avail (MR st m).
Hypothesis MNZ : mask <> 0.
Let first := lowbit mask.
Let idx := ctz32 first.
Let st' := upd_meta m (m_set_avail (mask - first)) st.

#[using="HEAD"] Lemma tafin_listed : In m (LS (LActive (m_sizeclass (MR st m)))).
Proof. destruct (LS (LActive (m_sizeclass (MR st m)))); cbn in HEAD; [discriminate|]. inversion HEAD. left. reflexivity. Qed.

#[using="ai INV HP HF Hm HEAD MNZ"] Theorem ta_fin_ok :
INVL (xpend X (Some (fst bm, sstart (MR st m) idx))) st' L BL LS
/\ 0 <= idx <= m_last_idx (MR st m) /\ first <> 0 /\ 0 <= first
/\ UNIT * size_class (m_sizeclass (MR st m)) <= get_stride (MR st m).
Proof.
pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
pose proof (ig_ok _ _ _ IG _ _ _ Hm) as GO. pose proof (g_masks _ _ _ _ _ _ GO) as (M1 & M2 & M3 & M4 & M5 & M6).
pose proof (g_li _ _ _ _ _ _ GO) as LI. pose proof (g_ai _ _ _ _ _ _ GO) as AI.
assert (Hmh : hosts st bm m) by (exists ai; exact Hm).
assert (MPOS : 0 < mask) by (unfold mask in *; lia).
destruct (lowbit_idiom mask MPOS) as (k0 & K0 & EL & EC & TB & A0 & TA).
assert (Eidx : idx = k0) by (unfold idx, first; exact EC).
assert (Hk0 : k0 <= ai) by (apply M3; [exact K0| exact TB]).
assert (NU : UNIT * size_class (m_sizeclass (MR st m)) <= get_stride (MR st m)).
{ destruct (g_sc _ _ _ _ _ _ GO) as [[Hsc _]|(E63 & _)].
- destruct (Z.lt_ge_cases (get_stride (MR st m)) (UNIT * size_class (m_sizeclass (MR st m)))) as [LT|GE]; [| exact GE].
exfalso. destruct (g_under _ _ _ _ _ _ GO ltac:(rewrite HF; discriminate) ltac:(lia) LT) as [A _]. unfold mask in MNZ. exact (MNZ A).
- rewrite E63. change (size_class 63) with 0. pose proof (stride_ge _ _ _ IG _ _ Hmh) as [SG _]. unfold UNIT in *. lia. }
assert (Ef : st' = upd_meta m (fun r => m_set_avail (mask - first) (m_set_freed (m_freed (MR st m)) r)) st).
{ unfold st', upd_meta, MR. destruct (get_meta_rec st m); reflexivity. }
rewrite Ef.
assert (FNZ : first <> 0 /\ 0 <= first) by (unfold first; rewrite EL; clear -K0; pose proof (Z.pow_pos_nonneg 2 k0); split; [lia| apply Z.pow_nonneg; lia]).
rewrite Eidx.
pose proof (stride_ge _ _ _ IG _ _ Hmh) as [SG _].
split; [| split; [clear -K0 Hk0 AI; lia| split; [exact (proj1 FNZ)| split; [exact (proj2 FNZ)| exact NU]]]]. replace X with (mkX (x_idle X) (x_zomb X) (x_pend X) (x_orph X) (x_fresh X)) at 1 by (destruct X; reflexivity).
apply (INVL_mask_change X st L BL LS m bm ai (mask - first) (m_freed (MR st m)) (Some (fst bm, sstart (MR st m) k0)) INV Hm).
- unfold first. split; [exact A0|]. split; [exact M2|]. split; [| split; [exact M4| split; [| exact M6]]].
+ intros i Hi. unfold tbit. rewrite TA by exact Hi. rewrite Bool.andb_true_iff. intros [H _]. exact (M3 i Hi H).
+ intros i Hi. unfold tbit. rewrite TA by exact Hi. rewrite Bool.andb_true_iff. intros [H _]. exact (M5 i Hi H).
- intros j Hj. cbn zeta. unfold first, tbit. rewrite TA by (clear -Hj; lia).
pose proof (is_part _ _ _ IS _ _ _ j Hm Hj) as P. cbn zeta in P. rewrite HP in P. rewrite (slot_start'_eq _ _ _ IM _ _ _ Hmh) in P |- *.
unfold tbit in P. destruct (Z.eqb_spec k0 j) as [<-|NE].
+ eapply one5_A_to_E; [exact TB| rewrite TB; cbn; discriminate| reflexivity| exact P].
+ rewrite Bool.andb_true_r. eapply one5_iff; [reflexivity| reflexivity| reflexivity| reflexivity| | exact P].
split; [discriminate|]. intros E. exfalso. inversion E.
destruct (Z.lt_total k0 j) as [LT|[EQ|LT]]; [| lia|].
* pose proof (sstart_lt _ _ _ IG _ _ k0 j Hmh LT) as SL. clear -SL SG H0. unfold UNIT in *. lia.
* pose proof (sstart_lt _ _ _ IG _ _ j k0 Hmh LT) as SL. clear -SL SG H0. unfold UNIT in *. lia.
- right. split; [rewrite HP; discriminate|]. intros s Hs. inversion Hs. subst s. exists k0. split; [clear -K0 Hk0 AI; lia|]. rewrite (slot_start'_eq _ _ _ IM _ _ _ Hmh). reflexivity.
- intros _ sc Hin Hnh. exfalso. destruct (il_active _ _ IL sc m Hin) as (_ & _ & Esc). subst sc. exact (Hnh (eq_sym HEAD)).
- intros _ _ NI. exfalso. apply NI. eexists. exact tafin_listed.
- intros _ Hsc LT. exfalso. clear -LT NU. lia.
Qed.
End TAFIN.

Section SETAI.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (m b : aptr) (ai ai' : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hm : s_groups st !! b = Some (mkGhdr (Some m) ai).
Hypothesis Hai' : ai <= ai' <= m_last_idx (MR st m).
Hypothesis AV : forall i, 0 <= i -> tbit (m_avail (MR st m)) i = true -> i <= ai'.
Hypothesis LISTED : ai' < m_last_idx (MR st m) -> In m (LS (LActive (m_sizeclass (MR st m)))).
Let st' := QUZl.set_groups (<[b := mkGhdr (Some m) ai']> (s_groups st)) st.

#[using="Type"] Lemma sa_lookup bb : s_groups st' !! bb = if aptr_eqb bb b then Some (mkGhdr (Some m) ai') else s_groups st !! bb.
Proof.
unfold st'. cbn. destruct (aptr_eqb_spec bb b) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity.
Qed.
#[using="LS ai Hm Hai' AV LISTED"] Lemma sa_hosts bb x : hosts st' bb x <-> hosts st bb x.
Proof.
unfold hosts. rewrite sa_lookup. destruct (aptr_eqb_spec bb b) as [->|NE]; [| tauto].
split; intros [a H]; [rewrite Hm; inversion H; subst; eexists; reflexivity| rewrite Hm in H; inversion H; subst; eexists; reflexivity].
Qed.
#[using="LS ai Hm Hai' AV LISTED"] Lemma sa_live x : live_group st' x <-> live_group st x.
Proof. unfold live_group. split; intros [bb H]; exists bb; apply sa_hosts; exact H. Qed.

#[using="ai INV Hm Hai' AV LISTED"] Theorem INVL_set_ai : INVL X st' L BL LS.
Proof.
pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
pose proof (ig_ok _ _ _ IG _ _ _ Hm) as GO. pose proof (g_ai _ _ _ _ _ _ GO) as AI.
assert (GNE : forall bb h, s_groups st' !! bb = Some h -> (bb = b /\ h = mkGhdr (Some m) ai') \/ (bb <> b /\ s_groups st !! bb = Some h)).
{ intros bb h. rewrite sa_lookup. destruct (aptr_eqb_spec bb b) as [->|NE]; [intros H; inversion H; auto| auto]. }
assert (GN : forall bb, s_groups st' !! bb <> None <-> s_groups st !! bb <> None).
{ intros bb. rewrite sa_lookup. destruct (aptr_eqb_spec bb b) as [->|NE]; [rewrite Hm; split; discriminate| tauto]. }
split; [| split; [| split; [| split; [| split; [| split]]]]].
- destruct IR; constructor; try assumption.
intros rid Ho. destruct (ir_orph rid Ho) as (r & Hr & K & NG). exists r. split; [exact Hr|]. split; [exact K|].
intros bb Hbb. rewrite sa_lookup. destruct (aptr_eqb_spec bb b) as [->|NE]; [| exact (NG bb Hbb)]. specialize (NG b Hbb). rewrite Hm in NG. discriminate.
- destruct IA; constructor; try assumption.
intros sc Hsc. change (usage st' sc) with (usage st sc). rewrite (ia_usage sc Hsc). unfold gcnt.
change (s_groups st') with (<[b:=mkGhdr (Some m) ai']> (s_groups st)).
rewrite <- (zsum_perm _ _ (Permutation_map _ (map_to_list_delete (s_groups st) b _ Hm))).
rewrite <- (zsum_perm _ _ (Permutation_map _ (map_to_list_delete (<[b:=mkGhdr (Some m) ai']> (s_groups st)) b (mkGhdr (Some m) ai') ltac:(apply lookup_insert_eq)))).
cbn [map zsum fold_right snd g_meta]. rewrite delete_insert_eq. reflexivity.
- destruct IM as [Q1 Q2 Q3 Q4 Q5]; constructor; try assumption.
+ intros x bb Hx. destruct (Q2 x bb Hx) as [H|H]; [left; apply sa_hosts; exact H| right; exact H].
+ intros bb h Hbb. apply GNE in Hbb as [[-> ->]|[NE Hbb]]; [| exact (Q3 bb h Hbb)].
exists m. cbn [g_meta g_active_idx]. split; [reflexivity|]. split; [exact (hosts_mem _ _ _ (mkIM _ _ _ Q1 Q2 Q3 Q4 Q5) _ _ (ex_intro _ ai Hm))| change (MR st' m) with (MR st m); lia].
+ intros z Hz. destruct (Q5 z Hz) as (A1 & A2 & A3 & bz & A4 & A5). split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
exists bz. split; [exact A4|]. rewrite sa_lookup. destruct (aptr_eqb_spec bz b) as [->|NE]; [rewrite Hm in A5; discriminate| exact A5].
- destruct IL as [L1 L2 L3 L4 L5 L6 L7 L9]; constructor; try assumption.
+ intros h. apply (dll_ext_metas st st' eq_refl). apply L2.
+ intros sc x Hx. destruct (L7 sc x Hx) as (B1 & B2 & B3). split; [exact B1|]. split; [apply sa_live; exact B2| exact B3].
- destruct IG as [G1 G2 G3 G4 G5]; constructor.
+ intros x bb aix Hbb. apply GNE in Hbb as [[-> E]|[NE Hbb]].
* inversion E. subst x aix. destruct GO; constructor; change (MR st') with (MR st); try assumption.
-- lia.
-- destruct g_masks as (W1 & W2 & W3 & W4 & W5 & W6). split; [exact W1|]. split; [exact W2|]. split; [exact AV|]. split; [exact W4|]. split; [exact W5|].
intros i Hi. apply W6. lia.
-- intros NF Hlt. apply LISTED. exact Hlt.
-- intros Hsc0. pose proof (g_full0 Hsc0). lia.
* apply (group_ok_ext X st st'); [reflexivity| reflexivity| auto| exact (G1 x bb aix Hbb)].
+ intros bb aix Hbb. apply GNE in Hbb as [[_ E]|[NE Hbb]]; [discriminate| exact (G2 bb aix Hbb)].
+ intros m1 m2 b1 b2 ai1 ai2 H1 H2 P1 P2 Esc. change (MR st') with (MR st) in P1, P2, Esc.
apply GNE in H1 as [[-> E1]|[N1 H1]]; apply GNE in H2 as [[-> E2]|[N2 H2]].
* inversion E1. inversion E2. subst. reflexivity.
* inversion E1. subst m1 ai1. eapply G3; [exact Hm| exact H2| lia| exact P2| exact Esc].
* inversion E2. subst m2 ai2. eapply G3; [exact H1| exact Hm| exact P1| lia| exact Esc].
* eapply G3; eassumption.
+ intros rid r Hr K Ho. destruct (G4 rid r Hr K Ho) as (x & Hx & Hml). exists x. split; [apply sa_hosts; exact Hx| exact Hml].
+ intros bb h Hbb. apply GNE in Hbb as [[-> _]|[NE Hbb]]; [exact (G5 _ _ Hm)| exact (G5 bb h Hbb)].
- destruct IS as [S1 S2 S3 S4 S5 S6]; constructor; try assumption.
+ intros s x i Hs. destruct (S1 s x i Hs) as (B1 & B2 & B3). split; [apply sa_live; exact B1| auto].
+ intros bb x i Hbb Hi. apply (S2 bb); [apply sa_hosts; exact Hbb| exact Hi].
+ intros bb x aix i Hbb Hi. cbn zeta. change (MR st') with (MR st) in Hi |- *.
eapply one5_iff; [reflexivity| reflexivity| reflexivity| apply iff_sym; apply GN| reflexivity|].
apply GNE in Hbb as [[-> E]|[NE Hbb]]; [inversion E; subst x aix; exact (S3 b m ai i Hm Hi)| exact (S3 bb x aix i Hbb Hi)].
- destruct ISH as [D1 D2 D3 D4 D5 D6]; constructor; try assumption.
+ intros bb x i Hbb Hi. apply (D3 bb x i); [apply sa_hosts; exact Hbb| exact Hi].
+ intros bb x o Hbb Ho. apply (D4 bb x o); [apply sa_hosts; exact Hbb| exact Ho].
+ intros bb x p i Hbb Hml Hs. apply (D5 bb x p i); [apply sa_hosts; exact Hbb| exact Hml| exact Hs].
Qed.
End SETAI.

#[using="Type"] Lemma span_loop_ge f : forall cnt span size, cnt <= span_loop f cnt span size.
Proof. induction f as [|f IH]; intros; cbn; [lia|]. destruct (_ <? _); [| lia]. pose proof (IH (cnt + 1) (span + size) size). lia. Qed.

End RC__1.
End Mq3.

From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfya.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfya. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPiB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPiB.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qatc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qatc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSfG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSfG.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdBa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdBa.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdBa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdBa.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpFQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpFQ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPiB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPiB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdBa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdBa.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYTG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYTG.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjcB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjcB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLaA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLaA.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1am.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1am.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QoCS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QoCS.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition am_init (st : mstate) : mstate :=
if c_init_done (ctx st) =? 0 then upd_ctx (fun c => set_init_done 1 (set_secret (s_secret st) c)) st else st.

#[using="Type"] Lemma INVL_am_init X st L BL LS : INVL X st L BL LS ->
INVL X (am_init st) L BL LS /\ c_init_done (s_ctx (am_init st)) = 1 /\ AM_frame st (am_init st).
Proof.
intros INV. pose proof INV as (IR & IA & IM & IL & IG & IS & ISH). unfold am_init, ctx.
destruct (ia_secret _ IA) as [S0 [(I0 & C0 & A0)|(I1 & C1)]].
- rewrite I0. cbn. set (st' := upd_ctx _ st).
split; [| split; [reflexivity| constructor; cbn; auto; first [reflexivity| lia]]].
split; [| split; [| split; [| split; [| split; [| split]]]]].
+ destruct IR; constructor; try assumption.
+ destruct IA; constructor; try assumption.
* cbn. split; [exact S0|]. right. auto.
* intros a ar Ha. change (s_areas st') with (s_areas st) in Ha. rewrite A0 in Ha. rewrite lookup_empty in Ha. discriminate.
+ apply (inv_M_ext X st st'); [reflexivity| reflexivity| exact IM].
+ apply (inv_L_ext st st'); [reflexivity| reflexivity| intros h; destruct h; reflexivity| exact IL].
+ destruct IG as [G1 G2 G3 G4 G5]; constructor; try assumption.
intros m b ai Hb. apply (group_ok_ext X st st'); [reflexivity| reflexivity| auto| exact (G1 m b ai Hb)].
+ apply (inv_S_ext X st st' BL); [reflexivity| reflexivity| reflexivity| exact IS].
+ apply (inv_SH_view st st'); try reflexivity. exact ISH.
- rewrite I1. cbn. split; [exact INV|]. split; [exact I1| apply amf_refl].
Qed.

Section AM.
Variables (T : Type) (BL : list blk) (Post : mled -> T -> Prop) (k : mstate -> optr -> M T) (bail : M T).
Variables (X : extras) (st0 : mstate) (L0 : mled).
Hypothesis KN : forall st1 L1 LS1, INVL X st1 L1 BL LS1 -> AM_frame st0 st1 -> L_frame L0 L1 -> ftree L1 (k st1 None) Post.
Hypothesis KS : forall st1 L1 LS1 m, INVL (xidle X (m :: x_idle X)) st1 L1 BL LS1 -> ~ In m (x_idle X) -> AM_frame st0 st1 -> L_frame L0 L1 -> ftree L1 (k st1 (Some m)) Post.

#[using="KS"] Lemma am_take_ft st L LS : INVL X st L BL LS -> AM_frame st0 st -> L_frame L0 L ->
0 < c_avail_meta_count (s_ctx st) -> ftree L (am_take st k bail) Post.
Proof.
intros INV AF LF HC. destruct (am_take_ok X st L BL LS INV HC k bail) as (m & st2 & -> & INV2 & AF2 & NI).
eapply KS; [exact INV2| exact NI| exact (amf_trans _ _ _ AF AF2)| exact LF].
Qed.

#[using="KS"] Lemma am_carve_ft s p L LS : INVL X s L BL LS ->
c_avail_meta_areas (s_ctx s) = Some (aadd p 4096) -> s_areas s !! p = None -> (forall k, 0 <= k < NSLOTS -> s_metas s !! mslot p k = None) ->
PGSZ <= snd p -> snd p mod PGSZ = 0 -> c_init_done (s_ctx s) = 1 ->
AM_frame st0 s -> L_frame L0 L -> ftree L (am_take (carve_rest s p) k bail) Post.
Proof.
intros INV H1 H2 H3 H4 H5 H6 AF LF. destruct (INVL_carve X s L BL LS p INV H1 H2 H3 H4 H5 H6) as (INV' & AF' & HC).
eapply am_take_ft; [exact INV'| exact (amf_trans _ _ _ AF AF')| exact LF| exact HC].
Qed.

#[using="KN KS"] Lemma am_finish_ft st L LS : INVL X st L BL LS -> AM_frame st0 st -> L_frame L0 L ->
0 < c_avail_meta_area_count (s_ctx st) -> c_init_done (s_ctx st) = 1 ->
ftree L (am_finish st true k bail) Post.
Proof.
intros INV AF LF HC HI.
destruct (ir_cursor _ _ _ (proj1 INV)) as (C1 & C2 & C3).
destruct (c_avail_meta_areas (ctx st)) as [[rid off]|] eqn:EC; [| exfalso; exact (C2 HC EC)].
destruct (C3 _ _ EC) as (r & Hr & K & P1 & P2 & P3 & P4).
unfold am_finish. rewrite EC. cbn [snd]. rewrite (proj2 (Z.eqb_eq _ _) P2). cbn [negb].
apply ftree_vis; [reflexivity| reflexivity| exact (ma_event_pre X st L BL LS rid off INV EC HC)| |].
- intros a Ha. cbn in Ha. rewrite Ha. cbn [negb].
change (if (a =? 0) || (a =? TWO64 - ENOSYS) then am_carve st (rid, off) k bail else k st None)
with (if (a =? 0) || (a =? TWO64 - ENOSYS) then am_carve st (rid, off) k bail else k st None).
cbn [event_post]. destruct ((a =? 0) || (a =? TWO64 - ENOSYS)).
+ rewrite am_carve_eq.
destruct (INVL_meta_adv X st L BL LS rid off INV EC HC) as (INV' & F1 & F2 & F3 & F4 & F5 & F6 & AF').
eapply am_carve_ft; [exact INV'| exact F1| exact F2| exact F3| exact F4| exact F5| rewrite F6; exact HI| exact (amf_trans _ _ _ AF AF')|].
destruct LF; constructor; assumption.
+ eapply KN; [exact INV| exact AF| exact LF].
- intros a Ha. cbn in Ha. rewrite Ha. exact I.
Qed.

#[using="KN KS"] Lemma am_after_brk_ft st L LS : INVL X st L BL LS -> AM_frame st0 st -> L_frame L0 L ->
c_init_done (s_ctx st) = 1 -> ftree L (am_after_brk st true k bail) Post.
Proof.
intros INV AF LF HI. unfold am_after_brk.
destruct (Z.eqb_spec (c_avail_meta_area_count (ctx st)) 0) as [HC|HC].
- apply ftree_vis; [reflexivity| reflexivity| exact (nm_event_pre X st L BL LS INV)| |].
+ intros a Ha. unfold answer_ok in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn [andb] in Ha.
rewrite (mmap_answer_ok_eq X st L (proj1 INV)) in Ha. unfold ctx. rewrite Ha. cbn [negb].
unfold event_post. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. change (PROT_NONE =? PROT_NONE) with true. cbn [andb].
destruct (is_err a) eqn:NE.
* eapply KN; [exact INV| exact AF| exact LF].
* destruct (INVL_new_meta X st L BL LS a INV HC Ha NE) as (INV' & HC' & HI' & AF').
eapply am_finish_ft; [exact INV'| exact (amf_trans _ _ _ AF AF')| destruct LF; constructor; assumption| exact HC'| rewrite HI'; exact HI].
+ intros a Ha. unfold answer_ok in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn [andb] in Ha.
rewrite (mmap_answer_ok_eq X st L (proj1 INV)) in Ha. unfold ctx. rewrite Ha. exact I.
- eapply am_finish_ft; [exact INV| exact AF| exact LF| pose proof (proj1 (ir_cursor _ _ _ (proj1 INV))); unfold ctx in HC; lia| exact HI].
Qed.

#[using="Type"] Lemma lbrk_pages_ok_ext L1 L2 lo len :
ld_resv L1 = ld_resv L2 -> ld_groups L1 = ld_groups L2 -> ld_metas L1 = ld_metas L2 -> ld_brkreg L1 = ld_brkreg L2 ->
lbrk_pages_ok L1 lo len = lbrk_pages_ok L2 lo len.
Proof. intros E1 E2 E3 E4. unfold lbrk_pages_ok, lranges. rewrite E1, E2, E3, E4. reflexivity. Qed.

#[using="Type"] Lemma dequeue_free_hmetas X' s L LS' m rest :
INVL X' s L BL LS' -> LS' LFree = m :: rest ->
forall b m0 ai, s_groups s !! b = Some (mkGhdr (Some m0) ai) -> MR (dequeue LFree m s) m0 = MR s m0.
Proof.
intros INV ELS b m0 ai Hb. pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
pose proof (inv_L_lists _ _ IL) as LO.
assert (Hm : In m (LS' LFree)) by (rewrite ELS; left; reflexivity).
assert (NF : forall x, In x (LS' LFree) -> x <> m0).
{ intros x Hx ->. pose proof (il_free _ _ IL m0 Hx) as E.
destruct (im_hdr _ _ _ IM b _ Hb) as (m1 & E1 & MM & _). cbn in E1. injection E1 as <-. rewrite E in MM. cbn in MM. discriminate. }
unfold MR at 1. unfold get_meta_rec. rewrite (dequeue_metas_other LFree m s m0); [reflexivity| | |].
- intros ->. exact (NF m Hm eq_refl).
- intros E. destruct (lists_prev_in s LS' LO LFree m Hm) as (y & Hy & Ey & _). rewrite Ey in E. injection E as ->. exact (NF _ Hy eq_refl).
- intros E. destruct (lists_next_in s LS' LO LFree m Hm) as (y & Hy & Ey & _). rewrite Ey in E. injection E as ->. exact (NF _ Hy eq_refl).
Qed.

#[using="KN KS"] Theorem alloc_meta_ft st L LS : INVL X st L BL LS -> AM_frame st0 st -> L_frame L0 L -> ftree L (alloc_meta st k bail) Post.
Proof.
intros INV0 AF0 LF.
destruct (INVL_am_init X st L BL LS INV0) as (INV & HI & AFi).
pose proof (amf_trans _ _ _ AF0 AFi) as AF. clear AF0 AFi INV0.
unfold alloc_meta. fold (am_init st). set (s := am_init st) in *. clearbody s.
pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).

destruct (c_free_meta_head (ctx s)) as [m|] eqn:EFH.
{ pose proof (il_head _ _ IL LFree) as HH. cbn in HH. unfold ctx in EFH. rewrite EFH in HH.
destruct (LS LFree) as [|m' rest] eqn:ELS; [discriminate|]. cbn in HH. inversion HH. subst m'.
pose proof (INVL_dequeue X (xidle X (m :: x_idle X)) s L BL LS m LFree [] rest INV ltac:(rewrite ELS; reflexivity) ltac:(right; split; reflexivity)) as INV1.
destruct (dequeue_frame LFree m s) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & FC).
eapply KS; [exact INV1| | | exact LF].
{ intros Hin. apply (proj2 (im_idle _ _ _ IM m Hin)). exists LFree. rewrite ELS. left. reflexivity. }
eapply amf_trans; [exact AF|]. destruct FC. constructor; auto; try congruence.
all: try (intros sc; change (active (dequeue LFree m s) sc) with (get_head (dequeue LFree m s) (LActive sc)); rewrite dequeue_head;
destruct (decide (LActive sc = LFree)); [discriminate| reflexivity]).
all: try (intros sc; unfold usage, ctx; rewrite cb_usage; reflexivity).
all: try (intros rid r H _; rewrite F1; exact H).
all: try (rewrite ?F3; lia).
exact (dequeue_free_hmetas _ s L LS m rest INV ELS). }

destruct (Z.eqb_spec (c_avail_meta_count (ctx s)) 0) as [HAC|HAC]; cbn [negb].
2:{ eapply am_take_ft; [exact INV| exact AF| exact LF| pose proof (proj1 (ia_avail _ IA)); unfold ctx in HAC; lia]. }

destruct (Z.eqb_spec (c_avail_meta_area_count (ctx s)) 0) as [HC|HC]; cbn [andb].
2:{ eapply am_after_brk_ft; [exact INV| exact AF| exact LF| exact HI]. }
pose proof (ir_brk _ _ _ IR) as IBK. unfold ctx. destruct (c_brk (s_ctx s)) as [| |rid off] eqn:EBRK; cbn [negb].
-
destruct IBK as [BP NB].
apply ftree_vis; [reflexivity| reflexivity| left; auto| |].
2:{ intros cur Hc. cbn in Hc. rewrite Hc. exact I. }
intros cur Hc. cbn in Hc. rewrite Hc. cbn [negb]. cbn [event_post Z.eqb].
set (L1 := Qfya.set_brkph (BPQueried cur) L).
set (base := round_up_pg cur). set (new := base + 2 * PGSZ).
assert (NZ : (new =? 0) = false).
{ apply Z.eqb_neq. unfold new, base. pose proof (round_up_ge cur). unfold brk0_answer_ok in Hc.
apply Bool.andb_true_iff in Hc as [Hc _]. apply Bool.andb_true_iff in Hc as [Hc _]. apply Z.ltb_lt in Hc. unfold PGSZ. lia. }
apply ftree_vis; [reflexivity| reflexivity| right; left; exists cur; split; reflexivity| |].
+ intros r Hr. unfold answer_ok in Hr. rewrite NZ in Hr. unfold L1 in Hr. cbn [Qfya.ld_brk Qfya.set_brkph] in Hr.
apply Bool.andb_true_iff in Hr as [Hb Hp]. rewrite Hb. cbn [negb].
unfold event_post. rewrite NZ. unfold L1. cbn [Qfya.ld_brk Qfya.set_brkph].
destruct (Z.eqb_spec r new) as [->|NE]; cbn [negb].
* cbn [negb orb] in Hp.
rewrite (lbrk_pages_ok_ext (Qfya.set_brkph (BPQueried cur) L) L) in Hp by reflexivity.
rewrite (brk_pages_ok_eq X s L IR) in Hp. fold base in Hp. rewrite Hp. cbn [negb].
apply ftree_vis; [reflexivity| reflexivity| right; exists cur; cbn; repeat split; reflexivity| |].
-- intros rg Hg. unfold answer_ok in Hg. change (Z.land (MAP_PRIVATE + MAP_ANON + MAP_FIXED) MAP_FIXED =? 0) with false in Hg. cbn [andb] in Hg.
fold base in Hg. rewrite Hg. cbn [negb]. unfold event_post. change (Z.land (MAP_PRIVATE + MAP_ANON + MAP_FIXED) MAP_FIXED =? 0) with false. cbn [andb].
set (st1 := new_region RKBrk base (2 * PGSZ) s). destruct st1 as [s1 rid] eqn:ES1.
assert (Erid : rid = s_next_rid s) by (unfold st1, new_region in ES1; inversion ES1; reflexivity).
assert (Es1 : s1 = fst (new_region RKBrk base (2 * PGSZ) s)) by (unfold st1 in ES1; rewrite <- ES1 || idtac; unfold new_region in *; inversion ES1; reflexivity).
subst rid s1.
unfold am_after_brk, ctx. cbn [c_avail_meta_area_count s_ctx upd_ctx set_avail_meta_area_count set_avail_meta_areas set_brk Z.eqb].
unfold am_finish, ctx. cbn [c_avail_meta_areas s_ctx upd_ctx set_avail_meta_area_count set_avail_meta_areas set_brk snd].
change (PGSZ mod PGSZ =? 0) with true. cbn [negb].
rewrite am_carve_eq.
destruct (INVL_brk_first X s L BL LS cur INV EBRK HC ltac:(exact Hp) (Qfya.set_brkph (BPGuard cur) (Qfya.set_brkph (BPQueried cur) L)) ltac:(repeat split; reflexivity))
as (INV' & G1 & G2 & G3 & G4 & G5 & G6 & AF').
eapply am_carve_ft; [exact INV'| exact G1| exact G2| exact G3| exact G4| exact G5| rewrite G6; exact HI| exact (amf_trans _ _ _ AF AF')|].
destruct LF; constructor; assumption.
-- intros rg Hg. unfold answer_ok in Hg. change (Z.land (MAP_PRIVATE + MAP_ANON + MAP_FIXED) MAP_FIXED =? 0) with false in Hg. cbn [andb] in Hg.
fold base in Hg. rewrite Hg. exact I.
* destruct (INVL_brk_dead X s L (Qfya.set_brkph BPDead (Qfya.set_brkph (BPQueried cur) L)) BL LS INV eq_refl eq_refl eq_refl eq_refl eq_refl) as [INV' AF'].
eapply am_after_brk_ft; [exact INV'| exact (amf_trans _ _ _ AF AF')| destruct LF; constructor; assumption| cbn; exact HI].
+ intros r Hr. unfold answer_ok in Hr. rewrite NZ in Hr. unfold L1 in Hr. cbn [Qfya.ld_brk Qfya.set_brkph] in Hr.
apply Bool.andb_false_iff in Hr. destruct Hr as [Hb|Hp].
* rewrite Hb. exact I.
* destruct (brk_answer_ok cur new r); [| exact I]. cbn [negb].
apply Bool.orb_false_iff in Hp as [Hn Hp]. apply Bool.negb_false_iff in Hn. rewrite Hn. cbn [negb].
rewrite (lbrk_pages_ok_ext (Qfya.set_brkph (BPQueried cur) L) L) in Hp by reflexivity.
rewrite (brk_pages_ok_eq X s L IR) in Hp. fold base in Hp. rewrite Hp. exact I.
-  eapply am_after_brk_ft; [exact INV| exact AF| exact LF| exact HI].
-
destruct IBK as [BP (r & Hr & K & Elen)].
pose proof (bg_event_pre X s L BL LS rid off INV EBRK) as PRE.
set (old := conc s (rid, off)) in *. set (new := old + PGSZ) in *.
assert (NZ : (new =? 0) = false).
{ apply Z.eqb_neq. unfold new, old, conc, get_region. rewrite Hr. cbn [fst snd]. pose proof (ir_shape _ _ _ IR _ _ Hr) as (S1 & _ & S3 & _). unfold PGSZ. lia. }
assert (BR : ld_brkreg L = Some (r_base r, off)).
{ apply (proj2 (ir_brkreg _ _ _ IR (r_base r) off)). exists rid, r. auto. }
assert (Eold : old = r_base r + off) by (unfold old, conc, get_region; rewrite Hr; cbn [fst snd]; reflexivity).
apply ftree_vis; [reflexivity| reflexivity| exact PRE| |].
+ intros z Hz. unfold answer_ok in Hz. rewrite NZ, BP, BR in Hz. rewrite <- Eold in Hz.
apply Bool.andb_true_iff in Hz as [Hb Hp]. rewrite Hb. cbn [negb].
unfold event_post. rewrite NZ, BP, BR.
destruct (Z.eqb_spec z new) as [->|NE]; cbn [negb].
* cbn [negb orb] in Hp. rewrite (brk_pages_ok_eq X s L IR) in Hp. rewrite Hp. cbn [negb].
unfold am_after_brk, ctx. cbn [c_avail_meta_area_count s_ctx upd_ctx set_avail_meta_area_count set_avail_meta_areas set_brk Z.eqb].
unfold am_finish, ctx. cbn [c_avail_meta_areas s_ctx upd_ctx set_avail_meta_area_count set_avail_meta_areas set_brk snd].
destruct (bg_region X s L BL LS rid off INV EBRK) as (r' & _ & _ & _ & _ & _ & _ & _ & OM & _).
rewrite (proj2 (Z.eqb_eq _ _) OM). cbn [negb].
rewrite am_carve_eq.
destruct (INVL_brk_grow X s L BL LS rid off INV EBRK HC ltac:(exact Hp)) as (INV' & G1 & G2 & G3 & G4 & G5 & G6 & AF').
replace (conc s (rid, off) - off) with (r_base r) in INV' by (unfold conc, get_region; rewrite Hr; cbn [fst snd]; lia).
eapply am_carve_ft; [exact INV'| exact G1| exact G2| exact G3| exact G4| exact G5| rewrite G6; exact HI| exact (amf_trans _ _ _ AF AF')|].
destruct LF; constructor; assumption.
* destruct (INVL_brk_dead X s L (Qfya.set_brkph BPDead L) BL LS INV eq_refl eq_refl eq_refl eq_refl eq_refl) as [INV' AF'].
eapply am_after_brk_ft; [exact INV'| exact (amf_trans _ _ _ AF AF')| destruct LF; constructor; assumption| cbn; exact HI].
+ intros z Hz. unfold answer_ok in Hz. rewrite NZ, BP, BR in Hz. rewrite <- Eold in Hz.
apply Bool.andb_false_iff in Hz. destruct Hz as [Hb|Hp].
* rewrite Hb. exact I.
* destruct (brk_answer_ok old new z); [| exact I]. cbn [negb].
apply Bool.orb_false_iff in Hp as [Hn Hp]. apply Bool.negb_false_iff in Hn. rewrite Hn. cbn [negb].
rewrite (brk_pages_ok_eq X s L IR) in Hp. rewrite Hp. exact I.
Qed.
End AM.

End RC__1.
