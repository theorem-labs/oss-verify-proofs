(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfya.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfya. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPiB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPiB.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qatc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qatc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSfG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSfG.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdBa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdBa.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdBa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdBa.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpFQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpFQ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPiB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPiB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYTG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYTG.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdBa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdBa.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QaiD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QaiD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLaA.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQg5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQg5.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1am.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1am.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSfG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSfG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QoCS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QoCS.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQCz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQCz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcV4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QcV4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7RC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7RC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQg5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQg5.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlOh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlOh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QhnL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QhnL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4en.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4en. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBv7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBv7.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Set Implicit Arguments.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Inductive strelU {R1 R2 : Type} (RR : R1 -> R2 -> Prop) : M R1 -> M R2 -> Prop :=
| strelU_ret : forall r1 r2, RR r1 r2 -> strelU RR (SRet r1) (SRet r2)
| strelU_undef : forall w k1 k2, strelU RR (SVis (EUndef w) k1) (SVis (EUndef w) k2)
| strelU_vis : forall e k1 k2, (forall a, strelU RR (k1 a) (k2 a)) -> strelU RR (SVis e k1) (SVis e k2).

#[using="Type"] Lemma strel_strelU {R1 R2} (RR : R1 -> R2 -> Prop) t1 t2 : strel RR t1 t2 -> strelU RR t1 t2.
Proof. induction 1; [constructor; assumption| apply strelU_vis; assumption]. Qed.

#[using="Type"] Lemma strelU_mono {R1 R2} (RR RR' : R1 -> R2 -> Prop) t1 t2 :
(forall a b, RR a b -> RR' a b) -> strelU RR t1 t2 -> strelU RR' t1 t2.
Proof. intros H. induction 1; [constructor; auto| apply strelU_undef| apply strelU_vis; assumption]. Qed.

#[using="Type"] Lemma strelU_steq_l {R1 R2} (RR : R1 -> R2 -> Prop) (t1 t1' : M R1) (t2 : M R2) :
steq t1 t1' -> strelU RR t1' t2 -> strelU RR t1 t2.
Proof.
intros H; revert t2; induction H; intros t2 Ht; inversion Ht; subst;
first [constructor; assumption | apply strelU_undef | apply strelU_vis; intros a; eauto].
Qed.

#[using="Type"] Lemma strelU_sbind_fk {R1 R2 S1 S2} (RR : R1 -> R2 -> Prop) (SS : S1 -> S2 -> Prop)
(t1 : M R1) (t2 : M R2) (f1 : R1 -> M S1) (f2 : R2 -> M S2) :
strelU RR t1 t2 ->
(forall ans rest x1 x2, followk t1 ans = Some (x1, rest) -> followk t2 ans = Some (x2, rest) -> RR x1 x2 ->
strelU SS (f1 x1) (f2 x2)) ->
strelU SS (sbind t1 f1) (sbind t2 f2).
Proof.
intros H. induction H as [r1 r2 Hr| w k1 k2| e k1 k2 Hk IH]; intros K; cbn [sbind].
- apply (K [] []); [reflexivity| reflexivity| exact Hr].
- apply strelU_undef.
- destruct e; try (apply strelU_undef; fail); apply strelU_vis; intros a; apply IH; intros ans rest x1 x2 H1 H2 HR;
apply (K (a :: ans) rest); cbn [followk]; assumption.
Qed.

#[using="Type"] Lemma strip_upd_shadow rid f st : strip (upd_shadow rid f st) = strip st.
Proof. reflexivity. Qed.

#[using="Type"] Lemma get_region_strip st rid : get_region (strip st) rid = get_region st rid.
Proof. reflexivity. Qed.

#[using="Type"] Lemma strip_remap_region rid nb nd g st :
strip (remap_region rid nb nd g st) = strip (remap_region rid nb nd g (strip st)).
Proof.
unfold remap_region, remap_bound. rewrite get_region_strip.
rewrite <- !strip_upd_meta, ?strip_upd_shadow, <- !strip_upd_region, ?strip_strip; reflexivity.
Qed.

#[using="Type"] Lemma get_shadow_upd_region rid f st q : get_shadow (upd_region rid f st) q = get_shadow st q.
Proof. unfold upd_region. destruct (get_region st rid); reflexivity. Qed.

#[using="Type"] Lemma get_shadow_upd_meta g f st q : get_shadow (upd_meta g f st) q = get_shadow st q.
Proof. reflexivity. Qed.

#[using="Type"] Lemma cell_read_truncate len sh o : 0 <= o < len -> cell_read (shadow_truncate len sh) o = cell_read sh o.
Proof.
intros Ho. unfold cell_read, shadow_truncate. cbn [r_cells r_hav r_havp].
rewrite !map_lookup_filter.
assert (H16 : 16 * (o / 16) < len) by (pose proof (Z_div_mod_eq_full o 16); pose proof (Z.mod_pos_bound o 16); lia).
assert (H4k : 4096 * (o / 4096) < len) by (pose proof (Z_div_mod_eq_full o 4096); pose proof (Z.mod_pos_bound o 4096); lia).
destruct (r_cells sh !! o) as [[v t]|] eqn:E1; destruct (r_hav sh !! (o / 16)) as [hl|] eqn:E2; destruct (r_havp sh !! (o / 4096)) as [hp|] eqn:E3; cbn;
repeat (rewrite option_guard_True by (cbn; lia)); cbn; reflexivity.
Qed.

#[using="Type"] Lemma cell_read_remap_region rid nb nd g st q :
(fst q = rid -> 0 <= snd q < remap_bound st rid nd) ->
cell_read (get_shadow (remap_region rid nb nd g st) (fst q)) (snd q) = cell_read (get_shadow st (fst q)) (snd q).
Proof.
intros Hq. unfold remap_region. rewrite get_shadow_upd_meta.
rewrite get_shadow_upd_shadow. destruct (N.eqb_spec (fst q) rid) as [E|NE].
- rewrite cell_read_truncate by (apply Hq; exact E). rewrite get_shadow_upd_region. rewrite E. reflexivity.
- rewrite get_shadow_upd_region. reflexivity.
Qed.

#[using="Type"] Lemma cell_read_truncate_beyond len sh o : len mod 4096 = 0 -> len <= o -> cell_read (shadow_truncate len sh) o = Known 0.
Proof.
intros Hal Ho. unfold cell_read, shadow_truncate. cbn [r_cells r_hav r_havp].
rewrite !map_lookup_filter.
assert (H16 : len <= 16 * (o / 16)) by (pose proof (Z_div_mod_eq_full o 16); pose proof (Z.mod_pos_bound o 16); pose proof (Z_div_mod_eq_full len 4096); nia).
assert (H4k : len <= 4096 * (o / 4096)) by (pose proof (Z_div_mod_eq_full o 4096); pose proof (Z.mod_pos_bound o 4096); pose proof (Z_div_mod_eq_full len 4096); nia).
destruct (r_cells sh !! o) as [[v t]|] eqn:E1; destruct (r_hav sh !! (o / 16)) as [hl|] eqn:E2; destruct (r_havp sh !! (o / 4096)) as [hp|] eqn:E3; cbn;
repeat (rewrite option_guard_False by (cbn; lia)); cbn; reflexivity.
Qed.

#[using="Type"] Lemma cell_read_remap_beyond rid nb nd g st o :
nd mod 4096 = 0 -> remap_bound st rid nd <= o ->
cell_read (get_shadow (remap_region rid nb nd g st) rid) o = Known 0.
Proof.
intros Hal Ho. unfold remap_region. rewrite get_shadow_upd_meta, get_shadow_upd_shadow, N.eqb_refl.
apply cell_read_truncate_beyond; [| exact Ho].
unfold remap_bound. pose proof (round_up_pg_spec (match get_region st rid with Some r => r_len r | None => 0 end)) as [_ B].
destruct (Z.min_spec nd (round_up_pg match get_region st rid with Some r => r_len r | None => 0 end)) as [[_ ->]|[_ ->]]; assumption.
Qed.

#[using="Type"] Lemma remap_bound_facts st L BL LS c off n0 m bm i ai a ar ka nd :
INVL x0 st L BL LS -> blk_facts st c off n0 m bm i ai a ar ka ->
m_maplen (MR st m) <> 0 -> m_last_idx (MR st m) = 0 ->
remap_bound st (fst bm) nd = Z.min nd (m_maplen (MR st m) * 4096)
/\ snd c + UNIT * off + n0 + IB <= m_maplen (MR st m) * 4096 /\ snd c = snd bm + UNIT /\ i = 0.
Proof.
intros INV BF ML LI0. pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
pose proof (ig_ok _ _ _ IG _ _ _ (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF)) as GO.
destruct (g_top _ _ _ _ _ _ GO ML) as (B0 & r & Hr & Kr & Eml & _).
assert (I0 : i = 0) by (pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF); lia).
pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF) as FIT. pose proof (bf_c _ _ _ _ _ _ _ _ _ _ _ BF) as Ec.
assert (STR : get_stride (MR st m) = m_maplen (MR st m) * 4096 - UNIT).
{ unfold get_stride. fold (MR st m). unfold MR in *. rewrite LI0. cbn [Z.eqb andb]. destruct (Z.eqb_spec (m_maplen (get_meta_rec st m)) 0); [lia| reflexivity]. }
split; [| split; [| split; [| exact I0]]].
- unfold remap_bound, get_region. rewrite Hr. unfold MR in *. rewrite Eml. reflexivity.
- rewrite Ec. cbn [snd]. unfold sstart, gbase. unfold MR in *. rewrite (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF). cbn [default snd]. unfold id. rewrite I0. unfold UNIT, IB in *. lia.
- rewrite Ec. cbn [snd]. unfold sstart, gbase. unfold MR in *. rewrite (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF). cbn [default snd]. unfold id. rewrite I0. lia.
Qed.

Section RC.
Context {O : Type} (pans : O -> aptr -> Z -> Z -> Z) (pupd : O -> ev -> Z -> O).
Hypothesis Hpans : forall o p c h, 0 <= pans o p c h < 256.
Local Notation PRUN := (prun pans pupd).

Definition RRREL (p : aptr) (x : O * (mstate * optr)) (y : mstate * option rr_where) : Prop :=
strip (fst (snd x)) = fst y /\
match snd (snd x), snd y with
| None, None => True
| Some p', Some RRSame => p' = p
| Some p', Some (RRNew b') => fst p' = fst (fst b') /\ exists off', snd p' = snd (fst b') + UNIT * off'
| _, _ => False
end.

#[using="Type"] Lemma prun_vis_keep {R} o e (k : Z -> M R) :
match e with EPeek _ _ _ => False | _ => True end ->
PRUN o (SVis e k) = SVis e (fun a => PRUN (pupd o e a) (k a)).
Proof. intros He. unfold prun. apply eruns_vis_keep. destruct e; try reflexivity. destruct He. Qed.

#[using="Type"] Lemma strelU_bad {R1 R2} (RR : O * R1 -> R2 -> Prop) o (b1 : M R1) (b2 : M R2) :
strelU RR (PRUN o (bad_answer b1)) (bad_answer b2).
Proof. unfold bad_answer. rewrite prun_vis_keep by exact I. apply strelU_undef. Qed.

#[using="Type"] Lemma strelU_guard {R1 R2} (RR : O * R1 -> R2 -> Prop) o tag c (k1 : M R1) (k2 : M R2) b1 b2 :
(c = true -> strelU RR (PRUN o k1) k2) -> strelU RR (PRUN o (guard tag c k1 b1)) (guard tag c k2 b2).
Proof. intros HK. unfold guard. destruct c; [apply HK; reflexivity|]. rewrite prun_vis_keep by exact I. apply strelU_undef. Qed.

#[using="Hpans"] Theorem realloc_body_control st L BL LS c off n0 n o :
INVL x0 st L BL LS -> In ((c, off), n0) BL -> 0 <= n ->
strelU (RRREL (aadd c (UNIT * off))) (PRUN o (realloc_body st (aadd c (UNIT * off)) n)) (crealloc (strip st) c off n).
Proof.
intros INV Hk Hn.
destruct (block_facts x0 st L BL LS INV c off n0 Hk) as (m & bm & i & ai & a & ar & ka & BF).
unfold realloc_body, crealloc. rewrite s_slots_strip. rewrite (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF).
destruct (size_overflows n) eqn:SO.
{ rewrite prun_ret. constructor. split; [reflexivity| exact I]. }
erewrite (get_meta_eq _ _ _ _ _ _ _ _ _ _ _ BF). cbv beta.
change (get_meta_rec (strip st) m) with (MR st m). change (get_meta_rec st m) with (MR st m).
unfold slot_start. rewrite (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF). cbv beta iota.
erewrite (get_nominal_size_eq _ _ _ _ _ _ _ _ _ _ _ BF). cbv beta.

pose proof (bf_c _ _ _ _ _ _ _ _ _ _ _ BF) as Ec. pose proof (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF) as Hmem.
pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF) as FIT. pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as OFF.
pose proof (bf_n _ _ _ _ _ _ _ _ _ _ _ BF) as N0. pose proof (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) as [ST1 ST2].
assert (Ec2 : snd c = snd bm + UNIT + get_stride (MR st m) * i).
{ rewrite Ec. unfold sstart, gbase. rewrite Hmem. reflexivity. }
assert (Ec1 : fst c = fst bm) by (rewrite Ec; reflexivity).
set (stride := get_stride (MR st m)) in *.
replace (snd (aadd (aadd bm (UNIT + stride * i)) (stride - IB)) - snd (aadd c (UNIT * off)))
with (stride - IB - UNIT * off) by (cbn [snd aadd]; lia).
replace (snd (aadd c (UNIT * off)) - snd (aadd bm (UNIT + stride * i))) with (UNIT * off) by (cbn [snd aadd]; lia).

pose proof (bf_shadow _ _ _ _ _ _ _ _ _ _ _ BF) as SH. unfold blk_shadow_ok in SH. cbn [bslot boff bsize fst snd] in SH.
destruct SH as (_ & K3 & _).
set (b3 := i + 32 * Z.min (snd c + get_stride (MR st m) - IB - (snd c + UNIT * off) - n0) 5) in K3.
assert (RD3 : forall (R : Type) st' (k : Z -> M R),
cell_read (get_shadow st' (fst c)) (snd c + UNIT * off + (-3)) = cell_read (get_shadow st (fst c)) (snd c + UNIT * off + (-3)) ->
rd8 st' (aadd (aadd c (UNIT * off)) (-3)) k = k b3).
{ intros R st' k E. apply rd8_known. cbn [fst snd aadd]. rewrite E. eapply known_at; [exact K3| cbn; lia| cbn; reflexivity]. }

destruct ((n <=? stride - IB - UNIT * off) && (n <? MMAP_THRESHOLD) && (m_sizeclass (MR st m) <=? size_to_class n + 1)) eqn:INPL.
{ unfold rr_set_size. rewrite (RD3 _ st) by reflexivity. rewrite prun_ret. constructor.
split; [cbn; rewrite strip_havoc, strip_set_size; reflexivity| reflexivity]. }

assert (MOVE : forall o1,
strelU (RRREL (aadd c (UNIT * off)))
(PRUN o1 (sbind (malloc st n) (fun x : mstate * optr => let (st1, r) := x in
match r with
| Some q => sbind (free st1 (Some (aadd c (UNIT * off)))) (fun st2 => ret (st2, Some q))
| None => ret (st1, None)
end)))
(sbind (cmalloc (strip st) n) (fun x : mstate * option cptr => let (cs1, r) := x in
match r with
| Some c' => sbind (cfree cs1 (Some c)) (fun cs2 => ret (cs2, Some (RRNew (c', fresh_off cs1 c' n))))
| None => ret (cs1, None)
end))).
{ intros o1. eapply strelU_steq_l. { unfold prun. apply eruns_sbind. }
eapply strelU_sbind_fk. { apply strel_strelU. apply (malloc_control pans pupd Hpans). }
intros ans rest [o2 [st1 r1]] [cs1 r2] F1 F2 [HS Hr]. cbn [fst snd] in HS, Hr. subst cs1.
destruct r1 as [q|], r2 as [c'|]; try (destruct Hr; fail).
-
pose proof (followk_follow _ _ F1) as FF.
destruct (malloc_sim pans pupd Hpans st L BL LS n o1 ans _ _ _ INV Hn FF) as (rc & Hf2 & CP & LIVE1 & GP1 & RES).
pose proof (followk_follow _ _ F2) as FF2. cbv zeta in Hf2. rewrite Hf2 in FF2. inversion FF2. subst rc. clear FF2.
destruct RES as (off1 & LS1 & Epf & Ho1 & INV1 & NI1).
pose proof (INVL_hdr_ok pans pupd st1 _ _ LS1 c off n0 INV1 ltac:(right; exact Hk)) as HOK.
eapply strelU_steq_l. { unfold prun. apply eruns_sbind. }
apply strel_strelU. eapply strel_sbind. { apply (free_control pans pupd st1 _ c o2 HOK). }
intros [o3 st2] cs2 HF. unfold prun, ret. cbn [eruns psel]. constructor.
unfold FREL in HF. cbn [snd] in HF. split; [exact HF| exact Hr].
- cbn [fst snd]. unfold prun, ret. cbn [eruns psel]. constructor. split; [reflexivity| exact I]. }
destruct ((48 <=? m_sizeclass (MR st m)) && (MMAP_THRESHOLD <=? n)) eqn:BIG; [| apply MOVE].

apply strelU_guard. intros E63. apply Z.eqb_eq in E63.
pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
pose proof (ig_ok _ _ _ IG _ _ _ (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF)) as GO.
assert (LI0 : m_last_idx (MR st m) = 0 /\ m_maplen (MR st m) <> 0).
{ destruct (g_sc _ _ _ _ _ _ GO) as [[Hsc _]|(_ & A1 & A2 & _)]; [unfold MR in *; lia| auto]. }
destruct LI0 as [LI0 ML].
assert (I0 : i = 0) by (pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF); lia). subst i.
destruct (bf_top _ _ _ _ _ _ _ _ _ _ _ BF ML) as [B0 _].
set (needed := rr_needed n (UNIT * off)) in *.
assert (ND : n + UNIT * off + UNIT + IB <= needed) by (unfold needed, rr_needed; apply round_up_ge).

assert (FIN : forall o1 nb,
strelU (RRREL (aadd c (UNIT * off)))
(PRUN o1 (rr_set_size (wr8 (aadd bm (UNIT + (needed - UNIT) - IB)) 0 (remap_region (fst bm) nb needed m st))
(aadd c (UNIT * off)) (aadd bm (UNIT + (needed - UNIT) - IB)) n
(fun st3 => ret (havoc (aadd c (UNIT * off)) n st3, Some (aadd c (UNIT * off))))))
(ret (strip (remap_region (fst bm) nb needed m (strip st)), Some RRSame))).
{ intros o1 nb. unfold rr_set_size. rewrite RD3.
2:{ rewrite (cell_read_wr8_other _ _ _ (fst c, snd c + UNIT * off + (-3))).
2:{ intros E. apply (f_equal snd) in E. cbn [snd aadd] in E. unfold UNIT, IB in *. lia. }
apply (@cell_read_remap_region (fst bm) nb needed m st (fst c, snd c + UNIT * off + (-3))). cbn [fst snd]. intros _.
destruct (remap_bound_facts needed INV BF ML LI0) as (-> & BND & _). pose proof (bf_n _ _ _ _ _ _ _ _ _ _ _ BF). unfold UNIT, IB in *. lia. }
rewrite prun_ret. constructor. split; [| reflexivity].
cbn [fst snd]. rewrite strip_havoc, strip_set_size, strip_wr8. apply strip_remap_region. }
destruct (m_maplen (MR st m) * 4096 =? needed) eqn:EQL.
{ unfold rr_set_size. rewrite (RD3 _ st) by reflexivity. rewrite prun_ret. constructor.
split; [cbn; rewrite strip_havoc, strip_set_size; reflexivity| reflexivity]. }
destruct (PTRDIFF_MAX <=? needed) eqn:PDM; [apply MOVE|].
rewrite conc_strip, live_ranges_strip. rewrite prun_vis_keep by exact I. apply strelU_vis. intros r.
destruct (negb (mremap_answer_ok (live_ranges st) (conc st bm) (m_maplen (MR st m) * 4096) needed r)); [apply strelU_bad|].
destruct (is_err r); [apply MOVE| apply FIN].
Qed.

#[using="Hpans"] Theorem realloc_control st L BL LS c off n0 n o :
INVL x0 st L BL LS -> In ((c, off), n0) BL -> 0 <= n ->
strelU (RRREL (aadd c (UNIT * off))) (PRUN o (realloc st (Some (aadd c (UNIT * off))) n)) (crealloc (strip st) c off n).
Proof.
intros INV Hk Hn. unfold realloc. rewrite <- (strip_set_tick (N.succ (s_tick st)) st).
apply (@realloc_body_control (set_tick (N.succ (s_tick st)) st) L BL LS c off n0 n o); [apply INVL_set_tick; [cbn; lia| exact INV]| exact Hk| exact Hn].
Qed.

#[using="Type"] Lemma strelU_steq_r {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : M R1) (t2 t2' : M R2) :
steq t2' t2 -> strelU RR t1 t2' -> strelU RR t1 t2.
Proof.
intros H; revert t1; induction H; intros t1 Ht; inversion Ht; subst;
first [constructor; assumption | apply strelU_undef | apply strelU_vis; intros a; eauto].
Qed.

#[using="Hpans"] Theorem calloc_control st L BL LS m n o :
INVL x0 st L BL LS -> 0 <= m -> 0 <= n ->
strelU (@MREL O) (PRUN o (calloc st m n)) (ccalloc (strip st) m n).
Proof.
intros INV Hm Hn. unfold calloc, ccalloc.
destruct (calloc_overflows m n). { rewrite prun_ret. constructor. split; [reflexivity| exact I]. }
eapply strelU_steq_l. { unfold prun. apply eruns_sbind. }
eapply strelU_steq_r. { apply sbind_ret_r. }
eapply strelU_sbind_fk. { apply strel_strelU. apply (malloc_control pans pupd Hpans). }
intros ans rest [o2 [st1 r1]] [cs1 r2] F1 F2 [HS Hr]. cbn [fst snd] in HS, Hr. subst cs1.
destruct r1 as [q|], r2 as [c'|]; try (destruct Hr; fail).
- pose proof (followk_follow _ _ F1) as FF.
destruct (malloc_sim pans pupd Hpans st L BL LS (m * n) o ans _ _ _ INV ltac:(lia) FF) as (rc & Hf2 & CP & LIVE1 & GP1 & RES).
pose proof (followk_follow _ _ F2) as FF2. cbv zeta in Hf2. rewrite Hf2 in FF2. inversion FF2. subst rc. clear FF2.
destruct RES as (off1 & LS1 & Epf & Ho1 & INV1 & NI1).
destruct (block_facts x0 st1 _ _ LS1 INV1 c' off1 (m * n) ltac:(left; reflexivity)) as (g & bm & i & ai & a & ar & ka & BF).
unfold malloc_allzerop. subst q. cbn [fst snd]. erewrite (get_meta_eq _ _ _ _ _ _ _ _ _ _ _ BF).
unfold prun, ret. cbn [eruns psel]. constructor. split; [reflexivity| exact Hr].
- cbn [fst snd]. unfold prun, ret. cbn [eruns psel]. constructor. split; [reflexivity| exact I].
Qed.

Section Leaves.
Local Open Scope stree_scope.
Variables (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (c : cptr) (off n0 n : Z).
Variables (m bm : aptr) (i ai : Z) (a : aptr) (ar : area) (ka : Z).
Hypothesis INV : INVL x0 st L BL LS.
Hypothesis Hk : In ((c, off), n0) BL.
Hypothesis Hn : 0 <= n.
Hypothesis BF : blk_facts st c off n0 m bm i ai a ar ka.
Hypothesis SO : size_overflows n = false.

Definition rl_stride : Z := get_stride (MR st m).
Definition rl_p : aptr := aadd c (UNIT * off).
Definition rl_e : aptr := aadd (aadd bm (UNIT + rl_stride * i)) (rl_stride - IB).
Definition rl_b3 : Z := i + 32 * Z.min (rl_stride - IB - UNIT * off - n0) 5.
Definition rl_inplace : bool :=
(n <=? rl_stride - IB - UNIT * off) && (n <? MMAP_THRESHOLD) && (m_sizeclass (MR st m) <=? size_to_class n + 1).
Definition rl_big : bool := (48 <=? m_sizeclass (MR st m)) && (MMAP_THRESHOLD <=? n).
Definition rl_needed : Z := rr_needed n (UNIT * off).
Definition rl_oldlen : Z := m_maplen (MR st m) * 4096.
Definition rl_e' : aptr := aadd bm (UNIT + (rl_needed - UNIT) - IB).
Definition rl_fin (nb : Z) : mstate :=
havoc rl_p n (set_size rl_p rl_e' n rl_b3 (wr8 rl_e' 0 (remap_region (fst bm) nb rl_needed m st))).

Definition rl_body : M (mstate * optr) :=
if rl_inplace then rr_set_size st rl_p rl_e n (fun st1 => ret (havoc rl_p n st1, Some rl_p))
else if rl_big then
guard 70 (m_sizeclass (MR st m) =? 63) (
let finish (st1 : mstate) :=
let st2 := wr8 rl_e' 0 st1 in
rr_set_size st2 rl_p rl_e' n (fun st3 => ret (havoc rl_p n st3, Some rl_p)) in
if rl_oldlen =? rl_needed then rr_set_size st rl_p rl_e n (fun st1 => ret (havoc rl_p n st1, Some rl_p))
else if PTRDIFF_MAX <=? rl_needed then
('(st1, r) <-- malloc st n ;;
match r with None => ret (st1, None) | Some q => st2 <-- free st1 (Some rl_p) ;; ret (st2, Some q) end)
else
SVis (EMremap (conc st bm) rl_oldlen rl_needed MREMAP_MAYMOVE) (fun r =>
if negb (mremap_answer_ok (live_ranges st) (conc st bm) rl_oldlen rl_needed r) then bad_answer (ret (st, @None aptr))
else if is_err r then
('(st1, r) <-- malloc st n ;;
match r with None => ret (st1, None) | Some q => st2 <-- free st1 (Some rl_p) ;; ret (st2, Some q) end)
else finish (remap_region (fst bm) r rl_needed m st)))
(ret (st, @None aptr))
else
('(st1, r) <-- malloc st n ;;
match r with None => ret (st1, None) | Some q => st2 <-- free st1 (Some rl_p) ;; ret (st2, Some q) end).

#[using="ai a ar ka BF SO"] Lemma realloc_body_unfold : realloc_body st rl_p n = rl_body
/\ (forall (R : Type) st' (k : Z -> M R),
cell_read (get_shadow st' (fst c)) (snd c + UNIT * off + (-3)) = cell_read (get_shadow st (fst c)) (snd c + UNIT * off + (-3)) ->
rd8 st' (aadd rl_p (-3)) k = k rl_b3).
Proof.
unfold rl_body, rl_p, rl_inplace, rl_big, rl_e, rl_e', rl_oldlen, rl_needed, rl_stride, rl_b3.
unfold realloc_body. rewrite SO.
erewrite (get_meta_eq _ _ _ _ _ _ _ _ _ _ _ BF). cbv beta. change (get_meta_rec st m) with (MR st m).
unfold slot_start. rewrite (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF). cbv beta iota.
erewrite (get_nominal_size_eq _ _ _ _ _ _ _ _ _ _ _ BF). cbv beta.
pose proof (bf_c _ _ _ _ _ _ _ _ _ _ _ BF) as Ec. pose proof (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF) as Hmem.
pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF) as FIT. pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as OFF.
pose proof (bf_n _ _ _ _ _ _ _ _ _ _ _ BF) as N0. pose proof (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) as [ST1 ST2].
assert (Ec2 : snd c = snd bm + UNIT + get_stride (MR st m) * i).
{ rewrite Ec. unfold sstart, gbase. rewrite Hmem. reflexivity. }
assert (Ec1 : fst c = fst bm) by (rewrite Ec; reflexivity).
replace (snd (aadd (aadd bm (UNIT + get_stride (MR st m) * i)) (get_stride (MR st m) - IB)) - snd (aadd c (UNIT * off)))
with (get_stride (MR st m) - IB - UNIT * off) by (cbn [snd aadd]; lia).
replace (snd (aadd c (UNIT * off)) - snd (aadd bm (UNIT + get_stride (MR st m) * i))) with (UNIT * off) by (cbn [snd aadd]; lia).
split; [reflexivity|].
pose proof (bf_shadow _ _ _ _ _ _ _ _ _ _ _ BF) as SH. unfold blk_shadow_ok in SH. cbn [bslot boff bsize fst snd] in SH.
destruct SH as (_ & K3 & _).
replace (snd c + get_stride (MR st m) - IB - (snd c + UNIT * off) - n0) with (get_stride (MR st m) - IB - UNIT * off - n0) in K3 by lia.
intros R st' k E. apply rd8_known. cbn [fst snd aadd]. rewrite E. eapply known_at; [exact K3| cbn; lia| cbn; reflexivity].
Qed.

Definition rl_cgen : M (mstate * option rr_where) :=
'(cs1, r) <-- cmalloc (strip st) n ;;
match r with
| None => ret (cs1, @None rr_where)
| Some c' => cs2 <-- cfree cs1 (Some c) ;; ret (cs2, Some (RRNew (c', fresh_off cs1 c' n)))
end.
Definition rl_cbody : M (mstate * option rr_where) :=
if rl_inplace then ret (strip st, Some RRSame)
else if rl_big then
guard 70 (m_sizeclass (MR st m) =? 63) (
if rl_oldlen =? rl_needed then ret (strip st, Some RRSame)
else if PTRDIFF_MAX <=? rl_needed then rl_cgen
else
SVis (EMremap (conc st bm) rl_oldlen rl_needed MREMAP_MAYMOVE) (fun r =>
if negb (mremap_answer_ok (live_ranges st) (conc st bm) rl_oldlen rl_needed r) then bad_answer (ret (strip st, @None rr_where))
else if is_err r then rl_cgen
else ret (strip (remap_region (fst bm) r rl_needed m (strip st)), Some RRSame)))
(ret (strip st, @None rr_where))
else rl_cgen.

#[using="n0 i ai a ar ka BF SO"] Lemma crealloc_unfold : crealloc (strip st) c off n = rl_cbody.
Proof.
unfold crealloc, rl_cbody, rl_cgen. rewrite s_slots_strip, (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF), SO.
change (get_meta_rec (strip st) m) with (MR st m). fold rl_stride. unfold rl_inplace, rl_big.
rewrite (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF). fold rl_needed rl_oldlen. rewrite conc_strip, live_ranges_strip. reflexivity.
Qed.

#[using="ai a ar ka BF SO"] Lemma realloc_hdr_unfold o :
PRUN o (realloc_body st rl_p n) =
PRUN o (if rl_inplace then rr_set_size st rl_p rl_e n (fun st1 => ret (havoc rl_p n st1, Some rl_p))
else if rl_big then
guard 70 (m_sizeclass (MR st m) =? 63) (
let finish (st1 : mstate) :=
let st2 := wr8 rl_e' 0 st1 in
rr_set_size st2 rl_p rl_e' n (fun st3 => ret (havoc rl_p n st3, Some rl_p)) in
if rl_oldlen =? rl_needed then rr_set_size st rl_p rl_e n (fun st1 => ret (havoc rl_p n st1, Some rl_p))
else if PTRDIFF_MAX <=? rl_needed then
('(st1, r) <-- malloc st n ;;
match r with None => ret (st1, None) | Some q => st2 <-- free st1 (Some rl_p) ;; ret (st2, Some q) end)
else
SVis (EMremap (conc st bm) rl_oldlen rl_needed MREMAP_MAYMOVE) (fun r =>
if negb (mremap_answer_ok (live_ranges st) (conc st bm) rl_oldlen rl_needed r) then bad_answer (ret (st, @None aptr))
else if is_err r then
('(st1, r) <-- malloc st n ;;
match r with None => ret (st1, None) | Some q => st2 <-- free st1 (Some rl_p) ;; ret (st2, Some q) end)
else finish (remap_region (fst bm) r rl_needed m st)))
(ret (st, @None aptr))
else
('(st1, r) <-- malloc st n ;;
match r with None => ret (st1, None) | Some q => st2 <-- free st1 (Some rl_p) ;; ret (st2, Some q) end))
/\ (forall (R : Type) st' (k : Z -> M R),
cell_read (get_shadow st' (fst c)) (snd c + UNIT * off + (-3)) = cell_read (get_shadow st (fst c)) (snd c + UNIT * off + (-3)) ->
rd8 st' (aadd rl_p (-3)) k = k rl_b3).
Proof.
unfold rl_p, rl_inplace, rl_big, rl_e, rl_e', rl_oldlen, rl_needed, rl_stride, rl_b3.
unfold realloc_body. rewrite SO.
erewrite (get_meta_eq _ _ _ _ _ _ _ _ _ _ _ BF). cbv beta. change (get_meta_rec st m) with (MR st m).
unfold slot_start. rewrite (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF). cbv beta iota.
erewrite (get_nominal_size_eq _ _ _ _ _ _ _ _ _ _ _ BF). cbv beta.
pose proof (bf_c _ _ _ _ _ _ _ _ _ _ _ BF) as Ec. pose proof (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF) as Hmem.
pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF) as FIT. pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as OFF.
pose proof (bf_n _ _ _ _ _ _ _ _ _ _ _ BF) as N0. pose proof (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) as [ST1 ST2].
assert (Ec2 : snd c = snd bm + UNIT + get_stride (MR st m) * i).
{ rewrite Ec. unfold sstart, gbase. rewrite Hmem. reflexivity. }
assert (Ec1 : fst c = fst bm) by (rewrite Ec; reflexivity).
replace (snd (aadd (aadd bm (UNIT + get_stride (MR st m) * i)) (get_stride (MR st m) - IB)) - snd (aadd c (UNIT * off)))
with (get_stride (MR st m) - IB - UNIT * off) by (cbn [snd aadd]; lia).
replace (snd (aadd c (UNIT * off)) - snd (aadd bm (UNIT + get_stride (MR st m) * i))) with (UNIT * off) by (cbn [snd aadd]; lia).
split; [reflexivity|].
pose proof (bf_shadow _ _ _ _ _ _ _ _ _ _ _ BF) as SH. unfold blk_shadow_ok in SH. cbn [bslot boff bsize fst snd] in SH.
destruct SH as (_ & K3 & _).
replace (snd c + get_stride (MR st m) - IB - (snd c + UNIT * off) - n0) with (get_stride (MR st m) - IB - UNIT * off - n0) in K3 by lia.
intros R st' k E. apply rd8_known. cbn [fst snd aadd]. rewrite E. eapply known_at; [exact K3| cbn; lia| cbn; reflexivity].
Qed.

#[using="ai a ar ka BF SO"] Theorem realloc_leaf_inplace o :
rl_inplace = true ->
PRUN o (realloc_body st rl_p n) = SRet (o, (havoc rl_p n (set_size rl_p rl_e n rl_b3 st), Some rl_p))
/\ crealloc (strip st) c off n = SRet (strip st, Some RRSame).
Proof.
intros INPL. destruct (realloc_hdr_unfold o) as [-> RD3]. rewrite INPL.
split.
- unfold rr_set_size. rewrite (RD3 _ st) by reflexivity. apply prun_ret.
- unfold crealloc. rewrite s_slots_strip, (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF), SO.
change (get_meta_rec (strip st) m) with (MR st m). fold rl_stride. unfold rl_inplace in INPL. rewrite INPL. reflexivity.
Qed.

#[using="RC__ L BL LS ai a ar ka INV BF"] Lemma rl_big_facts : rl_inplace = false -> rl_big = true -> m_sizeclass (MR st m) = 63 ->
i = 0 /\ m_last_idx (MR st m) = 0 /\ m_maplen (MR st m) <> 0 /\ snd bm = 0 /\ c = aadd bm UNIT
/\ 0 <= off /\ 0 <= n0 /\ UNIT * off + n0 <= rl_stride - IB /\ n + UNIT * off + UNIT + IB <= rl_needed.
Proof.
intros _ _ E63. pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
pose proof (ig_ok _ _ _ IG _ _ _ (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF)) as GO.
assert (LI0 : m_last_idx (MR st m) = 0 /\ m_maplen (MR st m) <> 0).
{ destruct (g_sc _ _ _ _ _ _ GO) as [[Hsc _]|(_ & A1 & A2 & _)]; [unfold MR in *; lia| auto]. }
destruct LI0 as [LI0 ML].
assert (I0 : i = 0) by (pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF); lia).
destruct (bf_top _ _ _ _ _ _ _ _ _ _ _ BF ML) as [B0 _].
pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF). pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF). pose proof (bf_n _ _ _ _ _ _ _ _ _ _ _ BF).
repeat split; auto; try lia.
- rewrite (bf_c _ _ _ _ _ _ _ _ _ _ _ BF). unfold sstart, gbase. rewrite (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF), I0.
unfold aadd. cbn [fst snd default id]. f_equal. lia.
- unfold rl_needed, rr_needed. apply round_up_ge.
Qed.

#[using="RC__ L BL LS ai a ar ka INV Hn BF SO"] Lemma rl_fin_rd3 nb (R : Type) (k : Z -> M R) :
rl_inplace = false -> rl_big = true -> m_sizeclass (MR st m) = 63 ->
rd8 (wr8 rl_e' 0 (remap_region (fst bm) nb rl_needed m st)) (aadd rl_p (-3)) k = k rl_b3.
Proof.
intros H1 H2 H3. destruct (rl_big_facts H1 H2 H3) as (I0 & LI0 & ML & B0 & Ecb & OFF & N0 & FIT & ND).
destruct realloc_body_unfold as [_ RD3]. apply RD3.
assert (Ec1 : fst c = fst bm) by (rewrite Ecb; reflexivity). assert (Ec2 : snd c = snd bm + UNIT) by (rewrite Ecb; reflexivity).
rewrite (cell_read_wr8_other _ _ _ (fst c, snd c + UNIT * off + (-3))).
2:{ unfold rl_e'. intros E. apply (f_equal snd) in E. cbn [snd aadd] in E. unfold UNIT, IB in *. lia. }
apply (@cell_read_remap_region (fst bm) nb rl_needed m st (fst c, snd c + UNIT * off + (-3))). cbn [fst snd]. intros _.
destruct (remap_bound_facts rl_needed INV BF ML LI0) as (-> & BND & _). unfold UNIT, IB in *. lia.
Qed.

#[using="ai a ar ka BF SO"] Theorem realloc_leaf_remap0 o :
rl_inplace = false -> rl_big = true -> m_sizeclass (MR st m) = 63 -> rl_oldlen = rl_needed ->
PRUN o (realloc_body st rl_p n) = SRet (o, (havoc rl_p n (set_size rl_p rl_e n rl_b3 st), Some rl_p))
/\ crealloc (strip st) c off n = SRet (strip st, Some RRSame).
Proof.
intros H1 H2 H3 EQ. destruct (realloc_hdr_unfold o) as [-> RD3]. rewrite H1, H2.
rewrite (guard_true 70) by (apply Z.eqb_eq; exact H3). cbv zeta. rewrite (proj2 (Z.eqb_eq _ _) EQ).
split.
- unfold rr_set_size. rewrite (RD3 _ st) by reflexivity. apply prun_ret.
- unfold crealloc. rewrite s_slots_strip, (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF), SO.
change (get_meta_rec (strip st) m) with (MR st m). fold rl_stride. unfold rl_inplace, rl_big in H1, H2. rewrite H1, H2.
rewrite (guard_true 70) by (apply Z.eqb_eq; exact H3). rewrite (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF).
fold rl_needed rl_oldlen. rewrite (proj2 (Z.eqb_eq _ _) EQ). reflexivity.
Qed.

#[using="L BL LS ai a ar ka INV Hn BF SO"] Theorem realloc_leaf_remap o z :
rl_inplace = false -> rl_big = true -> m_sizeclass (MR st m) = 63 -> rl_oldlen <> rl_needed -> rl_needed < PTRDIFF_MAX ->
mremap_answer_ok (live_ranges st) (conc st bm) rl_oldlen rl_needed z = true -> is_err z = false ->
follow (PRUN o (realloc_body st rl_p n)) [z]
= Some (pupd o (EMremap (conc st bm) rl_oldlen rl_needed MREMAP_MAYMOVE) z, (rl_fin z, Some rl_p))
/\ follow (crealloc (strip st) c off n) [z] = Some (strip (remap_region (fst bm) z rl_needed m (strip st)), Some RRSame).
Proof.
intros H1 H2 H3 NE PD OK NER. destruct (realloc_hdr_unfold o) as [-> _]. rewrite H1, H2.
rewrite (guard_true 70) by (apply Z.eqb_eq; exact H3). cbv zeta. rewrite (proj2 (Z.eqb_neq _ _) NE). rewrite (proj2 (Z.leb_gt _ _) PD).
split.
- rewrite prun_vis_keep by exact I. cbn [follow]. rewrite OK, NER. cbn [negb].
unfold rr_set_size. rewrite rl_fin_rd3 by assumption. rewrite prun_ret. reflexivity.
- unfold crealloc. rewrite s_slots_strip, (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF), SO.
change (get_meta_rec (strip st) m) with (MR st m). fold rl_stride. unfold rl_inplace, rl_big in H1, H2. rewrite H1, H2.
rewrite (guard_true 70) by (apply Z.eqb_eq; exact H3). rewrite (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF).
fold rl_needed rl_oldlen. rewrite (proj2 (Z.eqb_neq _ _) NE), (proj2 (Z.leb_gt _ _) PD). cbn [follow]. rewrite conc_strip, live_ranges_strip, OK, NER. reflexivity.
Qed.

#[using="n0 bm i ai a ar ka BF SO"] Theorem realloc_leaf_huge o :
rl_inplace = false -> rl_big = true -> m_sizeclass (MR st m) = 63 -> rl_oldlen <> rl_needed -> PTRDIFF_MAX <= rl_needed ->
PRUN o (realloc_body st rl_p n)
= PRUN o ('(st1, r) <-- malloc st n ;;
match r with None => ret (st1, None) | Some q => st2 <-- free st1 (Some rl_p) ;; ret (st2, Some q) end)
/\ crealloc (strip st) c off n = rl_cgen.
Proof.
intros H1 H2 H3 NE PD. destruct (realloc_hdr_unfold o) as [-> _]. rewrite H1, H2.
rewrite (guard_true 70) by (apply Z.eqb_eq; exact H3). cbv zeta. rewrite (proj2 (Z.eqb_neq _ _) NE). rewrite (proj2 (Z.leb_le _ _) PD).
split; [reflexivity|].
unfold crealloc. rewrite s_slots_strip, (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF), SO.
change (get_meta_rec (strip st) m) with (MR st m). fold rl_stride. unfold rl_inplace, rl_big in H1, H2. rewrite H1, H2.
rewrite (guard_true 70) by (apply Z.eqb_eq; exact H3). rewrite (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF).
fold rl_needed rl_oldlen. rewrite (proj2 (Z.eqb_neq _ _) NE), (proj2 (Z.leb_le _ _) PD). reflexivity.
Qed.
End Leaves.

#[using="Hpans"] Theorem malloc_core_allzero_ctrl st L BL LS n o ans o' st1 g idx :
INVL x0 st L BL LS -> 0 <= n ->
follow (PRUN o (malloc_core full_lay (set_tick (N.succ (s_tick st)) st) n)) ans = Some (o', (st1, Some (g, idx))) ->
is_allzero_ctrl (MR st1 g) = true ->
exists bg, m_mem (MR st1 g) = Some bg /\
forall k, 0 <= k < get_stride (MR st1 g) - IB ->
cell_read (get_shadow st1 (fst bg)) (sstart (MR st1 g) idx + k) = Known 0.
Proof.
intros INV Hn Hf AZ. apply (malloc_core_allzero pans pupd Hpans st L BL LS n o ans o' st1 g idx INV Hn Hf).
unfold is_allzero_ctrl in AZ. apply Bool.orb_prop in AZ as [AZ|AZ]; [left; apply Z.leb_le; exact AZ| right; apply Z.ltb_lt; exact AZ].
Qed.

End RC.

#[using="Type"] Lemma inv_R_ctrl X st st1 L : strip st1 = strip st -> inv_R X st1 L -> inv_R X st L.
Proof.
intros E H.
assert (Er : s_regions st1 = s_regions st) by (apply (f_equal s_regions) in E; exact E).
assert (Ec : s_ctx st1 = s_ctx st) by (apply (f_equal s_ctx) in E; exact E).
assert (En : s_next_rid st1 = s_next_rid st) by (apply (f_equal s_next_rid) in E; exact E).
assert (Ev : s_reserved st1 = s_reserved st) by (apply (f_equal s_reserved) in E; exact E).
assert (Eg : s_groups st1 = s_groups st) by (apply (f_equal s_groups) in E; exact E).
assert (Ef : forall rid r, frontier st1 rid r = frontier st rid r) by (intros; unfold frontier; rewrite Ec; reflexivity).
destruct H as [I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14].
constructor; rewrite <- ?Er, <- ?Ec, <- ?En, <- ?Ev, <- ?Eg; auto.
- erewrite map_ext; [exact I6|]. intros [rid r]. cbn. rewrite Ef. reflexivity.
- intros rid r H1 H2. rewrite <- Ef. apply I7; assumption.
- intros rid r H1 H2. rewrite <- Ef. apply I8; assumption.
Qed.

#[using="Type"] Theorem INVL_transplant X st st1 L L1 BL BL1 LS LS1 :
INVL X st L BL LS -> INVL X st1 L1 BL1 LS1 -> strip st1 = strip st -> INVL X st L1 BL LS.
Proof.
intros (IR & REST) (IR1 & _) E. split; [exact (inv_R_ctrl E IR1)| exact REST].
Qed.

#[using="Type"] Theorem ccalloc_ctree st L BL LS m n :
INVL x0 st L BL LS -> (forall c, In c (ld_live L) -> In c (map bslot BL)) -> 0 <= m -> 0 <= n ->
ctree_ok L (ccalloc (strip st) m n) (fun L' r => match snd r with Some c => ~ In c (ld_live L') | None => True end).
Proof.
intros INV LIVE Hm Hn. unfold ccalloc. destruct (calloc_overflows m n); [exact I|].
apply (cmalloc_ctree st L BL LS); [exact INV| exact LIVE| lia].
Qed.

#[using="Type"] Theorem ccalloc_leaf_INVL st L BL LS m n L' cs' r :
INVL x0 st L BL LS -> 0 <= m -> 0 <= n -> cpath L (ccalloc (strip st) m n) L' (cs', r) ->
ld_live L' = ld_live L /\
exists st' LS', strip st' = cs' /\
match r with
| None => INVL x0 st' L' BL LS'
| Some c => exists off, 0 <= off <= 255 /\ INVL x0 st' L' (((c, off), m * n) :: BL) LS' /\ ~ In c (map bslot BL)
end.
Proof.
intros INV Hm Hn CP. unfold ccalloc in CP. destruct (calloc_overflows m n).
- inversion CP; subst. split; [reflexivity|]. exists st, LS. split; [reflexivity| exact INV].
- apply (cmalloc_leaf_INVL st L BL LS); [exact INV| lia| exact CP].
Qed.

#[using="Type"] Lemma live_slot_clear st L BL LS c off n0 m bm i ai a ar ka :
INVL x0 st L BL LS -> In ((c, off), n0) BL -> blk_facts st c off n0 m bm i ai a ar ka ->
let lo := sstart (MR st m) i - IB in
let hi := sstart (MR st m) i + get_stride (MR st m) - IB in
(forall b' gh, s_groups st !! b' = Some gh -> fst b' = fst bm -> snd b' + 12 <= lo \/ hi <= snd b')
/\ (forall k', In k' BL -> bslot k' <> c -> fst (bslot k') = fst bm ->
snd (bslot k') + UNIT * boff k' + bsize k' <= lo \/ hi <= snd (bslot k') + UNIT * boff k' - IB).
Proof.
intros INV Hk BF. pose proof INV as (IR & IA & IM & IL & IG & IS & ISH). cbn zeta.
pose proof (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF) as Hb. assert (Hm : hosts st bm m) by (exists ai; exact Hb).
pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi. pose proof (bf_c _ _ _ _ _ _ _ _ _ _ _ BF) as Ec.
pose proof (bf_notH _ _ _ _ _ _ _ _ _ _ _ BF) as NH. rewrite Ec in NH.
pose proof (sstart_succ st m i) as SS.
split.
- intros b' gh Hb' Hf. destruct (im_hdr _ _ _ IM _ _ Hb') as (m' & Eg & _ & _).
assert (Hm' : hosts st b' m') by (destruct gh as [gm gai]; cbn in Eg; subst gm; exists gai; exact Hb').
destruct (sep_ghdr _ _ _ _ IM IG IS m bm i Hm Hi NH m' b' Hm' Hf) as [A|A]; unfold IB in *; lia.
- intros [[c2 off2] n2] Hk' NEk Hf. cbn [bslot boff bsize fst snd] in *.
destruct (block_facts x0 st L BL LS INV c2 off2 n2 Hk') as (m2 & b2 & i2 & ai2 & a2 & ar2 & ka2 & BF2).
pose proof (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF2) as Hb2. assert (Hm2 : hosts st b2 m2) by (exists ai2; exact Hb2).
pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF2) as Hi2. pose proof (bf_c _ _ _ _ _ _ _ _ _ _ _ BF2) as Ek.
pose proof (bf_notH _ _ _ _ _ _ _ _ _ _ _ BF2) as NH2. rewrite Ek in NH2.
pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF2) as Ho2. pose proof (bf_n _ _ _ _ _ _ _ _ _ _ _ BF2) as Hn2. pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF2) as Fit2.
assert (Hf2 : fst b2 = fst bm) by (rewrite Ek in Hf; exact Hf).
assert (NE : m2 <> m \/ i2 <> i).
{ destruct (aptr_eq_dec m2 m) as [->|]; [right| now left]. intros ->. apply NEk. rewrite Ek, Ec.
pose proof (hosts_inj _ _ _ IM _ _ _ Hm2 Hm). subst b2. reflexivity. }
pose proof (sstart_succ st m2 i2) as SS2.
destruct (sep_ext _ _ _ _ IM IG IS m bm i Hm Hi NH m2 b2 i2 Hm2 Hf2 Hi2 NE NH2) as [A|A]; rewrite Ek; cbn [snd]; unfold UNIT, IB in *; lia.
Qed.

End RC__1.
