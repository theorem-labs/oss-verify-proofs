(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Bool Lia Permutation.
From stdpp Require gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi QUZl Q7S0 Qfya QPiB Qatc QSfG QdBa QpFQ Ql2m QYTG QaiD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Qfya QPiB.Mq0 Qatc QSfG.Mq2 Q7S0 QdBa.Mq1 QdBa.Mq0 QpFQ Ql2m.Mq1 QPiB QdBa.Mq2 Ql2m.Mq2 QYTG.Mq1 QaiD.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma add_bit_lor f i : 0 <= f -> 0 <= i -> Z.testbit f i = false -> f + 2 ^ i = Z.lor f (2 ^ i).
Proof.
intros Hf Hi Hb. rewrite <- Z.lxor_lor.
- apply Z.add_nocarry_lxor. apply Z.bits_inj'. intros j Hj.
rewrite Z.land_spec, Z.bits_0. destruct (Z.eq_dec j i) as [->|NE].
+ rewrite Hb. reflexivity.
+ rewrite Z.pow2_bits_false by lia. apply Bool.andb_false_r.
- apply Z.bits_inj'. intros j Hj. rewrite Z.land_spec, Z.bits_0. destruct (Z.eq_dec j i) as [->|NE].
+ rewrite Hb. reflexivity.
+ rewrite Z.pow2_bits_false by lia. apply Bool.andb_false_r.
Qed.

#[using="Type"] Lemma testbit_add_bit f i j : 0 <= f -> 0 <= i -> 0 <= j -> Z.testbit f i = false ->
Z.testbit (f + 2 ^ i) j = Z.testbit f j || (i =? j).
Proof.
intros Hf Hi Hj Hb. rewrite (add_bit_lor f i Hf Hi Hb). rewrite Z.lor_spec. f_equal.
destruct (Z.eqb_spec i j) as [<-|NE]; [apply Z.pow2_bits_true; lia| apply Z.pow2_bits_false; lia].
Qed.

#[using="Type"] Lemma bit_eq i : bit i = 2 ^ i. Proof. reflexivity. Qed.

Section WR.
Variables (st : mstate) (q : aptr) (v : Z).
Let st' := wr8 q v st.

#[using="Type"] Lemma wr8_shadow_lookup rid :
s_shadow st' !! rid = if (rid =? fst q)%N then Some (mkShadow (<[snd q := (Z.land v 255, s_tick st)]> (r_cells (get_shadow st (fst q)))) (r_hav (get_shadow st (fst q))) (r_havp (get_shadow st (fst q)))) else s_shadow st !! rid.
Proof.
unfold st', wr8, upd_shadow. cbn. destruct (N.eqb_spec rid (fst q)) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity.
Qed.

#[using="Type"] Lemma wr8_dom (P : N -> Prop) :
(forall rid sh, s_shadow st !! rid = Some sh -> P rid) -> P (fst q) ->
forall rid sh, s_shadow st' !! rid = Some sh -> P rid.
Proof.
intros H Hq rid sh. rewrite wr8_shadow_lookup. destruct (N.eqb_spec rid (fst q)) as [->|NE]; [auto|]. apply H.
Qed.

#[using="Type"] Lemma wr8_tks (T : N) :
(s_tick st <= T)%N ->
(forall rid sh, s_shadow st !! rid = Some sh ->
(forall o w t, r_cells sh !! o = Some (w, t) -> 0 <= w < 256 /\ (t <= T)%N)
/\ (forall u hl ch, r_hav sh !! u = Some hl -> In ch hl -> (snd ch <= T)%N)
/\ (forall pg t, r_havp sh !! pg = Some t -> (t <= T)%N)) ->
forall rid sh, s_shadow st' !! rid = Some sh ->
(forall o w t, r_cells sh !! o = Some (w, t) -> 0 <= w < 256 /\ (t <= T)%N)
/\ (forall u hl ch, r_hav sh !! u = Some hl -> In ch hl -> (snd ch <= T)%N)
/\ (forall pg t, r_havp sh !! pg = Some t -> (t <= T)%N).
Proof.
intros HT H rid sh. rewrite wr8_shadow_lookup. destruct (N.eqb_spec rid (fst q)) as [->|NE]; [| apply H].
intros E. inversion E. subst sh. cbn.
assert (G : forall o w t, r_cells (get_shadow st (fst q)) !! o = Some (w, t) -> 0 <= w < 256 /\ (t <= T)%N).
{ intros o w t Ho. unfold get_shadow in Ho. destruct (s_shadow st !! fst q) as [sh0|] eqn:E0; cbn in Ho.
- exact (proj1 (H _ _ E0) o w t Ho).
- rewrite lookup_empty in Ho. discriminate. }
assert (G2 : forall u hl ch, r_hav (get_shadow st (fst q)) !! u = Some hl -> In ch hl -> (snd ch <= T)%N).
{ intros u hl ch Hu Hin. unfold get_shadow in Hu. destruct (s_shadow st !! fst q) as [sh0|] eqn:E0; cbn in Hu.
- exact (proj1 (proj2 (H _ _ E0)) u hl ch Hu Hin).
- rewrite lookup_empty in Hu. discriminate. }
assert (G3 : forall pg t, r_havp (get_shadow st (fst q)) !! pg = Some t -> (t <= T)%N).
{ intros pg t Hp. unfold get_shadow in Hp. destruct (s_shadow st !! fst q) as [sh0|] eqn:E0; cbn in Hp.
- exact (proj2 (proj2 (H _ _ E0)) pg t Hp).
- rewrite lookup_empty in Hp. discriminate. }
split; [| split; [exact G2| exact G3]].
intros o w t. destruct (Z.eq_dec o (snd q)) as [->|NEo].
- rewrite lookup_insert_eq. intros X. inversion X. subst. split; [| exact HT].
change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
- rewrite lookup_insert_ne by congruence. apply G.
Qed.
End WR.

Definition xpend (X : extras) (p : option aptr) : extras := mkX (x_idle X) (x_zomb X) p (x_orph X) (x_fresh X).
Definition xorph (X : extras) (o : option N) : extras := mkX (x_idle X) (x_zomb X) (x_pend X) o (x_fresh X).

Definition NTF_SPEC : Prop :=
forall (T : Type) (f : nat) X st L BL LS g bg i (k : mstate -> mapinfo -> M T) (bail : M T),
INVL X st L BL LS -> hosts st bg g -> 0 <= i <= m_last_idx (MR st g) ->
x_pend X = Some (fst bg, sstart (MR st g) i) -> x_fresh X = None -> x_orph X = None ->
(1 <= f)%nat -> 49 - m_sizeclass (MR st g) <= Z.of_nat f ->
exists st' mi LS',
nontrivial_free dec_hdr f st g i k bail = k st' mi /\
match mi with
| None => INVL (xpend X None) st' L BL LS'
| Some (base, len) =>
exists r, snd base = 0 /\ s_regions st' !! (fst base) = Some r /\ r_kind r = RKGroup
/\ len = round_up_pg (r_len r) /\ 0 < len
/\ INVL (xorph (xpend X None) (Some (fst base))) st' L BL LS'
end.

#[using="Type"] Lemma g_remove_perm lG : forall rest b l,
Permutation lG ((b, l) :: rest) -> (forall y, In y rest -> fst y <> b) -> Permutation (g_remove b lG) rest.
Proof.
induction lG as [|y lG IH]; intros rest b l P Hr.
- apply Permutation_nil_cons in P. destruct P.
- cbn. assert (Hy : In y ((b, l) :: rest)) by (eapply Permutation_in; [exact P| left; reflexivity]).
destruct (Z.eqb_spec (fst y) b) as [E|NE].
+ destruct Hy as [<-|Hy]; [| exfalso; exact (Hr _ Hy E)].
apply Permutation_cons_inv with (a := (b, l)). exact P.
+ destruct Hy as [<-|Hy]; [cbn in NE; congruence|].
destruct (in_split _ _ Hy) as (r1 & r2 & ->).
assert (P' : Permutation lG ((b, l) :: r1 ++ r2)).
{ apply Permutation_cons_inv with (a := y). eapply Permutation_trans; [exact P|].
change ((b, l) :: r1 ++ y :: r2) with (((b, l) :: r1) ++ y :: r2). change (y :: (b, l) :: r1 ++ r2) with (y :: ((b, l) :: r1) ++ r2).
apply Permutation_sym. apply Permutation_middle. }
eapply Permutation_trans; [| apply Permutation_middle]. apply perm_skip. apply (IH _ _ l P').
intros z Hz. apply Hr. apply in_app_iff in Hz. apply in_app_iff. cbn. tauto.
Qed.

#[using="Type"] Lemma round_up_ge x : x <= round_up_pg x.
Proof. unfold round_up_pg. pose proof (proj2 (Z.land_nonneg (-x) (PGSZ - 1)) ltac:(right; unfold PGSZ; lia)). lia. Qed.

#[using="Type"] Lemma perm_filter {A} (f : A -> bool) l l' : Permutation l l' -> Permutation (List.filter f l) (List.filter f l').
Proof.
induction 1; cbn.
- constructor.
- destruct (f x); [apply perm_skip|]; assumption.
- destruct (f x), (f y); try apply perm_swap; try apply perm_skip; apply Permutation_refl.
- eapply Permutation_trans; eauto.
Qed.

#[using="Type"] Lemma regions_delete_perm (st : mstate) rid r (F : N * region -> bool) :
s_regions st !! rid = Some r ->
Permutation (List.filter F (map_to_list (s_regions st))) (List.filter F ((rid, r) :: map_to_list (delete rid (s_regions st)))).
Proof. intros H. apply perm_filter. apply Permutation_sym. apply map_to_list_delete. exact H. Qed.

#[using="Type"] Lemma inv_S_X X X' st BL : x_pend X' = x_pend X -> inv_S X st BL -> inv_S X' st BL.
Proof. intros E I. destruct I; constructor; rewrite ?E; assumption. Qed.

Section DROP.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (rid : N) (r : region).
Hypothesis INV : INVL X st L BL LS.
Hypothesis HO : x_orph X = Some rid.
Hypothesis Hr : s_regions st !! rid = Some r.
Let st' := drop_region rid st.
Let L' := Qfya.set_groups (g_remove (r_base r) (ld_groups L)) L.
Let X' := xorph X None.

#[using="Type"] Lemma drop_lookup q : s_regions st' !! q = if (q =? rid)%N then None else s_regions st !! q.
Proof. apply lookup_drop_region. Qed.
#[using="Type"] Lemma drop_keep q rq : s_regions st !! q = Some rq -> q <> rid -> s_regions st' !! q = Some rq.
Proof. intros H NE. rewrite drop_lookup. destruct (N.eqb_spec q rid); [congruence| exact H]. Qed.
#[using="Type"] Lemma drop_some q rq : s_regions st' !! q = Some rq -> s_regions st !! q = Some rq /\ q <> rid.
Proof. rewrite drop_lookup. destruct (N.eqb_spec q rid); [discriminate| auto]. Qed.

#[using="INV HO Hr"] Theorem INVL_drop_orph : INVL X' st' L' BL LS.
Proof.
destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
pose proof (ir_orph _ _ _ IR rid HO) as (r0 & Hr0 & Hk & NOG). rewrite Hr in Hr0. symmetry in Hr0. inversion Hr0. subst r0. clear Hr0.
assert (KEEP : forall q rq, s_regions st !! q = Some rq -> r_kind rq <> RKGroup \/ q <> rid -> s_regions st' !! q = Some rq).
{ intros q rq Hq [K|NE]; apply drop_keep; auto. intros ->. rewrite Hr in Hq. inversion Hq. subst. congruence. }
assert (FR : forall q rq, frontier st' q rq = frontier st q rq) by (intros; reflexivity).
split; [| split; [| split; [| split; [| split; [| split]]]]].
- destruct IR; constructor; cbn -[drop_region g_remove frontier region_live_range round_up_pg Z.mul Z.pow Z.add].
+ intros q rq Hq. apply drop_some in Hq as [Hq _]. exact (ir_ids q rq Hq).
+ intros q rq Hq. apply drop_some in Hq as [Hq _]. exact (ir_shape q rq Hq).
+ intros q1 q2 r1 r2 H1 H2 NE. apply drop_some in H1 as [H1 _]. apply drop_some in H2 as [H2 _]. exact (ir_disj q1 q2 r1 r2 H1 H2 NE).
+ exact ir_resv.
+
apply g_remove_perm with (l := r_len r).
* eapply Permutation_trans; [exact ir_groups|].
eapply Permutation_trans; [apply Permutation_map; apply (regions_delete_perm st rid r _ Hr)|].
cbn. rewrite Hk. cbn. apply perm_skip. unfold st', drop_region. cbn. apply Permutation_refl.
* intros y Hy. apply in_map_iff in Hy as ([q rq] & <- & Hq). apply filter_In in Hq as [Hq Hkq]. cbn in Hkq |- *.
apply elem_of_list_In in Hq || apply list_elem_of_In in Hq. apply elem_of_map_to_list in Hq.
unfold st', drop_region in Hq. cbn in Hq. apply lookup_delete_Some in Hq as [NE Hq].
destruct (r_kind rq) eqn:Ek; try discriminate.
intros E. pose proof (ir_disj q rid rq r Hq Hr ltac:(congruence)) as D. unfold region_live_range in D. rewrite Ek, Hk in D.
pose proof (ir_shape _ _ Hq) as (S1 & _ & S3 & _). pose proof (ir_shape _ _ Hr) as (T1 & _ & T3 & _).
pose proof (round_up_ge (r_len rq)). pose proof (round_up_ge (r_len r)). lia.
+ eapply Permutation_trans; [exact ir_metas|].
eapply Permutation_trans; [apply Permutation_map; apply (regions_delete_perm st rid r _ Hr)|].
cbn. rewrite Hk. cbn. unfold st', drop_region. cbn. apply Permutation_refl.
+ intros q rq Hq K. apply drop_some in Hq as [Hq _]. rewrite FR. exact (ir_metalen q rq Hq K).
+ intros q rq Hq K. apply drop_some in Hq as [Hq _]. rewrite FR. exact (ir_brkfront q rq Hq K).
+ destruct ir_shift as [S1 [S2|(q & rq & Hq & K & E)]]; split; [exact S1| left; exact S2| exact S1|].
right. exists q, rq. split; [apply KEEP; [exact Hq| left; congruence]| auto].
+ intros b l. rewrite ir_brkreg. split; intros (q & rq & Hq & K & E1 & E2); exists q, rq.
* split; [apply KEEP; [exact Hq| left; congruence]| auto].
* apply drop_some in Hq as [Hq _]. auto.
+ intros q1 q2 r1 r2 H1 H2. apply drop_some in H1 as [H1 _]. apply drop_some in H2 as [H2 _]. exact (ir_brk1 q1 q2 r1 r2 H1 H2).
+ revert ir_brk. change (c_brk (s_ctx st')) with (c_brk (s_ctx st)). destruct (c_brk (s_ctx st)) as [| |brid boff]; intros IBK.
* destruct IBK as [B NB]. split; [exact B|]. intros q rq Hq. apply drop_some in Hq as [Hq _]. exact (NB q rq Hq).
* exact IBK.
* destruct IBK as [B (rq & Hq & K & E)]. split; [exact B|]. exists rq. split; [apply KEEP; [exact Hq| left; congruence]| auto].
+ destruct ir_cursor as (C1 & C2 & C3). split; [exact C1|]. split; [exact C2|].
intros q off E. destruct (C3 q off E) as (rq & Hq & K & B). exists rq. split; [apply KEEP; [exact Hq| left; destruct K; congruence]| auto].
+ intros q Hq. cbn in Hq. discriminate.
- destruct IA; constructor; try assumption.
+ intros a ar Ha. destruct (ia_areas a ar Ha) as ((rq & Hq & K & M & P & F) & rest). split; [| exact rest].
exists rq. rewrite FR. split; [apply KEEP; [exact Hq| left; destruct K; congruence]| auto].
+ intros q Hq. destruct (ia_availptr q Hq) as (rq & Hrq & K). exists rq. split; [apply KEEP; [exact Hrq| left; destruct K; congruence]| exact K].
- apply (inv_M_ext X' st st'); [reflexivity| reflexivity|]. apply (inv_M_X X); [reflexivity| reflexivity| exact IM].
- apply (inv_L_ext st st'); [reflexivity| reflexivity| intros h; destruct h; reflexivity| exact IL].
- destruct IG as [G1 G2 G3 G4 G5]. constructor.
+ intros m b ai Hb. apply (group_ok_ext X' st st'); [reflexivity| reflexivity| |].
* intros q rq Hq K E. apply KEEP; [exact Hq|]. right. intros ->. specialize (NOG b E). rewrite NOG in Hb. discriminate.
* apply (group_ok_X X); [reflexivity|]. eapply G1. exact Hb.
+ exact G2.
+ exact G3.
+ intros q rq Hq K _. apply drop_some in Hq as [Hq NE]. apply (G4 q rq Hq K). rewrite HO. congruence.
+ intros b h Hb. destruct (G5 b h Hb) as (rq & Hq & K). exists rq. split; [| exact K]. apply KEEP; [exact Hq|]. right. intros E. specialize (NOG b E). rewrite NOG in Hb. discriminate.
- apply (inv_S_ext X' st st' BL); [reflexivity| reflexivity| reflexivity|]. apply (inv_S_X X); [reflexivity| exact IS].
- assert (GS : forall q, q <> rid -> get_shadow st' q = get_shadow st q).
{ intros q NE. unfold get_shadow, st', drop_region. cbn. rewrite lookup_delete_ne by congruence. reflexivity. }
assert (KN : forall q o v, q <> rid -> known st (q, o) v -> known st' (q, o) v).
{ intros q o v NE K. unfold known, SHd in *. cbn [fst snd] in *. rewrite GS by exact NE. exact K. }
assert (UN : forall q o, q <> rid -> unknown st (q, o) -> unknown st' (q, o)).
{ intros q o NE K. unfold unknown, SHd in *. cbn [fst snd] in *. rewrite GS by exact NE. exact K. }
assert (HNE : forall b m, hosts st b m -> fst b <> rid).
{ intros b m [ai Hb] E. specialize (NOG b E). rewrite NOG in Hb. discriminate. }
destruct ISH as [D1 D2 D3 D4 D5 D6]; constructor.
+ intros q sh Hq. unfold st', drop_region in Hq. cbn in Hq. apply lookup_delete_Some in Hq as [NE Hq].
destruct (D1 q sh Hq) as (rq & Hrq & K). exists rq. split; [apply drop_keep; auto| exact K].
+ intros q sh Hq. unfold st', drop_region in Hq. cbn in Hq. apply lookup_delete_Some in Hq as [NE Hq]. eapply D2. exact Hq.
+ intros b m i Hb Hi. apply KN; [exact (HNE b m Hb)|]. apply (D3 b m i Hb Hi).
+ intros b m o Hb Ho. apply UN; [exact (HNE b m Hb)|]. apply (D4 b m o Hb Ho).
+ intros b m p i Hb Hml Hs. destruct (D5 b m p i Hb Hml Hs) as ((v3 & K3 & E3 & R3) & K2 & K1 & Q).
pose proof (HNE b m Hb) as NE.
split; [exists v3; split; [apply KN; [exact NE| exact K3]| auto]|]. split; [apply KN; [exact NE| exact K2]|]. split; [apply KN; [exact NE| exact K1]| exact Q].
+ intros k m i Hkk Hs. destruct (D6 k m i Hkk Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
assert (NE : fst (bslot k) <> rid).
{ destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b Hb] & _ & Ek). rewrite Ek. rewrite (slot_start'_eq _ _ _ IM _ _ _ Hb). exact (HNE b m Hb). }
split; [apply KN; [exact NE| exact A1]|]. split; [apply KN; [exact NE| exact A2]|]. split; [apply KN; [exact NE| exact A3]|]. split; [apply KN; [exact NE| exact A4]|].
split; [exact A5|]. split.
* intros Hres. destruct (A6 Hres) as (B1 & B2 & B3 & B4 & B5 & B6). repeat split; try (apply KN; [exact NE| assumption]). exact B6.
* split; [intros Hres; apply KN; [exact NE| apply A7; exact Hres]|]. intros a Ha. apply UN; [exact NE| apply A8; exact Ha].
Qed.
End DROP.

#[using="Type"] Lemma In_perm_map {A B} (f : A -> B) l l' x : Permutation l (map f l') -> In x l' -> In (f x) l.
Proof. intros P Hx. eapply Permutation_in; [apply Permutation_sym; exact P|]. apply in_map. exact Hx. Qed.

#[using="Type"] Lemma group_region_in_ledger X st L rid r :
inv_R X st L -> s_regions st !! rid = Some r -> r_kind r = RKGroup -> In (r_base r, r_len r) (ld_groups L).
Proof.
intros IR Hr Hk. pose proof (ir_groups _ _ _ IR) as P.
apply (In_perm_map (fun kr : N * region => (r_base (snd kr), r_len (snd kr))) _ _ (rid, r) P).
apply filter_In. split; [| rewrite Hk; reflexivity]. apply list_elem_of_In. apply elem_of_map_to_list. exact Hr.
Qed.

#[using="Type"] Lemma brk_quiet_of X st L : inv_R X st L -> brk_quiet L.
Proof.
intros IR. pose proof (ir_brk _ _ _ IR) as B. unfold brk_quiet.
destruct (c_brk (s_ctx st)); [destruct B as [-> _]| rewrite B| destruct B as [-> _]]; exact I.
Qed.

Section FREE.
Hypothesis NTF : NTF_SPEC.

#[using="NTF"] Theorem free_INVL st L BL LS c off n :
INVL x0 st L BL LS -> In ((c, off), n) BL ->
ftree L (free st (Some (aadd c (UNIT * off))))
(fun L' st' => exists LS', INVL x0 st' L' (bl_remove c BL) LS').
Proof.
intros INV Hk.
destruct (block_facts x0 st L BL LS INV c off n Hk) as (m & bm & i & ai & a & ar & ka & BF).
pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
unfold free. rewrite (free_hdr_eq st c off n m bm i ai a ar ka BF). cbn [sbind].
set (p := aadd c (UNIT * off)).
set (st1 := wr16 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st)).

assert (CE1 : ctrl_eq st st1) by (eapply ctrl_eq_trans; [apply ctrl_eq_wr8| apply ctrl_eq_wr16]).
assert (TK1 : s_tick st1 = s_tick st) by reflexivity.
pose proof (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF) as Hs. pose proof (bf_c _ _ _ _ _ _ _ _ _ _ _ BF) as Ec.
pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF) as FIT. pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as OFF. pose proof (bf_n _ _ _ _ _ _ _ _ _ _ _ BF) as N0.
pose proof (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) as [SG _].
assert (INV1 : INVL (xpend x0 (Some c)) st1 L (bl_remove c BL) LS).
{ change c with (bslot ((c, off), n)) at 1 2.
apply (INVL_remove_block x0 st st1 L BL LS ((c, off), n) INV Hk eq_refl CE1 TK1).
- intros m' i' Hs' q Hq. cbn [bslot fst snd] in Hs', Hq. rewrite Hs in Hs'. inversion Hs'. subst m' i'.
subst st1. unfold wr16. rewrite !cell_read_wr8_other; [reflexivity| | |];
intros ->; apply Hq; unfold inT; subst p; rewrite Ec; cbn [fst snd aadd]; rewrite sstart_succ; unfold UNIT, IB in *; lia.
- subst st1. unfold wr16. set (P := fun rid : N => exists r, s_regions st !! rid = Some r /\ r_kind r = RKGroup).
change (forall rid sh, s_shadow (wr8 (aadd (aadd p (-2)) 1) (Z.shiftr 0 8) (wr8 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st))) !! rid = Some sh -> P rid).
assert (HP : P (fst bm)) by (destruct (ig_region _ _ _ IG _ _ (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF)) as (r & Hr & Hkr); exists r; auto).
assert (Efst : forall d1 d2, fst (aadd (aadd p d1) d2) = fst bm) by (intros; subst p; rewrite Ec; reflexivity).
assert (Efst1 : forall d1, fst (aadd p d1) = fst bm) by (intros; subst p; rewrite Ec; reflexivity).
apply (wr8_dom _ _ _ P); [apply (wr8_dom _ _ _ P); [apply (wr8_dom _ _ _ P); [exact (ish_dom _ _ ISH)|]|]|]; rewrite ?Efst, ?Efst1; exact HP.
- subst st1. unfold wr16. apply wr8_tks; [cbn; lia|]. apply wr8_tks; [cbn; lia|]. apply wr8_tks; [cbn; lia|]. exact (ish_ticks _ _ ISH). }

unfold free_tail.
assert (MR1' : forall x, MR st1 x = MR st x) by (intros; apply MR_ext; reflexivity).
assert (MR1 : forall x, get_meta_rec st1 x = get_meta_rec st x) by exact MR1'.
rewrite !MR1.
pose proof (bf_notA _ _ _ _ _ _ _ _ _ _ _ BF) as NA. pose proof (bf_notF _ _ _ _ _ _ _ _ _ _ _ BF) as NF. unfold tbit in NA, NF.
pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi.
rewrite (guard_true 60) by (unfold testbit; rewrite Z.lor_spec; fold (MR st m); rewrite NA, NF; reflexivity).
fold (MR st m).
destruct (negb ((m_freed (MR st m) =? 0) || (Z.lor (m_freed (MR st m)) (m_avail (MR st m)) + bit i =? mask_upto (m_last_idx (MR st m))))) eqn:BR.
-
cbn [ftree ret]. exists LS.
pose proof (ig_ok _ _ _ IG _ _ _ (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF)) as GO.
pose proof (g_masks _ _ _ _ _ _ GO) as (M1 & M2 & M3 & M4 & M5 & M6).
assert (Efun : upd_meta m (m_set_freed (m_freed (MR st m) + bit i)) st1
= upd_meta m (fun r => m_set_avail (m_avail (MR st m)) (m_set_freed (m_freed (MR st m) + bit i) r)) st1).
{ unfold upd_meta. f_equal. all: rewrite <- (MR1 m); fold (MR st1 m); destruct (MR st1 m); reflexivity. }
rewrite Efun.
assert (Hfr : m_freed (MR st m) <> 0).
{ intros E. rewrite E in BR. cbn in BR. discriminate. }
apply (INVL_mask_change (xpend x0 (Some c)) st1 L (bl_remove c BL) LS m bm ai (m_avail (MR st m)) (m_freed (MR st m) + bit i) None INV1).
+ exact (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF).
+ rewrite !MR1'. rewrite bit_eq. unfold tbit.
split; [exact M1|]. split; [pose proof (Z.pow_nonneg 2 i); lia|]. split; [exact M3|]. split; [| split].
* intros j Hj. rewrite testbit_add_bit by (auto; lia). rewrite Bool.orb_true_iff. intros [H|H]; [apply M4; auto| apply Z.eqb_eq in H; lia].
* intros j Hj Ha. rewrite testbit_add_bit by (auto; lia). rewrite Bool.orb_true_iff. intros [H|H]; [exact (M5 j Hj Ha H)| apply Z.eqb_eq in H; subst j; rewrite NA in Ha; discriminate].
* pose proof (bf_ai _ _ _ _ _ _ _ _ _ _ _ BF) as AI. intros j Hj. rewrite testbit_add_bit by (auto; lia). unfold tbit in M6. rewrite (M6 j Hj). reflexivity.
+
intros j Hj. rewrite !MR1'. cbn zeta.
destruct INV1 as (_ & _ & _ & _ & _ & IS1 & _).
pose proof (is_part _ _ _ IS1 bm m ai j (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF) ltac:(rewrite MR1'; exact Hj)) as P1.
rewrite !MR1' in P1. cbn zeta in P1. cbn [x_pend xpend] in P1.
unfold tbit in *. rewrite bit_eq. rewrite testbit_add_bit by (auto; lia).
rewrite (slot_start'_eq _ _ _ IM _ _ _ (ex_intro _ ai (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF))) in P1 |- *.
assert (N5 : ~ (@None aptr = Some (fst bm, sstart (MR st m) j))) by discriminate.
destruct (Z.eqb_spec i j) as [<-|NE].
* rewrite <- Ec in P1 |- *. rewrite NF, Bool.orb_false_l || rewrite Bool.orb_true_r.
unfold one5 in P1 |- *. rewrite NF in P1.
clear - P1. revert P1.
generalize (Z.testbit (m_avail (MR st m)) i = true) as A.
generalize (In c (map bslot (bl_remove c BL))) as U. generalize (s_groups st1 !! c <> None) as Hh.
generalize (@eq (option aptr) (Some c) (Some c)) as P5 || idtac.
intros. assert (FF : ~ (false = true)) by discriminate. assert (N5 : forall x : aptr, ~ (@None aptr = Some x)) by discriminate.
pose proof (N5 c). pose proof (@eq_refl (option aptr) (Some c)). tauto.
* rewrite Bool.orb_false_r.
assert (NS : ~ (Some c = Some (fst bm, sstart (MR st m) j))).
{ intros E. apply NE. assert (E2 : slot_start' (MR st m) i = slot_start' (MR st m) j).
{ rewrite !(slot_start'_eq _ _ _ IM _ _ _ (ex_intro _ ai (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF))). rewrite <- Ec. congruence. }
exact (proj2 (slot_key_inj _ _ _ IS _ _ _ _ _ _ (ex_intro _ ai (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF)) (ex_intro _ ai (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF)) Hi Hj E2)). }
unfold one5 in P1 |- *.
clear - P1 NS N5. revert P1 NS N5.
generalize (Z.testbit (m_avail (MR st m)) j = true) as A. generalize (Z.testbit (m_freed (MR st m)) j = true) as F.
generalize (In (fst bm, sstart (MR st m) j) (map bslot (bl_remove c BL))) as U. generalize (s_groups st1 !! (fst bm, sstart (MR st m) j) <> None) as Hh.
intros. tauto.
+ right. split.
* intros s Hs'. cbn in Hs'. inversion Hs'. subst s. exists i. rewrite !MR1'. split; [exact Hi|]. rewrite (slot_start'_eq _ _ _ IM _ _ _ (ex_intro _ ai (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF))). exact Ec.
* intros s Hs'. discriminate.
+ intros _ sc Hin Hnh. split; [| pose proof (Z.pow_nonneg 2 i); rewrite bit_eq; lia]. exact (proj1 (g_rest _ _ _ _ _ _ GO ltac:(discriminate) sc Hin Hnh)).
+ intros _ Hsc NI. exfalso. apply Hfr. rewrite MR1' in Hsc. exact (proj2 (g_unlisted _ _ _ _ _ _ GO ltac:(discriminate) Hsc NI)).
+ intros _ Hsc Hst. exfalso. apply Hfr. rewrite MR1' in Hsc, Hst. exact (proj2 (g_under _ _ _ _ _ _ GO ltac:(discriminate) Hsc Hst)).
-
pose proof (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF) as Hb.
assert (Hsc0 : 0 <= m_sizeclass (MR st m)).
{ pose proof (g_sc _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hb)) as [[? _]|(E63 & _)]; lia. }
destruct (NTF mstate FUEL (xpend x0 (Some c)) st1 L (bl_remove c BL) LS m bm i
(fun st2 mi => match mi with
| Some (base, len) => if negb (len =? 0)
then SVis (EMunmap (conc st2 base) len) (fun ru => if munmap_answer_ok ru then ret (drop_region (fst base) st2) else bad_answer (ret st1))
else ret st2
| None => ret st2 end) (ret st1) INV1)
as (st' & mi & LS' & EQ & POST).
+ apply (hosts_ext st st1); [reflexivity|]. exists ai. exact Hb.
+ rewrite MR1'. exact Hi.
+ cbn [x_pend xpend]. rewrite MR1', Ec. reflexivity.
+ reflexivity.
+ reflexivity.
+ unfold FUEL. lia.
+ rewrite MR1'. unfold FUEL. lia.
+ rewrite EQ. destruct mi as [[base len]|].
* destruct POST as (r & Hb0 & Hr & Hkr & Hlen & Hpos & INV').
destruct (Z.eqb_spec len 0) as [|NZ]; [lia|]. cbn [negb].
pose proof INV' as (IR' & _).
cbn [ftree]. split.
-- split; [exact (brk_quiet_of _ _ _ IR')|]. exists (r_len r). split; [| right; exact Hlen].
rewrite (conc_eq st' base r Hr), Hb0, Z.add_0_r. exact (group_region_in_ledger _ _ _ _ _ IR' Hr Hkr).
-- intros z. cbn [answer_ok]. destruct (munmap_answer_ok z); [| exact I].
cbn [ftree ret]. exists LS'. rewrite (conc_eq st' base r Hr), Hb0, Z.add_0_r.
apply (INVL_drop_orph (xorph (xpend (xpend x0 (Some c)) None) (Some (fst base))) st' L (bl_remove c BL) LS' (fst base) r INV' eq_refl Hr).
* cbn [ftree ret]. exists LS'. exact POST.
Qed.
End FREE.

End RC__1.
End Mq0.

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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPiB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYTG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYTG.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjcB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjcB.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition xfresh (X : extras) (f : option aptr) : extras := mkX (x_idle X) (x_zomb X) (x_pend X) (x_orph X) f.

#[using="Type"] Lemma data0_shape r : data_of r = data_of meta0 <-> r = mkMeta (m_prev r) (m_next r) None 0 0 0 0 0 0.
Proof.
destruct r; unfold data_of, m_set_prev, m_set_next, meta0; cbn. split; intros H; [injection H; intros; subst; reflexivity| injection H; intros; subst; reflexivity].
Qed.

#[using="Type"] Lemma data0_mem r : data_of r = data_of meta0 -> m_mem r = None.
Proof. intros H. apply data_of_eq in H. destruct H as (H & _). exact H. Qed.

Section DEXT.
Variables (st st' : mstate).
Hypothesis DE : forall x, data_of (MR st' x) = data_of (MR st x).
#[using="DE"] Lemma de_fields x :
m_mem (MR st' x) = m_mem (MR st x) /\ m_avail (MR st' x) = m_avail (MR st x) /\ m_freed (MR st' x) = m_freed (MR st x)
/\ m_last_idx (MR st' x) = m_last_idx (MR st x) /\ m_freeable (MR st' x) = m_freeable (MR st x)
/\ m_sizeclass (MR st' x) = m_sizeclass (MR st x) /\ m_maplen (MR st' x) = m_maplen (MR st x).
Proof. apply data_of_eq. apply DE. Qed.
#[using="DE"] Lemma de_mem x : m_mem (MR st' x) = m_mem (MR st x). Proof. apply de_fields. Qed.
#[using="DE"] Lemma de_avail x : m_avail (MR st' x) = m_avail (MR st x). Proof. apply de_fields. Qed.
#[using="DE"] Lemma de_freed x : m_freed (MR st' x) = m_freed (MR st x). Proof. apply de_fields. Qed.
#[using="DE"] Lemma de_last x : m_last_idx (MR st' x) = m_last_idx (MR st x). Proof. apply de_fields. Qed.
#[using="DE"] Lemma de_freeable x : m_freeable (MR st' x) = m_freeable (MR st x). Proof. apply de_fields. Qed.
#[using="DE"] Lemma de_sc x : m_sizeclass (MR st' x) = m_sizeclass (MR st x). Proof. apply de_fields. Qed.
#[using="DE"] Lemma de_maplen x : m_maplen (MR st' x) = m_maplen (MR st x). Proof. apply de_fields. Qed.
#[using="DE"] Lemma de_stride x : get_stride (MR st' x) = get_stride (MR st x). Proof. apply get_stride_data. apply DE. Qed.
#[using="DE"] Lemma de_gbase x : gbase (MR st' x) = gbase (MR st x). Proof. unfold gbase. rewrite de_mem. reflexivity. Qed.
#[using="DE"] Lemma de_sstart x i : sstart (MR st' x) i = sstart (MR st x) i. Proof. unfold sstart. rewrite de_gbase, de_stride. reflexivity. Qed.
#[using="DE"] Lemma de_slot_start' x i : slot_start' (MR st' x) i = slot_start' (MR st x) i.
Proof. unfold slot_start'. rewrite de_mem, de_stride. reflexivity. Qed.
#[using="DE"] Lemma de_cnt x : cnt_of (MR st' x) = cnt_of (MR st x). Proof. unfold cnt_of. rewrite de_last. reflexivity. Qed.
#[using="DE"] Lemma de_gend x : gend (MR st' x) = gend (MR st x). Proof. unfold gend. rewrite de_sstart, de_cnt. reflexivity. Qed.
End DEXT.

Record ctx_but_heads (c c' : mctx) : Prop := mkCBH {
cb_secret : c_secret c' = c_secret c;
cb_init : c_init_done c' = c_init_done c;
cb_mc : c_mmap_counter c' = c_mmap_counter c;
cb_am : c_avail_meta c' = c_avail_meta c;
cb_amc : c_avail_meta_count c' = c_avail_meta_count c;
cb_amac : c_avail_meta_area_count c' = c_avail_meta_area_count c;
cb_shift : c_meta_alloc_shift c' = c_meta_alloc_shift c;
cb_mah : c_meta_area_head c' = c_meta_area_head c;
cb_mat : c_meta_area_tail c' = c_meta_area_tail c;
cb_amas : c_avail_meta_areas c' = c_avail_meta_areas c;
cb_usage : c_usage c' = c_usage c;
cb_unmap : c_unmap_seq c' = c_unmap_seq c;
cb_bounces : c_bounces c' = c_bounces c;
cb_seq : c_seq c' = c_seq c;
cb_brk : c_brk c' = c_brk c
}.
#[using="Type"] Lemma cbh_refl c : ctx_but_heads c c. Proof. constructor; reflexivity. Qed.
#[using="Type"] Lemma cbh_trans a b c : ctx_but_heads a b -> ctx_but_heads b c -> ctx_but_heads a c.
Proof. intros [] []; constructor; congruence. Qed.
#[using="Type"] Lemma cbh_set_head st h v : ctx_but_heads (s_ctx st) (s_ctx (set_head h v st)).
Proof. destruct h; constructor; reflexivity. Qed.
#[using="Type"] Lemma cbh_upd_meta st m f : ctx_but_heads (s_ctx st) (s_ctx (upd_meta m f st)).
Proof. constructor; reflexivity. Qed.

#[using="Type"] Lemma inv_L_lists st LS : inv_L st LS -> lists_ok st LS.
Proof. intros [L1 L2 L3 L4 L5 L6 L7 L9]. constructor; auto. Qed.

#[using="Type"] Lemma head_of_app (l : list aptr) g : l <> [] -> head_of (l ++ [g]) = head_of l.
Proof. destruct l; cbn; congruence. Qed.

Section RELINK.
Variables (X X' : extras) (st st' : mstate) (L : mled) (BL : list blk) (LS LS' : lhead -> list aptr).
Hypothesis INV : INVL X st L BL LS.
Hypothesis DE : forall x, data_of (MR st' x) = data_of (MR st x).
Hypothesis KEYS : forall x, s_metas st' !! x <> None <-> s_metas st !! x <> None.
Hypotheses (HR : s_regions st' = s_regions st) (HSh : s_shadow st' = s_shadow st) (HN : s_next_rid st' = s_next_rid st)
(HA : s_areas st' = s_areas st) (HG : s_groups st' = s_groups st) (HS : s_slots st' = s_slots st)
(HT : s_tick st' = s_tick st) (HX : s_secret st' = s_secret st) (HV : s_reserved st' = s_reserved st).
Hypothesis HC : ctx_but_heads (s_ctx st) (s_ctx st').
Hypothesis XE : x_pend X' = x_pend X /\ x_orph X' = x_orph X /\ x_zomb X' = x_zomb X.
Hypothesis LO' : lists_ok st' LS'.
Hypothesis H_free : forall m, In m (LS' LFree) -> data_of (MR st m) = data_of meta0.
Hypothesis H_active : forall sc m, In m (LS' (LActive sc)) -> 0 <= sc < 48 /\ live_group st m /\ m_sizeclass (MR st m) = sc.
Hypothesis H_keys : forall sc, LS' (LActive sc) <> [] -> 0 <= sc < 48.
Hypothesis H_actkeys : forall sc g, c_active (s_ctx st') !! sc = Some g -> 0 <= sc < 48.
Hypothesis H_idle : forall m, In m (x_idle X') -> s_metas st' !! m = Some meta0 /\ ~ in_list LS' m.
Hypothesis H_zomb : forall z, In z (x_zomb X) -> m_next (MR st' z) = None /\ m_prev (MR st' z) = None /\ ~ in_list LS' z.
Hypothesis H_groups : forall m b ai, s_groups st !! b = Some (mkGhdr (Some m) ai) ->
(x_fresh X' <> Some m -> ai < m_last_idx (MR st m) -> In m (LS' (LActive (m_sizeclass (MR st m)))))
/\ (x_fresh X' <> Some m -> m_sizeclass (MR st m) < 48 -> ~ in_list LS' m -> m_avail (MR st m) = 0 /\ m_freed (MR st m) = 0)
/\ (x_fresh X' <> Some m -> forall sc, In m (LS' (LActive sc)) -> Some m <> head_of (LS' (LActive sc)) ->
m_avail (MR st m) = 0 /\ m_freed (MR st m) <> 0)
/\ (m_sizeclass (MR st m) = 63 -> ~ in_list LS' m)
/\ (x_fresh X' <> Some m -> m_sizeclass (MR st m) < 48 -> get_stride (MR st m) < UNIT * size_class (m_sizeclass (MR st m)) ->
m_avail (MR st m) = 0 /\ m_freed (MR st m) = 0).

Let dmem := de_mem st st' DE. Let davail := de_avail st st' DE. Let dfreed := de_freed st st' DE.
Let dlast := de_last st st' DE. Let dfreeable := de_freeable st st' DE. Let dsc := de_sc st st' DE.
Let dmaplen := de_maplen st st' DE. Let dstride := de_stride st st' DE. Let dgbase := de_gbase st st' DE.
Let dsstart := de_sstart st st' DE. Let dslot := de_slot_start' st st' DE. Let dcnt := de_cnt st st' DE. Let dgend := de_gend st st' DE.

#[using="HG"] Lemma rl_hosts b m : hosts st' b m <-> hosts st b m. Proof. apply hosts_ext. exact HG. Qed.
#[using="HG"] Lemma rl_live m : live_group st' m <-> live_group st m. Proof. apply live_group_ext. exact HG. Qed.
#[using="HC"] Lemma rl_frontier rid r : frontier st' rid r = frontier st rid r.
Proof. unfold frontier. rewrite (cb_amas _ _ HC). reflexivity. Qed.
#[using="HC"] Lemma rl_usage sc : usage st' sc = usage st sc.
Proof. unfold usage, ctx. rewrite (cb_usage _ _ HC). reflexivity. Qed.
#[using="DE HG dsc dcnt"] Lemma rl_gcnt sc : gcnt st' sc = gcnt st sc.
Proof.
apply gcnt_ext_groups; [exact HG|]. intros b h m Hb Hm. rewrite dsc, dcnt. auto.
Qed.

#[using="X st LS INV DE KEYS HR HSh HN HA HG HS HT HX HV HC XE LO' H_free H_active H_keys H_actkeys H_idle H_zomb H_groups dmem davail dfreed dlast dfreeable dsc dmaplen dstride dgbase dsstart dslot dcnt dgend"] Theorem INVL_relink : INVL X' st' L BL LS'.
Proof.
destruct XE as (XP & XO & XZ).
destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
pose proof HC as [cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 cs12 cs13 cs14 cs15].
split; [| split; [| split; [| split; [| split; [| split]]]]].
-  destruct IR; constructor; rewrite ?HR, ?HN, ?HV, ?HG, ?XO, ?cs6, ?cs7, ?cs10, ?cs15; try assumption.
+ eapply Permutation_trans; [exact ir_metas|]. erewrite map_ext; [apply Permutation_refl|]. intros [rid r]; cbn. rewrite rl_frontier. reflexivity.
+ intros rid r H1 H2. rewrite rl_frontier. exact (ir_metalen rid r H1 H2).
+ intros rid r H1 H2. rewrite rl_frontier. exact (ir_brkfront rid r H1 H2).
-  destruct IA; constructor; rewrite ?HR, ?HA, ?HX, ?cs1, ?cs2, ?cs3, ?cs4, ?cs5, ?cs6, ?cs8, ?cs9, ?cs10, ?cs11, ?cs12, ?cs13, ?cs14; try assumption.
+ intros a ar Ha. destruct (ia_areas a ar Ha) as ((r & ? & ? & ? & ? & ?) & ? & ? & ?). split; [| auto]. exists r. rewrite rl_frontier. auto.
+ intros m mr Hm. assert (K : s_metas st' !! m <> None) by congruence. apply KEYS in K.
destruct (s_metas st !! m) as [mr0|] eqn:E; [| congruence]. exact (ia_metas m mr0 E).
+ destruct ia_avail as [A1 A2]. split; [exact A1|]. intros Hc. destruct (A2 Hc) as (a & T & E & Hk). exists a. split; [exact T|]. split; [exact E|].
intros k Hk2. destruct (s_metas st' !! mslot a k) eqn:E2; [| reflexivity]. exfalso.
assert (K : s_metas st' !! mslot a k <> None) by congruence. apply KEYS in K. apply K. apply Hk. exact Hk2.
+ intros sc Hsc. rewrite rl_usage, rl_gcnt. exact (ia_usage sc Hsc).
-  destruct IM as [M1 M2 M3 M4 M5]; constructor.
+ intros m Hm. apply data0_shape. rewrite DE. apply data0_shape. apply M1. rewrite <- dmem. exact Hm.
+ intros m b Hm. rewrite dmem in Hm. rewrite rl_hosts, XZ. apply M2. exact Hm.
+ intros b h Hb. rewrite HG in Hb. destruct (M3 b h Hb) as (m & ? & ? & ?). exists m. rewrite dmem, dlast. auto.
+ exact H_idle.
+ intros z Hz. rewrite XZ in Hz. destruct (H_zomb z Hz) as (A1 & A2 & A3). destruct (M5 z Hz) as (_ & _ & _ & b & B1 & B2).
split; [exact A3|]. split; [exact A1|]. split; [exact A2|]. exists b. rewrite dmem, HG. auto.
-  destruct LO' as [Q1 Q2 Q3 Q4 Q5]. constructor; try assumption.
+ intros m Hm. apply data0_shape. rewrite DE. apply H_free. exact Hm.
+ intros sc m Hm. destruct (H_active sc m Hm) as (A1 & A2 & A3). rewrite rl_live, dsc. auto.
+ intros [sc|] Hne; [| exact I]. apply H_keys. exact Hne.
-  destruct IG as [G1 G2 G3 G4 G5]; constructor.
+ intros m b ai Hb. rewrite HG in Hb. pose proof (G1 m b ai Hb) as GO. destruct (H_groups m b ai Hb) as (P1 & P2 & P3 & P4 & P5).
destruct GO; constructor; rewrite ?dmem, ?davail, ?dfreed, ?dlast, ?dfreeable, ?dsc, ?dmaplen, ?dstride, ?dcnt, ?dgend, ?HR, ?HS; try assumption.
* apply KEYS. exact g_present.
* destruct g_sc as [A|(A1 & A2 & A3 & A4)]; [left; exact A| right]. auto.
* intros Hml. destruct (g_nest Hml) as (p & i & ? & ? & ? & ? & ?). exists p, i. rewrite dgbase, dsstart, dstride, dsc. auto 10.
+ intros b ai Hb. rewrite HG in Hb. exact (G2 b ai Hb).
+ intros m1 m2 b1 b2 ai1 ai2 H1 H2. rewrite HG in H1, H2. rewrite !dlast, !dsc. eapply G3; eassumption.
+ intros rid r Hr Hk Ho. rewrite HR in Hr. rewrite XO in Ho. destruct (G4 rid r Hr Hk Ho) as (m & Hm & Hml). exists m. rewrite rl_hosts, dmaplen. auto.
+ intros b h Hb. rewrite HG in Hb. rewrite HR. exact (G5 b h Hb).
-  destruct IS as [S1 S2 S3 S4 S5 S6]; constructor.
+ intros s m i Hs. rewrite HS in Hs. destruct (S1 s m i Hs) as (? & ? & ?). rewrite rl_live, dlast, dslot. auto.
+ intros b m i Hb Hi. rewrite HS, dslot. apply (S2 b); [apply rl_hosts; exact Hb| rewrite <- dlast; exact Hi].
+ intros b m ai i Hb Hi. rewrite HG in Hb. rewrite dlast in Hi. rewrite dslot, HG, davail, dfreed, XP. exact (S3 b m ai i Hb Hi).
+ intros s Hs. rewrite HS. apply S4. rewrite <- XP. exact Hs.
+ exact S5.
+ intros k Hk. destruct (S6 k Hk) as (m & i & ? & ?). exists m, i. rewrite HS, dstride. auto.
-  apply (inv_SH_view st st'); auto.
Qed.
End RELINK.

#[using="Type"] Lemma present_MR st x : s_metas st !! x <> None -> s_metas st !! x = Some (MR st x).
Proof. unfold MR, get_meta_rec. destruct (s_metas st !! x); [reflexivity| congruence]. Qed.

#[using="Type"] Lemma fupd_in LS h l h' m : In m (fupd LS h l h') <-> (h' = h /\ In m l) \/ (h' <> h /\ In m (LS h')).
Proof.
unfold fupd. destruct (decide (h' = h)) as [E|NE]; split; intros H; try tauto.
all: destruct H as [[H1 H2]|[H1 H2]]; first [exact H2| congruence].
Qed.

Section OLD.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : INVL X st L BL LS.

#[using="RC__ X L BL INV"] Lemma old_lists : lists_ok st LS. Proof. apply inv_L_lists. exact (proj1 (proj2 (proj2 (proj2 INV)))). Qed.
#[using="RC__ X L BL INV"] Lemma old_free m : In m (LS LFree) -> data_of (MR st m) = data_of meta0.
Proof. intros H. apply data0_shape. exact (il_free _ _ (proj1 (proj2 (proj2 (proj2 INV)))) m H). Qed.
#[using="RC__ X L BL INV"] Lemma old_active sc m : In m (LS (LActive sc)) -> 0 <= sc < 48 /\ live_group st m /\ m_sizeclass (MR st m) = sc.
Proof. exact (il_active _ _ (proj1 (proj2 (proj2 (proj2 INV)))) sc m). Qed.
#[using="RC__ X st L BL INV"] Lemma old_keys sc : LS (LActive sc) <> [] -> 0 <= sc < 48.
Proof. intros H. exact (il_keys _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc) H). Qed.
#[using="RC__ X L BL LS INV"] Lemma old_actkeys sc g : c_active (s_ctx st) !! sc = Some g -> 0 <= sc < 48.
Proof. exact (ia_active_keys _ (proj1 (proj2 INV)) sc g). Qed.
#[using="RC__ L BL INV"] Lemma old_idle m : In m (x_idle X) -> s_metas st !! m = Some meta0 /\ ~ in_list LS m.
Proof. exact (im_idle _ _ _ (proj1 (proj2 (proj2 INV))) m). Qed.
#[using="RC__ L BL INV"] Lemma old_zomb z : In z (x_zomb X) -> m_next (MR st z) = None /\ m_prev (MR st z) = None /\ ~ in_list LS z /\
exists b, m_mem (MR st z) = Some b /\ s_groups st !! b = None.
Proof. intros H. destruct (im_zomb _ _ _ (proj1 (proj2 (proj2 INV))) z H) as (A & B & C & D). auto. Qed.
#[using="RC__ L BL INV"] Lemma old_group m b ai : s_groups st !! b = Some (mkGhdr (Some m) ai) -> group_ok X st LS m b ai.
Proof. intros H. exact (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) m b ai H). Qed.
#[using="RC__ X L BL INV"] Lemma old_63 m b ai : s_groups st !! b = Some (mkGhdr (Some m) ai) -> m_sizeclass (MR st m) = 63 -> ~ in_list LS m.
Proof. intros H E. destruct (g_sc _ _ _ _ _ _ (old_group m b ai H)) as [[[_ Hlt] _]|(_ & _ & _ & NI)]; [lia| exact NI]. Qed.

#[using="RC__ X L BL INV"] Lemma listed_next m h : In m (LS h) -> m_next (MR st m) <> None.
Proof. intros H. apply (lists_in_next_some st LS old_lists h m H). Qed.
#[using="RC__ X L BL INV"] Lemma listed_present m h : In m (LS h) -> s_metas st !! m <> None.
Proof. intros H. destruct (m_next (MR st m)) as [x|] eqn:E; [exact (present_of_next st m x E)|]. exfalso. exact (listed_next m h H E). Qed.
#[using="RC__ X L BL INV"] Lemma head_listed h a : get_head st h = Some a -> In a (LS h).
Proof. intros H. rewrite (il_head _ _ (proj1 (proj2 (proj2 (proj2 INV)))) h) in H. destruct (LS h); cbn in H; [discriminate|]. inversion H. left. reflexivity. Qed.
#[using="RC__ X L BL INV"] Lemma prev_listed h a x : In a (LS h) -> m_prev (MR st a) = Some x -> In x (LS h).
Proof. intros Ha Hp. destruct (lists_prev_in st LS old_lists h a Ha) as (y & Hy & E & _). rewrite Hp in E. inversion E. subst. exact Hy. Qed.
#[using="RC__ X L BL INV"] Lemma next_listed h a x : In a (LS h) -> m_next (MR st a) = Some x -> In x (LS h).
Proof. intros Ha Hn. destruct (lists_next_in st LS old_lists h a Ha) as (y & Hy & E & _). rewrite Hn in E. inversion E. subst. exact Hy. Qed.
#[using="RC__ st L BL INV"] Lemma idle_unlisted m h : In m (x_idle X) -> ~ In m (LS h).
Proof. intros Hi H. apply (proj2 (old_idle m Hi)). exists h. exact H. Qed.
#[using="RC__ st L BL INV"] Lemma zomb_unlisted z h : In z (x_zomb X) -> ~ In z (LS h).
Proof. intros Hz H. apply (proj1 (proj2 (proj2 (old_zomb z Hz)))). exists h. exact H. Qed.
#[using="RC__ L BL LS INV"] Lemma idle_not_live m : In m (x_idle X) -> ~ live_group st m.
Proof.
intros Hi [b Hb]. pose proof (hosts_mem _ _ _ (proj1 (proj2 (proj2 INV))) _ _ Hb) as M.
destruct (old_idle m Hi) as [E _]. unfold MR, get_meta_rec in M. rewrite E in M. cbn in M. discriminate.
Qed.
#[using="RC__ L BL LS INV"] Lemma zomb_not_live z : In z (x_zomb X) -> ~ live_group st z.
Proof.
intros Hz [b Hb]. pose proof (hosts_mem _ _ _ (proj1 (proj2 (proj2 INV))) _ _ Hb) as M.
destruct (old_zomb z Hz) as (_ & _ & _ & b' & M' & G'). rewrite M in M'. inversion M'. subst. destruct Hb as [ai Hb]. rewrite Hb in G'. discriminate.
Qed.
#[using="RC__ X L BL INV"] Lemma free_not_live m : In m (LS LFree) -> ~ live_group st m.
Proof.
intros Hf [b Hb]. pose proof (hosts_mem _ _ _ (proj1 (proj2 (proj2 INV))) _ _ Hb) as M.
pose proof (data0_mem _ (old_free m Hf)) as D. rewrite D in M. discriminate.
Qed.
End OLD.

#[using="Type"] Lemma INVL_set_fresh X st L BL LS f :
INVL X st L BL LS -> x_fresh X = None -> INVL (xfresh X f) st L BL LS.
Proof.
intros INV HF.
refine (INVL_relink X (xfresh X f) st st L BL LS LS INV (fun x => eq_refl) (fun x => iff_refl _)
eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl (cbh_refl _) _
(old_lists _ _ _ _ _ INV) (old_free _ _ _ _ _ INV) (old_active _ _ _ _ _ INV) (old_keys _ _ _ _ _ INV)
(old_actkeys _ _ _ _ _ INV) _ _ _).
- cbn. auto.
- cbn. apply (old_idle _ _ _ _ _ INV).
- intros z Hz. destruct (old_zomb _ _ _ _ _ INV z Hz) as (A & B & C & _). auto.
- intros m b ai Hb. pose proof (old_group _ _ _ _ _ INV m b ai Hb) as GO.
assert (NF : x_fresh X <> Some m) by (rewrite HF; discriminate).
split; [| split; [| split; [| split]]].
+ intros _. exact (g_partial _ _ _ _ _ _ GO NF).
+ intros _. exact (g_unlisted _ _ _ _ _ _ GO NF).
+ intros _. exact (g_rest _ _ _ _ _ _ GO NF).
+ exact (old_63 _ _ _ _ _ INV m b ai Hb).
+ intros _. exact (g_under _ _ _ _ _ _ GO NF).
Qed.

#[using="Type"] Lemma INVL_clear_fresh X st L BL LS g :
INVL X st L BL LS -> x_fresh X = Some g ->
(forall b ai, s_groups st !! b = Some (mkGhdr (Some g) ai) ->
(ai < m_last_idx (MR st g) -> In g (LS (LActive (m_sizeclass (MR st g)))))
/\ (m_sizeclass (MR st g) < 48 -> ~ in_list LS g -> m_avail (MR st g) = 0 /\ m_freed (MR st g) = 0)
/\ (forall sc, In g (LS (LActive sc)) -> Some g <> head_of (LS (LActive sc)) -> m_avail (MR st g) = 0 /\ m_freed (MR st g) <> 0)
/\ (m_sizeclass (MR st g) < 48 -> get_stride (MR st g) < UNIT * size_class (m_sizeclass (MR st g)) -> m_avail (MR st g) = 0 /\ m_freed (MR st g) = 0)) ->
INVL (xfresh X None) st L BL LS.
Proof.
intros INV HF OB.
refine (INVL_relink X (xfresh X None) st st L BL LS LS INV (fun x => eq_refl) (fun x => iff_refl _)
eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl (cbh_refl _) _
(old_lists _ _ _ _ _ INV) (old_free _ _ _ _ _ INV) (old_active _ _ _ _ _ INV) (old_keys _ _ _ _ _ INV)
(old_actkeys _ _ _ _ _ INV) _ _ _).
- cbn. auto.
- cbn. apply (old_idle _ _ _ _ _ INV).
- intros z Hz. destruct (old_zomb _ _ _ _ _ INV z Hz) as (A & B & C & _). auto.
- intros m b ai Hb. pose proof (old_group _ _ _ _ _ INV m b ai Hb) as GO.
destruct (aptr_eq_dec m g) as [->|NE].
+ destruct (OB b ai Hb) as (O1 & O2 & O3 & O4). split; [| split; [| split; [| split]]]; auto. exact (old_63 _ _ _ _ _ INV g b ai Hb).
+ assert (NF : x_fresh X <> Some m) by (rewrite HF; congruence).
split; [| split; [| split; [| split]]].
* intros _. exact (g_partial _ _ _ _ _ _ GO NF).
* intros _. exact (g_unlisted _ _ _ _ _ _ GO NF).
* intros _. exact (g_rest _ _ _ _ _ _ GO NF).
* exact (old_63 _ _ _ _ _ INV m b ai Hb).
* intros _. exact (g_under _ _ _ _ _ _ GO NF).
Qed.

#[using="Type"] Lemma queue_frame h g st : let st' := queue_st h g st in
s_regions st' = s_regions st /\ s_shadow st' = s_shadow st /\ s_next_rid st' = s_next_rid st
/\ s_areas st' = s_areas st /\ s_groups st' = s_groups st /\ s_slots st' = s_slots st
/\ s_tick st' = s_tick st /\ s_secret st' = s_secret st /\ s_reserved st' = s_reserved st
/\ ctx_but_heads (s_ctx st) (s_ctx st').
Proof.
unfold queue_st, q_link, q_single. destruct (get_head st h) as [a|]; [destruct (m_prev (get_meta_rec st a))| destruct h]; cbn;
repeat split; try reflexivity; constructor; reflexivity.
Qed.

#[using="Type"] Lemma queue_metas_other h g st x :
x <> g -> (forall a, get_head st h = Some a -> x <> a /\ m_prev (MR st a) <> Some x) ->
s_metas (queue_st h g st) !! x = s_metas st !! x.
Proof.
intros NE H. unfold queue_st, q_link, q_single. destruct (get_head st h) as [a|] eqn:E.
- destruct (H a eq_refl) as [NA NP]. unfold MR in NP.
destruct (m_prev (get_meta_rec st a)) as [pv|] eqn:Ep; rewrite !s_metas_upd_meta, !lookup_insert_ne by congruence; reflexivity.
- rewrite set_head_metas, s_metas_upd_meta, lookup_insert_ne by congruence. reflexivity.
Qed.

#[using="Type"] Lemma dequeue_frame h m st : let st' := dequeue h m st in
s_regions st' = s_regions st /\ s_shadow st' = s_shadow st /\ s_next_rid st' = s_next_rid st
/\ s_areas st' = s_areas st /\ s_groups st' = s_groups st /\ s_slots st' = s_slots st
/\ s_tick st' = s_tick st /\ s_secret st' = s_secret st /\ s_reserved st' = s_reserved st
/\ ctx_but_heads (s_ctx st) (s_ctx st').
Proof.
unfold dequeue.
destruct (m_prev (get_meta_rec st m)) as [pv|]; destruct (m_next (get_meta_rec st m)) as [nx|]; cbn -[get_head optr_eqb aptr_eqb];
repeat match goal with |- context [if ?c then _ else _] => destruct c end; try destruct h; cbn;
repeat split; try reflexivity; constructor; reflexivity.
Qed.

#[using="Type"] Lemma dequeue_metas_other h m st x :
x <> m -> m_prev (MR st m) <> Some x -> m_next (MR st m) <> Some x ->
s_metas (dequeue h m st) !! x = s_metas st !! x.
Proof.
intros NE NP NN. unfold dequeue, MR in *.
rewrite s_metas_upd_meta, lookup_insert_ne by congruence.
destruct (m_prev (get_meta_rec st m)) as [pv|]; destruct (m_next (get_meta_rec st m)) as [nx|]; cbn -[get_head optr_eqb aptr_eqb upd_meta set_head];
repeat match goal with |- context [if ?c then _ else _] => destruct c end;
rewrite ?set_head_metas, ?s_metas_upd_meta, ?lookup_insert_ne by congruence; try reflexivity;
rewrite ?set_head_metas, ?s_metas_upd_meta, ?lookup_insert_ne by congruence; try reflexivity.
Qed.

#[using="Type"] Lemma get_head_active st sc : get_head st (LActive sc) = c_active (s_ctx st) !! sc.
Proof. reflexivity. Qed.

Section QUEUE.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (g : aptr) (h : lhead).
Hypothesis INV : INVL X st L BL LS.
Hypothesis NL : m_next (MR st g) = None.
Hypothesis PRES : s_metas st !! g <> None.
Hypothesis HQ : match h with
| LActive sc => 0 <= sc < 48 /\ live_group st g /\ m_sizeclass (MR st g) = sc /\ x_fresh X = Some g
| LFree => data_of (MR st g) = data_of meta0 /\ ~ In g (x_idle X) /\ ~ In g (x_zomb X)
end.
Let st' := queue_st h g st.
Let LS' := fupd LS h (LS h ++ [g]).

#[using="Type"] Lemma q_in m h' : In m (LS' h') <-> In m (LS h') \/ (h' = h /\ m = g).
Proof.
unfold LS'. rewrite fupd_in, in_app_iff. cbn. destruct (decide (h' = h)) as [->|NE]; intuition congruence.
Qed.
#[using="Type"] Lemma q_in_list m : in_list LS' m <-> in_list LS m \/ m = g.
Proof.
unfold in_list. split.
- intros [h' H]. apply q_in in H. destruct H as [H|[_ ->]]; [left; exists h'; exact H| right; reflexivity].
- intros [[h' H]| ->]; [exists h'; apply q_in; left; exact H| exists h; apply q_in; right; auto].
Qed.
#[using="RC__ X st L BL INV NL"] Lemma g_unlisted_old h' : ~ In g (LS h').
Proof. exact (lists_notin st LS (old_lists _ _ _ _ _ INV) g NL h'). Qed.
#[using="RC__ st L BL LS h INV HQ"] Lemma g_not_idle : ~ In g (x_idle X).
Proof.
destruct h as [sc|]; [| exact (proj1 (proj2 HQ))]. destruct HQ as (_ & Hl & _). intros Hi. exact (idle_not_live _ _ _ _ _ INV g Hi Hl).
Qed.
#[using="RC__ st L BL LS h INV HQ"] Lemma g_not_zomb : ~ In g (x_zomb X).
Proof.
destruct h as [sc|]; [| exact (proj2 (proj2 HQ))]. destruct HQ as (_ & Hl & _). intros Hz. exact (zomb_not_live _ _ _ _ _ INV g Hz Hl).
Qed.
#[using="RC__ X L BL INV"] Lemma untouched x : (forall h', ~ In x (LS h')) -> x <> g -> s_metas st' !! x = s_metas st !! x.
Proof.
intros NI NE. apply queue_metas_other; [exact NE|]. intros a Ha. split.
- intros ->. exact (NI h (head_listed _ _ _ _ _ INV h a Ha)).
- intros Hp. exact (NI h (prev_listed _ _ _ _ _ INV h a x (head_listed _ _ _ _ _ INV h a Ha) Hp)).
Qed.

#[using="INV NL PRES HQ"] Theorem INVL_queue : INVL X st' L BL LS'.
Proof.
destruct (queue_frame h g st) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & FC).
refine (INVL_relink X X st st' L BL LS LS' INV (queue_data h g st) _ F1 F2 F3 F4 F5 F6 F7 F8 F9 FC _ _ _ _ _ _ _ _ _).
-  intros x. split; [| apply queue_keys_mono]. intros K. apply queue_keys in K.
destruct K as [K|[->|[Hh|(a & Ha & Hp)]]]; [exact K| exact PRES| |].
+ exact (listed_present _ _ _ _ _ INV x h (head_listed _ _ _ _ _ INV h x Hh)).
+ exact (listed_present _ _ _ _ _ INV x h (prev_listed _ _ _ _ _ INV h a x (head_listed _ _ _ _ _ INV h a Ha) Hp)).
- auto.
- apply lists_queue; [apply (old_lists _ _ _ _ _ INV)| exact NL].
- intros m Hm. apply q_in in Hm. destruct Hm as [Hm|[E ->]]; [exact (old_free _ _ _ _ _ INV m Hm)|]. subst h. exact (proj1 HQ).
- intros sc m Hm. apply q_in in Hm. destruct Hm as [Hm|[E ->]]; [exact (old_active _ _ _ _ _ INV sc m Hm)|]. subst h. destruct HQ as (A & B & C & _). auto.
- intros sc Hne. destruct (decide (LActive sc = h)) as [E|NE].
+ subst h. exact (proj1 HQ).
+ unfold LS' in Hne. rewrite fupd_ne in Hne by exact NE. exact (old_keys _ _ _ _ _ INV sc Hne).
- intros sc x Hx. rewrite <- get_head_active in Hx. unfold st' in Hx. rewrite queue_head in Hx.
destruct (decide (LActive sc = h)) as [E|NE]; [subst h; exact (proj1 HQ)|]. exact (old_actkeys _ _ _ _ _ INV sc x Hx).
- intros m Hm. cbn in Hm. destruct (old_idle _ _ _ _ _ INV m Hm) as [E NI].
assert (NE : m <> g) by (intros ->; exact (g_not_idle Hm)).
split; [rewrite untouched; [exact E| intros h'; apply (idle_unlisted _ _ _ _ _ INV); exact Hm| exact NE]|].
rewrite q_in_list. tauto.
- intros z Hz. destruct (old_zomb _ _ _ _ _ INV z Hz) as (A & B & C & _).
assert (NE : z <> g) by (intros ->; exact (g_not_zomb Hz)).
assert (E : MR st' z = MR st z).
{ unfold MR, get_meta_rec. rewrite untouched; [reflexivity| intros h'; apply (zomb_unlisted _ _ _ _ _ INV); exact Hz| exact NE]. }
rewrite E, q_in_list. repeat split; auto. tauto.
- intros m b ai Hb. pose proof (old_group _ _ _ _ _ INV m b ai Hb) as GO. split; [| split; [| split; [| split]]].
5:{ exact (g_under _ _ _ _ _ _ GO). }
+ intros NF Hai. apply q_in. left. exact (g_partial _ _ _ _ _ _ GO NF Hai).
+ intros NF Hsc NI. apply (g_unlisted _ _ _ _ _ _ GO NF Hsc). rewrite q_in_list in NI. tauto.
+ intros NF sc Hm Hh. apply q_in in Hm. destruct Hm as [Hm|[E ->]].
* apply (g_rest _ _ _ _ _ _ GO NF sc Hm). unfold LS' in Hh. destruct (decide (LActive sc = h)) as [E|NE].
-- subst h. rewrite fupd_eq in Hh. rewrite head_of_app in Hh; [exact Hh|]. intros E0. rewrite E0 in Hm. exact Hm.
-- rewrite fupd_ne in Hh by exact NE. exact Hh.
* exfalso. subst h. apply NF. exact (proj2 (proj2 (proj2 HQ))).
+ intros H63. rewrite q_in_list. intros [NI| ->]; [exact (old_63 _ _ _ _ _ INV m b ai Hb H63 NI)|].
destruct h as [sc|].
* destruct HQ as (A & _ & C & _). lia.
* pose proof (hosts_mem _ _ _ (proj1 (proj2 (proj2 INV))) _ _ (ex_intro _ ai Hb)) as M.
rewrite (data0_mem _ (proj1 HQ)) in M. discriminate.
Qed.
End QUEUE.

Section DEQUEUE.
Variables (X X' : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (m : aptr) (h : lhead) (l1 l2 : list aptr).
Hypothesis INV : INVL X st L BL LS.
Hypothesis HL : LS h = l1 ++ m :: l2.
Hypothesis HX : (exists sc, h = LActive sc /\ x_fresh X = None /\ X' = xfresh X (Some m)) \/ (h = LFree /\ X' = xidle X (m :: x_idle X)).
Let st' := dequeue h m st.
Let LS' := fupd LS h (l1 ++ l2).

#[using="l1 l2 HL"] Lemma m_listed : In m (LS h). Proof. rewrite HL. apply in_app_iff. right. left. reflexivity. Qed.
#[using="X X' m HL HX"] Lemma d_in x h' : In x (LS' h') -> In x (LS h').
Proof.
unfold LS'. rewrite fupd_in. intros [[-> H]|[_ H]]; [| exact H]. rewrite HL. apply in_app_iff in H. apply in_app_iff. cbn. tauto.
Qed.
#[using="X X' HL HX"] Lemma d_in_rev x h' : In x (LS h') -> x <> m -> In x (LS' h').
Proof.
intros H NE. unfold LS'. apply fupd_in. destruct (decide (h' = h)) as [->|NE'].
- left. split; [reflexivity|]. rewrite HL in H. apply in_app_iff in H. apply in_app_iff. cbn in H. destruct H as [H|[H|H]]; [tauto| congruence| tauto].
- right. auto.
Qed.
#[using="X X' m HL HX"] Lemma d_in_list x : in_list LS' x -> in_list LS x.
Proof. intros [h' H]. exists h'. apply (d_in x h' H). Qed.
#[using="RC__ X X' st L BL INV HL HX"] Lemma m_out : ~ in_list LS' m.
Proof.
intros [h' H]. unfold LS' in H. apply fupd_in in H. destruct H as [[-> H]|[NE H]].
- pose proof (il_nodup _ _ (proj1 (proj2 (proj2 (proj2 INV)))) h) as ND. rewrite HL in ND.
destruct (NoDup_In_split l1 l2 m ND) as [N1 N2]. apply in_app_iff in H. tauto.
- apply NE. exact (il_disj _ _ (proj1 (proj2 (proj2 (proj2 INV)))) h' h m H m_listed).
Qed.
#[using="RC__ X L BL l1 l2 INV HL"] Lemma untouched_d x : (forall h', ~ In x (LS h')) -> s_metas st' !! x = s_metas st !! x.
Proof.
intros NI. apply dequeue_metas_other.
- intros ->. exact (NI h m_listed).
- intros Hp. exact (NI h (prev_listed _ _ _ _ _ INV h m x m_listed Hp)).
- intros Hn. exact (NI h (next_listed _ _ _ _ _ INV h m x m_listed Hn)).
Qed.
#[using="RC__ X st L BL m INV HL"] Lemma nonhead_old x : In x (LS' h) -> Some x <> head_of (LS' h) -> Some x <> head_of (LS h).
Proof.
intros Hx Hh. unfold LS' in Hx, Hh. rewrite fupd_eq in Hx, Hh. rewrite HL. destruct l1 as [|a l1']; cbn in *.
- intros E. inversion E. subst x.
pose proof (il_nodup _ _ (proj1 (proj2 (proj2 (proj2 INV)))) h) as ND. rewrite HL in ND. cbn in ND.
apply NoDup_cons in ND as [N _]. apply N. apply list_elem_of_In. exact Hx.
- exact Hh.
Qed.
#[using="Type"] Lemma MR'_m : MR st' m = data_of (MR st m).
Proof.
pose proof (dequeue_data h m st m) as D. fold st' in D. rewrite <- D.
unfold st', dequeue, MR. rewrite get_meta_rec_upd_same. reflexivity.
Qed.

#[using="X INV HL HX"] Theorem INVL_dequeue : INVL X' st' L BL LS'.
Proof.
destruct (dequeue_frame h m st) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & FC).
refine (INVL_relink X X' st st' L BL LS LS' INV (dequeue_data h m st) _ F1 F2 F3 F4 F5 F6 F7 F8 F9 FC _ _ _ _ _ _ _ _ _).
-  intros x. split; [| apply dequeue_keys_mono]. intros K. apply dequeue_keys in K.
destruct K as [K|[->|[Hp|Hn]]]; [exact K| exact (listed_present _ _ _ _ _ INV m h m_listed)| |].
+ exact (listed_present _ _ _ _ _ INV x h (prev_listed _ _ _ _ _ INV h m x m_listed Hp)).
+ exact (listed_present _ _ _ _ _ INV x h (next_listed _ _ _ _ _ INV h m x m_listed Hn)).
- destruct HX as [(sc & Eh & HD & ->)|(Eh & ->)]; cbn; auto.
- apply lists_dequeue; [apply (old_lists _ _ _ _ _ INV)| exact HL].
- intros x Hx. exact (old_free _ _ _ _ _ INV x (d_in x LFree Hx)).
- intros sc x Hx. exact (old_active _ _ _ _ _ INV sc x (d_in x _ Hx)).
- intros sc Hne. apply (old_keys _ _ _ _ _ INV sc). intros E. apply Hne. unfold LS'. unfold fupd.
destruct (decide (LActive sc = h)) as [E2|NE2]; [| exact E]. exfalso. rewrite E2, HL in E. destruct l1; discriminate.
- intros sc x Hx. rewrite <- get_head_active in Hx. unfold st' in Hx. rewrite dequeue_head in Hx.
destruct (decide (LActive sc = h)) as [E|NE]; [| exact (old_actkeys _ _ _ _ _ INV sc x Hx)].
apply (old_keys _ _ _ _ _ INV sc). rewrite E, HL. destruct l1; discriminate.
- intros x Hx.
assert (OLD : In x (x_idle X) -> s_metas st' !! x = Some meta0 /\ ~ in_list LS' x).
{ intros Hi. destruct (old_idle _ _ _ _ _ INV x Hi) as [E NI]. split.
- rewrite untouched_d; [exact E|]. intros h'. apply (idle_unlisted _ _ _ _ _ INV). exact Hi.
- intros IL'. exact (NI (d_in_list x IL')). }
destruct HX as [(sc & Eh & HD & EX)|(Eh & EX)]; rewrite EX in Hx; cbn in Hx; [exact (OLD Hx)|].
destruct Hx as [<-|Hx]; [| exact (OLD Hx)].
split; [| exact m_out].
rewrite (present_MR st' m (dequeue_key_m h m st)). f_equal. rewrite MR'_m.
apply (old_free _ _ _ _ _ INV). rewrite <- Eh. exact m_listed.
- intros z Hz. destruct (old_zomb _ _ _ _ _ INV z Hz) as (A & B & C & _).
assert (E : MR st' z = MR st z).
{ unfold MR, get_meta_rec. rewrite untouched_d; [reflexivity|]. intros h'. apply (zomb_unlisted _ _ _ _ _ INV). exact Hz. }
rewrite E. repeat split; auto. intros IL'. exact (C (d_in_list z IL')).
- intros x b ai Hb. pose proof (old_group _ _ _ _ _ INV x b ai Hb) as GO.
destruct (aptr_eq_dec x m) as [->|NEm].
+ destruct HX as [(sc & Eh & HD & EX)|(Eh & EX)].
* pose proof m_listed as ML. rewrite Eh in ML. destruct (old_active _ _ _ _ _ INV sc m ML) as (A1 & A2 & A3).
rewrite EX. cbn. split; [| split; [| split; [| split]]]; [intros NF; exfalso; apply NF; reflexivity..| | intros NF; exfalso; apply NF; reflexivity]. intros H63. lia.
* exfalso. pose proof m_listed as ML. rewrite Eh in ML. exact (free_not_live _ _ _ _ _ INV m ML (ex_intro _ b (ex_intro _ ai Hb))).
+ assert (HNF : x_fresh X' <> Some x -> x_fresh X <> Some x).
{ destruct HX as [(sc & Eh & HD & ->)|(Eh & ->)]; cbn; [rewrite HD; intros _; discriminate| exact (fun H => H)]. }
split; [| split; [| split; [| split]]].
5:{ intros NF. exact (g_under _ _ _ _ _ _ GO (HNF NF)). }
* intros NF Hai. apply d_in_rev; [| exact NEm]. exact (g_partial _ _ _ _ _ _ GO (HNF NF) Hai).
* intros NF Hsc NI. apply (g_unlisted _ _ _ _ _ _ GO (HNF NF) Hsc). intros [h' H]. apply NI. exists h'. apply d_in_rev; [exact H| exact NEm].
* intros NF sc Hx Hh. apply (g_rest _ _ _ _ _ _ GO (HNF NF) sc (d_in x _ Hx)).
destruct (decide (LActive sc = h)) as [E|NE].
-- rewrite E in Hx, Hh |- *. exact (nonhead_old x Hx Hh).
-- unfold LS' in Hh. rewrite fupd_ne in Hh by exact NE. exact Hh.
* intros H63 IL'. exact (old_63 _ _ _ _ _ INV x b ai Hb H63 (d_in_list x IL')).
Qed.
End DEQUEUE.

Section ROTATE.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (sc : Z) (a a' : aptr) (rest : list aptr).
Hypothesis INV : INVL X st L BL LS.
Hypothesis HL : LS (LActive sc) = a :: rest.
Hypothesis Hn : m_next (MR st a) = Some a'.
Hypothesis OB : x_fresh X <> Some a -> rest <> [] -> m_avail (MR st a) = 0 /\ m_freed (MR st a) <> 0.
Let h := LActive sc.
Let st' := set_head h (Some a') st.
Let LS' := fupd LS h (rest ++ [a]).

#[using="HL"] Lemma r_in x h' : In x (LS' h') <-> In x (LS h').
Proof.
unfold LS'. rewrite fupd_in. destruct (decide (h' = h)) as [->|NE].
- unfold h. rewrite HL, in_app_iff. cbn. tauto.
- tauto.
Qed.
#[using="HL"] Lemma r_in_list x : in_list LS' x <-> in_list LS x.
Proof. unfold in_list. split; intros [h' H]; exists h'; apply r_in; exact H. Qed.

#[using="INV HL Hn OB"] Theorem INVL_rotate : INVL X st' L BL LS'.
Proof.
refine (INVL_relink X X st st' L BL LS LS' INV (fun x => eq_refl) (fun x => iff_refl _)
eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl (cbh_set_head st h (Some a')) _
_ _ _ _ _ _ _ _).
- auto.
- apply lists_rotate; [apply (old_lists _ _ _ _ _ INV)| exact HL| exact Hn].
- intros m Hm. apply r_in in Hm. exact (old_free _ _ _ _ _ INV m Hm).
- intros sc0 m Hm. apply r_in in Hm. exact (old_active _ _ _ _ _ INV sc0 m Hm).
- intros sc0 Hne. apply (old_keys _ _ _ _ _ INV sc0). intros E. apply Hne. unfold LS', fupd.
destruct (decide (LActive sc0 = h)) as [E2|NE2]; [| exact E]. exfalso. unfold h in E2. inversion E2. subst. rewrite HL in E. discriminate.
- intros sc0 x Hx. rewrite <- get_head_active in Hx. unfold st' in Hx.
destruct (decide (LActive sc0 = h)) as [E|NE].
+ apply (old_keys _ _ _ _ _ INV sc0). unfold h in E. inversion E. subst. rewrite HL. discriminate.
+ rewrite get_head_set_head_other in Hx by exact NE. exact (old_actkeys _ _ _ _ _ INV sc0 x Hx).
- intros m Hm. cbn in Hm. destruct (old_idle _ _ _ _ _ INV m Hm) as [E NI]. split; [| rewrite r_in_list; exact NI].
unfold st'. rewrite set_head_metas. exact E.
- intros z Hz. destruct (old_zomb _ _ _ _ _ INV z Hz) as (A & B & C & _).
unfold st', MR. rewrite get_meta_rec_set_head. fold (MR st z). rewrite r_in_list. auto.
- intros m b ai Hb. pose proof (old_group _ _ _ _ _ INV m b ai Hb) as GO. split; [| split; [| split; [| split]]].
5:{ exact (g_under _ _ _ _ _ _ GO). }
+ intros NF Hai. apply r_in. exact (g_partial _ _ _ _ _ _ GO NF Hai).
+ intros NF Hsc NI. rewrite r_in_list in NI. exact (g_unlisted _ _ _ _ _ _ GO NF Hsc NI).
+ intros NF sc0 Hm Hh. destruct (decide (LActive sc0 = h)) as [E|NE].
* unfold h in E. inversion E. subst sc0. unfold LS' in Hm, Hh. fold h in Hm, Hh. rewrite fupd_eq in Hm, Hh.
apply in_app_iff in Hm. destruct Hm as [Hm|[<-|[]]].
-- apply (g_rest _ _ _ _ _ _ GO NF sc). { unfold h in HL. rewrite HL. right. exact Hm. }
unfold h in HL. rewrite HL. cbn. intros E2. inversion E2. subst m.
pose proof (il_nodup _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc)) as ND. rewrite HL in ND.
apply NoDup_cons in ND as [N _]. apply N. apply list_elem_of_In. exact Hm.
-- apply OB; [exact NF|]. intros ->. cbn in Hh. apply Hh. reflexivity.
* unfold LS' in Hm, Hh. rewrite fupd_ne in Hm, Hh by exact NE. exact (g_rest _ _ _ _ _ _ GO NF sc0 Hm Hh).
+ intros H63. rewrite r_in_list. exact (old_63 _ _ _ _ _ INV m b ai Hb H63).
Qed.
End ROTATE.

End RC__1.
