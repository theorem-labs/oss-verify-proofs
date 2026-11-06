(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Bool Lia.
From stdpp Require gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi QUZl Qfya Qatc QSfG Q7S0 QdBa QpFQ QPiB QLaA Q1am.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import stdpp.gmap.
Import QZAi.Mq2 QUZl Qfya Qatc QSfG.Mq2 Q7S0 QdBa.Mq0 QpFQ QPiB QLaA.Mq0 Q1am.Mq1.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition TW (st : mstate) (P : aptr -> Prop) : Prop :=
forall rid sh o v t, s_shadow st !! rid = Some sh -> r_cells sh !! o = Some (v, t) -> t = s_tick st -> P (rid, o).

Definition TF0 (st : mstate) : Prop :=
forall rid sh o v t, s_shadow st !! rid = Some sh -> r_cells sh !! o = Some (v, t) -> (t < s_tick st)%N.

Definition PS (st : mstate) (q : aptr) : Prop :=
exists b m, hosts st b m /\ fst b = fst q /\
((exists i, 0 <= i <= cnt_of (MR st m) /\ snd q = sstart (MR st m) i - IB)
\/ (m_maplen (MR st m) = 0 /\ snd b - 3 <= snd q <= snd b - 1)).

Definition TF2 (st : mstate) : Prop := TW st (PS st).

#[using="Type"] Lemma TF0_TW st P : TF0 st -> TW st P.
Proof. intros H rid sh o v t Hs Hc Ht. exfalso. pose proof (H rid sh o v t Hs Hc). lia. Qed.
#[using="Type"] Lemma TF0_TF2 st : TF0 st -> TF2 st. Proof. apply TF0_TW. Qed.
#[using="Type"] Lemma TF0_TF st : TF0 st -> TF st.
Proof. intros H rid sh o v t Hs Hc Ht. exfalso. pose proof (H rid sh o v t Hs Hc). lia. Qed.

#[using="Type"] Lemma TW_mono st (P P' : aptr -> Prop) : (forall q, P q -> P' q) -> TW st P -> TW st P'.
Proof. intros HP H rid sh o v t Hs Hc Ht. apply HP. eapply H; eassumption. Qed.

#[using="Type"] Lemma TW_ctrl st st' P : s_shadow st' = s_shadow st -> s_tick st' = s_tick st -> TW st P -> TW st' P.
Proof. intros E1 E2 H rid sh o v t Hs Hc Ht. rewrite E1 in Hs. rewrite E2 in Ht. eapply H; eassumption. Qed.

#[using="Type"] Lemma TF0_ctrl st st' : s_shadow st' = s_shadow st -> s_tick st' = s_tick st -> TF0 st -> TF0 st'.
Proof. intros E1 E2 H rid sh o v t Hs Hc. rewrite E1 in Hs. rewrite E2. eapply H; eassumption. Qed.

#[using="Type"] Lemma TF0_tick_new st t : TKS st (s_tick st) -> (s_tick st < t)%N -> TF0 (set_tick t st).
Proof.
intros TK Ht rid sh o v tk Hs Hc. cbn in Hs |- *. destruct (TK rid sh Hs) as (C & _ & _). destruct (C o v tk Hc) as [_ Hle]. lia.
Qed.

#[using="Type"] Lemma TF0_hdr_havoc st b : TF0 st -> TF0 (hdr_havoc b st).
Proof.
intros H rid sh o v t Hs Hc. unfold hdr_havoc, upd_shadow in Hs. cbn in Hs.
change (s_tick (hdr_havoc b st)) with (s_tick st).
destruct (N.eq_dec rid (fst b)) as [->|NE].
- rewrite lookup_insert_eq in Hs. inversion Hs; subst; clear Hs. cbn in Hc.
unfold get_shadow in Hc. destruct (s_shadow st !! fst b) as [sh0|] eqn:E0; cbn in Hc.
+ eapply H; eassumption.
+ rewrite lookup_empty in Hc. discriminate.
- rewrite lookup_insert_ne in Hs by congruence. eapply H; eassumption.
Qed.

#[using="Type"] Lemma TW_hdr_havoc st b P : TW st P -> TW (hdr_havoc b st) P.
Proof.
intros H rid sh o v t Hs Hc Ht. unfold hdr_havoc, upd_shadow in Hs. cbn in Hs.
change (s_tick (hdr_havoc b st)) with (s_tick st) in Ht.
destruct (N.eq_dec rid (fst b)) as [->|NE].
- rewrite lookup_insert_eq in Hs. inversion Hs; subst; clear Hs. cbn in Hc.
unfold get_shadow in Hc. destruct (s_shadow st !! fst b) as [sh0|] eqn:E0; cbn in Hc.
+ eapply H; [eassumption| eassumption| first [reflexivity| exact Ht]].
+ rewrite lookup_empty in Hc. discriminate.
- rewrite lookup_insert_ne in Hs by congruence. eapply H; [eassumption| eassumption| first [reflexivity| exact Ht]].
Qed.

#[using="Type"] Lemma TW_wr8' st q v P : TW st P -> P q -> TW (wr8 q v st) P.
Proof.
intros H Hq rid sh o w t Hs Hc Ht. change (s_tick (wr8 q v st)) with (s_tick st) in Ht.
unfold wr8, upd_shadow in Hs. cbn in Hs.
destruct (N.eq_dec rid (fst q)) as [->|NE].
- rewrite lookup_insert_eq in Hs. inversion Hs; subst; clear Hs. cbn in Hc.
destruct (Z.eq_dec o (snd q)) as [->|NEo].
+ replace (fst q, snd q) with q by (destruct q; reflexivity). exact Hq.
+ rewrite lookup_insert_ne in Hc by congruence. unfold get_shadow in Hc.
destruct (s_shadow st !! fst q) as [sh0|] eqn:E0; cbn in Hc; [| rewrite lookup_empty in Hc; discriminate].
eapply H; [exact E0| exact Hc| first [reflexivity| exact Ht]].
- rewrite lookup_insert_ne in Hs by congruence. eapply H; [exact Hs| exact Hc| first [reflexivity| exact Ht]].
Qed.

#[using="Type"] Lemma TW_wrs l : forall st P, TW st P -> (forall q, In q (map fst l) -> P q) -> TW (wrs l st) P.
Proof.
induction l as [|[q v] l IH]; intros st P H HP; cbn [wrs]; [exact H|].
apply IH.
- apply TW_wr8'; [exact H| apply HP; left; reflexivity].
- intros q' Hq'. apply HP. right. exact Hq'.
Qed.

Definition geom_kept (st st' : mstate) : Prop :=
forall b m, hosts st b m -> hosts st' b m /\ (forall i, sstart (MR st' m) i = sstart (MR st m) i)
/\ cnt_of (MR st' m) = cnt_of (MR st m) /\ m_maplen (MR st' m) = m_maplen (MR st m).

#[using="Type"] Lemma geom_kept_refl st : geom_kept st st.
Proof. intros b m H. auto. Qed.
#[using="Type"] Lemma geom_kept_trans a b c : geom_kept a b -> geom_kept b c -> geom_kept a c.
Proof.
intros H1 H2 bb m H. destruct (H1 _ _ H) as (Hb & S1 & C1 & M1). destruct (H2 _ _ Hb) as (Hc & S2 & C2 & M2).
split; [exact Hc|]. split; [intros i; rewrite S2; apply S1|]. split; congruence.
Qed.

#[using="Type"] Lemma PS_mono st st' q : geom_kept st st' -> PS st q -> PS st' q.
Proof.
intros GK (b & m & Hm & Hf & ALT). destruct (GK _ _ Hm) as (Hm' & S & C & ML).
exists b, m. split; [exact Hm'|]. split; [exact Hf|].
destruct ALT as [(i & Hi & E)|(Z0 & R0)].
- left. exists i. rewrite C, S. auto.
- right. rewrite ML. auto.
Qed.

#[using="Type"] Lemma TF2_kept st st' : s_shadow st' = s_shadow st -> s_tick st' = s_tick st -> geom_kept st st' -> TF2 st -> TF2 st'.
Proof.
intros E1 E2 GK H. unfold TF2. eapply TW_mono; [intros q; apply (PS_mono st st' q GK)|]. exact (TW_ctrl st st' _ E1 E2 H).
Qed.

#[using="Type"] Lemma geom_kept_of st st' :
(forall b h, s_groups st !! b = Some h -> s_groups st' !! b = Some h) ->
(forall b m, hosts st b m -> MR st' m = MR st m) ->
geom_kept st st'.
Proof.
intros HG HM b m Hm. pose proof Hm as [ai Hb]. split; [exists ai; apply HG; exact Hb|].
rewrite (HM _ _ Hm). auto.
Qed.

#[using="Type"] Lemma wr8_cells_other st q v rid o : (rid, o) <> q ->
r_cells (get_shadow (wr8 q v st) rid) !! o = r_cells (get_shadow st rid) !! o.
Proof.
intros NE. unfold get_shadow at 1. rewrite (wr8_shadow_lookup st q v rid).
destruct (N.eqb_spec rid (fst q)) as [->|NR]; [| reflexivity]. cbn.
rewrite lookup_insert_ne; [reflexivity|]. intros E. apply NE. rewrite <- E. destruct q; reflexivity.
Qed.

#[using="Type"] Lemma wrs_cells_other l : forall st rid o, ~ In (rid, o) (map fst l) ->
r_cells (get_shadow (wrs l st) rid) !! o = r_cells (get_shadow st rid) !! o.
Proof.
induction l as [|[q v] l IH]; intros st rid o Hn; cbn [wrs]; [reflexivity|].
rewrite IH by (cbn in Hn; tauto). apply wr8_cells_other. cbn in Hn. intros E. apply Hn. left. symmetry. exact E.
Qed.

Section INTERIOR.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : INVL X st L BL LS.

#[using="RC__ X L BL LS INV"] Lemma sstart_res b x i : hosts st b x -> (sstart (MR st x) i - IB) mod 16 = 12.
Proof.
intros Hx. pose proof INV as (_ & _ & IM0 & _ & IG0 & _).
pose proof (stride_ge X st LS IG0 _ _ Hx) as [SG SM]. destruct (hosts_ok X st LS IG0 _ _ Hx) as (a & Hb & GO). pose proof (g_align _ _ _ _ _ _ GO) as [A0 A16].
unfold sstart, IB, UNIT in *. rewrite (hosts_gbase X st LS IM0 _ _ Hx).
pose proof (Z.div_mod (snd b) 16 ltac:(lia)) as D1. rewrite A16 in D1. pose proof (Z.div_mod (get_stride (MR st x)) 16 ltac:(lia)) as D2. rewrite SM in D2.
replace (snd b + 16 + get_stride (MR st x) * i - 4) with (12 + (snd b / 16 + get_stride (MR st x) / 16 * i) * 16) by nia.
rewrite Z_mod_plus_full. reflexivity.
Qed.
Variables (g bg : aptr) (idx : Z).
Hypothesis Hg : hosts st bg g.
Hypothesis Hidx : 0 <= idx <= m_last_idx (MR st g).
Hypothesis NH : s_groups st !! (fst bg, sstart (MR st g) idx) = None.

Let IM := proj1 (proj2 (proj2 INV)).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

#[using="RC__ X L BL LS INV Hg Hidx NH IM IG IS"] Lemma PS_not_interior q :
PS st q -> fst q = fst bg -> ~ (sstart (MR st g) idx <= snd q < sstart (MR st g) (idx + 1) - IB).
Proof.
intros (b & m & Hm & Hf & ALT) Hq HI. rewrite Hq in Hf.
destruct ALT as [(i & Hi & E)|(Z0 & R0)].
- destruct (Z.eq_dec i (cnt_of (MR st m))) as [Ei|NEi].
+
assert (Hi' : 0 <= i <= m_last_idx (MR st m) + 1) by (unfold cnt_of in *; lia).
destruct (aptr_eq_dec m g) as [->|NEm].
* pose proof (sstart_mono X st LS IG _ _ (idx + 1) i Hg ltac:(unfold cnt_of in *; lia)). unfold IB in *. lia.
* destruct (sep_hdr0 _ _ _ _ IM IG IS g bg idx Hg Hidx NH m b i Hm Hf Hi' ltac:(left; exact NEm)); unfold IB in *; lia.
+ assert (Hi' : 0 <= i <= m_last_idx (MR st m) + 1) by (unfold cnt_of in *; lia).
destruct (aptr_eq_dec m g) as [->|NEm].
* destruct (Z.eq_dec i idx) as [->|NEi2]; [unfold IB in *; lia|].
destruct (sep_hdr0 _ _ _ _ IM IG IS g bg idx Hg Hidx NH g b i Hm Hf Hi' ltac:(right; exact NEi2)); unfold IB in *; lia.
* destruct (sep_hdr0 _ _ _ _ IM IG IS g bg idx Hg Hidx NH m b i Hm Hf Hi' ltac:(left; exact NEm)); unfold IB in *; lia.
-
destruct (hosts_ok X st LS IG _ _ Hm) as (ai & Hb & GO).
destruct (g_nest _ _ _ _ _ _ GO Z0) as (p & ip & Hsl & Hfp & _ & _ & _).
destruct (is_valid _ _ _ IS _ _ _ Hsl) as (LVp & Hip & Eb).
destruct LVp as [bp Hp].
rewrite (slot_start'_eq _ _ _ IM _ _ _ Hp) in Eb.
assert (Hfb : fst bp = fst bg) by (rewrite Eb in Hf; exact Hf).
assert (Esnd : snd b = sstart (MR st p) ip) by (rewrite Eb; reflexivity).
assert (NE : p <> g \/ ip <> idx).
{ destruct (aptr_eq_dec p g) as [->|]; [| left; assumption]. right. intros ->.
pose proof (hosts_inj _ _ _ IM _ _ _ Hp Hg) as Ebp. rewrite Ebp in Eb. rewrite Eb in Hb. rewrite NH in Hb. discriminate. }
destruct (sep_h3 _ _ _ _ IM IG IS g bg idx Hg Hidx NH p bp ip Hp Hfb Hip NE); unfold IB in *; lia.
Qed.

#[using="RC__ X L BL LS INV Hg Hidx NH IM IG IS"] Lemma TF2_interior_old :
TF2 st -> forall o v t, r_cells (get_shadow st (fst bg)) !! o = Some (v, t) ->
sstart (MR st g) idx <= o < sstart (MR st g) (idx + 1) - IB -> (t < s_tick st)%N.
Proof.
intros TF o v t Hc Ho. destruct (get_shadow_cells_some st (fst bg) o (v, t) Hc) as (sh & Hs & Hc').
destruct (TKS_of _ _ _ _ _ INV (fst bg) sh Hs) as (C & _ & _). destruct (C o v t Hc') as [_ Hle].
destruct (N.eq_dec t (s_tick st)) as [Et|]; [| lia]. exfalso.
exact (PS_not_interior (fst bg, o) (TF _ _ _ _ _ Hs Hc' Et) eq_refl Ho).
Qed.

#[using="RC__ X L BL LS INV IG"] Lemma TF2_ghdr_old (p : aptr) :
TF2 st -> snd p mod 16 = 0 ->
forall o v t, snd p <= o < snd p + 12 -> r_cells (get_shadow st (fst p)) !! o = Some (v, t) -> (t < s_tick st)%N.
Proof.
intros TF Al o v t Ho Hc. destruct (get_shadow_cells_some st (fst p) o (v, t) Hc) as (sh & Hs & Hc').
destruct (TKS_of _ _ _ _ _ INV (fst p) sh Hs) as (C & _ & _). destruct (C o v t Hc') as [_ Hle].
destruct (N.eq_dec t (s_tick st)) as [Et|]; [| lia]. exfalso.
destruct (TF _ _ _ _ _ Hs Hc' Et) as (b & m & Hm & Hf & ALT). cbn in Hf.
destruct ALT as [(i & Hi & E)|(Z0 & R0)]; cbn in *.
- pose proof (sstart_res b m i Hm) as RS. rewrite <- E in RS.
pose proof (Z.div_mod o 16 ltac:(lia)). pose proof (Z.div_mod (snd p) 16 ltac:(lia)). lia.
- destruct (hosts_ok X st LS IG _ _ Hm) as (ai & Hb & GO). pose proof (g_align _ _ _ _ _ _ GO) as [_ A16]. unfold UNIT in A16.
pose proof (Z.div_mod o 16 ltac:(lia)). pose proof (Z.div_mod (snd p) 16 ltac:(lia)). pose proof (Z.div_mod (snd b) 16 ltac:(lia)).
pose proof (Z.mod_pos_bound o 16 ltac:(lia)). lia.
Qed.

#[using="RC__ X L BL LS INV IG"] Lemma TF2_TF : TF2 st -> TF st.
Proof.
intros TF rid sh o v t Hs Hc Ht. destruct (TF _ _ _ _ _ Hs Hc Ht) as (b & m & Hm & Hf & ALT). cbn in Hf.
destruct ALT as [(i & Hi & E)|(Z0 & R0)]; cbn in *.
- pose proof (sstart_res b m i Hm) as RS. rewrite <- E in RS. pose proof (Z.mod_pos_bound o 16 ltac:(lia)). lia.
- destruct (hosts_ok X st LS IG _ _ Hm) as (ai & Hb & GO). pose proof (g_align _ _ _ _ _ _ GO) as [_ A16]. unfold UNIT in A16.
pose proof (Z.div_mod o 16 ltac:(lia)). pose proof (Z.div_mod (snd b) 16 ltac:(lia)).
pose proof (Z.mod_pos_bound o 16 ltac:(lia)). lia.
Qed.
End INTERIOR.

End RC__1.
End Mq0.
From Stdlib Require Permutation.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m QYTG QjcB QaiD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Qfya QPiB.Mq0 Qatc QSfG.Mq2 Q7S0 QdBa.Mq1 QdBa.Mq0 QpFQ Ql2m.Mq1 QPiB QdBa.Mq2 Ql2m.Mq2 QYTG.Mq1 QjcB QLaA QaiD QLaA.Mq0 Q1am.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma one5_iff (A B C D E A' B' C' D' E' : Prop) :
(A <-> A') -> (B <-> B') -> (C <-> C') -> (D <-> D') -> (E <-> E') -> one5 A B C D E -> one5 A' B' C' D' E'.
Proof. unfold one5. tauto. Qed.

#[using="Type"] Lemma one5_E_to_B (A B C D E B' E' : Prop) : E -> B' -> ~ E' -> one5 A B C D E -> one5 A B' C D E'.
Proof. unfold one5. tauto. Qed.

Section AOR.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (g bg : aptr) (ai i : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hg : s_groups st !! bg = Some (mkGhdr (Some g) ai).
Hypothesis Hi : 0 <= i <= m_last_idx (MR st g).
Hypothesis HP : x_pend X = Some (fst bg, sstart (MR st g) i).
Hypothesis C1 : x_fresh X <> Some g -> forall sc, In g (LS (LActive sc)) -> Some g <> head_of (LS (LActive sc)) -> m_avail (MR st g) = 0.
Hypothesis C2 : x_fresh X <> Some g -> m_sizeclass (MR st g) < 48 -> in_list LS g.
Hypothesis C3 : m_sizeclass (MR st g) < 48 -> UNIT * size_class (m_sizeclass (MR st g)) <= get_stride (MR st g).
Let st' := upd_meta g (fun r => m_set_freed (Z.lor (m_freed r) (bit i)) r) st.

#[using="Type"] Lemma aor_form : st' = upd_meta g (fun r => m_set_avail (m_avail (MR st g)) (m_set_freed (Z.lor (m_freed (MR st g)) (bit i)) r)) st.
Proof. unfold st', upd_meta, MR. destruct (get_meta_rec st g); reflexivity. Qed.

#[using="bg ai INV Hg Hi HP C1 C2 C3"] Theorem INVL_aor : INVL (xpend X None) st' L BL LS.
Proof.
pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
pose proof (ig_ok _ _ _ IG _ _ _ Hg) as GO. pose proof (g_masks _ _ _ _ _ _ GO) as (M1 & M2 & M3 & M4 & M5 & M6).
pose proof (g_li _ _ _ _ _ _ GO) as LI. pose proof (g_ai _ _ _ _ _ _ GO) as AI.
assert (Hgh : hosts st bg g) by (exists ai; exact Hg).
pose proof (is_part _ _ _ IS _ _ _ i Hg Hi) as Pi. cbn zeta in Pi. rewrite (slot_start'_eq _ _ _ IM _ _ _ Hgh) in Pi.
assert (NA : tbit (m_avail (MR st g)) i = false).
{ destruct (tbit (m_avail (MR st g)) i) eqn:E; [| reflexivity]. exfalso. unfold one5 in Pi. tauto. }
assert (TB : forall j, 0 <= j -> tbit (Z.lor (m_freed (MR st g)) (bit i)) j = tbit (m_freed (MR st g)) j || (i =? j)).
{ intros j Hj. unfold tbit. rewrite Z.lor_spec, testbit_bit by lia. reflexivity. }
assert (NZ : Z.lor (m_freed (MR st g)) (bit i) <> 0).
{ intros E. pose proof (TB i ltac:(lia)) as T. rewrite E, Z.eqb_refl, Bool.orb_true_r in T. unfold tbit in T. rewrite Z.bits_0 in T. discriminate. }
rewrite aor_form.
apply (INVL_mask_change X st L BL LS g bg ai (m_avail (MR st g)) (Z.lor (m_freed (MR st g)) (bit i)) None INV Hg).
- split; [exact M1|]. split; [apply Z.lor_nonneg; split; [exact M2| unfold bit; apply Z.pow_nonneg; lia]|]. split; [exact M3|].
split; [| split].
+ intros j Hj. rewrite TB by exact Hj. rewrite Bool.orb_true_iff. intros [H|H]; [exact (M4 j Hj H)| apply Z.eqb_eq in H; lia].
+ intros j Hj Ha. rewrite TB by exact Hj. rewrite Bool.orb_true_iff. intros [H|H]; [exact (M5 j Hj Ha H)| apply Z.eqb_eq in H; subst j; rewrite NA in Ha; discriminate].
+ intros j Hj. rewrite TB by lia. rewrite (M6 j Hj). reflexivity.
- intros j Hj. cbn zeta. rewrite TB by lia.
pose proof (is_part _ _ _ IS _ _ _ j Hg Hj) as P. cbn zeta in P. rewrite (slot_start'_eq _ _ _ IM _ _ _ Hgh) in P |- *.
destruct (Z.eqb_spec i j) as [<-|NE].
+ rewrite Bool.orb_true_r. eapply one5_E_to_B; [exact HP| reflexivity| discriminate| exact P].
+ rewrite Bool.orb_false_r. eapply one5_iff; [reflexivity| reflexivity| reflexivity| reflexivity| | exact P].
rewrite HP. split; [intros E; exfalso| discriminate]. inversion E.
destruct (Z.lt_total i j) as [LT|[EQ|LT]]; [| lia|].
* pose proof (sstart_lt _ _ _ IG _ _ i j Hgh LT). pose proof (stride_ge _ _ _ IG _ _ Hgh) as [SG _]. unfold UNIT in *. lia.
* pose proof (sstart_lt _ _ _ IG _ _ j i Hgh LT). pose proof (stride_ge _ _ _ IG _ _ Hgh) as [SG _]. unfold UNIT in *. lia.
- right. split.
+ intros s Hs. rewrite HP in Hs. inversion Hs. subst s. exists i. split; [exact Hi|]. rewrite (slot_start'_eq _ _ _ IM _ _ _ Hgh). reflexivity.
+ intros s Hs. discriminate.
- intros NF sc Hin Hnh. split; [exact (C1 NF sc Hin Hnh)| exact NZ].
- intros NF Hsc NI. exfalso. exact (NI (C2 NF Hsc)).
- intros _ Hsc Hlt. exfalso. pose proof (C3 Hsc). lia.
Qed.
End AOR.

Section ACT.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (a ba : aptr) (aia : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Ha : s_groups st !! ba = Some (mkGhdr (Some a) aia).
Hypothesis AV0 : m_avail (MR st a) = 0.
Hypothesis HEAD : head_of (LS (LActive (m_sizeclass (MR st a)))) = Some a.
Let act := mask_upto aia.
Let A' := Z.land (m_freed (MR st a)) act.
Let F' := Z.ldiff (m_freed (MR st a)) act.
Let st' := upd_meta a (fun r => m_set_avail A' (m_set_freed F' r)) st.

#[using="RC__ X L BL LS ba INV Ha A' F'"] Lemma act_eq : match m_mem (MR st a) with
| Some _ => mask_upto (group_active_idx st (default (0%N, -1) (m_mem (MR st a))))
| None => 0 end = act.
Proof.
pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
rewrite (hosts_mem _ _ _ IM _ _ (ex_intro _ aia Ha)). cbn. unfold group_active_idx, get_group. rewrite Ha.
pose proof (g_ai _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Ha)) as AI. pose proof (g_li _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Ha)) as LI.
unfold act. f_equal. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. change (2 ^ 5) with 32. lia.
Qed.

#[using="RC__ X L BL LS ba INV Ha AV0"] Lemma activate_group_eq {T} (k : mstate -> Z -> M T) bail : activate_group a st k bail = k st' A'.
Proof.
unfold activate_group. fold (MR st a). rewrite AV0. cbn [guard Z.eqb]. rewrite act_eq. reflexivity.
Qed.

#[using="HEAD"] Lemma a_listed : In a (LS (LActive (m_sizeclass (MR st a)))).
Proof. destruct (LS (LActive (m_sizeclass (MR st a)))); cbn in HEAD; [discriminate|]. inversion HEAD. left. reflexivity. Qed.

#[using="ba INV Ha AV0 HEAD"] Theorem INVL_activate : INVL X st' L BL LS.
Proof.
pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
pose proof (ig_ok _ _ _ IG _ _ _ Ha) as GO. pose proof (g_masks _ _ _ _ _ _ GO) as (M1 & M2 & M3 & M4 & M5 & M6).
pose proof (g_li _ _ _ _ _ _ GO) as LI. pose proof (g_ai _ _ _ _ _ _ GO) as AI.
assert (Hah : hosts st ba a) by (exists aia; exact Ha).
assert (TA : forall j, 0 <= j -> tbit A' j = tbit (m_freed (MR st a)) j && (j <=? aia)).
{ intros j Hj. unfold A', act, tbit. rewrite Z.land_spec, testbit_mask_upto by lia. reflexivity. }
assert (TF : forall j, 0 <= j -> tbit F' j = tbit (m_freed (MR st a)) j && negb (j <=? aia)).
{ intros j Hj. unfold F', act, tbit. rewrite Z.ldiff_spec, testbit_mask_upto by lia. reflexivity. }
assert (X_eta : X = mkX (x_idle X) (x_zomb X) (x_pend X) (x_orph X) (x_fresh X)) by (destruct X; reflexivity).
rewrite X_eta at 1.
apply (INVL_mask_change X st L BL LS a ba aia A' F' (x_pend X) INV Ha).
- split; [apply Z.land_nonneg; left; exact M2|]. split; [apply Z.ldiff_nonneg; left; exact M2|].
split; [| split; [| split]].
+ intros j Hj. rewrite TA by exact Hj. rewrite Bool.andb_true_iff. intros [_ H]. apply Z.leb_le in H. exact H.
+ intros j Hj. rewrite TF by exact Hj. rewrite Bool.andb_true_iff. intros [H _]. exact (M4 j Hj H).
+ intros j Hj. rewrite TA, TF by exact Hj. rewrite !Bool.andb_true_iff. intros [_ H1] [_ H2]. rewrite H1 in H2. discriminate.
+ intros j Hj. rewrite TF by lia. rewrite (M6 j Hj). cbn. destruct (Z.leb_spec j aia); [lia| reflexivity].
- intros j Hj. cbn zeta. rewrite TA, TF by lia.
pose proof (is_part _ _ _ IS _ _ _ j Ha Hj) as P. cbn zeta in P.
assert (NAj : tbit (m_avail (MR st a)) j = false) by (unfold tbit; rewrite AV0; apply Z.bits_0).
rewrite NAj in P.
destruct (tbit (m_freed (MR st a)) j); destruct (j <=? aia); cbn [andb negb]; revert P; unfold one5; clear; tauto.
- left. reflexivity.
- intros NF sc Hin Hnh. exfalso. destruct (il_active _ _ IL sc a Hin) as (_ & _ & E). subst sc. exact (Hnh (eq_sym HEAD)).
- intros NF Hsc NI. exfalso. apply NI. exists (LActive (m_sizeclass (MR st a))). exact a_listed.
- intros NF Hsc Hlt. destruct (g_under _ _ _ _ _ _ GO NF Hsc Hlt) as [_ F0]. unfold A', F'. rewrite F0. split; [apply Z.land_0_l| apply Z.ldiff_0_l].
Qed.
End ACT.

End RC__1.
End Mq1.

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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1am.Mq0.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Record AM_frame (st st1 : mstate) : Prop := mkAMF {
amf_groups : s_groups st1 = s_groups st;
amf_slots : s_slots st1 = s_slots st;
amf_shadow : s_shadow st1 = s_shadow st;
amf_tick : s_tick st1 = s_tick st;
amf_active : forall sc, active st1 sc = active st sc;
amf_usage : forall sc, usage st1 sc = usage st sc;
amf_bounces : c_bounces (s_ctx st1) = c_bounces (s_ctx st);
amf_seq : c_seq (s_ctx st1) = c_seq (s_ctx st);
amf_mc : c_mmap_counter (s_ctx st1) = c_mmap_counter (s_ctx st);
amf_regions : forall rid r, s_regions st !! rid = Some r -> r_kind r = RKGroup -> s_regions st1 !! rid = Some r;
amf_next_rid : (s_next_rid st <= s_next_rid st1)%N;
amf_ssec : s_secret st1 = s_secret st;

amf_init : c_init_done (s_ctx st) = 1 -> c_init_done (s_ctx st1) = 1;

amf_hmetas : forall b m ai, s_groups st !! b = Some (mkGhdr (Some m) ai) -> MR st1 m = MR st m
}.
#[using="Type"] Lemma amf_refl st : AM_frame st st.
Proof. constructor; auto; first [reflexivity| lia]. Qed.
#[using="Type"] Lemma amf_trans a b c : AM_frame a b -> AM_frame b c -> AM_frame a c.
Proof.
intros [A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14] [B1 B2 B3 B4 B5 B6 B7 B8 B9 B10 B11 B12 B13 B14]; constructor; try congruence.
- intros rid r H K. apply B10; [| exact K]. apply A10; assumption.
- clear -A11 B11. eapply N.le_trans; eassumption.
- auto.
- intros b0 m ai Hb. rewrite <- (A14 b0 m ai Hb). apply (B14 b0 m ai). rewrite A1. exact Hb.
Qed.

Record L_frame (L L1 : mled) : Prop := mkLF {
lf_groups : ld_groups L1 = ld_groups L;
lf_live : ld_live L1 = ld_live L;
lf_resv : ld_resv L1 = ld_resv L
}.
#[using="Type"] Lemma lf_refl L : L_frame L L. Proof. constructor; reflexivity. Qed.
#[using="Type"] Lemma lf_trans a b c : L_frame a b -> L_frame b c -> L_frame a c.
Proof. intros [] []; constructor; congruence. Qed.

#[using="Type"] Lemma inv_SH_view' st st' BL :
s_shadow st' = s_shadow st -> s_tick st' = s_tick st ->
(forall rid r, s_regions st !! rid = Some r -> r_kind r = RKGroup -> s_regions st' !! rid = Some r) ->
s_groups st' = s_groups st -> s_slots st' = s_slots st -> s_metas st' = s_metas st ->
inv_SH st BL -> inv_SH st' BL.
Proof.
intros SH TK HR HG HS HM I.
pose proof (inv_SH_view st (set_regions (s_regions st) st') BL SH TK eq_refl HG HS) as V.
assert (ME : forall x, MR (set_regions (s_regions st) st') x = MR st x) by (intros; apply MR_ext; exact HM).
specialize (V ltac:(intros; rewrite ME; reflexivity) ltac:(intros; rewrite ME; reflexivity) ltac:(intros; rewrite ME; reflexivity) ltac:(intros; rewrite ME; reflexivity) I).
destruct V as [D1 D2 D3 D4 D5 D6]; constructor; try assumption.
intros rid sh H. destruct (D1 rid sh H) as (r & Hr & K). exists r. split; [apply HR; assumption| exact K].
Qed.

#[using="Type"] Lemma mslot_succ a k : aadd (mslot a k) META_SIZE = mslot a (k + 1).
Proof. unfold mslot, aadd, META_SIZE. cbn. f_equal. lia. Qed.

Section TAKE.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : INVL X st L BL LS.
Hypothesis HC : 0 < c_avail_meta_count (s_ctx st).

#[using="INV HC"] Lemma am_take_ok {T} (k : mstate -> optr -> M T) bail :
exists m st2, am_take st k bail = k st2 (Some m) /\ INVL (xidle X (m :: x_idle X)) st2 L BL LS /\ AM_frame st st2 /\ ~ In m (x_idle X).
Proof.
destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
destruct (ia_avail _ IA) as [A1 A2]. destruct (A2 HC) as (a & Ht & Eam & FREE).
set (k0 := NSLOTS - c_avail_meta_count (s_ctx st)) in *.
exists (mslot a k0).
unfold am_take, ctx. rewrite Eam.
set (st1 := upd_ctx _ st). set (st2 := upd_meta (mslot a k0) _ st1).
exists st2. split; [reflexivity|].
assert (ABS : s_metas st !! mslot a k0 = None) by (apply FREE; lia).
assert (MRm : MR st (mslot a k0) = meta0) by (unfold MR, get_meta_rec; rewrite ABS; reflexivity).
assert (M2 : s_metas st2 = <[mslot a k0 := meta0]> (s_metas st)).
{ unfold st2, st1. rewrite s_metas_upd_meta. cbn. f_equal. rewrite get_meta_rec_upd_ctx. fold (MR st (mslot a k0)). rewrite MRm. reflexivity. }
assert (MR2 : forall x, MR st2 x = MR st x).
{ intros x. unfold MR, get_meta_rec. rewrite M2. destruct (aptr_eq_dec x (mslot a k0)) as [->|NE].
- rewrite lookup_insert_eq, ABS. reflexivity.
- rewrite lookup_insert_ne by congruence. reflexivity. }
assert (DE : forall x, data_of (MR st2 x) = data_of (MR st x)) by (intros x; rewrite MR2; reflexivity).
assert (KEYS : forall x, s_metas st2 !! x <> None <-> s_metas st !! x <> None \/ x = mslot a k0).
{ intros x. rewrite M2. destruct (aptr_eq_dec x (mslot a k0)) as [->|NE].
- rewrite lookup_insert_eq. split; [auto| discriminate].
- rewrite lookup_insert_ne by congruence. tauto. }
assert (Ha : s_areas st !! a <> None) by (apply (ia_tail _ IA); exact Ht).
assert (NLm : forall h, ~ In (mslot a k0) (LS h)).
{ intros h Hin. apply (listed_present _ _ _ _ _ (conj IR (conj IA (conj IM (conj IL (conj IG (conj IS ISH)))))) _ _ Hin). exact ABS. }
split.
-
split; [| split; [| split; [| split; [| split; [| split]]]]].
+ destruct IR; constructor; try assumption.
+ destruct (s_areas st !! a) as [ar|] eqn:Ea; [| congruence].
assert (CT2 : c_meta_area_tail (s_ctx st2) = c_meta_area_tail (ctx st)) by reflexivity.
assert (CC2 : c_avail_meta_count (s_ctx st2) = c_avail_meta_count (s_ctx st) - 1) by reflexivity.
assert (CA2 : c_avail_meta (s_ctx st2) = Some (mslot a (k0 + 1))) by (rewrite <- mslot_succ; reflexivity).
destruct IA; constructor.
* exact ia_ctx.
* exact ia_secret.
* exact ia_areas.
* exact ia_head.
* exact ia_tail.
* cbn. intros Hn. exfalso. unfold ctx in Ht. rewrite Ht in Hn. discriminate.
* intros m mr Hm. rewrite M2 in Hm. destruct (aptr_eq_dec m (mslot a k0)) as [->|NE].
-- exists a, ar, k0. split; [exact Ea|]. split; [unfold k0; lia| reflexivity].
-- rewrite lookup_insert_ne in Hm by congruence. exact (ia_metas m mr Hm).
* rewrite CT2, CA2, CC2. split; [lia|]. intros Hc. exists a. split; [exact Ht|]. split; [unfold k0; f_equal; f_equal; lia|].
intros k1 Hk1. rewrite M2, lookup_insert_ne; [apply FREE; lia|]. unfold mslot, aadd. intros E. inversion E. unfold META_SIZE in *. lia.
* rewrite CA2. intros q Hq. inversion Hq. subst q. unfold mslot, aadd. cbn [fst].
destruct (ia_areas _ _ Ea) as ((r & Hr & K & _) & _). exists r. auto.
* intros sc Hsc. unfold usage, ctx. cbn. fold (ctx st). fold (usage st sc). rewrite (ia_usage sc Hsc). symmetry.
apply (gcnt_ext_groups st st2 eq_refl). intros b h m _ _. rewrite MR2. auto.
* exact ia_usage_keys.
* exact ia_active_keys.
+ destruct IM as [Q1 Q2 Q3 Q4 Q5]; constructor; cbn [x_idle x_zomb x_pend x_orph x_fresh xidle].
* intros m Hm. rewrite !MR2 in *. exact (Q1 m Hm).
* intros m b Hm. rewrite MR2 in Hm. exact (Q2 m b Hm).
* intros b h Hb. destruct (Q3 b h Hb) as (m & ? & ? & ?). exists m. rewrite !MR2. auto.
* intros m [<-|Hm].
-- split; [rewrite M2, lookup_insert_eq; reflexivity|]. intros [h Hin]. exact (NLm h Hin).
-- destruct (Q4 m Hm) as [E NI]. split; [| exact NI]. rewrite M2, lookup_insert_ne; [exact E|]. intros Emm. congruence.
* intros z Hz. rewrite !MR2. exact (Q5 z Hz).
+ destruct IL as [L1 L2 L3 L4 L5 L6 L7 L9]; constructor; try assumption.
all: try (intros h; destruct h; cbn; apply L1).
* intros h. pose proof (L2 h) as D. destruct (LS h) as [|x l]; [exact I|]. cbn [dll] in D |- *. eapply linked_ext; [| | exact D]; intros; rewrite MR2; reflexivity.
* intros m. rewrite !MR2. apply L5.
* intros m Hm. rewrite !MR2. apply L6. exact Hm.
* intros sc m Hm. rewrite MR2. exact (L7 sc m Hm).
+ destruct IG as [G1 G2 G3 G4 G5]; constructor; try assumption.
* intros m b ai Hb. pose proof (G1 m b ai Hb) as GO. destruct GO; constructor; rewrite ?MR2; try assumption.
-- apply KEYS. left. exact g_present.
-- intros Hml. destruct (g_nest Hml) as (p & i & ? & ? & ? & ? & ?). exists p, i. rewrite !MR2. auto 10.
* intros m1 m2 b1 b2 ai1 ai2 H1 H2. rewrite !MR2. eapply G3; eassumption.
* intros rid r Hr Hk Ho. destruct (G4 rid r Hr Hk Ho) as (m & Hm & Hml). exists m. rewrite MR2. auto.
+ destruct IS as [S1 S2 S3 S4 S5 S6]; constructor; try assumption.
* intros s m i Hs. rewrite !MR2. exact (S1 s m i Hs).
* intros b m i Hb Hi. rewrite MR2 in Hi |- *. exact (S2 b m i Hb Hi).
* intros b m ai i Hb Hi. rewrite MR2 in Hi. rewrite !MR2. exact (S3 b m ai i Hb Hi).
* intros kk Hk. destruct (S6 kk Hk) as (m & i & ? & ?). exists m, i. rewrite MR2. auto.
+ apply (inv_SH_view st st2); try reflexivity; try (intros; rewrite MR2; reflexivity). exact ISH.
- split; [constructor; cbn; auto; first [reflexivity| lia]|].
intros Hin. pose proof (proj1 (im_idle _ _ _ IM _ Hin)) as E. rewrite ABS in E. discriminate.
Qed.
End TAKE.

Definition adv (st : mstate) (p : aptr) : mstate :=
upd_ctx (fun c => set_avail_meta_areas (Some (aadd p 4096)) (set_avail_meta_area_count (c_avail_meta_area_count c - 1) c)) st.

Definition carve_rest (s : mstate) (p : aptr) : mstate :=
let st2 := match c_meta_area_tail (ctx s) with
| Some tl => set_areas (<[tl := match (s_areas s) !! tl with
| Some a => mkArea (a_check a) (Some p) (a_nslots a)
| None => mkArea 0 (Some p) 0 end]> (s_areas s)) s
| None => upd_ctx (set_meta_area_head (Some p)) s
end in
let st3 := upd_ctx (set_meta_area_tail (Some p)) st2 in
let old := default (mkArea 0 None 0) ((s_areas st3) !! p) in
let st4 := set_areas (<[p := mkArea (c_secret (ctx st3)) (a_next old) NSLOTS]> (s_areas st3)) st3 in
upd_ctx (fun c => set_avail_meta (Some (aadd p AREA_HDR)) (set_avail_meta_count NSLOTS c)) st4.

#[using="Type"] Lemma am_carve_eq {T} st p (k : mstate -> optr -> M T) bail : am_carve st p k bail = am_take (carve_rest (adv st p) p) k bail.
Proof. reflexivity. Qed.

Section CARVE.
Variables (X : extras) (s : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (p : aptr).
Hypothesis INV : INVL X s L BL LS.
Hypothesis HP : c_avail_meta_areas (s_ctx s) = Some (aadd p 4096).
Hypothesis NA : s_areas s !! p = None.
Hypothesis NM : forall k, 0 <= k < NSLOTS -> s_metas s !! mslot p k = None.
Hypothesis PG : PGSZ <= snd p.
Hypothesis PM : snd p mod PGSZ = 0.
Hypothesis INIT : c_init_done (s_ctx s) = 1.
Let s' := carve_rest s p.

Definition cr_areas : gmap aptr area :=
match c_meta_area_tail (ctx s) with
| Some tl => <[p := mkArea (c_secret (ctx s)) None NSLOTS]>
(<[tl := match (s_areas s) !! tl with Some a => mkArea (a_check a) (Some p) (a_nslots a) | None => mkArea 0 (Some p) 0 end]> (s_areas s))
| None => <[p := mkArea (c_secret (ctx s)) None NSLOTS]> (s_areas s)
end.
Definition cr_head : optr := match c_meta_area_tail (ctx s) with Some _ => c_meta_area_head (ctx s) | None => Some p end.

#[using="RC__ X L BL LS INV NA"] Lemma tail_not_p tl : c_meta_area_tail (ctx s) = Some tl -> tl <> p.
Proof. intros Ht ->. apply (ia_tail _ (proj1 (proj2 INV)) p Ht). exact NA. Qed.

#[using="RC__ X L BL LS INV NA"] Lemma cr_shape :
s_areas s' = cr_areas /\ c_meta_area_head (s_ctx s') = cr_head /\ c_meta_area_tail (s_ctx s') = Some p
/\ c_avail_meta (s_ctx s') = Some (aadd p AREA_HDR) /\ c_avail_meta_count (s_ctx s') = NSLOTS
/\ s_regions s' = s_regions s /\ s_metas s' = s_metas s /\ s_groups s' = s_groups s /\ s_slots s' = s_slots s
/\ s_shadow s' = s_shadow s /\ s_tick s' = s_tick s /\ s_next_rid s' = s_next_rid s /\ s_secret s' = s_secret s /\ s_reserved s' = s_reserved s
/\ c_avail_meta_areas (s_ctx s') = c_avail_meta_areas (s_ctx s) /\ c_avail_meta_area_count (s_ctx s') = c_avail_meta_area_count (s_ctx s)
/\ c_secret (s_ctx s') = c_secret (s_ctx s) /\ c_init_done (s_ctx s') = c_init_done (s_ctx s)
/\ c_active (s_ctx s') = c_active (s_ctx s) /\ c_usage (s_ctx s') = c_usage (s_ctx s) /\ c_free_meta_head (s_ctx s') = c_free_meta_head (s_ctx s)
/\ c_meta_alloc_shift (s_ctx s') = c_meta_alloc_shift (s_ctx s) /\ c_brk (s_ctx s') = c_brk (s_ctx s)
/\ c_mmap_counter (s_ctx s') = c_mmap_counter (s_ctx s) /\ c_seq (s_ctx s') = c_seq (s_ctx s)
/\ c_bounces (s_ctx s') = c_bounces (s_ctx s) /\ c_unmap_seq (s_ctx s') = c_unmap_seq (s_ctx s).
Proof.
unfold s', carve_rest, cr_areas, cr_head, ctx. destruct (c_meta_area_tail (s_ctx s)) as [tl|] eqn:ET; cbn -[lookup insert NSLOTS AREA_HDR].
- rewrite lookup_insert_ne by (intros E; exact (tail_not_p tl ET (eq_sym E)) || exact (tail_not_p tl ET E)). rewrite NA. cbn. repeat split; reflexivity.
- rewrite NA. cbn. repeat split; reflexivity.
Qed.

#[using="Type"] Lemma cr_areas_lookup a : cr_areas !! a =
if aptr_eqb a p then Some (mkArea (c_secret (ctx s)) None NSLOTS)
else match c_meta_area_tail (ctx s) with
| Some tl => if aptr_eqb a tl then Some (match (s_areas s) !! tl with Some ar => mkArea (a_check ar) (Some p) (a_nslots ar) | None => mkArea 0 (Some p) 0 end)
else s_areas s !! a
| None => s_areas s !! a
end.
Proof.
unfold cr_areas. destruct (c_meta_area_tail (ctx s)) as [tl|] eqn:ET.
- destruct (aptr_eqb_spec a p) as [->|NE]; [rewrite lookup_insert_eq; reflexivity|]. rewrite lookup_insert_ne by congruence.
destruct (aptr_eqb_spec a tl) as [->|NE2]; [rewrite lookup_insert_eq; reflexivity|]. rewrite lookup_insert_ne by congruence. reflexivity.
- destruct (aptr_eqb_spec a p) as [->|NE]; [rewrite lookup_insert_eq; reflexivity|]. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

#[using="Type"] Lemma mslot0 : aadd p AREA_HDR = mslot p (NSLOTS - NSLOTS).
Proof. unfold mslot, aadd. f_equal. Qed.

#[using="INV HP NA NM PG PM INIT"] Theorem INVL_carve : INVL X s' L BL LS /\ AM_frame s s' /\ 0 < c_avail_meta_count (s_ctx s').
Proof.
destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
destruct cr_shape as (EA & EH & ET & EAM & EAC & ER & EM & EG & ESL & ESH & ETK & EN & ESE & ERS & ECA & ECC & EC1 & EC2 & EC3 & EC4 & EC5 & EC6 & EC7 & EC8 & EC9 & EC10 & EC11).
assert (FR : forall rid r, frontier s' rid r = frontier s rid r) by (intros; unfold frontier; rewrite ECA; reflexivity).
assert (MRE : forall x, MR s' x = MR s x) by (intros; unfold MR, get_meta_rec; rewrite EM; reflexivity).
destruct (ir_cursor _ _ _ IR) as (CU1 & CU2 & CU3). destruct (CU3 _ _ HP) as (rp & Hrp & Kp & _ & _ & Ep & _). cbn in Hrp, Ep.
assert (HE : forall h, get_head s' h = get_head s h) by (intros [sc|]; cbn [get_head]; unfold active, ctx; rewrite ?EC3, ?EC5; reflexivity).
split; [| split].
- split; [| split; [| split; [| split; [| split; [| split]]]]].
+ destruct IR; constructor; rewrite ?ER, ?EN, ?ERS, ?EG, ?ECA, ?ECC, ?EC6, ?EC7; try assumption.
* eapply Permutation_trans; [exact ir_metas|]. erewrite map_ext; [apply Permutation_refl|]. intros [rid r]; cbn. rewrite FR. reflexivity.
* intros rid r H1 H2. rewrite FR. exact (ir_metalen rid r H1 H2).
* intros rid r H1 H2. rewrite FR. exact (ir_brkfront rid r H1 H2).
+ destruct IA; constructor; rewrite ?ER, ?EA, ?EH, ?ET, ?EAM, ?EAC, ?EM, ?ESE, ?EC1, ?EC2, ?EC3, ?EC4, ?EC8, ?EC9, ?EC10, ?EC11; try assumption.
* destruct ia_secret as [S0 [[I0 _]|S1]]; [exfalso; rewrite INIT in I0; discriminate|]. split; [exact S0| right; exact S1].
* intros a ar. rewrite cr_areas_lookup. destruct (aptr_eqb_spec a p) as [->|NEp].
-- intros E. inversion E. subst ar. cbn. split; [| split; [reflexivity| split; [reflexivity| intros a' H; discriminate]]].
exists rp. rewrite FR. unfold frontier. rewrite HP. cbn. rewrite N.eqb_refl. split; [exact Hrp|]. split; [exact Kp|]. split; [exact PM|]. split; [exact PG|]. unfold PGSZ. lia.
-- assert (OLD : forall ar0, s_areas s !! a = Some ar0 -> (exists r, s_regions s !! fst a = Some r /\ is_metakind r /\ snd a mod PGSZ = 0 /\ PGSZ <= snd a /\ snd a + PGSZ <= frontier s' (fst a) r)
/\ a_check ar0 = c_secret (s_ctx s) /\ a_nslots ar0 = NSLOTS /\ (forall a', a_next ar0 = Some a' -> cr_areas !! a' <> None)).
{ intros ar0 H0. destruct (ia_areas a ar0 H0) as ((r & Hr & K & M & P & F) & C & NS & NX). split; [exists r; rewrite FR; auto 10|]. split; [exact C|]. split; [exact NS|].
intros a' Ha'. rewrite cr_areas_lookup. destruct (aptr_eqb a' p); [discriminate|].
destruct (c_meta_area_tail (ctx s)) as [tl|]; [destruct (aptr_eqb a' tl); [discriminate|]|]; exact (NX a' Ha'). }
destruct (c_meta_area_tail (ctx s)) as [tl|] eqn:ETL.
++ destruct (aptr_eqb_spec a tl) as [->|NEt].
** destruct (s_areas s !! tl) as [ar0|] eqn:E0; [| exfalso; exact (ia_tail tl ETL E0)].
intros E. inversion E. subst ar. cbn. destruct (OLD ar0 E0) as (R1 & C & NS & _). split; [exact R1|]. split; [exact C|]. split; [exact NS|].
intros a' Ha'. inversion Ha'. subst a'. rewrite cr_areas_lookup, aptr_eqb_refl. discriminate.
** intros H0. exact (OLD ar H0).
++ intros H0. exact (OLD ar H0).
* intros h Hh. rewrite cr_areas_lookup. destruct (aptr_eqb_spec h p) as [->|NEhp]; [discriminate|].
unfold cr_head in Hh. destruct (c_meta_area_tail (ctx s)) as [tl|] eqn:ETL.
-- destruct (aptr_eqb h tl); [discriminate|]. exact (ia_head h Hh).
-- inversion Hh. congruence.
* intros t Ht. inversion Ht. subst t. rewrite cr_areas_lookup, aptr_eqb_refl. discriminate.
* intros H. discriminate.
* intros m mr Hm. destruct (ia_metas m mr Hm) as (a & ar & k & Ha & Hk & Em). exists a.
rewrite cr_areas_lookup. destruct (aptr_eqb_spec a p) as [->|NEp]; [rewrite NA in Ha; discriminate|].
destruct (c_meta_area_tail (ctx s)) as [tl|]; [destruct (aptr_eqb a tl); [eexists _, k; eauto| exists ar, k; auto]| exists ar, k; auto].
* split; [unfold NSLOTS; lia|]. intros _. exists p. split; [reflexivity|]. split; [rewrite mslot0; reflexivity|].
intros k Hk. apply NM. unfold NSLOTS in *. lia.
* intros q Hq. inversion Hq. subst q. cbn. exists rp. auto.
* intros sc Hsc. unfold usage, ctx. rewrite EC4. fold (ctx s). fold (usage s sc). rewrite (ia_usage sc Hsc). symmetry.
apply (gcnt_ext s s'); [exact EG| exact EM].
+ apply (inv_M_ext X s s'); [exact EM| exact EG| exact IM].
+ apply (inv_L_ext s s'); [exact EM| exact EG| exact HE| exact IL].
+ destruct IG as [G1 G2 G3 G4 G5]; constructor; rewrite ?EG, ?ER.
* intros m b ai Hb. apply (group_ok_ext X s s'); [exact EM| exact ESL| intros; rewrite ER; assumption| exact (G1 m b ai Hb)].
* exact G2.
* intros m1 m2 b1 b2 ai1 ai2 H1 H2. rewrite !MRE. eapply G3; eassumption.
* intros rid r Hr Hk Ho. destruct (G4 rid r Hr Hk Ho) as (m & Hm & Hml). exists m. rewrite (hosts_ext s s' EG), MRE. auto.
* exact G5.
+ apply (inv_S_ext X s s' BL); [exact EM| exact EG| exact ESL| exact IS].
+ apply (inv_SH_view s s'); auto; intros; rewrite MRE; reflexivity.
- constructor; rewrite ?EG, ?ESL, ?ESH, ?ETK, ?EC8, ?EC9, ?EC10, ?EN, ?EC2; auto; try reflexivity.
+ intros sc. unfold active, ctx. rewrite EC3. reflexivity.
+ intros sc. unfold usage, ctx. rewrite EC4. reflexivity.
+ intros rid r H _. rewrite ER. exact H.
- rewrite EAC. unfold NSLOTS. lia.
Qed.
End CARVE.

#[using="Type"] Lemma above_frontier X st L BL LS rid r (p : aptr) :
INVL X st L BL LS -> s_regions st !! rid = Some r -> fst p = rid -> frontier st rid r <= snd p ->
s_areas st !! p = None /\ forall k, 0 <= k < NSLOTS -> s_metas st !! mslot p k = None.
Proof.
intros INV Hr Hf Hfr. pose proof (proj1 (proj2 INV)) as IA. split.
- destruct (s_areas st !! p) as [ar|] eqn:E; [| reflexivity]. exfalso.
destruct (ia_areas _ IA _ _ E) as ((r' & Hr' & _ & _ & _ & F) & _). rewrite Hf, Hr in Hr'. inversion Hr'. subst r'. rewrite Hf in F. unfold PGSZ in F. lia.
- intros k Hk. destruct (s_metas st !! mslot p k) as [mr|] eqn:E; [| reflexivity]. exfalso.
destruct (ia_metas _ IA _ _ E) as (a & ar & k' & Ha & Hk' & Em).
destruct (ia_areas _ IA _ _ Ha) as ((r' & Hr' & _ & _ & _ & F) & _).
unfold mslot, aadd in Em. inversion Em. rewrite Hf in H0. rewrite <- H0, Hr in Hr'. inversion Hr'. subst r'. rewrite <- H0 in F.
unfold AREA_HDR, META_SIZE, NSLOTS, PGSZ in *. lia.
Qed.

Section META_ADV.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (rid : N) (off : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hcur : c_avail_meta_areas (s_ctx st) = Some (rid, off).
Hypothesis Hcnt : 0 < c_avail_meta_area_count (s_ctx st).
Let p : aptr := (rid, off).
Let a : Z := conc st p.
Let st' := adv st p.
Let L' := Qfya.set_metas (map (bump_meta a) (ld_metas L)) L.

#[using="X L BL LS INV Hcur Hcnt p a"] Lemma ma_region : exists r, s_regions st !! rid = Some r /\ r_kind r = RKMeta /\ PGSZ <= off /\ off mod PGSZ = 0
/\ off + c_avail_meta_area_count (s_ctx st) * PGSZ = r_len r /\ r_len r mod PGSZ = 0 /\ 0 < r_base r
/\ r_base r + r_len r <= alloc_ceiling.
Proof.
destruct (ir_cursor _ _ _ (proj1 INV)) as (C1 & C2 & C3). destruct (C3 _ _ Hcur) as (r & Hr & K & P1 & P2 & P3 & P4).
pose proof (ir_shape _ _ _ (proj1 INV) _ _ Hr) as (S1 & S2 & S3 & S4 & S5 & S6). destruct (S6 K) as [S7 S8].
exists r. repeat split; auto.
pose proof (round_up_ge (r_len r)). lia.
Qed.

#[using="Hcur"] Lemma ma_frontier q rq : frontier st q rq = if (rid =? q)%N then off else r_len rq.
Proof. unfold frontier. rewrite Hcur. reflexivity. Qed.
#[using="Type"] Lemma ma_frontier' q rq : frontier st' q rq = if (rid =? q)%N then off + 4096 else r_len rq.
Proof. unfold frontier, st', adv. cbn. reflexivity. Qed.

#[using="RC__ X BL LS INV Hcur Hcnt"] Lemma ma_event_pre : event_pre L (EMprotect a PGSZ PROT_RW).
Proof.
destruct ma_region as (r & Hr & K & P1 & P2 & P3 & P4 & P5 & P6).
cbn. split; [exact (brk_quiet_of _ _ _ (proj1 INV))|]. split; [reflexivity|]. split; [reflexivity|].
exists (r_base r), (r_len r), (frontier st rid r / PGSZ - 1).
split.
- pose proof (ir_metas _ _ _ (proj1 INV)) as P. eapply Permutation_in; [apply Permutation_sym; exact P|].
apply in_map_iff. exists (rid, r). split; [reflexivity|]. apply filter_In. split; [apply In_map_to_list_regions; exact Hr| cbn; rewrite K; reflexivity].
- rewrite ma_frontier, N.eqb_refl. unfold a, conc, get_region, p. cbn [fst snd]. rewrite Hr.
unfold PGSZ in *. pose proof (round_up_ge (r_len r)).
pose proof (Z.div_mod off 4096 ltac:(lia)) as DM. rewrite P2 in DM. set (q := off / 4096) in *. clearbody q. nia.
Qed.

#[using="INV Hcur Hcnt"] Theorem INVL_meta_adv : INVL X st' L' BL LS
/\ c_avail_meta_areas (s_ctx st') = Some (aadd p 4096)
/\ s_areas st' !! p = None /\ (forall k, 0 <= k < NSLOTS -> s_metas st' !! mslot p k = None)
/\ PGSZ <= snd p /\ snd p mod PGSZ = 0 /\ c_init_done (s_ctx st') = c_init_done (s_ctx st)
/\ AM_frame st st'.
Proof.
destruct ma_region as (r & Hr & K & P1 & P2 & P3 & P4 & P5 & P6).
destruct (above_frontier X st L BL LS rid r p INV Hr eq_refl ltac:(rewrite ma_frontier, N.eqb_refl; cbn; lia)) as [NA NM].
pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
split; [| split; [reflexivity| split; [exact NA| split; [exact NM| split; [cbn; lia| split; [exact P2| split; [reflexivity|]]]]]]].
2:{ constructor; cbn; auto; first [reflexivity| lia]. }
split; [| split; [| split; [| split; [| split; [| split]]]]].
- assert (Rg : s_regions st' = s_regions st) by reflexivity. assert (Rn : s_next_rid st' = s_next_rid st) by reflexivity.
assert (Rv : s_reserved st' = s_reserved st) by reflexivity. assert (Rgr : s_groups st' = s_groups st) by reflexivity.
assert (Csh : c_meta_alloc_shift (s_ctx st') = c_meta_alloc_shift (s_ctx st)) by reflexivity.
assert (Cbrk : c_brk (s_ctx st') = c_brk (s_ctx st)) by reflexivity.
assert (Cam : c_avail_meta_areas (s_ctx st') = Some (aadd p 4096)) by reflexivity.
assert (Cac : c_avail_meta_area_count (s_ctx st') = c_avail_meta_area_count (s_ctx st) - 1) by reflexivity.
unfold L'. destruct IR; constructor; cbn [Qfya.ld_metas Qfya.ld_groups Qfya.ld_resv Qfya.ld_brkreg Qfya.ld_brk Qfya.ld_live Qfya.set_metas];
rewrite ?Rg, ?Rn, ?Rv, ?Rgr, ?Csh, ?Cbrk, ?Cam, ?Cac; try assumption.
+
eapply Permutation_trans; [apply Permutation_map; exact ir_metas|]. rewrite map_map.
erewrite map_ext_in; [apply Permutation_refl|]. intros [q rq] Hin. apply filter_In in Hin as [Hin Hk]. cbn in Hk |- *.
apply In_map_to_list_regions in Hin. destruct (r_kind rq) eqn:Ekq; try discriminate.
rewrite ma_frontier.
pose proof (ir_shape q rq Hin) as (S1 & S2 & S3 & S4 & S5 & S6). destruct (S6 ltac:(right; exact Ekq)) as [S7 S8].
destruct (N.eqb_spec rid q) as [<-|NE].
* rewrite Hr in Hin. inversion Hin. subst rq.
replace (r_base r + (1 + (off / PGSZ - 1)) * PGSZ) with a.
2:{ unfold a, conc, get_region, p. cbn. rewrite Hr. unfold PGSZ in *. pose proof (Z.div_mod off 4096 ltac:(lia)). lia. }
rewrite Z.eqb_refl. f_equal. unfold PGSZ in *.
pose proof (Z.div_mod off 4096 ltac:(lia)). rewrite P2 in H.
replace (off + 4096) with ((off / 4096 + 1) * 4096) by lia. rewrite Z.div_mul by lia. lia.
* destruct (Z.eqb_spec (r_base rq + (1 + (r_len rq / PGSZ - 1)) * PGSZ) a) as [E|NE2]; [| reflexivity]. exfalso.
unfold a, conc, get_region, p in E. cbn in E. rewrite Hr in E.
pose proof (Z.div_mod (r_len rq) PGSZ ltac:(unfold PGSZ; lia)) as DM. rewrite S7 in DM.
pose proof (ir_disj q rid rq r Hin Hr ltac:(congruence)) as D. unfold region_live_range in D. rewrite Ekq, K in D.
pose proof (round_up_ge (r_len rq)). pose proof (round_up_ge (r_len r)). unfold PGSZ in *. nia.
+ intros q rq Hq Kq. rewrite ma_frontier'. pose proof (ir_metalen q rq Hq Kq) as (J & F1 & F2). rewrite ma_frontier in F1, F2.
split; [exact J|]. destruct (N.eqb_spec rid q) as [<-|NE]; [| auto].
rewrite Hr in Hq. inversion Hq. subst rq. unfold PGSZ in *. split; [lia|].
rewrite <- Zplus_mod_idemp_l, P2. reflexivity.
+ intros q rq Hq Kq. rewrite ma_frontier'. destruct (N.eqb_spec rid q) as [<-|NE]; [rewrite Hr in Hq; inversion Hq; subst rq; rewrite Kq in K; discriminate|].
pose proof (ir_brkfront q rq Hq Kq) as F. rewrite ma_frontier in F. destruct (N.eqb_spec rid q); [congruence| exact F].
+ split; [lia|]. split; [intros _; discriminate|]. intros q o E. inversion E. subst q o. exists r.
split; [exact Hr|]. split; [right; exact K|]. split; [lia|]. split; [unfold PGSZ in *; rewrite <- Zplus_mod_idemp_l, P2; reflexivity|].
split; [unfold PGSZ in *; lia| intros _; exact K].
- destruct IA; constructor; cbn -[frontier PGSZ]; try assumption.
intros a0 ar Ha. destruct (ia_areas a0 ar Ha) as ((rq & Hq & Kq & M & P & F) & rest). split; [| exact rest].
exists rq. split; [exact Hq|]. split; [exact Kq|]. split; [exact M|]. split; [exact P|].
rewrite ma_frontier'. rewrite ma_frontier in F. destruct (N.eqb_spec rid (fst a0)); lia.
- apply (inv_M_ext X st st'); [reflexivity| reflexivity| exact IM].
- apply (inv_L_ext st st'); [reflexivity| reflexivity| intros h; destruct h; reflexivity| exact IL].
- destruct IG as [G1 G2 G3 G4 G5]; constructor; try assumption.
intros m b ai Hb. apply (group_ok_ext X st st'); [reflexivity| reflexivity| auto| exact (G1 m b ai Hb)].
- apply (inv_S_ext X st st' BL); [reflexivity| reflexivity| reflexivity| exact IS].
- apply (inv_SH_view st st'); try reflexivity. exact ISH.
Qed.
End META_ADV.

#[using="Type"] Lemma frontier_full X st L rid r :
inv_R X st L -> c_avail_meta_area_count (s_ctx st) = 0 -> s_regions st !! rid = Some r -> frontier st rid r = r_len r.
Proof.
intros IR Hc Hr. unfold frontier. destruct (c_avail_meta_areas (s_ctx st)) as [[q off]|] eqn:E; [| reflexivity].
destruct (N.eqb_spec q rid) as [->|NE]; [| reflexivity].
destruct (ir_cursor _ _ _ IR) as (_ & _ & C3). destruct (C3 _ _ E) as (r' & Hr' & _ & _ & _ & Eq & _).
rewrite Hr in Hr'. inversion Hr'. subst r'. rewrite Hc in Eq. lia.
Qed.

Section NEW_META.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (r : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hcnt : c_avail_meta_area_count (s_ctx st) = 0.
Let n : Z := Z.shiftl 2 (c_meta_alloc_shift (s_ctx st)).
Let len : Z := n * PGSZ.
Hypothesis HOK : mmap_answer_ok (live_ranges st) len r = true.
Hypothesis NERR : is_err r = false.
Let rid := s_next_rid st.
Let st1 := fst (new_region RKMeta r len st).
Let st2 := upd_ctx (fun c => set_meta_alloc_shift (c_meta_alloc_shift c + 1)
(set_avail_meta_area_count (n - 1) (set_avail_meta_areas (Some (rid, PGSZ)) c))) st1.
Let L' := Qfya.set_metas ((r, len, 0) :: ld_metas L) L.

#[using="RC__ X L BL LS INV len rid"] Lemma nm_n : n = 2 ^ (c_meta_alloc_shift (s_ctx st) + 1) /\ 2 <= n.
Proof.
pose proof (proj1 (ir_shift _ _ _ (proj1 INV))) as S0. unfold n. rewrite Z.shiftl_mul_pow2 by exact S0.
rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2. split; [lia|].
pose proof (Z.pow_pos_nonneg 2 (c_meta_alloc_shift (s_ctx st))). lia.
Qed.

#[using="RC__ X L BL LS INV rid"] Lemma nm_len : 0 < len < LEN_MAX.
Proof.
destruct nm_n as [En N2]. unfold len. split; [unfold PGSZ; lia|].
destruct (ir_shift _ _ _ (proj1 INV)) as [S0 [S1|(q & rq & Hq & K & E)]].
- unfold n. rewrite S1. change (Z.shiftl 2 0 * PGSZ) with 8192. unfold LEN_MAX. lia.
- pose proof (ir_shape _ _ _ (proj1 INV) _ _ Hq) as (A1 & _ & _ & _ & A5 & _). pose proof (round_up_ge (r_len rq)).
rewrite En. rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2. rewrite E in *. unfold alloc_ceiling, LEN_MAX, PGSZ in *. nia.
Qed.

#[using="RC__ X L BL LS INV n len"] Lemma nm_fresh : s_regions st !! rid = None.
Proof.
destruct (s_regions st !! rid) as [r0|] eqn:E; [| reflexivity]. exfalso.
pose proof (ir_ids _ _ _ (proj1 INV) _ _ E) as H. unfold rid in H. lia.
Qed.
#[using="Type"] Lemma nm_lookup q : s_regions st2 !! q = if (q =? rid)%N then Some (mkRegion RKMeta r len) else s_regions st !! q.
Proof. unfold st2, st1. cbn -[new_region]. apply lookup_new_region. Qed.
#[using="RC__ X L BL LS INV"] Lemma nm_keep q rq : s_regions st !! q = Some rq -> s_regions st2 !! q = Some rq.
Proof. intros H. rewrite nm_lookup. destruct (N.eqb_spec q rid) as [->|]; [rewrite nm_fresh in H; discriminate| exact H]. Qed.
#[using="Type"] Lemma nm_some q rq : s_regions st2 !! q = Some rq -> (q = rid /\ rq = mkRegion RKMeta r len) \/ (q <> rid /\ s_regions st !! q = Some rq).
Proof. rewrite nm_lookup. destruct (N.eqb_spec q rid) as [->|NE]; [intros H; inversion H; auto| auto]. Qed.
#[using="Type"] Lemma nm_frontier q rq : frontier st2 q rq = if (rid =? q)%N then PGSZ else r_len rq.
Proof. reflexivity. Qed.
#[using="RC__ X L BL LS INV Hcnt"] Lemma nm_frontier_old q rq : s_regions st !! q = Some rq -> frontier st q rq = r_len rq.
Proof. intros Hq. exact (frontier_full X st L q rq (proj1 INV) Hcnt Hq). Qed.

#[using="RC__ X BL LS INV rid"] Lemma nm_event_pre : event_pre L (EMmap 0 len PROT_NONE MAPF).
Proof. left. split; [exact (brk_quiet_of _ _ _ (proj1 INV))|]. split; [reflexivity|]. split; [reflexivity|]. split; [left; reflexivity| exact nm_len]. Qed.

#[using="INV Hcnt HOK NERR"] Theorem INVL_new_meta : INVL X st2 L' BL LS /\ 0 < c_avail_meta_area_count (s_ctx st2)
/\ c_init_done (s_ctx st2) = c_init_done (s_ctx st) /\ AM_frame st st2.
Proof.
destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
destruct (mmap_ok_facts _ _ _ HOK NERR) as (R0 & RPG & RCEIL & RFREE).
destruct nm_n as [En N2]. pose proof nm_len as [L0 L1].
assert (LPG : len mod PGSZ = 0) by (unfold len; apply Z_mod_mult).
assert (RU : round_up_pg len = len).
{ unfold round_up_pg. unfold PGSZ in *. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia.
rewrite Z.mod_opp_l_z; [lia| lia| ]. change (2 ^ 12) with 4096. exact LPG. }
split; [| split; [cbn; lia| split; [reflexivity| constructor; cbn; auto; try reflexivity; [intros q rq H _; apply nm_keep; exact H| unfold rid; lia]]]].
split; [| split; [| split; [| split; [| split; [| split]]]]].
- unfold L'. destruct IR; constructor; cbn [Qfya.ld_metas Qfya.ld_groups Qfya.ld_resv Qfya.ld_brkreg Qfya.ld_brk Qfya.ld_live Qfya.set_metas].
+ intros q rq Hq. unfold st2, st1. cbn -[new_region]. rewrite s_next_rid_new_region. apply nm_some in Hq as [[-> _]|[_ Hq]]; [unfold rid; lia|]. pose proof (ir_ids q rq Hq). lia.
+ intros q rq Hq. apply nm_some in Hq as [[-> ->]|[_ Hq]]; [| exact (ir_shape q rq Hq)]. cbn.
rewrite RU. rewrite RU in RCEIL. split; [lia|]. split; [exact RPG|]. split; [lia|]. split; [lia|]. split; [exact RCEIL|]. intros _. split; [exact LPG|]. unfold len, PGSZ in *. nia.
+ intros q1 q2 r1 r2 H1 H2 NE.
apply nm_some in H1 as [[-> ->]|[N1 H1]]; apply nm_some in H2 as [[-> ->]|[N2' H2]]; [congruence| | | exact (ir_disj q1 q2 r1 r2 H1 H2 NE)].
* cbn. rewrite RU in RFREE |- *. pose proof (ranges_free_regions st _ _ q2 r2 RFREE H2) as D. destruct (region_live_range r2) as [b2 l2]. lia.
* pose proof (ranges_free_regions st _ _ q1 r1 RFREE H1) as D. rewrite RU in D. destruct (region_live_range r1) as [b1 l1]. cbn. rewrite RU. lia.
+ exact ir_resv.
+ eapply Permutation_trans; [exact ir_groups|].
change (s_regions st2) with (<[rid := mkRegion RKMeta r len]> (s_regions st)).
eapply Permutation_trans; [| apply Permutation_map; apply Permutation_sym; apply (regions_insert_perm st rid _ _ nm_fresh)].
cbn. apply Permutation_refl.
+ eapply Permutation_trans; [apply perm_skip; exact ir_metas|].
change (s_regions st2) with (<[rid := mkRegion RKMeta r len]> (s_regions st)).
eapply Permutation_trans; [| apply Permutation_map; apply Permutation_sym; apply (regions_insert_perm st rid _ _ nm_fresh)].
cbn -[frontier PGSZ Z.div Z.sub]. rewrite nm_frontier, N.eqb_refl. replace (PGSZ / PGSZ - 1) with 0 by reflexivity. apply perm_skip.
erewrite map_ext_in; [apply Permutation_refl|]. intros [q rq] Hin. apply filter_In in Hin as [Hin _]. apply In_map_to_list_regions in Hin. cbn.
rewrite (nm_frontier_old q rq Hin). destruct (N.eqb_spec rid q) as [<-|]; [rewrite nm_fresh in Hin; discriminate| reflexivity].
+ intros q rq Hq K. rewrite nm_frontier. apply nm_some in Hq as [[-> ->]|[NE Hq]].
* rewrite N.eqb_refl. cbn. split; [exists (c_meta_alloc_shift (s_ctx st) + 1); split; [pose proof (proj1 ir_shift); lia| unfold len; rewrite En; reflexivity]|].
unfold len, PGSZ in *. split; [nia| reflexivity].
* destruct (N.eqb_spec rid q) as [<-|]; [congruence|]. pose proof (ir_metalen q rq Hq K) as (J & F1 & F2). rewrite (nm_frontier_old q rq Hq) in F1, F2. auto.
+ intros q rq Hq K. rewrite nm_frontier. apply nm_some in Hq as [[-> ->]|[NE Hq]]; [discriminate|].
destruct (N.eqb_spec rid q) as [<-|]; [congruence| reflexivity].
+ cbn. split; [pose proof (proj1 ir_shift); lia|]. right. exists rid, (mkRegion RKMeta r len). split; [rewrite nm_lookup, N.eqb_refl; reflexivity|].
split; [reflexivity|]. cbn. unfold len. rewrite En. reflexivity.
+ intros b l. rewrite ir_brkreg. split; intros (q & rq & Hq & K & E1 & E2); exists q, rq.
* split; [apply nm_keep; exact Hq| auto].
* apply nm_some in Hq as [[-> ->]|[_ Hq]]; [discriminate| auto].
+ intros q1 q2 r1 r2 H1 H2 K1 K2. apply nm_some in H1 as [[-> ->]|[_ H1]]; [discriminate|]. apply nm_some in H2 as [[-> ->]|[_ H2]]; [discriminate|].
exact (ir_brk1 q1 q2 r1 r2 H1 H2 K1 K2).
+ revert ir_brk. change (c_brk (s_ctx st2)) with (c_brk (s_ctx st)). destruct (c_brk (s_ctx st)) as [| |brid boff]; intros IBK.
* destruct IBK as [B NB]. split; [exact B|]. intros q rq Hq. apply nm_some in Hq as [[-> ->]|[_ Hq]]; [discriminate| exact (NB q rq Hq)].
* exact IBK.
* destruct IBK as [B (rq & Hq & K & E)]. split; [exact B|]. exists rq. split; [apply nm_keep; exact Hq| auto].
+ cbn. split; [lia|]. split; [intros _; discriminate|]. intros q off E. inversion E. subst q off.
exists (mkRegion RKMeta r len). split; [rewrite nm_lookup, N.eqb_refl; reflexivity|]. cbn. split; [right; reflexivity|].
split; [lia|]. split; [reflexivity|]. split; [unfold len; lia| reflexivity].
+ intros q Hq. destruct (ir_orph q Hq) as (rq & Hrq & K & NG). exists rq. split; [apply nm_keep; exact Hrq| auto].
- destruct IA; constructor; try assumption.
+ intros a ar Ha. destruct (ia_areas a ar Ha) as ((rq & Hq & K & M & P & F) & rest). split; [| exact rest].
exists rq. rewrite nm_frontier. split; [apply nm_keep; exact Hq|]. split; [exact K|]. split; [exact M|]. split; [exact P|].
rewrite (nm_frontier_old _ _ Hq) in F. destruct (N.eqb_spec rid (fst a)) as [E|]; [| exact F]. exfalso. rewrite <- E, nm_fresh in Hq. discriminate.
+ intros q Hq. destruct (ia_availptr q Hq) as (rq & Hrq & K). exists rq. split; [apply nm_keep; exact Hrq| exact K].
- apply (inv_M_ext X st st2); [reflexivity| reflexivity| exact IM].
- apply (inv_L_ext st st2); [reflexivity| reflexivity| intros h; destruct h; reflexivity| exact IL].
- destruct IG as [G1 G2 G3 G4 G5]. constructor.
+ intros m b ai Hb. apply (group_ok_ext X st st2); [reflexivity| reflexivity| intros q rq Hq K E; apply nm_keep; exact Hq| exact (G1 m b ai Hb)].
+ exact G2.
+ exact G3.
+ intros q rq Hq K Ho. apply nm_some in Hq as [[-> ->]|[NE Hq]]; [discriminate|]. exact (G4 q rq Hq K Ho).
+ intros b h Hb. destruct (G5 b h Hb) as (rq & Hq & K). exists rq. split; [apply nm_keep; exact Hq| exact K].
- apply (inv_S_ext X st st2 BL); [reflexivity| reflexivity| reflexivity| exact IS].
- destruct ISH as [D1 D2 D3 D4 D5 D6]; constructor; try assumption.
intros q sh Hq. destruct (D1 q sh Hq) as (rq & Hrq & K). exists rq. split; [apply nm_keep; exact Hrq| exact K].
Qed.
End NEW_META.

#[using="Type"] Lemma INVL_brk_dead X st L L' BL LS :
INVL X st L BL LS ->
ld_resv L' = ld_resv L -> ld_groups L' = ld_groups L -> ld_metas L' = ld_metas L -> ld_brkreg L' = ld_brkreg L ->
ld_brk L' = BPDead ->
INVL X (upd_ctx (set_brk BrkDead) st) L' BL LS /\ AM_frame st (upd_ctx (set_brk BrkDead) st).
Proof.
intros INV E1 E2 E3 E4 E5. destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
set (st' := upd_ctx (set_brk BrkDead) st).
assert (FR : forall q rq, frontier st' q rq = frontier st q rq) by reflexivity.
split; [| constructor; cbn; auto; first [reflexivity| lia]].
split; [| split; [| split; [| split; [| split; [| split]]]]].
- destruct IR; constructor; cbn -[frontier]; rewrite ?E1, ?E2, ?E3, ?E4, ?E5; try assumption.
all: try reflexivity.
all: try (intros q rq H1 H2; rewrite FR; first [exact (ir_metalen q rq H1 H2)| exact (ir_brkfront q rq H1 H2)]).
all: try (eapply Permutation_trans; [exact ir_metas|]; erewrite map_ext; [apply Permutation_refl|]; intros [q rq]; cbn -[frontier]; rewrite FR; reflexivity).
- destruct IA; constructor; cbn -[frontier]; try assumption.
- apply (inv_M_ext X st st'); [reflexivity| reflexivity| exact IM].
- apply (inv_L_ext st st'); [reflexivity| reflexivity| intros h; destruct h; reflexivity| exact IL].
- destruct IG as [G1 G2 G3 G4 G5]; constructor; try assumption.
intros m b ai Hb. apply (group_ok_ext X st st'); [reflexivity| reflexivity| auto| exact (G1 m b ai Hb)].
- apply (inv_S_ext X st st' BL); [reflexivity| reflexivity| reflexivity| exact IS].
- apply (inv_SH_view st st'); try reflexivity. exact ISH.
Qed.

#[using="Type"] Lemma round_up_pg_mod x : round_up_pg x mod PGSZ = 0.
Proof.
unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096.
pose proof (Z.div_mod (-x) 4096 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (-x) 4096 ltac:(lia)) as B.
replace (x + (- x) mod 4096) with ((- ((- x) / 4096)) * 4096) by lia. apply Z_mod_mult.
Qed.
#[using="Type"] Lemma round_up_pg_id x : x mod PGSZ = 0 -> round_up_pg x = x.
Proof.
intros H. unfold round_up_pg. unfold PGSZ in *. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096.
pose proof (Z.div_mod x 4096 ltac:(lia)) as D. rewrite H in D.
replace (- x) with ((- (x / 4096)) * 4096) by lia. rewrite Z_mod_mult. lia.
Qed.

#[using="Type"] Lemma brk_pages_ok_facts st lo len :
brk_pages_ok st lo len = true -> 0 < lo /\ lo + len <= alloc_ceiling /\ ranges_free (live_ranges st) lo len = true.
Proof.
unfold brk_pages_ok. intros H. apply Bool.andb_true_iff in H as [H H3]. apply Bool.andb_true_iff in H as [H1 H2].
apply Z.ltb_lt in H1. apply Z.leb_le in H2. auto.
Qed.

#[using="Type"] Lemma regions_update_perm (st : mstate) rid r r' (F : N * region -> bool) :
s_regions st !! rid = Some r -> F (rid, r) = false -> F (rid, r') = false ->
Permutation (List.filter F (map_to_list (s_regions st))) (List.filter F (map_to_list (<[rid := r']> (s_regions st)))).
Proof.
intros H F1 F2.
eapply Permutation_trans; [apply perm_filter; apply Permutation_sym; apply (map_to_list_delete _ _ _ H)|].
eapply Permutation_trans; [| apply perm_filter; apply (map_to_list_delete _ rid r'); rewrite lookup_insert_eq; reflexivity].
cbn. rewrite F1, F2. rewrite delete_insert_eq. apply Permutation_refl.
Qed.

Section BRK_GROW.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (rid : N) (off : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hbrk : c_brk (s_ctx st) = BrkLive rid off.
Hypothesis Hcnt : c_avail_meta_area_count (s_ctx st) = 0.
Let old : Z := conc st (rid, off).
Hypothesis HOK : brk_pages_ok st old PGSZ = true.
Let st1 := upd_region rid (fun rg => mkRegion (r_kind rg) (r_base rg) (off + PGSZ)) st.
Let st2 := upd_ctx (fun c => set_avail_meta_area_count 1 (set_avail_meta_areas (Some (rid, off)) (set_brk (BrkLive rid (off + PGSZ)) c))) st1.
Let st3 := adv st2 (rid, off).

#[using="RC__ X BL LS INV Hbrk"] Lemma bg_region : exists r, s_regions st !! rid = Some r /\ r_kind r = RKBrk /\ r_len r = off /\ ld_brk L = BPLive
/\ ld_brkreg L = Some (r_base r, off) /\ 0 < r_base r /\ r_base r mod PGSZ = 0 /\ off mod PGSZ = 0 /\ 2 * PGSZ <= off
/\ old = r_base r + off.
Proof.
pose proof (ir_brk _ _ _ (proj1 INV)) as B. rewrite Hbrk in B. destruct B as [BP (r & Hr & K & E)].
pose proof (ir_shape _ _ _ (proj1 INV) _ _ Hr) as (S1 & S2 & S3 & S4 & S5 & S6). destruct (S6 ltac:(left; exact K)) as [S7 S8].
exists r. split; [exact Hr|]. split; [exact K|]. split; [exact E|]. split; [exact BP|].
split; [rewrite <- E; apply (proj2 (ir_brkreg _ _ _ (proj1 INV) (r_base r) (r_len r))); exists rid, r; auto|].
split; [exact S1|]. split; [exact S2|]. split; [rewrite <- E; exact S7|]. split; [rewrite <- E; exact S8|].
unfold old, conc, get_region. rewrite Hr. reflexivity.
Qed.

Let L' := Qfya.set_brkreg (Some (old - off, off + PGSZ)) L.

#[using="Type"] Lemma bg_lookup q : s_regions st3 !! q = if (q =? rid)%N then option_map (fun rg => mkRegion (r_kind rg) (r_base rg) (off + PGSZ)) (s_regions st !! rid) else s_regions st !! q.
Proof. unfold st3, adv, st2, st1. cbn -[upd_region]. apply lookup_upd_region. Qed.
#[using="Type"] Lemma bg_frontier q rq : frontier st3 q rq = if (rid =? q)%N then off + 4096 else r_len rq.
Proof. unfold frontier, st3, adv. cbn. reflexivity. Qed.
#[using="RC__ X L BL LS INV Hcnt"] Lemma bg_frontier_old q rq : s_regions st !! q = Some rq -> frontier st q rq = r_len rq.
Proof. intros Hq. exact (frontier_full X st L q rq (proj1 INV) Hcnt Hq). Qed.

#[using="RC__ X BL LS INV Hbrk"] Lemma bg_event_pre : event_pre L (EBrk (old + PGSZ)).
Proof.
destruct bg_region as (r & Hr & K & E & BP & BR & B0 & BM & OM & O2 & Eold).
right. right. exists (r_base r), off. split; [exact BP|]. split; [exact BR|]. lia.
Qed.

#[using="INV Hbrk Hcnt HOK"] Theorem INVL_brk_grow : INVL X st3 L' BL LS
/\ c_avail_meta_areas (s_ctx st3) = Some (aadd (rid, off) 4096)
/\ s_areas st3 !! (rid, off) = None /\ (forall k, 0 <= k < NSLOTS -> s_metas st3 !! mslot (rid, off) k = None)
/\ PGSZ <= off /\ off mod PGSZ = 0 /\ c_init_done (s_ctx st3) = c_init_done (s_ctx st) /\ AM_frame st st3.
Proof.
destruct bg_region as (r & Hr & K & E & BP & BR & B0 & BM & OM & O2 & Eold).
destruct (brk_pages_ok_facts _ _ _ HOK) as (P0 & PC & PF).
destruct (above_frontier X st L BL LS rid r (rid, off) INV Hr eq_refl ltac:(rewrite (bg_frontier_old _ _ Hr); cbn; lia)) as [NA NM].
pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
set (r' := mkRegion RKBrk (r_base r) (off + PGSZ)).
assert (LK : forall q, s_regions st3 !! q = if (q =? rid)%N then Some r' else s_regions st !! q).
{ intros q. rewrite bg_lookup. destruct (N.eqb_spec q rid) as [->|]; [rewrite Hr; cbn; rewrite K; reflexivity| reflexivity]. }
assert (KEEP : forall q rq, s_regions st !! q = Some rq -> q <> rid -> s_regions st3 !! q = Some rq).
{ intros q rq Hq NE. rewrite LK. destruct (N.eqb_spec q rid); [congruence| exact Hq]. }
assert (SOME : forall q rq, s_regions st3 !! q = Some rq -> (q = rid /\ rq = r') \/ (q <> rid /\ s_regions st !! q = Some rq)).
{ intros q rq. rewrite LK. destruct (N.eqb_spec q rid) as [->|NE]; [intros H; inversion H; auto| auto]. }
assert (KEEPG : forall q rq, s_regions st !! q = Some rq -> r_kind rq = RKGroup -> s_regions st3 !! q = Some rq).
{ intros q rq Hq Kq. apply KEEP; [exact Hq|]. intros ->. rewrite Hr in Hq. inversion Hq. subst. congruence. }
assert (KEEPM : forall q rq, s_regions st !! q = Some rq -> is_metakind rq -> exists rq', s_regions st3 !! q = Some rq' /\ is_metakind rq').
{ intros q rq Hq Kq. destruct (N.eq_dec q rid) as [->|NE]; [exists r'; rewrite LK, N.eqb_refl; split; [reflexivity| left; reflexivity]|].
exists rq. split; [apply KEEP; assumption| exact Kq]. }
assert (RU : round_up_pg (off + PGSZ) = off + PGSZ) by (apply round_up_pg_id; unfold PGSZ in *; rewrite <- Zplus_mod_idemp_l, OM; reflexivity).
assert (RUo : round_up_pg off = off) by (apply round_up_pg_id; exact OM).
assert (F3 : s_metas st3 = s_metas st /\ s_areas st3 = s_areas st /\ s_groups st3 = s_groups st /\ s_slots st3 = s_slots st
/\ s_shadow st3 = s_shadow st /\ s_tick st3 = s_tick st /\ s_next_rid st3 = s_next_rid st /\ s_secret st3 = s_secret st
/\ s_reserved st3 = s_reserved st /\ (forall h, get_head st3 h = get_head st h)
/\ c_usage (s_ctx st3) = c_usage (s_ctx st) /\ c_bounces (s_ctx st3) = c_bounces (s_ctx st) /\ c_seq (s_ctx st3) = c_seq (s_ctx st)
/\ c_mmap_counter (s_ctx st3) = c_mmap_counter (s_ctx st) /\ c_init_done (s_ctx st3) = c_init_done (s_ctx st)
/\ c_meta_alloc_shift (s_ctx st3) = c_meta_alloc_shift (s_ctx st) /\ c_secret (s_ctx st3) = c_secret (s_ctx st)
/\ c_avail_meta (s_ctx st3) = c_avail_meta (s_ctx st) /\ c_avail_meta_count (s_ctx st3) = c_avail_meta_count (s_ctx st)
/\ c_meta_area_head (s_ctx st3) = c_meta_area_head (s_ctx st) /\ c_meta_area_tail (s_ctx st3) = c_meta_area_tail (s_ctx st)
/\ c_free_meta_head (s_ctx st3) = c_free_meta_head (s_ctx st) /\ c_unmap_seq (s_ctx st3) = c_unmap_seq (s_ctx st)).
{ unfold st3, adv, st2, st1, upd_region, get_region. rewrite Hr. repeat split; try reflexivity. all: intros h; destruct h; reflexivity. }
destruct F3 as (FM & FA & FG & FS & FSH & FT & FN & FSE & FRS & FH & FU & FB & FQ & FMC & FI & FSF & FSC & FAM & FAC & FMH & FMT & FFH & FUS).
split; [| split; [reflexivity| split; [rewrite FA; exact NA| split; [rewrite FM; exact NM| split; [clear -O2; unfold PGSZ in *; lia| split; [exact OM| split; [exact FI|]]]]]]].
2:{ constructor; rewrite ?FG, ?FS, ?FSH, ?FT, ?FB, ?FQ, ?FMC, ?FN; auto; try reflexivity; try lia.
- intros sc. exact (FH (LActive sc)).
- intros sc. unfold usage, ctx. rewrite FU. reflexivity.
- intros b0 m0 ai0 _. unfold MR, get_meta_rec. rewrite FM. reflexivity. }
split; [| split; [| split; [| split; [| split; [| split]]]]].
- unfold L'. destruct IR; constructor; cbn [Qfya.ld_metas Qfya.ld_groups Qfya.ld_resv Qfya.ld_brkreg Qfya.ld_brk Qfya.ld_live Qfya.set_brkreg].
+ intros q rq Hq. rewrite FN.
apply SOME in Hq as [[-> _]|[_ Hq]]; [exact (ir_ids _ _ Hr)| exact (ir_ids _ _ Hq)].
+ intros q rq Hq. apply SOME in Hq as [[-> ->]|[_ Hq]]; [| exact (ir_shape q rq Hq)]. cbn. rewrite RU.
pose proof (ir_shape _ _ Hr) as (S1 & S2 & S3 & S4 & S5 & S6).
split; [lia|]. split; [exact BM|]. split; [unfold PGSZ; lia|]. split; [unfold alloc_ceiling, LEN_MAX, PGSZ in *; lia|]. split; [unfold PGSZ in *; lia|].
intros _. split; [unfold PGSZ in *; rewrite <- Zplus_mod_idemp_l, OM; reflexivity| lia].
+ intros q1 q2 r1 r2 H1 H2 NE.
assert (GROW : forall q rq, s_regions st !! q = Some rq -> q <> rid ->
let '(b2, l2) := region_live_range rq in r_base r + PGSZ + (round_up_pg (off + PGSZ) - PGSZ) <= b2 \/ b2 + l2 <= r_base r + PGSZ).
{ intros q rq Hq NEq. pose proof (ir_disj rid q r rq Hr Hq ltac:(congruence)) as D. unfold region_live_range in D at 1. rewrite K, E, RUo in D.
pose proof (ranges_free_regions st _ _ q rq PF Hq) as D2. rewrite Eold in D2.
pose proof (ir_shape q rq Hq) as (T1 & _ & T3 & _). pose proof (round_up_ge (r_len rq)) as T4.
assert (NB : r_kind rq <> RKBrk) by (intros Kq; apply NEq; exact (ir_brk1 q rid rq r Hq Hr Kq K)).
unfold region_live_range in *. destruct (r_kind rq); [congruence| |]; rewrite RU; unfold PGSZ in *; lia. }
apply SOME in H1 as [[-> ->]|[N1 H1]]; apply SOME in H2 as [[-> ->]|[N2 H2]]; [congruence| | | exact (ir_disj q1 q2 r1 r2 H1 H2 NE)].
* cbn. pose proof (GROW q2 r2 H2 N2) as D. destruct (region_live_range r2) as [b2 l2]. lia.
* pose proof (GROW q1 r1 H1 N1) as D. destruct (region_live_range r1) as [b1 l1]. cbn. lia.
+ rewrite FRS. exact ir_resv.
+ eapply Permutation_trans; [exact ir_groups|]. apply Permutation_map.
change (s_regions st3) with (s_regions st1). unfold st1, upd_region, get_region. rewrite Hr. cbn -[map_to_list].
apply (regions_update_perm st rid r _ _ Hr); cbn; rewrite ?K; reflexivity.
+ eapply Permutation_trans; [exact ir_metas|].
eapply Permutation_trans; [| apply Permutation_map; change (s_regions st3) with (s_regions st1); unfold st1, upd_region, get_region; rewrite Hr; cbn -[map_to_list];
apply (regions_update_perm st rid r _ _ Hr); cbn; rewrite ?K; reflexivity].
erewrite map_ext_in; [apply Permutation_refl|]. intros [q rq] Hin. apply filter_In in Hin as [Hin Hk]. apply In_map_to_list_regions in Hin. cbn in Hk. cbn [fst snd].
rewrite (bg_frontier_old q rq Hin), bg_frontier. destruct (N.eqb_spec rid q) as [<-|]; [rewrite Hr in Hin; inversion Hin; subst rq; rewrite K in Hk; discriminate| reflexivity].
+ intros q rq Hq Kq. rewrite bg_frontier. apply SOME in Hq as [[-> ->]|[NE Hq]]; [discriminate|].
destruct (N.eqb_spec rid q) as [<-|]; [congruence|]. pose proof (ir_metalen q rq Hq Kq) as (J & F1 & F2). rewrite (bg_frontier_old q rq Hq) in F1, F2. auto.
+ intros q rq Hq Kq. rewrite bg_frontier. apply SOME in Hq as [[-> ->]|[NE Hq]]; [rewrite N.eqb_refl; reflexivity|].
exfalso. apply NE. exact (ir_brk1 q rid rq r Hq Hr Kq K).
+ rewrite FSF. split; [exact (proj1 ir_shift)|]. destruct ir_shift as [_ [S|(q & rq & Hq & Kq & Eq)]]; [left; exact S| right].
exists q, rq. split; [apply KEEP; [exact Hq| intros ->; rewrite Hr in Hq; inversion Hq; subst; congruence]| auto].
+ intros b l. split.
* intros Eb. inversion Eb. subst b l. exists rid, r'. split; [rewrite LK, N.eqb_refl; reflexivity|]. cbn. repeat split; auto. lia.
* intros (q & rq & Hq & Kq & Eb & El). apply SOME in Hq as [[-> ->]|[NE Hq]]; [cbn in Eb, El; subst; f_equal; f_equal; lia|].
exfalso. apply NE. exact (ir_brk1 q rid rq r Hq Hr Kq K).
+ intros q1 q2 r1 r2 H1 H2 K1 K2.
apply SOME in H1 as [[-> ->]|[N1 H1]]; apply SOME in H2 as [[-> ->]|[N2 H2]]; [reflexivity| | |].
* exfalso. apply N2. exact (ir_brk1 q2 rid r2 r H2 Hr K2 K).
* exfalso. apply N1. exact (ir_brk1 q1 rid r1 r H1 Hr K1 K).
* exact (ir_brk1 q1 q2 r1 r2 H1 H2 K1 K2).
+ change (c_brk (s_ctx st3)) with (BrkLive rid (off + PGSZ)). split; [exact BP|]. exists r'. rewrite LK, N.eqb_refl. cbn. auto.
+ change (c_avail_meta_area_count (s_ctx st3)) with (1 - 1). change (c_avail_meta_areas (s_ctx st3)) with (Some (aadd (rid, off) 4096)).
split; [lia|]. split; [intros; lia|]. intros q o Eq. inversion Eq. subst q o. exists r'. rewrite LK, N.eqb_refl.
split; [reflexivity|]. split; [left; reflexivity|]. split; [unfold PGSZ in *; lia|]. split; [unfold PGSZ in *; rewrite <- Zplus_mod_idemp_l, OM; reflexivity|].
cbn. split; [unfold PGSZ; lia| intros; lia].
+ intros q Hq. destruct (ir_orph q Hq) as (rq & Hrq & Kq & NG). exists rq. split; [apply KEEPG; assumption|]. split; [exact Kq|]. rewrite FG. exact NG.
- destruct IA; constructor; rewrite ?FA, ?FM, ?FSE, ?FU, ?FB, ?FQ, ?FMC, ?FI, ?FSC, ?FAM, ?FAC, ?FMH, ?FMT, ?FUS; try assumption.
+ intros a ar Ha. destruct (ia_areas a ar Ha) as ((rq & Hq & Kq & M & P & F) & rest). split; [| exact rest].
destruct (KEEPM _ _ Hq Kq) as (rq' & Hq' & Kq'). exists rq'. rewrite bg_frontier. split; [exact Hq'|]. split; [exact Kq'|]. split; [exact M|]. split; [exact P|].
rewrite (bg_frontier_old _ _ Hq) in F. destruct (N.eqb_spec rid (fst a)) as [E1|NE1].
* rewrite <- E1, Hr in Hq. inversion Hq. subst rq. lia.
* rewrite LK in Hq'. destruct (N.eqb_spec (fst a) rid); [congruence|]. rewrite Hq in Hq'. inversion Hq'. subst. lia.
+ intros q Hq. destruct (ia_availptr q Hq) as (rq & Hrq & Kq). destruct (KEEPM _ _ Hrq Kq) as (rq' & Hq' & Kq'). exists rq'. auto.
+ intros sc Hsc. unfold usage, ctx. rewrite FU. fold (ctx st). fold (usage st sc). rewrite (ia_usage sc Hsc). symmetry. apply (gcnt_ext st st3 FG FM).
+ intros sc g. unfold active, ctx in FH. rewrite <- !get_head_active, (FH (LActive sc)). apply ia_active_keys.
- apply (inv_M_ext X st st3); [exact FM| exact FG| exact IM].
- apply (inv_L_ext st st3); [exact FM| exact FG| exact FH| exact IL].
- destruct IG as [G1 G2 G3 G4 G5]. constructor; rewrite ?FG.
+ intros m b ai Hb. apply (group_ok_ext X st st3); [exact FM| exact FS| intros q rq Hq Kq _; apply KEEPG; assumption| exact (G1 m b ai Hb)].
+ exact G2.
+ intros m1 m2 b1 b2 ai1 ai2 H1 H2. rewrite !(MR_ext st st3 FM). eapply G3; eassumption.
+ intros q rq Hq Kq Ho. apply SOME in Hq as [[-> ->]|[NE Hq]]; [discriminate|]. destruct (G4 q rq Hq Kq Ho) as (m & Hm & Hml). exists m.
rewrite (hosts_ext st st3 FG), (MR_ext st st3 FM). auto.
+ intros b h Hb. destruct (G5 b h Hb) as (rq & Hq & Kq). exists rq. split; [apply KEEPG; assumption| exact Kq].
- apply (inv_S_ext X st st3 BL); [exact FM| exact FG| exact FS| exact IS].
- apply (inv_SH_view' st st3 BL FSH FT KEEPG FG FS FM ISH).
Qed.
End BRK_GROW.

Section BRK_FIRST.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (cur : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hbrk : c_brk (s_ctx st) = BrkUntried.
Hypothesis Hcnt : c_avail_meta_area_count (s_ctx st) = 0.
Hypothesis Hcur : brk0_answer_ok cur = true.
Let base : Z := round_up_pg cur.
Hypothesis HOK : brk_pages_ok st base (2 * PGSZ) = true.
Let rid := s_next_rid st.
Let st1 := fst (new_region RKBrk base (2 * PGSZ) st).
Let st2 := upd_ctx (fun c => set_avail_meta_area_count 1 (set_avail_meta_areas (Some (rid, PGSZ)) (set_brk (BrkLive rid (2 * PGSZ)) c))) st1.
Let st3 := adv st2 (rid, PGSZ).
Variable L0 : mled.
Hypothesis HL0 : ld_resv L0 = ld_resv L /\ ld_groups L0 = ld_groups L /\ ld_metas L0 = ld_metas L.
Let L' := Qfya.set_brkph BPLive (Qfya.set_brkreg (Some (base, 2 * PGSZ)) L0).

#[using="HOK"] Lemma bf_base : 0 < base /\ base mod PGSZ = 0 /\ base + 2 * PGSZ <= alloc_ceiling /\ ranges_free (live_ranges st) base (2 * PGSZ) = true.
Proof.
destruct (brk_pages_ok_facts _ _ _ HOK) as (P0 & PC & PF). split; [exact P0|]. split; [apply round_up_pg_mod|]. auto.
Qed.

#[using="RC__ X L BL LS cur INV base"] Lemma bf_fresh : s_regions st !! rid = None.
Proof.
destruct (s_regions st !! rid) as [r0|] eqn:E; [| reflexivity]. exfalso.
pose proof (ir_ids _ _ _ (proj1 INV) _ _ E) as H. unfold rid in H. lia.
Qed.
#[using="RC__ X L BL LS INV Hbrk"] Lemma bf_nobrk q rq : s_regions st !! q = Some rq -> r_kind rq <> RKBrk.
Proof. pose proof (ir_brk _ _ _ (proj1 INV)) as B. rewrite Hbrk in B. destruct B as [_ NB]. apply NB. Qed.
#[using="Type"] Lemma bf_lookup q : s_regions st3 !! q = if (q =? rid)%N then Some (mkRegion RKBrk base (2 * PGSZ)) else s_regions st !! q.
Proof. unfold st3, adv, st2, st1. cbn -[new_region Z.mul]. apply lookup_new_region. Qed.
#[using="RC__ X L BL LS INV"] Lemma bf_keep q rq : s_regions st !! q = Some rq -> s_regions st3 !! q = Some rq.
Proof. intros H. rewrite bf_lookup. destruct (N.eqb_spec q rid) as [->|]; [rewrite bf_fresh in H; discriminate| exact H]. Qed.
#[using="Type"] Lemma bf_some q rq : s_regions st3 !! q = Some rq -> (q = rid /\ rq = mkRegion RKBrk base (2 * PGSZ)) \/ (q <> rid /\ s_regions st !! q = Some rq).
Proof. rewrite bf_lookup. destruct (N.eqb_spec q rid) as [->|NE]; [intros H; inversion H; auto| auto]. Qed.
#[using="Type"] Lemma bf_frontier q rq : frontier st3 q rq = if (rid =? q)%N then PGSZ + 4096 else r_len rq.
Proof. reflexivity. Qed.
#[using="RC__ X L BL LS INV Hcnt"] Lemma bf_frontier_old q rq : s_regions st !! q = Some rq -> frontier st q rq = r_len rq.
Proof. intros Hq. exact (frontier_full X st L q rq (proj1 INV) Hcnt Hq). Qed.

#[using="L INV Hbrk Hcnt HOK HL0"] Theorem INVL_brk_first : INVL X st3 L' BL LS
/\ c_avail_meta_areas (s_ctx st3) = Some (aadd (rid, PGSZ) 4096)
/\ s_areas st3 !! (rid, PGSZ) = None /\ (forall k, 0 <= k < NSLOTS -> s_metas st3 !! mslot (rid, PGSZ) k = None)
/\ PGSZ <= PGSZ /\ PGSZ mod PGSZ = 0 /\ c_init_done (s_ctx st3) = c_init_done (s_ctx st) /\ AM_frame st st3.
Proof.
destruct bf_base as (B0 & BM & BC & BF). destruct HL0 as (HL1 & HL2 & HL3).
pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
assert (NA : s_areas st !! (rid, PGSZ) = None).
{ destruct (s_areas st !! (rid, PGSZ)) as [ar|] eqn:E; [| reflexivity]. exfalso.
destruct (ia_areas _ IA _ _ E) as ((r' & Hr' & _) & _). cbn in Hr'. fold rid in Hr'. rewrite bf_fresh in Hr'. discriminate. }
assert (NM : forall k, 0 <= k < NSLOTS -> s_metas st !! mslot (rid, PGSZ) k = None).
{ intros k Hk. destruct (s_metas st !! mslot (rid, PGSZ) k) as [mr|] eqn:E; [| reflexivity]. exfalso.
destruct (ia_metas _ IA _ _ E) as (a & ar & k' & Ha & Hk' & Em). destruct (ia_areas _ IA _ _ Ha) as ((r' & Hr' & _) & _).
unfold mslot, aadd in Em. inversion Em. rewrite <- H0 in Hr'. cbn in Hr'. fold rid in Hr'. rewrite bf_fresh in Hr'. discriminate. }
assert (RU : round_up_pg (2 * PGSZ) = 2 * PGSZ) by reflexivity.
split; [| split; [reflexivity| split; [exact NA| split; [exact NM| split; [lia| split; [reflexivity| split; [reflexivity|]]]]]]].
2:{ constructor; cbn -[Z.mul]; auto; try reflexivity; [intros q rq H _; apply bf_keep; exact H| unfold rid; lia]. }
split; [| split; [| split; [| split; [| split; [| split]]]]].
- unfold L'. destruct IR; constructor; cbn [Qfya.ld_metas Qfya.ld_groups Qfya.ld_resv Qfya.ld_brkreg Qfya.ld_brk Qfya.ld_live Qfya.set_brkreg Qfya.set_brkph]; rewrite ?HL1, ?HL2, ?HL3.
+ intros q rq Hq. change (s_next_rid st3) with (N.succ (s_next_rid st)). apply bf_some in Hq as [[-> _]|[_ Hq]]; [unfold rid; lia|]. pose proof (ir_ids q rq Hq). lia.
+ intros q rq Hq. apply bf_some in Hq as [[-> ->]|[_ Hq]]; [| exact (ir_shape q rq Hq)]. cbn -[Z.mul]. rewrite RU.
split; [exact B0|]. split; [exact BM|]. split; [unfold PGSZ; lia|]. split; [unfold PGSZ, LEN_MAX; lia|]. split; [exact BC|]. intros _. split; [apply Z_mod_mult| lia].
+ intros q1 q2 r1 r2 H1 H2 NE.
apply bf_some in H1 as [[-> ->]|[N1 H1]]; apply bf_some in H2 as [[-> ->]|[N2 H2]]; [congruence| | | exact (ir_disj q1 q2 r1 r2 H1 H2 NE)].
* cbn -[Z.mul]. rewrite RU. pose proof (ranges_free_regions st _ _ q2 r2 BF H2) as D. destruct (region_live_range r2) as [b2 l2]. unfold PGSZ in *. lia.
* pose proof (ranges_free_regions st _ _ q1 r1 BF H1) as D. destruct (region_live_range r1) as [b1 l1]. cbn -[Z.mul]. rewrite RU. unfold PGSZ in *. lia.
+ exact ir_resv.
+ eapply Permutation_trans; [exact ir_groups|].
change (s_regions st3) with (<[rid := mkRegion RKBrk base (2 * PGSZ)]> (s_regions st)).
eapply Permutation_trans; [| apply Permutation_map; apply Permutation_sym; apply (regions_insert_perm st rid _ _ bf_fresh)].
cbn -[Z.mul map_to_list]. apply Permutation_refl.
+ eapply Permutation_trans; [exact ir_metas|].
change (s_regions st3) with (<[rid := mkRegion RKBrk base (2 * PGSZ)]> (s_regions st)).
eapply Permutation_trans; [| apply Permutation_map; apply Permutation_sym; apply (regions_insert_perm st rid _ _ bf_fresh)].
cbn -[frontier PGSZ Z.div Z.sub Z.mul map_to_list].
erewrite map_ext_in; [apply Permutation_refl|]. intros [q rq] Hin. apply filter_In in Hin as [Hin _]. apply In_map_to_list_regions in Hin. cbn [fst snd].
rewrite (bf_frontier_old q rq Hin), bf_frontier. destruct (N.eqb_spec rid q) as [<-|]; [rewrite bf_fresh in Hin; discriminate| reflexivity].
+ intros q rq Hq K. rewrite bf_frontier. apply bf_some in Hq as [[-> ->]|[NE Hq]]; [discriminate|].
destruct (N.eqb_spec rid q) as [<-|]; [congruence|]. pose proof (ir_metalen q rq Hq K) as (J & F1 & F2). rewrite (bf_frontier_old q rq Hq) in F1, F2. auto.
+ intros q rq Hq K. rewrite bf_frontier. apply bf_some in Hq as [[-> ->]|[NE Hq]]; [rewrite N.eqb_refl; reflexivity|]. exfalso. exact (bf_nobrk q rq Hq K).
+ cbn. split; [exact (proj1 ir_shift)|]. destruct ir_shift as [_ [S|(q & rq & Hq & Kq & Eq)]]; [left; exact S| right].
exists q, rq. split; [apply bf_keep; exact Hq| auto].
+ intros b l. split.
* intros Eb. inversion Eb. subst b l. exists rid, (mkRegion RKBrk base (2 * PGSZ)). split; [rewrite bf_lookup, N.eqb_refl; reflexivity|]. cbn. auto.
* intros (q & rq & Hq & Kq & Eb & El). apply bf_some in Hq as [[-> ->]|[NE Hq]]; [cbn in Eb, El; subst; reflexivity|]. exfalso. exact (bf_nobrk q rq Hq Kq).
+ intros q1 q2 r1 r2 H1 H2 K1 K2.
apply bf_some in H1 as [[-> ->]|[N1 H1]]; apply bf_some in H2 as [[-> ->]|[N2 H2]]; [reflexivity| | |].
* exfalso. exact (bf_nobrk q2 r2 H2 K2).
* exfalso. exact (bf_nobrk q1 r1 H1 K1).
* exfalso. exact (bf_nobrk q1 r1 H1 K1).
+ cbn -[Z.mul]. split; [reflexivity|]. exists (mkRegion RKBrk base (2 * PGSZ)). rewrite bf_lookup, N.eqb_refl. cbn. auto.
+ cbn -[Z.mul]. split; [lia|]. split; [intros; lia|]. intros q o Eq. inversion Eq. subst q o. exists (mkRegion RKBrk base (2 * PGSZ)). rewrite bf_lookup, N.eqb_refl.
split; [reflexivity|]. split; [left; reflexivity|]. cbn -[Z.mul]. unfold PGSZ. split; [lia|]. split; [reflexivity|]. split; [lia| intros; lia].
+ intros q Hq. destruct (ir_orph q Hq) as (rq & Hrq & Kq & NG). exists rq. split; [apply bf_keep; exact Hrq| auto].
- destruct IA; constructor; try assumption.
+ intros a ar Ha. destruct (ia_areas a ar Ha) as ((rq & Hq & Kq & M & P & F) & rest). split; [| exact rest].
exists rq. rewrite bf_frontier. split; [apply bf_keep; exact Hq|]. split; [exact Kq|]. split; [exact M|]. split; [exact P|].
rewrite (bf_frontier_old _ _ Hq) in F. destruct (N.eqb_spec rid (fst a)) as [E1|]; [| exact F]. exfalso. rewrite <- E1, bf_fresh in Hq. discriminate.
+ intros q Hq. destruct (ia_availptr q Hq) as (rq & Hrq & Kq). exists rq. split; [apply bf_keep; exact Hrq| exact Kq].
- apply (inv_M_ext X st st3); [reflexivity| reflexivity| exact IM].
- apply (inv_L_ext st st3); [reflexivity| reflexivity| intros h; destruct h; reflexivity| exact IL].
- destruct IG as [G1 G2 G3 G4 G5]. constructor.
+ intros m b ai Hb. apply (group_ok_ext X st st3); [reflexivity| reflexivity| intros q rq Hq Kq E; apply bf_keep; exact Hq| exact (G1 m b ai Hb)].
+ exact G2.
+ exact G3.
+ intros q rq Hq Kq Ho. apply bf_some in Hq as [[-> ->]|[NE Hq]]; [discriminate|]. exact (G4 q rq Hq Kq Ho).
+ intros b h Hb. destruct (G5 b h Hb) as (rq & Hq & Kq). exists rq. split; [apply bf_keep; exact Hq| exact Kq].
- apply (inv_S_ext X st st3 BL); [reflexivity| reflexivity| reflexivity| exact IS].
- destruct ISH as [D1 D2 D3 D4 D5 D6]; constructor; try assumption.
intros q sh Hq. destruct (D1 q sh Hq) as (rq & Hrq & Kq). exists rq. split; [apply bf_keep; exact Hrq| exact Kq].
Qed.
End BRK_FIRST.

End RC__1.
