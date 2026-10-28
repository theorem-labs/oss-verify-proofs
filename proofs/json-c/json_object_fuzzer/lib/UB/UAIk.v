(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q8tj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8tj.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSL3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require ULLZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import ULLZ.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope Z_scope.

Lemma nx_of_app_lt : forall tbl es e' j, (S j < length es)%nat -> nx_of tbl (es ++ [e']) j = nx_of tbl es j.
Proof. intros. unfold nx_of. rewrite nth_error_app1 by lia. reflexivity. Qed.
Lemma nx_of_app_last : forall tbl es e' j, (S j = length es)%nat -> nx_of tbl (es ++ [e']) j = ent_addr tbl (le_ix e').
Proof. intros. unfold nx_of. rewrite nth_error_app2 by lia. replace (S j - length es)%nat with 0%nat by lia. reflexivity. Qed.
Lemma nx_of_app_new : forall tbl es e' j, (j = length es)%nat -> nx_of tbl (es ++ [e']) j = 0.
Proof. intros. unfold nx_of. rewrite nth_error_app2 by lia. replace (S j - length es)%nat with 1%nat by lia. reflexivity. Qed.

Lemma pv_of_app_le : forall tbl es e' j, (j <= length es)%nat -> pv_of tbl (es ++ [e']) j = pv_of tbl es j.
Proof. intros. unfold pv_of. destruct j; [reflexivity|]. rewrite nth_error_app1 by lia. reflexivity. Qed.

Lemma last_nth_error : forall (es : list lent) j e d, nth_error es j = Some e -> (S j = length es)%nat -> last es d = e.
Proof.
induction es as [|a es IH]; intros j e d E Hj; [discriminate|].
destruct es as [|b es'].
- cbn in Hj. assert (j = 0%nat) by lia. subst j. cbn in E. injection E as ->. reflexivity.
- destruct j as [|j]; [cbn in Hj; lia|]. cbn in E. change (last (a :: b :: es') d) with (last (b :: es') d).
eapply IH; [exact E|]. cbn in Hj |- *. lia.
Qed.
Lemma tl_of_last : forall tbl es j e, nth_error es j = Some e -> (S j = length es)%nat -> tl_of tbl es = ent_addr tbl (le_ix e).
Proof.
intros tbl es j e E Hj. unfold tl_of. destruct es as [|e0 es'] eqn:EES; [discriminate|]. rewrite <- EES in *.
rewrite (last_nth_error es j e _ E Hj). reflexivity.
Qed.
Lemma tl_of_app : forall tbl es e', tl_of tbl (es ++ [e']) = ent_addr tbl (le_ix e').
Proof. intros. unfold tl_of. destruct (es ++ [e']) eqn:E; [destruct es; discriminate|]. rewrite <- E, last_last. reflexivity. Qed.
Lemma hd_of_app : forall tbl es e', hd_of tbl (es ++ [e']) = match es with [] => ent_addr tbl (le_ix e') | _ => hd_of tbl es end.
Proof. intros. destruct es; reflexivity. Qed.

Section Snoc.
Variables (tbl : Z) (es : list lent) (svs : list slotv) (g : nat) (sg : slotv) (k kn : Z) (ks : list byte) (v : Z).
Let e' := LE g k kn ks v.

Hypothesis LINK : lh_link tbl es svs.
Hypothesis Hg : (g < length svs)%nat.
Hypothesis Esg : nth_error svs g = Some sg.
Hypothesis FREE : ~ In g (map le_ix es).
Hypothesis Hk : 0 < k /\ k + kn < LH_FREEDv /\ kn <= 2^31.
Hypothesis Hv : 0 <= v < 2^64.
Hypothesis Htbl : 0 < tbl.

#[using="LINK Hg FREE Hk Hv"] Lemma lh_link_snoc_nil : es = [] -> lh_link tbl [e'] (upd svs g (new_slot k v (sv_pad sg) 0)).
Proof.
intros ->. destruct LINK as (LK1 & LK2 & LK3 & LK4).
split; [| split; [| split; [constructor; [intros []| constructor] | intros e [<-|[]]; cbn; lia]]].
- intros j e E. destruct j as [|j]; [| destruct j; discriminate]. cbn in E. injection E as <-. cbn [le_ix le_k le_v e'].
exists (new_slot k v (sv_pad sg) 0). rewrite nth_error_upd_same by exact Hg. repeat split; reflexivity.
- intros i s E NI. destruct (Nat.eq_dec i g) as [->|NE]; [exfalso; apply NI; left; reflexivity|].
rewrite nth_error_upd_other in E by (intros X; apply NE; symmetry; exact X). apply (LK2 i s E). intros [].
Qed.

#[using="LINK Hg FREE Hk Hv"] Lemma lh_link_snoc_cons : forall jl el sl,
nth_error es jl = Some el -> (S jl = length es)%nat -> nth_error svs (le_ix el) = Some sl ->
lh_link tbl (es ++ [e'])
(upd (upd svs g (new_slot k v (sv_pad sg) (ent_addr tbl (le_ix el)))) (le_ix el)
(SV (sv_k sl) (sv_kc sl) (sv_pad sl) (sv_v sl) (ent_addr tbl g) (sv_pv sl))).
Proof.
intros jl el sl El Hjl Esl. destruct LINK as (LK1 & LK2 & LK3 & LK4).
pose proof (proj1 (nth_error_Some svs (le_ix el)) ltac:(rewrite Esl; discriminate)) as Hixl.
assert (NEgl : le_ix el <> g).
{ intros X. apply FREE. rewrite <- X. apply in_map. eapply nth_error_In. exact El. }
split; [| split; [| split]].
- intros j e E.
destruct (Nat.lt_trichotomy (S j) (length es)) as [LT | [EQ | GT]].
+
rewrite nth_error_app1 in E by lia. destruct (LK1 j e E) as (s & Es & A1 & A2 & A3 & A4 & A5).
assert (NE1 : le_ix e <> g).
{ intros X. apply FREE. rewrite <- X. apply in_map. eapply nth_error_In. exact E. }
assert (NE2 : le_ix e <> le_ix el).
{ intros X. assert (j = jl); [|lia]. eapply (proj1 (NoDup_nth_error _) LK3 j jl); [rewrite length_map; lia|].
erewrite nth_error_map, E, nth_error_map, El. cbn. rewrite X. reflexivity. }
exists s. rewrite nth_error_upd_other by (intros X; apply NE2; symmetry; exact X).
rewrite nth_error_upd_other by (intros X; apply NE1; symmetry; exact X).
rewrite nx_of_app_lt by lia. rewrite pv_of_app_le by lia. repeat split; assumption.
+
rewrite nth_error_app1 in E by lia. assert (j = jl) by lia. subst j. rewrite El in E. injection E as <-.
destruct (LK1 jl el El) as (s & Es & A1 & A2 & A3 & A4 & A5). rewrite Esl in Es. injection Es as ->.
eexists. rewrite nth_error_upd_same by (rewrite upd_length; exact Hixl). split; [reflexivity|]. cbn [sv_k sv_kc sv_v sv_nx sv_pv].
rewrite nx_of_app_last by lia. rewrite pv_of_app_le by lia.
repeat split; assumption.
+
rewrite nth_error_app2 in E by lia. destruct (j - length es)%nat eqn:D; [| destruct n; discriminate]. cbn in E. injection E as <-.
assert (j = length es) by lia. subst j. cbn [le_ix le_k le_v e'].
eexists. rewrite nth_error_upd_other by (intros X; apply NEgl; exact X). rewrite nth_error_upd_same by exact Hg. split; [reflexivity|].
cbn [new_slot sv_k sv_kc sv_v sv_nx sv_pv]. rewrite nx_of_app_new by reflexivity. rewrite pv_of_app_le by lia.
repeat split; try reflexivity. unfold pv_of. destruct (length es) eqn:L; [lia|]. replace n with jl by lia. rewrite El. reflexivity.
- intros i s E NI. rewrite map_app in NI. cbn in NI.
assert (NE1 : i <> g) by (intros ->; apply NI; apply in_or_app; right; left; reflexivity).
assert (NE2 : i <> le_ix el) by (intros ->; apply NI; apply in_or_app; left; apply in_map; eapply nth_error_In; exact El).
rewrite nth_error_upd_other in E by (intros X; apply NE2; symmetry; exact X).
rewrite nth_error_upd_other in E by (intros X; apply NE1; symmetry; exact X).
apply (LK2 i s E). intros X. apply NI. apply in_or_app. left. exact X.
- rewrite map_app. cbn. apply NoDup_app; [exact LK3 | constructor; [intros [] | constructor] |].
intros a Ha [<- | []]. exact (FREE Ha).
- intros e He. apply in_app_iff in He as [He | [<- | []]]; [exact (LK4 e He) | cbn; lia].
Qed.
End Snoc.

Section OpenSnoc.
Variable segs : list Segment.
Variable fn : fnaddrs.

#[using="Type"] Lemma lh_open_snoc : forall ffn m t tbl size es svs (g : nat) sg k kn ks v ixl sl,
lh_link tbl es svs -> lh_keys segs m es -> cstr segs m k kn ks ->
In size lf_sizes -> Z.of_nat (length es) + 1 <= lf_thr size -> Z.of_nat (length svs) = size ->
(g < length svs)%nat -> nth_error svs g = Some sg -> ~ In g (map le_ix es) ->
0 < k /\ k + kn < LH_FREEDv /\ kn <= 2^31 -> 0 <= v < 2^64 -> 0 < tbl ->
(es <> [] -> exists jl el, nth_error es jl = Some el /\ (S jl = length es)%nat /\ ixl = le_ix el /\ nth_error svs ixl = Some sl) ->
lh_hdrf segs fn ffn m t size (Z.of_nat (length es) + 1) (match es with [] => ent_addr tbl g | _ => hd_of tbl es end) (ent_addr tbl g) tbl ->
lh_slots segs m tbl (ins_svs svs g sg k v (hd_of tbl es) (tl_of tbl es) ixl sl tbl) ->
lh_openf segs fn ffn m t tbl size (es ++ [LE g k kn ks v]) (ins_svs svs g sg k v (hd_of tbl es) (tl_of tbl es) ixl sl tbl).
Proof.
intros ffn m t tbl size es svs g sg k kn ks v ixl sl LINK KEYS CS Hsz Hcnt Hlen Hg Esg FREE Hk Hv Htbl LAST HDR SL.
split; [| split; [exact SL | split; [| split; [| split; [exact Hsz | split; [rewrite length_app; cbn; lia |]]]]]].
- rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. cbn [Z.of_nat Pos.of_succ_nat]. rewrite hd_of_app, tl_of_app. cbn [le_ix]. exact HDR.
- unfold ins_svs. destruct es as [|e0 es'] eqn:EES.
+ cbn [hd_of tl_of Z.eqb app]. subst es. eapply lh_link_snoc_nil; try eassumption. reflexivity.
+ rewrite <- EES in *. assert (NE : es <> []) by (rewrite EES; discriminate).
destruct (LAST NE) as (jl & el & El & Hjl & -> & Esl).
assert (HD : hd_of tbl es =? 0 = false).
{ rewrite EES. cbn [hd_of]. unfold ent_addr. apply Z.eqb_neq. lia. }
rewrite HD. rewrite (tl_of_last tbl es jl el El Hjl).
eapply (lh_link_snoc_cons tbl es svs g sg k kn ks v) with (jl := jl); try eassumption.
- unfold lh_keys in *. apply Forall_app. split; [exact KEYS|]. constructor; [cbn; exact CS | constructor].
- unfold ins_svs. destruct (hd_of tbl es =? 0); rewrite !upd_length; lia.
Qed.
End OpenSnoc.
