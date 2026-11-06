(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YG03.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: class_elems_count bounds rg_alloc_user by kFreeArrayOffset instead of 2 ^ 31 (YG06Free.mapped_user_le_free_array); its proof does not unfold EV_MAX. *)
From Stdlib Require Import ZArith List Bool Lia.
From Stdlib Require Import Sorting.Permutation.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG06Free.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Local Open Scope am_scope.
Ltac cbnr := cbn [rg_mapped_user rg_alloc_user rg_mapped_fa rg_free rg_holes fst snd].
Ltac splits := repeat lazymatch goal with |- _ /\ _ => split end.
Lemma chunk_offs_begs : forall s s' c, map ck_beg (st_chunks s') = map ck_beg (st_chunks s) -> chunk_offs s' c = chunk_offs s c.
Proof.
intros s s' c H. unfold chunk_offs. remember (st_chunks s) as l eqn:El. remember (st_chunks s') as l' eqn:El'. clear El El'.
revert l' H. induction l as [|k t IH]; intros [|k0 t0] H; cbn in H; try discriminate; [reflexivity|].
injection H as Hb Ht. cbn [flat_map]. rewrite Hb, (IH _ Ht). reflexivity.
Qed.
Lemma sec_live_bytes_begs : forall l l', map ck_beg l' = map ck_beg l -> map ck_req l' = map ck_req l ->
fold_right (fun k acc => match ck_beg k with PSec _ _ => sec_map_size (ck_req k) + acc | _ => acc end) 0 l'
= fold_right (fun k acc => match ck_beg k with PSec _ _ => sec_map_size (ck_req k) + acc | _ => acc end) 0 l.
Proof.
induction l as [|k t IH]; intros [|k0 t0] H1 H2; cbn in *; try discriminate; [reflexivity|].
injection H1 as Hb Ht. injection H2 as Hr Ht2. rewrite Hb, Hr, (IH _ Ht Ht2). reflexivity.
Qed.
Lemma user_inj : forall U pp cc bb s k1 k2,
WfP U pp cc bb s -> In k1 (st_chunks s) -> In k2 (st_chunks s) -> ck_user k1 = ck_user k2 -> k1 = k2.
Proof.
intros U pp cc bb s k1 k2 W H1 H2 E.
assert (EB : ck_beg k1 = ck_beg k2).
{ pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ W) k1 H1) as [N1 C1].
pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ W) k2 H2) as [N2 C2].
unfold ck_user in E. destruct (ck_beg k1) as [|b1|r1 o1|c1 p1] eqn:E1; destruct (ck_beg k2) as [|b2|r2 o2|c2 p2] eqn:E2;
cbn [padd] in E; try discriminate; try solve [destruct C1 | destruct C2].
- injection E as E. destruct C2 as (P2 & Q2 & R2).
pose proof (prim_chunk_off U pp cc bb s k2 b2 W H2 E2) as (G1 & G2 & G3 & G4 & G5 & G6). cbv zeta in *.
pose proof (prim_user_inj U pp cc bb s k1 b1 (prim_class b2) (b2 - region_off (prim_class b2)) (ck_req k2) W H1 E1
ltac:(lia) G5 G6 ltac:(lia) P2 (eq_sym Q2)) as J.
unfold ck_rz in E, J. f_equal. specialize (J ltac:(lia)). lia.
- injection E as <- Eo. destruct C1 as (_ & -> & _), C2 as (_ & -> & _). reflexivity. }
pose proof (In_split_beg _ _ H1 (wf_chunks_nodup _ _ _ _ _ W)) as (l1 & l2 & El & N1 & N2).
rewrite El in H2. apply in_app_iff in H2 as [H2|[<-|H2]]; [exfalso | reflexivity | exfalso].
- apply N1. rewrite EB. apply in_map. exact H2.
- apply N2. rewrite EB. apply in_map. exact H2.
Qed.
Lemma find_user_block : forall U pp cc bb s p n, WfP U pp cc bb s -> In (p, n) (blocks s) ->
exists k, find_user (st_chunks s) p = Some k /\ In k (st_chunks s) /\ ck_state k = CAllocated /\ ck_user k = p /\ ck_req k = n.
Proof.
intros U pp cc bb s p n W Hin. apply In_blocks in Hin as (k & Hk & Hs & Hu & Hr).
destruct (find_user (st_chunks s) p) as [k'|] eqn:F.
- apply find_user_spec in F as [Hk' Hu']. pose proof (user_inj U pp cc bb s k k' W Hk Hk' ltac:(congruence)) as <-.
exists k. auto.
- exfalso. exact (find_user_None _ _ F k Hk Hu).
Qed.
Lemma WfP_set_internal_inited : forall U pp cc bb s v, WfP U pp cc bb s -> WfP U pp cc bb (set_internal_inited v s).
Proof. intros U pp cc bb s v W. wf_fields W. constructor; wf_easy. Qed.
Definition quar_of (k : chunk) : chunk := mkChunk (ck_beg k) (ck_req k) CQuarantined.
Definition bbytes (l : list chunk) : Z := fold_right (fun k acc => if is_alloc k then ck_req k + acc else acc) 0 l.
Lemma blocks_bytes_eq : forall s, blocks_bytes s = bbytes (st_chunks s). Proof. reflexivity. Qed.
Lemma bbytes_split : forall l1 k l2, bbytes (l1 ++ k :: l2) = bbytes (l1 ++ l2) + (if is_alloc k then ck_req k else 0).
Proof.
intros l1 k l2. unfold bbytes. induction l1 as [|h t IH]; cbn; [destruct (is_alloc k); lia | rewrite IH; destruct (is_alloc h); lia].
Qed.
Lemma bbytes_app : forall l1 l2, bbytes (l1 ++ l2) = bbytes l1 + bbytes l2.
Proof. intros l1 l2. unfold bbytes. induction l1 as [|h t IH]; cbn; [lia | rewrite IH; destruct (is_alloc h); lia]. Qed.
Lemma bbytes_nonneg : forall s l, Forall (chunk_ok s) l -> 0 <= bbytes l.
Proof. intros s l H. unfold bbytes. induction H as [|k t [Hk _] Ht IH]; cbn; [lia|]. destruct (is_alloc k); lia. Qed.
Definition unq (s : astate) : Z := quar_n s - queued_n s.
Lemma quar_nl_split : forall l1 k l2, quar_nl (l1 ++ k :: l2) = quar_nl (l1 ++ l2) + (if is_alloc k then 0 else ck_n k).
Proof.
intros l1 k l2. unfold quar_nl. induction l1 as [|h t IH]; cbn; [destruct (is_alloc k); lia | rewrite IH; destruct (is_alloc h); lia].
Qed.
Lemma items_n_flat_app : forall P Q, items_n (flat_map b_items (P ++ Q)) = items_n (flat_map b_items P) + items_n (flat_map b_items Q).
Proof. intros P Q. rewrite flat_map_app, items_n_app. reflexivity. Qed.
Lemma queued_n_eq : forall s, queued_n s = items_n (flat_map b_items (qc_list (st_qthread s))) + items_n (flat_map b_items (qc_list (st_qglobal s))).
Proof. intros s. unfold queued_n, q_items, all_batches. apply items_n_flat_app. Qed.
Lemma items_n_cons : forall k l, items_n (k :: l) = ck_n k + items_n l. Proof. reflexivity. Qed.
Lemma items_n_nil : items_n [] = 0. Proof. reflexivity. Qed.
Lemma unq_flip : forall s l1 k l2, st_chunks s = l1 ++ k :: l2 -> ck_state k = CAllocated ->
unq (set_chunks (l1 ++ quar_of k :: l2) s) = unq s + ck_n k.
Proof.
intros s l1 k l2 E Hst. unfold unq, quar_n, queued_n, q_items, all_batches. cbn [st_chunks st_qthread st_qglobal set_chunks].
rewrite E, !quar_nl_split. replace (is_alloc k) with true by (unfold is_alloc; rewrite Hst; reflexivity).
replace (is_alloc (quar_of k)) with false by reflexivity. change (ck_n (quar_of k)) with (ck_n k). lia.
Qed.
Lemma unq_push : forall s s' kq nb,
st_chunks s' = st_chunks s -> st_qthread s' = qc_push (st_qthread s) kq nb -> st_qglobal s' = st_qglobal s ->
(nb = None -> need_new_batch (st_qthread s) = false) ->
unq s' = unq s - ck_n kq.
Proof.
intros s s' kq nb Hc Hq Hg Hnb. unfold unq, quar_n. rewrite !queued_n_eq, Hc, Hq, Hg.
enough (E : items_n (flat_map b_items (qc_list (qc_push (st_qthread s) kq nb))) = items_n (flat_map b_items (qc_list (st_qthread s))) + ck_n kq) by lia.
destruct nb as [off|]; cbn [qc_push qc_list].
- rewrite items_n_flat_app. cbn [flat_map b_items app]. rewrite items_n_cons, items_n_nil. lia.
- specialize (Hnb eq_refl). unfold need_new_batch in Hnb. destruct (rev (qc_list (st_qthread s))) as [|lastb initr] eqn:R; [discriminate|].
rewrite <- (rev_involutive (qc_list (st_qthread s))). rewrite R. cbn [rev]. rewrite !items_n_flat_app. cbn [flat_map b_items].
rewrite !app_nil_r, items_n_app, items_n_cons, items_n_nil. lia.
Qed.
Lemma unq_transfer : forall s,
unq (set_qglobal (mkQC (qc_list (st_qglobal s) ++ qc_list (st_qthread s)) (qc_bytes (st_qglobal s) + qc_bytes (st_qthread s))) (set_qthread qc0 s)) = unq s.
Proof.
intros s. unfold unq, quar_n. rewrite !queued_n_eq. cbn [st_chunks st_qthread st_qglobal set_qglobal set_qthread qc_list qc0 flat_map].
rewrite items_n_nil. fold (flat_map b_items (qc_list (st_qglobal s) ++ qc_list (st_qthread s))). rewrite items_n_flat_app. lia.
Qed.
Lemma unq_pop : forall s P rest bytes', qc_list (st_qglobal s) = P ++ rest ->
unq (set_qglobal (mkQC rest bytes') s) = unq s + items_n (flat_map b_items P).
Proof.
intros s P rest bytes' E. unfold unq, quar_n. rewrite !queued_n_eq. cbn [st_chunks st_qthread st_qglobal set_qglobal qc_list].
rewrite E, items_n_flat_app. lia.
Qed.
Lemma unq_del : forall s s' l1 k l2, st_chunks s = l1 ++ k :: l2 -> st_chunks s' = l1 ++ l2 -> ck_state k = CQuarantined ->
st_qthread s' = st_qthread s -> st_qglobal s' = st_qglobal s -> unq s' = unq s - ck_n k.
Proof.
intros s s' l1 k l2 E E' Hst Hq Hg. unfold unq, quar_n. rewrite !queued_n_eq, E, E', Hq, Hg, quar_nl_split.
replace (is_alloc k) with false by (unfold is_alloc; rewrite Hst; reflexivity). lia.
Qed.
Lemma unq_same : forall s s', st_chunks s' = st_chunks s -> st_qthread s' = st_qthread s -> st_qglobal s' = st_qglobal s -> unq s' = unq s.
Proof. intros s s' H1 H2 H3. unfold unq, quar_n. rewrite !queued_n_eq, H1, H2, H3. reflexivity. Qed.
Lemma WfP_flip : forall U pp cc bb s l1 k l2,
WfP U pp cc bb s -> st_chunks s = l1 ++ k :: l2 -> ck_state k = CAllocated ->
WfP U pp cc bb (set_chunks (l1 ++ quar_of k :: l2) s).
Proof.
intros U pp cc bb s l1 k l2 W El Hst. wf_fields W.
assert (EM : map ck_beg (l1 ++ quar_of k :: l2) = map ck_beg (st_chunks s)) by (rewrite El, !map_app; reflexivity).
assert (ER : map ck_req (l1 ++ quar_of k :: l2) = map ck_req (st_chunks s)) by (rewrite El, !map_app; reflexivity).
assert (ND : NoDup (map ck_beg (l1 ++ k :: l2))) by (rewrite <- El; exact Xnd).
rewrite map_app in ND. cbn in ND. apply NoDup_app_iff in ND as (ND1 & ND2 & ND3). inversion ND2; subst.
constructor; wf_easy.
- intros c Hc. unfold wf_class. rewrite (chunk_offs_begs s) by exact EM. rewrite batch_offs_set_chunks, reg_set_chunks, cache_set_chunks.
exact (Xcl c Hc).
- cbn [st_chunks set_chunks]. rewrite El in Xck. apply Forall_app in Xck as [X1 X2]. inversion X2; subst.
apply Forall_app. split; [eapply Forall_chunk_ok_ext; [reflexivity | exact X1]|]. constructor; [|eapply Forall_chunk_ok_ext; [reflexivity | eassumption]].
unfold chunk_ok in *. cbn [quar_of ck_req ck_beg st_secs set_chunks]. assumption.
- cbn [st_chunks set_chunks]. rewrite EM. exact Xnd.
- cbn [st_chunks set_chunks st_nev]. rewrite length_app in *. cbn [length] in *. rewrite El, length_app in Xcev. cbn in Xcev. lia.
- rewrite blocks_bytes_eq in *. cbn [st_chunks set_chunks]. rewrite El in Xlive. rewrite bbytes_split in *. cbn [is_alloc quar_of ck_state].
rewrite El in Xck. apply Forall_app in Xck as [X1 X2]. inversion X2; subst.
match goal with H : chunk_ok s k |- _ => destruct H as [Hn _] end. destruct (is_alloc k); lia.
- quar_fields Xq. constructor; cbn [st_qthread st_qglobal st_chunks set_chunks]; rewrite ?all_batches_set_chunks, ?q_items_set_chunks; try assumption.
eapply Forall_impl; [|exact Qit]. intros k' [Hk' Hs']. split; [|exact Hs'].
rewrite El in Hk'. apply in_app_iff in Hk' as [Hk'|[<-|Hk']]; [apply in_app_iff; left; exact Hk' | congruence | apply in_app_iff; right; right; exact Hk'].
- sec_fields Xsec. constructor; cbn [st_sec_arr st_secs st_chunks st_sec_reserved set_chunks]; try assumption.
intros r. rewrite Sac. rewrite El. split; intros (k' & Hk' & Hb); apply in_app_iff in Hk' as [Hk'|[<-|Hk']].
+ exists k'. split; [apply in_app_iff; left; exact Hk' | exact Hb].
+ exists (quar_of k). split; [apply in_app_iff; right; left; reflexivity | exact Hb].
+ exists k'. split; [apply in_app_iff; right; right; exact Hk' | exact Hb].
+ exists k'. split; [apply in_app_iff; left; exact Hk' | exact Hb].
+ exists k. split; [apply in_app_iff; right; left; reflexivity | exact Hb].
+ exists k'. split; [apply in_app_iff; right; right; exact Hk' | exact Hb].
- apply (wf_fa_room_ext s _ (fun c0 => cc + bslack c0 bb)); [ | reflexivity | reflexivity | exact Xroom].
intros c Hc. unfold class_elems. rewrite (chunk_offs_begs s) by exact EM. reflexivity.
-
apply (regime_xfer _ _ s _ Xreg); [reflexivity | intros HBP; exact HBP | cbn [st_chunks set_chunks]; rewrite El, !length_app; cbn [length]; lia].
Qed.
Lemma sum_bytes_app : forall l1 l2, sum_bytes (l1 ++ l2) = sum_bytes l1 + sum_bytes l2.
Proof. intros l1 l2. unfold sum_bytes. apply (fold_right_add_app b_bytes). Qed.
Lemma b_bytes_app1 : forall b k, b_bytes (mkBatch (b_self b) (b_items b ++ [k])) = b_bytes b + ck_n k.
Proof.
intros b k. unfold b_bytes. cbn [b_items]. rewrite (fold_right_add_app ck_n). cbn [fold_right]. lia.
Qed.
Lemma cls_ok_rebatch : forall c r p i ko bo ko' bo',
cls_ok c r p i ko bo -> Permutation (ko ++ bo) (ko' ++ bo') -> cls_ok c r p i ko' bo'.
Proof.
intros c r p i ko bo ko' bo' C HP.
eapply (cls_ok_repart c r p i ko bo r p i ko' bo' []); try reflexivity; [exact C | exact (wr_runs _ _ _ _ _ _ C) | exact (wr_fa_len _ _ _ _ _ _ C) | exact (wr_cache _ _ _ _ _ _ C) |].
cbn [app]. apply Permutation_app_head. apply Permutation_app_head. exact HP.
Qed.
Lemma cls_ok_add_bo : forall c r p i ko bo x,
cls_ok c r p i ko bo ->
~ In x (fa_elems (class_size c) (rg_free r) ++ pc_chunks p ++ ko ++ bo) ->
0 <= x < rg_alloc_user r -> x mod class_size c = 0 ->
cls_ok c r p i ko (bo ++ [x]).
Proof.
intros c r p i ko bo x C Hni Hx Hm.
pose proof (cls_ok_add_ko c r p i ko bo x C Hni Hx Hm) as C'.
eapply cls_ok_rebatch; [exact C'|]. rewrite <- app_assoc. apply Permutation_app_head. apply Permutation_app_comm.
Qed.
Lemma batch_offs_other : forall s c, c <> kBatchClass -> batch_offs s c = [].
Proof. intros s c Hc. unfold batch_offs. destruct (Z.eqb_spec c kBatchClass); [lia | reflexivity]. Qed.
Lemma batch_offs_24 : forall s, batch_offs s kBatchClass = map (fun b => b_self b - region_off kBatchClass) (all_batches s).
Proof. intros s. unfold batch_offs. rewrite Z.eqb_refl. reflexivity. Qed.
Lemma boffs_map : forall L, map (fun b => b_self b - region_off kBatchClass) L = map (fun z => z - region_off kBatchClass) (map b_self L).
Proof. intros L. rewrite map_map. reflexivity. Qed.
Lemma qc_list_push : forall q k nb,
(nb = None -> need_new_batch q = false) ->
exists T0 bl, qc_list (qc_push q k nb) = T0 ++ [bl] /\
match nb with
| Some off => T0 = qc_list q /\ bl = mkBatch off [k]
| None => exists lastb, qc_list q = T0 ++ [lastb] /\ bl = mkBatch (b_self lastb) (b_items lastb ++ [k]) /\
Z.of_nat (length (b_items lastb)) <> kBatchSlots
end /\
qc_bytes (qc_push q k nb) = qc_bytes q + ck_n k + (match nb with Some _ => kBatchBytes | None => 0 end).
Proof.
intros q k nb Hnb. destruct nb as [off|]; cbn -[ck_n kBatchBytes].
- exists (qc_list q), (mkBatch off [k]). splits; try reflexivity.
- specialize (Hnb eq_refl). unfold need_new_batch in Hnb.
destruct (rev (qc_list q)) as [|lastb initr] eqn:Er; [discriminate|].
exists (rev initr), (mkBatch (b_self lastb) (b_items lastb ++ [k])). splits; try reflexivity; [|lia].
exists lastb. splits; [|reflexivity | apply Z.eqb_neq; exact Hnb].
rewrite <- (rev_involutive (qc_list q)), Er. cbn. reflexivity.
Qed.
Lemma removelast_snoc {X} : forall (l : list X) a, removelast (l ++ [a]) = l.
Proof.
intros l a. induction l as [|h t IH]; [reflexivity|]. cbn [app removelast]. rewrite IH.
destruct t as [|h' t']; cbn; reflexivity.
Qed.
Lemma need_new_batch_full : forall q, need_new_batch q = true -> Forall bfull (removelast (qc_list q)) -> Forall bfull (qc_list q).
Proof.
intros q H F. unfold need_new_batch in H. destruct (rev (qc_list q)) as [|lastb initr] eqn:Er.
- apply (f_equal (@rev batch)) in Er. rewrite rev_involutive in Er. rewrite Er. constructor.
- apply (f_equal (@rev batch)) in Er. rewrite rev_involutive in Er. cbn [rev] in Er. rewrite Er in F |- *. rewrite removelast_snoc in F.
apply Forall_app. split; [exact F|]. constructor; [|constructor]. unfold bfull. apply Z.eqb_eq in H. rewrite <- H. rewrite Nat2Z.id. reflexivity.
Qed.
Lemma Forall_removelast_tl {X} (P : X -> Prop) : forall a (l : list X), Forall P (removelast (a :: l)) -> Forall P (removelast l).
Proof. intros a l H. destruct l as [|b t]; [constructor|]. cbn [removelast] in H. inversion H; subst. assumption. Qed.
Lemma WfP_qpush : forall U pp cc bb s kq nb,
WfP U pp cc bb s -> 1 <= bb ->
In kq (st_chunks s) -> ck_state kq = CQuarantined -> ~ In (ck_beg kq) (map ck_beg (q_items s)) ->
match nb with
| Some off => exists x, off = region_off kBatchClass + x /\ 0 <= x < rg_alloc_user (reg s kBatchClass) /\
x mod class_size kBatchClass = 0 /\ ~ In x (class_elems s kBatchClass)
| None => need_new_batch (st_qthread s) = false
end ->
match nb with Some _ => st_cache_inited s = true | None => True end ->
(nb <> None -> need_new_batch (st_qthread s) = true) ->
WfP U pp cc (bb - 1) (set_qthread (qc_push (st_qthread s) kq nb) s).
Proof.
intros U pp cc bb s kq nb W Hbb Hk Hst Hnotin Hnb Hci Hnew.
assert (QI' : all_batches s <> [] \/ st_cache_inited s = true).
{ destruct nb as [off|]; [right; exact Hci|]. left. unfold all_batches. intros E. apply app_eq_nil in E as [E _].
unfold need_new_batch in Hnb. rewrite E in Hnb. cbn in Hnb. discriminate. }
destruct (qc_list_push (st_qthread s) kq nb ltac:(intros ->; exact Hnb)) as (T0 & bl & EL & CASE & EB).
set (q' := qc_push (st_qthread s) kq nb) in *.
wf_fields W. quar_fields Xq.
assert (SHAPE : exists T1 its, qc_list (st_qthread s) = T0 ++ T1 /\ b_items bl = its ++ [kq] /\ flat_map b_items T1 = its /\
sum_bytes [bl] = sum_bytes T1 + ck_n kq + (match nb with Some _ => kBatchBytes | None => 0 end) /\
(1 <= length (b_items bl) <= Z.to_nat kBatchSlots)%nat /\
map b_self (T0 ++ [bl]) = map b_self (qc_list (st_qthread s)) ++ (match nb with Some off => [off] | None => [] end)).
{ destruct nb as [off|].
- destruct CASE as [-> ->]. exists [], []. rewrite app_nil_r, map_app. cbn -[ck_n kBatchBytes kBatchSlots Z.add Z.of_nat Z.to_nat].
unfold kBatchSlots. splits; try reflexivity; try lia. unfold b_bytes. cbn -[ck_n kBatchBytes Z.add]. lia.
- destruct CASE as (lastb & ET & -> & Hlen). exists [lastb], (b_items lastb). rewrite ET.
pose proof (proj1 (Forall_forall _ _) Qbat lastb ltac:(unfold all_batches; rewrite ET, <- app_assoc; apply in_elt)) as BL.
cbn -[ck_n kBatchBytes kBatchSlots b_bytes Z.add Z.of_nat Z.to_nat]. rewrite app_nil_r, b_bytes_app1, !map_app. cbn [map b_self].
rewrite length_app. cbn [length]. unfold kBatchSlots in *. splits; try reflexivity; try lia. rewrite app_nil_r. reflexivity. }
destruct SHAPE as (T1 & its & ET & EI & EF & ES & BLEN & SELF).
assert (AB : all_batches (set_qthread q' s) = (T0 ++ [bl]) ++ qc_list (st_qglobal s)) by (unfold all_batches; cbn; rewrite EL; reflexivity).
assert (AB0 : all_batches s = (T0 ++ T1) ++ qc_list (st_qglobal s)) by (unfold all_batches; rewrite ET; reflexivity).
assert (QI : q_items (set_qthread q' s) = (flat_map b_items T0 ++ its ++ [kq]) ++ flat_map b_items (qc_list (st_qglobal s))).
{ unfold q_items. rewrite AB, !flat_map_app. cbn [flat_map]. rewrite EI, app_nil_r, app_assoc. reflexivity. }
assert (QI0 : q_items s = (flat_map b_items T0 ++ its) ++ flat_map b_items (qc_list (st_qglobal s))).
{ unfold q_items. rewrite AB0, !flat_map_app, EF. reflexivity. }
assert (PQ : Permutation (q_items (set_qthread q' s)) (kq :: q_items s)).
{ rewrite QI, QI0. rewrite !app_assoc. rewrite <- (app_assoc (flat_map b_items T0 ++ its) [kq]). cbn [app].
apply Permutation_sym. apply Permutation_middle. }
assert (PB : Permutation (batch_offs (set_qthread q' s) kBatchClass)
(batch_offs s kBatchClass ++ map (fun z => z - region_off kBatchClass) (match nb with Some off => [off] | None => [] end))).
{ rewrite !batch_offs_24, !boffs_map, AB, <- map_app. apply Permutation_map. unfold all_batches.
rewrite !map_app, <- (map_app b_self T0 [bl]), SELF, <- !app_assoc. apply Permutation_app_head. apply Permutation_app_comm. }
constructor; wf_easy.
- intros c Hc. unfold wf_class. cbn [st_cache_inited set_qthread]. change (reg (set_qthread q' s) c) with (reg s c). change (cache (set_qthread q' s) c) with (cache s c).
rewrite (chunk_offs_begs s) by reflexivity.
pose proof (Xcl c Hc) as C. unfold wf_class in C.
destruct (Z.eq_dec c kBatchClass) as [->|Hne].
+ eapply cls_ok_rebatch; [|apply Permutation_app_head; apply Permutation_sym; exact PB].
destruct nb as [off|]; [|rewrite app_nil_r; exact C].
destruct Hnb as (x & -> & Hx & Hxm & Hxni). cbn [map]. replace (region_off kBatchClass + x - region_off kBatchClass) with x by lia.
apply cls_ok_add_bo; [exact C | exact Hxni | exact Hx | exact Hxm].
+ rewrite !batch_offs_other by exact Hne. rewrite batch_offs_other in C by exact Hne. exact C.
- constructor; cbn [st_qthread st_qglobal st_chunks set_qthread]; try assumption.
+ subst q'. rewrite EB, EL, sum_bytes_app, ES. rewrite Qbt, ET, sum_bytes_app. lia.
+ rewrite AB. rewrite AB0 in Qbat. rewrite <- app_assoc in Qbat |- *. apply Forall_app in Qbat as [Q1 Q2]. apply Forall_app in Q2 as [_ Q3].
apply Forall_app. split; [exact Q1|]. constructor; [exact BLEN | exact Q3].
+ eapply Forall_Permutation; [apply Permutation_sym; exact PQ|]. constructor; [split; assumption | exact Qit].
+ eapply NoDup_Permutation; [apply Permutation_map; apply Permutation_sym; exact PQ|]. cbn [map]. constructor; [exact Hnotin | exact Qnd].
+
rewrite EL, removelast_snoc. destruct nb as [off|].
* destruct CASE as [-> _]. apply need_new_batch_full; [apply Hnew; discriminate | exact Qtf].
* destruct CASE as (lastb & ET' & _ & _). rewrite ET', removelast_snoc in Qtf. exact Qtf.
- cbn [st_nev set_qthread]. rewrite AB. rewrite AB0 in Xbev. rewrite !length_app in *. cbn [length] in *. lia.
- lia.
- cbn [st_cache_inited set_qthread]. intros _. destruct QI' as [Q|Q]; [exact (Xqi Q) | exact Q].
- intros c Hc. eapply fa_room_xfer; [exact (Xroom c Hc) | | apply Z.le_refl].
cbn [st_nev set_qthread]. unfold class_elems. change (reg (set_qthread q' s) c) with (reg s c). change (cache (set_qthread q' s) c) with (cache s c).
change (chunk_offs (set_qthread q' s) c) with (chunk_offs s c).
destruct (Z.eq_dec c kBatchClass) as [->|Hne].
+ rewrite !length_app, (Permutation_length PB), length_app, length_map, !bslack_24. destruct nb; cbn [length]; lia.
+ rewrite !(batch_offs_other (set_qthread q' s)), !(batch_offs_other s), !bslack_other by exact Hne. lia.
Qed.
Definition enqueue_post (U : Univ) (pp cc bb : Z) (s : astate) (kq : chunk) (ns : bool) (res : unit * astate) : Prop :=
let s' := snd res in
WfP U (pp - 1) cc (bb - 1) s' /\ st_chunks s' = st_chunks s /\ st_secs s' = st_secs s /\ st_sec_arr s' = st_sec_arr s /\
st_sec_reserved s' = st_sec_reserved s /\ st_fs s' = st_fs s /\ st_depot s' = st_depot s /\ st_nev s' = st_nev s /\
(exists nb, st_qthread s' = qc_push (st_qthread s) kq nb /\ (nb = None -> need_new_batch (st_qthread s) = false)) /\
st_qglobal s' = st_qglobal s.
Definition enqueue_postx (U : Univ) (pp cc bb : Z) (s : astate) (kq : chunk) (ns : bool) (res : unit * astate) : Prop :=
enqueue_post U pp cc bb s kq ns res /\
(forall c', 1 <= c' <= 31 -> cdef (snd res) c' = cdef s c') /\
(cdef s kBatchClass = 0 -> nrecZ s kBatchClass + 10248 <= 65536 -> BigP s -> BigP (snd res)).
Lemma length_qc_push_none : forall q k, length (qc_list (qc_push q k None)) = length (qc_list q).
Proof.
intros q k. cbn [qc_push qc_list]. rewrite <- (length_rev (qc_list q)). destruct (rev (qc_list q)) as [|lastb initr]; [reflexivity|].
rewrite length_app, length_rev. cbn [length]. lia.
Qed.
Lemma enqueue_okx : forall U pp cc bb s kq ns,
WfP U pp cc bb s -> 1 <= pp -> 1 <= bb ->
In kq (st_chunks s) -> ck_state kq = CQuarantined -> ~ In (ck_beg kq) (map ck_beg (q_items s)) ->
preg s kBatchClass ->
atok ns (enqueue kq s) (enqueue_postx U pp cc bb s kq).
Proof.
intros U pp cc bb s kq ns W Hpp Hbb Hk Hst Hni Hreg.
unfold enqueue. apply atok_bind. apply atok_get. cbn [fst snd]. apply atok_bind.
destruct (need_new_batch (st_qthread s)) eqn:NB.
- apply atok_bind. eapply atok_mono; [|apply (cache_alloc_okx U pp cc bb s kBatchClass ns W ltac:(unfold kBatchClass; lia) Hpp Hreg)].
intros ns2 [o s2] ((W2 & RO2 & Hi2 & Ho) & DEF2 & BIG2). cbn [fst snd] in DEF2, BIG2 |- *.
destruct RO2 as (Rck & Rsecs & Rarr & Rres & Rqt & Rqg & Rfs & Rdep & Rii & Rnev).
destruct o as [off|].
+ apply atok_ret. apply atok_modify. cbn [fst snd]. unfold enqueue_postx. cbn [snd]. split; [|split].
* split; [|cbn; rewrite ?Rck, ?Rsecs, ?Rarr, ?Rres, ?Rfs, ?Rdep, ?Rnev, ?Rqt, ?Rqg; splits; try reflexivity; exists (Some off); split; [reflexivity | intros; discriminate]].
apply WfP_qpush; [exact W2 | lia | rewrite Rck; exact Hk | exact Hst | | | exact Hi2 | intros _; rewrite Rqt; exact NB].
-- unfold q_items, all_batches. rewrite Rqt, Rqg. exact Hni.
-- destruct Ho as (x & -> & Hx32 & Hxa & Hxm & Hxni). exists x. splits; auto; lia.
*
intros c' Hc'. rewrite <- (Z.add_0_r (cdef s c')).
replace 0 with ((if c' =? kBatchClass then class_size kBatchClass else 0) - (if c' =? kBatchClass then class_size kBatchClass else 0)) by lia.
rewrite Z.add_sub_assoc, <- (DEF2 c' Hc'). unfold cdef, class_elems.
change (reg (set_qthread ?[q] s2) c') with (reg s2 c'). change (cache (set_qthread ?[q] s2) c') with (cache s2 c').
change (chunk_offs (set_qthread ?[q] s2) c') with (chunk_offs s2 c').
unfold batch_offs, all_batches. cbn [st_qthread st_qglobal set_qthread qc_push qc_list].
destruct (Z.eqb_spec c' kBatchClass) as [->|Hne]; [|lia].
rewrite !length_app, !length_map, !length_app. cbn [length]. rewrite !Nat2Z.inj_add. lia.
* intros D0 HR HB c' Hc'. change (reg (set_qthread ?[q] s2) c') with (reg s2 c'). exact (BIG2 D0 HR HB c' Hc').
+ subst ns2. apply atok_spin.
- apply atok_ret. cbn [fst snd]. apply atok_modify. cbn [fst snd]. unfold enqueue_postx. cbn [snd]. split; [|split].
+ split; [|cbn; splits; try reflexivity; exists None; split; [reflexivity | intros _; exact NB]].
pose proof (wf_slack _ _ _ _ _ W). apply (WfP_weaken U pp cc (bb - 1)); [|lia|lia|lia].
apply WfP_qpush; [exact W | lia | exact Hk | exact Hst | exact Hni | exact NB | exact I | intros HNN; exfalso; apply HNN; reflexivity].
+ intros c' Hc'. apply cdef_ext; [reflexivity|]. unfold class_elems.
change (reg (set_qthread ?[q] s) c') with (reg s c'). change (cache (set_qthread ?[q] s) c') with (cache s c').
change (chunk_offs (set_qthread ?[q] s) c') with (chunk_offs s c').
unfold batch_offs, all_batches. cbn [st_qthread st_qglobal set_qthread].
destruct (c' =? kBatchClass); [|reflexivity]. rewrite !length_app, !length_map, !length_app, length_qc_push_none. reflexivity.
+ intros _ _ HB c' Hc'. exact (HB c' Hc').
Qed.
Lemma enqueue_ok : forall U pp cc bb s kq ns,
WfP U pp cc bb s -> 1 <= pp -> 1 <= bb ->
In kq (st_chunks s) -> ck_state kq = CQuarantined -> ~ In (ck_beg kq) (map ck_beg (q_items s)) ->
preg s kBatchClass ->
atok ns (enqueue kq s) (enqueue_post U pp cc bb s kq).
Proof.
intros U pp cc bb s kq ns W Hpp Hbb Hk Hst Hni Hreg.
eapply atok_mono; [|exact (enqueue_okx U pp cc bb s kq ns W Hpp Hbb Hk Hst Hni Hreg)]. intros b r (H & _). exact H.
Qed.
Lemma WfP_transfer : forall U pp cc bb s,
WfP U pp cc bb s ->
kQuarantineCacheMax < qc_bytes (st_qthread s) ->
let g := mkQC (qc_list (st_qglobal s) ++ qc_list (st_qthread s)) (qc_bytes (st_qglobal s) + qc_bytes (st_qthread s)) in
WfP U pp cc bb (set_qglobal g (set_qthread qc0 s)).
Proof.
intros U pp cc bb s W Hover g. subst g. set (g := mkQC _ _).
wf_fields W. quar_fields Xq.
assert (PB : Permutation (all_batches (set_qglobal g (set_qthread qc0 s))) (all_batches s)).
{ unfold all_batches. cbn. apply Permutation_app_comm. }
assert (PQ : Permutation (q_items (set_qglobal g (set_qthread qc0 s))) (q_items s)).
{ unfold q_items, all_batches in *. cbn in *. rewrite !flat_map_app. apply Permutation_app_comm. }
constructor; wf_easy.
- intros c Hc. unfold wf_class. cbn [st_cache_inited set_qglobal set_qthread].
change (reg (set_qglobal g (set_qthread qc0 s)) c) with (reg s c). change (cache (set_qglobal g (set_qthread qc0 s)) c) with (cache s c).
rewrite (chunk_offs_begs s) by reflexivity. pose proof (Xcl c Hc) as C. unfold wf_class in C.
destruct (Z.eq_dec c kBatchClass) as [->|Hne].
+ eapply cls_ok_rebatch; [exact C|]. apply Permutation_app_head. rewrite !batch_offs_24. apply Permutation_map. apply Permutation_sym. exact PB.
+ rewrite !batch_offs_other in * by exact Hne. exact C.
- constructor; subst g; cbn [st_qthread st_qglobal st_chunks set_qglobal set_qthread qc0 qc_bytes qc_list]; try assumption.
+ reflexivity.
+ rewrite sum_bytes_app. lia.
+ eapply Forall_Permutation; [apply Permutation_sym; exact PB | exact Qbat].
+ eapply Forall_Permutation; [apply Permutation_sym; exact PQ | exact Qit].
+ eapply NoDup_Permutation; [apply Permutation_map; apply Permutation_sym; exact PQ | exact Qnd].
+ constructor.
+
destruct Qgr as (F & GS & EG & FF & FG). exists F, (GS ++ [qc_list (st_qthread s)]).
rewrite EG, concat_app. cbn [concat]. rewrite app_nil_r, <- app_assoc. split; [reflexivity|]. split; [exact FF|].
apply Forall_app. split; [exact FG|]. constructor; [|constructor]. unfold qgroup_ok. rewrite <- Qbt. split; [|split; [exact Qtf | exact Hover]].
intros E. rewrite Qbt, E in Hover. cbn in Hover. unfold kQuarantineCacheMax in Hover. lia.
- cbn [st_nev set_qglobal set_qthread]. rewrite (Permutation_length PB). exact Xbev.
- cbn [st_cache_inited set_qglobal set_qthread]. intros NE. apply Xqi. intros E. apply NE.
apply Permutation_sym in PB. rewrite E in PB. apply Permutation_nil in PB. exact PB.
- apply (wf_fa_room_ext s _ (fun c0 => cc + bslack c0 bb)); [ | reflexivity | reflexivity | exact Xroom].
intros c Hc. unfold class_elems. change (reg (set_qglobal g (set_qthread qc0 s)) c) with (reg s c).
change (cache (set_qglobal g (set_qthread qc0 s)) c) with (cache s c). change (chunk_offs (set_qglobal g (set_qthread qc0 s)) c) with (chunk_offs s c).
rewrite !length_app. destruct (Z.eq_dec c kBatchClass) as [->|Hne].
+ rewrite !batch_offs_24, !length_map, (Permutation_length PB). reflexivity.
+ rewrite !(batch_offs_other (set_qglobal g (set_qthread qc0 s))), !(batch_offs_other s) by exact Hne. reflexivity.
Qed.
Lemma pop_batches_spec : forall fuel q acc q' pop,
pop_batches fuel q acc = (q', pop) ->
exists P, pop = rev acc ++ P /\ qc_list q = P ++ qc_list q' /\ qc_bytes q' = qc_bytes q - sum_bytes P.
Proof.
induction fuel as [|f IH]; intros q acc q' pop H; cbn [pop_batches] in H.
- injection H as <- <-. exists []. rewrite !app_nil_r. cbn. splits; [reflexivity | reflexivity | lia].
- destruct (qc_bytes q <=? kQuarantineMin).
+ injection H as <- <-. exists []. rewrite !app_nil_r. cbn. splits; [reflexivity | reflexivity | lia].
+ remember (qc_list q) as L eqn:El. destruct L as [|b t].
* injection H as <- <-. exists []. cbn. splits; [rewrite app_nil_r; reflexivity | rewrite <- El; reflexivity | lia].
* apply IH in H as (P & -> & E2 & E3). cbn [qc_list qc_bytes] in E2, E3. exists (b :: P). cbn [rev]. rewrite <- app_assoc. cbn [app].
splits; [reflexivity | rewrite E2; reflexivity | unfold sum_bytes in *; cbn [fold_right]; lia].
Qed.
Lemma pop_batches_stop : forall fuel q acc q' pop,
pop_batches fuel q acc = (q', pop) -> (length (qc_list q) < fuel)%nat ->
qc_bytes q' <= kQuarantineMin \/ qc_list q' = [].
Proof.
induction fuel as [|f IH]; intros q acc q' pop H Hlen; cbn [pop_batches] in H; [lia|].
destruct (Z.leb_spec (qc_bytes q) kQuarantineMin) as [Hle|Hgt].
- injection H as <- <-. left. exact Hle.
- destruct (qc_list q) as [|b t] eqn:El.
+ injection H as <- <-. right. exact El.
+ apply (IH _ _ _ _ H). cbn [qc_list]. cbn [length] in Hlen. lia.
Qed.
Definition RI (U : Univ) (pp cc bb : Z) (s : astate) (P : list batch) : Prop :=
WfP U pp cc bb s /\
Forall (fun k => In k (st_chunks s) /\ ck_state k = CQuarantined) (flat_map b_items P) /\
NoDup (map ck_beg (flat_map b_items P ++ q_items s)) /\
Forall (fun b => (1 <= length (b_items b) <= Z.to_nat kBatchSlots)%nat) P /\
Forall (fun b => 0 <= b_self b - region_off kBatchClass < rg_alloc_user (reg s kBatchClass) /\
(b_self b - region_off kBatchClass) mod class_size kBatchClass = 0 /\
~ In (b_self b - region_off kBatchClass) (class_elems s kBatchClass)) P /\
NoDup (map b_self P) /\
fa_room (rg_alloc_user (reg s kBatchClass)) (length (class_elems s kBatchClass) + length P)
(cc + bb + 2 * (EV_MAX - st_nev s)) (rg_mapped_fa (reg s kBatchClass)).
Lemma perm_insert4 : forall (F Pc K T P R : list Z),
Permutation (F ++ Pc ++ K ++ (T ++ P ++ R)) (P ++ F ++ Pc ++ K ++ (T ++ R)).
Proof.
intros. eapply Permutation_trans; [|eapply Permutation_trans; [apply (Permutation_app_swap_app (F ++ Pc ++ K ++ T) P R)|]];
rewrite <- ?app_assoc; apply Permutation_refl.
Qed.
Lemma groups_drop : forall (P rest F : list batch) (GS : list (list batch)),
P ++ rest = F ++ concat GS -> Forall bfull (removelast F) -> Forall qgroup_ok GS ->
exists F' GS', rest = F' ++ concat GS' /\ Forall bfull (removelast F') /\ Forall qgroup_ok GS'.
Proof.
induction P as [|b P IH]; intros rest F GS E FF FG.
- exists F, GS. cbn [app] in E. auto.
- destruct F as [|b' F0].
+ destruct GS as [|g GS0]; [cbn in E; discriminate|]. inversion FG as [|g' GS' (GN & GF & _) FG0]; subst.
destruct g as [|b0 g0]; [exfalso; apply GN; reflexivity|]. cbn [app concat] in E. injection E as _ E.
apply (IH rest g0 GS0 E); [exact (Forall_removelast_tl _ _ _ GF) | exact FG0].
+ cbn [app] in E. injection E as _ E. apply (IH rest F0 GS E); [exact (Forall_removelast_tl _ _ _ FF) | exact FG].
Qed.
Lemma RI_pop : forall U pp cc bb s P rest,
WfP U pp cc bb s -> qc_list (st_qglobal s) = P ++ rest ->
RI U pp cc bb (set_qglobal (mkQC rest (qc_bytes (st_qglobal s) - sum_bytes P)) s) P.
Proof.
intros U pp cc bb s P rest W EP. wf_fields W. quar_fields Xq.
set (s' := set_qglobal _ s).
assert (AB : all_batches s = qc_list (st_qthread s) ++ P ++ rest) by (unfold all_batches; rewrite EP; reflexivity).
assert (AB' : all_batches s' = qc_list (st_qthread s) ++ rest) by reflexivity.
assert (PB : Permutation (P ++ all_batches s') (all_batches s)). { rewrite AB, AB'. apply Permutation_app_swap_app. }
assert (PQ : Permutation (flat_map b_items P ++ q_items s') (q_items s)).
{ unfold q_items. rewrite <- flat_map_app. apply Permutation_flat_map. exact PB. }
pose proof (Xcl kBatchClass ltac:(unfold kBatchClass; lia)) as C24. unfold wf_class in C24.
assert (PE : Permutation (fa_elems (class_size kBatchClass) (rg_free (reg s kBatchClass)) ++ pc_chunks (cache s kBatchClass) ++ chunk_offs s kBatchClass ++ batch_offs s kBatchClass)
(map (fun b => b_self b - region_off kBatchClass) P ++ class_elems s' kBatchClass)).
{ unfold class_elems. subst s'. cbn [set_qglobal]. change (reg (set_qglobal ?g s) ?c) with (reg s c). change (cache (set_qglobal ?g s) ?c) with (cache s c).
rewrite (chunk_offs_begs s (set_qglobal _ s)) by reflexivity. rewrite !batch_offs_24, AB', AB, !map_app. apply perm_insert4. }
split; [|split; [|split; [|split; [|split; [|split]]]]].
- constructor; wf_easy.
+ intros c Hc. unfold wf_class. subst s'. cbn [st_cache_inited set_qglobal].
change (reg (set_qglobal ?g s) c) with (reg s c). change (cache (set_qglobal ?g s) c) with (cache s c).
rewrite (chunk_offs_begs s) by reflexivity. pose proof (Xcl c Hc) as C. unfold wf_class in C.
destruct (Z.eq_dec c kBatchClass) as [->|Hne].
* eapply (cls_ok_repart _ _ _ _ _ _ _ _ _ _ _ (map (fun b => b_self b - region_off kBatchClass) P)); try reflexivity;
[exact C | exact (wr_runs _ _ _ _ _ _ C) | exact (wr_fa_len _ _ _ _ _ _ C) | exact (wr_cache _ _ _ _ _ _ C) |].
unfold class_elems in PE. exact PE.
* rewrite !batch_offs_other in * by exact Hne. exact C.
+ constructor; subst s'; cbn [st_qthread st_qglobal st_chunks set_qglobal qc_bytes qc_list]; try assumption.
* rewrite Qbg, EP, sum_bytes_app. lia.
* eapply (proj1 (Forall_app _ P _)). eapply Forall_Permutation; [apply Permutation_sym; exact PB | exact Qbat].
* eapply (proj1 (Forall_app _ (flat_map b_items P) _)). eapply Forall_Permutation; [apply Permutation_sym; exact PQ | exact Qit].
* pose proof (NoDup_Permutation _ _ (Permutation_map ck_beg (Permutation_sym PQ)) Qnd) as ND. rewrite map_app in ND.
apply NoDup_app_iff in ND as (_ & ND & _). exact ND.
* destruct Qgr as (F & GS & EG & FF & FG). rewrite EP in EG. exact (groups_drop P rest F GS EG FF FG).
+ subst s'. cbn [st_nev set_qglobal]. pose proof (Permutation_length PB) as L. rewrite length_app in L. lia.
+ subst s'. cbn [st_cache_inited set_qglobal]. intros NE. apply Xqi. rewrite AB, AB' in *. intros E. apply NE.
apply app_eq_nil in E as [E1 E2]. apply app_eq_nil in E2 as [_ E3]. rewrite E1, E3. reflexivity.
+ subst s'. intros c Hc. change (reg (set_qglobal ?g s) c) with (reg s c). cbn [st_nev set_qglobal].
destruct (Z.eq_dec c kBatchClass) as [->|Hne].
* eapply fa_room_xfer; [exact (Xroom kBatchClass Hc) | | apply Z.le_refl].
pose proof (Permutation_length PE) as L. rewrite (length_app (map _ P)), length_map in L.
change (length (fa_elems _ _ ++ _)) with (length (class_elems s kBatchClass)) in L. rewrite ?bslack_24. lia.
* eapply fa_room_xfer; [exact (Xroom c Hc) | | apply Z.le_refl]. unfold class_elems.
change (reg (set_qglobal ?g s) c) with (reg s c). change (cache (set_qglobal ?g s) c) with (cache s c).
rewrite (chunk_offs_begs s (set_qglobal _ s)) by reflexivity.
rewrite !(batch_offs_other (set_qglobal _ s)), !(batch_offs_other s) by exact Hne. apply Z.le_refl.
- apply Forall_forall. intros k Hk.
pose proof (proj1 (Forall_forall _ _) Qit k ltac:(eapply Permutation_in; [exact PQ | apply in_app_iff; left; exact Hk])) as [H1 H2]. subst s'. cbn. auto.
- eapply NoDup_Permutation; [apply Permutation_map; apply Permutation_sym; exact PQ | exact Qnd].
- pose proof (Forall_Permutation _ _ _ (Permutation_sym PB) Qbat) as FB. apply Forall_app in FB as [FB _]. exact FB.
- pose proof (Forall_Permutation _ _ _ PE (wr_elems _ _ _ _ _ _ C24)) as FE. apply Forall_app in FE as [FE _].
pose proof (Permutation_NoDup PE (wr_nodup _ _ _ _ _ _ C24)) as ND. apply NoDup_app_iff in ND as (ND1 & _ & ND3).
apply Forall_forall. intros b Hb.
pose proof (proj1 (Forall_forall _ _) FE _ (in_map (fun b => b_self b - region_off kBatchClass) _ _ Hb)) as [E1 E2].
change (reg s' kBatchClass) with (reg s kBatchClass). split; [exact E1 | split; [exact E2|]].
intros Hin. exact (ND3 _ (in_map (fun b => b_self b - region_off kBatchClass) _ _ Hb) Hin).
- pose proof (Permutation_NoDup PE (wr_nodup _ _ _ _ _ _ C24)) as ND. apply NoDup_app_iff in ND as (ND1 & _).
rewrite boffs_map in ND1. apply NoDup_map_inv in ND1. exact ND1.
- subst s'. change (reg (set_qglobal ?g s) kBatchClass) with (reg s kBatchClass). cbn [st_nev set_qglobal].
eapply fa_room_xfer; [exact (Xroom kBatchClass ltac:(unfold kBatchClass; lia)) | | apply Z.le_refl].
pose proof (Permutation_length PE) as L. rewrite (length_app (map _ P)), length_map in L.
change (length (fa_elems _ _ ++ _)) with (length (class_elems s kBatchClass)) in L. rewrite Nat2Z.inj_add, ?bslack_24. lia.
Qed.
Lemma reg_upd_pc : forall c p s c', reg (upd_pc c p s) c' = reg s c'. Proof. reflexivity. Qed.
Lemma chunk_offs_upd_pc : forall c p s c', chunk_offs (upd_pc c p s) c' = chunk_offs s c'. Proof. reflexivity. Qed.
Lemma batch_offs_upd_pc : forall c p s c', batch_offs (upd_pc c p s) c' = batch_offs s c'. Proof. reflexivity. Qed.
Lemma chunk_offs_upd_reg : forall c r s c', chunk_offs (upd_reg c r s) c' = chunk_offs s c'. Proof. reflexivity. Qed.
Lemma batch_offs_upd_reg : forall c r s c', batch_offs (upd_reg c r s) c' = batch_offs s c'. Proof. reflexivity. Qed.
Lemma cache_upd_reg : forall c r s c', cache (upd_reg c r s) c' = cache s c'. Proof. reflexivity. Qed.
Lemma cache_upd_pc_other : forall c c' p s, 0 <= c -> 0 <= c' -> c <> c' -> cache (upd_pc c p s) c' = cache s c'.
Proof. intros c c' p s H1 H2 H3. unfold upd_pc, cache. cbn [st_cache set_cache]. apply znth_zupd_other; lia. Qed.
Lemma class_elems_upd_pc_same : forall c p s, 0 <= c -> (Z.to_nat c < length (st_cache s))%nat ->
class_elems (upd_pc c p s) c = fa_elems (class_size c) (rg_free (reg s c)) ++ pc_chunks p ++ chunk_offs s c ++ batch_offs s c.
Proof. intros c p s Hc Hl. unfold class_elems. rewrite cache_upd_pc by (exact Hc || exact Hl). reflexivity. Qed.
Lemma class_elems_upd_pc_other : forall c c' p s, 0 <= c -> 0 <= c' -> c <> c' -> class_elems (upd_pc c p s) c' = class_elems s c'.
Proof. intros c c' p s H1 H2 H3. unfold class_elems. rewrite cache_upd_pc_other by assumption. reflexivity. Qed.
Lemma class_elems_upd_reg_other : forall c c' r s, 0 <= c -> 0 <= c' -> c <> c' -> class_elems (upd_reg c r s) c' = class_elems s c'.
Proof. intros c c' r s H1 H2 H3. unfold class_elems. rewrite reg_upd_reg_other by assumption. reflexivity. Qed.
Lemma class_elems_count : forall U pp cc bb s c, WfP U pp cc bb s -> 1 <= c <= 31 ->
32 * (fa_len (rg_free (reg s c)) + Z.of_nat (length (pc_chunks (cache s c)))) <= rg_alloc_user (reg s c) /\
rg_alloc_user (reg s c) < kFreeArrayOffset.
Proof.
intros U pp cc bb s c W Hc. pose proof (class_ok c Hc) as (Ksz & K32 & _).
pose proof (wf_classes _ _ _ _ _ W c Hc) as C. unfold wf_class in C.
pose proof (wr_nodup _ _ _ _ _ _ C) as ND. pose proof (wr_elems _ _ _ _ _ _ C) as EL. pose proof (wr_runs _ _ _ _ _ _ C) as R.
pose proof (wr_alloc _ _ _ _ _ _ C) as A. pose proof (wr_alloc_al _ _ _ _ _ _ C) as AL.
rewrite app_assoc in ND, EL. apply NoDup_app_iff in ND as (ND & _ & _). apply Forall_app in EL as [EL _].
pose proof (multiples_bound (class_size c) (rg_alloc_user (reg s c)) _ Ksz ltac:(lia) AL ND EL) as MB.
rewrite length_app, Nat2Z.inj_add in MB. rewrite <- (fa_elems_length (class_size c)) by exact R.
pose proof (mapped_user_le_free_array U pp cc bb s c W Hc). pose proof (wf_slack _ _ _ _ _ W).
assert (K32' : 32 <= class_size c). { apply Z.mod_divide in K32 as [k Hk]; [nia | lia]. }
pose proof (fa_len_nonneg _ R). cbv beta in *. nia.
Qed.
Lemma cls_ok_add_pc : forall c r p ko bo x,
cls_ok c r p true ko bo ->
~ In x (fa_elems (class_size c) (rg_free r) ++ pc_chunks p ++ ko ++ bo) ->
0 <= x < rg_alloc_user r -> x mod class_size c = 0 ->
Z.of_nat (length (pc_chunks p)) + 1 <= max_cached c ->
cls_ok c r (mkPC (pc_max p) (pc_chunks p ++ [x])) true ko bo.
Proof.
intros c r p ko bo x C Hni Hx Hm Hlen.
pose proof (cls_ok_add_ko c r p true ko bo x C Hni Hx Hm) as C'.
eapply (cls_ok_repart c r p true (ko ++ [x]) bo r _ true ko bo []); try reflexivity;
[exact C' | exact (wr_runs _ _ _ _ _ _ C) | exact (wr_fa_len _ _ _ _ _ _ C) | |].
- cbn [pc_max pc_chunks]. pose proof (wr_cache _ _ _ _ _ _ C) as [PM PL]. rewrite length_app. cbn [length]. split; [exact PM | lia].
- cbn [app pc_chunks]. apply Permutation_app_head. rewrite <- !app_assoc. apply Permutation_app_head. cbn [app].
apply Permutation_sym. apply Permutation_middle.
Qed.
Definition cache_dealloc_post (U : Univ) (pp cc bb : Z) (s : astate) (c x : Z) (ns : bool) (res : unit * astate) : Prop :=
let s' := snd res in
WfP U pp cc bb s' /\ regs_only s s' /\
(forall c', 0 <= c' <= 31 -> rg_alloc_user (reg s' c') = rg_alloc_user (reg s c')) /\
(forall c' y, 0 <= c' <= 31 -> In y (class_elems s' c') -> (y = x /\ c' = c) \/ In y (class_elems s c')) /\
(forall c', 0 <= c' <= 31 -> rg_mapped_fa (reg s c') <= rg_mapped_fa (reg s' c')) /\
(forall c', 0 <= c' <= 31 -> length (class_elems s' c') = (length (class_elems s c') + (if (c' =? c)%Z then 1 else 0))%nat).
Lemma cache_dealloc_ok : forall U pp cc bb s c off ns,
WfP U pp cc bb s -> 1 <= c <= 31 ->
0 <= off - region_off c < rg_alloc_user (reg s c) -> (off - region_off c) mod class_size c = 0 ->
~ In (off - region_off c) (class_elems s c) ->
4 * (Z.of_nat (length (class_elems s c)) + 1 + (cc + bslack c bb + 2 * (EV_MAX - st_nev s))) <= rg_mapped_fa (reg s c) ->
atok ns (cache_dealloc c off s) (cache_dealloc_post U pp cc bb s c (off - region_off c)).
Proof.
intros U pp cc bb s c off ns W Hc Hx Hxm Hxni HROOM. set (x := off - region_off c) in *.
pose proof (class_ok c Hc) as (Ksz & K32 & Kmax & Kmc & Kmc2 & Kmcs).
unfold cache_dealloc. apply atok_bind. unfold init_cache_if_needed. apply atok_bind. apply atok_get. cbn [fst snd].
assert (STEP1 : forall s1, WfP U pp cc bb s1 -> st_cache_inited s1 = true -> regs_only s s1 -> st_regions s1 = st_regions s ->
(forall c', 0 <= c' <= 31 -> pc_chunks (cache s1 c') = pc_chunks (cache s c')) ->
atok ns ((p <- get_pc c ;;
(if Z.of_nat (length (pc_chunks p)) =? pc_max p
then return_to_allocator c (skipn (length (pc_chunks p) - Z.to_nat (pc_max p / 2)) (pc_chunks p)) ;;
set_pc c (mkPC (pc_max p) (firstn (length (pc_chunks p) - Z.to_nat (pc_max p / 2)) (pc_chunks p)))
else ret tt) ;;
p <- get_pc c ;; set_pc c (mkPC (pc_max p) (pc_chunks p ++ [x]))) s1)
(cache_dealloc_post U pp cc bb s c x)).
2:{ destruct (st_cache_inited s) eqn:Ei.
- apply atok_ret. apply (STEP1 s W Ei (regs_only_refl s) eq_refl). intros; reflexivity.
- apply atok_put. apply STEP1; [apply WfP_init_caches; [exact W | exact Ei] | reflexivity | unfold regs_only; cbn; repeat split; reflexivity | reflexivity |].
intros c' Hc'. cbn [snd]. rewrite cache_after_init by exact Hc'. reflexivity. }
intros s1 W1 Hi1 RO1 ER1 EC1.
assert (HL : (Z.to_nat c < length (st_regions s1))%nat) by (eapply WfP_len_regions; [exact W1 | lia]).
assert (HLc : (Z.to_nat c < length (st_cache s1))%nat) by (eapply WfP_len_cache; [exact W1 | lia]).
assert (EREG : forall c', reg s1 c' = reg s c') by (intros c'; unfold reg; rewrite ER1; reflexivity).
assert (ECE : forall c', 0 <= c' <= 31 -> class_elems s1 c' = class_elems s c').
{ intros c' Hc'. unfold class_elems. rewrite EREG, EC1 by exact Hc'. destruct RO1 as (Rck & _ & _ & _ & Rqt & Rqg & _).
rewrite (chunk_offs_begs s s1) by (rewrite Rck; reflexivity). unfold batch_offs, all_batches. rewrite Rqt, Rqg. reflexivity. }
pose proof (wf_classes _ _ _ _ _ W1 c Hc) as C1. unfold wf_class in C1. rewrite Hi1 in C1. pose proof (wr_cache _ _ _ _ _ _ C1) as [PM1 PL1].
assert (PUSH : forall ns4 s4 p4, WfP U pp cc bb s4 -> st_cache_inited s4 = true -> regs_only s s4 ->
(forall c', 0 <= c' <= 31 -> rg_alloc_user (reg s4 c') = rg_alloc_user (reg s c')) ->
cache s4 c = p4 -> Permutation (class_elems s4 c) (class_elems s c) ->
(forall c', 0 <= c' <= 31 -> c' <> c -> class_elems s4 c' = class_elems s c') ->
pc_max p4 = max_cached c -> Z.of_nat (length (pc_chunks p4)) + 1 <= max_cached c ->
(Z.to_nat c < length (st_cache s4))%nat ->
(forall c', 0 <= c' <= 31 -> rg_mapped_fa (reg s c') <= rg_mapped_fa (reg s4 c')) ->
atok ns4 ((p <- get_pc c ;; set_pc c (mkPC (pc_max p) (pc_chunks p ++ [x]))) s4) (cache_dealloc_post U pp cc bb s c x)).
{ intros ns4 s4 p4 W4 Hi4 RO4 AU4 EC4 P4 OC4 PM4 PL4 HLc4 MFA4. pose proof (MFA4 c ltac:(lia)) as MF4.
apply atok_bind. apply atok_get_pc. cbn [fst snd]. rewrite EC4. apply atok_set_pc.
pose proof (wf_classes _ _ _ _ _ W4 c Hc) as C4. unfold wf_class in C4. rewrite EC4, Hi4 in C4.
split; [|split; [|split; [|split; [|split]]]].
- eapply WfP_set_pc; [exact W4 | exact Hc | |].
{ rewrite Hi4. apply cls_ok_add_pc; [exact C4 | | | exact Hxm | exact PL4].
+ intros Hin. apply Hxni. eapply Permutation_in; [exact P4|]. unfold class_elems. rewrite EC4. exact Hin.
+ rewrite AU4 by lia. exact Hx. }
right. cbn [pc_chunks]. pose proof (Permutation_length P4) as L4. unfold class_elems in L4, HROOM. rewrite EC4 in L4.
rewrite !length_app in L4. rewrite !length_app in HROOM. rewrite !length_app. cbn [length] in L4, HROOM |- *.
destruct RO4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & RN4). rewrite RN4. lia.
- destruct RO4 as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10). unfold regs_only, upd_pc. cbn. repeat split; assumption.
- intros c' Hc'. cbn [snd]. rewrite reg_upd_pc. apply AU4. exact Hc'.
- intros c' y Hc' Hin. cbn [snd] in Hin.
destruct (Z.eq_dec c c') as [<-|Hne].
+ rewrite class_elems_upd_pc_same in Hin by (lia || exact HLc4). cbn [pc_chunks] in Hin.
assert (Hin' : In y (class_elems s4 c ++ [x])).
{ unfold class_elems. rewrite EC4. rewrite !in_app_iff in Hin |- *. cbn [In] in *. tauto. }
apply in_app_iff in Hin' as [Hin'|[<-|[]]]; [right; eapply Permutation_in; [exact P4 | exact Hin'] | left; split; reflexivity].
+ right. rewrite class_elems_upd_pc_other in Hin by lia. rewrite <- (OC4 c') by lia. exact Hin.
- intros c' Hc'. cbn [snd]. rewrite reg_upd_pc. apply MFA4. exact Hc'.
- intros c' Hc'. cbn [snd]. destruct (Z.eq_dec c c') as [<-|Hne].
+ rewrite class_elems_upd_pc_same by (lia || exact HLc4). cbn [pc_chunks]. rewrite Z.eqb_refl.
pose proof (Permutation_length P4) as L4. unfold class_elems in L4 |- *. rewrite EC4 in L4.
rewrite !length_app in L4. rewrite !length_app. cbn [length] in L4 |- *. lia.
+ rewrite class_elems_upd_pc_other by lia. rewrite (OC4 c') by lia. destruct (Z.eqb_spec c' c); [lia | lia]. }
apply atok_bind. apply atok_get_pc. cbn [fst snd]. rewrite PM1.
destruct (Z.eqb_spec (Z.of_nat (length (pc_chunks (cache s1 c)))) (max_cached c)) as [FULL|NF].
-
set (l := pc_chunks (cache s1 c)) in *. set (n := max_cached c / 2).
assert (N1 : 1 <= n <= 8) by (subst n; split; [apply Z.div_le_lower_bound | apply Z.div_le_upper_bound]; lia).
assert (N3 : n + 1 <= max_cached c) by (subst n; pose proof (Z.mul_div_le (max_cached c) 2 ltac:(lia)); lia).
set (keep := firstn (length l - Z.to_nat n) l). set (drained := skipn (length l - Z.to_nat n) l).
assert (EL : l = keep ++ drained) by (subst keep drained; symmetry; apply firstn_skipn).
assert (LD : Z.of_nat (length drained) = n) by (subst drained; rewrite length_skipn; lia).
assert (LK : Z.of_nat (length keep) = max_cached c - n) by (subst keep; rewrite length_firstn; lia).
apply atok_bind. unfold return_to_allocator. apply atok_bind. apply atok_bind. apply atok_get_region. cbn [fst snd].
pose proof (class_elems_count U pp cc bb s1 c W1 Hc) as [CNT AFO]. unfold kFreeArrayOffset in AFO.
pose proof (wr_fa_len _ _ _ _ _ _ C1) as FL. pose proof (fa_len_nonneg _ (wr_runs _ _ _ _ _ _ C1)) as FL0.
apply atok_bind.
eapply atok_mono; [|apply (ensure_free_array_ok U pp cc bb s1 c (fa_len (rg_free (reg s1 c)) + Z.of_nat (length drained)) true ns W1 Hc)].
2:{ lia. } 2:{ unfold kFreeArrayMapSize. lia. } 2:{ unfold kFreeArrayMax. fold l in CNT. lia. }
intros ns2 [ok s2] (r2 & -> & W2 & M2 & A2 & F2 & FA2 & OK2 & NS2). cbn [fst snd].
destruct ok; [|destruct (NS2 eq_refl); discriminate]. specialize (OK2 eq_refl). clear NS2.
apply atok_bind. apply atok_get_region. rewrite reg_upd_reg by (lia || exact HL). cbn [fst snd].
apply atok_set_region. cbn [fst snd]. rewrite upd_reg_upd_reg. apply atok_set_pc.
set (R := mkRegion _ _ _ _ _).
pose proof (fa_push_list_spec (class_size c) (rg_free r2) drained) as (PE1 & PE2 & PE3).
pose proof (wf_classes _ _ _ _ _ W2 c Hc) as C2. unfold wf_class in C2.
rewrite reg_upd_reg, cache_upd_reg, chunk_offs_upd_reg, batch_offs_upd_reg in C2 by (lia || exact HL).
replace (st_cache_inited (upd_reg c r2 s1)) with true in C2 by (symmetry; exact Hi1).
assert (PERM : forall K B : list Z, Permutation (fa_elems (class_size c) (rg_free r2) ++ (keep ++ drained) ++ K ++ B)
((rev drained ++ fa_elems (class_size c) (rg_free r2)) ++ keep ++ K ++ B)).
{ intros K B. rewrite <- !app_assoc. rewrite (app_assoc (fa_elems (class_size c) (rg_free r2)) keep (drained ++ K ++ B)).
eapply Permutation_trans; [apply Permutation_app_swap_app|].
rewrite <- !app_assoc. apply Permutation_app; [apply Permutation_rev | apply Permutation_refl]. }
assert (W4 : WfP U pp cc bb (upd_pc c (mkPC (max_cached c) keep) (upd_reg c R s1))).
{ rewrite <- (upd_reg_upd_reg c r2 R s1). eapply (WfP_set_region_pc U pp cc bb (upd_reg c r2 s1) c R _ pp W2 Hc).
- replace (st_cache_inited (upd_reg c r2 s1)) with true by (symmetry; exact Hi1). rewrite chunk_offs_upd_reg, batch_offs_upd_reg.
eapply (cls_ok_repart c r2 (cache s1 c) true _ _ R _ true _ _ []); try exact C2; try reflexivity.
+ apply PE3. exact (wr_runs _ _ _ _ _ _ C2).
+ subst R. cbnr. rewrite PE2, F2. lia.
+ cbn [pc_max pc_chunks]. split; [reflexivity | lia].
+ cbn [app pc_chunks]. subst R. cbnr. rewrite PE1. fold l. rewrite EL. apply PERM.
- pose proof (wf_slack _ _ _ _ _ W2). lia.
- rewrite reg_upd_reg by (lia || exact HL). subst R. cbnr. pose proof (wf_prim_ev _ _ _ _ _ W2). lia.
-
pose proof (wf_fa_room _ _ _ _ _ W2 c Hc) as RM. unfold class_elems in RM.
rewrite reg_upd_reg, cache_upd_reg, chunk_offs_upd_reg, batch_offs_upd_reg in RM by (lia || exact HL).
rewrite chunk_offs_upd_reg, batch_offs_upd_reg. change (st_nev (upd_reg c r2 s1)) with (st_nev s1) in RM |- *.
subst R. cbnr. eapply fa_room_xfer; [exact RM | | apply Z.le_refl].
cbn [pc_chunks]. rewrite PE1. fold l. rewrite EL, !length_app, length_rev. lia.
-
apply (regime_cap_keep U pp cc bb (upd_reg c r2 s1) c _ W2 Hc); rewrite reg_upd_reg by (lia || exact HL); subst R; cbnr; [reflexivity | lia]. }
assert (HLc4 : (Z.to_nat c < length (st_cache (upd_pc c (mkPC (max_cached c) keep) (upd_reg c R s1))))%nat).
{ unfold upd_pc, upd_reg. cbn [st_cache set_cache set_regions]. rewrite zupd_length. exact HLc. }
apply (PUSH ns2 _ (mkPC (max_cached c) keep) W4); try reflexivity.
+ cbn [st_cache_inited upd_pc upd_reg set_cache set_regions]. exact Hi1.
+ destruct RO1 as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10). unfold regs_only, upd_pc, upd_reg. cbn. repeat split; assumption.
+ intros c' Hc'. rewrite reg_upd_pc. destruct (Z.eq_dec c c') as [<-|Hne].
* rewrite reg_upd_reg by (lia || exact HL). subst R. cbnr. rewrite A2, EREG. reflexivity.
* rewrite reg_upd_reg_other by lia. rewrite EREG. reflexivity.
+ apply cache_upd_pc; [lia | unfold upd_reg; cbn [st_cache set_regions]; exact HLc].
+ rewrite <- (ECE c) by lia. rewrite class_elems_upd_pc_same by (lia || unfold upd_reg; cbn [st_cache set_regions]; exact HLc).
rewrite reg_upd_reg, chunk_offs_upd_reg, batch_offs_upd_reg by (lia || exact HL). cbn [pc_chunks]. subst R. cbnr. rewrite PE1.
unfold class_elems. fold l. rewrite EL, <- F2. apply Permutation_sym. apply PERM.
+ intros c' Hc' Hne. rewrite class_elems_upd_pc_other, class_elems_upd_reg_other by lia. apply ECE. exact Hc'.
+ cbn [pc_chunks]. lia.
+ exact HLc4.
+ intros c' Hc'. rewrite reg_upd_pc. destruct (Z.eq_dec c c') as [<-|Hne].
* rewrite reg_upd_reg by (lia || exact HL). subst R. cbnr. rewrite <- EREG. exact FA2.
* rewrite reg_upd_reg_other by lia. rewrite EREG. apply Z.le_refl.
-
apply atok_bind. apply atok_ret. cbn [fst snd].
apply (PUSH ns s1 (cache s1 c) W1 Hi1 RO1); try reflexivity.
+ intros c' Hc'. rewrite EREG. reflexivity.
+ rewrite ECE by lia. apply Permutation_refl.
+ intros c' Hc' _. apply ECE. exact Hc'.
+ exact PM1.
+ lia.
+ exact HLc.
+ intros c' Hc'. rewrite EREG. apply Z.le_refl.
Qed.
Lemma chunk_offs_list_app : forall s l1 l2 c, chunk_offs (set_chunks (l1 ++ l2) s) c = chunk_offs (set_chunks l1 s) c ++ chunk_offs (set_chunks l2 s) c.
Proof. intros s l1 l2 c. unfold chunk_offs. cbn [st_chunks set_chunks]. rewrite flat_map_app. reflexivity. Qed.
Lemma chunk_offs_one : forall s k c, chunk_offs (set_chunks [k] s) c =
match ck_beg k with PPrim off => if prim_class off =? c then [off - region_off c] else [] | _ => [] end.
Proof. intros s k c. unfold chunk_offs. cbn. rewrite app_nil_r. reflexivity. Qed.
Lemma class_elems_del : forall s l1 k l2 c,
st_chunks s = l1 ++ k :: l2 ->
Permutation (class_elems s c) (chunk_offs (set_chunks [k] s) c ++ class_elems (set_chunks (l1 ++ l2) s) c).
Proof.
intros s l1 k l2 c E. unfold class_elems. rewrite reg_set_chunks, cache_set_chunks, batch_offs_set_chunks.
replace (chunk_offs s c) with (chunk_offs (set_chunks (l1 ++ k :: l2) s) c) by (rewrite <- E; destruct s; reflexivity).
change (k :: l2) with ([k] ++ l2). rewrite !chunk_offs_list_app.
set (F := fa_elems _ _). set (P := pc_chunks _). set (A := chunk_offs (set_chunks l1 s) c). set (X := chunk_offs (set_chunks [k] s) c).
set (B := chunk_offs (set_chunks l2 s) c). set (Q := batch_offs s c).
eapply Permutation_trans; [|eapply Permutation_trans; [apply (Permutation_app_swap_app (F ++ P ++ A) X (B ++ Q))|]];
rewrite <- ?app_assoc; apply Permutation_refl.
Qed.
Lemma WfP_del_prim : forall U pp cc bb s l1 k l2 off,
WfP U pp cc bb s -> st_chunks s = l1 ++ k :: l2 -> ck_beg k = PPrim off -> ck_state k = CQuarantined ->
~ In (ck_beg k) (map ck_beg (q_items s)) ->
WfP U pp cc bb (set_chunks (l1 ++ l2) s) /\
let c := prim_class off in let x := off - region_off c in
1 <= c <= 30 /\ 0 <= x < rg_alloc_user (reg s c) /\ x mod class_size c = 0 /\ ~ In x (class_elems (set_chunks (l1 ++ l2) s) c) /\
(forall c' y, In y (class_elems (set_chunks (l1 ++ l2) s) c') -> In y (class_elems s c')) /\
4 * (Z.of_nat (length (class_elems (set_chunks (l1 ++ l2) s) c)) + 1 + (cc + bslack c bb + 2 * (EV_MAX - st_nev s))) <= rg_mapped_fa (reg s c).
Proof.
intros U pp cc bb s l1 k l2 off W E Hb Hst Hni.
assert (Hk : In k (st_chunks s)) by (rewrite E; apply in_elt).
pose proof (prim_chunk_off U pp cc bb s k off W Hk Hb) as (G1 & G2 & G3 & G4 & G5 & G6). cbv zeta in *.
set (c := prim_class off) in *. set (x := off - region_off c) in *.
assert (X1 : chunk_offs (set_chunks [k] s) c = [x]) by (rewrite chunk_offs_one, Hb; fold c; rewrite Z.eqb_refl; reflexivity).
assert (X0 : forall c', c' <> c -> chunk_offs (set_chunks [k] s) c' = []).
{ intros c' Hc'. rewrite chunk_offs_one, Hb. fold c. destruct (Z.eqb_spec c c'); [lia | reflexivity]. }
wf_fields W. quar_fields Xq.
assert (ND : NoDup (map ck_beg (l1 ++ k :: l2))) by (rewrite <- E; exact Xnd).
pose proof (Xcl c ltac:(lia)) as C. unfold wf_class in C.
pose proof (class_elems_del s l1 k l2 c E) as PE. rewrite X1 in PE. cbn [app] in PE.
pose proof (wr_elems _ _ _ _ _ _ C) as EL. pose proof (wr_alloc _ _ _ _ _ _ C) as AL.
assert (INX : In x (class_elems s c)) by (eapply Permutation_in; [apply Permutation_sym; exact PE | left; reflexivity]).
pose proof (proj1 (Forall_forall _ _) EL x INX) as [Ex1 Ex2].
split; [|split; [lia | split; [lia | split; [exact Ex2 | split; [|split]]]]].
- constructor; wf_easy.
+ intros c' Hc'. unfold wf_class. rewrite reg_set_chunks, cache_set_chunks, batch_offs_set_chunks. cbn [st_cache_inited set_chunks].
pose proof (Xcl c' Hc') as C'. unfold wf_class in C'.
pose proof (class_elems_del s l1 k l2 c' E) as PE'. unfold class_elems in PE'. rewrite reg_set_chunks, cache_set_chunks, batch_offs_set_chunks in PE'.
eapply (cls_ok_repart c' _ _ _ _ _ _ _ _ _ _ (chunk_offs (set_chunks [k] s) c')); try reflexivity;
[exact C' | exact (wr_runs _ _ _ _ _ _ C') | exact (wr_fa_len _ _ _ _ _ _ C') | exact (wr_cache _ _ _ _ _ _ C') | exact PE'].
+ cbn [st_chunks set_chunks]. rewrite E in Xck. apply Forall_app in Xck as [X1' X2']. inversion X2'; subst.
apply Forall_app. split; [eapply Forall_chunk_ok_ext; [reflexivity | exact X1'] | eapply Forall_chunk_ok_ext; [reflexivity | eassumption]].
+ cbn [st_chunks set_chunks]. rewrite map_app in ND |- *. cbn [map] in ND. exact (NoDup_remove_1 _ _ _ ND).
+ cbn [st_chunks set_chunks st_nev]. rewrite E, !length_app in Xcev. rewrite length_app. cbn [length] in Xcev. lia.
+ rewrite blocks_bytes_eq in *. cbn [st_chunks set_chunks]. rewrite E, bbytes_split in Xlive. unfold is_alloc in Xlive. rewrite Hst in Xlive. lia.
+ constructor; cbn [st_qthread st_qglobal st_chunks set_chunks]; rewrite ?all_batches_set_chunks, ?q_items_set_chunks; try assumption.
apply Forall_forall. intros k' Hk'. pose proof (proj1 (Forall_forall _ _) Qit k' Hk') as [H1 H2]. split; [|exact H2].
rewrite E in H1. apply in_app_iff in H1 as [H1|[<-|H1]]; [apply in_app_iff; left; exact H1 | exfalso | apply in_app_iff; right; exact H1].
apply Hni. apply in_map. exact Hk'.
+ sec_fields Xsec. constructor; cbn [st_sec_arr st_secs st_chunks st_sec_reserved set_chunks]; try assumption.
intros r. rewrite Sac, E. split; intros (k' & Hk' & Hb'); apply in_app_iff in Hk' as [Hk'|Hk'].
* exists k'. split; [apply in_app_iff; left; exact Hk' | exact Hb'].
* destruct Hk' as [<-|Hk']; [congruence|]. exists k'. split; [apply in_app_iff; right; exact Hk' | exact Hb'].
* exists k'. split; [apply in_app_iff; left; exact Hk' | exact Hb'].
* exists k'. split; [apply in_app_iff; right; right; exact Hk' | exact Hb'].
+ intros c' Hc'. eapply fa_room_xfer; [exact (Xroom c' Hc') | | apply Z.le_refl]. cbn [st_nev set_chunks].
pose proof (Permutation_length (class_elems_del s l1 k l2 c' E)) as L'. rewrite length_app in L'. lia.
+
apply (regime_xfer _ _ s _ Xreg); [reflexivity | intros HBP; exact HBP | cbn [st_chunks set_chunks]; rewrite E, !length_app; cbn [length]; lia].
- pose proof (Permutation_NoDup PE (wr_nodup _ _ _ _ _ _ C)) as NDx. inversion NDx; subst. assumption.
- intros c' y Hy. destruct (Z.eq_dec c' c) as [->|Hne].
+ eapply Permutation_in; [apply Permutation_sym; exact PE | right; exact Hy].
+ pose proof (class_elems_del s l1 k l2 c' E) as PE'. rewrite (X0 c' Hne) in PE'. cbn [app] in PE'.
eapply Permutation_in; [apply Permutation_sym; exact PE' | exact Hy].
- destruct (Xroom c ltac:(lia)) as [Z0|R]; [lia|]. pose proof (Permutation_length PE) as L. cbn [length] in L. lia.
Qed.
Lemma index_of_spec : forall l r i0, In r l -> exists j, index_of l r i0 = Some (i0 + j)%nat /\ nth_error l j = Some r.
Proof.
induction l as [|y t IH]; intros r i0 Hin; [destruct Hin|]. cbn [index_of].
destruct (Nat.eqb_spec y r) as [->|Hne].
- exists 0%nat. rewrite Nat.add_0_r. split; reflexivity.
- destruct Hin as [->|Hin]; [congruence|]. destruct (IH r (S i0) Hin) as (j & E1 & E2).
exists (S j). rewrite E1. split; [f_equal; lia | exact E2].
Qed.
Lemma lupd_app_mid : forall {X} (a1 : list X) y a2 v, lupd (a1 ++ y :: a2) (length a1) v = a1 ++ v :: a2.
Proof. intros X a1. induction a1 as [|h t IH]; intros y a2 v; cbn; [reflexivity | rewrite IH; reflexivity]. Qed.
Lemma removelast_last' : forall {X} (l : list X) a, removelast (l ++ [a]) = l.
Proof.
intros X l a. induction l as [|h t IH]; [reflexivity|]. cbn [app removelast]. rewrite IH.
destruct t as [|h' t']; cbn; reflexivity.
Qed.
Lemma swap_remove_perm : forall (arr : list nat) i r,
nth_error arr i = Some r -> Permutation (r :: removelast (lupd arr i (last arr r))) arr.
Proof.
intros arr i r Hn.
destruct (nth_error_split arr i Hn) as (a1 & a2 & -> & <-).
destruct (list_eq_dec Nat.eq_dec a2 []) as [->|Hne].
- replace (last (a1 ++ [r]) r) with r by (rewrite last_last; reflexivity). rewrite lupd_app_mid, removelast_last'. apply Permutation_cons_append.
- pose proof (app_removelast_last r Hne) as E. set (z := last a2 r) in *. set (a2' := List.removelast a2) in *.
rewrite E. replace (last (a1 ++ r :: a2' ++ [z]) r) with z.
2:{ rewrite app_comm_cons, app_assoc, last_last. reflexivity. }
rewrite lupd_app_mid. replace (a1 ++ z :: a2' ++ [z]) with ((a1 ++ z :: a2') ++ [z]) by (rewrite <- app_assoc; reflexivity).
rewrite removelast_last'. apply Permutation_cons_app. apply Permutation_app_head. apply Permutation_cons_append.
Qed.
Lemma chunk_offs_del_sec : forall s l1 k l2 r o c, st_chunks s = l1 ++ k :: l2 -> ck_beg k = PSec r o ->
chunk_offs (set_chunks (l1 ++ l2) s) c = chunk_offs s c.
Proof.
intros s l1 k l2 r o c E Hb.
replace (chunk_offs s c) with (chunk_offs (set_chunks (l1 ++ k :: l2) s) c) by (rewrite <- E; destruct s; reflexivity).
change (k :: l2) with ([k] ++ l2). rewrite !chunk_offs_list_app, chunk_offs_one, Hb. reflexivity.
Qed.
Lemma Forall_lupd : forall {X} (P : X -> Prop) (l : list X) i v, Forall P l -> P v -> Forall P (lupd l i v).
Proof.
intros X P l. induction l as [|h t IH]; intros i v HF Hv; [destruct i; exact HF|].
inversion HF as [|? ? Hh Ht]; subst. destruct i as [|i]; cbn [lupd]; constructor; auto.
Qed.
Lemma WfP_del_sec : forall U pp cc bb s l1 k l2 r sm i,
WfP U pp cc bb s -> st_chunks s = l1 ++ k :: l2 -> ck_beg k = PSec r kPage -> ck_state k = CQuarantined ->
~ In (ck_beg k) (map ck_beg (q_items s)) ->
nth_error (st_secs s) r = Some sm -> nth_error (st_sec_arr s) i = Some r ->
WfP U pp cc bb (set_sec_arr (removelast (lupd (st_sec_arr s) i (last (st_sec_arr s) r)))
(set_secs (lupd (st_secs s) r (mkSec (sm_len sm) (sm_size sm) false)) (set_chunks (l1 ++ l2) s))).
Proof.
intros U pp cc bb s l1 k l2 r sm i W E Hb Hst Hni Hsm Hi.
assert (Hk : In k (st_chunks s)) by (rewrite E; apply in_elt).
wf_fields W. quar_fields Xq. sec_fields Xsec.
assert (ND : NoDup (map ck_beg (l1 ++ k :: l2))) by (rewrite <- E; exact Xnd).
rewrite map_app in ND. cbn [map] in ND. pose proof (NoDup_remove_1 _ _ _ ND) as ND'. apply NoDup_app_iff in ND as (NDa & NDb & NDc). inversion NDb; subst.
pose proof (swap_remove_perm _ _ _ Hi) as PA. set (arr' := removelast (lupd _ _ _)) in *.
assert (NDA : NoDup arr' /\ ~ In r arr').
{ pose proof (NoDup_Permutation _ _ (Permutation_sym PA) Snd) as X. inversion X; subst. auto. }
destruct NDA as [NDA NIA].
assert (INA : forall r', In r' arr' <-> In r' (st_sec_arr s) /\ r' <> r).
{ intros r'. split.
- intros H. split; [eapply Permutation_in; [exact PA | right; exact H] | intros ->; exact (NIA H)].
- intros [H Hne]. pose proof (Permutation_in _ (Permutation_sym PA) H) as [<-|H']; [congruence | exact H']. }
assert (OTHER : forall k', In k' (l1 ++ l2) -> forall o, ck_beg k' <> PSec r o).
{ intros k' Hk' o Hb'. pose proof (proj1 (Forall_forall _ _) Xck k' ltac:(rewrite E; apply in_app_iff in Hk' as [?|?]; apply in_app_iff; [left|right;right]; assumption)) as [_ CK].
rewrite Hb' in CK. destruct CK as (_ & -> & _).
assert (EBB : ck_beg k' = ck_beg k) by (rewrite Hb, Hb'; reflexivity).
apply in_app_iff in Hk' as [Hk'|Hk'].
- apply (NDc (ck_beg k)); [rewrite <- EBB; apply in_map; exact Hk' | left; reflexivity].
- match goal with H : ~ In (ck_beg k) (map ck_beg l2) |- _ => apply H end. rewrite <- EBB. apply in_map. exact Hk'. }
constructor; wf_easy.
- intros c' Hc'. unfold wf_class. cbn [st_cache_inited set_sec_arr set_secs set_chunks].
change (reg ?[S] c') with (reg s c'). change (cache ?[S] c') with (cache s c').
change (batch_offs ?[S] c') with (batch_offs s c').
change (chunk_offs ?[S] c') with (chunk_offs (set_chunks (l1 ++ l2) s) c'). rewrite (chunk_offs_del_sec s l1 k l2 r kPage c' E Hb).
exact (Xcl c' Hc').
- cbn [st_chunks set_sec_arr set_secs set_chunks]. apply Forall_forall. intros k' Hk'.
pose proof (proj1 (Forall_forall _ _) Xck k' ltac:(rewrite E; apply in_app_iff in Hk' as [?|?]; apply in_app_iff; [left|right;right]; assumption)) as [CKn CK].
split; [exact CKn|]. cbn [st_secs set_sec_arr set_secs set_chunks].
destruct (ck_beg k') as [|b'|r' o'|c' p'] eqn:Eb'; try exact CK.
destruct CK as (P1 & P2 & sm' & Q1 & Q2 & Q3 & Q4). split; [exact P1|]. split; [exact P2|]. exists sm'.
rewrite nth_error_lupd_other; [auto|]. intros <-. exact (OTHER k' Hk' o' Eb').
- cbn [st_chunks set_sec_arr set_secs set_chunks]. rewrite map_app. exact ND'.
- cbn [st_chunks set_sec_arr set_secs set_chunks st_nev]. rewrite E, !length_app in Xcev. rewrite length_app. cbn [length] in Xcev. lia.
- rewrite blocks_bytes_eq in *. cbn [st_chunks set_sec_arr set_secs set_chunks]. rewrite E, bbytes_split in Xlive. unfold is_alloc in Xlive. rewrite Hst in Xlive. lia.
- constructor; cbn [st_qthread st_qglobal st_chunks set_sec_arr set_secs set_chunks]; try assumption.
apply Forall_forall. intros k' Hk'. pose proof (proj1 (Forall_forall _ _) Qit k' Hk') as [H1' H2']. split; [|exact H2'].
rewrite E in H1'. apply in_app_iff in H1' as [H1'|[<-|H1']]; [apply in_app_iff; left; exact H1' | exfalso | apply in_app_iff; right; exact H1'].
apply Hni. apply in_map. exact Hk'.
- constructor; cbn [st_sec_arr st_secs st_chunks st_sec_reserved set_sec_arr set_secs set_chunks].
+ exact NDA.
+ intros r'. rewrite INA, Sac, E. split.
* intros [(k' & Hk' & Hb') Hne]. exists k'. split; [|exact Hb'].
apply in_app_iff in Hk' as [Hk'|[<-|Hk']]; [apply in_app_iff; left; exact Hk' | congruence | apply in_app_iff; right; exact Hk'].
* intros (k' & Hk' & Hb'). split; [exists k'; split; [|exact Hb']|].
-- apply in_app_iff in Hk' as [Hk'|Hk']; apply in_app_iff; [left | right; right]; assumption.
-- intros ->. exact (OTHER k' Hk' kPage Hb').
+ intros r'. rewrite INA, Sal. split.
* intros [(sm' & Q1 & Q2) Hne]. exists sm'. rewrite nth_error_lupd_other by (intros ->; exact (Hne eq_refl)). auto.
* intros (sm' & Q1 & Q2). destruct (Nat.eq_dec r r') as [<-|Hne].
-- rewrite nth_error_lupd_same in Q1 by (eapply nth_error_lt; exact Hsm). injection Q1 as <-. cbn in Q2. discriminate.
-- rewrite nth_error_lupd_other in Q1 by exact Hne. split; [exists sm'; auto | intros ->; exact (Hne eq_refl)].
+ pose proof (Permutation_length PA) as L. cbn [length] in L. lia.
+ exact Sral.
+
apply Forall_lupd; [exact Slen|]. cbn [sm_len]. exact (proj1 (Forall_forall _ _) Slen sm (nth_error_In _ _ Hsm)).
- apply (wf_fa_room_ext s _ (fun c0 => cc + bslack c0 bb)); [ | reflexivity | reflexivity | exact Xroom].
intros c' Hc'. match goal with |- length (class_elems ?S2 _) = _ =>
unfold class_elems; change (reg S2 c') with (reg s c'); change (cache S2 c') with (cache s c');
change (batch_offs S2 c') with (batch_offs s c'); change (chunk_offs S2 c') with (chunk_offs (set_chunks (l1 ++ l2) s) c') end.
rewrite (chunk_offs_del_sec s l1 k l2 r kPage c' E Hb). reflexivity.
-
cbn [st_secs st_nev set_sec_arr set_secs set_chunks]. rewrite lupd_length. exact Xsev.
-
apply (regime_xfer _ _ s _ Xreg); [reflexivity | intros HBP; exact HBP | cbn [st_chunks set_sec_arr set_secs set_chunks]; rewrite E, !length_app; cbn [length]; lia].
Qed.
Definition recycle_post (U : Univ) (pp cc bb : Z) (s : astate) (k : chunk) (ns : bool) (res : unit * astate) : Prop :=
let s' := snd res in
WfP U pp cc bb s' /\
(exists l1 l2, st_chunks s = l1 ++ k :: l2 /\ st_chunks s' = l1 ++ l2) /\
st_qthread s' = st_qthread s /\ st_qglobal s' = st_qglobal s /\ st_nev s' = st_nev s /\ st_fs s' = st_fs s /\ st_depot s' = st_depot s /\
secs_ext s s' /\
(forall c', 0 <= c' <= 31 -> rg_alloc_user (reg s' c') = rg_alloc_user (reg s c')) /\
(forall c' y, 0 <= c' <= 31 -> In y (class_elems s' c') -> In y (class_elems s c')) /\
(forall c', 1 <= c' <= 31 -> rg_mapped_fa (reg s c') <= rg_mapped_fa (reg s' c')) /\
(forall c', 1 <= c' <= 31 -> length (class_elems s' c') = length (class_elems s c')).
Definition recycle_postx (U : Univ) (pp cc bb : Z) (s : astate) (k : chunk) (ns : bool) (res : unit * astate) : Prop :=
recycle_post U pp cc bb s k ns res /\ length (st_secs (snd res)) = length (st_secs s).
Lemma recycle_chunk_okx : forall U pp cc bb s k ns,
WfP U pp cc bb s -> In k (st_chunks s) -> ck_state k = CQuarantined -> ~ In (ck_beg k) (map ck_beg (q_items s)) ->
atok ns (recycle_chunk k s) (recycle_postx U pp cc bb s k).
Proof.
intros U pp cc bb s k ns W Hk Hst Hni.
destruct (In_split_beg _ _ Hk (wf_chunks_nodup _ _ _ _ _ W)) as (l1 & l2 & E & N1 & N2).
pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ W) k Hk) as [CKn CK].
unfold recycle_chunk. apply atok_bind. apply atok_get. cbn [fst snd]. apply atok_bind. apply atok_mcheck; [apply mem_chunk_spec; exact Hk|].
cbn [fst snd]. apply atok_bind. apply atok_put. cbn [fst snd]. rewrite E at 1. rewrite del_chunk_present by exact N1.
destruct (ck_beg k) as [|off|r o|cc' pp'] eqn:Hb; try solve [destruct CK].
-
destruct (WfP_del_prim U pp cc bb s l1 k l2 off W E Hb Hst ltac:(rewrite Hb; exact Hni)) as (W1 & G1 & G2 & G3 & G4 & G5 & G6). cbv zeta in *.
eapply atok_mono; [|apply (cache_dealloc_ok U pp cc bb (set_chunks (l1 ++ l2) s) (prim_class off) off ns W1 ltac:(lia) G2 G3 G4 G6)].
intros ns' [[] s'] (W' & RO' & AU' & CE' & MF' & LEN'). cbn [snd] in *.
destruct RO' as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10). cbn in R1, R2, R3, R4, R5, R6, R7, R8, R9, R10.
unfold recycle_postx, recycle_post. cbn [snd]. split; [|rewrite R2; reflexivity]. splits; try assumption.
+ exists l1, l2. auto.
+ intros r0 sm0 E0. exists sm0. rewrite R2. auto.
+ intros c' y Hc' Hy. destruct (CE' c' y Hc' Hy) as [[-> ->]|Hy'].
* unfold class_elems. rewrite !in_app_iff. right. right. left. apply (In_chunk_offs s k off Hk Hb).
* exact (G5 c' y Hy').
+ intros c' Hc'. exact (MF' c' ltac:(lia)).
+ intros c' Hc'. rewrite (LEN' c') by lia. pose proof (Permutation_length (class_elems_del s l1 k l2 c' E)) as L.
rewrite length_app, chunk_offs_one, Hb in L.
destruct (Z.eqb_spec c' (prim_class off)) as [->|Hne].
* rewrite Z.eqb_refl in L. cbn [length] in L. lia.
* replace (prim_class off =? c') with false in L by (symmetry; apply Z.eqb_neq; lia). cbn [length] in L. lia.
-
destruct CK as (P1 & -> & sm & Hsm & Hlive & Hsz & Hlen).
pose proof (wf_secondary _ _ _ _ _ W) as X. destruct X as [Snd Sac Sal Sres Sral].
assert (Hr : In r (st_sec_arr s)) by (apply Sac; exists k; auto).
destruct (index_of_spec (st_sec_arr s) r 0%nat Hr) as (i & Ei & Hi). rewrite Nat.add_0_l in Ei.
unfold sec_dealloc. apply atok_bind. apply atok_get. cbn [fst snd st_secs st_sec_arr set_chunks]. rewrite Hsm, Ei.
set (s1 := set_chunks (l1 ++ l2) s).
assert (TAIL : forall ns1, atok ns1
((_ <- askz (KMunmapSec r (sm_len sm)) ;;
modify (fun s0 => set_sec_arr (removelast (lupd (st_sec_arr s0) i (last (st_sec_arr s0) r)))
(set_secs (lupd (st_secs s0) r (mkSec (sm_len sm) (sm_size sm) false)) s0))) s1)
(recycle_postx U pp cc bb s k)).
{ intros ns1. apply atok_bind. apply atok_askz.
- cbn. split; [exact Hr | exists sm; auto].
- intros z Hz. cbn [fst snd progz]. apply atok_modify. unfold recycle_postx, recycle_post. cbn [snd]. subst s1.
cbn [st_sec_arr st_secs set_chunks st_qthread st_qglobal st_nev st_fs st_depot set_sec_arr set_secs].
split; [|apply lupd_length]. splits; try reflexivity.
+ apply (WfP_del_sec U pp cc bb s l1 k l2 r sm i W E Hb Hst ltac:(rewrite Hb; exact Hni) Hsm Hi).
+ exists l1, l2. auto.
+ intros r0 sm0 E0. cbn [st_secs set_sec_arr set_secs set_chunks]. destruct (Nat.eq_dec r r0) as [<-|Hne].
* rewrite Hsm in E0. injection E0 as <-. exists (mkSec (sm_len sm) (sm_size sm) false).
rewrite nth_error_lupd_same by (eapply nth_error_lt; exact Hsm). cbn. auto.
* exists sm0. rewrite nth_error_lupd_other by exact Hne. auto.
+ intros c' y Hc' Hy. unfold class_elems in Hy |- *.
change (reg ?[S] c') with (reg s c') in Hy. change (cache ?[S] c') with (cache s c') in Hy. change (batch_offs ?[S] c') with (batch_offs s c') in Hy.
change (chunk_offs ?[S] c') with (chunk_offs (set_chunks (l1 ++ l2) s) c') in Hy. rewrite (chunk_offs_del_sec s l1 k l2 r kPage c' E Hb) in Hy. exact Hy.
+ intros c' Hc'. match goal with |- length (class_elems ?S2 _) = _ =>
unfold class_elems; change (reg S2 c') with (reg s c'); change (cache S2 c') with (cache s c');
change (batch_offs S2 c') with (batch_offs s c'); change (chunk_offs S2 c') with (chunk_offs (set_chunks (l1 ++ l2) s) c') end.
rewrite (chunk_offs_del_sec s l1 k l2 r kPage c' E Hb). reflexivity. }
destruct (needs_remap (sm_len sm)) eqn:NR.
+ apply atok_bind. apply atok_bind. apply atok_askz.
* cbn -[Z.le Z.div Z.add Z.modulo kClearShadowMmapThreshold Z.mul]. unfold needs_remap in NR. apply Z.leb_le in NR.
split; [exact NR|]. exists r, 0, sm. subst s1. cbn [st_secs set_chunks]. splits; auto; try lia; reflexivity.
* intros z Hz. cbn in Hz. cbn [fst snd]. unfold aGranted. destruct (Z.eqb_spec z 1) as [->|Hne].
-- cbn [progz Z.eqb Pos.eqb]. apply atok_ret. apply TAIL.
-- replace (progz _ z) with false by (cbn; destruct Hz as [->| ->]; cbn; congruence). apply atok_spin.
+ apply atok_bind. apply atok_ret. apply TAIL.
Qed.
Lemma recycle_chunk_ok : forall U pp cc bb s k ns,
WfP U pp cc bb s -> In k (st_chunks s) -> ck_state k = CQuarantined -> ~ In (ck_beg k) (map ck_beg (q_items s)) ->
atok ns (recycle_chunk k s) (recycle_post U pp cc bb s k).
Proof.
intros U pp cc bb s k ns W Hk Hst Hni. eapply atok_mono; [|exact (recycle_chunk_okx U pp cc bb s k ns W Hk Hst Hni)]. intros b r (H & _). exact H.
Qed.
Definition fframe (s s' : astate) : Prop :=
st_nev s' = st_nev s /\ st_fs s' = st_fs s /\ st_depot s' = st_depot s /\ blocks s' = blocks s /\ secs_ext s s'.
Lemma fframe_refl : forall s, fframe s s.
Proof. intros s. unfold fframe. splits; try reflexivity. apply secs_ext_refl. Qed.
Lemma fframe_trans : forall s1 s2 s3, fframe s1 s2 -> fframe s2 s3 -> fframe s1 s3.
Proof.
intros s1 s2 s3 (A1 & A2 & A3 & A4 & A5) (B1 & B2 & B3 & B4 & B5). unfold fframe.
rewrite B1, B2, B3, B4. splits; try assumption. eapply secs_ext_trans; eassumption.
Qed.
Lemma blocks_del_quar : forall s s' l1 k l2, st_chunks s = l1 ++ k :: l2 -> st_chunks s' = l1 ++ l2 -> ck_state k = CQuarantined ->
blocks s' = blocks s.
Proof.
intros s s' l1 k l2 E E' Hst. unfold blocks. rewrite E, E', !filter_app. cbn [filter].
replace (is_alloc k) with false by (unfold is_alloc; rewrite Hst; reflexivity). reflexivity.
Qed.
Lemma recycle_post_fframe : forall U pp cc bb s k ns r, ck_state k = CQuarantined -> recycle_post U pp cc bb s k ns r -> fframe s (snd r).
Proof.
intros U pp cc bb s k ns [u s'] Hst (W' & (l1 & l2 & E & E') & Rqt & Rqg & Rnev & Rfs & Rdep & SE & _). cbn [snd] in *.
unfold fframe. splits; try assumption. eapply blocks_del_quar; eassumption.
Qed.
Definition RIx (U : Univ) (pp cc bb : Z) (s : astate) (its : list chunk) (P : list batch) (selfs : list Z) : Prop :=
WfP U pp cc bb s /\
Forall (fun k => In k (st_chunks s) /\ ck_state k = CQuarantined) (its ++ flat_map b_items P) /\
NoDup (map ck_beg ((its ++ flat_map b_items P) ++ q_items s)) /\
Forall (fun b => (1 <= length (b_items b) <= Z.to_nat kBatchSlots)%nat) P /\
Forall (fun z => 0 <= z - region_off kBatchClass < rg_alloc_user (reg s kBatchClass) /\
(z - region_off kBatchClass) mod class_size kBatchClass = 0 /\
~ In (z - region_off kBatchClass) (class_elems s kBatchClass)) (selfs ++ map b_self P) /\
NoDup (selfs ++ map b_self P) /\
fa_room (rg_alloc_user (reg s kBatchClass)) (length (class_elems s kBatchClass) + length (selfs ++ map b_self P))
(cc + bb + 2 * (EV_MAX - st_nev s)) (rg_mapped_fa (reg s kBatchClass)).
Lemma RI_RIx : forall U pp cc bb s P, RI U pp cc bb s P -> RIx U pp cc bb s [] P [].
Proof.
intros U pp cc bb s P (A1 & A2 & A3 & A4 & A5 & A6 & A7). unfold RIx. cbn [app]. splits; try assumption.
- apply Forall_forall. intros z Hz. apply in_map_iff in Hz as (b & <- & Hb). exact (proj1 (Forall_forall _ _) A5 b Hb).
- rewrite length_map. exact A7.
Qed.
Definition xfr (s s' : astate) (d : Z -> Z) : Prop :=
(forall c', 1 <= c' <= 31 -> rg_alloc_user (reg s' c') = rg_alloc_user (reg s c')) /\
(forall c', 1 <= c' <= 31 -> rg_mapped_fa (reg s c') <= rg_mapped_fa (reg s' c')) /\
(forall c', 1 <= c' <= 31 -> Z.of_nat (length (class_elems s' c')) = Z.of_nat (length (class_elems s c')) + d c') /\
(Z.of_nat (length (st_chunks s')) <= Z.of_nat (length (st_chunks s)) /\ crw (st_chunks s') <= crw (st_chunks s) /\
length (st_secs s') = length (st_secs s) /\ Z.of_nat (length (all_batches s')) <= Z.of_nat (length (all_batches s))).
Lemma xfr_refl : forall s, xfr s s (fun _ => 0).
Proof. intros s. unfold xfr. splits; intros; lia. Qed.
Lemma xfr_trans : forall s1 s2 s3 d1 d2 d, xfr s1 s2 d1 -> xfr s2 s3 d2 -> (forall c', 1 <= c' <= 31 -> d c' = d1 c' + d2 c') -> xfr s1 s3 d.
Proof.
intros s1 s2 s3 d1 d2 d (A1 & M1 & L1 & K1 & C1 & S1 & B1) (A2 & M2 & L2 & K2 & C2 & S2 & B2) E. unfold xfr. splits; try lia; intros c' Hc'.
- rewrite (A2 c' Hc'). exact (A1 c' Hc').
- pose proof (M1 c' Hc'). pose proof (M2 c' Hc'). lia.
- rewrite (L2 c' Hc'), (L1 c' Hc'), (E c' Hc'). lia.
Qed.
Lemma xfr_cdef : forall s s' d, xfr s s' d -> forall c', 1 <= c' <= 31 -> cdef s' c' = cdef s c' - class_size c' * d c'.
Proof. intros s s' d (A & _ & L & _) c' Hc'. unfold cdef. rewrite (A c' Hc'), (L c' Hc'). lia. Qed.
Lemma xfr_BigP : forall s s' d, xfr s s' d -> BigP s -> BigP s'.
Proof.
intros s s' d (A & M & _) HB c' Hc'. rewrite (A c' Hc'). pose proof (M c' Hc'). destruct (HB c' Hc') as [HB0|HB0]; [left; exact HB0 | right; lia].
Qed.
Lemma recycle_post_xfr : forall U pp cc bb s k ns r, recycle_postx U pp cc bb s k ns r -> xfr s (snd r) (fun _ => 0).
Proof.
intros U pp cc bb s k ns r ((_ & (l1 & l2 & E & E') & Rqt & Rqg & _ & _ & _ & _ & AU & _ & MF & LEN) & RS). unfold xfr. splits; try (intros c' Hc').
- apply AU. lia.
- apply MF. exact Hc'.
- rewrite (LEN c' Hc'). lia.
- rewrite E, E', !length_app. cbn [length]. lia.
- rewrite E, E', !crw_app. change (crw (k :: l2)) with (cw k + crw l2). pose proof (cw_nonneg k). lia.
- exact RS.
- unfold all_batches. rewrite Rqt, Rqg. lia.
Qed.
Lemma cache_dealloc_post_xfr : forall U pp cc bb s c x ns r, cache_dealloc_post U pp cc bb s c x ns r ->
xfr s (snd r) (fun c' => if c' =? c then 1 else 0).
Proof.
intros U pp cc bb s c x ns r (_ & (R1 & R2 & _ & _ & R5 & R6 & _) & AU & _ & MF & LEN). unfold xfr. splits; try (intros c' Hc').
- apply AU. lia.
- apply MF. lia.
- rewrite (LEN c' ltac:(lia)). destruct (c' =? c); lia.
- rewrite R1. lia.
- rewrite R1. lia.
- rewrite R2. reflexivity.
- unfold all_batches. rewrite R5, R6. lia.
Qed.
Lemma recycle_items_okx : forall U pp cc bb its, forall s P selfs ns fuel,
RIx U pp cc bb s its P selfs -> (length its <= fuel)%nat ->
atok ns (recycle_items fuel its s)
(fun ns' res => (RIx U pp cc bb (snd res) [] P selfs /\ fframe s (snd res) /\
st_qthread (snd res) = st_qthread s /\ st_qglobal (snd res) = st_qglobal s /\ unq (snd res) = unq s - items_n its) /\
xfr s (snd res) (fun _ => 0)).
Proof.
intros U pp cc bb its. induction its as [|k its IH]; intros s P selfs ns fuel RX Hfuel.
- destruct fuel; cbn [recycle_items]; apply atok_ret; cbn [snd]; (split; [|apply xfr_refl]); (split; [exact RX | split; [apply fframe_refl | rewrite items_n_nil; splits; [reflexivity | reflexivity | lia]]]).
- destruct fuel as [|f]; [cbn in Hfuel; lia|]. cbn [recycle_items]. apply atok_bind.
destruct RX as (W & IT & ND & BL & SF & NDS & RM).
inversion IT as [|k0 rest [Hk Hst] ITr]; subst.
assert (Hni : ~ In (ck_beg k) (map ck_beg (q_items s))).
{ cbn [app map] in ND. inversion ND; subst. intros Hin. match goal with H : ~ In (ck_beg k) _ |- _ => apply H end.
rewrite map_app. apply in_app_iff. right. exact Hin. }
eapply atok_mono; [|apply (recycle_chunk_okx U pp cc bb s k ns W Hk Hst Hni)].
intros ns1 [[] s1] RPX. pose proof (recycle_post_xfr _ _ _ _ _ _ _ _ RPX) as XF1. destruct RPX as [RP _].
pose proof (recycle_post_fframe U pp cc bb s k ns1 _ Hst RP) as FF.
unfold recycle_post in RP. cbn [fst snd] in FF, RP, XF1 |- *.
destruct RP as (W1 & (l1 & l2 & E & E1) & Rqt & Rqg & Rnev & Rfs & Rdep & SE & AU & CE & MF & LEN).
assert (EQI : q_items s1 = q_items s) by (unfold q_items, all_batches; rewrite Rqt, Rqg; reflexivity).
pose proof (unq_del s s1 l1 k l2 E E1 Hst Rqt Rqg) as UQ1.
eapply atok_mono; [|apply (IH s1 P selfs ns1 f); [|cbn in Hfuel; lia]].
{ intros b [u s2] ((RX2 & FF2 & Q2 & G2 & U2) & XF2). cbn [snd] in Q2, G2, U2, XF2 |- *.
split; [|eapply xfr_trans; [exact XF1 | exact XF2 | intros; lia]].
split; [exact RX2 | split; [eapply fframe_trans; [exact FF | exact FF2]|]].
rewrite Q2, G2, U2, UQ1, Rqt, Rqg, items_n_cons. splits; [reflexivity | reflexivity | lia]. }
cbn [app map] in ND. inversion ND as [|b0 rest0 Hnk NDr]; subst.
unfold RIx. splits.
+ exact W1.
+ apply Forall_forall. intros k' Hk'. pose proof (proj1 (Forall_forall _ _) ITr k' Hk') as [H1 H2]. split; [|exact H2].
rewrite E1. rewrite E in H1. apply in_app_iff in H1 as [H1|[<-|H1]]; [apply in_app_iff; left; exact H1 | exfalso | apply in_app_iff; right; exact H1].
apply Hnk. rewrite map_app. apply in_app_iff. left. apply in_map. exact Hk'.
+ rewrite EQI. exact NDr.
+ exact BL.
+ eapply Forall_impl; [|exact SF]. cbv beta. intros z (Z1 & Z2 & Z3). rewrite AU by (unfold kBatchClass; lia).
split; [exact Z1 | split; [exact Z2|]]. intros Hin. exact (Z3 (CE kBatchClass _ ltac:(unfold kBatchClass; lia) Hin)).
+ exact NDS.
+ rewrite AU, LEN, Rnev by (unfold kBatchClass; lia). eapply fa_room_xfer; [exact RM | apply Z.le_refl | apply MF; unfold kBatchClass; lia].
Qed.
Lemma recycle_items_ok : forall U pp cc bb its, forall s P selfs ns fuel,
RIx U pp cc bb s its P selfs -> (length its <= fuel)%nat ->
atok ns (recycle_items fuel its s)
(fun ns' res => RIx U pp cc bb (snd res) [] P selfs /\ fframe s (snd res) /\
st_qthread (snd res) = st_qthread s /\ st_qglobal (snd res) = st_qglobal s /\ unq (snd res) = unq s - items_n its).
Proof.
intros U pp cc bb its s P selfs ns fuel RX Hfuel.
eapply atok_mono; [|exact (recycle_items_okx U pp cc bb its s P selfs ns fuel RX Hfuel)]. intros b r (H & _). exact H.
Qed.
Lemma cache_dealloc_post_fframe : forall U pp cc bb s c x ns r, cache_dealloc_post U pp cc bb s c x ns r -> fframe s (snd r).
Proof.
intros U pp cc bb s c x ns [u s'] (W' & RO & _ & _). cbn [snd] in *.
destruct RO as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10). unfold fframe. splits; try assumption.
- unfold blocks. rewrite R1. reflexivity.
- intros r0 sm0 E0. exists sm0. rewrite R2. auto.
Qed.
Lemma do_recycle_okx : forall U pp cc bb P, forall s ns fuel,
RIx U pp cc bb s [] P [] -> (length P <= fuel)%nat ->
atok ns (do_recycle fuel P s) (fun ns' res => (WfP U pp cc bb (snd res) /\ fframe s (snd res) /\
st_qthread (snd res) = st_qthread s /\ st_qglobal (snd res) = st_qglobal s /\ unq (snd res) = unq s - items_n (flat_map b_items P)) /\
xfr s (snd res) (fun c' => if c' =? kBatchClass then Z.of_nat (length P) else 0)).
Proof.
intros U pp cc bb P. induction P as [|b P IH]; intros s ns fuel RX Hfuel.
- destruct fuel; cbn [do_recycle flat_map]; apply atok_ret; cbn [snd]; (split; [|eapply xfr_trans; [apply xfr_refl | apply xfr_refl | intros c' _; cbn [length]; destruct (c' =? kBatchClass); reflexivity]]);
(split; [exact (proj1 RX) | split; [apply fframe_refl | rewrite items_n_nil; splits; [reflexivity | reflexivity | lia]]]).
- destruct fuel as [|f]; [cbn in Hfuel; lia|]. cbn [do_recycle]. apply atok_bind.
destruct RX as (W & IT & ND & BL & SF & NDS & RM). cbn [app flat_map map] in IT, ND, SF, NDS, RM.
inversion BL as [|b0 P0 BLb BLP]; subst.
eapply atok_mono; [|apply (recycle_items_okx U pp cc bb (b_items b) s P [b_self b] ns 1100)].
2:{ unfold RIx. cbn [app]. splits; try assumption. }
2:{ unfold kBatchSlots in BLb. lia. }
intros ns1 [[] s1] ((RX1 & FF1 & TQ1 & TG1 & UQ1) & XF1). cbn [fst snd] in TQ1, TG1, UQ1, XF1 |- *. apply atok_bind.
destruct RX1 as (W1 & IT1 & ND1 & BL1 & SF1 & NDS1 & RM1). cbn [app] in IT1, ND1. cbn [app length fst snd] in RM1. cbn [fst snd] in SF1.
inversion SF1 as [|z0 l0 (Z1 & Z2 & Z3) SFP]; subst. inversion NDS1 as [|z1 l1 Hnself NDSP]; subst.
assert (ROOM1 : 4 * (Z.of_nat (length (class_elems s1 kBatchClass)) + 1 + (cc + bb + 2 * (EV_MAX - st_nev s1))) <= rg_mapped_fa (reg s1 kBatchClass)).
{ destruct RM1 as [Z0|R]; [lia|]. rewrite length_map in R. lia. }
eapply atok_mono; [|apply (cache_dealloc_ok U pp cc bb s1 kBatchClass (b_self b) ns1 W1 ltac:(unfold kBatchClass; lia) Z1 Z2 Z3 ROOM1)].
intros ns2 [[] s2] CP. pose proof (cache_dealloc_post_fframe _ _ _ _ _ _ _ _ _ CP) as FF2. pose proof (cache_dealloc_post_xfr _ _ _ _ _ _ _ _ _ CP) as XF2. cbn [fst snd] in FF2, XF2 |- *.
destruct CP as (W2 & RO2 & AU2 & CE2 & MF2 & LEN2). cbn [snd] in W2, RO2, AU2, CE2, MF2, LEN2.
destruct RO2 as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10).
pose proof (unq_same s1 s2 R1 R5 R6) as UQ2.
eapply atok_mono; [|apply (IH s2 ns2 f); [|cbn in Hfuel; lia]].
{ intros b' [u s3] ((W3 & FF3 & TQ3 & TG3 & UQ3) & XF3). cbn [snd] in TQ3, TG3, UQ3, XF3 |- *.
split; [|eapply xfr_trans; [exact XF1 | eapply xfr_trans; [exact XF2 | exact XF3 | intros; reflexivity] |]].
2:{ intros c' _. cbn beta. cbn [length]. rewrite Nat2Z.inj_succ. destruct (c' =? kBatchClass); lia. }
split; [exact W3 | split; [eapply fframe_trans; [exact FF1 | eapply fframe_trans; [exact FF2 | exact FF3]]|]].
rewrite TQ3, TG3, UQ3, R5, R6, TQ1, TG1, UQ2, UQ1. cbn [flat_map]. rewrite items_n_app. splits; [reflexivity | reflexivity | lia]. }
unfold RIx. cbn [app]. splits.
+ exact W2.
+ rewrite R1. exact IT1.
+ replace (q_items s2) with (q_items s1) by (unfold q_items, all_batches; rewrite R5, R6; reflexivity). exact ND1.
+ exact BLP.
+ apply Forall_forall. intros z Hz. pose proof (proj1 (Forall_forall _ _) SFP z Hz) as (Y1 & Y2 & Y3).
rewrite AU2 by (unfold kBatchClass; lia). split; [exact Y1 | split; [exact Y2|]].
intros Hin. destruct (CE2 kBatchClass _ ltac:(unfold kBatchClass; lia) Hin) as [[Ez _]|Hin'].
* apply Hnself. replace (b_self b) with z by lia. exact Hz.
* exact (Y3 Hin').
+ exact NDSP.
+ rewrite AU2, (LEN2 kBatchClass), R10 by (unfold kBatchClass; lia). rewrite Z.eqb_refl.
eapply fa_room_xfer; [exact RM1 | rewrite length_map; lia | apply MF2; unfold kBatchClass; lia].
Qed.
Lemma do_recycle_ok : forall U pp cc bb P, forall s ns fuel,
RIx U pp cc bb s [] P [] -> (length P <= fuel)%nat ->
atok ns (do_recycle fuel P s) (fun ns' res => WfP U pp cc bb (snd res) /\ fframe s (snd res) /\
st_qthread (snd res) = st_qthread s /\ st_qglobal (snd res) = st_qglobal s /\ unq (snd res) = unq s - items_n (flat_map b_items P)).
Proof.
intros U pp cc bb P s ns fuel RX Hfuel.
eapply atok_mono; [|exact (do_recycle_okx U pp cc bb P s ns fuel RX Hfuel)]. intros b r (H & _). exact H.
Qed.
Lemma of_nat_100000 : Z.of_nat 100000%nat = 100000.
Proof. vm_compute. reflexivity. Qed.
Lemma batches_bound : forall U pp cc bb s, WfP U pp cc bb s -> st_nev s <= EV_MAX -> Z.of_nat (length (all_batches s)) <= EV_MAX.
Proof.
intros U pp cc bb s W Hev. pose proof (wf_batches_ev _ _ _ _ _ W). pose proof (wf_nev _ _ _ _ _ W). pose proof (wf_slack _ _ _ _ _ W). lia.
Qed.
Lemma xfr_transfer : forall s,
xfr s (set_qglobal (mkQC (qc_list (st_qglobal s) ++ qc_list (st_qthread s)) (qc_bytes (st_qglobal s) + qc_bytes (st_qthread s))) (set_qthread qc0 s)) (fun _ => 0).
Proof.
intros s. unfold xfr. splits; try (intros c' Hc'); [reflexivity | apply Z.le_refl | | apply Z.le_refl | apply Z.le_refl | reflexivity |].
- unfold class_elems. match goal with |- context [reg ?S c'] => change (reg S c') with (reg s c'); change (cache S c') with (cache s c'); change (chunk_offs S c') with (chunk_offs s c') end.
unfold batch_offs, all_batches. cbn [st_qthread st_qglobal set_qglobal set_qthread qc_list qc0 app].
destruct (c' =? kBatchClass); [|lia]. rewrite !length_app, !length_map, !length_app. lia.
- unfold all_batches. cbn [st_qthread st_qglobal set_qglobal set_qthread qc_list qc0 app]. rewrite !length_app. lia.
Qed.
Lemma xfr_pop : forall s P rest bytes, qc_list (st_qglobal s) = P ++ rest ->
xfr s (set_qglobal (mkQC rest bytes) s) (fun c' => if c' =? kBatchClass then - Z.of_nat (length P) else 0).
Proof.
intros s P rest bytes EL. unfold xfr. splits; try (intros c' Hc'); [reflexivity | apply Z.le_refl | | apply Z.le_refl | apply Z.le_refl | reflexivity |].
- unfold class_elems. match goal with |- context [reg ?S c'] => change (reg S c') with (reg s c'); change (cache S c') with (cache s c'); change (chunk_offs S c') with (chunk_offs s c') end.
unfold batch_offs, all_batches. cbn [st_qthread st_qglobal set_qglobal qc_list]. rewrite EL.
destruct (c' =? kBatchClass); [|lia]. rewrite !length_app, !length_map, !length_app, !Nat2Z.inj_add. lia.
- unfold all_batches. cbn [st_qthread st_qglobal set_qglobal qc_list]. rewrite EL, !length_app. lia.
Qed.
Lemma sum_bytes_nonneg : forall l, Forall (fun k => 0 <= ck_req k) (flat_map b_items l) -> 0 <= sum_bytes l.
Proof.
induction l as [|b t IH]; intros H; [cbn; lia|]. cbn [flat_map] in H. apply Forall_app in H as [Hb Ht]. specialize (IH Ht).
unfold sum_bytes in *. cbn [fold_right].
assert (0 <= b_bytes b); [|lia]. unfold b_bytes, kBatchBytes.
assert (G : forall its, Forall (fun k => 0 <= ck_req k) its -> 0 <= fold_right (fun k acc => ck_n k + acc) 0 its).
{ induction its as [|k its IHi]; intros Hi; cbn [fold_right]; [lia|]. inversion Hi as [|k' its' Hk Hits]; subst. specialize (IHi Hits).
assert (1 <= ck_n k) by (unfold ck_n, req_size; destruct (Z.eqb_spec (ck_req k) 0); lia). lia. }
pose proof (G (b_items b) Hb). lia.
Qed.
Lemma full_items : forall l, Forall bfull l -> Z.of_nat (length (flat_map b_items l)) = kBatchSlots * Z.of_nat (length l).
Proof.
induction l as [|b t IH]; intros H; [cbn; lia|]. inversion H as [|b' t' Hb Ht]; subst. cbn [flat_map length].
rewrite length_app, Nat2Z.inj_add, (IH Ht), Nat2Z.inj_succ. unfold bfull in Hb. rewrite Hb. unfold kBatchSlots. lia.
Qed.
Lemma almost_full_items : forall l, Forall bfull (removelast l) -> kBatchSlots * (Z.of_nat (length l) - 1) <= Z.of_nat (length (flat_map b_items l)).
Proof.
intros l H. destruct (rev l) as [|lastb initr] eqn:Er.
- apply (f_equal (@rev batch)) in Er. rewrite rev_involutive in Er. subst l. cbn. unfold kBatchSlots. lia.
- apply (f_equal (@rev batch)) in Er. rewrite rev_involutive in Er. cbn [rev] in Er. subst l. rewrite removelast_snoc in H.
rewrite flat_map_app, !length_app, !Nat2Z.inj_add, (full_items _ H). cbn [length]. unfold kBatchSlots. lia.
Qed.
Lemma qgroups_count : forall GS, Forall qgroup_ok GS ->
kBatchSlots * (Z.of_nat (length (concat GS)) - Z.of_nat (length GS)) <= Z.of_nat (length (flat_map b_items (concat GS))) /\
kQuarantineCacheMax * Z.of_nat (length GS) <= sum_bytes (concat GS).
Proof.
induction GS as [|g GS IH]; intros H; [cbn; unfold kBatchSlots, kQuarantineCacheMax; lia|].
inversion H as [|g' GS' (GN & GF & GB) HG]; subst. destruct (IH HG) as [I1 I2]. pose proof (almost_full_items g GF) as A.
cbn [concat length]. rewrite flat_map_app, !length_app, !Nat2Z.inj_add, sum_bytes_app, Nat2Z.inj_succ.
unfold kBatchSlots, kQuarantineCacheMax in *. split; lia.
Qed.
Lemma qbatches_bound : forall U pp cc bb s, WfP U pp cc bb s -> exists ng,
0 <= ng /\ kBatchSlots * (Z.of_nat (length (qc_list (st_qglobal s))) - 1 - ng) <= Z.of_nat (length (flat_map b_items (qc_list (st_qglobal s)))) /\
kQuarantineCacheMax * ng <= qc_bytes (st_qglobal s).
Proof.
intros U pp cc bb s W. pose proof (wf_quarantine _ _ _ _ _ W) as Q.
destruct (wq_groups _ Q) as (F & GS & EG & FF & FG). exists (Z.of_nat (length GS)).
destruct (qgroups_count GS FG) as [C1 C2]. pose proof (almost_full_items F FF) as A.
assert (N : 0 <= sum_bytes F).
{ apply sum_bytes_nonneg. apply Forall_forall. intros k Hk.
assert (HQ : In k (q_items s)). { unfold q_items, all_batches. rewrite EG, !flat_map_app, !in_app_iff. right. left. exact Hk. }
pose proof (proj1 (proj1 (Forall_forall _ _) (wq_items _ Q) k HQ)) as HC.
pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ W) k HC) as [HR _]. lia. }
rewrite (wq_bytes_g _ Q), EG, flat_map_app, !length_app, !Nat2Z.inj_add, sum_bytes_app.
unfold kBatchSlots, kQuarantineCacheMax in *. splits; lia.
Qed.
Lemma q_items_le_chunks : forall U pp cc bb s, WfP U pp cc bb s -> (length (q_items s) <= length (st_chunks s))%nat.
Proof.
intros U pp cc bb s W. pose proof (wf_quarantine _ _ _ _ _ W) as Q.
rewrite <- (length_map ck_beg (q_items s)), <- (length_map ck_beg (st_chunks s)). apply NoDup_incl_length; [exact (wq_nodup _ Q)|].
intros p Hp. apply in_map_iff in Hp as (k & <- & Hk). apply in_map. exact (proj1 (proj1 (Forall_forall _ _) (wq_items _ Q) k Hk)).
Qed.
Lemma maybe_drain_okx : forall U pp cc bb s ns,
WfP U pp cc bb s ->
(st_nev s <= EV_MAX \/ (Z.of_nat (length (st_chunks s)) <= 2 ^ 23 /\ qc_bytes (st_qglobal s) + qc_bytes (st_qthread s) <= 2 ^ 36)) ->
atok ns (maybe_drain s) (fun ns' res => (WfP U pp cc bb (snd res) /\ fframe s (snd res) /\
qc_bytes (st_qthread (snd res)) <= kQuarantineCacheMax /\ qc_bytes (st_qglobal (snd res)) <= Z.max (qc_bytes (st_qglobal s)) kQuarantineMax /\
unq (snd res) = unq s) /\ xfr s (snd res) (fun _ => 0)).
Proof.
intros U pp cc bb s ns W HB4.
unfold maybe_drain. apply atok_bind. apply atok_get. cbn [fst snd].
destruct (qc_bytes (st_qthread s) <=? kQuarantineCacheMax) eqn:E1.
{ apply atok_ret. apply Z.leb_le in E1. cbn [snd]. split; [|apply xfr_refl]. splits; [exact W | apply fframe_refl | exact E1 | lia | reflexivity]. }
apply atok_bind. apply atok_put. cbn [fst snd].
pose proof (WfP_transfer U pp cc bb s W ltac:(apply Z.leb_gt; exact E1)) as WT. cbv zeta in WT. set (sT := set_qglobal _ _) in *.
assert (FFT : fframe s sT).
{ subst sT. unfold fframe. cbn [st_nev st_fs st_depot set_qglobal set_qthread]. splits; try reflexivity. intros r0 sm0 E0; exists sm0; auto. }
pose proof (unq_transfer s) as UQT. fold sT in UQT.
pose proof (xfr_transfer s) as XFT. fold sT in XFT.
match goal with |- atok _ ((if ?b then _ else _) _) _ => destruct b eqn:E2 end.
{ apply atok_ret. apply Z.leb_le in E2. cbn [snd]. split; [|exact XFT]. splits; [exact WT | exact FFT | subst sT; cbn; kc; lia | subst sT; cbn [st_qglobal set_qglobal set_qthread] in E2 |- *; lia | exact UQT]. }
apply Z.leb_gt in E2. cbn [qc_bytes] in E2.
assert (BB : Z.of_nat (length (qc_list (st_qglobal s) ++ qc_list (st_qthread s))) < 100000 /\
2 * (kBatchBytes * Z.of_nat (length (qc_list (st_qglobal s) ++ qc_list (st_qthread s)))) <= qc_bytes (st_qglobal s) + qc_bytes (st_qthread s)).
{ destruct HB4 as [Hev|[HCH HQB]].
- pose proof (batches_bound U pp cc bb s W Hev) as LB. unfold all_batches in LB. rewrite length_app in LB |- *.
unfold kBatchBytes, kQuarantineMax, EV_MAX in *. lia.
-
destruct (qbatches_bound U pp cc bb sT WT) as (ng & NG0 & C1 & C2).
pose proof (q_items_le_chunks U pp cc bb sT WT) as QL.
assert (IT : (length (flat_map b_items (qc_list (st_qglobal sT))) <= length (q_items sT))%nat).
{ unfold q_items, all_batches. rewrite flat_map_app, length_app. lia. }
subst sT. cbn [st_qglobal st_chunks set_qglobal set_qthread qc_list qc_bytes] in C1, C2, QL, IT.
unfold kBatchSlots, kBatchBytes, kQuarantineCacheMax, kQuarantineMax in *. lia. }
apply atok_bind. apply atok_mcheck.
{ apply Z.leb_le. subst sT. cbn [st_qglobal set_qglobal set_qthread qc_list qc_bytes]. exact (proj2 BB). }
cbn [fst snd]. destruct (pop_batches _ _ _) as [g' popped] eqn:EP. pose proof EP as EP0.
apply pop_batches_spec in EP as (P & -> & EL & EB). cbn [rev app qc_list qc_bytes] in EL, EB |- *.
apply atok_bind. apply atok_modify. cbn [fst snd].
assert (EG : g' = mkQC (qc_list g') (qc_bytes (st_qglobal sT) - sum_bytes P)) by (destruct g'; cbn in EB |- *; rewrite EB; reflexivity).
pose proof (RI_pop U pp cc bb sT P (qc_list g') WT EL) as RI0. rewrite <- EG in RI0.
assert (FFP : fframe sT (set_qglobal g' sT)).
{ unfold fframe. cbn [st_nev st_fs st_depot set_qglobal]. splits; try reflexivity. intros r0 sm0 E0; exists sm0; auto. }
assert (L : (length P <= length (qc_list (st_qglobal s) ++ qc_list (st_qthread s)))%nat) by (rewrite EL, length_app; lia).
assert (GB : qc_bytes g' <= kQuarantineMax).
{ destruct (pop_batches_stop _ _ _ _ _ EP0) as [Hmin|Hnil].
- cbn [qc_list]. apply Nat2Z.inj_lt. rewrite of_nat_100000. exact (proj1 BB).
- kc. lia.
- rewrite EB. pose proof (wq_bytes_g _ (wf_quarantine _ _ _ _ _ WT)) as QB. subst sT. cbn [st_qglobal set_qglobal set_qthread qc_bytes qc_list] in QB, EL |- *.
rewrite QB, EL, Hnil, sum_bytes_app. cbn. kc. lia. }
pose proof (unq_pop sT P (qc_list g') (qc_bytes (st_qglobal sT) - sum_bytes P) EL) as UQP. rewrite <- EG in UQP.
pose proof (xfr_pop sT P (qc_list g') (qc_bytes g') EL) as XFP. replace (mkQC (qc_list g') (qc_bytes g')) with g' in XFP by (destruct g'; reflexivity).
eapply atok_mono; [|apply (do_recycle_okx U pp cc bb P (set_qglobal g' sT) _ 100000%nat (RI_RIx _ _ _ _ _ _ RI0))].
- intros b [u s'] ((W' & FF' & TQ' & TG' & UQ') & XF'). cbn [snd] in TQ', TG', UQ', XF' |- *.
split; [|eapply xfr_trans; [exact XFT | eapply xfr_trans; [exact XFP | exact XF' | intros; reflexivity] | intros c' _; cbn beta; destruct (c' =? kBatchClass); lia]].
split; [exact W' | split; [eapply fframe_trans; [exact FFT | eapply fframe_trans; [exact FFP | exact FF']]|]].
rewrite TQ', TG', UQ', UQP, UQT. subst sT. cbn [st_qthread st_qglobal set_qglobal set_qthread qc_bytes qc0]. splits; [kc; lia | lia | lia].
- apply Nat2Z.inj_le. rewrite of_nat_100000. pose proof (proj1 BB). lia.
Qed.
Lemma maybe_drain_ok : forall U pp cc bb s ns,
WfP U pp cc bb s ->
(st_nev s <= EV_MAX \/ (Z.of_nat (length (st_chunks s)) <= 2 ^ 23 /\ qc_bytes (st_qglobal s) + qc_bytes (st_qthread s) <= 2 ^ 36)) ->
atok ns (maybe_drain s) (fun ns' res => WfP U pp cc bb (snd res) /\ fframe s (snd res) /\
qc_bytes (st_qthread (snd res)) <= kQuarantineCacheMax /\ qc_bytes (st_qglobal (snd res)) <= Z.max (qc_bytes (st_qglobal s)) kQuarantineMax /\
unq (snd res) = unq s).
Proof.
intros U pp cc bb s ns W HB4. eapply atok_mono; [|exact (maybe_drain_okx U pp cc bb s ns W HB4)]. intros b r (H & _). exact H.
Qed.
Theorem free_gen : forall U s p n tr,
universe_ok U ->
Wf U s -> regime_ok s -> (p = PNull \/ In (p, n) (blocks s)) -> admits U tr s ->
atok true (free p tr s) (fun ns r => free_post U s p n ns r /\ (BigInv s -> BigInv (snd r)) /\ fgrow s (snd r)).
Proof.
intros U s p n tr HU W Hreg Hp Htr.
assert (TREG : st_nev s < EV_MAX \/ (BigP s /\ Z.of_nat (length (st_chunks s)) + 1 <= 2 ^ 23)).
{ destruct Hreg as [Hev | ((_ & HP) & _ & _ & HCH & _)]; [left; exact Hev | right; split; [exact HP | exact HCH]]. }
pose proof (WfP_tick' U s W TREG) as W1. set (s1 := set_nev (st_nev s + 1) s) in *.
unfold free. apply atok_bind. apply atok_tick. cbn [fst snd]. fold s1.
apply atok_bind. apply atok_get. cbn [fst snd].
assert (K : forall v, let s2 := set_internal_inited v s1 in WfP U 1 1 1 s2 ->
atok true
(match p with
| PNull => ret tt
| _ => s0 <- get ;;
match find_user (st_chunks s0) p with
| Some k =>
mcheck match ck_state k with CAllocated => true | CQuarantined => false end 1 ;;
depot_put tr ;;
modify (fun s3 => set_chunks (upd_chunk (st_chunks s3) (mkChunk (ck_beg k) (ck_req k) CQuarantined)) s3) ;;
enqueue (mkChunk (ck_beg k) (ck_req k) CQuarantined) ;;
maybe_drain
| None => fail (FCheck 2)
end
end s2) (fun ns r => free_post U s p n ns r /\ (BigInv s -> BigInv (snd r)) /\ fgrow s (snd r))).
2:{ apply atok_bind. destruct (st_internal_inited s1) eqn:Ei.
- apply atok_ret. cbn [fst snd]. replace s1 with (set_internal_inited true s1) by (subst s1; destruct s; cbn in Ei |- *; subst; reflexivity).
apply K. apply WfP_set_internal_inited. exact W1.
- apply atok_modify. cbn [fst snd]. apply K. apply WfP_set_internal_inited. exact W1. }
intros v s2 W2.
assert (F2 : st_chunks s2 = st_chunks s /\ st_secs s2 = st_secs s /\ st_fs s2 = st_fs s /\ st_depot s2 = st_depot s /\
st_nev s2 = st_nev s + 1 /\ q_items s2 = q_items s /\ blocks s2 = blocks s) by (subst s2 s1; repeat split; reflexivity).
destruct F2 as (Fck & Fsecs & Ffs & Fdep & Fnev & Fqi & Fbl).
assert (MAIN : forall q, In (q, n) (blocks s) ->
atok true ((s0 <- get ;;
match find_user (st_chunks s0) q with
| Some k =>
mcheck match ck_state k with CAllocated => true | CQuarantined => false end 1 ;;
depot_put tr ;;
modify (fun s3 => set_chunks (upd_chunk (st_chunks s3) (mkChunk (ck_beg k) (ck_req k) CQuarantined)) s3) ;;
enqueue (mkChunk (ck_beg k) (ck_req k) CQuarantined) ;;
maybe_drain
| None => fail (FCheck 2)
end) s2) (fun ns r => free_post U s q n ns r /\ (BigInv s -> BigInv (snd r)) /\ fgrow s (snd r))).
2:{ destruct p as [|po|pr poff|pc ppos]; [| apply MAIN | apply MAIN | apply MAIN]; try (destruct Hp as [Hp|Hp]; [discriminate | exact Hp]).
apply atok_ret. unfold free_post. cbn [snd]. pose proof (wf_slack _ _ _ _ _ W2).
split; [|split; [intros HBI; exact HBI | unfold fgrow, all_batches; subst s2 s1; cbn [st_chunks st_secs st_qthread st_qglobal set_internal_inited set_nev]; splits; try reflexivity; lia]].
splits; [unfold Wf; eapply WfP_weaken; [exact W2|lia|lia|lia] | exact Fnev | intros r0 sm0 E0; exists sm0; rewrite Fsecs; auto | unfold frames; rewrite Ffs; reflexivity | |].
- exists [], (blocks s). cbn [app]. split; [left; auto | exact Fbl].
- intros QT. apply (qtight_ext s); [exact Fck | subst s2 s1; reflexivity | subst s2 s1; reflexivity | exact QT]. }
intros q Hq. apply atok_bind. apply atok_get. cbn [fst snd].
destruct (find_user_block U 1 1 1 s2 q n W2 ltac:(rewrite Fbl; exact Hq)) as (k & -> & Hk & Hst & Hu & Hr).
apply atok_bind. apply atok_mcheck; [rewrite Hst; reflexivity|]. cbn [fst snd].
apply atok_bind. eapply atok_mono; [|apply (depot_put_ok U s2 tr true); [rewrite Fdep; exact (wf_depot _ _ _ _ _ W) | exact HU | exact (admits_keep U tr s s2 Htr (or_introl Fdep))]].
intros ns3 [[] s3] (d & -> & Hdf & Hd & ->). cbn [fst snd].
pose proof (WfP_set_depot U 1 1 1 s2 d W2 Hdf) as W3.
destruct (In_split_beg _ _ Hk (wf_chunks_nodup _ _ _ _ _ W2)) as (l1 & l2 & E & N1 & N2).
apply atok_bind. apply atok_modify. cbn [fst snd st_chunks set_depot]. rewrite E at 1.
rewrite upd_chunk_present by (reflexivity || exact N1). fold (quar_of k).
pose proof (WfP_flip U 1 1 1 (set_depot d s2) l1 k l2 W3 E Hst) as W4.
set (s4 := set_chunks (l1 ++ quar_of k :: l2) (set_depot d s2)) in *.
assert (Hni : ~ In (ck_beg (quar_of k)) (map ck_beg (q_items s4))).
{ cbn [quar_of ck_beg]. replace (q_items s4) with (q_items s2) by reflexivity. intros Hin.
apply in_map_iff in Hin as (k'' & Hb'' & Hk''). pose proof (proj1 (Forall_forall _ _) (wq_items _ (wf_quarantine _ _ _ _ _ W2)) k'' Hk'') as [H1 H2].
rewrite E in H1. apply in_app_iff in H1 as [H1|[<-|H1]]; [apply N1 | congruence | apply N2]; rewrite <- Hb''; apply in_map; exact H1. }
assert (CO4 : forall c', chunk_offs s4 c' = chunk_offs s c').
{ intros c'. apply chunk_offs_begs. subst s4. cbn [st_chunks set_chunks]. rewrite <- Fck, E, !map_app. reflexivity. }
assert (CD4 : forall c', cdef s4 c' = cdef s c').
{ intros c'. apply cdef_ext; [reflexivity|]. unfold class_elems. rewrite CO4. reflexivity. }
assert (NR4 : forall c', nrecZ s4 c' = nrecZ s c') by (intros c'; unfold nrecZ; rewrite CO4; reflexivity).
assert (PREG4 : preg s4 kBatchClass).
{ destruct Hreg as [Hev | ((CP & _) & HB & _)]; [left; subst s4 s2 s1; cbn; unfold EV_MAX in *; lia | right].
rewrite CD4, NR4. destruct (HB kBatchClass ltac:(unfold kBatchClass; lia)) as [HB1 HB2].
split; [exact (CP kBatchClass ltac:(unfold kBatchClass; lia)) | split; [exact HB1 | exact HB2]]. }
assert (HR4 : nrecZ s4 kBatchClass + 10248 <= 65536).
{ destruct Hreg as [Hev | (_ & HB & _)]; [| rewrite NR4; exact (proj2 (HB kBatchClass ltac:(unfold kBatchClass; lia)))].
apply (nrecZ_small U 1 1 1 s4 kBatchClass W4). subst s4 s2 s1. cbn. unfold EV_MAX in *. lia. }
apply atok_bind. eapply atok_mono; [|apply (enqueue_okx U 1 1 1 s4 (quar_of k) true W4 ltac:(lia) ltac:(lia) ltac:(subst s4; cbn; apply in_elt) eq_refl Hni PREG4)].
intros ns5 [[] s5] ((W5 & R1 & R2 & R3 & R4 & R5 & R6 & R7 & (nb5 & Q5 & NB5) & G5') & DEF5 & BIG5). cbn [fst snd] in *.
assert (HB45 : st_nev s5 <= EV_MAX \/ (Z.of_nat (length (st_chunks s5)) <= 2 ^ 23 /\ qc_bytes (st_qglobal s5) + qc_bytes (st_qthread s5) <= 2 ^ 36)).
{ destruct Hreg as [Hev | (_ & _ & _ & HCH & HQB)]; [left; rewrite R7; subst s4 s2 s1; cbn; unfold EV_MAX in *; lia | right]. split.
- rewrite R1. subst s4. cbn [st_chunks set_chunks]. rewrite <- Fck, E in HCH. rewrite !length_app in *. cbn [length] in *. lia.
- destruct (qc_list_push (st_qthread s4) (quar_of k) nb5 NB5) as (_ & _ & _ & _ & EBY). rewrite Q5, G5', EBY.
pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ W2) k Hk) as [HRK _].
assert (CK : ck_n (quar_of k) <= MALLOC_MAX) by (unfold ck_n, req_size, quar_of; cbn [ck_req]; destruct (ck_req k =? 0); unfold MALLOC_MAX in *; lia).
subst s4 s2 s1. cbn [st_qthread st_qglobal set_chunks set_depot set_internal_inited set_nev].
unfold MALLOC_MAX, kBatchBytes in *. destruct nb5; lia. }
eapply atok_mono; [|apply (maybe_drain_okx U 0 1 0 s5 ns5); [cbn in W5; exact W5 | exact HB45]].
intros ns6 [[] s6] ((W6 & (G1 & G2 & G3 & G4 & G5) & QT6 & QG6 & UQ6) & XF6). cbn [snd] in *. unfold free_post. cbn [snd].
pose proof (wf_slack _ _ _ _ _ W6).
assert (B4 : blocks s4 = map (fun k => (ck_user k, ck_req k)) (filter is_alloc l1) ++ map (fun k => (ck_user k, ck_req k)) (filter is_alloc l2)).
{ unfold blocks. subst s4. cbn [st_chunks set_chunks]. rewrite filter_app. cbn [filter is_alloc quar_of ck_state]. rewrite map_app. reflexivity. }
assert (B0 : blocks s = map (fun k => (ck_user k, ck_req k)) (filter is_alloc l1) ++ (q, n) :: map (fun k => (ck_user k, ck_req k)) (filter is_alloc l2)).
{ rewrite <- Fbl. unfold blocks. rewrite E, filter_app. cbn [filter]. unfold is_alloc at 2. rewrite Hst, map_app. cbn [map app]. rewrite Hu, Hr. reflexivity. }
assert (UQ0 : unq (set_depot d s2) = unq s) by (apply unq_same; [exact Fck | subst s2 s1; reflexivity | subst s2 s1; reflexivity]).
pose proof (unq_flip (set_depot d s2) l1 k l2 E Hst) as UQ4. fold s4 in UQ4.
pose proof (unq_push s4 s5 (quar_of k) nb5 R1 Q5 G5' NB5) as UQ5. change (ck_n (quar_of k)) with (ck_n k) in UQ5.
split; [splits | split].
7:{
intros [CP HB]. split.
- intros c' Hc'. rewrite (xfr_cdef _ _ _ XF6 c' Hc'), (DEF5 c' Hc'), CD4, (CP c' Hc'). lia.
- apply (xfr_BigP _ _ _ XF6). apply BIG5; [rewrite CD4; exact (CP kBatchClass ltac:(unfold kBatchClass; lia)) | exact HR4 |].
intros c' Hc'. exact (HB c' Hc'). }
7:{
destruct XF6 as (_ & _ & _ & K6 & C6 & S6 & B6). unfold fgrow. rewrite R1 in K6, C6. rewrite R2 in S6.
assert (L5 : (length (all_batches s5) <= length (all_batches s) + 1)%nat).
{ unfold all_batches. rewrite Q5, G5', !length_app. subst s4 s2 s1. cbn [st_qthread st_qglobal set_chunks set_depot set_internal_inited set_nev].
destruct nb5 as [off5|]; [cbn [qc_push qc_list]; rewrite length_app; cbn [length]; lia | rewrite length_qc_push_none; lia]. }
assert (K4 : length (st_chunks s4) = length (st_chunks s)).
{ subst s4. cbn [st_chunks set_chunks]. rewrite <- Fck, E, !length_app. reflexivity. }
assert (C4 : crw (st_chunks s4) = crw (st_chunks s)).
{ subst s4. cbn [st_chunks set_chunks]. rewrite <- Fck, E, !crw_app. reflexivity. }
assert (S4 : length (st_secs s4) = length (st_secs s)) by (subst s4; cbn [st_secs set_chunks set_depot]; rewrite Fsecs; reflexivity).
splits; lia. }
- unfold Wf. eapply WfP_weaken; [exact W6|lia|lia|lia].
- rewrite G1, R7. subst s4. cbn. exact Fnev.
- eapply secs_ext_trans; [|exact G5]. intros r0 sm0 E0. exists sm0. rewrite R2. subst s4. cbn. rewrite ?Fsecs. auto.
- unfold frames. rewrite G2, R5. subst s4. cbn. rewrite ?Ffs. reflexivity.
- eexists _, _. split; [right; exact B0|]. rewrite G4. unfold blocks. rewrite R1. fold (blocks s4). exact B4.
- intros (T1 & T2 & T3). split; [exact QT6 | split].
+ rewrite G5' in QG6. subst s4. cbn [st_qglobal set_chunks set_depot] in QG6. replace (st_qglobal s2) with (st_qglobal s) in QG6 by (subst s2 s1; reflexivity). lia.
+ unfold unq in *. lia.
Qed.
Theorem free_ok : forall U s p n tr,
universe_ok U ->
Wf U s -> aregime s   -> (p = PNull \/ In (p, n) (blocks s)) -> admits U tr s ->
atok true (free p tr s) (free_post U s p n).
Proof.
intros U s p n tr HU W Hev Hp Htr.
eapply atok_mono; [|exact (free_gen U s p n tr HU W (aregime_ok s Hev) Hp Htr)]. intros b r (H & _). exact H.
Qed.
Theorem free_big : forall U s p n tr,
universe_ok U ->
Wf U s -> regime_big s -> (p = PNull \/ In (p, n) (blocks s)) -> admits U tr s ->
atok true (free p tr s) (fun ns r => free_post U s p n ns r /\ BigInv (snd r) /\ fgrow s (snd r)).
Proof.
intros U s p n tr HU W Hbig Hp Htr.
eapply atok_mono; [|exact (free_gen U s p n tr HU W (or_intror Hbig) Hp Htr)]. intros b r (H1 & H2 & H3). split; [exact H1 | split; [exact (H2 (proj1 Hbig)) | exact H3]].
Qed.
