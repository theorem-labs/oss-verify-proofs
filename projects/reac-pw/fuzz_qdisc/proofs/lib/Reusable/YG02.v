(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YG02.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/Reusable/YG02.v at origin/ossv/recipes 6ebe35ba632 (fuzz_knock's released ASan tree); module paths changed to reac-pw/fuzz_qdisc. *)
From Stdlib Require Import ZArith List Bool Lia.
From Stdlib Require Import Sorting.Permutation.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YG00 YG0a YG01 YG04.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Lemma chunk_offs_set_regions : forall v s c, chunk_offs (set_regions v s) c = chunk_offs s c. Proof. reflexivity. Qed.
Lemma batch_offs_set_regions : forall v s c, batch_offs (set_regions v s) c = batch_offs s c. Proof. reflexivity. Qed.
Lemma chunk_offs_set_cache : forall v s c, chunk_offs (set_cache v s) c = chunk_offs s c. Proof. reflexivity. Qed.
Lemma batch_offs_set_cache : forall v s c, batch_offs (set_cache v s) c = batch_offs s c. Proof. reflexivity. Qed.
Lemma chunk_offs_set_cache_inited : forall v s c, chunk_offs (set_cache_inited v s) c = chunk_offs s c. Proof. reflexivity. Qed.
Lemma batch_offs_set_cache_inited : forall v s c, batch_offs (set_cache_inited v s) c = batch_offs s c. Proof. reflexivity. Qed.
Lemma reg_set_cache : forall v s c, reg (set_cache v s) c = reg s c. Proof. reflexivity. Qed.
Lemma reg_set_cache_inited : forall v s c, reg (set_cache_inited v s) c = reg s c. Proof. reflexivity. Qed.
Lemma cache_set_regions : forall v s c, cache (set_regions v s) c = cache s c. Proof. reflexivity. Qed.
Lemma cache_set_cache_inited : forall v s c, cache (set_cache_inited v s) c = cache s c. Proof. reflexivity. Qed.
Lemma reg_set_nev : forall v s c, reg (set_nev v s) c = reg s c. Proof. reflexivity. Qed.
Lemma cache_set_nev : forall v s c, cache (set_nev v s) c = cache s c. Proof. reflexivity. Qed.
Lemma fold_mapped_lupd : forall l i r,
(i < length l)%nat ->
fold_right (fun r acc => rg_mapped_user r + acc) 0 (lupd l i r)
= fold_right (fun r acc => rg_mapped_user r + acc) 0 l - rg_mapped_user (nth i l region0) + rg_mapped_user r.
Proof.
induction l as [|h t IH]; intros [|i] r Hi; cbn in *; try lia. rewrite IH; lia.
Qed.
Lemma fold_committed_lupd : forall l i r,
(i < length l)%nat ->
fold_right (fun r acc => rg_mapped_user r + rg_mapped_fa r + acc) 0 (lupd l i r)
= fold_right (fun r acc => rg_mapped_user r + rg_mapped_fa r + acc) 0 l
- (rg_mapped_user (nth i l region0) + rg_mapped_fa (nth i l region0)) + (rg_mapped_user r + rg_mapped_fa r).
Proof.
induction l as [|h t IH]; intros [|i] r Hi; cbn in *; try lia. rewrite IH; lia.
Qed.
Lemma prim_user_mapped_set_region : forall s c r, 0 <= c -> (Z.to_nat c < length (st_regions s))%nat ->
prim_user_mapped (set_regions (zupd c r (st_regions s)) s) = prim_user_mapped s - rg_mapped_user (reg s c) + rg_mapped_user r.
Proof.
intros s c r Hc Hl. unfold prim_user_mapped, zupd, reg, znth. cbn [st_regions set_regions]. apply fold_mapped_lupd. exact Hl.
Qed.
Lemma prim_committed_set_region : forall s c r, 0 <= c -> (Z.to_nat c < length (st_regions s))%nat ->
prim_committed (set_regions (zupd c r (st_regions s)) s)
= prim_committed s - (rg_mapped_user (reg s c) + rg_mapped_fa (reg s c)) + (rg_mapped_user r + rg_mapped_fa r).
Proof.
intros s c r Hc Hl. unfold prim_committed, zupd, reg, znth. cbn [st_regions set_regions]. apply fold_committed_lupd. exact Hl.
Qed.
Lemma fold_mapped_ge_nth : forall l i,
(forall j, (j < length l)%nat -> 0 <= rg_mapped_user (nth j l region0)) -> (i < length l)%nat ->
0 <= rg_mapped_user (nth i l region0) <= fold_right (fun r acc => rg_mapped_user r + acc) 0 l.
Proof.
induction l as [|h t IH]; intros [|i] Hall Hi; cbn in *; try lia.
- pose proof (Hall 0%nat ltac:(lia)) as H0. cbn in H0.
assert (Ht : 0 <= fold_right (fun r acc => rg_mapped_user r + acc) 0 t).
{ clear IH Hi. induction t as [|h' t' IH']; cbn; [lia|].
pose proof (Hall 1%nat ltac:(cbn; lia)) as H1. cbn in H1.
assert (0 <= fold_right (fun r acc => rg_mapped_user r + acc) 0 t'); [|lia].
apply IH'. intros [|j] Hj; [exact H0|]. apply (Hall (S (S j))). cbn. lia. }
lia.
- pose proof (Hall 0%nat ltac:(lia)) as H0. cbn in H0.
destruct (IH i) as [A1 A2]; [intros j Hj; apply (Hall (S j)); lia | lia | lia].
Qed.
Lemma regions_nonneg : forall U pp cc bb s j, WfP U pp cc bb s -> (j < length (st_regions s))%nat ->
0 <= rg_mapped_user (nth j (st_regions s) region0).
Proof.
intros U pp cc bb s j W Hj. rewrite (wf_len_regions _ _ _ _ _ W) in Hj.
destruct j as [|j].
- pose proof (wf_reg0 _ _ _ _ _ W) as H0. unfold reg, znth in H0. cbn in H0. rewrite H0. cbn. lia.
- pose proof (wr_alloc _ _ _ _ _ _ (wf_classes _ _ _ _ _ W (Z.of_nat (S j)) ltac:(lia))) as H.
unfold reg, znth in H. rewrite Nat2Z.id in H. lia.
Qed.
Lemma mapped_le_prim : forall U pp cc bb s c, WfP U pp cc bb s -> 0 <= c <= 31 ->
0 <= rg_mapped_user (reg s c) <= prim_user_mapped s.
Proof.
intros U pp cc bb s c W Hc. unfold reg, znth, prim_user_mapped.
apply fold_mapped_ge_nth; [intros j Hj; eapply regions_nonneg; eassumption|].
rewrite (wf_len_regions _ _ _ _ _ W). lia.
Qed.
Lemma wf_quar_ext : forall s s',
st_qthread s' = st_qthread s -> st_qglobal s' = st_qglobal s -> st_chunks s' = st_chunks s ->
wf_quar s -> wf_quar s'.
Proof.
intros s s' E1 E2 E3 W.
assert (EB : all_batches s' = all_batches s) by (unfold all_batches; rewrite E1, E2; reflexivity).
assert (EQ : q_items s' = q_items s) by (unfold q_items; rewrite EB; reflexivity).
destruct W. constructor; rewrite ?E1, ?E2, ?E3, ?EB, ?EQ; assumption.
Qed.
Lemma wf_sec_ext : forall s s',
st_sec_arr s' = st_sec_arr s -> st_secs s' = st_secs s -> st_chunks s' = st_chunks s -> st_sec_reserved s' = st_sec_reserved s ->
wf_sec s -> wf_sec s'.
Proof.
intros s s' E1 E2 E3 E4 W. destruct W. constructor; rewrite ?E1, ?E2, ?E3, ?E4; assumption.
Qed.
Lemma wf_fs_ext : forall s s', st_fs s' = st_fs s -> wf_fs s -> wf_fs s'.
Proof. intros s s' E W. destruct W. constructor; rewrite ?E; assumption. Qed.
Lemma chunk_ok_ext : forall s s' k, st_secs s' = st_secs s -> chunk_ok s k -> chunk_ok s' k.
Proof. intros s s' k E H. unfold chunk_ok in *. rewrite E. exact H. Qed.
Lemma Forall_chunk_ok_ext : forall s s' l, st_secs s' = st_secs s -> Forall (chunk_ok s) l -> Forall (chunk_ok s') l.
Proof. intros s s' l E H. eapply Forall_impl; [|exact H]. intros k. apply chunk_ok_ext. exact E. Qed.
Lemma regime_xfer : forall cc cc' (s s' : astate),
(st_nev s <= EV_MAX \/ BigM cc s) -> st_nev s' = st_nev s -> (BigP s -> BigP s') ->
Z.of_nat (length (st_chunks s')) + cc' <= Z.of_nat (length (st_chunks s)) + cc ->
st_nev s' <= EV_MAX \/ BigM cc' s'.
Proof. intros cc cc' s s' [H|[HP HC]] E HB L; [left; rewrite E; exact H | right; split; [exact (HB HP) | lia]]. Qed.
Ltac wf_fields W :=
pose proof (wf_len_regions _ _ _ _ _ W) as Xlr; pose proof (wf_len_cache _ _ _ _ _ W) as Xlc;
pose proof (wf_reg0 _ _ _ _ _ W) as Xr0; pose proof (wf_classes _ _ _ _ _ W) as Xcl;
pose proof (wf_chunks _ _ _ _ _ W) as Xck; pose proof (wf_chunks_nodup _ _ _ _ _ W) as Xnd;
pose proof (wf_chunks_ev _ _ _ _ _ W) as Xcev; pose proof (wf_prim_ev _ _ _ _ _ W) as Xpev;
pose proof (wf_live _ _ _ _ _ W) as Xlive; pose proof (wf_quarantine _ _ _ _ _ W) as Xq;
pose proof (wf_batches_ev _ _ _ _ _ W) as Xbev; pose proof (wf_secondary _ _ _ _ _ W) as Xsec;
pose proof (wf_fakestack _ _ _ _ _ W) as Xfs; pose proof (wf_depot _ _ _ _ _ W) as Xdep;
pose proof (wf_nev _ _ _ _ _ W) as Xnev; pose proof (wf_slack _ _ _ _ _ W) as Xsl;
pose proof (wf_qinited _ _ _ _ _ W) as Xqi; pose proof (wf_fa_room _ _ _ _ _ W) as Xroom;
pose proof (wf_secs_ev _ _ _ _ _ W) as Xsev; pose proof (wf_regime _ _ _ _ _ W) as Xreg.
Lemma wf_noholes : forall U pp cc bb s c, WfP U pp cc bb s -> 1 <= c <= 31 -> rg_holes (reg s c) = [].
Proof.
intros U pp cc bb s c W Hc. pose proof (proj1 (wr_holes _ _ _ _ _ _ (wf_classes _ _ _ _ _ W c Hc))) as Hh.
destruct (rg_holes (reg s c)) as [|h t]; [reflexivity|]. apply Forall_inv in Hh. destruct Hh.
Qed.
Ltac quar_fields Q :=
pose proof (wq_bytes_t _ Q) as Qbt; pose proof (wq_bytes_g _ Q) as Qbg; pose proof (wq_batches _ Q) as Qbat;
pose proof (wq_items _ Q) as Qit; pose proof (wq_nodup _ Q) as Qnd;
pose proof (wq_tfull _ Q) as Qtf; pose proof (wq_groups _ Q) as Qgr.
Ltac sec_fields X :=
pose proof (ws_nodup _ X) as Snd; pose proof (ws_arr_chunks _ X) as Sac; pose proof (ws_arr_live _ X) as Sal;
pose proof (ws_reserved _ X) as Sres; pose proof (ws_reserved_al _ X) as Sral; pose proof (ws_lens _ X) as Slen  .
Ltac wf_easy :=
first [ assumption
| match goal with H : wf_quar ?s0 |- wf_quar _ => apply (wf_quar_ext s0); [reflexivity | reflexivity | reflexivity | exact H] end
| match goal with H : wf_sec ?s0 |- wf_sec _ => apply (wf_sec_ext s0); [reflexivity | reflexivity | reflexivity | reflexivity | exact H] end
| match goal with H : wf_fs ?s0 |- wf_fs _ => apply (wf_fs_ext s0); [reflexivity | exact H] end
| match goal with H : all_batches ?s0 <> [] -> st_cache_inited ?s0 = true |- all_batches _ <> [] -> st_cache_inited _ = true =>
first [ exact H | (intros ?HB; apply H; exact HB) ] end
| match goal with H : forall c, 1 <= c <= 31 -> fa_room _ _ _ _ |- forall c, 1 <= c <= 31 -> fa_room _ _ _ _ => exact H end
| match goal with |- Z.of_nat (length (st_secs _)) + _ <= st_nev _ =>
solve [ cbn [st_secs st_nev set_chunks set_depot set_regions set_cache set_qthread set_qglobal set_nev set_sec_arr set_sec_reserved
set_cache_inited set_internal_inited set_fs]; lia ] end
| match goal with H : st_nev ?s0 <= EV_MAX \/ BigM _ ?s0 |- st_nev _ <= EV_MAX \/ BigM _ _ =>
first [ exact H
| solve [ apply (regime_xfer _ _ s0 _ H); [reflexivity | (intros ?HBP; exact HBP) |
cbn [st_chunks set_chunks set_depot set_regions set_cache set_qthread set_qglobal set_nev set_sec_arr set_sec_reserved set_secs
set_cache_inited set_internal_inited set_fs]; rewrite ?length_app; cbn [length]; lia] ] ] end
| idtac ].
Lemma wf_fa_room_ext : forall (s s' : astate) (k : Z -> Z),
(forall c, 1 <= c <= 31 -> length (class_elems s' c) = length (class_elems s c)) ->
st_regions s' = st_regions s -> st_nev s' = st_nev s ->
(forall c, 1 <= c <= 31 -> fa_room (rg_alloc_user (reg s c)) (length (class_elems s c)) (k c + 2 * (EV_MAX - st_nev s)) (rg_mapped_fa (reg s c))) ->
forall c, 1 <= c <= 31 -> fa_room (rg_alloc_user (reg s' c)) (length (class_elems s' c)) (k c + 2 * (EV_MAX - st_nev s')) (rg_mapped_fa (reg s' c)).
Proof. intros s s' k E R N H c Hc. unfold reg. rewrite E, R, N by exact Hc. apply H. exact Hc. Qed.
Lemma WfP_tick' : forall U s, Wf U s ->
(st_nev s < EV_MAX \/ (BigP s /\ Z.of_nat (length (st_chunks s)) + 1 <= 2 ^ 23)) ->
WfP U 1 1 1 (set_nev (st_nev s + 1) s).
Proof.
intros U s W Hreg. wf_fields W. constructor; wf_easy.
- cbn. lia.
- change (prim_user_mapped s + kUserMapSize * 1 <= kUserMapSize * (st_nev s + 1)). lia.
- change (Z.of_nat (length (all_batches s)) + 1 <= st_nev s + 1). lia.
- cbn. lia.
- lia.
- intros c Hc. eapply fa_room_xfer; [exact (Xroom c Hc) | | apply Z.le_refl].
change (class_elems (set_nev (st_nev s + 1) s) c) with (class_elems s c). cbn [st_nev set_nev]. unfold bslack. destruct (c =? kBatchClass); lia.
- destruct Hreg as [Hev|[HP HC]]; [left; cbn [st_nev set_nev]; lia | right; split; [exact HP | exact HC]].
Qed.
Lemma WfP_tick_small : forall U s, Wf U s -> st_nev s < EV_MAX -> WfP U 1 1 1 (set_nev (st_nev s + 1) s).
Proof. intros U s W Hev. apply WfP_tick'; [exact W | left; exact Hev]. Qed.
Lemma WfP_tick : forall U s, Wf U s -> aregime s -> WfP U 1 1 1 (set_nev (st_nev s + 1) s).
Proof.
intros U s W [Hev|(((_ & HP) & _ & _ & HC & _) & _)]; apply WfP_tick'; try exact W; [left; exact Hev | right; split; [exact HP | exact HC]].
Qed.
Lemma WfP_set_region : forall U pp cc bb s c r' pp',
WfP U pp cc bb s -> 1 <= c <= 31 ->
cls_ok c r' (cache s c) (st_cache_inited s) (chunk_offs s c) (batch_offs s c) ->
0 <= pp' ->
prim_user_mapped s - rg_mapped_user (reg s c) + rg_mapped_user r' + kUserMapSize * pp' <= kUserMapSize * st_nev s ->
fa_room (rg_alloc_user r') (length (fa_elems (class_size c) (rg_free r') ++ pc_chunks (cache s c) ++ chunk_offs s c ++ batch_offs s c))
(cc + bslack c bb + 2 * (EV_MAX - st_nev s)) (rg_mapped_fa r') ->
(st_nev s <= EV_MAX \/ rg_alloc_user r' = 0 \/ 4 * (rg_alloc_user r' / class_size c) <= rg_mapped_fa r') ->
WfP U pp' cc bb (set_regions (zupd c r' (st_regions s)) s).
Proof.
intros U pp cc bb s c r' pp' W Hc Hcls Hpp' Hbound Hroom Hcap.
assert (Hlen : (Z.to_nat c < length (st_regions s))%nat) by (rewrite (wf_len_regions _ _ _ _ _ W); lia).
wf_fields W. constructor; wf_easy.
- cbn. rewrite zupd_length. assumption.
- rewrite reg_upd_other; [assumption | lia | lia | lia].
- intros c' Hc'. unfold wf_class. rewrite cache_set_regions, chunk_offs_set_regions, batch_offs_set_regions. cbn [st_cache_inited set_regions].
destruct (Z.eq_dec c c') as [<-|Hne].
+ rewrite reg_upd_same; [exact Hcls | lia | exact Hlen].
+ rewrite reg_upd_other; [ | lia | lia | exact Hne]. exact (Xcl c' Hc').
- change (prim_user_mapped (set_regions (zupd c r' (st_regions s)) s) + kUserMapSize * pp' <= kUserMapSize * st_nev s).
rewrite prim_user_mapped_set_region; [| lia | exact Hlen]. exact Hbound.
- lia.
- intros c' Hc'. unfold class_elems. rewrite cache_set_regions, chunk_offs_set_regions, batch_offs_set_regions. cbn [st_nev set_regions].
destruct (Z.eq_dec c c') as [<-|Hne].
+ rewrite reg_upd_same; [exact Hroom | lia | exact Hlen].
+ rewrite reg_upd_other; [ | lia | lia | exact Hne]. exact (Xroom c' Hc').
-
destruct Hcap as [Hs|Hcap]; [left; exact Hs|]. destruct Xreg as [Hs|[HP HC]]; [left; exact Hs|]. right. split; [|exact HC].
intros c' Hc'. destruct (Z.eq_dec c c') as [<-|Hne].
+ rewrite reg_upd_same; [exact Hcap | lia | exact Hlen].
+ rewrite reg_upd_other; [ | lia | lia | exact Hne]. exact (HP c' Hc').
Qed.
Lemma WfP_set_pc : forall U pp cc bb s c p',
WfP U pp cc bb s -> 1 <= c <= 31 ->
cls_ok c (reg s c) p' (st_cache_inited s) (chunk_offs s c) (batch_offs s c) ->
fa_room (rg_alloc_user (reg s c)) (length (fa_elems (class_size c) (rg_free (reg s c)) ++ pc_chunks p' ++ chunk_offs s c ++ batch_offs s c))
(cc + bslack c bb + 2 * (EV_MAX - st_nev s)) (rg_mapped_fa (reg s c)) ->
WfP U pp cc bb (set_cache (zupd c p' (st_cache s)) s).
Proof.
intros U pp cc bb s c p' W Hc Hcls Hroom.
assert (Hlen : (Z.to_nat c < length (st_cache s))%nat) by (rewrite (wf_len_cache _ _ _ _ _ W); lia).
wf_fields W. constructor; wf_easy.
- cbn. rewrite zupd_length. assumption.
- intros c' Hc'. unfold wf_class. rewrite reg_set_cache, chunk_offs_set_cache, batch_offs_set_cache. cbn [st_cache_inited set_cache].
destruct (Z.eq_dec c c') as [<-|Hne].
+ rewrite cache_upd_same; [exact Hcls | lia | exact Hlen].
+ rewrite cache_upd_other; [ | lia | lia | exact Hne]. exact (Xcl c' Hc').
- intros c' Hc'. unfold class_elems. rewrite reg_set_cache, chunk_offs_set_cache, batch_offs_set_cache. cbn [st_nev set_cache].
destruct (Z.eq_dec c c') as [<-|Hne].
+ rewrite cache_upd_same; [exact Hroom | lia | exact Hlen].
+ rewrite cache_upd_other; [ | lia | lia | exact Hne]. exact (Xroom c' Hc').
Qed.
Lemma cls_ok_repart : forall c r p (i : bool) ko bo r' p' (i' : bool) ko' bo' extra,
cls_ok c r p i ko bo ->
rg_mapped_user r' = rg_mapped_user r -> rg_alloc_user r' = rg_alloc_user r -> rg_mapped_fa r' = rg_mapped_fa r ->
rg_holes r' = rg_holes r ->
runs_ok (rg_free r') -> 4 * fa_len (rg_free r') <= rg_mapped_fa r ->
(if i' then pc_max p' = max_cached c /\ Z.of_nat (length (pc_chunks p')) <= max_cached c else p' = pclass0) ->
Permutation (fa_elems (class_size c) (rg_free r) ++ pc_chunks p ++ ko ++ bo)
(extra ++ fa_elems (class_size c) (rg_free r') ++ pc_chunks p' ++ ko' ++ bo') ->
cls_ok c r' p' i' ko' bo'.
Proof.
intros c r p i ko bo r' p' i' ko' bo' extra C E1 E2 E3 E4 Hruns Hfl Hcache HP.
pose proof (wr_alloc _ _ _ _ _ _ C). pose proof (wr_mapped_al _ _ _ _ _ _ C). pose proof (wr_alloc_al _ _ _ _ _ _ C).
pose proof (wr_fa _ _ _ _ _ _ C). pose proof (wr_fa_bound _ _ _ _ _ _ C). pose proof (wr_holes _ _ _ _ _ _ C).
pose proof (wr_carved _ _ _ _ _ _ C). pose proof (wr_mapped_bound _ _ _ _ _ _ C).
constructor; rewrite ?E1, ?E2, ?E3, ?E4; try assumption.
- pose proof (Permutation_NoDup HP (wr_nodup _ _ _ _ _ _ C)) as ND. apply NoDup_app_iff in ND as (_ & ND & _). exact ND.
- pose proof (Forall_Permutation _ _ _ HP (wr_elems _ _ _ _ _ _ C)) as FA. apply Forall_app in FA as [_ FA]. exact FA.
Qed.
Lemma cls_ok_take : forall c r p i ko bo x rest,
cls_ok c r p i ko bo ->
Permutation (fa_elems (class_size c) (rg_free r) ++ pc_chunks p ++ ko ++ bo) (x :: rest) ->
0 <= x < rg_alloc_user r /\ x mod class_size c = 0 /\ ~ In x rest /\ NoDup rest.
Proof.
intros c r p i ko bo x rest C HP.
pose proof (Permutation_NoDup HP (wr_nodup _ _ _ _ _ _ C)) as ND. inversion ND; subst.
pose proof (Forall_Permutation _ _ _ HP (wr_elems _ _ _ _ _ _ C)) as FA. inversion FA; subst. tauto.
Qed.
Lemma length_init_caches : forall l, length (init_caches l) = 32%nat.
Proof. intros l. unfold init_caches. rewrite length_map, length_seq. reflexivity. Qed.
Lemma nth_init_caches : forall l i, (i < 32)%nat ->
nth i (init_caches l) pclass0 = mkPC (max_cached (Z.of_nat i)) (pc_chunks (nth i l pclass0)).
Proof.
intros l i Hi. unfold init_caches.
assert (G : forall base k, (k < 32 - base)%nat ->
nth k (map (fun c : nat => mkPC (max_cached (Z.of_nat c)) (pc_chunks (nth c l pclass0))) (seq base (32 - base))) pclass0
= mkPC (max_cached (Z.of_nat (base + k))) (pc_chunks (nth (base + k) l pclass0))).
{ intros base. remember (32 - base)%nat as n. revert base Heqn. induction n as [|n IH]; intros base Hn k Hk; [lia|].
cbn [seq map]. destruct k as [|k]; [rewrite Nat.add_0_r; reflexivity|]. cbn [nth].
rewrite (IH (S base)); [|lia|lia]. rewrite Nat.add_succ_r. reflexivity. }
pose proof (G 0%nat i ltac:(lia)) as G0. cbn [Nat.add Nat.sub] in G0. exact G0.
Qed.
Lemma cache_after_init : forall s c, 0 <= c <= 31 ->
cache (set_cache_inited true (set_cache (init_caches (st_cache s)) s)) c = mkPC (max_cached c) (pc_chunks (cache s c)).
Proof.
intros s c Hc. unfold cache, znth. cbn [st_cache set_cache_inited set_cache].
rewrite nth_init_caches by lia. rewrite Z2Nat.id by lia. reflexivity.
Qed.
Lemma WfP_init_caches : forall U pp cc bb s,
WfP U pp cc bb s -> st_cache_inited s = false ->
WfP U pp cc bb (set_cache_inited true (set_cache (init_caches (st_cache s)) s)).
Proof.
intros U pp cc bb s W Hi. wf_fields W. constructor; wf_easy.
- cbn [st_cache set_cache_inited set_cache]. apply length_init_caches.
- intros c' Hc'. pose proof (Xcl c' Hc') as C. unfold wf_class in *.
rewrite reg_set_cache_inited, reg_set_cache, chunk_offs_set_cache_inited, chunk_offs_set_cache,
batch_offs_set_cache_inited, batch_offs_set_cache, cache_after_init by lia.
cbn [st_cache_inited set_cache_inited]. rewrite Hi in C.
pose proof (wr_cache _ _ _ _ _ _ C) as Hp. cbn in Hp. rewrite Hp in C |- *. cbn [pc_chunks pclass0].
eapply (cls_ok_repart c' _ _ false _ _ _ _ true _ _ []); try exact C; try reflexivity.
+ exact (wr_runs _ _ _ _ _ _ C).
+ exact (wr_fa_len _ _ _ _ _ _ C).
+ cbn [pc_max pc_chunks length Z.of_nat]. split; [reflexivity|]. pose proof (class_ok c' Hc'). lia.
- intros _. reflexivity.
- intros c' Hc'. pose proof (Xroom c' Hc') as R. pose proof (Xcl c' Hc') as C. unfold wf_class in C. rewrite Hi in C.
pose proof (wr_cache _ _ _ _ _ _ C) as Hp. unfold class_elems in *.
rewrite reg_set_cache_inited, reg_set_cache, chunk_offs_set_cache_inited, chunk_offs_set_cache,
batch_offs_set_cache_inited, batch_offs_set_cache, cache_after_init by lia.
cbn [st_nev set_cache_inited set_cache pc_chunks]. rewrite Hp in R |- *. cbn [pc_chunks pclass0] in R |- *. exact R.
Qed.
Lemma chunk_offs_app : forall s l c, chunk_offs (set_chunks (st_chunks s ++ l) s) c = chunk_offs s c ++ chunk_offs (set_chunks l s) c.
Proof. intros s l c. unfold chunk_offs. cbn [st_chunks set_chunks]. rewrite flat_map_app. reflexivity. Qed.
Lemma chunk_offs_one_prim : forall s off n st c,
chunk_offs (set_chunks [mkChunk (PPrim off) n st] s) c = if prim_class off =? c then [off - region_off c] else [].
Proof. intros. unfold chunk_offs. cbn [flat_map st_chunks set_chunks ck_beg app]. destruct (prim_class off =? c); reflexivity. Qed.
Lemma batch_offs_set_chunks : forall v s c, batch_offs (set_chunks v s) c = batch_offs s c. Proof. reflexivity. Qed.
Lemma reg_set_chunks : forall v s c, reg (set_chunks v s) c = reg s c. Proof. reflexivity. Qed.
Lemma cache_set_chunks : forall v s c, cache (set_chunks v s) c = cache s c. Proof. reflexivity. Qed.
Lemma all_batches_set_chunks : forall v s, all_batches (set_chunks v s) = all_batches s. Proof. reflexivity. Qed.
Lemma q_items_set_chunks : forall v s, q_items (set_chunks v s) = q_items s. Proof. reflexivity. Qed.
Lemma blocks_bytes_app1 : forall s k, blocks_bytes (set_chunks (st_chunks s ++ [k]) s) = blocks_bytes s + (if is_alloc k then ck_req k else 0).
Proof.
intros s k. unfold blocks_bytes. cbn [st_chunks set_chunks].
induction (st_chunks s) as [|h t IH]; cbn; [destruct (is_alloc k); lia | rewrite IH; destruct (is_alloc h); lia].
Qed.
Lemma WfP_add_prim_chunk : forall U pp cc bb s off n,
WfP U pp cc bb s -> 1 <= cc ->
0 <= n < MALLOC_MAX -> from_primary n = true ->
prim_class off = chunk_class n -> 0 <= off - region_off (chunk_class n) < 2 ^ 32 ->
cls_ok (chunk_class n) (reg s (chunk_class n)) (cache s (chunk_class n)) (st_cache_inited s)
(chunk_offs s (chunk_class n) ++ [off - region_off (chunk_class n)]) (batch_offs s (chunk_class n)) ->
~ In (PPrim off) (map ck_beg (st_chunks s)) ->
blocks_bytes s + n <= LIVE_MAX ->
WfP U pp (cc - 1) bb (set_chunks (st_chunks s ++ [mkChunk (PPrim off) n CAllocated]) s).
Proof.
intros U pp cc bb s off n W Hcc Hn Hprim Hcls Hoff Hcls' Hfresh Hlive.
assert (Hn0 : 0 <= n) by lia. destruct (primary_geometry n Hn0 Hprim) as [G1 Grest].
wf_fields W. constructor; wf_easy.
- intros c' Hc'. unfold wf_class. rewrite reg_set_chunks, cache_set_chunks, batch_offs_set_chunks, chunk_offs_app, chunk_offs_one_prim.
cbn [st_cache_inited set_chunks]. rewrite Hcls.
destruct (Z.eqb_spec (chunk_class n) c') as [<-|Hne]; [exact Hcls'|]. rewrite app_nil_r. exact (Xcl c' Hc').
- cbn [st_chunks set_chunks]. apply Forall_app. split.
+ eapply Forall_chunk_ok_ext; [reflexivity | exact Xck].
+ constructor; [|constructor]. unfold chunk_ok. cbn [ck_req ck_beg st_secs set_chunks]. rewrite Hcls. split; [lia|]. split; [exact Hprim|]. split; [reflexivity|]. exact Hoff.
- cbn [st_chunks set_chunks]. rewrite map_app. cbn [map ck_beg]. apply NoDup_app_iff. split; [exact Xnd|]. split; [repeat constructor; intros []|].
intros x Hx [<-|[]]. exact (Hfresh Hx).
- cbn [st_chunks set_chunks st_nev]. rewrite length_app. cbn [length]. lia.
- rewrite blocks_bytes_app1. cbn [is_alloc ck_state ck_req]. lia.
- quar_fields Xq. constructor; rewrite ?all_batches_set_chunks, ?q_items_set_chunks; cbn [st_qthread st_qglobal st_chunks set_chunks]; try assumption.
+ eapply Forall_impl; [|exact Qit]. intros k [Hk Hs]. split; [apply in_app_iff; left; exact Hk | exact Hs].
- sec_fields Xsec. constructor; cbn [st_sec_arr st_secs st_chunks st_sec_reserved set_chunks]; try assumption.
intros r. rewrite Sac. split.
+ intros (k & Hk & Hb). exists k. split; [apply in_app_iff; left; exact Hk | exact Hb].
+ intros (k & Hk & Hb). apply in_app_iff in Hk as [Hk|[<-|[]]]; [exists k; auto | cbn in Hb; discriminate].
- lia.
- intros c' Hc'. unfold class_elems. rewrite reg_set_chunks, cache_set_chunks, batch_offs_set_chunks, chunk_offs_app, chunk_offs_one_prim.
cbn [st_nev set_chunks]. rewrite Hcls. pose proof (Xroom c' Hc') as R. unfold class_elems in R.
destruct (Z.eqb_spec (chunk_class n) c') as [<-|Hne].
+ eapply fa_room_xfer; [exact R | rewrite !length_app; cbn [length]; lia | apply Z.le_refl].
+ rewrite app_nil_r. eapply fa_room_xfer; [exact R | lia | apply Z.le_refl].
Qed.
