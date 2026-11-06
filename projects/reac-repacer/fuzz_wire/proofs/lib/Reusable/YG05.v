(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YG05.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_grant/lib/Reusable/YG05.v at 4f87de75d677 (donor image sha256 c2c7559b29bd), with its module paths changed. *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From Stdlib Require Import Sorting.Permutation.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG0u.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG0d.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Local Open Scope am_scope.
Ltac splits := repeat lazymatch goal with |- _ /\ _ => split end.
Lemma fs_frames_pos : forall cid, 0 <= cid <= 10 -> 0 < fs_frames cid.
Proof. intros cid H. unfold fs_frames, kStackSizeLog. rewrite Z.shiftl_1_l. apply Z.pow_pos_nonneg; lia. Qed.
Lemma mem_pos_spec : forall l cid pos, mem_pos l cid pos = true <-> In (cid, pos) l.
Proof.
induction l as [|[c p] t IH]; intros cid pos; cbn [mem_pos]; [split; [discriminate | intros []]|].
rewrite Bool.orb_true_iff, Bool.andb_true_iff, !Z.eqb_eq, IH. split.
- intros [[-> ->]|H]; [left; reflexivity | right; exact H].
- intros [E|H]; [injection E as -> ->; left; split; reflexivity | right; exact H].
Qed.
Lemma mem_pos_false : forall l cid pos, mem_pos l cid pos = false -> ~ In (cid, pos) l.
Proof. intros l cid pos H Hin. apply mem_pos_spec in Hin. congruence. Qed.
Lemma fs_probe_some : forall fuel live cid hint pos hint',
0 < fs_frames cid -> fs_probe fuel live cid hint = Some (pos, hint') ->
exists h, hint <= h /\ hint' = h + 1 /\ pos = h mod fs_frames cid /\ mem_pos live cid pos = false.
Proof.
induction fuel as [|f IH]; intros live cid hint pos hint' HN H; cbn [fs_probe] in H; [discriminate|].
destruct (mem_pos live cid (hint mod fs_frames cid)) eqn:E.
- apply IH in H as (h & H1 & H2 & H3 & H4); [|exact HN]. exists h. splits; auto; lia.
- injection H as <- <-. exists hint. splits; auto; lia.
Qed.
Lemma fs_probe_none : forall fuel live cid hint,
fs_probe fuel live cid hint = None -> forall j, (j < fuel)%nat -> mem_pos live cid ((hint + Z.of_nat j) mod fs_frames cid) = true.
Proof.
induction fuel as [|f IH]; intros live cid hint H j Hj; [lia|]. cbn [fs_probe] in H.
destruct (mem_pos live cid (hint mod fs_frames cid)) eqn:E; [|discriminate].
destruct j as [|j]; [rewrite Z.add_0_r; exact E|].
replace (hint + Z.of_nat (S j)) with (hint + 1 + Z.of_nat j) by lia. apply (IH live cid (hint + 1) H j). lia.
Qed.
Lemma count_cid_nonneg : forall cid l, 0 <= count_cid cid l.
Proof. intros cid l. induction l as [|[c p] t IH]; cbn [count_cid]; [lia|]. destruct (c =? cid); lia. Qed.
Lemma count_cid_filter : forall cid l, count_cid cid l = Z.of_nat (length (filter (fun cp => fst cp =? cid) l)).
Proof.
intros cid l. induction l as [|[c p] t IH]; cbn [count_cid filter fst]; [reflexivity|].
rewrite IH. destruct (c =? cid); cbn [length]; lia.
Qed.
Lemma count_cid_ge : forall cid live ps,
NoDup ps -> Forall (fun p => In (cid, p) live) ps -> Z.of_nat (length ps) <= count_cid cid live.
Proof.
intros cid live ps Hnd Hall. rewrite count_cid_filter, <- (length_map (fun p => (cid, p)) ps). apply inj_le.
apply NoDup_incl_length.
- apply NoDup_map_NoDup_ForallPairs; [|exact Hnd]. intros a b _ _ E. injection E. auto.
- intros cp Hcp. apply in_map_iff in Hcp as (p & <- & Hp). apply filter_In. split; [exact (proj1 (Forall_forall _ _) Hall p Hp) | cbn; apply Z.eqb_refl].
Qed.
Lemma mod_window_nodup : forall N hint n, 0 < N -> (Z.of_nat n <= N) ->
NoDup (map (fun j => (hint + Z.of_nat j) mod N) (seq 0 n)).
Proof.
intros N hint n HN Hn. apply NoDup_map_NoDup_ForallPairs; [|apply seq_NoDup].
intros j1 j2 Hj1 Hj2 E. apply in_seq in Hj1. apply in_seq in Hj2.
assert (D : ((hint + Z.of_nat j1) - (hint + Z.of_nat j2)) mod N = 0).
{ rewrite Zminus_mod, E, Z.sub_diag. apply Z.mod_0_l. lia. }
apply Z.mod_divide in D as [q Hq]; [|lia].
assert (q = 0) by nia. subst q. lia.
Qed.
Theorem stack_malloc_progress : forall U s cid,
Wf U s -> 0 <= cid <= 10 -> count_cid cid (frames s) < fs_frames cid ->
exists pos s', apath (stack_malloc cid s) [] (PFake cid pos, s').
Proof.
intros U s cid W Hc Hcnt. pose proof (fs_frames_pos cid Hc) as HN.
unfold stack_malloc, bind, get, put, ret. cbn [ibind].
destruct (fs_probe (Z.to_nat (fs_frames cid)) (fs_live (st_fs s)) cid (znth 0 cid (fs_hint (st_fs s)))) as [[pos hint']|] eqn:EP.
- cbn [ibind]. exists pos. eexists. reflexivity.
- exfalso. set (N := fs_frames cid) in *. set (hint := znth 0 cid (fs_hint (st_fs s))) in *.
pose proof (fs_probe_none _ _ _ _ EP) as ALL.
pose proof (count_cid_ge cid (fs_live (st_fs s)) (map (fun j => (hint + Z.of_nat j) mod N) (seq 0 (Z.to_nat N)))
(mod_window_nodup N hint (Z.to_nat N) HN ltac:(lia))) as GE.
rewrite length_map, length_seq in GE. unfold frames in Hcnt.
specialize (GE ltac:(apply Forall_forall; intros p Hp; apply in_map_iff in Hp as (j & <- & Hj); apply in_seq in Hj;
apply mem_pos_spec; apply ALL; lia)). lia.
Qed.
Lemma Wf_push_frame : forall U s cid pos hint',
Wf U s -> 0 <= cid <= 10 -> 0 <= pos < fs_frames cid -> 0 <= hint' -> ~ In (cid, pos) (frames s) ->
Wf U (set_fs (mkFS (zupd cid hint' (fs_hint (st_fs s))) ((cid, pos) :: fs_live (st_fs s))) s).
Proof.
intros U s cid pos hint' W Hc Hpos Hh Hni. unfold Wf in *. wf_fields W. constructor; wf_easy.
destruct Xfs as [[L F] ND LV]. constructor; cbn [st_fs set_fs fs_hint fs_live].
- split; [rewrite zupd_length; exact L|]. unfold zupd.
apply Forall_nth. intros i d Hi. rewrite lupd_length in Hi. destruct (Nat.eq_dec i (Z.to_nat cid)) as [->|Hne].
+ rewrite nth_lupd_same by lia. exact Hh.
+ rewrite nth_lupd_other by (intros E; apply Hne; symmetry; exact E). exact (proj1 (Forall_nth _ _) F i d Hi).
- constructor; [exact Hni | exact ND].
- constructor; [cbn; lia | exact LV].
Qed.
Theorem stack_malloc_ok : forall U s cid,
Wf U s -> 0 <= cid <= 10 -> atok true (stack_malloc cid s) (stack_malloc_post U s cid).
Proof.
intros U s cid W Hc. pose proof (fs_frames_pos cid Hc) as HN.
unfold stack_malloc. apply atok_bind. apply atok_get. cbn [fst snd].
destruct (fs_probe _ _ _ _) as [[pos hint']|] eqn:EP.
- apply fs_probe_some in EP as (h & H1 & -> & -> & H4); [|exact HN].
apply atok_bind. apply atok_put. cbn [fst snd]. apply atok_ret. cbn -[Z.add Z.modulo fs_frames zupd Wf In].
pose proof (wfs_hints _ (wf_fakestack _ _ _ _ _ W)) as [L F].
assert (Hh : 0 <= znth 0 cid (fs_hint (st_fs s))).
{ unfold znth. destruct (nth_in_or_default (Z.to_nat cid) (fs_hint (st_fs s)) 0) as [Hin| ->]; [|lia].
exact (proj1 (Forall_forall _ _) F _ Hin). }
pose proof (Z.mod_pos_bound h (fs_frames cid) HN) as MB.
splits; try reflexivity; try lia.
+ apply Wf_push_frame; [exact W | exact Hc | exact MB | lia | unfold frames; apply mem_pos_false; exact H4].
+ eexists. reflexivity.
+ unfold frames. apply mem_pos_false. exact H4.
- apply atok_ret. cbn. split; [exact W | split; [exists (st_fs s); destruct s; reflexivity | reflexivity]].
Qed.
Lemma del_pos_spec : forall l cid pos, NoDup l -> In (cid, pos) l -> exists l1 l2, l = l1 ++ (cid, pos) :: l2 /\ del_pos l cid pos = l1 ++ l2.
Proof.
induction l as [|[c p] t IH]; intros cid pos Hnd Hin; [destruct Hin|]. cbn [del_pos].
destruct (andb (c =? cid) (p =? pos)) eqn:E.
- apply Bool.andb_true_iff in E as [E1 E2]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. subst. exists [], t. split; reflexivity.
- destruct Hin as [Heq|Hin]; [injection Heq as -> ->; rewrite !Z.eqb_refl in E; discriminate|].
inversion Hnd; subst. destruct (IH cid pos ltac:(assumption) Hin) as (l1 & l2 & -> & E2).
exists ((c, p) :: l1), l2. rewrite E2. split; reflexivity.
Qed.
Theorem stack_free_ok : forall U s cid pos,
Wf U s -> In (cid, pos) (frames s) -> stack_free_post U s cid pos.
Proof.
intros U s cid pos W Hin. unfold stack_free_post, stack_free_state.
pose proof (wf_fakestack _ _ _ _ _ W) as X. destruct X as [[L F] ND LV].
destruct (del_pos_spec _ _ _ ND Hin) as (l1 & l2 & E & ED). unfold frames in *. split.
- unfold Wf in *. wf_fields W. constructor; wf_easy. constructor; cbn [st_fs set_fs fs_hint fs_live].
+ split; assumption.
+ rewrite ED. rewrite E in ND. exact (NoDup_remove_1 _ _ _ ND).
+ rewrite ED. rewrite E in LV. apply Forall_app in LV as [LV1 LV2]. inversion LV2; subst. apply Forall_app. auto.
- exists l1, l2. cbn. rewrite ED. auto.
Qed.
Theorem model_laws_ok : forall U, universe_ok U -> model_laws U.
Proof.
intros U HU. constructor.
- intros s n tr W Hev. apply malloc_ok; [exact HU | exact W | exact (aregime_small s Hev)].
- intros s p n tr W Hev. apply free_ok; [exact HU | exact W | exact (aregime_small s Hev)].
- intros s cid. apply stack_malloc_ok.
- intros s cid. apply stack_malloc_progress.
- intros s cid pos. apply stack_free_ok.
- intros s n tr. apply malloc_big. exact HU.
- intros s p n tr. apply free_big. exact HU.
-   intros s n tr W Hreg Hn Hlive Htr.
eapply atok_mono; [|exact (YG0u.malloc_gen_ns U s n tr HU W Hreg Hn Hlive Htr)]. intros b r (H0 & H & _). split; [exact H | exact H0].
Qed.
Lemma BigInv_set_fs : forall f s, BigInv (set_fs f s) <-> BigInv s.
Proof. intros f s. split; intros H; exact H. Qed.
Lemma regime_big_set_fs : forall f s, regime_big (set_fs f s) <-> regime_big s.
Proof. intros f s. split; intros H; exact H. Qed.
Lemma regime_ok_small : forall s, st_nev s < EV_MAX -> regime_ok s.
Proof. intros s H. left. exact H. Qed.
