(* CARRIED from commit 0deb5310273b0d538ec2a1697f391a1c8ad21c34,
   proofs/cgif/cgif_file_fuzzer/lib/YGcfCount.v, sha256 f04afd970af85fe747603cc7cf13996bc56a9d948bb6828adc14f6656615161f (donor version not released; internal record).
   DO NOT EDIT in this tree: change it on that branch and carry it again. The changes made here are in the Require lines only:
   the module prefix OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable
   (lib.Spec -> fuzz_reply.lib.Spec).
*)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30: the header points to YGcfSecsStep.v for the model-level steps. *)
(* Theorem Labs, 2026-10-30: the run's user-secondary count for reply's KF-COUNT (Main 2026-10-30). nsec_cf
   (YG0ncf.v) counts the USER st_secs entries (sec_user_cf, YGcfNames.v: 0 <= sm_size; the errbuf's control entries
   carry a negative sm_size and stay out). This file states it at the three st_secs steps over the state shapes
   (nsec_cf_alloc: a granted secondary appends one user entry; nsec_cf_kill: a recycle kills an entry in place;
   nsec_cf_errb: an errbuf step, secs_errb_grow, keeps it), names the recycled secondaries dead_secs_cf (the user
   entries that are dead), and bounds the kit's eviction count by it: kf_le_nsec_cf, D + qsec_cf S <= nsec_cf S
   (every quarantined secondary chunk names its own live user entry, distinct chunks distinct entries). The model-
   level step lemmas over the cf operations are YGcfSecsStep.v's (YGcfNsec.v restates five of them in YGcfXs.v's
   cfx_ipost form). No function is proved here (rule 24). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YGcfNames YG01cf YG00cf YG0ncf
YGcfLazyResid.
(* stdpp, through the LPS modules, shadows NoDup and Forall_forall; the lemmas here are Stdlib's. *)
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------- *)
(* 1. Sums over lists. cfa_fold_lupd is YGcfAbudget.v's lemma, restated here so that this file stays below       *)
(*    YGcfAbudget.v (the budget's hull terms read dead_secs_cf and nsec_cf).                                     *)
Lemma cfa_fold_app1 {X : Type} (F : X -> Z -> Z) (g : X -> Z) :
(forall x a, F x a = g x + a) -> forall l x, fold_right F 0 (l ++ [x]) = fold_right F 0 l + g x.
Proof.
intros HF l x. induction l as [|y t IH]; cbn [app fold_right].
- rewrite HF. lia.
- rewrite !HF, IH. lia.
Qed.

Lemma cfa_fold_lupd {X : Type} (F : X -> Z -> Z) (g : X -> Z) :
(forall x a, F x a = g x + a) ->
forall l i v x, nth_error l i = Some x -> fold_right F 0 (lupd l i v) = fold_right F 0 l - g x + g v.
Proof.
intros HF l. induction l as [|y t IH]; intros i v x Hn; [destruct i; discriminate Hn|].
destruct i as [|i]; cbn [lupd fold_right nth_error] in *.
- injection Hn as <-. rewrite !HF. lia.
- rewrite !HF, (IH i v x Hn). lia.
Qed.

Lemma cfa_sum_zero : forall (g : secmap -> Z) l, (forall sm, In sm l -> g sm = 0) ->
fold_right (fun sm acc => g sm + acc) 0 l = 0.
Proof.
intros g l. induction l as [|a t IH]; intros H; cbn [fold_right]; [reflexivity|].
rewrite (H a (or_introl eq_refl)), (IH (fun sm Hs => H sm (or_intror Hs))). reflexivity.
Qed.

Lemma user_true : forall sm, 0 <= sm_size sm -> sec_user_cf sm = true.
Proof. intros sm H. unfold sec_user_cf. apply Z.leb_le. exact H. Qed.

Lemma user_false : forall sm, sm_size sm < 0 -> sec_user_cf sm = false.
Proof. intros sm H. unfold sec_user_cf. apply Z.leb_gt. exact H. Qed.

Lemma seg_cons : forall a t l', secs_errb_grow (a :: t) l' ->
exists a' t', l' = a' :: t' /\ (0 <= sm_size a -> a' = a) /\ (sm_size a < 0 -> sm_size a' < 0 /\ sm_len a <= sm_len a') /\
secs_errb_grow t t'.
Proof.
intros a t l' [HL [HP HA]]. destruct l' as [|a' t']; [cbn in HL; exfalso; lia|].
destruct (HP 0%nat a eq_refl) as (sm' & E & H1 & H2). cbn in E. injection E as <-.
exists a', t'. split; [reflexivity|]. split; [exact H1|]. split; [exact H2|].
split; [cbn in HL; lia|]. split.
- intros i sm Hn. destruct (HP (S i) sm Hn) as (x & Ex & X1 & X2). exists x. split; [exact Ex|]. exact (conj X1 X2).
- intros i sm' Hi Hn. apply (HA (S i) sm'); [cbn; lia | exact Hn].
Qed.

(* A summand that is 0 on the control entries has the same sum along an errbuf step. *)
Lemma seg_sum_eq : forall (g : secmap -> Z), (forall sm, sm_size sm < 0 -> g sm = 0) ->
forall l l', secs_errb_grow l l' ->
fold_right (fun sm acc => g sm + acc) 0 l = fold_right (fun sm acc => g sm + acc) 0 l'.
Proof.
intros g H0 l. induction l as [|a t IH]; intros l' G.
- destruct G as [_ [_ HA]]. cbn [fold_right]. symmetry. apply cfa_sum_zero. intros sm Hin.
  destruct (In_nth_error l' sm Hin) as [i Hi]. destruct (HA i sm ltac:(cbn; lia) Hi) as [S1 _]. exact (H0 sm S1).
- destruct (seg_cons a t l' G) as (a' & t' & -> & H1 & H2 & G'). cbn [fold_right]. rewrite (IH t' G').
  destruct (Z_le_gt_dec 0 (sm_size a)) as [Hz|Hz].
  + rewrite (H1 Hz). reflexivity.
  + destruct (H2 ltac:(lia)) as [Ha' _]. rewrite (H0 a ltac:(lia)), (H0 a' Ha'). reflexivity.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 2. nsec_cf (YG0ncf.v), the user-entry count, at the three st_secs steps.        *)
Lemma nsec_cf_alloc : forall S S' L z, 0 <= z -> st_secs S' = st_secs S ++ [mkSec L z true] ->
nsec_cf S' = nsec_cf S + 1.
Proof.
intros S S' L z Hz E. unfold nsec_cf. rewrite E.
rewrite (cfa_fold_app1 (fun sm acc => (if sec_user_cf sm then 1 else 0) + acc) (fun sm => if sec_user_cf sm then 1 else 0))
  by (intros; reflexivity).
cbv beta. rewrite (user_true (mkSec L z true) Hz). reflexivity.
Qed.

Lemma nsec_cf_kill : forall X X2 r sm, nth_error (st_secs X) r = Some sm ->
st_secs X2 = lupd (st_secs X) r (mkSec (sm_len sm) (sm_size sm) false) -> nsec_cf X2 = nsec_cf X.
Proof.
intros X X2 r sm Hn E. unfold nsec_cf. rewrite E.
rewrite (cfa_fold_lupd (fun sm acc => (if sec_user_cf sm then 1 else 0) + acc) (fun sm => if sec_user_cf sm then 1 else 0)
  ltac:(intros; reflexivity) (st_secs X) r _ sm Hn).
cbv beta. replace (sec_user_cf (mkSec (sm_len sm) (sm_size sm) false)) with (sec_user_cf sm) by reflexivity. lia.
Qed.

Lemma nsec_cf_errb : forall S S', secs_errb_grow (st_secs S) (st_secs S') -> nsec_cf S' = nsec_cf S.
Proof.
intros S S' G. unfold nsec_cf. symmetry.
apply (seg_sum_eq (fun sm => if sec_user_cf sm then 1 else 0)); [|exact G].
intros sm H. cbv beta. rewrite (user_false sm H). reflexivity.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 3. The recycled secondaries: the user entries that are dead.                     *)
Definition dead_secs_cf (S : astate) : Z :=
fold_right (fun sm acc => (if sm_live sm || negb (sec_user_cf sm) then 0 else 1) + acc) 0 (st_secs S).

(* Every recycled secondary is a user entry. *)
Lemma dead_le_nsec_cf : forall S, dead_secs_cf S <= nsec_cf S.
Proof.
intros S. unfold dead_secs_cf, nsec_cf. induction (st_secs S) as [|sm t IH]; cbn [fold_right]; [lia|].
assert (D : (if sm_live sm || negb (sec_user_cf sm) then 0 else 1) <= (if sec_user_cf sm then 1 else 0))
  by (destruct (sec_user_cf sm), (sm_live sm); cbn [orb negb]; lia).
lia.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 4. kf <= nsec_cf (reply's admission nsec_cf S <= cf_kmax bounds kf = D + qsec_cf S): every quarantined          *)
(*    secondary chunk names its own LIVE user entry (chunk_ok_cf; distinct chunks name distinct entries:          *)
(*    ck_beg is duplicate-free, wfc_chunks_nodup, and every PSec offset is kPage), and the recycled secondaries D *)
(*    are the DEAD user entries. Sums over index lists.                                                          *)
Definition cfn_sum (f : nat -> Z) (l : list nat) : Z := fold_right (fun x acc => f x + acc) 0 l.

Lemma cfn_sum_cons : forall f x l, cfn_sum f (x :: l) = f x + cfn_sum f l.
Proof. reflexivity. Qed.

Lemma cfn_sum_app : forall f l1 l2, cfn_sum f (l1 ++ l2) = cfn_sum f l1 + cfn_sum f l2.
Proof.
intros f l1 l2. induction l1 as [|x t IH]; cbn [app]; [change (cfn_sum f []) with 0; lia|].
rewrite !cfn_sum_cons, IH. lia.
Qed.

Lemma cfn_sum_map : forall f (h : nat -> nat) l, cfn_sum f (map h l) = cfn_sum (fun x => f (h x)) l.
Proof. intros f h l. induction l as [|x t IH]; [reflexivity|]. cbn [map]. rewrite !cfn_sum_cons, IH. reflexivity. Qed.

Lemma cfn_sum_nonneg : forall f l, (forall x, In x l -> 0 <= f x) -> 0 <= cfn_sum f l.
Proof.
intros f l. induction l as [|b t IH]; intros H; [change (cfn_sum f []) with 0; lia|].
rewrite cfn_sum_cons. pose proof (H b (or_introl eq_refl)). specialize (IH (fun x Hx => H x (or_intror Hx))). lia.
Qed.

Lemma cfn_sum_remove : forall f a l, (forall x, In x l -> 0 <= f x) ->
cfn_sum f (remove Nat.eq_dec a l) <= cfn_sum f l.
Proof.
intros f a l. induction l as [|b t IH]; intros H; [cbn [remove]; lia|].
cbn [remove]. specialize (IH (fun x Hx => H x (or_intror Hx))). pose proof (H b (or_introl eq_refl)) as Hb.
destruct (Nat.eq_dec a b) as [_|_]; rewrite ?cfn_sum_cons; lia.
Qed.

Lemma cfn_sum_pick : forall f a l, In a l -> (forall x, In x l -> 0 <= f x) ->
f a + cfn_sum f (remove Nat.eq_dec a l) <= cfn_sum f l.
Proof.
intros f a l. induction l as [|b t IH]; intros Ha H; [destruct Ha|].
cbn [remove]. pose proof (H b (or_introl eq_refl)) as Hb.
destruct (Nat.eq_dec a b) as [<-|Hne].
- pose proof (cfn_sum_remove f a t (fun x Hx => H x (or_intror Hx))). rewrite cfn_sum_cons. lia.
- destruct Ha as [Ha|Ha]; [congruence|].
  specialize (IH Ha (fun x Hx => H x (or_intror Hx))). rewrite !cfn_sum_cons. lia.
Qed.

(* A sum over a duplicate-free index list is at most the sum over any list that contains it, when the summand is
   nonnegative there. *)
Lemma cfn_sum_incl : forall f l1 l2, NoDup l1 -> incl l1 l2 -> (forall x, In x l2 -> 0 <= f x) ->
cfn_sum f l1 <= cfn_sum f l2.
Proof.
intros f l1. induction l1 as [|a t IH]; intros l2 ND HI H.
- change (cfn_sum f []) with 0. exact (cfn_sum_nonneg f l2 H).
- inversion ND as [|a' t' Hna Hnd]; subst.
  assert (Ha : In a l2) by (apply HI; left; reflexivity).
  pose proof (cfn_sum_pick f a l2 Ha H) as P.
  assert (HI' : incl t (remove Nat.eq_dec a l2)).
  { intros x Hx. apply in_in_remove; [intros ->; exact (Hna Hx) | apply HI; right; exact Hx]. }
  assert (H' : forall x, In x (remove Nat.eq_dec a l2) -> 0 <= f x).
  { intros x Hx. apply in_remove in Hx as [Hx _]. exact (H x Hx). }
  specialize (IH _ Hnd HI' H'). rewrite cfn_sum_cons. lia.
Qed.

(* An st_secs summand by index (0 past the end), and a fold over st_secs as the index sum over all of it. *)
Definition cfn_at (g : secmap -> Z) (l : list secmap) (r : nat) : Z :=
match nth_error l r with Some sm => g sm | None => 0 end.

Lemma cfn_seq {F : secmap -> Z -> Z} (g : secmap -> Z) :
(forall x a, F x a = g x + a) -> forall l, fold_right F 0 l = cfn_sum (cfn_at g l) (seq 0 (length l)).
Proof.
intros HF l. induction l as [|a t IH]; [reflexivity|].
cbn [fold_right length seq]. rewrite HF, cfn_sum_cons, <- seq_shift, cfn_sum_map, IH. reflexivity.
Qed.

(* The st_secs indices of the PSec chunks. *)
Definition cfn_idx1 (k : chunk) : list nat := match ck_beg k with PSec r _ => [r] | _ => [] end.
Definition cfn_idx (l : list chunk) : list nat := flat_map cfn_idx1 l.

Lemma cfn_idx_cons : forall k t, cfn_idx (k :: t) = cfn_idx1 k ++ cfn_idx t.
Proof. reflexivity. Qed.

Lemma cfa_needed_size_nonneg : forall n, 0 <= n -> 0 <= needed_size n.
Proof.
intros n Hn. unfold needed_size. pose proof (needed_primary_bounds n Hn) as (_ & [N _] & _).
pose proof (rz_size_bounds n) as [[R _] _]. destruct (from_primary n); lia.
Qed.

Section U. Context {cp : CfParams}.

Lemma cfn_idx_bound : forall s l r, Forall (chunk_ok_cf s) l -> In r (cfn_idx l) -> (r < length (st_secs s))%nat.
Proof.
intros s l r H Hr. unfold cfn_idx in Hr. apply in_flat_map in Hr as (k & Hk & Hr). unfold cfn_idx1 in Hr.
pose proof (proj1 (Forall_forall _ _) H k Hk) as C. unfold chunk_ok_cf in C. destruct C as [_ C].
destruct (ck_beg k) as [|off|r2 o|cid pos] eqn:Eb; cbn in Hr; try contradiction.
destruct Hr as [<-|[]]. destruct C as (_ & _ & sm & Hsm & _).
apply nth_error_Some. rewrite Hsm. discriminate.
Qed.

(* Distinct chunks have distinct entries: ck_beg is duplicate-free and every PSec offset is kPage. *)
Lemma cfn_idx_nodup : forall s l, Forall (chunk_ok_cf s) l -> NoDup (map ck_beg l) -> NoDup (cfn_idx l).
Proof.
intros s l HF. induction HF as [|k t Hk Ht IH]; intros HN; [constructor|].
cbn [map] in HN. apply NoDup_cons_iff in HN as [Hnb Hnd].
specialize (IH Hnd). rewrite cfn_idx_cons.
unfold chunk_ok_cf in Hk. destruct Hk as [_ Hk]. unfold cfn_idx1.
destruct (ck_beg k) as [|off|r o|cid pos] eqn:Eb; cbn [app]; try exact IH.
destruct Hk as (_ & Ho & _). subst o.
constructor; [|exact IH].
intros Hin. unfold cfn_idx in Hin. apply in_flat_map in Hin as (k2 & Hk2 & Hr). unfold cfn_idx1 in Hr.
pose proof (proj1 (Forall_forall _ _) Ht k2 Hk2) as C2. unfold chunk_ok_cf in C2. destruct C2 as [_ C2].
destruct (ck_beg k2) as [|off2|r2 o2|cid2 pos2] eqn:Eb2; cbn in Hr; try contradiction.
destruct Hr as [Er|[]]. subst r2. destruct C2 as (_ & Ho2 & _). subst o2.
apply Hnb. try rewrite Eb. rewrite <- Eb2. apply in_map. exact Hk2.
Qed.

(* The live user entries: nsec_cf splits into the dead and the live user entries. *)
Definition live_user_g (sm : secmap) : Z := if sec_user_cf sm then (if sm_live sm then 1 else 0) else 0.

Lemma nsec_cf_split : forall S,
nsec_cf S = dead_secs_cf S + fold_right (fun sm acc => live_user_g sm + acc) 0 (st_secs S).
Proof.
intros S. unfold nsec_cf, dead_secs_cf. induction (st_secs S) as [|a t IH]; cbn [fold_right]; [reflexivity|].
assert (P : (if sec_user_cf a then 1 else 0) = (if sm_live a || negb (sec_user_cf a) then 0 else 1) + live_user_g a)
  by (unfold live_user_g; destruct (sec_user_cf a), (sm_live a); reflexivity).
lia.
Qed.

Lemma cfn_at_live_nonneg : forall l r, 0 <= cfn_at live_user_g l r.
Proof.
intros l r. unfold cfn_at. destruct (nth_error l r) as [sm|]; cbv iota; [|lia].
unfold live_user_g. destruct (sec_user_cf sm), (sm_live sm); cbv iota; lia.
Qed.

(* The live user entries the PSec chunks name are at most all of them. *)
Lemma cfn_live_le : forall U S, Wf_cf U S ->
cfn_sum (cfn_at live_user_g (st_secs S)) (cfn_idx (st_chunks S)) <= fold_right (fun sm acc => live_user_g sm + acc) 0 (st_secs S).
Proof.
intros U S W. unfold Wf_cf in W.
pose proof (wfc_chunks _ _ _ _ _ W) as CK. pose proof (wfc_chunks_nodup _ _ _ _ _ W) as ND.
apply Z.le_trans with (cfn_sum (cfn_at live_user_g (st_secs S)) (seq 0 (length (st_secs S)))).
- apply cfn_sum_incl.
  + exact (cfn_idx_nodup S (st_chunks S) CK ND).
  + intros r Hr. pose proof (cfn_idx_bound S (st_chunks S) r CK Hr). apply in_seq. lia.
  + intros r _. apply cfn_at_live_nonneg.
- apply Z.eq_le_incl. symmetry. apply (cfn_seq live_user_g). intros; reflexivity.
Qed.

Lemma cfn_qsec_le : forall s l, Forall (chunk_ok_cf s) l ->
Z.of_nat (length (List.filter is_qsec l)) <= cfn_sum (cfn_at live_user_g (st_secs s)) (cfn_idx l).
Proof.
intros s l H. induction H as [|k t Hk Ht IH]; [cbn; lia|].
rewrite cfn_idx_cons, cfn_sum_app. cbn [List.filter].
assert (NN : forall l0, 0 <= cfn_sum (cfn_at live_user_g (st_secs s)) l0).
{ intros l0. apply cfn_sum_nonneg. intros x _. apply cfn_at_live_nonneg. }
destruct (is_qsec k) eqn:Q.
- unfold is_qsec in Q. unfold chunk_ok_cf in Hk. destruct Hk as [Hreq Hk].
  destruct (ck_beg k) as [|off|r o|cid pos] eqn:Eb; cbv iota in Q; try discriminate Q.
  destruct Hk as (_ & _ & sm & Hsm & Hlive & Hsz & _).
  assert (I1 : cfn_idx1 k = [r]) by (unfold cfn_idx1; rewrite Eb; reflexivity).
  assert (F1 : cfn_at live_user_g (st_secs s) r = 1).
  { unfold cfn_at. rewrite Hsm. cbv iota. unfold live_user_g.
    rewrite (user_true sm ltac:(rewrite Hsz; apply cfa_needed_size_nonneg; lia)), Hlive. reflexivity. }
  rewrite I1, cfn_sum_cons, F1. cbn [length]. pose proof (NN []). lia.
- cbv iota. pose proof (NN (cfn_idx1 k)). lia.
Qed.

Lemma kf_le_nsec_cf : forall U S, Wf_cf U S -> dead_secs_cf S + qsec_cf S <= nsec_cf S.
Proof.
intros U S W. pose proof (cfn_live_le U S W) as LL. pose proof (nsec_cf_split S) as SP.
unfold Wf_cf in W. pose proof (wfc_chunks _ _ _ _ _ W) as CK.
pose proof (cfn_qsec_le S (st_chunks S) CK) as Q. unfold qsec_cf. lia.
Qed.

End U.
