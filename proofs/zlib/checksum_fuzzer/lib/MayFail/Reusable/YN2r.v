(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN2r.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0w.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0u.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO10.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO12.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0t.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN25.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN26.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2q.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2o.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2t.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Local Open Scope mm_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition am_act (a : ameta) : ameta :=
am_set_avail (Z.land (am_freed a) (ones (am_aidx a))) (am_set_freed (Z.ldiff (am_freed a) (ones (am_aidx a))) a).
Lemma am_set_links_twice pr nx pr' nx' a : am_set_links pr nx (am_set_links pr' nx' a) = am_set_links pr nx a.
Proof. destruct a; reflexivity. Qed.
Lemma am_avail_set_links pr nx a : am_avail (am_set_links pr nx a) = am_avail a.
Proof. destruct a; reflexivity. Qed.
Lemma active_hd_set_active_any s l v sc :
(Z.to_nat sc < length l)%nat -> active_hd (set_active (lupd l (Z.to_nat sc) v) s) sc = v.
Proof.
intros H. unfold active_hd. cbn [st_active set_active]. rewrite nth_lupd, Nat.eqb_refl.
replace (Nat.ltb (Z.to_nat sc) (length l)) with true by (symmetry; apply Nat.ltb_lt; exact H). reflexivity.
Qed.
Section e.
Variables (A : astate) (g : sptr) (am : ameta).
Hypothesis Hg : MT A g = Some (MUsed am).
Hypothesis HLA : length (st_active A) = 48%nat.
Lemma nt_deq_D0 : am_next am = None -> nt_deq g am A = IRet (tt, A).
Proof. intros Hn. unfold nt_deq. rewrite Hn. reflexivity. Qed.
Lemma Ng0 : MT A g <> None. Proof. rewrite Hg. discriminate. Qed.
Definition A_D1 : astate := set_active (lupd (st_active A) (Z.to_nat (am_sc am)) None) (upd_meta g (MUsed (strip am)) A).
Lemma nt_deq_D1 :
am_next am = Some g -> am_sc am < 48 -> 0 <= am_sc am -> active_hd A (am_sc am) = Some g ->
nt_deq g am A = IRet (tt, A_D1).
Proof.
intros Hn Hsc Hsc0 Hhd. unfold nt_deq. rewrite Hn.
erewrite (bind_eval _ _ A) by (apply massert_true; apply Z.ltb_lt; exact Hsc).
erewrite (bind_eval _ _ A) by apply get_head_active_eval. rewrite Hhd.
unfold dequeue. erewrite (bind_eval (bind _ _) _ A).
2:{ erewrite (bind_eval _ _ A) by (apply (get_links_eval A g (MUsed am)); exact Hg).
cbn [links_of snd]. rewrite Hn. cbn [osptr_eqb]. rewrite sptr_eqb_refl.
erewrite (bind_eval _ _ A) by apply set_head_active_eval.
apply set_links_eval. rewrite MT_set_active. exact Hg. }
erewrite (bind_eval _ _ _) by apply get_head_active_eval.
cbn [osptr_eqb]. rewrite sptr_eqb_refl. rewrite active_hd_upd_meta, active_hd_set_active_same by (rewrite HLA; lia).
unfold ret, A_D1. rewrite upd_meta_set_active. reflexivity.
Qed.
Variables (p n : sptr) (ap an : ameta).
Hypothesis Hng : n <> g.
Hypothesis Hpg : p <> g.
Hypothesis Mp : MT A p = Some (MUsed ap).
Hypothesis Mn : MT A n = Some (MUsed an).
Definition ap2 : ameta := am_set_links (am_prev ap) (Some n) ap.
Definition an2 : ameta := am_set_links (Some p) (am_next an) an.
Definition an2' : ameta := am_set_links (Some n) (Some n) an.
Definition A_unl : astate := upd_meta g (MUsed (strip am)) (upd_meta n (MUsed an2) (upd_meta p (MUsed ap2) A)).
Definition A_unl' : astate := upd_meta g (MUsed (strip am)) (upd_meta n (MUsed an2') A).
Definition A_D2a : astate := A_unl.
Definition A_D2a' : astate := A_unl'.
Definition act_n : list (option sptr) := lupd (st_active A) (Z.to_nat (am_sc am)) (Some n).
Definition A_D2b : astate := set_active act_n (upd_meta g (MUsed (strip am)) (upd_meta n (MUsed (am_act an2)) (upd_meta p (MUsed ap2) A))).
Definition A_D2b' : astate := set_active act_n (upd_meta g (MUsed (strip am)) (upd_meta n (MUsed (am_act an2')) A)).
Lemma get_head_cond_eval s sc m v :
(bind (get_head (HActive sc)) (fun hd => if osptr_eqb hd (Some m) then set_head (HActive sc) v else ret tt)) s =
IRet (tt, if osptr_eqb (active_hd s sc) (Some m) then set_active (lupd (st_active s) (Z.to_nat sc) v) s else s).
Proof. unfold bind, get_head, get, active_hd. cbn. destruct (osptr_eqb (nth (Z.to_nat sc) (st_active s) None) (Some m)); reflexivity. Qed.
Lemma dequeue_D2_eval :
am_next am = Some n -> am_prev am = Some p -> p <> n ->
dequeue (HActive (am_sc am)) g A =
IRet (tt, if osptr_eqb (active_hd A (am_sc am)) (Some g)
then upd_meta g (MUsed (strip am)) (set_active act_n (upd_meta n (MUsed an2) (upd_meta p (MUsed ap2) A)))
else A_unl).
Proof.
intros Hn Hp Hpn. unfold dequeue.
erewrite (bind_eval (get_links g) _ A) by (apply (get_links_eval A g (MUsed am)); exact Hg).
cbn [links_of fst snd]. rewrite Hn, Hp. cbn [osptr_eqb]. replace (sptr_eqb n g) with false by (symmetry; apply sptr_eqb_neq; exact Hng).
erewrite (bind_eval (bind _ _) _ A).
2:{ unfold set_next. erewrite (bind_eval (bind _ _) _ A).
2:{ erewrite (bind_eval _ _ A) by (apply (get_links_eval A p (MUsed ap)); exact Mp). cbn [links_of fst]. apply (set_links_eval A p (MUsed ap)). exact Mp. }
unfold set_prev. erewrite (bind_eval (bind _ _) _ _).
2:{ erewrite (bind_eval _ _ _) by (apply (get_links_eval _ n (MUsed an)); rewrite MT_upd_other by (intros E; exact (Hpn (eq_sym E))); exact Mn).
cbn [links_of snd with_links]. apply (set_links_eval _ n (MUsed an)). rewrite MT_upd_other by (intros E; exact (Hpn (eq_sym E))). exact Mn. }
rewrite get_head_cond_eval, !active_hd_upd_meta. reflexivity. }
cbn [with_links].
assert (Hgn : g <> n) by (intros E; exact (Hng (eq_sym E))). assert (Hgp : g <> p) by (intros E; exact (Hpg (eq_sym E))).
destruct (osptr_eqb (active_hd A (am_sc am)) (Some g)).
- rewrite (set_links_eval _ g (MUsed am)); [| rewrite MT_set_active, (MT_upd_other n) by exact Hgn; rewrite (MT_upd_other p) by exact Hgp; exact Hg].
unfold act_n, ap2, an2. cbn [with_links st_active upd_meta set_metas]. reflexivity.
- rewrite (set_links_eval _ g (MUsed am)); [| rewrite (MT_upd_other n) by exact Hgn; rewrite (MT_upd_other p) by exact Hgp; exact Hg].
unfold A_unl, ap2, an2. reflexivity.
Qed.
Lemma dequeue_D2'_eval :
am_next am = Some n -> am_prev am = Some n ->
dequeue (HActive (am_sc am)) g A =
IRet (tt, if osptr_eqb (active_hd A (am_sc am)) (Some g)
then upd_meta g (MUsed (strip am)) (set_active act_n (upd_meta n (MUsed an2') A))
else A_unl').
Proof.
intros Hn Hp. unfold dequeue.
erewrite (bind_eval (get_links g) _ A) by (apply (get_links_eval A g (MUsed am)); exact Hg).
cbn [links_of fst snd]. rewrite Hn, Hp. cbn [osptr_eqb]. replace (sptr_eqb n g) with false by (symmetry; apply sptr_eqb_neq; exact Hng).
erewrite (bind_eval (bind _ _) _ A).
2:{ unfold set_next. erewrite (bind_eval (bind _ _) _ A).
2:{ erewrite (bind_eval _ _ A) by (apply (get_links_eval A n (MUsed an)); exact Mn). cbn [links_of fst]. apply (set_links_eval A n (MUsed an)). exact Mn. }
unfold set_prev. erewrite (bind_eval (bind _ _) _ _).
2:{ erewrite (bind_eval _ _ _) by (apply get_links_eval; apply MT_upd_same).
cbn [links_of snd with_links am_next am_set_links]. apply set_links_eval. apply MT_upd_same. }
rewrite get_head_cond_eval, !active_hd_upd_meta. reflexivity. }
cbn [with_links]. rewrite upd_meta_twice.
assert (Hgn : g <> n) by (intros E; exact (Hng (eq_sym E))).
rewrite am_set_links_twice. fold an2'.
destruct (osptr_eqb (active_hd A (am_sc am)) (Some g)).
- rewrite (set_links_eval _ g (MUsed am)); [| rewrite MT_set_active, (MT_upd_other n) by exact Hgn; exact Hg].
unfold act_n. cbn [with_links st_active upd_meta set_metas]. reflexivity.
- rewrite (set_links_eval _ g (MUsed am)); [| rewrite (MT_upd_other n) by exact Hgn; exact Hg]. reflexivity.
Qed.
Lemma NN' q z r (s0 : astate) : MT s0 r <> None -> MT (upd_meta q z s0) r <> None.
Proof. intros Hp0. rewrite MT_upd. destruct (sptr_eqb r q); [discriminate | exact Hp0]. Qed.
Lemma Nn0 : MT A n <> None. Proof. rewrite Mn. discriminate. Qed.
Lemma Np0 : MT A p <> None. Proof. rewrite Mp. discriminate. Qed.
Lemma nt_deq_D2a :
am_next am = Some n -> am_prev am = Some p -> p <> n -> am_sc am < 48 -> active_hd A (am_sc am) <> Some g ->
nt_deq g am A = IRet (tt, A_D2a).
Proof.
intros Hn Hp Hpn Hsc Hhd. unfold nt_deq. rewrite Hn.
erewrite (bind_eval _ _ A) by (apply massert_true; apply Z.ltb_lt; exact Hsc).
erewrite (bind_eval _ _ A) by apply get_head_active_eval.
erewrite (bind_eval _ _ A) by (apply dequeue_D2_eval; assumption).
assert (E : osptr_eqb (active_hd A (am_sc am)) (Some g) = false).
{ destruct (active_hd A (am_sc am)) as [q|]; [cbn; apply sptr_eqb_neq; congruence | reflexivity]. }
rewrite E. erewrite (bind_eval _ _ _) by apply get_head_active_eval. reflexivity.
Qed.
Lemma nt_deq_D2a' :
am_next am = Some n -> am_prev am = Some n -> am_sc am < 48 -> active_hd A (am_sc am) <> Some g ->
nt_deq g am A = IRet (tt, A_D2a').
Proof.
intros Hn Hp Hsc Hhd. unfold nt_deq. rewrite Hn.
erewrite (bind_eval _ _ A) by (apply massert_true; apply Z.ltb_lt; exact Hsc).
erewrite (bind_eval _ _ A) by apply get_head_active_eval.
erewrite (bind_eval _ _ A) by (apply dequeue_D2'_eval; assumption).
assert (E : osptr_eqb (active_hd A (am_sc am)) (Some g) = false).
{ destruct (active_hd A (am_sc am)) as [q|]; [cbn; apply sptr_eqb_neq; congruence | reflexivity]. }
rewrite E. erewrite (bind_eval _ _ _) by apply get_head_active_eval. reflexivity.
Qed.
Lemma nt_deq_D2b :
am_next am = Some n -> am_prev am = Some p -> p <> n -> am_sc am < 48 -> 0 <= am_sc am -> active_hd A (am_sc am) = Some g -> am_avail an = 0 ->
nt_deq g am A = IRet (tt, A_D2b).
Proof.
intros Hn Hp Hpn Hsc Hsc0 Hhd Hav. unfold nt_deq. rewrite Hn.
assert (Hgn : g <> n) by (intros E; exact (Hng (eq_sym E))). assert (Hnp : n <> p) by (intros E; exact (Hpn (eq_sym E))).
erewrite (bind_eval _ _ A) by (apply massert_true; apply Z.ltb_lt; exact Hsc).
erewrite (bind_eval _ _ A) by apply get_head_active_eval.
erewrite (bind_eval _ _ A) by (apply dequeue_D2_eval; assumption).
rewrite Hhd. cbn [osptr_eqb]. rewrite sptr_eqb_refl.
erewrite (bind_eval _ _ _) by apply get_head_active_eval.
rewrite active_hd_upd_meta. unfold act_n. rewrite active_hd_set_active_any by (rewrite HLA; lia).
unfold activate_group. erewrite (bind_eval (bind _ _) _ _).
2:{ erewrite (bind_eval (getm n) _ _).
2:{ apply getm_eval. rewrite (MT_upd_other g) by exact Hng. rewrite MT_set_active. apply MT_upd_same. }
erewrite (bind_eval _ _ _) by (apply massert_true; apply Z.eqb_eq; unfold an2; rewrite am_avail_set_links; exact Hav).
erewrite (bind_eval _ _ _) by apply setm_eval. apply ret_eval. }
unfold ret, A_D2b, am_act. f_equal. f_equal.
rewrite (upd_meta_comm n _ g); [| exact Hng | rewrite MT_set_active, MT_upd_same; discriminate].
rewrite !upd_meta_set_active, upd_meta_twice. reflexivity.
Qed.
Lemma nt_deq_D2b' :
am_next am = Some n -> am_prev am = Some n -> am_sc am < 48 -> 0 <= am_sc am -> active_hd A (am_sc am) = Some g -> am_avail an = 0 ->
nt_deq g am A = IRet (tt, A_D2b').
Proof.
intros Hn Hp Hsc Hsc0 Hhd Hav. unfold nt_deq. rewrite Hn.
assert (Hgn : g <> n) by (intros E; exact (Hng (eq_sym E))).
erewrite (bind_eval _ _ A) by (apply massert_true; apply Z.ltb_lt; exact Hsc).
erewrite (bind_eval _ _ A) by apply get_head_active_eval.
erewrite (bind_eval _ _ A) by (apply dequeue_D2'_eval; assumption).
rewrite Hhd. cbn [osptr_eqb]. rewrite sptr_eqb_refl.
erewrite (bind_eval _ _ _) by apply get_head_active_eval.
rewrite active_hd_upd_meta. unfold act_n. rewrite active_hd_set_active_any by (rewrite HLA; lia).
unfold activate_group. erewrite (bind_eval (bind _ _) _ _).
2:{ erewrite (bind_eval (getm n) _ _).
2:{ apply getm_eval. rewrite (MT_upd_other g) by exact Hng. rewrite MT_set_active. apply MT_upd_same. }
erewrite (bind_eval _ _ _) by (apply massert_true; apply Z.eqb_eq; unfold an2'; rewrite am_avail_set_links; exact Hav).
erewrite (bind_eval _ _ _) by apply setm_eval. apply ret_eval. }
unfold ret, A_D2b', am_act. f_equal. f_equal.
rewrite (upd_meta_comm n _ g); [| exact Hng | rewrite MT_set_active, MT_upd_same; discriminate].
rewrite !upd_meta_set_active, upd_meta_twice. reflexivity.
Qed.
End e.
Definition A_usg (A : astate) (sc : Z) (am1 : ameta) (s : astate) : astate :=
if sc <? 48 then set_usage (zset sc (usage_of A sc - (am_last am1 + 1)) (st_usage s)) s else s.
Definition A_seq (s : astate) : astate :=
if st_seq s =? 255 then set_seq 1 (set_unmap_seq (repeat 0 32) s) else set_seq (st_seq s + 1) s.
Definition A_rec (sc : Z) (s : astate) : astate :=
match bounce_idx sc with
| Some k => set_unmap_seq (zset k (st_seq s) (st_unmap_seq s)) s
| None => s
end.
Lemma step_seq_eval s : step_seq s = IRet (tt, A_seq s).
Proof. reflexivity. Qed.
Lemma record_seq_eval sc s : record_seq sc s = IRet (tt, A_rec sc s).
Proof. unfold record_seq, A_rec. destruct (bounce_idx sc); reflexivity. Qed.
Section j.
Variables (f : nat) (A : astate) (g : sptr) (am : ameta) (s1 : astate) (am1 : ameta).
Hypothesis M1 : MT s1 g = Some (MUsed am1).
Lemma usage_eval :
(if am_sc am <? 48 then set_usage_of (am_sc am) (usage_of A (am_sc am) - (am_last am1 + 1)) else ret tt) s1 = IRet (tt, A_usg A (am_sc am) am1 s1).
Proof. unfold A_usg. destruct (am_sc am <? 48); reflexivity. Qed.
Lemma nt_free_group_mapped :
am_maplen am1 <> 0 ->
nt_free_group f A g am s1 =
(free_meta g ;; ret (Some (prid (am_mem am1), am_maplen am1 * 4096))) (A_rec (am_sc am) (A_seq (A_usg A (am_sc am) am1 s1))).
Proof.
intros Hml. unfold nt_free_group.
erewrite (bind_eval (getm g) _ s1) by (apply getm_eval; exact M1).
erewrite (bind_eval _ _ s1) by apply usage_eval.
replace (negb (am_maplen am1 =? 0)) with true by (symmetry; apply negb_true_iff; apply Z.eqb_neq; exact Hml).
erewrite (bind_eval (bind _ _) _ _).
2:{ erewrite (bind_eval _ _ _) by apply step_seq_eval. erewrite (bind_eval _ _ _) by apply record_seq_eval. apply ret_eval. }
reflexivity.
Qed.
Variables (g' : sptr) (i' : Z) (am' : ameta).
Definition A_fgt : astate :=
upd_meta g' (MUsed (upd_slot am' i' (mkSlot (ss_hdr (nth_slot am' i')) None))) (A_usg A (am_sc am) am1 s1).
Lemma nt_free_group_nested :
am_maplen am1 = 0 ->
find_frame_in (st_metas (A_usg A (am_sc am) am1 s1)) (am_mem am1) = Some (g', i') ->
MT (A_usg A (am_sc am) am1 s1) g' = Some (MUsed am') ->
slot_is_group (nth_slot am' i') = true ->
nt_free_group f A g am s1 =
ibind (nontrivial_free f g' i' A_fgt) (fun r : option (nat * Z) * astate => let '(mi, s4) := r in (free_meta g ;; ret mi) s4).
Proof.
intros Hml Hff M' Hsg. unfold nt_free_group.
erewrite (bind_eval (getm g) _ s1) by (apply getm_eval; exact M1).
erewrite (bind_eval _ _ s1) by apply usage_eval.
rewrite Hml. cbn [Z.eqb negb].
unfold bind at 1. f_equal.
- unfold find_frame. erewrite (bind_eval (bind get _) _ _).
2:{ erewrite (bind_eval get _ _) by apply get_eval. rewrite Hff. apply ret_eval. }
cbn [fst snd]. erewrite (bind_eval (getm g') _ _) by (apply getm_eval; exact M').
erewrite (bind_eval _ _ _) by (unfold mcheck; rewrite Hsg; apply ret_eval).
unfold forget_frame. erewrite (bind_eval (bind _ _) _ _).
2:{ erewrite (bind_eval (getm g') _ _) by (apply getm_eval; exact M'). apply setm_eval. }
reflexivity.
Qed.
End j.
Section o.
Variables (g : sptr) (s : astate).
Lemma setslot_eval p x s0 : setslot p x s0 = IRet (tt, upd_meta p x s0).
Proof. reflexivity. Qed.
Definition A_F0 : astate := set_free_meta_head (Some g) (upd_meta g (MFree (Some g) (Some g)) s).
Lemma free_meta_F0 : st_free_meta_head s = None -> free_meta g s = IRet (tt, A_F0).
Proof.
intros Hh. unfold free_meta. erewrite (bind_eval _ _ s) by apply setslot_eval.
unfold queue. erewrite (bind_eval (get_links g) _ _) by (apply get_links_eval; apply MT_upd_same). cbn [links_of fst snd osptr_eqb andb].
erewrite (bind_eval _ _ _) by reflexivity.
erewrite (bind_eval _ _ _) by reflexivity. cbn [st_free_meta_head upd_meta set_metas]. rewrite Hh.
erewrite (bind_eval _ _ _) by (apply set_links_eval; apply MT_upd_same). cbn [with_links].
unfold set_head, modify, A_F0. rewrite upd_meta_twice. reflexivity.
Qed.
Variables (h hp : sptr) (hnx hpp : option sptr).
Hypothesis Hhg : h <> g.
Hypothesis Mh : MT s h = Some (MFree (Some hp) hnx).
Definition A_F1a : astate := upd_meta h (MFree (Some g) (Some g)) (upd_meta g (MFree (Some h) (Some h)) s).
Definition A_F1b : astate := upd_meta h (MFree (Some g) hnx) (upd_meta hp (MFree hpp (Some g)) (upd_meta g (MFree (Some hp) (Some h)) s)).
Lemma free_meta_F1a : st_free_meta_head s = Some h -> hp = h -> free_meta g s = IRet (tt, A_F1a).
Proof.
intros Hh Ehp. assert (Mh' : MT s h = Some (MFree (Some h) hnx)) by (rewrite Mh, Ehp; reflexivity). clear Ehp.
assert (Hgh : g <> h) by (intros E; exact (Hhg (eq_sym E))).
unfold free_meta. erewrite (bind_eval _ _ s) by apply setslot_eval.
unfold queue. erewrite (bind_eval (get_links g) _ _) by (apply get_links_eval; apply MT_upd_same). cbn [links_of fst snd osptr_eqb andb].
erewrite (bind_eval _ _ _) by reflexivity.
erewrite (bind_eval _ _ _) by reflexivity. cbn [st_free_meta_head upd_meta set_metas]. rewrite Hh.
erewrite (bind_eval (get_links h) _ _) by (apply get_links_eval; rewrite MT_upd_other by exact Hhg; exact Mh'). cbn [links_of fst].
erewrite (bind_eval _ _ _) by (apply set_links_eval; apply MT_upd_same). cbn [with_links]. rewrite upd_meta_twice.
unfold set_next. erewrite (bind_eval (bind _ _) _ _).
2:{ erewrite (bind_eval _ _ _) by (apply get_links_eval; rewrite MT_upd_other by exact Hhg; exact Mh'). cbn [links_of fst].
apply set_links_eval. rewrite MT_upd_other by exact Hhg. exact Mh'. }
cbn [with_links]. unfold set_prev. erewrite (bind_eval (get_links h) _ _) by (apply get_links_eval; apply MT_upd_same). cbn [links_of snd].
rewrite (set_links_eval _ h (MFree (Some h) (Some g))) by apply MT_upd_same. cbn [with_links]. rewrite upd_meta_twice. reflexivity.
Qed.
Hypothesis Mhp : MT s hp = Some (MFree hpp (Some h)).
Lemma free_meta_F1b : st_free_meta_head s = Some h -> hp <> h -> hp <> g -> free_meta g s = IRet (tt, A_F1b).
Proof.
intros Hh Hph Hpg. assert (Hgh : g <> h) by (intros E; exact (Hhg (eq_sym E))). assert (Hhp' : h <> hp) by (intros E; exact (Hph (eq_sym E))).
unfold free_meta. erewrite (bind_eval _ _ s) by apply setslot_eval.
unfold queue. erewrite (bind_eval (get_links g) _ _) by (apply get_links_eval; apply MT_upd_same). cbn [links_of fst snd osptr_eqb andb].
erewrite (bind_eval _ _ _) by reflexivity.
erewrite (bind_eval _ _ _) by reflexivity. cbn [st_free_meta_head upd_meta set_metas]. rewrite Hh.
erewrite (bind_eval (get_links h) _ _) by (apply get_links_eval; rewrite MT_upd_other by exact Hhg; exact Mh). cbn [links_of fst].
erewrite (bind_eval _ _ _) by (apply set_links_eval; apply MT_upd_same). cbn [with_links]. rewrite upd_meta_twice.
unfold set_next. erewrite (bind_eval (bind _ _) _ _).
2:{ erewrite (bind_eval _ _ _) by (apply get_links_eval; rewrite MT_upd_other by exact Hpg; exact Mhp). cbn [links_of fst].
apply set_links_eval. rewrite MT_upd_other by exact Hpg. exact Mhp. }
cbn [with_links]. unfold set_prev. erewrite (bind_eval (get_links h) _ _).
2:{ apply get_links_eval. rewrite MT_upd_other by exact Hhp'. rewrite MT_upd_other by exact Hhg. exact Mh. }
cbn [links_of snd]. rewrite (set_links_eval _ h (MFree (Some hp) hnx)).
2:{ rewrite MT_upd_other by exact Hhp'. rewrite MT_upd_other by exact Hhg. exact Mh. }
cbn [with_links]. reflexivity.
Qed.
End o.
Section u.
Variable segs : list MemImageType.Segment.
Lemma SR_mreal {R} c (P : config -> Prop) (t : itree astate R) Q :
SR segs c P -> (forall c', P c' -> mreal segs c' t Q) -> mreal segs c t Q.
Proof.
intros HS HK. destruct t as [r | q snap k | f]; cbn [mreal] in *.
- eapply SR_bind; [exact HS | exact HK].
- eapply SR_bind; [exact HS | exact HK].
- exact I.
Qed.
Lemma knode_mono c q snap (K K' : Z -> config -> Prop) :
(forall z c', K z c' -> K' z c') -> knode segs c q snap K -> knode segs c q snap K'.
Proof.
intros HK. unfold knode. destruct q;
try (intros (I & nx & bit & i0 & Hn & Hc & Hcl); exists I, nx, bit, i0; split; [exact Hn|]; split; [intros i; apply HK, Hc | exact Hcl]).
intros (z & Hz & Hc). exists z. split; [exact Hz | apply HK, Hc].
Qed.
Theorem mreal_bind {R1 R2} (t : itree astate R1) (k : R1 -> itree astate R2) :
forall c (P : R1 -> config -> Prop) (Q : R2 -> config -> Prop),
mreal segs c t P -> (forall r c', P r c' -> mreal segs c' (k r) Q) -> mreal segs c (ibind t k) Q.
Proof.
induction t as [r | q snap kk IH | f]; intros c P Q HM HK; cbn [ibind].
- cbn [mreal] in HM. eapply SR_mreal; [exact HM | intros c' HP; exact (HK r c' HP)].
- cbn [mreal] in HM |- *. eapply SR_mono; [exact HM|]. intros c1 Hk. eapply knode_mono; [|exact Hk].
intros z c2 HM2. cbn beta in HM2. eapply IH; [exact HM2 | exact HK].
- exact I.
Qed.
End u.
Lemma ring_next_self lk hd ms x pr :
ring_ok lk hd ms -> In x ms -> lk x = Some (pr, Some x) -> ms = [x] /\ hd = Some x /\ pr = Some x.
Proof.
intros [[Hnd Hch] Hhd] Hin Hx. destruct ms as [|m0 rest]; [destruct Hin|].
destruct (chain_next _ _ _ _ _ _ _ Hch Hin Hx) as (l1 & l2 & Ems & Hnx & Hpr).
destruct l2 as [|y l2'].
- cbn in Hnx. injection Hnx as Exm. subst x.
destruct l1 as [|z l1'].
+ cbn in Ems. injection Ems as Er. subst rest. cbn in Hpr. subst. auto.
+ exfalso. cbn in Ems. injection Ems as Ez Er. subst z. rewrite Er in Hnd.
apply NoDup_cons_iff in Hnd as [Hni _]. apply Hni. apply in_app_iff. right. left. reflexivity.
- exfalso. cbn in Hnx. injection Hnx as Exy. subst y. rewrite Ems in Hnd.
apply NoDup_app_remove_l in Hnd. inversion Hnd as [|a l Hni Hnd']; subst. apply Hni. left. reflexivity.
Qed.
Lemma ring_neighbors lk hd0 ms x p n :
ring_ok lk hd0 ms -> In x ms -> lk x = Some (Some p, Some n) ->
(n = x /\ p = x /\ ms = [x] /\ hd0 = Some x) \/ (n <> x /\ p <> x /\ In p ms /\ In n ms).
Proof.
intros [Cy Hhd] Hin Hx. destruct (in_split x ms Hin) as (l1 & l2 & Ems).
assert (Cy' : cycle_ok lk ((x :: l2) ++ l1)) by (rewrite Ems in Cy; apply cycle_rotate_n; exact Cy).
cbn [app] in Cy'. destruct Cy' as [Hnd Hch]. cbn [chain] in Hch. destruct Hch as [Lx _]. rewrite Hx in Lx.
injection Lx as Ep En.
assert (SUB : forall y, In y (l2 ++ l1) -> In y ms).
{ intros y Hy. rewrite Ems. apply in_app_iff in Hy as [Hy|Hy]; apply in_app_iff; [right; right; exact Hy | left; exact Hy]. }
destruct (l2 ++ l1) as [|y r] eqn:Er.
- left. cbn in En, Ep. subst n p. destruct (app_eq_nil _ _ Er) as [-> ->]. rewrite Ems in *. cbn in *. subst. auto.
- right. cbn [hd] in En. subst y. rewrite last_cons in Ep.
apply NoDup_cons_iff in Hnd as [Hnx Hnd].
assert (Hpin : In p (n :: r)) by (rewrite Ep, <- (last_cons n r x); apply In_last; discriminate).
split; [intros ->; apply Hnx; left; reflexivity|]. split; [intros ->; exact (Hnx Hpin)|].
split; [apply SUB; exact Hpin | apply SUB; left; reflexivity].
Qed.
Inductive apathM := MQ1 | MQ2 | MQ3 | MQ4V1 | MQ4V2 | MQ5V1 | MQ5V2 | MQ6V1 | MQ6V2 | MQ7V1 | MQ7V2.
Inductive dvarM := MD0 | MD1 | MD2a | MD2b | MD2a' | MD2b'.
Definition validAM (q : apathM) (d : dvarM) : bool :=
match q, d with
| MQ1, MD0 => true
| (MQ2 | MQ3), _ => true
| (MQ4V1 | MQ4V2), (MD0 | MD2a | MD2b | MD2a' | MD2b') => true
| (MQ5V1 | MQ5V2 | MQ6V1 | MQ6V2 | MQ7V1 | MQ7V2), MD1 => true
| _, _ => false
end.
Section w.
Variables (X : list sptr) (U : Z -> Z) (A : astate) (g : sptr) (i : Z) (am : ameta).
Hypothesis HI : Inv X (Some (g, i)) U A.
Hypothesis Hu : usedX X A g am.
Hypothesis HC1 : nt_C1 A g i am = true.
Let sc := am_sc am.
Definition okA : Prop := nt_mask am + bit i = ones (am_last am).
Definition strideV1 : Prop := 0 < am_maplen am /\ am_last am = 0 /\ class_size (am_sc am) <= am_maplen am * 4096 - UNIT.
Definition strideV2 : Prop := 0 < am_maplen am /\ am_last am <> 0.
Definition bouncing : Prop := 7 <= am_sc am <= 38 /\ 100 <= znth (am_sc am - 7) (st_bounces A).
Definition qfacts (q : apathM) : Prop :=
okA /\
match q with
| MQ1 => am_sc am = 63
| MQ2 => 0 <= am_sc am < 48 /\ am_maplen am = 0
| MQ3 => 0 <= am_sc am < 48 /\ 0 < am_maplen am /\ am_last am = 0 /\ am_maplen am * 4096 - UNIT < class_size (am_sc am)
| MQ4V1 => 0 <= am_sc am < 48 /\ strideV1 /\ am_next am <> Some g
| MQ4V2 => 0 <= am_sc am < 48 /\ strideV2 /\ am_next am <> Some g
| MQ5V1 => 0 <= am_sc am < 48 /\ strideV1 /\ am_next am = Some g /\ (am_sc am < 7 \/ 38 < am_sc am)
| MQ5V2 => 0 <= am_sc am < 48 /\ strideV2 /\ am_next am = Some g /\ (am_sc am < 7 \/ 38 < am_sc am)
| MQ6V1 => 0 <= am_sc am < 48 /\ strideV1 /\ am_next am = Some g /\ 7 <= am_sc am <= 38 /\ znth (am_sc am - 7) (st_bounces A) < 100
| MQ6V2 => 0 <= am_sc am < 48 /\ strideV2 /\ am_next am = Some g /\ 7 <= am_sc am <= 38 /\ znth (am_sc am - 7) (st_bounces A) < 100
| MQ7V1 => 0 <= am_sc am < 48 /\ strideV1 /\ am_next am = Some g /\ bouncing /\ 9 * (am_last am + 1) <= usage_of A (am_sc am) /\ am_last am + 1 < 20
| MQ7V2 => 0 <= am_sc am < 48 /\ strideV2 /\ am_next am = Some g /\ bouncing /\ 9 * (am_last am + 1) <= usage_of A (am_sc am) /\ am_last am + 1 < 20
end.
Definition hd_ok : Prop := forall q, active_hd A (am_sc am) = Some q -> q <> g /\ exists aq, usedX X A q aq.
Definition dfacts (d : dvarM) (p n : sptr) (ap an : ameta) : Prop :=
match d with
| MD0 => am_next am = None /\ am_prev am = None /\ (p = g /\ n = g /\ ap = am /\ an = am)
| MD1 => am_next am = Some g /\ am_prev am = Some g /\ 0 <= am_sc am < 48 /\ active_hd A (am_sc am) = Some g /\ (p = g /\ n = g /\ ap = am /\ an = am)
| MD2a => am_next am = Some n /\ am_prev am = Some p /\ n <> g /\ p <> g /\ p <> n /\ usedX X A p ap /\ usedX X A n an /\
0 <= am_sc am < 48 /\ hd_ok
| MD2b => am_next am = Some n /\ am_prev am = Some p /\ n <> g /\ p <> g /\ p <> n /\ usedX X A p ap /\ usedX X A n an /\
0 <= am_sc am < 48 /\ active_hd A (am_sc am) = Some g /\ am_avail an = 0
| MD2a' => am_next am = Some n /\ am_prev am = Some n /\ n <> g /\ (p = n /\ ap = an) /\ usedX X A n an /\
0 <= am_sc am < 48 /\ hd_ok
| MD2b' => am_next am = Some n /\ am_prev am = Some n /\ n <> g /\ (p = n /\ ap = an) /\ usedX X A n an /\
0 <= am_sc am < 48 /\ active_hd A (am_sc am) = Some g /\ am_avail an = 0
end.
Theorem ntA_cases :
exists q d p n ap an, validAM q d = true /\ qfacts q /\ dfacts d p n ap an.
Proof.
pose proof (mask_facts X U A g i am HI Hu) as (Hi & Hlast & Hm0 & Hbit & HL0 & HM0).
pose proof (inv_groups HI g am Hu) as ((Glast & Gaidx & Glen & Gav & Gfrn & Gdisj & Gabove & _) & Gml & Gsl & Gcl & Gmp & Gns).
unfold nt_C1 in HC1. apply andb_prop in HC1 as [Eall Hok]. apply Z.eqb_eq in Eall.
assert (Hscr : am_sc am = 63 \/ 0 <= am_sc am < 48) by (destruct Gcl as [(C & _) | (C & _)]; [left | right]; exact C).
assert (D : exists d p n ap an, dfacts d p n ap an /\
match d with MD0 => am_next am = None | MD1 => am_next am = Some g | _ => exists n', am_next am = Some n' /\ n' <> g end).
{ destruct (am_next am) as [n|] eqn:En.
2:{ exists MD0, g, g, am, am. cbn. split; [split; [exact En|split; [|auto]] | reflexivity].
destruct Hscr as [H63|Hsc]; [destruct (inv_rings HI) as (_ & _ & DU); exact (proj1 (DU g am Hu H63)) | eapply unlinked_of_next_None; eauto]. }
assert (Hsc : 0 <= am_sc am < 48).
{ destruct Hscr as [H63|H]; [|exact H]. exfalso. destruct (inv_rings HI) as (_ & _ & DU). destruct (DU g am Hu H63) as [_ E]. rewrite En in E. discriminate. }
destruct (inv_rings HI) as (_ & AR & _). destruct (AR (am_sc am) Hsc) as (ms & Rg & Mem & Full & R1 & R2). pose proof Hsc as [Hsc0 Hsc48].
assert (Hgin : In g ms) by (apply (Mem g am Hu eq_refl); rewrite En; discriminate).
destruct (ring_links _ _ _ _ Rg Hgin) as (pr & nx & Lg).
pose proof Lg as Lg'. unfold alinks in Lg'. pose proof Hu as Hu0. unfold usedX in Hu0. rewrite Hu0, Z.eqb_refl in Lg'. injection Lg' as Epr Enx.
rewrite En in Enx. injection Enx as <-.
assert (USED : forall q, In q ms -> exists aq, usedX X A q aq /\ am_sc aq = am_sc am) by (intros q Hq; exact (ring_members_used _ _ _ _ _ _ Rg Hq)).
destruct (ring_neighbors _ _ _ _ _ _ Rg Hgin Lg) as [(-> & -> & Ems & Hhd) | (Hng & Hpg & Hpin & Hnin)].
- exists MD1, g, g, am, am. cbn. rewrite Epr, En. auto 10.
- destruct (USED pr Hpin) as (ap & Up & Sp). destruct (USED n Hnin) as (an & Un & Sn).
assert (HDOK : active_hd A (am_sc am) <> Some g -> hd_ok).
{ intros Hne q Hq. destruct (ring_head_In _ _ _ ltac:(rewrite <- Hq; exact Rg)) as [Hqin _].
destruct (USED q Hqin) as (aq & Uq & _). split; [congruence | exists aq; exact Uq]. }
assert (AVN : active_hd A (am_sc am) = Some g -> am_avail an = 0).
{ intros Hhd. destruct (Z.eq_dec (am_avail an) 0) as [E|E]; [exact E|]. exfalso.
pose proof (R1 n an Un Sn E) as Hn'. rewrite Hhd in Hn'. injection Hn'. intros ->. exact (Hng eq_refl). }
destruct (sptr_eq_dec pr n) as [Epn|Hpn].
+ destruct (osptr_eqb (active_hd A (am_sc am)) (Some g)) eqn:Ehd.
* apply osptr_eqb_eq in Ehd. pose proof (AVN Ehd) as AV0. exists MD2b', n, n, an, an. cbn. rewrite Epr, En, Epn. split; [| exists n; auto]. repeat match goal with |- _ /\ _ => split end; auto.
* assert (Hne : active_hd A (am_sc am) <> Some g) by (intros E; rewrite E in Ehd; cbn in Ehd; rewrite sptr_eqb_refl in Ehd; discriminate).
pose proof (HDOK Hne) as HD0. exists MD2a', n, n, an, an. cbn [dfacts]. rewrite Epr, En, Epn. split; [| exists n; auto]. repeat match goal with |- _ /\ _ => split end; auto.
+ destruct (osptr_eqb (active_hd A (am_sc am)) (Some g)) eqn:Ehd.
* apply osptr_eqb_eq in Ehd. pose proof (AVN Ehd) as AV0. exists MD2b, pr, n, ap, an. cbn. rewrite Epr, En. split; [| exists n; auto]. repeat match goal with |- _ /\ _ => split end; auto.
* assert (Hne : active_hd A (am_sc am) <> Some g) by (intros E; rewrite E in Ehd; cbn in Ehd; rewrite sptr_eqb_refl in Ehd; discriminate).
pose proof (HDOK Hne) as HD0. exists MD2a, pr, n, ap, an. cbn [dfacts]. rewrite Epr, En. split; [| exists n; auto]. repeat match goal with |- _ /\ _ => split end; auto. }
destruct D as (d & p & n & ap & an & Df & Dn).
unfold okay_to_free in Hok.
destruct Hscr as [H63 | Hsc].
{   exists MQ1, d, p, n, ap, an.
assert (d = MD0) as ->.
{ destruct (inv_rings HI) as (_ & _ & DU). destruct (DU g am Hu H63) as [_ E]. destruct d; try reflexivity; exfalso;
try (destruct Dn as (n' & E' & _)); congruence. }
split; [reflexivity|]. split; [| exact Df]. unfold qfacts. split; [exact Eall | exact H63]. }
replace (48 <=? am_sc am) with false in Hok by (symmetry; apply Z.leb_gt; lia). cbn [orb] in Hok.
assert (QD : forall q, match q with MQ1 => False | MQ2 | MQ3 => True | MQ4V1 | MQ4V2 => am_next am <> Some g | _ => am_next am = Some g end ->
qfacts q -> exists q d p n ap an, validAM q d = true /\ qfacts q /\ dfacts d p n ap an).
{ intros q Hq Qf. exists q, d, p, n, ap, an. split; [|auto].
destruct q, d; try reflexivity; cbn in Hq; exfalso; try (destruct Dn as (n' & E' & N')); first [exact Hq | congruence]. }
destruct (Z.eq_dec (am_maplen am) 0) as [Hml0 | Hml].
{ apply (QD MQ2 I). unfold qfacts, okA. auto. }
assert (STR : (am_last am = 0 /\ stride_of am = am_maplen am * 4096 - UNIT) \/ (am_last am <> 0 /\ stride_of am = class_size (am_sc am))).
{ unfold stride_of. destruct (Z.eq_dec (am_last am) 0) as [L0|L0]; [left | right]; split; auto.
- rewrite L0. cbn [Z.eqb andb]. replace (am_maplen am =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hml). reflexivity.
- replace (am_last am =? 0) with false by (symmetry; apply Z.eqb_neq; exact L0). reflexivity. }
destruct (stride_of am <? class_size (am_sc am)) eqn:Estr.
{ apply Z.ltb_lt in Estr. destruct STR as [[L0 ES] | [L0 ES]]; [| rewrite ES in Estr; lia].
apply (QD MQ3 I). unfold qfacts, okA. rewrite ES in Estr. repeat match goal with |- _ /\ _ => split end; auto; lia. }
apply Z.ltb_ge in Estr.
replace (am_maplen am =? 0) with false in Hok by (symmetry; apply Z.eqb_neq; exact Hml).
assert (SV : (strideV1 /\ forall q1 q2 : apathM, (exists q0 d0 p0 n0 ap0 an0, validAM q0 d0 = true /\ qfacts q0 /\ dfacts d0 p0 n0 ap0 an0) -> True) \/ strideV2).
{ destruct STR as [[L0 ES] | [L0 ES]]; [left | right].
- split; [|auto]. unfold strideV1. rewrite ES in Estr. repeat split; auto; lia.
- unfold strideV2. split; [lia | exact L0]. }
assert (PICK : forall (q1 q2 : apathM) (P : Prop),
(strideV1 -> qfacts q1) -> (strideV2 -> qfacts q2) ->
match q1 with MQ1 => False | MQ2 | MQ3 => True | MQ4V1 | MQ4V2 => am_next am <> Some g | _ => am_next am = Some g end ->
match q2 with MQ1 => False | MQ2 | MQ3 => True | MQ4V1 | MQ4V2 => am_next am <> Some g | _ => am_next am = Some g end ->
exists q d p n ap an, validAM q d = true /\ qfacts q /\ dfacts d p n ap an).
{ intros q1 q2 _ H1 H2 M1 M2. destruct SV as [[V1 _] | V2]; [apply (QD q1 M1 (H1 V1)) | apply (QD q2 M2 (H2 V2))]. }
destruct (osptr_eqb (am_next am) (Some g)) eqn:Enx.
2:{ assert (Hnx : am_next am <> Some g) by (intros E; rewrite E in Enx; cbn in Enx; rewrite sptr_eqb_refl in Enx; discriminate).
apply (PICK MQ4V1 MQ4V2 True); [ intros HV; unfold qfacts, okA, bouncing; repeat match goal with |- _ /\ _ => split end; auto; lia | intros HV; unfold qfacts, okA, bouncing; repeat match goal with |- _ /\ _ => split end; auto; lia | cbn; auto | cbn; auto ]. }
apply osptr_eqb_eq in Enx. cbn [negb] in Hok.
unfold is_bouncing, bounce_idx in Hok.
destruct ((7 <=? am_sc am) && (am_sc am <? 39)) eqn:Eb.
2:{ assert (Hb : am_sc am < 7 \/ 38 < am_sc am).
{ destruct (Z.leb_spec 7 (am_sc am)); destruct (Z.ltb_spec (am_sc am) 39); cbn in Eb; try discriminate; lia. }
apply (PICK MQ5V1 MQ5V2 True); [ intros HV; unfold qfacts, okA, bouncing; repeat match goal with |- _ /\ _ => split end; auto; lia | intros HV; unfold qfacts, okA, bouncing; repeat match goal with |- _ /\ _ => split end; auto; lia | cbn; auto | cbn; auto ]. }
apply andb_prop in Eb as [Eb1 Eb2]. apply Z.leb_le in Eb1. apply Z.ltb_lt in Eb2.
destruct (100 <=? znth (am_sc am - 7) (st_bounces A)) eqn:Ebn.
2:{ apply Z.leb_gt in Ebn. apply (PICK MQ6V1 MQ6V2 True); [ intros HV; unfold qfacts, okA, bouncing; repeat match goal with |- _ /\ _ => split end; auto; lia | intros HV; unfold qfacts, okA, bouncing; repeat match goal with |- _ /\ _ => split end; auto; lia | cbn; auto | cbn; auto ]. }
apply Z.leb_le in Ebn. cbn [negb] in Hok. apply andb_prop in Hok as [H9 H20]. apply Z.leb_le in H9. apply Z.ltb_lt in H20.
apply (PICK MQ7V1 MQ7V2 True); [ intros HV; unfold qfacts, okA, bouncing; repeat match goal with |- _ /\ _ => split end; auto; lia | intros HV; unfold qfacts, okA, bouncing; repeat match goal with |- _ /\ _ => split end; auto; lia | cbn; auto | cbn; auto ].
Qed.
End w.
End b.
