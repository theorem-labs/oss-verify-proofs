(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Trevor Hansen, 2026-11: module names. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import YK15 YN02.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import YP0j YP0g YP0h YP0r YP07 YP04 YP05.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Fixpoint along {A : Type} (pol : kreq -> Z) (P : A -> Prop) (t : itree astate A) : Prop :=
match t with
| IRet a => P a
| IFail _ => True
| IAsk q _ k => along pol P (k (pol q))
end.
Lemma along_mono {A} pol (P Q : A -> Prop) t : (forall a, P a -> Q a) -> along pol P t -> along pol Q t.
Proof. revert P Q. induction t as [a | q s k IH | f]; intros P Q HPQ H; cbn in *; auto. eapply IH; eauto. Qed.
Lemma along_true {A} pol (t : itree astate A) : along pol (fun _ => True) t.
Proof. induction t as [a | q s k IH | f]; cbn; auto. Qed.
Lemma along_ibind {A B} pol (P : B -> Prop) (t : itree astate A) (f : A -> itree astate B) :
along pol (fun a => along pol P (f a)) t -> along pol P (ibind t f).
Proof. revert P f. induction t as [a | q s k IH | e]; intros P f H; cbn in *; auto. Qed.
Lemma along_bind {A B} pol (P : B * astate -> Prop) (Q : A * astate -> Prop) (m : M A) (f : A -> M B) s :
along pol Q (m s) -> (forall a s', Q (a, s') -> along pol P (f a s')) -> along pol P (bind m f s).
Proof.
intros Hm Hf. unfold bind. apply along_ibind. eapply along_mono; [|exact Hm]. intros [a s'] H. apply Hf, H.
Qed.
Lemma along_bind_any {A B} pol (P : B * astate -> Prop) (m : M A) (f : A -> M B) s :
(forall a s', along pol P (f a s')) -> along pol P (bind m f s).
Proof. intros Hf. apply (along_bind pol P (fun _ => True)); [apply along_true | intros; apply Hf]. Qed.
Lemma along_ret {A} pol (P : A * astate -> Prop) (a : A) s : P (a, s) -> along pol P (ret a s).
Proof. intros H. exact H. Qed.

Lemma along_fail {A} pol (P : A * astate -> Prop) f s : along pol P (fail f s).
Proof. exact I. Qed.
Lemma along_if {A} pol (P : A * astate -> Prop) (c : bool) (m1 m2 : M A) s :
(c = true -> along pol P (m1 s)) -> (c = false -> along pol P (m2 s)) -> along pol P ((if c then m1 else m2) s).
Proof. destruct c; auto. Qed.
Lemma along_ask pol (P : bool * astate -> Prop) q s : P (negb (pol q =? 0), s) -> along pol P (ask q s).
Proof. intros H. exact H. Qed.




Lemma along_massert pol (P : unit * astate -> Prop) b x s : P (tt, s) -> along pol P (massert b x s).
Proof. intros H. unfold massert. destruct b; [exact H | exact I]. Qed.
Lemma along_mcheck pol (P : unit * astate -> Prop) b x s : P (tt, s) -> along pol P (mcheck b x s).
Proof. intros H. unfold mcheck. destruct b; [exact H | exact I]. Qed.
Definition polR (q : kreq) : Z := if fallible q then 0 else canon q.
Definition polG (q : kreq) : Z := if fallible q then 1 else canon q.





Definition t_incl (T T' : TSet) : Prop := forall tr, T tr -> T' tr.
Lemma t_eq_of_incl T T' : t_incl T T' -> t_incl T' T -> t_eq T T'.
Proof. intros H1 H2 tr. split; auto. Qed.
Lemma tset_incl {A} (t : itree astate A) (K : A -> TSet) (T : TSet) :
(forall a, t_incl (K a) T) -> t_incl (tset t K) T.
Proof.
revert K. induction t as [a | q s k IH | f]; intros K HK tr H; cbn in *.
- exact (HK a tr H).
- destruct (fallible q); [destruct H as [H|H]|]; eapply IH; eauto.
- destruct H.
Qed.
Definition pol_canon (pol : kreq -> Z) : Prop :=
forall q, (fallible q = true -> pol q = 0 \/ pol q = 1) /\ (fallible q = false -> pol q = canon q).
Lemma polR_canon : pol_canon polR.
Proof. intros q. unfold polR. split; intros H; rewrite H; auto. Qed.
Lemma polG_canon : pol_canon polG.
Proof. intros q. unfold polG. split; intros H; rewrite H; auto. Qed.
Lemma along_tset_incl {A} pol (P : A -> Prop) (t : itree astate A) (K : A -> TSet) (T : TSet) :
pol_canon pol -> safe t -> along pol P t -> (forall a, P a -> t_incl T (K a)) -> t_incl T (tset t K).
Proof.
intros Hpol. revert K. induction t as [a | q s k IH | f]; intros K Hs H HK tr Htr; cbn in *.
- exact (HK a H tr Htr).
- destruct (Hpol q) as [P1 P2]. destruct (fallible q) eqn:Hf.
+ destruct (P1 eq_refl) as [E | E]; rewrite E in H;
[left | right]; (eapply IH; [apply Hs; apply answer_ok_kernel; exact Hf | exact H | exact HK | exact Htr]).
+ rewrite (P2 eq_refl) in H. eapply IH; [apply Hs; apply canon_answer_ok | exact H | exact HK | exact Htr].
- destruct Hs.
Qed.
Fixpoint tsum (l : list TSet) : TSet :=
match l with [] => t_bot | T :: r => t_alt2 T (tsum r) end.
Lemma tsum_app l1 l2 tr : tsum (l1 ++ l2) tr <-> t_alt2 (tsum l1) (tsum l2) tr.
Proof.
induction l1 as [|T l1 IH]; cbn; unfold t_alt2, t_bot in *; [tauto|]. rewrite IH. unfold t_alt2. tauto.
Qed.
Lemma tsum_In l tr : tsum l tr <-> exists T, In T l /\ T tr.
Proof.
induction l as [|T l IH]; cbn; unfold t_bot, t_alt2.
- split; [tauto | intros (T & [] & _)].
- rewrite IH. split.
+ intros [H | (T' & Hin & H)]; [exists T; auto | exists T'; auto].
+ intros (T' & [<- | Hin] & H); [left; exact H | right; exists T'; auto].
Qed.
Lemma tset_cleaves {A} (t : itree astate A) (K : A -> TSet) l :
cleaves t = Some l -> t_eq (tset t K) (tsum (map K l)).
Proof.
revert K l. induction t as [a | q s k IH | f]; intros K l Hc; cbn in Hc.
- injection Hc as <-. cbn. intros tr. unfold t_alt2, t_bot. tauto.
- destruct q; cbn [cleaves fallible] in Hc; try discriminate Hc;
first [
destruct (cleaves (k 0)) as [l0|] eqn:E0; [|discriminate Hc];
destruct (cleaves (k 1)) as [l1|] eqn:E1; [|discriminate Hc]; injection Hc as <-;
rewrite tset_ask_fallible by reflexivity;
intros tr; rewrite map_app; pose proof (tsum_app (map K l0) (map K l1) tr) as X;
pose proof (IH 0 K l0 E0 tr) as X0; pose proof (IH 1 K l1 E1 tr) as X1; unfold t_alt2 in *; tauto
|
rewrite tset_ask_canon by reflexivity; cbn [canon]; apply IH; exact Hc ].
- injection Hc as <-. cbn. apply t_eq_refl.
Qed.
Definition AKeep (s0 : astate) {A} (r : A * astate) : Prop := st_active (snd r) = st_active s0.
Definition keepsA {A} (pol : kreq -> Z) (m : M A) : Prop := forall s0 s, st_active s = st_active s0 -> along pol (AKeep s0) (m s).
Section i.
Variable pol : kreq -> Z.
Lemma kA_along {A} (m : M A) s0 s : keepsA pol m -> st_active s = st_active s0 -> along pol (AKeep s0) (m s).
Proof. intros H E. exact (H s0 s E). Qed.
Lemma along_bind_keep {A B} (m : M A) (f : A -> M B) s0 s :
along pol (AKeep s0) (m s) -> (forall a s', st_active s' = st_active s0 -> along pol (AKeep s0) (f a s')) ->
along pol (AKeep s0) (bind m f s).
Proof. intros Hm Hf. eapply along_bind; [exact Hm|]. intros a s' E. apply Hf. exact E. Qed.
Lemma kA_bind {A B} (m : M A) (f : A -> M B) : keepsA pol m -> (forall a, keepsA pol (f a)) -> keepsA pol (bind m f).
Proof. intros Hm Hf s0 s E. apply along_bind_keep; [apply Hm, E | intros a s' E'; apply (Hf a), E']. Qed.
Lemma kA_ret {A} (a : A) : keepsA pol (ret a). Proof. intros s0 s E. exact E. Qed.
Lemma kA_get : keepsA pol get. Proof. intros s0 s E. exact E. Qed.
Lemma kA_put_eq s' s0 s : st_active s' = st_active s0 -> along pol (AKeep s0) (put s' s). Proof. intros E. exact E. Qed.
Lemma kA_fail {A} f : keepsA pol (@fail A f). Proof. intros s0 s E. exact I. Qed.
Lemma kA_massert b x : keepsA pol (massert b x). Proof. intros s0 s E. apply along_massert. exact E. Qed.
Lemma kA_mcheck b x : keepsA pol (mcheck b x). Proof. intros s0 s E. apply along_mcheck. exact E. Qed.
Lemma kA_ask q : keepsA pol (ask q). Proof. intros s0 s E. exact E. Qed.
Lemma kA_askz q : keepsA pol (askz q). Proof. intros s0 s E. exact E. Qed.
Lemma kA_modify f : (forall s, st_active (f s) = st_active s) -> keepsA pol (modify f).
Proof. intros Hf s0 s E. unfold AKeep, modify. cbn. rewrite Hf. exact E. Qed.
Lemma kA_getm p : keepsA pol (getm p).
Proof. intros s0 s E. unfold getm, bind, get. cbn. destruct (mlookup (st_metas s) p) as [[]|]; cbn; auto. Qed.
Lemma kA_setm p am : keepsA pol (setm p am). Proof. intros s0 s E. exact E. Qed.
Lemma kA_setslot p x : keepsA pol (setslot p x). Proof. intros s0 s E. exact E. Qed.
Lemma kA_get_links p : keepsA pol (get_links p).
Proof. intros s0 s E. unfold get_links, bind, get. cbn. destruct (mlookup (st_metas s) p) as [[]|]; cbn; auto. Qed.
Lemma kA_set_links p a b : keepsA pol (set_links p a b).
Proof. intros s0 s E. unfold set_links, bind, get. cbn. destruct (mlookup (st_metas s) p) as [[]|]; cbn; auto. Qed.
Lemma kA_set_prev p a : keepsA pol (set_prev p a).
Proof. unfold set_prev. apply kA_bind; [apply kA_get_links | intros l; apply kA_set_links]. Qed.
Lemma kA_set_next p a : keepsA pol (set_next p a).
Proof. unfold set_next. apply kA_bind; [apply kA_get_links | intros l; apply kA_set_links]. Qed.
Lemma kA_get_head h : keepsA pol (get_head h).
Proof. intros s0 s E. unfold get_head, bind, get. cbn. destruct h; exact E. Qed.
Lemma kA_set_head_free v : keepsA pol (set_head HFreeMeta v). Proof. intros s0 s E. exact E. Qed.
Lemma kA_set_usage_of sc v : keepsA pol (set_usage_of sc v). Proof. intros s0 s E. exact E. Qed.
Lemma kA_new_region k len : keepsA pol (new_region k len). Proof. intros s0 s E. exact E. Qed.
Lemma kA_upd_region r f : keepsA pol (upd_region r f). Proof. intros s0 s E. exact E. Qed.
Lemma kA_step_seq : keepsA pol step_seq.
Proof. intros s0 s E. unfold step_seq, modify, AKeep. cbn. destruct (st_seq s =? 255); exact E. Qed.
Lemma kA_record_seq sc : keepsA pol (record_seq sc).
Proof. unfold record_seq. destruct (bounce_idx sc); [apply kA_modify; reflexivity | apply kA_ret]. Qed.
Lemma kA_account_bounce sc : keepsA pol (account_bounce sc).
Proof.
unfold account_bounce. destruct (bounce_idx sc); [|apply kA_ret]. apply kA_modify. intros s. cbn.
destruct (negb (znth z (st_unmap_seq s) =? 0) && (st_seq s - znth z (st_unmap_seq s) <? 10))%bool; reflexivity.
Qed.
Lemma kA_decay_bounces sc : keepsA pol (decay_bounces sc).
Proof.
unfold decay_bounces. destruct (bounce_idx sc); [|apply kA_ret]. apply kA_modify. intros s. cbn.
destruct (znth z (st_bounces s) =? 0); reflexivity.
Qed.
End i.
End d.
Create HintDb keepsA.
#[export] Hint Resolve kA_ret kA_get kA_fail kA_massert kA_mcheck kA_ask kA_askz kA_getm kA_setm kA_setslot kA_get_links
kA_set_links kA_set_prev kA_set_next kA_get_head kA_set_head_free kA_set_usage_of kA_new_region kA_upd_region
kA_step_seq kA_record_seq kA_account_bounce kA_decay_bounces : keepsA.
Ltac kago1 :=
lazymatch goal with
| |- along _ (AKeep _) (bind get _ _) => unfold bind at 1; unfold get at 1; cbn [ibind]
| |- along _ (AKeep _) (bind _ _ _) => apply along_bind_keep; [ | intros ? ? ? ]
| |- along _ (AKeep _) ((if ?c then _ else _) _) => destruct c
| |- along _ (AKeep _) (if ?c then _ else _) => destruct c
| |- along _ (AKeep _) ((match ?x with _ => _ end) _) => destruct x
| |- along _ (AKeep _) (match ?x with _ => _ end) => destruct x
| |- along _ (AKeep _) (modify _ _) => apply kA_along; [apply kA_modify; intros ?; reflexivity | assumption]
| |- along _ (AKeep _) (put _ _) => apply kA_put_eq; cbn; assumption
| |- along _ (AKeep _) (ret _ _) => unfold AKeep, ret; cbn; assumption
| |- along _ (AKeep _) (IRet _) => unfold AKeep; cbn; assumption
| |- along _ (AKeep _) (?m _) => apply kA_along; [solve [auto 2 with keepsA] | assumption]
end.
Ltac kago := repeat kago1.
Section j. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section o.
Variable pol : kreq -> Z.
Lemma kA_queue_free m : keepsA pol (queue HFreeMeta m).
Proof. intros s0 s E. unfold queue. kago. Qed.
Lemma kA_dequeue_free m : keepsA pol (dequeue HFreeMeta m).
Proof. intros s0 s E. unfold dequeue. kago. Qed.
Lemma kA_dequeue_head_free : keepsA pol (dequeue_head HFreeMeta).
Proof. intros s0 s E. unfold dequeue_head. pose proof (kA_dequeue_free). kago. Qed.
Lemma kA_free_meta m : keepsA pol (free_meta m).
Proof. intros s0 s E. unfold free_meta. pose proof kA_queue_free. kago. Qed.
Lemma kA_area_from_brk : keepsA pol area_from_brk.
Proof. intros s0 s E. unfold area_from_brk. kago. Qed.
Lemma kA_area_from_mmap : keepsA pol area_from_mmap.
Proof. intros s0 s E. unfold area_from_mmap. kago. Qed.
Lemma kA_open_area nu : keepsA pol (open_area nu).
Proof. intros s0 s E. unfold open_area. kago. Qed.
Lemma kA_alloc_meta : keepsA pol alloc_meta.
Proof.
intros s0 s E. unfold alloc_meta.
pose proof kA_dequeue_head_free. pose proof kA_area_from_brk. pose proof kA_area_from_mmap. pose proof kA_open_area.
kago.
Qed.
Lemma try_avail_none sc s : active_hd s sc = None -> try_avail sc s = IRet (0, s).
Proof. intros H. unfold try_avail, bind, get_head, get. cbn. unfold active_hd in H. rewrite H. reflexivity. Qed.
End o.
Ltac afin := first [ exact I | reflexivity | eexists; reflexivity | assumption ].
Ltac atail := repeat first [ afin
| apply along_bind_any; intros
| progress (unfold bind at 1; unfold get at 1; cbn [ibind])
| apply along_if; intros ].
Lemma PS_alloc_meta s : along polG (fun r => exists m, fst r = Some m) (alloc_meta s).
Proof.
unfold alloc_meta. apply along_bind_any. intros u0 s0.
apply along_bind_any. intros [m|] s1; [exists m; reflexivity|].
unfold bind at 1, get at 1. cbn [ibind].
apply (along_bind polG _ (fun r => fst r = true)).
{ apply along_if; [intros _; reflexivity|]. intros _.
apply along_bind_any. intros nu s3. apply (along_bind polG _ (fun r => fst r = true)).
- unfold area_from_mmap. unfold bind at 1, get at 1. cbn [ibind]. apply along_if; [|intros _; reflexivity]. intros _.
apply (along_bind polG _ (fun r => fst r = true)); [apply along_ask; reflexivity|].
intros ok s5 E5. cbn in E5. subst ok. cbn [negb]. atail.
- intros rs s4 E4. cbn in E4. subst rs. cbn [negb]. unfold open_area. unfold bind at 1, get at 1. cbn [ibind].
apply (along_bind polG _ (fun r => fst r = true)).
+ destruct nu; [apply along_ask; reflexivity | reflexivity].
+ intros ok s6 E6. cbn in E6. subst ok. cbn [negb]. atail. }
intros ok s3 E3. cbn in E3. subst ok. cbn [negb]. atail.
Qed.
Lemma ctz32_nonneg m : 0 <= ctz32 m.
Proof. unfold ctz32. apply Z.log2_nonneg. Qed.
Lemma PS_slot_group : forall F,
(forall sc req s, along polG (fun r => 0 <= fst r) (alloc_slot F sc req s))
/\ (forall sc req s, along polG (fun r => exists m, fst r = Some m) (alloc_group F sc req s)).
Proof.
induction F as [|F [IHs IHg]].
- split; intros; cbn; exact I.
- split; intros sc req s.
+ rewrite alloc_slot_S. apply along_bind_any. intros first s1. apply along_if.
* intros _. apply along_ret. cbn. apply ctz32_nonneg.
* intros _. eapply along_bind; [apply IHg|]. intros og s2 [m E]. cbn in E. subst og. apply along_ret. cbn. lia.
+ cbn [alloc_group]. eapply along_bind; [apply PS_alloc_meta|]. intros om s1 [m E]. cbn in E. subst om.
unfold bind at 1, get at 1. cbn [ibind].
apply along_if; intros _.
* apply along_bind_any; intros; apply along_bind_any; intros.
apply (along_bind polG _ (fun r => fst r = true)); [apply along_ask; reflexivity|]. intros ok s5 E5. cbn in E5. subst ok. cbn [negb]. atail.
* eapply along_bind; [apply IHs|]. intros idx s3 Hidx. cbn in Hidx.
apply along_if; [intros E; apply Z.ltb_lt in E; lia|]. intros _.
apply along_bind_any. intros [g|] s4; [|apply along_fail]. atail.
Qed.
Theorem PS_malloc n s : size_overflows n = false -> along polG (fun r => exists p, fst r = Some p) (malloc n s).
Proof.
intros Hov. unfold malloc. rewrite Hov.
destruct (MMAP_THRESHOLD <=? n).
- apply (along_bind polG _ (fun r => fst r = true)); [apply along_ask; reflexivity|]. intros ok s1 E1. cbn in E1. subst ok. cbn [negb].
apply along_bind_any; intros; apply along_bind_any; intros.
eapply along_bind; [apply PS_alloc_meta|]. intros og s4 [g E]. cbn in E. subst og. atail.
- unfold bind at 1, get at 1. cbn [ibind]. apply along_bind_any. intros r s1.
apply (along_bind polG _ (fun x => exists gi, fst x = Some gi)).
+ destruct r as [gi|]; [eexists; reflexivity|].
eapply along_bind; [apply (proj1 (PS_slot_group NEST_FUEL))|]. intros idx s2 Hidx. cbn in Hidx.
apply along_if; [intros E; apply Z.ltb_lt in E; lia|]. intros _.
apply along_bind_any. intros [gm|] s3; [eexists; reflexivity | apply along_fail].
+ intros gi s2 [[gm idx] E]. cbn in E. subst gi. atail.
Qed.
Definition HN (N : Z) (s : astate) : Prop := forall sc, 0 <= sc < N -> active_hd s sc = None.
Lemma HN_of_active N s s' : st_active s' = st_active s -> HN N s -> HN N s'.
Proof. intros E H sc Hsc. unfold active_hd. rewrite E. apply H, Hsc. Qed.
Fixpoint zseq (a : Z) (n : nat) : list Z := match n with O => [] | S n' => a :: zseq (a + 1) n' end.
Lemma zseq_In a n z : In z (zseq a n) <-> a <= z < a + Z.of_nat n.
Proof. revert a. induction n as [|n IH]; intros a; cbn [zseq In]; [lia|]. rewrite IH. lia. Qed.
Definition HNb (N : Z) (s : astate) : bool :=
forallb (fun sc => match active_hd s sc with None => true | Some _ => false end) (zseq 0 (Z.to_nat N)).
Lemma HNb_HN N s : 0 <= N -> HNb N s = true -> HN N s.
Proof.
intros HN0 H sc Hsc. unfold HNb in H. apply forallb_forall with (x := sc) in H.
- destruct (active_hd s sc); [discriminate H | reflexivity].
- apply zseq_In. lia.
Qed.
Definition units (n : Z) : Z := Z.shiftr (n + IB - 1) 4.
Lemma size_to_class_units n : size_to_class n = class_of_units (units n).
Proof. reflexivity. Qed.
Lemma units_bound n b : 0 <= n -> n + 3 < 16 * b -> 0 <= units n < b.
Proof.
intros Hn Hb. unfold units, IB. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.
Definition cou_le (hi b : Z) : bool :=
forallb (fun u => (0 <=? class_of_units u) && (class_of_units u <=? hi))%bool (zseq 0 (Z.to_nat b)).
Lemma cou_le_sound hi b u : cou_le hi b = true -> 0 <= u < b -> 0 <= class_of_units u <= hi.
Proof.
intros H Hu. unfold cou_le in H. apply forallb_forall with (x := u) in H; [|apply zseq_In; rewrite Z2Nat.id by lia; lia].
apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.
Lemma cou_8191 : cou_le 47 8191 = true. Proof. vm_compute. reflexivity. Qed.
Lemma cou_4095 : cou_le 43 4095 = true. Proof. vm_compute. reflexivity. Qed.
Lemma cou_128 : cou_le 24 128 = true. Proof. vm_compute. reflexivity. Qed.
Lemma size_to_class_lt48 n : 0 <= n < MMAP_THRESHOLD -> 0 <= size_to_class n <= 47.
Proof. intros Hn. rewrite size_to_class_units. apply (cou_le_sound 47 8191); [apply cou_8191 | apply units_bound; unfold MMAP_THRESHOLD in Hn; lia]. Qed.
Lemma size_to_class_lt44 n : 0 <= n <= 65516 -> 0 <= size_to_class n <= 43.
Proof. intros Hn. rewrite size_to_class_units. apply (cou_le_sound 43 4095); [apply cou_4095 | apply units_bound; lia]. Qed.
Lemma size_to_class_nest n : 0 <= n <= 2044 -> 0 <= size_to_class n <= 24.
Proof. intros Hn. rewrite size_to_class_units. apply (cou_le_sound 24 128); [apply cou_128 | apply units_bound; lia]. Qed.
Lemma along_keep_HN {A} (m : M A) N s (c : A -> Prop) :
keepsA polR m -> HN N s -> (forall a, c a) -> along polR (fun r => c (fst r) /\ HN N (snd r)) (m s).
Proof.
intros Hm Hs Hc. eapply along_mono; [|apply (Hm s s eq_refl)]. intros [a s'] E. unfold AKeep in E. cbn in *.
split; [apply Hc | exact (HN_of_active N s s' E Hs)].
Qed.
Lemma PN_slot_group : forall F N, 25 <= N ->
(forall sc req s, HN N s -> 0 <= sc < N ->
along polR (fun r => fst r = -1 /\ HN N (snd r)) (alloc_slot F sc req s))
/\ (forall sc req s, HN N s -> 0 <= sc < N ->
along polR (fun r => fst r = None /\ HN N (snd r)) (alloc_group F sc req s)).
Proof.
intros F N HN24. induction F as [|F [IHs IHg]].
- split; intros; cbn; exact I.
- split; intros sc req s Hs Hsc.
+ rewrite alloc_slot_S. unfold bind at 1. rewrite (try_avail_none sc s (Hs sc Hsc)). cbn [ibind Z.eqb negb].
eapply along_bind; [apply IHg; assumption|]. intros og s2 [E H2]. cbn in E. subst og. apply along_ret. cbn. auto.
+ cbn [alloc_group]. eapply along_bind.
{ eapply along_mono; [|apply (kA_alloc_meta polR s s eq_refl)]. intros r Hr. exact Hr. }
intros om s1 E1. unfold AKeep in E1. cbn in E1. pose proof (HN_of_active N s s1 E1 Hs) as H1.
destruct om as [m|]; [|apply along_ret; cbn; auto].
unfold bind at 1, get at 1. cbn [ibind].
apply along_if; intros Enest.
*
eapply along_bind; [apply (along_keep_HN _ N s1 (fun _ => True)); [auto with keepsA | exact H1 | auto]|]. intros u2 s2 [_ H2].
eapply along_bind; [apply (along_keep_HN _ N s2 (fun _ => True)); [auto with keepsA | exact H2 | auto]|]. intros u3 s3 [_ H3].
apply (along_bind polR _ (fun r => fst r = false /\ HN N (snd r))); [apply along_ask; cbn; auto|].
intros ok s4 [E4 H4]. cbn in E4. subst ok. cbn [negb].
eapply along_bind; [apply (along_keep_HN _ N s4 (fun _ => True)); [apply kA_free_meta | exact H4 | auto]|]. intros u5 s5 [_ H5].
apply along_ret. cbn. auto.
*
apply Z.ltb_ge in Enest.
pose proof (initial_cnt_bound sc (usage_of s1 sc)) as Hcnt. pose proof (class_size_bound sc) as Hsz.
assert (Hj : 0 <= size_to_class (UNIT + initial_cnt sc (usage_of s1 sc) * class_size sc - IB) <= 24).
{ apply size_to_class_nest. unfold UNIT, IB, PGSZ in *. nia. }
eapply along_bind; [apply IHs; [exact H1 | lia]|]. intros idx s3 [E3 H3]. cbn in E3. subst idx. cbn [Z.ltb].
eapply along_bind; [apply (along_keep_HN _ N s3 (fun _ => True)); [apply kA_free_meta | exact H3 | auto]|]. intros u5 s5 [_ H5].
apply along_ret. cbn. auto.
Qed.
Theorem PN_malloc N n s :
25 <= N -> HN N s -> 0 <= n ->
(n < MMAP_THRESHOLD -> size_to_class n < N /\ (size_to_class n < 32 -> size_to_class n + 1 < N)) ->
along polR (fun r => fst r = None) (malloc n s).
Proof.
intros HN24 Hs Hn Hsc. unfold malloc.
destruct (size_overflows n); [reflexivity|].
destruct (MMAP_THRESHOLD <=? n) eqn:Eth.
-   reflexivity.
- apply Z.leb_gt in Eth. destruct (Hsc Eth) as [HscN Hsc32]. pose proof (size_to_class_lt48 n ltac:(lia)) as Hr.
unfold bind at 1, get at 1. cbn [ibind].
set (sc0 := size_to_class n) in *.
assert (A0 : nth (Z.to_nat sc0) (st_active s) None = None) by (apply (Hs sc0); lia).
rewrite A0. cbn [osptr_eqb andb].
match goal with |- along _ _ (bind ?r _ _) =>
set (sc := if ((4 <=? sc0) && (sc0 <? 32) && negb (sc0 =? 6) && Z.even sc0 && (usage_of s sc0 =? 0))%bool
then (if (if match nth (Z.to_nat (sc0 + 1)) (st_active s) None with
| Some h => match mlookup (st_metas s) h with
| Some (MUsed am) => ((am_avail am =? 0) && (am_freed am =? 0))%bool
| _ => true end
| None => true end
then usage_of s (sc0 + 1) + 3 else usage_of s (sc0 + 1)) <=? 12 then sc0 + 1 else sc0)
else sc0) in * end.
assert (Hsc' : 0 <= sc < N).
{ subst sc. destruct ((4 <=? sc0) && (sc0 <? 32) && negb (sc0 =? 6) && Z.even sc0 && (usage_of s sc0 =? 0))%bool eqn:Eb; [|lia].
apply andb_prop in Eb as [Eb _]. apply andb_prop in Eb as [Eb _]. apply andb_prop in Eb as [Eb _]. apply andb_prop in Eb as [_ Eb].
apply Z.ltb_lt in Eb.
match goal with |- context [if ?c then sc0 + 1 else sc0] => destruct c; lia end. }
assert (A1 : nth (Z.to_nat sc) (st_active s) None = None) by (apply (Hs sc); lia).
rewrite A1. cbn [ibind]. rewrite bind_ret_l. cbv beta iota.
apply (along_bind polR _ (fun r => fst r = None)).
{ eapply along_bind; [apply (proj1 (PN_slot_group NEST_FUEL N HN24)); [exact Hs | exact Hsc']|].
intros idx s2 [E2 H2]. cbn in E2. subst idx. cbn [Z.ltb]. apply along_ret. reflexivity. }
intros gi s2 E2. cbn in E2. subst gi. reflexivity.
Qed.
Theorem tset_malloc_nonesome N n s (K : option sptr * astate -> TSet) (A B : TSet) :
WF s -> 25 <= N -> HN N s -> 0 <= n ->
(n < MMAP_THRESHOLD -> size_to_class n < N /\ (size_to_class n < 32 -> size_to_class n + 1 < N)) ->
size_overflows n = false ->
(forall s', t_eq (K (None, s')) A) -> (forall p s', t_eq (K (Some p, s')) B) ->
t_eq (tset (malloc n s) K) (t_alt2 A B).
Proof.
intros HW HN24 Hs Hn Hsc Hov HA HB.
pose proof (malloc_safe s n HW Hn) as SAFE.
apply t_eq_of_incl.
- apply tset_incl. intros [[p|] s'] tr H; [right; apply (HB p s'), H | left; apply (HA s'), H].
- intros tr [H | H].
+ eapply (along_tset_incl polR _ _ K A polR_canon SAFE (PN_malloc N n s HN24 Hs Hn Hsc)); [|exact H].
intros [r s'] E. cbn in E. subst r. intros u Hu. apply (HA s'), Hu.
+ eapply (along_tset_incl polG _ _ K B polG_canon SAFE (PS_malloc n s Hov)); [|exact H].
intros [r s'] [p E]. cbn in E. subst r. intros u Hu. apply (HB p s'), Hu.
Qed.
End j.
