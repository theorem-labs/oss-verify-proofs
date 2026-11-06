From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YO0i YO0f YM02 YO0p.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Local Open Scope mm_scope.

Ltac fs := cbn beta iota zeta delta [fst snd].
Ltac bz := cbv beta iota zeta.

Fixpoint lwn {A : Type} (P : A -> Prop) (t : itree astate A) : Prop :=
match t with
| IRet a => P a
| IFail _ => True
| IAsk q _ k => mmapclass q = false /\ forall z, lwn P (k z)
end.
Lemma lwn_mono {A} (P P' : A -> Prop) t : (forall a, P a -> P' a) -> lwn P t -> lwn P' t.
Proof.
induction t as [a|q sn k IH|f]; cbn [lwn]; intros HP H.
- apply HP, H.
- destruct H as [Hm H]. split; [exact Hm | intros z; apply IH; [exact HP | apply H]].
- exact I.
Qed.
Lemma lwn_ibind {A B} (t : itree astate A) (k : A -> itree astate B) P :
lwn (fun a => lwn P (k a)) t -> lwn P (ibind t k).
Proof.
induction t as [a|q sn c IH|f]; cbn [lwn ibind]; intros H.
- exact H.
- destruct H as [Hm H]. split; [exact Hm | intros z; apply IH, H].
- exact I.
Qed.
Definition NMm {A} (m : M A) : Prop := forall s, lwn (fun _ => True) (m s).
Lemma NM_bind {A B} (m : M A) (k : A -> M B) : NMm m -> (forall a, NMm (k a)) -> NMm (bind m k).
Proof.
intros Hm Hk s. unfold bind. apply lwn_ibind. eapply lwn_mono; [|apply Hm]. intros [a s'] _. apply Hk.
Qed.
Lemma NM_ret {A} (a : A) : NMm (ret a).
Proof. intros s. exact I. Qed.
Lemma NM_fail {A} f : NMm (@fail A f).
Proof. intros s. exact I. Qed.
Lemma NM_get : NMm get.
Proof. intros s. exact I. Qed.
Lemma NM_put x : NMm (put x).
Proof. intros s. exact I. Qed.
Lemma NM_modify f : NMm (modify f).
Proof. intros s. exact I. Qed.
Lemma NM_massert b i : NMm (massert b i).
Proof. unfold massert. destruct b; [apply NM_ret | apply NM_fail]. Qed.
Lemma NM_mcheck b i : NMm (mcheck b i).
Proof. unfold mcheck. destruct b; [apply NM_ret | apply NM_fail]. Qed.
Lemma NM_ask q : mmapclass q = false -> NMm (ask q).
Proof. intros H s. unfold ask. cbn [lwn]. split; [exact H | intros z; exact I]. Qed.
Lemma NM_askz q : mmapclass q = false -> NMm (askz q).
Proof. intros H s. unfold askz. cbn [lwn]. split; [exact H | intros z; exact I]. Qed.
Lemma NM_getm p : NMm (getm p).
Proof.
unfold getm. apply NM_bind; [apply NM_get | intros s0].
destruct (mlookup (st_metas s0) p) as [[| |am]|]; first [apply NM_ret | apply NM_fail].
Qed.
Lemma NM_setm p am : NMm (setm p am).
Proof. apply NM_modify. Qed.
Lemma NM_setslot p x : NMm (setslot p x).
Proof. apply NM_modify. Qed.
Lemma NM_get_links p : NMm (get_links p).
Proof.
unfold get_links. apply NM_bind; [apply NM_get | intros s0].
destruct (mlookup (st_metas s0) p); first [apply NM_ret | apply NM_fail].
Qed.
Lemma NM_set_links p pr nx : NMm (set_links p pr nx).
Proof.
unfold set_links. apply NM_bind; [apply NM_get | intros s0].
destruct (mlookup (st_metas s0) p); [apply NM_setslot | apply NM_fail].
Qed.
Lemma NM_set_prev p pr : NMm (set_prev p pr).
Proof. unfold set_prev. apply NM_bind; [apply NM_get_links | intros; apply NM_set_links]. Qed.
Lemma NM_set_next p nx : NMm (set_next p nx).
Proof. unfold set_next. apply NM_bind; [apply NM_get_links | intros; apply NM_set_links]. Qed.
Lemma NM_get_head h : NMm (get_head h).
Proof. unfold get_head. apply NM_bind; [apply NM_get | intros s0; destruct h; apply NM_ret]. Qed.
Lemma NM_set_head h v : NMm (set_head h v).
Proof. unfold set_head. destruct h; apply NM_modify. Qed.
Lemma NM_queue h m : NMm (queue h m).
Proof.
unfold queue. apply NM_bind; [apply NM_get_links | intros l].
apply NM_bind; [apply NM_massert | intros _].
apply NM_bind; [apply NM_get_head | intros [head|]].
- apply NM_bind; [apply NM_get_links | intros lh]. destruct (fst lh); [| apply NM_fail].
apply NM_bind; [apply NM_set_links | intros _]. apply NM_bind; [apply NM_set_next | intros _]. apply NM_set_prev.
- apply NM_bind; [apply NM_set_links | intros _]. apply NM_set_head.
Qed.
Lemma NM_dequeue h m : NMm (dequeue h m).
Proof.
unfold dequeue. apply NM_bind; [apply NM_get_links | intros l].
apply NM_bind; [| intros _; apply NM_set_links].
destruct (osptr_eqb (snd l) (Some m)); [apply NM_set_head|].
destruct (fst l) as [pr|]; [| apply NM_fail]. destruct (snd l) as [nx|]; [| apply NM_fail].
apply NM_bind; [apply NM_set_next | intros _]. apply NM_bind; [apply NM_set_prev | intros _].
apply NM_bind; [apply NM_get_head | intros hd]. destruct (osptr_eqb hd (Some m)); [apply NM_set_head | apply NM_ret].
Qed.
Lemma NM_dequeue_head h : NMm (dequeue_head h).
Proof.
unfold dequeue_head. apply NM_bind; [apply NM_get_head | intros [m|]]; [|apply NM_ret].
apply NM_bind; [apply NM_dequeue | intros _; apply NM_ret].
Qed.
Lemma NM_free_meta m : NMm (free_meta m).
Proof. unfold free_meta. apply NM_bind; [apply NM_setslot | intros _; apply NM_queue]. Qed.
Lemma NM_activate_group m : NMm (activate_group m).
Proof.
unfold activate_group. apply NM_bind; [apply NM_getm | intros am]. bz.
apply NM_bind; [apply NM_massert | intros _]. apply NM_bind; [apply NM_setm | intros _; apply NM_ret].
Qed.
Lemma NM_decay_bounces sc : NMm (decay_bounces sc).
Proof. unfold decay_bounces. destruct (bounce_idx sc); [apply NM_modify | apply NM_ret]. Qed.
Lemma NM_try_avail sc : NMm (try_avail sc).
Proof.
unfold try_avail. apply NM_bind; [apply NM_get_head | intros [m0|]; bz; [|apply NM_ret]].
apply NM_bind; [apply NM_getm | intros am0]. bz.
destruct (negb (am_avail am0 =? 0)); [apply NM_bind; [apply NM_setm | intros; apply NM_ret]|].
apply NM_bind.
{ destruct (am_freed am0 =? 0).
- apply NM_bind; [apply NM_dequeue | intros; apply NM_get_head].
- apply NM_bind; [apply NM_set_head | intros; apply NM_ret]. }
intros [m1|]; bz; [|apply NM_ret].
apply NM_bind; [apply NM_getm | intros am1].
apply NM_bind.
{ destruct (am_freed am1 =? ones (am_last am1)); [|apply NM_ret].
destruct (am_next am1); [|apply NM_fail]. apply NM_bind; [apply NM_set_head | intros; apply NM_ret]. }
intros m2. apply NM_bind; [apply NM_getm | intros am2]. bz.
apply NM_bind.
{ destruct (Z.land (am_freed am2) (ones (am_aidx am2)) =? 0); [|apply NM_ret].
destruct (negb (osptr_eqb (am_next am2) (Some m2))).
- destruct (am_next am2); [|apply NM_fail]. apply NM_bind; [apply NM_set_head | intros; apply NM_ret].
- apply NM_bind; [apply NM_setm | intros; apply NM_ret]. }
intros m3. apply NM_bind; [apply NM_activate_group | intros mask].
apply NM_bind; [apply NM_massert | intros _]. apply NM_bind; [apply NM_getm | intros am3].
apply NM_bind; [apply NM_decay_bounces | intros _]. apply NM_bind; [apply NM_getm | intros am3'].
bz. apply NM_bind; [apply NM_setm | intros; apply NM_ret].
Qed.
Lemma NM_enframe g idx n ctr k : NMm (enframe g idx n ctr k).
Proof.
unfold enframe. apply NM_bind; [apply NM_getm | intros am]. apply NM_bind; [apply NM_mcheck | intros _]. bz.
apply NM_bind.
{ match goal with |- NMm (if ?c then _ else _) => destruct c end; [apply NM_ret|].
match goal with |- NMm (match ?x with _ => _ end) => destruct x as [[h3 h16]|] end;
[apply NM_ret | apply NM_bind; [apply NM_askz; reflexivity | intros; apply NM_ret]]. }
intros off0. bz. apply NM_bind; [apply NM_massert | intros _]. bz.
apply NM_bind; [apply NM_setm | intros; apply NM_ret].
Qed.
Lemma NM_step_seq : NMm step_seq.
Proof. apply NM_modify. Qed.
Lemma NM_account_bounce sc : NMm (account_bounce sc).
Proof. unfold account_bounce. destruct (bounce_idx sc); [apply NM_modify | apply NM_ret]. Qed.
Lemma NM_install_group m sc cnt aidx maplen mem sl : NMm (install_group m sc cnt aidx maplen mem sl).
Proof.
unfold install_group. apply NM_bind; [apply NM_get | intros s0].
apply NM_bind; [apply NM_modify | intros _]. bz.
apply NM_bind; [apply NM_setm | intros _]. apply NM_queue.
Qed.
Lemma NM_new_region k len : NMm (new_region k len).
Proof.
unfold new_region. apply NM_bind; [apply NM_get | intros s0]. bz.
apply NM_bind; [apply NM_put | intros _; apply NM_ret].
Qed.
Lemma NM_upd_region r f : NMm (upd_region r f).
Proof. apply NM_modify. Qed.
Lemma NM_area_from_brk : NMm area_from_brk.
Proof.
unfold area_from_brk. apply NM_bind; [apply NM_get | intros s0].
match goal with |- NMm (if ?c then _ else _) => destruct c end; [|apply NM_ret].
destruct (st_brk s0) as [| |r p].
- apply NM_bind; [apply NM_ask; reflexivity | intros _]. apply NM_bind; [apply NM_ask; reflexivity | intros ok].
destruct ok.
+ apply NM_bind; [apply NM_new_region | intros r]. apply NM_bind; [apply NM_modify | intros _].
apply NM_bind; [apply NM_ask; reflexivity | intros _; apply NM_ret].
+ apply NM_bind; [apply NM_modify | intros _; apply NM_ret].
- apply NM_ret.
- apply NM_bind; [apply NM_ask; reflexivity | intros ok]. destruct ok.
+ apply NM_bind; [apply NM_upd_region | intros _]. apply NM_bind; [apply NM_modify | intros _; apply NM_ret].
+ apply NM_bind; [apply NM_modify | intros _; apply NM_ret].
Qed.

Fixpoint lff {A : Type} (P : bool -> A -> Prop) (b : bool) (t : itree astate A) : Prop :=
match t with
| IRet a => P b a
| IFail _ => True
| IAsk q _ k => forall z, canswer q z -> lff P (b || (mmapclass q && (z =? 0))) (k z)
end.
Lemma lff_mono {A} (P P' : bool -> A -> Prop) b t : (forall b' a, P b' a -> P' b' a) -> lff P b t -> lff P' b t.
Proof.
revert b. induction t as [a|q sn k IH|f]; cbn [lff]; intros b HP H.
- apply HP, H.
- intros z Hz. apply IH; [exact HP | apply H, Hz].
- exact I.
Qed.
Lemma lff_ibind {A B} (t : itree astate A) (k : A -> itree astate B) P b :
lff (fun b' a => lff P b' (k a)) b t -> lff P b (ibind t k).
Proof.
revert b. induction t as [a|q sn c IH|f]; cbn [lff ibind]; intros b H.
- exact H.
- intros z Hz. apply IH, H, Hz.
- exact I.
Qed.
Lemma lff_lwn {A B} (t : itree astate A) (k : A -> itree astate B) Q P b :
lwn Q t -> (forall a, Q a -> lff P b (k a)) -> lff P b (ibind t k).
Proof.
induction t as [a|q sn c IH|f]; cbn [lff lwn ibind]; intros Hl Hk.
- apply Hk, Hl.
- destruct Hl as [Hm Hl]. intros z Hz. rewrite Hm. cbn [andb]. rewrite orb_false_r. apply IH; [apply Hl | exact Hk].
- exact I.
Qed.
Lemma lff_cpath {A} (t : itree astate A) P b tr a :
lff P b t -> cpath t tr a -> exists b', P b' a /\ (b' = false -> b = false /\ cpath04 t tr a).
Proof.
revert b tr. induction t as [a'|q sn k IH|f]; intros b tr HL HC; destruct tr as [|[q' z] tr]; cbn [cpath] in HC; try contradiction.
- subst a'. exists b. split; [exact HL|]. intros ->. split; [reflexivity | cbn [cpath04]; reflexivity].
- destruct HC as (-> & Hc & HC). cbn [lff] in HL.
destruct (IH z _ tr (HL z Hc) HC) as (b' & HP & Hb). exists b'. split; [exact HP|].
intros E. destruct (Hb E) as [E1 E2]. apply orb_false_iff in E1 as [E3 E4]. split; [exact E3|].
cbn [cpath04]. split; [reflexivity|]. split; [|exact E2].
assert (Hz : mmapclass q = true -> z <> 0).
{ intros M. rewrite M in E4. cbn [andb] in E4. apply Z.eqb_neq in E4. exact E4. }
unfold canswer04. destruct (mmapclass q) eqn:Em; [|exact Hc].
specialize (Hz eq_refl). destruct q; cbn in Em; try discriminate; cbn in Hc; lia.
Qed.

Section mo.
Context {A B : Type}.
Lemma lff_bind (m : M B) (k : B -> M A) s b P :
lff (fun b' r => lff P b' (k (fst r) (snd r))) b (m s) -> lff P b (bind m k s).
Proof. intros H. unfold bind. apply lff_ibind. eapply lff_mono; [|exact H]. intros b' [a s'] H'. exact H'. Qed.
Lemma lff_ret (a : A) s b (P : bool -> A * astate -> Prop) : P b (a, s) -> lff P b (ret a s).
Proof. intros H. exact H. Qed.
Lemma lff_NM (m : M B) (k : B -> M A) s b P :
NMm m -> (forall a s', lff P b (k a s')) -> lff P b (bind m k s).
Proof.
intros Hm Hk. unfold bind. apply (lff_lwn _ _ (fun _ => True)); [apply Hm|]. intros [a s'] _. exact (Hk a s').
Qed.
End mo.
Lemma lff_get s b (P : bool -> astate * astate -> Prop) : P b (s, s) -> lff P b (get s).
Proof. intros H. exact H. Qed.
Lemma lff_modify f s b (P : bool -> unit * astate -> Prop) : P b (tt, f s) -> lff P b (modify f s).
Proof. intros H. exact H. Qed.
Lemma lff_ask q s b (P : bool -> bool * astate -> Prop) :
(forall z, canswer q z -> P (b || (mmapclass q && (z =? 0))) (negb (z =? 0), s)) -> lff P b (ask q s).
Proof. intros H. exact H. Qed.

Definition FSf {A} (m : M A) (bad : A -> Prop) : Prop :=
forall s b, lff (fun b' r => b' = b \/ bad (fst r)) b (m s).
Lemma lff_use {A B} (bad : B -> Prop) (m : M B) (k : B -> M A) s b P :
FSf m bad -> (forall a s', lff P b (k a s')) -> (forall a s' b', bad a -> lff P b' (k a s')) -> lff P b (bind m k s).
Proof.
intros Hm H1 H2. apply lff_bind. eapply lff_mono; [|apply Hm].
intros b' [a s'] [E|E]; cbn [fst snd] in *; [subst b'; apply H1 | apply H2; exact E].
Qed.

Lemma FS_mmap : FSf area_from_mmap (fun r => r = false).
Proof.
intros s b. unfold area_from_mmap. apply lff_bind, lff_get. fs.
destruct (st_avail_meta_area_count s =? 0).
- apply lff_bind, lff_ask. intros z Hz. fs. destruct (z =? 0) eqn:Ez; cbn [negb].
+ apply lff_ret. right. reflexivity.
+ rewrite andb_false_r, orb_false_r.
apply lff_NM; [apply NM_new_region | intros r s1]. fs.
apply lff_bind, lff_modify. fs. apply lff_ret. left. reflexivity.
- apply lff_ret. left. reflexivity.
Qed.
Lemma FS_open nu : FSf (open_area nu) (fun r => r = false).
Proof.
intros s b. unfold open_area. apply lff_bind, lff_get. fs.
destruct nu; bz.
- apply lff_bind, lff_ask. intros z Hz. fs. destruct (z =? 0) eqn:Ez; cbn [negb].
+ apply lff_ret. right. reflexivity.
+ rewrite andb_false_r, orb_false_r.
apply lff_NM; [apply NM_upd_region | intros u s1]. fs.
apply lff_bind, lff_modify. fs. apply lff_ret. left. reflexivity.
- apply lff_bind, lff_ret. fs. bz. apply lff_bind, lff_ret. fs.
apply lff_bind, lff_modify. fs. apply lff_ret. left. reflexivity.
Qed.
Lemma FS_alloc_meta : FSf alloc_meta (fun r => r = None).
Proof.
intros s b. unfold alloc_meta.
apply lff_NM; [apply NM_modify | intros u s0].
apply lff_NM; [apply NM_dequeue_head | intros fm s1]. fs.
destruct fm as [m|]; [apply lff_ret; left; reflexivity|].
apply lff_bind, lff_get. fs.
apply (lff_use (fun ok : bool => ok = false)).
- destruct (0 <? st_avail_meta_count s1); [intros s2 b2; apply lff_ret; left; reflexivity|].
intros s2 b2. apply lff_NM; [apply NM_area_from_brk | intros nu s3].
apply (lff_use (fun rs : bool => rs = false)); [apply FS_mmap | |].
+ intros rs s4. destruct rs; bz; [apply FS_open | apply lff_ret; right; reflexivity].
+ intros rs s4 b4 E. subst rs. bz. apply lff_ret. right. reflexivity.
- intros ok s2. destruct ok; cbn [negb]; bz; [|apply lff_ret; left; reflexivity].
apply lff_NM; [apply NM_get | intros s3 s4]. fs.
apply lff_NM; [apply NM_put | intros u5 s5].
apply lff_NM; [apply NM_setslot | intros u6 s6]. apply lff_ret. left. reflexivity.
- intros ok s2 b2 E. subst ok. cbn [negb]. bz. apply lff_ret. right. reflexivity.
Qed.

Theorem alloc_FS fuel :
(forall sc req, FSf (alloc_slot fuel sc req) (fun i => i < 0)) /\
(forall sc req, FSf (alloc_group fuel sc req) (fun o => o = None)).
Proof.
induction fuel as [|f [IHs IHg]]; [split; intros sc req s b; exact I|].
split.
- intros sc req s b. cbn fix beta iota delta [alloc_slot].
apply lff_NM; [apply NM_try_avail | intros first s1].
destruct (negb (first =? 0)); [apply lff_ret; left; reflexivity|].
apply (lff_use (fun o : option sptr => o = None)); [apply IHg | |].
+ intros og s2. destruct og; apply lff_ret; left; reflexivity.
+ intros og s2 b' E. subst og. apply lff_ret. right. cbn [fst]. lia.
- intros sc req s b. cbn fix beta iota delta [alloc_group].
apply (lff_use (fun o : option sptr => o = None)); [apply FS_alloc_meta | |].
2:{ intros om s1 b' E. subst om. apply lff_ret. right. reflexivity. }
intros om s1. destruct om as [m|]; [|apply lff_ret; left; reflexivity].
apply lff_bind, lff_get. fs.
match goal with |- lff _ _ ((if ?c then _ else _) _) => destruct c end.
+ apply lff_NM; [apply NM_account_bounce | intros u2 s2].
apply lff_NM; [apply NM_step_seq | intros u3 s3].
apply lff_bind, lff_ask. intros z Hz. fs. destruct (z =? 0) eqn:Ez; cbn [negb].
* apply lff_NM; [apply NM_free_meta | intros u4 s4]. apply lff_ret. right. reflexivity.
* rewrite andb_false_r, orb_false_r.
apply lff_NM; [apply NM_new_region | intros r4 s4]. fs.
apply lff_NM; [apply NM_get | intros s5 s6]. fs.
apply lff_NM; [apply NM_put | intros u7 s7]. fs.
apply lff_NM; [apply NM_install_group | intros u8 s8]. apply lff_ret. left. reflexivity.
+ apply (lff_use (fun i : Z => i < 0)); [apply IHs | |].
* intros idx s2. destruct (idx <? 0).
-- apply lff_NM; [apply NM_free_meta | intros u3 s3]. apply lff_ret. right. reflexivity.
-- apply lff_NM; [apply NM_get_head | intros hj s3]. destruct hj as [g|]; [|exact I].
apply lff_NM; [apply NM_getm | intros amg s4].
apply lff_NM; [apply NM_mcheck | intros u5 s5].
apply lff_NM; [apply NM_get | intros s6 s7].
apply lff_NM; [apply NM_enframe | intros p s8].
apply lff_NM; [apply NM_install_group | intros u9 s9]. apply lff_ret. left. reflexivity.
* intros idx s2 b' E. destruct (idx <? 0) eqn:Ei; [|apply Z.ltb_ge in Ei; lia].
apply lff_NM; [apply NM_free_meta | intros u3 s3]. apply lff_ret. right. reflexivity.
Qed.

Theorem malloc_FS n : FSf (malloc n) (fun r => r = None).
Proof.
intros s b. unfold malloc.
destruct (size_overflows n); [apply lff_ret; right; reflexivity|].
destruct (MMAP_THRESHOLD <=? n).
- apply lff_bind, lff_ask. intros z Hz. fs. destruct (z =? 0) eqn:Ez; cbn [negb]; [apply lff_ret; right; reflexivity|].
rewrite andb_false_r, orb_false_r.
apply lff_NM; [apply NM_new_region | intros r s1].
apply lff_NM; [apply NM_step_seq | intros u2 s2].
apply (lff_use (fun o : option sptr => o = None)); [apply FS_alloc_meta | |].
+ intros og s3. destruct og as [g|].
* apply lff_NM; [apply NM_setm | intros u4 s4].
apply lff_NM; [apply NM_get | intros s5 s6]. fs.
apply lff_NM; [apply NM_put | intros u7 s7].
apply lff_NM; [apply NM_enframe | intros p s8]. apply lff_ret. left. reflexivity.
* apply lff_NM; [apply NM_ask; reflexivity | intros z4 s4].
apply lff_NM; [apply NM_upd_region | intros u5 s5]. apply lff_ret. right. reflexivity.
+ intros og s3 b' E. subst og.
apply lff_NM; [apply NM_ask; reflexivity | intros z4 s4].
apply lff_NM; [apply NM_upd_region | intros u5 s5]. apply lff_ret. right. reflexivity.
- apply lff_NM; [apply NM_get | intros s0 s1]. fs.
apply lff_NM.
{ match goal with |- NMm (match ?x with _ => _ end) => destruct x as [gm|] end; [|apply NM_ret].
apply NM_bind; [apply NM_getm | intros am].
destruct (am_avail am =? 0); [apply NM_ret|]. bz. apply NM_bind; [apply NM_setm | intros; apply NM_ret]. }
intros r s2.
apply (lff_use (fun gi : option (sptr * Z) => gi = None)).
+ destruct r as [gi|]; [intros s3 b3; apply lff_ret; left; reflexivity|].
intros s3 b3. apply (lff_use (fun i : Z => i < 0)); [apply (proj1 (alloc_FS NEST_FUEL)) | |].
* intros idx s4. destruct (idx <? 0); [apply lff_ret; right; reflexivity|].
apply lff_NM; [apply NM_get_head | intros hd s5]. destruct hd as [gm|]; [apply lff_ret; left; reflexivity | exact I].
* intros idx s4 b4 E. destruct (idx <? 0) eqn:Ei; [apply lff_ret; right; reflexivity | apply Z.ltb_ge in Ei; lia].
+ intros gi s3. destruct gi as [[gm idx]|]; [|apply lff_ret; left; reflexivity].
apply lff_NM; [apply NM_get | intros s4 s5].
apply lff_NM; [apply NM_enframe | intros p s6]. apply lff_ret. left. reflexivity.
+ intros gi s3 b3 E. subst gi. apply lff_ret. right. reflexivity.
Qed.

Theorem malloc_some_cpath04 : forall s n tr q s', WF s -> 0 <= n ->
cpath (malloc n s) tr (Some q, s') -> cpath04 (malloc n s) tr (Some q, s').
Proof.
intros s n tr q s' _ _ Hc.
destruct (lff_cpath _ _ false tr _ (malloc_FS n s false) Hc) as (b' & HP & Hb).
destruct HP as [-> | E]; [exact (proj2 (Hb eq_refl)) | cbn in E; discriminate].
Qed.
