From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YO0i YO0f YM02 YO0p.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Local Open Scope mm_scope.

Fixpoint nomm {A : Type} (t : itree astate A) : Prop :=
  match t with
  | IRet _ => True
  | IFail _ => True
  | IAsk q _ k => mmapclass q = false /\ forall z, nomm (k z)
  end.

Lemma nomm_cpath04 {A} : forall (t : itree astate A) tr a, nomm t -> cpath t tr a -> cpath04 t tr a.
Proof.
  induction t as [a' | q s k IH | f]; intros [|[q' z] tr] a Hn H; cbn in *; try exact H; try contradiction.
  destruct Hn as [Hq Hk]. destruct H as (-> & Hc & H). split; [reflexivity|]. split.
  - unfold canswer04. rewrite Hq. exact Hc.
  - apply IH; [apply Hk | exact H].
Qed.

Lemma nomm_ibind {A B} (t : itree astate A) (k : A -> itree astate B) :
  nomm t -> (forall a, nomm (k a)) -> nomm (ibind t k).
Proof.
  induction t as [a | q s c IH | f]; intros Ht Hk; cbn in *; [apply Hk | | exact I].
  destruct Ht as [Hq Hc]. split; [exact Hq|]. intros z. apply IH; [apply Hc | exact Hk].
Qed.

Definition NM {A} (m : M A) : Prop := forall s, nomm (m s).

Lemma nm_ret {A} (a : A) : NM (ret a).
Proof. intros s. exact I. Qed.

Lemma nm_fail {A} f : NM (@fail A f).
Proof. intros s. exact I. Qed.

Lemma nm_bind {A B} (m : M A) (k : A -> M B) : NM m -> (forall a, NM (k a)) -> NM (bind m k).
Proof. intros Hm Hk s. unfold bind. apply nomm_ibind; [apply Hm|]. intros [a s1]. apply Hk. Qed.

Lemma nm_bind_get {B} (k : astate -> M B) : (forall s0, NM (k s0)) -> NM (bind get k).
Proof. intros Hk s. unfold bind, get. cbn [ibind]. apply Hk. Qed.

Lemma nm_modify f : NM (modify f).
Proof. intros s. exact I. Qed.

Lemma nm_massert b site : NM (massert b site).
Proof. unfold massert. destruct b; [apply nm_ret | apply nm_fail]. Qed.

Lemma nm_mcheck b tag : NM (mcheck b tag).
Proof. unfold mcheck. destruct b; [apply nm_ret | apply nm_fail]. Qed.

Lemma nm_getm p : NM (getm p).
Proof.
  unfold getm. apply nm_bind_get. intros s0. destruct (mlookup (st_metas s0) p) as [[pr nx| |am]|]; try apply nm_fail.
  apply nm_ret.
Qed.

Lemma nm_setm p am : NM (setm p am).
Proof. apply nm_modify. Qed.

Lemma nm_setslot p x : NM (setslot p x).
Proof. apply nm_modify. Qed.

Lemma nm_get_links p : NM (get_links p).
Proof. unfold get_links. apply nm_bind_get. intros s0. destruct (mlookup (st_metas s0) p); [apply nm_ret | apply nm_fail]. Qed.

Lemma nm_set_links p pr nx : NM (set_links p pr nx).
Proof.
  unfold set_links. apply nm_bind_get. intros s0. destruct (mlookup (st_metas s0) p); [apply nm_setslot | apply nm_fail].
Qed.

Lemma nm_set_prev p pr : NM (set_prev p pr).
Proof. unfold set_prev. apply nm_bind; [apply nm_get_links | intros; apply nm_set_links]. Qed.

Lemma nm_set_next p nx : NM (set_next p nx).
Proof. unfold set_next. apply nm_bind; [apply nm_get_links | intros; apply nm_set_links]. Qed.

Lemma nm_get_head h : NM (get_head h).
Proof. unfold get_head. apply nm_bind_get. intros s0. destruct h; apply nm_ret. Qed.

Lemma nm_set_head h v : NM (set_head h v).
Proof. unfold set_head. destruct h; apply nm_modify. Qed.

Lemma nm_queue h m : NM (queue h m).
Proof.
  unfold queue. apply nm_bind; [apply nm_get_links | intros l].
  apply nm_bind; [apply nm_massert | intros _].
  apply nm_bind; [apply nm_get_head | intros [head|]].
  - apply nm_bind; [apply nm_get_links | intros lh]. destruct (fst lh); [| apply nm_fail].
    apply nm_bind; [apply nm_set_links | intros _]. apply nm_bind; [apply nm_set_next | intros _]. apply nm_set_prev.
  - apply nm_bind; [apply nm_set_links | intros _]. apply nm_set_head.
Qed.

Lemma nm_dequeue h m : NM (dequeue h m).
Proof.
  unfold dequeue. apply nm_bind; [apply nm_get_links | intros l].
  apply nm_bind; [| intros _; apply nm_set_links].
  destruct (osptr_eqb (snd l) (Some m)); [apply nm_set_head|].
  destruct (fst l); [| apply nm_fail]. destruct (snd l); [| apply nm_fail].
  apply nm_bind; [apply nm_set_next | intros _]. apply nm_bind; [apply nm_set_prev | intros _].
  apply nm_bind; [apply nm_get_head | intros hd]. destruct (osptr_eqb hd (Some m)); [apply nm_set_head | apply nm_ret].
Qed.

Lemma nm_free_meta m : NM (free_meta m).
Proof. unfold free_meta. apply nm_bind; [apply nm_setslot | intros; apply nm_queue]. Qed.

Lemma nm_activate_group m : NM (activate_group m).
Proof.
  unfold activate_group. apply nm_bind; [apply nm_getm | intros am]. apply nm_bind; [apply nm_massert | intros _].
  cbv zeta. apply nm_bind; [apply nm_setm | intros _]. apply nm_ret.
Qed.

Lemma nm_set_usage_of sc v : NM (set_usage_of sc v).
Proof. apply nm_modify. Qed.

Lemma nm_step_seq : NM step_seq.
Proof. apply nm_modify. Qed.

Lemma nm_record_seq sc : NM (record_seq sc).
Proof. unfold record_seq. destruct (bounce_idx sc); [apply nm_modify | apply nm_ret]. Qed.

Lemma nm_find_frame p : NM (find_frame p).
Proof.
  unfold find_frame. apply nm_bind_get. intros s0. destruct (find_frame_in (st_metas s0) p); [apply nm_ret | apply nm_fail].
Qed.

Lemma nm_forget_frame g i : NM (forget_frame g i).
Proof. unfold forget_frame. apply nm_bind; [apply nm_getm | intros am]. cbv zeta. apply nm_setm. Qed.

Lemma nm_release_slot g i : NM (release_slot g i).
Proof. unfold release_slot. apply nm_bind; [apply nm_getm | intros am]. cbv zeta. apply nm_setm. Qed.

Lemma nm_upd_region r f : NM (upd_region r f).
Proof. apply nm_modify. Qed.

Lemma nm_ask_munmap r len : NM (ask (KMunmap r len)).
Proof. intros s. cbn. split; [reflexivity|]. intros z. exact I. Qed.

Theorem nm_nontrivial_free fuel : forall g i, NM (nontrivial_free fuel g i).
Proof.
  induction fuel as [|fuel IH]; intros g i; [intros s; exact I|].
  cbn fix beta iota delta [nontrivial_free].
  apply nm_bind; [apply nm_getm | intros am].
  apply nm_bind_get. intros s0. cbn zeta.
  destruct ((Z.lor (am_freed am) (am_avail am) + bit i =? ones (am_last am)) && okay_to_free s0 g am).
  - apply nm_bind.
    + destruct (am_next am); [| apply nm_ret].
      apply nm_bind; [apply nm_massert | intros _]. apply nm_bind; [apply nm_get_head | intros hd].
      apply nm_bind; [apply nm_dequeue | intros _]. apply nm_bind; [apply nm_get_head | intros hd'].
      destruct (osptr_eqb hd (Some g)); [| apply nm_ret]. destruct hd'; [| apply nm_ret].
      apply nm_bind; [apply nm_activate_group | intros _; apply nm_ret].
    + intros _. apply nm_bind; [apply nm_getm | intros am'].
      apply nm_bind; [destruct (am_sc am <? 48); [apply nm_set_usage_of | apply nm_ret] | intros _].
      apply nm_bind; [| intros mi; apply nm_bind; [apply nm_free_meta | intros _; apply nm_ret]].
      destruct (negb (am_maplen am' =? 0)).
      * apply nm_bind; [apply nm_step_seq | intros _]. apply nm_bind; [apply nm_record_seq | intros _]. apply nm_ret.
      * apply nm_bind; [apply nm_find_frame | intros pf]. apply nm_bind; [apply nm_getm | intros amp].
        apply nm_bind; [apply nm_mcheck | intros _]. apply nm_bind; [apply nm_forget_frame | intros _]. apply IH.
  - apply nm_bind.
    + destruct (Z.lor (am_freed am) (am_avail am) =? 0); [| apply nm_ret].
      apply nm_bind; [apply nm_massert | intros _]. apply nm_bind; [apply nm_get_head | intros hd].
      destruct (osptr_eqb hd (Some g)); [apply nm_ret | apply nm_queue].
    + intros _. apply nm_bind; [apply nm_getm | intros am']. apply nm_bind; [apply nm_setm | intros _]. apply nm_ret.
Qed.

Theorem nm_free p : NM (free p).
Proof.
  unfold free. destruct p as [p|]; [|apply nm_ret].
  apply nm_bind; [apply nm_find_frame | intros gi]. cbv zeta.
  apply nm_bind; [apply nm_getm | intros am].
  apply nm_bind; [apply nm_release_slot | intros _].
  apply nm_bind; [apply nm_massert | intros _].
  match goal with |- NM (if ?b then _ else _) => destruct b end.
  - apply nm_bind; [apply nm_getm | intros am']. apply nm_setm.
  - apply nm_bind; [apply nm_nontrivial_free | intros mi]. destruct mi as [[r len]|]; [|apply nm_ret].
    apply nm_bind; [apply nm_ask_munmap | intros _]. apply nm_upd_region.
Qed.

Theorem free_cpath04 : forall s p n tr r, WF s -> In (p, n) (user_blocks s) ->
  cpath (free (Some p) s) tr r -> cpath04 (free (Some p) s) tr r.
Proof. intros s p n tr r _ _ H. exact (nomm_cpath04 _ tr r (nm_free (Some p) s) H). Qed.
