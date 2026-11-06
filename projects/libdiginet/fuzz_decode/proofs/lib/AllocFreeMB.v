(* Modified by Theorem Labs, 2026-10: ported from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/AllocFreeMB.v at bf7779f81ed764787b77895d2f5c0db2627f33f3 for libdiginet/fuzz_decode; no image value changed; module path OSSVerify.Proofs.libdiginet.fuzz_decode.lib. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Reusable Require Import YO0i YO0f YO0g YO0s YO0e YO0j YO0m.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib Require Import AllocMB AllocFree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Definition mbstep (rg rg' : region) : Prop := rg' = rg \/ (rg_kind rg' = RkMap /\ rg_live rg' = false).

Definition mbr (s s' : astate) : Prop :=
  st_areas s' = st_areas s /\ st_meta_alloc_shift s' = st_meta_alloc_shift s /\
  Forall2 mbstep (st_regions s) (st_regions s').

Definition MBR {A} (m : M A) : Prop := forall s, tall (fun r => mbr s (snd r)) (m s).

Lemma mbstep_F2_refl l : Forall2 mbstep l l.
Proof. induction l as [|x l IH]; constructor; [left; reflexivity | exact IH]. Qed.

Lemma mbstep_F2_trans l1 l2 l3 : Forall2 mbstep l1 l2 -> Forall2 mbstep l2 l3 -> Forall2 mbstep l1 l3.
Proof.
  intros H12. revert l3. induction H12 as [|x y l1 l2 Hxy H12 IH]; intros l3 H23; inversion H23 as [|y' z l2' l3' Hyz H23']; subst.
  - constructor.
  - constructor; [|exact (IH _ H23')].
    destruct Hyz as [->|Hz]; [exact Hxy | right; exact Hz].
Qed.

Lemma mbstep_F2_lupd l r v : rg_kind v = RkMap -> rg_live v = false -> Forall2 mbstep l (lupd l r v).
Proof.
  intros Hk Hl. revert r. induction l as [|x l IH]; intros [|r]; cbn [lupd]; constructor.
  - right. split; assumption.
  - apply mbstep_F2_refl.
  - left. reflexivity.
  - apply IH.
Qed.

Lemma mbr_refl s : mbr s s.
Proof. split; [reflexivity|]. split; [reflexivity | apply mbstep_F2_refl]. Qed.

Lemma mbr_trans s1 s2 s3 : mbr s1 s2 -> mbr s2 s3 -> mbr s1 s3.
Proof.
  intros (A1 & B1 & C1) (A2 & B2 & C2). split; [congruence|]. split; [congruence|]. eapply mbstep_F2_trans; eauto.
Qed.

Lemma mbr_same s s' : st_regions s' = st_regions s -> st_areas s' = st_areas s ->
  st_meta_alloc_shift s' = st_meta_alloc_shift s -> mbr s s'.
Proof. intros Er Ea Es. split; [exact Ea|]. split; [exact Es|]. rewrite Er. apply mbstep_F2_refl. Qed.

Lemma mbr_upd s p x : mbr s (upd_meta p x s).
Proof. apply mbr_same; reflexivity. Qed.

Lemma mb_ret {A} (a : A) : MBR (ret a).
Proof. intros s. exact (mbr_refl s). Qed.

Lemma mb_fail {A} f : MBR (@fail A f).
Proof. intros s. exact I. Qed.

Lemma mb_bind {A B} (m : M A) (k : A -> M B) : MBR m -> (forall a, MBR (k a)) -> MBR (bind m k).
Proof.
  intros Hm Hk s. unfold bind. eapply tall_ibind; [apply Hm|]. intros [a s1] H1. cbn [snd] in *.
  eapply tall_mono; [|apply (Hk a s1)]. intros [b s2] H2. cbn [snd] in *. eapply mbr_trans; eauto.
Qed.

Lemma mb_bind_get {B} (k : astate -> M B) : (forall s0, MBR (k s0)) -> MBR (bind get k).
Proof. intros Hk s. unfold bind, get. cbn [ibind]. apply Hk. Qed.

Lemma mb_modify f : (forall s, mbr s (f s)) -> MBR (modify f).
Proof. intros Hf s. exact (Hf s). Qed.

Lemma mb_massert b site : MBR (massert b site).
Proof. unfold massert. destruct b; [apply mb_ret | apply mb_fail]. Qed.

Lemma mb_mcheck b tag : MBR (mcheck b tag).
Proof. unfold mcheck. destruct b; [apply mb_ret | apply mb_fail]. Qed.

Lemma mb_getm p : MBR (getm p).
Proof.
  unfold getm. apply mb_bind_get. intros s0. destruct (mlookup (st_metas s0) p) as [[pr nx| |am]|]; try apply mb_fail.
  apply mb_ret.
Qed.

Lemma mb_setm p am : MBR (setm p am).
Proof. intros s. exact (mbr_upd s p (MUsed am)). Qed.

Lemma mb_setslot p x : MBR (setslot p x).
Proof. intros s. exact (mbr_upd s p x). Qed.

Lemma mb_get_links p : MBR (get_links p).
Proof. unfold get_links. apply mb_bind_get. intros s0. destruct (mlookup (st_metas s0) p); [apply mb_ret | apply mb_fail]. Qed.

Lemma mb_set_links p pr nx : MBR (set_links p pr nx).
Proof.
  unfold set_links. apply mb_bind_get. intros s0. destruct (mlookup (st_metas s0) p) as [x|]; [apply mb_setslot | apply mb_fail].
Qed.

Lemma mb_set_prev p pr : MBR (set_prev p pr).
Proof. unfold set_prev. apply mb_bind; [apply mb_get_links | intros; apply mb_set_links]. Qed.

Lemma mb_set_next p nx : MBR (set_next p nx).
Proof. unfold set_next. apply mb_bind; [apply mb_get_links | intros; apply mb_set_links]. Qed.

Lemma mb_get_head h : MBR (get_head h).
Proof. unfold get_head. apply mb_bind_get. intros s0. destruct h; apply mb_ret. Qed.

Lemma mb_set_head h v : MBR (set_head h v).
Proof. unfold set_head. destruct h; apply mb_modify; intros s; apply mbr_same; reflexivity. Qed.

Lemma mb_queue h m : MBR (queue h m).
Proof.
  unfold queue. apply mb_bind; [apply mb_get_links | intros l].
  apply mb_bind; [apply mb_massert | intros _].
  apply mb_bind; [apply mb_get_head | intros [head|]].
  - apply mb_bind; [apply mb_get_links | intros lh]. destruct (fst lh); [| apply mb_fail].
    apply mb_bind; [apply mb_set_links | intros _]. apply mb_bind; [apply mb_set_next | intros _]. apply mb_set_prev.
  - apply mb_bind; [apply mb_set_links | intros _]. apply mb_set_head.
Qed.

Lemma mb_dequeue h m : MBR (dequeue h m).
Proof.
  unfold dequeue. apply mb_bind; [apply mb_get_links | intros l].
  apply mb_bind; [| intros _; apply mb_set_links].
  destruct (osptr_eqb (snd l) (Some m)); [apply mb_set_head|].
  destruct (fst l); [| apply mb_fail]. destruct (snd l); [| apply mb_fail].
  apply mb_bind; [apply mb_set_next | intros _]. apply mb_bind; [apply mb_set_prev | intros _].
  apply mb_bind; [apply mb_get_head | intros hd]. destruct (osptr_eqb hd (Some m)); [apply mb_set_head | apply mb_ret].
Qed.

Lemma mb_free_meta m : MBR (free_meta m).
Proof. unfold free_meta. apply mb_bind; [apply mb_setslot | intros; apply mb_queue]. Qed.

Lemma mb_activate_group m : MBR (activate_group m).
Proof.
  unfold activate_group. apply mb_bind; [apply mb_getm | intros am]. apply mb_bind; [apply mb_massert | intros _].
  cbv zeta. apply mb_bind; [apply mb_setm | intros _]. apply mb_ret.
Qed.

Lemma mb_set_usage_of sc v : MBR (set_usage_of sc v).
Proof. unfold set_usage_of. apply mb_modify. intros s. apply mbr_same; reflexivity. Qed.

Lemma mb_step_seq : MBR step_seq.
Proof. unfold step_seq. apply mb_modify. intros s. destruct (st_seq s =? 255); apply mbr_same; reflexivity. Qed.

Lemma mb_record_seq sc : MBR (record_seq sc).
Proof.
  unfold record_seq. destruct (bounce_idx sc); [apply mb_modify; intros s; apply mbr_same; reflexivity | apply mb_ret].
Qed.

Lemma mb_find_frame p : MBR (find_frame p).
Proof.
  unfold find_frame. apply mb_bind_get. intros s0. destruct (find_frame_in (st_metas s0) p); [apply mb_ret | apply mb_fail].
Qed.

Lemma mb_forget_frame g i : MBR (forget_frame g i).
Proof. unfold forget_frame. apply mb_bind; [apply mb_getm | intros am]. cbv zeta. apply mb_setm. Qed.

Lemma mb_release_slot g i : MBR (release_slot g i).
Proof. unfold release_slot. apply mb_bind; [apply mb_getm | intros am]. cbv zeta. apply mb_setm. Qed.

Lemma mb_ask q : MBR (ask q).
Proof. intros s z. exact (mbr_refl s). Qed.

Lemma mb_upd_region_kill r : MBR (upd_region r (fun rg => mkRegion RkMap (rg_len rg) [] false)).
Proof.
  unfold upd_region. apply mb_modify. intros s. split; [reflexivity|]. split; [reflexivity|].
  cbn [st_regions set_regions]. apply mbstep_F2_lupd; reflexivity.
Qed.

Theorem mb_nontrivial_free fuel : forall g i, MBR (nontrivial_free fuel g i).
Proof.
  induction fuel as [|fuel IH]; intros g i; [intros s; exact I|].
  cbn fix beta iota delta [nontrivial_free].
  apply mb_bind; [apply mb_getm | intros am].
  apply mb_bind_get. intros s0. cbn zeta.
  destruct ((Z.lor (am_freed am) (am_avail am) + bit i =? ones (am_last am)) && okay_to_free s0 g am).
  - apply mb_bind.
    + destruct (am_next am); [| apply mb_ret].
      apply mb_bind; [apply mb_massert | intros _]. apply mb_bind; [apply mb_get_head | intros hd].
      apply mb_bind; [apply mb_dequeue | intros _]. apply mb_bind; [apply mb_get_head | intros hd'].
      destruct (osptr_eqb hd (Some g)); [| apply mb_ret]. destruct hd'; [| apply mb_ret].
      apply mb_bind; [apply mb_activate_group | intros _; apply mb_ret].
    + intros _. apply mb_bind; [apply mb_getm | intros am'].
      apply mb_bind; [destruct (am_sc am <? 48); [apply mb_set_usage_of | apply mb_ret] | intros _].
      apply mb_bind; [| intros mi; apply mb_bind; [apply mb_free_meta | intros _; apply mb_ret]].
      destruct (negb (am_maplen am' =? 0)).
      * apply mb_bind; [apply mb_step_seq | intros _]. apply mb_bind; [apply mb_record_seq | intros _]. apply mb_ret.
      * apply mb_bind; [apply mb_find_frame | intros pf]. apply mb_bind; [apply mb_getm | intros amp].
        apply mb_bind; [apply mb_mcheck | intros _]. apply mb_bind; [apply mb_forget_frame | intros _]. apply IH.
  - apply mb_bind.
    + destruct (Z.lor (am_freed am) (am_avail am) =? 0); [| apply mb_ret].
      apply mb_bind; [apply mb_massert | intros _]. apply mb_bind; [apply mb_get_head | intros hd].
      destruct (osptr_eqb hd (Some g)); [apply mb_ret | apply mb_queue].
    + intros _. apply mb_bind; [apply mb_getm | intros am']. apply mb_bind; [apply mb_setm | intros _]. apply mb_ret.
Qed.

Theorem mb_free p : MBR (free p).
Proof.
  unfold free. destruct p as [p|]; [|apply mb_ret].
  apply mb_bind; [apply mb_find_frame | intros gi]. cbv zeta.
  apply mb_bind; [apply mb_getm | intros am].
  apply mb_bind; [apply mb_release_slot | intros _].
  apply mb_bind; [apply mb_massert | intros _].
  match goal with |- MBR (if ?b then _ else _) => destruct b end.
  - apply mb_bind; [apply mb_getm | intros am']. apply mb_setm.
  - apply mb_bind; [apply mb_nontrivial_free | intros mi]. destruct mi as [[r len]|]; [|apply mb_ret].
    apply mb_bind; [apply mb_ask | intros _]. apply mb_upd_region_kill.
Qed.

Lemma rsum_mbstep f l l' : Forall2 mbstep l l' ->
  (forall rg', rg_kind rg' = RkMap -> rg_live rg' = false -> f rg' = 0) ->
  (forall rg, In rg l -> 0 <= f rg) -> rsum f l' <= rsum f l.
Proof.
  intros H Hz Hn. induction H as [|x y l l' Hxy H IH]; [rewrite !rsum_nil; lia|].
  rewrite !rsum_cons. assert (rsum f l' <= rsum f l) by (apply IH; intros rg Hr; apply Hn; right; exact Hr).
  destruct Hxy as [->|[Hk Hl]]; [lia|]. rewrite (Hz y Hk Hl). pose proof (Hn x (or_introl eq_refl)). lia.
Qed.

Theorem free_MB : forall s p n tr s', WF s -> MB s -> In (p, n) (user_blocks s) ->
  yields (free (Some p) s) tr (tt, s') -> MB s'.
Proof.
  intros s p n tr s' HW (Hb & Hr) _ Y. pose proof (tall_yields _ _ tr (tt, s') (mb_free (Some p) s) Y) as (Ea & Es & F).
  cbn [snd] in Ea, Es, F. pose proof (regs_nn_wf s HW) as NN.
  assert (Lb : brk_bytes s' <= brk_bytes s).
  { unfold brk_bytes. apply (rsum_mbstep _ _ _ F).
    - intros rg' Hk Hl. unfold f_brkb. rewrite Hl. reflexivity.
    - intros rg Hin. unfold f_brkb. destruct (rg_live rg && is_brk rg); [exact (NN rg Hin) | lia]. }
  assert (Lr : resv_count s' <= resv_count s).
  { unfold resv_count. apply (rsum_mbstep _ _ _ F).
    - intros rg' Hk Hl. unfold f_resvc, is_resv. rewrite Hk. reflexivity.
    - intros rg Hin. unfold f_resvc. destruct (is_resv rg); lia. }
  unfold MB, nareas, shift in *. rewrite Ea, Es. split; lia.
Qed.
