From Stdlib Require Import ZArith List Bool Lia Arith.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YO0i YO0f YO0g YO0h YO0w YO0s YO11 YO15 YO12 YO0z YO14 YO0u YO0q YO0v YO0t YO0e YO0m YO0x YO03 YO0p.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import AllocSI AllocGS AllocRealloc AllocPack.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require AllocFree AllocMalloc AllocBound.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Definition pkm (s s' : astate) : Prop :=
  forall q a', MT s' q = Some (MUsed a') -> exists a, MT s q = Some (MUsed a) /\ am_mem a' = am_mem a.

Definition PKM {A} (m : M A) : Prop := forall s, tall (fun r => pkm s (snd r)) (m s).

Lemma pkm_refl s : pkm s s.
Proof. intros q a H. exists a. split; [exact H | reflexivity]. Qed.

Lemma pkm_trans s1 s2 s3 : pkm s1 s2 -> pkm s2 s3 -> pkm s1 s3.
Proof.
  intros A B q a H. destruct (B q a H) as (a1 & H1 & E1). destruct (A q a1 H1) as (a0 & H0 & E0).
  exists a0. split; [exact H0 | congruence].
Qed.

Lemma pkm_same s s' : st_metas s' = st_metas s -> pkm s s'.
Proof. intros E q a H. unfold MT in H. rewrite E in H. exists a. split; [exact H | reflexivity]. Qed.

Lemma pkm_upd_free s p x : (forall a, x <> MUsed a) -> pkm s (upd_meta p x s).
Proof.
  intros Hu q a H. rewrite MT_upd in H. destruct (sptr_eqb q p).
  - injection H as E. exfalso. exact (Hu a E).
  - exists a. split; [exact H | reflexivity].
Qed.

Lemma pkm_upd_used s p a a' : MT s p = Some (MUsed a) -> am_mem a' = am_mem a -> pkm s (upd_meta p (MUsed a') s).
Proof.
  intros Hp E q b H. rewrite MT_upd in H. destruct (sptr_eqb q p) eqn:Eq.
  - apply sptr_eqb_eq in Eq. subst q. injection H as <-. exists a. split; [exact Hp | exact E].
  - exists b. split; [exact H | reflexivity].
Qed.

Lemma pk_mfree pr nx a : MFree pr nx <> MUsed a.
Proof. discriminate. Qed.

Lemma pk_setm p am s : setm p am s = IRet (tt, upd_meta p (MUsed am) s).
Proof. reflexivity. Qed.

Lemma pkm_ret {A} (a : A) : PKM (ret a).
Proof. intros s. exact (pkm_refl s). Qed.

Lemma pkm_fail {A} f : PKM (@fail A f).
Proof. intros s. exact I. Qed.

Lemma pkm_bind {A B} (m : M A) (k : A -> M B) : PKM m -> (forall a, PKM (k a)) -> PKM (bind m k).
Proof.
  intros Hm Hk s. unfold bind. eapply tall_ibind; [apply Hm|]. intros [a s1] H1. cbn [snd] in *.
  eapply tall_mono; [|apply (Hk a s1)]. intros [b s2] H2. cbn [snd] in *. eapply pkm_trans; eauto.
Qed.

Lemma pkm_bind_get {B} (k : astate -> M B) : (forall s0, PKM (k s0)) -> PKM (bind get k).
Proof. intros Hk s. unfold bind, get. cbn [ibind]. apply Hk. Qed.

Lemma pkm_bind_get' {B} (k : astate -> M B) : (forall s, tall (fun r => pkm s (snd r)) (k s s)) -> PKM (bind get k).
Proof. intros Hk s. exact (Hk s). Qed.

Lemma pkm_modify f : (forall s, pkm s (f s)) -> PKM (modify f).
Proof. intros Hf s. exact (Hf s). Qed.

Lemma pkm_massert b site : PKM (massert b site).
Proof. unfold massert. destruct b; [apply pkm_ret | apply pkm_fail]. Qed.

Lemma pkm_mcheck b tag : PKM (mcheck b tag).
Proof. unfold mcheck. destruct b; [apply pkm_ret | apply pkm_fail]. Qed.

Lemma pkm_getm p : PKM (getm p).
Proof.
  unfold getm. apply pkm_bind_get. intros s0. destruct (mlookup (st_metas s0) p) as [[pr nx| |am]|]; try apply pkm_fail.
  apply pkm_ret.
Qed.

Lemma pkm_get_links p : PKM (get_links p).
Proof. unfold get_links. apply pkm_bind_get. intros s0. destruct (mlookup (st_metas s0) p); [apply pkm_ret | apply pkm_fail]. Qed.

Lemma pkm_set_links p pr nx : PKM (set_links p pr nx).
Proof.
  unfold set_links. apply pkm_bind_get'. intros s. destruct (mlookup (st_metas s) p) as [x|] eqn:E; [|exact I].
  destruct x as [pr0 nx0| |am].
  - exact (pkm_upd_free s p (MFree pr nx) (pk_mfree pr nx)).
  - exact (pkm_upd_free s p (MFree pr nx) (pk_mfree pr nx)).
  - exact (pkm_upd_used s p am (am_set_links pr nx am) E eq_refl).
Qed.

Lemma pkm_set_prev p pr : PKM (set_prev p pr).
Proof. unfold set_prev. apply pkm_bind; [apply pkm_get_links | intros; apply pkm_set_links]. Qed.

Lemma pkm_set_next p nx : PKM (set_next p nx).
Proof. unfold set_next. apply pkm_bind; [apply pkm_get_links | intros; apply pkm_set_links]. Qed.

Lemma pkm_get_head h : PKM (get_head h).
Proof. unfold get_head. apply pkm_bind_get. intros s0. destruct h; apply pkm_ret. Qed.

Lemma pkm_set_head h v : PKM (set_head h v).
Proof. unfold set_head. destruct h; apply pkm_modify; intros s; apply pkm_same; reflexivity. Qed.

Lemma pkm_queue h m : PKM (queue h m).
Proof.
  unfold queue. apply pkm_bind; [apply pkm_get_links | intros l].
  apply pkm_bind; [apply pkm_massert | intros _].
  apply pkm_bind; [apply pkm_get_head | intros [head|]].
  - apply pkm_bind; [apply pkm_get_links | intros lh]. destruct (fst lh); [| apply pkm_fail].
    apply pkm_bind; [apply pkm_set_links | intros _]. apply pkm_bind; [apply pkm_set_next | intros _]. apply pkm_set_prev.
  - apply pkm_bind; [apply pkm_set_links | intros _]. apply pkm_set_head.
Qed.

Lemma pkm_dequeue h m : PKM (dequeue h m).
Proof.
  unfold dequeue. apply pkm_bind; [apply pkm_get_links | intros l].
  apply pkm_bind; [| intros _; apply pkm_set_links].
  destruct (osptr_eqb (snd l) (Some m)); [apply pkm_set_head|].
  destruct (fst l); [| apply pkm_fail]. destruct (snd l); [| apply pkm_fail].
  apply pkm_bind; [apply pkm_set_next | intros _]. apply pkm_bind; [apply pkm_set_prev | intros _].
  apply pkm_bind; [apply pkm_get_head | intros hd]. destruct (osptr_eqb hd (Some m)); [apply pkm_set_head | apply pkm_ret].
Qed.

Lemma pkm_free_meta m : PKM (free_meta m).
Proof.
  unfold free_meta. apply pkm_bind; [|intros; apply pkm_queue].
  intros s. exact (pkm_upd_free s m (MFree None None) (pk_mfree None None)).
Qed.

Lemma pkm_activate_group m : PKM (activate_group m).
Proof.
  intros s. unfold activate_group, getm, bind, get, ret, fail. cbn [ibind].
  destruct (mlookup (st_metas s) m) as [[| |am]|] eqn:E; cbn [ibind]; try exact I.
  unfold massert, ret, fail. destruct (am_avail am =? 0); cbn [ibind]; [| exact I].
  cbv zeta. rewrite pk_setm. cbn [ibind tall snd].
  eapply pkm_upd_used; [exact E | reflexivity].
Qed.

Lemma pkm_set_usage_of sc v : PKM (set_usage_of sc v).
Proof. unfold set_usage_of. apply pkm_modify. intros s. apply pkm_same; reflexivity. Qed.

Lemma pkm_step_seq : PKM step_seq.
Proof. unfold step_seq. apply pkm_modify. intros s. destruct (st_seq s =? 255); apply pkm_same; reflexivity. Qed.

Lemma pkm_record_seq sc : PKM (record_seq sc).
Proof.
  unfold record_seq. destruct (bounce_idx sc); [apply pkm_modify; intros s; apply pkm_same; reflexivity | apply pkm_ret].
Qed.

Lemma pkm_find_frame p : PKM (find_frame p).
Proof.
  unfold find_frame. apply pkm_bind_get. intros s0. destruct (find_frame_in (st_metas s0) p); [apply pkm_ret | apply pkm_fail].
Qed.

Lemma pkm_getm_setm p (F : ameta -> ameta) :
  (forall am, am_mem (F am) = am_mem am) -> PKM (bind (getm p) (fun am => setm p (F am))).
Proof.
  intros HF s. unfold getm, bind, get, ret, fail. cbn [ibind].
  destruct (mlookup (st_metas s) p) as [[| |am]|] eqn:E; cbn [ibind]; try exact I.
  exact (pkm_upd_used s p am (F am) E (HF am)).
Qed.

Lemma pkm_getm_setm_k {B} p (F : ameta -> ameta) (k : ameta -> unit -> M B) :
  (forall am, am_mem (F am) = am_mem am) -> (forall am u, PKM (k am u)) ->
  PKM (bind (getm p) (fun am => bind (setm p (F am)) (k am))).
Proof.
  intros HF Hk s. unfold getm, bind, get, ret, fail. cbn [ibind].
  destruct (mlookup (st_metas s) p) as [[| |am]|] eqn:E; cbn [ibind]; try exact I.
  rewrite pk_setm. cbn [ibind].
  eapply tall_mono; [|apply (Hk am tt)]. intros [b s2] H2. cbn [snd] in *. eapply pkm_trans; [|exact H2].
  exact (pkm_upd_used s p am (F am) E (HF am)).
Qed.

Lemma pkm_forget_frame g i : PKM (forget_frame g i).
Proof. unfold forget_frame. cbv zeta. apply pkm_getm_setm. intros am. reflexivity. Qed.

Lemma pkm_release_slot g i : PKM (release_slot g i).
Proof. unfold release_slot. cbv zeta. apply pkm_getm_setm. intros am. reflexivity. Qed.

Lemma pkm_upd_region r f : PKM (upd_region r f).
Proof. unfold upd_region. apply pkm_modify. intros s. apply pkm_same; reflexivity. Qed.

Lemma pkm_ask q : PKM (ask q).
Proof. intros s z. exact (pkm_refl s). Qed.

Theorem pkm_nontrivial_free fuel : forall g i, PKM (nontrivial_free fuel g i).
Proof.
  induction fuel as [|fuel IH]; intros g i; [intros s; exact I|].
  cbn fix beta iota delta [nontrivial_free].
  apply pkm_bind; [apply pkm_getm | intros am].
  apply pkm_bind_get. intros s0. cbn zeta.
  destruct ((Z.lor (am_freed am) (am_avail am) + bit i =? ones (am_last am)) && okay_to_free s0 g am).
  - apply pkm_bind.
    + destruct (am_next am); [| apply pkm_ret].
      apply pkm_bind; [apply pkm_massert | intros _]. apply pkm_bind; [apply pkm_get_head | intros hd].
      apply pkm_bind; [apply pkm_dequeue | intros _]. apply pkm_bind; [apply pkm_get_head | intros hd'].
      destruct (osptr_eqb hd (Some g)); [| apply pkm_ret]. destruct hd'; [| apply pkm_ret].
      apply pkm_bind; [apply pkm_activate_group | intros _; apply pkm_ret].
    + intros _. apply pkm_bind; [apply pkm_getm | intros am'].
      apply pkm_bind; [destruct (am_sc am <? 48); [apply pkm_set_usage_of | apply pkm_ret] | intros _].
      apply pkm_bind; [| intros mi; apply pkm_bind; [apply pkm_free_meta | intros _; apply pkm_ret]].
      destruct (negb (am_maplen am' =? 0)).
      * apply pkm_bind; [apply pkm_step_seq | intros _]. apply pkm_bind; [apply pkm_record_seq | intros _]. apply pkm_ret.
      * apply pkm_bind; [apply pkm_find_frame | intros pf]. apply pkm_bind; [apply pkm_getm | intros amp].
        apply pkm_bind; [apply pkm_mcheck | intros _]. apply pkm_bind; [apply pkm_forget_frame | intros _]. apply IH.
  - apply pkm_bind.
    + destruct (Z.lor (am_freed am) (am_avail am) =? 0); [| apply pkm_ret].
      apply pkm_bind; [apply pkm_massert | intros _]. apply pkm_bind; [apply pkm_get_head | intros hd].
      destruct (osptr_eqb hd (Some g)); [apply pkm_ret | apply pkm_queue].
    + intros _. apply (pkm_getm_setm_k g (fun am' => am_set_freed (Z.lor (am_freed am') (bit i)) am') (fun _ _ => ret None)).
      * intros am'. reflexivity.
      * intros _ _. apply pkm_ret.
Qed.

Theorem pkm_free p : PKM (free p).
Proof.
  unfold free. destruct p as [p|]; [|apply pkm_ret].
  apply pkm_bind; [apply pkm_find_frame | intros gi]. cbv zeta.
  apply pkm_bind; [apply pkm_getm | intros am].
  apply pkm_bind; [apply pkm_release_slot | intros _].
  apply pkm_bind; [apply pkm_massert | intros _].
  match goal with |- PKM (if ?b then _ else _) => destruct b end.
  - apply pkm_getm_setm. intros am'. reflexivity.
  - apply pkm_bind; [apply pkm_nontrivial_free | intros mi]. destruct mi as [[r len]|]; [|apply pkm_ret].
    apply pkm_bind; [apply pkm_ask | intros _]. apply pkm_upd_region.
Qed.

Lemma free_rel s p tr s' : yields (free (Some p) s) tr (tt, s') ->
  forall q a', MT s' q = Some (MUsed a') -> exists a, MT s q = Some (MUsed a) /\
  am_mem a' = am_mem a /\ am_maplen a' = am_maplen a /\ am_sc a' = am_sc a /\ am_last a' = am_last a /\
  AllocFree.af_frs a a'.
Proof.
  intros Y q a' H.
  pose proof (tall_yields _ _ tr (tt, s') (AllocFree.kr_free (Some p) s) Y) as (_ & _ & _ & Mc).
  pose proof (tall_yields _ _ tr (tt, s') (pkm_free (Some p) s) Y) as Mm.
  destruct (Mc q a' H) as (a & Ha & L & S & T & F). destruct (Mm q a' H) as (b & Hb & E).
  rewrite Ha in Hb. injection Hb as <-. exists a.
  split; [exact Ha|]. split; [exact E|]. split; [exact L|]. split; [exact S|]. split; [exact T | exact F].
Qed.

Definition pk_shp (a a' : ameta) : Prop :=
  am_mem a' = am_mem a /\ am_maplen a' = am_maplen a /\ am_sc a' = am_sc a /\ am_last a' = am_last a.

Lemma pk_shp_stride a a' : pk_shp a a' -> stride_of a' = stride_of a.
Proof. intros (M & L & S & T). unfold stride_of. rewrite L, S, T. reflexivity. Qed.

Lemma pk_shp_slot_start a a' j : pk_shp a a' -> slot_start a' j = slot_start a j.
Proof. intros H. unfold slot_start. rewrite (pk_shp_stride _ _ H). destruct H as (M & _). rewrite M. reflexivity. Qed.

Definition pk_frel (a a' : ameta) : Prop :=
  forall j f, 0 <= j <= am_last a -> ss_fr (nth_slot a' j) = Some f ->
  ss_fr (nth_slot a j) = Some f \/
  (fr_kind f = FUser /\ (am_sc a < 48 -> fr_n f < MMAP_THRESHOLD /\ am_sc a <= size_to_class (fr_n f) + 1)).

Lemma PKS_tr s s' : PKS [] s ->
  (forall q a', usedX [] s' q a' ->
     (exists a, usedX [] s q a /\ pk_shp a a' /\ pk_frel a a') \/
     (am_sc a' = 63 /\ 0 < am_maplen a' /\
      forall j f, 0 <= j <= am_last a' -> ss_fr (nth_slot a' j) = Some f -> fr_kind f = FUser)) ->
  PKS [] s'.
Proof.
  intros (P1 & P2 & P3 & P4) H. split; [|split; [|split]].
  - intros g am i fr Hu Hsc Hi Hf Hk.
    destruct (H g am Hu) as [(a & Ha & (M & L & S & T) & F) | (E & _)]; [|lia].
    rewrite S in Hsc |- *. rewrite T in Hi.
    destruct (F i fr Hi Hf) as [Hf0 | (_ & B)]; [exact (P1 g a i fr Ha Hsc Hi Hf0 Hk) | exact (B Hsc)].
  - intros g am i fr c ac Hu Hi Hf Hk Hc Hm Hmem.
    destruct (H g am Hu) as [(a & Ha & Sa & F) | (_ & _ & Hall)]; [|rewrite (Hall i fr Hi Hf) in Hk; discriminate].
    destruct (H c ac Hc) as [(b & Hb & Sb & _) | (_ & Hml & _)]; [|lia].
    pose proof Sa as (Ma & La & Sca & Ta). pose proof Sb as (Mb & Lb & Scb & Tb).
    rewrite Ta in Hi.
    destruct (F i fr Hi Hf) as [Hf0 | (Hu' & _)]; [|rewrite Hu' in Hk; discriminate].
    rewrite Sca, Scb, Tb.
    apply (P2 g a i fr c b Ha Hi Hf0 Hk Hb); [lia|].
    rewrite <- Mb, Hmem. apply pk_shp_slot_start. exact Sa.
  - intros g am Hu Hsc. destruct (H g am Hu) as [(a & Ha & (M & L & S & T) & _) | (E & _)]; [|lia].
    rewrite S in Hsc |- *. rewrite T. exact (P3 g a Ha Hsc).
  - intros g am Hu Hsc Hml. destruct (H g am Hu) as [(a & Ha & (M & L & S & T) & _) | (E & _)]; [|lia].
    rewrite S in Hsc |- *. rewrite L in Hml. exact (P4 g a Ha Hsc Hml).
Qed.

Fixpoint pk_sum {A} (f : A -> nat) (l : list A) : nat :=
  match l with [] => 0%nat | x :: t => (f x + pk_sum f t)%nat end.

Lemma pk_sum_ext {A} (f' f : A -> nat) l : (forall y, In y l -> f' y = f y) -> pk_sum f' l = pk_sum f l.
Proof.
  induction l as [|y l IH]; intros H; cbn [pk_sum]; [reflexivity|].
  rewrite (H y (or_introl eq_refl)), IH; [reflexivity|]. intros z Hz. apply H. right. exact Hz.
Qed.

Lemma pk_sum_mono {A} (f' f : A -> nat) l : (forall y, In y l -> (f' y <= f y)%nat) -> (pk_sum f' l <= pk_sum f l)%nat.
Proof.
  induction l as [|y l IH]; intros H; cbn [pk_sum]; [lia|].
  pose proof (H y (or_introl eq_refl)). enough (pk_sum f' l <= pk_sum f l)%nat by lia.
  apply IH. intros z Hz. apply H. right. exact Hz.
Qed.

Lemma pk_nodup_rm {A} (dec : forall x y : A, {x = y} + {x <> y}) x l : NoDup l -> NoDup (remove dec x l).
Proof.
  induction l as [|y l IH]; intros ND; cbn [remove]; [constructor|].
  apply NoDup_cons_iff in ND as [Hy ND]. destruct (dec x y); cbv beta iota; [exact (IH ND)|].
  constructor; [|exact (IH ND)]. intros Hin. apply in_remove in Hin as [Hin _]. exact (Hy Hin).
Qed.

Lemma pk_sum_remove {A} (dec : forall x y : A, {x = y} + {x <> y}) (f : A -> nat) l x :
  NoDup l -> In x l -> pk_sum f l = (f x + pk_sum f (remove dec x l))%nat.
Proof.
  induction l as [|y l IH]; intros ND Hx; [destruct Hx|].
  apply NoDup_cons_iff in ND as [Hy ND]. cbn [pk_sum remove].
  destruct (dec x y) as [E|Ne]; cbn [pk_sum].
  - subst y. rewrite notin_remove by exact Hy. reflexivity.
  - destruct Hx as [E|Hx]; [congruence|]. rewrite (IH ND Hx). lia.
Qed.

Lemma pk_sum_le {A} (dec : forall x y : A, {x = y} + {x <> y}) (f' f : A -> nat) : forall l' l,
  NoDup l' -> NoDup l ->
  (forall x, In x l' -> f' x <> 0%nat -> In x l /\ (f' x <= f x)%nat) ->
  (pk_sum f' l' <= pk_sum f l)%nat.
Proof.
  induction l' as [|x t IH]; intros l ND' ND H; cbn [pk_sum]; [lia|].
  apply NoDup_cons_iff in ND' as [Hx ND'].
  destruct (Nat.eq_dec (f' x) 0) as [Hz0|NZ].
  - rewrite Hz0. cbn [Nat.add]. apply IH; [exact ND' | exact ND |]. intros y Hy. apply H. right. exact Hy.
  - destruct (H x (or_introl eq_refl) NZ) as [Hin Hle].
    rewrite (pk_sum_remove dec f l x ND Hin).
    enough (pk_sum f' t <= pk_sum f (remove dec x l))%nat by lia.
    apply IH; [exact ND' | apply pk_nodup_rm; exact ND |].
    intros y Hy Hny. destruct (H y (or_intror Hy) Hny) as [Hiy Hley]. split; [|exact Hley].
    apply in_in_remove; [intros E; subst y; exact (Hx Hy) | exact Hiy].
Qed.

Lemma pk_sum_upd {A} (dec : forall x y : A, {x = y} + {x <> y}) (f' f : A -> nat) l x :
  NoDup l -> In x l -> (forall y, In y l -> y <> x -> f' y = f y) ->
  (pk_sum f' l + f x = pk_sum f l + f' x)%nat.
Proof.
  intros ND Hx H. rewrite (pk_sum_remove dec f' l x ND Hx), (pk_sum_remove dec f l x ND Hx).
  assert (E : pk_sum f' (remove dec x l) = pk_sum f (remove dec x l)).
  { apply pk_sum_ext. intros y Hy. apply in_remove in Hy as [Hy Ne]. exact (H y Hy Ne). }
  lia.
Qed.

Lemma pk_len_filter_flat {A B} (P : B -> bool) (h : A -> list B) l :
  length (filter P (flat_map h l)) = pk_sum (fun x => length (filter P (h x))) l.
Proof. induction l as [|x l IH]; cbn [flat_map pk_sum]; [reflexivity|]. rewrite filter_app, length_app, IH. reflexivity. Qed.

Lemma pk_len_filter {A} (P : A -> bool) l : length (filter P l) = pk_sum (fun x => if P x then 1%nat else 0%nat) l.
Proof. induction l as [|x l IH]; cbn [filter pk_sum]; [reflexivity|]. destruct (P x); cbn [length]; rewrite IH; reflexivity. Qed.

Lemma pk_fm_cons {A B} (f : A -> list B) a l : flat_map f (a :: l) = f a ++ flat_map f l.
Proof. reflexivity. Qed.

Lemma pk_um_keys {B} (H : ameta -> list B) s : NoDup (keys s) ->
  flat_map (fun gm : sptr * ameta => H (snd gm)) (used_metas s) =
  flat_map (fun g => match MT s g with Some (MUsed am) => H am | _ => [] end) (keys s).
Proof.
  unfold used_metas, keys, MT. generalize (st_metas s) as l. clear s.
  induction l as [|[p x] t IH]; intros ND; [reflexivity|].
  change (NoDup (p :: map fst t)) in ND. apply NoDup_cons_iff in ND as [Hp Ht].
  assert (E : flat_map (fun g => match mlookup ((p, x) :: t) g with Some (MUsed am) => H am | _ => [] end) (map fst t) =
              flat_map (fun g => match mlookup t g with Some (MUsed am) => H am | _ => [] end) (map fst t)).
  { apply flat_map_ext_In. intros g Hg. cbn [mlookup]. destruct (sptr_eqb g p) eqn:Eg; [|reflexivity].
    apply sptr_eqb_eq in Eg. subst g. exfalso. exact (Hp Hg). }
  change (map fst ((p, x) :: t)) with (p :: map fst t).
  rewrite !pk_fm_cons, flat_map_app, E, <- (IH Ht).
  cbn [mlookup]. rewrite sptr_eqb_refl. destruct x as [pr nx| |am]; cbn; rewrite ?app_nil_r; reflexivity.
Qed.

Definition pk_ublk (c : Z) (am : ameta) : list (sptr * Z) :=
  if (am_sc am =? c) && (1 <=? am_last am) then blocks_of0 am else [].

Definition pk_ucnt (c : Z) (x : option mslot) : nat :=
  match x with
  | Some (MUsed am) => length (filter (fun b : sptr * Z => band (snd b) =? c - 1) (pk_ublk c am))
  | _ => 0%nat
  end.

Lemma upc_sum s c : NoDup (keys s) -> upc s c = Z.of_nat (pk_sum (fun g => pk_ucnt c (MT s g)) (keys s)).
Proof.
  intros N. unfold upc.
  change (ub_cls s c) with (flat_map (fun gm : sptr * ameta => pk_ublk c (snd gm)) (used_metas s)).
  rewrite (pk_um_keys (pk_ublk c) s N), pk_len_filter_flat. f_equal. apply pk_sum_ext.
  intros g _. cbv beta. destruct (MT s g) as [[| |am]|]; reflexivity.
Qed.

Definition pk_gind (f : ameta -> bool) (x : option mslot) : nat :=
  match x with Some (MUsed am) => if f am then 1%nat else 0%nat | _ => 0%nat end.

Lemma gcount_sum s f : gcountX [] s f = Z.of_nat (pk_sum (fun g => pk_gind f (MT s g)) (keys s)).
Proof.
  unfold gcountX. rewrite pk_len_filter. f_equal. apply pk_sum_ext. intros g _. cbv beta.
  unfold MTX. cbn [memb existsb]. destruct (MT s g) as [[| |am]|]; reflexivity.
Qed.

Lemma gcount_le s s' (f : ameta -> bool) : NoDup (keys s') -> NoDup (keys s) ->
  (forall q a', MT s' q = Some (MUsed a') -> f a' = true -> exists a, MT s q = Some (MUsed a) /\ f a = true) ->
  gcountX [] s' f <= gcountX [] s f.
Proof.
  intros N' N H. rewrite !gcount_sum. apply Nat2Z.inj_le.
  apply (pk_sum_le sptr_eq_dec); [exact N' | exact N |].
  intros q _ Hnz. cbv beta in Hnz |- *. revert Hnz.
  destruct (MT s' q) as [[pr nx| |a']|] eqn:E; cbn [pk_gind]; intros Hnz; try (exfalso; apply Hnz; reflexivity).
  revert Hnz. destruct (f a') eqn:Fa; intros Hnz; [|exfalso; apply Hnz; reflexivity].
  destruct (H q a' E Fa) as (a & Ea & Fa0). split; [exact (MT_Some_In_keys _ _ _ Ea)|].
  rewrite Ea. cbn [pk_gind]. rewrite Fa0. cbv beta iota. lia.
Qed.

Lemma PKC_tr s s' caps : NoDup (keys s') -> NoDup (keys s) -> PKC [] caps s ->
  (forall q a', MT s' q = Some (MUsed a') -> am_sc a' < 48 ->
     exists a, MT s q = Some (MUsed a) /\ am_sc a' = am_sc a /\ am_last a' = am_last a) ->
  PKC [] caps s'.
Proof.
  intros N' N HP H c Hc. destruct (HP c Hc) as [F R]. split.
  - eapply Z.le_trans; [|exact F]. apply gcount_le; [exact N' | exact N |].
    intros q a' E Fa. unfold gfull in Fa. apply andb_prop in Fa as [S T]. apply Z.eqb_eq in S.
    destruct (H q a' E ltac:(lia)) as (a & Ea & Sa & Ta). exists a. split; [exact Ea|].
    unfold gfull. rewrite <- Sa, <- Ta, S, Z.eqb_refl. exact T.
  - eapply Z.le_trans; [|exact R]. apply gcount_le; [exact N' | exact N |].
    intros q a' E Fa. unfold gred in Fa. apply andb_prop in Fa as [S T]. apply Z.eqb_eq in S.
    destruct (H q a' E ltac:(lia)) as (a & Ea & Sa & Ta). exists a. split; [exact Ea|].
    unfold gred. rewrite <- Sa, <- Ta, S, Z.eqb_refl. exact T.
Qed.

Lemma ucnt_le c a a' : am_sc a' = am_sc a -> am_last a' = am_last a -> AllocFree.af_frs a a' ->
  (pk_ucnt c (Some (MUsed a')) <= pk_ucnt c (Some (MUsed a)))%nat.
Proof.
  intros S T F. cbn [pk_ucnt]. unfold pk_ublk, blocks_of0. rewrite S, T.
  destruct ((am_sc a =? c) && (1 <=? am_last a)); cbv beta iota; [|cbn; lia].
  rewrite !pk_len_filter_flat. apply pk_sum_mono. intros j _. cbv beta.
  unfold slot_block0. destruct (ss_fr (nth_slot a' j)) as [f|] eqn:E; [|cbn; lia].
  rewrite (F j f E). destruct (fr_kind f); cbn [filter snd]; try (destruct (band (fr_n f) =? c - 1)); cbn; lia.
Qed.

Lemma upc_le s s' c : NoDup (keys s') -> NoDup (keys s) ->
  (forall q a', MT s' q = Some (MUsed a') -> exists a, MT s q = Some (MUsed a) /\
     am_sc a' = am_sc a /\ am_last a' = am_last a /\ AllocFree.af_frs a a') ->
  upc s' c <= upc s c.
Proof.
  intros N' N H. rewrite (upc_sum s' c N'), (upc_sum s c N). apply Nat2Z.inj_le.
  apply (pk_sum_le sptr_eq_dec); [exact N' | exact N |].
  intros q _ Hnz. cbv beta in Hnz |- *. revert Hnz.
  destruct (MT s' q) as [[pr nx| |a']|] eqn:E; intros Hnz; try (exfalso; apply Hnz; reflexivity).
  destruct (H q a' E) as (a & Ea & S & T & F). rewrite Ea.
  split; [exact (MT_Some_In_keys _ _ _ Ea) | exact (ucnt_le c a a' S T F)].
Qed.

Lemma bcount_del s s' l1 l2 x j : user_blocks s = l1 ++ x :: l2 -> user_blocks s' = l1 ++ l2 ->
  bcount s' j + (if band (snd x) =? j then 1 else 0) = bcount s j.
Proof.
  intros E E'. unfold bcount. rewrite E, E', !filter_app, !length_app. cbn [filter].
  destruct (band (snd x) =? j); cbn [length]; lia.
Qed.

Lemma bcount_swap s s' l1 l2 x y j : user_blocks s = l1 ++ x :: l2 -> user_blocks s' = l1 ++ y :: l2 ->
  bcount s' j + (if band (snd x) =? j then 1 else 0) = bcount s j + (if band (snd y) =? j then 1 else 0).
Proof.
  intros E E'. unfold bcount. rewrite E, E', !filter_app, !length_app. cbn [filter].
  destruct (band (snd x) =? j), (band (snd y) =? j); cbn [length]; lia.
Qed.

Lemma zupd_nth l i v j : nth j (zupd l i v) 0 = if Nat.eqb j i && Nat.ltb i (length l) then v else nth j l 0.
Proof.
  revert i j. induction l as [|h t IH]; intros i j.
  - cbn [zupd]. destruct (Nat.eqb j i); reflexivity.
  - destruct i as [|i], j as [|j]; [reflexivity | reflexivity | reflexivity | exact (IH i j)].
Qed.

Lemma zupd_length l i v : length (zupd l i v) = length l.
Proof.
  revert i. induction l as [|h t IH]; intros [|i]; cbn [zupd length]; [reflexivity | reflexivity | reflexivity |].
  rewrite IH. reflexivity.
Qed.

Lemma lv_add_length L k d : length (lv_add L k d) = length L.
Proof. apply zupd_length. Qed.

Lemma lv_add_nth L k d j : 0 <= j -> 0 <= k ->
  znth j (lv_add L k d) = znth j L + (if (j =? k) && (k <? Z.of_nat (length L)) then d else 0).
Proof.
  intros Hj Hk. unfold lv_add, zset, znth. rewrite zupd_nth.
  destruct (Z.eqb_spec j k) as [->|E'].
  - rewrite Nat.eqb_refl. cbn [andb].
    destruct (Nat.ltb_spec (Z.to_nat k) (length L)); destruct (Z.ltb_spec k (Z.of_nat (length L))); cbv beta iota; lia.
  - destruct (Nat.eqb_spec (Z.to_nat j) (Z.to_nat k)) as [E|E]; [lia|]. cbn [andb]. lia.
Qed.

Lemma lv_add_in L k d j : 0 <= j -> 0 <= k < Z.of_nat (length L) ->
  znth j (lv_add L k d) = znth j L + (if j =? k then d else 0).
Proof.
  intros Hj Hk. rewrite lv_add_nth by lia. destruct (Z.ltb_spec k (Z.of_nat (length L))); [|lia].
  destruct (j =? k); reflexivity.
Qed.

Lemma lv_add_same L k d : 0 <= k < Z.of_nat (length L) -> znth k (lv_add L k d) = znth k L + d.
Proof. intros Hk. rewrite lv_add_in by lia. rewrite Z.eqb_refl. reflexivity. Qed.

Lemma lv_add_other L k d j : 0 <= j -> 0 <= k -> j <> k -> znth j (lv_add L k d) = znth j L.
Proof. intros Hj Hk Ne. rewrite lv_add_nth by lia. destruct (Z.eqb_spec j k); [lia|]. cbn [andb]. lia. Qed.

Lemma lv_add_le_neg L k d j : 0 <= j -> 0 <= k -> d <= 0 ->
  znth j L + (if j =? k then d else 0) <= znth j (lv_add L k d).
Proof.
  intros Hj Hk Hd. rewrite lv_add_nth by lia.
  destruct (j =? k); destruct (k <? Z.of_nat (length L)); cbn [andb]; lia.
Qed.

Lemma UPB_mono s L L' : (forall k, 0 <= k < 49 -> znth k L <= znth k L') -> UPB s L -> UPB s L'.
Proof.
  intros H (U1 & U2). split.
  - intros k Hk. specialize (U1 k Hk). specialize (H k Hk). lia.
  - intros c Hc. specialize (U2 c Hc). specialize (H c ltac:(lia)). lia.
Qed.

Lemma band_range x : 0 <= x -> 0 <= band x <= 48.
Proof.
  intros H. unfold band. destruct (Z.leb_spec MMAP_THRESHOLD x) as [Hm|Hm]; [lia|].
  pose proof (size_to_class_range x (conj H Hm)) as [R _]. lia.
Qed.

Lemma stc_le c n : 0 <= c < 48 -> 0 <= n -> n + IB <= class_size c -> size_to_class n <= c.
Proof.
  intros Hc Hn Hf. pose proof (class_size_bounds c Hc) as CB. unfold size_to_class.
  assert (Hk : 0 <= Z.shiftr (n + IB - 1) 4 /\ UNIT * Z.shiftr (n + IB - 1) 4 <= n + IB - 1).
  { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16. unfold UNIT.
    pose proof (Z.mul_div_le (n + IB - 1) 16 ltac:(lia)) as D. split; [apply Z.div_pos; unfold IB; lia | lia]. }
  set (k := Z.shiftr (n + IB - 1) 4) in *. unfold UNIT, IB in Hk, Hf.
  brute class_of_units_ok k as HT.
  apply andb_prop in HT as [HT H4]. apply andb_prop in HT as [HT H3]. apply andb_prop in HT as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.ltb_lt in H3.
  destruct (Z.le_gt_cases (class_of_units k) c) as [L|L]; [exact L|]. exfalso.
  unfold implb in H4. destruct (0 <? class_of_units k) eqn:E; [|apply Z.ltb_ge in E; lia].
  cbn [negb orb] in H4. apply Z.leb_le in H4.
  pose proof (class_size_mono c (class_of_units k - 1) ltac:(lia) ltac:(lia) ltac:(lia)) as M.
  unfold class_size, UNIT in M, Hf. lia.
Qed.

Theorem free_pack : forall s p n caps L tr u s',
  WF s -> SI s -> PKS [] s -> PKC [] caps s -> UPB s L -> In (p, n) (user_blocks s) ->
  yields (free (Some p) s) tr (u, s') ->
  PKS [] s' /\ PKC [] caps s' /\ UPB s' (lv_add L (band n) (-1)).
Proof.
  intros s p n caps L tr u s' HW _ HP HC (U1 & U2) Hin Y. destruct u.
  pose proof (free_wf s p n tr s' HW Hin Y) as HW'.
  pose proof (proj1 (inv_keys HW)) as N. pose proof (proj1 (inv_keys HW')) as N'.
  pose proof (free_rel s p tr s' Y) as R.
  destruct (free_blocks s p n tr s' HW Hin Y) as (l1 & l2 & E1 & E2).
  pose proof (AllocBound.ub_nonneg s HW (p, n) Hin) as Hn. cbn [snd] in Hn.
  pose proof (band_range n Hn) as Bn.
  split; [|split].
  - apply (PKS_tr s s' HP). intros q a' Hu. left.
    destruct (usedX_MT _ _ _ _ Hu) as [Hm _]. destruct (R q a' Hm) as (a & Ha & M & Lm & S & T & F).
    exists a. split; [apply usedX_intro; [reflexivity | exact Ha]|].
    split; [exact (conj M (conj Lm (conj S T)))|].
    intros j f _ Hf. left. exact (F j f Hf).
  - apply (PKC_tr s s' caps N' N HC). intros q a' Hm _. destruct (R q a' Hm) as (a & Ha & _ & _ & S & T & _).
    exists a. split; [exact Ha|]. split; [exact S | exact T].
  - assert (UP : forall c, upc s' c <= upc s c).
    { intros c. apply (upc_le s s' c N' N). intros q a' Hm. destruct (R q a' Hm) as (a & Ha & _ & _ & S & T & F).
      exists a. split; [exact Ha|]. split; [exact S|]. split; [exact T | exact F]. }
    split.
    + intros j Hj. pose proof (bcount_del s s' l1 l2 (p, n) j E1 E2) as B. cbn [snd] in B. specialize (U1 j Hj).
      pose proof (lv_add_le_neg L (band n) (-1) j ltac:(lia) ltac:(lia) ltac:(lia)) as V.
      revert B V. destruct (Z.eqb_spec (band n) j); destruct (Z.eqb_spec j (band n)); cbv beta iota; intros B V; lia.
    + intros c Hc. pose proof (bcount_del s s' l1 l2 (p, n) c E1 E2) as B. cbn [snd] in B. specialize (U2 c Hc).
      pose proof (lv_add_le_neg L (band n) (-1) c ltac:(lia) ltac:(lia) ltac:(lia)) as V. pose proof (UP c) as W.
      revert B V. destruct (Z.eqb_spec (band n) c); destruct (Z.eqb_spec c (band n)); cbv beta iota; intros B V; lia.
Qed.

Lemma lv_realloc_nth L k n j : length L = 49%nat -> 0 <= j -> 0 <= k -> 0 <= n ->
  znth j (lv_realloc L k n) = znth j L + (if j =? band n then 1 else 0) -
    (if band n <? band k then 0 else if j =? band k then 1 else 0).
Proof.
  intros HL Hj Hk Hn. pose proof (band_range k Hk) as Bk. pose proof (band_range n Hn) as Bn.
  unfold lv_realloc. destruct (Z.ltb_spec (band n) (band k)); cbv beta iota.
  - rewrite lv_add_nth by lia. rewrite HL. change (Z.of_nat 49) with 49.
    destruct (Z.eqb_spec j (band n)); destruct (Z.ltb_spec (band n) 49); cbn [andb]; lia.
  - rewrite !lv_add_nth by lia. rewrite lv_add_length, HL. change (Z.of_nat 49) with 49.
    destruct (Z.eqb_spec j (band n)); destruct (Z.eqb_spec j (band k)); destruct (Z.ltb_spec (band n) 49);
      destruct (Z.ltb_spec (band k) 49); cbn [andb]; lia.
Qed.

Lemma move_le L k n j : length L = 49%nat -> 0 <= k -> 0 <= n -> 0 <= j ->
  znth j (lv_add (lv_add L (band n) 1) (band k) (-1)) <= znth j (lv_realloc L k n).
Proof.
  intros HL Hk Hn Hj. pose proof (band_range k Hk) as Bk. pose proof (band_range n Hn) as Bn.
  rewrite (lv_realloc_nth L k n j HL Hj Hk Hn). rewrite !lv_add_nth by lia. rewrite lv_add_length, HL.
  change (Z.of_nat 49) with 49.
  destruct (Z.eqb_spec j (band n)); destruct (Z.eqb_spec j (band k)); destruct (Z.ltb_spec (band n) 49);
    destruct (Z.ltb_spec (band k) 49); destruct (Z.ltb_spec (band n) (band k)); cbn [andb]; lia.
Qed.

Lemma UPB_swap s s' L k n : length L = 49%nat -> 0 <= k -> 0 <= n -> UPB s L ->
  (forall j, bcount s' j + (if band k =? j then 1 else 0) = bcount s j + (if band n =? j then 1 else 0)) ->
  (forall c, 1 <= c < 48 -> upc s' c <= upc s c + (if band n <? band k then (if band k =? c then 1 else 0) else 0)) ->
  UPB s' (lv_realloc L k n).
Proof.
  intros HL Hk Hn (U1 & U2) B Up. split.
  - intros j Hj. rewrite (lv_realloc_nth L k n j HL ltac:(lia) Hk Hn). specialize (U1 j Hj). specialize (B j).
    revert B. destruct (Z.eqb_spec (band k) j); destruct (Z.eqb_spec (band n) j); destruct (Z.eqb_spec j (band n));
      destruct (Z.eqb_spec j (band k)); destruct (Z.ltb_spec (band n) (band k)); cbv beta iota; intros B; lia.
  - intros c Hc. rewrite (lv_realloc_nth L k n c HL ltac:(lia) Hk Hn). specialize (U2 c Hc). specialize (B c).
    specialize (Up c Hc).
    revert B Up. destruct (Z.eqb_spec (band k) c); destruct (Z.eqb_spec (band n) c); destruct (Z.eqb_spec c (band n));
      destruct (Z.eqb_spec c (band k)); destruct (Z.ltb_spec (band n) (band k)); cbv beta iota; intros B Up; lia.
Qed.

Lemma PKS_upd s g am am1 i : PKS [] s -> usedX [] s g am -> pk_shp am am1 ->
  (forall j, 0 <= j -> j <> i -> nth_slot am1 j = nth_slot am j) ->
  (forall f, ss_fr (nth_slot am1 i) = Some f ->
     fr_kind f = FUser /\ (am_sc am < 48 -> fr_n f < MMAP_THRESHOLD /\ am_sc am <= size_to_class (fr_n f) + 1)) ->
  PKS [] (upd_meta g (MUsed am1) s).
Proof.
  intros HP Hg Sh Hj Hi. apply (PKS_tr s _ HP). intros q a' Hu. left.
  apply usedX_upd in Hu as [(-> & _ & E) | (Ne & Hu)].
  - injection E as <-. exists am. split; [exact Hg|]. split; [exact Sh|].
    intros j f Hjr Hf. destruct (Z.eq_dec j i) as [->|Ne]; [right; exact (Hi f Hf)|].
    left. rewrite <- (Hj j ltac:(lia) Ne). exact Hf.
  - exists a'. split; [exact Hu|]. split; [split; [reflexivity | split; [reflexivity | split; reflexivity]]|].
    intros j f _ Hf. left. exact Hf.
Qed.

Lemma PKC_upd s g am am1 caps : WF s -> PKC [] caps s -> usedX [] s g am ->
  am_sc am1 = am_sc am -> am_last am1 = am_last am -> PKC [] caps (upd_meta g (MUsed am1) s).
Proof.
  intros HW HC Hg S T. pose proof (proj1 (usedX_MT _ _ _ _ Hg)) as Mg.
  pose proof (proj1 (inv_keys HW)) as N.
  assert (N' : NoDup (keys (upd_meta g (MUsed am1) s))) by (rewrite keys_upd_In by exact (MT_Some_In_keys _ _ _ Mg); exact N).
  apply (PKC_tr s _ caps N' N HC). intros q a' E _. rewrite MT_upd in E.
  destruct (sptr_eqb q g) eqn:Eq.
  - apply sptr_eqb_eq in Eq. subst q. injection E as <-. exists am. split; [exact Mg|]. split; [exact S | exact T].
  - exists a'. split; [exact E|]. split; reflexivity.
Qed.

Lemma upc_upd s g am am1 c : NoDup (keys s) -> MT s g = Some (MUsed am) ->
  upc (upd_meta g (MUsed am1) s) c + Z.of_nat (pk_ucnt c (Some (MUsed am))) =
  upc s c + Z.of_nat (pk_ucnt c (Some (MUsed am1))).
Proof.
  intros N Mg. pose proof (MT_Some_In_keys _ _ _ Mg) as Kg.
  assert (N' : NoDup (keys (upd_meta g (MUsed am1) s))) by (rewrite keys_upd_In by exact Kg; exact N).
  rewrite (upc_sum _ c N'), (upc_sum s c N), (keys_upd_In g (MUsed am1) s Kg).
  assert (E : (pk_sum (fun q => pk_ucnt c (MT (upd_meta g (MUsed am1) s) q)) (keys s) + pk_ucnt c (MT s g) =
               pk_sum (fun q => pk_ucnt c (MT s q)) (keys s) + pk_ucnt c (MT (upd_meta g (MUsed am1) s) g))%nat).
  { apply (pk_sum_upd sptr_eq_dec (fun q => pk_ucnt c (MT (upd_meta g (MUsed am1) s) q)) (fun q => pk_ucnt c (MT s q))
      (keys s) g N Kg).
    intros y _ Ne. rewrite MT_upd_other by exact Ne. reflexivity. }
  rewrite MT_upd_same, Mg in E. lia.
Qed.

Definition pk_bnd (c x : Z) : nat := if band x =? c - 1 then 1%nat else 0%nat.

Lemma pk_zseq_ge lo n j : In j (zseq lo n) -> lo <= j.
Proof. unfold zseq. intros H. apply in_map_iff in H as (m & <- & _). lia. Qed.

Lemma ucnt_off c a : (am_sc a =? c) && (1 <=? am_last a) = false -> pk_ucnt c (Some (MUsed a)) = 0%nat.
Proof. intros H. cbn [pk_ucnt]. unfold pk_ublk. rewrite H. reflexivity. Qed.

Lemma ucnt63 c a : am_sc a = 63 -> c < 48 -> pk_ucnt c (Some (MUsed a)) = 0%nat.
Proof.
  intros H Hc. apply ucnt_off. rewrite H. destruct (Z.eqb_spec 63 c); [lia | reflexivity].
Qed.

Lemma ucnt_on c am am1 i fr f1 : (am_sc am =? c) && (1 <=? am_last am) = true -> pk_shp am am1 ->
  0 <= i <= am_last am -> (forall j, 0 <= j -> j <> i -> nth_slot am1 j = nth_slot am j) ->
  ss_fr (nth_slot am i) = Some fr -> fr_kind fr = FUser ->
  ss_fr (nth_slot am1 i) = Some f1 -> fr_kind f1 = FUser ->
  (pk_ucnt c (Some (MUsed am1)) + pk_bnd c (fr_n fr) = pk_ucnt c (Some (MUsed am)) + pk_bnd c (fr_n f1))%nat.
Proof.
  intros Cd Sh Hi Hj Hf Hk Hf1 Hk1. pose proof Sh as (M & Lm & S & T).
  cbn [pk_ucnt]. unfold pk_ublk. rewrite S, T, Cd. cbv beta iota. unfold blocks_of0. rewrite T, !pk_len_filter_flat.
  assert (Ei : length (filter (fun b : sptr * Z => band (snd b) =? c - 1) (slot_block0 am i)) = pk_bnd c (fr_n fr)).
  { unfold slot_block0. rewrite Hf. cbn [filter]. rewrite Hk. cbn [filter snd]. unfold pk_bnd.
    destruct (band (fr_n fr) =? c - 1); reflexivity. }
  assert (Ei1 : length (filter (fun b : sptr * Z => band (snd b) =? c - 1) (slot_block0 am1 i)) = pk_bnd c (fr_n f1)).
  { unfold slot_block0. rewrite Hf1. cbn [filter]. rewrite Hk1. cbn [filter snd]. unfold pk_bnd.
    destruct (band (fr_n f1) =? c - 1); reflexivity. }
  rewrite <- Ei, <- Ei1.
  apply (pk_sum_upd Z.eq_dec (fun x => length (filter (fun b : sptr * Z => band (snd b) =? c - 1) (slot_block0 am1 x)))
    (fun x => length (filter (fun b : sptr * Z => band (snd b) =? c - 1) (slot_block0 am x)))
    (zseq 0 (am_last am + 1)) i).
  - apply zseq_NoDup.
  - apply zseq_In; lia.
  - intros j Hj0 Ne. pose proof (pk_zseq_ge _ _ _ Hj0) as Hj1. cbv beta.
    unfold slot_block0. rewrite (Hj j Hj1 Ne), (pk_shp_slot_start am am1 j Sh). reflexivity.
Qed.

Lemma pk_frame s g am i fr : WF s -> usedX [] s g am -> 0 <= i <= am_last am -> ss_fr (nth_slot am i) = Some fr ->
  0 <= fr_n fr /\ 0 <= fr_off fr /\ UNIT * fr_off fr + fr_n fr <= stride_of am - IB /\ 0 <= am_sc am.
Proof.
  intros HW Hu Hi Hfr. pose proof (inv_groups HW g am Hu) as (_ & _ & Gsl & Gcl & _).
  assert (Hs0 : 0 <= am_sc am) by (destruct Gcl as [(C & _)|(C & _)]; lia).
  specialize (Gsl i Hi). unfold slot_ok in Gsl. cbv zeta in Gsl. rewrite Hfr in Gsl.
  destruct Gsl as (_ & _ & _ & _ & (F0 & F1 & F2 & _) & _). lia.
Qed.

Lemma ip_pack_gen s g am am1 i fr f1 caps L : WF s -> usedX [] s g am -> 0 <= i <= am_last am ->
  ss_fr (nth_slot am i) = Some fr -> fr_kind fr = FUser -> pk_shp am am1 ->
  (forall j, 0 <= j -> j <> i -> nth_slot am1 j = nth_slot am j) ->
  ss_fr (nth_slot am1 i) = Some f1 -> fr_kind f1 = FUser -> 0 <= fr_n f1 ->
  (am_sc am < 48 -> fr_n f1 < MMAP_THRESHOLD /\ am_sc am <= size_to_class (fr_n f1) + 1) ->
  (exists l1 l2 x y, user_blocks s = l1 ++ (x, fr_n fr) :: l2 /\
     user_blocks (upd_meta g (MUsed am1) s) = l1 ++ (y, fr_n f1) :: l2) ->
  PKS [] s -> PKC [] caps s -> UPB s L -> length L = 49%nat ->
  PKS [] (upd_meta g (MUsed am1) s) /\ PKC [] caps (upd_meta g (MUsed am1) s) /\
  UPB (upd_meta g (MUsed am1) s) (lv_realloc L (fr_n fr) (fr_n f1)).
Proof.
  intros HW Hu Hi Hfr Hk Sh Hj Hf1 Hk1 Hn1 Hc1 Hbl HP HC HU HL.
  pose proof Sh as (M & Lm & S & T).
  pose proof (usedX_MT _ _ _ _ Hu) as [Mg _]. pose proof (proj1 (inv_keys HW)) as N.
  destruct (pk_frame s g am i fr HW Hu Hi Hfr) as (Hk0 & Fo & F2 & Hs0).
  assert (Fk : 1 <= am_last am -> am_sc am < 48 -> am_sc am - 1 <= band (fr_n fr) <= am_sc am).
  { intros Hl Hs. pose proof HP as (P1 & _). destruct (P1 g am i fr Hu Hs Hi Hfr Hk) as (Hm & Hb).
    assert (St : stride_of am = class_size (am_sc am)).
    { unfold stride_of. destruct (Z.eqb_spec (am_last am) 0); [lia | reflexivity]. }
    rewrite St in F2. unfold UNIT in F2.
    pose proof (stc_le (am_sc am) (fr_n fr) ltac:(lia) Hk0 ltac:(lia)) as Le.
    unfold band. destruct (Z.leb_spec MMAP_THRESHOLD (fr_n fr)); lia. }
  split; [|split].
  - apply (PKS_upd s g am am1 i HP Hu Sh Hj). intros f Ef. rewrite Hf1 in Ef. injection Ef as <-.
    split; [exact Hk1 | exact Hc1].
  - exact (PKC_upd s g am am1 caps HW HC Hu S T).
  - destruct Hbl as (l1 & l2 & x & y & E1 & E2).
    apply (UPB_swap s _ L (fr_n fr) (fr_n f1) HL Hk0 Hn1 HU).
    + intros j. exact (bcount_swap s _ l1 l2 (x, fr_n fr) (y, fr_n f1) j E1 E2).
    + intros c Hc. pose proof (upc_upd s g am am1 c N Mg) as E.
      destruct ((am_sc am =? c) && (1 <=? am_last am)) eqn:Cd.
      * pose proof (ucnt_on c am am1 i fr f1 Cd Sh Hi Hj Hfr Hk Hf1 Hk1) as E'.
        apply andb_prop in Cd as [Cs Cl]. apply Z.eqb_eq in Cs. apply Z.leb_le in Cl.
        destruct (Fk Cl ltac:(lia)) as [Fk1 Fk2].
        unfold pk_bnd in E'. revert E E'.
        destruct (Z.eqb_spec (band (fr_n fr)) (c - 1)); destruct (Z.eqb_spec (band (fr_n f1)) (c - 1));
          destruct (Z.ltb_spec (band (fr_n f1)) (band (fr_n fr))); destruct (Z.eqb_spec (band (fr_n fr)) c);
          cbv beta iota; intros E E'; lia.
      * assert (Cd1 : (am_sc am1 =? c) && (1 <=? am_last am1) = false) by (rewrite S, T; exact Cd).
        rewrite (ucnt_off c am Cd), (ucnt_off c am1 Cd1) in E.
        destruct (band (fr_n f1) <? band (fr_n fr)), (band (fr_n fr) =? c); cbv beta iota; lia.
Qed.

Lemma ip_pack s g am i fr n caps L : IPH s g am i fr n -> PKS [] s -> PKC [] caps s -> UPB s L -> length L = 49%nat ->
  (am_sc am < 48 -> n < MMAP_THRESHOLD /\ am_sc am <= size_to_class n + 1) ->
  PKS [] (upd_meta g (MUsed (rs_am am i (fr_off fr) n)) s) /\
  PKC [] caps (upd_meta g (MUsed (rs_am am i (fr_off fr) n)) s) /\
  UPB (upd_meta g (MUsed (rs_am am i (fr_off fr) n)) s) (lv_realloc L (fr_n fr) n).
Proof.
  intros H HP HC HU HL Hc. pose proof H as (HW & Hu & Hi & Hfr & Hk & Hn & _).
  destruct (rs_fields am i (fr_off fr) n) as (M & T & S & Lm & _).
  destruct (ip_blocks s g am i fr n H) as (l1 & l2 & E1 & E2).
  assert (Hj : forall j, 0 <= j -> j <> i -> nth_slot (rs_am am i (fr_off fr) n) j = nth_slot am j).
  { intros j Hj Ne. rewrite (ip_ns s g am i fr n j H Hj). apply Z.eqb_neq in Ne. rewrite Ne. reflexivity. }
  exact (ip_pack_gen s g am (rs_am am i (fr_off fr) n) i fr (mkFrame (fr_off fr) n FUser) caps L HW Hu Hi Hfr Hk
    (conj M (conj Lm (conj S T))) Hj (ip_fr1 s g am i fr n H) eq_refl Hn Hc
    (ex_intro _ l1 (ex_intro _ l2 (ex_intro _ _ (ex_intro _ _ (conj E1 E2))))) HP HC HU HL).
Qed.

Lemma PKS_metas s s' : st_metas s' = st_metas s -> PKS [] s -> PKS [] s'.
Proof. intros E H. unfold PKS, usedX, MTX, MT in *. rewrite E. exact H. Qed.

Lemma PKC_metas s s' caps : st_metas s' = st_metas s -> PKC [] caps s -> PKC [] caps s'.
Proof. intros E H. unfold PKC, gcountX, keys, MTX, MT in *. rewrite E. exact H. Qed.

Lemma upc_metas s s' c : st_metas s' = st_metas s -> upc s' c = upc s c.
Proof. intros E. unfold upc, ub_cls, used_metas. rewrite E. reflexivity. Qed.

Lemma rm_pack s g am fr n caps L : RMH s g am fr n -> PKS [] s -> PKC [] caps s -> UPB s L -> length L = 49%nat ->
  0 <= n -> 0 <= fr_n fr ->
  PKS [] (rm_state s g am 0 (fr_off fr) n) /\ PKC [] caps (rm_state s g am 0 (fr_off fr) n) /\
  UPB (rm_state s g am 0 (fr_off fr) n) (lv_realloc L (fr_n fr) n).
Proof.
  intros H HP HC HU HL Hn Hk0. pose proof H as (HW & Hu & Hfr & Hk & Hsc & Hbig).
  destruct (rm_basic s g am fr n H) as (Hl & _ & _ & _ & _ & _ & _ & Hsl & Foff & _).
  pose proof (usedX_MT _ _ _ _ Hu) as [Mg _]. pose proof (proj1 (inv_keys HW)) as N.
  assert (EM : st_metas (rm_state s g am 0 (fr_off fr) n) =
               st_metas (upd_meta g (MUsed (rm_am s am 0 (fr_off fr) n)) s)) by reflexivity.
  split; [|split].
  - apply (PKS_metas _ _ EM). apply (PKS_tr s _ HP). intros q a' Hq.
    apply usedX_upd in Hq as [(-> & _ & E) | (Ne & Hq)].
    + injection E as <-. right. split; [exact Hsc|]. split.
      * pose proof (rm_need_facts n (fr_off fr) Hbig Foff) as (_ & RN & _).
        change (0 < rm_need n (fr_off fr) / 4096). lia.
      * intros j f Hj Hf. change (0 <= j <= am_last am) in Hj. rewrite Hl in Hj. assert (j = 0) by lia. subst j.
        rewrite (rm_slot0 s am (fr_off fr) n Hsl) in Hf. cbn [resize_slot ss_fr] in Hf. injection Hf as <-. reflexivity.
    + left. exists a'. split; [exact Hq|]. split; [split; [reflexivity | split; [reflexivity | split; reflexivity]]|].
      intros j f _ Hf. left. exact Hf.
  - apply (PKC_metas _ _ caps EM). exact (PKC_upd s g am (rm_am s am 0 (fr_off fr) n) caps HW HC Hu eq_refl eq_refl).
  - destruct (rm_blocks s g am fr n H) as (l1 & l2 & E1 & E2).
    apply (UPB_swap s _ L (fr_n fr) n HL Hk0 Hn HU).
    + intros j. exact (bcount_swap s _ l1 l2 _ _ j E1 E2).
    + intros c Hc. rewrite (upc_metas _ _ c EM). pose proof (upc_upd s g am (rm_am s am 0 (fr_off fr) n) c N Mg) as E.
      rewrite (ucnt63 c am Hsc ltac:(lia)), (ucnt63 c (rm_am s am 0 (fr_off fr) n) Hsc ltac:(lia)) in E.
      destruct (band n <? band (fr_n fr)), (band (fr_n fr) =? c); cbv beta iota; lia.
Qed.

Section PackRealloc.

Hypothesis malloc_pack_h : forall s n caps L tr r s',
  WF s -> SI s -> GS s -> NL s -> noraw s -> PKS [] s -> PKC [] caps s -> UPB s L ->
  length caps = 49%nat -> length L = 49%nat -> (forall k, 0 <= k < 49 -> 0 <= znth k L <= znth k caps) ->
  0 <= n -> yields (malloc n s) tr (r, s') ->
  PKS [] s' /\ PKC [] caps s' /\ UPB s' (match r with Some _ => lv_add L (band n) 1 | None => L end).

Theorem realloc_pack : forall s p k n caps L tr r s',
  WF s -> SI s -> GS s -> NL s -> noraw s -> PKS [] s -> PKC [] caps s -> UPB s L ->
  length caps = 49%nat -> length L = 49%nat -> (forall k, 0 <= k < 49 -> 0 <= znth k L <= znth k caps) ->
  In (p, k) (user_blocks s) -> 0 <= n -> yields (realloc (Some p) n s) tr (r, s') ->
  PKS [] s' /\ PKC [] caps s' /\ UPB s' (match r with Some _ => lv_realloc L k n | None => L end).
Proof.
  intros s p k n caps L tr r s' HW HS HG HN HR HP HC HU Lc LL Lb Hin Hn Y.
  pose proof (AllocBound.ub_nonneg s HW (p, k) Hin) as Hk0. cbn [snd] in Hk0.
  destruct (ra_cases answer_ok s p k n tr r s' HW Hin (rpath_yields _ _ _ Y))
    as [[-> ->] | (g & am & i & fr & Hu & Hi & Hfr & Hk & En & Ep & C)]; [exact (conj HP (conj HC HU))|].
  subst k.
  destruct C as [(Hc & -> & ->) | [(Hsc & Hbig & Hml & -> & ->) | [(Hsc & Hbig & Hne & -> & ->) | (tr' & Hm)]]].
  - pose proof (ip_of_c1 s g am i fr n HW Hu Hi Hfr Hk Hn Hc) as I.
    unfold ra_c1 in Hc. apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [_ H2].
    apply Z.ltb_lt in H2. apply Z.leb_le in H3.
    exact (ip_pack s g am i fr n caps L I HP HC HU LL (fun _ => conj H2 H3)).
  - pose proof (ip_of_same s g am i fr n HW Hu Hi Hfr Hk Hsc Hbig Hml) as I.
    assert (Hc' : am_sc am < 48 -> n < MMAP_THRESHOLD /\ am_sc am <= size_to_class n + 1) by (intros; exfalso; lia).
    exact (ip_pack s g am i fr n caps L I HP HC HU LL Hc').
  - destruct (rm_of s g am i fr n HW Hu Hi Hfr Hk Hsc Hbig) as [-> R].
    exact (rm_pack s g am fr n caps L R HP HC HU LL Hn Hk0).
  - destruct (ra_move answer_ok p n s tr' r s' Hm) as (tr1 & q & s1 & H1 & Hq).
    pose proof (yields_rpath _ _ _ H1) as Y1.
    destruct (malloc_pack_h s n caps L tr1 q s1 HW HS HG HN HR HP HC HU Lc LL Lb Hn Y1) as (P1 & C1 & U1).
    destruct q as [q|].
    + destruct Hq as (-> & tr2 & H2).
      pose proof (malloc_wf s n tr1 (Some q) s1 HW Hn Y1) as HW1.
      pose proof (AllocMalloc.malloc_SI s n tr1 (Some q) s1 HW HS Hn Y1) as HS1.
      destruct (malloc_blocks s n tr1 (Some q) s1 HW Hn Y1) as (l1 & l2 & E1 & E2 & _).
      pose proof (in_after_malloc s s1 l1 l2 q n (p, fr_n fr) E1 E2 Hin) as Hin1.
      destruct (free_pack s1 p (fr_n fr) caps (lv_add L (band n) 1) tr2 tt s' HW1 HS1 P1 C1 U1 Hin1
        (yields_rpath _ _ _ H2)) as (P2 & C2 & U2).
      split; [exact P2|]. split; [exact C2|].
      assert (ML : forall j, 0 <= j < 49 ->
        znth j (lv_add (lv_add L (band n) 1) (band (fr_n fr)) (-1)) <= znth j (lv_realloc L (fr_n fr) n))
        by (intros j Hj; apply move_le; lia).
      exact (UPB_mono s' _ _ ML U2).
    + destruct Hq as (-> & ->). exact (conj P1 (conj C1 U1)).
Qed.

End PackRealloc.
