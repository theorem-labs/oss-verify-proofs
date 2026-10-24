(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11 YK0s YK0i YK15 YM06 YM02 YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YO0i YO0f YO0g YO0w YO0s YO10 YO0r YO0e YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YN03 YN31.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma mreal_tall {R} : forall segs (t : itree astate R) c (Q : R -> config -> Prop) (P : R -> Prop),
mreal segs c t Q -> tall P t -> mreal segs c t (fun r c' => Q r c' /\ P r).
Proof.
intros segs t. induction t as [r | q s k IH | f]; intros c Q P HM HT; cbn in *.
- eapply SR_mono; [exact HM|]. intros c' H'. split; [exact H' | exact HT].
- eapply SR_mono; [exact HM|]. intros c1 Hk.
destruct q;
try (destruct Hk as (J & nx & bit & i0 & Hn & Hc & Hcl); exists J, nx, bit, i0;
split; [exact Hn|]; split; [| exact Hcl]; intros i; apply IH; [apply Hc | apply HT]).
destruct Hk as (z & Hz & Hc). exists z. split; [exact Hz|]. apply IH; [exact Hc | apply HT].
- exact I.
Qed.
Definition same_shape (a0 a : ameta) : Prop :=
am_mem a = am_mem a0 /\ am_sc a = am_sc a0 /\ am_aidx a = am_aidx a0 /\ am_last a = am_last a0 /\ am_maplen a = am_maplen a0 /\
length (am_slots a) = length (am_slots a0) /\
(forall i f, ss_fr (nth_slot a i) = Some f -> ss_fr (nth_slot a0 i) = Some f).
Lemma same_shape_refl a : same_shape a a.
Proof. repeat split; auto. Qed.
Lemma same_shape_trans a0 a1 a2 : same_shape a0 a1 -> same_shape a1 a2 -> same_shape a0 a2.
Proof.
intros (M1 & S1 & I1 & L1 & P1 & N1 & F1) (M2 & S2 & I2 & L2 & P2 & N2 & F2). repeat split; try congruence. intros i f H. apply F1, F2, H.
Qed.
Lemma same_shape_stride a0 a : same_shape a0 a -> stride_of a = stride_of a0.
Proof. intros (M & S & _ & L & P & _). unfold stride_of. rewrite L, P, S. reflexivity. Qed.
Definition mcorr (s0 s : astate) : Prop :=
forall q a, MT s q = Some (MUsed a) -> exists a0, MT s0 q = Some (MUsed a0) /\ same_shape a0 a.
Definition nt_keep (s0 s : astate) : Prop :=
st_regions s = st_regions s0 /\ st_brk s = st_brk s0 /\ st_areas s = st_areas s0 /\
st_meta_alloc_shift s = st_meta_alloc_shift s0 /\ st_avail_meta_areas s = st_avail_meta_areas s0 /\
st_init_done s = st_init_done s0 /\ length (st_usage s) = length (st_usage s0).
Definition ntrel (s0 s : astate) : Prop := mcorr s0 s /\ nt_keep s0 s.
Lemma ntrel_refl s : ntrel s s.
Proof. split; [| repeat split; reflexivity]. intros q a H. exists a. split; [exact H | apply same_shape_refl]. Qed.
Lemma ntrel_trans s0 s1 s2 : ntrel s0 s1 -> ntrel s1 s2 -> ntrel s0 s2.
Proof.
intros [C1 K1] [C2 K2]. split.
- intros q a H. destruct (C2 q a H) as (a1 & H1 & S1). destruct (C1 q a1 H1) as (a0 & H0 & S0).
exists a0. split; [exact H0 | eapply same_shape_trans; eauto].
- unfold nt_keep in *. destruct K1 as (?&?&?&?&?&?&?). destruct K2 as (?&?&?&?&?&?&?). repeat split; congruence.
Qed.
Definition PRES {A} (m : M A) : Prop := forall s, tall (fun r => ntrel s (snd r)) (m s).
Lemma pres_ret {A} (a : A) : PRES (ret a).
Proof. intros s. cbn. apply ntrel_refl. Qed.
Lemma pres_fail {A} f : PRES (@fail A f).
Proof. intros s. exact I. Qed.
Lemma pres_bind {A B} (m : M A) (k : A -> M B) : PRES m -> (forall a, PRES (k a)) -> PRES (bind m k).
Proof.
intros Hm Hk s. unfold bind. eapply tall_ibind; [apply Hm|]. intros [a s1] H1. cbn [fst snd] in *.
eapply tall_mono; [| apply (Hk a s1)]. intros [b s2] H2. cbn [snd] in *. eapply ntrel_trans; eauto.
Qed.
Lemma pres_bind_get {B} (k : astate -> M B) : (forall s0, PRES (k s0)) -> PRES (bind get k).
Proof. intros Hk s. unfold bind, get. cbn [ibind]. apply Hk. Qed.
Lemma pres_modify f : (forall s, ntrel s (f s)) -> PRES (modify f).
Proof. intros Hf s. cbn. apply Hf. Qed.
Lemma pres_massert b site : PRES (massert b site).
Proof. unfold massert. destruct b; [apply pres_ret | apply pres_fail]. Qed.
Lemma pres_mcheck b tag : PRES (mcheck b tag).
Proof. unfold mcheck. destruct b; [apply pres_ret | apply pres_fail]. Qed.
Lemma pres_getm p : PRES (getm p).
Proof.
unfold getm. apply pres_bind_get. intros s0. destruct (mlookup (st_metas s0) p) as [[| |am]|]; try apply pres_fail. apply pres_ret.
Qed.
Lemma pres_get_links p : PRES (get_links p).
Proof. unfold get_links. apply pres_bind_get. intros s0. destruct (mlookup (st_metas s0) p); [apply pres_ret | apply pres_fail]. Qed.
Lemma pres_get_head h : PRES (get_head h).
Proof. unfold get_head. apply pres_bind_get. intros s0. destruct h; apply pres_ret. Qed.
Lemma pres_find_frame p : PRES (find_frame p).
Proof. unfold find_frame. apply pres_bind_get. intros s0. destruct (find_frame_in (st_metas s0) p); [apply pres_ret | apply pres_fail]. Qed.
Lemma ntrel_same_metas s s' :
st_metas s' = st_metas s -> nt_keep s s' -> ntrel s s'.
Proof.
intros Hm Hk. split; [| exact Hk]. intros q a H. exists a. unfold MT in *. rewrite Hm in H. split; [exact H | apply same_shape_refl].
Qed.
Lemma pres_set_head h v : PRES (set_head h v).
Proof.
unfold set_head. destruct h; apply pres_modify; intros s; apply ntrel_same_metas; try reflexivity; repeat split; reflexivity.
Qed.
Lemma pres_set_usage_of sc v : PRES (set_usage_of sc v).
Proof.
unfold set_usage_of. apply pres_modify. intros s. apply ntrel_same_metas; [reflexivity|]. repeat split; try reflexivity.
cbn. apply length_zset.
Qed.
Lemma pres_step_seq : PRES step_seq.
Proof.
unfold step_seq. apply pres_modify. intros s. destruct (st_seq s =? 255); apply ntrel_same_metas; try reflexivity; repeat split; reflexivity.
Qed.
Lemma pres_record_seq sc : PRES (record_seq sc).
Proof.
unfold record_seq. destruct (bounce_idx sc); [| apply pres_ret]. apply pres_modify. intros s. apply ntrel_same_metas; try reflexivity; repeat split; reflexivity.
Qed.
Lemma ntrel_upd_meta s p x :
(forall a, x = MUsed a -> exists a0, MT s p = Some (MUsed a0) /\ same_shape a0 a) ->
ntrel s (upd_meta p x s).
Proof.
intros Hx. split; [| repeat split; reflexivity].
intros q a H. rewrite MT_upd in H. destruct (sptr_eqb q p) eqn:E.
- apply sptr_eqb_eq in E. subst q. injection H as ->. exact (Hx a eq_refl).
- exists a. split; [exact H | apply same_shape_refl].
Qed.
Lemma setm_is_upd p am s : setm p am s = IRet (tt, upd_meta p (MUsed am) s).
Proof. reflexivity. Qed.
Lemma setslot_is_upd p x s : setslot p x s = IRet (tt, upd_meta p x s).
Proof. reflexivity. Qed.
Lemma pres_getm_setm p (F : ameta -> ameta) :
(forall am, same_shape am (F am)) -> PRES (bind (getm p) (fun am => setm p (F am))).
Proof.
intros HF s. unfold getm. unfold bind, get, ret, fail. cbn [ibind].
destruct (mlookup (st_metas s) p) as [[| |am]|] eqn:E; cbn [ibind]; try exact I.
rewrite setm_is_upd. cbn [tall snd]. apply ntrel_upd_meta. intros a Ha. injection Ha as <-.
exists am. split; [exact E | apply HF].
Qed.
Lemma pres_getm_setm_k {B} p (F : ameta -> ameta) (k : ameta -> unit -> M B) :
(forall am, same_shape am (F am)) -> (forall am u, PRES (k am u)) ->
PRES (bind (getm p) (fun am => bind (setm p (F am)) (k am))).
Proof.
intros HF Hk s. unfold getm. unfold bind, get, ret, fail. cbn [ibind].
destruct (mlookup (st_metas s) p) as [[| |am]|] eqn:E; cbn [ibind]; try exact I.
rewrite setm_is_upd. cbn [ibind].
eapply tall_mono; [| apply (Hk am tt)]. intros [b s2] H2. cbn [snd] in *.
eapply ntrel_trans; [| exact H2]. apply ntrel_upd_meta. intros a Ha. injection Ha as <-.
exists am. split; [exact E | apply HF].
Qed.
Lemma same_shape_set_links pr nx am : same_shape am (am_set_links pr nx am).
Proof. destruct am; repeat split; auto. Qed.
Lemma same_shape_set_freed m am : same_shape am (am_set_freed m am).
Proof. destruct am; repeat split; auto. Qed.
Lemma same_shape_set_avail m am : same_shape am (am_set_avail m am).
Proof. destruct am; repeat split; auto. Qed.
Lemma pres_set_links p pr nx : PRES (set_links p pr nx).
Proof.
intros s. unfold set_links, bind, get, fail. cbn [ibind].
destruct (mlookup (st_metas s) p) as [x|] eqn:E; cbn [ibind]; [| exact I].
rewrite setslot_is_upd. cbn [tall snd]. apply ntrel_upd_meta. intros a Ha.
destruct x as [| |am]; cbn in Ha; try discriminate. injection Ha as <-. exists am. split; [exact E | apply same_shape_set_links].
Qed.
Lemma pres_set_prev p pr : PRES (set_prev p pr).
Proof. unfold set_prev. apply pres_bind; [apply pres_get_links | intros; apply pres_set_links]. Qed.
Lemma pres_set_next p nx : PRES (set_next p nx).
Proof. unfold set_next. apply pres_bind; [apply pres_get_links | intros; apply pres_set_links]. Qed.
Lemma pres_queue h m : PRES (queue h m).
Proof.
unfold queue. apply pres_bind; [apply pres_get_links | intros l].
apply pres_bind; [apply pres_massert | intros _].
apply pres_bind; [apply pres_get_head | intros [head|]].
- apply pres_bind; [apply pres_get_links | intros lh]. destruct (fst lh); [| apply pres_fail].
apply pres_bind; [apply pres_set_links | intros _]. apply pres_bind; [apply pres_set_next | intros _]. apply pres_set_prev.
- apply pres_bind; [apply pres_set_links | intros _]. apply pres_set_head.
Qed.
Lemma pres_dequeue h m : PRES (dequeue h m).
Proof.
unfold dequeue. apply pres_bind; [apply pres_get_links | intros l].
apply pres_bind; [| intros _; apply pres_set_links].
destruct (osptr_eqb (snd l) (Some m)); [apply pres_set_head|].
destruct (fst l); [| apply pres_fail]. destruct (snd l); [| apply pres_fail].
apply pres_bind; [apply pres_set_next | intros _]. apply pres_bind; [apply pres_set_prev | intros _].
apply pres_bind; [apply pres_get_head | intros hd]. destruct (osptr_eqb hd (Some m)); [apply pres_set_head | apply pres_ret].
Qed.
Lemma pres_free_meta m : PRES (free_meta m).
Proof.
unfold free_meta. apply pres_bind; [| intros ?; apply pres_queue].
intros s. rewrite setslot_is_upd. cbn [tall snd]. apply ntrel_upd_meta. intros a Ha. discriminate.
Qed.
Lemma pres_activate_group m : PRES (activate_group m).
Proof.
intros s. unfold activate_group. unfold getm. unfold bind, get, ret, fail. cbn [ibind].
destruct (mlookup (st_metas s) m) as [[| |am]|] eqn:E; cbn [ibind]; try exact I.
unfold massert, ret, fail. destruct (am_avail am =? 0); cbn [ibind]; [| exact I].
rewrite setm_is_upd. cbn [ibind tall snd]. apply ntrel_upd_meta. intros a Ha. injection Ha as <-.
exists am. split; [exact E|]. eapply same_shape_trans; [apply same_shape_set_freed | apply same_shape_set_avail].
Qed.
Lemma nth_slot_upd_slot am i x j :
nth_slot (upd_slot am i x) j = if (Z.to_nat j =? Z.to_nat i)%nat && (Z.to_nat i <? length (am_slots am))%nat then x else nth_slot am j.
Proof.
unfold nth_slot, upd_slot, am_set_slots. destruct am; cbn. apply nth_lupd.
Qed.
Lemma pres_forget_frame g i : PRES (forget_frame g i).
Proof.
unfold forget_frame. apply pres_getm_setm. intros am. split; [destruct am; reflexivity|].
split; [destruct am; reflexivity|]. split; [destruct am; reflexivity|]. split; [destruct am; reflexivity|]. split; [destruct am; reflexivity|]. split.
- unfold upd_slot. destruct am; cbn. apply length_lupd.
- intros j f H. rewrite nth_slot_upd_slot in H.
destruct ((Z.to_nat j =? Z.to_nat i)%nat && (Z.to_nat i <? length (am_slots am))%nat); [cbn in H; discriminate | exact H].
Qed.
Theorem pres_nontrivial_free fuel : forall g i, PRES (nontrivial_free fuel g i).
Proof.
induction fuel as [|fuel IH]; intros g i; [intros s; exact I|].
cbn fix beta iota delta [nontrivial_free].
apply pres_bind; [apply pres_getm | intros am].
apply pres_bind_get. intros s0. cbn zeta.
destruct ((Z.lor (am_freed am) (am_avail am) + bit i =? ones (am_last am)) && okay_to_free s0 g am).
- apply pres_bind.
+ destruct (am_next am); [| apply pres_ret].
apply pres_bind; [apply pres_massert | intros _]. apply pres_bind; [apply pres_get_head | intros hd].
apply pres_bind; [apply pres_dequeue | intros _]. apply pres_bind; [apply pres_get_head | intros hd'].
destruct (osptr_eqb hd (Some g)); [| apply pres_ret]. destruct hd'; [| apply pres_ret].
apply pres_bind; [apply pres_activate_group | intros _; apply pres_ret].
+ intros _. apply pres_bind; [apply pres_getm | intros am'].
apply pres_bind; [destruct (am_sc am <? 48); [apply pres_set_usage_of | apply pres_ret] | intros _].
apply pres_bind; [| intros mi; apply pres_bind; [apply pres_free_meta | intros _; apply pres_ret]].
destruct (negb (am_maplen am' =? 0)).
* apply pres_bind; [apply pres_step_seq | intros _]. apply pres_bind; [apply pres_record_seq | intros _]. apply pres_ret.
* apply pres_bind; [apply pres_find_frame | intros pf]. apply pres_bind; [apply pres_getm | intros amp].
apply pres_bind; [apply pres_mcheck | intros _]. apply pres_bind; [apply pres_forget_frame | intros _]. apply IH.
- apply pres_bind.
+ destruct (Z.lor (am_freed am) (am_avail am) =? 0); [| apply pres_ret].
apply pres_bind; [apply pres_massert | intros _]. apply pres_bind; [apply pres_get_head | intros hd].
destruct (osptr_eqb hd (Some g)); [apply pres_ret | apply pres_queue].
+ intros _. apply (pres_getm_setm_k g (fun am' => am_set_freed (Z.lor (am_freed am') (bit i)) am') (fun _ _ => ret None)).
* intros am'. apply same_shape_set_freed.
* intros _ _. apply pres_ret.
Qed.
Corollary nontrivial_free_ntrel fuel g i s : tall (fun r => ntrel s (snd r)) (nontrivial_free fuel g i s).
Proof. apply pres_nontrivial_free. Qed.
Lemma frames_intro' s g am i fr :
List.NoDup (keys s) -> MT s g = Some (MUsed am) -> 0 <= i <= am_last am -> ss_fr (nth_slot am i) = Some fr ->
In (g, am, i, fr) (frames s).
Proof.
intros ND Mg Hi Hfr. unfold frames. apply in_flat_map. exists (g, am). split.
- apply (used_metas_iff s g am ND). exact Mg.
- apply in_flat_map. exists i. split; [apply In_zseq; lia|]. rewrite Hfr. left. reflexivity.
Qed.
Section e.
Variables (s0 s : astate).
Hypothesis R : ntrel s0 s.
Hypothesis ND0 : List.NoDup (keys s0).
Hypothesis ND : List.NoDup (keys s).
Lemma ntrel_frames q a i f :
In (q, a, i, f) (frames s) -> exists a0, In (q, a0, i, f) (frames s0) /\ same_shape a0 a.
Proof.
intros Hin. destruct (in_frames_inv s q a i f Hin) as (Hu & Hi & Hf).
apply (used_metas_iff s q a ND) in Hu. destruct (proj1 R q a Hu) as (a0 & H0 & SS).
exists a0. split; [| exact SS]. destruct SS as (_ & _ & _ & L & _ & _ & F).
apply frames_intro'; [exact ND0 | exact H0 | rewrite <- L; exact Hi | apply F; exact Hf].
Qed.
Lemma ntrel_used q a : In (q, a) (used_metas s) -> exists a0, In (q, a0) (used_metas s0) /\ same_shape a0 a.
Proof.
intros Hu. apply (used_metas_iff s q a ND) in Hu. destruct (proj1 R q a Hu) as (a0 & H0 & SS).
exists a0. split; [apply (used_metas_iff s0 q a0 ND0); exact H0 | exact SS].
Qed.
Lemma same_shape_tail_cells a0 a c : same_shape a0 a -> In c (group_tail_cells a) -> In c (group_tail_cells a0).
Proof.
intros SS Hc. pose proof (same_shape_stride _ _ SS) as ST. destruct SS as (M & S & Ia & L & P & N & F).
unfold group_tail_cells in *.
assert (EX : group_extent a = group_extent a0) by (unfold group_extent; rewrite ST, L; reflexivity).
assert (ESS : forall j, slot_start a j = slot_start a0 j) by (intros j; unfold slot_start; rewrite M, ST; reflexivity).
assert (ESE : forall j, slot_end a j = slot_end a0 j) by (intros j; unfold slot_end; rewrite ESS, ST; reflexivity).
destruct Hc as [<- | Hc]; [left; rewrite M, EX; reflexivity | right].
apply in_flat_map in Hc as (j & Hj & Hc). apply in_flat_map. exists j. rewrite <- L. split; [exact Hj|].
unfold frame_tail_cells in *. destruct (ss_fr (nth_slot a j)) as [f|] eqn:Ef; [| destruct Hc].
rewrite (F j f Ef). unfold reserved_of, frame_ptr in *. rewrite <- ST, <- ESS, <- ESE. exact Hc.
Qed.
Lemma ntrel_tail_cells c : In c (tail_cells s) -> In c (tail_cells s0).
Proof.
intros Hc. unfold tail_cells in *. apply in_flat_map in Hc as ([q a] & Hu & Hc). cbn [snd] in Hc.
destruct (ntrel_used q a Hu) as (a0 & Hu0 & SS). apply in_flat_map. exists (q, a0). split; [exact Hu0|]. cbn [snd].
eapply same_shape_tail_cells; eauto.
Qed.
Lemma ntrel_footprint : footprint s = footprint s0.
Proof. destruct R as [_ (Rg & _ & Ar & _)]. unfold footprint, region_of. rewrite Rg, Ar. reflexivity. Qed.
Lemma ntrel_live_bytes : live_bytes s = live_bytes s0.
Proof. destruct R as [_ (Rg & _)]. unfold live_bytes. rewrite Rg. reflexivity. Qed.
Lemma ntrel_nslots : nslots s = nslots s0.
Proof. destruct R as [_ (Rg & _)]. unfold nslots. rewrite Rg. reflexivity. Qed.
Lemma ntrel_region_of k : region_of s k = region_of s0 k.
Proof. destruct R as [_ (Rg & _)]. unfold region_of. rewrite Rg. reflexivity. Qed.
Lemma ntrel_span_ok : span_ok s0 -> span_ok s.
Proof.
intros SP. apply (span_ok_transfer s0 s SP). intros q a Hq. destruct (proj1 R q a Hq) as (a0 & H0 & (_ & S & Ia & L & _)).
exists q, a0. split; [exact H0|]. split; [exact Ia|]. split; [exact L | exact S].
Qed.
End e.
Lemma bounded_of_WF s :
WF s -> Z.of_nat (length (st_areas s)) < 2 ^ 36 -> 0 <= st_meta_alloc_shift s <= 40 -> bounded s.
Proof.
intros HW Har Hsh. pose proof (inv_ctx HW) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12).
split; [|split; [exact Hsh | exact Har]].
intros sc.
assert (Hnn : forall c, 0 <= usage_of s c).
{ intros c. unfold usage_of, znth. destruct (nth_in_or_default (Z.to_nat c) (st_usage s) 0) as [H|H]; [apply C5; exact H | rewrite H; lia]. }
split; [apply Hnn|].
assert (K : forall c, 0 <= c < 48 -> usage_of s c < 2 ^ 48).
{ intros c Hc. rewrite (inv_usage HW c Hc). unfold U0. pose proof (class_sum_le s c HW). pose proof (keys_le_areas s (inv_keys HW)).
unfold METAS_PER_AREA in *. nia. }
destruct (Z_lt_dec sc 0) as [Hneg|Hnneg].
- replace (usage_of s sc) with (usage_of s 0) by (unfold usage_of, znth; replace (Z.to_nat sc) with (Z.to_nat 0) by lia; reflexivity). apply K. lia.
- destruct (Z_lt_dec sc 48) as [Hlt|Hge]; [apply K; lia|].
unfold usage_of, znth. rewrite nth_overflow; [lia|]. rewrite C2. lia.
Qed.
End d.
