(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require Import MallocModel MallocInv MallocWfArith.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import MngRz2 MngBud.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint rbq {A : Type} (B : Z) (t : itree astate A) (Q : A -> Z -> Prop) {struct t} : Prop :=
  match t with
  | IRet r => Q r B
  | IAsk q _ k => CH q <= B /\ forall z, rbq (B - CH q) (k z) Q
  | IFail _ => True
  end.

Lemma rbq_mono : forall {A} (t : itree astate A) B (Q Q' : A -> Z -> Prop), (forall r b, Q r b -> Q' r b) -> rbq B t Q -> rbq B t Q'.
Proof.
  intros A t. induction t as [r | q s k IH | f]; intros B Q Q' HQ H; cbn [rbq] in *.
  - exact (HQ r B H).
  - destruct H as (H1 & H2). split; [exact H1|]. intros z. exact (IH z (B - CH q) Q Q' HQ (H2 z)).
  - exact I.
Qed.

Lemma rbq_bind : forall {A C} (t : itree astate A) (k : A -> itree astate C) B Q,
  rbq B t (fun r b => rbq b (k r) Q) -> rbq B (ibind t k) Q.
Proof.
  intros A C t. induction t as [r | q s c IH | f]; intros k B Q H; cbn [ibind rbq] in *.
  - exact H.
  - destruct H as (H1 & H2). split; [exact H1|]. intros z. exact (IH z k (B - CH q) Q (H2 z)).
  - exact I.
Qed.

Lemma rb_of_rbq : forall {A} (t : itree astate A) B Q, rbq B t Q -> rb CH B t.
Proof.
  intros A t. induction t as [r | q s k IH | f]; intros B Q H; cbn [rbq rb] in *; [exact I | | exact I].
  destruct H as (H1 & H2). split; [exact H1|]. intros z. exact (IH z (B - CH q) Q (H2 z)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition costM {A} (m : M A) (c : Z) : Prop :=
  0 <= c /\ forall s B, c <= B -> rbq B (m s) (fun _ b => B - c <= b).

Lemma costM_le : forall {A} (m : M A) c c', costM m c -> c <= c' -> costM m c'.
Proof.
  intros A m c c' (H0 & H) Hc. split; [lia|]. intros s B HB.
  eapply rbq_mono; [|exact (H s B ltac:(lia))]. intros r b Hb. cbv beta in *. lia.
Qed.

(* [comment removed for export] *)
Lemma costM_bind : forall {A C} (m : M A) (k : A -> M C) c1 c2, costM m c1 -> 0 <= c2 -> (forall a, costM (k a) c2) -> costM (bind m k) (c1 + c2).
Proof.
  intros A C m k c1 c2 (H10 & H1) H20 H2. split; [lia|]. intros s B HB. unfold bind. apply rbq_bind.
  eapply rbq_mono; [|exact (H1 s B ltac:(lia))]. intros [a s'] b Hb. cbv beta in Hb.
  destruct (H2 a) as (_ & H2'). eapply rbq_mono; [|exact (H2' s' b ltac:(lia))]. intros r b' Hb'. cbv beta in *. lia.
Qed.

Lemma costM_bind0 : forall {A C} (m : M A) (k : A -> M C) c, costM m 0 -> 0 <= c -> (forall a, costM (k a) c) -> costM (bind m k) c.
Proof. intros A C m k c H1 H0 H2. replace c with (0 + c) by ring. exact (costM_bind m k 0 c H1 H0 H2). Qed.

Lemma costM_bindc : forall {A C} (m : M A) (k : A -> M C) c1 c, costM m c1 -> c1 <= c -> (forall a, costM (k a) (c - c1)) -> costM (bind m k) c.
Proof. intros A C m k c1 c H1 Hc H2. replace c with (c1 + (c - c1)) by ring. apply costM_bind; [exact H1 | lia | exact H2]. Qed.

Lemma costM_ret : forall {A} (a : A) c, 0 <= c -> costM (ret a) c.
Proof. intros A a c H. split; [exact H|]. intros s B HB. cbn. lia. Qed.

Lemma costM_fail : forall {A} f c, 0 <= c -> costM (@fail A f) c.
Proof. intros A f c H. split; [exact H|]. intros s B HB. exact I. Qed.

Lemma costM_get : forall c, 0 <= c -> costM get c.
Proof. intros c H. split; [exact H|]. intros s B HB. cbn. lia. Qed.

Lemma costM_put : forall s' c, 0 <= c -> costM (put s') c.
Proof. intros s' c H. split; [exact H|]. intros s B HB. cbn. lia. Qed.

Lemma costM_modify : forall f c, 0 <= c -> costM (modify f) c.
Proof. intros f c H. split; [exact H|]. intros s B HB. cbn. lia. Qed.

Lemma costM_massert : forall b site c, 0 <= c -> costM (massert b site) c.
Proof. intros b site c H. unfold massert. destruct b; [apply costM_ret | apply costM_fail]; exact H. Qed.

Lemma costM_mcheck : forall b tag c, 0 <= c -> costM (mcheck b tag) c.
Proof. intros b tag c H. unfold mcheck. destruct b; [apply costM_ret | apply costM_fail]; exact H. Qed.

Lemma costM_ask : forall q c, CH q <= c -> costM (ask q) c.
Proof.
  intros q c H. pose proof (CH_nonneg q). split; [lia|]. intros s B HB. cbn [ask rbq]. split; [lia|]. intros z. cbn. lia.
Qed.

Lemma costM_askz : forall q c, CH q <= c -> costM (askz q) c.
Proof.
  intros q c H. pose proof (CH_nonneg q). split; [lia|]. intros s B HB. cbn [askz rbq]. split; [lia|]. intros z. cbn. lia.
Qed.

Lemma costM_bind_ask : forall {C} q (k : bool -> M C) c, CH q <= c -> (forall a, costM (k a) (c - CH q)) -> costM (bind (ask q) k) c.
Proof. intros C q k c H1 H2. apply (costM_bindc _ _ (CH q) c); [apply costM_ask; lia | exact H1 | exact H2]. Qed.

Lemma costM_bind_askz : forall {C} q (k : Z -> M C) c, CH q <= c -> (forall a, costM (k a) (c - CH q)) -> costM (bind (askz q) k) c.
Proof. intros C q k c H1 H2. apply (costM_bindc _ _ (CH q) c); [apply costM_askz; lia | exact H1 | exact H2]. Qed.

Lemma costM_nonneg : forall {A} (m : M A) c, costM m c -> 0 <= c.
Proof. intros A m c (H & _). exact H. Qed.

(* [comment removed for export] *)
Create HintDb costdb.
Ltac cM :=
  lazymatch goal with
  | |- costM (bind (ask ?q) ?k) ?c => apply costM_bind_ask; [cbn [CH]; unfold PGSZ; lia | intros ?; cM]
  | |- costM (bind (askz ?q) ?k) ?c => apply costM_bind_askz; [cbn [CH]; unfold PGSZ; lia | intros ?; cM]
  | |- costM (bind ?m ?k) ?c => first [ eapply costM_bindc; [solve [eauto with costdb] | cbn [CH]; unfold PGSZ; lia | intros ?; cM]
                                      | apply costM_bind0; [solve [cM] | cbn [CH]; unfold PGSZ; lia | intros ?; cM] ]
  | |- costM (ret _) _ => apply costM_ret; cbn [CH]; unfold PGSZ; lia
  | |- costM (fail _) _ => apply costM_fail; cbn [CH]; unfold PGSZ; lia
  | |- costM get _ => apply costM_get; cbn [CH]; unfold PGSZ; lia
  | |- costM (put _) _ => apply costM_put; cbn [CH]; unfold PGSZ; lia
  | |- costM (modify _) _ => apply costM_modify; cbn [CH]; unfold PGSZ; lia
  | |- costM (massert _ _) _ => apply costM_massert; cbn [CH]; unfold PGSZ; lia
  | |- costM (mcheck _ _) _ => apply costM_mcheck; cbn [CH]; unfold PGSZ; lia
  | |- costM (ask _) _ => apply costM_ask; cbn [CH]; unfold PGSZ; lia
  | |- costM (askz _) _ => apply costM_askz; cbn [CH]; unfold PGSZ; lia
  | |- costM (let _ := _ in _) _ => cbv zeta; cM
  | |- costM (if ?b then _ else _) _ => destruct b; cM
  | |- costM (match ?x with _ => _ end) _ => destruct x; cM
  | |- costM ?m ?c => first [ solve [eapply costM_le; [eauto with costdb | cbn [CH]; unfold PGSZ; lia]]
                            | let h := head_of m in unfold h; cM ]
  end
with head_of t := match t with ?f _ => head_of f | ?f => f end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma c_getm : forall p, costM (getm p) 0. Proof. intros p. unfold getm. cM. Qed.
Lemma c_setm : forall p am, costM (setm p am) 0. Proof. intros. unfold setm. cM. Qed.
Lemma c_setslot : forall p x, costM (setslot p x) 0. Proof. intros. unfold setslot. cM. Qed.
Lemma c_get_links : forall p, costM (get_links p) 0. Proof. intros. unfold get_links. cM. Qed.
Lemma c_set_links : forall p pr nx, costM (set_links p pr nx) 0. Proof. intros. unfold set_links. cM. Qed.
Lemma c_set_prev : forall p pr, costM (set_prev p pr) 0. Proof. intros. unfold set_prev. cM. Qed.
Lemma c_set_next : forall p nx, costM (set_next p nx) 0. Proof. intros. unfold set_next. cM. Qed.
Lemma c_get_head : forall h, costM (get_head h) 0. Proof. intros. unfold get_head. cM. Qed.
Lemma c_set_head : forall h v, costM (set_head h v) 0. Proof. intros. unfold set_head. cM. Qed.
Lemma c_get0 : costM get 0. Proof. apply costM_get. lia. Qed.
Global Hint Resolve c_get0 : costdb.
Global Hint Resolve c_getm c_setm c_setslot c_get_links c_set_links c_set_prev c_set_next c_get_head c_set_head : costdb.

Lemma c_queue : forall h m, costM (queue h m) 0. Proof. intros. unfold queue. cM. Qed.
Lemma c_dequeue : forall h m, costM (dequeue h m) 0. Proof. intros. unfold dequeue. cM. Qed.
Global Hint Resolve c_queue c_dequeue : costdb.
Lemma c_dequeue_head : forall h, costM (dequeue_head h) 0. Proof. intros. unfold dequeue_head. cM. Qed.
Lemma c_free_meta : forall m, costM (free_meta m) 0. Proof. intros. unfold free_meta. cM. Qed.
Lemma c_set_usage_of : forall sc v, costM (set_usage_of sc v) 0. Proof. intros. unfold set_usage_of. cM. Qed.
Lemma c_step_seq : costM step_seq 0. Proof. unfold step_seq. cM. Qed.
Lemma c_record_seq : forall sc, costM (record_seq sc) 0. Proof. intros. unfold record_seq. cM. Qed.
Lemma c_account_bounce : forall sc, costM (account_bounce sc) 0. Proof. intros. unfold account_bounce. cM. Qed.
Lemma c_decay_bounces : forall sc, costM (decay_bounces sc) 0. Proof. intros. unfold decay_bounces. cM. Qed.
Lemma c_new_region : forall k len, costM (new_region k len) 0. Proof. intros. unfold new_region. cM. Qed.
Lemma c_upd_region : forall r f, costM (upd_region r f) 0. Proof. intros. unfold upd_region. cM. Qed.
Global Hint Resolve c_dequeue_head c_free_meta c_set_usage_of c_step_seq c_record_seq c_account_bounce c_decay_bounces
  c_new_region c_upd_region : costdb.
Lemma c_activate_group : forall m, costM (activate_group m) 0. Proof. intros. unfold activate_group. cM. Qed.
Global Hint Resolve c_activate_group : costdb.
Lemma c_try_avail : forall sc, costM (try_avail sc) 0. Proof. intros. unfold try_avail. cM. Qed.
Lemma c_enframe : forall g idx n ctr k, costM (enframe g idx n ctr k) 0. Proof. intros. unfold enframe. cM. Qed.
Lemma c_install_group : forall m sc cnt aidx maplen mem sl, costM (install_group m sc cnt aidx maplen mem sl) 0.
Proof. intros. unfold install_group. cM. Qed.
Global Hint Resolve c_try_avail c_enframe c_install_group : costdb.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma c_area_from_brk : costM area_from_brk 12288. Proof. unfold area_from_brk. cM. Qed.
Lemma c_area_from_mmap : costM area_from_mmap 4096. Proof. unfold area_from_mmap. cM. Qed.
Lemma c_open_area : forall nu, costM (open_area nu) 4096.
Proof.
  intros nu. unfold open_area. apply costM_bind0; [cM | lia | intros s].
  apply (costM_bindc _ _ 4096); [destruct nu; cM | lia | intros ok; cM].
Qed.
Global Hint Resolve c_area_from_brk c_area_from_mmap c_open_area : costdb.

Lemma c_alloc_meta : costM alloc_meta 20480.
Proof.
  unfold alloc_meta. apply costM_bind0; [cM | lia | intros ?].
  apply costM_bind0; [cM | lia | intros fm]. destruct fm as [m|]; [cM|].
  apply costM_bind0; [cM | lia | intros s].
  apply (costM_bindc _ _ 20480); [| lia | intros ok; cM].
  destruct (0 <? st_avail_meta_count s); [cM|].
  apply (costM_bindc _ _ 12288); [exact c_area_from_brk | lia | intros nu].
  apply (costM_bindc _ _ 4096); [exact c_area_from_mmap | lia | intros rs].
  destruct rs; [eapply costM_le; [exact (c_open_area nu) | lia] | cM].
Qed.
Global Hint Resolve c_alloc_meta : costdb.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition PHI (size : Z) : Z := 2 ^ 20 + 4096 + 20480 * Z.max 1 (12 - Z.log2 size).

Lemma PHI_bounds : forall size, 16 <= size -> 2 ^ 20 + 4096 + 20480 <= PHI size <= 2 ^ 20 + 4096 + 20480 * 8.
Proof.
  intros size H. unfold PHI. assert (4 <= Z.log2 size) by (change 4 with (Z.log2 16); apply Z.log2_le_mono; lia). lia.
Qed.

Lemma nest_facts : forall sc u, 0 <= sc < 48 ->
  class_size sc * initial_cnt sc u + UNIT <= PGSZ / 2 ->
  let total := UNIT + initial_cnt sc u * class_size sc - IB in
  0 <= total < MMAP_THRESHOLD /\ 2 * class_size sc + 16 <= total + IB /\ class_size sc <= 2032.
Proof.
  intros sc u Hsc Hb total. destruct (initial_cnt_facts sc u Hsc) as (C1 & C2 & C3). pose proof (class_size_bounds sc Hsc) as (S1 & S2).
  assert (Hs : class_size sc <= 2032) by (change (PGSZ / 2) with 2048 in Hb; unfold UNIT in Hb; nia).
  pose proof (class_le_23 sc Hsc Hs) as H23. specialize (C3 ltac:(lia)).
  unfold total, UNIT, IB, MMAP_THRESHOLD. change (PGSZ / 2) with 2048 in Hb. unfold UNIT in Hb. nia.
Qed.

Lemma PHI_nest : forall size size', 16 <= size <= 2032 -> 2 * size <= size' -> 20480 + PHI size' <= PHI size.
Proof.
  intros size size' H1 H2. unfold PHI.
  assert (L1 : Z.log2 size + 1 <= Z.log2 size') by (rewrite Z.add_1_r, <- Z.log2_double by lia; apply Z.log2_le_mono; lia).
  assert (L2 : Z.log2 size < 11) by (apply Z.log2_lt_pow2; lia). lia.
Qed.

Theorem c_slot_group : forall fuel sc req, 0 <= sc < 48 -> 0 <= req -> req + IB <= class_size sc ->
  costM (alloc_slot fuel sc req) (PHI (class_size sc)) /\ costM (alloc_group fuel sc req) (PHI (class_size sc)).
Proof.
  induction fuel as [|f IH]; intros sc req Hsc Hr Hfit; pose proof (class_size_bounds sc Hsc) as (S1 & S2);
    pose proof (PHI_bounds (class_size sc) S1) as PB.
  - split; cbn [alloc_slot alloc_group]; apply costM_fail; lia.
  - split.
    + cbn [alloc_slot]. apply costM_bind0; [exact (c_try_avail sc) | lia | intros first].
      destruct (negb (first =? 0)); [apply costM_ret; lia|].
      apply (costM_bindc _ _ (PHI (class_size sc))); [exact (proj2 (IH sc req Hsc Hr Hfit)) | lia | intros og].
      destruct og; apply costM_ret; lia.
    + cbn [alloc_group]. apply (costM_bindc _ _ 20480); [exact c_alloc_meta | lia | intros om].
      destruct om as [m|]; [|apply costM_ret; lia].
      apply costM_bind0; [exact c_get0 | lia | intros s]. cbv zeta.
      destruct (initial_cnt_facts sc (usage_of s sc) Hsc) as (C1 & C2 & C3).
      destruct (PGSZ / 2 <? class_size sc * initial_cnt sc (usage_of s sc) + UNIT) eqn:Eb.
      * (* [comment removed for export] *)
        destruct (mmap_plan s sc req (initial_cnt sc (usage_of s sc)) (usage_of s sc)) as [cnt needed] eqn:Ep.
        destruct (mmap_plan_facts s sc req (initial_cnt sc (usage_of s sc)) (usage_of s sc) cnt needed Hsc C1 C2 Hr Hfit C3 Ep) as (_ & _ & _ & N1 & N2 & N3 & _).
        cbn [fst snd]. apply costM_bind0; [exact (c_account_bounce sc) | lia | intros _].
        apply costM_bind0; [exact c_step_seq | lia | intros _].
        apply costM_bind_ask; [cbn [CH]; rewrite (page_round_fixed needed N1); unfold PGSZ in *; lia | intros ok].
        replace (CH (KMmapRW needed)) with (needed + 4096) by (cbn [CH]; rewrite (page_round_fixed needed N1); unfold PGSZ in *; lia).
        cM.
      * (* [comment removed for export] *)
        apply Z.ltb_ge in Eb.
        destruct (nest_facts sc (usage_of s sc) Hsc ltac:(lia)) as (T1 & T2 & T3).
        set (total := UNIT + initial_cnt sc (usage_of s sc) * class_size sc - IB) in *.
        destruct (size_to_class_range total T1) as (J1 & J2).
        pose proof (PHI_nest (class_size sc) (class_size (size_to_class total)) ltac:(lia) ltac:(lia)) as PN.
        apply (costM_bindc _ _ (PHI (class_size (size_to_class total))));
          [exact (proj1 (IH (size_to_class total) total J1 ltac:(lia) J2)) | lia | intros idx].
        cM.
Qed.

Lemma c_alloc_slot_any : forall sc req, 0 <= sc < 48 -> 0 <= req -> req + IB <= class_size sc ->
  costM (alloc_slot NEST_FUEL sc req) (2 ^ 20 + 4096 + 20480 * 8).
Proof.
  intros sc req H1 H2 H3. pose proof (class_size_bounds sc H1) as (S1 & _).
  eapply costM_le; [exact (proj1 (c_slot_group NEST_FUEL sc req H1 H2 H3)) | exact (proj2 (PHI_bounds _ S1))].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem c_malloc : forall n, 0 <= n -> costM (malloc n) (n + 2 ^ 21).
Proof.
  intros n Hn. unfold malloc. destruct (size_overflows n); [apply costM_ret; lia|].
  destruct (MMAP_THRESHOLD <=? n) eqn:Ed.
  - (* [comment removed for export] *)
    pose proof (page_round_ge (n + IB + UNIT)) as G1. pose proof (page_round_lt (n + IB + UNIT)) as G2.
    apply costM_bind_ask; [cbn [CH]; unfold IB, UNIT, PGSZ in *; lia | intros ok].
    replace (CH (KMmapRW (n + IB + UNIT))) with (page_round (n + IB + UNIT) + 4096) by (cbn [CH]; unfold IB, UNIT, PGSZ in *; lia).
    destruct (negb ok); [apply costM_ret; unfold IB, UNIT, PGSZ in *; lia|].
    apply costM_bind0; [exact (c_new_region _ _) | unfold IB, UNIT, PGSZ in *; lia | intros r].
    apply costM_bind0; [exact c_step_seq | unfold IB, UNIT, PGSZ in *; lia | intros _].
    apply (costM_bindc _ _ 20480); [exact c_alloc_meta | unfold IB, UNIT, PGSZ in *; lia | intros og].
    assert (R0 : 0 <= n + 2 ^ 21 - (page_round (n + IB + UNIT) + 4096) - 20480) by (unfold IB, UNIT, PGSZ in *; lia).
    destruct og as [g|].
    + apply costM_bind0; [exact (c_setm _ _) | exact R0 | intros _]. apply costM_bind0; [exact c_get0 | exact R0 | intros s].
      apply costM_bind0; [apply costM_put; lia | exact R0 | intros _]. apply costM_bind0; [exact (c_enframe _ _ _ _ _) | exact R0 | intros p].
      apply costM_ret. exact R0.
    + apply costM_bind_ask; [cbn [CH]; exact R0 | intros _]. cbn [CH]. rewrite Z.sub_0_r.
      apply costM_bind0; [exact (c_upd_region _ _) | exact R0 | intros _]. apply costM_ret. exact R0.
  - (* [comment removed for export] *)
    apply Z.leb_gt in Ed. destruct (size_to_class_range n ltac:(lia)) as (K1 & K2).
    apply costM_bind0; [exact c_get0 | lia | intros s].
    match goal with |- costM (bind (match nth (Z.to_nat ?sc) _ _ with _ => _ end) _) _ =>
      assert (SCF : 0 <= sc < 48 /\ n + IB <= class_size sc);
      [ repeat match goal with |- context [if ?b then _ else _] => destruct b eqn:? end;
        repeat match goal with H : (_ && _) = true |- _ => apply andb_prop in H as [? ?] end;
        repeat match goal with H : (_ <? _) = true |- _ => apply Z.ltb_lt in H end;
        first [ split; [exact K1 | exact K2]
              | split; [lia | eapply Z.le_trans; [exact K2 | apply class_size_mono; lia]] ]
      | remember sc as SC eqn:ESC ] end.
    destruct SCF as (SC1 & SC2).
    apply costM_bind0; [destruct (nth (Z.to_nat SC) (st_active s) None); cM | lia | intros r].
    apply (costM_bindc _ _ (2 ^ 20 + 4096 + 20480 * 8)); [| lia | intros gi; cM].
    destruct r as [gi|]; [cM|].
    apply (costM_bindc _ _ (2 ^ 20 + 4096 + 20480 * 8)); [exact (c_alloc_slot_any SC n SC1 Hn SC2) | lia | intros idx; cM].
Qed.

(* [comment removed for export] *)
Theorem rb_malloc : forall n s, 0 <= n -> rb CH (n + 2 ^ 21) (malloc n s).
Proof.
  intros n s Hn. destruct (c_malloc n Hn) as (_ & H). exact (rb_of_rbq _ _ _ (H s (n + 2 ^ 21) ltac:(lia))).
Qed.
