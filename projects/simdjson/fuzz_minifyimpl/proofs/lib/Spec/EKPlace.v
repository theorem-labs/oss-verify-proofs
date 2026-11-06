(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Cfg MmEd NodesEd.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad MSafe STree Malloc KInv KStep PState KLink KEv Relim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition LIM : Z := 2^34.            (* [comment removed for export] *)
Definition CORR : Z := 2^35.           (* [comment removed for export] *)
Definition ABASE : Z := 3 * 2^44.      (* [comment removed for export] *)
Definition ARENA (c : Z) : Z := ABASE + (c - 12) * 2^35.
Definition cls (n : Z) : Z := Z.log2_up n.
Definition esz (e : word * word) : Z := bv_unsigned (snd e).

Lemma ABASE_40 : 2^40 <= ABASE. Proof. unfold ABASE. lia. Qed.
(* [comment removed for export] *)
Lemma ARENA_top : ARENA 34 + 2^35 <= alloc_ceiling_lo.
Proof. rewrite alloc_ceiling_lo_val. unfold ARENA, ABASE. lia. Qed.
Lemma ARENA_top_TASK_SIZE : ARENA 34 + 2^35 <= TASK_SIZE.
Proof. rewrite TASK_SIZE_val. unfold ARENA, ABASE. lia. Qed.

Definition slab_entry (e : word * word) : Prop :=
  exists c i, 12 <= c <= 34 /\ 0 <= i < 2^(35 - c) /\ elo e = ARENA c + i * 2^c /\ 2^(c-1) < esz e <= 2^c.
Definition in_corr (b0 : Z) (e : word * word) : Prop := b0 <= elo e /\ ehi e <= b0 + CORR.
Definition NICE (b0 : Z) (maps : list (word * word)) : Prop :=
  (forall e, In e maps -> in_corr b0 e \/ slab_entry e) /\ 0 < b0 /\ b0 + CORR <= 2^40.

Lemma ehi_elo : forall e, ehi e = elo e + esz e. Proof. intros [a n]. reflexivity. Qed.

Lemma cls_bounds : forall n, PGSZ <= n <= LIM -> 12 <= cls n <= 34 /\ 2^(cls n - 1) < n <= 2^(cls n).
Proof.
  intros n Hn. unfold cls, PGSZ, LIM in *.
  pose proof (Z.log2_up_spec n ltac:(lia)) as [H1 H2]. rewrite <- Z.sub_1_r in H1.
  split; [|lia]. split.
  - pose proof (Z.log2_up_le_mono (2^12) n ltac:(lia)) as H. rewrite Z.log2_up_pow2 in H by lia. lia.
  - apply (proj1 (Z.log2_up_le_pow2 n 34 ltac:(lia))). lia.
Qed.

Lemma pow35_split : forall c, 0 <= c <= 35 -> 2^35 = 2^(35-c) * 2^c.
Proof. intros c Hc. rewrite <- Z.pow_add_r by lia. f_equal. lia. Qed.

Lemma ARENA_mono : forall c c', c < c' -> ARENA c + 2^35 <= ARENA c'.
Proof. intros. unfold ARENA. nia. Qed.

Lemma ARENA_lo : forall c, 12 <= c -> ABASE <= ARENA c.
Proof. intros. unfold ARENA. nia. Qed.

(* [comment removed for export] *)
Fixpoint zremove1 (x : Z) (l : list Z) : list Z :=
  match l with [] => [] | y :: l' => if y =? x then l' else y :: zremove1 x l' end.
Lemma zremove1_length : forall x l, In x l -> length (zremove1 x l) = (length l - 1)%nat.
Proof.
  induction l as [|y l IH]; intros Hin; [destruct Hin|]. cbn. destruct (Z.eqb_spec y x); [cbn; lia|].
  destruct Hin as [->|Hin]; [contradiction|]. cbn. rewrite IH by exact Hin. destruct l; [destruct Hin| cbn; lia].
Qed.
Lemma zremove1_In : forall x z l, In z l -> z <> x -> In z (zremove1 x l).
Proof.
  induction l as [|y l IH]; intros Hin Hne; [destruct Hin|]. cbn. destruct (Z.eqb_spec y x).
  - destruct Hin as [->|Hin]; [contradiction| exact Hin].
  - destruct Hin as [->|Hin]; [left; reflexivity| right; apply IH; assumption].
Qed.
Lemma pigeon : forall N (l : list Z), (length l < N)%nat -> exists i, 0 <= i < Z.of_nat N /\ ~ In i l.
Proof.
  induction N as [|N IH]; intros l Hl; [lia|].
  destruct (in_dec Z.eq_dec (Z.of_nat N) l) as [Hin|Hnin].
  - destruct (IH (zremove1 (Z.of_nat N) l)) as (i & Hi & Hni); [rewrite zremove1_length by exact Hin; destruct l; [destruct Hin| cbn [length] in *; lia]|].
    exists i. split; [lia|]. intros Hin'. apply Hni. apply zremove1_In; [exact Hin'| lia].
  - exists (Z.of_nat N). split; [lia| exact Hnin].
Qed.

(* [comment removed for export] *)
Lemma live_bytes_filter_le : forall f l, live_bytes (List.filter f l) <= live_bytes l.
Proof.
  induction l as [|[a n] l IH]; cbn; [lia|]. pose proof (bv_unsigned_in_range 64 n). destruct (f (a, n)); cbn; lia.
Qed.
Lemma live_bytes_lower : forall l m, (forall e, In e l -> m < esz e) -> Z.of_nat (length l) * m <= live_bytes l - Z.of_nat (length l).
Proof.
  induction l as [|[a n] l IH]; intros m H; cbn -[Z.of_nat]; [lia|].
  specialize (IH m (fun e He => H e (or_intror He))). pose proof (H (a, n) (or_introl eq_refl)) as Hn. unfold esz in Hn; cbn in Hn.
  rewrite Nat2Z.inj_succ. nia.
Qed.

Definition in_arena (c : Z) (e : word * word) : bool := (ARENA c <=? elo e) && (elo e <? ARENA c + 2^35).
Definition slot_idx (c : Z) (e : word * word) : Z := (elo e - ARENA c) / 2^c.

Lemma slab_in_arena : forall b0 e c, 0 < b0 -> b0 + CORR <= 2^40 -> 12 <= c <= 34 -> elo e < ehi e ->
  in_corr b0 e \/ slab_entry e -> in_arena c e = true ->
  exists i, 0 <= i < 2^(35-c) /\ elo e = ARENA c + i * 2^c /\ 2^(c-1) < esz e <= 2^c.
Proof.
  intros b0 e c Hb0 Hc0 Hc Hpos [Hcor|(c' & i & Hc' & Hi & He & Hsz)] Ha; unfold in_arena in Ha; apply andb_prop in Ha as [A1 A2]; apply Z.leb_le in A1; apply Z.ltb_lt in A2.
  - exfalso. destruct Hcor as [C1 C2]. pose proof (ARENA_lo c ltac:(lia)). pose proof ABASE_40. unfold CORR in *. pose proof (ehi_elo e). pose proof (bv_unsigned_in_range 64 (snd e)). unfold esz in *. nia.
  - assert (c' = c).
    { destruct (Z.lt_total c' c) as [Hlt|[Heq|Hgt]]; [| exact Heq |]; exfalso.
      + pose proof (ARENA_mono c' c Hlt). assert (i * 2^c' < 2^35); [|lia].
        rewrite (pow35_split c') by lia. apply Z.mul_lt_mono_pos_r; [apply Z.pow_pos_nonneg|]; lia.
      + pose proof (ARENA_mono c c' Hgt). assert (0 <= i * 2^c') by (apply Z.mul_nonneg_nonneg; [lia| apply Z.pow_nonneg; lia]). lia. }
    subst c'. exists i. auto.
Qed.

Lemma free_slot : forall b0 maps n,
  NICE b0 maps -> (forall e, In e maps -> elo e < ehi e) -> live_bytes maps + n <= LIM -> PGSZ <= n ->
  let c := cls n in
  exists i, 0 <= i < 2^(35 - c) /\
    forall e, In e maps -> ehi e <= ARENA c + i * 2^c \/ ARENA c + i * 2^c + n <= elo e.
Proof.
  intros b0 maps n (Hn1 & Hb0 & Hc40) Hwf Hlive Hpg c.
  pose proof (live_bytes_nonneg maps) as Hnn.
  pose proof (cls_bounds n ltac:(unfold LIM in *; lia)) as [Hc Hsz]. fold c in Hc, Hsz.
  set (E := List.filter (in_arena c) maps).
  set (idx := map (slot_idx c) E).
  assert (HE : forall e, In e E -> exists i, 0 <= i < 2^(35-c) /\ elo e = ARENA c + i * 2^c /\ 2^(c-1) < esz e <= 2^c).
  { intros e He. apply filter_In in He as [He Ha]. eapply (slab_in_arena b0); eauto. }
  assert (Hlen : (length idx < Z.to_nat (2^(35-c)))%nat).
  { unfold idx. rewrite length_map.
    pose proof (live_bytes_lower E (2^(c-1)) ltac:(intros e He; destruct (HE e He) as (i & _ & _ & H); lia)) as HL.
    pose proof (live_bytes_filter_le (in_arena c) maps) as HF. fold E in HF.
    assert (Hp : 2^34 = 2^(35-c) * 2^(c-1)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    assert (0 < 2^(c-1)) by (apply Z.pow_pos_nonneg; lia). assert (0 < 2^(35-c)) by (apply Z.pow_pos_nonneg; lia).
    unfold LIM in Hlive. nia. }
  destruct (pigeon (Z.to_nat (2^(35-c))) idx Hlen) as (i & Hi & Hni). rewrite Z2Nat.id in Hi by (apply Z.pow_nonneg; lia).
  exists i. split; [exact Hi|]. intros e He.
  assert (Hpc : 0 < 2^c) by (apply Z.pow_pos_nonneg; lia).
  assert (Hslot : ARENA c + i * 2^c + n <= ARENA c + 2^35).
  { assert (i * 2^c + 2^c <= 2^35); [|lia]. rewrite (pow35_split c) by lia. nia. }
  destruct (in_arena c e) eqn:Ha.
  - destruct (HE e ltac:(apply filter_In; auto)) as (j & Hj & Hej & Hszj).
    assert (Hji : j <> i).
    { intros ->. apply Hni. unfold idx. apply in_map_iff. exists e. split; [|apply filter_In; auto].
      unfold slot_idx. rewrite Hej. replace (ARENA c + i * 2^c - ARENA c) with (i * 2^c) by lia. rewrite Z.div_mul by lia. reflexivity. }
    rewrite ehi_elo, Hej. destruct (Z.lt_total j i) as [Hlt|[Heq|Hgt]]; [left| contradiction| right]; nia.
  - unfold in_arena in Ha. destruct (Hn1 e He) as [[C1 C2]|(c' & j & Hc' & Hj & Hej & Hszj)].
    + left. pose proof (ARENA_lo c ltac:(lia)). pose proof ABASE_40. unfold CORR in *. nia.
    + assert (c' <> c).
      { intros ->. apply Bool.andb_false_iff in Ha. destruct Ha as [Ha|Ha]; [apply Z.leb_gt in Ha| apply Z.ltb_ge in Ha]; [nia|].
        assert (j * 2^c < 2^35); [|lia]. rewrite (pow35_split c) by lia. apply Z.mul_lt_mono_pos_r; lia. }
      rewrite ehi_elo, Hej. destruct (Z.lt_total c' c) as [Hlt|[Heq|Hgt]]; [left| contradiction| right].
      * pose proof (ARENA_mono c' c Hlt). assert (j * 2^c' + 2^c' <= 2^35); [|lia].
        rewrite (pow35_split c') by lia. assert (0 < 2^c') by (apply Z.pow_pos_nonneg; lia). nia.
      * pose proof (ARENA_mono c c' Hgt). assert (0 <= j * 2^c') by (apply Z.mul_nonneg_nonneg; [lia| apply Z.pow_nonneg; lia]). lia.
Qed.

Lemma slab_entry_lo : forall e, slab_entry e -> 2^40 <= elo e.
Proof.
  intros e (c & i & Hc & Hi & He & _). rewrite He. pose proof (ARENA_lo c ltac:(lia)). pose proof ABASE_40.
  assert (0 <= i * 2^c) by (apply Z.mul_nonneg_nonneg; [lia| apply Z.pow_nonneg; lia]). lia.
Qed.

Lemma ARENA_aligned : forall c i, 12 <= c -> 0 <= i -> (ARENA c + i * 2^c) mod 4096 = 0.
Proof.
  intros c i Hc Hi. unfold ARENA, ABASE.
  assert (E : 2^c = 2^(c-12) * 4096). { change 4096 with (2^12). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  rewrite E. replace (3 * 2^44 + (c - 12) * 2 ^ 35 + i * (2 ^ (c - 12) * 4096)) with ((3 * 2^32 + (c - 12) * 2^23 + i * 2^(c-12)) * 4096) by lia.
  apply Z_mod_mult.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma live_bytes_cons : forall e l, live_bytes (e :: l) = esz e + live_bytes l.
Proof. intros [a n] l. reflexivity. Qed.

Lemma live_bytes_perm : forall l l', Permutation l l' -> live_bytes l = live_bytes l'.
Proof.
  intros l l' HP. induction HP; [reflexivity| | |lia].
  - rewrite !live_bytes_cons. lia.
  - rewrite !live_bytes_cons. lia.
Qed.

Lemma vmwf_incl : forall l l', vmwf l -> (forall e, In e l' -> In e l) -> List.NoDup l' -> vmwf l'.
Proof.
  intros l l' [Hb Hp] Hi Hnd. split; [intros e He; apply Hb; auto|].
  induction l' as [|e l' IH]; [constructor|]. inversion Hnd; subst. constructor.
  - intros e' He'. destruct (pwdisj_In l e e' Hp (Hi e (or_introl eq_refl)) (Hi e' (or_intror He'))) as [->|D]; [contradiction| exact D].
  - apply IH; [intros x Hx; apply Hi; right; exact Hx| assumption].
Qed.

Lemma vmwf_nodup : forall l, vmwf l -> List.NoDup l.
Proof.
  intros l [Hb Hp]. induction l as [|e l IH]; [constructor|]. inversion Hp; subst. constructor.
  - intros Hin. pose proof (H1 e Hin) as D. pose proof (Hb e (or_introl eq_refl)). unfold edisj in D. lia.
  - apply IH; [intros x Hx; apply Hb; right; exact Hx| assumption].
Qed.

Lemma vmwf_perm : forall l l', Permutation l l' -> vmwf l -> vmwf l'.
Proof.
  intros l l' HP Hw. eapply vmwf_incl; [exact Hw| intros e He; eapply Permutation_in; [apply Permutation_sym; exact HP| exact He]|].
  eapply Permutation_NoDup; [exact HP| apply vmwf_nodup; exact Hw].
Qed.

Lemma vmwf_tail : forall e l, vmwf (e :: l) -> vmwf l.
Proof. intros e l [Hb Hp]. inversion Hp; subst. split; [intros x Hx; apply Hb; right; exact Hx| assumption]. Qed.

Lemma vmwf_app_l : forall l1 l2, vmwf (l1 ++ l2) -> vmwf l1.
Proof.
  intros l1 l2 Hw. eapply vmwf_incl; [exact Hw| intros e He; apply in_or_app; left; exact He|].
  apply vmwf_nodup in Hw. apply List.NoDup_app_remove_r in Hw. exact Hw.
Qed.
Lemma vmwf_app_r : forall l1 l2, vmwf (l1 ++ l2) -> vmwf l2.
Proof.
  intros l1 l2 Hw. eapply vmwf_incl; [exact Hw| intros e He; apply in_or_app; right; exact He|].
  apply vmwf_nodup in Hw. apply List.NoDup_app_remove_l in Hw. exact Hw.
Qed.

(* [comment removed for export] *)
Lemma live_bytes_remove : forall maps a n, vmwf maps -> In (a, n) maps ->
  live_bytes (map_remove maps a) = live_bytes maps - bv_unsigned n.
Proof.
  induction maps as [|[a0 n0] maps IH]; intros a n Hw Hin; [destruct Hin|].
  pose proof (vmwf_tail _ _ Hw) as Hw'. destruct Hw as [Hb Hp]. inversion Hp; subst.
  unfold map_remove. cbn [List.filter fst]. destruct Hin as [E|Hin].
  - injection E as -> ->. rewrite bv_eqb_refl. cbn [negb]. rewrite live_bytes_cons. unfold esz; cbn [snd].
    enough (List.filter (fun p : word * word => negb (bv_eqb (fst p) a)) maps = maps) as -> by lia.
    apply List.forallb_filter_id. apply forallb_forall. intros [a' n'] Hin'. cbn [fst].
    destruct (bv_eqb a' a) eqn:E; [|reflexivity]. apply bv_eqb_eq in E. subst a'. exfalso.
    pose proof (H1 _ Hin') as D. pose proof (Hb (a, n) (or_introl eq_refl)). pose proof (Hb (a, n') (or_intror Hin')). unfold edisj, elo, ehi in *. cbn in *. lia.
  - destruct (bv_eqb a0 a) eqn:E.
    + apply bv_eqb_eq in E. subst a0. exfalso.
      pose proof (H1 _ Hin) as D. pose proof (Hb (a, n0) (or_introl eq_refl)). pose proof (Hb (a, n) (or_intror Hin)). unfold edisj, elo, ehi in *. cbn in *. lia.
    + cbn [negb]. rewrite !live_bytes_cons. fold (map_remove maps a). rewrite (IH a n Hw' Hin). lia.
Qed.

(* [comment removed for export] *)
Lemma live_bytes_iv_subtract_in : forall a sz lo hi,
  bv_unsigned a <= lo -> lo < hi -> hi <= bv_unsigned a + bv_unsigned sz -> bv_unsigned a + bv_unsigned sz <= 2^64 ->
  live_bytes (iv_subtract a sz lo hi) = bv_unsigned sz - (hi - lo).
Proof.
  intros a sz lo hi H1 H2 H3 H4. unfold iv_subtract.
  pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 sz). unfold bv_modulus in *.
  destruct (Z.ltb_spec (bv_unsigned a) lo); destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); cbn -[Z.min Z.max Z_to_bv bv_unsigned Z.sub Z.add];
    rewrite ?unsigned_lit by lia; lia.
Qed.

Lemma maps_subtract_disjoint_id : forall maps lo hi, vmwf maps -> lo < hi ->
  (forall e, In e maps -> ehi e <= lo \/ hi <= elo e) -> maps_subtract maps lo hi = maps.
Proof.
  induction maps as [|[a sz] maps IH]; intros lo hi Hw Hlh Hd; [reflexivity|]. cbn.
  pose proof (proj1 Hw (a, sz) (or_introl eq_refl)) as W. unfold elo, ehi in W; cbn in W.
  rewrite iv_subtract_disjoint; [| lia| exact Hlh| specialize (Hd (a, sz) (or_introl eq_refl)); unfold elo, ehi in Hd; cbn in Hd; lia].
  cbn. f_equal. apply IH; [eapply vmwf_tail; exact Hw| exact Hlh| intros e He; apply Hd; right; exact He].
Qed.

Lemma live_bytes_subtract : forall maps lo n, vmwf maps -> 0 < bv_unsigned n -> bv_unsigned lo + bv_unsigned n <= 2^64 ->
  map_contains maps lo n = true ->
  live_bytes (maps_subtract maps (bv_unsigned lo) (bv_unsigned lo + bv_unsigned n)) = live_bytes maps - bv_unsigned n.
Proof.
  intros maps lo n Hw Hn Hb Hc.
  unfold map_contains in Hc. apply existsb_exists in Hc as ([a0 s0] & Hin & Hc). apply andb_prop in Hc as [C1 C2]. apply Z.leb_le in C1. apply Z.leb_le in C2. cbn [fst snd] in C1, C2.
  revert Hw Hin. induction maps as [|[a sz] maps IH]; intros Hw Hin; [destruct Hin|].
  pose proof (vmwf_tail _ _ Hw) as Hw'. destruct Hw as [Hbd Hp]. inversion Hp; subst. cbn [maps_subtract]. rewrite live_bytes_app, !live_bytes_cons. unfold esz; cbn [snd].
  destruct Hin as [E|Hin].
  - injection E as -> ->. pose proof (Hbd (a0, s0) (or_introl eq_refl)) as W. unfold elo, ehi in W; cbn in W.
    rewrite live_bytes_iv_subtract_in by lia.
    rewrite maps_subtract_disjoint_id; [lia| exact Hw'| lia|].
    intros e He. pose proof (H1 e He) as D. unfold edisj, elo, ehi in D |- *. cbn in D. lia.
  - pose proof (H1 _ Hin) as D. pose proof (Hbd (a, sz) (or_introl eq_refl)) as W. unfold edisj, elo, ehi in D, W; cbn in D, W.
    rewrite iv_subtract_disjoint; [| lia| lia| lia]. rewrite live_bytes_cons. unfold esz; cbn [snd].
    rewrite (IH Hw' Hin). cbn [live_bytes]. lia.
Qed.

Lemma maps_subtract_app : forall l1 l2 lo hi, maps_subtract (l1 ++ l2) lo hi = maps_subtract l1 lo hi ++ maps_subtract l2 lo hi.
Proof. induction l1 as [|[a n] l1 IH]; intros; cbn; [reflexivity|]. rewrite IH, app_assoc. reflexivity. Qed.

Lemma maps_subtract_flat_map : forall l lo hi, maps_subtract l lo hi = flat_map (fun e => iv_subtract (fst e) (snd e) lo hi) l.
Proof. induction l as [|[a n] l IH]; intros; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma maps_subtract_perm : forall l l' lo hi, Permutation l l' -> Permutation (maps_subtract l lo hi) (maps_subtract l' lo hi).
Proof. intros. rewrite !maps_subtract_flat_map. apply Permutation_flat_map. assumption. Qed.

Lemma live_bytes_ge_elem : forall e l, In e l -> esz e <= live_bytes l.
Proof.
  induction l as [|e' l IH]; intros Hin; [destruct Hin|]. rewrite live_bytes_cons. pose proof (live_bytes_nonneg l).
  destruct Hin as [<-|Hin]; [lia|]. specialize (IH Hin). pose proof (bv_unsigned_in_range 64 (snd e')). unfold esz in *. lia.
Qed.

Lemma Permutation_filter {A} : forall (f : A -> bool) l l', Permutation l l' -> Permutation (List.filter f l) (List.filter f l').
Proof.
  intros f l l' HP. induction HP; cbn.
  - constructor.
  - destruct (f x); [apply perm_skip|]; assumption.
  - destruct (f x), (f y); try apply perm_swap; try apply perm_skip; try apply Permutation_refl.
  - eapply Permutation_trans; eauto.
Qed.

Lemma filter_id {A} : forall (f : A -> bool) l, (forall x, In x l -> f x = true) -> List.filter f l = l.
Proof.
  induction l as [|x l IH]; intros H; cbn; [reflexivity|]. rewrite (H x (or_introl eq_refl)). f_equal. apply IH. intros y Hy. apply H. right. exact Hy.
Qed.

Lemma region_free_intro : forall maps aw nw,
  (forall e, In e maps -> ehi e <= bv_unsigned aw \/ bv_unsigned aw + bv_unsigned nw <= elo e) -> region_free maps aw nw = true.
Proof.
  induction maps as [|[e sz] maps IH]; intros aw nw H; [reflexivity|]. cbn [region_free].
  rewrite IH by (intros e' He'; apply H; right; exact He'). unfold iv_overlap.
  specialize (H (e, sz) (or_introl eq_refl)). unfold elo, ehi in H; cbn in H.
  destruct H as [H|H].
  - replace (bv_unsigned aw <? bv_unsigned e + bv_unsigned sz) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
  - replace (bv_unsigned e <? bv_unsigned aw + bv_unsigned nw) with false by (symmetry; apply Z.ltb_ge; lia). rewrite andb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma backing_le_live_minv : forall mo, minv mo -> vm_backing_used mo <= vm_live_bytes (m_vmmaps mo).
Proof. intros mo Hmi. apply backing_le_live; apply Hmi. Qed.

Lemma vm_only_tables : forall m m', vm_only m m' -> m_fds m' = m_fds m /\ m_fs m' = m_fs m.
Proof. intros m m' (F & _ & S & _). unfold m_fds, m_fs. rewrite F, S. auto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma listNN_eqb_refl : forall l, listNN_eqb l l = true.
Proof. intros l. apply listNN_eqb_eq. reflexivity. Qed.

(* [comment removed for export] *)
Lemma nstep_brk_intro : forall req mo r,
  let h := m_vmmaps mo in
  brk_r_ok mo (Z_to_bv 64 req) r = true ->
  mm_ns (NBrk req) mo (mkEffectU r [] (brk_zeros (Z_to_bv 64 req) r (vm_brk h)) (brk_unmaps r (vm_brk h)) [] []) ->
  nstep (NBrk req) mo (mkEffectU r [] (brk_zeros (Z_to_bv 64 req) r (vm_brk h)) (brk_unmaps r (vm_brk h)) [] [])
        (with_brk_next mo (Z_to_bv 64 req) r) [].
Proof.
  intros req mo r h Hr Hns. apply nstep_brk_iff. split; [|exact Hns].
  unfold check_brk. fold h. rewrite Hr, !listNN_eqb_refl. reflexivity.
Qed.

Lemma brk_r_ok_refuse : forall mo req, brk_r_ok mo req (vm_brk (m_vmmaps mo)) = true.
Proof.
  intros mo req. unfold brk_r_ok.
  destruct (w_is0 req || (bv_unsigned req <? bv_unsigned (min_brk (m_vmmaps mo)))); [apply bv_eqb_refl|].
  destruct (bv_unsigned req <? bv_unsigned (vm_brk (m_vmmaps mo))); [rewrite bv_eqb_refl; apply orb_true_r|].
  rewrite bv_eqb_refl, orb_true_r. cbn [andb]. unfold brk_grow_ok, brk_budget_ok. rewrite Z.ltb_irrefl, andb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma brk_r_ok_grant : forall mo req,
  let h := m_vmmaps mo in let b := bv_unsigned (vm_brk h) in
  bv_unsigned (vm_start_brk h) <= b -> 0 < b -> b < req < 2^64 - 4096 -> b mod 4096 = 0 -> req mod 4096 = 0 ->
  req <= alloc_top h ->
  region_free (vm_reserved h ++ vm_maps h) (vm_brk h) (Z_to_bv 64 (req + 4096 - b)) = true ->
  vm_backing_used mo + (req - b) <= vm_limit h ->
  brk_r_ok mo (Z_to_bv 64 req) (Z_to_bv 64 req) = true.
Proof.
  intros mo req h b Hs Hb Hreq Hba Hra Hc Hrf Hl. pose proof (alloc_top_lt h) as HT. unfold two_pow_64 in HT.
  unfold brk_r_ok. fold h. rewrite w_is0_lit by lia. replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  unfold min_brk. rewrite unsigned_lit by lia. replace (req <? bv_unsigned (vm_start_brk h)) with false by (symmetry; apply Z.ltb_ge; lia).
  fold b. replace (req <? b) with false by (symmetry; apply Z.ltb_ge; lia). cbn [orb]. rewrite bv_eqb_refl. cbn [orb andb].
  unfold brk_grow_ok, brk_budget_ok. fold h. rewrite unsigned_lit by lia. fold b.
  replace (0 <? b) with true by (symmetry; apply Z.ltb_lt; lia). replace (b <? req) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb].
  unfold page_round_up_Z. rewrite page_size_eq.
  replace ((b + 4096 - 1) / 4096 * 4096) with b.
  2:{ pose proof (Z_div_mod_eq_full b 4096). pose proof (Z_div_mod_eq_full (b+4096-1) 4096). pose proof (Z.mod_pos_bound (b+4096-1) 4096). nia. }
  replace ((req + 4096 - 1) / 4096 * 4096) with req.
  2:{ pose proof (Z_div_mod_eq_full req 4096). pose proof (Z_div_mod_eq_full (req+4096-1) 4096). pose proof (Z.mod_pos_bound (req+4096-1) 4096). nia. }
  replace (b <? req) with true by (symmetry; apply Z.ltb_lt; lia).
  rewrite (proj2 (Z.leb_le _ _) Hc). subst b. rewrite Z_to_bv_bv_unsigned, Hrf. cbn [andb].
  assert (Hsub : bv_unsigned (Z_to_bv 64 req - vm_brk h)%bv = req - bv_unsigned (vm_brk h)).
  { rewrite bv_sub_unsigned, unsigned_lit by lia. apply bv_wrap_small. unfold bv_modulus. lia. }
  rewrite Hsub. apply Z.leb_le. exact Hl.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma nstep_mmap_ok_intro : forall len prot mo a,
  let h := m_vmmaps mo in let n := mmap_len len in
  0 < len < 2^63 -> (prot = PROT_NONE \/ prot = PROT_RW) ->
  0 < a -> a mod 4096 = 0 -> a + n <= alloc_top h ->
  region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 a) (Z_to_bv 64 n) = true ->
  vm_backing_used mo + n <= vm_limit h ->
  nstep (NMmap 0 len prot MAPF) mo
        (mkEffectU (Z_to_bv 64 a) [] (if prot =? PROT_NONE then [] else [(Z_to_bv 64 a, Z_to_bv 64 n)])
                                  (if prot =? PROT_NONE then [(Z_to_bv 64 a, Z_to_bv 64 n)] else []) [] [])
        (with_vmmaps (mkVmMapsFull (vm_reserved h) ((Z_to_bv 64 a, Z_to_bv 64 n) :: vm_maps h)
                        (if prot =? PROT_NONE then (Z_to_bv 64 a, Z_to_bv 64 n) :: vm_noaccess h else vm_noaccess h)
                        (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) mo) [].
Proof.
  intros len prot mo a h n Hlen Hp Ha Hal Hc Hrf Hl. pose proof (alloc_top_lt h) as HT. unfold two_pow_64 in HT.
  pose proof (mmap_len_ge len ltac:(lia)) as Hn. fold n in Hn.
  apply nstep_mmap_of_ed; [reflexivity|]. unfold check_mmap_ed.
  change (negb (mmap_off_aligned_b (Z_to_bv 64 0))) with false. change (negb (mmap_anon_b (Z_to_bv 64 MAPF))) with false. cbv iota.
  rewrite w_is0_lit by lia. replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  assert (Herr : forall b, errno_ret_in (mmap_errnos_when b) (Z_to_bv 64 a) = false).
  { intros [|]; [|reflexivity]. cbn [mmap_errnos_when].
    destruct (errno_ret_in mmap_errnos (Z_to_bv 64 a)) eqn:E; [|reflexivity]. apply errno_ret_in_true in E as (e & He & E).
    cbn in He. destruct He as [<-|[]]. apply (f_equal bv_unsigned) in E. rewrite unsigned_lit in E by lia. rewrite errno_ret_unsigned in E by (unfold ENOMEM; lia). unfold two_pow_64, ENOMEM in E. lia. }
  assert (TAIL : forall noacc,
    (if (bv_unsigned (Z_to_bv 64 a) mod page_size =? 0) && (0 <? bv_unsigned (Z_to_bv 64 a)) && (bv_unsigned (Z_to_bv 64 a) + page_round_up_Z (bv_unsigned (Z_to_bv 64 len)) <=? alloc_top h)
        && region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 a) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (Z_to_bv 64 len))))
        && listNN_eqb [(Z_to_bv 64 a, Z_to_bv 64 (page_round_up_Z (bv_unsigned (Z_to_bv 64 len))))] [(Z_to_bv 64 a, Z_to_bv 64 (page_round_up_Z (bv_unsigned (Z_to_bv 64 len))))]
     then CheckOk (with_mmap_backing (Z_to_bv 64 MAPF) (Z_to_bv 64 a) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (Z_to_bv 64 len))))
            (with_vmmaps (mkVmMapsFull (vm_reserved h) ((Z_to_bv 64 a, Z_to_bv 64 (page_round_up_Z (bv_unsigned (Z_to_bv 64 len)))) :: vm_maps h) noacc
                            (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) mo)) []
     else CheckReject)
    = CheckOk (with_vmmaps (mkVmMapsFull (vm_reserved h) ((Z_to_bv 64 a, Z_to_bv 64 n) :: vm_maps h) noacc
                             (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) mo) []).
  { intros noacc. rewrite !unsigned_lit by lia. fold (mmap_len len). fold n. rewrite page_size_eq, Hal, Z.eqb_refl.
    rewrite (proj2 (Z.ltb_lt 0 a) Ha). rewrite (proj2 (Z.leb_le _ _) Hc), Hrf, listNN_eqb_refl. cbn [andb].
    rewrite with_mmap_backing_plain by reflexivity. reflexivity. }
  assert (Hbud : mmap_noreserve_backed_ok (Z_to_bv 64 MAPF) mo (page_round_up_Z (bv_unsigned (Z_to_bv 64 len))) = true).
  { rewrite mmap_noreserve_backed_ok_plain by reflexivity. rewrite unsigned_lit by lia. fold (mmap_len len) n h. apply Z.leb_le. exact Hl. }
  destruct Hp as [-> | ->].
  - change (mmap_modeled_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 MAPF) (Z_to_bv 64 0)) with false.
    change (mmap_noaccess_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 MAPF) (Z_to_bv 64 0)) with true. cbv iota beta.
    change (PROT_NONE =? PROT_NONE) with true. cbv iota. fold h. cbv zeta. rewrite Herr.
    rewrite <- (TAIL ((Z_to_bv 64 a, Z_to_bv 64 n) :: vm_noaccess h)). rewrite !unsigned_lit by lia. reflexivity.
  - change (mmap_modeled_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 MAPF) (Z_to_bv 64 0)) with true. cbv iota beta.
    change (PROT_RW =? PROT_NONE) with false. cbv iota. fold h. cbv zeta. rewrite Herr. rewrite Hbud.
    rewrite <- (TAIL (vm_noaccess h)). rewrite !unsigned_lit by lia. cbn [andb].
    destruct ((a mod page_size =? 0) && (0 <? a) && (a + page_round_up_Z len <=? alloc_top h) && region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 a) (Z_to_bv 64 (page_round_up_Z len))); reflexivity.
Qed.

(* [comment removed for export] *)
Section Fixed.
Variables (a : Z) (mo : Model).
Let h := m_vmmaps mo.
Let aw := Z_to_bv 64 a.
Let nw := Z_to_bv 64 PGSZ.
Hypothesis Ha : 0 < a.
Hypothesis Hc : a + PGSZ <= alloc_top h.   (* [comment removed for export] *)
Hypothesis Hal : a mod 4096 = 0.
Hypothesis Hrf : region_free (vm_reserved h) aw nw = true.
Hypothesis Hmc : map_contains (vm_maps h) aw nw = true.

Definition fixed_done_h : VmMaps :=
  mkVmMapsFull (vm_reserved h) (vm_maps h) ((aw, nw) :: maps_subtract (vm_noaccess h) a (a + PGSZ))
               (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).

(* [comment removed for export] *)
Lemma check_mmap_fixed_gate : forall eff,
  check_mmap_ed aw nw (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 MAPFX) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eff mo =
  match eff with
  | mkEffectU r [] [] us [] [] =>
      if bv_eqb r aw && listNN_eqb us [(aw, nw)]
      then CheckOk (with_mmap_replacement (Z_to_bv 64 MAPFX) aw nw (with_vmmaps fixed_done_h mo)) []
      else CheckReject
  | _ => CheckReject
  end.
Proof.
  intros eff. pose proof (alloc_top_lt h) as HT. unfold two_pow_64 in HT. unfold check_mmap_ed.
  change (negb (mmap_off_aligned_b (Z_to_bv 64 0))) with false. change (negb (mmap_anon_b (Z_to_bv 64 MAPFX))) with false.
  change (w_is0 nw) with false.
  change (mmap_modeled_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 MAPFX) (Z_to_bv 64 0)) with false.
  change (mmap_noaccess_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 MAPFX) (Z_to_bv 64 0)) with false.
  change (mmap_fixed_noaccess_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 MAPFX) (Z_to_bv 64 0)) with true. cbv iota beta.
  assert (Un : bv_unsigned nw = PGSZ) by (subst nw; apply unsigned_lit; unfold PGSZ; lia). rewrite Un. change (page_round_up_Z PGSZ) with PGSZ. cbv zeta.
  assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; unfold PGSZ in *; lia). rewrite Ua.
  replace (two_pow_64 <=? a + PGSZ) with false by (symmetry; apply Z.leb_gt; unfold two_pow_64, PGSZ in *; lia).
  fold h. replace (a + PGSZ <=? alloc_top h) with true by (symmetry; apply Z.leb_le; lia). cbn [negb].
  rewrite page_size_eq, Hal. cbn [Z.eqb negb]. replace (0 <? a) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb].
  fold nw. fold h. rewrite Hrf, Hmc. cbn [andb]. rewrite Un.
  destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity]. destruct zs; [|reflexivity].
  destruct cs; [|destruct us; reflexivity]. destruct ci; [|destruct us; reflexivity].
  change (mmap_errnos_when false) with (@nil Z). change mmap_destructive_errnos with (@nil Z).
  cbn [errno_ret_in existsb andb]. reflexivity.
Qed.

Lemma nstep_fixed_done_intro :
  nstep (NMmap a PGSZ PROT_NONE MAPFX) mo (mkEffectU aw [] [] [(aw, nw)] [] [])
        (with_mmap_replacement (Z_to_bv 64 MAPFX) aw nw (with_vmmaps fixed_done_h mo)) [].
Proof.
  apply nstep_mmap_of_ed; [reflexivity|]. fold aw nw. rewrite check_mmap_fixed_gate.
  rewrite bv_eqb_refl, listNN_eqb_refl. reflexivity.
Qed.
Lemma m_vmmaps_fixed_done : m_vmmaps (with_mmap_replacement (Z_to_bv 64 MAPFX) aw nw (with_vmmaps fixed_done_h mo)) = fixed_done_h.
Proof. rewrite with_mmap_replacement_plain by reflexivity. rewrite m_vmmaps_vm_forget_range. apply m_vmmaps_with_vmmaps. Qed.
Lemma vm_only_fixed_done : vm_only mo (with_mmap_replacement (Z_to_bv 64 MAPFX) aw nw (with_vmmaps fixed_done_h mo)).
Proof.
  apply (vm_only_trans _ (with_vmmaps fixed_done_h mo)); [apply vm_only_with_vmmaps; reflexivity|]. apply vm_only_replacement_off. reflexivity.
Qed.
End Fixed.

(* [comment removed for export] *)
Definition munmap_h (h : VmMaps) (aw nw : word) : VmMaps :=
  mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) aw) (maps_subtract (vm_noaccess h) (bv_unsigned aw) (bv_unsigned aw + bv_unsigned nw))
               (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).

(* [comment removed for export] *)
Lemma nstep_munmap_intro : forall a len mo,
  let h := m_vmmaps mo in let n := mmap_len len in let aw := Z_to_bv 64 a in let nw := Z_to_bv 64 n in
  0 <= a -> a mod 4096 = 0 -> 0 < len -> a + n <= TASK_SIZE ->
  map_has (vm_maps h) aw nw = true ->
  nstep (NMunmap a len) mo (mkEffectU (Z_to_bv 64 0) [] [] [(aw, nw)] [] [])
        (with_mmap_destroyed aw nw (munmap_h h aw nw) mo) [].
Proof.
  intros a len mo h n aw nw Ha Hal Hlen Hb Hhas. pose proof (mmap_len_ge len Hlen) as Hn. fold n in Hn. pose proof TASK_SIZE_val as TS.
  apply nstep_munmap_iff. unfold check_munmap. fold aw h.
  assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; lia). rewrite Ua, page_size_eq, Hal.
  rewrite w_is0_lit by lia. replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [Z.eqb negb orb]. cbv zeta.
  rewrite (unsigned_lit len) by lia. fold (mmap_len len). fold n nw.
  replace (TASK_SIZE <? a + n) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite Hhas. change (w_is0 (Z_to_bv 64 0)) with true. rewrite listNN_eqb_refl. cbn [andb]. unfold munmap_h. rewrite Ua. reflexivity.
Qed.

Lemma m_vmmaps_munmap : forall aw nw h mo, m_vmmaps (with_mmap_destroyed aw nw (munmap_h h aw nw) mo) = munmap_h h aw nw.
Proof. intros. apply m_vmmaps_with_mmap_destroyed. Qed.

(* [comment removed for export] *)
Section Mprotect.
Variables (a : Z) (mo : Model).
Let h := m_vmmaps mo.
Let aw := Z_to_bv 64 a.
Let nw := Z_to_bv 64 PGSZ.
Hypothesis Ha : 0 <= a.
Hypothesis Hb : a + PGSZ < 2^64.
Hypothesis Hal : a mod 4096 = 0.
Hypothesis Hcn : map_contains (vm_noaccess h) aw nw = true.
Hypothesis Hcm : map_contains (vm_maps h) aw nw = true.

Lemma check_mprotect_gate : forall eff,
  check_mprotect_ed aw nw (Z_to_bv 64 PROT_RW) eff mo =
  match eff with
  | mkEffectU r [] zs [] [] [] =>
      if errno_ret_in (mprotect_errnos_when (mprotect_refusable mo aw nw)) r   (* [comment removed for export] *)
      then match zs with [] => CheckOk mo [] | _ => CheckReject end
      else if mprotect_budget_ok mo aw nw && w_is0 r && listNN_eqb zs [(aw, nw)]
      then CheckOk (mprotect_model_next mo aw nw) []
      else CheckReject
  | _ => CheckReject
  end.
Proof.
  intros eff. unfold check_mprotect_ed.
  change (mprotect_grows_conflict_b (Z_to_bv 64 PROT_RW)) with false. change (mprotect_modeled_b (Z_to_bv 64 PROT_RW)) with true.
  assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; unfold PGSZ in *; lia). rewrite Ua, page_size_eq, Hal.
  change (w_is0 nw) with false. cbv iota. cbn [Z.eqb negb].
  assert (Un : bv_unsigned nw = PGSZ) by (subst nw; apply unsigned_lit; unfold PGSZ; lia). rewrite Un. change (page_round_up_Z PGSZ) with PGSZ.
  replace (two_pow_64 <=? a + PGSZ) with false by (symmetry; apply Z.leb_gt; unfold two_pow_64; lia). cbv zeta. fold nw h. rewrite Hcn, Hcm. reflexivity.
Qed.

Lemma nstep_mprotect_ok_intro :
  vm_live_bytes h <= vm_limit h -> minv mo ->
  nstep (NMprotect a PGSZ PROT_RW) mo (mkEffectU (Z_to_bv 64 0) [] [(aw, nw)] [] [] [])
        (mprotect_model_next mo aw nw) [].
Proof.
  intros Hl Hmi. apply nstep_mprotect_of_ed. fold aw nw. rewrite check_mprotect_gate.
  assert (Herr : forall b, errno_ret_in (mprotect_errnos_when b) (Z_to_bv 64 0) = false).
  { intros [|]; [|reflexivity]. cbn [mprotect_errnos_when].
    destruct (errno_ret_in mprotect_errnos (Z_to_bv 64 0)) eqn:E; [|reflexivity]. apply errno_ret_in_true in E as (e & He & E).
    cbn in He. destruct He as [<-|[]]. apply (f_equal bv_unsigned) in E. rewrite unsigned_lit in E by lia.
    rewrite errno_ret_unsigned in E by (unfold ENOMEM; lia). unfold two_pow_64, ENOMEM in E. lia. }
  assert (Hbud : mprotect_budget_ok mo aw nw = true).
  { unfold mprotect_budget_ok, vm_backing_within_limit. apply Z.leb_le.
    eapply Z.le_trans; [apply backing_le_live| ].
    - unfold mprotect_model_next. rewrite m_vm_lazy_with_vmmaps. apply Hmi.
    - unfold mprotect_model_next. rewrite m_vm_materialized_with_vmmaps. apply Hmi.
    - unfold mprotect_model_next. rewrite m_vmmaps_with_vmmaps. cbn [vm_limit]. unfold vm_live_bytes in *. cbn [vm_maps]. exact Hl. }
  rewrite Herr, Hbud. change (w_is0 (Z_to_bv 64 0)) with true. rewrite listNN_eqb_refl. reflexivity.
Qed.

Lemma m_vmmaps_mprotect_next : m_vmmaps (mprotect_model_next mo aw nw) =
  mkVmMapsFull (vm_reserved h) (vm_maps h) (maps_subtract (vm_noaccess h) a (a + PGSZ))
               (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).
Proof.
  unfold mprotect_model_next. rewrite m_vmmaps_with_vmmaps. fold h.
  rewrite (unsigned_lit a) by (unfold PGSZ in *; lia). subst nw. rewrite (unsigned_lit PGSZ) by (unfold PGSZ; lia). reflexivity.
Qed.
End Mprotect.
