From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import disco_table_c disco_table memcpy_c memcpy_same_c
  reac_disco_table_age_c.
Import ListNotations.
Open Scope Z_scope.

Lemma list_ext_nth : forall (l1 l2 : list byte), length l1 = length l2 ->
  (forall j, (j < length l1)%nat -> nth_error l1 j = nth_error l2 j) -> l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros l2 L H; destruct l2 as [|y l2]; cbn in L; try discriminate.
  - reflexivity.
  - pose proof (H 0%nat ltac:(cbn; lia)) as H0. cbn in H0. inversion H0; subst y.
    f_equal. apply IH; [lia|]. intros j Hj. specialize (H (S j)). cbn in H. apply H. lia.
Qed.

Lemma nth_sub : forall X a l j, 0 <= a -> (j < l)%nat -> nth_error (sub X a l) j = nth_error X (Z.to_nat a + j).
Proof. intros. unfold sub. rewrite nth_firstn by lia. apply nth_skipn. Qed.

Lemma nth_upd : forall X k v j, 0 <= k -> k + Z.of_nat (length v) <= Z.of_nat (length X) -> (j < length X)%nat ->
  nth_error (upd X k v) j =
  if ((Z.to_nat k <=? j)%nat && (j <? Z.to_nat k + length v)%nat)%bool then nth_error v (j - Z.to_nat k)
  else nth_error X j.
Proof. intros. unfold upd. apply upd_bytes_nth; lia. Qed.

Lemma length_upd : forall X k v, 0 <= k -> k + Z.of_nat (length v) <= Z.of_nat (length X) ->
  length (upd X k v) = length X.
Proof. intros. unfold upd. apply upd_bytes_length. lia. Qed.

Ltac nth_cases :=
  repeat match goal with
  | |- context [(?a <=? ?b)%nat] => destruct (Nat.leb_spec a b)
  | |- context [(?a <? ?b)%nat] => destruct (Nat.ltb_spec a b)
  end; cbn [andb].

Lemma sub_upd_out : forall X k v a l, 0 <= k -> 0 <= a -> k + Z.of_nat (length v) <= Z.of_nat (length X) ->
  a + Z.of_nat l <= Z.of_nat (length X) -> a + Z.of_nat l <= k \/ k + Z.of_nat (length v) <= a ->
  sub (upd X k v) a l = sub X a l.
Proof.
  intros X k v a l Hk Ha Hv Hl Hd.
  assert (LU : length (upd X k v) = length X) by (apply length_upd; lia).
  apply list_ext_nth.
  - rewrite !length_sub by (rewrite ?LU; lia). reflexivity.
  - intros j Hj. rewrite length_sub in Hj by (rewrite ?LU; lia). rewrite !nth_sub by lia.
    rewrite nth_upd by lia. nth_cases; try reflexivity; lia.
Qed.

Lemma sub_upd_in : forall X k v, 0 <= k -> k + Z.of_nat (length v) <= Z.of_nat (length X) ->
  sub (upd X k v) k (length v) = v.
Proof.
  intros X k v Hk Hv. assert (LU : length (upd X k v) = length X) by (apply length_upd; lia).
  apply list_ext_nth.
  - rewrite length_sub; [reflexivity|lia|rewrite LU; lia].
  - intros j Hj. rewrite length_sub in Hj by (rewrite ?LU; lia). rewrite nth_sub by lia.
    rewrite nth_upd by lia. nth_cases; try lia. f_equal. lia.
Qed.

Lemma upd_comm : forall X a u b v, 0 <= a -> 0 <= b -> a + Z.of_nat (length u) <= Z.of_nat (length X) ->
  b + Z.of_nat (length v) <= Z.of_nat (length X) -> a + Z.of_nat (length u) <= b \/ b + Z.of_nat (length v) <= a ->
  upd (upd X a u) b v = upd (upd X b v) a u.
Proof.
  intros X a u b v Ha Hb Hu Hv Hd.
  assert (L1 : length (upd X a u) = length X) by (apply length_upd; lia).
  assert (L2 : length (upd X b v) = length X) by (apply length_upd; lia).
  apply list_ext_nth.
  - rewrite (length_upd (upd X a u)) by (rewrite ?L1; lia). rewrite (length_upd (upd X b v)) by (rewrite ?L2; lia).
    rewrite L1, L2. reflexivity.
  - intros j Hj. rewrite (length_upd (upd X a u)) in Hj by (rewrite ?L1; lia). rewrite L1 in Hj.
    rewrite !nth_upd by (rewrite ?L1, ?L2; lia).
    nth_cases; try reflexivity; lia.
Qed.

Lemma upd_upd : forall X k u v, 0 <= k -> k + Z.of_nat (length u) <= Z.of_nat (length X) -> length v = length u ->
  upd (upd X k u) k v = upd X k v.
Proof.
  intros X k u v Hk Hu Hl.
  assert (L1 : length (upd X k u) = length X) by (apply length_upd; lia).
  apply list_ext_nth.
  - rewrite (length_upd (upd X k u)) by (rewrite ?L1; lia). rewrite L1. symmetry. apply length_upd; rewrite ?Hl; lia.
  - intros j Hj. rewrite (length_upd (upd X k u)) in Hj by (rewrite ?L1; lia). rewrite L1 in Hj.
    rewrite !nth_upd by (rewrite ?L1; lia).
    nth_cases; try reflexivity; lia.
Qed.

Lemma upd_self : forall X k l, 0 <= k -> k + Z.of_nat l <= Z.of_nat (length X) -> upd X k (sub X k l) = X.
Proof.
  intros X k l Hk Hl. assert (LS : length (sub X k l) = l) by (apply length_sub; lia).
  apply list_ext_nth.
  - apply length_upd; rewrite ?LS; lia.
  - intros j Hj. rewrite length_upd in Hj by (rewrite ?LS; lia).
    rewrite nth_upd by (rewrite ?LS; lia). rewrite LS.
    nth_cases; try reflexivity. rewrite nth_sub by lia. f_equal. lia.
Qed.

Lemma sub_sub : forall X a l b l', 0 <= a -> 0 <= b -> a + Z.of_nat l <= Z.of_nat (length X) ->
  b + Z.of_nat l' <= Z.of_nat l -> sub (sub X a l) b l' = sub X (a + b) l'.
Proof.
  intros X a l b l' Ha Hb Hl Hl'.
  assert (LS : length (sub X a l) = l) by (apply length_sub; lia).
  apply list_ext_nth.
  - rewrite !length_sub by (rewrite ?LS; lia). reflexivity.
  - intros j Hj. rewrite length_sub in Hj by (rewrite ?LS; lia).
    rewrite !nth_sub by lia. f_equal. lia.
Qed.

Lemma sub_frame : forall A T a l, 0 <= a -> a + Z.of_nat l <= Z.of_nat (length T) -> length A = length T ->
  (forall k, a <= k < a + Z.of_nat l -> nth_error A (Z.to_nat k) = nth_error T (Z.to_nat k)) ->
  sub A a l = sub T a l.
Proof.
  intros A T a l Ha Hl LA H. apply list_ext_nth.
  - rewrite !length_sub by lia. reflexivity.
  - intros j Hj. rewrite length_sub in Hj by lia. rewrite !nth_sub by lia.
    replace (Z.to_nat a + j)%nat with (Z.to_nat (a + Z.of_nat j)) by lia. apply H. lia.
Qed.

Lemma ent_sub : forall A j o l, length A = 400%nat -> 0 <= j < 8 -> 0 <= o -> o + Z.of_nat l <= 48 ->
  sub A (48 * j + o) l = sub (entry_of A j) o l.
Proof. intros A j o l LA Hj Ho Hl. unfold entry_of. rewrite sub_sub by (rewrite ?LA; lia). reflexivity. Qed.

Lemma ent_eq_sub : forall A B i j o l, length A = 400%nat -> length B = 400%nat -> 0 <= i < 8 -> 0 <= j < 8 ->
  0 <= o -> o + Z.of_nat l <= 48 -> entry_of A i = entry_of B j -> sub A (48 * i + o) l = sub B (48 * j + o) l.
Proof. intros A B i j o l LA LB Hi Hj Ho Hl E. rewrite !ent_sub by (assumption || lia). rewrite E. reflexivity. Qed.

Lemma stale_ent : forall A B i j now, length A = 400%nat -> length B = 400%nat -> 0 <= i < 8 -> 0 <= j < 8 ->
  entry_of A i = entry_of B j -> disco_stale A i now = disco_stale B j now.
Proof.
  intros A B i j now LA LB Hi Hj E. unfold disco_stale, last_of, u_at.
  rewrite (ent_eq_sub A B i j 40 8) by (assumption || lia). reflexivity.
Qed.

Lemma fields_ent : forall A B i j, length A = 400%nat -> length B = 400%nat -> 0 <= i < 8 -> 0 <= j < 8 ->
  entry_of A i = entry_of B j ->
  mac_of A i = mac_of B j /\ role_of_e A i = role_of_e B j /\ hd_of A i = hd_of B j /\ din_of A i = din_of B j /\
  dout_of A i = dout_of B j /\ owned_of A i = owned_of B j.
Proof.
  intros A B i j LA LB Hi Hj E.
  pose proof (ent_eq_sub A B i j 0 6 LA LB Hi Hj ltac:(lia) ltac:(lia) E) as M. rewrite !Z.add_0_r in M.
  unfold mac_of, role_of_e, hd_of, din_of, dout_of, owned_of, s32_at, u_at.
  rewrite M, (ent_eq_sub A B i j 8 4), (ent_eq_sub A B i j 12 1), (ent_eq_sub A B i j 13 1),
    (ent_eq_sub A B i j 14 1), (ent_eq_sub A B i j 24 4) by (assumption || lia).
  repeat split.
Qed.

Lemma entry_upd_same : forall A i e, length A = 400%nat -> 0 <= i < 8 -> length e = 48%nat ->
  entry_of (upd A (48 * i) e) i = e.
Proof.
  intros A i e LA Hi Le. unfold entry_of.
  pose proof (sub_upd_in A (48 * i) e ltac:(lia) ltac:(rewrite Le, LA; lia)) as S. rewrite Le in S. exact S.
Qed.

Lemma entry_upd_other : forall A i j e, length A = 400%nat -> 0 <= i < 8 -> 0 <= j < 8 -> i <> j ->
  length e = 48%nat -> entry_of (upd A (48 * i) e) j = entry_of A j.
Proof. intros A i j e LA Hi Hj Hij Le. unfold entry_of. apply sub_upd_out; rewrite ?Le, ?LA; lia. Qed.

Lemma entry_upd_hi : forall A j k v, length A = 400%nat -> 0 <= j < 8 -> 384 <= k ->
  k + Z.of_nat (length v) <= 400 -> entry_of (upd A k v) j = entry_of A j.
Proof. intros A j k v LA Hj Hk Hv. unfold entry_of. apply sub_upd_out; rewrite ?LA; lia. Qed.

Lemma n_of_upd_out : forall A k v, length A = 400%nat -> 0 <= k -> k + Z.of_nat (length v) <= 400 ->
  k + Z.of_nat (length v) <= 384 \/ 388 <= k -> n_of (upd A k v) = n_of A.
Proof. intros A k v LA Hk Hv Hd. unfold n_of, s32_at, u_at. rewrite sub_upd_out by (rewrite ?LA; lia). reflexivity. Qed.

Lemma seq_of_upd_out : forall A k v, length A = 400%nat -> 0 <= k -> k + Z.of_nat (length v) <= 400 ->
  k + Z.of_nat (length v) <= 392 \/ 396 <= k -> seq_of (upd A k v) = seq_of A.
Proof. intros A k v LA Hk Hv Hd. unfold seq_of, u_at. rewrite sub_upd_out by (rewrite ?LA; lia). reflexivity. Qed.

Lemma n_of_set : forall A m, length A = 400%nat -> 0 <= m < 2^31 -> n_of (upd A 384 (le4 (Z_to_bv 64 m))) = m.
Proof.
  intros A m LA Hm. unfold n_of, s32_at, u_at.
  pose proof (sub_upd_in A 384 (le4 (Z_to_bv 64 m)) ltac:(lia) ltac:(rewrite length_le4, LA; lia)) as S.
  rewrite length_le4 in S. rewrite S, bytes_le_to_Z_le4, unsigned_lit by lia.
  rewrite Z.mod_small by lia. apply swrap32_small. lia.
Qed.

Lemma seq_range : forall T, 0 <= seq_of T < 2^32.
Proof.
  intros T. unfold seq_of, u_at. pose proof (ble_range (sub T 392 4)) as H.
  destruct (Nat.leb_spec (length (sub T 392 4)) 4).
  - assert (2 ^ (8 * Z.of_nat (length (sub T 392 4))) <= 2^32) by (apply Z.pow_le_mono_r; lia). lia.
  - unfold sub in *. rewrite length_firstn in *. lia.
Qed.

Lemma seq_of_set : forall B s, length B = 400%nat -> 0 <= s < 2^32 ->
  seq_of (upd B 392 (le4 (Z_to_bv 64 (s + 1)))) = (s + 1) mod 2^32.
Proof.
  intros B s LB Hs. unfold seq_of, u_at.
  pose proof (sub_upd_in B 392 (le4 (Z_to_bv 64 (s + 1))) ltac:(lia) ltac:(rewrite length_le4, LB; lia)) as S.
  rewrite length_le4 in S. rewrite S, bytes_le_to_Z_le4, unsigned_lit by lia. reflexivity.
Qed.

Lemma upd_n_self : forall T, length T = 400%nat -> upd T 384 (le4 (Z_to_bv 64 (n_of T))) = T.
Proof.
  intros T L. unfold n_of, s32_at, u_at.
  rewrite <- lw_val by (apply length_sub; lia).
  rewrite le4_lw by (apply length_sub; lia).
  apply upd_self; rewrite ?L; lia.
Qed.

Lemma le4_eq_mod : forall v w : word, bv_unsigned v mod 2^32 = bv_unsigned w mod 2^32 -> le4 v = le4 w.
Proof.
  intros v w H. apply le4_of_mod32; [apply length_le4|].
  rewrite <- bytes_le_to_Z_le_val, bytes_le_to_Z_le4. exact H.
Qed.

Lemma age_count_ext : forall f g k, (forall j, 0 <= j < Z.of_nat k -> f j = g j) -> age_count f k = age_count g k.
Proof.
  intros f g. induction k as [|k IH]; intros H; cbn [age_count]; [reflexivity|].
  rewrite IH by (intros; apply H; lia). rewrite (H (Z.of_nat k)) by lia. reflexivity.
Qed.

Lemma age_count_zero : forall f k, (forall j, 0 <= j < Z.of_nat k -> f j = false) -> age_count f k = 0.
Proof.
  intros f. induction k as [|k IH]; intros H; cbn [age_count]; [reflexivity|].
  rewrite IH by (intros; apply H; lia). rewrite (H (Z.of_nat k)) by lia. reflexivity.
Qed.

Lemma age_count_upd : forall f g k i, 0 <= i < Z.of_nat k ->
  (forall j, 0 <= j < Z.of_nat k -> j <> i -> f j = g j) ->
  age_count g k = age_count f k - (if f i then 1 else 0) + (if g i then 1 else 0).
Proof.
  intros f g. induction k as [|k IH]; intros i Hi H; [lia|]. cbn [age_count].
  destruct (Z.eq_dec i (Z.of_nat k)) as [->|Ne].
  - rewrite (age_count_ext g f k) by (intros j Hj; symmetry; apply H; lia). lia.
  - rewrite (IH i) by (try lia; intros j Hj Hji; apply H; lia). rewrite (H (Z.of_nat k)) by lia. lia.
Qed.

Definition age_inv (T : list byte) (now : Z) (A : list byte) (i m r : Z) : Prop :=
  length A = 400%nat /\ 0 <= i <= m /\ m <= n_of T /\ r = n_of T - m /\
  r + age_count (fun j => disco_stale A j now) (Z.to_nat m) =
    age_count (fun j => disco_stale T j now) (Z.to_nat (n_of T)) /\
  (exists p : Z -> Z,
     (forall j, 0 <= j < m -> 0 <= p j < n_of T /\ entry_of A j = entry_of T (p j)) /\
     (forall j1 j2, 0 <= j1 < m -> 0 <= j2 < m -> p j1 = p j2 -> j1 = j2)) /\
  (forall j, 0 <= j < i -> disco_stale A j now = false) /\
  (forall k, 48 * n_of T <= k < 400 -> nth_error A (Z.to_nat k) = nth_error T (Z.to_nat k)).

Lemma age_inv_init : forall T now, length T = 400%nat -> tbl_T1 T -> age_inv T now T 0 (n_of T) 0.
Proof.
  intros T now LT T1. unfold tbl_T1 in T1.
  split; [exact LT|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [|split; [intros; lia|intros; reflexivity]].
  exists (fun j => j). split; [intros j Hj; split; [lia|reflexivity]|]. intros; assumption.
Qed.

Lemma age_inv_keep : forall T now A i m r, age_inv T now A i m r -> i < m -> disco_stale A i now = false ->
  age_inv T now A (i + 1) m r.
Proof.
  intros T now A i m r (LA & Hi & Hm & Hr & Hc & Hp & Hns & Hfr) Him Hs.
  split; [exact LA|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hc|]. split; [exact Hp|].
  split; [|exact Hfr].
  intros j Hj. destruct (Z.eq_dec j i) as [->|Ne]; [exact Hs|]. apply Hns. lia.
Qed.

Lemma age_inv_stale : forall T now A i m r, length T = 400%nat -> tbl_T1 T -> age_inv T now A i m r -> i < m ->
  disco_stale A i now = true -> age_inv T now (upd A (48 * i) (entry_of A (m - 1))) i (m - 1) (r + 1).
Proof.
  intros T now A i m r LT T1 (LA & Hi & Hm & Hr & Hc & (p & Hp & Hinj) & Hns & Hfr) Him Hs.
  unfold tbl_T1 in T1.
  assert (LE : length (entry_of A (m - 1)) = 48%nat) by (unfold entry_of; apply length_sub; rewrite ?LA; lia).
  set (A' := upd A (48 * i) (entry_of A (m - 1))).
  assert (LA' : length A' = 400%nat) by (unfold A'; rewrite length_upd; rewrite ?LE, ?LA; lia).
  assert (EI : entry_of A' i = entry_of A (m - 1)) by (unfold A'; apply entry_upd_same; assumption || lia).
  assert (EJ : forall j, 0 <= j < 8 -> j <> i -> entry_of A' j = entry_of A j)
    by (intros j Hj Hji; unfold A'; apply entry_upd_other; assumption || lia).
  split; [exact LA'|]. split; [lia|]. split; [lia|]. split; [lia|].
  split.
  { rewrite <- Hc. replace (Z.to_nat m) with (S (Z.to_nat (m - 1))) by lia. cbn [age_count].
    rewrite Z2Nat.id by lia.
    destruct (Z.eq_dec i (m - 1)) as [E|Ne].
    - assert (AA : A' = A) by (unfold A'; rewrite <- E; unfold entry_of; apply upd_self; rewrite ?LA; lia).
      rewrite AA. rewrite <- E, Hs. change (if true then 1 else 0) with 1. lia.
    - rewrite (age_count_upd (fun j => disco_stale A j now) (fun j => disco_stale A' j now) (Z.to_nat (m - 1)) i)
        by (lia || (intros j Hj Hji; cbv beta; symmetry; apply (stale_ent A' A j j now LA' LA); [lia|lia|];
            apply EJ; lia)).
      cbv beta. rewrite Hs. rewrite (stale_ent A' A i (m - 1) now LA' LA ltac:(lia) ltac:(lia) EI).
      change (if true then 1 else 0) with 1. lia. }
  split.
  { exists (fun j => if Z.eqb j i then p (m - 1) else p j). split.
    - intros j Hj. cbv beta. destruct (Z.eqb_spec j i) as [->|Ne].
      + rewrite EI. apply Hp. lia.
      + rewrite EJ by lia. apply Hp. lia.
    - intros j1 j2 Hj1 Hj2 E. cbv beta in E.
      destruct (Z.eqb_spec j1 i); destruct (Z.eqb_spec j2 i); cbv iota in E.
      + lia.
      + pose proof (Hinj (m - 1) j2 ltac:(lia) ltac:(lia) E). lia.
      + pose proof (Hinj j1 (m - 1) ltac:(lia) ltac:(lia) E). lia.
      + apply Hinj; lia. }
  split.
  { intros j Hj. rewrite (stale_ent A' A j j now LA' LA ltac:(lia) ltac:(lia)) by (apply EJ; lia). apply Hns. lia. }
  intros k Hk. unfold A'. rewrite nth_upd by (rewrite ?LE, ?LA; lia). rewrite LE.
  nth_cases; try lia. apply Hfr. lia.
Qed.

Lemma age_loop_inv : forall T now, length T = 400%nat -> tbl_T1 T ->
  forall k A i m r A' m' r', Z.of_nat k = m - i -> age_inv T now A i m r ->
  age_loop k A now i m r = (A', m', r') -> age_inv T now A' m' m' r'.
Proof.
  intros T now LT T1. induction k as [|k IH]; intros A i m r A' m' r' Hk HI E.
  - cbn [age_loop] in E. inversion E; subst A' m' r'. replace i with m in HI by lia. exact HI.
  - pose proof HI as (LA & Hi & _). cbn [age_loop] in E.
    replace (i <? m) with true in E by (symmetry; apply Z.ltb_lt; lia).
    destruct (disco_stale A i now) eqn:S.
    + apply (IH (upd A (48 * i) (entry_of A (m - 1))) i (m - 1) (r + 1) A' m' r');
        [lia | apply age_inv_stale; assumption || lia | exact E].
    + apply (IH A (i + 1) m r A' m' r'); [lia | apply age_inv_keep; assumption || lia | exact E].
Qed.

Lemma age_final : forall T now A m r, length T = 400%nat -> table_ok T -> age_inv T now A m m r ->
  age_post T now
    (if 0 <? r then upd (upd A 384 (le4 (Z_to_bv 64 m))) 392 (le4 (Z_to_bv 64 (seq_of T + 1)))
     else upd A 384 (le4 (Z_to_bv 64 m))) r.
Proof.
  intros T now A m r LT (T1 & T2 & T3 & T4) (LA & Hi & Hm & Hr & Hc & (p & Hp & Hinj) & Hns & Hfr).
  unfold tbl_T1 in T1.
  set (B := upd A 384 (le4 (Z_to_bv 64 m))).
  assert (LB : length B = 400%nat) by (unfold B; rewrite length_upd; rewrite ?length_le4, ?LA; lia).
  set (T' := if 0 <? r then upd B 392 (le4 (Z_to_bv 64 (seq_of T + 1))) else B).
  assert (LT' : length T' = 400%nat)
    by (unfold T'; destruct (0 <? r); [rewrite length_upd; rewrite ?length_le4, ?LB; lia | exact LB]).
  assert (EB : forall j, 0 <= j < 8 -> entry_of T' j = entry_of A j).
  { intros j Hj. unfold T', B. destruct (0 <? r).
    - rewrite entry_upd_hi by (rewrite ?length_le4, ?LB, ?length_upd; rewrite ?length_le4, ?LA; lia).
      apply entry_upd_hi; rewrite ?length_le4, ?LA; lia.
    - apply entry_upd_hi; rewrite ?length_le4, ?LA; lia. }
  assert (NB : n_of B = m) by (unfold B; apply n_of_set; assumption || lia).
  assert (NT : n_of T' = m).
  { unfold T'. destruct (0 <? r); [|exact NB].
    rewrite n_of_upd_out by (rewrite ?length_le4, ?LB; lia). exact NB. }
  assert (EP : forall j, 0 <= j < m -> entry_of T' j = entry_of T (p j)).
  { intros j Hj. rewrite EB by lia. apply Hp. exact Hj. }
  assert (FP : forall j, 0 <= j < m ->
    mac_of T' j = mac_of T (p j) /\ role_of_e T' j = role_of_e T (p j) /\ hd_of T' j = hd_of T (p j) /\
    din_of T' j = din_of T (p j) /\ dout_of T' j = dout_of T (p j) /\ owned_of T' j = owned_of T (p j)).
  { intros j Hj. pose proof (Hp j Hj) as [Pj _]. apply fields_ent; try assumption; try lia. apply EP. exact Hj. }
  split; [exact LT'|].
  split.
  { rewrite <- Hc. rewrite (age_count_zero (fun j => disco_stale A j now)); [lia|].
    intros j Hj. apply Hns. lia. }
  split; [lia|].
  split; [rewrite NT; lia|].
  split.
  { intros j Hj. rewrite NT in Hj. rewrite (stale_ent T' A j j now LT' LA ltac:(lia) ltac:(lia)) by (apply EB; lia).
    apply Hns. exact Hj. }
  split.
  { unfold T'. destruct (Z.ltb_spec 0 r).
    - apply seq_of_set; [exact LB|apply seq_range].
    - unfold B. rewrite seq_of_upd_out by (rewrite ?length_le4, ?LA; lia).
      unfold seq_of, u_at. f_equal. apply sub_frame; rewrite ?LA, ?LT; try lia. intros k Hk. apply Hfr. lia. }
  split.
  { split; [unfold tbl_T1; rewrite NT; lia|]. split; [|split].
    - intros j Hj. rewrite NT in Hj. pose proof (Hp j Hj) as [Pj _]. destruct (FP j Hj) as (_ & -> & _).
      apply T2. exact Pj.
    - intros j1 j2 Hj1 Hj12 Hj2. rewrite NT in Hj2.
      pose proof (Hp j1 ltac:(lia)) as [P1 _]. pose proof (Hp j2 ltac:(lia)) as [P2 _].
      destruct (FP j1 ltac:(lia)) as (-> & _). destruct (FP j2 ltac:(lia)) as (-> & _).
      assert (NE : p j1 <> p j2) by (intro E; apply Hinj in E; lia).
      destruct (Z_lt_le_dec (p j1) (p j2)).
      + apply T3; lia.
      + intro E. symmetry in E. revert E. apply T3; lia.
    - intros j Hj. rewrite NT in Hj. pose proof (Hp j Hj) as [Pj _].
      destruct (FP j Hj) as (_ & _ & -> & -> & -> & ->). apply T4. exact Pj. }
  split.
  { exists p. rewrite NT. split; [|exact Hinj]. intros j Hj. split; [apply Hp; exact Hj|apply EP; exact Hj]. }
  intros k Hk.
  assert (FA : nth_error A (Z.to_nat k) = nth_error T (Z.to_nat k)) by (apply Hfr; lia).
  unfold T'. destruct (0 <? r).
  - rewrite nth_upd by (rewrite ?length_le4, ?LB; lia). rewrite length_le4.
    nth_cases; try lia; unfold B; rewrite nth_upd by (rewrite ?length_le4, ?LA; lia); rewrite length_le4;
    nth_cases; try lia; exact FA.
  - unfold B. rewrite nth_upd by (rewrite ?length_le4, ?LA; lia). rewrite length_le4.
    nth_cases; try lia; exact FA.
Qed.

Lemma age_model_post : forall T now T' r, length T = 400%nat -> table_ok T -> age_model T now = (T', r) ->
  age_post T now T' r.
Proof.
  intros T now T' r LT TOK E. unfold age_model in E.
  destruct (age_loop (Z.to_nat (n_of T)) T now 0 (n_of T) 0) as [[A m] r0] eqn:L.
  pose proof TOK as (T1 & _). pose proof T1 as T1'. unfold tbl_T1 in T1'.
  pose proof (age_loop_inv T now LT T1 (Z.to_nat (n_of T)) T 0 (n_of T) 0 A m r0 ltac:(lia)
    (age_inv_init T now LT T1) L) as HI.
  inversion E; subst T' r. apply age_final; assumption.
Qed.

Lemma rw_cb : forall m a n bs, rw_cells rsegs m a [CB n bs] <->
  length bs = n /\ bytes_at rsegs m a bs /\ wr_at rsegs m a (Z.of_nat n).
Proof.
  intros. unfold rw_cells, cells_at. cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize].
  rewrite app_nil_r, Nat.add_0_r. tauto.
Qed.

Lemma wr_at_sub : forall m a n k l, wr_at rsegs m a n -> 0 <= k -> 0 <= l -> k + l <= n -> wr_at rsegs m (a + k) l.
Proof.
  intros m a n k l (Ha & Hn & H) Hk Hl Hkl. split; [lia|]. split; [lia|].
  intros j Hj. replace (a + k + j) with (a + (k + j)) by lia. apply H. lia.
Qed.

Lemma bytes_at_patch : forall m m' t X k v, bytes_at rsegs m t X -> 0 <= k ->
  k + Z.of_nat (length v) <= Z.of_nat (length X) ->
  munch [(t + k, t + k + Z.of_nat (length v))] m m' -> bytes_at rsegs m' (t + k) v -> bytes_at rsegs m' t (upd X k v).
Proof.
  intros m m' t X k v (Ht & Hl & HX) Hk Hkv MU (_ & _ & Hv).
  assert (LU : length (upd X k v) = length X) by (apply length_upd; lia).
  split; [lia|]. split; [rewrite LU; lia|].
  intros j Hj. rewrite LU in Hj. rewrite nth_upd by lia.
  destruct (Nat.leb_spec (Z.to_nat k) j); destruct (Nat.ltb_spec j (Z.to_nat k + length v)); cbn [andb].
  1: { replace (t + Z.of_nat j) with (t + k + Z.of_nat (j - Z.to_nat k)) by lia. apply Hv. lia. }
  all: rewrite <- (HX j Hj); unfold mrd; rewrite MU; [reflexivity|];
    cbn [outside]; rewrite wa_unsigned by lia; split; [lia|exact I].
Qed.

Lemma stk_copy : forall m m' lo hi d bs, stk rsegs m lo hi -> munch [(d, d + Z.of_nat (length bs))] m m' ->
  wmono rsegs m m' -> bytes_at rsegs m' d bs -> stk rsegs m' lo hi.
Proof.
  intros m m' lo hi d bs (H1 & H2 & H) MU WM (Hd & Hl & Hb). split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as [Hw (b & Hm)]. split; [apply WM; exact Hw|].
  destruct (Z_lt_le_dec a d) as [Lt|Ge]; [|destruct (Z_lt_le_dec a (d + Z.of_nat (length bs))) as [Lt2|Ge2]].
  - exists b. unfold mrd in *. rewrite MU; [exact Hm|]. cbn [outside]. rewrite wa_unsigned by lia.
    split; [lia|exact I].
  - replace a with (d + Z.of_nat (Z.to_nat (a - d))) by lia. rewrite Hb by lia.
    destruct (nth_error bs (Z.to_nat (a - d))) eqn:E; [eexists; reflexivity|]. apply nth_error_None in E. lia.
  - exists b. unfold mrd in *. rewrite MU; [exact Hm|]. cbn [outside]. rewrite wa_unsigned by lia.
    split; [lia|exact I].
Qed.

Lemma tbl_store : forall m mI lo hi FA FC t X k v W,
  bytes_at rsegs m t X -> wr_at rsegs m t 400 -> length X = 400%nat -> 0 <= k -> k + Z.of_nat (length v) <= 400 ->
  rw_cells rsegs m FA FC -> FA + Z.of_nat (cells_size FC) <= t \/ t + 400 <= FA ->
  stk rsegs m lo hi -> munch W mI m -> inside W (t + k) (Z.of_nat (length v)) -> wmono rsegs mI m ->
  mem_inv rsegs m ->
  bytes_at rsegs (write_to_mem m (wa (t + k)) v) t (upd X k v) /\ wr_at rsegs (write_to_mem m (wa (t + k)) v) t 400 /\
  rw_cells rsegs (write_to_mem m (wa (t + k)) v) FA FC /\ stk rsegs (write_to_mem m (wa (t + k)) v) lo hi /\
  munch W mI (write_to_mem m (wa (t + k)) v) /\ wmono rsegs mI (write_to_mem m (wa (t + k)) v) /\
  mem_inv rsegs (write_to_mem m (wa (t + k)) v).
Proof.
  intros m mI lo hi FA FC t X k v W HX HW LX Hk Hkv FR DF ST MU IN WM MI.
  pose proof (bytes_at_bound rsegs m t X HX) as TB. rewrite LX in TB.
  split; [apply bytes_at_write_inside; [exact HX|lia|rewrite LX; lia]|].
  split; [apply wr_at_write; exact HW|].
  split; [apply rw_cells_frame; [exact FR|lia|lia|lia]|].
  split; [apply stk_write; [exact ST|lia|lia]|].
  split; [apply munch_write; [exact MU|lia|lia|exact IN]|].
  split; [apply wmono_write; exact WM|].
  apply mem_inv_store; [exact MI|]. apply (wr_at_store_ok rsegs m t 400 k (length v) HW); lia.
Qed.

Lemma tbl_copy : forall m m' mI lo hi FA FC t X i src s1 s2,
  bytes_at rsegs m t X -> wr_at rsegs m t 400 -> length X = 400%nat -> 0 <= i < 8 -> length src = 48%nat ->
  munch [(t + 48 * i, t + 48 * i + 48)] m m' -> wmono rsegs m m' -> rw_cells rsegs m' (t + 48 * i) [CB 48 src] ->
  rw_cells rsegs m FA FC -> FA + Z.of_nat (cells_size FC) <= t \/ t + 400 <= FA ->
  stk rsegs m lo hi -> munch [(t, t + 400); (s1, s2)] mI m -> wmono rsegs mI m ->
  bytes_at rsegs m' t (upd X (48 * i) src) /\ wr_at rsegs m' t 400 /\ rw_cells rsegs m' FA FC /\
  stk rsegs m' lo hi /\ munch [(t, t + 400); (s1, s2)] mI m' /\ wmono rsegs mI m'.
Proof.
  intros m m' mI lo hi FA FC t X i src s1 s2 HX HW LX Hi Ls MU WM RC FR DF ST MUI WMI.
  apply rw_cb in RC. destruct RC as (_ & HS & _).
  pose proof (bytes_at_bound rsegs m t X HX) as TB. rewrite LX in TB.
  split.
  { apply (bytes_at_patch m m' t X (48 * i) src); [exact HX|lia|rewrite Ls, LX; lia| |exact HS].
    rewrite Ls. exact MU. }
  split; [eapply wr_at_transport; eauto|].
  split; [eapply rw_cells_transport; [exact FR|exact MU|exact WM|]; cbn [disjoint_from]; split; [lia|exact I]|].
  split; [eapply stk_copy; [exact ST| |exact WM|exact HS]; rewrite Ls; exact MU|].
  split; [|eapply wmono_trans; eauto].
  eapply munch_trans; [exact MUI|]. eapply munch_weaken; [|exact MU].
  unfold sub_fp. intros x Hx. cbn [outside] in *. destruct Hx as [Hx1 _]. split; [lia|exact I].
Qed.

Lemma ld_val : forall bs, length bs = 8%nat -> bv_extract 0 64 (le_bytes_to_word bs) = Z_to_bv 64 (bytes_le_to_Z bs).
Proof.
  intros bs L. apply bv_eq. rewrite extract_low_mod by lia. unfold le_bytes_to_word.
  pose proof (ble_range bs) as H. rewrite L in H. change (8 * Z.of_nat 8) with 64 in H.
  rewrite !unsigned_lit by lia. change (Z.of_N 64) with 64. apply Z.mod_small. lia.
Qed.

Lemma last_range : forall X i, length X = 400%nat -> 0 <= i < 8 -> 0 <= last_of X i < 2^64.
Proof.
  intros X i LX Hi. unfold last_of, u_at. pose proof (ble_range (sub X (48 * i + 40) 8)) as H.
  rewrite length_sub in H by (rewrite ?LX; lia). change (8 * Z.of_nat 8) with 64 in H. exact H.
Qed.

Lemma age_loop_keep : forall k A now i m r, i < m -> disco_stale A i now = false ->
  age_loop (S k) A now i m r = age_loop k A now (i + 1) m r.
Proof.
  intros k A now i m r H S. cbn [age_loop]. replace (i <? m) with true by (symmetry; apply Z.ltb_lt; lia).
  rewrite S. reflexivity.
Qed.

Lemma age_loop_stale : forall k A now i m r, i < m -> disco_stale A i now = true ->
  age_loop (S k) A now i m r = age_loop k (upd A (48 * i) (entry_of A (m - 1))) now i (m - 1) (r + 1).
Proof.
  intros k A now i m r H S. cbn [age_loop]. replace (i <? m) with true by (symmetry; apply Z.ltb_lt; lia).
  rewrite S. reflexivity.
Qed.

Lemma age_loop_end : forall k A now i m r, m <= i -> age_loop k A now i m r = (A, m, r).
Proof.
  intros k A now i m r H. destruct k; cbn [age_loop]; [reflexivity|].
  replace (i <? m) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma tbl_mem_step : forall A i mm v w, length A = 400%nat -> 0 <= i < mm -> mm <= 8 ->
  length v = 4%nat -> length w = 4%nat ->
  upd (upd (upd A 384 v) (48 * i) (entry_of (upd A 384 v) (mm - 1))) 384 w =
  upd (upd A (48 * i) (entry_of A (mm - 1))) 384 w.
Proof.
  intros A i mm v w LA Hi Hm Lv Lw.
  assert (LE : length (entry_of A (mm - 1)) = 48%nat) by (unfold entry_of; apply length_sub; rewrite ?LA; lia).
  rewrite entry_upd_hi by (rewrite ?Lv; lia).
  rewrite (upd_comm A 384 v (48 * i) (entry_of A (mm - 1))) by (rewrite ?Lv, ?LE, ?LA; lia).
  assert (L1 : length (upd A (48 * i) (entry_of A (mm - 1))) = 400%nat) by (rewrite length_upd; rewrite ?LE, ?LA; lia).
  apply upd_upd; rewrite ?Lv, ?Lw, ?L1; lia.
Qed.

Lemma seq_inc_le4 : forall s, 0 <= s < 2^32 ->
  le4 (Z_to_bv 64 (bv_swrap 32 s + 1)) = le4 (Z_to_bv 64 (s + 1)).
Proof.
  intros s Hs. apply le4_eq_mod. rewrite !unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  Z.div_mod_to_equations. lia.
Qed.

Lemma sx32_small : forall z, 0 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold sx32. rewrite unsigned_lit by lia. rewrite swrap32_small by lia. reflexivity. Qed.

Lemma age_model_of : forall T now A m r, age_loop (Z.to_nat (n_of T)) T now 0 (n_of T) 0 = (A, m, r) ->
  age_model T now =
    ((if 0 <? r then upd (upd A 384 (le4 (Z_to_bv 64 m))) 392 (le4 (Z_to_bv 64 (seq_of T + 1)))
      else upd A 384 (le4 (Z_to_bv 64 m))), r).
Proof. intros T now A m r H. unfold age_model. rewrite H. reflexivity. Qed.

Theorem reac_disco_table_age_holds : memcpy_contract -> memcpy_same_contract -> reac_disco_table_age_contract.
Proof.
  intros MC MCS. unfold reac_disco_table_age_contract, REAC_DISCO_TABLE_AGE, REAC_DISCO_TABLE_AGE_K.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo t now T -> -> Hnow Ht0 Ht8 RW LT TOK MI ST LO DT.
  apply rw_cb in RW. destruct RW as (_ & HT & HW).
  pose proof TOK as (T1 & _). unfold tbl_T1 in T1. unfold off_window in DT.
  pose proof (bytes_at_bound rsegs m t T HT) as TB. rewrite LT in TB.
  pose proof (munch_refl [(t, t + 400); (bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  carve_frame 64%nat ST.
  do 9 step.
  lazymatch goal with H : rw_cells _ ?mm _ _ |- _ => rename mm into mF end.
  rename m into mI. rename MU into MU0. rename WM into WM0.
  lazymatch goal with H : rw_cells _ mF _ ?cs |- _ => set (FRC := cs) in H; rename H into FR end.
  change (Z.of_nat 400) with 400 in HW, TB.
  assert (DF : bv_unsigned sp + -64 + Z.of_nat (cells_size FRC) <= t \/ t + 400 <= bv_unsigned sp + -64)
    by (unfold FRC; cbn [cells_size csize]; lia).
  assert (EPI : forall (m2 : word -> option byte) (T' : list byte) (r : Z)
                       (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x28 x29 x30 x31 : word),
    rw_cells rsegs m2 (bv_unsigned sp + -64) FRC -> stk rsegs m2 lo (bv_unsigned sp + -64) ->
    munch [(t, t + 400); (bv_unsigned sp + -64, bv_unsigned sp)] mI m2 -> wmono rsegs mI m2 -> mem_inv rsegs m2 ->
    bytes_at rsegs m2 t T' -> wr_at rsegs m2 t 400 -> length T' = 400%nat -> age_model T now = (T', r) ->
    evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13
                          x14 x15 x16 x17 (Z_to_bv 64 r) x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x15c04) fc None m2 (seg_rom rsegs))).
  { intros m2 T' r x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x28 x29 x30 x31
      FR2 ST2 MU2 WM2 MI2 HT2 HW2 LT2 AM.
    unfold FRC in FR2.
    do 9 step.
    release_frame FR2 ST2 (bv_unsigned sp).
    do 2 step.
    apply evt_done. unfold QQ. do 14 eexists. exists m2, T', r. split; [reflexivity|].
    split; [exact MU2|]. split; [exact WM2|]. split; [exact MI2|]. split; [exact ST2|].
    split; [apply rw_cb; split; [exact LT2|split; [exact HT2|exact HW2]]|].
    split; [exact AM|]. apply age_model_post; assumption. }
  assert (EXIT : forall (m2 : word -> option byte) (A : list byte) (mm r : Z)
                        (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x28 x29 x30 x31 : word),
    rw_cells rsegs m2 (bv_unsigned sp + -64) FRC -> stk rsegs m2 lo (bv_unsigned sp + -64) ->
    munch [(t, t + 400); (bv_unsigned sp + -64, bv_unsigned sp)] mI m2 -> wmono rsegs mI m2 -> mem_inv rsegs m2 ->
    bytes_at rsegs m2 t (upd A 384 (le4 (Z_to_bv 64 mm))) -> wr_at rsegs m2 t 400 ->
    age_inv T now A mm mm r -> age_loop (Z.to_nat (n_of T)) T now 0 (n_of T) 0 = (A, mm, r) ->
    evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x5 x6 x7 (Z_to_bv 64 t) x9 x10 x11
                          x12 x13 x14 x15 x16 x17 (Z_to_bv 64 r) x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x15bf4) fc None m2 (seg_rom rsegs))).
  { intros m2 A mm r x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x28 x29 x30 x31
      FR2 ST2 MU2 WM2 MI2 HX2 HW2 HI RES.
    pose proof HI as (LA & Hi & Hm & Hr & _).
    pose proof (age_model_of T now A mm r RES) as AM.
    set (X := upd A 384 (le4 (Z_to_bv 64 mm))) in *.
    assert (LX : length X = 400%nat) by (unfold X; rewrite length_upd; rewrite ?length_le4, ?LA; lia).
    step.
    rewrite eqb_lit by lia.
    destruct (Z.eqb_spec r 0) as [R0|R0].
    - apply (EPI m2 X r); try assumption.
      rewrite AM, R0. reflexivity.
    - pose proof (rd_sub _ t X 392 4 HX2 ltac:(lia) ltac:(rewrite LX; lia)) as RS.
      assert (SQ : sub X 392 4 = sub T 392 4).
      { unfold X. rewrite sub_upd_out by (rewrite ?length_le4, ?LA; lia).
        destruct HI as (_ & _ & _ & _ & _ & _ & _ & Hfr).
        apply sub_frame; rewrite ?LA, ?LT; try lia. intros k Hk. apply Hfr. lia. }
      rewrite SQ in RS.
      step.
      rewrite lw_val by (apply length_sub; lia).
      change (bytes_le_to_Z (sub T 392 4)) with (seq_of T).
      step.
      pose proof (wr_at_store_ok rsegs m2 t 400 392 4 HW2 ltac:(lia) ltac:(lia)) as SO.
      step.
      rewrite seq_inc_le4 by apply seq_range.
      change (Z_to_bv 64 (t + 392)) with (wa (t + 392)).
      destruct (tbl_store m2 mI lo (bv_unsigned sp + -64) (bv_unsigned sp + -64) FRC t X 392
                 (le4 (Z_to_bv 64 (seq_of T + 1))) [(t, t + 400); (bv_unsigned sp + -64, bv_unsigned sp)] HX2 HW2 LX
                 ltac:(lia) ltac:(rewrite length_le4; lia) FR2 DF ST2 MU2
                 ltac:(cbn [inside]; left; rewrite length_le4; lia) WM2 MI2)
        as (HX4 & HW4 & FR4 & ST4 & MU4 & WM4 & MI4).
      remember (write_to_mem m2 (wa (t + 392)) (le4 (Z_to_bv 64 (seq_of T + 1)))) as m4 eqn:Em4. clear Em4.
      apply (EPI m4 (upd X 392 (le4 (Z_to_bv 64 (seq_of T + 1)))) r); try assumption.
      + rewrite length_upd; rewrite ?length_le4, ?LX; lia.
      + rewrite AM. replace (0 <? r) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
  assert (LOOP : forall (k : nat) (A : list byte) (i mm r : Z) (m2 : word -> option byte)
                        (x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    Z.of_nat k = mm - i -> i < mm -> age_inv T now A i mm r ->
    age_loop k A now i mm r = age_loop (Z.to_nat (n_of T)) T now 0 (n_of T) 0 ->
    rw_cells rsegs m2 (bv_unsigned sp + -64) FRC -> stk rsegs m2 lo (bv_unsigned sp + -64) ->
    munch [(t, t + 400); (bv_unsigned sp + -64, bv_unsigned sp)] mI m2 -> wmono rsegs mI m2 -> mem_inv rsegs m2 ->
    bytes_at rsegs m2 t (upd A 384 (le4 (Z_to_bv 64 mm))) -> wr_at rsegs m2 t 400 ->
    evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x5 x6 x7 (Z_to_bv 64 t) (Z_to_bv 64 now) x10
                          (Z_to_bv 64 mm) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 r) (Z_to_bv 64 i)
                          (Z_to_bv 64 (2^64 - 1 - t)) (Z_to_bv 64 8) (Z_to_bv 64 5000000000)
                          s7 s8 s9 s10 s11 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x15b7c) fc None m2 (seg_rom rsegs))).
  { induction k as [|k IH];
      intros A i mm r m2 x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 Hk Him HI RES
        FR2 ST2 MU2 WM2 MI2 HX2 HW2; [lia|].
    pose proof HI as (LA & Hi & Hm & Hr & _).
    set (X := upd A 384 (le4 (Z_to_bv 64 mm))) in *.
    assert (LX : length X = 400%nat) by (unfold X; rewrite length_upd; rewrite ?length_le4, ?LA; lia).
    step.
    rewrite ltu_lit by lia. replace (i <? 8) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb].
    do 3 step.
    rewrite mul48_lit by lia.
    step.
    rewrite ltu_lit by lia. replace (2^64 - 1 - t <? 48 * i) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
    step.
    pose proof (rd_sub _ t X (48 * i + 40) 8 HX2 ltac:(lia) ltac:(rewrite LX; lia)) as RL.
    step.
    rewrite ld_val by (apply length_sub; lia).
    change (bytes_le_to_Z (sub X (48 * i + 40) 8)) with (last_of X i).
    pose proof (last_range X i LX ltac:(lia)) as LR.
    assert (SX : disco_stale X i now = disco_stale A i now)
      by (apply stale_ent; [exact LX|exact LA|lia|lia|unfold X; apply entry_upd_hi; rewrite ?length_le4; lia]).
    assert (KEEP : disco_stale A i now = false -> forall y12 : word,
      evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x5 x6 x7 (Z_to_bv 64 t) (Z_to_bv 64 now)
                            (Z_to_bv 64 (t + 48 * i)) (Z_to_bv 64 mm) y12 x13 x14 x15 x16 x17 (Z_to_bv 64 r)
                            (Z_to_bv 64 i) (Z_to_bv 64 (2^64 - 1 - t)) (Z_to_bv 64 8) (Z_to_bv 64 5000000000)
                            s7 s8 s9 s10 s11 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x15be8) fc None m2 (seg_rom rsegs))).
    { intros NS y12. step. step. rewrite addiw_small by lia. rewrite Z.add_0_r. step.
      rewrite lts_lit by lia.
      pose proof (age_inv_keep _ _ _ _ _ _ HI Him NS) as HI'.
      destruct (Z.ltb_spec (i + 1) mm) as [L2|L2].
      - apply (IH A (i + 1) mm r m2); try assumption; try lia.
        rewrite <- RES. symmetry. apply age_loop_keep; assumption.
      - replace (i + 1) with mm in HI' by lia.
        apply (EXIT m2 A mm r); try assumption.
        rewrite <- RES. rewrite age_loop_keep by assumption. apply age_loop_end. lia. }
    step.
    rewrite ltu_lit by lia.
    destruct (Z.ltb_spec (last_of X i) now) as [L1|L1]; cbn [negb].
    2: { apply KEEP. rewrite <- SX. unfold disco_stale. destruct (Z.ltb_spec (last_of X i) now); [lia|reflexivity]. }
    step.
    rewrite (unsigned_lit now), (unsigned_lit (last_of X i)) by lia.
    step.
    rewrite ltu_lit by lia.
    destruct (Z.ltb_spec 5000000000 (now - last_of X i)) as [L2|L2]; cbn [negb].
    2: { apply KEEP. rewrite <- SX. unfold disco_stale, REAC_DISCO_STALE_NS.
         destruct (Z.ltb_spec 5000000000 (now - last_of X i)); [lia|]. apply andb_false_r. }
    assert (SA : disco_stale A i now = true).
    { rewrite <- SX. unfold disco_stale, REAC_DISCO_STALE_NS.
      destruct (Z.ltb_spec (last_of X i) now); [|lia]. destruct (Z.ltb_spec 5000000000 (now - last_of X i)); [|lia].
      reflexivity. }
    step.
    rewrite addiw_small by lia. replace (mm + -1) with (mm - 1) by lia.
    step.
    rewrite ltu_lit by lia. replace (8 <? mm - 1) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
    do 3 step.
    rewrite mul48_lit by lia.
    step.
    rewrite ltu_lit by lia. replace (2^64 - 1 - t <? 48 * (mm - 1)) with false by (symmetry; apply Z.ltb_ge; lia).
    cbv iota.
    do 3 step.
    assert (LE : length (entry_of X (mm - 1)) = 48%nat) by (unfold entry_of; apply length_sub; rewrite ?LX; lia).
    assert (DST : rw_cells rsegs m2 (t + 48 * i) [CB 48 (entry_of X i)]).
    { apply rw_cb. split; [unfold entry_of; apply length_sub; rewrite ?LX; lia|]. split.
      - unfold entry_of. apply bytes_at_sub; [exact HX2|lia|rewrite LX; lia].
      - apply (wr_at_sub m2 t 400); [exact HW2|lia|lia|lia]. }
    eapply evt_cut.
    { destruct (Z.eq_dec i (mm - 1)) as [Ei|Ni].
      - eapply MCS with (src := entry_of X (mm - 1)).
        + f_equal. lia.
        + rewrite unsigned_lit by lia. exact LE.
        + rewrite !unsigned_lit by lia. rewrite <- Ei. exact DST.
        + exact MI2.
      - eapply MC with (src := entry_of X (mm - 1)) (junk := entry_of X i).
        + rewrite unsigned_lit by lia. unfold entry_of. apply bytes_at_sub; [exact HX2|lia|rewrite LX; lia].
        + rewrite unsigned_lit by lia. exact LE.
        + rewrite !unsigned_lit by lia. exact DST.
        + rewrite !unsigned_lit by lia. lia.
        + exact MI2. }
    intros ms' PO. unfold memcpy_post in PO.
    destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m3 &
                    E3 & MU3 & WM3 & MI3 & RC3 & _).
    subst ms'.
    rewrite !unsigned_lit in MU3, RC3 by lia. change (Z.to_nat 48) with 48%nat in RC3.
    replace (ret_pc (Z_to_bv 64 89032)) with (Z_to_bv 64 89032) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    destruct (tbl_copy m2 m3 mI lo (bv_unsigned sp + -64) (bv_unsigned sp + -64) FRC t X i (entry_of X (mm - 1))
               (bv_unsigned sp + -64) (bv_unsigned sp) HX2 HW2 LX ltac:(lia) LE MU3 WM3 RC3 FR2 DF ST2 MU2 WM2)
      as (HX3 & HW3 & FR3 & ST3 & MU3' & WM3').
    clear HX2 HW2 FR2 ST2 MU2 WM2 MI2 MU3 WM3 RC3 RL.
    set (X3 := upd X (48 * i) (entry_of X (mm - 1))) in *.
    assert (LX3 : length X3 = 400%nat) by (unfold X3; rewrite length_upd; rewrite ?LE, ?LX; lia).
    assert (N3 : sub X3 384 4 = le4 (Z_to_bv 64 mm)).
    { unfold X3. rewrite sub_upd_out by (rewrite ?LE, ?LX; lia). unfold X.
      pose proof (sub_upd_in A 384 (le4 (Z_to_bv 64 mm)) ltac:(lia) ltac:(rewrite length_le4, LA; lia)) as S.
      rewrite length_le4 in S. exact S. }
    pose proof (rd_sub _ t X3 384 4 HX3 ltac:(lia) ltac:(rewrite LX3; lia)) as RN3. rewrite N3 in RN3.
    step.
    rewrite sx32_small by lia.
    step.
    rewrite addiw_small by lia. replace (mm + -1) with (mm - 1) by lia.
    step.
    rewrite lts_lit by lia. replace (mm - 1 <? mm) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb].
    step.
    rewrite addiw_small by lia.
    pose proof (wr_at_store_ok rsegs m3 t 400 384 4 HW3 ltac:(lia) ltac:(lia)) as SO.
    step.
    change (Z_to_bv 64 (t + 384)) with (wa (t + 384)).
    destruct (tbl_store m3 mI lo (bv_unsigned sp + -64) (bv_unsigned sp + -64) FRC t X3 384
               (le4 (Z_to_bv 64 (mm - 1))) [(t, t + 400); (bv_unsigned sp + -64, bv_unsigned sp)] HX3 HW3 LX3
               ltac:(lia) ltac:(rewrite length_le4; lia) FR3 DF ST3 MU3'
               ltac:(cbn [inside]; left; rewrite length_le4; lia) WM3' MI3)
      as (HX4 & HW4 & FR4 & ST4 & MU4 & WM4 & MI4).
    remember (write_to_mem m3 (wa (t + 384)) (le4 (Z_to_bv 64 (mm - 1)))) as m4 eqn:Em4. clear Em4.
    step.
    rewrite lts_lit by lia. replace (r + 1 <? r) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
    do 3 step.
    rewrite addiw_small by lia. rewrite Z.add_0_r.
    step.
    rewrite lts_lit by lia.
    assert (MS4 : upd X3 384 (le4 (Z_to_bv 64 (mm - 1))) =
                  upd (upd A (48 * i) (entry_of A (mm - 1))) 384 (le4 (Z_to_bv 64 (mm - 1)))).
    { unfold X3, X. apply tbl_mem_step; [exact LA|lia|lia|apply length_le4|apply length_le4]. }
    rewrite MS4 in HX4.
    pose proof (age_inv_stale T now A i mm r LT (proj1 TOK) HI Him SA) as HI'.
    set (A' := upd A (48 * i) (entry_of A (mm - 1))) in *.
    destruct (Z.ltb_spec i (mm - 1)) as [L3|L3].
    - apply (IH A' i (mm - 1) (r + 1) m4); try assumption; try lia.
      rewrite <- RES. symmetry. apply age_loop_stale; assumption.
    - replace i with (mm - 1) in HI' by lia.
      apply (EXIT m4 A' (mm - 1) (r + 1)); try assumption.
      rewrite <- RES. rewrite age_loop_stale by assumption. apply age_loop_end. lia. }
  pose proof (rd_sub _ t T 384 4 HT ltac:(lia) ltac:(rewrite LT; lia)) as RN.
  step.
  rewrite eqb_lit by lia. replace (t =? 0) with false by (symmetry; apply Z.eqb_neq; exact Ht0). cbv iota.
  do 3 step.
  rewrite land7_lit by lia. if_false.
  step.
  step.
  rewrite lw_val by (apply length_sub; lia).
  change (bv_swrap 32 (bytes_le_to_Z (sub T 384 4))) with (n_of T) in *.
  step.
  rewrite lts_lit by lia.
  destruct (Z.ltb_spec 0 (n_of T)) as [Hn|Hn]; cbn [negb].
  2: { step. step. if_false. step.
       apply (EPI mF T 0); try assumption.
       pose proof (upd_n_self T LT) as U.
       assert (L0 : age_loop (Z.to_nat (n_of T)) T now 0 (n_of T) 0 = (T, n_of T, 0))
         by (replace (Z.to_nat (n_of T)) with O by lia; reflexivity).
       rewrite (age_model_of T now T (n_of T) 0 L0). rewrite U. reflexivity. }
  do 7 step.
  rewrite not_lit by lia.
  apply (LOOP (Z.to_nat (n_of T)) T 0 (n_of T) 0); try assumption; try lia.
  - apply age_inv_init; assumption.
  - reflexivity.
  - rewrite upd_n_self by exact LT. exact HT.
Qed.
