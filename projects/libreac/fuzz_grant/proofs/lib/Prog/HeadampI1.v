From Stdlib Require Import ZArith List Lia Bool Znumtheory.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import Mem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel GrantModel NextModel NextLemmas
  SlotNeeds_c reac_headamp_tx_arm_scene_c reac_headamp_tx_set_resweep_c.
Import ListNotations.
Open Scope Z_scope.

Lemma mod64_mod256 : forall v, (v mod 18446744073709551616) mod 256 = v mod 256.
Proof. intros. symmetry. apply Zmod_div_mod; [lia|lia|]. exists 72057594037927936. reflexivity. Qed.

Lemma tb_setb_if : forall T k v i, length T = 460%nat -> 0 <= k < 460 -> 0 <= i < 460 ->
  tb (setb T k v) i = if i =? k then v mod 256 else tb T i.
Proof.
  intros T k v i HL Hk Hi. destruct (Z.eqb_spec i k) as [->|Hne]; [|apply tb_setb_out; lia].
  unfold tb, setb. rewrite nth_as_error. rewrite upd_bytes_nth by (rewrite ?length_le1; lia).
  rewrite length_le1.
  replace (Nat.leb (Z.to_nat k) (Z.to_nat k) && Nat.ltb (Z.to_nat k) (Z.to_nat k + 1))%bool with true
    by (symmetry; apply andb_true_iff; split; [apply Nat.leb_le | apply Nat.ltb_lt]; lia).
  rewrite Nat.sub_diag. unfold le1. cbn [Z_to_le_bytes nth_error].
  rewrite Z_to_bv_unsigned, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616. change (2 ^ Z.of_N 8) with 256.
  apply mod64_mod256.
Qed.

Lemma set4_mod : forall T k v, set4 T k v = set4 T k (v mod 4294967296).
Proof. intros. unfold set4. f_equal. apply le4_eqm. rewrite Z.mod_mod by lia. reflexivity. Qed.

Lemma u32_set4_mod : forall T k v, length T = 460%nat -> 0 <= k -> k + 4 <= 460 ->
  u32 (set4 T k v) k = v mod 4294967296.
Proof. intros. rewrite set4_mod. apply u32_set4; [assumption | lia | lia | apply Z.mod_pos_bound; lia]. Qed.

Lemma u32_set4_out : forall T k v k', length T = 460%nat -> 0 <= k -> k + 4 <= 460 -> 0 <= k' -> k' + 4 <= 460 ->
  (k + 4 <= k' \/ k' + 4 <= k) -> u32 (set4 T k v) k' = u32 T k'.
Proof. intros. unfold u32. rewrite !tb_set4_out by lia. reflexivity. Qed.

Lemma u32_setb_out : forall T k v k', length T = 460%nat -> 0 <= k < 460 -> 0 <= k' -> k' + 4 <= 460 ->
  (k < k' \/ k' + 4 <= k) -> u32 (setb T k v) k' = u32 T k'.
Proof. intros. unfold u32. rewrite !tb_setb_out by lia. reflexivity. Qed.

Lemma upd_upd_same : forall (T bs1 bs2 : list byte) k, length bs1 = length bs2 -> (k + length bs1 <= length T)%nat ->
  upd_bytes (upd_bytes T k bs1) k bs2 = upd_bytes T k bs2.
Proof.
  intros T bs1 bs2 k E H. assert (L1 : length (upd_bytes T k bs1) = length T) by (apply upd_bytes_length; lia).
  apply nth_error_ext. intros n. destruct (Nat.ltb_spec n (length T)).
  - rewrite (upd_bytes_nth (upd_bytes T k bs1)) by lia. rewrite (upd_bytes_nth T k bs2) by lia.
    rewrite (upd_bytes_nth T k bs1) by lia. rewrite E.
    destruct (Nat.leb k n && Nat.ltb n (k + length bs2))%bool; reflexivity.
  - rewrite (proj2 (nth_error_None _ _)) by (rewrite upd_bytes_length; lia).
    rewrite (proj2 (nth_error_None _ _)) by (rewrite upd_bytes_length; lia). reflexivity.
Qed.

Lemma set4_set4 : forall T k a b, length T = 460%nat -> 0 <= k -> k + 4 <= 460 ->
  set4 (set4 T k a) k b = set4 T k b.
Proof. intros. unfold set4. apply upd_upd_same; rewrite ?length_le4; lia. Qed.

Lemma carried_set4_440 : forall T bs o j a, length T = 460%nat -> 0 <= bs -> 0 <= j ->
  carried (set4 T 440 a) bs o j = carried T bs o j.
Proof.
  intros T bs o j a HL Hb Hj. unfold carried.
  destruct (Z.leb_spec (bs + j / 3) 47); cbn [andb]; [|reflexivity].
  rewrite tb_set4_out; [reflexivity | lia | lia | lia | |]; Z.div_mod_to_equations; lia.
Qed.

Fixpoint first_carried (T : list byte) (bs o j : Z) (n : nat) : option Z :=
  match n with
  | O => None
  | S n' => if carried T bs o j then Some j else first_carried T bs o (j + 1) n'
  end.

Lemma first_carried_set4 : forall n T bs o j a, length T = 460%nat -> 0 <= bs -> 0 <= j ->
  first_carried (set4 T 440 a) bs o j n = first_carried T bs o j n.
Proof.
  induction n as [|n IH]; intros T bs o j a HL Hb Hj; [reflexivity|].
  cbn [first_carried]. rewrite carried_set4_440 by lia. rewrite IH by lia. reflexivity.
Qed.

Lemma walk_eq : forall n T t bs o total j, length T = 460%nat -> 0 <= bs -> 0 <= j ->
  j + Z.of_nat (S n) = total ->
  walk T t bs o total j (S n) =
    match first_carried T bs o j (S n) with
    | Some j' => emit_res (set4 T 440 (j' + 1)) t (bs + j' / 3) (j' mod 3) j' total
    | None => resweep (setb (set4 T 440 total) 437 0)
    end.
Proof.
  induction n as [|n IH]; intros T t bs o total j HL Hb Hj Ht.
  - rewrite walk_step. cbv zeta. cbn [first_carried]. rewrite carried_set4_440 by lia.
    destruct (carried T bs o j); [reflexivity|].
    rewrite (proj2 (Z.eqb_eq (j + 1) total)) by lia. replace total with (j + 1) by lia. reflexivity.
  - rewrite walk_step. cbv zeta. rewrite carried_set4_440 by lia.
    remember (S n) as n1. cbn [first_carried]. subst n1.
    destruct (carried T bs o j); [reflexivity|].
    rewrite (proj2 (Z.eqb_neq (j + 1) total)) by lia.
    rewrite IH by (try apply len_set4; lia).
    rewrite first_carried_set4 by lia.
    destruct (first_carried T bs o (j + 1) (S n)); rewrite set4_set4 by lia; reflexivity.
Qed.

Lemma first_carried_some : forall n T bs o j j', first_carried T bs o j n = Some j' ->
  j <= j' < j + Z.of_nat n /\ carried T bs o j' = true /\ (forall k, j <= k < j' -> carried T bs o k = false).
Proof.
  induction n as [|n IH]; intros T bs o j j' H; cbn [first_carried] in H; [discriminate|].
  destruct (carried T bs o j) eqn:Ec.
  - injection H as <-. split; [lia|]. split; [exact Ec|]. intros k Hk. lia.
  - apply IH in H as (H1 & H2 & H3). split; [lia|]. split; [exact H2|].
    intros k Hk. destruct (Z.eq_dec k j) as [->|Hne]; [exact Ec|]. apply H3. lia.
Qed.

Lemma first_carried_none : forall n T bs o j, first_carried T bs o j n = None ->
  forall k, j <= k < j + Z.of_nat n -> carried T bs o k = false.
Proof.
  induction n as [|n IH]; intros T bs o j H k Hk; cbn [first_carried] in H; [lia|].
  destruct (carried T bs o j) eqn:Ec; [discriminate|].
  destruct (Z.eq_dec k j) as [->|Hne]; [exact Ec|]. apply (IH T bs o (j + 1) H). lia.
Qed.

Lemma first_dirty_some : forall n T i k, first_dirty_from T i n = Some k ->
  i <= k < i + Z.of_nat n /\ tb T (288 + k) <> 0 /\ (forall l, i <= l < k -> tb T (288 + l) = 0).
Proof.
  induction n as [|n IH]; intros T i k H; cbn [first_dirty_from] in H; [discriminate|].
  destruct (Z.eqb_spec (tb T (288 + i)) 0) as [E|E].
  - apply IH in H as (H1 & H2 & H3). split; [lia|]. split; [exact H2|].
    intros l Hl. destruct (Z.eq_dec l i) as [->|Hne]; [exact E|]. apply H3. lia.
  - injection H as <-. split; [lia|]. split; [exact E|]. intros l Hl. lia.
Qed.

Lemma first_dirty_none : forall n T i, first_dirty_from T i n = None ->
  forall l, i <= l < i + Z.of_nat n -> tb T (288 + l) = 0.
Proof.
  induction n as [|n IH]; intros T i H l Hl; cbn [first_dirty_from] in H; [lia|].
  destruct (Z.eqb_spec (tb T (288 + i)) 0) as [E|E]; [|discriminate].
  destruct (Z.eq_dec l i) as [->|Hne]; [exact E|]. apply (IH T (i + 1) H). lia.
Qed.

Lemma s32_set4_out : forall T k v k', length T = 460%nat -> 0 <= k -> k + 4 <= 460 -> 0 <= k' -> k' + 4 <= 460 ->
  (k + 4 <= k' \/ k' + 4 <= k) -> s32 (set4 T k v) k' = s32 T k'.
Proof. intros. unfold s32. rewrite u32_set4_out by lia. reflexivity. Qed.

Lemma s32_setb_out : forall T k v k', length T = 460%nat -> 0 <= k < 460 -> 0 <= k' -> k' + 4 <= 460 ->
  (k < k' \/ k' + 4 <= k) -> s32 (setb T k v) k' = s32 T k'.
Proof. intros. unfold s32. rewrite u32_setb_out by lia. reflexivity. Qed.

Ltac L460 := repeat first [ apply len_setb | apply len_set4 ]; first [ assumption | lia ].
Ltac sidec := first [ L460 | lia ].

Ltac rds :=
  repeat match goal with
  | |- context [u32 (set4 ?X ?k ?v) ?k] => rewrite (u32_set4_mod X k v) by sidec
  | |- context [u32 (set4 ?X ?k ?v) ?k'] => rewrite (u32_set4_out X k v k') by sidec
  | |- context [u32 (setb ?X ?k ?v) ?k'] => rewrite (u32_setb_out X k v k') by sidec
  | |- context [s32 (set4 ?X ?k ?v) ?k] => rewrite (s32_set4 X k v) by sidec
  | |- context [s32 (set4 ?X ?k ?v) ?k'] => rewrite (s32_set4_out X k v k') by sidec
  | |- context [s32 (setb ?X ?k ?v) ?k'] => rewrite (s32_setb_out X k v k') by sidec
  | |- context [tb (set4 ?X ?k ?v) ?i] => rewrite (tb_set4_out X k v i) by sidec
  | |- context [tb (setb ?X ?k ?v) ?i] => rewrite (tb_setb_if X k v i) by sidec
  end.

Ltac dec := repeat match goal with
  | |- context [?a =? ?b] => first [ rewrite (proj2 (Z.eqb_eq a b)) by lia | rewrite (proj2 (Z.eqb_neq a b)) by lia ]
  end; rewrite ?Zmod_0_l.

Definition lowsame (S S' : list byte) : Prop := forall i, 0 <= i < 288 -> tb S' i = tb S i.
Definition dsub (S S' : list byte) : Prop :=
  forall i, 0 <= i < 144 -> tb S' (288 + i) = tb S (288 + i) \/ tb S' (288 + i) = 0.
Definition stepok (S S' : list byte) : Prop :=
  length S' = 460%nat /\ lowsame S S' /\ dsub S S' /\ u32 S' 432 = u32 S 432.

Definition scal (T : list byte) : Prop :=
  (tb T 437 = 0 \/ (tb T 436 < 48 /\ tb T 436 + tb T 437 <= 48)) /\
  (tb T 450 = 0 \/ (tb T 449 < 48 /\ tb T 449 + tb T 450 <= 48)) /\
  (0 <= s32 T 440 /\ (tb T 437 <> 0 -> s32 T 440 <= 3 * tb T 437) /\ 0 <= s32 T 444 <= 11 /\ tb T 448 <= 1) /\
  (u32 T 452 <> 0 -> u32 T 456 <= u32 T 452).

Lemma I1_scal : forall T, I1 T -> scal T.
Proof. intros T (_ & _ & _ & _ & H). exact H. Qed.

Lemma stepok_refl : forall S, length S = 460%nat -> stepok S S.
Proof.
  intros S HL. split; [exact HL|]. split; [intros i Hi; reflexivity|]. split; [|reflexivity].
  intros i Hi; left; reflexivity.
Qed.

Lemma stepok_trans : forall S1 S2 S3, stepok S1 S2 -> stepok S2 S3 -> stepok S1 S3.
Proof.
  intros S1 S2 S3 (L2 & l2 & d2 & a2) (L3 & l3 & d3 & a3). split; [exact L3|]. split.
  - intros i Hi. rewrite l3, l2 by lia. reflexivity.
  - split; [|congruence]. intros i Hi. destruct (d3 i Hi) as [E|E]; [|right; exact E].
    rewrite E. exact (d2 i Hi).
Qed.

Lemma I1_step : forall S S', I1 S -> stepok S S' -> scal S' -> I1 S'.
Proof.
  intros S S' (P1 & P2 & P3 & (P4a & P4b) & _) (L & Hl & Hd & Ha) Hs.
  change u32at with u32 in *. change s32at with s32 in *.
  refine (conj _ (conj _ (conj _ (conj (conj _ _) Hs)))); change u32at with u32 in *.
  - intros i Hi. rewrite (Hl (144 + i)) by lia. destruct (Hd i Hi) as [E|E]; rewrite E; [apply P1; lia|].
    split; [apply P1; lia | lia].
  - intros c q Hc Hq Hset. rewrite (Hl (144 + 3 * c + q)) in Hset by lia. rewrite (Hl (3 * c + q)) by lia.
    apply P2; assumption.
  - intros i Hi Hd1. rewrite (Hl (144 + i)) by lia. destruct (Hd i Hi) as [E|E]; rewrite E in Hd1; [|lia].
    apply P3; assumption.
  - rewrite Ha. exact P4a.
  - intros (i & Hi & Hd1). rewrite Ha. apply P4b. exists i. split; [exact Hi|].
    destruct (Hd i Hi) as [E|E]; rewrite E in Hd1; [exact Hd1 | lia].
Qed.

Lemma eff_lowsame : forall S S' t c q, lowsame S S' -> 0 <= c < 48 -> 0 <= q < 3 -> eff S' t c q = eff S t c q.
Proof.
  intros S S' t c q Hl Hc Hq. unfold eff.
  destruct (3 <=? q); [reflexivity|]. destruct ((t =? 0) || (48 <=? c)); [reflexivity|].
  rewrite (Hl (144 + 3 * c + q)) by lia. rewrite (Hl (3 * c + q)) by lia. reflexivity.
Qed.

Definition rearm (X : list byte) : list byte :=
  set4 (set4 (setb (setb (set4 (setb (set4 X 456 (u32 X 456 + 1)) 448 1) 456 0) 436 (tb X 449)) 437 (tb X 450)) 440 0) 444 0.

Lemma resweep_shape : forall X,
  (resweep X = silent X /\ (u32 X 452 = 0 \/ tb X 450 = 0)) \/
  (u32 X 452 <> 0 /\ tb X 450 <> 0 /\ (u32 X 456 + 1) mod 4294967296 < u32 X 452 /\
     resweep X = silent (set4 X 456 (u32 X 456 + 1))) \/
  (u32 X 452 <> 0 /\ tb X 450 <> 0 /\ u32 X 452 <= (u32 X 456 + 1) mod 4294967296 /\
     resweep X = silent (rearm X)).
Proof.
  intros X. unfold resweep.
  destruct (Z.eqb_spec (u32 X 452) 0) as [E1|E1]; [left; split; [reflexivity | left; exact E1]|].
  destruct (Z.eqb_spec (tb X 450) 0) as [E2|E2]; [left; split; [reflexivity | right; exact E2]|].
  destruct (Z.leb_spec (u32 X 452) ((u32 X 456 + 1) mod 4294967296)) as [E3|E3].
  - right; right. split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. reflexivity.
  - right; left. split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. reflexivity.
Qed.

Definition complete (T : list byte) : Prop := tb T 437 <> 0 /\ tb T 448 = 0.

Definition phase_le (S S' : list byte) : Prop :=
  complete S' -> complete S /\ tb S' 436 = tb S 436 /\ tb S' 437 = tb S 437 /\ s32 S 440 <= s32 S' 440.

Lemma phase_le_trans : forall S1 S2 S3, phase_le S1 S2 -> phase_le S2 S3 -> phase_le S1 S3.
Proof.
  intros S1 S2 S3 H12 H23 C3. destruct (H23 C3) as (C2 & a & b & c). destruct (H12 C2) as (C1 & a' & b' & c').
  split; [exact C1|]. split; [congruence|]. split; [congruence | lia].
Qed.

Lemma resweep_ok : forall S X, length X = 460%nat -> stepok S X -> scal X ->
  match resweep X with (r, _, Y) => r = 0 /\ stepok S Y /\ scal Y /\ phase_le X Y end.
Proof.
  intros S X HL HX Hs. pose proof (tb_range X 449). pose proof (tb_range X 450). pose proof (tb_range X 436).
  pose proof (u32_range X 452). pose proof (u32_range X 456).
  destruct Hs as (H5 & H6 & (H7a & H7b & H7c & H7d) & H8).
  destruct (resweep_shape X) as [(E & _) | [(E1 & E2 & E3 & E) | (E1 & E2 & E3 & E)]]; rewrite E.
  - split; [reflexivity|]. split; [exact HX|].
    split; [exact (conj H5 (conj H6 (conj (conj H7a (conj H7b (conj H7c H7d))) H8)))|].
    intros C. split; [exact C | lia].
  - split; [reflexivity|]. split.
    + eapply stepok_trans; [exact HX|]. split; [L460|]. split.
      * intros i Hi. rds. reflexivity.
      * split; [intros i Hi; left; rds; reflexivity | rds; reflexivity].
    + split.
      * unfold scal. rds. dec. split; [exact H5|]. split; [exact H6|]. split; [lia|]. lia.
      * intros C. unfold complete in C. revert C. rds. intros C. split; [exact C|]. lia.
  - split; [reflexivity|]. split.
    + eapply stepok_trans; [exact HX|]. unfold rearm. split; [L460|]. split.
      * intros i Hi. rds. dec. reflexivity.
      * split; [intros i Hi; left; rds; dec; reflexivity | rds; reflexivity].
    + split.
      * unfold scal, rearm. rds. dec. rewrite !Z.mod_small by lia.
        split; [right; lia|]. split; [exact H6|]. split; [lia|]. lia.
      * intros C. unfold complete, rearm in C. revert C. rds. dec. intros C. lia.
Qed.

Definition nodirty (S : list byte) : Prop := forall l, 0 <= l < 144 -> tb S (288 + l) = 0.

Lemma next_shape : forall S t, length S = 460%nat -> 0 <= s32 S 440 ->
  (next_model S t = silent S /\ u32 S 432 = 0 /\ tb S 437 = 0) \/
  (exists i, 0 <= i < 144 /\ tb S (288 + i) <> 0 /\ next_model S t = edge_res S i) \/
  (nodirty S /\ tb S 437 = 0 /\ next_model S t = resweep S) \/
  (nodirty S /\ tb S 437 <> 0 /\ 0 < s32 S 444 /\ next_model S t = silent (set4 S 444 (s32 S 444 - 1))) \/
  (nodirty S /\ tb S 437 <> 0 /\ s32 S 444 <= 0 /\ 3 * tb S 437 <= s32 S 440 /\
     next_model S t = resweep (setb S 437 0)) \/
  (nodirty S /\ tb S 437 <> 0 /\ s32 S 444 <= 0 /\ s32 S 440 < 3 * tb S 437 /\
     exists j, s32 S 440 <= j < 3 * tb S 437 /\ carried S (tb S 436) (tb S 448) j = true /\
       (forall k, s32 S 440 <= k < j -> carried S (tb S 436) (tb S 448) k = false) /\
       next_model S t = emit_res (set4 S 440 (j + 1)) t (tb S 436 + j / 3) (j mod 3) j (3 * tb S 437)) \/
  (nodirty S /\ tb S 437 <> 0 /\ s32 S 444 <= 0 /\ s32 S 440 < 3 * tb S 437 /\
     (forall k, s32 S 440 <= k < 3 * tb S 437 -> carried S (tb S 436) (tb S 448) k = false) /\
     next_model S t = resweep (setb (set4 S 440 (3 * tb S 437)) 437 0)).
Proof.
  intros S t HL HX. pose proof (tb_range S 436) as Ra. pose proof (tb_range S 448) as Rb. pose proof (tb_range S 437) as Rc.
  unfold next_model.
  destruct ((u32 S 432 =? 0) && (tb S 437 =? 0)) eqn:E0.
  { left. apply andb_true_iff in E0 as [E1 E2]. apply Z.eqb_eq in E1, E2. split; [reflexivity|]. split; assumption. }
  right. destruct (first_dirty_from S 0 144) as [i|] eqn:Ed.
  { left. apply first_dirty_some in Ed as (H1 & H2 & _). exists i. split; [lia|]. split; [exact H2 | reflexivity]. }
  right. assert (ND : nodirty S) by (intros l Hl; apply (first_dirty_none 144 S 0 Ed); lia).
  unfold after_scan.
  destruct (Z.eqb_spec (tb S 437) 0) as [Ew|Ew]; [left; split; [exact ND|]; split; [exact Ew | reflexivity]|].
  right. destruct (Z.ltb_spec 0 (s32 S 444)) as [Et|Et].
  { left. split; [exact ND|]. split; [exact Ew|]. split; [exact Et | reflexivity]. }
  right. destruct (Z.leb_spec (3 * tb S 437) (s32 S 440)) as [Ex|Ex].
  { left. split; [exact ND|]. split; [exact Ew|]. split; [exact Et|]. split; [exact Ex | reflexivity]. }
  right. destruct (Z.to_nat (3 * tb S 437 - s32 S 440)) as [|n] eqn:En; [lia|].
  rewrite walk_eq by lia.
  destruct (first_carried S (tb S 436) (tb S 448) (s32 S 440) (Datatypes.S n)) as [j|] eqn:Ec.
  - left. apply first_carried_some in Ec as (H1 & H2 & H3).
    split; [exact ND|]. split; [exact Ew|]. split; [exact Et|]. split; [exact Ex|].
    exists j. split; [lia|]. split; [exact H2|]. split; [exact H3 | reflexivity].
  - right. split; [exact ND|]. split; [exact Ew|]. split; [exact Et|]. split; [exact Ex|].
    split; [intros k Hk; apply (first_carried_none (Datatypes.S n) S _ _ _ Ec); lia | reflexivity].
Qed.

Lemma eff_legal : forall T t c q, I1 T -> 0 <= c < 48 -> 0 <= q < 3 -> legal q (eff T t c q).
Proof.
  intros T t c q (P1 & P2 & _) Hc Hq. unfold eff.
  rewrite (proj2 (Z.leb_gt 3 q)) by lia.
  assert (Hd : legal q (dflt q)) by (unfold legal, dflt; destruct (Z.eqb_spec q 2); lia).
  destruct ((t =? 0) || (48 <=? c)); [exact Hd|].
  destruct (Z.eqb_spec (tb T (144 + 3 * c + q)) 0) as [E|E]; [exact Hd|].
  apply P2; [lia | lia |]. pose proof (P1 (3 * c + q) ltac:(lia)) as [B _].
  pose proof (tb_range T (144 + 3 * c + q)). replace (144 + (3 * c + q)) with (144 + 3 * c + q) in B by lia. lia.
Qed.

Definition next_facts (S : list byte) (t : Z) (res : nres) : Prop :=
  match res with
  | (r, (c, p, v), S') =>
      stepok S S' /\ scal S' /\ phase_le S S' /\ (r = 0 \/ r = 1) /\
      (r = 1 ->
         0 <= c < 48 /\ 0 <= p < 3 /\ legal p v /\ (t <> 0 -> v = eff S t c p) /\
         ((tb S (288 + 3 * c + p) <> 0 /\ tb S (144 + 3 * c + p) = 1 /\
           s32 S' 440 = s32 S 440 /\ tb S' 436 = tb S 436 /\ tb S' 437 = tb S 437 /\ tb S' 448 = tb S 448) \/
          (tb S 437 <> 0 /\ exists j, s32 S 440 <= j < 3 * tb S 437 /\ c = tb S 436 + j / 3 /\ p = j mod 3 /\
             (tb S 448 = 0 -> j = s32 S 440) /\ (tb S 448 <> 0 -> tb S (144 + 3 * c + p) <> 0) /\
             s32 S' 440 = j + 1 /\ tb S' 436 = tb S 436 /\ tb S' 448 = tb S 448 /\
             (tb S' 437 = tb S 437 \/ tb S' 437 = 0))))
  end.

Lemma resweep_facts : forall S t X, I1 S -> length X = 460%nat -> stepok S X -> scal X -> phase_le S X ->
  next_facts S t (resweep X).
Proof.
  intros S t X HI HL HX Hs Hp. pose proof (resweep_ok S X HL HX Hs) as R.
  destruct (resweep X) as [[r [[c p] v]] Y]. destruct R as (Er & HY & HsY & HpY).
  split; [exact HY|]. split; [exact HsY|]. split; [exact (phase_le_trans _ _ _ Hp HpY)|].
  split; [left; exact Er|]. intros E1. lia.
Qed.

Lemma next_props : forall S t, I1 S -> length S = 460%nat -> next_facts S t (next_model S t).
Proof.
  intros S t HI HL. pose proof HI as HI0.
  destruct HI as (P1 & P2 & P3 & (P4a & P4b) & P5 & P6 & (P7a & P7b & P7c & P7d) & P8).
  change u32at with u32 in *. change s32at with s32 in *.
  pose proof (tb_range S 436) as R436. pose proof (tb_range S 437) as R437. pose proof (tb_range S 448) as R448.
  pose proof (tb_range S 449). pose proof (tb_range S 450).
  pose proof (u32_range S 452). pose proof (u32_range S 456). pose proof (s32_range S 440). pose proof (s32_range S 444).
  pose proof (I1_scal S HI0) as HsS.
  destruct (next_shape S t HL P7a) as
    [ (E & _) | [ (i & Hi & Hdi & E) | [ (ND & Ew & E) | [ (ND & Ew & Et & E) | [ (ND & Ew & Et & Ex & E) |
      [ (ND & Ew & Et & Ex & j & Hj & Hc & Hkf & E) | (ND & Ew & Et & Ex & Hkf & E) ] ] ] ] ] ]; rewrite E.
  - split; [apply stepok_refl; exact HL|]. split; [exact HsS|]. split; [intros C; split; [exact C | lia]|].
    split; [left; reflexivity|]. intros; lia.
  - unfold edge_res.
    assert (Hd1 : tb S (288 + i) = 1) by (pose proof (P1 i Hi); pose proof (tb_range S (288 + i)); lia).
    assert (Hs1 : tb S (144 + i) = 1) by (apply P3; assumption).
    split.
    { split; [L460|]. split; [intros k Hk; rds; dec; reflexivity|]. split; [|rds; reflexivity].
      intros l Hl. rds. destruct (Z.eqb_spec (288 + l) (288 + i)); [right; reflexivity | left; reflexivity]. }
    split.
    { unfold scal. rds. dec. destruct HsS as (Q5 & Q6 & Q7 & Q8). split; [exact Q5|]. split; [exact Q6|].
      split; [exact Q7|]. intros _. lia. }
    split.
    { intros C. unfold complete in C. revert C. rds. dec. intros C. split; [exact C|]. lia. }
    split; [right; reflexivity|]. intros _.
    replace (3 * (i / 3) + i mod 3) with i by (Z.div_mod_to_equations; lia).
    split; [Z.div_mod_to_equations; lia|]. split; [Z.div_mod_to_equations; lia|].
    split.
    { replace (tb S i) with (tb S (3 * (i / 3) + i mod 3)) by (f_equal; Z.div_mod_to_equations; lia).
      apply P2; [Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia|].
      replace (144 + 3 * (i / 3) + i mod 3) with (144 + i) by (Z.div_mod_to_equations; lia). exact Hs1. }
    split.
    { intros Ht. rewrite eff_cell by (try exact Ht; Z.div_mod_to_equations; lia).
      replace (144 + 3 * (i / 3) + i mod 3) with (144 + i) by (Z.div_mod_to_equations; lia).
      replace (3 * (i / 3) + i mod 3) with i by (Z.div_mod_to_equations; lia).
      rewrite Hs1. reflexivity. }
    left. replace (288 + 3 * (i / 3) + i mod 3) with (288 + i) by (Z.div_mod_to_equations; lia).
    split; [exact Hdi|].
    replace (144 + 3 * (i / 3) + i mod 3) with (144 + i) by (Z.div_mod_to_equations; lia). split; [exact Hs1|].
    rds. dec. split; [reflexivity|]. split; [reflexivity|]. split; reflexivity.
  - apply resweep_facts; [exact HI0 | exact HL | apply stepok_refl; exact HL | exact HsS | intros C; split; [exact C | lia]].
  - split.
    { split; [L460|]. split; [intros k Hk; rds; reflexivity|]. split; [intros l Hl; left; rds; reflexivity | rds; reflexivity]. }
    split.
    { unfold scal. rds. destruct HsS as (Q5 & Q6 & Q7 & Q8). split; [exact Q5|]. split; [exact Q6|]. split; [lia|]. exact Q8. }
    split.
    { intros C. unfold complete in C. revert C. rds. intros C. split; [exact C|]. lia. }
    split; [left; reflexivity|]. intros; lia.
  - apply resweep_facts; [exact HI0 | L460 | | |].
    + split; [L460|]. split; [intros k Hk; rds; dec; reflexivity|].
      split; [intros l Hl; left; rds; dec; reflexivity | rds; reflexivity].
    + unfold scal. rds. dec. destruct HsS as (Q5 & Q6 & Q7 & Q8).
      split; [left; reflexivity|]. split; [exact Q6|]. split; [lia|]. exact Q8.
    + intros C. unfold complete in C. revert C. rds. dec. intros C. lia.
  - unfold emit_res. cbv zeta.
    assert (Hc48 : tb S 436 + j / 3 < 48) by (destruct P5 as [P5|P5]; [lia|]; Z.div_mod_to_equations; lia).
    assert (Hj3 : 0 <= j / 3) by (apply Z.div_pos; lia).
    rewrite (Z.mod_small (tb S 436 + j / 3) 256) by lia.
    assert (HT1 : length (set4 S 440 (j + 1)) = 460%nat) by L460.
    assert (Elow : lowsame S (set4 S 440 (j + 1))) by (intros k Hk; rds; reflexivity).
    assert (Hjm : j = s32 S 440 \/ tb S 448 <> 0).
    { destruct (Z.eqb_spec (tb S 448) 0) as [O0|O0]; [left|right; exact O0].
      destruct (Z.eq_dec j (s32 S 440)) as [Ej|Ej]; [exact Ej|].
      pose proof (Hkf (s32 S 440) ltac:(lia)) as F. unfold carried in F. rewrite O0 in F. discriminate. }
    assert (Hset : tb S 448 <> 0 -> tb S (144 + 3 * (tb S 436 + j / 3) + j mod 3) <> 0).
    { intros O1. unfold carried in Hc. rewrite (proj2 (Z.eqb_neq (tb S 448) 0) O1) in Hc. cbn [orb] in Hc.
      apply andb_true_iff in Hc as [_ Hc]. apply negb_true_iff in Hc. apply Z.eqb_neq in Hc. exact Hc. }
    destruct (Z.ltb_spec (j + 1) (3 * tb S 437)) as [Ej|Ej].
    + split.
      { split; [L460|]. split; [intros k Hk; rds; reflexivity|].
        split; [intros l Hl; left; rds; reflexivity | rds; reflexivity]. }
      split.
      { unfold scal. rds. destruct HsS as (Q5 & Q6 & Q7 & Q8). split; [exact Q5|]. split; [exact Q6|]. split; [lia|]. lia. }
      split.
      { intros C. unfold complete in C. revert C. rds. intros C. split; [exact C|]. lia. }
      split; [right; reflexivity|]. intros _.
      split; [lia|]. split; [apply Z.mod_pos_bound; lia|].
      split; [rewrite (eff_lowsame S (set4 S 440 (j + 1))) by (try exact Elow; try lia; apply Z.mod_pos_bound; lia);
              apply eff_legal; [exact HI0 | lia | apply Z.mod_pos_bound; lia]|].
      split; [intros _; apply eff_lowsame; [exact Elow | lia | apply Z.mod_pos_bound; lia]|].
      right. split; [exact Ew|]. exists j. split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
      split; [intros O0; destruct Hjm as [Hjm|Hjm]; [exact Hjm | lia]|]. split; [exact Hset|].
      rds. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. left; reflexivity.
    + split.
      { split; [L460|]. split; [intros k Hk; rds; dec; reflexivity|].
        split; [intros l Hl; left; rds; dec; reflexivity | rds; reflexivity]. }
      split.
      { unfold scal. rds. dec. destruct HsS as (Q5 & Q6 & Q7 & Q8). split; [left; reflexivity|]. split; [exact Q6|].
        split; [lia|]. lia. }
      split.
      { intros C. unfold complete in C. revert C. rds. dec. intros C. lia. }
      split; [right; reflexivity|]. intros _.
      split; [lia|]. split; [apply Z.mod_pos_bound; lia|].
      split; [rewrite (eff_lowsame S (set4 S 440 (j + 1))) by (try exact Elow; try lia; apply Z.mod_pos_bound; lia);
              apply eff_legal; [exact HI0 | lia | apply Z.mod_pos_bound; lia]|].
      split; [intros _; apply eff_lowsame; [exact Elow | lia | apply Z.mod_pos_bound; lia]|].
      right. split; [exact Ew|]. exists j. split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
      split; [intros O0; destruct Hjm as [Hjm|Hjm]; [exact Hjm | lia]|]. split; [exact Hset|].
      rds. dec. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. right; reflexivity.
  - apply resweep_facts; [exact HI0 | L460 | | |].
    + split; [L460|]. split; [intros k Hk; rds; dec; reflexivity|].
      split; [intros l Hl; left; rds; dec; reflexivity | rds; reflexivity].
    + unfold scal. rds. dec. destruct HsS as (Q5 & Q6 & Q7 & Q8).
      split; [left; reflexivity|]. split; [exact Q6|]. split; [lia|]. exact Q8.
    + intros C. unfold complete in C. revert C. rds. dec. intros C. lia.
Qed.

Lemma I1_next : forall S t, I1 S -> length S = 460%nat ->
  match next_model S t with (_, _, S') => I1 S' /\ length S' = 460%nat end.
Proof.
  intros S t HI HL. pose proof (next_props S t HI HL) as F.
  destruct (next_model S t) as [[r [[c p] v]] S']. destruct F as (Hok & Hs & _).
  split; [exact (I1_step S S' HI Hok Hs) | exact (proj1 Hok)].
Qed.

Lemma next_eff_same : forall S t c q, I1 S -> length S = 460%nat -> 0 <= c < 48 -> 0 <= q < 3 ->
  match next_model S t with (_, _, S') => eff S' t c q = eff S t c q end.
Proof.
  intros S t c q HI HL Hc Hq. pose proof (next_props S t HI HL) as F.
  destruct (next_model S t) as [[r [[c' p'] v]] S']. destruct F as ((_ & Hl & _) & _).
  apply eff_lowsame; assumption.
Qed.

Lemma next_emit : forall S t r c p v S', I1 S -> length S = 460%nat -> t <> 0 ->
  next_model S t = (r, (c, p, v), S') -> (r = 0 \/ r = 1) /\
  (r = 1 ->
    0 <= c < 48 /\ 0 <= p < 3 /\ legal p v /\ v = eff S t c p /\ v = eff S' t c p /\
    ((tb S (288 + 3 * c + p) <> 0 /\ tb S (144 + 3 * c + p) = 1 /\
      s32 S' 440 = s32 S 440 /\ tb S' 436 = tb S 436 /\ tb S' 437 = tb S 437 /\ tb S' 448 = tb S 448) \/
     (tb S 437 <> 0 /\ exists j, s32 S 440 <= j < 3 * tb S 437 /\ c = tb S 436 + j / 3 /\ p = j mod 3 /\
        (tb S 448 = 0 -> j = s32 S 440) /\ (tb S 448 <> 0 -> tb S (144 + 3 * c + p) <> 0) /\
        s32 S' 440 = j + 1 /\ tb S' 436 = tb S 436 /\ tb S' 448 = tb S 448 /\
        (tb S' 437 = tb S 437 \/ tb S' 437 = 0)))).
Proof.
  intros S t r c p v S' HI HL Ht E. pose proof (next_props S t HI HL) as F. rewrite E in F.
  destruct F as ((_ & Hl & _) & _ & _ & Hr & Hf). split; [exact Hr|]. intros E1.
  destruct (Hf E1) as (Hc & Hp & Hlg & Hv & Hrest). split; [exact Hc|]. split; [exact Hp|]. split; [exact Hlg|].
  split; [exact (Hv Ht)|]. split; [rewrite (eff_lowsame S S') by assumption; exact (Hv Ht)|]. exact Hrest.
Qed.

Lemma next_phase : forall S t, I1 S -> length S = 460%nat ->
  match next_model S t with (_, _, S') => phase_le S S' end.
Proof.
  intros S t HI HL. pose proof (next_props S t HI HL) as F.
  destruct (next_model S t) as [[r [[c p] v]] S']. destruct F as (_ & _ & Hp & _). exact Hp.
Qed.

Lemma next_unset_emit : forall S t c p v S', I1 S -> length S = 460%nat ->
  next_model S t = (1, (c, p, v), S') -> tb S (144 + 3 * c + p) = 0 ->
  complete S /\ c = tb S 436 + s32 S 440 / 3 /\ p = s32 S 440 mod 3 /\ s32 S 440 < 3 * tb S 437 /\
  s32 S' 440 = s32 S 440 + 1 /\ 0 <= c < 48 /\ 0 <= p < 3.
Proof.
  intros S t c p v S' HI HL E Hz. pose proof (next_props S t HI HL) as F. rewrite E in F.
  destruct F as (_ & _ & _ & _ & Hf). destruct (Hf eq_refl) as (Hc & Hp & _ & _ & [(_ & H1 & _) | (Hw & j & Hj & Ec & Ep & H0 & Hn & HX & _)]).
  - lia.
  - destruct (Z.eqb_spec (tb S 448) 0) as [O0|O0]; [|exfalso; apply (Hn O0); exact Hz].
    specialize (H0 O0). subst j. split; [split; [exact Hw | exact O0]|].
    split; [exact Ec|]. split; [exact Ep|]. split; [lia|]. split; [exact HX|]. split; assumption.
Qed.

Lemma arm_T_eq : forall T b w, arm_T T b w =
  set4 (setb (setb (setb (set4 (set4 (setb (setb T 436 b) 437 (arm_w b w)) 440 0) 444 0) 448 0) 449 b) 450 (arm_w b w)) 456 0.
Proof. reflexivity. Qed.

Lemma set_resweep_T_eq : forall T per, set_resweep_T T (Z_to_bv 64 per) = set4 (set4 T 452 per) 456 0.
Proof. reflexivity. Qed.

Lemma arm_w_range : forall b w, 0 <= b < 48 -> 0 < w < 256 -> 1 <= arm_w b w /\ b + arm_w b w <= 48 /\ arm_w b w <= w.
Proof. intros b w Hb Hw. unfold arm_w. destruct (Z.ltb_spec 48 (b + w)); lia. Qed.

Lemma I1_arm_T : forall T b w, I1 T -> length T = 460%nat -> 0 <= b < 48 -> 0 < w < 256 ->
  I1 (arm_T T b w) /\ length (arm_T T b w) = 460%nat /\ lowsame T (arm_T T b w) /\
  tb (arm_T T b w) 436 = b /\ tb (arm_T T b w) 437 = arm_w b w /\ tb (arm_T T b w) 448 = 0 /\
  s32 (arm_T T b w) 440 = 0.
Proof.
  intros T b w HI HL Hb Hw. pose proof (arm_w_range b w Hb Hw) as Ha. rewrite arm_T_eq.
  pose proof (u32_range T 452). pose proof (s32_range T 440).
  pose proof (I1_scal T HI) as (Q5 & Q6 & Q7 & Q8).
  assert (Hok : stepok T (set4 (setb (setb (setb (set4 (set4 (setb (setb T 436 b) 437 (arm_w b w)) 440 0) 444 0) 448 0) 449 b) 450 (arm_w b w)) 456 0)).
  { split; [L460|]. split; [intros i Hi; rds; dec; reflexivity|].
    split; [intros l Hl; left; rds; dec; reflexivity | rds; reflexivity]. }
  split.
  { apply (I1_step T); [exact HI | exact Hok|]. unfold scal. rds. dec. rewrite !Z.mod_small by lia.
    split; [right; lia|]. split; [right; lia|]. split; [lia|]. lia. }
  split; [L460|]. split; [exact (proj1 (proj2 Hok))|]. rds. dec. rewrite !Z.mod_small by lia.
  split; [reflexivity|]. split; [reflexivity|]. split; reflexivity.
Qed.

Lemma I1_set_resweep_T : forall T per, I1 T -> length T = 460%nat ->
  I1 (set_resweep_T T (Z_to_bv 64 per)) /\ length (set_resweep_T T (Z_to_bv 64 per)) = 460%nat /\
  lowsame T (set_resweep_T T (Z_to_bv 64 per)) /\
  tb (set_resweep_T T (Z_to_bv 64 per)) 436 = tb T 436 /\ tb (set_resweep_T T (Z_to_bv 64 per)) 437 = tb T 437 /\
  tb (set_resweep_T T (Z_to_bv 64 per)) 448 = tb T 448.
Proof.
  intros T per HI HL. rewrite set_resweep_T_eq. pose proof (I1_scal T HI) as (Q5 & Q6 & Q7 & Q8).
  assert (Hok : stepok T (set4 (set4 T 452 per) 456 0)).
  { split; [L460|]. split; [intros i Hi; rds; reflexivity|]. split; [intros l Hl; left; rds; reflexivity | rds; reflexivity]. }
  split.
  { apply (I1_step T); [exact HI | exact Hok|]. unfold scal. rds. dec.
    split; [exact Q5|]. split; [exact Q6|]. split; [exact Q7|]. intros _. pose proof (Z.mod_pos_bound per 4294967296). lia. }
  split; [L460|]. split; [exact (proj1 (proj2 Hok))|]. rds. split; [reflexivity|]. split; reflexivity.
Qed.
