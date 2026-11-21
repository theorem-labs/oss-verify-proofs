(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItDefs.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItGen.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItMath.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Lemma countz_nil : forall x, countz x [] = 0.
Proof. reflexivity. Qed.
Lemma countz_cons : forall x a l, countz x (a :: l) = (if x =? a then 1 else 0) + countz x l.
Proof.
  intros x a l. unfold countz. cbn [filter]. destruct (x =? a); [rewrite zlength_cons|]; lia.
Qed.
Lemma countz_app : forall x l1 l2, countz x (l1 ++ l2) = countz x l1 + countz x l2.
Proof.
  intros x l1 l2. induction l1 as [|a l1 IH]; [cbn; reflexivity|].
  cbn [app]. rewrite !countz_cons, IH. lia.
Qed.
Lemma countz_nonneg : forall x l, 0 <= countz x l.
Proof. intros. unfold countz. apply zlength_nonneg. Qed.
Lemma countz_le_length : forall x l, countz x l <= zlength l.
Proof.
  intros x l. induction l as [|a l IH]; [unfold countz; cbn [filter]; rewrite !zlength_nil; lia|]. rewrite countz_cons, zlength_cons. destruct (x =? a); lia.
Qed.

Lemma firstn_S_nth : forall {A} (l : list A) n d, (n < length l)%nat ->
  firstn (S n) l = firstn n l ++ [nth n l d].
Proof.
  intros A l. induction l as [|a l IH]; intros n d Hn; [cbn in Hn; lia|].
  destruct n as [|n]; [reflexivity|]. cbn [firstn nth]. rewrite (IH n d) by (cbn in Hn; lia). reflexivity.
Qed.

Lemma countz_firstn_S : forall x l n, (n < length l)%nat ->
  countz x (firstn (S n) l) = countz x (firstn n l) + (if x =? nth n l 0 then 1 else 0).
Proof.
  intros x l n Hn. rewrite (firstn_S_nth l n 0 Hn). rewrite countz_app, countz_cons, countz_nil. lia.
Qed.

Lemma countz_firstn_le : forall x l n, countz x (firstn n l) <= countz x l.
Proof.
  intros x l n. rewrite <- (firstn_skipn n l) at 2. rewrite countz_app. pose proof (countz_nonneg x (skipn n l)). lia.
Qed.

Lemma countz_firstn_mono : forall x l n m, (n <= m)%nat -> countz x (firstn n l) <= countz x (firstn m l).
Proof.
  intros x l n m H. rewrite <- (firstn_skipn n (firstn m l)), firstn_firstn.
  replace (Nat.min n m) with n by lia. rewrite countz_app. pose proof (countz_nonneg x (skipn n (firstn m l))). lia.
Qed.


Definition sel (p : Z -> bool) (n : nat) : list Z := filter p (map Z.of_nat (seq 0 n)).

Lemma sel_S : forall p n, sel p (S n) = sel p n ++ (if p (Z.of_nat n) then [Z.of_nat n] else []).
Proof.
  intros p n. unfold sel. rewrite seq_S, map_app, filter_app. cbn [map filter Nat.add]. reflexivity.
Qed.

Lemma sel_spec : forall p n r, (r < length (sel p n))%nat ->
  let s := nth r (sel p n) 0 in
  p s = true /\ 0 <= s < Z.of_nat n /\ length (sel p (Z.to_nat s)) = r.
Proof.
  intros p n. induction n as [|n IH]; intros r Hr.
  - cbn in Hr. lia.
  - rewrite sel_S in *. destruct (p (Z.of_nat n)) eqn:E.
    + rewrite app_length in Hr. cbn [length] in Hr.
      destruct (Nat.lt_ge_cases r (length (sel p n))) as [H|H].
      * cbn zeta. rewrite app_nth1 by exact H. destruct (IH r H) as [A [B C]]. repeat split; try assumption; lia.
      * assert (r = length (sel p n)) by lia. subst r. cbn zeta.
        rewrite app_nth2, Nat.sub_diag by lia. cbn [nth]. rewrite Nat2Z.id.
        repeat split; try assumption; lia.
    + rewrite app_nil_r in *. destruct (IH r Hr) as [A [B C]]. cbn zeta. repeat split; try assumption; lia.
Qed.


Lemma nth_map_seq : forall {B} (f : nat -> B) len n d, (n < len)%nat -> nth n (map f (seq 0 len)) d = f n.
Proof.
  intros B f len n d H. rewrite (nth_indep _ d (f 0%nat)) by (rewrite map_length, seq_length; lia).
  rewrite map_nth. rewrite seq_nth by lia. reflexivity.
Qed.

Section LL.
  Variable ll : list Z.
  Hypothesis Hll : Forall (fun l => 0 <= l <= 15) ll.
  #[local] Set Default Proof Using "Hll".

  Local Notation wl := (wl_of ll).
  Local Notation W := (W (wl_of ll)).
  Local Notation NC := (NC ll).
  Local Notation LofS := (LofS ll).

  Lemma wl_of_length : length wl = 16%nat.
  Proof. unfold wl_of. rewrite map_length, seq_length. reflexivity. Qed.

  Lemma W_of : forall l, 0 <= l <= 15 -> W l = countz l ll.
  Proof.
    intros l Hl. unfold ItDefs.W, wl_of. rewrite nth_map_seq by lia. f_equal. lia.
  Qed.

  Lemma W_of_nonneg : forall l, 0 <= W l.
  Proof.
    intros l. unfold ItDefs.W. destruct (Nat.lt_ge_cases (Z.to_nat l) 16) as [H|H].
    - unfold wl_of. rewrite nth_map_seq by lia. apply countz_nonneg.
    - rewrite nth_overflow by (rewrite wl_of_length; lia). lia.
  Qed.

  Let HW := W_of_nonneg.
  Let HL := wl_of_length.

  Lemma LofS_range : forall s, 0 <= s < NC -> 0 <= LofS s <= 15.
  Proof.
    intros s Hs. unfold ItDefs.LofS. apply (Forall_nth (fun l => 0 <= l <= 15) ll); [exact Hll|]. unfold ItDefs.NC, zlength in Hs. lia.
  Qed.

  Lemma sel_countz : forall l n, (n <= length ll)%nat ->
    Z.of_nat (length (sel (fun s => LofS s =? l) n)) = countz l (firstn n ll).
  Proof.
    intros l n. induction n as [|n IH]; intros Hn.
    - cbn. reflexivity.
    - rewrite sel_S, app_length, Nat2Z.inj_add, IH by lia.
      rewrite countz_firstn_S by lia. unfold ItDefs.LofS. rewrite Nat2Z.id.
      rewrite (Z.eqb_sym (nth n ll 0) l). destruct (l =? nth n ll 0); cbn [length]; lia.
  Qed.

  Lemma syms_of_sel : forall l, syms_of ll l = sel (fun s => LofS s =? l) (length ll).
  Proof. intros l. unfold syms_of, sel, ItDefs.NC, zlength. rewrite Nat2Z.id. reflexivity. Qed.

  Lemma syms_of_length : forall l, Z.of_nat (length (syms_of ll l)) = countz l ll.
  Proof.
    intros l. rewrite syms_of_sel, sel_countz by lia. rewrite firstn_all. reflexivity.
  Qed.

  Lemma SYM_spec : forall l r, 0 <= r < countz l ll ->
    0 <= SYM ll l r < NC /\ LofS (SYM ll l r) = l /\ countz l (firstn (Z.to_nat (SYM ll l r)) ll) = r.
  Proof.
    intros l r Hr. unfold SYM. rewrite syms_of_sel.
    pose proof (syms_of_length l) as SL. rewrite syms_of_sel in SL.
    pose proof (sel_spec (fun s => LofS s =? l) (length ll) (Z.to_nat r) ltac:(lia)) as [A [B C]].
    cbn zeta in *. set (s := nth (Z.to_nat r) (sel (fun s => LofS s =? l) (length ll)) 0) in *.
    apply Z.eqb_eq in A. split; [unfold ItDefs.NC, zlength; lia|]. split; [exact A|].
    rewrite <- sel_countz by lia. lia.
  Qed.

  Lemma countz_firstn_lt : forall s, 0 <= s < NC ->
    countz (LofS s) (firstn (Z.to_nat s) ll) < countz (LofS s) ll.
  Proof.
    intros s Hs. unfold ItDefs.NC, zlength in Hs.
    pose proof (countz_firstn_S (LofS s) ll (Z.to_nat s) ltac:(lia)) as E.
    unfold ItDefs.LofS in E at 3. rewrite Z.eqb_refl in E.
    pose proof (countz_firstn_le (LofS s) ll (S (Z.to_nat s))). lia.
  Qed.

  Definition sidx (s : Z) : Z := OFF wl (LofS s) + countz (LofS s) (firstn (Z.to_nat s) ll).

  Lemma sidx_range : forall s, 0 <= s < NC -> LofS s <> 0 ->
    OFF wl (LofS s) <= sidx s < OFF wl (LofS s + 1) /\ 1 <= LofS s <= 15.
  Proof.
    intros s Hs Hnz. pose proof (LofS_range s Hs) as LR. unfold sidx.
    rewrite (OFF_step wl HW HL (LofS s)) by lia. rewrite W_of by lia.
    pose proof (countz_firstn_lt s Hs). pose proof (countz_nonneg (LofS s) (firstn (Z.to_nat s) ll)). lia.
  Qed.

  Lemma sidx_inj : forall s1 s2, 0 <= s1 < NC -> 0 <= s2 < NC -> LofS s1 <> 0 -> LofS s2 <> 0 ->
    sidx s1 = sidx s2 -> s1 = s2.
  Proof.
    intros s1 s2 H1 H2 N1 N2 E.
    pose proof (sidx_range s1 H1 N1) as [R1 L1]. pose proof (sidx_range s2 H2 N2) as [R2 L2].
    destruct (Z.eq_dec (LofS s1) (LofS s2)) as [EL|NL].
    -
      destruct (Z.lt_total s1 s2) as [LT|[EQ|GT]]; [|exact EQ|]; exfalso.
      + pose proof (countz_firstn_S (LofS s1) ll (Z.to_nat s1) ltac:(unfold ItDefs.NC, zlength in H1; lia)) as X.
        unfold ItDefs.LofS in X at 3. rewrite Z.eqb_refl in X.
        pose proof (countz_firstn_mono (LofS s1) ll (S (Z.to_nat s1)) (Z.to_nat s2) ltac:(lia)).
        unfold sidx in E. rewrite <- EL in E. lia.
      + pose proof (countz_firstn_S (LofS s2) ll (Z.to_nat s2) ltac:(unfold ItDefs.NC, zlength in H2; lia)) as X.
        unfold ItDefs.LofS in X at 3. rewrite Z.eqb_refl in X.
        pose proof (countz_firstn_mono (LofS s2) ll (S (Z.to_nat s2)) (Z.to_nat s1) ltac:(lia)).
        unfold sidx in E. rewrite EL in E. lia.
    - exfalso.
      destruct (Z.lt_total (LofS s1) (LofS s2)) as [LT|[EQ|GT]]; [|contradiction|].
      + pose proof (OFF_mono wl HW HL (LofS s1 + 1) (LofS s2) ltac:(lia)). lia.
      + pose proof (OFF_mono wl HW HL (LofS s2 + 1) (LofS s1) ltac:(lia)). lia.
  Qed.

  Lemma sidx_SYM : forall l r, 1 <= l <= 15 -> 0 <= r < W l -> sidx (SYM ll l r) = OFF wl l + r.
  Proof.
    intros l r Hl Hr. rewrite W_of in Hr by lia. pose proof (SYM_spec l r Hr) as [A [B C]].
    unfold sidx. rewrite B, C. reflexivity.
  Qed.

  Lemma In_sort_writes : forall i v,
    In (i, v) (sort_writes wl ll) <-> 0 <= v < NC /\ LofS v <> 0 /\ i = sidx v.
  Proof.
    intros i v. unfold sort_writes. rewrite in_flat_map. split.
    - intros [s [Hs Hin]]. apply in_map_iff in Hs as [n [<- Hn]]. apply in_seq in Hn.
      destruct (Z.eqb_spec (LofS (Z.of_nat n)) 0) as [E|E]; [destruct Hin|].
      destruct Hin as [Hin|[]]. injection Hin; intros <- <-.
      split; [unfold ItDefs.NC, zlength in *; lia|]. split; [exact E|]. unfold sidx. rewrite Nat2Z.id. reflexivity.
    - intros [Hv [Hnz ->]]. exists v. split.
      + apply in_map_iff. exists (Z.to_nat v). split; [lia|]. apply in_seq. unfold ItDefs.NC, zlength in *. lia.
      + destruct (Z.eqb_spec (LofS v) 0); [contradiction|]. left. reflexivity.
  Qed.

  Lemma sort_writes_range : forall i v, In (i, v) (sort_writes wl ll) -> 0 <= i < NZ wl /\ 0 <= v < NC.
  Proof.
    intros i v H. apply In_sort_writes in H as [Hv [Hnz ->]].
    pose proof (sidx_range v Hv Hnz) as [R L].
    pose proof (OFF_nonneg wl HW HL (LofS v)). pose proof (OFF_mono wl HW HL (LofS v + 1) 16 ltac:(lia)).
    unfold ItDefs.NZ. lia.
  Qed.

  Lemma sorted_cell : forall work l r, 1 <= l <= 15 -> 0 <= r < W l -> NZ wl <= arr_len work ->
    arr_get (applyw (sort_writes wl ll) work) (OFF wl l + r) = SYM ll l r.
  Proof.
    intros work l r Hl Hr Hlen.
    pose proof Hr as Hr'. rewrite W_of in Hr' by lia. pose proof (SYM_spec l r Hr') as [A [B C]].
    assert (Hin : In (OFF wl l + r, SYM ll l r) (sort_writes wl ll)).
    { apply In_sort_writes. split; [exact A|]. split; [rewrite B; lia|]. symmetry. apply sidx_SYM; assumption. }
    pose proof (sort_writes_range _ _ Hin) as [R _].
    apply (applyw_all (fun i v => i = OFF wl l + r -> v = SYM ll l r)); [| eapply in_map_fst; exact Hin | lia | reflexivity].
    intros j v Hj ->. apply In_sort_writes in Hj as [Hv [Hnz E]].
    apply sidx_inj; try assumption; [rewrite B; lia|]. rewrite <- E. symmetry. apply sidx_SYM; assumption.
  Qed.

  Lemma sorted_work : forall work k, NZ wl <= arr_len work -> 0 <= k < NZ wl ->
    arr_get (applyw (sort_writes wl ll) work) k = wsym wl ll k.
  Proof.
    intros work k Hlen Hk.
    pose proof (len_at_spec wl HW HL k Hk) as [L O]. pose proof (rank_at_spec wl HW HL k Hk) as R.
    unfold wsym. replace k with (OFF wl (len_at wl k) + rank_at wl k) at 1 by (unfold rank_at; lia).
    apply sorted_cell; assumption.
  Qed.

  Lemma wsym_spec : forall k, 0 <= k < NZ wl -> 0 <= wsym wl ll k < NC /\ LofS (wsym wl ll k) = len_at wl k.
  Proof.
    intros k Hk.
    pose proof (len_at_spec wl HW HL k Hk) as [L O]. pose proof (rank_at_spec wl HW HL k Hk) as R.
    rewrite W_of in R by lia. pose proof (SYM_spec (len_at wl k) (rank_at wl k) R) as [A [B C]].
    unfold wsym. split; assumption.
  Qed.

  Lemma sum_countz : forall xs, Forall (fun l => 0 <= l <= 15) xs ->
    sumz (fun l => countz l xs) 0 16 = zlength xs.
  Proof.
    intros xs Hxs. induction xs as [|x xs IH].
    - rewrite (@zlength_nil Z). apply sumz_zero. intros; reflexivity.
    - apply Forall_cons_iff in Hxs as [Hx Hxs]. rewrite zlength_cons, <- (IH Hxs).
      rewrite (sumz_ext (fun l => countz l (x :: xs)) (fun l => (if l =? x then 1 else 0) + countz l xs)) by (intros; apply countz_cons).
      rewrite sumz_add, sumz_indicator by lia.
      destruct (Z.leb_spec 0 x), (Z.ltb_spec x 16); cbn [andb]; lia.
  Qed.

  Lemma NZ_le_NC : NZ wl <= NC.
  Proof.
    unfold ItDefs.NZ, ItDefs.OFF, ItDefs.NC. rewrite <- (sum_countz ll Hll).
    rewrite (sumz_cons (fun l => countz l ll) 0 16) by lia.
    rewrite (sumz_ext (ItDefs.W wl) (fun l => countz l ll) 1 16) by (intros; apply W_of; lia).
    pose proof (countz_nonneg 0 ll). change (0 + 1) with 1. lia.
  Qed.

End LL.
