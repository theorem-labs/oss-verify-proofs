(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import EbrInv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition art_inw (lo len : Z) (it : Z * Z) : bool := (lo <=? fst it) && (fst it <? lo + len).
Definition art_cntw (lo len : Z) (l : list (Z * Z)) : Z := Z.of_nat (length (List.filter (art_inw lo len) l)).

Lemma art_cntw_range : forall lo len l, 0 <= art_cntw lo len l <= Z.of_nat (length l).
Proof. intros lo len l. unfold art_cntw. pose proof (List.filter_length_le (art_inw lo len) l). lia. Qed.

Lemma art_inj_length : forall (A B : Type) (f : A -> B) (l : list A) (m : list B),
  List.NoDup l -> (forall x y, In x l -> In y l -> f x = f y -> x = y) -> (forall x, In x l -> In (f x) m) ->
  (length l <= length m)%nat.
Proof.
  intros A B f l m ND INJ INC. rewrite <- (length_map f l).
  apply NoDup_incl_length.
  - apply NoDup_map_NoDup_ForallPairs; [|exact ND]. intros x y Hx Hy E. exact (INJ x y Hx Hy E).
  - intros y Hy. apply in_map_iff in Hy. destruct Hy as (x & <- & Hx). exact (INC x Hx).
Qed.

Definition art_is_free (s : art_cst) : bool := match s with CFree => true | _ => false end.
Definition art_is_alloc (s : art_cst) : bool := match s with CAlloc _ _ => true | _ => false end.
Definition art_is_quar (s : art_cst) : bool := match s with CQuar _ _ => true | _ => false end.
Definition art_is_batch (s : art_cst) : bool := match s with CBatch => true | _ => false end.

Lemma art_partition4 : forall (A : Type) (st : A -> art_cst) (l : list A),
  length l = (length (List.filter (fun x => art_is_free (st x)) l) + length (List.filter (fun x => art_is_alloc (st x)) l)
              + length (List.filter (fun x => art_is_quar (st x)) l) + length (List.filter (fun x => art_is_batch (st x)) l))%nat.
Proof.
  intros A st l. induction l as [|x r IH]; [reflexivity|]. cbn [List.filter length].
  destruct (st x); cbn [art_is_free art_is_alloc art_is_quar art_is_batch length]; lia.
Qed.

Definition art_st_item (s : art_cst) : Z * Z := match s with CAlloc u n => (u - 16, n) | CQuar u n => (u - 16, n) | _ => (0, 0) end.

Section Count.
Variable st : Z -> art_cst.
Variables (cf : list Z) (hb items : list (Z * Z)) (baddrs : list Z).
Variables (rb sz q : Z) (K : nat).
Hypothesis Hsz : sz = 16 * q.
Hypothesis Hq : 0 < q.

Hypothesis ST : forall i, 0 <= i < Z.of_nat K ->
  match st (q * i) with
  | CFree => In (q * i) cf
  | CAlloc u n => In (u - 16, n) hb /\ rb + sz * i + 16 <= u /\ u < rb + sz * i + sz
  | CQuar u n => In (u - 16, n) items /\ rb + sz * i + 16 <= u /\ u < rb + sz * i + sz
  | CBatch => In (rb + sz * i) baddrs
  end.

Let I : list Z := map Z.of_nat (seq 0 K).
Lemma art_I_in : forall i, In i I <-> 0 <= i < Z.of_nat K.
Proof.
  intros i. unfold I. rewrite in_map_iff. split.
  - intros (k & <- & Hk). apply in_seq in Hk. lia.
  - intros Hi. exists (Z.to_nat i). split; [lia|]. apply in_seq. lia.
Qed.
Lemma art_I_nodup : List.NoDup I.
Proof.
  unfold I. apply NoDup_map_NoDup_ForallPairs; [|apply seq_NoDup]. intros x y _ _ E. lia.
Qed.
Lemma art_I_len : length I = K.
Proof. unfold I. rewrite length_map, length_seq. reflexivity. Qed.

Lemma art_count_pure :
  Z.of_nat K <= Z.of_nat (length cf) + art_cntw rb (sz * Z.of_nat K) hb + art_cntw rb (sz * Z.of_nat K) items + Z.of_nat (length baddrs).
Proof.
  pose proof (art_partition4 Z (fun i => st (q * i)) I) as P. rewrite art_I_len in P.
  assert (Hsz0 : 0 < sz) by lia.

  assert (F : (length (List.filter (fun i => art_is_free (st (q * i))) I) <= length cf)%nat).
  { apply (art_inj_length Z Z (fun i => q * i)).
    - apply NoDup_filter. exact art_I_nodup.
    - intros x y _ _ E. nia.
    - intros x Hx. apply filter_In in Hx. destruct Hx as (Hx & Sx). apply art_I_in in Hx. pose proof (ST x Hx) as S.
      destruct (st (q * x)); try discriminate. exact S. }

  assert (A : (length (List.filter (fun i => art_is_alloc (st (q * i))) I) <= length (List.filter (art_inw rb (sz * Z.of_nat K)) hb))%nat).
  { apply (art_inj_length Z (Z * Z) (fun i => art_st_item (st (q * i)))).
    - apply NoDup_filter. exact art_I_nodup.
    - intros x y Hx Hy E. apply filter_In in Hx, Hy. destruct Hx as (Hx & Sx), Hy as (Hy & Sy). apply art_I_in in Hx, Hy.
      pose proof (ST x Hx) as S1. pose proof (ST y Hy) as S2.
      destruct (st (q * x)) as [|u n| |]; try discriminate. destruct (st (q * y)) as [|u' n'| |]; try discriminate.
      cbn [art_st_item] in E. injection E as E1 E2. assert (u = u') by lia. subst u'.
      destruct S1 as (_ & L1 & U1), S2 as (_ & L2 & U2). nia.
    - intros x Hx. apply filter_In in Hx. destruct Hx as (Hx & Sx). apply art_I_in in Hx. pose proof (ST x Hx) as S.
      destruct (st (q * x)) as [|u n| |]; try discriminate. destruct S as (S1 & S2 & S3). cbn [art_st_item].
      apply filter_In. split; [exact S1|]. unfold art_inw. cbn [fst]. apply andb_true_iff. split; [apply Z.leb_le; nia | apply Z.ltb_lt; nia]. }

  assert (Q : (length (List.filter (fun i => art_is_quar (st (q * i))) I) <= length (List.filter (art_inw rb (sz * Z.of_nat K)) items))%nat).
  { apply (art_inj_length Z (Z * Z) (fun i => art_st_item (st (q * i)))).
    - apply NoDup_filter. exact art_I_nodup.
    - intros x y Hx Hy E. apply filter_In in Hx, Hy. destruct Hx as (Hx & Sx), Hy as (Hy & Sy). apply art_I_in in Hx, Hy.
      pose proof (ST x Hx) as S1. pose proof (ST y Hy) as S2.
      destruct (st (q * x)) as [| |u n|]; try discriminate. destruct (st (q * y)) as [| |u' n'|]; try discriminate.
      cbn [art_st_item] in E. injection E as E1 E2. assert (u = u') by lia. subst u'.
      destruct S1 as (_ & L1 & U1), S2 as (_ & L2 & U2). nia.
    - intros x Hx. apply filter_In in Hx. destruct Hx as (Hx & Sx). apply art_I_in in Hx. pose proof (ST x Hx) as S.
      destruct (st (q * x)) as [| |u n|]; try discriminate. destruct S as (S1 & S2 & S3). cbn [art_st_item].
      apply filter_In. split; [exact S1|]. unfold art_inw. cbn [fst]. apply andb_true_iff. split; [apply Z.leb_le; nia | apply Z.ltb_lt; nia]. }

  assert (B : (length (List.filter (fun i => art_is_batch (st (q * i))) I) <= length baddrs)%nat).
  { apply (art_inj_length Z Z (fun i => rb + sz * i)).
    - apply NoDup_filter. exact art_I_nodup.
    - intros x y _ _ E. nia.
    - intros x Hx. apply filter_In in Hx. destruct Hx as (Hx & Sx). apply art_I_in in Hx. pose proof (ST x Hx) as S.
      destruct (st (q * x)); try discriminate. exact S. }
  unfold art_cntw. lia.
Qed.
End Count.
