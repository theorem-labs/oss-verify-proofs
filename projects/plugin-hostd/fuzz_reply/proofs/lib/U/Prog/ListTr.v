From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import RelayRunT TrNames HarnessRep ListRep.
Import ListNotations.
Local Open Scope Z_scope.

Notation tad := (addr sptr).
Notation tev := (rev sptr).

Definition pdefT : sptr := SP 0 0.

Record shl := SHL { sh_v : tad; sh_cap : Z; sh_recs : list (tad * list Z) }.

Definition sh_n (s : shl) : Z := Z.of_nat (length (sh_recs s)).

Definition sh_keys (s : shl) : list (list Z) := map snd (sh_recs s).

Definition rec_len (r : tad * list Z) : Z := Z.of_nat (length (snd r)) + 1.

Definition shr (nm : Z -> tad) (r : Z * list byte) : tad * list Z := (nm (fst r), bzs (snd r)).

Definition sh_of (nm : Z -> tad) (l : hlist) : shl := SHL (nm (hl_v l)) (hl_cap l) (map (shr nm) (hl_recs l)).

Definition list_grow_tr (s : shl) : list tev :=
  if sh_n s =? sh_cap s then
    (if sh_cap s =? 0 then [RMalloc 128] else [RRealloc (16 * sh_cap s) (32 * sh_cap s) (sh_v s)])
  else [].

Definition list_push_tr (s : shl) (x : list Z) : list tev := list_grow_tr s ++ [RMalloc (Z.of_nat (length x) + 1)].

Definition list_push_sh (j : nat) (s : shl) (x : list Z) : shl :=
  if sh_n s =? sh_cap s then SHL (Ret j) (grow_cap (sh_n s) (sh_cap s)) (sh_recs s ++ [(Ret (S j), x)])
  else SHL (sh_v s) (sh_cap s) (sh_recs s ++ [(Ret j, x)]).

Definition rec_drop_tr (r : tad * list Z) : list tev := [RFree (rec_len r) (fst r)].

Definition recs_drop_tr (rs : list (tad * list Z)) : list tev := concat (map rec_drop_tr rs).

Definition list_drop_tr (s : shl) (i : nat) : list tev := rec_drop_tr (nth i (sh_recs s) (Known pdefT, [])).

Definition list_drop_sh (s : shl) (i : nat) : shl :=
  SHL (sh_v s) (sh_cap s) (firstn i (sh_recs s) ++ skipn (S i) (sh_recs s)).

Definition list_free_tr (s : shl) : list tev :=
  recs_drop_tr (List.rev (sh_recs s)) ++ (if sh_cap s =? 0 then [] else [RFree (16 * sh_cap s) (sh_v s)]).

Definition empty_sh : shl := SHL (Known pdefT) 0 [].

Definition list_push_tra (v : tad) (N CAP n : Z) : list tev :=
  (if N =? CAP then (if CAP =? 0 then [RMalloc 128] else [RRealloc (16 * CAP) (32 * CAP) v]) else []) ++
  [RMalloc (n + 1)].

Definition list_drop_tra (a : tad) (n : Z) : list tev := [RFree (n + 1) a].

Lemma list_push_tr_tra : forall s x,
    list_push_tr s x = list_push_tra (sh_v s) (sh_n s) (sh_cap s) (Z.of_nat (length x)).
Proof. reflexivity. Qed.

Lemma list_drop_tr_tra : forall s i,
    list_drop_tr s i = list_drop_tra (fst (nth i (sh_recs s) (Known pdefT, [])))
                                     (Z.of_nat (length (snd (nth i (sh_recs s) (Known pdefT, []))))).
Proof. reflexivity. Qed.

Lemma nret_list_grow : forall s, nret sptr (list_grow_tr s) = (if Z.eqb (sh_n s) (sh_cap s) then 1 else 0)%nat.
Proof.
  intros s. unfold list_grow_tr. destruct (sh_n s =? sh_cap s); [|reflexivity].
  destruct (sh_cap s =? 0); reflexivity.
Qed.

Lemma nret_list_push : forall s x, nret sptr (list_push_tr s x) = (if Z.eqb (sh_n s) (sh_cap s) then 2 else 1)%nat.
Proof.
  intros s x. unfold list_push_tr. rewrite nret_app, nret_list_grow. simpl.
  destruct (sh_n s =? sh_cap s); reflexivity.
Qed.

Lemma nret_recs_drop : forall rs, nret sptr (recs_drop_tr rs) = 0%nat.
Proof. induction rs as [|r rs IH]; [reflexivity|]. simpl. exact IH. Qed.

Lemma nret_list_drop : forall s i, nret sptr (list_drop_tr s i) = 0%nat.
Proof. reflexivity. Qed.

Lemma nret_list_free : forall s, nret sptr (list_free_tr s) = 0%nat.
Proof.
  intros s. unfold list_free_tr. rewrite nret_app, nret_recs_drop. destruct (sh_cap s =? 0); reflexivity.
Qed.

Lemma Forall2_rev_l : forall (A B : Type) (Rr : A -> B -> Prop) l1 l2,
  Forall2 Rr l1 l2 -> Forall2 Rr (List.rev l1) (List.rev l2).
Proof.
  intros A B Rr l1 l2 H. induction H as [|x y l1 l2 Hxy _ IH]; [constructor|].
  simpl. apply Forall2_app; [exact IH | constructor; [exact Hxy | constructor]].
Qed.

Section Rel.
Variables (qs1 qs2 : list sptr).

Definition rec_rel (r1 r2 : tad * list Z) : Prop := snd r1 = snd r2 /\ ad_eq sptr pdefT qs1 qs2 (fst r1) (fst r2).

Definition sh_rel (s1 s2 : shl) : Prop :=
  sh_cap s1 = sh_cap s2 /\ (sh_cap s2 <> 0 -> ad_eq sptr pdefT qs1 qs2 (sh_v s1) (sh_v s2)) /\
  Forall2 rec_rel (sh_recs s1) (sh_recs s2).

Lemma sh_rel_n : forall s1 s2, sh_rel s1 s2 -> sh_n s1 = sh_n s2.
Proof. intros s1 s2 (_ & _ & H). unfold sh_n. now rewrite (Forall2_length H). Qed.

Lemma sh_rel_keys : forall s1 s2, sh_rel s1 s2 -> sh_keys s1 = sh_keys s2.
Proof.
  intros s1 s2 (_ & _ & H). unfold sh_keys. induction H as [|r1 r2 l1 l2 Hr _ IH]; [reflexivity|].
  simpl. rewrite IH, (proj1 Hr). reflexivity.
Qed.

Lemma rec_drop_rel : forall r1 r2, rec_rel r1 r2 -> tr_rel sptr pdefT qs1 qs2 (rec_drop_tr r1) (rec_drop_tr r2).
Proof.
  intros [a1 x1] [a2 x2] [Hx Ha]. simpl in Hx, Ha. subst x2. unfold rec_drop_tr, rec_len. simpl.
  constructor; [constructor; exact Ha | constructor].
Qed.

Lemma recs_drop_rel : forall l1 l2, Forall2 rec_rel l1 l2 -> tr_rel sptr pdefT qs1 qs2 (recs_drop_tr l1) (recs_drop_tr l2).
Proof.
  intros l1 l2 H. unfold recs_drop_tr. apply tr_rel_concat.
  induction H as [|r1 r2 l1 l2 Hr _ IH]; [constructor|]. simpl. constructor; [apply rec_drop_rel, Hr | exact IH].
Qed.

Lemma list_grow_rel : forall s1 s2, sh_rel s1 s2 -> tr_rel sptr pdefT qs1 qs2 (list_grow_tr s1) (list_grow_tr s2).
Proof.
  intros s1 s2 H. pose proof (sh_rel_n _ _ H) as En. destruct H as (Ec & Ev & _).
  unfold list_grow_tr. rewrite En, Ec.
  destruct (sh_n s2 =? sh_cap s2); [|constructor].
  destruct (Z.eqb_spec (sh_cap s2) 0) as [E0|E0]; [repeat constructor|].
  constructor; [constructor; exact (Ev E0) | constructor].
Qed.

Lemma list_push_rel : forall s1 s2 x, sh_rel s1 s2 -> tr_rel sptr pdefT qs1 qs2 (list_push_tr s1 x) (list_push_tr s2 x).
Proof.
  intros s1 s2 x H. unfold list_push_tr. apply tr_rel_app; [apply list_grow_rel, H | repeat constructor].
Qed.

Lemma list_free_rel : forall s1 s2, sh_rel s1 s2 -> tr_rel sptr pdefT qs1 qs2 (list_free_tr s1) (list_free_tr s2).
Proof.
  intros s1 s2 H. destruct H as (Ec & Ev & Hr). unfold list_free_tr. apply tr_rel_app.
  - apply recs_drop_rel. apply Forall2_rev_l, Hr.
  - rewrite Ec. destruct (Z.eqb_spec (sh_cap s2) 0) as [E0|E0]; [constructor|].
    constructor; [constructor; exact (Ev E0) | constructor].
Qed.

Lemma Forall2_nth_rec : forall l1 l2 i, Forall2 rec_rel l1 l2 -> (i < length l1)%nat ->
  rec_rel (nth i l1 (Known pdefT, [])) (nth i l2 (Known pdefT, [])).
Proof.
  intros l1 l2 i H. revert i. induction H as [|r1 r2 l1 l2 Hr _ IH]; intros i Hi; [simpl in Hi; lia|].
  destruct i; [exact Hr | simpl in Hi; apply IH; lia].
Qed.

Lemma list_drop_rel : forall s1 s2 i, sh_rel s1 s2 -> (i < length (sh_recs s1))%nat ->
  tr_rel sptr pdefT qs1 qs2 (list_drop_tr s1 i) (list_drop_tr s2 i).
Proof.
  intros s1 s2 i (_ & _ & Hr) Hi. unfold list_drop_tr. apply rec_drop_rel, Forall2_nth_rec; assumption.
Qed.

Lemma Forall2_firstn_skipn : forall (A B : Type) (Rr : A -> B -> Prop) l1 l2 i,
  Forall2 Rr l1 l2 -> Forall2 Rr (firstn i l1 ++ skipn (S i) l1) (firstn i l2 ++ skipn (S i) l2).
Proof.
  intros A B Rr l1 l2 i H. revert i. induction H as [|x y l1 l2 Hxy Ht IH]; intros i; [destruct i; constructor|].
  destruct i as [|i]; simpl; [exact Ht | constructor; [exact Hxy | apply IH]].
Qed.

Lemma list_drop_sh_rel : forall s1 s2 i, sh_rel s1 s2 -> sh_rel (list_drop_sh s1 i) (list_drop_sh s2 i).
Proof.
  intros s1 s2 i (Ec & Ev & Hr). unfold list_drop_sh. split; [exact Ec|]. split; [exact Ev|].
  simpl. apply Forall2_firstn_skipn, Hr.
Qed.

End Rel.

Lemma list_push_sh_rel : forall qs1 qs2 s1 s2 x j1 j2,
    sh_rel qs1 qs2 s1 s2 -> ret_agree sptr pdefT qs1 qs2 j1 j2 (if Z.eqb (sh_n s2) (sh_cap s2) then 2 else 1)%nat ->
    sh_rel qs1 qs2 (list_push_sh j1 s1 x) (list_push_sh j2 s2 x).
Proof.
  intros qs1 qs2 s1 s2 x j1 j2 H Hr. pose proof (sh_rel_n _ _ _ _ H) as En. destruct H as (Ec & Ev & Hrs).
  unfold list_push_sh. rewrite En, Ec.
  destruct (sh_n s2 =? sh_cap s2).
  - split; [reflexivity|]. split.
    + intros _. unfold ad_eq. simpl. specialize (Hr 0%nat ltac:(lia)). rewrite !Nat.add_0_r in Hr. exact Hr.
    + simpl. apply Forall2_app; [exact Hrs|]. constructor; [|constructor].
      split; [reflexivity|]. unfold ad_eq. simpl. specialize (Hr 1%nat ltac:(lia)).
      replace (S j1) with (j1 + 1)%nat by lia. replace (S j2) with (j2 + 1)%nat by lia. exact Hr.
  - split; [simpl; first [reflexivity | exact Ec]|]. split; [exact Ev|]. simpl. apply Forall2_app; [exact Hrs|]. constructor; [|constructor].
    split; [reflexivity|]. unfold ad_eq. simpl. specialize (Hr 0%nat ltac:(lia)). rewrite !Nat.add_0_r in Hr. exact Hr.
Qed.
