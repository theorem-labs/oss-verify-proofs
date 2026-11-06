(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim BnModel BnTree BgState ApBase ApState ApLogic ApErr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Section Inv.
Context {ptr : Type}.
Definition optb (o : option (ptr * Z)) : list (ptr * Z) := match o with Some b => [b] | None => [] end.
Definition fm (l : list (option (ptr * Z))) : list (ptr * Z) := flat_map optb l.

Lemma fm_cons x l : fm (x :: l) = optb x ++ fm l. Proof. reflexivity. Qed.

Lemma fm_lset : forall l i v, (i < length l)%nat ->
  Permutation (optb v ++ fm (lset l i None)) (fm (lset l i v)) /\
  Permutation (fm l) (optb (nth i l None) ++ fm (lset l i None)).
Proof.
  induction l as [|x l IH]; intros [|i] v Hi; cbn [length] in Hi; try lia; cbn [lset nth]; rewrite !fm_cons.
  - cbn [optb]. cbn [app]. split; apply Permutation_refl.
  - destruct (IH i v ltac:(lia)) as [H1 H2]. split.
    + eapply Permutation_trans. { rewrite app_assoc. apply Permutation_app_tail. apply Permutation_app_comm. }
      rewrite <- app_assoc. apply Permutation_app_head. exact H1.
    + eapply Permutation_trans. { apply Permutation_app_head. exact H2. }
      rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm.
Qed.
Local Notation ST := (ap_st ptr) (only parsing).

Definition cnf_blocks (c : option (ptr * ptr * ptr)) : list (ptr * Z) :=
  match c with Some (a, b, c) => [(a, 40); (b, 104); (c, 128)] | None => [] end.
Definition st_blocks (s : ST) : list (ptr * Z) := fm (as_file s) ++ fm (as_func s) ++ fm (as_data s) ++ cnf_blocks (as_cnf s).

Definition sizes_le (B : Z) (l : list (option (ptr * Z))) : Prop :=
  Forall (fun o => match o with Some (_, n) => 0 <= n <= B | None => True end) l.

Lemma sizes_le_lset B l i v : sizes_le B l -> match v with Some (_, n) => 0 <= n <= B | None => True end -> sizes_le B (lset l i v).
Proof.
  revert i. induction l as [|x l IH]; intros [|i] Hl Hv; cbn; inversion Hl; subst; constructor; auto. apply IH; assumption.
Qed.

Lemma fm_length B l : sizes_le B l -> (length (fm l) <= length l)%nat.
Proof.
  induction l as [|x l IH]; intros H; [cbn; lia|]. inversion H; subst. rewrite fm_cons, length_app. cbn [length].
  specialize (IH ltac:(assumption)). destruct x as [b|]; cbn; lia.
Qed.

Lemma fm_sum B l : 0 <= B -> sizes_le B l -> bsum (fm l) <= B * Z.of_nat (length l) /\ bnonneg (fm l).
Proof.
  intros HB. induction l as [|x l IH]; intros H.
  - cbn. unfold bsum, bnonneg; cbn. split; [lia|constructor].
  - inversion H; subst. destruct (IH ltac:(assumption)) as [S N]. rewrite fm_cons, bsum_app. cbn [length]. rewrite Nat2Z.inj_succ.
    destruct x as [[p n]|]; cbn [optb]; [rewrite bsum_cons, bsum_nil; cbn [snd]|rewrite bsum_nil]; split; try nia.
    + constructor; [cbn; lia|exact N].
    + exact N.
Qed.

Lemma nth_sizes_le B l i p n : sizes_le B l -> nth i l None = Some (p, n) -> 0 <= n <= B.
Proof.
  revert i. induction l as [|x l IH]; intros [|i] H E; cbn in E; try discriminate; inversion H; subst; [exact H2|eapply IH; eassumption].
Qed.

Definition ST_NB : Z := 51.
Definition ST_TOT : Z := 1744.

Definition sinv (s : ST) : Prop :=
  length (as_file s) = ERR_NUM /\ length (as_func s) = ERR_NUM /\ length (as_marks s) = ERR_NUM /\ length (as_buf s) = ERR_NUM
  /\ length (as_line s) = ERR_NUM /\ length (as_data s) = ERR_NUM /\ length (as_dflags s) = ERR_NUM
  /\ (as_top s < ERR_NUM)%nat /\ (as_bottom s < ERR_NUM)%nat
  /\ sizes_le 23 (as_file s) /\ sizes_le 23 (as_func s) /\ sizes_le 46 (as_data s)
  /\ (forall i, get_data i s <> None -> Z.land (get_dflags i s) ERR_TXT_MALLOCED <> 0)
  /\ (forall i, nth i (as_data s) None = None)        (* [comment removed for export] *)
  /\ as_cnf s = None.                                  (* [comment removed for export] *)

Lemma st_blocks_bound : forall s, sinv s -> zlength (st_blocks s) <= ST_NB /\ bsum (st_blocks s) <= ST_TOT /\ bnonneg (st_blocks s).
Proof.
  intros s (L1 & L2 & _ & _ & _ & L6 & _ & _ & _ & S1 & S2 & S3 & _).
  unfold st_blocks, zlength. rewrite !length_app, !bsum_app.
  pose proof (fm_length _ _ S1) as C1. pose proof (fm_length _ _ S2) as C2. pose proof (fm_length _ _ S3) as C3.
  destruct (fm_sum 23 _ ltac:(lia) S1) as [B1 N1]. destruct (fm_sum 23 _ ltac:(lia) S2) as [B2 N2]. destruct (fm_sum 46 _ ltac:(lia) S3) as [B3 N3].
  rewrite L1, L2, L6 in *. unfold ERR_NUM, ST_NB, ST_TOT in *. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in *.
  destruct (as_cnf s) as [[[a b] c]|]; cbn [cnf_blocks length].
  - rewrite !bsum_cons, bsum_nil. cbn [snd]. split; [lia|split; [lia|]]. repeat apply bnonneg_app; try assumption. repeat constructor; cbn; lia.
  - rewrite bsum_nil. split; [lia|split; [lia|]]. repeat apply bnonneg_app; try assumption. constructor.
Qed.

Definition rel (s : ST) (R X : list (ptr * Z)) : Prop := sinv s /\ Permutation X (st_blocks s ++ R).

(* [comment removed for export] *)
Lemma st_blocks_set_top v s : st_blocks (set_top v s) = st_blocks s. Proof. reflexivity. Qed.
Lemma st_blocks_set_bottom v s : st_blocks (set_bottom v s) = st_blocks s. Proof. reflexivity. Qed.
Lemma st_blocks_set_marks i v s : st_blocks (set_marks i v s) = st_blocks s. Proof. reflexivity. Qed.
Lemma st_blocks_set_buf i v s : st_blocks (set_buf i v s) = st_blocks s. Proof. reflexivity. Qed.
Lemma st_blocks_set_line i v s : st_blocks (set_line i v s) = st_blocks s. Proof. reflexivity. Qed.
Lemma st_blocks_set_dflags i v s : st_blocks (set_dflags i v s) = st_blocks s. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma fm_set_perm (F : list (option (ptr * Z))) (REST : list (ptr * Z)) i v : (i < length F)%nat ->
  Permutation (optb (nth i F None) ++ (fm (lset F i v) ++ REST)) (optb v ++ (fm F ++ REST)).
Proof.
  intros Hi. destruct (fm_lset F i v Hi) as [H1 H2].
  transitivity (optb (nth i F None) ++ ((optb v ++ fm (lset F i None)) ++ REST)).
  { apply Permutation_app_head. apply Permutation_app_tail. apply Permutation_sym. exact H1. }
  transitivity (optb v ++ ((optb (nth i F None) ++ fm (lset F i None)) ++ REST)).
  2:{ apply Permutation_app_head. apply Permutation_app_tail. apply Permutation_sym. exact H2. }
  rewrite <- !app_assoc. apply Permutation_app_swap_app.
Qed.

Lemma st_blocks_set_file i v s : (i < length (as_file s))%nat ->
  Permutation (optb (get_file i s) ++ st_blocks (set_file i v s)) (optb v ++ st_blocks s).
Proof. intros Hi. unfold st_blocks, get_file. cbn [as_file as_func as_data as_cnf set_file]. apply fm_set_perm. exact Hi. Qed.

Lemma st_blocks_set_func i v s : (i < length (as_func s))%nat ->
  Permutation (optb (get_func i s) ++ st_blocks (set_func i v s)) (optb v ++ st_blocks s).
Proof.
  intros Hi. unfold st_blocks, get_func. cbn [as_file as_func as_data as_cnf set_func].
  transitivity (fm (as_file s) ++ (optb (nth i (as_func s) None) ++ (fm (lset (as_func s) i v) ++ fm (as_data s) ++ cnf_blocks (as_cnf s)))).
  { rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_tail. rewrite <- !app_assoc. apply Permutation_app_swap_app. }
  transitivity (fm (as_file s) ++ (optb v ++ (fm (as_func s) ++ fm (as_data s) ++ cnf_blocks (as_cnf s)))).
  2:{ rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_tail. apply Permutation_app_tail. apply Permutation_app_comm. }
  apply Permutation_app_head. apply fm_set_perm. exact Hi.
Qed.
Lemma st_blocks_set_data i v s : (i < length (as_data s))%nat ->
  Permutation (optb (get_data i s) ++ st_blocks (set_data i v s)) (optb v ++ st_blocks s).
Proof.
  intros Hi. unfold st_blocks, get_data. cbn [as_file as_func as_data as_cnf set_data].
  set (A := fm (as_file s) ++ fm (as_func s)).
  transitivity (A ++ (optb (nth i (as_data s) None) ++ (fm (lset (as_data s) i v) ++ cnf_blocks (as_cnf s)))).
  { unfold A. rewrite !app_assoc. apply Permutation_app_tail. rewrite <- !app_assoc.
    transitivity (fm (as_file s) ++ (optb (nth i (as_data s) None) ++ (fm (as_func s) ++ fm (lset (as_data s) i v)))).
    - apply Permutation_app_swap_app.
    - apply Permutation_app_head. apply Permutation_app_swap_app. }
  transitivity (A ++ (optb v ++ (fm (as_data s) ++ cnf_blocks (as_cnf s)))).
  2:{ unfold A. rewrite !app_assoc. apply Permutation_app_tail. rewrite <- !app_assoc.
      transitivity (fm (as_file s) ++ (optb v ++ (fm (as_func s) ++ fm (as_data s)))).
      - apply Permutation_app_head. apply Permutation_sym. apply Permutation_app_swap_app.
      - apply Permutation_sym. apply Permutation_app_swap_app. }
  apply Permutation_app_head. apply fm_set_perm. exact Hi.
Qed.

Lemma st_blocks_set_cnf_some a b c s : as_cnf s = None ->
  Permutation (st_blocks (set_cnf (Some (a, b, c)) s)) ([(a, 40); (b, 104); (c, 128)] ++ st_blocks s).
Proof.
  intros E. unfold st_blocks. cbn [as_file as_func as_data as_cnf set_cnf]. rewrite E. cbn [cnf_blocks]. rewrite app_nil_r.
  apply Permutation_sym. rewrite !app_assoc. apply (Permutation_app_comm [(a, 40); (b, 104); (c, 128)]).
Qed.
Lemma st_blocks_set_cnf_same v s : as_cnf s = v -> st_blocks (set_cnf v s) = st_blocks s.
Proof. intros E. unfold st_blocks. cbn. rewrite E. reflexivity. Qed.

(* [comment removed for export] *)
Ltac sinv_destr H := destruct H as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & T1 & T2 & S1 & S2 & S3 & FL & DN & CN).
Ltac sinv_split := unfold sinv; cbn [as_file as_func as_marks as_buf as_line as_data as_dflags as_top as_bottom as_cnf
  set_top set_bottom set_file set_func set_marks set_buf set_line set_data set_dflags set_cnf]; rewrite ?lset_length.

Lemma sinv_set_top v s : (v < ERR_NUM)%nat -> sinv s -> sinv (set_top v s).
Proof. intros Hv H. sinv_destr H. sinv_split. repeat (split; [assumption|]). exact CN. Qed.
Lemma sinv_set_bottom v s : (v < ERR_NUM)%nat -> sinv s -> sinv (set_bottom v s).
Proof. intros Hv H. sinv_destr H. sinv_split. repeat (split; [assumption|]). exact CN. Qed.
Lemma sinv_set_marks i v s : sinv s -> sinv (set_marks i v s).
Proof. intros H. sinv_destr H. sinv_split. repeat (split; [assumption|]). exact CN. Qed.
Lemma sinv_set_buf i v s : sinv s -> sinv (set_buf i v s).
Proof. intros H. sinv_destr H. sinv_split. repeat (split; [assumption|]). exact CN. Qed.
Lemma sinv_set_line i v s : sinv s -> sinv (set_line i v s).
Proof. intros H. sinv_destr H. sinv_split. repeat (split; [assumption|]). exact CN. Qed.
Lemma sinv_set_cnf s : sinv s -> sinv (set_cnf None s).
Proof. intros H. sinv_destr H. sinv_split. repeat (split; [assumption|]). reflexivity. Qed.
Lemma sinv_set_file i v s : sinv s -> match v with Some (_, n) => 0 <= n <= 23 | None => True end -> sinv (set_file i v s).
Proof. intros H Hv. sinv_destr H. sinv_split. repeat (split; [assumption|]). split; [apply sizes_le_lset; assumption|]. repeat (split; [assumption|]). exact CN. Qed.
Lemma sinv_set_func i v s : sinv s -> match v with Some (_, n) => 0 <= n <= 23 | None => True end -> sinv (set_func i v s).
Proof. intros H Hv. sinv_destr H. sinv_split. repeat (split; [assumption|]). split; [apply sizes_le_lset; assumption|]. repeat (split; [assumption|]). exact CN. Qed.
(* [comment removed for export] *)
Lemma sinv_set_data_none i fl s : sinv s -> sinv (set_dflags i fl (set_data i None s)).
Proof.
  intros H. sinv_destr H. sinv_split. repeat (split; [assumption|]). split; [apply sizes_le_lset; [assumption|exact I]|].
  split; [| split; [| exact CN]].
  - intros j. unfold get_data, get_dflags in *. cbn [as_data as_dflags set_dflags set_data]. destruct (Nat.eq_dec i j) as [<-|NE].
    + destruct (Nat.lt_ge_cases i (length (as_data s))) as [Hi|Hi].
      * rewrite nth_lset_same by exact Hi. intros C. exfalso. apply C. reflexivity.
      * rewrite nth_overflow by (rewrite lset_length; exact Hi). intros C. exfalso. apply C. reflexivity.
    + rewrite !nth_lset_other by exact NE. apply FL.
  - intros j. destruct (Nat.eq_dec i j) as [<-|NE].
    + destruct (Nat.lt_ge_cases i (length (as_data s))) as [Hi|Hi].
      * rewrite nth_lset_same by exact Hi. reflexivity.
      * rewrite nth_overflow by (rewrite lset_length; exact Hi). reflexivity.
    + rewrite nth_lset_other by exact NE. apply DN.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sinv_set_dflags i fl s : sinv s -> (get_data i s <> None -> Z.land fl ERR_TXT_MALLOCED <> 0) -> sinv (set_dflags i fl s).
Proof.
  intros H Hfl. sinv_destr H. sinv_split. repeat (split; [assumption|]).
  split; [| split; [exact DN| exact CN]].
  intros j. unfold get_data, get_dflags in *. cbn [as_data as_dflags set_dflags]. destruct (Nat.eq_dec i j) as [<-|NE].
  - destruct (Nat.lt_ge_cases i (length (as_dflags s))) as [Hi|Hi].
    + rewrite nth_lset_same by exact Hi. exact Hfl.
    + rewrite (nth_overflow (lset _ _ _)) by (rewrite lset_length; exact Hi). rewrite (nth_overflow (as_data s)) by lia. intros C. exfalso. apply C. reflexivity.
  - rewrite !nth_lset_other by exact NE. apply FL.
Qed.

Variable ok : list (ptr * Z) -> Z -> Prop.           (* [comment removed for export] *)
Variables rcrit rcritS rcritI : Z -> Z -> Prop.
Variable spre : sysop -> Prop.
Local Notation awp := (awp ok rcrit rcritS rcritI spre) (only parsing).
Variable RF : list (ptr * Z) -> Prop.                 (* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis okR : forall s R X n, rel s R X -> RF R -> 0 <= n <= 23 -> ok X n.

Lemma rel_perm s R X Y : rel s R X -> Permutation X Y -> rel s R Y.
Proof. intros [H1 H2] HP. split; [exact H1|]. transitivity X; [apply Permutation_sym; exact HP|exact H2]. Qed.

Lemma ERR_NUM_16 : ERR_NUM = 16%nat. Proof. reflexivity. Qed.

Definition ecd_fun (i : nat) (deall : bool) (s : ST) : ST :=
  if negb (Z.land (get_dflags i s) ERR_TXT_MALLOCED =? 0) then
    (if deall then set_dflags i 0 (set_data i None s)
     else match get_data i s with Some _ => set_dflags i ERR_TXT_MALLOCED s | None => s end)
  else set_dflags i 0 (set_data i None s).

Lemma ecd_fun_facts i deall s : as_cnf (ecd_fun i deall s) = as_cnf s /\ as_file (ecd_fun i deall s) = as_file s /\ as_func (ecd_fun i deall s) = as_func s
  /\ as_top (ecd_fun i deall s) = as_top s /\ as_bottom (ecd_fun i deall s) = as_bottom s /\ as_marks (ecd_fun i deall s) = as_marks s /\ as_buf (ecd_fun i deall s) = as_buf s.
Proof. unfold ecd_fun. destruct (negb _); [destruct deall; [|destruct (get_data i s)]|]; cbn; repeat split; reflexivity. Qed.

Lemma err_clear_data_spec : forall i deall s R X, rel s R X -> (i < ERR_NUM)%nat ->
  awp (err_clear_data i deall s) X (fun r X' => rel (snd r) R X' /\ snd r = ecd_fun i deall s).
Proof.
  intros i deall s R X HR Hi. pose proof HR as [Hs HP]. unfold err_clear_data, ecd_fun. cbn.
  destruct (Z.land (get_dflags i s) ERR_TXT_MALLOCED =? 0) eqn:EF; cbn.
  - (* [comment removed for export] *)
    split; [|reflexivity]. split; [apply sinv_set_data_none; exact Hs|]. cbn [snd].
    assert (Ed : get_data i s = None).
    { destruct (get_data i s) eqn:Ed; [|reflexivity]. exfalso. pose proof Hs as Hs'. sinv_destr Hs'.
      apply (FL i); [rewrite Ed; discriminate| apply Z.eqb_eq; exact EF]. }
    rewrite st_blocks_set_dflags. pose proof (st_blocks_set_data i None s ltac:(sinv_destr Hs; rewrite L6; exact Hi)) as HPd.
    rewrite Ed in HPd. cbn [optb app] in HPd. transitivity (st_blocks s ++ R); [exact HP|]. apply Permutation_app_tail. apply Permutation_sym. exact HPd.
  - destruct deall.
    + destruct (get_data i s) as [[p n]|] eqn:Ed; cbn.
      * (* [comment removed for export] *)
        pose proof (st_blocks_set_data i None s ltac:(sinv_destr Hs; rewrite L6; exact Hi)) as HPd. rewrite Ed in HPd. cbn [optb app] in HPd.
        exists n, (st_blocks (set_data i None s) ++ R). split.
        { transitivity (st_blocks s ++ R); [exact HP|]. change ((p, n) :: st_blocks (set_data i None s) ++ R) with (((p, n) :: st_blocks (set_data i None s)) ++ R).
          apply Permutation_app_tail. apply Permutation_sym. exact HPd. }
        split; [|reflexivity]. split; [apply sinv_set_data_none; exact Hs|]. cbn [snd]. rewrite st_blocks_set_dflags. apply Permutation_refl.
      * split; [|reflexivity]. split; [apply sinv_set_data_none; exact Hs|]. cbn [snd]. rewrite st_blocks_set_dflags.
        pose proof (st_blocks_set_data i None s ltac:(sinv_destr Hs; rewrite L6; exact Hi)) as HPd. rewrite Ed in HPd. cbn [optb app] in HPd.
        transitivity (st_blocks s ++ R); [exact HP|]. apply Permutation_app_tail. apply Permutation_sym. exact HPd.
    + destruct (get_data i s) as [[p n]|] eqn:Ed; cbn.
      * split; [|reflexivity]. split; [|cbn [snd]; rewrite st_blocks_set_dflags; exact HP].
        apply sinv_set_dflags; [exact Hs|]. intros _. cbn. discriminate.
      * split; [exact HR|reflexivity].
Qed.

(* [comment removed for export] *)
Lemma sinv_len_file s : sinv s -> length (as_file s) = ERR_NUM. Proof. intros H; sinv_destr H; exact L1. Qed.
Lemma sinv_len_func s : sinv s -> length (as_func s) = ERR_NUM. Proof. intros H; sinv_destr H; exact L2. Qed.
Lemma sinv_len_data s : sinv s -> length (as_data s) = ERR_NUM. Proof. intros H; sinv_destr H; exact L6. Qed.
Lemma sinv_top s : sinv s -> (as_top s < ERR_NUM)%nat. Proof. intros H; sinv_destr H; exact T1. Qed.
Lemma sinv_bottom s : sinv s -> (as_bottom s < ERR_NUM)%nat. Proof. intros H; sinv_destr H; exact T2. Qed.

Lemma free_file_slot_spec : forall i s R X, rel s R X -> (i < ERR_NUM)%nat ->
  awp (free_file_slot i s) X (fun r X' => rel (snd r) R X' /\ snd r = set_file i None s).
Proof.
  intros i s R X [Hs HP] Hi. pose proof (st_blocks_set_file i None s ltac:(rewrite (sinv_len_file s Hs); exact Hi)) as HPf. cbn [optb app] in HPf.
  assert (Hs' : sinv (set_file i None s)) by (apply sinv_set_file; [exact Hs|exact I]).
  unfold free_file_slot. cbn. destruct (get_file i s) as [[p n]|] eqn:Ef; cbn.
  - exists n, (st_blocks (set_file i None s) ++ R). split.
    + transitivity (st_blocks s ++ R); [exact HP|]. change ((p, n) :: st_blocks (set_file i None s) ++ R) with (((p, n) :: st_blocks (set_file i None s)) ++ R).
      apply Permutation_app_tail. apply Permutation_sym. exact HPf.
    + split; [|reflexivity]. split; [exact Hs'|apply Permutation_refl].
  - split; [|reflexivity]. split; [exact Hs'|]. transitivity (st_blocks s ++ R); [exact HP|]. apply Permutation_app_tail. apply Permutation_sym. exact HPf.
Qed.

Lemma free_func_slot_spec : forall i s R X, rel s R X -> (i < ERR_NUM)%nat ->
  awp (free_func_slot i s) X (fun r X' => rel (snd r) R X' /\ snd r = set_func i None s).
Proof.
  intros i s R X [Hs HP] Hi. pose proof (st_blocks_set_func i None s ltac:(rewrite (sinv_len_func s Hs); exact Hi)) as HPf. cbn [optb app] in HPf.
  assert (Hs' : sinv (set_func i None s)) by (apply sinv_set_func; [exact Hs|exact I]).
  unfold free_func_slot. cbn. destruct (get_func i s) as [[p n]|] eqn:Ef; cbn.
  - exists n, (st_blocks (set_func i None s) ++ R). split.
    + transitivity (st_blocks s ++ R); [exact HP|]. change ((p, n) :: st_blocks (set_func i None s) ++ R) with (((p, n) :: st_blocks (set_func i None s)) ++ R).
      apply Permutation_app_tail. apply Permutation_sym. exact HPf.
    + split; [|reflexivity]. split; [exact Hs'|apply Permutation_refl].
  - split; [|reflexivity]. split; [exact Hs'|]. transitivity (st_blocks s ++ R); [exact HP|]. apply Permutation_app_tail. apply Permutation_sym. exact HPf.
Qed.

Definition slot_cleared (i : nat) (s s' : ST) : Prop :=
  as_cnf s' = as_cnf s /\ get_file i s' = None /\ get_func i s' = None /\
  (forall j, j <> i -> get_file j s' = get_file j s /\ get_func j s' = get_func j s) /\
  (as_top s' = as_top s /\ as_bottom s' = as_bottom s /\ as_buf s' = lset (as_buf s) i 0).

Lemma get_file_set_file_other i j v (s : ST) : i <> j -> get_file j (set_file i v s) = get_file j s.
Proof. intros. unfold get_file, set_file. cbn. apply nth_lset_other. assumption. Qed.
Lemma get_func_set_func_other i j v (s : ST) : i <> j -> get_func j (set_func i v s) = get_func j s.
Proof. intros. unfold get_func, set_func. cbn. apply nth_lset_other. assumption. Qed.
Lemma get_file_set_file_same i v (s : ST) : (i < length (as_file s))%nat -> get_file i (set_file i v s) = v.
Proof. intros. unfold get_file, set_file. cbn. apply nth_lset_same. assumption. Qed.
Lemma get_func_set_func_same i v (s : ST) : (i < length (as_func s))%nat -> get_func i (set_func i v s) = v.
Proof. intros. unfold get_func, set_func. cbn. apply nth_lset_same. assumption. Qed.

Lemma err_clear_spec : forall i deall s R X, rel s R X -> (i < ERR_NUM)%nat ->
  awp (err_clear i deall s) X (fun r X' => rel (snd r) R X' /\ slot_cleared i s (snd r)).
Proof.
  intros i deall s R X HR Hi. unfold err_clear.
  apply awp_abind. eapply awp_mono; [apply err_clear_data_spec; [exact HR|exact Hi]|]. intros [u s1] X1 [HR1 E1]. cbn [fst snd] in *.
  destruct (ecd_fun_facts i deall s) as (HC1 & HF1 & HN1 & HT1 & HB1 & HM1 & HU1). rewrite <- E1 in HC1, HF1, HN1, HT1, HB1, HM1, HU1.
  apply awp_abind. cbn [amodify apbind awp fst snd].
  set (s2 := set_line i (-1) (set_buf i 0 (set_marks i 0 s1))).
  assert (HR2 : rel s2 R X1). { destruct HR1 as [Hs1 HP1]. split; [|exact HP1]. unfold s2. apply sinv_set_line, sinv_set_buf, sinv_set_marks. exact Hs1. }
  apply awp_abind. eapply awp_mono; [apply free_file_slot_spec; [exact HR2|exact Hi]|]. intros [u3 s3] X3 [HR3 E3]. cbn [fst snd] in *. subst s3.
  eapply awp_mono; [apply free_func_slot_spec; [exact HR3|exact Hi]|]. intros [u4 s4] X4 [HR4 E4]. cbn [fst snd] in *. subst s4.
  split; [exact HR4|]. destruct HR1 as [Hs1 _].
  unfold slot_cleared. split; [unfold s2; cbn; exact HC1|]. split; [|split; [|split]].
  - unfold get_file, set_file, set_func. cbn. apply nth_lset_same. rewrite (sinv_len_file s1 Hs1). exact Hi.
  - unfold get_func, set_func. cbn. apply nth_lset_same. rewrite (sinv_len_func s1 Hs1). exact Hi.
  - intros j Hj. unfold get_file, get_func, set_file, set_func. cbn. rewrite !nth_lset_other by (intros E; apply Hj; symmetry; exact E). rewrite <- HF1, <- HN1. split; reflexivity.
  - unfold s2. cbn. rewrite HT1, HB1, HU1. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rel_add_file i b s R X : rel (set_file i None s) R X -> (i < ERR_NUM)%nat -> 0 <= snd b <= 23 ->
  rel (set_file i (Some b) (set_file i None s)) R (b :: X).
Proof.
  intros [Hs HP] Hi Hb. split; [apply sinv_set_file; [exact Hs|destruct b; cbn in *; lia]|].
  assert (Hlen : (i < length (as_file (set_file i None s)))%nat) by (rewrite (sinv_len_file _ Hs); exact Hi).
  assert (Hlen0 : (i < length (as_file s))%nat) by (pose proof Hlen as L; cbn in L; rewrite lset_length in L; exact L).
  pose proof (st_blocks_set_file i (Some b) (set_file i None s) Hlen) as HPf.
  rewrite (get_file_set_file_same _ _ _ Hlen0) in HPf. cbn [optb app] in HPf.
  transitivity (b :: st_blocks (set_file i None s) ++ R); [apply perm_skip; exact HP|].
  change (b :: st_blocks (set_file i None s) ++ R) with (([b] ++ st_blocks (set_file i None s)) ++ R).
  apply Permutation_app_tail. apply Permutation_sym. exact HPf.
Qed.
Lemma rel_add_func i b s R X : rel (set_func i None s) R X -> (i < ERR_NUM)%nat -> 0 <= snd b <= 23 ->
  rel (set_func i (Some b) (set_func i None s)) R (b :: X).
Proof.
  intros [Hs HP] Hi Hb. split; [apply sinv_set_func; [exact Hs|destruct b; cbn in *; lia]|].
  assert (Hlen : (i < length (as_func (set_func i None s)))%nat) by (rewrite (sinv_len_func _ Hs); exact Hi).
  assert (Hlen0 : (i < length (as_func s))%nat) by (pose proof Hlen as L; cbn in L; rewrite lset_length in L; exact L).
  pose proof (st_blocks_set_func i (Some b) (set_func i None s) Hlen) as HPf.
  rewrite (get_func_set_func_same _ _ _ Hlen0) in HPf. cbn [optb app] in HPf.
  transitivity (b :: st_blocks (set_func i None s) ++ R); [apply perm_skip; exact HP|].
  change (b :: st_blocks (set_func i None s) ++ R) with (([b] ++ st_blocks (set_func i None s)) ++ R).
  apply Permutation_app_tail. apply Permutation_sym. exact HPf.
Qed.
Lemma set_file_set_file i a b (s : ST) : set_file i a (set_file i b s) = set_file i a s.
Proof. unfold set_file. cbn. f_equal. revert i. induction (as_file s) as [|x l IH]; intros [|i]; cbn; try reflexivity. rewrite IH. reflexivity. Qed.
Lemma set_func_set_func i a b (s : ST) : set_func i a (set_func i b s) = set_func i a s.
Proof. unfold set_func. cbn. f_equal. revert i. induction (as_func s) as [|x l IH]; intros [|i]; cbn; try reflexivity. rewrite IH. reflexivity. Qed.
Lemma rel_set_line i v s R X : rel s R X -> rel (set_line i v s) R X.
Proof. intros [Hs HP]. split; [apply sinv_set_line; exact Hs|rewrite st_blocks_set_line; exact HP]. Qed.
Lemma rel_set_buf i v s R X : rel s R X -> rel (set_buf i v s) R X.
Proof. intros [Hs HP]. split; [apply sinv_set_buf; exact Hs|rewrite st_blocks_set_buf; exact HP]. Qed.
Lemma rel_set_marks i v s R X : rel s R X -> rel (set_marks i v s) R X.
Proof. intros [Hs HP]. split; [apply sinv_set_marks; exact Hs|rewrite st_blocks_set_marks; exact HP]. Qed.
Lemma rel_set_top v s R X : rel s R X -> (v < ERR_NUM)%nat -> rel (set_top v s) R X.
Proof. intros [Hs HP] Hv. split; [apply sinv_set_top; assumption|rewrite st_blocks_set_top; exact HP]. Qed.
Lemma rel_set_bottom v s R X : rel s R X -> (v < ERR_NUM)%nat -> rel (set_bottom v s) R X.
Proof. intros [Hs HP] Hv. split; [apply sinv_set_bottom; assumption|rewrite st_blocks_set_bottom; exact HP]. Qed.

Lemma ring_next_lt i : (ring_next i < ERR_NUM)%nat.
Proof. unfold ring_next, ERR_NUM. apply Nat.mod_upper_bound. lia. Qed.
Lemma ring_prev_lt i : (i < ERR_NUM)%nat -> (ring_prev i < ERR_NUM)%nat.
Proof. unfold ring_prev, ERR_NUM. destruct i; lia. Qed.

Lemma ring_next_neq i : (i < ERR_NUM)%nat -> ring_next i <> i.
Proof. unfold ring_next, ERR_NUM. intros Hi E. do 16 (destruct i as [|i]; [cbn in E; lia|]). lia. Qed.

Lemma err_new_spec : forall s R X, rel s R X ->
  awp (err_new s) X (fun r X' => rel (snd r) R X' /\ as_cnf (snd r) = as_cnf s /\
     (as_top (snd r) = ring_next (as_top s) /\ as_top (snd r) <> as_bottom (snd r) /\ as_buf (snd r) = lset (as_buf s) (ring_next (as_top s)) 0)).
Proof.
  intros s R X HR. unfold err_new. cbn -[err_clear ring_next].
  set (s1 := set_bottom _ (set_top _ s)).
  assert (HR1 : rel s1 R X).
  { destruct HR as [Hs HP]. split; [|exact HP]. unfold s1. apply sinv_set_bottom; [|apply sinv_set_top; [apply ring_next_lt|exact Hs]].
    destruct (Nat.eqb _ _); [apply ring_next_lt|apply sinv_bottom; exact Hs]. }
  eapply awp_mono; [apply err_clear_spec; [exact HR1|apply ring_next_lt]|]. intros [u s2] X2 [HR2 (HC & _ & _ & _ & HT & HB & HU)]. cbn [fst snd] in *.
  split; [exact HR2|]. split; [rewrite HC; reflexivity|]. rewrite HT, HB, HU. unfold s1. cbn -[ring_next Nat.eqb]. split; [reflexivity|]. split; [|reflexivity].
  destruct (Nat.eqb_spec (ring_next (as_top s)) (as_bottom s)) as [E|NE]; [|exact NE].
  intros C. apply (ring_next_neq (ring_next (as_top s))); [apply ring_next_lt|]. rewrite E at 1. symmetry. exact C.
Qed.

Lemma err_set_debug_spec : forall rs s R X, rel s R X -> RF R -> 0 <= rs_flen rs <= 23 -> 0 <= rs_fnlen rs <= 23 ->
  awp (err_set_debug rs s) X (fun r X' => rel (snd r) R X' /\ as_cnf (snd r) = as_cnf s /\
     (as_top (snd r) = as_top s /\ as_bottom (snd r) = as_bottom s /\ as_buf (snd r) = as_buf s)).
Proof.
  intros rs s R X HR HF Hfl Hfn. pose proof (sinv_top s (proj1 HR)) as Ht. unfold err_set_debug. cbn -[free_file_slot free_func_slot amalloc].
  apply awp_abind. eapply awp_mono; [apply free_file_slot_spec; [exact HR|exact Ht]|]. intros [u1 s1] X1 [HR1 E1]. cbn [fst snd] in *. subst s1.
  apply awp_abind. apply awp_amalloc; [lia|eapply okR; [exact HR1|exact HF|lia]|]. intros pf Hpf. cbn -[free_func_slot amalloc].
  set (s2 := set_line _ _ _).
  assert (HR2 : rel s2 R ((pf, rs_flen rs) :: X1)) by (unfold s2; apply rel_set_line; apply rel_add_file; [exact HR1|exact Ht|cbn; lia]).
  apply awp_abind. eapply awp_mono; [apply free_func_slot_spec; [exact HR2|unfold s2; cbn; exact Ht]|]. intros [u3 s3] X3 [HR3 E3]. cbn [fst snd] in *. subst s3.
  apply awp_abind. apply awp_amalloc; [lia|eapply okR; [exact HR3|exact HF|lia]|]. intros pn Hpn. cbn.
  split; [|repeat split; reflexivity]. apply (rel_add_func (as_top s) (pn, rs_fnlen rs)); [exact HR3|exact Ht|cbn; lia].
Qed.

Lemma err_set_error_spec : forall rs s R X, rel s R X ->
  awp (err_set_error rs s) X (fun r X' => rel (snd r) R X' /\ as_cnf (snd r) = as_cnf s /\
     (as_top (snd r) = as_top s /\ as_bottom (snd r) = as_bottom s /\ as_buf (snd r) = lset (as_buf s) (as_top s) (rs_code rs))).
Proof.
  intros rs s R X HR. pose proof (sinv_top s (proj1 HR)) as Ht. unfold err_set_error. cbn -[err_clear_data].
  apply awp_abind. eapply awp_mono; [apply err_clear_data_spec; [exact HR|exact Ht]|]. intros [u1 s1] X1 [HR1 E1]. cbn [fst snd] in *.
  cbn. split; [apply rel_set_buf; exact HR1|]. cbn. subst s1. destruct (ecd_fun_facts (as_top s) false s) as (HC & _ & _ & HT & HB & _ & HU).
  rewrite HT, HB, HU. repeat split; try reflexivity. exact HC.
Qed.

Lemma get_buf_lset_same i v (s : ST) l : sinv s -> as_buf s = lset l i v -> length l = ERR_NUM -> (i < ERR_NUM)%nat -> get_buf i s = v.
Proof. intros Hs E Hl Hi. unfold get_buf. rewrite E. apply nth_lset_same. rewrite Hl. exact Hi. Qed.
Lemma sinv_len_buf s : sinv s -> length (as_buf s) = ERR_NUM. Proof. intros H; sinv_destr H; exact L4. Qed.

Lemma err_raise_spec : forall rs s R X, rel s R X -> RF R -> 0 <= rs_flen rs <= 23 -> 0 <= rs_fnlen rs <= 23 ->
  awp (err_raise rs s) X (fun r X' => rel (snd r) R X' /\ as_cnf (snd r) = as_cnf s /\
     (as_top (snd r) <> as_bottom (snd r) /\ get_buf (as_top (snd r)) (snd r) = rs_code rs)).
Proof.
  intros rs s R X HR HF Hfl Hfn. unfold err_raise.
  apply awp_abind. eapply awp_mono; [apply err_new_spec; exact HR|]. intros [u1 s1] X1 (HR1 & C1 & T1 & NE1 & B1). cbn [fst snd] in *.
  apply awp_abind. eapply awp_mono; [apply err_set_debug_spec; [exact HR1|exact HF|exact Hfl|exact Hfn]|]. intros [u2 s2] X2 (HR2 & C2 & T2 & B2 & U2). cbn [fst snd] in *.
  eapply awp_mono; [apply err_set_error_spec; exact HR2|]. intros [u3 s3] X3 (HR3 & C3 & T3 & B3 & U3). cbn [fst snd] in *.
  split; [exact HR3|]. split; [congruence|]. split; [rewrite T3, B3, T2, B2; exact NE1|].
  apply (get_buf_lset_same _ _ _ (as_buf s2)); [exact (proj1 HR3)|rewrite T3; exact U3|apply sinv_len_buf; exact (proj1 HR2)|apply sinv_top; exact (proj1 HR3)].
Qed.
Lemma get_dflags_set_dflags_same i v (s : ST) : (i < length (as_dflags s))%nat -> get_dflags i (set_dflags i v s) = v.
Proof. intros. unfold get_dflags, set_dflags. cbn. apply nth_lset_same. assumption. Qed.
Lemma get_data_set_data_same i v (s : ST) : (i < length (as_data s))%nat -> get_data i (set_data i v s) = v.
Proof. intros. unfold get_data, set_data. cbn. apply nth_lset_same. assumption. Qed.
Lemma sinv_len_dflags s : sinv s -> length (as_dflags s) = ERR_NUM. Proof. intros H; sinv_destr H; exact L7. Qed.


Lemma err_clear_slots_spec : forall n i s R X, rel s R X -> (i + n <= ERR_NUM)%nat ->
  awp (err_clear_slots i n s) X (fun r X' => rel (snd r) R X' /\ as_cnf (snd r) = as_cnf s /\
     (forall j, (i <= j < i + n)%nat -> get_file j (snd r) = None /\ get_func j (snd r) = None) /\
     (forall j, (j < i)%nat \/ (i + n <= j)%nat -> get_file j (snd r) = get_file j s /\ get_func j (snd r) = get_func j s)).
Proof.
  induction n as [|n IH]; intros i s R X HR Hn.
  - cbn. split; [exact HR|]. split; [reflexivity|]. split; [intros j Hj; lia|]. intros j _. split; reflexivity.
  - cbn -[err_clear err_clear_slots]. apply awp_abind. eapply awp_mono; [apply err_clear_spec; [exact HR|lia]|].
    intros [u1 s1] X1 [HR1 (HC1 & HF1 & HN1 & HO1)]. cbn [fst snd] in *.
    eapply awp_mono; [apply IH; [exact HR1|lia]|]. intros [u2 s2] X2 (HR2 & HC2 & HA2 & HB2). cbn [fst snd] in *.
    split; [exact HR2|]. split; [congruence|]. split.
    + intros j Hj. destruct (Nat.eq_dec j i) as [->|NE].
      * destruct (HB2 i ltac:(lia)) as [-> ->]. split; assumption.
      * apply HA2. lia.
    + intros j Hj. destruct (HB2 j ltac:(lia)) as [-> ->]. apply HO1. lia.
Qed.

Lemma err_clear_error_spec : forall s R X, rel s R X ->
  awp (err_clear_error s) X (fun r X' => rel (snd r) R X' /\ as_cnf (snd r) = as_cnf s /\
     (forall j, (j < ERR_NUM)%nat -> get_file j (snd r) = None /\ get_func j (snd r) = None)).
Proof.
  intros s R X HR. unfold err_clear_error. apply awp_abind. eapply awp_mono; [apply (err_clear_slots_spec ERR_NUM 0); [exact HR|lia]|].
  intros [u1 s1] X1 (HR1 & HC1 & HA1 & _). cbn -[ERR_NUM]. split; [|split; [exact HC1|intros j Hj; apply HA1; lia]].
  apply rel_set_bottom; [|unfold ERR_NUM; lia]. apply rel_set_top; [exact HR1|unfold ERR_NUM; lia].
Qed.

End Inv.
