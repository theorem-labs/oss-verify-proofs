(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith List Bool Lia Permutation.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees HuffTree HuffHeap.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import TreeModel BuildTreeModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.


Fixpoint ziota (a : Z) (n : nat) : list Z := match n with O => [] | S n' => a :: ziota (a + 1) n' end.

Lemma in_ziota : forall a n x, In x (ziota a n) <-> a <= x < a + Z.of_nat n.
Proof.
  intros a n. revert a. induction n as [|n IH]; intros a x; cbn [ziota]; [cbn; lia|].
  rewrite Nat2Z.inj_succ. cbn [In]. rewrite IH. lia.
Qed.

Lemma ziota_S_r : forall n a, ziota a (S n) = ziota a n ++ [a + Z.of_nat n].
Proof.
  induction n as [|n IH]; intros a; [cbn; f_equal; lia|].
  change (a :: ziota (a + 1) (S n) = a :: (ziota (a + 1) n ++ [a + Z.of_nat (S n)])).
  rewrite IH. rewrite Nat2Z.inj_succ. do 3 f_equal. lia.
Qed.

Lemma NoDup_ziota : forall a n, NoDup (ziota a n).
Proof.
  intros a n. revert a. induction n as [|n IH]; intros a; cbn; constructor; [|apply IH].
  rewrite in_ziota. lia.
Qed.

Lemma ziota_length : forall a n, length (ziota a n) = n.
Proof. intros a n. revert a. induction n; intros; cbn; [reflexivity| now rewrite IHn]. Qed.


Definition zlen {A} (l : list A) : Z := Z.of_nat (length l).


Section Leaves.
Variables (FC0 : arr).

Definition nzb (j : Z) : bool := negb (arr_get FC0 j =? 0).
Definition Ul (n : Z) : list Z := filter nzb (ziota 0 (Z.to_nat n)).

Lemma Ul_in : forall n j, 0 <= n -> In j (Ul n) <-> 0 <= j < n /\ arr_get FC0 j <> 0.
Proof.
  intros n j Hn. unfold Ul. rewrite filter_In, in_ziota. unfold nzb. rewrite Bool.negb_true_iff, Z.eqb_neq. lia.
Qed.

Lemma Ul_step : forall n, 0 <= n -> Ul (n + 1) = Ul n ++ (if nzb n then [n] else []).
Proof.
  intros n Hn. unfold Ul. replace (Z.to_nat (n + 1)) with (S (Z.to_nat n)) by lia.
  rewrite ziota_S_r, filter_app. cbn. replace (0 + Z.of_nat (Z.to_nat n)) with n by lia. destruct (nzb n); reflexivity.
Qed.

Lemma Ul_NoDup : forall n, NoDup (Ul n).
Proof. intros. unfold Ul. apply NoDup_filter. apply NoDup_ziota. Qed.

Lemma Ul_last_max : forall n j, 0 <= n -> In j (Ul n) -> j <= last (Ul n) (-1).
Proof.
  intros n j Hn. rewrite <- (Z2Nat.id n) by lia. generalize (Z.to_nat n) as m. clear n Hn.
  induction m as [|m IH]; intros Hin; [destruct Hin|].
  rewrite Nat2Z.inj_succ, <- Z.add_1_r in *. rewrite Ul_step in * by lia.
  destruct (nzb (Z.of_nat m)).
  - rewrite last_last. apply in_app_iff in Hin. destruct Hin as [Hin|[<-|[]]]; [|lia].
    apply Ul_in in Hin; lia.
  - rewrite app_nil_r in *. apply IH, Hin.
Qed.

Variable (t : tree_id).

Definition Ulist : list Z := Ul (sd_elems t).
Definition pads : list Z :=
  match Ulist with
  | [] => [0; 1]
  | [j] => [if j <? 2 then j + 1 else 0]
  | _ => []
  end.
Definition UP : list Z := Ulist ++ pads.
Definition FP (j : Z) : Z := if existsb (Z.eqb j) pads then 1 else arr_get FC0 j.
Definition MCP : Z := fold_right Z.max (-1) UP.

End Leaves.

Lemma elems_tsize : forall t, tsize t = 2 * sd_elems t + 1 /\ 19 <= sd_elems t <= 286.
Proof. intros [| |]; cbn; unfold L_CODES, D_CODES, BL_CODES; lia. Qed.

Lemma zlen_app : forall {A} (l m : list A), zlen (l ++ m) = zlen l + zlen m.
Proof. intros. unfold zlen. rewrite length_app. lia. Qed.
Lemma zlen_cons : forall {A} (x : A) l, zlen (x :: l) = zlen l + 1.
Proof. intros. unfold zlen. cbn [length]. lia. Qed.
Lemma zlen_nil : forall {A}, zlen (@nil A) = 0.
Proof. reflexivity. Qed.
Lemma zlen_nonneg : forall {A} (l : list A), 0 <= zlen l.
Proof. intros. unfold zlen. lia. Qed.
Lemma zlen_filter_ziota : forall f a n, zlen (filter f (ziota a n)) <= Z.of_nat n.
Proof.
  intros f a n. revert a. induction n as [|n IH]; intros a; cbn [ziota filter]; [apply Z.le_refl|].
  specialize (IH (a + 1)). destruct (f a); rewrite ?zlen_cons; lia.
Qed.

Lemma inb_true : forall (a : arr) i, 0 <= i < arr_len a -> arr_inb a i = true.
Proof. intros. apply arr_inb_spec. assumption. Qed.

Lemma fold_max_spec : forall l0 : list Z, (forall j, In j l0 -> 0 <= j) -> l0 <> [] ->
  In (fold_right Z.max (-1) l0) l0 /\ forall j, In j l0 -> j <= fold_right Z.max (-1) l0.
Proof.
  induction l0 as [|x l0 IH]; intros Hnn Hne; [congruence|]. cbn.
  destruct l0 as [|y l1].
  - cbn. pose proof (Hnn x (or_introl eq_refl)). rewrite Z.max_l by lia. split; [now left| intros j [<-|[]]; lia].
  - destruct (IH ltac:(intros; apply Hnn; now right) ltac:(discriminate)) as [A B].
    cbn [fold_right] in *. destruct (Z.max_spec x (Z.max y (fold_right Z.max (-1) l1))) as [[C ->]|[C ->]].
    + split; [right; exact A|]. intros j [<-|Hj]; [lia|]. apply B, Hj.
    + split; [now left|]. intros j [<-|Hj]; [lia|]. pose proof (B j Hj). lia.
Qed.


Section Build.
Variables (s : deflate_state) (t : tree_id) (FC0 : arr).
Variables (HM : Z) (BC : arr) (OL SL MC : Z).
Hypothesis LFC : arr_len FC0 = tsize t.

Local Set Warnings "-notation-for-abbreviation".
Local Notation elems := (sd_elems t).
Local Notation Uln := (Ul FC0).
Local Notation UL := (Ulist FC0 t).

Lemma Ul_len : forall n, 0 <= n -> zlen (Uln n) <= n.
Proof. intros n Hn. unfold Ul. pose proof (zlen_filter_ziota (nzb FC0) 0 (Z.to_nat n)). lia. Qed.

Lemma loop1_flat : forall fuel n DL HP HL DP mc,
  0 <= n <= elems -> (Z.to_nat (elems - n) <= fuel)%nat ->
  arr_len HP = 573 -> arr_len DP = 573 -> arr_len DL = tsize t ->
  HL = zlen (Uln n) -> (forall i, 1 <= i <= HL -> arr_get HP i = nth (Z.to_nat (i - 1)) (Uln n) 0) ->
  (forall j, 0 <= j < n -> arr_get FC0 j = 0 -> arr_get DL j = 0) ->
  mc = last (Uln n) (-1) ->
  exists DL' HP' DP',
    build_tree_loop1 fuel (bt_upd s t FC0 DL HP HL HM DP BC OL SL MC) t elems n mc
      = (bt_upd s t FC0 DL' HP' (zlen UL) HM DP' BC OL SL MC, last UL (-1))
    /\ arr_len HP' = 573 /\ arr_len DP' = 573 /\ arr_len DL' = tsize t
    /\ (forall i, 1 <= i <= zlen UL -> arr_get HP' i = nth (Z.to_nat (i - 1)) UL 0)
    /\ (forall j, 0 <= j < elems -> arr_get FC0 j = 0 -> arr_get DL' j = 0).
Proof.
  induction fuel as [|fuel IH]; intros n DL HP HL DP mc Hn Hf LHP LDP LDL HHL HHP HDL Hmc.
  - assert (n = elems) by lia. subst n. exists DL, HP, DP. cbn [build_tree_loop1].
    subst HL mc. unfold Ulist. repeat split; auto.
  - pose proof (elems_tsize t) as ET. cbn [build_tree_loop1]. autorewrite with btupd.
    destruct (Z.ltb_spec n elems).
    2:{ assert (n = elems) by lia. subst n. exists DL, HP, DP. subst HL mc. unfold Ulist. repeat split; auto. }
    pose proof (Ul_len n ltac:(lia)) as HLn.
    destruct (Z.eqb_spec (arr_get FC0 n) 0) as [Z0|NZ]; cbn [negb].
    +
      destruct (IH (n + 1) (arr_set DL n (wrap16 0)) HP HL DP mc) as (DL' & HP' & DP' & E & R);
        [lia| lia| exact LHP| exact LDP| rewrite arr_len_set; exact LDL| | | | |].
      * rewrite Ul_step by lia. unfold nzb. rewrite Z0. cbn. rewrite app_nil_r. exact HHL.
      * rewrite Ul_step by lia. unfold nzb. rewrite Z0. cbn. rewrite app_nil_r. exact HHP.
      * intros j Hj Hj0. rewrite arr_get_set. destruct (Z.eqb_spec n j); [cbn [andb]|apply HDL; lia].
        rewrite inb_true by lia. reflexivity.
      * rewrite Ul_step by lia. unfold nzb. rewrite Z0. cbn. rewrite app_nil_r. exact Hmc.
      * exists DL', HP', DP'. split; [exact E| exact R].
    +
      assert (EU : Uln (n + 1) = Uln n ++ [n]).
      { rewrite Ul_step by lia. unfold nzb. replace (arr_get FC0 n =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ). reflexivity. }
      destruct (IH (n + 1) DL (arr_set HP (HL + 1) n) (HL + 1) (arr_set DP n (wrap8 0)) n) as (DL' & HP' & DP' & E & R);
        [lia| lia| rewrite arr_len_set; exact LHP| rewrite arr_len_set; exact LDP| exact LDL| | | | |].
      * rewrite EU, zlen_app, zlen_cons, zlen_nil. lia.
      * intros i Hi. rewrite EU. rewrite arr_get_set, inb_true by lia.
        destruct (Z.eqb_spec (HL + 1) i); cbn [andb].
        -- rewrite app_nth2 by (unfold zlen in HHL; lia). replace (Z.to_nat (i - 1) - length (Uln n))%nat with 0%nat by (unfold zlen in HHL; lia). reflexivity.
        -- rewrite app_nth1 by (unfold zlen in HHL; lia). apply HHP. lia.
      * intros j Hj Hj0. destruct (Z.eq_dec j n); [subst; congruence|]. apply HDL; lia.
      * rewrite EU, last_last. reflexivity.
      * exists DL', HP', DP'. split; [exact E| exact R].
Qed.

Local Notation PADS := (pads FC0 t).
Local Notation UPl := (UP FC0 t).
Local Notation FPf := (FP FC0 t).

Definition sl_pad : Z := zsum (map (stree_Len t) PADS).

Lemma pads_facts :
  NoDup UPl /\ (forall j, In j UPl -> 0 <= j < elems) /\ 2 <= zlen UPl
  /\ (forall j, In j PADS -> arr_get FC0 j = 0 /\ 0 <= j <= 2)
  /\ (forall j, In j UPl -> j <= MCP FC0 t) /\ In (MCP FC0 t) UPl.
Proof.
  pose proof (elems_tsize t) as ET.
  pose proof (Ul_NoDup FC0 elems) as ND. pose proof (fun j => Ul_in FC0 elems j ltac:(lia)) as IN.
  pose proof (fun j => Ul_last_max FC0 elems j ltac:(lia)) as LM.
  unfold MCP in *. unfold UP in *. unfold pads in *. unfold Ulist in *.
  destruct (Ul FC0 elems) as [|j1 [|j2 l]] eqn:EU.
  - cbn. split; [repeat constructor; cbn; lia|]. split; [intros j [<-|[<-|[]]]; lia|]. split; [unfold zlen; cbn [length app]; lia|].
    split. { intros j Hj. assert (Hj' : j = 0 \/ j = 1) by (destruct Hj as [<-|[<-|[]]]; lia). clear Hj. split; [|lia].
             destruct (Z.eq_dec (arr_get FC0 j) 0); [assumption|]. exfalso.
             pose proof (proj2 (IN j) ltac:(lia)) as HH. destruct HH. }
    split; [intros j [<-|[<-|[]]]; cbn; lia| cbn; auto].
  - pose proof (proj1 (IN j1) ltac:(now left)) as [R1 N1]. cbn -[Z.add Z.ltb Z.max].
    destruct (Z.ltb_spec j1 2).
    + split. { constructor; [|repeat constructor; cbn; auto]. cbn. lia. }
      split. { intros j [<-|[<-|[]]]; lia. }
      split; [unfold zlen; cbn [length app]; lia|]. split.
      { intros j [<-|[]]. split; [|lia]. destruct (Z.eq_dec (arr_get FC0 (j1 + 1)) 0); [assumption|]. exfalso.
        pose proof (proj2 (IN (j1 + 1)) ltac:(lia)). destruct H0 as [H0|[]]. lia. }
      split; [intros j [<-|[<-|[]]]; lia| right; left; lia].
    + split. { constructor; [|repeat constructor; cbn; auto]. cbn. lia. }
      split. { intros j [<-|[<-|[]]]; lia. }
      split; [unfold zlen; cbn [length app]; lia|]. split.
      { intros j [<-|[]]. split; [|lia]. destruct (Z.eq_dec (arr_get FC0 0) 0); [assumption|]. exfalso.
        pose proof (proj2 (IN 0) ltac:(lia)). destruct H0 as [H0|[]]. lia. }
      split; [intros j [<-|[<-|[]]]; lia| left; lia].
  - rewrite app_nil_r. split; [exact ND|]. split; [intros j Hj; apply IN in Hj; lia|].
    split; [rewrite !zlen_cons; pose proof (zlen_nonneg l); lia|]. split; [intros j []|].
    destruct (fold_max_spec (j1 :: j2 :: l) ltac:(intros j Hj; apply IN in Hj; lia) ltac:(discriminate)) as [A B].
    split; [exact B| exact A].
Qed.

Lemma last_UL_MCP : forall j1 j2 l, UL = j1 :: j2 :: l -> last UL (-1) = MCP FC0 t.
Proof.
  intros j1 j2 l EU. pose proof (elems_tsize t) as ET.
  pose proof (fun j => Ul_in FC0 elems j ltac:(lia)) as IN.
  pose proof (fun j => Ul_last_max FC0 elems j ltac:(lia)) as LM.
  unfold MCP, UP, pads. fold UL. unfold Ulist in *. rewrite EU in *. rewrite app_nil_r.
  destruct (fold_max_spec (j1 :: j2 :: l) ltac:(intros j Hj; apply IN in Hj; lia) ltac:(discriminate)) as [A B].
  assert (Hl : forall (l0 : list Z) x, In (last (x :: l0) (-1)) (x :: l0)).
  { clear. induction l0 as [|y l0 IH]; intros x; [now left|]. right. apply IH. }
  specialize (Hl (j2 :: l) j1).
  pose proof (LM _ A). pose proof (B _ Hl). lia.
Qed.

Lemma bt_if_sl : forall (b : bool) FC DL HP HL0 HM0 DP BC0 OL0 SL1 SL2 MC0,
  (if b then bt_upd s t FC DL HP HL0 HM0 DP BC0 OL0 SL1 MC0 else bt_upd s t FC DL HP HL0 HM0 DP BC0 OL0 SL2 MC0)
  = bt_upd s t FC DL HP HL0 HM0 DP BC0 OL0 (if b then SL1 else SL2) MC0.
Proof. intros. destruct b; reflexivity. Qed.

Lemma loop2_flat : forall DL1 HP1 DP1, 0 <= OL < 2 ^ 64 -> 0 <= SL < 2 ^ 64 ->
  arr_len HP1 = 573 -> arr_len DP1 = 573 ->
  (forall i, 1 <= i <= zlen UL -> arr_get HP1 i = nth (Z.to_nat (i - 1)) UL 0) ->
  exists FC2 HP2 DP2,
    build_tree_loop2 2 (bt_upd s t FC0 DL1 HP1 (zlen UL) HM DP1 BC OL SL MC) t (last UL (-1))
      = (bt_upd s t FC2 DL1 HP2 (zlen UPl) HM DP2 BC (wrap64 (OL - zlen PADS))
                (if stree_has t then wrap64 (SL - sl_pad) else SL) MC, MCP FC0 t)
    /\ arr_len FC2 = tsize t /\ arr_len HP2 = 573 /\ arr_len DP2 = 573
    /\ (forall j, arr_get FC2 j = FPf j)
    /\ (forall i, 1 <= i <= zlen UPl -> arr_get HP2 i = nth (Z.to_nat (i - 1)) UPl 0).
Proof.
  intros DL1 HP1 DP1 OLr SLr LHP LDP HHP. pose proof (elems_tsize t) as ET.
  unfold sl_pad, FP, MCP, UP, pads. fold UL.
  destruct UL as [|j1 [|j2 l]] eqn:EU.
  -
    change (zlen (@nil Z)) with 0. change (zlen ([] ++ [0; 1])) with 2. change (zlen [0; 1]) with 2. cbn [last app map zsum fold_right].
    cbn [build_tree_loop2]. autorewrite with btupd.
    replace (0 <? 2) with true by reflexivity. replace (-1 <? 2) with true by reflexivity.
    replace (-1 + 1) with 0 by reflexivity. replace (0 + 1) with 1 by reflexivity. cbv beta iota zeta. autorewrite with btupd.
    rewrite !bt_if_sl. autorewrite with btupd.
    replace (1 <? 2) with true by reflexivity. replace (0 <? 2) with true by reflexivity. replace (1 + 1) with 2 by reflexivity.
    cbv beta iota zeta. autorewrite with btupd. rewrite !bt_if_sl.
    eexists _, _, _. split.
    + f_equal. apply bt_upd_congr; try reflexivity.
      * rewrite BuildTreeModel.wrap64_sub_l. f_equal. lia.
      * destruct (stree_has t); [|reflexivity]. rewrite BuildTreeModel.wrap64_sub_l. f_equal. lia.
    + rewrite !arr_len_set. split; [exact LFC|]. split; [exact LHP|]. split; [exact LDP|]. split.
      * intros j. rewrite !arr_get_set. unfold arr_inb. rewrite arr_len_set, LFC. cbn [existsb].
        rewrite (Z.eqb_sym j 0), (Z.eqb_sym j 1).
        destruct (Z.eqb_spec 1 j); [subst; cbn -[Z.ltb]; replace (1 <? tsize t) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity|].
        destruct (Z.eqb_spec 0 j); [subst; cbn -[Z.ltb]|]; cbn [orb andb]; [|reflexivity].
        replace (0 <? tsize t) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
      * intros i Hi. rewrite !arr_get_set. unfold arr_inb. rewrite arr_len_set, LHP.
        destruct (Z.eqb_spec 2 i); [subst; reflexivity|]. destruct (Z.eqb_spec 1 i); [subst; reflexivity|]. lia.
  -
    change (zlen [j1]) with 1. cbn [last app].
    pose proof (proj1 (Ul_in FC0 elems j1 ltac:(lia)) ltac:(unfold Ulist in EU; rewrite EU; now left)) as [R1 N1].
    set (node := if j1 <? 2 then j1 + 1 else 0).
    assert (Hnode : 0 <= node <= 2 /\ node <> j1) by (subst node; destruct (Z.ltb_spec j1 2); lia).
    change (zlen [j1; node]) with 2. change (zlen [node]) with 1. cbn [map zsum].
    cbn [build_tree_loop2]. autorewrite with btupd.
    replace (1 <? 2) with true by reflexivity.
    replace (if j1 <? 2 then (j1 + 1, j1 + 1) else (0, j1)) with (node, if j1 <? 2 then j1 + 1 else j1)
      by (subst node; destruct (j1 <? 2); reflexivity).
    replace (1 + 1) with 2 by reflexivity. cbv beta iota zeta. autorewrite with btupd.
    rewrite !bt_if_sl. autorewrite with btupd.
    replace (2 <? 2) with false by reflexivity. cbv beta iota zeta. rewrite ?bt_if_sl.
    eexists _, _, _. split.
    + f_equal.
      * apply bt_upd_congr; try reflexivity.
        destruct (stree_has t); [|reflexivity]. rewrite Z.add_0_r. reflexivity.
      * cbn [fold_right]. subst node. destruct (Z.ltb_spec j1 2); lia.
    + rewrite !arr_len_set. split; [exact LFC|]. split; [exact LHP|]. split; [exact LDP|]. split.
      * intros j. rewrite arr_get_set. unfold arr_inb. rewrite LFC. cbn [existsb].
        rewrite (Z.eqb_sym j node). destruct (Z.eqb_spec node j); cbn [orb andb]; [|reflexivity].
        replace ((0 <=? node) && (node <? tsize t)) with true by (symmetry; rewrite Bool.andb_true_iff, Z.leb_le, Z.ltb_lt; lia).
        reflexivity.
      * intros i Hi. rewrite arr_get_set. unfold arr_inb. rewrite LHP.
        destruct (Z.eqb_spec 2 i); [subst; reflexivity|]. cbn [andb]. rewrite HHP by (change (zlen [j1]) with 1; lia).
        replace i with 1 by lia. reflexivity.
  -
    cbn [build_tree_loop2]. autorewrite with btupd.
    replace (zlen (j1 :: j2 :: l) <? 2) with false.
    2:{ symmetry. apply Z.ltb_ge. rewrite !zlen_cons. pose proof (zlen_nonneg l). lia. }
    exists FC0, HP1, DP1. rewrite app_nil_r. split.
    + pose proof (last_UL_MCP j1 j2 l EU) as LM. unfold MCP, UP, pads in LM. fold UL in LM. rewrite EU, app_nil_r in LM. rewrite LM.
      change (zlen (@nil Z)) with 0. cbn [map zsum]. rewrite !Z.sub_0_r.
      f_equal. apply bt_upd_congr; try reflexivity.
      * symmetry. apply wrap64_id. exact OLr.
      * destruct (stree_has t); [|reflexivity]. symmetry. apply wrap64_id. exact SLr.
    + split; [exact LFC|]. split; [exact LHP|]. split; [exact LDP|]. split; [|exact HHP].
      intros j. cbn. reflexivity.
Qed.


Local Notation W6 FC DL HP HL HM0 DP := (bt_upd s t FC DL HP HL HM0 DP BC OL SL MC).

Lemma pq_flat : forall FC DL HP HL HM0 DP k,
  pqdownheap (W6 FC DL HP HL HM0 DP) t k = W6 FC DL (ds_heap (pqdownheap (W6 FC DL HP HL HM0 DP) t k)) HL HM0 DP.
Proof.
  intros. rewrite (pqdownheap_shape (W6 FC DL HP HL HM0 DP) t k) at 1. rewrite bt_set_heap. reflexivity.
Qed.

Definition dmax (DP : arr) (n m : Z) : Z := if arr_get DP m <=? arr_get DP n then arr_get DP n else arr_get DP m.

Section Trip.
Variables (FC DL HP : arr) (HL HM0 : Z) (DP : arr) (node : Z).
Let n := arr_get HP 1.
Let HP1 := arr_set HP 1 (arr_get HP HL).
Let HP2 := ds_heap (pqdownheap (W6 FC DL HP1 (HL - 1) HM0 DP) t 1).
Let m_ := arr_get HP2 1.
Let FC' := arr_set FC node (wrap16 (arr_get FC n + arr_get FC m_)).
Let DL' := arr_set (arr_set DL m_ (wrap16 node)) n (wrap16 node).
Let HP3 := arr_set (arr_set (arr_set HP2 (HM0 - 1) n) (HM0 - 2) m_) 1 node.
Let DP' := arr_set DP node (wrap8 (dmax DP n m_ + 1)).
Definition trip : deflate_state := pqdownheap (W6 FC' DL' HP3 (HL - 1) (HM0 - 2) DP') t 1.

Lemma trip_flat : trip = W6 FC' DL' (ds_heap trip) (HL - 1) (HM0 - 2) DP'.
Proof. unfold trip. apply pq_flat. Qed.

Lemma L4_step : forall f,
  build_tree_loop4 (Datatypes.S f) (W6 FC DL HP HL HM0 DP) t node =
    if 2 <=? HL - 1 then build_tree_loop4 f trip t (node + 1) else trip.
Proof.
  intros f. cbn [build_tree_loop4]. unfold SMALLEST. autorewrite with btupd.
  rewrite (pq_flat FC DL (arr_set HP 1 (arr_get HP HL)) (HL - 1) HM0 DP).
  fold HP1. fold HP2. autorewrite with btupd.
  unfold trip. subst n m_ FC' DL' HP3 DP'. fold HP1. fold HP2.
  rewrite pqdownheap_heap_len, bt_heap_len. unfold dmax.
  replace (HM0 - 1 - 1) with (HM0 - 2) by lia. reflexivity.
Qed.
End Trip.

End Build.

Fixpoint up (DL : arr) (n : nat) (a : Z) : Z := match n with O => a | S n' => arr_get DL (up DL n' a) end.

Lemma up_ext : forall DL DL' n a, (forall s, (s < n)%nat -> arr_get DL' (up DL s a) = arr_get DL (up DL s a)) ->
  up DL' n a = up DL n a.
Proof.
  induction n as [|n IH]; intros a H; cbn; [reflexivity|].
  rewrite IH by (intros; apply H; lia). apply H. lia.
Qed.




Ltac Zify.zify_post_hook ::= idtac.
