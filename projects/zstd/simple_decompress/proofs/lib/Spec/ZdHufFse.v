(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia Permutation FinFun.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas FseReadSound ZdSeqTable ZdSeqBuild ZdSeqBuildThm.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma hZnth_app_l : forall (l1 l2 : list Z) i, 0 <= i < Zlength l1 -> Znth i (l1 ++ l2) = Znth i l1.
Proof. intros l1 l2 i H. unfold Znth, Zlength in *. apply app_nth1. lia. Qed.
Lemma hZnth_app_r : forall (l1 l2 : list Z) i, 0 <= i -> Znth (Zlength l1 + i) (l1 ++ l2) = Znth i l2.
Proof.
  intros l1 l2 i H. unfold Znth, Zlength in *. rewrite app_nth2 by lia. f_equal. lia.
Qed.
Lemma hZnth_repeat : forall (x : Z) n i, 0 <= i < Z.of_nat n -> Znth i (repeat x n) = x.
Proof. intros x n i H. unfold Znth. apply nth_repeat_lt. lia. Qed.
Lemma hZlength_app : forall (l1 l2 : list Z), Zlength (l1 ++ l2) = Zlength l1 + Zlength l2.
Proof. intros. unfold Zlength. rewrite length_app. lia. Qed.
Lemma hZlength_repeat : forall (x : Z) n, Zlength (repeat x n) = Z.of_nat n.
Proof. intros. unfold Zlength. rewrite repeat_length. reflexivity. Qed.
Lemma hZnth_In : forall (l : list Z) i, 0 <= i < Zlength l -> In (Znth i l) l.
Proof. intros l i H. unfold Znth, Zlength in *. apply nth_In. lia. Qed.

Lemma zseq_length : forall n from, length (zseq n from) = n.
Proof. induction n as [|n IH]; intros; cbn [zseq length]; [reflexivity| rewrite IH; reflexivity]. Qed.
Lemma zseq_snoc : forall n from, zseq (S n) from = zseq n from ++ [from + Z.of_nat n].
Proof.
  induction n as [|n IH]; intros from.
  - cbn. rewrite Z.add_0_r. reflexivity.
  - change (zseq (S (S n)) from) with (from :: zseq (S n) (from + 1)). rewrite IH.
    cbn [zseq app]. do 3 f_equal. lia.
Qed.
Lemma zseq_NoDup : forall n from, NoDup (zseq n from).
Proof.
  induction n as [|n IH]; intros from; cbn [zseq]; constructor; [|apply IH].
  intros H. apply zseq_In_iff in H. lia.
Qed.
Lemma Znth_zseq : forall n from i, 0 <= i < Z.of_nat n -> Znth i (zseq n from) = from + i.
Proof.
  induction n as [|n IH]; intros from i H; [lia|]. unfold Znth. cbn [zseq].
  destruct (Z.to_nat i) as [|k] eqn:E; cbn [nth]; [lia|].
  specialize (IH (from + 1) (i - 1) ltac:(lia)). unfold Znth in IH. replace (Z.to_nat (i - 1)) with k in IH by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint src_list (norm : list Z) (s : Z) (k : nat) : list Z :=
  match k with O => [] | S k' => repeat s (Z.to_nat (Znth s norm)) ++ src_list norm (s + 1) k' end.
Fixpoint low_list (norm : list Z) (s : Z) (k : nat) : list Z :=
  match k with O => [] | S k' => (if Znth s norm =? -1 then [s] else []) ++ low_list norm (s + 1) k' end.

Lemma src_list_app norm : forall a b s, src_list norm s (a + b) = src_list norm s a ++ src_list norm (s + Z.of_nat a) b.
Proof.
  induction a as [|a IH]; intros b s.
  - cbn [Nat.add src_list app]. rewrite Z.add_0_r. reflexivity.
  - cbn [Nat.add src_list]. rewrite IH, <- app_assoc. do 3 f_equal. lia.
Qed.
Lemma low_list_app norm : forall a b s, low_list norm s (a + b) = low_list norm s a ++ low_list norm (s + Z.of_nat a) b.
Proof.
  induction a as [|a IH]; intros b s.
  - cbn [Nat.add low_list app]. rewrite Z.add_0_r. reflexivity.
  - cbn [Nat.add low_list]. rewrite IH, <- app_assoc. do 3 f_equal. lia.
Qed.

(* [comment removed for export] *)
Definition nsrc (norm : list Z) (s : Z) : Z := Zlength (src_list norm 0 (Z.to_nat s)).
Definition nlow (norm : list Z) (s : Z) : Z := Zlength (low_list norm 0 (Z.to_nat s)).

Lemma nsrc_0 norm : nsrc norm 0 = 0. Proof. reflexivity. Qed.
Lemma nlow_0 norm : nlow norm 0 = 0. Proof. reflexivity. Qed.
Lemma nsrc_S norm s : 0 <= s -> nsrc norm (s + 1) = nsrc norm s + Z.max 0 (Znth s norm).
Proof.
  intros H. unfold nsrc. replace (Z.to_nat (s + 1)) with (Z.to_nat s + 1)%nat by lia.
  rewrite src_list_app, hZlength_app. cbn [src_list]. rewrite app_nil_r, hZlength_repeat.
  replace (0 + Z.of_nat (Z.to_nat s)) with s by lia. lia.
Qed.
Lemma nlow_S norm s : 0 <= s -> nlow norm (s + 1) = nlow norm s + (if Znth s norm =? -1 then 1 else 0).
Proof.
  intros H. unfold nlow. replace (Z.to_nat (s + 1)) with (Z.to_nat s + 1)%nat by lia.
  rewrite low_list_app, hZlength_app. cbn [low_list]. rewrite app_nil_r.
  replace (0 + Z.of_nat (Z.to_nat s)) with s by lia. destruct (Znth s norm =? -1); reflexivity.
Qed.
Lemma nsrc_nonneg norm s : 0 <= nsrc norm s. Proof. unfold nsrc, Zlength. lia. Qed.
Lemma nlow_nonneg norm s : 0 <= nlow norm s. Proof. unfold nlow, Zlength. lia. Qed.

Lemma nsrc_mono norm : forall a b, 0 <= a <= b -> nsrc norm a <= nsrc norm b.
Proof.
  intros a b H. replace b with (a + Z.of_nat (Z.to_nat (b - a))) by lia.
  induction (Z.to_nat (b - a)) as [|n IH]; [rewrite Z.add_0_r; lia|].
  replace (a + Z.of_nat (S n)) with (a + Z.of_nat n + 1) by lia. rewrite nsrc_S by lia. lia.
Qed.
Lemma nlow_mono norm : forall a b, 0 <= a <= b -> nlow norm a <= nlow norm b.
Proof.
  intros a b H. replace b with (a + Z.of_nat (Z.to_nat (b - a))) by lia.
  induction (Z.to_nat (b - a)) as [|n IH]; [rewrite Z.add_0_r; lia|].
  replace (a + Z.of_nat (S n)) with (a + Z.of_nat n + 1) by lia. rewrite nlow_S by lia. destruct (_ =? -1); lia.
Qed.

(* [comment removed for export] *)
Lemma nsrc_nlow_pws norm : forall s, 0 <= s <= Zlength norm -> (forall i, 0 <= i < s -> -1 <= Znth i norm) ->
  nsrc norm s + nlow norm s = pws norm s.
Proof.
  intros s Hs. replace s with (Z.of_nat (Z.to_nat s)) in * by lia.
  induction (Z.to_nat s) as [|n IH]; intros GE; [reflexivity|].
  replace (Z.of_nat (S n)) with (Z.of_nat n + 1) in * by lia.
  rewrite nsrc_S, nlow_S, pws_S by lia. specialize (IH ltac:(lia) ltac:(intros; apply GE; lia)).
  specialize (GE (Z.of_nat n) ltac:(lia)). unfold weight. destruct (Z.eqb_spec (Znth (Z.of_nat n) norm) (-1)); lia.
Qed.

(* [comment removed for export] *)
Lemma Znth_src norm N s i : 0 <= s < N -> 0 <= i < Znth s norm ->
  Znth (nsrc norm s + i) (src_list norm 0 (Z.to_nat N)) = s.
Proof.
  intros Hs Hi. replace (Z.to_nat N) with (Z.to_nat s + S (Z.to_nat (N - s - 1)))%nat by lia.
  rewrite src_list_app. unfold nsrc. rewrite hZnth_app_r by lia. cbn [src_list].
  replace (0 + Z.of_nat (Z.to_nat s)) with s by lia. rewrite hZnth_app_l by (rewrite hZlength_repeat; lia).
  apply hZnth_repeat. lia.
Qed.
Lemma Znth_low norm N s : 0 <= s < N -> Znth s norm = -1 ->
  Znth (nlow norm s) (low_list norm 0 (Z.to_nat N)) = s.
Proof.
  intros Hs E. replace (Z.to_nat N) with (Z.to_nat s + S (Z.to_nat (N - s - 1)))%nat by lia.
  rewrite low_list_app. unfold nlow. replace (Zlength (low_list norm 0 (Z.to_nat s))) with (Zlength (low_list norm 0 (Z.to_nat s)) + 0) at 1 by lia.
  rewrite hZnth_app_r by lia. cbn [low_list]. replace (0 + Z.of_nat (Z.to_nat s)) with s by lia. rewrite E. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma src_list_In norm : forall k s0 x, In x (src_list norm s0 k) -> s0 <= x < s0 + Z.of_nat k /\ 0 < Znth x norm.
Proof.
  induction k as [|k IH]; intros s0 x H; cbn [src_list] in H; [contradiction|].
  apply in_app_or in H. destruct H as [H|H].
  - apply repeat_spec in H as E. subst x. split; [lia|]. destruct (Z.to_nat (Znth s0 norm)) eqn:E; [contradiction|lia].
  - apply IH in H. lia.
Qed.
Lemma low_list_In norm : forall k s0 x, In x (low_list norm s0 k) -> s0 <= x < s0 + Z.of_nat k /\ Znth x norm = -1.
Proof.
  induction k as [|k IH]; intros s0 x H; cbn [low_list] in H; [contradiction|].
  apply in_app_or in H. destruct H as [H|H].
  - destruct (Z.eqb_spec (Znth s0 norm) (-1)); [|contradiction]. destruct H as [<-|[]]. split; [lia|assumption].
  - apply IH in H. lia.
Qed.
Lemma src_list_count norm : forall k s0 s,
  count_occ Z.eq_dec (src_list norm s0 k) s = if (s0 <=? s) && (s <? s0 + Z.of_nat k) then Z.to_nat (Znth s norm) else 0%nat.
Proof.
  induction k as [|k IH]; intros s0 s; cbn [src_list].
  - cbn [count_occ]. destruct (Z.leb_spec s0 s), (Z.ltb_spec s (s0 + Z.of_nat 0)); cbn [andb]; try reflexivity. lia.
  - rewrite count_occ_app, IH. destruct (Z.eq_dec s s0) as [->|NE].
    + rewrite count_occ_repeat_eq by reflexivity.
      destruct (Z.leb_spec (s0 + 1) s0); [lia|]. cbn [andb]. destruct (Z.leb_spec s0 s0); [|lia].
      destruct (Z.ltb_spec s0 (s0 + Z.of_nat (S k))); [|lia]. cbn [andb]. lia.
    + rewrite count_occ_repeat_neq by exact NE.
      destruct (Z.leb_spec (s0 + 1) s), (Z.leb_spec s0 s), (Z.ltb_spec s (s0 + 1 + Z.of_nat k)), (Z.ltb_spec s (s0 + Z.of_nat (S k)));
        cbn [andb]; try reflexivity; lia.
Qed.
Lemma low_list_count norm : forall k s0 s,
  count_occ Z.eq_dec (low_list norm s0 k) s =
  if (s0 <=? s) && (s <? s0 + Z.of_nat k) then (if Znth s norm =? -1 then 1%nat else 0%nat) else 0%nat.
Proof.
  induction k as [|k IH]; intros s0 s; cbn [low_list].
  - cbn [count_occ]. destruct (Z.leb_spec s0 s), (Z.ltb_spec s (s0 + Z.of_nat 0)); cbn [andb]; try reflexivity. lia.
  - rewrite count_occ_app, IH. destruct (Z.eq_dec s s0) as [->|NE].
    + destruct (Z.leb_spec (s0 + 1) s0); [lia|]. cbn [andb]. destruct (Z.leb_spec s0 s0); [|lia].
      destruct (Z.ltb_spec s0 (s0 + Z.of_nat (S k))); [|lia]. cbn [andb].
      destruct (Znth s0 norm =? -1); cbn [count_occ]; [destruct (Z.eq_dec s0 s0); [reflexivity|contradiction] | reflexivity].
    + assert (E : count_occ Z.eq_dec (if Znth s0 norm =? -1 then [s0] else []) s = 0%nat).
      { destruct (Znth s0 norm =? -1); cbn [count_occ]; [destruct (Z.eq_dec s0 s); [congruence|reflexivity] | reflexivity]. }
      rewrite E.
      destruct (Z.leb_spec (s0 + 1) s), (Z.leb_spec s0 s), (Z.ltb_spec s (s0 + 1 + Z.of_nat k)), (Z.ltb_spec s (s0 + Z.of_nat (S k)));
        cbn [andb]; try reflexivity; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hpos (tl high : Z) : list Z := pos_seq (Z.to_nat (high + 1)) (2^tl) (fse_tablestep (2^tl)) high 0.

Lemma pos_seq_length : forall k size step high p, length (pos_seq k size step high p) = k.
Proof. induction k as [|k IH]; intros; cbn [pos_seq length]; [reflexivity| rewrite IH; reflexivity]. Qed.
Lemma hpos_length tl high : -1 <= high -> Zlength (hpos tl high) = high + 1.
Proof. intros H. unfold hpos, Zlength. rewrite pos_seq_length. lia. Qed.

Lemma skip_low_nonneg : forall fuel size step high q, 0 < size -> 0 <= q -> 0 <= skip_low fuel size step high q.
Proof.
  induction fuel as [|f IH]; intros size step high q Hs Hq; cbn [skip_low]; [exact Hq|].
  destruct (high <? q); [|exact Hq]. apply IH; [exact Hs|]. apply Z.mod_pos_bound. exact Hs.
Qed.

(* [comment removed for export] *)
Definition hskip_cover (tl : Z) : bool :=
  let size := 2^tl in let step := fse_tablestep size in
  forallb (fun q => existsb (fun j => (q + j * step) mod size =? 0) (zseq (Z.to_nat size) 0)) (zseq (Z.to_nat size) 0).
Lemma hskip_cover_ok : forall tl, 5 <= tl <= 9 -> hskip_cover tl = true.
Proof.
  intros tl H. assert (C : tl = 5 \/ tl = 6 \/ tl = 7 \/ tl = 8 \/ tl = 9) by lia.
  destruct C as [->|[->|[->|[->| ->]]]]; vm_compute; reflexivity.
Qed.
Lemma hskip_low_reach : forall size step high, 0 < size -> 0 <= high ->
  forall (j : nat) (fuel : nat) q, (j < fuel)%nat -> 0 <= q < size -> (q + Z.of_nat j * step) mod size = 0 ->
  skip_low fuel size step high q <= high.
Proof.
  intros size step high Hs Hh. induction j as [|j IH]; intros fuel q Hj Hq E.
  - destruct fuel as [|f]; [lia|]. cbn [skip_low].
    rewrite Z.mul_0_l, Z.add_0_r, Z.mod_small in E by lia. subst q.
    destruct (Z.ltb_spec high 0); lia.
  - destruct fuel as [|f]; [lia|]. cbn [skip_low].
    destruct (Z.ltb_spec high q); [|lia].
    apply IH; [lia| apply Z.mod_pos_bound; lia|].
    rewrite Z.add_mod_idemp_l by lia. rewrite <- E. f_equal. rewrite Nat2Z.inj_succ. ring.
Qed.
Lemma hskip_low_term : forall tl high q, 5 <= tl <= 9 -> 0 <= high -> 0 <= q < 2^tl ->
  skip_low (Z.to_nat (2^tl)) (2^tl) (fse_tablestep (2^tl)) high q <= high.
Proof.
  intros tl high q Htl Hh Hq. pose proof (hskip_cover_ok tl Htl) as C. unfold hskip_cover in C. cbv zeta in C.
  rewrite forallb_forall in C. specialize (C q ltac:(apply zseq_In_iff; lia)).
  rewrite existsb_exists in C. destruct C as (j & Hj & E). apply zseq_In_iff in Hj. apply Z.eqb_eq in E.
  assert (0 < 2^tl) by (apply Z.pow_pos_nonneg; lia).
  apply (hskip_low_reach (2^tl) _ high ltac:(lia) Hh (Z.to_nat j)); [lia| exact Hq|].
  rewrite Z2Nat.id by lia. exact E.
Qed.

Lemma next_pos_range tl high p : 5 <= tl <= 9 -> 0 <= high ->
  0 <= next_pos (2^tl) (fse_tablestep (2^tl)) high p <= high.
Proof.
  intros TL HH. assert (SZ : 0 < 2^tl) by (apply Z.pow_pos_nonneg; lia). unfold next_pos. split.
  - apply skip_low_nonneg; [exact SZ|]. apply Z.mod_pos_bound. exact SZ.
  - apply hskip_low_term; [exact TL| exact HH|]. apply Z.mod_pos_bound. exact SZ.
Qed.

Lemma pos_seq_range tl high : 5 <= tl <= 9 -> 0 <= high ->
  forall k p x, 0 <= p <= high -> In x (pos_seq k (2^tl) (fse_tablestep (2^tl)) high p) -> 0 <= x <= high.
Proof.
  intros TL HH. induction k as [|k IH]; intros p x Hp H; cbn [pos_seq] in H; [contradiction|].
  destruct H as [<-|H]; [exact Hp|]. eapply IH; [|exact H]. apply next_pos_range; assumption.
Qed.

Lemma hpos_range tl high x : 5 <= tl <= 9 -> 0 <= high -> In x (hpos tl high) -> 0 <= x <= high.
Proof. intros TL HH H. eapply (pos_seq_range tl high TL HH); [|exact H]. lia. Qed.

Lemma hpos_NoDup tl high : 5 <= tl <= 9 -> 0 <= high < 2^tl -> NoDup (hpos tl high).
Proof.
  intros TL HH. apply (NoDup_incl_NoDup (l := zseq (Z.to_nat (high + 1)) 0)); [apply zseq_NoDup| |].
  - unfold hpos. rewrite pos_seq_length, zseq_length. lia.
  - intros u Hu. apply zseq_In_iff in Hu. apply cover_all; [exact TL| exact HH| lia].
Qed.

Lemma pos_seq_nth : forall k size step high p j, (j < k)%nat ->
  nth j (pos_seq k size step high p) 0 = pos_iter j size step high p.
Proof.
  induction k as [|k IH]; intros size step high p j H; [lia|]. cbn [pos_seq].
  destruct j as [|j]; cbn [nth pos_iter]; [reflexivity|]. apply IH. lia.
Qed.
Lemma Znth_hpos tl high k : 0 <= k <= high ->
  Znth k (hpos tl high) = pos_iter (Z.to_nat k) (2^tl) (fse_tablestep (2^tl)) high 0.
Proof. intros H. unfold Znth, hpos. apply pos_seq_nth. lia. Qed.
Lemma pos_iter_S : forall k size step high p,
  pos_iter (S k) size step high p = next_pos size step high (pos_iter k size step high p).
Proof.
  induction k as [|k IH]; intros; [reflexivity|].
  change (pos_iter (S (S k)) size step high p) with (pos_iter (S k) size step high (next_pos size step high p)).
  rewrite IH. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma pos_iter_nohigh tl : 5 <= tl <= 9 -> forall k,
  pos_iter k (2^tl) (fse_tablestep (2^tl)) (2^tl - 1) 0 = (Z.of_nat k * fse_tablestep (2^tl)) mod 2^tl.
Proof.
  intros TL. assert (SZ : 0 < 2^tl) by (apply Z.pow_pos_nonneg; lia).
  induction k as [|k IH]; [cbn [pos_iter]; rewrite Z.mul_0_l, Z.mod_0_l by lia; reflexivity|].
  rewrite pos_iter_S, IH, next_pos_nohigh by exact TL. rewrite Z.add_mod_idemp_l by lia. f_equal. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma perm_scatter (T : Z -> Z) (sg S : list Z) (n : nat) :
  NoDup sg -> length sg = n -> length S = n -> (forall p, In p sg -> 0 <= p < Z.of_nat n) ->
  (forall j, 0 <= j < Z.of_nat n -> T (Znth j sg) = Znth j S) ->
  Permutation (map T (zseq n 0)) S.
Proof.
  intros ND L1 L2 B E.
  assert (ES : S = map T sg).
  { apply (nth_ext _ _ 0 (T 0)); [rewrite length_map; lia|]. intros j Hj. rewrite map_nth.
    specialize (E (Z.of_nat j) ltac:(lia)). unfold Znth in E. rewrite Nat2Z.id in E. symmetry. exact E. }
  rewrite ES. apply Permutation_map. apply Permutation_sym. apply NoDup_Permutation_bis; [exact ND| rewrite zseq_length; lia|].
  intros p Hp. apply zseq_In_iff. specialize (B p Hp). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hsym (tb : list Z) (u : Z) : Z := Znth (4 * u + 2) tb.

Section Table.
  Variables (norm : list Z) (maxSV tl : Z).
  Hypothesis TL : 5 <= tl <= 9.
  Hypothesis MSV : 0 <= maxSV.
  Hypothesis LEN : maxSV + 1 <= Zlength norm.
  Hypothesis GE : forall i, 0 <= i <= maxSV -> -1 <= Znth i norm.
  Hypothesis SUM : pws norm (maxSV + 1) = 2^tl.
  Set Default Proof Using "TL MSV LEN GE SUM".

  Let size := 2^tl.
  Definition hSRC : list Z := src_list norm 0 (Z.to_nat (maxSV + 1)).
  Definition hLOW : list Z := low_list norm 0 (Z.to_nat (maxSV + 1)).
  (* [comment removed for export] *)
  Definition hhigh : Z := size - 1 - nlow norm (maxSV + 1).

  Lemma hsize_range : 32 <= size <= 512.
  Proof.
    unfold size. assert (2^5 <= 2^tl) by (apply Z.pow_le_mono_r; lia). assert (2^tl <= 2^9) by (apply Z.pow_le_mono_r; lia).
    change (2^5) with 32 in *. change (2^9) with 512 in *. lia.
  Qed.

  Lemma hsrc_low_total : nsrc norm (maxSV + 1) + nlow norm (maxSV + 1) = size.
  Proof. rewrite nsrc_nlow_pws; [exact SUM| lia|]. intros i Hi. apply GE. lia. Qed.
  Lemma hSRC_length : Zlength hSRC = hhigh + 1.
  Proof. pose proof hsrc_low_total. unfold hhigh, hSRC. fold (nsrc norm (maxSV + 1)). lia. Qed.
  Lemma hLOW_length : Zlength hLOW = size - 1 - hhigh.
  Proof. unfold hhigh, hLOW. fold (nlow norm (maxSV + 1)). lia. Qed.
  Lemma hhigh_range : -1 <= hhigh < size.
  Proof. pose proof hsrc_low_total. pose proof (nsrc_nonneg norm (maxSV + 1)). pose proof (nlow_nonneg norm (maxSV + 1)). unfold hhigh. lia. Qed.

  (* [comment removed for export] *)
  Lemma hcount_le_size s : 0 <= s <= maxSV -> Znth s norm <= size.
  Proof.
    intros H. pose proof (nsrc_mono norm 0 s ltac:(lia)). pose proof (nsrc_mono norm (s + 1) (maxSV + 1) ltac:(lia)).
    rewrite nsrc_S in H1 by lia. rewrite nsrc_0 in H0. pose proof hsrc_low_total. pose proof (nlow_nonneg norm (maxSV + 1)). lia.
  Qed.

  (* [comment removed for export] *)
  Definition symtab_ok (tb : list Z) : Prop :=
    (forall j, 0 <= j <= hhigh -> hsym tb (Znth j (hpos tl hhigh)) = Znth j hSRC) /\
    (forall i, 0 <= i < size - 1 - hhigh -> hsym tb (size - 1 - i) = Znth i hLOW).

  Definition hT (tb : list Z) : list Z := map (hsym tb) (zseq (Z.to_nat size) 0).

  Lemma symtab_perm tb : symtab_ok tb -> Permutation (hT tb) (hSRC ++ hLOW).
  Proof.
    intros [H1 H2]. pose proof hsize_range as SR. pose proof hhigh_range as HR.
    pose proof hSRC_length as LS. pose proof hLOW_length as LL.
    set (nl := Z.to_nat (size - 1 - hhigh)).
    apply (perm_scatter (hsym tb) (hpos tl hhigh ++ map (fun i => size - 1 - i) (zseq nl 0))).
    - (* [comment removed for export] *)
      apply NoDup_app.
      + destruct (Z.eq_dec hhigh (-1)) as [E|NE]; [rewrite E; constructor| apply hpos_NoDup; [exact TL| fold size; lia]].
      + apply Finite.Injective_map_NoDup; [intros a b; lia| apply zseq_NoDup].
      + intros x Hx Hy. destruct (Z.eq_dec hhigh (-1)) as [E|NE]; [rewrite E in Hx; exact Hx|].
        apply hpos_range in Hx; [|exact TL|lia]. apply in_map_iff in Hy. destruct Hy as (i & <- & Hi). apply zseq_In_iff in Hi. lia.
    - rewrite length_app, length_map, zseq_length. pose proof (hpos_length tl hhigh ltac:(lia)) as HL. unfold Zlength in HL. lia.
    - rewrite length_app. unfold Zlength in LS, LL. lia.
    - intros p Hp. apply in_app_or in Hp. destruct Hp as [Hp|Hp].
      + destruct (Z.eq_dec hhigh (-1)) as [E|NE]; [rewrite E in Hp; contradiction|]. apply hpos_range in Hp; [|exact TL|lia]. lia.
      + apply in_map_iff in Hp. destruct Hp as (i & <- & Hi). apply zseq_In_iff in Hi. lia.
    - intros j Hj. pose proof (hpos_length tl hhigh ltac:(lia)) as HL.
      destruct (Z_lt_le_dec j (hhigh + 1)) as [A|A].
      + rewrite hZnth_app_l by lia. rewrite hZnth_app_l by lia. apply H1. lia.
      + replace j with (Zlength (hpos tl hhigh) + (j - hhigh - 1)) by lia. rewrite hZnth_app_r by lia.
        replace (Zlength (hpos tl hhigh) + (j - hhigh - 1)) with (Zlength hSRC + (j - hhigh - 1)) by lia. rewrite hZnth_app_r by lia.
        unfold Znth at 1. rewrite (nth_indep _ 0 ((fun i => size - 1 - i) 0)) by (rewrite length_map, zseq_length; lia).
        rewrite map_nth. fold (Znth (j - hhigh - 1) (zseq nl 0)). rewrite Znth_zseq by lia.
        rewrite Z.add_0_l. apply H2. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma symtab_counts tb s : symtab_ok tb -> 0 <= s <= maxSV ->
    count_occ Z.eq_dec (hT tb) s = Z.to_nat (weight (Znth s norm)).
  Proof.
    intros OK Hs. pose proof (symtab_perm tb OK) as P.
    rewrite (proj1 (Permutation_count_occ Z.eq_dec _ _) P s), count_occ_app.
    unfold hSRC, hLOW. rewrite src_list_count, low_list_count.
    destruct (Z.leb_spec 0 s); [|lia]. destruct (Z.ltb_spec s (0 + Z.of_nat (Z.to_nat (maxSV + 1)))); [|lia]. cbn [andb].
    specialize (GE s Hs). unfold weight. destruct (Z.eqb_spec (Znth s norm) (-1)) as [E|NE]; [rewrite E; reflexivity| lia].
  Qed.

  Lemma symtab_good tb v : symtab_ok tb -> 0 <= v < size -> good norm maxSV (hsym tb v).
  Proof.
    intros OK Hv. pose proof (symtab_perm tb OK) as P.
    assert (IN : In (hsym tb v) (hT tb)).
    { unfold hT. apply in_map. apply zseq_In_iff. lia. }
    apply (Permutation_in _ P) in IN. apply in_app_or in IN. unfold good. destruct IN as [IN|IN].
    - apply src_list_In in IN. lia.
    - apply low_list_In in IN. lia.
  Qed.
End Table.
Unset Default Proof Using.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma hZnth_Zupd : forall i j v (l : list Z), 0 <= i < Zlength l -> 0 <= j ->
  Znth j (Zupd i v l) = if j =? i then v else Znth j l.
Proof.
  intros i j v l Hi Hj. destruct (Z.eqb_spec j i) as [->|NE]; [apply Znth_Zupd_same; exact Hi| apply Znth_Zupd_other; lia].
Qed.
Lemma hZnth_write8 : forall (l : list Z) p v j, 0 <= p -> p + 8 <= Zlength l -> 0 <= j ->
  Znth j (write8 l p v) = if (p <=? j) && (j <? p + 8) then v else Znth j l.
Proof.
  intros l p v j Hp Hl Hj. unfold write8.
  rewrite !hZnth_Zupd by (unfold Zlength in *; rewrite ?Zupd_length; lia).
  repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b) end;
    destruct (Z.leb_spec p j), (Z.ltb_spec j (p + 8)); cbn [andb]; try reflexivity; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fse_cell_ok (tl fast : Z) (tb : list Z) (u : Z) : Prop :=
  let nb := Znth (4 * u + 3) tb in let nx := Znth (4 * u) tb + 256 * Znth (4 * u + 1) tb in
  0 <= nb <= tl /\ (fast = 1 -> 1 <= nb) /\ 0 <= nx /\ nx + 2^nb <= 2^tl.

(* [comment removed for export] *)
Definition hocc (T : Z -> Z) (s u : Z) : Z := Z.of_nat (count_occ Z.eq_dec (map T (zseq (Z.to_nat u) 0)) s).

Lemma hocc_0 T s : hocc T s 0 = 0. Proof. reflexivity. Qed.
Lemma hocc_S T s u : 0 <= u -> hocc T s (u + 1) = hocc T s u + (if T u =? s then 1 else 0).
Proof.
  intros H. unfold hocc. replace (Z.to_nat (u + 1)) with (S (Z.to_nat u)) by lia.
  rewrite zseq_snoc, map_app, count_occ_app. cbn [map count_occ]. rewrite Z.add_0_l, Z2Nat.id by lia.
  destruct (Z.eq_dec (T u) s) as [E|NE]; destruct (Z.eqb_spec (T u) s); try contradiction; lia.
Qed.
Lemma hocc_mono T s : forall a b, 0 <= a <= b -> hocc T s a <= hocc T s b.
Proof.
  intros a b H. replace b with (a + Z.of_nat (Z.to_nat (b - a))) by lia.
  induction (Z.to_nat (b - a)) as [|n IH]; [rewrite Z.add_0_r; lia|].
  replace (a + Z.of_nat (S n)) with (a + Z.of_nat n + 1) by lia. rewrite hocc_S by lia. destruct (_ =? s); lia.
Qed.

Section Passes.
  Variables (norm : list Z) (maxSV tl : Z).
  Hypothesis TL : 5 <= tl <= 9.
  Hypothesis MSV : 0 <= maxSV <= 255.
  Hypothesis LEN : maxSV + 1 <= Zlength norm.
  Hypothesis GE : forall i, 0 <= i <= maxSV -> -1 <= Znth i norm.
  Hypothesis SUM : pws norm (maxSV + 1) = 2^tl.
  Set Default Proof Using "TL MSV LEN GE SUM".

  Let size := 2^tl.
  Notation SRC := (hSRC norm maxSV).
  Notation LOW := (hLOW norm maxSV).
  Notation HIGH := (hhigh norm maxSV tl).

  Local Lemma MSV0 : 0 <= maxSV. Proof. lia. Qed.
  Local Lemma SR : 32 <= size <= 512.
  Proof. exact (hsize_range norm maxSV tl TL MSV0 LEN GE SUM). Qed.

  Lemma hnorm_range s : 0 <= s <= maxSV -> -1 <= Znth s norm <= size.
  Proof. intros H. split; [apply GE; exact H| apply (hcount_le_size norm maxSV tl TL MSV0 LEN GE SUM); exact H]. Qed.

  Lemma hsnext0 s : 0 <= s <= maxSV -> snext0 norm s = if Znth s norm =? -1 then 1 else Znth s norm.
  Proof.
    intros H. unfold snext0. pose proof (hnorm_range s H). pose proof SR.
    destruct (Z.eqb_spec (Znth s norm) (-1)); [reflexivity|]. apply Z.mod_small. change (2^16) with 65536. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition p1_inv (s : Z) (tb sn : list Z) (high fast : Z) : Prop :=
    Zlength tb = 4 * size /\ Zlength sn = maxSV + 1 /\
    high = size - 1 - nlow norm s /\
    (forall i, 0 <= i < nlow norm s -> hsym tb (size - 1 - i) = Znth i LOW) /\
    (forall i, 0 <= i < s -> Znth i sn = snext0 norm i) /\
    0 <= fast <= 1 /\ (fast = 1 -> forall i, 0 <= i < s -> Znth i norm < 2^(tl - 1)).

  Lemma p1_init tb sn : Zlength tb = 4 * size -> Zlength sn = maxSV + 1 -> p1_inv 0 tb sn (size - 1) 1.
  Proof.
    intros H1 H2. unfold p1_inv. rewrite nlow_0. split; [exact H1|]. split; [exact H2|]. split; [lia|].
    split; [intros; lia|]. split; [intros; lia|]. split; [lia|]. intros; lia.
  Qed.

  Lemma nlow_le s : 0 <= s <= maxSV + 1 -> nlow norm s <= size - nsrc norm (maxSV + 1).
  Proof.
    intros H. pose proof (nlow_mono norm s (maxSV + 1) ltac:(lia)).
    pose proof (hsrc_low_total norm maxSV tl TL MSV0 LEN GE SUM). fold size in H1. lia.
  Qed.

  Lemma p1_low s tb sn high fast : p1_inv s tb sn high fast -> 0 <= s <= maxSV -> Znth s norm = -1 ->
    0 <= high < size /\ p1_inv (s + 1) (Zupd (4 * high + 2) s tb) (Zupd s 1 sn) (high - 1) fast.
  Proof.
    intros (I1 & I2 & I3 & I4 & I5 & I6 & I7) Hs E. pose proof SR as SR.
    pose proof (nlow_S norm s ltac:(lia)) as NS. rewrite E in NS. change (-1 =? -1) with true in NS. cbv iota in NS.
    pose proof (nlow_le (s + 1) ltac:(lia)) as NL. pose proof (nsrc_nonneg norm (maxSV + 1)). pose proof (nlow_nonneg norm s).
    assert (HH : 0 <= high < size) by lia. split; [exact HH|].
    unfold p1_inv. split; [unfold Zlength in *; rewrite Zupd_length; exact I1|].
    split; [unfold Zlength in *; rewrite Zupd_length; exact I2|]. split; [lia|].
    split.
    { intros i Hi. unfold hsym. destruct (Z.eq_dec i (nlow norm s)) as [->|NE].
      - replace (size - 1 - nlow norm s) with high by lia. rewrite Znth_Zupd_same by lia.
        symmetry. apply Znth_low; [lia| exact E].
      - rewrite Znth_Zupd_other by lia. apply I4. lia. }
    split.
    { intros i Hi. destruct (Z.eq_dec i s) as [->|NE].
      - rewrite Znth_Zupd_same by lia. unfold snext0. rewrite E. reflexivity.
      - rewrite Znth_Zupd_other by lia. apply I5. lia. }
    split; [exact I6|]. intros F i Hi. destruct (Z.eq_dec i s) as [->|NE]; [rewrite E; assert (0 < 2^(tl - 1)) by (apply Z.pow_pos_nonneg; lia); lia|].
    apply I7; [exact F| lia].
  Qed.

  Lemma p1_norm s tb sn high fast : p1_inv s tb sn high fast -> 0 <= s <= maxSV -> Znth s norm <> -1 ->
    0 <= Znth s norm <= size /\
    p1_inv (s + 1) tb (Zupd s (Znth s norm) sn) high (if 2^(tl - 1) <=? Znth s norm then 0 else fast).
  Proof.
    intros (I1 & I2 & I3 & I4 & I5 & I6 & I7) Hs NE. pose proof SR as SR. pose proof (hnorm_range s Hs) as NR.
    pose proof (nlow_S norm s ltac:(lia)) as NS. destruct (Z.eqb_spec (Znth s norm) (-1)) as [|_] in NS; [contradiction|].
    split; [lia|]. unfold p1_inv. split; [exact I1|]. split; [unfold Zlength in *; rewrite Zupd_length; exact I2|].
    split; [lia|]. split; [intros i Hi; apply I4; lia|].
    split.
    { intros i Hi. destruct (Z.eq_dec i s) as [->|NE2].
      - rewrite Znth_Zupd_same by lia. rewrite hsnext0 by exact Hs. destruct (Z.eqb_spec (Znth s norm) (-1)); [contradiction|reflexivity].
      - rewrite Znth_Zupd_other by lia. apply I5. lia. }
    split; [destruct (_ <=? _); lia|].
    intros F i Hi. destruct (Z.leb_spec (2^(tl - 1)) (Znth s norm)) as [L|L]; [discriminate F|].
    destruct (Z.eq_dec i s) as [->|NE2]; [exact L|]. apply I7; [exact F| lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition p2_inv (k : Z) (tb : list Z) : Prop :=
    Zlength tb = 4 * size /\
    (forall j, 0 <= j < k -> hsym tb (Znth j (hpos tl HIGH)) = Znth j SRC) /\
    (forall i, 0 <= i < size - 1 - HIGH -> hsym tb (size - 1 - i) = Znth i LOW).

  Lemma p2_init tb sn high fast : p1_inv (maxSV + 1) tb sn high fast -> high = HIGH /\ p2_inv 0 tb.
  Proof.
    intros (I1 & I2 & I3 & I4 & _). split; [exact I3|]. unfold p2_inv. split; [exact I1|]. split; [intros; lia|].
    intros i Hi. apply I4. unfold hhigh in Hi. fold size in Hi. lia.
  Qed.

  Lemma p2_step k tb : p2_inv k tb -> 0 <= k <= HIGH ->
    0 <= Znth k (hpos tl HIGH) <= HIGH /\
    p2_inv (k + 1) (Zupd (4 * Znth k (hpos tl HIGH) + 2) (Znth k SRC) tb).
  Proof.
    intros (I1 & I2 & I3) Hk. pose proof SR as SR.
    pose proof (hhigh_range norm maxSV tl TL MSV0 LEN GE SUM) as HR. fold size in HR.
    pose proof (hpos_length tl HIGH ltac:(lia)) as PL.
    assert (PR : 0 <= Znth k (hpos tl HIGH) <= HIGH).
    { apply (hpos_range tl HIGH); [exact TL| lia|]. apply hZnth_In. lia. }
    split; [exact PR|]. unfold p2_inv. split; [unfold Zlength in *; rewrite Zupd_length; exact I1|]. split.
    - intros j Hj. unfold hsym. destruct (Z.eq_dec j k) as [->|NE].
      + rewrite Znth_Zupd_same by lia. reflexivity.
      + assert (D : Znth j (hpos tl HIGH) <> Znth k (hpos tl HIGH)).
        { pose proof (hpos_NoDup tl HIGH TL ltac:(fold size; lia)) as ND. rewrite (NoDup_nth _ 0) in ND.
          intros EQ. unfold Znth in EQ. apply ND in EQ; unfold Zlength in PL; lia. }
        assert (PJ : 0 <= Znth j (hpos tl HIGH) <= HIGH).
        { apply (hpos_range tl HIGH); [exact TL| lia|]. apply hZnth_In. lia. }
        rewrite Znth_Zupd_other by lia. apply I2. lia.
    - intros i Hi. unfold hsym. rewrite Znth_Zupd_other by lia. apply I3. exact Hi.
  Qed.

  Lemma p2_done tb : p2_inv (HIGH + 1) tb -> symtab_ok norm maxSV tl tb.
  Proof. intros (I1 & I2 & I3). split; [intros j Hj; apply I2; lia| exact I3]. Qed.

  (* [comment removed for export] *)
  Lemma hSRC_at s i : 0 <= s <= maxSV -> 0 <= i < Znth s norm -> Znth (nsrc norm s + i) SRC = s.
  Proof. intros Hs Hi. apply Znth_src; lia. Qed.
  Lemma hSRC_total : nsrc norm (maxSV + 1) = HIGH + 1.
  Proof. pose proof (hSRC_length norm maxSV tl TL MSV0 LEN GE SUM) as H. exact H. Qed.

  (* [comment removed for export] *)
  Lemma hnolow s : HIGH = size - 1 -> 0 <= s <= maxSV -> 0 <= Znth s norm.
  Proof.
    intros HH Hs. unfold hhigh in HH. fold size in HH. pose proof (GE s Hs).
    destruct (Z.eq_dec (Znth s norm) (-1)) as [E|NE]; [|lia]. exfalso.
    pose proof (nlow_S norm s ltac:(lia)) as NS. rewrite E in NS. change (-1 =? -1) with true in NS. cbv iota in NS.
    pose proof (nlow_mono norm (s + 1) (maxSV + 1) ltac:(lia)). pose proof (nlow_nonneg norm s). lia.
  Qed.

  (* [comment removed for export] *)
  Definition lay_inv (s : Z) (sp : list Z) : Prop := forall j, 0 <= j < nsrc norm s -> Znth j sp = Znth j SRC.

  Lemma lay_write8 s i sp : 0 <= s <= maxSV -> 0 <= i -> nsrc norm s + i + 8 <= Zlength sp ->
    lay_inv s sp -> (forall j, nsrc norm s <= j < nsrc norm s + i -> Znth j sp = s) ->
    lay_inv s (write8 sp (nsrc norm s + i) s) /\
    (forall j, nsrc norm s <= j < nsrc norm s + i + 8 -> Znth j (write8 sp (nsrc norm s + i) s) = s).
  Proof.
    intros Hs Hi HL LI HS. pose proof (nsrc_nonneg norm s). split.
    - intros j Hj. rewrite hZnth_write8 by lia.
      destruct (Z.leb_spec (nsrc norm s + i) j); [lia|]. cbn [andb]. apply LI. exact Hj.
    - intros j Hj. rewrite hZnth_write8 by lia.
      destruct (Z.leb_spec (nsrc norm s + i) j), (Z.ltb_spec j (nsrc norm s + i + 8)); cbn [andb]; try reflexivity; try lia.
      apply HS. lia.
  Qed.

  Lemma lay_next s i sp : 0 <= s <= maxSV -> Znth s norm <= i -> 0 <= Znth s norm ->
    lay_inv s sp -> (forall j, nsrc norm s <= j < nsrc norm s + i -> Znth j sp = s) -> lay_inv (s + 1) sp.
  Proof.
    intros Hs Hi NN LI HS j Hj. rewrite nsrc_S in Hj by lia.
    destruct (Z_lt_le_dec j (nsrc norm s)) as [A|A]; [apply LI; lia|].
    rewrite HS by lia. replace j with (nsrc norm s + (j - nsrc norm s)) at 1 by lia. symmetry. apply hSRC_at; [exact Hs| lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section P3.
    Variables (T : Z -> Z) (fast : Z).
    Hypothesis TGOOD : forall v, 0 <= v < size -> good norm maxSV (T v).
    Hypothesis TCNT : forall s, 0 <= s <= maxSV -> hocc T s size = weight (Znth s norm).
    Hypothesis FAST : fast = 1 -> forall i, 0 <= i <= maxSV -> Znth i norm < 2^(tl - 1).

    Definition p3_inv (u : Z) (tb sn : list Z) : Prop :=
      Zlength tb = 4 * size /\ Zlength sn = maxSV + 1 /\
      (forall v, 0 <= v < size -> hsym tb v = T v) /\
      (forall v, 0 <= v < u -> fse_cell_ok tl fast tb v) /\
      (forall s, 0 <= s <= maxSV -> Znth s norm <> 0 -> Znth s sn = snext0 norm s + hocc T s u).

    Lemma p3_step u tb sn : p3_inv u tb sn -> 0 <= u < size ->
      let s := hsym tb u in let ns := Znth s sn in let nb := tl - Z.log2 ns in let nx := ns * 2^nb - size in
      0 <= s <= maxSV /\ 1 <= ns < 2 * size /\ 0 <= Z.log2 ns <= tl /\ 0 <= nx < size /\
      p3_inv (u + 1) (Zupd (4 * u + 3) nb (Zupd (4 * u + 1) (nx / 256) (Zupd (4 * u) (nx mod 256) tb))) (Zupd s (ns + 1) sn).
    Proof using TL MSV LEN GE SUM TGOOD TCNT FAST.
      intros (I1 & I2 & I3 & I4 & I5) Hu s ns nb nx. pose proof SR as SR.
      assert (ES : s = T u) by (apply I3; exact Hu).
      pose proof (TGOOD u Hu) as (GS & NZ). rewrite <- ES in GS, NZ.
      pose proof (hnorm_range s GS) as NR.
      assert (NSV : ns = snext0 norm s + hocc T s u) by (apply I5; assumption).
      pose proof (hocc_S T s u ltac:(lia)) as OS. rewrite <- ES, Z.eqb_refl in OS.
      pose proof (hocc_mono T s (u + 1) size ltac:(lia)) as OM. rewrite (TCNT s GS) in OM.
      pose proof (hocc_mono T s 0 u ltac:(lia)) as O0. rewrite hocc_0 in O0.
      rewrite (hsnext0 s GS) in NSV.
      assert (NSR : 1 <= ns < 2 * size /\ (fast = 1 -> ns < 2^(tl - 1) * 2)).
      { unfold weight in OM. destruct (Z.eqb_spec (Znth s norm) (-1)) as [E|NE].
        - split; [lia|]. intros _. assert (16 <= 2^(tl - 1)); [|lia]. change 16 with (2^4). apply Z.pow_le_mono_r; lia.
        - split; [lia|]. intros F. specialize (FAST F s GS). lia. }
      destruct NSR as (NSR & NSF).
      assert (P2 : 2^(tl - 1) * 2 = size).
      { unfold size. replace tl with (Z.succ (tl - 1)) at 2 by lia. rewrite Z.pow_succ_r by lia. lia. }
      set (L := Z.log2 ns) in *.
      assert (L0 : 0 <= L) by apply Z.log2_nonneg.
      assert (LT : L <= tl).
      { assert (L < tl + 1); [|lia]. apply Z.log2_lt_pow2; [lia|]. rewrite Z.pow_add_r by lia. fold size. lia. }
      pose proof (Z.log2_spec ns ltac:(lia)) as SP. fold L in SP. rewrite Z.pow_succ_r in SP by lia.
      assert (PW : 2^L * 2^(tl - L) = size) by (unfold size; rewrite <- Z.pow_add_r by lia; f_equal; lia).
      assert (PP : 0 < 2^(tl - L)) by (apply Z.pow_pos_nonneg; lia).
      assert (NX : 0 <= nx /\ nx + 2^(tl - L) <= size) by (unfold nx, nb; nia).
      assert (NXR : 0 <= nx < size) by lia.
      split; [exact GS|]. split; [exact NSR|]. split; [lia|]. split; [exact NXR|].
      assert (LEN3 : forall a b c x y z (l : list Z), Zlength (Zupd a x (Zupd b y (Zupd c z l))) = Zlength l)
        by (intros; unfold Zlength; rewrite !Zupd_length; reflexivity).
      unfold p3_inv. split; [rewrite LEN3; exact I1|]. split; [unfold Zlength in *; rewrite Zupd_length; exact I2|].
      assert (OTH : forall j, 0 <= j -> j <> 4 * u -> j <> 4 * u + 1 -> j <> 4 * u + 3 ->
                Znth j (Zupd (4 * u + 3) nb (Zupd (4 * u + 1) (nx / 256) (Zupd (4 * u) (nx mod 256) tb))) = Znth j tb).
      { intros j J0 J1 J2 J3. rewrite !Znth_Zupd_other by lia. reflexivity. }
      split; [intros v Hv; unfold hsym; rewrite OTH by lia; apply I3; exact Hv|].
      split.
      { intros v Hv. destruct (Z.eq_dec v u) as [->|NE].
        - unfold fse_cell_ok. cbv zeta.
          rewrite Znth_Zupd_same by (unfold Zlength in *; rewrite !Zupd_length; lia).
          rewrite (Znth_Zupd_other (4 * u + 3)) by lia. rewrite (Znth_Zupd_other (4 * u + 1) (4 * u)) by lia.
          rewrite Znth_Zupd_same by lia. rewrite (Znth_Zupd_other (4 * u + 3)) by lia.
          rewrite Znth_Zupd_same by (unfold Zlength in *; rewrite !Zupd_length; lia).
          replace (nx mod 256 + 256 * (nx / 256)) with nx by (pose proof (Z.div_mod nx 256 ltac:(lia)); lia).
          unfold nb. fold L. split; [lia|]. split; [|lia].
          intros F. specialize (NSF F). rewrite P2 in NSF. assert (L < tl); [|lia]. apply Z.log2_lt_pow2; [lia| exact NSF].
        - specialize (I4 v ltac:(lia)). unfold fse_cell_ok in *. cbv zeta in *. rewrite !OTH by lia. exact I4. }
      intros s' Hs' NZ'. rewrite hocc_S by lia. rewrite <- ES.
      destruct (Z.eq_dec s' s) as [->|NE].
      - rewrite Znth_Zupd_same by lia. rewrite Z.eqb_refl. rewrite NSV. rewrite (hsnext0 s GS). lia.
      - rewrite Znth_Zupd_other by lia. destruct (Z.eqb_spec s s'); [congruence|]. rewrite (I5 s' Hs' NZ'). lia.
    Qed.

    Lemma p3_done tb sn : p3_inv size tb sn -> forall u, 0 <= u < size -> fse_cell_ok tl fast tb u.
    Proof using TL MSV LEN GE SUM TGOOD TCNT FAST. intros (_ & _ & _ & I4 & _) u Hu. apply I4. exact Hu. Qed.
  End P3.

  (* [comment removed for export] *)
  Lemma p3_init tb sn high fast : p1_inv (maxSV + 1) tb sn high fast -> forall tb2, symtab_ok norm maxSV tl tb2 -> Zlength tb2 = 4 * size ->
    (forall v, 0 <= v < size -> good norm maxSV (hsym tb2 v)) /\
    (forall s, 0 <= s <= maxSV -> hocc (hsym tb2) s size = weight (Znth s norm)) /\
    (fast = 1 -> forall i, 0 <= i <= maxSV -> Znth i norm < 2^(tl - 1)) /\
    p3_inv (hsym tb2) fast 0 tb2 sn.
  Proof.
    intros (I1 & I2 & I3 & I4 & I5 & I6 & I7) tb2 OK L2.
    split; [intros v Hv; apply (symtab_good norm maxSV tl TL MSV0 LEN GE SUM); assumption|].
    split.
    { intros s Hs. unfold hocc. pose proof (symtab_counts norm maxSV tl TL MSV0 LEN GE SUM tb2 s OK Hs) as C.
      unfold hT in C. fold size in C. rewrite C. pose proof (GE s Hs). unfold weight. destruct (Z.eqb_spec (Znth s norm) (-1)); lia. }
    split; [intros F i Hi; apply I7; [exact F| lia]|].
    unfold p3_inv. split; [exact L2|]. split; [exact I2|]. split; [intros; reflexivity|]. split; [intros; lia|].
    intros s Hs _. rewrite hocc_0, Z.add_0_r. apply I5. lia.
  Qed.
End Passes.
Unset Default Proof Using.
