(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas FseReadSound ZdSeqTable ZdSeqBuild.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma set_base_nat_length n v l : length (set_base_nat n v l) = length l.
Proof. revert n; induction l as [|c l IH]; intros [|n]; cbn; auto. Qed.
Lemma set_base_length i v l : length (set_base i v l) = length l.
Proof. unfold set_base. destruct (i <? 0); [reflexivity|apply set_base_nat_length]. Qed.

Lemma set_base_nat_same n v l : (n < length l)%nat -> ss_base (nth n (set_base_nat n v l) ss0) = v.
Proof. revert n; induction l as [|c l IH]; intros [|n] H; cbn in *; try lia; auto. apply IH; lia. Qed.
Lemma set_base_nat_other n m v l : n <> m -> nth m (set_base_nat n v l) ss0 = nth m l ss0.
Proof. revert n m; induction l as [|c l IH]; intros [|n] [|m] H; cbn; auto; try lia. Qed.

Lemma cell_nth_set_base_same i v l : 0 <= i < Zlength l -> ss_base (cell_nth (set_base i v l) i) = v.
Proof.
  intros H. unfold cell_nth, set_base. destruct (Z.ltb_spec i 0); [lia|]. apply set_base_nat_same. unfold Zlength in H. lia.
Qed.
Lemma cell_nth_set_base_other i j v l : 0 <= j -> i <> j -> cell_nth (set_base i v l) j = cell_nth l j.
Proof.
  intros Hj H. unfold cell_nth, set_base. destruct (Z.ltb_spec i 0); [reflexivity|]. apply set_base_nat_other. lia.
Qed.

Lemma set_cell_nat_length n c l : length (set_cell_nat n c l) = length l.
Proof. revert n; induction l as [|x l IH]; intros [|n]; cbn; auto. Qed.
Lemma set_cell_length i c l : length (set_cell i c l) = length l.
Proof. unfold set_cell. destruct (i <? 0); [reflexivity|apply set_cell_nat_length]. Qed.
Lemma set_cell_nat_same n c l : (n < length l)%nat -> nth n (set_cell_nat n c l) ss0 = c.
Proof. revert n; induction l as [|x l IH]; intros [|n] H; cbn in *; try lia; auto. apply IH; lia. Qed.
Lemma set_cell_nat_other n m c l : n <> m -> nth m (set_cell_nat n c l) ss0 = nth m l ss0.
Proof. revert n m; induction l as [|x l IH]; intros [|n] [|m] H; cbn; auto; try lia. Qed.
Lemma cell_nth_set_cell_same i c l : 0 <= i < Zlength l -> cell_nth (set_cell i c l) i = c.
Proof. intros H. unfold cell_nth, set_cell. destruct (Z.ltb_spec i 0); [lia|]. apply set_cell_nat_same. unfold Zlength in H. lia. Qed.
Lemma cell_nth_set_cell_other i j c l : 0 <= j -> i <> j -> cell_nth (set_cell i c l) j = cell_nth l j.
Proof. intros Hj H. unfold cell_nth, set_cell. destruct (Z.ltb_spec i 0); [reflexivity|]. apply set_cell_nat_other. lia. Qed.

Lemma Znth_Zupd_neg i j v l : i < 0 -> 0 < j -> Znth j (Zupd i v l) = Znth j l.
Proof.
  intros Hi Hj. unfold Znth, Zupd. replace (Z.to_nat i) with 0%nat by lia. apply nth_upd_nat_other. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint pos_seq (k : nat) (size step high p : Z) : list Z :=
  match k with O => [] | S k' => p :: pos_seq k' size step high (next_pos size step high p) end.
Fixpoint pos_iter (k : nat) (size step high p : Z) : Z :=
  match k with O => p | S k' => pos_iter k' size step high (next_pos size step high p) end.

Lemma pos_seq_app a : forall b size step high p,
  pos_seq (a + b) size step high p = pos_seq a size step high p ++ pos_seq b size step high (pos_iter a size step high p).
Proof. induction a as [|a IH]; intros; cbn [pos_seq pos_iter Nat.add app]; [reflexivity|]. rewrite IH. reflexivity. Qed.
Lemma pos_iter_add a : forall b size step high p,
  pos_iter (a + b) size step high p = pos_iter b size step high (pos_iter a size step high p).
Proof. induction a as [|a IH]; intros; cbn [pos_iter Nat.add]; [reflexivity|]. apply IH. Qed.

Lemma zseq_In_iff n : forall from x, In x (zseq n from) <-> from <= x < from + Z.of_nat n.
Proof.
  induction n as [|n IH]; intros from x; cbn [zseq In]; [lia|]. rewrite IH. lia.
Qed.

(* [comment removed for export] *)
Definition cover_one (tl high : Z) : bool :=
  let size := 2^tl in
  let l := pos_seq (Z.to_nat (high + 1)) size (fse_tablestep size) high 0 in
  forallb (fun u => existsb (Z.eqb u) l) (zseq (Z.to_nat (high + 1)) 0).
Definition cover_tl (tl : Z) : bool := forallb (cover_one tl) (zseq (Z.to_nat (2^tl)) 0).

Lemma cover_5 : cover_tl 5 = true. Proof. vm_compute. reflexivity. Qed.
Lemma cover_6 : cover_tl 6 = true. Proof. vm_compute. reflexivity. Qed.
Lemma cover_7 : cover_tl 7 = true. Proof. vm_compute. reflexivity. Qed.
Lemma cover_8 : cover_tl 8 = true. Proof. vm_compute. reflexivity. Qed.
Lemma cover_9 : cover_tl 9 = true. Proof. vm_compute. reflexivity. Qed.

Lemma cover_all tl high u : 5 <= tl <= 9 -> 0 <= high < 2^tl -> 0 <= u <= high ->
  In u (pos_seq (Z.to_nat (high + 1)) (2^tl) (fse_tablestep (2^tl)) high 0).
Proof.
  intros TL HH HU.
  assert (C : cover_tl tl = true).
  { assert (E : tl = 5 \/ tl = 6 \/ tl = 7 \/ tl = 8 \/ tl = 9) by lia.
    destruct E as [->|[->|[->|[->| ->]]]]; [apply cover_5|apply cover_6|apply cover_7|apply cover_8|apply cover_9]. }
  unfold cover_tl in C. rewrite forallb_forall in C.
  specialize (C high ltac:(apply zseq_In_iff; lia)). unfold cover_one in C. cbv zeta in C.
  rewrite forallb_forall in C. specialize (C u ltac:(apply zseq_In_iff; lia)).
  rewrite existsb_exists in C. destruct C as (x & Hx & E). apply Z.eqb_eq in E. subst x. exact Hx.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Build.
  Variables (norm : list Z) (maxSV tl : Z).
  Hypothesis TL : 5 <= tl <= 9.
  Hypothesis MSV : 0 <= maxSV <= 52.
  Hypothesis LEN : maxSV + 1 <= Zlength norm.
  Hypothesis GE : forall i, 0 <= i <= maxSV -> -1 <= Znth i norm.
  Hypothesis SUM : pws norm (maxSV + 1) = 2^tl.

  Let size := 2^tl.

  Lemma size_range : 32 <= size <= 512.
  Proof.
    unfold size. assert (2^5 <= 2^tl) by (apply Z.pow_le_mono_r; lia). assert (2^tl <= 2^9) by (apply Z.pow_le_mono_r; lia).
    change (2^5) with 32 in *. change (2^9) with 512 in *. lia.
  Qed.

  (* [comment removed for export] *)
  Definition good (s : Z) : Prop := 0 <= s <= maxSV /\ Znth s norm <> 0.

  Lemma weight_nonneg i : 0 <= i <= maxSV -> 0 <= weight (Znth i norm).
  Proof. intros H. specialize (GE i H). unfold weight. destruct (Z.eqb_spec (Znth i norm) (-1)); lia. Qed.

  Lemma pws_mono a b : 0 <= a <= b -> b <= maxSV + 1 -> pws norm a <= pws norm b.
  Proof.
    intros Hab Hb. replace b with (a + Z.of_nat (Z.to_nat (b - a))) by lia.
    induction (Z.to_nat (b - a)) as [|n IH] eqn:E in b, Hab, Hb |- *.
    - rewrite Z.add_0_r. lia.
    - assert (Hn : Z.to_nat (b - 1 - a) = n) by lia.
      specialize (IH (b - 1) ltac:(lia) ltac:(lia) Hn).
      replace (a + Z.of_nat (S n)) with (a + Z.of_nat n + 1) by lia.
      rewrite pws_S by (unfold Zlength in *; lia). pose proof (weight_nonneg (a + Z.of_nat n) ltac:(lia)). lia.
  Qed.

  Lemma pws_0 : pws norm 0 = 0.
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma count_le_size i : 0 <= i <= maxSV -> weight (Znth i norm) <= size.
  Proof.
    intros H. pose proof (pws_mono 0 i ltac:(lia) ltac:(lia)). pose proof (pws_mono (i + 1) (maxSV + 1) ltac:(lia) ltac:(lia)).
    rewrite pws_S in H1 by (unfold Zlength in *; lia). rewrite pws_0 in H0. unfold size. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Fixpoint nsum_list (l : list Z) : Z := match l with [] => 0 | c :: t => Z.max 0 c + nsum_list t end.
  Definition nsum (k : Z) : Z := nsum_list (firstn (Z.to_nat k) norm).

  Lemma nsum_list_firstn_S : forall (l : list Z) (n : nat), (n < length l)%nat ->
    nsum_list (firstn (S n) l) = nsum_list (firstn n l) + Z.max 0 (nth n l 0).
  Proof.
    induction l as [|c l IH]; intros [|n] H; cbn [length] in H; try lia.
    - cbn. lia.
    - change (firstn (S (S n)) (c :: l)) with (c :: firstn (S n) l).
      change (firstn (S n) (c :: l)) with (c :: firstn n l). change (nth (S n) (c :: l) 0) with (nth n l 0).
      cbn [nsum_list]. rewrite IH by lia. lia.
  Qed.

  Lemma nsum_S k : 0 <= k < Zlength norm -> nsum (k + 1) = nsum k + Z.max 0 (Znth k norm).
  Proof.
    intros H. unfold nsum, Znth. replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) by lia.
    apply nsum_list_firstn_S. unfold Zlength in H. lia.
  Qed.

  Lemma nsum_mono a b : 0 <= a <= b -> b <= maxSV + 1 -> nsum a <= nsum b.
  Proof.
    intros Hab Hb. replace b with (a + Z.of_nat (Z.to_nat (b - a))) by lia.
    induction (Z.to_nat (b - a)) as [|n IH] eqn:E in b, Hab, Hb |- *.
    - rewrite Z.add_0_r. lia.
    - assert (Hn : Z.to_nat (b - 1 - a) = n) by lia.
      specialize (IH (b - 1) ltac:(lia) ltac:(lia) Hn).
      replace (a + Z.of_nat (S n)) with (a + Z.of_nat n + 1) by lia.
      rewrite nsum_S by (unfold Zlength in *; lia). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma low_step k : 0 <= k <= maxSV ->
    pws norm (k + 1) - nsum (k + 1) = pws norm k - nsum k + (if Znth k norm =? -1 then 1 else 0).
  Proof.
    intros H. rewrite pws_S, nsum_S by (unfold Zlength in *; lia). specialize (GE k H). unfold weight.
    destruct (Z.eqb_spec (Znth k norm) (-1)); lia.
  Qed.

  Lemma low_mono a b : 0 <= a <= b -> b <= maxSV + 1 -> pws norm a - nsum a <= pws norm b - nsum b.
  Proof.
    intros Hab Hb. replace b with (a + Z.of_nat (Z.to_nat (b - a))) by lia.
    induction (Z.to_nat (b - a)) as [|n IH] eqn:E in b, Hab, Hb |- *.
    - rewrite Z.add_0_r. lia.
    - assert (Hn : Z.to_nat (b - 1 - a) = n) by lia.
      specialize (IH (b - 1) ltac:(lia) ltac:(lia) Hn).
      replace (a + Z.of_nat (S n)) with (a + Z.of_nat n + 1) by lia.
      rewrite low_step by lia. destruct (_ =? -1); lia.
  Qed.

  Lemma nsum_nonneg k : 0 <= k <= maxSV + 1 -> 0 <= nsum k.
  Proof. intros H. pose proof (nsum_mono 0 k ltac:(lia) ltac:(lia)). change (nsum 0) with 0 in H0. lia. Qed.

  (* [comment removed for export] *)
  Definition snext0 (i : Z) : Z := if Znth i norm =? -1 then 1 else Znth i norm mod 2^16.

  Lemma snext0_good i : good i -> 1 <= snext0 i <= size.
  Proof.
    intros (Hi & NZ). unfold snext0. pose proof (GE i Hi). pose proof (count_le_size i Hi) as C. unfold weight in C.
    pose proof size_range.
    destruct (Z.eqb_spec (Znth i norm) (-1)); [lia|]. rewrite Z.mod_small by (change (2^16) with 65536; lia). lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma lowprob_inv ll : forall (f : nat) s cells symNext high fast,
    0 <= s -> s + Z.of_nat f = maxSV + 1 ->
    Zlength cells = size -> maxSV + 1 <= Zlength symNext ->
    size - 1 - high = pws norm s - nsum s ->
    (forall u, high < u < size -> good (ss_base (cell_nth cells u))) ->
    (forall i, 0 <= i < s -> Znth i symNext = snext0 i) ->
    let '(cells', symNext', high', fast') := lowprob f norm ll s cells symNext high fast in
    Zlength cells' = size /\ Zlength symNext' = Zlength symNext /\
    size - 1 - high' = size - nsum (maxSV + 1) /\
    (forall u, high' < u < size -> good (ss_base (cell_nth cells' u))) /\
    (forall u, 0 <= u <= high' -> cell_nth cells' u = cell_nth cells u) /\
    (forall i, 0 <= i <= maxSV -> Znth i symNext' = snext0 i).
  Proof.
    induction f as [|f IH]; intros s cells symNext high fast Hs Hf HC HN HH HG HS; cbn [lowprob].
    - assert (s = maxSV + 1) by lia. subst s. rewrite SUM in HH. fold size in HH.
      splits; auto; try lia. intros i Hi. apply HS. lia.
    - assert (Hs' : 0 <= s <= maxSV) by lia.
      pose proof (low_step s Hs') as LS. pose proof (low_mono (s + 1) (maxSV + 1) ltac:(lia) ltac:(lia)) as LM.
      rewrite SUM in LM. fold size in LM. pose proof (nsum_nonneg (maxSV + 1) ltac:(lia)) as NN.
      pose proof (low_mono 0 s ltac:(lia) ltac:(lia)) as LM0. change (pws norm 0 - nsum 0) with 0 in LM0.
      destruct (Z.eqb_spec (Znth s norm) (-1)) as [E|E].
      + (* [comment removed for export] *)
        assert (HI : 0 <= high < size) by lia.
        specialize (IH (s + 1) (set_base high s cells) (Zupd s 1 symNext) (high - 1) fast ltac:(lia) ltac:(lia)).
        destruct (lowprob f norm ll (s + 1) (set_base high s cells) (Zupd s 1 symNext) (high - 1) fast) as [[[c' n'] h'] f'].
        destruct IH as (I1 & I2 & I3 & I4 & I5 & I6).
        * unfold Zlength. rewrite set_base_length. exact HC.
        * unfold Zlength. rewrite Zupd_length. exact HN.
        * lia.
        * intros u Hu. destruct (Z.eq_dec u high) as [->|NE].
          -- rewrite cell_nth_set_base_same by lia. split; [lia|]. rewrite E. lia.
          -- rewrite cell_nth_set_base_other by lia. apply HG. lia.
        * intros i Hi. destruct (Z.eq_dec i s) as [->|NE].
          -- rewrite Znth_Zupd_same by (unfold Zlength in *; lia). unfold snext0. rewrite E. reflexivity.
          -- rewrite Znth_Zupd_other by lia. apply HS. lia.
        * splits; auto.
          -- unfold Zlength in *. rewrite Zupd_length in I2. exact I2.
          -- intros u Hu. rewrite I5 by lia. apply cell_nth_set_base_other; lia.
      + specialize (IH (s + 1) cells (Zupd s (Znth s norm mod 2^16) symNext) high (if ll <=? Znth s norm then 0 else fast) ltac:(lia) ltac:(lia)).
        destruct (lowprob f norm ll (s + 1) cells (Zupd s (Znth s norm mod 2^16) symNext) high (if ll <=? Znth s norm then 0 else fast)) as [[[c' n'] h'] f'].
        destruct (Z.eqb_spec (Znth s norm) (-1)) as [E2|_] in LS; [contradiction|].
        destruct IH as (I1 & I2 & I3 & I4 & I5 & I6); auto.
        * unfold Zlength. rewrite Zupd_length. exact HN.
        * lia.
        * intros i Hi. destruct (Z.eq_dec i s) as [->|NE].
          -- rewrite Znth_Zupd_same by (unfold Zlength in *; lia). unfold snext0.
             destruct (Z.eqb_spec (Znth s norm) (-1)); [contradiction|reflexivity].
          -- rewrite Znth_Zupd_other by lia. apply HS. lia.
        * splits; auto. unfold Zlength in *. rewrite Zupd_length in I2. exact I2.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition above_good (high : Z) (cells : list seqsym) : Prop :=
    forall u, 0 <= u < size -> high < u -> good (ss_base (cell_nth cells u)).
  Definition written_good (W : list Z) (cells : list seqsym) : Prop :=
    forall u, In u W -> 0 <= u < size -> good (ss_base (cell_nth cells u)).

  Lemma set_base_good q s cells high W : good s -> Zlength cells = size ->
    above_good high cells -> written_good W cells ->
    Zlength (set_base q s cells) = size /\ above_good high (set_base q s cells) /\ written_good (q :: W) (set_base q s cells).
  Proof.
    intros GS HC HA HW. split; [unfold Zlength; rewrite set_base_length; exact HC|]. split.
    - intros u Hu Hh. destruct (Z.eq_dec q u) as [->|NE].
      + rewrite cell_nth_set_base_same by lia. exact GS.
      + rewrite cell_nth_set_base_other by lia. apply HA; assumption.
    - intros u [->|Hin] Hu.
      + rewrite cell_nth_set_base_same by lia. exact GS.
      + destruct (Z.eq_dec q u) as [->|NE].
        * rewrite cell_nth_set_base_same by lia. exact GS.
        * rewrite cell_nth_set_base_other by lia. apply HW; assumption.
  Qed.

  Lemma written_good_perm W W' cells : (forall u, In u W' -> In u W) -> written_good W cells -> written_good W' cells.
  Proof. intros H HW u Hu. apply HW. apply H. exact Hu. Qed.

  (* [comment removed for export] *)
  Lemma place_n_inv step high s : forall (k : nat) p cells W,
    (k <> 0%nat -> good s) -> Zlength cells = size -> above_good high cells -> written_good W cells ->
    let '(cells', p') := place_n k size step high s p cells in
    Zlength cells' = size /\ above_good high cells' /\ written_good (pos_seq k size step high p ++ W) cells' /\
    p' = pos_iter k size step high p.
  Proof.
    induction k as [|k IH]; intros p cells W GS HC HA HW; cbn [place_n pos_seq pos_iter app].
    - auto.
    - destruct (set_base_good p s cells high W (GS ltac:(discriminate)) HC HA HW) as (C1 & A1 & W1).
      specialize (IH (next_pos size step high p) (set_base p s cells) (p :: W) (fun _ => GS ltac:(discriminate)) C1 A1 W1).
      destruct (place_n k size step high s (next_pos size step high p) (set_base p s cells)) as [c' p'].
      destruct IH as (I1 & I2 & I3 & I4). splits; auto.
      eapply written_good_perm; [|exact I3]. intros u Hu. cbn [In] in Hu. rewrite in_app_iff in *. cbn [In]. tauto.
  Qed.

  Lemma spread_slow_inv step high : forall (f : nat) s p cells W,
    0 <= s -> s + Z.of_nat f = maxSV + 1 ->
    Zlength cells = size -> above_good high cells -> written_good W cells ->
    let '(cells', p') := spread_slow f norm size step high s p cells in
    Zlength cells' = size /\ above_good high cells' /\
    written_good (pos_seq (Z.to_nat (nsum (maxSV + 1) - nsum s)) size step high p ++ W) cells'.
  Proof.
    induction f as [|f IH]; intros s p cells W Hs Hf HC HA HW; cbn [spread_slow].
    - assert (s = maxSV + 1) by lia. subst s. rewrite Z.sub_diag. cbn [Z.to_nat pos_seq app]. auto.
    - assert (Hs' : 0 <= s <= maxSV) by lia.
      pose proof (place_n_inv step high s (Z.to_nat (Znth s norm)) p cells W) as PN.
      destruct (place_n (Z.to_nat (Znth s norm)) size step high s p cells) as [c1 p1].
      destruct PN as (P1 & P2 & P3 & P4); auto.
      { intros NZ. split; [exact Hs'|]. lia. }
      specialize (IH (s + 1) p1 c1 _ ltac:(lia) ltac:(lia) P1 P2 P3).
      destruct (spread_slow f norm size step high (s + 1) p1 c1) as [c2 p2].
      destruct IH as (I1 & I2 & I3). splits; auto.
      eapply written_good_perm; [|exact I3]. intros u Hu.
      pose proof (nsum_S s ltac:(unfold Zlength in *; lia)) as NS. pose proof (nsum_mono (s + 1) (maxSV + 1) ltac:(lia) ltac:(lia)) as NM.
      replace (Z.to_nat (nsum (maxSV + 1) - nsum s)) with (Z.to_nat (Znth s norm) + Z.to_nat (nsum (maxSV + 1) - nsum (s + 1)))%nat in Hu by lia.
      rewrite pos_seq_app in Hu. rewrite <- P4 in Hu. rewrite !in_app_iff in *. tauto.
  Qed.

  (* [comment removed for export] *)
  Lemma Znth_Zupd_eq i j v l : 0 <= i < Zlength l -> 0 <= j -> Znth j (Zupd i v l) = if j =? i then v else Znth j l.
  Proof.
    intros Hi Hj. destruct (Z.eqb_spec j i) as [->|NE]; [apply Znth_Zupd_same; exact Hi|apply Znth_Zupd_other; lia].
  Qed.

  Lemma write8_length l p v : length (write8 l p v) = length l.
  Proof. unfold write8. rewrite !Zupd_length. reflexivity. Qed.

  Lemma Znth_write8 l p v j : 0 <= p -> p + 8 <= Zlength l -> 0 <= j ->
    Znth j (write8 l p v) = if (p <=? j) && (j <? p + 8) then v else Znth j l.
  Proof.
    intros Hp Hl Hj. unfold write8.
    rewrite !Znth_Zupd_eq by (unfold Zlength in *; rewrite ?Zupd_length; lia).
    destruct (Z.eqb_spec j (p + 7)), (Z.eqb_spec j (p + 6)), (Z.eqb_spec j (p + 5)), (Z.eqb_spec j (p + 4)),
             (Z.eqb_spec j (p + 3)), (Z.eqb_spec j (p + 2)), (Z.eqb_spec j (p + 1)), (Z.eqb_spec j p),
             (Z.leb_spec p j), (Z.ltb_spec j (p + 8)); cbn [andb]; try reflexivity; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma lay_more_inv v pos n : forall (f : nat) l i,
    0 <= pos -> 8 <= i -> pos + n + 8 <= Zlength l -> n <= i + 8 * Z.of_nat f - 8 \/ n <= i ->
    (forall j, pos <= j < pos + i -> Znth j l = v) ->
    let l' := lay_more f l pos v i n in
    length l' = length l /\ (forall j, 0 <= j < pos -> Znth j l' = Znth j l) /\ (forall j, pos <= j < pos + n -> Znth j l' = v).
  Proof.
    induction f as [|f IH]; intros l i Hp Hi Hl Hf HV; cbn [lay_more].
    - splits; auto. intros j Hj. apply HV. lia.
    - destruct (Z.ltb_spec i n) as [L|L].
      + specialize (IH (write8 l (pos + i) v) (i + 8) Hp ltac:(lia)).
        destruct IH as (I1 & I2 & I3).
        * unfold Zlength in *. rewrite write8_length. lia.
        * lia.
        * intros j Hj. rewrite Znth_write8 by lia.
          destruct (Z.leb_spec (pos + i) j), (Z.ltb_spec j (pos + i + 8)); cbn [andb]; try reflexivity; apply HV; lia.
        * splits.
          -- rewrite I1. apply write8_length.
          -- intros j Hj. rewrite I2 by lia. rewrite Znth_write8 by lia.
             destruct (Z.leb_spec (pos + i) j), (Z.ltb_spec j (pos + i + 8)); cbn [andb]; try reflexivity; lia.
          -- exact I3.
      + splits; auto. intros j Hj. apply HV. lia.
  Qed.

  Lemma lay_symbols_inv : forall (f : nat) s pos l,
    0 <= s -> s + Z.of_nat f = maxSV + 1 -> (forall i, 0 <= i <= maxSV -> 0 <= Znth i norm) ->
    pos = nsum s -> size + 8 <= Zlength l ->
    (forall j, 0 <= j < pos -> good (Znth j l)) ->
    let '(l', pos') := lay_symbols f norm s pos l in
    length l' = length l /\ pos' = nsum (maxSV + 1) /\ (forall j, 0 <= j < pos' -> good (Znth j l')).
  Proof.
    induction f as [|f IH]; intros s pos l Hs Hf NN HP HL HG; cbn [lay_symbols].
    - assert (s = maxSV + 1) by lia. subst s. auto.
    - assert (Hs' : 0 <= s <= maxSV) by lia. set (n := Znth s norm).
      pose proof (NN s Hs') as N0. fold n in N0.
      pose proof (nsum_S s ltac:(unfold Zlength in *; lia)) as NS. fold n in NS. rewrite Z.max_r in NS by lia.
      pose proof (nsum_mono (s + 1) (maxSV + 1) ltac:(lia) ltac:(lia)) as NM.
      pose proof (nsum_nonneg s ltac:(lia)) as NP.
      assert (TOT : nsum (maxSV + 1) <= size).
      { pose proof (low_mono 0 (maxSV + 1) ltac:(lia) ltac:(lia)) as LM. change (pws norm 0 - nsum 0) with 0 in LM.
        rewrite SUM in LM. fold size in LM. lia. }
      pose proof (lay_more_inv s pos n (Z.to_nat (n / 8 + 1)) (write8 l pos s) 8 ltac:(lia) ltac:(lia)) as LM.
      destruct LM as (L1 & L2 & L3).
      { unfold Zlength in *. rewrite write8_length. lia. }
      { left. pose proof (Z.div_mod n 8 ltac:(lia)). pose proof (Z.mod_pos_bound n 8 ltac:(lia)).
        assert (0 <= n / 8) by (apply Z.div_pos; lia). lia. }
      { intros j Hj. rewrite Znth_write8 by lia.
        destruct (Z.leb_spec pos j), (Z.ltb_spec j (pos + 8)); cbn [andb]; try reflexivity; lia. }
      specialize (IH (s + 1) (pos + n) (lay_more (Z.to_nat (n / 8 + 1)) (write8 l pos s) pos s 8 n) ltac:(lia) ltac:(lia) NN ltac:(lia)).
      destruct (lay_symbols f norm (s + 1) (pos + n) (lay_more (Z.to_nat (n / 8 + 1)) (write8 l pos s) pos s 8 n)) as [l' pos'].
      destruct IH as (I1 & I2 & I3).
      { unfold Zlength in *. rewrite L1, write8_length. lia. }
      { intros j Hj. destruct (Z.lt_ge_cases j pos) as [B|B].
        - rewrite L2 by lia. rewrite Znth_write8 by lia.
          destruct (Z.leb_spec pos j), (Z.ltb_spec j (pos + 8)); cbn [andb]; try lia; apply HG; lia.
        - rewrite L3 by lia. split; [exact Hs'|]. fold n. lia. }
      splits; auto. rewrite I1, L1. apply write8_length.
  Qed.

  Lemma next_pos_nohigh step p : next_pos size step (size - 1) p = (p + step) mod size.
  Proof.
    unfold next_pos. pose proof size_range as SR. destruct (Z.to_nat size) as [|f] eqn:E; [lia|]. cbn [skip_low].
    pose proof (Z.mod_pos_bound (p + step) size ltac:(lia)). destruct (Z.ltb_spec (size - 1) ((p + step) mod size)); [lia|reflexivity].
  Qed.

  Lemma place_fast_inv step spread : (forall j, 0 <= j < size -> good (Znth j spread)) ->
    forall (f : nat) i p cells W,
    0 <= i -> 2 * i + 2 * Z.of_nat f = size -> 0 <= p < size ->
    Zlength cells = size -> above_good (size - 1) cells -> written_good W cells ->
    let '(cells', _) := place_fast f size step spread (2 * i) p cells in
    Zlength cells' = size /\ written_good (pos_seq (2 * f) size step (size - 1) p ++ W) cells'.
  Proof.
    intros SG. induction f as [|f IH]; intros i p cells W Hi Hf Hp HC HA HW; cbn [place_fast].
    - cbn [Nat.mul pos_seq app]. auto.
    - replace (2 * S f)%nat with (S (S (2 * f))) by lia. cbn [pos_seq]. rewrite !next_pos_nohigh.
      pose proof size_range as SR.
      rewrite (Z.mod_small p size) by lia.
      destruct (set_base_good p (Znth (2 * i) spread) cells (size - 1) W (SG (2 * i) ltac:(lia)) HC HA HW) as (C1 & A1 & W1).
      destruct (set_base_good ((p + step) mod size) (Znth (2 * i + 1) spread) _ (size - 1) _ (SG (2 * i + 1) ltac:(lia)) C1 A1 W1) as (C2 & A2 & W2).
      specialize (IH (i + 1) ((p + 2 * step) mod size) _ _ ltac:(lia) ltac:(lia) (Z.mod_pos_bound (p + 2 * step) size ltac:(lia)) C2 A2 W2).
      replace (2 * (i + 1)) with (2 * i + 2) in IH by lia.
      destruct (place_fast f size step spread (2 * i + 2) ((p + 2 * step) mod size) _) as [c' p'].
      destruct IH as (I1 & I2). split; [exact I1|].
      eapply written_good_perm; [|exact I2]. intros u Hu. cbn [In app] in Hu.
      replace (((p + step) mod size + step) mod size) with ((p + 2 * step) mod size) in Hu
        by (rewrite Z.add_mod_idemp_l by lia; f_equal; lia).
      rewrite in_app_iff in *. cbn [In]. tauto.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Variable k : seq_kind.
  Hypothesis MSVK : maxSV <= kind_max k.

  Lemma build_one_ok symbol ns : good symbol -> 1 <= ns < 2 * size ->
    cell_ok k tl (build_one tl (kind_base k) (kind_bits k) symbol ns).
  Proof.
    intros (GS & _) NS. pose proof size_range as SR. unfold size in *.
    set (lg := Z.log2 ns).
    assert (LG0 : 0 <= lg) by apply Z.log2_nonneg.
    assert (LGT : lg <= tl).
    { assert (lg < tl + 1); [|lia]. apply Z.log2_lt_pow2; [lia|]. rewrite Z.pow_add_r by lia. change (2^1) with 2. lia. }
    pose proof (Z.log2_spec ns ltac:(lia)) as SP. fold lg in SP. rewrite Z.pow_succ_r in SP by lia.
    assert (PW : 2^lg * 2^(tl - lg) = 2^tl) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    assert (P0 : 0 < 2^(tl - lg)) by (apply Z.pow_pos_nonneg; lia).
    unfold build_one. fold lg. cbv zeta.
    rewrite (Z.mod_small (tl - lg) 256) by lia.
    assert (B : 0 <= ns * 2^(tl - lg) - 2^tl /\ ns * 2^(tl - lg) - 2^tl + 2^(tl - lg) <= 2^tl) by nia.
    rewrite (Z.mod_small (ns * 2^(tl - lg) - 2^tl) (2^16)) by (change (2^16) with 65536; lia).
    unfold cell_ok; cbn [ss_nbBits ss_next ss_nbAdd ss_base]. splits; try lia.
    exists symbol. splits; auto; lia.
  Qed.

  Lemma build_cells_inv : forall (f : nat) u cells symNext,
    0 <= u -> u + Z.of_nat f = size ->
    Zlength cells = size -> maxSV + 1 <= Zlength symNext ->
    (forall v, u <= v < size -> good (ss_base (cell_nth cells v))) ->
    (forall v, 0 <= v < u -> cell_ok k tl (cell_nth cells v)) ->
    (forall s, good s -> 1 <= Znth s symNext <= snext0 s + u) ->
    let '(cells', _) := build_cells f tl (kind_base k) (kind_bits k) u cells symNext in
    Zlength cells' = size /\ (forall v, 0 <= v < size -> cell_ok k tl (cell_nth cells' v)).
  Proof.
    induction f as [|f IH]; intros u cells symNext Hu Hf HC HN HG HK HS; cbn [build_cells].
    - assert (u = size) by lia. subst u. auto.
    - pose proof size_range as SR.
      set (symbol := ss_base (cell_nth cells u)). set (ns := Znth symbol symNext).
      assert (GSY : good symbol) by (apply HG; lia).
      pose proof (HS symbol GSY) as NSR. fold ns in NSR. pose proof (snext0_good symbol GSY) as S0.
      assert (NS2 : 1 <= ns < 2 * size) by lia.
      specialize (IH (u + 1) (set_cell u (build_one tl (kind_base k) (kind_bits k) symbol ns) cells)
                     (Zupd symbol ((ns + 1) mod 2^16) symNext) ltac:(lia) ltac:(lia)).
      destruct (build_cells f tl (kind_base k) (kind_bits k) (u + 1) _ _) as [c' n'].
      apply IH.
      + unfold Zlength. rewrite set_cell_length. exact HC.
      + unfold Zlength. rewrite Zupd_length. exact HN.
      + intros v Hv. rewrite cell_nth_set_cell_other by lia. apply HG. lia.
      + intros v Hv. destruct (Z.eq_dec v u) as [->|NE].
        * rewrite cell_nth_set_cell_same by lia. apply build_one_ok; assumption.
        * rewrite cell_nth_set_cell_other by lia. apply HK. lia.
      + intros s GS. destruct GSY as (GY & _). pose proof GS as (GS1 & _).
        rewrite Znth_Zupd_eq by (unfold Zlength in *; lia).
        destruct (Z.eqb_spec s symbol) as [->|NE].
        * rewrite Z.mod_small by (change (2^16) with 65536; lia). fold ns. lia.
        * pose proof (HS s GS). lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Hypothesis TLK : tl <= kind_maxLog k.

  Theorem build_fse_table_ok cells0 symNext0 spread0 :
    Zlength cells0 = size -> maxSV + 1 <= Zlength symNext0 -> size + 8 <= Zlength spread0 ->
    seq_table_ok k (fst (fst (build_fse_table_k k norm maxSV tl cells0 symNext0 spread0))).
  Proof.
    intros HC HN HSP. pose proof size_range as SR.
    unfold build_fse_table_k, build_fse_table. fold size. cbv zeta.
    pose proof (lowprob_inv (2^(tl - 1)) (Z.to_nat (maxSV + 1)) 0 cells0 symNext0 (size - 1) 1 ltac:(lia) ltac:(lia) HC HN) as P1.
    destruct (lowprob (Z.to_nat (maxSV + 1)) norm (2^(tl - 1)) 0 cells0 symNext0 (size - 1) 1) as [[[cells1 symNext1] high] fast].
    destruct P1 as (C1 & N1 & H1 & G1 & _ & S1).
    { change (pws norm 0 - nsum 0) with 0. lia. }
    { intros u Hu. lia. }
    { intros i Hi. lia. }
    pose proof (nsum_nonneg (maxSV + 1) ltac:(lia)) as NN.
    assert (TOT : nsum (maxSV + 1) <= size).
    { pose proof (low_mono 0 (maxSV + 1) ltac:(lia) ltac:(lia)) as LM. change (pws norm 0 - nsum 0) with 0 in LM.
      rewrite SUM in LM. fold size in LM. lia. }
    assert (HH : high = nsum (maxSV + 1) - 1) by lia.
    assert (AG1 : above_good high cells1) by (intros u Hu Hh; apply G1; lia).
    (* [comment removed for export] *)
    assert (P2 : exists cells2 spread2,
              (if high =? size - 1
               then let '(spread1, _) := lay_symbols (Z.to_nat (maxSV + 1)) norm 0 0 spread0 in
                    (fst (place_fast (Z.to_nat (size / 2)) size (fse_tablestep size) spread1 0 0 cells1), spread1)
               else (fst (spread_slow (Z.to_nat (maxSV + 1)) norm size (fse_tablestep size) high 0 0 cells1), spread0))
              = (cells2, spread2) /\ Zlength cells2 = size /\ forall v, 0 <= v < size -> good (ss_base (cell_nth cells2 v))).
    { destruct (Z.eqb_spec high (size - 1)) as [EH|NH].
      - (* [comment removed for export] *)
        assert (NOLOW : forall i, 0 <= i <= maxSV -> 0 <= Znth i norm).
        { intros i Hi. pose proof (GE i Hi). destruct (Z.eq_dec (Znth i norm) (-1)) as [E|E]; [|lia]. exfalso.
          pose proof (low_step i Hi) as LS. rewrite E in LS. change (-1 =? -1) with true in LS. cbv iota in LS.
          pose proof (low_mono 0 i ltac:(lia) ltac:(lia)) as L0. change (pws norm 0 - nsum 0) with 0 in L0.
          pose proof (low_mono (i + 1) (maxSV + 1) ltac:(lia) ltac:(lia)) as L1. rewrite SUM in L1. fold size in L1. lia. }
        pose proof (lay_symbols_inv (Z.to_nat (maxSV + 1)) 0 0 spread0 ltac:(lia) ltac:(lia) NOLOW eq_refl HSP ltac:(intros; lia)) as LS.
        destruct (lay_symbols (Z.to_nat (maxSV + 1)) norm 0 0 spread0) as [spread1 pos1].
        destruct LS as (_ & PE & SG). rewrite PE in SG. replace (nsum (maxSV + 1)) with size in SG by lia.
        assert (EVEN : 2 * (size / 2) = size).
        { assert (E2 : size = 2^(tl - 1) * 2).
          { unfold size. replace tl with (Z.succ (tl - 1)) at 1 by lia. rewrite Z.pow_succ_r by lia. lia. }
          rewrite E2, Z.div_mul by lia. lia. }
        pose proof (place_fast_inv (fse_tablestep size) spread1 SG (Z.to_nat (size / 2)) 0 0 cells1 [] ltac:(lia) ltac:(lia) ltac:(lia) C1) as PF.
        change (2 * 0) with 0 in PF.
        destruct (place_fast (Z.to_nat (size / 2)) size (fse_tablestep size) spread1 0 0 cells1) as [cells2 p2].
        destruct PF as (C2 & W2); [rewrite <- EH; exact AG1|intros u []|].
        exists cells2, spread1. split; [reflexivity|]. split; [exact C2|].
        intros v Hv. apply W2; [|exact Hv]. rewrite app_nil_r.
        replace (2 * Z.to_nat (size / 2))%nat with (Z.to_nat (size - 1 + 1)) by lia.
        apply (cover_all tl (size - 1) v); unfold size in *; lia.
      - pose proof (spread_slow_inv (fse_tablestep size) high (Z.to_nat (maxSV + 1)) 0 0 cells1 [] ltac:(lia) ltac:(lia) C1 AG1 ltac:(intros u [])) as SS.
        destruct (spread_slow (Z.to_nat (maxSV + 1)) norm size (fse_tablestep size) high 0 0 cells1) as [cells2 p2].
        destruct SS as (C2 & A2 & W2). exists cells2, spread0. split; [reflexivity|]. split; [exact C2|].
        intros v Hv. destruct (Z.le_gt_cases v high) as [LE|GT]; [|apply A2; lia].
        apply W2; [|exact Hv]. rewrite app_nil_r. change (nsum 0) with 0. rewrite Z.sub_0_r.
        replace (nsum (maxSV + 1)) with (high + 1) by lia.
        apply (cover_all tl high v); unfold size in *; lia. }
    destruct P2 as (cells2 & spread2 & E2 & C2 & G2). rewrite E2.
    pose proof (build_cells_inv (Z.to_nat size) 0 cells2 symNext1 ltac:(lia) ltac:(lia) C2 ltac:(lia)) as P3.
    destruct (build_cells (Z.to_nat size) tl (kind_base k) (kind_bits k) 0 cells2 symNext1) as [cells3 symNext3].
    destruct P3 as (C3 & K3).
    { intros v Hv. apply G2. lia. }
    { intros v Hv. lia. }
    { intros s GS. rewrite S1 by (destruct GS; lia). pose proof (snext0_good s GS). lia. }
    cbn [fst]. unfold seq_table_ok; cbn [st_log st_cells]. split; [lia|]. split; [exact C3|].
    apply Forall_forall. intros c Hc. apply In_nth with (d := ss0) in Hc. destruct Hc as (n & Hn & <-).
    specialize (K3 (Z.of_nat n) ltac:(unfold Zlength in C3; lia)). unfold cell_nth in K3. rewrite Nat2Z.id in K3. exact K3.
  Qed.
End Build.

(* [comment removed for export] *)
Corollary build_fse_table_ok_wsum k norm maxSV tl cells0 symNext0 spread0 :
  5 <= tl <= kind_maxLog k -> 0 <= maxSV <= kind_max k -> maxSV + 1 <= Zlength norm ->
  (forall i, 0 <= i <= maxSV -> -1 <= Znth i norm) ->
  wsum (firstn (Z.to_nat (maxSV + 1)) norm) = 2^tl ->
  Zlength cells0 = 2^tl -> maxSV + 1 <= Zlength symNext0 -> 2^tl + 8 <= Zlength spread0 ->
  seq_table_ok k (fst (fst (build_fse_table_k k norm maxSV tl cells0 symNext0 spread0))).
Proof.
  intros TL MSV LEN GE SUM HC HN HS.
  apply build_fse_table_ok; auto; try (destruct k; cbn [kind_maxLog kind_max] in *; lia).
Qed.
