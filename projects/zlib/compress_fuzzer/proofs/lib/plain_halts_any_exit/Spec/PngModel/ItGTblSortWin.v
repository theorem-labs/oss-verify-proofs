(** * SortWin — the [inflate_table] PROLOGUE facts the root-region COVERAGE
      theorem needs: sorted-work placement, the offsets layout, and the
      max/min scans.

    SPEC-SIDE ONLY.  Imports [Spec.PngModel.Base] and [Spec.PngModel.Inftrees]
    and nothing else; in particular it never mentions [ItModel], so a chain
    that consumes these lemmas stays independent of the other formalisation.

    Shape of the development, following [pbf/ItWKSorted.v] (which proves the
    same placement theorem for [ItModel.it_sort], whose recursion applies the
    last symbol AFTER the recursive call).  The spec's [it_count]/[it_sort]
    are TAIL-recursive and carry the symbol index, so the whole file is built
    on SNOC lemmas ([spec_count_snoc], [spec_sort_snoc]) that convert the
    tail recursion into the template's shape.

    TRAPS, recorded here because a consumer will hit them:

    - Every peel lemma whose statement contains [let l := ... in] tests the
      BOUND VARIABLE, not the body: [destruct (Z.eqb (lens i) 0)] leaves the
      [if] unresolved and the branch's [reflexivity] then fails.  [cbv zeta]
      before any such destruct.  All the derived peels below
      ([sort_fst_snoc0_zero] and friends) are stated let-free and if-free
      precisely so no consumer has to know this.
    - A nat numeral IS a constructor application, so a lemma keyed on [S k]
      fires on the literal [1] (= [S O]).  Give the arguments explicitly
      rather than debugging occurrence order.
    - [it_findmax]/[it_findmin] BOTH need a fuel-sufficiency premise for their
      zero-above / zero-below halves; see the two [*_as_stated_false] lemmas.
*)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Base Inftrees.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Open Scope Z_scope.

(** [Z.of_nat] on the three literals this file needs.  [lia] is not asked to
    do this: it treats [Z.of_nat 14] as an atom in some positions. *)
Lemma zon14 : Z.of_nat 14%nat = 14. Proof. reflexivity. Qed.
Lemma zon15 : Z.of_nat 15%nat = 15. Proof. reflexivity. Qed.
Lemma zon16 : Z.of_nat 16%nat = 16. Proof. reflexivity. Qed.

(** ** The three objects under study — verbatim mirrors of [it_pre] :378-419 *)

Definition sw_cnt (lens : zarr) (codes : Z) : zarr := it_count (Z.to_nat codes) 0 lens zzero.
Definition sw_offs (cnt : zarr) : zarr := it_offs 14%nat 1 cnt (zset zzero 1 0).
Definition sw_work (lens : zarr) (codes : Z) : zarr :=
  snd (it_sort (Z.to_nat codes) 0 lens (sw_offs (sw_cnt lens codes)) zzero).

(** ** Peeling the tail recursions from the BACK *)

Lemma spec_sort_step : forall n i lens offs work,
  it_sort (S n) i lens offs work
  = (let l := lens i in
     if Z.eqb l 0 then it_sort n (i + 1) lens offs work
     else it_sort n (i + 1) lens (zset offs l (offs l + 1)) (zset work (offs l) i)).
Proof. intros. reflexivity. Qed.

Lemma spec_sort_snoc : forall n i lens offs work,
  it_sort (S n) i lens offs work
  = (let l := lens (i + Z.of_nat n) in
     if Z.eqb l 0 then it_sort n i lens offs work
     else (zset (fst (it_sort n i lens offs work)) l
                (fst (it_sort n i lens offs work) l + 1),
           zset (snd (it_sort n i lens offs work))
                (fst (it_sort n i lens offs work) l)
                (i + Z.of_nat n))).
Proof.
  induction n as [|k IH]; intros i lens offs work.
  - rewrite spec_sort_step. cbn [it_sort fst snd]. cbv zeta.
    rewrite Z.add_0_r. destruct (Z.eqb (lens i) 0); reflexivity.
  - rewrite (spec_sort_step (S k) i lens offs work).
    rewrite (spec_sort_step k i lens offs work).
    cbv zeta.
    destruct (Z.eqb (lens i) 0) eqn:E0.
    + rewrite (IH (i + 1) lens offs work).
      replace (i + 1 + Z.of_nat k) with (i + Z.of_nat (S k)) by lia.
      reflexivity.
    + rewrite (IH (i + 1) lens _ _).
      replace (i + 1 + Z.of_nat k) with (i + Z.of_nat (S k)) by lia. reflexivity.
Qed.

Lemma spec_count_step : forall n i lens cnt,
  it_count (S n) i lens cnt
  = it_count n (i + 1) lens (zset cnt (lens i) (cnt (lens i) + 1)).
Proof. intros. reflexivity. Qed.

Lemma spec_count_snoc : forall n i lens cnt,
  it_count (S n) i lens cnt
  = (let l := lens (i + Z.of_nat n) in
     zset (it_count n i lens cnt) l (it_count n i lens cnt l + 1)).
Proof.
  induction n as [|k IH]; intros i lens cnt.
  - cbn [it_count]. cbv zeta. rewrite Z.add_0_r. reflexivity.
  - rewrite (spec_count_step (S k) i lens cnt).
    rewrite (spec_count_step k i lens cnt).
    cbv zeta. rewrite (IH (i + 1) lens (zset cnt (lens i) (cnt (lens i) + 1))).
    replace (i + 1 + Z.of_nat k) with (i + Z.of_nat (S k)) by lia. reflexivity.
Qed.

(** The peels the rest of the file uses: START INDEX 0, let-free and if-free,
    so that neither the [cbv zeta] trap nor an unresolved [if] can reach a
    consumer. *)

Lemma count_snoc0 : forall n lens cnt,
  it_count (S n) 0 lens cnt
  = zset (it_count n 0 lens cnt) (lens (Z.of_nat n))
         (it_count n 0 lens cnt (lens (Z.of_nat n)) + 1).
Proof.
  intros n lens cnt. rewrite (spec_count_snoc n 0 lens cnt). cbv zeta.
  rewrite Z.add_0_l. reflexivity.
Qed.

Lemma count_hit0 : forall n lens cnt,
  it_count (S n) 0 lens cnt (lens (Z.of_nat n))
  = it_count n 0 lens cnt (lens (Z.of_nat n)) + 1.
Proof. intros n lens cnt. rewrite (count_snoc0 n lens cnt). apply zset_same. Qed.

Lemma count_miss0 : forall n lens cnt l,
  l <> lens (Z.of_nat n) ->
  it_count (S n) 0 lens cnt l = it_count n 0 lens cnt l.
Proof.
  intros n lens cnt l H. rewrite (count_snoc0 n lens cnt). now apply zset_other.
Qed.

Lemma sort_snoc0 : forall n lens offs work,
  it_sort (S n) 0 lens offs work
  = (let l := lens (Z.of_nat n) in
     if Z.eqb l 0 then it_sort n 0 lens offs work
     else (zset (fst (it_sort n 0 lens offs work)) l
                (fst (it_sort n 0 lens offs work) l + 1),
           zset (snd (it_sort n 0 lens offs work))
                (fst (it_sort n 0 lens offs work) l)
                (Z.of_nat n))).
Proof.
  intros n lens offs work. rewrite (spec_sort_snoc n 0 lens offs work).
  cbv zeta. rewrite Z.add_0_l. reflexivity.
Qed.

Lemma sort_fst_snoc0_zero : forall n lens offs work,
  lens (Z.of_nat n) = 0 ->
  fst (it_sort (S n) 0 lens offs work) = fst (it_sort n 0 lens offs work).
Proof.
  intros n lens offs work H.
  rewrite (sort_snoc0 n lens offs work). cbv zeta. rewrite H. reflexivity.
Qed.

Lemma sort_fst_snoc0_nz : forall n lens offs work,
  lens (Z.of_nat n) <> 0 ->
  fst (it_sort (S n) 0 lens offs work)
  = zset (fst (it_sort n 0 lens offs work)) (lens (Z.of_nat n))
         (fst (it_sort n 0 lens offs work) (lens (Z.of_nat n)) + 1).
Proof.
  intros n lens offs work H.
  rewrite (sort_snoc0 n lens offs work). cbv zeta.
  apply Z.eqb_neq in H as ->. reflexivity.
Qed.

Lemma sort_snd_snoc0_zero : forall n lens offs work,
  lens (Z.of_nat n) = 0 ->
  snd (it_sort (S n) 0 lens offs work) = snd (it_sort n 0 lens offs work).
Proof.
  intros n lens offs work H.
  rewrite (sort_snoc0 n lens offs work). cbv zeta. rewrite H. reflexivity.
Qed.

Lemma sort_snd_snoc0_nz : forall n lens offs work,
  lens (Z.of_nat n) <> 0 ->
  snd (it_sort (S n) 0 lens offs work)
  = zset (snd (it_sort n 0 lens offs work))
         (fst (it_sort n 0 lens offs work) (lens (Z.of_nat n)))
         (Z.of_nat n).
Proof.
  intros n lens offs work H.
  rewrite (sort_snoc0 n lens offs work). cbv zeta.
  apply Z.eqb_neq in H as ->. reflexivity.
Qed.

(** ** LEMMA 1 — the histogram is nonnegative *)

Lemma count_nonneg_gen : forall n i lens cnt,
  (forall l, 0 <= cnt l) -> forall l, 0 <= it_count n i lens cnt l.
Proof.
  induction n as [|k IH]; intros i lens cnt Hc l; cbn [it_count].
  - apply Hc.
  - apply IH. intros l'. unfold zset. destruct (Z.eqb l' (lens i)).
    + specialize (Hc (lens i)). lia.
    + apply Hc.
Qed.

Lemma count_zzero_nonneg : forall n i lens l, 0 <= it_count n i lens zzero l.
Proof.
  intros n i lens l. apply count_nonneg_gen.
  intros l'. unfold zzero, zconst. lia.
Qed.

Lemma sw_cnt_nonneg : forall lens codes l, 0 <= sw_cnt lens codes l.
Proof. intros lens codes l. unfold sw_cnt. apply count_zzero_nonneg. Qed.

(** The prefix histogram never exceeds the full one. *)
Lemma count_mono : forall m n i lens cnt l,
  (n <= m)%nat -> it_count n i lens cnt l <= it_count m i lens cnt l.
Proof.
  induction m as [|k IH]; intros n i lens cnt l H.
  - replace n with O by lia. lia.
  - destruct (Nat.eq_dec n (S k)) as [->|Hne]; [lia|].
    assert (Hk : (n <= k)%nat) by lia.
    specialize (IH n i lens cnt l Hk).
    rewrite (spec_count_snoc k i lens cnt). cbv zeta.
    destruct (Z.eq_dec l (lens (i + Z.of_nat k))) as [->|Hd].
    + rewrite zset_same. lia.
    + rewrite zset_other by exact Hd. exact IH.
Qed.

(** ** LEMMAS 2-4 — the cumulative offsets layout *)

(** Indices at or below the scan's start are never written. *)
Lemma it_offs_below : forall n len cnt offs j,
  j <= len -> it_offs n len cnt offs j = offs j.
Proof.
  induction n as [|k IH]; intros len cnt offs j Hj; cbn [it_offs]; [reflexivity|].
  rewrite IH by lia. apply zset_other. lia.
Qed.

(** The step relation, at an arbitrary start and fuel. *)
Lemma it_offs_step_gen : forall n len cnt offs j,
  len < j <= len + Z.of_nat n ->
  it_offs n len cnt offs j = it_offs n len cnt offs (j - 1) + cnt (j - 1).
Proof.
  induction n as [|k IH]; intros len cnt offs j Hj.
  - cbn [Z.of_nat] in Hj. lia.
  - cbn [it_offs].
    destruct (Z.eq_dec j (len + 1)) as [->|Hne].
    + rewrite it_offs_below by lia. rewrite it_offs_below by lia.
      replace (len + 1 - 1) with len by lia.
      rewrite zset_same. rewrite zset_other by lia. reflexivity.
    + rewrite (IH (len + 1) cnt (zset offs (len + 1) (offs len + cnt len)) j)
        by (rewrite Nat2Z.inj_succ in Hj; lia).
      reflexivity.
Qed.

Lemma sw_offs_1 : forall cnt, sw_offs cnt 1 = 0.
Proof.
  intros cnt. unfold sw_offs. rewrite it_offs_below by lia. apply zset_same.
Qed.

Lemma sw_offs_step : forall cnt l,
  1 <= l <= 14 -> sw_offs cnt (l + 1) = sw_offs cnt l + cnt l.
Proof.
  intros cnt l Hl. unfold sw_offs.
  rewrite it_offs_step_gen by (rewrite zon14; lia).
  replace (l + 1 - 1) with l by lia. reflexivity.
Qed.

(** Same fact with the successor index supplied as a separate equation, so a
    caller can instantiate it at LITERAL indices ([sw_offs cnt 2 = ...]) and
    not at [sw_offs cnt (1 + 1)], which is a different [lia] atom. *)
Lemma sw_offs_step' : forall cnt a b,
  1 <= a <= 14 -> b = a + 1 -> sw_offs cnt b = sw_offs cnt a + cnt a.
Proof. intros cnt a b Ha ->. apply sw_offs_step. exact Ha. Qed.

(** NOTE the shape change: [1 <= a <= b <= 15] does NOT parse in Rocq (the
    chained-comparison notations are 3-ary only, so the 4-chain is read as
    [(1 <= a <= b) <= 15] and is a type error).  Split into two premises. *)
Lemma sw_offs_mono : forall cnt a b,
  (forall i, 1 <= i <= 15 -> 0 <= cnt i) ->
  1 <= a <= b -> b <= 15 -> sw_offs cnt a <= sw_offs cnt b.
Proof.
  intros cnt a b Hnn Hab Hb.
  remember (Z.to_nat (b - a)) as d eqn:Hd. revert a b Hab Hb Hd.
  induction d as [|d IH]; intros a b Hab Hb Hd.
  - replace b with a by lia. lia.
  - specialize (IH (a + 1) b ltac:(lia) ltac:(lia) ltac:(lia)).
    pose proof (sw_offs_step cnt a ltac:(lia)) as Hs.
    specialize (Hnn a ltac:(lia)). lia.
Qed.

(** ** The running offsets during the sort *)

Lemma sort_offs_advance0 : forall n lens offs0 wk0 l,
  l <> 0 ->
  fst (it_sort n 0 lens offs0 wk0) l = offs0 l + it_count n 0 lens zzero l.
Proof.
  intros n lens offs0 wk0 l Hl.
  induction n as [|k IH].
  - cbn [it_sort it_count fst]. unfold zzero, zconst. lia.
  - destruct (Z.eq_dec (lens (Z.of_nat k)) 0) as [Hz|Hnz].
    + rewrite (sort_fst_snoc0_zero k lens offs0 wk0 Hz).
      rewrite IH. rewrite (count_miss0 k lens zzero l) by (rewrite Hz; exact Hl).
      reflexivity.
    + rewrite (sort_fst_snoc0_nz k lens offs0 wk0 Hnz).
      destruct (Z.eq_dec l (lens (Z.of_nat k))) as [->|Hne].
      * rewrite zset_same. rewrite IH. rewrite (count_hit0 k lens zzero). lia.
      * rewrite zset_other by exact Hne. rewrite IH.
        rewrite (count_miss0 k lens zzero l) by exact Hne. reflexivity.
Qed.

(** ** LEMMA 5 — the placement theorem

    Symbols of length [l] occupy exactly the work slots
    [[sw_offs cnt l, sw_offs cnt l + sw_cnt lens codes l)].

    Stated at an arbitrary PREFIX [n] of the sort (the prefix count is the
    window WIDTH, the FULL count's layout supplies the offsets), which is what
    makes the induction go through: the windows are disjoint only because
    [sw_offs] is the cumulative layout of the FULL counts.

    [lens i <= 15] is load-bearing, not decoration, and this is STRONGER than
    the template needed.  The template's [it_offs] is monotone at every index,
    so [0 <= lens i] sufficed there.  Here [sw_offs] has fuel 14: it is only
    a cumulative layout on [1..15], so the disjointness argument needs the
    placed length to be INSIDE that range, i.e. [lens i <= 15]. *)
Lemma places_prefix : forall lens codes cnt n s l,
  (forall i, 0 <= i < codes -> 0 <= lens i <= 15) ->
  cnt = sw_cnt lens codes ->
  (n <= Z.to_nat codes)%nat ->
  1 <= l <= 15 ->
  sw_offs cnt l <= s < sw_offs cnt l + it_count n 0 lens zzero l ->
  lens (snd (it_sort n 0 lens (sw_offs cnt) zzero) s) = l.
Proof.
  intros lens codes cnt n s l Hlens Hcnt Hn Hl Hs.
  assert (Hnn : forall i, 1 <= i <= 15 -> 0 <= cnt i)
    by (intros i _; rewrite Hcnt; apply sw_cnt_nonneg).
  revert Hn Hs. induction n as [|k IH]; intros Hn Hs.
  - cbn [it_count] in Hs. unfold zzero, zconst in Hs. lia.
  - assert (Hkr : 0 <= Z.of_nat k < codes) by lia.
    assert (Hoff : forall l', l' <> 0 ->
              fst (it_sort k 0 lens (sw_offs cnt) zzero) l'
              = sw_offs cnt l' + it_count k 0 lens zzero l')
      by (intros l' Hl'; apply sort_offs_advance0; exact Hl').
    destruct (Z.eq_dec (lens (Z.of_nat k)) 0) as [Hz|Hnz].
    + rewrite (sort_snd_snoc0_zero k lens (sw_offs cnt) zzero Hz).
      apply IH; [lia|].
      rewrite (count_miss0 k lens zzero l) in Hs by (rewrite Hz; lia). exact Hs.
    + rewrite (sort_snd_snoc0_nz k lens (sw_offs cnt) zzero Hnz).
      assert (Hl'r : 1 <= lens (Z.of_nat k) <= 15)
        by (specialize (Hlens (Z.of_nat k) Hkr); lia).
      destruct (Z.eq_dec l (lens (Z.of_nat k))) as [Heq|Hne].
      * assert (Hc2 : it_count (S k) 0 lens zzero l
                      = it_count k 0 lens zzero l + 1)
          by (rewrite Heq; apply (count_hit0 k lens zzero)).
        rewrite Hc2 in Hs.
        destruct (Z.eq_dec s (fst (it_sort k 0 lens (sw_offs cnt) zzero)
                                  (lens (Z.of_nat k)))) as [->|Hsne].
        -- rewrite zset_same. symmetry. exact Heq.
        -- rewrite zset_other by exact Hsne.
           apply IH; [lia|].
           rewrite Hoff in Hsne by exact Hnz.
           rewrite <- Heq in Hsne. lia.
      * rewrite (count_miss0 k lens zzero l) in Hs by exact Hne.
        assert (Hd : s <> fst (it_sort k 0 lens (sw_offs cnt) zzero)
                            (lens (Z.of_nat k))).
        { rewrite Hoff by exact Hnz.
          assert (Hlt : it_count k 0 lens zzero (lens (Z.of_nat k))
                        < cnt (lens (Z.of_nat k))).
          { rewrite Hcnt. unfold sw_cnt.
            pose proof (count_mono (Z.to_nat codes) (S k) 0 lens zzero
                          (lens (Z.of_nat k)) Hn) as Hm.
            rewrite (count_hit0 k lens zzero) in Hm. lia. }
          assert (Hle : it_count k 0 lens zzero l <= cnt l)
            by (rewrite Hcnt; unfold sw_cnt; apply count_mono; lia).
          pose proof (count_zzero_nonneg k 0 lens (lens (Z.of_nat k))) as Hcnn.
          destruct (Z.lt_ge_cases l (lens (Z.of_nat k))) as [Hlt2|Hge].
          - pose proof (sw_offs_mono cnt (l + 1) (lens (Z.of_nat k))
                          Hnn ltac:(lia) ltac:(lia)) as Hmono.
            rewrite sw_offs_step in Hmono by lia. lia.
          - pose proof (sw_offs_mono cnt (lens (Z.of_nat k) + 1) l
                          Hnn ltac:(lia) ltac:(lia)) as Hmono.
            rewrite sw_offs_step in Hmono by lia. lia. }
        rewrite zset_other by exact Hd. apply IH; [lia|]. exact Hs.
Qed.

Theorem sw_places : forall lens codes l s,
  0 <= codes ->
  (forall i, 0 <= i < codes -> 0 <= lens i <= 15) ->
  1 <= l <= 15 ->
  sw_offs (sw_cnt lens codes) l <= s
    < sw_offs (sw_cnt lens codes) l + sw_cnt lens codes l ->
  lens (sw_work lens codes s) = l.
Proof.
  intros lens codes l s Hc Hlens Hl Hs. unfold sw_work.
  apply (places_prefix lens codes (sw_cnt lens codes) (Z.to_nat codes) s l);
    [ exact Hlens | reflexivity | lia | exact Hl | exact Hs ].
Qed.

(** ** LEMMA 6 — the windows tile [[0, N)]

    Pure tiling: it needs neither the [lens] bound nor nonnegativity of the
    counts, only [sw_offs cnt 1 = 0] and the step equation.  The general form
    is stated over an arbitrary [cnt] for exactly that reason. *)
Lemma sw_window_exists_gen : forall cnt s,
  0 <= s < sw_offs cnt 15 + cnt 15 ->
  exists l, 1 <= l <= 15 /\ sw_offs cnt l <= s < sw_offs cnt l + cnt l.
Proof.
  intros cnt s Hs.
  pose proof (sw_offs_1 cnt) as O1.
  pose proof (sw_offs_step' cnt 1 2 ltac:(lia) ltac:(lia)) as S1.
  pose proof (sw_offs_step' cnt 2 3 ltac:(lia) ltac:(lia)) as S2.
  pose proof (sw_offs_step' cnt 3 4 ltac:(lia) ltac:(lia)) as S3.
  pose proof (sw_offs_step' cnt 4 5 ltac:(lia) ltac:(lia)) as S4.
  pose proof (sw_offs_step' cnt 5 6 ltac:(lia) ltac:(lia)) as S5.
  pose proof (sw_offs_step' cnt 6 7 ltac:(lia) ltac:(lia)) as S6.
  pose proof (sw_offs_step' cnt 7 8 ltac:(lia) ltac:(lia)) as S7.
  pose proof (sw_offs_step' cnt 8 9 ltac:(lia) ltac:(lia)) as S8.
  pose proof (sw_offs_step' cnt 9 10 ltac:(lia) ltac:(lia)) as S9.
  pose proof (sw_offs_step' cnt 10 11 ltac:(lia) ltac:(lia)) as S10.
  pose proof (sw_offs_step' cnt 11 12 ltac:(lia) ltac:(lia)) as S11.
  pose proof (sw_offs_step' cnt 12 13 ltac:(lia) ltac:(lia)) as S12.
  pose proof (sw_offs_step' cnt 13 14 ltac:(lia) ltac:(lia)) as S13.
  pose proof (sw_offs_step' cnt 14 15 ltac:(lia) ltac:(lia)) as S14.
  destruct (Z.lt_ge_cases s (sw_offs cnt 2))  as [H|H];  [exists 1;  lia|].
  destruct (Z.lt_ge_cases s (sw_offs cnt 3))  as [H2|H2]; [exists 2;  lia|].
  destruct (Z.lt_ge_cases s (sw_offs cnt 4))  as [H3|H3]; [exists 3;  lia|].
  destruct (Z.lt_ge_cases s (sw_offs cnt 5))  as [H4|H4]; [exists 4;  lia|].
  destruct (Z.lt_ge_cases s (sw_offs cnt 6))  as [H5|H5]; [exists 5;  lia|].
  destruct (Z.lt_ge_cases s (sw_offs cnt 7))  as [H6|H6]; [exists 6;  lia|].
  destruct (Z.lt_ge_cases s (sw_offs cnt 8))  as [H7|H7]; [exists 7;  lia|].
  destruct (Z.lt_ge_cases s (sw_offs cnt 9))  as [H8|H8]; [exists 8;  lia|].
  destruct (Z.lt_ge_cases s (sw_offs cnt 10)) as [H9|H9]; [exists 9;  lia|].
  destruct (Z.lt_ge_cases s (sw_offs cnt 11)) as [H10|H10]; [exists 10; lia|].
  destruct (Z.lt_ge_cases s (sw_offs cnt 12)) as [H11|H11]; [exists 11; lia|].
  destruct (Z.lt_ge_cases s (sw_offs cnt 13)) as [H12|H12]; [exists 12; lia|].
  destruct (Z.lt_ge_cases s (sw_offs cnt 14)) as [H13|H13]; [exists 13; lia|].
  destruct (Z.lt_ge_cases s (sw_offs cnt 15)) as [H14|H14]; [exists 14; lia|].
  exists 15. lia.
Qed.

Theorem sw_window_exists : forall lens codes s,
  0 <= codes ->
  (forall i, 0 <= i < codes -> 0 <= lens i <= 15) ->
  0 <= s < sw_offs (sw_cnt lens codes) 15 + sw_cnt lens codes 15 ->
  exists l, 1 <= l <= 15 /\
            sw_offs (sw_cnt lens codes) l <= s
              < sw_offs (sw_cnt lens codes) l + sw_cnt lens codes l.
Proof. intros lens codes s _ _ Hs. now apply sw_window_exists_gen. Qed.

(** ** LEMMA 7 — the downward max scan

    [it_findmax] steps DOWN from [m] with fuel [n], so it only ever inspects
    [(m - n, m]].  See [sw_findmax_spec_as_stated_false]: without a
    fuel-sufficiency premise the zero-above half is FALSE. *)

Lemma findmax_step_zero : forall k m cnt,
  cnt m = 0 -> it_findmax (S k) m cnt = it_findmax k (m - 1) cnt.
Proof. intros k m cnt H. cbn [it_findmax]. rewrite H. reflexivity. Qed.

Lemma findmax_step_nz : forall k m cnt,
  cnt m <> 0 -> it_findmax (S k) m cnt = m.
Proof.
  intros k m cnt H. cbn [it_findmax]. apply Z.eqb_neq in H as ->. reflexivity.
Qed.

(** Zero-above, in the form that is true for EVERY [n], [m]: the conclusion is
    restricted to the window the scan actually visited. *)
Lemma findmax_zero_above : forall n m cnt l,
  m - Z.of_nat n < l -> it_findmax n m cnt < l -> l <= m -> cnt l = 0.
Proof.
  intros n. induction n as [|k IH]; intros m cnt l Hw Hlt Hle.
  - cbn [Z.of_nat] in Hw. lia.
  - destruct (Z.eq_dec (cnt m) 0) as [Hz|Hnz].
    + destruct (Z.eq_dec l m) as [->|Hne]; [exact Hz|].
      rewrite (findmax_step_zero k m cnt Hz) in Hlt.
      apply (IH (m - 1) cnt l);
        [ rewrite Nat2Z.inj_succ in Hw; lia | exact Hlt | lia ].
    + rewrite (findmax_step_nz k m cnt Hnz) in Hlt. lia.
Qed.

(** Nonzero-at-the-max, true for every [n], [m]. *)
Lemma findmax_range : forall n m cnt,
  it_findmax n m cnt = 0
  \/ (m - Z.of_nat n < it_findmax n m cnt <= m /\ cnt (it_findmax n m cnt) <> 0).
Proof.
  intros n. induction n as [|k IH]; intros m cnt.
  - left. reflexivity.
  - destruct (Z.eq_dec (cnt m) 0) as [Hz|Hnz].
    + rewrite (findmax_step_zero k m cnt Hz).
      destruct (IH (m - 1) cnt) as [H|[H1 H2]].
      * left. exact H.
      * right. split; [rewrite Nat2Z.inj_succ; lia | exact H2].
    + rewrite (findmax_step_nz k m cnt Hnz).
      right. split; [rewrite Nat2Z.inj_succ; lia | exact Hnz].
Qed.

(** SHAPE CHANGE (reported): the requested statement needs the extra premise
    [m <= Z.of_nat n] — "the fuel reaches index 1".  Both real call sites
    satisfy it: [it_pre] calls [it_findmax 15 MAXBITS], i.e. [15 <= 15]. *)
Theorem sw_findmax_spec : forall (n : nat) (m : Z) (cnt : zarr),
  0 <= m -> m <= Z.of_nat n ->
  (forall l, it_findmax n m cnt < l <= m -> cnt l = 0)
  /\ (it_findmax n m cnt = 0
      \/ (m - Z.of_nat n < it_findmax n m cnt <= m
          /\ cnt (it_findmax n m cnt) <> 0)).
Proof.
  intros n m cnt Hm Hfuel. split; [|apply findmax_range].
  intros l [Hlt Hle]. apply (findmax_zero_above n m cnt l); [|exact Hlt|exact Hle].
  destruct (findmax_range n m cnt) as [H|[H1 _]]; lia.
Qed.

(** The call site, with the premise discharged. *)
Corollary sw_findmax_15 : forall cnt : zarr,
  (forall l, it_findmax 15%nat MAXBITS cnt < l <= MAXBITS -> cnt l = 0)
  /\ (it_findmax 15%nat MAXBITS cnt = 0
      \/ (0 < it_findmax 15%nat MAXBITS cnt <= MAXBITS
          /\ cnt (it_findmax 15%nat MAXBITS cnt) <> 0)).
Proof.
  intros cnt.
  destruct (sw_findmax_spec 15%nat MAXBITS cnt
              ltac:(unfold MAXBITS; lia) ltac:(rewrite zon15; unfold MAXBITS; lia))
    as [HA HB].
  split; [exact HA|]. rewrite zon15 in HB. unfold MAXBITS in *. exact HB.
Qed.

(** ** LEMMA 8 — the upward min scan

    See the FUEL BOUNDARY comment at [Inftrees.v:131]: fuel 16 from [m = 1]
    can reach index 16.  The statement below is deliberately kept free of any
    [mx <= 15] side condition; what it DOES need is the fuel-sufficiency
    premise [mx <= m + Z.of_nat n] (at the call site, [mx <= 17] — weaker than
    the [mx <= 16] a fold bridge needs, so the trap is untouched).  See
    [sw_findmin_spec_as_stated_false]. *)

Lemma findmin_step_ge : forall k m mx cnt,
  mx <= m -> it_findmin (S k) m mx cnt = mx.
Proof.
  intros k m mx cnt H. cbn [it_findmin].
  destruct (Z.geb_spec m mx) as [_|Hlt]; [reflexivity|lia].
Qed.

Lemma findmin_step_lt_zero : forall k m mx cnt,
  m < mx -> cnt m = 0 -> it_findmin (S k) m mx cnt = it_findmin k (m + 1) mx cnt.
Proof.
  intros k m mx cnt Hlt Hz. cbn [it_findmin].
  destruct (Z.geb_spec m mx) as [Hge|_]; [lia|]. rewrite Hz. reflexivity.
Qed.

Lemma findmin_step_lt_nz : forall k m mx cnt,
  m < mx -> cnt m <> 0 -> it_findmin (S k) m mx cnt = m.
Proof.
  intros k m mx cnt Hlt Hnz. cbn [it_findmin].
  destruct (Z.geb_spec m mx) as [Hge|_]; [lia|].
  apply Z.eqb_neq in Hnz as ->. reflexivity.
Qed.

Lemma findmin_le : forall n m mx cnt, it_findmin n m mx cnt <= Z.max m mx.
Proof.
  intros n. induction n as [|k IH]; intros m mx cnt.
  - cbn [it_findmin]. lia.
  - destruct (Z.le_gt_cases mx m) as [Hge|Hmx].
    + rewrite (findmin_step_ge k m mx cnt Hge). lia.
    + destruct (Z.eq_dec (cnt m) 0) as [Hz|Hnz].
      * rewrite (findmin_step_lt_zero k m mx cnt ltac:(lia) Hz).
        specialize (IH (m + 1) mx cnt). lia.
      * rewrite (findmin_step_lt_nz k m mx cnt ltac:(lia) Hnz). lia.
Qed.

Lemma findmin_zero_below : forall n m mx cnt l,
  mx <= m + Z.of_nat n -> m <= l -> l < it_findmin n m mx cnt -> cnt l = 0.
Proof.
  intros n. induction n as [|k IH]; intros m mx cnt l Hf Hml Hlt.
  - cbn [it_findmin] in Hlt. cbn [Z.of_nat] in Hf. lia.
  - destruct (Z.le_gt_cases mx m) as [Hge|Hmx].
    + rewrite (findmin_step_ge k m mx cnt Hge) in Hlt. lia.
    + destruct (Z.eq_dec (cnt m) 0) as [Hz|Hnz].
      * rewrite (findmin_step_lt_zero k m mx cnt ltac:(lia) Hz) in Hlt.
        destruct (Z.eq_dec l m) as [->|Hne]; [exact Hz|].
        apply (IH (m + 1) mx cnt l);
          [ rewrite Nat2Z.inj_succ in Hf; lia | lia | exact Hlt ].
      * rewrite (findmin_step_lt_nz k m mx cnt ltac:(lia) Hnz) in Hlt. lia.
Qed.

(** SHAPE CHANGE (reported): extra premise [mx <= m + Z.of_nat n]. *)
Theorem sw_findmin_spec : forall (n : nat) (m mx : Z) (cnt : zarr),
  mx <= m + Z.of_nat n ->
  (forall l, m <= l < it_findmin n m mx cnt -> cnt l = 0)
  /\ it_findmin n m mx cnt <= Z.max m mx.
Proof.
  intros n m mx cnt Hf. split; [|apply findmin_le].
  intros l [H1 H2]. apply (findmin_zero_below n m mx cnt l); assumption.
Qed.

(** The call site ([it_pre] calls [it_findmin 16 1 mx]), with the premise
    discharged from the bound every caller has on [mx]. *)
Corollary sw_findmin_16 : forall (mx : Z) (cnt : zarr),
  mx <= 17 ->
  (forall l, 1 <= l < it_findmin 16%nat 1 mx cnt -> cnt l = 0)
  /\ it_findmin 16%nat 1 mx cnt <= Z.max 1 mx.
Proof.
  intros mx cnt H. apply sw_findmin_spec. rewrite zon16. lia.
Qed.

(** ** Why lemmas 7 and 8 needed a premise: the requested forms are FALSE

    Both counterexamples are the same phenomenon — a scan whose FUEL runs out
    before it has covered the interval the conclusion talks about.  Kept in
    the file (rather than only in prose) so the claim is machine-checked. *)

Lemma sw_findmax_spec_as_stated_false :
  ~ (forall (n : nat) (m : Z) (cnt : zarr),
       0 <= m ->
       (forall l, it_findmax n m cnt < l <= m -> cnt l = 0)
       /\ (it_findmax n m cnt = 0
           \/ (m - Z.of_nat n < it_findmax n m cnt <= m
               /\ cnt (it_findmax n m cnt) <> 0))).
Proof.
  intros H. assert (H1 : 0 <= 1) by lia.
  specialize (H 0%nat 1 (zset zzero 1 5) H1).
  destruct H as [H0 _]. specialize (H0 1). cbn [it_findmax] in H0.
  assert (Hc : zset zzero 1 5 1 = 0) by (apply H0; lia).
  rewrite zset_same in Hc. discriminate.
Qed.

Lemma sw_findmin_spec_as_stated_false :
  ~ (forall (n : nat) (m mx : Z) (cnt : zarr),
       (forall l, m <= l < it_findmin n m mx cnt -> cnt l = 0)
       /\ it_findmin n m mx cnt <= Z.max m mx).
Proof.
  intros H. specialize (H 0%nat 1 5 (zset zzero 3 7)).
  destruct H as [H0 _]. specialize (H0 3). cbn [it_findmin] in H0.
  assert (Hc : zset zzero 3 7 3 = 0) by (apply H0; lia).
  rewrite zset_same in Hc. discriminate.
Qed.

(** ** Axiom audit — the eight deliverables *)

Print Assumptions sw_cnt_nonneg.
Print Assumptions sw_offs_1.
Print Assumptions sw_offs_step.
Print Assumptions sw_offs_mono.
Print Assumptions sw_places.
Print Assumptions sw_window_exists.
Print Assumptions sw_findmax_spec.
Print Assumptions sw_findmin_spec.
