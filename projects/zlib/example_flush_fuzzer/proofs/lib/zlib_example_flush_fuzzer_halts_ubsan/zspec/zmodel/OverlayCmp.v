(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith List Bool Lia Permutation.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees HuffTree HuffBuild DeflRoom OverlayFBS OverlayRace.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Section Cmp.
  Variable U : list Z.
  Variables F L u : Z -> Z.
  Variables HL HU : Z.
  Hypothesis Fnn : forall j, In j U -> 0 <= F j.
  Hypothesis LH : forall j, In j U -> 1 <= L j <= HL.
  Hypothesis UH : forall j, In j U -> 0 <= u j <= HU.
  Hypothesis KL : zsum (map (fun j => 2 ^ (HL - L j)) U) <= 2 ^ HL.
  Hypothesis KU : zsum (map (fun j => 2 ^ (HU - u j)) U) <= 2 ^ HU.
  Hypothesis OPT : forall H c, dep_ok H c -> kraft H c <= 2 ^ H -> (forall e, In e c -> 0 <= ew e) ->
      Permutation (map ew c) (map F U) -> zsum (map (fun j => F j * L j) U) <= ccost c.

  Hypothesis HL0 : 0 <= HL.
  Hypothesis HU0 : 0 <= HU.

  Theorem cmp_code : forall P : Z -> bool,
    zsum (map (fun j => F j * (L j - u j)) (filter P U)) <= zsum (map F U).
  Proof.
    intros P.
    set (H := Z.max HL HU + 1).
    set (l' := fun j => if P j then u j + 1 else L j + 1).
    set (c := map (fun j => E (F j) j (l' j)) U).
    assert (D : dep_ok H c).
    { unfold dep_ok. intros e He. apply in_map_iff in He. destruct He as (j & Ee & Hj). subst e. cbn [ed]. subst l' H. cbn beta.
      specialize (LH j Hj). specialize (UH j Hj). destruct (P j); lia. }
    assert (W : forall e, In e c -> 0 <= ew e).
    { intros e He. apply in_map_iff in He. destruct He as (j & Ee & Hj). subst e. cbn [ew]. apply Fnn. exact Hj. }
    assert (PW : Permutation (map ew c) (map F U)).
    { subst c. rewrite map_map. cbn. apply Permutation_refl. }
    assert (K : kraft H c <= 2 ^ H).
    { unfold kraft. subst c. rewrite map_map. cbn [ed].
      transitivity (zsum (map (fun j => 2 ^ (H - 1 - HU) * 2 ^ (HU - u j) + 2 ^ (H - 1 - HL) * 2 ^ (HL - L j)) U)).
      -
        assert (GEN : forall l, (forall j, In j l -> In j U) ->
                  zsum (map (fun x => 2 ^ (H - l' x)) l) <= zsum (map (fun j => 2 ^ (H - 1 - HU) * 2 ^ (HU - u j) + 2 ^ (H - 1 - HL) * 2 ^ (HL - L j)) l)).
        { induction l as [|j l IH]; intros Hl; cbn [map zsum]; [lia|].
          specialize (IH ltac:(intros; apply Hl; right; assumption)).
          assert (Hj : In j U) by (apply Hl; left; reflexivity).
          specialize (LH j Hj). specialize (UH j Hj).
          pose proof (Z.pow_nonneg 2 (H - 1 - HU) ltac:(lia)). pose proof (Z.pow_nonneg 2 (HU - u j) ltac:(lia)).
          pose proof (Z.pow_nonneg 2 (H - 1 - HL) ltac:(lia)). pose proof (Z.pow_nonneg 2 (HL - L j) ltac:(lia)).
          subst l'. cbn beta in *. destruct (P j).
          - rewrite <- (Z.pow_add_r 2 (H - 1 - HU)) by lia. replace (H - 1 - HU + (HU - u j)) with (H - (u j + 1)) by lia. nia.
          - rewrite <- (Z.pow_add_r 2 (H - 1 - HL)) by lia. replace (H - 1 - HL + (HL - L j)) with (H - (L j + 1)) by lia. nia. }
        apply GEN. auto.
      - rewrite zsum_map_add, !zsum_map_mul.
        pose proof (Z.pow_nonneg 2 (H - 1 - HU) ltac:(lia)) as A. pose proof (Z.pow_nonneg 2 (H - 1 - HL) ltac:(lia)) as B.
        assert (E1 : 2 ^ (H - 1 - HU) * 2 ^ HU = 2 ^ (H - 1)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
        assert (E2 : 2 ^ (H - 1 - HL) * 2 ^ HL = 2 ^ (H - 1)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
        assert (E3 : 2 ^ H = 2 * 2 ^ (H - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
        nia. }
    pose proof (OPT H c D K W PW) as O.
    unfold ccost in O. subst c. rewrite map_map in O. cbn [ew ed] in O.
    assert (SPLIT : forall l, zsum (map (fun x => F x * l' x) l)
              = zsum (map (fun j => F j * L j) l) + zsum (map F l) - zsum (map (fun j => F j * (L j - u j)) (filter P l))).
    { subst l'. induction l as [|j l IH]; cbn [map zsum filter]; [lia|]. destruct (P j); cbn [map zsum]; lia. }
    rewrite SPLIT in O. lia.
  Qed.

  Theorem cmp_code_pos : forall lam : Z -> Z,
    zsum (map (fun j => F j * Z.max 0 (lam j - u j)) U)
      <= zsum (map F U) + zsum (map (fun j => F j * Z.max 0 (lam j - L j)) U).
  Proof.
    intros lam. pose proof (cmp_code (fun j => u j <? lam j)) as C.
    assert (GEN : forall l, (forall j, In j l -> In j U) ->
       zsum (map (fun j => F j * Z.max 0 (lam j - u j)) l)
         <= zsum (map (fun j => F j * (L j - u j)) (filter (fun j => u j <? lam j) l))
            + zsum (map (fun j => F j * Z.max 0 (lam j - L j)) l)).
    { induction l as [|j l IH]; intros Hl; cbn; [lia|].
      specialize (IH ltac:(intros; apply Hl; right; assumption)).
      pose proof (Fnn j (Hl j (or_introl eq_refl))) as Fj.
      destruct (Z.ltb_spec (u j) (lam j)); cbn.
      - rewrite Z.max_r by lia. assert (F j * (lam j - u j) <= F j * (L j - u j) + F j * Z.max 0 (lam j - L j)) by nia. lia.
      - rewrite Z.max_l by lia. nia. }
    specialize (GEN U ltac:(auto)). lia.
  Qed.
End Cmp.


Lemma table_range : forall (a : arr) lo hi n,
  forallb (fun i => (lo <=? arr_get a i) && (arr_get a i <=? hi)) (ziota 0 n) = true ->
  forall k, 0 <= k < Z.of_nat n -> lo <= arr_get a k <= hi.
Proof.
  intros a lo hi n H k Hk. rewrite forallb_forall in H.
  specialize (H k ltac:(apply in_ziota; lia)). apply andb_prop in H. destruct H as [A B].
  apply Z.leb_le in A. apply Z.leb_le in B. lia.
Qed.

Definition ul (j : Z) : Z := if (257 <=? j) && (j <=? 285) then 9 - arr_get extra_lbits_a (j - 257) else 15.
Definition vd (i : Z) : Z := 15 - arr_get extra_dbits_a i.

Lemma ul_range : forall j, 0 <= ul j <= 15.
Proof.
  intros j. unfold ul.
  destruct (Z.leb_spec 257 j) as [A|A]; [|cbn; lia]. destruct (Z.leb_spec j 285) as [B|B]; [|cbn; lia]. cbn [andb].
  pose proof (table_range extra_lbits_a 0 5 29 ltac:(vm_compute; reflexivity) (j - 257) ltac:(lia)). lia.
Qed.

Lemma vd_range : forall i, 0 <= i <= 29 -> 2 <= vd i <= 15.
Proof.
  intros i Hi. unfold vd.
  pose proof (table_range extra_dbits_a 0 13 30 ltac:(vm_compute; reflexivity) i ltac:(lia)). lia.
Qed.

Lemma ul_kraft_full : zsum (map (fun j => 2 ^ (15 - ul j)) (ziota 0 286)) = 16705.
Proof. vm_compute. reflexivity. Qed.
Lemma vd_kraft_full : zsum (map (fun i => 2 ^ (15 - vd i)) (ziota 0 30)) = 32768.
Proof. vm_compute. reflexivity. Qed.

Lemma zsum_sub : forall (g : Z -> Z) (U V : list Z),
  NoDup U -> (forall j, In j U -> In j V) -> (forall j, In j V -> 0 <= g j) ->
  zsum (map g U) <= zsum (map g V).
Proof.
  intros g U V ND SUB NN. revert V SUB NN. induction ND as [|x U Hx ND IH]; intros V SUB NN; cbn.
  - apply zsum_nonneg. intros y Hy. apply in_map_iff in Hy. destruct Hy as (j & <- & Hj). apply NN. exact Hj.
  - assert (HxV : In x V) by (apply SUB; left; reflexivity).
    destruct (in_split x V HxV) as (V1 & V2 & ->).
    rewrite map_app, zsum_app. cbn.
    specialize (IH (V1 ++ V2)).
    rewrite map_app, zsum_app in IH.
    assert (S' : forall j, In j U -> In j (V1 ++ V2)).
    { intros j Hj. assert (In j (V1 ++ x :: V2)) by (apply SUB; right; exact Hj).
      apply in_app_iff in H. apply in_app_iff. destruct H as [H|[H|H]]; [left; exact H| subst j; contradiction | right; exact H]. }
    assert (N' : forall j, In j (V1 ++ V2) -> 0 <= g j).
    { intros j Hj. apply NN. apply in_app_iff in Hj. apply in_app_iff. destruct Hj; [left|right; right]; assumption. }
    specialize (IH S' N'). lia.
Qed.

Lemma ul_kraft : forall U, NoDup U -> (forall j, In j U -> 0 <= j < 286) ->
  zsum (map (fun j => 2 ^ (15 - ul j)) U) <= 2 ^ 15.
Proof.
  intros U ND R. etransitivity; [apply (zsum_sub _ U (ziota 0 286) ND)|].
  - intros j Hj. apply in_ziota. specialize (R j Hj). lia.
  - intros j _. apply Z.pow_nonneg. lia.
  - rewrite ul_kraft_full. vm_compute. discriminate.
Qed.

Lemma vd_kraft : forall U, NoDup U -> (forall j, In j U -> 0 <= j < 30) ->
  zsum (map (fun i => 2 ^ (15 - vd i)) U) <= 2 ^ 15.
Proof.
  intros U ND R. etransitivity; [apply (zsum_sub _ U (ziota 0 30) ND)|].
  - intros j Hj. apply in_ziota. specialize (R j Hj). lia.
  - intros j _. apply Z.pow_nonneg. lia.
  - rewrite vd_kraft_full. apply Z.le_refl.
Qed.

Lemma ul_lext : forall c, 0 <= c <= 28 -> ul (c + LITERALS + 1) + arr_get extra_lbits_a c = 9.
Proof.
  intros c Hc. unfold ul, LITERALS.
  replace ((257 <=? c + 256 + 1) && (c + 256 + 1 <=? 285)) with true by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia).
  replace (c + 256 + 1 - 257) with c by lia. lia.
Qed.
Lemma vd_dext : forall i, vd i + arr_get extra_dbits_a i = 15.
Proof. intros. unfold vd. lia. Qed.


Lemma length_code_range : forall lc, 0 <= lc <= 255 -> 0 <= arr_get length_code_a lc <= 28.
Proof.
  intros lc H. exact (table_range length_code_a 0 28 256 ltac:(vm_compute; reflexivity) lc ltac:(lia)).
Qed.

Lemma dist_code_range : forall k, 0 <= k < 512 -> 0 <= arr_get dist_code_a k <= 29.
Proof.
  intros k H. exact (table_range dist_code_a 0 29 512 ltac:(vm_compute; reflexivity) k ltac:(lia)).
Qed.

Lemma d_code_range : forall d, 0 <= d < 32768 -> 0 <= d_code d <= 29.
Proof.
  intros d Hd. unfold d_code. destruct (Z.ltb_spec d 256).
  - apply dist_code_range. lia.
  - apply dist_code_range. rewrite Z.shiftr_div_pow2 by lia.
    assert (0 <= d / 2 ^ 7) by (apply Z.div_pos; lia).
    assert (d / 2 ^ 7 < 256) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

Lemma cost_of_lit : forall lfc ldl dfc ddl lc, cost_of lfc ldl dfc ddl (0, lc) = arr_get ldl lc.
Proof. intros. unfold cost_of, calls_of. cbn. lia. Qed.

Lemma cost_of_match : forall lfc ldl dfc ddl d lc, d <> 0 ->
  cost_of lfc ldl dfc ddl (d, lc) =
    arr_get ldl (arr_get length_code_a lc + LITERALS + 1) + arr_get extra_lbits_a (arr_get length_code_a lc)
    + arr_get ddl (d_code (d - 1)) + arr_get extra_dbits_a (d_code (d - 1)).
Proof.
  intros lfc ldl dfc ddl d lc Hd. unfold cost_of, calls_of.
  replace (d =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hd). cbv zeta.
  rewrite !sumlen_app. cbn [sumlen].
  destruct (Z.eqb_spec (arr_get extra_lbits_a (arr_get length_code_a lc)) 0);
  destruct (Z.eqb_spec (arr_get extra_dbits_a (d_code (d - 1))) 0); cbn [negb sumlen]; lia.
Qed.

Lemma zsum_indicator_notin : forall (h : Z -> Z) U k, ~ In k U ->
  zsum (map (fun j => (if k =? j then 1 else 0) * h j) U) = 0.
Proof.
  intros h U k Hk. induction U as [|y U IH]; cbn [map zsum]; [reflexivity|].
  destruct (Z.eqb_spec k y); [subst y; exfalso; apply Hk; left; reflexivity|].
  rewrite IH by (intros H; apply Hk; right; exact H). lia.
Qed.

Lemma zsum_indicator : forall (h : Z -> Z) U k, NoDup U -> In k U ->
  zsum (map (fun j => (if k =? j then 1 else 0) * h j) U) = h k.
Proof.
  intros h U k ND Hk. induction ND as [|x U Hx ND IH]; [destruct Hk|]. cbn [map zsum].
  destruct Hk as [->|Hk].
  - rewrite Z.eqb_refl. rewrite zsum_indicator_notin by exact Hx. lia.
  - destruct (Z.eqb_spec k x); [subst x; contradiction|]. rewrite IH by exact Hk. lia.
Qed.

Lemma regroup_le : forall (l : list (Z * Z)) (sel : Z * Z -> bool) (key : Z * Z -> Z) (g : Z -> Z) U,
  NoDup U -> (forall x, In x l -> sel x = true -> In (key x) U) ->
  csum (fun x => if sel x then g (key x) else 0) l
    = zsum (map (fun j => zcount (fun x => sel x && (key x =? j)) l * g j) U).
Proof.
  intros l sel key g U ND IN. induction l as [|x l IH]; cbn [csum].
  - unfold zcount. cbn [filter length]. change (Z.of_nat 0) with 0. clear ND IN. induction U as [|a U' IHU]; cbn [map zsum]; lia.
  - rewrite IH by (intros; apply IN; [right|]; assumption).
    assert (STEP : forall j, zcount (fun x0 => sel x0 && (key x0 =? j)) (x :: l)
                   = (if sel x && (key x =? j) then 1 else 0) + zcount (fun x0 => sel x0 && (key x0 =? j)) l).
    { intros j. unfold zcount. cbn [filter]. destruct (sel x && (key x =? j)); cbn [length]; lia. }
    transitivity (zsum (map (fun j => (if key x =? j then 1 else 0) * (if sel x then g j else 0) + zcount (fun x0 => sel x0 && (key x0 =? j)) l * g j) U)).
    + rewrite zsum_map_add.
      destruct (sel x) eqn:S.
      * rewrite (zsum_indicator g U (key x) ND (IN x (or_introl eq_refl) S)). lia.
      * destruct (in_dec Z.eq_dec (key x) U).
        -- rewrite (zsum_indicator (fun _ => 0) U (key x) ND) by assumption. lia.
        -- rewrite (zsum_indicator_notin (fun _ => 0) U (key x)) by assumption. lia.
    + apply zsum_map_ext. intros j _. rewrite STEP. destruct (sel x); destruct (Z.eqb_spec (key x) j); cbn [andb]; try subst j; lia.
Qed.

Section Excess.
  Variables lfc ldl dfc ddl : arr.
  Variable syms : list (Z * Z).
  Variables UL UD : list Z.
  Variables FL FD : Z -> Z.

  Let lam := arr_get ldl.
  Let mu := arr_get ddl.
  Definition ism (x : Z * Z) : bool := negb (fst x =? 0).
  Definition sdc (x : Z * Z) : Z := d_code (fst x - 1).

  Hypothesis VALID : Forall sym_valid syms.
  Hypothesis LAM : forall lc, 0 <= lc <= 255 -> lam lc <= 24.
  Hypothesis NDL : NoDup UL.
  Hypothesis NDD : NoDup UD.
  Hypothesis INL : forall x, In x syms -> ism x = true -> In (sym_lcode x) UL.
  Hypothesis IND : forall x, In x syms -> ism x = true -> In (sdc x) UD.
  Hypothesis CNTL : forall j, In j UL -> zcount (fun x => ism x && (sym_lcode x =? j)) syms <= FL j.
  Hypothesis CNTD : forall i, In i UD -> zcount (fun x => ism x && (sdc x =? i)) syms <= FD i.

  Lemma excess_sym : forall x, In x syms ->
    Z.max 0 (cost_of lfc ldl dfc ddl x - 24)
      <= (if ism x then Z.max 0 (lam (sym_lcode x) - ul (sym_lcode x)) else 0)
         + (if ism x then Z.max 0 (mu (sdc x) - vd (sdc x)) else 0).
  Proof.
    intros [d lc] Hx. pose proof (proj1 (Forall_forall _ _) VALID (d, lc) Hx) as V. cbn in V.
    unfold ism, sdc, sym_lcode. cbn [fst].
    destruct (Z.eqb_spec d 0) as [->|Hd]; cbn [negb].
    - rewrite cost_of_lit. specialize (LAM lc ltac:(lia)). unfold lam in LAM. lia.
    - rewrite cost_of_match by exact Hd.
      pose proof (length_code_range lc ltac:(lia)) as CR.
      pose proof (ul_lext (arr_get length_code_a lc) CR) as E1.
      pose proof (vd_dext (d_code (d - 1))) as E2.
      unfold lam, mu. lia.
  Qed.

  Theorem excess_le :
    excess (cost_of lfc ldl dfc ddl) syms
      <= zsum (map (fun j => FL j * Z.max 0 (lam j - ul j)) UL)
         + zsum (map (fun i => FD i * Z.max 0 (mu i - vd i)) UD).
  Proof.
    unfold excess.
    transitivity (csum (fun x => if ism x then Z.max 0 (lam (sym_lcode x) - ul (sym_lcode x)) else 0) syms
                  + csum (fun x => if ism x then Z.max 0 (mu (sdc x) - vd (sdc x)) else 0) syms).
    - assert (GEN : forall l, (forall x, In x l -> In x syms) ->
        csum (fun x => Z.max 0 (cost_of lfc ldl dfc ddl x - 24)) l
          <= csum (fun x => if ism x then Z.max 0 (lam (sym_lcode x) - ul (sym_lcode x)) else 0) l
             + csum (fun x => if ism x then Z.max 0 (mu (sdc x) - vd (sdc x)) else 0) l).
      { induction l as [|x l IH]; intros Hl; cbn [csum]; [lia|].
        pose proof (excess_sym x (Hl x (or_introl eq_refl))). specialize (IH ltac:(intros; apply Hl; right; assumption)). lia. }
      apply GEN. auto.
    - rewrite (regroup_le syms ism sym_lcode (fun j => Z.max 0 (lam j - ul j)) UL NDL INL).
      rewrite (regroup_le syms ism sdc (fun i => Z.max 0 (mu i - vd i)) UD NDD IND).
      assert (A : forall (U : list Z) (cnt bnd g : Z -> Z), (forall j, In j U -> cnt j <= bnd j) -> (forall j, 0 <= g j) ->
                 zsum (map (fun j => cnt j * g j) U) <= zsum (map (fun j => bnd j * g j) U)).
      { intros U cnt bnd g Hc Hg. induction U as [|j U IH]; cbn [map zsum]; [lia|].
        pose proof (Hc j (or_introl eq_refl)). pose proof (Hg j). specialize (IH ltac:(intros; apply Hc; right; assumption)). nia. }
      pose proof (A UL _ FL (fun j => Z.max 0 (lam j - ul j)) CNTL ltac:(intros; lia)) as X1.
      pose proof (A UD _ FD (fun i => Z.max 0 (mu i - vd i)) CNTD ltac:(intros; lia)) as X2.
      cbn beta in X1, X2. lia.
  Qed.
End Excess.


Section Bound.
  Variables lfc ldl dfc ddl : arr.
  Variable syms : list (Z * Z).
  Variables UL UD : list Z.
  Variables FL FD LL LD : Z -> Z.
  Variables HL HD : Z.

  Hypothesis VALID : Forall sym_valid syms.
  Hypothesis LAM : forall lc, 0 <= lc <= 255 -> arr_get ldl lc <= 24.
  Hypothesis NDL : NoDup UL.
  Hypothesis NDD : NoDup UD.
  Hypothesis RL : forall j, In j UL -> 0 <= j < 286.
  Hypothesis RD : forall i, In i UD -> 0 <= i < 30.
  Hypothesis INL : forall x, In x syms -> ism x = true -> In (sym_lcode x) UL.
  Hypothesis IND : forall x, In x syms -> ism x = true -> In (sdc x) UD.
  Hypothesis CNTL : forall j, In j UL -> zcount (fun x => ism x && (sym_lcode x =? j)) syms <= FL j.
  Hypothesis CNTD : forall i, In i UD -> zcount (fun x => ism x && (sdc x =? i)) syms <= FD i.
  Hypothesis FLnn : forall j, In j UL -> 0 <= FL j.
  Hypothesis FDnn : forall i, In i UD -> 0 <= FD i.
  Hypothesis LLH : forall j, In j UL -> 1 <= LL j <= HL.
  Hypothesis LDH : forall i, In i UD -> 1 <= LD i <= HD.
  Hypothesis HL0 : 0 <= HL.
  Hypothesis HD0 : 0 <= HD.
  Hypothesis KLL : zsum (map (fun j => 2 ^ (HL - LL j)) UL) <= 2 ^ HL.
  Hypothesis KLD : zsum (map (fun i => 2 ^ (HD - LD i)) UD) <= 2 ^ HD.
  Hypothesis OPTL : forall H c, dep_ok H c -> kraft H c <= 2 ^ H -> (forall e, In e c -> 0 <= ew e) ->
      Permutation (map ew c) (map FL UL) -> zsum (map (fun j => FL j * LL j) UL) <= ccost c.
  Hypothesis OPTD : forall H c, dep_ok H c -> kraft H c <= 2 ^ H -> (forall e, In e c -> 0 <= ew e) ->
      Permutation (map ew c) (map FD UD) -> zsum (map (fun j => FD j * LD j) UD) <= ccost c.

  Definition PEN (U : list Z) (F lamf L : Z -> Z) : Z := zsum (map (fun j => F j * Z.max 0 (lamf j - L j)) U).

  Theorem excess_bound :
    excess (cost_of lfc ldl dfc ddl) syms
      <= zsum (map FL UL) + zsum (map FD UD) + PEN UL FL (arr_get ldl) LL + PEN UD FD (arr_get ddl) LD.
  Proof.
    pose proof (excess_le lfc ldl dfc ddl syms UL UD FL FD VALID LAM NDL NDD INL IND CNTL CNTD) as E.
    pose proof (cmp_code_pos UL FL LL ul HL 15 FLnn LLH ltac:(intros; apply ul_range) KLL (ul_kraft UL NDL RL) OPTL HL0 ltac:(lia) (arr_get ldl)) as CL.
    pose proof (cmp_code_pos UD FD LD vd HD 15 FDnn LDH ltac:(intros i Hi; pose proof (vd_range i ltac:(specialize (RD i Hi); lia)); lia) KLD (vd_kraft UD NDD RD) OPTD HD0 ltac:(lia) (arr_get ddl)) as CD.
    unfold PEN. lia.
  Qed.
End Bound.
