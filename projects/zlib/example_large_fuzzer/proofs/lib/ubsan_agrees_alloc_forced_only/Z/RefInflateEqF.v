(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From Stdlib Require Import FunctionalExtensionality.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateArms.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InftreesCoverage.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InffastModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeD.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeT.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeH.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeK.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeF1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeF2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateEqD.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateEqA1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateEqA2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma land_zmask_any : forall h n, 0 <= n < 32 -> Z.land h (zmask n) = h mod 2 ^ n.
Proof.
  intros h n Hn. rewrite zmask_pow2 by lia.
  replace (2 ^ n - 1) with (Z.ones n) by (unfold Z.ones; rewrite Z.shiftl_1_l; lia).
  apply Z.land_ones. lia.
Qed.

Lemma land_zmask_range : forall h n, 0 <= n < 32 -> 0 <= Z.land h (zmask n) < 2 ^ n.
Proof. intros h n Hn. rewrite land_zmask_any by lia. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia. Qed.

Lemma code_val_range : forall e, 0 <= code_val e <= 65535.
Proof.
  intros e. unfold code_val. split; [apply Z.land_nonneg; right; lia|].
  replace 65535 with (Z.ones 16) by reflexivity. rewrite Z.land_ones by lia.
  change (Z.ones 16) with (2 ^ 16 - 1). pose proof (Z.mod_pos_bound (Z.shiftr e 16) (2 ^ 16) ltac:(lia)). lia.
Qed.

Lemma wrap32_range' : forall z, 0 <= wrap32 z < 2 ^ 32.
Proof. intros z. apply wrap32_range. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FastCong.
  Variable x1 : ffx.
Variable x2 : ffx.
Variable s1 : inflate_state.
Variable s2 : inflate_state.

  (* [comment removed for export] *)
  Hypothesis EXin : x_input x2 = x_input x1.
  Hypothesis EXlast : x_last x2 = x_last x1.
  Hypothesis EXbeg : x_beg x2 = x_beg x1.
  Hypothesis EXend : x_end x2 = x_end x1.
  Hypothesis EXws : x_wsize x2 = x_wsize x1.
  Hypothesis EXwh : x_whave x2 = x_whave x1.
  Hypothesis EXwn : x_wnext x2 = x_wnext x1.
  Hypothesis EXlm : x_lmask x2 = x_lmask x1.
  Hypothesis EXdm : x_dmask x2 = x_dmask x1.
  Hypothesis EXsane : x_sane x2 = x_sane x1.
  Definition W (j : Z) : Prop := arr_get (x_window x2) j = arr_get (x_window x1) j.
  Hypothesis EW : forall j, 0 <= j < x_whave x1 -> W j.

  (* [comment removed for export] *)
  Hypothesis Xwh : 0 <= x_whave x1.
  Hypothesis Xwn : 0 <= x_wnext x1.
  Hypothesis Xws : 0 <= x_wsize x1 < 2 ^ 32.
  Hypothesis Xz : x_wsize x1 = 0 -> x_whave x1 = 0 /\ x_wnext x1 = 0.
  Hypothesis Xnz : x_wsize x1 <> 0 -> x_wnext x1 < x_wsize x1 /\ x_whave x1 <= x_wsize x1.
  Hypothesis Xfill : x_wsize x1 <> 0 -> x_whave x1 < x_wsize x1 -> x_wnext x1 = x_whave x1.
  Hypothesis Xsane : x_sane x1 = 1.

  (* [comment removed for export] *)
  Hypothesis EL : is_lencode s2 = is_lencode s1.
  Hypothesis ED : is_distcode s2 = is_distcode s1.
  Variable okL : Z -> Prop.
Variable okD : Z -> Prop.
  Hypothesis HL0 : forall i, okL i -> code_at s2 (is_lencode s1) i = code_at s1 (is_lencode s1) i.
  Hypothesis HL1 : forall h, okL (Z.land h (x_lmask x1)).
  Hypothesis HL2 : forall i h, okL i ->
    let e := code_at s1 (is_lencode s1) i in
    code_op e <> 0 -> Z.land (code_op e) 16 = 0 -> Z.land (code_op e) 64 = 0 ->
    okL (code_val e + Z.land h (zmask (code_op e))).
  Hypothesis HD0 : forall i, okD i -> code_at s2 (is_distcode s1) i = code_at s1 (is_distcode s1) i.
  Hypothesis HD1 : forall h, okD (Z.land h (x_dmask x1)).
  Hypothesis HD2 : forall i h, okD i ->
    let e := code_at s1 (is_distcode s1) i in
    Z.land (code_op e) 16 = 0 -> Z.land (code_op e) 64 = 0 ->
    okD (code_val e + Z.land h (zmask (code_op e))).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma fpull_c : forall f, fpull x2 f = fpull x1 f.
  Proof. intros f. unfold fpull. rewrite EXin. reflexivity. Qed.

  Lemma fpull2_if_c : forall f, fpull2_if x2 f = fpull2_if x1 f.
  Proof. intros f. unfold fpull2_if. rewrite !fpull_c. reflexivity. Qed.

  Lemma cp1_c : forall f, (forall i, f_from f = FWin i -> W i) -> cp1 x2 f = cp1 x1 f.
  Proof.
    intros f Hw. unfold cp1. destruct (f_from f) as [i|i] eqn:Ef; [| reflexivity].
    rewrite (Hw i eq_refl). reflexivity.
  Qed.

  Lemma cp1_fields : forall x f,
    f_in (cp1 x f) = f_in f /\ f_out (cp1 x f) = f_out f + 1 /\ f_hold (cp1 x f) = f_hold f /\ f_bits (cp1 x f) = f_bits f
    /\ f_len (cp1 x f) = f_len f /\ f_dist (cp1 x f) = f_dist f /\ f_op (cp1 x f) = f_op f /\ f_from (cp1 x f) = from_succ (f_from f).
  Proof. intros x f. unfold cp1. destruct f; cbn. repeat split; reflexivity. Qed.

  (* [comment removed for export] *)
  Definition SRC (n : Z) (f : ffs) : Prop :=
    match f_from f with
    | FOut _ => True
    | FWin i => forall j, i <= j < i + n -> W j
    end.

  Lemma SRC_le : forall n m f, SRC n f -> m <= n -> SRC m f.
  Proof. intros n m f H Hm. unfold SRC in *. destruct (f_from f); [| exact I]. intros j Hj. apply H. lia. Qed.

  Lemma SRC_cp1 : forall n f, SRC n f -> 1 <= n -> cp1 x2 f = cp1 x1 f /\ SRC (n - 1) (cp1 x1 f).
  Proof.
    intros n f H Hn. pose proof (cp1_fields x1 f) as (_ & _ & _ & _ & _ & _ & _ & Efr).
    unfold SRC in *. rewrite Efr. destruct (f_from f) as [i|i] eqn:Ef; cbn [from_succ].
    - split; [apply cp1_c; intros i' E; rewrite Ef in E; injection E as <-; apply H; lia|]. intros j Hj. apply H. lia.
    - split; [apply cp1_c; intros i' E; rewrite Ef in E; discriminate E | exact I].
  Qed.

  (* [comment removed for export] *)
  Lemma SRC_set_op : forall n f v, SRC n f -> SRC n (fset_op f v). Proof. intros n f v H. exact H. Qed.
  Lemma SRC_set_len : forall n f v, SRC n f -> SRC n (fset_len f v). Proof. intros n f v H. exact H. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma loopZ_cong_inv : forall {A} (P : A -> Prop) (b1 b2 : A -> bool * A),
    (forall a, P a -> b2 a = b1 a /\ (fst (b1 a) = true -> P (snd (b1 a)))) ->
    forall n a, P a -> loopZ n b2 a = loopZ n b1 a.
  Proof.
    intros A P b1 b2 H n. remember (Z.to_nat n) as m eqn:Em. revert n Em.
    induction m as [|m IH]; intros n Em a Pa.
    - rewrite !loopZ_le0 by lia. reflexivity.
    - rewrite !(loopZ_step n) by lia. destruct (H a Pa) as [E HP]. rewrite E.
      destruct (b1 a) as [c a']. cbn [fst snd] in HP. destruct c; [| reflexivity]. apply IH; [lia | exact (HP eq_refl)].
  Qed.
  Lemma loopZ_inv : forall {A} (P : A -> Prop) (b : A -> bool * A),
    (forall a, P a -> P (snd (b a))) -> forall n a, P a -> P (loopZ n b a).
  Proof.
    intros A P b H n. remember (Z.to_nat n) as m eqn:Em. revert n Em.
    induction m as [|m IH]; intros n Em a Pa.
    - rewrite loopZ_le0 by lia. exact Pa.
    - rewrite (loopZ_step n) by lia. pose proof (H a Pa) as HP. destruct (b a) as [c a']. cbn [snd] in HP.
      destruct c; [apply IH; [lia | exact HP] | exact HP].
  Qed.

  (* [comment removed for export] *)
  Lemma copy_op_c : forall f, 1 <= f_op f <= 2 ^ 32 -> SRC (f_op f) f -> copy_op x2 f = copy_op x1 f.
  Proof.
    intros f Hop HS. unfold copy_op.
    apply (loopZ_cong_inv (fun g => 1 <= f_op g <= 2 ^ 32 /\ SRC (f_op g) g)); [| exact (conj Hop HS)].
    intros a [Ha Sa]. destruct (SRC_cp1 _ a Sa ltac:(lia)) as [E1 S1].
    pose proof (cp1_fields x1 a) as (_ & _ & _ & _ & _ & _ & Eop & _).
    cbv beta zeta. rewrite E1. facc. rewrite Eop. rewrite wrap32_id by lia.
    split; [reflexivity|]. cbn [fst snd]. intros Hc.
    destruct (Z.eqb_spec (f_op a - 1) 0) as [Z0|Z0]; [discriminate Hc|].
    split; [facc; lia | apply SRC_set_op; facc; exact S1].
  Qed.

  (* [comment removed for export] *)
  Definition W3 (g : ffs) : Prop := 0 <= f_len g < 2 ^ 32 /\ SRC (f_len g) g.
  Lemma copy_while3_c : forall f, W3 f -> copy_while3 x2 f = copy_while3 x1 f /\ W3 (copy_while3 x1 f).
  Proof.
    intros f Hf. unfold copy_while3.
    assert (STEP : forall a, W3 a ->
      (if 2 <? f_len a then let a' := cp1 x2 (cp1 x2 (cp1 x2 a)) in (true, fset_len a' (wrap32 (f_len a' - 3))) else (false, a))
      = (if 2 <? f_len a then let a' := cp1 x1 (cp1 x1 (cp1 x1 a)) in (true, fset_len a' (wrap32 (f_len a' - 3))) else (false, a))
      /\ W3 (snd (if 2 <? f_len a then let a' := cp1 x1 (cp1 x1 (cp1 x1 a)) in (true, fset_len a' (wrap32 (f_len a' - 3))) else (false, a)))).
    { intros a [Ha Sa]. destruct (Z.ltb_spec 2 (f_len a)) as [L|L]; [| split; [reflexivity | exact (conj Ha Sa)]].
      destruct (SRC_cp1 _ a Sa ltac:(lia)) as [E1 S1]. pose proof (cp1_fields x1 a) as (_ & _ & _ & _ & El1 & _).
      destruct (SRC_cp1 _ (cp1 x1 a) S1 ltac:(lia)) as [E2 S2]. pose proof (cp1_fields x1 (cp1 x1 a)) as (_ & _ & _ & _ & El2 & _).
      destruct (SRC_cp1 _ (cp1 x1 (cp1 x1 a)) S2 ltac:(lia)) as [E3 S3]. pose proof (cp1_fields x1 (cp1 x1 (cp1 x1 a))) as (_ & _ & _ & _ & El3 & _).
      cbv beta zeta. rewrite E1, E2, E3. rewrite El3, El2, El1. rewrite wrap32_id by lia.
      split; [reflexivity|]. cbn [snd]. split; [facc; lia | apply SRC_set_len; facc; eapply SRC_le; [exact S3 | lia]]. }
    split.
    - apply (loopZ_cong_inv W3); [| exact Hf]. intros a Ha. destruct (STEP a Ha) as [E P]. split; [exact E | intros _; exact P].
    - apply (loopZ_inv W3); [| exact Hf]. intros a Ha. exact (proj2 (STEP a Ha)).
  Qed.

  (* [comment removed for export] *)
  Lemma copy_tail_c : forall f, 0 <= f_len f -> SRC (f_len f) f -> copy_tail x2 f = copy_tail x1 f.
  Proof.
    intros f Hlen HS. unfold copy_tail.
    destruct (Z.eqb_spec (f_len f) 0) as [Z0|Z0]; cbn [negb]; [reflexivity|].
    destruct (SRC_cp1 _ f HS ltac:(lia)) as [E1 HS1]. rewrite E1.
    pose proof (cp1_fields x1 f) as (_ & _ & _ & _ & El1 & _). rewrite El1.
    destruct (Z.ltb_spec 1 (f_len f)) as [L|L]; [| reflexivity].
    destruct (SRC_cp1 _ (cp1 x1 f) HS1 ltac:(lia)) as [E2 _]. exact E2.
  Qed.

  (* [comment removed for export] *)
  Definition OUTSRC (g : ffs) : Prop := exists i, f_from g = FOut i.
  Lemma f_from_set_len : forall g v, f_from (fset_len g v) = f_from g. Proof. intros g v; destruct g; reflexivity. Qed.
  Lemma cp1_out_c : forall g, OUTSRC g -> cp1 x2 g = cp1 x1 g /\ OUTSRC (cp1 x1 g).
  Proof.
    intros g [i Hg]. split; [apply cp1_c; intros i' E; rewrite Hg in E; discriminate E|].
    pose proof (cp1_fields x1 g) as (_ & _ & _ & _ & _ & _ & _ & Efr). exists (i + 1). rewrite Efr, Hg. reflexivity.
  Qed.
  Lemma copy_do3_c : forall f, OUTSRC f -> copy_do3 x2 f = copy_do3 x1 f /\ OUTSRC (copy_do3 x1 f).
  Proof.
    intros f Hf. unfold copy_do3.
    assert (STEP : forall a, OUTSRC a ->
      (let a' := cp1 x2 (cp1 x2 (cp1 x2 a)) in let a' := fset_len a' (wrap32 (f_len a' - 3)) in (2 <? f_len a', a'))
      = (let a' := cp1 x1 (cp1 x1 (cp1 x1 a)) in let a' := fset_len a' (wrap32 (f_len a' - 3)) in (2 <? f_len a', a'))
      /\ OUTSRC (snd (let a' := cp1 x1 (cp1 x1 (cp1 x1 a)) in let a' := fset_len a' (wrap32 (f_len a' - 3)) in (2 <? f_len a', a')))).
    { intros a Ha. destruct (cp1_out_c a Ha) as [E1 O1]. destruct (cp1_out_c _ O1) as [E2 O2]. destruct (cp1_out_c _ O2) as [E3 O3].
      cbv beta zeta. rewrite E1, E2, E3. split; [reflexivity|]. cbn [snd]. destruct O3 as [i Hi]. exists i. rewrite f_from_set_len. exact Hi. }
    split.
    - apply (loopZ_cong_inv OUTSRC); [| exact Hf]. intros a Ha. destruct (STEP a Ha) as [E P]. split; [exact E | intros _; exact P].
    - apply (loopZ_inv OUTSRC); [| exact Hf]. intros a Ha. exact (proj2 (STEP a Ha)).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma copy_tail_out_c : forall f, OUTSRC f -> copy_tail x2 f = copy_tail x1 f.
  Proof.
    intros f [i Hi]. unfold copy_tail.
    destruct (negb (f_len f =? 0)); [| reflexivity].
    assert (E1 : cp1 x2 f = cp1 x1 f) by (apply cp1_c; intros i' E; rewrite Hi in E; discriminate E). rewrite E1.
    pose proof (cp1_fields x1 f) as (_ & _ & _ & _ & El1 & _ & _ & Efr). rewrite El1.
    destruct (1 <? f_len f); [| reflexivity].
    apply cp1_c. intros i' E. rewrite Efr, Hi in E. discriminate E.
  Qed.

  Lemma out_copy_c : forall f, out_copy x2 f = out_copy x1 f.
  Proof.
    intros f. unfold out_copy.
    destruct (copy_do3_c (fset_from f (FOut (f_out f - f_dist f))) ltac:(eexists; reflexivity)) as [E O].
    rewrite E. apply copy_tail_out_c. exact O.
  Qed.

  Lemma dist_tailcopy_c : forall f, 0 <= f_len f < 2 ^ 32 -> SRC (f_len f) f -> dist_tailcopy x2 f = dist_tailcopy x1 f.
  Proof.
    intros f Hlen HS. unfold dist_tailcopy.
    destruct (copy_while3_c f (conj Hlen HS)) as [E [Hl HS']]. rewrite E. apply copy_tail_c; [lia | exact HS'].
  Qed.

  (* [comment removed for export] *)
  Lemma win_place_c : forall f, 1 <= f_op f <= x_whave x1 -> 0 <= f_len f < 2 ^ 32 ->
    win_place x2 f = win_place x1 f
    /\ 0 <= f_len (win_place x1 f) <= f_len f /\ SRC (f_len (win_place x1 f)) (win_place x1 f).
  Proof.
    intros f Hop Hlen.
    assert (Hnz : x_wsize x1 <> 0) by (intros Z0; destruct (Xz Z0); lia).
    destruct (Xnz Hnz) as [Hwn Hwh].
    assert (CPW : forall g i, f_from g = FWin i -> 1 <= f_op g <= 2 ^ 32 -> 0 <= i -> i + f_op g <= x_whave x1 ->
              copy_op x2 g = copy_op x1 g).
    { intros g i Hg Hog Hi Hiw. apply copy_op_c; [exact Hog|]. unfold SRC. rewrite Hg. intros j Hj. apply EW. lia. }
    assert (KL : forall g, 1 <= f_op g < 2 ^ 32 -> f_len (copy_op x1 g) = f_len g /\ f_dist (copy_op x1 g) = f_dist g).
    { intros g Hg. rewrite copy_op_cpn by exact Hg. facc.
      destruct (cpn_keep x1 (Z.to_nat (f_op g)) g) as (_ & _ & _ & K4 & K5 & _). rewrite K4, K5. split; reflexivity. }
    unfold win_place. rewrite EXwn, EXws.
    destruct (Z.eqb_spec (x_wnext x1) 0) as [W0|W0].
    - (* [comment removed for export] *)
      assert (Hfull : x_whave x1 = x_wsize x1)
        by (destruct (Z_lt_le_dec (x_whave x1) (x_wsize x1)); [pose proof (Xfill Hnz ltac:(lia)); lia | lia]).
      facc. destruct (Z.ltb_spec (f_op f) (f_len f)) as [C|C].
      + rewrite (wrap32_id (f_len f - f_op f)) by lia.
        set (f1 := fset_len (fset_from f (FWin (x_wsize x1 - f_op f))) (f_len f - f_op f)).
        rewrite (CPW f1 (x_wsize x1 - f_op f)) by (subst f1; facc; first [reflexivity | lia]).
        split; [reflexivity|]. facc.
        destruct (KL f1 ltac:(subst f1; facc; lia)) as [K4 K5]. rewrite K4. subst f1. facc.
        split; [lia|]. unfold SRC. facc. exact I.
      + split; [reflexivity|]. facc. split; [lia|]. unfold SRC. facc. intros j Hj. apply EW. lia.
    - destruct (Z.ltb_spec (x_wnext x1) (f_op f)) as [C1|C1].
      + (* [comment removed for export] *)
        assert (Hfull : x_whave x1 = x_wsize x1)
          by (destruct (Z_lt_le_dec (x_whave x1) (x_wsize x1)); [pose proof (Xfill Hnz ltac:(lia)); lia | lia]).
        facc. rewrite (wrap32_id (f_op f - x_wnext x1)) by lia.
        destruct (Z.ltb_spec (f_op f - x_wnext x1) (f_len f)) as [C2|C2].
        * rewrite (wrap32_id (f_len f - (f_op f - x_wnext x1))) by lia.
          set (f1 := fset_len (fset_op (fset_from f (FWin (x_wsize x1 + x_wnext x1 - f_op f))) (f_op f - x_wnext x1)) (f_len f - (f_op f - x_wnext x1))).
          rewrite (CPW f1 (x_wsize x1 + x_wnext x1 - f_op f)) by (subst f1; facc; first [reflexivity | lia]).
          destruct (KL f1 ltac:(subst f1; facc; lia)) as [K4 K5].
          set (f2 := copy_op x1 f1) in *. facc. rewrite ?K4, ?K5.
          replace (f_len f1) with (f_len f - (f_op f - x_wnext x1)) by reflexivity.
          destruct (Z.ltb_spec (x_wnext x1) (f_len f - (f_op f - x_wnext x1))) as [C3|C3].
          -- rewrite (wrap32_id (f_len f - (f_op f - x_wnext x1) - x_wnext x1)) by lia.
             set (f3 := fset_len (fset_op (fset_from f2 (FWin 0)) (x_wnext x1)) (f_len f - (f_op f - x_wnext x1) - x_wnext x1)).
             rewrite (CPW f3 0) by (subst f3; facc; first [reflexivity | lia]).
             split; [reflexivity|]. facc.
             destruct (KL f3 ltac:(subst f3; facc; lia)) as [K4' K5']. rewrite K4'. subst f3. facc.
             split; [lia|]. unfold SRC. facc. exact I.
          -- split; [reflexivity|]. facc. rewrite K4. subst f1. facc. split; [lia|].
             unfold SRC. facc. intros j Hj. apply EW. lia.
        * split; [reflexivity|]. facc. split; [lia|]. unfold SRC. facc. intros j Hj. apply EW. lia.
      + (* [comment removed for export] *)
        assert (Hwnh : x_wnext x1 <= x_whave x1)
          by (destruct (Z_lt_le_dec (x_whave x1) (x_wsize x1)); [pose proof (Xfill Hnz ltac:(lia)); lia | lia]).
        facc. destruct (Z.ltb_spec (f_op f) (f_len f)) as [C|C].
        * rewrite (wrap32_id (f_len f - f_op f)) by lia.
          set (f1 := fset_len (fset_from f (FWin (x_wnext x1 - f_op f))) (f_len f - f_op f)).
          rewrite (CPW f1 (x_wnext x1 - f_op f)) by (subst f1; facc; first [reflexivity | lia]).
          split; [reflexivity|]. facc.
          destruct (KL f1 ltac:(subst f1; facc; lia)) as [K4 K5]. rewrite K4. subst f1. facc.
          split; [lia|]. unfold SRC. facc. exact I.
        * split; [reflexivity|]. facc. split; [lia|]. unfold SRC. facc. intros j Hj. apply EW. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma fdrop_fields : forall f c,
    f_in (fdrop f c) = f_in f /\ f_out (fdrop f c) = f_out f /\ f_len (fdrop f c) = f_len f /\ f_dist (fdrop f c) = f_dist f
    /\ f_op (fdrop f c) = f_op f /\ f_from (fdrop f c) = f_from f /\ f_ob (fdrop f c) = f_ob f.
  Proof. intros f c. unfold fdrop. destruct f; cbn. repeat split; reflexivity. Qed.
  Lemma fpull_fields : forall x f,
    f_out (fpull x f) = f_out f /\ f_len (fpull x f) = f_len f /\ f_dist (fpull x f) = f_dist f
    /\ f_op (fpull x f) = f_op f /\ f_from (fpull x f) = f_from f /\ f_ob (fpull x f) = f_ob f.
  Proof. intros x f. unfold fpull. destruct f; cbn. repeat split; reflexivity. Qed.

  (* [comment removed for export] *)

  Lemma len_extra_c : forall op f, len_extra x2 op f = len_extra x1 op f.
  Proof. intros op f. unfold len_extra. rewrite !fpull_c. reflexivity. Qed.

  Lemma len_extra_len : forall op f, 0 <= f_len f < 2 ^ 32 -> 0 <= f_len (len_extra x1 op f) < 2 ^ 32.
  Proof.
    intros op f H. unfold len_extra. destruct (negb (op =? 0)); [| exact H]. cbv zeta.
    pose proof (fdrop_fields (fset_len (if f_bits f <? op then fpull x1 f else f)
                 (wrap32 (f_len (if f_bits f <? op then fpull x1 f else f) + Z.land (wrap32 (f_hold (if f_bits f <? op then fpull x1 f else f))) (zmask op)))) op) as (_ & _ & L & _).
    rewrite L. facc. apply wrap32_range'.
  Qed.

  Lemma fpull2_if_len : forall f, f_len (fpull2_if x1 f) = f_len f.
  Proof.
    intros f. unfold fpull2_if. destruct (f_bits f <? 15); [| reflexivity].
    pose proof (fpull_fields x1 f) as (_ & L1 & _). pose proof (fpull_fields x1 (fpull x1 f)) as (_ & L2 & _). rewrite L2. exact L1.
  Qed.

  (* [comment removed for export] *)
  Lemma refill2_len : forall (c1 c2 : bool) fd,
    f_len (if c1 then if c2 then fpull x1 (fpull x1 fd) else fpull x1 fd else fd) = f_len fd.
  Proof.
    intros c1 c2 fd. destruct c1; [| reflexivity].
    pose proof (fpull_fields x1 fd) as (_ & L1 & _). pose proof (fpull_fields x1 (fpull x1 fd)) as (_ & L2 & _).
    destruct c2; [rewrite L2|]; exact L1.
  Qed.

  (* [comment removed for export] *)
  Lemma dist_base_c : forall F, 0 <= f_len F < 2 ^ 32 -> 0 <= f_dist F < 2 ^ 32 ->
    (if wrap32 (f_out F - x_beg x1) <? f_dist F
     then if (x_whave x1 <? wrap32 (f_dist F - wrap32 (f_out F - x_beg x1))) && negb (x_sane x1 =? 0)
          then FBreak (fset_op F (wrap32 (f_dist F - wrap32 (f_out F - x_beg x1)))) BAD (Some MSG_ff_invalid_distance_too_far_back)
          else FCont (dist_tailcopy x2 (win_place x2 (fset_op F (wrap32 (f_dist F - wrap32 (f_out F - x_beg x1))))))
     else FCont (out_copy x2 F))
    = (if wrap32 (f_out F - x_beg x1) <? f_dist F
       then if (x_whave x1 <? wrap32 (f_dist F - wrap32 (f_out F - x_beg x1))) && negb (x_sane x1 =? 0)
            then FBreak (fset_op F (wrap32 (f_dist F - wrap32 (f_out F - x_beg x1)))) BAD (Some MSG_ff_invalid_distance_too_far_back)
            else FCont (dist_tailcopy x1 (win_place x1 (fset_op F (wrap32 (f_dist F - wrap32 (f_out F - x_beg x1))))))
       else FCont (out_copy x1 F)).
  Proof.
    intros F Hlen Hdist.
    pose proof (wrap32_range' (f_out F - x_beg x1)) as Rz. set (z := wrap32 (f_out F - x_beg x1)) in *. clearbody z.
    destruct (Z.ltb_spec z (f_dist F)) as [C|C]; [| rewrite out_copy_c; reflexivity].
    rewrite (wrap32_id (f_dist F - z)) by lia.
    rewrite Xsane. change (negb (1 =? 0)) with true. rewrite andb_true_r.
    destruct (Z.ltb_spec (x_whave x1) (f_dist F - z)) as [D|D]; [reflexivity|]. f_equal.
    set (G := fset_op F (f_dist F - z)).
    destruct (win_place_c G ltac:(subst G; facc; lia) ltac:(subst G; facc; exact Hlen)) as [E [L S]].
    rewrite E. apply dist_tailcopy_c; [| exact S]. subst G. facc. cbn [f_len fset_op] in L. lia.
  Qed.

  Lemma dodist_c : forall k here i f,
    okD i -> here = code_at s1 (is_distcode s1) i -> 0 <= f_len f < 2 ^ 32 ->
    dodist k x2 s2 here f = dodist k x1 s1 here f.
  Proof.
    induction k as [|k IH]; intros here i f Hi Eh Hlen; [reflexivity|].
    rewrite !dodist_S. cbv zeta. rewrite ED, EXbeg, EXwh, EXsane, !fpull_c.
    destruct (negb (Z.land (code_op here) 16 =? 0)) eqn:B16.
    - (* [comment removed for export] *)
      match goal with |- context [out_copy x2 ?F] => apply (dist_base_c F) end.
      + cbn [f_len fdrop fset_dist fset_bits fset_hold]. rewrite refill2_len. cbn [f_len fset_dist fdrop fset_bits fset_hold]. exact Hlen.
      + cbn [f_dist fdrop fset_dist fset_bits fset_hold]. apply wrap32_range'.
    - destruct (Z.land (code_op here) 64 =? 0) eqn:B64; [| reflexivity].
      apply Bool.negb_false_iff in B16. apply Z.eqb_eq in B16. apply Z.eqb_eq in B64.
      assert (Hi' : okD (code_val here + Z.land (f_hold (fdrop f (code_bits here))) (zmask (code_op here)))).
      { rewrite Eh. apply (HD2 i); [exact Hi | rewrite <- Eh; exact B16 | rewrite <- Eh; exact B64]. }
      rewrite (HD0 _ Hi'). apply (IH _ _ _ Hi' eq_refl).
      pose proof (fdrop_fields f (code_bits here)) as (_ & _ & L & _). rewrite L. exact Hlen.
  Qed.

  (* [comment removed for export] *)
  Lemma len_base_c : forall F, 0 <= f_len F < 2 ^ 32 ->
    dodist 4 x2 s2 (code_at s2 (is_distcode s1) (Z.land (f_hold F) (x_dmask x1))) F
    = dodist 4 x1 s1 (code_at s1 (is_distcode s1) (Z.land (f_hold F) (x_dmask x1))) F.
  Proof.
    intros F Hlen. rewrite (HD0 _ (HD1 (f_hold F))). apply (dodist_c 4 _ (Z.land (f_hold F) (x_dmask x1))); [apply HD1 | reflexivity | exact Hlen].
  Qed.

  Lemma dolen_c : forall k here i f,
    okL i -> here = code_at s1 (is_lencode s1) i ->
    dolen k x2 s2 here f = dolen k x1 s1 here f.
  Proof.
    induction k as [|k IH]; intros here i f Hi Eh; [reflexivity|].
    rewrite !dolen_S. cbv zeta. rewrite EL, ED, EXdm, !len_extra_c, !fpull2_if_c.
    destruct (code_op here =? 0) eqn:B0; [reflexivity|].
    destruct (negb (Z.land (code_op here) 16 =? 0)) eqn:B16.
    - apply len_base_c. rewrite fpull2_if_len. apply len_extra_len. facc. apply (conj (proj1 (code_val_range here))). pose proof (code_val_range here). lia.
    - destruct (Z.land (code_op here) 64 =? 0) eqn:B64; [| reflexivity].
      apply Z.eqb_neq in B0. apply Bool.negb_false_iff in B16. apply Z.eqb_eq in B16. apply Z.eqb_eq in B64.
      assert (Hi' : okL (code_val here + Z.land (f_hold (fdrop f (code_bits here))) (zmask (code_op here)))).
      { rewrite Eh. apply (HL2 i); [exact Hi | rewrite <- Eh; exact B0 | rewrite <- Eh; exact B16 | rewrite <- Eh; exact B64]. }
      rewrite (HL0 _ Hi'). exact (IH _ _ _ Hi' eq_refl).
  Qed.

  Theorem fast_trip_c : forall f, fast_trip x2 s2 f = fast_trip x1 s1 f.
  Proof.
    intros f. unfold fast_trip. rewrite fpull2_if_c, EL, EXlm.
    rewrite (HL0 _ (HL1 _)). exact (dolen_c 4 _ _ _ (HL1 _) eq_refl).
  Qed.
End FastCong.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ffxo (s : inflate_state) (c : icall) (r : iregs) : ffx :=
  mkFX (ic_input c) (ic_next_in c + wrap32 (ic_avail_in c - 5))
       (ic_next_out c - wrap32 (ir_out r - ic_avail_out c))
       (ic_next_out c + wrap32 (ic_avail_out c - 257))
       (is_wsize s) (is_whave s) (is_wnext s) (is_window s)
       (zmask (is_lenbits s)) (zmask (is_distbits s)) (is_sane s).
Definition ff0o (s : inflate_state) (c : icall) : ffs :=
  mkF (ic_next_in c) (ic_next_out c) (is_hold s) (is_bits s) 0 0 0 (FOut 0) (ic_outbuf c).
Definition ff_stepo (x : ffx) (s : inflate_state) (f : ffs) : ffs + (ffs * option (Z * option Z)) :=
  match fast_trip x s f with
  | FCont f' => if (f_in f' <? x_last x) && (f_out f' <? x_end x) then inl f' else inr (f', None)
  | FBreak f' mode msg => inr (f', Some (mode, msg))
  end.
Definition ff_loopo (s : inflate_state) (c : icall) (r : iregs) : ffs * option (Z * option Z) :=
  iterZ (8 * ic_avail_in c + ic_avail_out c + 80) (ff_stepo (ffxo s c r) s) (fun f => (f, None)) (ff0o s c).
Definition ff_fino (f : ffs) : ffs :=
  let len := Z.shiftr (f_bits f) 3 in
  let f := fset_in f (f_in f - len) in
  let f := fset_bits f (wrap32 (f_bits f - Z.shiftl len 3)) in
  fset_hold f (Z.land (f_hold f) (zmask (f_bits f))).
Definition ff_posto (s : inflate_state) (c : icall) (r : iregs) (x : ffx) (f : ffs) (mm : option (Z * option Z)) : iw :=
  let c := icset_outbuf c (f_ob f) in
  let c := icset_next_in c (f_in f) in
  let c := icset_next_out c (f_out f) in
  let c := icset_avail_in c (wrap32 (if f_in f <? x_last x then 5 + (x_last x - f_in f) else 5 - (f_in f - x_last x))) in
  let c := icset_avail_out c (wrap32 (if f_out f <? x_end x then 257 + (x_end x - f_out f) else 257 - (f_out f - x_end x))) in
  let s := iset_hold s (f_hold f) in
  let s := iset_bits s (f_bits f) in
  let '(s, c) := match mm with
                 | Some (mode, Some msg) => (iset_mode s mode, icset_msg c msg)
                 | Some (mode, None) => (iset_mode s mode, c)
                 | None => (s, c)
                 end in
  mkW s c r.

Lemma inflate_fast_eqo : forall s c r,
  inflate_fast (mkW s c r) = let '(f, mm) := ff_loopo s c r in ff_posto s c r (ffxo s c r) (ff_fino f) mm.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma land64_96 : Z.land 96 64 <> 0. Proof. discriminate. Qed.
Lemma land64_203 : Z.land 203 64 <> 0. Proof. discriminate. Qed.
Lemma land64_77 : Z.land 77 64 <> 0. Proof. discriminate. Qed.

Lemma okT_lens : forall s1 s2,
  tbl_eq (is_codes s1) (is_codes s2) LENS (is_lencode s1) (is_lenbits s1) ->
  exists okL : Z -> Prop,
    (forall i, okL i -> code_at s2 (is_lencode s1) i = code_at s1 (is_lencode s1) i)
    /\ (forall h, okL (Z.land h (zmask (is_lenbits s1))))
    /\ (forall i h, okL i -> let e := code_at s1 (is_lencode s1) i in
          code_op e <> 0 -> Z.land (code_op e) 16 = 0 -> Z.land (code_op e) 64 = 0 ->
          okL (code_val e + Z.land h (zmask (code_op e)))).
Proof.
  intros s1 s2. destruct (is_lencode s1) as [o| |]; cbn [tbl_eq code_at]; intros T.
  - destruct T as [used [HT HA]]. exists (fun i => 0 <= i < used).
    pose proof (T_root _ _ _ _ HT) as HR. pose proof (T_used _ _ _ _ HT) as HU.
    split; [intros i Hi; apply HA; lia|]. split.
    + intros h. pose proof (land_zmask_range h (is_lenbits s1) ltac:(lia)). lia.
    + intros i h Hi. cbv zeta. intros B0 B16 B64.
      destruct (T_shape _ _ _ _ HT i Hi) as [[(sy & len & Hsy & Hlen & Hop & Hval & _)|[(Hx & Hb & Hop & Hv1 & Hv2)|(Hop & _)]]|[Hop _]].
      * exfalso. pose proof (lens_sym_cases sy Hsy) as SC. destruct (sym_entry LENS sy) as [op v]. cbn [fst snd] in Hop, Hval.
        rewrite Hop in B0, B16, B64. clear Hop Hval.
        destruct SC as [[O1 _]|[[O1 _]|[(O1 & _)|[O1|O1]]]].
        -- exact (B0 O1).
        -- rewrite O1 in B64. exact (land64_96 B64).
        -- destruct (len_op_facts _ O1) as (_ & _ & _ & F4 & _). exact (F4 B16).
        -- rewrite O1 in B64. exact (land64_203 B64).
        -- rewrite O1 in B64. exact (land64_77 B64).
      * pose proof (land_zmask_range h (code_op (arr_get (is_codes s1) (o + i))) ltac:(lia)). lia.
      * exfalso. rewrite Hop in B64. discriminate B64.
      * exfalso. rewrite Hop in B64. discriminate B64.
  - exists (fun _ => True). repeat split; intros; exact I || reflexivity.
  - exists (fun _ => True). repeat split; intros; exact I || reflexivity.
Qed.

Lemma okT_dists : forall s1 s2,
  tbl_eq (is_codes s1) (is_codes s2) DISTS (is_distcode s1) (is_distbits s1) ->
  exists okD : Z -> Prop,
    (forall i, okD i -> code_at s2 (is_distcode s1) i = code_at s1 (is_distcode s1) i)
    /\ (forall h, okD (Z.land h (zmask (is_distbits s1))))
    /\ (forall i h, okD i -> let e := code_at s1 (is_distcode s1) i in
          Z.land (code_op e) 16 = 0 -> Z.land (code_op e) 64 = 0 ->
          okD (code_val e + Z.land h (zmask (code_op e)))).
Proof.
  intros s1 s2. destruct (is_distcode s1) as [o| |]; cbn [tbl_eq code_at]; intros T.
  - destruct T as [used [HT HA]]. exists (fun i => 0 <= i < used).
    pose proof (T_root _ _ _ _ HT) as HR. pose proof (T_used _ _ _ _ HT) as HU.
    split; [intros i Hi; apply HA; lia|]. split.
    + intros h. pose proof (land_zmask_range h (is_distbits s1) ltac:(lia)). lia.
    + intros i h Hi. cbv zeta. intros B16 B64.
      destruct (T_shape _ _ _ _ HT i Hi) as [[(sy & len & Hsy & Hlen & Hop & Hval & _)|[(Hx & Hb & Hop & Hv1 & Hv2)|(Hop & _)]]|[Hop _]].
      * exfalso. pose proof (dists_sym_cases sy Hsy) as SC. destruct (sym_entry DISTS sy) as [op v]. cbn [fst snd] in Hop, Hval.
        rewrite Hop in B16, B64. clear Hop Hval.
        destruct SC as [(O1 & _)|[O1 _]]; [destruct (dist_op_facts _ O1) as (_ & _ & _ & F4); exact (F4 B16) | rewrite O1 in B64; discriminate B64].
      * pose proof (land_zmask_range h (code_op (arr_get (is_codes s1) (o + i))) ltac:(lia)). lia.
      * exfalso. rewrite Hop in B64. discriminate B64.
      * exfalso. rewrite Hop in B64. discriminate B64.
  - exists (fun _ => True). repeat split; intros; exact I || reflexivity.
  - exists (fun _ => True). repeat split; intros; exact I || reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Inst.
  Variable s1 : inflate_state.
Variable s2 : inflate_state.
Variable c : icall.
Variable r : iregs.
  Hypothesis HC : CORE s1.
  Hypothesis E : is_mode s1 = LEN.
  Hypothesis HQ : IEQ s1 s2.

  Lemma fast_trip_inst : forall f, fast_trip (ffxo s2 c r) s2 f = fast_trip (ffxo s1 c r) s1 f.
  Proof.
    intros f. pose proof HQ as HQ0. ieq_open HQ E.
    pose proof HC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14).
    destruct (okT_lens s1 s2 QtblL) as [okL (HL0 & HL1 & HL2)].
    destruct (okT_dists s1 s2 QtblD) as [okD (HD0 & HD1 & HD2)].
    assert (Xws : 0 <= is_wsize s1 < 2 ^ 32).
    { destruct (Z.eq_dec (is_wsize s1) 0) as [Z0|Z0]; [lia|]. rewrite (C3 Z0). unfold shl32. apply wrap32_range'. }
    refine (fast_trip_c (ffxo s1 c r) (ffxo s2 c r) s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ okL okD _ _ _ _ _ _ f);
      cbn [x_input x_beg x_wsize x_whave x_wnext x_lmask x_dmask x_sane x_window ffxo]; unfold W; cbn [x_window ffxo];
      try assumption; try reflexivity.
    - rewrite Qlenbits. reflexivity.
    - rewrite Qdistbits. reflexivity.
  Qed.

  Lemma ff_loop_inst : ff_loopo s2 c r = ff_loopo s1 c r.
  Proof.
    unfold ff_loopo.
    replace (ff0o s2 c) with (ff0o s1 c).
    2:{ pose proof HQ as HQ0. ieq_open HQ0 E. unfold ff0o. rewrite Qhold, Qbits. reflexivity. }
    replace (ff_stepo (ffxo s2 c r) s2) with (ff_stepo (ffxo s1 c r) s1); [reflexivity|].
    extensionality f. unfold ff_stepo. rewrite fast_trip_inst. cbn [x_last x_end ffxo]. reflexivity.
  Qed.
End Inst.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mode_ok (st : fstep) : Prop := match st with FCont _ => True | FBreak _ m _ => m = TYPE \/ m = BAD end.

Lemma dodist_mode : forall k x s here f, mode_ok (dodist k x s here f).
Proof.
  induction k as [|k IH]; intros x s here f; [exact I|]. rewrite dodist_S. cbv zeta.
  destruct (negb _); [| destruct (_ =? 0); [apply IH | right; reflexivity]].
  destruct (_ <? _); [| exact I]. destruct (_ && _); [right; reflexivity | exact I].
Qed.
Lemma dolen_mode : forall k x s here f, mode_ok (dolen k x s here f).
Proof.
  induction k as [|k IH]; intros x s here f; [exact I|]. rewrite dolen_S. cbv zeta.
  destruct (_ =? 0); [exact I|]. destruct (negb _); [apply dodist_mode|].
  destruct (_ =? 0); [apply IH|]. destruct (negb _); [left | right]; reflexivity.
Qed.
Lemma ff_loopo_mode : forall s c r, match snd (ff_loopo s c r) with Some (m, _) => m = TYPE \/ m = BAD | None => True end.
Proof.
  intros s c r. unfold ff_loopo.
  set (n := 8 * ic_avail_in c + ic_avail_out c + 80). clearbody n. set (f := ff0o s c). clearbody f.
  remember (Z.to_nat n) as m eqn:Em. revert n Em f.
  induction m as [|m IH]; intros n Em f.
  - rewrite iterZ_le0 by lia. exact I.
  - rewrite iterZ_step by lia. unfold ff_stepo at 1.
    pose proof (dolen_mode 4 (ffxo s c r) s (code_at s (is_lencode s) (Z.land (f_hold (fpull2_if (ffxo s c r) f)) (x_lmask (ffxo s c r)))) (fpull2_if (ffxo s c r) f)) as M.
    unfold fast_trip. destruct (dolen 4 _ s _ _) as [f'|f' mode msg]; cbn [mode_ok] in M.
    + destruct (_ && _); [apply IH; lia | exact I].
    + exact M.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem fastc_proof : FASTC.
Proof.
  intros s1 s2 c r HC E HQ HU Hh Hl. unfold amodify. cbn [RES2]. split; [reflexivity|].
  notHB HU E W5 F0. pose proof HQ as HQ0. ieq_open HQ E.
  pose proof HC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14).
  unfold RESTORE. cbn [w_s w_c w_r].
  set (cR := icset_avail_in (icset_next_in (icset_avail_out (icset_next_out c (ir_put r)) (ir_left r)) (ir_next r)) (ir_have r)).
  set (sR1 := iset_bits (iset_hold s1 (ir_hold r)) (ir_bits r)).
  set (sR2 := iset_bits (iset_hold s2 (ir_hold r)) (ir_bits r)).
  assert (ER : is_mode sR1 = LEN) by (subst sR1; sacc; exact E).
  assert (HQR : IEQ sR1 sR2) by (subst sR1 sR2; ieq_close E).
  assert (HCR : CORE sR1).
  { apply (CORE_keep s1); [exact HC | subst sR1; sacc; reflexivity .. | subst sR1; sacc; exact C14]. }
  rewrite !inflate_fast_eqo. rewrite (ff_loop_inst sR1 sR2 cR r HCR ER HQR).
  pose proof (ff_loopo_mode sR1 cR r) as HM.
  destruct (ff_loopo sR1 cR r) as [f mm]. cbn [snd] in HM.
  unfold ff_posto, LOAD. cbv zeta.
  destruct mm as [[mode [msg|]]|].
  - destruct HM as [-> | ->]; subst sR1 sR2 cR; cbn [w_s w_c w_r]; unfold wset_r; cbn [w_s w_c w_r]; sacc;
      (apply WMID_mk; [ieq_close E | uw0 W5 F0]).
  - destruct HM as [-> | ->]; subst sR1 sR2 cR; cbn [w_s w_c w_r]; unfold wset_r; cbn [w_s w_c w_r]; sacc;
      (apply WMID_mk; [ieq_close E | uw0 W5 F0]).
  - subst sR1 sR2 cR; cbn [w_s w_c w_r]; unfold wset_r; cbn [w_s w_c w_r]; sacc.
    apply WMID_mk; [ieq_close E | uw0 W5 F0].
Qed.
