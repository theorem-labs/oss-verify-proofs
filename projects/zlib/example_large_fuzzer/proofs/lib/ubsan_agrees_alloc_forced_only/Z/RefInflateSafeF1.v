(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateArms.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InftreesCoverage.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ItProof.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InffastModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeD.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeT.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeH.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac facc :=
  cbn [f_in f_out f_hold f_bits f_len f_dist f_op f_from f_ob
       fset_in fset_out fset_hold fset_bits fset_len fset_dist fset_op fset_from fset_ob
       x_input x_last x_beg x_end x_wsize x_whave x_wnext x_window x_lmask x_dmask x_sane].
Ltac facc_in H :=
  cbn [f_in f_out f_hold f_bits f_len f_dist f_op f_from f_ob
       fset_in fset_out fset_hold fset_bits fset_len fset_dist fset_op fset_from fset_ob
       x_input x_last x_beg x_end x_wsize x_whave x_wnext x_window x_lmask x_dmask x_sane] in H.

(* [comment removed for export] *)
Definition FB (ON : Z) (f : ffs) : Prop :=
  0 <= f_in f /\ 0 <= f_out f /\ 0 <= f_bits f <= 32 /\ 0 <= f_hold f < 2 ^ f_bits f /\ arr_len (f_ob f) = ON.

(* [comment removed for export] *)
Definition COPIED (n : Z) (f f' : ffs) : Prop :=
  f_in f' = f_in f /\ f_hold f' = f_hold f /\ f_bits f' = f_bits f /\ f_dist f' = f_dist f
  /\ f_out f' = f_out f + n /\ arr_len (f_ob f') = arr_len (f_ob f).

Lemma COPIED_refl : forall f, COPIED 0 f f.
Proof. intros f. unfold COPIED. repeat split; lia. Qed.
Lemma COPIED_trans : forall a b f f1 f2, COPIED a f f1 -> COPIED b f1 f2 -> COPIED (a + b) f f2.
Proof.
  intros a b f f1 f2 (A1 & A2 & A3 & A4 & A5 & A6) (B1 & B2 & B3 & B4 & B5 & B6). unfold COPIED.
  rewrite B1, B2, B3, B4, B5, B6, A1, A2, A3, A4, A5, A6. repeat split; lia.
Qed.
Lemma cpn_COPIED : forall x n f, COPIED (Z.of_nat n) f (cpn x n f).
Proof.
  intros x n f. destruct (cpn_keep x n f) as (A & B & C & _ & E & _).
  unfold COPIED. rewrite A, B, C, E, cpn_out, cpn_len_ob. repeat split; reflexivity.
Qed.
Lemma COPIED_set_len : forall n f f' v, COPIED n f f' -> COPIED n f (fset_len f' v).
Proof. intros n f f' v H. unfold COPIED in *. destruct f'; cbn in *. exact H. Qed.
Lemma COPIED_set_op : forall n f f' v, COPIED n f f' -> COPIED n f (fset_op f' v).
Proof. intros n f f' v H. unfold COPIED in *. destruct f'; cbn in *. exact H. Qed.
Lemma COPIED_set_from : forall n f f' v, COPIED n f f' -> COPIED n f (fset_from f' v).
Proof. intros n f f' v H. unfold COPIED in *. destruct f'; cbn in *. exact H. Qed.
Lemma COPIED_from_l : forall n f f' v, COPIED n (fset_from f v) f' -> COPIED n f f'.
Proof. intros n f f' v H. unfold COPIED in *. destruct f; cbn in *. exact H. Qed.
Lemma COPIED_op_l : forall n f f' v, COPIED n (fset_op f v) f' -> COPIED n f f'.
Proof. intros n f f' v H. unfold COPIED in *. destruct f; cbn in *. exact H. Qed.
Lemma COPIED_len_l : forall n f f' v, COPIED n (fset_len f v) f' -> COPIED n f f'.
Proof. intros n f f' v H. unfold COPIED in *. destruct f; cbn in *. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition win_place (x : ffx) (f : ffs) : ffs :=
  if x_wnext x =? 0 then
    let f := fset_from f (FWin (x_wsize x - f_op f)) in
    if f_op f <? f_len f then
      let f := fset_len f (wrap32 (f_len f - f_op f)) in
      let f := copy_op x f in
      fset_from f (FOut (f_out f - f_dist f))
    else f
  else if x_wnext x <? f_op f then
    let f := fset_from f (FWin (x_wsize x + x_wnext x - f_op f)) in
    let f := fset_op f (wrap32 (f_op f - x_wnext x)) in
    if f_op f <? f_len f then
      let f := fset_len f (wrap32 (f_len f - f_op f)) in
      let f := copy_op x f in
      let f := fset_from f (FWin 0) in
      if x_wnext x <? f_len f then
        let f := fset_op f (x_wnext x) in
        let f := fset_len f (wrap32 (f_len f - f_op f)) in
        let f := copy_op x f in
        fset_from f (FOut (f_out f - f_dist f))
      else f
    else f
  else
    let f := fset_from f (FWin (x_wnext x - f_op f)) in
    if f_op f <? f_len f then
      let f := fset_len f (wrap32 (f_len f - f_op f)) in
      let f := copy_op x f in
      fset_from f (FOut (f_out f - f_dist f))
    else f.
(* [comment removed for export] *)
Definition dist_tailcopy (x : ffx) (f : ffs) : ffs := copy_tail x (copy_while3 x f).
(* [comment removed for export] *)
Definition out_copy (x : ffx) (f : ffs) : ffs :=
  copy_tail x (copy_do3 x (fset_from f (FOut (f_out f - f_dist f)))).

(* [comment removed for export] *)
Lemma dodist_S : forall k x s here f,
  dodist (S k) x s here f =
    let op := code_bits here in
    let f := fdrop f op in
    let op := code_op here in
    if negb (Z.land op 16 =? 0) then
      let f := fset_dist f (code_val here) in
      let op := Z.land op 15 in
      let f := if f_bits f <? op then
                 let f := fpull x f in
                 if f_bits f <? op then fpull x f else f
               else f in
      let f := fset_dist f (wrap32 (f_dist f + Z.land (wrap32 (f_hold f)) (zmask op))) in
      let f := fdrop f op in
      let op := wrap32 (f_out f - x_beg x) in
      if op <? f_dist f then
        let op := wrap32 (f_dist f - op) in
        if (x_whave x <? op) && negb (x_sane x =? 0) then
          FBreak (fset_op f op) BAD (Some MSG_ff_invalid_distance_too_far_back)
        else FCont (dist_tailcopy x (win_place x (fset_op f op)))
      else FCont (out_copy x f)
    else if Z.land op 64 =? 0 then
      dodist k x s (code_at s (is_distcode s) (code_val here + Z.land (f_hold f) (zmask op))) f
    else FBreak f BAD (Some MSG_ff_invalid_distance_code).
Proof.
  intros. unfold win_place, dist_tailcopy, out_copy. cbv zeta. cbn [dodist].
  lazymatch goal with |- ?a = ?b => exact (@eq_refl _ a) end.
Qed.

(* [comment removed for export] *)
Lemma copy_op_COPIED : forall x f, 1 <= f_op f < 2 ^ 32 -> COPIED (f_op f) f (copy_op x f).
Proof.
  intros x f H. rewrite copy_op_cpn by exact H. apply COPIED_set_op.
  rewrite <- (Z2Nat.id (f_op f)) at 1 by lia. apply cpn_COPIED.
Qed.

Lemma win_place_spec : forall x f,
  1 <= f_op f < 2 ^ 32 -> 0 <= f_len f < 2 ^ 32 -> 0 <= x_wnext x ->
  exists n, COPIED n f (win_place x f) /\ 0 <= n /\ 0 <= f_len (win_place x f)
            /\ n + f_len (win_place x f) = f_len f.
Proof.
  intros x f Hop Hlen Hwn. unfold win_place.
  destruct (Z.eqb_spec (x_wnext x) 0) as [W0|W0].
  - facc. destruct (Z.ltb_spec (f_op f) (f_len f)) as [C|C].
    + set (f1 := fset_len (fset_from f (FWin (x_wsize x - f_op f))) (wrap32 (f_len f - f_op f))).
      assert (H1 : f_op f1 = f_op f /\ f_len f1 = f_len f - f_op f) by (subst f1; facc; rewrite wrap32_id by lia; split; reflexivity).
      destruct H1 as [Eo El].
      pose proof (copy_op_COPIED x f1 ltac:(rewrite Eo; exact Hop)) as CP. rewrite Eo in CP.
      destruct (cpn_keep x (Z.to_nat (f_op f1)) f1) as (_ & _ & _ & KL & _).
      exists (f_op f). split; [|split; [lia|]].
      * apply COPIED_set_from. apply (COPIED_from_l _ f _ (FWin (x_wsize x - f_op f))). apply (COPIED_len_l _ _ _ (wrap32 (f_len f - f_op f))). exact CP.
      * facc. rewrite copy_op_cpn by (rewrite Eo; exact Hop). facc. rewrite KL, El. lia.
    + exists 0. split; [apply COPIED_set_from; apply COPIED_refl|]. facc. lia.
  - destruct (Z.ltb_spec (x_wnext x) (f_op f)) as [Cw|Cw].
    + facc. rewrite (wrap32_id (f_op f - x_wnext x)) by lia.
      destruct (Z.ltb_spec (f_op f - x_wnext x) (f_len f)) as [C|C].
      * set (f1 := fset_len (fset_op (fset_from f (FWin (x_wsize x + x_wnext x - f_op f))) (f_op f - x_wnext x)) (wrap32 (f_len f - (f_op f - x_wnext x)))).
        assert (H1 : f_op f1 = f_op f - x_wnext x /\ f_len f1 = f_len f - (f_op f - x_wnext x) /\ f_dist f1 = f_dist f)
          by (subst f1; facc; rewrite wrap32_id by lia; repeat split; reflexivity).
        destruct H1 as (Eo & El & Ed).
        pose proof (copy_op_COPIED x f1 ltac:(rewrite Eo; lia)) as CP1. rewrite Eo in CP1.
        set (f2 := copy_op x f1) in *.
        assert (K2 : f_len f2 = f_len f1 /\ f_dist f2 = f_dist f1).
        { subst f2. rewrite copy_op_cpn by (rewrite Eo; lia). facc. destruct (cpn_keep x (Z.to_nat (f_op f1)) f1) as (_ & _ & _ & KL & KD & _). rewrite KL, KD. split; reflexivity. }
        destruct K2 as [El2 Ed2].
        assert (CPa : COPIED (f_op f - x_wnext x) f f2).
        { apply (COPIED_from_l _ f _ (FWin (x_wsize x + x_wnext x - f_op f))). apply (COPIED_op_l _ _ _ (f_op f - x_wnext x)).
          apply (COPIED_len_l _ _ _ (wrap32 (f_len f - (f_op f - x_wnext x)))). exact CP1. }
        facc. rewrite El2, El.
        destruct (Z.ltb_spec (x_wnext x) (f_len f - (f_op f - x_wnext x))) as [C2|C2].
        -- set (f3 := fset_len (fset_op (fset_from f2 (FWin 0)) (x_wnext x)) (wrap32 (f_len f - (f_op f - x_wnext x) - x_wnext x))).
           assert (H3 : f_op f3 = x_wnext x /\ f_len f3 = f_len f - (f_op f - x_wnext x) - x_wnext x)
             by (subst f3; facc; rewrite wrap32_id by lia; split; reflexivity).
           destruct H3 as [Eo3 El3].
           pose proof (copy_op_COPIED x f3 ltac:(rewrite Eo3; lia)) as CP3. rewrite Eo3 in CP3.
           destruct (cpn_keep x (Z.to_nat (f_op f3)) f3) as (_ & _ & _ & KL3 & _).
           exists (f_op f - x_wnext x + x_wnext x). split; [|split; [lia|]].
           ++ apply COPIED_set_from. eapply COPIED_trans; [exact CPa|].
              apply (COPIED_from_l _ f2 _ (FWin 0)). apply (COPIED_op_l _ _ _ (x_wnext x)). eapply COPIED_len_l. exact CP3.
           ++ facc. rewrite copy_op_cpn by (rewrite Eo3; lia). facc. rewrite KL3, El3. lia.
        -- exists (f_op f - x_wnext x). split; [apply COPIED_set_from; exact CPa|]. facc. rewrite El2, El. lia.
      * exists 0. split; [apply COPIED_set_op; apply COPIED_set_from; apply COPIED_refl|]. facc. lia.
    + facc. destruct (Z.ltb_spec (f_op f) (f_len f)) as [C|C].
      * set (f1 := fset_len (fset_from f (FWin (x_wnext x - f_op f))) (wrap32 (f_len f - f_op f))).
        assert (H1 : f_op f1 = f_op f /\ f_len f1 = f_len f - f_op f) by (subst f1; facc; rewrite wrap32_id by lia; split; reflexivity).
        destruct H1 as [Eo El].
        pose proof (copy_op_COPIED x f1 ltac:(rewrite Eo; exact Hop)) as CP. rewrite Eo in CP.
        destruct (cpn_keep x (Z.to_nat (f_op f1)) f1) as (_ & _ & _ & KL & _).
        exists (f_op f). split; [|split; [lia|]].
        -- apply COPIED_set_from. apply (COPIED_from_l _ f _ (FWin (x_wnext x - f_op f))). eapply COPIED_len_l. exact CP.
        -- facc. rewrite copy_op_cpn by (rewrite Eo; exact Hop). facc. rewrite KL, El. lia.
      * exists 0. split; [apply COPIED_set_from; apply COPIED_refl|]. facc. lia.
Qed.

Lemma dist_tailcopy_spec : forall x f, 0 <= f_len f < 2 ^ 32 -> COPIED (f_len f) f (dist_tailcopy x f).
Proof.
  intros x f H. unfold dist_tailcopy.
  rewrite copy_while3_cpn by exact H.
  set (f1 := fset_len (cpn x (Z.to_nat (3 * (f_len f / 3))) f) (f_len f mod 3)).
  assert (El : f_len f1 = f_len f mod 3) by (subst f1; reflexivity).
  pose proof (Z.mod_pos_bound (f_len f) 3 ltac:(lia)) as M3.
  pose proof (Z.div_mod (f_len f) 3 ltac:(lia)) as DM.
  pose proof (Z.div_pos (f_len f) 3 ltac:(lia) ltac:(lia)) as DP.
  rewrite copy_tail_cpn by (rewrite El; lia).
  replace (f_len f) with (Z.of_nat (Z.to_nat (3 * (f_len f / 3))) + Z.of_nat (Z.to_nat (f_len f1))) by (rewrite El; lia).
  eapply COPIED_trans; [|apply cpn_COPIED]. subst f1. apply COPIED_set_len. apply cpn_COPIED.
Qed.

Lemma out_copy_spec : forall x f, 3 <= f_len f < 2 ^ 32 -> COPIED (f_len f) f (out_copy x f).
Proof.
  intros x f H. unfold out_copy.
  set (f0 := fset_from f (FOut (f_out f - f_dist f))).
  assert (El0 : f_len f0 = f_len f) by (subst f0; reflexivity).
  rewrite copy_do3_cpn by (rewrite El0; exact H). rewrite El0.
  set (f1 := fset_len (cpn x (Z.to_nat (3 * (f_len f / 3))) f0) (f_len f mod 3)).
  assert (El : f_len f1 = f_len f mod 3) by (subst f1; reflexivity).
  pose proof (Z.mod_pos_bound (f_len f) 3 ltac:(lia)) as M3.
  pose proof (Z.div_mod (f_len f) 3 ltac:(lia)) as DM.
  pose proof (Z.div_pos (f_len f) 3 ltac:(lia) ltac:(lia)) as DP.
  rewrite copy_tail_cpn by (rewrite El; lia).
  replace (f_len f) with (Z.of_nat (Z.to_nat (3 * (f_len f / 3))) + Z.of_nat (Z.to_nat (f_len f1))) by (rewrite El; lia).
  eapply COPIED_trans; [|apply cpn_COPIED]. subst f1. apply COPIED_set_len. apply (COPIED_from_l _ f _ (FOut (f_out f - f_dist f))). apply cpn_COPIED.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma shiftr_bound : forall h b c, 0 <= h < 2 ^ b -> 0 <= c <= b -> 0 <= Z.shiftr h c < 2 ^ (b - c).
Proof.
  intros h b c Hh Hc. rewrite Z.shiftr_div_pow2 by lia. pose proof (pow2_pos c ltac:(lia)).
  split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
  rewrite <- Z.pow_add_r by lia. replace (c + (b - c)) with b by lia. lia.
Qed.

Lemma land_zmask : forall h n, 0 <= h -> 0 <= n < 32 -> Z.land h (zmask n) = h mod 2 ^ n.
Proof.
  intros h n Hh Hn. rewrite zmask_pow2 by lia.
  replace (2 ^ n - 1) with (Z.ones n) by (rewrite Z.ones_equiv; lia). apply Z.land_ones. lia.
Qed.

Lemma land_wrap32_zmask : forall h n, 0 <= h -> 0 <= n < 32 -> Z.land (wrap32 h) (zmask n) = h mod 2 ^ n.
Proof.
  intros h n Hh Hn. rewrite land_zmask by (try apply wrap32_range; lia). rewrite wrap32_mod.
  rewrite <- (Z.mod_mod_divide h (2 ^ 32) (2 ^ n)); [reflexivity|]. apply pow2_divide. lia.
Qed.

(* [comment removed for export] *)
Lemma shiftr_land_zmask : forall h b o, 0 <= h -> 0 <= b -> 0 <= o < 32 ->
  Z.land (Z.shiftr h b) (zmask o) = h mod 2 ^ (b + o) / 2 ^ b.
Proof.
  intros h b o Hh Hb Ho. rewrite land_zmask by (try (apply Z.shiftr_nonneg; lia); lia).
  rewrite Z.shiftr_div_pow2 by lia.
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.testbit_mod_pow2 by lia. rewrite !Z.div_pow2_bits by lia. rewrite Z.testbit_mod_pow2 by lia.
  destruct (Z.ltb_spec i o), (Z.ltb_spec (i + b) (b + o)); cbn [andb]; try reflexivity; lia.
Qed.

Lemma land16_small : forall op, 0 <= op < 16 -> Z.land op 16 = 0.
Proof.
  intros op H. destruct (Z.eq_dec op 0) as [->|]; [reflexivity|].
  pose proof (allz_range 0 16 (fun op => Z.land op 16 =? 0) ltac:(vm_compute; reflexivity) op H) as E. cbn beta in E.
  apply Z.eqb_eq. exact E.
Qed.
Lemma land64_small : forall op, 0 <= op < 64 -> Z.land op 64 = 0.
Proof.
  intros op H.
  pose proof (allz_range 0 64 (fun op => Z.land op 64 =? 0) ltac:(vm_compute; reflexivity) op H) as E. cbn beta in E.
  apply Z.eqb_eq. exact E.
Qed.

(* [comment removed for export] *)
Section Prims.
  Variable x : ffx.
Variable ON : Z.
  Hypothesis Xin : forall i, 0 <= arr_get (x_input x) i < 256.

  Lemma FB_fdrop : forall f c, FB ON f -> 0 <= c <= f_bits f ->
    FB ON (fdrop f c) /\ f_in (fdrop f c) = f_in f /\ f_out (fdrop f c) = f_out f /\ f_bits (fdrop f c) = f_bits f - c
    /\ f_hold (fdrop f c) = Z.shiftr (f_hold f) c /\ f_len (fdrop f c) = f_len f /\ f_dist (fdrop f c) = f_dist f /\ f_ob (fdrop f c) = f_ob f.
  Proof.
    intros f c (B1 & B2 & B3 & B4 & B5) Hc. unfold fdrop, FB. facc. rewrite wrap32_id by lia.
    pose proof (shiftr_bound (f_hold f) (f_bits f) c B4 Hc). repeat split; try lia; try exact B5; reflexivity.
  Qed.

  Lemma FB_fpull : forall f, FB ON f -> f_bits f <= 24 ->
    FB ON (fpull x f) /\ f_in (fpull x f) = f_in f + 1 /\ f_out (fpull x f) = f_out f /\ f_bits (fpull x f) = f_bits f + 8
    /\ f_hold (fpull x f) mod 2 ^ f_bits f = f_hold f /\ f_len (fpull x f) = f_len f /\ f_dist (fpull x f) = f_dist f /\ f_ob (fpull x f) = f_ob f.
  Proof.
    intros f (B1 & B2 & B3 & B4 & B5) Hb.
    destruct (fpull_eq x f ltac:(lia) ltac:(lia) ltac:(lia) (Xin _)) as [E Hh]. rewrite E. unfold FB. facc.
    pose proof (Xin (f_in f)). pose proof (pow2_pos (f_bits f) ltac:(lia)).
    repeat split; try lia; try exact B5; try reflexivity.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  Qed.
End Prims.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition DACC (ON : Z) (f f' : ffs) (c : Z) : Prop :=
  FB ON f' /\
  exists p e, 0 <= p <= 2 /\ 0 <= e <= 13 /\ f_in f' = f_in f + p
    /\ f_bits f + 8 * p - c - e <= f_bits f' <= f_bits f + 8 * p - c
    /\ (1 <= p -> f_bits f - c < e) /\ (p = 2 -> f_bits f - c + 8 < e).

Section Dodist.
  Variable x : ffx.
Variable s : inflate_state.
Variable ON : Z.
Variable used : Z.
  Hypothesis Xin : forall i, 0 <= arr_get (x_input x) i < 256.
  Hypothesis Xwn : 0 <= x_wnext x.
  Hypothesis Xbeg : 0 <= x_beg x.
  Hypothesis HON : ON < 2 ^ 32.
  Hypothesis HT : TBLg DISTS (code_at s (is_distcode s)) (is_distbits s) used.

  (* [comment removed for export] *)
  Lemma dodist_term : forall k here f,
    FB ON f -> 1 <= code_bits here <= 15 -> code_bits here <= f_bits f ->
    3 <= f_len f <= 258 -> x_beg x <= f_out f -> f_out f + f_len f <= ON ->
    ((exists sy, 0 <= sy < 32 /\ code_op here = fst (sym_entry DISTS sy) /\ code_val here = snd (sym_entry DISTS sy)) \/ code_op here = 64) ->
    match dodist (S k) x s here f with
    | FCont f' => DACC ON f f' (code_bits here) /\ f_out f' = f_out f + f_len f
    | FBreak f' m msg => DACC ON f f' (code_bits here) /\ f_out f' = f_out f /\ m = BAD /\ msg <> None
    end.
  Proof.
    intros k here f HF Hcb Hcf Hlen Hbeg Hroom Hsh. rewrite dodist_S. cbv zeta.
    destruct (FB_fdrop ON f (code_bits here) HF ltac:(lia)) as (HF1 & E1i & E1o & E1b & E1h & E1l & E1d & E1ob).
    set (f1 := fdrop f (code_bits here)) in *.
    pose proof HF as (B1 & B2 & B3 & B4 & B5). pose proof HF1 as (C1 & C2 & C3 & C4 & C5).
    assert (BADc : forall msg : Z, DACC ON f f1 (code_bits here) /\ f_out f1 = f_out f /\ BAD = BAD /\ Some msg <> None).
    { intros msg. split; [|split; [exact E1o|split; [reflexivity|discriminate]]].
      split; [exact HF1|]. exists 0, 0. rewrite E1i, E1b. repeat split; lia. }
    destruct Hsh as [[sy (Hsy & Hop & Hv)]|Hop].
    2:{ rewrite Hop. cbn [Z.land Z.eqb negb]. apply BADc. }
    pose proof (dists_sym_cases sy Hsy) as SC. destruct (sym_entry DISTS sy) as [op v]. cbn [fst snd] in Hop, Hv.
    rewrite Hop, Hv. destruct SC as [(O1 & O2 & O3)|[O1 O2]].
    2:{ rewrite O1. cbn [Z.land Z.eqb negb]. apply BADc. }
    destruct (dist_op_facts op O1) as (F1 & F2 & F3 & F4).
    replace (negb (Z.land op 16 =? 0)) with true by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; exact F4).
    rewrite F3. set (e := op - 16) in *.
    assert (He : 0 <= e <= 13) by lia.
    pose proof (pow2_le e 13 ltac:(lia)) as P13. change (2 ^ 13) with 8192 in P13. pose proof (pow2_pos e ltac:(lia)) as P0.
    (* [comment removed for export] *)
    set (f1d := fset_dist f1 v).
    assert (HF1d : FB ON f1d /\ f_in f1d = f_in f /\ f_out f1d = f_out f /\ f_bits f1d = f_bits f - code_bits here /\ f_len f1d = f_len f /\ f_dist f1d = v
                   /\ 0 <= f_hold f1d).
    { subst f1d. unfold FB. facc. repeat split; first [assumption | reflexivity | lia]. }
    clearbody f1d. clear HF1 E1i E1o E1b E1h E1l E1d E1ob C1 C2 C3 C4 C5 BADc f1.
    destruct HF1d as (HF1 & E1i & E1o & E1b & E1l & E1d & E1h0).
    match goal with |- context [fset_dist ?F _] => set (f2 := F) in * end.
    assert (HF2 : FB ON f2 /\ f_out f2 = f_out f /\ f_len f2 = f_len f /\ f_dist f2 = v /\ e <= f_bits f2 /\
                  exists p, 0 <= p <= 2 /\ f_in f2 = f_in f + p /\ f_bits f2 = f_bits f - code_bits here + 8 * p
                            /\ (1 <= p -> f_bits f - code_bits here < e) /\ (p = 2 -> f_bits f - code_bits here + 8 < e)).
    { subst f2. destruct (Z.ltb_spec (f_bits f1d) e) as [L1|L1].
      - destruct (FB_fpull x ON Xin f1d HF1 ltac:(lia)) as (HP1 & P1i & P1o & P1b & _ & P1l & P1d & _).
        destruct (Z.ltb_spec (f_bits (fpull x f1d)) e) as [L2|L2].
        + destruct (FB_fpull x ON Xin (fpull x f1d) HP1 ltac:(lia)) as (HP2 & P2i & P2o & P2b & _ & P2l & P2d & _).
          split; [exact HP2|]. rewrite P2o, P2l, P2d, P1o, P1l, P1d, P2b, P1b. repeat (split; [first [assumption | lia]|]).
          exists 2. rewrite P2i, P1i, E1i. repeat split; lia.
        + split; [exact HP1|]. rewrite P1o, P1l, P1d, P1b. repeat (split; [first [assumption | lia]|]).
          exists 1. rewrite P1i, E1i. repeat split; lia.
      - split; [exact HF1|]. repeat (split; [first [assumption | lia]|]). exists 0. rewrite E1i, E1b. repeat split; lia. }
    clearbody f2. destruct HF2 as (HF2 & E2o & E2l & E2d & E2e & p & Hp & E2i & E2b & C1p & C2p).
    pose proof HF2 as (D1 & D2 & D3 & D4 & D5).
    rewrite (land_wrap32_zmask (f_hold f2) e) by lia.
    pose proof (mod_pow2_range (f_hold f2) e ltac:(lia)) as MR.
    rewrite E2d. rewrite (wrap32_id (v + _)) by lia.
    set (dist := v + f_hold f2 mod 2 ^ e) in *.
    destruct (FB_fdrop ON (fset_dist f2 dist) e ltac:(unfold FB in *; facc; repeat split; try lia; exact D5) ltac:(facc; lia))
      as (HF3 & E3i & E3o & E3b & E3h & E3l & E3d & E3ob).
    set (f3 := fdrop (fset_dist f2 dist) e) in *. revert E3i E3o E3b E3l E3d. facc. intros E3i E3o E3b E3l E3d.
    assert (ACC3 : DACC ON f f3 (code_bits here)).
    { split; [exact HF3|]. exists p, e. rewrite E3i, E3b, E2i, E2b. repeat split; lia. }
    rewrite ?E3o, ?E3d, ?E2o. rewrite (wrap32_id (f_out f - x_beg x)) by lia.
    destruct (Z.ltb_spec (f_out f - x_beg x) dist) as [Cw|Cw].
    - (* [comment removed for export] *)
      rewrite (wrap32_id (dist - _)) by lia.
      destruct ((x_whave x <? dist - (f_out f - x_beg x)) && negb (x_sane x =? 0)).
      + split; [|split; [facc; rewrite ?E3o, ?E2o; reflexivity|split; [reflexivity|discriminate]]].
        destruct ACC3 as [HF3' AC]. split; [unfold FB in *; facc; exact HF3'|]. facc. exact AC.
      + set (f4 := fset_op f3 (dist - (f_out f - x_beg x))).
        destruct (win_place_spec x f4 ltac:(subst f4; facc; lia) ltac:(subst f4; facc; lia) Xwn) as (n & CPw & Hn & Hl5 & En).
        apply COPIED_op_l in CPw.
        pose proof (dist_tailcopy_spec x (win_place x f4) ltac:(subst f4; revert Hl5 En; facc; intros; lia)) as CPt.
        pose proof (COPIED_trans _ _ _ _ _ CPw CPt) as (T1 & T2 & T3 & T4 & T5 & T6).
        subst f4. revert En T5. facc. rewrite E3l. intros En T5.
        split; [|rewrite T5, ?E3o, ?E2o; lia].
        destruct ACC3 as [_ AC]. split.
        * unfold FB. rewrite T1, T2, T3, T5, T6. unfold FB in HF3. lia.
        * rewrite T1, T3. exact AC.
    - (* [comment removed for export] *)
      pose proof (out_copy_spec x f3 ltac:(rewrite E3l; lia)) as (T1 & T2 & T3 & T4 & T5 & T6).
      split; [|rewrite T5, ?E3o, ?E2o, ?E3l, ?E2l; lia].
      destruct ACC3 as [_ AC]. split.
      + unfold FB. rewrite T1, T2, T3, T5, T6. unfold FB in HF3. lia.
      + rewrite T1, T3. exact AC.
  Qed.

  (* [comment removed for export] *)
  Lemma DACC_shift : forall f f1 f' c0 c,
    DACC ON f1 f' c -> f_in f1 = f_in f -> f_bits f1 = f_bits f - c0 -> DACC ON f f' (c0 + c).
  Proof.
    intros f f1 f' c0 c [HF (p & e & Hp & He & Ei & Eb & C1 & C2)] E1 E2. split; [exact HF|].
    exists p, e. rewrite E1 in Ei. rewrite E2 in Eb, C1, C2. repeat split; try lia.
  Qed.

  (* [comment removed for export] *)
  Lemma dodist_root : forall k f,
    FB ON f -> 15 <= f_bits f -> 3 <= f_len f <= 258 -> x_beg x <= f_out f -> f_out f + f_len f <= ON ->
    exists c, 1 <= c <= 15 /\
    match dodist (S (S k)) x s (code_at s (is_distcode s) (f_hold f mod 2 ^ is_distbits s)) f with
    | FCont f' => DACC ON f f' c /\ f_out f' = f_out f + f_len f
    | FBreak f' m msg => DACC ON f f' c /\ f_out f' = f_out f /\ m = BAD /\ msg <> None
    end.
  Proof.
    intros k f HF Hb Hlen Hbeg Hroom. pose proof HF as (B1 & B2 & B3 & B4 & B5).
    pose proof (T_root _ _ _ _ HT) as HR15.
    pose proof (ridx_range _ _ _ _ HT (f_hold f)) as XR.
    destruct (root_cell _ _ _ _ HT _ XR) as (Hbits & RL & RN).
    set (getD := code_at s (is_distcode s)) in *. set (root := is_distbits s) in *.
    set (here := getD (f_hold f mod 2 ^ root)) in *.
    destruct (is_linkb here) eqn:HL.
    - (* [comment removed for export] *)
      destruct (RL eq_refl) as (Hbr & Hop & Hv1 & Hv2).
      rewrite dodist_S. cbv zeta.
      rewrite (land16_small (code_op here)) by lia. rewrite (land64_small (code_op here)) by lia. cbn [Z.eqb negb].
      destruct (FB_fdrop ON f (code_bits here) HF ltac:(lia)) as (HF1 & E1i & E1o & E1b & E1h & E1l & E1d & E1ob).
      set (f1 := fdrop f (code_bits here)) in *.
      rewrite E1h. rewrite (shiftr_land_zmask (f_hold f) (code_bits here) (code_op here)) by lia.
      set (y := f_hold f mod 2 ^ (code_bits here + code_op here) / 2 ^ code_bits here).
      pose proof (subidx_range (f_hold f) (code_bits here) (code_op here) ltac:(lia) ltac:(lia)) as Hy. fold y in Hy.
      destruct (sub_cell _ _ _ _ HT (f_hold f mod 2 ^ root) y XR HL Hy) as (Sb & SNL & SSh).
      fold getD root in Sb, SNL, SSh. fold here in Sb, SNL, SSh. fold getD.
      set (here2 := getD (code_val here + y)) in *.
      pose proof (dodist_term k here2 f1 HF1 ltac:(lia) ltac:(rewrite E1b; lia) ltac:(rewrite E1l; exact Hlen)
                    ltac:(rewrite E1o; exact Hbeg) ltac:(rewrite E1o, E1l; exact Hroom) SSh) as DT.
      exists (code_bits here + code_bits here2). split; [lia|].
      revert DT. destruct (dodist (S k) x s here2 f1) as [f'|f' m msg]; intros DT.
      + destruct DT as [DA EO]. split; [exact (DACC_shift f f1 f' _ _ DA E1i E1b)|]. rewrite EO, E1o, E1l. reflexivity.
      + destruct DT as (DA & EO & Hm & Hmsg). split; [exact (DACC_shift f f1 f' _ _ DA E1i E1b)|]. rewrite EO, E1o. repeat split; assumption.
    - (* [comment removed for export] *)
      destruct (RN eq_refl) as [Hbr SH].
      exists (code_bits here). split; [lia|].
      exact (dodist_term (S k) here f HF ltac:(lia) ltac:(lia) Hlen Hbeg Hroom SH).
  Qed.
End Dodist.
