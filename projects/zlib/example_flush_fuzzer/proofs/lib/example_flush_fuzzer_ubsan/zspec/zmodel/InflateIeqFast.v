(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia FunctionalExtensionality.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import
  Prog ZIface InflateState Inftrees InflateFast InflateArms Inflate InflateGarbBase InflateGarbFast InflateGarb
  InflateInv InflateInvTab InflateInvKit InflateInvFastA InflateInvFastB.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateIeq InflateIeqKit InflateIeqArms2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Lemma loopZ_lock2 : forall {A} (R : A -> A -> Prop) (step1 step2 : A -> bool * A) n a1 a2,
  R a1 a2 ->
  (forall a1 a2, R a1 a2 -> fst (step1 a1) = fst (step2 a2) /\ R (snd (step1 a1)) (snd (step2 a2))) ->
  R (loopZ n step1 a1) (loopZ n step2 a2).
Proof.
  intros A R step1 step2 n. enough (G : forall k a1 a2, R a1 a2 ->
    (forall a1 a2, R a1 a2 -> fst (step1 a1) = fst (step2 a2) /\ R (snd (step1 a1)) (snd (step2 a2))) ->
    R (loopZ (Z.of_nat k) step1 a1) (loopZ (Z.of_nat k) step2 a2)).
  { intros a1 a2 H HS. destruct (Z.le_gt_cases n 0).
    - rewrite !loopZ_le0 by lia. exact H.
    - rewrite <- (Z2Nat.id n) by lia. apply G; assumption. }
  induction k as [|k IH]; intros a1 a2 H HS.
  - rewrite !loopZ_le0 by lia. exact H.
  - rewrite !(loopZ_step (Z.of_nat (S k))) by lia. destruct (HS a1 a2 H) as [E HR].
    destruct (step1 a1) as [c1 b1]; destruct (step2 a2) as [c2 b2]. cbn [fst snd] in E, HR. subst c2.
    replace (Z.of_nat (S k) - 1) with (Z.of_nat k) by lia.
    destruct c1; [apply IH; [exact HR | exact HS] | exact HR].
Qed.


Section Win.
  Variables (x1 x2 : ffx).
  Hypothesis Xin : x_input x2 = x_input x1.

  Lemma cp1_out : forall f j, f_from f = FOut j -> cp1 x2 f = cp1 x1 f.
  Proof. intros [i o h b l d op fr ob] j E. cbn in E. subst fr. reflexivity. Qed.

  Lemma cp1_win : forall f j, f_from f = FWin j -> arr_get (x_window x2) j = arr_get (x_window x1) j -> cp1 x2 f = cp1 x1 f.
  Proof. intros [i o h b l d op fr ob] j E W. cbn in E. subst fr. unfold cp1. cbn [f_from]. rewrite W. reflexivity. Qed.

  Lemma cpn_out : forall n f j, f_from f = FOut j -> cpn x2 n f = cpn x1 n f.
  Proof.
    induction n as [|n IH]; intros f j E; [reflexivity|]. cbn [cpn].
    rewrite (cp1_out f j E). apply (IH _ (j + 1)). destruct f as [i o h b l d op fr ob]; cbn in E |- *. subst fr. reflexivity.
  Qed.

  Lemma cpn_win : forall n f j, f_from f = FWin j ->
    (forall k, j <= k < j + Z.of_nat n -> arr_get (x_window x2) k = arr_get (x_window x1) k) ->
    cpn x2 n f = cpn x1 n f.
  Proof.
    induction n as [|n IH]; intros f j E W; [reflexivity|]. cbn [cpn].
    rewrite (cp1_win f j E) by (apply W; lia). apply (IH _ (j + 1)).
    - destruct f as [i o h b l d op fr ob]; cbn in E |- *. subst fr. reflexivity.
    - intros k Hk. apply W. lia.
  Qed.

  Lemma fpull_x : forall f, fpull x2 f = fpull x1 f.
  Proof. intros f. unfold fpull. rewrite Xin. reflexivity. Qed.
  Lemma fpull2_if_x : forall f, fpull2_if x2 f = fpull2_if x1 f.
  Proof. intros f. unfold fpull2_if. rewrite !fpull_x. reflexivity. Qed.

  Lemma copy_op_win : forall f j, 1 <= f_op f < 2 ^ 32 -> f_from f = FWin j ->
    (forall k, j <= k < j + f_op f -> arr_get (x_window x2) k = arr_get (x_window x1) k) ->
    copy_op x2 f = copy_op x1 f.
  Proof.
    intros f j Hop E W. rewrite !copy_op_eq by exact Hop. f_equal. apply (cpn_win _ _ j E). intros k Hk. apply W. lia.
  Qed.

  Lemma w3tail_win : forall f j, 0 <= f_len f < 2 ^ 32 -> f_from f = FWin j ->
    (forall k, j <= k < j + f_len f -> arr_get (x_window x2) k = arr_get (x_window x1) k) ->
    copy_tail x2 (copy_while3 x2 f) = copy_tail x1 (copy_while3 x1 f).
  Proof.
    intros f j Hl E W. rewrite !copy_w3_tail by exact Hl. f_equal. apply (cpn_win _ _ j E). intros k Hk. apply W. lia.
  Qed.
  Lemma w3tail_out : forall f j, 0 <= f_len f < 2 ^ 32 -> f_from f = FOut j ->
    copy_tail x2 (copy_while3 x2 f) = copy_tail x1 (copy_while3 x1 f).
  Proof. intros f j Hl E. rewrite !copy_w3_tail by exact Hl. f_equal. apply (cpn_out _ _ j E). Qed.

  Lemma from_cp1_out : forall x f j, f_from f = FOut j -> f_from (cp1 x f) = FOut (j + 1).
  Proof. intros x [i o h b l d op fr ob] j E. cbn in E |- *. subst fr. reflexivity. Qed.

  Lemma d3tail_out : forall f j, f_from f = FOut j ->
    copy_tail x2 (copy_do3 x2 f) = copy_tail x1 (copy_do3 x1 f).
  Proof.
    intros f j E.
    set (R := fun a b : ffs => b = a /\ exists j, f_from a = FOut j).
    assert (HR : R (copy_do3 x2 f) (copy_do3 x1 f)).
    { unfold copy_do3. apply loopZ_lock2.
      - subst R. cbv beta. split; [reflexivity | exists j; exact E].
      - subst R. cbv beta. intros a b [-> (j' & E')].
        pose proof (from_cp1_out x1 _ _ E') as E1. pose proof (from_cp1_out x1 _ _ E1) as E2. pose proof (from_cp1_out x1 _ _ E2) as E3.
        rewrite (cp1_out a j' E'), (cp1_out _ _ E1), (cp1_out _ _ E2). cbn [fst snd].
        split; [reflexivity|]. split; [reflexivity|]. exists (j' + 1 + 1 + 1).
        destruct (cp1 x1 (cp1 x1 (cp1 x1 a))) as [i o h b l d op fr ob]; cbn in E3 |- *. exact E3. }
    subst R. cbv beta in HR. destruct HR as [EE [j' E']]. rewrite EE. unfold copy_tail.
    pose proof (from_cp1_out x1 _ _ E') as E1.
    rewrite (cp1_out _ _ E'), (cp1_out _ _ E1). reflexivity.
  Qed.
End Win.


Lemma dodist_md : forall k x s here f,
  match dodist k x s here f with FCont _ => True | FBreak _ md _ => md = BAD \/ md = TYPE end.
Proof.
  induction k as [|k IH]; intros x s here f; [exact I|]. cbn [dodist].
  destruct (negb (Z.land (code_op here) 16 =? 0)).
  - cbv zeta. destruct (_ <? _); [| exact I]. destruct (_ && _); [left; reflexivity|]. exact I.
  - destruct (Z.land (code_op here) 64 =? 0); [apply IH | left; reflexivity].
Qed.

Lemma dolen_md : forall k x s here f,
  match dolen k x s here f with FCont _ => True | FBreak _ md _ => md = BAD \/ md = TYPE end.
Proof.
  induction k as [|k IH]; intros x s here f; [exact I|]. cbn [dolen].
  destruct (code_op here =? 0); [exact I|].
  destruct (negb (Z.land (code_op here) 16 =? 0)); [apply dodist_md|].
  destruct (Z.land (code_op here) 64 =? 0); [apply IH|].
  destruct (negb (Z.land (code_op here) 32 =? 0)); [right | left]; reflexivity.
Qed.

Lemma fast_loop_md : forall n x s F f0,
  (forall f, F f = match fast_trip x s f with
                   | FCont f' => if (f_in f' <? x_last x) && (f_out f' <? x_end x) then inl f' else inr (f', None)
                   | FBreak f' mode msg => inr (f', Some (mode, msg)) end) ->
  match iterZ n F (fun f => (f, @None (Z * option Z))) f0 with
  | (_, Some (md, _)) => md = BAD \/ md = TYPE
  | (_, None) => True
  end.
Proof.
  intros n x s F f0 HF.
  enough (G : forall k f, match iterZ (Z.of_nat k) F (fun f => (f, @None (Z * option Z))) f with
                        | (_, Some (md, _)) => md = BAD \/ md = TYPE | (_, None) => True end).
  { destruct (Z.le_gt_cases n 0); [rewrite iterZ_le0 by lia; exact I|]. rewrite <- (Z2Nat.id n) by lia. apply G. }
  induction k as [|k IH]; intros f; [rewrite iterZ_le0 by lia; exact I|].
  rewrite iterZ_step by lia. rewrite HF. unfold fast_trip.
  pose proof (dolen_md 4 x s (code_at s (is_lencode s) (Z.land (f_hold (fpull2_if x f)) (x_lmask x))) (fpull2_if x f)) as M.
  destruct (dolen 4 x s _ (fpull2_if x f)) as [f'|f' md msg].
  - destruct (_ && _); [| exact I]. replace (Z.of_nat (S k) - 1) with (Z.of_nat k) by lia. apply IH.
  - exact M.
Qed.


Section Trip.
  Variables (s1 s2 : inflate_state) (x1 x2 : ffx).
  Hypothesis Xin : x_input x2 = x_input x1.
  Hypothesis Xlast : x_last x2 = x_last x1.
  Hypothesis Xbeg : x_beg x2 = x_beg x1.
  Hypothesis Xend : x_end x2 = x_end x1.
  Hypothesis Xws : x_wsize x2 = x_wsize x1.
  Hypothesis Xwh : x_whave x2 = x_whave x1.
  Hypothesis Xwn : x_wnext x2 = x_wnext x1.
  Hypothesis Xlm : x_lmask x2 = x_lmask x1.
  Hypothesis Xdm : x_dmask x2 = x_dmask x1.
  Hypothesis Xsane : x_sane x2 = x_sane x1.
  Hypothesis Xsane1 : x_sane x1 <> 0.
  Hypothesis WIN : forall i, 0 <= i < x_whave x1 -> arr_get (x_window x2) i = arr_get (x_window x1) i.
  Hypothesis WD1 : 0 <= x_whave x1 <= x_wsize x1.
  Hypothesis WD2 : 0 <= x_wnext x1 <= x_wsize x1.
  Hypothesis WD3 : x_wsize x1 <> 0 -> x_whave x1 < x_wsize x1 -> x_wnext x1 = x_whave x1.
  Hypothesis LC : is_lencode s2 = is_lencode s1.
  Hypothesis DC : is_distcode s2 = is_distcode s1.
  Hypothesis CO : forall i, 0 <= i < is_next s1 -> arr_get (is_codes s2) i = arr_get (is_codes s1) i.
  Hypothesis TL : TV LENS (is_codes s1) (is_next s1) (is_lencode s1) (is_lenbits s1).
  Hypothesis TD : TV DISTS (is_codes s1) (is_next s1) (is_distcode s1) (is_distbits s1).
  Hypothesis Xlm1 : x_lmask x1 = zmask (is_lenbits s1).
  Hypothesis Xdm1 : x_dmask x1 = zmask (is_distbits s1).

  Lemma read_root : forall ty p rb, TV ty (is_codes s1) (is_next s1) p rb ->
    forall h, code_at s2 p (Z.land h (zmask rb)) = code_at s1 p (Z.land h (zmask rb)).
  Proof.
    intros ty [off| |] rb T h; cbn [code_at]; [| reflexivity | reflexivity].
    destruct T as (ext & Ho & He & T). destruct (tab_ok_root _ _ _ _ T) as (R1 & R2 & _).
    pose proof (zmask_index h rb ltac:(lia)). apply CO. lia.
  Qed.

  Definition followD (e : Z) : Prop := Z.land (code_op e) 16 = 0 /\ Z.land (code_op e) 64 = 0.
  Definition followL (e : Z) : Prop := code_op e <> 0 /\ followD e.
  Fixpoint okn (fol : Z -> Prop) (p : codeptr) (n : nat) (e : Z) : Prop :=
    match n with
    | O => True
    | S n' => fol e -> forall h,
        code_at s2 p (code_val e + Z.land h (zmask (code_op e))) = code_at s1 p (code_val e + Z.land h (zmask (code_op e)))
        /\ okn fol p n' (code_at s1 p (code_val e + Z.land h (zmask (code_op e))))
    end.

  Lemma okn_nofollow : forall fol p n e, ~ fol e -> okn fol p n e.
  Proof. intros fol p [|n] e NF; cbn; [exact I|]. intros F. exfalso. exact (NF F). Qed.

  Lemma okn_fixed : forall fol p n e, match p with CDyn _ => False | _ => True end -> okn fol p n e.
  Proof.
    intros fol p n. induction n as [|n IH]; intros e Hp; cbn; [exact I|]. intros _ h.
    destruct p as [off| |]; [destruct Hp| |]; (split; [reflexivity | apply IH; exact I]).
  Qed.

  Lemma term_LENS_nofollow : forall mb e, term_ok LENS mb e = true -> ~ followL e.
  Proof.
    intros mb e T [NZ [L16 L64]]. apply term_ok_LENS in T. destruct T as (_ & [[O _] | [(O & _) | [O _]]]).
    - exact (NZ O).
    - destruct (op_base_tests (code_op e) ltac:(lia)) as (O16 & _). lia.
    - exact (O L64).
  Qed.
  Lemma term_DISTS_nofollow : forall mb e, term_ok DISTS mb e = true -> ~ followD e.
  Proof.
    intros mb e T [L16 L64]. apply term_ok_DISTS in T. destruct T as (_ & [(O & _) | [O _]]).
    - destruct (op_base_tests (code_op e) ltac:(lia)) as (O16 & _). lia.
    - exact (O L64).
  Qed.

  Lemma okn_root : forall ty (fol : Z -> Prop) p rb, TV ty (is_codes s1) (is_next s1) p rb ->
    (forall mb e, term_ok ty mb e = true -> ~ fol e) ->
    forall n h, okn fol p n (code_at s1 p (Z.land h (zmask rb))).
  Proof.
    intros ty fol p rb T NF n h. destruct p as [off| |]; [| apply okn_fixed; exact I | apply okn_fixed; exact I].
    destruct T as (ext & Ho & He & T).
    destruct (tab_ok_root _ _ _ _ T) as (R1 & R2 & _).
    pose proof (zmask_index h rb ltac:(lia)) as Hx.
    destruct (tab_root_entry ty _ rb ext (Z.land h (zmask rb)) T Hx) as (B & R & RE & [[NL TM] | (Q1 & Q2 & Q3 & Q4 & SUB)]).
    - apply okn_nofollow. exact (NF _ _ TM).
    - destruct n as [|n]; cbn [okn]; [exact I|]. intros _ h'. cbn [code_at cat] in *.
      pose proof (zmask_index h' (code_op (arr_get (is_codes s1) (off + Z.land h (zmask rb)))) ltac:(lia)) as Hx'.
      split.
      + apply CO. lia.
      + apply okn_nofollow. destruct (SUB (Z.land h' (zmask (code_op (arr_get (is_codes s1) (off + Z.land h (zmask rb)))))) Hx') as [_ TM'].
        exact (NF _ _ TM').
  Qed.

  Local Notation lc := (is_lencode s1).
  Local Notation dc := (is_distcode s1).

  Lemma fpull_fx : fpull x2 = fpull x1.
  Proof. extensionality f. apply (fpull_x x1 x2 Xin). Qed.
  Lemma fpull2_if_fx : fpull2_if x2 = fpull2_if x1.
  Proof. extensionality f. apply (fpull2_if_x x1 x2 Xin). Qed.

  Ltac xrw := rewrite ?fpull_fx, ?fpull2_if_fx, ?Xin, ?Xlast, ?Xbeg, ?Xend, ?Xws, ?Xwh, ?Xwn, ?Xlm, ?Xdm, ?Xsane.

  Definition DPRE (x : ffx) (here : Z) (f : ffs) : ffs :=
    let op := code_bits here in
    let f := fdrop f op in
    let op := code_op here in
    let f := fset_dist f (code_val here) in
    let op := Z.land op 15 in
    let f := if f_bits f <? op then
               let f := fpull x f in
               if f_bits f <? op then fpull x f else f
             else f in
    let f := fset_dist f (wrap32 (f_dist f + Z.land (wrap32 (f_hold f)) (zmask op))) in
    fdrop f op.
  Definition DTAIL (x : ffx) (f : ffs) : fstep :=
    let op := wrap32 (f_out f - x_beg x) in
    if op <? f_dist f then
      let op := wrap32 (f_dist f - op) in
      if (x_whave x <? op) && negb (x_sane x =? 0) then
        FBreak (fset_op f op) BAD (Some MSG_invalid_distance_too_far_back)
      else
      let f := fset_op f op in
      let f :=
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
          else f in
      let f := copy_while3 x f in
      FCont (copy_tail x f)
    else
      let f := fset_from f (FOut (f_out f - f_dist f)) in
      let f := copy_do3 x f in
      FCont (copy_tail x f).

  Lemma dodist_S_dist : forall k x s here f, Z.land (code_op here) 16 <> 0 ->
    dodist (S k) x s here f = DTAIL x (DPRE x here f).
  Proof.
    intros k x s here f H. cbn [dodist]. rewrite (proj2 (Z.eqb_neq _ _) H). cbn [negb]. unfold DTAIL, DPRE. reflexivity.
  Qed.

  Lemma DPRE_x : forall here f, DPRE x2 here f = DPRE x1 here f.
  Proof. intros here f. unfold DPRE. xrw. reflexivity. Qed.

  Lemma DPRE_fields : forall x here f, 0 <= f_dist (DPRE x here f) < 2 ^ 32 /\ f_len (DPRE x here f) = f_len f.
  Proof.
    intros x here [i o h b l d op fr ob]. unfold DPRE. cbv zeta.
    destruct (_ <? _); [destruct (_ <? _)|]; cbn; (split; [apply wrap32_range | reflexivity]).
  Qed.

  Lemma copy_op_fields : forall x f, 1 <= f_op f < 2 ^ 32 ->
    f_len (copy_op x f) = f_len f /\ f_dist (copy_op x f) = f_dist f /\ f_out (copy_op x f) = f_out f + f_op f.
  Proof.
    intros x f H. rewrite copy_op_eq by exact H.
    destruct (cpn_fields x (Z.to_nat (f_op f)) f) as (_ & _ & _ & L & D & _ & O & _).
    rewrite f_len_set_op. split; [exact L|].
    destruct (cpn x (Z.to_nat (f_op f)) f) as [i o hh b l d op fr ob]; cbn in *. split; [exact D | lia].
  Qed.

  Lemma DTAIL_cong : forall f, 0 <= f_len f < 2 ^ 32 -> 0 <= f_dist f < 2 ^ 32 -> DTAIL x2 f = DTAIL x1 f.
  Proof.
    intros [i o h b l d op fr ob] HL HD. cbn in HL, HD. unfold DTAIL. xrw. fred.
    set (opw := wrap32 (o - x_beg x1)). pose proof (wrap32_range (o - x_beg x1)) as Ropw. fold opw in Ropw.
    destruct (Z.ltb_spec opw d) as [LT|GE].
    2:{ f_equal. apply (d3tail_out x1 x2 _ (o - d)). reflexivity. }
    rewrite (wrap32_id (d - opw)) by lia.
    destruct (Z.ltb_spec (x_whave x1) (d - opw)) as [FAR|NEAR]; cbn [andb].
    { rewrite (proj2 (Z.eqb_neq _ _) Xsane1). reflexivity. }
    fred.
    assert (WLE : x_wnext x1 <= x_whave x1) by (destruct (Z.eq_dec (x_wsize x1) 0); [lia|]; destruct (Z_lt_le_dec (x_whave x1) (x_wsize x1)); [rewrite (WD3 ltac:(lia) ltac:(lia)); lia | lia]).
    destruct (Z.eqb_spec (x_wnext x1) 0) as [W0|W0].
    -
      assert (FULL : x_whave x1 = x_wsize x1) by (destruct (Z.eq_dec (x_wsize x1) 0); [lia|]; destruct (Z_lt_le_dec (x_whave x1) (x_wsize x1)); [pose proof (WD3 ltac:(lia) ltac:(lia)); lia | lia]).
      destruct (Z.ltb_spec (d - opw) l) as [L1|L1].
      + rewrite (wrap32_id (l - (d - opw))) by lia.
        set (F := mkF i o h b (l - (d - opw)) d (d - opw) (FWin (x_wsize x1 - (d - opw))) ob).
        rewrite (copy_op_win x1 x2 F (x_wsize x1 - (d - opw))); [| cbn; lia | reflexivity | intros k Hk; apply WIN; cbn in Hk; lia].
        destruct (copy_op_fields x1 F ltac:(cbn; lia)) as (FL & FD & FO).
        f_equal. apply (w3tail_out x1 x2 _ (f_out (copy_op x1 F) - f_dist (copy_op x1 F))); [| reflexivity].
        fred. destruct (copy_op x1 F); cbn in FL |- *. subst. cbn in HL. lia.
      + f_equal. apply (w3tail_win x1 x2 _ (x_wsize x1 - (d - opw))); [cbn; lia | reflexivity | intros k Hk; apply WIN; cbn in Hk; lia].
    - destruct (Z.ltb_spec (x_wnext x1) (d - opw)) as [WR|NW].
      +
        assert (FULL : x_whave x1 = x_wsize x1) by (destruct (Z_lt_le_dec (x_whave x1) (x_wsize x1)); [pose proof (WD3 ltac:(lia) ltac:(lia)); lia | lia]).
        rewrite (wrap32_id (d - opw - x_wnext x1)) by lia.
        destruct (Z.ltb_spec (d - opw - x_wnext x1) l) as [L1|L1].
        * rewrite (wrap32_id (l - (d - opw - x_wnext x1))) by lia.
          set (F := mkF i o h b (l - (d - opw - x_wnext x1)) d (d - opw - x_wnext x1) (FWin (x_wsize x1 + x_wnext x1 - (d - opw))) ob).
          rewrite (copy_op_win x1 x2 F (x_wsize x1 + x_wnext x1 - (d - opw))); [| cbn; lia | reflexivity | intros k Hk; apply WIN; cbn in Hk; lia].
          destruct (copy_op_fields x1 F ltac:(cbn; lia)) as (FL & FD & FO).
          destruct (copy_op x1 F) as [i2 o2 h2 b2 l2 d2 op2 fr2 ob2] eqn:EF. cbn in FL, FD, FO. fred. subst l2 d2.
          destruct (Z.ltb_spec (x_wnext x1) (l - (d - opw - x_wnext x1))) as [L2|L2].
          -- rewrite (wrap32_id (l - (d - opw - x_wnext x1) - x_wnext x1)) by lia.
             set (F2 := mkF i2 o2 h2 b2 (l - (d - opw - x_wnext x1) - x_wnext x1) d (x_wnext x1) (FWin 0) ob2).
             rewrite (copy_op_win x1 x2 F2 0); [| cbn; lia | reflexivity | intros k Hk; apply WIN; cbn in Hk; lia].
             destruct (copy_op_fields x1 F2 ltac:(cbn; lia)) as (FL2 & FD2 & FO2).
             f_equal. apply (w3tail_out x1 x2 _ (f_out (copy_op x1 F2) - f_dist (copy_op x1 F2))); [| reflexivity].
             fred. destruct (copy_op x1 F2); cbn in FL2 |- *. subst. cbn in HL. lia.
          -- f_equal. apply (w3tail_win x1 x2 _ 0); [cbn; lia | reflexivity | intros k Hk; apply WIN; cbn in Hk; lia].
        * f_equal. apply (w3tail_win x1 x2 _ (x_wsize x1 + x_wnext x1 - (d - opw))); [cbn; lia | reflexivity | intros k Hk; apply WIN; cbn in Hk; lia].
      +
        destruct (Z.ltb_spec (d - opw) l) as [L1|L1].
        * rewrite (wrap32_id (l - (d - opw))) by lia.
          set (F := mkF i o h b (l - (d - opw)) d (d - opw) (FWin (x_wnext x1 - (d - opw))) ob).
          rewrite (copy_op_win x1 x2 F (x_wnext x1 - (d - opw))); [| cbn; lia | reflexivity | intros k Hk; apply WIN; cbn in Hk; lia].
          destruct (copy_op_fields x1 F ltac:(cbn; lia)) as (FL & FD & FO).
          f_equal. apply (w3tail_out x1 x2 _ (f_out (copy_op x1 F) - f_dist (copy_op x1 F))); [| reflexivity].
          fred. destruct (copy_op x1 F); cbn in FL |- *. subst. cbn in HL. lia.
        * f_equal. apply (w3tail_win x1 x2 _ (x_wnext x1 - (d - opw))); [cbn; lia | reflexivity | intros k Hk; apply WIN; cbn in Hk; lia].
  Qed.

  Lemma dodist_cong : forall k here f, okn followD dc k here -> 0 <= f_len f < 2 ^ 32 ->
    dodist k x2 s2 here f = dodist k x1 s1 here f.
  Proof.
    induction k as [|k IH]; intros here f OK HL; [reflexivity|].
    destruct (Z.eqb_spec (Z.land (code_op here) 16) 0) as [L16|L16].
    -
      cbn [dodist]. rewrite DC, L16. cbn [Z.eqb negb].
      destruct (Z.eqb_spec (Z.land (code_op here) 64) 0) as [L64|L64]; [| reflexivity].
      cbn [okn] in OK. destruct (OK (conj L16 L64) (f_hold (fdrop f (code_bits here)))) as [E OK'].
      rewrite E. apply IH; [exact OK'|]. destruct f; cbn in HL |- *. exact HL.
    - rewrite !(dodist_S_dist k) by exact L16. rewrite DPRE_x.
      destruct (DPRE_fields x1 here f) as [D L]. apply DTAIL_cong; [rewrite L; exact HL | exact D].
  Qed.

  Definition LPRE (x : ffx) (here : Z) (f : ffs) : ffs :=
    let op := code_bits here in
    let f := fdrop f op in
    let op := code_op here in
    let f := fset_len f (code_val here) in
    let op := Z.land op 15 in
    let f := if negb (op =? 0) then
               let f := if f_bits f <? op then fpull x f else f in
               let f := fset_len f (wrap32 (f_len f + Z.land (wrap32 (f_hold f)) (zmask op))) in
               fdrop f op
             else f in
    fpull2_if x f.
  Lemma dolen_S_len : forall k x s here f, code_op here <> 0 -> Z.land (code_op here) 16 <> 0 ->
    dolen (S k) x s here f =
      (let f := LPRE x here f in
       dodist 4 x s (code_at s (is_distcode s) (Z.land (f_hold f) (x_dmask x))) f).
  Proof.
    intros k x s here f H0 H16. cbn [dolen]. rewrite (proj2 (Z.eqb_neq _ _) H0). rewrite (proj2 (Z.eqb_neq _ _) H16). cbn [negb].
    unfold LPRE. reflexivity.
  Qed.
  Lemma LPRE_x : forall here f, LPRE x2 here f = LPRE x1 here f.
  Proof. intros here f. unfold LPRE. xrw. reflexivity. Qed.
  Lemma LPRE_len : forall x here f, 0 <= f_len (LPRE x here f) < 2 ^ 32 \/ f_len (LPRE x here f) = code_val here.
  Proof.
    intros x here [i o h b l d op fr ob]. unfold LPRE. cbv zeta.
    destruct (negb _).
    - left. unfold fpull2_if. destruct (_ <? _); destruct (_ <? _); fred; apply wrap32_range.
    - right. unfold fpull2_if. destruct (_ <? _); fred; reflexivity.
  Qed.

  Lemma dolen_cong : forall k here f, okn followL lc k here ->
    dolen k x2 s2 here f = dolen k x1 s1 here f.
  Proof.
    induction k as [|k IH]; intros here f OK; [reflexivity|].
    destruct (Z.eqb_spec (code_op here) 0) as [O0|O0].
    { cbn [dolen]. rewrite O0. reflexivity. }
    destruct (Z.eqb_spec (Z.land (code_op here) 16) 0) as [L16|L16].
    -
      cbn [dolen]. rewrite LC, L16, (proj2 (Z.eqb_neq _ _) O0). cbn [Z.eqb negb].
      destruct (Z.eqb_spec (Z.land (code_op here) 64) 0) as [L64|L64]; [| reflexivity].
      cbn [okn] in OK. destruct (OK (conj O0 (conj L16 L64)) (f_hold (fdrop f (code_bits here)))) as [E OK'].
      rewrite E. apply IH. exact OK'.
    -
      rewrite !(dolen_S_len k) by assumption. cbv zeta. rewrite LPRE_x, DC. xrw. rewrite Xdm1.
      rewrite (read_root DISTS dc (is_distbits s1) TD).
      apply dodist_cong.
      + apply (okn_root DISTS followD dc (is_distbits s1) TD). exact term_DISTS_nofollow.
      + destruct (LPRE_len x1 here f) as [R | ->]; [exact R|]. pose proof (InflateGarbBase.code_val_bound here). lia.
  Qed.

  Theorem fast_trip_cong : forall f, fast_trip x2 s2 f = fast_trip x1 s1 f.
  Proof.
    intros f. unfold fast_trip. xrw. rewrite LC, Xlm1.
    rewrite (read_root LENS lc (is_lenbits s1) TL).
    apply dolen_cong. apply (okn_root LENS followL lc (is_lenbits s1) TL). exact term_LENS_nofollow.
  Qed.
End Trip.


Theorem FASTC : forall s1 s2 c d r, is_mode s1 = LEN -> CC s1 -> SEQX (chk_guard s1 r) s1 s2 ->
  WEQ (LOAD (inflate_fast (RESTORE (mkW s1 c r)))) (LOAD (inflate_fast (RESTORE (mkW s2 (cdt c d) r)))).
Proof.
  intros s1 s2 c d r Hm HC SQ.
  dstate1 s1; dstate2 s2; dcall c; dregs r; proj_cbn_in Hm; subst; seq_open SQ.
  destruct HC as (HTL & HTD & HW). unfold TVL in HTL. unfold TVD in HTD. unfold WD in HW. proj_cbn_in HTL. proj_cbn_in HTD. proj_cbn_in HW.
  destruct HW as (W1 & W2 & W3 & HS). subst f_sane.
  unfold RESTORE, LOAD, inflate_fast, cdt. wred0.
  match goal with |- context [mkFX ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 f_window ?a9 ?a10 ?a11] =>
    set (X1 := mkFX a1 a2 a3 a4 a5 a6 a7 f_window a9 a10 a11); set (X2 := mkFX a1 a2 a3 a4 a5 a6 a7 g_window a9 a10 a11) end.
  lazymatch goal with |- WEQ ?A ?B =>
    match A with context [fast_trip X1 ?S] => set (S1 := S) end;
    match B with context [fast_trip X2 ?S] => set (S2 := S) end end.
  lazymatch goal with |- WEQ ?A ?B =>
    match A with context [iterZ ?n ?F ?d ?a] => set (F1 := F); set (f0 := a); set (NN := n);
    match B with context [iterZ n ?G d a] => set (F2 := G) end end end.
  assert (EF : F2 = F1).
  { subst F1 F2. extensionality f.
    rewrite (fast_trip_cong S1 S2 X1 X2); try reflexivity.
    - cbn. lia.
    - exact WIq.
    - exact W1.
    - exact W2.
    - exact W3.
    - exact CO.
    - exact HTL.
    - exact HTD. }
  rewrite EF.
  pose proof (fast_loop_md NN X1 S1 F1 f0 ltac:(intros; reflexivity)) as MD. revert MD.
  destruct (iterZ NN F1 (fun f => (f, None)) f0) as [f' mm]. intros MD.
  subst X1 X2 S1 S2. clear EF F1 F2.
  destruct mm as [[md [msg|]]|]; [destruct MD as [-> | ->] | destruct MD as [-> | ->] |]; wred0; fred; weq_auto.
  all: match goal with |- ?G => idtac "LEFTF:" G end.
Qed.
