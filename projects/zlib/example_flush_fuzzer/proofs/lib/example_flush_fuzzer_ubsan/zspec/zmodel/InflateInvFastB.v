(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import
  Prog ZIface InflateState Inftrees InflateFast InflateArms InflateGarbBase InflateGarbFast.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateInv InflateInvRun InflateInvTab InflateInvFastA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Ltac fred :=
  cbv beta iota zeta delta [f_in f_out f_hold f_bits f_len f_dist f_op f_from f_ob
                            fset_in fset_out fset_hold fset_bits fset_len fset_dist fset_op fset_from fset_ob fsf].
Tactic Notation "fred" "in" hyp(H) :=
  cbv beta iota zeta delta [f_in f_out f_hold f_bits f_len f_dist f_op f_from f_ob
                            fset_in fset_out fset_hold fset_bits fset_len fset_dist fset_op fset_from fset_ob fsf] in H.
Ltac bsimp := cbn [andb orb negb xorb Z.eqb Z.ltb Z.leb Z.compare Pos.compare Pos.compare_cont Pos.eqb].

Definition FB (f : ffs) : Prop := 0 <= f_bits f < 64 /\ 0 <= f_hold f < 2 ^ f_bits f.

Lemma fpull_eq : forall x i o h b l d op fr ob,
  0 <= b -> b + 8 <= 64 -> 0 <= h < 2 ^ b -> 0 <= arr_get (x_input x) i < 256 ->
  fpull x (mkF i o h b l d op fr ob) = mkF (i + 1) o (h + arr_get (x_input x) i * 2 ^ b) (b + 8) l d op fr ob
  /\ 0 <= h + arr_get (x_input x) i * 2 ^ b < 2 ^ (b + 8).
Proof.
  intros x i o h b l d op fr ob Hb Hb8 Hh Hby. unfold fpull. fred.
  destruct (pull_acc h b (arr_get (x_input x) i) Hb Hb8 Hh Hby) as [EW RG]. rewrite EW. rewrite (wrap32_id (b + 8)) by lia.
  split; [reflexivity | exact RG].
Qed.

Lemma fdrop_eq : forall i o h b l d op fr ob n,
  0 <= n <= b -> b < 64 -> 0 <= h < 2 ^ b ->
  fdrop (mkF i o h b l d op fr ob) n = mkF i o (Z.shiftr h n) (b - n) l d op fr ob /\ 0 <= Z.shiftr h n < 2 ^ (b - n).
Proof.
  intros i o h b l d op fr ob n Hn Hb Hh. unfold fdrop. fred.
  destruct (drop_acc h b n Hn Hb Hh) as [EW RG]. rewrite EW. split; [reflexivity | exact RG].
Qed.

Lemma extra_bound : forall h n, 0 <= n -> 0 <= Z.land (wrap32 h) (zmask n) < 2 ^ n.
Proof. intros h n Hn. apply (BITSv_bound h n Hn). Qed.

Lemma ones_index : forall h n, 0 <= n -> 0 <= Z.land h (Z.ones n) < 2 ^ n.
Proof. intros h n Hn. apply land_ones_bound. exact Hn. Qed.
Lemma zmask_index : forall h n, 0 <= n <= 15 -> 0 <= Z.land h (zmask n) < 2 ^ n.
Proof. intros h n Hn. rewrite zmask_ones by lia. rewrite Z.min_l by lia. apply land_ones_bound. lia. Qed.

Lemma obytes_set : forall ON ob k v, obytes ON ob -> 0 <= v < 256 -> obytes ON (arr_set ob k v).
Proof.
  intros ON ob k v [L B] Hv. split; [rewrite arr_len_set; exact L|].
  intros i Hi. rewrite arr_get_set. destruct ((k =? i) && arr_inb ob k); [exact Hv | apply B; exact Hi].
Qed.
Lemma wrap8_range : forall z, 0 <= wrap8 z < 256.
Proof. intros z. unfold wrap8. change 255 with (Z.ones 8). apply land_ones_bound. lia. Qed.

Section Trip.
  Variables (x : ffx) (s : inflate_state) (NI NO : Z).
  Hypothesis NO32 : 0 <= NO < 2 ^ 32.
  Hypothesis NIpos : 0 <= NI.
  Hypothesis Xinb : forall i, 0 <= i < NI -> 0 <= arr_get (x_input x) i < 256.
  Hypothesis Xwinb : forall i, 0 <= i < arr_len (x_window x) -> 0 <= arr_get (x_window x) i < 256.
  Hypothesis Xbeg : x_beg x = 0.
  Hypothesis Xsane : x_sane x <> 0.
  Hypothesis Xwh : 0 <= x_whave x <= x_wsize x.
  Hypothesis Xwn : 0 <= x_wnext x <= x_wsize x.
  Hypothesis Xwlen : x_wsize x <> 0 -> arr_len (x_window x) = x_wsize x.
  Hypothesis Xws32 : x_wsize x < 2 ^ 32.
  Hypothesis Xlmask : x_lmask x = Z.ones (is_lenbits s).
  Hypothesis Xdmask : x_dmask x = Z.ones (is_distbits s).
  Variables extL extD : Z.
  Hypothesis TL : tab_ok LENS (fun i => code_at s (is_lencode s) i) (is_lenbits s) extL = true.
  Hypothesis TD : tab_ok DISTS (fun i => code_at s (is_distcode s) i) (is_distbits s) extD = true.


  Lemma dist_pre_spec : forall here i o h b l d op fr ob m,
    term_ok DISTS m here = true -> Z.land (code_op here) 16 <> 0 -> code_bits here <= b ->
    0 <= b < 64 -> 0 <= h < 2 ^ b -> 0 <= i <= NI -> 8 * (NI - i) + b - code_bits here >= 13 ->
    exists i1 h1 b1 d1,
      dist_pre x here (mkF i o h b l d op fr ob) = mkF i1 o h1 b1 l d1 op fr ob
      /\ 0 <= b1 < 64 /\ 0 <= h1 < 2 ^ b1 /\ i <= i1 <= NI
      /\ 8 * i1 - b1 = 8 * i - b + code_bits here + (code_op here - 16)
      /\ 1 <= d1 <= 32768.
  Proof.
    intros here i o h b l d op fr ob m TM O16 HB Bb Hh Hi BUD.
    pose proof (term_ok_DISTS _ _ TM) as (Hbits & [(O1 & V1 & V2 & O2) | (I64 & I16 & _)]); [| exfalso; exact (O16 I16)].
    destruct (op_base_tests (code_op here) ltac:(lia)) as (E16 & E64 & E32 & E240 & E15 & NZ).
    rewrite Z.shiftl_1_l in V2.
    assert (P2 : 2 ^ (code_op here - 16) <= 2 ^ 13) by (apply Z.pow_le_mono_r; lia). change (2 ^ 13) with 8192 in P2.
    assert (P0 : 0 < 2 ^ (code_op here - 16)) by (apply Z.pow_pos_nonneg; lia).
    unfold dist_pre. rewrite E15.
    destruct (fdrop_eq i o h b l d op fr ob (code_bits here) ltac:(lia) ltac:(lia) Hh) as [-> R1]. fred.
    destruct (Z.ltb_spec (b - code_bits here) (code_op here - 16)) as [L1|L1].
    - destruct (fpull_eq x i o (Z.shiftr h (code_bits here)) (b - code_bits here) l (code_val here) op fr ob
                 ltac:(lia) ltac:(lia) R1 ltac:(apply Xinb; lia)) as [-> R2]. fred.
      destruct (Z.ltb_spec (b - code_bits here + 8) (code_op here - 16)) as [L2|L2].
      + destruct (fpull_eq x (i + 1) o (Z.shiftr h (code_bits here) + arr_get (x_input x) i * 2 ^ (b - code_bits here)) (b - code_bits here + 8)
                   l (code_val here) op fr ob ltac:(lia) ltac:(lia) R2 ltac:(apply Xinb; lia)) as [-> R3]. fred.
        match goal with |- context [Z.land (wrap32 ?hh) (zmask ?n)] => pose proof (extra_bound hh n ltac:(lia)) as EB end.
        match goal with |- context [wrap32 (code_val here + ?v)] => rewrite (wrap32_id (code_val here + v)) by lia end.
        match goal with |- context [fdrop (mkF ?i' ?o' ?h' ?b' ?l' ?d' ?op' ?fr' ?ob') ?n] =>
          destruct (fdrop_eq i' o' h' b' l' d' op' fr' ob' n ltac:(lia) ltac:(lia) R3) as [-> R4] end.
        do 4 eexists. split; [reflexivity|]. repeat split; lia.
      + match goal with |- context [Z.land (wrap32 ?hh) (zmask ?n)] => pose proof (extra_bound hh n ltac:(lia)) as EB end.
        match goal with |- context [wrap32 (code_val here + ?v)] => rewrite (wrap32_id (code_val here + v)) by lia end.
        match goal with |- context [fdrop (mkF ?i' ?o' ?h' ?b' ?l' ?d' ?op' ?fr' ?ob') ?n] =>
          destruct (fdrop_eq i' o' h' b' l' d' op' fr' ob' n ltac:(lia) ltac:(lia) R2) as [-> R4] end.
        do 4 eexists. split; [reflexivity|]. repeat split; lia.
    - match goal with |- context [Z.land (wrap32 ?hh) (zmask ?n)] => pose proof (extra_bound hh n ltac:(lia)) as EB end.
      match goal with |- context [wrap32 (code_val here + ?v)] => rewrite (wrap32_id (code_val here + v)) by lia end.
      match goal with |- context [fdrop (mkF ?i' ?o' ?h' ?b' ?l' ?d' ?op' ?fr' ?ob') ?n] =>
        destruct (fdrop_eq i' o' h' b' l' d' op' fr' ob' n ltac:(lia) ltac:(lia) R1) as [-> R4] end.
      do 4 eexists. split; [reflexivity|]. repeat split; lia.
  Qed.


  Lemma fpull2_if_spec : forall i o h b l d op fr ob,
    0 <= b < 64 -> 0 <= h < 2 ^ b -> 0 <= i <= NI -> 8 * (NI - i) + b >= 23 ->
    exists i1 h1 b1,
      fpull2_if x (mkF i o h b l d op fr ob) = mkF i1 o h1 b1 l d op fr ob
      /\ 0 <= b1 < 64 /\ 0 <= h1 < 2 ^ b1 /\ i <= i1 <= NI /\ 15 <= b1
      /\ 8 * i1 - b1 = 8 * i - b /\ h1 mod 2 ^ b = h /\ (b1 = b \/ b1 < 31).
  Proof.
    intros i o h b l d op fr ob Bb Hh Hi BUD. unfold fpull2_if. fred.
    destruct (Z.ltb_spec b 15) as [L|L].
    - destruct (fpull_eq x i o h b l d op fr ob ltac:(lia) ltac:(lia) Hh ltac:(apply Xinb; lia)) as [-> R2].
      destruct (fpull_eq x (i + 1) o (h + arr_get (x_input x) i * 2 ^ b) (b + 8) l d op fr ob ltac:(lia) ltac:(lia) R2 ltac:(apply Xinb; lia)) as [-> R3].
      do 3 eexists. split; [reflexivity|]. split; [lia|]. split; [exact R3|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [|lia].
      pose proof (Xinb i ltac:(lia)). pose proof (Xinb (i + 1) ltac:(lia)).
      assert (P : 0 < 2 ^ b) by (apply Z.pow_pos_nonneg; lia).
      rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256.
      replace (h + arr_get (x_input x) i * 2 ^ b + arr_get (x_input x) (i + 1) * (2 ^ b * 256))
        with (h + (arr_get (x_input x) i + arr_get (x_input x) (i + 1) * 256) * 2 ^ b) by lia.
      rewrite Z.mod_add by lia. apply Z.mod_small. lia.
    - do 3 eexists. split; [reflexivity|]. repeat split; try lia. apply Z.mod_small. lia.
  Qed.

  Lemma len_pre_spec : forall here i o h b l d op fr ob m,
    term_ok LENS m here = true -> Z.land (code_op here) 16 <> 0 -> code_bits here <= b ->
    0 <= b < 64 -> 0 <= h < 2 ^ b -> 0 <= i <= NI -> 8 * (NI - i) + b - code_bits here >= 33 ->
    exists i1 h1 b1 l1,
      len_pre x here (mkF i o h b l d op fr ob) = mkF i1 o h1 b1 l1 d op fr ob
      /\ 0 <= b1 < 64 /\ 0 <= h1 < 2 ^ b1 /\ i <= i1 <= NI /\ 15 <= b1
      /\ 8 * i1 - b1 = 8 * i - b + code_bits here + (code_op here - 16)
      /\ 3 <= l1 <= 258.
  Proof.
    intros here i o h b l d op fr ob m TM O16 HB Bb Hh Hi BUD.
    pose proof (term_ok_LENS _ _ TM) as (Hbits & [(O0 & _) | [(O1 & V1 & V2 & O2) | (I64 & I16)]]);
      [exfalso; rewrite O0 in O16; apply O16; reflexivity | | exfalso; exact (O16 I16)].
    destruct (op_base_tests (code_op here) ltac:(lia)) as (E16 & E64 & E32 & E240 & E15 & NZ).
    rewrite Z.shiftl_1_l in V2.
    assert (P0 : 0 < 2 ^ (code_op here - 16)) by (apply Z.pow_pos_nonneg; lia).
    unfold len_pre. rewrite E15.
    destruct (fdrop_eq i o h b l d op fr ob (code_bits here) ltac:(lia) ltac:(lia) Hh) as [-> R1]. fred.
    destruct (Z.eqb_spec (code_op here - 16) 0) as [EZ|NZ']; bsimp.
    -
      destruct (fpull2_if_spec i o (Z.shiftr h (code_bits here)) (b - code_bits here) (code_val here) d op fr ob
                  ltac:(lia) R1 ltac:(lia) ltac:(lia)) as (i1 & h1 & b1 & -> & B1 & H1 & I1 & F1 & E1 & _ & _).
      do 4 eexists. split; [reflexivity|]. rewrite EZ in P0 |- *. change (2 ^ 0) with 1 in V2. repeat split; lia.
    - destruct (Z.ltb_spec (b - code_bits here) (code_op here - 16)) as [L1|L1].
      + destruct (fpull_eq x i o (Z.shiftr h (code_bits here)) (b - code_bits here) (code_val here) d op fr ob
                   ltac:(lia) ltac:(lia) R1 ltac:(apply Xinb; lia)) as [-> R2]. fred.
        match goal with |- context [Z.land (wrap32 ?hh) (zmask ?n)] => pose proof (extra_bound hh n ltac:(lia)) as EB end.
        match goal with |- context [wrap32 (code_val here + ?v)] => rewrite (wrap32_id (code_val here + v)) by lia end.
        match goal with |- context [fdrop (mkF ?i' ?o' ?h' ?b' ?l' ?d' ?op' ?fr' ?ob') ?n] =>
          destruct (fdrop_eq i' o' h' b' l' d' op' fr' ob' n ltac:(lia) ltac:(lia) R2) as [-> R4] end.
        match goal with |- context [fpull2_if x (mkF ?i' ?o' ?h' ?b' ?l' ?d' ?op' ?fr' ?ob')] =>
          destruct (fpull2_if_spec i' o' h' b' l' d' op' fr' ob' ltac:(lia) R4 ltac:(lia) ltac:(lia))
            as (i1 & h1 & b1 & -> & B1 & H1 & I1 & F1 & E1 & _ & _) end.
        do 4 eexists. split; [reflexivity|]. repeat split; lia.
      + match goal with |- context [Z.land (wrap32 ?hh) (zmask ?n)] => pose proof (extra_bound hh n ltac:(lia)) as EB end.
        match goal with |- context [wrap32 (code_val here + ?v)] => rewrite (wrap32_id (code_val here + v)) by lia end.
        match goal with |- context [fdrop (mkF ?i' ?o' ?h' ?b' ?l' ?d' ?op' ?fr' ?ob') ?n] =>
          destruct (fdrop_eq i' o' h' b' l' d' op' fr' ob' n ltac:(lia) ltac:(lia) R1) as [-> R4] end.
        match goal with |- context [fpull2_if x (mkF ?i' ?o' ?h' ?b' ?l' ?d' ?op' ?fr' ?ob')] =>
          destruct (fpull2_if_spec i' o' h' b' l' d' op' fr' ob' ltac:(lia) R4 ltac:(lia) ltac:(lia))
            as (i1 & h1 & b1 & -> & B1 & H1 & I1 & F1 & E1 & _ & _) end.
        do 4 eexists. split; [reflexivity|]. repeat split; lia.
  Qed.


  Definition TPOST (i o b c : Z) (r : fstep) : Prop :=
    let f' := fsf r in
    FB f' /\ obytes NO (f_ob f') /\ o <= f_out f' <= NO /\ i <= f_in f' <= NI
    /\ 8 * f_in f' - f_bits f' >= 8 * i - b + c
    /\ match r with FCont _ => o + 1 <= f_out f' | FBreak _ md _ => md = BAD \/ md = TYPE end.

  Lemma TPOST_w : forall i o b c i' b' c' r, TPOST i' o b' c' r -> i <= i' -> 8 * i' - b' + c' >= 8 * i - b + c -> TPOST i o b c r.
  Proof.
    intros i o b c i' b' c' r (A & B & C & D & E & F) H1 H2. unfold TPOST.
    split; [exact A|]. split; [exact B|]. split; [exact C|]. split; [lia|]. split; [lia | exact F].
  Qed.

  Ltac run_cpn OB OB' side :=
    match goal with |- context [cpn x ?k ?F] =>
      let G := fresh "G" in let CF := fresh "cf" in
      let ci := fresh "ci" in let co := fresh "co" in let ch := fresh "ch" in let cb := fresh "cb" in let cl := fresh "cl" in
      let cd := fresh "cd" in let cop := fresh "cop" in let cfr := fresh "cfr" in let cob := fresh "ob" in
      pose proof (cpn_obytes x NO k F Xwinb OB ltac:(rewrite ?Z2Nat.id by lia; first [assumption | (unfold src_ok; fred; side; lia)])) as OB';
      pose proof (cpn_fields x k F) as G; fred in G;
      set (CF := cpn x k F) in *; clearbody CF;
      destruct CF as [ci co ch cb cl cd cop cfr cob]; fred in G; fred in OB'; fred;
      destruct G as (-> & -> & -> & -> & -> & -> & -> & -> & ?Elen); rewrite ?Z2Nat.id in * by lia
    end.


  Lemma place_spec : forall i1 o h1 b1 l d1 opw fr ob,
    obytes NO ob -> 0 <= o -> 1 <= l <= 258 -> o + l <= NO -> 1 <= opw <= x_whave x -> d1 = o + opw ->
    let f := mkF i1 o h1 b1 l d1 opw fr ob in
    placeG x NO f = true /\
    exists o2 l2 op2 fr2 ob2, place x f = mkF i1 o2 h1 b1 l2 d1 op2 fr2 ob2
      /\ obytes NO ob2 /\ 0 <= l2 < 2 ^ 32 /\ o2 + l2 = o + l /\ o <= o2
      /\ cps_ok x NO (mkF i1 o2 h1 b1 l2 d1 op2 fr2 ob2) (Z.to_nat l2)
      /\ src_ok x NO (mkF i1 o2 h1 b1 l2 d1 op2 fr2 ob2) l2.
  Proof.
    intros i1 o h1 b1 l d1 opw fr ob OB Ho Hl Hol Hopw Hd. cbv zeta.
    assert (WS : x_wsize x <> 0) by lia. pose proof (Xwlen WS) as WL.
    unfold placeG, place. fred.
    destruct (Z.eqb_spec (x_wnext x) 0) as [W0|W0]; bsimp.
    - destruct (Z.ltb_spec opw l) as [L1|L1].
      + rewrite (wrap32_id (l - opw)) by lia. split.
        { apply copy_opG_ok; [fred; lia|]. fred. apply cps_ok_intro; fred; [lia | rewrite Z2Nat.id by lia; lia | exact I]. }
        match goal with |- context [copy_op x ?F] => rewrite (copy_op_eq x F) by (fred; lia) end. fred.
        run_cpn OB OB0 ltac:(rewrite WL).
        do 5 eexists. split; [reflexivity|]. split; [exact OB0|]. split; [lia|]. split; [lia|]. split; [lia|]. split.
        * apply cps_ok_intro; fred; lia.
        * unfold src_ok; fred. lia.
      + split; [reflexivity|].
        do 5 eexists. split; [reflexivity|]. split; [exact OB|]. split; [lia|]. split; [lia|]. split; [lia|]. split.
        * apply cps_ok_intro; fred; [lia | lia | exact I].
        * unfold src_ok; fred. rewrite WL. lia.
    - destruct (Z.ltb_spec (x_wnext x) opw) as [L2|L2].
      + rewrite (wrap32_id (opw - x_wnext x)) by lia.
        destruct (Z.ltb_spec (opw - x_wnext x) l) as [L3|L3].
        * rewrite (wrap32_id (l - (opw - x_wnext x))) by lia.
          match goal with |- context [copy_op x ?F] => rewrite (copy_op_eq x F) by (fred; lia) end. fred.
          assert (CP1 : cps_ok x NO (mkF i1 o h1 b1 (l - (opw - x_wnext x)) d1 (opw - x_wnext x) (FWin (x_wsize x + x_wnext x - opw)) ob) (Z.to_nat (opw - x_wnext x))).
          { apply cps_ok_intro; fred; [lia | rewrite Z2Nat.id by lia; lia | exact I]. }
          run_cpn OB OB0 ltac:(rewrite WL).
          destruct (Z.ltb_spec (x_wnext x) (l - (opw - x_wnext x))) as [L4|L4].
          -- rewrite (wrap32_id (l - (opw - x_wnext x) - x_wnext x)) by lia. split.
             { apply andb_true_intro; split; [apply copy_opG_ok; [fred; lia | fred; exact CP1] |].
               apply copy_opG_ok; [fred; lia|]. fred. apply cps_ok_intro; fred; [lia | rewrite Z2Nat.id by lia; lia | exact I]. }
             match goal with |- context [copy_op x ?F] => rewrite (copy_op_eq x F) by (fred; lia) end. fred.
             run_cpn OB0 OB1 ltac:(rewrite WL).
             do 5 eexists. split; [reflexivity|]. split; [exact OB1|]. split; [lia|]. split; [lia|]. split; [lia|]. split.
             ++ apply cps_ok_intro; fred; lia.
             ++ unfold src_ok; fred. lia.
          -- split.
             { apply andb_true_intro; split; [apply copy_opG_ok; [fred; lia | fred; exact CP1] | reflexivity]. }
             do 5 eexists. split; [reflexivity|]. split; [exact OB0|]. split; [lia|]. split; [lia|]. split; [lia|]. split.
             ++ apply cps_ok_intro; fred; [lia | lia | exact I].
             ++ unfold src_ok; fred. rewrite WL. lia.
        * split; [reflexivity|].
          do 5 eexists. split; [reflexivity|]. split; [exact OB|]. split; [lia|]. split; [lia|]. split; [lia|]. split.
          -- apply cps_ok_intro; fred; [lia | lia | exact I].
          -- unfold src_ok; fred. rewrite WL. lia.
      + destruct (Z.ltb_spec opw l) as [L5|L5].
        * rewrite (wrap32_id (l - opw)) by lia. split.
          { apply copy_opG_ok; [fred; lia|]. fred. apply cps_ok_intro; fred; [lia | rewrite Z2Nat.id by lia; lia | exact I]. }
          match goal with |- context [copy_op x ?F] => rewrite (copy_op_eq x F) by (fred; lia) end. fred.
          run_cpn OB OB0 ltac:(rewrite WL).
          do 5 eexists. split; [reflexivity|]. split; [exact OB0|]. split; [lia|]. split; [lia|]. split; [lia|]. split.
          -- apply cps_ok_intro; fred; lia.
          -- unfold src_ok; fred. lia.
        * split; [reflexivity|].
          do 5 eexists. split; [reflexivity|]. split; [exact OB|]. split; [lia|]. split; [lia|]. split; [lia|]. split.
          -- apply cps_ok_intro; fred; [lia | lia | exact I].
          -- unfold src_ok; fred. rewrite WL. lia.
  Qed.

  Ltac tpost OB :=
    unfold TPOST, FB; fred; split; [lia|]; split; [exact OB|]; split; [lia|]; split; [lia|]; split; [lia|];
    first [exact I | left; reflexivity | right; reflexivity | lia].


  Lemma dodist_term : forall k here i o h b l d op fr ob m,
    term_ok DISTS m here = true -> code_bits here <= b ->
    0 <= b < 64 -> 0 <= h < 2 ^ b -> obytes NO ob -> 0 <= i <= NI -> 8 * (NI - i) + b - code_bits here >= 13 ->
    0 <= o -> 3 <= l <= 258 -> o + l <= NO ->
    let f := mkF i o h b l d op fr ob in
    dodistG x s NO (S k) here f = true /\ TPOST i o b (code_bits here) (dodist (S k) x s here f).
  Proof.
    intros k here i o h b l d op fr ob m TM HB Bb Hh OB Hi BUD Ho Hl Hol. cbv zeta.
    rewrite dodist_S, dodistG_S.
    pose proof (term_ok_DISTS _ _ TM) as (Hbits & CL).
    destruct (Z.eqb_spec (Z.land (code_op here) 16) 0) as [I16|O16]; bsimp.
    -
      destruct CL as [(O1 & _) | (I64 & _ & _)]; [exfalso; destruct (op_base_tests (code_op here) ltac:(lia)) as (E16 & _); lia|].
      destruct (Z.eqb_spec (Z.land (code_op here) 64) 0) as [?|_]; [lia|]. bsimp.
      destruct (fdrop_eq i o h b l d op fr ob (code_bits here) ltac:(lia) ltac:(lia) Hh) as [-> R1].
      split; [reflexivity|]. tpost OB.
    -
      destruct (dist_pre_spec here i o h b l d op fr ob m TM O16 HB Bb Hh Hi BUD) as (i1 & h1 & b1 & d1 & EP & B1 & H1 & I1 & E1 & D1).
      rewrite EP. cbv zeta. fred. rewrite Xbeg, Z.sub_0_r. rewrite (wrap32_id o) by lia.
      destruct (Z.ltb_spec o d1) as [LT|GE].
      + rewrite (wrap32_id (d1 - o)) by lia.
        destruct (Z.ltb_spec (x_whave x) (d1 - o)) as [FAR|NEAR]; bsimp.
        * destruct (Z.eqb_spec (x_sane x) 0) as [?|_]; [contradiction|]. bsimp.
          split; [reflexivity|]. tpost OB.
        * destruct (place_spec i1 o h1 b1 l d1 (d1 - o) fr ob OB Ho ltac:(lia) Hol ltac:(lia) ltac:(lia))
            as (PG & o2 & l2 & op2 & fr2 & ob2 & EPl & OB2 & L2 & SUM & LE & CPS & SRC).
          rewrite PG, EPl.
          destruct (copy_w3_tailG x NO (mkF i1 o2 h1 b1 l2 d1 op2 fr2 ob2) ltac:(fred; lia) ltac:(fred; exact CPS)) as [G1 G2].
          rewrite G1, G2. split; [reflexivity|].
          rewrite (copy_w3_tail x (mkF i1 o2 h1 b1 l2 d1 op2 fr2 ob2)) by (fred; lia). fred.
          run_cpn OB2 OB3 ltac:(idtac).
          pose proof (Z.mod_pos_bound l2 3 ltac:(lia)). tpost OB3.
      + destruct (copy_d3_tailG x NO (mkF i1 o h1 b1 l d1 op (FOut (o - d1)) ob) ltac:(fred; lia)
                    ltac:(apply cps_ok_intro; fred; [lia | rewrite Z2Nat.id by lia; lia | lia])) as [G1 G2].
        rewrite G1, G2. split; [reflexivity|].
        rewrite (copy_d3_tail x (mkF i1 o h1 b1 l d1 op (FOut (o - d1)) ob)) by (fred; lia). fred.
        run_cpn OB OB3 ltac:(idtac).
        pose proof (Z.mod_pos_bound l 3 ltac:(lia)). tpost OB3.
  Qed.

  Lemma dodist_root : forall i o h b l d op fr ob,
    0 <= b < 64 -> 0 <= h < 2 ^ b -> 15 <= b -> obytes NO ob -> 0 <= i <= NI -> 8 * (NI - i) + b >= 28 ->
    0 <= o -> 3 <= l <= 258 -> o + l <= NO ->
    let here := code_at s (is_distcode s) (Z.land h (x_dmask x)) in
    let f := mkF i o h b l d op fr ob in
    dodistG x s NO 4 here f = true /\ TPOST i o b 1 (dodist 4 x s here f).
  Proof.
    intros i o h b l d op fr ob Bb Hh B15 OB Hi BUD Ho Hl Hol. cbv zeta. rewrite Xdmask.
    destruct (tab_ok_root _ _ _ _ TD) as (RR0 & _ & _).
    pose proof (ones_index h (is_distbits s) ltac:(lia)) as IX.
    pose proof (tab_root_entry DISTS _ _ _ _ TD IX) as RT. cbv beta in RT.
    set (here := code_at s (is_distcode s) (Z.land h (Z.ones (is_distbits s)))) in *.
    destruct RT as (RB & RR & RE & [[NL TM] | (OP & BR & VR & XR & SUB)]).
    - destruct (dodist_term 3 here i o h b l d op fr ob _ TM ltac:(lia) Bb Hh OB Hi ltac:(lia) Ho Hl Hol) as [G P].
      split; [exact G | eapply TPOST_w; [exact P | lia | lia]].
    - rewrite dodist_S, dodistG_S.
      destruct (op_link_tests (code_op here) ltac:(lia)) as (E16 & E64 & E240 & NZ). rewrite E16, E64. bsimp.
      destruct (fdrop_eq i o h b l d op fr ob (code_bits here) ltac:(lia) ltac:(lia) Hh) as [-> R1]. fred.
      pose proof (zmask_index (Z.shiftr h (code_bits here)) (code_op here) ltac:(lia)) as JX.
      destruct (SUB _ JX) as [NL2 TM2]. pose proof (term_ok_DISTS _ _ TM2) as (HB2 & _).
      set (here2 := code_at s (is_distcode s) (code_val here + Z.land (Z.shiftr h (code_bits here)) (zmask (code_op here)))) in *.
      destruct (dodist_term 2 here2 i o (Z.shiftr h (code_bits here)) (b - code_bits here) l d op fr ob _ TM2
                 ltac:(lia) ltac:(lia) R1 OB Hi ltac:(lia) Ho Hl Hol) as [G P].
      split; [exact G | eapply TPOST_w; [exact P | lia | lia]].
  Qed.


  Lemma dolen_term : forall k here i o h b l d op fr ob m,
    term_ok LENS m here = true -> code_bits here <= b ->
    0 <= b < 64 -> 0 <= h < 2 ^ b -> obytes NO ob -> 0 <= i <= NI -> 8 * (NI - i) + b - code_bits here >= 33 ->
    0 <= o -> o + 258 <= NO ->
    let f := mkF i o h b l d op fr ob in
    dolenG x s NO (S k) here f = true /\ TPOST i o b (code_bits here) (dolen (S k) x s here f).
  Proof.
    intros k here i o h b l d op fr ob m TM HB Bb Hh OB Hi BUD Ho Hol. cbv zeta.
    rewrite dolen_S, dolenG_S.
    pose proof (term_ok_LENS _ _ TM) as (Hbits & CL).
    destruct (fdrop_eq i o h b l d op fr ob (code_bits here) ltac:(lia) ltac:(lia) Hh) as [EF R1]. rewrite EF.
    destruct (Z.eqb_spec (code_op here) 0) as [O0|O0]; bsimp.
    -
      cbv zeta. fred. pose proof (wrap8_range (code_val here)) as W8.
      split; [apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia|].
      pose proof (obytes_set NO ob o (wrap8 (code_val here)) OB W8) as OB1. tpost OB1.
    - destruct CL as [(O0' & _) | [(O1 & V1 & V2 & O2) | (I64 & I16)]]; [lia| |].
      +
        destruct (op_base_tests (code_op here) ltac:(lia)) as (E16 & E64 & E32 & E240 & E15 & NZ).
        destruct (Z.eqb_spec (Z.land (code_op here) 16) 0) as [?|O16]; [lia|]. bsimp.
        destruct (len_pre_spec here i o h b l d op fr ob m TM O16 HB Bb Hh Hi BUD) as (i1 & h1 & b1 & l1 & EP & B1 & H1 & I1 & B15 & E1 & L1).
        rewrite EP. cbv zeta. fred.
        destruct (dodist_root i1 o h1 b1 l1 d op fr ob B1 H1 B15 OB ltac:(lia) ltac:(lia) Ho L1 ltac:(lia)) as [G P].
        split; [exact G | eapply TPOST_w; [exact P | lia | lia]].
      +
        destruct (Z.eqb_spec (Z.land (code_op here) 16) 0) as [_|?]; [| contradiction]. bsimp.
        destruct (Z.eqb_spec (Z.land (code_op here) 64) 0) as [?|_]; [lia|]. bsimp. cbv zeta.
        split; [reflexivity|].
        destruct (Z.eqb_spec (Z.land (code_op here) 32) 0); bsimp; tpost OB.
  Qed.

  Lemma dolen_root : forall i o h b l d op fr ob,
    0 <= b < 64 -> 0 <= h < 2 ^ b -> 15 <= b -> obytes NO ob -> 0 <= i <= NI -> 8 * (NI - i) + b >= 48 ->
    0 <= o -> o + 258 <= NO ->
    let here := code_at s (is_lencode s) (Z.land h (x_lmask x)) in
    let f := mkF i o h b l d op fr ob in
    dolenG x s NO 4 here f = true /\ TPOST i o b (lcons s h) (dolen 4 x s here f) /\ 1 <= lcons s h.
  Proof.
    intros i o h b l d op fr ob Bb Hh B15 OB Hi BUD Ho Hol. cbv zeta. rewrite Xlmask. unfold lcons.
    destruct (tab_ok_root _ _ _ _ TL) as (RR0 & _ & _).
    pose proof (ones_index h (is_lenbits s) ltac:(lia)) as IX.
    pose proof (tab_root_entry LENS _ _ _ _ TL IX) as RT. cbv beta in RT.
    set (here := code_at s (is_lencode s) (Z.land h (Z.ones (is_lenbits s)))) in *.
    destruct RT as (RB & RR & RE & [[NL TM] | (OP & BR & VR & XR & SUB)]).
    - rewrite NL. destruct (dolen_term 3 here i o h b l d op fr ob _ TM ltac:(lia) Bb Hh OB Hi ltac:(lia) Ho Hol) as [G P].
      split; [exact G|]. split; [exact P | lia].
    - replace (is_linkop (code_op here)) with true by (symmetry; apply is_linkop_true; lia).
      rewrite dolen_S, dolenG_S.
      destruct (op_link_tests (code_op here) ltac:(lia)) as (E16 & E64 & E240 & NZ).
      destruct (Z.eqb_spec (code_op here) 0); [lia|]. rewrite E16, E64. bsimp.
      destruct (fdrop_eq i o h b l d op fr ob (code_bits here) ltac:(lia) ltac:(lia) Hh) as [-> R1]. cbv zeta. fred.
      pose proof (zmask_index (Z.shiftr h (code_bits here)) (code_op here) ltac:(lia)) as JX.
      destruct (SUB _ JX) as [NL2 TM2]. pose proof (term_ok_LENS _ _ TM2) as (HB2 & _).
      set (here2 := code_at s (is_lencode s) (code_val here + Z.land (Z.shiftr h (code_bits here)) (zmask (code_op here)))) in *.
      destruct (dolen_term 2 here2 i o (Z.shiftr h (code_bits here)) (b - code_bits here) l d op fr ob _ TM2
                 ltac:(lia) ltac:(lia) R1 OB Hi ltac:(lia) Ho Hol) as [G P].
      split; [exact G|]. split; [eapply TPOST_w; [exact P | lia | lia] | lia].
  Qed.


  Theorem trip_spec : forall i o h b l d op fr ob,
    0 <= b < 64 -> 0 <= h < 2 ^ b -> obytes NO ob -> 0 <= i -> i + 6 <= NI -> 0 <= o -> o + 258 <= NO ->
    let f := mkF i o h b l d op fr ob in
    exists h1, 0 <= h1 /\ h1 mod 2 ^ b = h /\ 1 <= lcons s h1 /\
      fast_tripG x s NO f = true /\ TPOST i o b (lcons s h1) (fast_trip x s f).
  Proof.
    intros i o h b l d op fr ob Bb Hh OB Hi0 Hi6 Ho Hol. cbv zeta. unfold fast_trip, fast_tripG.
    destruct (fpull2_if_spec i o h b l d op fr ob Bb Hh ltac:(lia) ltac:(lia)) as (i1 & h1 & b1 & -> & B1 & H1 & I1 & B15 & E1 & M1 & _).
    cbv zeta. fred.
    destruct (dolen_root i1 o h1 b1 l d op fr ob B1 H1 B15 OB ltac:(lia) ltac:(lia) Ho Hol) as (G & P & L1).
    exists h1. split; [lia|]. split; [exact M1|]. split; [exact L1|]. split; [exact G|]. eapply TPOST_w; [exact P | lia | lia].
  Qed.
End Trip.
