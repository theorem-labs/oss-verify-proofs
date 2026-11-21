(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require InffastCtx.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import InffastSafe.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require InffastFastOk.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import
  Prog ZIface InflateState Inftrees InflateFast InflateArms Inflate InflateGarbBase InflateGarbFast InflateGarb.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateInv InflateInvRun InflateInvTab InflateInvDec InflateInvKit
  InflateInvFastA InflateInvFastB InflateInvFastC.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.



Lemma trip_ok_eq : forall x s IN ON WN f, trip_ok x s IN ON WN f =
  pull2_ok IN f &&
  (let f0 := fpull2_if x f in
   let i := Z.land (f_hold f0) (x_lmask x) in
   (i <? InffastCtx.ctab_len (is_lencode s)) && dolen_ok x s IN ON WN 4 (code_at s (is_lencode s) i) f0).
Proof. reflexivity. Qed.

Lemma ctab_len_cext : forall p, InffastCtx.ctab_len p = cext p.
Proof. intros p; destruct p; reflexivity. Qed.

Section TripOK.
  Variables (x : ffx) (s : inflate_state) (NI NO WN : Z).
  Hypothesis NO32 : 0 <= NO < 2 ^ 32.
  Hypothesis NIpos : 0 <= NI.
  Hypothesis Xinb : forall i, 0 <= i < NI -> 0 <= arr_get (x_input x) i < 256.
  Hypothesis Xwinb : forall i, 0 <= i < arr_len (x_window x) -> 0 <= arr_get (x_window x) i < 256.
  Hypothesis Xbeg : x_beg x = 0.
  Hypothesis Xsane : x_sane x <> 0.
  Hypothesis Xwh : 0 <= x_whave x <= x_wsize x.
  Hypothesis Xwn : 0 <= x_wnext x <= x_wsize x.
  Hypothesis Xwlen : x_wsize x <> 0 -> arr_len (x_window x) = x_wsize x.
  Hypothesis XWN : x_wsize x <> 0 -> x_wsize x <= WN.
  Hypothesis Xws32 : x_wsize x < 2 ^ 32.
  Hypothesis Xlmask : x_lmask x = Z.ones (is_lenbits s).
  Hypothesis Xdmask : x_dmask x = Z.ones (is_distbits s).
  Variables extL extD : Z.
  Hypothesis TL : tab_ok LENS (fun i => code_at s (is_lencode s) i) (is_lenbits s) extL = true.
  Hypothesis TD : tab_ok DISTS (fun i => code_at s (is_distcode s) i) (is_distbits s) extD = true.
  Hypothesis HextL : extL <= InffastCtx.ctab_len (is_lencode s).
  Hypothesis HextD : extD <= InffastCtx.ctab_len (is_distcode s).

  Local Ltac btrue := first [apply Z.leb_le | apply Z.ltb_lt | symmetry; apply Z.leb_le | symmetry; apply Z.ltb_lt]; lia.

  Lemma window_ok_place : forall i1 o h1 b1 l d1 opw fr ob,
    0 <= o -> 1 <= l -> o + l <= NO -> 1 <= opw <= x_whave x ->
    window_ok x NO WN (mkF i1 o h1 b1 l d1 opw fr ob) = true.
  Proof.
    intros i1 o h1 b1 l d1 opw fr ob Ho Hl Hol Hopw.
    assert (WS : x_wsize x <> 0) by lia. pose proof (XWN WS) as WL.
    unfold window_ok. fred.
    replace (o + l <=? NO) with true by btrue. cbn [andb].
    destruct (Z.eqb_spec (x_wnext x) 0) as [W0|W0].
    - replace (opw <=? x_wsize x) with true by btrue. cbn [andb].
      destruct (Z.ltb_spec opw l); apply Z.leb_le; lia.
    - destruct (Z.ltb_spec (x_wnext x) opw) as [L2|L2].
      + replace (opw <=? x_wsize x + x_wnext x) with true by btrue. cbn [andb].
        destruct (Z.ltb_spec (opw - x_wnext x) l) as [L3|L3].
        * replace (x_wsize x + x_wnext x - opw + (opw - x_wnext x) <=? WN) with true by btrue. cbn [andb].
          destruct (Z.ltb_spec (x_wnext x) (l - (opw - x_wnext x))); apply Z.leb_le; lia.
        * apply Z.leb_le; lia.
      + destruct (Z.ltb_spec opw l); apply Z.leb_le; lia.
  Qed.

  Definition dchk1 (here : Z) (f : ffs) : bool :=
    let f1 := fset_dist (fdrop f (code_bits here)) (code_val here) in
    let op1 := Z.land (code_op here) 15 in
    if f_bits f1 <? op1 then (f_in f1 + 1 <=? NI) && (if f_bits f1 + 8 <? op1 then f_in f1 + 2 <=? NI else true) else true.
  Definition dchk2 (here : Z) (f : ffs) : bool :=
    let f1 := fset_dist (fdrop f (code_bits here)) (code_val here) in
    let op1 := Z.land (code_op here) 15 in
    op1 <=? f_bits (if f_bits f1 <? op1 then let f2 := fpull x f1 in if f_bits f2 <? op1 then fpull x f2 else f2 else f1).
  Definition dtail (f4 : ffs) : bool :=
    (1 <=? f_dist f4) && (3 <=? f_len f4) && (f_out f4 + f_len f4 <=? NO) &&
    (let op2 := wrap32 (f_out f4 - x_beg x) in
     if op2 <? f_dist f4 then
       let op3 := wrap32 (f_dist f4 - op2) in
       if (x_whave x <? op3) && negb (x_sane x =? 0) then true else window_ok x NO WN (fset_op f4 op3)
     else true).

  Lemma dodist_ok_S' : forall k here f, dodist_ok x s NI NO WN (S k) here f =
    (code_bits here <=? f_bits f) &&
    (if negb (Z.land (code_op here) 16 =? 0) then dchk1 here f && (dchk2 here f && dtail (dist_pre x here f))
     else if Z.land (code_op here) 64 =? 0 then
       (code_op here <? 16) &&
       ((code_val here + Z.land (f_hold (fdrop f (code_bits here))) (zmask (code_op here)) <? InffastCtx.ctab_len (is_distcode s)) &&
        dodist_ok x s NI NO WN k (code_at s (is_distcode s) (code_val here + Z.land (f_hold (fdrop f (code_bits here))) (zmask (code_op here)))) (fdrop f (code_bits here)))
     else true).
  Proof. intros k here f. reflexivity. Qed.

  Lemma dchk_spec : forall here i o h b l d op fr ob m,
    term_ok DISTS m here = true -> Z.land (code_op here) 16 <> 0 -> code_bits here <= b ->
    0 <= b < 64 -> 0 <= h < 2 ^ b -> 0 <= i <= NI -> 8 * (NI - i) + b - code_bits here >= 13 ->
    dchk1 here (mkF i o h b l d op fr ob) = true /\ dchk2 here (mkF i o h b l d op fr ob) = true.
  Proof.
    intros here i o h b l d op fr ob m TM O16 HB Bb Hh Hi BUD.
    pose proof (term_ok_DISTS _ _ TM) as (Hbits & [(O1 & V1 & V2 & O2) | (I64 & I16 & _)]); [| exfalso; exact (O16 I16)].
    destruct (op_base_tests (code_op here) ltac:(lia)) as (E16 & E64 & E32 & E240 & E15 & NZ).
    unfold dchk1, dchk2. rewrite E15.
    destruct (fdrop_eq i o h b l d op fr ob (code_bits here) ltac:(lia) ltac:(lia) Hh) as [-> R1]. fred.
    destruct (Z.ltb_spec (b - code_bits here) (code_op here - 16)) as [L1|L1].
    - destruct (fpull_eq x i o (Z.shiftr h (code_bits here)) (b - code_bits here) l (code_val here) op fr ob
                 ltac:(lia) ltac:(lia) R1 ltac:(apply Xinb; lia)) as [-> R2]. fred.
      replace (i + 1 <=? NI) with true by btrue. cbn [andb].
      destruct (Z.ltb_spec (b - code_bits here + 8) (code_op here - 16)) as [L2|L2].
      + replace (i + 2 <=? NI) with true by btrue.
        destruct (fpull_eq x (i + 1) o (Z.shiftr h (code_bits here) + arr_get (x_input x) i * 2 ^ (b - code_bits here)) (b - code_bits here + 8)
                   l (code_val here) op fr ob ltac:(lia) ltac:(lia) R2 ltac:(apply Xinb; lia)) as [-> R3]. fred.
        split; [reflexivity | btrue].
      + split; [reflexivity | btrue].
    - split; [reflexivity | btrue].
  Qed.

  Lemma dodist_ok_term : forall k here i o h b l d op fr ob m,
    term_ok DISTS m here = true -> code_bits here <= b ->
    0 <= b < 64 -> 0 <= h < 2 ^ b -> 0 <= i <= NI -> 8 * (NI - i) + b - code_bits here >= 13 ->
    0 <= o -> 3 <= l <= 258 -> o + l <= NO ->
    dodist_ok x s NI NO WN (S k) here (mkF i o h b l d op fr ob) = true.
  Proof.
    intros k here i o h b l d op fr ob m TM HB Bb Hh Hi BUD Ho Hl Hol.
    rewrite dodist_ok_S'. cbn [f_bits]. replace (code_bits here <=? b) with true by btrue. cbn [andb].
    pose proof (term_ok_DISTS _ _ TM) as (Hbits & CL).
    destruct (Z.eqb_spec (Z.land (code_op here) 16) 0) as [I16|O16]; bsimp.
    -
      destruct CL as [(O1 & _) | (I64 & _ & _)]; [exfalso; destruct (op_base_tests (code_op here) ltac:(lia)) as (E16 & _); lia|].
      destruct (Z.eqb_spec (Z.land (code_op here) 64) 0) as [?|_]; [lia|]. reflexivity.
    -
      destruct (dchk_spec here i o h b l d op fr ob m TM O16 HB Bb Hh Hi BUD) as [-> ->]. cbn [andb].
      destruct (dist_pre_spec x NI NO NO32 Xinb here i o h b l d op fr ob m TM O16 HB Bb Hh Hi BUD) as (i1 & h1 & b1 & d1 & EP & B1 & H1 & I1 & E1 & D1).
      rewrite EP. unfold dtail. fred. rewrite Xbeg, Z.sub_0_r. rewrite (wrap32_id o) by lia.
      replace (1 <=? d1) with true by btrue. replace (3 <=? l) with true by btrue. replace (o + l <=? NO) with true by btrue. cbn [andb].
      destruct (Z.ltb_spec o d1) as [LT|GE]; [| reflexivity].
      rewrite (wrap32_id (d1 - o)) by lia.
      destruct (Z.ltb_spec (x_whave x) (d1 - o)) as [FAR|NEAR]; bsimp.
      + destruct (Z.eqb_spec (x_sane x) 0) as [?|_]; [contradiction|]. reflexivity.
      + apply window_ok_place; lia.
  Qed.

  Lemma dodist_ok_root : forall i o h b l d op fr ob,
    0 <= b < 64 -> 0 <= h < 2 ^ b -> 15 <= b -> 0 <= i <= NI -> 8 * (NI - i) + b >= 28 ->
    0 <= o -> 3 <= l <= 258 -> o + l <= NO ->
    let ix := Z.land h (x_dmask x) in
    (ix <? InffastCtx.ctab_len (is_distcode s)) = true /\
    dodist_ok x s NI NO WN 4 (code_at s (is_distcode s) ix) (mkF i o h b l d op fr ob) = true.
  Proof.
    intros i o h b l d op fr ob Bb Hh B15 Hi BUD Ho Hl Hol. cbv zeta. rewrite Xdmask.
    destruct (tab_ok_root _ _ _ _ TD) as (RR0 & RR2 & _).
    pose proof (ones_index h (is_distbits s) ltac:(lia)) as IX.
    split; [apply Z.ltb_lt; lia|].
    pose proof (tab_root_entry DISTS _ _ _ _ TD IX) as RT. cbv beta in RT.
    set (here := code_at s (is_distcode s) (Z.land h (Z.ones (is_distbits s)))) in *.
    destruct RT as (RB & RR & RE & [[NL TM] | (OP & BR & VR & XR & SUB)]).
    - exact (dodist_ok_term 3 here i o h b l d op fr ob _ TM ltac:(lia) Bb Hh Hi ltac:(lia) Ho Hl Hol).
    - rewrite dodist_ok_S'. cbn [f_bits]. replace (code_bits here <=? b) with true by btrue. cbn [andb].
      destruct (op_link_tests (code_op here) ltac:(lia)) as (E16 & E64 & E240 & NZ). rewrite E16, E64. bsimp.
      replace (code_op here <? 16) with true by btrue. cbn [andb].
      destruct (fdrop_eq i o h b l d op fr ob (code_bits here) ltac:(lia) ltac:(lia) Hh) as [-> R1]. fred.
      pose proof (zmask_index (Z.shiftr h (code_bits here)) (code_op here) ltac:(lia)) as JX.
      destruct (SUB _ JX) as [NL2 TM2]. pose proof (term_ok_DISTS _ _ TM2) as (HB2 & _).
      replace (code_val here + Z.land (Z.shiftr h (code_bits here)) (zmask (code_op here)) <? InffastCtx.ctab_len (is_distcode s)) with true by btrue. cbn [andb].
      set (here2 := code_at s (is_distcode s) (code_val here + Z.land (Z.shiftr h (code_bits here)) (zmask (code_op here)))) in *.
      exact (dodist_ok_term 2 here2 i o (Z.shiftr h (code_bits here)) (b - code_bits here) l d op fr ob _ TM2 ltac:(lia) ltac:(lia) R1 Hi ltac:(lia) Ho Hl Hol).
  Qed.

  Definition lchk (here : Z) (f : ffs) : bool :=
    let f1 := fset_len (fdrop f (code_bits here)) (code_val here) in
    let op1 := Z.land (code_op here) 15 in
    if negb (op1 =? 0) then if f_bits f1 <? op1 then (f_in f1 + 1 <=? NI) && (op1 <=? f_bits f1 + 8) else true else true.
  Definition lmid (here : Z) (f : ffs) : ffs :=
    let f1 := fset_len (fdrop f (code_bits here)) (code_val here) in
    let op1 := Z.land (code_op here) 15 in
    if negb (op1 =? 0) then
      let f2 := if f_bits f1 <? op1 then fpull x f1 else f1 in
      let f3 := fset_len f2 (wrap32 (f_len f2 + Z.land (wrap32 (f_hold f2)) (zmask op1))) in
      fdrop f3 op1
    else f1.
  Definition ltail (f1 : ffs) : bool :=
    let i := Z.land (f_hold f1) (x_dmask x) in
    (i <? InffastCtx.ctab_len (is_distcode s)) && dodist_ok x s NI NO WN 4 (code_at s (is_distcode s) i) f1.

  Lemma dolen_ok_S' : forall k here f, dolen_ok x s NI NO WN (S k) here f =
    (code_bits here <=? f_bits f) &&
    (if code_op here =? 0 then f_out (fdrop f (code_bits here)) <? NO
     else if negb (Z.land (code_op here) 16 =? 0) then lchk here f && (pull2_ok NI (lmid here f) && ltail (len_pre x here f))
     else if Z.land (code_op here) 64 =? 0 then
       (code_op here <? 16) &&
       ((code_val here + Z.land (f_hold (fdrop f (code_bits here))) (zmask (code_op here)) <? InffastCtx.ctab_len (is_lencode s)) &&
        dolen_ok x s NI NO WN k (code_at s (is_lencode s) (code_val here + Z.land (f_hold (fdrop f (code_bits here))) (zmask (code_op here)))) (fdrop f (code_bits here)))
     else true).
  Proof. intros k here f. reflexivity. Qed.

  Lemma lmid_spec : forall here i o h b l d op fr ob m,
    term_ok LENS m here = true -> Z.land (code_op here) 16 <> 0 -> code_bits here <= b ->
    0 <= b < 64 -> 0 <= h < 2 ^ b -> 0 <= i <= NI -> 8 * (NI - i) + b - code_bits here >= 33 ->
    lchk here (mkF i o h b l d op fr ob) = true /\
    exists i1 h1 b1 l1,
      lmid here (mkF i o h b l d op fr ob) = mkF i1 o h1 b1 l1 d op fr ob
      /\ 0 <= b1 < 64 /\ 0 <= h1 < 2 ^ b1 /\ i <= i1 <= NI
      /\ 8 * i1 - b1 = 8 * i - b + code_bits here + (code_op here - 16)
      /\ 3 <= l1 <= 258.
  Proof.
    intros here i o h b l d op fr ob m TM O16 HB Bb Hh Hi BUD.
    pose proof (term_ok_LENS _ _ TM) as (Hbits & [(O0 & _) | [(O1 & V1 & V2 & O2) | (I64 & I16)]]);
      [exfalso; rewrite O0 in O16; apply O16; reflexivity | | exfalso; exact (O16 I16)].
    destruct (op_base_tests (code_op here) ltac:(lia)) as (E16 & E64 & E32 & E240 & E15 & NZ).
    rewrite Z.shiftl_1_l in V2.
    assert (P0 : 0 < 2 ^ (code_op here - 16)) by (apply Z.pow_pos_nonneg; lia).
    unfold lchk, lmid. rewrite E15.
    destruct (fdrop_eq i o h b l d op fr ob (code_bits here) ltac:(lia) ltac:(lia) Hh) as [-> R1]. fred.
    destruct (Z.eqb_spec (code_op here - 16) 0) as [EZ|NZ']; bsimp.
    - split; [reflexivity|]. do 4 eexists. split; [reflexivity|]. rewrite EZ in P0 |- *. change (2 ^ 0) with 1 in V2. repeat split; lia.
    - destruct (Z.ltb_spec (b - code_bits here) (code_op here - 16)) as [L1|L1].
      + replace (i + 1 <=? NI) with true by btrue. replace (code_op here - 16 <=? b - code_bits here + 8) with true by btrue. cbn [andb].
        split; [reflexivity|].
        destruct (fpull_eq x i o (Z.shiftr h (code_bits here)) (b - code_bits here) (code_val here) d op fr ob
                   ltac:(lia) ltac:(lia) R1 ltac:(apply Xinb; lia)) as [-> R2]. fred.
        match goal with |- context [Z.land (wrap32 ?hh) (zmask ?n)] => pose proof (extra_bound hh n ltac:(lia)) as EB end.
        match goal with |- context [wrap32 (code_val here + ?v)] => rewrite (wrap32_id (code_val here + v)) by lia end.
        match goal with |- context [fdrop (mkF ?i' ?o' ?h' ?b' ?l' ?d' ?op' ?fr' ?ob') ?n] =>
          destruct (fdrop_eq i' o' h' b' l' d' op' fr' ob' n ltac:(lia) ltac:(lia) R2) as [-> R4] end.
        do 4 eexists. split; [reflexivity|]. repeat split; lia.
      + split; [reflexivity|].
        match goal with |- context [Z.land (wrap32 ?hh) (zmask ?n)] => pose proof (extra_bound hh n ltac:(lia)) as EB end.
        match goal with |- context [wrap32 (code_val here + ?v)] => rewrite (wrap32_id (code_val here + v)) by lia end.
        match goal with |- context [fdrop (mkF ?i' ?o' ?h' ?b' ?l' ?d' ?op' ?fr' ?ob') ?n] =>
          destruct (fdrop_eq i' o' h' b' l' d' op' fr' ob' n ltac:(lia) ltac:(lia) R1) as [-> R4] end.
        do 4 eexists. split; [reflexivity|]. repeat split; lia.
  Qed.

  Lemma dolen_ok_term : forall k here i o h b l d op fr ob m,
    term_ok LENS m here = true -> code_bits here <= b ->
    0 <= b < 64 -> 0 <= h < 2 ^ b -> 0 <= i <= NI -> 8 * (NI - i) + b - code_bits here >= 33 ->
    0 <= o -> o + 258 <= NO ->
    dolen_ok x s NI NO WN (S k) here (mkF i o h b l d op fr ob) = true.
  Proof.
    intros k here i o h b l d op fr ob m TM HB Bb Hh Hi BUD Ho Hol.
    rewrite dolen_ok_S'. cbn [f_bits]. replace (code_bits here <=? b) with true by btrue. cbn [andb].
    pose proof (term_ok_LENS _ _ TM) as (Hbits & CL).
    destruct (Z.eqb_spec (code_op here) 0) as [O0|O0].
    -
      destruct (fdrop_eq i o h b l d op fr ob (code_bits here) ltac:(lia) ltac:(lia) Hh) as [-> R1]. fred. btrue.
    - destruct CL as [(O0' & _) | [(O1 & V1 & V2 & O2) | (I64 & I16)]]; [lia| |].
      +
        destruct (op_base_tests (code_op here) ltac:(lia)) as (E16 & E64 & E32 & E240 & E15 & NZ).
        destruct (Z.eqb_spec (Z.land (code_op here) 16) 0) as [?|O16]; [lia|]. bsimp.
        destruct (lmid_spec here i o h b l d op fr ob m TM O16 HB Bb Hh Hi BUD) as (-> & i1 & h1 & b1 & l1 & EM & B1 & H1 & I1 & E1 & L1).
        rewrite EM. cbn [andb].
        replace (pull2_ok NI (mkF i1 o h1 b1 l1 d op fr ob)) with true
          by (unfold pull2_ok; fred; destruct (Z.ltb_spec b1 15); [btrue | reflexivity]).
        cbn [andb].
        destruct (len_pre_spec x NI NO NO32 Xinb here i o h b l d op fr ob m TM O16 HB Bb Hh Hi BUD) as (i2 & h2 & b2 & l2 & EP & B2 & H2 & I2 & B15 & E2 & L2).
        rewrite EP. unfold ltail. fred.
        destruct (dodist_ok_root i2 o h2 b2 l2 d op fr ob B2 H2 B15 ltac:(lia) ltac:(lia) Ho L2 ltac:(lia)) as [G1 G2].
        rewrite G1. exact G2.
      +
        destruct (Z.eqb_spec (Z.land (code_op here) 16) 0) as [_|?]; [| contradiction]. bsimp.
        destruct (Z.eqb_spec (Z.land (code_op here) 64) 0) as [?|_]; [lia|]. reflexivity.
  Qed.

  Lemma dolen_ok_root : forall i o h b l d op fr ob,
    0 <= b < 64 -> 0 <= h < 2 ^ b -> 15 <= b -> 0 <= i <= NI -> 8 * (NI - i) + b >= 48 ->
    0 <= o -> o + 258 <= NO ->
    let ix := Z.land h (x_lmask x) in
    (ix <? InffastCtx.ctab_len (is_lencode s)) = true /\
    dolen_ok x s NI NO WN 4 (code_at s (is_lencode s) ix) (mkF i o h b l d op fr ob) = true.
  Proof.
    intros i o h b l d op fr ob Bb Hh B15 Hi BUD Ho Hol. cbv zeta. rewrite Xlmask.
    destruct (tab_ok_root _ _ _ _ TL) as (RR0 & RR2 & _).
    pose proof (ones_index h (is_lenbits s) ltac:(lia)) as IX.
    split; [apply Z.ltb_lt; lia|].
    pose proof (tab_root_entry LENS _ _ _ _ TL IX) as RT. cbv beta in RT.
    set (here := code_at s (is_lencode s) (Z.land h (Z.ones (is_lenbits s)))) in *.
    destruct RT as (RB & RR & RE & [[NL TM] | (OP & BR & VR & XR & SUB)]).
    - exact (dolen_ok_term 3 here i o h b l d op fr ob _ TM ltac:(lia) Bb Hh Hi ltac:(lia) Ho Hol).
    - rewrite dolen_ok_S'. cbn [f_bits]. replace (code_bits here <=? b) with true by btrue. cbn [andb].
      destruct (op_link_tests (code_op here) ltac:(lia)) as (E16 & E64 & E240 & NZ).
      destruct (Z.eqb_spec (code_op here) 0); [lia|]. rewrite E16, E64. bsimp.
      replace (code_op here <? 16) with true by btrue. cbn [andb].
      destruct (fdrop_eq i o h b l d op fr ob (code_bits here) ltac:(lia) ltac:(lia) Hh) as [-> R1]. fred.
      pose proof (zmask_index (Z.shiftr h (code_bits here)) (code_op here) ltac:(lia)) as JX.
      destruct (SUB _ JX) as [NL2 TM2]. pose proof (term_ok_LENS _ _ TM2) as (HB2 & _).
      replace (code_val here + Z.land (Z.shiftr h (code_bits here)) (zmask (code_op here)) <? InffastCtx.ctab_len (is_lencode s)) with true by btrue. cbn [andb].
      set (here2 := code_at s (is_lencode s) (code_val here + Z.land (Z.shiftr h (code_bits here)) (zmask (code_op here)))) in *.
      exact (dolen_ok_term 2 here2 i o (Z.shiftr h (code_bits here)) (b - code_bits here) l d op fr ob _ TM2 ltac:(lia) ltac:(lia) R1 Hi ltac:(lia) Ho Hol).
  Qed.

  Theorem trip_ok_spec : forall i o h b l d op fr ob,
    0 <= b < 64 -> 0 <= h < 2 ^ b -> 0 <= i -> i + 6 <= NI -> 0 <= o -> o + 258 <= NO ->
    trip_ok x s NI NO WN (mkF i o h b l d op fr ob) = true.
  Proof.
    intros i o h b l d op fr ob Bb Hh Hi0 Hi6 Ho Hol. rewrite trip_ok_eq.
    replace (pull2_ok NI (mkF i o h b l d op fr ob)) with true
      by (unfold pull2_ok; fred; destruct (Z.ltb_spec b 15); [btrue | reflexivity]). cbn [andb].
    destruct (fpull2_if_spec x NI NO NO32 Xinb i o h b l d op fr ob Bb Hh ltac:(lia) ltac:(lia)) as (i1 & h1 & b1 & -> & B1 & H1 & I1 & B15 & E1 & M1 & _).
    cbv zeta. fred.
    destruct (dolen_ok_root i1 o h1 b1 l d op fr ob B1 H1 B15 ltac:(lia) ltac:(lia) Ho Hol) as [G1 G2].
    rewrite G1. exact G2.
  Qed.

  Hypothesis Xlast : x_last x = NI - 5.
  Hypothesis Xend : x_end x = NO - 257.

  Definition estep (f : ffs) : ffs + bool :=
    if trip_ok x s NI NO WN f then
      match fast_trip x s f with
      | FCont f' => if (f_in f' <? x_last x) && (f_out f' <? x_end x) then inl f' else inr (exit_ok f')
      | FBreak f' _ _ => inr (exit_ok f')
      end
    else inr false.
  Definition eres (r : ffs + bool) : bool := match r with inl _ => false | inr b => b end.

  Lemma loop_ok_eq : forall fuel f0, loop_ok x s NI NO WN fuel f0 = eres (iterK_nat (Z.to_nat fuel) estep f0).
  Proof. intros fuel f0. unfold loop_ok. rewrite iterZ_nat. reflexivity. Qed.

  Lemma exit_ok_of : forall f, 0 <= f_bits f -> 8 * f_in f - f_bits f >= -7 -> exit_ok f = true.
  Proof.
    intros f Hb H. unfold exit_ok. rewrite (Z.shiftr_div_pow2 (f_bits f) 3) by lia. change (2 ^ 3) with 8.
    apply Z.leb_le. pose proof (Z.div_mod (f_bits f) 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (f_bits f) 8 ltac:(lia)) as MB.
    set (q := f_bits f / 8) in *. lia.
  Qed.

  Lemma loop_okN : forall n i o h b l d op fr ob,
    0 <= b < 64 -> 0 <= h < 2 ^ b -> obytes NO ob -> 0 <= i -> i + 6 <= NI -> 0 <= o -> o + 258 <= NO ->
    (forall h1, 0 <= h1 -> h1 mod 2 ^ b = h -> 1 <= lcons s h1 -> 8 * i - b + lcons s h1 >= -7) ->
    NO - 257 - o < Z.of_nat n ->
    eres (iterK_nat n estep (mkF i o h b l d op fr ob)) = true.
  Proof.
    induction n as [|n IH]; intros i o h b l d op fr ob Bb Hh OB Hi0 Hi6 Ho0 Ho258 HD M; [exfalso; cbn in M; lia|].
    cbn [iterK_nat]. unfold estep at 1.
    rewrite (trip_ok_spec i o h b l d op fr ob Bb Hh Hi0 Hi6 Ho0 Ho258).
    destruct (trip_spec x s NI NO NO32 Xinb Xwinb Xbeg Xsane Xwh Xwn Xwlen Xws32 Xlmask Xdmask extL extD TL TD
                i o h b l d op fr ob Bb Hh OB Hi0 Hi6 Ho0 Ho258) as (h1 & H1 & M1 & L1 & _ & P).
    specialize (HD h1 H1 M1 L1).
    destruct (fast_trip x s (mkF i o h b l d op fr ob)) as [f'|f' md msg].
    - unfold TPOST in P. cbn [fsf] in P. destruct P as (B' & OB' & O' & I' & C' & CO). unfold FB in B'.
      rewrite Xlast, Xend.
      destruct (Z.ltb_spec (f_in f') (NI - 5)) as [CI|CI]; destruct (Z.ltb_spec (f_out f') (NO - 257)) as [CO'|CO']; cbn [andb eres].
      + destruct f' as [i' o' h' b' l' d' op' fr' ob']. cbn [f_in f_out f_hold f_bits f_ob] in *.
        apply IH; [lia | lia | exact OB' | lia | lia | lia | lia | intros; lia | replace (Z.of_nat (S n)) with (Z.of_nat n + 1) in M by lia; lia].
      + apply exit_ok_of; lia.
      + apply exit_ok_of; lia.
      + apply exit_ok_of; lia.
    - cbn [eres]. unfold TPOST in P. cbn [fsf] in P. destruct P as (B' & OB' & O' & I' & C' & _). unfold FB in B'.
      apply exit_ok_of; lia.
  Qed.
End TripOK.

Theorem ffok : forall (NI NO WN TOT0 : Z) s c r ob,
  pinv NI NO WN TOT0 (mkW s c r) -> is_mode s = LEN -> 6 <= ir_have r -> 258 <= ir_left r ->
  arr_len ob = NO -> (forall i, 0 <= i < ir_put r -> arr_get ob i = arr_get (ic_outbuf c) i) ->
  (forall i, 0 <= i < NO -> 0 <= arr_get ob i < 256) ->
  ff_ok (iset_bits (iset_hold s (ir_hold r)) (ir_bits r))
        (icset_outbuf (icset_avail_in (icset_next_in (icset_avail_out (icset_next_out c (ir_put r)) (ir_left r)) (ir_next r)) (ir_have r)) ob) r = true.
Proof.
  intros NI NO WN TOT0 s c r ob PI Hm FH FL HobL Hagree Hobb.
  pose proof (InffastFastOk.DEBT_LEN NI NO WN TOT0 s c r PI Hm) as HD.
  pose (w := mkW s c r). change (mkW s c r) with w in PI, HD.
  change s with (w_s w) in Hm |- *. change c with (w_c w) in Hagree |- *. change r with (w_r w) in FH, FL, Hagree |- *.
  clearbody w. clear s c r.
  dworld w. cbn [w_s w_c w_r is_mode ir_have ir_left ir_put ir_hold ir_bits ir_next ic_outbuf] in Hm, FH, FL, Hagree |- *.
  unfold DEBT in HD. cbn [w_s w_r ir_bits ir_hold ir_next] in HD.
  pinv_open PI. subst f_mode. sinv_triage.
  destruct (dist_tab _ SIr eq_refl) as (extD & TD & HextD). cbn [is_codes is_distcode is_distbits] in TD, HextD.
  destruct (len_tab _ SIr eq_refl) as (extL & TL & HextL). cbn [is_codes is_lencode is_lenbits] in TL, HextL.
  destruct (tab_ok_root _ _ _ _ TL) as (Rl1 & _ & _). destruct (tab_ok_root _ _ _ _ TD) as (Rd1 & _ & _).
  assert (OL : r_out - r_left = r_put) by (destruct Xol as [X|[X1 X2]]; [exact X | exfalso; clear -X2 Klen Kcheck; lia]).
  unfold ff_ok, InffastCtx.ffx_of, InffastCtx.ff0_of. wred.
  rewrite (wrap32_id (r_have - 5)) by liaq. rewrite (wrap32_id (r_left - 257)) by liaq. rewrite OL. rewrite (wrap32_id r_put) by liaq.
  rewrite Z.sub_diag. rewrite HobL, ClNI.
  rewrite loop_ok_eq.
  match goal with |- eres (iterK_nat _ (estep ?X ?ST _ _ _) _) = true => set (XX := X); set (S1 := ST) end.
  assert (XL : x_lmask XX = Z.ones f_lenbits) by (unfold XX; cbn [x_lmask]; rewrite zmask_ones by liaq; f_equal; liaq).
  assert (XD : x_dmask XX = Z.ones f_distbits) by (unfold XX; cbn [x_dmask]; rewrite zmask_ones by liaq; f_equal; liaq).
  assert (TL1 : tab_ok LENS (fun i => code_at S1 f_lencode i) f_lenbits extL = true).
  { apply (tab_ok_ext LENS (fun i => cat f_codes f_lencode i)); [intros i Hi; unfold S1; rewrite code_at_cat; reflexivity | exact TL]. }
  assert (TD1 : tab_ok DISTS (fun i => code_at S1 f_distcode i) f_distbits extD = true).
  { apply (tab_ok_ext DISTS (fun i => cat f_codes f_distcode i)); [intros i Hi; unfold S1; rewrite code_at_cat; reflexivity | exact TD]. }
  assert (XWL : x_wsize XX <> 0 -> arr_len (x_window XX) = x_wsize XX) by (unfold XX; cbn [x_wsize x_window]; intros; lia).
  assert (XWN : x_wsize XX <> 0 -> x_wsize XX <= arr_len f_window) by (unfold XX; cbn [x_wsize]; intros; lia).
  apply (loop_okN XX S1 NI NO (arr_len f_window) (proj2 B)
           ltac:(unfold XX; cbn [x_input]; exact Cinb) ltac:(unfold XX; cbn [x_window]; exact Swinb)
           ltac:(reflexivity) ltac:(unfold XX; cbn [x_sane]; liaq) ltac:(unfold XX; cbn [x_whave x_wsize]; liaq) ltac:(unfold XX; cbn [x_wnext x_wsize]; liaq)
           XWL XWN ltac:(unfold XX; cbn [x_wsize]; liaq) XL XD extL extD TL1 TD1
           ltac:(rewrite ctab_len_cext; unfold S1; cbn [is_lencode]; exact HextL) ltac:(rewrite ctab_len_cext; unfold S1; cbn [is_distcode]; exact HextD)
           ltac:(unfold XX; cbn [x_last]; liaq) ltac:(unfold XX; cbn [x_end]; liaq)).
  - exact Rbits.
  - exact Rhold.
  - split; [exact HobL | exact Hobb].
  - liaq.
  - liaq.
  - liaq.
  - liaq.
  - intros h1 A1 A2 A3. specialize (HD h1 A1 A2).
    match type of HD with lcons ?S0 h1 + _ + _ >= _ =>
      replace (lcons S1 h1) with (lcons S0 h1) by (symmetry; exact (lcons_hb S0 r_hold r_bits h1)) end.
    clear -HD A3. lia.
  - rewrite Z2Nat.id by liaq. liaq.
Qed.
