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
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeF1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
(* [comment removed for export] *)
Local Ltac fit3_l2_prune :=
  repeat match goal with
         | H : _ \/ _ |- _ => clear H
         | H : ?fit3A -> ?fit3B |- _ => clear H
         | H : _ <-> _ |- _ => clear H
         | H : exists _, _ |- _ => clear H
         end.
Local Ltac lia ::= first [ solve [ fit3_l2_prune; Zify.zify; xlia zchecker ] | Zify.zify; xlia zchecker ].

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition len_extra (x : ffx) (op : Z) (f : ffs) : ffs :=
  if negb (op =? 0) then
    let f := if f_bits f <? op then fpull x f else f in
    let f := fset_len f (wrap32 (f_len f + Z.land (wrap32 (f_hold f)) (zmask op))) in
    fdrop f op
  else f.

Lemma dolen_S : forall k x s here f,
  dolen (S k) x s here f =
    let op := code_bits here in
    let f := fdrop f op in
    let op := code_op here in
    if op =? 0 then
      FCont (fset_out (fset_ob f (arr_set (f_ob f) (f_out f) (wrap8 (code_val here)))) (f_out f + 1))
    else if negb (Z.land op 16 =? 0) then
      let f := fset_len f (code_val here) in
      let op := Z.land op 15 in
      let f := len_extra x op f in
      let f := fpull2_if x f in
      dodist 4 x s (code_at s (is_distcode s) (Z.land (f_hold f) (x_dmask x))) f
    else if Z.land op 64 =? 0 then
      dolen k x s (code_at s (is_lencode s) (code_val here + Z.land (f_hold f) (zmask op))) f
    else if negb (Z.land op 32 =? 0) then FBreak f TYPE None
    else FBreak f BAD (Some MSG_ff_invalid_literal_length_code).
Proof.
  intros. unfold len_extra. cbv zeta. cbn [dolen].
  lazymatch goal with |- ?a = ?b => exact (@eq_refl _ a) end.
Qed.

(* [comment removed for export] *)
Definition LACC (ON : Z) (f f' : ffs) (c : Z) : Prop :=
  FB ON f' /\
  exists p, 0 <= p <= 5 /\ (1 <= f_bits f - c -> p <= 4) /\ f_in f' = f_in f + p
    /\ 0 <= f_bits f' <= f_bits f + 8 * p - c
    /\ f_out f <= f_out f' <= f_out f + 258.

Definition break_ok (m : Z) (msg : option Z) : Prop := (m = TYPE /\ msg = None) \/ (m = BAD /\ msg <> None).

Section Dolen.
  Variable x : ffx.
Variable s : inflate_state.
Variable ON : Z.
Variable usedL : Z.
Variable usedD : Z.
  Hypothesis Xin : forall i, 0 <= arr_get (x_input x) i < 256.
  Hypothesis Xwn : 0 <= x_wnext x.
  Hypothesis Xbeg : 0 <= x_beg x.
  Hypothesis HON : ON < 2 ^ 32.
  Hypothesis Xdm : x_dmask x = zmask (is_distbits s).
  Hypothesis Xlm : x_lmask x = zmask (is_lenbits s).
  Hypothesis HTL : TBLg LENS (code_at s (is_lencode s)) (is_lenbits s) usedL.
  Hypothesis HTD : TBLg DISTS (code_at s (is_distcode s)) (is_distbits s) usedD.

  Lemma LACC_shift : forall f f1 f' c0 c,
    LACC ON f1 f' c -> f_in f1 = f_in f -> f_bits f1 = f_bits f - c0 -> f_out f1 = f_out f -> LACC ON f f' (c0 + c).
  Proof.
    intros f f1 f' c0 c [HF (p & Hp & Hp4 & Ei & Eb & Eo)] E1 E2 E3. split; [exact HF|].
    exists p. rewrite E1 in Ei. rewrite E2 in Eb, Hp4. rewrite E3 in Eo. repeat split; try lia.
  Qed.

  (* [comment removed for export] *)
  Lemma dolen_term : forall k here f,
    FB ON f -> 1 <= code_bits here <= 15 -> code_bits here <= f_bits f ->
    x_beg x <= f_out f -> f_out f + 258 <= ON ->
    ((exists sy, 0 <= sy < 288 /\ code_op here = fst (sym_entry LENS sy) /\ code_val here = snd (sym_entry LENS sy)) \/ code_op here = 64) ->
    match dolen (S k) x s here f with
    | FCont f' => LACC ON f f' (code_bits here)
    | FBreak f' m msg => LACC ON f f' (code_bits here) /\ break_ok m msg
    end.
  Proof.
    intros k here f HF Hcb Hcf Hbeg Hroom Hsh. rewrite dolen_S. cbv zeta.
    pose proof HF as (B1 & B2 & B3 & B4 & B5).
    destruct (FB_fdrop ON f (code_bits here) HF ltac:(lia)) as (HF1 & E1i & E1o & E1b & E1h & E1l & E1d & E1ob).
    set (f1 := fdrop f (code_bits here)) in *. pose proof HF1 as (C1 & C2 & C3 & C4 & C5).
    assert (STAY : LACC ON f f1 (code_bits here)).
    { split; [exact HF1|]. exists 0. rewrite E1i, E1b, E1o. repeat split; lia. }
    destruct Hsh as [[sy (Hsy & Hop & Hv)]|Hop].
    2:{ rewrite Hop. cbn [Z.land Z.eqb negb]. split; [exact STAY|]. right. split; [reflexivity|discriminate]. }
    pose proof (lens_sym_cases sy Hsy) as SC. destruct (sym_entry LENS sy) as [op v]. cbn [fst snd] in Hop, Hv.
    rewrite Hop, Hv. destruct SC as [[O1 O2]|[[O1 O2]|[(O1 & O2 & O3)|[O1|O1]]]].
    - (* [comment removed for export] *)
      rewrite O1. cbn [Z.eqb]. split.
      + unfold FB. facc. rewrite arr_len_set. unfold FB in HF1. lia.
      + exists 0. facc. rewrite E1i, E1b, E1o. repeat split; lia.
    - (* [comment removed for export] *)
      rewrite O1. cbn [Z.land Z.eqb negb]. split; [exact STAY|]. left. split; reflexivity.
    - (* [comment removed for export] *)
      destruct (len_op_facts op O1) as (F1 & F2 & F3 & F4 & F5).
      replace (op =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (negb (Z.land op 16 =? 0)) with true by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; exact F4).
      rewrite F3. set (e := op - 16) in *.
      assert (He : 0 <= e <= 5) by lia.
      pose proof (pow2_le e 5 ltac:(lia)) as P5. change (2 ^ 5) with 32 in P5. pose proof (pow2_pos e ltac:(lia)) as P0.
      (* [comment removed for export] *)
      set (f2 := len_extra x e (fset_len f1 v)).
      assert (HF2 : FB ON f2 /\ f_out f2 = f_out f /\ 3 <= f_len f2 <= 258 /\
                    exists p1, 0 <= p1 <= 1 /\ f_in f2 = f_in f + p1 /\ f_bits f2 = f_bits f - code_bits here + 8 * p1 - e
                               /\ (p1 = 1 -> f_bits f - code_bits here < e) /\ 0 <= f_bits f2).
      { subst f2. unfold len_extra. destruct (Z.eqb_spec e 0) as [E0|E0]; cbn [negb].
        - unfold FB. facc. split; [unfold FB in HF1; lia|]. split; [exact E1o|]. split; [lia|].
          exists 0. rewrite E1i, E1b. repeat split; lia.
        - cbv zeta.
          set (f1v := fset_len f1 v) in *.
          assert (HF1v : FB ON f1v /\ f_len f1v = v /\ f_in f1v = f_in f /\ f_out f1v = f_out f /\ f_bits f1v = f_bits f - code_bits here)
            by (subst f1v; unfold FB in *; facc; repeat split; first [assumption | reflexivity | lia]).
          clearbody f1v. destruct HF1v as (HF1v & Vl & Vi & Vo & Vb).
          match goal with |- context [fdrop ?F e] => set (fp := F) in * end.
          assert (HFp : FB ON fp /\ f_out fp = f_out f /\ e <= f_bits fp /\
                        exists p1, 0 <= p1 <= 1 /\ f_in fp = f_in f + p1 /\ f_bits fp = f_bits f - code_bits here + 8 * p1
                                   /\ (p1 = 1 -> f_bits f - code_bits here < e) /\ f_len fp = v + f_hold fp mod 2 ^ e).
          { subst fp. destruct (Z.ltb_spec (f_bits f1v) e) as [L1|L1].
            - destruct (FB_fpull x ON Xin f1v HF1v ltac:(lia)) as (HP1 & P1i & P1o & P1b & _ & P1l & P1d & _).
              unfold FB. facc. unfold FB in HP1. rewrite (land_wrap32_zmask (f_hold (fpull x f1v)) e) by lia.
              rewrite wrap32_id by (pose proof (mod_pow2_range (f_hold (fpull x f1v)) e ltac:(lia)); lia).
              rewrite P1o, P1l, Vl. split; [lia|]. split; [exact Vo|]. split; [lia|].
              exists 1. rewrite P1i, Vi, P1b, Vb. repeat split; lia.
            - unfold FB. facc. unfold FB in HF1v. rewrite (land_wrap32_zmask (f_hold f1v) e) by lia.
              rewrite wrap32_id by (pose proof (mod_pow2_range (f_hold f1v) e ltac:(lia)); lia).
              rewrite Vl. split; [lia|]. split; [exact Vo|]. split; [lia|].
              exists 0. rewrite Vi, Vb. repeat split; lia. }
          clearbody fp. destruct HFp as (HFp & Po & Pe & p1 & Hp1 & Pi & Pb & Pc & Pl).
          destruct (FB_fdrop ON fp e HFp ltac:(lia)) as (HQ & Qi & Qo & Qb & Qh & Ql & Qd & Qob).
          pose proof (mod_pow2_range (f_hold fp) e ltac:(lia)).
          split; [exact HQ|]. rewrite Qo, Ql, Pl. split; [exact Po|]. split; [lia|].
          exists p1. rewrite Qi, Qb, Pi, Pb. unfold FB in HQ. repeat split; lia. }
      clearbody f2. clear STAY. destruct HF2 as (HF2 & E2o & E2l & p1 & Hp1 & E2i & E2b & Cp1 & E2nn).
      (* [comment removed for export] *)
      set (f3 := fpull2_if x f2).
      assert (HF3 : FB ON f3 /\ f_out f3 = f_out f /\ f_len f3 = f_len f2 /\ 15 <= f_bits f3 /\
                    exists p2, (p2 = 0 \/ p2 = 2) /\ f_in f3 = f_in f2 + p2 /\ f_bits f3 = f_bits f2 + 8 * p2 /\ (p2 = 2 <-> f_bits f2 < 15)).
      { subst f3. unfold fpull2_if. destruct (Z.ltb_spec (f_bits f2) 15) as [L|L].
        - destruct (FB_fpull x ON Xin f2 HF2 ltac:(lia)) as (HP1 & P1i & P1o & P1b & _ & P1l & _ & _).
          destruct (FB_fpull x ON Xin (fpull x f2) HP1 ltac:(lia)) as (HP2 & P2i & P2o & P2b & _ & P2l & _ & _).
          split; [exact HP2|]. rewrite P2o, P2l, P2b, P2i, P1o, P1l, P1b, P1i. repeat (split; [first [assumption | lia]|]).
          exists 2. repeat split; lia.
        - split; [exact HF2|]. repeat (split; [first [assumption | lia]|]). exists 0. repeat split; lia. }
      clearbody f3. destruct HF3 as (HF3 & E3o & E3l & E3b & p2 & Hp2 & E3i & E3bb & Cp2).
      rewrite Xdm. rewrite land_zmask by (pose proof (T_root _ _ _ _ HTD); unfold FB in HF3; lia).
      destruct (dodist_root x s ON usedD Xin Xwn Xbeg HON HTD 2 f3 HF3 E3b ltac:(lia) ltac:(lia) ltac:(lia)) as (c2 & Hc2 & DD).
      change 4%nat with (S (S 2)).
      destruct (dodist 4 x s _ f3) as [f'|f' m msg].
      + destruct DD as [[HF' (p3 & e2 & Hp3 & He2 & Ei & Eb & D1 & D2)] Eo].
        split; [exact HF'|]. exists (p1 + p2 + p3). rewrite Ei, E3i, E2i, Eo, E3o. unfold FB in HF'. repeat split; try lia.
      + destruct DD as ([HF' (p3 & e2 & Hp3 & He2 & Ei & Eb & D1 & D2)] & Eo & Hm & Hmsg).
        split; [|right; split; assumption].
        split; [exact HF'|]. exists (p1 + p2 + p3). rewrite Ei, E3i, E2i, Eo, E3o. unfold FB in HF'. repeat split; try lia.
    - (* [comment removed for export] *)
      rewrite O1. cbn [Z.land Z.eqb negb]. split; [exact STAY|]. right. split; [reflexivity|discriminate].
    - rewrite O1. cbn [Z.land Z.eqb negb]. split; [exact STAY|]. right. split; [reflexivity|discriminate].
  Qed.

  (* [comment removed for export] *)
  Lemma dolen_root : forall k f,
    FB ON f -> 15 <= f_bits f -> x_beg x <= f_out f -> f_out f + 258 <= ON ->
    let c := lneedg (code_at s (is_lencode s)) (is_lenbits s) (f_hold f) in
    1 <= c <= 15 /\
    match dolen (S (S k)) x s (code_at s (is_lencode s) (f_hold f mod 2 ^ is_lenbits s)) f with
    | FCont f' => LACC ON f f' c
    | FBreak f' m msg => LACC ON f f' c /\ break_ok m msg
    end.
  Proof.
    intros k f HF Hb Hbeg Hroom. pose proof HF as (B1 & B2 & B3 & B4 & B5).
    pose proof (T_root _ _ _ _ HTL) as HR15.
    pose proof (ridx_range _ _ _ _ HTL (f_hold f)) as XR.
    destruct (root_cell _ _ _ _ HTL _ XR) as (Hbits & RL & RN).
    pose proof (lneedg_range _ _ _ _ HTL (f_hold f)) as [LR _].
    cbv zeta. split; [exact LR|].
    set (getL := code_at s (is_lencode s)) in *. set (root := is_lenbits s) in *.
    set (here := getL (f_hold f mod 2 ^ root)) in *.
    unfold lneedg. fold here.
    destruct (is_linkb here) eqn:HL.
    - destruct (RL eq_refl) as (Hbr & Hop & Hv1 & Hv2).
      rewrite dolen_S. cbv zeta.
      replace (code_op here =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      rewrite (land16_small (code_op here)) by lia. rewrite (land64_small (code_op here)) by lia. cbn [Z.eqb negb].
      destruct (FB_fdrop ON f (code_bits here) HF ltac:(lia)) as (HF1 & E1i & E1o & E1b & E1h & E1l & E1d & E1ob).
      set (f1 := fdrop f (code_bits here)) in *.
      rewrite E1h. rewrite (shiftr_land_zmask (f_hold f) (code_bits here) (code_op here)) by lia.
      set (y := f_hold f mod 2 ^ (code_bits here + code_op here) / 2 ^ code_bits here).
      pose proof (subidx_range (f_hold f) (code_bits here) (code_op here) ltac:(lia) ltac:(lia)) as Hy. fold y in Hy.
      destruct (sub_cell _ _ _ _ HTL (f_hold f mod 2 ^ root) y XR HL Hy) as (Sb & SNL & SSh).
      fold getL root in Sb, SNL, SSh. fold here in Sb, SNL, SSh. fold getL.
      set (here2 := getL (code_val here + y)) in *.
      pose proof (dolen_term k here2 f1 HF1 ltac:(lia) ltac:(rewrite E1b; lia) ltac:(rewrite E1o; exact Hbeg) ltac:(rewrite E1o; exact Hroom) SSh) as DT.
      revert DT. destruct (dolen (S k) x s here2 f1) as [f'|f' m msg]; intros DT.
      + exact (LACC_shift f f1 f' _ _ DT E1i E1b E1o).
      + destruct DT as [DT BK]. split; [exact (LACC_shift f f1 f' _ _ DT E1i E1b E1o)|exact BK].
    - destruct (RN eq_refl) as [Hbr SH].
      exact (dolen_term (S k) here f HF ltac:(lia) ltac:(lia) Hbeg Hroom SH).
  Qed.

  (* [comment removed for export] *)
  Lemma fast_trip_spec : forall f,
    FB ON f -> x_beg x <= f_out f -> f_out f + 258 <= ON ->
    let f1 := fpull2_if x f in
    let c := lneedg (code_at s (is_lencode s)) (is_lenbits s) (f_hold f1) in
    f_hold f1 mod 2 ^ f_bits f = f_hold f /\ 1 <= c <= 15 /\
    match fast_trip x s f with
    | FCont f' | FBreak f' _ _ =>
        FB ON f' /\ f_in f <= f_in f' <= f_in f + 6 /\ f_out f <= f_out f' <= f_out f + 258
        /\ c <= 8 * (f_in f' - f_in f) + f_bits f - f_bits f'
    end /\
    match fast_trip x s f with FCont _ => True | FBreak _ m msg => break_ok m msg end.
  Proof.
    intros f HF Hbeg Hroom. pose proof HF as (B1 & B2 & B3 & B4 & B5).
    unfold fast_trip.
    set (f1 := fpull2_if x f).
    assert (HF1 : FB ON f1 /\ f_out f1 = f_out f /\ 15 <= f_bits f1 /\ f_hold f1 mod 2 ^ f_bits f = f_hold f /\
                  exists p0, (p0 = 0 \/ p0 = 2) /\ f_in f1 = f_in f + p0 /\ f_bits f1 = f_bits f + 8 * p0 /\ (p0 = 2 <-> f_bits f < 15)).
    { subst f1. unfold fpull2_if. destruct (Z.ltb_spec (f_bits f) 15) as [L|L].
      - destruct (FB_fpull x ON Xin f HF ltac:(lia)) as (HP1 & P1i & P1o & P1b & P1m & _ & _ & _).
        destruct (FB_fpull x ON Xin (fpull x f) HP1 ltac:(lia)) as (HP2 & P2i & P2o & P2b & P2m & _ & _ & _).
        split; [exact HP2|]. rewrite P2o, P2b, P2i, P1o, P1b, P1i. split; [reflexivity|]. split; [lia|]. split.
        + rewrite <- P1m. rewrite <- P2m at 1. rewrite P1b. symmetry. apply (mod_down (f_bits f) (f_bits f + 8)); [lia|].
          rewrite Z.mod_mod by (apply Z.pow_nonzero; lia). reflexivity.
        + exists 2. repeat split; lia.
      - split; [exact HF|]. split; [reflexivity|]. split; [lia|]. split; [apply Z.mod_small; lia|]. exists 0. repeat split; lia. }
    clearbody f1. destruct HF1 as (HF1 & E1o & E1b & E1m & p0 & Hp0 & E1i & E1bb & C0).
    cbv zeta. split; [exact E1m|].
    rewrite Xlm. rewrite land_zmask by (pose proof (T_root _ _ _ _ HTL); unfold FB in HF1; lia).
    destruct (dolen_root 2 f1 HF1 E1b ltac:(lia) ltac:(lia)) as [Hc DL]. cbv zeta in DL.
    split; [exact Hc|].
    change 4%nat with (S (S 2)).
    destruct (dolen 4 x s _ f1) as [f'|f' m msg].
    - destruct DL as [HF' (p & Hp & Hp4 & Ei & Eb & Eo)]. split; [|exact I].
      split; [exact HF'|]. rewrite Ei, E1i, E1o in *. unfold FB in HF'. repeat split; try lia.
    - destruct DL as [[HF' (p & Hp & Hp4 & Ei & Eb & Eo)] BK]. split; [|exact BK].
      split; [exact HF'|]. rewrite Ei, E1i, E1o in *. unfold FB in HF'. repeat split; try lia.
  Qed.
End Dolen.
