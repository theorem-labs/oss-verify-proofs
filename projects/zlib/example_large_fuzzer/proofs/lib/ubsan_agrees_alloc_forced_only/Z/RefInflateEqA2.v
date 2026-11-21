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
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeD.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeT.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeH.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeK.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeA1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeA3.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateEqD.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateEqA1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac fit3_l2_prune :=
  repeat match goal with
         | H : _ \/ _ |- _ => clear H
         | H : ?fit3A -> ?fit3B |- _ => clear H
         | H : _ <-> _ |- _ => clear H
         | H : exists _, _ |- _ => clear H
         end.
Local Ltac lia ::= first [ solve [ fit3_l2_prune; Zify.zify; xlia zchecker ] | Zify.zify; xlia zchecker ].

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma match_copy_out : forall m win1 win2 ob put i, Z.of_nat (S m) < 2 ^ 32 ->
  match_copy win2 (ob, put, FOut i, Z.of_nat (S m)) = match_copy win1 (ob, put, FOut i, Z.of_nat (S m)).
Proof.
  induction m as [|m IH]; intros win1 win2 ob put i Hm.
  - rewrite !match_copy_step by (cbn; lia). reflexivity.
  - rewrite !match_copy_step by lia. cbv zeta. cbn [from_succ].
    replace (Z.of_nat (S (S m)) - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (Z.of_nat (S (S m)) - 1) with (Z.of_nat (S m)) by lia. apply IH. lia.
Qed.

Lemma match_copy_win : forall m win1 win2 ob put i, Z.of_nat (S m) < 2 ^ 32 ->
  (forall j, i <= j < i + Z.of_nat (S m) -> arr_get win2 j = arr_get win1 j) ->
  match_copy win2 (ob, put, FWin i, Z.of_nat (S m)) = match_copy win1 (ob, put, FWin i, Z.of_nat (S m)).
Proof.
  induction m as [|m IH]; intros win1 win2 ob put i Hm Hw.
  - rewrite !match_copy_step by (cbn; lia). cbv zeta. rewrite (Hw i) by (cbn; lia). reflexivity.
  - rewrite !match_copy_step by lia. cbv zeta. cbn [from_succ]. rewrite (Hw i) by lia.
    replace (Z.of_nat (S (S m)) - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (Z.of_nat (S (S m)) - 1) with (Z.of_nat (S m)) by lia. apply IH; [lia|]. intros j Hj. apply Hw. lia.
Qed.

Lemma match_copy_cong : forall win1 win2 ob put from n, 1 <= n < 2 ^ 32 ->
  (forall i j, from = FWin i -> i <= j < i + n -> arr_get win2 j = arr_get win1 j) ->
  match_copy win2 (ob, put, from, n) = match_copy win1 (ob, put, from, n).
Proof.
  intros win1 win2 ob put from n Hn Hw.
  replace n with (Z.of_nat (S (Z.to_nat (n - 1)))) in * by lia.
  destruct from as [i|i].
  - apply match_copy_win; [lia|]. intros j Hj. apply (Hw i j eq_refl). lia.
  - apply match_copy_out. lia.
Qed.

Section Code.

  Definition iv : ivariant := ivar_ref.
  Variable flush : Z.
  Ltac auxt := cbv beta iota delta [set_back add_back aux iv_aux iv ivar_ref].

  Lemma match_copy_agree : forall s1 s2 ob put from n,
    (forall i, 0 <= i < is_whave s1 -> arr_get (is_window s2) i = arr_get (is_window s1) i) ->
    n < 2 ^ 32 ->
    (forall i, from = FWin i -> 1 <= n -> 0 <= i /\ i + n <= is_whave s1) ->
    match_copy (is_window s2) (ob, put, from, n) = match_copy (is_window s1) (ob, put, from, n).
  Proof.
    intros s1 s2 ob put from n Qwin Hn Hfrom.
    destruct (Z.lt_ge_cases n 1) as [Z0|Z0].
    - unfold match_copy. cbn [snd]. rewrite !loopZ_le0 by lia. reflexivity.
    - apply match_copy_cong; [lia|]. intros i j Ei Hj. apply Qwin. destruct (Hfrom i Ei Z0). lia.
  Qed.

  Ltac mc_step MC1 MC2 :=
    aflat; eapply RES2_step2;
    [ cbv beta; cbn [w_s w_c w_r wset_c wset_r]; sacc; rewrite MC1; reflexivity
    | cbv beta; cbn [w_s w_c w_r wset_c wset_r]; sacc; rewrite MC2; reflexivity | ].

  Lemma arm_MATCH_cong : arm_cong MATCH FCore (arm_MATCH iv).
  Proof.
    intros s1 s2 c r HC E HQ HU. notHB HU E W5 F0. pose proof HQ as HQ0. ieq_open HQ E. unfold arm_MATCH.
    pose proof HC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14).
    rstep gr_eq. destruct (ir_left r =? 0).
    { apply RES2_leave. apply WMID_mk; [exact HQ0 | exact HU]. }
    rstep gs_eq. nrm s1 s2 W5 F0.
    set (copy := wrap32 (ir_out r - ir_left r)). pose proof (wrap32_range (ir_out r - ir_left r)) as CR. fold copy in CR.
    destruct (Z.ltb_spec copy (is_offset s1)) as [Cw|Cw].
    -
      set (copy' := wrap32 (is_offset s1 - copy)). pose proof (wrap32_range (is_offset s1 - copy)) as CR'. fold copy' in CR'.
      destruct ((is_whave s1 <? copy') && (if iv_aux iv then negb (is_sane s1 =? 0) else true)) eqn:G.
      + unfold go_bad, set_msg, set_mode. rstep uc_eq. rstep us_eq. rstep aret_eq. apply RES2_ret. wmid E W5 F0.
      + assert (Gw : copy' <= is_whave s1).
        { rewrite C13 in G. destruct (Z.ltb_spec (is_whave s1) copy'); [|lia]. exfalso. destruct (iv_aux iv); discriminate G. }
        assert (Hcf : exists cp from, (if is_wnext s1 <? copy' then (wrap32 (copy' - is_wnext s1), FWin (is_wsize s1 - wrap32 (copy' - is_wnext s1))) else (copy', FWin (is_wnext s1 - copy')))
                                     = (cp, from) /\ 0 <= cp <= copy'
                                     /\ forall i, from = FWin i -> 0 <= i /\ i + cp <= is_whave s1).
        { destruct (Z.ltb_spec (is_wnext s1) copy') as [W1|W1].
          - eexists _, _. split; [reflexivity|]. rewrite wrap32_id by lia. split; [lia|].
            intros i Ei. injection Ei; intros <-.
            assert (WS : is_wsize s1 <> 0) by (intros Z0; destruct (C6 Z0); lia).
            destruct (C7 WS) as [N1 N2].
            assert (is_whave s1 = is_wsize s1) by (destruct (Z.eq_dec (is_whave s1) (is_wsize s1)); [assumption|]; pose proof (C8 WS ltac:(lia)); lia).
            lia.
          - eexists _, _. split; [reflexivity|]. split; [lia|]. intros i Ei. injection Ei; intros <-.
            destruct (Z.eq_dec (is_wsize s1) 0) as [Z0|WS]; [destruct (C6 Z0); lia|].
            destruct (C7 WS) as [N1 N2].
            destruct (Z.lt_ge_cases (is_whave s1) (is_wsize s1)) as [L|L]; [pose proof (C8 WS L); lia | lia]. }
        destruct Hcf as (cp & from & Ecf & Hcp & Hfrom). rewrite Ecf.
        rstep aret_eq.
        set (cp2 := if is_length s1 <? cp then is_length s1 else cp).
        set (cp3 := if ir_left r <? cp2 then ir_left r else cp2).
        assert (Hcp3 : cp3 <= cp) by (subst cp3 cp2; destruct (Z.ltb_spec (is_length s1) cp); destruct (Z.ltb_spec (ir_left r) (is_length s1)); destruct (Z.ltb_spec (ir_left r) cp); lia).
        rstep ur_eq. rstep us_eq.
        destruct (match_copy (is_window s1) (ic_outbuf c, ir_put r, from, cp3)) as [[[ob put'] fr'] cc] eqn:MC1.
        assert (MC2 : match_copy (is_window s2) (ic_outbuf c, ir_put r, from, cp3) = (ob, put', fr', cc)).
        { rewrite <- MC1. apply match_copy_agree; [exact Qwin | lia |]. intros i Ei Hn. destruct (Hfrom i Ei). lia. }
        mc_step MC1 MC2.
        rstep gs_eq. nrm s1 s2 W5 F0.
        destruct (wrap32 (is_length s1 - cp3) =? 0); [unfold set_mode; rlast | apply RES2_ret]; wmid E W5 F0.
    -
      rstep aret_eq.
      set (cp3 := if ir_left r <? is_length s1 then ir_left r else is_length s1).
      assert (Hcp3 : cp3 <= is_length s1) by (subst cp3; destruct (Z.ltb_spec (ir_left r) (is_length s1)); lia).
      rstep ur_eq. rstep us_eq.
      destruct (match_copy (is_window s1) (ic_outbuf c, ir_put r, FOut (ir_put r - is_offset s1), cp3)) as [[[ob put'] fr'] cc] eqn:MC1.
      assert (MC2 : match_copy (is_window s2) (ic_outbuf c, ir_put r, FOut (ir_put r - is_offset s1), cp3) = (ob, put', fr', cc)).
      { rewrite <- MC1. apply match_copy_agree; [exact Qwin | lia |]. intros i Ei. discriminate Ei. }
      mc_step MC1 MC2.
      rstep gs_eq. nrm s1 s2 W5 F0.
      destruct (wrap32 (is_length s1 - cp3) =? 0); [unfold set_mode; rlast | apply RES2_ret]; wmid E W5 F0.
  Qed.

  Lemma land_65535_32 : forall a, 0 <= Z.land a 65535 < 2 ^ 32.
  Proof. intros a. pose proof (land_65535 a). lia. Qed.

  Ltac core_of HC := apply (CORE_keep _ _ HC); unfold fixedtables; sacc; rewrite ?arr_len_set; try reflexivity; try (apply CORE_length; exact HC); try apply wrap32_range; try (unfold code_val; apply land_65535_32).

  Lemma arm_DISTEXT_cong : arm_cong DISTEXT FCore (arm_DISTEXT iv).
  Proof.
    intros s1 s2 c r HC E HQ HU. notHB HU E W5 F0. pose proof HQ as HQ0. ieq_open HQ E. unfold arm_DISTEXT.
    rstep gs_eq. nrm s1 s2 W5 F0.
    destruct (negb (is_extra s1 =? 0)).
    - aflat. rlock SFREE_NEEDBITS; [exact HQ0 | exact HU |]. intros [] r1 HU1 _. cbv beta.
      unfold BITS. rstep gr_eq. rstep us_eq. nrm s1 s2 W5 F0. unfold DROPBITS. rstep ur_eq. unfold add_back, aux.
      destruct (iv_aux iv).
      + rstep us_eq. nrm s1 s2 W5 F0. unfold set_mode at 1. rstep us_eq.
        apply arm_MATCH_cong; [core_of HC | reflexivity | ieq_close E | uw0 W5 F0].
      + rstep aret_eq. unfold set_mode at 1. rstep us_eq.
        apply arm_MATCH_cong; [core_of HC | reflexivity | ieq_close E | uw0 W5 F0].
    - rstep aret_eq. unfold set_mode at 1. rstep us_eq.
      apply arm_MATCH_cong; [core_of HC | reflexivity | ieq_close E | uw0 W5 F0].
  Qed.

  Lemma dist_tail_cong : forall here0 s1 s2 c r, CORE s1 -> is_mode s1 = DIST -> IEQ s1 s2 -> UW s1 c r ->
    RES2 ((DROPBITS (code_bits here0);; add_back iv (code_bits here0);;
           (if negb (Z.land (code_op here0) 64 =? 0) then go_bad MSG_invalid_distance_code
            else us (fun s : inflate_state => iset_extra (iset_offset s (code_val here0)) (Z.land (code_op here0) 15));; set_mode DISTEXT;; arm_DISTEXT iv))%am (mkW s1 c r))
         ((DROPBITS (code_bits here0);; add_back iv (code_bits here0);;
           (if negb (Z.land (code_op here0) 64 =? 0) then go_bad MSG_invalid_distance_code
            else us (fun s : inflate_state => iset_extra (iset_offset s (code_val here0)) (Z.land (code_op here0) 15));; set_mode DISTEXT;; arm_DISTEXT iv))%am (mkW s2 c r)).
  Proof.
    intros here0 s1 s2 c r HC E HQ HU. notHB HU E W5 F0. pose proof HQ as HQ0. ieq_open HQ E.
    unfold DROPBITS. rstep ur_eq. unfold add_back, aux.
    destruct (iv_aux iv); [rstep us_eq | rstep aret_eq]; nrm s1 s2 W5 F0.
    all: destruct (negb (Z.land (code_op here0) 64 =? 0));
      [ unfold go_bad, set_msg, set_mode; rstep uc_eq; rlast; wmid E W5 F0
      | rstep us_eq; unfold set_mode at 1; rstep us_eq; apply arm_DISTEXT_cong; [core_of HC | reflexivity | ieq_close E | uw0 W5 F0] ].
  Qed.

  Lemma arm_DIST_cong : arm_cong DIST FCore (arm_DIST iv).
  Proof.
    intros s1 s2 c r HC E HQ HU. notHB HU E W5 F0. pose proof HQ as HQ0. ieq_open HQ E. unfold arm_DIST.
    rstep gs_eq. nrm s1 s2 W5 F0.

    unfold DECODE1 at 1 2. aflat. eapply RES2_bind_lock; [apply DECODE_k_LOCK; intros h; exact (tbl_eq_DECODE1 s1 s2 DISTS _ _ QtblD h) | exact HQ0 | exact HU |].
    intros here r1 HU1 E1. cbv beta.
    destruct (DECODE_k_ret _ _ _ _ _ _ _ _ _ E1) as (r1' & Ew & Ehere). injection Ew; intros <-.
    destruct (Z.land (code_op here) 240 =? 0) eqn:T240.
    - aflat. unfold DECODE2 at 1 2. eapply RES2_bind_lock; [ | exact HQ0 | exact HU1 |].
      { apply DECODE_k_LOCK. intros h. rewrite Ehere. apply (tbl_eq_DECODE2 s1 s2 DISTS _ _ (ir_hold r1) QtblD).
        apply (tbl_eq_link s1 s2 DISTS _ _ (ir_hold r1) (fun op => Z.land op 240 =? 0) QtblD dists_two_contra). rewrite <- Ehere. exact T240. }
      intros here2 r2 HU2 E2. cbv beta. unfold DROPBITS at 1 3. rstep ur_eq. unfold add_back at 1 3. unfold aux.
      destruct (iv_aux iv) eqn:AUX; [rstep us_eq | rstep aret_eq]; nrm s1 s2 W5 F0; rstep aret_eq.
      + apply dist_tail_cong; [core_of HC | sacc; exact E | ieq_close E | uw0 W5 F0].
      + apply dist_tail_cong; [exact HC | exact E | exact HQ0 | eapply UW_regs; [exact HU2 | reflexivity | reflexivity]].
    - rstep aret_eq. apply dist_tail_cong; [exact HC | exact E | exact HQ0 | exact HU1].
  Qed.

  Ltac to_DIST HC E W5 F0 s1 s2 :=
    first [rstep us_eq | rstep aret_eq]; nrm s1 s2 W5 F0; unfold set_mode at 1; rstep us_eq;
    apply arm_DIST_cong; [core_of HC | reflexivity | ieq_close E | uw0 W5 F0].

  Lemma arm_LENEXT_cong : arm_cong LENEXT FCore (arm_LENEXT iv).
  Proof.
    intros s1 s2 c r HC E HQ HU. notHB HU E W5 F0. pose proof HQ as HQ0. ieq_open HQ E. unfold arm_LENEXT, add_back, aux.
    destruct (iv_aux iv); cbv iota.
    all: rstep gs_eq; nrm s1 s2 W5 F0.
    all: destruct (negb (is_extra s1 =? 0)); [| rstep aret_eq; to_DIST HC E W5 F0 s1 s2].
    all: aflat; rlock SFREE_NEEDBITS; [exact HQ0 | exact HU |]; intros [] r1 HU1 _; cbv beta.
    all: unfold BITS; rstep gr_eq; rstep us_eq; nrm s1 s2 W5 F0; unfold DROPBITS; rstep ur_eq.
    all: first [rstep us_eq; nrm s1 s2 W5 F0 | rstep aret_eq]; to_DIST HC E W5 F0 s1 s2.
  Qed.

  Definition FASTC : Prop := forall s1 s2 c r,
    CORE s1 -> is_mode s1 = LEN -> IEQ s1 s2 -> UW s1 c r -> 6 <= ir_have r -> 258 <= ir_left r ->
    RES2 (amodify (fun w => LOAD (inflate_fast (RESTORE w))) (mkW s1 c r))
         (amodify (fun w => LOAD (inflate_fast (RESTORE w))) (mkW s2 c r)).
  Hypothesis fastc : FASTC.

  Lemma len_tail_cong : forall here0 s1 s2 c r, CORE s1 -> is_mode s1 = LEN -> IEQ s1 s2 -> UW s1 c r ->
    RES2 ((DROPBITS (code_bits here0);; add_back iv (code_bits here0);;
           us (fun s : inflate_state => iset_length s (code_val here0));;
           (if code_op here0 =? 0 then set_mode LIT
            else if negb (Z.land (code_op here0) 32 =? 0) then set_back iv (-1);; set_mode TYPE
            else if negb (Z.land (code_op here0) 64 =? 0) then go_bad MSG_invalid_literal_length_code
            else us (fun s : inflate_state => iset_extra s (Z.land (code_op here0) 15));; set_mode LENEXT;; arm_LENEXT iv))%am (mkW s1 c r))
         ((DROPBITS (code_bits here0);; add_back iv (code_bits here0);;
           us (fun s : inflate_state => iset_length s (code_val here0));;
           (if code_op here0 =? 0 then set_mode LIT
            else if negb (Z.land (code_op here0) 32 =? 0) then set_back iv (-1);; set_mode TYPE
            else if negb (Z.land (code_op here0) 64 =? 0) then go_bad MSG_invalid_literal_length_code
            else us (fun s : inflate_state => iset_extra s (Z.land (code_op here0) 15));; set_mode LENEXT;; arm_LENEXT iv))%am (mkW s2 c r)).
  Proof.
    intros here0 s1 s2 c r HC E HQ HU. notHB HU E W5 F0. pose proof HQ as HQ0. ieq_open HQ E.
    unfold DROPBITS, add_back, set_back, aux. rstep ur_eq.
    destruct (iv_aux iv); cbv iota; [rstep us_eq | rstep aret_eq]; nrm s1 s2 W5 F0; rstep us_eq.
    all: destruct (code_op here0 =? 0); [unfold set_mode; rlast; wmid E W5 F0|].
    all: destruct (negb (Z.land (code_op here0) 32 =? 0)); [first [rstep us_eq | rstep aret_eq]; unfold set_mode; rlast; wmid E W5 F0|].
    all: destruct (negb (Z.land (code_op here0) 64 =? 0)); [unfold go_bad, set_msg, set_mode; rstep uc_eq; rlast; wmid E W5 F0|].
    all: rstep us_eq; unfold set_mode at 1; rstep us_eq; apply arm_LENEXT_cong; [core_of HC | reflexivity | ieq_close E | uw0 W5 F0].
  Qed.

  Lemma arm_LEN_cong : arm_cong LEN FCore (arm_LEN iv).
  Proof.
    intros s1 s2 c r HC E HQ HU. notHB HU E W5 F0. pose proof HQ as HQ0. ieq_open HQ E. unfold arm_LEN.
    rstep gr_eq.
    (* zlib 1.4: the fast path also needs bits < 8 *)
    destruct (iv_fast iv && (6 <=? ir_have r) && (258 <=? ir_left r) && (ir_bits r <? 8)) eqn:FP.
    - apply andb_prop in FP as [FP _].
      apply andb_prop in FP as [FP F2]. apply andb_prop in FP as [_ F1]. apply Z.leb_le in F1. apply Z.leb_le in F2.
      aflat. eapply RES2_bind; [exact (fastc s1 s2 c r HC E HQ0 HU F1 F2)|].
      intros [] s1' s2' c' r' HQ' HU' _.
      rstep gs_eq. pose proof HQ' as HQ1.
      destruct HQ' as ((Qm & _) & _). rewrite Qm.
      destruct (Z.eqb_spec (is_mode s1') TYPE) as [ET|ET].
      + auxt. rlast. apply WMID_mk.
        * apply IEQ_set_back. exact HQ1.
        * destruct HU' as (W' & G' & D'). split; [exact W'|]. sacc. split; [exact G'|]. destruct D' as [D'|(D' & M' & P')]; [left; exact D'|right]. exact (conj D' (conj M' P')).
      + apply RES2_ret. apply WMID_mk; assumption.
    - auxt. rstep us_eq.
      all: rstep gs_eq; nrm s1 s2 W5 F0.
      all: unfold DECODE1 at 1 2; aflat; eapply RES2_bind_lock; [apply DECODE_k_LOCK; intros h; exact (tbl_eq_DECODE1 s1 s2 LENS _ _ QtblL h) | first [exact HQ0 | ieq_close E] | first [exact HU | uw0 W5 F0] |].
      all: intros here r1 HU1 E1; cbv beta.
      all: destruct (DECODE_k_ret _ _ _ _ _ _ _ _ _ E1) as (r1' & Ew & Ehere); injection Ew; intros <-.
      all: destruct (negb (code_op here =? 0) && (Z.land (code_op here) 240 =? 0)) eqn:T2.
      1: aflat; unfold DECODE2 at 1 2; eapply RES2_bind_lock; [ | first [exact HQ0 | ieq_close E] | exact HU1 |];
        [ apply DECODE_k_LOCK; intros h; rewrite Ehere; sacc; apply (tbl_eq_DECODE2 s1 s2 LENS _ _ (ir_hold r1) QtblL);
          apply (tbl_eq_link s1 s2 LENS _ _ (ir_hold r1) (fun op => negb (op =? 0) && (Z.land op 240 =? 0)) QtblL lens_two_contra); revert T2; rewrite Ehere; sacc; intros T2; exact T2
        | ].
      1: intros here2 r2 HU2 E2; cbv beta; unfold DROPBITS at 1 3; rstep ur_eq;
           rstep us_eq; nrm s1 s2 W5 F0; rstep aret_eq;
           (apply len_tail_cong; [core_of HC | sacc; exact E | ieq_close E | uw0 W5 F0]).
      all: rstep aret_eq; apply len_tail_cong; [core_of HC | sacc; exact E | first [exact HQ0 | ieq_close E] | first [exact HU1 | uw0 W5 F0]].
  Qed.

  Lemma arm_LEN__cong : arm_cong LEN_ FCore (arm_LEN_ iv).
  Proof.
    intros s1 s2 c r HC E HQ HU. notHB HU E W5 F0. pose proof HQ as HQ0. ieq_open HQ E. unfold arm_LEN_, set_mode.
    rstep us_eq. apply arm_LEN_cong; [core_of HC | reflexivity | ieq_close E | uw0 W5 F0].
  Qed.
End Code.
