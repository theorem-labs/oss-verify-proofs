(** * Spec.PngModel.InflateThy14 — [InflateThy]'s per-arm obligations for 1.4's six twin arms, the 1.4 step
    obligation, "[inflate_model14] never declines", and the 32/32 coverage at 1.4

    (option (A)).  Every arm that 1.4 leaves alone keeps its
    [InflateThy] lemma; the six twins ([Inflate14]) get theirs here, as copies of 1.3.1's proofs with the twin
    names:
    - LEN / LEN_: the fast branch is guarded by [have >= 6 && left >= 258 && bits < 8]; the fast-path call contract
      is owed only under that guard; the slow branch's proof never read the guard;
    - CODELENS: its in-call tail is 1.4's LEN_;
    - LENLENS: distcode is set with lencode (nothing the obligation reads); its tail is 1.4's CODELENS;
    - TABLE: its tail is 1.4's LENLENS;
    - HEAD: the window-size check before the [wbits] store. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Base.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import ZBitsIn.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Inftrees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import InflateFast.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Checksum.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import GtItTotal.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import InflateThy.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Inflate14.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.
Local Open Scope bool_scope.

(** ** HEAD at 1.4 *)
Lemma arm_HEAD14 :
  forall c q, q_pos q -> q_mode q = M_HEAD -> arm_ok q (inf_HEAD14 c q).
Proof.
  intros c q Hp Hm. pose proof Hp as (Hh & Hb & Hl).
  unfold inf_HEAD14. cbv zeta.
  dif.
  { apply arm_ok_mono with (q1 := qmode q M_TYPEDO).
    - apply rank2_le' with (m := M_HEAD) (m' := M_TYPEDO);
        [exact Hm | reflexivity |].
      cbn [inf_mrank]. unfold inf_budget. bsimp. lia.
    - apply arm_TYPEDO with (m := M_TYPEDO);
        [unfold q_pos; bsimp; exact Hp | reflexivity | cbn [inf_mrank]; lia]. }
  destruct (inf_nb 16 (q_br q)) as [b|b] eqn:Enb; [|exact I].
  pose proof Enb as Enb'. apply inf_nb_bud in Enb' as (E1 & E2 & E3).
  pose proof (inf_nb_ok _ _ _ Enb) as E16.
  dif; [contsplit M_HEAD M_FLAGS Hm Hp|].
  dif; [contsplit M_HEAD M_BAD Hm Hp|].
  dif; [contsplit M_HEAD M_BAD Hm Hp|].
  dif; [contsplit M_HEAD M_BAD Hm Hp|].
  match goal with
  | |- context[if ?B then M_TYPE else M_DICTID] => destruct B
  end.
  - contsplit M_HEAD M_TYPE Hm Hp.
  - contsplit M_HEAD M_DICTID Hm Hp.
Qed.

(** ** LEN / LEN_ at 1.4 *)
Definition inf_LEN14' (q : InfSt) : InfStep :=
  let st := q_st q in
  let tb := s_tab st in
  let b  := q_br q in
  let o  := q_ob q in
  if Z.leb 6 (br_have b) && Z.leb 258 (o_left o) && Z.ltb (br_bits b) 8 then
    match if_model (len_args q) with
    | None => InfFuel
    | Some y => InfCont (len_post q y)
    end
  else
    let q0 := qset_st q (set_back st 0) in
    match inf_decode sub_len (tbl_of st (t_lencode tb)) (t_lenbits tb) b with
    | DecFuel      => InfFuel
    | DecLeave b'  => InfLeave (qset_br q0 b')
    | DecOk h b' nb =>
        let st1 := set_length (set_back (q_st q0) (0 + nb)) (c_val h) in
        let q1  := qset_br (qset_st q0 st1) b' in
        if Z.eqb (c_op h) 0 then
          InfCont (qmode q1 M_LIT)
        else if negb (Z.eqb (Z.land (c_op h) 32) 0) then
          InfCont (qmode (qset_st q1 (set_back (q_st q1) (-1))) M_TYPE)
        else if negb (Z.eqb (Z.land (c_op h) 64) 0) then
          InfCont (qbad q1 MSG_LIT_LEN_CODE)
        else
          let st2 := set_extra (q_st q1) (Z.land (c_op h) 15) in
          inf_LENEXT (qmode (qset_st q1 st2) M_LENEXT)
    end.

Lemma inf_LEN14_eq : forall q, inf_LEN14 q = inf_LEN14' q.
Proof. reflexivity. Qed.

(** The 1.4 fast-path gate. *)
Definition len_gate14 (q : InfSt) : bool :=
  Z.leb 6 (br_have (q_br q)) && Z.leb 258 (o_left (q_ob q)) && Z.ltb (br_bits (q_br q)) 8.

Lemma arm_LEN14 :
  forall q, q_pos q -> q_mode q = M_LEN ->
    (len_gate14 q = true ->
       if_wf_lax (len_args q) /\ if_wf_tbl (len_args q)
       /\ br_have (q_br q) <= 4294967290
       /\ o_left (q_ob q) <= 4294967295) ->
    LcSide (tbl_of (q_st q) (t_lencode (s_tab (q_st q)))) ->
    TblSide (tbl_of (q_st q) (t_distcode (s_tab (q_st q)))) ->
    0 <= w_wnext (s_win (q_st q)) ->
    arm_ok q (inf_LEN14 q).
Proof.
  intros q Hp Hm Hfast Hlc Htd Hwn. pose proof Hp as (Hh & Hb & Hl).
  assert (Hm' : h_mode (s_hdr (q_st q)) = M_LEN) by exact Hm.
  rewrite inf_LEN14_eq. unfold inf_LEN14', len_gate14 in *. cbv zeta.
  destruct (Z.leb 6 (br_have (q_br q)) && Z.leb 258 (o_left (q_ob q)) && Z.ltb (br_bits (q_br q)) 8)
    eqn:Egate.
  - destruct (Hfast eq_refl) as (Hwf & Htbl & Hain & Haout).
    destruct (if_model_total_lax (len_args q) Hwf) as (y & EM).
    rewrite EM. cbv beta iota.
    pose proof (if_model_bud (len_args q) y Hwf Htbl Hain Haout EM)
      as (Bud & Yai & Yb & Yao & Yh).
    cbn [len_args a_avail_in a_bits a_avail_out] in Bud.
    unfold len_post. cbv zeta.
    destruct (y_exit y) eqn:Eex; cbv beta iota.
    + lp_norm. rewrite Hm. cbv beta iota.
      cbn [arm_ok]. split.
      * unfold q_pos. lp_norm. repeat split; lia.
      * apply rank2_lt' with (m := M_LEN) (m' := M_LEN);
          [exact Hm | lp_norm; exact Hm | apply q_pos_bud, Hp |].
        unfold inf_budget. lp_norm. lia.
    + lp_norm. cbv beta iota.
      cbn [arm_ok]. split.
      * unfold q_pos. lp_norm. repeat split; lia.
      * apply rank2_lt' with (m := M_LEN) (m' := M_TYPE);
          [exact Hm | lp_norm; reflexivity | apply q_pos_bud, Hp |].
        cbn [inf_mrank]. unfold inf_budget. lp_norm. lia.
    + lp_norm. cbv beta iota.
      cbn [arm_ok]. split.
      * unfold q_pos. lp_norm. repeat split; lia.
      * apply rank2_lt' with (m := M_LEN) (m' := M_BAD);
          [exact Hm | lp_norm; reflexivity | apply q_pos_bud, Hp |].
        cbn [inf_mrank]. unfold inf_budget. lp_norm. lia.
  - destruct Hlc as (Lb0 & Leob & Lval).
    destruct (inf_decode sub_len
                (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
                (t_lenbits (s_tab (q_st q))) (q_br q)) as [h b' nb|b'|]
      eqn:Edec.
    2:{ exact I. }
    2:{ exfalso. exact (inf_decode_no_fuel _ _ _ _ Hh Edec). }
    destruct (inf_decode_ok_facts _ _ _ _ _ _ _ Lb0 Edec)
      as ((i0 & Hhe) & Hnb).
    pose proof (inf_decode_bud _ _ _ _ _ _ _ Edec) as (Ebud & Ehave).
    specialize (Ehave Hh).
    pose proof (inf_decode_bits_nonneg _ _ _ _ _ _ _ Edec) as Ebits.
    cbv zeta.
    destruct (Z.eqb (c_op h) 0) eqn:E0.
    + cbn [arm_ok]. split.
      * unfold q_pos. bsimp. repeat split; lia.
      * apply rank2_lt' with (m := M_LEN) (m' := M_LIT);
          [exact Hm | bsimp; reflexivity | apply q_pos_bud, Hp |].
        cbn [inf_mrank]. unfold inf_budget. bsimp. lia.
    + destruct (negb (Z.eqb (Z.land (c_op h) 32) 0)) eqn:E32.
      * apply Bool.negb_true_iff, Z.eqb_neq in E32.
        assert (Hnb1 : 1 <= nb).
        { eapply inf_decode_eob_pos;
            [exact Lb0 | exact Leob | exact Edec |].
          rewrite Hhe in E32 |- *. exact E32. }
        cbn [arm_ok]. split.
        { unfold q_pos. bsimp. repeat split; lia. }
        apply rank2_lt' with (m := M_LEN) (m' := M_TYPE);
          [exact Hm | bsimp; reflexivity | apply q_pos_bud, Hp |].
        cbn [inf_mrank]. unfold inf_budget. bsimp. lia.
      * destruct (negb (Z.eqb (Z.land (c_op h) 64) 0)) eqn:E64.
        { cbn [arm_ok]. split.
          - unfold q_pos. bsimp. repeat split; lia.
          - apply rank2_lt' with (m := M_LEN) (m' := M_BAD);
              [exact Hm | bsimp; reflexivity | apply q_pos_bud, Hp |].
            cbn [inf_mrank]. unfold inf_budget. bsimp. lia. }
        apply Bool.negb_false_iff, Z.eqb_eq in E64.
        apply Bool.negb_false_iff, Z.eqb_eq in E32.
        apply Z.eqb_neq in E0.
        assert (Hval : 1 <= c_val h).
        { eapply inf_decode_val_pos; [exact Lval | exact Edec | | |];
            rewrite Hhe in E0, E32, E64 |- *; assumption. }
        pose proof (land15_range (c_op h)) as He15.
        eapply (arm_ok_mono _ q).
        2:{ apply arm_LENEXT;
            [ unfold q_pos; bsimp; repeat split; lia
            | reflexivity
            | bsimp; lia
            | bsimp; lia
            | bsimp; lia
            | bsimp; exact Htd ]. }
        apply rank2_le' with (m := M_LEN) (m' := M_LENEXT);
          [ exact Hm | reflexivity
          | cbn [inf_mrank]; unfold inf_budget; bsimp; lia ].
Qed.

Lemma arm_LEN_14 :
  forall q, q_pos q -> q_mode q = M_LEN_ ->
    (len_gate14 q = true ->
       if_wf_lax (len_args q) /\ if_wf_tbl (len_args q)
       /\ br_have (q_br q) <= 4294967290
       /\ o_left (q_ob q) <= 4294967295) ->
    LcSide (tbl_of (q_st q) (t_lencode (s_tab (q_st q)))) ->
    TblSide (tbl_of (q_st q) (t_distcode (s_tab (q_st q)))) ->
    0 <= w_wnext (s_win (q_st q)) ->
    arm_ok q (inf_LEN_14 q).
Proof.
  intros q Hp Hm Hfast Hlc Htd Hwn.
  unfold inf_LEN_14.
  eapply (arm_ok_mono _ q).
  2:{ apply arm_LEN14.
      - unfold q_pos. bsimp. exact Hp.
      - reflexivity.
      - exact Hfast.
      - exact Hlc.
      - exact Htd.
      - bsimp. exact Hwn. }
  apply rank2_le' with (m := M_LEN_) (m' := M_LEN);
    [exact Hm | reflexivity |].
  cbn [inf_mrank]. unfold inf_budget. bsimp. lia.
Qed.

(** ** TABLE / LENLENS / CODELENS at 1.4 *)
Lemma arm_CODELENS14 :
  forall c q, q_pos q -> q_mode q = M_CODELENS ->
    TblSide (tbl_of (q_st q) (t_lencode (s_tab (q_st q)))) ->
    lens_ok (b_lens (s_bld (q_st q))) ->
    0 <= b_have (s_bld (q_st q)) ->
    0 <= b_nlen (s_bld (q_st q)) -> 0 <= b_ndist (s_bld (q_st q)) ->
    (forall q', q_mode q' = M_LEN_ -> q_pos q' ->
       arm_ok q' (inf_LEN_14 q')) ->
    arm_ok q (inf_CODELENS14 c q).
Proof.
  intros c q Hp Hm Htl Hlens Hhave Hnlen Hndist HLEN.
  pose proof Hp as (Hh & Hb & Hl).
  unfold inf_CODELENS14. cbv zeta beta.
  destruct (cl_loop_at_codelens_fuel
              (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
              (t_lenbits (s_tab (q_st q)))
              (b_nlen (s_bld (q_st q)) + b_ndist (s_bld (q_st q)))
              {| cl_have := b_have (s_bld (q_st q));
                 cl_lens := b_lens (s_bld (q_st q));
                 cl_br := q_br q |}
              ltac:(cbn [cl_br]; lia) ltac:(cbn [cl_have]; lia))
    as (r & Hr & Hexit).
  rewrite Hr. cbv beta iota.
  pose proof (cl_loop_walk
                (S (Z.to_nat (b_nlen (s_bld (q_st q))
                              + b_ndist (s_bld (q_st q)))))
                (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
                (t_lenbits (s_tab (q_st q)))
                (b_nlen (s_bld (q_st q)) + b_ndist (s_bld (q_st q)))
                {| cl_have := b_have (s_bld (q_st q));
                   cl_lens := b_lens (s_bld (q_st q));
                   cl_br := q_br q |} r Htl Hh Hb Hlens Hr) as HW.
  cbn [cl_br cl_lens cl_have] in HW.
  destruct r as [s1|s1|s1 m1|s1|]; cbn [cl_exit] in Hexit;
    try contradiction; [| |exact I].
  - destruct HW as (W1 & W2 & W3 & W4).
    destruct (Z.eqb (cl_lens s1 256) 0).
    { cbn [arm_ok]. split.
      - unfold q_pos. bsimp. repeat split; lia.
      - apply rank2_lt' with (m := M_CODELENS) (m' := M_BAD);
          [exact Hm | bsimp; reflexivity | apply q_pos_bud, Hp |].
        cbn [inf_mrank]. unfold inf_budget. bsimp. lia. }
    unfold inf_table.
    assert (HLB1 : LensBounded (cl_lens s1) (b_nlen (s_bld (q_st q))))
      by (intros i _; apply W4).
    match goal with
    | |- context [it_model CT_LENS ?l ?cs ?rt ?t0] =>
        remember (it_model CT_LENS l cs rt t0) as R1 eqn:EI1
    end.
    destruct R1 as [o1|].
    2:{ exfalso.
        exact (it_model_total _ _ _ _ _ Hnlen HLB1 (eq_sym EI1)). }
    cbv beta iota zeta.
    destruct (negb (Z.eqb (o_ret o1) 0)).
    { cbn [arm_ok]. split.
      - unfold q_pos. bsimp. repeat split; lia.
      - apply rank2_lt' with (m := M_CODELENS) (m' := M_BAD);
          [exact Hm | bsimp; reflexivity | apply q_pos_bud, Hp |].
        cbn [inf_mrank]. unfold inf_budget. bsimp. lia. }
    assert (HLB2 : LensBounded (fun i => cl_lens s1 (i + b_nlen (s_bld (q_st q))))
                     (b_ndist (s_bld (q_st q))))
      by (intros i _; cbv beta; apply W4).
    match goal with
    | |- context [it_model CT_DISTS ?l ?cs ?rt ?t0] =>
        remember (it_model CT_DISTS l cs rt t0) as R2 eqn:EI2
    end.
    destruct R2 as [o2|].
    2:{ exfalso.
        exact (it_model_total _ _ _ _ _ Hndist HLB2 (eq_sym EI2)). }
    cbv beta iota zeta.
    destruct (negb (Z.eqb (o_ret o2) 0)).
    { cbn [arm_ok]. split.
      - unfold q_pos. bsimp. repeat split; lia.
      - apply rank2_lt' with (m := M_CODELENS) (m' := M_BAD);
          [exact Hm | bsimp; reflexivity | apply q_pos_bud, Hp |].
        cbn [inf_mrank]. unfold inf_budget. bsimp. lia. }
    destruct (Z.eqb (n_flush c) Z_TREES); [exact I|].
    eapply (arm_ok_mono _ q).
    2:{ apply HLEN; [bsimp; reflexivity |].
        unfold q_pos. bsimp. repeat split; lia. }
    apply rank2_le' with (m := M_CODELENS) (m' := M_LEN_);
      [exact Hm | bsimp; reflexivity |].
    cbn [inf_mrank]. unfold inf_budget. bsimp. lia.
  - destruct HW as (W1 & W2 & W3 & W4).
    cbn [arm_ok]. split.
    + unfold q_pos. bsimp. repeat split; lia.
    + apply rank2_lt' with (m := M_CODELENS) (m' := M_BAD);
        [exact Hm | bsimp; reflexivity | apply q_pos_bud, Hp |].
      cbn [inf_mrank]. unfold inf_budget. bsimp. lia.
Qed.

Lemma arm_LENLENS14 :
  forall c q, q_pos q -> q_mode q = M_LENLENS ->
    lens_ok (b_lens (s_bld (q_st q))) ->
    (forall q', q_mode q' = M_CODELENS -> q_pos q' ->
       arm_ok q' (inf_CODELENS14 c q')) ->
    arm_ok q (inf_LENLENS14 c q).
Proof.
  intros c q Hp Hm Hlens HCL. pose proof Hp as (Hh & Hb & Hl).
  unfold inf_LENLENS14. cbv zeta.
  pose proof (ll_go_walk 19 (b_ncode (s_bld (q_st q)))
                (b_have (s_bld (q_st q))) (b_lens (s_bld (q_st q)))
                (q_br q) Hh Hb Hlens) as HW.
  match goal with
  | |- context [ll_go ?f ?nc ?hv0 ?ls0 ?b0] =>
      remember (ll_go f nc hv0 ls0 b0) as LG eqn:ELG
  end.
  destruct LG as [hv ls b|hv ls b]; [|exact I].
  destruct HW as (W1 & W2 & W3 & W4).
  remember (ll_zero 19 hv ls) as LZ eqn:EZ.
  destruct LZ as [hv1 ls1]. cbv beta iota.
  assert (Hls1 : lens_ok ls1).
  { pose proof (ll_zero_walk 19 hv ls W4) as HZ. rewrite <- EZ in HZ.
    exact HZ. }
  unfold inf_table.
  assert (HLB : LensBounded ls1 19) by (intros i _; apply Hls1).
  match goal with
  | |- context [it_model CT_CODES ?l ?cs ?rt ?t0] =>
      remember (it_model CT_CODES l cs rt t0) as R1 eqn:EI1
  end.
  destruct R1 as [o1|].
  2:{ exfalso.
      assert (Hc19 : 0 <= 19) by lia.
      exact (it_model_total _ _ _ _ _ Hc19 HLB (eq_sym EI1)). }
  cbv beta iota zeta.
  destruct (negb (Z.eqb (o_ret o1) 0)).
  { cbn [arm_ok]. split.
    - unfold q_pos. bsimp. repeat split; lia.
    - apply rank2_lt' with (m := M_LENLENS) (m' := M_BAD);
        [exact Hm | bsimp; reflexivity | apply q_pos_bud, Hp |].
      cbn [inf_mrank]. unfold inf_budget. bsimp. lia. }
  eapply (arm_ok_mono _ q).
  2:{ apply HCL; [bsimp; reflexivity |].
      unfold q_pos. bsimp. repeat split; lia. }
  apply rank2_le' with (m := M_LENLENS) (m' := M_CODELENS);
    [exact Hm | bsimp; reflexivity |].
  cbn [inf_mrank]. unfold inf_budget. bsimp. lia.
Qed.

Lemma arm_TABLE14 :
  forall c q, q_pos q -> q_mode q = M_TABLE ->
    lens_ok (b_lens (s_bld (q_st q))) ->
    (forall q', q_mode q' = M_CODELENS -> q_pos q' ->
       arm_ok q' (inf_CODELENS14 c q')) ->
    arm_ok q (inf_TABLE14 c q).
Proof.
  intros c q Hp Hm Hlens HCL. pose proof Hp as (Hh & Hb & Hl).
  unfold inf_TABLE14.
  destruct (inf_nb 14 (q_br q)) as [b|b] eqn:Enb; [|exact I].
  pose proof (inf_nb_ok _ _ _ Enb) as E14.
  apply inf_nb_bud in Enb as (E1 & E2 & E3). specialize (E3 Hh).
  cbv zeta.
  destruct (Z.ltb 286 (br_bits_of 5 b + 257)
            || Z.ltb 30 (br_bits_of 5 (br_dropbits 5 b) + 1)).
  { cbn [arm_ok]. split.
    - unfold q_pos. bsimp. repeat split; lia.
    - apply rank2_lt' with (m := M_TABLE) (m' := M_BAD);
        [exact Hm | bsimp; reflexivity | apply q_pos_bud, Hp |].
      cbn [inf_mrank]. unfold inf_budget. bsimp. lia. }
  eapply (arm_ok_mono _ q).
  2:{ apply arm_LENLENS14.
      - unfold q_pos. bsimp. repeat split; lia.
      - bsimp. reflexivity.
      - cbn [qmode qset_st q_st set_mode set_have set_ncode set_ndist
             set_nlen s_bld b_lens]. exact Hlens.
      - exact HCL. }
  apply rank2_le' with (m := M_TABLE) (m' := M_LENLENS);
    [exact Hm | bsimp; reflexivity |].
  cbn [inf_mrank]. unfold inf_budget. bsimp. lia.
Qed.

(** ** The 1.4 step obligation and "[inflate_model14] never declines" *)
Definition step_ok14 (c : InfCtx) (q : InfSt) : Prop :=
  match inf_step14 c q with
  | InfCont q'  => q_pos q' /\ (inf_rank2 q' < inf_rank2 q)%nat
  | InfLeave _  => True
  | InfRet _ _  => True
  | InfDead _   => False
  | InfFuel     => False
  end.

Section InflateTermination14.

  Variable c : InfCtx.
  Variable Hstep : forall q, q_pos q -> step_ok14 c q.

  Lemma inf_loop14_reaches_exit :
    forall n q, q_pos q -> (inf_rank2 q <= n)%nat ->
      exists r, inf_loop14 (S n) c q = Some r /\ exit_step r.
  Proof.
    induction n as [|n IH]; intros q Hp Hr;
      rewrite inf_loop14_S;
      pose proof (Hstep q Hp) as HS; unfold step_ok14 in HS;
      destruct (inf_step14 c q) as [q'|q'|q' r0|m0|] eqn:E.
    - destruct HS as [Hp' Hlt]. lia.
    - exists (InfLeave q'). split; [reflexivity | exact I].
    - exists (InfRet q' r0). split; [reflexivity | exact I].
    - contradiction.
    - contradiction.
    - destruct HS as [Hp' Hlt]. apply IH; [exact Hp' | lia].
    - exists (InfLeave q'). split; [reflexivity | exact I].
    - exists (InfRet q' r0). split; [reflexivity | exact I].
    - contradiction.
    - contradiction.
  Qed.

  Theorem inflate_model14_total :
    forall a, inf_ctx a = c ->
      0 <= g_avail_in a -> 0 <= g_avail_out a -> 0 <= s_bits (g_st a) ->
      exists r, inflate_model14 a = Some r.
  Proof.
    intros a Hc Hin Hout Hbits. unfold inflate_model14.
    destruct (g_state_null a || g_out_null a
              || (g_in_null a && negb (Z.eqb (g_avail_in a) 0)));
      [eexists; reflexivity|].
    rewrite Hc.
    assert (Hb0 : br_bits (q_br (inf_st0 a)) = s_bits (g_st a)).
    { unfold inf_st0. destruct (h_mode (s_hdr (g_st a))); reflexivity. }
    assert (Hp0 : q_pos (inf_st0 a)).
    { unfold q_pos. rewrite Hb0. cbn [inf_st0 q_br q_ob br_have o_left].
      repeat split; lia. }
    set (n := Z.to_nat (33 * (8 * br_have (q_br (inf_st0 a))
                              + br_bits (q_br (inf_st0 a))
                              + o_left (q_ob (inf_st0 a)) + 1))).
    assert (Hfuel : inf_fuel (inf_st0 a) = S n) by reflexivity.
    assert (Hle : (inf_rank2 (inf_st0 a) <= n)%nat).
    { pose proof (inf_fuel_dominates_rank2 (inf_st0 a) (q_pos_bud _ Hp0)) as HD.
      rewrite Hfuel in HD. lia. }
    destruct (inf_loop14_reaches_exit n (inf_st0 a) Hp0 Hle) as [r [Heq Hr]].
    rewrite Hfuel, Heq.
    destruct r as [q'|q'|q' r0|m0|]; cbn [exit_step] in Hr; try contradiction.
    - destruct (inf_leave c q') as [q'' rr]. eexists; reflexivity.
    - eexists; reflexivity.
  Qed.

End InflateTermination14.

(** ** [step_ok14_covered], 32/32 at 1.4: [step_ok_covered]'s premises, with the LEN / LEN_ fast-path contract
    owed under the 1.4 gate and the in-call tails at their 1.4 twins. *)
Theorem step_ok14_covered :
  forall c q,
    q_pos q ->
    0 <= u_length (s_cur (q_st q)) ->
    (q_mode q = M_MATCH -> match_side q) ->
    (q_mode q = M_FLAGS \/ q_mode q = M_TIME \/ q_mode q = M_OS
       \/ q_mode q = M_EXLEN ->
     (forall j, 0 <= br_in (q_br q) j) /\ 0 <= br_hold (q_br q)) ->
    (q_mode q = M_LENEXT \/ q_mode q = M_DIST \/ q_mode q = M_DISTEXT ->
       1 <= u_length (s_cur (q_st q)) /\ 0 <= w_wnext (s_win (q_st q))) ->
    (q_mode q = M_LENEXT \/ q_mode q = M_DISTEXT ->
       0 <= u_extra (s_cur (q_st q)) <= 15) ->
    (q_mode q = M_LENEXT \/ q_mode q = M_DIST ->
       TblSide (tbl_of (q_st q) (t_distcode (s_tab (q_st q))))) ->
    (q_mode q = M_DISTEXT ->
       0 <= u_offset (s_cur (q_st q))
       /\ u_offset (s_cur (q_st q)) + Z.shiftl 1 (u_extra (s_cur (q_st q)))
          <= 4294967296) ->
    (q_mode q = M_LEN \/ q_mode q = M_LEN_ ->
       (len_gate14 q = true ->
          if_wf_lax (len_args q) /\ if_wf_tbl (len_args q)
          /\ br_have (q_br q) <= 4294967290
          /\ o_left (q_ob q) <= 4294967295)
       /\ LcSide (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
       /\ TblSide (tbl_of (q_st q) (t_distcode (s_tab (q_st q))))
       /\ 0 <= w_wnext (s_win (q_st q))) ->
    (q_mode q = M_TABLE \/ q_mode q = M_LENLENS \/ q_mode q = M_CODELENS ->
       lens_ok (b_lens (s_bld (q_st q)))) ->
    (q_mode q = M_TABLE \/ q_mode q = M_LENLENS ->
       forall q', q_mode q' = M_CODELENS -> q_pos q' ->
         arm_ok q' (inf_CODELENS14 c q')) ->
    (q_mode q = M_CODELENS ->
       TblSide (tbl_of (q_st q) (t_lencode (s_tab (q_st q))))
       /\ 0 <= b_have (s_bld (q_st q))
       /\ 0 <= b_nlen (s_bld (q_st q)) /\ 0 <= b_ndist (s_bld (q_st q))
       /\ (forall q', q_mode q' = M_LEN_ -> q_pos q' ->
             arm_ok q' (inf_LEN_14 q'))) ->
    step_ok14 c q.
Proof.
  intros c q Hp Hlen Hms Hgz Hcs Hce Hct Hco Hln Hlens3 Hcl Hcod.
  destruct (q_mode q) eqn:Hm.
  all: try (unfold step_ok14; rewrite inf_step14_same by (rewrite Hm; discriminate);
            fold (step_ok c q);
            apply step_ok_covered; rewrite ?Hm;
            first [ assumption
                  | intros Hx;
                    first [ discriminate Hx
                          | destruct Hx as [Hx|Hx]; discriminate Hx
                          | destruct Hx as [Hx|[Hx|Hx]]; discriminate Hx
                          | destruct Hx as [Hx|[Hx|[Hx|Hx]]]; discriminate Hx ] ]).
  all: unfold step_ok14, inf_step14; rewrite Hm.
  - exact (arm_HEAD14 c q Hp Hm).
  - exact (arm_TABLE14 c q Hp Hm (Hlens3 (or_introl eq_refl))
             (Hcl (or_introl eq_refl))).
  - exact (arm_LENLENS14 c q Hp Hm
             (Hlens3 (or_intror (or_introl eq_refl)))
             (Hcl (or_intror eq_refl))).
  - destruct (Hcod eq_refl) as (C1 & C2 & C3 & C4 & C5).
    exact (arm_CODELENS14 c q Hp Hm C1
             (Hlens3 (or_intror (or_intror eq_refl))) C2 C3 C4 C5).
  - destruct (Hln (or_intror eq_refl)) as (L1 & L2 & L3 & L4).
    exact (arm_LEN_14 q Hp Hm L1 L2 L3 L4).
  - destruct (Hln (or_introl eq_refl)) as (L1 & L2 & L3 & L4).
    exact (arm_LEN14 q Hp Hm L1 L2 L3 L4).
Qed.
