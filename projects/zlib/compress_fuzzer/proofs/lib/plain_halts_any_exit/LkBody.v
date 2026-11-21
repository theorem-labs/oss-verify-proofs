(** * LkBody — [if_model] totality WITHOUT the wnext clause, under the
    block band's [whave = 0 /\ sane <> 0] (q7-decode leavekill fork,
    2026-08-22, OFF-TREE SCRATCH).

    WHY THIS FILE EXISTS: the landed totality chain
    ([InflateThy.if_body_ok] -> [if_loop_total] -> [if_model_total])
    is bundled behind [if_ctx_wf], whose first conjunct
    [0 <= f_wnext c] the ratified K2/K3 premise bands do NOT supply
    (they carry [w_whave = 0] and [t_sane <> 0] only).  But under
    whave = 0 the window-copy phase — the ONLY consumer of wnext — is
    dead: at [inffast.c:163-187]'s too-far branch, [op > whave = 0]
    always holds (op >= 1 whenever the distance exceeds the emitted
    output), so the sane check fires and the body answers BodyBad
    BEFORE any wnext-fueled copy.  This file re-runs the five-lemma
    chain with [f_whave c = 0 /\ f_sane c <> 0] (plus a 16-bit dcode
    VALUE bound, needed to keep the too-far op away from the u32 wrap)
    replacing [0 <= f_wnext c].  Everything else is the landed text,
    verbatim.

    The dcode value bound is discharged at the fixed table by the
    reflective [lk_distfix_val] below (dbase tops out at 24577).

    PA-EXPORTS: lk_if_model_total0, lk_distfix_val. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits BwStream ZBitsIn Huff DeflateSpec Inflate
  InflateFast InflateThy StepReach.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  The whave-0 context contract.
   ========================================================================== *)

Definition lk_ctx_wf0 (c : IfCtx) : Prop :=
  lcode_two_level c
  /\ dcode_two_level c
  /\ lcode_len_bounded c
  /\ f_whave c = 0
  /\ f_sane c <> 0
  /\ (forall x s0,
        0 <= c_val (f_dcode c (Z.land x (f_dmask c))) < 65536
        /\ (dc_chains (c_op (f_dcode c (Z.land x (f_dmask c)))) = true ->
            0 <= c_val (f_dcode c
                   (c_val (f_dcode c (Z.land x (f_dmask c)))
                    + if_low (c_op (f_dcode c (Z.land x (f_dmask c)))) s0))
              < 65536)).

(* ==========================================================================
   2.  The distance body: too-far dies at the sane check.
   ========================================================================== *)

Lemma lk_dodist_body_ok0 :
  forall c len s3 dist,
    f_whave c = 0 -> f_sane c <> 0 ->
    0 <= dist < 4294967296 -> 3 <= len <= 258 ->
    body_out_eq (f_out s3) len (dodist_body c len s3 dist).
Proof.
  intros c len s3 dist Hwh Hsn Hdist Hlen. unfold dodist_body. cbv zeta.
  destruct (Z.ltb_spec (u32 (f_out s3 - f_beg c)) dist) as [Eod|Eod].
  - (* too far: whave = 0 and sane <> 0 force BodyBad *)
    pose proof (u32_range (f_out s3 - f_beg c)) as Hod.
    assert (Eow : u32 (dist - u32 (f_out s3 - f_beg c))
                  = dist - u32 (f_out s3 - f_beg c))
      by (apply u32_id; lia).
    rewrite Hwh.
    rewrite (proj2 (Z.ltb_lt 0 (u32 (dist - u32 (f_out s3 - f_beg c))))
               ltac:(rewrite Eow; lia)).
    rewrite (proj2 (negb_true_iff _) (proj2 (Z.eqb_neq _ 0) Hsn)).
    cbn [andb]. exact I.
  - (* direct copy: landed text verbatim *)
    destruct (if_copydirect_ok c s3 (SrcOut (f_out s3 - dist)) len Hlen)
      as [s5 [Heq Hout5]].
    rewrite Heq. cbn [body_out_eq]. exact Hout5.
Qed.

Lemma lk_if_dodist_nochain_ok0 :
  forall k c len s h,
    dc_chains (c_op h) = false ->
    f_whave c = 0 -> f_sane c <> 0 ->
    0 <= c_val h < 65536 ->
    3 <= len <= 258 ->
    body_out_eq (f_out s) len (if_dodist (S k) c len s h).
Proof.
  intros k c len s h Hnc Hwh Hsn Hval Hlen.
  destruct (Z.eqb (Z.land (c_op h) 16) 0) eqn:E16.
  - unfold dc_chains in Hnc. rewrite E16 in Hnc. cbn [andb] in Hnc.
    cbn [if_dodist]. rewrite E16, Hnc. cbn [negb body_out_eq]. exact I.
  - rewrite (if_dodist_unfold_base k c len s h E16).
    pose proof (land_15_nonneg (c_op h)) as He0.
    assert (He15 : Z.land (c_op h) 15 < 16).
    { change 15 with (Z.ones 4).
      rewrite Z.land_ones by lia.
      apply Z.mod_pos_bound. lia. }
    pose proof (if_low_range (Z.land (c_op h) 15)
                  (dodist_pull c (Z.land (c_op h) 15)
                     (if_drop (c_bits h) s)) He0) as Hlow.
    assert (Hcap : Z.shiftl 1 (Z.land (c_op h) 15) <= 32768).
    { rewrite Z.shiftl_1_l. change 32768 with (2 ^ 15).
      apply Z.pow_le_mono_r; lia. }
    assert (Hs3 : f_out (if_drop (Z.land (c_op h) 15)
                    (dodist_pull c (Z.land (c_op h) 15)
                       (if_drop (c_bits h) s)))
                  = f_out s).
    { rewrite if_drop_out, dodist_pull_out, if_drop_out. reflexivity. }
    rewrite <- Hs3.
    apply lk_dodist_body_ok0; [exact Hwh | exact Hsn | lia | exact Hlen].
Qed.

Lemma lk_if_dodist_two_ok0 :
  forall k c len s x,
    dcode_two_level c ->
    f_whave c = 0 -> f_sane c <> 0 ->
    (forall s0,
        0 <= c_val (f_dcode c (Z.land x (f_dmask c))) < 65536
        /\ (dc_chains (c_op (f_dcode c (Z.land x (f_dmask c)))) = true ->
            0 <= c_val (f_dcode c
                   (c_val (f_dcode c (Z.land x (f_dmask c)))
                    + if_low (c_op (f_dcode c (Z.land x (f_dmask c)))) s0))
              < 65536)) ->
    3 <= len <= 258 ->
    body_out_eq (f_out s) len
      (if_dodist (S (S k)) c len s (f_dcode c (Z.land x (f_dmask c)))).
Proof.
  intros k c len s x Hdt Hwh Hsn Hvals Hlen.
  set (v := Z.land x (f_dmask c)) in *.
  destruct (dc_chains (c_op (f_dcode c v))) eqn:Hch.
  - rewrite (if_dodist_chain_step (S k) c len s _ Hch).
    pose proof (Hdt v x (if_drop (c_bits (f_dcode c v)) s)
                  ltac:(reflexivity) Hch) as Hnext.
    pose proof (lk_if_dodist_nochain_ok0 k c len
                  (if_drop (c_bits (f_dcode c v)) s) _ Hnext Hwh Hsn
                  (proj2 (Hvals (if_drop (c_bits (f_dcode c v)) s))
                     eq_refl)
                  Hlen) as HH.
    rewrite if_drop_out in HH. exact HH.
  - exact (lk_if_dodist_nochain_ok0 (S k) c len s _ Hch Hwh Hsn
             (proj1 (Hvals s)) Hlen).
Qed.

(* ==========================================================================
   3.  The length side, verbatim modulo the premise swap.
   ========================================================================== *)

Lemma lk_dolen_base_ok0 :
  forall c h s1,
    dcode_two_level c -> lc_len_ok h ->
    f_whave c = 0 -> f_sane c <> 0 ->
    (forall x s0,
        0 <= c_val (f_dcode c (Z.land x (f_dmask c))) < 65536
        /\ (dc_chains (c_op (f_dcode c (Z.land x (f_dmask c)))) = true ->
            0 <= c_val (f_dcode c
                   (c_val (f_dcode c (Z.land x (f_dmask c)))
                    + if_low (c_op (f_dcode c (Z.land x (f_dmask c)))) s0))
              < 65536)) ->
    Z.eqb (Z.land (c_op h) 16) 0 = false ->
    body_out_lt (f_out s1) (dolen_base c h s1).
Proof.
  intros c h s1 Hdt Hlc Hwh Hsn Hvals E16.
  apply Z.eqb_neq in E16.
  destruct (Hlc E16) as [Hv3 Hv258].
  pose proof (land_15_nonneg (c_op h)) as He0.
  unfold dolen_base. cbv zeta.
  assert (Hpow : 1 <= Z.shiftl 1 (Z.land (c_op h) 15)).
  { rewrite Z.shiftl_1_l.
    apply Z.pow_le_mono_r with (a := 2) (b := 0)
                               (c := Z.land (c_op h) 15);
      [lia | exact He0]. }
  destruct (Z.eqb (Z.land (c_op h) 15) 0) eqn:Ee.
  - apply (body_out_eq_lt _ (c_val h)); [lia|].
    rewrite <- (if_refill15_out c s1).
    apply lk_if_dodist_two_ok0 with (k := 14%nat);
      [exact Hdt | exact Hwh | exact Hsn | exact (Hvals _) |].
    apply Z.eqb_eq in Ee. rewrite Ee in Hv258. cbn in Hv258. lia.
  - pose proof (if_low_range (Z.land (c_op h) 15)
                  (dolen_pull c (Z.land (c_op h) 15) s1) He0) as Hlow.
    apply (body_out_eq_lt _ (c_val h
             + if_low (Z.land (c_op h) 15)
                 (dolen_pull c (Z.land (c_op h) 15) s1)));
      [lia|].
    assert (Hs3 : f_out (if_refill15 c (if_drop (Z.land (c_op h) 15)
                           (dolen_pull c (Z.land (c_op h) 15) s1)))
                  = f_out s1).
    { rewrite if_refill15_out, if_drop_out, dolen_pull_out. reflexivity. }
    rewrite <- Hs3.
    apply lk_if_dodist_two_ok0 with (k := 14%nat);
      [exact Hdt | exact Hwh | exact Hsn | exact (Hvals _) | lia].
Qed.

Lemma lk_if_dolen_nochain_ok0 :
  forall k c s h,
    lc_chains (c_op h) = false ->
    dcode_two_level c -> lc_len_ok h ->
    f_whave c = 0 -> f_sane c <> 0 ->
    (forall x s0,
        0 <= c_val (f_dcode c (Z.land x (f_dmask c))) < 65536
        /\ (dc_chains (c_op (f_dcode c (Z.land x (f_dmask c)))) = true ->
            0 <= c_val (f_dcode c
                   (c_val (f_dcode c (Z.land x (f_dmask c)))
                    + if_low (c_op (f_dcode c (Z.land x (f_dmask c)))) s0))
              < 65536)) ->
    body_out_lt (f_out s) (if_dolen (S k) c s h).
Proof.
  intros k c s h Hnc Hdt Hlc Hwh Hsn Hvals.
  destruct (Z.eqb (c_op h) 0) eqn:E0.
  - cbn [if_dolen]. rewrite E0. cbn [body_out_lt if_put if_drop f_out].
    lia.
  - destruct (Z.eqb (Z.land (c_op h) 16) 0) eqn:E16.
    + unfold lc_chains in Hnc. rewrite E0, E16 in Hnc.
      cbn [negb andb] in Hnc.
      cbn [if_dolen]. rewrite E0, E16, Hnc. cbn [negb].
      destruct (Z.eqb (Z.land (c_op h) 32) 0);
        cbn [negb body_out_lt]; exact I.
    + rewrite (if_dolen_unfold_base k c s h E0 E16).
      pose proof (lk_dolen_base_ok0 c h (if_drop (c_bits h) s)
                    Hdt Hlc Hwh Hsn Hvals E16) as HH.
      rewrite if_drop_out in HH. exact HH.
Qed.

Lemma lk_if_dolen_two_ok0 :
  forall k c s v n,
    lcode_two_level c -> dcode_two_level c ->
    (lc_chains (c_op (f_lcode c v)) = true ->
       exists x, v = Z.land x (f_lmask c)) ->
    lcode_len_bounded_upto c n -> lcode_index_range n c ->
    0 <= v < n ->
    f_whave c = 0 -> f_sane c <> 0 ->
    (forall x s0,
        0 <= c_val (f_dcode c (Z.land x (f_dmask c))) < 65536
        /\ (dc_chains (c_op (f_dcode c (Z.land x (f_dmask c)))) = true ->
            0 <= c_val (f_dcode c
                   (c_val (f_dcode c (Z.land x (f_dmask c)))
                    + if_low (c_op (f_dcode c (Z.land x (f_dmask c)))) s0))
              < 65536)) ->
    body_out_lt (f_out s) (if_dolen (S (S k)) c s (f_lcode c v)).
Proof.
  intros k c s v n Hlt Hdt Hwv Hup [Hroot Hchain] Hv Hwh Hsn Hvals.
  destruct (lc_chains (c_op (f_lcode c v))) eqn:Hch.
  - rewrite (if_dolen_chain_step (S k) c s _ Hch).
    destruct (Hwv eq_refl) as (xw & Hxw).
    pose proof (Hlt v xw (if_drop (c_bits (f_lcode c v)) s) Hxw Hch)
      as Hnext.
    pose proof (lk_if_dolen_nochain_ok0 k c
                  (if_drop (c_bits (f_lcode c v)) s) _ Hnext Hdt
                  (Hup _ (Hchain v (if_drop (c_bits (f_lcode c v)) s)
                            Hv Hch)) Hwh Hsn Hvals) as HH.
    rewrite if_drop_out in HH. exact HH.
  - exact (lk_if_dolen_nochain_ok0 (S k) c s _ Hch Hdt (Hup v Hv)
             Hwh Hsn Hvals).
Qed.

(* ==========================================================================
   4.  Body, step, loop, model.
   ========================================================================== *)

Lemma lk_if_body_ok0 :
  forall c s, lk_ctx_wf0 c -> body_out_lt (f_out s) (if_body c s).
Proof.
  intros c s (Hlt & Hdt & Hlb & Hwh & Hsn & Hvals). unfold if_body.
  destruct Hlb as [n [Hup Hrange]].
  pose proof (lk_if_dolen_two_ok0 14 c (if_refill15 c s)
                (Z.land (f_hold (if_refill15 c s)) (f_lmask c)) n
                Hlt Hdt ltac:(intros _; eexists; reflexivity) Hup Hrange
                (proj1 Hrange (if_refill15 c s)) Hwh Hsn Hvals) as HH.
  rewrite if_refill15_out in HH. exact HH.
Qed.

Lemma lk_if_step_ok0 :
  forall c s, lk_ctx_wf0 c ->
    match if_step c s with
    | IfCont s' => f_out s < f_out s' /\ f_out s' < f_end c
    | IfFuel => False
    | _ => True
    end.
Proof.
  intros c s Hwf. rewrite if_step_unfold.
  exact (if_step_ok_abs c (if_body c s) (f_out s)
           (lk_if_body_ok0 c s Hwf)).
Qed.

Lemma lk_if_loop_total0 :
  forall n c s, lk_ctx_wf0 c -> f_end c - f_out s <= Z.of_nat n ->
    exists r, if_loop (S n) c s = Some r /\ loop_done r.
Proof.
  induction n as [|n IH]; intros c s Hwf Hb; rewrite if_loop_S;
    pose proof (lk_if_step_ok0 c s Hwf) as HS;
    destruct (if_step c s) as [s1|s1|s1|s1 m|] eqn:E.
  - destruct HS as [H1 H2]. cbn [Z.of_nat] in Hb. lia.
  - exists (IfStop s1). split; [reflexivity | exact I].
  - exists (IfEob s1). split; [reflexivity | exact I].
  - exists (IfBad s1 m). split; [reflexivity | exact I].
  - contradiction.
  - destruct HS as [H1 H2]. apply IH; [exact Hwf | lia].
  - exists (IfStop s1). split; [reflexivity | exact I].
  - exists (IfEob s1). split; [reflexivity | exact I].
  - exists (IfBad s1 m). split; [reflexivity | exact I].
  - contradiction.
Qed.

Theorem lk_if_model_total0 :
  forall a, lk_ctx_wf0 (if_ctx a) -> exists y, if_model a = Some y.
Proof.
  intros a Hwf.
  unfold if_model.
  destruct (lk_if_loop_total0
              (Z.to_nat (f_end (if_ctx a) - f_out (if_st0 a)))
              (if_ctx a) (if_st0 a) Hwf ltac:(lia)) as [r [Heq Hd]].
  rewrite Heq.
  destruct r as [s1|s1|s1|s1 m|]; cbn [loop_done] in Hd;
    try contradiction; eexists; reflexivity.
Qed.

(* ==========================================================================
   5.  The fixed distance table's 16-bit value bound, reflectively.
   ========================================================================== *)

Definition lk_chk_val16 (h : Code) : bool :=
  (0 <=? c_val h) && (c_val h <? 65536).

Lemma lk_distfix_chk :
  forallb (fun t => lk_chk_val16 (code_of3 t)) distfix_list = true.
Proof. vm_compute. reflexivity. Qed.

Lemma lk_distfix_val : forall i, 0 <= c_val (distfix i) < 65536.
Proof.
  intros i.
  pose proof (tbl_of_list_all lk_chk_val16 distfix_list lk_distfix_chk
                ltac:(vm_compute; reflexivity) i) as H.
  unfold lk_chk_val16 in H.
  apply andb_prop in H. destruct H as [H1 H2].
  split; [apply Z.leb_le; exact H1 | apply Z.ltb_lt; exact H2].
Qed.

Set Printing Width 2000.
Print Assumptions lk_if_model_total0.
Print Assumptions lk_distfix_val.
