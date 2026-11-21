(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateArms.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InftreesCoverage.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ItProof.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeD.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeT.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeH.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeK.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeA1.
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

Lemma match_copy_step : forall win ob put from copy, 0 < copy < 2 ^ 32 ->
  match_copy win (ob, put, from, copy) =
    let v := match from with FWin i => arr_get win i | FOut i => arr_get ob i end in
    let st' := ((arr_set ob put v : arr), put + 1, from_succ from, copy - 1) in
    if copy - 1 =? 0 then st' else match_copy win st'.
Proof.
  intros win ob put from copy Hc. unfold match_copy at 1. cbn [snd]. rewrite loopZ_step by lia. cbv beta iota zeta.
  rewrite (wrap32_id (copy - 1)) by lia.
  destruct (Z.eqb_spec (copy - 1) 0) as [E|E]; cbn [negb]; [reflexivity|].
  unfold match_copy. cbn [snd]. reflexivity.
Qed.

Lemma match_copy_spec : forall m win ob put from, Z.of_nat (S m) < 2 ^ 32 ->
  exists ob' from', match_copy win (ob, put, from, Z.of_nat (S m)) = (ob', put + Z.of_nat (S m), from', 0)
                    /\ arr_len ob' = arr_len ob.
Proof.
  induction m as [|m IH]; intros win ob put from Hm.
  - rewrite match_copy_step by (cbn; lia). cbv zeta. change (Z.of_nat 1 - 1 =? 0) with true. cbv iota.
    eexists _, _. split; [reflexivity|]. apply arr_len_set.
  - rewrite match_copy_step by lia. cbv zeta.
    replace (Z.of_nat (S (S m)) - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (Z.of_nat (S (S m)) - 1) with (Z.of_nat (S m)) by lia.
    lazymatch goal with |- exists _ _, match_copy _ (?ob1, ?p1, ?f1, _) = _ /\ _ =>
      destruct (IH win ob1 p1 f1 ltac:(lia)) as (ob' & from' & E & L) end.
    rewrite E. eexists _, _. split; [f_equal; f_equal; f_equal; lia|]. rewrite L. apply arr_len_set.
Qed.

Lemma match_copy_ok : forall win ob put from copy, 1 <= copy < 2 ^ 32 ->
  exists ob' from', match_copy win (ob, put, from, copy) = (ob', put + copy, from', 0) /\ arr_len ob' = arr_len ob.
Proof.
  intros win ob put from copy Hc.
  destruct (match_copy_spec (Z.to_nat (copy - 1)) win ob put from ltac:(lia)) as (ob' & from' & E & L).
  replace (Z.of_nat (S (Z.to_nat (copy - 1)))) with copy in E by lia.
  eexists _, _. split; [exact E|exact L].
Qed.

Section MatchArm.
  Variable iv : ivariant.

  Lemma match_tail : forall w0 s c r from copy,
    CORE s -> REGS c r -> is_mode s = MATCH ->
    common s -> ir_bits r < 8 -> tables s -> 1 <= is_length s -> 1 <= is_offset s < 2 ^ 32 ->
    ir_out r = arr_len (ic_outbuf c) -> (is_wbits s = 0 -> ir_put r = 0) ->
    0 < ir_left r -> 1 <= copy <= is_length s ->
    64 * ir_have r + 8 * ir_bits r + 8 * ir_left r + 1 <= PHI w0 ->
    POST w0 ((let copy := if ir_left r <? copy then ir_left r else copy in
              ur (fun r0 => irset_left r0 (wrap32 (ir_left r0 - copy))) ;;
              us (fun s0 => iset_length s0 (wrap32 (is_length s0 - copy))) ;;
              (fun w => let '(ob, put, _, _) := match_copy (is_window (w_s w)) (ic_outbuf (w_c w), ir_put (w_r w), from, copy) in
                        ARun tt (wset_r (wset_c w (icset_outbuf (w_c w) ob)) (irset_put (w_r w) put))) ;;
              do s0 <- gs (fun s0 => s0) ;
              if is_length s0 =? 0 then set_mode LEN else aret tt)%am (mkW s c r)).
  Proof.
    intros w0 s c r from copy HC HR E HCm Hb8 Htb HL HO HWF HWB Hleft Hcp HP.
    regs_open HR. cbv zeta.
    set (cp := if ir_left r <? copy then ir_left r else copy).
    assert (Hc : 1 <= cp <= copy /\ cp <= ir_left r) by (subst cp; destruct (Z.ltb_spec (ir_left r) copy); lia).
    aflat. arun ur_eq. aflat. arun us_eq. cbn [w_s w_c w_r]. sacc.
    destruct (match_copy_ok (is_window s) (ic_outbuf c) (ir_put r) from cp ltac:(lia)) as (ob' & from' & EM & LM).
    aflat. eapply POST_bind_run; [cbv beta; cbn [w_s w_c w_r]; sacc; rewrite EM; reflexivity|]. cbv beta. arun gs_eq. sacc.
    rewrite (wrap32_id (ir_left r - cp)) by lia.
    pose proof (wrap32_range (is_length s - cp)) as WR.
    destruct (Z.eqb_spec (wrap32 (is_length s - cp)) 0) as [L0|L0].
    - rewrite set_mode_eq. apply POST_ARun.
      + winv_split.
        * core_keep HC. lia.
        * unfold REGS. sacc. rewrite LM. regs_solve RIN.
        * split; [common_keep HCm|]. split; [left; exact Hb8 | tables_keep Htb].
        * rewrite LM. exact HWF.
        * intros W. exfalso. exact (proj1 HCm W).
      + phi_goal. lia.
    - rewrite aret_eq. apply POST_ARun.
      + winv_split.
        * core_keep HC. lia.
        * unfold REGS. sacc. rewrite LM. regs_solve RIN.
        * rewrite E. mred. split; [common_keep HCm|]. split; [exact Hb8|]. split; [tables_keep Htb|]. lia.
        * rewrite E. mred. rewrite LM. exact HWF.
        * intros W. exfalso. exact (proj1 HCm W).
      + phi_goal. rewrite E. mred. lia.
  Qed.

  Lemma arm_MATCH_safe : arm_safe MATCH (arm_MATCH iv).
  Proof.
    intros w0 s c r HW E HP. unfold arm_MATCH.
    pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR.
    destruct HMF as (HCm & Hb8 & Htb & HL & HO).
    pose proof HC as (_ & _ & _ & CW4 & CW5 & CW6 & CW7 & CW8 & _ & _ & _ & _ & CS & _).
    assert (HP' : 64 * ir_have r + 8 * ir_bits r + 8 * ir_left r + 1 <= PHI w0).
    { unfold PHI in HP. cbn [w_s w_c w_r] in HP. rewrite E in HP. exact HP. }
    arun gr_eq.
    destruct (Z.eqb_spec (ir_left r) 0) as [L0|L0]; [aleave; exact HW0|].
    arun gs_eq. cbv zeta.
    rewrite (wrap32_id (ir_out r - ir_left r)) by lia.
    replace (ir_out r - ir_left r) with (ir_put r) by lia.
    acase Cwin.
    -
      apply Z.ltb_lt in Cwin. cbv zeta.
      rewrite (wrap32_id (is_offset s - ir_put r)) by lia.
      rewrite CS. replace (if iv_aux iv then negb (1 =? 0) else true) with true by (destruct (iv_aux iv); reflexivity).
      rewrite Bool.andb_true_r.
      acase Cfar.
      + aflat. arun go_bad_eq. arun aret_eq. rewrite aret_eq. apply POST_ARun.
        * winv_split.
          -- core_keep HC. apply CORE_length; exact HC.
          -- eapply REGS_cview; [exact HR | reflexivity | reflexivity].
          -- exact (proj2 HCm).
          -- exact I.
          -- exact HWB.
        * phi_goal. lia.
      + apply Z.ltb_ge in Cfar.
        destruct (Z.ltb_spec (is_wnext s) (is_offset s - ir_put r)) as [Cwrap|Cwrap].
        * rewrite (wrap32_id (is_offset s - ir_put r - is_wnext s)) by lia.
          arun aret_eq.
          apply match_tail; try assumption; try lia.
          destruct (Z.ltb_spec (is_length s) (is_offset s - ir_put r - is_wnext s)); lia.
        * arun aret_eq.
          apply match_tail; try assumption; try lia.
          destruct (Z.ltb_spec (is_length s) (is_offset s - ir_put r)); lia.
    -
      arun aret_eq. apply match_tail; try assumption; lia.
  Qed.
End MatchArm.

Lemma add_back_ref : forall v s c r, add_back ivar_ref v (mkW s c r) = ARun tt (mkW (iset_back s (swrap32 (is_back s + v))) c r).
Proof. reflexivity. Qed.
Lemma set_back_ref : forall v s c r, set_back ivar_ref v (mkW s c r) = ARun tt (mkW (iset_back s v) c r).
Proof. reflexivity. Qed.
Lemma aux_ref : forall f s c r, aux ivar_ref f (mkW s c r) = ARun tt (mkW (f s) c r).
Proof. reflexivity. Qed.

Lemma arm_DISTEXT_safe : arm_safe DISTEXT (arm_DISTEXT ivar_ref).
Proof.
  intros w0 s c r HW E HP. unfold arm_DISTEXT. arun gs_eq.
  pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR.
  destruct HMF as (HCm & Hbx & Htb & HL & HX & HO). pose proof (CORE_length s HC) as HL0.
  acase Cx.
  - assert (Xnz : is_extra s <> 0) by (intros X; rewrite X in Cx; discriminate Cx).
    aflat.
    destruct (NEEDBITS_spec c (is_extra s) s r HR ltac:(lia)) as [(r1 & EQ & HR1 & HP1 & Hn1 & Hb1)|(r1 & EQ & HR1 & HP1 & Hb1 & Hh1)].
    + eapply POST_bind_run; [exact EQ|]. cbv beta iota.
      pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & El1 & _). pose proof (pulled_phi r r1 HP1) as PH1.
      pose proof HR1 as (_ & _ & _ & _ & _ & _ & [RB1 RHO1] & _).
      aflat. arun BITS_eq. aflat. arun us_eq. aflat. arun DROPBITS_eq. aflat. arun add_back_ref. arun set_mode_eq. sacc.
      rewrite (BITSv_mod (ir_hold r1) (is_extra s)) by lia.
      pose proof (mod_pow2_range (ir_hold r1) (is_extra s) ltac:(lia)) as MV.
      pose proof (pow2_le (is_extra s) 15 ltac:(lia)) as P15.
      rewrite (wrap32_id (is_offset s + _)) by (change (2 ^ 15) with 32768 in P15; lia).
      rewrite (wrap32_id (ir_bits r1 - is_extra s)) by lia.
      apply (POST_arm MATCH (arm_MATCH ivar_ref) _ _ _ _ (arm_MATCH_safe ivar_ref)).
      * winv_split.
        -- core_keep HC. exact HL0.
        -- apply REGS_holdbits; [exact HR1|]. apply HB_drop; [split; [exact RB1|exact RHO1]|lia].
        -- split; [common_keep HCm|]. split; [lia|]. split; [tables_keep Htb|]. change (2 ^ 15) with 32768 in P15. lia.
        -- rewrite Eo1. exact HWF.
        -- rewrite Ep1. exact HWB.
      * reflexivity.
      * phi_norm E HP. lia.
    + eapply POST_bind_leave; [exact EQ|].
      pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & _).
      apply (WINV_regs s c r r1 HW0 HR1 Eo1 Ep1). rewrite E. mred. intros _. repeat (split; [first [assumption | lia]|]). lia.
  - apply Z.eqb_eq in Cx || (destruct (Z.eqb_spec (is_extra s) 0) as [Cx'|Cx']; [clear Cx; rename Cx' into Cx|discriminate Cx]).
    arun aret_eq. arun set_mode_eq.
    apply (POST_arm MATCH (arm_MATCH ivar_ref) _ _ _ _ (arm_MATCH_safe ivar_ref)).
    + winv_split.
      * core_keep HC. exact HL0.
      * exact HR.
      * split; [common_keep HCm|]. split; [lia|]. split; [tables_keep Htb|]. lia.
      * exact HWF.
      * exact HWB.
    + reflexivity.
    + phi_norm E HP. lia.
Qed.

Lemma dist_tail : forall w0 s c r here,
  CORE s -> REGS c r -> is_mode s = DIST -> common s -> tables s -> 1 <= is_length s ->
  ir_out r = arr_len (ic_outbuf c) -> (is_wbits s = 0 -> ir_put r = 0) ->
  1 <= code_bits here <= ir_bits r -> ir_bits r - code_bits here < 8 ->
  ((exists sy, 0 <= sy < nsyms DISTS /\ code_op here = fst (sym_entry DISTS sy) /\ code_val here = snd (sym_entry DISTS sy)) \/ code_op here = 64) ->
  64 * ir_have r + 8 * ir_bits r + 8 * ir_left r <= PHI w0 ->
  POST w0 ((DROPBITS (code_bits here) ;; add_back ivar_ref (code_bits here) ;;
            if negb (Z.land (code_op here) 64 =? 0) then go_bad MSG_invalid_distance_code
            else us (fun s0 => iset_extra (iset_offset s0 (code_val here)) (Z.land (code_op here) 15)) ;;
                 set_mode DISTEXT ;; arm_DISTEXT ivar_ref)%am (mkW s c r)).
Proof.
  intros w0 s c r here HC HR E HCm Htb HL HWF HWB Hcb Hb8 Hsh HP.
  regs_open HR. pose proof (CORE_length s HC) as HL0.
  aflat. arun DROPBITS_eq. aflat. arun add_back_ref. rewrite (wrap32_id (ir_bits r - code_bits here)) by lia.
  assert (HRd : REGS c (irset_bits (irset_hold r (Z.shiftr (ir_hold r) (code_bits here))) (ir_bits r - code_bits here))).
  { apply REGS_holdbits; [exact HR|]. apply HB_drop; [split; [exact RB|exact RHO]|lia]. }
  assert (BADc : POST w0 ((go_bad MSG_invalid_distance_code) (mkW (iset_back s (swrap32 (is_back s + code_bits here))) c
                             (irset_bits (irset_hold r (Z.shiftr (ir_hold r) (code_bits here))) (ir_bits r - code_bits here))))).
  { unfold go_bad. arun set_msg_eq. rewrite set_mode_eq. apply POST_ARun.
    - winv_split.
      + core_keep HC. exact HL0.
      + eapply REGS_cview; [exact HRd|reflexivity|reflexivity].
      + exact (proj2 HCm).
      + exact I.
      + exact HWB.
    - phi_goal. lia. }
  destruct Hsh as [[sy (Hsy & Hop & Hv)]|Hop].
  - cbn [nsyms] in Hsy. pose proof (dists_sym_cases sy Hsy) as L.
    destruct (sym_entry DISTS sy) as [op v] eqn:Es. cbn [fst snd] in Hop, Hv. rewrite Hop, Hv.
    destruct L as [(L1 & L2 & L3)|[L1 L2]].
    + destruct (dist_op_facts op L1) as (F1 & F2 & F3 & F4). rewrite F2, F3. cbn [Z.eqb negb].
      aflat. arun us_eq. arun set_mode_eq.
      pose proof (pow2_le (op - 16) 13 ltac:(lia)) as P13. change (2 ^ 13) with 8192 in P13.
      pose proof (pow2_pos (op - 16) ltac:(lia)) as P0.
      apply (POST_arm DISTEXT (arm_DISTEXT ivar_ref) _ _ _ _ arm_DISTEXT_safe).
      * winv_split.
        -- core_keep HC. exact HL0.
        -- exact HRd.
        -- split; [common_keep HCm|]. split; [left; exact Hb8|]. split; [tables_keep Htb|]. lia.
        -- exact HWF.
        -- exact HWB.
      * reflexivity.
      * phi_goal. lia.
    + rewrite L1. cbn [Z.land Z.eqb negb]. exact BADc.
  - rewrite Hop. cbn [Z.land Z.eqb negb]. exact BADc.
Qed.

Lemma arm_DIST_safe : arm_safe DIST (arm_DIST ivar_ref).
Proof.
  intros w0 s c r HW E HP. unfold arm_DIST. arun gs_eq.
  pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR.
  destruct HMF as (HCm & Hbx & Htb & HL).
  assert (HP0 : 64 * ir_have r + 8 * ir_bits r + 8 * ir_left r <= PHI w0).
  { unfold PHI at 1 in HP. cbn [w_s w_c w_r] in HP. rewrite E in HP. change (rank DIST) with 0 in HP. lia. }
  destruct (cpok_TBLg DISTS s (is_distcode s) (is_distbits s) (proj2 Htb)) as (used & HT & _).
  pose proof (T_root _ _ _ _ HT) as HR15.
  aflat.
  destruct (DECODE1_spec c s (is_distcode s) DISTS (is_distbits s) used HT r HR)
    as [(r1 & here & EQ & HR1 & HP1 & Eh & Hle & Hb1)|(r1 & EQ & HR1 & HP1 & Hh1 & Hb1)].
  - eapply POST_bind_run; [exact EQ|]. cbv beta iota.
    pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & El1 & _). pose proof (pulled_phi r r1 HP1) as PH1.
    pose proof HR1 as (_ & _ & _ & _ & _ & _ & [RB1 RHO1] & _).
    destruct (root_cell DISTS _ _ used HT (ir_hold r1 mod 2 ^ is_distbits s) (ridx_range _ _ _ _ HT _)) as (Hbits & RLk & RNk).
    rewrite <- Eh in Hbits, RLk, RNk.

    assert (SAME : ir_bits r1 = ir_bits r -> ir_hold r1 = ir_hold r).
    { intros Eb. destruct HP1 as (k & _ & _ & _ & _ & Bk & Mk & Hk & _). rewrite <- Mk. symmetry. apply Z.mod_small. rewrite <- Eb. exact Hk. }
    aflat. acase Clink.
    +
      apply Z.eqb_eq in Clink.
      assert (HLk : is_linkb here = true).
      { destruct (is_linkb here) eqn:Lk; [reflexivity|]. exfalso. destruct (RNk eq_refl) as [_ SH].
        apply (notlink_land240 DISTS here SH ltac:(discriminate)); [|exact Clink].
        destruct SH as [[sy (Hsy & Hop & _)]|Hop]; [|rewrite Hop; discriminate].
        cbn [nsyms] in Hsy. pose proof (dists_sym_cases sy Hsy) as L. destruct (sym_entry DISTS sy) as [op v]. cbn [fst] in Hop. rewrite Hop. lia. }
      destruct (RLk HLk) as (Hbr & Hop & Hv1 & Hv2).
      aflat.
      destruct (DECODE2_spec c s (is_distcode s) DISTS (is_distbits s) used HT r1 here HR1 Eh HLk Hle)
        as [(r2 & here2 & EQ2 & HR2 & HP2 & Eh2 & Hsb & Hle2 & Hb2)|(r2 & EQ2 & HR2 & HP2 & Hh2 & Hb2)].
      * eapply POST_bind_run; [exact EQ2|]. cbv beta iota.
        pose proof (pulled_out r1 r2 HP2) as (Eo2 & Ep2 & El2 & _). pose proof (pulled_phi r1 r2 HP2) as PH2.
        pose proof HR2 as (_ & _ & _ & _ & _ & _ & [RB2 RHO2] & _).
        pose proof (sub_cell DISTS _ _ used HT (ir_hold r1 mod 2 ^ is_distbits s)
                      (ir_hold r2 mod 2 ^ (code_bits here + code_op here) / 2 ^ code_bits here)) as SC.
        rewrite <- Eh in SC.
        specialize (SC (ridx_range _ _ _ _ HT _) HLk (subidx_range (ir_hold r2) (code_bits here) (code_op here) ltac:(lia) ltac:(lia))).
        unfold subix in Eh2. rewrite <- Eh2 in SC. destruct SC as (Sb & SNL & SN).
        aflat. arun DROPBITS_eq. aflat. arun add_back_ref. arun aret_eq. sacc.
        rewrite (wrap32_id (ir_bits r2 - code_bits here)) by lia.
        assert (SAME2 : ir_bits r2 = ir_bits r1 -> ir_hold r2 = ir_hold r1).
        { intros Eb. destruct HP2 as (k & _ & _ & _ & _ & Bk & Mk & Hk & _). rewrite <- Mk. symmetry. apply Z.mod_small. rewrite <- Eb. exact Hk. }

        assert (B8 : ir_bits r2 - code_bits here - code_bits here2 < 8).
        { destruct Hb2 as [Hb2|Hb2]; [|lia]. destruct Hb1 as [Hb1|Hb1]; [|lia].
          destruct Hbx as [Hbx|Hbx]; [lia|]. exfalso.
          rewrite (lneed_lneedg s) in Hbx. unfold lneedg in Hbx.
          rewrite <- (SAME Hb1), <- Eh, HLk in Hbx. rewrite (SAME2 Hb2) in Eh2. rewrite <- Eh2 in Hbx. lia. }
        apply dist_tail;
          first [ assumption
                | core_keep HC; apply CORE_length; exact HC
                | apply REGS_holdbits; [exact HR2|]; apply HB_drop; [split; [exact RB2|exact RHO2]|lia]
                | common_keep HCm
                | tables_keep Htb
                | rewrite Eo2, Eo1; exact HWF
                | rewrite Ep2, Ep1; exact HWB
                | sacc; lia ].
      * eapply POST_bind_leave; [exact EQ2|].
        pose proof (pulled_out r1 r2 HP2) as (Eo2 & Ep2 & _).
        apply (WINV_regs s c r r2 HW0 HR2 ltac:(rewrite Eo2; exact Eo1) ltac:(rewrite Ep2; exact Ep1)).
        rewrite E. mred. intros _. split; [exact HCm|]. split; [|split; [exact Htb|exact HL]].
        right. rewrite lneed_lneedg. exact Hb2.
    +
      assert (HLk : is_linkb here = false).
      { destruct (is_linkb here) eqn:Lk; [|reflexivity]. exfalso. destruct (RLk eq_refl) as (_ & Hop & _).
        rewrite (land240_small (code_op here)) in Clink by lia. discriminate Clink. }
      destruct (RNk HLk) as [Hbr SH].
      arun aret_eq.
      assert (B8 : ir_bits r1 - code_bits here < 8).
      { destruct Hb1 as [Hb1|Hb1]; [|lia]. destruct Hbx as [Hbx|Hbx]; [lia|]. exfalso.
        rewrite (lneed_lneedg s) in Hbx. unfold lneedg in Hbx.
        rewrite <- (SAME Hb1), <- Eh, HLk in Hbx. lia. }
      apply dist_tail;
        first [ assumption
              | rewrite Eo1; exact HWF
              | rewrite Ep1; exact HWB
              | lia ].
  - eapply POST_bind_leave; [exact EQ|].
    pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & _).
    apply (WINV_regs s c r r1 HW0 HR1 Eo1 Ep1).
    rewrite E. mred. intros _. split; [exact HCm|]. split; [|split; [exact Htb|exact HL]].
    right. rewrite lneed_lneedg. pose proof (lneedg_range DISTS _ _ used HT (ir_hold r1)) as [_ LR]. lia.
Qed.

Lemma arm_LENEXT_safe : arm_safe LENEXT (arm_LENEXT ivar_ref).
Proof.
  intros w0 s c r HW E HP. unfold arm_LENEXT. arun gs_eq.
  pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR.
  destruct HMF as (HCm & Hbx & Htb & HX & HL). pose proof (CORE_length s HC) as HL0.
  acase Cx.
  - assert (Xnz : is_extra s <> 0) by (intros X; rewrite X in Cx; discriminate Cx).
    aflat.
    destruct (NEEDBITS_spec c (is_extra s) s r HR ltac:(lia)) as [(r1 & EQ & HR1 & HP1 & Hn1 & Hb1)|(r1 & EQ & HR1 & HP1 & Hb1 & Hh1)].
    + eapply POST_bind_run; [exact EQ|]. cbv beta iota.
      pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & El1 & _). pose proof (pulled_phi r r1 HP1) as PH1.
      pose proof HR1 as (_ & _ & _ & _ & _ & _ & [RB1 RHO1] & _).
      aflat. arun BITS_eq. aflat. arun us_eq. aflat. arun DROPBITS_eq. aflat. arun add_back_ref.
      aflat. arun aux_ref. arun set_mode_eq. sacc.
      rewrite (BITSv_mod (ir_hold r1) (is_extra s)) by lia.
      pose proof (mod_pow2_range (ir_hold r1) (is_extra s) ltac:(lia)) as MV.
      pose proof (pow2_le (is_extra s) 15 ltac:(lia)) as P15. change (2 ^ 15) with 32768 in P15.
      rewrite (wrap32_id (is_length s + _)) by lia.
      rewrite (wrap32_id (ir_bits r1 - is_extra s)) by lia.
      apply (POST_arm DIST (arm_DIST ivar_ref) _ _ _ _ arm_DIST_safe).
      * winv_split.
        -- core_keep HC. lia.
        -- apply REGS_holdbits; [exact HR1|]. apply HB_drop; [split; [exact RB1|exact RHO1]|lia].
        -- split; [common_keep HCm|]. split; [lia|]. split; [tables_keep Htb|]. lia.
        -- rewrite Eo1. exact HWF.
        -- rewrite Ep1. exact HWB.
      * reflexivity.
      * phi_norm E HP. lia.
    + eapply POST_bind_leave; [exact EQ|].
      pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & _).
      apply (WINV_regs s c r r1 HW0 HR1 Eo1 Ep1). rewrite E. mred. intros _. repeat (split; [first [assumption | lia]|]). lia.
  - arun aret_eq. aflat. arun aux_ref. arun set_mode_eq.
    apply (POST_arm DIST (arm_DIST ivar_ref) _ _ _ _ arm_DIST_safe).
    + winv_split.
      * core_keep HC. exact HL0.
      * exact HR.
      * split; [common_keep HCm|]. split; [lia|]. split; [tables_keep Htb|]. lia.
      * exact HWF.
      * exact HWB.
    + reflexivity.
    + phi_norm E HP. lia.
Qed.
