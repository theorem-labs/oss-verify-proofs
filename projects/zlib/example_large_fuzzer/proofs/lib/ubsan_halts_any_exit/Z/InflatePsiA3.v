(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg ZIface InflateState Inftrees InflateFast InflateArms Inflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InftreesCoverage AdlerModel RefInflateSafeD RefInflateSafeT RefInflateSafeH RefInflateSafeK RefInflateSafeA1 RefInflateSafeA3.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflatePsi InflatePsi1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Section MatchArm.
  Variable iv : ivariant.

  Lemma match_tail_psi : forall w0 s c r from copy,
    CORE s -> REGS c r -> is_mode s = MATCH -> 1 <= is_length s ->
    0 < ir_left r -> 1 <= copy <= is_length s ->
    PPw w0 (mkW s c r) ->
    PP w0 ((let copy := if ir_left r <? copy then ir_left r else copy in
              ur (fun r0 => irset_left r0 (wrap32 (ir_left r0 - copy))) ;;
              us (fun s0 => iset_length s0 (wrap32 (is_length s0 - copy))) ;;
              (fun w => let '(ob, put, _, _) := match_copy (is_window (w_s w)) (ic_outbuf (w_c w), ir_put (w_r w), from, copy) in
                        ARun tt (wset_r (wset_c w (icset_outbuf (w_c w) ob)) (irset_put (w_r w) put))) ;;
              do s0 <- gs (fun s0 => s0) ;
              if is_length s0 =? 0 then set_mode LEN else aret tt)%am (mkW s c r)).
  Proof.
    intros w0 s c r from copy HC HR E HL Hleft Hcp HQ.
    regs_open HR. pose proof (CORE_length s HC) as HL0. cbv zeta.
    set (cp := if ir_left r <? copy then ir_left r else copy).
    assert (Hc : 1 <= cp <= copy /\ cp <= ir_left r) by (subst cp; destruct (Z.ltb_spec (ir_left r) copy); lia).
    aflat. arun2 ur_eq. aflat. arun2 us_eq. cbn [w_s w_c w_r]. sacc.
    destruct (match_copy_ok (is_window s) (ic_outbuf c) (ir_put r) from cp ltac:(lia)) as (ob' & from' & EM & LM).
    aflat. eapply PP_bind_run; [cbv beta; cbn [w_s w_c w_r]; sacc; rewrite EM; reflexivity|]. cbv beta. arun2 gs_eq. sacc.
    pose proof (wrap32_range (is_length s - cp)) as WR.
    rewrite (wrap32_id (is_length s - cp)) in * by lia.
    destruct (Z.eqb_spec (is_length s - cp) 0) as [L0|L0].
    - rewrite set_mode_eq. apply PP_ARun. ppw_open E HQ. rewrite ?(wrap32_id (is_length s - cp)) by lia. lia.
    - rewrite aret_eq. apply PP_ARun. ppw_open E HQ. rewrite ?(wrap32_id (is_length s - cp)) by lia. lia.
  Qed.

  Lemma arm_MATCH_psi : arm_psi MATCH (arm_MATCH iv).
  Proof.
    intros w0 s c r HW E HQ. unfold arm_MATCH.
    pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR.
    destruct HMF as (HCm & Hb8 & Htb & HL & HO).
    pose proof HC as (_ & _ & _ & CW4 & CW5 & CW6 & CW7 & CW8 & _ & _ & _ & _ & CS & _).
    arun2 gr_eq.
    destruct (Z.eqb_spec (ir_left r) 0) as [L0|L0]; [aleave2; exact HQ|].
    arun2 gs_eq. cbv zeta.
    rewrite (wrap32_id (ir_out r - ir_left r)) by lia.
    replace (ir_out r - ir_left r) with (ir_put r) by lia.
    acase2 Cwin.
    -
      apply Z.ltb_lt in Cwin. cbv zeta.
      rewrite (wrap32_id (is_offset s - ir_put r)) by lia.
      rewrite CS. replace (if iv_aux iv then negb (1 =? 0) else true) with true by (destruct (iv_aux iv); reflexivity).
      rewrite Bool.andb_true_r.
      acase2 Cfar.
      + aflat. arun2 go_bad_eq. arun2 aret_eq. rewrite aret_eq. apply PP_ARun. ppw E HQ.
      + apply Z.ltb_ge in Cfar.
        destruct (Z.ltb_spec (is_wnext s) (is_offset s - ir_put r)) as [Cwrap|Cwrap].
        * rewrite (wrap32_id (is_offset s - ir_put r - is_wnext s)) by lia.
          arun2 aret_eq.
          apply match_tail_psi; try assumption; try lia.
          destruct (Z.ltb_spec (is_length s) (is_offset s - ir_put r - is_wnext s)); lia.
        * arun2 aret_eq.
          apply match_tail_psi; try assumption; try lia.
          destruct (Z.ltb_spec (is_length s) (is_offset s - ir_put r)); lia.
    -
      arun2 aret_eq. apply match_tail_psi; try assumption; lia.
  Qed.
End MatchArm.


Lemma arm_DISTEXT_psi : arm_psi DISTEXT (arm_DISTEXT ivar_ref).
Proof.
  intros w0 s c r HW E HQ. unfold arm_DISTEXT. arun2 gs_eq.
  pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR.
  destruct HMF as (HCm & Hbx & Htb & HL & HX & HO). pose proof (CORE_length s HC) as HL0.
  acase2 Cx.
  - assert (Xnz : is_extra s <> 0) by (intros X; rewrite X in Cx; discriminate Cx).
    aflat.
    destruct (NEEDBITS_spec c (is_extra s) s r HR ltac:(lia)) as [(r1 & EQ & HR1 & HP1 & Hn1 & Hb1)|(r1 & EQ & HR1 & HP1 & Hb1 & Hh1)].
    + eapply PP_bind_run; [exact EQ|]. cbv beta iota.
      pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & El1 & _). pose proof (pulled_psi r r1 HP1) as PS1.
      pose proof HR1 as (_ & _ & _ & _ & _ & _ & [RB1 RHO1] & _).
      aflat. arun2 BITS_eq. aflat. arun2 us_eq. aflat. arun2 DROPBITS_eq. aflat. arun2 add_back_ref. arun2 set_mode_eq. sacc.
      rewrite (BITSv_mod (ir_hold r1) (is_extra s)) by lia.
      pose proof (mod_pow2_range (ir_hold r1) (is_extra s) ltac:(lia)) as MV.
      pose proof (pow2_le (is_extra s) 15 ltac:(lia)) as P15.
      rewrite (wrap32_id (is_offset s + _)) by (change (2 ^ 15) with 32768 in P15; lia).
      rewrite (wrap32_id (ir_bits r1 - is_extra s)) by lia.
      apply (PP_arm MATCH (arm_MATCH ivar_ref) _ _ _ _ (arm_MATCH_psi ivar_ref)).
      * winv_split.
        -- core_keep HC. exact HL0.
        -- apply REGS_holdbits; [exact HR1|]. apply HB_drop; [split; [exact RB1|exact RHO1]|lia].
        -- split; [common_keep HCm|]. split; [lia|]. split; [tables_keep Htb|]. change (2 ^ 15) with 32768 in P15. lia.
        -- rewrite Eo1. exact HWF.
        -- rewrite Ep1. exact HWB.
      * reflexivity.
      * ppw E HQ.
    + eapply PP_bind_leave; [exact EQ|]. exact (PPw_pulled w0 s c r r1 HQ HP1).
  - apply Z.eqb_eq in Cx || (destruct (Z.eqb_spec (is_extra s) 0) as [Cx'|Cx']; [clear Cx; rename Cx' into Cx|discriminate Cx]).
    arun2 aret_eq. arun2 set_mode_eq.
    apply (PP_arm MATCH (arm_MATCH ivar_ref) _ _ _ _ (arm_MATCH_psi ivar_ref)).
    + winv_split.
      * core_keep HC. exact HL0.
      * exact HR.
      * split; [common_keep HCm|]. split; [lia|]. split; [tables_keep Htb|]. lia.
      * exact HWF.
      * exact HWB.
    + reflexivity.
    + ppw E HQ.
Qed.


Lemma dist_tail_psi : forall w0 s c r here,
  CORE s -> REGS c r -> is_mode s = DIST -> common s -> tables s -> 1 <= is_length s ->
  ir_out r = arr_len (ic_outbuf c) -> (is_wbits s = 0 -> ir_put r = 0) ->
  1 <= code_bits here <= ir_bits r -> ir_bits r - code_bits here < 8 ->
  ((exists sy, 0 <= sy < nsyms DISTS /\ code_op here = fst (sym_entry DISTS sy) /\ code_val here = snd (sym_entry DISTS sy)) \/ code_op here = 64) ->
  PPw w0 (mkW s c r) ->
  PP w0 ((DROPBITS (code_bits here) ;; add_back ivar_ref (code_bits here) ;;
            if negb (Z.land (code_op here) 64 =? 0) then go_bad MSG_invalid_distance_code
            else us (fun s0 => iset_extra (iset_offset s0 (code_val here)) (Z.land (code_op here) 15)) ;;
                 set_mode DISTEXT ;; arm_DISTEXT ivar_ref)%am (mkW s c r)).
Proof.
  intros w0 s c r here HC HR E HCm Htb HL HWF HWB Hcb Hb8 Hsh HQ.
  regs_open HR. pose proof (CORE_length s HC) as HL0.
  aflat. arun2 DROPBITS_eq. aflat. arun2 add_back_ref. rewrite (wrap32_id (ir_bits r - code_bits here)) by lia.
  assert (HRd : REGS c (irset_bits (irset_hold r (Z.shiftr (ir_hold r) (code_bits here))) (ir_bits r - code_bits here))).
  { apply REGS_holdbits; [exact HR|]. apply HB_drop; [split; [exact RB|exact RHO]|lia]. }
  assert (BADc : PP w0 ((go_bad MSG_invalid_distance_code) (mkW (iset_back s (swrap32 (is_back s + code_bits here))) c
                             (irset_bits (irset_hold r (Z.shiftr (ir_hold r) (code_bits here))) (ir_bits r - code_bits here))))).
  { unfold go_bad. arun2 set_msg_eq. rewrite set_mode_eq. apply PP_ARun. ppw E HQ. }
  destruct Hsh as [[sy (Hsy & Hop & Hv)]|Hop].
  - cbn [nsyms] in Hsy. pose proof (dists_sym_cases sy Hsy) as L.
    destruct (sym_entry DISTS sy) as [op v] eqn:Es. cbn [fst snd] in Hop, Hv. rewrite Hop, Hv.
    destruct L as [(L1 & L2 & L3)|[L1 L2]].
    + destruct (dist_op_facts op L1) as (F1 & F2 & F3 & F4). rewrite F2, F3. cbn [Z.eqb negb].
      aflat. arun2 us_eq. arun2 set_mode_eq.
      pose proof (pow2_le (op - 16) 13 ltac:(lia)) as P13. change (2 ^ 13) with 8192 in P13.
      pose proof (pow2_pos (op - 16) ltac:(lia)) as P0.
      apply (PP_arm DISTEXT (arm_DISTEXT ivar_ref) _ _ _ _ arm_DISTEXT_psi).
      * winv_split.
        -- core_keep HC. exact HL0.
        -- exact HRd.
        -- split; [common_keep HCm|]. split; [left; exact Hb8|]. split; [tables_keep Htb|]. lia.
        -- exact HWF.
        -- exact HWB.
      * reflexivity.
      * ppw E HQ.
    + rewrite L1. cbn [Z.land Z.eqb negb]. exact BADc.
  - rewrite Hop. cbn [Z.land Z.eqb negb]. exact BADc.
Qed.

Lemma arm_DIST_psi : arm_psi DIST (arm_DIST ivar_ref).
Proof.
  intros w0 s c r HW E HQ. unfold arm_DIST. arun2 gs_eq.
  pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR.
  destruct HMF as (HCm & Hbx & Htb & HL).
  destruct (cpok_TBLg DISTS s (is_distcode s) (is_distbits s) (proj2 Htb)) as (used & HT & _).
  pose proof (T_root _ _ _ _ HT) as HR15.
  aflat.
  destruct (DECODE1_spec c s (is_distcode s) DISTS (is_distbits s) used HT r HR)
    as [(r1 & here & EQ & HR1 & HP1 & Eh & Hle & Hb1)|(r1 & EQ & HR1 & HP1 & Hh1 & Hb1)].
  - eapply PP_bind_run; [exact EQ|]. cbv beta iota.
    pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & El1 & _). pose proof (pulled_psi r r1 HP1) as PS1.
    pose proof HR1 as (_ & _ & _ & _ & _ & _ & [RB1 RHO1] & _).
    destruct (root_cell DISTS _ _ used HT (ir_hold r1 mod 2 ^ is_distbits s) (ridx_range _ _ _ _ HT _)) as (Hbits & RLk & RNk).
    rewrite <- Eh in Hbits, RLk, RNk.
    assert (SAME : ir_bits r1 = ir_bits r -> ir_hold r1 = ir_hold r).
    { intros Eb. destruct HP1 as (k & _ & _ & _ & _ & Bk & Mk & Hk & _). rewrite <- Mk. symmetry. apply Z.mod_small. rewrite <- Eb. exact Hk. }
    assert (HQ1 : PPw w0 (mkW s c r1)) by exact (PPw_pulled w0 s c r r1 HQ HP1).
    aflat. acase2 Clink.
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
      * eapply PP_bind_run; [exact EQ2|]. cbv beta iota.
        pose proof (pulled_out r1 r2 HP2) as (Eo2 & Ep2 & El2 & _). pose proof (pulled_psi r1 r2 HP2) as PS2.
        pose proof HR2 as (_ & _ & _ & _ & _ & _ & [RB2 RHO2] & _).
        pose proof (sub_cell DISTS _ _ used HT (ir_hold r1 mod 2 ^ is_distbits s)
                      (ir_hold r2 mod 2 ^ (code_bits here + code_op here) / 2 ^ code_bits here)) as SC.
        rewrite <- Eh in SC.
        specialize (SC (ridx_range _ _ _ _ HT _) HLk (subidx_range (ir_hold r2) (code_bits here) (code_op here) ltac:(lia) ltac:(lia))).
        unfold subix in Eh2. rewrite <- Eh2 in SC. destruct SC as (Sb & SNL & SN).
        assert (HQ2 : PPw w0 (mkW s c r2)) by exact (PPw_pulled w0 s c r1 r2 HQ1 HP2).
        aflat. arun2 DROPBITS_eq. aflat. arun2 add_back_ref. arun2 aret_eq. sacc.
        rewrite (wrap32_id (ir_bits r2 - code_bits here)) by lia.
        assert (SAME2 : ir_bits r2 = ir_bits r1 -> ir_hold r2 = ir_hold r1).
        { intros Eb. destruct HP2 as (k & _ & _ & _ & _ & Bk & Mk & Hk & _). rewrite <- Mk. symmetry. apply Z.mod_small. rewrite <- Eb. exact Hk. }
        assert (B8 : ir_bits r2 - code_bits here - code_bits here2 < 8).
        { destruct Hb2 as [Hb2|Hb2]; [|lia]. destruct Hb1 as [Hb1|Hb1]; [|lia].
          destruct Hbx as [Hbx|Hbx]; [lia|]. exfalso.
          rewrite (lneed_lneedg s) in Hbx. unfold lneedg in Hbx.
          rewrite <- (SAME Hb1), <- Eh, HLk in Hbx. rewrite (SAME2 Hb2) in Eh2. rewrite <- Eh2 in Hbx. lia. }
        apply dist_tail_psi;
          first [ assumption
                | core_keep HC; apply CORE_length; exact HC
                | apply REGS_holdbits; [exact HR2|]; apply HB_drop; [split; [exact RB2|exact RHO2]|lia]
                | common_keep HCm
                | tables_keep Htb
                | rewrite Eo2, Eo1; exact HWF
                | rewrite Ep2, Ep1; exact HWB
                | sacc; lia
                | eapply (PPw_trans _ _ _ HQ2); unfold PPw, PSI, PSIr; cbn [w_r w_s]; sacc; unfold PSIW; unfold pend; sacc; rewrite E; pend_red; lia ].
      * eapply PP_bind_leave; [exact EQ2|]. exact (PPw_pulled w0 s c r1 r2 HQ1 HP2).
    +
      assert (HLk : is_linkb here = false).
      { destruct (is_linkb here) eqn:Lk; [|reflexivity]. exfalso. destruct (RLk eq_refl) as (_ & Hop & _).
        rewrite (land240_small (code_op here)) in Clink by lia. discriminate Clink. }
      destruct (RNk HLk) as [Hbr SH].
      arun2 aret_eq.
      assert (B8 : ir_bits r1 - code_bits here < 8).
      { destruct Hb1 as [Hb1|Hb1]; [|lia]. destruct Hbx as [Hbx|Hbx]; [lia|]. exfalso.
        rewrite (lneed_lneedg s) in Hbx. unfold lneedg in Hbx.
        rewrite <- (SAME Hb1), <- Eh, HLk in Hbx. lia. }
      apply dist_tail_psi;
        first [ assumption
              | rewrite Eo1; exact HWF
              | rewrite Ep1; exact HWB
              | lia ].
  - eapply PP_bind_leave; [exact EQ|]. exact (PPw_pulled w0 s c r r1 HQ HP1).
Qed.


Lemma arm_LENEXT_psi : arm_psi LENEXT (arm_LENEXT ivar_ref).
Proof.
  intros w0 s c r HW E HQ. unfold arm_LENEXT. arun2 gs_eq.
  pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR.
  destruct HMF as (HCm & Hbx & Htb & HX & HL). pose proof (CORE_length s HC) as HL0.
  pose proof (pow2_pos (is_extra s) ltac:(lia)) as P0.
  acase2 Cx.
  - assert (Xnz : is_extra s <> 0) by (intros X; rewrite X in Cx; discriminate Cx).
    aflat.
    destruct (NEEDBITS_spec c (is_extra s) s r HR ltac:(lia)) as [(r1 & EQ & HR1 & HP1 & Hn1 & Hb1)|(r1 & EQ & HR1 & HP1 & Hb1 & Hh1)].
    + eapply PP_bind_run; [exact EQ|]. cbv beta iota.
      pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & El1 & _). pose proof (pulled_psi r r1 HP1) as PS1.
      pose proof HR1 as (_ & _ & _ & _ & _ & _ & [RB1 RHO1] & _).
      aflat. arun2 BITS_eq. aflat. arun2 us_eq. aflat. arun2 DROPBITS_eq. aflat. arun2 add_back_ref.
      aflat. arun2 aux_ref. arun2 set_mode_eq. sacc.
      rewrite (BITSv_mod (ir_hold r1) (is_extra s)) by lia.
      pose proof (mod_pow2_range (ir_hold r1) (is_extra s) ltac:(lia)) as MV.
      pose proof (pow2_le (is_extra s) 15 ltac:(lia)) as P15. change (2 ^ 15) with 32768 in P15.
      rewrite (wrap32_id (is_length s + _)) by lia.
      rewrite (wrap32_id (ir_bits r1 - is_extra s)) by lia.
      apply (PP_arm DIST (arm_DIST ivar_ref) _ _ _ _ arm_DIST_psi).
      * winv_split.
        -- core_keep HC. lia.
        -- apply REGS_holdbits; [exact HR1|]. apply HB_drop; [split; [exact RB1|exact RHO1]|lia].
        -- split; [common_keep HCm|]. split; [lia|]. split; [tables_keep Htb|]. lia.
        -- rewrite Eo1. exact HWF.
        -- rewrite Ep1. exact HWB.
      * reflexivity.
      * ppw E HQ.
    + eapply PP_bind_leave; [exact EQ|]. exact (PPw_pulled w0 s c r r1 HQ HP1).
  - apply Z.eqb_eq in Cx || (destruct (Z.eqb_spec (is_extra s) 0) as [Cx'|Cx']; [clear Cx; rename Cx' into Cx|discriminate Cx]).
    arun2 aret_eq. aflat. arun2 aux_ref. arun2 set_mode_eq.
    apply (PP_arm DIST (arm_DIST ivar_ref) _ _ _ _ arm_DIST_psi).
    + winv_split.
      * core_keep HC. exact HL0.
      * exact HR.
      * split; [common_keep HCm|]. split; [lia|]. split; [tables_keep Htb|]. lia.
      * exact HWF.
      * exact HWB.
    + reflexivity.
    + ppw_open E HQ. rewrite Cx. change (2 ^ 0) with 1. lia.
Qed.
