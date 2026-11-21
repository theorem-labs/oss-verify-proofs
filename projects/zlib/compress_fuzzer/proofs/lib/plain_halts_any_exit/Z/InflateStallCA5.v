(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg ZIface InflateState Inftrees InflateFast InflateArms Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InftreesCoverage AdlerModel RefInflateSafeD RefInflateSafeT RefInflateSafeH RefInflateSafeK RefInflateSafeA1 RefInflateSafeA3.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateStall InflateStallC InflateStallCA1 InflateStallCA3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section LenSlow.

  Lemma len_tail_sq : forall s c r here,
    CORE s -> REGS c r -> is_mode s = LEN -> common s -> tables s ->
    ir_out r = arr_len (ic_outbuf c) -> (is_wbits s = 0 -> ir_put r = 0) ->
    1 <= code_bits here <= ir_bits r -> ir_bits r - code_bits here < 8 ->
    ((exists sy, 0 <= sy < nsyms LENS /\ code_op here = fst (sym_entry LENS sy) /\ code_val here = snd (sym_entry LENS sy)) \/ code_op here = 64) ->
    SQ ((DROPBITS (code_bits here) ;; add_back ivar_ref (code_bits here) ;;
         us (fun s0 => iset_length s0 (code_val here)) ;;
         if code_op here =? 0 then set_mode LIT
         else if negb (Z.land (code_op here) 32 =? 0) then set_back ivar_ref (-1) ;; set_mode TYPE
         else if negb (Z.land (code_op here) 64 =? 0) then go_bad MSG_invalid_literal_length_code
         else us (fun s0 => iset_extra s0 (Z.land (code_op here) 15)) ;; set_mode LENEXT ;; arm_LENEXT ivar_ref)%am
        (mkW s c r)).
  Proof.
    intros s c r here HC HR E HCm Htb HWF HWB Hcb Hb8 Hsh.
    regs_open HR. pose proof (CORE_length s HC) as HL0.
    pose proof (code_val_nonneg here) as HV0.
    assert (HV16 : code_val here < 65536) by (unfold code_val; pose proof (land_65535 (Z.shiftr here 16)); lia).
    aflat. arun3 DROPBITS_eq. aflat. arun3 add_back_ref. aflat. arun3 us_eq. rewrite (wrap32_id (ir_bits r - code_bits here)) by lia.
    set (r1 := irset_bits (irset_hold r (Z.shiftr (ir_hold r) (code_bits here))) (ir_bits r - code_bits here)).
    assert (HRd : REGS c r1).
    { subst r1. apply REGS_holdbits; [exact HR|]. apply HB_drop; [split; [exact RB|exact RHO]|lia]. }
    set (s1 := iset_length (iset_back s (swrap32 (is_back s + code_bits here))) (code_val here)).
    assert (HC1 : CORE s1) by (subst s1; core_keep HC; lia).
    assert (BADc : SQ ((go_bad MSG_invalid_literal_length_code) (mkW s1 c r1))).
    { unfold go_bad. arun3 set_msg_eq. rewrite set_mode_eq. exact I. }
    assert (TYPEc : SQ ((set_back ivar_ref (-1) ;; set_mode TYPE)%am (mkW s1 c r1))).
    { arun3 set_back_ref. rewrite set_mode_eq. exact I. }
    destruct Hsh as [[sy (Hsy & Hop & Hv)]|Hop].
    2:{ rewrite Hop. cbn [Z.land Z.eqb negb]. exact BADc. }
    cbn [nsyms] in Hsy. pose proof (lens_sym_cases sy Hsy) as L.
    destruct (sym_entry LENS sy) as [op v] eqn:Es. cbn [fst snd] in Hop, Hv. rewrite Hop. rewrite Hv in *.
    destruct L as [[L1 L2]|[[L1 L2]|[(L1 & L2 & L3)|[L1|L1]]]].
    -
      rewrite L1. cbn [Z.eqb]. rewrite set_mode_eq. exact I.
    -
      rewrite L1. cbn [Z.land Z.eqb negb]. exact TYPEc.
    -
      destruct (len_op_facts op L1) as (F1 & F2 & F3 & F4 & F5).
      replace (op =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      rewrite F5, F2, F3. cbn [Z.eqb negb].
      pose proof (pow2_pos (op - 16) ltac:(lia)) as P0.
      aflat. arun3 us_eq. arun3 set_mode_eq.
      apply arm_LENEXT_sqW; [|reflexivity].
      winv_split.
      + core_keep HC1. subst s1. sacc. lia.
      + exact HRd.
      + split; [common_keep HCm|]. split; [left; subst r1; sacc; exact Hb8|]. split; [tables_keep Htb|]. subst s1. sacc. lia.
      + subst r1. sacc. exact HWF.
      + subst r1. sacc. exact HWB.
    - rewrite L1. cbn [Z.land Z.eqb negb]. exact BADc.
    - rewrite L1. cbn [Z.land Z.eqb negb]. exact BADc.
  Qed.

  Lemma len_slow_sq : forall s c r,
    CORE s -> REGS c r -> is_mode s = LEN -> common s ->
    (ir_bits r < 8 \/ ir_bits r < lneed s (is_lencode s) (is_lenbits s) (ir_hold r)) -> tables s ->
    ir_out r = arr_len (ic_outbuf c) -> (is_wbits s = 0 -> ir_put r = 0) ->
    SQ ((do s0 <- gs (fun s0 => s0) ;
         do here <- DECODE1 (is_lencode s0) (is_lenbits s0) ;
         do here <- (if negb (code_op here =? 0) && (Z.land (code_op here) 240 =? 0) then
                       let last := here in
                       do here <- DECODE2 (is_lencode s0) last ;
                       DROPBITS (code_bits last) ;;
                       add_back ivar_ref (code_bits last) ;;
                       aret here
                     else aret here) ;
         DROPBITS (code_bits here) ;;
         add_back ivar_ref (code_bits here) ;;
         us (fun s1 => iset_length s1 (code_val here)) ;;
         if code_op here =? 0 then set_mode LIT
         else if negb (Z.land (code_op here) 32 =? 0) then set_back ivar_ref (-1) ;; set_mode TYPE
         else if negb (Z.land (code_op here) 64 =? 0) then go_bad MSG_invalid_literal_length_code
         else
           us (fun s1 => iset_extra s1 (Z.land (code_op here) 15)) ;;
           set_mode LENEXT ;; arm_LENEXT ivar_ref)%am (mkW s c r)).
  Proof.
    intros s c r HC HR E HCm Hbx Htb HWF HWB. arun3 gs_eq. regs_open HR.
    destruct (cpok_TBLg LENS s (is_lencode s) (is_lenbits s) (proj1 Htb)) as (used & HT & _).
    pose proof (T_root _ _ _ _ HT) as HR15.
    aflat.
    destruct (DECODE1_spec c s (is_lencode s) LENS (is_lenbits s) used HT r HR)
      as [(r1 & here & EQ & HR1 & HP1 & Eh & Hle & Hb1)|(r1 & EQ & HR1 & HP1 & Hh1 & Hb1)].
    - eapply SQ_bind_run; [exact EQ|]. cbv beta iota.
      pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & El1 & _).
      pose proof HR1 as (_ & _ & _ & _ & _ & _ & [RB1 RHO1] & _).
      destruct (root_cell LENS _ _ used HT (ir_hold r1 mod 2 ^ is_lenbits s) (ridx_range _ _ _ _ HT _)) as (Hbits & RLk & RNk).
      rewrite <- Eh in Hbits, RLk, RNk.
      assert (SAME : ir_bits r1 = ir_bits r -> ir_hold r1 = ir_hold r).
      { intros Eb. destruct HP1 as (k & _ & _ & _ & _ & Bk & Mk & Hk & _). rewrite <- Mk. symmetry. apply Z.mod_small. rewrite <- Eb. exact Hk. }
      aflat. acase3 Clink.
      +
        apply andb_prop in Clink as [Cnz Clink]. apply Z.eqb_eq in Clink. apply Bool.negb_true_iff in Cnz. apply Z.eqb_neq in Cnz.
        assert (HLk : is_linkb here = true).
        { destruct (is_linkb here) eqn:Lk; [reflexivity|]. exfalso. destruct (RNk eq_refl) as [_ SH].
          exact (notlink_land240 LENS here SH ltac:(discriminate) Cnz Clink). }
        destruct (RLk HLk) as (Hbr & Hop & Hv1 & Hv2).
        aflat.
        destruct (DECODE2_spec c s (is_lencode s) LENS (is_lenbits s) used HT r1 here HR1 Eh HLk Hle)
          as [(r2 & here2 & EQ2 & HR2 & HP2 & Eh2 & Hsb & Hle2 & Hb2)|(r2 & EQ2 & HR2 & HP2 & Hh2 & Hb2)].
        * eapply SQ_bind_run; [exact EQ2|]. cbv beta iota.
          pose proof (pulled_out r1 r2 HP2) as (Eo2 & Ep2 & El2 & _).
          pose proof HR2 as (_ & _ & _ & _ & _ & _ & [RB2 RHO2] & _).
          pose proof (sub_cell LENS _ _ used HT (ir_hold r1 mod 2 ^ is_lenbits s)
                        (ir_hold r2 mod 2 ^ (code_bits here + code_op here) / 2 ^ code_bits here)) as SC2.
          rewrite <- Eh in SC2.
          specialize (SC2 (ridx_range _ _ _ _ HT _) HLk (subidx_range (ir_hold r2) (code_bits here) (code_op here) ltac:(lia) ltac:(lia))).
          unfold subix in Eh2. rewrite <- Eh2 in SC2. destruct SC2 as (Sb & SNL & SN).
          aflat. arun3 DROPBITS_eq. aflat. arun3 add_back_ref. arun3 aret_eq. sacc.
          rewrite (wrap32_id (ir_bits r2 - code_bits here)) by lia.
          assert (SAME2 : ir_bits r2 = ir_bits r1 -> ir_hold r2 = ir_hold r1).
          { intros Eb. destruct HP2 as (k & _ & _ & _ & _ & Bk & Mk & Hk & _). rewrite <- Mk. symmetry. apply Z.mod_small. rewrite <- Eb. exact Hk. }
          assert (B8 : ir_bits r2 - code_bits here - code_bits here2 < 8).
          { destruct Hb2 as [Hb2|Hb2]; [|lia]. destruct Hb1 as [Hb1|Hb1]; [|lia].
            destruct Hbx as [Hbx|Hbx]; [lia|]. exfalso.
            rewrite (lneed_lneedg s) in Hbx. unfold lneedg in Hbx.
            rewrite <- (SAME Hb1), <- Eh, HLk in Hbx. rewrite (SAME2 Hb2) in Eh2. rewrite <- Eh2 in Hbx. lia. }
          apply len_tail_sq;
            first [ assumption
                  | core_keep HC; apply CORE_length; exact HC
                  | apply REGS_holdbits; [exact HR2|]; apply HB_drop; [split; [exact RB2|exact RHO2]|lia]
                  | common_keep HCm
                  | tables_keep Htb
                  | rewrite Eo2, Eo1; exact HWF
                  | rewrite Ep2, Ep1; exact HWB
                  | sacc; lia ].
        * eapply SQ_bind_leave; [exact EQ2|]. apply LV_stall; [exact Hh2|]. unfold SC. rewrite E. sc_red.
          rewrite lneed_lneedg. exact Hb2.
      +
        assert (HLk : is_linkb here = false).
        { destruct (is_linkb here) eqn:Lk; [|reflexivity]. exfalso. destruct (RLk eq_refl) as (_ & Hop & _).
          rewrite (land240_small (code_op here)) in Clink by lia.
          replace (code_op here =? 0) with false in Clink by (symmetry; apply Z.eqb_neq; lia). discriminate Clink. }
        destruct (RNk HLk) as [Hbr SH].
        arun3 aret_eq.
        assert (B8 : ir_bits r1 - code_bits here < 8).
        { destruct Hb1 as [Hb1|Hb1]; [|lia]. destruct Hbx as [Hbx|Hbx]; [lia|]. exfalso.
          rewrite (lneed_lneedg s) in Hbx. unfold lneedg in Hbx.
          rewrite <- (SAME Hb1), <- Eh, HLk in Hbx. lia. }
        apply len_tail_sq;
          first [ assumption
                | rewrite Eo1; exact HWF
                | rewrite Ep1; exact HWB
                | lia ].
    - eapply SQ_bind_leave; [exact EQ|]. apply LV_stall; [exact Hh1|]. unfold SC. rewrite E. sc_red. rewrite lneed_lneedg.
      pose proof (lneedg_range LENS _ _ used HT (ir_hold r1)) as [_ LR]. lia.
  Qed.

  Lemma arm_LEN_sqW : forall s c r, WINV (mkW s c r) -> is_mode s = LEN -> SQ (arm_LEN ivar_ref (mkW s c r)).
  Proof.
    intros s c r HW E. unfold arm_LEN. arun3 gr_eq.
    pose proof HW as HW0. winv_open2 HW E HC HR. destruct HMF as (HCm & Hbx & Htb).
    acase3 Cfast.
    -
      apply SQ_bind_any; [rewrite amodify_eq; exact I|].
      intros u w'. destruct w' as [s' c' r']. arun3 gs_eq.
      destruct (is_mode s' =? TYPE); [rewrite set_back_ref|rewrite aret_eq]; exact I.
    - aflat. arun3 set_back_ref.
      apply len_slow_sq; first [ assumption
                               | core_keep HC; apply CORE_length; exact HC
                               | common_keep HCm
                               | rewrite (lneed_keep s (iset_back s 0)) by reflexivity; exact Hbx
                               | tables_keep Htb ].
  Qed.

  Lemma arm_LEN_sq : arm_sq LEN (arm_LEN ivar_ref).
  Proof. intros s c r HW _ E. exact (arm_LEN_sqW s c r HW E). Qed.

  Lemma arm_LEN__sqW : forall s c r, WINV (mkW s c r) -> is_mode s = LEN_ -> SQ (arm_LEN_ ivar_ref (mkW s c r)).
  Proof.
    intros s c r HW E. unfold arm_LEN_. arun3 set_mode_eq.
    winv_open2 HW E HC HR. destruct HMF as (HCm & Hb8 & Htb).
    apply arm_LEN_sqW; [|reflexivity].
    winv_split.
    - core_keep HC. apply CORE_length; exact HC.
    - exact HR.
    - split; [common_keep HCm|]. split; [left; exact Hb8|tables_keep Htb].
    - exact HWF.
    - exact HWB.
  Qed.

  Lemma arm_LEN__sq : arm_sq LEN_ (arm_LEN_ ivar_ref).
  Proof. intros s c r HW _ E. exact (arm_LEN__sqW s c r HW E). Qed.
End LenSlow.
