(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface InflateState Inftrees InflateFast InflateArms Inflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InftreesCoverage AdlerModel RefInflateSafeD RefInflateSafeT RefInflateSafeH RefInflateSafeK RefInflateSafeA1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflatePsi InflatePsi1 InflatePsiA1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section StoredArms.
  Variable iv : ivariant.
  Variable flush : Z.

  Lemma arm_COPY_psi : arm_psi COPY arm_COPY.
  Proof.
    intros w0 s c r HW E HQ. unfold arm_COPY. arun2 gs_eq. cbv zeta.
    pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR. destruct HMF as [HCm Hb8]. pose proof (CORE_length s HC) as HL0.
    acase2 Clen.
    - arun2 gr_eq. cbv zeta.
      match goal with |- PP _ ((if ?x =? 0 then _ else _) _) => set (cp := x) in * end.
      assert (Hcp : 0 <= cp /\ cp <= ir_have r /\ cp <= ir_left r /\ cp <= is_length s).
      { subst cp. destruct (Z.ltb_spec (ir_have r) (is_length s));
          [destruct (Z.ltb_spec (ir_left r) (ir_have r)) | destruct (Z.ltb_spec (ir_left r) (is_length s))]; lia. }
      acase2 Ccp.
      + aleave2. exact HQ.
      + apply Z.eqb_neq in Ccp.
        aflat. arun2 uc_eq. aflat. arun2 ur_eq. rewrite us_eq. apply PP_ARun.
        ppw_open E HQ. rewrite !wrap32_id by lia. lia.
    - rewrite set_mode_eq. apply PP_ARun. ppw E HQ.
  Qed.

  Lemma arm_COPY__psi : arm_psi COPY_ arm_COPY_.
  Proof.
    intros w0 s c r HW E HQ. unfold arm_COPY_. arun2 set_mode_eq.
    winv_open2 HW E HC HR. destruct HMF as [HCm Hb8].
    apply (PP_arm COPY arm_COPY _ _ _ _ arm_COPY_psi).
    - winv_split.
      + core_keep HC. apply CORE_length; exact HC.
      + exact HR.
      + split; [common_keep HCm | exact Hb8].
      + exact HWF.
      + exact HWB.
    - reflexivity.
    - ppw E HQ.
  Qed.

  Lemma arm_STORED_psi : arm_psi STORED (arm_STORED iv flush).
  Proof.
    intros w0 s c r HW E HQ. unfold arm_STORED.
    pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR.
    arun2 BYTEBITS_eq.
    pose proof (land7_mod (ir_bits r) ltac:(lia)) as L7.
    assert (Hm8 : 0 <= ir_bits r mod 8 <= ir_bits r) by (split; [apply Z.mod_pos_bound; lia|apply Z.mod_le; lia]).
    set (rb := irset_bits (irset_hold r (Z.shiftr (ir_hold r) (Z.land (ir_bits r) 7))) (wrap32 (ir_bits r - Z.land (ir_bits r) 7))).
    assert (HRb : REGS c rb) by (subst rb; apply REGS_drop; [exact HR|lia]).
    assert (Ebb : ir_bits rb = ir_bits r - ir_bits r mod 8) by (subst rb; sacc; rewrite L7; apply wrap32_id; lia).
    assert (Eob : ir_out rb = ir_out r /\ ir_put rb = ir_put r /\ ir_left rb = ir_left r /\ ir_have rb = ir_have r) by (subst rb; sacc; repeat split; reflexivity).
    destruct Eob as (Eob & Epb & Elb & Ehb).
    assert (HQb : PPw w0 (mkW s c rb)).
    { eapply (PPw_trans _ _ _ HQ). unfold PPw, PSI, PSIr. cbn [w_r w_s]. rewrite Epb, Ehb, Ebb. unfold PSIW. lia. }
    destruct (NEEDBITS_spec c 32 s rb HRb ltac:(lia)) as [(r1 & EQ & HR1 & HP1 & Hn1 & Hb1)|(r1 & EQ & HR1 & HP1 & Hb1 & Hh1)].
    - eapply PP_bind_run; [exact EQ|]. cbv beta.
      pose proof (pulled_out rb r1 HP1) as (Eo1 & Ep1 & El1 & _). pose proof (pulled_psi rb r1 HP1) as PS1.
      rewrite Eob in Eo1. rewrite Epb in Ep1. rewrite Elb in El1. rewrite Elb, Ehb, Ebb, Epb in PS1.
      pose proof HR1 as (_ & _ & _ & _ & _ & _ & [RB1 RHO1] & _).
      arun2 HOLD_eq. acase2 Cbad.
      + arun2 set_msg_eq. rewrite set_mode_eq. apply PP_ARun. ppw E HQ.
      + aflat. arun2 us_eq. aflat. arun2 INITBITS_eq. aflat. arun2 set_mode_eq.
        match goal with |- PP _ (_ ?w) => assert (HW2 : WINV w) end.
        { winv_split.
          - core_keep HC. pose proof (land_65535 (wrap32 (ir_hold r1))). lia.
          - apply REGS_init. exact HR1.
          - split; [common_keep HMF|]. lia.
          - rewrite Eo1. exact HWF.
          - rewrite Ep1. exact HWB. }
        match goal with |- PP _ (_ ?w) => assert (HQ2 : PPw w0 w) end.
        { ppw E HQ. }
        acase2 Cz.
        * aleave2. exact HQ2.
        * match goal with |- PP _ (_ (mkW ?s2 ?c2 ?r2)) => apply (PP_arm COPY_ arm_COPY_ w0 s2 c2 r2 arm_COPY__psi HW2) end.
          -- reflexivity.
          -- exact HQ2.
    - eapply PP_bind_leave; [exact EQ|]. exact (PPw_pulled w0 s c rb r1 HQb HP1).
  Qed.
End StoredArms.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section DictArms.
  Variable iv : ivariant.
  Variable flush : Z.

  Lemma arm_DICT_psi : arm_psi DICT (arm_DICT iv flush).
  Proof.
    intros w0 s c r HW E HQ. unfold arm_DICT. arun2 gs_eq.
    winv_open2 HW E HC HR. destruct HMF as [HWb Hb8].
    acase2 Chd.
    - (* zlib 1.4 (zl14infl-r2): total_in += in - avail_in after RESTORE, before Z_NEED_DICT *)
      arun2 amodify_eq. arun2 gr_eq. arun2 uc_eq. aleave2. exact I.
    - aflat. arun2 set_adler_check_eq. arun2 set_mode_eq.
      apply (PP_arm TYPE (arm_TYPE iv flush) _ _ _ _ (arm_TYPE_psi iv flush)).
      + winv_split.
        * core_keep HC. apply CORE_length; exact HC.
        * eapply REGS_cview; [exact HR | reflexivity | reflexivity].
        * split; [|exact Hb8]. split; [exact HWb|]. intros _. exact adler_canon_1.
        * exact HWF.
        * exact HWB.
      + reflexivity.
      + ppw E HQ.
  Qed.

  Lemma arm_DICTID_psi : arm_psi DICTID (arm_DICTID iv flush).
  Proof.
    intros w0 s c r HW E HQ. unfold arm_DICTID.
    pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR.
    destruct (NEEDBITS_spec c 32 s r HR ltac:(lia)) as [(r1 & EQ & HR1 & HP1 & Hn1 & Hb1)|(r1 & EQ & HR1 & HP1 & Hb1 & Hh1)].
    - eapply PP_bind_run; [exact EQ|]. cbv beta.
      pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & El1 & _). pose proof (pulled_psi r r1 HP1) as PS1.
      pose proof HR1 as (_ & _ & _ & _ & _ & _ & [RB1 RHO1] & _).
      arun2 HOLD_eq. aflat. arun2 set_adler_check_eq. aflat. arun2 INITBITS_eq. aflat. arun2 set_mode_eq.
      apply (PP_arm DICT (arm_DICT iv flush) _ _ _ _ arm_DICT_psi).
      + winv_split.
        * core_keep HC. apply CORE_length; exact HC.
        * eapply REGS_cview; [apply REGS_init; exact HR1 | reflexivity | reflexivity].
        * split; [exact (proj1 HMF) | lia].
        * rewrite Eo1. exact HWF.
        * rewrite Ep1. exact HWB.
      + reflexivity.
      + ppw E HQ.
    - eapply PP_bind_leave; [exact EQ|]. exact (PPw_pulled w0 s c r r1 HQ HP1).
  Qed.
End DictArms.
