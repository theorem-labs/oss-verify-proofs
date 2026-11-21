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
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeD.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeT.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeH.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeK.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeA1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section StoredArms.
  Variable iv : ivariant.
Variable flush : Z.

  Lemma arm_COPY_safe : arm_safe COPY arm_COPY.
  Proof.
    intros w0 s c r HW E HP. unfold arm_COPY. arun gs_eq. cbv zeta.
    pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR. destruct HMF as [HCm Hb8]. pose proof (CORE_length s HC) as HL0.
    acase Clen.
    - arun gr_eq. cbv zeta.
      match goal with |- POST _ ((if ?x =? 0 then _ else _) _) => set (cp := x) in * end.
      assert (Hcp : 0 <= cp /\ cp <= ir_have r /\ cp <= ir_left r /\ cp <= is_length s).
      { subst cp. destruct (Z.ltb_spec (ir_have r) (is_length s));
          [destruct (Z.ltb_spec (ir_left r) (ir_have r)) | destruct (Z.ltb_spec (ir_left r) (is_length s))]; lia. }
      acase Ccp.
      + aleave. exact HW0.
      + apply Z.eqb_neq in Ccp.
        aflat. arun uc_eq. aflat. arun ur_eq. rewrite us_eq. apply POST_ARun.
        * winv_split.
          -- core_keep HC. apply wrap32_range.
          -- apply REGS_copy; [exact HR | apply arr_len_blit | lia | lia | lia].
          -- rewrite E. mred. split; [common_keep HCm | exact Hb8].
          -- rewrite E. mred. rewrite arr_len_blit. exact HWF.
          -- intros W. exfalso. exact (proj1 HCm W).
        * phi_norm E HP. rewrite !wrap32_id by lia. lia.
    - rewrite set_mode_eq. apply POST_ARun.
      + winv_split.
        * core_keep HC. exact HL0.
        * exact HR.
        * split; [common_keep HCm | exact Hb8].
        * exact HWF.
        * exact HWB.
      + phi_norm E HP. lia.
  Qed.

  Lemma arm_COPY__safe : arm_safe COPY_ arm_COPY_.
  Proof.
    intros w0 s c r HW E HP. unfold arm_COPY_. arun set_mode_eq.
    winv_open2 HW E HC HR. destruct HMF as [HCm Hb8].
    apply (POST_arm COPY arm_COPY _ _ _ _ arm_COPY_safe).
    - winv_split.
      + core_keep HC. apply CORE_length; exact HC.
      + exact HR.
      + split; [common_keep HCm | exact Hb8].
      + exact HWF.
      + exact HWB.
    - reflexivity.
    - phi_norm E HP. lia.
  Qed.

  Lemma arm_STORED_safe : arm_safe STORED (arm_STORED iv flush).
  Proof.
    intros w0 s c r HW E HP. unfold arm_STORED.
    pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR.
    arun BYTEBITS_eq.
    pose proof (land7_mod (ir_bits r) ltac:(lia)) as L7.
    assert (Hm8 : 0 <= ir_bits r mod 8 <= ir_bits r) by (split; [apply Z.mod_pos_bound; lia|apply Z.mod_le; lia]).
    set (rb := irset_bits (irset_hold r (Z.shiftr (ir_hold r) (Z.land (ir_bits r) 7))) (wrap32 (ir_bits r - Z.land (ir_bits r) 7))).
    assert (HRb : REGS c rb) by (subst rb; apply REGS_drop; [exact HR|lia]).
    assert (Ebb : ir_bits rb = ir_bits r - ir_bits r mod 8) by (subst rb; sacc; rewrite L7; apply wrap32_id; lia).
    assert (Eob : ir_out rb = ir_out r /\ ir_put rb = ir_put r /\ ir_left rb = ir_left r /\ ir_have rb = ir_have r) by (subst rb; sacc; repeat split; reflexivity).
    destruct Eob as (Eob & Epb & Elb & Ehb).
    destruct (NEEDBITS_spec c 32 s rb HRb ltac:(lia)) as [(r1 & EQ & HR1 & HP1 & Hn1 & Hb1)|(r1 & EQ & HR1 & HP1 & Hb1 & Hh1)].
    - eapply POST_bind_run; [exact EQ|]. cbv beta.
      pose proof (pulled_out rb r1 HP1) as (Eo1 & Ep1 & El1 & _). pose proof (pulled_phi rb r1 HP1) as PH1.
      rewrite Eob in Eo1. rewrite Epb in Ep1. rewrite Elb in El1. rewrite Elb, Ehb, Ebb in PH1.
      pose proof HR1 as (_ & _ & _ & _ & _ & _ & [RB1 RHO1] & _).
      arun HOLD_eq. acase Cbad.
      + arun set_msg_eq. rewrite set_mode_eq. apply POST_ARun.
        * winv_split.
          -- core_keep HC. apply CORE_length; exact HC.
          -- eapply REGS_cview; [exact HR1 | reflexivity | reflexivity].
          -- exact (proj2 HMF).
          -- exact I.
          -- rewrite Ep1. exact HWB.
        * phi_norm E HP. lia.
      + aflat. arun us_eq. aflat. arun INITBITS_eq. aflat. arun set_mode_eq.
        match goal with |- POST _ (_ ?w) => assert (HW2 : WINV w) end.
        { winv_split.
          - core_keep HC. pose proof (land_65535 (wrap32 (ir_hold r1))). lia.
          - apply REGS_init. exact HR1.
          - split; [common_keep HMF|]. lia.
          - rewrite Eo1. exact HWF.
          - rewrite Ep1. exact HWB. }
        acase Cz.
        * aleave. exact HW2.
        * match goal with |- POST _ (_ (mkW ?s2 ?c2 ?r2)) => apply (POST_arm COPY_ arm_COPY_ w0 s2 c2 r2 arm_COPY__safe HW2) end.
          -- reflexivity.
          -- phi_norm E HP. lia.
    - eapply POST_bind_leave; [exact EQ|].
      pose proof (pulled_out rb r1 HP1) as (Eo1 & Ep1 & _). rewrite Eob in Eo1. rewrite Epb in Ep1.
      apply (WINV_regs s c r r1 HW0 HR1 Eo1 Ep1). rewrite E. intros X; exact X.
  Qed.
End StoredArms.

Section DictArms.
  Variable iv : ivariant.
Variable flush : Z.

  Lemma arm_DICT_safe : arm_safe DICT (arm_DICT iv flush).
  Proof.
    intros w0 s c r HW E HP. unfold arm_DICT. arun gs_eq.
    winv_open2 HW E HC HR. destruct HMF as [HWb Hb8].
    acase Chd.
    - (* zlib 1.4: total_in += in - avail_in after RESTORE, before Z_NEED_DICT *)
      arun amodify_eq. arun gr_eq. arun uc_eq. aleave. unfold RESTORE. cbn [w_s w_c w_r]. split.
      + winv_split.
        * core_keep HC. apply CORE_length; exact HC.
        * eapply REGS_cview; [exact HR | reflexivity | reflexivity].
        * rewrite E. mred. split; [exact HWb | exact Hb8].
        * rewrite E. mred. exact HWF.
        * exact HWB.
      + unfold INV. sacc. rewrite E. mred. split; [core_keep HC; apply CORE_length; exact HC|].
        split; [|split; [exact HWb | exact Hb8]]. destruct HR as (_ & _ & _ & _ & _ & _ & HBr & _). exact HBr.
    - aflat. arun set_adler_check_eq. arun set_mode_eq.
      apply (POST_arm TYPE (arm_TYPE iv flush) _ _ _ _ (arm_TYPE_safe iv flush)).
      + winv_split.
        * core_keep HC. apply CORE_length; exact HC.
        * eapply REGS_cview; [exact HR | reflexivity | reflexivity].
        * split; [|exact Hb8]. split; [exact HWb|]. intros _. exact adler_canon_1.
        * exact HWF.
        * exact HWB.
      + reflexivity.
      + phi_norm E HP. lia.
  Qed.

  Lemma arm_DICTID_safe : arm_safe DICTID (arm_DICTID iv flush).
  Proof.
    intros w0 s c r HW E HP. unfold arm_DICTID.
    pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR.
    destruct (NEEDBITS_spec c 32 s r HR ltac:(lia)) as [(r1 & EQ & HR1 & HP1 & Hn1 & Hb1)|(r1 & EQ & HR1 & HP1 & Hb1 & Hh1)].
    - eapply POST_bind_run; [exact EQ|]. cbv beta.
      pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & El1 & _). pose proof (pulled_phi r r1 HP1) as PH1.
      pose proof HR1 as (_ & _ & _ & _ & _ & _ & [RB1 RHO1] & _).
      arun HOLD_eq. aflat. arun set_adler_check_eq. aflat. arun INITBITS_eq. aflat. arun set_mode_eq.
      apply (POST_arm DICT (arm_DICT iv flush) _ _ _ _ arm_DICT_safe).
      + winv_split.
        * core_keep HC. apply CORE_length; exact HC.
        * eapply REGS_cview; [apply REGS_init; exact HR1 | reflexivity | reflexivity].
        * split; [exact (proj1 HMF) | lia].
        * rewrite Eo1. exact HWF.
        * rewrite Ep1. exact HWB.
      + reflexivity.
      + phi_norm E HP. lia.
    - eapply POST_bind_leave; [exact EQ|].
      pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & _).
      apply (WINV_regs s c r r1 HW0 HR1 Eo1 Ep1). rewrite E. intros X; exact X.
  Qed.
End DictArms.
