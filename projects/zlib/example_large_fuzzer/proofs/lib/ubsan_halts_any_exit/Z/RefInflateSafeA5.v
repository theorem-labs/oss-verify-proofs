(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateArms.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InftreesCoverage.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItProof.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItTable.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeD.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeT.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeH.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeK.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeA1.
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


Lemma decoded_entry_stable : forall ty get root used h1 b1 h' here,
  TBLg ty get root used -> here = get (h1 mod 2 ^ root) -> code_bits here <= b1 -> 0 <= b1 ->
  0 <= h1 < 2 ^ b1 -> h' mod 2 ^ b1 = h1 -> get (h' mod 2 ^ root) = here.
Proof.
  intros ty get root used h1 b1 h' here HT Eh Hcb Hb1 Hh1 Hm.
  pose proof (T_root _ _ _ _ HT) as HR.
  assert (Hm' : h' mod 2 ^ b1 = h1 mod 2 ^ b1) by (rewrite Hm; symmetry; apply Z.mod_small; lia).
  destruct (Z.lt_ge_cases b1 root) as [LT|GE].
  - rewrite Eh. symmetry. symmetry. rewrite <- (rep_root_apply ty get root used HT h' h1 b1 ltac:(lia) ltac:(symmetry; exact Hm') ltac:(rewrite <- Eh; exact Hcb)). reflexivity.
  - rewrite (same_root_idx ty get root used HT h1 h' b1 GE Hm'). symmetry. exact Eh.
Qed.


Lemma cl_ext_lt16 : forall v, v < 16 -> cl_ext v = 0.
Proof. intros v H. unfold cl_ext. replace (v <? 16) with true by (symmetry; apply Z.ltb_lt; exact H). reflexivity. Qed.

Lemma cl_ext_ge18 : forall v, 18 <= v -> cl_ext v = 7.
Proof.
  intros v H. unfold cl_ext. replace (v <? 16) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (v =? 16) with false by (symmetry; apply Z.eqb_neq; lia). replace (v =? 17) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.

Lemma TBLg_ext : forall ty get get' root used,
  (forall x, 0 <= x < used -> get' x = get x) -> TBLg ty get root used -> TBLg ty get' root used.
Proof.
  intros ty get get' root used E HT. pose proof HT as (R1 & R2 & SH & RRt & RSb).
  pose proof (pow2_pos root ltac:(lia)) as PR.
  split; [exact R1|]. split; [exact R2|]. split; [|split].
  - intros x Hx. rewrite E by exact Hx. exact (SH x Hx).
  - intros x x' Hx Hx' Hb Hm. rewrite !E in * by lia. exact (RRt x x' Hx Hx' Hb Hm).
  - intros x Hx Hop y y' Hy Hy' Hb Hm. rewrite (E x) in * by lia.
    destruct (root_cell ty get root used HT x Hx) as (_ & RL & _).
    destruct (RL ltac:(apply is_linkb_true; exact Hop)) as (_ & _ & Hv1 & Hv2).
    pose proof (pow2_pos (code_op (get x)) ltac:(lia)).
    rewrite !E in * by lia. exact (RSb x Hx Hop y y' Hy Hy' Hb Hm).
Qed.

Lemma lens_repeat_loop : forall m lens have len,
  0 <= have -> have + Z.of_nat m < 2 ^ 32 ->
  let '(lens', have', copy') :=
    loopZ (Z.of_nat m)
      (fun st : arr * Z * Z => let '(lens0, have0, copy0) := st in
         if negb (copy0 =? 0) then (true, (arr_set lens0 have0 (wrap16 len), wrap32 (have0 + 1), wrap32 (copy0 - 1)))
         else (false, (lens0, have0, copy0))) (lens, have, Z.of_nat m) in
  have' = have + Z.of_nat m /\ arr_len lens' = arr_len lens
  /\ (forall i, arr_get lens' i = if (have <=? i) && (i <? have + Z.of_nat m) && (i <? arr_len lens) then wrap16 len else arr_get lens i).
Proof.
  induction m as [|m IH]; intros lens have len Hh Hm.
  - change (Z.of_nat 0) with 0. rewrite loopZ_le0 by lia. split; [lia|]. split; [reflexivity|].
    intros i. destruct (Z.leb_spec have i), (Z.ltb_spec i (have + 0)), (Z.ltb_spec i (arr_len lens)); cbn [andb]; try reflexivity. all: exfalso; lia.
  - rewrite loopZ_step by lia. cbv beta iota zeta.
    replace (negb (Z.of_nat (S m) =? 0)) with true by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; lia). cbv iota.
    rewrite (wrap32_id (have + 1)) by lia. replace (wrap32 (Z.of_nat (S m) - 1)) with (Z.of_nat m) by (rewrite wrap32_id by lia; lia).
    replace (Z.of_nat (S m) - 1) with (Z.of_nat m) by lia.
    specialize (IH (arr_set lens have (wrap16 len)) (have + 1) len ltac:(lia) ltac:(lia)).
    destruct (loopZ (Z.of_nat m) _ _) as [[lens' have'] copy']. destruct IH as (A & B & C).
    split; [lia|]. split; [rewrite B; apply arr_len_set|].
    intros i. rewrite C. rewrite arr_len_set. rewrite arr_get_set. unfold arr_inb.
    destruct (Z.leb_spec (have + 1) i), (Z.ltb_spec i (have + 1 + Z.of_nat m)), (Z.leb_spec have i), (Z.ltb_spec i (have + Z.of_nat (S m))),
      (Z.eqb_spec have i), (Z.leb_spec 0 have), (Z.ltb_spec have (arr_len lens)), (Z.ltb_spec i (arr_len lens)); cbn [andb]; try reflexivity; try (exfalso; lia); subst; try reflexivity; try lia.
Qed.

Lemma lens_repeat_eq : forall copy len s c r, 0 <= copy -> 0 <= is_have s -> is_have s + copy < 2 ^ 32 ->
  exists lens', lens_repeat copy len (mkW s c r) = ARun tt (mkW (iset_have (iset_lens s lens') (is_have s + copy)) c r)
    /\ arr_len lens' = arr_len (is_lens s)
    /\ (forall i, arr_get lens' i = if (is_have s <=? i) && (i <? is_have s + copy) && (i <? arr_len (is_lens s)) then wrap16 len else arr_get (is_lens s) i).
Proof.
  intros copy len s c r Hc Hh Hm. unfold lens_repeat, us. cbn [w_s wset_s].
  pose proof (lens_repeat_loop (Z.to_nat copy) (is_lens s) (is_have s) len Hh ltac:(lia)) as L.
  rewrite Z2Nat.id in L by lia.
  destruct (loopZ copy _ _) as [[lens' have'] copy']. destruct L as (A & B & C).
  exists lens'. rewrite A. split; [reflexivity|]. split; [exact B|exact C].
Qed.


Definition CL (s : inflate_state) (c : icall) (r : iregs) : Prop :=
  CORE s /\ REGS c r /\ is_mode s = CODELENS /\ common s
  /\ (ir_bits r < 8 \/ ir_bits r < cneed s (ir_hold r))
  /\ 257 <= is_nlen s <= 286 /\ 1 <= is_ndist s <= 30 /\ 0 <= is_have s <= is_nlen s + is_ndist s
  /\ (forall i, 0 <= i < is_have s -> 0 <= arr_get (is_lens s) i <= 15)
  /\ cpok CODES (is_codes s) (is_lencode s) (is_lenbits s)
  /\ ir_out r = arr_len (ic_outbuf c) /\ (is_wbits s = 0 -> ir_put r = 0).

Lemma CL_WINV : forall s c r, CL s c r -> is_have s < is_nlen s + is_ndist s -> WINV (mkW s c r).
Proof.
  intros s c r (HC & HR & E & HCm & Hbx & Hnl & Hnd & Hh & HLs & HT & HWF & HWB) Hlt.
  unfold WINV. cbn [w_s w_c w_r]. rewrite E. mred.
  split; [exact HC|]. split; [exact HR|]. split; [|split; [exact HWF|exact HWB]].
  repeat (split; [first [assumption | lia]|]). exact HT.
Qed.

Definition PHIr (r : iregs) : Z := 64 * ir_have r + 8 * ir_bits r + 8 * ir_left r.

Ltac mrun lem := rewrite ?abind_assoc; unfold abind at 1; rewrite lem; cbv beta iota.

Section Codelens.
  Variable c : icall.

  Lemma codelens_body_spec : forall s r,
    CL s c r -> is_have s < is_nlen s + is_ndist s ->
    match codelens_body (mkW s c r) with
    | ARun true (mkW s' c' r') => c' = c /\ CL s' c' r' /\ is_have s < is_have s' /\ ir_bits r' < 8
        /\ is_nlen s' = is_nlen s /\ is_ndist s' = is_ndist s /\ PHIr r' + 8 <= PHIr r /\ ir_put r' = ir_put r
    | ARun false (mkW s' c' r') => is_mode s' = BAD /\ WINV (mkW s' c' r') /\ PHIr r' + 8 <= PHIr r /\ ir_put r' = ir_put r
        /\ ic_input c' = ic_input c /\ ic_outbuf c' = ic_outbuf c
    | ALeave w' => WINV w' /\ ir_put (w_r w') = ir_put r
    | ARet _ _ => False
    end.
  Proof.
    intros s r HCL Hlt. pose proof HCL as (HC & HR & E & HCm & Hbx & Hnl & Hnd & Hh & HLs & HT & HWF & HWB).
    regs_open HR. pose proof (CORE_length s HC) as HL0. pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CA1 & _).
    destruct (cpok_TBLg CODES s (is_lencode s) (is_lenbits s) HT) as (used & HTg & _).
    pose proof (T_root _ _ _ _ HTg) as HR15.
    unfold codelens_body. unfold abind at 1. rewrite gs_eq. cbn [w_s].
    destruct (DECODE1_spec c s (is_lencode s) CODES (is_lenbits s) used HTg r HR)
      as [(r1 & here & EQ & HR1 & HP1 & Eh & Hle & Hb1)|(r1 & EQ & HR1 & HP1 & Hh1 & Hb1)].
    2:{ unfold abind at 1. rewrite EQ. split.
        - pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & _).
          apply (WINV_regs s c r r1 (CL_WINV s c r HCL Hlt) HR1 Eo1 Ep1). rewrite E. mred.
          intros _. split; [exact HCm|]. split; [|repeat (split; [first [assumption | lia]|]); exact HT].
          right. rewrite cneed_cneedg. pose proof (cneedg_range CODES _ _ used HTg (ir_hold r1)) as [_ CR]. lia.
        - cbn [w_r]. destruct (pulled_out r r1 HP1) as (_ & Ep1 & _). exact Ep1. }
    unfold abind at 1. rewrite EQ.
    pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & El1 & _). pose proof (pulled_phi r r1 HP1) as PH1.
    pose proof HR1 as (RN1 & RH1 & RNH1 & RP1 & RL1 & RPL1 & [RB1 RHO1] & _).
    destruct (root_cell CODES _ _ used HTg (ir_hold r1 mod 2 ^ is_lenbits s) (ridx_range _ _ _ _ HTg _)) as (Hbits & RLk & RNk).
    rewrite <- Eh in Hbits, RLk, RNk.
    assert (SAME : ir_bits r1 = ir_bits r -> ir_hold r1 = ir_hold r).
    { intros Eb. destruct HP1 as (k & _ & _ & _ & _ & Bk & Mk & Hk & _). rewrite <- Mk. symmetry. apply Z.mod_small. rewrite <- Eb. exact Hk. }
    assert (DISC : ir_bits r1 = ir_bits r -> ir_bits r < 8 \/ ir_bits r < code_bits here + cl_ext (code_val here)).
    { intros Eb. destruct Hbx as [Hbx|Hbx]; [left; exact Hbx|right].
      rewrite cneed_cneedg in Hbx. unfold cneedg in Hbx. rewrite <- (SAME Eb), <- Eh in Hbx. exact Hbx. }
    cbv beta. destruct (Z.ltb_spec (code_val here) 16) as [V16|V16].
    -
      rewrite (cl_ext_lt16 _ V16) in DISC.
      unfold abind. rewrite DROPBITS_eq. rewrite gs_eq. cbn [w_s]. unfold set_lens. rewrite us_eq. rewrite us_eq. unfold aret. sacc.
      rewrite (wrap32_id (ir_bits r1 - code_bits here)) by lia. rewrite (wrap32_id (is_have s + 1)) by lia.
      rewrite (wrap16_id (code_val here)) by (pose proof (code_val_nonneg here); lia).
      pose proof (code_val_nonneg here) as V0.
      split; [reflexivity|]. split; [|split; [sacc; lia|split; [sacc|split; [reflexivity|split; [reflexivity|split; [unfold PHIr; sacc; lia|sacc; exact Ep1]]]]]].
      2:{ destruct Hb1 as [Hb1|Hb1]; [|lia]. destruct (DISC Hb1); lia. }
      unfold CL. sacc. split; [core_keep HC; exact HL0|].
      split; [apply REGS_holdbits; [exact HR1|]; apply HB_drop; [split; [exact RB1|exact RHO1]|lia]|].
      split; [exact E|]. split; [common_keep HCm|].
      split; [left; destruct Hb1 as [Hb1|Hb1]; [destruct (DISC Hb1); lia|lia]|].
      split; [exact Hnl|]. split; [exact Hnd|]. split; [lia|].
      split.
      { intros i Hi. rewrite arr_get_set. unfold arr_inb. rewrite CA1.
        destruct (Z.eqb_spec (is_have s) i); cbn [andb].
        - replace ((0 <=? is_have s) && (is_have s <? 320)) with true by (symmetry; rewrite Bool.andb_true_iff, Z.leb_le, Z.ltb_lt; lia). lia.
        - apply HLs. lia. }
      split; [exact HT|]. split; [rewrite Eo1; exact HWF|rewrite Ep1; exact HWB].
    -
      assert (GEN : forall e base (lenf : inflate_state -> Z) (chk : bool),
        cl_ext (code_val here) = e -> 1 <= e <= 7 -> 3 <= base -> base + 2 ^ e <= 139 ->
        (forall s0, is_have s0 = is_have s -> is_lens s0 = is_lens s -> (chk = true -> 1 <= is_have s) -> 0 <= lenf s0 <= 15) ->
        match (abind (NEEDBITS (code_bits here + e) ;; DROPBITS (code_bits here) ;;
                      do s0 <- gs (fun s0 => s0) ;
                      if chk && (is_have s0 =? 0) then go_bad MSG_invalid_bit_length_repeat ;; aret None
                      else do b <- BITS e ; DROPBITS e ;; aret (Some (lenf s0, base + b)))
                     (fun lc => match lc with
                                | None => aret false
                                | Some (len, copy) =>
                                    do s0 <- gs (fun s0 => s0) ;
                                    if is_nlen s0 + is_ndist s0 <? is_have s0 + copy
                                    then go_bad MSG_invalid_bit_length_repeat ;; aret false
                                    else lens_repeat copy len ;; aret true
                                end) (mkW s c r1))%am
        with
        | ARun true (mkW s' c' r') => c' = c /\ CL s' c' r' /\ is_have s < is_have s' /\ ir_bits r' < 8
            /\ is_nlen s' = is_nlen s /\ is_ndist s' = is_ndist s /\ PHIr r' + 8 <= PHIr r /\ ir_put r' = ir_put r
        | ARun false (mkW s' c' r') => is_mode s' = BAD /\ WINV (mkW s' c' r') /\ PHIr r' + 8 <= PHIr r /\ ir_put r' = ir_put r
            /\ ic_input c' = ic_input c /\ ic_outbuf c' = ic_outbuf c
        | ALeave w' => WINV w' /\ ir_put (w_r w') = ir_put r
        | ARet _ _ => False
        end).
      { intros e base lenf chk He HeR Hbase Hcap Hlenf.
        pose proof (pow2_pos e ltac:(lia)) as PE.
        rewrite abind_assoc. unfold abind at 1.
        destruct (NEEDBITS_spec c (code_bits here + e) s r1 HR1 ltac:(lia)) as [(r2 & EQ2 & HR2 & HP2 & Hn2 & Hb2)|(r2 & EQ2 & HR2 & HP2 & Hb2 & Hh2)].
        2:{ rewrite EQ2. pose proof (pulled_out r1 r2 HP2) as (Eo2 & Ep2 & _). split; [|cbn [w_r]; rewrite Ep2; exact Ep1].
            apply (WINV_regs s c r r2 (CL_WINV s c r HCL Hlt) HR2 ltac:(rewrite Eo2; exact Eo1) ltac:(rewrite Ep2; exact Ep1)).
            rewrite E. mred. intros _. split; [exact HCm|]. split; [|repeat (split; [first [assumption | lia]|]); exact HT].
            right. rewrite cneed_cneedg. unfold cneedg.
            destruct HP2 as (k & _ & _ & _ & _ & _ & Mk & _).
            rewrite (decoded_entry_stable CODES _ _ used (ir_hold r1) (ir_bits r1) (ir_hold r2) here HTg Eh Hle ltac:(lia) RHO1 Mk).
            rewrite He. exact Hb2. }
        rewrite EQ2. pose proof (pulled_out r1 r2 HP2) as (Eo2 & Ep2 & El2 & _). pose proof (pulled_phi r1 r2 HP2) as PH2.
        pose proof HR2 as (RN2 & RH2 & RNH2 & RP2 & RL2 & RPL2 & [RB2 RHO2] & _).
        assert (B8 : ir_bits r2 - code_bits here - e < 8).
        { destruct Hb2 as [Hb2|Hb2]; [|lia]. destruct Hb1 as [Hb1|Hb1]; [|lia]. destruct (DISC Hb1); lia. }
        mrun DROPBITS_eq. mrun gs_eq. cbn [w_s].
        rewrite (wrap32_id (ir_bits r2 - code_bits here)) by lia.
        set (r3 := irset_bits (irset_hold r2 (Z.shiftr (ir_hold r2) (code_bits here))) (ir_bits r2 - code_bits here)).
        assert (HR3 : REGS c r3) by (subst r3; apply REGS_holdbits; [exact HR2|]; apply HB_drop; [split; [exact RB2|exact RHO2]|lia]).
        destruct (chk && (is_have s =? 0)) eqn:Cchk.
        {
          mrun go_bad_eq. unfold aret.
          split; [reflexivity|]. split; [|split; [unfold PHIr; subst r3; sacc; lia|split; [subst r3; sacc; rewrite Ep2; exact Ep1|split; reflexivity]]].
          unfold WINV. cbn [w_s w_c w_r]. sacc. mred.
          split; [core_keep HC; exact HL0|]. split; [eapply REGS_cview; [exact HR3|reflexivity|reflexivity]|].
          split; [exact (proj2 HCm)|]. split; [exact I|]. subst r3. sacc. rewrite Ep2, Ep1. exact HWB. }
        mrun BITS_eq. mrun DROPBITS_eq. mrun aret_eq.
        subst r3. sacc. rewrite (BITSv_mod _ e) by (try apply Z.shiftr_nonneg; lia).
        pose proof (mod_pow2_range (Z.shiftr (ir_hold r2) (code_bits here)) e ltac:(lia)) as MV.
        set (v := Z.shiftr (ir_hold r2) (code_bits here) mod 2 ^ e) in *.
        rewrite (wrap32_id (ir_bits r2 - code_bits here - e)) by lia.
        set (r4 := irset_bits (irset_hold (irset_bits (irset_hold r2 (Z.shiftr (ir_hold r2) (code_bits here))) (ir_bits r2 - code_bits here))
                     (Z.shiftr (Z.shiftr (ir_hold r2) (code_bits here)) e)) (ir_bits r2 - code_bits here - e)).
        assert (HR4 : REGS c r4).
        { subst r4. apply (REGS_holdbits c (irset_bits (irset_hold r2 (Z.shiftr (ir_hold r2) (code_bits here))) (ir_bits r2 - code_bits here))); [exact HR3|].
          apply (HB_drop _ (ir_bits r2 - code_bits here)); [|lia]. apply HB_drop; [split; [exact RB2|exact RHO2]|lia]. }
        assert (E4 : ir_bits r4 = ir_bits r2 - code_bits here - e /\ ir_have r4 = ir_have r2 /\ ir_left r4 = ir_left r2 /\ ir_put r4 = ir_put r2 /\ ir_out r4 = ir_out r2)
          by (subst r4; sacc; repeat split; reflexivity).
        destruct E4 as (E4b & E4h & E4l & E4p & E4o).
        mrun gs_eq. cbn [w_s].
        destruct (Z.ltb_spec (is_nlen s + is_ndist s) (is_have s + (base + v))) as [OV|OV].
        { mrun go_bad_eq. unfold aret.
          split; [reflexivity|]. split; [|split; [unfold PHIr; rewrite E4b, E4h, E4l; lia|split; [rewrite E4p, Ep2; exact Ep1|split; reflexivity]]].
          unfold WINV. cbn [w_s w_c w_r]. sacc. mred.
          split; [core_keep HC; exact HL0|]. split; [eapply REGS_cview; [exact HR4|reflexivity|reflexivity]|].
          split; [exact (proj2 HCm)|]. split; [exact I|]. rewrite E4p, Ep2, Ep1. exact HWB. }
        destruct (lens_repeat_eq (base + v) (lenf s) s c r4 ltac:(lia) ltac:(lia) ltac:(lia)) as (lens' & EQR & HL' & HG').
        mrun EQR. unfold aret.
        assert (HLF : 0 <= lenf s <= 15).
        { apply (Hlenf s eq_refl eq_refl). intros Hc. rewrite Hc in Cchk. cbn [andb] in Cchk. apply Z.eqb_neq in Cchk. lia. }
        split; [reflexivity|]. split; [|split; [sacc; lia|split; [lia|split; [reflexivity|split; [reflexivity|split; [unfold PHIr; rewrite E4b, E4h, E4l; lia|rewrite E4p, Ep2; exact Ep1]]]]]].
        unfold CL. sacc. split; [core_keep HC; [rewrite HL'; reflexivity|exact HL0]|].
        split; [exact HR4|]. split; [exact E|]. split; [common_keep HCm|]. split; [left; lia|].
        split; [exact Hnl|]. split; [exact Hnd|]. split; [lia|].
        split.
        { intros i Hi. rewrite HG'. rewrite CA1.
          destruct (Z.ltb_spec i (is_have s)) as [LT|GE].
          - replace (is_have s <=? i) with false by (symmetry; apply Z.leb_gt; exact LT). cbn [andb]. apply HLs. lia.
          - replace ((is_have s <=? i) && (i <? is_have s + (base + v)) && (i <? 320)) with true
              by (symmetry; rewrite !Bool.andb_true_iff, Z.leb_le, !Z.ltb_lt; lia).
            rewrite wrap16_id by lia. exact HLF. }
        split; [exact HT|]. rewrite E4o, E4p, Eo2, Ep2. split; [rewrite Eo1; exact HWF|rewrite Ep1; exact HWB]. }
      pose proof (code_val_nonneg here) as V0.
      destruct (Z.eqb_spec (code_val here) 16) as [E16|E16].
      + exact (GEN 2 3 (fun s0 => arr_get (is_lens s0) (is_have s0 - 1)) true ltac:(rewrite E16; reflexivity) ltac:(lia) ltac:(lia) ltac:(cbn; lia)
                 ltac:(intros s0 Eh0 El0 H1; cbv beta; rewrite Eh0, El0; apply HLs; lia)).
      + destruct (Z.eqb_spec (code_val here) 17) as [E17|E17].
        * exact (GEN 3 3 (fun _ => 0) false ltac:(rewrite E17; reflexivity) ltac:(lia) ltac:(lia) ltac:(cbn; lia) ltac:(intros; lia)).
        * exact (GEN 7 11 (fun _ => 0) false ltac:(apply cl_ext_ge18; lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia) ltac:(intros; lia)).
  Qed.

  Lemma codelens_while_S : forall k w,
    codelens_while (S k) w = (do s0 <- gs (fun s0 => s0) ;
                              if is_have s0 <? is_nlen s0 + is_ndist s0 then
                                do c0 <- codelens_body ; if c0 then codelens_while k else aret tt
                              else aret tt)%am w.
  Proof. reflexivity. Qed.

  Lemma codelens_while_spec : forall k s r,
    CL s c r -> is_nlen s + is_ndist s - is_have s < Z.of_nat k ->
    match codelens_while k (mkW s c r) with
    | ARun _ (mkW s' c' r') =>
        (c' = c /\ CL s' c' r' /\ is_have s' = is_nlen s' + is_ndist s' /\ is_nlen s' = is_nlen s /\ is_ndist s' = is_ndist s
         /\ PHIr r' <= PHIr r /\ ir_put r' = ir_put r /\ (is_have s < is_nlen s + is_ndist s -> PHIr r' + 8 <= PHIr r /\ ir_bits r' < 8)
         /\ (is_nlen s + is_ndist s <= is_have s -> s' = s /\ r' = r))
        \/ (is_mode s' = BAD /\ WINV (mkW s' c' r') /\ PHIr r' + 8 <= PHIr r /\ ir_put r' = ir_put r
            /\ ic_input c' = ic_input c /\ ic_outbuf c' = ic_outbuf c)
    | ALeave w' => WINV w' /\ ir_put (w_r w') = ir_put r
    | ARet _ _ => False
    end.
  Proof.
    induction k as [|k IH]; intros s r HCL Hk.
    { exfalso. pose proof HCL as (_ & _ & _ & _ & _ & _ & _ & Hh & _). cbn in Hk. lia. }
    rewrite codelens_while_S. mrun gs_eq. cbn [w_s].
    destruct (Z.ltb_spec (is_have s) (is_nlen s + is_ndist s)) as [LT|GE].
    - unfold abind at 1. pose proof (codelens_body_spec s r HCL LT) as B.
      destruct (codelens_body (mkW s c r)) as [[|] [s1 c1 r1] | w1 | rc w1].
      + cbv beta iota. destruct B as (-> & HCL1 & Hh1 & Hb1 & En1 & Ed1 & P1 & Ep1).
        specialize (IH s1 r1 HCL1 ltac:(lia)).
        destruct (codelens_while k (mkW s1 c r1)) as [u [s' c' r'] | w' | rc w']; [|rewrite <- Ep1; exact IH|exact IH].
        destruct IH as [(-> & HCL' & Hh' & En' & Ed' & P' & Ep' & Q' & Z')|(Hm & HW' & P' & Ep' & Ei' & Eo')].
        * left. rewrite En', Ed', En1, Ed1 in *. rewrite Ep1 in Ep'.
          split; [reflexivity|]. split; [exact HCL'|]. split; [exact Hh'|]. split; [reflexivity|]. split; [reflexivity|].
          split; [lia|]. split; [exact Ep'|]. split.
          -- intros _. split; [lia|]. destruct (Z.lt_ge_cases (is_have s1) (is_nlen s + is_ndist s)) as [X|X]; [apply Q'; exact X|].
             destruct (Z' X) as [_ ->]. exact Hb1.
          -- intros X. exfalso. lia.
        * right. rewrite Ep1 in Ep'. repeat (split; [first [assumption | lia]|]). exact Eo'.
      + cbv beta iota. unfold aret. right. destruct B as (Hm & HW1 & P1 & Ep1 & Ei1 & Eo1). repeat (split; [first [assumption | lia]|]). exact Eo1.
      + exact B.
      + exact B.
    - unfold aret. left. pose proof HCL as (_ & _ & _ & _ & _ & _ & _ & Hh & _).
      split; [reflexivity|]. split; [exact HCL|]. split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
      split; [lia|]. split; [reflexivity|]. split; [intros X; exfalso; lia|]. intros _; split; reflexivity.
  Qed.
End Codelens.
