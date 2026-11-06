(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Od_arm_dbl_defs Od_arm_int.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section ArmDblInt.
  Variable E : odenv.
  Hypothesis OK : od_ok E.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).

  Lemma dbl_int_tail : forall (Q : machine_state -> Prop) st (neg q0 q : Z) v128 j0 j8 j16 j56 j64 j72 j80 j136
      xt0 xt1 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xt4 xt5 xF xfc m1,
    tokT bs idxs (o_n E - 1) = C_RBRACKET ->
    od_head_ok bs idxs 1 st -> frm0 xfc ->
    DBLINVc E st [CB 8 j0; CB 8 j8; CB 8 j16] [CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; C8 (Z_to_bv 64 neg)] [C8 v128; CB 8 j136] m1 ->
    od_plus_k E Q st -> dbl_A_k E Q st ->
    (0 <= neg <= 1)%Z -> q0 = (tokI bs idxs (o_pos st) + neg)%Z -> (q0 <= q <= o_len E + 2)%Z ->
    evt psegs Q (ODST E 0x27b14 xt0 xt1 (Z_to_bv 64 (o_BUF E + q)) xa0 (Z_to_bv 64 (o_BUF E + q0)) xa2 xa3 xa4 xa5 xa6 xa7
                      (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 2) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 (B bs q)) xt4 xt5 xF xfc m1).
  Proof using OK.
    intros until m1. intros HLAST HH FRM INV HK HA NGR Hq0 Hq.
    assert (INV2 := INV). dbl_open_inv INV. od_env OK.
    zstep. zstep. zstep. zstep. zstep.
    if_cases K; zify_cond K.
    - apply (HK st); [| exact FRM| dbl_close_od].
      apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_none.
    - eapply evt_eq; [| eapply (HA neg q0 q); [exact NGR | exact Hq0 | exact Hq | exact FRM | exact INV2]].
      od_st_eq.
  Qed.

  Lemma dbl_int_loop : forall (f : nat) (Q : machine_state -> Prop) st (neg q0 k : Z) v128 j0 j8 j16 j56 j64 j72 j80 j136
      xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt5 xF xfc m1,
    tokT bs idxs (o_n E - 1) = C_RBRACKET ->
    od_head_ok bs idxs 1 st -> frm0 xfc ->
    DBLINVc E st [CB 8 j0; CB 8 j8; CB 8 j16] [CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; C8 (Z_to_bv 64 neg)] [C8 v128; CB 8 j136] m1 ->
    od_plus_k E Q st -> dbl_A_k E Q st ->
    (0 <= neg <= 1)%Z -> q0 = (tokI bs idxs (o_pos st) + neg)%Z -> (1 <= k)%Z -> (48 <= B bs (q0 + k) <= 57)%Z ->
    (blen bs - (q0 + k) <= Z.of_nat f)%Z ->
    evt psegs Q (ODST E 0x27840 xt0 xt1 xt2 xa0 (Z_to_bv 64 (o_BUF E + q0)) xa2 xa3 xa4 xa5 xa6 xa7
                      (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 2) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) xt3 (Z_to_bv 64 k) xt5 xF xfc m1).
  Proof using OK.
    intros f. induction f as [|f IH]; intros until m1; intros HLAST HH FRM INV HK HA NGR Hq0 Hk HDIG Hf.
    - exfalso. assert (q0 + k < blen bs)%Z by (apply B_nonzero_lt_len; lia). lia.
    - assert (QL : (q0 + k < blen bs)%Z) by (apply B_nonzero_lt_len; lia).
      pose proof HH as (HP & HD & HE & HAL & HB).
      assert (INV2 := INV). dbl_open_inv INV. od_env OK.
      pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
      pose proof (od_B_range E BOK (q0 + k + 1)) as R1.
      pose proof (tokB_read m1 E (q0 + k + 1) BUFRO ltac:(lia)) as RB1.
      set (c := B bs (q0 + k + 1)) in *.
      zstep. zstep. odnorm. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      if_cases K; zify_cond K.
      +
        eapply evt_eq; [| eapply (IH Q st neg q0 (k + 1)%Z); [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| exact HA| exact NGR| exact Hq0| lia| | ]].
        * od_st_eq.
        * replace (q0 + (k + 1))%Z with (q0 + k + 1)%Z by lia. fold c. apply (zxb_digit c R1 K).
        * lia.
      + zstep. zstep. if_cases K2; zify_cond K2; [|exfalso; lia].
        eapply evt_eq; [| eapply (dbl_int_tail Q st neg q0 (q0 + k + 1)%Z); [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| exact HA| exact NGR| exact Hq0| lia]].
        od_st_eq.
  Qed.

  Theorem od_dbl_int : forall (Q : machine_state -> Prop) st xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xF xfc m1,
    tokT bs idxs (o_n E - 1) = C_RBRACKET ->
    od_head_ok bs idxs 1 st -> frm0 xfc -> ODINV E st m1 ->
    od_plus_k E Q st -> dbl_A_k E Q st ->
    evt psegs Q (ODST E 0x277e0 xt0 xt1 xt2 (Z_to_bv 64 1) xa1 xa2 xa3 xa4 xa5 xa6 xa7
                      (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 2) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) xt3 xt4 xt5 xF xfc m1).
  Proof using OK.
    intros Q st xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xF xfc m1 HLAST HH FRM INV HK HA.
    pose proof HH as (HP & HD & HE & HAL & HB).
    assert (INV2 := INV). od_open_inv INV. od_env OK.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (tokI_read m1 E ws (o_pos st) IDXA (conj IDXL IDXF) ltac:(lia)) as RD1.
    set (off := tokI bs idxs (o_pos st)) in *.
    pose proof (od_B_range E BOK off) as R0.
    pose proof (tokB_read m1 E off BUFRO ltac:(lia)) as RB0.
    set (b0 := B bs off) in *.
    zstep. if_false.
    zstep. zstep. odnorm. zstep. zstep. odnorm. zstep. zstep.
    match goal with |- context [Z.b2z (?x <? 1)] => set (neg := Z.b2z (x <? 1)) in * end.
    assert (NGR : (0 <= neg <= 1)%Z) by (unfold neg; destruct (_ <? 1)%Z; cbn; lia). clearbody neg.
    zstep.
    od_cur_mem ltac:(fun mm => pose proof (tokB_read mm E (off + neg) BUFRO ltac:(lia)) as RBn).
    pose proof (od_B_range E BOK (off + neg)) as Rn.
    set (d0 := B bs (off + neg)) in *.
    zstep. zstep. odnorm. zstep. zstep. zstep.
    assert (KNONE : forall xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 mm,
      ODINV E st mm ->
      evt psegs Q (ODST E OD_PLUS xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                      (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 2) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) xt3 xt4 xt5 xF xfc mm)).
    { intros. apply (HK st); [| exact FRM| assumption].
      apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_none. }
    unfold OD_PLUS in KNONE.
    destruct (Z.ltb_spec (Z.land ((d0 + -48) mod 18446744073709551616) 255) 10) as [DG|ND]; cbn [Z.b2z].
    -
      pose proof (zxb_digit d0 Rn DG) as D0.
      assert (QL : (off + neg < blen bs)%Z) by (apply B_nonzero_lt_len; fold d0; lia).
      od_cur_mem ltac:(fun mm => pose proof (tokB_read mm E (off + neg + 1) BUFRO ltac:(lia)) as RB1).
      pose proof (od_B_range E BOK (off + neg + 1)) as R1.
      set (d1 := B bs (off + neg + 1)) in *.
      zstep. zstep. odnorm. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (INV3 : DBLINVc E st [CB 8 j0; CB 8 j8; CB 8 j16] [CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; C8 (Z_to_bv 64 neg)]
                         [C8 (Z_to_bv 64 (Z.land 18446744073709551615 (d0 + -48))); CB 8 j136] mm) by dbl_close_inv end.
      zstep.
      if_cases K; zify_cond K.
      +
        zstep. zstep. if_false.
        eapply evt_eq; [| eapply (dbl_int_tail Q st neg (off + neg)%Z (off + neg + 1)%Z); [exact HLAST| exact HH| exact FRM| exact INV3| exact HK| exact HA| exact NGR| reflexivity| lia]].
        od_st_eq.
      + zstep.
        eapply evt_eq; [| eapply (dbl_int_loop (Z.to_nat (blen bs)) Q st neg (off + neg)%Z 1%Z); [exact HLAST| exact HH| exact FRM| exact INV3| exact HK| exact HA| exact NGR| reflexivity| lia| | lia]].
        * od_st_eq.
        * fold d1. apply (zxb_digit d1 R1). lia.
    -
      zstep. zstep. odnorm. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      zstep.
      if_cases K; zify_cond K; [| exfalso; lia].
      zstep. zstep. if_true.
      apply KNONE. dbl_close_od.
  Qed.
End ArmDblInt.
