(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Od_arm_int.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow Sj_akit Od_defsA Od_tablesA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ od_load_hook | solve_load_base | solve_load_image ].

Notation IST E pc xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m :=
  (MS (mkR (Z_to_bv 64 (o_act E)) (Z_to_bv 64 (oa_S1 E)) (o_gp E) (o_tp E) xt0 xt1 xt2
           (Z_to_bv 64 (oa_USP E)) (Z_to_bv 64 (oa_S1 E)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
           xs2 (Z_to_bv 64 2147450880) (Z_to_bv 64 (oa_F E + 32)) (Z_to_bv 64 ((oa_F E + 200) / 8 + 2147450880))
           (Z_to_bv 64 (oa_F E + 192)) (Z_to_bv 64 ((oa_F E + 228) / 8 + 2147450880)) (Z_to_bv 64 (oa_F E + 200))
           xs9 xs10 xs11 xt3 xt4 xt5 xt6)
      xF (Z_to_bv 64 pc) xfc None m (seg_rom asegs)).

Section ArmInt.
  Variable E : oaenv.
  Hypothesis OK : od_oka E.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).

  Lemma od_int_tail : forall (Q : machine_state -> Prop) st (c k off neg : Z) xt2 xa5 xa6 xa7 xs2 xt3 xt5 xt6 xF xfc m1,
    tokT bs idxs (o_n E - 1) = C_RBRACKET ->
    od_head_ok bs idxs 1 st -> frm0 xfc -> ODINV E st m1 ->
    od_plus_k E Q st ->
    (0 <= c < 256)%Z -> (0 <= off <= o_len E)%Z -> (0 <= neg <= 1)%Z ->
    evt asegs Q (IST E 0x97f88 (Z_to_bv 64 k) (Z_to_bv 64 ((o_BUF E + off + neg) / 8 + 2147450880)) xt2
                     (Z_to_bv 64 (oa_F E + 200)) (Z_to_bv 64 (o_BUF E + off + neg)) (Z_to_bv 64 ((oa_F E + 200) / 8 + 2147450880))
                     (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 neg) xa5 xa6 xa7
                     xs2 (Z_to_bv 64 2) (Z_to_bv 64 (oa_F E + 192)) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) xt3 (Z_to_bv 64 c) xt5 xt6 xF xfc m1).
  Proof using OK.
    intros Q st c k off neg xt2 xa5 xa6 xa7 xs2 xt3 xt5 xt6 xF xfc m1 HLAST HH FRM INV HK HC TR NGR.
    pose proof HH as (HP & HD & HE & HA & HB).
    od_open_inv INV. od_env OK.
    pose proof (od_B_range E BOK (off + neg)) as Rn.
    pose proof (tokB_read m1 E (off + neg) BUFRO ltac:(lia)) as RBn.
    set (d0 := B bs (off + neg)) in *.
    pose proof (afin_read m1 c MI HC) as RT. unfold AT_FIN in RT.
    assert (KNONE : forall xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4,
      evt asegs Q (ODST E OD_PLUS xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1)).
    { intros. apply (HK st); [| exact FRM| od_close_inv].
      apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_none. }
    unfold OD_PLUS in KNONE.

    ostep. ostep. ostep. zstep.
    if_cases K1; zify_cond K1; [apply KNONE|].

    ostep. ostep. ostep. if_true. ostep. odnorm. ostep. zstep.
    assert (KFIN : forall xa1 xa5,
      evt asegs Q (IST E 0x97fbc (Z_to_bv 64 k) (Z_to_bv 64 ((o_BUF E + off + neg) / 8 + 2147450880)) (Z_to_bv 64 2)
                     (Z_to_bv 64 (oa_F E + 200)) xa1 (Z_to_bv 64 ((oa_F E + 200) / 8 + 2147450880))
                     (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 neg) xa5 xa6 xa7
                     xs2 (Z_to_bv 64 2) (Z_to_bv 64 (oa_F E + 192)) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) xt3 (Z_to_bv 64 c)
                     (Z_to_bv 64 1) (Z_to_bv 64 1) xF xfc m1)).
    { intros.

      ostep. ostep. ostep. ostep. ostep. ostep. ostep. if_true. ostep. odnorm. zstep.
      if_cases K3; zify_cond K3; [apply KNONE|].

      ostep. ostep. zstep. if_cases K4; zify_cond K4; [apply KNONE|].

      zstep. if_false.

      ostep. ostep. ostep. ostep. ostep. if_true. ostep. ostep. if_true. ostep. ostep. ostep. ostep. if_true. ostep. ostep. ostep.
      apply (HK (consume 1 st)); [| exact FRM| od_close_inv].
      apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_scalar. }
    if_cases K2; zify_cond K2.
    -
      eapply evt_eq; [| eapply KFIN]. od_st_eq.
    -
      ostep. zstep. if_cases K2b; zify_cond K2b; [apply KNONE|].
      eapply evt_eq; [| eapply KFIN]. od_st_eq.
  Qed.

  Lemma od_int_loop : forall (f : nat) (Q : machine_state -> Prop) st (off neg k : Z) xt2 xa5 xa6 xa7 xt4 xt5 xt6 xF xfc m1,
    tokT bs idxs (o_n E - 1) = C_RBRACKET ->
    od_head_ok bs idxs 1 st -> frm0 xfc -> ODINV E st m1 ->
    od_plus_k E Q st ->
    (0 <= off <= o_len E)%Z -> (0 <= neg <= 1)%Z -> (0 <= k)%Z -> (48 <= B bs (off + neg + k) <= 57)%Z -> (blen bs - (off + neg + k) <= Z.of_nat f)%Z ->
    evt asegs Q (IST E 0x97758 (Z_to_bv 64 k) (Z_to_bv 64 ((o_BUF E + off + neg) / 8 + 2147450880)) xt2
                     (Z_to_bv 64 (oa_F E + 200)) (Z_to_bv 64 (o_BUF E + off + neg)) (Z_to_bv 64 ((oa_F E + 200) / 8 + 2147450880))
                     (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 neg) xa5 xa6 xa7
                     (Z_to_bv 64 10) (Z_to_bv 64 2) (Z_to_bv 64 (oa_F E + 192)) (Z_to_bv 64 (o_IDX E + 4 * o_pos st))
                     (Z_to_bv 64 (o_BUF E + (neg + off) + 1)) xt4 xt5 xt6 xF xfc m1).
  Proof using OK.
    intros f. induction f as [|f IH];
      intros Q st off neg k xt2 xa5 xa6 xa7 xt4 xt5 xt6 xF xfc m1 HLAST HH FRM INV HK TR NGR Hk HDIG Hf.
    - exfalso. assert (off + neg + k < blen bs)%Z by (apply B_nonzero_lt_len; lia). lia.
    - assert (QL : (off + neg + k < blen bs)%Z) by (apply B_nonzero_lt_len; lia).
      assert (INV2 := INV). od_open_inv INV. od_env OK.
      pose proof (od_B_range E BOK (off + neg + k + 1)) as R1.
      pose proof (tokB_read m1 E (off + neg + k + 1) BUFRO ltac:(lia)) as RB1.
      set (c := B bs (off + neg + k + 1)) in *.

      ostep. ostep. ostep. ostep. ostep. if_false. ostep. odnorm. ostep. ostep. ostep. ostep. ostep. ostep. zstep.
      if_cases K; zify_cond K.
      +
        eapply evt_eq; [| eapply (IH Q st off neg (k + 1)%Z); [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| lia| lia| lia| | ]].
        * od_st_eq.
        * replace (off + neg + (k + 1))%Z with (off + neg + k + 1)%Z by lia. fold c. apply (zxb_digit c R1 K).
        * lia.
      +
        ostep.
        eapply evt_eq; [| eapply (od_int_tail Q st c (k + 1)%Z off neg); [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| lia| lia| lia]].
        od_st_eq.
  Qed.

  Theorem od_arm_int64 : arm_stmt E 0x97690.
  Proof using OK.
    unfold arm_stmt, arm_k. intros Q st HLAST HH HK xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs11 xt3 xt4 xF xfc m1 FRM INV.
    pose proof HH as (HP & HD & HE & HA & HB).
    assert (INV2 := INV). od_open_inv INV. od_env OK.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (tokI_read m1 E ws (o_pos st) IDXA (conj IDXL IDXF) ltac:(lia)) as RD1.
    set (off := tokI bs idxs (o_pos st)) in *.
    pose proof (od_B_range E BOK off) as R0.
    pose proof (tokB_read m1 E off BUFRO ltac:(lia)) as RB0.
    set (b0 := B bs off) in *.
    zstep. if_true.
    ostep. ostep. ostep. ostep. ostep. if_true. ostep. ostep. ostep. ostep. if_true. ostep. ostep. ostep. ostep. ostep. ostep. if_true.
    ostep. odnorm. ostep. ostep. ostep. ostep. ostep. if_true. ostep. odnorm. ostep. ostep.
    match goal with |- context [Z.b2z (?x <? 1)] => set (neg := Z.b2z (x <? 1)) in * end.
    assert (NGR : (0 <= neg <= 1)%Z) by (unfold neg; destruct (_ <? 1)%Z; cbn; lia). clearbody neg.
    pose proof (od_B_range E BOK (off + neg)) as Rn.
    pose proof (tokB_read m1 E (off + neg) BUFRO ltac:(lia)) as RBn.
    set (d0 := B bs (off + neg)) in *.
    ostep. ostep. ostep. ostep. ostep. if_true. ostep. odnorm. ostep. ostep. ostep. zstep.
    if_cases K; zify_cond K.
    - ostep. ostep. ostep. ostep. ostep. ostep. ostep. ostep.
      eapply evt_eq; [| eapply (od_int_loop (Z.to_nat (blen bs)) Q st off neg 0); [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| lia| lia| lia| | lia]].
      + od_st_eq.
      + replace (off + neg + 0)%Z with (off + neg)%Z by lia. fold d0. apply (zxb_digit d0 Rn). lia.
    -
      ostep.
      apply (HK st); [| exact FRM| od_close_inv].
      apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_none.
  Qed.

  Lemma od_uint_tail : forall (Q : machine_state -> Prop) st (c off : Z) xt0 xt1 xa2 xa5 xa6 xs11 xt3 xt4 xF xfc m1,
    tokT bs idxs (o_n E - 1) = C_RBRACKET ->
    od_head_ok bs idxs 1 st -> frm0 xfc -> ODINV E st m1 ->
    od_plus_k E Q st ->
    (0 <= c < 256)%Z -> (0 <= off <= o_len E)%Z ->
    evt asegs Q (ODST E 0x98034 xt0 xt1 (Z_to_bv 64 c)
                     (Z_to_bv 64 (oa_F E + 200)) (Z_to_bv 64 (o_BUF E + off)) xa2 (Z_to_bv 64 ((oa_F E + 200) / 8 + 2147450880))
                     (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) xa5 xa6 (Z_to_bv 64 ((o_BUF E + off) / 8 + 2147450880))
                     (Z_to_bv 64 2) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 (oa_F E + 192)) xs11 xt3 xt4 xF xfc m1).
  Proof using OK.
    intros Q st c off xt0 xt1 xa2 xa5 xa6 xs11 xt3 xt4 xF xfc m1 HLAST HH FRM INV HK HC TR.
    pose proof HH as (HP & HD & HE & HA & HB).
    od_open_inv INV. od_env OK.
    pose proof (od_B_range E BOK off) as R0.
    pose proof (tokB_read m1 E off BUFRO ltac:(lia)) as RB0.
    set (b0 := B bs off) in *.
    pose proof (afin_read m1 c MI HC) as RT. unfold AT_FIN in RT.
    assert (KNONE : forall xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4,
      evt asegs Q (ODST E OD_PLUS xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1)).
    { intros. apply (HK st); [| exact FRM| od_close_inv].
      apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_none. }
    unfold OD_PLUS in KNONE.
    assert (KFIN : forall xt0 xa1 xa2 xa5 xa6 xa7,
      evt asegs Q (ODST E 0x98060 xt0 xt1 (Z_to_bv 64 c)
                     (Z_to_bv 64 (oa_F E + 200)) xa1 xa2 (Z_to_bv 64 ((oa_F E + 200) / 8 + 2147450880))
                     (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) xa5 xa6 xa7
                     (Z_to_bv 64 2) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 (oa_F E + 192)) xs11 xt3 xt4 xF xfc m1)).
    { intros.

      ostep. ostep. ostep. ostep. ostep. ostep. ostep. if_true. ostep. odnorm. zstep.
      if_cases K3; zify_cond K3; [apply KNONE|].

      ostep. ostep. ostep. ostep. ostep. ostep. ostep. ostep. zstep.
      if_cases K4; zify_cond K4; [apply KNONE|].

      zstep. if_false.

      ostep. ostep. ostep. ostep. ostep. if_true. ostep. ostep. if_true. ostep. ostep. ostep. ostep. if_true. ostep. ostep. ostep.
      apply (HK (consume 1 st)); [| exact FRM| od_close_inv].
      apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_scalar. }

    ostep. ostep. zstep. if_cases K1; zify_cond K1; [apply KNONE|].

    ostep. ostep. if_true. ostep. odnorm. ostep. zstep. if_cases K2; zify_cond K2; [apply KFIN|].

    ostep. zstep. if_cases K2b; zify_cond K2b; [apply KNONE|].
    apply KFIN.
  Qed.

  Lemma od_uint_loop : forall (f : nat) (Q : machine_state -> Prop) st (off q : Z) xt0 xt2 xa5 xa6 xs11 xt3 xF xfc m1,
    tokT bs idxs (o_n E - 1) = C_RBRACKET ->
    od_head_ok bs idxs 1 st -> frm0 xfc -> ODINV E st m1 ->
    od_plus_k E Q st ->
    (0 <= off <= o_len E)%Z -> (0 <= q)%Z -> (48 <= B bs q <= 57)%Z -> (blen bs - q <= Z.of_nat f)%Z ->
    evt asegs Q (ODST E 0x97970 xt0 (Z_to_bv 64 (o_BUF E + q + 1)) xt2
                     (Z_to_bv 64 (oa_F E + 200)) (Z_to_bv 64 (o_BUF E + off)) (Z_to_bv 64 (o_BUF E + q + 1)) (Z_to_bv 64 ((oa_F E + 200) / 8 + 2147450880))
                     (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) xa5 xa6 (Z_to_bv 64 ((o_BUF E + off) / 8 + 2147450880))
                     (Z_to_bv 64 2) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 (oa_F E + 192)) xs11 xt3 (Z_to_bv 64 10) xF xfc m1).
  Proof using OK.
    intros f. induction f as [|f IH];
      intros Q st off q xt0 xt2 xa5 xa6 xs11 xt3 xF xfc m1 HLAST HH FRM INV HK TR Hq HDIG Hf.
    - exfalso. assert (q < blen bs)%Z by (apply B_nonzero_lt_len; lia). lia.
    - assert (QL : (q < blen bs)%Z) by (apply B_nonzero_lt_len; lia).
      assert (INV2 := INV). od_open_inv INV. od_env OK.
      pose proof (od_B_range E BOK (q + 1)) as R1.
      pose proof (tokB_read m1 E (q + 1) BUFRO ltac:(lia)) as RB1.
      set (c := B bs (q + 1)) in *.

      ostep. ostep. ostep. ostep. if_false. ostep. ostep. odnorm. ostep. ostep. ostep. ostep. ostep. ostep. ostep. zstep.
      if_cases K; zify_cond K.
      + eapply evt_eq; [| eapply (IH Q st off (q + 1)%Z); [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| lia| lia| | ]].
        * od_st_eq.
        * fold c. apply (zxb_digit c R1 K).
        * lia.
      +
        ostep.
        eapply evt_eq; [| eapply (od_uint_tail Q st c off); [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| lia| lia]].
        od_st_eq.
  Qed.

  Theorem od_arm_uint64 : arm_stmt E 0x978d8.
  Proof using OK.
    unfold arm_stmt, arm_k. intros Q st HLAST HH HK xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs11 xt3 xt4 xF xfc m1 FRM INV.
    pose proof HH as (HP & HD & HE & HA & HB).
    assert (INV2 := INV). od_open_inv INV. od_env OK.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (tokI_read m1 E ws (o_pos st) IDXA (conj IDXL IDXF) ltac:(lia)) as RD1.
    set (off := tokI bs idxs (o_pos st)) in *.
    pose proof (od_B_range E BOK off) as R0.
    pose proof (tokB_read m1 E off BUFRO ltac:(lia)) as RB0.
    set (b0 := B bs off) in *.

    zstep. if_true.
    ostep. ostep. ostep. ostep. ostep. if_true. ostep. ostep. ostep. ostep. if_true. ostep. ostep. ostep. ostep. ostep. ostep. if_true.
    ostep. odnorm. ostep. ostep. ostep. ostep. ostep. if_true. ostep. odnorm. ostep. ostep. ostep. zstep.
    if_cases K; zify_cond K.
    -
      ostep. ostep. ostep. ostep. ostep.
      eapply evt_eq; [| eapply (od_uint_loop (Z.to_nat (blen bs)) Q st off off); [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| lia| lia| | lia]].
      + od_st_eq.
      + fold b0. apply (zxb_digit b0 R0). lia.
    -
      ostep.
      apply (HK st); [| exact FRM| od_close_inv].
      apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_none.
  Qed.
End ArmInt.
