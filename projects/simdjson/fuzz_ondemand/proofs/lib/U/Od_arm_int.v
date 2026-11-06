(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.U Require Import Od_defs Od_tables.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Lemma B_nonzero_lt_len : forall bs q, B bs q <> 0%Z -> (q < blen bs)%Z.
Proof. intros bs q H. destruct (Z.lt_ge_cases q (blen bs)) as [L|G]; [exact L|]. exfalso. apply H. apply B_pad. exact G. Qed.

Lemma zxb_digit : forall c, (0 <= c < 256)%Z -> (Z.land ((c + -48) mod 18446744073709551616) 255 < 10)%Z -> (48 <= c <= 57)%Z.
Proof.
  intros c Hc H. change 255%Z with (Z.ones 8) in H. rewrite Z.land_ones in H by lia.
  change (2 ^ 8)%Z with 256%Z in H.
  destruct (Z.lt_ge_cases c 48) as [L|G].
  - exfalso. replace ((c + -48) mod 18446744073709551616)%Z with (c + 18446744073709551568)%Z in H
      by (apply Z.mod_unique with (q := (-1)%Z); lia).
    replace ((c + 18446744073709551568) mod 256)%Z with (c + 208)%Z in H
      by (apply Z.mod_unique with (q := 72057594037927935%Z); lia).
    lia.
  - rewrite (Z.mod_small (c + -48)) in H by lia. rewrite Z.mod_small in H by lia. lia.
Qed.

Section ArmInt.
  Variable E : odenv.
  Hypothesis OK : od_ok E.
  Hypothesis OKU : od_oku E.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).

  Lemma od_num_consume : forall (Q : machine_state -> Prop) st xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs11 xt3 xt4 xt5 xt6 xF xfc m1,
    tokT bs idxs (o_n E - 1) = C_RBRACKET ->
    od_head_ok bs idxs 1 st -> frm0 xfc -> ODINV E st m1 ->
    od_plus_k E Q st ->
    evt usegs Q (ODST E 0x28edc xra xt0 xt1 xt2 (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 (o_BUF E)) xa2 xa3 xa4 xa5 xa6 xa7
                      (Z_to_bv 64 2) (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) xs11 xt3 xt4 xt5 xt6 xF xfc m1).
  Proof using OK OKU.
    intros Q st xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs11 xt3 xt4 xt5 xt6 xF xfc m1 HLAST HH FRM INV HK.
    pose proof HH as (HP & HD & HE & HA & HB).
    od_open_inv INV. od_env OK. od_envu OKU.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (tokI_read m1 E ws (o_pos st) IDXA (conj IDXL IDXF) ltac:(lia)) as RD1.
    set (off := tokI bs idxs (o_pos st)) in *.
    assert (A8 : ((bv_unsigned (o_sp E) + -272) mod 8 = 0)%Z) by (apply od_sp_al8; [exact USP| reflexivity]).
    assert (A4 : ((o_IDX E + 4 * o_pos st) mod 4 = 0)%Z) by (apply od_idx_al4; lia).

    zstep. if_cases K1; zify_cond K1; try (exfalso; lia). clear K1.
    zstep. odnorm. zstep. utrap. zstep. utrap. zstep. zstep. utrap.
    zstep. zstep. utrap. zstep.

    zstep. zstep. zstep. utrap. zstep. ual. zstep. if_false. zstep.

    od_cur_mem ltac:(fun mm => pose proof (tokI_read mm E ws (o_pos st) ltac:(eassumption) (conj IDXL IDXF) ltac:(lia)) as RD3).
    fold off in RD3.
    zstep. odnorm. zstep. zstep. utrap.
    zstep. zstep. zstep. unz. zstep. utrap.
    zstep. zstep. utrap. zstep. zstep.
    apply (HK (consume 1 st)); [| exact FRM| od_close_inv].
    apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_scalar.
  Qed.

  Lemma od_int_tail : forall (Q : machine_state -> Prop) st (q0 q neg c : Z) xra xt0 xt1 xt2 xa3 xa6 xs11 xt3 xt4 xt5 xt6 xF xfc m1,
    tokT bs idxs (o_n E - 1) = C_RBRACKET ->
    od_head_ok bs idxs 1 st -> frm0 xfc -> ODINV E st m1 ->
    od_plus_k E Q st ->
    (0 <= q0 <= q)%Z -> (q < blen bs)%Z -> (0 <= neg <= 1)%Z -> (0 <= c < 256)%Z ->
    evt usegs Q (ODST E 0x282e4 xra xt0 xt1 xt2 (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 (o_BUF E)) (Z_to_bv 64 neg) xa3
                      (Z_to_bv 64 (o_BUF E + q0)) (Z_to_bv 64 c) xa6 (Z_to_bv 64 (o_BUF E + q + 1))
                      (Z_to_bv 64 2) (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) xs11 xt3 xt4 xt5 xt6 xF xfc m1).
  Proof using OK OKU.
    intros Q st q0 q neg c xra xt0 xt1 xt2 xa3 xa6 xs11 xt3 xt4 xt5 xt6 xF xfc m1 HLAST HH FRM INV HK Hq HQL HN HC.
    pose proof HH as (HP & HD & HE & HA & HB).
    assert (INV2 := INV). od_open_inv INV. od_env OK. od_envu OKU.
    pose proof (ufin_read m1 c MI HC) as RT. unfold UT_FIN in RT.
    pose proof (ofin_range c) as RF.
    pose proof (od_B_range E BOK q0) as R0.
    pose proof (tokB_read m1 E q0 BUFRO ltac:(unfold blen in *; lia)) as RB0.
    set (d0 := B bs q0) in *.
    assert (KNONE : forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs11 xt3 xt4 xt5 xt6,
      evt usegs Q (ODST E OD_PLUS xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                      (Z_to_bv 64 2) (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) xs11 xt3 xt4 xt5 xt6 xF xfc m1)).
    { intros. apply (HK st); [| exact FRM| od_close_inv].
      apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_none. }
    unfold OD_PLUS in KNONE.
    assert (KFIN : forall xra xt0 xt1 xt2 xa3 xa4 xa6 xa7 xs11 xt3 xt4 xt5 xt6,
      evt usegs Q (ODST E 0x28318 xra xt0 xt1 xt2 (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 (o_BUF E)) (Z_to_bv 64 neg) xa3
                      xa4 (Z_to_bv 64 c) xa6 xa7
                      (Z_to_bv 64 2) (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) xs11 xt3 xt4 xt5 xt6 xF xfc m1)).
    { intros.

      zstep. zstep. zstep. zstep. uok. zstep. odnorm. zstep.
      if_cases K3; zify_cond K3.
      -
        zstep. zstep. zstep. if_cases K4; zify_cond K4; [apply KNONE|].
        eapply evt_eq; [| eapply (od_num_consume Q st); [exact HLAST| exact HH| exact FRM| exact INV2| exact HK]].
        od_st_eq.
      - zstep. utrap. zstep. apply KNONE. }

    zstep. if_cases K0; zify_cond K0; try (exfalso; lia). clear K0.
    zstep. zstep. zstep. if_cases K1; zify_cond K1; [apply KNONE|].

    zstep. odnorm. zstep. zstep.
    if_cases K2; zify_cond K2; [apply KFIN|].
    zstep. zstep. if_cases K2b; zify_cond K2b; [apply KNONE|].
    apply KFIN.
  Qed.

  Lemma od_int_loop : forall (f : nat) (Q : machine_state -> Prop) st (q0 q neg : Z) xra xt1 xt2 xa3 xa5 xa6 xa7 xs11 xt3 xt4 xt5 xt6 xF xfc m1,
    tokT bs idxs (o_n E - 1) = C_RBRACKET ->
    od_head_ok bs idxs 1 st -> frm0 xfc -> ODINV E st m1 ->
    od_plus_k E Q st ->
    (0 <= q0 <= q)%Z -> (0 <= neg <= 1)%Z -> (48 <= B bs q <= 57)%Z -> (blen bs - q <= Z.of_nat f)%Z ->
    evt usegs Q (ODST E 0x282b8 xra (Z_to_bv 64 (o_BUF E + q)) xt1 xt2 (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 (o_BUF E)) (Z_to_bv 64 neg) xa3
                      (Z_to_bv 64 (o_BUF E + q0)) xa5 xa6 xa7
                      (Z_to_bv 64 2) (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) xs11 xt3 xt4 xt5 xt6 xF xfc m1).
  Proof using OK OKU.
    intros f. induction f as [|f IH];
      intros Q st q0 q neg xra xt1 xt2 xa3 xa5 xa6 xa7 xs11 xt3 xt4 xt5 xt6 xF xfc m1 HLAST HH FRM INV HK Hq0 HN HDIG Hf.
    - exfalso. assert (q < blen bs)%Z by (apply B_nonzero_lt_len; lia). lia.
    - assert (QL : (q < blen bs)%Z) by (apply B_nonzero_lt_len; lia).
      assert (INV2 := INV). od_open_inv INV. od_env OK. od_envu OKU.
      pose proof (od_B_range E BOK (q + 1)) as R1.
      pose proof (tokB_read m1 E (q + 1) BUFRO ltac:(unfold blen in *; lia)) as RB1.
      set (c := B bs (q + 1)) in *.

      zstep. uok. zstep. odnorm. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      if_cases K; zify_cond K.
      +
        eapply evt_eq; [| eapply (IH Q st q0 (q + 1)%Z neg); [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| lia| lia| | ]].
        * od_st_eq.
        * fold c. apply (zxb_digit c R1 K).
        * lia.
      + eapply evt_eq; [| eapply (od_int_tail Q st q0 q neg c); [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| lia| lia| lia| lia]].
        od_st_eq.
  Qed.

  Theorem od_arm_int64 : arm_stmt E 0x27a74.
  Proof using OK OKU.
    unfold arm_stmt. intros Q st xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs11 xt3 xt4 xt5 xt6 xF xfc m1 HLAST HH FRM INV HK.
    pose proof HH as (HP & HD & HE & HA & HB).
    assert (INV2 := INV). od_open_inv INV. od_env OK. od_envu OKU.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (tokI_read m1 E ws (o_pos st) IDXA (conj IDXL IDXF) ltac:(lia)) as RD1.
    set (off := tokI bs idxs (o_pos st)) in *.
    pose proof (od_B_range E BOK off) as R0.
    pose proof (tokB_read m1 E off BUFRO ltac:(lia)) as RB0.
    set (b0 := B bs off) in *.
    assert (A8 : ((bv_unsigned (o_sp E) + -272) mod 8 = 0)%Z) by (apply od_sp_al8; [exact USP| reflexivity]).
    assert (A4 : ((o_IDX E + 4 * o_pos st) mod 4 = 0)%Z) by (apply od_idx_al4; lia).

    zstep. if_false.
    zstep. uok. zstep. ual. zstep. if_true.
    zstep. zstep. if_cases K1; zify_cond K1; try (exfalso; lia). clear K1.

    zstep. odnorm. zstep. uok. zstep. uok. zstep. zstep. uok. zstep. uok. zstep. ual. zstep. if_true.

    zstep. zstep. odnorm. zstep. zstep. uok.
    zstep. zstep. zstep. unz. zstep. uok. zstep. uok.

    zstep. odnorm. zstep. zstep.
    match goal with |- context [Z.b2z (?x <? 1)] => set (neg := Z.b2z (x <? 1)) in * end.
    assert (NGR : (0 <= neg <= 1)%Z) by (unfold neg; destruct (_ <? 1)%Z; cbn; lia). clearbody neg.
    pose proof (od_B_range E BOK (off + neg)) as Rn.
    pose proof (tokB_read m1 E (off + neg) BUFRO ltac:(lia)) as RBn.
    set (d0 := B bs (off + neg)) in *.
    zstep. zstep. uok. zstep.

    zstep. odnorm. zstep. zstep. zstep. zstep.
    if_cases K; zify_cond K.
    -
      zstep. zstep. zstep. if_true.
      apply (HK st); [| exact FRM| od_close_inv].
      apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_none.
    -
      zstep. zstep.
      eapply evt_eq; [| eapply (od_int_loop (Z.to_nat (blen bs)) Q st (off + neg) (off + neg) neg); [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| lia| lia| | lia]].
      + od_st_eq.
      + fold d0. apply (zxb_digit d0 Rn). lia.
  Qed.

  Lemma od_uint_tail : forall (Q : machine_state -> Prop) st (q0 q c : Z) xra xt0 xt1 xt2 xa4 xa6 xa7 xs11 xt3 xt4 xt5 xt6 xF xfc m1,
    tokT bs idxs (o_n E - 1) = C_RBRACKET ->
    od_head_ok bs idxs 1 st -> frm0 xfc -> ODINV E st m1 ->
    od_plus_k E Q st ->
    (0 <= q0 <= q)%Z -> (q < blen bs)%Z -> (0 <= c < 256)%Z ->
    evt usegs Q (ODST E 0x28580 xra xt0 xt1 xt2 (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 (o_BUF E)) (Z_to_bv 64 (o_BUF E + q0)) (Z_to_bv 64 c)
                      xa4 (Z_to_bv 64 (o_BUF E + q + 1)) xa6 xa7
                      (Z_to_bv 64 2) (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) xs11 xt3 xt4 xt5 xt6 xF xfc m1).
  Proof using OK OKU.
    intros Q st q0 q c xra xt0 xt1 xt2 xa4 xa6 xa7 xs11 xt3 xt4 xt5 xt6 xF xfc m1 HLAST HH FRM INV HK Hq HQL HC.
    pose proof HH as (HP & HD & HE & HA & HB).
    assert (INV2 := INV). od_open_inv INV. od_env OK. od_envu OKU.
    pose proof (ufin_read m1 c MI HC) as RT. unfold UT_FIN in RT.
    pose proof (ofin_range c) as RF.
    pose proof (od_B_range E BOK q0) as R0.
    pose proof (tokB_read m1 E q0 BUFRO ltac:(unfold blen in *; lia)) as RB0.
    set (d0 := B bs q0) in *.
    assert (KNONE : forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs11 xt3 xt4 xt5 xt6,
      evt usegs Q (ODST E OD_PLUS xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                      (Z_to_bv 64 2) (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) xs11 xt3 xt4 xt5 xt6 xF xfc m1)).
    { intros. apply (HK st); [| exact FRM| od_close_inv].
      apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_none. }
    unfold OD_PLUS in KNONE.
    assert (KCONS : forall xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs11 xt3 xt4 xt5 xt6,
      evt usegs Q (ODST E 0x28edc xra xt0 xt1 xt2 (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 (o_BUF E)) xa2 xa3 xa4 xa5 xa6 xa7
                      (Z_to_bv 64 2) (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) xs11 xt3 xt4 xt5 xt6 xF xfc m1)).
    { intros. apply (od_num_consume Q st); [exact HLAST| exact HH| exact FRM| exact INV2| exact HK]. }
    assert (KFIN : forall xra xt0 xt1 xt2 xa2 xa4 xa5 xa6 xa7 xs11 xt3 xt4 xt5 xt6,
      evt usegs Q (ODST E 0x285bc xra xt0 xt1 xt2 (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 (o_BUF E)) xa2 (Z_to_bv 64 c)
                      xa4 xa5 xa6 xa7
                      (Z_to_bv 64 2) (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) xs11 xt3 xt4 xt5 xt6 xF xfc m1)).
    { intros.

      zstep. zstep. zstep. zstep. utrap. zstep. odnorm. zstep.
      if_cases K3; zify_cond K3.
      -
        zstep. zstep. if_cases K4; zify_cond K4; [apply KCONS|].
        zstep. zstep. zstep. zstep. zstep. if_cases K5; zify_cond K5; [apply KNONE|].
        zstep. apply KCONS.
      - zstep. utrap. zstep. apply KNONE. }

    zstep. zstep. zstep. if_cases K0; zify_cond K0; try (exfalso; lia). clear K0.
    zstep. zstep. zstep. if_cases K1; zify_cond K1; [apply KNONE|].

    zstep. odnorm. zstep. zstep.
    if_cases K2; zify_cond K2; [apply KFIN|].
    zstep. zstep. if_cases K2b; zify_cond K2b; [apply KNONE|].
    apply KFIN.
  Qed.

  Lemma od_uint_loop : forall (f : nat) (Q : machine_state -> Prop) st (q0 q : Z) xra xt0 xt1 xt2 xa3 xa4 xa5 xa6 xs11 xt3 xt4 xt5 xt6 xF xfc m1,
    tokT bs idxs (o_n E - 1) = C_RBRACKET ->
    od_head_ok bs idxs 1 st -> frm0 xfc -> ODINV E st m1 ->
    od_plus_k E Q st ->
    (0 <= q0 <= q)%Z -> (48 <= B bs q <= 57)%Z -> (blen bs - q <= Z.of_nat f)%Z ->
    evt usegs Q (ODST E 0x28558 xra xt0 xt1 xt2 (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 (o_BUF E)) (Z_to_bv 64 (o_BUF E + q0)) xa3
                      xa4 xa5 xa6 (Z_to_bv 64 (o_BUF E + q))
                      (Z_to_bv 64 2) (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) xs11 xt3 xt4 xt5 xt6 xF xfc m1).
  Proof using OK OKU.
    intros f. induction f as [|f IH];
      intros Q st q0 q xra xt0 xt1 xt2 xa3 xa4 xa5 xa6 xs11 xt3 xt4 xt5 xt6 xF xfc m1 HLAST HH FRM INV HK Hq0 HDIG Hf.
    - exfalso. assert (q < blen bs)%Z by (apply B_nonzero_lt_len; lia). lia.
    - assert (QL : (q < blen bs)%Z) by (apply B_nonzero_lt_len; lia).
      assert (INV2 := INV). od_open_inv INV. od_env OK. od_envu OKU.
      pose proof (od_B_range E BOK (q + 1)) as R1.
      pose proof (tokB_read m1 E (q + 1) BUFRO ltac:(unfold blen in *; lia)) as RB1.
      set (c := B bs (q + 1)) in *.

      zstep. utrap. zstep. odnorm. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      if_cases K; zify_cond K.
      + eapply evt_eq; [| eapply (IH Q st q0 (q + 1)%Z); [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| lia| | ]].
        * od_st_eq.
        * fold c. apply (zxb_digit c R1 K).
        * lia.
      + eapply evt_eq; [| eapply (od_uint_tail Q st q0 q c); [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| lia| lia| lia]].
        od_st_eq.
  Qed.

  Theorem od_arm_uint64 : arm_stmt E 0x27b34.
  Proof using OK OKU.
    unfold arm_stmt. intros Q st xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs11 xt3 xt4 xt5 xt6 xF xfc m1 HLAST HH FRM INV HK.
    pose proof HH as (HP & HD & HE & HA & HB).
    assert (INV2 := INV). od_open_inv INV. od_env OK. od_envu OKU.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (tokI_read m1 E ws (o_pos st) IDXA (conj IDXL IDXF) ltac:(lia)) as RD1.
    set (off := tokI bs idxs (o_pos st)) in *.
    pose proof (od_B_range E BOK off) as R0.
    pose proof (tokB_read m1 E off BUFRO ltac:(lia)) as RB0.
    set (b0 := B bs off) in *.
    assert (A8 : ((bv_unsigned (o_sp E) + -272) mod 8 = 0)%Z) by (apply od_sp_al8; [exact USP| reflexivity]).
    assert (A4 : ((o_IDX E + 4 * o_pos st) mod 4 = 0)%Z) by (apply od_idx_al4; lia).

    zstep. if_false.
    zstep. uok. zstep. ual. zstep. if_true.
    zstep. zstep. if_cases K1; zify_cond K1; try (exfalso; lia). clear K1.

    zstep. odnorm. zstep. utrap. zstep. utrap. zstep. zstep. utrap. zstep. utrap. zstep. ual. zstep. if_false.

    zstep. zstep. odnorm. zstep. zstep. utrap.
    zstep. zstep. zstep. unz. zstep. utrap. zstep. utrap.

    zstep. odnorm. zstep. zstep. zstep. zstep.
    if_cases K; zify_cond K.
    -
      zstep. zstep. zstep. if_true.
      apply (HK st); [| exact FRM| od_close_inv].
      apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_none.
    -
      zstep. zstep.
      eapply evt_eq; [| eapply (od_uint_loop (Z.to_nat (blen bs)) Q st off off); [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| lia| | lia]].
      + od_st_eq.
      + fold b0. apply (zxb_digit b0 R0). lia.
  Qed.
End ArmInt.
