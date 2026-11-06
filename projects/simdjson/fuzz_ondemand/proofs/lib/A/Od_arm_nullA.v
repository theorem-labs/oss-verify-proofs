(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow Sj_akit Od_defsA Od_tablesA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ od_load_hook | solve_load_base | solve_load_image ].

Section ArmNull.
  Variable E : oaenv.
  Hypothesis OK : od_oka E.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).

  Lemma od_null_join : forall (Q : machine_state -> Prop) st xt0 xt1 xt2 xa1 xa2 xa3 xa6 xa7 xs11 xt3 xt4 xF xfc m1,
    tokT bs idxs (o_n E - 1) = C_RBRACKET ->
    od_head_ok bs idxs 1 st -> frm0 xfc -> ODINV E st m1 ->
    od_plus_k E Q st ->
    evt asegs Q (ODST E 0x97c30 xt0 xt1 xt2 (Z_to_bv 64 (oa_F E + 200)) xa1 xa2 xa3
                      (Z_to_bv 64 ((oa_F E + 200) / 8 + 2147450880)) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) xa6 xa7
                      (Z_to_bv 64 2) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 (oa_F E + 192)) xs11 xt3 xt4 xF xfc m1).
  Proof using OK.
    intros Q st xt0 xt1 xt2 xa1 xa2 xa3 xa6 xa7 xs11 xt3 xt4 xF xfc m1 HLAST HH FRM INV HK.
    pose proof HH as (HP & HD & HE & HA & HB).
    od_open_inv INV. od_env OK.
    assert (KNONE : forall xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4,
      evt asegs Q (ODST E OD_PLUS xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1)).
    { intros. apply (HK st); [| exact FRM| od_close_inv].
      apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_none. }
    unfold OD_PLUS in KNONE.

    ostep. zstep.
    if_cases K; zify_cond K; [| ostep; apply KNONE].
    zstep. if_true. ostep. zstep.
    if_cases K2; zify_cond K2; [| ostep; apply KNONE].

    ostep. ostep. ostep. ostep. ostep. if_true. ostep. ostep. if_true. ostep. ostep. ostep. ostep. if_true. ostep. ostep. ostep.
    apply (HK (consume 1 st)); [| exact FRM| od_close_inv].
    apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_scalar.
  Qed.

  Theorem od_arm_null : arm_stmt E 0x97b0c.
  Proof using OK.
    unfold arm_stmt, arm_k. intros Q st HLAST HH HK xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs11 xt3 xt4 xF xfc m1 FRM INV.
    pose proof HH as (HP & HD & HE & HA & HB).
    assert (INV2 := INV). od_open_inv INV. od_env OK.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (tokI_read m1 E ws (o_pos st) IDXA (conj IDXL IDXF) ltac:(lia)) as RD1.
    set (off := tokI bs idxs (o_pos st)) in *.
    pose proof (od_B_range E BOK off) as R0. pose proof (od_B_range E BOK (off + 1)) as R1.
    pose proof (od_B_range E BOK (off + 2)) as R2. pose proof (od_B_range E BOK (off + 3)) as R3.
    pose proof (od_B_range E BOK (off + 4)) as R4.
    pose proof (tokB_read m1 E off BUFRO ltac:(lia)) as RB0.
    pose proof (tokB_read m1 E (off + 1) BUFRO ltac:(lia)) as RB1.
    pose proof (tokB_read m1 E (off + 2) BUFRO ltac:(lia)) as RB2.
    pose proof (tokB_read m1 E (off + 3) BUFRO ltac:(lia)) as RB3.
    pose proof (tokB_read m1 E (off + 4) BUFRO ltac:(lia)) as RB4.
    set (b0 := B bs off) in *. set (b1 := B bs (off + 1)) in *. set (b2 := B bs (off + 2)) in *.
    set (b3 := B bs (off + 3)) in *. set (b4 := B bs (off + 4)) in *.
    pose proof (asow_read m1 b4 MI ltac:(lia)) as RT4. pose proof (osow_range b4) as RS4. unfold AT_SOW in RT4.

    assert (KTAIL : forall xt0 xt1 xt2 xa1 xa3 xa7 xs11 xt3 xt4,
      evt asegs Q (ODST E 0x97c0c xt0 xt1 xt2 (Z_to_bv 64 (oa_F E + 200)) xa1 (Z_to_bv 64 (o_BUF E + off)) xa3
                      (Z_to_bv 64 ((oa_F E + 200) / 8 + 2147450880)) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 ((o_BUF E + off) / 8 + 2147450880)) xa7
                      (Z_to_bv 64 2) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 (oa_F E + 192)) xs11 xt3 xt4 xF xfc m1)).
    { intros.

      ostep. ostep. if_true. ostep. odnorm. ostep. ostep. ostep. ostep. ostep.
      eapply evt_eq; [| eapply (od_null_join Q st); [exact HLAST| exact HH| exact FRM| exact INV2| exact HK]].
      od_st_eq. }

    zstep. if_true.
    ostep. ostep. ostep. ostep. ostep. if_true. ostep. ostep. ostep. ostep. if_true. ostep. ostep. ostep. ostep. ostep. ostep. if_true.
    ostep. odnorm. ostep. ostep. ostep. ostep. ostep. if_true. ostep. ostep. ostep. ostep. ostep. if_true.
    ostep. odnorm. ostep. odnorm. ostep. odnorm. ostep. odnorm. ostep. ostep. ostep. ostep. ostep. ostep.
    repeat match goal with |- context [Z_to_bv 64 (Z.lor ?x ?y)] => let w := fresh "w" in set (w := Z_to_bv 64 (Z.lor x y)) in *; clearbody w end.
    repeat match goal with |- context [Z_to_bv 64 (Z.shiftl ?x ?y)] => let w := fresh "v" in set (w := Z_to_bv 64 (Z.shiftl x y)) in *; clearbody w end.

    ostep. zstep.
    if_cases K; zify_cond K.
    -
      eapply evt_eq; [| eapply KTAIL]. od_st_eq.
    -
      ostep. ostep. ostep. ostep. ostep. if_true. ostep. odnorm. ostep. ostep. ostep. ostep. ostep. ostep. ostep. if_true. ostep. odnorm. zstep.
      if_cases K2; zify_cond K2.
      + eapply evt_eq; [| eapply KTAIL]. od_st_eq.
      + ostep. ostep.
        eapply evt_eq; [| eapply (od_null_join Q st); [exact HLAST| exact HH| exact FRM| exact INV2| exact HK]].
        od_st_eq.
  Qed.
End ArmNull.
