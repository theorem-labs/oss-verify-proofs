(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow Sj_akit Od_defsA Od_tablesA Od_headA Od_nest_plusA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ od_load_hook | solve_load_base | solve_load_image ].

Section NestElem.
  Variable E : oaenv.
  Hypothesis OK : od_oka E.
  Hypothesis HLAST : tokT (o_bs E) (o_idxs E) (o_n E - 1) = C_RBRACKET.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).
  Notation n := (o_n E).

  Definition nest_next (st st' : ost) : Prop :=
    od_next_ok bs idxs 2 st st' \/ od_next_ok bs idxs 2 (consume 2 st) st'.

  Lemma an_null_join : forall (Q : machine_state -> Prop) st xa5 xa6 xs9 xt5 xt6 xF xfc m1,
    od_head_ok bs idxs 2 st -> frm0 xfc -> NODINV E st m1 ->
    nhead_any E Q (nest_next st) ->
    evt asegs Q (NSTp E 0x988a0 (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) xa5 xa6 (Z_to_bv 64 2) xs9 xt5 xt6 xF xfc m1).
  Proof using OK HLAST.
    intros Q st xa5 xa6 xs9 xt5 xt6 xF xfc m1 HH FRM INV HK.
    pose proof HH as (HP & HD & HE & HA & HB).
    assert (HD3 : o_depth st = 3%Z) by lia.
    od_env OK.

    pose proof (acc_plus_ok bs idxs S1 HLAST 2 st st ltac:(lia) HH (acc_none bs idxs 2 st)) as PO0.
    pose proof (acc_plus_ok bs idxs S1 HLAST 2 st (consume 2 st) ltac:(lia) HH (acc_scalar bs idxs 2 st)) as PO1.
    assert (K_NONE : forall ya4 ya5 ya6 yt5,
              evt asegs Q (NSTp E 0x988dc ya4 ya5 ya6 (Z_to_bv 64 2) xs9 yt5 xt6 xF xfc m1)).
    { intros. eapply (an_plus E OK HLAST Q st _ _ _ _ _ _ _ _ m1 PO0 FRM INV).
      intros st' ? ? ? ? ? ? ? ? ? ? m' P' F' I'. apply (HK st'); [left; exact P'| exact F'| exact I']. }
    assert (K_CONS : forall ya4 ya5 ya6 yt5 mm, NODINV E (consume 2 st) mm ->
              evt asegs Q (NSTp E 0x988dc ya4 ya5 ya6 (Z_to_bv 64 2) xs9 yt5 xt6 xF xfc mm)).
    { intros ya4 ya5 ya6 yt5 mm INV2.
      eapply (an_plus E OK HLAST Q (consume 2 st) _ _ _ _ _ _ _ _ mm PO1 FRM INV2).
      intros st' ? ? ? ? ? ? ? ? ? ? m' P' F' I'. apply (HK st'); [right; exact P'| exact F'| exact I']. }
    nod_open INV. rewrite HD3 in ITER.

    ostep. ostep. ostep. ostep. zstep.
    if_cases K; [apply K_NONE|].

    ostep. ostep. if_false. ostep. ostep. if_true. ostep. ostep. ostep. ostep. if_false. ostep.
    eapply evt_eq; [| eapply K_CONS; nod_close]. od_st_eq.
  Qed.

  Lemma an_null_tail : forall (Q : machine_state -> Prop) st xa6 xs2 xs9 xt6 xF xfc m1,
    od_head_ok bs idxs 2 st -> frm0 xfc -> NODINV E st m1 ->
    nhead_any E Q (nest_next st) ->
    evt asegs Q (NSTp E 0x98878 (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 (o_BUF E + tokI bs idxs (o_pos st))) xa6 xs2 xs9
                      (Z_to_bv 64 ((o_BUF E + tokI bs idxs (o_pos st)) / 8 + 2147450880)) xt6 xF xfc m1).
  Proof using OK HLAST.
    intros Q st xa6 xs2 xs9 xt6 xF xfc m1 HH FRM INV HK.
    pose proof HH as (HP & HD & HE & HA & HB).
    assert (INV2 := INV). nod_open INV. od_env OK.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    set (off := tokI bs idxs (o_pos st)) in *.
    pose proof (od_B_range E BOK off) as R0.
    pose proof (tokB_read m1 E off BUFRO ltac:(lia)) as RB0.
    set (b0 := B bs off) in *.

    ostep. ostep. ostep. ostep. if_false. ostep. odnorm. ostep. ostep. ostep. ostep. ostep.
    eapply evt_eq; [| eapply (an_null_join Q st); [exact HH| exact FRM| exact INV2| exact HK]].
    od_st_eq.
  Qed.

  Lemma an_elem : forall (Q : machine_state -> Prop) st xa4 xa5 xa6 xa7 xs9 xt3 xt4 xt5 xt6 xF xfc m1,
    od_head_ok bs idxs 2 st -> frm0 xfc -> NODINV E st m1 ->
    nhead_any E Q (nest_next st) ->
    evt asegs Q (NSTa E 0x98784 (Z_to_bv 64 ((oa_F E + 228) / 8 + 2147450880)) (Z_to_bv 64 ((oa_F E + 224) / 8 + 2147450880))
                      xa4 xa5 xa6 xa7 (Z_to_bv 64 2) xs9 xt3 xt4 xt5 xt6 xF xfc m1).
  Proof using OK HLAST.
    intros Q st xa4 xa5 xa6 xa7 xs9 xt3 xt4 xt5 xt6 xF xfc m1 HH FRM INV HK.
    pose proof HH as (HP & HD & HE & HA & HB).
    assert (INV2 := INV). nod_open INV. od_env OK.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (tokI_read m1 E ws (o_pos st) IDXA (conj IDXL IDXF) ltac:(lia)) as RD1.
    set (off := tokI bs idxs (o_pos st)) in *.
    pose proof (od_B_range E BOK off) as R0. pose proof (od_B_range E BOK (off + 1)) as R1.
    pose proof (od_B_range E BOK (off + 2)) as R2. pose proof (od_B_range E BOK (off + 3)) as R3.
    pose proof (od_B_range E BOK (off + 4)) as R4.
    set (b0 := B bs off) in *. set (b1 := B bs (off + 1)) in *. set (b2 := B bs (off + 2)) in *.
    set (b3 := B bs (off + 3)) in *. set (b4 := B bs (off + 4)) in *.

    ochk. ostep. ostep. ostep. if_false. ochk. ostep. ostep. ostep. ostep. ostep. if_false.

    ostep. odnorm. clear RD1. ostep. ochkn. ostep. ostep. ochkn.

    pose proof (tokB_read m1 E (off + 1) BUFRO ltac:(lia)) as RB1. fold b1 in RB1. ostep. odnorm. clear RB1.
    pose proof (tokB_read m1 E off BUFRO ltac:(lia)) as RB0. fold b0 in RB0. ostep. odnorm. clear RB0.
    pose proof (tokB_read m1 E (off + 2) BUFRO ltac:(lia)) as RB2. fold b2 in RB2. ostep. odnorm. clear RB2.
    pose proof (tokB_read m1 E (off + 3) BUFRO ltac:(lia)) as RB3. fold b3 in RB3. ostep. odnorm. clear RB3.
    ostep. ostep. ostep. ostep. ostep. ostep.
    repeat match goal with |- context [Z_to_bv 64 (Z.lor ?x ?y)] => let w := fresh "w" in set (w := Z_to_bv 64 (Z.lor x y)) in *; clearbody w end.
    repeat match goal with |- context [Z_to_bv 64 (Z.shiftl ?x ?y)] => let w := fresh "v" in set (w := Z_to_bv 64 (Z.shiftl x y)) in *; clearbody w end.

    ostep. zstep.
    if_cases K; zify_cond K.
    -
      eapply evt_eq; [| eapply (an_null_tail Q st); [exact HH| exact FRM| exact INV2| exact HK]]. od_st_eq.
    -
      ostep. ochkn.
      pose proof (tokB_read m1 E (off + 4) BUFRO ltac:(lia)) as RB4. fold b4 in RB4. ostep. odnorm. clear RB4.
      pose proof (asow_read m1 b4 MI ltac:(lia)) as RT4. pose proof (osow_range b4) as RS4. unfold AT_SOW in RT4.
      ostep. ostep. ostep. ochkn. ostep. odnorm. zstep.
      if_cases K2; zify_cond K2.
      + eapply evt_eq; [| eapply (an_null_tail Q st); [exact HH| exact FRM| exact INV2| exact HK]]. od_st_eq.
      + ostep. ostep. ostep. ostep.
        eapply evt_eq; [| eapply (an_null_join Q st); [exact HH| exact FRM| exact INV2| exact HK]].
        od_st_eq.
  Qed.
End NestElem.
