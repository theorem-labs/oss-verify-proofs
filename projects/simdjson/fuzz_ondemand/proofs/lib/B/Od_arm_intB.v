(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Od_arm_int.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Import Sj_akit Od_defsB Od_tablesB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ od_load_hook | solve_load_base | solve_load_image ].

Section ArmInt.
  Variable E : oaenv.
  Hypothesis OK : od_oka E.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).

  Lemma od_int_tail : forall (Q : machine_state -> Prop) st (c k off neg : Z) xra xt1 xt2 xa2 xa5 xs2 xs5 xs6 xs10 xt3 xt5 xt6 xF xfc m1,
    tokT bs idxs (o_n E - 1) = C_RBRACKET ->
    od_head_ok bs idxs 1 st -> frm0 xfc -> ODINV E st m1 ->
    od_plus_k E Q st ->
    (0 <= c < 256)%Z -> (0 <= off <= o_len E)%Z -> (0 <= neg <= 1)%Z -> (1 <= k)%Z -> (off + neg + k <= o_len E)%Z ->
    evt bsegs Q (ODST E 0x98734 xra (Z_to_bv 64 (off + o_BUF E + neg + k)) xt1 xt2
                     (Z_to_bv 64 (oa_F E + 200)) (Z_to_bv 64 (off + o_BUF E + neg)) xa2 (Z_to_bv 64 ((oa_F E + 200) / 8 + 2147450880))
                     (Z_to_bv 64 neg) xa5 (Z_to_bv 64 ((off + o_BUF E + neg) / 8 + 2147450880)) (Z_to_bv 64 c)
                     xs2 xs5 xs6 xs10 (Z_to_bv 64 (oa_F E + 192)) xt3 (Z_to_bv 64 2) xt5 xt6 xF xfc m1).
  Proof using OK.
    intros Q st c k off neg xra xt1 xt2 xa2 xa5 xs2 xs5 xs6 xs10 xt3 xt5 xt6 xF xfc m1 HLAST HH FRM INV HK HC TR NGR HK1 HKL.
    pose proof HH as (HP & HD & HE & HA & HB).
    od_open_inv INV. od_env OK.
    pose proof (od_B_range E BOK (off + neg)) as Rn.
    pose proof (tokB_read m1 E (off + neg) BUFRO ltac:(lia)) as RBn.
    set (d0 := B bs (off + neg)) in *.
    pose proof (bfin_read m1 c MI HC) as RT. unfold BT_FIN in RT.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TRI.
    assert (KNONE : forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs10 xs11 xt3 xt4 xt5 xt6,
      evt bsegs Q (ODST E OD_PLUS xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1)).
    { intros. eapply (HK st); [| exact FRM| od_close_inv].
      apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_none. }
    unfold OD_PLUS in KNONE.
    assert (KFIN : forall xt0 xa1 xa2 xa6,
      evt bsegs Q (ODST E 0x98770 xra xt0 xt1 xt2
                     (Z_to_bv 64 (oa_F E + 200)) xa1 xa2 (Z_to_bv 64 ((oa_F E + 200) / 8 + 2147450880))
                     (Z_to_bv 64 neg) xa5 xa6 (Z_to_bv 64 c)
                     xs2 xs5 xs6 xs10 (Z_to_bv 64 (oa_F E + 192)) xt3 (Z_to_bv 64 2) xt5 xt6 xF xfc m1)).
    { intros.

      ostep. ostep. ostep. rewrite (Z.add_comm c 143808). ostep. uok. ostep. ostep. ostep. ostep. if_true. ostep. odnorm. zstep.
      if_cases K3; zify_cond K3; [ostep; uok; ostep; apply KNONE|].

      ostep. ostep. ostep. zstep. if_cases K4; zify_cond K4; [| ostep; apply KNONE].

      ostep. ostep. if_true. ostep. ostep. zstep. if_true.

      ostep. ostep. ostep. ostep. ostep. if_true. ostep. odnorm. ostep. ostep. uok. ostep. if_true. ostep. ostep. if_true.
      ostep. ostep. ostep. ostep. if_true. ostep. ostep. uok. ostep. ostep. if_true. ostep. ostep. ostep.
      od_cur_mem ltac:(fun mm => pose proof (tokI_read mm E ws (o_pos st) ltac:(eassumption) (conj IDXL IDXF) ltac:(lia)) as RD3).
      ostep. uok. ostep. ual. ostep. if_true. ostep. ostep. ostep. ostep. if_true. ostep. odnorm. ostep. ostep. uok. ostep. ostep. ostep. unz. ostep. if_true.
      ostep. ostep. if_true. ostep. ostep. if_true. ostep. ostep. ostep.
      eapply (HK (consume 1 st)); [| exact FRM| od_close_inv].
      apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_scalar. }

    zstep. uok.
    ostep. ostep. zstep. if_cases K1; zify_cond K1; [| ostep; apply KNONE].

    ostep. ostep. if_true. ostep. odnorm. ostep. zstep.
    if_cases K2; zify_cond K2; [apply KFIN|].
    ostep. zstep. if_cases K2b; zify_cond K2b; [apply KFIN| ostep; apply KNONE].
  Qed.

  Lemma od_int_loop : forall (f : nat) (Q : machine_state -> Prop) st (off neg k : Z) xra xt1 xt2 xa5 xa7 xs2 xs5 xs6 xs10 xt3 xt5 xt6 xF xfc m1,
    tokT bs idxs (o_n E - 1) = C_RBRACKET ->
    od_head_ok bs idxs 1 st -> frm0 xfc -> ODINV E st m1 ->
    od_plus_k E Q st ->
    (0 <= off <= o_len E)%Z -> (0 <= neg <= 1)%Z -> (0 <= k)%Z -> (48 <= B bs (off + neg + k) <= 57)%Z -> (blen bs - (off + neg + k) <= Z.of_nat f)%Z ->
    evt bsegs Q (ODST E 0x986d8 xra (Z_to_bv 64 (off + o_BUF E + neg + k)) xt1 xt2
                     (Z_to_bv 64 (oa_F E + 200)) (Z_to_bv 64 (off + o_BUF E + neg)) (Z_to_bv 64 (off + o_BUF E + neg + k + 1)) (Z_to_bv 64 ((oa_F E + 200) / 8 + 2147450880))
                     (Z_to_bv 64 neg) xa5 (Z_to_bv 64 ((off + o_BUF E + neg) / 8 + 2147450880)) xa7
                     xs2 xs5 xs6 xs10 (Z_to_bv 64 (oa_F E + 192)) xt3 (Z_to_bv 64 2) xt5 xt6 xF xfc m1).
  Proof using OK.
    intros f. induction f as [|f IH];
      intros Q st off neg k xra xt1 xt2 xa5 xa7 xs2 xs5 xs6 xs10 xt3 xt5 xt6 xF xfc m1 HLAST HH FRM INV HK TR NGR Hk HDIG Hf.
    - exfalso. assert (off + neg + k < blen bs)%Z by (apply B_nonzero_lt_len; lia). lia.
    - assert (QL : (off + neg + k < blen bs)%Z) by (apply B_nonzero_lt_len; lia).
      assert (INV2 := INV). od_open_inv INV. od_env OK.
      pose proof (od_B_range E BOK (off + neg + k + 1)) as R1.
      pose proof (tokB_read m1 E (off + neg + k + 1) BUFRO ltac:(lia)) as RB1.
      set (c := B bs (off + neg + k + 1)) in *.

      ostep. ostep. uok. ostep. ostep. ostep. ostep. if_false. ostep. ostep. odnorm. ostep. ostep. ostep. ostep. ostep. ostep. ostep. zstep.
      if_cases K; zify_cond K.
      +
        eapply evt_eq; [| eapply (IH Q st off neg (k + 1)%Z); [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| lia| lia| lia| | ]].
        * od_st_eq.
        * replace (off + neg + (k + 1))%Z with (off + neg + k + 1)%Z by lia. fold c. apply (zxb_digit c R1 K).
        * lia.
      +
        ostep.
        eapply evt_eq; [| eapply (od_int_tail Q st c (k + 1)%Z off neg); [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| lia| lia| lia| lia| lia]].
        od_st_eq.
  Qed.

  Theorem od_arm_int64 : arm_stmt E 0x97964.
  Proof using OK.
    unfold arm_stmt, arm_k. intros Q st HLAST HH HK xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs10 xt3 xt5 xt6 xF xfc m1 FRM INV.
    pose proof HH as (HP & HD & HE & HA & HB).
    assert (INV2 := INV). od_open_inv INV. od_env OK.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (tokI_read m1 E ws (o_pos st) IDXA (conj IDXL IDXF) ltac:(lia)) as RD1.
    set (off := tokI bs idxs (o_pos st)) in *.
    pose proof (od_B_range E BOK off) as R0.
    pose proof (tokB_read m1 E off BUFRO ltac:(lia)) as RB0.
    set (b0 := B bs off) in *.

    zstep. if_true.
    ostep. utrap. ostep. ual. ostep. if_false. ostep. ostep. ostep. ostep. ostep. ostep. ostep. if_true. ostep.
    zstep. if_true.

    ostep. ostep. ostep. ostep. ostep. if_true. ostep. odnorm. ostep. uok. ostep. if_true. ostep. if_true. ostep. ostep. ostep. ostep. if_true. ostep. uok. ostep. ual. ostep. if_true.
    ostep. ostep. ostep. ostep. ostep. if_true. ostep. odnorm. ostep. ostep. uok. ostep. ostep. ostep. unz. ostep. if_true. ostep. uok.
    ostep. ostep. ostep. ostep. if_true. ostep. odnorm. ostep. ostep.
    match goal with |- context [Z.b2z (?x <? 1)] => set (neg := Z.b2z (x <? 1)) in * end.
    assert (NGR : (0 <= neg <= 1)%Z) by (unfold neg; destruct (_ <? 1)%Z; cbn; lia). clearbody neg.
    pose proof (od_B_range E BOK (off + neg)) as Rn.
    pose proof (tokB_read m1 E (off + neg) BUFRO ltac:(lia)) as RBn.
    set (d0 := B bs (off + neg)) in *.

    ostep. ostep. uok. ostep. ostep. ostep. ostep. ostep. if_true. ostep. odnorm. ostep. ostep. ostep. zstep.
    if_cases K; zify_cond K.
    -
      ostep. ostep. zstep. if_false. ostep.
      eapply (HK st); [| exact FRM| od_close_inv].
      apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_none.
    -
      ostep. ostep. ostep. ostep.
      eapply evt_eq; [| eapply (od_int_loop (Z.to_nat (blen bs)) Q st off neg 0); [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| lia| lia| lia| | lia]].
      + od_st_eq.
      + replace (off + neg + 0)%Z with (off + neg)%Z by lia. fold d0. apply (zxb_digit d0 Rn). lia.
  Qed.

  Lemma od_uint_tail : forall (Q : machine_state -> Prop) st (k off : Z) xra xt0 xt1 xt2 xa3 xa6 xa7 xs2 xs5 xs6 xs10 xt3 xt5 xt6 xF xfc m1,
    tokT bs idxs (o_n E - 1) = C_RBRACKET ->
    od_head_ok bs idxs 1 st -> frm0 xfc -> ODINV E st m1 ->
    od_plus_k E Q st ->
    (0 <= off <= o_len E)%Z -> (1 <= k)%Z -> (off + k <= o_len E)%Z ->
    evt bsegs Q (ODST E 0x99100 xra xt0 xt1 xt2
                     (Z_to_bv 64 (oa_F E + 200)) (Z_to_bv 64 (off + o_BUF E)) (Z_to_bv 64 (off + o_BUF E + k)) xa3
                     (Z_to_bv 64 ((oa_F E + 200) / 8 + 2147450880)) (Z_to_bv 64 ((off + o_BUF E) / 8 + 2147450880)) xa6 xa7
                     xs2 xs5 xs6 xs10 (Z_to_bv 64 (oa_F E + 192)) xt3 (Z_to_bv 64 2) xt5 xt6 xF xfc m1).
  Proof using OK.
    intros Q st k off xra xt0 xt1 xt2 xa3 xa6 xa7 xs2 xs5 xs6 xs10 xt3 xt5 xt6 xF xfc m1 HLAST HH FRM INV HK TR HK1 HKL.
    pose proof HH as (HP & HD & HE & HA & HB).
    od_open_inv INV. od_env OK.
    pose proof (od_B_range E BOK off) as R0.
    pose proof (tokB_read m1 E off BUFRO ltac:(lia)) as RB0.
    set (b0 := B bs off) in *.
    pose proof (od_B_range E BOK (off + k)) as HC.
    pose proof (tokB_read m1 E (off + k) BUFRO ltac:(lia)) as RBk.
    set (c := B bs (off + k)) in *.
    pose proof (bfin_read m1 c MI HC) as RT. unfold BT_FIN in RT.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TRI.
    assert (KNONE : forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs10 xs11 xt3 xt4 xt5 xt6,
      evt bsegs Q (ODST E OD_PLUS xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1)).
    { intros. eapply (HK st); [| exact FRM| od_close_inv].
      apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_none. }
    unfold OD_PLUS in KNONE.
    assert (KCONS : forall xra xt0 xt1 xt2 xa1 xa2 xa3 xa5 xa6 xa7 xs2 xs5 xs6 xs10 xt3 xt5 xt6,
      evt bsegs Q (ODST E 0x9acc0 xra xt0 xt1 xt2
                     (Z_to_bv 64 (oa_F E + 200)) xa1 xa2 xa3 (Z_to_bv 64 ((oa_F E + 200) / 8 + 2147450880)) xa5 xa6 xa7
                     xs2 xs5 xs6 xs10 (Z_to_bv 64 (oa_F E + 192)) xt3 (Z_to_bv 64 2) xt5 xt6 xF xfc m1)).
    { intros. clear RB0 RBk RT.

      ostep. ostep. if_true. ostep. ostep. zstep. if_false.
      ostep. ostep. ostep. ostep. ostep. if_false. ostep. odnorm. ostep. ostep. uok. ostep. if_true. ostep. ostep. if_true.
      ostep. ostep. ostep. ostep. if_true. ostep. ostep. uok. ostep. ostep. if_true. ostep. ostep. ostep.
      od_cur_mem ltac:(fun mm => pose proof (tokI_read mm E ws (o_pos st) ltac:(eassumption) (conj IDXL IDXF) ltac:(lia)) as RD3).
      ostep. uok. ostep. ual. ostep. if_true. ostep. ostep. ostep. ostep. if_false. ostep. odnorm. ostep. ostep. uok. ostep. ostep. ostep. unz. ostep. if_true.
      ostep. ostep. if_true. ostep. ostep. if_false. ostep. ostep. ostep. ostep.
      eapply (HK (consume 1 st)); [| exact FRM| od_close_inv].
      apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_scalar. }
    assert (KFIN : forall xa1 xa3 xa5 xa6 xa7,
      evt bsegs Q (ODST E 0x99144 xra xt0 xt1 xt2
                     (Z_to_bv 64 (oa_F E + 200)) xa1 (Z_to_bv 64 (off + o_BUF E + k)) xa3
                     (Z_to_bv 64 ((oa_F E + 200) / 8 + 2147450880)) xa5 xa6 xa7
                     xs2 xs5 xs6 xs10 (Z_to_bv 64 (oa_F E + 192)) xt3 (Z_to_bv 64 2) xt5 xt6 xF xfc m1)).
    { intros.

      ostep. ostep. ostep. ostep. if_true. ostep. odnorm. ostep. ostep. ostep. rewrite (Z.add_comm c 143808). ostep. uok. ostep. ostep. ostep. ostep. if_true. ostep. odnorm. zstep.
      if_cases K3; zify_cond K3; [ostep; uok; ostep; apply KNONE|].

      ostep. ostep. zstep. if_cases K4; clear K4; [apply KCONS|].
      ostep. ostep. ostep. ostep. zstep. if_cases K5; clear K5; [apply KNONE| apply KCONS]. }

    ostep. ostep. zstep. uok.
    ostep. ostep. zstep. if_cases K1; zify_cond K1; [| ostep; apply KNONE].

    ostep. ostep. if_true. ostep. odnorm. ostep. zstep.
    if_cases K2; zify_cond K2; [apply KFIN|].
    ostep. zstep. if_cases K2b; zify_cond K2b; [apply KFIN| ostep; apply KNONE].
  Qed.

  Lemma od_uint_loop : forall (f : nat) (Q : machine_state -> Prop) st (off k : Z) xra xt0 xt1 xt2 xa6 xa7 xs2 xs5 xs6 xs10 xt3 xt5 xt6 xF xfc m1,
    tokT bs idxs (o_n E - 1) = C_RBRACKET ->
    od_head_ok bs idxs 1 st -> frm0 xfc -> ODINV E st m1 ->
    od_plus_k E Q st ->
    (0 <= off <= o_len E)%Z -> (0 <= k)%Z -> (48 <= B bs (off + k) <= 57)%Z -> (blen bs - (off + k) <= Z.of_nat f)%Z ->
    evt bsegs Q (ODST E 0x9909c xra xt0 xt1 xt2
                     (Z_to_bv 64 (oa_F E + 200)) (Z_to_bv 64 (off + o_BUF E)) (Z_to_bv 64 (off + o_BUF E + k)) (Z_to_bv 64 (off + o_BUF E + k + 1))
                     (Z_to_bv 64 ((oa_F E + 200) / 8 + 2147450880)) (Z_to_bv 64 ((off + o_BUF E) / 8 + 2147450880)) xa6 xa7
                     xs2 xs5 xs6 xs10 (Z_to_bv 64 (oa_F E + 192)) xt3 (Z_to_bv 64 2) xt5 xt6 xF xfc m1).
  Proof using OK.
    intros f. induction f as [|f IH];
      intros Q st off k xra xt0 xt1 xt2 xa6 xa7 xs2 xs5 xs6 xs10 xt3 xt5 xt6 xF xfc m1 HLAST HH FRM INV HK TR Hk HDIG Hf.
    - exfalso. assert (off + k < blen bs)%Z by (apply B_nonzero_lt_len; lia). lia.
    - assert (QL : (off + k < blen bs)%Z) by (apply B_nonzero_lt_len; lia).
      assert (INV2 := INV). od_open_inv INV. od_env OK.
      pose proof (od_B_range E BOK (off + k + 1)) as R1.
      pose proof (tokB_read m1 E (off + k + 1) BUFRO ltac:(lia)) as RB1.
      set (c := B bs (off + k + 1)) in *.

      ostep. ostep. uok. ostep. ostep. ostep. ostep. if_false. ostep. ostep. odnorm. ostep. ostep. ostep. ostep. ostep. ostep. ostep. zstep.
      if_cases K; zify_cond K.
      + eapply evt_eq; [| eapply (IH Q st off (k + 1)%Z); [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| lia| lia| | ]].
        * od_st_eq.
        * replace (off + (k + 1))%Z with (off + k + 1)%Z by lia. fold c. apply (zxb_digit c R1 K).
        * lia.
      +
        ostep.
        eapply evt_eq; [| eapply (od_uint_tail Q st (k + 1)%Z off); [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| lia| lia| lia]].
        od_st_eq.
  Qed.

  Theorem od_arm_uint64 : arm_stmt E 0x97b4c.
  Proof using OK.
    unfold arm_stmt, arm_k. intros Q st HLAST HH HK xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs10 xt3 xt5 xt6 xF xfc m1 FRM INV.
    pose proof HH as (HP & HD & HE & HA & HB).
    assert (INV2 := INV). od_open_inv INV. od_env OK.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (tokI_read m1 E ws (o_pos st) IDXA (conj IDXL IDXF) ltac:(lia)) as RD1.
    set (off := tokI bs idxs (o_pos st)) in *.
    pose proof (od_B_range E BOK off) as R0.
    pose proof (tokB_read m1 E off BUFRO ltac:(lia)) as RB0.
    set (b0 := B bs off) in *.

    zstep. if_true.
    ostep. utrap. ostep. ual. ostep. if_false. ostep. ostep. ostep. ostep. ostep. ostep. ostep. if_true. ostep.
    zstep. if_false. ostep.

    ostep. ostep. ostep. ostep. ostep. if_true. ostep. odnorm. ostep. uok. ostep. if_true. ostep. if_true. ostep. ostep. ostep. ostep. if_true. ostep. uok. ostep. ual. ostep. if_true.
    ostep. ostep. ostep. ostep. ostep. if_true. ostep. odnorm. ostep. ostep. uok. ostep. ostep. ostep. unz. ostep. if_true. ostep. uok.
    ostep. ostep. ostep. ostep. if_true. ostep. odnorm. ostep. ostep. ostep. zstep.
    if_cases K; zify_cond K.
    -
      ostep. ostep. zstep. if_false. ostep.
      eapply (HK st); [| exact FRM| od_close_inv].
      apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_none.
    -
      ostep. ostep. ostep.
      eapply evt_eq; [| eapply (od_uint_loop (Z.to_nat (blen bs)) Q st off 0); [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| lia| lia| | lia]].
      + od_st_eq.
      + replace (off + 0)%Z with off by lia. fold b0. apply (zxb_digit b0 R0). lia.
  Qed.
End ArmInt.
