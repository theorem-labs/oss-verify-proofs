(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.U Require Import Od_defs Od_plus.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section Head.
  Variable E : odenv.
  Hypothesis OK : od_ok E.
  Hypothesis OKU : od_oku E.
  Hypothesis HLAST : tokT (o_bs E) (o_idxs E) (o_n E - 1) = C_RBRACKET.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).
  Notation n := (o_n E).

  Lemma od_disp_err : forall (Q : machine_state -> Prop) st v144 v176 v184 v200 v208 v216
      xra xt0 xt1 xt2 xs0 xs1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs5 xs7 xs8 xs9 xs11 xt3 xt4 xt5 xt6 xF xfc m1,
    frm0 xfc -> ODINVg E v144 v176 v184 v200 v208 v216 st m1 ->
    (forall xa0' xa1' xa2' xs11' m',
       ODINVg E v144 v176 v184 v200 v208 v216 st m' ->
       evt usegs Q (MS (mkR xra (Z_to_bv 64 (FR E)) (o_gp E) (o_tp E) xt0 xt1 xt2 xs0 xs1 xa0' xa1' xa2' xa3 xa4 xa5 xa6 xa7
                            (Z_to_bv 64 0) xs3 (Z_to_bv 64 (o_act E)) xs5 (Z_to_bv 64 0) xs7 xs8 xs9 (Z_to_bv 64 0) xs11' xt3 xt4 xt5 xt6)
                       xF (Z_to_bv 64 OD_PLUS) xfc None m' (seg_rom usegs))) ->
    evt usegs Q (MS (mkR xra (Z_to_bv 64 (FR E)) (o_gp E) (o_tp E) xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 0) xa1 xa2 xa3 xa4 xa5 xa6 xa7
                         (Z_to_bv 64 0) xs3 (Z_to_bv 64 (o_act E)) xs5 (Z_to_bv 64 0) xs7 xs8 xs9 (Z_to_bv 64 0) xs11 xt3 xt4 xt5 xt6)
                    xF (Z_to_bv 64 OD_DISP) xfc None m1 (seg_rom usegs)).
  Proof using OK.
    intros Q st v144 v176 v184 v200 v208 v216 xra xt0 xt1 xt2 xs0 xs1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs5 xs7 xs8 xs9 xs11 xt3 xt4 xt5 xt6 xF xfc m1 FRM INV HK.
    pose proof INV as INV0. od_env OK. unfold OD_DISP, OD_PLUS in *. od_open_inv INV.
    assert (C : (o_act E = 0 \/ o_act E = 1 \/ o_act E = 2 \/ o_act E = 3 \/ o_act E = 4 \/ o_act E = 5 \/ o_act E = 6 \/ o_act E = 7
                 \/ o_act E = 8 \/ o_act E = 9 \/ o_act E = 10 \/ o_act E = 11 \/ o_act E = 12)%Z) by lia.
    destruct C as [C|[C|[C|[C|[C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]]]]]]; rewrite C in *.
    all: zstep; zstep; first [ if_true | if_false ].

    13: (eapply evt_eq; [| eapply (HK _ _ _ _ m1 INV0)]; try rewrite C; od_st_eq).
    all: do 7 zstep.

    11: (eapply evt_eq; [| eapply (HK _ _ _ _ m1 INV0)]; try rewrite C; od_st_eq).

    11: {
          zstep. if_true. zstep. zstep. zstep. zstep. zstep. zstep. lstep.

          zstep. if_true. zstep. zstep. zstep. if_true.
          zstep. if_true. zstep. zstep. zstep. if_false. zstep.
          od_forget FR168.
          eapply evt_eq; [| eapply (HK _ _ _ _ _); od_close_inv]. try rewrite C. od_st_eq. }

    all: zstep; if_true; (eapply evt_eq; [| eapply (HK _ _ _ _ m1 INV0)]; try rewrite C; od_st_eq).
  Qed.

  Hypothesis ARM_STR  : arm_stmt E 0x27ab4.
  Hypothesis ARM_BOOL : arm_stmt E 0x27af4.
  Hypothesis ARM_ARR  : arm_stmt E 0x27884.
  Hypothesis ARM_I64  : arm_stmt E 0x27a74.
  Hypothesis ARM_DBL  : arm_stmt E 0x279b0.
  Hypothesis ARM_OBJ  : arm_stmt E 0x27a00.
  Hypothesis ARM_U64  : arm_stmt E 0x27b34.
  Hypothesis ARM_RAW  : arm_stmt E 0x27b74.
  Hypothesis ARM_NULL : arm_stmt E 0x27bb4.
  Hypothesis ARM_NEST : arm_stmt E 0x2793c.

  Lemma od_disp_item : forall (Q : machine_state -> Prop) st xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs11 xt3 xt4 xt5 xt6 xF xfc m1,
    od_head_ok bs idxs 1 st -> frm0 xfc -> ODINV E st m1 ->
    od_plus_k E Q st ->
    evt usegs Q (ODST E OD_DISP xra xt0 xt1 xt2 (Z_to_bv 64 1) xa1 xa2 xa3 xa4 xa5 xa6 xa7
                      (Z_to_bv 64 2) (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) xs11 xt3 xt4 xt5 xt6 xF xfc m1).
  Proof using OK HLAST ARM_STR ARM_BOOL ARM_ARR ARM_I64 ARM_DBL ARM_OBJ ARM_U64 ARM_RAW ARM_NULL ARM_NEST.
    intros Q st xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs11 xt3 xt4 xt5 xt6 xF xfc m1 HH FRM INV HK.
    pose proof INV as INV0. od_open_inv INV. od_env OK. unfold OD_DISP.
    pose proof HK as HK0. unfold od_plus_k, OD_PLUS in HK0.
    assert (NONE : od_arm_out bs idxs st st) by (apply (acc_arm_out bs idxs st st S1 HLAST HH); apply acc_none).
    assert (C : (o_act E = 0 \/ o_act E = 1 \/ o_act E = 2 \/ o_act E = 3 \/ o_act E = 4 \/ o_act E = 5 \/ o_act E = 6 \/ o_act E = 7
                 \/ o_act E = 8 \/ o_act E = 9 \/ o_act E = 10 \/ o_act E = 11 \/ o_act E = 12)%Z) by lia.
    destruct C as [C|[C|[C|[C|[C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]]]]]]; rewrite C in *.
    all: zstep; zstep; first [ if_true | if_false ].
    13: { eapply evt_eq; [| eapply (HK0 st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ NONE FRM INV0)]. od_st_eq. }
    all: do 7 zstep.
    11: { eapply evt_eq; [| eapply (HK0 st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ NONE FRM INV0)]. od_st_eq. }
    - eapply evt_eq; [| eapply (ARM_STR Q st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 HLAST HH FRM INV0 HK)]. rewrite C. od_st_eq.
    - eapply evt_eq; [| eapply (ARM_BOOL Q st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 HLAST HH FRM INV0 HK)]. rewrite C. od_st_eq.
    - eapply evt_eq; [| eapply (ARM_ARR Q st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 HLAST HH FRM INV0 HK)]. rewrite C. od_st_eq.
    - eapply evt_eq; [| eapply (ARM_I64 Q st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 HLAST HH FRM INV0 HK)]. rewrite C. od_st_eq.
    - eapply evt_eq; [| eapply (ARM_DBL Q st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 HLAST HH FRM INV0 HK)]. rewrite C. od_st_eq.
    - eapply evt_eq; [| eapply (ARM_OBJ Q st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 HLAST HH FRM INV0 HK)]. rewrite C. od_st_eq.
    - eapply evt_eq; [| eapply (ARM_U64 Q st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 HLAST HH FRM INV0 HK)]. rewrite C. od_st_eq.
    - eapply evt_eq; [| eapply (ARM_RAW Q st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 HLAST HH FRM INV0 HK)]. rewrite C. od_st_eq.
    - eapply evt_eq; [| eapply (ARM_NULL Q st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 HLAST HH FRM INV0 HK)]. rewrite C. od_st_eq.
    - eapply evt_eq; [| eapply (ARM_ARR Q st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 HLAST HH FRM INV0 HK)]. rewrite C. od_st_eq.
    - eapply evt_eq; [| eapply (ARM_NEST Q st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 HLAST HH FRM INV0 HK)]. rewrite C. od_st_eq.
  Qed.

  Lemma od_head_exit : forall (Q : machine_state -> Prop) st v216 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1,
    (0 <= o_depth st < 1)%Z -> frm0 xfc -> ODINVv E v216 st m1 ->
    od_exit_k E Q ->
    evt usegs Q (ODST E OD_HEAD xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 1) (Z_to_bv 64 1) xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1).
  Proof using OK.
    intros Q st v216 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1 CD FRM INV KX.
    pose proof INV as INV0. od_env OK. unfold OD_HEAD.
    pose proof KX as KX0. unfold od_exit_k, OD_EXIT in KX0.
    od_open_inv INV.

    zstep. if_cases K0; zify_cond K0; try (exfalso; lia). clear K0.
    zstep. odnorm. zstep.
    if_cases K; zify_cond K; odsig K; try (exfalso; lia). clear K.
    zstep.
    eapply evt_eq; [| eapply (KX0 st 0%Z 2%Z 1%Z (o_IDX E) 1%Z v216); [exact FRM| exact INV0]]. od_st_eq.
  Qed.

  Theorem od_head : forall (Q : machine_state -> Prop) st0 st v216 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1,
    od_head_pre E st0 st -> frm0 xfc -> ODINVv E v216 st m1 ->
    od_exit_k E Q -> od_plus_k E Q st ->
    evt usegs Q (ODST E OD_HEAD xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 1) (Z_to_bv 64 1) xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1).
  Proof using OK OKU HLAST ARM_STR ARM_BOOL ARM_ARR ARM_I64 ARM_DBL ARM_OBJ ARM_U64 ARM_RAW ARM_NULL ARM_NEST.
    intros Q st0 st v216 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1 PRE FRM INV KX HK.
    pose proof INV as INV0. od_env OK. od_envu OKU. unfold OD_HEAD.

    assert (CASES : (0 <= o_depth st < 1)%Z
                    \/ (od_head_ok bs idxs 1 st)
                    \/ (o_err st = 3%Z /\ (1 <= o_depth st <= o_pos st + 3)%Z /\ o_alive st = true /\ (o_pos st <= n + 1)%Z /\ (0 <= o_sbo st)%Z)).
    { destruct PRE as [(A1 & A2 & A3 & A4 & A5)|(DA & DD & DE & DS)].
      - destruct A5 as [(B1 & B2)|[(B1 & B2 & B3)|B]].
        + right; right. unfold TAPE_ERROR in B1. destruct A3 as [A3 _]. repeat split; try assumption; try lia.
        + left. lia.
        + right; left. exact B.
      - left. unfold TAPE_ERROR in DE. lia. }
    destruct CASES as [CD|[HH|(CE & CD & CA & CP & CS)]].
    -
      eapply evt_eq; [| eapply (od_head_exit Q st v216); [exact CD| exact FRM| exact INV0| exact KX]]. unfold OD_HEAD. od_st_eq.
    -
      pose proof HH as (HP & HD & HE & HA & HB).
      assert (HD2 : o_depth st = 2%Z) by lia.
      od_open_inv INV. rewrite HD2 in ITER.

      zstep. if_cases K0; zify_cond K0; try (exfalso; lia). clear K0.
      zstep. odnorm. zstep. if_true.
      zstep. zstep. if_false.
      zstep. odnorm. zstep. zstep. uok. zstep.
      if_cases K; zify_cond K; try (exfalso; lia). clear K.

      zstep. zstep. uok. zstep. odnorm. zstep. zstep. zstep. ultb. zstep. zstep. zstep. if_true.

      zstep. lstep. zstep. zstep. zstep.
      eapply evt_eq; [| eapply (od_disp_item Q st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HH FRM); [| exact HK]]; [unfold OD_DISP; od_st_eq|].
      od_close_inv.
    -
      od_open_inv INV. rewrite CA in ITER.
      zstep. if_cases K0; zify_cond K0; try (exfalso; lia). clear K0.
      zstep. odnorm. zstep.
      if_cases K; zify_cond K; odsig K; try (exfalso; lia). clear K.
      zstep. zstep. if_false.
      zstep. odnorm. zstep. zstep. uok. zstep.
      if_cases K; zify_cond K; try (exfalso; lia). clear K.

      zstep. zstep. zstep. zstep. lstep. lstep. zstep. lstep. zstep.
      od_cur_mem ltac:(fun mm => assert (INVA : ODINV E (o_abandon st) mm) by od_close_inv).
      eapply evt_eq.
      2: { eapply (od_disp_err Q (o_abandon st) 0%Z 2%Z 1%Z (o_IDX E) 1%Z 1%Z); [exact FRM| exact INVA|].
           intros xa0' xa1' xa2' xs11' m' INV'.
           pose proof HK as HK0. unfold od_plus_k, OD_PLUS in HK0.
           eapply evt_eq.
           2: { eapply (HK0 (o_abandon st)); [| exact FRM| exact INV'].
                split; [cbn [o_abandon o_pos]; lia|]. right. unfold od_dead, TAPE_ERROR. cbn [o_abandon o_alive o_depth o_err o_pos o_sbo].
                repeat split; try assumption; lia. }
           unfold OD_PLUS. od_st_eq. }
      unfold OD_DISP. od_st_eq.
  Qed.
End Head.
