(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow Sj_akit Od_defsA Od_plusA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ od_load_hook | solve_load_base | solve_load_image ].

Ltac oa_forget_1 H :=
  match type of H with
  | rw_cells ?s ?m ?A (C8 ?v :: ?post) => apply (rw_cells_forget_C8 s m A [] v post) in H; cbn [app] in H
  | rw_cells ?s ?m ?A (?c0 :: C8 ?v :: ?post) => apply (rw_cells_forget_C8 s m A [c0] v post) in H; cbn [app] in H
  | rw_cells ?s ?m ?A (?c0 :: ?c1 :: C8 ?v :: ?post) => apply (rw_cells_forget_C8 s m A [c0; c1] v post) in H; cbn [app] in H
  | rw_cells ?s ?m ?A (?c0 :: ?c1 :: ?c2 :: C8 ?v :: ?post) => apply (rw_cells_forget_C8 s m A [c0; c1; c2] v post) in H; cbn [app] in H
  end.
Ltac oa_forget H := repeat (oa_forget_1 H).

Section Head.
  Variable E : oaenv.
  Hypothesis OK : od_oka E.
  Hypothesis HLAST : tokT (o_bs E) (o_idxs E) (o_n E - 1) = C_RBRACKET.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).
  Notation n := (o_n E).

  Lemma od_disp_err : forall (Q : machine_state -> Prop) st vs6 v224 v248 v304 v312 v328 v344
      xt0 xt1 xt2 xs0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs7 xs8 xs11 xt3 xt4 xt5 xt6 xF xfc m1,
    frm0 xfc -> ODINVg E vs6 v224 v248 v304 v312 v328 v344 st m1 ->
    (forall xa0' xa1' xa2' xa3' xa4' xa5' xs11' m',
       ODINVg E vs6 v224 v248 v304 v312 v328 v344 st m' ->
       evt asegs Q (MS (mkR (Z_to_bv 64 (o_act E)) (Z_to_bv 64 (oa_S1 E)) (o_gp E) (o_tp E) xt0 xt1 xt2 xs0 (Z_to_bv 64 (oa_S1 E))
                            xa0' xa1' xa2' xa3' xa4' xa5' xa6 xa7
                            (Z_to_bv 64 0) xs3 xs4 xs5 xs6 xs7 xs8 (Z_to_bv 64 0) (Z_to_bv 64 0) xs11' xt3 xt4 xt5 xt6)
                       xF (Z_to_bv 64 OD_PLUS) xfc None m' (seg_rom asegs))) ->
    evt asegs Q (MS (mkR (Z_to_bv 64 (o_act E)) (Z_to_bv 64 (oa_S1 E)) (o_gp E) (o_tp E) xt0 xt1 xt2 xs0 (Z_to_bv 64 (oa_S1 E))
                         (Z_to_bv 64 0) xa1 xa2 xa3 xa4 xa5 xa6 xa7
                         (Z_to_bv 64 0) xs3 xs4 xs5 xs6 xs7 xs8 (Z_to_bv 64 0) (Z_to_bv 64 0) xs11 xt3 xt4 xt5 xt6)
                    xF (Z_to_bv 64 OD_DISP) xfc None m1 (seg_rom asegs)).
  Proof using OK.
    intros Q st vs6 v224 v248 v304 v312 v328 v344 xt0 xt1 xt2 xs0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs7 xs8 xs11 xt3 xt4 xt5 xt6 xF xfc m1 FRM INV HK.
    pose proof INV as INV0. od_env OK. unfold OD_DISP, OD_PLUS in *. od_open_inv INV.
    assert (C : (o_act E = 0 \/ o_act E = 1 \/ o_act E = 2 \/ o_act E = 3 \/ o_act E = 4 \/ o_act E = 5 \/ o_act E = 6 \/ o_act E = 7
                 \/ o_act E = 8 \/ o_act E = 9 \/ o_act E = 10 \/ o_act E = 11 \/ o_act E = 12)%Z) by lia.
    destruct C as [C|[C|[C|[C|[C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]]]]]]; rewrite C in *.
    all: zstep; zstep; first [ if_true | if_false ].

    13: (zstep; eapply evt_eq; [| eapply (HK _ _ _ _ _ _ _ m1 INV0)]; try rewrite C; od_st_eq).
    all: do 7 zstep.

    11: (eapply evt_eq; [| eapply (HK _ _ _ _ _ _ _ m1 INV0)]; try rewrite C; od_st_eq).

    11: {
          zstep. if_true. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. lstep.

          zstep. if_true. zstep. zstep. zstep. if_true.
          zstep. if_true. zstep. zstep. zstep. if_false. zstep.
          oa_forget FR176.
          eapply evt_eq; [| eapply (HK _ _ _ _ _ _ _ _); od_close_inv]. try rewrite C. od_st_eq. }

    all: zstep; if_false; zstep; (eapply evt_eq; [| eapply (HK _ _ _ _ _ _ _ m1 INV0)]; try rewrite C; od_st_eq).
  Qed.

  Hypothesis ARM_STR   : arm_stmt E 0x973bc.
  Hypothesis ARM_BOOL  : arm_stmt E 0x9781c.
  Hypothesis ARM_ARR   : arm_stmt E 0x9779c.
  Hypothesis ARM_I64   : arm_stmt E 0x97690.
  Hypothesis ARM_OBJ   : arm_stmt E 0x97610.
  Hypothesis ARM_U64   : arm_stmt E 0x978d8.
  Hypothesis ARM_RAW   : arm_stmt E 0x979b8.
  Hypothesis ARM_NULL  : arm_stmt E 0x97b0c.
  Hypothesis ARM_BEGIN : arm_stmt E 0x97a8c.
  Hypothesis ARM_NEST  : arm_stmt E 0x97474.

  Lemma od_disp_item : forall (Q : machine_state -> Prop) st xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs11 xt3 xt4 xF xfc m1,
    od_head_ok bs idxs 1 st -> frm0 xfc -> ODINV E st m1 ->
    od_plus_k E Q st -> arm_k E Q 0x974f0 st ->
    evt asegs Q (ODST E OD_DISP (Z_to_bv 64 122) xt1 xt2 (Z_to_bv 64 1) xa1 xa2 xa3 xa4 xa5 xa6 xa7
                      (Z_to_bv 64 2) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 (oa_F E + 192)) xs11 xt3 xt4 xF xfc m1).
  Proof using OK HLAST ARM_STR ARM_BOOL ARM_ARR ARM_I64 ARM_OBJ ARM_U64 ARM_RAW ARM_NULL ARM_BEGIN ARM_NEST.
    intros Q st xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs11 xt3 xt4 xF xfc m1 HH FRM INV HK KDBL.
    pose proof INV as INV0. od_open_inv INV. od_env OK. unfold OD_DISP.
    pose proof HK as HK0. unfold od_plus_k, OD_PLUS in HK0.
    assert (NONE : od_arm_out bs idxs st st) by (apply (acc_arm_out bs idxs st st S1 HLAST HH); apply acc_none).
    assert (C : (o_act E = 0 \/ o_act E = 1 \/ o_act E = 2 \/ o_act E = 3 \/ o_act E = 4 \/ o_act E = 5 \/ o_act E = 6 \/ o_act E = 7
                 \/ o_act E = 8 \/ o_act E = 9 \/ o_act E = 10 \/ o_act E = 11 \/ o_act E = 12)%Z) by lia.
    destruct C as [C|[C|[C|[C|[C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]]]]]]; rewrite C in *.
    all: zstep; zstep; first [ if_true | if_false ].
    13: { zstep. eapply evt_eq; [| eapply (HK0 st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ NONE FRM INV0)]. od_st_eq. }
    all: do 7 zstep.
    11: { eapply evt_eq; [| eapply (HK0 st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ NONE FRM INV0)]. od_st_eq. }
    - eapply evt_eq; [| eapply (ARM_STR Q st HLAST HH HK _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 FRM INV0)]. rewrite C. od_st_eq.
    - eapply evt_eq; [| eapply (ARM_BOOL Q st HLAST HH HK _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 FRM INV0)]. rewrite C. od_st_eq.
    - eapply evt_eq; [| eapply (ARM_ARR Q st HLAST HH HK _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 FRM INV0)]. rewrite C. od_st_eq.
    - eapply evt_eq; [| eapply (ARM_I64 Q st HLAST HH HK _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 FRM INV0)]. rewrite C. od_st_eq.
    - eapply evt_eq; [| eapply (KDBL _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 FRM INV0)]. rewrite C. od_st_eq.
    - eapply evt_eq; [| eapply (ARM_OBJ Q st HLAST HH HK _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 FRM INV0)]. rewrite C. od_st_eq.
    - eapply evt_eq; [| eapply (ARM_U64 Q st HLAST HH HK _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 FRM INV0)]. rewrite C. od_st_eq.
    - eapply evt_eq; [| eapply (ARM_RAW Q st HLAST HH HK _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 FRM INV0)]. rewrite C. od_st_eq.
    - eapply evt_eq; [| eapply (ARM_NULL Q st HLAST HH HK _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 FRM INV0)]. rewrite C. od_st_eq.
    - eapply evt_eq; [| eapply (ARM_BEGIN Q st HLAST HH HK _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 FRM INV0)]. rewrite C. od_st_eq.
    - eapply evt_eq; [| eapply (ARM_NEST Q st HLAST HH HK _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 FRM INV0)]. rewrite C. od_st_eq.
  Qed.

  Lemma od_head_exit : forall (Q : machine_state -> Prop) st v344 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1,
    (0 <= o_depth st < 1)%Z -> frm0 xfc -> ODINVh E v344 st m1 ->
    od_exit_k E Q ->
    evt asegs Q (ODST E OD_HEAD xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1).
  Proof using OK.
    intros Q st v344 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1 CD FRM INV KX.
    pose proof INV as INV0. od_env OK. unfold OD_HEAD.
    pose proof KX as KX0. unfold od_exit_k, OD_EXIT in KX0.
    od_open_inv INV.

    ostep. if_false. ostep. ostep. if_true. ostep. odnorm. ostep.
    if_cases K; zify_cond K; odsig K; [exfalso; lia|]. clear K.
    ostep.
    eapply evt_eq; [| eapply (KX0 st (oa_F E + 192)%Z 0%Z 2%Z 1%Z 1%Z 1%Z v344); [exact FRM| exact INV0]]. od_st_eq.
  Qed.

  Theorem od_head : forall (Q : machine_state -> Prop) st0 st v344 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1,
    od_head_pre E st0 st -> frm0 xfc -> ODINVh E v344 st m1 ->
    od_exit_k E Q -> od_plus_k E Q st -> (od_head_ok bs idxs 1 st -> arm_k E Q 0x974f0 st) ->
    evt asegs Q (ODST E OD_HEAD xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1).
  Proof using OK HLAST ARM_STR ARM_BOOL ARM_ARR ARM_I64 ARM_OBJ ARM_U64 ARM_RAW ARM_NULL ARM_BEGIN ARM_NEST.
    intros Q st0 st v344 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1 PRE FRM INV KX HK KDBL.
    pose proof INV as INV0. od_env OK. unfold OD_HEAD.
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
      eapply evt_eq; [| eapply (od_head_exit Q st v344); [exact CD| exact FRM| exact INV0| exact KX]]. unfold OD_HEAD. od_st_eq.
    -
      pose proof HH as (HP & HD & HE & HA & HB).
      assert (HD2 : o_depth st = 2%Z) by lia.
      od_open_inv INV. rewrite HD2 in ITER.

      ostep. if_false. ostep. ostep. if_true. ostep. odnorm. ostep. if_true.
      ostep. ostep. if_false. ostep. ostep. ostep. if_true.
      ostep. odnorm. ostep.
      if_cases K; zify_cond K; [| exfalso; lia]. clear K.

      ostep. ostep. if_true. ostep. ostep. ostep. ostep. lstep. ostep. ostep. if_true. ostep. ostep. ostep.
      eapply evt_eq; [| eapply (od_disp_item Q st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HH FRM); [| exact HK| exact (KDBL HH)]]; [unfold OD_DISP; od_st_eq|].
      od_close_inv.
    -
      od_open_inv INV. rewrite CA in ITER.
      ostep. if_false. ostep. ostep. if_true. ostep. odnorm. ostep.
      if_cases K; zify_cond K; odsig K; [| exfalso; lia]. clear K.
      ostep. ostep. if_false. ostep. ostep. ostep. if_true.
      ostep. odnorm. ostep.
      if_cases K; zify_cond K; [exfalso; lia|]. clear K.

      ostep. ostep. ostep. if_true. ostep. lstep. ostep. ostep. if_true.
      ostep. ostep. ostep. ostep. lstep. ostep. lstep. ostep.
      od_cur_mem ltac:(fun mm => assert (INVA : ODINV E (o_abandon st) mm) by od_close_inv).
      eapply evt_eq.
      2: { eapply (od_disp_err Q (o_abandon st) (oa_F E + 192)%Z 0%Z 2%Z 1%Z 1%Z 1%Z 1%Z); [exact FRM| exact INVA|].
           intros xa0' xa1' xa2' xa3' xa4' xa5' xs11' m' INV'.
           pose proof HK as HK0. unfold od_plus_k, OD_PLUS in HK0.
           eapply evt_eq.
           2: { eapply (HK0 (o_abandon st)); [| exact FRM| exact INV'].
                split; [cbn [o_abandon o_pos]; lia|]. right. unfold od_dead, TAPE_ERROR. cbn [o_abandon o_alive o_depth o_err o_pos o_sbo].
                repeat split; try assumption; lia. }
           unfold OD_PLUS. od_st_eq. }
      unfold OD_DISP. od_st_eq.
  Qed.
End Head.
