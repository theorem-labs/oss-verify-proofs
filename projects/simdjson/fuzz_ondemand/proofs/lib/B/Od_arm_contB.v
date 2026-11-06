(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Import Sj_akit Od_defsB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ od_load_hook | solve_load_base | solve_load_image ].

Section ArmCont.
  Variable E : oaenv.
  Hypothesis OK : od_oka E.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).

  Theorem od_arm_array : arm_stmt E 0x979ec.
  Proof using OK.
    unfold arm_stmt, arm_k. intros Q st HLAST HH HK xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs10 xt3 xt5 xt6 xF xfc m1 FRM INV.
    pose proof HH as (HP & HD & HE & HA & HB).
    od_open_inv INV. od_env OK.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (od_tokT_range E BOK (o_pos st)) as CR.
    pose proof (od_tokI_range E S1 (o_pos st + 1) ltac:(lia)) as TR2.
    pose proof (od_tokT_range E BOK (o_pos st + 1)) as CR2.
    pose proof (tokI_read m1 E ws (o_pos st) IDXA (conj IDXL IDXF) ltac:(lia)) as RD1.
    pose proof (tokB_read m1 E (tokI bs idxs (o_pos st)) BUFRO ltac:(lia)) as RD2.
    fold (tokT bs idxs (o_pos st)) in RD2.
    set (c := tokT bs idxs (o_pos st)) in *. set (off := tokI bs idxs (o_pos st)) in *.
    set (c2 := tokT bs idxs (o_pos st + 1)) in *. set (off2 := tokI bs idxs (o_pos st + 1)) in *.

    zstep. if_true.
    ostep. ostep. utrap. ostep. ual. ostep. if_false. ostep. ostep. ostep. ostep. ostep. if_true. ostep.
    zstep. if_false. ostep.

    ostep. ostep. ostep. ostep. ostep. if_true. ostep. odnorm. ostep. uok. ostep. if_true.
    ostep. ostep. ostep. ostep. if_true. ostep. uok. ostep. ual. ostep. if_true.
    ostep. ostep. ostep. ostep. ostep. if_true. ostep. odnorm. ostep. ostep. uok.
    ostep. ostep. ostep. unz. ostep. if_true. ostep. uok.
    ostep. ostep. ostep. ostep. if_true. ostep. odnorm. ostep. zstep.
    if_cases K; zify_cond K.
    -
      ostep. ostep. uok. ostep. ostep. uok. ostep. ostep. if_true. ostep. ostep.
      od_cur_mem ltac:(fun mm =>
        pose proof (tokI_read mm E ws (o_pos st + 1) ltac:(eassumption) (conj IDXL IDXF) ltac:(lia)) as RD3;
        pose proof (tokB_read mm E off2 ltac:(eassumption) ltac:(lia)) as RD4).
      change (B (o_bs E) off2) with c2 in RD4.

      ostep. uok. ostep. ostep. uok. ostep. ostep. if_true.
      ostep. ostep. ostep. ostep. ostep. if_true.
      ostep. odnorm. ostep. uok. ostep. if_true.
      ostep. ostep. ostep. ostep. if_true.
      ostep. ual. ostep. if_true.
      ostep. ostep. ostep. ostep. ostep. if_true.
      ostep. odnorm. ostep. ostep. uok.
      ostep. ostep. ostep. unz. ostep. if_true. ostep. uok.
      ostep. ostep. ostep. ostep. if_true. ostep. odnorm. ostep. zstep.
      if_cases K2; zify_cond K2.
      +
        ostep. uok. ostep. uok. ostep. ostep. uok. ostep. ostep. if_true. ostep. ostep.
        ostep. ostep. if_true. ostep. ostep. ostep. ostep. if_true. ostep.
        eapply (HK (o_setd (o_adv st 2) 1)); [| exact FRM| od_close_inv].
        apply (acc_arm_out bs idxs st _ S1 HLAST HH).
        replace (o_setd (o_adv st 2) 1) with (fst (start_array bs idxs 1 st)); [apply acc_array|].
        unfold start_array. fold c c2.
        replace (c =? C_LBRACKET)%Z with true by (symmetry; apply Z.eqb_eq; unfold C_LBRACKET; lia).
        replace (c2 =? C_RBRACKET)%Z with true by (symmetry; apply Z.eqb_eq; unfold C_RBRACKET; lia). reflexivity.
      +
        ostep. ostep. ostep. if_true. ostep. ostep. if_true. ostep. ostep. if_true. ostep. ostep. if_true. ostep.
        eapply (HK (o_setd (o_adv st 1) 3)); [| exact FRM| od_close_inv].
        apply (acc_arm_out bs idxs st _ S1 HLAST HH).
        replace (o_setd (o_adv st 1) 3) with (fst (start_array bs idxs 1 st)); [apply acc_array|].
        unfold start_array. fold c c2.
        replace (c =? C_LBRACKET)%Z with true by (symmetry; apply Z.eqb_eq; unfold C_LBRACKET; lia).
        replace (c2 =? C_RBRACKET)%Z with false by (symmetry; apply Z.eqb_neq; unfold C_RBRACKET; lia). reflexivity.
    -
      zstep.
      eapply (HK st); [| exact FRM| od_close_inv].
      apply (acc_arm_out bs idxs st _ S1 HLAST HH).
      replace st with (fst (start_array bs idxs 1 st)) at 2; [apply acc_array|].
      unfold start_array. fold c. replace (c =? C_LBRACKET)%Z with false by (symmetry; apply Z.eqb_neq; unfold C_LBRACKET; lia). reflexivity.
  Qed.
  Theorem od_arm_begin : arm_stmt E 0x97c60.
  Proof using OK.
    unfold arm_stmt, arm_k. intros Q st HLAST HH HK xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs10 xt3 xt5 xt6 xF xfc m1 FRM INV.
    pose proof HH as (HP & HD & HE & HA & HB).
    od_open_inv INV. od_env OK.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (od_tokT_range E BOK (o_pos st)) as CR.
    pose proof (od_tokI_range E S1 (o_pos st + 1) ltac:(lia)) as TR2.
    pose proof (od_tokT_range E BOK (o_pos st + 1)) as CR2.
    pose proof (tokI_read m1 E ws (o_pos st) IDXA (conj IDXL IDXF) ltac:(lia)) as RD1.
    pose proof (tokB_read m1 E (tokI bs idxs (o_pos st)) BUFRO ltac:(lia)) as RD2.
    fold (tokT bs idxs (o_pos st)) in RD2.
    set (c := tokT bs idxs (o_pos st)) in *. set (off := tokI bs idxs (o_pos st)) in *.
    set (c2 := tokT bs idxs (o_pos st + 1)) in *. set (off2 := tokI bs idxs (o_pos st + 1)) in *.

    zstep. if_true.
    ostep. ostep. uok. ostep. ual. ostep. if_true. ostep. ostep. ostep. ostep. ostep. if_true. ostep.
    zstep. if_false. ostep.

    ostep. ostep. ostep. ostep. ostep. if_true. ostep. odnorm. ostep. uok. ostep. if_true.
    ostep. ostep. ostep. ostep. if_true. ostep. uok. ostep. ual. ostep. if_true.
    ostep. ostep. ostep. ostep. ostep. if_true. ostep. odnorm. ostep. ostep. uok.
    ostep. ostep. ostep. unz. ostep. if_true. ostep. uok.
    ostep. ostep. ostep. ostep. if_true. ostep. odnorm. ostep. zstep.
    if_cases K; zify_cond K.
    -
      ostep. ostep. uok. ostep. ostep. uok. ostep. ostep. if_true. ostep. ostep.
      od_cur_mem ltac:(fun mm =>
        pose proof (tokI_read mm E ws (o_pos st + 1) ltac:(eassumption) (conj IDXL IDXF) ltac:(lia)) as RD3;
        pose proof (tokB_read mm E off2 ltac:(eassumption) ltac:(lia)) as RD4).
      change (B (o_bs E) off2) with c2 in RD4.

      ostep. uok. ostep. ostep. uok. ostep. ostep. if_true.
      ostep. ostep. ostep. ostep. ostep. if_true.
      ostep. odnorm. ostep. uok. ostep. if_true.
      ostep. ostep. ostep. ostep. if_true.
      ostep. ual. ostep. if_true.
      ostep. ostep. ostep. ostep. ostep. if_true.
      ostep. odnorm. ostep. ostep. uok.
      ostep. ostep. ostep. unz. ostep. if_true. ostep. uok.
      ostep. ostep. ostep. ostep. if_true. ostep. odnorm. ostep. zstep.
      if_cases K2; zify_cond K2.
      +
        ostep. uok. ostep. uok. ostep. ostep. uok. ostep. ostep. if_true. ostep. ostep.
        ostep. ostep. if_true. ostep. ostep. ostep. ostep. if_false. ostep.
        eapply (HK (o_setd (o_adv st 2) 1)); [| exact FRM| od_close_inv].
        apply (acc_arm_out bs idxs st _ S1 HLAST HH).
        replace (o_setd (o_adv st 2) 1) with (fst (start_array bs idxs 1 st)); [apply acc_array|].
        unfold start_array. fold c c2.
        replace (c =? C_LBRACKET)%Z with true by (symmetry; apply Z.eqb_eq; unfold C_LBRACKET; lia).
        replace (c2 =? C_RBRACKET)%Z with true by (symmetry; apply Z.eqb_eq; unfold C_RBRACKET; lia). reflexivity.
      +
        ostep. ostep. ostep. if_true. ostep. ostep. if_true. ostep. ostep. if_true. ostep. ostep. if_false. ostep.
        eapply (HK (o_setd (o_adv st 1) 3)); [| exact FRM| od_close_inv].
        apply (acc_arm_out bs idxs st _ S1 HLAST HH).
        replace (o_setd (o_adv st 1) 3) with (fst (start_array bs idxs 1 st)); [apply acc_array|].
        unfold start_array. fold c c2.
        replace (c =? C_LBRACKET)%Z with true by (symmetry; apply Z.eqb_eq; unfold C_LBRACKET; lia).
        replace (c2 =? C_RBRACKET)%Z with false by (symmetry; apply Z.eqb_neq; unfold C_RBRACKET; lia). reflexivity.
    -
      zstep.
      eapply (HK st); [| exact FRM| od_close_inv].
      apply (acc_arm_out bs idxs st _ S1 HLAST HH).
      replace st with (fst (start_array bs idxs 1 st)) at 2; [apply acc_array|].
      unfold start_array. fold c. replace (c =? C_LBRACKET)%Z with false by (symmetry; apply Z.eqb_neq; unfold C_LBRACKET; lia). reflexivity.
  Qed.
  Theorem od_arm_object : arm_stmt E 0x97894.
  Proof using OK.
    unfold arm_stmt, arm_k. intros Q st HLAST HH HK xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs10 xt3 xt5 xt6 xF xfc m1 FRM INV.
    pose proof HH as (HP & HD & HE & HA & HB).
    od_open_inv INV. od_env OK.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (od_tokT_range E BOK (o_pos st)) as CR.
    pose proof (od_tokI_range E S1 (o_pos st + 1) ltac:(lia)) as TR2.
    pose proof (od_tokT_range E BOK (o_pos st + 1)) as CR2.
    pose proof (tokI_read m1 E ws (o_pos st) IDXA (conj IDXL IDXF) ltac:(lia)) as RD1.
    pose proof (tokB_read m1 E (tokI bs idxs (o_pos st)) BUFRO ltac:(lia)) as RD2.
    fold (tokT bs idxs (o_pos st)) in RD2.
    set (c := tokT bs idxs (o_pos st)) in *. set (off := tokI bs idxs (o_pos st)) in *.
    set (c2 := tokT bs idxs (o_pos st + 1)) in *. set (off2 := tokI bs idxs (o_pos st + 1)) in *.

    zstep. if_true.
    ostep. ostep. utrap. ostep. ual. ostep. if_false. ostep. ostep. ostep. ostep. ostep. if_true. ostep.
    zstep. if_true.

    ostep. ostep. ostep. ostep. ostep. if_true. ostep. odnorm. ostep. uok. ostep. if_true. ostep. ostep. ostep. ostep. if_true. ostep. uok. ostep. ual. ostep. if_true.
    ostep. ostep. ostep. ostep. ostep. if_true. ostep. odnorm. ostep. ostep. uok. ostep. ostep. ostep. unz. ostep. if_true. ostep. uok.
    ostep. ostep. ostep. ostep. if_true. ostep. odnorm. ostep. zstep.
    if_cases K; zify_cond K.
    -
      ostep. ostep. uok. ostep. ostep. uok. ostep. ostep. if_true. ostep. ostep.
      od_cur_mem ltac:(fun mm =>
        pose proof (tokI_read mm E ws (o_pos st + 1) ltac:(eassumption) (conj IDXL IDXF) ltac:(lia)) as RD3;
        pose proof (tokB_read mm E off2 ltac:(eassumption) ltac:(lia)) as RD4).
      change (B (o_bs E) off2) with c2 in RD4.
      ostep. uok. ostep. ostep. uok. ostep. ostep. if_true. ostep. ostep. ostep. ostep. ostep. if_true. ostep. odnorm. ostep. uok. ostep. if_true.
      ostep. ostep. ostep. ostep. if_true. ostep. ual. ostep. if_true. ostep. ostep. ostep. ostep. ostep. if_true. ostep. odnorm. ostep. ostep. uok.
      ostep. ostep. ostep. unz. ostep. if_true. ostep. uok. ostep. ostep. ostep. ostep. if_true. ostep. odnorm. ostep. zstep.
      if_cases K2; zify_cond K2.
      +
        ostep. uok. ostep. uok. ostep. ostep. uok. ostep. ostep. if_true. ostep. ostep.
        ostep. ostep. if_true. ostep. ostep. if_true. ostep. ostep. ostep.
        eapply (HK (o_setd (o_adv st 2) 1)); [| exact FRM| od_close_inv].
        apply (acc_arm_out bs idxs st _ S1 HLAST HH).
        replace (o_setd (o_adv st 2) 1) with (start_object bs idxs 1 st); [apply acc_object|].
        unfold start_object. fold c c2.
        replace (c =? C_LBRACE)%Z with true by (symmetry; apply Z.eqb_eq; unfold C_LBRACE; lia).
        replace (c2 =? C_RBRACE)%Z with true by (symmetry; apply Z.eqb_eq; unfold C_RBRACE; lia). reflexivity.
      +
        zstep.
        eapply (HK (o_adv st 1)); [| exact FRM| od_close_inv].
        apply (acc_arm_out bs idxs st _ S1 HLAST HH).
        replace (o_adv st 1) with (start_object bs idxs 1 st); [apply acc_object|].
        unfold start_object. fold c c2.
        replace (c =? C_LBRACE)%Z with true by (symmetry; apply Z.eqb_eq; unfold C_LBRACE; lia).
        replace (c2 =? C_RBRACE)%Z with false by (symmetry; apply Z.eqb_neq; unfold C_RBRACE; lia). reflexivity.
    -
      zstep.
      eapply (HK st); [| exact FRM| od_close_inv].
      apply (acc_arm_out bs idxs st _ S1 HLAST HH).
      replace st with (start_object bs idxs 1 st) at 2; [apply acc_object|].
      unfold start_object. fold c. replace (c =? C_LBRACE)%Z with false by (symmetry; apply Z.eqb_neq; unfold C_LBRACE; lia). reflexivity.
  Qed.
End ArmCont.
