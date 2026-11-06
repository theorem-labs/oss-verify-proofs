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

Section ArmRaw.
  Variable E : oaenv.
  Hypothesis OK : od_oka E.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).

  Theorem od_arm_raw : arm_stmt E 0x97bd4.
  Proof using OK.
    unfold arm_stmt, arm_k. intros Q st HLAST HH HK xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs10 xt3 xt5 xt6 xF xfc m1 FRM INV.
    pose proof HH as (HP & HD & HE & HA & HB).
    od_open_inv INV. od_env OK.

    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (od_tokT_range E BOK (o_pos st)) as CR.
    pose proof (tokI_read m1 E ws (o_pos st) IDXA (conj IDXL IDXF) ltac:(lia)) as RD1.
    pose proof (tokB_read m1 E (tokI bs idxs (o_pos st)) BUFRO ltac:(lia)) as RD2.
    fold (tokT bs idxs (o_pos st)) in RD2. set (c := tokT bs idxs (o_pos st)) in *. set (off := tokI bs idxs (o_pos st)) in *.

    zstep. if_true.

    ostep. uok. ostep. ual. ostep. if_true.
    ostep. ostep. ostep. ostep. ostep. ostep. if_true. ostep.
    zstep. if_false. ostep.

    ostep. ochk. ostep. odnorm. ostep. uok. ostep. if_true.
    ochk. ostep. uok. ostep. ual. ostep. if_true.

    ostep. ostep. ostep. ostep. ostep. if_true.
    ostep. odnorm. ostep. ostep. uok.
    ostep. ostep. ostep. unz. ostep. if_true. ostep. uok.

    ochk. ostep. odnorm. ostep. zstep.
    if_cases K; zify_cond K.
    -
      ostep. zstep. if_false.
      ostep. ochk. ostep. odnorm. ostep. uok. ostep. if_true.
      ochk. ostep. ostep. uok. ostep. ostep. if_true.
      ostep. ostep. ostep. ual. ostep.

      od_cur_mem ltac:(fun mm => pose proof (tokI_read mm E ws (o_pos st) ltac:(eassumption) (conj IDXL IDXF) ltac:(lia)) as RD3).
      fold off in RD3.
      ostep. if_true. ochk. ostep. odnorm. ostep. ostep. uok.
      ostep. ostep. ostep. unz. ostep. if_true.
      ostep. ostep. if_true. ostep. ostep. if_true.
      ostep. ostep. ostep. zstep. utrap. zstep.
      eapply (HK (consume 1 st)); [| exact FRM| od_close_inv].
      apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_scalar.
    -
      zstep.
      eapply (HK st); [| exact FRM| od_close_inv].
      apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_none.
  Qed.
End ArmRaw.
