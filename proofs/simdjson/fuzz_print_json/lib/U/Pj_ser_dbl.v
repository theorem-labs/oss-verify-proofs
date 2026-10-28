(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel PjModel Target Prog PjImpl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjS1Out SjAlloc SjTape SjTapeList SjTapeTile SjPjSer.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_h_kit F_memcpy F_memmove_t2.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Pj_defs Pj_kit Pj_copy Pj_grow Pj_ser_defs Pj_ser_kit Pj_ser_calls Pj_num_defs Pj_itoa Pj_ser_ncalls.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Pj_tochars_cl.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_store ::= first [ pj_solve_store0 | pj_store_wr ].
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.
  Hypothesis HTC : tochars_stmt.

  Theorem dbl_proof : dbl_stmt.
  Proof.
    unfold dbl_stmt.
    intros E Q e64 e72 e80 spill isobj st s m F fc i dp A xs3 xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 OK HSM FRM I1 I2 ACC BUD HK.
    ser_env OK.
    pose proof OK as [_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ [D8 T8]].
    pose proof (ser_ranges _ _ _ _ _ _ _ _ _ OK HSM) as (TP0 & TP1 & _ & _).
    ser_open HSM OK.
    pose proof (doc_cells_mu E _ _ _ _ OK HREF MU WM) as DOCC.
    pose proof (tape_read_mu E _ _ _ _ (i + 1) OK HREF MU WM ltac:(lia)) as RD.

    zstep. step. step. step.
    eapply tape_ref_call; [exact DOCC| exact T8| lia| lia| lia| lia| reflexivity|].

    step. zstep. step. step.
    clear RD DOCC.
    ser_close HSM1 OK.
    eapply (ser_tochars E Q e64 e72 e80 spill isobj st s) with (rpc := 0x3ec48); [exact HTC| exact OK| exact HSM1| exact FRM| lia| reflexivity|].
    intros m2 n F2 fc2 yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM2 FRM2 HN.
    eapply (num_tail HM HF E Q e64 e72 e80 spill isobj st s m2 F2 fc2 (i + 1) dp A 27 n); try eassumption; lia.
  Qed.
End Proofs.

Theorem dbl_closed : rmalloc_stmt -> rfree_stmt -> dbl_stmt.
Proof. intros HM HF. exact (dbl_proof HM HF Pj_tochars_cl.tochars_proof). Qed.

End WithCeiling0.
