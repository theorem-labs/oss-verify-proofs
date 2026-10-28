(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast MState.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjS1Out SjStage2 SjLeaves.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Sj_stage2_defs Sj_stage2_traps Sj_stage2_guard Sj_tables Sj_stage2_hooks Sj_stage2_auto.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac lia ::= s2lia.
Local Ltac tlia ::= s2tlia.
Local Ltac solve_load ::= first [ solve_load_base | s2_load_buf | s2_load_dig | solve_load_image ].
Local Ltac solve_store ::= first [ solve_store0 | s2_store_wr ].

Section Hex4.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Notation INV := (Inv (e_bs E) (e_idxs E)).

  Notation bs := (e_bs E).

  Definition hex4v (q : Z) : Z :=
    or4 (dig (420 + B bs (q + 1))) (dig (630 + B bs q)) (dig (210 + B bs (q + 2))) (dig (0 + B bs (q + 3))).

  Local Ltac hguard :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ (if ?c then Z_to_bv 64 ?a else Z_to_bv 64 ?b) _ _ _ _) =>
        lazymatch a with
        | 0x5b864%Z => let K := fresh "KG" in destruct c eqn:K; [ g_solve K | clear K ]
        end
    end.

  Lemma hex4_call : forall (Q : machine_state -> Prop) (R q : Z)
      x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    (0 <= R < 2 ^ 64)%Z -> (R mod 2 = 0)%Z ->
    bytes_at usegs m1 (e_BUF E) (padded_bytes bs) -> mem_inv usegs m1 ->
    (0 <= q /\ q + 3 < e_len E + 64)%Z ->
    (forall y10 y11 y12 y13 y14 y15 y16, y10 = Z_to_bv 64 (hex4v q) ->
       evt usegs Q (S2R E R (Z_to_bv 64 R) x5 x6 x7 x8 x9 y10 y11 y12 y13 y14 y15 y16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                        x28 x29 x30 x31 F fc m1)) ->
    evt usegs Q (S2R E 0x5b7d0 (Z_to_bv 64 R) x5 x6 x7 x8 x9 (Z_to_bv 64 (e_BUF E + q)) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                     x28 x29 x30 x31 F fc m1).
  Proof using OK.
    intros Q R q x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m1 HR0 HR1 BUFRO MI HQ K.
    pose proof (ok_bytes _ OK) as BOK.
    pose proof (B_range bs q BOK) as HB0. pose proof (B_range bs (q + 1) BOK) as HB1.
    pose proof (B_range bs (q + 2) BOK) as HB2. pose proof (B_range bs (q + 3) BOK) as HB3.
    pose proof (padded_bytes_blen bs) as PBL.
    s2_env OK.
    repeat first [ hguard | gstep ].
    rewrite (ret_pc_even R HR0 HR1).
    apply K. unfold hex4v, or4, sxu. rewrite Z.lor_assoc. reflexivity.
  Qed.
End Hex4.
