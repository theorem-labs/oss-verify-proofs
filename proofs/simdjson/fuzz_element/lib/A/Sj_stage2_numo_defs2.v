(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast FP ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_akit Sj_stage2_defs Sj_stage2_tapek Sj_stage2_numkit Sj_stage2_numo_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Definition numo_cmpslow_k (E : s2env) (Q : machine_state -> Prop) (s : st) (neg e : Z) : Prop :=
  forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs6 xs7 xs9 xs11 xt3 xt4 xt5 xt6
         j64 j72 j80 j96 j104 j112 j120 j128 j136 j144 j272 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j64; CB 8 j72; CB 8 j80; C8 (Z_to_bv 64 (e_BUF E + e_off E (k s))); CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); C8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))); C8 (Z_to_bv 64 (e_TAPE E + 8 * W s)); C8 (Z_to_bv 64 (e_SBUF E + sb s)); CB 8 j272]
         (scopes s) fc m1 ->
    evt asegs Q (S2R E 0xc3670 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 xa1 xa2 xa3 (Z_to_bv 64 (e)) xa5 xa6 xa7 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (depth s)) xs6 xs7 (Z_to_bv 64 (e_BUF E)) xs9 (Z_to_bv 64 (e_THIS E + 56)) xs11 xt3 xt4 xt5 xt6 F fc m1).

