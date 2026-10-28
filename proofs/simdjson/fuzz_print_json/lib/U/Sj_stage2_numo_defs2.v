(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Sj_stage2_defs Sj_stage2_tapek Sj_stage2_numkit Sj_stage2_numo_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section NumODefs2.
  Variable E : s2env.
  Notation bs := (e_bs E).

  Definition numo_e14_k (Q : machine_state -> Prop) (s : st) (neg : Z) (v e0 x : Z) : Prop :=
    forall xra xt0 xt2 xs0 xa0 xa1 xa2 xa3 xa6 xs2 xs3 xs4 xs6 xs7 xs8 xs10 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j24 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (NSL E s neg (W s) j0 j8 j16 j24 j72) (scopes s) fc m1 ->
      evt usegs Q (S2R E 0x4b65c xra xt0 (Z_to_bv 64 (x)) xt2 xs0 (Z_to_bv 64 (e_BUF E + e_off E (k s))) xa0 xa1 xa2 xa3 (Z_to_bv 64 (e_BUF E + (e_off E (k s) + neg))) (Z_to_bv 64 (v)) xa6 (Z_to_bv 64 (e0)) xs2 xs3 xs4 (Z_to_bv 64 (e_BUF E)) xs6 xs7 xs8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))) xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).
End NumODefs2.
