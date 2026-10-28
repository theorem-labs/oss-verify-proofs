(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sj_stage2_defs Sj_stage2_tapek Sj_stage2_numkit Sj_stage2_numkitr Sj_stage2_numr_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section NumRDefs2.
  Variable E : s2env.
  Variables (CP : Z) (t : list Z).

  Definition numr_i468_k (Q : machine_state -> Prop) (c : Z) : Prop :=
    forall xra xt0 xt1 xt2 xs0 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs11 xt3 xt4 xt5 xt6 j0 j8 j16 j24 j32 j72 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      MEMI E (e_nxt0 E) (RSL E j0 j8 j16 j24 j32 j72) [] fc m1 -> bytes_at usegs m1 CP (zbytes (crs t)) ->
      evt usegs Q (S2R E 0x471b4 xra xt0 xt1 xt2 xs0 (Z_to_bv 64 (CP)) (Z_to_bv 64 (c)) (Z_to_bv 64 (83920)) xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 (e_TAPE E + 8)) xs4 xs5 xs6 xs7 xs8 xs9 (Z_to_bv 64 (e_TAPE E)) xs11 xt3 xt4 xt5 xt6 F fc m1).
End NumRDefs2.
