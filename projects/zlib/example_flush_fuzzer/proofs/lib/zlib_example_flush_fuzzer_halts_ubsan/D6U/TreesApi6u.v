(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import
  SymEx2Expr SymEx2 SymEx2Tac MemRel DSLayout BitsLib BuildTreeLib TreesRod.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees TreeModel SendModel GenBitlenModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U Require Import Segs6u DS6u TreesRod6u Callee6u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

End FXG.
Abbreviation BR6u := (BR s6u_segs 180992 181024 181056).
Abbreviation BRx6u := (BRx s6u_segs 180992 181024 181056).
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Definition call_frame (F : franges) (mem : word -> option byte) (S PB PBL sp K : Z) : Prop :=
  K <= sp <= 2 ^ 63 /\ sub_franges F (sp - K) K /\ mapped mem (sp - K) K
  /\ (S + dsl_SIZE <= sp - K \/ sp <= S) /\ (PB + PBL <= sp - K \/ sp <= PB).


Definition BT_CLOB : list reg := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.
Definition BT_FRAME : Z := 272.
Definition A6U_BUILD_TREE : Z := 0x1ca38.

Definition build_tree_run6u (SAFE : deflate_state -> tree_id -> Prop) : Prop :=
  forall (F : franges) (mem0 mem : word -> option byte) (S : Z) (p : ds_ptrs) (PBL : Z)
         (ds : deflate_state) (ra : word) (sp : Z) (t : tree_id) (regs : bvmap 5 word),
    BRH F S p PBL -> sub_franges F S dsl_SIZE -> ret_ok ra -> S mod 8 = 0 ->
    BR6u F mem0 S p PBL mem ds -> trees_rod_clear6u mem -> SAFE ds t ->
    call_frame F mem S (p_pending_buf p) PBL sp BT_FRAME ->
    getr regs 10 = zw S -> getr regs 11 = zw (S + dsc_off t) -> getr regs 2 = zw sp -> getr regs 1 = ra ->
    exists R m',
      msteps s6u_segs (mkst regs (zw A6U_BUILD_TREE) mem s6u_rom) (mkst R ra m' s6u_rom)
      /\ BR6u F mem0 S p PBL m' (build_tree ds t)
      /\ trees_rod_clear6u m'
      /\ getr R 2 = getr regs 2
      /\ (forall r : reg, reg_in r BT_CLOB = false -> getr R r = getr regs r).
End FXG.
