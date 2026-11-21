(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import
  SymEx2Expr SymEx2 SymEx2Tac MemRel DSLayout ZSLayout RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import
  ZIface DeflateState Trees DeflateLz DeflateBlk Deflate.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Import DeflBlkApi6 Defl6Api.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U Require Import Segs6u DS6u Callee6u TreesRod6u DeflBlkApi6u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Definition DEFL_FR6u : Z := 64.
Definition DEFL_K6u : Z := 528.
Definition A6U_DEFLATE : Z := 0x16f84.

Definition adler32_null_run6u : Prop :=
  forall (mem : word -> option byte) (regs : bvmap 5 word) (usp : Z) (ra : word),
    ADLER_FR6U <= usp -> usp < 2 ^ 63 -> mapped mem (usp - ADLER_FR6U) ADLER_FR6U ->
    ret_ok ra ->
    reg_get regs 1 = ra -> reg_get regs 2 = zw usp -> reg_get regs 11 = zw 0 -> reg_get regs 12 = zw 0 ->
    exists regs' mem',
      msteps s6u_segs (mkst regs (zw A6U_ADLER32) mem s6u_rom) (mkst regs' ra mem' s6u_rom)
      /\ reg_get regs' 10 = zw 1
      /\ reg_get regs' 2 = zw usp
      /\ (forall r : reg, reg_in r c_clob = false -> getr regs' r = getr regs r)
      /\ agree_out [(usp - ADLER_FR6U, ADLER_FR6U)] mem mem'
      /\ (forall x, mem x <> None -> mem' x <> None).

Definition deflate_run6u (ROM : (word -> option byte) -> Prop) (SAFE : deflate_state -> Z -> Prop) : Prop :=
  forall (mem : word -> option byte) (S : Z) (p : ds_ptrs) (zp : zs_ptrs) (ds : deflate_state)
         (flush : Z) (ra : word) (sp : Z) (regs : bvmap 5 word),
    ZRH6u DEFL_K6u mem S sp p zp ds -> rom_clear mem 0x10000 0x2c3f8 -> DPTRS S p zp ->
    ret_ok ra -> ZR6u mem S p zp ds -> ROM mem -> SAFE ds flush ->
    getr regs 10 = zw (p_strm p) -> getr regs 11 = zw flush -> getr regs 2 = zw sp -> getr regs 1 = ra ->
    exists R m',
      msteps s6u_segs (mkst regs (zw A6U_DEFLATE) mem s6u_rom) (mkst R ra m' s6u_rom)
      /\ ZR6u m' S p zp (fst (deflate_core ds flush))
      /\ getr R 10 = zw (snd (deflate_core ds flush))
      /\ getr R 2 = zw sp
      /\ (forall r : reg, reg_in r LZ_CLOB = false -> getr R r = getr regs r)
      /\ agree_out (ZRFo DEFL_K6u S sp p zp ds (Z.of_nat (length (cs_out_rev (ds_strm (fst (deflate_core ds flush))))))) mem m'
      /\ rod6u m'
      /\ ROM m'
      /\ (forall x, mem x <> None -> m' x <> None)
      /\ lzk ds (fst (deflate_core ds flush)).
End FXG.
