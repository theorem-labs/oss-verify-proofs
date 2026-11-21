(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1 Require Import
  SymEx2Expr SymEx2 SymEx2Tac MemRel DSLayout ZSLayout RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import
  ZIface DeflateState Trees DeflateLz DeflateBlk Deflate.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.D6S Require Import Segs6 DS6 Callee6 TreesRod6 DeflBlkApi6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.

Definition DEFL_FR6 : Z := 80.
Definition DEFL_K6 : Z := 416.
Definition A6_DEFLATE : Z := 0x16c80.
Record DPTRS (S : Z) (p : ds_ptrs) (zp : zs_ptrs) : Prop := {
  dp_S : 0 < S;
  dp_strm : 0 < p_strm p;
  dp_in : 0 < zp_in zp;
  dp_za : 0 < zp_zalloc zp < 2 ^ 64;
  dp_zf : 0 < zp_zfree zp < 2 ^ 64 }.

Definition deflate_run6 (ROM : (word -> option byte) -> Prop) (SAFE : deflate_state -> Z -> Prop) : Prop :=
  forall (mem : word -> option byte) (S : Z) (p : ds_ptrs) (zp : zs_ptrs) (ds : deflate_state)
         (flush : Z) (ra : word) (sp : Z) (regs : bvmap 5 word),
    ZRH6 DEFL_K6 mem S sp p zp ds -> rom_clear mem 0x10000 0x293d8 -> DPTRS S p zp ->
    ret_ok ra -> ZR6 mem S p zp ds -> ROM mem -> SAFE ds flush ->
    getr regs 10 = zw (p_strm p) -> getr regs 11 = zw flush -> getr regs 2 = zw sp -> getr regs 1 = ra ->
    exists R m',
      msteps s6_segs (mkst regs (zw A6_DEFLATE) mem s6_rom) (mkst R ra m' s6_rom)
      /\ ZR6 m' S p zp (fst (deflate_core ds flush))
      /\ getr R 10 = zw (snd (deflate_core ds flush))
      /\ getr R 2 = zw sp
      /\ (forall r : reg, reg_in r LZ_CLOB = false -> getr R r = getr regs r)
      /\ agree_out (ZRFo DEFL_K6 S sp p zp ds (Z.of_nat (length (cs_out_rev (ds_strm (fst (deflate_core ds flush))))))) mem m'
      /\ rod6 m'
      /\ ROM m'
      /\ (forall x, mem x <> None -> m' x <> None)
      /\ lzk ds (fst (deflate_core ds flush)).
End FXG.
