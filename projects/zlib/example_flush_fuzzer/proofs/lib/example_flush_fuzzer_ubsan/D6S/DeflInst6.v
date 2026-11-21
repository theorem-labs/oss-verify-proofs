(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.World Require Import Src_zlib_example_flush_fuzzer_repro.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux DSLayout ZSLayout RomRead TreesRod FillWinMem TreeMem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate HarnessKit BoundArith RefFlushBlk11 FB6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Import Segs6 DS6 Callee6 CalleeKits6 Memset6_run TreesRod6 TreesApi6 DeflBlkApi6 DeflSlow6_1 DeflSlow6_M DeflSlow6_11
  TrFlushBits6 TrStored6 TFB6_14 Defl6Api Defl6_M Defl6_7.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.


Definition zcall_of (d : list Z) (c : czs) : ZCall := fst (cz_call c (arr_of_list d)).
Definition dsc (d : list Z) (st : deflate_state) (c : czs) : deflate_state := set_strm st (cstrm_of_call (zcall_of d c)).





Definition SSAFE6 (ds : deflate_state) (f : Z) : Prop := DWF ds /\ slow_safe6 FB6 ds f.
Definition DSAFE6 (ds : deflate_state) (f : Z) : Prop := DWF ds /\ dsafe6 SSAFE6 ds f.


Lemma tr_flush_block_run6_FB6 : tr_flush_block_run6 FB6.
Proof.
  unfold tr_flush_block_run6.
  intros F mem0 mem S p PBL ds ra regs sp buf bufp len last MS MC HL HFS Hret HB HBI HRC HS.
  exact (tr_flush_block_run6_ok F mem0 mem S p PBL ds ra regs sp buf bufp len last MS MC HL HFS Hret HB HBI HRC (proj1 HS)).
Qed.

Theorem deflate_run6_S6 : deflate_run6 ROM6 DSAFE6.
Proof.
  pose proof (deflate_run6_ok ROM6 SSAFE6 memcpy_run6_ok tr_flush_bits_run6_ok
                (deflate_slow_run6_ok ROM6 FB6 memcpy_run6_ok memset_run6_ok adler32_run6_ok tr_flush_bits_run6_ok tr_flush_block_run6_FB6 rom_local6_ok)
                rom_local6_ok memset_run6_ok tr_stored_block_run6_ok) as H.
  exact H.
Qed.
End FXG.
