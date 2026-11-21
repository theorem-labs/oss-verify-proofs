(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.World Require Import Src_zlib_example_flush_fuzzer_repro.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require Import PropExec CatExec CatSim SeqExec StoreOk Frame Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require Import ZlibStmtBase ExSmallIface MallocDefs LibMaskBits.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel MemFill SymAux.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.D6S Require Import Segs6 Callee6 Memset6_run.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.FMQ6 Require Import CallocLib6.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.

Lemma find_segment_off6 : forall a k, 0 < k -> (a + k <= 0x10000 \/ 0x5c000 <= a) -> find_segment s6_segs a k = None.
Proof.
  intros a k Hk H. unfold s6_segs, Src_zlib_example_flush_fuzzer_repro.M.loaded_segments, Src_zlib_example_flush_fuzzer_repro_loaded_segments.
  assert (SK : forall seg rest a' k', 0 < k' ->
            (a' < Z.of_N (seg_base seg) \/ Z.of_N (seg_base seg) + Z.of_N (seg_size seg) < a' + k') ->
            find_segment (seg :: rest) a' k' = find_segment rest a' k').
  { intros seg rest a' k' Hk' H'. cbn [find_segment].
    destruct (Z.leb_spec (Z.of_N (seg_base seg)) a'); destruct (Z.leb_spec (a' + k') (Z.of_N (seg_base seg) + Z.of_N (seg_size seg)));
      cbn [andb]; try reflexivity. lia. }
  rewrite 4 SK; [reflexivity | exact Hk | | exact Hk | | exact Hk | | exact Hk |];
    cbn [seg_base seg_size Src_zlib_example_flush_fuzzer_repro_segment_000 Src_zlib_example_flush_fuzzer_repro_segment_001 Src_zlib_example_flush_fuzzer_repro_segment_002 Src_zlib_example_flush_fuzzer_repro_segment_003]; lia.
Qed.

Lemma mapped_of_store_ok6 : forall mem p n, 0 <= p -> 0 <= n -> p + n <= 2 ^ 64 ->
  (p + n <= 0x10000 \/ 0x5c000 <= p) ->
  store_ok s6_segs mem (zw p) (Z.to_nat n) = true ->
  forall x : word, p <= bv_unsigned x < p + n -> mem x <> None.
Proof.
  intros mem p n Hp Hn Hpn Hoff Hsok x Hx.
  destruct (Z.eq_dec n 0) as [->|Hn0]; [lia|].
  pose proof (store_ok_all s6_segs mem (Z.to_nat n) (zw p) ltac:(rewrite u_zw_small, Z2Nat.id by lia; lia) Hsok x
                ltac:(rewrite u_zw_small, Z2Nat.id by lia; lia)) as W.
  unfold wview in W. destruct (mem x) as [b|]; [discriminate|].
  rewrite find_segment_off6 in W by lia. exact W.
Qed.
End FXG.
