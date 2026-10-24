(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(** Actual CRC chunk counter, pointer and exit branch. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Import Tac Bytes.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import Img0 CrcLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require TacDiet2.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Step.transport_chunks segs m a bs ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Tac.footprint_after_store segs m a bs ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Step.mem_after_store ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Tac.transport_after_call segs m m' MU WM ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Step.addr_eq_tac ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.ZBridge.word_eq_tac ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.ZBridge.mlia ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require StepFast.
#[local] Ltac2 Set OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Step.step_core segs R F pc fc rv m ro ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Step.zstep ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Destzna.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Tac.destruct_exs PO ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Destzna.dk_exs PO.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Tac.destruct_ands PO ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require WeqGuard TacDiet2.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.WeqGuard.weq_guard; OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Stor0fe.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Step.mem_after_store ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Dieta54.
Local Ltac lia ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Dieta54.dlia.
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import
  CrcModel CrcByteStep CrcTables CrcLoads CrcLinearBasis.

From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import
  CrcBodyEntry CrcWordBody CrcTailReturn CrcFrame CrcPrologue CrcSeed.
Local Opaque csteps raw_crc raw_byte.

Theorem fuzzer_crc_head : forall (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s8 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (B n k i q op : Z),
  (1 <= n <= 1048576)%Z -> (1 <= k <= 255)%Z -> (0 <= i <= n)%Z ->
  (0 < B)%Z -> (B+n < 2^64)%Z ->
  ((n < i+k)%Z -> evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 B) (Z_to_bv 64 i) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 n) (Z_to_bv 64 k) (Z_to_bv 64 op) (Z_to_bv 64 0) (Z_to_bv 64 q) s8 (Z_to_bv 64 (i+k)) (Z_to_bv 64 4294967295) s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14320) fc None m (seg_rom rsegs))) ->
  ((i+k <= n)%Z -> evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 B) (Z_to_bv 64 i) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 n) (Z_to_bv 64 k) (Z_to_bv 64 op) (Z_to_bv 64 0) (Z_to_bv 64 q) (Z_to_bv 64 (B+i)) (Z_to_bv 64 (i+k)) (Z_to_bv 64 4294967295) s11 t3 t4 t5 t6) F (Z_to_bv 64 0x142b8) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 B) a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 n) (Z_to_bv 64 k) (Z_to_bv 64 op) (Z_to_bv 64 0) (Z_to_bv 64 q) s8 (Z_to_bv 64 i) (Z_to_bv 64 4294967295) s11 t3 t4 t5 t6) F (Z_to_bv 64 0x142a0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s8 s11 t3 t4 t5 t6 F fc m Q B n k i q op HN HK HI HB TOP EXIT BODY.
  idtac "CRC HEAD counter". do 4 zstep.
  try unfold_swrap32.
  repeat match goal with |- context [(?v mod 4294967296)%Z] => rewrite (Z.mod_small v 4294967296) by lia end.
  replace (i+k+2147483648-2147483648)%Z with (i+k)%Z by ring.
  replace (i+0+2147483648-2147483648)%Z with i by ring.
  try rewrite crc_shift32_extract.
  repeat match goal with |- context [(?v mod 4294967296)%Z] => rewrite (Z.mod_small v 4294967296) by lia end.
  idtac "CRC HEAD branch". zstep. if_cases K;zify_cond K.
  - apply EXIT. lia.
  - zstep. apply BODY. lia.
Qed.
