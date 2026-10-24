(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(** Functional multiplication loop adapted from the pinned Varnish proof to
    the actual zlib checksum_fuzzer instruction layout and register allocation. *)
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

From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import CrcUnrolledBytes.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import AdlerModel AdlerWord.
Lemma adler_large_threshold_cert : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (n : Z),
  (0 <= n <= 1048576)%Z ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x11ed4) a1 (Z_to_bv 64 n) a3 a4 (Z_to_bv 64 (Z.shiftr n 4)) (Z_to_bv 64 347) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (if bv_ltu (Z_to_bv 64 (Z.shiftr n 4)) (Z_to_bv 64 347) then Z_to_bv 64 0x15038 else Z_to_bv 64 0x14edc) fc None m (seg_rom rsegs)) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14ecc) fc None m (seg_rom rsegs)).
Proof. intros. do 4 zstep. exact H0. Qed.
Lemma adler_outer_setup_cert : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop),
  ov_read_bytes rsegs m (wa 0x119e0) 8 = Some (le8 (Z_to_bv 64 ADLER_MAGIC)) ->
  evt rsegs Q (MS (mkR ra sp gp tp (Z_to_bv 64 5552) (Z_to_bv 64 (-5552)) (Z_to_bv 64 ADLER_BASE) s0 s1 (Z_to_bv 64 0x11ed4) a1 a2 a3 a4 a1 (Z_to_bv 64 0) (Z_to_bv 64 ADLER_MAGIC) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 346) t4 t5 t6) F (Z_to_bv 64 0x14f04) fc None m (seg_rom rsegs)) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x11ed4) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14edc) fc None m (seg_rom rsegs)).
Proof. intros. unfold ADLER_BASE,ADLER_MAGIC in *. do 10 zstep. exact H0. Qed.
Lemma adler_outer_chunk_init : forall (ra sp gp tp s0 s1 a3 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (B i n g : Z),
  (0 <= B < 2^64)%Z -> (0 <= g <= 1048576)%Z -> (5552 <= n <= 1048576)%Z -> (i=5552*g)%Z ->
  evt rsegs Q (MS (mkR ra sp gp tp (Z_to_bv 64 5552) (Z_to_bv 64 (-5552)) (Z_to_bv 64 ADLER_BASE) s0 s1 (Z_to_bv 64 0x11ed4) (Z_to_bv 64 B) (Z_to_bv 64 (n-5552)) a3 a4 (Z_to_bv 64 (B+i)) (Z_to_bv 64 g) (Z_to_bv 64 ADLER_MAGIC) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 346) (Z_to_bv 64 (B+i+5552)) (Z_to_bv 64 (B+i)) t6) F (Z_to_bv 64 0x14f18) fc None m (seg_rom rsegs)) ->
  evt rsegs Q (MS (mkR ra sp gp tp (Z_to_bv 64 5552) (Z_to_bv 64 (-5552)) (Z_to_bv 64 ADLER_BASE) s0 s1 (Z_to_bv 64 0x11ed4) (Z_to_bv 64 B) (Z_to_bv 64 n) a3 a4 (Z_to_bv 64 (B+i)) (Z_to_bv 64 g) (Z_to_bv 64 ADLER_MAGIC) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 346) t4 t5 t6) F (Z_to_bv 64 0x14f04) fc None m (seg_rom rsegs)).
Proof. intros ra sp gp tp s0 s1 a3 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 F fc m Q B i n g HB HG HN HI CONT.
  unfold ADLER_BASE,ADLER_MAGIC in *. do 5 zstep.
  assert (E : Z_to_bv 64 (n+18446744073709546064) = Z_to_bv 64 (n-5552)).
  { apply Z_to_bv_eqm. replace (n+18446744073709546064)%Z with ((n-5552)+1*2^64)%Z by ring. rewrite Z.mod_add by lia. reflexivity. }
  try rewrite E.
  replace (B+(g*5552+5552))%Z with (B+i+5552)%Z by lia.
  replace (g*5552+5552+B)%Z with (B+i+5552)%Z by lia.
  exact CONT.
Qed.
