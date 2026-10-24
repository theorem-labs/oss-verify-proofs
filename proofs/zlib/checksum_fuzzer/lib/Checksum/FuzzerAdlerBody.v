(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(** Actual Adler chunk iteration and its repeat and exit branches. *)
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
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import Crc32 CrcGen CrcOp CrcChunkLaw CrcGenModel CrcSeed.
Local Opaque crc_model combine_op_model combine_gen_model.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import Adler32 AdlerFrame AdlerModel AdlerWord AdlerComposition.
Local Opaque adler_output adler_model adler_pack.
Theorem fuzzer_adler_chunk_iteration : forall (ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (lo B n k i a b : Z) (bs : list byte) (m : word -> option byte) (Q : machine_state -> Prop),
  (0 <= a < ADLER_BASE)%Z -> (0 <= b < ADLER_BASE)%Z ->
  (1 <= n <= 1048576)%Z -> (1 <= k <= 255)%Z -> (0 <= i)%Z -> (i+k <= n)%Z ->
  Z.of_nat (length bs) = k ->
  bytes_at rsegs m (B+i) bs -> bytes_at rsegs m 0x119e0 (le8 (Z_to_bv 64 ADLER_MAGIC)) ->
  (0 < B)%Z -> (B+n < 2^64)%Z ->
  stk rsegs m lo (bv_unsigned sp) -> (lo+32 <= bv_unsigned sp)%Z ->
  (B+i+k <= bv_unsigned sp-32 \/ bv_unsigned sp <= B+i)%Z ->
  (0x119e0+8 <= bv_unsigned sp-32 \/ bv_unsigned sp <= 0x119e0)%Z ->
  (forall (h5 h6 h7 h12 h13 h14 h15 h16 h17 h28 h29 h30 h31 : word) m1,
    (i+k+k <= n)%Z ->
    munch [(bv_unsigned sp-32,bv_unsigned sp)]%Z m m1 -> wmono rsegs m m1 ->
    stk rsegs m1 lo (bv_unsigned sp) ->
    bytes_at rsegs m1 (B+i) bs -> bytes_at rsegs m1 0x119e0 (le8 (Z_to_bv 64 ADLER_MAGIC)) ->
    evt rsegs Q (MS (mkR (Z_to_bv 64 0x14410) sp gp tp h5 h6 h7 (Z_to_bv 64 n) (Z_to_bv 64 B) (Z_to_bv 64 (adler_output bs a b)) (Z_to_bv 64 (i+k+k)) h12 h13 h14 h15 h16 h17 (Z_to_bv 64 1) (Z_to_bv 64 n) (Z_to_bv 64 k) s5 (Z_to_bv 64 (i+k)) s7 s8 s9 (Z_to_bv 64 4294967295) s11 h28 h29 h30 h31) F (Z_to_bv 64 0x143f8) fc None m1 (seg_rom rsegs))) ->
  (forall (h5 h6 h7 h12 h13 h14 h15 h16 h17 h28 h29 h30 h31 : word) m1,
    (n < i+k+k)%Z ->
    munch [(bv_unsigned sp-32,bv_unsigned sp)]%Z m m1 -> wmono rsegs m m1 ->
    stk rsegs m1 lo (bv_unsigned sp) ->
    bytes_at rsegs m1 (B+i) bs -> bytes_at rsegs m1 0x119e0 (le8 (Z_to_bv 64 ADLER_MAGIC)) ->
    evt rsegs Q (MS (mkR (Z_to_bv 64 0x14410) sp gp tp h5 h6 h7 (Z_to_bv 64 n) (Z_to_bv 64 B) (Z_to_bv 64 (adler_output bs a b)) (Z_to_bv 64 (i+k)) h12 h13 h14 h15 h16 h17 (Z_to_bv 64 1) (Z_to_bv 64 n) (Z_to_bv 64 k) s5 (Z_to_bv 64 (i+k)) s7 s8 s9 (Z_to_bv 64 4294967295) s11 h28 h29 h30 h31) F (Z_to_bv 64 0x14424) fc None m1 (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 B) (Z_to_bv 64 (adler_pack a b)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 1) (Z_to_bv 64 n) (Z_to_bv 64 k) s5 (Z_to_bv 64 i) s7 s8 s9 (Z_to_bv 64 4294967295) s11 t3 t4 t5 t6) F (Z_to_bv 64 0x143f8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s7 s8 s9 s11 t3 t4 t5 t6 F fc lo B n k i a b bs m Q HA HB HN HK HI GOOD LK INP TABLE HBUF TOP ST LO DI DT AGAIN EXIT.
  remember (adler_pack a b) as q eqn:DQ.
  pose proof (adler_pack_range a b HA HB) as HQ. rewrite <- DQ in HQ.
  assert (LQ : Z.land q 4294967295 = q).
  { change (Z.land q (Z.ones 32) = q). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity. }
  idtac "ADLER ITERATION call". do 6 zstep.
  try rewrite LQ. try rewrite crc_shift32_extract.
  repeat match goal with |- context [(?v mod 4294967296)%Z] => rewrite (Z.mod_small v 4294967296) by lia end.
  rewrite DQ. rewrite <- LK.
  eapply evt_cut.
  - apply adler32_z_nonnull_spec with (lo:=lo);
      [exact HA|exact HB|exact INP|exact TABLE|lia|rewrite LK;lia|rewrite LK;lia|exact ST|exact LO|rewrite LK;exact DI|exact DT].
  - intros final HP. unfold adler_value_post in HP.
    destruct HP as (h5 & h6 & h7 & h11 & h12 & h13 & h14 & h15 & h16 & h17 & h28 & h29 & h30 & h31 & m1 & HS & MU & WM & ST1). subst final.
    rewrite LK.
    assert (INP1 : bytes_at rsegs m1 (B+i) bs).
    { eapply bytes_at_transport;[exact INP|exact MU|]. cbn [disjoint_from]. unfold ADLER_FRAME. rewrite LK. split;[exact DI|exact I]. }
    assert (TABLE1 : bytes_at rsegs m1 0x119e0 (le8 (Z_to_bv 64 ADLER_MAGIC))).
    { eapply bytes_at_transport;[exact TABLE|exact MU|]. cbn [disjoint_from]. unfold ADLER_FRAME. split;[exact DT|exact I]. }
    replace (ret_pc (Z_to_bv 64 0x14410)) with (Z_to_bv 64 0x14410) by (apply bv_eq;vm_compute;reflexivity).
    remember (adler_output bs a b) as qnext eqn:DQN in *.
    idtac "ADLER ITERATION branch". do 2 zstep.
    try unfold_swrap32.
    repeat match goal with |- context [(?v mod 4294967296)%Z] => rewrite (Z.mod_small v 4294967296) by lia end.
    replace (k+(i+k)+2147483648-2147483648)%Z with (i+k+k)%Z by ring.
    zstep. if_cases K;zify_cond K.
    + eapply AGAIN;[exact K|exact MU|exact WM|exact ST1|exact INP1|exact TABLE1].
    + do 2 zstep. try rewrite crc_shift32_extract.
      repeat match goal with |- context [(?v mod 4294967296)%Z] => rewrite (Z.mod_small v 4294967296) by lia end.
      eapply EXIT;[lia|exact MU|exact WM|exact ST1|exact INP1|exact TABLE1].
Qed.
