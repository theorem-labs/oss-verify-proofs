(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(** Actual three-call CRC chunk iteration, including its agreement assertion. *)
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
Theorem fuzzer_crc_chunk_iteration : forall
  (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s9 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (lo B q : Z) (bs : list byte) (m : word -> option byte) (Q : machine_state -> Prop),
  bytes_at rsegs m B bs -> bytes_at rsegs m CRC_TABS crc_table_bytes ->
  (0 < B)%Z -> (B+Z.of_nat (length bs) < 2^64)%Z ->
  (1 <= Z.of_nat (length bs) <= 255)%Z -> (0 <= q < 2^32)%Z ->
  stk rsegs m lo (bv_unsigned sp) -> (lo+80 <= bv_unsigned sp)%Z ->
  (B+Z.of_nat (length bs) <= bv_unsigned sp-80 \/ bv_unsigned sp <= B)%Z ->
  (CRC_TABS+5120 <= bv_unsigned sp-80 \/ bv_unsigned sp <= CRC_TABS)%Z ->
  (forall h5 h6 h7 h11 h12 h13 h14 h15 h16 h17 h28 h29 h30 h31 m1,
    munch [(bv_unsigned sp-80,bv_unsigned sp)]%Z m m1 -> wmono rsegs m m1 ->
    stk rsegs m1 lo (bv_unsigned sp) -> bytes_at rsegs m1 B bs -> bytes_at rsegs m1 CRC_TABS crc_table_bytes ->
    evt rsegs Q
      (MS (mkR (Z_to_bv 64 0x142f0) sp gp tp h5 h6 h7 s0 s1 (Z_to_bv 64 (crc_model q bs))
        h11 h12 h13 h14 h15 h16 h17 s2 s3 (Z_to_bv 64 (Z.of_nat (length bs)))
        (Z_to_bv 64 (combine_gen_model (Z.of_nat (length bs)))) (Z_to_bv 64 0) (Z_to_bv 64 (crc_model q bs))
        (Z_to_bv 64 B) s9 (Z_to_bv 64 (2^32-1)) (Z_to_bv 64 (crc_model q bs)) h28 h29 h30 h31)
        F (Z_to_bv 64 0x142a0) fc None m1 (seg_rom rsegs))) ->
  evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3
      (Z_to_bv 64 (Z.of_nat (length bs))) (Z_to_bv 64 (combine_gen_model (Z.of_nat (length bs))))
      (Z_to_bv 64 0) (Z_to_bv 64 q) (Z_to_bv 64 B) s9 (Z_to_bv 64 (2^32-1)) s11 t3 t4 t5 t6)
      F (Z_to_bv 64 0x142b8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s9 s11 t3 t4 t5 t6 F fc lo B q bs m Q INP TABLE HB TOP SIZE HQ ST LO DI DT CONT.
  remember (combine_gen_model (Z.of_nat (length bs))) as op eqn:DOP in *.
  remember (crc_model q bs) as answer eqn:DANSWER in *.
  assert (HANSWER : (0 <= answer < 2^32)%Z) by (rewrite DANSWER;apply crc_model_range;exact HQ).
  remember (crc_model 0 bs) as part eqn:DPART.
  assert (HPART : (0 <= part < 2^32)%Z) by (rewrite DPART;apply crc_model_range;lia).
  assert (HOP : (0 < op < 2^32)%Z) by (rewrite DOP;apply combine_gen_model_positive).
  assert (MODEL : combine_op_model q part op = answer).
  { rewrite DPART,DOP,DANSWER. apply crc_chunk_combine;lia. }
  assert (UQ : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit;lia).
  assert (UP : bv_unsigned (Z_to_bv 64 part) = part) by (apply unsigned_lit;lia).
  assert (UOP : bv_unsigned (Z_to_bv 64 op) = op) by (apply unsigned_lit;lia).
  assert (LAND : Z.land part (2^32-1) = part).
  { change (Z.land part (Z.ones 32) = part). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity. }
  change (Z.land part 4294967295 = part) in LAND.
  idtac "FUZZER CRC OP first call". do 4 zstep.
  eapply evt_cut.
  - apply crc32_z_nonnull_spec with (lo:=lo);try assumption. lia.
  - intros final HP. unfold crc32_value_post in HP.
    destruct HP as (g5 & g6 & g7 & g11 & g12 & g13 & g14 & g15 & g16 & g17 & g28 & g29 & g30 & g31 & m1 & HS & MU & WM & ST1). subst final.
    change (bv_unsigned (Z_to_bv 64 0) mod 2^32)%Z with 0%Z.
    rewrite <- DPART.
    assert (INP1 : bytes_at rsegs m1 B bs).
    { eapply bytes_at_transport; [exact INP|exact MU|]. cbn [disjoint_from]. split;[exact DI|exact I]. }
    assert (TABLE1 : bytes_at rsegs m1 CRC_TABS crc_table_bytes).
    { eapply bytes_at_transport; [exact TABLE|exact MU|]. cbn [disjoint_from]. split;[exact DT|exact I]. }
    replace (ret_pc (Z_to_bv 64 0x142c8)) with (Z_to_bv 64 0x142c8) by (apply bv_eq;vm_compute;reflexivity).
    idtac "FUZZER CRC OP combine". do 4 zstep.
    try rewrite LAND.
    repeat match goal with |- context [(?v mod 4294967296)%Z] => rewrite (Z.mod_small v 4294967296) by lia end.
    eapply evt_cut.
    + apply crc32_combine_op_any_memory_spec;rewrite ?LAND,?UQ,?UP,?UOP;lia.
    + intros final HP. unfold crc_return_post in HP.
      destruct HP as (h5 & h6 & h7 & h11 & h12 & h13 & h14 & h15 & h16 & h17 & h28 & h29 & h30 & h31 & HS & MU0 & WM0). subst final.
      try rewrite LAND. rewrite UQ,UP,UOP,MODEL.
      replace (ret_pc (Z_to_bv 64 0x142d8)) with (Z_to_bv 64 0x142d8) by (apply bv_eq;vm_compute;reflexivity).
      idtac "FUZZER CRC iteration third call". do 6 zstep.
      try rewrite crc_shift32_extract.
      repeat match goal with |- context [(?v mod 4294967296)%Z] => rewrite (Z.mod_small v 4294967296) by lia end.
      eapply evt_cut.
      * apply crc32_z_nonnull_spec with (lo:=lo);
          [exact INP1|exact TABLE1|exact HB|exact TOP|lia|exact ST1|exact LO|exact DI|exact DT].
      * intros final HP. unfold crc32_value_post in HP.
        destruct HP as (j5 & j6 & j7 & j11 & j12 & j13 & j14 & j15 & j16 & j17 & j28 & j29 & j30 & j31 & m2 & HS & MU2 & WM2 & ST2). subst final.
        rewrite UQ. rewrite (Z.mod_small q (2^32) HQ). rewrite <- DANSWER.
        assert (INP2 : bytes_at rsegs m2 B bs).
        { eapply bytes_at_transport; [exact INP1|exact MU2|]. cbn [disjoint_from]. split;[exact DI|exact I]. }
        assert (TABLE2 : bytes_at rsegs m2 CRC_TABS crc_table_bytes).
        { eapply bytes_at_transport; [exact TABLE1|exact MU2|]. cbn [disjoint_from]. split;[exact DT|exact I]. }
        replace (ret_pc (Z_to_bv 64 0x142f0)) with (Z_to_bv 64 0x142f0) by (apply bv_eq;vm_compute;reflexivity).
        idtac "FUZZER CRC iteration assertion". do 3 zstep.
        try rewrite crc_shift32_extract.
        repeat match goal with |- context [(?v mod 4294967296)%Z] => rewrite (Z.mod_small v 4294967296) by lia end.
        zstep. if_cases K;zify_cond K.
        -- eapply CONT; [eapply munch_trans;[exact MU|exact MU2]|eapply wmono_trans;[exact WM|exact WM2]|exact ST2|exact INP2|exact TABLE2].
        -- exfalso. lia.
Qed.
