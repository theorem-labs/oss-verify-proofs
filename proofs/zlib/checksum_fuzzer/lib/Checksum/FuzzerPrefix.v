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
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import CrcSeed AdlerSeed AdlerBlockControl.
Section FuzzerPrefix.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : word -> option byte).
  Variables (B n : Z).
  Hypothesis NVALID : (1 <= n <= 1048576)%Z.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo+192 <= bv_unsigned sp)%Z.
  Variable Q : machine_state -> Prop.
  Theorem fuzzer_valid_prefix :
    (forall m1 junk,
      munch [(bv_unsigned sp-192,bv_unsigned sp)]%Z m m1 ->
      wmono rsegs m m1 -> stk rsegs m1 lo (bv_unsigned sp-112) ->
      rw_cells rsegs m1 (bv_unsigned sp-112)
        [CB 8 junk;C8 s11;C8 s10;C8 s9;C8 s8;C8 s7;C8 s6;C8 s5;C8 s4;C8 s3;C8 s2;C8 s1;C8 s0;C8 ra] ->
      evt rsegs Q (MS (mkR (Z_to_bv 64 0x14254) (Z_to_bv 64 (bv_unsigned sp-112)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 B) (Z_to_bv 64 1) (Z_to_bv 64 (-1048576)) (Z_to_bv 64 (n-1048577)) (Z_to_bv 64 0) (Z_to_bv 64 0) a5 a6 a7 s2 (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14264) fc None m1 (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 B) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x141f0) fc None m (seg_rom rsegs)).
  Proof.
    intros CONT.
    pose proof (munch_refl [(bv_unsigned sp-192,bv_unsigned sp)]%Z m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp.
    carve_frame 112%nat ST.
    do 14 zstep. try Stor0fe.sb_flush.
    do 6 zstep.
    eapply crc_length_wrapper. eapply crc_null_cert.
    replace (ret_pc (Z_to_bv 64 0x14240)) with (Z_to_bv 64 0x14240) by (apply bv_eq;vm_compute;reflexivity).
    do 5 zstep.
    eapply adler_length_wrapper. do 4 zstep.
    eapply adler_entry_one_cert. if_cases ONE;zify_cond ONE.
    2:{ exfalso. lia. }
    eapply adler_entry_null_cert. if_cases NULL;zify_cond NULL.
    2:{ exfalso. lia. }
    zstep.
    replace (ret_pc (Z_to_bv 64 0x14254)) with (Z_to_bv 64 0x14254) by (apply bv_eq;vm_compute;reflexivity).
    do 4 zstep.
    assert (U : bv_unsigned (Z_to_bv 64 (n-1048577)) = (2^64+n-1048577)%Z).
    { rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64)%Z.
      replace (n-1048577)%Z with ((2^64+n-1048577)+(-1)*2^64)%Z by ring.
      rewrite Z.mod_add by lia. apply Z.mod_small. clear -NVALID;lia. }
    assert (C : bv_unsigned (Z_to_bv 64 (-1048576)) = (2^64-1048576)%Z) by (vm_compute;reflexivity).
    if_cases BAD;try (unfold bv_ltu in BAD;rewrite U,C in BAD);zify_cond BAD.
    { exfalso. clear -BAD NVALID;Z.div_mod_to_equations;lia. }
    eapply CONT;[exact MU|exact WM|exact ST|exact FR].
  Qed.
End FuzzerPrefix.
