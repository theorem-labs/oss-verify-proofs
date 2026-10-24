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

From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import AdlerModel AdlerWord.
Definition ADLER_FRAME : Z := 32%Z.
Definition adler_value_post (answer : Z)
  (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
  (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun final => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    final = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 answer) a1 a2 a3 a4 a5 a6 a7
      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp-ADLER_FRAME,bv_unsigned sp)]%Z m m' /\
    wmono rsegs m m' /\ stk rsegs m' lo (bv_unsigned sp).
Section AdlerEpilogue.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m m1 : word -> option byte) (junk : list byte).
  Hypothesis MU : munch [(bv_unsigned sp-ADLER_FRAME,bv_unsigned sp)]%Z m m1.
  Hypothesis WM : wmono rsegs m m1.
  Hypothesis LO : (lo+ADLER_FRAME <= bv_unsigned sp)%Z.
  Hypothesis ST : stk rsegs m1 lo (bv_unsigned sp-ADLER_FRAME).
  Hypothesis FR : rw_cells rsegs m1 (bv_unsigned sp-ADLER_FRAME) [CB 8 junk;C8 s2;C8 s1;C8 s0].
  Lemma adler_epilogue : forall pc answer t0 t1 t2 g8 g9 a1 a2 a3 a4 a5 a6 a7 g18 t3 t4 t5 t6,
    (pc=0x14eb8 \/ pc=0x15178)%Z ->
    evt rsegs (adler_value_post answer ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp-ADLER_FRAME)) gp tp t0 t1 t2 g8 g9 (Z_to_bv 64 answer)
        a1 a2 a3 a4 a5 a6 a7 g18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m1 (seg_rom rsegs)).
  Proof.
    intros. unfold adler_value_post,ADLER_FRAME in *.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp.
    destruct H as [Hpc | Hpc]; subst pc; do 4 zstep;
      replace (bv_unsigned sp-32+32)%Z with (bv_unsigned sp) by lia;
      rewrite Z_to_bv_bv_unsigned;
      release_frame FR ST (bv_unsigned sp); zstep;finish.
  Qed.
End AdlerEpilogue.
Section AdlerPack_main.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variable Q : machine_state -> Prop.
  Lemma adler_pack_main_steps : forall a b, (0 <= a < 65536)%Z -> (0 <= b < 65536)%Z ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (adler_pack a b)) a1 a2 (Z_to_bv 64 b) (Z_to_bv 64 a) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15178) fc None m (seg_rom rsegs)) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 b) (Z_to_bv 64 a) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15170) fc None m (seg_rom rsegs)).
  Proof. intros a b HA HB CONT.
    assert (SB : (0 <= Z.shiftl b 16 < 2^64)%Z) by (rewrite Z.shiftl_mul_pow2 by lia;lia).
    do 2 zstep. try rewrite (Z.mod_small (Z.shiftl b 16) 18446744073709551616) by exact SB.
    first [rewrite adler_pack_or by lia|rewrite (Z.lor_comm a (Z.shiftl b 16));rewrite adler_pack_or by lia].
    exact CONT. Qed.
End AdlerPack_main.
Section AdlerPack_short.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variable Q : machine_state -> Prop.
  Lemma adler_pack_short_steps : forall a b, (0 <= a < 65536)%Z -> (0 <= b < 65536)%Z ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (adler_pack a b)) (Z_to_bv 64 a) a2 (Z_to_bv 64 b) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14eb8) fc None m (seg_rom rsegs)) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 a) a2 (Z_to_bv 64 b) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14eb0) fc None m (seg_rom rsegs)).
  Proof. intros a b HA HB CONT.
    assert (SB : (0 <= Z.shiftl b 16 < 2^64)%Z) by (rewrite Z.shiftl_mul_pow2 by lia;lia).
    do 2 zstep. try rewrite (Z.mod_small (Z.shiftl b 16) 18446744073709551616) by exact SB.
    first [rewrite adler_pack_or by lia|rewrite (Z.lor_comm a (Z.shiftl b 16));rewrite adler_pack_or by lia].
    exact CONT. Qed.
End AdlerPack_short.
