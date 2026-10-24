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
Section AdlerReduce.
  Variables (ra sp gp tp t1 s0 s1 a0 a1 a2 a5 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variable Q : machine_state -> Prop.
Lemma adler_reduce_outer : forall a b, (0 <= a < 2^48)%Z -> (0 <= b < 2^48)%Z ->
  (forall h30 h31, evt rsegs Q (MS (mkR ra sp gp tp (Z_to_bv 64 5552) t1 (Z_to_bv 64 ADLER_BASE) s0 s1 a0 a1 a2 (Z_to_bv 64 (b mod ADLER_BASE)) (Z_to_bv 64 (a mod ADLER_BASE)) (Z_to_bv 64 (bv_unsigned a5+5552)) (Z_to_bv 64 (bv_unsigned a6+1)) (Z_to_bv 64 ADLER_MAGIC) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 (Z_to_bv 64 (Z.shiftr (bv_unsigned a2) 4)) h30 h31) F (Z_to_bv 64 0x15024) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp (Z_to_bv 64 5552) t1 (Z_to_bv 64 ADLER_BASE) s0 s1 a0 a1 a2 (Z_to_bv 64 b) (Z_to_bv 64 a) a5 a6 (Z_to_bv 64 ADLER_MAGIC) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14fe0) fc None m (seg_rom rsegs)).
Proof.
  intros a b HA HB CONT.
  remember (Z.shiftr (a*ADLER_MAGIC) 64) as hA eqn:DHA.
  assert (HHA : (0 <= hA <= a)%Z).
  { rewrite DHA,Z.shiftr_div_pow2 by lia. apply adler_mulhu_bounds. lia. }
  assert (NHA : (0 <= Z.shiftr (a-hA) 1+hA <= a)%Z).
  { rewrite Z.shiftr_div_pow2 by lia.
    assert (HD : (0 <= (a-hA)/2 <= a-hA)%Z).
    { split;[apply Z.div_pos;lia|apply Z.div_le_upper_bound;lia]. } lia. }
  assert (QA : Z.shiftr (Z.shiftr (a-hA) 1+hA) 15 = (a/ADLER_BASE)%Z).
  { rewrite DHA. apply adler_div_form. lia. }
  pose proof (Z.div_mod a ADLER_BASE ltac:(unfold ADLER_BASE;lia)) as DA.
  pose proof (Z.mod_pos_bound a ADLER_BASE ltac:(unfold ADLER_BASE;lia)) as RA.
  assert (PQA : (0 <= (a/ADLER_BASE)*ADLER_BASE <= a)%Z).
  { pose proof (Z.div_pos a ADLER_BASE ltac:(lia) ltac:(unfold ADLER_BASE;lia)). unfold ADLER_BASE in *. lia. }
  remember (Z.shiftr (b*ADLER_MAGIC) 64) as hB eqn:DHB.
  assert (HHB : (0 <= hB <= b)%Z).
  { rewrite DHB,Z.shiftr_div_pow2 by lia. apply adler_mulhu_bounds. lia. }
  assert (NHB : (0 <= Z.shiftr (b-hB) 1+hB <= b)%Z).
  { rewrite Z.shiftr_div_pow2 by lia.
    assert (HD : (0 <= (b-hB)/2 <= b-hB)%Z).
    { split;[apply Z.div_pos;lia|apply Z.div_le_upper_bound;lia]. } lia. }
  assert (QB : Z.shiftr (Z.shiftr (b-hB) 1+hB) 15 = (b/ADLER_BASE)%Z).
  { rewrite DHB. apply adler_div_form. lia. }
  pose proof (Z.div_mod b ADLER_BASE ltac:(unfold ADLER_BASE;lia)) as DB.
  pose proof (Z.mod_pos_bound b ADLER_BASE ltac:(unfold ADLER_BASE;lia)) as RB.
  assert (PQB : (0 <= (b/ADLER_BASE)*ADLER_BASE <= b)%Z).
  { pose proof (Z.div_pos b ADLER_BASE ltac:(lia) ltac:(unfold ADLER_BASE;lia)). unfold ADLER_BASE in *. lia. }
  unfold ADLER_BASE,ADLER_MAGIC in *.
  idtac "ADLER REDUCE step 0". zstep.
  try rewrite <- DHA. try rewrite <- DHB.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  idtac "ADLER REDUCE step 1". zstep.
  try rewrite <- DHA. try rewrite <- DHB.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  idtac "ADLER REDUCE step 2". zstep.
  try rewrite <- DHA. try rewrite <- DHB.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  idtac "ADLER REDUCE step 3". zstep.
  try rewrite <- DHA. try rewrite <- DHB.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  idtac "ADLER REDUCE step 4". zstep.
  try rewrite <- DHA. try rewrite <- DHB.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  idtac "ADLER REDUCE step 5". zstep.
  try rewrite <- DHA. try rewrite <- DHB.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  idtac "ADLER REDUCE step 6". zstep.
  try rewrite <- DHA. try rewrite <- DHB.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  idtac "ADLER REDUCE step 7". zstep.
  try rewrite <- DHA. try rewrite <- DHB.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  idtac "ADLER REDUCE step 8". zstep.
  try rewrite <- DHA. try rewrite <- DHB.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  idtac "ADLER REDUCE step 9". zstep.
  try rewrite <- DHA. try rewrite <- DHB.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  rewrite QA.
  idtac "ADLER REDUCE step 10". zstep.
  try rewrite <- DHA. try rewrite <- DHB.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  idtac "ADLER REDUCE step 11". zstep.
  try rewrite <- DHA. try rewrite <- DHB.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  replace (a-a/65521*65521)%Z with (a mod 65521)%Z by (rewrite Z.mod_eq by lia;ring).
  idtac "ADLER REDUCE step 12". zstep.
  try rewrite <- DHA. try rewrite <- DHB.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  idtac "ADLER REDUCE step 13". zstep.
  try rewrite <- DHA. try rewrite <- DHB.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  rewrite QB.
  idtac "ADLER REDUCE step 14". zstep.
  try rewrite <- DHA. try rewrite <- DHB.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  idtac "ADLER REDUCE step 15". zstep.
  try rewrite <- DHA. try rewrite <- DHB.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  replace (b-b/65521*65521)%Z with (b mod 65521)%Z by (rewrite Z.mod_eq by lia;ring).
  idtac "ADLER REDUCE step 16". zstep.
  try rewrite <- DHA. try rewrite <- DHB.
  repeat match goal with |- context [(?v mod 18446744073709551616)%Z] => rewrite (Z.mod_small v 18446744073709551616) by lia end.
  apply CONT.
Qed.
End AdlerReduce.
