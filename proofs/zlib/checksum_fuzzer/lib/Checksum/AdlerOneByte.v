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
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import AdlerModel AdlerWord AdlerShortReduce.
Lemma adler_conditional_shift_word : forall x, (0 <= x < 2*65521)%Z ->
  Z_to_bv 64 (Z.shiftl x 16+Z.land ((-Z.b2z (65520 <? x)) mod 2^64) 18446744069415567360) =
  Z_to_bv 64 (Z.shiftl (x mod 65521) 16).
Proof.
  intros x HX. destruct (Z.ltb_spec 65520 x).
  - change (Z_to_bv 64 (Z.shiftl x 16+18446744069415567360) = Z_to_bv 64 (Z.shiftl (x mod 65521) 16)).
    assert (E : (x mod 65521 = x-65521)%Z).
    { replace x with ((x-65521)+1*65521)%Z at 1 by ring. rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
    rewrite E. apply Z_to_bv_eqm. rewrite !Z.shiftl_mul_pow2 by lia.
    replace (x*2^16+18446744069415567360)%Z with ((x-65521)*2^16+1*2^64)%Z by ring.
    rewrite Z.mod_add by lia. reflexivity.
  - change (Z_to_bv 64 (Z.shiftl x 16+0) = Z_to_bv 64 (Z.shiftl (x mod 65521) 16)).
    rewrite Z.add_0_r,Z.mod_small by lia. reflexivity.
Qed.
Lemma adler_one_model : forall a b c,
  adler_pack ((a+bv_unsigned c) mod ADLER_BASE) ((((a+bv_unsigned c) mod ADLER_BASE)+b) mod ADLER_BASE) =
  adler_output [c] a b.
Proof.
  intros a b c. change (adler_pack ((a+bv_unsigned c) mod ADLER_BASE)
    ((((a+bv_unsigned c) mod ADLER_BASE)+b) mod ADLER_BASE) =
    adler_pack ((a+bv_unsigned c) mod ADLER_BASE) ((b+a+bv_unsigned c) mod ADLER_BASE)).
  f_equal. rewrite (Z.add_mod ((a+bv_unsigned c) mod ADLER_BASE) b ADLER_BASE),Z.mod_mod,
    <- (Z.add_mod (a+bv_unsigned c) b ADLER_BASE) by (unfold ADLER_BASE;lia). f_equal;ring.
Qed.
Lemma adler_one_byte_cert : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (B a b : Z) (c : byte),
  (0 <= B < 2^64)%Z -> (0 <= a < ADLER_BASE)%Z -> (0 <= b < ADLER_BASE)%Z ->
  ov_read_bytes rsegs m (wa B) 1 = Some [c] ->
  (forall h11 h12 h13 h14, evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (adler_output [c] a b)) h11 h12 h13 h14 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 B) a2 (Z_to_bv 64 b) (Z_to_bv 64 a) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14ddc) fc None m (seg_rom rsegs)).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Q B a b c HBP HA HB RD CONT.
  pose proof (byte_unsigned_range c) as HC.
  assert (HS : (0 <= a+bv_unsigned c < 2*65521)%Z) by (unfold ADLER_BASE in HA;lia).
  pose proof (Z.mod_pos_bound (a+bv_unsigned c) ADLER_BASE ltac:(unfold ADLER_BASE;lia)) as HAF.
  assert (HT : (0 <= (a+bv_unsigned c) mod ADLER_BASE+b < 2*65521)%Z) by (unfold ADLER_BASE in *;lia).
  assert (SB : (0 <= Z.shiftl ((a+bv_unsigned c) mod ADLER_BASE+b) 16 < 2^64)%Z) by (unfold ADLER_BASE in *;rewrite Z.shiftl_mul_pow2 by lia;nia).
  pose proof (Z.mod_pos_bound (((a+bv_unsigned c) mod ADLER_BASE)+b) ADLER_BASE ltac:(unfold ADLER_BASE;lia)) as HBF.
  assert (SBF : (0 <= Z.shiftl ((((a+bv_unsigned c) mod ADLER_BASE)+b) mod ADLER_BASE) 16 < 2^64)%Z).
  { rewrite Z.shiftl_mul_pow2 by lia. unfold ADLER_BASE in *. nia. }
  unfold ADLER_BASE in *.
  idtac "ADLER ONE BYTE step 0". zstep.
  idtac "ADLER ONE BYTE step 1". zstep.
  idtac "ADLER ONE BYTE step 2". zstep.
  idtac "ADLER ONE BYTE step 3". zstep.
  idtac "ADLER ONE BYTE step 4". zstep.
  idtac "ADLER ONE BYTE step 5". zstep.
  idtac "ADLER ONE BYTE step 6". zstep.
  idtac "ADLER ONE BYTE step 7". zstep.
  idtac "ADLER ONE BYTE step 8". zstep.
  idtac "ADLER ONE BYTE step 9". zstep.
  idtac "ADLER ONE BYTE step 10". zstep.
  rewrite adler_conditional_subtract_word by exact HS.
  idtac "ADLER ONE BYTE step 11". zstep.
  idtac "ADLER ONE BYTE step 12". zstep.
  idtac "ADLER ONE BYTE step 13". zstep.
  idtac "ADLER ONE BYTE step 14". zstep.
  idtac "ADLER ONE BYTE step 15". zstep.
  idtac "ADLER ONE BYTE step 16". zstep.
  idtac "ADLER ONE BYTE step 17". zstep.
  rewrite adler_conditional_shift_word by exact HT.
  idtac "ADLER ONE BYTE step 18". zstep.
  first [rewrite adler_pack_or by lia|rewrite Z.lor_comm;rewrite adler_pack_or by lia].
  rewrite adler_one_model.
  idtac "ADLER ONE BYTE step 19". zstep.
  apply CONT.
Qed.
