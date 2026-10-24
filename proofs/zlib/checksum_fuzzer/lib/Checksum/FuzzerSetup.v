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
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import CrcGen CrcGenModel.
Local Opaque combine_gen_model.
Definition fuzzer_chunk (c : byte) : Z := bv_unsigned c+Z.b2z (bv_unsigned c =? 0).
Lemma fuzzer_chunk_bound : forall c, (1 <= fuzzer_chunk c <= 255)%Z.
Proof. intros. pose proof (byte_unsigned_range c). unfold fuzzer_chunk. destruct (Z.eqb_spec (bv_unsigned c) 0);cbn;lia. Qed.
Lemma fuzzer_chunk_setup : forall
  (ra sp gp tp t0 t1 t2 s2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (B n : Z) (c : byte),
  (0 <= B < 2^64)%Z -> (1 <= n <= 1048576)%Z ->
  ov_read_bytes rsegs m (wa B) 1 = Some [c] ->
  bytes_at rsegs m X2N_TAB x2n_bytes ->
  (forall h5 h6 h7 h10 h11 h12 h13 h14 h15 h16 h17 h28 h29 h30 h31,
    evt rsegs Q
      (MS (mkR (Z_to_bv 64 0x1428c) sp gp tp h5 h6 h7 (Z_to_bv 64 n) (Z_to_bv 64 B)
        h10 h11 h12 h13 h14 h15 h16 h17 (Z_to_bv 64 1) (Z_to_bv 64 n)
        (Z_to_bv 64 (fuzzer_chunk c)) (Z_to_bv 64 (combine_gen_model (fuzzer_chunk c)))
        (Z_to_bv 64 0) (Z_to_bv 64 0) s8 (Z_to_bv 64 0) (Z_to_bv 64 (2^32-1)) s11 h28 h29 h30 h31)
        F (Z_to_bv 64 0x142a0) fc None m (seg_rom rsegs))) ->
  evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 B) (Z_to_bv 64 1)
      a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 0x14264) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Q B n c HB HN RD TABLE CONT.
  pose proof (byte_unsigned_range c) as HC.
  pose proof (fuzzer_chunk_bound c) as HK.
  pose proof (combine_gen_model_positive (fuzzer_chunk c)) as HOP.
  remember (combine_gen_model (fuzzer_chunk c)) as op eqn:DOP.
  assert (UK : bv_unsigned (Z_to_bv 64 (fuzzer_chunk c)) = fuzzer_chunk c).
  { rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64)%Z. apply Z.mod_small. lia. }
  assert (FLAG : (bv_unsigned c <? 1) = (bv_unsigned c =? 0)).
  { destruct (Z.ltb_spec (bv_unsigned c) 1);destruct (Z.eqb_spec (bv_unsigned c) 0);try reflexivity;lia. }
  idtac "FUZZER SETUP prefix". do 10 zstep. idtac "FUZZER SETUP gen". rewrite FLAG.
  change (bv_unsigned c+Z.b2z (bv_unsigned c =? 0))%Z with (fuzzer_chunk c).
  eapply evt_cut.
  - apply crc32_combine_gen_table_spec; [exact TABLE|rewrite UK;lia].
  - intros final HP. unfold crc_return_post in HP.
    destruct HP as (h5 & h6 & h7 & h11 & h12 & h13 & h14 & h15 & h16 & h17 & h28 & h29 & h30 & h31 & HS & MU & WM). subst final.
    rewrite UK. rewrite <- DOP.
    replace (ret_pc (Z_to_bv 64 0x1428c)) with (Z_to_bv 64 0x1428c) by (apply bv_eq;vm_compute;reflexivity).
    idtac "FUZZER SETUP after gen0". zstep.
    idtac "FUZZER SETUP after gen1". zstep.
    idtac "FUZZER SETUP after gen2". zstep.
    idtac "FUZZER SETUP after gen3". zstep.
    idtac "FUZZER SETUP after gen4". zstep.
    idtac "FUZZER SETUP normalize".
    try rewrite crc_shift32_extract.
    try unfold_swrap32.
    repeat match goal with |- context [(?v mod 4294967296)%Z] => rewrite (Z.mod_small v 4294967296) by lia end.
    replace (n+0+2147483648-2147483648)%Z with n by ring.
    apply CONT.
Qed.
