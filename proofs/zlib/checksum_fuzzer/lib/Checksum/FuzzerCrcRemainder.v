(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(** Actual CRC remainder, whole-input checksum and agreement assertion. *)
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
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import FuzzerSlices.
Lemma fuzzer_remainder_mod : forall n i k,
  (0 <= i <= n)%Z -> (n < i+k)%Z -> (0 < k)%Z -> (i mod k = 0)%Z -> (n mod k = n-i)%Z.
Proof.
  intros n i k HI END HK IMOD.
  replace n with ((n-i)+i)%Z at 1 by ring.
  rewrite Z.add_mod,IMOD,Z.add_0_r,Z.mod_mod by lia. apply Z.mod_small. lia.
Qed.
Lemma fuzzer_bytes_suffix : forall segs m B inp i,
  bytes_at segs m B inp -> (i <= length inp)%nat ->
  bytes_at segs m (B+Z.of_nat i) (skipn i inp).
Proof.
  intros segs m B inp i H HI.
  pose proof (fuzzer_bytes_slice segs m B inp i (length (skipn i inp)) H ltac:(rewrite skipn_length;lia)) as HS.
  rewrite firstn_all in HS. exact HS.
Qed.
Theorem fuzzer_crc_remainder : forall (ra sp gp tp t0 t1 t2 s2 a1 a2 a3 a4 a5 a6 a7 old5 s8 s9 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (lo B k i q : Z) (inp : list byte) (m : word -> option byte) (Q : machine_state -> Prop),
  bytes_at rsegs m B inp -> bytes_at rsegs m CRC_TABS crc_table_bytes ->
  (0 < B)%Z -> (B+Z.of_nat (length inp) < 2^64)%Z ->
  (1 <= Z.of_nat (length inp) <= 1048576)%Z -> (1 <= k <= 255)%Z ->
  (0 <= i <= Z.of_nat (length inp))%Z -> (Z.of_nat (length inp) < i+k)%Z -> (i mod k = 0)%Z ->
  (0 <= q < 2^32)%Z -> crc_model q (skipn (Z.to_nat i) inp) = crc_model 0 inp ->
  stk rsegs m lo (bv_unsigned sp) -> (lo+80 <= bv_unsigned sp)%Z ->
  (B+Z.of_nat (length inp) <= bv_unsigned sp-80 \/ bv_unsigned sp <= B)%Z ->
  (CRC_TABS+5120 <= bv_unsigned sp-80 \/ bv_unsigned sp <= CRC_TABS)%Z ->
  (forall h5 h6 h7 h11 h12 h13 h14 h15 h16 h17 h24 h28 h29 h30 h31 m2,
    munch [(bv_unsigned sp-80,bv_unsigned sp)]%Z m m2 -> wmono rsegs m m2 ->
    stk rsegs m2 lo (bv_unsigned sp) -> bytes_at rsegs m2 B inp -> bytes_at rsegs m2 CRC_TABS crc_table_bytes ->
    evt rsegs Q (MS (mkR (Z_to_bv 64 0x1434c) sp gp tp h5 h6 h7 (Z_to_bv 64 (Z.of_nat (length inp))) (Z_to_bv 64 B) (Z_to_bv 64 (crc_model 0 inp)) h11 h12 h13 h14 h15 h16 h17 s2 (Z_to_bv 64 (Z.of_nat (length inp))) (Z_to_bv 64 k) (Z_to_bv 64 (Z.of_nat (length inp)-i)) (Z_to_bv 64 0) (Z_to_bv 64 (crc_model 0 inp)) h24 s9 (Z_to_bv 64 4294967295) s11 h28 h29 h30 h31) F (Z_to_bv 64 0x14354) fc None m2 (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (Z.of_nat (length inp))) (Z_to_bv 64 B) (Z_to_bv 64 i) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (Z.of_nat (length inp))) (Z_to_bv 64 k) old5 (Z_to_bv 64 0) (Z_to_bv 64 q) s8 s9 (Z_to_bv 64 4294967295) s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14320) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s2 a1 a2 a3 a4 a5 a6 a7 old5 s8 s9 s11 t3 t4 t5 t6 F fc lo B k i q inp m Q INP TABLE HB TOP SIZE HK HI END IMOD HQ INV ST LO DI DT CONT.
  remember (crc_model 0 inp) as answer eqn:DANS in *.
  assert (HANS : (0 <= answer < 2^32)%Z) by (rewrite DANS;apply crc_model_range;lia).
  assert (RM : (Z.of_nat (length inp) mod k = Z.of_nat (length inp)-i)%Z) by (apply fuzzer_remainder_mod;lia).
  set (rest := skipn (Z.to_nat i) inp).
  assert (LR : Z.of_nat (length rest) = (Z.of_nat (length inp)-i)%Z).
  { unfold rest. rewrite skipn_length. lia. }
  assert (REST : bytes_at rsegs m (B+i) rest).
  { replace (B+i)%Z with (B+Z.of_nat (Z.to_nat i))%Z by lia. apply fuzzer_bytes_suffix;[exact INP|lia]. }
  assert (UQ : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit;lia).
  assert (UN : bv_unsigned (Z_to_bv 64 (Z.of_nat (length inp))) = Z.of_nat (length inp)) by (apply unsigned_lit;lia).
  assert (UK : bv_unsigned (Z_to_bv 64 k) = k) by (apply unsigned_lit;lia).
  assert (RW : mul_div M_REMU (Z_to_bv 64 (Z.of_nat (length inp))) (Z_to_bv 64 k) = Z_to_bv 64 (Z.of_nat (length inp)-i)).
  { unfold mul_div. rewrite UK. assert (NK : (k =? 0) = false) by (apply Z.eqb_neq;lia). rewrite NK.
    apply bv_eq.
    change (bv_unsigned (Z_to_bv 64 (Z.of_nat (length inp))) mod bv_unsigned (Z_to_bv 64 k) = bv_unsigned (Z_to_bv 64 (Z.of_nat (length inp)-i)))%Z.
    rewrite UN,UK,RM. symmetry. apply unsigned_lit;lia. }
  idtac "CRC REMAINDER first call". do 5 zstep.
  rewrite RW. rewrite <- LR.
  eapply evt_cut.
  - apply crc32_z_nonnull_spec with (B:=(B+i)%Z) (inp:=rest) (lo:=lo);
      [exact REST|exact TABLE|lia|rewrite LR;lia|rewrite LR;lia|exact ST|exact LO|unfold CRC_FRAME;rewrite LR;lia|exact DT].
  - intros final HP. unfold crc32_value_post in HP.
    destruct HP as (g5 & g6 & g7 & g11 & g12 & g13 & g14 & g15 & g16 & g17 & g28 & g29 & g30 & g31 & m1 & HS & MU & WM & ST1). subst final.
    rewrite UQ. rewrite (Z.mod_small q (2^32) HQ). unfold rest. rewrite INV.
    assert (INP1 : bytes_at rsegs m1 B inp).
    { eapply bytes_at_transport;[exact INP|exact MU|]. cbn [disjoint_from]. split;[exact DI|exact I]. }
    assert (TABLE1 : bytes_at rsegs m1 CRC_TABS crc_table_bytes).
    { eapply bytes_at_transport;[exact TABLE|exact MU|]. cbn [disjoint_from]. split;[exact DT|exact I]. }
    replace (ret_pc (Z_to_bv 64 0x14334)) with (Z_to_bv 64 0x14334) by (apply bv_eq;vm_compute;reflexivity).
    idtac "CRC REMAINDER oneshot". do 6 zstep.
    eapply evt_cut.
    + apply crc32_nonnull_spec with (lo:=lo);try assumption. lia.
    + intros final HP. unfold crc32_value_post in HP.
      destruct HP as (h5 & h6 & h7 & h11 & h12 & h13 & h14 & h15 & h16 & h17 & h28 & h29 & h30 & h31 & m2 & HS & MU2 & WM2 & ST2). subst final.
      change (bv_unsigned (Z_to_bv 64 0) mod 2^32)%Z with 0%Z. rewrite <- DANS.
      assert (INP2 : bytes_at rsegs m2 B inp).
      { eapply bytes_at_transport;[exact INP1|exact MU2|]. cbn [disjoint_from]. split;[exact DI|exact I]. }
      assert (TABLE2 : bytes_at rsegs m2 CRC_TABS crc_table_bytes).
      { eapply bytes_at_transport;[exact TABLE1|exact MU2|]. cbn [disjoint_from]. split;[exact DT|exact I]. }
      replace (ret_pc (Z_to_bv 64 0x1434c)) with (Z_to_bv 64 0x1434c) by (apply bv_eq;vm_compute;reflexivity).
      idtac "CRC REMAINDER assertion". do 2 zstep.
      try (if_cases K;zify_cond K;try (exfalso;lia)).
      fold rest. rewrite LR.
      eapply CONT; [eapply munch_trans;[exact MU|exact MU2]|eapply wmono_trans;[exact WM|exact WM2]|exact ST2|exact INP2|exact TABLE2].
Qed.
