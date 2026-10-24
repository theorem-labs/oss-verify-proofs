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

From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import
  CrcTailMachine CrcUnrolledBlock CrcChunks.
Section CrcTailControl.
  Variables (ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (B : Z) (inp : list byte).
  Hypothesis INP : bytes_at rsegs m B inp.
  Hypothesis TABLE : bytes_at rsegs m CRC_TABS crc_table_bytes.
  Hypothesis TOP : (B+Z.of_nat (length inp) < 2^64)%Z.
  Variable Q : machine_state -> Prop.
  Notation L := (Z.of_nat (length inp)).
  Notation AT pc x5 x6 x11 x12 x13 x14 x15 x16 x17 :=
    (MS (mkR ra sp gp tp x5 x6 t2 s0 s1 (Z_to_bv 64 CRC_TABS)
      x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
  Definition crc_tail_cont (i q : Z) (x5 x6 x17 : word) : Prop :=
    forall x11 x12 x15 x16, evt rsegs Q
      (AT 0x14bb4 x5 x6 x11 x12 (Z_to_bv 64 CRC_MASK)
        (Z_to_bv 64 (raw_crc (skipn (Z.to_nat i) inp) q)) x15 x16 x17).

  Lemma crc_tail_entry : forall (i q : Z) x5 x6 x15 x16 x17,
    (0 <= i <= L)%Z -> (0 <= q < 2^32)%Z ->
    crc_tail_cont i q x5 x6 x17 ->
    evt rsegs Q (AT 0x14b7c x5 x6 (Z_to_bv 64 (B+i)) (Z_to_bv 64 (L-i))
      (Z_to_bv 64 (-1)) (Z_to_bv 64 q) x15 x16 x17).
  Proof.
    intros i q x5 x6 x15 x16 x17 Hi Hq CONT. unfold crc_tail_cont in CONT.
    pose proof (bytes_at_bound _ _ _ _ INP) as BB.
    do 2 zstep. if_cases K;zify_cond K.
    - assert (E : i=L) by lia. subst i.
      rewrite Nat2Z.id,skipn_all in CONT. cbn [raw_crc] in CONT. apply CONT.
    - zstep. replace (B+i+(L-i))%Z with (B+L)%Z by lia.
      eapply tail_byte_loop with (k:=Z.to_nat (L-i));
        [exact INP|exact TABLE|exact TOP|reflexivity|lia|exact Hq|].
      intros. apply CONT.
  Qed.

  Lemma crc_unrolled_loop : forall (k : nat) (i q : Z) x5 x6 x16 x17,
    k=Z.to_nat (L-i) -> (0 <= i)%Z -> (i+8 <= L)%Z -> (0 <= q < 2^32)%Z ->
    (forall x5' x6' x17', crc_tail_cont i q x5' x6' x17') ->
    evt rsegs Q (AT 0x14a70 x5 x6 (Z_to_bv 64 (B+i)) (Z_to_bv 64 (L-i))
      (Z_to_bv 64 (-1)) (Z_to_bv 64 q) (Z_to_bv 64 7) x16 x17).
  Proof.
    induction k as [k IH] using lt_wf_ind;intros i q x5 x6 x16 x17 Hk Hi HL Hq CONT.
    pose proof (bytes_at_bound _ _ _ _ INP) as BB.
    unfold crc_tail_cont in CONT.
    rewrite (raw_suffix_eight inp i q Hi) in CONT.
    eapply unrolled8_update;
      [exact INP|exact TABLE|exact TOP|exact Hi|exact HL|exact Hq|].
    intros x5' x6' x16' x17'. zstep. if_cases K;zify_cond K.
    - eapply (IH (Z.to_nat (L-(i+8))) ltac:(lia) (i+8)%Z (eight_crc inp i q));
        [reflexivity|lia|lia|apply eight_crc_range;exact Hq|].
      unfold crc_tail_cont. exact CONT.
    - eapply crc_tail_entry;[lia|apply eight_crc_range;exact Hq|].
      unfold crc_tail_cont. apply CONT.
  Qed.

  Theorem crc_tail_all : forall (i q : Z) x5 x6 x13 x15 x16 x17,
    (0 <= i <= L)%Z -> (0 <= q < 2^32)%Z ->
    (forall x5' x6' x17', crc_tail_cont i q x5' x6' x17') ->
    evt rsegs Q (AT 0x14a60 x5 x6 (Z_to_bv 64 (B+i)) (Z_to_bv 64 (L-i))
      x13 (Z_to_bv 64 q) x15 x16 x17).
  Proof.
    intros i q x5 x6 x13 x15 x16 x17 Hi Hq CONT.
    pose proof (bytes_at_bound _ _ _ _ INP) as BB.
    do 3 zstep. if_cases K;zify_cond K.
    - eapply crc_tail_entry;[exact Hi|exact Hq|apply CONT].
    - zstep. eapply crc_unrolled_loop with (k:=Z.to_nat (L-i));
        [reflexivity|lia|lia|exact Hq|exact CONT].
  Qed.
End CrcTailControl.
