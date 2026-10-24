(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(** Termination and suffix checksum invariant of the actual repeated Adler loop. *)
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
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import FuzzerAdlerBody FuzzerSlices.
Section AdlerFuzzerLoop.
  Variables (sp gp tp s5 s7 s8 s9 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo B k answer : Z) (inp : list byte).
  Let n := Z.of_nat (length inp).
  Hypothesis SIZE : (1 <= n <= 1048576)%Z.
  Hypothesis HK : (1 <= k <= 255)%Z.
  Hypothesis HBUF : (0 < B)%Z.
  Hypothesis TOP : (B+n < 2^64)%Z.
  Hypothesis LO : (lo+32 <= bv_unsigned sp)%Z.
  Hypothesis DI : (B+n <= bv_unsigned sp-32 \/ bv_unsigned sp <= B)%Z.
  Hypothesis DT : (0x119e0+8 <= bv_unsigned sp-32 \/ bv_unsigned sp <= 0x119e0)%Z.
  Variable Q : machine_state -> Prop.
  Theorem fuzzer_adler_loop : forall (fuel : nat) (i a b : Z) (m : word -> option byte) (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    bytes_at rsegs m B inp -> bytes_at rsegs m 0x119e0 (le8 (Z_to_bv 64 ADLER_MAGIC)) ->
    stk rsegs m lo (bv_unsigned sp) -> (0 <= i)%Z -> (i+k <= n)%Z -> (n-i <= Z.of_nat fuel)%Z ->
    (0 <= a < ADLER_BASE)%Z -> (0 <= b < ADLER_BASE)%Z -> (i mod k = 0)%Z ->
    adler_model (adler_pack a b) (skipn (Z.to_nat i) inp) = answer ->
    (forall (j ao bo : Z) (mfinal : word -> option byte) (h5 h6 h7 h12 h13 h14 h15 h16 h17 h28 h29 h30 h31 : word),
      (0 <= j <= n)%Z -> (n < j+k)%Z -> (j mod k = 0)%Z ->
      (0 <= ao < ADLER_BASE)%Z -> (0 <= bo < ADLER_BASE)%Z ->
      adler_model (adler_pack ao bo) (skipn (Z.to_nat j) inp) = answer ->
      munch [(bv_unsigned sp-32,bv_unsigned sp)]%Z m mfinal -> wmono rsegs m mfinal ->
      stk rsegs mfinal lo (bv_unsigned sp) -> bytes_at rsegs mfinal B inp ->
      bytes_at rsegs mfinal 0x119e0 (le8 (Z_to_bv 64 ADLER_MAGIC)) ->
      evt rsegs Q (MS (mkR (Z_to_bv 64 0x14410) sp gp tp h5 h6 h7 (Z_to_bv 64 n) (Z_to_bv 64 B) (Z_to_bv 64 (adler_pack ao bo)) (Z_to_bv 64 j) h12 h13 h14 h15 h16 h17 (Z_to_bv 64 1) (Z_to_bv 64 n) (Z_to_bv 64 k) s5 (Z_to_bv 64 j) s7 s8 s9 (Z_to_bv 64 4294967295) s11 h28 h29 h30 h31) F (Z_to_bv 64 0x14424) fc None mfinal (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 B) (Z_to_bv 64 (adler_pack a b)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 1) (Z_to_bv 64 n) (Z_to_bv 64 k) s5 (Z_to_bv 64 i) s7 s8 s9 (Z_to_bv 64 4294967295) s11 t3 t4 t5 t6) F (Z_to_bv 64 0x143f8) fc None m (seg_rom rsegs)).
  Proof.
    induction fuel as [|fuel IH]; intros i a b m ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 INP TABLE ST HI GOOD BUD HA HB IMOD INV CONT.
    { cbn in BUD. exfalso. lia. }
    set (chunk := firstn (Z.to_nat k) (skipn (Z.to_nat i) inp)).
    assert (LK : Z.of_nat (length chunk) = k).
    { unfold chunk. rewrite fuzzer_slice_length by (unfold n in *;lia). rewrite Z2Nat.id by lia. reflexivity. }
    assert (CHUNK : bytes_at rsegs m (B+i) chunk).
    { replace (B+i)%Z with (B+Z.of_nat (Z.to_nat i))%Z by lia.
      apply fuzzer_bytes_slice; [exact INP|unfold n in *;lia]. }
    assert (IMODN : ((i+k) mod k = 0)%Z).
    { rewrite Z.add_mod,IMOD,Z.mod_same by lia. change ((0+0) mod k = 0)%Z. apply Z.mod_0_l. lia. }
    destruct (adler_output_components chunk a b) as (an & bn & HAN & HBN & DN).
    assert (INVN : adler_model (adler_pack an bn) (skipn (Z.to_nat (i+k)) inp) = answer).
    { rewrite <- DN, <- adler_model_packed by assumption. unfold chunk.
      replace (Z.to_nat (i+k)) with (Z.to_nat i+Z.to_nat k)%nat by lia.
      rewrite <- fuzzer_adler_suffix_chunk. exact INV. }
    eapply fuzzer_adler_chunk_iteration with (bs:=chunk) (lo:=lo);
      [exact HA|exact HB|exact SIZE|exact HK|exact HI|exact GOOD|exact LK|exact CHUNK|exact TABLE|exact HBUF|exact TOP|exact ST|exact LO|lia|exact DT| |].
    + intros h5 h6 h7 h12 h13 h14 h15 h16 h17 h28 h29 h30 h31 m1 END MU WM ST1 CHUNK1 TABLE1.
      assert (INP1 : bytes_at rsegs m1 B inp).
      { eapply bytes_at_transport;[exact INP|exact MU|]. cbn [disjoint_from]. split;[exact DI|exact I]. }
      rewrite DN.
      eapply IH with (i:=(i+k)%Z) (a:=an) (b:=bn) (m:=m1);
        [exact INP1|exact TABLE1|exact ST1|lia|exact END|rewrite Nat2Z.inj_succ in BUD;lia|exact HAN|exact HBN|exact IMODN|exact INVN|].
      intros j ao bo mfinal zh5 zh6 zh7 zh12 zh13 zh14 zh15 zh16 zh17 zh28 zh29 zh30 zh31 HJ BAD JMOD HAO HBO INVR MU2 WM2 ST2 INP2 TABLE2.
      eapply CONT;[exact HJ|exact BAD|exact JMOD|exact HAO|exact HBO|exact INVR|eapply munch_trans;[exact MU|exact MU2]|eapply wmono_trans;[exact WM|exact WM2]|exact ST2|exact INP2|exact TABLE2].
    + intros h5 h6 h7 h12 h13 h14 h15 h16 h17 h28 h29 h30 h31 m1 END MU WM ST1 CHUNK1 TABLE1.
      assert (INP1 : bytes_at rsegs m1 B inp).
      { eapply bytes_at_transport;[exact INP|exact MU|]. cbn [disjoint_from]. split;[exact DI|exact I]. }
      rewrite DN.
      eapply CONT;[lia|exact END|exact IMODN|exact HAN|exact HBN|exact INVN|exact MU|exact WM|exact ST1|exact INP1|exact TABLE1].
  Qed.
End AdlerFuzzerLoop.
