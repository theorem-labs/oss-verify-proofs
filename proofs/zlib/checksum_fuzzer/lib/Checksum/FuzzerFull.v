(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(** Complete actual valid-input fuzzer certificate, including both checksum phases, return, saved registers and the 192-byte write footprint. *)
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
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import FuzzerPrefix FuzzerSetup FuzzerCrcPhase FuzzerAdlerPhase FuzzerReturn.
Theorem fuzzer_valid_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (lo B : Z) (inp : list byte) (m : word -> option byte),
  bytes_at rsegs m B inp -> bytes_at rsegs m CRC_TABS crc_table_bytes ->
  bytes_at rsegs m X2N_TAB x2n_bytes -> bytes_at rsegs m 0x119e0 (le8 (Z_to_bv 64 ADLER_MAGIC)) ->
  (0 < B)%Z -> (B+Z.of_nat (length inp) < 2^64)%Z -> (1 <= Z.of_nat (length inp) <= 1048576)%Z ->
  stk rsegs m lo (bv_unsigned sp) -> (lo+192 <= bv_unsigned sp)%Z ->
  (B+Z.of_nat (length inp) <= bv_unsigned sp-192 \/ bv_unsigned sp <= B)%Z ->
  (CRC_TABS+5120 <= bv_unsigned sp-192 \/ bv_unsigned sp <= CRC_TABS)%Z ->
  (X2N_TAB+128 <= bv_unsigned sp-192 \/ bv_unsigned sp <= X2N_TAB)%Z ->
  (0x119e0+8 <= bv_unsigned sp-192 \/ bv_unsigned sp <= 0x119e0)%Z ->
  evt rsegs (fuzzer_value_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 B) (Z_to_bv 64 (Z.of_nat (length inp))) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x141f0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo B inp m INP TABLE XTABLE MAGIC HBUF TOP SIZE ST LO DI DT DX DM.
  pose proof (proj1 ST) as LON.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. change (0 <= bv_unsigned sp < 2^64)%Z in RSP.
  assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp-112)) = (bv_unsigned sp-112)%Z) by (apply unsigned_lit;lia).
  eapply fuzzer_valid_prefix with (lo:=lo);[exact SIZE|exact ST|exact LO|].
  intros m1 junk MU WM ST1 FR.
  assert (INP1 : bytes_at rsegs m1 B inp).
  { eapply bytes_at_transport;[exact INP|exact MU|]. cbn [disjoint_from]. split;[exact DI|exact I]. }
  assert (TABLE1 : bytes_at rsegs m1 CRC_TABS crc_table_bytes).
  { eapply bytes_at_transport;[exact TABLE|exact MU|]. cbn [disjoint_from]. rewrite crc_table_bytes_length. cbn. split;[exact DT|exact I]. }
  assert (X1 : bytes_at rsegs m1 X2N_TAB x2n_bytes).
  { eapply bytes_at_transport;[exact XTABLE|exact MU|]. cbn [disjoint_from]. rewrite x2n_bytes_length. cbn. split;[exact DX|exact I]. }
  assert (MAGIC1 : bytes_at rsegs m1 0x119e0 (le8 (Z_to_bv 64 ADLER_MAGIC))).
  { eapply bytes_at_transport;[exact MAGIC|exact MU|]. cbn [disjoint_from]. split;[exact DM|exact I]. }
  assert (RD : exists c, ov_read_bytes rsegs m1 (wa B) 1 = Some [c]).
  { pose proof (bytes_at_ov_read rsegs m1 B inp 0 1 INP1 ltac:(lia)) as HR.
    cbn [skipn] in HR. rewrite Z.add_0_r in HR.
    destruct inp as [|c tail];[cbn in SIZE;lia|exists c;exact HR]. }
  destruct RD as [c RD]. pose proof (fuzzer_chunk_bound c) as HK.
  eapply fuzzer_chunk_setup;
    [lia|exact SIZE|exact RD|exact X1|].
  intros h5 h6 h7 h10 h11 h12 h13 h14 h15 h16 h17 h28 h29 h30 h31.
  eapply fuzzer_crc_phase with (lo:=lo);
    [exact INP1|exact TABLE1|exact X1|exact HBUF|exact TOP|exact SIZE|exact HK|rewrite USP;exact ST1|rewrite USP;lia|rewrite USP;lia|rewrite USP;lia|rewrite USP;lia|].
  intros g1 g5 g6 g7 g10 g11 g12 g13 g14 g15 g16 g17 g22 g23 g24 g25 g27 g28 g29 g30 g31 m2 MU2 WM2 ST2 INP2.
  assert (MAGIC2 : bytes_at rsegs m2 0x119e0 (le8 (Z_to_bv 64 ADLER_MAGIC))).
  { eapply bytes_at_transport;[exact MAGIC1|exact MU2|]. cbn [disjoint_from]. rewrite USP. split;[change (0x119e0+8 <= bv_unsigned sp-112-80 \/ bv_unsigned sp-112 <= 0x119e0)%Z;lia|exact I]. }
  eapply fuzzer_adler_phase with (lo:=lo);
    [exact INP2|exact MAGIC2|exact HBUF|exact TOP|exact SIZE|exact HK|exact ST2|rewrite USP;lia|rewrite USP;lia|rewrite USP;lia|].
  intros v1 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 mfinal MU3 WM3 ST3.
  assert (MUC : munch [(bv_unsigned (Z_to_bv 64 (bv_unsigned sp-112))-80,bv_unsigned (Z_to_bv 64 (bv_unsigned sp-112)))]%Z m1 mfinal).
  { eapply munch_trans;[exact MU2|]. eapply munch_weaken;[|exact MU3].
    unfold sub_fp,outside. cbn. intros x HX. lia. }
  assert (WMALL : wmono rsegs m mfinal) by (eapply wmono_trans;[exact WM|eapply wmono_trans;eassumption]).
  assert (MUALL : munch [(bv_unsigned sp-192,bv_unsigned sp)]%Z m mfinal).
  { eapply munch_trans;[exact MU|]. eapply munch_weaken;[|exact MUC].
    unfold sub_fp,outside. cbn. rewrite USP. intros x HX. lia. }
  assert (FRFINAL : rw_cells rsegs mfinal (bv_unsigned sp-112)
    [CB 8 junk;C8 s11;C8 s10;C8 s9;C8 s8;C8 s7;C8 s6;C8 s5;C8 s4;C8 s3;C8 s2;C8 s1;C8 s0;C8 ra]).
  { eapply rw_cells_transport;[exact FR|exact MUC|eapply wmono_trans;eassumption|].
    cbn [disjoint_from]. rewrite USP. split;[right;lia|exact I]. }
  eapply fuzzer_return with (junk:=junk);
    [exact MUALL|exact WMALL|exact LO|rewrite <- USP;exact ST3|exact FRFINAL].
Qed.
