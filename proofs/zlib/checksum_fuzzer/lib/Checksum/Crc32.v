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
  CrcBodyEntry CrcWordBody CrcTailReturn CrcFrame CrcPrologue CrcSeed.
Local Opaque csteps raw_crc raw_byte.
Theorem crc32_z_nonnull_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 seed a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (lo B : Z) (inp : list byte) (m : word -> option byte),
  bytes_at rsegs m B inp -> bytes_at rsegs m CRC_TABS crc_table_bytes ->
  (0 < B)%Z -> (B+Z.of_nat (length inp) < 2^64)%Z ->
  (Z.of_nat (length inp) <= 1048576)%Z ->
  stk rsegs m lo (bv_unsigned sp) -> (lo+CRC_FRAME <= bv_unsigned sp)%Z ->
  (B+Z.of_nat (length inp) <= bv_unsigned sp-CRC_FRAME \/ bv_unsigned sp <= B)%Z ->
  (CRC_TABS+5120 <= bv_unsigned sp-CRC_FRAME \/ bv_unsigned sp <= CRC_TABS)%Z ->
  evt rsegs (crc32_value_post (crc_model (bv_unsigned seed mod 2^32) inp) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 seed (Z_to_bv 64 B) (Z_to_bv 64 (Z.of_nat (length inp))) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14580) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 seed a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo B inp m INP TABLE HB TOP SIZE ST LO DI DT.
  pose proof (bytes_at_bound _ _ _ _ INP) as BB.
  zstep. if_cases K;zify_cond K.
  { exfalso. clear -K HB TOP BB. lia. }
  eapply crc_save_frame with (B:=B) (inp:=inp);
    [exact INP|exact TABLE|exact ST|exact LO|exact DI|exact DT|].
  intros m1 junk MU WM ST1 FR INP1 TABLE1.
  eapply crc_seed_setup.
  replace (Z_to_bv 64 B) with (Z_to_bv 64 (B+0)) by (f_equal;ring).
  replace (Z_to_bv 64 (Z.of_nat (length inp))) with (Z_to_bv 64 (Z.of_nat (length inp)-0)) by (f_equal;ring).
  eapply crc_body_entry with (B:=B) (inp:=inp) (i:=0%Z) (q:=crc_seed seed) (answer:=raw_crc inp (crc_seed seed));
    [exact INP1|exact TABLE1|exact TOP|exact SIZE|lia|apply crc_seed_range|reflexivity|].
  unfold crc_word_cont.
  intros j qf HJ HQ RF h5 h6 h7 h8 h9 h13 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h28 h29 h30 h31.
  change (evt rsegs (crc32_value_post (Z.lxor (raw_crc inp (crc_seed seed)) CRC_MASK)
    ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp-CRC_FRAME)) gp tp h5 h6 h7 h8 h9
      (Z_to_bv 64 CRC_TABS) (Z_to_bv 64 (B+j)) (Z_to_bv 64 (Z.of_nat (length inp)-j)) h13
      (Z_to_bv 64 qf) h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 s9 s10 s11 h28 h29 h30 h31)
      F (Z_to_bv 64 0x14a60) fc None m1 (seg_rom rsegs))).
  rewrite <- RF.
  eapply crc_tail_returns with (sp:=sp) (m:=m) (junk:=junk);
    [exact INP1|exact TABLE1|exact TOP|exact MU|exact WM|exact LO|exact ST1|exact FR|exact HJ|exact HQ].
Qed.
Theorem crc32_nonnull_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 seed a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (lo B : Z) (inp : list byte) (m : word -> option byte),
  bytes_at rsegs m B inp -> bytes_at rsegs m CRC_TABS crc_table_bytes ->
  (0 < B)%Z -> (B+Z.of_nat (length inp) < 2^64)%Z ->
  (Z.of_nat (length inp) <= 1048576)%Z ->
  stk rsegs m lo (bv_unsigned sp) -> (lo+CRC_FRAME <= bv_unsigned sp)%Z ->
  (B+Z.of_nat (length inp) <= bv_unsigned sp-CRC_FRAME \/ bv_unsigned sp <= B)%Z ->
  (CRC_TABS+5120 <= bv_unsigned sp-CRC_FRAME \/ bv_unsigned sp <= CRC_TABS)%Z ->
  evt rsegs (crc32_value_post (crc_model (bv_unsigned seed mod 2^32) inp) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 seed (Z_to_bv 64 B) (Z_to_bv 64 (Z.of_nat (length inp))) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14be4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 seed a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo B inp m INP TABLE HB TOP SIZE ST LO DI DT.
  eapply crc_length_wrapper.
  assert (LN : (bv_unsigned (Z_to_bv 64 (Z.of_nat (length inp))) mod 2^32 = Z.of_nat (length inp))%Z).
  { rewrite Z_to_bv_unsigned,(bv_wrap_small 64 (Z.of_nat (length inp)) ltac:(change (0 <= Z.of_nat (length inp) < 2^64)%Z;lia)).
    apply Z.mod_small. lia. }
  rewrite LN. eapply crc32_z_nonnull_spec;
    [exact INP|exact TABLE|exact HB|exact TOP|exact SIZE|exact ST|exact LO|exact DI|exact DT].
Qed.
Theorem crc32_z_null_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : word -> option byte),
  stk rsegs m lo (bv_unsigned sp) -> evt rsegs (crc32_value_post 0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14580) fc None m (seg_rom rsegs)).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m ST.
  pose proof (munch_refl [(bv_unsigned sp-CRC_FRAME,bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  eapply crc_null_cert. finish.
Qed.
Theorem crc32_null_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : word -> option byte),
  stk rsegs m lo (bv_unsigned sp) -> evt rsegs (crc32_value_post 0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14be4) fc None m (seg_rom rsegs)).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m ST.
  eapply crc_length_wrapper. eapply crc32_z_null_spec. exact ST.
Qed.
