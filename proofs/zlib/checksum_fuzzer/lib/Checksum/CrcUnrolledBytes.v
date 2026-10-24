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

Lemma crc_loaded_byte_value : forall q (b : byte), (0 <= q < 2^32)%Z ->
  Z.lxor (Z.shiftr q 8) (bv_unsigned (zx32 (Z_to_bv 64
    (csteps 8 (Z.land (Z.lxor (bv_unsigned b) q) 255))))) = raw_byte q b.
Proof.
  intros q b Hq. pose proof (byte_unsigned_range b) as Hb.
  pose proof (land255_range (Z.lxor (bv_unsigned b) q)) as Hi.
  pose proof (csteps_range 8 (Z.land (Z.lxor (bv_unsigned b) q) 255) ltac:(lia)) as HT.
  rewrite (Exec.DA_Myrk.zx32_small _ HT),Z_to_bv_unsigned.
  unfold bv_wrap. change (bv_modulus 64) with (2^64)%Z.
  rewrite Z.mod_small by lia. unfold raw_byte.
  rewrite (byte_table_step q (bv_unsigned b) Hq Hb),(Z.lxor_comm (bv_unsigned b) q).
  apply Z.lxor_comm.
Qed.

Section UnrolledBytes.
  Variables (ra sp gp tp t2 s0 s1 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Hypothesis TABLE : bytes_at rsegs m CRC_TABS crc_table_bytes.
  Variable Q : machine_state -> Prop.
  Notation AT pc x5 x6 x11 x12 x13 x14 x16 x17 :=
    (MS (mkR ra sp gp tp x5 x6 t2 s0 s1 (Z_to_bv 64 CRC_TABS)
      x11 x12 x13 x14 a5 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
  Lemma unrolled_byte_a6 : forall (start q : Z) (b : byte) x5 x6 x17 x11 x12 x13,
    (start=0x14a80 \/ start=0x14b00)%Z -> (0 <= q < 2^32)%Z ->
    (forall x16', evt rsegs Q (AT (start+28) x5 x6 x11 x12 x13
      (Z_to_bv 64 (raw_byte q b)) x16' x17)) ->
    evt rsegs Q (AT start x5 x6 x11 x12 x13
      (Z_to_bv 64 q) (Z_to_bv 64 (bv_unsigned b)) x17).
  Proof.
    intros start q b x5 x6 x17 x11 x12 x13 HPC Hq CONT.
    pose proof (byte_unsigned_range b) as Hb.
    pose proof (land255_range (Z.lxor (bv_unsigned b) q)) as Hi.
    pose proof (crc_byte_table_at m (Z.land (Z.lxor (bv_unsigned b) q) 255) TABLE ltac:(lia)) as RT.
    replace (4*Z.land (Z.lxor (bv_unsigned b) q) 255)%Z with
      (Z.shiftl (Z.land (Z.lxor (bv_unsigned b) q) 255) 2) in RT
      by (rewrite Z.shiftl_mul_pow2 by lia;ring).
    destruct HPC as [HPC|HPC]; subst start.
    all: do 7 zstep; rewrite (crc_loaded_byte_value q b Hq); apply CONT.
  Qed.
  Lemma unrolled_byte_a7 : forall (start q : Z) (b : byte) x5 x6 x16 x11 x12 x13,
    (start=0x14a9c \/ start=0x14b1c)%Z -> (0 <= q < 2^32)%Z ->
    (forall x16', evt rsegs Q (AT (start+28) x5 x6 x11 x12 x13
      (Z_to_bv 64 (raw_byte q b)) x16' (Z_to_bv 64 (bv_unsigned b)))) ->
    evt rsegs Q (AT start x5 x6 x11 x12 x13
      (Z_to_bv 64 q) x16 (Z_to_bv 64 (bv_unsigned b))).
  Proof.
    intros start q b x5 x6 x16 x11 x12 x13 HPC Hq CONT.
    pose proof (byte_unsigned_range b) as Hb.
    pose proof (land255_range (Z.lxor (bv_unsigned b) q)) as Hi.
    pose proof (crc_byte_table_at m (Z.land (Z.lxor (bv_unsigned b) q) 255) TABLE ltac:(lia)) as RT.
    replace (4*Z.land (Z.lxor (bv_unsigned b) q) 255)%Z with
      (Z.shiftl (Z.land (Z.lxor (bv_unsigned b) q) 255) 2) in RT
      by (rewrite Z.shiftl_mul_pow2 by lia;ring).
    destruct HPC as [HPC|HPC]; subst start.
    all: do 7 zstep; rewrite (crc_loaded_byte_value q b Hq); apply CONT.
  Qed.
  Lemma unrolled_byte_t0 : forall (start q : Z) (b : byte) x6 x16 x17 x11 x12 x13,
    (start=0x14ab8 \/ start=0x14b38)%Z -> (0 <= q < 2^32)%Z ->
    (forall x16', evt rsegs Q (AT (start+28) (Z_to_bv 64 (bv_unsigned b)) x6 x11 x12 x13
      (Z_to_bv 64 (raw_byte q b)) x16' x17)) ->
    evt rsegs Q (AT start (Z_to_bv 64 (bv_unsigned b)) x6 x11 x12 x13
      (Z_to_bv 64 q) x16 x17).
  Proof.
    intros start q b x6 x16 x17 x11 x12 x13 HPC Hq CONT.
    pose proof (byte_unsigned_range b) as Hb.
    pose proof (land255_range (Z.lxor (bv_unsigned b) q)) as Hi.
    pose proof (crc_byte_table_at m (Z.land (Z.lxor (bv_unsigned b) q) 255) TABLE ltac:(lia)) as RT.
    replace (4*Z.land (Z.lxor (bv_unsigned b) q) 255)%Z with
      (Z.shiftl (Z.land (Z.lxor (bv_unsigned b) q) 255) 2) in RT
      by (rewrite Z.shiftl_mul_pow2 by lia;ring).
    destruct HPC as [HPC|HPC]; subst start.
    all: do 7 zstep; rewrite (crc_loaded_byte_value q b Hq); apply CONT.
  Qed.
  Lemma unrolled_byte_t1 : forall (start q : Z) (b : byte) x5 x16 x17 x11 x12 x13,
    (start=0x14ad4)%Z -> (0 <= q < 2^32)%Z ->
    (forall x16', evt rsegs Q (AT (start+28) x5 (Z_to_bv 64 (bv_unsigned b)) x11 x12 x13
      (Z_to_bv 64 (raw_byte q b)) x16' x17)) ->
    evt rsegs Q (AT start x5 (Z_to_bv 64 (bv_unsigned b)) x11 x12 x13
      (Z_to_bv 64 q) x16 x17).
  Proof.
    intros start q b x5 x16 x17 x11 x12 x13 HPC Hq CONT.
    pose proof (byte_unsigned_range b) as Hb.
    pose proof (land255_range (Z.lxor (bv_unsigned b) q)) as Hi.
    pose proof (crc_byte_table_at m (Z.land (Z.lxor (bv_unsigned b) q) 255) TABLE ltac:(lia)) as RT.
    replace (4*Z.land (Z.lxor (bv_unsigned b) q) 255)%Z with
      (Z.shiftl (Z.land (Z.lxor (bv_unsigned b) q) 255) 2) in RT
      by (rewrite Z.shiftl_mul_pow2 by lia;ring).
    subst start.
    all: do 7 zstep; rewrite (crc_loaded_byte_value q b Hq); apply CONT.
  Qed.
  Lemma unrolled_byte_last : forall (q : Z) (b : byte) x5 x16 x17 x11 x12 x13,
    (0 <= q < 2^32)%Z ->
    (forall x16', evt rsegs Q
      (AT 0x14b78 x5 (Z_to_bv 64 (bv_unsigned b))
        (Z_to_bv 64 (bv_unsigned x11+8)) (Z_to_bv 64 (bv_unsigned x12-8)) x13
        (Z_to_bv 64 (raw_byte q b)) x16' x17)) ->
    evt rsegs Q (AT 0x14b54 x5 (Z_to_bv 64 (bv_unsigned b)) x11 x12 x13
      (Z_to_bv 64 q) x16 x17).
  Proof.
    intros q b x5 x16 x17 x11 x12 x13 Hq CONT.
    pose proof (byte_unsigned_range b) as Hb.
    pose proof (land255_range (Z.lxor (bv_unsigned b) q)) as Hi.
    pose proof (crc_byte_table_at m (Z.land (Z.lxor (bv_unsigned b) q) 255) TABLE ltac:(lia)) as RT.
    replace (4*Z.land (Z.lxor (bv_unsigned b) q) 255)%Z with
      (Z.shiftl (Z.land (Z.lxor (bv_unsigned b) q) 255) 2) in RT
      by (rewrite Z.shiftl_mul_pow2 by lia;ring).
    do 9 zstep. rewrite (crc_loaded_byte_value q b Hq). apply CONT.
  Qed.
End UnrolledBytes.
