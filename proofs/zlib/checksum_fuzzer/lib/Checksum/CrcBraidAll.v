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
  CrcBraidLoop CrcBraidMachine CrcBraidWord CrcBraidModel CrcWordChunks CrcWord CrcMergeMachine.
Local Opaque csteps SX merge_model block5.
Section BraidAll.
  Variables (ra sp gp tp a2 a3 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (B ending : Z) (inp : list byte).
  Hypothesis INP : bytes_at rsegs m B inp.
  Hypothesis TABLE : bytes_at rsegs m CRC_TABS crc_table_bytes.
  Hypothesis TOP : (B+Z.of_nat (length inp) < 2^64)%Z.
  Hypothesis LEN : Z_to_bv 64 (bv_unsigned a3+bv_unsigned a2) =
    Z_to_bv 64 (Z.of_nat (length inp)-(ending+20)).
  Variable Q : machine_state -> Prop.
  Notation AT pc x5 x8 x9 x11 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x31 :=
    (MS (mkR ra sp gp tp x5 (Z_to_bv 64 (B+ending)) (Z_to_bv 64 0x10954) x8 x9 (Z_to_bv 64 CRC_TABS)
      x11 a2 a3 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 s9 s10 s11
      (Z_to_bv 64 0x10d54) (Z_to_bv 64 0x11154) (Z_to_bv 64 0x11554) x31)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
  Definition crc_braid_tail_cont (answer : Z) : Prop :=
    forall qf, (0 <= qf < 2^32)%Z -> raw_crc (skipn (Z.to_nat (ending+20)) inp) qf = answer ->
    forall h5 h6 h7 h8 h9 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h28 h29 h31,
    evt rsegs Q (MS (mkR ra sp gp tp h5 h6 h7 h8 h9 (Z_to_bv 64 CRC_TABS)
      (Z_to_bv 64 (B+(ending+20))) (Z_to_bv 64 (Z.of_nat (length inp)-(ending+20))) a3
      (Z_to_bv 64 qf) h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 s9 s10 s11 h28 h29
      (Z_to_bv 64 0x11554) h31) F (Z_to_bv 64 0x14a60) fc None m (seg_rom rsegs)).
  Theorem crc_braid_all : forall (n : nat) (i q R0 R1 R2 R3 R4 answer : Z)
    g8 g9 g18 g19 g20 g21 g22 g23 g24 g31,
    (ending=i+20*Z.of_nat (S n))%Z -> (0 <= i)%Z -> (ending+20 <= Z.of_nat (length inp))%Z ->
    (0 <= q < 2^32)%Z ->
    (0 <= R0 < 2^64)%Z -> (0 <= R1 < 2^64)%Z -> (0 <= R2 < 2^64)%Z ->
    (0 <= R3 < 2^64)%Z -> (0 <= R4 < 2^64)%Z ->
    merge5 (R0 mod 2^32) (R1 mod 2^32) (R2 mod 2^32) (R3 mod 2^32) (R4 mod 2^32) = csteps 128 q ->
    raw_crc (skipn (Z.to_nat i) inp) q = answer ->
    crc_braid_tail_cont answer ->
    evt rsegs Q
      (AT 0x14674 (Z_to_bv 64 R1) g8 g9 (Z_to_bv 64 (B+i))
        (Z_to_bv 64 R0) (Z_to_bv 64 R4) (Z_to_bv 64 R3) (Z_to_bv 64 R2)
        g18 g19 g20 g21 g22 g23 g24 g31).
  Proof.
    intros n i q R0 R1 R2 R3 R4 answer g8 g9 g18 g19 g20 g21 g22 g23 g24 g31 END Hi HL Hq HR0 HR1 HR2 HR3 HR4 MC REM CONT.
    eapply crc_braid_loop with (n:=n) (q:=q) (answer:=answer);
      [exact INP|exact TABLE|exact TOP|exact END|exact Hi|exact HL|exact Hq|
       exact HR0|exact HR1|exact HR2|exact HR3|exact HR4|exact MC|exact REM|].
    unfold braid_loop_cont.
    intros qf F0 F1 F2 F3 F4 HF HF0 HF1 HF2 HF3 HF4 MCF REMF h8 h9 h18 h19 h20 h21 h22 h23 h24 h31.
    eapply crc_braid_merge;
      [exact INP|exact TABLE|clear -END Hi;lia|exact HL|exact HF0|exact HF1|exact HF2|exact HF3|exact HF4|].
    intros h5 h6 h7 h15 h16 h17 h28 h29.
    rewrite LEN,merge_model_finish,(braid_finish_serial qf _ _ _ _ _ _ _ _ _ _ MCF).
    pose proof (bword4_unsigned_range inp ending) as HW0.
    pose proof (bword4_unsigned_range inp (ending+4)) as HW1.
    pose proof (bword4_unsigned_range inp (ending+8)) as HW2.
    pose proof (bword4_unsigned_range inp (ending+12)) as HW3.
    pose proof (bword4_unsigned_range inp (ending+16)) as HW4.
    pose proof (block5_range qf _ _ _ _ _ HF HW0 HW1 HW2 HW3 HW4) as HFINAL.
    rewrite (raw_suffix_twenty inp ending qf ltac:(clear -END Hi;lia) HL) in REMF.
    unfold crc_braid_tail_cont in CONT.
    exact (CONT _ HFINAL REMF h5 h6 h7 h8 h9 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h28 h29 h31).
  Qed.
End BraidAll.
