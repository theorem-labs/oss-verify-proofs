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

From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import CrcBraidWord CrcBraidModel CrcWord.
Lemma sx32_bword4 : forall bs k,
  sx32 (bword4 bs k) = Z_to_bv 64 (SX (bv_unsigned (bword4 bs k))).
Proof. intros. apply sx32_SX;[reflexivity|apply bword4_unsigned_range]. Qed.
Local Ltac braid_norm :=
  repeat match goal with
  | |- context [sx32 (bword4 ?bs ?k)] => rewrite (sx32_bword4 bs k)
  | |- context [sx32 (Z_to_bv 64 (braid_part ?a ?j))] =>
      rewrite (sx32_of_small (braid_part a j) (braid_part_range a j))
  | |- context [bv_swrap 32 (Z.shiftr (bv_wrap 32 ?a) 24)] => rewrite (srliw24_raw a)
  end.
Section BraidInstructionBlock.
  Variables (ra sp gp tp t1 a2 a3 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (B : Z) (inp : list byte).
  Hypothesis INP : bytes_at rsegs m B inp.
  Hypothesis TABLE : bytes_at rsegs m CRC_TABS crc_table_bytes.
  Variable Q : machine_state -> Prop.
  Notation AT pc x5 x8 x9 x11 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x31 :=
    (MS (mkR ra sp gp tp x5 t1 (Z_to_bv 64 0x10954) x8 x9 (Z_to_bv 64 CRC_TABS)
      x11 a2 a3 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 s9 s10 s11
      (Z_to_bv 64 0x10d54) (Z_to_bv 64 0x11154) (Z_to_bv 64 0x11554) x31)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
  Theorem crc_braid_iteration : forall (i R0 R1 R2 R3 R4 : Z)
    g8 g9 g18 g19 g20 g21 g22 g23 g24 g31,
    (0 <= i)%Z -> (i+20 <= Z.of_nat (length inp))%Z ->
    (0 <= R0 < 2^64)%Z -> (0 <= R1 < 2^64)%Z -> (0 <= R2 < 2^64)%Z ->
    (0 <= R3 < 2^64)%Z -> (0 <= R4 < 2^64)%Z ->
    (forall h8 h9 h18 h19 h20 h21 h22 h23 h24 h31, evt rsegs Q
      (AT 0x1481c (Z_to_bv 64 (SX (csteps 160 (Z.lxor (R1 mod 2^32) (bv_unsigned (bword4 inp (i+4))))))) h8 h9 (Z_to_bv 64 (B+(i+20)))
        (Z_to_bv 64 (SX (csteps 160 (Z.lxor (R0 mod 2^32) (bv_unsigned (bword4 inp i)))))) (Z_to_bv 64 (SX (csteps 160 (Z.lxor (R4 mod 2^32) (bv_unsigned (bword4 inp (i+16))))))) (Z_to_bv 64 (SX (csteps 160 (Z.lxor (R3 mod 2^32) (bv_unsigned (bword4 inp (i+12))))))) (Z_to_bv 64 (SX (csteps 160 (Z.lxor (R2 mod 2^32) (bv_unsigned (bword4 inp (i+8))))))) h18 h19 h20 h21 h22 h23 h24 h31)) ->
    evt rsegs Q
      (AT 0x14674 (Z_to_bv 64 R1) g8 g9 (Z_to_bv 64 (B+i))
        (Z_to_bv 64 R0) (Z_to_bv 64 R4) (Z_to_bv 64 R3) (Z_to_bv 64 R2)
        g18 g19 g20 g21 g22 g23 g24 g31).
  Proof.
    intros i R0 R1 R2 R3 R4 g8 g9 g18 g19 g20 g21 g22 g23 g24 g31 Hi HL HR0 HR1 HR2 HR3 HR4 CONT.
    pose proof (bytes_at_bound _ _ _ _ INP) as BB.
    set (W0 := (bv_unsigned (bword4 inp i))).
    assert (HW0 : (0 <= W0 < 2^32)%Z) by (unfold W0;apply bword4_unsigned_range).
    pose proof (SX_range W0 HW0) as HSW0.
    set (C0 := Z.lxor (SX W0) R0).
    assert (HC0 : (0 <= C0 < 2^64)%Z) by (unfold C0;apply lxor_bound;[lia|exact HSW0|exact HR0]).
    assert (EC0 : (C0 mod 2^32 = Z.lxor (R0 mod 2^32) W0)%Z).
    { unfold C0. rewrite low32_xor,(SX_mod32 W0 HW0). apply Z.lxor_comm. }
    pose proof (crc_braid_table_read m 0 C0 TABLE ltac:(lia) HC0) as RT00.
    change (ov_read_bytes rsegs m (wa (0x10954+(Z.shiftl (Z.land C0 255) 2))) 4 = Some (le4 (Z_to_bv 64 (braid_part C0 0)))) in RT00.
    pose proof (braid_part_range C0 0) as HP00.
    pose proof (SX_range (braid_part C0 0) HP00) as HSP00.
    pose proof (crc_braid_table_read m 1 C0 TABLE ltac:(lia) HC0) as RT01.
    change (ov_read_bytes rsegs m (wa (0x10d54+(Z.land (Z.shiftr C0 6) 1020))) 4 = Some (le4 (Z_to_bv 64 (braid_part C0 1)))) in RT01.
    pose proof (braid_part_range C0 1) as HP01.
    pose proof (SX_range (braid_part C0 1) HP01) as HSP01.
    pose proof (crc_braid_table_read m 2 C0 TABLE ltac:(lia) HC0) as RT02.
    change (ov_read_bytes rsegs m (wa (0x11154+(Z.land (Z.shiftr C0 14) 1020))) 4 = Some (le4 (Z_to_bv 64 (braid_part C0 2)))) in RT02.
    pose proof (braid_part_range C0 2) as HP02.
    pose proof (SX_range (braid_part C0 2) HP02) as HSP02.
    pose proof (crc_braid_table_read m 3 C0 TABLE ltac:(lia) HC0) as RT03.
    change (ov_read_bytes rsegs m (wa (0x11554+(Z.shiftl (Z.shiftr (C0 mod 2^32) 24) 2))) 4 = Some (le4 (Z_to_bv 64 (braid_part C0 3)))) in RT03.
    pose proof (braid_part_range C0 3) as HP03.
    pose proof (SX_range (braid_part C0 3) HP03) as HSP03.
    assert (HL0 : (0 <= Z.lxor (SX (braid_part C0 0)) (SX (braid_part C0 1)) < 2^64)%Z) by (apply lxor_bound;lia).
    assert (HH0 : (0 <= Z.lxor (SX (braid_part C0 3)) (SX (braid_part C0 2)) < 2^64)%Z) by (apply lxor_bound;lia).
    assert (HV0 : (0 <= Z.lxor (Z.lxor (SX (braid_part C0 3)) (SX (braid_part C0 2))) (Z.lxor (SX (braid_part C0 0)) (SX (braid_part C0 1))) < 2^64)%Z) by (apply lxor_bound;lia).
    pose proof (braid_signed_value C0) as VAL0. rewrite EC0 in VAL0.
    rewrite (Z.lxor_comm (SX (braid_part C0 0)) (SX (braid_part C0 1))) in VAL0.
    set (W1 := (bv_unsigned (bword4 inp (i+4)))).
    assert (HW1 : (0 <= W1 < 2^32)%Z) by (unfold W1;apply bword4_unsigned_range).
    pose proof (SX_range W1 HW1) as HSW1.
    set (C1 := Z.lxor (SX W1) R1).
    assert (HC1 : (0 <= C1 < 2^64)%Z) by (unfold C1;apply lxor_bound;[lia|exact HSW1|exact HR1]).
    assert (EC1 : (C1 mod 2^32 = Z.lxor (R1 mod 2^32) W1)%Z).
    { unfold C1. rewrite low32_xor,(SX_mod32 W1 HW1). apply Z.lxor_comm. }
    pose proof (crc_braid_table_read m 0 C1 TABLE ltac:(lia) HC1) as RT10.
    change (ov_read_bytes rsegs m (wa (0x10954+(Z.shiftl (Z.land C1 255) 2))) 4 = Some (le4 (Z_to_bv 64 (braid_part C1 0)))) in RT10.
    pose proof (braid_part_range C1 0) as HP10.
    pose proof (SX_range (braid_part C1 0) HP10) as HSP10.
    pose proof (crc_braid_table_read m 1 C1 TABLE ltac:(lia) HC1) as RT11.
    change (ov_read_bytes rsegs m (wa (0x10d54+(Z.land (Z.shiftr C1 6) 1020))) 4 = Some (le4 (Z_to_bv 64 (braid_part C1 1)))) in RT11.
    pose proof (braid_part_range C1 1) as HP11.
    pose proof (SX_range (braid_part C1 1) HP11) as HSP11.
    pose proof (crc_braid_table_read m 2 C1 TABLE ltac:(lia) HC1) as RT12.
    change (ov_read_bytes rsegs m (wa (0x11154+(Z.land (Z.shiftr C1 14) 1020))) 4 = Some (le4 (Z_to_bv 64 (braid_part C1 2)))) in RT12.
    pose proof (braid_part_range C1 2) as HP12.
    pose proof (SX_range (braid_part C1 2) HP12) as HSP12.
    pose proof (crc_braid_table_read m 3 C1 TABLE ltac:(lia) HC1) as RT13.
    change (ov_read_bytes rsegs m (wa (0x11554+(Z.shiftl (Z.shiftr (C1 mod 2^32) 24) 2))) 4 = Some (le4 (Z_to_bv 64 (braid_part C1 3)))) in RT13.
    pose proof (braid_part_range C1 3) as HP13.
    pose proof (SX_range (braid_part C1 3) HP13) as HSP13.
    assert (HL1 : (0 <= Z.lxor (SX (braid_part C1 0)) (SX (braid_part C1 1)) < 2^64)%Z) by (apply lxor_bound;lia).
    assert (HH1 : (0 <= Z.lxor (SX (braid_part C1 3)) (SX (braid_part C1 2)) < 2^64)%Z) by (apply lxor_bound;lia).
    assert (HV1 : (0 <= Z.lxor (Z.lxor (SX (braid_part C1 3)) (SX (braid_part C1 2))) (Z.lxor (SX (braid_part C1 0)) (SX (braid_part C1 1))) < 2^64)%Z) by (apply lxor_bound;lia).
    pose proof (braid_signed_value C1) as VAL1. rewrite EC1 in VAL1.
    rewrite (Z.lxor_comm (SX (braid_part C1 0)) (SX (braid_part C1 1))) in VAL1.
    set (W2 := (bv_unsigned (bword4 inp (i+8)))).
    assert (HW2 : (0 <= W2 < 2^32)%Z) by (unfold W2;apply bword4_unsigned_range).
    pose proof (SX_range W2 HW2) as HSW2.
    set (C2 := Z.lxor (SX W2) R2).
    assert (HC2 : (0 <= C2 < 2^64)%Z) by (unfold C2;apply lxor_bound;[lia|exact HSW2|exact HR2]).
    assert (EC2 : (C2 mod 2^32 = Z.lxor (R2 mod 2^32) W2)%Z).
    { unfold C2. rewrite low32_xor,(SX_mod32 W2 HW2). apply Z.lxor_comm. }
    pose proof (crc_braid_table_read m 0 C2 TABLE ltac:(lia) HC2) as RT20.
    change (ov_read_bytes rsegs m (wa (0x10954+(Z.shiftl (Z.land C2 255) 2))) 4 = Some (le4 (Z_to_bv 64 (braid_part C2 0)))) in RT20.
    pose proof (braid_part_range C2 0) as HP20.
    pose proof (SX_range (braid_part C2 0) HP20) as HSP20.
    pose proof (crc_braid_table_read m 1 C2 TABLE ltac:(lia) HC2) as RT21.
    change (ov_read_bytes rsegs m (wa (0x10d54+(Z.land (Z.shiftr C2 6) 1020))) 4 = Some (le4 (Z_to_bv 64 (braid_part C2 1)))) in RT21.
    pose proof (braid_part_range C2 1) as HP21.
    pose proof (SX_range (braid_part C2 1) HP21) as HSP21.
    pose proof (crc_braid_table_read m 2 C2 TABLE ltac:(lia) HC2) as RT22.
    change (ov_read_bytes rsegs m (wa (0x11154+(Z.land (Z.shiftr C2 14) 1020))) 4 = Some (le4 (Z_to_bv 64 (braid_part C2 2)))) in RT22.
    pose proof (braid_part_range C2 2) as HP22.
    pose proof (SX_range (braid_part C2 2) HP22) as HSP22.
    pose proof (crc_braid_table_read m 3 C2 TABLE ltac:(lia) HC2) as RT23.
    change (ov_read_bytes rsegs m (wa (0x11554+(Z.shiftl (Z.shiftr (C2 mod 2^32) 24) 2))) 4 = Some (le4 (Z_to_bv 64 (braid_part C2 3)))) in RT23.
    pose proof (braid_part_range C2 3) as HP23.
    pose proof (SX_range (braid_part C2 3) HP23) as HSP23.
    assert (HL2 : (0 <= Z.lxor (SX (braid_part C2 0)) (SX (braid_part C2 1)) < 2^64)%Z) by (apply lxor_bound;lia).
    assert (HH2 : (0 <= Z.lxor (SX (braid_part C2 3)) (SX (braid_part C2 2)) < 2^64)%Z) by (apply lxor_bound;lia).
    assert (HV2 : (0 <= Z.lxor (Z.lxor (SX (braid_part C2 3)) (SX (braid_part C2 2))) (Z.lxor (SX (braid_part C2 0)) (SX (braid_part C2 1))) < 2^64)%Z) by (apply lxor_bound;lia).
    pose proof (braid_signed_value C2) as VAL2. rewrite EC2 in VAL2.
    rewrite (Z.lxor_comm (SX (braid_part C2 0)) (SX (braid_part C2 1))) in VAL2.
    set (W3 := (bv_unsigned (bword4 inp (i+12)))).
    assert (HW3 : (0 <= W3 < 2^32)%Z) by (unfold W3;apply bword4_unsigned_range).
    pose proof (SX_range W3 HW3) as HSW3.
    set (C3 := Z.lxor (SX W3) R3).
    assert (HC3 : (0 <= C3 < 2^64)%Z) by (unfold C3;apply lxor_bound;[lia|exact HSW3|exact HR3]).
    assert (EC3 : (C3 mod 2^32 = Z.lxor (R3 mod 2^32) W3)%Z).
    { unfold C3. rewrite low32_xor,(SX_mod32 W3 HW3). apply Z.lxor_comm. }
    pose proof (crc_braid_table_read m 0 C3 TABLE ltac:(lia) HC3) as RT30.
    change (ov_read_bytes rsegs m (wa (0x10954+(Z.shiftl (Z.land C3 255) 2))) 4 = Some (le4 (Z_to_bv 64 (braid_part C3 0)))) in RT30.
    pose proof (braid_part_range C3 0) as HP30.
    pose proof (SX_range (braid_part C3 0) HP30) as HSP30.
    pose proof (crc_braid_table_read m 1 C3 TABLE ltac:(lia) HC3) as RT31.
    change (ov_read_bytes rsegs m (wa (0x10d54+(Z.land (Z.shiftr C3 6) 1020))) 4 = Some (le4 (Z_to_bv 64 (braid_part C3 1)))) in RT31.
    pose proof (braid_part_range C3 1) as HP31.
    pose proof (SX_range (braid_part C3 1) HP31) as HSP31.
    pose proof (crc_braid_table_read m 2 C3 TABLE ltac:(lia) HC3) as RT32.
    change (ov_read_bytes rsegs m (wa (0x11154+(Z.land (Z.shiftr C3 14) 1020))) 4 = Some (le4 (Z_to_bv 64 (braid_part C3 2)))) in RT32.
    pose proof (braid_part_range C3 2) as HP32.
    pose proof (SX_range (braid_part C3 2) HP32) as HSP32.
    pose proof (crc_braid_table_read m 3 C3 TABLE ltac:(lia) HC3) as RT33.
    change (ov_read_bytes rsegs m (wa (0x11554+(Z.shiftl (Z.shiftr (C3 mod 2^32) 24) 2))) 4 = Some (le4 (Z_to_bv 64 (braid_part C3 3)))) in RT33.
    pose proof (braid_part_range C3 3) as HP33.
    pose proof (SX_range (braid_part C3 3) HP33) as HSP33.
    assert (HL3 : (0 <= Z.lxor (SX (braid_part C3 0)) (SX (braid_part C3 1)) < 2^64)%Z) by (apply lxor_bound;lia).
    assert (HH3 : (0 <= Z.lxor (SX (braid_part C3 3)) (SX (braid_part C3 2)) < 2^64)%Z) by (apply lxor_bound;lia).
    assert (HV3 : (0 <= Z.lxor (Z.lxor (SX (braid_part C3 3)) (SX (braid_part C3 2))) (Z.lxor (SX (braid_part C3 0)) (SX (braid_part C3 1))) < 2^64)%Z) by (apply lxor_bound;lia).
    pose proof (braid_signed_value C3) as VAL3. rewrite EC3 in VAL3.
    rewrite (Z.lxor_comm (SX (braid_part C3 0)) (SX (braid_part C3 1))) in VAL3.
    set (W4 := (bv_unsigned (bword4 inp (i+16)))).
    assert (HW4 : (0 <= W4 < 2^32)%Z) by (unfold W4;apply bword4_unsigned_range).
    pose proof (SX_range W4 HW4) as HSW4.
    set (C4 := Z.lxor (SX W4) R4).
    assert (HC4 : (0 <= C4 < 2^64)%Z) by (unfold C4;apply lxor_bound;[lia|exact HSW4|exact HR4]).
    assert (EC4 : (C4 mod 2^32 = Z.lxor (R4 mod 2^32) W4)%Z).
    { unfold C4. rewrite low32_xor,(SX_mod32 W4 HW4). apply Z.lxor_comm. }
    pose proof (crc_braid_table_read m 0 C4 TABLE ltac:(lia) HC4) as RT40.
    change (ov_read_bytes rsegs m (wa (0x10954+(Z.shiftl (Z.land C4 255) 2))) 4 = Some (le4 (Z_to_bv 64 (braid_part C4 0)))) in RT40.
    pose proof (braid_part_range C4 0) as HP40.
    pose proof (SX_range (braid_part C4 0) HP40) as HSP40.
    pose proof (crc_braid_table_read m 1 C4 TABLE ltac:(lia) HC4) as RT41.
    change (ov_read_bytes rsegs m (wa (0x10d54+(Z.land (Z.shiftr C4 6) 1020))) 4 = Some (le4 (Z_to_bv 64 (braid_part C4 1)))) in RT41.
    pose proof (braid_part_range C4 1) as HP41.
    pose proof (SX_range (braid_part C4 1) HP41) as HSP41.
    pose proof (crc_braid_table_read m 2 C4 TABLE ltac:(lia) HC4) as RT42.
    change (ov_read_bytes rsegs m (wa (0x11154+(Z.land (Z.shiftr C4 14) 1020))) 4 = Some (le4 (Z_to_bv 64 (braid_part C4 2)))) in RT42.
    pose proof (braid_part_range C4 2) as HP42.
    pose proof (SX_range (braid_part C4 2) HP42) as HSP42.
    pose proof (crc_braid_table_read m 3 C4 TABLE ltac:(lia) HC4) as RT43.
    change (ov_read_bytes rsegs m (wa (0x11554+(Z.shiftl (Z.shiftr (C4 mod 2^32) 24) 2))) 4 = Some (le4 (Z_to_bv 64 (braid_part C4 3)))) in RT43.
    pose proof (braid_part_range C4 3) as HP43.
    pose proof (SX_range (braid_part C4 3) HP43) as HSP43.
    assert (HL4 : (0 <= Z.lxor (SX (braid_part C4 0)) (SX (braid_part C4 1)) < 2^64)%Z) by (apply lxor_bound;lia).
    assert (HH4 : (0 <= Z.lxor (SX (braid_part C4 3)) (SX (braid_part C4 2)) < 2^64)%Z) by (apply lxor_bound;lia).
    assert (HV4 : (0 <= Z.lxor (Z.lxor (SX (braid_part C4 3)) (SX (braid_part C4 2))) (Z.lxor (SX (braid_part C4 0)) (SX (braid_part C4 1))) < 2^64)%Z) by (apply lxor_bound;lia).
    pose proof (braid_signed_value C4) as VAL4. rewrite EC4 in VAL4.
    rewrite (Z.lxor_comm (SX (braid_part C4 0)) (SX (braid_part C4 1))) in VAL4.
    pose proof (rd4_at rsegs m B inp i _ INP ltac:(lia) ltac:(lia) eq_refl) as RD0.
    zstep. braid_norm. fold W0 W1 W2 W3 W4 C0 C1 C2 C3 C4.
    pose proof (rd4_at rsegs m B inp (i+4) _ INP ltac:(lia) ltac:(lia) eq_refl) as RD1.
    zstep. braid_norm. fold W0 W1 W2 W3 W4 C0 C1 C2 C3 C4.
    pose proof (rd4_at rsegs m B inp (i+8) _ INP ltac:(lia) ltac:(lia) eq_refl) as RD2.
    zstep. braid_norm. fold W0 W1 W2 W3 W4 C0 C1 C2 C3 C4.
    pose proof (rd4_at rsegs m B inp (i+12) _ INP ltac:(lia) ltac:(lia) eq_refl) as RD3.
    zstep. braid_norm. fold W0 W1 W2 W3 W4 C0 C1 C2 C3 C4.
    pose proof (rd4_at rsegs m B inp (i+16) _ INP ltac:(lia) ltac:(lia) eq_refl) as RD4.
    zstep. braid_norm. fold W0 W1 W2 W3 W4 C0 C1 C2 C3 C4.
    do 6 (zstep;braid_norm;fold W0 W1 W2 W3 W4 C0 C1 C2 C3 C4).
    do 95 (zstep;braid_norm;fold W0 W1 W2 W3 W4 C0 C1 C2 C3 C4).
    rewrite VAL0,VAL1,VAL2,VAL3,VAL4.
    replace (B+i+20)%Z with (B+(i+20))%Z by lia.
    apply CONT.
  Qed.
End BraidInstructionBlock.
