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
  CrcBraidMachine CrcBraidWord CrcBraidModel CrcWordChunks CrcWord CrcBraidExit CrcBraidBranch.
Local Opaque csteps SX.
Section BraidLoop.
  Variables (ra sp gp tp a2 a3 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (B ending : Z) (inp : list byte).
  Hypothesis INP : bytes_at rsegs m B inp.
  Hypothesis TABLE : bytes_at rsegs m CRC_TABS crc_table_bytes.
  Hypothesis TOP : (B+Z.of_nat (length inp) < 2^64)%Z.
  Variable Q : machine_state -> Prop.
  Notation AT pc x5 x8 x9 x11 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x31 :=
    (MS (mkR ra sp gp tp x5 (Z_to_bv 64 (B+ending)) (Z_to_bv 64 0x10954) x8 x9 (Z_to_bv 64 CRC_TABS)
      x11 a2 a3 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 s9 s10 s11
      (Z_to_bv 64 0x10d54) (Z_to_bv 64 0x11154) (Z_to_bv 64 0x11554) x31)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
  Definition braid_loop_cont (answer : Z) : Prop :=
    forall qf Rf0 Rf1 Rf2 Rf3 Rf4,
    (0 <= qf < 2^32)%Z ->
    (0 <= Rf0 < 2^64)%Z -> (0 <= Rf1 < 2^64)%Z -> (0 <= Rf2 < 2^64)%Z ->
    (0 <= Rf3 < 2^64)%Z -> (0 <= Rf4 < 2^64)%Z ->
    merge5 (Rf0 mod 2^32) (Rf1 mod 2^32) (Rf2 mod 2^32) (Rf3 mod 2^32) (Rf4 mod 2^32) = csteps 128 qf ->
    raw_crc (skipn (Z.to_nat ending) inp) qf = answer ->
    forall h8 h9 h18 h19 h20 h21 h22 h23 h24 h31, evt rsegs Q
      (AT 0x14840 (Z_to_bv 64 Rf1) h8 h9 (Z_to_bv 64 (B+ending))
        (Z_to_bv 64 Rf0) (Z_to_bv 64 Rf4) (Z_to_bv 64 Rf3) (Z_to_bv 64 Rf2)
        h18 h19 h20 h21 h22 h23 h24 h31).
  Theorem crc_braid_loop : forall (n : nat) (i q R0 R1 R2 R3 R4 answer : Z)
    g8 g9 g18 g19 g20 g21 g22 g23 g24 g31,
    (ending=i+20*Z.of_nat (S n))%Z -> (0 <= i)%Z -> (ending+20 <= Z.of_nat (length inp))%Z ->
    (0 <= q < 2^32)%Z ->
    (0 <= R0 < 2^64)%Z -> (0 <= R1 < 2^64)%Z -> (0 <= R2 < 2^64)%Z ->
    (0 <= R3 < 2^64)%Z -> (0 <= R4 < 2^64)%Z ->
    merge5 (R0 mod 2^32) (R1 mod 2^32) (R2 mod 2^32) (R3 mod 2^32) (R4 mod 2^32) = csteps 128 q ->
    raw_crc (skipn (Z.to_nat i) inp) q = answer ->
    braid_loop_cont answer ->
    evt rsegs Q
      (AT 0x14674 (Z_to_bv 64 R1) g8 g9 (Z_to_bv 64 (B+i))
        (Z_to_bv 64 R0) (Z_to_bv 64 R4) (Z_to_bv 64 R3) (Z_to_bv 64 R2)
        g18 g19 g20 g21 g22 g23 g24 g31).
  Proof.
    induction n as [n IH] using lt_wf_ind.
    intros i q R0 R1 R2 R3 R4 answer g8 g9 g18 g19 g20 g21 g22 g23 g24 g31 END Hi HL Hq HR0 HR1 HR2 HR3 HR4 MC REM CONT.
    pose proof (bytes_at_bound _ _ _ _ INP) as BB.
    set (W0 := bv_unsigned (bword4 inp i)).
    assert (HW0 : (0 <= W0 < 2^32)%Z) by (unfold W0;apply bword4_unsigned_range).
    set (A0 := csteps 160 (Z.lxor (R0 mod 2^32) W0)).
    assert (HA0 : (0 <= A0 < 2^32)%Z).
    { unfold A0. apply csteps_range,lxor_bound;[lia|apply Z.mod_pos_bound;lia|exact HW0]. }
    pose proof (SX_range A0 HA0) as HSA0.
    set (W1 := bv_unsigned (bword4 inp (i+4))).
    assert (HW1 : (0 <= W1 < 2^32)%Z) by (unfold W1;apply bword4_unsigned_range).
    set (A1 := csteps 160 (Z.lxor (R1 mod 2^32) W1)).
    assert (HA1 : (0 <= A1 < 2^32)%Z).
    { unfold A1. apply csteps_range,lxor_bound;[lia|apply Z.mod_pos_bound;lia|exact HW1]. }
    pose proof (SX_range A1 HA1) as HSA1.
    set (W2 := bv_unsigned (bword4 inp (i+8))).
    assert (HW2 : (0 <= W2 < 2^32)%Z) by (unfold W2;apply bword4_unsigned_range).
    set (A2 := csteps 160 (Z.lxor (R2 mod 2^32) W2)).
    assert (HA2 : (0 <= A2 < 2^32)%Z).
    { unfold A2. apply csteps_range,lxor_bound;[lia|apply Z.mod_pos_bound;lia|exact HW2]. }
    pose proof (SX_range A2 HA2) as HSA2.
    set (W3 := bv_unsigned (bword4 inp (i+12))).
    assert (HW3 : (0 <= W3 < 2^32)%Z) by (unfold W3;apply bword4_unsigned_range).
    set (A3 := csteps 160 (Z.lxor (R3 mod 2^32) W3)).
    assert (HA3 : (0 <= A3 < 2^32)%Z).
    { unfold A3. apply csteps_range,lxor_bound;[lia|apply Z.mod_pos_bound;lia|exact HW3]. }
    pose proof (SX_range A3 HA3) as HSA3.
    set (W4 := bv_unsigned (bword4 inp (i+16))).
    assert (HW4 : (0 <= W4 < 2^32)%Z) by (unfold W4;apply bword4_unsigned_range).
    set (A4 := csteps 160 (Z.lxor (R4 mod 2^32) W4)).
    assert (HA4 : (0 <= A4 < 2^32)%Z).
    { unfold A4. apply csteps_range,lxor_bound;[lia|apply Z.mod_pos_bound;lia|exact HW4]. }
    pose proof (SX_range A4 HA4) as HSA4.
    set (qnext := block5 q W0 W1 W2 W3 W4).
    assert (HQN : (0 <= qnext < 2^32)%Z) by (apply block5_range;assumption).
    assert (MCN : merge5 (SX A0 mod 2^32) (SX A1 mod 2^32) (SX A2 mod 2^32)
      (SX A3 mod 2^32) (SX A4 mod 2^32) = csteps 128 qnext).
    { rewrite (SX_mod32 A0 HA0),(SX_mod32 A1 HA1),(SX_mod32 A2 HA2),(SX_mod32 A3 HA3),(SX_mod32 A4 HA4).
      unfold A0,A1,A2,A3,A4,qnext. apply braid_step_preserves_serial. exact MC. }
    rewrite (raw_suffix_twenty inp i q Hi ltac:(clear -END HL Hi;lia)) in REM.
    fold W0 W1 W2 W3 W4 qnext in REM.
    eapply crc_braid_iteration;
      [exact INP|exact TABLE|exact Hi|lia|exact HR0|exact HR1|exact HR2|exact HR3|exact HR4|].
    intros h8 h9 h18 h19 h20 h21 h22 h23 h24 h31.
    fold W0 W1 W2 W3 W4 A0 A1 A2 A3 A4.
    assert (PI : (0 <= B+(i+20) < 2^64)%Z).
    { clear -END Hi HL TOP BB. lia. }
    assert (PE : (0 <= B+ending < 2^64)%Z).
    { clear -END Hi HL TOP BB. lia. }
    eapply braid_branch_cert. if_cases BR;zify_bool BR;unfold bv_eqb in BR;
      rewrite !Z_to_bv_unsigned in BR;
      rewrite (bv_wrap_small 64 (B+(i+20)) PI),(bv_wrap_small 64 (B+ending) PE) in BR;
      zify_bool BR.
    - destruct n as [|n];[exfalso;clear -END BR;cbn in END;lia|].
      eapply (IH n ltac:(apply Nat.lt_succ_diag_r) (i+20)%Z qnext (SX A0) (SX A1) (SX A2) (SX A3) (SX A4) answer);
        [clear -END;rewrite Nat2Z.inj_succ in END;lia|clear -Hi;lia|exact HL|exact HQN|
         exact HSA0|exact HSA1|exact HSA2|exact HSA3|exact HSA4|exact MCN|exact REM|exact CONT].
    - eapply braid_exit_cert.
      assert (EF : raw_crc (skipn (Z.to_nat ending) inp) qnext = answer).
      { assert (E : (i+20=ending)%Z) by (clear -BR;lia). rewrite <- E. exact REM. }
      unfold braid_loop_cont in CONT.
      exact (CONT qnext (SX A0) (SX A1) (SX A2) (SX A3) (SX A4)
        HQN HSA0 HSA1 HSA2 HSA3 HSA4 MCN EF h8 h9 h18 h19 h20 h21 h22 h23 h24 h31).
  Qed.
End BraidLoop.
