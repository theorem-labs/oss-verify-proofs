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
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import AdlerModel AdlerByte AdlerControl.
Local Opaque adler_output.
Lemma adler_budget_boundedA : forall k a b d cap,
  (1 <= k)%Z -> (0 <= a)%Z -> (0 <= b)%Z -> (0 <= d < 256)%Z ->
  (a+255*k < cap)%Z -> (b+k*a+255*k*k < 2^40)%Z ->
  (a+d+255*(k-1) < cap)%Z /\
  ((b+a+d)+(k-1)*(a+d)+255*(k-1)*(k-1) < 2^40)%Z.
Proof. intros. split;nia. Qed.
Section AdlerShortBounded.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (B ending : Z) (inp : list byte).
  Hypothesis INP : bytes_at rsegs m B inp.
  Hypothesis TOP : (B+Z.of_nat (length inp) < 2^64)%Z.
  Variable Q : machine_state -> Prop.
  Variable AMAX : Z.
  Hypothesis ACAP : (0 < AMAX <= 2^40)%Z.
  Definition adler_short_bounded_cont answer : Prop := forall af bf, (0 <= af < AMAX)%Z -> (0 <= bf < 2^40)%Z ->
    adler_output (skipn (Z.to_nat ending) inp) af bf = answer -> forall h0 h1, evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 h0 (Z_to_bv 64 (B+ending)) (Z_to_bv 64 (B+ending)) (Z_to_bv 64 bf) (Z_to_bv 64 af) h1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14e68) fc None m (seg_rom rsegs)).
  Theorem adler_short_bounded_loop : forall (n : nat) (i a b answer : Z) g0 g1,
    (ending=i+Z.of_nat (S n))%Z -> (0 <= i)%Z -> (ending <= Z.of_nat (length inp))%Z ->
    (0 <= a)%Z -> (0 <= b)%Z -> (a+255*Z.of_nat (S n) < AMAX)%Z ->
    (b+Z.of_nat (S n)*a+255*Z.of_nat (S n)*Z.of_nat (S n) < 2^40)%Z ->
    adler_output (skipn (Z.to_nat i) inp) a b = answer -> adler_short_bounded_cont answer ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 g0 (Z_to_bv 64 (B+i)) (Z_to_bv 64 (B+ending)) (Z_to_bv 64 b) (Z_to_bv 64 a) g1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14e50) fc None m (seg_rom rsegs)).
  Proof.
    induction n as [n IH] using lt_wf_ind.
    intros i a b answer g0 g1 END HI HL HA HB BA BB REM CONT.
    pose proof (bytes_at_bound _ _ _ _ INP) as PB.
    assert (NI : (0 <= i < Z.of_nat (length inp))%Z) by (clear -END HI HL;lia).
    assert (RA : (0 <= a < 2^48)%Z) by (clear -HA BA ACAP;nia).
    assert (RB : (0 <= b < 2^48)%Z) by (clear -HB BB HA;nia).
    pose proof (byte_unsigned_range (bbyte inp i)) as HD.
    pose proof (adler_budget_boundedA (Z.of_nat (S n)) a b (bv_unsigned (bbyte inp i)) AMAX
      ltac:(lia) HA HB HD BA BB) as [BAN BBN].
    replace (Z.of_nat (S n)-1)%Z with (Z.of_nat n) in BAN,BBN by lia.
    assert (RAN : (0 <= a+bv_unsigned (bbyte inp i) < AMAX)%Z) by (clear -HA HD BAN;nia).
    assert (RBN : (0 <= b+a+bv_unsigned (bbyte inp i) < 2^40)%Z) by (clear -HA HB HD BBN;nia).
    rewrite (adler_suffix_step inp i a b NI) in REM.
    eapply adler_byte_update;[exact INP|exact NI|exact RA|exact RB|].
    assert (PN : (0 <= B+i+1 < 2^64)%Z) by (clear -PB HI END HL TOP;lia).
    assert (PE : (0 <= B+ending < 2^64)%Z) by (clear -PB HI END HL TOP;lia).
    eapply adler_byte_branch_cert. if_cases BR;zify_bool BR;unfold bv_eqb in BR;
      rewrite !Z_to_bv_unsigned in BR;
      rewrite (bv_wrap_small 64 (B+i+1) PN),(bv_wrap_small 64 (B+ending) PE) in BR;zify_bool BR.
    - destruct n as [|n];[exfalso;clear -END BR;cbn in END;lia|].
      replace (B+i+1)%Z with (B+(i+1))%Z by ring.
      eapply (IH n ltac:(apply Nat.lt_succ_diag_r) (i+1)%Z
        (a+bv_unsigned (bbyte inp i))%Z (b+a+bv_unsigned (bbyte inp i))%Z answer);
        [clear -END;rewrite Nat2Z.inj_succ in END;lia|clear -HI;lia|exact HL|
         exact (proj1 RAN)|exact (proj1 RBN)|exact BAN|exact BBN|exact REM|exact CONT].
    - assert (E : (i+1=ending)%Z) by (clear -BR;lia).
      replace (B+i+1)%Z with (B+ending)%Z by (clear -E;lia).
      assert (RF : adler_output (skipn (Z.to_nat ending) inp)
        (a+bv_unsigned (bbyte inp i))%Z (b+a+bv_unsigned (bbyte inp i))%Z = answer).
      { rewrite <- E. exact REM. }
      unfold adler_short_bounded_cont in CONT. exact (CONT _ _ RAN RBN RF
        (Z_to_bv 64 (bv_unsigned (bbyte inp i))) (Z_to_bv 64 (B+ending))).
  Qed.
End AdlerShortBounded.