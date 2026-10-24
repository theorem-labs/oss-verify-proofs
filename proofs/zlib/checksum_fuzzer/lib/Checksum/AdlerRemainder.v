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
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import
  AdlerModel AdlerLoops AdlerBlockLoops AdlerBlockControl AdlerReduceTail.
Open Scope Z_scope.
Section AdlerRemainder.
  Variables (ra sp gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (B : Z) (inp : list byte).
  Hypothesis INP : bytes_at rsegs m B inp.
  Hypothesis TOP : B+Z.of_nat (length inp) < 2^64.
  Hypothesis SIZE : Z.of_nat (length inp) <= 1048576.
  Hypothesis MAGIC : ov_read_bytes rsegs m (wa 0x119e0) 8 = Some (le8 (Z_to_bv 64 ADLER_MAGIC)).
  Variable Q : machine_state -> Prop.
  Notation L := (Z.of_nat (length inp)).
  Definition adler_packed_cont answer : Prop := forall af bf, 0 <= af < ADLER_BASE -> 0 <= bf < ADLER_BASE ->
    adler_pack af bf = answer -> forall t0 t1 t2 s0 s1 a0 a1 a2 a5 a6 a7 s2 t3 t4 t5 t6, evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 bf) (Z_to_bv 64 af) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15170) fc None m (seg_rom rsegs)).
  Lemma adler_finalize_raw : forall a b answer t0 t1 t2 s0 s1 a1 a2 a5 a6 a7 s2 t3 t4 t5 t6,
    0 <= a < 2^48 -> 0 <= b < 2^48 -> adler_output [] a b = answer -> adler_packed_cont answer ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x11ed4) a1 a2 (Z_to_bv 64 b) (Z_to_bv 64 a) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1512c) fc None m (seg_rom rsegs)).
  Proof. intros a b answer t0 t1 t2 s0 s1 a1 a2 a5 a6 a7 s2 t3 t4 t5 t6 HA HB RN CONT.
    eapply adler_reduce_tail;[exact MAGIC|exact HA|exact HB|].
    intros h10 h11 h12. unfold adler_packed_cont in CONT.
    change (adler_pack (a mod ADLER_BASE) (b mod ADLER_BASE) = answer) in RN.
    eapply CONT;[apply Z.mod_pos_bound;unfold ADLER_BASE;lia|apply Z.mod_pos_bound;unfold ADLER_BASE;lia|exact RN].
  Qed.
  Lemma adler_tail_path : forall i a b answer t0 t1 t2 s0 s1 a1 a6 a7 s2 t3 t4 t5 t6,
    0 <= i -> 0 < L-i < 16 -> 0 <= a -> 0 <= b ->
    a+255*(L-i) < 2^40 -> b+(L-i)*a+255*(L-i)*(L-i) < 2^40 ->
    adler_output (skipn (Z.to_nat i) inp) a b = answer -> adler_packed_cont answer ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x11ed4) a1 (Z_to_bv 64 (L-i)) (Z_to_bv 64 b) (Z_to_bv 64 a) (Z_to_bv 64 (B+i)) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15110) fc None m (seg_rom rsegs)).
  Proof. intros i a b answer t0 t1 t2 s0 s1 a1 a6 a7 s2 t3 t4 t5 t6 HI HR HA HB BA BB REM CONT.
    pose proof (bytes_at_bound _ _ _ _ INP) as PB.
    assert (PU : bv_unsigned (Z_to_bv 64 (B+i)) = B+i).
    { rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (0 <= B+i < 2^64). clear -HI HR PB TOP;lia. }
    assert (NU : bv_unsigned (Z_to_bv 64 (L-i)) = L-i).
    { rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (0 <= L-i < 2^64). clear -HR;lia. }
    eapply adler_inner_tail_init_cert. rewrite PU,NU.
    replace (B+i+(L-i)) with (B+L) by ring.
    eapply adler_tail_loop with (B:=B) (inp:=inp) (ending:=L) (n:=Z.to_nat (L-i-1)) (a:=a) (b:=b) (answer:=answer);
      [exact INP|exact TOP|rewrite Nat2Z.inj_succ,Z2Nat.id by lia;lia|exact HI|lia|exact HA|exact HB|
       replace (Z.of_nat (S (Z.to_nat (L-i-1)))) with (L-i) by lia;exact BA|
       replace (Z.of_nat (S (Z.to_nat (L-i-1)))) with (L-i) by lia;exact BB|exact REM|].
    unfold adler_tail_cont. intros af bf RA RB RF h11 h16.
    rewrite Nat2Z.id,skipn_all in RF.
    eapply adler_finalize_raw with (a:=af) (b:=bf) (answer:=answer);
      [lia|lia|exact RF|exact CONT].
  Qed.
  Lemma adler_remainder_finish : forall i a b answer t0 t1 t2 s0 s1 a6 a7 s2 t3 t4 t5 t6,
    0 <= i <= L -> L-i < 16 -> 0 <= a -> 0 <= b ->
    a+255*(L-i) < 2^40 -> b+(L-i)*a+255*(L-i)*(L-i) < 2^40 ->
    adler_output (skipn (Z.to_nat i) inp) a b = answer -> adler_packed_cont answer ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x11ed4) (Z_to_bv 64 15) (Z_to_bv 64 (L-i)) (Z_to_bv 64 b) (Z_to_bv 64 a) (Z_to_bv 64 (B+i)) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1510c) fc None m (seg_rom rsegs)).
  Proof. intros i a b answer t0 t1 t2 s0 s1 a6 a7 s2 t3 t4 t5 t6 HI HR HA HB BA BB REM CONT.
    assert (NL : 0 <= L-i < 2^64) by (clear -HI HR;lia).
    eapply adler_inner_tail_dispatch_cert. if_cases BR;zify_bool BR;unfold bv_eqb in BR;
      rewrite !Z_to_bv_unsigned in BR;
      rewrite (bv_wrap_small 64 (L-i) NL),(bv_wrap_small 64 0 ltac:(change (0 <= 0 < 2^64);lia)) in BR;zify_bool BR.
    - assert (E : i=L) by (clear -BR;lia). subst i. rewrite Nat2Z.id,skipn_all in REM.
      eapply adler_finalize_raw with (a:=a) (b:=b) (answer:=answer);
        [clear -HA BA;lia|clear -HA HB BB;nia|exact REM|exact CONT].
    - eapply adler_tail_path with (a:=a) (b:=b) (answer:=answer);
        [exact (proj1 HI)|clear -HI HR BR;lia|exact HA|exact HB|exact BA|exact BB|exact REM|exact CONT].
  Qed.
  Theorem adler_inner_finish : forall i a b answer t0 t1 t2 s0 s1 a6 a7 s2 t3 t4 t5 t6,
    0 <= i -> i+16 <= L -> 0 <= a -> 0 <= b ->
    a+255*(L-i) < 2^40 -> b+(L-i)*a+255*(L-i)*(L-i) < 2^40 ->
    adler_output (skipn (Z.to_nat i) inp) a b = answer -> adler_packed_cont answer ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x11ed4) (Z_to_bv 64 15) (Z_to_bv 64 (L-i)) (Z_to_bv 64 b) (Z_to_bv 64 a) (Z_to_bv 64 (B+i)) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15040) fc None m (seg_rom rsegs)).
  Proof. intros i a b answer t0 t1 t2 s0 s1 a6 a7 s2 t3 t4 t5 t6 HI HL HA HB BA BB REM CONT.
    eapply adler_inner_blocks with (k:=Z.to_nat (L-i)) (a:=a) (b:=b) (answer:=answer);
      [exact INP|exact SIZE|reflexivity|exact HI|exact HL|exact HA|exact HB|exact BA|exact BB|exact REM|].
    unfold adler_inner_blocks_cont. intros j af bf HJ HR RA RB BAN BBN RF h5 h6 h16 h17.
    eapply adler_remainder_finish with (a:=af) (b:=bf) (answer:=answer);
      [exact HJ|exact HR|exact RA|exact RB|exact BAN|exact BBN|exact RF|exact CONT].
  Qed.
End AdlerRemainder.
