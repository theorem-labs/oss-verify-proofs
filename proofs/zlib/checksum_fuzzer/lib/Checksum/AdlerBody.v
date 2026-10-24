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
  AdlerModel AdlerWord AdlerOuter AdlerSetup AdlerRemainder AdlerBlockControl AdlerShortBounded AdlerShortReduce.
Open Scope Z_scope.
Section AdlerBody.
  Variables (ra sp gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (B : Z) (inp : list byte).
  Hypothesis INP : bytes_at rsegs m B inp.
  Hypothesis TOP : B+Z.of_nat (length inp) < 2^64.
  Hypothesis SIZE : Z.of_nat (length inp) <= 1048576.
  Hypothesis MAGIC : ov_read_bytes rsegs m (wa 0x119e0) 8 = Some (le8 (Z_to_bv 64 ADLER_MAGIC)).
  Variable Q : machine_state -> Prop.
  Notation L := (Z.of_nat (length inp)).
  Notation PCONT := (adler_packed_cont ra sp gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m Q).
  Definition adler_short_packed_cont answer : Prop := forall af bf, 0 <= af < ADLER_BASE -> 0 <= bf < ADLER_BASE ->
    adler_pack af bf = answer -> forall t0 t1 t2 s0 s1 a0 a2 a4 a5 a6 a7 s2 t3 t4 t5 t6, evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 af) a2 (Z_to_bv 64 bf) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14eb0) fc None m (seg_rom rsegs)).
  Lemma adler_short_finalize : forall a b answer t0 t1 t2 s0 s1 a0 a1 a2 a5 a6 a7 s2 t3 t4 t5 t6,
    0 <= a < 2*ADLER_BASE -> 0 <= b < 2^48 -> adler_output [] a b = answer -> adler_short_packed_cont answer ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 b) (Z_to_bv 64 a) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14e68) fc None m (seg_rom rsegs)).
  Proof. intros a b answer t0 t1 t2 s0 s1 a0 a1 a2 a5 a6 a7 s2 t3 t4 t5 t6 HA HB RN CONT.
    eapply adler_reduce_short;[exact MAGIC|exact HA|exact HB|]. intros h10 h12 h14 h15.
    change (adler_pack (a mod ADLER_BASE) (b mod ADLER_BASE) = answer) in RN.
    unfold adler_short_packed_cont in CONT. eapply CONT;
      [apply Z.mod_pos_bound;unfold ADLER_BASE;lia|apply Z.mod_pos_bound;unfold ADLER_BASE;lia|exact RN].
  Qed.
  Lemma adler_short_path : forall a b answer t0 t1 t2 s0 s1 a5 a6 a7 s2 t3 t4 t5 t6,
    L < 16 -> 0 <= a < ADLER_BASE -> 0 <= b < ADLER_BASE ->
    adler_output inp a b = answer -> adler_short_packed_cont answer ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 16) (Z_to_bv 64 B) (Z_to_bv 64 L) (Z_to_bv 64 b) (Z_to_bv 64 a) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14e48) fc None m (seg_rom rsegs)).
  Proof. intros a b answer t0 t1 t2 s0 s1 a5 a6 a7 s2 t3 t4 t5 t6 HL HA HB REM CONT.
    pose proof (bytes_at_bound _ _ _ _ INP) as PB.
    assert (NL : 0 <= L < 2^64) by lia.
    eapply adler_short_nonzero_cert. if_cases BR;zify_bool BR;unfold bv_eqb in BR;
      rewrite !Z_to_bv_unsigned in BR;
      rewrite (bv_wrap_small 64 L NL),(bv_wrap_small 64 0 ltac:(change (0 <= 0 < 2^64);lia)) in BR;zify_bool BR.
    - assert (EI : inp=[]) by (destruct inp;[reflexivity|cbn in BR;lia]). rewrite EI in REM.
      eapply adler_short_finalize with (a:=a) (b:=b) (answer:=answer);
        [clear -HA;unfold ADLER_BASE in *;lia|clear -HB;unfold ADLER_BASE in HB;lia|exact REM|exact CONT].
    - eapply adler_short_ptrend_cert.
      assert (PU : bv_unsigned (Z_to_bv 64 B) = B).
      { rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (0 <= B < 2^64). clear -PB TOP;lia. }
      assert (NU : bv_unsigned (Z_to_bv 64 L) = L) by (rewrite Z_to_bv_unsigned;apply bv_wrap_small;exact NL).
      rewrite PU,NU.
      replace (Z_to_bv 64 B) with (Z_to_bv 64 (B+0)) by (f_equal;ring).
      eapply adler_short_bounded_loop with (B:=B) (inp:=inp) (ending:=L) (AMAX:=2*ADLER_BASE)
        (n:=Z.to_nat (L-1)) (i:=0) (a:=a) (b:=b) (answer:=answer);
        [exact INP|exact TOP|unfold ADLER_BASE;lia|rewrite Nat2Z.inj_succ,Z2Nat.id by lia;lia|lia|lia|
         exact (proj1 HA)|exact (proj1 HB)|
         replace (Z.of_nat (S (Z.to_nat (L-1)))) with L by lia;clear -HA HL;unfold ADLER_BASE in *;lia|
         replace (Z.of_nat (S (Z.to_nat (L-1)))) with L by lia;clear -HA HB HL;unfold ADLER_BASE in *;nia|exact REM|].
      unfold adler_short_bounded_cont. intros af bf RA RB RF h10 h15.
      rewrite Nat2Z.id,skipn_all in RF.
      eapply adler_short_finalize with (a:=af) (b:=bf) (answer:=answer);
        [exact RA|clear -RB;lia|exact RF|exact CONT].
  Qed.
  Theorem adler_body_all : forall a b answer t0 t1 t2 s0 s1 a0 a5 a6 a7 s2 t3 t4 t5 t6,
    0 <= a < ADLER_BASE -> 0 <= b < ADLER_BASE -> adler_output inp a b = answer ->
    PCONT answer -> adler_short_packed_cont answer ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 B) (Z_to_bv 64 L) (Z_to_bv 64 b) (Z_to_bv 64 a) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14e40) fc None m (seg_rom rsegs)).
  Proof. intros a b answer t0 t1 t2 s0 s1 a0 a5 a6 a7 s2 t3 t4 t5 t6 HA HB REM MAIN SHORT.
    assert (NL : 0 <= L < 2^64) by lia.
    eapply adler_short_size_cert. if_cases BR;zify_bool BR;
      rewrite !Z_to_bv_unsigned in BR;rewrite (bv_wrap_small 64 L NL) in BR;zify_bool BR.
    - eapply adler_large_threshold_cert;[lia|].
      assert (SH : 0 <= Z.shiftr L 4 < 2^64).
      { rewrite Z.shiftr_div_pow2 by lia. split;[apply Z.div_pos;lia|apply Z.div_lt_upper_bound;lia]. }
      if_cases BIG;zify_bool BIG;unfold bv_ltu in BIG;rewrite !Z_to_bv_unsigned in BIG;
        rewrite (bv_wrap_small 64 (Z.shiftr L 4) SH),
          (bv_wrap_small 64 347 ltac:(change (0 <= 347 < 2^64);lia)) in BIG;zify_bool BIG;
        rewrite Z.shiftr_div_pow2 in BIG by lia;change (2^4) with 16 in BIG.
      + assert (LL : L < 5552) by (clear -BIG;lia).
        eapply adler_initial_inner_cert.
        replace (Z_to_bv 64 B) with (Z_to_bv 64 (B+0)) by (f_equal;ring).
        replace (Z_to_bv 64 L) with (Z_to_bv 64 (L-0)) by (f_equal;ring).
        eapply adler_inner_finish with (B:=B) (inp:=inp) (i:=0) (a:=a) (b:=b) (answer:=answer);
          [exact INP|exact TOP|exact SIZE|exact MAGIC|lia|clear -BR;lia|exact (proj1 HA)|exact (proj1 HB)|
           clear -HA LL;unfold ADLER_BASE in HA;nia|clear -HA HB LL;unfold ADLER_BASE in *;nia|exact REM|exact MAIN].
      + eapply adler_outer_setup_cert;[exact MAGIC|].
        replace (Z_to_bv 64 B) with (Z_to_bv 64 (B+0)) at 2 by (f_equal;ring).
        replace (Z_to_bv 64 L) with (Z_to_bv 64 (L-0)) by (f_equal;ring).
        eapply adler_outer_loop with (B:=B) (inp:=inp) (k:=Z.to_nat (L/5552)) (i:=0) (g:=0)
          (a:=a) (b:=b) (answer:=answer);
          [exact INP|exact TOP|exact SIZE|exact MAGIC|replace (L-0) with L by ring;reflexivity|lia|
           clear -BIG;lia|reflexivity|exact HA|exact HB|exact REM|exact MAIN].
    - eapply adler_short_path;[clear -BR;lia|exact HA|exact HB|exact REM|exact SHORT].
  Qed.
End AdlerBody.
