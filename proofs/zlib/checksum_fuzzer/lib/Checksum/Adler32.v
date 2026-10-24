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
  AdlerModel AdlerWord AdlerSeed AdlerOneByte AdlerBody AdlerRemainder AdlerFrame AdlerPrologue AdlerBlockControl.
Open Scope Z_scope.
Theorem adler32_z_nonnull_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (lo B a b : Z) (inp : list byte) (m : word -> option byte),
  (0 <= a < ADLER_BASE)%Z -> (0 <= b < ADLER_BASE)%Z ->
  bytes_at rsegs m B inp -> bytes_at rsegs m 0x119e0 (le8 (Z_to_bv 64 ADLER_MAGIC)) ->
  (0 < B)%Z -> (B+Z.of_nat (length inp) < 2^64)%Z -> (Z.of_nat (length inp) <= 1048576)%Z ->
  stk rsegs m lo (bv_unsigned sp) -> (lo+ADLER_FRAME <= bv_unsigned sp)%Z ->
  (B+Z.of_nat (length inp) <= bv_unsigned sp-ADLER_FRAME \/ bv_unsigned sp <= B)%Z ->
  (0x119e0+8 <= bv_unsigned sp-ADLER_FRAME \/ bv_unsigned sp <= 0x119e0)%Z ->
  evt rsegs (adler_value_post (adler_output inp a b) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (adler_pack a b)) (Z_to_bv 64 B) (Z_to_bv 64 (Z.of_nat (length inp))) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14dc8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo B a b inp m HA HB INP TABLE HBUF TOP SIZE ST LO DI DT.
  pose proof (bytes_at_bound _ _ _ _ INP) as PB.
  assert (B64 : (0 <= B < 2^64)%Z) by (clear -PB TOP;lia).
  assert (LN : (0 <= Z.of_nat (length inp) < 2^64)%Z) by (clear -SIZE;lia).
  eapply adler_seed_decode;[exact HA|exact HB|].
  eapply adler_entry_one_cert. if_cases ONE;zify_bool ONE;unfold bv_eqb in ONE;
    rewrite !Z_to_bv_unsigned in ONE;
    rewrite (bv_wrap_small 64 (Z.of_nat (length inp)) LN),
      (bv_wrap_small 64 1 ltac:(change (0 <= 1 < 2^64)%Z;lia)) in ONE;zify_bool ONE.
  - eapply adler_entry_null_cert. if_cases NULL;zify_bool NULL;unfold bv_eqb in NULL;
      rewrite !Z_to_bv_unsigned in NULL;
      rewrite (bv_wrap_small 64 B B64),(bv_wrap_small 64 0 ltac:(change (0 <= 0 < 2^64)%Z;lia)) in NULL;zify_bool NULL.
    { exfalso. clear -NULL HBUF;lia. }
    eapply adler_save_frame with (B:=B) (inp:=inp);
      [exact INP|exact TABLE|exact ST|exact LO|exact DI|exact DT|].
    intros m1 junk MU WM ST1 FR INP1 TABLE1.
    assert (MR : ov_read_bytes rsegs m1 (wa 0x119e0) 8 = Some (le8 (Z_to_bv 64 ADLER_MAGIC))).
    { replace (wa 0x119e0) with (wa (0x119e0+0)) by reflexivity.
      rewrite (bytes_at_read rsegs m1 0x119e0 (le8 (Z_to_bv 64 ADLER_MAGIC)) 0 8 TABLE1 ltac:(lia))
        by (rewrite length_le8;lia). reflexivity. }
    eapply adler_body_all with (a:=a) (b:=b) (answer:=adler_output inp a b);
      [exact INP1|exact TOP|exact SIZE|exact MR|exact HA|exact HB|reflexivity| |].
    + unfold adler_packed_cont. intros af bf RAF RBF EQ ct0 ct1 ct2 cs0 cs1 ca0 ca1 ca2 ca5 ca6 ca7 cs2 ct3 ct4 ct5 ct6.
      change (evt rsegs (adler_value_post (adler_output inp a b) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m) (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp-ADLER_FRAME)) gp tp ct0 ct1 ct2 cs0 cs1 ca0 ca1 ca2 (Z_to_bv 64 bf) (Z_to_bv 64 af) ca5 ca6 ca7 cs2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ct3 ct4 ct5 ct6) F (Z_to_bv 64 0x15170) fc None m1 (seg_rom rsegs))).
      rewrite <- EQ.
      eapply adler_pack_main_steps;[clear -RAF;unfold ADLER_BASE in RAF;lia|clear -RBF;unfold ADLER_BASE in RBF;lia|].
      eapply adler_epilogue with (sp:=sp) (m:=m) (junk:=junk);
        [exact MU|exact WM|exact LO|exact ST1|exact FR|right;reflexivity].
    + unfold adler_short_packed_cont. intros af bf RAF RBF EQ ct0 ct1 ct2 cs0 cs1 ca0 ca2 ca4 ca5 ca6 ca7 cs2 ct3 ct4 ct5 ct6.
      change (evt rsegs (adler_value_post (adler_output inp a b) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m) (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp-ADLER_FRAME)) gp tp ct0 ct1 ct2 cs0 cs1 ca0 (Z_to_bv 64 af) ca2 (Z_to_bv 64 bf) ca4 ca5 ca6 ca7 cs2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ct3 ct4 ct5 ct6) F (Z_to_bv 64 0x14eb0) fc None m1 (seg_rom rsegs))).
      rewrite <- EQ.
      eapply adler_pack_short_steps;[clear -RAF;unfold ADLER_BASE in RAF;lia|clear -RBF;unfold ADLER_BASE in RBF;lia|].
      eapply adler_epilogue with (sp:=sp) (m:=m) (junk:=junk);
        [exact MU|exact WM|exact LO|exact ST1|exact FR|left;reflexivity].
  - assert (EX : exists c, inp=[c]).
    { destruct inp as [|c xs];[cbn in ONE;lia|]. destruct xs as [|d xs];[eexists;reflexivity|cbn in ONE;lia]. }
    destruct EX as [c EI]. subst inp.
    assert (RD : ov_read_bytes rsegs m (wa B) 1 = Some [c]).
    { pose proof (rd1_at rsegs m B [c] 0 _ INP ltac:(lia) ltac:(lia) eq_refl) as R.
      change (ov_read_bytes rsegs m (wa (B+0)) 1 = Some [c]) in R.
      replace (B+0)%Z with B in R by ring. exact R. }
    pose proof (munch_refl [(bv_unsigned sp-ADLER_FRAME,bv_unsigned sp)]%Z m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    eapply adler_one_byte_cert with (B:=B) (a:=a) (b:=b) (c:=c);
      [exact B64|exact HA|exact HB|exact RD|].
    intros. finish.
Qed.
Theorem adler32_nonnull_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (lo B a b : Z) (inp : list byte) (m : word -> option byte),
  (0 <= a < ADLER_BASE)%Z -> (0 <= b < ADLER_BASE)%Z ->
  bytes_at rsegs m B inp -> bytes_at rsegs m 0x119e0 (le8 (Z_to_bv 64 ADLER_MAGIC)) ->
  (0 < B)%Z -> (B+Z.of_nat (length inp) < 2^64)%Z -> (Z.of_nat (length inp) <= 1048576)%Z ->
  stk rsegs m lo (bv_unsigned sp) -> (lo+ADLER_FRAME <= bv_unsigned sp)%Z ->
  (B+Z.of_nat (length inp) <= bv_unsigned sp-ADLER_FRAME \/ bv_unsigned sp <= B)%Z ->
  (0x119e0+8 <= bv_unsigned sp-ADLER_FRAME \/ bv_unsigned sp <= 0x119e0)%Z ->
  evt rsegs (adler_value_post (adler_output inp a b) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (adler_pack a b)) (Z_to_bv 64 B) (Z_to_bv 64 (Z.of_nat (length inp))) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1518c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo B a b inp m HA HB INP TABLE HBUF TOP SIZE ST LO DI DT.
  eapply adler_length_wrapper.
  assert (LN : (bv_unsigned (Z_to_bv 64 (Z.of_nat (length inp))) mod 2^32 = Z.of_nat (length inp))%Z).
  { rewrite Z_to_bv_unsigned,(bv_wrap_small 64 (Z.of_nat (length inp)) ltac:(change (0 <= Z.of_nat (length inp) < 2^64)%Z;lia)).
    apply Z.mod_small. lia. }
  rewrite LN. eapply adler32_z_nonnull_spec;
    [exact HA|exact HB|exact INP|exact TABLE|exact HBUF|exact TOP|exact SIZE|exact ST|exact LO|exact DI|exact DT].
Qed.
Theorem adler32_z_null0_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : word -> option byte),
  stk rsegs m lo (bv_unsigned sp) -> evt rsegs (adler_value_post 1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 0) (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14dc8) fc None m (seg_rom rsegs)).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m ST.
  pose proof (munch_refl [(bv_unsigned sp-ADLER_FRAME,bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 4 zstep. eapply adler_entry_one_cert. if_cases ONE;zify_cond ONE.
  - eapply adler_entry_null_cert. if_cases NULL;zify_cond NULL.
    + zstep. finish.
    + exfalso. lia.
  - exfalso. lia.
Qed.
Theorem adler32_null0_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : word -> option byte),
  stk rsegs m lo (bv_unsigned sp) -> evt rsegs (adler_value_post 1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 0) (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1518c) fc None m (seg_rom rsegs)).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m ST.
  eapply adler_length_wrapper. eapply adler32_z_null0_spec. exact ST.
Qed.
