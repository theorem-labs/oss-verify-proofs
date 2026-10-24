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
  AdlerModel AdlerWord AdlerBlockLoops AdlerBlockControl AdlerSetup AdlerReduce AdlerRemainder.
Open Scope Z_scope.
Local Opaque adler_output.
Section AdlerOuter.
  Variables (ra sp gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (B : Z) (inp : list byte).
  Hypothesis INP : bytes_at rsegs m B inp.
  Hypothesis TOP : B+Z.of_nat (length inp) < 2^64.
  Hypothesis SIZE : Z.of_nat (length inp) <= 1048576.
  Hypothesis MAGIC : ov_read_bytes rsegs m (wa 0x119e0) 8 = Some (le8 (Z_to_bv 64 ADLER_MAGIC)).
  Variable Q : machine_state -> Prop.
  Notation L := (Z.of_nat (length inp)).
  Notation PCONT := (adler_packed_cont ra sp gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m Q).
  Lemma adler_after_outer : forall i a b answer t0 t1 t2 s0 s1 a1 a6 a7 s2 t3 t4 t5 t6,
    0 <= i <= L -> L-i < 5552 -> 0 <= a < ADLER_BASE -> 0 <= b < ADLER_BASE ->
    adler_output (skipn (Z.to_nat i) inp) a b = answer -> PCONT answer ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x11ed4) a1 (Z_to_bv 64 (L-i)) (Z_to_bv 64 b) (Z_to_bv 64 a) (Z_to_bv 64 (B+i)) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15028) fc None m (seg_rom rsegs)).
  Proof. intros i a b answer t0 t1 t2 s0 s1 a1 a6 a7 s2 t3 t4 t5 t6 HI HR HA HB REM CONT.
    assert (NL : 0 <= L-i < 2^64) by (clear -HI HR;lia).
    assert (BA : a+255*(L-i) < 2^40) by (clear -HA HI HR;unfold ADLER_BASE in HA;nia).
    assert (BB : b+(L-i)*a+255*(L-i)*(L-i) < 2^40) by (clear -HA HB HI HR;unfold ADLER_BASE in *;nia).
    eapply adler_after_outer_empty_cert. if_cases BR;zify_bool BR;unfold bv_eqb in BR;
      rewrite !Z_to_bv_unsigned in BR;
      rewrite (bv_wrap_small 64 (L-i) NL),(bv_wrap_small 64 0 ltac:(change (0 <= 0 < 2^64);lia)) in BR;zify_bool BR.
    - assert (E : i=L) by (clear -BR;lia). subst i. rewrite Nat2Z.id,skipn_all in REM.
      assert (EQ : adler_pack a b = answer).
      { change (adler_pack (a mod ADLER_BASE) (b mod ADLER_BASE) = answer) in REM.
        rewrite (Z.mod_small a ADLER_BASE HA),(Z.mod_small b ADLER_BASE HB) in REM. exact REM. }
      unfold adler_packed_cont in CONT. eapply CONT;[exact HA|exact HB|exact EQ].
    - eapply adler_after_outer_size_cert. if_cases BR2;zify_bool BR2;
        rewrite !Z_to_bv_unsigned in BR2;rewrite (bv_wrap_small 64 (L-i) NL) in BR2;zify_bool BR2.
      + eapply adler_inner_init_cert.
        eapply adler_inner_finish with (a:=a) (b:=b) (answer:=answer);
          [exact INP|exact TOP|exact SIZE|exact MAGIC|exact (proj1 HI)|clear -BR2;lia|
           exact (proj1 HA)|exact (proj1 HB)|exact BA|exact BB|exact REM|exact CONT].
      + eapply adler_small_jump_cert.
        eapply adler_tail_path with (a:=a) (b:=b) (answer:=answer);
          [exact INP|exact TOP|exact MAGIC|exact (proj1 HI)|clear -HI BR BR2;lia|
           exact (proj1 HA)|exact (proj1 HB)|exact BA|exact BB|exact REM|exact CONT].
  Qed.
  Theorem adler_outer_loop : forall (k : nat) i g a b answer s0 s1 s2 t4 t5 t6,
    k=Z.to_nat ((L-i)/5552) -> 0 <= i -> i+5552 <= L -> i=5552*g ->
    0 <= a < ADLER_BASE -> 0 <= b < ADLER_BASE ->
    adler_output (skipn (Z.to_nat i) inp) a b = answer -> PCONT answer ->
    evt rsegs Q (MS (mkR ra sp gp tp (Z_to_bv 64 5552) (Z_to_bv 64 (-5552)) (Z_to_bv 64 ADLER_BASE) s0 s1 (Z_to_bv 64 0x11ed4) (Z_to_bv 64 B) (Z_to_bv 64 (L-i)) (Z_to_bv 64 b) (Z_to_bv 64 a) (Z_to_bv 64 (B+i)) (Z_to_bv 64 g) (Z_to_bv 64 ADLER_MAGIC) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 346) t4 t5 t6) F (Z_to_bv 64 0x14f04) fc None m (seg_rom rsegs)).
  Proof.
    induction k as [k IH] using lt_wf_ind. intros i g a b answer s0 s1 s2 t4 t5 t6 HK HI HL GI HA HB REM CONT.
    pose proof (bytes_at_bound _ _ _ _ INP) as PB.
    assert (HB0 : 0 <= B < 2^64) by (clear -PB TOP;lia).
    assert (HG : 0 <= g <= 1048576) by (clear -GI HI HL SIZE;lia).
    assert (HN : 5552 <= L-i <= 1048576) by (clear -HI HL SIZE;lia).
    eapply adler_outer_chunk_init;[exact HB0|exact HG|exact HN|exact GI|].
    replace (B+i+5552) with (B+(i+5552)) by ring.
    eapply adler_outer_blocks with (B:=B) (inp:=inp) (i:=i) (ending:=i+5552) (n:=346%nat) (a:=a) (b:=b) (answer:=answer);
      [exact INP|exact TOP|reflexivity|exact HI|exact HL|exact (proj1 HA)|exact (proj1 HB)|
       clear -HA;unfold ADLER_BASE in HA;cbn;lia|
       clear -HA HB;unfold ADLER_BASE in *;cbn;lia|exact REM|].
    unfold adler_outer_blocks_cont. intros af bf RAF RBF RF h8 h9 h18 h31.
    eapply adler_reduce_outer with (a:=af) (b:=bf);[lia|lia|]. intros h30 h31'.
    assert (PU : bv_unsigned (Z_to_bv 64 (B+i)) = B+i).
    { rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (0 <= B+i < 2^64). clear -HI HL PB TOP;lia. }
    assert (GU : bv_unsigned (Z_to_bv 64 g) = g).
    { rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (0 <= g < 2^64). clear -HG;lia. }
    assert (NU : bv_unsigned (Z_to_bv 64 (L-i-5552)) = L-i-5552).
    { rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (0 <= L-i-5552 < 2^64). clear -HN;lia. }
    rewrite PU,GU,NU.
    replace (L-i-5552) with (L-(i+5552)) by ring.
    replace (B+i+5552) with (B+(i+5552)) by ring.
    assert (RAN : 0 <= af mod ADLER_BASE < ADLER_BASE) by (apply Z.mod_pos_bound;unfold ADLER_BASE;lia).
    assert (RBN : 0 <= bf mod ADLER_BASE < ADLER_BASE) by (apply Z.mod_pos_bound;unfold ADLER_BASE;lia).
    assert (RN : adler_output (skipn (Z.to_nat (i+5552)) inp) (af mod ADLER_BASE) (bf mod ADLER_BASE) = answer).
    { rewrite <- RF. symmetry. apply adler_output_congr;rewrite Z.mod_mod by (unfold ADLER_BASE;lia);reflexivity. }
    assert (NL : 0 <= L-(i+5552) <= 1048576) by (clear -HI HL SIZE;lia).
    assert (SH : 0 <= Z.shiftr (L-(i+5552)) 4 < 2^64).
    { rewrite Z.shiftr_div_pow2 by lia. split;[apply Z.div_pos;lia|apply Z.div_lt_upper_bound;lia]. }
    eapply adler_outer_branch_cert. if_cases BR;zify_bool BR;
      rewrite !Z_to_bv_unsigned in BR;
      rewrite (bv_wrap_small 64 346 ltac:(change (0 <= 346 < 2^64);lia)),
        (bv_wrap_small 64 (Z.shiftr (L-(i+5552)) 4) SH) in BR;zify_bool BR;
      rewrite Z.shiftr_div_pow2 in BR by lia;change (2^4) with 16 in BR.
    - assert (NEXT : (i+5552)+5552 <= L) by (clear -BR NL;lia).
      assert (DQ : (L-i)/5552 = 1+(L-(i+5552))/5552).
      { replace (L-i) with ((L-(i+5552))+1*5552) at 1 by ring. rewrite Z.div_add by lia. ring. }
      assert (HQ : 0 <= (L-(i+5552))/5552) by (apply Z.div_pos;lia).
      eapply (IH (Z.to_nat ((L-(i+5552))/5552)) ltac:(clear -HK DQ HQ;lia)
        (i+5552) (g+1) (af mod ADLER_BASE) (bf mod ADLER_BASE) answer);
        [reflexivity|clear -HI;lia|exact NEXT|clear -GI;ring_simplify;lia|exact RAN|exact RBN|exact RN|exact CONT].
    - eapply adler_after_outer with (a:=af mod ADLER_BASE) (b:=bf mod ADLER_BASE) (answer:=answer);
        [clear -HI HL;lia|clear -BR NL;lia|exact RAN|exact RBN|exact RN|exact CONT].
  Qed.
End AdlerOuter.
