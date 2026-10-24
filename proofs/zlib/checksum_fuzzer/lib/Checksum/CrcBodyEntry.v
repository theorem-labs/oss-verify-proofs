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
  CrcWordBody CrcAlignLoop CrcAlignControl.
Local Opaque csteps raw_byte.
Section CrcBodyEntry.
  Variables (ra sp gp tp s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (B : Z) (inp : list byte).
  Hypothesis INP : bytes_at rsegs m B inp.
  Hypothesis TABLE : bytes_at rsegs m CRC_TABS crc_table_bytes.
  Hypothesis TOP : (B+Z.of_nat (length inp) < 2^64)%Z.
  Hypothesis SIZE : (Z.of_nat (length inp) <= 1048576)%Z.
  Variable Q : machine_state -> Prop.
  Notation L := (Z.of_nat (length inp)).
  Notation AT pc j q h5 h6 h7 h8 h9 h13 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h28 h29 h30 h31 :=
    (MS (mkR ra sp gp tp h5 h6 h7 h8 h9 (Z_to_bv 64 CRC_TABS)
      (Z_to_bv 64 (B+j)) (Z_to_bv 64 (L-j)) h13 (Z_to_bv 64 q) h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 s9 s10 s11 h28 h29 h30 h31)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
  Notation CWC := (crc_word_cont ra sp gp tp s9 s10 s11 F fc m B inp Q).
  Lemma crc_align_dispatch : forall i q answer
    g5 g6 g7 g8 g9 g13 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g28 g29 g30 g31,
    (0 <= i)%Z -> (i+23 <= L)%Z -> (0 <= q < 2^32)%Z ->
    raw_crc (skipn (Z.to_nat i) inp) q = answer -> CWC answer ->
    evt rsegs Q (AT 0x145c8 i q g5 g6 g7 g8 g9 g13 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g28 g29 g30 g31).
  Proof.
    intros i q answer g5 g6 g7 g8 g9 g13 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g28 g29 g30 g31 Hi HL Hq REM CONT.
    pose proof (bytes_at_bound _ _ _ _ INP) as BB.
    assert (PU : bv_unsigned (Z_to_bv 64 (B+i)) = (B+i)%Z).
    { rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (0 <= B+i < 2^64)%Z. clear -Hi HL TOP BB;lia. }
    eapply align_dispatch_cert. rewrite PU,crc_land3_mod.
    set (r := ((B+i) mod 4)%Z).
    assert (HR : (0 <= r < 4)%Z) by (apply Z.mod_pos_bound;lia).
    if_cases BR;zify_bool BR;unfold bv_eqb in BR;rewrite !Z_to_bv_unsigned in BR;
      rewrite (bv_wrap_small 64 r ltac:(change (0 <= r < 2^64)%Z;lia)),
        (bv_wrap_small 64 0 ltac:(change (0 <= 0 < 2^64)%Z;lia)) in BR;zify_bool BR.
    - eapply crc_word_body with (answer:=answer) (q:=q);
        [exact INP|exact TABLE|exact TOP|exact SIZE|exact Hi|lia|exact Hq|exact REM|exact CONT].
    - eapply align_init_cert. rewrite PU.
      set (e := (i+(4-r))%Z).
      assert (HE : ((B+e) mod 4 = 0)%Z).
      { pose proof (Z.div_mod (B+i) 4 ltac:(lia)) as DP. fold r in DP.
        replace (B+e)%Z with (4*((B+i)/4+1))%Z by (unfold e;lia).
        rewrite Z.mul_comm,Z.mod_mul by lia. reflexivity. }
      assert (EI : (0 <= e)%Z) by (unfold e;clear -HR Hi;lia).
      assert (EL : (e+20 <= L)%Z) by (unfold e;clear -HR BR HL;lia).
      eapply crc_align_loop with (ending:=e) (n:=Z.to_nat (3-r)) (q:=q) (answer:=answer);
        [exact INP|exact TABLE|exact TOP|exact HE|
         unfold e;rewrite Nat2Z.inj_succ,Z2Nat.id by lia;lia|
         lia|exact Hi|exact EL|exact Hq|exact REM|].
      unfold crc_align_cont. intros qf HF RF h13 h16 h17.
      eapply crc_word_body with (answer:=answer) (q:=qf);
        [exact INP|exact TABLE|exact TOP|exact SIZE|exact EI|exact EL|exact HF|exact RF|exact CONT].
  Qed.
  Theorem crc_body_entry : forall i q answer
    g5 g6 g7 g8 g9 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g28 g29 g30 g31,
    (0 <= i <= L)%Z -> (0 <= q < 2^32)%Z ->
    raw_crc (skipn (Z.to_nat i) inp) q = answer -> CWC answer ->
    evt rsegs Q (AT 0x145c4 i q g5 g6 g7 g8 g9 (Z_to_bv 64 23) g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g28 g29 g30 g31).
  Proof.
    intros i q answer g5 g6 g7 g8 g9 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g28 g29 g30 g31 Hi Hq REM CONT.
    zstep. if_cases K;zify_cond K.
    - unfold crc_word_cont in CONT. exact (CONT i q Hi Hq REM
        g5 g6 g7 g8 g9 (Z_to_bv 64 23) g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g28 g29 g30 g31).
    - eapply crc_align_dispatch with (answer:=answer) (q:=q);
        [exact (proj1 Hi)|lia|exact Hq|exact REM|exact CONT].
  Qed.
End CrcBodyEntry.
