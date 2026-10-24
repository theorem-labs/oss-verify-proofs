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
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import CrcAlignByte CrcAlignControl CrcSuffix.
Lemma crc_land3_mod : forall a, Z.land a 3 = (a mod 4)%Z.
Proof. intros. change (Z.land a (Z.ones 2) = a mod 2^2)%Z. rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma crc_aligned_gap : forall x y,
  (y mod 4 = 0)%Z -> (0 < y-x < 4)%Z -> (x mod 4 <> 0)%Z.
Proof.
  intros x y HY Hgap HX.
  pose proof (Z.div_mod x 4 ltac:(lia)) as DX.
  pose proof (Z.div_mod y 4 ltac:(lia)) as DY. lia.
Qed.
Section AlignLoop.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (B ending : Z) (inp : list byte).
  Hypothesis INP : bytes_at rsegs m B inp.
  Hypothesis TABLE : bytes_at rsegs m CRC_TABS crc_table_bytes.
  Hypothesis TOP : (B+Z.of_nat (length inp) < 2^64)%Z.
  Hypothesis ALIGNED : ((B+ending) mod 4 = 0)%Z.
  Variable Q : machine_state -> Prop.
  Notation L := (Z.of_nat (length inp)).
  Notation AT pc x11 x12 x13 x14 x16 x17 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 CRC_TABS)
      x11 x12 x13 x14 (Z_to_bv 64 1) x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
  Definition crc_align_cont (answer : Z) : Prop :=
    forall qf, (0 <= qf < 2^32)%Z -> raw_crc (skipn (Z.to_nat ending) inp) qf = answer ->
    forall x13 x16 x17, evt rsegs Q
      (AT 0x14614 (Z_to_bv 64 (B+ending)) (Z_to_bv 64 (L-ending)) x13 (Z_to_bv 64 qf) x16 x17).
  Theorem crc_align_loop : forall (n : nat) (i q answer : Z) g16 g17,
    (ending=i+Z.of_nat (S n))%Z -> (n<3)%nat -> (0 <= i)%Z -> (ending+20 <= L)%Z ->
    (0 <= q < 2^32)%Z -> raw_crc (skipn (Z.to_nat i) inp) q = answer ->
    crc_align_cont answer ->
    evt rsegs Q (AT 0x145d8 (Z_to_bv 64 (B+i)) (Z_to_bv 64 (L-i))
      (Z_to_bv 64 (B+i+1)) (Z_to_bv 64 q) g16 g17).
  Proof.
    induction n as [n IH] using lt_wf_ind.
    intros i q answer g16 g17 END Hn Hi HL Hq REM CONT.
    pose proof (bytes_at_bound _ _ _ _ INP) as BB.
    assert (NI : (0 <= i < L)%Z) by (clear -END Hi HL;lia).
    pose proof (raw_byte_range q (bbyte inp i) Hq) as HQN.
    rewrite (raw_suffix_step inp i q NI) in REM.
    eapply crc_align_byte;[exact INP|exact TABLE|exact NI|exact Hq|].
    intros h16.
    assert (NL : (0 <= L-i < 2^64)%Z) by (clear -Hi TOP BB END HL;lia).
    assert (NP : (0 <= B+i+1 < 2^64)%Z) by (clear -Hi TOP BB END HL;lia).
    eapply align_branch_cert. if_cases BR;zify_bool BR;unfold bv_eqb in BR;
      rewrite !Z_to_bv_unsigned in BR;
      rewrite (bv_wrap_small 64 (L-i) NL),(bv_wrap_small 64 1 ltac:(change (0 <= 1 < 2^64)%Z;lia)) in BR;zify_bool BR.
    - exfalso. clear -BR END HL. lia.
    - eapply align_next_cert.
      assert (PU : bv_unsigned (Z_to_bv 64 (B+i+1)) = (B+i+1)%Z).
      { rewrite Z_to_bv_unsigned. apply bv_wrap_small. exact NP. }
      rewrite PU,crc_land3_mod.
      pose proof (Z.mod_pos_bound (B+i+1) 4 ltac:(lia)) as HM.
      if_cases BR2;zify_bool BR2;unfold bv_eqb in BR2;rewrite !Z_to_bv_unsigned in BR2;
        rewrite (bv_wrap_small 64 ((B+i+1) mod 4) ltac:(change (0 <= (B+i+1) mod 4 < 2^64)%Z;lia)),(bv_wrap_small 64 0 ltac:(change (0 <= 0 < 2^64)%Z;lia)) in BR2;zify_bool BR2.
      + destruct n as [|n].
        * exfalso. assert (E : (B+i+1=B+ending)%Z) by (clear -END;cbn in END;lia).
          rewrite E,ALIGNED in BR2. lia.
        * replace (B+i+1+1)%Z with (B+(i+1)+1)%Z by ring.
          replace (B+i+1)%Z with (B+(i+1))%Z by ring.
          replace (L-i-1)%Z with (L-(i+1))%Z by ring.
          eapply (IH n ltac:(apply Nat.lt_succ_diag_r) (i+1)%Z (raw_byte q (bbyte inp i)) answer);
            [clear -END;rewrite Nat2Z.inj_succ in END;lia|lia|lia|exact HL|exact HQN|exact REM|exact CONT].
      + destruct n as [|n].
        * assert (E : (i+1=ending)%Z) by (clear -END;cbn in END;lia).
          unfold crc_align_cont in CONT.
          replace (B+i+1)%Z with (B+ending)%Z by (clear -E;lia).
          replace (L-i-1)%Z with (L-ending)%Z by (clear -E;lia).
          assert (RE : raw_crc (skipn (Z.to_nat ending) inp) (raw_byte q (bbyte inp i)) = answer).
          { rewrite <- E. exact REM. }
          exact (CONT (raw_byte q (bbyte inp i)) HQN RE (Z_to_bv 64 (B+ending+1))
            (Z_to_bv 64 ((B+ending) mod 4)) (Z_to_bv 64 (L-i))).
        * exfalso. apply (crc_aligned_gap (B+i+1) (B+ending) ALIGNED ltac:(clear -END Hn;rewrite Nat2Z.inj_succ in END;lia)). exact BR2.
  Qed.
End AlignLoop.
