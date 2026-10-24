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
  CrcBraidAll CrcBraidSetup CrcBraidModel CrcBraidWord CrcWordChunks CrcMergeMachine CrcWord.
Local Opaque csteps SX merge_model block5.
Lemma crc_drop_length : forall n g,
  Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (-20*g))+bv_unsigned (Z_to_bv 64 n)) =
  Z_to_bv 64 (n-20*g).
Proof.
  intros n g. apply Z_to_bv_eqm. rewrite !Z_to_bv_unsigned.
  change ((((-20*g) mod 2^64)+(n mod 2^64)) mod 2^64 = (n-20*g) mod 2^64)%Z.
  rewrite <- Z.add_mod by lia. f_equal. ring.
Qed.
Section CrcWordBody.
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
  Definition crc_word_cont (answer : Z) : Prop :=
    forall j qf, (0 <= j <= L)%Z -> (0 <= qf < 2^32)%Z ->
    raw_crc (skipn (Z.to_nat j) inp) qf = answer ->
    forall h5 h6 h7 h8 h9 h13 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h28 h29 h30 h31,
    evt rsegs Q (AT 0x14a60 j qf h5 h6 h7 h8 h9 h13 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h28 h29 h30 h31).
  Theorem crc_word_body : forall i q answer
    g5 g6 g7 g8 g9 g13 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g28 g29 g30 g31,
    (0 <= i)%Z -> (i+20 <= L)%Z -> (0 <= q < 2^32)%Z ->
    raw_crc (skipn (Z.to_nat i) inp) q = answer -> crc_word_cont answer ->
    evt rsegs Q (AT 0x14614 i q g5 g6 g7 g8 g9 g13 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g28 g29 g30 g31).
  Proof.
    intros i q answer g5 g6 g7 g8 g9 g13 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g28 g29 g30 g31 Hi HL Hq REM CONT.
    assert (HN : (0 <= L-i < 2^64)%Z) by (clear -Hi HL SIZE;lia).
    set (g := ((L-i)/20)%Z).
    pose proof (Z.div_mod (L-i) 20 ltac:(lia)) as DN.
    pose proof (Z.mod_pos_bound (L-i) 20 ltac:(lia)) as RN.
    fold g in DN.
    assert (HG : (1 <= g <= 1048576)%Z) by (clear -Hi HL SIZE DN RN;lia).
    assert (GE : (i+20*g <= L)%Z) by (clear -DN RN;lia).
    assert (GI : (0 <= i+20*g-20)%Z) by (clear -Hi HG;lia).
    assert (LOWQ : (q mod 2^32 = q)%Z) by (apply Z.mod_small;exact Hq).
    assert (MC0 : merge5 (q mod 2^32) (0 mod 2^32) (0 mod 2^32) (0 mod 2^32) (0 mod 2^32) = csteps 128 q).
    { rewrite LOWQ. change (merge5 q 0 0 0 0 = csteps 128 q). apply merge5_initial. }
    eapply crc_div20_setup with (t1:=g6) (a2:=Z_to_bv 64 (L-i)) (a3:=g13) (a5:=g15) (a6:=g16);[exact HN|]. fold g.
    eapply braid_setup_branch_cert. if_cases BR;zify_bool BR;unfold bv_eqb in BR;
      rewrite !Z_to_bv_unsigned in BR;
      rewrite (bv_wrap_small 64 g ltac:(change (0 <= g < 2^64)%Z;lia)),
        (bv_wrap_small 64 1 ltac:(change (0 <= 1 < 2^64)%Z;lia)) in BR;zify_bool BR.
    - eapply braid_single_cert.
      eapply crc_braid_merge;
        [exact INP|exact TABLE|exact Hi|exact HL|lia|lia|lia|lia|lia|].
      intros h5 h6 h7 h15 h16 h17 h28 h29.
      rewrite crc_drop_length.
      replace (L-i-20*g)%Z with (L-(i+20))%Z by (clear -BR;lia).
      rewrite merge_model_finish,(braid_finish_serial q _ _ _ _ _ _ _ _ _ _ MC0).
      pose proof (block5_range q _ _ _ _ _ Hq
        (bword4_unsigned_range inp i) (bword4_unsigned_range inp (i+4))
        (bword4_unsigned_range inp (i+8)) (bword4_unsigned_range inp (i+12))
        (bword4_unsigned_range inp (i+16))) as HF.
      rewrite (raw_suffix_twenty inp i q Hi HL) in REM.
      unfold crc_word_cont in CONT. exact (CONT (i+20)%Z _ ltac:(lia) HF REM
        h5 h6 h7 g8 g9 (Z_to_bv 64 (-20*g)) h15 h16 h17 g18 g19 g20 g21 g22 g23 g24 h28 h29 g30 g31).
    - eapply braid_init_cert with (t1:=Z_to_bv 64 g);[exact HG|].
      pose proof (bytes_at_bound _ _ _ _ INP) as BB.
      assert (PU : bv_unsigned (Z_to_bv 64 (B+i)) = (B+i)%Z).
      { rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (0 <= B+i < 2^64)%Z. clear -Hi HL TOP BB;lia. }
      rewrite PU.
      replace (g*20+(B+i)-20)%Z with (B+(i+20*g-20))%Z by ring.
      assert (LN : Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (-20*g))+bv_unsigned (Z_to_bv 64 (L-i))) =
        Z_to_bv 64 (L-((i+20*g-20)+20))).
      { rewrite crc_drop_length. f_equal. ring. }
      eapply crc_braid_all with (ending:=(i+20*g-20)%Z) (n:=Z.to_nat (g-2)) (q:=q) (answer:=answer);
        [exact INP|exact TABLE|exact TOP|exact LN|
         clear -HG BR;rewrite Nat2Z.inj_succ,Z2Nat.id by lia;lia|exact Hi|clear -GE;lia|exact Hq|
         lia|lia|lia|lia|lia|exact MC0|exact REM|].
      unfold crc_braid_tail_cont. intros qf HF RF h5 h6 h7 h8 h9 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h28 h29 h31.
      unfold crc_word_cont in CONT.
      exact (CONT ((i+20*g-20)+20)%Z qf ltac:(clear -Hi HG GE;lia) HF RF
        h5 h6 h7 h8 h9 (Z_to_bv 64 (-20*g)) h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h28 h29
        (Z_to_bv 64 0x11554) h31).
  Qed.
End CrcWordBody.
