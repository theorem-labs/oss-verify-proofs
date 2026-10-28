(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Spec Require Import Prelim StrFun AtpModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow IcptSpec.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface RT_iface2 D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit Atp_defsA Atp_kitA Atp_objwA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Section ObjN.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.
  Variable d : nat.

  Lemma key_word_rangeA : forall (T S : Z -> Z) (sn i : Z), is_str T S sn i -> sn < 2^56 ->
    0 <= T i < 2^64 /\ Z.land (T i) 72057594037927935 = tval (T i) /\ ttype (T i) = t_str.
  Proof.
    intros T S sn i (o & l & X & (Y1 & Y2 & Y3 & _)) Hsn. rewrite X.
    split; [apply tword_range; [unfold t_str; lia| lia]|].
    split; [| apply ttype_tword; lia].
    change 72057594037927935 with (Z.ones 56). rewrite Z.land_ones by (unfold tword, t_str; lia).
    unfold tval. reflexivity.
  Qed.

  Lemma sbs_byteA : forall o, 0 <= o < ae_sn E -> 0 <= ae_S E o < 256.
  Proof using OK.
    intros o Ho. destruct OK as [_ SBS _ _ _ _ _ _ _ _ _]. unfold Tf. apply Forall_nth_Z; [exact SBS| lia].
  Qed.

  Definition sbuf_bytesA (o l : Z) : list byte := firstn (Z.to_nat l) (skipn (Z.to_nat (o + 4)) (map (Z_to_bv 8) (ae_sbs E))).
  Lemma sbuf_bytesA_at : forall m o l, bytes_at bsegs m (ae_SBUF E) (map (Z_to_bv 8) (ae_sbs E)) -> 0 <= o -> 0 <= l -> o + 4 + l < ae_sn E ->
    bytes_at bsegs m (ae_SBUF E + o + 4) (sbuf_bytesA o l) /\ length (sbuf_bytesA o l) = Z.to_nat l.
  Proof.
    intros m o l HB Ho Hl Hol. unfold sbuf_bytesA. split.
    - replace (ae_SBUF E + o + 4) with (ae_SBUF E + Z.of_nat (Z.to_nat (o + 4))) by lia.
      apply bytes_at_firstn. apply bytes_at_skipn; [exact HB|]. rewrite length_map. lia.
    - rewrite firstn_length_le; [reflexivity|]. rewrite length_skipn, length_map. lia.
  Qed.

End ObjN.
