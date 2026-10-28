(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_defsA Atp_kitA Atp_arrlA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition arrat_W (spq out : Z) : list (Z * Z) := [(spq + -112, spq); (out, out + 24)].

Definition arrat_frame (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : word) (j0 : list byte) : list cell :=
  [CB 8 j0; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma firstn4_le8 : forall v : word, firstn 4 (le8 v) = le4 v.
Proof. intros v. unfold le8, le4, word_to_le_bytes. cbn [Z_to_le_bytes firstn]. reflexivity. Qed.
Lemma zx32_tnext : forall w, (0 <= w < 2^64)%Z -> zx32 (Z_to_bv 64 w) = Z_to_bv 64 (tnext w).
Proof. intros w Hw. unfold zx32. f_equal. rewrite a_u64_small by lia. rewrite <- land32_tnext by lia. symmetry. change 4294967295 with (Z.ones 32). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma sub_fp_tix : forall spq out, sub_fp [(spq + -96 + -16, spq + -96)] (arrat_W spq out).
Proof. intros spq out x Hx. unfold arrat_W in Hx. cbn [outside] in *. lia. Qed.

Section ArrAt.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.
  Variable d : nat.

  Lemma tape_read_lo32 : forall m (i : Z),
    bytes_at asegs m (ae_TAPE E) (u64s (map (Z_to_bv 64) (ae_tws E))) -> 0 <= i < ae_n E ->
    ov_read_bytes asegs m (wa (ae_TAPE E + 8 * i)) 4 = Some (le4 (Z_to_bv 64 (ae_T E i))).
  Proof.
    intros m i HB Hi.
    rewrite (bytes_at_read asegs m (ae_TAPE E) _ (8 * i) 4 HB); [| lia| rewrite u64s_length, length_map; lia]. f_equal.
    replace (Z.to_nat (8 * i)) with (8 * Z.to_nat i)%nat by lia.
    match goal with |- firstn 4 ?X = _ => replace (firstn 4 X) with (firstn 4 (firstn 8 X)) by (rewrite firstn_firstn; reflexivity) end.
    rewrite (u64s_read _ (Z.to_nat i)) by (rewrite length_map; lia). rewrite firstn4_le8.
    f_equal. unfold Tf. rewrite (map_nth (Z_to_bv 64)). reflexivity.
  Qed.

End ArrAt.
