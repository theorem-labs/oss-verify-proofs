(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdSeqTable ZdSeqBuild.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun WStr FseWalkKit ZdWalkKit ZdCellKit ZdSeqBuildW.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma cell_of_bytes : forall b0 b1 b2 b3 b4 b5 b6 b7 : byte, exists c, cellB c = [b0; b1; b2; b3; b4; b5; b6; b7].
Proof.
  intros.
  pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
  pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
  pose proof (bv_unsigned_in_range 8 b4) as R4. pose proof (bv_unsigned_in_range 8 b5) as R5.
  pose proof (bv_unsigned_in_range 8 b6) as R6. pose proof (bv_unsigned_in_range 8 b7) as R7.
  unfold bv_modulus in *. change (2 ^ Z.of_N 8) with 256 in *.
  exists (mkSS (bv_unsigned b0 + 256 * bv_unsigned b1) (bv_unsigned b2) (bv_unsigned b3)
               (bv_unsigned b4 + 256 * bv_unsigned b5 + 65536 * bv_unsigned b6 + 16777216 * bv_unsigned b7)).
  assert (E : [b0; b1; b2; b3; b4; b5; b6; b7]
              = map (Z_to_bv 8) [bv_unsigned b0; bv_unsigned b1; bv_unsigned b2; bv_unsigned b3; bv_unsigned b4; bv_unsigned b5; bv_unsigned b6; bv_unsigned b7])
    by (cbn [map]; rewrite !byte_of_unsigned; reflexivity).
  rewrite E. unfold cellB, seqsym_bytes, zle2, zle4. cbn [ss_next ss_nbAdd ss_nbBits ss_base app map].
  repeat (f_equal; try (apply Mem.Z_to_bv8_mod; change (2^8) with 256; Z.div_mod_to_equations; lia)).
Qed.

Lemma cells_of_bytes : forall (n : nat) (bs : list byte), length bs = (8 * n)%nat ->
  exists cells, length cells = n /\ cellsB cells = bs.
Proof.
  induction n as [|n IH]; intros bs L.
  - destruct bs; [|cbn in L; lia]. exists []. split; reflexivity.
  - destruct bs as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 bs]]]]]]]]; cbn [length] in L; try lia.
    destruct (IH bs ltac:(lia)) as (cells & LC & EC). destruct (cell_of_bytes b0 b1 b2 b3 b4 b5 b6 b7) as (c & Ec).
    exists (c :: cells). split; [cbn [length]; lia|]. rewrite cellsB_cons, Ec, EC. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma le4_of_bytes : forall bs : list byte, length bs = 4%nat -> le4 (le_bytes_to_word bs) = bs.
Proof.
  intros bs HL. unfold le4, le_bytes_to_word.
  pose proof (le_val_range _ (bytes_ok_map bs)) as HR. rewrite length_map, HL in HR.
  change (256 ^ Z.of_nat 4) with (2^32) in HR. rewrite <- bytes_le_to_Z_le_val in HR.
  rewrite unsigned_lit by lia. rewrite <- HL. apply Z_to_le_bytes_to_Z.
Qed.

Lemma cb8_as_c4s : forall segs m A j, rw_cells segs m A [CB 8 j] -> exists a b, rw_cells segs m A [C4 a; C4 b].
Proof.
  intros segs m A j H. pose proof H as [[WF _] _]. cbn in WF. destruct WF as [WFJ _].
  exists (le_bytes_to_word (firstn 4 j)), (le_bytes_to_word (skipn 4 j)).
  eapply rw_cells_recell; [exact H | cbn; auto |].
  cbn [cells_bytes cbytes]. rewrite !app_nil_r.
  rewrite le4_of_bytes by (rewrite firstn_length; lia). rewrite le4_of_bytes by (rewrite skipn_length; lia).
  apply firstn_skipn.
Qed.
