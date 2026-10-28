From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx41g.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma bi_bd_hinv : forall mm A (k : word) c pad S n,
  1 <= c <= 64 -> (8 <= n -> c <= 8) ->
  rw_cells usegs mm A (bitd_cells k (Z_to_bv 64 c) pad (bitd_ptr S n) S) ->
  exists o, RZ_huf_dx41g.HINV o n c /\
    rw_cells usegs mm A [C8 k; C4 (Z_to_bv 64 c); CB 4 pad; C8 (Z_to_bv 64 (S + o)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))].
Proof.
  intros mm A k c pad S n HC HC8 H. unfold bitd_cells, bitd_ptr in H.
  destruct (8 <=? n) eqn:E8; [apply Z.leb_le in E8 | apply Z.leb_gt in E8].
  - exists (n - 8). split.
    + unfold RZ_huf_dx41g.HINV. split; [lia | split; [lia | right; split; [lia | apply HC8; exact E8]]].
    + replace (S + (n - 8)) with (S + n - 8) by lia. exact H.
  - exists 0. split.
    + unfold RZ_huf_dx41g.HINV. split; [lia | split; [lia | left; reflexivity]].
    + replace (S + 0) with S by lia. exact H.
Qed.
