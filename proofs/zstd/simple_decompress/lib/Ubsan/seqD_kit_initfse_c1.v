(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import ZdSeqW KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXUb KXUb2 SepHide.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_seq_kit seqD_kit_initfse seqD_kit_initfse_k.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac kx_pull ::= kx_pull1; kx_pull1.
#[local] Ltac kx_lia ::= kx_bv_ranges; first [ solve [kx_lia_pruned] | solve [lia] ].

Lemma ifs_c1 : zd_initfse_stmt_if (fun bc tl ptr SEQ n => 65 <= bc + tl).
Proof.
  unfold zd_initfse_stmt_if, PZD_INITFSE. intros until t.
  intros MI HBD HST TB OK SQB LN N1 R1 R2 R3 R4 R5 R5b R6 R7 A1 A2 A3 DJ1 DJ2 DJ3 DJ4 DJ5 RB RBB IB C. cbv beta in C.
  pose proof (seq_rdn_log usegs m T k t TB OK) as RL. pose proof (seq_tl_range k t OK) as RT.
  remember (st_log t) as tl eqn:Etl.
  pose proof (bitmask_know m tl MI ltac:(clear - RT; lia)) as BK. unfold BITMASK in BK.
  assert (RP : 1 <= 2^tl <= 512) by (clear - RT; split; [pose proof (Z.pow_pos_nonneg 2 tl); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
  assert (MU : munch [(BD, BD + 40); (STP, STP + 16)] m m) by apply munch_refl.
  assert (WM : wmono usegs m m) by apply wmono_refl.
  assert (RG : 4096 <= BD < 2^47 /\ 4096 <= STP < 2^47 /\ 4096 <= SEQ < 2^47 /\ 4096 <= SEQ + n < 2^47) by lia.
  unfold bitd_cells in HBD.
  clear TB.
  hide DJ1. hide DJ2. hide DJ3. hide DJ4. hide DJ5.
  kx_autoLx (@nil Z) 200%nat
      [KZRange bc 0 82; KZRange (bc + tl) 65 91; KZRange n 1 (2^47);
       KZRange BD 4096 (2^47 - 40); KZRange STP 4096 (2^47 - 16); KZRange T 4096 (2^47); KZRange SEQ 4096 (2^47); KZRange (SEQ + n) 4096 (2^47);
       KZRange tl 0 9; KZRange (2^tl) 1 512; KZAlign BD 8; KZAlign STP 8; KZAlign T 4;
       KZWord (T + 4) 4 tl; KZWord (BITMASK + 4 * tl) 4 (2^tl - 1);
       KZWr BD 40; KZWr STP 16; KZDisj BD 40 STP 16; KZDisj BD 40 SEQ n; KZDisj STP 16 SEQ n;
       KZDisj BD 40 T 16; KZDisj STP 16 T 16]
      [(SEQ, n); (BD, 40); (STP, 16)].
  all: try (lazymatch goal with |- _ /\ _ /\ _ /\ rdn _ _ _ _ = Some _ => split; [lia | split; [lia | split; [lia | assumption]]] end).
  all: try (lazymatch goal with |- evt _ _ _ => fail | _ => kx_z end).
  all: try (lazymatch goal with |- evt _ _ _ => fail | _ => try kx_side_pre;
            lazymatch goal with |- _ /\ _ /\ (?A + _ <= ?B \/ _) =>
              let X := base_of A in let Y := base_of B in unhide_related X Y;
              repeat match goal with H : hidden _ |- _ => clear H end; repeat split; lia end end).
  all: lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1dd74) _ _ _ _) => kx_trap_fast | _ => idtac end.
  all: unhide.
  all: kx_mem.
  all: zstep.
  all: kx_abs.
  all: try kx_mkR_fold.
  all: ifs_close.
Qed.
