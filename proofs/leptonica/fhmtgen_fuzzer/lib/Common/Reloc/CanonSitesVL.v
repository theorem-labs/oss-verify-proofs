(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Import PropExec.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc Require Import Reloc RelocCode RelocSites.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

(* [comment removed for export] *)
Definition vlcs_237e0 : csite := mkSite 0x237e0 230%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 240%positive 0x23878).
(* [comment removed for export] *)
Definition vlcs_2381c : csite := mkSite 0x2381c 230%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1091%positive 0x1cdb8).
(* [comment removed for export] *)
Definition vlcs_23828 : csite := mkSite 0x23828 230%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_2382c : csite := mkSite 0x2382c 230%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x23828 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_2383c : csite := mkSite 0x2383c 230%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23840 : csite := mkSite 0x23840 230%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23844 : csite := mkSite 0x23844 230%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x2383c 413%positive 0x103c3).
(* [comment removed for export] *)
Definition vlcs_23848 : csite := mkSite 0x23848 230%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x23840 423%positive 0x104e2).
(* [comment removed for export] *)
Definition vlcs_2385c : csite := mkSite 0x2385c 230%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1012%positive 0x13730).
(* [comment removed for export] *)
Definition vlcs_2388c : csite := mkSite 0x2388c 240%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 241%positive 0x239c0).
(* [comment removed for export] *)
Definition vlcs_238b8 : csite := mkSite 0x238b8 240%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_238bc : csite := mkSite 0x238bc 240%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 9 11 imm)) (SK_lo12 0x238b8 5028%positive 0x1f430).
(* [comment removed for export] *)
Definition vlcs_238d8 : csite := mkSite 0x238d8 240%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 236%positive 0x242cc).
(* [comment removed for export] *)
Definition vlcs_238e0 : csite := mkSite 0x238e0 240%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_238e4 : csite := mkSite 0x238e4 240%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x238e0 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_238f4 : csite := mkSite 0x238f4 240%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_238f8 : csite := mkSite 0x238f8 240%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_238fc : csite := mkSite 0x238fc 240%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x238f4 413%positive 0x103c3).
(* [comment removed for export] *)
Definition vlcs_23900 : csite := mkSite 0x23900 240%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x238f8 419%positive 0x1046c).
(* [comment removed for export] *)
Definition vlcs_23918 : csite := mkSite 0x23918 240%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1012%positive 0x13730).
(* [comment removed for export] *)
Definition vlcs_23948 : csite := mkSite 0x23948 240%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1035%positive 0x15b38).
(* [comment removed for export] *)
Definition vlcs_2395c : csite := mkSite 0x2395c 240%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 248%positive 0x247d4).
(* [comment removed for export] *)
Definition vlcs_23968 : csite := mkSite 0x23968 240%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1035%positive 0x15b38).
(* [comment removed for export] *)
Definition vlcs_2396c : csite := mkSite 0x2396c 240%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23970 : csite := mkSite 0x23970 240%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x2396c 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_23980 : csite := mkSite 0x23980 240%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23984 : csite := mkSite 0x23984 240%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23988 : csite := mkSite 0x23988 240%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x23980 458%positive 0x108f4).
(* [comment removed for export] *)
Definition vlcs_2398c : csite := mkSite 0x2398c 240%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x23984 419%positive 0x1046c).
(* [comment removed for export] *)
Definition vlcs_23994 : csite := mkSite 0x23994 240%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1012%positive 0x13730).
(* [comment removed for export] *)
Definition vlcs_23a14 : csite := mkSite 0x23a14 241%positive OP_AUIPC (SH20 (fun imm => Auipc 13 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23a18 : csite := mkSite 0x23a18 241%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 8 13 imm)) (SK_lo12 0x23a14 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_23a28 : csite := mkSite 0x23a28 241%positive OP_AUIPC (SH20 (fun imm => Auipc 13 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23a2c : csite := mkSite 0x23a2c 241%positive OP_AUIPC (SH20 (fun imm => Auipc 14 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23a30 : csite := mkSite 0x23a30 241%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 13 13 imm)) (SK_lo12 0x23a28 462%positive 0x10950).
(* [comment removed for export] *)
Definition vlcs_23a34 : csite := mkSite 0x23a34 241%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 14 14 imm)) (SK_lo12 0x23a2c 426%positive 0x10553).
(* [comment removed for export] *)
Definition vlcs_23a50 : csite := mkSite 0x23a50 241%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1011%positive 0x13694).
(* [comment removed for export] *)
Definition vlcs_23a5c : csite := mkSite 0x23a5c 241%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23a60 : csite := mkSite 0x23a60 241%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23a64 : csite := mkSite 0x23a64 241%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x23a5c 420%positive 0x1047c).
(* [comment removed for export] *)
Definition vlcs_23a68 : csite := mkSite 0x23a68 241%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x23a60 426%positive 0x10553).
(* [comment removed for export] *)
Definition vlcs_23a70 : csite := mkSite 0x23a70 241%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23a74 : csite := mkSite 0x23a74 241%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x23a70 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_23a84 : csite := mkSite 0x23a84 241%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23a88 : csite := mkSite 0x23a88 241%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23a8c : csite := mkSite 0x23a8c 241%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x23a84 400%positive 0x10298).
(* [comment removed for export] *)
Definition vlcs_23a90 : csite := mkSite 0x23a90 241%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x23a88 426%positive 0x10553).
(* [comment removed for export] *)
Definition vlcs_23a98 : csite := mkSite 0x23a98 241%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23a9c : csite := mkSite 0x23a9c 241%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x23a98 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_23aac : csite := mkSite 0x23aac 241%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23ab0 : csite := mkSite 0x23ab0 241%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23ab4 : csite := mkSite 0x23ab4 241%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x23aac 441%positive 0x10713).
(* [comment removed for export] *)
Definition vlcs_23ab8 : csite := mkSite 0x23ab8 241%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x23ab0 426%positive 0x10553).
(* [comment removed for export] *)
Definition vlcs_23ad8 : csite := mkSite 0x23ad8 241%positive OP_AUIPC (SH20 (fun imm => Auipc 13 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23adc : csite := mkSite 0x23adc 241%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 8 13 imm)) (SK_lo12 0x23ad8 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_23aec : csite := mkSite 0x23aec 241%positive OP_AUIPC (SH20 (fun imm => Auipc 13 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23af0 : csite := mkSite 0x23af0 241%positive OP_AUIPC (SH20 (fun imm => Auipc 14 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23af4 : csite := mkSite 0x23af4 241%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 13 13 imm)) (SK_lo12 0x23aec 462%positive 0x10950).
(* [comment removed for export] *)
Definition vlcs_23af8 : csite := mkSite 0x23af8 241%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 14 14 imm)) (SK_lo12 0x23af0 426%positive 0x10553).
(* [comment removed for export] *)
Definition vlcs_23b14 : csite := mkSite 0x23b14 241%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1011%positive 0x13694).
(* [comment removed for export] *)
Definition vlcs_23b20 : csite := mkSite 0x23b20 241%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23b24 : csite := mkSite 0x23b24 241%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23b28 : csite := mkSite 0x23b28 241%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x23b20 452%positive 0x10838).
(* [comment removed for export] *)
Definition vlcs_23b2c : csite := mkSite 0x23b2c 241%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x23b24 426%positive 0x10553).
(* [comment removed for export] *)
Definition vlcs_23b34 : csite := mkSite 0x23b34 241%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23b38 : csite := mkSite 0x23b38 241%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x23b34 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_23b48 : csite := mkSite 0x23b48 241%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23b4c : csite := mkSite 0x23b4c 241%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23b50 : csite := mkSite 0x23b50 241%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x23b48 417%positive 0x1041b).
(* [comment removed for export] *)
Definition vlcs_23b54 : csite := mkSite 0x23b54 241%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x23b4c 426%positive 0x10553).
(* [comment removed for export] *)
Definition vlcs_23b78 : csite := mkSite 0x23b78 241%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1012%positive 0x13730).
(* [comment removed for export] *)
Definition vlcs_23b88 : csite := mkSite 0x23b88 241%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23b8c : csite := mkSite 0x23b8c 241%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x23b88 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_23b9c : csite := mkSite 0x23b9c 241%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23ba0 : csite := mkSite 0x23ba0 241%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23ba4 : csite := mkSite 0x23ba4 241%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x23b9c 411%positive 0x1035b).
(* [comment removed for export] *)
Definition vlcs_23ba8 : csite := mkSite 0x23ba8 241%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x23ba0 426%positive 0x10553).
(* [comment removed for export] *)
Definition vlcs_23bbc : csite := mkSite 0x23bbc 241%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23bc0 : csite := mkSite 0x23bc0 241%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x23bbc 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_23bd0 : csite := mkSite 0x23bd0 241%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23bd4 : csite := mkSite 0x23bd4 241%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23bd8 : csite := mkSite 0x23bd8 241%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x23bd0 464%positive 0x10991).
(* [comment removed for export] *)
Definition vlcs_23bdc : csite := mkSite 0x23bdc 241%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x23bd4 426%positive 0x10553).
(* [comment removed for export] *)
Definition vlcs_23be8 : csite := mkSite 0x23be8 241%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23bec : csite := mkSite 0x23bec 241%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x23be8 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_23bfc : csite := mkSite 0x23bfc 241%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23c00 : csite := mkSite 0x23c00 241%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23c04 : csite := mkSite 0x23c04 241%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x23bfc 444%positive 0x1075b).
(* [comment removed for export] *)
Definition vlcs_23c08 : csite := mkSite 0x23c08 241%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x23c00 426%positive 0x10553).
(* [comment removed for export] *)
Definition vlcs_23c0c : csite := mkSite 0x23c0c 241%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1011%positive 0x13694).
(* [comment removed for export] *)
Definition vlcs_23c48 : csite := mkSite 0x23c48 241%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1034%positive 0x15a00).
(* [comment removed for export] *)
Definition vlcs_23c58 : csite := mkSite 0x23c58 241%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 244%positive 0x23fbc).
(* [comment removed for export] *)
Definition vlcs_23c64 : csite := mkSite 0x23c64 241%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 245%positive 0x24044).
(* [comment removed for export] *)
Definition vlcs_23c70 : csite := mkSite 0x23c70 241%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 246%positive 0x240cc).
(* [comment removed for export] *)
Definition vlcs_23c9c : csite := mkSite 0x23c9c 241%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23ca0 : csite := mkSite 0x23ca0 241%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x23c9c 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_23cb0 : csite := mkSite 0x23cb0 241%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23cb4 : csite := mkSite 0x23cb4 241%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23cb8 : csite := mkSite 0x23cb8 241%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x23cb0 413%positive 0x103c3).
(* [comment removed for export] *)
Definition vlcs_23cbc : csite := mkSite 0x23cbc 241%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x23cb4 426%positive 0x10553).
(* [comment removed for export] *)
Definition vlcs_23cf8 : csite := mkSite 0x23cf8 242%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23cfc : csite := mkSite 0x23cfc 242%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x23cf8 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_23d0c : csite := mkSite 0x23d0c 242%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23d10 : csite := mkSite 0x23d10 242%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23d14 : csite := mkSite 0x23d14 242%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x23d0c 408%positive 0x10331).
(* [comment removed for export] *)
Definition vlcs_23d18 : csite := mkSite 0x23d18 242%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x23d10 453%positive 0x10850).
(* [comment removed for export] *)
Definition vlcs_23d20 : csite := mkSite 0x23d20 242%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1010%positive 0x13660).
(* [comment removed for export] *)
Definition vlcs_23d7c : csite := mkSite 0x23d7c 243%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23d80 : csite := mkSite 0x23d80 243%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 11 11 imm)) (SK_lo12 0x23d7c 5028%positive 0x1f438).
(* [comment removed for export] *)
Definition vlcs_23d90 : csite := mkSite 0x23d90 243%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1035%positive 0x15b38).
(* [comment removed for export] *)
Definition vlcs_23da4 : csite := mkSite 0x23da4 243%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 248%positive 0x247d4).
(* [comment removed for export] *)
Definition vlcs_23db0 : csite := mkSite 0x23db0 243%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1035%positive 0x15b38).
(* [comment removed for export] *)
Definition vlcs_23dc0 : csite := mkSite 0x23dc0 243%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23dc4 : csite := mkSite 0x23dc4 243%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x23dc0 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_23dd4 : csite := mkSite 0x23dd4 243%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23dd8 : csite := mkSite 0x23dd8 243%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23ddc : csite := mkSite 0x23ddc 243%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x23dd4 466%positive 0x109d5).
(* [comment removed for export] *)
Definition vlcs_23de0 : csite := mkSite 0x23de0 243%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x23dd8 428%positive 0x10586).
(* [comment removed for export] *)
Definition vlcs_23df4 : csite := mkSite 0x23df4 243%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1011%positive 0x13694).
(* [comment removed for export] *)
Definition vlcs_23e8c : csite := mkSite 0x23e8c 231%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23e90 : csite := mkSite 0x23e90 231%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x23e8c 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_23ea0 : csite := mkSite 0x23ea0 231%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23ea4 : csite := mkSite 0x23ea4 231%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23ea8 : csite := mkSite 0x23ea8 231%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x23ea0 408%positive 0x10331).
(* [comment removed for export] *)
Definition vlcs_23eac : csite := mkSite 0x23eac 231%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x23ea4 468%positive 0x10a41).
(* [comment removed for export] *)
Definition vlcs_23eb4 : csite := mkSite 0x23eb4 231%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1010%positive 0x13660).
(* [comment removed for export] *)
Definition vlcs_23f04 : csite := mkSite 0x23f04 232%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 248%positive 0x247d4).
(* [comment removed for export] *)
Definition vlcs_23f20 : csite := mkSite 0x23f20 232%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 237%positive 0x244bc).
(* [comment removed for export] *)
Definition vlcs_23f34 : csite := mkSite 0x23f34 232%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23f38 : csite := mkSite 0x23f38 232%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x23f34 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_23f48 : csite := mkSite 0x23f48 232%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23f4c : csite := mkSite 0x23f4c 232%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23f50 : csite := mkSite 0x23f50 232%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x23f48 408%positive 0x10331).
(* [comment removed for export] *)
Definition vlcs_23f54 : csite := mkSite 0x23f54 232%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x23f4c 437%positive 0x10671).
(* [comment removed for export] *)
Definition vlcs_23f6c : csite := mkSite 0x23f6c 232%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1010%positive 0x13660).
(* [comment removed for export] *)
Definition vlcs_23f70 : csite := mkSite 0x23f70 232%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23f74 : csite := mkSite 0x23f74 232%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x23f70 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_23f84 : csite := mkSite 0x23f84 232%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23f88 : csite := mkSite 0x23f88 232%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23f8c : csite := mkSite 0x23f8c 232%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x23f84 454%positive 0x1085a).
(* [comment removed for export] *)
Definition vlcs_23f90 : csite := mkSite 0x23f90 232%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x23f88 437%positive 0x10671).
(* [comment removed for export] *)
Definition vlcs_23f98 : csite := mkSite 0x23f98 232%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1010%positive 0x13660).
(* [comment removed for export] *)
Definition vlcs_23fd8 : csite := mkSite 0x23fd8 244%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23fdc : csite := mkSite 0x23fdc 244%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x23fd8 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_23fec : csite := mkSite 0x23fec 244%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23ff0 : csite := mkSite 0x23ff0 244%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_23ff4 : csite := mkSite 0x23ff4 244%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x23fec 408%positive 0x10331).
(* [comment removed for export] *)
Definition vlcs_23ff8 : csite := mkSite 0x23ff8 244%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x23ff0 465%positive 0x109c5).
(* [comment removed for export] *)
Definition vlcs_24000 : csite := mkSite 0x24000 244%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1010%positive 0x13660).
(* [comment removed for export] *)
Definition vlcs_24008 : csite := mkSite 0x24008 244%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_2400c : csite := mkSite 0x2400c 244%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 11 11 imm)) (SK_lo12 0x24008 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_24020 : csite := mkSite 0x24020 244%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_24024 : csite := mkSite 0x24024 244%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_24028 : csite := mkSite 0x24028 244%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x24020 422%positive 0x104cf).
(* [comment removed for export] *)
Definition vlcs_2402c : csite := mkSite 0x2402c 244%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x24024 465%positive 0x109c5).
(* [comment removed for export] *)
Definition vlcs_24034 : csite := mkSite 0x24034 244%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1010%positive 0x13660).
(* [comment removed for export] *)
Definition vlcs_24060 : csite := mkSite 0x24060 245%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_24064 : csite := mkSite 0x24064 245%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x24060 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_24074 : csite := mkSite 0x24074 245%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_24078 : csite := mkSite 0x24078 245%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_2407c : csite := mkSite 0x2407c 245%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x24074 408%positive 0x10331).
(* [comment removed for export] *)
Definition vlcs_24080 : csite := mkSite 0x24080 245%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x24078 436%positive 0x10664).
(* [comment removed for export] *)
Definition vlcs_24088 : csite := mkSite 0x24088 245%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1010%positive 0x13660).
(* [comment removed for export] *)
Definition vlcs_24090 : csite := mkSite 0x24090 245%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_24094 : csite := mkSite 0x24094 245%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 11 11 imm)) (SK_lo12 0x24090 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_240a8 : csite := mkSite 0x240a8 245%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_240ac : csite := mkSite 0x240ac 245%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_240b0 : csite := mkSite 0x240b0 245%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x240a8 451%positive 0x10814).
(* [comment removed for export] *)
Definition vlcs_240b4 : csite := mkSite 0x240b4 245%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x240ac 436%positive 0x10664).
(* [comment removed for export] *)
Definition vlcs_240bc : csite := mkSite 0x240bc 245%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1010%positive 0x13660).
(* [comment removed for export] *)
Definition vlcs_240e8 : csite := mkSite 0x240e8 246%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_240ec : csite := mkSite 0x240ec 246%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x240e8 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_240fc : csite := mkSite 0x240fc 246%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_24100 : csite := mkSite 0x24100 246%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_24104 : csite := mkSite 0x24104 246%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x240fc 408%positive 0x10331).
(* [comment removed for export] *)
Definition vlcs_24108 : csite := mkSite 0x24108 246%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x24100 402%positive 0x102b6).
(* [comment removed for export] *)
Definition vlcs_24110 : csite := mkSite 0x24110 246%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1010%positive 0x13660).
(* [comment removed for export] *)
Definition vlcs_24114 : csite := mkSite 0x24114 246%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_24118 : csite := mkSite 0x24118 246%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x24114 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_24128 : csite := mkSite 0x24128 246%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_2412c : csite := mkSite 0x2412c 246%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_24130 : csite := mkSite 0x24130 246%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x24128 445%positive 0x10790).
(* [comment removed for export] *)
Definition vlcs_24134 : csite := mkSite 0x24134 246%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x2412c 402%positive 0x102b6).
(* [comment removed for export] *)
Definition vlcs_2413c : csite := mkSite 0x2413c 246%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1010%positive 0x13660).
(* [comment removed for export] *)
Definition vlcs_24160 : csite := mkSite 0x24160 233%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_24164 : csite := mkSite 0x24164 233%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x24160 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_24174 : csite := mkSite 0x24174 233%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_24178 : csite := mkSite 0x24178 233%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_2417c : csite := mkSite 0x2417c 233%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x24174 408%positive 0x10331).
(* [comment removed for export] *)
Definition vlcs_24180 : csite := mkSite 0x24180 233%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x24178 447%positive 0x107af).
(* [comment removed for export] *)
Definition vlcs_24188 : csite := mkSite 0x24188 233%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1010%positive 0x13660).
(* [comment removed for export] *)
Definition vlcs_241ac : csite := mkSite 0x241ac 234%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_241b0 : csite := mkSite 0x241b0 234%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x241ac 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_241c0 : csite := mkSite 0x241c0 234%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_241c4 : csite := mkSite 0x241c4 234%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_241c8 : csite := mkSite 0x241c8 234%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x241c0 408%positive 0x10331).
(* [comment removed for export] *)
Definition vlcs_241cc : csite := mkSite 0x241cc 234%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x241c4 401%positive 0x102aa).
(* [comment removed for export] *)
Definition vlcs_241d4 : csite := mkSite 0x241d4 234%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1010%positive 0x13660).
(* [comment removed for export] *)
Definition vlcs_241f8 : csite := mkSite 0x241f8 247%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_241fc : csite := mkSite 0x241fc 247%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x241f8 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_2420c : csite := mkSite 0x2420c 247%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_24210 : csite := mkSite 0x24210 247%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_24214 : csite := mkSite 0x24214 247%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x2420c 408%positive 0x10331).
(* [comment removed for export] *)
Definition vlcs_24218 : csite := mkSite 0x24218 247%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x24210 409%positive 0x10341).
(* [comment removed for export] *)
Definition vlcs_24220 : csite := mkSite 0x24220 247%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1012%positive 0x13730).
(* [comment removed for export] *)
Definition vlcs_24244 : csite := mkSite 0x24244 235%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_24248 : csite := mkSite 0x24248 235%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x24244 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_24258 : csite := mkSite 0x24258 235%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_2425c : csite := mkSite 0x2425c 235%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_24260 : csite := mkSite 0x24260 235%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x24258 408%positive 0x10331).
(* [comment removed for export] *)
Definition vlcs_24264 : csite := mkSite 0x24264 235%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x2425c 459%positive 0x10911).
(* [comment removed for export] *)
Definition vlcs_2426c : csite := mkSite 0x2426c 235%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1010%positive 0x13660).
(* [comment removed for export] *)
Definition vlcs_242f8 : csite := mkSite 0x242f8 236%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 231%positive 0x23e10).
(* [comment removed for export] *)
Definition vlcs_24310 : csite := mkSite 0x24310 236%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_24314 : csite := mkSite 0x24314 236%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x24310 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_24328 : csite := mkSite 0x24328 236%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_2432c : csite := mkSite 0x2432c 236%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_24330 : csite := mkSite 0x24330 236%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x24328 429%positive 0x10591).
(* [comment removed for export] *)
Definition vlcs_24334 : csite := mkSite 0x24334 236%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x2432c 439%positive 0x10693).
(* [comment removed for export] *)
Definition vlcs_24338 : csite := mkSite 0x24338 236%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1011%positive 0x13694).
(* [comment removed for export] *)
Definition vlcs_24340 : csite := mkSite 0x24340 236%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_24344 : csite := mkSite 0x24344 236%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x24340 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_24354 : csite := mkSite 0x24354 236%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_24358 : csite := mkSite 0x24358 236%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_2435c : csite := mkSite 0x2435c 236%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x24354 408%positive 0x10331).
(* [comment removed for export] *)
Definition vlcs_24360 : csite := mkSite 0x24360 236%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x24358 439%positive 0x10693).
(* [comment removed for export] *)
Definition vlcs_2437c : csite := mkSite 0x2437c 236%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1010%positive 0x13660).
(* [comment removed for export] *)
Definition vlcs_2438c : csite := mkSite 0x2438c 236%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 247%positive 0x241e4).
(* [comment removed for export] *)
Definition vlcs_24398 : csite := mkSite 0x24398 236%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 242%positive 0x23ce4).
(* [comment removed for export] *)
Definition vlcs_243d0 : csite := mkSite 0x243d0 236%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_243d4 : csite := mkSite 0x243d4 236%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 14 11 imm)) (SK_lo12 0x243d0 5018%positive 0x10a80).
(* [comment removed for export] *)
Definition vlcs_24544 : csite := mkSite 0x24544 237%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 234%positive 0x24198).
(* [comment removed for export] *)
Definition vlcs_24554 : csite := mkSite 0x24554 237%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_24558 : csite := mkSite 0x24558 237%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x24554 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_24568 : csite := mkSite 0x24568 237%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_2456c : csite := mkSite 0x2456c 237%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_24570 : csite := mkSite 0x24570 237%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x24568 427%positive 0x10563).
(* [comment removed for export] *)
Definition vlcs_24574 : csite := mkSite 0x24574 237%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x2456c 415%positive 0x103e0).
(* [comment removed for export] *)
Definition vlcs_24580 : csite := mkSite 0x24580 237%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_24584 : csite := mkSite 0x24584 237%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x24580 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_24594 : csite := mkSite 0x24594 237%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_24598 : csite := mkSite 0x24598 237%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_2459c : csite := mkSite 0x2459c 237%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x24594 424%positive 0x104ec).
(* [comment removed for export] *)
Definition vlcs_245a0 : csite := mkSite 0x245a0 237%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x24598 415%positive 0x103e0).
(* [comment removed for export] *)
Definition vlcs_245a8 : csite := mkSite 0x245a8 237%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_245ac : csite := mkSite 0x245ac 237%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x245a8 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_245bc : csite := mkSite 0x245bc 237%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_245c0 : csite := mkSite 0x245c0 237%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_245c4 : csite := mkSite 0x245c4 237%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x245bc 403%positive 0x102c2).
(* [comment removed for export] *)
Definition vlcs_245c8 : csite := mkSite 0x245c8 237%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x245c0 415%positive 0x103e0).
(* [comment removed for export] *)
Definition vlcs_245d0 : csite := mkSite 0x245d0 237%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_245d4 : csite := mkSite 0x245d4 237%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x245d0 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_245e4 : csite := mkSite 0x245e4 237%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_245e8 : csite := mkSite 0x245e8 237%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_245ec : csite := mkSite 0x245ec 237%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x245e4 455%positive 0x10870).
(* [comment removed for export] *)
Definition vlcs_245f0 : csite := mkSite 0x245f0 237%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x245e8 415%positive 0x103e0).
(* [comment removed for export] *)
Definition vlcs_24610 : csite := mkSite 0x24610 237%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1010%positive 0x13660).
(* [comment removed for export] *)
Definition vlcs_24634 : csite := mkSite 0x24634 237%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_24638 : csite := mkSite 0x24638 237%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 11 11 imm)) (SK_lo12 0x24634 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_24648 : csite := mkSite 0x24648 237%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_2464c : csite := mkSite 0x2464c 237%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_24650 : csite := mkSite 0x24650 237%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x24648 456%positive 0x10887).
(* [comment removed for export] *)
Definition vlcs_24654 : csite := mkSite 0x24654 237%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x2464c 415%positive 0x103e0).
(* [comment removed for export] *)
Definition vlcs_24664 : csite := mkSite 0x24664 237%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_24668 : csite := mkSite 0x24668 237%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 11 11 imm)) (SK_lo12 0x24664 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_24678 : csite := mkSite 0x24678 237%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_2467c : csite := mkSite 0x2467c 237%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_24680 : csite := mkSite 0x24680 237%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x24678 434%positive 0x10603).
(* [comment removed for export] *)
Definition vlcs_24684 : csite := mkSite 0x24684 237%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x2467c 415%positive 0x103e0).
(* [comment removed for export] *)
Definition vlcs_2468c : csite := mkSite 0x2468c 237%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1011%positive 0x13694).
(* [comment removed for export] *)
Definition vlcs_24698 : csite := mkSite 0x24698 237%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_2469c : csite := mkSite 0x2469c 237%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x24698 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_246b0 : csite := mkSite 0x246b0 237%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_246b4 : csite := mkSite 0x246b4 237%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_246b8 : csite := mkSite 0x246b8 237%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x246b0 406%positive 0x102fd).
(* [comment removed for export] *)
Definition vlcs_246bc : csite := mkSite 0x246bc 237%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x246b4 415%positive 0x103e0).
(* [comment removed for export] *)
Definition vlcs_246c4 : csite := mkSite 0x246c4 237%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1011%positive 0x13694).
(* [comment removed for export] *)
Definition vlcs_246e0 : csite := mkSite 0x246e0 237%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_246e4 : csite := mkSite 0x246e4 237%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 11 11 imm)) (SK_lo12 0x246e0 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_246f4 : csite := mkSite 0x246f4 237%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_246f8 : csite := mkSite 0x246f8 237%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_246fc : csite := mkSite 0x246fc 237%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x246f4 435%positive 0x10631).
(* [comment removed for export] *)
Definition vlcs_24700 : csite := mkSite 0x24700 237%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x246f8 415%positive 0x103e0).
(* [comment removed for export] *)
Definition vlcs_24718 : csite := mkSite 0x24718 237%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_2471c : csite := mkSite 0x2471c 237%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x24718 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_24730 : csite := mkSite 0x24730 237%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_24734 : csite := mkSite 0x24734 237%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_24738 : csite := mkSite 0x24738 237%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x24730 448%positive 0x107bc).
(* [comment removed for export] *)
Definition vlcs_2473c : csite := mkSite 0x2473c 237%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x24734 415%positive 0x103e0).
(* [comment removed for export] *)
Definition vlcs_24744 : csite := mkSite 0x24744 237%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_24748 : csite := mkSite 0x24748 237%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x24744 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_2475c : csite := mkSite 0x2475c 237%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_24760 : csite := mkSite 0x24760 237%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_24764 : csite := mkSite 0x24764 237%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x2475c 412%positive 0x1038b).
(* [comment removed for export] *)
Definition vlcs_24768 : csite := mkSite 0x24768 237%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x24760 415%positive 0x103e0).
(* [comment removed for export] *)
Definition vlcs_2476c : csite := mkSite 0x2476c 237%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1011%positive 0x13694).
(* [comment removed for export] *)
Definition vlcs_24780 : csite := mkSite 0x24780 237%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 249%positive 0x24b70).
(* [comment removed for export] *)
Definition vlcs_247a4 : csite := mkSite 0x247a4 237%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_247a8 : csite := mkSite 0x247a8 237%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x247a4 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_247bc : csite := mkSite 0x247bc 237%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_247c0 : csite := mkSite 0x247c0 237%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_247c4 : csite := mkSite 0x247c4 237%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x247bc 440%positive 0x106a1).
(* [comment removed for export] *)
Definition vlcs_247c8 : csite := mkSite 0x247c8 237%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x247c0 415%positive 0x103e0).
(* [comment removed for export] *)
Definition vlcs_24808 : csite := mkSite 0x24808 248%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1035%positive 0x15b38).
(* [comment removed for export] *)
Definition vlcs_24810 : csite := mkSite 0x24810 248%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1035%positive 0x15b38).
(* [comment removed for export] *)
Definition vlcs_2481c : csite := mkSite 0x2481c 248%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_24820 : csite := mkSite 0x24820 248%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x2481c 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_24830 : csite := mkSite 0x24830 248%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_24834 : csite := mkSite 0x24834 248%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_24838 : csite := mkSite 0x24838 248%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x24830 466%positive 0x109d5).
(* [comment removed for export] *)
Definition vlcs_2483c : csite := mkSite 0x2483c 248%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x24834 414%positive 0x103d1).
(* [comment removed for export] *)
Definition vlcs_24850 : csite := mkSite 0x24850 248%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1011%positive 0x13694).
(* [comment removed for export] *)
Definition vlcs_248b4 : csite := mkSite 0x248b4 238%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_248b8 : csite := mkSite 0x248b8 238%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x248b4 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_248c8 : csite := mkSite 0x248c8 238%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_248cc : csite := mkSite 0x248cc 238%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x248c8 418%positive 0x10442).
(* [comment removed for export] *)
Definition vlcs_248d4 : csite := mkSite 0x248d4 238%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_248d8 : csite := mkSite 0x248d8 238%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x248d4 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_248e8 : csite := mkSite 0x248e8 238%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_248ec : csite := mkSite 0x248ec 238%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x248e8 449%positive 0x107f6).
(* [comment removed for export] *)
Definition vlcs_24904 : csite := mkSite 0x24904 238%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_24908 : csite := mkSite 0x24908 238%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x24904 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_24918 : csite := mkSite 0x24918 238%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_2491c : csite := mkSite 0x2491c 238%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x24918 431%positive 0x105b7).
(* [comment removed for export] *)
Definition vlcs_24924 : csite := mkSite 0x24924 238%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_24928 : csite := mkSite 0x24928 238%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x24924 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_24938 : csite := mkSite 0x24938 238%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_2493c : csite := mkSite 0x2493c 238%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x24938 430%positive 0x105ac).
(* [comment removed for export] *)
Definition vlcs_24940 : csite := mkSite 0x24940 238%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_24944 : csite := mkSite 0x24944 238%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x24940 461%positive 0x10933).
(* [comment removed for export] *)
Definition vlcs_2497c : csite := mkSite 0x2497c 238%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1012%positive 0x13730).
(* [comment removed for export] *)
Definition vlcs_249e8 : csite := mkSite 0x249e8 238%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1034%positive 0x15a00).
(* [comment removed for export] *)
Definition vlcs_24a14 : csite := mkSite 0x24a14 238%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1034%positive 0x15a00).
(* [comment removed for export] *)
Definition vlcs_24a24 : csite := mkSite 0x24a24 238%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_24a2c : csite := mkSite 0x24a2c 238%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 25 10 imm)) (SK_lo12 0x24a24 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_24a30 : csite := mkSite 0x24a30 238%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_24a34 : csite := mkSite 0x24a34 238%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 20 10 imm)) (SK_lo12 0x24a30 460%positive 0x1091d).
(* [comment removed for export] *)
Definition vlcs_24a38 : csite := mkSite 0x24a38 238%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_24a3c : csite := mkSite 0x24a3c 238%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 21 10 imm)) (SK_lo12 0x24a38 404%positive 0x102d3).
(* [comment removed for export] *)
Definition vlcs_24b64 : csite := mkSite 0x24b64 238%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1010%positive 0x13660).
(* [comment removed for export] *)
Definition vlcs_24bc0 : csite := mkSite 0x24bc0 249%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 231%positive 0x23e10).
(* [comment removed for export] *)
Definition vlcs_24be4 : csite := mkSite 0x24be4 249%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 242%positive 0x23ce4).
(* [comment removed for export] *)
Definition vlcs_24bf0 : csite := mkSite 0x24bf0 249%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 247%positive 0x241e4).
(* [comment removed for export] *)
Definition vlcs_24c10 : csite := mkSite 0x24c10 249%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 250%positive 0x24ed4).
(* [comment removed for export] *)
Definition vlcs_24c28 : csite := mkSite 0x24c28 249%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_24c2c : csite := mkSite 0x24c2c 249%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x24c28 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_24c3c : csite := mkSite 0x24c3c 249%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_24c40 : csite := mkSite 0x24c40 249%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_24c44 : csite := mkSite 0x24c44 249%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x24c3c 469%positive 0x10a52).
(* [comment removed for export] *)
Definition vlcs_24c48 : csite := mkSite 0x24c48 249%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x24c40 470%positive 0x10a68).
(* [comment removed for export] *)
Definition vlcs_24c50 : csite := mkSite 0x24c50 249%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_24c54 : csite := mkSite 0x24c54 249%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x24c50 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_24c64 : csite := mkSite 0x24c64 249%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_24c68 : csite := mkSite 0x24c68 249%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_24c6c : csite := mkSite 0x24c6c 249%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x24c64 405%positive 0x102e2).
(* [comment removed for export] *)
Definition vlcs_24c70 : csite := mkSite 0x24c70 249%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x24c68 470%positive 0x10a68).
(* [comment removed for export] *)
Definition vlcs_24c9c : csite := mkSite 0x24c9c 249%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1010%positive 0x13660).
(* [comment removed for export] *)
Definition vlcs_24e60 : csite := mkSite 0x24e60 249%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_24e64 : csite := mkSite 0x24e64 249%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x24e60 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_24e74 : csite := mkSite 0x24e74 249%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_24e78 : csite := mkSite 0x24e78 249%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_24e7c : csite := mkSite 0x24e7c 249%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x24e74 432%positive 0x105c5).
(* [comment removed for export] *)
Definition vlcs_24e80 : csite := mkSite 0x24e80 249%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x24e78 470%positive 0x10a68).
(* [comment removed for export] *)
Definition vlcs_24e88 : csite := mkSite 0x24e88 249%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1010%positive 0x13660).
(* [comment removed for export] *)
Definition vlcs_24f14 : csite := mkSite 0x24f14 250%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 235%positive 0x24230).
(* [comment removed for export] *)
Definition vlcs_24f20 : csite := mkSite 0x24f20 250%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 234%positive 0x24198).
(* [comment removed for export] *)
Definition vlcs_24f34 : csite := mkSite 0x24f34 250%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 233%positive 0x2414c).
(* [comment removed for export] *)
Definition vlcs_24f40 : csite := mkSite 0x24f40 250%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 242%positive 0x23ce4).
(* [comment removed for export] *)
Definition vlcs_24f4c : csite := mkSite 0x24f4c 250%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 247%positive 0x241e4).
(* [comment removed for export] *)
Definition vlcs_25020 : csite := mkSite 0x25020 250%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_25024 : csite := mkSite 0x25024 250%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x25020 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_25034 : csite := mkSite 0x25034 250%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_25038 : csite := mkSite 0x25038 250%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_2503c : csite := mkSite 0x2503c 250%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x25034 438%positive 0x10680).
(* [comment removed for export] *)
Definition vlcs_25040 : csite := mkSite 0x25040 250%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x25038 467%positive 0x10a28).
(* [comment removed for export] *)
Definition vlcs_25048 : csite := mkSite 0x25048 250%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_2504c : csite := mkSite 0x2504c 250%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 11 11 imm)) (SK_lo12 0x25048 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_2505c : csite := mkSite 0x2505c 250%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_25060 : csite := mkSite 0x25060 250%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_25064 : csite := mkSite 0x25064 250%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x2505c 408%positive 0x10331).
(* [comment removed for export] *)
Definition vlcs_25068 : csite := mkSite 0x25068 250%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x25060 467%positive 0x10a28).
(* [comment removed for export] *)
Definition vlcs_2508c : csite := mkSite 0x2508c 250%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1010%positive 0x13660).
(* [comment removed for export] *)
Definition vlcs_25170 : csite := mkSite 0x25170 239%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_25174 : csite := mkSite 0x25174 239%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x25170 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_25184 : csite := mkSite 0x25184 239%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_25188 : csite := mkSite 0x25188 239%positive OP_AUIPC (SH20 (fun imm => Auipc 12 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_2518c : csite := mkSite 0x2518c 239%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x25184 442%positive 0x10726).
(* [comment removed for export] *)
Definition vlcs_25190 : csite := mkSite 0x25190 239%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 13 12 imm)) (SK_lo12 0x25188 433%positive 0x105ea).
(* [comment removed for export] *)
Definition vlcs_2519c : csite := mkSite 0x2519c 239%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1011%positive 0x13694).
(* [comment removed for export] *)
Definition vlcs_251a4 : csite := mkSite 0x251a4 239%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_251a8 : csite := mkSite 0x251a8 239%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x251a4 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_251b8 : csite := mkSite 0x251b8 239%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_251bc : csite := mkSite 0x251bc 239%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_251c0 : csite := mkSite 0x251c0 239%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x251b8 449%positive 0x107f6).
(* [comment removed for export] *)
Definition vlcs_251c4 : csite := mkSite 0x251c4 239%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x251bc 433%positive 0x105ea).
(* [comment removed for export] *)
Definition vlcs_25278 : csite := mkSite 0x25278 239%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_2527c : csite := mkSite 0x2527c 239%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x25278 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_2528c : csite := mkSite 0x2528c 239%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_25290 : csite := mkSite 0x25290 239%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_25294 : csite := mkSite 0x25294 239%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x2528c 463%positive 0x1097f).
(* [comment removed for export] *)
Definition vlcs_25298 : csite := mkSite 0x25298 239%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x25290 433%positive 0x105ea).
(* [comment removed for export] *)
Definition vlcs_252a0 : csite := mkSite 0x252a0 239%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_252a4 : csite := mkSite 0x252a4 239%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x252a0 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_252b4 : csite := mkSite 0x252b4 239%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_252b8 : csite := mkSite 0x252b8 239%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_252bc : csite := mkSite 0x252bc 239%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x252b4 443%positive 0x10749).
(* [comment removed for export] *)
Definition vlcs_252c0 : csite := mkSite 0x252c0 239%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x252b8 433%positive 0x105ea).
(* [comment removed for export] *)
Definition vlcs_252f0 : csite := mkSite 0x252f0 239%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1012%positive 0x13730).
(* [comment removed for export] *)
Definition vlcs_25300 : csite := mkSite 0x25300 239%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_25304 : csite := mkSite 0x25304 239%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x25300 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_25314 : csite := mkSite 0x25314 239%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_25318 : csite := mkSite 0x25318 239%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_2531c : csite := mkSite 0x2531c 239%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x25314 410%positive 0x1034c).
(* [comment removed for export] *)
Definition vlcs_25320 : csite := mkSite 0x25320 239%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x25318 433%positive 0x105ea).
(* [comment removed for export] *)
Definition vlcs_25338 : csite := mkSite 0x25338 239%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_2533c : csite := mkSite 0x2533c 239%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x25338 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_2534c : csite := mkSite 0x2534c 239%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_25350 : csite := mkSite 0x25350 239%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_25354 : csite := mkSite 0x25354 239%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x2534c 407%positive 0x10322).
(* [comment removed for export] *)
Definition vlcs_25358 : csite := mkSite 0x25358 239%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x25350 433%positive 0x105ea).
(* [comment removed for export] *)
Definition vlcs_25390 : csite := mkSite 0x25390 239%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 241%positive 0x239c0).
(* [comment removed for export] *)
Definition vlcs_253a0 : csite := mkSite 0x253a0 239%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 242%positive 0x23ce4).
(* [comment removed for export] *)
Definition vlcs_253e4 : csite := mkSite 0x253e4 239%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 243%positive 0x23d30).
(* [comment removed for export] *)
Definition vlcs_253fc : csite := mkSite 0x253fc 239%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 230%positive 0x237d4).
(* [comment removed for export] *)
Definition vlcs_25424 : csite := mkSite 0x25424 239%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 238%positive 0x2486c).
(* [comment removed for export] *)
Definition vlcs_25438 : csite := mkSite 0x25438 239%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 232%positive 0x23ecc).
(* [comment removed for export] *)
Definition vlcs_25444 : csite := mkSite 0x25444 239%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 243%positive 0x23d30).
(* [comment removed for export] *)
Definition vlcs_25448 : csite := mkSite 0x25448 239%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_2544c : csite := mkSite 0x2544c 239%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x25448 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_2545c : csite := mkSite 0x2545c 239%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_25460 : csite := mkSite 0x25460 239%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_25464 : csite := mkSite 0x25464 239%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x2545c 457%positive 0x108b6).
(* [comment removed for export] *)
Definition vlcs_25468 : csite := mkSite 0x25468 239%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x25460 433%positive 0x105ea).
(* [comment removed for export] *)
Definition vlcs_25470 : csite := mkSite 0x25470 239%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_25474 : csite := mkSite 0x25474 239%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x25470 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_25484 : csite := mkSite 0x25484 239%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_25488 : csite := mkSite 0x25488 239%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_2548c : csite := mkSite 0x2548c 239%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x25484 446%positive 0x1079f).
(* [comment removed for export] *)
Definition vlcs_25490 : csite := mkSite 0x25490 239%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x25488 433%positive 0x105ea).
(* [comment removed for export] *)
Definition vlcs_25498 : csite := mkSite 0x25498 239%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_2549c : csite := mkSite 0x2549c 239%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x25498 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_254ac : csite := mkSite 0x254ac 239%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_254b0 : csite := mkSite 0x254b0 239%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_254b4 : csite := mkSite 0x254b4 239%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x254ac 421%positive 0x10488).
(* [comment removed for export] *)
Definition vlcs_254b8 : csite := mkSite 0x254b8 239%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x254b0 433%positive 0x105ea).
(* [comment removed for export] *)
Definition vlcs_254c0 : csite := mkSite 0x254c0 239%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_254c4 : csite := mkSite 0x254c4 239%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x254c0 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_254d4 : csite := mkSite 0x254d4 239%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_254d8 : csite := mkSite 0x254d8 239%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_254dc : csite := mkSite 0x254dc 239%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x254d4 425%positive 0x104ff).
(* [comment removed for export] *)
Definition vlcs_254e0 : csite := mkSite 0x254e0 239%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x254d8 433%positive 0x105ea).
(* [comment removed for export] *)
Definition vlcs_254f0 : csite := mkSite 0x254f0 239%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1011%positive 0x13694).
(* [comment removed for export] *)
Definition vlcs_254f8 : csite := mkSite 0x254f8 239%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_254fc : csite := mkSite 0x254fc 239%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x254f8 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_2550c : csite := mkSite 0x2550c 239%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_25510 : csite := mkSite 0x25510 239%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_25514 : csite := mkSite 0x25514 239%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x2550c 450%positive 0x10807).
(* [comment removed for export] *)
Definition vlcs_25518 : csite := mkSite 0x25518 239%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x25510 433%positive 0x105ea).
(* [comment removed for export] *)
Definition vlcs_2552c : csite := mkSite 0x2552c 239%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 243%positive 0x23d30).
(* [comment removed for export] *)
Definition vlcs_25530 : csite := mkSite 0x25530 239%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_25534 : csite := mkSite 0x25534 239%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x25530 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_25544 : csite := mkSite 0x25544 239%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_25548 : csite := mkSite 0x25548 239%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_2554c : csite := mkSite 0x2554c 239%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x25544 471%positive 0x10a7c).
(* [comment removed for export] *)
Definition vlcs_25550 : csite := mkSite 0x25550 239%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x25548 433%positive 0x105ea).
(* [comment removed for export] *)
Definition vlcs_2555c : csite := mkSite 0x2555c 239%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 247%positive 0x241e4).
(* [comment removed for export] *)
Definition vlcs_2558c : csite := mkSite 0x2558c 239%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1090%positive 0x1c9b4).
(* [comment removed for export] *)
Definition vlcs_255a0 : csite := mkSite 0x255a0 239%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 237%positive 0x244bc).
(* [comment removed for export] *)
Definition vlcs_255b8 : csite := mkSite 0x255b8 239%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 243%positive 0x23d30).
(* [comment removed for export] *)
Definition vlcs_255bc : csite := mkSite 0x255bc 239%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_255c0 : csite := mkSite 0x255c0 239%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x255bc 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition vlcs_255d0 : csite := mkSite 0x255d0 239%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_255d4 : csite := mkSite 0x255d4 239%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition vlcs_255d8 : csite := mkSite 0x255d8 239%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x255d0 416%positive 0x103ef).
(* [comment removed for export] *)
Definition vlcs_255dc : csite := mkSite 0x255dc 239%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x255d4 433%positive 0x105ea).
(* [comment removed for export] *)
Definition vlcs_255e4 : csite := mkSite 0x255e4 239%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1012%positive 0x13730).

Definition canon_sites_VL : list csite := [
  vlcs_237e0; vlcs_2381c; vlcs_23828; vlcs_2382c; vlcs_2383c; vlcs_23840; vlcs_23844; vlcs_23848;
  vlcs_2385c; vlcs_2388c; vlcs_238b8; vlcs_238bc; vlcs_238d8; vlcs_238e0; vlcs_238e4; vlcs_238f4;
  vlcs_238f8; vlcs_238fc; vlcs_23900; vlcs_23918; vlcs_23948; vlcs_2395c; vlcs_23968; vlcs_2396c;
  vlcs_23970; vlcs_23980; vlcs_23984; vlcs_23988; vlcs_2398c; vlcs_23994; vlcs_23a14; vlcs_23a18;
  vlcs_23a28; vlcs_23a2c; vlcs_23a30; vlcs_23a34; vlcs_23a50; vlcs_23a5c; vlcs_23a60; vlcs_23a64;
  vlcs_23a68; vlcs_23a70; vlcs_23a74; vlcs_23a84; vlcs_23a88; vlcs_23a8c; vlcs_23a90; vlcs_23a98;
  vlcs_23a9c; vlcs_23aac; vlcs_23ab0; vlcs_23ab4; vlcs_23ab8; vlcs_23ad8; vlcs_23adc; vlcs_23aec;
  vlcs_23af0; vlcs_23af4; vlcs_23af8; vlcs_23b14; vlcs_23b20; vlcs_23b24; vlcs_23b28; vlcs_23b2c;
  vlcs_23b34; vlcs_23b38; vlcs_23b48; vlcs_23b4c; vlcs_23b50; vlcs_23b54; vlcs_23b78; vlcs_23b88;
  vlcs_23b8c; vlcs_23b9c; vlcs_23ba0; vlcs_23ba4; vlcs_23ba8; vlcs_23bbc; vlcs_23bc0; vlcs_23bd0;
  vlcs_23bd4; vlcs_23bd8; vlcs_23bdc; vlcs_23be8; vlcs_23bec; vlcs_23bfc; vlcs_23c00; vlcs_23c04;
  vlcs_23c08; vlcs_23c0c; vlcs_23c48; vlcs_23c58; vlcs_23c64; vlcs_23c70; vlcs_23c9c; vlcs_23ca0;
  vlcs_23cb0; vlcs_23cb4; vlcs_23cb8; vlcs_23cbc; vlcs_23cf8; vlcs_23cfc; vlcs_23d0c; vlcs_23d10;
  vlcs_23d14; vlcs_23d18; vlcs_23d20; vlcs_23d7c; vlcs_23d80; vlcs_23d90; vlcs_23da4; vlcs_23db0;
  vlcs_23dc0; vlcs_23dc4; vlcs_23dd4; vlcs_23dd8; vlcs_23ddc; vlcs_23de0; vlcs_23df4; vlcs_23e8c;
  vlcs_23e90; vlcs_23ea0; vlcs_23ea4; vlcs_23ea8; vlcs_23eac; vlcs_23eb4; vlcs_23f04; vlcs_23f20;
  vlcs_23f34; vlcs_23f38; vlcs_23f48; vlcs_23f4c; vlcs_23f50; vlcs_23f54; vlcs_23f6c; vlcs_23f70;
  vlcs_23f74; vlcs_23f84; vlcs_23f88; vlcs_23f8c; vlcs_23f90; vlcs_23f98; vlcs_23fd8; vlcs_23fdc;
  vlcs_23fec; vlcs_23ff0; vlcs_23ff4; vlcs_23ff8; vlcs_24000; vlcs_24008; vlcs_2400c; vlcs_24020;
  vlcs_24024; vlcs_24028; vlcs_2402c; vlcs_24034; vlcs_24060; vlcs_24064; vlcs_24074; vlcs_24078;
  vlcs_2407c; vlcs_24080; vlcs_24088; vlcs_24090; vlcs_24094; vlcs_240a8; vlcs_240ac; vlcs_240b0;
  vlcs_240b4; vlcs_240bc; vlcs_240e8; vlcs_240ec; vlcs_240fc; vlcs_24100; vlcs_24104; vlcs_24108;
  vlcs_24110; vlcs_24114; vlcs_24118; vlcs_24128; vlcs_2412c; vlcs_24130; vlcs_24134; vlcs_2413c;
  vlcs_24160; vlcs_24164; vlcs_24174; vlcs_24178; vlcs_2417c; vlcs_24180; vlcs_24188; vlcs_241ac;
  vlcs_241b0; vlcs_241c0; vlcs_241c4; vlcs_241c8; vlcs_241cc; vlcs_241d4; vlcs_241f8; vlcs_241fc;
  vlcs_2420c; vlcs_24210; vlcs_24214; vlcs_24218; vlcs_24220; vlcs_24244; vlcs_24248; vlcs_24258;
  vlcs_2425c; vlcs_24260; vlcs_24264; vlcs_2426c; vlcs_242f8; vlcs_24310; vlcs_24314; vlcs_24328;
  vlcs_2432c; vlcs_24330; vlcs_24334; vlcs_24338; vlcs_24340; vlcs_24344; vlcs_24354; vlcs_24358;
  vlcs_2435c; vlcs_24360; vlcs_2437c; vlcs_2438c; vlcs_24398; vlcs_243d0; vlcs_243d4; vlcs_24544;
  vlcs_24554; vlcs_24558; vlcs_24568; vlcs_2456c; vlcs_24570; vlcs_24574; vlcs_24580; vlcs_24584;
  vlcs_24594; vlcs_24598; vlcs_2459c; vlcs_245a0; vlcs_245a8; vlcs_245ac; vlcs_245bc; vlcs_245c0;
  vlcs_245c4; vlcs_245c8; vlcs_245d0; vlcs_245d4; vlcs_245e4; vlcs_245e8; vlcs_245ec; vlcs_245f0;
  vlcs_24610; vlcs_24634; vlcs_24638; vlcs_24648; vlcs_2464c; vlcs_24650; vlcs_24654; vlcs_24664;
  vlcs_24668; vlcs_24678; vlcs_2467c; vlcs_24680; vlcs_24684; vlcs_2468c; vlcs_24698; vlcs_2469c;
  vlcs_246b0; vlcs_246b4; vlcs_246b8; vlcs_246bc; vlcs_246c4; vlcs_246e0; vlcs_246e4; vlcs_246f4;
  vlcs_246f8; vlcs_246fc; vlcs_24700; vlcs_24718; vlcs_2471c; vlcs_24730; vlcs_24734; vlcs_24738;
  vlcs_2473c; vlcs_24744; vlcs_24748; vlcs_2475c; vlcs_24760; vlcs_24764; vlcs_24768; vlcs_2476c;
  vlcs_24780; vlcs_247a4; vlcs_247a8; vlcs_247bc; vlcs_247c0; vlcs_247c4; vlcs_247c8; vlcs_24808;
  vlcs_24810; vlcs_2481c; vlcs_24820; vlcs_24830; vlcs_24834; vlcs_24838; vlcs_2483c; vlcs_24850;
  vlcs_248b4; vlcs_248b8; vlcs_248c8; vlcs_248cc; vlcs_248d4; vlcs_248d8; vlcs_248e8; vlcs_248ec;
  vlcs_24904; vlcs_24908; vlcs_24918; vlcs_2491c; vlcs_24924; vlcs_24928; vlcs_24938; vlcs_2493c;
  vlcs_24940; vlcs_24944; vlcs_2497c; vlcs_249e8; vlcs_24a14; vlcs_24a24; vlcs_24a2c; vlcs_24a30;
  vlcs_24a34; vlcs_24a38; vlcs_24a3c; vlcs_24b64; vlcs_24bc0; vlcs_24be4; vlcs_24bf0; vlcs_24c10;
  vlcs_24c28; vlcs_24c2c; vlcs_24c3c; vlcs_24c40; vlcs_24c44; vlcs_24c48; vlcs_24c50; vlcs_24c54;
  vlcs_24c64; vlcs_24c68; vlcs_24c6c; vlcs_24c70; vlcs_24c9c; vlcs_24e60; vlcs_24e64; vlcs_24e74;
  vlcs_24e78; vlcs_24e7c; vlcs_24e80; vlcs_24e88; vlcs_24f14; vlcs_24f20; vlcs_24f34; vlcs_24f40;
  vlcs_24f4c; vlcs_25020; vlcs_25024; vlcs_25034; vlcs_25038; vlcs_2503c; vlcs_25040; vlcs_25048;
  vlcs_2504c; vlcs_2505c; vlcs_25060; vlcs_25064; vlcs_25068; vlcs_2508c; vlcs_25170; vlcs_25174;
  vlcs_25184; vlcs_25188; vlcs_2518c; vlcs_25190; vlcs_2519c; vlcs_251a4; vlcs_251a8; vlcs_251b8;
  vlcs_251bc; vlcs_251c0; vlcs_251c4; vlcs_25278; vlcs_2527c; vlcs_2528c; vlcs_25290; vlcs_25294;
  vlcs_25298; vlcs_252a0; vlcs_252a4; vlcs_252b4; vlcs_252b8; vlcs_252bc; vlcs_252c0; vlcs_252f0;
  vlcs_25300; vlcs_25304; vlcs_25314; vlcs_25318; vlcs_2531c; vlcs_25320; vlcs_25338; vlcs_2533c;
  vlcs_2534c; vlcs_25350; vlcs_25354; vlcs_25358; vlcs_25390; vlcs_253a0; vlcs_253e4; vlcs_253fc;
  vlcs_25424; vlcs_25438; vlcs_25444; vlcs_25448; vlcs_2544c; vlcs_2545c; vlcs_25460; vlcs_25464;
  vlcs_25468; vlcs_25470; vlcs_25474; vlcs_25484; vlcs_25488; vlcs_2548c; vlcs_25490; vlcs_25498;
  vlcs_2549c; vlcs_254ac; vlcs_254b0; vlcs_254b4; vlcs_254b8; vlcs_254c0; vlcs_254c4; vlcs_254d4;
  vlcs_254d8; vlcs_254dc; vlcs_254e0; vlcs_254f0; vlcs_254f8; vlcs_254fc; vlcs_2550c; vlcs_25510;
  vlcs_25514; vlcs_25518; vlcs_2552c; vlcs_25530; vlcs_25534; vlcs_25544; vlcs_25548; vlcs_2554c;
  vlcs_25550; vlcs_2555c; vlcs_2558c; vlcs_255a0; vlcs_255b8; vlcs_255bc; vlcs_255c0; vlcs_255d0;
  vlcs_255d4; vlcs_255d8; vlcs_255dc; vlcs_255e4].

Class RelocSitesVL (RL : Reloc) := { rl_sites_vl_ok : sites_check canon_sites_VL = true }.

Section Facts.
Context {RL : Reloc} {RS : RelocSitesVL RL}.
Definition rl_site_F_VL := site_F canon_sites_VL rl_sites_vl_ok.
Definition rl_site_D_VL := site_D canon_sites_VL rl_sites_vl_ok.
Definition rl_site_V_VL := site_V canon_sites_VL rl_sites_vl_ok.
Definition rl_site_J_VL := site_J canon_sites_VL rl_sites_vl_ok.
End Facts.
