(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require Import PropExec.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Reloc Require Import Reloc RelocCode RelocSites.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

(* [comment removed for export] *)
Definition olcs_2372c : csite := mkSite 0x2372c 200%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 210%positive 0x237ac).
(* [comment removed for export] *)
Definition olcs_23754 : csite := mkSite 0x23754 200%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1091%positive 0x1cdb8).
(* [comment removed for export] *)
Definition olcs_23760 : csite := mkSite 0x23760 200%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23764 : csite := mkSite 0x23764 200%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x23760 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_23774 : csite := mkSite 0x23774 200%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23778 : csite := mkSite 0x23778 200%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_2377c : csite := mkSite 0x2377c 200%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x23774 312%positive 0x103b7).
(* [comment removed for export] *)
Definition olcs_23780 : csite := mkSite 0x23780 200%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x23778 321%positive 0x104c3).
(* [comment removed for export] *)
Definition olcs_23794 : csite := mkSite 0x23794 200%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1012%positive 0x13730).
(* [comment removed for export] *)
Definition olcs_237c4 : csite := mkSite 0x237c4 210%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 211%positive 0x238e8).
(* [comment removed for export] *)
Definition olcs_237d4 : csite := mkSite 0x237d4 210%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_237d8 : csite := mkSite 0x237d8 210%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 18 11 imm)) (SK_lo12 0x237d4 5028%positive 0x1f430).
(* [comment removed for export] *)
Definition olcs_237fc : csite := mkSite 0x237fc 210%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 206%positive 0x23f9c).
(* [comment removed for export] *)
Definition olcs_23804 : csite := mkSite 0x23804 210%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23808 : csite := mkSite 0x23808 210%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x23804 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_23818 : csite := mkSite 0x23818 210%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_2381c : csite := mkSite 0x2381c 210%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23820 : csite := mkSite 0x23820 210%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x23818 312%positive 0x103b7).
(* [comment removed for export] *)
Definition olcs_23824 : csite := mkSite 0x23824 210%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x2381c 318%positive 0x10460).
(* [comment removed for export] *)
Definition olcs_23840 : csite := mkSite 0x23840 210%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1012%positive 0x13730).
(* [comment removed for export] *)
Definition olcs_23870 : csite := mkSite 0x23870 210%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1035%positive 0x15b38).
(* [comment removed for export] *)
Definition olcs_23884 : csite := mkSite 0x23884 210%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 215%positive 0x24414).
(* [comment removed for export] *)
Definition olcs_23890 : csite := mkSite 0x23890 210%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1035%positive 0x15b38).
(* [comment removed for export] *)
Definition olcs_23894 : csite := mkSite 0x23894 210%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23898 : csite := mkSite 0x23898 210%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x23894 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_238a8 : csite := mkSite 0x238a8 210%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_238ac : csite := mkSite 0x238ac 210%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_238b0 : csite := mkSite 0x238b0 210%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x238a8 353%positive 0x108aa).
(* [comment removed for export] *)
Definition olcs_238b4 : csite := mkSite 0x238b4 210%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x238ac 318%positive 0x10460).
(* [comment removed for export] *)
Definition olcs_238bc : csite := mkSite 0x238bc 210%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1012%positive 0x13730).
(* [comment removed for export] *)
Definition olcs_2393c : csite := mkSite 0x2393c 211%positive OP_AUIPC (SH20 (fun imm => Auipc 13 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23940 : csite := mkSite 0x23940 211%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 8 13 imm)) (SK_lo12 0x2393c 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_23950 : csite := mkSite 0x23950 211%positive OP_AUIPC (SH20 (fun imm => Auipc 13 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23954 : csite := mkSite 0x23954 211%positive OP_AUIPC (SH20 (fun imm => Auipc 14 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23958 : csite := mkSite 0x23958 211%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 13 13 imm)) (SK_lo12 0x23950 357%positive 0x10906).
(* [comment removed for export] *)
Definition olcs_2395c : csite := mkSite 0x2395c 211%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 14 14 imm)) (SK_lo12 0x23954 324%positive 0x10534).
(* [comment removed for export] *)
Definition olcs_23978 : csite := mkSite 0x23978 211%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1011%positive 0x13694).
(* [comment removed for export] *)
Definition olcs_23984 : csite := mkSite 0x23984 211%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23988 : csite := mkSite 0x23988 211%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_2398c : csite := mkSite 0x2398c 211%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x23984 319%positive 0x10470).
(* [comment removed for export] *)
Definition olcs_23990 : csite := mkSite 0x23990 211%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x23988 324%positive 0x10534).
(* [comment removed for export] *)
Definition olcs_23998 : csite := mkSite 0x23998 211%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_2399c : csite := mkSite 0x2399c 211%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x23998 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_239ac : csite := mkSite 0x239ac 211%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_239b0 : csite := mkSite 0x239b0 211%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_239b4 : csite := mkSite 0x239b4 211%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x239ac 300%positive 0x10298).
(* [comment removed for export] *)
Definition olcs_239b8 : csite := mkSite 0x239b8 211%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x239b0 324%positive 0x10534).
(* [comment removed for export] *)
Definition olcs_239c0 : csite := mkSite 0x239c0 211%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_239c4 : csite := mkSite 0x239c4 211%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x239c0 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_239d4 : csite := mkSite 0x239d4 211%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_239d8 : csite := mkSite 0x239d8 211%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_239dc : csite := mkSite 0x239dc 211%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x239d4 338%positive 0x106e7).
(* [comment removed for export] *)
Definition olcs_239e0 : csite := mkSite 0x239e0 211%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x239d8 324%positive 0x10534).
(* [comment removed for export] *)
Definition olcs_23a00 : csite := mkSite 0x23a00 211%positive OP_AUIPC (SH20 (fun imm => Auipc 13 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23a04 : csite := mkSite 0x23a04 211%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 8 13 imm)) (SK_lo12 0x23a00 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_23a14 : csite := mkSite 0x23a14 211%positive OP_AUIPC (SH20 (fun imm => Auipc 13 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23a18 : csite := mkSite 0x23a18 211%positive OP_AUIPC (SH20 (fun imm => Auipc 14 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23a1c : csite := mkSite 0x23a1c 211%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 13 13 imm)) (SK_lo12 0x23a14 357%positive 0x10906).
(* [comment removed for export] *)
Definition olcs_23a20 : csite := mkSite 0x23a20 211%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 14 14 imm)) (SK_lo12 0x23a18 324%positive 0x10534).
(* [comment removed for export] *)
Definition olcs_23a3c : csite := mkSite 0x23a3c 211%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1011%positive 0x13694).
(* [comment removed for export] *)
Definition olcs_23a48 : csite := mkSite 0x23a48 211%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23a4c : csite := mkSite 0x23a4c 211%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23a50 : csite := mkSite 0x23a50 211%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x23a48 347%positive 0x107ee).
(* [comment removed for export] *)
Definition olcs_23a54 : csite := mkSite 0x23a54 211%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x23a4c 324%positive 0x10534).
(* [comment removed for export] *)
Definition olcs_23a5c : csite := mkSite 0x23a5c 211%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23a60 : csite := mkSite 0x23a60 211%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x23a5c 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_23a70 : csite := mkSite 0x23a70 211%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23a74 : csite := mkSite 0x23a74 211%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23a78 : csite := mkSite 0x23a78 211%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x23a70 316%positive 0x1040f).
(* [comment removed for export] *)
Definition olcs_23a7c : csite := mkSite 0x23a7c 211%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x23a74 324%positive 0x10534).
(* [comment removed for export] *)
Definition olcs_23aa0 : csite := mkSite 0x23aa0 211%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1012%positive 0x13730).
(* [comment removed for export] *)
Definition olcs_23ab0 : csite := mkSite 0x23ab0 211%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23ab4 : csite := mkSite 0x23ab4 211%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x23ab0 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_23ac4 : csite := mkSite 0x23ac4 211%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23ac8 : csite := mkSite 0x23ac8 211%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23acc : csite := mkSite 0x23acc 211%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x23ac4 310%positive 0x1034f).
(* [comment removed for export] *)
Definition olcs_23ad0 : csite := mkSite 0x23ad0 211%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x23ac8 324%positive 0x10534).
(* [comment removed for export] *)
Definition olcs_23ae4 : csite := mkSite 0x23ae4 211%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23ae8 : csite := mkSite 0x23ae8 211%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x23ae4 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_23af8 : csite := mkSite 0x23af8 211%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23afc : csite := mkSite 0x23afc 211%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23b00 : csite := mkSite 0x23b00 211%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x23af8 359%positive 0x10947).
(* [comment removed for export] *)
Definition olcs_23b04 : csite := mkSite 0x23b04 211%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x23afc 324%positive 0x10534).
(* [comment removed for export] *)
Definition olcs_23b10 : csite := mkSite 0x23b10 211%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23b14 : csite := mkSite 0x23b14 211%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x23b10 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_23b24 : csite := mkSite 0x23b24 211%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23b28 : csite := mkSite 0x23b28 211%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23b2c : csite := mkSite 0x23b2c 211%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x23b24 341%positive 0x1072f).
(* [comment removed for export] *)
Definition olcs_23b30 : csite := mkSite 0x23b30 211%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x23b28 324%positive 0x10534).
(* [comment removed for export] *)
Definition olcs_23b34 : csite := mkSite 0x23b34 211%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1011%positive 0x13694).
(* [comment removed for export] *)
Definition olcs_23b74 : csite := mkSite 0x23b74 211%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1034%positive 0x15a00).
(* [comment removed for export] *)
Definition olcs_23ba0 : csite := mkSite 0x23ba0 211%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23ba4 : csite := mkSite 0x23ba4 211%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x23ba0 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_23bb4 : csite := mkSite 0x23bb4 211%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23bb8 : csite := mkSite 0x23bb8 211%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23bbc : csite := mkSite 0x23bbc 211%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x23bb4 312%positive 0x103b7).
(* [comment removed for export] *)
Definition olcs_23bc0 : csite := mkSite 0x23bc0 211%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x23bb8 324%positive 0x10534).
(* [comment removed for export] *)
Definition olcs_23bf0 : csite := mkSite 0x23bf0 212%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23bf4 : csite := mkSite 0x23bf4 212%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x23bf0 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_23c04 : csite := mkSite 0x23c04 212%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23c08 : csite := mkSite 0x23c08 212%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23c0c : csite := mkSite 0x23c0c 212%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x23c04 307%positive 0x10325).
(* [comment removed for export] *)
Definition olcs_23c10 : csite := mkSite 0x23c10 212%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x23c08 348%positive 0x10806).
(* [comment removed for export] *)
Definition olcs_23c18 : csite := mkSite 0x23c18 212%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1010%positive 0x13660).
(* [comment removed for export] *)
Definition olcs_23c60 : csite := mkSite 0x23c60 213%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23c64 : csite := mkSite 0x23c64 213%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 11 11 imm)) (SK_lo12 0x23c60 5028%positive 0x1f438).
(* [comment removed for export] *)
Definition olcs_23c74 : csite := mkSite 0x23c74 213%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1035%positive 0x15b38).
(* [comment removed for export] *)
Definition olcs_23c88 : csite := mkSite 0x23c88 213%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 215%positive 0x24414).
(* [comment removed for export] *)
Definition olcs_23c94 : csite := mkSite 0x23c94 213%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1035%positive 0x15b38).
(* [comment removed for export] *)
Definition olcs_23ca4 : csite := mkSite 0x23ca4 213%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23ca8 : csite := mkSite 0x23ca8 213%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x23ca4 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_23cb8 : csite := mkSite 0x23cb8 213%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23cbc : csite := mkSite 0x23cbc 213%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23cc0 : csite := mkSite 0x23cc0 213%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x23cb8 360%positive 0x1097f).
(* [comment removed for export] *)
Definition olcs_23cc4 : csite := mkSite 0x23cc4 213%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x23cbc 326%positive 0x10567).
(* [comment removed for export] *)
Definition olcs_23cd8 : csite := mkSite 0x23cd8 213%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1011%positive 0x13694).
(* [comment removed for export] *)
Definition olcs_23d3c : csite := mkSite 0x23d3c 201%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23d40 : csite := mkSite 0x23d40 201%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x23d3c 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_23d50 : csite := mkSite 0x23d50 201%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23d54 : csite := mkSite 0x23d54 201%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23d58 : csite := mkSite 0x23d58 201%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x23d50 307%positive 0x10325).
(* [comment removed for export] *)
Definition olcs_23d5c : csite := mkSite 0x23d5c 201%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x23d54 362%positive 0x109eb).
(* [comment removed for export] *)
Definition olcs_23d64 : csite := mkSite 0x23d64 201%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1010%positive 0x13660).
(* [comment removed for export] *)
Definition olcs_23da0 : csite := mkSite 0x23da0 202%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 215%positive 0x24414).
(* [comment removed for export] *)
Definition olcs_23dbc : csite := mkSite 0x23dbc 202%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 207%positive 0x24118).
(* [comment removed for export] *)
Definition olcs_23dd0 : csite := mkSite 0x23dd0 202%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23dd4 : csite := mkSite 0x23dd4 202%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x23dd0 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_23de4 : csite := mkSite 0x23de4 202%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23de8 : csite := mkSite 0x23de8 202%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23dec : csite := mkSite 0x23dec 202%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x23de4 307%positive 0x10325).
(* [comment removed for export] *)
Definition olcs_23df0 : csite := mkSite 0x23df0 202%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x23de8 334%positive 0x10645).
(* [comment removed for export] *)
Definition olcs_23e08 : csite := mkSite 0x23e08 202%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1010%positive 0x13660).
(* [comment removed for export] *)
Definition olcs_23e0c : csite := mkSite 0x23e0c 202%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23e10 : csite := mkSite 0x23e10 202%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x23e0c 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_23e20 : csite := mkSite 0x23e20 202%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23e24 : csite := mkSite 0x23e24 202%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23e28 : csite := mkSite 0x23e28 202%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x23e20 349%positive 0x10810).
(* [comment removed for export] *)
Definition olcs_23e2c : csite := mkSite 0x23e2c 202%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x23e24 334%positive 0x10645).
(* [comment removed for export] *)
Definition olcs_23e34 : csite := mkSite 0x23e34 202%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1010%positive 0x13660).
(* [comment removed for export] *)
Definition olcs_23e60 : csite := mkSite 0x23e60 203%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23e64 : csite := mkSite 0x23e64 203%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x23e60 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_23e74 : csite := mkSite 0x23e74 203%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23e78 : csite := mkSite 0x23e78 203%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23e7c : csite := mkSite 0x23e7c 203%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x23e74 307%positive 0x10325).
(* [comment removed for export] *)
Definition olcs_23e80 : csite := mkSite 0x23e80 203%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x23e78 343%positive 0x10774).
(* [comment removed for export] *)
Definition olcs_23e88 : csite := mkSite 0x23e88 203%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1010%positive 0x13660).
(* [comment removed for export] *)
Definition olcs_23ea0 : csite := mkSite 0x23ea0 204%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23ea4 : csite := mkSite 0x23ea4 204%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x23ea0 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_23eb4 : csite := mkSite 0x23eb4 204%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23eb8 : csite := mkSite 0x23eb8 204%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23ebc : csite := mkSite 0x23ebc 204%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x23eb4 307%positive 0x10325).
(* [comment removed for export] *)
Definition olcs_23ec0 : csite := mkSite 0x23ec0 204%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x23eb8 301%positive 0x102aa).
(* [comment removed for export] *)
Definition olcs_23ec8 : csite := mkSite 0x23ec8 204%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1010%positive 0x13660).
(* [comment removed for export] *)
Definition olcs_23ee0 : csite := mkSite 0x23ee0 214%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23ee4 : csite := mkSite 0x23ee4 214%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x23ee0 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_23ef4 : csite := mkSite 0x23ef4 214%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23ef8 : csite := mkSite 0x23ef8 214%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23efc : csite := mkSite 0x23efc 214%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x23ef4 307%positive 0x10325).
(* [comment removed for export] *)
Definition olcs_23f00 : csite := mkSite 0x23f00 214%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x23ef8 308%positive 0x10335).
(* [comment removed for export] *)
Definition olcs_23f08 : csite := mkSite 0x23f08 214%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1012%positive 0x13730).
(* [comment removed for export] *)
Definition olcs_23f20 : csite := mkSite 0x23f20 205%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23f24 : csite := mkSite 0x23f24 205%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x23f20 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_23f34 : csite := mkSite 0x23f34 205%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23f38 : csite := mkSite 0x23f38 205%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23f3c : csite := mkSite 0x23f3c 205%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x23f34 307%positive 0x10325).
(* [comment removed for export] *)
Definition olcs_23f40 : csite := mkSite 0x23f40 205%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x23f38 354%positive 0x108c7).
(* [comment removed for export] *)
Definition olcs_23f48 : csite := mkSite 0x23f48 205%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1010%positive 0x13660).
(* [comment removed for export] *)
Definition olcs_23fc8 : csite := mkSite 0x23fc8 206%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 201%positive 0x23cf0).
(* [comment removed for export] *)
Definition olcs_23fe0 : csite := mkSite 0x23fe0 206%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23fe4 : csite := mkSite 0x23fe4 206%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x23fe0 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_23ff8 : csite := mkSite 0x23ff8 206%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_23ffc : csite := mkSite 0x23ffc 206%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24000 : csite := mkSite 0x24000 206%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x23ff8 327%positive 0x10572).
(* [comment removed for export] *)
Definition olcs_24004 : csite := mkSite 0x24004 206%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x23ffc 336%positive 0x10667).
(* [comment removed for export] *)
Definition olcs_24008 : csite := mkSite 0x24008 206%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1011%positive 0x13694).
(* [comment removed for export] *)
Definition olcs_24010 : csite := mkSite 0x24010 206%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24014 : csite := mkSite 0x24014 206%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x24010 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_24024 : csite := mkSite 0x24024 206%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24028 : csite := mkSite 0x24028 206%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_2402c : csite := mkSite 0x2402c 206%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x24024 307%positive 0x10325).
(* [comment removed for export] *)
Definition olcs_24030 : csite := mkSite 0x24030 206%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x24028 336%positive 0x10667).
(* [comment removed for export] *)
Definition olcs_2404c : csite := mkSite 0x2404c 206%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1010%positive 0x13660).
(* [comment removed for export] *)
Definition olcs_2405c : csite := mkSite 0x2405c 206%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 214%positive 0x23ed4).
(* [comment removed for export] *)
Definition olcs_24068 : csite := mkSite 0x24068 206%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 212%positive 0x23be4).
(* [comment removed for export] *)
Definition olcs_240a4 : csite := mkSite 0x240a4 206%positive OP_AUIPC (SH20 (fun imm => Auipc 13 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_240a8 : csite := mkSite 0x240a8 206%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 13 13 imm)) (SK_lo12 0x240a4 5018%positive 0x10a80).
(* [comment removed for export] *)
Definition olcs_24190 : csite := mkSite 0x24190 207%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 204%positive 0x23e94).
(* [comment removed for export] *)
Definition olcs_241a0 : csite := mkSite 0x241a0 207%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_241a4 : csite := mkSite 0x241a4 207%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x241a0 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_241b4 : csite := mkSite 0x241b4 207%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_241b8 : csite := mkSite 0x241b8 207%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_241bc : csite := mkSite 0x241bc 207%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x241b4 325%positive 0x10544).
(* [comment removed for export] *)
Definition olcs_241c0 : csite := mkSite 0x241c0 207%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x241b8 314%positive 0x103d4).
(* [comment removed for export] *)
Definition olcs_241cc : csite := mkSite 0x241cc 207%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_241d0 : csite := mkSite 0x241d0 207%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x241cc 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_241e0 : csite := mkSite 0x241e0 207%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_241e4 : csite := mkSite 0x241e4 207%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_241e8 : csite := mkSite 0x241e8 207%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x241e0 322%positive 0x104cd).
(* [comment removed for export] *)
Definition olcs_241ec : csite := mkSite 0x241ec 207%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x241e4 314%positive 0x103d4).
(* [comment removed for export] *)
Definition olcs_241f4 : csite := mkSite 0x241f4 207%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_241f8 : csite := mkSite 0x241f8 207%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x241f4 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_24208 : csite := mkSite 0x24208 207%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_2420c : csite := mkSite 0x2420c 207%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24210 : csite := mkSite 0x24210 207%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x24208 302%positive 0x102b6).
(* [comment removed for export] *)
Definition olcs_24214 : csite := mkSite 0x24214 207%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x2420c 314%positive 0x103d4).
(* [comment removed for export] *)
Definition olcs_2421c : csite := mkSite 0x2421c 207%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24220 : csite := mkSite 0x24220 207%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x2421c 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_24230 : csite := mkSite 0x24230 207%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24234 : csite := mkSite 0x24234 207%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24238 : csite := mkSite 0x24238 207%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x24230 350%positive 0x10826).
(* [comment removed for export] *)
Definition olcs_2423c : csite := mkSite 0x2423c 207%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x24234 314%positive 0x103d4).
(* [comment removed for export] *)
Definition olcs_2425c : csite := mkSite 0x2425c 207%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1010%positive 0x13660).
(* [comment removed for export] *)
Definition olcs_24280 : csite := mkSite 0x24280 207%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24284 : csite := mkSite 0x24284 207%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 11 11 imm)) (SK_lo12 0x24280 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_24294 : csite := mkSite 0x24294 207%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24298 : csite := mkSite 0x24298 207%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_2429c : csite := mkSite 0x2429c 207%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x24294 351%positive 0x1083d).
(* [comment removed for export] *)
Definition olcs_242a0 : csite := mkSite 0x242a0 207%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x24298 314%positive 0x103d4).
(* [comment removed for export] *)
Definition olcs_242b0 : csite := mkSite 0x242b0 207%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_242b4 : csite := mkSite 0x242b4 207%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 11 11 imm)) (SK_lo12 0x242b0 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_242c4 : csite := mkSite 0x242c4 207%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_242c8 : csite := mkSite 0x242c8 207%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_242cc : csite := mkSite 0x242cc 207%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x242c4 332%positive 0x105e4).
(* [comment removed for export] *)
Definition olcs_242d0 : csite := mkSite 0x242d0 207%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x242c8 314%positive 0x103d4).
(* [comment removed for export] *)
Definition olcs_242d8 : csite := mkSite 0x242d8 207%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1011%positive 0x13694).
(* [comment removed for export] *)
Definition olcs_242e4 : csite := mkSite 0x242e4 207%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_242e8 : csite := mkSite 0x242e8 207%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x242e4 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_242fc : csite := mkSite 0x242fc 207%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24300 : csite := mkSite 0x24300 207%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24304 : csite := mkSite 0x24304 207%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x242fc 305%positive 0x102f1).
(* [comment removed for export] *)
Definition olcs_24308 : csite := mkSite 0x24308 207%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x24300 314%positive 0x103d4).
(* [comment removed for export] *)
Definition olcs_24310 : csite := mkSite 0x24310 207%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1011%positive 0x13694).
(* [comment removed for export] *)
Definition olcs_24324 : csite := mkSite 0x24324 207%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24328 : csite := mkSite 0x24328 207%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 11 11 imm)) (SK_lo12 0x24324 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_24338 : csite := mkSite 0x24338 207%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_2433c : csite := mkSite 0x2433c 207%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24340 : csite := mkSite 0x24340 207%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x24338 333%positive 0x10612).
(* [comment removed for export] *)
Definition olcs_24344 : csite := mkSite 0x24344 207%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x2433c 314%positive 0x103d4).
(* [comment removed for export] *)
Definition olcs_2435c : csite := mkSite 0x2435c 207%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24360 : csite := mkSite 0x24360 207%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x2435c 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_24374 : csite := mkSite 0x24374 207%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24378 : csite := mkSite 0x24378 207%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_2437c : csite := mkSite 0x2437c 207%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x24374 344%positive 0x10781).
(* [comment removed for export] *)
Definition olcs_24380 : csite := mkSite 0x24380 207%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x24378 314%positive 0x103d4).
(* [comment removed for export] *)
Definition olcs_24388 : csite := mkSite 0x24388 207%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_2438c : csite := mkSite 0x2438c 207%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x24388 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_243a0 : csite := mkSite 0x243a0 207%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_243a4 : csite := mkSite 0x243a4 207%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_243a8 : csite := mkSite 0x243a8 207%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x243a0 311%positive 0x1037f).
(* [comment removed for export] *)
Definition olcs_243ac : csite := mkSite 0x243ac 207%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x243a4 314%positive 0x103d4).
(* [comment removed for export] *)
Definition olcs_243b0 : csite := mkSite 0x243b0 207%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1011%positive 0x13694).
(* [comment removed for export] *)
Definition olcs_243c4 : csite := mkSite 0x243c4 207%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 216%positive 0x246d4).
(* [comment removed for export] *)
Definition olcs_243e8 : csite := mkSite 0x243e8 207%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_243ec : csite := mkSite 0x243ec 207%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x243e8 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_24400 : csite := mkSite 0x24400 207%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24404 : csite := mkSite 0x24404 207%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24408 : csite := mkSite 0x24408 207%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x24400 337%positive 0x10675).
(* [comment removed for export] *)
Definition olcs_2440c : csite := mkSite 0x2440c 207%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x24404 314%positive 0x103d4).
(* [comment removed for export] *)
Definition olcs_24438 : csite := mkSite 0x24438 215%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1035%positive 0x15b38).
(* [comment removed for export] *)
Definition olcs_24440 : csite := mkSite 0x24440 215%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1035%positive 0x15b38).
(* [comment removed for export] *)
Definition olcs_2444c : csite := mkSite 0x2444c 215%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24450 : csite := mkSite 0x24450 215%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x2444c 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_24460 : csite := mkSite 0x24460 215%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24464 : csite := mkSite 0x24464 215%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24468 : csite := mkSite 0x24468 215%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x24460 360%positive 0x1097f).
(* [comment removed for export] *)
Definition olcs_2446c : csite := mkSite 0x2446c 215%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x24464 313%positive 0x103c5).
(* [comment removed for export] *)
Definition olcs_24480 : csite := mkSite 0x24480 215%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1011%positive 0x13694).
(* [comment removed for export] *)
Definition olcs_244d8 : csite := mkSite 0x244d8 208%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_244dc : csite := mkSite 0x244dc 208%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x244d8 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_244ec : csite := mkSite 0x244ec 208%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_244f0 : csite := mkSite 0x244f0 208%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x244ec 317%positive 0x10436).
(* [comment removed for export] *)
Definition olcs_244f8 : csite := mkSite 0x244f8 208%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_244fc : csite := mkSite 0x244fc 208%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x244f8 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_2450c : csite := mkSite 0x2450c 208%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24510 : csite := mkSite 0x24510 208%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x2450c 345%positive 0x107bb).
(* [comment removed for export] *)
Definition olcs_24524 : csite := mkSite 0x24524 208%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24528 : csite := mkSite 0x24528 208%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x24524 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_24538 : csite := mkSite 0x24538 208%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_2453c : csite := mkSite 0x2453c 208%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x24538 329%positive 0x10598).
(* [comment removed for export] *)
Definition olcs_24544 : csite := mkSite 0x24544 208%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24548 : csite := mkSite 0x24548 208%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x24544 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_24558 : csite := mkSite 0x24558 208%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_2455c : csite := mkSite 0x2455c 208%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x24558 328%positive 0x1058d).
(* [comment removed for export] *)
Definition olcs_24560 : csite := mkSite 0x24560 208%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24564 : csite := mkSite 0x24564 208%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x24560 356%positive 0x108e9).
(* [comment removed for export] *)
Definition olcs_24598 : csite := mkSite 0x24598 208%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1012%positive 0x13730).
(* [comment removed for export] *)
Definition olcs_2460c : csite := mkSite 0x2460c 208%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1034%positive 0x15a00).
(* [comment removed for export] *)
Definition olcs_24628 : csite := mkSite 0x24628 208%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1034%positive 0x15a00).
(* [comment removed for export] *)
Definition olcs_2463c : csite := mkSite 0x2463c 208%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24648 : csite := mkSite 0x24648 208%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 24 11 imm)) (SK_lo12 0x2463c 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_2464c : csite := mkSite 0x2464c 208%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24650 : csite := mkSite 0x24650 208%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 18 10 imm)) (SK_lo12 0x2464c 355%positive 0x108d3).
(* [comment removed for export] *)
Definition olcs_24654 : csite := mkSite 0x24654 208%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24658 : csite := mkSite 0x24658 208%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 19 10 imm)) (SK_lo12 0x24654 303%positive 0x102c7).
(* [comment removed for export] *)
Definition olcs_246cc : csite := mkSite 0x246cc 208%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1010%positive 0x13660).
(* [comment removed for export] *)
Definition olcs_24718 : csite := mkSite 0x24718 216%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 201%positive 0x23cf0).
(* [comment removed for export] *)
Definition olcs_2473c : csite := mkSite 0x2473c 216%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 212%positive 0x23be4).
(* [comment removed for export] *)
Definition olcs_24748 : csite := mkSite 0x24748 216%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 214%positive 0x23ed4).
(* [comment removed for export] *)
Definition olcs_24760 : csite := mkSite 0x24760 216%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 217%positive 0x2499c).
(* [comment removed for export] *)
Definition olcs_24778 : csite := mkSite 0x24778 216%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_2477c : csite := mkSite 0x2477c 216%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x24778 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_2478c : csite := mkSite 0x2478c 216%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24790 : csite := mkSite 0x24790 216%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24794 : csite := mkSite 0x24794 216%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x2478c 363%positive 0x109fc).
(* [comment removed for export] *)
Definition olcs_24798 : csite := mkSite 0x24798 216%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x24790 364%positive 0x10a12).
(* [comment removed for export] *)
Definition olcs_247a0 : csite := mkSite 0x247a0 216%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_247a4 : csite := mkSite 0x247a4 216%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x247a0 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_247b4 : csite := mkSite 0x247b4 216%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_247b8 : csite := mkSite 0x247b8 216%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_247bc : csite := mkSite 0x247bc 216%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x247b4 304%positive 0x102d6).
(* [comment removed for export] *)
Definition olcs_247c0 : csite := mkSite 0x247c0 216%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x247b8 364%positive 0x10a12).
(* [comment removed for export] *)
Definition olcs_247e8 : csite := mkSite 0x247e8 216%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1010%positive 0x13660).
(* [comment removed for export] *)
Definition olcs_24930 : csite := mkSite 0x24930 216%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24934 : csite := mkSite 0x24934 216%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x24930 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_24944 : csite := mkSite 0x24944 216%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24948 : csite := mkSite 0x24948 216%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_2494c : csite := mkSite 0x2494c 216%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x24944 330%positive 0x105a6).
(* [comment removed for export] *)
Definition olcs_24950 : csite := mkSite 0x24950 216%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x24948 364%positive 0x10a12).
(* [comment removed for export] *)
Definition olcs_24958 : csite := mkSite 0x24958 216%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1010%positive 0x13660).
(* [comment removed for export] *)
Definition olcs_249d8 : csite := mkSite 0x249d8 217%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 205%positive 0x23f14).
(* [comment removed for export] *)
Definition olcs_249e4 : csite := mkSite 0x249e4 217%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 204%positive 0x23e94).
(* [comment removed for export] *)
Definition olcs_249f0 : csite := mkSite 0x249f0 217%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 203%positive 0x23e54).
(* [comment removed for export] *)
Definition olcs_249fc : csite := mkSite 0x249fc 217%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 212%positive 0x23be4).
(* [comment removed for export] *)
Definition olcs_24a08 : csite := mkSite 0x24a08 217%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 214%positive 0x23ed4).
(* [comment removed for export] *)
Definition olcs_24a7c : csite := mkSite 0x24a7c 217%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24a80 : csite := mkSite 0x24a80 217%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x24a7c 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_24a90 : csite := mkSite 0x24a90 217%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24a94 : csite := mkSite 0x24a94 217%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24a98 : csite := mkSite 0x24a98 217%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x24a90 335%positive 0x10654).
(* [comment removed for export] *)
Definition olcs_24a9c : csite := mkSite 0x24a9c 217%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x24a94 361%positive 0x109d2).
(* [comment removed for export] *)
Definition olcs_24aa4 : csite := mkSite 0x24aa4 217%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24aa8 : csite := mkSite 0x24aa8 217%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 11 11 imm)) (SK_lo12 0x24aa4 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_24ab8 : csite := mkSite 0x24ab8 217%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24abc : csite := mkSite 0x24abc 217%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24ac0 : csite := mkSite 0x24ac0 217%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x24ab8 307%positive 0x10325).
(* [comment removed for export] *)
Definition olcs_24ac4 : csite := mkSite 0x24ac4 217%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x24abc 361%positive 0x109d2).
(* [comment removed for export] *)
Definition olcs_24aec : csite := mkSite 0x24aec 217%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1010%positive 0x13660).
(* [comment removed for export] *)
Definition olcs_24bd8 : csite := mkSite 0x24bd8 209%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24bdc : csite := mkSite 0x24bdc 209%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x24bd8 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_24bec : csite := mkSite 0x24bec 209%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24bf0 : csite := mkSite 0x24bf0 209%positive OP_AUIPC (SH20 (fun imm => Auipc 12 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24bf4 : csite := mkSite 0x24bf4 209%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x24bec 339%positive 0x106fa).
(* [comment removed for export] *)
Definition olcs_24bf8 : csite := mkSite 0x24bf8 209%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 13 12 imm)) (SK_lo12 0x24bf0 331%positive 0x105cb).
(* [comment removed for export] *)
Definition olcs_24c04 : csite := mkSite 0x24c04 209%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1011%positive 0x13694).
(* [comment removed for export] *)
Definition olcs_24c0c : csite := mkSite 0x24c0c 209%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24c10 : csite := mkSite 0x24c10 209%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x24c0c 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_24c20 : csite := mkSite 0x24c20 209%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24c24 : csite := mkSite 0x24c24 209%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24c28 : csite := mkSite 0x24c28 209%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x24c20 345%positive 0x107bb).
(* [comment removed for export] *)
Definition olcs_24c2c : csite := mkSite 0x24c2c 209%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x24c24 331%positive 0x105cb).
(* [comment removed for export] *)
Definition olcs_24c78 : csite := mkSite 0x24c78 209%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24c7c : csite := mkSite 0x24c7c 209%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x24c78 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_24c8c : csite := mkSite 0x24c8c 209%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24c90 : csite := mkSite 0x24c90 209%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24c94 : csite := mkSite 0x24c94 209%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x24c8c 358%positive 0x10935).
(* [comment removed for export] *)
Definition olcs_24c98 : csite := mkSite 0x24c98 209%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x24c90 331%positive 0x105cb).
(* [comment removed for export] *)
Definition olcs_24ca0 : csite := mkSite 0x24ca0 209%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24ca4 : csite := mkSite 0x24ca4 209%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x24ca0 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_24cb4 : csite := mkSite 0x24cb4 209%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24cb8 : csite := mkSite 0x24cb8 209%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24cbc : csite := mkSite 0x24cbc 209%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x24cb4 340%positive 0x1071d).
(* [comment removed for export] *)
Definition olcs_24cc0 : csite := mkSite 0x24cc0 209%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x24cb8 331%positive 0x105cb).
(* [comment removed for export] *)
Definition olcs_24cf8 : csite := mkSite 0x24cf8 209%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1012%positive 0x13730).
(* [comment removed for export] *)
Definition olcs_24d08 : csite := mkSite 0x24d08 209%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24d0c : csite := mkSite 0x24d0c 209%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x24d08 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_24d1c : csite := mkSite 0x24d1c 209%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24d20 : csite := mkSite 0x24d20 209%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24d24 : csite := mkSite 0x24d24 209%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x24d1c 309%positive 0x10340).
(* [comment removed for export] *)
Definition olcs_24d28 : csite := mkSite 0x24d28 209%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x24d20 331%positive 0x105cb).
(* [comment removed for export] *)
Definition olcs_24d40 : csite := mkSite 0x24d40 209%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24d44 : csite := mkSite 0x24d44 209%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x24d40 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_24d54 : csite := mkSite 0x24d54 209%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24d58 : csite := mkSite 0x24d58 209%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24d5c : csite := mkSite 0x24d5c 209%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x24d54 306%positive 0x10316).
(* [comment removed for export] *)
Definition olcs_24d60 : csite := mkSite 0x24d60 209%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x24d58 331%positive 0x105cb).
(* [comment removed for export] *)
Definition olcs_24d98 : csite := mkSite 0x24d98 209%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 211%positive 0x238e8).
(* [comment removed for export] *)
Definition olcs_24da8 : csite := mkSite 0x24da8 209%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 212%positive 0x23be4).
(* [comment removed for export] *)
Definition olcs_24dd0 : csite := mkSite 0x24dd0 209%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 213%positive 0x23c24).
(* [comment removed for export] *)
Definition olcs_24de8 : csite := mkSite 0x24de8 209%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 200%positive 0x23720).
(* [comment removed for export] *)
Definition olcs_24e04 : csite := mkSite 0x24e04 209%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 208%positive 0x24498).
(* [comment removed for export] *)
Definition olcs_24e18 : csite := mkSite 0x24e18 209%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 202%positive 0x23d70).
(* [comment removed for export] *)
Definition olcs_24e24 : csite := mkSite 0x24e24 209%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 213%positive 0x23c24).
(* [comment removed for export] *)
Definition olcs_24e28 : csite := mkSite 0x24e28 209%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24e2c : csite := mkSite 0x24e2c 209%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x24e28 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_24e3c : csite := mkSite 0x24e3c 209%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24e40 : csite := mkSite 0x24e40 209%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24e44 : csite := mkSite 0x24e44 209%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x24e3c 352%positive 0x1086c).
(* [comment removed for export] *)
Definition olcs_24e48 : csite := mkSite 0x24e48 209%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x24e40 331%positive 0x105cb).
(* [comment removed for export] *)
Definition olcs_24e50 : csite := mkSite 0x24e50 209%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24e54 : csite := mkSite 0x24e54 209%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x24e50 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_24e64 : csite := mkSite 0x24e64 209%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24e68 : csite := mkSite 0x24e68 209%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24e6c : csite := mkSite 0x24e6c 209%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x24e64 342%positive 0x10764).
(* [comment removed for export] *)
Definition olcs_24e70 : csite := mkSite 0x24e70 209%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x24e68 331%positive 0x105cb).
(* [comment removed for export] *)
Definition olcs_24e78 : csite := mkSite 0x24e78 209%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24e7c : csite := mkSite 0x24e7c 209%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x24e78 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_24e8c : csite := mkSite 0x24e8c 209%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24e90 : csite := mkSite 0x24e90 209%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24e94 : csite := mkSite 0x24e94 209%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x24e8c 320%positive 0x1047c).
(* [comment removed for export] *)
Definition olcs_24e98 : csite := mkSite 0x24e98 209%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x24e90 331%positive 0x105cb).
(* [comment removed for export] *)
Definition olcs_24ea0 : csite := mkSite 0x24ea0 209%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24ea4 : csite := mkSite 0x24ea4 209%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x24ea0 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_24eb4 : csite := mkSite 0x24eb4 209%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24eb8 : csite := mkSite 0x24eb8 209%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24ebc : csite := mkSite 0x24ebc 209%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x24eb4 323%positive 0x104e0).
(* [comment removed for export] *)
Definition olcs_24ec0 : csite := mkSite 0x24ec0 209%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x24eb8 331%positive 0x105cb).
(* [comment removed for export] *)
Definition olcs_24ed0 : csite := mkSite 0x24ed0 209%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1011%positive 0x13694).
(* [comment removed for export] *)
Definition olcs_24ed8 : csite := mkSite 0x24ed8 209%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24edc : csite := mkSite 0x24edc 209%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x24ed8 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_24eec : csite := mkSite 0x24eec 209%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24ef0 : csite := mkSite 0x24ef0 209%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24ef4 : csite := mkSite 0x24ef4 209%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x24eec 346%positive 0x107cc).
(* [comment removed for export] *)
Definition olcs_24ef8 : csite := mkSite 0x24ef8 209%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x24ef0 331%positive 0x105cb).
(* [comment removed for export] *)
Definition olcs_24f0c : csite := mkSite 0x24f0c 209%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 213%positive 0x23c24).
(* [comment removed for export] *)
Definition olcs_24f10 : csite := mkSite 0x24f10 209%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24f14 : csite := mkSite 0x24f14 209%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x24f10 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_24f24 : csite := mkSite 0x24f24 209%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24f28 : csite := mkSite 0x24f28 209%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24f2c : csite := mkSite 0x24f2c 209%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x24f24 365%positive 0x10a26).
(* [comment removed for export] *)
Definition olcs_24f30 : csite := mkSite 0x24f30 209%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x24f28 331%positive 0x105cb).
(* [comment removed for export] *)
Definition olcs_24f3c : csite := mkSite 0x24f3c 209%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 214%positive 0x23ed4).
(* [comment removed for export] *)
Definition olcs_24f48 : csite := mkSite 0x24f48 209%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1090%positive 0x1c9b4).
(* [comment removed for export] *)
Definition olcs_24f5c : csite := mkSite 0x24f5c 209%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 207%positive 0x24118).
(* [comment removed for export] *)
Definition olcs_24f74 : csite := mkSite 0x24f74 209%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 213%positive 0x23c24).
(* [comment removed for export] *)
Definition olcs_24f78 : csite := mkSite 0x24f78 209%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24f7c : csite := mkSite 0x24f7c 209%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x24f78 5026%positive 0x1e3b0).
(* [comment removed for export] *)
Definition olcs_24f8c : csite := mkSite 0x24f8c 209%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24f90 : csite := mkSite 0x24f90 209%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition olcs_24f94 : csite := mkSite 0x24f94 209%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x24f8c 315%positive 0x103e3).
(* [comment removed for export] *)
Definition olcs_24f98 : csite := mkSite 0x24f98 209%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x24f90 331%positive 0x105cb).
(* [comment removed for export] *)
Definition olcs_24fa0 : csite := mkSite 0x24fa0 209%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1012%positive 0x13730).

Definition canon_sites_OL : list csite := [
  olcs_2372c; olcs_23754; olcs_23760; olcs_23764; olcs_23774; olcs_23778; olcs_2377c; olcs_23780;
  olcs_23794; olcs_237c4; olcs_237d4; olcs_237d8; olcs_237fc; olcs_23804; olcs_23808; olcs_23818;
  olcs_2381c; olcs_23820; olcs_23824; olcs_23840; olcs_23870; olcs_23884; olcs_23890; olcs_23894;
  olcs_23898; olcs_238a8; olcs_238ac; olcs_238b0; olcs_238b4; olcs_238bc; olcs_2393c; olcs_23940;
  olcs_23950; olcs_23954; olcs_23958; olcs_2395c; olcs_23978; olcs_23984; olcs_23988; olcs_2398c;
  olcs_23990; olcs_23998; olcs_2399c; olcs_239ac; olcs_239b0; olcs_239b4; olcs_239b8; olcs_239c0;
  olcs_239c4; olcs_239d4; olcs_239d8; olcs_239dc; olcs_239e0; olcs_23a00; olcs_23a04; olcs_23a14;
  olcs_23a18; olcs_23a1c; olcs_23a20; olcs_23a3c; olcs_23a48; olcs_23a4c; olcs_23a50; olcs_23a54;
  olcs_23a5c; olcs_23a60; olcs_23a70; olcs_23a74; olcs_23a78; olcs_23a7c; olcs_23aa0; olcs_23ab0;
  olcs_23ab4; olcs_23ac4; olcs_23ac8; olcs_23acc; olcs_23ad0; olcs_23ae4; olcs_23ae8; olcs_23af8;
  olcs_23afc; olcs_23b00; olcs_23b04; olcs_23b10; olcs_23b14; olcs_23b24; olcs_23b28; olcs_23b2c;
  olcs_23b30; olcs_23b34; olcs_23b74; olcs_23ba0; olcs_23ba4; olcs_23bb4; olcs_23bb8; olcs_23bbc;
  olcs_23bc0; olcs_23bf0; olcs_23bf4; olcs_23c04; olcs_23c08; olcs_23c0c; olcs_23c10; olcs_23c18;
  olcs_23c60; olcs_23c64; olcs_23c74; olcs_23c88; olcs_23c94; olcs_23ca4; olcs_23ca8; olcs_23cb8;
  olcs_23cbc; olcs_23cc0; olcs_23cc4; olcs_23cd8; olcs_23d3c; olcs_23d40; olcs_23d50; olcs_23d54;
  olcs_23d58; olcs_23d5c; olcs_23d64; olcs_23da0; olcs_23dbc; olcs_23dd0; olcs_23dd4; olcs_23de4;
  olcs_23de8; olcs_23dec; olcs_23df0; olcs_23e08; olcs_23e0c; olcs_23e10; olcs_23e20; olcs_23e24;
  olcs_23e28; olcs_23e2c; olcs_23e34; olcs_23e60; olcs_23e64; olcs_23e74; olcs_23e78; olcs_23e7c;
  olcs_23e80; olcs_23e88; olcs_23ea0; olcs_23ea4; olcs_23eb4; olcs_23eb8; olcs_23ebc; olcs_23ec0;
  olcs_23ec8; olcs_23ee0; olcs_23ee4; olcs_23ef4; olcs_23ef8; olcs_23efc; olcs_23f00; olcs_23f08;
  olcs_23f20; olcs_23f24; olcs_23f34; olcs_23f38; olcs_23f3c; olcs_23f40; olcs_23f48; olcs_23fc8;
  olcs_23fe0; olcs_23fe4; olcs_23ff8; olcs_23ffc; olcs_24000; olcs_24004; olcs_24008; olcs_24010;
  olcs_24014; olcs_24024; olcs_24028; olcs_2402c; olcs_24030; olcs_2404c; olcs_2405c; olcs_24068;
  olcs_240a4; olcs_240a8; olcs_24190; olcs_241a0; olcs_241a4; olcs_241b4; olcs_241b8; olcs_241bc;
  olcs_241c0; olcs_241cc; olcs_241d0; olcs_241e0; olcs_241e4; olcs_241e8; olcs_241ec; olcs_241f4;
  olcs_241f8; olcs_24208; olcs_2420c; olcs_24210; olcs_24214; olcs_2421c; olcs_24220; olcs_24230;
  olcs_24234; olcs_24238; olcs_2423c; olcs_2425c; olcs_24280; olcs_24284; olcs_24294; olcs_24298;
  olcs_2429c; olcs_242a0; olcs_242b0; olcs_242b4; olcs_242c4; olcs_242c8; olcs_242cc; olcs_242d0;
  olcs_242d8; olcs_242e4; olcs_242e8; olcs_242fc; olcs_24300; olcs_24304; olcs_24308; olcs_24310;
  olcs_24324; olcs_24328; olcs_24338; olcs_2433c; olcs_24340; olcs_24344; olcs_2435c; olcs_24360;
  olcs_24374; olcs_24378; olcs_2437c; olcs_24380; olcs_24388; olcs_2438c; olcs_243a0; olcs_243a4;
  olcs_243a8; olcs_243ac; olcs_243b0; olcs_243c4; olcs_243e8; olcs_243ec; olcs_24400; olcs_24404;
  olcs_24408; olcs_2440c; olcs_24438; olcs_24440; olcs_2444c; olcs_24450; olcs_24460; olcs_24464;
  olcs_24468; olcs_2446c; olcs_24480; olcs_244d8; olcs_244dc; olcs_244ec; olcs_244f0; olcs_244f8;
  olcs_244fc; olcs_2450c; olcs_24510; olcs_24524; olcs_24528; olcs_24538; olcs_2453c; olcs_24544;
  olcs_24548; olcs_24558; olcs_2455c; olcs_24560; olcs_24564; olcs_24598; olcs_2460c; olcs_24628;
  olcs_2463c; olcs_24648; olcs_2464c; olcs_24650; olcs_24654; olcs_24658; olcs_246cc; olcs_24718;
  olcs_2473c; olcs_24748; olcs_24760; olcs_24778; olcs_2477c; olcs_2478c; olcs_24790; olcs_24794;
  olcs_24798; olcs_247a0; olcs_247a4; olcs_247b4; olcs_247b8; olcs_247bc; olcs_247c0; olcs_247e8;
  olcs_24930; olcs_24934; olcs_24944; olcs_24948; olcs_2494c; olcs_24950; olcs_24958; olcs_249d8;
  olcs_249e4; olcs_249f0; olcs_249fc; olcs_24a08; olcs_24a7c; olcs_24a80; olcs_24a90; olcs_24a94;
  olcs_24a98; olcs_24a9c; olcs_24aa4; olcs_24aa8; olcs_24ab8; olcs_24abc; olcs_24ac0; olcs_24ac4;
  olcs_24aec; olcs_24bd8; olcs_24bdc; olcs_24bec; olcs_24bf0; olcs_24bf4; olcs_24bf8; olcs_24c04;
  olcs_24c0c; olcs_24c10; olcs_24c20; olcs_24c24; olcs_24c28; olcs_24c2c; olcs_24c78; olcs_24c7c;
  olcs_24c8c; olcs_24c90; olcs_24c94; olcs_24c98; olcs_24ca0; olcs_24ca4; olcs_24cb4; olcs_24cb8;
  olcs_24cbc; olcs_24cc0; olcs_24cf8; olcs_24d08; olcs_24d0c; olcs_24d1c; olcs_24d20; olcs_24d24;
  olcs_24d28; olcs_24d40; olcs_24d44; olcs_24d54; olcs_24d58; olcs_24d5c; olcs_24d60; olcs_24d98;
  olcs_24da8; olcs_24dd0; olcs_24de8; olcs_24e04; olcs_24e18; olcs_24e24; olcs_24e28; olcs_24e2c;
  olcs_24e3c; olcs_24e40; olcs_24e44; olcs_24e48; olcs_24e50; olcs_24e54; olcs_24e64; olcs_24e68;
  olcs_24e6c; olcs_24e70; olcs_24e78; olcs_24e7c; olcs_24e8c; olcs_24e90; olcs_24e94; olcs_24e98;
  olcs_24ea0; olcs_24ea4; olcs_24eb4; olcs_24eb8; olcs_24ebc; olcs_24ec0; olcs_24ed0; olcs_24ed8;
  olcs_24edc; olcs_24eec; olcs_24ef0; olcs_24ef4; olcs_24ef8; olcs_24f0c; olcs_24f10; olcs_24f14;
  olcs_24f24; olcs_24f28; olcs_24f2c; olcs_24f30; olcs_24f3c; olcs_24f48; olcs_24f5c; olcs_24f74;
  olcs_24f78; olcs_24f7c; olcs_24f8c; olcs_24f90; olcs_24f94; olcs_24f98; olcs_24fa0].

Class RelocSitesOL (RL : Reloc) := { rl_sites_ol_ok : sites_check canon_sites_OL = true }.

Section Facts.
Context {RL : Reloc} {RS : RelocSitesOL RL}.
Definition rl_site_F_OL := site_F canon_sites_OL rl_sites_ol_ok.
Definition rl_site_D_OL := site_D canon_sites_OL rl_sites_ol_ok.
Definition rl_site_V_OL := site_V canon_sites_OL rl_sites_ol_ok.
Definition rl_site_J_OL := site_J canon_sites_OL rl_sites_ol_ok.
End Facts.
