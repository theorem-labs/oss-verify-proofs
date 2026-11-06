(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require Import PropExec.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc Require Import Reloc RelocCode RelocSites.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

(* [comment removed for export] *)
Definition cs_13084 : csite := mkSite 0x13084 1000%positive OP_AUIPC (SH20 (fun imm => Auipc 3 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_13088 : csite := mkSite 0x13088 1000%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 3 3 imm)) (SK_lo12 0x13084 8%positive 0x10800).
(* [comment removed for export] *)
Definition cs_13090 : csite := mkSite 0x13090 1000%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_13094 : csite := mkSite 0x13094 1000%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x13090 8%positive 0x0).
(* [comment removed for export] *)
Definition cs_1309c : csite := mkSite 0x1309c 1000%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1001%positive 0x130a0).
(* [comment removed for export] *)
Definition cs_130a4 : csite := mkSite 0x130a4 1001%positive OP_AUIPC (SH20 (fun imm => Auipc 12 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_130a8 : csite := mkSite 0x130a8 1001%positive OP_AUIPC (SH20 (fun imm => Auipc 13 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_130ac : csite := mkSite 0x130ac 1001%positive OP_AUIPC (SH20 (fun imm => Auipc 14 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_130b0 : csite := mkSite 0x130b0 1001%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 15 12 imm)) (SK_lo12 0x130a4 5012%positive 0x1e370).
(* [comment removed for export] *)
Definition cs_130b4 : csite := mkSite 0x130b4 1001%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 13 13 imm)) (SK_lo12 0x130a8 5012%positive 0x1e378).
(* [comment removed for export] *)
Definition cs_130b8 : csite := mkSite 0x130b8 1001%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 14 14 imm)) (SK_lo12 0x130ac 5012%positive 0x1e380).
(* [comment removed for export] *)
Definition cs_130c8 : csite := mkSite 0x130c8 1001%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1019%positive 0x153e8).
(* [comment removed for export] *)
Definition cs_130dc : csite := mkSite 0x130dc 1002%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_130e0 : csite := mkSite 0x130e0 1002%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x130dc 5015%positive 0x1f630).
(* [comment removed for export] *)
Definition cs_130f8 : csite := mkSite 0x130f8 1002%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_130fc : csite := mkSite 0x130fc 1002%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 10 imm)) (SK_lo12 0x130f8 5015%positive 0x1f630).
(* [comment removed for export] *)
Definition cs_13108 : csite := mkSite 0x13108 1002%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_1310c : csite := mkSite 0x1310c 1002%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x13108 5012%positive 0x1e388).
(* [comment removed for export] *)
Definition cs_13118 : csite := mkSite 0x13118 1002%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_1311c : csite := mkSite 0x1311c 1002%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x13118 5011%positive 0x11968).
(* [comment removed for export] *)
Definition cs_13120 : csite := mkSite 0x13120 1002%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_13124 : csite := mkSite 0x13124 1002%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x13120 5015%positive 0x1f638).
(* [comment removed for export] *)
Definition cs_13150 : csite := mkSite 0x13150 1003%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_13154 : csite := mkSite 0x13154 1003%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x13150 5015%positive 0x1f678).
(* [comment removed for export] *)
Definition cs_1316c : csite := mkSite 0x1316c 1003%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_13170 : csite := mkSite 0x13170 1003%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 10 imm)) (SK_lo12 0x1316c 5015%positive 0x1f678).
(* [comment removed for export] *)
Definition cs_1317c : csite := mkSite 0x1317c 1003%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_13180 : csite := mkSite 0x13180 1003%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x1317c 5012%positive 0x1e390).
(* [comment removed for export] *)
Definition cs_1318c : csite := mkSite 0x1318c 1003%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_13190 : csite := mkSite 0x13190 1003%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x1318c 5013%positive 0x1f3f8).
(* [comment removed for export] *)
Definition cs_131a0 : csite := mkSite 0x131a0 1003%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_131a4 : csite := mkSite 0x131a4 1003%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x131a0 5012%positive 0x1e398).
(* [comment removed for export] *)
Definition cs_131b0 : csite := mkSite 0x131b0 1003%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_131b4 : csite := mkSite 0x131b4 1003%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x131b0 5011%positive 0x11968).
(* [comment removed for export] *)
Definition cs_1320c : csite := mkSite 0x1320c 1004%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1028%positive 0x15874).
(* [comment removed for export] *)
Definition cs_13220 : csite := mkSite 0x13220 1004%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1036%positive 0x15b3c).
(* [comment removed for export] *)
Definition cs_13230 : csite := mkSite 0x13230 1004%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_13234 : csite := mkSite 0x13234 1004%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 22 10 imm)) (SK_lo12 0x13230 5015%positive 0x1f679).
(* [comment removed for export] *)
Definition cs_1324c : csite := mkSite 0x1324c 1004%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1090%positive 0x1c9b4).
(* [comment removed for export] *)
Definition cs_13274 : csite := mkSite 0x13274 1004%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1036%positive 0x15b3c).
(* [comment removed for export] *)
Definition cs_13290 : csite := mkSite 0x13290 1004%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1090%positive 0x1c9b4).
(* [comment removed for export] *)
Definition cs_13298 : csite := mkSite 0x13298 1004%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1035%positive 0x15b38).
(* [comment removed for export] *)
Definition cs_132b4 : csite := mkSite 0x132b4 1004%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1101%positive 0x1d314).
(* [comment removed for export] *)
Definition cs_132c8 : csite := mkSite 0x132c8 1004%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1099%positive 0x1d2b4).
(* [comment removed for export] *)
Definition cs_1332c : csite := mkSite 0x1332c 1004%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1005%positive 0x13494).
(* [comment removed for export] *)
Definition cs_13340 : csite := mkSite 0x13340 1004%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1007%positive 0x134a0).
(* [comment removed for export] *)
Definition cs_13350 : csite := mkSite 0x13350 1004%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1006%positive 0x13498).
(* [comment removed for export] *)
Definition cs_13368 : csite := mkSite 0x13368 1004%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_1336c : csite := mkSite 0x1336c 1004%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x13368 5034%positive 0x1e3a0).   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition cs_13378 : csite := mkSite 0x13378 1004%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_1337c : csite := mkSite 0x1337c 1004%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x13378 4006%positive 0x10492).
(* [comment removed for export] *)
Definition cs_13380 : csite := mkSite 0x13380 1004%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1057%positive 0x17a88).
(* [comment removed for export] *)
Definition cs_13388 : csite := mkSite 0x13388 1004%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_1338c : csite := mkSite 0x1338c 1004%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x13388 5034%positive 0x1e3a0).   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition cs_13394 : csite := mkSite 0x13394 1004%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_1339c : csite := mkSite 0x1339c 1004%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x13394 4015%positive 0x109eb).
(* [comment removed for export] *)
Definition cs_133a4 : csite := mkSite 0x133a4 1004%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_133a8 : csite := mkSite 0x133a8 1004%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x133a4 5034%positive 0x1e3a0).   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition cs_133b0 : csite := mkSite 0x133b0 1004%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_133b8 : csite := mkSite 0x133b8 1004%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x133b0 4007%positive 0x104a3).
(* [comment removed for export] *)
Definition cs_133c0 : csite := mkSite 0x133c0 1004%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1061%positive 0x17cd4).
(* [comment removed for export] *)
Definition cs_133c8 : csite := mkSite 0x133c8 1004%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1035%positive 0x15b38).
(* [comment removed for export] *)
Definition cs_133fc : csite := mkSite 0x133fc 1004%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_13400 : csite := mkSite 0x13400 1004%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x133fc 5034%positive 0x1e3a0).   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition cs_13408 : csite := mkSite 0x13408 1004%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_1340c : csite := mkSite 0x1340c 1004%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x13408 4012%positive 0x108cc).
(* [comment removed for export] *)
Definition cs_13418 : csite := mkSite 0x13418 1004%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_1341c : csite := mkSite 0x1341c 1004%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x13418 5034%positive 0x1e3a0).   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition cs_13424 : csite := mkSite 0x13424 1004%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_13428 : csite := mkSite 0x13428 1004%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x13424 4010%positive 0x106e8).
(* [comment removed for export] *)
Definition cs_13430 : csite := mkSite 0x13430 1004%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1057%positive 0x17a88).
(* [comment removed for export] *)
Definition cs_13438 : csite := mkSite 0x13438 1004%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_1343c : csite := mkSite 0x1343c 1004%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x13438 5034%positive 0x1e3a0).   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition cs_13444 : csite := mkSite 0x13444 1004%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_1344c : csite := mkSite 0x1344c 1004%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x13444 4002%positive 0x10445).
(* [comment removed for export] *)
Definition cs_13454 : csite := mkSite 0x13454 1004%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1061%positive 0x17cd4).
(* [comment removed for export] *)
Definition cs_1345c : csite := mkSite 0x1345c 1004%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1027%positive 0x15800).
(* [comment removed for export] *)
Definition cs_13460 : csite := mkSite 0x13460 1004%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_13464 : csite := mkSite 0x13464 1004%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x13460 5034%positive 0x1e3a0).   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition cs_1346c : csite := mkSite 0x1346c 1004%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_13470 : csite := mkSite 0x13470 1004%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x1346c 4011%positive 0x108b7).
(* [comment removed for export] *)
Definition cs_13478 : csite := mkSite 0x13478 1004%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_1347c : csite := mkSite 0x1347c 1004%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x13478 5034%positive 0x1e3a0).   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition cs_13484 : csite := mkSite 0x13484 1004%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_1348c : csite := mkSite 0x1348c 1004%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x13484 4002%positive 0x10445).
(* [comment removed for export] *)
Definition cs_134cc : csite := cs_13084.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition cs_134d0 : csite := cs_13084.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition cs_134e0 : csite := cs_13084.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition cs_134e4 : csite := cs_13084.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition cs_134f4 : csite := cs_13084.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition cs_134f8 : csite := cs_13084.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition cs_13524 : csite := cs_13084.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition cs_13538 : csite := cs_13084.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition cs_1355c : csite := cs_13084.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition cs_13568 : csite := cs_13084.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition cs_13578 : csite := cs_13084.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition cs_135d8 : csite := mkSite 0x135d8 1008%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_135dc : csite := mkSite 0x135dc 1008%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x135d8 4003%positive 0x10459).
(* [comment removed for export] *)
Definition cs_135e4 : csite := mkSite 0x135e4 1008%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1085%positive 0x1c684).
(* [comment removed for export] *)
Definition cs_13674 : csite := mkSite 0x13674 1010%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_13678 : csite := mkSite 0x13678 1010%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x13674 4016%positive 0x10a13).
(* [comment removed for export] *)
Definition cs_1367c : csite := mkSite 0x1367c 1010%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1011%positive 0x13694).
(* [comment removed for export] *)
Definition cs_13708 : csite := mkSite 0x13708 1011%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1087%positive 0x1c740).
(* [comment removed for export] *)
Definition cs_13710 : csite := mkSite 0x13710 1011%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_13714 : csite := mkSite 0x13714 1011%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 11 10 imm)) (SK_lo12 0x13710 5013%positive 0x1f428).
(* [comment removed for export] *)
Definition cs_13744 : csite := mkSite 0x13744 1012%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_13748 : csite := mkSite 0x13748 1012%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x13744 4016%positive 0x10a13).
(* [comment removed for export] *)
Definition cs_1374c : csite := mkSite 0x1374c 1012%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1011%positive 0x13694).
(* [comment removed for export] *)
Definition cs_1376c : csite := mkSite 0x1376c 1013%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_13770 : csite := mkSite 0x13770 1013%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 11 11 imm)) (SK_lo12 0x1376c 5034%positive 0x1e3a0).   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition cs_13778 : csite := mkSite 0x13778 1013%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1059%positive 0x17b40).
(* [comment removed for export] *)
Definition cs_13780 : csite := mkSite 0x13780 1014%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_13784 : csite := mkSite 0x13784 1014%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x13780 1013%positive 0x13764).
(* [comment removed for export] *)
Definition cs_13788 : csite := mkSite 0x13788 1014%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_1378c : csite := mkSite 0x1378c 1014%positive OP_STORE (SH12 (fun imm => Store SZ8 11 10 imm)) (SK_lo12 0x13788 5013%positive 0x1f428).
(* [comment removed for export] *)
Definition cs_14d1c : csite := mkSite 0x14d1c 1015%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 3001%positive 0x14d20).
(* [comment removed for export] *)
Definition cs_15198 : csite := mkSite 0x15198 1017%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1091%positive 0x1cdb8).
(* [comment removed for export] *)
Definition cs_1519c : csite := mkSite 0x1519c 1017%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_151a0 : csite := mkSite 0x151a0 1017%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x1519c 5027%positive 0x1e3b8).
(* [comment removed for export] *)
Definition cs_151b4 : csite := mkSite 0x151b4 1017%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_151b8 : csite := mkSite 0x151b8 1017%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 18 10 imm)) (SK_lo12 0x151b4 5031%positive 0x2f868).
(* [comment removed for export] *)
Definition cs_15204 : csite := mkSite 0x15204 1017%positive OP_AUIPC (SH20 (fun imm => Auipc 12 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_15208 : csite := mkSite 0x15208 1017%positive OP_STORE (SH12 (fun imm => Store SZ8 12 11 imm)) (SK_lo12 0x15204 5031%positive 0x2f8d0).
(* [comment removed for export] *)
Definition cs_15210 : csite := mkSite 0x15210 1017%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_15214 : csite := mkSite 0x15214 1017%positive OP_STORE (SH12 (fun imm => Store SZ8 11 10 imm)) (SK_lo12 0x15210 5031%positive 0x2f850).
(* [comment removed for export] *)
Definition cs_1521c : csite := mkSite 0x1521c 1017%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_15220 : csite := mkSite 0x15220 1017%positive OP_STORE (SH12 (fun imm => Store SZ8 10 0 imm)) (SK_lo12 0x1521c 5031%positive 0x2f8d0).
(* [comment removed for export] *)
Definition cs_15238 : csite := mkSite 0x15238 1017%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_1523c : csite := mkSite 0x1523c 1017%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 8 10 imm)) (SK_lo12 0x15238 4004%positive 0x1045d).
(* [comment removed for export] *)
Definition cs_15240 : csite := mkSite 0x15240 1017%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_15244 : csite := mkSite 0x15244 1017%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 11 10 imm)) (SK_lo12 0x15240 5027%positive 0x1e3c0).
(* [comment removed for export] *)
Definition cs_15248 : csite := mkSite 0x15248 1017%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_1524c : csite := mkSite 0x1524c 1017%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x15248 5027%positive 0x1e3c8).
(* [comment removed for export] *)
Definition cs_1527c : csite := mkSite 0x1527c 1017%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1021%positive 0x15490).
(* [comment removed for export] *)
Definition cs_15284 : csite := mkSite 0x15284 1017%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1029%positive 0x15958).
(* [comment removed for export] *)
Definition cs_152f8 : csite := mkSite 0x152f8 1017%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_15304 : csite := mkSite 0x15304 1017%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 10 imm)) (SK_lo12 0x152f8 4017%positive 0x10a6d).
(* [comment removed for export] *)
Definition cs_15328 : csite := mkSite 0x15328 1017%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_15334 : csite := mkSite 0x15334 1017%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 10 imm)) (SK_lo12 0x15328 4017%positive 0x10a6d).
(* [comment removed for export] *)
Definition cs_15358 : csite := mkSite 0x15358 1017%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_15364 : csite := mkSite 0x15364 1017%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 10 imm)) (SK_lo12 0x15358 4017%positive 0x10a6d).
(* [comment removed for export] *)
Definition cs_153ac : csite := mkSite 0x153ac 1018%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1016%positive 0x1516c).
(* [comment removed for export] *)
Definition cs_153b0 : csite := mkSite 0x153b0 1018%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_153b4 : csite := mkSite 0x153b4 1018%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_153b8 : csite := mkSite 0x153b8 1018%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 8 10 imm)) (SK_lo12 0x153b0 5027%positive 0x1e3d0).
(* [comment removed for export] *)
Definition cs_153bc : csite := mkSite 0x153bc 1018%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 9 11 imm)) (SK_lo12 0x153b4 5027%positive 0x1e3d8).
(* [comment removed for export] *)
Definition cs_15418 : csite := mkSite 0x15418 1019%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1017%positive 0x15170).
(* [comment removed for export] *)
Definition cs_1541c : csite := mkSite 0x1541c 1019%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_15420 : csite := mkSite 0x15420 1019%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 6 10 imm)) (SK_lo12 0x1541c 1020%positive 0x15448).
(* [comment removed for export] *)
Definition cs_15478 : csite := mkSite 0x15478 1020%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1018%positive 0x1539c).
(* [comment removed for export] *)
Definition cs_1548c : csite := mkSite 0x1548c 1020%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1027%positive 0x15800).
Definition cs_154b4 : csite := mkSite 0x154b4 1021%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
Definition cs_154b8 : csite := mkSite 0x154b8 1021%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x154b4 5036%positive 0x2f6b8).
Definition cs_154bc : csite := mkSite 0x154bc 1021%positive OP_AUIPC (SH20 (fun imm => Auipc 12 imm)) SK_auipc.
Definition cs_154c0 : csite := mkSite 0x154c0 1021%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 9 12 imm)) (SK_lo12 0x154bc 5031%positive 0x2f868).
Definition cs_154d0 : csite := mkSite 0x154d0 1021%positive OP_AUIPC (SH20 (fun imm => Auipc 14 imm)) SK_auipc.
Definition cs_154e0 : csite := mkSite 0x154e0 1021%positive OP_AUIPC (SH20 (fun imm => Auipc 5 imm)) SK_auipc.
Definition cs_154e4 : csite := mkSite 0x154e4 1021%positive OP_LOAD (SH12 (fun imm => Load SZ4 false 30 14 imm)) (SK_lo12 0x154d0 5019%positive 0x1f620).
Definition cs_154e8 : csite := mkSite 0x154e8 1021%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 5 5 imm)) (SK_lo12 0x154e0 5012%positive 0x1e368).
Definition cs_15630 : csite := mkSite 0x15630 1021%positive OP_AUIPC (SH20 (fun imm => Auipc 13 imm)) SK_auipc.
Definition cs_15644 : csite := mkSite 0x15644 1021%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 13 imm)) (SK_lo12 0x15630 5029%positive 0x2f6f0).
Definition cs_156c0 : csite := mkSite 0x156c0 1021%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1098%positive 0x1d2a8).
Definition cs_156d8 : csite := mkSite 0x156d8 1021%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
Definition cs_156e4 : csite := mkSite 0x156e4 1021%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 11 imm)) (SK_lo12 0x156d8 5036%positive 0x2f6b8).
Definition cs_15700 : csite := mkSite 0x15700 1021%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
Definition cs_15704 : csite := mkSite 0x15704 1021%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x15700 5031%positive 0x2f850).
(* [comment removed for export] *)
Definition cs_15768 : csite := mkSite 0x15768 1023%positive OP_AUIPC (SH20 (fun imm => Auipc 12 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_15774 : csite := mkSite 0x15774 1023%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 12 12 imm)) (SK_lo12 0x15768 5000%positive 0x112ac).
(* [comment removed for export] *)
Definition cs_15784 : csite := mkSite 0x15784 1023%positive OP_AUIPC (SH20 (fun imm => Auipc 12 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_15788 : csite := mkSite 0x15788 1023%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 12 12 imm)) (SK_lo12 0x15784 5000%positive 0x10b04).
(* [comment removed for export] *)
Definition cs_15790 : csite := mkSite 0x15790 1023%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1033%positive 0x159fc).
(* [comment removed for export] *)
Definition cs_157c4 : csite := mkSite 0x157c4 1026%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_157c8 : csite := mkSite 0x157c8 1026%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_157cc : csite := mkSite 0x157cc 1026%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x157c4 5027%positive 0x1e3e8).
(* [comment removed for export] *)
Definition cs_157d0 : csite := mkSite 0x157d0 1026%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 8 11 imm)) (SK_lo12 0x157c8 5027%positive 0x1e3f0).
(* [comment removed for export] *)
Definition cs_157fc : csite := mkSite 0x157fc 1026%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1025%positive 0x157b0).
(* [comment removed for export] *)
Definition cs_15818 : csite := mkSite 0x15818 1027%positive OP_AUIPC (SH20 (fun imm => Auipc 13 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_1581c : csite := mkSite 0x1581c 1027%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 13 13 imm)) (SK_lo12 0x15818 5030%positive 0x2f840).
(* [comment removed for export] *)
Definition cs_15860 : csite := mkSite 0x15860 1027%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1900%positive 0x157b0).   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition cs_15864 : csite := mkSite 0x15864 1027%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1026%positive 0x157b4).
(* [comment removed for export] *)
Definition cs_15868 : csite := mkSite 0x15868 1027%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1052%positive 0x1771c).
(* [comment removed for export] *)
Definition cs_15870 : csite := mkSite 0x15870 1027%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1024%positive 0x15794).
(* [comment removed for export] *)
Definition cs_15894 : csite := mkSite 0x15894 1028%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_15898 : csite := mkSite 0x15898 1028%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 9 10 imm)) (SK_lo12 0x15894 5027%positive 0x1e3e0).
(* [comment removed for export] *)
Definition cs_158f0 : csite := mkSite 0x158f0 1028%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1097%positive 0x1d2a4).
(* [comment removed for export] *)
Definition cs_1592c : csite := mkSite 0x1592c 1028%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1031%positive 0x159c0).
(* [comment removed for export] *)
Definition cs_15954 : csite := mkSite 0x15954 1028%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1030%positive 0x159b8).
(* [comment removed for export] *)
Definition cs_15968 : csite := mkSite 0x15968 1029%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_1596c : csite := mkSite 0x1596c 1029%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x15968 5027%positive 0x1e3e0).
(* [comment removed for export] *)
Definition cs_15974 : csite := mkSite 0x15974 1029%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1090%positive 0x1c9b4).
(* [comment removed for export] *)
Definition cs_1597c : csite := mkSite 0x1597c 1029%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_15980 : csite := mkSite 0x15980 1029%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x1597c 5027%positive 0x1e3e0).
(* [comment removed for export] *)
Definition cs_15994 : csite := mkSite 0x15994 1029%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_15998 : csite := mkSite 0x15998 1029%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x15994 5027%positive 0x1e3e0).
(* [comment removed for export] *)
Definition cs_159dc : csite := mkSite 0x159dc 1031%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1022%positive 0x1574c).
(* [comment removed for export] *)
Definition cs_159fc : csite := mkSite 0x159fc 1033%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1032%positive 0x159f8).
(* [comment removed for export] *)
Definition cs_15a1c : csite := mkSite 0x15a1c 1034%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1022%positive 0x1574c).
(* [comment removed for export] *)
Definition cs_15a4c : csite := mkSite 0x15a4c 1034%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1036%positive 0x15b3c).
(* [comment removed for export] *)
Definition cs_15a58 : csite := mkSite 0x15a58 1034%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_15a5c : csite := mkSite 0x15a5c 1034%positive OP_LOAD (SH12 (fun imm => Load SZ4 true 10 10 imm)) (SK_lo12 0x15a58 5031%positive 0x2fc80).
(* [comment removed for export] *)
Definition cs_15a84 : csite := mkSite 0x15a84 1034%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1091%positive 0x1cdb8).
(* [comment removed for export] *)
Definition cs_15aa0 : csite := mkSite 0x15aa0 1034%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1091%positive 0x1cdb8).
(* [comment removed for export] *)
Definition cs_15ae0 : csite := mkSite 0x15ae0 1034%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1091%positive 0x1cdb8).
(* [comment removed for export] *)
Definition cs_15b0c : csite := mkSite 0x15b0c 1034%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1091%positive 0x1cdb8).
(* [comment removed for export] *)
Definition cs_15b2c : csite := mkSite 0x15b2c 1034%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1044%positive 0x17230).
(* [comment removed for export] *)
Definition cs_15b38 : csite := mkSite 0x15b38 1035%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1037%positive 0x15b40).
(* [comment removed for export] *)
Definition cs_15b3c : csite := mkSite 0x15b3c 1036%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1041%positive 0x164cc).
(* [comment removed for export] *)
Definition cs_15b60 : csite := mkSite 0x15b60 1037%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1038%positive 0x15d0c).
(* [comment removed for export] *)
Definition cs_15b94 : csite := mkSite 0x15b94 1037%positive OP_AUIPC (SH20 (fun imm => Auipc 14 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_15b9c : csite := mkSite 0x15b9c 1037%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 14 14 imm)) (SK_lo12 0x15b94 5020%positive 0x113d4).
(* [comment removed for export] *)
Definition cs_15c40 : csite := mkSite 0x15c40 1037%positive OP_AUIPC (SH20 (fun imm => Auipc 14 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_15c5c : csite := mkSite 0x15c5c 1037%positive OP_LOAD (SH12 (fun imm => Load SZ1 false 17 14 imm)) (SK_lo12 0x15c40 5031%positive 0x2f86b).
(* [comment removed for export] *)
Definition cs_15c94 : csite := mkSite 0x15c94 1037%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_15c98 : csite := mkSite 0x15c98 1037%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x15c94 5031%positive 0x2f8d8).
(* [comment removed for export] *)
Definition cs_15ca4 : csite := mkSite 0x15ca4 1037%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1094%positive 0x1cf84).
(* [comment removed for export] *)
Definition cs_15cb0 : csite := mkSite 0x15cb0 1037%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1039%positive 0x15e1c).
(* [comment removed for export] *)
Definition cs_15cbc : csite := mkSite 0x15cbc 1037%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_15cc0 : csite := mkSite 0x15cc0 1037%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x15cbc 5031%positive 0x2f8d8).
(* [comment removed for export] *)
Definition cs_15cc4 : csite := mkSite 0x15cc4 1037%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1095%positive 0x1d20c).
(* [comment removed for export] *)
Definition cs_15ccc : csite := mkSite 0x15ccc 1037%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1022%positive 0x1574c).
(* [comment removed for export] *)
Definition cs_15ce0 : csite := mkSite 0x15ce0 1037%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1049%positive 0x17578).
(* [comment removed for export] *)
Definition cs_15d9c : csite := mkSite 0x15d9c 1038%positive OP_AUIPC (SH20 (fun imm => Auipc 15 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_15da8 : csite := mkSite 0x15da8 1038%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 15 15 imm)) (SK_lo12 0x15d9c 5031%positive 0x2f8e0).
(* [comment removed for export] *)
Definition cs_15dc8 : csite := mkSite 0x15dc8 1038%positive OP_AUIPC (SH20 (fun imm => Auipc 15 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_15dcc : csite := mkSite 0x15dcc 1038%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 15 15 imm)) (SK_lo12 0x15dc8 5020%positive 0x113d4).
(* [comment removed for export] *)
Definition cs_15e34 : csite := mkSite 0x15e34 1039%positive OP_AUIPC (SH20 (fun imm => Auipc 12 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_15e38 : csite := mkSite 0x15e38 1039%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 9 12 imm)) (SK_lo12 0x15e34 5027%positive 0x1e3e0).
(* [comment removed for export] *)
Definition cs_15e84 : csite := mkSite 0x15e84 1039%positive OP_AUIPC (SH20 (fun imm => Auipc 16 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_15e88 : csite := mkSite 0x15e88 1039%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 18 16 imm)) (SK_lo12 0x15e84 5031%positive 0x2f8e0).
(* [comment removed for export] *)
Definition cs_15e98 : csite := mkSite 0x15e98 1039%positive OP_AUIPC (SH20 (fun imm => Auipc 16 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_15e9c : csite := mkSite 0x15e9c 1039%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 16 16 imm)) (SK_lo12 0x15e98 5020%positive 0x113d4).
(* [comment removed for export] *)
Definition cs_15f90 : csite := mkSite 0x15f90 1039%positive OP_AUIPC (SH20 (fun imm => Auipc 13 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_15f94 : csite := mkSite 0x15f94 1039%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 13 13 imm)) (SK_lo12 0x15f90 5031%positive 0x2f8e0).
(* [comment removed for export] *)
Definition cs_1608c : csite := mkSite 0x1608c 1039%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1038%positive 0x15d0c).
(* [comment removed for export] *)
Definition cs_161f0 : csite := mkSite 0x161f0 1039%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1030%positive 0x159b8).
(* [comment removed for export] *)
Definition cs_16210 : csite := mkSite 0x16210 1040%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_16214 : csite := mkSite 0x16214 1040%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 18 10 imm)) (SK_lo12 0x16210 5027%positive 0x1e3e0).
(* [comment removed for export] *)
Definition cs_1621c : csite := mkSite 0x1621c 1040%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_16224 : csite := mkSite 0x16224 1040%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 19 11 imm)) (SK_lo12 0x1621c 5031%positive 0x2f8d8).
(* [comment removed for export] *)
Definition cs_1622c : csite := mkSite 0x1622c 1040%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_16230 : csite := mkSite 0x16230 1040%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 8 11 imm)) (SK_lo12 0x1622c 5031%positive 0x2f868).
(* [comment removed for export] *)
Definition cs_1626c : csite := mkSite 0x1626c 1040%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1090%positive 0x1c9b4).
(* [comment removed for export] *)
Definition cs_1637c : csite := mkSite 0x1637c 1040%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1047%positive 0x17444).
(* [comment removed for export] *)
Definition cs_163d4 : csite := mkSite 0x163d4 1040%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1047%positive 0x17444).
(* [comment removed for export] *)
Definition cs_164a8 : csite := mkSite 0x164a8 1040%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1048%positive 0x17530).
(* [comment removed for export] *)
Definition cs_164b0 : csite := mkSite 0x164b0 1040%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1022%positive 0x1574c).
(* [comment removed for export] *)
Definition cs_164c8 : csite := mkSite 0x164c8 1040%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1030%positive 0x159b8).
(* [comment removed for export] *)
Definition cs_164f8 : csite := mkSite 0x164f8 1041%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1022%positive 0x1574c).
(* [comment removed for export] *)
Definition cs_16534 : csite := mkSite 0x16534 1041%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_16538 : csite := mkSite 0x16538 1041%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 9 11 imm)) (SK_lo12 0x16534 5031%positive 0x2f8d8).
(* [comment removed for export] *)
Definition cs_16560 : csite := mkSite 0x16560 1041%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1047%positive 0x17444).
(* [comment removed for export] *)
Definition cs_1656c : csite := mkSite 0x1656c 1041%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_16570 : csite := mkSite 0x16570 1041%positive OP_LOAD (SH12 (fun imm => Load SZ1 false 10 10 imm)) (SK_lo12 0x1656c 5031%positive 0x2f86b).
(* [comment removed for export] *)
Definition cs_16578 : csite := mkSite 0x16578 1041%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_1657c : csite := mkSite 0x1657c 1041%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x16578 5031%positive 0x2f8d8).
(* [comment removed for export] *)
Definition cs_16580 : csite := mkSite 0x16580 1041%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1094%positive 0x1cf84).
(* [comment removed for export] *)
Definition cs_165b0 : csite := mkSite 0x165b0 1041%positive OP_AUIPC (SH20 (fun imm => Auipc 12 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_165b8 : csite := mkSite 0x165b8 1041%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 19 12 imm)) (SK_lo12 0x165b0 5001%positive 0x113b4).
(* [comment removed for export] *)
Definition cs_16620 : csite := mkSite 0x16620 1041%positive OP_AUIPC (SH20 (fun imm => Auipc 12 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_16634 : csite := mkSite 0x16634 1041%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 12 imm)) (SK_lo12 0x16620 5020%positive 0x113d4).
(* [comment removed for export] *)
Definition cs_16654 : csite := mkSite 0x16654 1041%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1040%positive 0x161f4).
(* [comment removed for export] *)
Definition cs_166c0 : csite := mkSite 0x166c0 1041%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_166c4 : csite := mkSite 0x166c4 1041%positive OP_LOAD (SH12 (fun imm => Load SZ1 false 10 10 imm)) (SK_lo12 0x166c0 5031%positive 0x2f86b).
(* [comment removed for export] *)
Definition cs_166cc : csite := mkSite 0x166cc 1041%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_166d0 : csite := mkSite 0x166d0 1041%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x166cc 5031%positive 0x2f8d8).
(* [comment removed for export] *)
Definition cs_166d4 : csite := mkSite 0x166d4 1041%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1094%positive 0x1cf84).
(* [comment removed for export] *)
Definition cs_16718 : csite := mkSite 0x16718 1041%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_1671c : csite := mkSite 0x1671c 1041%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x16718 5031%positive 0x2f8d8).
(* [comment removed for export] *)
Definition cs_16720 : csite := mkSite 0x16720 1041%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1095%positive 0x1d20c).
(* [comment removed for export] *)
Definition cs_1672c : csite := mkSite 0x1672c 1041%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1049%positive 0x17578).
(* [comment removed for export] *)
Definition cs_167d8 : csite := mkSite 0x167d8 1041%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1042%positive 0x1683c).
(* [comment removed for export] *)
Definition cs_167f8 : csite := mkSite 0x167f8 1041%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1095%positive 0x1d20c).
(* [comment removed for export] *)
Definition cs_16828 : csite := mkSite 0x16828 1041%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1043%positive 0x170e0).
(* [comment removed for export] *)
Definition cs_1682c : csite := mkSite 0x1682c 1041%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_16830 : csite := mkSite 0x16830 1041%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x1682c 5031%positive 0x2f8d8).
(* [comment removed for export] *)
Definition cs_16834 : csite := mkSite 0x16834 1041%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1095%positive 0x1d20c).
(* [comment removed for export] *)
Definition cs_16874 : csite := mkSite 0x16874 1042%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_16878 : csite := mkSite 0x16878 1042%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 20 10 imm)) (SK_lo12 0x16874 5027%positive 0x1e3e0).
(* [comment removed for export] *)
Definition cs_16884 : csite := mkSite 0x16884 1042%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_16888 : csite := mkSite 0x16888 1042%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 22 11 imm)) (SK_lo12 0x16884 5031%positive 0x2f8d8).
(* [comment removed for export] *)
Definition cs_16a04 : csite := mkSite 0x16a04 1042%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_16a0c : csite := mkSite 0x16a0c 1042%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x16a04 5001%positive 0x113b4).
(* [comment removed for export] *)
Definition cs_16a20 : csite := mkSite 0x16a20 1042%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_16a24 : csite := mkSite 0x16a24 1042%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 25 10 imm)) (SK_lo12 0x16a20 5020%positive 0x113d4).
(* [comment removed for export] *)
Definition cs_16a30 : csite := mkSite 0x16a30 1042%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1040%positive 0x161f4).
(* [comment removed for export] *)
Definition cs_16a44 : csite := mkSite 0x16a44 1042%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_16a48 : csite := mkSite 0x16a48 1042%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 11 11 imm)) (SK_lo12 0x16a44 5031%positive 0x2f898).
(* [comment removed for export] *)
Definition cs_16a5c : csite := mkSite 0x16a5c 1042%positive OP_AUIPC (SH20 (fun imm => Auipc 13 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_16a60 : csite := mkSite 0x16a60 1042%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 13 13 imm)) (SK_lo12 0x16a5c 5020%positive 0x11434).
(* [comment removed for export] *)
Definition cs_16a8c : csite := mkSite 0x16a8c 1042%positive OP_AUIPC (SH20 (fun imm => Auipc 13 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_16a90 : csite := mkSite 0x16a90 1042%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 13 13 imm)) (SK_lo12 0x16a8c 5002%positive 0x1144f).
(* [comment removed for export] *)
Definition cs_16ba4 : csite := mkSite 0x16ba4 1042%positive OP_AUIPC (SH20 (fun imm => Auipc 13 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_16bac : csite := mkSite 0x16bac 1042%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 13 13 imm)) (SK_lo12 0x16ba4 5001%positive 0x113b4).
(* [comment removed for export] *)
Definition cs_16c48 : csite := mkSite 0x16c48 1042%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1043%positive 0x170e0).
(* [comment removed for export] *)
Definition cs_16d18 : csite := mkSite 0x16d18 1042%positive OP_AUIPC (SH20 (fun imm => Auipc 14 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_16d20 : csite := mkSite 0x16d20 1042%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 14 14 imm)) (SK_lo12 0x16d18 5020%positive 0x113d4).
(* [comment removed for export] *)
Definition cs_16ee8 : csite := mkSite 0x16ee8 1042%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1047%positive 0x17444).
(* [comment removed for export] *)
Definition cs_170dc : csite := mkSite 0x170dc 1042%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1030%positive 0x159b8).
(* [comment removed for export] *)
Definition cs_17108 : csite := mkSite 0x17108 1043%positive OP_AUIPC (SH20 (fun imm => Auipc 15 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_17110 : csite := mkSite 0x17110 1043%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 15 15 imm)) (SK_lo12 0x17108 5020%positive 0x113d4).
(* [comment removed for export] *)
Definition cs_172c4 : csite := mkSite 0x172c4 1044%positive OP_AUIPC (SH20 (fun imm => Auipc 15 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_172cc : csite := mkSite 0x172cc 1044%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 15 15 imm)) (SK_lo12 0x172c4 5031%positive 0x2f8e0).
(* [comment removed for export] *)
Definition cs_172ec : csite := mkSite 0x172ec 1044%positive OP_AUIPC (SH20 (fun imm => Auipc 16 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_172f0 : csite := mkSite 0x172f0 1044%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 16 16 imm)) (SK_lo12 0x172ec 5020%positive 0x113d4).
(* [comment removed for export] *)
Definition cs_17360 : csite := mkSite 0x17360 1044%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_17364 : csite := mkSite 0x17364 1044%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x17360 5020%positive 0x113d4).
(* [comment removed for export] *)
Definition cs_1738c : csite := mkSite 0x1738c 1044%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_17390 : csite := mkSite 0x17390 1044%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x1738c 5020%positive 0x113d4).
(* [comment removed for export] *)
Definition cs_173b0 : csite := mkSite 0x173b0 1045%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_173b4 : csite := mkSite 0x173b4 1045%positive OP_FLOAD (SH12 (fun imm => FLoad FMT_D 15 11 imm)) (SK_lo12 0x173b0 5006%positive 0x11480).
(* [comment removed for export] *)
Definition cs_173e8 : csite := mkSite 0x173e8 1045%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_173ec : csite := mkSite 0x173ec 1045%positive OP_FLOAD (SH12 (fun imm => FLoad FMT_D 15 11 imm)) (SK_lo12 0x173e8 5025%positive 0x11498).
(* [comment removed for export] *)
Definition cs_1746c : csite := mkSite 0x1746c 1047%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1022%positive 0x1574c).
(* [comment removed for export] *)
Definition cs_17484 : csite := mkSite 0x17484 1047%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1022%positive 0x1574c).
(* [comment removed for export] *)
Definition cs_174e0 : csite := mkSite 0x174e0 1047%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1046%positive 0x17440).
(* [comment removed for export] *)
Definition cs_17528 : csite := mkSite 0x17528 1047%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1031%positive 0x159c0).
(* [comment removed for export] *)
Definition cs_17538 : csite := mkSite 0x17538 1048%positive OP_AUIPC (SH20 (fun imm => Auipc 13 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_1753c : csite := mkSite 0x1753c 1048%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 13 13 imm)) (SK_lo12 0x17538 5031%positive 0x2f898).
(* [comment removed for export] *)
Definition cs_17564 : csite := mkSite 0x17564 1048%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1031%positive 0x159c0).
(* [comment removed for export] *)
Definition cs_17590 : csite := mkSite 0x17590 1049%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1046%positive 0x17440).
(* [comment removed for export] *)
Definition cs_175a4 : csite := mkSite 0x175a4 1049%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1031%positive 0x159c0).
(* [comment removed for export] *)
Definition cs_17728 : csite := mkSite 0x17728 1052%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1062%positive 0x17d8c).
(* [comment removed for export] *)
Definition cs_17734 : csite := mkSite 0x17734 1052%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_17738 : csite := mkSite 0x17738 1052%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 8 10 imm)) (SK_lo12 0x17734 5032%positive 0x2fc88).
(* [comment removed for export] *)
Definition cs_1774c : csite := mkSite 0x1774c 1052%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1050%positive 0x175c0).
(* [comment removed for export] *)
Definition cs_17790 : csite := mkSite 0x17790 1052%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_17794 : csite := mkSite 0x17794 1052%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 8 10 imm)) (SK_lo12 0x17790 5019%positive 0x1f618).
(* [comment removed for export] *)
Definition cs_177a8 : csite := mkSite 0x177a8 1052%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1050%positive 0x175c0).
(* [comment removed for export] *)
Definition cs_177ec : csite := mkSite 0x177ec 1052%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_177f0 : csite := mkSite 0x177f0 1052%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 8 10 imm)) (SK_lo12 0x177ec 5019%positive 0x1f528).
(* [comment removed for export] *)
Definition cs_17804 : csite := mkSite 0x17804 1052%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1050%positive 0x175c0).
(* [comment removed for export] *)
Definition cs_17868 : csite := mkSite 0x17868 1052%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1050%positive 0x175c0).
(* [comment removed for export] *)
Definition cs_178ec : csite := mkSite 0x178ec 1053%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_178f0 : csite := mkSite 0x178f0 1053%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 21 10 imm)) (SK_lo12 0x178ec 5027%positive 0x1e3e0).
(* [comment removed for export] *)
Definition cs_1794c : csite := mkSite 0x1794c 1053%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1031%positive 0x159c0).
(* [comment removed for export] *)
Definition cs_179d4 : csite := mkSite 0x179d4 1053%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1031%positive 0x159c0).
(* [comment removed for export] *)
Definition cs_17a4c : csite := mkSite 0x17a4c 1053%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1030%positive 0x159b8).
(* [comment removed for export] *)
Definition cs_17a54 : csite := mkSite 0x17a54 1054%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1100%positive 0x1d308).
(* [comment removed for export] *)
Definition cs_17a68 : csite := mkSite 0x17a68 1056%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1055%positive 0x17a58).
(* [comment removed for export] *)
Definition cs_17a74 : csite := mkSite 0x17a74 1056%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1031%positive 0x159c0).
(* [comment removed for export] *)
Definition cs_17a9c : csite := mkSite 0x17a9c 1057%positive OP_AUIPC (SH20 (fun imm => Auipc 16 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_17aa0 : csite := mkSite 0x17aa0 1057%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 8 16 imm)) (SK_lo12 0x17a9c 5027%positive 0x1e3e0).
(* [comment removed for export] *)
Definition cs_17ac8 : csite := mkSite 0x17ac8 1057%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1063%positive 0x17dbc).
(* [comment removed for export] *)
Definition cs_17ae8 : csite := mkSite 0x17ae8 1057%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1030%positive 0x159b8).
(* [comment removed for export] *)
Definition cs_17b5c : csite := mkSite 0x17b5c 1059%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1092%positive 0x1ceb0).
(* [comment removed for export] *)
Definition cs_17b74 : csite := mkSite 0x17b74 1059%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1061%positive 0x17cd4).
(* [comment removed for export] *)
Definition cs_17c54 : csite := mkSite 0x17c54 1060%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1058%positive 0x17aec).
(* [comment removed for export] *)
Definition cs_17c9c : csite := mkSite 0x17c9c 1060%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1090%positive 0x1c9b4).
(* [comment removed for export] *)
Definition cs_17d14 : csite := mkSite 0x17d14 1061%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1050%positive 0x175c0).
(* [comment removed for export] *)
Definition cs_17d28 : csite := mkSite 0x17d28 1061%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1060%positive 0x17b9c).
(* [comment removed for export] *)
Definition cs_17d38 : csite := mkSite 0x17d38 1061%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1051%positive 0x176bc).
(* [comment removed for export] *)
Definition cs_17d58 : csite := mkSite 0x17d58 1061%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1060%positive 0x17b9c).
(* [comment removed for export] *)
Definition cs_17d98 : csite := mkSite 0x17d98 1062%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_17d9c : csite := mkSite 0x17d9c 1062%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 8 10 imm)) (SK_lo12 0x17d98 5032%positive 0x2fc90).
(* [comment removed for export] *)
Definition cs_17da4 : csite := mkSite 0x17da4 1062%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1094%positive 0x1cf84).
(* [comment removed for export] *)
Definition cs_17de4 : csite := mkSite 0x17de4 1063%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_17de8 : csite := mkSite 0x17de8 1063%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 18 10 imm)) (SK_lo12 0x17de4 5027%positive 0x1e3e0).
(* [comment removed for export] *)
Definition cs_17e20 : csite := mkSite 0x17e20 1063%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1064%positive 0x17f6c).
(* [comment removed for export] *)
Definition cs_17e34 : csite := mkSite 0x17e34 1063%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1050%positive 0x175c0).
(* [comment removed for export] *)
Definition cs_17e94 : csite := mkSite 0x17e94 1063%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1058%positive 0x17aec).
(* [comment removed for export] *)
Definition cs_17ec0 : csite := mkSite 0x17ec0 1063%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1064%positive 0x17f6c).
(* [comment removed for export] *)
Definition cs_17f30 : csite := mkSite 0x17f30 1063%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1051%positive 0x176bc).
(* [comment removed for export] *)
Definition cs_17f68 : csite := mkSite 0x17f68 1063%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1030%positive 0x159b8).
(* [comment removed for export] *)
Definition cs_17fc4 : csite := mkSite 0x17fc4 1064%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_17fd0 : csite := mkSite 0x17fd0 1064%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 12 10 imm)) (SK_lo12 0x17fc4 5027%positive 0x1e3e0).
(* [comment removed for export] *)
Definition cs_180b0 : csite := mkSite 0x180b0 1064%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1060%positive 0x17b9c).
(* [comment removed for export] *)
Definition cs_183d0 : csite := mkSite 0x183d0 1064%positive OP_AUIPC (SH20 (fun imm => Auipc 13 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_183d4 : csite := mkSite 0x183d4 1064%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 13 13 imm)) (SK_lo12 0x183d0 5008%positive 0x115f0).
(* [comment removed for export] *)
Definition cs_18444 : csite := mkSite 0x18444 1064%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1065%positive 0x18d9c).
(* [comment removed for export] *)
Definition cs_1849c : csite := mkSite 0x1849c 1064%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_184a0 : csite := mkSite 0x184a0 1064%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x1849c 5008%positive 0x114a8).
(* [comment removed for export] *)
Definition cs_184dc : csite := mkSite 0x184dc 1064%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1067%positive 0x18fa4).
(* [comment removed for export] *)
Definition cs_1850c : csite := mkSite 0x1850c 1064%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_18514 : csite := mkSite 0x18514 1064%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x1850c 4000%positive 0x102e7).
(* [comment removed for export] *)
Definition cs_18538 : csite := mkSite 0x18538 1064%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_1853c : csite := mkSite 0x1853c 1064%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x18538 4000%positive 0x102e7).
(* [comment removed for export] *)
Definition cs_18554 : csite := mkSite 0x18554 1064%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_18558 : csite := mkSite 0x18558 1064%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 23 10 imm)) (SK_lo12 0x18554 4018%positive 0x10a77).
(* [comment removed for export] *)
Definition cs_18560 : csite := mkSite 0x18560 1064%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1022%positive 0x1574c).
(* [comment removed for export] *)
Definition cs_18568 : csite := mkSite 0x18568 1064%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1023%positive 0x15758).
(* [comment removed for export] *)
Definition cs_18580 : csite := mkSite 0x18580 1064%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1093%positive 0x1cf40).
(* [comment removed for export] *)
Definition cs_18598 : csite := mkSite 0x18598 1064%positive OP_AUIPC (SH20 (fun imm => Auipc 12 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_1859c : csite := mkSite 0x1859c 1064%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 12 12 imm)) (SK_lo12 0x18598 4000%positive 0x102e7).
(* [comment removed for export] *)
Definition cs_185dc : csite := mkSite 0x185dc 1064%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_185e0 : csite := mkSite 0x185e0 1064%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x185dc 4000%positive 0x102e7).
(* [comment removed for export] *)
Definition cs_18614 : csite := mkSite 0x18614 1064%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_18618 : csite := mkSite 0x18618 1064%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x18614 5008%positive 0x11588).
(* [comment removed for export] *)
Definition cs_18644 : csite := mkSite 0x18644 1064%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_18648 : csite := mkSite 0x18648 1064%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 17 11 imm)) (SK_lo12 0x18644 4000%positive 0x102e7).
(* [comment removed for export] *)
Definition cs_18680 : csite := mkSite 0x18680 1064%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_18684 : csite := mkSite 0x18684 1064%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x18680 4000%positive 0x102e7).
(* [comment removed for export] *)
Definition cs_186b8 : csite := mkSite 0x186b8 1064%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_186bc : csite := mkSite 0x186bc 1064%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 14 11 imm)) (SK_lo12 0x186b8 4000%positive 0x102e7).
(* [comment removed for export] *)
Definition cs_186d0 : csite := mkSite 0x186d0 1064%positive OP_AUIPC (SH20 (fun imm => Auipc 13 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_186d4 : csite := mkSite 0x186d4 1064%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 13 13 imm)) (SK_lo12 0x186d0 5009%positive 0x117c0).
(* [comment removed for export] *)
Definition cs_18734 : csite := mkSite 0x18734 1064%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1068%positive 0x1a66c).
(* [comment removed for export] *)
Definition cs_1876c : csite := mkSite 0x1876c 1064%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1066%positive 0x18ed0).
(* [comment removed for export] *)
Definition cs_18790 : csite := mkSite 0x18790 1064%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1068%positive 0x1a66c).
(* [comment removed for export] *)
Definition cs_187b4 : csite := mkSite 0x187b4 1064%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1060%positive 0x17b9c).
(* [comment removed for export] *)
Definition cs_187c0 : csite := mkSite 0x187c0 1064%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_187c4 : csite := mkSite 0x187c4 1064%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x187c0 4000%positive 0x102e7).
(* [comment removed for export] *)
Definition cs_187e8 : csite := mkSite 0x187e8 1064%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_187f0 : csite := mkSite 0x187f0 1064%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 17 11 imm)) (SK_lo12 0x187e8 4000%positive 0x102e7).
(* [comment removed for export] *)
Definition cs_18938 : csite := mkSite 0x18938 1064%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1091%positive 0x1cdb8).
(* [comment removed for export] *)
Definition cs_18968 : csite := mkSite 0x18968 1064%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1060%positive 0x17b9c).
(* [comment removed for export] *)
Definition cs_1898c : csite := mkSite 0x1898c 1064%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1060%positive 0x17b9c).
(* [comment removed for export] *)
Definition cs_189a8 : csite := mkSite 0x189a8 1064%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1060%positive 0x17b9c).
(* [comment removed for export] *)
Definition cs_189dc : csite := mkSite 0x189dc 1064%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1091%positive 0x1cdb8).
(* [comment removed for export] *)
Definition cs_18a0c : csite := mkSite 0x18a0c 1064%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1060%positive 0x17b9c).
(* [comment removed for export] *)
Definition cs_18a30 : csite := mkSite 0x18a30 1064%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1060%positive 0x17b9c).
(* [comment removed for export] *)
Definition cs_18a60 : csite := mkSite 0x18a60 1064%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1091%positive 0x1cdb8).
(* [comment removed for export] *)
Definition cs_18a90 : csite := mkSite 0x18a90 1064%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1060%positive 0x17b9c).
(* [comment removed for export] *)
Definition cs_18ab4 : csite := mkSite 0x18ab4 1064%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1060%positive 0x17b9c).
(* [comment removed for export] *)
Definition cs_18ad0 : csite := mkSite 0x18ad0 1064%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1060%positive 0x17b9c).
(* [comment removed for export] *)
Definition cs_18b04 : csite := mkSite 0x18b04 1064%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1091%positive 0x1cdb8).
(* [comment removed for export] *)
Definition cs_18b34 : csite := mkSite 0x18b34 1064%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1060%positive 0x17b9c).
(* [comment removed for export] *)
Definition cs_18b54 : csite := mkSite 0x18b54 1064%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1060%positive 0x17b9c).
(* [comment removed for export] *)
Definition cs_18b70 : csite := mkSite 0x18b70 1064%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1066%positive 0x18ed0).
(* [comment removed for export] *)
Definition cs_18b94 : csite := mkSite 0x18b94 1064%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1066%positive 0x18ed0).
(* [comment removed for export] *)
Definition cs_18be4 : csite := mkSite 0x18be4 1064%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1022%positive 0x1574c).
(* [comment removed for export] *)
Definition cs_18c18 : csite := mkSite 0x18c18 1064%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1065%positive 0x18d9c).
(* [comment removed for export] *)
Definition cs_18c2c : csite := mkSite 0x18c2c 1064%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1065%positive 0x18d9c).
(* [comment removed for export] *)
Definition cs_18c40 : csite := mkSite 0x18c40 1064%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1065%positive 0x18d9c).
(* [comment removed for export] *)
Definition cs_18c54 : csite := mkSite 0x18c54 1064%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1065%positive 0x18d9c).
(* [comment removed for export] *)
Definition cs_18c68 : csite := mkSite 0x18c68 1064%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1065%positive 0x18d9c).
(* [comment removed for export] *)
Definition cs_18c7c : csite := mkSite 0x18c7c 1064%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1065%positive 0x18d9c).
(* [comment removed for export] *)
Definition cs_18c90 : csite := mkSite 0x18c90 1064%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1065%positive 0x18d9c).
(* [comment removed for export] *)
Definition cs_18ca4 : csite := mkSite 0x18ca4 1064%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1065%positive 0x18d9c).
(* [comment removed for export] *)
Definition cs_18cb8 : csite := mkSite 0x18cb8 1064%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1065%positive 0x18d9c).
(* [comment removed for export] *)
Definition cs_18d38 : csite := mkSite 0x18d38 1064%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1022%positive 0x1574c).
(* [comment removed for export] *)
Definition cs_18d98 : csite := mkSite 0x18d98 1064%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1030%positive 0x159b8).
(* [comment removed for export] *)
Definition cs_18dac : csite := mkSite 0x18dac 1065%positive OP_AUIPC (SH20 (fun imm => Auipc 13 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_18db0 : csite := mkSite 0x18db0 1065%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 13 13 imm)) (SK_lo12 0x18dac 5008%positive 0x115a8).
(* [comment removed for export] *)
Definition cs_18dfc : csite := mkSite 0x18dfc 1065%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1070%positive 0x1a7bc).
(* [comment removed for export] *)
Definition cs_18eec : csite := mkSite 0x18eec 1066%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_18ef0 : csite := mkSite 0x18ef0 1066%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 18 10 imm)) (SK_lo12 0x18eec 5027%positive 0x1e3e0).
(* [comment removed for export] *)
Definition cs_18f24 : csite := mkSite 0x18f24 1066%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1091%positive 0x1cdb8).
(* [comment removed for export] *)
Definition cs_18f54 : csite := mkSite 0x18f54 1066%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1060%positive 0x17b9c).
(* [comment removed for export] *)
Definition cs_18f74 : csite := mkSite 0x18f74 1066%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1060%positive 0x17b9c).
(* [comment removed for export] *)
Definition cs_18fa0 : csite := mkSite 0x18fa0 1066%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1030%positive 0x159b8).
(* [comment removed for export] *)
Definition cs_19000 : csite := mkSite 0x19000 1067%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_19004 : csite := mkSite 0x19004 1067%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 20 10 imm)) (SK_lo12 0x19000 5027%positive 0x1e3e0).
(* [comment removed for export] *)
Definition cs_1905c : csite := mkSite 0x1905c 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1071%positive 0x1a94c).
(* [comment removed for export] *)
Definition cs_19068 : csite := mkSite 0x19068 1067%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_19070 : csite := mkSite 0x19070 1067%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x19068 4001%positive 0x103fc).
(* [comment removed for export] *)
Definition cs_19084 : csite := mkSite 0x19084 1067%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_1908c : csite := mkSite 0x1908c 1067%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x19084 4001%positive 0x103fc).
(* [comment removed for export] *)
Definition cs_190c4 : csite := mkSite 0x190c4 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1072%positive 0x1a954).
(* [comment removed for export] *)
Definition cs_190e0 : csite := mkSite 0x190e0 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1073%positive 0x1a998).
(* [comment removed for export] *)
Definition cs_190f0 : csite := mkSite 0x190f0 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1076%positive 0x1b238).
(* [comment removed for export] *)
Definition cs_19104 : csite := mkSite 0x19104 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1075%positive 0x1ab38).
(* [comment removed for export] *)
Definition cs_19118 : csite := mkSite 0x19118 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1074%positive 0x1aa70).
(* [comment removed for export] *)
Definition cs_19154 : csite := mkSite 0x19154 1067%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_19158 : csite := mkSite 0x19158 1067%positive OP_FLOAD (SH12 (fun imm => FLoad FMT_D 10 10 imm)) (SK_lo12 0x19154 5003%positive 0x11458).
(* [comment removed for export] *)
Definition cs_1915c : csite := mkSite 0x1915c 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1070%positive 0x1a7bc).
(* [comment removed for export] *)
Definition cs_19170 : csite := mkSite 0x19170 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1075%positive 0x1ab38).
(* [comment removed for export] *)
Definition cs_191a0 : csite := mkSite 0x191a0 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1074%positive 0x1aa70).
(* [comment removed for export] *)
Definition cs_191a8 : csite := mkSite 0x191a8 1067%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_191ac : csite := mkSite 0x191ac 1067%positive OP_AUIPC (SH20 (fun imm => Auipc 12 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_191b0 : csite := mkSite 0x191b0 1067%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x191a8 4008%positive 0x10563).
(* [comment removed for export] *)
Definition cs_191b4 : csite := mkSite 0x191b4 1067%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 19 12 imm)) (SK_lo12 0x191ac 4014%positive 0x109b4).
(* [comment removed for export] *)
Definition cs_19210 : csite := mkSite 0x19210 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1045%positive 0x173a8).
(* [comment removed for export] *)
Definition cs_19230 : csite := mkSite 0x19230 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1070%positive 0x1a7bc).
(* [comment removed for export] *)
Definition cs_1924c : csite := mkSite 0x1924c 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1077%positive 0x1b340).
(* [comment removed for export] *)
Definition cs_19258 : csite := mkSite 0x19258 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1078%positive 0x1b350).
(* [comment removed for export] *)
Definition cs_19268 : csite := mkSite 0x19268 1067%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_1926c : csite := mkSite 0x1926c 1067%positive OP_AUIPC (SH20 (fun imm => Auipc 12 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_19270 : csite := mkSite 0x19270 1067%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x19268 4009%positive 0x106e4).
(* [comment removed for export] *)
Definition cs_19274 : csite := mkSite 0x19274 1067%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 19 12 imm)) (SK_lo12 0x1926c 4013%positive 0x1097c).
(* [comment removed for export] *)
Definition cs_192b0 : csite := mkSite 0x192b0 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1091%positive 0x1cdb8).
(* [comment removed for export] *)
Definition cs_192e0 : csite := mkSite 0x192e0 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1060%positive 0x17b9c).
(* [comment removed for export] *)
Definition cs_19300 : csite := mkSite 0x19300 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1060%positive 0x17b9c).
(* [comment removed for export] *)
Definition cs_1931c : csite := mkSite 0x1931c 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1060%positive 0x17b9c).
(* [comment removed for export] *)
Definition cs_19338 : csite := mkSite 0x19338 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1060%positive 0x17b9c).
(* [comment removed for export] *)
Definition cs_1936c : csite := mkSite 0x1936c 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1091%positive 0x1cdb8).
(* [comment removed for export] *)
Definition cs_1939c : csite := mkSite 0x1939c 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1060%positive 0x17b9c).
(* [comment removed for export] *)
Definition cs_193bc : csite := mkSite 0x193bc 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1060%positive 0x17b9c).
(* [comment removed for export] *)
Definition cs_19454 : csite := mkSite 0x19454 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1081%positive 0x1bb58).
(* [comment removed for export] *)
Definition cs_19464 : csite := mkSite 0x19464 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1076%positive 0x1b238).
(* [comment removed for export] *)
Definition cs_19478 : csite := mkSite 0x19478 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1082%positive 0x1bbec).
(* [comment removed for export] *)
Definition cs_1948c : csite := mkSite 0x1948c 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1077%positive 0x1b340).
(* [comment removed for export] *)
Definition cs_194a0 : csite := mkSite 0x194a0 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1075%positive 0x1ab38).
(* [comment removed for export] *)
Definition cs_194b4 : csite := mkSite 0x194b4 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1074%positive 0x1aa70).
(* [comment removed for export] *)
Definition cs_194c0 : csite := mkSite 0x194c0 1067%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_194c4 : csite := mkSite 0x194c4 1067%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 10 10 imm)) (SK_lo12 0x194c0 5024%positive 0x11490).
(* [comment removed for export] *)
Definition cs_1975c : csite := mkSite 0x1975c 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1070%positive 0x1a7bc).
(* [comment removed for export] *)
Definition cs_19778 : csite := mkSite 0x19778 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1078%positive 0x1b350).
(* [comment removed for export] *)
Definition cs_19784 : csite := mkSite 0x19784 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1077%positive 0x1b340).
(* [comment removed for export] *)
Definition cs_19864 : csite := mkSite 0x19864 1067%positive OP_AUIPC (SH20 (fun imm => Auipc 15 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_19880 : csite := mkSite 0x19880 1067%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 18 15 imm)) (SK_lo12 0x19864 5009%positive 0x117c0).
(* [comment removed for export] *)
Definition cs_198a0 : csite := mkSite 0x198a0 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1074%positive 0x1aa70).
(* [comment removed for export] *)
Definition cs_198b4 : csite := mkSite 0x198b4 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1083%positive 0x1bcd8).
(* [comment removed for export] *)
Definition cs_198d4 : csite := mkSite 0x198d4 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1076%positive 0x1b238).
(* [comment removed for export] *)
Definition cs_198e4 : csite := mkSite 0x198e4 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1076%positive 0x1b238).
(* [comment removed for export] *)
Definition cs_198f8 : csite := mkSite 0x198f8 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1077%positive 0x1b340).
(* [comment removed for export] *)
Definition cs_1990c : csite := mkSite 0x1990c 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1075%positive 0x1ab38).
(* [comment removed for export] *)
Definition cs_19934 : csite := mkSite 0x19934 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1074%positive 0x1aa70).
(* [comment removed for export] *)
Definition cs_199f4 : csite := mkSite 0x199f4 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1091%positive 0x1cdb8).
(* [comment removed for export] *)
Definition cs_19a24 : csite := mkSite 0x19a24 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1060%positive 0x17b9c).
(* [comment removed for export] *)
Definition cs_19a68 : csite := mkSite 0x19a68 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1076%positive 0x1b238).
(* [comment removed for export] *)
Definition cs_19a78 : csite := mkSite 0x19a78 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1084%positive 0x1bd80).
(* [comment removed for export] *)
Definition cs_19ab8 : csite := mkSite 0x19ab8 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1076%positive 0x1b238).
(* [comment removed for export] *)
Definition cs_19acc : csite := mkSite 0x19acc 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1078%positive 0x1b350).
(* [comment removed for export] *)
Definition cs_19ae0 : csite := mkSite 0x19ae0 1067%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_19ae4 : csite := mkSite 0x19ae4 1067%positive OP_FLOAD (SH12 (fun imm => FLoad FMT_D 10 10 imm)) (SK_lo12 0x19ae0 5021%positive 0x11470).
(* [comment removed for export] *)
Definition cs_19b08 : csite := mkSite 0x19b08 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1060%positive 0x17b9c).
(* [comment removed for export] *)
Definition cs_19b24 : csite := mkSite 0x19b24 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1060%positive 0x17b9c).
(* [comment removed for export] *)
Definition cs_19b50 : csite := mkSite 0x19b50 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1091%positive 0x1cdb8).
(* [comment removed for export] *)
Definition cs_19b80 : csite := mkSite 0x19b80 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1060%positive 0x17b9c).
(* [comment removed for export] *)
Definition cs_19ba0 : csite := mkSite 0x19ba0 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1060%positive 0x17b9c).
(* [comment removed for export] *)
Definition cs_19bc4 : csite := mkSite 0x19bc4 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1060%positive 0x17b9c).
(* [comment removed for export] *)
Definition cs_19bec : csite := mkSite 0x19bec 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1091%positive 0x1cdb8).
(* [comment removed for export] *)
Definition cs_19c1c : csite := mkSite 0x19c1c 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1060%positive 0x17b9c).
(* [comment removed for export] *)
Definition cs_19c3c : csite := mkSite 0x19c3c 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1060%positive 0x17b9c).
(* [comment removed for export] *)
Definition cs_19c58 : csite := mkSite 0x19c58 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1060%positive 0x17b9c).
(* [comment removed for export] *)
Definition cs_19c84 : csite := mkSite 0x19c84 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1091%positive 0x1cdb8).
(* [comment removed for export] *)
Definition cs_19cb4 : csite := mkSite 0x19cb4 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1060%positive 0x17b9c).
(* [comment removed for export] *)
Definition cs_19cd4 : csite := mkSite 0x19cd4 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1060%positive 0x17b9c).
(* [comment removed for export] *)
Definition cs_19cf0 : csite := mkSite 0x19cf0 1067%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_19cf4 : csite := mkSite 0x19cf4 1067%positive OP_FLOAD (SH12 (fun imm => FLoad FMT_D 10 10 imm)) (SK_lo12 0x19cf0 5004%positive 0x11460).
(* [comment removed for export] *)
Definition cs_19cfc : csite := mkSite 0x19cfc 1067%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_19d00 : csite := mkSite 0x19d00 1067%positive OP_FLOAD (SH12 (fun imm => FLoad FMT_D 10 10 imm)) (SK_lo12 0x19cfc 5023%positive 0x11488).
(* [comment removed for export] *)
Definition cs_19d04 : csite := mkSite 0x19d04 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1070%positive 0x1a7bc).
(* [comment removed for export] *)
Definition cs_19d38 : csite := mkSite 0x19d38 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1076%positive 0x1b238).
(* [comment removed for export] *)
Definition cs_19d54 : csite := mkSite 0x19d54 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1075%positive 0x1ab38).
(* [comment removed for export] *)
Definition cs_19d70 : csite := mkSite 0x19d70 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1075%positive 0x1ab38).
(* [comment removed for export] *)
Definition cs_19d90 : csite := mkSite 0x19d90 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1078%positive 0x1b350).
(* [comment removed for export] *)
Definition cs_19d9c : csite := mkSite 0x19d9c 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1074%positive 0x1aa70).
(* [comment removed for export] *)
Definition cs_1a0dc : csite := mkSite 0x1a0dc 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1091%positive 0x1cdb8).
(* [comment removed for export] *)
Definition cs_1a110 : csite := mkSite 0x1a110 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1060%positive 0x17b9c).
(* [comment removed for export] *)
Definition cs_1a138 : csite := mkSite 0x1a138 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1060%positive 0x17b9c).
(* [comment removed for export] *)
Definition cs_1a158 : csite := mkSite 0x1a158 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1060%positive 0x17b9c).
(* [comment removed for export] *)
Definition cs_1a194 : csite := mkSite 0x1a194 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1091%positive 0x1cdb8).
(* [comment removed for export] *)
Definition cs_1a1c8 : csite := mkSite 0x1a1c8 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1060%positive 0x17b9c).
(* [comment removed for export] *)
Definition cs_1a1f0 : csite := mkSite 0x1a1f0 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1060%positive 0x17b9c).
(* [comment removed for export] *)
Definition cs_1a2ec : csite := mkSite 0x1a2ec 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1060%positive 0x17b9c).
(* [comment removed for export] *)
Definition cs_1a314 : csite := mkSite 0x1a314 1067%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_1a324 : csite := mkSite 0x1a324 1067%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 11 imm)) (SK_lo12 0x1a314 4005%positive 0x1045e).
(* [comment removed for export] *)
Definition cs_1a3dc : csite := mkSite 0x1a3dc 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1060%positive 0x17b9c).
(* [comment removed for export] *)
Definition cs_1a424 : csite := mkSite 0x1a424 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1060%positive 0x17b9c).
(* [comment removed for export] *)
Definition cs_1a458 : csite := mkSite 0x1a458 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1060%positive 0x17b9c).
(* [comment removed for export] *)
Definition cs_1a484 : csite := mkSite 0x1a484 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1066%positive 0x18ed0).
(* [comment removed for export] *)
Definition cs_1a4ac : csite := mkSite 0x1a4ac 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1060%positive 0x17b9c).
(* [comment removed for export] *)
Definition cs_1a4c8 : csite := mkSite 0x1a4c8 1067%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_1a4cc : csite := mkSite 0x1a4cc 1067%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x1a4c8 4005%positive 0x1045e).
(* [comment removed for export] *)
Definition cs_1a4d8 : csite := mkSite 0x1a4d8 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1060%positive 0x17b9c).
(* [comment removed for export] *)
Definition cs_1a5a0 : csite := mkSite 0x1a5a0 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1060%positive 0x17b9c).
(* [comment removed for export] *)
Definition cs_1a5c8 : csite := mkSite 0x1a5c8 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1066%positive 0x18ed0).
(* [comment removed for export] *)
Definition cs_1a604 : csite := mkSite 0x1a604 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1091%positive 0x1cdb8).
(* [comment removed for export] *)
Definition cs_1a634 : csite := mkSite 0x1a634 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1060%positive 0x17b9c).
(* [comment removed for export] *)
Definition cs_1a654 : csite := mkSite 0x1a654 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1060%positive 0x17b9c).
(* [comment removed for export] *)
Definition cs_1a668 : csite := mkSite 0x1a668 1067%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1030%positive 0x159b8).
(* [comment removed for export] *)
Definition cs_1a67c : csite := mkSite 0x1a67c 1068%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1069%positive 0x1a690).
(* [comment removed for export] *)
Definition cs_1a76c : csite := mkSite 0x1a76c 1069%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1022%positive 0x1574c).
(* [comment removed for export] *)
Definition cs_1a9d4 : csite := mkSite 0x1a9d4 1073%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1074%positive 0x1aa70).
(* [comment removed for export] *)
Definition cs_1a9dc : csite := mkSite 0x1a9dc 1073%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_1a9e0 : csite := mkSite 0x1a9e0 1073%positive OP_FLOAD (SH12 (fun imm => FLoad FMT_D 10 10 imm)) (SK_lo12 0x1a9dc 5007%positive 0x114a0).
(* [comment removed for export] *)
Definition cs_1a9e4 : csite := mkSite 0x1a9e4 1073%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1070%positive 0x1a7bc).
(* [comment removed for export] *)
Definition cs_1a9f8 : csite := mkSite 0x1a9f8 1073%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1075%positive 0x1ab38).
(* [comment removed for export] *)
Definition cs_1b34c : csite := mkSite 0x1b34c 1077%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1078%positive 0x1b350).
(* [comment removed for export] *)
Definition cs_1ba70 : csite := mkSite 0x1ba70 1078%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1079%positive 0x1bb1c).
(* [comment removed for export] *)
Definition cs_1bad0 : csite := mkSite 0x1bad0 1078%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1080%positive 0x1bb4c).
(* [comment removed for export] *)
Definition cs_1bb30 : csite := mkSite 0x1bb30 1079%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_1bb34 : csite := mkSite 0x1bb34 1079%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x1bb30 5010%positive 0x117d0).
(* [comment removed for export] *)
Definition cs_1c688 : csite := mkSite 0x1c688 1085%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_1c68c : csite := mkSite 0x1c68c 1085%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 11 11 imm)) (SK_lo12 0x1c688 5019%positive 0x1f530).
(* [comment removed for export] *)
Definition cs_1c69c : csite := mkSite 0x1c69c 1085%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1063%positive 0x17dbc).
(* [comment removed for export] *)
Definition cs_1c6ac : csite := mkSite 0x1c6ac 1086%positive OP_AUIPC (SH20 (fun imm => Auipc 13 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_1c6b0 : csite := mkSite 0x1c6b0 1086%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 8 13 imm)) (SK_lo12 0x1c6ac 5027%positive 0x1e3e0).
(* [comment removed for export] *)
Definition cs_1c6c0 : csite := mkSite 0x1c6c0 1086%positive OP_AUIPC (SH20 (fun imm => Auipc 14 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_1c6c4 : csite := mkSite 0x1c6c4 1086%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 14 14 imm)) (SK_lo12 0x1c6c0 1053%positive 0x178c0).
(* [comment removed for export] *)
Definition cs_1c71c : csite := mkSite 0x1c71c 1086%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1053%positive 0x178c0).
(* [comment removed for export] *)
Definition cs_1c73c : csite := mkSite 0x1c73c 1086%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1030%positive 0x159b8).
(* [comment removed for export] *)
Definition cs_1c760 : csite := mkSite 0x1c760 1087%positive OP_AUIPC (SH20 (fun imm => Auipc 12 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_1c764 : csite := mkSite 0x1c764 1087%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 18 12 imm)) (SK_lo12 0x1c760 5027%positive 0x1e3e0).
(* [comment removed for export] *)
Definition cs_1c7a0 : csite := mkSite 0x1c7a0 1087%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1091%positive 0x1cdb8).
(* [comment removed for export] *)
Definition cs_1c7a4 : csite := mkSite 0x1c7a4 1087%positive OP_AUIPC (SH20 (fun imm => Auipc 10 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_1c7b0 : csite := mkSite 0x1c7b0 1087%positive OP_IMM (SH12 (fun imm => OpImm ALU_ADD 10 10 imm)) (SK_lo12 0x1c7a4 1088%positive 0x1c80c).
(* [comment removed for export] *)
Definition cs_1c7dc : csite := mkSite 0x1c7dc 1087%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1063%positive 0x17dbc).
(* [comment removed for export] *)
Definition cs_1c808 : csite := mkSite 0x1c808 1087%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1030%positive 0x159b8).
(* [comment removed for export] *)
Definition cs_1c864 : csite := mkSite 0x1c864 1088%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1090%positive 0x1c9b4).
(* [comment removed for export] *)
Definition cs_1c894 : csite := mkSite 0x1c894 1088%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1090%positive 0x1c9b4).
(* [comment removed for export] *)
Definition cs_1c940 : csite := mkSite 0x1c940 1089%positive OP_AUIPC (SH20 (fun imm => Auipc 13 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_1c944 : csite := mkSite 0x1c944 1089%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 13 13 imm)) (SK_lo12 0x1c940 5022%positive 0x11478).
(* [comment removed for export] *)
Definition cs_1c948 : csite := mkSite 0x1c948 1089%positive OP_AUIPC (SH20 (fun imm => Auipc 14 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_1c94c : csite := mkSite 0x1c94c 1089%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 14 14 imm)) (SK_lo12 0x1c948 5005%positive 0x11468).
(* [comment removed for export] *)
Definition cs_1ceec : csite := mkSite 0x1ceec 1092%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_1cef0 : csite := mkSite 0x1cef0 1092%positive OP_AUIPC (SH20 (fun imm => Auipc 14 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_1cef4 : csite := mkSite 0x1cef4 1092%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 13 11 imm)) (SK_lo12 0x1ceec 5022%positive 0x11478).
(* [comment removed for export] *)
Definition cs_1cef8 : csite := mkSite 0x1cef8 1092%positive OP_LOAD (SH12 (fun imm => Load SZ8 true 14 14 imm)) (SK_lo12 0x1cef0 5005%positive 0x11468).
(* [comment removed for export] *)
Definition cs_1cf60 : csite := mkSite 0x1cf60 1093%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1089%positive 0x1c8e8).
(* [comment removed for export] *)
Definition cs_1cf84 : csite := mkSite 0x1cf84 1094%positive OP_AUIPC (SH20 (fun imm => Auipc 11 imm)) SK_auipc.
(* [comment removed for export] *)
Definition cs_1cf88 : csite := mkSite 0x1cf88 1094%positive OP_LOAD (SH12 (fun imm => Load SZ1 true 13 11 imm)) (SK_lo12 0x1cf84 5031%positive 0x2f86b).
(* [comment removed for export] *)
Definition cs_1cfb4 : csite := mkSite 0x1cfb4 1094%positive OP_STORE (SH12 (fun imm => Store SZ1 11 0 imm)) (SK_lo12 0x1cf84 5031%positive 0x2f86b).
(* [comment removed for export] *)
Definition cs_1d2a4 : csite := mkSite 0x1d2a4 1097%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1096%positive 0x1d280).
(* [comment removed for export] *)
Definition cs_1d2bc : csite := mkSite 0x1d2bc 1099%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1055%positive 0x17a58).
(* [comment removed for export] *)
Definition cs_1d2dc : csite := mkSite 0x1d2dc 1099%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1097%positive 0x1d2a4).
(* [comment removed for export] *)
Definition cs_1d2f4 : csite := mkSite 0x1d2f4 1099%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1031%positive 0x159c0).
(* [comment removed for export] *)
Definition cs_1d310 : csite := mkSite 0x1d310 1100%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1031%positive 0x159c0).
(* [comment removed for export] *)
Definition cs_1d338 : csite := mkSite 0x1d338 1101%positive OP_JAL (SH21 (fun imm => Jal 1 imm)) (SK_jal 1097%positive 0x1d2a4).
(* [comment removed for export] *)
Definition cs_1d344 : csite := mkSite 0x1d344 1101%positive OP_JAL (SH21 (fun imm => Jal 0 imm)) (SK_jal 1031%positive 0x159c0).

Definition canon_sites : list csite := [
  cs_13084; cs_13088; cs_13090; cs_13094; cs_1309c; cs_130a4; cs_130a8; cs_130ac;
  cs_130b0; cs_130b4; cs_130b8; cs_130c8; cs_130dc; cs_130e0; cs_130f8; cs_130fc;
  cs_13108; cs_1310c; cs_13118; cs_1311c; cs_13120; cs_13124; cs_13150; cs_13154;
  cs_1316c; cs_13170; cs_1317c; cs_13180; cs_1318c; cs_13190; cs_131a0; cs_131a4;
  cs_131b0; cs_131b4; cs_1320c; cs_13220; cs_13230; cs_13234; cs_1324c; cs_13274;
  cs_13290; cs_13298; cs_132b4; cs_132c8; cs_1332c; cs_13340; cs_13350; cs_13368;
  cs_1336c; cs_13378; cs_1337c; cs_13380; cs_13388; cs_1338c; cs_13394; cs_1339c;
  cs_133a4; cs_133a8; cs_133b0; cs_133b8; cs_133c0; cs_133c8; cs_133fc; cs_13400;
  cs_13408; cs_1340c; cs_13418; cs_1341c; cs_13424; cs_13428; cs_13430; cs_13438;
  cs_1343c; cs_13444; cs_1344c; cs_13454; cs_1345c; cs_13460; cs_13464; cs_1346c;
  cs_13470; cs_13478; cs_1347c; cs_13484; cs_1348c; cs_134cc; cs_134d0; cs_134e0;
  cs_134e4; cs_134f4; cs_134f8; cs_13524; cs_13538; cs_1355c; cs_13568; cs_13578;
  cs_135d8; cs_135dc; cs_135e4; cs_13674; cs_13678; cs_1367c; cs_13708; cs_13710;
  cs_13714; cs_13744; cs_13748; cs_1374c; cs_1376c; cs_13770; cs_13778; cs_13780;
  cs_13784; cs_13788; cs_1378c; cs_14d1c; cs_15198; cs_1519c; cs_151a0; cs_151b4;
  cs_151b8; cs_15204; cs_15208; cs_15210; cs_15214; cs_1521c; cs_15220; cs_15238;
  cs_1523c; cs_15240; cs_15244; cs_15248; cs_1524c; cs_1527c; cs_15284; cs_152f8;
  cs_15304; cs_15328; cs_15334; cs_15358; cs_15364; cs_153ac; cs_153b0; cs_153b4;
  cs_153b8; cs_153bc; cs_15418; cs_1541c; cs_15420; cs_15478; cs_1548c; cs_154b4;
  cs_154b8; cs_154bc; cs_154c0; cs_154d0; cs_154e0; cs_154e4; cs_154e8; cs_15630;
  cs_15644; cs_156c0; cs_156d8; cs_156e4; cs_15700; cs_15704; cs_15768; cs_15774;
  cs_15784; cs_15788; cs_15790; cs_157c4; cs_157c8; cs_157cc; cs_157d0; cs_157fc;
  cs_15818; cs_1581c; cs_15860; cs_15864; cs_15868; cs_15870; cs_15894; cs_15898;
  cs_158f0; cs_1592c; cs_15954; cs_15968; cs_1596c; cs_15974; cs_1597c; cs_15980;
  cs_15994; cs_15998; cs_159dc; cs_159fc; cs_15a1c; cs_15a4c; cs_15a58; cs_15a5c;
  cs_15a84; cs_15aa0; cs_15ae0; cs_15b0c; cs_15b2c; cs_15b38; cs_15b3c; cs_15b60;
  cs_15b94; cs_15b9c; cs_15c40; cs_15c5c; cs_15c94; cs_15c98; cs_15ca4; cs_15cb0;
  cs_15cbc; cs_15cc0; cs_15cc4; cs_15ccc; cs_15ce0; cs_15d9c; cs_15da8; cs_15dc8;
  cs_15dcc; cs_15e34; cs_15e38; cs_15e84; cs_15e88; cs_15e98; cs_15e9c; cs_15f90;
  cs_15f94; cs_1608c; cs_161f0; cs_16210; cs_16214; cs_1621c; cs_16224; cs_1622c;
  cs_16230; cs_1626c; cs_1637c; cs_163d4; cs_164a8; cs_164b0; cs_164c8; cs_164f8;
  cs_16534; cs_16538; cs_16560; cs_1656c; cs_16570; cs_16578; cs_1657c; cs_16580;
  cs_165b0; cs_165b8; cs_16620; cs_16634; cs_16654; cs_166c0; cs_166c4; cs_166cc;
  cs_166d0; cs_166d4; cs_16718; cs_1671c; cs_16720; cs_1672c; cs_167d8; cs_167f8;
  cs_16828; cs_1682c; cs_16830; cs_16834; cs_16874; cs_16878; cs_16884; cs_16888;
  cs_16a04; cs_16a0c; cs_16a20; cs_16a24; cs_16a30; cs_16a44; cs_16a48; cs_16a5c;
  cs_16a60; cs_16a8c; cs_16a90; cs_16ba4; cs_16bac; cs_16c48; cs_16d18; cs_16d20;
  cs_16ee8; cs_170dc; cs_17108; cs_17110; cs_172c4; cs_172cc; cs_172ec; cs_172f0;
  cs_17360; cs_17364; cs_1738c; cs_17390; cs_173b0; cs_173b4; cs_173e8; cs_173ec;
  cs_1746c; cs_17484; cs_174e0; cs_17528; cs_17538; cs_1753c; cs_17564; cs_17590;
  cs_175a4; cs_17728; cs_17734; cs_17738; cs_1774c; cs_17790; cs_17794; cs_177a8;
  cs_177ec; cs_177f0; cs_17804; cs_17868; cs_178ec; cs_178f0; cs_1794c; cs_179d4;
  cs_17a4c; cs_17a54; cs_17a68; cs_17a74; cs_17a9c; cs_17aa0; cs_17ac8; cs_17ae8;
  cs_17b5c; cs_17b74; cs_17c54; cs_17c9c; cs_17d14; cs_17d28; cs_17d38; cs_17d58;
  cs_17d98; cs_17d9c; cs_17da4; cs_17de4; cs_17de8; cs_17e20; cs_17e34; cs_17e94;
  cs_17ec0; cs_17f30; cs_17f68; cs_17fc4; cs_17fd0; cs_180b0; cs_183d0; cs_183d4;
  cs_18444; cs_1849c; cs_184a0; cs_184dc; cs_1850c; cs_18514; cs_18538; cs_1853c;
  cs_18554; cs_18558; cs_18560; cs_18568; cs_18580; cs_18598; cs_1859c; cs_185dc;
  cs_185e0; cs_18614; cs_18618; cs_18644; cs_18648; cs_18680; cs_18684; cs_186b8;
  cs_186bc; cs_186d0; cs_186d4; cs_18734; cs_1876c; cs_18790; cs_187b4; cs_187c0;
  cs_187c4; cs_187e8; cs_187f0; cs_18938; cs_18968; cs_1898c; cs_189a8; cs_189dc;
  cs_18a0c; cs_18a30; cs_18a60; cs_18a90; cs_18ab4; cs_18ad0; cs_18b04; cs_18b34;
  cs_18b54; cs_18b70; cs_18b94; cs_18be4; cs_18c18; cs_18c2c; cs_18c40; cs_18c54;
  cs_18c68; cs_18c7c; cs_18c90; cs_18ca4; cs_18cb8; cs_18d38; cs_18d98; cs_18dac;
  cs_18db0; cs_18dfc; cs_18eec; cs_18ef0; cs_18f24; cs_18f54; cs_18f74; cs_18fa0;
  cs_19000; cs_19004; cs_1905c; cs_19068; cs_19070; cs_19084; cs_1908c; cs_190c4;
  cs_190e0; cs_190f0; cs_19104; cs_19118; cs_19154; cs_19158; cs_1915c; cs_19170;
  cs_191a0; cs_191a8; cs_191ac; cs_191b0; cs_191b4; cs_19210; cs_19230; cs_1924c;
  cs_19258; cs_19268; cs_1926c; cs_19270; cs_19274; cs_192b0; cs_192e0; cs_19300;
  cs_1931c; cs_19338; cs_1936c; cs_1939c; cs_193bc; cs_19454; cs_19464; cs_19478;
  cs_1948c; cs_194a0; cs_194b4; cs_194c0; cs_194c4; cs_1975c; cs_19778; cs_19784;
  cs_19864; cs_19880; cs_198a0; cs_198b4; cs_198d4; cs_198e4; cs_198f8; cs_1990c;
  cs_19934; cs_199f4; cs_19a24; cs_19a68; cs_19a78; cs_19ab8; cs_19acc; cs_19ae0;
  cs_19ae4; cs_19b08; cs_19b24; cs_19b50; cs_19b80; cs_19ba0; cs_19bc4; cs_19bec;
  cs_19c1c; cs_19c3c; cs_19c58; cs_19c84; cs_19cb4; cs_19cd4; cs_19cf0; cs_19cf4;
  cs_19cfc; cs_19d00; cs_19d04; cs_19d38; cs_19d54; cs_19d70; cs_19d90; cs_19d9c;
  cs_1a0dc; cs_1a110; cs_1a138; cs_1a158; cs_1a194; cs_1a1c8; cs_1a1f0; cs_1a2ec;
  cs_1a314; cs_1a324; cs_1a3dc; cs_1a424; cs_1a458; cs_1a484; cs_1a4ac; cs_1a4c8;
  cs_1a4cc; cs_1a4d8; cs_1a5a0; cs_1a5c8; cs_1a604; cs_1a634; cs_1a654; cs_1a668;
  cs_1a67c; cs_1a76c; cs_1a9d4; cs_1a9dc; cs_1a9e0; cs_1a9e4; cs_1a9f8; cs_1b34c;
  cs_1ba70; cs_1bad0; cs_1bb30; cs_1bb34; cs_1c688; cs_1c68c; cs_1c69c; cs_1c6ac;
  cs_1c6b0; cs_1c6c0; cs_1c6c4; cs_1c71c; cs_1c73c; cs_1c760; cs_1c764; cs_1c7a0;
  cs_1c7a4; cs_1c7b0; cs_1c7dc; cs_1c808; cs_1c864; cs_1c894; cs_1c940; cs_1c944;
  cs_1c948; cs_1c94c; cs_1ceec; cs_1cef0; cs_1cef4; cs_1cef8; cs_1cf60; cs_1cf84;
  cs_1cf88; cs_1cfb4; cs_1d2a4; cs_1d2bc; cs_1d2dc; cs_1d2f4; cs_1d310; cs_1d338;
  cs_1d344].

(* [comment removed for export] *)
Class RelocSites (RL : Reloc) := { rl_sites_ok : sites_check canon_sites = true }.

Section Facts.
Context {RL : Reloc} {RS : RelocSites RL}.
Definition rl_site_F := site_F canon_sites rl_sites_ok.
Definition rl_site_D := site_D canon_sites rl_sites_ok.
Definition rl_site_V := site_V canon_sites rl_sites_ok.
Definition rl_site_J := site_J canon_sites rl_sites_ok.
End Facts.
