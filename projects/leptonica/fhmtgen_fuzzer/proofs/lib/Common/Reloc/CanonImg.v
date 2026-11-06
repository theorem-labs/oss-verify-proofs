(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Import PropExec.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc Require Import Reloc RelocImg.
Import ListNotations.
Local Open Scope Z_scope.

Definition ce_10040_4 : ccell := mkCell 8%positive 0x10040 4%nat (CV_lit 6).
Definition ce_10050_8 : ccell := mkCell 8%positive 0x10050 8%nat (CV_lit 65600).
Definition ce_10078_4 : ccell := mkCell 8%positive 0x10078 4%nat (CV_lit 1).
Definition ce_100b0_4 : ccell := mkCell 8%positive 0x100b0 4%nat (CV_lit 1).
Definition ce_100e8_4 : ccell := mkCell 8%positive 0x100e8 4%nat (CV_lit 1).
Definition ce_10120_4 : ccell := mkCell 8%positive 0x10120 4%nat (CV_lit 1).
Definition ce_10158_4 : ccell := mkCell 8%positive 0x10158 4%nat (CV_lit 1685382482).
Definition ce_10190_4 : ccell := mkCell 8%positive 0x10190 4%nat (CV_lit 1685382480).
Definition ce_101c8_4 : ccell := mkCell 8%positive 0x101c8 4%nat (CV_lit 1685382481).
Definition ce_101f0_8 : ccell := mkCell 8%positive 0x101f0 8%nat (CV_lit 0).
Definition ce_10200_4 : ccell := mkCell 8%positive 0x10200 4%nat (CV_lit 4).
Definition ce_10238_4 : ccell := mkCell 8%positive 0x10238 4%nat (CV_lit 1879048195).
Definition ce_11468_8 : ccell := mkCell 5005%positive 0x11468 8%nat (CV_lit 9259542123273814144).
Definition ce_11478_8 : ccell := mkCell 5022%positive 0x11478 8%nat (CV_lit 72340172838076672).
Definition ce_11534_4 : ccell := mkCell 5008%positive 0x11534 4%nat (CV_rel 1064%positive 0x18504 5008%positive 0x114a8).
Definition ce_11570_4 : ccell := mkCell 5008%positive 0x11570 4%nat (CV_rel 1064%positive 0x1854c 5008%positive 0x114a8).
Definition ce_11578_4 : ccell := mkCell 5008%positive 0x11578 4%nat (CV_rel 1064%positive 0x1863c 5008%positive 0x114a8).
Definition ce_115a8_4 : ccell := mkCell 5008%positive 0x115a8 4%nat (CV_rel 1065%positive 0x18dc4 5008%positive 0x115a8).
Definition ce_115ac_4 : ccell := mkCell 5008%positive 0x115ac 4%nat (CV_rel 1065%positive 0x18eb8 5008%positive 0x115a8).
Definition ce_115b0_4 : ccell := mkCell 5008%positive 0x115b0 4%nat (CV_rel 1065%positive 0x18e30 5008%positive 0x115a8).
Definition ce_115d4_4 : ccell := mkCell 5008%positive 0x115d4 4%nat (CV_rel 1065%positive 0x18dc4 5008%positive 0x115a8).
Definition ce_11613_1 : ccell := mkCell 5008%positive 0x11613 1%nat (CV_lit 10).
Definition ce_11622_1 : ccell := mkCell 5008%positive 0x11622 1%nat (CV_lit 9).
Definition ce_11624_1 : ccell := mkCell 5008%positive 0x11624 1%nat (CV_lit 11).
Definition ce_11629_1 : ccell := mkCell 5008%positive 0x11629 1%nat (CV_lit 6).
Definition ce_11780_1 : ccell := mkCell 5008%positive 0x11780 1%nat (CV_lit 20).
Definition ce_1e348_8 : ccell := mkCell 5016%positive 0x1e348 8%nat (CV_rl 1002%positive 0x130cc).
Definition ce_1e368_8 : ccell := mkCell 5012%positive 0x1e368 8%nat (CV_lit 0).
Definition ce_1e370_8 : ccell := mkCell 5012%positive 0x1e370 8%nat (CV_rl 1004%positive 0x131d0).
Definition ce_1e378_8 : ccell := mkCell 5012%positive 0x1e378 8%nat (CV_rl 1016%positive 0x1516c).
Definition ce_1e380_8 : ccell := mkCell 5012%positive 0x1e380 8%nat (CV_rl 1025%positive 0x157b0).
Definition ce_1e388_8 : ccell := mkCell 5012%positive 0x1e388 8%nat (CV_lit 0).
Definition ce_1e3b8_8 : ccell := mkCell 5027%positive 0x1e3b8 8%nat (CV_rl 5035%positive 0x2f6b0).
Definition ce_1e3c0_8 : ccell := mkCell 5027%positive 0x1e3c0 8%nat (CV_rl 5031%positive 0x2f860).
Definition ce_1e3c8_8 : ccell := mkCell 5027%positive 0x1e3c8 8%nat (CV_rl 5031%positive 0x2f858).
Definition ce_1e3d0_8 : ccell := mkCell 5027%positive 0x1e3d0 8%nat (CV_rl 5016%positive 0x1e350).
Definition ce_1e3d8_8 : ccell := mkCell 5027%positive 0x1e3d8 8%nat (CV_rl 5016%positive 0x1e348).
Definition ce_1e3e0_8 : ccell := mkCell 5027%positive 0x1e3e0 8%nat (CV_rl 5031%positive 0x2f848).
Definition ce_1f620_4 : ccell := mkCell 5019%positive 0x1f620 4%nat (CV_lit 131072).
Definition ce_1f630_1 : ccell := mkCell 5015%positive 0x1f630 1%nat (CV_bytes [0]).
Definition ce_2f6c8_8 : ccell := mkCell 5036%positive 0x2f6c8 8%nat (CV_lit 0).
Definition ce_2f6d8_8 : ccell := mkCell 5036%positive 0x2f6d8 8%nat (CV_lit 0).
Definition ce_2f6e0_8 : ccell := mkCell 5036%positive 0x2f6e0 8%nat (CV_lit 0).
Definition ce_2f850_8 : ccell := mkCell 5031%positive 0x2f850 8%nat (CV_lit 0).
Definition ce_2f878_8 : ccell := mkCell 5031%positive 0x2f878 8%nat (CV_lit 0).
Definition ce_2f890_8 : ccell := mkCell 5031%positive 0x2f890 8%nat (CV_lit 0).

Definition canon_cells : list ccell := [
  ce_10040_4; ce_10050_8; ce_10078_4; ce_100b0_4; ce_100e8_4; ce_10120_4; ce_10158_4; ce_10190_4;
  ce_101c8_4; ce_101f0_8; ce_10200_4; ce_10238_4; ce_11468_8; ce_11478_8; ce_11534_4; ce_11570_4;
  ce_11578_4; ce_115a8_4; ce_115ac_4; ce_115b0_4; ce_115d4_4; ce_11613_1; ce_11622_1; ce_11624_1;
  ce_11629_1; ce_11780_1; ce_1e348_8; ce_1e368_8; ce_1e370_8; ce_1e378_8; ce_1e380_8; ce_1e388_8;
  ce_1e3b8_8; ce_1e3c0_8; ce_1e3c8_8; ce_1e3d0_8; ce_1e3d8_8; ce_1e3e0_8; ce_1f620_4; ce_1f630_1;
  ce_2f6c8_8; ce_2f6d8_8; ce_2f6e0_8; ce_2f850_8; ce_2f878_8; ce_2f890_8].

Class RelocImg (RL : Reloc) := { rl_cells_ok : cells_check canon_cells = true }.

Definition rl_cell_fact {RL : Reloc} {RI : RelocImg RL} := cell_fact canon_cells rl_cells_ok.
