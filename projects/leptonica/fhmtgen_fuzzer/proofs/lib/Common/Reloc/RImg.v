(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Import PropExec.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc Require Import Reloc RelocImg CanonImg.
Import ListNotations.
Open Scope bv_scope.

Section I.
Context {RL : Reloc} {RI : RelocImg RL}.
Lemma img_10040_4 : rdn rl_segs (fun _ => None) (rl (rl_delta 8%positive) 0x10040) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 6)).
Proof. exact (rl_cell_fact 0%nat ce_10040_4 eq_refl). Qed.
Lemma img_10050_8 : rdn rl_segs (fun _ => None) (rl (rl_delta 8%positive) 0x10050) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 65600)).
Proof. exact (rl_cell_fact 1%nat ce_10050_8 eq_refl). Qed.
Lemma img_10078_4 : rdn rl_segs (fun _ => None) (rl (rl_delta 8%positive) 0x10078) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. exact (rl_cell_fact 2%nat ce_10078_4 eq_refl). Qed.
Lemma img_100b0_4 : rdn rl_segs (fun _ => None) (rl (rl_delta 8%positive) 0x100b0) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. exact (rl_cell_fact 3%nat ce_100b0_4 eq_refl). Qed.
Lemma img_100e8_4 : rdn rl_segs (fun _ => None) (rl (rl_delta 8%positive) 0x100e8) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. exact (rl_cell_fact 4%nat ce_100e8_4 eq_refl). Qed.
Lemma img_10120_4 : rdn rl_segs (fun _ => None) (rl (rl_delta 8%positive) 0x10120) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. exact (rl_cell_fact 5%nat ce_10120_4 eq_refl). Qed.
Lemma img_10158_4 : rdn rl_segs (fun _ => None) (rl (rl_delta 8%positive) 0x10158) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1685382482)).
Proof. exact (rl_cell_fact 6%nat ce_10158_4 eq_refl). Qed.
Lemma img_10190_4 : rdn rl_segs (fun _ => None) (rl (rl_delta 8%positive) 0x10190) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1685382480)).
Proof. exact (rl_cell_fact 7%nat ce_10190_4 eq_refl). Qed.
Lemma img_101c8_4 : rdn rl_segs (fun _ => None) (rl (rl_delta 8%positive) 0x101c8) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1685382481)).
Proof. exact (rl_cell_fact 8%nat ce_101c8_4 eq_refl). Qed.
Lemma img_101f0_8 : rdn rl_segs (fun _ => None) (rl (rl_delta 8%positive) 0x101f0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. exact (rl_cell_fact 9%nat ce_101f0_8 eq_refl). Qed.
Lemma img_10200_4 : rdn rl_segs (fun _ => None) (rl (rl_delta 8%positive) 0x10200) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4)).
Proof. exact (rl_cell_fact 10%nat ce_10200_4 eq_refl). Qed.
Lemma img_10238_4 : rdn rl_segs (fun _ => None) (rl (rl_delta 8%positive) 0x10238) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1879048195)).
Proof. exact (rl_cell_fact 11%nat ce_10238_4 eq_refl). Qed.
Lemma img_11468_8 : rdn rl_segs (fun _ => None) (rl (rl_delta 5005%positive) 0x11468) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 9259542123273814144)).
Proof. exact (rl_cell_fact 12%nat ce_11468_8 eq_refl). Qed.
Lemma img_11478_8 : rdn rl_segs (fun _ => None) (rl (rl_delta 5022%positive) 0x11478) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 72340172838076672)).
Proof. exact (rl_cell_fact 13%nat ce_11478_8 eq_refl). Qed.
Lemma img_11534_4 : rdn rl_segs (fun _ => None) (rl (rl_delta 5008%positive) 0x11534) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 ((0x18504 + rl_delta 1064%positive) - (0x114a8 + rl_delta 5008%positive)))).
Proof. exact (rl_cell_fact 14%nat ce_11534_4 eq_refl). Qed.
Lemma img_11570_4 : rdn rl_segs (fun _ => None) (rl (rl_delta 5008%positive) 0x11570) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 ((0x1854c + rl_delta 1064%positive) - (0x114a8 + rl_delta 5008%positive)))).
Proof. exact (rl_cell_fact 15%nat ce_11570_4 eq_refl). Qed.
Lemma img_11578_4 : rdn rl_segs (fun _ => None) (rl (rl_delta 5008%positive) 0x11578) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 ((0x1863c + rl_delta 1064%positive) - (0x114a8 + rl_delta 5008%positive)))).
Proof. exact (rl_cell_fact 16%nat ce_11578_4 eq_refl). Qed.
Lemma img_115a8_4 : rdn rl_segs (fun _ => None) (rl (rl_delta 5008%positive) 0x115a8) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 ((0x18dc4 + rl_delta 1065%positive) - (0x115a8 + rl_delta 5008%positive)))).
Proof. exact (rl_cell_fact 17%nat ce_115a8_4 eq_refl). Qed.
Lemma img_115ac_4 : rdn rl_segs (fun _ => None) (rl (rl_delta 5008%positive) 0x115ac) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 ((0x18eb8 + rl_delta 1065%positive) - (0x115a8 + rl_delta 5008%positive)))).
Proof. exact (rl_cell_fact 18%nat ce_115ac_4 eq_refl). Qed.
Lemma img_115b0_4 : rdn rl_segs (fun _ => None) (rl (rl_delta 5008%positive) 0x115b0) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 ((0x18e30 + rl_delta 1065%positive) - (0x115a8 + rl_delta 5008%positive)))).
Proof. exact (rl_cell_fact 19%nat ce_115b0_4 eq_refl). Qed.
Lemma img_115d4_4 : rdn rl_segs (fun _ => None) (rl (rl_delta 5008%positive) 0x115d4) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 ((0x18dc4 + rl_delta 1065%positive) - (0x115a8 + rl_delta 5008%positive)))).
Proof. exact (rl_cell_fact 20%nat ce_115d4_4 eq_refl). Qed.
Lemma img_11613_1 : rdn rl_segs (fun _ => None) (rl (rl_delta 5008%positive) 0x11613) 1%nat = Some (word_to_le_bytes 1 (Z_to_bv 64 10)).
Proof. exact (rl_cell_fact 21%nat ce_11613_1 eq_refl). Qed.
Lemma img_11622_1 : rdn rl_segs (fun _ => None) (rl (rl_delta 5008%positive) 0x11622) 1%nat = Some (word_to_le_bytes 1 (Z_to_bv 64 9)).
Proof. exact (rl_cell_fact 22%nat ce_11622_1 eq_refl). Qed.
Lemma img_11624_1 : rdn rl_segs (fun _ => None) (rl (rl_delta 5008%positive) 0x11624) 1%nat = Some (word_to_le_bytes 1 (Z_to_bv 64 11)).
Proof. exact (rl_cell_fact 23%nat ce_11624_1 eq_refl). Qed.
Lemma img_11629_1 : rdn rl_segs (fun _ => None) (rl (rl_delta 5008%positive) 0x11629) 1%nat = Some (word_to_le_bytes 1 (Z_to_bv 64 6)).
Proof. exact (rl_cell_fact 24%nat ce_11629_1 eq_refl). Qed.
Lemma img_11780_1 : rdn rl_segs (fun _ => None) (rl (rl_delta 5008%positive) 0x11780) 1%nat = Some (word_to_le_bytes 1 (Z_to_bv 64 20)).
Proof. exact (rl_cell_fact 25%nat ce_11780_1 eq_refl). Qed.
Lemma img_1e348_8 : rdn rl_segs (fun _ => None) (rl (rl_delta 5016%positive) 0x1e348) 8%nat = Some (word_to_le_bytes 8 (rl (rl_delta 1002%positive) 0x130cc)).
Proof. exact (rl_cell_fact 26%nat ce_1e348_8 eq_refl). Qed.
Lemma img_1e368_8 : rdn rl_segs (fun _ => None) (rl (rl_delta 5012%positive) 0x1e368) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. exact (rl_cell_fact 27%nat ce_1e368_8 eq_refl). Qed.
Lemma img_1e370_8 : rdn rl_segs (fun _ => None) (rl (rl_delta 5012%positive) 0x1e370) 8%nat = Some (word_to_le_bytes 8 (rl (rl_delta 1004%positive) 0x131d0)).
Proof. exact (rl_cell_fact 28%nat ce_1e370_8 eq_refl). Qed.
Lemma img_1e378_8 : rdn rl_segs (fun _ => None) (rl (rl_delta 5012%positive) 0x1e378) 8%nat = Some (word_to_le_bytes 8 (rl (rl_delta 1016%positive) 0x1516c)).
Proof. exact (rl_cell_fact 29%nat ce_1e378_8 eq_refl). Qed.
Lemma img_1e380_8 : rdn rl_segs (fun _ => None) (rl (rl_delta 5012%positive) 0x1e380) 8%nat = Some (word_to_le_bytes 8 (rl (rl_delta 1025%positive) 0x157b0)).
Proof. exact (rl_cell_fact 30%nat ce_1e380_8 eq_refl). Qed.
Lemma img_1e388_8 : rdn rl_segs (fun _ => None) (rl (rl_delta 5012%positive) 0x1e388) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. exact (rl_cell_fact 31%nat ce_1e388_8 eq_refl). Qed.
Lemma img_1e3b8_8 : rdn rl_segs (fun _ => None) (rl (rl_delta 5027%positive) 0x1e3b8) 8%nat = Some (word_to_le_bytes 8 (rl (rl_delta 5035%positive) 0x2f6b0)).
Proof. exact (rl_cell_fact 32%nat ce_1e3b8_8 eq_refl). Qed.
Lemma img_1e3c0_8 : rdn rl_segs (fun _ => None) (rl (rl_delta 5027%positive) 0x1e3c0) 8%nat = Some (word_to_le_bytes 8 (rl (rl_delta 5031%positive) 0x2f860)).
Proof. exact (rl_cell_fact 33%nat ce_1e3c0_8 eq_refl). Qed.
Lemma img_1e3c8_8 : rdn rl_segs (fun _ => None) (rl (rl_delta 5027%positive) 0x1e3c8) 8%nat = Some (word_to_le_bytes 8 (rl (rl_delta 5031%positive) 0x2f858)).
Proof. exact (rl_cell_fact 34%nat ce_1e3c8_8 eq_refl). Qed.
Lemma img_1e3d0_8 : rdn rl_segs (fun _ => None) (rl (rl_delta 5027%positive) 0x1e3d0) 8%nat = Some (word_to_le_bytes 8 (rl (rl_delta 5016%positive) 0x1e350)).
Proof. exact (rl_cell_fact 35%nat ce_1e3d0_8 eq_refl). Qed.
Lemma img_1e3d8_8 : rdn rl_segs (fun _ => None) (rl (rl_delta 5027%positive) 0x1e3d8) 8%nat = Some (word_to_le_bytes 8 (rl (rl_delta 5016%positive) 0x1e348)).
Proof. exact (rl_cell_fact 36%nat ce_1e3d8_8 eq_refl). Qed.
Lemma img_1e3e0_8 : rdn rl_segs (fun _ => None) (rl (rl_delta 5027%positive) 0x1e3e0) 8%nat = Some (word_to_le_bytes 8 (rl (rl_delta 5031%positive) 0x2f848)).
Proof. exact (rl_cell_fact 37%nat ce_1e3e0_8 eq_refl). Qed.
Lemma img_1f620_4 : rdn rl_segs (fun _ => None) (rl (rl_delta 5019%positive) 0x1f620) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 131072)).
Proof. exact (rl_cell_fact 38%nat ce_1f620_4 eq_refl). Qed.
Lemma img_1f630_1 : rdn rl_segs (fun _ => None) (rl (rl_delta 5015%positive) 0x1f630) 1%nat = Some ([Z_to_bv 8 0]).
Proof. exact (rl_cell_fact 39%nat ce_1f630_1 eq_refl). Qed.
Lemma img_2f6c8_8 : rdn rl_segs (fun _ => None) (rl (rl_delta 5036%positive) 0x2f6c8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. exact (rl_cell_fact 40%nat ce_2f6c8_8 eq_refl). Qed.
Lemma img_2f6d8_8 : rdn rl_segs (fun _ => None) (rl (rl_delta 5036%positive) 0x2f6d8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. exact (rl_cell_fact 41%nat ce_2f6d8_8 eq_refl). Qed.
Lemma img_2f6e0_8 : rdn rl_segs (fun _ => None) (rl (rl_delta 5036%positive) 0x2f6e0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. exact (rl_cell_fact 42%nat ce_2f6e0_8 eq_refl). Qed.
Lemma img_2f850_8 : rdn rl_segs (fun _ => None) (rl (rl_delta 5031%positive) 0x2f850) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. exact (rl_cell_fact 43%nat ce_2f850_8 eq_refl). Qed.
Lemma img_2f878_8 : rdn rl_segs (fun _ => None) (rl (rl_delta 5031%positive) 0x2f878) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. exact (rl_cell_fact 44%nat ce_2f878_8 eq_refl). Qed.
Lemma img_2f890_8 : rdn rl_segs (fun _ => None) (rl (rl_delta 5031%positive) 0x2f890) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. exact (rl_cell_fact 45%nat ce_2f890_8 eq_refl). Qed.
End I.
