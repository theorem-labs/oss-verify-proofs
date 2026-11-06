(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Reloc Require Import Reloc RelocImg CanonImg.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_RImg () := "I47Corelib4Init9Datatypes6option00C46Stdlib5Lists4List9nth_errorK47Corelib4Init5Logic2eq01C69OSSVerify5KrLib6Common5Reloc8CanonImg<rl_cell_factC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib6Common5Reloc8CanonImg:ce_10040_4C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common5Reloc8RelocImg5ccell00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc8CanonImg;canon_cellsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C69OSSVerify5KrLib6Common5Reloc8CanonImg:ce_10050_8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc8CanonImg:ce_10078_4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc8CanonImg:ce_100b0_4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc8CanonImg:ce_100e8_4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc8CanonImg:ce_10120_4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc8CanonImg:ce_10158_4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc8CanonImg:ce_10190_4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc8CanonImg:ce_101c8_4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc8CanonImg:ce_101f0_8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc8CanonImg:ce_10200_4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc8CanonImg:ce_10238_4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc8CanonImg:ce_11468_8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc8CanonImg:ce_11478_8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc8CanonImg:ce_11534_4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc8CanonImg:ce_11570_4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc8CanonImg:ce_11578_4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc8CanonImg:ce_115a8_4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc8CanonImg:ce_115ac_4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc8CanonImg:ce_115b0_4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc8CanonImg:ce_115d4_4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc8CanonImg:ce_11613_1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc8CanonImg:ce_11622_1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc8CanonImg:ce_11624_1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc8CanonImg:ce_11629_1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc8CanonImg:ce_11780_1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc8CanonImg:ce_1e348_8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc8CanonImg:ce_1e368_8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc8CanonImg:ce_1e370_8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc8CanonImg:ce_1e378_8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc8CanonImg:ce_1e380_8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc8CanonImg:ce_1e388_8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc8CanonImg:ce_1e3b8_8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc8CanonImg:ce_1e3c0_8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc8CanonImg:ce_1e3c8_8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc8CanonImg:ce_1e3d0_8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc8CanonImg:ce_1e3d8_8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc8CanonImg:ce_1e3e0_8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc8CanonImg:ce_1f620_4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc8CanonImg:ce_1f630_1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc8CanonImg:ce_2f6c8_8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc8CanonImg:ce_2f6d8_8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc8CanonImg:ce_2f6e0_8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc8CanonImg:ce_2f850_8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc8CanonImg:ce_2f878_8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc8CanonImg:ce_2f890_8C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.

Section I.
Context {RL : Reloc} {RI : RelocImg RL}.
Lemma img_10040_4 : rdn rl_segs (fun _ => None) (rl (rl_delta 8%positive) 0x10040) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 6)).
Proof.
ltac2:(KReplay.run1 (kr_t_RImg ()) ["I"] "p;1p;3p;2p;5g0000j13Tg000Rj32Tg0010j20Tg001Jj51Tp,2RLp,2RIg002QR0g0030g0045R1#3g0057=210'0D1o"). Qed.
Lemma img_10050_8 : rdn rl_segs (fun _ => None) (rl (rl_delta 8%positive) 0x10050) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 65600)).
Proof.
ltac2:(KReplay.run1 (kr_t_RImg ()) ["I"] "p;1p;3p;2p;5g006=j14Tg0000j13Tg000Rj30Tg0010j21Tg001Jj52Tp,2RLp,2RIg002Q#4R0g006\g0045R1#3g0057=010'1D2o"). Qed.
Lemma img_10078_4 : rdn rl_segs (fun _ => None) (rl (rl_delta 8%positive) 0x10078) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof.
ltac2:(KReplay.run1 (kr_t_RImg ()) ["I"] "p;1p;3p;2p;5g006=j10Tg0000j14Tg000Rj32Tg0010j21Tg001Jj53Tp,2RLp,2RIg002Q#0#0R0g007ag0045R1#4g0057=210'1D3o"). Qed.
Lemma img_100b0_4 : rdn rl_segs (fun _ => None) (rl (rl_delta 8%positive) 0x100b0) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof.
ltac2:(KReplay.run1 (kr_t_RImg ()) ["I"] "p;1p;3p;2p;5g006=j10Tg0000j14Tg000Rj32Tg0010j21Tg001Jj53Tp,2RLp,2RIg002Q#0#0#0R0g008fg0045R1#4g0057=210'1D3o"). Qed.
Lemma img_100e8_4 : rdn rl_segs (fun _ => None) (rl (rl_delta 8%positive) 0x100e8) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof.
ltac2:(KReplay.run1 (kr_t_RImg ()) ["I"] "p;1p;3p;2p;5g006=j10Tg0000j14Tg000Rj32Tg0010j21Tg001Jj53Tp,2RLp,2RIg002Q#0#0#0#0R0g009kg0045R1#4g0057=210'1D3o"). Qed.
Lemma img_10120_4 : rdn rl_segs (fun _ => None) (rl (rl_delta 8%positive) 0x10120) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof.
ltac2:(KReplay.run1 (kr_t_RImg ()) ["I"] "p;1p;3p;2p;5g006=j10Tg0000j14Tg000Rj32Tg0010j21Tg001Jj53Tp,2RLp,2RIg002Q#0#0#0#0#0R0g00;0g0045R1#4g0057=210'1D3o"). Qed.
Lemma img_10158_4 : rdn rl_segs (fun _ => None) (rl (rl_delta 8%positive) 0x10158) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1685382482)).
Proof.
ltac2:(KReplay.run1 (kr_t_RImg ()) ["I"] "p;1p;3p;2p;5g006=j10Tg0000j14Tg000Rj32Tg0010j21Tg001Jj53Tp,2RLp,2RIg002Q#0#0#0#0#0#0R0g00<5g0045R1#4g0057=210'1D3o"). Qed.
Lemma img_10190_4 : rdn rl_segs (fun _ => None) (rl (rl_delta 8%positive) 0x10190) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1685382480)).
Proof.
ltac2:(KReplay.run1 (kr_t_RImg ()) ["I"] "p;1p;3p;2p;5g006=j10Tg0000j14Tg000Rj32Tg0010j21Tg001Jj53Tp,2RLp,2RIg002Q#0#0#0#0#0#0#0R0g00=:g0045R1#4g0057=210'1D3o"). Qed.
Lemma img_101c8_4 : rdn rl_segs (fun _ => None) (rl (rl_delta 8%positive) 0x101c8) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1685382481)).
Proof.
ltac2:(KReplay.run1 (kr_t_RImg ()) ["I"] "p;1p;3p;2p;5g006=j10Tg0000j14Tg000Rj32Tg0010j21Tg001Jj53Tp,2RLp,2RIg002Q#0#0#0#0#0#0#0#0R0g00>?g0045R1#4g0057=210'1D3o"). Qed.
Lemma img_101f0_8 : rdn rl_segs (fun _ => None) (rl (rl_delta 8%positive) 0x101f0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_RImg ()) ["I"] "p;1p;3p;2p;5g006=j11Tg0000j13Tg000Rj32Tg0010j25Tg001Jj54Tf0#1#1p=0p,2RLp,2RIg002Q#1#0#0#0#0R0g00?Dg0045R1#3g0057=210'5D4o"). Qed.
Lemma img_10200_4 : rdn rl_segs (fun _ => None) (rl (rl_delta 8%positive) 0x10200) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4)).
Proof.
ltac2:(KReplay.run1 (kr_t_RImg ()) ["I"] "p;1p;3p;2p;5g0000j15Tg000Rj33Tg0010j22Tg001Jj54Tg006=j11Tf0#1#1p=0p,2RLp,2RIg002Q#0#0#0#0#0R0g00@Ig0045R1#5g0057=310'2D4o"). Qed.
Lemma img_10238_4 : rdn rl_segs (fun _ => None) (rl (rl_delta 8%positive) 0x10238) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1879048195)).
Proof.
ltac2:(KReplay.run1 (kr_t_RImg ()) ["I"] "p;1p;3p;2p;5g006=j11Tg0000j13Tg000Rj32Tg0010j25Tg001Jj54Tf0#1#1p=0p,2RLp,2RIg002Q#1#0#0#0#0#0R0g00ANg0045R1#3g0057=210'5D4o"). Qed.
Lemma img_11468_8 : rdn rl_segs (fun _ => None) (rl (rl_delta 5005%positive) 0x11468) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 9259542123273814144)).
Proof.
ltac2:(KReplay.run1 (kr_t_RImg ()) ["I"] "p;1p;3p;2p;5g0000j15Tg000Rj33Tg0010j22Tg001Jj54Tg006=j11Tf0#1#1p=0p,2RLp,2RIg002Q#0#0#0#0#0#0R0g00BSg0045R1#5g0057=310'2D4o"). Qed.
Lemma img_11478_8 : rdn rl_segs (fun _ => None) (rl (rl_delta 5022%positive) 0x11478) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 72340172838076672)).
Proof.
ltac2:(KReplay.run1 (kr_t_RImg ()) ["I"] "p;1p;3p;2p;5g006=j11Tg0000j13Tg000Rj32Tg0010j25Tg001Jj54Tf0#1#1p=0p,2RLp,2RIg002Q#1#0#0#0#0#0#0R0g00CXg0045R1#3g0057=210'5D4o"). Qed.
Lemma img_11534_4 : rdn rl_segs (fun _ => None) (rl (rl_delta 5008%positive) 0x11534) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 ((0x18504 + rl_delta 1064%positive) - (0x114a8 + rl_delta 5008%positive)))).
Proof.
ltac2:(KReplay.run1 (kr_t_RImg ()) ["I"] "p;1p;3p;2p;5g0000j15Tg000Rj33Tg0010j22Tg001Jj54Tg006=j11Tf0#1#1p=0p,2RLp,2RIg002Q#0#0#0#0#0#0#0R0g00D]g0045R1#5g0057=310'2D4o"). Qed.
Lemma img_11570_4 : rdn rl_segs (fun _ => None) (rl (rl_delta 5008%positive) 0x11570) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 ((0x1854c + rl_delta 1064%positive) - (0x114a8 + rl_delta 5008%positive)))).
Proof.
ltac2:(KReplay.run1 (kr_t_RImg ()) ["I"] "p;1p;3p;2p;5g006=j11Tg0000j13Tg000Rj32Tg0010j25Tg001Jj54Tf0#1#1p=0p,2RLp,2RIg002Q#1#0#0#0#0#0#0#0R0g00Ebg0045R1#3g0057=210'5D4o"). Qed.
Lemma img_11578_4 : rdn rl_segs (fun _ => None) (rl (rl_delta 5008%positive) 0x11578) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 ((0x1863c + rl_delta 1064%positive) - (0x114a8 + rl_delta 5008%positive)))).
Proof.
ltac2:(KReplay.run1 (kr_t_RImg ()) ["I"] "p;1p;3p;2p;5g0000j15Tg000Rj33Tg0010j22Tg001Jj54Tg006=j11Tf0#1#1p=0p,2RLp,2RIg002Q#0#0#0#0#0#0#0#0R0g00Fgg0045R1#5g0057=310'2D4o"). Qed.
Lemma img_115a8_4 : rdn rl_segs (fun _ => None) (rl (rl_delta 5008%positive) 0x115a8) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 ((0x18dc4 + rl_delta 1065%positive) - (0x115a8 + rl_delta 5008%positive)))).
Proof.
ltac2:(KReplay.run1 (kr_t_RImg ()) ["I"] "p;1p;3p;2p;5g006=j11Tg0000j13Tg000Rj32Tg0010j25Tg001Jj54Tf0#1#1p=0p,2RLp,2RIg002Q#1#0#0#0#0#0#0#0#0R0g00Glg0045R1#3g0057=210'5D4o"). Qed.
Lemma img_115ac_4 : rdn rl_segs (fun _ => None) (rl (rl_delta 5008%positive) 0x115ac) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 ((0x18eb8 + rl_delta 1065%positive) - (0x115a8 + rl_delta 5008%positive)))).
Proof.
ltac2:(KReplay.run1 (kr_t_RImg ()) ["I"] "p;1p;3p;2p;5g0000j13Tg000Rj32Tg0010j25Tg001Jj54Tg006=j10Tf0R0#0#0p=6%00#0#0#0p=1p,2RLp,2RIg002Q#6#1#1#1#1R0g00I1g0045R1#3g0057=210'5D4o"). Qed.
Lemma img_115b0_4 : rdn rl_segs (fun _ => None) (rl (rl_delta 5008%positive) 0x115b0) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 ((0x18e30 + rl_delta 1065%positive) - (0x115a8 + rl_delta 5008%positive)))).
Proof.
ltac2:(KReplay.run1 (kr_t_RImg ()) ["I"] "p;1p;3p;2p;5g006=j10Tg0000j12Tg000Rj35Tg0010j24Tg001Jj53Tf0R0#0#0p=6%00#0#0#0p=1p,2RLp,2RIg002Q#0#6#1#1#1#1R0g00J6g0045R1#2g0057=510'4D3o"). Qed.
Lemma img_115d4_4 : rdn rl_segs (fun _ => None) (rl (rl_delta 5008%positive) 0x115d4) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 ((0x18dc4 + rl_delta 1065%positive) - (0x115a8 + rl_delta 5008%positive)))).
Proof.
ltac2:(KReplay.run1 (kr_t_RImg ()) ["I"] "p;1p;3p;2p;5g0000j15Tg000Rj33Tg0010j22Tg001Jj54Tg006=j11Tf0#1#1#1#1p=0p,2RLp,2RIg002Q#0#0#0#0#0R0g00K;g0045R1#5g0057=310'2D4o"). Qed.
Lemma img_11613_1 : rdn rl_segs (fun _ => None) (rl (rl_delta 5008%positive) 0x11613) 1%nat = Some (word_to_le_bytes 1 (Z_to_bv 64 10)).
Proof.
ltac2:(KReplay.run1 (kr_t_RImg ()) ["I"] "p;1p;3p;2p;5g006=j10Tg0000j13Tg000Rj32Tg0010j25Tg001Jj54Tf0#0#0#0#0p=1p,2RLp,2RIg002Q#0#1#1#1#1#1R0g00L@g0045R1#3g0057=210'5D4o"). Qed.
Lemma img_11622_1 : rdn rl_segs (fun _ => None) (rl (rl_delta 5008%positive) 0x11622) 1%nat = Some (word_to_le_bytes 1 (Z_to_bv 64 9)).
Proof.
ltac2:(KReplay.run1 (kr_t_RImg ()) ["I"] "p;1p;3p;2p;5g0000j13Tg000Rj32Tg0010j25Tg001Jj54Tg006=j10Tf0R0#0#0p=6%00#0#0#0p=1p,2RLp,2RIg002Q#6#1#1#1#1#1R0g00MEg0045R1#3g0057=210'5D4o"). Qed.
Lemma img_11624_1 : rdn rl_segs (fun _ => None) (rl (rl_delta 5008%positive) 0x11624) 1%nat = Some (word_to_le_bytes 1 (Z_to_bv 64 11)).
Proof.
ltac2:(KReplay.run1 (kr_t_RImg ()) ["I"] "p;1p;3p;2p;5g006=j10Tg0000j12Tg000Rj35Tg0010j24Tg001Jj53Tf0R0#0#0p=6%00#0#0#0p=1p,2RLp,2RIg002Q#0#6#1#1#1#1#1R0g00NJg0045R1#2g0057=510'4D3o"). Qed.
Lemma img_11629_1 : rdn rl_segs (fun _ => None) (rl (rl_delta 5008%positive) 0x11629) 1%nat = Some (word_to_le_bytes 1 (Z_to_bv 64 6)).
Proof.
ltac2:(KReplay.run1 (kr_t_RImg ()) ["I"] "p;1p;3p;2p;5g0000j15Tg000Rj33Tg0010j22Tg001Jj54Tg006=j11Tf0#1#1#1#1p=0p,2RLp,2RIg002Q#0#0#0#0#0#0R0g00OOg0045R1#5g0057=310'2D4o"). Qed.
Lemma img_11780_1 : rdn rl_segs (fun _ => None) (rl (rl_delta 5008%positive) 0x11780) 1%nat = Some (word_to_le_bytes 1 (Z_to_bv 64 20)).
Proof.
ltac2:(KReplay.run1 (kr_t_RImg ()) ["I"] "p;1p;3p;2p;5g006=j11Tg0000j13Tg000Rj32Tg0010j25Tg001Jj54Tf0#1#1#1#1p=0p,2RLp,2RIg002Q#1#0#0#0#0#0#0R0g00PTg0045R1#3g0057=210'5D4o"). Qed.
Lemma img_1e348_8 : rdn rl_segs (fun _ => None) (rl (rl_delta 5016%positive) 0x1e348) 8%nat = Some (word_to_le_bytes 8 (rl (rl_delta 1002%positive) 0x130cc)).
Proof.
ltac2:(KReplay.run1 (kr_t_RImg ()) ["I"] "p;1p;3p;2p;5g0000j13Tg000Rj32Tg0010j25Tg001Jj54Tg006=j10Tf0R0#0#0p=6%00#0#0#0p=1p,2RLp,2RIg002Q#6#1#1#1#1#1#1R0g00QYg0045R1#3g0057=210'5D4o"). Qed.
Lemma img_1e368_8 : rdn rl_segs (fun _ => None) (rl (rl_delta 5012%positive) 0x1e368) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_RImg ()) ["I"] "p;1p;3p;2p;5g006=j10Tg0000j12Tg000Rj35Tg0010j24Tg001Jj53Tf0R0#0#0p=6%00#0#0#0p=1p,2RLp,2RIg002Q#0#6#1#1#1#1#1#1R0g00R^g0045R1#2g0057=510'4D3o"). Qed.
Lemma img_1e370_8 : rdn rl_segs (fun _ => None) (rl (rl_delta 5012%positive) 0x1e370) 8%nat = Some (word_to_le_bytes 8 (rl (rl_delta 1004%positive) 0x131d0)).
Proof.
ltac2:(KReplay.run1 (kr_t_RImg ()) ["I"] "p;1p;3p;2p;5g0000j15Tg000Rj33Tg0010j22Tg001Jj54Tg006=j11Tf0#1#1#1#1p=0p,2RLp,2RIg002Q#0#0#0#0#0#0#0R0g00Scg0045R1#5g0057=310'2D4o"). Qed.
Lemma img_1e378_8 : rdn rl_segs (fun _ => None) (rl (rl_delta 5012%positive) 0x1e378) 8%nat = Some (word_to_le_bytes 8 (rl (rl_delta 1016%positive) 0x1516c)).
Proof.
ltac2:(KReplay.run1 (kr_t_RImg ()) ["I"] "p;1p;3p;2p;5g006=j11Tg0000j13Tg000Rj32Tg0010j25Tg001Jj54Tf0#1#1#1#1p=0p,2RLp,2RIg002Q#1#0#0#0#0#0#0#0R0g00Thg0045R1#3g0057=210'5D4o"). Qed.
Lemma img_1e380_8 : rdn rl_segs (fun _ => None) (rl (rl_delta 5012%positive) 0x1e380) 8%nat = Some (word_to_le_bytes 8 (rl (rl_delta 1025%positive) 0x157b0)).
Proof.
ltac2:(KReplay.run1 (kr_t_RImg ()) ["I"] "p;1p;3p;2p;5g0000j13Tg000Rj32Tg0010j25Tg001Jj54Tg006=j11Tf0R0#1#1p=6%10#1#1#1p=0p,2RLp,2RIg002Q#6#0#0#0#0#0#0#0R0g00Umg0045R1#3g0057=210'5D4o"). Qed.
Lemma img_1e388_8 : rdn rl_segs (fun _ => None) (rl (rl_delta 5012%positive) 0x1e388) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_RImg ()) ["I"] "p;1p;3p;2p;5g006=j11Tg0000j12Tg000Rj35Tg0010j24Tg001Jj53Tf0R0#1#1p=6%10#1#1#1p=0p,2RLp,2RIg002Q#1#6#0#0#0#0#0#0#0R0g00W2g0045R1#2g0057=510'4D3o"). Qed.
Lemma img_1e3b8_8 : rdn rl_segs (fun _ => None) (rl (rl_delta 5027%positive) 0x1e3b8) 8%nat = Some (word_to_le_bytes 8 (rl (rl_delta 5036%positive) 0x2f6b0)).
Proof. exact (rl_cell_fact 32%nat ce_1e3b8_8 eq_refl). Qed.
Lemma img_1e3c0_8 : rdn rl_segs (fun _ => None) (rl (rl_delta 5027%positive) 0x1e3c0) 8%nat = Some (word_to_le_bytes 8 (rl (rl_delta 5031%positive) 0x2f860)).
Proof.
ltac2:(KReplay.run1 (kr_t_RImg ()) ["I"] "p;1p;3p;2p;5g006=j11Tg0000j13Tg000Rj32Tg0010j25Tg001Jj54Tf0#1#1#1#1p=0p,2RLp,2RIg002Q#1#0#0#0#0#0#0#0#0R0g00Y<g0045R1#3g0057=210'5D4o"). Qed.
Lemma img_1e3c8_8 : rdn rl_segs (fun _ => None) (rl (rl_delta 5027%positive) 0x1e3c8) 8%nat = Some (word_to_le_bytes 8 (rl (rl_delta 5031%positive) 0x2f858)).
Proof.
ltac2:(KReplay.run1 (kr_t_RImg ()) ["I"] "p;1p;3p;2p;5g0000j13Tg000Rj32Tg0010j25Tg001Jj54Tg006=j11Tf0R0#1#1p=6%10#1#1#1p=0p,2RLp,2RIg002Q#6#0#0#0#0#0#0#0#0R0g00ZAg0045R1#3g0057=210'5D4o"). Qed.
Lemma img_1e3d0_8 : rdn rl_segs (fun _ => None) (rl (rl_delta 5027%positive) 0x1e3d0) 8%nat = Some (word_to_le_bytes 8 (rl (rl_delta 5016%positive) 0x1e350)).
Proof.
ltac2:(KReplay.run1 (kr_t_RImg ()) ["I"] "p;1p;3p;2p;5g006=j11Tg0000j12Tg000Rj35Tg0010j24Tg001Jj53Tf0R0#1#1p=6%10#1#1#1p=0p,2RLp,2RIg002Q#1#6#0#0#0#0#0#0#0#0R0g00[Fg0045R1#2g0057=510'4D3o"). Qed.
Lemma img_1e3d8_8 : rdn rl_segs (fun _ => None) (rl (rl_delta 5027%positive) 0x1e3d8) 8%nat = Some (word_to_le_bytes 8 (rl (rl_delta 5016%positive) 0x1e348)).
Proof.
ltac2:(KReplay.run1 (kr_t_RImg ()) ["I"] "p;1p;3p;2p;5g0000j13Tg000Rj32Tg0010j25Tg001Jj54Tg006=j10Tf0R0#0#0#0#0p=6%00#0#0#0#0#0#0#0p=1p,2RLp,2RIg002Q#6#1#1#1#1R0g00\Kg0045R1#3g0057=210'5D4o"). Qed.
Lemma img_1e3e0_8 : rdn rl_segs (fun _ => None) (rl (rl_delta 5027%positive) 0x1e3e0) 8%nat = Some (word_to_le_bytes 8 (rl (rl_delta 5031%positive) 0x2f848)).
Proof.
ltac2:(KReplay.run1 (kr_t_RImg ()) ["I"] "p;1p;3p;2p;5g006=j10Tg0000j12Tg000Rj35Tg0010j24Tg001Jj53Tf0R0#0#0#0#0p=6%00#0#0#0#0#0#0#0p=1p,2RLp,2RIg002Q#0#6#1#1#1#1R0g00]Pg0045R1#2g0057=510'4D3o"). Qed.
Lemma img_1f620_4 : rdn rl_segs (fun _ => None) (rl (rl_delta 5019%positive) 0x1f620) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 131072)).
Proof.
ltac2:(KReplay.run1 (kr_t_RImg ()) ["I"] "p;1p;3p;2p;5g0000j12Tg000Rj35Tg0010j24Tg001Jj53Tg006=j10Tf0R0#0#0p=7%00#0#0#0p=6%00#0#0#0#0#0#0#0p=1p,2RLp,2RIg002Q#7#6#1#1#1#1R0g00^Ug0045R1#2g0057=510'4D3o"). Qed.
Lemma img_1f630_1 : rdn rl_segs (fun _ => None) (rl (rl_delta 5015%positive) 0x1f630) 1%nat = Some ([Z_to_bv 8 0]).
Proof.
ltac2:(KReplay.run1 (kr_t_RImg ()) ["I"] "p;1p;3p;2p;5g006=j10Tg0000j16Tg000Rj35Tg0010j23Tg001Jj54Tf0R0#0#0p=7%00#0#0#0p=2%00#0#0#0#0#0#0#0p=1p,2RLp,2RIg002Q#0#7#2#1#1#1#1R0g00_Zg0045R1#6g0057=510'3D4o"). Qed.
Lemma img_2f6c8_8 : rdn rl_segs (fun _ => None) (rl (rl_delta 5037%positive) 0x2f6c8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. exact (rl_cell_fact 40%nat ce_2f6c8_8 eq_refl). Qed.
Lemma img_2f6d8_8 : rdn rl_segs (fun _ => None) (rl (rl_delta 5037%positive) 0x2f6d8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. exact (rl_cell_fact 41%nat ce_2f6d8_8 eq_refl). Qed.
Lemma img_2f6e0_8 : rdn rl_segs (fun _ => None) (rl (rl_delta 5037%positive) 0x2f6e0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. exact (rl_cell_fact 42%nat ce_2f6e0_8 eq_refl). Qed.
Lemma img_2f850_8 : rdn rl_segs (fun _ => None) (rl (rl_delta 5031%positive) 0x2f850) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_RImg ()) ["I"] "p;1p;3p;2p;5g006=j10Tg0000j12Tg000Rj35Tg0010j24Tg001Jj53Tf0R0#0#0p=6%00#0#0#0#0#0#0#0p=1p,2RLp,2RIg002Q#0#6#1#1#1#1#1R0g00cng0045R1#2g0057=510'4D3o"). Qed.
Lemma img_2f878_8 : rdn rl_segs (fun _ => None) (rl (rl_delta 5031%positive) 0x2f878) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_RImg ()) ["I"] "p;1p;3p;2p;5g0000j13Tg000Rj32Tg0010j25Tg001Jj54Tg006=j10Tf0R0#0#0#0#0p=6%00#0#0#0#0#0#0#0p=1p,2RLp,2RIg002Q#6#1#1#1#1#1R0g00e3g0045R1#3g0057=210'5D4o"). Qed.
Lemma img_2f890_8 : rdn rl_segs (fun _ => None) (rl (rl_delta 5031%positive) 0x2f890) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_RImg ()) ["I"] "p;1p;3p;2p;5g006=j10Tg0000j12Tg000Rj35Tg0010j24Tg001Jj53Tf0R0#0#0#0#0p=6%00#0#0#0#0#0#0#0p=1p,2RLp,2RIg002Q#0#6#1#1#1#1#1R0g00f8g0045R1#2g0057=510'4D3o"). Qed.
End I.
