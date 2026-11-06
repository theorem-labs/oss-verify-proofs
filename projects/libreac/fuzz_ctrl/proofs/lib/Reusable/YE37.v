(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YE37.v (donor image sha256 1c29845fe605), with its module paths changed, names TfibSyms -> CtrlTSyms and its addresses moved to libreac/fuzz_ctrl's ASan build. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YB1v YE34 YF0l YF0m YE3g YE2p YE3i YE3h YE3m YE23 YF0x YE20 YE2y YE7f.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Notation tbl2 := tbl_x213 (only parsing).
Notation tbl2_ok := tbl_x213_ok (only parsing).
Definition x2_rodata : list (Z * Z * list (Z * N * Z)) :=
[ (0x103a0, 8, [(0, 8%N, 0xafffff00000fffff)]);
(0xa08d0, 72, [(0, 8%N, 0x139160); (8, 8%N, 0xa2790); (16, 8%N, 0x13b1e8); (24, 8%N, 0xa6eb8); (32, 8%N, 0xa96b8);
(40, 8%N, 0xaa3a8); (48, 8%N, 0xaa3b0); (56, 8%N, 0xaa3a0); (64, 8%N, 0xa2758)]);
(0xa1568, 16, [(0, 8%N, 0xa51a0); (8, 8%N, 0xa5fe0)]);
(0xa2758, 8, [(0, 8%N, 0x98e34)]);
(0xa51a0, 3648, [(0, 8%N, 0x21140); (8, 8%N, 0x6); (16, 8%N, 0x20);   (32, 8%N, 0x211a0);
(40, 8%N, 0); (48, 8%N, 0); (56, 8%N, 0xffffffffffffffff);
(64, 8%N, 0x21160); (72, 8%N, 0x1); (80, 8%N, 0x20);   (96, 8%N, 0x211a0);
(104, 8%N, 0); (112, 8%N, 0); (120, 8%N, 0xffffffffffffffff);
(128, 8%N, 0x21180); (136, 8%N, 0xc); (144, 8%N, 0x20);   (160, 8%N, 0x211a0);
(168, 8%N, 0); (176, 8%N, 0); (184, 8%N, 0xffffffffffffffff);
(192, 8%N, 0x211e0); (200, 8%N, 0x2); (208, 8%N, 0x20);   (224, 8%N, 0x219e0);
(232, 8%N, 0); (240, 8%N, 0); (248, 8%N, 0xffffffffffffffff);
(256, 8%N, 0x21200); (264, 8%N, 0x7); (272, 8%N, 0x20);   (288, 8%N, 0x219e0);
(296, 8%N, 0); (304, 8%N, 0); (312, 8%N, 0xffffffffffffffff);
(320, 8%N, 0x21220); (328, 8%N, 0x5); (336, 8%N, 0x20);   (352, 8%N, 0x219e0);
(360, 8%N, 0); (368, 8%N, 0); (376, 8%N, 0xffffffffffffffff);
(384, 8%N, 0x21240); (392, 8%N, 0x7); (400, 8%N, 0x20);   (416, 8%N, 0x219e0);
(424, 8%N, 0); (432, 8%N, 0); (440, 8%N, 0xffffffffffffffff);
(448, 8%N, 0x21260); (456, 8%N, 0xf); (464, 8%N, 0x20);   (480, 8%N, 0x219e0);
(488, 8%N, 0); (496, 8%N, 0); (504, 8%N, 0xffffffffffffffff);
(512, 8%N, 0x21280); (520, 8%N, 0xa); (528, 8%N, 0x20);   (544, 8%N, 0x219e0);
(552, 8%N, 0); (560, 8%N, 0); (568, 8%N, 0xffffffffffffffff);
(576, 8%N, 0x212a0); (584, 8%N, 0x10); (592, 8%N, 0x20);   (608, 8%N, 0x219e0);
(616, 8%N, 0); (624, 8%N, 0); (632, 8%N, 0xffffffffffffffff);
(640, 8%N, 0x212c0); (648, 8%N, 0x6); (656, 8%N, 0x20);   (672, 8%N, 0x219e0);
(680, 8%N, 0); (688, 8%N, 0); (696, 8%N, 0xffffffffffffffff);
(704, 8%N, 0x212e0); (712, 8%N, 0x8); (720, 8%N, 0x20);   (736, 8%N, 0x219e0);
(744, 8%N, 0); (752, 8%N, 0); (760, 8%N, 0xffffffffffffffff);
(768, 8%N, 0x21300); (776, 8%N, 0x7); (784, 8%N, 0x20);   (800, 8%N, 0x219e0);
(808, 8%N, 0); (816, 8%N, 0); (824, 8%N, 0xffffffffffffffff);
(832, 8%N, 0x21320); (840, 8%N, 0xf); (848, 8%N, 0x20);   (864, 8%N, 0x219e0);
(872, 8%N, 0); (880, 8%N, 0); (888, 8%N, 0xffffffffffffffff);
(896, 8%N, 0x21340); (904, 8%N, 0x10); (912, 8%N, 0x20);   (928, 8%N, 0x219e0);
(936, 8%N, 0); (944, 8%N, 0); (952, 8%N, 0xffffffffffffffff);
(960, 8%N, 0x21360); (968, 8%N, 0xa); (976, 8%N, 0x20);   (992, 8%N, 0x219e0);
(1000, 8%N, 0); (1008, 8%N, 0); (1016, 8%N, 0xffffffffffffffff);
(1024, 8%N, 0x21380); (1032, 8%N, 0x10); (1040, 8%N, 0x20);   (1056, 8%N, 0x219e0);
(1064, 8%N, 0); (1072, 8%N, 0); (1080, 8%N, 0xffffffffffffffff);
(1088, 8%N, 0x213a0); (1096, 8%N, 0x6); (1104, 8%N, 0x20);   (1120, 8%N, 0x219e0);
(1128, 8%N, 0); (1136, 8%N, 0); (1144, 8%N, 0xffffffffffffffff);
(1152, 8%N, 0x213c0); (1160, 8%N, 0xd); (1168, 8%N, 0x20);   (1184, 8%N, 0x219e0);
(1192, 8%N, 0); (1200, 8%N, 0); (1208, 8%N, 0xffffffffffffffff);
(1216, 8%N, 0x213e0); (1224, 8%N, 0x6); (1232, 8%N, 0x20);   (1248, 8%N, 0x219e0);
(1256, 8%N, 0); (1264, 8%N, 0); (1272, 8%N, 0xffffffffffffffff);
(1280, 8%N, 0x21400); (1288, 8%N, 0x17); (1296, 8%N, 0x40);   (1312, 8%N, 0x219e0);
(1320, 8%N, 0); (1328, 8%N, 0); (1336, 8%N, 0xffffffffffffffff);
(1344, 8%N, 0x21440); (1352, 8%N, 0x6); (1360, 8%N, 0x20);   (1376, 8%N, 0x219e0);
(1384, 8%N, 0); (1392, 8%N, 0); (1400, 8%N, 0xffffffffffffffff);
(1408, 8%N, 0x21460); (1416, 8%N, 0x16); (1424, 8%N, 0x40);   (1440, 8%N, 0x219e0);
(1448, 8%N, 0); (1456, 8%N, 0); (1464, 8%N, 0xffffffffffffffff);
(1472, 8%N, 0x214a0); (1480, 8%N, 0x7); (1488, 8%N, 0x20);   (1504, 8%N, 0x219e0);
(1512, 8%N, 0); (1520, 8%N, 0); (1528, 8%N, 0xffffffffffffffff);
(1536, 8%N, 0x214c0); (1544, 8%N, 0x7); (1552, 8%N, 0x20);   (1568, 8%N, 0x219e0);
(1576, 8%N, 0); (1584, 8%N, 0); (1592, 8%N, 0xffffffffffffffff);
(1600, 8%N, 0x214e0); (1608, 8%N, 0x1d); (1616, 8%N, 0x40);   (1632, 8%N, 0x219e0);
(1640, 8%N, 0); (1648, 8%N, 0); (1656, 8%N, 0xffffffffffffffff);
(1664, 8%N, 0x21520); (1672, 8%N, 0xc); (1680, 8%N, 0x20);   (1696, 8%N, 0x219e0);
(1704, 8%N, 0); (1712, 8%N, 0); (1720, 8%N, 0xffffffffffffffff);
(1728, 8%N, 0x21540); (1736, 8%N, 0x1d); (1744, 8%N, 0x40);   (1760, 8%N, 0x219e0);
(1768, 8%N, 0); (1776, 8%N, 0); (1784, 8%N, 0xffffffffffffffff);
(1792, 8%N, 0x21580); (1800, 8%N, 0x6); (1808, 8%N, 0x20);   (1824, 8%N, 0x219e0);
(1832, 8%N, 0); (1840, 8%N, 0); (1848, 8%N, 0xffffffffffffffff);
(1856, 8%N, 0x215a0); (1864, 8%N, 0x17); (1872, 8%N, 0x40);   (1888, 8%N, 0x219e0);
(1896, 8%N, 0); (1904, 8%N, 0); (1912, 8%N, 0xffffffffffffffff);
(1920, 8%N, 0x215e0); (1928, 8%N, 0x8); (1936, 8%N, 0x20);   (1952, 8%N, 0x219e0);
(1960, 8%N, 0); (1968, 8%N, 0); (1976, 8%N, 0xffffffffffffffff);
(1984, 8%N, 0x21600); (1992, 8%N, 0x6); (2000, 8%N, 0x20);   (2016, 8%N, 0x219e0);
(2024, 8%N, 0); (2032, 8%N, 0); (2040, 8%N, 0xffffffffffffffff);
(2048, 8%N, 0x21620); (2056, 8%N, 0x18); (2064, 8%N, 0x40);   (2080, 8%N, 0x219e0);
(2088, 8%N, 0); (2096, 8%N, 0); (2104, 8%N, 0xffffffffffffffff);
(2112, 8%N, 0x21660); (2120, 8%N, 0x8); (2128, 8%N, 0x20);   (2144, 8%N, 0x219e0);
(2152, 8%N, 0); (2160, 8%N, 0); (2168, 8%N, 0xffffffffffffffff);
(2176, 8%N, 0x21680); (2184, 8%N, 0x7); (2192, 8%N, 0x20);   (2208, 8%N, 0x219e0);
(2216, 8%N, 0); (2224, 8%N, 0); (2232, 8%N, 0xffffffffffffffff);
(2240, 8%N, 0x216a0); (2248, 8%N, 0x18); (2256, 8%N, 0x40);   (2272, 8%N, 0x219e0);
(2280, 8%N, 0); (2288, 8%N, 0); (2296, 8%N, 0xffffffffffffffff);
(2304, 8%N, 0x216e0); (2312, 8%N, 0x9); (2320, 8%N, 0x20);   (2336, 8%N, 0x219e0);
(2344, 8%N, 0); (2352, 8%N, 0); (2360, 8%N, 0xffffffffffffffff);
(2368, 8%N, 0x21700); (2376, 8%N, 0x7); (2384, 8%N, 0x20);   (2400, 8%N, 0x219e0);
(2408, 8%N, 0); (2416, 8%N, 0); (2424, 8%N, 0xffffffffffffffff);
(2432, 8%N, 0x21720); (2440, 8%N, 0x18); (2448, 8%N, 0x40);   (2464, 8%N, 0x219e0);
(2472, 8%N, 0); (2480, 8%N, 0); (2488, 8%N, 0xffffffffffffffff);
(2496, 8%N, 0x21760); (2504, 8%N, 0x9); (2512, 8%N, 0x20);   (2528, 8%N, 0x219e0);
(2536, 8%N, 0); (2544, 8%N, 0); (2552, 8%N, 0xffffffffffffffff);
(2560, 8%N, 0x21780); (2568, 8%N, 0x7); (2576, 8%N, 0x20);   (2592, 8%N, 0x219e0);
(2600, 8%N, 0); (2608, 8%N, 0); (2616, 8%N, 0xffffffffffffffff);
(2624, 8%N, 0x217a0); (2632, 8%N, 0x17); (2640, 8%N, 0x40);   (2656, 8%N, 0x219e0);
(2664, 8%N, 0); (2672, 8%N, 0); (2680, 8%N, 0xffffffffffffffff);
(2688, 8%N, 0x217e0); (2696, 8%N, 0x8); (2704, 8%N, 0x20);   (2720, 8%N, 0x219e0);
(2728, 8%N, 0); (2736, 8%N, 0); (2744, 8%N, 0xffffffffffffffff);
(2752, 8%N, 0x21800); (2760, 8%N, 0x7); (2768, 8%N, 0x20);   (2784, 8%N, 0x219e0);
(2792, 8%N, 0); (2800, 8%N, 0); (2808, 8%N, 0xffffffffffffffff);
(2816, 8%N, 0x21820); (2824, 8%N, 0x17); (2832, 8%N, 0x40);   (2848, 8%N, 0x219e0);
(2856, 8%N, 0); (2864, 8%N, 0); (2872, 8%N, 0xffffffffffffffff);
(2880, 8%N, 0x21860); (2888, 8%N, 0x8); (2896, 8%N, 0x20);   (2912, 8%N, 0x219e0);
(2920, 8%N, 0); (2928, 8%N, 0); (2936, 8%N, 0xffffffffffffffff);
(2944, 8%N, 0x21880); (2952, 8%N, 0x7); (2960, 8%N, 0x20);   (2976, 8%N, 0x219e0);
(2984, 8%N, 0); (2992, 8%N, 0); (3000, 8%N, 0xffffffffffffffff);
(3008, 8%N, 0x218a0); (3016, 8%N, 0x18); (3024, 8%N, 0x40);   (3040, 8%N, 0x219e0);
(3048, 8%N, 0); (3056, 8%N, 0); (3064, 8%N, 0xffffffffffffffff);
(3072, 8%N, 0x218e0); (3080, 8%N, 0x8); (3088, 8%N, 0x20);   (3104, 8%N, 0x219e0);
(3112, 8%N, 0); (3120, 8%N, 0); (3128, 8%N, 0xffffffffffffffff);
(3136, 8%N, 0x21900); (3144, 8%N, 0x20); (3152, 8%N, 0x40);   (3168, 8%N, 0x219e0);
(3176, 8%N, 0); (3184, 8%N, 0); (3192, 8%N, 0xffffffffffffffff);
(3200, 8%N, 0x21940); (3208, 8%N, 0x20); (3216, 8%N, 0x40);   (3232, 8%N, 0x219e0);
(3240, 8%N, 0); (3248, 8%N, 0); (3256, 8%N, 0xffffffffffffffff);
(3264, 8%N, 0x21980); (3272, 8%N, 0x38); (3280, 8%N, 0x60);   (3296, 8%N, 0x219e0);
(3304, 8%N, 0); (3312, 8%N, 0); (3320, 8%N, 0xffffffffffffffff);
(3328, 8%N, 0x21a20); (3336, 8%N, 0x20); (3344, 8%N, 0x40);   (3360, 8%N, 0x21aa0);
(3368, 8%N, 0); (3376, 8%N, 0); (3384, 8%N, 0xffffffffffffffff);
(3392, 8%N, 0x21a60); (3400, 8%N, 0x20); (3408, 8%N, 0x40);   (3424, 8%N, 0x21aa0);
(3432, 8%N, 0); (3440, 8%N, 0); (3448, 8%N, 0xffffffffffffffff);
(3456, 8%N, 0x9f580); (3464, 8%N, 0x70); (3472, 8%N, 0xa0);   (3488, 8%N, 0x219e0);
(3496, 8%N, 0); (3504, 8%N, 0); (3512, 8%N, 0xffffffffffffffff);
(3520, 8%N, 0x9f620); (3528, 8%N, 0xcb8); (3536, 8%N, 0xfe0);   (3552, 8%N, 0x219e0);
(3560, 8%N, 0); (3568, 8%N, 0); (3576, 8%N, 0xffffffffffffffff);
(3584, 8%N, 0xa0600); (3592, 8%N, 0x108); (3600, 8%N, 0x160);   (3616, 8%N, 0x219e0);
(3624, 8%N, 0); (3632, 8%N, 0); (3640, 8%N, 0xffffffffffffffff)]);
(0xa6ed0, 8, [(0, 8%N, 0x101010000000001)]);
(0xa6f00, 8, [(0, 8%N, 0x1000100000000)]);
(0xa8f1c, 1, [(0, 1%N, 1)]);
(0xa96b8, 8, [(0, 8%N, 0x7fff8000)]);
(0xaa398, 1, [(0, 1%N, 1)]);
(0xaa3a0, 24, [(0, 8%N, 0x7fffffffffff); (8, 8%N, 0); (16, 8%N, 0)]);
(0x139160, 8, [(0, 8%N, 0x1000)]);
(0x13b260, 8, [(0, 8%N, 0xffffffffffffffff)]) ].
Definition ro_chunk (base : Z) (c : Z * N * Z) : YP09.chunk := YP09.mkChunk (base + fst (fst c)) (CVal (snd (fst c)) (SLit (snd c))).
Definition ro_region (r : Z * Z * list (Z * N * Z)) : YP09.region :=
YP09.mkRegion None (fst (fst r)) (fst (fst r) + snd (fst r)) (fst (fst r)) (fst (fst r)) (map (ro_chunk (fst (fst r))) (snd r)).
Definition X2_STK : Z := 272.
Definition x2_shw : list (Z * Z) := [(0x7fffc228, 12); (0x7fffc23c, 256); (0x7fffc344, 16); (0x8000beb0, 572); (0x8000ca34, 456)].
Definition shw_region (w : Z * Z) : YP09.region :=
YP09.mkRegion None (fst w) (fst w + snd w) (fst w) (fst w + snd w) [].
Definition x2_regions : smem :=
YP09.mkRegion (Some 2%nat) (- X2_STK) 0 (- X2_STK) 0 []
:: cellr 0xa6000 8 (SLit 1) true
:: cellr 0xa6f70 8 (SLit 0) true
:: map shw_region x2_shw ++ map ro_region x2_rodata.
Definition ss_x2 : sstate := mkSS X2_PC sr_atoms x2_regions None (mkFacts [(2%nat, mkAF (2 ^ 44) (2 ^ 47) 4)] [] []).
Definition x2_st : sstate := Eval vm_compute in fst (sym_runN tfibsegs tbl2 FUEL ss_x2).
Lemma x2_run : sym_runN tfibsegs tbl2 FUEL ss_x2 = (x2_st, RS_stopped (SR_jalr (SOff 1 0))).
Proof. vm_compute. reflexivity. Qed.
Lemma x2_phase : forall (W : world tfibsegs) E ss ss' st ms md,
st_ok tfibsegs E ss (restrict (w_H W) ms) ->
sym_runN tfibsegs tbl2 FUEL ss = (ss', st) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1)
| _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E ss ss' st ms md HS Hrun.
eapply (SRr_run_gen tfibsegs tbl2 tbl2_ok YF0x.Hwx_tfa W FUEL E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|].
split; [exact HS1|]. split; [exact HF | exact HFr].
Qed.
Definition const_chk (ly : alayout) (a : Z) (n : N) (v : Z) : bool :=
match cell_lookup (Tfib_const ly) (ANum a) with
| Some (ACell (ANum a') w' (AV (ANum v'))) => (a' =? a) && Nat.eqb w' (N.to_nat n) && (v' =? v)
| _ => false
end.
Lemma const_chk_sound : forall ly a n v, const_chk ly a n v = true ->
cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) (N.to_nat n) (AV (ANum v))).
Proof.
intros ly a n v H. unfold const_chk in H.
destruct (cell_lookup (Tfib_const ly) (ANum a)) as [[e w av]|]; [|discriminate].
destruct e; try discriminate. destruct av as [e'| ]; try discriminate. destruct e'; try discriminate.
apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply Z.eqb_eq in H1. apply Nat.eqb_eq in H2. apply Z.eqb_eq in H3. subst. reflexivity.
Qed.
Definition rodata_chk (ly : alayout) : bool :=
forallb (fun r => (0 <=? fst (fst r)) && (fst (fst r) + snd (fst r) <=? 2 ^ 47) &&
forallb (fun c => const_chk ly (fst (fst r) + fst (fst c)) (snd (fst c)) (snd c)
&& (0 <=? snd c) && (snd c <? 2 ^ (8 * Z.of_N (snd (fst c)))) && (Z.of_N (snd (fst c)) <=? 8)) (snd r))
x2_rodata.
Lemma rodata_chk_true : forall ly, rodata_chk ly = true.
Proof. intros ly. vm_compute. reflexivity. Qed.
Fixpoint zrange (lo : Z) (n : nat) : list Z := match n with O => [] | S k => lo :: zrange (lo + 1) k end.
Lemma In_zrange : forall n lo a, lo <= a < lo + Z.of_nat n -> In a (zrange lo n).
Proof.
induction n as [|n IH]; intros lo a Ha; [lia|]. cbn [zrange].
destruct (Z.eq_dec a lo) as [->|Hne]; [left; reflexivity | right]. apply IH. lia.
Qed.
Definition x2_shw_const : list (Z * Z) :=
[(0x7fffc228, 8); (0x7fffc231, 3); (0x7fffc23c, 16); (0x7fffc24d, 3); (0x7fffc251, 3); (0x7fffc256, 6);
(0x7fffc25d, 7); (0x7fffc265, 3); (0x7fffc26a, 2); (0x7fffc26d, 3); (0x7fffc272, 6); (0x7fffc279, 7);
(0x7fffc282, 10); (0x7fffc28e, 14); (0x7fffc29f, 5); (0x7fffc2a5, 3); (0x7fffc2ab, 9); (0x7fffc2b6, 6);
(0x7fffc2bd, 7); (0x7fffc2c7, 5); (0x7fffc2cd, 7); (0x7fffc2d7, 5); (0x7fffc2dd, 7); (0x7fffc2e7, 5);
(0x7fffc2ed, 7); (0x7fffc2f6, 6); (0x7fffc2fd, 7); (0x7fffc306, 6); (0x7fffc30d, 7); (0x7fffc317, 5);
(0x7fffc31d, 3); (0x7fffc324, 4); (0x7fffc32c, 4); (0x7fffc337, 5); (0x7fffc348, 4); (0x7fffc350, 4);
(0x8000bebe, 6); (0x8000c05b, 101); (0x8000c0e1, 11); (0x8000ca34, 456)].
Definition x2_shbytes : list Z := flat_map (fun w => zrange (fst w) (Z.to_nat (snd w))) x2_shw_const.
Definition shbyte_chk (ly : alayout) : bool :=
forallb (fun a => match cell_lookup (Tfib_const ly) (ANum a) with
| Some (ACell (ANum a') 1%nat (AV (ANum v))) => (a' =? a) && (0 <=? v) && (v <? 256)
| _ => false end) x2_shbytes.
Lemma shbyte_chk_true : forall ly, shbyte_chk ly = true.
Proof. intros ly. vm_compute. reflexivity. Qed.
Definition x2_shw_zero : list (Z * Z) :=
[(0x7fffc230, 1); (0x7fffc24c, 1); (0x7fffc250, 1); (0x7fffc254, 2); (0x7fffc25c, 1); (0x7fffc264, 1);
(0x7fffc268, 2); (0x7fffc26c, 1); (0x7fffc270, 2); (0x7fffc278, 1); (0x7fffc280, 2); (0x7fffc28c, 2);
(0x7fffc29c, 3); (0x7fffc2a4, 1); (0x7fffc2a8, 3); (0x7fffc2b4, 2); (0x7fffc2bc, 1); (0x7fffc2c4, 3);
(0x7fffc2cc, 1); (0x7fffc2d4, 3); (0x7fffc2dc, 1); (0x7fffc2e4, 3); (0x7fffc2ec, 1); (0x7fffc2f4, 2);
(0x7fffc2fc, 1); (0x7fffc304, 2); (0x7fffc30c, 1); (0x7fffc314, 3); (0x7fffc31c, 1); (0x7fffc320, 4);
(0x7fffc328, 4); (0x7fffc330, 7); (0x7fffc344, 4); (0x7fffc34c, 4); (0x8000beb0, 14); (0x8000bec4, 407);
(0x8000c0c0, 33)].
Definition x2_zbytes : list Z := flat_map (fun w => zrange (fst w) (Z.to_nat (snd w))) x2_shw_zero.
Definition x2_zsh_hit (a : Z) (r : Z * Z) : bool :=
(shadow_of_addr SHADOW_OFF (fst r) <=? a) && (a <? shadow_of_addr SHADOW_OFF (fst r) + snd r / 8).
Definition x2_zbyte_chk : bool := forallb (fun a => existsb (x2_zsh_hit a) Tfib_zero_shadow) x2_zbytes.
Lemma x2_zbyte_chk_true : x2_zbyte_chk = true.
Proof. vm_compute. reflexivity. Qed.
Definition x2_inb (a : Z) (l : list Z) : bool := existsb (Z.eqb a) l.
Lemma x2_inb_In : forall a l, x2_inb a l = true -> In a l.
Proof. intros a l H. unfold x2_inb in H. apply existsb_exists in H as (x & Hx & He). apply Z.eqb_eq in He. subst x. exact Hx. Qed.
Definition x2_cover_chk : bool :=
forallb (fun w => forallb (fun o => x2_inb o x2_shbytes || x2_inb o x2_zbytes) (zrange (fst w) (Z.to_nat (snd w)))) x2_shw.
Lemma x2_cover_chk_true : x2_cover_chk = true.
Proof. vm_compute. reflexivity. Qed.
Section S.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : CtrlTSyms B.
Hypothesis MU0 : forall ly, cell_lookup (Tfib_const ly) (ANum 0xa6f70) = Some (ACell (ANum 0xa6f70) 8 (AV (ANum 0))).
Lemma rodata_ok : forall ly S (H : word -> bool) mem E,
ARm B ly S (aview tfibsegs H mem) -> Forall (region_ok tfibsegs E (mrestrict H mem)) (map ro_region x2_rodata).
Proof.
intros ly S H mem E HM. pose proof (rodata_chk_true ly) as Hc. unfold rodata_chk in Hc.
rewrite forallb_forall in Hc. apply Forall_map. apply Forall_forall. intros [[base sz] cs] Hin.
specialize (Hc _ Hin). cbn [fst snd] in Hc. apply andb_prop in Hc as [Hc Hcs]. apply andb_prop in Hc as [H0 Hhi].
apply Z.leb_le in H0. apply Z.leb_le in Hhi.
unfold ro_region, region_ok. cbn [fst snd YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
rewrite forallb_forall in Hcs. apply Forall_map. apply Forall_forall. intros [[off n] v] Hc'.
specialize (Hcs _ Hc'). cbn [fst snd] in Hcs.
apply andb_prop in Hcs as [Hcs H4]. apply andb_prop in Hcs as [Hcs H3]. apply andb_prop in Hcs as [H1 H2].
apply Z.leb_le in H2. apply Z.ltb_lt in H3. apply Z.leb_le in H4.
unfold ro_chunk. cbn [fst snd].
eapply (chunk_ok_val tfibsegs E _ 0 (base + off) n (SLit v) v); [reflexivity | lia | lia |].
rewrite Z.add_0_l. exact (tfib_const_lookup B TB ly S H mem (base + off) (N.to_nat n) v HM (const_chk_sound _ _ _ _ H1)).
Qed.
Lemma shbytes_present : forall ly S (H : word -> bool) mem a,
ARm B ly S (aview tfibsegs H mem) -> In a x2_shbytes -> exists b, mbyte tfibsegs (mrestrict H mem) a = Some b.
Proof.
intros ly S H mem a HM Hin. pose proof (shbyte_chk_true ly) as Hc. unfold shbyte_chk in Hc.
rewrite forallb_forall in Hc. specialize (Hc a Hin). cbn beta in Hc.
destruct (cell_lookup (Tfib_const ly) (ANum a)) as [[e w av]|] eqn:HL; [|discriminate].
destruct e; try discriminate. destruct w as [|[|w]]; try discriminate.
destruct av as [e'| ]; try discriminate. destruct e'; try discriminate.
apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _]. apply Z.eqb_eq in Hc. subst.
pose proof (tfib_const_lookup B TB ly S H mem a 1 _ HM HL) as Hv.
specialize (Hv 0%nat ltac:(lia)). rewrite Z.add_0_r in Hv. eexists. exact Hv.
Qed.
Lemma zbytes_present : forall ly S (H : word -> bool) mem a,
ARm B ly S (aview tfibsegs H mem) -> In a x2_zbytes -> exists b, mbyte tfibsegs (mrestrict H mem) a = Some b.
Proof.
intros ly S H mem a HM Hin. pose proof x2_zbyte_chk_true as Hc. unfold x2_zbyte_chk in Hc.
rewrite forallb_forall in Hc. specialize (Hc a Hin). cbn beta in Hc. apply existsb_exists in Hc as ([lo len] & Hr & Hh).
unfold x2_zsh_hit in Hh. cbn [fst snd] in Hh. apply andb_prop in Hh as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
pose proof (proj1 (Forall_forall _ _) (am_zshadow B ly S _ HM) (lo, len)
ltac:(unfold zero_shadow_ranges; right; rewrite (ts_zsh _ TB); exact Hr)) as HZ.
specialize (HZ (a - shadow_of_addr SHADOW_OFF lo) ltac:(cbn [fst snd]; lia)). cbn [fst snd] in HZ.
replace (shadow_of_addr SHADOW_OFF lo + (a - shadow_of_addr SHADOW_OFF lo)) with a in HZ by lia.
unfold aview in HZ. destruct (mbyte tfibsegs (mrestrict H mem) a) as [b|]; [exists b; reflexivity | discriminate].
Qed.
Lemma shbyte0_present : forall ly S (H : word -> bool) mem,
ARm B ly S (aview tfibsegs H mem) -> exists b, mbyte tfibsegs (mrestrict H mem) 0x7fffc230 = Some b.
Proof.
intros ly S H mem HM. apply (zbytes_present ly S H mem _ HM). apply x2_inb_In. vm_compute. reflexivity.
Qed.
Lemma shw_ok : forall ly S (H : word -> bool) mem E,
ARm B ly S (aview tfibsegs H mem) -> Forall (region_ok tfibsegs E (mrestrict H mem)) (map shw_region x2_shw).
Proof.
intros ly S H mem E HM. apply Forall_map. apply Forall_forall. intros [lo n] Hin.
pose proof x2_cover_chk_true as Hc. unfold x2_cover_chk in Hc. rewrite forallb_forall in Hc.
specialize (Hc _ Hin). cbn [fst snd] in Hc. rewrite forallb_forall in Hc.
assert (Hr : 0x5fe000 <= lo /\ 0 <= n /\ lo + n <= 2 ^ 47).
{ cbn in Hin. repeat (destruct Hin as [Hq|Hin]; [injection Hq as <- <-; lia|]). destruct Hin. }
unfold shw_region, region_ok. cbn [fst snd YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. rewrite Z.add_0_l.
assert (Hb2 : exists b, mbyte tfibsegs (mrestrict H mem) o = Some b).
{ specialize (Hc o (In_zrange (Z.to_nat n) lo o ltac:(rewrite Z2Nat.id by lia; lia))). cbn beta in Hc.
apply orb_prop in Hc as [Hc|Hc]; [apply (shbytes_present ly S H mem o HM) | apply (zbytes_present ly S H mem o HM)]; exact (x2_inb_In _ _ Hc). }
destruct Hb2 as [b Hb].
apply (mbyte_high_writable _ o b); [unfold TFIB_IMG_END; lia | exact Hb].
Qed.
Lemma zi8_14ea00 : wseg_ok tfibsegs (Z_to_bv 64 0xa6000) (Z.to_nat 8) = true. Proof. vm_compute. reflexivity. Qed.
Lemma zi8_14f970 : wseg_ok tfibsegs (Z_to_bv 64 0xa6f70) (Z.to_nat 8) = true. Proof. vm_compute. reflexivity. Qed.
Lemma x2_windows : forall E a, in_wrange E (ss_mem ss_x2) a ->
(bv_unsigned (ew E 2) - X2_STK <= a < bv_unsigned (ew E 2)) \/ XW2 a.
Proof.
intros E a Hin. destruct (in_wrange_windows E _ a Hin) as (b & lo & hi & Ht & Hr).
cbn in Ht. unfold XW2. unfold X2_STK in *.
repeat (destruct Ht as [Hq|Ht]; [injection Hq as <- <- <-; cbn [base_val] in Hr; lia|]). destruct Ht.
Qed.
Theorem x2_realizes : xret_realizes_noar tfibsegs B X2_PC XW2 XTRUE.
Proof.
intros ly S W regs mem md HPRE _. pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof YF0x.Hwx_tfa as Hwx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HES : ESTACK = 4096) by reflexivity.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
pose proof (proj1 HAR) as HM.
unfold cfg_at. change (w64 X2_PC) with (Z_to_bv 64 X2_PC).
set (sp0 := spZ regs) in *.
assert (Hsp44 : 2 ^ 44 <= sp0 <= 2 ^ 47) by lia.
set (E := Ereg regs (@nil word)).
assert (E2 : bv_unsigned (ew E 2) = sp0) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (HS0 : st_ok tfibsegs E ss_x2 (restrict (w_H W) (mkst regs (Z_to_bv 64 X2_PC) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_x2. apply (entry_st_ok_full tfibsegs); change (Ereg regs []) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold x2_regions. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_app; split; [exact (shw_ok ly S _ mem E HM) | exact (rodata_ok ly S _ mem E HM)]]]].
+ apply (region_ok_stack tfibsegs E _ 2 sp0 (- X2_STK)); [exact E2 | unfold X2_STK; lia | lia |].
intros a Ha. apply YE2y.apresent_writable. apply HpresE. unfold X2_STK in Ha. lia.
+ unfold region_ok, cellr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val Z.of_N].
split; [lia|]. split; [lia|]. split; [intros o Ho; rewrite Z.add_0_l; apply (wseg_writable _ 0xa6000 8); [exact zi8_14ea00 | lia | lia | lia | lia] |].
constructor; [|constructor]. eapply (chunk_ok_val tfibsegs E _ 0 _ 8 _ 1); [reflexivity | zside | zside |].
rewrite Z.add_0_l. exact (tfib_const_lookup B TB ly S _ mem 0xa6000 8 1 HM ltac:(vm_compute; reflexivity)).
+ unfold region_ok, cellr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val Z.of_N].
split; [lia|]. split; [lia|]. split; [intros o Ho; rewrite Z.add_0_l; apply (wseg_writable _ 0xa6f70 8); [exact zi8_14f970 | lia | lia | lia | lia] |].
constructor; [|constructor]. eapply (chunk_ok_val tfibsegs E _ 0 _ 8 _ 0); [reflexivity | zside | zside |].
rewrite Z.add_0_l. exact (tfib_const_lookup B TB ly S _ mem 0xa6f70 8 0 HM (MU0 ly)).
- apply pairwise_disjoint_of_extents. unfold x2_regions, x2_shw, x2_rodata, cellr, shw_region, ro_region, extent_of_region.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2. unfold X2_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2.
change (2 ^ 4) with 16. repeat split; lia. }
eapply SRr_bind; [apply (x2_phase W E ss_x2 x2_st _ _ md HS0 x2_run)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1).
eapply (SRr_ret_at tfibsegs tbl2 tbl2_ok Hwx W E); [exact HS1 | reflexivity | vm_compute; reflexivity |].
intros mat'. rewrite wvb_wvb.
assert (MEQ : forall x : word, ~ ((sp0 - X2_STK <= bv_unsigned x < sp0) \/ XW2 (bv_unsigned x)) -> ms_mem ms1 x = mem x).
{ intros x Hx. apply HF1. intros Hin. apply Hx. destruct (x2_windows E _ Hin) as [Hw|Hw]; rewrite ?E2 in Hw; [left; exact Hw | right; exact Hw]. }
assert (MEQr : forall x : word, ~ ((sp0 - X2_STK <= bv_unsigned x < sp0) \/ XW2 (bv_unsigned x)) ->
mrestrict (w_H W) (ms_mem ms1) x = mrestrict (w_H W) mem x).
{ intros x Hx. apply HFr1. intros Hin. apply Hx. destruct (x2_windows E _ Hin) as [Hw|Hw]; rewrite ?E2 in Hw; [left; exact Hw | right; exact Hw]. }
assert (AV : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - X2_STK <= a < sp0) -> ~ XW2 a ->
aview tfibsegs (w_H W) (ms_mem ms1) a = aview tfibsegs (w_H W) mem a).
{ intros a Hr H1 H2. apply aview_eq_of. apply MEQr. rewrite unsigned_lit_small by lia. tauto. }
assert (PRS : forall a, sp0 - X2_STK <= a < sp0 -> apresent (w_H W) (ms_mem ms1) a).
{ intros a Ha. unfold X2_STK in Ha. apply (apresent_of_writable (w_H W) (ms_mem ms1) a ltac:(lia) (high_not_img a ltac:(lia))).
destruct HS1 as (_ & _ & _ & _ & _ & _ & _ & (_ & Hrs & _) & _).
pose proof (Forall_inv Hrs) as Hr0. destruct Hr0 as (_ & _ & Hw & _).
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw. rewrite E2 in Hw. unfold X2_STK in Hw.
replace a with (sp0 + (a - sp0)) by lia. apply Hw. lia. }
rreg HS1 (1%bv : bv 5) Q1. replace (ew E 1) with (getr regs 1) in Q1 by (symmetry; exact (ew_Ereg_nat regs [] 1 1%bv eq_refl)).
replace (v_jalr (getr (ms_regs ms1) 1) 0) with (w64 (raZ regs)) by (rewrite Q1; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; symmetry; exact Hra).
split; [reflexivity|]. exists (ms_regs ms1), (ms_mem ms1), (with_vm_backing (m_vm_lazy md) mat' md).
split; [reflexivity|].
split; [|split; [|split]].
- exact (aregs_preserved_of_st_ok _ E _ _ regs [] HS1 ltac:(split; [intros i Hi; reflexivity | reflexivity]) ltac:(vm_compute; reflexivity)).
- apply with_vm_backing_same.
- intros a Hr Hs Hx. apply AV; [exact Hr | unfold X2_STK; unfold sp0 in *; lia | exact Hx].
- intros a Hr Hx Hp.
destruct (Z_lt_le_dec a (sp0 - X2_STK)) as [L1|L1]; [| destruct (Z_lt_le_dec a sp0) as [L2|L2]; [apply PRS; lia|]].
all: destruct Hp as [Hh [b Hb]]; split; [exact Hh|]; exists b; rewrite MEQ; [exact Hb|]; rewrite unsigned_lit_small by lia; intros [Hw|Hw]; [lia | exact (Hx Hw)].
Qed.
End S.
End d.
