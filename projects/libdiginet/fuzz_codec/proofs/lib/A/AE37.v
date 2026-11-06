(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AE37.v, with its module paths changed, names TfibSyms -> GrantSyms and its addresses moved to libreac/fuzz_grant's ASan build; shw_ok takes each window byte from a constant shadow cell or a range start-up leaves marked usable. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/libreac/fuzz_grant/proofs/lib/A/AE37.v (donor image sha256 c2c7559b29bd), with its module paths changed and names GrantSyms -> TfibSyms; every image numeral re-derived for libdiginet/fuzz_codec.asan (sha256 7d470194ffdbde8b) from cgif's lib/A/AE37.v at c8557374ad2e by the rule of libreac/fuzz_decode's provenance/startup-gen/A/exitdrv (a Theorem Labs tool + symtab name, a .got slot by the pointer it holds, the shadow of the unit's own globals): the walk's globals array is fuzz_codec's 40 descriptors at 0xa23c0 (all 8 fields), its shadow windows are those globals' and that array's; every odr_indicator is -1, so the exit writes no ODR byte and there is no ODR region. *)
(* Read from: fuzz_codec.asan (libdiginet/fuzz_codec asan) sha256 7d470194ffdbde8b30a9810840f8e81d620ba1c555d510c475daeff37548a422; unstripped twin sha256 b28356da1a6547814e3a3c56e2d9e065e4f5b45715ccb5a236942cda3471fe1d *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AB1v AE34 AF0l AF0m AE3g AE2p AE3i AE3h AE3m AE23 AF0x AE20 AE2y AE7f.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YM05.
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
(0x9daf0, 72, [(0, 8%N, 0x135f20); (8, 8%N, 0x9f9b0); (16, 8%N, 0x137fa8); (24, 8%N, 0xa3c78); (32, 8%N, 0xa6478);
(40, 8%N, 0xa7168); (48, 8%N, 0xa7170); (56, 8%N, 0xa7160); (64, 8%N, 0x9f978)]);
(0x9e788, 16, [(0, 8%N, 0xa23c0); (8, 8%N, 0xa2dc0)]);
(0x9f978, 8, [(0, 8%N, 0x96efc)]);
(0xa23c0, 2560, [(0, 8%N, 0x20f40); (8, 8%N, 0xc); (16, 8%N, 0x20); (24, 8%N, 0x15888);
(32, 8%N, 0x21340); (40, 8%N, 0); (48, 8%N, 0); (56, 8%N, 0xffffffffffffffff);
(64, 8%N, 0x20f60); (72, 8%N, 0x9); (80, 8%N, 0x20); (88, 8%N, 0x1c116);
(96, 8%N, 0x21340); (104, 8%N, 0); (112, 8%N, 0); (120, 8%N, 0xffffffffffffffff);
(128, 8%N, 0x20f80); (136, 8%N, 0x9); (144, 8%N, 0x20); (152, 8%N, 0x2063f);
(160, 8%N, 0x21340); (168, 8%N, 0); (176, 8%N, 0); (184, 8%N, 0xffffffffffffffff);
(192, 8%N, 0x20fa0); (200, 8%N, 0x8); (208, 8%N, 0x20); (216, 8%N, 0x13733);
(224, 8%N, 0x21340); (232, 8%N, 0); (240, 8%N, 0); (248, 8%N, 0xffffffffffffffff);
(256, 8%N, 0x20fc0); (264, 8%N, 0xa); (272, 8%N, 0x20); (280, 8%N, 0x1d0d0);
(288, 8%N, 0x21340); (296, 8%N, 0); (304, 8%N, 0); (312, 8%N, 0xffffffffffffffff);
(320, 8%N, 0x20fe0); (328, 8%N, 0x1); (336, 8%N, 0x20); (344, 8%N, 0x18829);
(352, 8%N, 0x21340); (360, 8%N, 0); (368, 8%N, 0); (376, 8%N, 0xffffffffffffffff);
(384, 8%N, 0x21000); (392, 8%N, 0x7); (400, 8%N, 0x20); (408, 8%N, 0x1a55e);
(416, 8%N, 0x21340); (424, 8%N, 0); (432, 8%N, 0); (440, 8%N, 0xffffffffffffffff);
(448, 8%N, 0x21020); (456, 8%N, 0x3); (464, 8%N, 0x20); (472, 8%N, 0x113a4);
(480, 8%N, 0x21340); (488, 8%N, 0); (496, 8%N, 0); (504, 8%N, 0xffffffffffffffff);
(512, 8%N, 0x21040); (520, 8%N, 0x6); (528, 8%N, 0x20); (536, 8%N, 0x1669f);
(544, 8%N, 0x21340); (552, 8%N, 0); (560, 8%N, 0); (568, 8%N, 0xffffffffffffffff);
(576, 8%N, 0x21060); (584, 8%N, 0x6); (592, 8%N, 0x20); (600, 8%N, 0x1f973);
(608, 8%N, 0x21340); (616, 8%N, 0); (624, 8%N, 0); (632, 8%N, 0xffffffffffffffff);
(640, 8%N, 0x21080); (648, 8%N, 0x5); (656, 8%N, 0x20); (664, 8%N, 0x113ab);
(672, 8%N, 0x21340); (680, 8%N, 0); (688, 8%N, 0); (696, 8%N, 0xffffffffffffffff);
(704, 8%N, 0x210a0); (712, 8%N, 0x6); (720, 8%N, 0x20); (728, 8%N, 0x19eb4);
(736, 8%N, 0x21340); (744, 8%N, 0); (752, 8%N, 0); (760, 8%N, 0xffffffffffffffff);
(768, 8%N, 0x210c0); (776, 8%N, 0x7); (784, 8%N, 0x20); (792, 8%N, 0x1f97b);
(800, 8%N, 0x21340); (808, 8%N, 0); (816, 8%N, 0); (824, 8%N, 0xffffffffffffffff);
(832, 8%N, 0x210e0); (840, 8%N, 0x4); (848, 8%N, 0x20); (856, 8%N, 0x1de4a);
(864, 8%N, 0x21340); (872, 8%N, 0); (880, 8%N, 0); (888, 8%N, 0xffffffffffffffff);
(896, 8%N, 0x21100); (904, 8%N, 0x8); (912, 8%N, 0x20); (920, 8%N, 0x1c11b);
(928, 8%N, 0x21340); (936, 8%N, 0); (944, 8%N, 0); (952, 8%N, 0xffffffffffffffff);
(960, 8%N, 0x21120); (968, 8%N, 0x7); (976, 8%N, 0x20); (984, 8%N, 0x1976e);
(992, 8%N, 0x21340); (1000, 8%N, 0); (1008, 8%N, 0); (1016, 8%N, 0xffffffffffffffff);
(1024, 8%N, 0x21140); (1032, 8%N, 0x7); (1040, 8%N, 0x20); (1048, 8%N, 0x1b95e);
(1056, 8%N, 0x21340); (1064, 8%N, 0); (1072, 8%N, 0); (1080, 8%N, 0xffffffffffffffff);
(1088, 8%N, 0x21160); (1096, 8%N, 0x6); (1104, 8%N, 0x20); (1112, 8%N, 0x11b56);
(1120, 8%N, 0x21340); (1128, 8%N, 0); (1136, 8%N, 0); (1144, 8%N, 0xffffffffffffffff);
(1152, 8%N, 0x21180); (1160, 8%N, 0x5); (1168, 8%N, 0x20); (1176, 8%N, 0x11b5e);
(1184, 8%N, 0x21340); (1192, 8%N, 0); (1200, 8%N, 0); (1208, 8%N, 0xffffffffffffffff);
(1216, 8%N, 0x211a0); (1224, 8%N, 0x6); (1232, 8%N, 0x20); (1240, 8%N, 0x17e2c);
(1248, 8%N, 0x21340); (1256, 8%N, 0); (1264, 8%N, 0); (1272, 8%N, 0xffffffffffffffff);
(1280, 8%N, 0x211c0); (1288, 8%N, 0x6); (1296, 8%N, 0x20); (1304, 8%N, 0x19ebc);
(1312, 8%N, 0x21340); (1320, 8%N, 0); (1328, 8%N, 0); (1336, 8%N, 0xffffffffffffffff);
(1344, 8%N, 0x211e0); (1352, 8%N, 0x5); (1360, 8%N, 0x20); (1368, 8%N, 0x147c5);
(1376, 8%N, 0x21340); (1384, 8%N, 0); (1392, 8%N, 0); (1400, 8%N, 0xffffffffffffffff);
(1408, 8%N, 0x21200); (1416, 8%N, 0x6); (1424, 8%N, 0x20); (1432, 8%N, 0x13d23);
(1440, 8%N, 0x21340); (1448, 8%N, 0); (1456, 8%N, 0); (1464, 8%N, 0xffffffffffffffff);
(1472, 8%N, 0x21220); (1480, 8%N, 0x5); (1488, 8%N, 0x20); (1496, 8%N, 0x1373a);
(1504, 8%N, 0x21340); (1512, 8%N, 0); (1520, 8%N, 0); (1528, 8%N, 0xffffffffffffffff);
(1536, 8%N, 0x21240); (1544, 8%N, 0x5); (1552, 8%N, 0x20); (1560, 8%N, 0x16ee3);
(1568, 8%N, 0x21340); (1576, 8%N, 0); (1584, 8%N, 0); (1592, 8%N, 0xffffffffffffffff);
(1600, 8%N, 0x21260); (1608, 8%N, 0x4); (1616, 8%N, 0x20); (1624, 8%N, 0x10add);
(1632, 8%N, 0x21340); (1640, 8%N, 0); (1648, 8%N, 0); (1656, 8%N, 0xffffffffffffffff);
(1664, 8%N, 0x21280); (1672, 8%N, 0x5); (1680, 8%N, 0x20); (1688, 8%N, 0x17e34);
(1696, 8%N, 0x21340); (1704, 8%N, 0); (1712, 8%N, 0); (1720, 8%N, 0xffffffffffffffff);
(1728, 8%N, 0x212a0); (1736, 8%N, 0x6); (1744, 8%N, 0x20); (1752, 8%N, 0x17613);
(1760, 8%N, 0x21340); (1768, 8%N, 0); (1776, 8%N, 0); (1784, 8%N, 0xffffffffffffffff);
(1792, 8%N, 0x212c0); (1800, 8%N, 0x3); (1808, 8%N, 0x20); (1816, 8%N, 0x10ae5);
(1824, 8%N, 0x21340); (1832, 8%N, 0); (1840, 8%N, 0); (1848, 8%N, 0xffffffffffffffff);
(1856, 8%N, 0x212e0); (1864, 8%N, 0x6); (1872, 8%N, 0x20); (1880, 8%N, 0x13742);
(1888, 8%N, 0x21340); (1896, 8%N, 0); (1904, 8%N, 0); (1912, 8%N, 0xffffffffffffffff);
(1920, 8%N, 0x21300); (1928, 8%N, 0x6); (1936, 8%N, 0x20); (1944, 8%N, 0x113b3);
(1952, 8%N, 0x21340); (1960, 8%N, 0); (1968, 8%N, 0); (1976, 8%N, 0xffffffffffffffff);
(1984, 8%N, 0x21320); (1992, 8%N, 0x2); (2000, 8%N, 0x20); (2008, 8%N, 0x1239f);
(2016, 8%N, 0x21340); (2024, 8%N, 0); (2032, 8%N, 0); (2040, 8%N, 0xffffffffffffffff);
(2048, 8%N, 0x21360); (2056, 8%N, 0x9); (2064, 8%N, 0x20); (2072, 8%N, 0x1c116);
(2080, 8%N, 0x21560); (2088, 8%N, 0); (2096, 8%N, 0); (2104, 8%N, 0xffffffffffffffff);
(2112, 8%N, 0x21380); (2120, 8%N, 0x9); (2128, 8%N, 0x20); (2136, 8%N, 0x1e8ca);
(2144, 8%N, 0x21560); (2152, 8%N, 0); (2160, 8%N, 0); (2168, 8%N, 0xffffffffffffffff);
(2176, 8%N, 0x213a0); (2184, 8%N, 0x16c); (2192, 8%N, 0x1c0); (2200, 8%N, 0x18dcc);
(2208, 8%N, 0x21560); (2216, 8%N, 0); (2224, 8%N, 0); (2232, 8%N, 0xffffffffffffffff);
(2240, 8%N, 0x9d660); (2248, 8%N, 0x18); (2256, 8%N, 0x40); (2264, 8%N, 0x175f2);
(2272, 8%N, 0x21340); (2280, 8%N, 0); (2288, 8%N, 0); (2296, 8%N, 0xffffffffffffffff);
(2304, 8%N, 0x9d6a0); (2312, 8%N, 0x10); (2320, 8%N, 0x20); (2328, 8%N, 0x19765);
(2336, 8%N, 0x21340); (2344, 8%N, 0); (2352, 8%N, 0); (2360, 8%N, 0xffffffffffffffff);
(2368, 8%N, 0x9d6c0); (2376, 8%N, 0x10); (2384, 8%N, 0x20); (2392, 8%N, 0x16edb);
(2400, 8%N, 0x21340); (2408, 8%N, 0); (2416, 8%N, 0); (2424, 8%N, 0xffffffffffffffff);
(2432, 8%N, 0x9d6e0); (2440, 8%N, 0x1d0); (2448, 8%N, 0x240); (2456, 8%N, 0x1f963);
(2464, 8%N, 0x21340); (2472, 8%N, 0); (2480, 8%N, 0); (2488, 8%N, 0xffffffffffffffff);
(2496, 8%N, 0x9d920); (2504, 8%N, 0x30); (2512, 8%N, 0x60); (2520, 8%N, 0x1c123);
(2528, 8%N, 0x21560); (2536, 8%N, 0); (2544, 8%N, 0); (2552, 8%N, 0xffffffffffffffff)]);
(0xa3c90, 8, [(0, 8%N, 0x101010000000001)]);
(0xa3cc0, 8, [(0, 8%N, 0x1000100000000)]);
(0xa5cdc, 1, [(0, 1%N, 1)]);
(0xa6478, 8, [(0, 8%N, 0x7fff8000)]);
(0xa7158, 1, [(0, 1%N, 1)]);
(0xa7160, 24, [(0, 8%N, 0x7fffffffffff); (8, 8%N, 0); (16, 8%N, 0)]);
(0x135f20, 8, [(0, 8%N, 0x1000)]);
(0x138020, 8, [(0, 8%N, 0xffffffffffffffff)]) ].
Definition ro_chunk (base : Z) (c : Z * N * Z) : YP09.chunk := YP09.mkChunk (base + fst (fst c)) (CVal (snd (fst c)) (SLit (snd c))).
Definition ro_region (r : Z * Z * list (Z * N * Z)) : YP09.region :=
YP09.mkRegion None (fst (fst r)) (fst (fst r) + snd (fst r)) (fst (fst r)) (fst (fst r)) (map (ro_chunk (fst (fst r))) (snd r)).
Definition X2_STK : Z := 272.
Definition x2_shw : list (Z * Z) := [(0x7fffc1e8, 4); (0x7fffc1ec, 4); (0x7fffc1f0, 4); (0x7fffc1f4, 4); (0x7fffc1f8, 4); (0x7fffc1fc, 4); (0x7fffc200, 4); (0x7fffc204, 4); (0x7fffc208, 4); (0x7fffc20c, 4); (0x7fffc210, 4); (0x7fffc214, 4); (0x7fffc218, 4); (0x7fffc21c, 4); (0x7fffc220, 4); (0x7fffc224, 4); (0x7fffc228, 4); (0x7fffc22c, 4); (0x7fffc230, 4); (0x7fffc234, 4); (0x7fffc238, 4); (0x7fffc23c, 4); (0x7fffc240, 4); (0x7fffc244, 4); (0x7fffc248, 4); (0x7fffc24c, 4); (0x7fffc250, 4); (0x7fffc254, 4); (0x7fffc258, 4); (0x7fffc25c, 4); (0x7fffc260, 4); (0x7fffc264, 4); (0x7fffc26c, 4); (0x7fffc270, 4); (0x7fffc274, 56); (0x8000bacc, 8); (0x8000bad4, 4); (0x8000bad8, 4); (0x8000badc, 72); (0x8000bb24, 12); (0x8000c478, 320)].
Definition shw_region (w : Z * Z) : YP09.region :=
YP09.mkRegion None (fst w) (fst w + snd w) (fst w) (fst w + snd w) [].
Definition x2_regions : smem :=
YP09.mkRegion (Some 2%nat) (- X2_STK) 0 (- X2_STK) 0 []
:: cellr 0xa2dc0 8 (SLit 1) true
:: cellr 0xa3d30 8 (SLit 0) true
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
eapply (SRr_run_gen tfibsegs tbl2 tbl2_ok AF0x.Hwx_tfa W FUEL E ss ss' st ms md _ HS Hrun).
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
Definition x2_shbytes : list Z := flat_map (fun w => zrange (fst w) (Z.to_nat (snd w))) x2_shw.
Definition shc_cov (ly : alayout) (a : Z) : bool :=
match cell_lookup (Tfib_const ly) (ANum a) with
| Some (ACell (ANum a') 1%nat (AV (ANum v))) => (a' =? a) && (0 <=? v) && (v <? 256)
| _ => false end.
Definition zsh_cov (a : Z) : bool :=
existsb (fun r => (shadow_of_addr SHADOW_OFF (fst r) <=? a) && (a <? shadow_of_addr SHADOW_OFF (fst r) + snd r / 8)) Tfib_zero_shadow.
Definition shbyte_chk (ly : alayout) : bool := forallb (fun a => shc_cov ly a || zsh_cov a) x2_shbytes.
Lemma shbyte_chk_true : forall ly, shbyte_chk ly = true.
Proof. intros ly. vm_compute. reflexivity. Qed.
Section S.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Hypothesis MU0 : forall ly, cell_lookup (Tfib_const ly) (ANum 0xa3d30) = Some (ACell (ANum 0xa3d30) 8 (AV (ANum 0))).
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
Lemma shbyte_present : forall ly S (H : word -> bool) mem a,
ARm B ly S (aview tfibsegs H mem) -> In a x2_shbytes -> exists b, mbyte tfibsegs (mrestrict H mem) a = Some b.
Proof.
intros ly S H mem a HM Hin. pose proof (shbyte_chk_true ly) as Hc. unfold shbyte_chk in Hc.
rewrite forallb_forall in Hc. specialize (Hc a Hin). apply orb_prop in Hc as [Hc|Hc].
- unfold shc_cov in Hc.
destruct (cell_lookup (Tfib_const ly) (ANum a)) as [[e w av]|] eqn:HL; [|discriminate].
destruct e; try discriminate. destruct w as [|[|w]]; try discriminate.
destruct av as [e'| ]; try discriminate. destruct e'; try discriminate.
apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _]. apply Z.eqb_eq in Hc. subst.
pose proof (tfib_const_lookup B TB ly S H mem a 1 _ HM HL) as Hv.
specialize (Hv 0%nat ltac:(lia)). rewrite Z.add_0_r in Hv. eexists. exact Hv.
- unfold zsh_cov in Hc. apply existsb_exists in Hc as (r & Hr & Hb). apply andb_prop in Hb as [H1 H2].
apply Z.leb_le in H1. apply Z.ltb_lt in H2.
pose proof (proj1 (Forall_forall _ _) (am_zshadow B ly S _ HM) r
ltac:(unfold zero_shadow_ranges; right; rewrite (ts_zsh _ TB); exact Hr)) as HZ.
specialize (HZ (a - shadow_of_addr SHADOW_OFF (fst r)) ltac:(lia)).
replace (shadow_of_addr SHADOW_OFF (fst r) + (a - shadow_of_addr SHADOW_OFF (fst r))) with a in HZ by lia.
unfold aview in HZ. destruct (mbyte tfibsegs (mrestrict H mem) a) as [b|]; [exists b; reflexivity | discriminate].
Qed.
Lemma shw_ok : forall ly S (H : word -> bool) mem E,
ARm B ly S (aview tfibsegs H mem) -> Forall (region_ok tfibsegs E (mrestrict H mem)) (map shw_region x2_shw).
Proof.
intros ly S H mem E HM. apply Forall_map. apply Forall_forall. intros [lo n] Hin.
assert (Hr : 0x7fffc1e8 <= lo /\ lo + n <= 0x8000c5b8 /\ 0 <= n).
{ cbn in Hin. repeat (destruct Hin as [Hq|Hin]; [injection Hq as <- <-; lia|]). destruct Hin. }
unfold shw_region, region_ok. cbn [fst snd YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. rewrite Z.add_0_l.
destruct (shbyte_present ly S H mem o HM) as [b Hb].
{ unfold x2_shbytes. apply in_flat_map. exists (lo, n). split; [exact Hin|]. cbn [fst snd]. apply In_zrange. rewrite Z2Nat.id by lia. lia. }
apply (mbyte_high_writable _ o b); [unfold TFIB_IMG_END; lia | exact Hb].
Qed.
Lemma zi8_14ea00 : wseg_ok tfibsegs (Z_to_bv 64 0xa2dc0) (Z.to_nat 8) = true. Proof. vm_compute. reflexivity. Qed.
Lemma zi8_14f970 : wseg_ok tfibsegs (Z_to_bv 64 0xa3d30) (Z.to_nat 8) = true. Proof. vm_compute. reflexivity. Qed.
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
pose proof AF0x.Hwx_tfa as Hwx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HES : ESTACK = 4096) by reflexivity.
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
intros a Ha. apply AE2y.apresent_writable. apply HpresE. unfold X2_STK in Ha. lia.
+ unfold region_ok, cellr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val Z.of_N].
split; [lia|]. split; [lia|]. split; [intros o Ho; rewrite Z.add_0_l; apply (wseg_writable _ 0xa2dc0 8); [exact zi8_14ea00 | lia | lia | lia | lia] |].
constructor; [|constructor]. eapply (chunk_ok_val tfibsegs E _ 0 _ 8 _ 1); [reflexivity | zside | zside |].
rewrite Z.add_0_l. exact (tfib_const_lookup B TB ly S _ mem 0xa2dc0 8 1 HM ltac:(vm_compute; reflexivity)).
+ unfold region_ok, cellr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val Z.of_N].
split; [lia|]. split; [lia|]. split; [intros o Ho; rewrite Z.add_0_l; apply (wseg_writable _ 0xa3d30 8); [exact zi8_14f970 | lia | lia | lia | lia] |].
constructor; [|constructor]. eapply (chunk_ok_val tfibsegs E _ 0 _ 8 _ 0); [reflexivity | zside | zside |].
rewrite Z.add_0_l. exact (tfib_const_lookup B TB ly S _ mem 0xa3d30 8 0 HM (MU0 ly)).
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
