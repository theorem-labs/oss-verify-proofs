(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AE34 AF0l AF0m AE3g AE2p AE3i AE3h AE3m AE23 AF0x AE20 AE2y AE7f AsanNoAR.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import PcapImgEnd YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Notation tbl2 := tbl_x213 (only parsing).
Notation tbl2_ok := tbl_x213_ok (only parsing).
Definition x2_rodata : list (Z * Z * list (Z * N * Z)) :=
[ (0x103b8, 8, [(0, 8%N, 0xafffff00000fffff)]);
(0xa19b0, 72, [(0, 8%N, 0x139ee0); (8, 8%N, 0xa3888); (16, 8%N, 0x13bf68); (24, 8%N, 0xa7c38); (32, 8%N, 0xaa438);
(40, 8%N, 0xab128); (48, 8%N, 0xab130); (56, 8%N, 0xab120); (64, 8%N, 0xa3850)]);
(0xa2648, 16, [(0, 8%N, 0xa62a0); (8, 8%N, 0xa6d60)]);
(0xa3850, 8, [(0, 8%N, 0x9afa8)]);
(0xa62a0, 2752, [(0, 8%N, 0x20fa0); (8, 8%N, 0x5); (16, 8%N, 0x20); (32, 8%N, 0x21280);
(40, 8%N, 0); (48, 8%N, 0); (56, 8%N, 0xffffffffffffffff);
(64, 8%N, 0x20fc0); (72, 8%N, 0x1); (80, 8%N, 0x20); (96, 8%N, 0x21280);
(104, 8%N, 0); (112, 8%N, 0); (120, 8%N, 0xffffffffffffffff);
(128, 8%N, 0x20fe0); (136, 8%N, 0xc); (144, 8%N, 0x20); (160, 8%N, 0x21280);
(168, 8%N, 0); (176, 8%N, 0); (184, 8%N, 0xffffffffffffffff);
(192, 8%N, 0x21000); (200, 8%N, 0x5); (208, 8%N, 0x20); (224, 8%N, 0x21280);
(232, 8%N, 0); (240, 8%N, 0); (248, 8%N, 0xffffffffffffffff);
(256, 8%N, 0x21020); (264, 8%N, 0x6); (272, 8%N, 0x20); (288, 8%N, 0x21280);
(296, 8%N, 0); (304, 8%N, 0); (312, 8%N, 0xffffffffffffffff);
(320, 8%N, 0x21040); (328, 8%N, 0x9); (336, 8%N, 0x20); (352, 8%N, 0x21280);
(360, 8%N, 0); (368, 8%N, 0); (376, 8%N, 0xffffffffffffffff);
(384, 8%N, 0x21060); (392, 8%N, 0x6); (400, 8%N, 0x20); (416, 8%N, 0x21280);
(424, 8%N, 0); (432, 8%N, 0); (440, 8%N, 0xffffffffffffffff);
(448, 8%N, 0x21080); (456, 8%N, 0x18); (464, 8%N, 0x40); (480, 8%N, 0x21280);
(488, 8%N, 0); (496, 8%N, 0); (504, 8%N, 0xffffffffffffffff);
(512, 8%N, 0x210c0); (520, 8%N, 0x2); (528, 8%N, 0x20); (544, 8%N, 0x21280);
(552, 8%N, 0); (560, 8%N, 0); (568, 8%N, 0xffffffffffffffff);
(576, 8%N, 0x210e0); (584, 8%N, 0x10); (592, 8%N, 0x20); (608, 8%N, 0x21280);
(616, 8%N, 0); (624, 8%N, 0); (632, 8%N, 0xffffffffffffffff);
(640, 8%N, 0x21100); (648, 8%N, 0xf); (656, 8%N, 0x20); (672, 8%N, 0x21280);
(680, 8%N, 0); (688, 8%N, 0); (696, 8%N, 0xffffffffffffffff);
(704, 8%N, 0x21120); (712, 8%N, 0xf); (720, 8%N, 0x20); (736, 8%N, 0x21280);
(744, 8%N, 0); (752, 8%N, 0); (760, 8%N, 0xffffffffffffffff);
(768, 8%N, 0x21140); (776, 8%N, 0xb); (784, 8%N, 0x20); (800, 8%N, 0x21280);
(808, 8%N, 0); (816, 8%N, 0); (824, 8%N, 0xffffffffffffffff);
(832, 8%N, 0x21160); (840, 8%N, 0x9); (848, 8%N, 0x20); (864, 8%N, 0x21280);
(872, 8%N, 0); (880, 8%N, 0); (888, 8%N, 0xffffffffffffffff);
(896, 8%N, 0x21180); (904, 8%N, 0x10); (912, 8%N, 0x20); (928, 8%N, 0x21280);
(936, 8%N, 0); (944, 8%N, 0); (952, 8%N, 0xffffffffffffffff);
(960, 8%N, 0x211a0); (968, 8%N, 0x8); (976, 8%N, 0x20); (992, 8%N, 0x21280);
(1000, 8%N, 0); (1008, 8%N, 0); (1016, 8%N, 0xffffffffffffffff);
(1024, 8%N, 0x211c0); (1032, 8%N, 0x5); (1040, 8%N, 0x20); (1056, 8%N, 0x21280);
(1064, 8%N, 0); (1072, 8%N, 0); (1080, 8%N, 0xffffffffffffffff);
(1088, 8%N, 0x211e0); (1096, 8%N, 0x5); (1104, 8%N, 0x20); (1120, 8%N, 0x21280);
(1128, 8%N, 0); (1136, 8%N, 0); (1144, 8%N, 0xffffffffffffffff);
(1152, 8%N, 0x21200); (1160, 8%N, 0x6); (1168, 8%N, 0x20); (1184, 8%N, 0x21280);
(1192, 8%N, 0); (1200, 8%N, 0); (1208, 8%N, 0xffffffffffffffff);
(1216, 8%N, 0x21220); (1224, 8%N, 0x4); (1232, 8%N, 0x20); (1248, 8%N, 0x21280);
(1256, 8%N, 0); (1264, 8%N, 0); (1272, 8%N, 0xffffffffffffffff);
(1280, 8%N, 0x21240); (1288, 8%N, 0x3); (1296, 8%N, 0x20); (1312, 8%N, 0x21280);
(1320, 8%N, 0); (1328, 8%N, 0); (1336, 8%N, 0xffffffffffffffff);
(1344, 8%N, 0x21260); (1352, 8%N, 0x2); (1360, 8%N, 0x20); (1376, 8%N, 0x21280);
(1384, 8%N, 0); (1392, 8%N, 0); (1400, 8%N, 0xffffffffffffffff);
(1408, 8%N, 0x212a0); (1416, 8%N, 0x9); (1424, 8%N, 0x20); (1440, 8%N, 0x216a0);
(1448, 8%N, 0); (1456, 8%N, 0); (1464, 8%N, 0xffffffffffffffff);
(1472, 8%N, 0x212c0); (1480, 8%N, 0x5); (1488, 8%N, 0x20); (1504, 8%N, 0x216a0);
(1512, 8%N, 0); (1520, 8%N, 0); (1528, 8%N, 0xffffffffffffffff);
(1536, 8%N, 0x212e0); (1544, 8%N, 0x8); (1552, 8%N, 0x20); (1568, 8%N, 0x216a0);
(1576, 8%N, 0); (1584, 8%N, 0); (1592, 8%N, 0xffffffffffffffff);
(1600, 8%N, 0x21300); (1608, 8%N, 0x94); (1616, 8%N, 0xc0); (1632, 8%N, 0x216a0);
(1640, 8%N, 0); (1648, 8%N, 0); (1656, 8%N, 0xffffffffffffffff);
(1664, 8%N, 0x213c0); (1672, 8%N, 0xf); (1680, 8%N, 0x20); (1696, 8%N, 0x216a0);
(1704, 8%N, 0); (1712, 8%N, 0); (1720, 8%N, 0xffffffffffffffff);
(1728, 8%N, 0x213e0); (1736, 8%N, 0x67); (1744, 8%N, 0xa0); (1760, 8%N, 0x216a0);
(1768, 8%N, 0); (1776, 8%N, 0); (1784, 8%N, 0xffffffffffffffff);
(1792, 8%N, 0x21480); (1800, 8%N, 0x23); (1808, 8%N, 0x60); (1824, 8%N, 0x216a0);
(1832, 8%N, 0); (1840, 8%N, 0); (1848, 8%N, 0xffffffffffffffff);
(1856, 8%N, 0x214e0); (1864, 8%N, 0x1); (1872, 8%N, 0x20); (1888, 8%N, 0x216a0);
(1896, 8%N, 0); (1904, 8%N, 0); (1912, 8%N, 0xffffffffffffffff);
(1920, 8%N, 0x21500); (1928, 8%N, 0x76); (1936, 8%N, 0xa0); (1952, 8%N, 0x216a0);
(1960, 8%N, 0); (1968, 8%N, 0); (1976, 8%N, 0xffffffffffffffff);
(1984, 8%N, 0x215a0); (1992, 8%N, 0x7a); (2000, 8%N, 0xa0); (2016, 8%N, 0x216a0);
(2024, 8%N, 0); (2032, 8%N, 0); (2040, 8%N, 0xffffffffffffffff);
(2048, 8%N, 0x21640); (2056, 8%N, 0x8); (2064, 8%N, 0x20); (2080, 8%N, 0x216a0);
(2088, 8%N, 0); (2096, 8%N, 0); (2104, 8%N, 0xffffffffffffffff);
(2112, 8%N, 0x21660); (2120, 8%N, 0xd); (2128, 8%N, 0x20); (2144, 8%N, 0x216a0);
(2152, 8%N, 0); (2160, 8%N, 0); (2168, 8%N, 0xffffffffffffffff);
(2176, 8%N, 0x21680); (2184, 8%N, 0x3); (2192, 8%N, 0x20); (2208, 8%N, 0x216a0);
(2216, 8%N, 0); (2224, 8%N, 0); (2232, 8%N, 0xffffffffffffffff);
(2240, 8%N, 0xa1760); (2248, 8%N, 0x30); (2256, 8%N, 0x60); (2272, 8%N, 0x21280);
(2280, 8%N, 0); (2288, 8%N, 0); (2296, 8%N, 0xffffffffffffffff);
(2304, 8%N, 0xa17c0); (2312, 8%N, 0x58); (2320, 8%N, 0x80); (2336, 8%N, 0x21280);
(2344, 8%N, 0); (2352, 8%N, 0); (2360, 8%N, 0xffffffffffffffff);
(2368, 8%N, 0x5dcac0); (2376, 8%N, 0x42678); (2384, 8%N, 0x53000); (2400, 8%N, 0x21280);
(2408, 8%N, 0); (2416, 8%N, 0); (2424, 8%N, 0xffffffffffffffff);
(2432, 8%N, 0x62fac0); (2440, 8%N, 0x200); (2448, 8%N, 0x280); (2464, 8%N, 0x21280);
(2472, 8%N, 0); (2480, 8%N, 0); (2488, 8%N, 0xffffffffffffffff);
(2496, 8%N, 0x62fd40); (2504, 8%N, 0x12d); (2512, 8%N, 0x180); (2528, 8%N, 0x21280);
(2536, 8%N, 0); (2544, 8%N, 0); (2552, 8%N, 0xffffffffffffffff);
(2560, 8%N, 0x62fec0); (2568, 8%N, 0x8); (2576, 8%N, 0x20); (2592, 8%N, 0x21280);
(2600, 8%N, 0); (2608, 8%N, 0); (2616, 8%N, 0xffffffffffffffff);
(2624, 8%N, 0x62fee0); (2632, 8%N, 0x1000); (2640, 8%N, 0x1400); (2656, 8%N, 0x21280);
(2664, 8%N, 0); (2672, 8%N, 0); (2680, 8%N, 0xffffffffffffffff);
(2688, 8%N, 0x6312e0); (2696, 8%N, 0x8); (2704, 8%N, 0x20); (2720, 8%N, 0x216a0);
(2728, 8%N, 0); (2736, 8%N, 0); (2744, 8%N, 0xffffffffffffffff)]);
(0xa7c50, 8, [(0, 8%N, 0x101010000000001)]);
(0xa7c80, 8, [(0, 8%N, 0x1000100000000)]);
(0xa9c9c, 1, [(0, 1%N, 1)]);
(0xaa438, 8, [(0, 8%N, 0x7fff8000)]);
(0xab118, 1, [(0, 1%N, 1)]);
(0xab120, 24, [(0, 8%N, 0x7fffffffffff); (8, 8%N, 0); (16, 8%N, 0)]);
(0x139ee0, 8, [(0, 8%N, 0x1000)]);
(0x13bfe0, 8, [(0, 8%N, 0xffffffffffffffff)]) ].
Definition ro_chunk (base : Z) (c : Z * N * Z) : YP09.chunk := YP09.mkChunk (base + fst (fst c)) (CVal (snd (fst c)) (SLit (snd c))).
Definition ro_region (r : Z * Z * list (Z * N * Z)) : YP09.region :=
YP09.mkRegion None (fst (fst r)) (fst (fst r) + snd (fst r)) (fst (fst r)) (fst (fst r)) (map (ro_chunk (fst (fst r))) (snd r)).
Definition X2_STK : Z := 272.
Definition x2_shw : list (Z * Z) := [(0x7fffc1f4, 4); (0x7fffc1f8, 4); (0x7fffc1fc, 4); (0x7fffc200, 4);
(0x7fffc204, 4); (0x7fffc208, 4); (0x7fffc20c, 4); (0x7fffc210, 8); (0x7fffc218, 4); (0x7fffc21c, 4); (0x7fffc220, 4);
(0x7fffc224, 4); (0x7fffc228, 4); (0x7fffc22c, 4); (0x7fffc230, 4); (0x7fffc234, 4); (0x7fffc238, 4); (0x7fffc23c, 4);
(0x7fffc240, 4); (0x7fffc244, 4); (0x7fffc248, 4); (0x7fffc24c, 4); (0x7fffc254, 4); (0x7fffc258, 4); (0x7fffc25c, 4);
(0x7fffc260, 24); (0x7fffc278, 4); (0x7fffc27c, 20); (0x7fffc290, 12); (0x7fffc29c, 4); (0x7fffc2a0, 20);
(0x7fffc2b4, 20); (0x7fffc2c8, 4); (0x7fffc2cc, 4); (0x7fffc2d0, 4); (0x8000c2ec, 12); (0x8000c2f8, 16);
(0x800b3958, 42496); (0x800bdf58, 80); (0x800bdfa8, 48); (0x800bdfd8, 4); (0x800bdfdc, 640); (0x800be25c, 4);
(0x8000cc54, 344)].
Definition shw_region (w : Z * Z) : YP09.region :=
YP09.mkRegion None (fst w) (fst w + snd w) (fst w) (fst w + snd w) [].
Definition x2_regions : smem :=
YP09.mkRegion (Some 2%nat) (- X2_STK) 0 (- X2_STK) 0 []
:: cellr 0xa6d80 8 (SLit 1) true
:: cellr 0xa7cf0 8 (SLit 0) true
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
Definition x2_shw_const : list (Z * Z) := [(0x7fffc1f4, 4); (0x7fffc1f8, 4); (0x7fffc1fd, 3); (0x7fffc200, 4);
(0x7fffc204, 4); (0x7fffc209, 3); (0x7fffc20c, 4); (0x7fffc213, 5); (0x7fffc218, 4); (0x7fffc21e, 2); (0x7fffc221, 3);
(0x7fffc225, 3); (0x7fffc229, 3); (0x7fffc22d, 3); (0x7fffc232, 2); (0x7fffc235, 3); (0x7fffc238, 4); (0x7fffc23c, 4);
(0x7fffc240, 4); (0x7fffc244, 4); (0x7fffc248, 4); (0x7fffc24c, 4); (0x7fffc255, 3); (0x7fffc258, 4); (0x7fffc25d, 3);
(0x7fffc272, 6); (0x7fffc279, 3); (0x7fffc288, 8); (0x7fffc294, 8); (0x7fffc29c, 4); (0x7fffc2ae, 6); (0x7fffc2c3, 5);
(0x7fffc2c9, 3); (0x7fffc2cd, 3); (0x7fffc2d0, 4); (0x8000c2f2, 6); (0x8000c303, 5); (0x800bbe27, 8497);
(0x800bdf98, 16); (0x800bdfcd, 11); (0x800bdfd9, 3); (0x800be1dc, 128); (0x800be25d, 3); (0x8000cc54, 344)].
Definition x2_shbytes : list Z := flat_map (fun w => zrange (fst w) (Z.to_nat (snd w))) x2_shw_const.
Lemma shbyte_chk_true : forall ly,
forallb (fun a => match cell_lookup (Tfib_const ly) (ANum a) with
| Some (ACell (ANum a') 1%nat (AV (ANum v))) => (a' =? a) && (0 <=? v) && (v <? 256)
| _ => false end) x2_shbytes = true.
Proof. intros ly. vm_compute. reflexivity. Qed.
Definition x2_inw (ws : list (Z * Z)) (o : Z) : bool := existsb (fun w => (fst w <=? o) && (o <? fst w + snd w)) ws.
Definition x2_shw_zero : list (Z * Z * nat) := [(0x7fffc1fc, 1, 1%nat); (0x7fffc208, 1, 2%nat);
(0x7fffc210, 3, 3%nat); (0x7fffc21c, 2, 4%nat); (0x7fffc220, 1, 5%nat); (0x7fffc224, 1, 6%nat);
(0x7fffc228, 1, 7%nat); (0x7fffc22c, 1, 8%nat); (0x7fffc230, 2, 9%nat); (0x7fffc234, 1, 10%nat);
(0x7fffc254, 1, 11%nat); (0x7fffc25c, 1, 12%nat); (0x7fffc260, 18, 13%nat); (0x7fffc278, 1, 14%nat);
(0x7fffc27c, 12, 15%nat); (0x7fffc290, 4, 16%nat); (0x7fffc2a0, 14, 17%nat); (0x7fffc2b4, 15, 18%nat);
(0x7fffc2c8, 1, 19%nat); (0x7fffc2cc, 1, 20%nat); (0x8000c2ec, 6, 21%nat); (0x8000c2f8, 11, 22%nat);
(0x800b3958, 33999, 24%nat); (0x800bdf58, 64, 25%nat); (0x800bdfa8, 37, 26%nat); (0x800bdfd8, 1, 27%nat);
(0x800bdfdc, 512, 28%nat); (0x800be25c, 1, 29%nat)].
Definition x2_zrow (z : Z * Z * nat) : Z * Z := nth (snd z) Tfib_zero_shadow (0, 0).
Lemma shz_chk_true :
forallb (fun z => Nat.ltb (snd z) (length Tfib_zero_shadow) &&
(shadow_of_addr SHADOW_OFF (fst (x2_zrow z)) <=? fst (fst z)) &&
(fst (fst z) + snd (fst z) <=? shadow_of_addr SHADOW_OFF (fst (x2_zrow z)) + snd (x2_zrow z) / 8)) x2_shw_zero = true.
Proof. vm_compute. reflexivity. Qed.
Lemma shw_cover_chk_true :
forallb (fun w => (TFIB_IMG_END <=? fst w) && (fst w + snd w <=? 2 ^ 47) &&
forallb (fun o => x2_inw x2_shw_const o || x2_inw (map fst x2_shw_zero) o) (zrange (fst w) (Z.to_nat (snd w)))) x2_shw = true.
Proof. vm_compute. reflexivity. Qed.
Section S.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : PcapSyms B.
Hypothesis MU0 : forall ly, cell_lookup (Tfib_const ly) (ANum 0xa7cf0) = Some (ACell (ANum 0xa7cf0) 8 (AV (ANum 0))).
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
intros ly S H mem a HM Hin. pose proof (shbyte_chk_true ly) as Hc.
rewrite forallb_forall in Hc. specialize (Hc a Hin). cbn beta in Hc.
destruct (cell_lookup (Tfib_const ly) (ANum a)) as [[e w av]|] eqn:HL; [|discriminate].
destruct e; try discriminate. destruct w as [|[|w]]; try discriminate.
destruct av as [e'| ]; try discriminate. destruct e'; try discriminate.
apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _]. apply Z.eqb_eq in Hc. subst.
pose proof (tfib_const_lookup B TB ly S H mem a 1 _ HM HL) as Hv.
specialize (Hv 0%nat ltac:(lia)). rewrite Z.add_0_r in Hv. eexists. exact Hv.
Qed.
Lemma shz_present : forall ly S (H : word -> bool) mem z o,
ARm B ly S (aview tfibsegs H mem) -> In z x2_shw_zero -> fst (fst z) <= o < fst (fst z) + snd (fst z) ->
exists b, mbyte tfibsegs (mrestrict H mem) o = Some b.
Proof.
intros ly S H mem z o HM Hin Ho. pose proof shz_chk_true as Hc.
rewrite forallb_forall in Hc. specialize (Hc z Hin). cbn beta in Hc.
apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
apply Nat.ltb_lt in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
pose proof (proj1 (Forall_forall _ _) (am_zshadow B ly S _ HM) (x2_zrow z)
ltac:(unfold zero_shadow_ranges, x2_zrow; right; rewrite (ts_zsh _ TB); apply nth_In; exact H1)) as HZ.
specialize (HZ (o - shadow_of_addr SHADOW_OFF (fst (x2_zrow z))) ltac:(lia)).
replace (shadow_of_addr SHADOW_OFF (fst (x2_zrow z)) + (o - shadow_of_addr SHADOW_OFF (fst (x2_zrow z)))) with o in HZ by lia.
unfold aview in HZ. destruct (mbyte tfibsegs (mrestrict H mem) o) as [b|]; [exists b; reflexivity | discriminate].
Qed.
Lemma shw_byte_present : forall ly S (H : word -> bool) mem w o,
ARm B ly S (aview tfibsegs H mem) -> In w x2_shw -> fst w <= o < fst w + snd w ->
exists b, mbyte tfibsegs (mrestrict H mem) o = Some b.
Proof.
intros ly S H mem w o HM Hin Ho. pose proof shw_cover_chk_true as Hc.
rewrite forallb_forall in Hc. specialize (Hc w Hin). cbn beta in Hc.
apply andb_prop in Hc as [_ Hc]. rewrite forallb_forall in Hc.
specialize (Hc o ltac:(apply In_zrange; rewrite Z2Nat.id by lia; lia)). cbn beta in Hc.
apply orb_prop in Hc as [Hc|Hc]; unfold x2_inw in Hc; apply existsb_exists in Hc as (v & Hv & Hvo); cbn beta in Hvo;
apply andb_prop in Hvo as [Hv1 Hv2]; apply Z.leb_le in Hv1; apply Z.ltb_lt in Hv2.
- apply (shbytes_present ly S H mem o HM). unfold x2_shbytes. apply in_flat_map. exists v. split; [exact Hv|].
cbn beta. apply In_zrange. rewrite Z2Nat.id by lia. lia.
- apply in_map_iff in Hv as (z & <- & Hz). exact (shz_present ly S H mem z o HM Hz ltac:(lia)).
Qed.
Lemma shw_ok : forall ly S (H : word -> bool) mem E,
ARm B ly S (aview tfibsegs H mem) -> Forall (region_ok tfibsegs E (mrestrict H mem)) (map shw_region x2_shw).
Proof.
intros ly S H mem E HM. apply Forall_map. apply Forall_forall. intros [lo n] Hin.
pose proof shw_cover_chk_true as Hc. rewrite forallb_forall in Hc.
specialize (Hc _ Hin). cbn beta in Hc. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. cbn [fst snd] in H1, H2. unfold TFIB_IMG_END, pcap_img_end, YImgTop.IMG_TOP in H1.
unfold shw_region, region_ok. cbn [fst snd YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. rewrite Z.add_0_l.
destruct (shw_byte_present ly S H mem (lo, n) o HM Hin ltac:(cbn [fst snd]; lia)) as [b Hb].
apply (mbyte_high_writable _ o b); [unfold TFIB_IMG_END, pcap_img_end, YImgTop.IMG_TOP; lia | exact Hb].
Qed.
Lemma zi8_14ea00 : wseg_ok tfibsegs (Z_to_bv 64 0xa6d80) (Z.to_nat 8) = true. Proof. vm_compute. reflexivity. Qed.
Lemma zi8_14f970 : wseg_ok tfibsegs (Z_to_bv 64 0xa7cf0) (Z.to_nat 8) = true. Proof. vm_compute. reflexivity. Qed.
Lemma x2_windows : forall E a, in_wrange E (ss_mem ss_x2) a ->
(bv_unsigned (ew E 2) - X2_STK <= a < bv_unsigned (ew E 2)) \/ XW2 a.
Proof.
intros E a Hin. destruct (in_wrange_windows E _ a Hin) as (b & lo & hi & Ht & Hr).
cbn in Ht. unfold XW2. unfold X2_STK in *.
repeat (destruct Ht as [Hq|Ht]; [injection Hq as <- <- <-; cbn [base_val] in Hr; first [left; lia | right; repeat (first [left; lia | right]); lia]|]). destruct Ht.
Qed.
Definition x2_zivs : list (Z * Z) := [(0xa6d80, 0xa6d88); (0xa7cf0, 0xa7cf8); (0x7fffc1f4, 0x7fffc1f8);
(0x7fffc1f8, 0x7fffc1fc); (0x7fffc1fc, 0x7fffc200); (0x7fffc200, 0x7fffc204); (0x7fffc204, 0x7fffc208);
(0x7fffc208, 0x7fffc20c); (0x7fffc20c, 0x7fffc210); (0x7fffc210, 0x7fffc218); (0x7fffc218, 0x7fffc21c);
(0x7fffc21c, 0x7fffc220); (0x7fffc220, 0x7fffc224); (0x7fffc224, 0x7fffc228); (0x7fffc228, 0x7fffc22c);
(0x7fffc22c, 0x7fffc230); (0x7fffc230, 0x7fffc234); (0x7fffc234, 0x7fffc238); (0x7fffc238, 0x7fffc23c);
(0x7fffc23c, 0x7fffc240); (0x7fffc240, 0x7fffc244); (0x7fffc244, 0x7fffc248); (0x7fffc248, 0x7fffc24c);
(0x7fffc24c, 0x7fffc250); (0x7fffc254, 0x7fffc258); (0x7fffc258, 0x7fffc25c); (0x7fffc25c, 0x7fffc260);
(0x7fffc260, 0x7fffc278); (0x7fffc278, 0x7fffc27c); (0x7fffc27c, 0x7fffc290); (0x7fffc290, 0x7fffc29c);
(0x7fffc29c, 0x7fffc2a0); (0x7fffc2a0, 0x7fffc2b4); (0x7fffc2b4, 0x7fffc2c8); (0x7fffc2c8, 0x7fffc2cc);
(0x7fffc2cc, 0x7fffc2d0); (0x7fffc2d0, 0x7fffc2d4); (0x8000c2ec, 0x8000c2f8); (0x8000c2f8, 0x8000c308);
(0x800b3958, 0x800bdf58); (0x800bdf58, 0x800bdfa8); (0x800bdfa8, 0x800bdfd8); (0x800bdfd8, 0x800bdfdc);
(0x800bdfdc, 0x800be25c); (0x800be25c, 0x800be260); (0x8000cc54, 0x8000cdac)].
Lemma x2_zivs_chk : forallb (fun iv => existsb (fun r => obase_eqb (YP09.r_base r) None && (YP09.r_lo r =? fst iv) &&
(YP09.r_hi r =? snd iv) && zcover (fst iv) (snd iv) (ChunkSort.sort (YP09.r_chunks r))) (ss_mem x2_st)) x2_zivs = true.
Proof. vm_compute. reflexivity. Qed.
Definition x2_inz (a : Z) : bool := existsb (fun iv => (fst iv <=? a) && (a <? snd iv)) x2_zivs.
Lemma inz_of_in : forall a lo hi, In (lo, hi) x2_zivs -> lo <= a < hi -> x2_inz a = true.
Proof.
intros a lo hi Hin Ha. unfold x2_inz. apply existsb_exists. exists (lo, hi). split; [exact Hin|]. cbn [fst snd].
apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Local Ltac inz_case Ha := match type of Ha with ?L <= ?a < ?H =>
apply (inz_of_in a L H); [unfold x2_zivs; cbn [In]; repeat (first [left; reflexivity | right]) | exact Ha] end.
Lemma XW2_inz : forall a, XW2 a -> x2_inz a = true.
Proof. intros a Ha. unfold XW2 in Ha. repeat (destruct Ha as [Ha|Ha]; [inz_case Ha|]). inz_case Ha. Qed.
Lemma x2_inz_region : forall a, x2_inz a = true -> exists r, In r (ss_mem x2_st) /\ YP09.r_base r = None /\
YP09.r_lo r <= a < YP09.r_hi r /\ zcover (YP09.r_lo r) (YP09.r_hi r) (ChunkSort.sort (YP09.r_chunks r)) = true.
Proof.
intros a Ha. unfold x2_inz in Ha. apply existsb_exists in Ha as ([lo hi] & Hin & Hb). cbn [fst snd] in Hb.
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
pose proof x2_zivs_chk as C. rewrite forallb_forall in C. specialize (C _ Hin). cbn [fst snd] in C.
apply existsb_exists in C as (r & Hr & C).
apply andb_prop in C as [C Hz]. apply andb_prop in C as [C Hh]. apply andb_prop in C as [Hbse Hl].
apply obase_eqb_eq in Hbse. apply Z.eqb_eq in Hl. apply Z.eqb_eq in Hh.
exists r. split; [exact Hr|]. split; [exact Hbse|]. rewrite Hl, Hh. split; [lia | exact Hz].
Qed.
Lemma x2_zero_bytes : forall E m, Forall (YP09.region_ok tfibsegs E m) (ss_mem x2_st) ->
forall a, XW2 a -> YP09.mbyte tfibsegs m a = Some (Z_to_bv 8 0).
Proof.
intros E m Hrs a Ha. destruct (x2_inz_region a (XW2_inz a Ha)) as (r & Hr & Hb & Hlh & Hz).
exact (region_zero tfibsegs E m r (proj1 (Forall_forall _ _) Hrs r Hr) Hb Hz a Hlh).
Qed.
Theorem x2_realizes_vals : xret_realizes_noar_vals tfibsegs B X2_PC XW2 (fun _ => 0) XTRUE.
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
split; [lia|]. split; [lia|]. split; [intros o Ho; rewrite Z.add_0_l; apply (wseg_writable _ 0xa6d80 8); [exact zi8_14ea00 | lia | lia | lia | lia] |].
constructor; [|constructor]. eapply (chunk_ok_val tfibsegs E _ 0 _ 8 _ 1); [reflexivity | zside | zside |].
rewrite Z.add_0_l. exact (tfib_const_lookup B TB ly S _ mem 0xa6d80 8 1 HM ltac:(vm_compute; reflexivity)).
+ unfold region_ok, cellr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val Z.of_N].
split; [lia|]. split; [lia|]. split; [intros o Ho; rewrite Z.add_0_l; apply (wseg_writable _ 0xa7cf0 8); [exact zi8_14f970 | lia | lia | lia | lia] |].
constructor; [|constructor]. eapply (chunk_ok_val tfibsegs E _ 0 _ 8 _ 0); [reflexivity | zside | zside |].
rewrite Z.add_0_l. exact (tfib_const_lookup B TB ly S _ mem 0xa7cf0 8 0 HM (MU0 ly)).
- apply pairwise_disjoint_of_extents. unfold x2_regions, x2_shw, x2_rodata, cellr, shw_region, ro_region, extent_of_region.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2. unfold X2_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. clear - Hsp44. repeat split; lia.
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
split; [|split; [|split; [|split]]].
- exact (aregs_preserved_of_st_ok _ E _ _ regs [] HS1 ltac:(split; [intros i Hi; reflexivity | reflexivity]) ltac:(vm_compute; reflexivity)).
- apply with_vm_backing_same.
- intros a Hr Hs Hx. apply AV; [exact Hr | unfold X2_STK; unfold sp0 in *; lia | exact Hx].
- intros a Hr Hx Hp.
destruct (Z_lt_le_dec a (sp0 - X2_STK)) as [L1|L1]; [| destruct (Z_lt_le_dec a sp0) as [L2|L2]; [apply PRS; lia|]].
all: destruct Hp as [Hh [b Hb]]; split; [exact Hh|]; exists b; rewrite MEQ; [exact Hb|]; rewrite unsigned_lit_small by lia; intros [Hw|Hw]; [lia | exact (Hx Hw)].
- intros a Hx. unfold aview. pose proof (st_ok_mem_ok tfibsegs E x2_st _ HS1) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs.
rewrite (x2_zero_bytes E _ Hrs a Hx). reflexivity.
Qed.
Theorem x2_realizes : xret_realizes_noar tfibsegs B X2_PC XW2 XTRUE.
Proof.
intros ly S W regs mem md HPRE HX. eapply SRr_mono; [exact (x2_realizes_vals ly S W regs mem md HPRE HX)|].
intros W' c' _ (HW & regs' & mem' & md' & Hc & Hp & Hm & Hf & Hpr & _). split; [exact HW|].
exists regs', mem', md'. split; [exact Hc|]. split; [exact Hp|]. split; [exact Hm|]. split; [exact Hf | exact Hpr].
Qed.
End S.
End d.
