(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec AgentLib AsanAcct AxSymExec3K AxSymExec3SoundK AxSymRun3K
AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK Jb0DefsK Jb0PlanImagesK HandoffBridgeK HandoffCellsK ArtMem SeqExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Jb0ArtCellsK () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanInitK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanK.APK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanSoundK.APSK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3K.AX2K."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0ArtCellsK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0DefsK."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1bool"; "1fst"; "1nat"; "1option"; "1pair"; "1prod"; "1snd"; "1true"; "2eq"; "3add"; "4le"; "5Z"; "0E"; "0FULL"; "6Model"; "7bvmap"]; ["0M"; "0R"; "8cell"; "9LIMIT"; "9SINV0"; "9argH0"; ":acs"; ":kn"; ";cs_ok"; "<env"; "=ART_LITW"; "=art_lits_chk"; "=chk_lit1"; ">APH0"; ">ASAN0"; ">ASEGS0"]; ["?In"; "@add"; "@le"; "@lt"; "@of_nat"; "@pow"; "0a"; "0argv"; "0brk0"; "0c"; "0cs"; "0envp"; "0fs"; "0hw"; "0model"; "0rdraw"]; ["0sp"; "Abv"; "0uid"; "0v"; "0w"; "0w1"; "0w2"]]).
Definition ART_LITW : list (Z * nat * Z) :=
[
(1283032 + 40, 4%nat, 0xffffffff); (1283032 + 56, 1%nat, 0); (0x10400, 8%nat, 0xafffff00000fffff); (0x134380, 8%nat, 0x1cc4e0); (0x1cc4e0, 8%nat, 4096);
(0x1ce568 + 260, 1%nat, 0); (0x1ce568 + 144, 8%nat, 0);
(0x1343a0, 8%nat, 0x13ca38); (0x13ca38, 8%nat, 0x7fff8000); (0x1343a8, 8%nat, 0x13d728); (0x13d728, 8%nat, 0); (0x1343b0, 8%nat, 0x13d730); (0x13d730, 8%nat, 0);
(0x1343b8, 8%nat, 0x13d720); (0x13d720, 8%nat, 2 ^ 47 - 1); (0x134398, 8%nat, 0x13a238); (0x13a238 + 78, 1%nat, 1); (0x1343c0, 8%nat, 0x1363b0); (0x1363b0, 8%nat, 0x126be8);
(0x134390, 8%nat, 0x1ce568); (0x1ce568 + 120, 8%nat, 18446744073709551615); (0x13c29c, 1%nat, 1);
(0x13c2a0, 1%nat, 1); (0x13c2a4, 4%nat, 0); (0x670ac0 - 88, 8%nat, 0x691f78);
(0x10418, 8%nat, 0x218a392cd3d5dbf); (0x10494, 1%nat, 3); (0x10358, 8%nat, 0xcc6e96b9cc6e96b9); (0x10598, 1%nat, 4); (0x105c1, 1%nat, 11);
(0x102e8, 8%nat, 0xc6a4a7935bd1e995); (0x10320, 8%nat, 0x35253c9ade8f4ca8); (0x103f8, 8%nat, 0x9747b28c9747b28c);
(0x13d718, 1%nat, 1); (0x1beca2, 1%nat, 0); (1283032 + 3616, 8%nat, 2 ^ 40); (1283032 + 3624, 2%nat, 16); (1283032 + 3626, 2%nat, 2048);
(0x1ce500, 8%nat, 0); (0x1ce508, 8%nat, 0); (0x13a238 + 44, 4%nat, 4096); (0x13a238 + 48, 4%nat, 0); (0x13a238 + 52, 4%nat, 190); (0x13a238 + 85, 1%nat, 1);
(0x135000, 8%nat, 0x10); (0x13d73c, 4%nat, 30); (0x1ce568 + 34, 1%nat, 1); (0x1396b0 + 80, 8%nat, 2 ^ 20); (0x1396b0 + 64, 8%nat, 2 ^ 28);
(0x136358, 8%nat, 0x127308); (0x1361e8, 8%nat, 0x1266e8);
(0x670ac0 + 0x10, 4%nat, 0);
(1283032 + 64, 8%nat, 4096); (1283032 + 64 + 56, 8%nat, 0); (1283032 + 64 + 48, 8%nat, 0); (1283032 + 64 + 616, 1%nat, 0);
(0x1396b0 + 160, 8%nat, 0); (0x1396b0 + 168, 8%nat, 0); (0x1396b0 + 176, 8%nat, 0); (0x1396b0 + 184, 8%nat, 0); (0x1396b0 + 152, 1%nat, 0); (0x1396b0 + 153, 1%nat, 0);
(0x1cc4c8, 1%nat, 0); (0x1cc4c9, 1%nat, 0);
(0x61e918, 4%nat, 1);
(1283032 + 64 + 617, 3%nat, 0); (0x1396b0 + 154, 2%nat, 0); (0x1cc4c8, 4%nat, 0);
(0x134388, 8%nat, 0x1363e8); (0x1363e8, 8%nat, 0x1a58b); (0x13d719, 1%nat, 1); (0x1ce663, 1%nat, 1); (0x1ce5f1, 1%nat, 1); (0x1ce568 + 84, 1%nat, 1);
(0x1cc4d8, 4%nat, 0); (0x13ca40, 4%nat, 1); (0x1363a8, 8%nat, 0x1267e4);
(0x1396b0 + 72, 8%nat, 0xe666661);
(0x1343e0, 8%nat, 1);
(0x136340, 8%nat, 0x10d684); (0x134f08, 8%nat, 0x13d719); (0x1362a0, 8%nat, 0x1277c8); (0x1343f0, 8%nat, 0x1cc4d8); (0x1351a8, 8%nat, 8);
(0x1ce5bc, 1%nat, 1); (0x1361f8, 8%nat, 0x12d1e8); (0x136200, 8%nat, 0x11dbe4); (0x136228, 8%nat, 0x1242e0); (0x136230, 8%nat, 0x11dffc);
(0x1361b0, 8%nat, 0x1361b0); (0x139380, 8%nat, 1); (0x1393d0, 1%nat, 0); (0x13a250, 4%nat, 1); (0x13a2f0, 8%nat, 0); (0x1ce8e0, 1%nat, 0);
(0x670ab8, 8%nat, 0x670ae0); (0x670ae8, 8%nat, 0x6712c0);
(0x1361b8, 8%nat, 0x1270cc); (0x136280, 8%nat, 0x115394); (0x136288, 8%nat, 0x127034);
(0x10498, 1%nat, 4);
(0x13a254, 1%nat, 0);
(0x136350, 8%nat, 0x11557c);
(0x13a298, 1%nat, 1);
(0x1361d8, 8%nat, 0x1267b4); (0x1ce666, 1%nat, 1); (0x1ce667, 1%nat, 1) ].
Definition chk_lit1 (k : list kentry) (c : Z * nat * Z) : bool :=
let '(a, w, v) := c in
(chk_sub k a w v || chk_img ASEGS0 ASAN0 k a w v || (chk_zero k (ELit 0) a (Z.of_nat w) && Z.eqb v 0 && Nat.leb w 8 && Z.leb 0 a))%bool.
Definition art_lits_chk (cs : acs) : bool := forallb (chk_lit1 (kn cs)) ART_LITW.
Section Lits.
Variable sp brk0 : word.
Variable rdraw : EntryDraw.
Variable argv envp : list (list byte).
Variables uid hw : word.
Variable fs : Fs.Fs.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
#[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 argv envp uid hw).
#[local] Notation argH := (argH0 APH0 sp rdraw argv envp uid hw).
#[local] Notation CSOK := (cs_ok ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs).
Let AH := argH0_high APH0 sp rdraw argv envp uid hw Hsp Hva.
Lemma art_lit1 : ltac2:(TCodec.tc2 tcn__Jb0ArtCellsK "R2'I'F&?y5'QAyR0%211%5241'3y8%611%311p061'>'5';'2%3221%4213'H&O&N&C&D&MvQ@vQ?vQ8vQ7vQ;vQBvQ=%9887654321&E%17:986543vQ<r6r5r4r3r2%F;EDC97654321'8'0&L&G%11:%3217(7%73621&B&1%13Q3Q5=%23Q6Q51&6%13Q8Q73%23Q7Q9A%75Q5D421p091p0B1pRDQ:1pRNQ@1pLQB1pQ4QH1pRFQO1pJR11").
Proof.
intros E cs R FULL model [[a w] v] HC H. cbn [fst snd]. unfold chk_lit1 in H. unfold cell.
apply orb_prop in H as [H|H]; [apply orb_prop in H as [H|H]|].
- exact (hc_sub ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs asan0_in_hull asan0_hull_ok AH E cs R FULL model a w v HC H).
- exact (hc_img ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs asan0_hull_ok AH E cs R FULL model a w v HC H).
- apply andb_prop in H as [H Ha]. apply andb_prop in H as [H Hw]. apply andb_prop in H as [H Hv].
apply Z.eqb_eq in Hv. subst v. apply Nat.leb_le in Hw. apply Z.leb_le in Ha.
apply (hc_zero_cell ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model (ELit 0) a (Z.of_nat w) HC H a w Hw);
unfold uE; cbn [edenot]; rewrite u64_lit by lia; lia.
Qed.
Lemma art_lit : ltac2:(TCodec.tc2 tcn__Jb0ArtCellsK "R4'I'F&?y5'QAyR0%211%5241'3y8%611%311p061'>'H&O&N&C&D&MvQ@vQ?vQ8vQ7vQ;vQBvQ=%9887654321&E%17:986543vQ<r5r4r3r2r1%F;EDC97654321'8'0&K%119(7%53421';'2&Q0'5%1243%2215(4%1476A@%24481@&J%83521&Br8%25Q91HGFp041pS8?1pS:?1pR>A1p0C1p0J1pRNQB1pLQD1pQ4QJ1pRFR11pJR31").
Proof.
intros E cs R FULL model HC H a w v Hin.
exact (art_lit1 E cs R FULL model (a, w, v) HC (proj1 (forallb_forall _ _) H _ Hin)).
Qed.
End Lits.
Lemma cell0_cat : ltac2:(TCodec.tc2 tcn__Jb0ArtCellsK "QD'QAyR0%211'3y8%511%311p051';'2&Q2zr3%3221&Q3&Q1r4&Q4%116%4231&Q5+2+R0%3221%:251':&9%12;?u8%4221&B&Or7r6r5%554321Hr8%D14%G261%958315Lr9%?298%<5;261Op041p091p0@1p0F1p0Q21pS>Q71pS<Q81pR>Q:1pQ2Q<1").
Proof.
intros M a w1 w2 Ha Hn Hw H1 H2. unfold cell in *. rewrite wleb_zero in * by lia.
assert (H2' : rdn ASEGS0 M (Z_to_bv 64 a + nat_to_word w1)%bv w2 = Some (repeat (Z_to_bv 8 0) w2)).
{ replace (Z_to_bv 64 a + nat_to_word w1)%bv with (Z_to_bv 64 (a + Z.of_nat w1)); [exact H2|].
apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small a) by lia. rewrite (Z.mod_small (Z.of_nat w1)) by lia. reflexivity. }
rewrite (rdn_app ASEGS0 M w1 w2 (Z_to_bv 64 a) _ _ H1 H2'). rewrite repeat_app. reflexivity.
Qed.
