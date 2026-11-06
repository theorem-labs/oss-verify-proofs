(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX DrvKitA Jb0DrvEntry Jb0Drv_defs Jb0DrvRead Jb0DrvG_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Jb0DrvC_defs () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Sem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.DrvKitA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0DrvC_defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0DrvC_defs.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0DrvC_defs.FPX_2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0Drv_defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymDrive."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymRun."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0Cc"; "1app"; "1bool"; "1cons"; "1false"; "1fst"; "1list"; "1nat"; "1nil"; "1pair"; "1prod"; "1snd"; "1true"; "2and"; "2eq"; "2iff"]; ["3Z"; "4ALU_ADD"; "4BC_LTU"; "4M_MUL"; "5alu64"; "5mul_div"; "0Lz"; "6ksubl_b"; "8cfglen_xA"; "8knGLA"; "8knHb0"; "8knT0A"; "8kn_bmA"; "8kn_tgtA"; "8rHa"; "8rHb"]; ["9cfgFA"; "9cfgGA"; "9cfgHA"; "9sx8FA"; "9zseqA"; "7cfglen_xA"; "7plen_xA"; "7sx8_xA"; ":kn_after"; ";blobs_ev"; "<EAlu"; "<ELit"; "<EMd"; "<EVar"; "<Env"; "<SCBr"]; ["<edenot"; "<expr"; "<kentry"; "<s_log"; "<s_pc"; "<scripts"; "<sentry"; "<sidecond"; "<sym_state"; "=vals_ev"; ">In"; ">forallb"; "?add"; "?eqb"; "?le"; "?lor"]; ["?lt"; "?modulo"; "?mul"; "?of_nat"; "?pow"; "?sub"; "0a"; "0b"; "0b0"; "0b1"; "0bl"; "0c"; "0k"; "0n"; "0q"; "0r"]; ["@Z_to_bv"; "@bv"; "@bv_or"; "@bv_unsigned"; "0v71"; "0v72"; "0vals"; "0z"]]).
Section FPX_1. Context {fx : PropExec.FPState}.
Definition STOPS_HA : list Z := 0xa75a4 :: 0xa774c :: STOPSA.
Definition runHA (scr : scripts) (ss : sym_state) := sym_exec ASEGS FUELA true STOPS_HA scr ss [].
Definition kn_hdrA : list kentry :=
[KWord (SA (EVar 48) 0) 1 (EVar 71); KWord (SA (EVar 48) 1) 1 (EVar 72); KRange (EVar 71) 0 255; KRange (EVar 72) 0 255].
Definition knGLA : list kentry := kn_hdrA ++ knGA 6 67108863.
Definition scr_fallA : scripts := SCR [false] [] [].
Definition rHa := Eval vm_compute in runHA scr_fallA (SS 0x1277c0 srGLA [] knGLA 73).
Definition srHa : list expr := Eval vm_compute in s_regs (fst (fst rHa)).
Definition cfglen_xA : expr := Eval vm_compute in nth 18 srHa (ELit 0).
Definition sx8_xA : expr := Eval vm_compute in nth 21 srHa (ELit 0).
Definition srHb0 : list expr := Eval vm_compute in map (esub sx8_xA (EVar 74)) (map (esub cfglen_xA (EVar 73)) srHa).
Definition PXA : expr := EAlu ALU_ADD (EVar 48) (EVar 73).
Definition kn_bmA : list kentry :=
[KRange (EVar 73) 0 32767;
KWord (SA PXA 2) 1 (EVar 75); KWord (SA PXA 3) 1 (EVar 76); KWord (SA PXA 4) 1 (EVar 77); KWord (SA PXA 5) 1 (EVar 78);
KRange (EVar 75) 0 255; KRange (EVar 76) 0 255; KRange (EVar 77) 0 255; KRange (EVar 78) 0 255].
Definition knHb0 : list kentry := kn_bmA ++ kn_after rHa knGLA.
Definition rHb := Eval vm_compute in runHA scr0 (SS 0xa75a4 srHb0 [] knHb0 79).
Definition srHb : list expr := Eval vm_compute in s_regs (fst (fst rHb)).
Definition plen_xA : expr := Eval vm_compute in nth 13 srHb (ELit 0).
Definition srT0A : list expr := Eval vm_compute in map (esub plen_xA (EVar 79)) srHb.
Definition kn_tgtA : list kentry :=
[KRange (EVar 73) 0 32767; KRange (EVar 79) 0 67108857; KWord (SA (EVar 48) 2) 1 (EVar 80); KRange (EVar 80) 0 255].
Definition knT0A : list kentry := kn_tgtA ++ knGLA.
Definition summH (r : sym_state * list sidecond * scripts) := (s_pc (fst (fst r)), snd (fst r), s_next (fst (fst r)), s_log (fst (fst r))).
Lemma hdr_itinerary_okA : ltac2:(TCodec.tc2 tcn__Jb0DrvC_defs "R:'='>':'@'6'QG%211%5241'QF%511%8231(9&QD&5'QH%=219'QE&N%53321%635=1%811&;%138@4%<4DA31&QC%116%?4CA31+dm]4(3(Q?(4(B(Q=uR6%211(Q:(A&H(Q;+6%211%63541%=4<;81(8%11Q7%A3Q831%Q34Q;Q8C1%41Q7%Q54Q9Q721%Q@3Q7G1'QB%Q?11&Q8&I%22Q51%QF3412&O%Q<3Q:Q91%Q=3Q<QD1%Q?11%Q73Q>QF3%QB4QJQG21%Q614%QD4QHQF21+dmj<%QF4QNQK1E%QG4QKQI1C%R23QI41&J%A2=1%R53C12%R7241%R82A1%R92H1").
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma knT0A_sub : ltac2:(TCodec.tc2 tcn__Jb0DrvC_defs "<'>'2&G&1'QB&M&J%43321&K%7221(<%;3:21").
Proof. vm_compute. reflexivity. Qed.
Lemma knHb0_eq : ltac2:(TCodec.tc2 tcn__Jb0DrvC_defs ":'>'6'QB%211&J&1&L&I%33621%93651").
Proof. vm_compute. reflexivity. Qed.
End FPX_1.
Section FPX_2. Context {fx : PropExec.FPState}.
Definition cfgFA (v71 v72 : word) : word :=
edenot (Env (fun n => match n with 71%nat => v71 | 72%nat => v72 | _ => Z_to_bv 64 0 end) (blobs_ev [])) cfglen_xA.
Lemma cfglen_x_cfgFA : ltac2:(TCodec.tc2 tcn__Jb0DrvC_defs "N'6'RAyR0%211%411y8%511%711%811'>&Q@(Q>&QIr2%211&Q9r1%211%7241&Q5%:221&Q0uR7%;2:1uR8%=2<1%5231%B3H71pTFD1pU>I1").
Proof. intros. reflexivity. Qed.
Definition zseqA (n : nat) : list Z := map Z.of_nat (seq 0 n).
Lemma in_zseqA : ltac2:(TCodec.tc2 tcn__Jb0DrvC_defs "E'7'@&?&QJr1&Q4r2%211%53741'=&QNz%2218&R0&R3%119%32<1%8251%@2:1pU@B1pTLD1").
Proof.
intros n z. unfold zseqA. rewrite in_map_iff. split.
- intros (k & <- & Hk). apply in_seq in Hk. lia.
- intros Hz. exists (Z.to_nat z). split; [lia|]. apply in_seq. lia.
Qed.
Definition cfgGA (v72 : word) : word :=
alu64 ALU_SRL (mul_div M_MUL (Z_to_bv 64 144115188075855872) (ext_val true 0 1 v72)) (Z_to_bv 64 49).
Definition cfgHA (v71 : word) : word := ext_val false 0 1 v71.
Lemma cfgF_splitA : ltac2:(TCodec.tc2 tcn__Jb0DrvC_defs "A'RAyR0%211'>&Q0r2r1%3221&RB&Q1%114&Q2%117%53<31%;3<71pU<=1pU:>1").
Proof. intros v71 v72. reflexivity. Qed.
Lemma cfgG_tabA : ltac2:(TCodec.tc2 tcn__Jb0DrvC_defs "K'>'2&QK'@&QM&RCyR0&Q1&R@r1%2241%411%7261&R2+X0&R1+T0%2281%5241%?271qTDA1&Q4uX0%211%F3E41(<%J3I21").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cfgH_tabA : ltac2:(TCodec.tc2 tcn__Jb0DrvC_defs "E'>'2&QK'@&QM&RCyR0&Q2&R@r1%2241%411%7261%9214qTB;1&Q4uX0%211%@3?41(<%D3C21").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lor_tabA : ltac2:(TCodec.tc2 tcn__Jb0DrvC_defs "J'>'2&QK'@&QM&QO&R2+X0r2%3221r1%6221&QL%1243%:231qT@<1&Q4uX0%211%A3@41qT>A1uT0%611%E3D31(<%I3H21").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cfgF_valA : ltac2:(TCodec.tc2 tcn__Jb0DrvC_defs "Q2'@'=&QNzr2%3221&R0+X0%2241%8241'>'RAyR0%211&Q0&R@r4%2251r3%4271%6231&R1&QL&R2%12A6%3291+QPP0%6221%=2@1%C3@91p0E1p0F1pTDQ01pTBQ11").
Proof.
intros b0 b1 H0 H1.
pose proof cfgG_tabA as TG. rewrite forallb_forall in TG. specialize (TG b1 (proj2 (in_zseqA 256 b1) ltac:(cbn; lia))). apply Z.eqb_eq in TG.
pose proof cfgH_tabA as TH. rewrite forallb_forall in TH. specialize (TH b0 (proj2 (in_zseqA 256 b0) ltac:(cbn; lia))). apply Z.eqb_eq in TH.
pose proof (Z.mod_pos_bound b1 128 ltac:(lia)) as HM.
pose proof lor_tabA as TL. rewrite forallb_forall in TL. specialize (TL (b1 mod 128) (proj2 (in_zseqA 128 (b1 mod 128)) ltac:(cbn; lia))).
rewrite forallb_forall in TL. specialize (TL b0 (proj2 (in_zseqA 256 b0) ltac:(cbn; lia))). apply Z.eqb_eq in TL.
apply bv_eq. rewrite cfgF_splitA, stdpp.bitvector.definitions.bv_or_unsigned, TG, TH, TL. symmetry.
assert (E : (b0 + 256 * b1) mod 32768 = 256 * (b1 mod 128) + b0).
{ pose proof (Z.div_mod b1 128 ltac:(lia)) as D.
symmetry. apply (Zmod_unique (b0 + 256 * b1) 32768 (b1 / 128)); lia. }
rewrite E. apply u_small. lia.
Qed.
Definition sx8FA (v72 : word) : word := ext_val true 0 1 v72.
Lemma sx8_x_sx8FA : ltac2:(TCodec.tc2 tcn__Jb0DrvC_defs "L'6'RAyR0%211%411y8%511%711%811'>&Q@(Q>&QIr2%211&Q9r1%211%7241&Q7%:221&Q3uR8%;2:1%311%@3F51pTFB1pU>G1").
Proof. intros. reflexivity. Qed.
Lemma plen_x_eqA : ltac2:(TCodec.tc2 tcn__Jb0DrvC_defs "E'>'QA&Q6(Q:(A(Q=uR6%211(Q<(C(Q;-1%211uR9%911%73631%=3<91-6%811%@3?31%D3CB1").
Proof. reflexivity. Qed.
Lemma mod_of_decompC : ltac2:(TCodec.tc2 tcn__Jb0DrvC_defs "O'@&R0zr3%3221'=&QNr2%2261r4%9231%6231'>r6&QL&R2r5%2218%421?%73C61&R1r7%2219%;3G1>p051p0>1p0F1pU0K1pTNL1pT@M1pT>N1").
Proof. intros a b q r Hb Hr He. symmetry. apply (Zmod_unique a b q r); lia. Qed.
Lemma add_negmulA : ltac2:(TCodec.tc2 tcn__Jb0DrvC_defs "Q8'@'=&QNzr1%3221r2%5231%7231&R0r3&R4+2+R0%3221%6251'>'RAyR0%211&D(A&R@r4%2261&E(C-1%62:1%72;C%54<421%;3:71&R5%12:G%<2@1%C3@41p0E1p0M1pTHQ61pT>Q71").
Proof.
intros a c H1 H2. apply bv_eq. rewrite alu_add. unfold v_add. rewrite u_mul64.
rewrite !Z_to_bv_unsigned. change (bv_modulus 64) with (2 ^ 64).
rewrite (bv_wrap_small 64 a) by (change (bv_modulus 64) with (2 ^ 64); lia).
rewrite (bv_wrap_small 64 c) by (change (bv_modulus 64) with (2 ^ 64); lia).
rewrite (bv_wrap_small 64 (a - c)) by (change (bv_modulus 64) with (2 ^ 64); lia).
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
replace ((-1) mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity.
destruct (Z.eq_dec c 0) as [->|Hnz].
- rewrite Z.mul_0_r. change ((0) mod 2 ^ 64) with 0. rewrite Z.add_0_r, Z.sub_0_r. apply Z.mod_small. lia.
- rewrite (mod_of_decompC ((2 ^ 64 - 1) * c) (2 ^ 64) (c - 1) (2 ^ 64 - c)) by lia.
rewrite (mod_of_decompC (a + (2 ^ 64 - c)) (2 ^ 64) 1 (a - c)) by lia. reflexivity.
Qed.
Lemma add_neglitA : ltac2:(TCodec.tc2 tcn__Jb0DrvC_defs "Q4'@&QNr1z%3221&QLr3r2%3221%8261&R0r4&R4+2+R0%3221%6251'>'RAyR0%211&D(A&R@r5%2261%327?%63521%G24A%62:1%=3:31p0?1p0G1p0M1pTJQ21pT>Q31").
Proof.
intros a k H0 H1 H2. apply bv_eq. rewrite alu_add. unfold v_add.
rewrite !Z_to_bv_unsigned. change (bv_modulus 64) with (2 ^ 64).
rewrite (bv_wrap_small 64 a) by (change (bv_modulus 64) with (2 ^ 64); lia).
rewrite (bv_wrap_small 64 (a + k)) by (change (bv_modulus 64) with (2 ^ 64); lia).
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
destruct (Z.eq_dec k 0) as [->|Hnz].
- change ((0) mod 2 ^ 64) with 0. rewrite !Z.add_0_r. apply Z.mod_small. lia.
- rewrite (mod_of_decompC k (2 ^ 64) (-1) (2 ^ 64 + k)) by lia.
rewrite (mod_of_decompC (a + (2 ^ 64 + k)) (2 ^ 64) 1 (a + k)) by lia. reflexivity.
Qed.
Lemma plen_valA : ltac2:(TCodec.tc2 tcn__Jb0DrvC_defs "QN'@'6'RAyR0%211%411y8%511%711%811&QNzr3%3221'=&QL+6r4%3221r5%:221&R0&R4+2+Q0%3221%5271%=271'>&QIuR6%22>1&R@r6%22O1%73O41uR9%82B1%:3Q214&Q@(Q>%<18&Q9%11H%4231&Q6%7221&R5r8%221Q1r7%4221%D2QA1%I3QA71p0@1p0D1p0M1p0Q<1pTFQA1pU>QF1p2QL1pQ>QM1").
Proof.
intros Lz Cc vals bl HC HL P70 P73. rewrite plen_x_eqA. cbn [edenot ev]. rewrite P70, P73.
rewrite add_negmulA by lia. rewrite add_neglitA by lia. f_equal. lia.
Qed.
End FPX_2.
