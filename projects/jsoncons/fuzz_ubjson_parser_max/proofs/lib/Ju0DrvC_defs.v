(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import RunEnv
PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib Ju0MainEntry Ju0LibStdioCall
HeapIface DrvKit Ju0Drv_defs Ju0DrvG_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ju0DrvC_defs () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Sem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.DrvKit."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0DrvC_defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0DrvC_defs.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0DrvC_defs.FPX_2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0Drv_defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0LibStdioCall."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymDrive."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymRun."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0C"; "1Some"; "1app"; "1bool"; "1cons"; "1false"; "1fst"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1snd"; "1true"; "2and"]; ["2eq"; "2iff"; "3Z"; "4ALU_ADD"; "4BC_LTU"; "4M_MUL"; "5alu64"; "5mul_div"; "0Lz"; "6ksubl_b"; "8cfglen_x"; "8knGL"; "8knHb0"; "8knHo"; "8knHs"; "8knT0"]; ["8kn_tgt"; "8rHa"; "8rHb"; "8rHo"; "8rHs"; "8rIo"; "8rIs"; "8rJo"; "8rJs"; "8scO"; "8scS"; "8srHo"; "8srHs"; "9cfgF"; "9cfgG"; "9cfgH"]; ["9sx8F"; "9zseq"; "7cfglen_x"; "7plen_x"; "7sx8_x"; ":kn_after"; ";sc_f"; ";sc_fd"; ";sc_ret"; ";stdio_call"; ";stdio_res"; "<blobs_ev"; "=EAlu"; "=ELit"; "=EMd"; "=EVar"]; ["=Env"; "=SCBr"; "=edenot"; "=expr"; "=kentry"; "=s_log"; "=s_pc"; "=scripts"; "=sentry"; "=sidecond"; "=sym_state"; ">vals_ev"; "?In"; "?forallb"; "@add"; "@eqb"]; ["@le"; "@lor"; "@lt"; "@modulo"; "@mul"; "@of_nat"; "@pow"; "@sub"; "0a"; "0b"; "0b0"; "0b1"; "0bl"; "0c"; "0k"; "0n"]; ["0q"; "0r"; "AZ_to_bv"; "Abv"; "Abv_or"; "Abv_unsigned"; "0v71"; "0v72"; "0vals"; "0z"]]).
Section FPX_1. Context {fx : PropExec.FPState}.
Definition STOPS_H : list Z := (0x33f44 :: 0x340ec :: STOPS)%Z.
Definition runH (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS_H scr ss [].
Definition knGS : list kentry := knG 0 5.
Definition rHs := Eval vm_compute in run scr0 (SS 0xab160 srGL [] knGS 71).
Definition srHs : list expr := Eval vm_compute in s_regs (fst (fst rHs)).
Definition knHs : list kentry := Eval vm_compute in kn_after rHs knGS.
Definition scS : stdio_res := Eval vm_compute in the_sc (stdio_call 71 srHs knHs).
Definition srIs0 : list expr := Eval vm_compute in sc_sr scS.
Definition knIs0 : list kentry := Eval vm_compute in sc_kn scS.
Definition rIs := Eval vm_compute in run scr0 (SS (sc_ret scS) srIs0 [] knIs0 103).
Definition srIs : list expr := Eval vm_compute in s_regs (fst (fst rIs)).
Definition knIs : list kentry := Eval vm_compute in kn_after rIs knIs0.
Definition srJs0 : list expr := Eval vm_compute in sr_after_call_j srIs (map ridx c_kept) 103.
Definition knJs0 : list kentry := Eval vm_compute in keep_alloc MSO [] [] knIs.
Definition rJs := Eval vm_compute in run scr0 (SS 0x34018 srJs0 [] knJs0 135).
Definition srJs : list expr := Eval vm_compute in s_regs (fst (fst rJs)).
Definition knJs : list kentry := Eval vm_compute in kn_after rJs knJs0.
Definition kn_hdr : list kentry :=
[KWord (SA (EVar 48) 0) 1 (EVar 71); KWord (SA (EVar 48) 1) 1 (EVar 72); KRange (EVar 71) 0 255; KRange (EVar 72) 0 255].
Definition knGL : list kentry := kn_hdr ++ knG 6 67108863.
Definition scr_taken : scripts := SCR [true] [] [].
Definition rHo := Eval vm_compute in runH scr_taken (SS 0xab160 srGL [] knGL 73).
Definition srHo : list expr := Eval vm_compute in s_regs (fst (fst rHo)).
Definition knHo : list kentry := Eval vm_compute in kn_after rHo knGL.
Definition scO : stdio_res := Eval vm_compute in the_sc (stdio_call 73 srHo knHo).
Definition srIo0 : list expr := Eval vm_compute in sc_sr scO.
Definition knIo0 : list kentry := Eval vm_compute in sc_kn scO.
Definition rIo := Eval vm_compute in run scr0 (SS (sc_ret scO) srIo0 [] knIo0 105).
Definition srIo : list expr := Eval vm_compute in s_regs (fst (fst rIo)).
Definition knIo : list kentry := Eval vm_compute in kn_after rIo knIo0.
Definition srJo0 : list expr := Eval vm_compute in sr_after_call_j srIo (map ridx c_kept) 105.
Definition knJo0 : list kentry := Eval vm_compute in keep_alloc MSO [] [] knIo.
Definition rJo := Eval vm_compute in run scr0 (SS 0x34018 srJo0 [] knJo0 137).
Definition srJo : list expr := Eval vm_compute in s_regs (fst (fst rJo)).
Definition knJo : list kentry := Eval vm_compute in kn_after rJo knJo0.
Definition scr_fall : scripts := SCR [false] [] [].
Definition rHa := Eval vm_compute in runH scr_fall (SS 0xab160 srGL [] knGL 73).
Definition srHa : list expr := Eval vm_compute in s_regs (fst (fst rHa)).
Definition cfglen_x : expr := Eval vm_compute in nth 18 srHa (ELit 0).
Definition sx8_x : expr := Eval vm_compute in nth 21 srHa (ELit 0).
Definition srHb0 : list expr := Eval vm_compute in map (esub sx8_x (EVar 74)) (map (esub cfglen_x (EVar 73)) srHa).
Definition PX : expr := EAlu ALU_ADD (EVar 48) (EVar 73).
Definition kn_bm : list kentry :=
[KRange (EVar 73) 0 32767;
KWord (SA PX 2) 1 (EVar 75); KWord (SA PX 3) 1 (EVar 76); KWord (SA PX 4) 1 (EVar 77); KWord (SA PX 5) 1 (EVar 78);
KRange (EVar 75) 0 255; KRange (EVar 76) 0 255; KRange (EVar 77) 0 255; KRange (EVar 78) 0 255].
Definition knHb0 : list kentry := kn_bm ++ knGL.
Definition rHb := Eval vm_compute in runH scr0 (SS 0x33f44 srHb0 [] knHb0 79).
Definition srHb : list expr := Eval vm_compute in s_regs (fst (fst rHb)).
Definition plen_x : expr := Eval vm_compute in nth 13 srHb (ELit 0).
Definition srT0 : list expr := Eval vm_compute in map (esub plen_x (EVar 79)) srHb.
Definition kn_tgt : list kentry :=
[KRange (EVar 73) 0 32767; KRange (EVar 79) 0 67108857; KWord (SA (EVar 48) 2) 1 (EVar 80); KRange (EVar 80) 0 255].
Definition knT0 : list kentry := kn_tgt ++ knGL.
Lemma hdr_itinerary_ok : ltac2:(TCodec.tc2 tcn__Ju0DrvC_defs "UK'?'@'<'B'7'R9%211%5241(;&R6&6'R:%:216'R7&Q4%53321%635:1%811&=%138=4%<4A>31+ckT<(9%11B%@4EB31%H3B51':'QJ%211&QIuR7&Q<&N%43321(1&Q:%2291%Q43941%Q42Q3Q3%Q521Q4&QH%116&QF%118%Q44Q9Q931&QG%11;%Q749Q<31+cmY4+flQ@%Q:4Q?Q?21+2%Q<4>QA21%QD3>61'R8%QC11%QF2QA1&Q6%Q@3Q>Q=1%QA3Q@QE1%QC11%Q;3QBQG3%QF4QKQH21&R5%115%QI4QJ:31+c^^8%QK4R0QM1Q<%Q>1>%QM4QN>21%R53>51&Q8%QN3QLQK1%QO3QNR31%R111%QI3R0R53%R44R9R621%>14%R64R7G21+cVi4%R84R=R:1QI%R94R:J1=%RA3J41&Q3%R:3R8R71%R;3R:R?1%R=11%R53R<RA3%R@4RERB21(4(R1(>(D(QOuR6%211(QL(C&J(QM+6%211%63541%=4<;81%?3S31RA%S14S6S3RD1%S93S3B1uR9&Q;&M%RA3321&Q9%R>2RE1%S@3RE31%R:13%R914%S<4SASA21%R816%S>4R@SC21%SF3R@1R3&Q5%S?3S=S<1%S@3S?SD1%SB11%S:3SASF3%SE4SJSG21%QO14%SG4SHR821%SO3R81QK&Q7%SH3SFSE1%SI3SHSM1%SK11%SC3SJSO3%SN4T3T021%R814%T04T1RA21%T83RA1QH&Q1%T13SOSN1%T23T1T61%T411%SL3T3T83%T74T<T921%RA14%T94T:RJ21+V_j4(5%QJ41QHQEQ>%QL3T@1SN%T>4TCT@41%T?4T@S01RC%TG3S071'R4%TF11&QE&K%22C1%TM3412&Q2%TF3TDTC1%TG3TFTK1%TI11%TA3THTM3%TL4U1TN21%S614%TN4TOS?21+V`W<%U04U5U21TA%U14U2SB1S5%U93SB41&L%A2=1%U<3C12%U>241%U?2A1%U@2H1%UA2Q81%UB2QB1%UC2QL1%UD2R31%UE2R;1%UF2S41%UG2SA1%UH2T31%UI2TD1%UJ2U11").
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma knT0_sub : ltac2:(TCodec.tc2 tcn__Ju0DrvC_defs "<'@'3&I&2'R4&Q0&L%43321&O%7221(>%;3:21").
Proof. vm_compute. reflexivity. Qed.
Lemma knGL_sub_Hb0 : ltac2:(TCodec.tc2 tcn__Ju0DrvC_defs "8'@'3&I&L&K%3221(>%73621").
Proof. vm_compute. reflexivity. Qed.
End FPX_1.
Section FPX_2. Context {fx : PropExec.FPState}.
Definition cfgF (v71 v72 : word) : word :=
edenot (Env (fun n => match n with 71%nat => v71 | 72%nat => v72 | _ => Z_to_bv 64 0 end) (blobs_ev [])) cfglen_x.
Lemma cfglen_x_cfgF : ltac2:(TCodec.tc2 tcn__Ju0DrvC_defs "N'7'S3yR0%211%411y8%511%711%811'@&R2(R0&R;r2%211&QKr1%211%7241&QB%:221&Q=uR7%;2:1uR8%=2<1%5231%B3H71pUJD1pVBI1").
Proof. intros. reflexivity. Qed.
Definition zseq (n : nat) : list Z := map Z.of_nat (seq 0 n).
Lemma in_zseq : ltac2:(TCodec.tc2 tcn__Ju0DrvC_defs "E'8'B&A&R<r1&QAr2%211%53741'?&R@z%2218&RB&RE%119%32<1%8251%@2:1pVDB1pV0D1").
Proof.
intros n z. unfold zseq. rewrite in_map_iff. split.
- intros (k & <- & Hk). apply in_seq in Hk. lia.
- intros Hz. exists (Z.to_nat z). split; [lia|]. apply in_seq. lia.
Qed.
Definition cfgG (v72 : word) : word :=
alu64 ALU_SRL (mul_div M_MUL (Z_to_bv 64 144115188075855872) (ext_val true 0 1 v72)) (Z_to_bv 64 49).
Definition cfgH (v71 : word) : word := ext_val false 0 1 v71.
Lemma cfgF_split : ltac2:(TCodec.tc2 tcn__Ju0DrvC_defs "A'S3yR0%211'@&Q=r2r1%3221&S4&Q>%114&Q?%117%53<31%;3<71pV@=1pV>>1").
Proof. intros v71 v72. reflexivity. Qed.
Lemma cfgG_tab : ltac2:(TCodec.tc2 tcn__Ju0DrvC_defs "K'@'3&R='B&R?&S5yR0&Q>&S2r1%2241%411%7261&RD+X0&RC+T0%2281%5241%?271qUHA1&QAuX0%211%F3E41(>%J3I21").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cfgH_tab : ltac2:(TCodec.tc2 tcn__Ju0DrvC_defs "E'@'3&R='B&R?&S5yR0&Q?&S2r1%2241%411%7261%9214qUF;1&QAuX0%211%@3?41(>%D3C21").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lor_tab : ltac2:(TCodec.tc2 tcn__Ju0DrvC_defs "J'@'3&R='B&R?&RA&RD+X0r2%3221r1%6221&R>%1243%:231qUD<1&QAuX0%211%A3@41qUBA1uT0%611%E3D31(>%I3H21").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cfgF_val : ltac2:(TCodec.tc2 tcn__Ju0DrvC_defs "Q2'B'?&R@zr2%3221&RB+X0%2241%8241'@'S3yR0%211&Q=&S2r4%2251r3%4271%6231&RC&R>&RD%12A6%3291+QPP0%6221%=2@1%C3@91p0E1p0F1pUHQ01pUFQ11").
Proof.
intros b0 b1 H0 H1.
pose proof cfgG_tab as TG. rewrite forallb_forall in TG. specialize (TG b1 (proj2 (in_zseq 256 b1) ltac:(cbn; lia))). apply Z.eqb_eq in TG.
pose proof cfgH_tab as TH. rewrite forallb_forall in TH. specialize (TH b0 (proj2 (in_zseq 256 b0) ltac:(cbn; lia))). apply Z.eqb_eq in TH.
pose proof (Z.mod_pos_bound b1 128 ltac:(lia)) as HM.
pose proof lor_tab as TL. rewrite forallb_forall in TL. specialize (TL (b1 mod 128)%Z (proj2 (in_zseq 128 (b1 mod 128)%Z) ltac:(cbn; lia))).
rewrite forallb_forall in TL. specialize (TL b0 (proj2 (in_zseq 256 b0) ltac:(cbn; lia))). apply Z.eqb_eq in TL.
apply bv_eq. rewrite cfgF_split, stdpp.bitvector.definitions.bv_or_unsigned, TG, TH, TL. symmetry.
assert (E : ((b0 + 256 * b1) mod 32768 = 256 * (b1 mod 128) + b0)%Z).
{ pose proof (Z.div_mod b1 128 ltac:(lia)) as D.
symmetry. apply (Zmod_unique (b0 + 256 * b1) 32768 (b1 / 128)); lia. }
rewrite E. apply u_small. lia.
Qed.
Definition sx8F (v72 : word) : word := ext_val true 0 1 v72.
Lemma sx8_x_sx8F : ltac2:(TCodec.tc2 tcn__Ju0DrvC_defs "L'7'S3yR0%211%411y8%511%711%811'@&R2(R0&R;r2%211&QKr1%211%7241&QD%:221&Q@uR8%;2:1%311%@3F51pUJB1pVBG1").
Proof. intros. reflexivity. Qed.
Lemma plen_x_eq : ltac2:(TCodec.tc2 tcn__Ju0DrvC_defs "E'@'R3&QC(QL(C(QOuR6%211(QN(E(QM-1%211uR9%911%73631%=3<91-6%811%@3?31%D3CB1").
Proof. reflexivity. Qed.
Lemma mod_of_decomp' : ltac2:(TCodec.tc2 tcn__Ju0DrvC_defs "O'B&RBzr3%3221'?&R@r2%2261r4%9231%6231'@r6&R>&RDr5%2218%421?%73C61&RCr7%2219%;3G1>p051p0>1p0F1pV4K1pV2L1pUDM1pUBN1").
Proof. intros a b q r Hb Hr He. symmetry. apply (Zmod_unique a b q r); lia. Qed.
Lemma add_negmul : ltac2:(TCodec.tc2 tcn__Ju0DrvC_defs "Q8'B'?&R@zr1%3221r2%5231%7231&RBr3&RF+2+R0%3221%6251'@'S3yR0%211&F(C&S2r4%2261&G(E-1%62:1%72;C%54<421%;3:71&RG%12:G%<2@1%C3@41p0E1p0M1pULQ61pUBQ71").
Proof.
intros a c H1 H2. apply bv_eq. rewrite alu_add. unfold v_add. rewrite u_mul64.
rewrite !Z_to_bv_unsigned. change (bv_modulus 64) with (2 ^ 64)%Z.
rewrite (bv_wrap_small 64 a) by (change (bv_modulus 64) with (2 ^ 64)%Z; lia).
rewrite (bv_wrap_small 64 c) by (change (bv_modulus 64) with (2 ^ 64)%Z; lia).
rewrite (bv_wrap_small 64 (a - c)) by (change (bv_modulus 64) with (2 ^ 64)%Z; lia).
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z.
replace ((-1) mod 2 ^ 64)%Z with (2 ^ 64 - 1)%Z by reflexivity.
destruct (Z.eq_dec c 0) as [->|Hnz].
- rewrite Z.mul_0_r. change ((0) mod 2 ^ 64)%Z with 0%Z. rewrite Z.add_0_r, Z.sub_0_r. apply Z.mod_small. lia.
- rewrite (mod_of_decomp' ((2 ^ 64 - 1) * c) (2 ^ 64) (c - 1) (2 ^ 64 - c)) by lia.
rewrite (mod_of_decomp' (a + (2 ^ 64 - c)) (2 ^ 64) 1 (a - c)) by lia. reflexivity.
Qed.
Lemma add_neglit : ltac2:(TCodec.tc2 tcn__Ju0DrvC_defs "Q4'B&R@r1z%3221&R>r3r2%3221%8261&RBr4&RF+2+R0%3221%6251'@'S3yR0%211&F(C&S2r5%2261%327?%63521%G24A%62:1%=3:31p0?1p0G1p0M1pUNQ21pUBQ31").
Proof.
intros a k H0 H1 H2. apply bv_eq. rewrite alu_add. unfold v_add.
rewrite !Z_to_bv_unsigned. change (bv_modulus 64) with (2 ^ 64)%Z.
rewrite (bv_wrap_small 64 a) by (change (bv_modulus 64) with (2 ^ 64)%Z; lia).
rewrite (bv_wrap_small 64 (a + k)) by (change (bv_modulus 64) with (2 ^ 64)%Z; lia).
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z.
destruct (Z.eq_dec k 0) as [->|Hnz].
- change ((0) mod 2 ^ 64)%Z with 0%Z. rewrite !Z.add_0_r. apply Z.mod_small. lia.
- rewrite (mod_of_decomp' k (2 ^ 64) (-1) (2 ^ 64 + k)) by lia.
rewrite (mod_of_decomp' (a + (2 ^ 64 + k)) (2 ^ 64) 1 (a + k)) by lia. reflexivity.
Qed.
Lemma plen_val : ltac2:(TCodec.tc2 tcn__Ju0DrvC_defs "QN'B'7'S3yR0%211%411y8%511%711%811&R@zr3%3221'?&R>+6r4%3221r5%:221&RB&RF+2+Q0%3221%5271%=271'@&R;uR6%22>1&S2r6%22O1%73O41uR9%82B1%:3Q214&R2(R0%<18&QK%11H%4231&QC%7221&RGr8%221Q1r7%4221%D2QA1%I3QA71p0@1p0D1p0M1p0Q<1pUJQA1pVBQF1p2QL1pQBQM1").
Proof.
intros Lz C vals bl HC HL P70 P73. rewrite plen_x_eq. cbn [edenot ev]. rewrite P70, P73.
rewrite add_negmul by lia. rewrite add_neglit by lia. f_equal. lia.
Qed.
End FPX_2.
