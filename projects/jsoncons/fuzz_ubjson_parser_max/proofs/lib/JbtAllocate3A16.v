(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtTac JbtLeaf JbtRzLog JbtPoison JbtAllocA JbtAllocB JbtAllocG JbtAllocV JbtInitCache JbtPopulate1 ArtRuns ArtRunsMem
JbtCls JbtFp JbtClsPop3 JbtClsRep JbtClsGfa2 JbtClsRefill JbtCellEx JbtCARSpec JbtAlloc3Pure JbtDepotA JbtDepot JbtAllocPre3 JbtAllocPost JbtAllocate3
JbtAllocA16 JbtAllocB16 JbtAllocPre3A16 JbtAllocPostA16.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtAllocate3A16 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtRuns."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.As0Tables.AsanTab."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtAllocA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtAllocB16."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtAllocate3."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtAllocate3A16."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtCARSpec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtCls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtDepot."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtLeaf."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtPoison."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtRzLog."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1S"; "1app"; "1bool"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1true"; "2I"; "2and"; "2eq"; "2not"; "2or"; "3Z"]; ["0EVOK"; "0GR"; "0HI"; "4machine_state"; "5bvmap"; "0M'"; "0M0"; "0Q"; "6apart"; "6cell"; "6wr"; "7aev"; "7aruns"; "8class_id"; "8class_size"; "8rz_log"]; ["9ret_ok"; ":art_alloc_rodata"; ";art_hdr_b1_16"; "<art_alloc3_fp"; "=art_alloc3_fp16"; ">art_ca_cptr"; ">art_ca_events"; ">art_ca_pre"; ">art_cls_pop"; "?art_cls"; "?art_cls_mfa'"; "?art_cls_needs_populate"; "?art_cls_new"; "?art_cls_ok"; "?art_cls_rep"; "?art_cptr_ok"]; ["?art_evok_list"; "?art_geo"; "?art_pc_hdr"; "?art_prim_consts"; "?cl_au"; "?cl_cache"; "?cl_free"; "?cl_mu"; "@DInvD"; "@DPreD"; "@DRoD"; "Aart_tsd"; "Bart_layout"; "Cart_rz_rodata"; "Dgetr"; "Dmkst"]; ["Emem_grows"; "Floaded_segments"; "0S"; "GIn"; "Hadd"; "Hland"; "Hle"; "Hlt"; "Hmodulo"; "Hmul"; "Hof_nat"; "Hpow"; "Hsub"; "0ab"; "0b1"; "0blk"]; ["0c"; "0cl"; "0ctx"; "0fx"; "0inited"; "0j"; "0kb"; "0key"; "0km"; "0l2"; "0loff"; "0log"; "0m8"; "0n"; "0ob"; "0q16"]; ["0qn"; "0qr"; "0qs"; "0qz"; "0r"; "0raw"; "0regs"; "0regs'"; "0ris"; "0rl"; "0rom"; "0rs"; "0rz"; "0shb"; "0sp"; "0spb"]; ["IBV"; "IZ_to_bv"; "Ibv"; "Ibv_unsigned"; "0stk"; "0szt"; "0t"; "0tp"; "0trp"; "0tsd"; "0v"; "0w"; "0x"; "0y"]]).
Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Definition art_alloc3_fp16 (sp t spb ris qs c km ab rz n rs l2 blk : Z) (x : Z) : Prop :=
(sp - 1920 <= x < sp) \/ art_ca_fp (sp - 128) t spb ris qs c km x
\/ (ab <= x < ab + rz + n) \/ (2147450880 + (ab + rz) / 8 <= x < 2147450880 + (ab + rz) / 8 + rs / 8)
\/ (t + 2800 <= x < t + 2824) \/ (t + 2912 + 8 * c <= x < t + 2920 + 8 * c) \/ dprivD l2 blk x.
Lemma art_alloc3_fp16_sub : ltac2:(TCodec.tc2 tcn__JbtAllocate3A16 "Q3'?&Q4r>r=r<r;r:r9r8r7r6r5r4r3r2r1%?>>=<;:987654321&Q3r?%2>1A@?>=<;:98765p041pWJE1pU0F1pUDG1pVHH1pULI1pVJJ1pTLK1pUBL1pU2M1pV6N1pVBO1pW0Q01pW>Q11pVNQ21").
Proof.
intros sp t spb ris qs c km ab rz n rs l2 blk x F. unfold art_alloc3_fp16 in F. unfold art_alloc3_fp.
destruct F as [F|F]; [left; lia|right; exact F].
Qed.
Lemma art_alloc3_fp16_window : ltac2:(TCodec.tc2 tcn__JbtAllocate3A16 "QB'?&Q4&R<r>+RT0%3221r=r<r;r:r9r8r7r6r5r4r3r2r1%B>>=<;:987654321'>';&R6r?+TP0%G221%4219&R7%12;5%8231&Q3+RS0%N291%3>1NKJIHGFEDCBA@%>251p0@1pWJQ41pU0Q51pUDQ61pVHQ71pULQ81pVJQ91pTLQ:1pUBQ;1pU2Q<1pV6Q=1pVBQ>1pW0Q?1pW>Q@1pT6QA1").
Proof.
intros S t spb ris qs c km ab rz n rs l2 blk x F. unfold art_alloc3_fp16 in F. unfold art_alloc3_fp.
destruct F as [F|[F|F]]; [left; lia| |right; right; right; exact F].
unfold art_ca_fp in F |- *. destruct F as [F|[F|F]]; [left; lia| |right; right; left; right; right; exact F].
unfold art_refill_fp in F |- *. destruct F as [F|F]; [left; lia|]. right; right; left; right; left; right; exact F.
Qed.
Lemma art_hdr_b1_type_16 : ltac2:(TCodec.tc2 tcn__JbtAllocate3A16 "L'?';&R6zr1%3221&R7+X0%2241%8241'<&R8&R5&Q2r2%211+WC%5221+4%8221+1%;3E21%D2C5%A26@%G221%H241p0A1pUNK1").
Proof.
intros ob Hob.
assert (H : forallb (fun o => (Z.land (art_hdr_b1_16 o) 243 mod 4 =? 1) && (0 <=? Z.land (art_hdr_b1_16 o) 243) && (Z.land (art_hdr_b1_16 o) 243 <? 256)) (AsanTab.zrange 0 256) = true)
by (vm_compute; reflexivity).
rewrite forallb_forall in H. specialize (H ob ltac:(unfold AsanTab.zrange; apply AsanTab.in_ziota; lia)).
apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3. lia.
Qed.
Section Spec.
Variable EVOK : list aev -> aev -> Prop.
Variable GR : list aev -> (word -> option byte) -> Z -> Z -> Prop.
Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_art_allocate3_16 := (ltac2:(TCodec.tc2 tcn__JbtAllocate3A16 "hA'5'K%211'C!p021p041&Dy5'SByR0%211%5241'8y8%611%311p061'?'6'2'Q9&M&R4r8+@%3221r:%5221%711&Q5r1r2%3221rE&R9&R;+2+Q0%3221%5281%B271%72;A%D221+QoooPP0+XP0rD%<221%I241r3+M%?2>1%A231%N251'<&QNrQ5(S@+1(:%33QD21%6251rQ2%93QD21&Q0rQ3%211rQ7%;3QLO9%>221&SA%12QM6%B3QM31rQ8+4%B3R31@%E231rQ0%82R41%I3R431rQ9+:%I3R:1G%L231+QWTnH%?2R;1%Q03R;31rQ:+;%Q03RA1N%Q3231rQ4%F2RB1%Q73RB31rQ;+<%Q73RH1Q5%Q:231%L2RHR9%Q=3RH21rQ<+=%Q=3RN1Q;%Q@231%Q22RNQ@%QC3RN21rQ=+>%QC3S41QA%QF231%Q82S4QD%QI3S421rQ>+?%QI3S:1QG%QL231%QN3S916&R6+8%221Q7rJ&O%11Q3%R53S931rK%RI2RH1%RK2S51%R93S=71%RM2S78%R;3S?51';%>2R97+T0%@291%4231rI%S52B1rH%SC221%RE3SIK1z%H216+7%J281%>231rMrL%S@2M1%RN3T231rN%S03T41FrQBrO%Q4221%T323<%Q6231%J231%T62R@T4%T721S0+RPP0%Q;221&QArQErQ?rQ@%483QE2>1R1R7R>rQF&R<rQG+Ql0%3221%QF251+TP0%TF251rQH%QJ221rQI+RS0%TK221+Q?%T@2T?1%R0231rQJ%R221?%U12:TOrQK%U321>%R6231%R72Q@RH&R7+R0%TK2TJ1%32RL1%QO251rQN%R>21RC%U12R>RD%U>2Q21rQO%U@21K%RC231%RD2QMQ1rQM%UD21M%RG2Q=1%UF2;M%UG21T4+Vb\P0%RK221+V[jY8+RH%Q<2=1%RO231%S024C+D%UC2UB1%V12Q@1rR4%S5221+G%UH2UG1%V62QE1rR5%S:221&H%14QA:KQErR1%34Q=<1QG+Q5%V12V01%V?21QJ%74Q>@Q11rQL+QoonlP0+`PQoooPP0%R4212%<44E31rR3%>46B1R2%?4Q5CAR3%@4Q>D3:%A4Q;E86&J&R1rRBrR?%R?21R=%54431R>rRCrR8%84721R>rRD%VI2V?N%W62VA1+Q2%VK2VJ1%>4=531&Q1rRE%211&IrRF+RQTHu1%45E321UN&QMrRG%211&QLrRH%211&QKrRIrRArR@rR>%564Q032O1&QCrR=rR<rRJ%43321rRK+QWehH%H5Q921EW2rRL+QgkU2%K5Q<21HTCrRM+Sa0%X;2V>1u8+Q8%X12X01%Q25QC6431rRN+Sa8%XB2VE1u2%Q75QH421XBrRO+Sa:%XG2VJ1+RP0%Q<5QM4261rS0+QiiX0%Q?5R021@U7rS1+QWXaH+Q<%Y0221u4%QE5R6521T=rS2+QD%Y5271+UN%QJ5R;4261rS3+RE%Y:2<1%QN5R?31QKX8rS4+QVdP0%R15RB21Q2QHrS5%Y@2Q0QG%R45RE21@ULrS6%R65RG1Q@Q7Q=rS7%YE2Q<VF%R95RJ21EV1rS8%R;5RL1EQ<R=rS9%YJ2BVK%R>5RO21Q?R@&QB+V@%YN2Q91rS:%432R01&Q>%Z22Q85rR;rS;%463QEQL2R51&Q=%12R7R8&=%[01Z>&QE%11R?(7%11ZB%Y?3531%711(9%YB3ZDRF1p031&QG%11SF+XPP0%Z:21R6%YH3ZL31%>1RM%YJ3@1<&Q;%12S0S1%YM3ZO1<%:1T0%ZN219+S`PPPP0%X2221&Q:&R:&4&QF%11T8%32[;1%511&Q<%12S?T<%[:231%:2T>1+`PPPP0%X?221%X32>1p0C1p0G1&Q@v@rSB&Q6%13R=SJSK%53431&QD%11TG%[=2XJ[A%XL221%Q81TJ%VF231%XB231rSC%[O2T4[F+WJ%TD5U532TA1p051pWL\81&R3&1%QL1U2%Q31U3%33\=21%53\>\11rSD%[O2[M\2%\<2TB1%U05UA31TM=p051pWF\D1&QH(0%11U4%34S@SF1E&QI%14SB;SHSK&QJrSE%211%[I2[OZN%\J2U7SB%[<2]81%[M3]831r4%[N21[ArSG%[A2]=1%\23]=31r5%\321[NrSI%\63]A21%]D1]E(3+3%\73]H1\5%\83]IZ;\6+9%\:3]K1\8+B%\<3]M1\:+C%\>3]O1\<%\?3^0WB\=+E%\A3^21\?+F%\C3^41\A%\D3^5WB\B+H%\F3^71\D+I%\H3^91\F+J%\J3^;1\H+K%\L3^=1\J%SC1I%I3J21%J3K51%K3L81%L3M;1%M3N>1%N3O@1%O3Q0C1%Q03Q1F1%Q13Q2H1%Q23Q3K1%Q33Q4N1%Q43Q5Q11%Q53Q6\H1%Q63Q7Q41%R:3Q8^61%]?2^>^6rSO%]A21^8%]C3^N31p051pV:Q>1&R0rSMr6%3221&Q4rSLrSArS@rS?rSJrS>rS=&SC%12_?^J%:>9RIS@87V>6VJU:5U?431%TL11r9%11^MrT0%11^O%^:3_@31p061pWJ_G1%RL4=<V9_;%_=2RFU@%UB31TN9rSF%_@21UC&Q8&Q7%12VFV@%311%UD65S;SGVH1_A%42VCV>%611%UB2VE1&Q?&N%11VC%:2VDV@%T611%5331VKr<%]22\;1+X0%ZL231%\H231&R8r=%221^C%_83`<1_4r?%`92VMQ=%[J21`8%XN5Y?31XK_Mr@%`=2VNQB%[N21]D%Y25YC31XO7rA%`A2VOTN%\221]N%Y65YG31X0\NrB%`E2W1TG%\621^>rT4%Y;5YL42WG1rC%`>2`<W1%`K2W71%Y?5Z031Y<TL%]O2]8`E%[H2`FU;%]D221rFrS<%`F2`D1%a32W41%`H2`FQE%a5221%a621`M%YJ5Z;71YG]Bp091pU<a>1%`;3a?R?]E%W311%a<27U>%Z05ZA=1YMUJp031%W51R@%`A3W71W3%VG2RBRD%`C3aE1W2+QPP0%\>2a<1%^:2H1%a:2a8RJ%a;2a9RI%aH221rT1%a>271%aK21aB%^N241rSH%aN261%\I241%^E241%WI11rT2%aG2@1%b42S71%b521a;%ZI5[:_11ZFV6p061p0C1pU<b>1p0H1p0K1%a=3bA?b:%X511+\hkdfgWVVmUeI%[25[C^MS?Z31%b@2S@_A%bA2SAU=%^221b@%[65[G_13Z71%_9251p081rTBrTA%W43FSKSL%VD3c?21&QOvRCrT=rT>%453_>2_<1%9261p0;1p0F1p0QD1p0QJ1p0R81p0R=1p0RC1p0RH1p0RM1p0S21p0S71p0S=1p0SD1p0SH1p0T01p0T31p0T51p0TI1p0TN1p0V>1p0VC1p0VI1pTNcK1pQ<cM1pV@d31'LvA+ZWeD%bJ3d91bH/01d9%Q45Q3R11VOT?%67]3X=5Q4U1VK1p081p0W91p0W=1p0W@1p0WE1p0X21p0X@1p0XG1p0YA1p0YG1p0Z31p0Z61p0Z<1p0ZB1p0ZF1p0ZI1p0ZM1p0[01p0[41p0[81p0[=1p0[C1p0[J1p0[N1p0\41p0\:1p0\B1p0\F1p0\J1p0]01p0]71p0];1p0]?1p0]E1p0]I1p0^01p0^41p0^;1p0^=1p0^?1p0^A1p0^D1p0^J1p0^O1p0_21p0_51p0_;1p0_A1p0_C1p0_H1p0_M1p0`11p0`31p0`91p0`<1p0`=1p0`D1p0`I1p0`L1p0a31p0a81p0a?1p0aE1p0aJ1p0b11p0b41p0b91p0b?1p0bE1p0bK1p0bN1p0c31p0c81p0c<1p0cB1p0cI1p0d01p0d71p0d?1p0dG1p0dO1p0e61p0e:1tVLfHeE1tTLfIf01tWHfJf;1tU2fKf@1pU4fI1pU:fK1pU>fM1pV0fO1pUJg01pV2g11pV4g21pVHg31pV8g41pVJg51pVDg61pW<g71pWBg81pU0g91pUDg:1pUBg;1pV6g<1pVBg=1pW0g>1pUFg?1pW>g@1pU6gA1pWDgB1pU@gC1pW@gD1pW:gE1pULgF1pQ6gG1pVNgH1pV<h01pVFgK1pQ>gL1pV>h21pUHh=1pQ@h:1")) (only parsing).
Variable Q : ltac:(sec_ty2 constr:(SEC_T_art_allocate3_16) 0%nat 0%nat).
Variable log : ltac:(sec_ty2 constr:(SEC_T_art_allocate3_16) 1%nat 0%nat).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_allocate3_16) 2%nat 0%nat).
Variable M0 : ltac:(sec_ty2 constr:(SEC_T_art_allocate3_16) 3%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_allocate3_16) 4%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_allocate3_16) 5%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_allocate3_16) 6%nat 0%nat).
Variable HI : ltac:(sec_ty2 constr:(SEC_T_art_allocate3_16) 7%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_allocate3_16) 8%nat 0%nat).
Variable stk : ltac:(sec_ty2 constr:(SEC_T_art_allocate3_16) 9%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_art_allocate3_16) 10%nat 0%nat).
Variable key : ltac:(sec_ty2 constr:(SEC_T_art_allocate3_16) 11%nat 0%nat).
Variable tsd : ltac:(sec_ty2 constr:(SEC_T_art_allocate3_16) 12%nat 0%nat).
Variable ctx : ltac:(sec_ty2 constr:(SEC_T_art_allocate3_16) 13%nat 0%nat).
Variable t : ltac:(sec_ty2 constr:(SEC_T_art_allocate3_16) 14%nat 0%nat).
Variable loff : ltac:(sec_ty2 constr:(SEC_T_art_allocate3_16) 15%nat 0%nat).
Variable spb : ltac:(sec_ty2 constr:(SEC_T_art_allocate3_16) 16%nat 0%nat).
Theorem art_allocate3_16 : ltac:(sec_stmt2 constr:(SEC_T_art_allocate3_16) 17%nat 0%nat).
Proof using Type Q log regs M0 rom raw sp HI n stk tp key tsd ctx t loff spb.
intros ris qs km l2 blk trp szt rl rz qz rs qr qn m8 q16 kb inited cl c w ab shb
H1 Hret H2 H4 H10 H11 H12 H13 H14 H15
Hn Erl Erz Erz16 Hqz En Hm8 Ers Ers16 Hrs Hprim
GEO HHI HHI' Hsp' Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd
Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs
W Wt Wsh RO C1046 RZRO L TSD PC Ci Cr Cmax Cmin16 Cmax2048 Chook Cmfs Cfb Cpp Cg Clsan Ctctx Ctid Ctrp Cszt
PH RC OK Hin Emu Room EV PZ1 PZ2 DI DP DR K.
assert (Eab : ab = spb + c * 2 ^ 32 + w * 16) by reflexivity.
assert (Eshb : shb = 2147450880 + 8192 * qs + c * 2 ^ 29) by reflexivity.
clearbody ab shb.
pose proof (AsanTab.class_id_ok (rs + 16 + rz) ltac:(lia)) as (Hc & Hfit & _). fold c in Hc, Hfit.
pose proof GEO as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & G9 & G10 & G11 & (qt & Et) & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22).
assert (At_i : apart t 4096 0x10000 (0x693000 - 0x10000)) by (unfold apart; clear - G9; lia).
assert (At_s : apart t 4096 0x7fff7000 (0x10007fff8000 - 0x7fff7000)) by (unfold apart; clear - G10; lia).
assert (Ac_i : apart ctx 4096 0x10000 (0x693000 - 0x10000)) by (unfold apart; clear - G15; lia).
assert (Ac_s : apart ctx 4096 0x7fff7000 (0x10007fff8000 - 0x7fff7000)) by (unfold apart; clear - G16; lia).
change (hid (t + 4096 <= 0x10000 \/ 0x693000 <= t)) in G9. change (hid (ctx + 4096 <= 0x10000 \/ 0x693000 <= ctx)) in G15.
clear G10 G16.
pose proof OK as (Hl16 & (Hau0 & Haumu) & _ & _ & _ & Hmu3 & _ & (Hmfa0 & Hmfa1) & Hnf4 & Hfor & _).
assert (Hkm : 0 <= km) by lia.
assert (Hkm' : 262144 * km <= 3758096384) by lia.
pose proof DI as (dN & dTF & dST & DG1 & DG2 & DG3 & DG4 & DG5 & DG6 & DG7 & _).
pose proof TSD as (_ & _ & _ & _ & _ & TR).
assert (Hq16 : (n + 15) / 16 = q16). { symmetry. apply (Z.div_unique _ 16 q16 (n + 15 - 16 * q16)); lia. }
assert (Ers_max : rs = (Z.max n 8 + 15) / 16 * 16) by (rewrite Z.max_l by lia; rewrite Hq16; lia).
destruct (art_allocate_pre3a_16 regs M0 rom raw sp 1283032 n stk tp key tsd ctx t rl rs qr rz qz
H1 H2 H4 H10 H11 H12 H13 H14 H15 ltac:(lia) Erl Erz Erz16 Hqz
Ers_max Ers ltac:(rewrite Z.max_l by lia; lia) Hprim
ltac:(lia) Hsp' Hstk Hstk' ltac:(lia) ltac:(lia)
G7 ltac:(lia) G9 ltac:(unfold apart; lia) ltac:(unfold apart; lia) G15 G18 G19 G20 G21 G22
W RO C1046 RZRO TSD Ci Cr Cmax Cmin16 Cmax2048)
as (r5 & M5 & RUN5 & P5_1 & P5_2 & P5_4 & P5_8 & P5_9 & P5_10 & P5_11 & P5_12 & P5_13 & P5_19 & P5_20 & P5_21 & P5_22 & P5_23 & P5_25 & P5_26 & P5_27 & P5_3
& G05 & AG05 & F120 & F112 & F104 & F96 & F88 & F80 & F72 & F64 & F56 & F48 & F40 & F32 & F24 & F8 & F16).
eapply ar_steps; [exact RUN5|].
assert (A05 : art_agree [(sp - 144, 144)] M0 M5). { intros x Hx. apply AG05. cbn in Hx. lia. }
assert (W5 : wrA M5 (sp - 128 - 720) 720) by (eapply wr_grows; [exact G05|]; eapply wr_sub; [exact W|lia|lia]).
assert (Wt5 : wrA M5 t 4096) by (eapply wr_grows; [exact G05|exact Wt]).
assert (Wsh5 : wrA M5 (2147450880 + 8192 * qs) (2 ^ 34)) by (eapply wr_grows; [exact G05|exact Wsh]).
assert (PC5 : art_prim_consts spb ris M5). { eapply art_prim_consts_fp; [exact A05| |exact PC]. intros z Hz. cbn. clear - Hz HHI G1. repeat split; lia. }
assert (L5 : art_layout M5). { eapply art_layout_fp; [exact A05| |exact L]. intros z Hz. cbn. clear - Hz HHI G1. repeat split; lia. }
assert (T5 : art_tsd M5 tp key tsd ctx t).
{ eapply art_tsd_fp; [exact A05| | |exact G19|exact G20|exact G21|exact G22|exact TSD].
- intros z Hz. cbn. clear - Hz HHI G1. repeat split; lia.
- intros z Hz. cbn. clear - Hz HHI G1 G13 G14. repeat split; lia. }
assert (PH5 : art_pc_hdr (t + 208) inited M5).
{ apply (art_pc_hdr_tr _ (t + 208) inited M0 M5 ltac:(lia) ltac:(lia) A05); [|exact PH]. intros c' Hc'. clear - Hc' HHI G7 G8. zarith_f. }
assert (RC5 : art_cls_rep (t + 208) spb ris c cl M5).
{ apply (art_cls_rep_tr [(sp - 144, 144)] (t + 208) spb ris c cl M0 M5); first [ exact RC | exact G05 | exact A05 | exact Hl16 | lia | idtac ];
clear - Hc HHI Hsp' G1 G2 G6 Eris G4 Espb G7 G8 Hnf4 Hmfa1; zarith_f. }
assert (Hs8 : (rs + 16 + rz) mod 8 = 0). { rewrite Ers, Erz16. replace (8 * qr + 16 + 16 * qz) with ((qr + 2 + 2 * qz) * 8) by lia. apply Z_mod_mult. }
apply (aruns_bind ASEGS EVOK GR (fun lg st => aruns ASEGS EVOK GR Q lg st) Q); [|intros lg st H; exact H].
apply (art_ca_rspec_holds EVOK GR (fun lg st => aruns ASEGS EVOK GR Q lg st) log r5 M5 rom (0x52154 : bv 64)%bv (sp - 128) HI t ctx tp key tsd spb ris qs (rs + 16 + rz) km inited cl
P5_1 ltac:(unfold ret_ok; bveq) P5_2 P5_4 P5_10 P5_11 P5_12 P5_13 ltac:(lia) Hs8 ltac:(lia) ltac:(lia) GEO W5 Wt5 PC5 L5 T5 PH5 RC5 OK Hin Emu).
{ intros E1 E2. destruct (Room E1 E2) as (R1 & R2). split; [exact R1|]. split; [exact R2|].
split; (eapply wr_sub; [exact Wsh5| |]); clear - Hc Hkm R1 Emu; lia. }
{ exact EV. }
intros r6 M6 R10 R2 R1 RK G56 RA RPH RCR ROK RCP RSH.
fold c in R10, RA, RCR, ROK, RCP, RSH. fold w in R10, RCP.
set (clp := art_ca_pre c cl) in *.
assert (R6_10 : getr r6 10 = Z_to_bv 64 ab) by (rewrite Eab; exact R10).
pose proof (art_class_size_facts c Hc) as (Hsz & Hsz16). set (sz := AsanTab.class_size c) in *.
pose proof RCP as (Hw0 & Hwsz & _).
pose proof ROK as OK'. unfold art_cls_ok in OK'. cbn [art_cls_pop cl_cache cl_free cl_au cl_mu cl_mfa] in OK'.
destruct OK' as (Hl16' & (Hau0' & Haumu') & _ & _ & _ & Hmu3' & _ & (_ & Hmfa1') & Hnf4' & _).
set (au' := cl_au clp) in *. set (mu' := cl_mu clp) in *.
destruct RCR as [CR6 RR6]. pose proof RR6 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Wu6).
cbn [art_cls_pop cl_mu] in Wu6. fold mu' in Wu6.
assert (A56 : art_agree (art_ca_W (sp - 128) t spb ris qs c km) M5 M6) by (apply art_ca_fp_agree; [exact Hc|exact RA]).
unfold art_ca_W in A56.
assert (G06 : mem_grows M0 M6) by (eapply mem_grows_trans; [exact G05|exact G56]).
assert (Hab16 : ab mod 16 = 0). { rewrite Eab, Espb. replace (65536 * qs + c * 2 ^ 32 + w * 16) with ((4096 * qs + c * 2 ^ 28 + w) * 16) by lia. apply Z_mod_mult. }
assert (Hrz16 : rz mod 16 = 0). { rewrite Erz16, Z.mul_comm. apply Z_mod_mult. }
assert (Hab8 : ab / 8 = 8192 * qs + c * 2 ^ 29 + 2 * w). { rewrite Eab, Espb. replace (65536 * qs + c * 2 ^ 32 + w * 16) with ((8192 * qs + c * 2 ^ 29 + 2 * w) * 8) by lia. apply Z.div_mul. lia. }
assert (Hub8 : (ab + rz) / 8 = 8192 * qs + c * 2 ^ 29 + 2 * w + 2 * qz). { rewrite Eab, Espb, Erz16. replace (65536 * qs + c * 2 ^ 32 + w * 16 + 16 * qz) with ((8192 * qs + c * 2 ^ 29 + 2 * w + 2 * qz) * 8) by lia. apply Z.div_mul. lia. }
assert (Hqr8 : rs / 8 = qr). { rewrite Ers, Z.mul_comm. apply Z.div_mul. lia. }
assert (SAB6 : cellA M6 (shb + 2 * w) 1 250).
{ assert (OLD : 16 * w < cl_mu cl -> cellA M0 (shb + 2 * w) 1 250 -> cellA M6 (shb + 2 * w) 1 250).
{ intros Hold C0. apply (art_cell_tr1 _ M5 M6 _ _ _ A56); [|apply (art_cell_tr1 _ M0 M5 _ _ _ A05); [|exact C0]].
- clear - Hold Emu HHI G1 G2 G4 G6 Espb Eris At_s Eshb Hc Hkm Hw0 Hmu3. zarith_f.
- clear - HHI G1 G2 G4 G6 Espb Eris Eshb Hc Hw0 Hold Hmu3. zarith_f. }
pose proof (art_ca_cptr_origin c cl Hc OK) as ORG. fold w in ORG. destruct ORG as [Hold|(Ecache & NP & Hauw)].
- apply OLD; [|apply PZ2; exact Hold].
pose proof (proj1 (Forall_forall _ _) Hfor w Hold) as (_ & Ho & _). fold sz in Ho. clear - Ho Haumu Hsz. lia.
- destruct (Z_lt_ge_dec (16 * w) (cl_mu cl)) as [Hlo|Hhi].
+ apply OLD; [exact Hlo|]. apply PZ1. clear - Hauw Hlo. lia.
+ pose proof (art_ca_pre_mu_pop c cl Ecache NP) as Emu'. fold clp in Emu'. fold mu' in Emu'.
pose proof (RSH Ecache NP (2 * w - 32768 * km) ltac:(clear - Hhi Emu Hwsz Haumu' Emu' Hsz; lia)) as C6.
replace (2147450880 + 8192 * qs + c * 2 ^ 29 + 32768 * km + (2 * w - 32768 * km)) with (shb + 2 * w) in C6 by (clear - Eshb; lia). exact C6. }
assert (Wc6 : wrA M6 ab (rs + rz)). { eapply wr_sub; [exact Wu6| |]; clear - Eab Hw0 Hwsz Haumu' Hfit; lia. }
destruct (art_cell_exists_b M6 (ab + rz - 15) 1 ltac:(lia) ltac:(right; clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia)
ltac:(eapply wr_sub; [exact Wc6| |]; clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia)) as (ob & Hob & Cob).
change (2 ^ (8 * Z.of_nat 1)) with 256 in Hob.
assert (R6_9 : getr r6 9 = Z_to_bv 64 n) by (rewrite RK by inl; exact P5_9).
assert (R6_19 : getr r6 19 = Z_to_bv 64 (rs + 16 + rz)) by (rewrite RK by inl; exact P5_19).
assert (R6_20 : getr r6 20 = Z_to_bv 64 rz) by (rewrite RK by inl; exact P5_20).
assert (R6_21 : getr r6 21 = Z_to_bv 64 n) by (rewrite RK by inl; exact P5_21).
assert (R6_23 : getr r6 23 = Z_to_bv 64 stk) by (rewrite RK by inl; exact P5_23).
assert (R6_25 : getr r6 25 = Z_to_bv 64 15) by (rewrite RK by inl; exact P5_25).
assert (R6_26 : getr r6 26 = Z_to_bv 64 t) by (rewrite RK by inl; exact P5_26).
assert (R6_27 : getr r6 27 = Z_to_bv 64 1) by (rewrite RK by inl; exact P5_27).
assert (R6_4 : getr r6 4 = Z_to_bv 64 tp) by (rewrite RK by inl; exact P5_4).
assert (R6_8 : getr r6 8 = Z_to_bv 64 1) by (rewrite RK by inl; exact P5_8).
assert (R6_3 : getr r6 3 = getr regs 3) by (rewrite RK by inl; exact P5_3).
assert (F16_6 : cellA M6 (sp - 128 + 16) 8 32) by (ztr_c ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris)).
assert (Ctctx6 : cellA M6 t 8 ctx) by (ztr_c ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris)).
assert (Ctid6 : cellA M6 (ctx + 8) 4 0) by (ztr_c ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris)).
assert (Ctrp6 : cellA M6 stk 8 trp) by (ztr_c ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris)).
assert (Cszt6 : cellA M6 (stk + 8) 8 szt) by (ztr_c ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris)).
pose proof (art_alloc_b_16_fn r6 M6 rom (sp - 128) ab n rs rz stk t ctx ob trp szt R2 R6_10 R6_9 R6_19 R6_20 R6_21 R6_23 R6_25 R6_26 R6_27
ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) Hab16 ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) Ers_max ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) Hrz16 Hprim
ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) G7 ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) G13 ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) Hob Htrp Hszt
ltac:(eapply wr_sub; [exact Wc6| |]; clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia)
Cob F16_6 Ctctx6 Ctid6 Ctrp6 Cszt6
ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zapart_f) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zapart_f) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zapart_f) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zapart_f)) as RUN7.
match type of RUN7 with msteps _ _ (mkst ?R _ ?MM _) => set (R7 := R) in RUN7; set (M7 := MM) in RUN7 end.
eapply ar_steps; [exact RUN7|].
assert (A67 : art_agree [(ab + rz - 16, 16)] M6 M7).
{ unfold M7, art_alloc_memB_16. clear - Eab Espb G4 G2 G6 Eris Hc Hw0 Hwsz Haumu' Hmu3' Hsz Hqz Erz16. eapply art_agree_sub; [zagree|]. zsub_c ltac:(clear). }
assert (G67 : mem_grows M6 M7) by (unfold M7, art_alloc_memB_16; zgrows).
assert (Hn32 : n / 2 ^ 32 = 0) by (apply Z.div_small; clear - Hn Hrs Hprim Hqz Erz16; lia).
pose proof (art_hdr_b1a_range ob Hob) as Hb1a. pose proof (art_hdr_b1_16_range ob Hob) as Hb1.
assert (B7 : cellA M7 (ab + rz - 15) 1 (art_hdr_b1_16 ob) /\ cellA M7 (ab + rz - 12) 4 n /\ cellA M7 (ab + rz - 14) 2 0).
{ unfold M7, art_alloc_memB_16. rewrite Hn32. clear - Hb1a Hb1 Eab Espb G4 G2 G6 Eris Hc Hw0 Hwsz Haumu' Hmu3' Hsz Hqz Erz16 Hn Hprim Hrs. repeat split; zcell. }
destruct B7 as (B7a & B7b & B7c).
assert (G07 : mem_grows M0 M7) by (eapply mem_grows_trans; [exact G06|exact G67]).
pose proof (art_agree_trans _ _ _ _ _ A05 (art_agree_trans _ _ _ _ _ A56 A67)) as A07.
assert (DO7 : forall z, dprivD l2 blk z -> art_out ([(sp - 144, 144)] ++ [(sp - 128 - 720, 720); (t + 208, 2592); (t + 2872, 16); (ris + 128 * c, 128); (spb + c * 2 ^ 32 + 262144 * km, 262144);
(spb + c * 2 ^ 32 + 3758096384, 536870912); (2147450880 + 8192 * qs + c * 2 ^ 29 + 32768 * km, 32768);
(2147450880 + 8192 * qs + c * 2 ^ 29 + 469762048, 67108864)] ++ [(ab + rz - 16, 16)]) z).
{ apply art_dpriv_out; clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zarith_f. }
assert (DI7 : DInvD l2 blk (S kb) M7). { apply (DInvD_frame l2 blk (S kb) M0 M7 DI). intros x Dx. apply A07. apply DO7. exact Dx. }
assert (DP7 : DPreD blk M7 trp szt).
{ apply (DPreD_frame blk M0 M7 trp szt DP). intros x Hx. apply A07. apply (art_gap_out _ trp (8 * szt)); [|exact Hx]. clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zarith_f. }
assert (DR7 : DRoD M7).
{ apply (DRoD_frame M0 M7 DR). intros x Hx. apply A07. apply (art_gap_out _ 0x10000 (0x20e908 - 0x10000)); [|clear - Hx; lia]. clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zarith_f. }
assert (W7 : wrA M7 (sp - 128 - 224) 224) by (eapply wr_grows; [exact G07|]; eapply wr_sub; [exact W|lia|lia]).
assert (ND7 : nodp (dprivD l2 blk) (sp - 128 - 224) 224). { intros i Hi D. unfold dprivD in D. clear - Hi D HHI G1 Dl2 Dblk. lia. }
pose proof (art_depot_spec_holds l2 blk) as DEPOT. unfold art_depot_spec in DEPOT.
destruct (DEPOT kb R7 M7 rom (0x52260 : bv 64)%bv (sp - 128) trp szt ltac:(unfold R7; gres; reflexivity) ltac:(unfold ret_ok; bveq) ltac:(unfold R7; gres; exact R2)
ltac:(unfold R7; gres; reflexivity) ltac:(unfold R7; gres; reflexivity) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) W7 ND7 DI7 DP7 DR7)
as (r8 & M8 & id & RUN8 & P8_10 & Hid & K8 & G78 & AGd & DI8).
clear DEPOT A07 DO7.
eapply ar_steps; [exact RUN8|].
assert (A78 : art_agree [(0x20e908, 0x65e928 - 0x20e908); (l2, 2 ^ 20); (blk, 2 ^ 23); (sp - 128 - 224, 224)] M7 M8).
{ intros x Hx. cbn [art_out fst snd] in Hx. apply AGd; [unfold dprivD; clear - Hx; lia | clear - Hx; lia]. }
pose proof (art_agree_trans _ _ _ _ _ A67 A78) as A68.
pose proof (art_agree_trans _ _ _ _ _ A56 A68) as A58.
pose proof (art_agree_trans _ _ _ _ _ A05 A58) as A08.
assert (G08 : mem_grows M0 M8) by (eapply mem_grows_trans; [exact G07|exact G78]).
assert (T_img : forall a (k : nat) v, 0x10000 <= a -> a + Z.of_nat k <= 0x20e908 -> cellA M0 a k v -> cellA M8 a k v).
{ intros a k v Ha Hk C. apply (art_cell_tr1 _ M0 M8 a k v A08); [|exact C]. revert Ha Hk. clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris. intros Ha Hk. zarith_f. }
assert (T_frm : forall a (k : nat) v, sp - 128 <= a -> a + Z.of_nat k <= sp -> cellA M5 a k v -> cellA M8 a k v).
{ intros a k v Ha Hk C. apply (art_cell_tr1 _ M5 M8 a k v A58); [|exact C]. revert Ha Hk. clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris. intros Ha Hk. zarith_f. }
assert (W8 : wrA M8 (sp - 1920) 1920) by (eapply wr_grows; [exact G08|exact W]).
assert (Wc8 : wrA M8 ab (rs + rz)) by (eapply wr_grows; [exact G78|]; eapply wr_grows; [exact G67|exact Wc6]).
assert (Wsh8 : wrA M8 (0x7fff8000 + ab / 8) 8192). { eapply wr_grows; [exact G08|]. eapply wr_sub; [exact Wsh| |]; rewrite Hab8; clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia. }
assert (Wt8 : wrA M8 t 4096) by (eapply wr_grows; [exact G08|exact Wt]).
assert (L8 : art_layout M8).
{ eapply art_layout_fp; [exact A08| |exact L]. intros z Hz. apply (art_gap_out _ 0x10000 (0x20e908 - 0x10000)); [|clear - Hz; lia]. clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zarith_f. }
assert (T8 : art_tsd M8 tp key tsd ctx t). { apply (art_tsd_tr _ M0 M8 tp key tsd ctx t A08); [| | | |exact TSD]; clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zarith_f. }
assert (SAB8 : cellA M8 (0x7fff8000 + ab / 8) 1 250).
{ rewrite Hab8. replace (0x7fff8000 + (8192 * qs + c * 2 ^ 29 + 2 * w)) with (shb + 2 * w) by (clear - Eshb; lia).
apply (art_cell_tr1 _ M6 M8 _ _ _ A68); [|exact SAB6]. clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zarith_f. }
assert (Clsan8 : cellA M8 (tp + loff) 4 0). { apply (art_cell_tr1 _ M0 M8 _ _ _ A08); [|exact Clsan]. clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zarith_f. }
assert (RO3 : cellA M0 0x10358 8 0xcc6e96b9cc6e96b9) by (unfold art_alloc_rodata in RO; tauto).
destruct (art_tcell_exists M8 t 2800 At_i G7 ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) ltac:(lia) ltac:(lia) Wt8) as (mc & Hmc & Cmc).
destruct (art_tcell_exists M8 t 2808 At_i G7 ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) ltac:(lia) ltac:(lia) Wt8) as (mb & Hmb & Cmb).
destruct (art_tcell_exists M8 t 2816 At_i G7 ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) ltac:(lia) ltac:(lia) Wt8) as (mr & Hmr & Cmr).
destruct (art_tcell_exists M8 t (2912 + 8 * c) At_i G7 ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) ltac:(clear - Hc; lia) ltac:(clear - Hc; lia) Wt8) as (mbs & Hmbs & Cmbs).
replace (t + 2808) with (t + 2800 + 8) in Cmb by (clear; lia). replace (t + 2816) with (t + 2800 + 16) in Cmr by (clear; lia).
replace (t + (2912 + 8 * c)) with (t + 2800 + 112 + 8 * c) in Cmbs by (clear; lia).
assert (B8a : cellA M8 (ab + rz - 15) 1 (art_hdr_b1_16 ob)). { apply (art_cell_tr1 _ M7 M8 _ _ _ A78); [|exact B7a]. clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zarith_f. }
assert (B8b : cellA M8 (ab + rz - 12) 4 n). { apply (art_cell_tr1 _ M7 M8 _ _ _ A78); [|exact B7b]. clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zarith_f. }
assert (B8c : cellA M8 (ab + rz - 14) 2 0). { apply (art_cell_tr1 _ M7 M8 _ _ _ A78); [|exact B7c]. clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zarith_f. }
assert (R8_2 : getr r8 2 = Z_to_bv 64 (sp - 128)) by (rewrite K8 by dk8; unfold R7; gres; exact R2).
assert (R8_3 : getr r8 3 = getr regs 3) by (rewrite K8 by dk8; unfold R7; gres; exact R6_3).
assert (R8_4 : getr r8 4 = Z_to_bv 64 tp) by (rewrite K8 by dk8; unfold R7; gres; exact R6_4).
assert (R8_8 : getr r8 8 = Z_to_bv 64 1) by (rewrite K8 by dk8; unfold R7; gres; exact R6_8).
assert (R8_9 : getr r8 9 = Z_to_bv 64 n) by (rewrite K8 by dk8; unfold R7; gres; exact R6_9).
assert (R8_18 : getr r8 18 = Z_to_bv 64 ab) by (rewrite K8 by dk8; unfold R7; gres; reflexivity).
assert (R8_19 : getr r8 19 = Z_to_bv 64 (rs + 16 + rz)) by (rewrite K8 by dk8; unfold R7; gres; exact R6_19).
assert (R8_20 : getr r8 20 = Z_to_bv 64 (ab + rz)) by (rewrite K8 by dk8; unfold R7; gres; reflexivity).
assert (R8_21 : getr r8 21 = Z_to_bv 64 (ab + rz - 16)) by (rewrite K8 by dk8; unfold R7; gres; reflexivity).
assert (R8_24 : getr r8 24 = Z_to_bv 64 0) by (rewrite K8 by dk8; unfold R7; gres; reflexivity).
destruct (art_allocate_post_16 r8 M8 rom raw sp n qn m8 rs qr rz qz c (4096 * qs) w ab t tp loff key tsd ctx id 250 (art_hdr_b1_16 ob) mc mb mr mbs
(U raw) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20)) (U (getr regs 21))
(U (getr regs 22)) (U (getr regs 23)) (U (getr regs 24)) (U (getr regs 25)) (U (getr regs 26)) (U (getr regs 27))
eq_refl Hret R8_2 R8_4 R8_8 R8_9 P8_10 R8_18 R8_19 R8_20 R8_21 R8_24
Hn En Hm8 Ers Hrs Erz16 ltac:(clear - Hqz Erz16; lia) Hprim eq_refl ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia)
ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) Hsp'
G7 ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) G9 ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zapart_f) ltac:(clear - At_s; unfold apart in *; lia)
ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zapart_f) G15 G18 ltac:(clear - Ac_s; unfold apart in *; lia)
Hloff G19 Hloff' Hloff'' G21 G22
ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zapart_f) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zapart_f) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zapart_f)
Hid ltac:(lia) Hb1 Hmc Hmb Hmr Hmbs
(u64_range raw) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _)
W8 Wc8 Wsh8 Wt8 L8 T8 SAB8
ltac:(apply T_img; [clear; lia|clear; cbn; lia|exact Cpp]) ltac:(apply T_img; [clear; lia|clear; cbn; lia|exact Cmfs]) ltac:(apply T_img; [clear; lia|clear; cbn; lia|exact Cfb])
ltac:(apply T_img; [clear; lia|clear; cbn; lia|exact Cg]) Clsan8 ltac:(apply T_img; [clear; lia|clear; cbn; lia|exact Chook]) ltac:(apply T_img; [clear; lia|clear; cbn; lia|exact RO3])
Cmc Cmb Cmr Cmbs B8a B8b B8c
ltac:(apply T_frm; [clear; lia|clear; cbn; lia|exact F8])
ltac:(apply T_frm; [clear; lia|clear; cbn; lia|exact F120]) ltac:(apply T_frm; [clear; lia|clear; cbn; lia|exact F112]) ltac:(apply T_frm; [clear; lia|clear; cbn; lia|exact F104])
ltac:(apply T_frm; [clear; lia|clear; cbn; lia|exact F96]) ltac:(apply T_frm; [clear; lia|clear; cbn; lia|exact F88]) ltac:(apply T_frm; [clear; lia|clear; cbn; lia|exact F80])
ltac:(apply T_frm; [clear; lia|clear; cbn; lia|exact F72]) ltac:(apply T_frm; [clear; lia|clear; cbn; lia|exact F64]) ltac:(apply T_frm; [clear; lia|clear; cbn; lia|exact F56])
ltac:(apply T_frm; [clear; lia|clear; cbn; lia|exact F48]) ltac:(apply T_frm; [clear; lia|clear; cbn; lia|exact F40]) ltac:(apply T_frm; [clear; lia|clear; cbn; lia|exact F32])
ltac:(apply T_frm; [clear; lia|clear; cbn; lia|exact F24]))
as (rF & MF & RUNF & PF10 & PF2 & PF1 & PF8 & PF9 & PF18 & PF19 & PF20 & PF21 & PF22 & PF23 & PF24 & PF25 & PF26 & PF27 & GF & AGF & CL1 & CL2 & CL3 & CL4 & SHZ & SHP & PF3 & PF4 & LCH).
eapply ar_steps; [exact RUNF|]. apply ar_done.
assert (A8F : art_agree [(sp - 1920, 1920); (ab, rz + n); (2147450880 + (ab + rz) / 8, rs / 8); (t + 2800, 24); (t + 2912 + 8 * c, 8)] M8 MF).
{ intros x Hx. cbn [art_out fst snd] in Hx. apply AGF. unfold art_post_writtenG16. clear - Hx. lia. }
rewrite Hub8, Hqr8 in A8F.
pose proof (art_agree_trans _ _ _ _ _ A68 A8F) as A6F.
assert (G6F : mem_grows M6 MF) by (eapply mem_grows_trans; [exact G67|]; eapply mem_grows_trans; [exact G78|exact GF]).
pose proof (art_hdr_b1_type_16 ob Hob) as (Hty & Hb1').
apply (K rF MF (Z.land (art_hdr_b1_16 ob) 243)).
- exact PF10.
- exact PF2.
- exact PF1.
- intros r Hr. cbn [In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]];
[ rewrite PF3; exact R8_3 | rewrite PF4, R8_4; symmetry; exact H4
| rewrite PF8 | rewrite PF9 | rewrite PF18 | rewrite PF19 | rewrite PF20 | rewrite PF21 | rewrite PF22 | rewrite PF23 | rewrite PF24 | rewrite PF25 | rewrite PF26 | rewrite PF27 ];
apply Z_to_bv_bv_unsigned.
- eapply mem_grows_trans; [exact G08|exact GF].
- intros x N.
assert (N1 : ~ art_post_writtenG16 sp t c ab rz n rs (U x)).
{ intros F; apply N; unfold art_alloc3_fp16; unfold art_post_writtenG16 in F.
destruct F as [F|[F|[F|[F|F]]]]; [left | do 2 right; left | do 3 right; left | do 4 right; left | do 5 right; left]; exact F. }
rewrite (AGF x N1).
rewrite (AGd x) by (intros F; apply N; unfold art_alloc3_fp16; first [ do 6 right; exact F | left; clear - F; lia ]).
rewrite (A67 x) by (cbn [art_out fst snd]; split; [|exact I]; intros F; apply N; unfold art_alloc3_fp16; right; right; left; clear - F Hqz Erz16 Hn; lia).
rewrite (RA x) by (intros F; apply N; unfold art_alloc3_fp16; right; left; exact F).
apply AG05. intros F. apply N. unfold art_alloc3_fp16. left. clear - F. lia.
- apply (DInvD_frame l2 blk kb M8 MF DI8). intros x Dx. apply A8F. revert Dx. apply art_dpriv_out; clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zarith_f.
- apply (art_pc_hdr_tr _ (t + 208) true M6 MF ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) A6F); [|exact RPH]. intros c' Hc'. revert Hc'. clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris. intros Hc'. zarith_f.
- match type of A6F with art_agree ?WW _ _ => apply (art_cls_rep_tr WW (t + 208) spb ris c (art_cls_pop clp) M6 MF) end; first [ exact (conj CR6 RR6) | exact G6F | exact A6F | exact Hl16' | idtac ];
cbn [art_cls_pop cl_free]; first [ clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia | clear - Hnf4' Hmfa1'; lia | idtac ].
all: revert Hnf4' Hmfa1'; clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; intros Hnf4' Hmfa1'; zarith_f.
- exact ROK.
- exact RCP.
- exact Hb1'.
- exact Hty.
- exact CL1.
- exact CL3.
- exact CL4.
- exact CL2.
- apply (art_cell_tr1 _ M6 MF _ _ _ A6F); [|exact SAB6]. clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zarith_f.
- intros j Hj. replace (shb + 2 * w + 2 * qz + j) with (2147450880 + ab / 8 + 2 * qz + j) by (rewrite Hab8; clear - Eshb; lia). apply SHZ. exact Hj.
- intros NE. replace (shb + 2 * w + 2 * qz + qn) with (2147450880 + ab / 8 + 2 * qz + qn) by (rewrite Hab8; clear - Eshb; lia). apply SHP. exact NE.
- intros E1 E2 j Hj Hex. pose proof (RSH E1 E2 j Hj) as C6.
replace (2147450880 + 8192 * qs + c * 2 ^ 29 + 32768 * km + j) with (shb + 32768 * km + j) in C6 by (clear - Eshb; lia).
apply (art_cell_tr1 _ M6 MF _ _ _ A6F); [|exact C6]. revert Hj Hex. clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris. intros Hj Hex. zarith_f.
- exact LCH.
Qed.
End SE.
End Spec.
