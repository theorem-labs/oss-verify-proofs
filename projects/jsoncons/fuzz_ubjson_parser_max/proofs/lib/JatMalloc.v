(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtTac JatLeaf JatPoison JatAllocG JatUnwind.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatMalloc () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatAllocG."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatLeaf."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1cons"; "1nil"; "1option"; "2I"; "2and"; "2eq"; "2ex"; "2not"; "2or"; "3Z"; "4bvmap"; "0M"; "0M1"; "5Wn"; "5apart"; "5cell"]; ["5wr"; "6msteps"; "7ret_ok"; "8hid"; "9art_tsd"; ":getr"; ":mkst"; ":regupd"; ";mem_grows"; "<loaded_segments"; "0S"; "=In"; ">add"; ">le"; ">lt"; ">pow"]; [">sub"; "0bot"; "0ctx"; "0f22"; "0f23"; "0f24"; "0fx"; "0g16"; "0g24"; "0g32"; "0g40"; "0g48"; "0g56"; "0key"; "0n"; "0r"]; ["0raw0"; "0regs"; "0regs1"; "0rom"; "?BV"; "?Z_to_bv"; "?bv"; "?bv_unsigned"; "0t"; "0top"; "0tp"; "0tsd"; "0ub"; "0x"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Section FPX. Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_art_icu1 := (ltac2:(TCodec.tc2 tcn__JatMalloc "^6&:y5'QFyR0%211%5241'2y8%611%311p061'9'5&Er=(QD+1(3%33A21%6251r:%93A21r>+2%93G17%<231&QE%12H7%@3H31r?+4%@3N1>%C231r9%82O1%G3O31r@+:%G3Q51E%J231r;%?2Q61%N3Q631&M&L+`PQoooPP0+XP0%3221%521Q2&O+Q?%22L1%92N1'4z%<21Q1&N+R0%92Q31%32Q51%7251+TP0%C21Q:%C2G2%821=&C'8r<%H217+RPP0%K221+VbTP0%M215%7231%911&>&Q0rC%221A%44R1B1Q1rD%521D%74QEE1Q4%Q72Q?F%Q921?%Q:2>QA%D221%F11rA%>4QEL1L+RPX0rE%QA221rF+8%QC221%QE21I%QF2L6+QP0%QG261%QI21M%QJ2Q?H%Q>2IF%QB221+QO%QH2RB1%QB2?1&@&IrQ0rM%Q321QB%54431QCrQ1rH%84721QF&DrQ2rLrKrJrI%665<4321&?rQ3+QW^^Hu1%45C321S?rQ4+QW^_Lu4+N%95H4321rQ5+QVYa8u8+QibQ8%>5M4321rQ6+Q2%S0241%B5Q131?SMrQ7rN+SS0%S5221%G5Q641DRLrQ8rO+Q8%S:221%L5Q;41IS1rQ9%S=2Q<QK%O5Q>21C6rQ:+@%SA2Q<1%Q35QB31G:'6'A&FvQ6rQ>+_TTL%TF3U21TD/01U2rQ=rQ<%8576321r2+cWoH%TM3U91TK/01U9r1%>5=5217%@3R471%U427TO+`Ub0%U43U@1U2/01U@%U93UA41%U92<TN+RU0%S<2M1%TO2UF1%U>3UF41%U>2ATE+RR@%SA2Q21%U42UK1%UC3UK41+;%UB3V01U@%UE2H1+_T[4%U:2V11%UI3V131+<%UH3V61UF%UK2N1%U?2V6Q>%UN3V621+=%UM3V;1UK%V02Q31%UD2V;RB%V33V;21+>%V23V@1V0%V52Q81%UI2V@RN%V83V@21+?%V73VE1V5%V:2Q=1%UN2VERE%V=3VE21+H%V<3VJ1V:%V?2QB1+QoO%UB2RN1%V52VL1%VD3VL41%VD2QGV2%V82VOR?%VG3VO21%W21W3&K(0+3%VI3W71VG+I%VK3W91VI+J%VM3W;1VK+K%VO3W=1VM(1%11<%;3=31%<3>61%=3?91%>3@<1%@3AR71r4%W:21R=rQ@%W<21R?%W>3WF31p061pS0H1&H%12RGR@&7rQ;+RW0%UF221&QG%12X1RF%VJ231%V>226%VB221%911%62X6RO%VN2T0SJ%WO3X021%=11r3%H11%G12%X43X721p051p0:1pSLX?1%V82SIUF%B2XBE%TK5U:S82T?1%V;2SLSK%X93XGUJX7%X<2SF1%G2XG1%U05U?S=4TD1%V@2T1R2+9%X?3XM1X=%XB2SL1%M2XM1%U65UESC5TJ1+Q0%VG2T81+B%XF3Y41XD%XI2T31%Q42Y41%U=5ULSJ5U11%VM2T>TD+C%XL3Y:1XJ%XO2T91%Q:2Y:1%UC5V2T05U71+Q@%W42TE1+D%Y33YA1Y1%Y62T@1%QA2YA1%UJ5V9T75U>1+QH%W;2TL1+E%Y:3YH1Y8%Y=2TG1%QH2YH1%V15V@T>5UE1+RRH%WB2U31+_T^0%V55VDTB2UI1+RS0%WF2U71%V85VGTE1ULU8+RS8%WI2U:1%V;5VJTH1UOU>+RS@%WL2U=1%YJ3Z6T6YH/01Z6%R82Z81%VA5W0TN4V51+RSH%X22UC1%VD5W3U11V8YO+RT0%X52UF1%VG5W6U41V;TE+RT8%X82UI1+RA%X:2UK1%VL5W;U93V@1+RT@%X=2UN1+F%Z<3ZJ1Z:%Z?2UI1%RJ2ZJ1%W35WBU@5VG1+RTH%XD2V51+G%ZC3[11ZA%ZF2V01%S12[11%W:5WIUG5VN1%ZI2V3T;%S42[41%W=5WLUJU@W11+RR0%XN2V?1%W@5WOUMU>W41+RR8%Y12VB1%WC5X2V01W<YH+RR4%Y42VE1%WF5X5V31W?YK%Y62VGYE%X84X7V51YF%YO231%Z0271%Z12;1%Z22?1%Z32C1%Z42K1%Z52Q31%Z62Q91%Z72Q=1%Z82QA1%Z92QH1%Z:2QL1%Z;2R01%Z<2R51%Z=2R=1%Z>2RE1%Z?2RL1%Z@2S41%ZA2S;1%ZB2SA1%ZC2SE1%ZD2T;1%ZE2T>1%ZF2U81%ZG2U<1%ZH2UD1%ZI2UJ1%ZJ2V01%ZK2V61%ZL2V<1%ZM2VC1%ZN2VI1%ZO2VO1%[02W51qJ\<1%WH2\=1qS6\C1%WJ2\D1p0WL1p0X11p0X51p0X;1p0XA1p0XF1p0XL1p0Y21p0Y81p0Y@1p0YD1p0YK1p0YO1p0Z31p0Z71p0Z91p0Z>1p0ZB1p0ZE1p0ZK1p0ZO1p0[51p0[@1p0[C1p0[F1p0[O1p0\41p0\;1p0\C1p0\K1p0]31pR4]>1pSD]?1pSB]@1pR6]A1pSH]B1pRL]C1pSF]D1pRN]E1pQF]F1pS2]N1pS8]I1pH]J1pS4^01")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_icu1) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_icu1) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_icu1) 2%nat 0%nat).
Variable raw0 : ltac:(sec_ty2 constr:(SEC_T_art_icu1) 3%nat 0%nat).
Variable S : ltac:(sec_ty2 constr:(SEC_T_art_icu1) 4%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_icu1) 5%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_art_icu1) 6%nat 0%nat).
Variable key : ltac:(sec_ty2 constr:(SEC_T_art_icu1) 7%nat 0%nat).
Variable tsd : ltac:(sec_ty2 constr:(SEC_T_art_icu1) 8%nat 0%nat).
Variable ctx : ltac:(sec_ty2 constr:(SEC_T_art_icu1) 9%nat 0%nat).
Variable t : ltac:(sec_ty2 constr:(SEC_T_art_icu1) 10%nat 0%nat).
Variable top : ltac:(sec_ty2 constr:(SEC_T_art_icu1) 11%nat 0%nat).
Variable bot : ltac:(sec_ty2 constr:(SEC_T_art_icu1) 12%nat 0%nat).
Lemma art_icu1 : ltac:(sec_stmt2 constr:(SEC_T_art_icu1) 13%nat 0%nat).
Proof using Type regs M rom raw0 S n tp key tsd ctx t top bot.
intros H1 H2 H4 H10 HS HS' Hn Ht Ht' Timg Atsp Actx Cimg Atctx Htp0 Htp1 Htsd0 Htsd Hbt Htop
W Wt TSD Ci Cctx Cg38 Cfast Cunw C40 C8 C16.
pose proof TSD as (Ttsd1 & Ttsd2 & Ttsd3 & Ttsd4 & Ttsd5 & TR).
eexists _, _. split.
- zstep (ltac:(oF' 0x7909c%Z)) (ltac:(oD' 0x7909c%Z)).
zsd (ltac:(oF' 0x790a0%Z)) (ltac:(oD' 0x790a0%Z)) (S - 8) (U raw0) ltac:(rewok W). zsd (ltac:(oF' 0x790a4%Z)) (ltac:(oD' 0x790a4%Z)) (S - 16) (U (getr regs 8)) ltac:(rewok W).
zsd (ltac:(oF' 0x790a8%Z)) (ltac:(oD' 0x790a8%Z)) (S - 24) (U (getr regs 9)) ltac:(rewok W). zsd (ltac:(oF' 0x790ac%Z)) (ltac:(oD' 0x790ac%Z)) (S - 32) (U (getr regs 18)) ltac:(rewok W).
zsd (ltac:(oF' 0x790b0%Z)) (ltac:(oD' 0x790b0%Z)) (S - 40) (U (getr regs 19)) ltac:(rewok W). zsd (ltac:(oF' 0x790b4%Z)) (ltac:(oD' 0x790b4%Z)) (S - 48) (U (getr regs 20)) ltac:(rewok W).
zsd (ltac:(oF' 0x790b8%Z)) (ltac:(oD' 0x790b8%Z)) (S - 56) (U (getr regs 21)) ltac:(rewok W).
zstep (ltac:(oF' 0x790bc%Z)) (ltac:(oD' 0x790bc%Z)). zstep (ltac:(oF' 0x790c0%Z)) (ltac:(oD' 0x790c0%Z)). zstep (ltac:(oF' 0x790c4%Z)) (ltac:(oD' 0x790c4%Z)). zstep (ltac:(oF' 0x790c8%Z)) (ltac:(oD' 0x790c8%Z)).
stepn (ltac:(oF' 0x790cc%Z)) (ltac:(oD' 0x790cc%Z)).
zcall (art_try_init_fn _ _ _ _ (S - 2128)).
zbft (ltac:(oF' 0x790d0%Z)) (ltac:(oD' 0x790d0%Z)).
zstep (ltac:(oF' 0x790d4%Z)) (ltac:(oD' 0x790d4%Z)). zstep (ltac:(oF' 0x790d8%Z)) (ltac:(oD' 0x790d8%Z)). zstep (ltac:(oF' 0x790dc%Z)) (ltac:(oD' 0x790dc%Z)). zstep (ltac:(oF' 0x790e0%Z)) (ltac:(oD' 0x790e0%Z)). zstep (ltac:(oF' 0x790e4%Z)) (ltac:(oD' 0x790e4%Z)).
zsd (ltac:(oF' 0x790e8%Z)) (ltac:(oD' 0x790e8%Z)) (S - 72) 0 ltac:(rewok W).
zsd (ltac:(oF' 0x790ec%Z)) (ltac:(oD' 0x790ec%Z)) (S - 2128) (S - 2112) ltac:(rewok W).
zsd (ltac:(oF' 0x790f0%Z)) (ltac:(oD' 0x790f0%Z)) (S - 2120) 0 ltac:(rewok W). rewrite (Wn8_zero_split _ (S - 2120)) by lia. replace (S - 2120 + 4) with (S - 2116) by lia.
stepn (ltac:(oF' 0x790f4%Z)) (ltac:(oD' 0x790f4%Z)).
zcall (art_malloc_ctx_fn _ _ _ _).
zstep (ltac:(oF' 0x790f8%Z)) (ltac:(oD' 0x790f8%Z)).
zbtk (ltac:(oF' 0x790fc%Z)) (ltac:(oD' 0x790fc%Z)).
stepn (ltac:(oF' 0x79160%Z)) (ltac:(oD' 0x79160%Z)).
zcall (art_get_pc_fn _ _ _ _).
zstep (ltac:(oF' 0x79164%Z)) (ltac:(oD' 0x79164%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cg38' : cellA X 0x132628 8 0x1cc828) by zcell; assert (Cfast' : cellA X (0x1cc828 + 34) 1 1) by zcell end.
zld (ltac:(oF' 0x79168%Z)) (ltac:(oD' 0x79168%Z)) 0x132628 Cg38'. zlbu (ltac:(oF' 0x7916c%Z)) (ltac:(oD' 0x7916c%Z)) (0x1cc828 + 34) Cfast'.
zstep (ltac:(oF' 0x79170%Z)) (ltac:(oD' 0x79170%Z)).
stepn (ltac:(oF' 0x79174%Z)) (ltac:(oD' 0x79174%Z)).
zcall (art_malloc_ctx_fn _ _ _ _).
zstep (ltac:(oF' 0x79178%Z)) (ltac:(oD' 0x79178%Z)). zstep (ltac:(oF' 0x7917c%Z)) (ltac:(oD' 0x7917c%Z)). zstep (ltac:(oF' 0x79180%Z)) (ltac:(oD' 0x79180%Z)).
stepn (ltac:(oF' 0x79184%Z)) (ltac:(oD' 0x79184%Z)). rwH. rewrite art_zb_and by lia. rewrite art_land_full_l by lia.
zstep (ltac:(oF' 0x79188%Z)) (ltac:(oD' 0x79188%Z)).
zsd (ltac:(oF' 0x7918c%Z)) (ltac:(oD' 0x7918c%Z)) (S - 72) S ltac:(rewok W).
zbtk (ltac:(oF' 0x79190%Z)) (ltac:(oD' 0x79190%Z)).
zstep (ltac:(oF' 0x791a4%Z)) (ltac:(oD' 0x791a4%Z)). zstep (ltac:(oF' 0x791a8%Z)) (ltac:(oD' 0x791a8%Z)). zstep (ltac:(oF' 0x791ac%Z)) (ltac:(oD' 0x791ac%Z)). zstep (ltac:(oF' 0x791b0%Z)) (ltac:(oD' 0x791b0%Z)). zstep (ltac:(oF' 0x791b4%Z)) (ltac:(oD' 0x791b4%Z)). zstep (ltac:(oF' 0x791b8%Z)) (ltac:(oD' 0x791b8%Z)).
stepn (ltac:(oF' 0x791bc%Z)) (ltac:(oD' 0x791bc%Z)).
zstep (ltac:(oF' 0x81524%Z)) (ltac:(oD' 0x81524%Z)).
zsd (ltac:(oF' 0x81528%Z)) (ltac:(oD' 0x81528%Z)) (S - 2136) 0x791c0 ltac:(rewok W). zsd (ltac:(oF' 0x8152c%Z)) (ltac:(oD' 0x8152c%Z)) (S - 2144) S ltac:(rewok W). zsd (ltac:(oF' 0x81530%Z)) (ltac:(oD' 0x81530%Z)) (S - 2152) n ltac:(rewok W).
zsd (ltac:(oF' 0x81534%Z)) (ltac:(oD' 0x81534%Z)) (S - 2160) (U (0x79164 : bv 64)%bv) ltac:(rewok W). zsd (ltac:(oF' 0x81538%Z)) (ltac:(oD' 0x81538%Z)) (S - 2168) 1 ltac:(rewok W). zsd (ltac:(oF' 0x8153c%Z)) (ltac:(oD' 0x8153c%Z)) (S - 2176) (S - 2128) ltac:(rewok W).
zsd (ltac:(oF' 0x81540%Z)) (ltac:(oD' 0x81540%Z)) (S - 2184) (S - 81) ltac:(rewok W). zsd (ltac:(oF' 0x81544%Z)) (ltac:(oD' 0x81544%Z)) (S - 2192) (U (getr regs 22)) ltac:(rewok W).
zsd (ltac:(oF' 0x81548%Z)) (ltac:(oD' 0x81548%Z)) (S - 2200) (U (getr regs 23)) ltac:(rewok W). zsd (ltac:(oF' 0x8154c%Z)) (ltac:(oD' 0x8154c%Z)) (S - 2208) (U (getr regs 24)) ltac:(rewok W).
zstep (ltac:(oF' 0x81550%Z)) (ltac:(oD' 0x81550%Z)). zstep (ltac:(oF' 0x81554%Z)) (ltac:(oD' 0x81554%Z)). zstep (ltac:(oF' 0x81558%Z)) (ltac:(oD' 0x81558%Z)). zstep (ltac:(oF' 0x8155c%Z)) (ltac:(oD' 0x8155c%Z)). zstep (ltac:(oF' 0x81560%Z)) (ltac:(oD' 0x81560%Z)). zstep (ltac:(oF' 0x81564%Z)) (ltac:(oD' 0x81564%Z)).
zsw (ltac:(oF' 0x81568%Z)) (ltac:(oD' 0x81568%Z)) (S - 2120) 0 ltac:(rewok W).
stepn (ltac:(oF' 0x8156c%Z)) (ltac:(oD' 0x8156c%Z)).
zcall (art_asan_inited_fn _ _ _ _).
zbft (ltac:(oF' 0x81570%Z)) (ltac:(oD' 0x81570%Z)).
stepn (ltac:(oF' 0x81574%Z)) (ltac:(oD' 0x81574%Z)).
zcall (art_cur_thread_fn _ _ _ _ (S - 2208) tp key tsd ctx t).
{ unfold art_tsd. repeat split; try lia; zcell. }
zbft (ltac:(oF' 0x81578%Z)) (ltac:(oD' 0x81578%Z)).
zstep (ltac:(oF' 0x8157c%Z)) (ltac:(oD' 0x8157c%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cunw' : cellA X (t + 2047 + 1121) 1 0) by (replace (t + 2047 + 1121) with (t + 3168) by lia; zcell) end.
zlbu (ltac:(oF' 0x81580%Z)) (ltac:(oD' 0x81580%Z)) (t + 2047 + 1121) Cunw'.
zstep (ltac:(oF' 0x81584%Z)) (ltac:(oD' 0x81584%Z)).
zsb (ltac:(oF' 0x81588%Z)) (ltac:(oD' 0x81588%Z)) (t + 2047 + 1121) 1 ltac:(rewok Wt).
zbft (ltac:(oF' 0x8158c%Z)) (ltac:(oD' 0x8158c%Z)).
zstep (ltac:(oF' 0x81590%Z)) (ltac:(oD' 0x81590%Z)).
stepn (ltac:(oF' 0x81594%Z)) (ltac:(oD' 0x81594%Z)).
zcall (art_stack_top_fn _ _ _ _ t top bot).
zstep (ltac:(oF' 0x81598%Z)) (ltac:(oD' 0x81598%Z)). zstep (ltac:(oF' 0x8159c%Z)) (ltac:(oD' 0x8159c%Z)).
stepn (ltac:(oF' 0x815a0%Z)) (ltac:(oD' 0x815a0%Z)).
zcall (art_stack_bottom_fn _ _ _ _ t top bot).
zstep (ltac:(oF' 0x815a4%Z)) (ltac:(oD' 0x815a4%Z)).
zbft (ltac:(oF' 0x815a8%Z)) (ltac:(oD' 0x815a8%Z)).
zstep (ltac:(oF' 0x815ac%Z)) (ltac:(oD' 0x815ac%Z)). zstep (ltac:(oF' 0x815b0%Z)) (ltac:(oD' 0x815b0%Z)). zstep (ltac:(oF' 0x815b4%Z)) (ltac:(oD' 0x815b4%Z)). zstep (ltac:(oF' 0x815b8%Z)) (ltac:(oD' 0x815b8%Z)). zstep (ltac:(oF' 0x815bc%Z)) (ltac:(oD' 0x815bc%Z)). zstep (ltac:(oF' 0x815c0%Z)) (ltac:(oD' 0x815c0%Z)). zstep (ltac:(oF' 0x815c4%Z)) (ltac:(oD' 0x815c4%Z)).
stepn (ltac:(oF' 0x815c8%Z)) (ltac:(oD' 0x815c8%Z)).
stepn (ltac:(oF' 0x8163c%Z)) (ltac:(oD' 0x8163c%Z)).
zcall (art_unwind_fn _ _ _ _ (S - 2208) (S - 2128) 0x79164 S top bot).
apply mst_refl.
- zsplit.
all: lazymatch goal with
| |- getr _ _ = _ => gres; rwH; first [reflexivity | f_equal; lia | bveq]
| |- forall r : reg, In r _ -> _ => intros r Hr; cbn [In] in Hr; destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; gres; reflexivity
| |- mem_grows _ _ => repeat (eapply mem_grows_trans; [|apply Wn_grows]); apply mem_grows_refl
| |- forall x : word, _ => intros x N1 N2; zagree
| |- wr _ _ _ _ => zwr
| |- cell _ _ _ _ _ => zcell
end.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_icu2_fn := (ltac2:(TCodec.tc2 tcn__JatMalloc "WJ&:y5'QFyR0%211%5241'2y8%611%311p061'9'5&Er9(QD+2(3%33A21%6251&QE&Q0r6+RU0%3221%52F1%>3F71r:+H%>3L1<%A231&Lr5+QoO%3221%?2Q01%H3Q061&M+XP0r8%3221&O+Q?%22K1%72N1'4z%:21Q1&N+R0%92Q21%32Q51%7251+TP0%A21Q8%H2L2%8216&>r;r=%Q7217%44381G%I2@4%?25=%C221&@&IrCrA%Q@21@%54431ArDr@%84721D&?rE+RRH%QH2:1u8+_T^0%65>5321rF+RS0%QN2<1%:5B316=rG+RS8%R22<1%>5F31:ArH+RS@%R62:1&QG+_T[4%R?3RK1R=/01RK%42RM1%G5O86C1rI+RSH%R?2?1+1%L5Q442H1rJ+RT0%RD2@1+RR@%RF2B1%Q25Q:53N1rK+RT8%RJ2=1+RA%RL2?1%Q85Q@53Q41rL+RT@%S02>1%Q<5QD31Q8Q1rM+RTH%S42<1%Q@5QH31Q<Q5rN%S729S5%QC5QK21Q?Q8'A&FvQ6rQ0+`Ub0%SD3T01SB/01T0rO%756521;&G%SI3T7Q3SG+ZVmD%SK3T71SI/01T7%53;41%SH2FQK%SJ2T;1%833SM1+8%T23T@1T0%SN2T?K%<3421+9%T63TD1T4%T22TCQ3%@3421+:%T:3TH1T8+QVmdH%T72TH1%E3531+;%T?3TM1T=%H3319+<%TB3U01T@%T>2TOB%L3421+=%TF3U41TD%TA2Q?QL%TC2U41%Q13531+>%TK3U91TI%TG2U8R6%Q53421+?%TO3U=1TM%Q83314+B%U23U@1U0%TN2U?RB%Q<3421+C%U63UD1U4%Q?331;+D%U93UG1U7%QB331B+E%U<3UJ1U:%U72R5R<%U92UJ1%QG3531+F%UA3UO1U?%U=2UNRJ%QK3421+G%UE3V31UC%UA2V2S3%QO3421%UC2V4S>%R132U;1+ZVo4%UK3V71UI/01V7&=u1+SS0%U@2S21%443R;1U2%UL2RJT5+_T^@%V43V@1V2/01V@%SI2VB1%:4T8651%;4T91R:S0%RI5RH@=1RM%RK3TGRC1p0RM1p0S11p0S61p0S;1p0SB1p0SI1p0SO1p0T91p0T>1p0TC1p0TK1p0TO1p0U61p0U71p0U81p0U<1p0UB1p0UE1p0UH1p0V11p0V61p0V;1p0VF1pR<W61pR:W71pR8W81pSBW91pRNW:1pQFW;1pS8W=1pHW>1pS4WD1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_icu2_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_icu2_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_icu2_fn) 2%nat 0%nat).
Variable S : ltac:(sec_ty2 constr:(SEC_T_art_icu2_fn) 3%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_icu2_fn) 4%nat 0%nat).
Variable t : ltac:(sec_ty2 constr:(SEC_T_art_icu2_fn) 5%nat 0%nat).
Variable f22 : ltac:(sec_ty2 constr:(SEC_T_art_icu2_fn) 6%nat 0%nat).
Variable f23 : ltac:(sec_ty2 constr:(SEC_T_art_icu2_fn) 7%nat 0%nat).
Variable f24 : ltac:(sec_ty2 constr:(SEC_T_art_icu2_fn) 8%nat 0%nat).
Lemma art_icu2_fn : ltac:(sec_stmt2 constr:(SEC_T_art_icu2_fn) 9%nat 0%nat).
Proof using Type regs M rom S n t f22 f23 f24.
intros H2 H24 HS HS' Hn Ht Ht' Atsp Hf22 Hf23 Hf24 W Wt C36 C44 C52 C60 C68 C76 C84 C92 C00 C08.
zsb (ltac:(oF' 0x81640%Z)) (ltac:(oD' 0x81640%Z)) (t + 2047 + 1121) 0 ltac:(rewok Wt). replace (t + 2047 + 1121) with (t + 3168) by lia.
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (D36 : cellA X (S - 2136) 8 0x791c0) by zcell; assert (D44 : cellA X (S - 2144) 8 S) by zcell; assert (D52 : cellA X (S - 2152) 8 n) by zcell;
assert (D60 : cellA X (S - 2160) 8 (U (0x79164 : bv 64)%bv)) by zcell; assert (D68 : cellA X (S - 2168) 8 1) by zcell;
assert (D76 : cellA X (S - 2176) 8 (S - 2128)) by zcell; assert (D84 : cellA X (S - 2184) 8 (S - 81)) by zcell;
assert (D92 : cellA X (S - 2192) 8 f22) by zcell; assert (D00 : cellA X (S - 2200) 8 f23) by zcell; assert (D08 : cellA X (S - 2208) 8 f24) by zcell end.
zld (ltac:(oF' 0x81644%Z)) (ltac:(oD' 0x81644%Z)) (S - 2136) D36. zld (ltac:(oF' 0x81648%Z)) (ltac:(oD' 0x81648%Z)) (S - 2144) D44. zld (ltac:(oF' 0x8164c%Z)) (ltac:(oD' 0x8164c%Z)) (S - 2152) D52. zld (ltac:(oF' 0x81650%Z)) (ltac:(oD' 0x81650%Z)) (S - 2160) D60.
zld (ltac:(oF' 0x81654%Z)) (ltac:(oD' 0x81654%Z)) (S - 2168) D68. zld (ltac:(oF' 0x81658%Z)) (ltac:(oD' 0x81658%Z)) (S - 2176) D76. zld (ltac:(oF' 0x8165c%Z)) (ltac:(oD' 0x8165c%Z)) (S - 2184) D84. zld (ltac:(oF' 0x81660%Z)) (ltac:(oD' 0x81660%Z)) (S - 2192) D92.
zld (ltac:(oF' 0x81664%Z)) (ltac:(oD' 0x81664%Z)) (S - 2200) D00. zld (ltac:(oF' 0x81668%Z)) (ltac:(oD' 0x81668%Z)) (S - 2208) D08.
zstep (ltac:(oF' 0x8166c%Z)) (ltac:(oD' 0x8166c%Z)).
stepjr (ltac:(oF' 0x81670%Z)) (ltac:(oD' 0x81670%Z)) (0x791c0 : bv 64)%bv ltac:(gres; bveq).
zstep (ltac:(oF' 0x791c0%Z)) (ltac:(oD' 0x791c0%Z)). zstep (ltac:(oF' 0x791c4%Z)) (ltac:(oD' 0x791c4%Z)). zstep (ltac:(oF' 0x791c8%Z)) (ltac:(oD' 0x791c8%Z)).
stepn (ltac:(oF' 0x791cc%Z)) (ltac:(oD' 0x791cc%Z)).
zstep (ltac:(oF' 0x51b88%Z)) (ltac:(oD' 0x51b88%Z)).
zsd (ltac:(oF' 0x51b8c%Z)) (ltac:(oD' 0x51b8c%Z)) (S - 2136) (U (0x791d0 : bv 64)%bv) ltac:(rewok W).
zsd (ltac:(oF' 0x51b90%Z)) (ltac:(oD' 0x51b90%Z)) (S - 2144) S ltac:(rewok W).
zstep (ltac:(oF' 0x51b94%Z)) (ltac:(oD' 0x51b94%Z)). zstep (ltac:(oF' 0x51b98%Z)) (ltac:(oD' 0x51b98%Z)). zstep (ltac:(oF' 0x51b9c%Z)) (ltac:(oD' 0x51b9c%Z)). zstep (ltac:(oF' 0x51ba0%Z)) (ltac:(oD' 0x51ba0%Z)). zstep (ltac:(oF' 0x51ba4%Z)) (ltac:(oD' 0x51ba4%Z)). zstep (ltac:(oF' 0x51ba8%Z)) (ltac:(oD' 0x51ba8%Z)). zstep (ltac:(oF' 0x51bac%Z)) (ltac:(oD' 0x51bac%Z)).
stepn (ltac:(oF' 0x51bb0%Z)) (ltac:(oD' 0x51bb0%Z)).
zret.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_ic3_fn := (ltac2:(TCodec.tc2 tcn__JatMalloc "U@&:y5'QFyR0%211%5241'2y8%611%311p061'9'5&Er<(QD+2(3%33A21%6251&QE&Q0r8+RS0%3221%52F1%>3F71r=+:%>3L1<%A231%;2L9%D3L21'4&M+1r9%3221&N&O+R0%22I1%4261%:261+XP0r;%<221+Q?%92Q01%?2Q31&Br>%211z%D21Q8%A2Q9>%G221&?&IrGrD+RRH%Q9221u8&QG+_T^@%QC3QO1QA/01QO%42R11%<5;:761rHrE%QC21QA%@5?31:2rIrF+8%QH221%>2R;C%F5E52@1rJ+@%QM2G1%J5I31D<rK+H%R12@1%N5M31H@rL+Q0%R52@1%Q25Q131LDrM+Q8%R92>1%Q65Q531Q0HrN+Q@%R=2>1%Q:5Q931Q4LrO+QH%RA2>1%Q>5Q=31Q8Q0'A&FvQ6rQ1+ZVmD%RN3S:1RL/01S:rQ0%756521<&G%S33SAR?S1%2381C%S02SAH%432S31%S73SEQ:S5%S32SDQ3%73321+9%S;3SI1S9%S72SHQ;%;3421+B%S?3SM1S=%S;2SLQE%?3421+C%SC3T11SA%S?2T0QM%C3421+D%SG3T51SE%SC2T4R<%G3421+E%SK3T91SI%SG2T8R0%K3421%Q45Q31Q=NQ9%Q63RDN1p0Q81p0Q=1p0QB1p0QG1p0QL1p0R11p0R61p0R=1p0RB1p0S01p0S11p0S21p0S31p0S41p0S51p0S:1p0S>1p0SB1p0SF1p0T21p0T91pRJTI1pRHTJ1pRFTK1pRDTL1pRBTM1pR@TN1pSJTO1pQFU01pS2U81pS8U31pHU41pS4U:1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_ic3_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_ic3_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_ic3_fn) 2%nat 0%nat).
Variable raw0 : ltac:(sec_ty2 constr:(SEC_T_art_ic3_fn) 3%nat 0%nat).
Variable S : ltac:(sec_ty2 constr:(SEC_T_art_ic3_fn) 4%nat 0%nat).
Variable ub : ltac:(sec_ty2 constr:(SEC_T_art_ic3_fn) 5%nat 0%nat).
Variable g16 : ltac:(sec_ty2 constr:(SEC_T_art_ic3_fn) 6%nat 0%nat).
Variable g24 : ltac:(sec_ty2 constr:(SEC_T_art_ic3_fn) 7%nat 0%nat).
Variable g32 : ltac:(sec_ty2 constr:(SEC_T_art_ic3_fn) 8%nat 0%nat).
Variable g40 : ltac:(sec_ty2 constr:(SEC_T_art_ic3_fn) 9%nat 0%nat).
Variable g48 : ltac:(sec_ty2 constr:(SEC_T_art_ic3_fn) 10%nat 0%nat).
Variable g56 : ltac:(sec_ty2 constr:(SEC_T_art_ic3_fn) 11%nat 0%nat).
Lemma art_ic3_fn : ltac:(sec_stmt2 constr:(SEC_T_art_ic3_fn) 12%nat 0%nat).
Proof using Type regs M rom raw0 S ub g16 g24 g32 g40 g48 g56.
intros H2 H10 Hub HS HS' Hret Hg16 Hg24 Hg32 Hg40 Hg48 Hg56 C36 C44 C8 C16 C24 C32 C40 C48 C56.
zbft (ltac:(oF' 0x51bb4%Z)) (ltac:(oD' 0x51bb4%Z)).
zld (ltac:(oF' 0x51bb8%Z)) (ltac:(oD' 0x51bb8%Z)) (S - 2136) C36. zld (ltac:(oF' 0x51bbc%Z)) (ltac:(oD' 0x51bbc%Z)) (S - 2144) C44.
zstep (ltac:(oF' 0x51bc0%Z)) (ltac:(oD' 0x51bc0%Z)).
stepjr (ltac:(oF' 0x51bc4%Z)) (ltac:(oD' 0x51bc4%Z)) (0x791d0 : bv 64)%bv ltac:(gres; bveq).
zstep (ltac:(oF' 0x791d0%Z)) (ltac:(oD' 0x791d0%Z)).
zld (ltac:(oF' 0x791d4%Z)) (ltac:(oD' 0x791d4%Z)) (S - 8) C8. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x791d8%Z)) (ltac:(oD' 0x791d8%Z)) (S - 16) C16. zld (ltac:(oF' 0x791dc%Z)) (ltac:(oD' 0x791dc%Z)) (S - 24) C24. zld (ltac:(oF' 0x791e0%Z)) (ltac:(oD' 0x791e0%Z)) (S - 32) C32.
zld (ltac:(oF' 0x791e4%Z)) (ltac:(oD' 0x791e4%Z)) (S - 40) C40. zld (ltac:(oF' 0x791e8%Z)) (ltac:(oD' 0x791e8%Z)) (S - 48) C48. zld (ltac:(oF' 0x791ec%Z)) (ltac:(oD' 0x791ec%Z)) (S - 56) C56.
zstep (ltac:(oF' 0x791f0%Z)) (ltac:(oD' 0x791f0%Z)).
stepret (ltac:(oF' 0x791f4%Z)) (ltac:(oD' 0x791f4%Z)) raw0 ltac:(rwH; reflexivity).
zret.
Qed.
End SE.
End FPX.
