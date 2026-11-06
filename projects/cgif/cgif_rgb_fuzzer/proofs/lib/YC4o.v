(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YF8z YC1d YC1a YC2o YC10 YC2p YC1b.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require YR00.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition A_GOT_rawnew : Z := 0xa2de0.
Definition A_stack_malloc_2 : Z := 0x3d03c.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition RBx : sv := SOff 35 0.
Definition RBspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition rn_extra (g pgct rattr Wd Hd sgct loops ctx : Z) : list word :=
map (Z_to_bv 64) [g; pgct; rattr; SB; Wd; Hd; sgct; loops; ctx].
Definition cfg_region : YQ0b.region :=
YQ0b.mkRegion (Some 10%nat) 0 40 0 0
[YQ0b.mkChunk 0 (CVal 8 (SLit A_cgif_writecb)); YQ0b.mkChunk 8 (CVal 8 (SOff 32 0)); YQ0b.mkChunk 16 (CVal 8 (SOff 33 0));
YQ0b.mkChunk 24 (CVal 4 (SOff 34 0)); YQ0b.mkChunk 28 (CVal 2 (SOff 36 0)); YQ0b.mkChunk 30 (CVal 2 (SOff 37 0));
YQ0b.mkChunk 32 (CVal 2 (SOff 38 0)); YQ0b.mkChunk 34 (CVal 2 (SOff 39 0))].
Definition g_region : YQ0b.region :=
YQ0b.mkRegion (Some 32%nat) 0 CGIF_SIZE 0 0
[YQ0b.mkChunk 56 (CVal 8 (SLit A_writecb)); YQ0b.mkChunk 64 (CVal 8 (SOff 40 0)); YQ0b.mkChunk 80 (CVal 8 (SLit 0))].
Definition rn_regions0 : smem :=
[ stack_region 192; got_region; bcell_region 35; uar_got_region; uar_cell_region; const8_region A_GOT_rawnew A_cgif_raw_newgif;
cfg_region; g_region ].
Definition rn_atoms0 : list (nat * afact) :=
[ (2%nat, mkAF (2^46) (2^47) 5); (10%nat, HPTR 3); (32%nat, HPTR 4); (33%nat, mkAF 0 (2^64 - 1) 0);
(34%nat, mkAF 0 (2^32 - 1) 0); (35%nat, mkAF SB SB 0); (36%nat, mkAF 0 65535 0); (37%nat, mkAF 0 65535 0);
(38%nat, mkAF 0 65535 0); (39%nat, mkAF 0 65535 0); (40%nat, mkAF 0 (2^64 - 1) 0) ].
Definition ss_rn0 : sstate := mkSS A_cgif_raw_newgif sr_atoms rn_regions0 None (mkFacts rn_atoms0 [] []).
Definition ss_B : sstate :=
ltac2:(YR00.build ['(mkSST); '(@cons sv); '(SLit); '(SOff); '(SAlu); '(ALU_ADD); '(ALU_SRL); '(@nil sv); '(@cons YQ0b.region); '(YQ0b.mkRegion); '(@Some nat); '(@cons YQ0b.chunk); '(YQ0b.mkChunk); '(CVal); '(@nil YQ0b.chunk); '(@None nat); '(@nil YQ0b.region); '(@None sv); '(mkFacts); '(@cons (prod nat afact)); '(@pair nat afact); '(mkAF); '(@nil (prod nat afact)); '(@cons acond); '(mkAC); '(BC_GEU); '(@nil acond); '(@cons (prod sv sv)); '(@pair sv sv); '(@nil (prod sv sv))] [24;2233281;40;68;1;40;104;302;1;40;104;10;3;192;40;104;14;1;40;104;18;1;40;104;306;1;40;104;310;1;40;104;314;1;40;104;10;1;40;104;10;3;192;40;104;318;1;40;104;322;1;40;104;326;1;40;104;330;1;40;104;334;1;40;104;338;1;40;104;342;1;40;104;346;1;40;104;182;1;40;104;78;1;40;104;42;1;40;104;86;1;40;104;90;1;40;104;42;129;40;104;142;1;40;140;160;140;192;104;42;129;68;13;104;142;1;40;104;234;1;40;104;182;1;40;104;350;1;40;104;354;1;40;104;358;1;40;104;362;1;224;224;264;312;324;254;1;193;161;193;360;392;1;424;15;8;68;2191249;360;392;33;424;15;8;104;130;1;360;392;65;424;15;8;104;134;1;360;392;97;424;15;4;104;138;1;360;392;113;424;15;2;104;146;1;360;392;121;424;15;2;104;150;1;360;392;129;424;15;2;104;154;1;360;392;137;424;15;2;104;158;1;448;264;312;324;234;1;129;1;1;360;392;29;424;15;1;68;1;360;392;25;424;15;1;68;1;360;392;21;424;15;1;68;7;1;3;1073741810;1073741823;15;360;392;17;424;15;1;68;7;1;3;1073741816;1073741823;15;360;392;45;424;15;1;68;7;1;3;1073741810;1073741823;15;360;392;41;424;15;1;68;7;1;3;1073741810;1073741823;15;360;392;37;424;15;1;68;7;1;3;1073741810;1073741823;15;360;392;33;424;15;1;68;13;360;392;69;424;15;1;68;7;1;3;1073741811;1073741823;15;360;392;65;424;15;1;68;7;1;3;1073741811;1073741823;15;360;392;61;424;15;1;68;21;360;392;57;424;15;1;68;1;360;392;77;424;15;1;68;7;1;3;1073741811;1073741823;15;360;392;73;424;15;1;68;7;1;3;1073741811;1073741823;15;360;392;53;424;15;1;68;7;1;3;1073741810;1073741823;15;360;392;49;424;15;1;68;7;1;3;1073741810;1073741823;15;360;392;13;424;15;1;68;7;1;3;1073741809;1073741823;15;360;392;9;424;15;1;68;7;1;3;1073741809;1073741823;15;360;392;5;424;15;1;68;7;1;3;1073741809;1073741823;15;360;392;1;424;15;1;68;7;1;3;1073741809;1073741823;15;360;392;97;424;15;8;68;1;448;264;312;324;182;1;1025;1;1025;360;392;65;424;15;8;68;2231761;360;392;33;424;15;8;68;475977;360;392;1;424;15;8;68;4409666253;360;392;993;424;15;8;104;230;1;448;264;312;324;10;3;192;1;3;192;1;360;392;3;152;424;15;8;104;254;1;360;392;3;112;424;15;8;104;182;1;360;392;3;104;424;15;8;104;110;1;360;392;3;96;424;15;8;104;106;1;360;392;3;88;424;15;8;104;102;1;360;392;3;80;424;15;8;104;98;1;360;392;3;72;424;15;8;104;94;1;360;392;3;64;424;15;8;104;90;1;360;392;3;56;424;15;8;104;86;1;360;392;3;48;424;15;8;104;82;1;360;392;3;40;424;15;8;104;78;1;360;392;3;32;424;15;8;104;74;1;360;392;3;24;424;15;8;104;38;1;360;392;3;16;424;15;8;104;34;1;360;392;3;8;424;15;8;104;6;1;360;392;3;192;424;15;8;68;1;448;264;312;480;2655617;2655649;1;1;360;392;2655617;424;15;8;68;2787041;448;264;312;480;2787041;2787073;1;1;360;392;2787041;424;15;8;104;142;1;448;264;312;480;2655969;2656001;1;1;360;392;2655969;424;15;8;68;2787073;448;264;312;480;2787073;2787089;1;1;360;392;2787073;424;15;4;68;5;448;264;312;480;2668417;2668449;1;1;360;392;2668417;424;15;8;68;2231761;448;264;312;324;42;1;161;1;1;360;392;1;424;15;8;68;2191249;360;392;33;424;15;8;104;130;1;360;392;65;424;15;8;104;134;1;360;392;97;424;15;4;104;138;1;360;392;113;424;15;2;104;146;1;360;392;121;424;15;2;104;150;1;360;392;129;424;15;2;104;154;1;360;392;137;424;15;2;104;158;1;448;264;312;324;130;1;385;1;1;360;392;225;424;15;8;68;2119313;360;392;257;424;15;8;104;162;1;360;392;321;424;15;8;68;1;448;512;544;588;616;648;254;684;16385;562949919866881;17;616;648;234;684;8589805569;70377333981185;9;616;648;230;684;16385;562949919866881;1;616;648;182;684;16385;562949919866881;21;616;648;10;684;281474976710657;562949953421313;21;616;648;42;684;16385;562949919866881;13;616;648;130;684;16385;562949919866881;17;616;648;134;684;1;7;1;3;1073741823;1073741823;15;1;616;648;138;684;1;17179869181;1;616;648;142;684;8589803521;8589803521;1;616;648;146;684;1;262141;1;616;648;150;684;1;262141;1;616;648;154;684;1;262141;1;616;648;158;684;1;262141;1;616;648;162;684;1;7;1;3;1073741823;1073741823;15;1;704;744;780;800;68;1025;104;154;1;832;872;904;140;160;140;192;104;182;1;68;13;104;142;1;104;234;1;928]).
Definition rn_deads_C : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 19; 21; 28; 29; 30; 31]%bv.
Definition ss_C : sstate :=
ltac2:(YR00.build ['(mkSST); '(@cons sv); '(SLit); '(SOff); '(SAlu); '(ALU_ADD); '(ALU_SRL); '(@nil sv); '(@cons YQ0b.region); '(YQ0b.mkRegion); '(@Some nat); '(@nil YQ0b.chunk); '(@cons YQ0b.chunk); '(YQ0b.mkChunk); '(CVal); '(@None nat); '(@nil YQ0b.region); '(@None sv); '(mkFacts); '(@cons (prod nat afact)); '(@pair nat afact); '(mkAF); '(@nil (prod nat afact)); '(@nil acond); '(@cons (prod sv sv)); '(@pair sv sv); '(@nil (prod sv sv))] [24;2234161;40;68;1;40;104;642;1;40;104;10;3;192;40;104;14;1;40;104;18;1;40;104;646;1;40;104;650;1;40;104;654;1;40;104;10;1;40;104;10;3;192;40;104;658;1;40;104;662;1;40;104;666;1;40;104;670;1;40;104;674;1;40;104;678;1;40;104;682;1;40;104;686;1;40;104;182;1;40;104;690;1;40;104;42;1;40;104;694;1;40;104;182;449;40;104;42;129;40;104;142;1;40;140;160;140;192;104;42;129;68;13;104;142;1;40;104;234;1;40;104;182;1;40;104;698;1;40;104;702;1;40;104;706;1;40;104;710;1;224;224;264;312;324;182;489;501;489;501;352;264;312;324;182;1;489;1;489;352;264;312;324;254;1;193;161;193;392;424;1;456;15;8;68;2191249;392;424;33;456;15;8;104;130;1;392;424;65;456;15;8;104;134;1;392;424;97;456;15;4;104;138;1;392;424;113;456;15;2;104;146;1;392;424;121;456;15;2;104;150;1;392;424;129;456;15;2;104;154;1;392;424;137;456;15;2;104;158;1;352;264;312;324;234;1;129;1;1;392;424;29;456;15;1;68;1;392;424;25;456;15;1;68;1;392;424;21;456;15;1;68;7;1;3;1073741810;1073741823;15;392;424;17;456;15;1;68;7;1;3;1073741816;1073741823;15;392;424;45;456;15;1;68;7;1;3;1073741810;1073741823;15;392;424;41;456;15;1;68;7;1;3;1073741810;1073741823;15;392;424;37;456;15;1;68;7;1;3;1073741810;1073741823;15;392;424;33;456;15;1;68;13;392;424;69;456;15;1;68;7;1;3;1073741811;1073741823;15;392;424;65;456;15;1;68;7;1;3;1073741811;1073741823;15;392;424;61;456;15;1;68;21;392;424;57;456;15;1;68;1;392;424;77;456;15;1;68;7;1;3;1073741811;1073741823;15;392;424;73;456;15;1;68;7;1;3;1073741811;1073741823;15;392;424;53;456;15;1;68;7;1;3;1073741810;1073741823;15;392;424;49;456;15;1;68;7;1;3;1073741810;1073741823;15;392;424;13;456;15;1;68;7;1;3;1073741809;1073741823;15;392;424;9;456;15;1;68;7;1;3;1073741809;1073741823;15;392;424;5;456;15;1;68;7;1;3;1073741809;1073741823;15;392;424;1;456;15;1;68;7;1;3;1073741809;1073741823;15;392;424;97;456;15;8;68;1;352;264;312;324;182;501;1025;501;1025;392;424;993;456;15;8;104;230;1;352;264;312;324;10;3;192;1;3;192;1;392;424;3;160;456;15;8;104;182;1;392;424;3;152;456;15;8;104;254;1;392;424;3;112;456;15;8;104;182;1;392;424;3;104;456;15;8;104;110;1;392;424;3;96;456;15;8;104;106;1;392;424;3;88;456;15;8;104;102;1;392;424;3;80;456;15;8;104;98;1;392;424;3;72;456;15;8;104;94;1;392;424;3;64;456;15;8;104;90;1;392;424;3;56;456;15;8;104;86;1;392;424;3;48;456;15;8;104;82;1;392;424;3;40;456;15;8;104;78;1;392;424;3;32;456;15;8;104;74;1;392;424;3;24;456;15;8;104;38;1;392;424;3;16;456;15;8;104;34;1;392;424;3;8;456;15;8;104;6;1;392;424;3;192;456;15;8;68;1;352;264;312;480;2655617;2655649;1;1;392;424;2655617;456;15;8;68;2787041;352;264;312;480;2787041;2787073;1;1;392;424;2787041;456;15;8;104;142;1;352;264;312;480;2655969;2656001;1;1;392;424;2655969;456;15;8;68;2787073;352;264;312;480;2787073;2787089;1;1;392;424;2787073;456;15;4;68;5;352;264;312;480;2668417;2668449;1;1;392;424;2668417;456;15;8;68;2231761;352;264;312;324;42;1;161;1;1;392;424;1;456;15;8;68;2191249;392;424;33;456;15;8;104;130;1;392;424;65;456;15;8;104;134;1;392;424;97;456;15;4;104;138;1;392;424;113;456;15;2;104;146;1;392;424;121;456;15;2;104;150;1;392;424;129;456;15;2;104;154;1;392;424;137;456;15;2;104;158;1;352;264;312;324;130;1;385;1;1;392;424;225;456;15;8;68;2119313;392;424;257;456;15;8;104;162;1;392;424;321;456;15;8;68;1;352;512;544;588;616;648;254;684;16385;562949919866881;17;616;648;234;684;8589805569;70377333981185;9;616;648;230;684;16385;562949919866881;1;616;648;182;684;16385;562949919866881;21;616;648;10;684;281474976710657;562949953421313;21;616;648;42;684;16385;562949919866881;13;616;648;130;684;16385;562949919866881;17;616;648;134;684;1;7;1;3;1073741823;1073741823;15;1;616;648;138;684;1;17179869181;1;616;648;142;684;8589803521;8589803521;1;616;648;146;684;1;262141;1;616;648;150;684;1;262141;1;616;648;154;684;1;262141;1;616;648;158;684;1;262141;1;616;648;162;684;1;7;1;3;1073741823;1073741823;15;1;704;736;776;808;140;160;140;192;104;182;1;68;13;104;142;1;104;234;1;832]).
Definition rn_deads_G : list (bv 5) := [1; 5; 6; 7; 11; 14; 16; 17; 25; 28; 29; 30; 31]%bv.
Definition ss_G : sstate :=
ltac2:(YR00.build ['(mkSST); '(@cons sv); '(SLit); '(SOff); '(@nil sv); '(@cons YQ0b.region); '(YQ0b.mkRegion); '(@Some nat); '(@nil YQ0b.chunk); '(@cons YQ0b.chunk); '(YQ0b.mkChunk); '(CVal); '(SAlu); '(ALU_ADD); '(ALU_SRL); '(@None nat); '(@nil YQ0b.region); '(@None sv); '(mkFacts); '(@cons (prod nat afact)); '(@pair nat afact); '(mkAF); '(@nil (prod nat afact)); '(@cons acond); '(mkAC); '(BC_NE); '(@nil acond); '(@cons (prod sv sv)); '(@pair sv sv); '(@nil (prod sv sv))] [24;2234881;40;68;1;40;104;882;1;40;104;10;3;192;40;104;14;1;40;104;18;1;40;104;886;1;40;104;890;1;40;104;894;1;40;104;10;1;40;104;10;3;192;40;68;1;40;104;898;1;40;68;1;40;68;5;40;104;902;1;40;104;154;1;40;104;906;1;40;104;910;1;40;104;182;1;40;104;42;33;40;104;42;1;40;68;1;40;104;182;449;40;104;182;129;40;104;142;1;40;104;914;1;40;104;234;1;40;104;182;1;40;104;918;1;40;104;922;1;40;104;926;1;40;104;930;1;128;128;168;216;228;10;3;208;3;192;3;208;3;192;256;168;216;228;182;489;501;489;501;256;168;216;228;182;1;489;1;489;256;168;216;228;254;1;193;161;193;296;328;1;360;15;8;68;2191249;296;328;33;360;15;8;104;130;1;296;328;65;360;15;8;104;134;1;296;328;97;360;15;4;104;138;1;296;328;113;360;15;2;104;146;1;296;328;121;360;15;2;104;150;1;296;328;129;360;15;2;104;154;1;296;328;137;360;15;2;104;158;1;256;168;216;228;234;1;129;1;1;296;328;29;360;15;1;68;1;296;328;25;360;15;1;68;1;296;328;21;360;15;1;68;7;1;3;1073741810;1073741823;15;296;328;17;360;15;1;68;7;1;3;1073741816;1073741823;15;296;328;45;360;15;1;68;7;1;3;1073741810;1073741823;15;296;328;41;360;15;1;68;7;1;3;1073741810;1073741823;15;296;328;37;360;15;1;68;7;1;3;1073741810;1073741823;15;296;328;33;360;15;1;68;13;296;328;69;360;15;1;68;7;1;3;1073741811;1073741823;15;296;328;65;360;15;1;68;7;1;3;1073741811;1073741823;15;296;328;61;360;15;1;68;21;296;328;57;360;15;1;68;1;296;328;77;360;15;1;68;7;1;3;1073741811;1073741823;15;296;328;73;360;15;1;68;7;1;3;1073741811;1073741823;15;296;328;53;360;15;1;68;7;1;3;1073741810;1073741823;15;296;328;49;360;15;1;68;7;1;3;1073741810;1073741823;15;296;328;13;360;15;1;68;7;1;3;1073741809;1073741823;15;296;328;9;360;15;1;68;7;1;3;1073741809;1073741823;15;296;328;5;360;15;1;68;7;1;3;1073741809;1073741823;15;296;328;1;360;15;1;68;7;1;3;1073741809;1073741823;15;296;328;97;360;15;8;68;1;256;168;216;228;182;501;1025;501;1025;296;328;993;360;15;8;104;230;1;256;168;216;228;10;3;192;1;3;192;1;296;328;3;168;360;15;8;104;42;33;296;328;3;144;360;15;8;396;416;396;448;104;42;33;68;13;104;142;1;296;328;3;136;360;15;8;396;416;396;448;104;42;1;68;13;104;142;1;296;328;3;160;360;15;8;104;182;1;296;328;3;152;360;15;8;104;254;1;296;328;3;112;360;15;8;104;182;1;296;328;3;104;360;15;8;104;110;1;296;328;3;96;360;15;8;104;106;1;296;328;3;88;360;15;8;104;102;1;296;328;3;80;360;15;8;104;98;1;296;328;3;72;360;15;8;104;94;1;296;328;3;64;360;15;8;104;90;1;296;328;3;56;360;15;8;104;86;1;296;328;3;48;360;15;8;104;82;1;296;328;3;40;360;15;8;104;78;1;296;328;3;32;360;15;8;104;74;1;296;328;3;24;360;15;8;104;38;1;296;328;3;16;360;15;8;104;34;1;296;328;3;8;360;15;8;104;6;1;296;328;3;192;360;15;8;68;1;256;168;216;480;2655617;2655649;1;1;296;328;2655617;360;15;8;68;2787041;256;168;216;480;2787041;2787073;1;1;296;328;2787041;360;15;8;104;142;1;256;168;216;480;2655969;2656001;1;1;296;328;2655969;360;15;8;68;2787073;256;168;216;480;2787073;2787089;1;1;296;328;2787073;360;15;4;68;5;256;168;216;480;2668417;2668449;1;1;296;328;2668417;360;15;8;68;2231761;256;168;216;228;42;1;161;1;1;296;328;1;360;15;8;68;2191249;296;328;33;360;15;8;104;130;1;296;328;65;360;15;8;104;134;1;296;328;97;360;15;4;104;138;1;296;328;113;360;15;2;104;146;1;296;328;121;360;15;2;104;150;1;296;328;129;360;15;2;104;154;1;296;328;137;360;15;2;104;158;1;256;168;216;228;130;1;385;1;1;296;328;225;360;15;8;68;2119313;296;328;257;360;15;8;104;162;1;296;328;321;360;15;8;68;1;256;512;544;588;616;648;254;684;16385;562949919866881;17;616;648;234;684;8589805569;70377333981185;9;616;648;230;684;16385;562949919866881;1;616;648;182;684;16385;562949919866881;21;616;648;10;684;281474976710657;562949953421313;21;616;648;42;684;16385;562949919866881;13;616;648;130;684;16385;562949919866881;17;616;648;134;684;1;7;1;3;1073741823;1073741823;15;1;616;648;138;684;1;17179869181;1;616;648;142;684;8589803521;8589803521;1;616;648;146;684;1;262141;1;616;648;150;684;1;262141;1;616;648;154;684;1;262141;1;616;648;158;684;1;262141;1;616;648;162;684;1;7;1;3;1073741823;1073741823;15;1;704;744;780;800;104;154;1;68;1;832;872;904;396;416;396;448;104;182;1;68;13;104;142;1;104;234;1;928]).
Definition rn_deads_D : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 19; 22; 23; 25; 28; 29; 30; 31]%bv.
Definition ss_D : sstate :=
ltac2:(YR00.build ['(mkSST); '(@cons sv); '(SLit); '(SOff); '(@nil sv); '(@cons YQ0b.region); '(YQ0b.mkRegion); '(@Some nat); '(@nil YQ0b.chunk); '(@cons YQ0b.chunk); '(YQ0b.mkChunk); '(CVal); '(SAlu); '(ALU_ADD); '(ALU_SRL); '(@None nat); '(@nil YQ0b.region); '(@None sv); '(mkFacts); '(@cons (prod nat afact)); '(@pair nat afact); '(mkAF); '(@nil (prod nat afact)); '(@nil acond); '(@cons (prod sv sv)); '(@pair sv sv); '(@nil (prod sv sv))] [24;2235601;40;68;1;40;104;1202;1;40;104;10;3;192;40;104;14;1;40;104;18;1;40;104;1206;1;40;104;1210;1;40;104;1214;1;40;104;10;1;40;104;10;3;192;40;104;1218;1;40;104;1222;1;40;104;1226;1;40;104;1230;1;40;104;1234;1;40;104;1238;1;40;104;1242;1;40;104;1246;1;40;104;182;1;40;104;1250;1;40;104;42;1;40;68;1;40;104;1254;1;40;104;1258;1;40;104;142;1;40;104;1262;1;40;104;234;1;40;104;182;1;40;104;1266;1;40;104;1270;1;40;104;1274;1;40;104;1278;1;128;128;168;216;228;182;489;501;489;501;256;168;216;228;182;1;489;1;489;256;168;216;228;254;1;193;161;193;296;328;1;360;15;8;68;2191249;296;328;33;360;15;8;104;130;1;296;328;65;360;15;8;104;134;1;296;328;97;360;15;4;104;138;1;296;328;113;360;15;2;104;146;1;296;328;121;360;15;2;104;150;1;296;328;129;360;15;2;104;154;1;296;328;137;360;15;2;104;158;1;256;168;216;228;234;1;129;1;1;296;328;29;360;15;1;68;1;296;328;25;360;15;1;68;1;296;328;21;360;15;1;68;7;1;3;1073741810;1073741823;15;296;328;17;360;15;1;68;7;1;3;1073741816;1073741823;15;296;328;45;360;15;1;68;7;1;3;1073741810;1073741823;15;296;328;41;360;15;1;68;7;1;3;1073741810;1073741823;15;296;328;37;360;15;1;68;7;1;3;1073741810;1073741823;15;296;328;33;360;15;1;68;13;296;328;69;360;15;1;68;7;1;3;1073741811;1073741823;15;296;328;65;360;15;1;68;7;1;3;1073741811;1073741823;15;296;328;61;360;15;1;68;21;296;328;57;360;15;1;68;1;296;328;77;360;15;1;68;7;1;3;1073741811;1073741823;15;296;328;73;360;15;1;68;7;1;3;1073741811;1073741823;15;296;328;53;360;15;1;68;7;1;3;1073741810;1073741823;15;296;328;49;360;15;1;68;7;1;3;1073741810;1073741823;15;296;328;13;360;15;1;68;7;1;3;1073741809;1073741823;15;296;328;9;360;15;1;68;7;1;3;1073741809;1073741823;15;296;328;5;360;15;1;68;7;1;3;1073741809;1073741823;15;296;328;1;360;15;1;68;7;1;3;1073741809;1073741823;15;296;328;97;360;15;8;68;1;256;168;216;228;182;501;1025;501;1025;296;328;993;360;15;8;104;230;1;256;168;216;228;10;3;192;1;3;192;1;296;328;3;168;360;15;8;104;42;33;296;328;3;144;360;15;8;396;416;396;448;104;42;33;68;13;104;142;1;296;328;3;136;360;15;8;396;416;396;448;104;42;1;68;13;104;142;1;296;328;3;160;360;15;8;104;182;1;296;328;3;152;360;15;8;104;254;1;296;328;3;112;360;15;8;104;182;1;296;328;3;104;360;15;8;104;110;1;296;328;3;96;360;15;8;104;106;1;296;328;3;88;360;15;8;104;102;1;296;328;3;80;360;15;8;104;98;1;296;328;3;72;360;15;8;104;94;1;296;328;3;64;360;15;8;104;90;1;296;328;3;56;360;15;8;104;86;1;296;328;3;48;360;15;8;104;82;1;296;328;3;40;360;15;8;104;78;1;296;328;3;32;360;15;8;104;74;1;296;328;3;24;360;15;8;104;38;1;296;328;3;16;360;15;8;104;34;1;296;328;3;8;360;15;8;104;6;1;296;328;3;192;360;15;8;68;1;256;168;216;480;2655617;2655649;1;1;296;328;2655617;360;15;8;68;2787041;256;168;216;480;2787041;2787073;1;1;296;328;2787041;360;15;8;104;142;1;256;168;216;480;2655969;2656001;1;1;296;328;2655969;360;15;8;68;2787073;256;168;216;480;2787073;2787089;1;1;296;328;2787073;360;15;4;68;5;256;168;216;480;2668417;2668449;1;1;296;328;2668417;360;15;8;68;2231761;256;168;216;228;42;1;161;1;1;296;328;1;360;15;8;68;2191249;296;328;33;360;15;8;104;130;1;296;328;65;360;15;8;104;134;1;296;328;97;360;15;4;104;138;1;296;328;113;360;15;2;104;146;1;296;328;121;360;15;2;104;150;1;296;328;129;360;15;2;104;154;1;296;328;137;360;15;2;104;158;1;256;168;216;228;130;1;385;1;1;296;328;225;360;15;8;68;2119313;296;328;257;360;15;8;104;162;1;296;328;321;360;15;8;68;1;256;512;544;588;616;648;254;684;16385;562949919866881;17;616;648;234;684;8589805569;70377333981185;9;616;648;230;684;16385;562949919866881;1;616;648;182;684;16385;562949919866881;21;616;648;10;684;281474976710657;562949953421313;21;616;648;42;684;16385;562949919866881;13;616;648;130;684;16385;562949919866881;17;616;648;134;684;1;7;1;3;1073741823;1073741823;15;1;616;648;138;684;1;17179869181;1;616;648;142;684;8589803521;8589803521;1;616;648;146;684;1;262141;1;616;648;150;684;1;262141;1;616;648;154;684;1;262141;1;616;648;158;684;1;262141;1;616;648;162;684;1;7;1;3;1073741823;1073741823;15;1;704;736;776;808;396;416;396;448;104;182;1;68;13;104;142;1;104;234;1;832]).
Definition rn_deads_X : list (bv 5) := [1; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 19; 20; 21; 22; 23; 24; 25; 28; 29; 30; 31]%bv.
Definition ss_X : sstate :=
ltac2:(YR00.build ['(mkSST); '(@cons sv); '(SLit); '(SOff); '(@nil sv); '(@cons YQ0b.region); '(YQ0b.mkRegion); '(@Some nat); '(@nil YQ0b.chunk); '(@cons YQ0b.chunk); '(YQ0b.mkChunk); '(CVal); '(SAlu); '(ALU_ADD); '(ALU_SRL); '(@None nat); '(@nil YQ0b.region); '(@None sv); '(mkFacts); '(@cons (prod nat afact)); '(@pair nat afact); '(mkAF); '(@nil (prod nat afact)); '(@nil acond); '(@cons (prod sv sv)); '(@pair sv sv); '(@nil (prod sv sv))] [24;2236689;40;68;1;40;104;1602;1;40;104;10;3;192;40;104;14;1;40;104;18;1;40;104;1606;1;40;104;1610;1;40;104;1614;1;40;104;10;1;40;104;10;3;192;40;104;254;1;40;104;1618;1;40;104;1622;1;40;104;1626;1;40;104;1630;1;40;104;1634;1;40;104;1638;1;40;104;1642;1;40;104;182;1;40;104;1646;1;40;104;1650;1;40;104;1654;1;40;104;1658;1;40;104;1662;1;40;104;1666;1;40;104;1670;1;40;104;234;1;40;104;182;1;40;104;1674;1;40;104;1678;1;40;104;1682;1;40;104;1686;1;128;128;168;216;228;182;489;501;489;501;256;168;216;228;182;1;489;1;489;256;168;216;228;254;1;193;161;193;296;328;161;360;15;4;68;25;296;328;1;360;15;8;68;2191249;296;328;33;360;15;8;104;130;1;296;328;65;360;15;8;104;134;1;296;328;97;360;15;4;104;138;1;296;328;113;360;15;2;104;146;1;296;328;121;360;15;2;104;150;1;296;328;129;360;15;2;104;154;1;296;328;137;360;15;2;104;158;1;256;168;216;228;234;1;129;1;1;296;328;29;360;15;1;68;1;296;328;25;360;15;1;68;1;296;328;21;360;15;1;68;7;1;3;1073741810;1073741823;15;296;328;17;360;15;1;68;7;1;3;1073741816;1073741823;15;296;328;45;360;15;1;68;7;1;3;1073741810;1073741823;15;296;328;41;360;15;1;68;7;1;3;1073741810;1073741823;15;296;328;37;360;15;1;68;7;1;3;1073741810;1073741823;15;296;328;33;360;15;1;68;13;296;328;69;360;15;1;68;7;1;3;1073741811;1073741823;15;296;328;65;360;15;1;68;7;1;3;1073741811;1073741823;15;296;328;61;360;15;1;68;21;296;328;57;360;15;1;68;1;296;328;77;360;15;1;68;7;1;3;1073741811;1073741823;15;296;328;73;360;15;1;68;7;1;3;1073741811;1073741823;15;296;328;53;360;15;1;68;7;1;3;1073741810;1073741823;15;296;328;49;360;15;1;68;7;1;3;1073741810;1073741823;15;296;328;13;360;15;1;68;7;1;3;1073741809;1073741823;15;296;328;9;360;15;1;68;7;1;3;1073741809;1073741823;15;296;328;5;360;15;1;68;7;1;3;1073741809;1073741823;15;296;328;1;360;15;1;68;7;1;3;1073741809;1073741823;15;296;328;97;360;15;8;68;1;256;168;216;228;182;501;1025;501;1025;296;328;993;360;15;8;104;230;1;256;168;216;228;10;3;192;1;3;192;1;296;328;3;168;360;15;8;104;42;33;296;328;3;144;360;15;8;396;416;396;448;104;42;33;68;13;104;142;1;296;328;3;136;360;15;8;396;416;396;448;104;42;1;68;13;104;142;1;296;328;3;160;360;15;8;104;182;1;296;328;3;152;360;15;8;104;254;1;296;328;3;112;360;15;8;104;182;1;296;328;3;104;360;15;8;104;110;1;296;328;3;96;360;15;8;104;106;1;296;328;3;88;360;15;8;104;102;1;296;328;3;80;360;15;8;104;98;1;296;328;3;72;360;15;8;104;94;1;296;328;3;64;360;15;8;104;90;1;296;328;3;56;360;15;8;104;86;1;296;328;3;48;360;15;8;104;82;1;296;328;3;40;360;15;8;104;78;1;296;328;3;32;360;15;8;104;74;1;296;328;3;24;360;15;8;104;38;1;296;328;3;16;360;15;8;104;34;1;296;328;3;8;360;15;8;104;6;1;296;328;3;192;360;15;8;68;1;256;168;216;480;2655617;2655649;1;1;296;328;2655617;360;15;8;68;2787041;256;168;216;480;2787041;2787073;1;1;296;328;2787041;360;15;8;104;142;1;256;168;216;480;2655969;2656001;1;1;296;328;2655969;360;15;8;68;2787073;256;168;216;480;2787073;2787089;1;1;296;328;2787073;360;15;4;68;5;256;168;216;480;2668417;2668449;1;1;296;328;2668417;360;15;8;68;2231761;256;168;216;228;42;1;161;1;1;296;328;1;360;15;8;68;2191249;296;328;33;360;15;8;104;130;1;296;328;65;360;15;8;104;134;1;296;328;97;360;15;4;104;138;1;296;328;113;360;15;2;104;146;1;296;328;121;360;15;2;104;150;1;296;328;129;360;15;2;104;154;1;296;328;137;360;15;2;104;158;1;256;168;216;228;130;1;385;1;1;296;328;225;360;15;8;68;2119313;296;328;257;360;15;8;104;162;1;296;328;321;360;15;8;68;1;256;512;544;588;616;648;254;684;16385;562949919866881;17;616;648;234;684;8589805569;70377333981185;9;616;648;230;684;16385;562949919866881;1;616;648;182;684;16385;562949919866881;21;616;648;10;684;281474976710657;562949953421313;21;616;648;42;684;16385;562949919866881;13;616;648;130;684;16385;562949919866881;17;616;648;134;684;1;7;1;3;1073741823;1073741823;15;1;616;648;138;684;1;17179869181;1;616;648;142;684;8589803521;8589803521;1;616;648;146;684;1;262141;1;616;648;150;684;1;262141;1;616;648;154;684;1;262141;1;616;648;158;684;1;262141;1;616;648;162;684;1;7;1;3;1073741823;1073741823;15;1;704;736;776;808;396;416;396;448;104;182;1;68;13;104;142;1;104;234;1;832]).
Definition rn_E0 (regs : bvmap 5 word) (cfgp g : Z) (E0 : env) : Prop :=
(forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = getr regs r) /\
ew E0 10 = Z_to_bv 64 cfgp /\ ew E0 32 = Z_to_bv 64 g /\ bv_unsigned (ew E0 2) = spZ regs.
Definition rn_E (E0 E : env) (pgct rattr Wd Hd sgct loops ctx F FL res : Z) : Prop :=
(forall n, (n < 33)%nat -> ew E n = ew E0 n) /\
ew E 33 = Z_to_bv 64 pgct /\ ew E 34 = Z_to_bv 64 rattr /\ ew E 35 = Z_to_bv 64 SB /\ ew E 36 = Z_to_bv 64 Wd /\
ew E 37 = Z_to_bv 64 Hd /\ ew E 38 = Z_to_bv 64 sgct /\ ew E 39 = Z_to_bv 64 loops /\ ew E 40 = Z_to_bv 64 ctx /\
ew E 45 = Z_to_bv 64 F /\ ew E 57 = Z_to_bv 64 FL /\ ew E 58 = Z_to_bv 64 (SB + F / 8) /\ ew E 63 = Z_to_bv 64 res.
Definition rn_cfg (B : asyms) (ly : alayout) (S : astate) (W : world trasegs) (mem : word -> option byte) (cid pos cfgp : Z) : Prop :=
In (cid, pos) (frames S) /\ 0 <= cid /\ frame_addr ly cid pos mod 8 = 0 /\
frame_addr ly cid pos <= cfgp /\ cfgp + 40 <= frame_addr ly cid pos + fs_frame_bytes cid /\ cfgp mod 8 = 0 /\
range_addressable (aview trasegs (w_H W) mem) SHADOW_OFF cfgp 40.
Definition rn_now (B : asyms) (regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world trasegs) (mem : word -> option byte) (md : Model) (fpos res : Z) (ly3 : alayout) (S3 : astate) (W3 : world trasegs) (ms3 : machine_state) (md3 : Model) (k : Z) : Prop :=
ajournal trasegs B TRAWNEW_STK (spZ regs) [] ly S W mem md [(2, fpos)] ly3 S3 W3 (ms_mem ms3) md3 k /\ k <= 2 /\
frames S3 = (2, fpos) :: frames S /\ ablocks B ly3 S3 = ablocks B ly S ++ [(res, 48)] /\ 4096 <= res /\
aftok [] (ablocks B ly S) (res, 48) /\
(forall blc lyq ownq i, In (res, 48) blc -> 0 <= i < 48 -> awr_byte TRAWNEW_STK (spZ regs) [] (ablocks B ly S) blc lyq ownq (res + i)).
Definition rn_post (B : asyms) (regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world trasegs) (mem : word -> option byte) (md : Model) (g pgct rattr Wd Hd sgct loops : Z) : world trasegs -> config -> Prop :=
apost_base B TRAWNEW_STK [] regs ly S W mem md EV_RAWNEW
(fun ly' S' W' regs' mem' md' => exists res : Z, getr regs' 10 = w64 res /\
((res = 0 /\ Permutation (ablocks B ly' S') (ablocks B ly S)) \/
(res <> 0 /\ sgct <= 256 /\
Permutation (ablocks B ly' S') ((res, RAW_SIZE) :: ablocks B ly S) /\
(forall blc i, In (res, RAW_SIZE) blc -> 0 <= i < RAW_SIZE ->
awr_byte TRAWNEW_STK (spZ regs) [] (ablocks B ly S) blc ly' [] (res + i)) /\
aftok [] (ablocks B ly S) (res, RAW_SIZE) /\
obj_at trasegs (mrestrict (w_H W') mem') res LAY_Raw [A_cgif_writecb; g; pgct; rattr; Wd; Hd; sgct; loops; R_PENDING]))).
Lemma rn_E_havoc : forall E0 E pgct rattr Wd Hd sgct loops ctx F FL res N vs,
(66 <= N)%nat -> rn_E E0 E pgct rattr Wd Hd sgct loops ctx F FL res -> rn_E E0 (havoc E N vs) pgct rattr Wd Hd sgct loops ctx F FL res.
Proof.
intros E0 E pgct rattr Wd Hd sgct loops ctx F FL res N vs HN (AG & H).
unfold rn_E. rewrite !ew_havoc_old by lia. split; [|exact H]. intros n Hn. rewrite ew_havoc_old by lia. apply AG. exact Hn.
Qed.
Lemma rn_E_ewset : forall E0 E pgct rattr Wd Hd sgct loops ctx F FL res n w,
(66 <= n)%nat -> rn_E E0 E pgct rattr Wd Hd sgct loops ctx F FL res -> rn_E E0 (ewset E n w) pgct rattr Wd Hd sgct loops ctx F FL res.
Proof.
intros E0 E pgct rattr Wd Hd sgct loops ctx F FL res n w HN (AG & H).
unfold rn_E. rewrite !ew_ewset_other by lia. split; [|exact H]. intros m Hm. rewrite ew_ewset_other by lia. apply AG. exact Hm.
Qed.
Definition rn_from (B : asyms) (ss : sstate) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (cfgp g pgct rattr Wd Hd sgct loops ctx : Z) rest (cid pos : Z)
(E0 E : env) W3 ly3 S3 (ms3 : machine_state) md3 (k fpos res : Z),
afn_pre trasegs B TRAWNEW_STK ly S W regs mem md ch -> spZ regs mod 32 = 0 ->
arodata_ok B (aview trasegs (w_H W) mem) ->
rn_cfg B ly S W mem cid pos cfgp ->
obj_at trasegs (mrestrict (w_H W) mem) cfgp LAY_RawConfig [A_cgif_writecb; g; pgct; rattr; Wd; Hd; sgct; loops] ->
Permutation (ablocks B ly S) ((g, CGIF_SIZE) :: rest) ->
vev S + EV_RAWNEW <= VEV_MAX ->
rn_E0 regs cfgp g E0 -> rn_E E0 E pgct rattr Wd Hd sgct loops ctx (frame_addr ly 2 fpos) (flag_addr ly 2 fpos) res ->
rn_now B regs ly S W mem md fpos res ly3 S3 W3 ms3 md3 k ->
sgct <= 256 ->
st_ok trasegs E ss (restrict (w_H W3) ms3) ->
SRr trasegs W3 (mkCfg ms3 md3) (rn_post B regs ly S W mem md g pgct rattr Wd Hd sgct loops).
Section RN.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL.
Lemma rn_entry : forall W ly S regs mem md ch cfgp g pgct rattr Wd Hd sgct loops ctx rest,
afn_pre trasegs B TRAWNEW_STK ly S W regs mem md ch -> spZ regs mod 32 = 0 ->
arodata_ok B (aview trasegs (w_H W) mem) ->
getr regs 10 = w64 cfgp ->
afobj B ly S W mem cfgp 40 ->
obj_at trasegs (mrestrict (w_H W) mem) cfgp LAY_RawConfig [A_cgif_writecb; g; pgct; rattr; Wd; Hd; sgct; loops] ->
Permutation (ablocks B ly S) ((g, CGIF_SIZE) :: rest) ->
val_mem trasegs (mrestrict (w_H W) mem) (g + 56) 8 A_writecb ->
val_mem trasegs (mrestrict (w_H W) mem) (g + 64) 8 ctx -> 0 <= ctx < 2 ^ 64 ->
val_mem trasegs (mrestrict (w_H W) mem) (g + 80) 8 0 ->
st_ok trasegs (Ereg regs (rn_extra g pgct rattr Wd Hd sgct loops ctx)) ss_rn0
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_cgif_raw_newgif) mem (seg_rom trasegs))).
Proof.
intros W ly S regs mem md ch cfgp g pgct rattr Wd Hd sgct loops ctx rest HPRE Hal32 HROD H10 HFO Hcfg HPerm Mgw Mgf Rctx Mg80.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (FFS : TRAWNEW_STK = 16576) by reflexivity.
destruct HFO as ((cid & pos & Hfin & Hcid0 & Hfal & Hflo & Hfhi) & Hcal & HRA).
destruct (frames_bounds trasegs B LAWS ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Hfhigh).
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR Hfin) as Hfhigh_img.
assert (Hing : In (g, CGIF_SIZE) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS ly S W mem md g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & _ & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_img _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in *.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell. rewrite HBguar, HBuar in Kguar. rewrite HBuar in Kuar.
pose proof Hcfg as Hcfg'. cbn [obj_at LAY_RawConfig] in Hcfg'.
destruct Hcfg' as ([V0 _] & [V8 R8] & [V16 R16] & [V24 R24] & [V28 R28] & [V30 R30] & [V32 R32] & [V34 R34] & _).
cbn [fst snd N.to_nat Z.of_N] in V0, V8, V16, V24, V28, V30, V32, V34, R8, R16, R24, R28, R30, R32, R34.
change (2 ^ (8 * 8)) with (2 ^ 64) in *. change (2 ^ (8 * 4)) with (2 ^ 32) in *. change (2 ^ (8 * 2)) with 65536 in *.
rewrite restrict_mkst_fx.
set (E := Ereg regs (rn_extra g pgct rattr Wd Hd sgct loops ctx)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 cfgp) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (EX : forall j, ew E (32 + j) = nth j (rn_extra g pgct rattr Wd Hd sgct loops ctx) (Z_to_bv 64 0)) by (intros j; subst E; apply ew_Ereg_extra).
pose proof (EX 0%nat) as E32. pose proof (EX 1%nat) as E33. pose proof (EX 2%nat) as E34. pose proof (EX 3%nat) as E35.
pose proof (EX 4%nat) as E36. pose proof (EX 5%nat) as E37. pose proof (EX 6%nat) as E38. pose proof (EX 7%nat) as E39. pose proof (EX 8%nat) as E40.
cbn [Nat.add nth rn_extra map] in E32, E33, E34, E35, E36, E37, E38, E39, E40. clear EX.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
Local Ltac ck HE M := eapply chunk_ok_val; [ cbn [sv_denot]; rewrite HE, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | first [exact M | rewrite Z.add_0_r; exact M] ].
unfold ss_rn0. apply (entry_st_ok_full trasegs); change (Ereg regs (rn_extra g pgct rattr Wd Hd sgct loops ctx)) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold rn_regions0, stack_region, got_region, bcell_region, uar_got_region, uar_cell_region, const8_region, cfg_region, g_region.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks].
+ cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable trasegs). apply Hpres. lia.
+ cbn [base_val]. unfold A_GOT_shadow. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 663904) at 1.
apply (chunk_ok_val trasegs E _ 0 663904 8 (SLit A_shadow_glob) A_shadow_glob); [reflexivity | unfold A_shadow_glob; zside | zside |].
exact (val_mem_of_rdword trasegs (w_H W) mem _ _ Kgot).
+ cbn [base_val]. unfold A_shadow_glob. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 696760) at 1.
apply (chunk_ok_val trasegs E _ 0 696760 8 (SOff 35 0) SB);
[cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
exact (val_mem_of_rdword trasegs (w_H W) mem _ _ Kcell).
+ cbn [base_val]. unfold A_GOT_uar. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 663992) at 1.
apply (chunk_ok_val trasegs E _ 0 663992 8 (SLit A_uar_glob) A_uar_glob); [reflexivity | unfold A_uar_glob; zside | zside |].
exact (val_mem_of_rdword trasegs (w_H W) mem _ _ Kguar).
+ cbn [base_val]. unfold A_uar_glob. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 696768) at 1.
apply (chunk_ok_val trasegs E _ 0 696768 4 (SLit 1) 1); [reflexivity | zside | zside |].
exact (val_mem_of_rd32 trasegs (w_H W) mem _ _ Kuar).
+ cbn [base_val]. unfold A_GOT_rawnew. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 667104) at 1.
apply (chunk_ok_val trasegs E _ 0 667104 8 (SLit A_cgif_raw_newgif) A_cgif_raw_newgif); [reflexivity | unfold A_cgif_raw_newgif; zside | zside |].
eapply (arodata_val8 B (w_H W) mem 667104 A_cgif_raw_newgif TL HROD); [lia | lia | intros x Hx; unfold lib_const_addr; lia |].
intros k Hk. do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
+ rewrite (VB 10%nat cfgp E10) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [apply (chunk_ok_val trasegs E _ cfgp 0 8 _ A_cgif_writecb); [reflexivity | unfold A_cgif_writecb; zside | zside | exact V0]|].
constructor; [ck E32 V8|]. constructor; [ck E33 V16|]. constructor; [ck E34 V24|]. constructor; [ck E36 V28|].
constructor; [ck E37 V30|]. constructor; [ck E38 V32|]. constructor; [ck E39 V34|]. constructor.
+ rewrite (VB 32%nat g E32) by lia. unfold CGIF_SIZE. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [apply (chunk_ok_val trasegs E _ g 56 8 _ A_writecb); [reflexivity | unfold A_writecb; zside | zside | exact Mgw]|].
constructor; [ck E40 Mgf|].
constructor; [apply (chunk_ok_val trasegs E _ g 80 8 _ 0); [reflexivity | zside | zside | exact Mg80] | constructor].
- apply pairwise_disjoint_of_extents.
unfold rn_regions0, stack_region, got_region, bcell_region, uar_got_region, uar_cell_region, const8_region, cfg_region, g_region, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi]. rewrite (VB 10%nat cfgp E10), (VB 32%nat g E32) by lia. cbn [base_val]. rewrite Usp.
unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rawnew, CGIF_SIZE.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
assert (Hgf : g + 96 <= cfgp \/ cfgp + 40 <= g).
{
pose proof (sep_block_frame trasegs B LAWS ly S W mem md g CGIF_SIZE cid pos HAR Hing Hfin) as Hbf.
unfold zdisjoint in Hbf. cbn [fst snd] in Hbf. change (req_size CGIF_SIZE) with 96 in Hbf. lia. }
revert Hslo Hshi H47 Hceil Hgceil Hgh Hgh_img Hg4096 Hfceil Hfhigh Hfhigh_img Hflo Hfhi Hgf C1 C3 FFS Hstk0. clear. unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros. repeat split; lia.
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok rn_atoms0]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E32, E33, E34, E35, E36, E37, E38, E39, E40, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 5) with 32. change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
assert (Hc8 : cfgp mod 8 = 0) by exact Hcal.
revert Hslo Hshi H47 Hceil Hgceil Hgh Hgh_img Hg4096 Hg16 Hfceil Hfhigh Hfhigh_img Hflo Hfhi Hal32 Hc8 R8 R16 R24 R28 R30 R32 R34 Rctx C1 C3 FFS Hstk0. clear. unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros.
repeat match goal with |- _ /\ _ => split end; lia.
Qed.
End RN.
End a.
