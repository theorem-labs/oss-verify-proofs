(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require As0Gc3. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require As0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.boost_json.fuzz_parse.images Require Import Asan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib SymDriveH4 SymAux.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import AsShadow AsPrintfFirst AsSxKit AsStdioCall.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_AsTail_usage_defs () := KReplay.lz_vm "#$BnI47Corelib4Init9Datatypes4list00K89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX24expr02C13~~~K!t5+7Numbers7BinNums8positive02!sKG1!sK=1Z03!t}c1!t}&!smb3!ulC1Z02!t3]8sidecond!t~+!x4A1!sFB2!xt25Logic2eq00!s@83and00K!s[;1K!s[<1!z-=prod00C!sF;3fst!sC=sndC!vm\5s_log!vh%!sl^carry!sl&7!slN6SymAux;log_covered!sl%I!y7f0!y7Cbool!}1#ELinuxProcessSemantics5Riscv5Instr;branch_!s~$5!sXG5aluop06!sRN!zi=3nat!~]?!#3&+3I!udA0!v+B1!w?]9sym_state!w@'!sr]7scripts!sp'c!spO2AsAAsTail_usage_defs2rB!sqk4scsB!uXc6kentry!uWm4knV!ssl:ot_regions!wGmC!wGoC!vVnC!y|nD!u[o!ssl3knC!#5dA!#3j#2!#><b4!t4&!#9A\sadd!#?se!#8U+6!uo'!#85Q3!#@Q?1!yCgE!yCoE!{xnE0!wFc!x}%7!wBZ6!sXT1!sXT4!x0gF!x0o!ssl5knF0_!#3CkrF!#5wk5!u]#0!u^p!#7cmG!x<oG!}FnG!u[nH!u[oH!u[nH0!zpn4!zpp4!zpo4!u^nG!u^pG!u^oG!u^oH!u^pH!u^oH!u^m4rFs1!ssk6!zw#!sum!zx#s!u`p2!u`q!sum!u`#2!uap3!uaq3!uap3!#4>ns!#4>os!#4>ns!#4>n!u^pH!u^oH!}\oG3s!zyo!suoknG3!uaoH!uaqH!uapH!ua+!#`o;6option!#nv^!#]'&!#S9&!sod1!sok5!sok7!sok!#X8V2As;AsStdioCall9s!s0#_res!#o3C!xK'!#o5=!#m[#1C!t^^:!t^%call!vDk!#='%!#mq\4s_pc!{`3!#Z-50!#ea\!#WQ$!#X@&!#kvL:!sRN7I!y>i!ttU2!#5reARIP!#4{j7AMEMCPY!svk3rI!#6gk<ASTDIO_WRIT!#_5k8AMAINEPI!swk4rI!#9Rl4s!#@Zm4kn!#AOoOF!stn!#@Zn5!#?c#!u`n!stp!#@Yn5!#?b#!u`n!stn;ASTRNLEN_TR!szk2rI!#4HlG3!srmH!srnI!sro!#YBk3s!#bzl3kn!#cnnO!#lVm!y+n4kn!ssnsc!sso!zon4knH!u]o!sso!#h8m4kn!ssnsc!sso!#eWm!x<#!u]o!ss'".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc4listhc4conshc3nil89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Ash1AsTail_usage_defs4FPX1~~~~~~k85AEXITk88AMAINEPIk87AMEMCPYk84ARIPk8cASTDIO_WRITEk8bASTRNLEN_TRhc3nat37Corelib4Init7Decimaltc2D0tc2D2tc3Nil37Corelib4Init3Nathg2bof_num_uint37Corelib4Init6Numberhi3bUIntDecimal79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymExec23SX2~~~~~~hk77scriptshc4boolhk73SCRhk74exprhc4prodhk79sym_statehk78sidecondhc4truek85FUELTk85STOPThk78sym_exec69OSSVerifyaboost_jsonafuzz_parse6images4Asan1M~~~~~~huafloaded_segmentshk76kentryhc3fsthk75carryhk75s_log79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsbAsStdioCall~~~~~~il49stdio_reshk74ELithc6optionil44SCR_il4astdio_call37Corelib5Lists7ListDefis93map04Npos69OSSVerify6Proofsaboost_jsonafuzz_parse3libcRefMemcpyLib~~~~~~iudbcallee_kepthk74ridx35stdpp9bitvectorbdefinitionsjk32bv46Stdlib5Arith8PeanoNat3Natjm63eqbhc4negbhc3orbk87KEPT_MC36Stdlib5Lists4Listjpf6filteriudccallee_saved3h5LinuxProcessSemantics5Riscv5Instrjsc7ALU_ADDhk74EAluhk74EVarhc5falseis93nthhg23addis93seqk88rip_clobk83spxk83FMThc4pairjsc7ALU_ANDjsc7ALU_SRLhk72SAhk75KWordhc3appk85OT_FRhk74KImghk76KRangehk73KWr79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As0d1A1s1P1r1i1n1t1f1F1i1r1s1t~~~~~~kp28kn_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AsShadow~~~~~~kuf7AAPP_HIkuf6AHI_LO79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AsSxKit~~~~~~lk24shknk89OT_SHOFFSk88ot_cellshk76KAlign46Stdlib6ZArith6BinInt1Zlq83subhk75saddrjsc5aluopjsc5mulopk82PXk8cnot_px_rangek8aOT_SHOFFS2k86OT_SHXk88px_rangek85shxknk84knV0k84srV0hk72SShk76sentryhk72SEk8bAMEMCPY_RETk84knC0k84srC0k83knCk84srD0k8cASTRNLEN_RETk84knE0k84srE0k85knF0_k84srF0k84knG0k84srG0k84knH0k84srH0k84knI0k84srI0k85knG30il46sc_retk85knH30k84scG3k85srH30k85knI30k85srI30k85knF40k85knG40k84scF4k85srG40k85knH40k85srH40k85knI40k85srI4069OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SymAux~~~~~~nja7sregion37Corelib4Init5Logicnne2eqk82rBhc3sndnne3andk8aot_regionsk84scsBnjablog_coveredk82rCk84scsCk82rDk84scsDk82rEk84scsEk82rFk84scsFk83rF0k85knF00k85scsF0k82rGk84scsGk82rHk84scsHk83rF4k85scsF4k83rG4k85scsG4k83rH4k85scsH4k84rFs1k85knFs0k86scsFs1k84rFs2k86knFs20k86scsFs2k84rFs3k86knFs30k86scsFs3k83rGsk85knGs0k85scsGsk83rHsk85knHs0k85scsHsk84rG3sk86knG3s0k86scsG3sk84rH3sk86knH3s0k86scsH3shk74s_pchc4Somek85knG3sk85knH3sk84knHsk84rI3sk83rIsk85scG3sk85scH3sk85scOFsk85srG3sk85srH3sk84srHsk84knF4k84knG3k83knHk84knH3k84knH4k83rG3k83rH3k82rIk83rI3k83rI4k84scH3k84scH4k84scOFk84srF4k84srG3k83srHk84srH3k84srH4" s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.
Open Scope Z_scope.

Abbreviation RSEGS := Asan.M.loaded_segments.

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition AMEMCPY : Z := 0x1a5624.          (* [comment removed for export] *)
Definition AMEMCPY_RET : Z := 0x902d4.       (* [comment removed for export] *)
Definition ASTRNLEN_TR : Z := 0x7a180.       (* [comment removed for export] *)
Definition ASTRNLEN_RET : Z := 0x7a5e4.      (* [comment removed for export] *)
Definition ASTDIO_WRITE : Z := 0x19bde8.
Definition AEXIT : Z := 0x1944fc.
Definition AMAINEPI : Z := 0xbeb1c.          (* [comment removed for export] *)
Definition ARIP : Z := 0x92804.              (* [comment removed for export] *)
Definition STOPT : ltac2:(zQ "20!j4!h9@1$0$1") := ltac2:(zQ "90!h9!jb!k2!p5!pd!q8!r2!r9!s8@3$1$0$5@3$1$0$8@3$1$0$7@3$1$0$3@3$1$0$4@3$1$0$6@1$2$0").
Definition FUELT : nat := 20000.
Definition scr0 : ltac2:(zQ "10!ho6$0") := ltac2:(zQ "40!k2!hp1!hp8!hpf@3$2@1$0$1@1$0$3@1$0$1").
Definition runT : ltac2:(zQ "50!hq7!ho6!hqe!j4!hrb>3scr$1>2ss$2@2$0@2$0$2@1$3$4$1") := ltac2:(zQ "90!k2!hs7!hse!ht6!ho6!hrb!hte!hqe!ihf\3scr$4\2ss$7@7$6$8$2$1$3^2^1@1$0$5").
Definition kn_afterT : ltac2:(zQ "60!j4!hq7!ij2!ho6!hrb!hqe>1r@2$1@2$1$5@1$0$4$3>2kn@1$0$2@1$0$2") := ltac2:(zQ "b0!j4!hrb!ijc!hq7!ij2!hqe!hp1!ho6!k2!ik2!ikb\1r@2$3@2$3$5@1$0$1$7\2kn@1$0$4@3$2@1$0$4@1$0$1@3$2@2$3@1$0$4@1$0$1@1$0$6@3$9@1$a@3$2$5@1$0$1@3$2@2$3$5@1$0$1$7^2^1@1$8$6").
Definition sc_of : ltac2:(zQ "50!j4!t6!ip5!hpf!ij2>2nv$1>2sr@1$0$3>2kn@1$0$4$2") := ltac2:(zQ "a0!iq2!ip5!j4!k2!iqa!hpf!ij2!t6!ir3!irb\2nv$7\2sr@1$2$5\2kn@1$2$6M4\1x@1$4$1$1@3$9^3^2^1\1r$1^1@c$8ZZZ@1$0Z@1$0Z@1$0Z@1$0Z@1$0Z@1$0Z@1$0Z@1$3$5@1$3$6").
Definition KEPT_MC : ltac2:(zQ "20!j4!t6@1$0$1") := ltac2:(zQ "60!t6!iu0!iu7!jic!jjb!jm0@4$1@1$5@1$2#5$0$4$3").     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition KEPT_MCI : ltac2:(zQ "20!j4!t6@1$0$1") := ltac2:(zQ "60!t6!jo1!jo8!jof!jp5!jr2@3$5$0\1i$0@1$2@2$3@2$1^1Nh3@2$1^1Nh4$4").
Definition KEPT_CS : ltac2:(zQ "20!j4!t6@1$0$1") := ltac2:(zQ "60!t6!iu0!iu7!jrc!jjb!jm0@4$1@1$5@1$2#5$0$4$3").    (* [comment removed for export] *)
Definition spx : ltac2:(zQ "20!h9!hpf>1k$0$1") := ltac2:(zQ "50!h9!jv0!jvb!iq2!kg3\1k$0@3$2$1@1$4N0@1$3^1").
(* [comment removed for export] *)
Definition rip_clob (i : nat) : bool :=
  match i with 5 | 11 | 12 | 13 | 14 | 15 | 16 | 17 => true | _ => false end%nat.
Definition after_rip : ltac2:(zQ "30!j4!hpf!t6>4base$2>2sr@1$0$1@1$0$1") := ltac2:(zQ "b0!t6!hpf!iq2!kh3!hp1!j4!kha!iu0!ki1!ki8!kg3\4base$0\2sr@1$5$1@4$7$0$1\1i$0M4\0$4$1@1$9^1@1$a@2$6^3^1M0\1i$0$1^1@4$3$1^1^2@1$2Z\1n$0M0\1n$0$1^1@4$3$1^2^3@1$2Z\2n0$0M0\2n0$0$1^1@4$3$1^3^4@1$2Z\2n1$0M0\2n1$0$1^1@4$3$1^4^5@1$2Z\2n2$0M0\2n2$0$1^1@4$3$1^5^6@1$2Z\2n3$0M0\2n3$0$1^1@4$3$1^6^7@1$2Z\2n4$0M0\2n4$0$1^1@4$3$1^7^8@1$2Z\2n5$0M0\2n5$0$1^1@4$3$1^8^9@1$2Z\2n6$0M0\2n6$0$1^1@4$3$1^9^a@1$2Z\2n7$0M0\2n7$0$1^1@4$3$1^a^b@1$2Z\2n8$0M0\2n8$0$1^1@1$2Z\2n9$0@4$3$1^c^d@1$2Z@2$8N0Ni0").
Definition RIP_FR : Z := 80.
Definition OT_FR : Z := 6000.                (* [comment removed for export] *)
Definition FMT : Z := 0x16ddc.
Definition NPRE : Z := 7.
Definition NSUF : Z := 7.                (* [comment removed for export] *)
Definition IHI : Z := 0x80000000.            (* [comment removed for export] *)
Definition BUF_LO : Z := (-592).
Definition BUF_HI : Z := (-512).
Definition PX : ltac2:(zQ "10!hpf$0") := ltac2:(zQ "10!kg3@1$0Nod").            (* [comment removed for export] *)

(* [comment removed for export] *)
Definition srV0 : ltac2:(zQ "20!j4!hpf@1$0$1") := ltac2:(zQ "90!t6!hpf!kha!kg3!iq2!kj3!kj9!iu0!ki1@4$7$0$1\1i$0M0\1i$0$1^1@1$4Z\1n$0M0\1n$0$1^1@1$4+nvho4\2n0$0M0\2n0$0$1^1@1$5-v0\2n1$0M0\2n1$0$1^1@1$3@2$2Ni3^4\2n2$0M0\2n2$0$1^1@1$4+mvkjt8\2n3$0M0\2n3$0$1^1@1$3@2$2Ni3^6\2n4$0M0\2n4$0$1^1@1$3@2$2Ni3^7\2n5$0M0\2n5$0$1^1@1$3@2$2Ni3^8\2n6$0M0\2n6$0$1^1@1$4$6\2n7$0M0\2n7$0$1^1@1$4+hrpvg8\2n8$0M0\2n8$0$1^1@1$4+hrpvg8\2n9$0M0\2n9$0$1^1@1$4$6\3n10$0M0\3n10$0$1^1@1$5-r0\3n11$0M0\3n11$0$1^1@1$3@2$2Ni3^e\3n12$0M0\3n12$0$1^1@1$3@2$2Ni3^f\3n13$0M0\3n13$0$1^1@1$3@2$2Ni3^h0\3n14$0M0\3n14$0$1^1@1$3@2$2Ni3^h1\3n15$0M0\3n15$0$1^1@1$3@2$2Ni3^h2\3n16$0M0\3n16$0$1^1@1$5-r0\3n17$0@1$3@2$2Ni3^h4@2$8N0Ni0").

(* [comment removed for export] *)
Definition ot_cells : ltac2:(zQ "40!hq7!h9!j4!t6@1$2@2$0@2$0$1$3$1") := ltac2:(zQ "60!h9!hq7!t6!kjf!jb!k2@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrnki0N8+hpstl4@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrnlp8N8+hqlmi4@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrnlq0N8+hqlqi8@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrnlk8N8+hqmhm8@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrnjt8N8+hqlli8@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hsgij8N8+nvvvogg0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hsgvh8N1+1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hsgvh9N1+1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+ilhtrcN1+1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+ilhum3N1+1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrpvg8N4+5@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrpvi8N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrpvj0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrpvk0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrpvl0N8+hprtu8@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrpvm0N8+nhkrv0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrpvm8N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrpvo0N4+2@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrpvp0N4Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrpvp4N4+vvvvvvvf@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrpvp8N4+vvvvvvvf@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nvvvqtr8N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nvvvqts0N8Z@1$5@2$1@2$1$0$2$0").

(* [comment removed for export] *)
Definition OT_SHOFFS : ltac2:(zQ "20!j4!h9@1$0$1") := ltac2:(zQ "30!h9!jb!k2@3$1$0-il0@3$1$0-ika@1$2$0").
Definition OT_SHOFFS2 : ltac2:(zQ "20!j4!h9@1$0$1") := ltac2:(zQ "30!h9!jb!k2@3$1$0-il0@3$1$0-ika@3$1$0-ik9@1$2$0").
Definition OT_SHX : ltac2:(zQ "20!j4!hpf@1$0$1") := ltac2:(zQ "90!jvb!iq2!jv0!kg3!hpf!jb!kk6!kl1!k2@3$5$4@3$0$6@3$0$2@3$0$7@3$0$2@3$0$2@1$3N2@1$3Nod@1$1-1@1$1+3@1$1+nvvvogg0@1$1-8@3$5$4@3$0$6@3$0$2@3$0$7@1$3N2@1$1+3@1$1+nvvvogg0@1$1-8@3$5$4@3$0$6@3$0$2@3$0$7@3$0$2@3$0$2@1$3N0@1$3Nod@1$1-ika@1$1+3@1$1+nvvvogg0@1$1-8@3$5$4@3$0$6@3$0$2@3$0$7@3$0$2@3$0$2@1$3N0@1$3Nod@1$1-ik9@1$1+3@1$1+nvvvogg0@1$1-8@3$5$4@3$0$6@3$0$2@3$0$7@3$0$2@3$0$2@1$3N0@1$3Nod@1$1-ik3@1$1+3@1$1+nvvvogg0@1$1-8@1$8$4").
Fixpoint shxkn (l : list expr) : list kentry :=
  match l with [] => [] | e :: r => KRange e 0x20000000000 0x10007fff8000 :: KZero (SA e 0) (ELit 8) :: shxkn r end.

Definition knV0 : ltac2:(zQ "20!j4!ij2@1$0$1") := ltac2:(zQ "h40!ij2!kg3!jb!klc!km2!iq2!kmb!kn1!kn9!ko1!kob!k2!ku3!lid!lj8!lnf!lo7!lp3!lpe!ls0@3$6$0@3$2$0@2$h2@1$1N0+h0@3$2$0@3$9@1$1N0+nvvvogggggg0+ogggggggggg0@3$2$0@2$a@2$3@1$1N0@2$h3-o0$7$7@3$2$0@3$9@1$1N2$e$d@3$2$0@2$8+hggg0+mngg0@3$2$0@2$8+hqtgg0+hrngg0@3$2$0@3$4@2$3@1$1N0-r0N8@1$1N2@3$2$0@3$4@2$3@1$1N0-r8N8@1$5+ruqt4@3$2$0@3$4@2$3@1$1N0-s0N8@1$1Nb@3$2$0@3$4@2$3@1$1N0-s8N8@1$1Nc@3$2$0@3$4@2$3@1$1N0-t0N8@1$1Nh5@3$2$0@3$4@2$3@1$5Z+nhkkh8N8@1$1N1@3$2$0@2$a@2$3@1$5Z+hrpvg8+u8@1$b$0@3$6$0@1$f$h0@1$c$h1").
(* [comment removed for export] *)
Definition not_px_range (k : kentry) : bool := match k with KRange (EVar 141) _ _ => false | _ => true end.
Definition px_range : ltac2:(zQ "30!j4!h9!ij2>2lo$1>2hi$1>2kn@1$0$2@1$0$2") := ltac2:(zQ "80!ij2!h9!jb!j4!lu2!lu7!ko1!jr2\2lo$1\2hi$1\2kn@1$3$0@3$2$0@3$6$4^3^2@3$7$0$5^1").
(* [comment removed for export] *)
Definition kn_readd : ltac2:(zQ "30!j4!h9!ij2>3plo$1>3phi$1>2kn@1$0$2@1$0$2") := ltac2:(zQ "90!ij2!kmb!h9!j4!lnf!lv6!mg3!mgc!mh7\3plo$2\3phi$2\2kn@1$3$0@3$7^3^2@3$1$0@1$8$6@3$1$0@1$4$5^1").

(* [comment removed for export] *)
Definition ssB0 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "50!k2!mhf!mi6!mid!mj3@5$3+hpstl4$2@1$0$4$1Nk3").
Definition rB := Eval vm_compute in runT (SCR [false] [] []) ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_afterT rB knV0.
(* [comment removed for export] *)
Definition logM1 : ltac2:(zQ "20!j4!mj3@1$0$1") := ltac2:(zQ "70!mj3!jb!iq2!kg3!klc!mjd!k2@3$1$0@3$5@2$4@1$3N0-ikaN1@1$2+i0@3$1$0@3$5@2$4@1$3N0-ikcN2@1$2+jqm5@3$1$0@3$5@2$4@1$3N0-il0N4@1$2+mnmhnjn5@1$6$0").
Definition knC0 : list kentry := Eval vm_compute in fst (fst (carry logM1 knB [])).
Definition srC0 : list expr := Eval vm_compute in sr_after_call_j srB KEPT_MC 67.
(* [comment removed for export] *)
Definition ssC0 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "60!k2!mk3!ml1!ml8!mid!mj3@5$4$1$3@1$0$5$2Nm3").
Definition rC := Eval vm_compute in runT (SCR [] [] []) ssC0.
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC)).
Definition knC : list kentry := Eval vm_compute in kn_afterT rC knC0.
Definition srD0 : list expr := Eval vm_compute in sr_after_call_j srC KEPT_MC 99.
(* [comment removed for export] *)
Definition ssD0 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "60!k2!mk3!mlf!mm5!mid!mj3@5$4$1$3@1$0$5$2No3").
Definition rD := Eval vm_compute in runT (SCR [] [] []) ssD0.
Definition srD : list expr := Eval vm_compute in s_regs (fst (fst rD)).
Definition knD : list kentry := Eval vm_compute in kn_afterT rD knC.
(* [comment removed for export] *)
Definition knE0 : list kentry := Eval vm_compute in kn_readd 0 131071 (kn_cut 0 (-1152 - 4400) (-1152) IHI knD).
Definition srE0 : list expr := Eval vm_compute in sr_after_call_j srD KEPT_CS 131.
(* [comment removed for export] *)
Definition ssE0 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "60!k2!mmc!mnb!mo2!mid!mj3@5$4$1$3@1$0$5$2Nq3").
Definition rE := Eval vm_compute in runT (SCR [false] [ELit 0] []) ssE0.
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
Definition knE : list kentry := Eval vm_compute in kn_afterT rE knE0.
Definition srF0 : list expr := Eval vm_compute in sr_after_call_j srE KEPT_MC 163.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FQMAX : Z := 64.
Definition knF0_ : list kentry := Eval vm_compute in px_range 1 FQMAX knE.
Definition ssF0 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "60!k2!mk3!mo9!mp1!mid!mj3@5$4$1$3@1$0$5$2Ns3").
Definition rF := Eval vm_compute in runT (SCR [true; false; true; false; false] [] []) ssF0.
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF)).
Definition knF : list kentry := Eval vm_compute in kn_afterT rF knF0_.
Definition knG0 : list kentry := Eval vm_compute in kn_readd 0 66 (kn_cut 0 (BUF_LO + NPRE) BUF_HI IHI knF).
Definition srG0 : list expr := Eval vm_compute in sr_after_call_j srF KEPT_MCI 195.
(* [comment removed for export] *)
Definition knF00 : list kentry := Eval vm_compute in px_range 0 0 knE.
Definition rF0 := Eval vm_compute in runT (SCR [false; true] [] []) (SS AMEMCPY_RET srF0 [] knF00 195).
Definition knF0' : list kentry := Eval vm_compute in kn_afterT rF0 knF00.
(* [comment removed for export] *)
Definition ssG0 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "60!k2!mk3!mp8!mpf!mid!mj3@5$4$1$3@1$0$5$2Nu3").
Definition rG := Eval vm_compute in runT (SCR [false] [] []) ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_afterT rG knG0.
Definition knH0 : list kentry := Eval vm_compute in kn_readd 0 66 (kn_cut 0 (BUF_LO + NPRE) BUF_HI IHI knG).
Definition srH0 : list expr := Eval vm_compute in sr_after_call_j srG KEPT_MC 227.
(* [comment removed for export] *)
Definition ssH0 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "60!k2!mk3!mq6!mqd!mid!mj3@5$4$1$3@1$0$5$2Nhg3").
Definition rH := Eval vm_compute in runT (SCR [] [] []) ssH0.
Definition srH : list expr := Eval vm_compute in s_regs (fst (fst rH)).
Definition knH : list kentry := Eval vm_compute in kn_afterT rH knH0.
Definition scOF : stdio_res := Eval vm_compute in sc_of 259 srH knH.
Definition srI0 : list expr := Eval vm_compute in sc_sr scOF.
Definition knI0 : list kentry := Eval vm_compute in sc_kn scOF.
(* [comment removed for export] *)
Definition ssI0 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "50!k2!mr4!mrb!mid!mj3@5$3+hpsunc$2@1$0$4$1Nhi3").
Definition rI := Eval vm_compute in runT (SCR [] [] []) ssI0.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition knG30 : list kentry := Eval vm_compute in kn_readd (66 + 1) (66 + NSUF) (kn_cut 0 (BUF_LO + NPRE) BUF_HI IHI knF).
Definition ssG30 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "60!k2!mk3!ms2!mpf!mid!mj3@5$4$1$3@1$0$5$2Nu3").
Definition rG3 := Eval vm_compute in runT (SCR [] [] []) ssG30.
Definition srG3 : list expr := Eval vm_compute in s_regs (fst (fst rG3)).
Definition knG3 : list kentry := Eval vm_compute in kn_afterT rG3 knG30.
Definition scG3 : stdio_res := Eval vm_compute in sc_of 227 srG3 knG3.
Definition srH30 : list expr := Eval vm_compute in sc_sr scG3.
Definition knH30 : list kentry := Eval vm_compute in sc_kn scG3.
(* [comment removed for export] *)
Definition ssH30 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "70!k2!msa!mt4!mtc!mu3!mid!mj3@5$5@1$1$3$4@1$0$6$2Nhg3").
Definition rH3 := Eval vm_compute in runT (SCR [] [] []) ssH30.
Definition srH3 : list expr := Eval vm_compute in s_regs (fst (fst rH3)).
Definition knH3 : list kentry := Eval vm_compute in kn_afterT rH3 knH30.
Definition scH3 : stdio_res := Eval vm_compute in sc_of 259 srH3 knH3.
Definition srI30 : list expr := Eval vm_compute in sc_sr scH3.
Definition knI30 : list kentry := Eval vm_compute in sc_kn scH3.
(* [comment removed for export] *)
Definition ssI30 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "50!k2!mub!mv3!mid!mj3@5$3+hpsunc$2@1$0$4$1Nhi3").
Definition rI3 := Eval vm_compute in runT (SCR [] [] []) ssI30.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition knF40 : list kentry := Eval vm_compute in px_range (66 + NSUF + 1) 131071 knE.
Definition ssF40 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "60!k2!mk3!mvb!mp1!mid!mj3@5$4$1$3@1$0$5$2Ns3").
Definition rF4 := Eval vm_compute in runT (SCR [true] [] []) ssF40.
Definition srF4 : list expr := Eval vm_compute in s_regs (fst (fst rF4)).
Definition knF4 : list kentry := Eval vm_compute in kn_afterT rF4 knF40.
Definition scF4 : stdio_res := Eval vm_compute in sc_of 195 srF4 knF4.
Definition srG40 : list expr := Eval vm_compute in sc_sr scF4.
Definition knG40 : list kentry := Eval vm_compute in kn_readd (66 + NSUF + 1) 131071 (sc_kn scF4).
(* [comment removed for export] *)
Definition ssG40 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "70!k2!msa!ng3!ngb!nh2!mid!mj3@5$5@1$1$3$4@1$0$6$2Nu3").
Definition rG4 := Eval vm_compute in runT (SCR [false] [] []) ssG40.
Definition srG4 : list expr := Eval vm_compute in s_regs (fst (fst rG4)).
Definition knG4 : list kentry := Eval vm_compute in kn_afterT rG4 knG40.
(* [comment removed for export] *)
Definition logNL : ltac2:(zQ "20!j4!mj3@1$0$1") := ltac2:(zQ "70!mj3!jb!iq2!kg3!klc!mjd!k2@3$1$0@3$5@2$4@1$3N0-ikaN1@1$2+a@3$1$0@3$5@2$4@1$3N0-ikcN2@1$2+lkl5@3$1$0@3$5@2$4@1$3N0-il0N4@1$2+lgkukpi0@1$6$0").
Definition knH40 : list kentry := Eval vm_compute in fst (fst (carry logNL knG4 [])).
Definition srH40 : list expr := Eval vm_compute in sr_after_call_j srG4 KEPT_MC 227.
(* [comment removed for export] *)
Definition ssH40 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "60!k2!mk3!nha!ni2!mid!mj3@5$4$1$3@1$0$5$2Nhg3").
Definition rH4 := Eval vm_compute in runT (SCR [] [] []) ssH40.
Definition srH4 : list expr := Eval vm_compute in s_regs (fst (fst rH4)).
Definition knH4 : list kentry := Eval vm_compute in kn_afterT rH4 knH40.
Definition scH4 : stdio_res := Eval vm_compute in sc_of 259 srH4 knH4.
Definition srI40 : list expr := Eval vm_compute in sc_sr scH4.
Definition knI40 : list kentry := Eval vm_compute in sc_kn scH4.
(* [comment removed for export] *)
Definition ssI40 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "50!k2!nia!nj2!mid!mj3@5$3+hpsunc$2@1$0$4$1Nhi3").
Definition rI4 := Eval vm_compute in runT (SCR [] [] []) ssI40.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition knFs0 : list kentry := Eval vm_compute in px_range (FQMAX + 1) (66 + NSUF) knE.
Definition rFs1 := Eval vm_compute in runT (SCR [true; false; true; false] [] []) (SS AMEMCPY_RET srF0 [] knFs0 195).
Definition srFs1 : list expr := Eval vm_compute in s_regs (fst (fst rFs1)).
Definition knFs1 : list kentry := Eval vm_compute in kn_afterT rFs1 knFs0.
(* [comment removed for export] *)
Definition RIPSP : Z := (-3376).
Definition srFs20 : list expr := Eval vm_compute in after_rip 195 srFs1.
Definition knFs20 : list kentry := Eval vm_compute in kn_readd (FQMAX + 1) (66 + NSUF) (kn_cut 0 (RIPSP - RIP_FR) RIPSP IHI knFs1).
(* [comment removed for export] *)
Definition rFs2 := Eval vm_compute in runT (SCR [false] [] []) (SS 0x90584 srFs20 [] knFs20 227).
Definition srFs2 : list expr := Eval vm_compute in s_regs (fst (fst rFs2)).
Definition knFs2 : list kentry := Eval vm_compute in kn_afterT rFs2 knFs20.
Definition srFs30 : list expr := Eval vm_compute in after_rip 227 srFs2.
Definition knFs30 : list kentry := Eval vm_compute in kn_readd (FQMAX + 1) (66 + NSUF) (kn_cut 0 (RIPSP - RIP_FR) RIPSP IHI knFs2).
(* [comment removed for export] *)
Definition rFs3 := Eval vm_compute in runT (SCR [] [] []) (SS 0x90680 srFs30 [] knFs30 259).
Definition srFs3 : list expr := Eval vm_compute in s_regs (fst (fst rFs3)).
Definition knFs3 : list kentry := Eval vm_compute in kn_afterT rFs3 knFs30.
(* [comment removed for export] *)
Definition knGs0 : list kentry := Eval vm_compute in kn_readd (FQMAX + 1) 66 (kn_cut 0 (BUF_LO + NPRE) BUF_HI IHI knFs3).
Definition srGs0 : list expr := Eval vm_compute in sr_after_call_j srFs3 KEPT_MCI 259.
Definition rGs := Eval vm_compute in runT (SCR [false] [] []) (SS AMEMCPY_RET srGs0 [] knGs0 291).
Definition srGs : list expr := Eval vm_compute in s_regs (fst (fst rGs)).
Definition knGs : list kentry := Eval vm_compute in kn_afterT rGs knGs0.
Definition knHs0 : list kentry := Eval vm_compute in kn_readd (FQMAX + 1) 66 (kn_cut 0 (BUF_LO + NPRE) BUF_HI IHI knGs).
Definition srHs0 : list expr := Eval vm_compute in sr_after_call_j srGs KEPT_MC 291.
Definition rHs := Eval vm_compute in runT (SCR [] [] []) (SS AMEMCPY_RET srHs0 [] knHs0 323).
Definition srHs : list expr := Eval vm_compute in s_regs (fst (fst rHs)).
Definition knHs : list kentry := Eval vm_compute in kn_afterT rHs knHs0.
Definition scOFs : stdio_res := Eval vm_compute in sc_of 323 srHs knHs.
Definition srIs0 : list expr := Eval vm_compute in sc_sr scOFs.
Definition knIs0 : list kentry := Eval vm_compute in sc_kn scOFs.
Definition rIs := Eval vm_compute in runT (SCR [] [] []) (SS 0x19ce7c srIs0 [] knIs0 355).
Definition knG3s0 : list kentry := Eval vm_compute in kn_readd (66 + 1) (66 + NSUF) (kn_cut 0 (BUF_LO + NPRE) BUF_HI IHI knFs3).
Definition rG3s := Eval vm_compute in runT (SCR [] [] []) (SS AMEMCPY_RET srGs0 [] knG3s0 291).
Definition srG3s : list expr := Eval vm_compute in s_regs (fst (fst rG3s)).
Definition knG3s : list kentry := Eval vm_compute in kn_afterT rG3s knG3s0.
Definition scG3s : stdio_res := Eval vm_compute in sc_of 291 srG3s knG3s.
Definition srH3s0 : list expr := Eval vm_compute in sc_sr scG3s.
Definition knH3s0 : list kentry := Eval vm_compute in sc_kn scG3s.
Definition rH3s := Eval vm_compute in runT (SCR [] [] []) (SS (sc_ret scG3s) srH3s0 [] knH3s0 323).
Definition srH3s : list expr := Eval vm_compute in s_regs (fst (fst rH3s)).
Definition knH3s : list kentry := Eval vm_compute in kn_afterT rH3s knH3s0.
Definition scH3s : stdio_res := Eval vm_compute in sc_of 323 srH3s knH3s.
Definition srI3s0 : list expr := Eval vm_compute in sc_sr scH3s.
Definition knI3s0 : list kentry := Eval vm_compute in sc_kn scH3s.
Definition rI3s := Eval vm_compute in runT (SCR [] [] []) (SS 0x19ce7c srI3s0 [] knI3s0 355).

(* [comment removed for export] *)
Definition ot_regions : ltac2:(zQ "20!j4!nn3@1$0$1") := ltac2:(zQ "b0!h9!ls7!hq7!jb!kjf!kn1!klc!k2!iq2!kg3!ls0@3$3@2$2$1$0@4$4$1$0@2$6@1$9N0@2$a-o0$5$5@3$3@2$2$1$0@4$4$1$0@2$6@1$8Z+hrpvg8+u8@1$7@2$2$1$0").
Definition scsB : list sidecond := Eval vm_compute in (snd (fst rB)).
Lemma factsB : ltac2:(zQ "h42!j4!hrb!ijc!hqe!hq7!hp1!np2!np8!ho6!k2!npd!nq3!ij2!ikb!hs7!mhf!nqa!nr7!nre!ik2&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_usage_defs ()) ["FPX1"] "p;1p;3p;4p;2g0000j14Tg000Pj1DTg001Wj10Tg002<j12Tg002aj1=Tg003?j16Tg004Fj3:Tg005Mj1@Tg005kj4?Tg0076j19Tg007Vj3>Tg0086j31Tg008Pj25Tg008kj27Tg009Ej4<Tg009`j28Tg00:@j33Tg00:]j3;Tg00;:j1CTg00<@j3BTg00=Fj2ATg00>LR0#4R1g00?Wg00@7g00@ig00AUg00BA#Dg00B`R2#0#0#2#0#2#0#0#0#0#=#63:%=2#63:%22#2#@#6C?%90R25>0R0;10A1122R3g00CER4g00CeR5;15R6'51710P3P617121745C<C<g00DER61861g00EQg00F[33R37;1g00Gf511g00I3#4R01801%44A3613#CR3g00J<%943B337;1=112g00KI/A3=145'5'5do"). Qed.
Definition scsC : list sidecond := Eval vm_compute in (snd (fst rC)).
Lemma factsC : ltac2:(zQ "h42!j4!hrb!ijc!hqe!hq7!hp1!np2!nsd!ho6!k2!npd!nq3!ij2!ikb!hs7!ml1!nqa!nt2!nre!ik2&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_usage_defs ()) ["FPX1"] "p;1p;3p;2p;4g0000j13Tg0076j18Tg0086j30Tg008Pj21Tg008kj27Tg009Ej46Tg009`j25Tg00:@j32Tg00:]j34Tg00;:j1;Tg00<@j3:Tg00=Fj29Tg00>LR0#3R1%80R0;00R2g00CER3g00CeR4;04R5,121710R6P2P5P61734C6C6g00DER61561g00EQg00L\32R5741g00Mg501g00I3#3R21521%33A2615#;R5g00O4%833:32741=010g00KI/95=034'1'1do"). Qed.
Definition scsD : list sidecond := Eval vm_compute in (snd (fst rD)).
Lemma factsD : ltac2:(zQ "h42!j4!hrb!ijc!hqe!hq7!hp1!np2!nt9!ho6!k2!npd!nq3!ij2!ikb!hs7!mlf!nqa!nte!nre!ik2&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_usage_defs ()) ["FPX1"] "p;1p;3p;2p;4g0000j13Tg0076j18Tg0086j30Tg008Pj21Tg008kj27Tg009Ej46Tg009`j25Tg00:@j32Tg00:]j34Tg00;:j1;Tg00<@j3:Tg00=Fj29Tg00>LR0#3R1%80R0;00R2g00CER3g00CeR4;04R5,121710R6P2P5P61734C6C6g00DER61561g00EQg00PA32R5741g00QL501g00I3#3R21521%33A2615#;R5g00RY%833:32741=010g00KI/95=034'1'1do"). Qed.
Definition scsE : list sidecond := Eval vm_compute in (snd (fst rE)).
Lemma factsE : ltac2:(zQ "h42!j4!hrb!ijc!hqe!hq7!hp1!np2!nu5!ho6!k2!npd!nq3!ij2!ikb!hs7!mnb!nqa!nua!nre!ik2&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1z (kr_t_AsTail_usage_defs ()) ["FPX1"] "##,,p;1p;3p;4p;2g0000j14Tg00Sej10Tg000Pj1;Tg003?j1GTg00TDj3BTg005kj4ATg004Fj3@Tg00UKj2>Tg00VSj4=Tg0076j17!s/$Vj3<Tg0086j32!s/$Pj26!s/$kj25Tg009Ej48!s/$`j29Tg00:@j33!s/$]j3:Tg00;:j1FTg00<@j3DTg00=Fj2ETf0R0#0#0p=C%0!s0$!s$,p=?!s:4!s$3p=1g00>LR0#4R1g00?WR2g00W^g00AUR3g00BA#0R4#0R5#0#C#?#1!s$2;R6g00XPR7#GR83BP6CA%;5=@36/>7P4P2P8C=%70R85<05<0R0;20A2188!t;$CER4g00CeR7;27R6'61510P2P615181547C8C8g00DER61961g00EQg00Xn33R27:1g00Z9521g00I3#4R01901%44A3612#F!t4$[F%743D337:1=218g00KI/E2=247'6'6do"). Qed.
Definition scsF : list sidecond := Eval vm_compute in (snd (fst rF)).
Lemma factsF : ltac2:(zQ "h42!j4!hrb!ijc!hqe!hq7!hp1!np2!nv1!ho6!k2!npd!nq3!ij2!ikb!hs7!mo9!nqa!nv6!nre!ik2&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1z (kr_t_AsTail_usage_defs ()) ["FPX1"] "##-^p;1p;3p;4p;2g0000j19Tg000Pj1=Tg001Wj13Tg002<j17!s/$aj1DTg003?j1:Tg004Fj36Tg00Sej10Tg005kj45Tg00\Sj4ETg00TDj3CTg0076j1B!s/$Vj34Tg0086j32!s/$Pj2;!s/$kj28Tg009Ej4@!s/$`j2ATg00:@j3<!s/$]j3?Tg00;:j1ITg00<@j3HTg00=Fj2GTf0R0#0#0p=>%0!s0$!s$,p=F!s:4!s$3p=1g00>LR0#9R1g00?WR2g00@7R3g00@iR4g00AUR5g00BAR6#=R7g00B`R8#3#3#7!s+0D#:R936R:%D8#:R836%>6R;#>R<#0#F#1!s$2=R=C5P2P3%=;R;=648P=C5g00CeR8g00]ZP;A657==659C5P2g00^LP:P;C5P8g00_>P8P6P<P=CEg00XP#:R<9C5==C5<C5%B0R<540!s%/R0;20A21<<!uK$CER=?288R6';1810P5P6181<18=8C@C@g00DER61A61g00EQg00`03<R57?1g00a;521g00I3#9R01A01%9=A<615#I!t-$bH%B=3H3<7?1=21<g00KI/G5=2=8';';do"). Qed.
Definition scsF0 : list sidecond := Eval vm_compute in (snd (fst rF0)).
Lemma factsF0 : ltac2:(zQ "h42!j4!hrb!ijc!hqe!hq7!hp1!np2!nvd!ho6!k2!npd!nq3!ij2!ikb!hs7!og3!nqa!ogb!nre!ik2&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1z (kr_t_AsTail_usage_defs ()) ["FPX1"] "##,Ap;1p;3p;4p;2g0000j16Tg000Pj1:Tg00Sej10Tg004Fj37Tg001Wj12Tg002<j15!s/$aj1CTg003?j1BTg005kj4<Tg0076j1;!s/$Vj3@Tg0086j33!s/$Pj28!s/$kj29Tg009Ej4>!s/$`j2?Tg00:@j34!s/$]j3=Tg00;:j1FTg00<@j3ETg00=Fj2DTf0R0#0#0p=A%0!s0$!s$,p=G!s:4!s$3p=1g00>LR0#6R1g00CeR2g00]Zg00BAR3#AR4#:R5g00AUR6%:3R3%04#A#G#1!s$2:576g00B`#2#2#5!s+0C#BR437C<g00?Wg00^LA7634P5C<%;0R55@05@0R0;30A3155R4g00CER3?322R6'81910P4P619151932C>C>g00DER61?61g00EQg00cV34R47!uN$db531g00I3#6R01?01%63A4614#F!t-$f0%;33E347=1=315g00KI/D4=332'8'8do"). Qed.
Definition scsG : list sidecond := Eval vm_compute in (snd (fst rG)).
Lemma factsG : ltac2:(zQ "h42!j4!hrb!ijc!hqe!hq7!hp1!np2!oh3!ho6!k2!npd!nq3!ij2!ikb!hs7!mp8!nqa!oh8!nre!ik2&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1z (kr_t_AsTail_usage_defs ()) ["FPX1"] "##,Fp;1p;3p;4p;2g0000j1:Tg000Pj1?Tg00Sej10Tg004Fj36Tg001Wj13Tg002<j14!s/$aj1<Tg003?j15Tg005Mj1B!s/$kj4ATg0076j1@!s/$Vj3GTg0086j32!s/$Pj27!s/$kj29Tg009Ej4>!s/$`j2=Tg00:@j38!s/$]j3;Tg00;:j1ETg00<@j3DTg00=Fj2FTf0R0#!s$&p=C%0!s4+!s:'H!s:4!s$3p=1g00>LR0#:R1g00?Wg00@7g00@ig00AUR2g00BAR3#?%03#C#H#1!s$2?56!sK$`R2#3#3#4!s+0<#536%<2!s,$42#4#B#5CA%@0R25G0R0;20A2122R3g00CER4g00CeR5;25R6'71910P3P619121945C>C>g00DER61=61g00EQg00g>38R37;1g00hI521g00I3#:R01=01%:4A8613#E!t4$iV%@43D387;1=212g00KI/F3=245'7'7do"). Qed.
Definition scsH : list sidecond := Eval vm_compute in (snd (fst rH)).
Lemma factsH : ltac2:(zQ "h42!j4!hrb!ijc!hqe!hq7!hp1!np2!ohf!ho6!k2!npd!nq3!ij2!ikb!hs7!mq6!nqa!oi4!nre!ik2&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_usage_defs ()) ["FPX1"] "p;1p;3p;2p;4g0000j13Tg0076j18Tg0086j30Tg008Pj21Tg008kj27Tg009Ej46Tg009`j25Tg00:@j32Tg00:]j34Tg00;:j1;Tg00<@j3:Tg00=Fj29Tg00>LR0#3R1%80R0;00R2g00CER3g00CeR4;04R5,121710R6P2P5P61734C6C6g00DER61561g00EQg00jc32R5741g00kn501g00I3#3R21521%33A2615#;R5g00m;%833:32741=010g00KI/95=034'1'1do"). Qed.
Definition scsF4 : list sidecond := Eval vm_compute in (snd (fst rF4)).
Lemma factsF4 : ltac2:(zQ "h42!j4!hrb!ijc!hqe!hq7!hp1!np2!oib!ho6!k2!npd!nq3!ij2!ikb!hs7!mvb!nqa!oj1!nre!ik2&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1z (kr_t_AsTail_usage_defs ()) ["FPX1"] "##+_p;1p;4p;3p;2g0000j13Tg00Sej10Tg000Pj1DTg00\Sj4CTg003?j1?Tg00TDj38Tg005kj4>Tg0076j17!s/$Vj3<Tg0086j32!s/$Pj26!s/$kj24Tg009Ej4;!s/$`j2:Tg00:@j35!s/$]j39Tg00;:j1BTg00<@j3@Tg00=Fj2ATf0R0#!s$&p=E%0!s4+!s:'=!s:4!s$3p=1g00>LR0#3R1g00CeR2g00_>P2g00BAR3%E3R3%03#=#1!s$2DR3CCg00AUR4g00XP#?R59843;85C>%70R55<0R0;20A2155!sL$CER3?222R6'61410P4P614151432C;C;g00DER61:61g00EQg00nH35R4791g00oT521g00I3#3R01:01%33A5614#BR4g010b%733@35791=215g00KI/A4=232'6'6do"). Qed.
Definition scsG4 : list sidecond := Eval vm_compute in (snd (fst rG4)).
Lemma factsG4 : ltac2:(zQ "h42!j4!hrb!ijc!hqe!hq7!hp1!np2!oj9!ho6!k2!npd!nq3!ij2!ikb!hs7!ng3!nqa!ojf!nre!ik2&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_usage_defs ()) ["FPX1"] "p;1p;3p;4p;2g0000j14Tg000Pj1DTg001Wj10Tg002<j12Tg002aj1=Tg003?j16Tg004Fj3:Tg005Mj1@Tg005kj4?Tg0076j19Tg007Vj3>Tg0086j31Tg008Pj25Tg008kj27Tg009Ej4<Tg009`j28Tg00:@j33Tg00:]j3;Tg00;:j1CTg00<@j3BTg00=Fj2ATg00>LR0#4R1g00?Wg00@7g00@ig00AUg00BA#Dg00B`R2#0#0#2#0#2#0#0#0#0#=#63:%=2#63:%22#2#@#6C?%90R25>0R0;10A1122R3g00CER4g00CeR5;15R6'51710P3P617121745C<C<g00DER61861g00EQg012033R37;1g013<511g00I3#4R01801%44A3613#CR3g014J%943B337;1=112g00KI/A3=145'5'5do"). Qed.
Definition scsH4 : list sidecond := Eval vm_compute in (snd (fst rH4)).
Lemma factsH4 : ltac2:(zQ "h42!j4!hrb!ijc!hqe!hq7!hp1!np2!ok7!ho6!k2!npd!nq3!ij2!ikb!hs7!nha!nqa!okd!nre!ik2&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_usage_defs ()) ["FPX1"] "p;1p;3p;2p;4g0000j13Tg0076j18Tg0086j30Tg008Pj21Tg008kj27Tg009Ej46Tg009`j25Tg00:@j32Tg00:]j34Tg00;:j1;Tg00<@j3:Tg00=Fj29Tg00>LR0#3R1%80R0;00R2g00CER3g00CeR4;04R5,121710R6P2P5P61734C6C6g00DER61561g00EQg015X32R5741g016d501g00I3#3R21521%33A2615#;R5g0182%833:32741=010g00KI/95=034'1'1do"). Qed.

Definition scsFs1 : list sidecond := Eval vm_compute in (snd (fst rFs1)).
Lemma factsFs1 : ltac2:(zQ "h42!j4!hrb!ijc!hqe!hq7!hp1!np2!ol5!ho6!k2!npd!nq3!ij2!ikb!hs7!olc!nqa!om4!nre!ik2&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1z (kr_t_AsTail_usage_defs ()) ["FPX1"] "##-Ep;1p;3p;4p;2g0000j18Tg000Pj19Tg002aj1>Tg003?j1=Tg004Fj36Tg00Sej10Tg005kj44Tg001Wj12!s\$<j17Tg00\Sj4ETg00TDj3CTg0076j1B!s/$Vj35Tg0086j33!s/$Pj2;!s/$kj2:Tg009Ej4@!s/$`j2ATg00:@j3<!s/$]j3?Tg00;:j1HTg00<@j3GTg00=Fj2FTf0R0#0#0p=D%0!s0$!s$,p=I!s:4!s$3p=1g00>LR0#8R1g00?WR2g00@7g00@ig00BAR3#DR4#9R5g00B`R6#>#=36%D4R4#0#I#1!s$29R7C4g00CeR8g00]ZP5g00AUR9%93R:=697%26#2#7#2!s+->#=R636C4P2g00^LA69:6P5C4P8g00_>P8P3P4P7CEg00XP#=R49C97=C94C4%B0R4550!s%+R0;30A3144R9g00CER7?388R3';1:10P9P31:141:78C@C@g00DER31A31g00EQg019@3<R97?1g01:M5!s?$I3#8R01A01%87A<319#HR9g01;\%B73G3<7?1=314g00KI/F9=378';';do"). Qed.
Definition scsFs2 : list sidecond := Eval vm_compute in (snd (fst rFs2)).
Lemma factsFs2 : ltac2:(zQ "h42!j4!hrb!ijc!hqe!hq7!hp1!np2!omd!ho6!k2!npd!nq3!ij2!ikb!hs7!on4!nqa!ond!nre!ik2&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1z (kr_t_AsTail_usage_defs ()) ["FPX1"] "##,/p;1p;3p;4p;2g0000j16Tg000Pj1@Tg001Wj13Tg002<j15!s/$aj1?Tg003?j1=Tg004Fj3;Tg00Sej10Tg005kj4ATg0076j19!s/$Vj3GTg0086j32!s/$Pj28!s/$kj27Tg009Ej4>!s/$`j2:Tg00:@j34!s/$]j3<Tg00;:j1FTg00<@j3ETg00=Fj2DTf0R0#!s$&p=C%0!s4+!s:'B!s:4!s$3p=1g00>LR0#6R1g00?Wg00@7g00@ig00AUg00BAR2#@g00B`R3#3#3#5!s+0?#=3;%?3!s,$02#C#B#1!s$2@CA%90R25G0R0;20A2122R3g00CER4g00CeR5;25R6'81710P3P617121745C>C>g00DER61:61g00EQg01<j34R37<1g01>7521g00I3#6R01:01%64A4613#FR3g01?F%943E347<1=212g00KI/D3=245'8'8do"). Qed.
Definition scsFs3 : list sidecond := Eval vm_compute in (snd (fst rFs3)).
Lemma factsFs3 : ltac2:(zQ "h42!j4!hrb!ijc!hqe!hq7!hp1!np2!oo6!ho6!k2!npd!nq3!ij2!ikb!hs7!ood!nqa!op6!nre!ik2&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_usage_defs ()) ["FPX1"] "p;1p;3p;2p;4g0000j13Tg0076j18Tg0086j30Tg008Pj21Tg008kj27Tg009Ej46Tg009`j25Tg00:@j32Tg00:]j34Tg00;:j1;Tg00<@j3:Tg00=Fj29Tg00>LR0#3R1%80R0;00R2g00CER3g00CeR4;04R5,121710R6P2P5P61734C6C6g00DER61561g00EQg01@U32R5741g01Ab501g00I3#3R21521%33A2615#;R5g01C1%833:32741=010g00KI/95=034'1'1do"). Qed.
Definition scsGs : list sidecond := Eval vm_compute in (snd (fst rGs)).
Lemma factsGs : ltac2:(zQ "h42!j4!hrb!ijc!hqe!hq7!hp1!np2!opf!ho6!k2!npd!nq3!ij2!ikb!hs7!oq5!nqa!oqd!nre!ik2&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1z (kr_t_AsTail_usage_defs ()) ["FPX1"] "##,Fp;1p;3p;4p;2g0000j1:Tg000Pj1?Tg00Sej10Tg004Fj36Tg001Wj13Tg002<j14!s/$aj1<Tg003?j15Tg005Mj1B!s/$kj4ATg0076j1@!s/$Vj3GTg0086j32!s/$Pj27!s/$kj29Tg009Ej4>!s/$`j2=Tg00:@j38!s/$]j3;Tg00;:j1ETg00<@j3DTg00=Fj2FTf0R0#!s$&p=C%0!s4+!s:'H!s:4!s$3p=1g00>LR0#:R1g00?Wg00@7g00@ig00AUR2g00BAR3#?%03#C#H#1!s$2?56!sK$`R2#3#3#4!s+0<#536%<2!s,$42#4#B#5CA%@0R25G0R0;20A2122R3g00CER4g00CeR5;25R6'71910P3P619121945C>C>g00DER61=61g00EQg01D@38R37;1g01EL521g00I3#:R01=01%:4A8613#ER3g01FZ%@43D387;1=212g00KI/F3=245'7'7do"). Qed.
Definition scsHs : list sidecond := Eval vm_compute in (snd (fst rHs)).
Lemma factsHs : ltac2:(zQ "h42!j4!hrb!ijc!hqe!hq7!hp1!np2!or5!ho6!k2!npd!nq3!ij2!ikb!hs7!orb!nqa!os3!nre!ik2&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_usage_defs ()) ["FPX1"] "p;1p;3p;2p;4g0000j13Tg0076j18Tg0086j30Tg008Pj21Tg008kj27Tg009Ej46Tg009`j25Tg00:@j32Tg00:]j34Tg00;:j1;Tg00<@j3:Tg00=Fj29Tg00>LR0#3R1%80R0;00R2g00CER3g00CeR4;04R5,121710R6P2P5P61734C6C6g00DER61561g00EQg01Gh32R5741g01I4501g00I3#3R21521%33A2615#;R5g01JB%833:32741=010g00KI/95=034'1'1do"). Qed.
Definition scsG3s : list sidecond := Eval vm_compute in (snd (fst rG3s)).
Lemma factsG3s : ltac2:(zQ "h42!j4!hrb!ijc!hqe!hq7!hp1!np2!osb!ho6!k2!npd!nq3!ij2!ikb!hs7!ot2!nqa!otb!nre!ik2&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_usage_defs ()) ["FPX1"] "p;1p;3p;2p;4g0000j13Tg0076j18Tg0086j30Tg008Pj21Tg008kj27Tg009Ej46Tg009`j25Tg00:@j32Tg00:]j34Tg00;:j1;Tg00<@j3:Tg00=Fj29Tg00>LR0#3R1%80R0;00R2g00CER3g00CeR4;04R5,121710R6P2P5P61734C6C6g00DER61561g00EQg01KP32R5741g01L]501g00I3#3R21521%33A2615#;R5g01Ml%833:32741=010g00KI/95=034'1'1do"). Qed.
Definition scsH3s : list sidecond := Eval vm_compute in (snd (fst rH3s)).
Lemma factsH3s : ltac2:(zQ "h42!j4!hrb!ijc!hqe!hq7!hp1!np2!ou4!ho6!k2!npd!nq3!ij2!ikb!hs7!oub!nqa!ov4!nre!ik2&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_usage_defs ()) ["FPX1"] "p;1p;3p;2p;4g0000j13Tg0076j18Tg0086j30Tg008Pj21Tg008kj27Tg009Ej46Tg009`j25Tg00:@j32Tg00:]j34Tg00;:j1;Tg00<@j3:Tg00=Fj29Tg00>LR0#3R1%80R0;00R2g00CER3g00CeR4;04R5,121710R6P2P5P61734C6C6g00DER61561g00EQg01O;32R5741g01PH501g00I3#3R21521%33A2615#;R5g01QW%833:32741=010g00KI/95=034'1'1do"). Qed.
Lemma ot_itinerary_s : ltac2:(zQ "i50!h9!hq7!ijc!j4!hrb!hqe!kjf!ovd!ho6!np2!ip5!nq3!pg5!iqa!irb!r9!pd!q8!r2!pgc!ph4!phc!ol5!omd!oo6!osb!opf!ou4!or5!pi3!pia!pj0!pj8!pk0!pk8!pl0!pl8@2$b@3$9@2$1@2$1$0$0$0@4$6@2$1$0$0$0@4$6$0$0@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$h6@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$h7@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$h8@4$6@2$1$0$0$0@4$6$0$0$h2$h2$h1@2$b@3$9@2$1@2$1$0$0$0@4$6@2$1$0$0$0@4$6$0$0@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$ha@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$hc@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$he@4$6@2$1$0$0$0@4$6$0$0$h1$f$h0@2$b@3$9@2$1@2$1$0$0$0@4$6@2$1$0$0$0@4$6$0$0@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$h9@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$hb@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$hd@4$6@2$1$0$0$0@4$6$0$0$f$f$h0@2$b@3$9@1$d$a@3$eNhk3$i4$h5@2$c$a$i1@2$b@3$9@1$d$a@3$eNhi3$i2$h3@2$c$a$hf@3$9@1$d$a@3$eNhk3$i3$h4@2$c$a$i0").
Proof.
ltac2:(KReplay.run1z (kr_t_AsTail_usage_defs ()) ["FPX1"] "##cJp%0p%1p&0p;2p;1p;3p;<p;4g009`j2xTg001Wj10Tg002<j12Tg0086j3FTg01Rfk109Tg005Mj1BTg000Pj17!sT$aj1;Tg00Sej11Tg003?j1ATg00TDj3_Tg0076k101Tg01SHj3HTg01TQj3CTg00UKj2>Tg01UZk207Tg01Vcj2|Tg01Wlj2{Tg01Y5l<wTg01ZCj2c!tj$Pj2P!s/$kj2eTg009Ej4i!ti$0k104!sT$ej4TTg01[Ej3vTg004Fj3h!ta$Vj3!sJ$\Rk203Tg00:@j3yTg01][k102Tf0R0#2#0p=5%00#!s$$p=?!s2%!s>$\%00#Bp=fg01^`R1P1f1R2P0CTp=d%00#2p=8%2!s`&Ef2R3P1P!sG&`%20#2!so%Z!s2$p=9!s:%!s2$l!tC'Bp=@!ss$!s>%W!sw&#0p=]!sj'2p=g!sV$p=<g00AUR4%A07h2p=M%10#1p=z!s-$#1#1p=[!s2&p=n!s<+!s$'p=p!s:4!s$3p=u!sJD!s$Cp=bAh420p=a%00#;p=t%B0#Ap=D!ud%!v8$R!u|%B#Ap=G!u|'0p=m!wM'2p=Y!vT'0p=Kg01_>R5%73%72=45034p=JA45209453p>00f4R6f3R7!s;+545545p=X!sY&p=s!wC&p=:1>73?C20p=r!w4+!s$'p=L!y1+!s$'p=^g01`Eg01a1?h73=h42;h0p=Vg00XPR8,>20030p=S%03#;,>7!t-%=!sr%;,>2p=q!v3$,>2p>08!tG&p=~1>73!vE$7C2p=k%;0!sT$}g00I3R9%B7,>6?C32;40p=I%27!tf&B!s>&=490p=UA4920949394979496p=3AC7!sF&>06%;7!sX06f6f5;C6!sK+549p=o!sn+p=j!s2$p>05!tD,;!sj0N%07!s92Og00DES00Ay3207y7$02p=Q1x11R7/x1R3g00B`R2#0R0#0R6#2R:#0R;#0R<#2R=#0R>#5R?#0#?#\#fR@/d@%22R@#0RA#2RB#0S01#0S02#2S03#8S04#8S05#E#8!sY$C5`7RD;FD%0AS06#2S07#2RA#0S08#2#Z#9#l#@RE,dC%20RF#2RG#2S09#9S0:#WS0;#]#Z#fRH5`7RI=F3IS0<1dEE=`7HRH=F3HS0=g01a]RJ$09RK%2BS0>!to%#8#gS0?#0RL#0RM#0S0@#8#@RN%B0R0%5A!t[%A#2RO#2S0B#5#8S0C!tk$fRPg00BARQ#7RR%2;R;#0S0D#<RS#0S0E#;S0F'MRT%1QRQ#1RU#zRV#[RW#nS0G#1S0H#1#pS0I#1#uRX#uS0J#1S0K#1S0L#1RY#1RZ#1R[#1R\#1R]#1R^#n#[#p#b#bR_#7R`,aRRa%0<S0M!we&b#t'MPT%0FRc#0Rd#0Re#0Rf#DRg%A8R8P8%2:!x@$h#0S0N#<S0O#tS0P,MRRi%z_#[#u#b!s$%R_#1#[S0Q#1S0R#1S0S#[S0T#1S0U#1S0V#1S0W#1S0X#1S0Y#1S0Z#n#pS0[#1S0\#1S0]#1S0^#1Rj%APPi%7XS0_%2B#8#?#g#R#GS0`%1j#[RB%1B!s''ANRX%2@Rk#DRlA_4`8Rm9_48S0a=_4lRn5_4P8%[BRB#7!s^-!s'70kRo#<S0b#2#mRp#0#]#Y#@S0c#AS0d%D2Rq%5p#g#K#GS0eP8%7YS0f%7ZS0g%7[S0h%7\S0i%7]S0j%7^S0k%nB#p!t;2&015S0l3J3J400DXDX3J3J3JDX's!s+%S0mP8%2MRM#8#@PW%06R6#0R5#0RB#:S0n#0R^#;,MRS0oCrS0pP8%5M#@PWPTCrS0qP8%2LRL#0S0r#<!s?,s%2BRM#B%25R]#0R\#B5H`%7UR[/a`%;2'M%D@R@%9kRk#9R2#2#LRZ#0S0t#<#?#^RY#DRp%;6#ARrCVRs%?^R^#:Rt#0#^#^#^Ru#BRv%9^R^#2#g#LRw#2#?#^#@Rx3HRy%D6Rz,SsS0uP[P@PpP!so$?HvxR{1SszS0v%;?S0w#AR?,aa!sJ2|!sJ%x%0>R>#2#;#ARs,aaS0y!sP+}!sP$~1S}zS0z%2b#;,M!so,a!sE$v1SazS0{PT!s?,%8^#9#Z!s&$L#R#@R^%0w!s1&w3HRb!s[%|1aR?!s]+??H^wRa1S?zS0}1aRs!sA+r!sA$w1SrzS0~PR%]eS10PWP8C=S11%5f,qRRe%0GRG#2Rr#2#8#9Rz#5R^#W#DR@7CW%<fRf#0S12-08RRsPWPl!}^%2R?#5,qRR}PW%9^#GR^PR%:?S13PWPXPR%0:R:PWP8PR%<!~8$S14PWP@PR%2hRhPWPlPR%:hS15!sX%Q0NPW%0O#Y#l#GPR%2;ROPWP!t#$OS0N!sM'DPWPnPRQ0EPWg01bk%~Z!x_$Z#DRO;_nS0EPR%E=!t4$OPR%<>PW%D;S0DPRQ0MPW%2ARA#:#\#R#fS0M#AS16PyP{P|P~PvPbPaPw!s6DR%26R6#2R;#2R>#E!v|'7PR%0;R;#<S18#0PWQ0aC=S0aPR%:>PWP`C=S19PR%0<S1:#0#tR<PW%2]R]!sp$2#5#8#WCkS1;PR%E;!t$'<!tR6:MPWP[C=S1=PRQ0PPW%2cRc#0S0P#<R;!}h$CrS1>PRQ0wPQPBCkS0wPR%;hPU%EoRo!t@$!t>$?PRQ0FPV%]A#W#K#l#9!s?$0FPR!~p%2RA#EPW%2ZRZ#9RU#<#K!s$-l#DC=S1@PR%:APW%2U!wb$U#0#L#L!sC%APR%EMPWQ08#0#9#Y!s$&GC=RMPR%:]PW%2SRA#0#\#8#DC=RhPR%<\RB!vn%dC=S08PR%E\!v:'B!xW&PiC=S1C!t}'EPWQ0oC=S0oPR%<6R6#0!vA$S1D#:S1E#;Rc,MRC=R>P8Q0@#2R!sz$P8%?!s/&Q0?#ER\#2!#=3$?#:PV%2U!uG%P8%5LRLPWPgP8%?LPWPT1>8NRLPV%DFS0@1}Rf!{q&2dRd#:!s5+0;R!xJ$1>Rc!s-$}!|C'!{t&GRG#<R:!tr&RFPRQ0OPW%7QRUPRPSPWQ0L#7PRQ1:PWQ0K!s2%8PWQ0J#7PRP6PWPFPRPB!|M'nPW%8z#9#GRzPR%:kPW%<2#8#]#8#G%B5-07R%0Y!#6:$%:u#@Ru5HRQ0:#K,qRQ09#0RY#Z#@'|AH[xu%BtQ0A#:#?#@'{Q01!ye$5#^#@Q0>#0#ZRt#0Ru!sH'!ud&[1qRYPWQ0;!xs$W#GPRQ06#?PWQ0G!u?$07#!uM$H!s4%2#<PWQ0I#7Q0c,>8PWPU%fo,|L!{t$8%5tRt#<#m#@PWQ0B#8#W#mCkP8%2tRt#5RL#8PW%AC!w{$!t8%4!tz$\#5#GP8%mtPWQ03!v'$R!s:&9u#lPWQ05#8!sN'Q0b#:Ru#\#YPWPpP8%~u#]#KRu#0PQPqP8%2u!s/&9ARA#R#9#K!s7&5A#R#Y!s3%Q0r#2#?PW%AEP8%0\#?PV%A0P8%E?PV%DZRZ!z?$PVP!s/$t#2#R#9RZ#0#9!zf&EZ#?PWP8&019DIDUDUDI!s$0U!s:&UD3H06D!s$$Fo3jD3!s2%!s$/Fo!s+&I!sm&UR9+05!sS$!s$+RZ!s4/DND6DODODN!s&$N!s0+O!t3&!s$&M<w,cJRV;FVR?PNP0Q0MPTQ0yPTPgP@Pl1MR<R<Q16P<Q0_Q0`Q0QQ0RQ0SQ0DPOPlQ0T#7Q0UQ0VQ0WQ0XQ0YQ0ZQ0EPnPXP^PlP@P8A_4m8Q0[Q0\Q0]Q0^Q!#A0$:00lm!#A24,s_Q0pQ0qQ0s%B]%B=5H`R`PyQ0uP{Q0vP|Q0xP~Q0zPvQ0{PbQ0|PaQ0}PwQ0~!#8vBQ11ACeW[ReACsW8RsAC}W@R}Q17Q0aQ19Q1;Q!#8%4Q1=Q1>Q0wQ1?Q0FQ1@Q1APR%?rPWPUQ08Q1BQ1CQ0oPR%EGPWQ0kC=PR%<!|A$jPRQ1DPWQ0iPRQ1EPWQ0h!#8o%Q0gPRP;PWQ0fPRPdPWQ0@PRPfPWQ0ePRQ10PWPqPRQ12PWQ0dPRQ13PWPzPRQ14!#3P%15PWQ0C#8#9#GP9!yZ-O!xq-65j>D3D69jMh!yJ0!s$4!y4&h=FKhRMPNP0PPPT!s$$gP8P8PiQ0m!wo+P!wfoPePsP}PZ!te>Z=FKZR}'PRs'PRe'PRw'P1e3DQ0<Pw1e3IQ0=Pe1e3HP?Ps1eKVPMP}1eKh1eKZCi!s$'g00>L$04RZQ00/xZRhg00EQR}g019@CQPZPhP}g01<jCQ'd!s5+@UCQ5`7P7P1P1P1g01cWRMPMCTg01ddRMCT5F3!sU+D!sq/Gh!sq0f4!sq0PMg01g@R!sq%hURV!sq1KP!sq-O;!sq0if!sq2PMCTP!sg%g01k3g01l@5vjg01mM,cJ5FKg01n[g01oi5v_g0217!s>'22Eg023S!sV$24a!s>%'P!s$'do"). Qed.

(* [comment removed for export] *)
Lemma ot_itinerary : ltac2:(zQ "j20!h9!hq7!ijc!j4!hrb!hqe!kjf!ovd!ho6!ip5!np2!nq3!q8!pg5!iqa!irb!r9!pd!s8!plf!pm6!pmd!pn3!pna!np8!nsd!nt9!nu5!nv1!nvd!oib!oh3!po1!oj9!ohf!po7!ok7!pod!pp2!pp8!ngb!mtc!ppe!pq5!pqc!pr3!pra!ps1!ps7!pse@2$b@3$a@2$1@2$1@2$1$0$0$0$0@4$6@2$1@2$1$0$0$0$0@4$6@2$1$0$0$0@4$6$0$0@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$h8@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$h9@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$ha@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$hb@4$6@2$1@2$1$0$0$0$0@4$6@2$1$0$0$0@4$6$0$0$c$c$h2$c@2$b@3$a@2$1@2$1@2$1@2$1$0$0$0$0$0@4$6@2$1@2$1@2$1$0$0$0$0$0@4$6@2$1@2$1$0$0$0$0@4$6@2$1$0$0$0@4$6$0$0@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$hc@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$hd@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$hf@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$i2@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$i5@4$6@2$1@2$1@2$1$0$0$0$0$0@4$6@2$1@2$1$0$0$0$0@4$6@2$1$0$0$0@4$6$0$0$c$c$c$h0$h1@2$b@3$a@2$1@2$1$0$0$0@4$6@2$1$0$0$0@4$6$0$0@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$i0@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$i3@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$i6@4$6@2$1$0$0$0@4$6$0$0$h0$h0$h1@2$b@3$a@2$1@2$1@2$1$0$0$0$0@4$6@2$1@2$1$0$0$0$0@4$6@2$1$0$0$0@4$6$0$0@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$he@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$i1@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$i4@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$i7@4$6@2$1@2$1$0$0$0$0@4$6@2$1$0$0$0@4$6$0$0$h0$c$h0$h1@2$b@3$a@1$e$9@3$fNhg3$if$h5@2$d$9$ic@2$b@3$a@1$e$9@3$fNu3$ie$h4@2$d$9$i9@2$b@3$a@1$e$9@3$fNhg3$j0$h6@2$d$9$ia@2$b@3$a@1$e$9@3$fNs3$id$h3@2$d$9$i8@3$a@1$e$9@3$fNhg3$j1$h7@2$d$9$ib").
Proof.
ltac2:(KReplay.run1z (kr_t_AsTail_usage_defs ()) ["FPX1"] "##n1p%0p%1p&0p;2p;1p;3p;<p;4g009`j2oTg002<j11Tg001Wj10Tg0086j3LTg01Rfk10@Tg005Mj1:Tg000Pj16!s]$aj1CTg00Sej12Tg003?j1=Tg00TDj3iTg0076k109Tg01SHj3JTg01TQj3<Tg00UKj2DTg01UZk20?Tg01Vck207Tg01Wlk206Tg01Y5l<mTg01ZCj2N!tl$Pj2V!s/$kk203!tc$0k10=!sL$ej4GTg01[Ej3lTg004Fj3q!t[$Vj34Tg01\Rk20!tR$9Ek40;Tg00:@j3sTg01][j1~Tf0R0#0#1p=8%10#0#0p=b%0!s:$#0p=\%00#:p=pg01^`R1P1f1R2P0CGp=^%0!sL$#0p=f!sZ'1p=S!s2%!s>$A!s2':p=;f4R3P1f3R4P1f2R5P2CG!sq%dP5P1P!s~%>0:%1!ta$>!ta%!s{$y!s:$!ty%x!tG'1p=`!u,&#0p=T!sJ%!u/$[!s2'1p=_!sJ$p=9!sR'1p=t!tg$p=@g00AUR6%=07q2p=M%20#2p>00!s/$#2#2p=R!s2&p=k!s<+!s$'p=j!s:4!s$3p=QAq620p=e%00#Cp=r%:0#=p=B!uA%!u%$c!vJ%:#=p=H!ue'0p=Pg01_>R7%62;40p=}%65%62=470547p=E!s3&94759474p=hA472!s6+9473p=U%64!s=+!s^${!wb&p=71D45?<20p=g!vV+!s$'p=O!x?+!s$'p=ag01`Eg01a1?q45=q62;q0p=Xg00XPR8,D200<0p=]%05#C,D4!t-%?!sr%C,D2p=w%C0!s/$v%15!t&&!sQ,I%=09<52p=u%10#:p>08g00I3R9%:4,D3?<5!v0%K%14!se&:!s>&=490p=YA4920949594!s$$3p=3A<4!sF&>0>%C4!sX05f6f5;<!sK,549p=z!sn+p>05!s3$p=n%:2#=9<45!ss&4P3P420352P0H0;p=Wg00DER3As5207s4#~p=F!s3$9s34p>02!{^%%~!{_%1P2P1P0g01hUCGp=|AL452/V0p=Z1o11R0/o1R5/o1R4P5P0g00B`R2#1R:#0R;#1R<#0S00#0S01#1S02#8S03#8S04#b#8#\#pR=/^=R>%1:R?#1R@#f#S#A#;P=DdRA;LA1o41S05P4P5B0:0>=%0;S06#1S07#1R;#0S08#1#>#y#x#;R>%02RB#1RC#1S09#1S0:#>S0;#`S0<#T#[#pRDDdRE;LES0=1^>>>0:0DRF=L5FS0>P5P01^>=P>PDDdRD=L4DS0?g01a]RG$0@RH%1<S0@!uW%#8#_S0A#0RI#0RJ#0S0B#8#;RK%:BRL%9;S0C#0S0D#1S0E#1S0F#tS0G#1!tZ$;g00BARM#6RN%0B!u2$O#0RP#1RQ#0RR#@RS#0S0H#CS0I'MRT%2MRM#2RU$00RV#RRW#kS0J#2S0K#2#jS0L#2#QRX#QS0M#2S0N#2S0O#2RY#2RZ#2R[#2R\#2R]#2R^#k#R#j#Q!s$%R_#6R`,eNRa%0PRP#0S0!s'$Q#1Rb#r'MPT%0CRc#0S0R#0Rd#0Re#BRf%=8RgPg%1ORO#0S0!u,$T#@S0U#rS0V,MNRh&00_#R!t9+2#RS0W#2S0X#2S0Y#RS0Z#2S0[#2S0\#2S0]#2S0^#2S0_#2S0`#k#jS0a#2S0b#2S0c#2S0d#2Ri!st%e#2S0f#2S0g#RS0h#2S0i#2S0j#2S0k#2S0l#2S0m#2S0n!st%o#2S0p#2S0q#2S0r#2Rj%=;Ph%6XS0s%1<#8#A#_#c#HS0t%2j#RR<%2<!s''=KRX%B?RkAi6`gRl9i6gS0u=i6kRm5i6Pg%R<R<#6!sZ-!s'70?S0v#@S0w#1#fR?#0#T#S#;S0x#=S0y%B2Rn%9?#_#P#HS0zPg%6YS0{%6ZS0|%6[S0}%6\S0~%6]S10%6^S11%k<#j!t<2&097R7'}3EChDUDU3E3E3EDU3EChC{S12Pg%1JRJ#8#;PW!zZ%0R<#0R^#7S13#0R]#C,MNS14CgR\Pg%9J#;PWPTCgRJPg%1IS15#0S16#@!s?+I%1<R[#0RZ#:9J`8%6UR8/e`%C2'M%B:R:%1@S17#>S18#1#OR@#0S19#@#A#aS1:#BR2%CB#=RYCXR?%A]R]#7S1;#0#a#a#aS1<#:Ro%>]R]#1#_#ORp#1#A#a#;Rq3JRr%BBRs,]?R?P8P:P2PYCXRt?JoqRu1]tsRt%1!{a$Rv#1#rS1=#=Rw,ea!sS+x!sS$y1]xsRx%0v!sO$C#=Rz,eaS1>!sO+{!sO$|1]{sR{%1b#C,M!sm,a!sD$o1]asRaPT!s>+b%8]#_#y#[#O#c#;R]%0p!s1&p3JR}1]bsRb1eNw!sZ+w?J]pR~1]wsRw1eNzS1?!sC+Y!sC$p1]YsRYPN%TdS1@PWPgC?Rd%9e,wNS1AQ09#0!#65$1B#1#8#>S1C#9Rs#`#BR]7<WS1D%0eS1E#0S1F#0S1G#0,vNS1H?<WkS1I!~^%1Re#9!s|$J%>s#HS1K!sd$LPN%7eS1MPWPXC?S1NPN%0ORO!t[$IS1OPN%@OS1P#0S1QPWP]C?S1RPNQ0S#1!sN$kCIS0SPN%7OS1S!so'TPNQ0TPWQ0E#0#S#x#HCIS0EPN%1QROPWQ1KCIS0T!s_&U!s_'VPNPRPWPmCIS1WPNQ0HPWg01bk%1@S0H#>#_#OS1X#BR@;imS1YC?S1ZPN%bPS1[PWP@C?S1\PN%0vPW%BQS1!u+$^PNQ0PPWQ0C#1S0C#7#\#c#pS0P#=S1_CIS1`PrPuPyP|PoP}P~PN%1!#8T$Q#1Rv!v4%ROPN%0QRQ#@S1a#0PWQ0uC?RePN%7vPWP`C?RvPNQ0Q!#7P$0#rS1bPW%1[R[#1S1c#1#t#`#BCgRsPNPQ!t#&Q!tL2pPN%1^S1d#7PWP8C?S1ePNQ0VPW%1cS0V#0S1f#@R:!~Y$CgRzQ1=,DNS1=%:^7uMS1gQ1[!y$$[Q0v#bS0v#>#\$087uUS1hQ0I,DNS0IQ0C#9S0C#0#\#[#c#[#9!sL$VS1iPN%0BS1j#1RBPWQ1X#1S1X#>R^#@#P!s$-x#BCIS1kPN%7BPW%1^!~P$^#0#O#O#BC?S1lPNQ1dPWQ08#0#>#S!s$&!y7$8PN%7[PW%1S!un$#t!s[%mPN%@ZS1n!w6%yC?S1oPNPZ!zh'pPNQ1c#@PWPhC?S1cPNQ1j#0RZPWQ14CIS14!sj&j!sj%V#1S0V#7S1q#CRZ,MNC?S1rPgQ0B!u_%PgPg%A!s/&Q0A#bRB#1S0A!#??$7PV%1^!uO%PgQ15#9R^PWPfPg%A^PWPT1DgKR^PV%BCS15Q1F,vN!st$NQ0R#1S0R#7S1F!s9%%0:S1sPWPg1DN!uN$Q1P!sW,1UPW!~q+@S1U!u'&S1PPNQ0UPW%6MRCPNPSPWQ0O#6!zA$PWQ0N!s2$1aPWQ0M!s2%jPWQ!s_$1nPWPXPNQ13PWQ1C#8#>#HS1CPNQ17#7PWQ18#@#8#T#8#H%:<-0?NQ1:#0!#7k$Q1<#7#;R<5JNQ0;#P,wNQ0:#0RS#[#;+07AJ8q<Q1;#:Q0D#7#A#;+06Q00#1#9#9!sk$0@#0#[R<#0Rq!sI+!u~&81wN!uJ$<!yF$`#HPNQ06#APWQ0J!u^%!tx%0K!s4%1#@PWQ0L#6Q0x,DgPWPCQ0v#p-07^!|i$g%9<R<#@#f#;PWQ0F#`#`#HCgPg%1<R<#9R^#8PW%==Pg%9^!t;%3!t~$\#9#HPg%f<PWQ02!v7$c!s:&>q#xPWQ04#8!sN'Q0w#7Rq#\#SPWP2Pg%1q#>#T#PRq#0PMPn!s9$!s/%Q1d#>Rq#8#y#P!sB&9q#c#S!sF'6#1#APW%=>Pg%0B#APV%=L!zt%bPVQ1X#BRB!zn$PVP!zW$9#1#8#yRB#0#>!{=&bB#APWPg&099DKDYDYDK!s$0Y!s:&YD3H0>D5D5D5Fz405D3!s3%!s$/Fz!s+&K!sn&YR9'nD3D3RB!sY%!s$$R>,np!s3'!s$1M<m,NGRq;LqR2PKPLQ0PPTQ1>PTPfP]PkQ1b,MNR<PiQ1_P<Q0sQ0tQ0eQ0fQ0gQ1]P@PkQ0h#6Q0iQ0jQ0kQ0lQ0mQ0nQ1YPmPXQ1KPkP]PgAi6lgR6PkPlQ0oQ0pQ0qQ0r/}7!#B^8P\PJPI%:[%:P5J`RPPrP?PuPtPyPxP|P{PoPaP}PbP~PwPpPYPdQ1A?<W8R[Q1H?<WgRmQ1J?<W]R^POPePvPsP!#8>1Q1ePzQ1gQ1hQ1iQ1kQ1lQ08Q1mPNQ1B#7PWPCC?Q1oQ1pQ1cQ14Q1rPNQ09PWQ11CIPNQ1U!{b$10PNQ0V#TPWQ0~PNQ1q!#5L$}PNQ1f!s>%|PNQ1s!s>%{!#4B$TPWQ15PNQ1F!s>%zPNQ1@PWPnPNQ1GPWQ0yPNQ1MPWQ!#3'$Q!#3G&!}Z$G!#3G$P9!y;5!s$&!xz'9!xz8!xv&W=LHWRNPKPLP;PT!s$$fPgPgPhQ12!wV%P!wMFP[PmP^P>!t16>=LH>RP!z&%C#1#f#8#;RnPTQ1?!t=$8P`P<P_%=n!z-,WQ0XQ0Y!z-%`Q0Z#6Q0[Q0\Q0]Q0^Q0_Q0`PgPkPXP]PgP8PgP6Q0uPlQ0aQ0bQ0cQ0d!z$DRQ0H#:5J`R`!u;+!yM/!um>1nY9!vr89=LH9R^!vr'!u\'!vs1Q1=%:c7uMQ1[PU%1:#8#`Q0IPVQ1E#b#[#f#t#\#APdQ1DQ1IQ1LQ1NQ1OQ1RQ0SQ1TQ0EQ0TQ1VQ1WQ1ZQ1\Q1^Q1`P`!wvD!uYJPYQ1e1nzB!#3R8!s$%H04H04!ut+B=LHBRz'VRY'VRp'VRw'VR~'VRb'VR}'VP4PAQ0=P}Q05PEQ0>PbP5PFQ0?P~P4PDP2PwPHPqPNPpPHPWPPPYPHP>P^PzPHP9203HBDW!s$1P!#Z+&>L$0=RB1o3BR3g00EQR9g00F[CFPBP3P9g00L\CF'^!s5+PA!sB-XnCFD!#d;$0P1P1P1g01ddRzPzCGR^g025oCGPzCGQ!#Z@$!s`+`0!sm-cV!t10g>H026010!s8+jc!sT,27C!tC0^PzCGg01g@R^CG,|!t4-28N!s^-9Z!t4/2:f!t4'1!sl$!sc$0!v9%!tG+nH!sg,120!sg/15X!t'-<2!tc$!u|&!tc%!sy%5PHg02=>g02>J5ljg02?V,NG!s=$@cg02B05lig02C=!s='DJg02EW!sT%Fd!s='H1g02I>5l_g02JK,NGg02KXg02Le!sR%N2,NG5LHCZ!s$1do"). Qed.
End FPX1.
(* [comment removed for export] *)
