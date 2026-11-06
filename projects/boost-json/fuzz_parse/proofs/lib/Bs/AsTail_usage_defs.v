(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require As0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.boost_json.fuzz_parse.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib SymDriveH4 SymAux.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import AsShadow AsPrintfFirst AsSxKit AsStdioCall.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_AsTail_usage_defs () := KReplay.lz_vm "#$BnI47Corelib4Init9Datatypes4list00K89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX24expr02C13~~~K!t5+7Numbers7BinNums8positive02!sKG1!sK=1Z03!t}c1!t}&!smb3!ulC1Z02!t3]8sidecond!t~+!x4A1!sFB2!xt25Logic2eq00!s@83and00K!s[;1K!s[<1!z-=prod00C!sF;3fst!sC=sndC!vm\5s_log!vh%!sl^carry!sl&7!slN6SymAux;log_covered!sl%I!y7f0!y7Cbool!}1#ELinuxProcessSemantics5Riscv5Instr;branch_!s~$5!sXG5aluop06!sRN!zi=3nat!~]?!#3&+3I!udA0!v+B1!w?]9sym_state!w@'!sr]7scripts!sp'c!spO2BsAAsTail_usage_defs2rB!sqk4scsB!uXc6kentry!uWm4knV!ssl:ot_regions!wGmC!wGoC!vVnC!y|nD!u[o!ssl3knC!#5dA!#3j#2!#><b4!t4&!#9A\sadd!#?se!#8U+6!uo'!#85Q3!#@Q?1!yCgE!yCoE!{xnE0!wFc!x}%7!wBZ6!sXT1!sXT4!x0gF!x0o!ssl5knF0_!#3CkrF!#5wk5!u]#0!u^p!#7cmG!x<oG!}FnG!u[nH!u[oH!u[nH0!zpn4!zpp4!zpo4!u^nG!u^pG!u^oG!u^oH!u^pH!u^oH!u^m4rFs1!ssk6!zw#!sum!zx#s!u`p2!u`q!sum!u`#2!uap3!uaq3!uap3!#4>ns!#4>os!#4>ns!#4>n!u^pH!u^oH!}\oG3s!zyo!suoknG3!uaoH!uaqH!uapH!ua+!#`o;6option!#nv^!#]'&!#S9&!sod1!sok5!sok7!sok!#X8V2Bs;AsStdioCall9s!s0#_res!#o3C!xK'!#o5=!#m[#1C!t^^:!t^%call!vDk!#='%!#mq\4s_pc!{`3!#Z-50!#ea\!#WQ$!#X@&!#kvL:!sRN7I!y>i!ttU2!#5reARIP!#4{j7AMEMCPY!svk3rI!#6gk<ASTDIO_WRIT!#_5k8AMAINEPI!swk4rI!#9Rl4s!#@Zm4kn!#AOoOF!stn!#@Zn5!#?c#!u`n!stp!#@Yn5!#?b#!u`n!stn;ASTRNLEN_TR!szk2rI!#4HlG3!srmH!srnI!sro!#YBk3s!#bzl3kn!#cnnO!#lVm!y+n4kn!ssnsc!sso!zon4knH!u]o!sso!#h8m4kn!ssnsc!sso!#eWm!x<#!u]o!ss'".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc4listhc4conshc3nil89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bsh1AsTail_usage_defs4FPX1~~~~~~k85AEXITk88AMAINEPIk87AMEMCPYk84ARIPk8cASTDIO_WRITEk8bASTRNLEN_TRhc3nat37Corelib4Init7Decimaltc2D0tc2D2tc3Nil37Corelib4Init3Nathg2bof_num_uint37Corelib4Init6Numberhi3bUIntDecimal79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymExec23SX2~~~~~~hk77scriptshc4boolhk73SCRhk74exprhc4prodhk79sym_statehk78sidecondhc4truek85FUELTk85STOPThk78sym_exec69OSSVerifyaboost_jsonafuzz_parse6images9AsanUbsan1M~~~~~~huafloaded_segmentshk76kentryhc3fsthk75carryhk75s_log79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsbAsStdioCall~~~~~~il99stdio_reshk74ELithc6optionil94SCR_il9astdio_call37Corelib5Lists7ListDefise3map04Npos69OSSVerify6Proofsaboost_jsonafuzz_parse3libcRefMemcpyLib~~~~~~iv2bcallee_kepthk74ridx35stdpp9bitvectorbdefinitionsjk82bv46Stdlib5Arith8PeanoNat3Natjmb3eqbhc4negbhc3orbk87KEPT_MC36Stdlib5Lists4Listjq46filteriv2ccallee_saved3h5LinuxProcessSemantics5Riscv5Instrjt17ALU_ADDhk74EAluhk74EVarhc5falseise3nthhg23addise3seqk88rip_clobk83spxk83FMThc4pairjt17ALU_ANDjt17ALU_SRLhk72SAhk75KWordhc3appk85OT_FRhk74KImghk76KRangehk73KWr79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs0d1A1s1P1r1i1n1t1f1F1i1r1s1t~~~~~~kp78kn_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AsShadow~~~~~~kv47AAPP_HIkv46AHI_LO79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7AsSxKit~~~~~~lk74shknk89OT_SHOFFSk88ot_cellshk76KAlign46Stdlib6ZArith6BinInt1Zlqd3subhk75saddrjt15aluopjt15mulopk82PXk8cnot_px_rangek8aOT_SHOFFS2k86OT_SHXk88px_rangek85shxknk84knV0k84srV0hk72SShk76sentryhk72SEk8bAMEMCPY_RETk84knC0k84srC0k83knCk84srD0k8cASTRNLEN_RETk84knE0k84srE0k85knF0_k84srF0k84knG0k84srG0k84knH0k84srH0k84knI0k84srI0k85knG30il96sc_retk85knH30k84scG3k85srH30k85knI30k85srI30k85knF40k85knG40k84scF4k85srG40k85knH40k85srH40k85knI40k85srI4069OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SymAux~~~~~~njf7sregion37Corelib4Init5Logicno32eqk82rBhc3sndno33andk8aot_regionsk84scsBnjfblog_coveredk82rCk84scsCk82rDk84scsDk82rEk84scsEk82rFk84scsFk83rF0k85knF00k85scsF0k82rGk84scsGk82rHk84scsHk83rF4k85scsF4k83rG4k85scsG4k83rH4k85scsH4k84rFs1k85knFs0k86scsFs1k84rFs2k86knFs20k86scsFs2k84rFs3k86knFs30k86scsFs3k83rGsk85knGs0k85scsGsk83rHsk85knHs0k85scsHsk84rG3sk86knG3s0k86scsG3sk84rH3sk86knH3s0k86scsH3shk74s_pchc4Somek85knG3sk85knH3sk84knHsk84rI3sk83rIsk85scG3sk85scH3sk85scOFsk85srG3sk85srH3sk84srHsk84knF4k84knG3k83knHk84knH3k84knH4k83rG3k83rH3k82rIk83rI3k83rI4k84scH3k84scH4k84scOFk84srF4k84srG3k83srHk84srH3k84srH4" s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.
Open Scope Z_scope.

Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition AMEMCPY : Z := 0x1a239c.          (* [comment removed for export] *)
Definition AMEMCPY_RET : Z := 0x90274.       (* [comment removed for export] *)
Definition ASTRNLEN_TR : Z := 0x7a120.       (* [comment removed for export] *)
Definition ASTRNLEN_RET : Z := 0x7a584.      (* [comment removed for export] *)
Definition ASTDIO_WRITE : Z := 0x198b60.
Definition AEXIT : Z := 0x191274.
Definition AMAINEPI : Z := 0xbeab8.          (* [comment removed for export] *)
Definition ARIP : Z := 0x927a4.              (* [comment removed for export] *)
Definition STOPT : ltac2:(zQ "20!j4!h9@1$0$1") := ltac2:(zQ "90!h9!jb!k2!p5!pd!q8!r2!r9!s8@3$1$0$5@3$1$0$8@3$1$0$7@3$1$0$3@3$1$0$4@3$1$0$6@1$2$0").
Definition FUELT : nat := 20000.
Definition scr0 : ltac2:(zQ "10!ho6$0") := ltac2:(zQ "40!k2!hp1!hp8!hpf@3$2@1$0$1@1$0$3@1$0$1").
Definition runT : ltac2:(zQ "50!hq7!ho6!hqe!j4!hrb>3scr$1>2ss$2@2$0@2$0$2@1$3$4$1") := ltac2:(zQ "90!k2!hs7!hse!ht6!ho6!hrb!hte!hqe!ii4\3scr$4\2ss$7@7$6$8$2$1$3^2^1@1$0$5").
Definition kn_afterT : ltac2:(zQ "60!j4!hq7!ij7!ho6!hrb!hqe>1r@2$1@2$1$5@1$0$4$3>2kn@1$0$2@1$0$2") := ltac2:(zQ "b0!j4!hrb!ik1!hq7!ij7!hqe!hp1!ho6!k2!ik7!il0\1r@2$3@2$3$5@1$0$1$7\2kn@1$0$4@3$2@1$0$4@1$0$1@3$2@2$3@1$0$4@1$0$1@1$0$6@3$9@1$a@3$2$5@1$0$1@3$2@2$3$5@1$0$1$7^2^1@1$8$6").
Definition sc_of : ltac2:(zQ "50!j4!t6!ipa!hpf!ij7>2nv$1>2sr@1$0$3>2kn@1$0$4$2") := ltac2:(zQ "a0!iq7!ipa!j4!k2!iqf!hpf!ij7!t6!ir8!is0\2nv$7\2sr@1$2$5\2kn@1$2$6M4\1x@1$4$1$1@3$9^3^2^1\1r$1^1@c$8ZZZ@1$0Z@1$0Z@1$0Z@1$0Z@1$0Z@1$0Z@1$0Z@1$3$5@1$3$6").
Definition KEPT_MC : ltac2:(zQ "20!j4!t6@1$0$1") := ltac2:(zQ "60!t6!iu5!iuc!jj1!jk0!jm5@4$1@1$5@1$2#5$0$4$3").     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition KEPT_MCI : ltac2:(zQ "20!j4!t6@1$0$1") := ltac2:(zQ "60!t6!jo6!jod!jp4!jpa!jr7@3$5$0\1i$0@1$2@2$3@2$1^1Nh3@2$1^1Nh4$4").
Definition KEPT_CS : ltac2:(zQ "20!j4!t6@1$0$1") := ltac2:(zQ "60!t6!iu5!iuc!js1!jk0!jm5@4$1@1$5@1$2#5$0$4$3").    (* [comment removed for export] *)
Definition spx : ltac2:(zQ "20!h9!hpf>1k$0$1") := ltac2:(zQ "50!h9!jv5!kg0!iq7!kg8\1k$0@3$2$1@1$4N0@1$3^1").
(* [comment removed for export] *)
Definition rip_clob (i : nat) : bool :=
  match i with 5 | 11 | 12 | 13 | 14 | 15 | 16 | 17 => true | _ => false end%nat.
Definition after_rip : ltac2:(zQ "30!j4!hpf!t6>4base$2>2sr@1$0$1@1$0$1") := ltac2:(zQ "b0!t6!hpf!iq7!kh8!hp1!j4!khf!iu5!ki6!kid!kg8\4base$0\2sr@1$5$1@4$7$0$1\1i$0M4\0$4$1@1$9^1@1$a@2$6^3^1M0\1i$0$1^1@4$3$1^1^2@1$2Z\1n$0M0\1n$0$1^1@4$3$1^2^3@1$2Z\2n0$0M0\2n0$0$1^1@4$3$1^3^4@1$2Z\2n1$0M0\2n1$0$1^1@4$3$1^4^5@1$2Z\2n2$0M0\2n2$0$1^1@4$3$1^5^6@1$2Z\2n3$0M0\2n3$0$1^1@4$3$1^6^7@1$2Z\2n4$0M0\2n4$0$1^1@4$3$1^7^8@1$2Z\2n5$0M0\2n5$0$1^1@4$3$1^8^9@1$2Z\2n6$0M0\2n6$0$1^1@4$3$1^9^a@1$2Z\2n7$0M0\2n7$0$1^1@4$3$1^a^b@1$2Z\2n8$0M0\2n8$0$1^1@1$2Z\2n9$0@4$3$1^c^d@1$2Z@2$8N0Ni0").
Definition RIP_FR : Z := 80.
Definition OT_FR : Z := 6000.                (* [comment removed for export] *)
Definition FMT : Z := 0x16ee8.
Definition NPRE : Z := 7.
Definition NSUF : Z := 7.                (* [comment removed for export] *)
Definition IHI : Z := 0x80000000.            (* [comment removed for export] *)
Definition BUF_LO : Z := (-592).
Definition BUF_HI : Z := (-512).
Definition PX : ltac2:(zQ "10!hpf$0") := ltac2:(zQ "10!kg8@1$0Nod").            (* [comment removed for export] *)

(* [comment removed for export] *)
Definition srV0 : ltac2:(zQ "20!j4!hpf@1$0$1") := ltac2:(zQ "90!t6!hpf!khf!kg8!iq7!kj8!kje!iu5!ki6@4$7$0$1\1i$0M0\1i$0$1^1@1$4Z\1n$0M0\1n$0$1^1@1$4+nvhi4\2n0$0M0\2n0$0$1^1@1$5-v0\2n1$0M0\2n1$0$1^1@1$3@2$2Ni3^4\2n2$0M0\2n2$0$1^1@1$4+mvhjh8\2n3$0M0\2n3$0$1^1@1$3@2$2Ni3^6\2n4$0M0\2n4$0$1^1@1$3@2$2Ni3^7\2n5$0M0\2n5$0$1^1@1$3@2$2Ni3^8\2n6$0M0\2n6$0$1^1@1$4$6\2n7$0M0\2n7$0$1^1@1$4+hrmti0\2n8$0M0\2n8$0$1^1@1$4+hrmti0\2n9$0M0\2n9$0$1^1@1$4$6\3n10$0M0\3n10$0$1^1@1$5-r0\3n11$0M0\3n11$0$1^1@1$3@2$2Ni3^e\3n12$0M0\3n12$0$1^1@1$3@2$2Ni3^f\3n13$0M0\3n13$0$1^1@1$3@2$2Ni3^h0\3n14$0M0\3n14$0$1^1@1$3@2$2Ni3^h1\3n15$0M0\3n15$0$1^1@1$3@2$2Ni3^h2\3n16$0M0\3n16$0$1^1@1$5-r0\3n17$0@1$3@2$2Ni3^h4@2$8N0Ni0").

(* [comment removed for export] *)
Definition ot_cells : ltac2:(zQ "40!hq7!h9!j4!t6@1$2@2$0@2$0$1$3$1") := ltac2:(zQ "60!h9!hq7!t6!kk4!jb!k2@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrkig0N8+hppqsc@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrkjn8N8+hqijpc@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrkjo0N8+hqinq0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrkji8N8+hqiuu0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrkhr8N8+hqiiq0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrthn8N8+nvvvogg0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrtul8N1+1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrtul9N1+1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+ikusvcN1+1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+ikutq3N1+1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmti0N4+5@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmtk0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmtk8N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmtl8N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmtm8N8+hporm0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmtn8N8+nhhrj0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmto0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmtp8N4+2@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmtq8N4Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmtqcN4+vvvvvvvf@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmtr0N4+vvvvvvvf@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nvvvqtt8N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nvvvqtu0N8Z@1$5@2$1@2$1$0$2$0").

(* [comment removed for export] *)
Definition OT_SHOFFS : ltac2:(zQ "20!j4!h9@1$0$1") := ltac2:(zQ "30!h9!jb!k2@3$1$0-il0@3$1$0-ika@1$2$0").
Definition OT_SHOFFS2 : ltac2:(zQ "20!j4!h9@1$0$1") := ltac2:(zQ "30!h9!jb!k2@3$1$0-il0@3$1$0-ika@3$1$0-ik9@1$2$0").
Definition OT_SHX : ltac2:(zQ "20!j4!hpf@1$0$1") := ltac2:(zQ "90!kg0!iq7!jv5!kg8!hpf!jb!kkb!kl6!k2@3$5$4@3$0$6@3$0$2@3$0$7@3$0$2@3$0$2@1$3N2@1$3Nod@1$1-1@1$1+3@1$1+nvvvogg0@1$1-8@3$5$4@3$0$6@3$0$2@3$0$7@1$3N2@1$1+3@1$1+nvvvogg0@1$1-8@3$5$4@3$0$6@3$0$2@3$0$7@3$0$2@3$0$2@1$3N0@1$3Nod@1$1-ika@1$1+3@1$1+nvvvogg0@1$1-8@3$5$4@3$0$6@3$0$2@3$0$7@3$0$2@3$0$2@1$3N0@1$3Nod@1$1-ik9@1$1+3@1$1+nvvvogg0@1$1-8@3$5$4@3$0$6@3$0$2@3$0$7@3$0$2@3$0$2@1$3N0@1$3Nod@1$1-ik3@1$1+3@1$1+nvvvogg0@1$1-8@1$8$4").
Fixpoint shxkn (l : list expr) : list kentry :=
  match l with [] => [] | e :: r => KRange e 0x20000000000 0x10007fff8000 :: KZero (SA e 0) (ELit 8) :: shxkn r end.

Definition knV0 : ltac2:(zQ "20!j4!ij7@1$0$1") := ltac2:(zQ "h40!ij7!kg8!jb!km1!km7!iq7!kn0!kn6!kne!ko6!kp0!k2!ku8!lj2!ljd!lo4!loc!lp8!lq3!ls5@3$6$0@3$2$0@2$h2@1$1N0+h0@3$2$0@3$9@1$1N0+nvvvogggggg0+ogggggggggg0@3$2$0@2$a@2$3@1$1N0@2$h3-o0$7$7@3$2$0@3$9@1$1N2$e$d@3$2$0@2$8+hggg0+mngg0@3$2$0@2$8+hqqgg0+hrkgg0@3$2$0@3$4@2$3@1$1N0-r0N8@1$1N2@3$2$0@3$4@2$3@1$1N0-r8N8@1$5+ruqn0@3$2$0@3$4@2$3@1$1N0-s0N8@1$1Nb@3$2$0@3$4@2$3@1$1N0-s8N8@1$1Nc@3$2$0@3$4@2$3@1$1N0-t0N8@1$1Nh5@3$2$0@3$4@2$3@1$5Z+nhhjl8N8@1$1N1@3$2$0@2$a@2$3@1$5Z+hrmti0+u8@1$b$0@3$6$0@1$f$h0@1$c$h1").
(* [comment removed for export] *)
Definition not_px_range (k : kentry) : bool := match k with KRange (EVar 141) _ _ => false | _ => true end.
Definition px_range : ltac2:(zQ "30!j4!h9!ij7>2lo$1>2hi$1>2kn@1$0$2@1$0$2") := ltac2:(zQ "80!ij7!h9!jb!j4!lu7!luc!ko6!jr7\2lo$1\2hi$1\2kn@1$3$0@3$2$0@3$6$4^3^2@3$7$0$5^1").
(* [comment removed for export] *)
Definition kn_readd : ltac2:(zQ "30!j4!h9!ij7>3plo$1>3phi$1>2kn@1$0$2@1$0$2") := ltac2:(zQ "90!ij7!kn0!h9!j4!lo4!lvb!mg8!mh1!mhc\3plo$2\3phi$2\2kn@1$3$0@3$7^3^2@3$1$0@1$8$6@3$1$0@1$4$5^1").

(* [comment removed for export] *)
Definition ssB0 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "50!k2!mi4!mib!mj2!mj8@5$3+hppqsc$2@1$0$4$1Nk3").
Definition rB := Eval vm_compute in runT (SCR [false] [] []) ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_afterT rB knV0.
(* [comment removed for export] *)
Definition logM1 : ltac2:(zQ "20!j4!mj8@1$0$1") := ltac2:(zQ "70!mj8!jb!iq7!kg8!km1!mk2!k2@3$1$0@3$5@2$4@1$3N0-ikaN1@1$2+i0@3$1$0@3$5@2$4@1$3N0-ikcN2@1$2+jqm5@3$1$0@3$5@2$4@1$3N0-il0N4@1$2+mnmhnjn5@1$6$0").
Definition knC0 : list kentry := Eval vm_compute in fst (fst (carry logM1 knB [])).
Definition srC0 : list expr := Eval vm_compute in sr_after_call_j srB KEPT_MC 67.
(* [comment removed for export] *)
Definition ssC0 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "60!k2!mk8!ml6!mld!mj2!mj8@5$4$1$3@1$0$5$2Nm3").
Definition rC := Eval vm_compute in runT (SCR [] [] []) ssC0.
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC)).
Definition knC : list kentry := Eval vm_compute in kn_afterT rC knC0.
Definition srD0 : list expr := Eval vm_compute in sr_after_call_j srC KEPT_MC 99.
(* [comment removed for export] *)
Definition ssD0 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "60!k2!mk8!mm4!mma!mj2!mj8@5$4$1$3@1$0$5$2No3").
Definition rD := Eval vm_compute in runT (SCR [] [] []) ssD0.
Definition srD : list expr := Eval vm_compute in s_regs (fst (fst rD)).
Definition knD : list kentry := Eval vm_compute in kn_afterT rD knC.
(* [comment removed for export] *)
Definition knE0 : list kentry := Eval vm_compute in kn_readd 0 131071 (kn_cut 0 (-1152 - 4400) (-1152) IHI knD).
Definition srE0 : list expr := Eval vm_compute in sr_after_call_j srD KEPT_CS 131.
(* [comment removed for export] *)
Definition ssE0 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "60!k2!mn1!mo0!mo7!mj2!mj8@5$4$1$3@1$0$5$2Nq3").
Definition rE := Eval vm_compute in runT (SCR [false] [ELit 0] []) ssE0.
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
Definition knE : list kentry := Eval vm_compute in kn_afterT rE knE0.
Definition srF0 : list expr := Eval vm_compute in sr_after_call_j srE KEPT_MC 163.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FQMAX : Z := 64.
Definition knF0_ : list kentry := Eval vm_compute in px_range 1 FQMAX knE.
Definition ssF0 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "60!k2!mk8!moe!mp6!mj2!mj8@5$4$1$3@1$0$5$2Ns3").
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
Definition ssG0 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "60!k2!mk8!mpd!mq4!mj2!mj8@5$4$1$3@1$0$5$2Nu3").
Definition rG := Eval vm_compute in runT (SCR [false] [] []) ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_afterT rG knG0.
Definition knH0 : list kentry := Eval vm_compute in kn_readd 0 66 (kn_cut 0 (BUF_LO + NPRE) BUF_HI IHI knG).
Definition srH0 : list expr := Eval vm_compute in sr_after_call_j srG KEPT_MC 227.
(* [comment removed for export] *)
Definition ssH0 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "60!k2!mk8!mqb!mr2!mj2!mj8@5$4$1$3@1$0$5$2Nhg3").
Definition rH := Eval vm_compute in runT (SCR [] [] []) ssH0.
Definition srH : list expr := Eval vm_compute in s_regs (fst (fst rH)).
Definition knH : list kentry := Eval vm_compute in kn_afterT rH knH0.
Definition scOF : stdio_res := Eval vm_compute in sc_of 259 srH knH.
Definition srI0 : list expr := Eval vm_compute in sc_sr scOF.
Definition knI0 : list kentry := Eval vm_compute in sc_kn scOF.
(* [comment removed for export] *)
Definition ssI0 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "50!k2!mr9!ms0!mj2!mj8@5$3+hpprv4$2@1$0$4$1Nhi3").
Definition rI := Eval vm_compute in runT (SCR [] [] []) ssI0.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition knG30 : list kentry := Eval vm_compute in kn_readd (66 + 1) (66 + NSUF) (kn_cut 0 (BUF_LO + NPRE) BUF_HI IHI knF).
Definition ssG30 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "60!k2!mk8!ms7!mq4!mj2!mj8@5$4$1$3@1$0$5$2Nu3").
Definition rG3 := Eval vm_compute in runT (SCR [] [] []) ssG30.
Definition srG3 : list expr := Eval vm_compute in s_regs (fst (fst rG3)).
Definition knG3 : list kentry := Eval vm_compute in kn_afterT rG3 knG30.
Definition scG3 : stdio_res := Eval vm_compute in sc_of 227 srG3 knG3.
Definition srH30 : list expr := Eval vm_compute in sc_sr scG3.
Definition knH30 : list kentry := Eval vm_compute in sc_kn scG3.
(* [comment removed for export] *)
Definition ssH30 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "70!k2!msf!mt9!mu1!mu8!mj2!mj8@5$5@1$1$3$4@1$0$6$2Nhg3").
Definition rH3 := Eval vm_compute in runT (SCR [] [] []) ssH30.
Definition srH3 : list expr := Eval vm_compute in s_regs (fst (fst rH3)).
Definition knH3 : list kentry := Eval vm_compute in kn_afterT rH3 knH30.
Definition scH3 : stdio_res := Eval vm_compute in sc_of 259 srH3 knH3.
Definition srI30 : list expr := Eval vm_compute in sc_sr scH3.
Definition knI30 : list kentry := Eval vm_compute in sc_kn scH3.
(* [comment removed for export] *)
Definition ssI30 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "50!k2!mv0!mv8!mj2!mj8@5$3+hpprv4$2@1$0$4$1Nhi3").
Definition rI3 := Eval vm_compute in runT (SCR [] [] []) ssI30.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition knF40 : list kentry := Eval vm_compute in px_range (66 + NSUF + 1) 131071 knE.
Definition ssF40 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "60!k2!mk8!ng0!mp6!mj2!mj8@5$4$1$3@1$0$5$2Ns3").
Definition rF4 := Eval vm_compute in runT (SCR [true] [] []) ssF40.
Definition srF4 : list expr := Eval vm_compute in s_regs (fst (fst rF4)).
Definition knF4 : list kentry := Eval vm_compute in kn_afterT rF4 knF40.
Definition scF4 : stdio_res := Eval vm_compute in sc_of 195 srF4 knF4.
Definition srG40 : list expr := Eval vm_compute in sc_sr scF4.
Definition knG40 : list kentry := Eval vm_compute in kn_readd (66 + NSUF + 1) 131071 (sc_kn scF4).
(* [comment removed for export] *)
Definition ssG40 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "70!k2!msf!ng8!nh0!nh7!mj2!mj8@5$5@1$1$3$4@1$0$6$2Nu3").
Definition rG4 := Eval vm_compute in runT (SCR [false] [] []) ssG40.
Definition srG4 : list expr := Eval vm_compute in s_regs (fst (fst rG4)).
Definition knG4 : list kentry := Eval vm_compute in kn_afterT rG4 knG40.
(* [comment removed for export] *)
Definition logNL : ltac2:(zQ "20!j4!mj8@1$0$1") := ltac2:(zQ "70!mj8!jb!iq7!kg8!km1!mk2!k2@3$1$0@3$5@2$4@1$3N0-ikaN1@1$2+a@3$1$0@3$5@2$4@1$3N0-ikcN2@1$2+lkl5@3$1$0@3$5@2$4@1$3N0-il0N4@1$2+lgkukpi0@1$6$0").
Definition knH40 : list kentry := Eval vm_compute in fst (fst (carry logNL knG4 [])).
Definition srH40 : list expr := Eval vm_compute in sr_after_call_j srG4 KEPT_MC 227.
(* [comment removed for export] *)
Definition ssH40 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "60!k2!mk8!nhf!ni7!mj2!mj8@5$4$1$3@1$0$5$2Nhg3").
Definition rH4 := Eval vm_compute in runT (SCR [] [] []) ssH40.
Definition srH4 : list expr := Eval vm_compute in s_regs (fst (fst rH4)).
Definition knH4 : list kentry := Eval vm_compute in kn_afterT rH4 knH40.
Definition scH4 : stdio_res := Eval vm_compute in sc_of 259 srH4 knH4.
Definition srI40 : list expr := Eval vm_compute in sc_sr scH4.
Definition knI40 : list kentry := Eval vm_compute in sc_kn scH4.
(* [comment removed for export] *)
Definition ssI40 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "50!k2!nif!nj7!mj2!mj8@5$3+hpprv4$2@1$0$4$1Nhi3").
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
Definition rFs2 := Eval vm_compute in runT (SCR [false] [] []) (SS 0x90524 srFs20 [] knFs20 227).
Definition srFs2 : list expr := Eval vm_compute in s_regs (fst (fst rFs2)).
Definition knFs2 : list kentry := Eval vm_compute in kn_afterT rFs2 knFs20.
Definition srFs30 : list expr := Eval vm_compute in after_rip 227 srFs2.
Definition knFs30 : list kentry := Eval vm_compute in kn_readd (FQMAX + 1) (66 + NSUF) (kn_cut 0 (RIPSP - RIP_FR) RIPSP IHI knFs2).
(* [comment removed for export] *)
Definition rFs3 := Eval vm_compute in runT (SCR [] [] []) (SS 0x90620 srFs30 [] knFs30 259).
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
Definition rIs := Eval vm_compute in runT (SCR [] [] []) (SS 0x199bf4 srIs0 [] knIs0 355).
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
Definition rI3s := Eval vm_compute in runT (SCR [] [] []) (SS 0x199bf4 srI3s0 [] knI3s0 355).

(* [comment removed for export] *)
Definition ot_regions : ltac2:(zQ "20!j4!nn8@1$0$1") := ltac2:(zQ "b0!h9!lsc!hq7!jb!kk4!kn6!km1!k2!iq7!kg8!ls5@3$3@2$2$1$0@4$4$1$0@2$6@1$9N0@2$a-o0$5$5@3$3@2$2$1$0@4$4$1$0@2$6@1$8Z+hrmti0+u8@1$7@2$2$1$0").
Definition scsB : list sidecond := Eval vm_compute in (snd (fst rB)).
Lemma factsB : ltac2:(zQ "h42!j4!hrb!ik1!hqe!hq7!hp1!np7!npd!ho6!k2!nq2!nq8!ij7!il0!hs7!mi4!nqf!nrc!ns3!ik7&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_usage_defs ()) ["FPX1"] "p;1p;3p;4p;2g0000j14Tg000Pj1DTg001Wj10Tg002<j12Tg002aj1=Tg003?j16Tg004Fj3:Tg005Mj1@Tg005kj4?Tg0076j19Tg007Vj3>Tg0086j31Tg008Pj25Tg008kj27Tg009Ej4<Tg009`j28Tg00:@j33Tg00:]j3;Tg00;:j1CTg00<@j3BTg00=Fj2ATg00>LR0#4R1g00?Wg00@7g00@ig00AUg00BA#Dg00B`R2#0#0#2#0#2#0#0#0#0#=#63:%=2#63:%22#2#@#6C?%90R25>0R0;10A1122R3g00CER4g00CeR5;15R6'51710P3P617121745C<C<g00DER61861g00EQg00F[33R37;1g00Gf511g00I3#4R01801%44A3613#CR3g00J<%943B337;1=112g00KI/A3=145'5'5do"). Qed.
Definition scsC : list sidecond := Eval vm_compute in (snd (fst rC)).
Lemma factsC : ltac2:(zQ "h42!j4!hrb!ik1!hqe!hq7!hp1!np7!nt2!ho6!k2!nq2!nq8!ij7!il0!hs7!ml6!nqf!nt7!ns3!ik7&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_usage_defs ()) ["FPX1"] "p;1p;3p;2p;4g0000j13Tg0076j18Tg0086j30Tg008Pj21Tg008kj27Tg009Ej46Tg009`j25Tg00:@j32Tg00:]j34Tg00;:j1;Tg00<@j3:Tg00=Fj29Tg00>LR0#3R1%80R0;00R2g00CER3g00CeR4;04R5,121710R6P2P5P61734C6C6g00DER61561g00EQg00L\32R5741g00Mg501g00I3#3R21521%33A2615#;R5g00O4%833:32741=010g00KI/95=034'1'1do"). Qed.
Definition scsD : list sidecond := Eval vm_compute in (snd (fst rD)).
Lemma factsD : ltac2:(zQ "h42!j4!hrb!ik1!hqe!hq7!hp1!np7!nte!ho6!k2!nq2!nq8!ij7!il0!hs7!mm4!nqf!nu3!ns3!ik7&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_usage_defs ()) ["FPX1"] "p;1p;3p;2p;4g0000j13Tg0076j18Tg0086j30Tg008Pj21Tg008kj27Tg009Ej46Tg009`j25Tg00:@j32Tg00:]j34Tg00;:j1;Tg00<@j3:Tg00=Fj29Tg00>LR0#3R1%80R0;00R2g00CER3g00CeR4;04R5,121710R6P2P5P61734C6C6g00DER61561g00EQg00PA32R5741g00QL501g00I3#3R21521%33A2615#;R5g00RY%833:32741=010g00KI/95=034'1'1do"). Qed.
Definition scsE : list sidecond := Eval vm_compute in (snd (fst rE)).
Lemma factsE : ltac2:(zQ "h42!j4!hrb!ik1!hqe!hq7!hp1!np7!nua!ho6!k2!nq2!nq8!ij7!il0!hs7!mo0!nqf!nuf!ns3!ik7&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1z (kr_t_AsTail_usage_defs ()) ["FPX1"] "##,,p;1p;3p;4p;2g0000j14Tg00Sej10Tg000Pj1;Tg003?j1GTg00TDj3BTg005kj4ATg004Fj3@Tg00UKj2>Tg00VSj4=Tg0076j17!s/$Vj3<Tg0086j32!s/$Pj26!s/$kj25Tg009Ej48!s/$`j29Tg00:@j33!s/$]j3:Tg00;:j1FTg00<@j3DTg00=Fj2ETf0R0#0#0p=C%0!s0$!s$,p=?!s:4!s$3p=1g00>LR0#4R1g00?WR2g00W^g00AUR3g00BA#0R4#0R5#0#C#?#1!s$2;R6g00XPR7#GR83BP6CA%;5=@36/>7P4P2P8C=%70R85<05<0R0;20A2188!t;$CER4g00CeR7;27R6'61510P2P615181547C8C8g00DER61961g00EQg00Xn33R27:1g00Z9521g00I3#4R01901%44A3612#F!t4$[F%743D337:1=218g00KI/E2=247'6'6do"). Qed.
Definition scsF : list sidecond := Eval vm_compute in (snd (fst rF)).
Lemma factsF : ltac2:(zQ "h42!j4!hrb!ik1!hqe!hq7!hp1!np7!nv6!ho6!k2!nq2!nq8!ij7!il0!hs7!moe!nqf!nvb!ns3!ik7&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1z (kr_t_AsTail_usage_defs ()) ["FPX1"] "##-^p;1p;3p;4p;2g0000j19Tg000Pj1=Tg001Wj13Tg002<j17!s/$aj1DTg003?j1:Tg004Fj36Tg00Sej10Tg005kj45Tg00\Sj4ETg00TDj3CTg0076j1B!s/$Vj34Tg0086j32!s/$Pj2;!s/$kj28Tg009Ej4@!s/$`j2ATg00:@j3<!s/$]j3?Tg00;:j1ITg00<@j3HTg00=Fj2GTf0R0#0#0p=>%0!s0$!s$,p=F!s:4!s$3p=1g00>LR0#9R1g00?WR2g00@7R3g00@iR4g00AUR5g00BAR6#=R7g00B`R8#3#3#7!s+0D#:R936R:%D8#:R836%>6R;#>R<#0#F#1!s$2=R=C5P2P3%=;R;=648P=C5g00CeR8g00]ZP;A657==659C5P2g00^LP:P;C5P8g00_>P8P6P<P=CEg00XP#:R<9C5==C5<C5%B0R<540!s%/R0;20A21<<!uK$CER=?288R6';1810P5P6181<18=8C@C@g00DER61A61g00EQg00`03<R57?1g00a;521g00I3#9R01A01%9=A<615#I!t-$bH%B=3H3<7?1=21<g00KI/G5=2=8';';do"). Qed.
Definition scsF0 : list sidecond := Eval vm_compute in (snd (fst rF0)).
Lemma factsF0 : ltac2:(zQ "h42!j4!hrb!ik1!hqe!hq7!hp1!np7!og2!ho6!k2!nq2!nq8!ij7!il0!hs7!og8!nqf!oh0!ns3!ik7&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1z (kr_t_AsTail_usage_defs ()) ["FPX1"] "##,Ap;1p;3p;4p;2g0000j16Tg000Pj1:Tg00Sej10Tg004Fj37Tg001Wj12Tg002<j15!s/$aj1CTg003?j1BTg005kj4<Tg0076j1;!s/$Vj3@Tg0086j33!s/$Pj28!s/$kj29Tg009Ej4>!s/$`j2?Tg00:@j34!s/$]j3=Tg00;:j1FTg00<@j3ETg00=Fj2DTf0R0#0#0p=A%0!s0$!s$,p=G!s:4!s$3p=1g00>LR0#6R1g00CeR2g00]Zg00BAR3#AR4#:R5g00AUR6%:3R3%04#A#G#1!s$2:576g00B`#2#2#5!s+0C#BR437C<g00?Wg00^LA7634P5C<%;0R55@05@0R0;30A3155R4g00CER3?322R6'81910P4P619151932C>C>g00DER61?61g00EQg00cV34R47!uN$db531g00I3#6R01?01%63A4614#F!t-$f0%;33E347=1=315g00KI/D4=332'8'8do"). Qed.
Definition scsG : list sidecond := Eval vm_compute in (snd (fst rG)).
Lemma factsG : ltac2:(zQ "h42!j4!hrb!ik1!hqe!hq7!hp1!np7!oh8!ho6!k2!nq2!nq8!ij7!il0!hs7!mpd!nqf!ohd!ns3!ik7&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1z (kr_t_AsTail_usage_defs ()) ["FPX1"] "##,Fp;1p;3p;4p;2g0000j1:Tg000Pj1?Tg00Sej10Tg004Fj36Tg001Wj13Tg002<j14!s/$aj1<Tg003?j15Tg005Mj1B!s/$kj4ATg0076j1@!s/$Vj3GTg0086j32!s/$Pj27!s/$kj29Tg009Ej4>!s/$`j2=Tg00:@j38!s/$]j3;Tg00;:j1ETg00<@j3DTg00=Fj2FTf0R0#!s$&p=C%0!s4+!s:'H!s:4!s$3p=1g00>LR0#:R1g00?Wg00@7g00@ig00AUR2g00BAR3#?%03#C#H#1!s$2?56!sK$`R2#3#3#4!s+0<#536%<2!s,$42#4#B#5CA%@0R25G0R0;20A2122R3g00CER4g00CeR5;25R6'71910P3P619121945C>C>g00DER61=61g00EQg00g>38R37;1g00hI521g00I3#:R01=01%:4A8613#E!t4$iV%@43D387;1=212g00KI/F3=245'7'7do"). Qed.
Definition scsH : list sidecond := Eval vm_compute in (snd (fst rH)).
Lemma factsH : ltac2:(zQ "h42!j4!hrb!ik1!hqe!hq7!hp1!np7!oi4!ho6!k2!nq2!nq8!ij7!il0!hs7!mqb!nqf!oi9!ns3!ik7&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_usage_defs ()) ["FPX1"] "p;1p;3p;2p;4g0000j13Tg0076j18Tg0086j30Tg008Pj21Tg008kj27Tg009Ej46Tg009`j25Tg00:@j32Tg00:]j34Tg00;:j1;Tg00<@j3:Tg00=Fj29Tg00>LR0#3R1%80R0;00R2g00CER3g00CeR4;04R5,121710R6P2P5P61734C6C6g00DER61561g00EQg00jc32R5741g00kn501g00I3#3R21521%33A2615#;R5g00m;%833:32741=010g00KI/95=034'1'1do"). Qed.
Definition scsF4 : list sidecond := Eval vm_compute in (snd (fst rF4)).
Lemma factsF4 : ltac2:(zQ "h42!j4!hrb!ik1!hqe!hq7!hp1!np7!oj0!ho6!k2!nq2!nq8!ij7!il0!hs7!ng0!nqf!oj6!ns3!ik7&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1z (kr_t_AsTail_usage_defs ()) ["FPX1"] "##+_p;1p;4p;3p;2g0000j13Tg00Sej10Tg000Pj1DTg00\Sj4CTg003?j1?Tg00TDj38Tg005kj4>Tg0076j17!s/$Vj3<Tg0086j32!s/$Pj26!s/$kj24Tg009Ej4;!s/$`j2:Tg00:@j35!s/$]j39Tg00;:j1BTg00<@j3@Tg00=Fj2ATf0R0#!s$&p=E%0!s4+!s:'=!s:4!s$3p=1g00>LR0#3R1g00CeR2g00_>P2g00BAR3%E3R3%03#=#1!s$2DR3CCg00AUR4g00XP#?R59843;85C>%70R55<0R0;20A2155!sL$CER3?222R6'61410P4P614151432C;C;g00DER61:61g00EQg00nH35R4791g00oT521g00I3#3R01:01%33A5614#BR4g010b%733@35791=215g00KI/A4=232'6'6do"). Qed.
Definition scsG4 : list sidecond := Eval vm_compute in (snd (fst rG4)).
Lemma factsG4 : ltac2:(zQ "h42!j4!hrb!ik1!hqe!hq7!hp1!np7!oje!ho6!k2!nq2!nq8!ij7!il0!hs7!ng8!nqf!ok4!ns3!ik7&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_usage_defs ()) ["FPX1"] "p;1p;3p;4p;2g0000j14Tg000Pj1DTg001Wj10Tg002<j12Tg002aj1=Tg003?j16Tg004Fj3:Tg005Mj1@Tg005kj4?Tg0076j19Tg007Vj3>Tg0086j31Tg008Pj25Tg008kj27Tg009Ej4<Tg009`j28Tg00:@j33Tg00:]j3;Tg00;:j1CTg00<@j3BTg00=Fj2ATg00>LR0#4R1g00?Wg00@7g00@ig00AUg00BA#Dg00B`R2#0#0#2#0#2#0#0#0#0#=#63:%=2#63:%22#2#@#6C?%90R25>0R0;10A1122R3g00CER4g00CeR5;15R6'51710P3P617121745C<C<g00DER61861g00EQg012033R37;1g013<511g00I3#4R01801%44A3613#CR3g014J%943B337;1=112g00KI/A3=145'5'5do"). Qed.
Definition scsH4 : list sidecond := Eval vm_compute in (snd (fst rH4)).
Lemma factsH4 : ltac2:(zQ "h42!j4!hrb!ik1!hqe!hq7!hp1!np7!okc!ho6!k2!nq2!nq8!ij7!il0!hs7!nhf!nqf!ol2!ns3!ik7&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_usage_defs ()) ["FPX1"] "p;1p;3p;2p;4g0000j13Tg0076j18Tg0086j30Tg008Pj21Tg008kj27Tg009Ej46Tg009`j25Tg00:@j32Tg00:]j34Tg00;:j1;Tg00<@j3:Tg00=Fj29Tg00>LR0#3R1%80R0;00R2g00CER3g00CeR4;04R5,121710R6P2P5P61734C6C6g00DER61561g00EQg015X32R5741g016d501g00I3#3R21521%33A2615#;R5g0182%833:32741=010g00KI/95=034'1'1do"). Qed.

Definition scsFs1 : list sidecond := Eval vm_compute in (snd (fst rFs1)).
Lemma factsFs1 : ltac2:(zQ "h42!j4!hrb!ik1!hqe!hq7!hp1!np7!ola!ho6!k2!nq2!nq8!ij7!il0!hs7!om1!nqf!om9!ns3!ik7&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1z (kr_t_AsTail_usage_defs ()) ["FPX1"] "##-Ep;1p;3p;4p;2g0000j18Tg000Pj19Tg002aj1>Tg003?j1=Tg004Fj36Tg00Sej10Tg005kj44Tg001Wj12!s\$<j17Tg00\Sj4ETg00TDj3CTg0076j1B!s/$Vj35Tg0086j33!s/$Pj2;!s/$kj2:Tg009Ej4@!s/$`j2ATg00:@j3<!s/$]j3?Tg00;:j1HTg00<@j3GTg00=Fj2FTf0R0#0#0p=D%0!s0$!s$,p=I!s:4!s$3p=1g00>LR0#8R1g00?WR2g00@7g00@ig00BAR3#DR4#9R5g00B`R6#>#=36%D4R4#0#I#1!s$29R7C4g00CeR8g00]ZP5g00AUR9%93R:=697%26#2#7#2!s+->#=R636C4P2g00^LA69:6P5C4P8g00_>P8P3P4P7CEg00XP#=R49C97=C94C4%B0R4550!s%+R0;30A3144R9g00CER7?388R3';1:10P9P31:141:78C@C@g00DER31A31g00EQg019@3<R97?1g01:M5!s?$I3#8R01A01%87A<319#HR9g01;\%B73G3<7?1=314g00KI/F9=378';';do"). Qed.
Definition scsFs2 : list sidecond := Eval vm_compute in (snd (fst rFs2)).
Lemma factsFs2 : ltac2:(zQ "h42!j4!hrb!ik1!hqe!hq7!hp1!np7!on2!ho6!k2!nq2!nq8!ij7!il0!hs7!on9!nqf!oo2!ns3!ik7&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1z (kr_t_AsTail_usage_defs ()) ["FPX1"] "##,/p;1p;3p;4p;2g0000j16Tg000Pj1@Tg001Wj13Tg002<j15!s/$aj1?Tg003?j1=Tg004Fj3;Tg00Sej10Tg005kj4ATg0076j19!s/$Vj3GTg0086j32!s/$Pj28!s/$kj27Tg009Ej4>!s/$`j2:Tg00:@j34!s/$]j3<Tg00;:j1FTg00<@j3ETg00=Fj2DTf0R0#!s$&p=C%0!s4+!s:'B!s:4!s$3p=1g00>LR0#6R1g00?Wg00@7g00@ig00AUg00BAR2#@g00B`R3#3#3#5!s+0?#=3;%?3!s,$02#C#B#1!s$2@CA%90R25G0R0;20A2122R3g00CER4g00CeR5;25R6'81710P3P617121745C>C>g00DER61:61g00EQg01<j34R37<1g01>7521g00I3#6R01:01%64A4613#FR3g01?F%943E347<1=212g00KI/D3=245'8'8do"). Qed.
Definition scsFs3 : list sidecond := Eval vm_compute in (snd (fst rFs3)).
Lemma factsFs3 : ltac2:(zQ "h42!j4!hrb!ik1!hqe!hq7!hp1!np7!oob!ho6!k2!nq2!nq8!ij7!il0!hs7!op2!nqf!opb!ns3!ik7&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_usage_defs ()) ["FPX1"] "p;1p;3p;2p;4g0000j13Tg0076j18Tg0086j30Tg008Pj21Tg008kj27Tg009Ej46Tg009`j25Tg00:@j32Tg00:]j34Tg00;:j1;Tg00<@j3:Tg00=Fj29Tg00>LR0#3R1%80R0;00R2g00CER3g00CeR4;04R5,121710R6P2P5P61734C6C6g00DER61561g00EQg01@U32R5741g01Ab501g00I3#3R21521%33A2615#;R5g01C1%833:32741=010g00KI/95=034'1'1do"). Qed.
Definition scsGs : list sidecond := Eval vm_compute in (snd (fst rGs)).
Lemma factsGs : ltac2:(zQ "h42!j4!hrb!ik1!hqe!hq7!hp1!np7!oq4!ho6!k2!nq2!nq8!ij7!il0!hs7!oqa!nqf!or2!ns3!ik7&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1z (kr_t_AsTail_usage_defs ()) ["FPX1"] "##,Fp;1p;3p;4p;2g0000j1:Tg000Pj1?Tg00Sej10Tg004Fj36Tg001Wj13Tg002<j14!s/$aj1<Tg003?j15Tg005Mj1B!s/$kj4ATg0076j1@!s/$Vj3GTg0086j32!s/$Pj27!s/$kj29Tg009Ej4>!s/$`j2=Tg00:@j38!s/$]j3;Tg00;:j1ETg00<@j3DTg00=Fj2FTf0R0#!s$&p=C%0!s4+!s:'H!s:4!s$3p=1g00>LR0#:R1g00?Wg00@7g00@ig00AUR2g00BAR3#?%03#C#H#1!s$2?56!sK$`R2#3#3#4!s+0<#536%<2!s,$42#4#B#5CA%@0R25G0R0;20A2122R3g00CER4g00CeR5;25R6'71910P3P619121945C>C>g00DER61=61g00EQg01D@38R37;1g01EL521g00I3#:R01=01%:4A8613#ER3g01FZ%@43D387;1=212g00KI/F3=245'7'7do"). Qed.
Definition scsHs : list sidecond := Eval vm_compute in (snd (fst rHs)).
Lemma factsHs : ltac2:(zQ "h42!j4!hrb!ik1!hqe!hq7!hp1!np7!ora!ho6!k2!nq2!nq8!ij7!il0!hs7!os0!nqf!os8!ns3!ik7&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_usage_defs ()) ["FPX1"] "p;1p;3p;2p;4g0000j13Tg0076j18Tg0086j30Tg008Pj21Tg008kj27Tg009Ej46Tg009`j25Tg00:@j32Tg00:]j34Tg00;:j1;Tg00<@j3:Tg00=Fj29Tg00>LR0#3R1%80R0;00R2g00CER3g00CeR4;04R5,121710R6P2P5P61734C6C6g00DER61561g00EQg01Gh32R5741g01I4501g00I3#3R21521%33A2615#;R5g01JB%833:32741=010g00KI/95=034'1'1do"). Qed.
Definition scsG3s : list sidecond := Eval vm_compute in (snd (fst rG3s)).
Lemma factsG3s : ltac2:(zQ "h42!j4!hrb!ik1!hqe!hq7!hp1!np7!ot0!ho6!k2!nq2!nq8!ij7!il0!hs7!ot7!nqf!ou0!ns3!ik7&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_usage_defs ()) ["FPX1"] "p;1p;3p;2p;4g0000j13Tg0076j18Tg0086j30Tg008Pj21Tg008kj27Tg009Ej46Tg009`j25Tg00:@j32Tg00:]j34Tg00;:j1;Tg00<@j3:Tg00=Fj29Tg00>LR0#3R1%80R0;00R2g00CER3g00CeR4;04R5,121710R6P2P5P61734C6C6g00DER61561g00EQg01KP32R5741g01L]501g00I3#3R21521%33A2615#;R5g01Ml%833:32741=010g00KI/95=034'1'1do"). Qed.
Definition scsH3s : list sidecond := Eval vm_compute in (snd (fst rH3s)).
Lemma factsH3s : ltac2:(zQ "h42!j4!hrb!ik1!hqe!hq7!hp1!np7!ou9!ho6!k2!nq2!nq8!ij7!il0!hs7!ov0!nqf!ov9!ns3!ik7&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_usage_defs ()) ["FPX1"] "p;1p;3p;2p;4g0000j13Tg0076j18Tg0086j30Tg008Pj21Tg008kj27Tg009Ej46Tg009`j25Tg00:@j32Tg00:]j34Tg00;:j1;Tg00<@j3:Tg00=Fj29Tg00>LR0#3R1%80R0;00R2g00CER3g00CeR4;04R5,121710R6P2P5P61734C6C6g00DER61561g00EQg01O;32R5741g01PH501g00I3#3R21521%33A2615#;R5g01QW%833:32741=010g00KI/95=034'1'1do"). Qed.
Lemma ot_itinerary_s : ltac2:(zQ "i50!h9!hq7!ik1!j4!hrb!hqe!kk4!pg2!ho6!np7!ipa!nq8!pga!iqf!is0!r9!pd!q8!r2!ph1!ph9!pi1!ola!on2!oob!ot0!oq4!ou9!ora!pi8!pif!pj5!pjd!pk5!pkd!pl5!pld@2$b@3$9@2$1@2$1$0$0$0@4$6@2$1$0$0$0@4$6$0$0@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$h6@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$h7@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$h8@4$6@2$1$0$0$0@4$6$0$0$h2$h2$h1@2$b@3$9@2$1@2$1$0$0$0@4$6@2$1$0$0$0@4$6$0$0@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$ha@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$hc@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$he@4$6@2$1$0$0$0@4$6$0$0$h1$f$h0@2$b@3$9@2$1@2$1$0$0$0@4$6@2$1$0$0$0@4$6$0$0@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$h9@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$hb@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$hd@4$6@2$1$0$0$0@4$6$0$0$f$f$h0@2$b@3$9@1$d$a@3$eNhk3$i4$h5@2$c$a$i1@2$b@3$9@1$d$a@3$eNhi3$i2$h3@2$c$a$hf@3$9@1$d$a@3$eNhk3$i3$h4@2$c$a$i0").
Proof.
ltac2:(KReplay.run1z (kr_t_AsTail_usage_defs ()) ["FPX1"] "##cTp%0p%1p&0p;2p;1p;3p;<p;4g009`j2zTg001Wj10Tg002<j11Tg0086j3ETg01Rfk10:Tg005Mj1ATg000Pj16!sT$aj1;Tg00Sej12Tg003?j1BTg00TDj3\Tg0076j1{Tg01SHj3HTg01TQj3@Tg00UKj2=Tg01UZk208Tg01Vcj2~Tg01Wlj2}Tg01Y5l<wTg01ZCj2`!ti$Pj2O!s/$kj2bTg009Ej4e!th$0k105!sT$ej4STg01[Ej3vTg004Fj3d!t`$Vj3!sJ$\Rk204Tg00:@k301Tg01][k103Tf0R0#1#1#0#1p=u%00#0p=4%1!s-$7%00#Ap=hg01^`R1P1f1R2P0CSp=a%0!sZ$9%10!sf$0p=:!s2%1#0p=mf2R3P1P!sU&]!sU$!sA%[!t5$#!t%$<!sY$p=N!sF'1p=c!sm&p=y!t'&p=fg00AUR4%B07d2p=K%20#2p=|!s-$#2#2p=Z!s2&p=n!s<+!s$'p=o!s:4!s$3p=x!sJD!s$Cp=_Ad420p=^%00#;p=l%A0#Bp=?!ul%A#Bp=F!w#$!uZ%Yg01_>R5%63%62=55035p=GA55209553p>02f4R6f3R7!s;+5!s#$p=X!sY&p=t!vs&p=C1=73?@20p=s!wW'!s$+p=J!wD'0p=D!s2+!s$'p=Wg01`Eg01a1?d73=d42;d0p=V!sr+p=kg00XPR8,=20040p=U!uG%!sg$T%03#;,=7!tR%>!t2%;,=2p=r!v3$,=2p>09!sZ&p=Q!xk%!xw$q1=73!vQ$7@2p=j!sd%!tD$i%;0!sa%0g00I3R9%A7,=6?@32;50p=I%17!u?&A!s>&=590p=PA5920959395979596p=3A@7!sF&>07%07#;!sZ0L%;7!s708f6f5;@6!s^+559p=p!t%+p=g!s2$p>06!tW,!s{1Mg00DES00B013208017$03p=R1z11R7/z1R3g00B`R2#0R0#0R6#1R:#0R;#0R<#1R=#0R>#0R?#1R@#1#u#4#7#hRA/aA%12RA#0RB#1RC#0S01#4S02#7S03#0S04#9S05#:#m#hRD5]7RE;EE%0BS06#1S07#1S08#4RB#9#[#:#<RF,aD%10RG#1RH#1S09#NS0:#0#7#7S0;#1#c#<RI5]7RJ=E3JS0<1aFF=]7IRI=E3IS0=g01a]RK$0:RL%1CRC#9S0>#7#uS0?#0RM#9S0@#0S0A#0#<RN%A0R0%1B!u@$O#0RP#1S0B#yS0C#f!uf$Qg00BARR#6RS%1;R;#0S0D#4RT#0S0E#;S0F'KRU%2RRR#2RV#|RW#ZRX#nS0G#2S0H#2#oS0I#2#xRY#xS0J#2S0K#2S0L#2RZ#2R[#2R\#2R]#2R^#2R_#n#Z#o#_#_R`#6Ra,^SRb%0<S0M!wg&c#l'KPU%0GRd#0S0N#0Re#0Rf#?Rg%B8R8P8%1:!xC$h#0S0O#4S0P#lS0Q,KSRi%|`#Z#x#_!s$%R`#2#ZS0R#2S0S#2S0T#ZS0U#2S0V#2S0W#2S0X#2S0Y#2S0Z#2S0[#n#oS0\#2S0]#2S0^#2S0_#2Rj%BQPi%6YS0`%fCS0a#0#9#4#:#[#FS0b%2j#ZRC%2C!s''BNRY%1ARk#?RlA\4a8Rm9\48S0c=\4lRn5\4P8%ZCRC#6!s^-!s'70kRo!t?&9Rp#0#[#Y#<S0d#BS0e%?2Rq%7p#:#:#FS0fP8%6ZS0g%6[S0h%6\S0i%6]S0j%6^S0k%6_S0l%nC#o!t:2%{5S0m3G3G402DXDX3G3G3GDX't!s+%S0nP8%1MRM#0R5#0RC#0#<PX%06R6#0R_#0R^#CS0o#0R]#;,KSS0pCsS0qP8%1C#<PXPUCsS0rP8%N5!s6,s%1^R5#A%1_RC#0R\#A5Ha%6VR[/^a%;2'K%?ARA%NkRk#NR2#1#JRZ#0S0t#4#D#WRp#?Rr%;6#BRsCVRt%D]R]#CRu#0#W#W#WRv#ARw%N]R]#1#k#JRx#1#D#W#<Ry3HRz%?6R{,UtS0uP[PAPrP!so$?HwyR|1Ut{S0v%1>#lS0w#BR>,^b!sL2}!sL%x%;@#BR@,^bS0y!sJ2~!sJ%z%1c#;,K!si,b!sE$w1Ub{S0{PU!s?,%9]#k#Y#m#J#[#<R]%0x!s1&x3HRc!sY%|1^S>!s[+>?H]xRb1U>{S0}1^S@!sA+s!sA$x1Us{S0~PS%TeS10PXP8C>S11%7f,rSRe%0HRH#1Rs#N#cR{#1R]#4#9#?RA7@X%4fRf#0S12-09SR@PXPl!}Z%1R>#7,rSRtPX%7]#FR]PS%C>S13PXPYPS%0:R:PXP8PS%4!~4$S14PXPAPS%1hRhPXPlPS%ChS15!sX%Q0OPX%[B#9#Y#FPS%1;RBPXP!t#$BS0O!sM'DPXPnPSQ0EPXg01bk%yZ!xY$Z#?RB;\nS0EPS%1=Rh#4R>PXPBPS%4?PX%?;S0DPSQ0MPX%YO#T#7#hS0M#BS16PzP|P}P~PwPcPbPx!s6DS%16R6#1RO#1R;#Q!v|'7PS%0ORO#4S18#0PXQ0cC>S0cPS%C;PXPaC>S19PS%0<S1:#0#lR<PX!#8Q$1R;#f#9#qCjS1;PS%QO!s~'<!tP6C5PXP[C>S1=PSQ0QPX%1d!#6`$Q#4RO!}W$CsS1>PSQ0wPRP^CjS0wPS%;>PV%QoRo#f!t<%?PSQ0FPWQ08#7RV#1#T#9#c#i#c!sG$08PS!~e%1R>#!t9$ZRZ#NR^#4#:!s$-u#?C>S0F!y%$PX%1^!wf$^#0#J#J!sC$1@PS%Q5PX%0P#N#i!s$$FC>RPPS%CCPX%TT#7#9#?C>R5PS%4\S1A!vk%eC>S1BPS%Q\!v9'CPS%4;PXPiC>S1D!tv'QPXQ0pC>S0pPS%46R6#0!v@$S1E#CS1F#;Rd,KSC>R;P8Q0@#1#D!zt$8Q0A!s/'?#7R\!uj$9R?#CPW%1^!u?%P8%0\R\#0!s\$g!#67&1PXPU1=8NR^PW%?GS0?200Sf!{v%Q0N#1S0N#CS!t2&!yE%PXP81=SdPXP8200S!|M&!{~%!}^$4R:!u#&RfPSQ0PPX%6RRGPSPTPXQ0L#6PSQ1:PXQ0K!s2%8PXQ0J#6PSP6PXPfPSQ1A!|X'oPX%0{#7#FR{PS%CkPX%42#9#4!wA$F%A_-08S%0p!#6A$%Cv#<Rv5HSQ0:#:,rSQ09#0Rp#m#<'~AH[yv%Au%WV#<'}Q01#1!ss$W#<Q0>#DRV#0Ru#4#D#<'}!ub&[1rSpPXQ0;#9#:#FPSQ06#DPXQ0G!u:$07#CPXQ0H!s4%2PXQ0I#6Q0d,=8PXPG%ho,~^!{y$8%1VRV!t0%PXQ0B#0#:#:Cj!s@'0R^#yPX%BDP8%TV!t6%4#1#m#T#FP8%0^#7PXQ03#N#Y!s:&1u#YPXQ05#0#7!s:%Q0a#1!uB$9#cPXPr!sM%:#7#:Ru#0PRPq!s9$!s/'h#[Rh#0#k#:!s9&fh#7#i!s3&0MPX%B!t;$\PW%B0P8%Q?PW%?ZRZP8%1>#DPWPZP8Q0t#Y#cRZ#9!z_%%7Z!zs%%{9DIDPDI!s+$!s-%!s2'P!s-$3H07DLD8D8Fp3gD3D8!s$3Fp!s+&!sm'IR9+06!sS$!s$+RZ!s4/DMD8DLDLDM!s&$M!s0+L!t3&!s$&M<w,`KRW;EWR>PNP0Q0MPUQ0yPUPgPAPl1KS<R<Q16P<Q0`Q0bQ0RQ0SQ0TQ0DPBPlQ0U#6Q0VQ0WQ0XQ0YQ0ZQ0[Q0EPnPYP]PlPAP8A\4m8Q0\Q0]Q0^Q0_Q!#A#$:02lm!#A%4,t`Q0qQ0rQ0s%AC%A=5HaRaPzQ0uP|Q0vP}Q0xP~Q0zPwQ0{PcQ0|PbQ0}PxQ0~!#8tBQ11A@eX[ReA@@X8R@A@tXARtQ17Q0cQ19Q1;Q!#8%4Q1=Q1>Q0wQ1?Q08Q0FQ1@PS%DsPXPGQ1BQ1CQ1DQ0pPS%QHPXQ0lC>PS%4!~\$kPSQ1EPXQ0jPSQ1FPXQ0i!#8o%Q0hPSPOPXQ0gPSQ0NPXQ0?PSQ0APXQ0fPSQ10PXPqPSQ1!||$ePSQ13PXP{PSQ14!#3E%15PXQ0C#q#FP9!yZ-L!xq-85g;D3D89gP5!yJ0!s$4!y4&5=EL5RPPNP0PQPU!s$$gP8P8PiQ0n!wo+P!wfoPeP@PtPZ!te>Z=ELZRt'OR@'ORe'ORx'O1b3EQ0<Px1b3JQ0=Pe1b3IP>P@1bLWPPPt1bL51bLZCe!s$'g00>L$05RZQ00/zZR5g00EQRtg019@CRPZP5Ptg01<jCR'a!s5+@UCR5]7P7P1P1P1g01cWRPPPCSg01ddRPCS5E3!sU+D!sq/Gh!sq0f4!sq0PPg01g@R!sq%hURW!sq1KP!sq-O;!sq0if!sq2PPCSP!sg%g01k3g01l@5vjg01mM,`K5ELg01n[g01oi5v`g0217!s>'22Eg023S!sV$24a!s>%'O!s$'do"). Qed.

(* [comment removed for export] *)
Lemma ot_itinerary : ltac2:(zQ "j20!h9!hq7!ik1!j4!hrb!hqe!kk4!pg2!ho6!ipa!np7!nq8!q8!pga!iqf!is0!r9!pd!s8!pm4!pmb!pn2!pn8!pnf!npd!nt2!nte!nua!nv6!og2!oj0!oh8!po6!oje!oi4!poc!okc!pp2!pp7!ppd!nh0!mu1!pq3!pqa!pr1!pr8!prf!ps6!psc!pt3@2$b@3$a@2$1@2$1@2$1$0$0$0$0@4$6@2$1@2$1$0$0$0$0@4$6@2$1$0$0$0@4$6$0$0@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$h8@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$h9@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$ha@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$hb@4$6@2$1@2$1$0$0$0$0@4$6@2$1$0$0$0@4$6$0$0$c$c$h2$c@2$b@3$a@2$1@2$1@2$1@2$1$0$0$0$0$0@4$6@2$1@2$1@2$1$0$0$0$0$0@4$6@2$1@2$1$0$0$0$0@4$6@2$1$0$0$0@4$6$0$0@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$hc@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$hd@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$hf@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$i2@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$i5@4$6@2$1@2$1@2$1$0$0$0$0$0@4$6@2$1@2$1$0$0$0$0@4$6@2$1$0$0$0@4$6$0$0$c$c$c$h0$h1@2$b@3$a@2$1@2$1$0$0$0@4$6@2$1$0$0$0@4$6$0$0@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$i0@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$i3@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$i6@4$6@2$1$0$0$0@4$6$0$0$h0$h0$h1@2$b@3$a@2$1@2$1@2$1$0$0$0$0@4$6@2$1@2$1$0$0$0$0@4$6@2$1$0$0$0@4$6$0$0@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$he@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$i1@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$i4@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$i7@4$6@2$1@2$1$0$0$0$0@4$6@2$1$0$0$0@4$6$0$0$h0$c$h0$h1@2$b@3$a@1$e$9@3$fNhg3$if$h5@2$d$9$ic@2$b@3$a@1$e$9@3$fNu3$ie$h4@2$d$9$i9@2$b@3$a@1$e$9@3$fNhg3$j0$h6@2$d$9$ia@2$b@3$a@1$e$9@3$fNs3$id$h3@2$d$9$i8@3$a@1$e$9@3$fNhg3$j1$h7@2$d$9$ib").
Proof.
ltac2:(KReplay.run1z (kr_t_AsTail_usage_defs ()) ["FPX1"] "##nCp%0p%1p&0p;2p;1p;3p;<p;4g009`j2nTg002<j11Tg001Wj10Tg0086j3LTg01Rfk10ATg005Mj19Tg000Pj17!s]$aj1!sA$Sej12Tg003?j1=Tg00TDj3_Tg0076k100Tg01SHj3JTg01TQj3;Tg00UKj2BTg01UZk20@Tg01Vck209Tg01Wlk208Tg01Y5l<kTg01ZCj2N!tl$Pj2Y!s/$kk205!tc$0k10>!sL$ej4ETg01[Ej3jTg004Fj3h!t[$Vj34Tg01\Rk20!tw$9Ek40<Tg00:@j3qTg01][k101Tf0R0#0#0p=:%1!s-$I%00#1p=6%10#1!sB%T!s2%1#0p=a%00#9p=rg01^`R1P1f1R2P0CEp=]!sb$!sZ%^%00#!s4$p=g!s2%!s^$8f4R3P1f3R4P1f2R5P2CE!se%fP5P1P!sr%>0;!ss%!sg$c!tO$p=?!ts$!s:%x!s2'1p=W!to&p=|g00AUR6%=07h2p=M%20#2p>04!s/$#2#2p=R!s2&p=l!s<+!s$'p=m!s:4!s$3p=QAh620p=`%00#Ap=p%90#=p=>!u`%9#=p=Gg01_>R7%72;40p=y%75%72=470547p=D!s3&94759474p=eA472!s6+9473p=V%74!s=+!s^$~!vl&p=@1B45?;20p=d!wi'!s$+p=O!w='0p=C!s2+!s$'p=Ug01`Eg01a1?h45=h62;h0p=[!sr+p=og00XPR8,B200=0p=Z!w=%!sg$P%05#A,B4!tR%<!t2%A,B2p=w%A0!s/$v%15!tB&!sQ,H!sl'1p=b%=09;52p=u!s<&p=}%10#9p>0:!y]'1p=t!s2+#!s:+sg00I3R9%94,B3?;5!w2%K%14!tC&9!s>&=490p=SA4920949594!s$$3p=3A;4!sF&>0?%A4!sX05f6f5;;!sK,549p={!sn+p>07!s3$p=i%92#=9;45!ss&6P3P420552P0H0<p=Xg00DER3Aq5207q4$01p=F!s4$9q34p>03!{k%&01!{m%2P2P1P0g01hUCEp=zAL452/Y0p=\1n11R0/n1R5/n1R4P5P0g00B`R2#1R:#0R;#1R<#0S00#:S01#IS02#0S03#6S04#T#a#rR=/]=R>%1:R?#1R@#^#g#^#8P=DfRA;LA1n41S05P4P5B0;0>=%0;S06#1S07#1S08#0S09!t<$6#c#T#8R>%02RB#1RC#1S0:#1S0;#?S0<#0#xS0=#1#6#?#8RDDfRE;LES0>1]>>>0;0DRF=L5FS0?P5P01]>=P>PDDfRD=L4DS0@g01a]RG$0ARH%1<R<#6S0A#W#6S0B#0RI#6S0C#0S0D#0#8RJ%9BRK%1;S0E#1S0F#0S0G#1S0H#|S0I#1#x#rR;g00BARL#7RM%0B!u5$N#0RO#1RP#0RQ#:RR#0S0J#AS0K'MRS%2LRL#2RT$04RU#RRV#lS0L#2S0M#2#mS0N#2#QRW#QS0O#2S0P#2S0Q#2RX#2RY#2RZ#2R[#2R\#2R]#l#R#m#Q!s$%R^#7R_,`MR`%0ORO#0S0!tO$S#1Ra#p'MPS%0CRb#0S0T#0Rc#0Rd#>Re%=8RfPf%1NRN#0S0U#0S0V#:S0W#pS0X,MMRg&04^#R!t9+2#RS0Y#2S0Z#2S0[#RS0\#2S0]#2S0^#2S0_#2S0`#2S0a#2S0b#l#mS0c#2S0d#2S0e#2S0f#2Rh!st%g#2S0h#2S0i#RS0j#2S0k#2S0l#2S0m#2S0n#2S0o#2S0p!st%q#2S0r#2S0s#2S0t#2Ri%=;Pg%7WS0u%1<#IS0v#0#^#T#c#GS0w%2i#RR<%2<!s''=JRW%>?RjA_6_fRk9_6fS0x=_6jRl5_6Pf%R<R<#7!sZ-!s'70?S0y!t:$6R?#0#c#W#8S0z#=S0{%>2Rm%I?#T#T#GS0|Pf%7XS0}%7YS0~%7ZS10%7[S11%7\S12%7]S13%l<#m!t92&007R7'y3DCeDVDV3D3D3DDV3DCeC~S14Pf%1IS15!{E$0R<#0#8PV!ze%0R]#0R\#@S16#0R[#A,MMS17CdRZPf%1<#8PVPSCdR<Pf%?I!s5+I%1]RY#0RX#99J_8%7TR8/`_%A2'M%>:R:%1@S18#?S19#1#OR@#0S1:#:#C#US1;#>R2%AB#=R?C[Rn%C[R[#@S1<#0#U#U#US1=#9Ro%?[R[#1#o#ORp#1#C#U#8Rq3JRr%>BRs,ZnRnP8P:P2P?C[Rt?JoqRu1ZtsRt%1!{b$Rv#1#pS1>#=Rw,``!sS+x!sS$y1ZxsRx%0v!sO$A#=Rz,``S1?!sO+{!sO$|1Z{sR{%1a#A,M!sm,`!sD$o1Z`sR`PS!s>+a%6[#o#W#a#O#c#8R[%0p!s1&p3JR}1ZasRa1`Mw!sZ+w?J[pR~1ZwsRw1`MzS1@!sC+?!sC$p1Z?sR?PM%PcS1APVPfC<Rc%Id,wMS1BQ0:#0!#69$1C#?#6#?S1D#1Rs#:#6#>R[7;VS1E%0dS1F#0S1G#0S1H#0,vMS1I?;VjS1J!~a%1Rd#I!s~$K%Is#GS1L!sd$MPM%@dS1NPVPWC<S1OPM%0NRN!t]$HS1PPM%:NS1Q#0S1RPVP[C<S1SPMQ0U#1!sN$jCHS0UPM%@NS1T!so'UPMQ0VPVQ0E#6#b#W#GCHS0EPM%1PRNPVQ1LCHS0V!s_&V!s_'WPMPQPVPlCHS1XPMQ0JPVg01bk%1@S0J#?#o#OS1Y#>R@;_lS1ZC<S1[PM%1OS1\#:S1]PVP@C<S1^PM%0vPV%>PS1_C<S1`PMQ0RPVQ0F#I#a#g#rS0F#=S0RCHS1aPrPuPyP|PoP}P~PM%1!#8W$P#1Rv!v4%RNPM%0PRP#:S1b#0PVQ0xC<RdPM%@vPVP_C<RvPMQ0S!#7S$0#pS1cPV%1YRY#1S1d#1#b#6#6#>CdRsPMPP!t%&P!tN2pPM%1\S1e#@PVP8C<S1fPMQ0XPV%1bS0X#0S1g#:R:!~S$CdRzQ1>,BMS1>%9\7uLS1hQ1]!y&$]Q0y#}S0y#?#g$0:7uTS1iQ0K,BMS0KQ08#IS08#?#C#W!wz$x!sL$US1jPM%0BS1k#1RBPVQ1!u>$Y#?R\#t#s!s$$6#>CHS1lPM%@BPV%1\!~N$\#0#O#O#>C<S1mPMQ1ePVQ0G#0#?!sb$!y/$GPM%@YPV%PR#b!sR%ePM%:XS1n!w%%{C<S1oPMPX!z['pPMQ1d#:PVPgC<S1dPMQ1k#0RXPVQ17CHS17!sj&k!sj%X#1S0X#@S1q#ARX,MMC<S1rPfQ0C#1#CPVPfPfQ0D!s/'B#IRB#1S0B#6S0D#@PU%1\!uF%Pf%0BS0C#0!s_$ePfQ15#1RB#1PVPS1BfJR\PU%>CS15Q1G,vM!s}$MQ0T#1S0T#@S1G!s9%%0:S1sPVPf1BM!uW$Q1Q!sW,1!|X$!~o&:S1V!u4&S1QPMQ0WPV%7LRCPMP!{A$Q#7!z=$PVQ0P!s2$1bPVQ0O!s2%kPVQ!s_$1nPVPWPMQ16PVQ1D#0#I#GS1DPMQ18#@PVQ19#:#^#b#G%9]-0@MQ1;#0!#7g$Q1=#@#8R]5JMQ0<#T,wMQ0;#0RR#a#8+09AJ8q]Q1<#9Q08#U#8+08Q00#1#^!sg$0A#CR]#0Rq#:#C!sE$!uv&81wM!uB$=#6#T#GPMQ06#CPVQ0L!uT%7!tn$0M!s4%1!xO%N#7Q0z,BfPVPCQ0y#r-09\!|Y$f%1]R]!t6%PVQ0H!z?&GCd!sB'0R\#|PV%==Pf%P]!t=%3#1#a#P#GPf%0\#IPVQ02#?#W!s:&1q#WPVQ04!v\$!s:$Q0v#1!uJ$6#6#?PVP2Pf%|q#g#TRq#0PLPm!s`$!s/%Q1\#1#cRq#0#o#T!sD+#x#t!s3&0BPV%=>!zg&PU%=K!zf$#}PUQ1Y#>R!sB$B!{'$UP>PfQ1:#W#6#?R>#6!{5%%I>!{I%&009DKDSDK!s+$!s-%!s2'S!s-$3H0?D5D5D5F{407D3!s3%!s$/F{!s+&!sn'KR9'iD3D3R>!sY%!s$$RB,ip!s3'!s$1M<k,NGRq;LqR2PJPKQ0FPSQ1?PSPeP[PjQ1c,MMR\PhQ0RP\Q0uQ0wQ0gQ0hQ0iQ1_P@PjQ0j#7Q0kQ0lQ0mQ0nQ0oQ0pQ1ZPlPWQ1LPjP[PfA_6kfR6PjPkQ0qQ0rQ0sQ0t/y7!#BS8PZP<PI%9Y%9O5J_ROPrPnPuPtPyPxP|P{PoP`P}PaP~PwPpP?PcQ1B?;V8RYQ1I?;VfRlQ1K?;V[R]PNPdPvPsP!#801Q1fPzQ1hQ1iQ1jQ1lQ1mQ0GQ1ePMQ1C#@PVPCC<Q1oQ1pQ1dQ17Q1rPMQ0:PVQ13CH!~}$#!s4$2PMQ0X#PPVQ11PMQ1q!{|$10PMQ1g!s>$0~PMQ1s!|<%}!#4:$!sV$5PMQ1G!s>%|PMQ1APVPmPMQ1HPVQ0{PMQ1NPVQ!~{%R!#3?&TPVQ0I!{N$GP9!y;5!s$&!xz'9!xz8!xv&V=LHVRMPJPKP;PS!s$$ePfPfPgQ14!wV%P!wMFPYPlP]PB!t16B=LHBRO!z&%9#1#6#U#8RmPSQ1@!t=$8P_P\P^%=m!z-,YQ0ZQ0[!z-%_Q0\#7Q0]Q0^Q0_Q0`Q0aQ0bPfPjPWP[PfP8PfP6Q0xPkQ0cQ0dQ0eQ0f!z$DQQ0J#95J_R_!u;+!yM/!um>1i?9!vr89=LH9R]!vr'!u\'!vs1Q1>%9b7uLQ1]PT%1!#4f$6Q0KPUQ1F#}#a#^#b#g#CPcQ1EQ1JQ1MQ1OQ1PQ1SQ0UQ1UQ0EQ0VQ1WQ1XQ1[Q1^Q1`Q1aP_!wxD!u[JP?Q1f1iz>!#3T8!s$%H06H06!uv+>=LH>Rz'YR?'YRp'YRw'YR~'YRa'YR}'YP4PAQ0>P}Q05PEQ0?PaP5PFQ0@P~P4PDP2PwPHPqPMPpPHPVPOP?PHPBP]PzPHP9205H>DX!s$1P!#Z%&>L$0>R>1n3>R3g00EQR9g00F[CFP>P3P9g00L\CF']!s5+PA!sB-XnCFD!#dF$0P1P1P1g01ddRzPzCER]g025oCEPzCEQ!#Z?$!s`+`0!sm-cV!t10g>H036020!s8+jc!sT,27C!tC0]PzCEg01g@R]CE,z!t4-28N!s^-9Z!t4/2:f!t4'1!sl$!sc$0!v9%!tG+nH!sg,120!sg/15X!t'-<2!tc$!u|&!tc%!sy%5PHg02=>g02>J5jig02?V,NG!s=$@cg02B05jhg02C=!s='DJg02EW!sT%Fd!s='H1g02I>5j^g02JK,NGg02KXg02Le!sR%N2,NG5LHC\!s$1do"). Qed.
End FPX1.
(* [comment removed for export] *)
