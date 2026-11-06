(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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
Ltac2 kr_t_AsTail_rderr_defs () := KReplay.lz_vm "#$%3I47Corelib4Init9Datatypes4list00K89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX24expr02C13~~~K!t5+7Numbers7BinNums8positive02!sKG1!sK=1Z03!t}c1!t}&!smb3!ulC1Z02!t3]8sidecond!t~+!x4A1!sFB2!xt25Logic2eq00!s@83and00K!s[;1K!s[<1!z-=prod00C!sF;3fst!sC=sndC!vm\5s_log!vh%!sl^carry!sl&7!slN6SymAux;log_covered!sl%I!y7f0!y7Cbool!}1#ELinuxProcessSemantics5Riscv5Instr;branch_!s~$5!sXG5aluop06!sRN!zi=3nat!~]?!#3&+3I!udA0!v+B1!w?]9sym_state!w@'!sr]7scripts!sp'c!spO2AsAAsTail_rderr_defs2rB!sqk4scsB!uXc6kentry!uWm4knV!ssl:ot_regions!wGmC!wGoC!vVnC!y|nD!u[o!ssl3knC!#5dA!#3j#2!#><b4!t4&!#9A\sadd!#?se!#8U+6!uo'!#85Q3!#@Q?1!yCgE!yCoE!{xnE0!wFc!x}%7!wBZ6!sXT1!sXT4!x0gF!x0o!ssl5knF0_!#3CkrF!#5wk5!u]#0!u^p!#7cmG!x<oG!}FnG!u[nH!u[oH!u[nH0!zpmG3!zpo!stnknG3!u^nH!u^pH!u^oH!u^oF4!#40o4!#40n4!zvo!u^pG!u^oG!u^oH!u^pH!u^oH!u^'!#SQ;6option!#aX^!#Oe&!#Es&!sod2!sok1!sok5!sok7!sok!#KcV2As;AsStdioCall9s!s0#_res!#b^C!y<'!#b`=!#a-#1C!t^^:!t^%call!t]%!#`S\4s_pc!{`3!#Lh50!#XC\!#J3$!#Jz&!#^XL7!sRN:!~cfAEXIT!v%&!yCi!ujU2!u>e7AMEMCPY!#5sj;ASTRNLEN_TR!szk2rI!sqk<ASTDIO_WRIT!#Rkk3rI3!srn!#:Gk3s!#I?l3kn!#J3nO!#Rsm!#I?m4kn!ssnsc!sso!#I>m4knH!u]o!sso!#I=m4kn!ssnsc!sso!#F\m!x<#!u]o!ss'".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc4listhc4conshc3nil89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Ash1AsTail_rderr_defs4FPX1~~~~~~k85AEXITk88AMAINEPIk87AMEMCPYk84ARIPk8cASTDIO_WRITEk8bASTRNLEN_TRhc3nat37Corelib4Init7Decimaltc2D0tc2D2tc3Nil37Corelib4Init3Nathg2bof_num_uint37Corelib4Init6Numberhi3bUIntDecimal79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymExec23SX2~~~~~~hk77scriptshc4boolhk73SCRhk74exprhc4prodhk79sym_statehk78sidecondhc4truek85FUELTk85STOPThk78sym_exec69OSSVerifyaboost_jsonafuzz_parse6images4Asan1M~~~~~~huafloaded_segmentshk76kentryhc3fsthk75carryhk75s_log79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsbAsStdioCall~~~~~~il49stdio_reshk74ELithc6optionil44SCR_il4astdio_call37Corelib5Lists7ListDefis93map04Npos69OSSVerify6Proofsaboost_jsonafuzz_parse3libcRefMemcpyLib~~~~~~iudbcallee_kepthk74ridx35stdpp9bitvectorbdefinitionsjk32bv46Stdlib5Arith8PeanoNat3Natjm63eqbhc4negbhc3orbk87KEPT_MC36Stdlib5Lists4Listjpf6filteriudccallee_saved3h5LinuxProcessSemantics5Riscv5Instrjsc7ALU_ADDhk74EAluhk74EVarhg23addk83spxk83FMTis93seqhc4pairjsc7ALU_ANDjsc7ALU_SRLhk72SAhk75KWordhc3appk85OT_FRhk74KImghk76KRangehk73KWr79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As0d1A1s1P1r1i1n1t1f1F1i1r1s1t~~~~~~kn88kn_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AsShadow~~~~~~kt57AAPP_HIkt56AHI_LO79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AsSxKit~~~~~~li84shknk89OT_SHOFFSk88ot_cellshk76KAlign46Stdlib6ZArith6BinInt1Zloe3subhk75saddrjsc5aluopjsc5mulophc5falsek82PXk8cnot_px_rangek8aOT_SHOFFS2k86OT_SHXk88px_rangek85shxknk84knV0k84srV0hk72SShk76sentryhk72SEk8bAMEMCPY_RETk84knC0k84srC0k83knCk84srD0k8cASTRNLEN_RETk84knE0k84srE0k85knF0_k84srF0k84knG0k84srG0k84knH0k84srH0k84knI0k84srI0k85knG30il46sc_retk85knH30k84scG3k85srH30k85knI30k85srI30k85knF40k85knG40k84scF4k85srG40k85knH40k85srH40k85knI40k85srI4069OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SymAux~~~~~~ni87sregion37Corelib4Init5Logicnmc2eqk82rBhc3sndnmc3andk8aot_regionsk84scsBni8blog_coveredk82rCk84scsCk82rDk84scsDk82rEk84scsEk82rFk84scsFk83rF0k85knF00k85scsF0k82rGk84scsGk82rHk84scsHk83rG3k85scsG3k83rH3k85scsH3k83rF4k85scsF4k83rG4k85scsG4k83rH4k85scsH4hk74s_pchc4Somek84knF4k84knG3k83knHk84knH3k84knH4k82rIk83rI3k83rI4k84scH3k84scH4k84scOFk84srF4k84srG3k83srHk84srH3k84srH4" s.
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
Definition OT_FR : Z := 6000.                (* [comment removed for export] *)
Definition FMT : Z := 0x20d0d.
Definition NPRE : Z := 19.
Definition NSUF : Z := 1.                (* [comment removed for export] *)
Definition IHI : Z := 0x80000000.            (* [comment removed for export] *)
Definition BUF_LO : Z := (-592).
Definition BUF_HI : Z := (-512).
Definition PX : ltac2:(zQ "10!hpf$0") := ltac2:(zQ "10!kg3@1$0Nod").            (* [comment removed for export] *)

(* [comment removed for export] *)
Definition srV0 : ltac2:(zQ "20!j4!hpf@1$0$1") := ltac2:(zQ "90!t6!hpf!kgb!kg3!iq2!kh2!kh8!iu0!khe@4$7$0$1\1i$0M0\1i$0$1^1@1$4Z\1n$0M0\1n$0$1^1@1$4+nvho4\2n0$0M0\2n0$0$1^1@1$5-v0\2n1$0M0\2n1$0$1^1@1$3@2$2Ni3^4\2n2$0M0\2n2$0$1^1@1$4+mvkjt8\2n3$0M0\2n3$0$1^1@1$3@2$2Ni3^6\2n4$0M0\2n4$0$1^1@1$3@2$2Ni3^7\2n5$0M0\2n5$0$1^1@1$3@2$2Ni3^8\2n6$0M0\2n6$0$1^1@1$4$6\2n7$0M0\2n7$0$1^1@1$4+hrpvg8\2n8$0M0\2n8$0$1^1@1$4+hrpvg8\2n9$0M0\2n9$0$1^1@1$4$6\3n10$0M0\3n10$0$1^1@1$5-r0\3n11$0M0\3n11$0$1^1@1$3@2$2Ni3^e\3n12$0M0\3n12$0$1^1@1$3@2$2Ni3^f\3n13$0M0\3n13$0$1^1@1$3@2$2Ni3^h0\3n14$0M0\3n14$0$1^1@1$3@2$2Ni3^h1\3n15$0M0\3n15$0$1^1@1$3@2$2Ni3^h2\3n16$0M0\3n16$0$1^1@1$5-r0\3n17$0@1$3@2$2Ni3^h4@2$8N0Ni0").

(* [comment removed for export] *)
Definition ot_cells : ltac2:(zQ "40!hq7!h9!j4!t6@1$2@2$0@2$0$1$3$1") := ltac2:(zQ "60!h9!hq7!t6!ki5!jb!k2@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrnki0N8+hpstl4@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrnlp8N8+hqlmi4@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrnlq0N8+hqlqi8@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrnlk8N8+hqmhm8@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrnjt8N8+hqlli8@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hsgij8N8+nvvvogg0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hsgvh8N1+1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hsgvh9N1+1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+ilhtrcN1+1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+ilhum3N1+1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrpvg8N4+5@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrpvi8N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrpvj0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrpvk0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrpvl0N8+hprtu8@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrpvm0N8+nhkrv0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrpvm8N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrpvo0N4+2@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrpvp0N4Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrpvp4N4+vvvvvvvf@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrpvp8N4+vvvvvvvf@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nvvvshp8N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nvvvshq0N8Z@1$5@2$1@2$1$0$2$0").

(* [comment removed for export] *)
Definition OT_SHOFFS : ltac2:(zQ "20!j4!h9@1$0$1") := ltac2:(zQ "30!h9!jb!k2@3$1$0-il0@3$1$0-ije@1$2$0").
Definition OT_SHOFFS2 : ltac2:(zQ "20!j4!h9@1$0$1") := ltac2:(zQ "30!h9!jb!k2@3$1$0-il0@3$1$0-ije@3$1$0-ijd@1$2$0").
Definition OT_SHX : ltac2:(zQ "20!j4!hpf@1$0$1") := ltac2:(zQ "90!jvb!iq2!jv0!kg3!hpf!jb!kic!kj7!k2@3$5$4@3$0$6@3$0$2@3$0$7@3$0$2@3$0$2@1$3N2@1$3Nod@1$1-1@1$1+3@1$1+nvvvogg0@1$1-8@3$5$4@3$0$6@3$0$2@3$0$7@1$3N2@1$1+3@1$1+nvvvogg0@1$1-8@3$5$4@3$0$6@3$0$2@3$0$7@3$0$2@3$0$2@1$3N0@1$3Nod@1$1-ije@1$1+3@1$1+nvvvogg0@1$1-8@3$5$4@3$0$6@3$0$2@3$0$7@3$0$2@3$0$2@1$3N0@1$3Nod@1$1-ijd@1$1+3@1$1+nvvvogg0@1$1-8@1$8$4").
Fixpoint shxkn (l : list expr) : list kentry :=
  match l with [] => [] | e :: r => KRange e 0x20000000000 0x10007fff8000 :: KZero (SA e 0) (ELit 8) :: shxkn r end.

Definition knV0 : ltac2:(zQ "20!j4!ij2@1$0$1") := ltac2:(zQ "h40!ij2!kg3!jb!kk2!kk8!iq2!kl1!kl7!klf!km7!kn1!k2!ks9!lh3!lhe!lm5!lmd!ln9!lo4!lq6@3$6$0@3$2$0@2$h2@1$1N0+h0@3$2$0@3$9@1$1N0+nvvvogggggg0+ogggggggggg0@3$2$0@2$a@2$3@1$1N0@2$h3-o0$7$7@3$2$0@3$9@1$1N2$e$d@3$2$0@2$8+hggg0+mngg0@3$2$0@2$8+hqtgg0+hrngg0@3$2$0@3$4@2$3@1$1N0-r0N8@1$1N2@3$2$0@3$4@2$3@1$1N0-r8N8@1$5+ruro4@3$2$0@3$4@2$3@1$1N0-s0N8@1$1Nb@3$2$0@3$4@2$3@1$1N0-s8N8@1$1Nc@3$2$0@3$4@2$3@1$1N0-t0N8@1$1Nh5@3$2$0@3$4@2$3@1$5Z+nhkkh8N8@1$1N1@3$2$0@2$a@2$3@1$5Z+hrpvg8+u8@1$b$0@3$6$0@1$f$h0@1$c$h1").
(* [comment removed for export] *)
Definition not_px_range (k : kentry) : bool := match k with KRange (EVar 141) _ _ => false | _ => true end.
Definition px_range : ltac2:(zQ "30!j4!h9!ij2>2lo$1>2hi$1>2kn@1$0$2@1$0$2") := ltac2:(zQ "80!ij2!h9!jb!j4!lt0!lt5!km7!jr2\2lo$1\2hi$1\2kn@1$3$0@3$2$0@3$6$4^3^2@3$7$0$5^1").
(* [comment removed for export] *)
Definition kn_readd : ltac2:(zQ "30!j4!h9!ij2>3plo$1>3phi$1>2kn@1$0$2@1$0$2") := ltac2:(zQ "90!ij2!kl1!h9!j4!lm5!lu4!lv1!lva!mg5\3plo$2\3phi$2\2kn@1$3$0@3$7^3^2@3$1$0@1$8$6@3$1$0@1$4$5^1").

(* [comment removed for export] *)
Definition ssB0 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "50!k2!mgd!mh4!mhb!mi1@5$3+hpstl4$2@1$0$4$1Nk3").
Definition rB := Eval vm_compute in runT (SCR [false] [] []) ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_afterT rB knV0.
(* [comment removed for export] *)
Definition logM1 : ltac2:(zQ "20!j4!mi1@1$0$1") := ltac2:(zQ "70!mi1!jb!iq2!kg3!kk2!mib!k2@3$1$0@3$5@2$4@1$3N0-ijeN1@1$2+i0@3$1$0@3$5@2$4@1$3N0-ik0N2@1$2+mumf@3$1$0@3$5@2$4@1$3N0-ik8N8@1$2+ignimvninimligm4@3$1$0@3$5@2$4@1$3N0-il0N8@1$2+mhmlniigjqmpmsm3@1$6$0").
Definition knC0 : list kentry := Eval vm_compute in fst (fst (carry logM1 knB [])).
Definition srC0 : list expr := Eval vm_compute in sr_after_call_j srB KEPT_MC 67.
(* [comment removed for export] *)
Definition ssC0 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "60!k2!mj1!mjf!mk6!mhb!mi1@5$4$1$3@1$0$5$2Nm3").
Definition rC := Eval vm_compute in runT (SCR [] [] []) ssC0.
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC)).
Definition knC : list kentry := Eval vm_compute in kn_afterT rC knC0.
Definition srD0 : list expr := Eval vm_compute in sr_after_call_j srC KEPT_MC 99.
(* [comment removed for export] *)
Definition ssD0 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "60!k2!mj1!mkd!ml3!mhb!mi1@5$4$1$3@1$0$5$2No3").
Definition rD := Eval vm_compute in runT (SCR [] [] []) ssD0.
Definition srD : list expr := Eval vm_compute in s_regs (fst (fst rD)).
Definition knD : list kentry := Eval vm_compute in kn_afterT rD knC.
(* [comment removed for export] *)
Definition knE0 : list kentry := Eval vm_compute in kn_readd 0 131071 (kn_cut 0 (-1152 - 4400) (-1152) IHI knD).
Definition srE0 : list expr := Eval vm_compute in sr_after_call_j srD KEPT_CS 131.
(* [comment removed for export] *)
Definition ssE0 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "60!k2!mla!mm9!mn0!mhb!mi1@5$4$1$3@1$0$5$2Nq3").
Definition rE := Eval vm_compute in runT (SCR [false] [ELit 0] []) ssE0.
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
Definition knE : list kentry := Eval vm_compute in kn_afterT rE knE0.
Definition srF0 : list expr := Eval vm_compute in sr_after_call_j srE KEPT_MC 163.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FQMAX : Z := 61.
Definition knF0_ : list kentry := Eval vm_compute in px_range 1 FQMAX knE.
Definition ssF0 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "60!k2!mj1!mn7!mnf!mhb!mi1@5$4$1$3@1$0$5$2Ns3").
Definition rF := Eval vm_compute in runT (SCR [true; false; true; false; false] [] []) ssF0.
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF)).
Definition knF : list kentry := Eval vm_compute in kn_afterT rF knF0_.
Definition knG0 : list kentry := Eval vm_compute in kn_readd 0 60 (kn_cut 0 (BUF_LO + NPRE) BUF_HI IHI knF).
Definition srG0 : list expr := Eval vm_compute in sr_after_call_j srF KEPT_MCI 195.
(* [comment removed for export] *)
Definition knF00 : list kentry := Eval vm_compute in px_range 0 0 knE.
Definition rF0 := Eval vm_compute in runT (SCR [false; true] [] []) (SS AMEMCPY_RET srF0 [] knF00 195).
Definition knF0' : list kentry := Eval vm_compute in kn_afterT rF0 knF00.
(* [comment removed for export] *)
Definition ssG0 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "60!k2!mj1!mo6!mod!mhb!mi1@5$4$1$3@1$0$5$2Nu3").
Definition rG := Eval vm_compute in runT (SCR [false] [] []) ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_afterT rG knG0.
Definition knH0 : list kentry := Eval vm_compute in kn_readd 0 60 (kn_cut 0 (BUF_LO + NPRE) BUF_HI IHI knG).
Definition srH0 : list expr := Eval vm_compute in sr_after_call_j srG KEPT_MC 227.
(* [comment removed for export] *)
Definition ssH0 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "60!k2!mj1!mp4!mpb!mhb!mi1@5$4$1$3@1$0$5$2Nhg3").
Definition rH := Eval vm_compute in runT (SCR [] [] []) ssH0.
Definition srH : list expr := Eval vm_compute in s_regs (fst (fst rH)).
Definition knH : list kentry := Eval vm_compute in kn_afterT rH knH0.
Definition scOF : stdio_res := Eval vm_compute in sc_of 259 srH knH.
Definition srI0 : list expr := Eval vm_compute in sc_sr scOF.
Definition knI0 : list kentry := Eval vm_compute in sc_kn scOF.
(* [comment removed for export] *)
Definition ssI0 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "50!k2!mq2!mq9!mhb!mi1@5$3+hpsunc$2@1$0$4$1Nhi3").
Definition rI := Eval vm_compute in runT (SCR [] [] []) ssI0.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition knG30 : list kentry := Eval vm_compute in kn_readd (60 + 1) (60 + NSUF) (kn_cut 0 (BUF_LO + NPRE) BUF_HI IHI knF).
Definition ssG30 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "60!k2!mj1!mr0!mod!mhb!mi1@5$4$1$3@1$0$5$2Nu3").
Definition rG3 := Eval vm_compute in runT (SCR [] [] []) ssG30.
Definition srG3 : list expr := Eval vm_compute in s_regs (fst (fst rG3)).
Definition knG3 : list kentry := Eval vm_compute in kn_afterT rG3 knG30.
Definition scG3 : stdio_res := Eval vm_compute in sc_of 227 srG3 knG3.
Definition srH30 : list expr := Eval vm_compute in sc_sr scG3.
Definition knH30 : list kentry := Eval vm_compute in sc_kn scG3.
(* [comment removed for export] *)
Definition ssH30 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "70!k2!mr8!ms2!msa!mt1!mhb!mi1@5$5@1$1$3$4@1$0$6$2Nhg3").
Definition rH3 := Eval vm_compute in runT (SCR [] [] []) ssH30.
Definition srH3 : list expr := Eval vm_compute in s_regs (fst (fst rH3)).
Definition knH3 : list kentry := Eval vm_compute in kn_afterT rH3 knH30.
Definition scH3 : stdio_res := Eval vm_compute in sc_of 259 srH3 knH3.
Definition srI30 : list expr := Eval vm_compute in sc_sr scH3.
Definition knI30 : list kentry := Eval vm_compute in sc_kn scH3.
(* [comment removed for export] *)
Definition ssI30 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "50!k2!mt9!mu1!mhb!mi1@5$3+hpsunc$2@1$0$4$1Nhi3").
Definition rI3 := Eval vm_compute in runT (SCR [] [] []) ssI30.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition knF40 : list kentry := Eval vm_compute in px_range (60 + NSUF + 1) 131071 knE.
Definition ssF40 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "60!k2!mj1!mu9!mnf!mhb!mi1@5$4$1$3@1$0$5$2Ns3").
Definition rF4 := Eval vm_compute in runT (SCR [true] [] []) ssF40.
Definition srF4 : list expr := Eval vm_compute in s_regs (fst (fst rF4)).
Definition knF4 : list kentry := Eval vm_compute in kn_afterT rF4 knF40.
Definition scF4 : stdio_res := Eval vm_compute in sc_of 195 srF4 knF4.
Definition srG40 : list expr := Eval vm_compute in sc_sr scF4.
Definition knG40 : list kentry := Eval vm_compute in kn_readd (60 + NSUF + 1) 131071 (sc_kn scF4).
(* [comment removed for export] *)
Definition ssG40 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "70!k2!mr8!mv1!mv9!ng0!mhb!mi1@5$5@1$1$3$4@1$0$6$2Nu3").
Definition rG4 := Eval vm_compute in runT (SCR [false] [] []) ssG40.
Definition srG4 : list expr := Eval vm_compute in s_regs (fst (fst rG4)).
Definition knG4 : list kentry := Eval vm_compute in kn_afterT rG4 knG40.
(* [comment removed for export] *)
Definition logNL : ltac2:(zQ "20!j4!mi1@1$0$1") := ltac2:(zQ "70!mi1!jb!k2!iq2!kg3!kk2!mib@3$1$0@3$6@2$5@1$4N0-il0N1@1$3+a@1$2$0").
Definition knH40 : list kentry := Eval vm_compute in fst (fst (carry logNL knG4 [])).
Definition srH40 : list expr := Eval vm_compute in sr_after_call_j srG4 KEPT_MC 227.
(* [comment removed for export] *)
Definition ssH40 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "60!k2!mj1!ng8!nh0!mhb!mi1@5$4$1$3@1$0$5$2Nhg3").
Definition rH4 := Eval vm_compute in runT (SCR [] [] []) ssH40.
Definition srH4 : list expr := Eval vm_compute in s_regs (fst (fst rH4)).
Definition knH4 : list kentry := Eval vm_compute in kn_afterT rH4 knH40.
Definition scH4 : stdio_res := Eval vm_compute in sc_of 259 srH4 knH4.
Definition srI40 : list expr := Eval vm_compute in sc_sr scH4.
Definition knI40 : list kentry := Eval vm_compute in sc_kn scH4.
(* [comment removed for export] *)
Definition ssI40 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "50!k2!nh8!ni0!mhb!mi1@5$3+hpsunc$2@1$0$4$1Nhi3").
Definition rI4 := Eval vm_compute in runT (SCR [] [] []) ssI40.

(* [comment removed for export] *)
Definition ot_regions : ltac2:(zQ "20!j4!nm1@1$0$1") := ltac2:(zQ "b0!h9!lqd!hq7!jb!ki5!kl7!kk2!k2!iq2!kg3!lq6@3$3@2$2$1$0@4$4$1$0@2$6@1$9N0@2$a-o0$5$5@3$3@2$2$1$0@4$4$1$0@2$6@1$8Z+hrpvg8+u8@1$7@2$2$1$0").
Definition scsB : list sidecond := Eval vm_compute in (snd (fst rB)).
Lemma factsB : ltac2:(zQ "h42!j4!hrb!ijc!hqe!hq7!hp1!no0!no6!ho6!k2!nob!np1!ij2!ikb!hs7!mgd!np8!nq5!nqc!ik2&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_rderr_defs ()) ["FPX1"] "p;1p;3p;4p;2g0000j13Tg000Pj1DTg001Wj10Tg002<j15Tg002aj1=Tg003?j16Tg004Fj3:Tg005Mj1@Tg005kj4?Tg0076j19Tg007Vj3>Tg0086j31Tg008Pj24Tg008kj27Tg009Ej4<Tg009`j28Tg00:@j32Tg00:]j3;Tg00;:j1CTg00<@j3BTg00=Fj2ATg00>LR0#3R1g00?Wg00@7g00@ig00AUg00BA#Dg00B`R2#0#0#5R3#0#5#0#0#0#0#=#63:%=2#63:%53#@#6C?%90R35>0R0;10A1133R2g00CER4g00CeR5;15R6'41710P2P617131745C<C<g00DER61861g00EQg00F[32R27;1g00Gf511g00I3#3R01801%34A2612#CR2g00J<%943B327;1=113g00KI/A2=145'4'4do"). Qed.
Definition scsC : list sidecond := Eval vm_compute in (snd (fst rC)).
Lemma factsC : ltac2:(zQ "h42!j4!hrb!ijc!hqe!hq7!hp1!no0!nrb!ho6!k2!nob!np1!ij2!ikb!hs7!mjf!np8!ns0!nqc!ik2&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_rderr_defs ()) ["FPX1"] "p;1p;3p;2p;4g0000j13Tg0076j18Tg0086j30Tg008Pj21Tg008kj27Tg009Ej46Tg009`j25Tg00:@j32Tg00:]j34Tg00;:j1;Tg00<@j3:Tg00=Fj29Tg00>LR0#3R1%80R0;00R2g00CER3g00CeR4;04R5,121710R6P2P5P61734C6C6g00DER61561g00EQg00L\32R5741g00Mg501g00I3#3R21521%33A2615#;R5g00O4%833:32741=010g00KI/95=034'1'1do"). Qed.
Definition scsD : list sidecond := Eval vm_compute in (snd (fst rD)).
Lemma factsD : ltac2:(zQ "h42!j4!hrb!ijc!hqe!hq7!hp1!no0!ns7!ho6!k2!nob!np1!ij2!ikb!hs7!mkd!np8!nsc!nqc!ik2&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_rderr_defs ()) ["FPX1"] "p;1p;3p;2p;4g0000j13Tg0076j18Tg0086j30Tg008Pj21Tg008kj27Tg009Ej46Tg009`j25Tg00:@j32Tg00:]j34Tg00;:j1;Tg00<@j3:Tg00=Fj29Tg00>LR0#3R1%80R0;00R2g00CER3g00CeR4;04R5,121710R6P2P5P61734C6C6g00DER61561g00EQg00PA32R5741g00QL501g00I3#3R21521%33A2615#;R5g00RY%833:32741=010g00KI/95=034'1'1do"). Qed.
Definition scsE : list sidecond := Eval vm_compute in (snd (fst rE)).
Lemma factsE : ltac2:(zQ "h42!j4!hrb!ijc!hqe!hq7!hp1!no0!nt3!ho6!k2!nob!np1!ij2!ikb!hs7!mm9!np8!nt8!nqc!ik2&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1z (kr_t_AsTail_rderr_defs ()) ["FPX1"] "##,,p;1p;3p;4p;2g0000j14Tg00Sej10Tg000Pj1;Tg003?j1GTg00TDj3BTg005kj4ATg004Fj3@Tg00UKj2>Tg00VSj4=Tg0076j17!s/$Vj3<Tg0086j32!s/$Pj26!s/$kj25Tg009Ej48!s/$`j29Tg00:@j33!s/$]j3:Tg00;:j1FTg00<@j3DTg00=Fj2ETf0R0#0#0p=C%0!s0$!s$,p=?!s:4!s$3p=1g00>LR0#4R1g00?WR2g00W^g00AUR3g00BA#0R4#0R5#0#C#?#1!s$2;R6g00XPR7#GR83BP6CA%;5=@36/>7P4P2P8C=%70R85<05<0R0;20A2188!t;$CER4g00CeR7;27R6'61510P2P615181547C8C8g00DER61961g00EQg00Xn33R27:1g00Z9521g00I3#4R01901%44A3612#F!t4$[F%743D337:1=218g00KI/E2=247'6'6do"). Qed.
Definition scsF : list sidecond := Eval vm_compute in (snd (fst rF)).
Lemma factsF : ltac2:(zQ "h42!j4!hrb!ijc!hqe!hq7!hp1!no0!ntf!ho6!k2!nob!np1!ij2!ikb!hs7!mn7!np8!nu4!nqc!ik2&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1z (kr_t_AsTail_rderr_defs ()) ["FPX1"] "##-^p;1p;3p;4p;2g0000j18Tg000Pj1=Tg001Wj17Tg002<j15!s/$aj1DTg003?j1:Tg004Fj36Tg00Sej10Tg005kj44Tg00\Sj4ETg00TDj3CTg0076j1B!s/$Vj33Tg0086j32!s/$Pj2;!s/$kj29Tg009Ej4@!s/$`j2ATg00:@j3<!s/$]j3?Tg00;:j1ITg00<@j3HTg00=Fj2GTf0R0#0#0p=>%0!s0$!s$,p=F!s:4!s$3p=1g00>LR0#8R1g00?WR2g00@7R3g00@iR4g00AUR5g00BAR6#=R7g00B`R8#7!s$$5!s$&7#5#D#:R936R:%D8#:R836%>6R;#>R<#0#F#1!s$2=R=C4P2P3%=;R;=648P=C4g00CeR8g00]ZP;A657==659C4P2g00^LP:P;C4P8g00_>P8P6P<P=CEg00XP#:R<9C5==C5<C4%B0R<530!s%/R0;20A21<<!uK$CER=?288R6';1910P5P6191<19=8C@C@g00DER61A61g00EQg00`03<R57?1g00a;521g00I3#8R01A01%8=A<615#I!t-$bH%B=3H3<7?1=21<g00KI/G5=2=8';';do"). Qed.
Definition scsF0 : list sidecond := Eval vm_compute in (snd (fst rF0)).
Lemma factsF0 : ltac2:(zQ "h42!j4!hrb!ijc!hqe!hq7!hp1!no0!nub!ho6!k2!nob!np1!ij2!ikb!hs7!nv1!np8!nv9!nqc!ik2&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1z (kr_t_AsTail_rderr_defs ()) ["FPX1"] "##,Ap;1p;3p;4p;2g0000j17Tg000Pj1:Tg00Sej10Tg004Fj36Tg001Wj14Tg002<j13!s/$aj1CTg003?j1BTg005kj4<Tg0076j1;!s/$Vj3@Tg0086j32!s/$Pj28!s/$kj29Tg009Ej4>!s/$`j2?Tg00:@j35!s/$]j3=Tg00;:j1FTg00<@j3ETg00=Fj2DTf0R0#0#0p=A%0!s0$!s$,p=G!s:4!s$3p=1g00>LR0#7R1g00CeR2g00]Zg00BAR3#AR4#:R5g00AUR6%:3R3%04#A#G#1!s$2:566g00B`#4!s$$3!s$&4#3#C#BR436C<g00?Wg00^LA6634P5C<%;0R55@05@0R0;20A2155R4g00CER3?222R6'81910P4P619151932C>C>g00DER61?61g00EQg00cV35R47!uN$db521g00I3#7R01?01%73A5614#F!t-$f0%;33E357=1=215g00KI/D4=232'8'8do"). Qed.
Definition scsG : list sidecond := Eval vm_compute in (snd (fst rG)).
Lemma factsG : ltac2:(zQ "h42!j4!hrb!ijc!hqe!hq7!hp1!no0!og1!ho6!k2!nob!np1!ij2!ikb!hs7!mo6!np8!og6!nqc!ik2&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1z (kr_t_AsTail_rderr_defs ()) ["FPX1"] "##,Bp;1p;3p;4p;2g0000j1:Tg000Pj1?Tg00Sej10Tg004Fj36Tg001Wj14Tg002<j13!s/$aj1<Tg003?j15Tg005Mj1B!s/$kj4ATg0076j1@!s/$Vj3GTg0086j32!s/$Pj27!s/$kj29Tg009Ej4>!s/$`j2=Tg00:@j38!s/$]j3;Tg00;:j1ETg00<@j3DTg00=Fj2FTf0R0#!s$&p=C%0!s4+!s:'H!s:4!s$3p=1g00>LR0#:R1g00?Wg00@7g00@ig00AUR2g00BAR3#?%03#C#H#1!s$2?56!sK$`R2#4!s$$3!s$&4#3#<#536%<2!s,$B2#5CA%@0R25G0R0;20A2122R3g00CER4g00CeR5;25R6'71910P3P619121945C>C>g00DER61=61g00EQg00g>38R37;1g00hI521g00I3#:R01=01%:4A8613#E!t4$iV%@43D387;1=212g00KI/F3=245'7'7do"). Qed.
Definition scsH : list sidecond := Eval vm_compute in (snd (fst rH)).
Lemma factsH : ltac2:(zQ "h42!j4!hrb!ijc!hqe!hq7!hp1!no0!ogd!ho6!k2!nob!np1!ij2!ikb!hs7!mp4!np8!oh2!nqc!ik2&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_rderr_defs ()) ["FPX1"] "p;1p;3p;2p;4g0000j13Tg0076j18Tg0086j30Tg008Pj21Tg008kj27Tg009Ej46Tg009`j25Tg00:@j32Tg00:]j34Tg00;:j1;Tg00<@j3:Tg00=Fj29Tg00>LR0#3R1%80R0;00R2g00CER3g00CeR4;04R5,121710R6P2P5P61734C6C6g00DER61561g00EQg00jc32R5741g00kn501g00I3#3R21521%33A2615#;R5g00m;%833:32741=010g00KI/95=034'1'1do"). Qed.
Definition scsG3 : list sidecond := Eval vm_compute in (snd (fst rG3)).
Lemma factsG3 : ltac2:(zQ "h42!j4!hrb!ijc!hqe!hq7!hp1!no0!oh9!ho6!k2!nob!np1!ij2!ikb!hs7!mr0!np8!ohf!nqc!ik2&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_rderr_defs ()) ["FPX1"] "p;1p;3p;2p;4g0000j13Tg0076j18Tg0086j30Tg008Pj21Tg008kj27Tg009Ej46Tg009`j25Tg00:@j32Tg00:]j34Tg00;:j1;Tg00<@j3:Tg00=Fj29Tg00>LR0#3R1%80R0;00R2g00CER3g00CeR4;04R5,121710R6P2P5P61734C6C6g00DER61561g00EQg00nH32R5741g00oT501g00I3#3R21521%33A2615#;R5g010b%833:32741=010g00KI/95=034'1'1do"). Qed.
Definition scsH3 : list sidecond := Eval vm_compute in (snd (fst rH3)).
Lemma factsH3 : ltac2:(zQ "h42!j4!hrb!ijc!hqe!hq7!hp1!no0!oi7!ho6!k2!nob!np1!ij2!ikb!hs7!ms2!np8!oid!nqc!ik2&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_rderr_defs ()) ["FPX1"] "p;1p;3p;2p;4g0000j13Tg0076j18Tg0086j30Tg008Pj21Tg008kj27Tg009Ej46Tg009`j25Tg00:@j32Tg00:]j34Tg00;:j1;Tg00<@j3:Tg00=Fj29Tg00>LR0#3R1%80R0;00R2g00CER3g00CeR4;04R5,121710R6P2P5P61734C6C6g00DER61561g00EQg012032R5741g013<501g00I3#3R21521%33A2615#;R5g014J%833:32741=010g00KI/95=034'1'1do"). Qed.
Definition scsF4 : list sidecond := Eval vm_compute in (snd (fst rF4)).
Lemma factsF4 : ltac2:(zQ "h42!j4!hrb!ijc!hqe!hq7!hp1!no0!oj5!ho6!k2!nob!np1!ij2!ikb!hs7!mu9!np8!ojb!nqc!ik2&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1z (kr_t_AsTail_rderr_defs ()) ["FPX1"] "##+_p;1p;4p;3p;2g0000j13Tg00Sej10Tg000Pj1DTg00\Sj4CTg003?j1?Tg00TDj38Tg005kj4>Tg0076j17!s/$Vj3<Tg0086j32!s/$Pj26!s/$kj24Tg009Ej4;!s/$`j2:Tg00:@j35!s/$]j39Tg00;:j1BTg00<@j3@Tg00=Fj2ATf0R0#!s$&p=E%0!s4+!s:'=!s:4!s$3p=1g00>LR0#3R1g00CeR2g00_>P2g00BAR3%E3R3%03#=#1!s$2DR3CCg00AUR4g00XP#?R59843;85C>%70R55<0R0;20A2155!sL$CER3?222R6'61410P4P614151432C;C;g00DER61:61g00EQg015X35R4791g016d521g00I3#3R01:01%33A5614#BR4g0182%733@35791=215g00KI/A4=232'6'6do"). Qed.
Definition scsG4 : list sidecond := Eval vm_compute in (snd (fst rG4)).
Lemma factsG4 : ltac2:(zQ "h42!j4!hrb!ijc!hqe!hq7!hp1!no0!ok3!ho6!k2!nob!np1!ij2!ikb!hs7!mv1!np8!ok9!nqc!ik2&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_rderr_defs ()) ["FPX1"] "p;1p;3p;4p;2g0000j13Tg000Pj1DTg001Wj10Tg002<j17Tg002aj1=Tg003?j15Tg004Fj3:Tg005Mj1@Tg005kj4?Tg0076j19Tg007Vj3>Tg0086j31Tg008Pj24Tg008kj26Tg009Ej4<Tg009`j28Tg00:@j32Tg00:]j3;Tg00;:j1CTg00<@j3BTg00=Fj2ATg00>LR0#3R1g00?Wg00@7g00@ig00AUg00BA#Dg00B`R2#0#0#7#0#7#0#0#0#0#=#53:%=2#53:%@2#5C?%90R25>0R0;10A1122R3g00CER4g00CeR5;15R6'41610P3P616121645C<C<g00DER61861g00EQg019@32R37;1g01:L511g00I3#3R01801%34A2613#CR3g01;Z%943B327;1=112g00KI/A3=145'4'4do"). Qed.
Definition scsH4 : list sidecond := Eval vm_compute in (snd (fst rH4)).
Lemma factsH4 : ltac2:(zQ "h42!j4!hrb!ijc!hqe!hq7!hp1!no0!ol1!ho6!k2!nob!np1!ij2!ikb!hs7!ng8!np8!ol7!nqc!ik2&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_rderr_defs ()) ["FPX1"] "p;1p;3p;2p;4g0000j13Tg0076j18Tg0086j30Tg008Pj21Tg008kj27Tg009Ej46Tg009`j25Tg00:@j32Tg00:]j34Tg00;:j1;Tg00<@j3:Tg00=Fj29Tg00>LR0#3R1%80R0;00R2g00CER3g00CeR4;04R5,121710R6P2P5P61734C6C6g00DER61561g00EQg01<h32R5741g01>4501g00I3#3R21521%33A2615#;R5g01?B%833:32741=010g00KI/95=034'1'1do"). Qed.

(* [comment removed for export] *)
Lemma ot_itinerary : ltac2:(zQ "j20!h9!hq7!ijc!j4!hrb!hqe!ki5!olf!ho6!ip5!no0!np1!q8!om7!iqa!irb!r9!p5!s8!ome!on5!onc!oo2!oo9!no6!nrb!ns7!nt3!ntf!nub!oj5!og1!oh9!ok3!ogd!oi7!ol1!op0!op5!opb!mv9!msa!oq1!oq8!oqf!or6!ord!os4!osa!ot1@2$b@3$a@2$1@2$1@2$1$0$0$0$0@4$6@2$1@2$1$0$0$0$0@4$6@2$1$0$0$0@4$6$0$0@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$h8@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$h9@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$ha@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$hb@4$6@2$1@2$1$0$0$0$0@4$6@2$1$0$0$0@4$6$0$0$c$c$h2$c@2$b@3$a@2$1@2$1@2$1@2$1$0$0$0$0$0@4$6@2$1@2$1@2$1$0$0$0$0$0@4$6@2$1@2$1$0$0$0$0@4$6@2$1$0$0$0@4$6$0$0@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$hc@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$hd@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$hf@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$i2@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$i5@4$6@2$1@2$1@2$1$0$0$0$0$0@4$6@2$1@2$1$0$0$0$0@4$6@2$1$0$0$0@4$6$0$0$c$c$c$h0$h1@2$b@3$a@2$1@2$1$0$0$0@4$6@2$1$0$0$0@4$6$0$0@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$i0@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$i3@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$i6@4$6@2$1$0$0$0@4$6$0$0$h0$h0$h1@2$b@3$a@2$1@2$1@2$1$0$0$0$0@4$6@2$1@2$1$0$0$0$0@4$6@2$1$0$0$0@4$6$0$0@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$he@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$i1@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$i4@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$i7@4$6@2$1@2$1$0$0$0$0@4$6@2$1$0$0$0@4$6$0$0$h0$c$h0$h1@2$b@3$a@1$e$9@3$fNhg3$if$h5@2$d$9$ic@2$b@3$a@1$e$9@3$fNu3$ie$h4@2$d$9$i9@2$b@3$a@1$e$9@3$fNhg3$j0$h6@2$d$9$ia@2$b@3$a@1$e$9@3$fNs3$id$h3@2$d$9$i8@3$a@1$e$9@3$fNhg3$j1$h7@2$d$9$ib").
Proof.
ltac2:(KReplay.run1z (kr_t_AsTail_rderr_defs ()) ["FPX1"] "##n<p%0p%1p&0p;2p;1p;3p;<p;4g009`j2tTg002<j11Tg001Wj10Tg0086j3MTg01@Pk10DTg005Mj1ATg000Pj17!s]$aj1=Tg00Sej12Tg003?j1@Tg00TDj3lTg0076k10=Tg01A2j3HTg01B;j2fTg01CDj3?Tg00UKj2BTg01DMk20!s0$EVk20;Tg01F_k20:Tg01Ghl<nTg01I6j2R!tu$Pj2Y!s/$kk208!tl$0k10@!sL$Xj4DTg01J8j3sTg004Fj3v!td$Vj34Tg009Ek40!tR$:@j3uTg01KEk104Tf0R0#0#1p=P%00#!s2&X!s2%1#0p=L%00#Ap=qg01LJR1P1f1R2P0CDp=_!sN$p=6!sV'1p=G!sn'0p=<!s2'Ap=9f4R3P1f3R4P1f2R5P2CD!sm%gP5P1P!sz%>0>%1!sq&{%1!s}+d!s<%!tm$c!s>$p=8%0!sD$#1p=h!s\&#0p=r!s^%!sR$wg00AUR6%@07v2p=Q%20#2p>07!s/$#2#2p=W!s2&p=o!s<+!s$'p=m!s:4!s$3p=TAv620p=F%A0#@p=>%00#=p=|!te'1p=J!t}'0p=O!v8%A#@p=N!s>%!uI$k!u1'0p=j!ui'0p=Sg01LhR7%72;40p>03%75%72=470547p=C!s3&94759474p=iA472!s6+9473p=V%74!s=+547p>021B45??20p=zg01Mo?v20p=b!tK$p=U!u7+!s$'p=]!xE&p=:!x[+!s$'p=ag01N[!sl%eg00XPR8,B0p=`%05#=,B4!t<%;!sb%=,B2p=y!un&p>01%=0,B2p>00%15!s~&!s],K!vL'1p=x1B45!w8$7?2p=p%10#Ap>0C%@09?52p>0<g00I3R9%A4,B3??5!v^$=I%14!t%&A!s>&=490p=\A4920949594!s$$3p=3A?4!sF&>0A%=4!sX05f6R:f5R;;?!sO,549p=}!sr4949;949:p=[!sB$p>09P3P420852P0H0?p=Zg00DER3Au5207u4$04p=E!s4$9u34p>06!|>%&04!|@%5P2P1P0g01OGCDp=~AM452/Y0p=^1t11R0/t1R5/t1R4P5P0g00B`R2#1R:#0R;#1R<#0S00#0S01#1S02#PS03#PS04#1#X#L#qR=/_=R>%1:R?#1R@#0RA#1S05#6#G#<#9P=DgRB;MB1t41S06P4P5B0>0>=%0;S07#1!t8$>#0S08#{#d#c#9RC!sC$9#8#L#h#r#qR;DgRD;MDS0:1_CC>0>0;RE=M5ES0;P5P01_C=PCP;DgR;=M4;S0<g01PURF$0DRG%1<S0=!uJ$GS0>#{S0?#0RH#0RI#0S0@#P#9RJ%02RK#ARL%8>!tc%A#1RM#1S0B#wS0C#1!t]$Ng00BARO#7RP%0KRQ#1RR#0RS#1RT#0RU#6RV#0S0D#=S0E'QRW%2ORO#2RX$07RY#WRZ#oS0F#2S0G#2#mS0H#2#TR[#TS0I#2S0J#2S0K#2R\#2R]#2R^#2R_#2R`#2Ra#o#W#m#T!s$%Rb#7Rc,FPRd%0QRQ#1S0L#1Re#1Rf#1Rg#0Rh#0Ri#='QPW%1KRK#0Rj#0S0M#0Rk#0Rl#>Rm%@8RnPn%1R!uG$o#0Rp#6S0N#|S0O,QPRq&07b#W!tF+2#WS0P#2S0Q#2S0R#WS0S#2S0T#2S0U#2S0V#2S0W#2S0X#2S0Y#o#mS0Z#2S0[#2S0\#2S0]#2Rr!st%^#2S0_#2S0`#WS0a#2S0b#2S0c#2S0d#2S0e#2S0f#2S0g!st%h#2S0i#2S0j#2S0k#2Rs%@NPq%7[S0l%1<#P#<#J#O#NS0m%2s#WR<%2<!s''@JR[%>2RtAl6cnRu9l6nS0n%>RS0o5l6Rv5l6Pn%W<R<#7!s_-!s'70?S0!vV$q#1#kR?#0#j#G#9S0r#@S0sPt%8?#J#S#NS0tPn%7\S0u%7]S0v%7^S0w%7_S0x%7`S0y%7aS0z%o<#m!t92&0=7R7+033CCiDVDV3C3C3CDV3CCiH02S0{Pn%1IRI#P#9PZ%0QR<#0Ra#0S0|#6S0}#0R`#=,QPS0~CzR_Pn%8I#9PZPWCzRIPn%1HS10#0S11#6!s?+H%qA9Hc8%7XR8/Fc%=2'Q%>:R:'b%1@S12#US13#1#]R@#:#<#aS14#>R2'F%=Q#@RA'eR^%<`R`#:S15#0#a#a#aS16#AR]%U`R`#1#J#]R\#1#<#a#9R?3HRw%`^%>QRQ'fR^1b8:/F2/eARx?H]?Ry%`x/fQRx%1g#|S17#@Rg,Fd/b!sN'z!sN${%`z/fQRz%1h#=#@Rh,FdS18!sN,d!sN$]%`d/fQRd1bW!s@'|%0`#J#c#J#h#J#dR`#0#9%h\!s3$\#0#93HR}%`|/fQR|1FPg!s},g%1`#9R`%1\#9R\3HR~%`g/fQRg1FPhS19!sR,A?H`\R\%`A/fQRQPP%jkS1:PZPnC;Rk%8l,yPS1;%1aRA#8R`$01S1<#1#XR:#0#>Rh7?ZS1=%6lS1>#0S1?#0-00PS1@??ZtS1A!~I%1Rl#8!ss$B%1:#>S1C!s`$DPP%:lS1EPZP[C;S1FPP%0RRR!tR$KS1GPP%6RS1H#0S1IPZPhC;S1JPP%1oRoPZPtCKS1KPP%:oS1L!sm'MPPPpPZ%0M#G#c#NCKS1NPP%1TRMPZQ1CCKS1OPP%:MS1P!s\'QPPPUPZPvCKS1RPPQ0DPZg01Qc%1@R@#U!yE$U#>RM;lvS0DC;S1SPP%0SRS#1Rp#1S1T#6PZPMC;S1UPP%:pRpPZ%>TS1VC;S1W!sU&PZ%1>S1X#:#L#O#qS1Y#@S1ZCKS1[PwPyP{P]P}P~P\PPPi!wZ&iPP%0eRe#6S1\#0PZQ0nC;R>PP%:fPZPcC;RfPP%6SS1]#0RS#|S1^PZ%1<RT#1Ro#1RR#1#w#xCpRlPPPe!w0%Re!tB3%:APZP8C;S1_PPQ0OPZ%1jRA#0S0O#6R:!~4$CzS1`PPQ17POPaCpS17PP%=SPXQ0>#0#JCpS0>PP%=pPZQ0|#{!ue$J#h#L!s&$O#x#L#<#O#kCpS0|Q0E,BPS0EQ07#6Rp#d#L#d#w#X#<#X#c#G#k#d#O#G#X$0C80<ZS07PPQ0L#0RX#1!vy%URU#URa#6#S!s$-c#>CKS0LPP%:!sM$a!x@$a#0#]#]#>C;S1aPP%0`PZQ08#0#U#G!s$&NC;S08!z#$PZ%1VRo#:#w!sZ%bPP%0TRT#6S1c!w]%sC;S1dPPPT!{1'e!{1$PZPqC;S1fPP%0XRXPZQ0~CKS0~PP%6XS1g#0PZ%1AS1h#:S1i#=RA,QPC;S1jPnQ0@#1RXPZPnPn%<!s/&Q0?$01RX#1!#?_$R#:PY%1a!uL%PnQ10#8RaPZPmPn%<aPZPW1BnJRaPY%>KS10Q1>-00P!su$PQ0M#1S0M#:S1>!s9%%0:R!~w$1BPAPZPnQ1H!sW-1PPZ!#>4&A#0S1P#6RT#=R`,QPS1HPPQ0NPZ%7ORSPPPVPZQ0K#7PPQ1]PZQ0J!s2%\PZQ0I!s2%gPZQ!s_$1cPZP[PPQ0}PZQ1<#6#c#>S1<PPQ12#0S12#6PZQ13#6#O#X#N%A<-0BPQ14#0!#8$$Q16#:#9R<5HP!tv%URV#S,yP%0KRK#r#9+0;AH8?<Q15#AQ0A#:#<#9+0:Q00#1#8#8!so$0=#0#rR<#0R?!sI+1BP`PZP81yPKPZ%0V#8#r#X#NPP%6!{_$F!uK$09!tx$0G!s4%1!s4%H#7Q0r,BnPZPSQ0p#1#9-0;a!}@$n%8<R<#6#k#9PZQ0B#P#x#kCpPn%1<R<#8Ra#PPZ%@=Pn%8a#<PZQ03!t~$L#8#NPn%k!s:$2#8#X#O!s:&U?#cPZQ04#P!sN'Q0q#:R?#L#GPZP2Pn%{?#j#SR?#0POPtPn%1?!s/&UoRo#P#d#S!s7&8o#O#G!s3%Q11#1#<PZ%@CPn%0X#<PY%@LPn&01RPY%>URU!zt$PYPUPn%<@#ORU#!yd%n%8U#<PZPn&0=9DID\D\DI!s$0\!s:&\D3H0AD5D5D5F}F[!s0%!s$/F}!s+&I!sk&\R9+09D3D3RUF[D3!s0$Y!s0'!s$/M<n,RFRR;MRRXPJPLQ1YPWQ18PWPmPhPtQ1^,QPRCPrQ1ZPCQ0lQ0mQ0^Q0_Q0`Q1VPMPtQ0a#7Q0bQ0cQ0dQ0eQ0fQ0gQ0DPvP[Q1CPtPhPnAl6unR6PtPuQ0hQ0iQ0jQ0k0037!#BZ9P_PIPHQ05#ARv=HcvRvPwP^PyPxP{PzP]PdP}P|P~PgP\PQPkQ1;??Z8RoQ1@??ZnR?Q1B??ZhR2PiP>PfPlP!#8T1Q1_Q1`Q17Q0>Q0|Q07Q0LQ1aQ08Q1bPP%1A!wp$SQ1dQ1eQ1fQ0~Q1j!~p&Q0zCKPP%6TPZQ0yPPQ1h#jPZQ0xPPQ1i!#6$$wPPQ0O!s>%vPP%0:PZQ0u!#45$jPZQ10PPQ1>!sT%tPPQ1:PZP!s/$?PZQ0sPPQ1E!~z$PPQ1I!#35%1LPZQ0C#h#NP9!y05!y6&[!s&$3R9!xq3!xm&Z=MGZRtPJPLPNPW!s$$mPnPnPqQ0{!wK%P!w@BPoP?P2P!y|-!t'&Y=MGYRv!ys%X#1#x#X#9R:PWQ19!t7$8PcPCPb%@:!yw,PQ0QQ0R!yw%cQ0S#7Q0TQ0UQ0VQ0WQ0XQ0YPnQ0oP[PhPnP8PnP6Q0nPuQ0ZQ0[Q0\Q0]!yrE12#A%A@5HcRc!u<+!yA/!uj:209Q!vn0!ue&9=MG9R2!vj'Q1T#U#=,QP!vr6Q0E%Aj80<OPkQ1=Q1AQ1DQ1FQ1GQ1JQ1KQ1MQ1NQ1OQ1QQ1RQ1SQ1UQ1WQ1[Pc!wV@!u8FPQ!{a2PU!#3#4!yD6U=MGURQ'YR\'YRg'YR~'YR|'YR}'YRd'YP4PBQ0:PdQ06PDQ0;P}P5PEQ0<P|P4P;PXP~PGPRPtPgPGPZPvP\PGPYP2PQPGP9208GUDZ!s$1P!#YX&>L$0@RU1t3UR3g00EQR9g00F[CEPUP3P9g00L\CE'_!s5+PA!sB-XnCED!#dH$0P1P1P1g01RORQPQCDR2g01S_CDPQCDQ!#Yc$!s`+`0!sm-cV!t10g>H066050!s8+jc!sT,1U3!tC02PQCDg01V>R2CD,~!t4/nH!s^-20!t4/1WS!t4'1!sl$!sc$0!v9%!sK+5X!sg-9@!sg0<h!sB-X_!tc$!u|&!tc%!sy%5PGg01Ykg01[75ssg01\C,RF!s=$]Pg01^]5srg01_j!s='a7g01bD!sT%cQ!s='d^g01ek5sbg01g8,RFg01hEg01iR!sR%j_,RF5MGC^!s$1do"). Qed.
End FPX1.
(* [comment removed for export] *)
