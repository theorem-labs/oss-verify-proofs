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
Ltac2 kr_t_AsTail_rderr_defs () := KReplay.lz_vm "#$%3I47Corelib4Init9Datatypes4list00K89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX24expr02C13~~~K!t5+7Numbers7BinNums8positive02!sKG1!sK=1Z03!t}c1!t}&!smb3!ulC1Z02!t3]8sidecond!t~+!x4A1!sFB2!xt25Logic2eq00!s@83and00K!s[;1K!s[<1!z-=prod00C!sF;3fst!sC=sndC!vm\5s_log!vh%!sl^carry!sl&7!slN6SymAux;log_covered!sl%I!y7f0!y7Cbool!}1#ELinuxProcessSemantics5Riscv5Instr;branch_!s~$5!sXG5aluop06!sRN!zi=3nat!~]?!#3&+3I!udA0!v+B1!w?]9sym_state!w@'!sr]7scripts!sp'c!spO2BsAAsTail_rderr_defs2rB!sqk4scsB!uXc6kentry!uWm4knV!ssl:ot_regions!wGmC!wGoC!vVnC!y|nD!u[o!ssl3knC!#5dA!#3j#2!#><b4!t4&!#9A\sadd!#?se!#8U+6!uo'!#85Q3!#@Q?1!yCgE!yCoE!{xnE0!wFc!x}%7!wBZ6!sXT1!sXT4!x0gF!x0o!ssl5knF0_!#3CkrF!#5wk5!u]#0!u^p!#7cmG!x<oG!}FnG!u[nH!u[oH!u[nH0!zpmG3!zpo!stnknG3!u^nH!u^pH!u^oH!u^oF4!#40o4!#40n4!zvo!u^pG!u^oG!u^oH!u^pH!u^oH!u^'!#SQ;6option!#aX^!#Oe&!#Es&!sod2!sok1!sok5!sok7!sok!#KcV2Bs;AsStdioCall9s!s0#_res!#b^C!y<'!#b`=!#a-#1C!t^^:!t^%call!t]%!#`S\4s_pc!{`3!#Lh50!#XC\!#J3$!#Jz&!#^XL7!sRN:!~cfAEXIT!v%&!yCi!ujU2!u>e7AMEMCPY!#5sj;ASTRNLEN_TR!szk2rI!sqk<ASTDIO_WRIT!#Rkk3rI3!srn!#:Gk3s!#I?l3kn!#J3nO!#Rsm!#I?m4kn!ssnsc!sso!#I>m4knH!u]o!sso!#I=m4kn!ssnsc!sso!#F\m!x<#!u]o!ss'".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc4listhc4conshc3nil89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bsh1AsTail_rderr_defs4FPX1~~~~~~k85AEXITk88AMAINEPIk87AMEMCPYk84ARIPk8cASTDIO_WRITEk8bASTRNLEN_TRhc3nat37Corelib4Init7Decimaltc2D0tc2D2tc3Nil37Corelib4Init3Nathg2bof_num_uint37Corelib4Init6Numberhi3bUIntDecimal79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymExec23SX2~~~~~~hk77scriptshc4boolhk73SCRhk74exprhc4prodhk79sym_statehk78sidecondhc4truek85FUELTk85STOPThk78sym_exec69OSSVerifyaboost_jsonafuzz_parse6images9AsanUbsan1M~~~~~~huafloaded_segmentshk76kentryhc3fsthk75carryhk75s_log79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsbAsStdioCall~~~~~~il99stdio_reshk74ELithc6optionil94SCR_il9astdio_call37Corelib5Lists7ListDefise3map04Npos69OSSVerify6Proofsaboost_jsonafuzz_parse3libcRefMemcpyLib~~~~~~iv2bcallee_kepthk74ridx35stdpp9bitvectorbdefinitionsjk82bv46Stdlib5Arith8PeanoNat3Natjmb3eqbhc4negbhc3orbk87KEPT_MC36Stdlib5Lists4Listjq46filteriv2ccallee_saved3h5LinuxProcessSemantics5Riscv5Instrjt17ALU_ADDhk74EAluhk74EVarhg23addk83spxk83FMTise3seqhc4pairjt17ALU_ANDjt17ALU_SRLhk72SAhk75KWordhc3appk85OT_FRhk74KImghk76KRangehk73KWr79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs0d1A1s1P1r1i1n1t1f1F1i1r1s1t~~~~~~knd8kn_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AsShadow~~~~~~kta7AAPP_HIkta6AHI_LO79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7AsSxKit~~~~~~lid4shknk89OT_SHOFFSk88ot_cellshk76KAlign46Stdlib6ZArith6BinInt1Zlp33subhk75saddrjt15aluopjt15mulophc5falsek82PXk8cnot_px_rangek8aOT_SHOFFS2k86OT_SHXk88px_rangek85shxknk84knV0k84srV0hk72SShk76sentryhk72SEk8bAMEMCPY_RETk84knC0k84srC0k83knCk84srD0k8cASTRNLEN_RETk84knE0k84srE0k85knF0_k84srF0k84knG0k84srG0k84knH0k84srH0k84knI0k84srI0k85knG30il96sc_retk85knH30k84scG3k85srH30k85knI30k85srI30k85knF40k85knG40k84scF4k85srG40k85knH40k85srH40k85knI40k85srI4069OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SymAux~~~~~~nid7sregion37Corelib4Init5Logicnn12eqk82rBhc3sndnn13andk8aot_regionsk84scsBnidblog_coveredk82rCk84scsCk82rDk84scsDk82rEk84scsEk82rFk84scsFk83rF0k85knF00k85scsF0k82rGk84scsGk82rHk84scsHk83rG3k85scsG3k83rH3k85scsH3k83rF4k85scsF4k83rG4k85scsG4k83rH4k85scsH4hk74s_pchc4Somek84knF4k84knG3k83knHk84knH3k84knH4k82rIk83rI3k83rI4k84scH3k84scH4k84scOFk84srF4k84srG3k83srHk84srH3k84srH4" s.
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
Definition OT_FR : Z := 6000.                (* [comment removed for export] *)
Definition FMT : Z := 0x20e2a.
Definition NPRE : Z := 19.
Definition NSUF : Z := 1.                (* [comment removed for export] *)
Definition IHI : Z := 0x80000000.            (* [comment removed for export] *)
Definition BUF_LO : Z := (-592).
Definition BUF_HI : Z := (-512).
Definition PX : ltac2:(zQ "10!hpf$0") := ltac2:(zQ "10!kg8@1$0Nod").            (* [comment removed for export] *)

(* [comment removed for export] *)
Definition srV0 : ltac2:(zQ "20!j4!hpf@1$0$1") := ltac2:(zQ "90!t6!hpf!kh0!kg8!iq7!kh7!khd!iu5!ki3@4$7$0$1\1i$0M0\1i$0$1^1@1$4Z\1n$0M0\1n$0$1^1@1$4+nvhi4\2n0$0M0\2n0$0$1^1@1$5-v0\2n1$0M0\2n1$0$1^1@1$3@2$2Ni3^4\2n2$0M0\2n2$0$1^1@1$4+mvhjh8\2n3$0M0\2n3$0$1^1@1$3@2$2Ni3^6\2n4$0M0\2n4$0$1^1@1$3@2$2Ni3^7\2n5$0M0\2n5$0$1^1@1$3@2$2Ni3^8\2n6$0M0\2n6$0$1^1@1$4$6\2n7$0M0\2n7$0$1^1@1$4+hrmti0\2n8$0M0\2n8$0$1^1@1$4+hrmti0\2n9$0M0\2n9$0$1^1@1$4$6\3n10$0M0\3n10$0$1^1@1$5-r0\3n11$0M0\3n11$0$1^1@1$3@2$2Ni3^e\3n12$0M0\3n12$0$1^1@1$3@2$2Ni3^f\3n13$0M0\3n13$0$1^1@1$3@2$2Ni3^h0\3n14$0M0\3n14$0$1^1@1$3@2$2Ni3^h1\3n15$0M0\3n15$0$1^1@1$3@2$2Ni3^h2\3n16$0M0\3n16$0$1^1@1$5-r0\3n17$0@1$3@2$2Ni3^h4@2$8N0Ni0").

(* [comment removed for export] *)
Definition ot_cells : ltac2:(zQ "40!hq7!h9!j4!t6@1$2@2$0@2$0$1$3$1") := ltac2:(zQ "60!h9!hq7!t6!kia!jb!k2@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrkig0N8+hppqsc@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrkjn8N8+hqijpc@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrkjo0N8+hqinq0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrkji8N8+hqiuu0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrkhr8N8+hqiiq0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrthn8N8+nvvvogg0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrtul8N1+1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrtul9N1+1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+ikusvcN1+1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+ikutq3N1+1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmti0N4+5@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmtk0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmtk8N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmtl8N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmtm8N8+hporm0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmtn8N8+nhhrj0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmto0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmtp8N4+2@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmtq8N4Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmtqcN4+vvvvvvvf@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmtr0N4+vvvvvvvf@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nvvvshs0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nvvvshs8N8Z@1$5@2$1@2$1$0$2$0").

(* [comment removed for export] *)
Definition OT_SHOFFS : ltac2:(zQ "20!j4!h9@1$0$1") := ltac2:(zQ "30!h9!jb!k2@3$1$0-il0@3$1$0-ije@1$2$0").
Definition OT_SHOFFS2 : ltac2:(zQ "20!j4!h9@1$0$1") := ltac2:(zQ "30!h9!jb!k2@3$1$0-il0@3$1$0-ije@3$1$0-ijd@1$2$0").
Definition OT_SHX : ltac2:(zQ "20!j4!hpf@1$0$1") := ltac2:(zQ "90!kg0!iq7!jv5!kg8!hpf!jb!kj1!kjc!k2@3$5$4@3$0$6@3$0$2@3$0$7@3$0$2@3$0$2@1$3N2@1$3Nod@1$1-1@1$1+3@1$1+nvvvogg0@1$1-8@3$5$4@3$0$6@3$0$2@3$0$7@1$3N2@1$1+3@1$1+nvvvogg0@1$1-8@3$5$4@3$0$6@3$0$2@3$0$7@3$0$2@3$0$2@1$3N0@1$3Nod@1$1-ije@1$1+3@1$1+nvvvogg0@1$1-8@3$5$4@3$0$6@3$0$2@3$0$7@3$0$2@3$0$2@1$3N0@1$3Nod@1$1-ijd@1$1+3@1$1+nvvvogg0@1$1-8@1$8$4").
Fixpoint shxkn (l : list expr) : list kentry :=
  match l with [] => [] | e :: r => KRange e 0x20000000000 0x10007fff8000 :: KZero (SA e 0) (ELit 8) :: shxkn r end.

Definition knV0 : ltac2:(zQ "20!j4!ij7@1$0$1") := ltac2:(zQ "h40!ij7!kg8!jb!kk7!kkd!iq7!kl6!klc!km4!kmc!kn6!k2!kse!lh8!li3!lma!ln2!lne!lo9!lqb@3$6$0@3$2$0@2$h2@1$1N0+h0@3$2$0@3$9@1$1N0+nvvvogggggg0+ogggggggggg0@3$2$0@2$a@2$3@1$1N0@2$h3-o0$7$7@3$2$0@3$9@1$1N2$e$d@3$2$0@2$8+hggg0+mngg0@3$2$0@2$8+hqqgg0+hrkgg0@3$2$0@3$4@2$3@1$1N0-r0N8@1$1N2@3$2$0@3$4@2$3@1$1N0-r8N8@1$5+ruri0@3$2$0@3$4@2$3@1$1N0-s0N8@1$1Nb@3$2$0@3$4@2$3@1$1N0-s8N8@1$1Nc@3$2$0@3$4@2$3@1$1N0-t0N8@1$1Nh5@3$2$0@3$4@2$3@1$5Z+nhhjl8N8@1$1N1@3$2$0@2$a@2$3@1$5Z+hrmti0+u8@1$b$0@3$6$0@1$f$h0@1$c$h1").
(* [comment removed for export] *)
Definition not_px_range (k : kentry) : bool := match k with KRange (EVar 141) _ _ => false | _ => true end.
Definition px_range : ltac2:(zQ "30!j4!h9!ij7>2lo$1>2hi$1>2kn@1$0$2@1$0$2") := ltac2:(zQ "80!ij7!h9!jb!j4!lt5!lta!kmc!jr7\2lo$1\2hi$1\2kn@1$3$0@3$2$0@3$6$4^3^2@3$7$0$5^1").
(* [comment removed for export] *)
Definition kn_readd : ltac2:(zQ "30!j4!h9!ij7>3plo$1>3phi$1>2kn@1$0$2@1$0$2") := ltac2:(zQ "90!ij7!kl6!h9!j4!lma!lu9!lv6!lvf!mga\3plo$2\3phi$2\2kn@1$3$0@3$7^3^2@3$1$0@1$8$6@3$1$0@1$4$5^1").

(* [comment removed for export] *)
Definition ssB0 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "50!k2!mh2!mh9!mi0!mi6@5$3+hppqsc$2@1$0$4$1Nk3").
Definition rB := Eval vm_compute in runT (SCR [false] [] []) ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_afterT rB knV0.
(* [comment removed for export] *)
Definition logM1 : ltac2:(zQ "20!j4!mi6@1$0$1") := ltac2:(zQ "70!mi6!jb!iq7!kg8!kk7!mj0!k2@3$1$0@3$5@2$4@1$3N0-ijeN1@1$2+i0@3$1$0@3$5@2$4@1$3N0-ik0N2@1$2+mumf@3$1$0@3$5@2$4@1$3N0-ik8N8@1$2+ignimvninimligm4@3$1$0@3$5@2$4@1$3N0-il0N8@1$2+mhmlniigjqmpmsm3@1$6$0").
Definition knC0 : list kentry := Eval vm_compute in fst (fst (carry logM1 knB [])).
Definition srC0 : list expr := Eval vm_compute in sr_after_call_j srB KEPT_MC 67.
(* [comment removed for export] *)
Definition ssC0 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "60!k2!mj6!mk4!mkb!mi0!mi6@5$4$1$3@1$0$5$2Nm3").
Definition rC := Eval vm_compute in runT (SCR [] [] []) ssC0.
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC)).
Definition knC : list kentry := Eval vm_compute in kn_afterT rC knC0.
Definition srD0 : list expr := Eval vm_compute in sr_after_call_j srC KEPT_MC 99.
(* [comment removed for export] *)
Definition ssD0 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "60!k2!mj6!ml2!ml8!mi0!mi6@5$4$1$3@1$0$5$2No3").
Definition rD := Eval vm_compute in runT (SCR [] [] []) ssD0.
Definition srD : list expr := Eval vm_compute in s_regs (fst (fst rD)).
Definition knD : list kentry := Eval vm_compute in kn_afterT rD knC.
(* [comment removed for export] *)
Definition knE0 : list kentry := Eval vm_compute in kn_readd 0 131071 (kn_cut 0 (-1152 - 4400) (-1152) IHI knD).
Definition srE0 : list expr := Eval vm_compute in sr_after_call_j srD KEPT_CS 131.
(* [comment removed for export] *)
Definition ssE0 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "60!k2!mlf!mme!mn5!mi0!mi6@5$4$1$3@1$0$5$2Nq3").
Definition rE := Eval vm_compute in runT (SCR [false] [ELit 0] []) ssE0.
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
Definition knE : list kentry := Eval vm_compute in kn_afterT rE knE0.
Definition srF0 : list expr := Eval vm_compute in sr_after_call_j srE KEPT_MC 163.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FQMAX : Z := 61.
Definition knF0_ : list kentry := Eval vm_compute in px_range 1 FQMAX knE.
Definition ssF0 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "60!k2!mj6!mnc!mo4!mi0!mi6@5$4$1$3@1$0$5$2Ns3").
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
Definition ssG0 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "60!k2!mj6!mob!mp2!mi0!mi6@5$4$1$3@1$0$5$2Nu3").
Definition rG := Eval vm_compute in runT (SCR [false] [] []) ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_afterT rG knG0.
Definition knH0 : list kentry := Eval vm_compute in kn_readd 0 60 (kn_cut 0 (BUF_LO + NPRE) BUF_HI IHI knG).
Definition srH0 : list expr := Eval vm_compute in sr_after_call_j srG KEPT_MC 227.
(* [comment removed for export] *)
Definition ssH0 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "60!k2!mj6!mp9!mq0!mi0!mi6@5$4$1$3@1$0$5$2Nhg3").
Definition rH := Eval vm_compute in runT (SCR [] [] []) ssH0.
Definition srH : list expr := Eval vm_compute in s_regs (fst (fst rH)).
Definition knH : list kentry := Eval vm_compute in kn_afterT rH knH0.
Definition scOF : stdio_res := Eval vm_compute in sc_of 259 srH knH.
Definition srI0 : list expr := Eval vm_compute in sc_sr scOF.
Definition knI0 : list kentry := Eval vm_compute in sc_kn scOF.
(* [comment removed for export] *)
Definition ssI0 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "50!k2!mq7!mqe!mi0!mi6@5$3+hpprv4$2@1$0$4$1Nhi3").
Definition rI := Eval vm_compute in runT (SCR [] [] []) ssI0.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition knG30 : list kentry := Eval vm_compute in kn_readd (60 + 1) (60 + NSUF) (kn_cut 0 (BUF_LO + NPRE) BUF_HI IHI knF).
Definition ssG30 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "60!k2!mj6!mr5!mp2!mi0!mi6@5$4$1$3@1$0$5$2Nu3").
Definition rG3 := Eval vm_compute in runT (SCR [] [] []) ssG30.
Definition srG3 : list expr := Eval vm_compute in s_regs (fst (fst rG3)).
Definition knG3 : list kentry := Eval vm_compute in kn_afterT rG3 knG30.
Definition scG3 : stdio_res := Eval vm_compute in sc_of 227 srG3 knG3.
Definition srH30 : list expr := Eval vm_compute in sc_sr scG3.
Definition knH30 : list kentry := Eval vm_compute in sc_kn scG3.
(* [comment removed for export] *)
Definition ssH30 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "70!k2!mrd!ms7!msf!mt6!mi0!mi6@5$5@1$1$3$4@1$0$6$2Nhg3").
Definition rH3 := Eval vm_compute in runT (SCR [] [] []) ssH30.
Definition srH3 : list expr := Eval vm_compute in s_regs (fst (fst rH3)).
Definition knH3 : list kentry := Eval vm_compute in kn_afterT rH3 knH30.
Definition scH3 : stdio_res := Eval vm_compute in sc_of 259 srH3 knH3.
Definition srI30 : list expr := Eval vm_compute in sc_sr scH3.
Definition knI30 : list kentry := Eval vm_compute in sc_kn scH3.
(* [comment removed for export] *)
Definition ssI30 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "50!k2!mte!mu6!mi0!mi6@5$3+hpprv4$2@1$0$4$1Nhi3").
Definition rI3 := Eval vm_compute in runT (SCR [] [] []) ssI30.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition knF40 : list kentry := Eval vm_compute in px_range (60 + NSUF + 1) 131071 knE.
Definition ssF40 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "60!k2!mj6!mue!mo4!mi0!mi6@5$4$1$3@1$0$5$2Ns3").
Definition rF4 := Eval vm_compute in runT (SCR [true] [] []) ssF40.
Definition srF4 : list expr := Eval vm_compute in s_regs (fst (fst rF4)).
Definition knF4 : list kentry := Eval vm_compute in kn_afterT rF4 knF40.
Definition scF4 : stdio_res := Eval vm_compute in sc_of 195 srF4 knF4.
Definition srG40 : list expr := Eval vm_compute in sc_sr scF4.
Definition knG40 : list kentry := Eval vm_compute in kn_readd (60 + NSUF + 1) 131071 (sc_kn scF4).
(* [comment removed for export] *)
Definition ssG40 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "70!k2!mrd!mv6!mve!ng5!mi0!mi6@5$5@1$1$3$4@1$0$6$2Nu3").
Definition rG4 := Eval vm_compute in runT (SCR [false] [] []) ssG40.
Definition srG4 : list expr := Eval vm_compute in s_regs (fst (fst rG4)).
Definition knG4 : list kentry := Eval vm_compute in kn_afterT rG4 knG40.
(* [comment removed for export] *)
Definition logNL : ltac2:(zQ "20!j4!mi6@1$0$1") := ltac2:(zQ "70!mi6!jb!k2!iq7!kg8!kk7!mj0@3$1$0@3$6@2$5@1$4N0-il0N1@1$3+a@1$2$0").
Definition knH40 : list kentry := Eval vm_compute in fst (fst (carry logNL knG4 [])).
Definition srH40 : list expr := Eval vm_compute in sr_after_call_j srG4 KEPT_MC 227.
(* [comment removed for export] *)
Definition ssH40 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "60!k2!mj6!ngd!nh5!mi0!mi6@5$4$1$3@1$0$5$2Nhg3").
Definition rH4 := Eval vm_compute in runT (SCR [] [] []) ssH40.
Definition srH4 : list expr := Eval vm_compute in s_regs (fst (fst rH4)).
Definition knH4 : list kentry := Eval vm_compute in kn_afterT rH4 knH40.
Definition scH4 : stdio_res := Eval vm_compute in sc_of 259 srH4 knH4.
Definition srI40 : list expr := Eval vm_compute in sc_sr scH4.
Definition knI40 : list kentry := Eval vm_compute in sc_kn scH4.
(* [comment removed for export] *)
Definition ssI40 : ltac2:(zQ "10!hqe$0") := ltac2:(zQ "50!k2!nhd!ni5!mi0!mi6@5$3+hpprv4$2@1$0$4$1Nhi3").
Definition rI4 := Eval vm_compute in runT (SCR [] [] []) ssI40.

(* [comment removed for export] *)
Definition ot_regions : ltac2:(zQ "20!j4!nm6@1$0$1") := ltac2:(zQ "b0!h9!lr2!hq7!jb!kia!klc!kk7!k2!iq7!kg8!lqb@3$3@2$2$1$0@4$4$1$0@2$6@1$9N0@2$a-o0$5$5@3$3@2$2$1$0@4$4$1$0@2$6@1$8Z+hrmti0+u8@1$7@2$2$1$0").
Definition scsB : list sidecond := Eval vm_compute in (snd (fst rB)).
Lemma factsB : ltac2:(zQ "h42!j4!hrb!ik1!hqe!hq7!hp1!no5!nob!ho6!k2!np0!np6!ij7!il0!hs7!mh2!npd!nqa!nr1!ik7&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_rderr_defs ()) ["FPX1"] "p;1p;3p;4p;2g0000j13Tg000Pj1DTg001Wj10Tg002<j15Tg002aj1=Tg003?j16Tg004Fj3:Tg005Mj1@Tg005kj4?Tg0076j19Tg007Vj3>Tg0086j31Tg008Pj24Tg008kj27Tg009Ej4<Tg009`j28Tg00:@j32Tg00:]j3;Tg00;:j1CTg00<@j3BTg00=Fj2ATg00>LR0#3R1g00?Wg00@7g00@ig00AUg00BA#Dg00B`R2#0#0#5R3#0#5#0#0#0#0#=#63:%=2#63:%53#@#6C?%90R35>0R0;10A1133R2g00CER4g00CeR5;15R6'41710P2P617131745C<C<g00DER61861g00EQg00F[32R27;1g00Gf511g00I3#3R01801%34A2612#CR2g00J<%943B327;1=113g00KI/A2=145'4'4do"). Qed.
Definition scsC : list sidecond := Eval vm_compute in (snd (fst rC)).
Lemma factsC : ltac2:(zQ "h42!j4!hrb!ik1!hqe!hq7!hp1!no5!ns0!ho6!k2!np0!np6!ij7!il0!hs7!mk4!npd!ns5!nr1!ik7&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_rderr_defs ()) ["FPX1"] "p;1p;3p;2p;4g0000j13Tg0076j18Tg0086j30Tg008Pj21Tg008kj27Tg009Ej46Tg009`j25Tg00:@j32Tg00:]j34Tg00;:j1;Tg00<@j3:Tg00=Fj29Tg00>LR0#3R1%80R0;00R2g00CER3g00CeR4;04R5,121710R6P2P5P61734C6C6g00DER61561g00EQg00L\32R5741g00Mg501g00I3#3R21521%33A2615#;R5g00O4%833:32741=010g00KI/95=034'1'1do"). Qed.
Definition scsD : list sidecond := Eval vm_compute in (snd (fst rD)).
Lemma factsD : ltac2:(zQ "h42!j4!hrb!ik1!hqe!hq7!hp1!no5!nsc!ho6!k2!np0!np6!ij7!il0!hs7!ml2!npd!nt1!nr1!ik7&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_rderr_defs ()) ["FPX1"] "p;1p;3p;2p;4g0000j13Tg0076j18Tg0086j30Tg008Pj21Tg008kj27Tg009Ej46Tg009`j25Tg00:@j32Tg00:]j34Tg00;:j1;Tg00<@j3:Tg00=Fj29Tg00>LR0#3R1%80R0;00R2g00CER3g00CeR4;04R5,121710R6P2P5P61734C6C6g00DER61561g00EQg00PA32R5741g00QL501g00I3#3R21521%33A2615#;R5g00RY%833:32741=010g00KI/95=034'1'1do"). Qed.
Definition scsE : list sidecond := Eval vm_compute in (snd (fst rE)).
Lemma factsE : ltac2:(zQ "h42!j4!hrb!ik1!hqe!hq7!hp1!no5!nt8!ho6!k2!np0!np6!ij7!il0!hs7!mme!npd!ntd!nr1!ik7&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1z (kr_t_AsTail_rderr_defs ()) ["FPX1"] "##,,p;1p;3p;4p;2g0000j14Tg00Sej10Tg000Pj1;Tg003?j1GTg00TDj3BTg005kj4ATg004Fj3@Tg00UKj2>Tg00VSj4=Tg0076j17!s/$Vj3<Tg0086j32!s/$Pj26!s/$kj25Tg009Ej48!s/$`j29Tg00:@j33!s/$]j3:Tg00;:j1FTg00<@j3DTg00=Fj2ETf0R0#0#0p=C%0!s0$!s$,p=?!s:4!s$3p=1g00>LR0#4R1g00?WR2g00W^g00AUR3g00BA#0R4#0R5#0#C#?#1!s$2;R6g00XPR7#GR83BP6CA%;5=@36/>7P4P2P8C=%70R85<05<0R0;20A2188!t;$CER4g00CeR7;27R6'61510P2P615181547C8C8g00DER61961g00EQg00Xn33R27:1g00Z9521g00I3#4R01901%44A3612#F!t4$[F%743D337:1=218g00KI/E2=247'6'6do"). Qed.
Definition scsF : list sidecond := Eval vm_compute in (snd (fst rF)).
Lemma factsF : ltac2:(zQ "h42!j4!hrb!ik1!hqe!hq7!hp1!no5!nu4!ho6!k2!np0!np6!ij7!il0!hs7!mnc!npd!nu9!nr1!ik7&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1z (kr_t_AsTail_rderr_defs ()) ["FPX1"] "##-^p;1p;3p;4p;2g0000j18Tg000Pj1=Tg001Wj17Tg002<j15!s/$aj1DTg003?j1:Tg004Fj36Tg00Sej10Tg005kj44Tg00\Sj4ETg00TDj3CTg0076j1B!s/$Vj33Tg0086j32!s/$Pj2;!s/$kj29Tg009Ej4@!s/$`j2ATg00:@j3<!s/$]j3?Tg00;:j1ITg00<@j3HTg00=Fj2GTf0R0#0#0p=>%0!s0$!s$,p=F!s:4!s$3p=1g00>LR0#8R1g00?WR2g00@7R3g00@iR4g00AUR5g00BAR6#=R7g00B`R8#7!s$$5!s$&7#5#D#:R936R:%D8#:R836%>6R;#>R<#0#F#1!s$2=R=C4P2P3%=;R;=648P=C4g00CeR8g00]ZP;A657==659C4P2g00^LP:P;C4P8g00_>P8P6P<P=CEg00XP#:R<9C5==C5<C4%B0R<530!s%/R0;20A21<<!uK$CER=?288R6';1910P5P6191<19=8C@C@g00DER61A61g00EQg00`03<R57?1g00a;521g00I3#8R01A01%8=A<615#I!t-$bH%B=3H3<7?1=21<g00KI/G5=2=8';';do"). Qed.
Definition scsF0 : list sidecond := Eval vm_compute in (snd (fst rF0)).
Lemma factsF0 : ltac2:(zQ "h42!j4!hrb!ik1!hqe!hq7!hp1!no5!nv0!ho6!k2!np0!np6!ij7!il0!hs7!nv6!npd!nve!nr1!ik7&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1z (kr_t_AsTail_rderr_defs ()) ["FPX1"] "##,Ap;1p;3p;4p;2g0000j17Tg000Pj1:Tg00Sej10Tg004Fj36Tg001Wj14Tg002<j13!s/$aj1CTg003?j1BTg005kj4<Tg0076j1;!s/$Vj3@Tg0086j32!s/$Pj28!s/$kj29Tg009Ej4>!s/$`j2?Tg00:@j35!s/$]j3=Tg00;:j1FTg00<@j3ETg00=Fj2DTf0R0#0#0p=A%0!s0$!s$,p=G!s:4!s$3p=1g00>LR0#7R1g00CeR2g00]Zg00BAR3#AR4#:R5g00AUR6%:3R3%04#A#G#1!s$2:566g00B`#4!s$$3!s$&4#3#C#BR436C<g00?Wg00^LA6634P5C<%;0R55@05@0R0;20A2155R4g00CER3?222R6'81910P4P619151932C>C>g00DER61?61g00EQg00cV35R47!uN$db521g00I3#7R01?01%73A5614#F!t-$f0%;33E357=1=215g00KI/D4=232'8'8do"). Qed.
Definition scsG : list sidecond := Eval vm_compute in (snd (fst rG)).
Lemma factsG : ltac2:(zQ "h42!j4!hrb!ik1!hqe!hq7!hp1!no5!og6!ho6!k2!np0!np6!ij7!il0!hs7!mob!npd!ogb!nr1!ik7&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1z (kr_t_AsTail_rderr_defs ()) ["FPX1"] "##,Bp;1p;3p;4p;2g0000j1:Tg000Pj1?Tg00Sej10Tg004Fj36Tg001Wj14Tg002<j13!s/$aj1<Tg003?j15Tg005Mj1B!s/$kj4ATg0076j1@!s/$Vj3GTg0086j32!s/$Pj27!s/$kj29Tg009Ej4>!s/$`j2=Tg00:@j38!s/$]j3;Tg00;:j1ETg00<@j3DTg00=Fj2FTf0R0#!s$&p=C%0!s4+!s:'H!s:4!s$3p=1g00>LR0#:R1g00?Wg00@7g00@ig00AUR2g00BAR3#?%03#C#H#1!s$2?56!sK$`R2#4!s$$3!s$&4#3#<#536%<2!s,$B2#5CA%@0R25G0R0;20A2122R3g00CER4g00CeR5;25R6'71910P3P619121945C>C>g00DER61=61g00EQg00g>38R37;1g00hI521g00I3#:R01=01%:4A8613#E!t4$iV%@43D387;1=212g00KI/F3=245'7'7do"). Qed.
Definition scsH : list sidecond := Eval vm_compute in (snd (fst rH)).
Lemma factsH : ltac2:(zQ "h42!j4!hrb!ik1!hqe!hq7!hp1!no5!oh2!ho6!k2!np0!np6!ij7!il0!hs7!mp9!npd!oh7!nr1!ik7&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_rderr_defs ()) ["FPX1"] "p;1p;3p;2p;4g0000j13Tg0076j18Tg0086j30Tg008Pj21Tg008kj27Tg009Ej46Tg009`j25Tg00:@j32Tg00:]j34Tg00;:j1;Tg00<@j3:Tg00=Fj29Tg00>LR0#3R1%80R0;00R2g00CER3g00CeR4;04R5,121710R6P2P5P61734C6C6g00DER61561g00EQg00jc32R5741g00kn501g00I3#3R21521%33A2615#;R5g00m;%833:32741=010g00KI/95=034'1'1do"). Qed.
Definition scsG3 : list sidecond := Eval vm_compute in (snd (fst rG3)).
Lemma factsG3 : ltac2:(zQ "h42!j4!hrb!ik1!hqe!hq7!hp1!no5!ohe!ho6!k2!np0!np6!ij7!il0!hs7!mr5!npd!oi4!nr1!ik7&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_rderr_defs ()) ["FPX1"] "p;1p;3p;2p;4g0000j13Tg0076j18Tg0086j30Tg008Pj21Tg008kj27Tg009Ej46Tg009`j25Tg00:@j32Tg00:]j34Tg00;:j1;Tg00<@j3:Tg00=Fj29Tg00>LR0#3R1%80R0;00R2g00CER3g00CeR4;04R5,121710R6P2P5P61734C6C6g00DER61561g00EQg00nH32R5741g00oT501g00I3#3R21521%33A2615#;R5g010b%833:32741=010g00KI/95=034'1'1do"). Qed.
Definition scsH3 : list sidecond := Eval vm_compute in (snd (fst rH3)).
Lemma factsH3 : ltac2:(zQ "h42!j4!hrb!ik1!hqe!hq7!hp1!no5!oic!ho6!k2!np0!np6!ij7!il0!hs7!ms7!npd!oj2!nr1!ik7&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_rderr_defs ()) ["FPX1"] "p;1p;3p;2p;4g0000j13Tg0076j18Tg0086j30Tg008Pj21Tg008kj27Tg009Ej46Tg009`j25Tg00:@j32Tg00:]j34Tg00;:j1;Tg00<@j3:Tg00=Fj29Tg00>LR0#3R1%80R0;00R2g00CER3g00CeR4;04R5,121710R6P2P5P61734C6C6g00DER61561g00EQg012032R5741g013<501g00I3#3R21521%33A2615#;R5g014J%833:32741=010g00KI/95=034'1'1do"). Qed.
Definition scsF4 : list sidecond := Eval vm_compute in (snd (fst rF4)).
Lemma factsF4 : ltac2:(zQ "h42!j4!hrb!ik1!hqe!hq7!hp1!no5!oja!ho6!k2!np0!np6!ij7!il0!hs7!mue!npd!ok0!nr1!ik7&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1z (kr_t_AsTail_rderr_defs ()) ["FPX1"] "##+_p;1p;4p;3p;2g0000j13Tg00Sej10Tg000Pj1DTg00\Sj4CTg003?j1?Tg00TDj38Tg005kj4>Tg0076j17!s/$Vj3<Tg0086j32!s/$Pj26!s/$kj24Tg009Ej4;!s/$`j2:Tg00:@j35!s/$]j39Tg00;:j1BTg00<@j3@Tg00=Fj2ATf0R0#!s$&p=E%0!s4+!s:'=!s:4!s$3p=1g00>LR0#3R1g00CeR2g00_>P2g00BAR3%E3R3%03#=#1!s$2DR3CCg00AUR4g00XP#?R59843;85C>%70R55<0R0;20A2155!sL$CER3?222R6'61410P4P614151432C;C;g00DER61:61g00EQg015X35R4791g016d521g00I3#3R01:01%33A5614#BR4g0182%733@35791=215g00KI/A4=232'6'6do"). Qed.
Definition scsG4 : list sidecond := Eval vm_compute in (snd (fst rG4)).
Lemma factsG4 : ltac2:(zQ "h42!j4!hrb!ik1!hqe!hq7!hp1!no5!ok8!ho6!k2!np0!np6!ij7!il0!hs7!mv6!npd!oke!nr1!ik7&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_rderr_defs ()) ["FPX1"] "p;1p;3p;4p;2g0000j13Tg000Pj1DTg001Wj10Tg002<j17Tg002aj1=Tg003?j15Tg004Fj3:Tg005Mj1@Tg005kj4?Tg0076j19Tg007Vj3>Tg0086j31Tg008Pj24Tg008kj26Tg009Ej4<Tg009`j28Tg00:@j32Tg00:]j3;Tg00;:j1CTg00<@j3BTg00=Fj2ATg00>LR0#3R1g00?Wg00@7g00@ig00AUg00BA#Dg00B`R2#0#0#7#0#7#0#0#0#0#=#53:%=2#53:%@2#5C?%90R25>0R0;10A1122R3g00CER4g00CeR5;15R6'41610P3P616121645C<C<g00DER61861g00EQg019@32R37;1g01:L511g00I3#3R01801%34A2613#CR3g01;Z%943B327;1=112g00KI/A3=145'4'4do"). Qed.
Definition scsH4 : list sidecond := Eval vm_compute in (snd (fst rH4)).
Lemma factsH4 : ltac2:(zQ "h42!j4!hrb!ik1!hqe!hq7!hp1!no5!ol6!ho6!k2!np0!np6!ij7!il0!hs7!ngd!npd!olc!nr1!ik7&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_rderr_defs ()) ["FPX1"] "p;1p;3p;2p;4g0000j13Tg0076j18Tg0086j30Tg008Pj21Tg008kj27Tg009Ej46Tg009`j25Tg00:@j32Tg00:]j34Tg00;:j1;Tg00<@j3:Tg00=Fj29Tg00>LR0#3R1%80R0;00R2g00CER3g00CeR4;04R5,121710R6P2P5P61734C6C6g00DER61561g00EQg01<h32R5741g01>4501g00I3#3R21521%33A2615#;R5g01?B%833:32741=010g00KI/95=034'1'1do"). Qed.

(* [comment removed for export] *)
Lemma ot_itinerary : ltac2:(zQ "j20!h9!hq7!ik1!j4!hrb!hqe!kia!om4!ho6!ipa!no5!np6!q8!omc!iqf!is0!r9!p5!s8!on3!ona!oo1!oo7!ooe!nob!ns0!nsc!nt8!nu4!nv0!oja!og6!ohe!ok8!oh2!oic!ol6!op5!opa!oq0!mve!msf!oq6!oqd!or4!orb!os2!os9!osf!ot6@2$b@3$a@2$1@2$1@2$1$0$0$0$0@4$6@2$1@2$1$0$0$0$0@4$6@2$1$0$0$0@4$6$0$0@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$h8@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$h9@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$ha@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$hb@4$6@2$1@2$1$0$0$0$0@4$6@2$1$0$0$0@4$6$0$0$c$c$h2$c@2$b@3$a@2$1@2$1@2$1@2$1$0$0$0$0$0@4$6@2$1@2$1@2$1$0$0$0$0$0@4$6@2$1@2$1$0$0$0$0@4$6@2$1$0$0$0@4$6$0$0@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$hc@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$hd@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$hf@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$i2@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$i5@4$6@2$1@2$1@2$1$0$0$0$0$0@4$6@2$1@2$1$0$0$0$0@4$6@2$1$0$0$0@4$6$0$0$c$c$c$h0$h1@2$b@3$a@2$1@2$1$0$0$0@4$6@2$1$0$0$0@4$6$0$0@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$i0@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$i3@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$i6@4$6@2$1$0$0$0@4$6$0$0$h0$h0$h1@2$b@3$a@2$1@2$1@2$1$0$0$0$0@4$6@2$1@2$1$0$0$0$0@4$6@2$1$0$0$0@4$6$0$0@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$he@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$i1@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$i4@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$i7@4$6@2$1@2$1$0$0$0$0@4$6@2$1$0$0$0@4$6$0$0$h0$c$h0$h1@2$b@3$a@1$e$9@3$fNhg3$if$h5@2$d$9$ic@2$b@3$a@1$e$9@3$fNu3$ie$h4@2$d$9$i9@2$b@3$a@1$e$9@3$fNhg3$j0$h6@2$d$9$ia@2$b@3$a@1$e$9@3$fNs3$id$h3@2$d$9$i8@3$a@1$e$9@3$fNhg3$j1$h7@2$d$9$ib").
Proof.
ltac2:(KReplay.run1z (kr_t_AsTail_rderr_defs ()) ["FPX1"] "##n>p%0p%1p&0p;2p;1p;3p;<p;4g009`j2sTg002<j11Tg001Wj10Tg0086j3MTg01@Pk10DTg005Mj1>Tg000Pj17!s]$aj1;Tg00Sej12Tg003?j1=Tg00TDj3fTg0076k10>Tg01A2j3HTg01B;j2aTg01CDj3<Tg00UKj2CTg01DMk20BTg01EVk20:Tg01F_k209Tg01Ghl<mTg01I6j2N!tu$Pj2[!s/$kk206!tl$0k10@!sL$Xj4DTg01J8j3rTg004Fj3u!td$Vj34Tg009Ek40?Tg00:@j3tTg01KEk103Tf0R0#0#0p=6%1!s-$I%00#1p=F%10#1!sB%9!s2%1#0p=v%00#>p=ng01LJR1P1f1R2P0CDp=_%00#!s\$p=o!sn$!sf%g!s>%!s^$8f4R3P1f3R4P1f2R5P2CD!se%iP5P1P!sr%>0=!sg%!ss$e!sg&p=B!tu$#!tq$P!t='1p=`!s>%!sT$w!u1'1p=p!u1&p=|g00AUR6%=07u2p=R%20#2p>05!s/$#2#2p=U!s2&p=k!s<+!s$'p=l!s:4!s$3p=TAu620p=G%>0#=p=@%00#;p=z!t{%>#=p=K!v-'1p=j!u/'1p=Sg01LhR7%72;40p>02%75%72=470547p=A!s3&94759474p=hA472!s6+9473p=X%74!s=+547p>011C45?<20p=y!v0$p=]g01Mo?u20p=d!xO'!s$+p=\!ts'0p=?!s2+!s$'p=Wg01N[!sf%b!sf+p=Qg00XPR8,C0p=c!x3'1p=~!x%'0p=O%05#;,C4!tb%:!t-%;,C2p=x!sN&p>0<%;0!s:$}%15!tI&!s\,L1C45!w,$7<2p=q%10#>p>0C%=09<52p>0;g00I3R9%14!se&>,C3?<5!w#$=V%>4!s6&=490p=JA4920949594!s$$3p=3A<4!sF&>0A%;!sX15f6R:f5R;;<!sO,549p={!sr4949;949:p=Z!sB$p>07P3P420652P0H0?p=Yg00DER3At5207t4$03p=E!s4$9t34p>08!|5%&03!|7%4P2P1P0g01OG!s7$0AM452/[0p=^1s11R0/s1R5/s1R4P5P0g00B`R2#1R:#0R;#1R<#0S00#6S01#IS02#0S03#FS04#9#v#nR=/_=R>%1:R?#1R@#0RA#1S05#6#o#g#8P=DiRB;MB1s41S06P4P5B0=0>=%0;S07#1R;#1S08#0S09#0R>#F#e#9#8RC%B;S0:#P#`#w#nR;DiRD;MDS0;1_CC>0=0;RE=M5ES0<P5P01_C=PCP;DiR;=M4;S0=g01PURF$0DRG%1<R<#FS0>#I#pS0?#0RH#FS0@#0S0A#0#8RI%02RJ#>RK%1>R>#1RL#0S0B#1S0C#|S0D#1!t[$Mg00BARN#7RO%0JRP#1RQ#0RR#1RS#0RT#6RU#0S0E#;S0F'RRV%2NRN#2RW$05RX#URY#kS0G#2S0H#2#lS0I#2#TRZ#TS0J#2S0K#2S0L#2R[#2R\#2R]#2R^#2R_#2R`#k#U#l#T!s$%Ra#7Rb,GORc%0PRP#1S0M#1Rd#1Re#1Rf#0Rg#0Rh#;'RPV%1JRJ#0Ri#0S0N#0Rj#0Rk#@Rl%=8RmPm%1Q!uG$n#0Ro#6S0O#zS0P,RORp&05a#U!tF+2#US0Q#2S0R#2S0S#US0T#2S0U#2S0V#2S0W#2S0X#2S0Y#2S0Z#k#lS0[#2S0\#2S0]#2S0^#2Rq!st%_#2S0`#2S0a#US0b#2S0c#2S0d#2S0e#2S0f#2S0g#2S0h!st%i#2S0j#2S0k#2S0l#2Rr%=MPp%7ZS0m%1<S0n#IS0o#0#g#9#e#KS0p%2r#UR<%2<!s''=IRZ%@2RsAf6bmRt9f6mS0q%@QS0r5f6Ru5f6Pm%U<R<#7!s_-!s'70?S0s#0#F#jR?#0#e#S#8S0t#=S0uPs%I?#9#9#KS0vPm%7[S0w%7\S0x%7]S0y%7^S0z%7_S0{%7`S0|%k<#l!t62&0>7R7+023AChDXDX3A3A3ADX3AChH01S0}Pm%1HS0~!{[$0R<#0#8PY%0PR`#0R_#0S10#6S11#0R^#;,ROS12CyR]Pm%1<#8PYPVCyR<Pm%]H!s5+H%nA9Hb8%7WR8/Gb%;2'R%@:R:'d%1@S13#]S14#1#\R@#B#?#WS15#@R2'G%;P#=RA'bR\%?^R^#BS16#0#W#W#WS17#>R[%]^R^#1#Q#\R?#1#?#W#8Rv3HRw%c\%@PRP'aR\1d8:/G2/bARx?H[vRy%cx/aPRx%1f#zS18#=Rf,Gc/d!sN'z!sN${%cz/aPRz%1g#;#=Rg,GcS19!sN,c!sN$[%cc/aPRc1dV!s@'|%0^#Q#p#Q#~#Q#SR^#0#8%~?!s3$?#0#83HR}%c|/aPR|1GOf!s},f%1^#8R^%1?#8R?3HR~%cf/aPRf1GOgS1:!sR,A?H^?R?%cA/aPRPPO%OjS1;PYPmC:Rj%Ik,xOS1<%1_RA#1R^$0<R:#FS1=!vY$@Rg7<YS1>%6kS1?#0S1@#0,}OS1A?<YsS1B!~L%1Rk#I!sr$C%1:#?#KS1D!sa$EPO%BkS1FPYPZC:S1GPO%0QRQ!tS$LS1HPO%6QS1I#0S1JPYPgC:S1KPO%1nRnPYPsCLS1LPO%BnS1M!sm'NPOPoPY%F>#P#S#KCLS1OPO%1SR>PYQ1DCLS1PPO%B>S1Q!s\'RPOPTPYPuCLS1SPOQ0EPYg01Qc%1@R@#]!yF$T#@R>;fuS0EC:S1TPO%0RRR#1Ro#1S1U#6PYP>C:S1VPO%BoRoPY%@SS1WC:S1X!sU&PY%IL#v#o#nS1Y#=S1ZCLS1[PwPyP{P[P}P~P?POPh!wV&hPO%0dRd#6S1\#0PYQ0qC:R!uq$ePYPbC:RePO%6RS1]#0RR#zS1^PY%1`RS#1Rn#1RQ#1#P#F#FCqRkPOPd!w,%Rd!tD3%BAPYP8C:S1_POQ0PPY%1iRA#0S0P#6R:!~$$CyS1`POQ18PNP_CqS18PO%;RPWQ0n#0#e#QCqS0nPO%;oPYQ10#1#9!wX$p!s-$9#P!t^$o#?#e#gCqS10Q0F,COS0FQ07#6Ro#S#o#S#P#j#?#j#p#`#g#S#e#`#j$0C80;YS07POQ0M#0RW#1!vz$1TRT#]R_#6#9!s$-p#@CLS0MPO%B!sM$_!xA$_#0#\#\#@C:S1aPO%6^PYQ0B#0#]#`!s$$KC:S0B!y~$PY%OU#P!sT%bPO%0SRS#6S1c!w]%uC:S1dPOPS!{+'!w^$QPYPpC:S1fPO%0WRWPYQ12CLS12PO%6WS1g#0PY%1AS1h#BS1i#;RA,ROC:S1jPmQ0@#1#?PYPmPmQ0A!s/'?#I!um$Q#FRS#BPX%1_!uD%Pm!t6$#0!s\$lPmQ0~#1R_#1PYPV1CmIRnPX%@JS0~Q1?,}O!sz$OQ0N#1S0N#BS1!t>%O%0:S0!s2$1CO!tI$Q1I!sW,1QPY!#>9&A#0S1Q!y;%R^,ROS1IPOQ0OPY%7NRRPOPUPYQ0L#7POQ1]PYQ0K!s2%\PYQ0J!s2%gPYQ!s_$1cPYPZPOQ11PYQ1=#0#w#@S1=POQ13#0S13#6PYQ14#6#g#P#K%>`-0BOQ15#0!#8%$Q17#B#8R`5HO!tv%]RU#9,xO%0JRJ#v#8+0:AH8v`Q16#>Q08#I#W#8+09Q00#1#g!sm$0>#?R`#0Rv#6#?!sE$1CO^PYP81xOJPY%0U#I#9#O#KPO%6oPYQ0G!uG$0:PYQ0H!s2%1!y@%I#7Q0t,CmPYPRQ0s#1#8-0:n!}=$m%1`R`!t6%PYQ0C#0#9#9Cq!s@'0Rn#|PY%==Pm%O`#?PYQ03#1#v!tM$m%0n#IPYQ02#]#S!s:&1v#SPYQ04#0#I!s:%Q0o#1Rv#j#~PYP2Pm%|v#o#9Rv#0PNPs!s\$!s/%Q1U!sQ$eR2#0#Q#9!sF'2#w#`!s3&0_PY%=CPm%1WPX%=KPm&0<SPX%@TRTPm%1Q#?PXPTPm%6@#j#9RT!{>'PTPYPm&0>9DVDJ!s$$V!s0+!s2%V!s-$3H0AD5D5D5F{FZ!s0%!s$/F{!s+&!sc%VDJR9+07D3D3RTFZD3!s0$X!s0'!s$/M<m,NFRQ;MQRSPIPKQ1YPVQ19PVPlPgPsQ1^,RORWPqQ1ZPWQ0mQ0pQ0_Q0`Q0aQ1WP>PsQ0b#7Q0cQ0dQ0eQ0fQ0gQ0hQ0EPuPZQ1DPsPgPmAf6tmR6PsPtQ0iQ0jQ0kQ0l0027!#BS9P]P<PHQ05#>Ru=HbuRuPwP\PyPxP{PzP[PcP}P|P~PfP?PPPjQ1<?<Y8RCQ1A?<YmR_Q1C?<YgR2PhPLPePkP!#8P1Q1_Q1`Q18Q0nQ10Q07Q0MQ1aQ0BQ1bPO%1A!wx$RQ1dQ1eQ1fQ12Q1j!~i&Q0|CLPO%6!{Z${POQ1h#OPYQ0zPOQ1i!{d%yPOQ0P!s>%xPOQ0?!s>%w!#40$!s>$~POQ1!s>&vPOQ1;PYPsPOQ1@PYQ0uPOQ1F!~u$POQ1J!#30&MPYQ0D#F#F#KP9!y45!y:&Z!s&$3R9!xu3!xq&Y=MGYRsPIPKPMPV!s$$l!ze$pQ0}!wO%P!wDBPCP_P2P!z$-!t'&X=MGXRu!yw$09#1#F#W#8R:PVQ1:!t7$8PbPWPa%=:!y{,QQ0RQ0S!y{%bQ0T#7Q0UQ0VQ0WQ0XQ0YQ0ZPmQ0rPZPgPmP8PmP6Q0qPtQ0[Q0\Q0]Q0^!yvE13#>%>@5HbRb!u<+!yE/!uj:207P!vn0!ue&9=MG9R2!vj'%1v#;,RO!vp6Q0F%>i80;NPjQ1>Q1BQ1EQ1GQ1HQ1KQ1LQ1NQ1OQ1PQ1RQ1SQ1TQ1VQ1XQ1[Pb!wT@!u6FPP!{c2PT!#3%4!yB6T=MGTRP'[R?'[Rf'[R~'[R|'[R}'[Rc'[P4PBQ0;PcQ06PDQ0<P}P5PEQ0=P|P4P;PSP~PGPQPsPfPGPYPuP?PGPXP2PPPGP9206GTDY!s$1P!#YW&>L$0@RT1s3TR3g00EQR9g00F[CEPTP3P9g00L\CE'_!s5+PA!sB-XnCED!#d?$0P1P1P1g01RORPPPCDR2g01S_CDPPCDQ!#Yd$!s`+`0!sm-cV!t10g>H086040!s8+jc!sT,1U3!tC02PPCDg01V>R2CD-00!t5/nH!s_-20!t5/1WS!t5'1!sm$!sd%0!v;%!sL+5X!sh-9@!sh0<h!sB-X_!te$!u~&!te%!sz&5PGg01Ykg01[75rrg01\C,NF!s=$]Pg01^]5rqg01_j!s='a7g01bD!sT%cQ!s='d^g01ek5rag01g8,NFg01hEg01iR!sR%j_,NF5MGC^!s$1do"). Qed.
End FPX1.
(* [comment removed for export] *)
