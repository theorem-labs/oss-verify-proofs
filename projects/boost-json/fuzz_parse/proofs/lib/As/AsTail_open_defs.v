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
Ltac2 kr_t_AsTail_open_defs () := KReplay.lz_vm "#$$MI47Corelib4Init9Datatypes4list00K89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX24expr02C13~~~K!t5+7Numbers7BinNums8positive02!sKG1!sK=1Z03!t}c1!t}&!smb3!ulC1Z02!t3]8sidecond!t~+!x4A1!sFB2!xt25Logic2eq00!s@83and00K!s[;1K!s[<1!z-=prod00C!sF;3fst!sC=sndC!vm\5s_log!vh%!sl^carry!sl&7!slN6SymAux;log_covered!sl%I!y7f0!y7Cbool!}1#ELinuxProcessSemantics5Riscv5Instr;branch_!s~$5!sXG5aluop06!sRN!zi=3nat!~]?!#3&+3I!udA0!v+B1!w?]9sym_state!w@'!sr]7scripts!sp'c!spO2As@AsTail_open_defs2rB!spj4scsB!uVc6kentry!uUl4knV!srk:ot_regions!wClC!wCnC!vRmC!yumD!uXn!srk3knC!#5ZA!#3`#2!#>2b4!t4&!#97\sadd!#?ie!#8K+6!uo'!#8'Q3!#@G?1!y@fE!y@nE!{rmE0!wCc!xz%7!w?Z6!sXT1!sXT4!x,fF!x,n!srk5knF0_!#3<jrF!#5mj5!uZ#0!u[o!#7WlG!x6nG!}=mG!uXmH!uXnH!uXmH0!zglG3!zgn!ssmknG3!u[mH!u[oH!u[nH!u[nF4!#3yn4!#3ym4!zmn!u[oG!u[nG!u[nH!u[oH!u[nH!u['!#S%;6option!#a0^!#O?&!#EU&!sod2!sok1!sok5!sok7!sok!#KEV2As;AsStdioCall9s!s0#_res!#b6C!y<'!#b8=!#`^#1C!t^^:!t^%call!t]%!#`'\4s_pc!{`3!#LJ50!#Wu\!#Ip$!#J_&!#^0L7!sRN:!~beAEXIT!v$&!yBi!uiU2!u=d7AMEMCPY!#5pi;ASTRNLEN_TR!syj2rI!spj<ASTDIO_WRIT!#RJj3rI3!sqm!#:?j3s!#H~k3kn!#IqmO!#ROl!#H~l4kn!srmsc!srn!#H}l4knH!uZn!srn!#H|l4kn!srmsc!srn!#FFl!x6#!uZn!sr'".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc4listhc4conshc3nil89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Ash0AsTail_open_defs4FPX1~~~~~~k85AEXITk88AMAINEPIk87AMEMCPYk84ARIPk8cASTDIO_WRITEk8bASTRNLEN_TRhc3nat37Corelib4Init7Decimaltb2D0tb2D2tb3Nil37Corelib4Init3Nathg1bof_num_uint37Corelib4Init6Numberhi2bUIntDecimal79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymExec23SX2~~~~~~hk67scriptshc4boolhk63SCRhk64exprhc4prodhk69sym_statehk68sidecondhc4truek85FUELTk85STOPThk68sym_exec69OSSVerifyaboost_jsonafuzz_parse6images4Asan1M~~~~~~hu9floaded_segmentshk66kentryhc3fsthk65carryhk65s_log79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsbAsStdioCall~~~~~~il39stdio_reshk64ELithc6optionil34SCR_il3astdio_call37Corelib5Lists7ListDefis83map04Npos69OSSVerify6Proofsaboost_jsonafuzz_parse3libcRefMemcpyLib~~~~~~iucbcallee_kepthk64ridx35stdpp9bitvectorbdefinitionsjk22bv46Stdlib5Arith8PeanoNat3Natjm53eqbhc4negbhc3orbk87KEPT_MC36Stdlib5Lists4Listjpe6filteriucccallee_saved3h5LinuxProcessSemantics5Riscv5Instrjsb7ALU_ADDhk64EAluhk64EVarhg13addk83spxk83FMTis83seqhc4pairjsb7ALU_ANDjsb7ALU_SRLhk62SAhk65KWordhc3appk85OT_FRhk64KImghk66KRangehk63KWr79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As0d1A1s1P1r1i1n1t1f1F1i1r1s1t~~~~~~kn78kn_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AsShadow~~~~~~kt47AAPP_HIkt46AHI_LO79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AsSxKit~~~~~~li74shknk89OT_SHOFFSk88ot_cellshk66KAlign46Stdlib6ZArith6BinInt1Zlod3subhk65saddrjsb5aluopjsb5mulophc5falsek82PXk8cnot_px_rangek8aOT_SHOFFS2k86OT_SHXk88px_rangek85shxknk84knV0k84srV0hk62SShk66sentryhk62SEk8bAMEMCPY_RETk84knC0k84srC0k83knCk84srD0k8cASTRNLEN_RETk84knE0k84srE0k85knF0_k84srF0k84knG0k84srG0k84knH0k84srH0k84knI0k84srI0k85knG30il36sc_retk85knH30k84scG3k85srH30k85knI30k85srI30k85knF40k85knG40k84scF4k85srG40k85knH40k85srH40k85knI40k85srI4069OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SymAux~~~~~~ni77sregion37Corelib4Init5Logicnmb2eqk82rBhc3sndnmb3andk8aot_regionsk84scsBni7blog_coveredk82rCk84scsCk82rDk84scsDk82rEk84scsEk82rFk84scsFk83rF0k85knF00k85scsF0k82rGk84scsGk82rHk84scsHk83rG3k85scsG3k83rH3k85scsH3k83rF4k85scsF4k83rG4k85scsG4k83rH4k85scsH4hk64s_pchc4Somek84knF4k84knG3k83knHk84knH3k84knH4k82rIk83rI3k83rI4k84scH3k84scH4k84scOFk84srF4k84srG3k83srHk84srH3k84srH4" s.
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
Definition STOPT : ltac2:(zQ "20!j4!h9@1$0$1") := ltac2:(zQ "90!h9!jb!k2!p4!pc!q7!r1!r8!s7@3$1$0$5@3$1$0$8@3$1$0$7@3$1$0$3@3$1$0$4@3$1$0$6@1$2$0").
Definition FUELT : nat := 20000.
Definition scr0 : ltac2:(zQ "10!ho5$0") := ltac2:(zQ "40!k2!hp0!hp7!hpe@3$2@1$0$1@1$0$3@1$0$1").
Definition runT : ltac2:(zQ "50!hq6!ho5!hqd!j4!hra>3scr$1>2ss$2@2$0@2$0$2@1$3$4$1") := ltac2:(zQ "90!k2!hs6!hsd!ht5!ho5!hra!htd!hqd!ihe\3scr$4\2ss$7@7$6$8$2$1$3^2^1@1$0$5").
Definition kn_afterT : ltac2:(zQ "60!j4!hq6!ij1!ho5!hra!hqd>1r@2$1@2$1$5@1$0$4$3>2kn@1$0$2@1$0$2") := ltac2:(zQ "b0!j4!hra!ijb!hq6!ij1!hqd!hp0!ho5!k2!ik1!ika\1r@2$3@2$3$5@1$0$1$7\2kn@1$0$4@3$2@1$0$4@1$0$1@3$2@2$3@1$0$4@1$0$1@1$0$6@3$9@1$a@3$2$5@1$0$1@3$2@2$3$5@1$0$1$7^2^1@1$8$6").
Definition sc_of : ltac2:(zQ "50!j4!t5!ip4!hpe!ij1>2nv$1>2sr@1$0$3>2kn@1$0$4$2") := ltac2:(zQ "a0!iq1!ip4!j4!k2!iq9!hpe!ij1!t5!ir2!ira\2nv$7\2sr@1$2$5\2kn@1$2$6M4\1x@1$4$1$1@3$9^3^2^1\1r$1^1@c$8ZZZ@1$0Z@1$0Z@1$0Z@1$0Z@1$0Z@1$0Z@1$0Z@1$3$5@1$3$6").
Definition KEPT_MC : ltac2:(zQ "20!j4!t5@1$0$1") := ltac2:(zQ "60!t5!itf!iu6!jib!jja!jlf@4$1@1$5@1$2#5$0$4$3").     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition KEPT_MCI : ltac2:(zQ "20!j4!t5@1$0$1") := ltac2:(zQ "60!t5!jo0!jo7!joe!jp4!jr1@3$5$0\1i$0@1$2@2$3@2$1^1Nh3@2$1^1Nh4$4").
Definition KEPT_CS : ltac2:(zQ "20!j4!t5@1$0$1") := ltac2:(zQ "60!t5!itf!iu6!jrb!jja!jlf@4$1@1$5@1$2#5$0$4$3").    (* [comment removed for export] *)
Definition spx : ltac2:(zQ "20!h9!hpe>1k$0$1") := ltac2:(zQ "50!h9!juf!jva!iq1!kg2\1k$0@3$2$1@1$4N0@1$3^1").
(* [comment removed for export] *)
Definition OT_FR : Z := 6000.                (* [comment removed for export] *)
Definition FMT : Z := 0x20cf8.
Definition NPRE : Z := 17.
Definition NSUF : Z := 1.                (* [comment removed for export] *)
Definition IHI : Z := 0x80000000.            (* [comment removed for export] *)
Definition BUF_LO : Z := (-592).
Definition BUF_HI : Z := (-512).
Definition PX : ltac2:(zQ "10!hpe$0") := ltac2:(zQ "10!kg2@1$0Nod").            (* [comment removed for export] *)

(* [comment removed for export] *)
Definition srV0 : ltac2:(zQ "20!j4!hpe@1$0$1") := ltac2:(zQ "90!t5!hpe!kga!kg2!iq1!kh1!kh7!itf!khd@4$7$0$1\1i$0M0\1i$0$1^1@1$4Z\1n$0M0\1n$0$1^1@1$4+nvho4\2n0$0M0\2n0$0$1^1@1$5-v0\2n1$0M0\2n1$0$1^1@1$3@2$2Ni3^4\2n2$0M0\2n2$0$1^1@1$4+mvkjt8\2n3$0M0\2n3$0$1^1@1$3@2$2Ni3^6\2n4$0M0\2n4$0$1^1@1$3@2$2Ni3^7\2n5$0M0\2n5$0$1^1@1$3@2$2Ni3^8\2n6$0M0\2n6$0$1^1@1$4$6\2n7$0M0\2n7$0$1^1@1$4+hrpvg8\2n8$0M0\2n8$0$1^1@1$4+hrpvg8\2n9$0M0\2n9$0$1^1@1$4$6\3n10$0M0\3n10$0$1^1@1$5-r0\3n11$0M0\3n11$0$1^1@1$3@2$2Ni3^e\3n12$0M0\3n12$0$1^1@1$3@2$2Ni3^f\3n13$0M0\3n13$0$1^1@1$3@2$2Ni3^h0\3n14$0M0\3n14$0$1^1@1$3@2$2Ni3^h1\3n15$0M0\3n15$0$1^1@1$3@2$2Ni3^h2\3n16$0M0\3n16$0$1^1@1$5-r0\3n17$0@1$3@2$2Ni3^h4@2$8N0Ni0").

(* [comment removed for export] *)
Definition ot_cells : ltac2:(zQ "40!hq6!h9!j4!t5@1$2@2$0@2$0$1$3$1") := ltac2:(zQ "60!h9!hq6!t5!ki4!jb!k2@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrnki0N8+hpstl4@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrnlp8N8+hqlmi4@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrnlq0N8+hqlqi8@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrnlk8N8+hqmhm8@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrnjt8N8+hqlli8@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hsgij8N8+nvvvogg0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hsgvh8N1+1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hsgvh9N1+1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+ilhtrcN1+1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+ilhum3N1+1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrpvg8N4+5@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrpvi8N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrpvj0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrpvk0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrpvl0N8+hprtu8@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrpvm0N8+nhkrv0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrpvm8N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrpvo0N4+2@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrpvp0N4Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrpvp4N4+vvvvvvvf@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrpvp8N4+vvvvvvvf@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nvvvshp8N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nvvvshq0N8Z@1$5@2$1@2$1$0$2$0").

(* [comment removed for export] *)
Definition OT_SHOFFS : ltac2:(zQ "20!j4!h9@1$0$1") := ltac2:(zQ "30!h9!jb!k2@3$1$0-il0@3$1$0-ik0@1$2$0").
Definition OT_SHOFFS2 : ltac2:(zQ "20!j4!h9@1$0$1") := ltac2:(zQ "30!h9!jb!k2@3$1$0-il0@3$1$0-ik0@3$1$0-ijf@1$2$0").
Definition OT_SHX : ltac2:(zQ "20!j4!hpe@1$0$1") := ltac2:(zQ "90!jva!iq1!juf!kg2!hpe!jb!kib!kj6!k2@3$5$4@3$0$6@3$0$2@3$0$7@3$0$2@3$0$2@1$3N2@1$3Nod@1$1-1@1$1+3@1$1+nvvvogg0@1$1-8@3$5$4@3$0$6@3$0$2@3$0$7@1$3N2@1$1+3@1$1+nvvvogg0@1$1-8@3$5$4@3$0$6@3$0$2@3$0$7@3$0$2@3$0$2@1$3N0@1$3Nod@1$1-ik0@1$1+3@1$1+nvvvogg0@1$1-8@3$5$4@3$0$6@3$0$2@3$0$7@3$0$2@3$0$2@1$3N0@1$3Nod@1$1-ijf@1$1+3@1$1+nvvvogg0@1$1-8@1$8$4").
Fixpoint shxkn (l : list expr) : list kentry :=
  match l with [] => [] | e :: r => KRange e 0x20000000000 0x10007fff8000 :: KZero (SA e 0) (ELit 8) :: shxkn r end.

Definition knV0 : ltac2:(zQ "20!j4!ij1@1$0$1") := ltac2:(zQ "h40!ij1!kg2!jb!kk1!kk7!iq1!kl0!kl6!kle!km6!kn0!k2!ks8!lh2!lhd!lm4!lmc!ln8!lo3!lq5@3$6$0@3$2$0@2$h2@1$1N0+h0@3$2$0@3$9@1$1N0+nvvvogggggg0+ogggggggggg0@3$2$0@2$a@2$3@1$1N0@2$h3-o0$7$7@3$2$0@3$9@1$1N2$e$d@3$2$0@2$8+hggg0+mngg0@3$2$0@2$8+hqtgg0+hrngg0@3$2$0@3$4@2$3@1$1N0-r0N8@1$1N2@3$2$0@3$4@2$3@1$1N0-r8N8@1$5+ruro4@3$2$0@3$4@2$3@1$1N0-s0N8@1$1Nb@3$2$0@3$4@2$3@1$1N0-s8N8@1$1Nc@3$2$0@3$4@2$3@1$1N0-t0N8@1$1Nh5@3$2$0@3$4@2$3@1$5Z+nhkkh8N8@1$1N1@3$2$0@2$a@2$3@1$5Z+hrpvg8+u8@1$b$0@3$6$0@1$f$h0@1$c$h1").
(* [comment removed for export] *)
Definition not_px_range (k : kentry) : bool := match k with KRange (EVar 141) _ _ => false | _ => true end.
Definition px_range : ltac2:(zQ "30!j4!h9!ij1>2lo$1>2hi$1>2kn@1$0$2@1$0$2") := ltac2:(zQ "80!ij1!h9!jb!j4!lsf!lt4!km6!jr1\2lo$1\2hi$1\2kn@1$3$0@3$2$0@3$6$4^3^2@3$7$0$5^1").
(* [comment removed for export] *)
Definition kn_readd : ltac2:(zQ "30!j4!h9!ij1>3plo$1>3phi$1>2kn@1$0$2@1$0$2") := ltac2:(zQ "90!ij1!kl0!h9!j4!lm4!lu3!lv0!lv9!mg4\3plo$2\3phi$2\2kn@1$3$0@3$7^3^2@3$1$0@1$8$6@3$1$0@1$4$5^1").

(* [comment removed for export] *)
Definition ssB0 : ltac2:(zQ "10!hqd$0") := ltac2:(zQ "50!k2!mgc!mh3!mha!mi0@5$3+hpstl4$2@1$0$4$1Nk3").
Definition rB := Eval vm_compute in runT (SCR [false] [] []) ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_afterT rB knV0.
(* [comment removed for export] *)
Definition logM1 : ltac2:(zQ "20!j4!mi0@1$0$1") := ltac2:(zQ "70!mi0!jb!iq1!kg2!kk1!mia!k2@3$1$0@3$5@2$4@1$3N0-ik0N1@1$2+i0@3$1$0@3$5@2$4@1$3N0-ik8N8@1$2+mumlngmvignkmvme@3$1$0@3$5@2$4@1$3N0-il0N8@1$2+mumhmjigjqmpmsm3@1$6$0").
Definition knC0 : list kentry := Eval vm_compute in fst (fst (carry logM1 knB [])).
Definition srC0 : list expr := Eval vm_compute in sr_after_call_j srB KEPT_MC 67.
(* [comment removed for export] *)
Definition ssC0 : ltac2:(zQ "10!hqd$0") := ltac2:(zQ "60!k2!mj0!mje!mk5!mha!mi0@5$4$1$3@1$0$5$2Nm3").
Definition rC := Eval vm_compute in runT (SCR [] [] []) ssC0.
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC)).
Definition knC : list kentry := Eval vm_compute in kn_afterT rC knC0.
Definition srD0 : list expr := Eval vm_compute in sr_after_call_j srC KEPT_MC 99.
(* [comment removed for export] *)
Definition ssD0 : ltac2:(zQ "10!hqd$0") := ltac2:(zQ "60!k2!mj0!mkc!ml2!mha!mi0@5$4$1$3@1$0$5$2No3").
Definition rD := Eval vm_compute in runT (SCR [] [] []) ssD0.
Definition srD : list expr := Eval vm_compute in s_regs (fst (fst rD)).
Definition knD : list kentry := Eval vm_compute in kn_afterT rD knC.
(* [comment removed for export] *)
Definition knE0 : list kentry := Eval vm_compute in kn_readd 0 131071 (kn_cut 0 (-1152 - 4400) (-1152) IHI knD).
Definition srE0 : list expr := Eval vm_compute in sr_after_call_j srD KEPT_CS 131.
(* [comment removed for export] *)
Definition ssE0 : ltac2:(zQ "10!hqd$0") := ltac2:(zQ "60!k2!ml9!mm8!mmf!mha!mi0@5$4$1$3@1$0$5$2Nq3").
Definition rE := Eval vm_compute in runT (SCR [false] [ELit 0] []) ssE0.
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
Definition knE : list kentry := Eval vm_compute in kn_afterT rE knE0.
Definition srF0 : list expr := Eval vm_compute in sr_after_call_j srE KEPT_MC 163.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FQMAX : Z := 63.
Definition knF0_ : list kentry := Eval vm_compute in px_range 1 FQMAX knE.
Definition ssF0 : ltac2:(zQ "10!hqd$0") := ltac2:(zQ "60!k2!mj0!mn6!mne!mha!mi0@5$4$1$3@1$0$5$2Ns3").
Definition rF := Eval vm_compute in runT (SCR [true; false; true; false; false] [] []) ssF0.
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF)).
Definition knF : list kentry := Eval vm_compute in kn_afterT rF knF0_.
Definition knG0 : list kentry := Eval vm_compute in kn_readd 0 62 (kn_cut 0 (BUF_LO + NPRE) BUF_HI IHI knF).
Definition srG0 : list expr := Eval vm_compute in sr_after_call_j srF KEPT_MCI 195.
(* [comment removed for export] *)
Definition knF00 : list kentry := Eval vm_compute in px_range 0 0 knE.
Definition rF0 := Eval vm_compute in runT (SCR [false; true] [] []) (SS AMEMCPY_RET srF0 [] knF00 195).
Definition knF0' : list kentry := Eval vm_compute in kn_afterT rF0 knF00.
(* [comment removed for export] *)
Definition ssG0 : ltac2:(zQ "10!hqd$0") := ltac2:(zQ "60!k2!mj0!mo5!moc!mha!mi0@5$4$1$3@1$0$5$2Nu3").
Definition rG := Eval vm_compute in runT (SCR [false] [] []) ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_afterT rG knG0.
Definition knH0 : list kentry := Eval vm_compute in kn_readd 0 62 (kn_cut 0 (BUF_LO + NPRE) BUF_HI IHI knG).
Definition srH0 : list expr := Eval vm_compute in sr_after_call_j srG KEPT_MC 227.
(* [comment removed for export] *)
Definition ssH0 : ltac2:(zQ "10!hqd$0") := ltac2:(zQ "60!k2!mj0!mp3!mpa!mha!mi0@5$4$1$3@1$0$5$2Nhg3").
Definition rH := Eval vm_compute in runT (SCR [] [] []) ssH0.
Definition srH : list expr := Eval vm_compute in s_regs (fst (fst rH)).
Definition knH : list kentry := Eval vm_compute in kn_afterT rH knH0.
Definition scOF : stdio_res := Eval vm_compute in sc_of 259 srH knH.
Definition srI0 : list expr := Eval vm_compute in sc_sr scOF.
Definition knI0 : list kentry := Eval vm_compute in sc_kn scOF.
(* [comment removed for export] *)
Definition ssI0 : ltac2:(zQ "10!hqd$0") := ltac2:(zQ "50!k2!mq1!mq8!mha!mi0@5$3+hpsunc$2@1$0$4$1Nhi3").
Definition rI := Eval vm_compute in runT (SCR [] [] []) ssI0.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition knG30 : list kentry := Eval vm_compute in kn_readd (62 + 1) (62 + NSUF) (kn_cut 0 (BUF_LO + NPRE) BUF_HI IHI knF).
Definition ssG30 : ltac2:(zQ "10!hqd$0") := ltac2:(zQ "60!k2!mj0!mqf!moc!mha!mi0@5$4$1$3@1$0$5$2Nu3").
Definition rG3 := Eval vm_compute in runT (SCR [] [] []) ssG30.
Definition srG3 : list expr := Eval vm_compute in s_regs (fst (fst rG3)).
Definition knG3 : list kentry := Eval vm_compute in kn_afterT rG3 knG30.
Definition scG3 : stdio_res := Eval vm_compute in sc_of 227 srG3 knG3.
Definition srH30 : list expr := Eval vm_compute in sc_sr scG3.
Definition knH30 : list kentry := Eval vm_compute in sc_kn scG3.
(* [comment removed for export] *)
Definition ssH30 : ltac2:(zQ "10!hqd$0") := ltac2:(zQ "70!k2!mr7!ms1!ms9!mt0!mha!mi0@5$5@1$1$3$4@1$0$6$2Nhg3").
Definition rH3 := Eval vm_compute in runT (SCR [] [] []) ssH30.
Definition srH3 : list expr := Eval vm_compute in s_regs (fst (fst rH3)).
Definition knH3 : list kentry := Eval vm_compute in kn_afterT rH3 knH30.
Definition scH3 : stdio_res := Eval vm_compute in sc_of 259 srH3 knH3.
Definition srI30 : list expr := Eval vm_compute in sc_sr scH3.
Definition knI30 : list kentry := Eval vm_compute in sc_kn scH3.
(* [comment removed for export] *)
Definition ssI30 : ltac2:(zQ "10!hqd$0") := ltac2:(zQ "50!k2!mt8!mu0!mha!mi0@5$3+hpsunc$2@1$0$4$1Nhi3").
Definition rI3 := Eval vm_compute in runT (SCR [] [] []) ssI30.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition knF40 : list kentry := Eval vm_compute in px_range (62 + NSUF + 1) 131071 knE.
Definition ssF40 : ltac2:(zQ "10!hqd$0") := ltac2:(zQ "60!k2!mj0!mu8!mne!mha!mi0@5$4$1$3@1$0$5$2Ns3").
Definition rF4 := Eval vm_compute in runT (SCR [true] [] []) ssF40.
Definition srF4 : list expr := Eval vm_compute in s_regs (fst (fst rF4)).
Definition knF4 : list kentry := Eval vm_compute in kn_afterT rF4 knF40.
Definition scF4 : stdio_res := Eval vm_compute in sc_of 195 srF4 knF4.
Definition srG40 : list expr := Eval vm_compute in sc_sr scF4.
Definition knG40 : list kentry := Eval vm_compute in kn_readd (62 + NSUF + 1) 131071 (sc_kn scF4).
(* [comment removed for export] *)
Definition ssG40 : ltac2:(zQ "10!hqd$0") := ltac2:(zQ "70!k2!mr7!mv0!mv8!mvf!mha!mi0@5$5@1$1$3$4@1$0$6$2Nu3").
Definition rG4 := Eval vm_compute in runT (SCR [false] [] []) ssG40.
Definition srG4 : list expr := Eval vm_compute in s_regs (fst (fst rG4)).
Definition knG4 : list kentry := Eval vm_compute in kn_afterT rG4 knG40.
(* [comment removed for export] *)
Definition logNL : ltac2:(zQ "20!j4!mi0@1$0$1") := ltac2:(zQ "70!mi0!jb!k2!iq1!kg2!kk1!mia@3$1$0@3$6@2$5@1$4N0-il0N1@1$3+a@1$2$0").
Definition knH40 : list kentry := Eval vm_compute in fst (fst (carry logNL knG4 [])).
Definition srH40 : list expr := Eval vm_compute in sr_after_call_j srG4 KEPT_MC 227.
(* [comment removed for export] *)
Definition ssH40 : ltac2:(zQ "10!hqd$0") := ltac2:(zQ "60!k2!mj0!ng7!ngf!mha!mi0@5$4$1$3@1$0$5$2Nhg3").
Definition rH4 := Eval vm_compute in runT (SCR [] [] []) ssH40.
Definition srH4 : list expr := Eval vm_compute in s_regs (fst (fst rH4)).
Definition knH4 : list kentry := Eval vm_compute in kn_afterT rH4 knH40.
Definition scH4 : stdio_res := Eval vm_compute in sc_of 259 srH4 knH4.
Definition srI40 : list expr := Eval vm_compute in sc_sr scH4.
Definition knI40 : list kentry := Eval vm_compute in sc_kn scH4.
(* [comment removed for export] *)
Definition ssI40 : ltac2:(zQ "10!hqd$0") := ltac2:(zQ "50!k2!nh7!nhf!mha!mi0@5$3+hpsunc$2@1$0$4$1Nhi3").
Definition rI4 := Eval vm_compute in runT (SCR [] [] []) ssI40.

(* [comment removed for export] *)
Definition ot_regions : ltac2:(zQ "20!j4!nm0@1$0$1") := ltac2:(zQ "b0!h9!lqc!hq6!jb!ki4!kl6!kk1!k2!iq1!kg2!lq5@3$3@2$2$1$0@4$4$1$0@2$6@1$9N0@2$a-o0$5$5@3$3@2$2$1$0@4$4$1$0@2$6@1$8Z+hrpvg8+u8@1$7@2$2$1$0").
Definition scsB : list sidecond := Eval vm_compute in (snd (fst rB)).
Lemma factsB : ltac2:(zQ "h42!j4!hra!ijb!hqd!hq6!hp0!nnf!no5!ho5!k2!noa!np0!ij1!ika!hs6!mgc!np7!nq4!nqb!ik1&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_open_defs ()) ["FPX1"] "p;1p;3p;4p;2g0000j13Tg000Pj1DTg001Wj10Tg002<j15Tg002aj1=Tg003?j16Tg004Fj3:Tg005Mj1@Tg005kj4?Tg0076j19Tg007Vj3>Tg0086j31Tg008Pj24Tg008kj27Tg009Ej4<Tg009`j28Tg00:@j32Tg00:]j3;Tg00;:j1CTg00<@j3BTg00=Fj2ATg00>LR0#3R1g00?Wg00@7g00@ig00AUg00BA#Dg00B`R2#0#0R3#5#0#5#0#0#0#0#=#63:%=2#63:%03#5#@#6C?%90R35>0R0;10A1133R2g00CER4g00CeR5;15R6'41710P2P617131745C<C<g00DER61861g00EQg00F[32R27;1g00Ge511g00I1#3R01801%34A2612#CR2g00J:%943B327;1=113g00KF/A2=145'4'4do"). Qed.
Definition scsC : list sidecond := Eval vm_compute in (snd (fst rC)).
Lemma factsC : ltac2:(zQ "h42!j4!hra!ijb!hqd!hq6!hp0!nnf!nra!ho5!k2!noa!np0!ij1!ika!hs6!mje!np7!nrf!nqb!ik1&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_open_defs ()) ["FPX1"] "p;1p;3p;2p;4g0000j13Tg0076j18Tg0086j30Tg008Pj21Tg008kj27Tg009Ej46Tg009`j25Tg00:@j32Tg00:]j34Tg00;:j1;Tg00<@j3:Tg00=Fj29Tg00>LR0#3R1%80R0;00R2g00CER3g00CeR4;04R5,121710R6P2P5P61734C6C6g00DER61561g00EQg00LX32R5741g00Mb501g00I1#3R21521%33A2615#;R5g00Nn%833:32741=010g00KF/95=034'1'1do"). Qed.
Definition scsD : list sidecond := Eval vm_compute in (snd (fst rD)).
Lemma factsD : ltac2:(zQ "h42!j4!hra!ijb!hqd!hq6!hp0!nnf!ns6!ho5!k2!noa!np0!ij1!ika!hs6!mkc!np7!nsb!nqb!ik1&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_open_defs ()) ["FPX1"] "p;1p;3p;2p;4g0000j13Tg0076j18Tg0086j30Tg008Pj21Tg008kj27Tg009Ej46Tg009`j25Tg00:@j32Tg00:]j34Tg00;:j1;Tg00<@j3:Tg00=Fj29Tg00>LR0#3R1%80R0;00R2g00CER3g00CeR4;04R5,121710R6P2P5P61734C6C6g00DER61561g00EQg00P:32R5741g00QD501g00I1#3R21521%33A2615#;R5g00RP%833:32741=010g00KF/95=034'1'1do"). Qed.
Definition scsE : list sidecond := Eval vm_compute in (snd (fst rE)).
Lemma factsE : ltac2:(zQ "h42!j4!hra!ijb!hqd!hq6!hp0!nnf!nt2!ho5!k2!noa!np0!ij1!ika!hs6!mm8!np7!nt7!nqb!ik1&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1z (kr_t_AsTail_open_defs ()) ["FPX1"] "##,,p;1p;3p;4p;2g0000j14Tg00S[j10Tg000Pj1;Tg003?j1GTg00T:j3BTg005kj4ATg004Fj3@Tg00UAj2>Tg00VIj4=Tg0076j17!s/$Vj3<Tg0086j32!s/$Pj26!s/$kj25Tg009Ej48!s/$`j29Tg00:@j33!s/$]j3:Tg00;:j1FTg00<@j3DTg00=Fj2ETf0R0#0#0p=C%0!s0$!s$,p=?!s:4!s$3p=1g00>LR0#4R1g00?WR2g00WTg00AUR3g00BA#0R4#0R5#0#C#?#1!s$2;R6g00XFR7#GR83BP6CA%;5=@36/>7P4P2P8C=%70R85<05<0R0;20A2188!t;$CER4g00CeR7;27R6'61510P2P615181547C8C8g00DER61961g00EQg00Xd33R27:1g00Yn521g00I1#4R01901%44A3612#F!t4$[:%743D337:1=218g00KF/E2=247'6'6do"). Qed.
Definition scsF : list sidecond := Eval vm_compute in (snd (fst rF)).
Lemma factsF : ltac2:(zQ "h42!j4!hra!ijb!hqd!hq6!hp0!nnf!nte!ho5!k2!noa!np0!ij1!ika!hs6!mn6!np7!nu3!nqb!ik1&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1z (kr_t_AsTail_open_defs ()) ["FPX1"] "##-^p;1p;3p;4p;2g0000j17Tg000Pj1=Tg001Wj18Tg002<j13!s/$aj1DTg003?j1:Tg004Fj36Tg00S[j10Tg005kj45Tg00\Fj4ETg00T:j3CTg0076j1B!s/$Vj34Tg0086j32!s/$Pj2;!s/$kj29Tg009Ej4@!s/$`j2ATg00:@j3<!s/$]j3?Tg00;:j1ITg00<@j3HTg00=Fj2GTf0R0#0#0p=>%0!s0$!s$,p=F!s:4!s$3p=1g00>LR0#7R1g00?WR2g00@7R3g00@iR4g00AUR5g00BAR6#=R7g00B`R8#!s$%3!s$-D#:R936R:%D8#:R836%>6R;#>R<#0#F#1!s$2=R=C5P2P3%=;R;=648P=C5g00CeR8g00]MP;A657==659C5P2g00^?P:P;C5P8g00_1P8P6P<P=CEg00XF#:R<9C5==C5<C5%B0R<540!s%/R0;20A21<<!uK$CER=?288R6';1910P5P6191<19=8C@C@g00DER61A61g00EQg00_c3<R57?1g00`m521g00I1#7R01A01%7=A<615#I!t-$b9%B=3H3<7?1=21<g00KF/G5=2=8';';do"). Qed.
Definition scsF0 : list sidecond := Eval vm_compute in (snd (fst rF0)).
Lemma factsF0 : ltac2:(zQ "h42!j4!hra!ijb!hqd!hq6!hp0!nnf!nua!ho5!k2!noa!np0!ij1!ika!hs6!nv0!np7!nv8!nqb!ik1&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1z (kr_t_AsTail_open_defs ()) ["FPX1"] "##,Ap;1p;3p;4p;2g0000j15Tg000Pj1:Tg00S[j10Tg004Fj37Tg001Wj16Tg002<j12!s/$aj1CTg003?j1BTg005kj4<Tg0076j1;!s/$Vj3@Tg0086j33!s/$Pj28!s/$kj29Tg009Ej4>!s/$`j2?Tg00:@j34!s/$]j3=Tg00;:j1FTg00<@j3ETg00=Fj2DTf0R0#0#0p=A%0!s0$!s$,p=G!s:4!s$3p=1g00>LR0#5R1g00CeR2g00]Mg00BAR3#AR4#:R5g00AUR6%:3R3%04#A#G#1!s$2:576g00B`#6!s$$2!s$-C#BR437C<g00?Wg00^?A7634P5C<%;0R55@05@0R0;30A3155R4g00CER3?322R6'81910P4P619151932C>C>g00DER61?61g00EQg00cF34R47!uN$dQ531g00I1#5R01?01%53A4614#F!t-$e^%;33E347=1=315g00KF/D4=332'8'8do"). Qed.
Definition scsG : list sidecond := Eval vm_compute in (snd (fst rG)).
Lemma factsG : ltac2:(zQ "h42!j4!hra!ijb!hqd!hq6!hp0!nnf!og0!ho5!k2!noa!np0!ij1!ika!hs6!mo5!np7!og5!nqb!ik1&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1z (kr_t_AsTail_open_defs ()) ["FPX1"] "##,Bp;1p;3p;4p;2g0000j1:Tg000Pj1?Tg00S[j10Tg004Fj35Tg001Wj16Tg002<j12!s/$aj1<Tg003?j14Tg005Mj1B!s/$kj4ATg0076j1@!s/$Vj3GTg0086j33!s/$Pj27!s/$kj29Tg009Ej4>!s/$`j2=Tg00:@j38!s/$]j3;Tg00;:j1ETg00<@j3DTg00=Fj2FTf0R0#!s$&p=C%0!s4+!s:'H!s:4!s$3p=1g00>LR0#:R1g00?Wg00@7g00@ig00AUR2g00BAR3#?%03#C#H#1!s$2?55!sK$`R2#6!s$$2!s$-<#435%<2!s,$B2#4CA%@0R25G0R0;30A3122R3g00CER4g00CeR5;35R6'71910P3P619121945C>C>g00DER61=61g00EQg00fk38R37;1g00h5531g00I1#:R01=01%:4A8613#E!t4$iA%@43D387;1=312g00KF/F3=345'7'7do"). Qed.
Definition scsH : list sidecond := Eval vm_compute in (snd (fst rH)).
Lemma factsH : ltac2:(zQ "h42!j4!hra!ijb!hqd!hq6!hp0!nnf!ogc!ho5!k2!noa!np0!ij1!ika!hs6!mp3!np7!oh1!nqb!ik1&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_open_defs ()) ["FPX1"] "p;1p;3p;2p;4g0000j13Tg0076j18Tg0086j30Tg008Pj21Tg008kj27Tg009Ej46Tg009`j25Tg00:@j32Tg00:]j34Tg00;:j1;Tg00<@j3:Tg00=Fj29Tg00>LR0#3R1%80R0;00R2g00CER3g00CeR4;04R5,121710R6P2P5P61734C6C6g00DER61561g00EQg00jM32R5741g00kW501g00I1#3R21521%33A2615#;R5g00lc%833:32741=010g00KF/95=034'1'1do"). Qed.
Definition scsG3 : list sidecond := Eval vm_compute in (snd (fst rG3)).
Lemma factsG3 : ltac2:(zQ "h42!j4!hra!ijb!hqd!hq6!hp0!nnf!oh8!ho5!k2!noa!np0!ij1!ika!hs6!mqf!np7!ohe!nqb!ik1&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_open_defs ()) ["FPX1"] "p;1p;3p;2p;4g0000j13Tg0076j18Tg0086j30Tg008Pj21Tg008kj27Tg009Ej46Tg009`j25Tg00:@j32Tg00:]j34Tg00;:j1;Tg00<@j3:Tg00=Fj29Tg00>LR0#3R1%80R0;00R2g00CER3g00CeR4;04R5,121710R6P2P5P61734C6C6g00DER61561g00EQg00mo32R5741g00o:501g00I1#3R21521%33A2615#;R5g010G%833:32741=010g00KF/95=034'1'1do"). Qed.
Definition scsH3 : list sidecond := Eval vm_compute in (snd (fst rH3)).
Lemma factsH3 : ltac2:(zQ "h42!j4!hra!ijb!hqd!hq6!hp0!nnf!oi6!ho5!k2!noa!np0!ij1!ika!hs6!ms1!np7!oic!nqb!ik1&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_open_defs ()) ["FPX1"] "p;1p;3p;2p;4g0000j13Tg0076j18Tg0086j30Tg008Pj21Tg008kj27Tg009Ej46Tg009`j25Tg00:@j32Tg00:]j34Tg00;:j1;Tg00<@j3:Tg00=Fj29Tg00>LR0#3R1%80R0;00R2g00CER3g00CeR4;04R5,121710R6P2P5P61734C6C6g00DER61561g00EQg011T32R5741g012_501g00I1#3R21521%33A2615#;R5g013l%833:32741=010g00KF/95=034'1'1do"). Qed.
Definition scsF4 : list sidecond := Eval vm_compute in (snd (fst rF4)).
Lemma factsF4 : ltac2:(zQ "h42!j4!hra!ijb!hqd!hq6!hp0!nnf!oj4!ho5!k2!noa!np0!ij1!ika!hs6!mu8!np7!oja!nqb!ik1&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1z (kr_t_AsTail_open_defs ()) ["FPX1"] "##+_p;1p;4p;3p;2g0000j13Tg00S[j10Tg000Pj1DTg00\Fj4CTg003?j1?Tg00T:j38Tg005kj4>Tg0076j17!s/$Vj3<Tg0086j32!s/$Pj26!s/$kj24Tg009Ej4;!s/$`j2:Tg00:@j35!s/$]j39Tg00;:j1BTg00<@j3@Tg00=Fj2ATf0R0#!s$&p=E%0!s4+!s:'=!s:4!s$3p=1g00>LR0#3R1g00CeR2g00_1P2g00BAR3%E3R3%03#=#1!s$2DR3CCg00AUR4g00XF#?R59843;85C>%70R55<0R0;20A2155!sL$CER3?222R6'61410P4P614151432C;C;g00DER61:61g00EQg015935R4791g016D521g00I1#3R01:01%33A5614#BR4g017Q%733@35791=215g00KF/A4=232'6'6do"). Qed.
Definition scsG4 : list sidecond := Eval vm_compute in (snd (fst rG4)).
Lemma factsG4 : ltac2:(zQ "h42!j4!hra!ijb!hqd!hq6!hp0!nnf!ok2!ho5!k2!noa!np0!ij1!ika!hs6!mv0!np7!ok8!nqb!ik1&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_open_defs ()) ["FPX1"] "p;1p;3p;4p;2g0000j13Tg000Pj1DTg001Wj10Tg002<j17Tg002aj1=Tg003?j15Tg004Fj3:Tg005Mj1@Tg005kj4?Tg0076j19Tg007Vj3>Tg0086j31Tg008Pj24Tg008kj26Tg009Ej4<Tg009`j28Tg00:@j32Tg00:]j3;Tg00;:j1CTg00<@j3BTg00=Fj2ATg00>LR0#3R1g00?Wg00@7g00@ig00AUg00BA#Dg00B`R2#0#0#7#0#7#0#0#0#0#=#53:%=2#53:%@2#5C?%90R25>0R0;10A1122R3g00CER4g00CeR5;15R6'41610P3P616121645C<C<g00DER61861g00EQg018^32R37;1g019i511g00I1#3R01801%34A2613#CR3g01;6%943B327;1=112g00KF/A3=145'4'4do"). Qed.
Definition scsH4 : list sidecond := Eval vm_compute in (snd (fst rH4)).
Lemma factsH4 : ltac2:(zQ "h42!j4!hra!ijb!hqd!hq6!hp0!nnf!ol0!ho5!k2!noa!np0!ij1!ika!hs6!ng7!np7!ol6!nqb!ik1&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_open_defs ()) ["FPX1"] "p;1p;3p;2p;4g0000j13Tg0076j18Tg0086j30Tg008Pj21Tg008kj27Tg009Ej46Tg009`j25Tg00:@j32Tg00:]j34Tg00;:j1;Tg00<@j3:Tg00=Fj29Tg00>LR0#3R1%80R0;00R2g00CER3g00CeR4;04R5,121710R6P2P5P61734C6C6g00DER61561g00EQg01<C32R5741g01=N501g00I1#3R21521%33A2615#;R5g01>[%833:32741=010g00KF/95=034'1'1do"). Qed.

(* [comment removed for export] *)
Lemma ot_itinerary : ltac2:(zQ "j20!h9!hq6!ijb!j4!hra!hqd!ki4!ole!ho5!ip4!nnf!np0!q7!om6!iq9!ira!r8!p4!s7!omd!on4!onb!oo1!oo8!no5!nra!ns6!nt2!nte!nua!oj4!og0!oh8!ok2!ogc!oi6!ol0!oof!op4!opa!mv8!ms9!oq0!oq7!oqe!or5!orc!os3!os9!ot0@2$b@3$a@2$1@2$1@2$1$0$0$0$0@4$6@2$1@2$1$0$0$0$0@4$6@2$1$0$0$0@4$6$0$0@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$h8@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$h9@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$ha@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$hb@4$6@2$1@2$1$0$0$0$0@4$6@2$1$0$0$0@4$6$0$0$c$c$h2$c@2$b@3$a@2$1@2$1@2$1@2$1$0$0$0$0$0@4$6@2$1@2$1@2$1$0$0$0$0$0@4$6@2$1@2$1$0$0$0$0@4$6@2$1$0$0$0@4$6$0$0@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$hc@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$hd@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$hf@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$i2@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$i5@4$6@2$1@2$1@2$1$0$0$0$0$0@4$6@2$1@2$1$0$0$0$0@4$6@2$1$0$0$0@4$6$0$0$c$c$c$h0$h1@2$b@3$a@2$1@2$1$0$0$0@4$6@2$1$0$0$0@4$6$0$0@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$i0@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$i3@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$i6@4$6@2$1$0$0$0@4$6$0$0$h0$h0$h1@2$b@3$a@2$1@2$1@2$1$0$0$0$0@4$6@2$1@2$1$0$0$0$0@4$6@2$1$0$0$0@4$6$0$0@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$he@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$i1@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$i4@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$i7@4$6@2$1@2$1$0$0$0$0@4$6@2$1$0$0$0@4$6$0$0$h0$c$h0$h1@2$b@3$a@1$e$9@3$fNhg3$if$h5@2$d$9$ic@2$b@3$a@1$e$9@3$fNu3$ie$h4@2$d$9$i9@2$b@3$a@1$e$9@3$fNhg3$j0$h6@2$d$9$ia@2$b@3$a@1$e$9@3$fNs3$id$h3@2$d$9$i8@3$a@1$e$9@3$fNhg3$j1$h7@2$d$9$ib").
Proof.
ltac2:(KReplay.run1z (kr_t_AsTail_open_defs ()) ["FPX1"] "##mQp%0p%1p&0p;2p;1p;3p;<p;4g009`j2rTg002<j11Tg001Wj10Tg0086j3PTg01?hk10CTg005Mj1>Tg000Pj17!s]$aj1=Tg00S[j12Tg003?j1@Tg00T:j3lTg0076k10<Tg01@Jj3KTg01ASj2aTg01B\j3?Tg00UAj2CTg01Cek20ATg01Dnk209Tg01F7k208Tg01G@l<nTg01HNj2R!tu$Pj2Y!s/$kk206!tl$0k10?Tg01I0j4F!s/$Pj3qTg004Fj3t!td$Vj34Tg009Ek40!uL$:@j3sTg01J]k103Tf0R0#0#1p=B%00#!s2&]!s2%1#0p=V%00#>p=wg01KbR1P1f1R2P0CFp=_%0!sL$#0p=^!sZ'1p=H!sr'0p=:!s2'>p=9f4R3P1f3R4P1f2R5P2CF!sq%gP5P1P!s~%>0=%1!sq%>01%1!s~+p!s=%!tr$j!s>$p=6!tR%!sF$i!s]&#0p=`!tF$p=8g00AUR6%@07t2p=S%20#2p>05!s/$#2#2p=T!s2&p=o!s<+!s$'p=m!s:4!s$3p=UAt620p=G%00#=p=z%>0#@p=A!ta'1p=L!ty'0p=N!v5%>#@p=J!uY%!t}$f!uY'0p=Og01L@R7%72;40p>02%75%72=470547p=D!s3&94759474p=kA472!s6+9473p=W%74!s=+547p>001C45??20p=yg01MG?t20p=d!t{+!s$'p=[!x-&p=<!xD+!s$'p=cg01N3!sd%b!sd$p=Qg00XFR8,C0p=e%05#=,C4!t<%;!sj%=,C2p=x%=0!s/$~%15!sz&!sQ,M!ys'1p=}1C45!vp$7?2p=v%10#>p>0B%@09?52p>0;!vc&p>0:g00I1R9%>4,C3??5!v]$=I%14!t4&>!s>&=490p=ZA4920949594!s$$3p=3A?4!sF&>0@%=4!sX05f6f5;?!sK,549p=|!sn+p=h!s2$p=uP3P420652P0H0>p=Xg00DER3As5207s4$03p=E!s4$9s34p>04!{q%&03!{s%7P2P1P0g01N_CFp={AP452/Y0p=\1r11R0/r1R5/r1R4P5P0g00B`R2#1R:#0R;#1R<#0S00#0S01#1S02#BS03#BS04#1#]#V#wR=/_=R>%1:R?#1R@#^#H#:#9P=DgRA;PA1r41S05P4P5B0=0>=%0;S06#1!t/$>#0S07$01#p#j#9RB!sD$8#6#V#i#`#wR;DgRC;PCS091_BB>0=0;RD=P5DS0:P5P01_B=PBP;DgR;=P4;S0;g01OlRE$0CRF%1<S0<!uB$HRG$01S0=#0RH#0RI#0S0>#B#9RJ%02RK#>RL%6>!td%?#1RM#1S0@#6#BS0A#1!t_$Ng00BARO#7RP%0KRQ#1RR#0RS#1RT#0S0B#8RU#0S0C#=S0D'SRV%2ORO#2RW$05RX#TRY#oS0E#2S0F#2#mS0G#2#URZ#US0H#2S0I#2S0J#2R[#2R\#2R]#2R^#2R_#2R`#o#T#m#U!s$%Ra#7Rb,GPRc%0Q!t_$d#1Re#1Rf#1Rg#1Rh#z'SPV%1KRK#0Ri#0S0K#0Rj#0Rk#ARl%@8RmPm%1R!uC$n#0S0L#8S0M#zS0N,SPRo&05a#T!tB+2#TS0O#2S0P#2S0Q#TS0R#2S0S#2S0T#2S0U#2S0V#2S0W#2S0X#o#mS0Y#2S0Z#2S0[#2S0\#2Rp!st%]#2S0^#2S0_#TS0`#2S0a#2S0b#2S0c#2S0d#2S0e#2S0f!st%g#2S0h#2S0i#2S0j#2Rq%@NPo%7ZS0k%1<#B#:#L#N#JS0l%2q#TR<%2<!s''@JRZ%A2RrAl6bmRs9l6mS0m%AdS0n5l6Rt5l6Pm%T<R<#7!s_-!s'70?S0o#8S0p#1#^R?#0#f#H#9S0q#@S0rPr%6?#L#O#JS0sPm%7[S0t%7\S0u%7]S0v%7^S0w%7_S0x%7`S0y%o<#m!t92&0<7R7+023DCkDWDW3D3D3DDW3DCkH00S0zPm%1IRI#B#9PY%0QR<#0R`#0S0{#8S0|#0R_#=,SPS0}CyR^Pm%6I#9PYPVCyRIPm%1HS0~#0S10#8!s?+H%1@R@#0S11#>9Kb8%7WRW/Gb%=2'S%A:R:'d%1@S12#1S13#1#[R@#<#:#cS14#AR2'G%=Q#@R8'bR]%:_R_#<S15#0#c#c#cS16#>R\%Q_R_#1#L#[R[#1#:#c#9R?3KRu%e]%AQRQ'aR]1dW:/G2/b8Rv?K\?Rw%ev/aQRv%0SRS#0S17#8S18#0Rx#=S19#@Ry,Gc/d!s^'z!s^${%ez/aQRz%1h#=#@Rh,GcS1:!sN,c!sN$\%ec/aQRc1dV!s@'|%0_#L#j#L#i#L#pR_#0#9%i[!s3$[#0#9R}3KR~%e|/aQR|1GPy!t#,y%1_#9R_;K}R}%ey/aQRy1GPhS1;!sL,8%1[#97K_R_%e8/aQRQPP%fjS1<PYPmC;Rj%6k,xPS1=%1`R8#6S1>#6#]!tP$Q#AR:7?YS1?%8kS1!x2$A#0,~PS1B??YrS1C!~_%1Rk#6!so$D%1[#JS1E!s_$FPP%<kS1GPYPZC;S1HPP%0RRR!tN$MS1IPP%8RS1J#0S1KPYP:C;S1LPP%1nRnPYPrCMS1MPP%<nS1N!sm'OPPQ0LPY%0M#H#j#JCMS0!s\$TRMPYQ1ECMS1PPP%<MS1Q!s]'RPPQ0BPYPtCMS0BPPQ0CPYg01Q:!zc%Q!yS$M#ARn;ltS0CC;S1SPP%1SRS#1S1T#8PYPnC;S1UPP%<SRSPY%ATS1VC;S1WPPQ17PY%1>S17#<#V#N#wS1X#@S1YCMS1ZPuPwP{P\P~PP%8g!wO&gPP%0eRe#8S1[#0PYQ0mC;R>PP%<fPYPbC;RfPP%zxS1\PY%1<Rx#1RT#1RR#1#6#B#}CvRkPPPe!vz%Re!t8-}P_PP%<8PYPWC;S1]PPQ0NPY%1iR8#0S0N#8R[!~;$CyRhPPQ19POP`CvR`PP%=SPY%8GRG#1#B#i#:#N#L#V#:#i#^!s2$N#`CvRSQ0D,CPS0D%VG#O#N#B#:#]#j#H#^#p#N#H#]$0B80;YS19PP%0dRd#1RGPY%1MS1^#QRM#8#O!s$-j#ACMS1!u7$!sN%!wk&0#[#[#AC;S1`PPQ1>#0RGPYQ07!z{$H!s$&JC;S07PP%<TPY%1URT#0#V#B!s`%>PP%0xRx#8S1a!w?%rC;S1bPPPx!zd'c!zd$PYPoC;S1d!u-&PYQ0}CMS0}PP%8dS1e#0PY%18S1f#<S1g#=R8,SPC;S1hPmQ0>#1RdPYPmPm%:!s/&Q0=$0:Rd#!#?N%R#<PX%1M!uR%PmQ0~#6RMPYPlPm%:MPYPV1CmJRMPX%AKS0~Q1@,~P!st$PQ0K#1S0K#<S1@!s9%%0[S0>PYPm1CP8PYPmQ1J!sW,1QPY!#=|&8#0S1Q#8S1J#=R[,SPS1iPPQ0MPY%7ORxPPPUPYQ0J#7PPQ18PYQ0I!s2%[PYQ0H!s2%ePYQ!s_$1aPYPZPPQ0|PY%QG#`#JRGPPQ11#8PYQ13#8#N#]#J%><-0APQ14#0!#7_$Q16#<#9R<5KP!to%QRU#O,xP%0KRK#`#9+09AKW?<Q15#>Q0?#<#:#9+08Q00!{{$6!so$0<#0#`R<#0R!sI,1CP[PYPW1xPKPY%0U#6#`#]#JPPQ06#:PYQ0E!uE$08!tz$0F!s4%!u0%0G#7Q0q,CmPYPxQ0o#1#9-09M!|{$m%6<R<#8#^#9PYQ0@#B#}#^CvPm%1<R<#6RM#BPY%@=Pm%6M!t=%3!u$$V#6#JPm%^<PYQ02#6#]#N!s:&Q?#jPYQ04#B!sN'Q0p#<R?#V#HPYP2Pm&01?#f#OR?#0POPrPm%1?!s/&QTRT#B#p#O!s7&6T#N#H!s3%Q10#1#:PY%@BPm%0d#:PX%@LPm&0:RPXQ1^#ARR!zq$PXPRPm%:@#NRR#B!{:&6R#:PYPm&0<9DIDZDZDI!s$0Z!s:&ZD3H0@D5D5D5F|3hD3!s2%!s$/F|!s+&I!sm&ZR9'uD3D3RR!s-%!s2$X9h}_!s4'!s$/M<n,RERd;PdRBPJPLQ1XPVQ1:PVPlP:PrQ1\,SPRTPpQ1YPTQ0kQ0lQ0]Q0^Q0_Q1VPnPrQ0`#7Q0aQ0bQ0cQ0dQ0eQ0fQ0CPtPZQ1EPrP:PmAl6smR6PrPsQ0gQ0hQ0iQ0j0027!#BN9P^PIPHQ12#>Rt=KbtRtPuP]PwPvP{PzP\PcP~P|P}PyP_PQPjQ1=??YWR?Q1B??YmR2Q1D??Y:R<PgP>PfPkP!#8A,Q1]PhP`PSQ19Q1_Q1`Q07Q1>PP%f8PYPxC;Q1bQ1cQ1dQ0}Q1h!~k&Q0yCMPPQ1J!{O%xPPQ1f#fPYQ0wPPQ1g!#5|$vPPQ0N!s>%uPPQ0>!s>%t!#44$!s>$~PPQ1@!s>%sPPQ1<PYPrPPQ1APYQ0!s0$GPYP!~q$K!#32%1NPYQ0A#i#JP9!y-5!s$&!xn'9!xn7!xj&Y=PFYRGPJPLPNPV!s$$lPmPmPoQ0z!wH%P!w=BP?Ah2<X!t&4X=PFXRt!yo%7#1#}#]#9RrPVQ1;!t6$WPbPTPa%@r!ys,OQ0PQ0Q!ys%bQ0R#7Q0SQ0TQ0UQ0VQ0WQ0XPmQ0nPZP:PmPWPmP6Q0mPsQ0YQ0ZQ0[Q0\!ynE0{#>%>@5KbRbPjP?P2P!y=1!ui61uQ99hy_!vh69=PF9R<!vh'Q1T#Q#=,SP!vp6Q0D%>i80;OPjQ1?Q1CQ1FQ1HQ1IQ1LQ1MQ1OQ0LQ1PQ1RQ0BQ1SQ1UQ1WQ1ZPb!wT@!u7B!sL%Q1]1uSR9hh`!~v7!uP2`=PF`Rh'YRR'YRS'YRQ'YR_'YRy'YR}'YP4PAQ09P}Q05PCQ0:PyP5PDQ0;P_P4P;PBPQPFPdPGPSPFPYPtPRPFPXP<PhPFP9206F`DX!s$1P!#Y6&>L$0?R`1r3`R3g00EQR9g00F[CEP`P3P9g00LXCE'_!s5+P:!sB-XdCED!#cY$0P1P1P1g01QfRhPhCFR<g01S5CFPhCFQ!#YJ$!s`+_c!sm-cF!t10fkH046070!s8+jM!sT,1TH!tC0<PhCFg01URR<CF,{!t4/mo!s^-1T!t4/1Vf!t4'1!sl$!sc$0!v9%!sK+59!sg-8^!sg0<C!sB-X1!tc$!u|&!tc%!sy%5PFg01Y<g01ZG5qqg01[R,RE!s=$\^g01]j5qpg01_6!s='`Bg01aN!sT%bZ!s='cfg01e25qag01f>,REg01gJg01hV!sR%ib,RE5PFC\!s$1do"). Qed.
End FPX1.
(* [comment removed for export] *)
