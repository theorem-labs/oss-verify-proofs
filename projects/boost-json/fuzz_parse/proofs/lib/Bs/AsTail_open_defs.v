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
Ltac2 kr_t_AsTail_open_defs () := KReplay.lz_vm "#$$MI47Corelib4Init9Datatypes4list00K89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX24expr02C13~~~K!t5+7Numbers7BinNums8positive02!sKG1!sK=1Z03!t}c1!t}&!smb3!ulC1Z02!t3]8sidecond!t~+!x4A1!sFB2!xt25Logic2eq00!s@83and00K!s[;1K!s[<1!z-=prod00C!sF;3fst!sC=sndC!vm\5s_log!vh%!sl^carry!sl&7!slN6SymAux;log_covered!sl%I!y7f0!y7Cbool!}1#ELinuxProcessSemantics5Riscv5Instr;branch_!s~$5!sXG5aluop06!sRN!zi=3nat!~]?!#3&+3I!udA0!v+B1!w?]9sym_state!w@'!sr]7scripts!sp'c!spO2Bs@AsTail_open_defs2rB!spj4scsB!uVc6kentry!uUl4knV!srk:ot_regions!wClC!wCnC!vRmC!yumD!uXn!srk3knC!#5ZA!#3`#2!#>2b4!t4&!#97\sadd!#?ie!#8K+6!uo'!#8'Q3!#@G?1!y@fE!y@nE!{rmE0!wCc!xz%7!w?Z6!sXT1!sXT4!x,fF!x,n!srk5knF0_!#3<jrF!#5mj5!uZ#0!u[o!#7WlG!x6nG!}=mG!uXmH!uXnH!uXmH0!zglG3!zgn!ssmknG3!u[mH!u[oH!u[nH!u[nF4!#3yn4!#3ym4!zmn!u[oG!u[nG!u[nH!u[oH!u[nH!u['!#S%;6option!#a0^!#O?&!#EU&!sod2!sok1!sok5!sok7!sok!#KEV2Bs;AsStdioCall9s!s0#_res!#b6C!y<'!#b8=!#`^#1C!t^^:!t^%call!t]%!#`'\4s_pc!{`3!#LJ50!#Wu\!#Ip$!#J_&!#^0L7!sRN:!~beAEXIT!v$&!yBi!uiU2!u=d7AMEMCPY!#5pi;ASTRNLEN_TR!syj2rI!spj<ASTDIO_WRIT!#RJj3rI3!sqm!#:?j3s!#H~k3kn!#IqmO!#ROl!#H~l4kn!srmsc!srn!#H}l4knH!uZn!srn!#H|l4kn!srmsc!srn!#FFl!x6#!uZn!sr'".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc4listhc4conshc3nil89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bsh0AsTail_open_defs4FPX1~~~~~~k85AEXITk88AMAINEPIk87AMEMCPYk84ARIPk8cASTDIO_WRITEk8bASTRNLEN_TRhc3nat37Corelib4Init7Decimaltb2D0tb2D2tb3Nil37Corelib4Init3Nathg1bof_num_uint37Corelib4Init6Numberhi2bUIntDecimal79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymExec23SX2~~~~~~hk67scriptshc4boolhk63SCRhk64exprhc4prodhk69sym_statehk68sidecondhc4truek85FUELTk85STOPThk68sym_exec69OSSVerifyaboost_jsonafuzz_parse6images9AsanUbsan1M~~~~~~hu9floaded_segmentshk66kentryhc3fsthk65carryhk65s_log79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsbAsStdioCall~~~~~~il89stdio_reshk64ELithc6optionil84SCR_il8astdio_call37Corelib5Lists7ListDefisd3map04Npos69OSSVerify6Proofsaboost_jsonafuzz_parse3libcRefMemcpyLib~~~~~~iv1bcallee_kepthk64ridx35stdpp9bitvectorbdefinitionsjk72bv46Stdlib5Arith8PeanoNat3Natjma3eqbhc4negbhc3orbk87KEPT_MC36Stdlib5Lists4Listjq36filteriv1ccallee_saved3h5LinuxProcessSemantics5Riscv5Instrjt07ALU_ADDhk64EAluhk64EVarhg13addk83spxk83FMTisd3seqhc4pairjt07ALU_ANDjt07ALU_SRLhk62SAhk65KWordhc3appk85OT_FRhk64KImghk66KRangehk63KWr79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs0d1A1s1P1r1i1n1t1f1F1i1r1s1t~~~~~~knc8kn_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AsShadow~~~~~~kt97AAPP_HIkt96AHI_LO79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7AsSxKit~~~~~~lic4shknk89OT_SHOFFSk88ot_cellshk66KAlign46Stdlib6ZArith6BinInt1Zlp23subhk65saddrjt05aluopjt05mulophc5falsek82PXk8cnot_px_rangek8aOT_SHOFFS2k86OT_SHXk88px_rangek85shxknk84knV0k84srV0hk62SShk66sentryhk62SEk8bAMEMCPY_RETk84knC0k84srC0k83knCk84srD0k8cASTRNLEN_RETk84knE0k84srE0k85knF0_k84srF0k84knG0k84srG0k84knH0k84srH0k84knI0k84srI0k85knG30il86sc_retk85knH30k84scG3k85srH30k85knI30k85srI30k85knF40k85knG40k84scF4k85srG40k85knH40k85srH40k85knI40k85srI4069OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SymAux~~~~~~nic7sregion37Corelib4Init5Logicnn02eqk82rBhc3sndnn03andk8aot_regionsk84scsBnicblog_coveredk82rCk84scsCk82rDk84scsDk82rEk84scsEk82rFk84scsFk83rF0k85knF00k85scsF0k82rGk84scsGk82rHk84scsHk83rG3k85scsG3k83rH3k85scsH3k83rF4k85scsF4k83rG4k85scsG4k83rH4k85scsH4hk64s_pchc4Somek84knF4k84knG3k83knHk84knH3k84knH4k82rIk83rI3k83rI4k84scH3k84scH4k84scOFk84srF4k84srG3k83srHk84srH3k84srH4" s.
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
Definition STOPT : ltac2:(zQ "20!j4!h9@1$0$1") := ltac2:(zQ "90!h9!jb!k2!p4!pc!q7!r1!r8!s7@3$1$0$5@3$1$0$8@3$1$0$7@3$1$0$3@3$1$0$4@3$1$0$6@1$2$0").
Definition FUELT : nat := 20000.
Definition scr0 : ltac2:(zQ "10!ho5$0") := ltac2:(zQ "40!k2!hp0!hp7!hpe@3$2@1$0$1@1$0$3@1$0$1").
Definition runT : ltac2:(zQ "50!hq6!ho5!hqd!j4!hra>3scr$1>2ss$2@2$0@2$0$2@1$3$4$1") := ltac2:(zQ "90!k2!hs6!hsd!ht5!ho5!hra!htd!hqd!ii3\3scr$4\2ss$7@7$6$8$2$1$3^2^1@1$0$5").
Definition kn_afterT : ltac2:(zQ "60!j4!hq6!ij6!ho5!hra!hqd>1r@2$1@2$1$5@1$0$4$3>2kn@1$0$2@1$0$2") := ltac2:(zQ "b0!j4!hra!ik0!hq6!ij6!hqd!hp0!ho5!k2!ik6!ikf\1r@2$3@2$3$5@1$0$1$7\2kn@1$0$4@3$2@1$0$4@1$0$1@3$2@2$3@1$0$4@1$0$1@1$0$6@3$9@1$a@3$2$5@1$0$1@3$2@2$3$5@1$0$1$7^2^1@1$8$6").
Definition sc_of : ltac2:(zQ "50!j4!t5!ip9!hpe!ij6>2nv$1>2sr@1$0$3>2kn@1$0$4$2") := ltac2:(zQ "a0!iq6!ip9!j4!k2!iqe!hpe!ij6!t5!ir7!irf\2nv$7\2sr@1$2$5\2kn@1$2$6M4\1x@1$4$1$1@3$9^3^2^1\1r$1^1@c$8ZZZ@1$0Z@1$0Z@1$0Z@1$0Z@1$0Z@1$0Z@1$0Z@1$3$5@1$3$6").
Definition KEPT_MC : ltac2:(zQ "20!j4!t5@1$0$1") := ltac2:(zQ "60!t5!iu4!iub!jj0!jjf!jm4@4$1@1$5@1$2#5$0$4$3").     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition KEPT_MCI : ltac2:(zQ "20!j4!t5@1$0$1") := ltac2:(zQ "60!t5!jo5!joc!jp3!jp9!jr6@3$5$0\1i$0@1$2@2$3@2$1^1Nh3@2$1^1Nh4$4").
Definition KEPT_CS : ltac2:(zQ "20!j4!t5@1$0$1") := ltac2:(zQ "60!t5!iu4!iub!js0!jjf!jm4@4$1@1$5@1$2#5$0$4$3").    (* [comment removed for export] *)
Definition spx : ltac2:(zQ "20!h9!hpe>1k$0$1") := ltac2:(zQ "50!h9!jv4!jvf!iq6!kg7\1k$0@3$2$1@1$4N0@1$3^1").
(* [comment removed for export] *)
Definition OT_FR : Z := 6000.                (* [comment removed for export] *)
Definition FMT : Z := 0x20e15.
Definition NPRE : Z := 17.
Definition NSUF : Z := 1.                (* [comment removed for export] *)
Definition IHI : Z := 0x80000000.            (* [comment removed for export] *)
Definition BUF_LO : Z := (-592).
Definition BUF_HI : Z := (-512).
Definition PX : ltac2:(zQ "10!hpe$0") := ltac2:(zQ "10!kg7@1$0Nod").            (* [comment removed for export] *)

(* [comment removed for export] *)
Definition srV0 : ltac2:(zQ "20!j4!hpe@1$0$1") := ltac2:(zQ "90!t5!hpe!kgf!kg7!iq6!kh6!khc!iu4!ki2@4$7$0$1\1i$0M0\1i$0$1^1@1$4Z\1n$0M0\1n$0$1^1@1$4+nvhi4\2n0$0M0\2n0$0$1^1@1$5-v0\2n1$0M0\2n1$0$1^1@1$3@2$2Ni3^4\2n2$0M0\2n2$0$1^1@1$4+mvhjh8\2n3$0M0\2n3$0$1^1@1$3@2$2Ni3^6\2n4$0M0\2n4$0$1^1@1$3@2$2Ni3^7\2n5$0M0\2n5$0$1^1@1$3@2$2Ni3^8\2n6$0M0\2n6$0$1^1@1$4$6\2n7$0M0\2n7$0$1^1@1$4+hrmti0\2n8$0M0\2n8$0$1^1@1$4+hrmti0\2n9$0M0\2n9$0$1^1@1$4$6\3n10$0M0\3n10$0$1^1@1$5-r0\3n11$0M0\3n11$0$1^1@1$3@2$2Ni3^e\3n12$0M0\3n12$0$1^1@1$3@2$2Ni3^f\3n13$0M0\3n13$0$1^1@1$3@2$2Ni3^h0\3n14$0M0\3n14$0$1^1@1$3@2$2Ni3^h1\3n15$0M0\3n15$0$1^1@1$3@2$2Ni3^h2\3n16$0M0\3n16$0$1^1@1$5-r0\3n17$0@1$3@2$2Ni3^h4@2$8N0Ni0").

(* [comment removed for export] *)
Definition ot_cells : ltac2:(zQ "40!hq6!h9!j4!t5@1$2@2$0@2$0$1$3$1") := ltac2:(zQ "60!h9!hq6!t5!ki9!jb!k2@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrkig0N8+hppqsc@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrkjn8N8+hqijpc@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrkjo0N8+hqinq0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrkji8N8+hqiuu0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrkhr8N8+hqiiq0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrthn8N8+nvvvogg0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrtul8N1+1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrtul9N1+1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+ikusvcN1+1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+ikutq3N1+1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmti0N4+5@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmtk0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmtk8N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmtl8N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmtm8N8+hporm0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmtn8N8+nhhrj0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmto0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmtp8N4+2@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmtq8N4Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmtqcN4+vvvvvvvf@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmtr0N4+vvvvvvvf@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nvvvshs0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nvvvshs8N8Z@1$5@2$1@2$1$0$2$0").

(* [comment removed for export] *)
Definition OT_SHOFFS : ltac2:(zQ "20!j4!h9@1$0$1") := ltac2:(zQ "30!h9!jb!k2@3$1$0-il0@3$1$0-ik0@1$2$0").
Definition OT_SHOFFS2 : ltac2:(zQ "20!j4!h9@1$0$1") := ltac2:(zQ "30!h9!jb!k2@3$1$0-il0@3$1$0-ik0@3$1$0-ijf@1$2$0").
Definition OT_SHX : ltac2:(zQ "20!j4!hpe@1$0$1") := ltac2:(zQ "90!jvf!iq6!jv4!kg7!hpe!jb!kj0!kjb!k2@3$5$4@3$0$6@3$0$2@3$0$7@3$0$2@3$0$2@1$3N2@1$3Nod@1$1-1@1$1+3@1$1+nvvvogg0@1$1-8@3$5$4@3$0$6@3$0$2@3$0$7@1$3N2@1$1+3@1$1+nvvvogg0@1$1-8@3$5$4@3$0$6@3$0$2@3$0$7@3$0$2@3$0$2@1$3N0@1$3Nod@1$1-ik0@1$1+3@1$1+nvvvogg0@1$1-8@3$5$4@3$0$6@3$0$2@3$0$7@3$0$2@3$0$2@1$3N0@1$3Nod@1$1-ijf@1$1+3@1$1+nvvvogg0@1$1-8@1$8$4").
Fixpoint shxkn (l : list expr) : list kentry :=
  match l with [] => [] | e :: r => KRange e 0x20000000000 0x10007fff8000 :: KZero (SA e 0) (ELit 8) :: shxkn r end.

Definition knV0 : ltac2:(zQ "20!j4!ij6@1$0$1") := ltac2:(zQ "h40!ij6!kg7!jb!kk6!kkc!iq6!kl5!klb!km3!kmb!kn5!k2!ksd!lh7!li2!lm9!ln1!lnd!lo8!lqa@3$6$0@3$2$0@2$h2@1$1N0+h0@3$2$0@3$9@1$1N0+nvvvogggggg0+ogggggggggg0@3$2$0@2$a@2$3@1$1N0@2$h3-o0$7$7@3$2$0@3$9@1$1N2$e$d@3$2$0@2$8+hggg0+mngg0@3$2$0@2$8+hqqgg0+hrkgg0@3$2$0@3$4@2$3@1$1N0-r0N8@1$1N2@3$2$0@3$4@2$3@1$1N0-r8N8@1$5+ruri0@3$2$0@3$4@2$3@1$1N0-s0N8@1$1Nb@3$2$0@3$4@2$3@1$1N0-s8N8@1$1Nc@3$2$0@3$4@2$3@1$1N0-t0N8@1$1Nh5@3$2$0@3$4@2$3@1$5Z+nhhjl8N8@1$1N1@3$2$0@2$a@2$3@1$5Z+hrmti0+u8@1$b$0@3$6$0@1$f$h0@1$c$h1").
(* [comment removed for export] *)
Definition not_px_range (k : kentry) : bool := match k with KRange (EVar 141) _ _ => false | _ => true end.
Definition px_range : ltac2:(zQ "30!j4!h9!ij6>2lo$1>2hi$1>2kn@1$0$2@1$0$2") := ltac2:(zQ "80!ij6!h9!jb!j4!lt4!lt9!kmb!jr6\2lo$1\2hi$1\2kn@1$3$0@3$2$0@3$6$4^3^2@3$7$0$5^1").
(* [comment removed for export] *)
Definition kn_readd : ltac2:(zQ "30!j4!h9!ij6>3plo$1>3phi$1>2kn@1$0$2@1$0$2") := ltac2:(zQ "90!ij6!kl5!h9!j4!lm9!lu8!lv5!lve!mg9\3plo$2\3phi$2\2kn@1$3$0@3$7^3^2@3$1$0@1$8$6@3$1$0@1$4$5^1").

(* [comment removed for export] *)
Definition ssB0 : ltac2:(zQ "10!hqd$0") := ltac2:(zQ "50!k2!mh1!mh8!mhf!mi5@5$3+hppqsc$2@1$0$4$1Nk3").
Definition rB := Eval vm_compute in runT (SCR [false] [] []) ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_afterT rB knV0.
(* [comment removed for export] *)
Definition logM1 : ltac2:(zQ "20!j4!mi5@1$0$1") := ltac2:(zQ "70!mi5!jb!iq6!kg7!kk6!mif!k2@3$1$0@3$5@2$4@1$3N0-ik0N1@1$2+i0@3$1$0@3$5@2$4@1$3N0-ik8N8@1$2+mumlngmvignkmvme@3$1$0@3$5@2$4@1$3N0-il0N8@1$2+mumhmjigjqmpmsm3@1$6$0").
Definition knC0 : list kentry := Eval vm_compute in fst (fst (carry logM1 knB [])).
Definition srC0 : list expr := Eval vm_compute in sr_after_call_j srB KEPT_MC 67.
(* [comment removed for export] *)
Definition ssC0 : ltac2:(zQ "10!hqd$0") := ltac2:(zQ "60!k2!mj5!mk3!mka!mhf!mi5@5$4$1$3@1$0$5$2Nm3").
Definition rC := Eval vm_compute in runT (SCR [] [] []) ssC0.
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC)).
Definition knC : list kentry := Eval vm_compute in kn_afterT rC knC0.
Definition srD0 : list expr := Eval vm_compute in sr_after_call_j srC KEPT_MC 99.
(* [comment removed for export] *)
Definition ssD0 : ltac2:(zQ "10!hqd$0") := ltac2:(zQ "60!k2!mj5!ml1!ml7!mhf!mi5@5$4$1$3@1$0$5$2No3").
Definition rD := Eval vm_compute in runT (SCR [] [] []) ssD0.
Definition srD : list expr := Eval vm_compute in s_regs (fst (fst rD)).
Definition knD : list kentry := Eval vm_compute in kn_afterT rD knC.
(* [comment removed for export] *)
Definition knE0 : list kentry := Eval vm_compute in kn_readd 0 131071 (kn_cut 0 (-1152 - 4400) (-1152) IHI knD).
Definition srE0 : list expr := Eval vm_compute in sr_after_call_j srD KEPT_CS 131.
(* [comment removed for export] *)
Definition ssE0 : ltac2:(zQ "10!hqd$0") := ltac2:(zQ "60!k2!mle!mmd!mn4!mhf!mi5@5$4$1$3@1$0$5$2Nq3").
Definition rE := Eval vm_compute in runT (SCR [false] [ELit 0] []) ssE0.
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
Definition knE : list kentry := Eval vm_compute in kn_afterT rE knE0.
Definition srF0 : list expr := Eval vm_compute in sr_after_call_j srE KEPT_MC 163.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FQMAX : Z := 63.
Definition knF0_ : list kentry := Eval vm_compute in px_range 1 FQMAX knE.
Definition ssF0 : ltac2:(zQ "10!hqd$0") := ltac2:(zQ "60!k2!mj5!mnb!mo3!mhf!mi5@5$4$1$3@1$0$5$2Ns3").
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
Definition ssG0 : ltac2:(zQ "10!hqd$0") := ltac2:(zQ "60!k2!mj5!moa!mp1!mhf!mi5@5$4$1$3@1$0$5$2Nu3").
Definition rG := Eval vm_compute in runT (SCR [false] [] []) ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_afterT rG knG0.
Definition knH0 : list kentry := Eval vm_compute in kn_readd 0 62 (kn_cut 0 (BUF_LO + NPRE) BUF_HI IHI knG).
Definition srH0 : list expr := Eval vm_compute in sr_after_call_j srG KEPT_MC 227.
(* [comment removed for export] *)
Definition ssH0 : ltac2:(zQ "10!hqd$0") := ltac2:(zQ "60!k2!mj5!mp8!mpf!mhf!mi5@5$4$1$3@1$0$5$2Nhg3").
Definition rH := Eval vm_compute in runT (SCR [] [] []) ssH0.
Definition srH : list expr := Eval vm_compute in s_regs (fst (fst rH)).
Definition knH : list kentry := Eval vm_compute in kn_afterT rH knH0.
Definition scOF : stdio_res := Eval vm_compute in sc_of 259 srH knH.
Definition srI0 : list expr := Eval vm_compute in sc_sr scOF.
Definition knI0 : list kentry := Eval vm_compute in sc_kn scOF.
(* [comment removed for export] *)
Definition ssI0 : ltac2:(zQ "10!hqd$0") := ltac2:(zQ "50!k2!mq6!mqd!mhf!mi5@5$3+hpprv4$2@1$0$4$1Nhi3").
Definition rI := Eval vm_compute in runT (SCR [] [] []) ssI0.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition knG30 : list kentry := Eval vm_compute in kn_readd (62 + 1) (62 + NSUF) (kn_cut 0 (BUF_LO + NPRE) BUF_HI IHI knF).
Definition ssG30 : ltac2:(zQ "10!hqd$0") := ltac2:(zQ "60!k2!mj5!mr4!mp1!mhf!mi5@5$4$1$3@1$0$5$2Nu3").
Definition rG3 := Eval vm_compute in runT (SCR [] [] []) ssG30.
Definition srG3 : list expr := Eval vm_compute in s_regs (fst (fst rG3)).
Definition knG3 : list kentry := Eval vm_compute in kn_afterT rG3 knG30.
Definition scG3 : stdio_res := Eval vm_compute in sc_of 227 srG3 knG3.
Definition srH30 : list expr := Eval vm_compute in sc_sr scG3.
Definition knH30 : list kentry := Eval vm_compute in sc_kn scG3.
(* [comment removed for export] *)
Definition ssH30 : ltac2:(zQ "10!hqd$0") := ltac2:(zQ "70!k2!mrc!ms6!mse!mt5!mhf!mi5@5$5@1$1$3$4@1$0$6$2Nhg3").
Definition rH3 := Eval vm_compute in runT (SCR [] [] []) ssH30.
Definition srH3 : list expr := Eval vm_compute in s_regs (fst (fst rH3)).
Definition knH3 : list kentry := Eval vm_compute in kn_afterT rH3 knH30.
Definition scH3 : stdio_res := Eval vm_compute in sc_of 259 srH3 knH3.
Definition srI30 : list expr := Eval vm_compute in sc_sr scH3.
Definition knI30 : list kentry := Eval vm_compute in sc_kn scH3.
(* [comment removed for export] *)
Definition ssI30 : ltac2:(zQ "10!hqd$0") := ltac2:(zQ "50!k2!mtd!mu5!mhf!mi5@5$3+hpprv4$2@1$0$4$1Nhi3").
Definition rI3 := Eval vm_compute in runT (SCR [] [] []) ssI30.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition knF40 : list kentry := Eval vm_compute in px_range (62 + NSUF + 1) 131071 knE.
Definition ssF40 : ltac2:(zQ "10!hqd$0") := ltac2:(zQ "60!k2!mj5!mud!mo3!mhf!mi5@5$4$1$3@1$0$5$2Ns3").
Definition rF4 := Eval vm_compute in runT (SCR [true] [] []) ssF40.
Definition srF4 : list expr := Eval vm_compute in s_regs (fst (fst rF4)).
Definition knF4 : list kentry := Eval vm_compute in kn_afterT rF4 knF40.
Definition scF4 : stdio_res := Eval vm_compute in sc_of 195 srF4 knF4.
Definition srG40 : list expr := Eval vm_compute in sc_sr scF4.
Definition knG40 : list kentry := Eval vm_compute in kn_readd (62 + NSUF + 1) 131071 (sc_kn scF4).
(* [comment removed for export] *)
Definition ssG40 : ltac2:(zQ "10!hqd$0") := ltac2:(zQ "70!k2!mrc!mv5!mvd!ng4!mhf!mi5@5$5@1$1$3$4@1$0$6$2Nu3").
Definition rG4 := Eval vm_compute in runT (SCR [false] [] []) ssG40.
Definition srG4 : list expr := Eval vm_compute in s_regs (fst (fst rG4)).
Definition knG4 : list kentry := Eval vm_compute in kn_afterT rG4 knG40.
(* [comment removed for export] *)
Definition logNL : ltac2:(zQ "20!j4!mi5@1$0$1") := ltac2:(zQ "70!mi5!jb!k2!iq6!kg7!kk6!mif@3$1$0@3$6@2$5@1$4N0-il0N1@1$3+a@1$2$0").
Definition knH40 : list kentry := Eval vm_compute in fst (fst (carry logNL knG4 [])).
Definition srH40 : list expr := Eval vm_compute in sr_after_call_j srG4 KEPT_MC 227.
(* [comment removed for export] *)
Definition ssH40 : ltac2:(zQ "10!hqd$0") := ltac2:(zQ "60!k2!mj5!ngc!nh4!mhf!mi5@5$4$1$3@1$0$5$2Nhg3").
Definition rH4 := Eval vm_compute in runT (SCR [] [] []) ssH40.
Definition srH4 : list expr := Eval vm_compute in s_regs (fst (fst rH4)).
Definition knH4 : list kentry := Eval vm_compute in kn_afterT rH4 knH40.
Definition scH4 : stdio_res := Eval vm_compute in sc_of 259 srH4 knH4.
Definition srI40 : list expr := Eval vm_compute in sc_sr scH4.
Definition knI40 : list kentry := Eval vm_compute in sc_kn scH4.
(* [comment removed for export] *)
Definition ssI40 : ltac2:(zQ "10!hqd$0") := ltac2:(zQ "50!k2!nhc!ni4!mhf!mi5@5$3+hpprv4$2@1$0$4$1Nhi3").
Definition rI4 := Eval vm_compute in runT (SCR [] [] []) ssI40.

(* [comment removed for export] *)
Definition ot_regions : ltac2:(zQ "20!j4!nm5@1$0$1") := ltac2:(zQ "b0!h9!lr1!hq6!jb!ki9!klb!kk6!k2!iq6!kg7!lqa@3$3@2$2$1$0@4$4$1$0@2$6@1$9N0@2$a-o0$5$5@3$3@2$2$1$0@4$4$1$0@2$6@1$8Z+hrmti0+u8@1$7@2$2$1$0").
Definition scsB : list sidecond := Eval vm_compute in (snd (fst rB)).
Lemma factsB : ltac2:(zQ "h42!j4!hra!ik0!hqd!hq6!hp0!no4!noa!ho5!k2!nof!np5!ij6!ikf!hs6!mh1!npc!nq9!nr0!ik6&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_open_defs ()) ["FPX1"] "p;1p;3p;4p;2g0000j13Tg000Pj1DTg001Wj10Tg002<j15Tg002aj1=Tg003?j16Tg004Fj3:Tg005Mj1@Tg005kj4?Tg0076j19Tg007Vj3>Tg0086j31Tg008Pj24Tg008kj27Tg009Ej4<Tg009`j28Tg00:@j32Tg00:]j3;Tg00;:j1CTg00<@j3BTg00=Fj2ATg00>LR0#3R1g00?Wg00@7g00@ig00AUg00BA#Dg00B`R2#0#0R3#5#0#5#0#0#0#0#=#63:%=2#63:%03#5#@#6C?%90R35>0R0;10A1133R2g00CER4g00CeR5;15R6'41710P2P617131745C<C<g00DER61861g00EQg00F[32R27;1g00Ge511g00I1#3R01801%34A2612#CR2g00J:%943B327;1=113g00KF/A2=145'4'4do"). Qed.
Definition scsC : list sidecond := Eval vm_compute in (snd (fst rC)).
Lemma factsC : ltac2:(zQ "h42!j4!hra!ik0!hqd!hq6!hp0!no4!nrf!ho5!k2!nof!np5!ij6!ikf!hs6!mk3!npc!ns4!nr0!ik6&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_open_defs ()) ["FPX1"] "p;1p;3p;2p;4g0000j13Tg0076j18Tg0086j30Tg008Pj21Tg008kj27Tg009Ej46Tg009`j25Tg00:@j32Tg00:]j34Tg00;:j1;Tg00<@j3:Tg00=Fj29Tg00>LR0#3R1%80R0;00R2g00CER3g00CeR4;04R5,121710R6P2P5P61734C6C6g00DER61561g00EQg00LX32R5741g00Mb501g00I1#3R21521%33A2615#;R5g00Nn%833:32741=010g00KF/95=034'1'1do"). Qed.
Definition scsD : list sidecond := Eval vm_compute in (snd (fst rD)).
Lemma factsD : ltac2:(zQ "h42!j4!hra!ik0!hqd!hq6!hp0!no4!nsb!ho5!k2!nof!np5!ij6!ikf!hs6!ml1!npc!nt0!nr0!ik6&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_open_defs ()) ["FPX1"] "p;1p;3p;2p;4g0000j13Tg0076j18Tg0086j30Tg008Pj21Tg008kj27Tg009Ej46Tg009`j25Tg00:@j32Tg00:]j34Tg00;:j1;Tg00<@j3:Tg00=Fj29Tg00>LR0#3R1%80R0;00R2g00CER3g00CeR4;04R5,121710R6P2P5P61734C6C6g00DER61561g00EQg00P:32R5741g00QD501g00I1#3R21521%33A2615#;R5g00RP%833:32741=010g00KF/95=034'1'1do"). Qed.
Definition scsE : list sidecond := Eval vm_compute in (snd (fst rE)).
Lemma factsE : ltac2:(zQ "h42!j4!hra!ik0!hqd!hq6!hp0!no4!nt7!ho5!k2!nof!np5!ij6!ikf!hs6!mmd!npc!ntc!nr0!ik6&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1z (kr_t_AsTail_open_defs ()) ["FPX1"] "##,,p;1p;3p;4p;2g0000j14Tg00S[j10Tg000Pj1;Tg003?j1GTg00T:j3BTg005kj4ATg004Fj3@Tg00UAj2>Tg00VIj4=Tg0076j17!s/$Vj3<Tg0086j32!s/$Pj26!s/$kj25Tg009Ej48!s/$`j29Tg00:@j33!s/$]j3:Tg00;:j1FTg00<@j3DTg00=Fj2ETf0R0#0#0p=C%0!s0$!s$,p=?!s:4!s$3p=1g00>LR0#4R1g00?WR2g00WTg00AUR3g00BA#0R4#0R5#0#C#?#1!s$2;R6g00XFR7#GR83BP6CA%;5=@36/>7P4P2P8C=%70R85<05<0R0;20A2188!t;$CER4g00CeR7;27R6'61510P2P615181547C8C8g00DER61961g00EQg00Xd33R27:1g00Yn521g00I1#4R01901%44A3612#F!t4$[:%743D337:1=218g00KF/E2=247'6'6do"). Qed.
Definition scsF : list sidecond := Eval vm_compute in (snd (fst rF)).
Lemma factsF : ltac2:(zQ "h42!j4!hra!ik0!hqd!hq6!hp0!no4!nu3!ho5!k2!nof!np5!ij6!ikf!hs6!mnb!npc!nu8!nr0!ik6&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1z (kr_t_AsTail_open_defs ()) ["FPX1"] "##-^p;1p;3p;4p;2g0000j17Tg000Pj1=Tg001Wj18Tg002<j13!s/$aj1DTg003?j1:Tg004Fj36Tg00S[j10Tg005kj45Tg00\Fj4ETg00T:j3CTg0076j1B!s/$Vj34Tg0086j32!s/$Pj2;!s/$kj29Tg009Ej4@!s/$`j2ATg00:@j3<!s/$]j3?Tg00;:j1ITg00<@j3HTg00=Fj2GTf0R0#0#0p=>%0!s0$!s$,p=F!s:4!s$3p=1g00>LR0#7R1g00?WR2g00@7R3g00@iR4g00AUR5g00BAR6#=R7g00B`R8#!s$%3!s$-D#:R936R:%D8#:R836%>6R;#>R<#0#F#1!s$2=R=C5P2P3%=;R;=648P=C5g00CeR8g00]MP;A657==659C5P2g00^?P:P;C5P8g00_1P8P6P<P=CEg00XF#:R<9C5==C5<C5%B0R<540!s%/R0;20A21<<!uK$CER=?288R6';1910P5P6191<19=8C@C@g00DER61A61g00EQg00_c3<R57?1g00`m521g00I1#7R01A01%7=A<615#I!t-$b9%B=3H3<7?1=21<g00KF/G5=2=8';';do"). Qed.
Definition scsF0 : list sidecond := Eval vm_compute in (snd (fst rF0)).
Lemma factsF0 : ltac2:(zQ "h42!j4!hra!ik0!hqd!hq6!hp0!no4!nuf!ho5!k2!nof!np5!ij6!ikf!hs6!nv5!npc!nvd!nr0!ik6&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1z (kr_t_AsTail_open_defs ()) ["FPX1"] "##,Ap;1p;3p;4p;2g0000j15Tg000Pj1:Tg00S[j10Tg004Fj37Tg001Wj16Tg002<j12!s/$aj1CTg003?j1BTg005kj4<Tg0076j1;!s/$Vj3@Tg0086j33!s/$Pj28!s/$kj29Tg009Ej4>!s/$`j2?Tg00:@j34!s/$]j3=Tg00;:j1FTg00<@j3ETg00=Fj2DTf0R0#0#0p=A%0!s0$!s$,p=G!s:4!s$3p=1g00>LR0#5R1g00CeR2g00]Mg00BAR3#AR4#:R5g00AUR6%:3R3%04#A#G#1!s$2:576g00B`#6!s$$2!s$-C#BR437C<g00?Wg00^?A7634P5C<%;0R55@05@0R0;30A3155R4g00CER3?322R6'81910P4P619151932C>C>g00DER61?61g00EQg00cF34R47!uN$dQ531g00I1#5R01?01%53A4614#F!t-$e^%;33E347=1=315g00KF/D4=332'8'8do"). Qed.
Definition scsG : list sidecond := Eval vm_compute in (snd (fst rG)).
Lemma factsG : ltac2:(zQ "h42!j4!hra!ik0!hqd!hq6!hp0!no4!og5!ho5!k2!nof!np5!ij6!ikf!hs6!moa!npc!oga!nr0!ik6&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1z (kr_t_AsTail_open_defs ()) ["FPX1"] "##,Bp;1p;3p;4p;2g0000j1:Tg000Pj1?Tg00S[j10Tg004Fj35Tg001Wj16Tg002<j12!s/$aj1<Tg003?j14Tg005Mj1B!s/$kj4ATg0076j1@!s/$Vj3GTg0086j33!s/$Pj27!s/$kj29Tg009Ej4>!s/$`j2=Tg00:@j38!s/$]j3;Tg00;:j1ETg00<@j3DTg00=Fj2FTf0R0#!s$&p=C%0!s4+!s:'H!s:4!s$3p=1g00>LR0#:R1g00?Wg00@7g00@ig00AUR2g00BAR3#?%03#C#H#1!s$2?55!sK$`R2#6!s$$2!s$-<#435%<2!s,$B2#4CA%@0R25G0R0;30A3122R3g00CER4g00CeR5;35R6'71910P3P619121945C>C>g00DER61=61g00EQg00fk38R37;1g00h5531g00I1#:R01=01%:4A8613#E!t4$iA%@43D387;1=312g00KF/F3=345'7'7do"). Qed.
Definition scsH : list sidecond := Eval vm_compute in (snd (fst rH)).
Lemma factsH : ltac2:(zQ "h42!j4!hra!ik0!hqd!hq6!hp0!no4!oh1!ho5!k2!nof!np5!ij6!ikf!hs6!mp8!npc!oh6!nr0!ik6&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_open_defs ()) ["FPX1"] "p;1p;3p;2p;4g0000j13Tg0076j18Tg0086j30Tg008Pj21Tg008kj27Tg009Ej46Tg009`j25Tg00:@j32Tg00:]j34Tg00;:j1;Tg00<@j3:Tg00=Fj29Tg00>LR0#3R1%80R0;00R2g00CER3g00CeR4;04R5,121710R6P2P5P61734C6C6g00DER61561g00EQg00jM32R5741g00kW501g00I1#3R21521%33A2615#;R5g00lc%833:32741=010g00KF/95=034'1'1do"). Qed.
Definition scsG3 : list sidecond := Eval vm_compute in (snd (fst rG3)).
Lemma factsG3 : ltac2:(zQ "h42!j4!hra!ik0!hqd!hq6!hp0!no4!ohd!ho5!k2!nof!np5!ij6!ikf!hs6!mr4!npc!oi3!nr0!ik6&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_open_defs ()) ["FPX1"] "p;1p;3p;2p;4g0000j13Tg0076j18Tg0086j30Tg008Pj21Tg008kj27Tg009Ej46Tg009`j25Tg00:@j32Tg00:]j34Tg00;:j1;Tg00<@j3:Tg00=Fj29Tg00>LR0#3R1%80R0;00R2g00CER3g00CeR4;04R5,121710R6P2P5P61734C6C6g00DER61561g00EQg00mo32R5741g00o:501g00I1#3R21521%33A2615#;R5g010G%833:32741=010g00KF/95=034'1'1do"). Qed.
Definition scsH3 : list sidecond := Eval vm_compute in (snd (fst rH3)).
Lemma factsH3 : ltac2:(zQ "h42!j4!hra!ik0!hqd!hq6!hp0!no4!oib!ho5!k2!nof!np5!ij6!ikf!hs6!ms6!npc!oj1!nr0!ik6&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_open_defs ()) ["FPX1"] "p;1p;3p;2p;4g0000j13Tg0076j18Tg0086j30Tg008Pj21Tg008kj27Tg009Ej46Tg009`j25Tg00:@j32Tg00:]j34Tg00;:j1;Tg00<@j3:Tg00=Fj29Tg00>LR0#3R1%80R0;00R2g00CER3g00CeR4;04R5,121710R6P2P5P61734C6C6g00DER61561g00EQg011T32R5741g012_501g00I1#3R21521%33A2615#;R5g013l%833:32741=010g00KF/95=034'1'1do"). Qed.
Definition scsF4 : list sidecond := Eval vm_compute in (snd (fst rF4)).
Lemma factsF4 : ltac2:(zQ "h42!j4!hra!ik0!hqd!hq6!hp0!no4!oj9!ho5!k2!nof!np5!ij6!ikf!hs6!mud!npc!ojf!nr0!ik6&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1z (kr_t_AsTail_open_defs ()) ["FPX1"] "##+_p;1p;4p;3p;2g0000j13Tg00S[j10Tg000Pj1DTg00\Fj4CTg003?j1?Tg00T:j38Tg005kj4>Tg0076j17!s/$Vj3<Tg0086j32!s/$Pj26!s/$kj24Tg009Ej4;!s/$`j2:Tg00:@j35!s/$]j39Tg00;:j1BTg00<@j3@Tg00=Fj2ATf0R0#!s$&p=E%0!s4+!s:'=!s:4!s$3p=1g00>LR0#3R1g00CeR2g00_1P2g00BAR3%E3R3%03#=#1!s$2DR3CCg00AUR4g00XF#?R59843;85C>%70R55<0R0;20A2155!sL$CER3?222R6'61410P4P614151432C;C;g00DER61:61g00EQg015935R4791g016D521g00I1#3R01:01%33A5614#BR4g017Q%733@35791=215g00KF/A4=232'6'6do"). Qed.
Definition scsG4 : list sidecond := Eval vm_compute in (snd (fst rG4)).
Lemma factsG4 : ltac2:(zQ "h42!j4!hra!ik0!hqd!hq6!hp0!no4!ok7!ho5!k2!nof!np5!ij6!ikf!hs6!mv5!npc!okd!nr0!ik6&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_open_defs ()) ["FPX1"] "p;1p;3p;4p;2g0000j13Tg000Pj1DTg001Wj10Tg002<j17Tg002aj1=Tg003?j15Tg004Fj3:Tg005Mj1@Tg005kj4?Tg0076j19Tg007Vj3>Tg0086j31Tg008Pj24Tg008kj26Tg009Ej4<Tg009`j28Tg00:@j32Tg00:]j3;Tg00;:j1CTg00<@j3BTg00=Fj2ATg00>LR0#3R1g00?Wg00@7g00@ig00AUg00BA#Dg00B`R2#0#0#7#0#7#0#0#0#0#=#53:%=2#53:%@2#5C?%90R25>0R0;10A1122R3g00CER4g00CeR5;15R6'41610P3P616121645C<C<g00DER61861g00EQg018^32R37;1g019i511g00I1#3R01801%34A2613#CR3g01;6%943B327;1=112g00KF/A3=145'4'4do"). Qed.
Definition scsH4 : list sidecond := Eval vm_compute in (snd (fst rH4)).
Lemma factsH4 : ltac2:(zQ "h42!j4!hra!ik0!hqd!hq6!hp0!no4!ol5!ho5!k2!nof!np5!ij6!ikf!hs6!ngc!npc!olb!nr0!ik6&@3$2$3@1$0$1@3$2@2$4$3@1$0$1$8$7&@1$d~0@2$b@3$6@1$0$1@3$a$3@1$0$1@3$2@2$4$3@1$0$1$8$7$h1@2$b@3$6@1$0$1@3$a@1$0$c@1$0$1@3$2@2$4@1$0$c@1$0$1@1$0$5@3$h3~1$f@1$9$5@1$9$1@3$6$5@2$h2$h0~1$e").
Proof.
ltac2:(KReplay.run1 (kr_t_AsTail_open_defs ()) ["FPX1"] "p;1p;3p;2p;4g0000j13Tg0076j18Tg0086j30Tg008Pj21Tg008kj27Tg009Ej46Tg009`j25Tg00:@j32Tg00:]j34Tg00;:j1;Tg00<@j3:Tg00=Fj29Tg00>LR0#3R1%80R0;00R2g00CER3g00CeR4;04R5,121710R6P2P5P61734C6C6g00DER61561g00EQg01<C32R5741g01=N501g00I1#3R21521%33A2615#;R5g01>[%833:32741=010g00KF/95=034'1'1do"). Qed.

(* [comment removed for export] *)
Lemma ot_itinerary : ltac2:(zQ "j20!h9!hq6!ik0!j4!hra!hqd!ki9!om3!ho5!ip9!no4!np5!q7!omb!iqe!irf!r8!p4!s7!on2!on9!oo0!oo6!ood!noa!nrf!nsb!nt7!nu3!nuf!oj9!og5!ohd!ok7!oh1!oib!ol5!op4!op9!opf!mvd!mse!oq5!oqc!or3!ora!os1!os8!ose!ot5@2$b@3$a@2$1@2$1@2$1$0$0$0$0@4$6@2$1@2$1$0$0$0$0@4$6@2$1$0$0$0@4$6$0$0@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$h8@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$h9@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$ha@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$hb@4$6@2$1@2$1$0$0$0$0@4$6@2$1$0$0$0@4$6$0$0$c$c$h2$c@2$b@3$a@2$1@2$1@2$1@2$1$0$0$0$0$0@4$6@2$1@2$1@2$1$0$0$0$0$0@4$6@2$1@2$1$0$0$0$0@4$6@2$1$0$0$0@4$6$0$0@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$hc@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$hd@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$hf@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$i2@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$i5@4$6@2$1@2$1@2$1$0$0$0$0$0@4$6@2$1@2$1$0$0$0$0@4$6@2$1$0$0$0@4$6$0$0$c$c$c$h0$h1@2$b@3$a@2$1@2$1$0$0$0@4$6@2$1$0$0$0@4$6$0$0@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$i0@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$i3@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$i6@4$6@2$1$0$0$0@4$6$0$0$h0$h0$h1@2$b@3$a@2$1@2$1@2$1$0$0$0$0@4$6@2$1@2$1$0$0$0$0@4$6@2$1$0$0$0@4$6$0$0@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$he@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$i1@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$i4@1$7@3$2$5@1$3$4@3$2@2$1$5@1$3$4$8$i7@4$6@2$1@2$1$0$0$0$0@4$6@2$1$0$0$0@4$6$0$0$h0$c$h0$h1@2$b@3$a@1$e$9@3$fNhg3$if$h5@2$d$9$ic@2$b@3$a@1$e$9@3$fNu3$ie$h4@2$d$9$i9@2$b@3$a@1$e$9@3$fNhg3$j0$h6@2$d$9$ia@2$b@3$a@1$e$9@3$fNs3$id$h3@2$d$9$i8@3$a@1$e$9@3$fNhg3$j1$h7@2$d$9$ib").
Proof.
ltac2:(KReplay.run1z (kr_t_AsTail_open_defs ()) ["FPX1"] "##mQp%0p%1p&0p;2p;1p;3p;<p;4g009`j2qTg002<j11Tg001Wj10Tg0086j3JTg01?hk10CTg005Mj1?Tg000Pj16!s]$aj1>Tg00S[j12Tg003?j1@Tg00T:j3fTg0076k103Tg01@Jj3ITg01ASj2`Tg01B\j3=Tg00UAj2BTg01Cek20ATg01Dnk20:Tg01F7k209Tg01G@l<nTg01HNj2O!tu$Pj2Y!s/$kk207!tl$0k10>Tg01I0j4G!s/$Pj3pTg004Fj3r!td$Vj34Tg009Ek40!tR$:@j3uTg01J]k104Tf0R0#0#0p=7%1!s-$9%00#1p=F%10#1!sB%:!s2%1#0p=g%00#?p=tg01KbR1P1f1R2P0CGp=_!sb$!sZ%[%00#!s4$p=^!s2%!s^$8f4R3P1f3R4P1f2R5P2CG!se%kP5P1P!sr%>0<!ss%!sg$P!sg&p=D!te'1p=x!te&p=}g00AUR6%@07r2p=R%20#2p>08!s/$#2#2p=S!s2&p=l!s<+!s$'p=m!s:4!s$3p=VAr620p=H%00#>p=z%?0#@p=!ty$0#?#@p=N!ub'1p=e!vr$!tq%]g01L@R7%62;40p>02%65%62=470547p=C!s3&94759474p=jA472!s6+9473p=W%64!s=+547p>011B45?=20p=y!v0$p=dg01MG?r20p=c!x''!s$+p=\!ts'0p=A!s2+!s$'p=Ug01N3!sf%b!sf+p=Qg00XFR8,B0p=a!wg'1p=o!u`%!sc$M%05#>,B4!tb%;!t-%>,B2p=w%>0,B2p>00%15!t?&!sR,K!yW'1p=~1B45!w#$7=2p=v!yf'1p=h%10#?p>0B%@09=52p>0;!tP&p>0@g00I1R9%14!t0&?,B3?=5!w@$=T%?4!s6&=490p=LA4920949594!s$$3p=3A=4!sF&>0?%>!sX15f6f5;!sK-549p=|!sn+p=i!s2$p=sP3P420752P0H0=p=Zg00DER3Au5207u4$04p=E!s4$9u34p>06!{m%&04!{o%5P2P1P0g01N_CGp={AJ452/Y0p=X1q11R0/q1R5/q1R4P5P0g00B`R2#1R:#0R;#1R<#0S00#7S01#9S02#0S03#FS04#:#g#tR=/_=R>%1:R?#1R@#[#^#[#8P=DkRA;JA1q41S05P4P5B0<0>=%0;S06#1R;#1S07#0S08#0R>#F#P#:#8RB%D;S09#9#[#g#9#tR;DkRC;JCS0:1_BB>0<0;RD=J5DS0;P5P01_B=PBP;DkR;=J4;S0<g01OlRE$0CRF%1<R<#FS0=#9#xS0>#0RG#FS0?#0S0@#0#8RH%02RI#?RJ%1>R>#1RK#0S0A#1S0B#}S0C#1#9!t]$Lg00BARM#6RN%0IRO#1RP#0RQ#1RR#0S0D#7RS#0S0E#>S0F'RRT%2MRM#2RU$08RV#SRW#lS0G#2S0H#2#mS0I#2#VRX#VS0J#2S0K#2S0L#2RY#2RZ#2R[#2R\#2R]#2R^#l#S#m#V!s$%R_#6R`,HNRa%0O!t_$b#1Rc#1Rd#1Re#1Rf#z'RPT%1IRI#0Rg#0S0M#0Rh#0Ri#<Rj%@8RkPk%1P!uC$l#0S0N#7S0O#zS0P,RNRm&08_#S!tB+2#SS0Q#2S0R#2S0S#SS0T#2S0U#2S0V#2S0W#2S0X#2S0Y#2S0Z#l#mS0[#2S0\#2S0]#2S0^#2Rn!st%_#2S0`#2S0a#SS0b#2S0c#2S0d#2S0e#2S0f#2S0g#2S0h!st%i#2S0j#2S0k#2S0l#2Ro%@LPm%6XS0m!xl%9S0n#0#[#:#P#NS0o%2o#SRX%2X!s''@HRp%<2RqAf6`kRr9f6kS0p%<bS0q5f6Rs5f6Pk%SXRX#6!s_-!s'70?S0r#0#F#eR?#0#P#]#8S0s#@S0tPq%9?#:#:#NS0uPk%6YS0v%6ZS0w%6[S0x%6\S0y%6]S0z%6^S0{%lX#m!t62&037R7+023CCjDWDW3C3C3CDW3CCjH01S0|Pk%1GS0}!{Y$0RX#0#8PW%0OR^#0R]#0S0~#7S10#0R\#>,RNS11CyR[Pk%1X#8PWPTCyRXPk%dG!s5+G%1@R@#0S12#?9I`8%6URU/H`%>2'R%<:R:'c%1@S13#1S14#1#\R@#D#A#US15#<R2'H%>O#@R8'bRZ%A\R\#DS16#0#U#U#US17#?RY%d\R\#1#Q#\R?#1#A#U#8Rt3IRu%aZ%<ORO'`RZ1cU:/H2/b8Rv?IYtRw%av/`ORv%0QRQ#0S18#7S19#0Rx#>S1:#@Ry,Ha/c!s^'z!s^${%az/`ORz%1f#>#@Rf,HaS1;!sN,a!sN$Y%aa/`ORa1cT!s@'|%0\#Q#x#Q#o#Q#]R\#0#8%o?!s3$?#0#8R}3IR~%a|/`OR|1HNy!t#,y%1\#8R\;I}R}%ay/`ORy1HNfS1<!sL,8%1?#87I\R\%a8/`OROPN%MhS1=PWPkC;Rh%9i,wNS1>%1]R8#1S1?#MS1@#1#[!tU$<R:7=WS1A%7iS1B#0S1C#0-00NS1D?=WqS1E!~f%1Ri#9!ss$F%1?#<S1G!s`$HPN%DiS1IPWPpC;S1JPN%0PRP!tR$KS1KPN%7PS1L#0S1MPWP:C;S1NPN%1lRlPWPqCKS1OPN%DlS1P!sm'QPNQ0NPW%P>#F#]#NCKS0!s\$RR>PWQ1GCKS1RPN%D>S1S!s]'TPNQ0DPWPsCKS0DPNQ0EPWg01Q:!zg%d!yW$>#<Rl;fsS0EC;S1UPN%1QRQ#1S1V#7PWPlC;S1WPN%DQRQPW%<RS1XC;S1YPNQ18PW%9K#g#^#tS18#@S1ZCKS1[PuPwP{PYP~PN%7e!wN&ePN%0cRc#7S1\#0PWQ0pC;RKPN%DdPWP`C;RdPN%zxS1]PW%1^Rx#1RR#1RP#1#9#F#~CvRiPNPc!vu%Rc!t8-}P\PN%D8PWPUC;S1^PNQ0PPW%1gR8#0S0P#7R?!~0$CyRfPNQ1:PMP]CvR]PN%>QPW%7<#:R<#1#F#o#A#P#Q#^#A#o#[!s2$P#gCvRQQ0F,BNS0F%^<#:#P#F#A#e#x#h#[#]#P#h#e$0B80;WS1:PN%0bRb#1R<PW%1>S1_#dR>#7#:!s$-x#<CKS1`PN%D!sN%!wh&0#\#\#<C;S1aPNQ1?#7PWQ0A#0#d#h!s$$NC;S0APN%DRPW%9S#^#F!sX%?PN%0xRx#7S1b!w9%tC;S1cPNPx!zY'd!zY$PWPmC;S1e!t~&PWQ11CKS11PN%7bS1f#0PW%18S1g#DS1h#>R8,RNC;S1iPkQ0?#1#APWPkPkQ0@!s/'>#9!ur$P#FRx#DPV%1>!uH%Pk!v6%0!s\$jPkQ0}#1R>#1PWPT1BkHRRPV%<IS0}Q1B-00N!s{$NQ0M#1S0M#DS1B!s9%%0?S0>PWPk1BN8PWPkQ1L!sX-1SPW!#>$&8#0S1S#7S1L#>R?,RNS0@PNQ0OPW%6MR<PNPSPWQ0L#6PNQ19PWQ0K!s2%\PWQ0J!s2%fPWQ!s_$1bPWPpPNQ10PWQ1@#F#~#<S1!sB$2!wu$14#e!w\$N%?^-0ANQ15#0!#7c$Q17#D#8R^5IN!tr%dRS#:,wN%0IRI#g#8+0:AIUt^Q16#?Q07#9#U#8+09Q00#1#[!sm$0=#AR^#0Rt#7#A!sE$1BN?PWPU1wNIPW%0S#9#:#M#NPNQ06#APWQ0G!uD$0!u\$H!s2%1!y@%I#6Q0s,BkPWP<Q0r#1#8-0:R!|z$k%1^R^!t8%PWQ0B#0#:#:Cv!s@'0RR#}PW%@=Pk%M^!t;%3#1#g!tO$k%0R#!tC$2#d#]!s:&1t#]PWQ04#0#9!s:%Q0n#1Rt#e#oPWP2Pk%}t#^#:Rt#0PMPq!s\$!s/%Q1V!sQ$PR2#0#Q#:!sF'2#9#9#h!s5&0>PW%@BPk%1bPV%@JPk&0@xPVQ1_#<RxPk%1P#APVPxPk%7@#e#:Rx!{B'!|F%&039DTDL!s$$T!s0+!s2%T!s-$3H0?D5D5D5F|3iD3!s2%!s$/F|!s+&!se%TDLR9'sD3D3Rx!s-%!s2$V9i}\!s4'!s$/M<n,OERP;JPRbPHPJQ18PTQ1;PTPjP:PqQ1],RNRBPnQ1ZPBQ0mQ0oQ0_Q0`Q0aQ1XPlPqQ0b#6Q0cQ0dQ0eQ0fQ0gQ0hQ0EPsPpQ1GPqP:PkAf6rkR6PqPrQ0iQ0jQ0kQ0l0027!#BK9P[PXPGQ13#?Rs=I`sRsPuPZPwPvP{PzPYPaP~P|P}PyP\POPhQ1>?=WUR>Q1D?=WkR2Q1F?=W:RRPePKPdPiP!#8@,Q1^PfP]PQQ1:Q1`Q1aQ0AQ1?PN%M8PWP<C;Q1cQ1dQ1eQ11Q1i!~h&Q0{CKPNQ1L!}S$0zPNQ1g#MPWQ0yPNQ1h!{g%xPNQ0P!s>%wPNQ0>!s>%v!#42$!s>$}PNQ1B!s>%uPNQ1=PWPqPNQ1CPWQ0tPNQ1I!~u$PNQ1M!#30&PPWQ0C#~#NP9!y/5!s$&!xo'9!xo7!xk&W=JFWRqPHPJPLPT!s$$j!zf$mQ0|!wI%P!w>BP>Ai2RV!t&4V=JFVRs!yp$08#1#F#U#8R<PTQ1<!t6$UP`PBP_%@<!yt,QQ0RQ0S!yt%`Q0T#6Q0UQ0VQ0WQ0XQ0YQ0ZPkQ0qPpP:PkPUPkP6Q0pPrQ0[Q0\Q0]Q0^!yoE0~#?%?@5I`R`PhP>P2P!y>1!ui61sO99iy\!vh69=JF9RR!vh'%1t#>,RN!vn6Q0F%?g80;MPhQ1AQ1EQ1HQ1JQ1KQ1NQ1OQ1QQ0NQ1RQ1TQ0DQ1UQ1WQ1YQ1[P`!wR@!u5B!sL%Q1^1sQx9if]!~u7!uN2]=JF]Rf'YRx'YRQ'YRO'YR\'YRy'YR}'YP4PAQ0:P}Q05PCQ0;PyP5PDQ0<P\P4P;PbPOPFPPPqPQPFPWPsPxPFPVPRPfPFP9207F]DZ!s$1P!#Y6&>L$0>R]1q3]R3g00EQR9g00F[CEP]P3P9g00LXCE'_!s5+P:!sB-XdCED!#cU$0P1P1P1g01QfRfPfCGRRg01S5CGPfCGQ!#YL$!s`+_c!sm-cF!t10fkH066050!s8+jM!sT,1TH!tC0RPfCGg01URRRCG,{!t4/mo!s^-1T!t4/1Vf!t4'1!sl$!sc$0!v9%!sK+59!sg-8^!sg0<C!sB-X1!tc$!u|&!tc%!sy%5PFg01Y<g01ZG5pog01[R,OE!s=$\^g01]j5png01_6!s='`Bg01aN!sT%bZ!s='cfg01e25p_g01f>,OEg01gJg01hV!sR%ib,OE5JFCX!s$1do"). Qed.
End FPX1.
(* [comment removed for export] *)
