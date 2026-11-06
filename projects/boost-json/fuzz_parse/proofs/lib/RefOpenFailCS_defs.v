(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.boost_json.fuzz_parse.images Require Import Plain.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Amb
  PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib SymDriveH4 LibStdioCall LibDiagKn.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_RefOpenFailCS_defs () := KReplay.lz_vm "##_OI47Corelib4Init9Datatypes4list00!sF=prod00C!sF;3fstC89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX24s_pcC13~~~K!t0+7Numbers7BinNums8positive01!sKG2!sK=1Z!sDB3K!uA]expr01!uC&!smb5!smi3!smc8sidecond!uO+!y^A1!sFB2!y~25Logic2eq!z@>6option00!t&<3nat02C7!u\N<LibStdioCall:s!s0#_call!u\B!tZ'1!t;]6sc_ret!t7%!sm]4sc_f!skc5!sk#d!slgwb!slhp!v5gs!skgl!}8i2!smi7!smi4!}{C!#8;#1!}[83and!}:4!}v,1!#8p<sndK!sx<1I!uJ\9sym_state00!uO%I!#8&>0I!v\b!t3'!#6Le!sqd7scripts!sp'c!{SOBRefOpenFailCS_defs3rG3!y33!#<Q<3!yX=bool02K4ELinuxProcessSemantics5Riscv5Instr;branch_!v/$6!sXG5aluop01!sRHmul!sR#!v7c2PX!wr&!#3U[9!#9U$re!wt+!#:h@!u&d4s!x<+!sqdkn!sqlsc!sqk3rH!tcl!sqmkn!tdmcH!}ED1Z!y@e3rI!wYlF!#9TC!~z$1!~zT4!xSf!tk'!xSf!sqlsc!sqk3rG!splH4!|hm!w;m!tdmcH!vIlI!{X'!#=][5sadd!#PDe!#?@+6!sq%I!#9X?0!urc2rB!vci2rC!sokD!sokE!#4v&!#4VQ3!tIeF!u:kG!sokH!|;js!splknH!~jlO!w7lI!so%".
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list37Corelib7Numbers7BinNumshe1Z04cons03nil03nat79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymExec23SX2~~~~~~kb7scripts04boolkb3SCRkb4expr04prodkb9sym_statekb8sidecond04true79OSSVerify6Proofsaboost_jsonafuzz_parse3libh2RefOpenFailCS_defs4FPX1~~~~~~sa4FUELsa5STOPSkb8sym_exec69OSSVerifyaboost_jsonafuzz_parse6images5Plain1M~~~~~~hiffloaded_segmentskb6kentry03fstkb5carrykb5s_log69OSSVerify6Proofsaboost_jsonafuzz_parse3libcLibStdioCall~~~~~~hp69stdio_reskb4ELit06optionhp64SCR_hp6astdio_call37Corelib5Lists7ListDefig73maphe4Npos69OSSVerify6Proofsaboost_jsonafuzz_parse3libcRefMemcpyLib~~~~~~iicbcallee_keptkb4ridx35stdpp9bitvectorbdefinitionsio12bviicccallee_saved3h5LinuxProcessSemantics5Riscv5Instrir47ALU_ADDkb4EAlukb4EVarsa3spxkb2SAkb6KRange03appsa6OF_STKkb5KWordkb3KWr69OSSVerify6Proofsaboost_jsonafuzz_parse3lib9LibDiagKn~~~~~~ji16CANARYji1adiag_cellsji18kn_cellskb6KAlignkb4KImg46Stdlib6ZArith6BinInt1Zjp13subsa4knB0sa4srB0kb2SSkb6sentrykb2SEsa4knC0sa4srC0sa3knCsa4srD0sa3IHIsa2PXsa3knD69OSSVerify6Proofsaboost_jsonafuzz_parse3libaSymDriveH4~~~~~~jvd6kn_cutsa4knE0sa4srE005falsesa3knEsa4srF0sa4knG0sa4srG0sa4knH0sa4srH0sa4knI0sa4srI0hp66sc_retsa5knH30sa4scG3sa5srH30sa5knI30sa5srI30sa5knG40sa4scF4sa5srG40sa5knH40sa5srH40sa5knI40sa5srI4004pair37Corelib4Init5Logickve2eqkve3and03sndsa4scH3sa4scH4kb4s_pc04Somehp64sc_fhp65sc_fdhp64sc_lhp65sc_wbhp65sc_wpkb4SCBrir46BC_GEUhp64sc_ssa3rF4sa3rG3sa3rG4sa3rH3sa3rH4sa3rI3sa3rI4kb5EAluwir45BC_GEir45M_MULsa4knF4sa4knG3sa4knH3sa4knH4sa4srF4sa4srG3sa4srH3sa4srH4kb4EExtkb3EMdsa4scOFsa2rBsa2rCsa2rDsa2rEsa2rFsa2rGsa2rHsa2rIir45BC_LTsa3knHsa3srHkbaSCReadBase" s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.

Abbreviation RSEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition STOPS : ltac2:(zQ "20!h8!j7@1$0$1") := ltac2:(zQ "30!j7!jb!k1@3$1$0+uqtq8@3$1$0+urji8@3$1$0+urpt4@3$1$0+uqsqc@3$1$0+hipk8@3$1$0+hiqt4@3$1$0+ttvu0@3$1$0+tqnrc@3$1$0+tvqk0@1$2$0").
Definition FUEL : nat := 5000.
Definition scr0 : ltac2:(zQ "10!oa$0") := ltac2:(zQ "40!k1!p4!pa!q0@3$2@1$0$1@1$0$3@1$0$1").
Definition run : ltac2:(zQ "50!q7!oa!qd!h8!r9>3scr$1>2ss$2@2$0@2$0$2@1$3$4$1") := ltac2:(zQ "90!k1!s4!hh5!hhc!oa!r9!hi4!qd!hm5\3scr$4\2ss$7@7$6$8$2$1$3^2^1@1$0$5").
Definition kn_after : ltac2:(zQ "60!h8!q7!hn8!oa!r9!qd>1r@2$1@2$1$5@1$0$4$3>2kn@1$0$2@1$0$2") := ltac2:(zQ "b0!h8!r9!ho1!q7!hn8!qd!p4!oa!k1!ho6!hoe\1r@2$3@2$3$5@1$0$1$7\2kn@1$0$4@3$2@1$0$4@1$0$1@3$2@2$3@1$0$4@1$0$1@1$0$6@3$9@1$a@3$2$5@1$0$1@3$2@2$3$5@1$0$1$7^2^1@1$8$6").
(* [comment removed for export] *)
Definition sc_of : ltac2:(zQ "50!h8!k6!ht5!q0!hn8>2nv$1>2sr@1$0$3>2kn@1$0$4$2") := ltac2:(zQ "a0!hu2!ht5!h8!k1!hu9!q0!hn8!k6!hv1!hv9\2nv$7\2sr@1$2$5\2kn@1$2$6M4\1x@1$4$1$1@3$9^3^2^1\1r$1^1@c$8ZZZ@1$0Z@1$0Z@1$0Z@1$0Z@1$0Z@1$0Z@1$0Z@1$3$5@1$3$6").
(* [comment removed for export] *)
Definition KEPT_MC : ltac2:(zQ "20!h8!k6@1$0$1") := ltac2:(zQ "60!k6!ihe!ii5!imb!ina!ipe@4$1@1$5@1$2#5$0$4$3").     (* [comment removed for export] *)
Definition KEPT_CS : ltac2:(zQ "20!h8!k6@1$0$1") := ltac2:(zQ "60!k6!ihe!ii5!iq4!ina!ipe@4$1@1$5@1$2#5$0$4$3").    (* [comment removed for export] *)
(* [comment removed for export] *)
Definition IHI : Z := 0x12d000.
(* [comment removed for export] *)
Definition BUF_LO : Z := -560.
Definition BUF_HI : Z := -480.

(* [comment removed for export] *)
Definition spx : ltac2:(zQ "20!j7!q0>1k$0$1") := ltac2:(zQ "50!j7!it8!iu3!hu2!iua\1k$0@3$2$1@1$4N0@1$3^1").
(* [comment removed for export] *)
Definition srOF_base : ltac2:(zQ "20!h8!q0@1$0$1") := ltac2:(zQ "60!q0!jb!hu2!k1!iv1!iua@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$4-o0@3$1$0@1$2+hgog0@3$1$0@1$2+hgrmr8@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$5N2@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@1$3$0").
Definition KEPT_OF : ltac2:(zQ "20!h8!k6@1$0$1") := ltac2:(zQ "30!k6!jb!k1@3$1$0N2@3$1$0N4@3$1$0Nh2@1$2$0").
Definition srB0 : list expr := Eval vm_compute in sr_after_call_j srOF_base KEPT_OF 6.
(* [comment removed for export] *)
Definition OF_STK : Z := 2048.
Definition knB0 : ltac2:(zQ "20!h8!hn8@1$0$1") := ltac2:(zQ "h10!hn8!jb!iua!iv7!hu2!ivc!jg5!k1!jga!jh3!jhb!jld!jm7!jn5!jo1!joa!jq9@3$6$0@3$1$0@2$e@1$2N0+h0@3$1$0@3$5@1$2N0+nvvvogggggg0+ogggggggggg0@3$1$0@2$a@2$3@1$2N0@2$h0-o0$8$8@3$1$0@3$5@1$2N2+nvvvogggggg0+ogggggkgggg0@3$1$0@2$a@2$3@1$4Z+vpgg0+jkgg0@3$1$0@2$f+hggg0+vhgg0@3$1$0@3$9@2$3@1$4Z+hgrmh0N4@1$2N5@3$1$0@3$9@2$3@1$4Z$bN8@1$2N1@1$7$0@3$6$0@1$d$c@3$1$0@3$5@1$2N5+1+jvvvvf@1$7$0").
Definition ssB0 : ltac2:(zQ "10!qd$0") := ltac2:(zQ "50!k1!jr0!jr7!jre!js3@5$3+knmm0$2@1$0$4$1Ni7").
Definition rB := Eval vm_compute in run scr0 ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knB0.
(* [comment removed for export] *)
Definition logM1 : ltac2:(zQ "20!h8!js3@1$0$1") := ltac2:(zQ "70!js3!jb!hu2!iua!iv7!jsc!k1@3$1$0@3$5@2$4@1$3N0-ii0N1@1$2+i0@3$1$0@3$5@2$4@1$3N0-ii8N8@1$2+mumlngmvignkmvme@3$1$0@3$5@2$4@1$3N0-ij0N8@1$2+mumhmjigjqmpmsm3@1$6$0").
Definition knC0 : list kentry := Eval vm_compute in fst (fst (carry logM1 knB [])).
Definition srC0 : list expr := Eval vm_compute in sr_after_call_j srB KEPT_MC 39.

(* [comment removed for export] *)
Definition ssC0 : ltac2:(zQ "10!qd$0") := ltac2:(zQ "50!k1!jt1!jt8!jre!js3@5$3+ugihc$2@1$0$4$1Nk7").
Definition rC := Eval vm_compute in run scr0 ssC0.
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC)).
Definition knC : list kentry := Eval vm_compute in kn_after rC knC0.
Definition srD0 : list expr := Eval vm_compute in sr_after_call_j srC KEPT_MC 71.

(* [comment removed for export] *)
Definition ssD0 : ltac2:(zQ "10!qd$0") := ltac2:(zQ "50!k1!jtf!ju5!jre!js3@5$3+ugihc$2@1$0$4$1Nm7").
Definition rD := Eval vm_compute in run scr0 ssD0.
Definition srD : list expr := Eval vm_compute in s_regs (fst (fst rD)).
Definition knD : list kentry := Eval vm_compute in kn_after rD knC.
(* [comment removed for export] *)
Definition PX : ltac2:(zQ "10!q0$0") := ltac2:(zQ "10!iua@1$0Nn1").
Definition knE0 : ltac2:(zQ "20!h8!hn8@1$0$1") := ltac2:(zQ "70!jb!juc!jv2!jv7!kja!ivc!hn8@3$0$6@3$5$2Z+hvvvf@5$4N0-ko0-km0$1$3").
Definition srE0 : list expr := Eval vm_compute in sr_after_call_j srD KEPT_CS 103.

(* [comment removed for export] *)
Definition ssE0 : ltac2:(zQ "10!qd$0") := ltac2:(zQ "50!k1!kk4!kkb!jre!js3@5$3+ugtoc$2@1$0$4$1No7").
Definition scrE : ltac2:(zQ "10!oa$0") := ltac2:(zQ "70!p4!k1!jb!q0!kl2!hu2!pa@3$6@3$2$0$4@1$1$0@3$2$3@1$5Z@1$1$3@1$1$0").
Definition rE := Eval vm_compute in run scrE ssE0.
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
Definition knE : list kentry := Eval vm_compute in kn_after rE knE0.
Definition srF0 : list expr := Eval vm_compute in sr_after_call_j srE KEPT_MC 135.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ssF0 : ltac2:(zQ "10!qd$0") := ltac2:(zQ "50!k1!kl9!klf!jre!js3@5$3+ugihc$2@1$0$4$1Nq7").
Definition scrF : ltac2:(zQ "10!oa$0") := ltac2:(zQ "60!p4!k1!jb!s4!pa!q0@3$4@3$2$0$3@3$2$0$3@1$1$0@1$1$5@1$1$0").   (* [comment removed for export] *)
Definition rF := Eval vm_compute in run scrF ssF0.
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF)).
Definition knF : list kentry := Eval vm_compute in kn_after rF knE.
Definition knG0 : list kentry := Eval vm_compute in kn_cut 0 (-543) BUF_HI IHI knF.
Definition srG0 : list expr := Eval vm_compute in sr_after_call_j srF KEPT_MC 167.

(* [comment removed for export] *)
Definition ssG0 : ltac2:(zQ "10!qd$0") := ltac2:(zQ "50!k1!km6!kmd!jre!js3@5$3+ugihc$2@1$0$4$1Ns7").
Definition scrG : ltac2:(zQ "10!oa$0") := ltac2:(zQ "60!p4!k1!jb!s4!pa!q0@3$4@3$2$0$3@1$1$0@1$1$5@1$1$0").         (* [comment removed for export] *)
Definition rG := Eval vm_compute in run scrG ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_after rG knG0.
Definition knH0 : list kentry := Eval vm_compute in kn_cut 0 (-543) BUF_HI IHI knG.
Definition srH0 : list expr := Eval vm_compute in sr_after_call_j srG KEPT_MC 199.

(* [comment removed for export] *)
Definition ssH0 : ltac2:(zQ "10!qd$0") := ltac2:(zQ "50!k1!kn4!knb!jre!js3@5$3+ugihc$2@1$0$4$1Nu7").
Definition rH := Eval vm_compute in run scr0 ssH0.
Definition srH : list expr := Eval vm_compute in s_regs (fst (fst rH)).
Definition knH : list kentry := Eval vm_compute in kn_after rH knH0.
(* [comment removed for export] *)
Definition scOF : stdio_res := Eval vm_compute in sc_of 231 srH knH.
Definition srI0 : list expr := Eval vm_compute in sc_sr scOF.
Definition knI0 : list kentry := Eval vm_compute in sc_kn scOF.

(* [comment removed for export] *)
Definition ssI0 : ltac2:(zQ "10!qd$0") := ltac2:(zQ "50!k1!ko2!ko9!jre!js3@5$3+ugmuc$2@1$0$4$1Nhg7").
Definition rI := Eval vm_compute in run scr0 ssI0.
Definition knI : list kentry := Eval vm_compute in kn_after rI knI0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition scrG3 : ltac2:(zQ "10!oa$0") := ltac2:(zQ "60!p4!k1!jb!kl2!pa!q0@3$4@3$2$0$3@1$1$0@1$1$5@1$1$0").   (* [comment removed for export] *)
Definition rG3 := Eval vm_compute in run scrG3 ssG0.
Definition srG3 : list expr := Eval vm_compute in s_regs (fst (fst rG3)).
Definition knG3 : list kentry := Eval vm_compute in kn_after rG3 knG0.
Definition scG3 : stdio_res := Eval vm_compute in sc_of 199 srG3 knG3.
Definition srH30 : list expr := Eval vm_compute in sc_sr scG3.
Definition knH30 : list kentry := Eval vm_compute in sc_kn scG3.
(* [comment removed for export] *)
Definition ssH30 : ltac2:(zQ "10!qd$0") := ltac2:(zQ "70!k1!kp0!kpa!kq2!kq9!jre!js3@5$5@1$1$3$4@1$0$6$2Nu7").
Definition rH3 := Eval vm_compute in run scr0 ssH30.
Definition srH3 : list expr := Eval vm_compute in s_regs (fst (fst rH3)).
Definition knH3 : list kentry := Eval vm_compute in kn_after rH3 knH30.
Definition scH3 : stdio_res := Eval vm_compute in sc_of 231 srH3 knH3.
Definition srI30 : list expr := Eval vm_compute in sc_sr scH3.
Definition knI30 : list kentry := Eval vm_compute in sc_kn scH3.
(* [comment removed for export] *)
Definition ssI30 : ltac2:(zQ "10!qd$0") := ltac2:(zQ "50!k1!kr1!kr9!jre!js3@5$3+ugmuc$2@1$0$4$1Nhg7").
Definition rI3 := Eval vm_compute in run scr0 ssI30.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition scrF4 : ltac2:(zQ "10!oa$0") := ltac2:(zQ "70!p4!k1!jb!kl2!s4!pa!q0@3$5@3$2$0$4@3$2$0$3@1$1$0@1$1$6@1$1$0").  (* [comment removed for export] *)
Definition rF4 := Eval vm_compute in run scrF4 ssF0.
Definition srF4 : list expr := Eval vm_compute in s_regs (fst (fst rF4)).
Definition knF4 : list kentry := Eval vm_compute in kn_after rF4 knE.
Definition scF4 : stdio_res := Eval vm_compute in sc_of 167 srF4 knF4.
Definition srG40 : list expr := Eval vm_compute in sc_sr scF4.
Definition knG40 : list kentry := Eval vm_compute in sc_kn scF4.
(* [comment removed for export] *)
Definition ssG40 : ltac2:(zQ "10!qd$0") := ltac2:(zQ "70!k1!kp0!ks1!ks9!kt0!jre!js3@5$5@1$1$3$4@1$0$6$2Ns7").
Definition rG4 := Eval vm_compute in run scr0 ssG40.
Definition srG4 : list expr := Eval vm_compute in s_regs (fst (fst rG4)).
Definition knG4 : list kentry := Eval vm_compute in kn_after rG4 knG40.
(* [comment removed for export] *)
Definition logNL : ltac2:(zQ "20!h8!js3@1$0$1") := ltac2:(zQ "70!js3!jb!k1!hu2!iua!iv7!jsc@3$1$0@3$6@2$5@1$4N0-ij0N1@1$3+a@1$2$0").
Definition knH40 : list kentry := Eval vm_compute in fst (fst (carry logNL knG4 [])).
Definition srH40 : list expr := Eval vm_compute in sr_after_call_j srG4 KEPT_MC 199.
(* [comment removed for export] *)
Definition ssH40 : ltac2:(zQ "10!qd$0") := ltac2:(zQ "50!k1!kt8!ku0!jre!js3@5$3+ugihc$2@1$0$4$1Nu7").
Definition rH4 := Eval vm_compute in run scr0 ssH40.
Definition srH4 : list expr := Eval vm_compute in s_regs (fst (fst rH4)).
Definition knH4 : list kentry := Eval vm_compute in kn_after rH4 knH40.
Definition scH4 : stdio_res := Eval vm_compute in sc_of 231 srH4 knH4.
Definition srI40 : list expr := Eval vm_compute in sc_sr scH4.
Definition knI40 : list kentry := Eval vm_compute in sc_kn scH4.
(* [comment removed for export] *)
Definition ssI40 : ltac2:(zQ "10!qd$0") := ltac2:(zQ "50!k1!ku8!kv0!jre!js3@5$3+ugmuc$2@1$0$4$1Nhg7").
Definition rI4 := Eval vm_compute in run scr0 ssI40.

Lemma itinerary_63_64 : ltac2:(zQ "jb3!j7!q0!q7!r9!kv8!h8!qd!ho1!lh2!lh8!hu2!oa!it8!iu3!iua!ht5!ks9!kq2!k1!lhf!li4!lib!lj2!jv2!lj9!hu9!ljf!lk7!ll0!kp0!ll8!lm1!hv9!jb!lma!kl2!s4!ln1!lnb!lo3!lo9!lof!lp5!lpb!lq1!lq7!lqd!lr5!lre!ls7!lse!lt5!ltc!lu3!lua!lv1!lv8!lvf!mg6&@4$4$0@1$5$3+tvqk0@1$h2$3&@4$4@2$2$0$0$0@4$4$0$0+ugmuc+vppq8+2&@4$4$0@1$5$3+tqnrc@1$h2$3@2$9@3$8@2$2$0@1$5$3@4$4$0@1$5$3@1$h6@3$7$6@1$5$3@3$7@2$2$6@1$5$3$b$i8@3$h3$6@1$5$3@3$7@2$2$6@1$5$3$b$i8@4$4$0@1$5$3+tvqk0@3$i1$3@4$i2$i3$i5@3$d$c@3$ja$j0@1$a-1$h7@1$a+jf@1$a+1@1$h2$3@2$9@3$8@1$h9$f@3$i0Ns7$j6$j2@2$h8$f$h1@2$9@3$8@2$2@2$2$0$0$0@4$4@2$2$0$0$0@4$4$0$0@1$hd$h1@1$ha$h1@1$hb$h1@4$4@2$2$0$0$0@4$4$0$0+ugorc+vppq8+2@2$9@3$8@2$2@2$2@2$2$1$1$1$1@4$4@2$2@2$2$1$1$1$1@4$4@2$2$1$1$1@4$4$1$1@1$he$h1@1$hf$h1@1$i6$h1@1$hc$h1@4$4@2$2@2$2$1$1$1$1@4$4@2$2$1$1$1@4$4$1$1@3$d$c@1$eN0@1$a-ij0@3$d$c@3$d$c@1$eN0$h7@1$a-ihf@1$a+hjik1@1$a+1@2$9@3$8@2$2$0@1$5$3@4$4$0@1$5$3@1$h6@3$7$6@1$5$3@3$7@2$2$6@1$5$3$b$ia@3$h3$6@1$5$3@3$7@2$2$6@1$5$3$b$ia~0@2$9@3$8@1$h9$f@3$i0Nu7$j7$j3@2$h8$f$h4@2$9@3$8@2$2@2$2$0$0$0@4$4@2$2$0$0$0@4$4$0$0@1$hd$h4@1$ha$h4@1$hb$h4~1@2$9@3$8@2$2@2$2$1$1$1@4$4@2$2$1$1$1@4$4$1$1@1$he$h4@1$hf$h4@1$hc$h4@4$4@2$2$1$1$1@4$4$1$1@3$d$c@1$eN0@1$a-ij0@3$d$c@1$eN0@1$a-ij0@1$aZ@2$9@3$8@2$2$0@1$5$3@4$4$0@1$5$3@1$h6@3$7$6@1$5$3@3$7@2$2$6@1$5$3$b$ic@3$h3$6@1$5$3@3$7@2$2$6@1$5$3$b$ic~2@2$9@3$8@2$2$0@1$5$3@4$4$0@1$5$3@1$h6@3$7$6@1$5$3@3$7@2$2$6@1$5$3$b$i7@3$h3$6@1$5$3@3$7@2$2$6@1$5$3$b$i7@4$4$0@1$5$3+tvqk0@3$i1$3@4$i2$i3$i5@1$a+jf$h7@3$i1$3@4$i2$i4$if@4$j9$i4N0N4$h7@3$ie$c@3$ie$c$h7@1$aZ@1$aZ@1$h2$3@2$9@3$8@1$h9$f@3$i0Nq7$j5$j1@2$h8$f$h0@2$9@3$8@2$2@2$2$0$0$0@4$4@2$2$0$0$0@4$4$0$0@1$hd$h0@1$ha$h0@1$hb$h0@4$4@2$2$0$0$0@4$4$0$0+uhitc+vppq8+2@2$9@3$8@2$2@2$2@2$2$1$1$1$1@4$4@2$2@2$2$1$1$1$1@4$4@2$2$1$1$1@4$4$1$1@1$he$h0@1$hf$h0@1$i6$h0@1$hc$h0@4$4@2$2@2$2$1$1$1$1@4$4@2$2$1$1$1@4$4$1$1@3$d$c@1$eN0@1$a-ij0@3$d$c@1$eN0@1$a-ihf@1$eN2$h7@2$9@3$8@2$2$0@1$5$3@4$4$0@1$5$3@1$h6@3$7$6@1$5$3@3$7@2$2$6@1$5$3$b$i9@3$h3$6@1$5$3@3$7@2$2$6@1$5$3$b$i9@4$4$0@1$5$3+uqtq8@1$h2$3@2$9@3$8@2$2$0@1$5$3@4$4$0@1$5$3@1$h6@3$7$6@1$5$3@3$7@2$2$6@1$5$3$b$ib@3$h3$6@1$5$3@3$7@2$2$6@1$5$3$b$ib~0@2$9@3$8@1$h9$f@3$i0Nu7$j8$j4@2$h8$f$h5@2$9@3$8@2$2@2$2$0$0$0@4$4@2$2$0$0$0@4$4$0$0@1$hd$h5@1$ha$h5@1$hb$h5~1@2$9@3$8@2$2@2$2$1$1$1@4$4@2$2$1$1$1@4$4$1$1@1$he$h5@1$hf$h5@1$hc$h5@4$4@2$2$1$1$1@4$4$1$1@3$d$c@1$eN0@1$a-ij0@3$d$c@1$eN0@1$a-iif@1$aZ@3$8@2$2$0@1$5$3@4$4$0@1$5$3@1$h6@3$7$6@1$5$3@3$7@2$2$6@1$5$3$b$id@3$h3$6@1$5$3@3$7@2$2$6@1$5$3$b$id~2").
Proof.
repeat split; vm_compute; reflexivity. Qed.

Lemma itinerary_le62 : ltac2:(zQ "j61!r9!h8!j7!q7!qd!ho1!kv8!oa!q0!lh2!lh8!hu2!k1!lhf!it8!jv2!lj2!mgc!jb!iu3!s4!lma!lqd!iua!kl2!ln1!ht5!mh3!mh8!mhd!mi2!mi7!mic!mj1!mj6!lj9!k6!hu9!lr5!mjb!lre!ljf!lk7!ll0!kp0!ll8!lm1!hv9!mk4!mka!lvf!mg6!iv7!ml0&@4$6$2@1$1$0+uqtq8@1$c$0@2$a@3$9$i4N0N0@2$a@3$9@2$3$2@1$1$0@4$6$2@1$1$0@1$h0@3$5$4@1$1$0@3$5@2$3$4@1$1$0$7$hb@3$d$4@1$1$0@3$5@2$3$4@1$1$0$7$hb~0@2$a@3$9@2$3$2@1$1$0@4$6$2@1$1$0@1$h0@3$5$4@1$1$0@3$5@2$3$4@1$1$0$7$hc@3$d$4@1$1$0@3$5@2$3$4@1$1$0$7$hc~0@2$a@3$9@2$3$2@1$1$0@4$6$2@1$1$0@1$h0@3$5$4@1$1$0@3$5@2$3$4@1$1$0$7$hd@3$d$4@1$1$0@3$5@2$3$4@1$1$0$7$hd@4$6$2@1$1$0+urpt4@1$c$0@2$a@3$9@2$3$2@1$1$0@4$6$2@1$1$0@1$h0@3$5$4@1$1$0@3$5@2$3$4@1$1$0$7$he@3$d$4@1$1$0@3$5@2$3$4@1$1$0$7$he@4$6$2@1$1$0+uqtq8@3$h2$0@4$h5$h8$i7@3$h6$e$f@1$bZ$f@3$h2$0@4$j5@2$j4@3$h3$e@1$h7N2$fZN1$h8@1$bZ@1$c$0@2$a@3$9@2$3$2@1$1$0@4$6$2@1$1$0@1$h0@3$5$4@1$1$0@3$5@2$3$4@1$1$0$7$hf@3$d$4@1$1$0@3$5@2$3$4@1$1$0$7$hf@4$6$2@1$1$0+uqtq8@3$h2$0@4$h5$h4$h9@1$b+jf$f@3$h2$0@4$h5$h4$i6@4$j2$h4N0N4$f@3$h6$e@3$h6$e$f@1$bZ@1$bZ@1$c$0@2$a@3$9@2$3$2@1$1$0@4$6$2@1$1$0@1$h0@3$5$4@1$1$0@3$5@2$3$4@1$1$0$7$i0@3$d$4@1$1$0@3$5@2$3$4@1$1$0$7$i0@4$6$2@1$1$0+uqtq8@3$h2$0@4$h5$h4$h9@3$h3$e@3$j3$i8@1$b-1$f@1$b+jf@1$b+1@1$c$0@2$a@3$9@2$3$2@1$1$0@4$6$2@1$1$0@1$h0@3$5$4@1$1$0@3$5@2$3$4@1$1$0$7$i1@3$d$4@1$1$0@3$5@2$3$4@1$1$0$7$i1@4$6$2@1$1$0+tvqk0@1$c$0@2$a@3$9@1$i5$ha@3$ifNu7$j1$j0@2$i3$ha$h1@2$a@3$9@2$3@2$3$2$2$2@4$6@2$3$2$2$2@4$6$2$2@1$ic$h1@1$i9$h1@1$ia$h1@4$6@2$3$2$2$2@4$6$2$2+ugmuc+vppq8+2@2$a@3$9@2$3@2$3$8$8$8@4$6@2$3$8$8$8@4$6$8$8@1$id$h1@1$ie$h1@1$ib$h1@4$6@2$3$8$8$8@4$6$8$8@3$h3$e@1$h7N0@1$b-ij0@3$h3$e@3$h3$e@1$h7N0$f@1$b-ihe@1$bZ@3$9@2$3$2@1$1$0@4$6$2@1$1$0@1$h0@3$5$4@1$1$0@3$5@2$3$4@1$1$0$7$i2@3$d$4@1$1$0@3$5@2$3$4@1$1$0$7$i2@4$6$2@1$1$0+tqnrc@1$c$0").
Proof.
repeat split; vm_compute; reflexivity. Qed.
End FPX1.
(* [comment removed for export] *)
