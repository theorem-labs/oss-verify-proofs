(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.U Require U0Gc6. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.boost_json.fuzz_parse.images Require Import Ubsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib SymDriveH4.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.U Require Import LibStdioCall LibDiagKn RefOpenFailCS_defs.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymExec23SX2~~~~~~he4expr04conshe4EVarhe4ELit79OSSVerify6Proofsaboost_jsonafuzz_parse3lib1Uh2RefOpenFailCS_defs~~~~~~n83spx03nil37Corelib7Numbers7BinNumssb1Zhe6kentryhe2SAhe5KWordhe6KRange03apphe3KWr89OSSVerify6Proofsaboost_jsonafuzz_parse3lib1UfRefUsageCS_defs4FPX1~~~~~~hh26US_STKhe6KAlignhe4KImg79OSSVerify6Proofsaboost_jsonafuzz_parse3lib1U9LibDiagKn~~~~~~hn56CANARYhn5adiag_cellshn58kn_cells46Stdlib6ZArith6BinInt1Zht73subhe9sym_statehe2SShe6sentryhh25knUS0hh25srUS0he7scriptsn84scr0he2SEhh26u_knB0hh26u_srB0hh25u_knBhh26u_srC069OSSVerify6Proofsaboost_jsonafuzz_parse3libaSymDriveH4~~~~~~ilf6kn_cutn83IHIhh22LXhh25u_knChh26u_knD0hh26u_srD004bool05falsehe3SCRhh25u_knDhh26u_srE004truehh26u_knF0hh26u_srF0hh26u_knG0hh26u_srG0hh26u_knH0hh26u_srH079OSSVerify6Proofsaboost_jsonafuzz_parse3lib1UcLibStdioCall~~~~~~jj76sc_rethh27u_knG30hh26u_scF3hh27u_srG30hh27u_knH30hh27u_srH30hh27u_knF40hh26u_scE4hh27u_srF40hh27u_knG40hh27u_srG40hh27u_knH40hh27u_srH40he8sidecond04prod04pair03fst37Corelib4Init5Logicki02eqki03and3h5LinuxProcessSemantics5Riscv5Instrkk17ALU_ADD03sndhe4EAluhe4s_pcjj79stdio_reshe4SCBrhh25u_scGhh26u_scG3hh26u_scG404Some06optionhe5EAluwjj74sc_fjj75sc_fdjj74sc_ljj75sc_wbjj75sc_wpjj7astdio_callkk16BC_GEUkk15BC_GEkk15M_MULhe4EExthe3EMdjj74sc_shh24u_rAhh24u_rBhh24u_rChh24u_rDhh24u_rEhh25u_rE4hh24u_rFhh25u_rF3hh25u_rF4hh24u_rGhh25u_rG3hh25u_rG4hh24u_rHhh25u_rH3hh25u_rH4kk15BC_LTheaSCReadBasehh26u_knE4hh26u_knF3hh25u_knGhh26u_knG3hh26u_knG4hh26u_srE4hh26u_srF3hh25u_srGhh26u_srG3hh26u_srG4" s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition srUS0 : ltac2:(zQ "20!h8!ld@1$0$1") := ltac2:(zQ "60!ld!m4!ma!n1!s0!s6@3$1$0@1$3Z@3$1$0@1$2N7@3$1$0@1$4-o0@3$1$0@1$2N9@3$1$0@1$3+hgurv8@3$1$0@1$2Nb@3$1$0@1$2Nc@3$1$0@1$2Nd@3$1$0@1$3+2@3$1$0@1$2Nf@3$1$0@1$2Nh0@3$1$0@1$4+8@3$1$0@1$2Nh2@3$1$0@1$2Nh3@3$1$0@1$2Nh4@3$1$0@1$2Nh5@3$1$0@1$2Nh6@3$1$0@1$2Nh7@3$1$0@1$2Nh8@3$1$0@1$2Nh9@3$1$0@1$2Nha@3$1$0@1$2Nhb@3$1$0@1$2Nhc@3$1$0@1$2Nhd@3$1$0@1$2Nhe@3$1$0@1$2Nhf@3$1$0@1$2Ni0@3$1$0@1$2Ni1@3$1$0@1$2Ni2@3$1$0@1$2Ni3@3$1$0@1$2Ni4@3$1$0@1$2Ni5@1$5$0").
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition US_STK : Z := 2128.
Definition knUS0 : ltac2:(zQ "20!h8!u8@1$0$1") := ltac2:(zQ "h10!ma!u8!m4!v1!v6!n1!ve!hg7!s6!hgc!hlb!hm5!hme!hr3!hrd!hsb!huf@3$7$1@3$2$1@2$b@1$0N0+h0@3$2$1@3$6@1$0N0+nvvvogggggg0+ogggggggggg0@3$2$1@2$9@2$3@1$0N0@2$h0-j0$a$a@3$2$1@3$4@2$3@1$0N0+8N8@1$0N1@3$2$1@3$6@1$0N1+nvvvogggggg0+ogggggkgggg0@3$2$1@3$4@2$3@1$0N0-j8N8@1$5+ttln4@3$2$1@3$4@2$3@1$0N0-k0N8@1$0N3@3$2$1@3$4@2$3@1$0N0-k8N8@1$0Nf@3$2$1@3$4@2$3@1$0N0-l0N8@1$0Nh8@3$2$1@3$4@2$3@1$0N0-l8N8@1$0Nh9@3$2$1@3$4@2$3@1$0N0-m0N8@1$0Nha@3$2$1@3$4@2$3@1$0N0-m8N8@1$0Nhb@3$2$1@3$4@2$3@1$0N0-n0N8@1$0Nhc@3$2$1@3$4@2$3@1$0N0-n8N8@1$0Nhd@3$2$1@2$9@2$3@1$5Z+vsgg0+jlgg0@3$2$1@2$c+hggg0+vkgg0@3$2$1@3$4@2$3@1$5Z+hgurl0N4@1$0N5@3$2$1@3$4@2$3@1$5Z$dN8@1$0N2@1$8$1@3$7$1@1$f$e@3$2$1@3$6@1$0N5+1+jvvvvf@1$8$1").

(* [comment removed for export] *)
Definition u_ssA0 : ltac2:(zQ "10!hv6$0") := ltac2:(zQ "50!s6!ig2!ig7!ih0!ih9@5$1+knhnc$4@1$0$2$3Ni6").
Definition u_scrA : ltac2:(zQ "10!ii2$0") := ltac2:(zQ "10!iic$0").
Definition u_rA := Eval vm_compute in run u_scrA u_ssA0.
Definition u_srA : list expr := Eval vm_compute in s_regs (fst (fst u_rA)).
Definition u_knA : list kentry := Eval vm_compute in kn_after u_rA knUS0.
(* [comment removed for export] *)
Definition u_logM1 : ltac2:(zQ "20!h8!ig7@1$0$1") := ltac2:(zQ "70!ig7!m4!s6!n1!ma!v1!ij3@3$1$0@3$6@2$5@1$4N0-ij0N7@1$3+igjqmlmnmhnjn5@1$2$0").
Definition u_knB0 : list kentry := Eval vm_compute in fst (fst (carry u_logM1 u_knA [])).
Definition u_srB0 : list expr := Eval vm_compute in sr_after_call_j u_srA KEPT_MC 38.

(* [comment removed for export] *)
Definition u_ssB0 : ltac2:(zQ "10!hv6$0") := ltac2:(zQ "50!s6!ig2!ig7!ij8!ik2@5$1+ujms4$4@1$0$2$3Nk6").
Definition u_rB := Eval vm_compute in run scr0 u_ssB0.
Definition u_srB : list expr := Eval vm_compute in s_regs (fst (fst u_rB)).
Definition u_knB : list kentry := Eval vm_compute in kn_after u_rB u_knB0.
Definition u_srC0 : list expr := Eval vm_compute in sr_after_call_j u_srB KEPT_MC 70.

(* [comment removed for export] *)
Definition u_ssC0 : ltac2:(zQ "10!hv6$0") := ltac2:(zQ "50!s6!ig2!ig7!ikc!il5@5$1+ujms4$4@1$0$2$3Nm6").
Definition u_rC := Eval vm_compute in run scr0 u_ssC0.
Definition u_srC : list expr := Eval vm_compute in s_regs (fst (fst u_rC)).
Definition u_knC : list kentry := Eval vm_compute in kn_after u_rC u_knB.
Definition LX : ltac2:(zQ "10!ld$0") := ltac2:(zQ "10!ma@1$0Nn0").
Definition u_knD0 : ltac2:(zQ "20!h8!u8@1$0$1") := ltac2:(zQ "70!m4!ipc!ve!u8!iq6!iqc!ir2@3$0$3@3$2$5Z+hvvvf@5$1N0-ko0-km0$4$6").
Definition u_srD0 : list expr := Eval vm_compute in sr_after_call_j u_srC KEPT_CS 102.

(* [comment removed for export] *)
Definition u_ssD0 : ltac2:(zQ "10!hv6$0") := ltac2:(zQ "50!s6!ig2!ig7!irb!is5@5$1+ukij4$4@1$0$2$3No6").
Definition u_scrD : ltac2:(zQ "10!ii2$0") := ltac2:(zQ "70!isf!s6!m4!ld!it5!n1!itc@3$6@3$2$0$4@1$1$0@3$2$3@1$5Z@1$1$3@1$1$0").
Definition u_rD := Eval vm_compute in run u_scrD u_ssD0.
Definition u_srD : list expr := Eval vm_compute in s_regs (fst (fst u_rD)).
Definition u_knD : list kentry := Eval vm_compute in kn_after u_rD u_knD0.
Definition u_srE0 : list expr := Eval vm_compute in sr_after_call_j u_srD KEPT_MC 134.

(* [comment removed for export] *)
Definition u_ssE0 : ltac2:(zQ "10!hv6$0") := ltac2:(zQ "50!s6!ig2!ig7!iu2!iub@5$1+ujms4$4@1$0$2$3Nq6").
Definition u_scrE : ltac2:(zQ "10!ii2$0") := ltac2:(zQ "60!isf!s6!m4!iv5!itc!ld@3$4@3$2$0$3@3$2$0$3@1$1$0@1$1$5@1$1$0").   (* [comment removed for export] *)
Definition u_rE := Eval vm_compute in run u_scrE u_ssE0.
Definition u_srE : list expr := Eval vm_compute in s_regs (fst (fst u_rE)).
Definition u_knE : list kentry := Eval vm_compute in kn_after u_rE u_knD.
Definition u_knF0 : list kentry := Eval vm_compute in kn_cut 0 (-553) BUF_HI IHI u_knE.
Definition u_srF0 : list expr := Eval vm_compute in sr_after_call_j u_srE KEPT_MC 166.

(* [comment removed for export] *)
Definition u_ssF0 : ltac2:(zQ "10!hv6$0") := ltac2:(zQ "50!s6!ig2!ig7!ivb!jg5@5$1+ujms4$4@1$0$2$3Ns6").
Definition u_scrF : ltac2:(zQ "10!ii2$0") := ltac2:(zQ "60!isf!s6!m4!iv5!itc!ld@3$4@3$2$0$3@1$1$0@1$1$5@1$1$0").         (* [comment removed for export] *)
Definition u_rF := Eval vm_compute in run u_scrF u_ssF0.
Definition u_srF : list expr := Eval vm_compute in s_regs (fst (fst u_rF)).
Definition u_knF : list kentry := Eval vm_compute in kn_after u_rF u_knF0.
Definition u_knG0 : list kentry := Eval vm_compute in kn_cut 0 (-553) BUF_HI IHI u_knF.
Definition u_srG0 : list expr := Eval vm_compute in sr_after_call_j u_srF KEPT_MC 198.
(* [comment removed for export] *)
Definition u_ssG0 : ltac2:(zQ "10!hv6$0") := ltac2:(zQ "50!s6!ig2!ig7!jgf!jh9@5$1+ujms4$4@1$0$2$3Nu6").
Definition u_rG := Eval vm_compute in run scr0 u_ssG0.
Definition u_srG : list expr := Eval vm_compute in s_regs (fst (fst u_rG)).
Definition u_knG : list kentry := Eval vm_compute in kn_after u_rG u_knG0.
Definition u_scG : stdio_res := Eval vm_compute in sc_of 230 u_srG u_knG.
Definition u_srH0 : list expr := Eval vm_compute in sc_sr u_scG.
Definition u_knH0 : list kentry := Eval vm_compute in sc_kn u_scG.
(* [comment removed for export] *)
Definition u_ssH0 : ltac2:(zQ "10!hv6$0") := ltac2:(zQ "50!s6!ig2!ig7!ji3!jid@5$1+ujrp4$4@1$0$2$3Nhg6").
Definition u_rH := Eval vm_compute in run scr0 u_ssH0.

(* [comment removed for export] *)
Definition u_scrF3 : ltac2:(zQ "10!ii2$0") := ltac2:(zQ "60!isf!s6!m4!it5!itc!ld@3$4@3$2$0$3@1$1$0@1$1$5@1$1$0").   (* [comment removed for export] *)
Definition u_rF3 := Eval vm_compute in run u_scrF3 u_ssF0.
Definition u_srF3 : list expr := Eval vm_compute in s_regs (fst (fst u_rF3)).
Definition u_knF3 : list kentry := Eval vm_compute in kn_after u_rF3 u_knF0.
Definition u_scF3 : stdio_res := Eval vm_compute in sc_of 198 u_srF3 u_knF3.
Definition u_srG30 : list expr := Eval vm_compute in sc_sr u_scF3.
Definition u_knG30 : list kentry := Eval vm_compute in sc_kn u_scF3.
(* [comment removed for export] *)
Definition u_ssG30 : ltac2:(zQ "10!hv6$0") := ltac2:(zQ "70!s6!ig2!ig7!jn8!jo2!jod!jp7@5$1@1$3$5$6@1$0$2$4Nu6").
Definition u_rG3 := Eval vm_compute in run scr0 u_ssG30.
Definition u_srG3 : list expr := Eval vm_compute in s_regs (fst (fst u_rG3)).
Definition u_knG3 : list kentry := Eval vm_compute in kn_after u_rG3 u_knG30.
Definition u_scG3 : stdio_res := Eval vm_compute in sc_of 230 u_srG3 u_knG3.
Definition u_srH30 : list expr := Eval vm_compute in sc_sr u_scG3.
Definition u_knH30 : list kentry := Eval vm_compute in sc_kn u_scG3.
(* [comment removed for export] *)
Definition u_ssH30 : ltac2:(zQ "10!hv6$0") := ltac2:(zQ "50!s6!ig2!ig7!jq2!jqd@5$1+ujrp4$4@1$0$2$3Nhg6").
Definition u_rH3 := Eval vm_compute in run scr0 u_ssH30.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition u_scrE4 : ltac2:(zQ "10!ii2$0") := ltac2:(zQ "70!isf!s6!m4!it5!iv5!itc!ld@3$5@3$2$0$4@3$2$0$3@1$1$0@1$1$6@1$1$0").  (* [comment removed for export] *)
Definition u_rE4 := Eval vm_compute in run u_scrE4 u_ssE0.
Definition u_srE4 : list expr := Eval vm_compute in s_regs (fst (fst u_rE4)).
Definition u_knE4 : list kentry := Eval vm_compute in kn_after u_rE4 u_knD.
Definition u_scE4 : stdio_res := Eval vm_compute in sc_of 166 u_srE4 u_knE4.
Definition u_srF40 : list expr := Eval vm_compute in sc_sr u_scE4.
Definition u_knF40 : list kentry := Eval vm_compute in sc_kn u_scE4.
(* [comment removed for export] *)
Definition u_ssF40 : ltac2:(zQ "10!hv6$0") := ltac2:(zQ "70!s6!ig2!ig7!jn8!jr8!js3!jsd@5$1@1$3$5$6@1$0$2$4Ns6").
Definition u_rF4 := Eval vm_compute in run scr0 u_ssF40.
Definition u_srF4 : list expr := Eval vm_compute in s_regs (fst (fst u_rF4)).
Definition u_knF4 : list kentry := Eval vm_compute in kn_after u_rF4 u_knF40.
(* [comment removed for export] *)
Definition u_logSUF : ltac2:(zQ "20!h8!ig7@1$0$1") := ltac2:(zQ "70!ig7!m4!s6!n1!ma!v1!ij3@3$1$0@3$6@2$5@1$4N0-ij0N7@1$3+qlklllgkukpi0@1$2$0").
Definition u_knG40 : list kentry := Eval vm_compute in fst (fst (carry u_logSUF u_knF4 [])).
Definition u_srG40 : list expr := Eval vm_compute in sr_after_call_j u_srF4 KEPT_MC 198.
(* [comment removed for export] *)
Definition u_ssG40 : ltac2:(zQ "10!hv6$0") := ltac2:(zQ "50!s6!ig2!ig7!jt8!ju3@5$1+ujms4$4@1$0$2$3Nu6").
Definition u_rG4 := Eval vm_compute in run scr0 u_ssG40.
Definition u_srG4 : list expr := Eval vm_compute in s_regs (fst (fst u_rG4)).
Definition u_knG4 : list kentry := Eval vm_compute in kn_after u_rG4 u_knG40.
Definition u_scG4 : stdio_res := Eval vm_compute in sc_of 230 u_srG4 u_knG4.
Definition u_srH40 : list expr := Eval vm_compute in sc_sr u_scG4.
Definition u_knH40 : list kentry := Eval vm_compute in sc_kn u_scG4.
(* [comment removed for export] *)
Definition u_ssH40 : ltac2:(zQ "10!hv6$0") := ltac2:(zQ "50!s6!ig2!ig7!jue!jv9@5$1+ujrp4$4@1$0$2$3Nhg6").
Definition u_rH4 := Eval vm_compute in run scr0 u_ssH40.

Lemma u_itinerary : ltac2:(zQ "k99!kg4!u4!h8!kgf!ld!kh5!hv6!khb!kj4!ii2!kja!n1!km5!s6!kn0!kn5!knc!iqc!ma!ko3!m4!js3!jod!kp0!kp7!kq0!kqa!iv5!kr4!kra!ks2!ksa!kt2!ktb!jn8!ku3!kuc!kv5!it5!lg3!lgd!lh6!lhf!li6!lic!lj4!ljc!lk4!lkc!ll4!llc!lm5!lmd!ln6!lnf!lo7!lp0!lp9!lq1!lqa!lr3!v1!lrc!ls9!lt3!ltd!lu6!lv0!lva!mg4!mge!mh7!mi1&@4$5$1@1$2$0+uuil0@1$d$0&@3$he$c@3$he$c$h1@1$bZ@1$bZ&@4$h7$hb$i8@4$ia$hbN0N4$h1~1&@3$h4$0~2@1$d$0&@3$f$c@3$ib$i9@1$b-1$h1@1$b+k9&@4$5$1@1$2$0+uiuu8@1$d$0&@4$5@2$3$1$1$1@4$5$1$1+ujrp4+vsuu8+2&@4$5$1@1$2$0+ttsm4@1$d$0&@4$5$4$4@3$f$c@1$h2N0@1$b-ij0@3$f$c@1$h2N0@1$b-ii9@2$a@3$8@2$3$1@1$2$0@4$5$1@1$2$0@1$h0@3$7$6@1$2$0@3$7@2$3$6@1$2$0$9$id@3$e$6@1$2$0@3$7@2$3$6@1$2$0$9$id~0@2$a@3$8@2$3$1@1$2$0@4$5$1@1$2$0@1$h0@3$7$6@1$2$0@3$7@2$3$6@1$2$0$9$ie@3$e$6@1$2$0@3$7@2$3$6@1$2$0$9$ie~0@2$a@3$8@2$3$1@1$2$0@4$5$1@1$2$0@1$h0@3$7$6@1$2$0@3$7@2$3$6@1$2$0$9$if@3$e$6@1$2$0@3$7@2$3$6@1$2$0$9$if@4$5$1@1$2$0+uuunc@1$d$0@2$a@3$8@2$3$1@1$2$0@4$5$1@1$2$0@1$h0@3$7$6@1$2$0@3$7@2$3$6@1$2$0$9$j0@3$e$6@1$2$0@3$7@2$3$6@1$2$0$9$j0@4$5$1@1$2$0+uuil0@3$h4$0@4$h7$i6$jc@3$he$c$h1@1$bZ$h1@3$h4$0@4$je@2$jd@3$f$c@1$h2N1$h1ZN1$i6@1$bZ@1$d$0@2$a@3$8@2$3$1@1$2$0@4$5$1@1$2$0@1$h0@3$7$6@1$2$0@3$7@2$3$6@1$2$0$9$j1@3$e$6@1$2$0@3$7@2$3$6@1$2$0$9$j1@4$5$1@1$2$0+uuil0@3$h4$0@4$h7$hb$i7@1$b+k9$h1~3@2$a@3$8@2$3$1@1$2$0@4$5$1@1$2$0@1$h0@3$7$6@1$2$0@3$7@2$3$6@1$2$0$9$j3@3$e$6@1$2$0@3$7@2$3$6@1$2$0$9$j3@4$5$1@1$2$0+uuil0@3$h4$0@4$h7$hb$i7~4@1$b+7@1$d$0@2$a@3$8@2$3$1@1$2$0@4$5$1@1$2$0@1$h0@3$7$6@1$2$0@3$7@2$3$6@1$2$0$9$j6@3$e$6@1$2$0@3$7@2$3$6@1$2$0$9$j6~5@2$a@3$8@1$hd$h3@3$i5Nu6$k6$k1@2$hc$h3$h8@2$a@3$8@2$3@2$3$1$1$1@4$5@2$3$1$1$1@4$5$1$1@1$i2$h8@1$hf$h8@1$i0$h8~6@2$a@3$8@2$3@2$3$4$4$4@4$5@2$3$4$4$4@4$5$4$4@1$i3$h8@1$i4$h8@1$i1$h8@4$5@2$3$4$4$4@4$5$4$4@3$f$c@1$h2N0@1$b-ij0@3$f$c@3$f$c@1$h2N0$h1@1$b-ii2@1$bZ@2$a@3$8@2$3$1@1$2$0@4$5$1@1$2$0@1$h0@3$7$6@1$2$0@3$7@2$3$6@1$2$0$9$j9@3$e$6@1$2$0@3$7@2$3$6@1$2$0$9$j9~7@2$a@3$8@2$3$1@1$2$0@4$5$1@1$2$0@1$h0@3$7$6@1$2$0@3$7@2$3$6@1$2$0$9$j4@3$e$6@1$2$0@3$7@2$3$6@1$2$0$9$j4@4$5$1@1$2$0+uiuu8@3$h4$0@4$h7$i6$i7~4@1$b+7@1$d$0@2$a@3$8@1$hd$h3@3$i5Ns6$k5$k0@2$hc$h3$h6@2$a@3$8@2$3@2$3$1$1$1@4$5@2$3$1$1$1@4$5$1$1@1$i2$h6@1$hf$h6@1$i0$h6@4$5@2$3$1$1$1@4$5$1$1+ujtm4+vsuu8+2@2$a@3$8@2$3@2$3@2$3$4$4$4$4@4$5@2$3@2$3$4$4$4$4@4$5@2$3$4$4$4@4$5$4$4@1$i3$h6@1$i4$h6@1$ic$h6@1$i1$h6@4$5@2$3@2$3$4$4$4$4@4$5@2$3$4$4$4@4$5$4$4@3$f$c@1$h2N0@1$b-ij0@3$f$c@3$f$c@1$h2N0$h1@1$b-ii9@1$b+hhkn9@1$b+7@2$a@3$8@2$3$1@1$2$0@4$5$1@1$2$0@1$h0@3$7$6@1$2$0@3$7@2$3$6@1$2$0$9$j7@3$e$6@1$2$0@3$7@2$3$6@1$2$0$9$j7~5@2$a@3$8@1$hd$h3@3$i5Nu6$k7$k2@2$hc$h3$h9@2$a@3$8@2$3@2$3$1$1$1@4$5@2$3$1$1$1@4$5$1$1@1$i2$h9@1$hf$h9@1$i0$h9~6@2$a@3$8@2$3@2$3$4$4$4@4$5@2$3$4$4$4@4$5$4$4@1$i3$h9@1$i4$h9@1$i1$h9@4$5@2$3$4$4$4@4$5$4$4@3$f$c@1$h2N0@1$b-ij0@3$f$c@1$h2N0@1$b-ij0@1$bZ@2$a@3$8@2$3$1@1$2$0@4$5$1@1$2$0@1$h0@3$7$6@1$2$0@3$7@2$3$6@1$2$0$9$ja@3$e$6@1$2$0@3$7@2$3$6@1$2$0$9$ja~7@2$a@3$8@2$3$1@1$2$0@4$5$1@1$2$0@1$h0@3$7$6@1$2$0@3$7@2$3$6@1$2$0$9$j2@3$e$6@1$2$0@3$7@2$3$6@1$2$0$9$j2@4$5$1@1$2$0+uiuu8@3$h4$0@4$h7$i6$i7@1$b+k9$h1~3@2$a@3$8@1$hd$h3@3$i5Nq6$k4$jf@2$hc$h3$h5@2$a@3$8@2$3@2$3$1$1$1@4$5@2$3$1$1$1@4$5$1$1@1$i2$h5@1$hf$h5@1$i0$h5@4$5@2$3$1$1$1@4$5$1$1+ukno4+vsuu8+2@2$a@3$8@2$3@2$3@2$3$4$4$4$4@4$5@2$3@2$3$4$4$4$4@4$5@2$3$4$4$4@4$5$4$4@1$i3$h5@1$i4$h5@1$ic$h5@1$i1$h5@4$5@2$3@2$3$4$4$4$4@4$5@2$3$4$4$4~8@1$h2N1$h1@2$a@3$8@2$3$1@1$2$0@4$5$1@1$2$0@1$h0@3$7$6@1$2$0@3$7@2$3$6@1$2$0$9$j5@3$e$6@1$2$0@3$7@2$3$6@1$2$0$9$j5~0@2$a@3$8@2$3$1@1$2$0@4$5$1@1$2$0@1$h0@3$7$6@1$2$0@3$7@2$3$6@1$2$0$9$j8@3$e$6@1$2$0@3$7@2$3$6@1$2$0$9$j8~5@2$a@3$8@1$hd$h3@3$i5Nu6$k8$k3@2$hc$h3$ha@2$a@3$8@2$3@2$3$1$1$1@4$5@2$3$1$1$1@4$5$1$1@1$i2$ha@1$hf$ha@1$i0$ha~6@2$a@3$8@2$3@2$3$4$4$4@4$5@2$3$4$4$4@4$5$4$4@1$i3$ha@1$i4$ha@1$i1$ha@4$5@2$3$4$4$4~8@1$bZ@3$8@2$3$1@1$2$0@4$5$1@1$2$0@1$h0@3$7$6@1$2$0@3$7@2$3$6@1$2$0$9$jb@3$e$6@1$2$0@3$7@2$3$6@1$2$0$9$jb~7").
Proof. vm_compute. repeat split; reflexivity. Qed.
End FPX1.
(* [comment removed for export] *)
