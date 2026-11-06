(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.boost_json.fuzz_parse.images Require Import Plain.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib SymDriveH4
  LibStdioCall LibDiagKn RefOpenFailCS_defs.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_RefUsageCS_defs () := KReplay.lz_vm "##^fI47Corelib4Init9Datatypes4list00!sF=prod00C!sF;3fstK!sC+7Numbers7BinNums8positive01!sKG2K!tuA1K89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX24expr01C13~~~!smc4!smc8sidecond!t`+!v~<nat02!u#c2!uni3!smc5sadd!wMf!v^,6!v^3!yt31Z!v]e7!t3F3!t3c5!t3%!}@<6option00C7!t7N<LibStdioCall:s!s0#_call!z5B!t;'1!t]25Logic2eq!tU_6sc_ret!tQ%!sm]4sc_f!skc5!sk#d!slgwb!slhp!v5gl!skgs!y:B!#8i$!y893and00K!yS;1C!|;]s_pc!uU&!#63;snd!#9AA2K!u,<!uH-!~F60I!u1\9sym_state00!~K&!#5Xe!sqd!#4,$!smd7scripts!sp'c!z;O?RefUsageCS_defs4u_rA!#6tB!#>w+3!t;dB!u'jC!snjD!}3Cbool!{+#ELinuxProcessSemantics5Riscv5Instr;branch_!yD$3!sXG5aluop01!u<`2LX!x/C1Z!#DF-!#A061!vgdE!vgH1!vgT6!sXT4!uBdF!uB'!x1Fmul!x1d!tB#G!~v&!#9A[9!#?[$re!~xi5u_s!tc'!sockn!sojscG!~VjH!t_irF3!sof6!w2#!spkkn!tblc!sph!vE#G!vElG!vEl!tblcG!vEkH!sokE4!w6k!spkkn!tblc!sph!}t$!sokG!w6lG!w6l!tblcG!vEkH!so&".
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymExec23SX2~~~~~~he4expr04conshe4EVarhe4ELit69OSSVerify6Proofsaboost_jsonafuzz_parse3libh2RefOpenFailCS_defs~~~~~~n83spx03nil37Corelib7Numbers7BinNumss91Zhe6kentryhe2SAhe5KWordhe6KRange03app79OSSVerify6Proofsaboost_jsonafuzz_parse3libfRefUsageCS_defs4FPX1~~~~~~hga6US_STKhe3KWr69OSSVerify6Proofsaboost_jsonafuzz_parse3lib9LibDiagKn~~~~~~hm16CANARYhm1adiag_cellshm18kn_cellshe6KAlignhe4KImg46Stdlib6ZArith6BinInt1Zht13subhe9sym_statehga5knUS0hga5srUS0he2SShe6sentryhe7scriptsn84scr0he2SEhga6u_knB0hga6u_srB0hga5u_knBhga6u_srC0n83IHIhga2LXhga5u_knC69OSSVerify6Proofsaboost_jsonafuzz_parse3libaSymDriveH4~~~~~~ime6kn_cuthga6u_knD0hga6u_srD004bool05falsehe3SCRhga5u_knDhga6u_srE004truehga6u_knF0hga6u_srF0hga6u_knG0hga6u_srG0hga6u_knH0hga6u_srH069OSSVerify6Proofsaboost_jsonafuzz_parse3libcLibStdioCall~~~~~~jj16sc_rethga7u_knG30hga6u_scF3hga7u_srG30hga7u_knH30hga7u_srH30hga7u_knF40hga6u_scE4hga7u_srF40hga7u_knG40hga7u_srG40hga7u_knH40hga7u_srH40he8sidecond04prod04pair03fst37Corelib4Init5Logickh82eqkh83and3h5LinuxProcessSemantics5Riscv5Instrkj97ALU_ADD03sndhe4EAluhe4s_pcjj19stdio_reshga5u_scGhga6u_scG3hga6u_scG4he4SCBr04Some06optionjj14sc_fjj15sc_fdjj14sc_ljj15sc_wbjj15sc_wpjj1astdio_callhe5EAluwkj96BC_GEUkj95BC_GEkj95M_MULjj14sc_shga4u_rAhga4u_rBhga4u_rChga4u_rDhga4u_rEhga5u_rE4hga4u_rFhga5u_rF3hga5u_rF4hga4u_rGhga5u_rG3hga5u_rG4hga4u_rHhga5u_rH3hga5u_rH4he4EExthe3EMdkj95BC_LThga6u_knE4hga6u_knF3hga5u_knGhga6u_knG3hga6u_knG4hga6u_srE4hga6u_srF3hga5u_srGhga6u_srG3hga6u_srG4heaSCReadBase" s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.

Abbreviation RSEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition srUS0 : ltac2:(zQ "20!h8!ld@1$0$1") := ltac2:(zQ "60!ld!m4!ma!n1!re!s4@3$1$0@1$3Z@3$1$0@1$2N7@3$1$0@1$4-o0@3$1$0@1$2N9@3$1$0@1$3+hgrmr8@3$1$0@1$2Nb@3$1$0@1$2Nc@3$1$0@1$2Nd@3$1$0@1$3+2@3$1$0@1$2Nf@3$1$0@1$2Nh0@3$1$0@1$4+8@3$1$0@1$2Nh2@3$1$0@1$2Nh3@3$1$0@1$2Nh4@3$1$0@1$2Nh5@3$1$0@1$2Nh6@3$1$0@1$2Nh7@3$1$0@1$2Nh8@3$1$0@1$2Nh9@3$1$0@1$2Nha@3$1$0@1$2Nhb@3$1$0@1$2Nhc@3$1$0@1$2Nhd@3$1$0@1$2Nhe@3$1$0@1$2Nhf@3$1$0@1$2Ni0@3$1$0@1$2Ni1@3$1$0@1$2Ni2@3$1$0@1$2Ni3@3$1$0@1$2Ni4@3$1$0@1$2Ni5@1$5$0").
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition US_STK : Z := 2128.
Definition knUS0 : ltac2:(zQ "20!h8!u6@1$0$1") := ltac2:(zQ "h10!ma!u6!m4!uf!v4!n1!vc!hg5!s4!hl1!hlb!hpd!hq7!hr5!hs1!hsa!hu9@3$7$1@3$2$1@2$e@1$0N0+h0@3$2$1@3$6@1$0N0+nvvvogggggg0+ogggggggggg0@3$2$1@2$a@2$3@1$0N0@2$h0-j0$9$9@3$2$1@3$4@2$3@1$0N0+8N8@1$0N1@3$2$1@3$6@1$0N1+nvvvogggggg0+ogggggkgggg0@3$2$1@3$4@2$3@1$0N0-j8N8@1$5+tqgsc@3$2$1@3$4@2$3@1$0N0-k0N8@1$0N3@3$2$1@3$4@2$3@1$0N0-k8N8@1$0Nf@3$2$1@3$4@2$3@1$0N0-l0N8@1$0Nh8@3$2$1@3$4@2$3@1$0N0-l8N8@1$0Nh9@3$2$1@3$4@2$3@1$0N0-m0N8@1$0Nha@3$2$1@3$4@2$3@1$0N0-m8N8@1$0Nhb@3$2$1@3$4@2$3@1$0N0-n0N8@1$0Nhc@3$2$1@3$4@2$3@1$0N0-n8N8@1$0Nhd@3$2$1@2$a@2$3@1$5Z+vpgg0+jkgg0@3$2$1@2$f+hggg0+vhgg0@3$2$1@3$4@2$3@1$5Z+hgrmh0N4@1$0N5@3$2$1@3$4@2$3@1$5Z$bN8@1$0N2@1$8$1@3$7$1@1$d$c@3$2$1@3$6@1$0N5+1+jvvvvf@1$8$1").

(* [comment removed for export] *)
Definition u_ssA0 : ltac2:(zQ "10!hv0$0") := ltac2:(zQ "50!s4!hvc!ig5!ige!ih3@5$3+knlm8$2@1$0$4$1Ni6").
Definition u_scrA : ltac2:(zQ "10!ihc$0") := ltac2:(zQ "10!ii6$0").
Definition u_rA := Eval vm_compute in run u_scrA u_ssA0.
Definition u_srA : list expr := Eval vm_compute in s_regs (fst (fst u_rA)).
Definition u_knA : list kentry := Eval vm_compute in kn_after u_rA knUS0.
(* [comment removed for export] *)
Definition u_logM1 : ltac2:(zQ "20!h8!ih3@1$0$1") := ltac2:(zQ "70!ih3!m4!s4!n1!ma!uf!iid@3$1$0@3$6@2$5@1$4N0-ij0N7@1$3+igjqmlmnmhnjn5@1$2$0").
Definition u_knB0 : list kentry := Eval vm_compute in fst (fst (carry u_logM1 u_knA [])).
Definition u_srB0 : list expr := Eval vm_compute in sr_after_call_j u_srA KEPT_MC 38.

(* [comment removed for export] *)
Definition u_ssB0 : ltac2:(zQ "10!hv0$0") := ltac2:(zQ "50!s4!ij2!ijc!ige!ih3@5$3+ugihc$2@1$0$4$1Nk6").
Definition u_rB := Eval vm_compute in run scr0 u_ssB0.
Definition u_srB : list expr := Eval vm_compute in s_regs (fst (fst u_rB)).
Definition u_knB : list kentry := Eval vm_compute in kn_after u_rB u_knB0.
Definition u_srC0 : list expr := Eval vm_compute in sr_after_call_j u_srB KEPT_MC 70.

(* [comment removed for export] *)
Definition u_ssC0 : ltac2:(zQ "10!hv0$0") := ltac2:(zQ "50!s4!ik6!ikf!ige!ih3@5$3+ugihc$2@1$0$4$1Nm6").
Definition u_rC := Eval vm_compute in run scr0 u_ssC0.
Definition u_srC : list expr := Eval vm_compute in s_regs (fst (fst u_rC)).
Definition u_knC : list kentry := Eval vm_compute in kn_after u_rC u_knB.
Definition LX : ltac2:(zQ "10!ld$0") := ltac2:(zQ "10!ma@1$0Nn0").
Definition u_knD0 : ltac2:(zQ "20!h8!u6@1$0$1") := ltac2:(zQ "70!m4!il9!ilf!im5!iqb!vc!u6@3$0$6@3$5$2Z+hvvvf@5$4N0-ko0-km0$1$3").
Definition u_srD0 : list expr := Eval vm_compute in sr_after_call_j u_srC KEPT_CS 102.

(* [comment removed for export] *)
Definition u_ssD0 : ltac2:(zQ "10!hv0$0") := ltac2:(zQ "50!s4!ir5!irf!ige!ih3@5$3+ugtoc$2@1$0$4$1No6").
Definition u_scrD : ltac2:(zQ "10!ihc$0") := ltac2:(zQ "70!is9!s4!m4!ld!isf!n1!it6@3$6@3$2$0$4@1$1$0@3$2$3@1$5Z@1$1$3@1$1$0").
Definition u_rD := Eval vm_compute in run u_scrD u_ssD0.
Definition u_srD : list expr := Eval vm_compute in s_regs (fst (fst u_rD)).
Definition u_knD : list kentry := Eval vm_compute in kn_after u_rD u_knD0.
Definition u_srE0 : list expr := Eval vm_compute in sr_after_call_j u_srD KEPT_MC 134.

(* [comment removed for export] *)
Definition u_ssE0 : ltac2:(zQ "10!hv0$0") := ltac2:(zQ "50!s4!itc!iu5!ige!ih3@5$3+ugihc$2@1$0$4$1Nq6").
Definition u_scrE : ltac2:(zQ "10!ihc$0") := ltac2:(zQ "60!is9!s4!m4!iuf!it6!ld@3$4@3$2$0$3@3$2$0$3@1$1$0@1$1$5@1$1$0").   (* [comment removed for export] *)
Definition u_rE := Eval vm_compute in run u_scrE u_ssE0.
Definition u_srE : list expr := Eval vm_compute in s_regs (fst (fst u_rE)).
Definition u_knE : list kentry := Eval vm_compute in kn_after u_rE u_knD.
Definition u_knF0 : list kentry := Eval vm_compute in kn_cut 0 (-553) BUF_HI IHI u_knE.
Definition u_srF0 : list expr := Eval vm_compute in sr_after_call_j u_srE KEPT_MC 166.

(* [comment removed for export] *)
Definition u_ssF0 : ltac2:(zQ "10!hv0$0") := ltac2:(zQ "50!s4!iv5!ivf!ige!ih3@5$3+ugihc$2@1$0$4$1Ns6").
Definition u_scrF : ltac2:(zQ "10!ihc$0") := ltac2:(zQ "60!is9!s4!m4!iuf!it6!ld@3$4@3$2$0$3@1$1$0@1$1$5@1$1$0").         (* [comment removed for export] *)
Definition u_rF := Eval vm_compute in run u_scrF u_ssF0.
Definition u_srF : list expr := Eval vm_compute in s_regs (fst (fst u_rF)).
Definition u_knF : list kentry := Eval vm_compute in kn_after u_rF u_knF0.
Definition u_knG0 : list kentry := Eval vm_compute in kn_cut 0 (-553) BUF_HI IHI u_knF.
Definition u_srG0 : list expr := Eval vm_compute in sr_after_call_j u_srF KEPT_MC 198.
(* [comment removed for export] *)
Definition u_ssG0 : ltac2:(zQ "10!hv0$0") := ltac2:(zQ "50!s4!jg9!jh3!ige!ih3@5$3+ugihc$2@1$0$4$1Nu6").
Definition u_rG := Eval vm_compute in run scr0 u_ssG0.
Definition u_srG : list expr := Eval vm_compute in s_regs (fst (fst u_rG)).
Definition u_knG : list kentry := Eval vm_compute in kn_after u_rG u_knG0.
Definition u_scG : stdio_res := Eval vm_compute in sc_of 230 u_srG u_knG.
Definition u_srH0 : list expr := Eval vm_compute in sc_sr u_scG.
Definition u_knH0 : list kentry := Eval vm_compute in sc_kn u_scG.
(* [comment removed for export] *)
Definition u_ssH0 : ltac2:(zQ "10!hv0$0") := ltac2:(zQ "50!s4!jhd!ji7!ige!ih3@5$3+ugmuc$2@1$0$4$1Nhg6").
Definition u_rH := Eval vm_compute in run scr0 u_ssH0.

(* [comment removed for export] *)
Definition u_scrF3 : ltac2:(zQ "10!ihc$0") := ltac2:(zQ "60!is9!s4!m4!isf!it6!ld@3$4@3$2$0$3@1$1$0@1$1$5@1$1$0").   (* [comment removed for export] *)
Definition u_rF3 := Eval vm_compute in run u_scrF3 u_ssF0.
Definition u_srF3 : list expr := Eval vm_compute in s_regs (fst (fst u_rF3)).
Definition u_knF3 : list kentry := Eval vm_compute in kn_after u_rF3 u_knF0.
Definition u_scF3 : stdio_res := Eval vm_compute in sc_of 198 u_srF3 u_knF3.
Definition u_srG30 : list expr := Eval vm_compute in sc_sr u_scF3.
Definition u_knG30 : list kentry := Eval vm_compute in sc_kn u_scF3.
(* [comment removed for export] *)
Definition u_ssG30 : ltac2:(zQ "10!hv0$0") := ltac2:(zQ "70!s4!jn0!jna!jo5!jof!ige!ih3@5$5@1$1$3$4@1$0$6$2Nu6").
Definition u_rG3 := Eval vm_compute in run scr0 u_ssG30.
Definition u_srG3 : list expr := Eval vm_compute in s_regs (fst (fst u_rG3)).
Definition u_knG3 : list kentry := Eval vm_compute in kn_after u_rG3 u_knG30.
Definition u_scG3 : stdio_res := Eval vm_compute in sc_of 230 u_srG3 u_knG3.
Definition u_srH30 : list expr := Eval vm_compute in sc_sr u_scG3.
Definition u_knH30 : list kentry := Eval vm_compute in sc_kn u_scG3.
(* [comment removed for export] *)
Definition u_ssH30 : ltac2:(zQ "10!hv0$0") := ltac2:(zQ "50!s4!jpa!jq5!ige!ih3@5$3+ugmuc$2@1$0$4$1Nhg6").
Definition u_rH3 := Eval vm_compute in run scr0 u_ssH30.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition u_scrE4 : ltac2:(zQ "10!ihc$0") := ltac2:(zQ "70!is9!s4!m4!isf!iuf!it6!ld@3$5@3$2$0$4@3$2$0$3@1$1$0@1$1$6@1$1$0").  (* [comment removed for export] *)
Definition u_rE4 := Eval vm_compute in run u_scrE4 u_ssE0.
Definition u_srE4 : list expr := Eval vm_compute in s_regs (fst (fst u_rE4)).
Definition u_knE4 : list kentry := Eval vm_compute in kn_after u_rE4 u_knD.
Definition u_scE4 : stdio_res := Eval vm_compute in sc_of 166 u_srE4 u_knE4.
Definition u_srF40 : list expr := Eval vm_compute in sc_sr u_scE4.
Definition u_knF40 : list kentry := Eval vm_compute in sc_kn u_scE4.
(* [comment removed for export] *)
Definition u_ssF40 : ltac2:(zQ "10!hv0$0") := ltac2:(zQ "70!s4!jn0!jr0!jrb!js5!ige!ih3@5$5@1$1$3$4@1$0$6$2Ns6").
Definition u_rF4 := Eval vm_compute in run scr0 u_ssF40.
Definition u_srF4 : list expr := Eval vm_compute in s_regs (fst (fst u_rF4)).
Definition u_knF4 : list kentry := Eval vm_compute in kn_after u_rF4 u_knF40.
(* [comment removed for export] *)
Definition u_logSUF : ltac2:(zQ "20!h8!ih3@1$0$1") := ltac2:(zQ "70!ih3!m4!s4!n1!ma!uf!iid@3$1$0@3$6@2$5@1$4N0-ij0N7@1$3+qlklllgkukpi0@1$2$0").
Definition u_knG40 : list kentry := Eval vm_compute in fst (fst (carry u_logSUF u_knF4 [])).
Definition u_srG40 : list expr := Eval vm_compute in sr_after_call_j u_srF4 KEPT_MC 198.
(* [comment removed for export] *)
Definition u_ssG40 : ltac2:(zQ "10!hv0$0") := ltac2:(zQ "50!s4!jt0!jtb!ige!ih3@5$3+ugihc$2@1$0$4$1Nu6").
Definition u_rG4 := Eval vm_compute in run scr0 u_ssG40.
Definition u_srG4 : list expr := Eval vm_compute in s_regs (fst (fst u_rG4)).
Definition u_knG4 : list kentry := Eval vm_compute in kn_after u_rG4 u_knG40.
Definition u_scG4 : stdio_res := Eval vm_compute in sc_of 230 u_srG4 u_knG4.
Definition u_srH40 : list expr := Eval vm_compute in sc_sr u_scG4.
Definition u_knH40 : list kentry := Eval vm_compute in sc_kn u_scG4.
(* [comment removed for export] *)
Definition u_ssH40 : ltac2:(zQ "10!hv0$0") := ltac2:(zQ "50!s4!ju6!jv1!ige!ih3@5$3+ugmuc$2@1$0$4$1Nhg6").
Definition u_rH4 := Eval vm_compute in run scr0 u_ssH40.

Lemma u_itinerary : ltac2:(zQ "k99!jvc!u2!h8!kg7!ld!kgd!hv0!kh3!kic!ihc!kj2!n1!kld!s4!km8!kmd!kn4!ilf!ma!knb!m4!jrb!jo5!ko8!kp1!kpb!kq5!iuf!kqc!kr2!kra!ks2!ksb!jn0!kt3!ktc!ku5!kv3!isf!kvb!lg5!lge!lh7!lhf!li7!lif!lj7!ljf!lk7!ll0!ll8!lm1!lma!ln2!lnb!lo4!loc!lp5!lpe!lq5!lqb!lr4!lre!ls8!lt1!ltb!lu5!luf!lv9!mg2!mgc!uf!mh6&@4$5$1@1$2$0+uqtq8@1$d$0&@3$i5$c@3$i5$c$h1@1$bZ@1$bZ&@4$ha$hb$i8@4$ja$hbN0N4$h1~1&@3$h4$0~2@1$d$0&@3$f$c@3$jb$i9@1$b-1$h1@1$b+k9&@4$5$1@1$2$0+tvqk0@1$d$0&@4$5@2$3$1$1$1@4$5$1$1+ugmuc+vppq8+2&@4$5$1@1$2$0+tqnrc@1$d$0&@4$5$4$4@3$f$c@1$h2N0@1$b-ij0@3$f$c@1$h2N0@1$b-ii9@2$a@3$8@2$3$1@1$2$0@4$5$1@1$2$0@1$h0@3$7$6@1$2$0@3$7@2$3$6@1$2$0$9$ib@3$e$6@1$2$0@3$7@2$3$6@1$2$0$9$ib~0@2$a@3$8@2$3$1@1$2$0@4$5$1@1$2$0@1$h0@3$7$6@1$2$0@3$7@2$3$6@1$2$0$9$ic@3$e$6@1$2$0@3$7@2$3$6@1$2$0$9$ic~0@2$a@3$8@2$3$1@1$2$0@4$5$1@1$2$0@1$h0@3$7$6@1$2$0@3$7@2$3$6@1$2$0$9$id@3$e$6@1$2$0@3$7@2$3$6@1$2$0$9$id@4$5$1@1$2$0+urpt4@1$d$0@2$a@3$8@2$3$1@1$2$0@4$5$1@1$2$0@1$h0@3$7$6@1$2$0@3$7@2$3$6@1$2$0$9$ie@3$e$6@1$2$0@3$7@2$3$6@1$2$0$9$ie@4$5$1@1$2$0+uqtq8@3$h4$0@4$ha$i6$jc@3$i5$c$h1@1$bZ$h1@3$h4$0@4$k8@2$k7@3$f$c@1$h2N1$h1ZN1$i6@1$bZ@1$d$0@2$a@3$8@2$3$1@1$2$0@4$5$1@1$2$0@1$h0@3$7$6@1$2$0@3$7@2$3$6@1$2$0$9$if@3$e$6@1$2$0@3$7@2$3$6@1$2$0$9$if@4$5$1@1$2$0+uqtq8@3$h4$0@4$ha$hb$i7@1$b+k9$h1~3@2$a@3$8@2$3$1@1$2$0@4$5$1@1$2$0@1$h0@3$7$6@1$2$0@3$7@2$3$6@1$2$0$9$j1@3$e$6@1$2$0@3$7@2$3$6@1$2$0$9$j1@4$5$1@1$2$0+uqtq8@3$h4$0@4$ha$hb$i7~4@1$b+7@1$d$0@2$a@3$8@2$3$1@1$2$0@4$5$1@1$2$0@1$h0@3$7$6@1$2$0@3$7@2$3$6@1$2$0$9$j4@3$e$6@1$2$0@3$7@2$3$6@1$2$0$9$j4~5@2$a@3$8@1$hd$h3@3$i4Nu6$k4$jf@2$hc$h3$h7@2$a@3$8@2$3@2$3$1$1$1@4$5@2$3$1$1$1@4$5$1$1@1$i1$h7@1$he$h7@1$hf$h7~6@2$a@3$8@2$3@2$3$4$4$4@4$5@2$3$4$4$4@4$5$4$4@1$i2$h7@1$i3$h7@1$i0$h7@4$5@2$3$4$4$4@4$5$4$4@3$f$c@1$h2N0@1$b-ij0@3$f$c@3$f$c@1$h2N0$h1@1$b-ii2@1$bZ@2$a@3$8@2$3$1@1$2$0@4$5$1@1$2$0@1$h0@3$7$6@1$2$0@3$7@2$3$6@1$2$0$9$j7@3$e$6@1$2$0@3$7@2$3$6@1$2$0$9$j7~7@2$a@3$8@2$3$1@1$2$0@4$5$1@1$2$0@1$h0@3$7$6@1$2$0@3$7@2$3$6@1$2$0$9$j2@3$e$6@1$2$0@3$7@2$3$6@1$2$0$9$j2@4$5$1@1$2$0+tvqk0@3$h4$0@4$ha$i6$i7~4@1$b+7@1$d$0@2$a@3$8@1$hd$h3@3$i4Ns6$k3$je@2$hc$h3$h6@2$a@3$8@2$3@2$3$1$1$1@4$5@2$3$1$1$1@4$5$1$1@1$i1$h6@1$he$h6@1$hf$h6@4$5@2$3$1$1$1@4$5$1$1+ugorc+vppq8+2@2$a@3$8@2$3@2$3@2$3$4$4$4$4@4$5@2$3@2$3$4$4$4$4@4$5@2$3$4$4$4@4$5$4$4@1$i2$h6@1$i3$h6@1$ia$h6@1$i0$h6@4$5@2$3@2$3$4$4$4$4@4$5@2$3$4$4$4@4$5$4$4@3$f$c@1$h2N0@1$b-ij0@3$f$c@3$f$c@1$h2N0$h1@1$b-ii9@1$b+hhkm0@1$b+7@2$a@3$8@2$3$1@1$2$0@4$5$1@1$2$0@1$h0@3$7$6@1$2$0@3$7@2$3$6@1$2$0$9$j5@3$e$6@1$2$0@3$7@2$3$6@1$2$0$9$j5~5@2$a@3$8@1$hd$h3@3$i4Nu6$k5$k0@2$hc$h3$h8@2$a@3$8@2$3@2$3$1$1$1@4$5@2$3$1$1$1@4$5$1$1@1$i1$h8@1$he$h8@1$hf$h8~6@2$a@3$8@2$3@2$3$4$4$4@4$5@2$3$4$4$4@4$5$4$4@1$i2$h8@1$i3$h8@1$i0$h8@4$5@2$3$4$4$4@4$5$4$4@3$f$c@1$h2N0@1$b-ij0@3$f$c@1$h2N0@1$b-ij0@1$bZ@2$a@3$8@2$3$1@1$2$0@4$5$1@1$2$0@1$h0@3$7$6@1$2$0@3$7@2$3$6@1$2$0$9$j8@3$e$6@1$2$0@3$7@2$3$6@1$2$0$9$j8~7@2$a@3$8@2$3$1@1$2$0@4$5$1@1$2$0@1$h0@3$7$6@1$2$0@3$7@2$3$6@1$2$0$9$j0@3$e$6@1$2$0@3$7@2$3$6@1$2$0$9$j0@4$5$1@1$2$0+tvqk0@3$h4$0@4$ha$i6$i7@1$b+k9$h1~3@2$a@3$8@1$hd$h3@3$i4Nq6$k2$jd@2$hc$h3$h5@2$a@3$8@2$3@2$3$1$1$1@4$5@2$3$1$1$1@4$5$1$1@1$i1$h5@1$he$h5@1$hf$h5@4$5@2$3$1$1$1@4$5$1$1+uhitc+vppq8+2@2$a@3$8@2$3@2$3@2$3$4$4$4$4@4$5@2$3@2$3$4$4$4$4@4$5@2$3$4$4$4@4$5$4$4@1$i2$h5@1$i3$h5@1$ia$h5@1$i0$h5@4$5@2$3@2$3$4$4$4$4@4$5@2$3$4$4$4~8@1$h2N1$h1@2$a@3$8@2$3$1@1$2$0@4$5$1@1$2$0@1$h0@3$7$6@1$2$0@3$7@2$3$6@1$2$0$9$j3@3$e$6@1$2$0@3$7@2$3$6@1$2$0$9$j3~0@2$a@3$8@2$3$1@1$2$0@4$5$1@1$2$0@1$h0@3$7$6@1$2$0@3$7@2$3$6@1$2$0$9$j6@3$e$6@1$2$0@3$7@2$3$6@1$2$0$9$j6~5@2$a@3$8@1$hd$h3@3$i4Nu6$k6$k1@2$hc$h3$h9@2$a@3$8@2$3@2$3$1$1$1@4$5@2$3$1$1$1@4$5$1$1@1$i1$h9@1$he$h9@1$hf$h9~6@2$a@3$8@2$3@2$3$4$4$4@4$5@2$3$4$4$4@4$5$4$4@1$i2$h9@1$i3$h9@1$i0$h9@4$5@2$3$4$4$4~8@1$bZ@3$8@2$3$1@1$2$0@4$5$1@1$2$0@1$h0@3$7$6@1$2$0@3$7@2$3$6@1$2$0$9$j9@3$e$6@1$2$0@3$7@2$3$6@1$2$0$9$j9~7").
Proof.
repeat split; vm_compute; reflexivity. Qed.
End FPX1.
(* [comment removed for export] *)
