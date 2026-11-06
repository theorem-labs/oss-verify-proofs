(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Amb PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib SymDriveH4.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.U Require Import LibStdioCall LibDiagKn.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list37Corelib7Numbers7BinNumshe1Z04cons03nil03nat79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymExec23SX2~~~~~~kb7scripts04boolkb3SCRkb4expr04prodkb9sym_statekb8sidecond04truekb8sym_exec89OSSVerify6Proofsaboost_jsonafuzz_parse3lib1Uh2RefOpenFailCS_defs4FPX1~~~~~~t54FUELt55STOPS69OSSVerifyaboost_jsonafuzz_parse6images5Ubsan1M~~~~~~hj1floaded_segmentskb6kentry03fstkb5carrykb5s_log79OSSVerify6Proofsaboost_jsonafuzz_parse3lib1UcLibStdioCall~~~~~~hp89stdio_reskb4ELit06optionhp84SCR_hp8astdio_call37Corelib5Lists7ListDefigb3maphe4Npos69OSSVerify6Proofsaboost_jsonafuzz_parse3libcRefMemcpyLib~~~~~~ij0bcallee_keptkb4ridx35stdpp9bitvectorbdefinitionsio52bvij0ccallee_saved3h5LinuxProcessSemantics5Riscv5Instrir87ALU_ADDkb4EAlukb4EVart53spxkb2SAkb6KRange03appkb5KWordkb3KWrt56OF_STKkb6KAlignkb4KImg79OSSVerify6Proofsaboost_jsonafuzz_parse3lib1U9LibDiagKn~~~~~~jj56CANARYjj5adiag_cellsjj58kn_cells46Stdlib6ZArith6BinInt1Zjp73subkb2SSkb6sentryt54knB0t54srB0kb2SEt54knC0t54srC0t53knCt54srD069OSSVerify6Proofsaboost_jsonafuzz_parse3libaSymDriveH4~~~~~~jv26kn_cutt53IHIt52PXt53knDt54knE0t54srE005falset53knEt54srF0t54knG0t54srG0t54knH0t54srH0t54knI0t54srI0hp86sc_rett55knH30t54scG3t55srH30t55knI30t55srI30t55knG40t54scF4t55srG40t55knH40t55srH40t55knI40t55srI4004pair37Corelib4Init5Logiclg42eqlg43and03sndkb4s_pct54scH3t54scH404Somehp84sc_fhp85sc_fdhp84sc_lhp85sc_wbhp85sc_wpkb4SCBrir86BC_GEUkb5EAluwhp84sc_st53rF4t53rG3t53rG4t53rH3t53rH4t53rI3t53rI4ir85BC_GEir85M_MULkb4EExtkb3EMdt54knF4t54knG3t54knH3t54knH4t54srF4t54srG3t54srH3t54srH4t54scOFt52rBt52rCt52rDt52rEt52rFt52rGt52rHt52rIir85BC_LTkbaSCReadBaset53knHt53srH" s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition STOPS : ltac2:(zQ "20!h8!j7@1$0$1") := ltac2:(zQ "30!j7!jb!k1@3$1$0+uuil0@3$1$0+uunt0@3$1$0+uuunc@3$1$0+uuhl4@3$1$0+hipk8@3$1$0+hiqt4@3$1$0+uhko8@3$1$0+ttsm4@3$1$0+uiuu8@1$2$0").
Definition FUEL : nat := 5000.
Definition scr0 : ltac2:(zQ "10!oa$0") := ltac2:(zQ "40!k1!p4!pa!q0@3$2@1$0$1@1$0$3@1$0$1").
Definition run : ltac2:(zQ "50!q7!oa!qd!h8!r9>3scr$1>2ss$2@2$0@2$0$2@1$3$4$1") := ltac2:(zQ "90!k1!s4!oa!r9!sa!qd!hi2!hi9!hm7\3scr$2\2ss$5@7$4$8$6$1$7^2^1@1$0$3").
Definition kn_after : ltac2:(zQ "60!h8!q7!hna!oa!r9!qd>1r@2$1@2$1$5@1$0$4$3>2kn@1$0$2@1$0$2") := ltac2:(zQ "b0!h8!r9!ho3!q7!hna!qd!p4!oa!k1!ho8!hp0\1r@2$3@2$3$5@1$0$1$7\2kn@1$0$4@3$2@1$0$4@1$0$1@3$2@2$3@1$0$4@1$0$1@1$0$6@3$9@1$a@3$2$5@1$0$1@3$2@2$3$5@1$0$1$7^2^1@1$8$6").
(* [comment removed for export] *)
Definition sc_of : ltac2:(zQ "50!h8!k6!q0!hna!ht9>2nv$1>2sr@1$0$2>2kn@1$0$3$4") := ltac2:(zQ "a0!hu6!ht9!h8!k1!hud!q0!hna!k6!hv5!hvd\2nv$7\2sr@1$2$5\2kn@1$2$6M4\1x@1$4$1$1@3$9^3^2^1\1r$1^1@c$8ZZZ@1$0Z@1$0Z@1$0Z@1$0Z@1$0Z@1$0Z@1$0Z@1$3$5@1$3$6").
(* [comment removed for export] *)
Definition KEPT_MC : ltac2:(zQ "20!h8!k6@1$0$1") := ltac2:(zQ "60!k6!ii2!ii9!imf!ine!iq2@4$1@1$5@1$2#5$0$4$3").     (* [comment removed for export] *)
Definition KEPT_CS : ltac2:(zQ "20!h8!k6@1$0$1") := ltac2:(zQ "60!k6!ii2!ii9!iq8!ine!iq2@4$1@1$5@1$2#5$0$4$3").    (* [comment removed for export] *)
(* [comment removed for export] *)
Definition IHI : Z := 0x131000.
(* [comment removed for export] *)
Definition BUF_LO : Z := -560.
Definition BUF_HI : Z := -480.

(* [comment removed for export] *)
Definition spx : ltac2:(zQ "20!j7!q0>1k$0$1") := ltac2:(zQ "50!j7!itc!iu7!hu6!iue\1k$0@3$2$1@1$4N0@1$3^1").
(* [comment removed for export] *)
Definition srOF_base : ltac2:(zQ "20!h8!q0@1$0$1") := ltac2:(zQ "60!q0!jb!hu6!k1!iue!iv5@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$5-o0@3$1$0@1$2+hgog0@3$1$0@1$2+hgurv8@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$4N2@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@1$3$0").
Definition KEPT_OF : ltac2:(zQ "20!h8!k6@1$0$1") := ltac2:(zQ "30!k6!jb!k1@3$1$0N2@3$1$0N4@3$1$0Nh2@1$2$0").
Definition srB0 : list expr := Eval vm_compute in sr_after_call_j srOF_base KEPT_OF 6.
(* [comment removed for export] *)
Definition OF_STK : Z := 2048.
Definition knB0 : ltac2:(zQ "20!h8!hna@1$0$1") := ltac2:(zQ "h10!hna!jb!iue!ivb!hu6!jg0!jg9!k1!jge!jh6!jhc!ji5!jie!jn3!jnd!job!jqf@3$6$0@3$1$0@2$b@1$2N0+h0@3$1$0@3$5@1$2N0+nvvvogggggg0+ogggggggggg0@3$1$0@2$9@2$3@1$2N0@2$h0-o0$a$a@3$1$0@3$5@1$2N2+nvvvogggggg0+ogggggkgggg0@3$1$0@2$9@2$3@1$4Z+vsgg0+jlgg0@3$1$0@2$c+hggg0+vkgg0@3$1$0@3$8@2$3@1$4Z+hgurl0N4@1$2N5@3$1$0@3$8@2$3@1$4Z$dN8@1$2N1@1$7$0@3$6$0@1$f$e@3$1$0@3$5@1$2N5+1+jvvvvf@1$7$0").
Definition ssB0 : ltac2:(zQ "10!qd$0") := ltac2:(zQ "50!k1!jr6!jrb!js4!jsb@5$1+knin4$4@1$0$2$3Ni7").
Definition rB := Eval vm_compute in run scr0 ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knB0.
(* [comment removed for export] *)
Definition logM1 : ltac2:(zQ "20!h8!jrb@1$0$1") := ltac2:(zQ "70!jrb!jb!hu6!iue!ivb!jt2!k1@3$1$0@3$5@2$4@1$3N0-ii0N1@1$2+i0@3$1$0@3$5@2$4@1$3N0-ii8N8@1$2+mumlngmvignkmvme@3$1$0@3$5@2$4@1$3N0-ij0N8@1$2+mumhmjigjqmpmsm3@1$6$0").
Definition knC0 : list kentry := Eval vm_compute in fst (fst (carry logM1 knB [])).
Definition srC0 : list expr := Eval vm_compute in sr_after_call_j srB KEPT_MC 39.

(* [comment removed for export] *)
Definition ssC0 : ltac2:(zQ "10!qd$0") := ltac2:(zQ "50!k1!jr6!jrb!jt7!jte@5$1+ujms4$4@1$0$2$3Nk7").
Definition rC := Eval vm_compute in run scr0 ssC0.
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC)).
Definition knC : list kentry := Eval vm_compute in kn_after rC knC0.
Definition srD0 : list expr := Eval vm_compute in sr_after_call_j srC KEPT_MC 71.

(* [comment removed for export] *)
Definition ssD0 : ltac2:(zQ "10!qd$0") := ltac2:(zQ "50!k1!jr6!jrb!ju5!jub@5$1+ujms4$4@1$0$2$3Nm7").
Definition rD := Eval vm_compute in run scr0 ssD0.
Definition srD : list expr := Eval vm_compute in s_regs (fst (fst rD)).
Definition knD : list kentry := Eval vm_compute in kn_after rD knC.
(* [comment removed for export] *)
Definition PX : ltac2:(zQ "10!q0$0") := ltac2:(zQ "10!iue@1$0Nn1").
Definition knE0 : ltac2:(zQ "20!h8!hna@1$0$1") := ltac2:(zQ "70!jb!kif!jg0!hna!kj9!kjf!kk4@3$0$3@3$2$5Z+hvvvf@5$1N0-ko0-km0$4$6").
Definition srE0 : list expr := Eval vm_compute in sr_after_call_j srD KEPT_CS 103.

(* [comment removed for export] *)
Definition ssE0 : ltac2:(zQ "10!qd$0") := ltac2:(zQ "50!k1!jr6!jrb!kka!kl1@5$1+ukij4$4@1$0$2$3No7").
Definition scrE : ltac2:(zQ "10!oa$0") := ltac2:(zQ "70!p4!k1!jb!q0!kl8!hu6!pa@3$6@3$2$0$4@1$1$0@3$2$3@1$5Z@1$1$3@1$1$0").
Definition rE := Eval vm_compute in run scrE ssE0.
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
Definition knE : list kentry := Eval vm_compute in kn_after rE knE0.
Definition srF0 : list expr := Eval vm_compute in sr_after_call_j srE KEPT_MC 135.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ssF0 : ltac2:(zQ "10!qd$0") := ltac2:(zQ "50!k1!jr6!jrb!klf!km5@5$1+ujms4$4@1$0$2$3Nq7").
Definition scrF : ltac2:(zQ "10!oa$0") := ltac2:(zQ "60!p4!k1!jb!s4!pa!q0@3$4@3$2$0$3@3$2$0$3@1$1$0@1$1$5@1$1$0").   (* [comment removed for export] *)
Definition rF := Eval vm_compute in run scrF ssF0.
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF)).
Definition knF : list kentry := Eval vm_compute in kn_after rF knE.
Definition knG0 : list kentry := Eval vm_compute in kn_cut 0 (-543) BUF_HI IHI knF.
Definition srG0 : list expr := Eval vm_compute in sr_after_call_j srF KEPT_MC 167.

(* [comment removed for export] *)
Definition ssG0 : ltac2:(zQ "10!qd$0") := ltac2:(zQ "50!k1!jr6!jrb!kmc!kn3@5$1+ujms4$4@1$0$2$3Ns7").
Definition scrG : ltac2:(zQ "10!oa$0") := ltac2:(zQ "60!p4!k1!jb!s4!pa!q0@3$4@3$2$0$3@1$1$0@1$1$5@1$1$0").         (* [comment removed for export] *)
Definition rG := Eval vm_compute in run scrG ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_after rG knG0.
Definition knH0 : list kentry := Eval vm_compute in kn_cut 0 (-543) BUF_HI IHI knG.
Definition srH0 : list expr := Eval vm_compute in sr_after_call_j srG KEPT_MC 199.

(* [comment removed for export] *)
Definition ssH0 : ltac2:(zQ "10!qd$0") := ltac2:(zQ "50!k1!jr6!jrb!kna!ko1@5$1+ujms4$4@1$0$2$3Nu7").
Definition rH := Eval vm_compute in run scr0 ssH0.
Definition srH : list expr := Eval vm_compute in s_regs (fst (fst rH)).
Definition knH : list kentry := Eval vm_compute in kn_after rH knH0.
(* [comment removed for export] *)
Definition scOF : stdio_res := Eval vm_compute in sc_of 231 srH knH.
Definition srI0 : list expr := Eval vm_compute in sc_sr scOF.
Definition knI0 : list kentry := Eval vm_compute in sc_kn scOF.

(* [comment removed for export] *)
Definition ssI0 : ltac2:(zQ "10!qd$0") := ltac2:(zQ "50!k1!jr6!jrb!ko8!kof@5$1+ujrp4$4@1$0$2$3Nhg7").
Definition rI := Eval vm_compute in run scr0 ssI0.
Definition knI : list kentry := Eval vm_compute in kn_after rI knI0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition scrG3 : ltac2:(zQ "10!oa$0") := ltac2:(zQ "60!p4!k1!jb!kl8!pa!q0@3$4@3$2$0$3@1$1$0@1$1$5@1$1$0").   (* [comment removed for export] *)
Definition rG3 := Eval vm_compute in run scrG3 ssG0.
Definition srG3 : list expr := Eval vm_compute in s_regs (fst (fst rG3)).
Definition knG3 : list kentry := Eval vm_compute in kn_after rG3 knG0.
Definition scG3 : stdio_res := Eval vm_compute in sc_of 199 srG3 knG3.
Definition srH30 : list expr := Eval vm_compute in sc_sr scG3.
Definition knH30 : list kentry := Eval vm_compute in sc_kn scG3.
(* [comment removed for export] *)
Definition ssH30 : ltac2:(zQ "10!qd$0") := ltac2:(zQ "70!k1!jr6!jrb!kp6!kq0!kq8!kqf@5$1@1$3$5$6@1$0$2$4Nu7").
Definition rH3 := Eval vm_compute in run scr0 ssH30.
Definition srH3 : list expr := Eval vm_compute in s_regs (fst (fst rH3)).
Definition knH3 : list kentry := Eval vm_compute in kn_after rH3 knH30.
Definition scH3 : stdio_res := Eval vm_compute in sc_of 231 srH3 knH3.
Definition srI30 : list expr := Eval vm_compute in sc_sr scH3.
Definition knI30 : list kentry := Eval vm_compute in sc_kn scH3.
(* [comment removed for export] *)
Definition ssI30 : ltac2:(zQ "10!qd$0") := ltac2:(zQ "50!k1!jr6!jrb!kr7!krf@5$1+ujrp4$4@1$0$2$3Nhg7").
Definition rI3 := Eval vm_compute in run scr0 ssI30.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition scrF4 : ltac2:(zQ "10!oa$0") := ltac2:(zQ "70!p4!k1!jb!kl8!s4!pa!q0@3$5@3$2$0$4@3$2$0$3@1$1$0@1$1$6@1$1$0").  (* [comment removed for export] *)
Definition rF4 := Eval vm_compute in run scrF4 ssF0.
Definition srF4 : list expr := Eval vm_compute in s_regs (fst (fst rF4)).
Definition knF4 : list kentry := Eval vm_compute in kn_after rF4 knE.
Definition scF4 : stdio_res := Eval vm_compute in sc_of 167 srF4 knF4.
Definition srG40 : list expr := Eval vm_compute in sc_sr scF4.
Definition knG40 : list kentry := Eval vm_compute in sc_kn scF4.
(* [comment removed for export] *)
Definition ssG40 : ltac2:(zQ "10!qd$0") := ltac2:(zQ "70!k1!jr6!jrb!kp6!ks7!ksf!kt6@5$1@1$3$5$6@1$0$2$4Ns7").
Definition rG4 := Eval vm_compute in run scr0 ssG40.
Definition srG4 : list expr := Eval vm_compute in s_regs (fst (fst rG4)).
Definition knG4 : list kentry := Eval vm_compute in kn_after rG4 knG40.
(* [comment removed for export] *)
Definition logNL : ltac2:(zQ "20!h8!jrb@1$0$1") := ltac2:(zQ "70!jrb!jb!k1!hu6!iue!ivb!jt2@3$1$0@3$6@2$5@1$4N0-ij0N1@1$3+a@1$2$0").
Definition knH40 : list kentry := Eval vm_compute in fst (fst (carry logNL knG4 [])).
Definition srH40 : list expr := Eval vm_compute in sr_after_call_j srG4 KEPT_MC 199.
(* [comment removed for export] *)
Definition ssH40 : ltac2:(zQ "10!qd$0") := ltac2:(zQ "50!k1!jr6!jrb!kte!ku6@5$1+ujms4$4@1$0$2$3Nu7").
Definition rH4 := Eval vm_compute in run scr0 ssH40.
Definition srH4 : list expr := Eval vm_compute in s_regs (fst (fst rH4)).
Definition knH4 : list kentry := Eval vm_compute in kn_after rH4 knH40.
Definition scH4 : stdio_res := Eval vm_compute in sc_of 231 srH4 knH4.
Definition srI40 : list expr := Eval vm_compute in sc_sr scH4.
Definition knI40 : list kentry := Eval vm_compute in sc_kn scH4.
(* [comment removed for export] *)
Definition ssI40 : ltac2:(zQ "10!qd$0") := ltac2:(zQ "50!k1!jr6!jrb!kue!kv6@5$1+ujrp4$4@1$0$2$3Nhg7").
Definition rI4 := Eval vm_compute in run scr0 ssI40.

Lemma itinerary_63_64 : ltac2:(zQ "jb3!j7!q0!q7!r9!kve!h8!qd!ho3!lh8!lhe!hu6!oa!itc!iu7!iue!ht9!ksf!kq8!k1!li5!lia!lj1!lj8!kjf!ljf!hud!lk5!lkd!ll6!kp6!lle!lm7!hvd!jb!ln0!kl8!s4!ln7!lo1!lo9!lp1!lp7!lpd!lq3!lq9!lqf!lr5!lrb!ls4!lsd!lt4!lta!lu1!lu8!luf!lv6!lvd!mg4!mgb&@4$4$0@1$5$3+uiuu8@1$h2$3&@4$4@2$2$0$0$0@4$4$0$0+ujrp4+vsuu8+2&@4$4$0@1$5$3+ttsm4@1$h2$3@2$9@3$8@2$2$0@1$5$3@4$4$0@1$5$3@1$h4@3$7$6@1$5$3@3$7@2$2$6@1$5$3$b$i9@3$h3$6@1$5$3@3$7@2$2$6@1$5$3$b$i9@4$4$0@1$5$3+uiuu8@3$i1$3@4$i2$i3$i5@3$d$c@3$j2$j0@1$a-1$h7@1$a+jf@1$a+1@1$h2$3@2$9@3$8@1$h9$f@3$i0Ns7$j8$j4@2$h8$f$h1@2$9@3$8@2$2@2$2$0$0$0@4$4@2$2$0$0$0@4$4$0$0@1$hd$h1@1$ha$h1@1$hb$h1@4$4@2$2$0$0$0@4$4$0$0+ujtm4+vsuu8+2@2$9@3$8@2$2@2$2@2$2$1$1$1$1@4$4@2$2@2$2$1$1$1$1@4$4@2$2$1$1$1@4$4$1$1@1$he$h1@1$hf$h1@1$i7$h1@1$hc$h1@4$4@2$2@2$2$1$1$1$1@4$4@2$2$1$1$1@4$4$1$1@3$d$c@1$eN0@1$a-ij0@3$d$c@3$d$c@1$eN0$h7@1$a-ihf@1$a+hjimf@1$a+1@2$9@3$8@2$2$0@1$5$3@4$4$0@1$5$3@1$h4@3$7$6@1$5$3@3$7@2$2$6@1$5$3$b$ib@3$h3$6@1$5$3@3$7@2$2$6@1$5$3$b$ib~0@2$9@3$8@1$h9$f@3$i0Nu7$j9$j5@2$h8$f$h5@2$9@3$8@2$2@2$2$0$0$0@4$4@2$2$0$0$0@4$4$0$0@1$hd$h5@1$ha$h5@1$hb$h5~1@2$9@3$8@2$2@2$2$1$1$1@4$4@2$2$1$1$1@4$4$1$1@1$he$h5@1$hf$h5@1$hc$h5@4$4@2$2$1$1$1@4$4$1$1@3$d$c@1$eN0@1$a-ij0@3$d$c@1$eN0@1$a-ij0@1$aZ@2$9@3$8@2$2$0@1$5$3@4$4$0@1$5$3@1$h4@3$7$6@1$5$3@3$7@2$2$6@1$5$3$b$id@3$h3$6@1$5$3@3$7@2$2$6@1$5$3$b$id~2@2$9@3$8@2$2$0@1$5$3@4$4$0@1$5$3@1$h4@3$7$6@1$5$3@3$7@2$2$6@1$5$3$b$i8@3$h3$6@1$5$3@3$7@2$2$6@1$5$3$b$i8@4$4$0@1$5$3+uiuu8@3$i1$3@4$i2$i3$i5@1$a+jf$h7@3$i1$3@4$i2$i4$if@4$j1$i4N0N4$h7@3$i6$c@3$i6$c$h7@1$aZ@1$aZ@1$h2$3@2$9@3$8@1$h9$f@3$i0Nq7$j7$j3@2$h8$f$h0@2$9@3$8@2$2@2$2$0$0$0@4$4@2$2$0$0$0@4$4$0$0@1$hd$h0@1$ha$h0@1$hb$h0@4$4@2$2$0$0$0@4$4$0$0+ukno4+vsuu8+2@2$9@3$8@2$2@2$2@2$2$1$1$1$1@4$4@2$2@2$2$1$1$1$1@4$4@2$2$1$1$1@4$4$1$1@1$he$h0@1$hf$h0@1$i7$h0@1$hc$h0@4$4@2$2@2$2$1$1$1$1@4$4@2$2$1$1$1@4$4$1$1@3$d$c@1$eN0@1$a-ij0@3$d$c@1$eN0@1$a-ihf@1$eN2$h7@2$9@3$8@2$2$0@1$5$3@4$4$0@1$5$3@1$h4@3$7$6@1$5$3@3$7@2$2$6@1$5$3$b$ia@3$h3$6@1$5$3@3$7@2$2$6@1$5$3$b$ia@4$4$0@1$5$3+uuil0@1$h2$3@2$9@3$8@2$2$0@1$5$3@4$4$0@1$5$3@1$h4@3$7$6@1$5$3@3$7@2$2$6@1$5$3$b$ic@3$h3$6@1$5$3@3$7@2$2$6@1$5$3$b$ic~0@2$9@3$8@1$h9$f@3$i0Nu7$ja$j6@2$h8$f$h6@2$9@3$8@2$2@2$2$0$0$0@4$4@2$2$0$0$0@4$4$0$0@1$hd$h6@1$ha$h6@1$hb$h6~1@2$9@3$8@2$2@2$2$1$1$1@4$4@2$2$1$1$1@4$4$1$1@1$he$h6@1$hf$h6@1$hc$h6@4$4@2$2$1$1$1@4$4$1$1@3$d$c@1$eN0@1$a-ij0@3$d$c@1$eN0@1$a-iif@1$aZ@3$8@2$2$0@1$5$3@4$4$0@1$5$3@1$h4@3$7$6@1$5$3@3$7@2$2$6@1$5$3$b$ie@3$h3$6@1$5$3@3$7@2$2$6@1$5$3$b$ie~2").
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma itinerary_le62 : ltac2:(zQ "j61!r9!h8!j7!q7!qd!ho3!kve!oa!q0!lh8!lhe!hu6!k1!li5!itc!lia!kjf!mh2!jb!iu7!s4!ln0!lo1!iue!kl8!ln7!ht9!mh9!mhe!mi3!mi8!mid!mj2!mj7!mjc!ljf!k6!hud!lrb!mk1!ls4!lsd!lt4!ivb!mka!lk5!lkd!ll6!kp6!lle!lm7!hvd!ml7!mld&@4$6$2@1$1$0+uuil0@1$c$0@2$a@3$9$i4N0N0@2$a@3$9@2$3$2@1$1$0@4$6$2@1$1$0@1$f@3$5$4@1$1$0@3$5@2$3$4@1$1$0$7$hb@3$d$4@1$1$0@3$5@2$3$4@1$1$0$7$hb~0@2$a@3$9@2$3$2@1$1$0@4$6$2@1$1$0@1$f@3$5$4@1$1$0@3$5@2$3$4@1$1$0$7$hc@3$d$4@1$1$0@3$5@2$3$4@1$1$0$7$hc~0@2$a@3$9@2$3$2@1$1$0@4$6$2@1$1$0@1$f@3$5$4@1$1$0@3$5@2$3$4@1$1$0$7$hd@3$d$4@1$1$0@3$5@2$3$4@1$1$0$7$hd@4$6$2@1$1$0+uuunc@1$c$0@2$a@3$9@2$3$2@1$1$0@4$6$2@1$1$0@1$f@3$5$4@1$1$0@3$5@2$3$4@1$1$0$7$he@3$d$4@1$1$0@3$5@2$3$4@1$1$0$7$he@4$6$2@1$1$0+uuil0@3$h2$0@4$h5$h8$i7@3$h6$e$h0@1$bZ$h0@3$h2$0@4$ic@2$ib@3$h3$e@1$h7N2$h0ZN1$h8@1$bZ@1$c$0@2$a@3$9@2$3$2@1$1$0@4$6$2@1$1$0@1$f@3$5$4@1$1$0@3$5@2$3$4@1$1$0$7$hf@3$d$4@1$1$0@3$5@2$3$4@1$1$0$7$hf@4$6$2@1$1$0+uuil0@3$h2$0@4$h5$h4$h9@1$b+jf$h0@3$h2$0@4$h5$h4$i6@4$i9$h4N0N4$h0@3$h6$e@3$h6$e$h0@1$bZ@1$bZ@1$c$0@2$a@3$9@2$3$2@1$1$0@4$6$2@1$1$0@1$f@3$5$4@1$1$0@3$5@2$3$4@1$1$0$7$i0@3$d$4@1$1$0@3$5@2$3$4@1$1$0$7$i0@4$6$2@1$1$0+uuil0@3$h2$0@4$h5$h4$h9@3$h3$e@3$ia$i8@1$b-1$h0@1$b+jf@1$b+1@1$c$0@2$a@3$9@2$3$2@1$1$0@4$6$2@1$1$0@1$f@3$5$4@1$1$0@3$5@2$3$4@1$1$0$7$i1@3$d$4@1$1$0@3$5@2$3$4@1$1$0$7$i1@4$6$2@1$1$0+uiuu8@1$c$0@2$a@3$9@1$i5$ha@3$j3Nu7$j5$j4@2$i3$ha$h1@2$a@3$9@2$3@2$3$2$2$2@4$6@2$3$2$2$2@4$6$2$2@1$j0$h1@1$id$h1@1$ie$h1@4$6@2$3$2$2$2@4$6$2$2+ujrp4+vsuu8+2@2$a@3$9@2$3@2$3$8$8$8@4$6@2$3$8$8$8@4$6$8$8@1$j1$h1@1$j2$h1@1$if$h1@4$6@2$3$8$8$8@4$6$8$8@3$h3$e@1$h7N0@1$b-ij0@3$h3$e@3$h3$e@1$h7N0$h0@1$b-ihe@1$bZ@3$9@2$3$2@1$1$0@4$6$2@1$1$0@1$f@3$5$4@1$1$0@3$5@2$3$4@1$1$0$7$i2@3$d$4@1$1$0@3$5@2$3$4@1$1$0$7$i2@4$6$2@1$1$0+ttsm4@1$c$0").
Proof. vm_compute. repeat split; reflexivity. Qed.
End FPX1.
(* [comment removed for export] *)
