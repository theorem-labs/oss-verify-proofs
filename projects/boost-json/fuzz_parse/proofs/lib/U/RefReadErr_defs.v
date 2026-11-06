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
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list37Corelib7Numbers7BinNumshe1Z04cons03nil03nat79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymExec23SX2~~~~~~kb7scripts04boolkb3SCRkb4expr04prodkb9sym_statekb8sidecond04truekb8sym_exec89OSSVerify6Proofsaboost_jsonafuzz_parse3lib1UfRefReadErr_defs4FPX1~~~~~~t54FUELt55STOPS69OSSVerifyaboost_jsonafuzz_parse6images5Ubsan1M~~~~~~hidfloaded_segmentskb6kentry03fstkb5carrykb5s_log37Corelib5Lists7ListDefhp43maphe4Npos69OSSVerify6Proofsaboost_jsonafuzz_parse3libcRefMemcpyLib~~~~~~hr9bcallee_keptkb4ridx35stdpp9bitvectorbdefinitionsige2bvhr9ccallee_saved3h5LinuxProcessSemantics5Riscv5Instrik17ALU_ADDkb4EAlukb4ELitkb4EVart53spxkb2SAkb6KRange03appkb5KWordkb3KWrt56RE_STKkb6KAlignkb4KImg79OSSVerify6Proofsaboost_jsonafuzz_parse3lib1U9LibDiagKn~~~~~~is56CANARYis5adiag_cellsis58kn_cells46Stdlib6ZArith6BinInt1Zji73subkb2SSkb6sentryt55knRE0t55srRE0kb2SEt54knC0t54srC0t53knCt54srD069OSSVerify6Proofsaboost_jsonafuzz_parse3libaSymDriveH4~~~~~~jo46kn_cutt53IHIt52PXt53knDt54knE0t54srE005falset53knEt54srF0t54knG0t54srG0t54knH0t54srH079OSSVerify6Proofsaboost_jsonafuzz_parse3lib1UcLibStdioCall~~~~~~kha6sc_rett54knI0t54scREt54srI004pair37Corelib4Init5Logicko02eqko03and03sndkb4s_pckb4SCBrkb5EAluwik16BC_GEUkha9stdio_rest52rBt52rCt52rDt52rEt52rFt52rGt52rHt52rI04Some06optionik15BC_GEik15BC_LTik15M_MULkb4EExtkb3EMdkbaSCReadBasekha4sc_fkha5sc_fdkha4sc_lkha5sc_wbkha5sc_wpkhaastdio_callt53knHt53srH" s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition STOPS : ltac2:(zQ "20!h8!j7@1$0$1") := ltac2:(zQ "30!j7!jb!k1@3$1$0+uuil0@3$1$0+uunt0@3$1$0+uuunc@3$1$0+uuhl4@3$1$0+hipk8@3$1$0+hiqt4@3$1$0+uhko8@3$1$0+ttsm4@3$1$0+uiuu8@1$2$0").
Definition FUEL : nat := 5000.
Definition scr0 : ltac2:(zQ "10!oa$0") := ltac2:(zQ "40!k1!p4!pa!q0@3$2@1$0$1@1$0$3@1$0$1").
Definition run : ltac2:(zQ "50!q7!oa!qd!h8!r9>3scr$1>2ss$2@2$0@2$0$2@1$3$4$1") := ltac2:(zQ "90!k1!s4!oa!r9!sa!qd!hhe!hi5!hm3\3scr$2\2ss$5@7$4$8$6$1$7^2^1@1$0$3").
Definition kn_after : ltac2:(zQ "60!h8!q7!hn6!oa!r9!qd>1r@2$1@2$1$5@1$0$4$3>2kn@1$0$2@1$0$2") := ltac2:(zQ "b0!h8!r9!hnf!q7!hn6!qd!p4!oa!k1!ho4!hoc\1r@2$3@2$3$5@1$0$1$7\2kn@1$0$4@3$2@1$0$4@1$0$1@3$2@2$3@1$0$4@1$0$1@1$0$6@3$9@1$a@3$2$5@1$0$1@3$2@2$3$5@1$0$1$7^2^1@1$8$6").
Definition KEPT_MC : ltac2:(zQ "20!h8!k6@1$0$1") := ltac2:(zQ "60!k6!hqb!hr2!hv8!ig7!iib@4$1@1$5@1$2#5$0$4$3").     (* [comment removed for export] *)
Definition KEPT_CS : ltac2:(zQ "20!h8!k6@1$0$1") := ltac2:(zQ "60!k6!hqb!hr2!ij1!ig7!iib@4$1@1$5@1$2#5$0$4$3").    (* [comment removed for export] *)
Definition IHI : Z := 0x131000.
Definition BUF_LO : Z := -560.
Definition BUF_HI : Z := -480.

(* [comment removed for export] *)
Definition spx : ltac2:(zQ "20!j7!q0>1k$0$1") := ltac2:(zQ "50!j7!im5!in0!in7!ine\1k$0@3$2$1@1$4N0@1$3^1").

(* [comment removed for export] *)
Definition srRE_base : ltac2:(zQ "20!h8!q0@1$0$1") := ltac2:(zQ "60!q0!jb!in7!k1!ine!io5@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$5-o0@3$1$0@1$2+hgog0@3$1$0@1$2+hgurv8@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$4N2@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@1$3$0").
Definition KEPT_RE : ltac2:(zQ "20!h8!k6@1$0$1") := ltac2:(zQ "30!k6!jb!k1@3$1$0N2@3$1$0N4@3$1$0Nh2@1$2$0").   (* [comment removed for export] *)
Definition srRE0 : list expr := Eval vm_compute in sr_after_call_j srRE_base KEPT_RE 6.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition RE_STK : Z := 2048.
Definition knRE0 : ltac2:(zQ "20!h8!hn6@1$0$1") := ltac2:(zQ "h10!hn6!jb!ine!iob!in7!ip0!ip9!k1!ipe!iq6!iqc!ir5!ire!jg3!jgd!jhb!jjf@3$6$0@3$1$0@2$b@1$2N0+h0@3$1$0@3$5@1$2N0+nvvvogggggg0+ogggggggggg0@3$1$0@2$9@2$3@1$2N0@2$h0-o0$a$a@3$1$0@3$5@1$2N2+nvvvogggggg0+ogggggkgggg0@3$1$0@2$9@2$3@1$4Z+vsgg0+jlgg0@3$1$0@2$c+hggg0+vkgg0@3$1$0@3$8@2$3@1$4Z+hgurl0N4@1$2N5@3$1$0@3$8@2$3@1$4Z$dN8@1$2N1@1$7$0@3$6$0@1$f$e@3$1$0@3$5@1$2N5+1+jvvvvf@1$7$0").

(* [comment removed for export] *)
Definition ssB0 : ltac2:(zQ "10!qd$0") := ltac2:(zQ "50!k1!jk6!jkb!jl4!jlc@5$1+knih0$4@1$0$2$3Ni7").
Definition rB := Eval vm_compute in run scr0 ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knRE0.
(* [comment removed for export] *)
Definition logM1 : ltac2:(zQ "20!h8!jkb@1$0$1") := ltac2:(zQ "70!jkb!jb!in7!ine!iob!jm4!k1@3$1$0@3$5@2$4@1$3N0-iheN1@1$2+i0@3$1$0@3$5@2$4@1$3N0-ii0N2@1$2+mumf@3$1$0@3$5@2$4@1$3N0-ii8N8@1$2+ignimvninimligm4@3$1$0@3$5@2$4@1$3N0-ij0N8@1$2+mhmlniigjqmpmsm3@1$6$0").
Definition knC0 : list kentry := Eval vm_compute in fst (fst (carry logM1 knB [])).
Definition srC0 : list expr := Eval vm_compute in sr_after_call_j srB KEPT_MC 39.

(* [comment removed for export] *)
Definition ssC0 : ltac2:(zQ "10!qd$0") := ltac2:(zQ "50!k1!jk6!jkb!jm9!jn0@5$1+ujms4$4@1$0$2$3Nk7").
Definition rC := Eval vm_compute in run scr0 ssC0.
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC)).
Definition knC : list kentry := Eval vm_compute in kn_after rC knC0.
Definition srD0 : list expr := Eval vm_compute in sr_after_call_j srC KEPT_MC 71.

(* [comment removed for export] *)
Definition ssD0 : ltac2:(zQ "10!qd$0") := ltac2:(zQ "50!k1!jk6!jkb!jn7!jnd@5$1+ujms4$4@1$0$2$3Nm7").
Definition rD := Eval vm_compute in run scr0 ssD0.
Definition srD : list expr := Eval vm_compute in s_regs (fst (fst rD)).
Definition knD : list kentry := Eval vm_compute in kn_after rD knC.
Definition PX : ltac2:(zQ "10!q0$0") := ltac2:(zQ "10!ine@1$0Nn1").
Definition knE0 : ltac2:(zQ "20!h8!hn6@1$0$1") := ltac2:(zQ "70!jb!js1!ip0!hn6!jsb!jt1!jt6@3$0$3@3$2$5Z+hvvvf@5$1N0-ko0-km0$4$6").
Definition srE0 : list expr := Eval vm_compute in sr_after_call_j srD KEPT_CS 103.

(* [comment removed for export] *)
Definition ssE0 : ltac2:(zQ "10!qd$0") := ltac2:(zQ "50!k1!jk6!jkb!jtc!ju3@5$1+ukij4$4@1$0$2$3No7").
Definition scrE : ltac2:(zQ "10!oa$0") := ltac2:(zQ "70!p4!k1!jb!q0!jua!in7!pa@3$6@3$2$0$4@1$1$0@3$2$3@1$5Z@1$1$3@1$1$0").
Definition rE := Eval vm_compute in run scrE ssE0.
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
Definition knE : list kentry := Eval vm_compute in kn_after rE knE0.
Definition srF0 : list expr := Eval vm_compute in sr_after_call_j srE KEPT_MC 135.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ssF0 : ltac2:(zQ "10!qd$0") := ltac2:(zQ "50!k1!jk6!jkb!jv1!jv7@5$1+ujms4$4@1$0$2$3Nq7").
Definition scrF : ltac2:(zQ "10!oa$0") := ltac2:(zQ "60!p4!k1!jb!s4!pa!q0@3$4@3$2$0$3@3$2$0$3@1$1$0@1$1$5@1$1$0").   (* [comment removed for export] *)
Definition rF := Eval vm_compute in run scrF ssF0.
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF)).
Definition knF : list kentry := Eval vm_compute in kn_after rF knE.
Definition knG0 : list kentry := Eval vm_compute in kn_cut 0 (-541) BUF_HI IHI knF.
Definition srG0 : list expr := Eval vm_compute in sr_after_call_j srF KEPT_MC 167.

(* [comment removed for export] *)
Definition ssG0 : ltac2:(zQ "10!qd$0") := ltac2:(zQ "50!k1!jk6!jkb!jve!kg5@5$1+ujms4$4@1$0$2$3Ns7").
Definition scrG : ltac2:(zQ "10!oa$0") := ltac2:(zQ "60!p4!k1!jb!s4!pa!q0@3$4@3$2$0$3@1$1$0@1$1$5@1$1$0").         (* [comment removed for export] *)
Definition rG := Eval vm_compute in run scrG ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_after rG knG0.
Definition knH0 : list kentry := Eval vm_compute in kn_cut 0 (-541) BUF_HI IHI knG.
Definition srH0 : list expr := Eval vm_compute in sr_after_call_j srG KEPT_MC 199.

(* [comment removed for export] *)
Definition ssH0 : ltac2:(zQ "10!qd$0") := ltac2:(zQ "50!k1!jk6!jkb!kgc!kh3@5$1+ujms4$4@1$0$2$3Nu7").
Definition rH := Eval vm_compute in run scr0 ssH0.
Definition srH : list expr := Eval vm_compute in s_regs (fst (fst rH)).
Definition knH : list kentry := Eval vm_compute in kn_after rH knH0.
(* [comment removed for export] *)
Definition scRE : stdio_res := Eval vm_compute in
  match stdio_call 231 srH knH with Some r => r | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [] end.
Definition srI0 : list expr := Eval vm_compute in sc_sr scRE.
Definition knI0 : list kentry := Eval vm_compute in sc_kn scRE.

(* [comment removed for export] *)
Definition ssI0 : ltac2:(zQ "10!qd$0") := ltac2:(zQ "70!k1!jk6!jkb!klb!km5!kmc!kn3@5$1@1$3$5$6@1$0$2$4Nhg7").
Definition rI := Eval vm_compute in run scr0 ssI0.
Definition knI : list kentry := Eval vm_compute in kn_after rI knI0.

Lemma itinerary_re : ltac2:(zQ "j51!r9!h8!j7!q7!qd!hnf!kna!oa!q0!kp4!in7!kpa!k1!kq1!im5!kq6!jt1!kmc!jb!in0!s4!kqd!kr4!ine!jua!krc!ks6!kt3!kt8!ktd!ku2!ku7!kuc!kv1!kv6!kvb!lg1!lg9!lh2!lhb!li4!lib!iob!lj1!lje!lk6!lkf!klb!ll7!lm0!lm9!ln7!lnd&@4$6$2@1$1$0+uuil0@1$c$0@2$b@3$9@2$3$2@1$1$0@4$6$2@1$1$0@1$f@3$5$4@1$1$0@3$5@2$3$4@1$1$0$7$hb@3$d$4@1$1$0@3$5@2$3$4@1$1$0$7$hb~0@2$b@3$9@2$3$2@1$1$0@4$6$2@1$1$0@1$f@3$5$4@1$1$0@3$5@2$3$4@1$1$0$7$hc@3$d$4@1$1$0@3$5@2$3$4@1$1$0$7$hc~0@2$b@3$9@2$3$2@1$1$0@4$6$2@1$1$0@1$f@3$5$4@1$1$0@3$5@2$3$4@1$1$0$7$hd@3$d$4@1$1$0@3$5@2$3$4@1$1$0$7$hd@4$6$2@1$1$0+uuunc@1$c$0@2$b@3$9@2$3$2@1$1$0@4$6$2@1$1$0@1$f@3$5$4@1$1$0@3$5@2$3$4@1$1$0$7$he@3$d$4@1$1$0@3$5@2$3$4@1$1$0$7$he@4$6$2@1$1$0+uuil0@3$h2$0@4$h5$h8$i6@3$h6$e$h0@1$aZ$h0@3$h2$0@4$ib@2$ia@3$h3$e@1$h7N2$h0ZN1$h8@1$aZ@1$c$0@2$b@3$9@2$3$2@1$1$0@4$6$2@1$1$0@1$f@3$5$4@1$1$0@3$5@2$3$4@1$1$0$7$hf@3$d$4@1$1$0@3$5@2$3$4@1$1$0$7$hf@4$6$2@1$1$0+uuil0@3$h2$0@4$h5$h4$h9@1$a+jd$h0@3$h2$0@4$h5$h4$i5@4$i8$h4N0N4$h0@3$h6$e@3$h6$e$h0@1$aZ@1$aZ@1$c$0@2$b@3$9@2$3$2@1$1$0@4$6$2@1$1$0@1$f@3$5$4@1$1$0@3$5@2$3$4@1$1$0$7$i0@3$d$4@1$1$0@3$5@2$3$4@1$1$0$7$i0@4$6$2@1$1$0+uuil0@3$h2$0@4$h5$h4$h9@3$h3$e@3$i9$i7@1$a-1$h0@1$a+jd@1$a+1@1$c$0@2$b@3$9@2$3$2@1$1$0@4$6$2@1$1$0@1$f@3$5$4@1$1$0@3$5@2$3$4@1$1$0$7$i1@3$d$4@1$1$0@3$5@2$3$4@1$1$0$7$i1@4$6$2@1$1$0+uiuu8@1$c$0@2$b@3$9@1$i4$ha@3$j2Nu7$j4$j3@2$i3$ha$h1@2$b@3$9@2$3@2$3$2$2$2@4$6@2$3$2$2$2@4$6$2$2@1$if$h1@1$ic$h1@1$id$h1@4$6@2$3$2$2$2@4$6$2$2+ujrp4+vsuu8+2@2$b@3$9@2$3@2$3$8$8$8@4$6@2$3$8$8$8@4$6$8$8@1$j0$h1@1$j1$h1@1$ie$h1@4$6@2$3$8$8$8@4$6$8$8@3$h3$e@1$h7N0@1$a-ij0@3$h3$e@3$h3$e@1$h7N0$h0@1$a-ihc@1$aZ@3$9@2$3$2@1$1$0@4$6$2@1$1$0@1$f@3$5$4@1$1$0@3$5@2$3$4@1$1$0$7$i2@3$d$4@1$1$0@3$5@2$3$4@1$1$0$7$i2@4$6$2@1$1$0+ttsm4@1$c$0").
Proof. vm_compute. repeat split; reflexivity. Qed.

End FPX1.
(* [comment removed for export] *)
