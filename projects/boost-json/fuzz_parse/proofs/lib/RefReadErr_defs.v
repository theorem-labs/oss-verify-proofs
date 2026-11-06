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
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list37Corelib7Numbers7BinNumshe1Z04cons03nil03nat79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymExec23SX2~~~~~~kb7scripts04boolkb3SCRkb4expr04prodkb9sym_statekb8sidecond04true79OSSVerify6Proofsaboost_jsonafuzz_parse3libfRefReadErr_defs4FPX1~~~~~~sa4FUELsa5STOPSkb8sym_exec69OSSVerifyaboost_jsonafuzz_parse6images5Plain1M~~~~~~hibfloaded_segmentskb6kentry03fstkb5carrykb5s_log37Corelib5Lists7ListDefhp23maphe4Npos69OSSVerify6Proofsaboost_jsonafuzz_parse3libcRefMemcpyLib~~~~~~hr7bcallee_keptkb4ridx35stdpp9bitvectorbdefinitionsigc2bvhr7ccallee_saved3h5LinuxProcessSemantics5Riscv5Instrijf7ALU_ADDkb4EAlukb4ELitkb4EVarsa3spxkb2SAkb6KRange03appsa6RE_STKkb5KWordkb3KWr69OSSVerify6Proofsaboost_jsonafuzz_parse3lib9LibDiagKn~~~~~~ir36CANARYir3adiag_cellsir38kn_cellskb6KAlignkb4KImg46Stdlib6ZArith6BinInt1Zji33subsa5knRE0sa5srRE0kb2SSkb6sentrykb2SEsa4knC0sa4srC0sa3knCsa4srD0sa3IHIsa2PXsa3knD69OSSVerify6Proofsaboost_jsonafuzz_parse3libaSymDriveH4~~~~~~jp16kn_cutsa4knE0sa4srE005falsesa3knEsa4srF0sa4knG0sa4srG0sa4knH0sa4srH069OSSVerify6Proofsaboost_jsonafuzz_parse3libcLibStdioCall~~~~~~kh66sc_retsa4knI0sa4scREsa4srI004pair37Corelib4Init5Logickna2eqkna3and03sndkb4s_pckb4SCBrkb5EAluwijf6BC_GEUkh69stdio_ressa2rBsa2rCsa2rDsa2rEsa2rFsa2rGsa2rHsa2rI04Some06optionijf5BC_GEijf5BC_LTijf5M_MULkh64sc_fkh65sc_fdkh64sc_lkh65sc_wbkh65sc_wpkh6astdio_callsa3knHsa3srHkb4EExtkb3EMdkbaSCReadBase" s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.

Abbreviation RSEGS := Plain.M.loaded_segments.

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition STOPS : ltac2:(zQ "20!h8!j7@1$0$1") := ltac2:(zQ "30!j7!jb!k1@3$1$0+uqtq8@3$1$0+urji8@3$1$0+urpt4@3$1$0+uqsqc@3$1$0+hipk8@3$1$0+hiqt4@3$1$0+ttvu0@3$1$0+tqnrc@3$1$0+tvqk0@1$2$0").
Definition FUEL : nat := 5000.
Definition scr0 : ltac2:(zQ "10!oa$0") := ltac2:(zQ "40!k1!p4!pa!q0@3$2@1$0$1@1$0$3@1$0$1").
Definition run : ltac2:(zQ "50!q7!oa!qd!h8!r9>3scr$1>2ss$2@2$0@2$0$2@1$3$4$1") := ltac2:(zQ "90!k1!s4!hh1!hh8!oa!r9!hi0!qd!hm1\3scr$4\2ss$7@7$6$8$2$1$3^2^1@1$0$5").
Definition kn_after : ltac2:(zQ "60!h8!q7!hn4!oa!r9!qd>1r@2$1@2$1$5@1$0$4$3>2kn@1$0$2@1$0$2") := ltac2:(zQ "b0!h8!r9!hnd!q7!hn4!qd!p4!oa!k1!ho2!hoa\1r@2$3@2$3$5@1$0$1$7\2kn@1$0$4@3$2@1$0$4@1$0$1@3$2@2$3@1$0$4@1$0$1@1$0$6@3$9@1$a@3$2$5@1$0$1@3$2@2$3$5@1$0$1$7^2^1@1$8$6").
Definition KEPT_MC : ltac2:(zQ "20!h8!k6@1$0$1") := ltac2:(zQ "60!k6!hq9!hr0!hv6!ig5!ii9@4$1@1$5@1$2#5$0$4$3").     (* [comment removed for export] *)
Definition KEPT_CS : ltac2:(zQ "20!h8!k6@1$0$1") := ltac2:(zQ "60!k6!hq9!hr0!iif!ig5!ii9@4$1@1$5@1$2#5$0$4$3").    (* [comment removed for export] *)
Definition IHI : Z := 0x12d000.
Definition BUF_LO : Z := -560.
Definition BUF_HI : Z := -480.

(* [comment removed for export] *)
Definition spx : ltac2:(zQ "20!j7!q0>1k$0$1") := ltac2:(zQ "50!j7!im3!ime!in5!inc\1k$0@3$2$1@1$4N0@1$3^1").

(* [comment removed for export] *)
Definition srRE_base : ltac2:(zQ "20!h8!q0@1$0$1") := ltac2:(zQ "60!q0!jb!in5!k1!io3!inc@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$4-o0@3$1$0@1$2+hgog0@3$1$0@1$2+hgrmr8@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$5N2@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@1$3$0").
Definition KEPT_RE : ltac2:(zQ "20!h8!k6@1$0$1") := ltac2:(zQ "30!k6!jb!k1@3$1$0N2@3$1$0N4@3$1$0Nh2@1$2$0").   (* [comment removed for export] *)
Definition srRE0 : list expr := Eval vm_compute in sr_after_call_j srRE_base KEPT_RE 6.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition RE_STK : Z := 2048.
Definition knRE0 : ltac2:(zQ "20!h8!hn4@1$0$1") := ltac2:(zQ "h10!hn4!jb!inc!io9!in5!ioe!ip7!k1!ipc!iq5!iqd!iuf!iv9!jg7!jh3!jhc!jjb@3$6$0@3$1$0@2$e@1$2N0+h0@3$1$0@3$5@1$2N0+nvvvogggggg0+ogggggggggg0@3$1$0@2$a@2$3@1$2N0@2$h0-o0$8$8@3$1$0@3$5@1$2N2+nvvvogggggg0+ogggggkgggg0@3$1$0@2$a@2$3@1$4Z+vpgg0+jkgg0@3$1$0@2$f+hggg0+vhgg0@3$1$0@3$9@2$3@1$4Z+hgrmh0N4@1$2N5@3$1$0@3$9@2$3@1$4Z$bN8@1$2N1@1$7$0@3$6$0@1$d$c@3$1$0@3$5@1$2N5+1+jvvvvf@1$7$0").

(* [comment removed for export] *)
Definition ssB0 : ltac2:(zQ "10!qd$0") := ltac2:(zQ "50!k1!jk2!jka!jl2!jl7@5$3+knlvc$2@1$0$4$1Ni7").
Definition rB := Eval vm_compute in run scr0 ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knRE0.
(* [comment removed for export] *)
Definition logM1 : ltac2:(zQ "20!h8!jl7@1$0$1") := ltac2:(zQ "70!jl7!jb!in5!inc!io9!jm0!k1@3$1$0@3$5@2$4@1$3N0-iheN1@1$2+i0@3$1$0@3$5@2$4@1$3N0-ii0N2@1$2+mumf@3$1$0@3$5@2$4@1$3N0-ii8N8@1$2+ignimvninimligm4@3$1$0@3$5@2$4@1$3N0-ij0N8@1$2+mhmlniigjqmpmsm3@1$6$0").
Definition knC0 : list kentry := Eval vm_compute in fst (fst (carry logM1 knB [])).
Definition srC0 : list expr := Eval vm_compute in sr_after_call_j srB KEPT_MC 39.

(* [comment removed for export] *)
Definition ssC0 : ltac2:(zQ "10!qd$0") := ltac2:(zQ "50!k1!jm5!jmc!jl2!jl7@5$3+ugihc$2@1$0$4$1Nk7").
Definition rC := Eval vm_compute in run scr0 ssC0.
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC)).
Definition knC : list kentry := Eval vm_compute in kn_after rC knC0.
Definition srD0 : list expr := Eval vm_compute in sr_after_call_j srC KEPT_MC 71.

(* [comment removed for export] *)
Definition ssD0 : ltac2:(zQ "10!qd$0") := ltac2:(zQ "50!k1!jn3!jn9!jl2!jl7@5$3+ugihc$2@1$0$4$1Nm7").
Definition rD := Eval vm_compute in run scr0 ssD0.
Definition srD : list expr := Eval vm_compute in s_regs (fst (fst rD)).
Definition knD : list kentry := Eval vm_compute in kn_after rD knC.
Definition PX : ltac2:(zQ "10!q0$0") := ltac2:(zQ "10!inc@1$0Nn1").
Definition knE0 : ltac2:(zQ "20!h8!hn4@1$0$1") := ltac2:(zQ "70!jb!jo0!jo6!job!jse!ioe!hn4@3$0$6@3$5$2Z+hvvvf@5$4N0-ko0-km0$1$3").
Definition srE0 : list expr := Eval vm_compute in sr_after_call_j srD KEPT_CS 103.

(* [comment removed for export] *)
Definition ssE0 : ltac2:(zQ "10!qd$0") := ltac2:(zQ "50!k1!jt8!jtf!jl2!jl7@5$3+ugtoc$2@1$0$4$1No7").
Definition scrE : ltac2:(zQ "10!oa$0") := ltac2:(zQ "70!p4!k1!jb!q0!ju6!in5!pa@3$6@3$2$0$4@1$1$0@3$2$3@1$5Z@1$1$3@1$1$0").
Definition rE := Eval vm_compute in run scrE ssE0.
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
Definition knE : list kentry := Eval vm_compute in kn_after rE knE0.
Definition srF0 : list expr := Eval vm_compute in sr_after_call_j srE KEPT_MC 135.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ssF0 : ltac2:(zQ "10!qd$0") := ltac2:(zQ "50!k1!jud!jv3!jl2!jl7@5$3+ugihc$2@1$0$4$1Nq7").
Definition scrF : ltac2:(zQ "10!oa$0") := ltac2:(zQ "60!p4!k1!jb!s4!pa!q0@3$4@3$2$0$3@3$2$0$3@1$1$0@1$1$5@1$1$0").   (* [comment removed for export] *)
Definition rF := Eval vm_compute in run scrF ssF0.
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF)).
Definition knF : list kentry := Eval vm_compute in kn_after rF knE.
Definition knG0 : list kentry := Eval vm_compute in kn_cut 0 (-541) BUF_HI IHI knF.
Definition srG0 : list expr := Eval vm_compute in sr_after_call_j srF KEPT_MC 167.

(* [comment removed for export] *)
Definition ssG0 : ltac2:(zQ "10!qd$0") := ltac2:(zQ "50!k1!jva!kg1!jl2!jl7@5$3+ugihc$2@1$0$4$1Ns7").
Definition scrG : ltac2:(zQ "10!oa$0") := ltac2:(zQ "60!p4!k1!jb!s4!pa!q0@3$4@3$2$0$3@1$1$0@1$1$5@1$1$0").         (* [comment removed for export] *)
Definition rG := Eval vm_compute in run scrG ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_after rG knG0.
Definition knH0 : list kentry := Eval vm_compute in kn_cut 0 (-541) BUF_HI IHI knG.
Definition srH0 : list expr := Eval vm_compute in sr_after_call_j srG KEPT_MC 199.

(* [comment removed for export] *)
Definition ssH0 : ltac2:(zQ "10!qd$0") := ltac2:(zQ "50!k1!kg8!kgf!jl2!jl7@5$3+ugihc$2@1$0$4$1Nu7").
Definition rH := Eval vm_compute in run scr0 ssH0.
Definition srH : list expr := Eval vm_compute in s_regs (fst (fst rH)).
Definition knH : list kentry := Eval vm_compute in kn_after rH knH0.
(* [comment removed for export] *)
Definition scRE : stdio_res := Eval vm_compute in
  match stdio_call 231 srH knH with Some r => r | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [] end.
Definition srI0 : list expr := Eval vm_compute in sc_sr scRE.
Definition knI0 : list kentry := Eval vm_compute in sc_kn scRE.

(* [comment removed for export] *)
Definition ssI0 : ltac2:(zQ "10!qd$0") := ltac2:(zQ "70!k1!kl5!klf!km6!kmd!jl2!jl7@5$5@1$1$3$4@1$0$6$2Nhg7").
Definition rI := Eval vm_compute in run scr0 ssI0.
Definition knI : list kentry := Eval vm_compute in kn_after rI knI0.

Lemma itinerary_re : ltac2:(zQ "j51!r9!h8!j7!q7!qd!hnd!kn4!oa!q0!koe!in5!kp4!k1!kpb!im3!jo6!kq0!km6!jb!ime!s4!kq7!kqe!inc!ju6!kr6!ks0!ksd!kt2!kt7!ktc!ku1!ku6!kub!kv0!kv5!kvb!lg3!lgc!lh5!lhe!li6!lif!kl5!lj7!lk0!lk9!ll7!lld!lm3!lma!io9!ln0&@4$6$2@1$1$0+uqtq8@1$c$0@2$b@3$9@2$3$2@1$1$0@4$6$2@1$1$0@1$h0@3$5$4@1$1$0@3$5@2$3$4@1$1$0$7$hb@3$d$4@1$1$0@3$5@2$3$4@1$1$0$7$hb~0@2$b@3$9@2$3$2@1$1$0@4$6$2@1$1$0@1$h0@3$5$4@1$1$0@3$5@2$3$4@1$1$0$7$hc@3$d$4@1$1$0@3$5@2$3$4@1$1$0$7$hc~0@2$b@3$9@2$3$2@1$1$0@4$6$2@1$1$0@1$h0@3$5$4@1$1$0@3$5@2$3$4@1$1$0$7$hd@3$d$4@1$1$0@3$5@2$3$4@1$1$0$7$hd@4$6$2@1$1$0+urpt4@1$c$0@2$b@3$9@2$3$2@1$1$0@4$6$2@1$1$0@1$h0@3$5$4@1$1$0@3$5@2$3$4@1$1$0$7$he@3$d$4@1$1$0@3$5@2$3$4@1$1$0$7$he@4$6$2@1$1$0+uqtq8@3$h2$0@4$h5$h8$i6@3$h6$e$f@1$aZ$f@3$h2$0@4$j4@2$j3@3$h3$e@1$h7N2$fZN1$h8@1$aZ@1$c$0@2$b@3$9@2$3$2@1$1$0@4$6$2@1$1$0@1$h0@3$5$4@1$1$0@3$5@2$3$4@1$1$0$7$hf@3$d$4@1$1$0@3$5@2$3$4@1$1$0$7$hf@4$6$2@1$1$0+uqtq8@3$h2$0@4$h5$h4$h9@1$a+jd$f@3$h2$0@4$h5$h4$i5@4$j1$h4N0N4$f@3$h6$e@3$h6$e$f@1$aZ@1$aZ@1$c$0@2$b@3$9@2$3$2@1$1$0@4$6$2@1$1$0@1$h0@3$5$4@1$1$0@3$5@2$3$4@1$1$0$7$i0@3$d$4@1$1$0@3$5@2$3$4@1$1$0$7$i0@4$6$2@1$1$0+uqtq8@3$h2$0@4$h5$h4$h9@3$h3$e@3$j2$i7@1$a-1$f@1$a+jd@1$a+1@1$c$0@2$b@3$9@2$3$2@1$1$0@4$6$2@1$1$0@1$h0@3$5$4@1$1$0@3$5@2$3$4@1$1$0$7$i1@3$d$4@1$1$0@3$5@2$3$4@1$1$0$7$i1@4$6$2@1$1$0+tvqk0@1$c$0@2$b@3$9@1$i4$ha@3$ieNu7$j0$if@2$i3$ha$h1@2$b@3$9@2$3@2$3$2$2$2@4$6@2$3$2$2$2@4$6$2$2@1$ib$h1@1$i8$h1@1$i9$h1@4$6@2$3$2$2$2@4$6$2$2+ugmuc+vppq8+2@2$b@3$9@2$3@2$3$8$8$8@4$6@2$3$8$8$8@4$6$8$8@1$ic$h1@1$id$h1@1$ia$h1@4$6@2$3$8$8$8@4$6$8$8@3$h3$e@1$h7N0@1$a-ij0@3$h3$e@3$h3$e@1$h7N0$f@1$a-ihc@1$aZ@3$9@2$3$2@1$1$0@4$6$2@1$1$0@1$h0@3$5$4@1$1$0@3$5@2$3$4@1$1$0$7$i2@3$d$4@1$1$0@3$5@2$3$4@1$1$0$7$i2@4$6$2@1$1$0+tqnrc@1$c$0").
Proof. vm_compute. repeat split; reflexivity. Qed.

End FPX1.
(* [comment removed for export] *)
