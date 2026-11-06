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
  PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib SymDriveH4 LibStdioCall
  RefReadErr_defs.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list03nat04cons03nil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymExec23SX2~~~~~~ie9sym_state69OSSVerify6Proofsaboost_jsonafuzz_parse3libfRefReadErr_defs~~~~~~n95knRE079OSSVerify6Proofsaboost_jsonafuzz_parse3libfRefRefused_defs4FPX1~~~~~~s35srRF0ie2SSie6sentryie4ELitie4EVarie2SAie2SEs34knC0s34srC0s33knCs34srD0s33knDs34srE0s34knF0s34srF0s34knG0s34srG069OSSVerify6Proofsaboost_jsonafuzz_parse3libcLibStdioCall~~~~~~hnc6sc_rets34knH0s34scRFs34srH0ie8sidecond37Corelib7Numbers7BinNumshu51Z04prod04pair03fstie7scriptsie4expr37Corelib4Init5Logicii52eqii53and03sndie4s_pc3h5LinuxProcessSemantics5Riscv5Instril27ALU_ADDhnc9stdio_ress32rBs32rCs32rDs32rEs32rFs32rGs32rHie4EAlu04Some06optionhnc4sc_fhnc5sc_fdhnc4sc_lhnc5sc_wbhnc5sc_wphncastdio_calls33knGs33srG" s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.

(* [comment removed for export] *)
Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition KEPT_RF : ltac2:(zQ "20!h8!he@1$0$1") := ltac2:(zQ "30!he!i3!i9@3$1$0N2@3$1$0N4@1$2$0").
Definition srRF0 : list expr := Eval vm_compute in sr_after_call_j srRE_base KEPT_RF 6.

(* [comment removed for export] *)
Definition ssB0 : ltac2:(zQ "10!md$0") := ltac2:(zQ "50!i9!rb!hga!hh2!hh7@5$3+knmh8$2@1$0$4$1Ni7").
Definition rB := Eval vm_compute in run scr0 ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knRE0.
(* [comment removed for export] *)
Definition logM1 : ltac2:(zQ "20!h8!hh7@1$0$1") := ltac2:(zQ "70!hh7!i3!hi0!hi7!hie!hj3!i9@3$1$0@3$5@2$4@1$3N0-ii4N2@1$2+igjd@3$1$0@3$5@2$4@1$3N0-ii8N4@1$2+juignkn5@3$1$0@3$5@2$4@1$3N0-ij0N8@1$2+ngmumpigjqmpmsm3@1$6$0").
Definition knC0 : list kentry := Eval vm_compute in fst (fst (carry logM1 knB [])).
Definition srC0 : list expr := Eval vm_compute in sr_after_call_j srB KEPT_MC 39.

(* [comment removed for export] *)
Definition ssC0 : ltac2:(zQ "10!md$0") := ltac2:(zQ "50!i9!hj8!hjf!hh2!hh7@5$3+ugihc$2@1$0$4$1Nk7").
Definition rC := Eval vm_compute in run scr0 ssC0.
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC)).
Definition knC : list kentry := Eval vm_compute in kn_after rC knC0.
Definition srD0 : list expr := Eval vm_compute in sr_after_call_j srC KEPT_MC 71.

(* [comment removed for export] *)
Definition ssD0 : ltac2:(zQ "10!md$0") := ltac2:(zQ "50!i9!hk6!hkc!hh2!hh7@5$3+ugihc$2@1$0$4$1Nm7").
Definition rD := Eval vm_compute in run scr0 ssD0.
Definition srD : list expr := Eval vm_compute in s_regs (fst (fst rD)).
Definition knD : list kentry := Eval vm_compute in kn_after rD knC.
Definition srE0 : list expr := Eval vm_compute in sr_after_call_j srD KEPT_MC 103.

(* [comment removed for export] *)
Definition ssE0 : ltac2:(zQ "10!md$0") := ltac2:(zQ "50!i9!hl3!hl9!hh2!hh7@5$3+ugihc$2@1$0$4$1No7").
Definition rE := Eval vm_compute in run scr0 ssE0.
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
Definition knE : list kentry := Eval vm_compute in kn_after rE knD.
(* [comment removed for export] *)
Definition logM4 : ltac2:(zQ "20!h8!hh7@1$0$1") := ltac2:(zQ "70!hh7!i3!i9!hi0!hi7!hie!hj3@3$1$0@3$6@2$5@1$4N0-ii2N8@1$3+jkjmjojojgjhjnj6@1$2$0").
Definition knF0 : list kentry := Eval vm_compute in fst (fst (carry logM4 knE [])).
Definition srF0 : list expr := Eval vm_compute in sr_after_call_j srE KEPT_MC 135.

(* [comment removed for export] *)
Definition ssF0 : ltac2:(zQ "10!md$0") := ltac2:(zQ "50!i9!hm0!hm7!hh2!hh7@5$3+ugihc$2@1$0$4$1Nq7").
Definition rF := Eval vm_compute in run scr0 ssF0.
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF)).
Definition knF : list kentry := Eval vm_compute in kn_after rF knF0.
Definition logM5 : ltac2:(zQ "20!h8!hh7@1$0$1") := ltac2:(zQ "70!hh7!i3!hi0!hi7!hie!hj3!i9@3$1$0@3$5@2$4@1$3N0-ih2N8@1$2+qmkmlnjnlmmmln2@3$1$0@3$5@2$4@1$3N0-ihaN8@1$2+igisnjmlnknpmii0@1$6$0").
Definition knG0 : list kentry := Eval vm_compute in fst (fst (carry logM5 knF [])).
Definition srG0 : list expr := Eval vm_compute in sr_after_call_j srF KEPT_MC 167.

(* [comment removed for export] *)
Definition ssG0 : ltac2:(zQ "10!md$0") := ltac2:(zQ "50!i9!hme!hn5!hh2!hh7@5$3+ugihc$2@1$0$4$1Ns7").
Definition rG := Eval vm_compute in run scr0 ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_after rG knG0.
Definition scRF : stdio_res := Eval vm_compute in
  match stdio_call 199 srG knG with Some r => r | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [] end.
Definition srH0 : list expr := Eval vm_compute in sc_sr scRF.
Definition knH0 : list kentry := Eval vm_compute in sc_kn scRF.

(* [comment removed for export] *)
Definition ssH0 : ltac2:(zQ "10!md$0") := ltac2:(zQ "70!i9!hrb!hs5!hsc!ht3!hh2!hh7@5$5@1$1$3$4@1$0$6$2Nu7").
Definition rH := Eval vm_compute in run scr0 ssH0.
Definition knH : list kentry := Eval vm_compute in kn_after rH knH0.

Lemma itinerary_rf : ltac2:(zQ "i61!hta!h8!hve!ig3!md!ig9!igf!ih4!ihe!ij9!ijf!i9!ik6!hsc!ikb!hi0!in6!io1!ioe!ip3!ip8!ipd!iq2!iq7!iqc!ir1!hi7!ir8!ire!is6!ise!it7!hrb!itf!iu8!iv1!ivf!jg5&@4$5$2@1$1$0+uqtq8@1$b$0@2$a@3$9@2$3$2@1$1$0@4$5$2@1$1$0@1$e@3$6$4@1$1$0@3$6@2$3$4@1$1$0$7$h2@3$c$4@1$1$0@3$6@2$3$4@1$1$0$7$h2~0@2$a@3$9@2$3$2@1$1$0@4$5$2@1$1$0@1$e@3$6$4@1$1$0@3$6@2$3$4@1$1$0$7$h3@3$c$4@1$1$0@3$6@2$3$4@1$1$0$7$h3~0@2$a@3$9@2$3$2@1$1$0@4$5$2@1$1$0@1$e@3$6$4@1$1$0@3$6@2$3$4@1$1$0$7$h4@3$c$4@1$1$0@3$6@2$3$4@1$1$0$7$h4~0@2$a@3$9@2$3$2@1$1$0@4$5$2@1$1$0@1$e@3$6$4@1$1$0@3$6@2$3$4@1$1$0$7$h5@3$c$4@1$1$0@3$6@2$3$4@1$1$0$7$h5~0@2$a@3$9@2$3$2@1$1$0@4$5$2@1$1$0@1$e@3$6$4@1$1$0@3$6@2$3$4@1$1$0$7$h6@3$c$4@1$1$0@3$6@2$3$4@1$1$0$7$h6~0@2$a@3$9@2$3$2@1$1$0@4$5$2@1$1$0@1$e@3$6$4@1$1$0@3$6@2$3$4@1$1$0$7$h7@3$c$4@1$1$0@3$6@2$3$4@1$1$0$7$h7@4$5$2@1$1$0+tvqk0@1$b$0@2$a@3$9@1$hc$h1@3$i3Ns7$i5$i4@2$hb$h1$d@2$a@3$9@2$3@2$3$2$2$2@4$5@2$3$2$2$2@4$5$2$2@1$i0$d@1$hd$d@1$he$d@4$5@2$3$2$2$2@4$5$2$2+ugmuc+vppq8+2@2$a@3$9@2$3@2$3$8$8$8@4$5@2$3$8$8$8@4$5$8$8@1$i1$d@1$i2$d@1$hf$d@4$5@2$3$8$8$8@4$5$8$8@3$h9$h0@1$haN0@1$f-ij0@3$h9$h0@1$haN0@1$f-iga@1$fZ@3$9@2$3$2@1$1$0@4$5$2@1$1$0@1$e@3$6$4@1$1$0@3$6@2$3$4@1$1$0$7$h8@3$c$4@1$1$0@3$6@2$3$4@1$1$0$7$h8@4$5$2@1$1$0+tqnrc@1$b$0").
Proof. vm_compute. repeat split; reflexivity. Qed.
End FPX1.
(* [comment removed for export] *)
