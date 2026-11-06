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
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.U Require Import LibStdioCall RefReadErr_defs.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list03nat04cons03nil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymExec23SX2~~~~~~ie9sym_stateie2SSie6sentry79OSSVerify6Proofsaboost_jsonafuzz_parse3lib1UfRefReadErr_defs~~~~~~o75knRE089OSSVerify6Proofsaboost_jsonafuzz_parse3lib1UfRefRefused_defs4FPX1~~~~~~t35srRF0ie4ELitie4EVarie2SAie2SEt34knC0t34srC0t33knCt34srD0t33knDt34srE0t34knF0t34srF0t34knG0t34srG079OSSVerify6Proofsaboost_jsonafuzz_parse3lib1UcLibStdioCall~~~~~~ho06sc_rett34knH0t34scRFt34srH0ie8sidecond37Corelib7Numbers7BinNumshub1Z04prod04pair03fstie7scriptsie4expr37Corelib4Init5Logiciib2eqiib3and03sndie4s_pc3h5LinuxProcessSemantics5Riscv5Instril87ALU_ADDie4EAluho09stdio_rest32rBt32rCt32rDt32rEt32rFt32rGt32rH04Some06optionho04sc_fho05sc_fdho04sc_lho05sc_wbho05sc_wpho0astdio_callt33knGt33srG" s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.

(* [comment removed for export] *)
Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition KEPT_RF : ltac2:(zQ "20!h8!he@1$0$1") := ltac2:(zQ "30!he!i3!i9@3$1$0N2@3$1$0N4@1$2$0").
Definition srRF0 : list expr := Eval vm_compute in sr_after_call_j srRE_base KEPT_RF 6.

(* [comment removed for export] *)
Definition ssB0 : ltac2:(zQ "10!md$0") := ltac2:(zQ "50!i9!n9!ne!sb!hhc@5$1+kniic$4@1$0$2$3Ni7").
Definition rB := Eval vm_compute in run scr0 ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knRE0.
(* [comment removed for export] *)
Definition logM1 : ltac2:(zQ "20!h8!ne@1$0$1") := ltac2:(zQ "70!ne!i3!hi4!hib!hj2!hj7!i9@3$1$0@3$5@2$4@1$3N0-ii4N2@1$2+igjd@3$1$0@3$5@2$4@1$3N0-ii8N4@1$2+juignkn5@3$1$0@3$5@2$4@1$3N0-ij0N8@1$2+ngmumpigjqmpmsm3@1$6$0").
Definition knC0 : list kentry := Eval vm_compute in fst (fst (carry logM1 knB [])).
Definition srC0 : list expr := Eval vm_compute in sr_after_call_j srB KEPT_MC 39.

(* [comment removed for export] *)
Definition ssC0 : ltac2:(zQ "10!md$0") := ltac2:(zQ "50!i9!n9!ne!hjc!hk3@5$1+ujms4$4@1$0$2$3Nk7").
Definition rC := Eval vm_compute in run scr0 ssC0.
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC)).
Definition knC : list kentry := Eval vm_compute in kn_after rC knC0.
Definition srD0 : list expr := Eval vm_compute in sr_after_call_j srC KEPT_MC 71.

(* [comment removed for export] *)
Definition ssD0 : ltac2:(zQ "10!md$0") := ltac2:(zQ "50!i9!n9!ne!hka!hl0@5$1+ujms4$4@1$0$2$3Nm7").
Definition rD := Eval vm_compute in run scr0 ssD0.
Definition srD : list expr := Eval vm_compute in s_regs (fst (fst rD)).
Definition knD : list kentry := Eval vm_compute in kn_after rD knC.
Definition srE0 : list expr := Eval vm_compute in sr_after_call_j srD KEPT_MC 103.

(* [comment removed for export] *)
Definition ssE0 : ltac2:(zQ "10!md$0") := ltac2:(zQ "50!i9!n9!ne!hl7!hld@5$1+ujms4$4@1$0$2$3No7").
Definition rE := Eval vm_compute in run scr0 ssE0.
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
Definition knE : list kentry := Eval vm_compute in kn_after rE knD.
(* [comment removed for export] *)
Definition logM4 : ltac2:(zQ "20!h8!ne@1$0$1") := ltac2:(zQ "70!ne!i3!i9!hi4!hib!hj2!hj7@3$1$0@3$6@2$5@1$4N0-ii2N8@1$3+jkjmjojojgjhjnj6@1$2$0").
Definition knF0 : list kentry := Eval vm_compute in fst (fst (carry logM4 knE [])).
Definition srF0 : list expr := Eval vm_compute in sr_after_call_j srE KEPT_MC 135.

(* [comment removed for export] *)
Definition ssF0 : ltac2:(zQ "10!md$0") := ltac2:(zQ "50!i9!n9!ne!hm4!hmb@5$1+ujms4$4@1$0$2$3Nq7").
Definition rF := Eval vm_compute in run scr0 ssF0.
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF)).
Definition knF : list kentry := Eval vm_compute in kn_after rF knF0.
Definition logM5 : ltac2:(zQ "20!h8!ne@1$0$1") := ltac2:(zQ "70!ne!i3!hi4!hib!hj2!hj7!i9@3$1$0@3$5@2$4@1$3N0-ih2N8@1$2+qmkmlnjnlmmmln2@3$1$0@3$5@2$4@1$3N0-ihaN8@1$2+igisnjmlnknpmii0@1$6$0").
Definition knG0 : list kentry := Eval vm_compute in fst (fst (carry logM5 knF [])).
Definition srG0 : list expr := Eval vm_compute in sr_after_call_j srF KEPT_MC 167.

(* [comment removed for export] *)
Definition ssG0 : ltac2:(zQ "10!md$0") := ltac2:(zQ "50!i9!n9!ne!hn2!hn9@5$1+ujms4$4@1$0$2$3Ns7").
Definition rG := Eval vm_compute in run scr0 ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_after rG knG0.
Definition scRF : stdio_res := Eval vm_compute in
  match stdio_call 199 srG knG with Some r => r | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [] end.
Definition srH0 : list expr := Eval vm_compute in sc_sr scRF.
Definition knH0 : list kentry := Eval vm_compute in sc_kn scRF.

(* [comment removed for export] *)
Definition ssH0 : ltac2:(zQ "10!md$0") := ltac2:(zQ "70!i9!n9!ne!hs1!hsb!ht2!ht9@5$1@1$3$5$6@1$0$2$4Nu7").
Definition rH := Eval vm_compute in run scr0 ssH0.
Definition knH : list kentry := Eval vm_compute in kn_after rH knH0.

Lemma itinerary_rf : ltac2:(zQ "i61!hu0!h8!ig4!ig9!md!igf!ih5!iha!ii4!ijf!ik5!i9!ikc!il1!ht2!hi4!inc!io7!hib!ioe!ipb!iq0!iq5!iqa!iqf!ir4!ir9!ire!is4!isc!it4!itd!hs1!iu5!iue!iv7!jg5!jgb&@4$5$2@1$1$0+uuil0@1$b$0@2$a@3$9@2$3$2@1$1$0@4$5$2@1$1$0@1$d@3$6$4@1$1$0@3$6@2$3$4@1$1$0$7$h4@3$c$4@1$1$0@3$6@2$3$4@1$1$0$7$h4~0@2$a@3$9@2$3$2@1$1$0@4$5$2@1$1$0@1$d@3$6$4@1$1$0@3$6@2$3$4@1$1$0$7$h5@3$c$4@1$1$0@3$6@2$3$4@1$1$0$7$h5~0@2$a@3$9@2$3$2@1$1$0@4$5$2@1$1$0@1$d@3$6$4@1$1$0@3$6@2$3$4@1$1$0$7$h6@3$c$4@1$1$0@3$6@2$3$4@1$1$0$7$h6~0@2$a@3$9@2$3$2@1$1$0@4$5$2@1$1$0@1$d@3$6$4@1$1$0@3$6@2$3$4@1$1$0$7$h7@3$c$4@1$1$0@3$6@2$3$4@1$1$0$7$h7~0@2$a@3$9@2$3$2@1$1$0@4$5$2@1$1$0@1$d@3$6$4@1$1$0@3$6@2$3$4@1$1$0$7$h8@3$c$4@1$1$0@3$6@2$3$4@1$1$0$7$h8~0@2$a@3$9@2$3$2@1$1$0@4$5$2@1$1$0@1$d@3$6$4@1$1$0@3$6@2$3$4@1$1$0$7$h9@3$c$4@1$1$0@3$6@2$3$4@1$1$0$7$h9@4$5$2@1$1$0+uiuu8@1$b$0@2$a@3$9@1$hc$h3@3$i3Ns7$i5$i4@2$hb$h3$e@2$a@3$9@2$3@2$3$2$2$2@4$5@2$3$2$2$2@4$5$2$2@1$i0$e@1$hd$e@1$he$e@4$5@2$3$2$2$2@4$5$2$2+ujrp4+vsuu8+2@2$a@3$9@2$3@2$3$8$8$8@4$5@2$3$8$8$8@4$5$8$8@1$i1$e@1$i2$e@1$hf$e@4$5@2$3$8$8$8@4$5$8$8@3$h1$h0@1$h2N0@1$f-ij0@3$h1$h0@1$h2N0@1$f-iga@1$fZ@3$9@2$3$2@1$1$0@4$5$2@1$1$0@1$d@3$6$4@1$1$0@3$6@2$3$4@1$1$0$7$ha@3$c$4@1$1$0@3$6@2$3$4@1$1$0$7$ha@4$5$2@1$1$0+ttsm4@1$b$0").
Proof. vm_compute. repeat split; reflexivity. Qed.
End FPX1.
(* [comment removed for export] *)
