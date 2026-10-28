(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX MemcpyLib SymDriveH4.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_main_entry U_stdio_call U_stdio_readerr_defs.
Import ListNotations. Import SX2. Import SX2S.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_stdio_refused_defs () : Init.string Init.list := ["Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.sentry"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.SE"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.SA"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.EVar"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.ELit"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_call.SCR_"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.EAlu"; "LinuxProcessSemantics.Riscv.Instr.ALU_ADD"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.expr"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.kentry"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KWord"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KAlign"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KRange"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KWr"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KImg"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.sidecond"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.s_pc"; "Corelib.Init.Datatypes.fst"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.sym_state"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.scripts"; "rB"; "Corelib.Init.Datatypes.snd"; "rC"; "rD"; "rE"; "rF"; "rG"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_call.stdio_res"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_call.stdio_call"; "srG"; "knG"; "Corelib.Init.Datatypes.Some"; "scRF"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_call.sc_ret"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_call.sc_f"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_call.sc_fd"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_call.sc_wb"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_call.sc_wp"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_call.sc_l"; "rH"].

#[local] Existing Instance PropExec.fx0.

(* [comment removed for export] *)
Definition KEPT_RF : list nat := [2; 3; 4]%nat.
Definition srRF0 : list expr := Eval vm_compute in sr_after_call_j srRE_base KEPT_RF 6.

(* [comment removed for export] *)
Definition ssB0 : sym_state := SS 0x1d494 srRF0 [] knRE0 39.
Definition rB := Eval vm_compute in run scr0 ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knRE0.
(* [comment removed for export] *)
Definition logM1 : list sentry := ltac2:(CDefT.buildp (gd_tbl_P_stdio_refused_defs ()) "(0.$1.(2.(3.(4.#0.)-224.)#2.(5.+203=.))(0.$1.(2.(3.(4.#0.)-228.)#4.(5.+3>207475.))(0.$1.(2.(3.(4.#0.)-230.)#8.(5.+706>69203:696<63.))(6.$1.))))")
(* [comment removed for export] *).
Definition knC0 : list kentry := Eval vm_compute in fst (fst (carry logM1 knB [])).
Definition srC0 : list expr := Eval vm_compute in sr_after_call_j srB KEPT_MC 39.

(* [comment removed for export] *)
Definition ssC0 : sym_state := SS 0x41d64 srC0 [] knC0 71.
Definition rC := Eval vm_compute in run scr0 ssC0.
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC)).
Definition knC : list kentry := Eval vm_compute in kn_after rC knC0.
Definition srD0 : list expr := Eval vm_compute in sr_after_call_j srC KEPT_MC 71.

(* [comment removed for export] *)
Definition ssD0 : sym_state := SS 0x41d64 srD0 [] knC 103.
Definition rD := Eval vm_compute in run scr0 ssD0.
Definition srD : list expr := Eval vm_compute in s_regs (fst (fst rD)).
Definition knD : list kentry := Eval vm_compute in kn_after rD knC.
Definition srE0 : list expr := Eval vm_compute in sr_after_call_j srD KEPT_MC 103.

(* [comment removed for export] *)
Definition ssE0 : sym_state := SS 0x41d64 srE0 [] knD 135.
Definition rE := Eval vm_compute in run scr0 ssE0.
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
Definition knE : list kentry := Eval vm_compute in kn_after rE knD.
(* [comment removed for export] *)
Definition logM4 : list sentry := [SE (SA (EVar 0) (-546)) 8 (ELit 3762256352692483894)].
Definition knF0 : list kentry := Eval vm_compute in fst (fst (carry logM4 knE [])).
Definition srF0 : list expr := Eval vm_compute in sr_after_call_j srE KEPT_MC 135.

(* [comment removed for export] *)
Definition ssF0 : sym_state := SS 0x41d64 srF0 [] knF0 167.
Definition rF := Eval vm_compute in run scr0 ssF0.
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF)).
Definition knF : list kentry := Eval vm_compute in kn_after rF knF0.
Definition logM5 : list sentry := ltac2:(CDefT.buildp (gd_tbl_P_stdio_refused_defs ()) "(0.$1.(2.(3.(4.#0.)-212.)#8.(5.+:64657375666572.))(0.$1.(2.(3.(4.#0.)-21:.)#8.(5.+202<736574796220.))(6.$1.)))")
(* [comment removed for export] *).
Definition knG0 : list kentry := Eval vm_compute in fst (fst (carry logM5 knF [])).
Definition srG0 : list expr := Eval vm_compute in sr_after_call_j srF KEPT_MC 167.

(* [comment removed for export] *)
Definition ssG0 : sym_state := SS 0x41d64 srG0 [] knG0 199.
Definition rG := Eval vm_compute in run scr0 ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_after rG knG0.
Definition scRF : stdio_res := ltac2:(CDefT.buildp (gd_tbl_P_stdio_refused_defs ()) "(7.+4<=30.+2.+420:8.(8.$9.(4.#0.)(5.-230.))(8.$9.(4.#0.)(5.-20:.))(8.$9.(4.#0.)(5.-230.))(5.+50.)(5.=)(5.=)(8.$9.(4.#0.)(5.-240.))(0.$:.(4.#<7.)(0.$:.(5.+420:8.)(0.$:.(8.$9.(4.#0.)(5.-240.))(0.$:.(5.+10800.)(0.$:.(5.+5=0<8.)(0.$:.(4.#<<.)(0.$:.(4.#<=.)(0.$:.(4.#<>.)(0.$:.(5.+4<=30.)(0.$:.(5.+26.)(0.$:.(5.=)(0.$:.(4.#=2.)(0.$:.(4.#=3.)(0.$:.(4.#=4.)(0.$:.(4.#=5.)(0.$:.(4.#=6.)(0.$:.(4.#=7.)(0.$:.(4.#=8.)(0.$:.(5.+7=330.)(0.$:.(5.+1.)(0.$:.(5.+7=790.)(0.$:.(5.=)(0.$:.(4.#1<.)(0.$:.(4.#1=.)(0.$:.(4.#1>.)(0.$:.(4.#1?.)(0.$:.(4.#20.)(0.$:.(4.#21.)(0.$:.(4.#>3.)(0.$:.(4.#>4.)(0.$:.(4.#>5.)(0.$:.(4.#>6.)(6.$:.)))))))))))))))))))))))))))))))))(0.$;.(<.(3.(5.=)+4<=50.)#8.(8.$9.(4.#0.)(5.-1>0.)))(0.$;.(<.(3.(5.=)+4<=58.)#8.(8.$9.(4.#0.)(5.-230.)))(0.$;.(<.(3.(5.=)+4<=68.)#8.(8.$9.(4.#0.)(5.-230.)))(0.$;.(<.(3.(4.#0.)-212.)#8.(5.+:64657375666572.))(0.$;.(<.(3.(4.#0.)-21:.)#8.(5.+202<736574796220.))(0.$;.(<.(3.(4.#0.)-498.)#8.(5.+106=7.))(0.$;.(<.(3.(4.#0.)-490.)#8.(5.+4<=30.))(0.$;.(<.(3.(4.#0.)-488.)#8.(5.+16.))(0.$;.(<.(3.(4.#0.)-480.)#8.(5.+7?????>9.))(0.$;.(<.(3.(4.#0.)-478.)#8.(5.+7???????.))(0.$;.(<.(3.(4.#0.)-470.)#8.(5.+25.))(0.$;.(<.(3.(4.#0.)-468.)#8.(5.+42278.))(0.$;.(<.(3.(4.#0.)-222.)#8.(5.+3436383830313736.))(0.$;.(<.(3.(4.#0.)-458.)#8.(5.=))(0.$;.(<.(3.(4.#0.)-440.)#8.(5.+8.))(0.$;.(<.(3.(4.#0.)-450.)#8.(5.+8.))(0.$;.(<.(3.(4.#0.)-3;8.)#1.(5.+36.))(0.$;.(<.(3.(4.#0.)-460.)#8.(5.+102:5.))(0.$;.(<.(3.(4.#0.)-3;7.)#1.(5.+37.))(0.$;.(<.(3.(4.#0.)-3;6.)#1.(5.+31.))(0.$;.(<.(3.(4.#0.)-3;5.)#1.(5.+30.))(0.$;.(<.(3.(4.#0.)-3;4.)#1.(5.+38.))(0.$;.(<.(3.(4.#0.)-3;3.)#1.(5.+38.))(0.$;.(<.(3.(4.#0.)-3;2.)#1.(5.+36.))(0.$;.(<.(3.(4.#0.)-3;1.)#1.(5.+34.))(0.$;.(<.(3.(4.#0.)-448.)#8.(5.=))(0.$;.(<.(3.(4.#0.)-3?0.)#8.(5.+4000000.))(0.$;.(<.(3.(4.#0.)-240.)#8.(8.$9.(4.#0.)(5.-:8.)))(0.$;.(<.(3.(4.#0.)-224.)#2.(5.+203=.))(0.$;.(<.(3.(4.#0.)-228.)#4.(5.+3>207475.))(0.$;.(<.(3.(4.#0.)-230.)#8.(5.+706>69203:696<63.))(0.$;.(<.(3.(4.#0.)-438.)#8.(5.+????????<<<<<<<=.))(0.$;.(<.(3.(4.#0.)-430.)#8.(5.+???????????>????.))(0.$;.(<.(3.(4.#0.)-3?8.)#8.(5.+<<<<<<<.))(0.$;.(<.(3.(4.#0.)-410.)#8.(5.+12889.))(0.$;.(<.(3.(4.#0.)-400.)#8.(5.+7=330.))(0.$;.(<.(3.(4.#0.)-408.)#8.(5.=))(0.$;.(<.(3.(4.#0.)-418.)#8.(8.$9.(4.#0.)(5.-240.)))(0.$;.(<.(3.(4.#0.)-428.)#8.(8.$9.(4.#0.)(5.-1>0.)))(0.$;.(<.(3.(4.#0.)-420.)#8.(8.$9.(4.#0.)(5.-138.)))(0.$;.(<.(3.(5.=)+4<=40.)#8.(5.=))(0.$;.(<.(3.(5.=)+4<=38.)#8.(5.=))(0.$;.(<.(3.(5.=)+4<=;8.)#4.(5.+????????????????.))(0.$;.(<.(3.(5.=)+4<=90.)#8.(5.+50.))(0.$;.(<.(3.(5.=)+4<=88.)#8.(8.$9.(4.#0.)(5.-230.)))(0.$;.(<.(3.(5.=)+4<=30.)#4.(5.+5.))(0.$;.(<.(3.(4.#0.)-120.)#8.(5.=))(0.$;.(<.(3.(4.#0.)-128.)#8.(5.=))(0.$;.(<.(3.(4.#0.)-130.)#8.(5.=))(0.$;.(<.(3.(4.#0.)-138.)#8.(5.=))(0.$;.(<.(3.(4.#0.)-118.)#8.(5.=))(0.$;.(<.(3.(4.#0.)-238.)#8.(8.$9.(4.#0.)(5.-;0.)))(0.$;.(<.(3.(4.#0.)-110.)#8.(4.#3.))(0.$;.(<.(3.(4.#0.)-108.)#8.(4.#1;.))(0.$;.(<.(3.(4.#0.)-100.)#8.(4.#1:.))(0.$;.(<.(3.(4.#0.)-?8.)#8.(4.#19.))(0.$;.(<.(3.(4.#0.)-?0.)#8.(4.#18.))(0.$;.(<.(3.(4.#0.)->8.)#8.(4.#?.))(0.$;.(<.(3.(4.#0.)->0.)#8.(5.+7=330.))(0.$;.(<.(3.(4.#0.)-=8.)#8.(5.+41<40.))(0.$;.(<.(3.(4.#0.)-=0.)#8.(8.$9.(4.#0.)(5.-;0.)))(0.$;.(<.(3.(4.#0.)-<8.)#8.(4.#3.))(0.$;.(<.(3.(4.#0.)-98.)#8.(4.#15.))(0.$;.(<.(3.(4.#0.)-:0.)#8.(4.#14.))(0.$;.(<.(3.(4.#0.)-:8.)#8.(4.#13.))(0.$;.(<.(3.(4.#0.)-;0.)#8.(5.+4000000.))(0.$;.(<.(3.(4.#0.)-88.)#8.(4.#17.))(0.$;.(<.(3.(4.#0.)-90.)#8.(4.#16.))(0.$;.(<.(3.(4.#0.)-<0.)#8.(4.#>.))(0.$;.(<.(3.(4.#0.)-;8.)#8.(5.+1=4;0.))(0.$;.(=.(4.#0.)+10.)(0.$;.(>.(4.#0.)+7???80000000.+800000000000.)(0.$;.(?.(3.(4.#0.)-800000.)+800000.)(0.$;.(>.(4.#2.)+7???80000000.+800000400000.)(0.$;.(?.(3.(5.=)+4<000.)+32000.)(0.$;.(10.+10000.+4;<=8.)(0.$;.(<.(3.(5.=)+4;<=8.)#8.(5.+7=330.))(0.$;.(10.+4;<>0.+4<=30.)(0.$;.(10.+4<=34.+4<=38.)(0.$;.(10.+4<=48.+4<=50.)(0.$;.(10.+4<=60.+4<=68.)(0.$;.(10.+4<=70.+4<=88.)(0.$;.(10.+4<=98.+4<=;8.)(0.$;.(10.+4<=;<.+4<?20.)(0.$;.(<.(3.(5.=)+4<?68.)#1.(5.=))(0.$;.(<.(3.(5.=)+5=020.)#4.(4.#5.))(0.$;.(<.(3.(5.=)+7=328.)#4.(5.=))(0.$;.(<.(3.(5.=)+7=330.)#8.(4.#3.))(0.$;.(<.(3.(5.=)+7=353.)#1.(5.=))(0.$;.(<.(3.(5.=)+7=770.)#8.(5.=))(0.$;.(<.(3.(5.=)+7=780.)#8.(5.=))(0.$;.(>.(4.#5.)+1.+3?????.)(0.$;.(10.+7=108.+7=120.)(6.$;.)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).
Definition srH0 : list expr := Eval vm_compute in sc_sr scRF.
Definition knH0 : list kentry := Eval vm_compute in sc_kn scRF.

(* [comment removed for export] *)
Definition ssH0 : sym_state := SS (sc_ret scRF) srH0 [] knH0 231.
Definition rH := Eval vm_compute in run scr0 ssH0.
Definition srH : list expr := Eval vm_compute in s_regs (fst (fst rH)).
Definition knH : list kentry := Eval vm_compute in kn_after rH knH0.

Lemma itinerary_rf : ltac2:(CDefT.buildp (gd_tbl_P_stdio_refused_defs ()) "(11.(12.(13.$14.(15.$16.))(17.$14.(15.$16.)(18.(19.$1:.(15.$16.)(19.(13.$1:.(15.$16.))$1;.$1<.)))(1=.$1:.(15.$16.)(19.(13.$1:.(15.$16.))$1;.$1<.)))(17.$14.(15.$16.)+46:40.(6.$16.)))(11.(12.(13.$14.(15.$16.))(17.$14.(15.$16.)(18.(19.$1:.(15.$16.)(19.(13.$1:.(15.$16.))$1;.$1>.)))(1=.$1:.(15.$16.)(19.(13.$1:.(15.$16.))$1;.$1>.)))(17.$14.(15.$16.)+46:40.(6.$16.)))(11.(12.(13.$14.(15.$16.))(17.$14.(15.$16.)(18.(19.$1:.(15.$16.)(19.(13.$1:.(15.$16.))$1;.$1?.)))(1=.$1:.(15.$16.)(19.(13.$1:.(15.$16.))$1;.$1?.)))(17.$14.(15.$16.)+46:40.(6.$16.)))(11.(12.(13.$14.(15.$16.))(17.$14.(15.$16.)(18.(19.$1:.(15.$16.)(19.(13.$1:.(15.$16.))$1;.$20.)))(1=.$1:.(15.$16.)(19.(13.$1:.(15.$16.))$1;.$20.)))(17.$14.(15.$16.)+46:40.(6.$16.)))(11.(12.(13.$14.(15.$16.))(17.$14.(15.$16.)(18.(19.$1:.(15.$16.)(19.(13.$1:.(15.$16.))$1;.$21.)))(1=.$1:.(15.$16.)(19.(13.$1:.(15.$16.))$1;.$21.)))(17.$14.(15.$16.)+46:40.(6.$16.)))(11.(12.(13.$14.(15.$16.))(17.$14.(15.$16.)(18.(19.$1:.(15.$16.)(19.(13.$1:.(15.$16.))$1;.$22.)))(1=.$1:.(15.$16.)(19.(13.$1:.(15.$16.))$1;.$22.)))(17.$14.(15.$16.)+41:34.(6.$16.)))(11.(12.(23.$24.)(25.#<7.$26.$27.)(28.$24.$29.))(11.(12.(13.(13.$14.$14.)$14.)(17.(13.$14.$14.)$14.(17.$14.$14.(2:.$29.)(2;.$29.))(2<.$29.))(17.(13.$14.$14.)$14.(17.$14.$14.+420:8.+4<=30.)+2.))(11.(12.(13.(13.$:.$:.)$:.)(17.(13.$:.$:.)$:.(17.$:.$:.(2=.$29.)(2>.$29.))(2?.$29.))(17.(13.$:.$:.)$:.(17.$:.$:.(8.$9.(4.#0.)(5.-230.))(8.$9.(4.#0.)(5.-20:.)))(5.=)))(12.(13.$14.(15.$16.))(17.$14.(15.$16.)(18.(19.$1:.(15.$16.)(19.(13.$1:.(15.$16.))$1;.$30.)))(1=.$1:.(15.$16.)(19.(13.$1:.(15.$16.))$1;.$30.)))(17.$14.(15.$16.)+3?74<.(6.$16.))))))))))))")
(* [comment removed for export] *).
Proof. vm_compute. repeat split; reflexivity. Qed.
